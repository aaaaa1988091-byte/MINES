"""
human_aim.py — 擬人化瞄準（v5）

設計原則：不要把行為寫死成「每次抽籤」，而是讓一個「人」有持續的狀態。

  Personality   節奏(tempo)會慢慢漂移；有自己的習慣小動作，很久才會換；
                小動作的相位跨方塊延續（上一顆點頭，下一顆還在點頭）
  human_look    由多個「重疊的子動作」疊加而成（不是停住再轉）。
                終點誤差隨「速度、距離」增加（訊號相依雜訊）——慢慢轉不會出錯，
                猛甩才會轉過頭或沒到位；誤差落在目標容忍範圍內就不修正，
                需要修正時在 0.1 秒內接上
  AimHolder     盯著同一個方塊時的小動作，並用準心檢查確保還在同一個方塊上
  IdleDrift     沒事做時偶爾輕輕東張西望
"""

import math
import random
import threading
import time

import minescript
from pest_utils import (
    player_tracker, _perlin_1d, _clamp, _angle_diff, _calc_yaw_pitch,
)

def _adiff(a, b):
    """從角度 a 轉到 b 的最短有號差（-180~180）。自己寫，不依賴 pest_utils 的實作。"""
    return (b - a + 180.0) % 360.0 - 180.0


_angle_diff = _adiff

# ─────────────────────────────────────────────
# 參數（這些是「分佈的尺度」，不是固定行為）
# ─────────────────────────────────────────────
TREMOR_AMP   = 0.18    # 手部細微抖動幅度（度）
TICK_MIN     = 0.002   # 每次更新視角的間隔（秒）。要夠密（約 200Hz）才不會跟畫面更新錯拍而抽幀
TICK_MAX     = 0.005

ERR_K        = 0   # 終點誤差 σ = ERR_K × 距離 × 速度² + ERR_FLOOR（度）
ERR_FLOOR    = 0
OVER_BIAS    = 0    # 誤差平均略偏向「轉過頭」（單位：σ）
DEFAULT_TOL  = 0.8     # 沒指定容忍範圍時，誤差小於此值就不修正（度）
FIX_GAP      = (-0.06, 0.07)   # 修正動作相對於主動作結束的時間差（秒）；負值=提早接上、與主動作重疊
CLUTCH_DEG   = 85.0    # 單次轉動超過這個角度，可能拆成兩段「換手」重疊動作
CLUTCH_CHANCE = 0.5

# ── 挖掘時的橢圓晃動（準心繞著方塊畫「上下長」的橢圓）──
ELLIPSE_MODE   = True  # True=固定畫橢圓；False=用舊的個人習慣小動作
ELLIPSE_A      = 0.01 # 橢圓長軸半幅（方塊格）：視角「上下」方向。錄製結果你每顆方塊上掃過約 0.3~0.7 格
MAX_YAW_SPEED   = 1500.0  # 度/秒：任何來源的視角更新都不會超過（擋掉突然轉 360）
MAX_PITCH_SPEED = 900.0
ELLIPSE_B      = 0.01  # 橢圓短軸半幅（錄製結果：短軸/長軸約 0.5）
ELLIPSE_FREQ   = (1.5, 2)   # 每秒轉幾圈（錄製結果：主頻約 1.1~1.25 Hz）
RECALC_SEC     = 0.04   # 重新對準方塊中心的間隔（邊走邊挖時要夠勤，不然準心會落後）
EDGE_MARGIN    = 0.07   # 準心離方塊邊緣至少保留多少格（吸收微顫與延遲）

AIM_LEAD       = 0.035  # 視角低通濾波的時間常數（秒）：把目標位置往前推這麼久，抵消追等速移動目標時的固定落後
WOBBLE_MAX_DEG = 14.0  # 橢圓晃動在「畫面上」的最大幅度（度）。只是近距離的保險：實際幅度由 ELLIPSE_A / ELLIPSE_B 決定。
                       # 注意：這個值如果比 ELLIPSE_A 在該距離對應的角度小，ELLIPSE_A 改多大都沒用（舊值 2.5 就是這樣把幅度壓死的）
LOST_FAILS     = 8     # 準心連續幾次檢查（每 0.15 秒一次，約 1.2 秒）都不在目標方塊上，才算「瞄丟了」，交給主程式重新瞄準

_abort = None
FORCE_EYE = None       # 蹲下時由 auto_mine 設成 1.27（錄製驗證：用 1.27 時準心命中率 98.5%，1.62 只有 91.7%）


def eye_height():
    return FORCE_EYE if FORCE_EYE is not None else player_tracker.eye_height()


def _now() -> float:
    return time.perf_counter()


def set_abort(fn):
    """設定中止檢查函式；回傳 True 時所有動作立刻停在當下位置（不會補完、不會瞬移）。"""
    global _abort
    _abort = fn


def _aborted() -> bool:
    try:
        return bool(_abort and _abort())
    except Exception:
        return False


# ─────────────────────────────────────────────
# 基礎
# ─────────────────────────────────────────────
def tremor(amp=None):
    """連續的平滑微顫 (dyaw, dpitch)：慢漂移 + 細抖動兩層疊加，時間上連續。"""
    a = TREMOR_AMP if amp is None else amp
    t = _now()
    y = _perlin_1d(t * 1.2, 11) * 0.65 + _perlin_1d(t * 4.5, 12) * 0.35
    p = _perlin_1d(t * 1.0, 21) * 0.65 + _perlin_1d(t * 4.0, 22) * 0.35
    return y * a, p * a * 0.7


_last_out = None


def _set(yaw, pitch):
    """
    所有視角更新的唯一出口：
    1. 角度取最短路徑（永遠不會多繞 360）
    2. 限制角速度（任何 bug 也不會突然猛轉）
    """
    global _last_out
    now = time.perf_counter()
    if _last_out is None or now - _last_out[2] > 0.4:
        by, bp = _cur_orientation()          # 久沒輸出（或玩家自己動過）→ 從實際視角接續
        dt = 0.016
    else:
        by, bp = _last_out[0], _last_out[1]
        dt = _clamp(now - _last_out[2], 0.004, 0.1)
    dy = _clamp(_adiff(by, yaw), -MAX_YAW_SPEED * dt, MAX_YAW_SPEED * dt)
    dp = _clamp(pitch - bp, -MAX_PITCH_SPEED * dt, MAX_PITCH_SPEED * dt)
    ny, np_ = by + dy, _clamp(bp + dp, -90.0, 90.0)
    _last_out = (ny, np_, now)
    minescript.player_set_orientation(ny, np_)


def _cur_orientation():
    try:
        o = minescript.player_orientation()
        if o:
            return float(o[0]), float(o[1])
    except Exception:
        pass
    return player_tracker.orientation()


def cur_view():
    """
    目前視角的「單一來源」。最近 0.4 秒內有自己輸出過 → 用自己最後輸出的值；
    否則（玩家自己動過滑鼠、或剛啟動）才讀遊戲實際值。
    以前各模組各自讀 player_orientation()，而遊戲實際值會比我們剛寫的慢一拍，
    兩邊算出來的「現在在哪」就會差一點，接手時來回修正 → 微抽搐。
    """
    if _last_out is not None and time.perf_counter() - _last_out[2] <= 0.4:
        return _last_out[0], _last_out[1]
    return _cur_orientation()


TICK = 0.05     # 遊戲一個 tick = 50ms


class Sampler:
    """
    背景取樣：玩家位置 + 其他「慢」的遊戲呼叫（getblock、準心檢查…）。

    為什麼需要：
      * player_position() 回傳的是「tick 位置」，每 50ms 才變一次；但畫面上看到的相機位置是
        前後兩個 tick 之間補間出來的、連續的。拿 tick 位置算視角，目標每 50ms 跳一階
        （橫移 4 格/秒、距離 2.5 格 → 每階約 4~5 度），再怎麼平滑都是階梯狀的卡頓。
        這裡估計速度，輸出「畫面上實際看到的位置」(= 最新 tick 位置往回推一段)，目標就連續了。
      * 視角迴圈裡只要夾一次同步的 getblock / 準心檢查，整個視角就停住好幾個 tick。
        這些慢呼叫改在另一條執行緒做，視角迴圈只讀快取。
    """

    def __init__(self):
        self.running = False
        self._jobs = {}
        self._reset()

    def _reset(self):
        self.cur = None
        self.t_change = 0.0
        self.vel = (0.0, 0.0, 0.0)
        self.change_dt = TICK          # 相鄰兩次「位置改變」的間隔（EMA）。≈50ms = 位置只在 tick 更新；很小 = 本來就連續

    def start(self):
        if self.running:
            return
        self._reset()
        self.running = True
        threading.Thread(target=self._run_pos, daemon=True).start()
        threading.Thread(target=self._run_jobs, daemon=True).start()

    def stop(self):
        self.running = False
        self._jobs.clear()

    def add_job(self, key, interval, fn):
        self._jobs[key] = [interval, 0.0, fn]

    def remove_job(self, key):
        self._jobs.pop(key, None)

    def _run_pos(self):
        while self.running:
            t0 = _now()
            try:
                p = minescript.player_position()
                self._update((float(p[0]), float(p[1]), float(p[2])), t0)
            except Exception:
                pass
            dt = _now() - t0
            if dt < 0.008:
                time.sleep(0.008 - dt)

    def _run_jobs(self):
        while self.running:
            t = _now()
            for key in list(self._jobs):
                j = self._jobs.get(key)
                if j and t - j[1] >= j[0]:
                    j[1] = t
                    try:
                        j[2]()
                    except Exception:
                        pass
            time.sleep(0.004)

    def _update(self, p, t):
        c = self.cur
        if c is None:
            self.cur, self.t_change = p, t
            return
        if p != c:
            dt = t - self.t_change
            if dt <= 0.3:
                self.change_dt += (min(dt, 0.1) - self.change_dt) * 0.1
            n = max(1, round(dt / TICK))
            if dt <= 0.3:
                v = tuple((p[i] - c[i]) / (n * TICK) for i in range(3))
                self.vel = tuple(self.vel[i] * 0.4 + v[i] * 0.6 for i in range(3))
            else:
                self.vel = (0.0, 0.0, 0.0)
            self.cur, self.t_change = p, t
        elif t - self.t_change > 0.15:
            self.vel = (0.0, 0.0, 0.0)

    def position(self, lead=0.0):
        """
        畫面上實際看到的位置（連續）。沒在取樣時退回直接問遊戲。
        lead: 再往前推幾秒。視角用一階低通在追目標，追著等速移動的目標會固定落後 速度×時間常數，
              把目標往前推同樣的時間就剛好抵消。
        """
        c = self.cur
        if not self.running or c is None:
            p = minescript.player_position()
            return (float(p[0]), float(p[1]), float(p[2]))
        v = self.vel
        if self.change_dt < 0.03:                    # 位置本來就每次都在變 → 已經是連續的，只需要 lead
            off = lead
        else:
            off = _clamp(_now() - self.t_change - TICK, -TICK, TICK) + lead
        return (c[0] + v[0] * off, c[1] + v[1] * off, c[2] + v[2] * off)


SAMPLER = Sampler()


def _min_jerk(t):
    """最小急動度曲線：起步慢、中段快、收尾慢，比貝茲/smoothstep 更接近手臂運動。"""
    t = _clamp(t, 0.0, 1.0)
    return 10 * t**3 - 15 * t**4 + 6 * t**5


def _duration(d, speed=1.0):
    """Fitts 定律風格：距離越遠越久但非線性；speed 越大越快。"""
    t = (0.07 + 0.06 * math.log2(1 + d / 3.0)) / max(speed, 0.3) * random.uniform(0.92, 1.1)
    return _clamp(t, 0.05, 0.6)


# ─────────────────────────────────────────────
# 個性：節奏與習慣（持續的狀態，不是每次重新抽籤）
# ─────────────────────────────────────────────
class Personality:
    HABITS  = ["nod", "circle", "figure8", "sway", "still"]
    HABIT_W = [3, 3, 1, 2, 3]

    def __init__(self):
        t = _now()
        self.tempo = 1.0                 # 節奏：>1 趕、<1 悠閒，會慢慢漂移
        self._t_tempo = t
        self.habit = random.choices(self.HABITS, self.HABIT_W)[0]   # 習慣的小動作
        self.fid_on = random.random() < 0.6                          # 目前有沒有在「手癢」
        self.fid_until = t + random.uniform(25, 90)
        self.phase = random.uniform(0, 2 * math.pi)                  # 小動作相位（跨方塊延續）
        self._t_fid = t

    # 節奏：Ornstein–Uhlenbeck 過程，往 1.0 回歸（τ≈25 秒），所以會有一陣子急、一陣子慢
    def update_tempo(self):
        t = _now()
        dt = _clamp(t - self._t_tempo, 0.0, 2.0)
        self._t_tempo = t
        self.tempo += (1.0 - self.tempo) * dt / 25.0 + 0.08 * math.sqrt(dt) * random.gauss(0, 1)
        self.tempo = _clamp(self.tempo, 0.55, 1.8)

    def move_speed(self):
        """這一次轉動的速度係數：節奏 × 一點點隨機。"""
        self.update_tempo()
        return _clamp(self.tempo * math.exp(random.gauss(0, 0.10)), 0.5, 2.0)

    def new_block(self):
        """每挖一顆有很小的機率換習慣（平均幾十顆才換一次）。"""
        if random.random() < 0.03:
            self.habit = random.choices(self.HABITS, self.HABIT_W)[0]

    def fidget_target(self, max_amp):
        """依習慣給出目前的小動作偏移 (dyaw, dpitch)。頻率、幅度連續漂移，相位延續。"""
        t = _now()
        dt = _clamp(t - self._t_fid, 0.0, 0.1)
        self._t_fid = t
        if t > self.fid_until:
            self.fid_on = not self.fid_on
            self.fid_until = t + (random.uniform(25, 120) if self.fid_on else random.uniform(8, 40))
        if not self.fid_on or self.habit == "still":
            return 0.0, 0.0
        freq = 1.3 + 0.5 * _perlin_1d(t * 0.05, 31)                       # 約 0.8~1.8 Hz，緩慢漂移
        amp = max_amp * (0.75 + 0.25 * _perlin_1d(t * 0.08, 32))
        amp *= _clamp(1.6 - self.tempo * 0.6, 0.3, 1.0)                    # 趕的時候動作變小
        self.phase += 2 * math.pi * freq * dt
        w = self.phase
        if self.habit == "nod":
            return 0.0, amp * math.sin(w)
        if self.habit == "circle":
            return amp * math.cos(w), amp * math.sin(w)
        if self.habit == "figure8":
            return amp * math.sin(w), amp * 0.6 * math.sin(2 * w)
        if self.habit == "sway":
            return amp * math.sin(w), 0.0
        return 0.0, 0.0


    def ellipse_target(self, ay, ap):
        """上下長的橢圓：水平半幅 ay、垂直半幅 ap（度）。頻率與幅度緩慢漂移，相位延續。"""
        t = _now()
        dt = _clamp(t - self._t_fid, 0.0, 0.1)
        self._t_fid = t
        lo, hi = ELLIPSE_FREQ
        freq = lo + (hi - lo) * (0.5 + 0.5 * _perlin_1d(t * 0.07, 33))
        freq *= _clamp(0.85 + 0.25 * self.tempo, 0.8, 1.2)
        k = 0.88 + 0.12 * _perlin_1d(t * 0.09, 34)          # 每圈幅度略有不同，但不超過上限
        self.phase += 2 * math.pi * freq * dt
        return ay * k * math.cos(self.phase), ap * k * math.sin(self.phase)


me = Personality()


def _ray_hits_cube(eye, yaw, pitch, cell, margin):
    """從 eye 沿 (yaw, pitch) 射出的射線，是否穿過方塊 cell 往內縮 margin 格的立方體。"""
    yr, pr = math.radians(yaw), math.radians(pitch)
    d = (-math.sin(yr) * math.cos(pr), -math.sin(pr), math.cos(yr) * math.cos(pr))
    tmin, tmax = 0.0, 1e9
    for i in range(3):
        lo, hi = cell[i] + margin, cell[i] + 1.0 - margin
        if abs(d[i]) < 1e-9:
            if eye[i] < lo or eye[i] > hi:
                return False
            continue
        t1, t2 = (lo - eye[i]) / d[i], (hi - eye[i]) / d[i]
        if t1 > t2:
            t1, t2 = t2, t1
        tmin, tmax = max(tmin, t1), min(tmax, t2)
        if tmin > tmax:
            return False
    return True


# ─────────────────────────────────────────────
# 擬人轉頭：單段平順直達，不做過頭回拉
# ─────────────────────────────────────────────
def _endpoint_error(d, speed):
    """終點誤差：σ 隨距離與速度² 增加（訊號相依雜訊）。慢慢轉 σ≈地板值，幾乎不會出錯。"""
    sigma = ERR_K * d * speed ** 2 + ERR_FLOOR
    along = random.gauss(OVER_BIAS * sigma, sigma)     # 正=轉過頭、負=沒到位
    lat = random.gauss(0.0, sigma * 0.5)
    return along, lat


def _sub(t0, T, vy, vp, arc):
    d = math.hypot(vy, vp) or 1.0
    return (t0, T, vy, vp, arc, -vp / d, vy / d)      # 最後兩個是垂直方向，用來做弧形偏移


def _plan(start, end, tol, speed):
    """
    單段直接轉向：從目前視角平順抵達目標，不預先瞄過頭，也不安排回拉修正。
    tol 保留參數以相容既有呼叫端，但不再用它觸發終點往返修正。
    """
    dy, dp = end[0] - start[0], end[1] - start[1]
    distance = math.hypot(dy, dp)
    if distance < 1e-6:
        return [_sub(0.0, 0.05, 0.0, 0.0, 0.0)], end

    duration = _duration(distance, speed)
    subs = [_sub(0.0, duration, dy, dp, 0.0)]
    return subs, end


def _run(start, subs, tr_amp=None):
    """執行子動作疊加。回傳 (目前位置, 是否走完)。被中止時停在當下位置，不補完。"""
    t_total = max(s[0] + s[1] for s in subs)
    cur = start
    t_begin = _now()
    while True:
        if _aborted():
            return cur, False
        t = _now() - t_begin
        if t >= t_total:
            break
        y, p = start
        for (t0, T, vy, vp, arc, px, pp) in subs:
            if t <= t0:
                continue
            s = _min_jerk((t - t0) / T)
            bow = math.sin(math.pi * s) * arc
            y += vy * s + px * bow
            p += vp * s + pp * bow
        cur = (y, p)
        ty, tp = tremor(tr_amp)
        _set(y + ty, p + tp)
        time.sleep(random.uniform(TICK_MIN, TICK_MAX))
    y, p = start
    for (_, _, vy, vp, _, _, _) in subs:
        y += vy
        p += vp
    ty, tp = tremor(tr_amp)
    _set(y + ty, p + tp)
    return (y, p), True


def human_look(yaw, pitch, tol=None, speed=None, tr_amp=None):
    """
    轉向 (yaw, pitch)。回傳實際停下的 (yaw, pitch)（連續角度，不做 360 折返）。
    tol:   容忍範圍（度）。終點誤差小於它就不修正——呼叫者可依「方塊在視野中的大小」傳入。
    speed: 速度係數。None 則取目前的個人節奏；只影響轉向時間，不增加終點偏移。
    """
    sy, sp = cur_view()
    start = (sy, sp)
    end = (sy + _angle_diff(sy, yaw), _clamp(pitch, -90.0, 90.0))
    d = math.hypot(end[0] - sy, end[1] - sp)
    tol = DEFAULT_TOL if tol is None else tol
    speed = me.move_speed() if speed is None else speed

    if d < 0.3:   # 很小的調整：一個短短的子動作
        subs = [_sub(0.0, random.uniform(0.05, 0.10), end[0] - sy, end[1] - sp, 0.0)]
        final = end
    else:
        subs, final = _plan(start, end, tol, speed)
    pos, ok = _run(start, subs, tr_amp)
    return final if ok else pos


# ─────────────────────────────────────────────
# 接續轉向：把晃動的動量帶進下一次轉向
# ─────────────────────────────────────────────
GLIDE_W = 4.6      # 彈簧頻率 ω = GLIDE_W / 轉向時間：越大收斂越快（轉向時間仍由距離與節奏決定）


def glide_look(yaw, pitch, tol=None, v0=(0.0, 0.0), speed=None, tick=None, max_time=1.0):
    """
    從「目前視角 + 目前速度 v0」平順轉向 (yaw, pitch)，不停頓、不重新起步。

    用臨界阻尼彈簧（有閉合解，任何 dt 都穩定）：初速度保留，所以挖完一顆時晃動的方向會自然
    彎進下一個方塊，而不是停住再轉。進入容忍範圍（且速度夠小）就結束，把控制權交給下一個 AimHolder。
    tick: 每個迴圈額外呼叫的函式（例如橫移的 step）。**不可以在裡面做同步的遊戲呼叫**，否則視角會一頓一頓。
    回傳結束時的 (yaw, pitch)。診斷：結束後讀 glide_look.stats = (總用時秒, 最大迴圈間隔秒)。
    """
    sy, sp = cur_view()
    ty = sy + _adiff(sy, yaw)
    tp = _clamp(pitch, -90.0, 90.0)
    tol = DEFAULT_TOL if tol is None else tol
    speed = me.move_speed() if speed is None else speed
    d = math.hypot(ty - sy, tp - sp)
    w = GLIDE_W / _duration(max(d, 1.0), speed)
    x, p = sy, sp
    vy, vp = v0
    done_err = max(0.4, 0.35 * tol)
    t_begin = last = _now()
    max_gap = 0.0

    def fin():
        glide_look.stats = (_now() - t_begin, max_gap)
        return (x, p)

    while True:
        if _aborted():
            return fin()
        if tick:
            tick()
        now = _now()
        max_gap = max(max_gap, now - last)
        dt = _clamp(now - last, 0.001, 0.05)
        last = now
        e = math.exp(-w * dt)
        ay, ap = x - ty, p - tp
        cy, cp = vy + w * ay, vp + w * ap
        x = ty + (ay + cy * dt) * e
        p = tp + (ap + cp * dt) * e
        vy = (vy - w * cy * dt) * e
        vp = (vp - w * cp * dt) * e
        tr_y, tr_p = tremor()
        _set(x + tr_y, p + tr_p)
        if math.hypot(ty - x, tp - p) < done_err and math.hypot(vy, vp) < 60.0:
            return fin()
        if now - t_begin > max_time:
            return fin()
        time.sleep(random.uniform(TICK_MIN, TICK_MAX))


glide_look.stats = (0.0, 0.0)


# ─────────────────────────────────────────────
# 盯著方塊時的小動作
# ─────────────────────────────────────────────
class AimHolder:
    """
    挖掘期間每個 tick 呼叫 step()：準心繞著方塊面畫「畫面上下長」的橢圓。

    v5 重點（修「晃動和主視角搶控制權」）：
      1. 瞄準的「面」在建立時就定下來，之後不再重算（以前每 0.1 秒依眼睛位置重選面/長軸，
         邊走邊挖時會在兩個面或兩個軸之間跳，準心位置瞬間差好幾度）。
      2. 橢圓直接定義在「畫面座標」（右/上向量）上，再投影回方塊面：連續、沒有任何離散切換。
      3. 檢查準心偏掉時只是慢慢縮小幅度，不再「幅度歸零 0.3 秒 → 又放大 → 又偏掉」的來回循環；
         連續偏掉很多次就回報 lost()，讓主程式重新瞄準，而不是一直對著空氣晃。
    """

    def __init__(self, block_pos, aim_pt, reach=4.5):
        self.pos = tuple(int(v) for v in block_pos)
        self.aim = tuple(float(v) for v in aim_pt)
        self.reach = reach
        self.y, self.p = cur_view()              # 目前輸出（連續角度）
        self.vy = 0.0                            # 晃動當下的視角速度（度/秒，已平滑）；換方塊時接續用
        self.vp = 0.0
        self.k = 0.3                             # 晃動幅度係數（淡入）。不從 0 開始：換方塊時晃動要無縫接上，不是停一下才重新開始
        self.k_cap = 1.0                         # 準心檢查失敗時縮小，成功時慢慢回升
        self._verify_ok = True
        self.fails = 0                           # 準心連續不在目標上的次數
        now = _now()
        self._last_t = now
        self._last_verify = now
        self._verify_n = 0
        self.n = 0                               # 瞄準面的法線軸
        self.sign = 1.0                          # 面在方塊的哪一側
        self.cen = list(self.aim)
        self._pick_face(self._eye())
        SAMPLER.add_job("verify", 0.15, self._verify_job)     # 準心檢查在背景做，不卡視角迴圈
        me.new_block()

    def _pos(self):
        try:
            return SAMPLER.position(lead=AIM_LEAD)
        except Exception:
            return player_tracker.position()

    def _eye(self):
        x, y, z = self._pos()
        return (x, y + eye_height(), z)

    def _verify_job(self):
        if _now() - self._last_t > 0.3:          # 沒在 step（這顆已經挖完/換人了）就不檢查
            return
        self._verify()

    def _pick_face(self, eye):
        """
        面與晃動中心直接取自「已驗證準心打得到」的瞄準點（aim）所在的面，
        不再自己依視線主軸重選面——重選的面可能被鄰居擋住，且會讓視角從第一次瞄的點滑到另一個面（迴旋）。
        """
        best = None
        for i in range(3):
            for sign, off in ((1.0, 1.0), (-1.0, 0.0)):
                e = abs(self.aim[i] - (self.pos[i] + off))
                if best is None or e < best[0]:
                    best = (e, i, sign, off)
        if best is not None and best[0] <= 0.02:
            _, n, sign, off = best
            cen = list(self.aim)
            cen[n] = self.pos[n] + off              # 精確貼在面上
            self.n, self.sign, self.cen = n, sign, cen
            return
        # aim 不在任何面上（呼叫端給了奇怪的點）：退回舊的「依視線主軸選面」
        c = [self.pos[i] + 0.5 for i in range(3)]
        d = [eye[i] - c[i] for i in range(3)]
        n = max(range(3), key=lambda i: abs(d[i]))
        sign = 1.0 if d[n] >= 0 else -1.0

        # 以可見面的中心為基準。晃動只在這個面內進行，不沿用可能偏向邊角的 aim 座標。
        cen = c[:]
        cen[n] = c[n] + 0.5 * sign
        self.n, self.sign, self.cen = n, sign, cen

    def _wobble_point(self, eye, u, v):
        """畫面座標 (u 右, v 上) 的偏移，沿視線投影回方塊面。回傳世界座標的瞄準點。"""
        cen = self.cen
        vd = [cen[i] - eye[i] for i in range(3)]
        L = math.sqrt(sum(t * t for t in vd))
        if L < 1e-6:
            return cen
        vd = [t / L for t in vd]
        # 近距離時方塊在畫面上很大：把晃動限制在 WOBBLE_MAX_DEG 以內
        ang = math.degrees(math.atan(ELLIPSE_A / max(L, 0.8)))
        sc = min(1.0, WOBBLE_MAX_DEG / max(ang, 1e-6))
        u, v = u * sc, v * sc
        rx, rz = vd[2], -vd[0]                          # 世界「上」 × 視線 = 畫面的右
        rn = math.hypot(rx, rz)
        right = (rx / rn, 0.0, rz / rn) if rn > 1e-6 else (1.0, 0.0, 0.0)
        up = (vd[1] * right[2] - vd[2] * right[1],
              vd[2] * right[0] - vd[0] * right[2],
              vd[0] * right[1] - vd[1] * right[0])
        Q = [cen[i] + right[i] * u + up[i] * v for i in range(3)]
        D = [Q[i] - eye[i] for i in range(3)]
        n = self.n
        plane = self.pos[n] + 0.5 + 0.5 * self.sign
        P = list(cen)
        if abs(D[n]) > 1e-6:
            t = (plane - eye[n]) / D[n]
            if t > 0.2:
                P = [eye[i] + D[i] * t for i in range(3)]
        P[n] = plane
        for i in range(3):
            if i != n:
                c = self.pos[i] + 0.5
                P[i] = _clamp(P[i], c - 0.44, c + 0.44)
        return P

    def fresh(self, within=0.6):
        """最近有在 step()（也就是剛剛還在晃動）。"""
        return _now() - self._last_t < within

    def velocity(self):
        """目前的視角速度 (度/秒)。太久沒更新就當作靜止。"""
        if not self.fresh(0.25):
            return (0.0, 0.0)
        return (self.vy, self.vp)

    def lost(self):
        """準心已經連續好幾次不在目標方塊上（被擊退、面被擋住、方塊已經不見…）。"""
        return self.fails >= LOST_FAILS

    def _verify(self):
        """準心真的還在同一個方塊上嗎？偏了就縮小幅度（慢慢回升，不來回開關）。"""
        self._last_verify = _now()
        if not self._verify_ok:
            return
        try:
            tb = minescript.player_get_targeted_block(self.reach + 1.0)
        except Exception:
            self._verify_ok = False
            return
        cur = None if tb is None else tuple(int(v) for v in tb.position)
        if cur != self.pos:
            self.fails += 1
            self.k_cap = max(0.35, self.k_cap * 0.85)
        else:
            self.fails = 0
            self.k_cap = min(1.0, self.k_cap + 0.02)

    def step(self, fidget=True):
        """更新一次視角並睡一個 tick。fidget=False 時只保留微顫、不做橢圓。"""
        now = _now()
        dt = _clamp(now - self._last_t, 0.001, 0.1)
        self._last_t = now
        x, y, z = self._pos()
        eh = eye_height()
        eye = (x, y + eh, z)
        goal = self.k_cap if fidget else 0.0
        self.k += (goal - self.k) * (1 - math.exp(-dt / 0.15))
        u, v = me.ellipse_target(ELLIPSE_B, ELLIPSE_A)       # (短軸, 長軸) 畫面座標偏移（方塊格）
        P = self._wobble_point(eye, u * self.k, v * self.k)
        yaw, pitch = _calc_yaw_pitch((x, y, z), P, eh)
        ty = self.y + _adiff(self.y, yaw)
        tp = _clamp(pitch, -90.0, 90.0)
        a = 1 - math.exp(-dt / 0.035)
        oy, op = self.y, self.p
        self.y += (ty - self.y) * a
        self.p += (tp - self.p) * a
        self.vy += ((self.y - oy) / dt - self.vy) * 0.5
        self.vp += ((self.p - op) / dt - self.vp) * 0.5
        tr_y, tr_p = tremor()
        _set(self.y + tr_y, self.p + tr_p)
        if fidget and not SAMPLER.running and now - self._last_verify > 0.15:
            self._verify()                       # 沒有背景取樣時才在迴圈裡檢查（相容舊用法）
        time.sleep(random.uniform(TICK_MIN, TICK_MAX))


# ─────────────────────────────────────────────
# 閒置時東張西望
# ─────────────────────────────────────────────
class IdleDrift:
    """沒有目標時呼叫 step()：視角微顫，偶爾輕輕看向旁邊一點。"""
    def __init__(self):
        self.reset()

    def reset(self):
        self.anchor = None
        self.next_t = 0.0

    def step(self):
        now = time.time()
        if self.anchor is None:
            self.anchor = cur_view()
            self.next_t = now + random.uniform(1.0, 3.0)
        if now >= self.next_t:
            ay, ap = self.anchor
            self.anchor = human_look(ay + random.uniform(-14, 14),
                                     _clamp(ap + random.uniform(-7, 7), -85, 85),
                                     tol=1.5, speed=min(me.move_speed(), 0.9))   # 隨意看看，不急
            self.next_t = time.time() + random.uniform(2.0, 5.0)
        else:
            ty, tp = tremor()
            _set(self.anchor[0] + ty, self.anchor[1] + tp)
            time.sleep(random.uniform(TICK_MIN, TICK_MAX))