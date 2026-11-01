"""
auto_mine.py — 多目標自動挖掘（擬人版 v2：防呆修正）
挖掉會變基岩、幾秒後自動恢復；眼前變基岩就換下一顆。

操作：
  滑鼠按鈕 3            切換到下一個目標群組
  滑鼠按鈕 5            把準心對著的方塊記錄到 mine_targets.json（成為新群組並切過去）
                        （SNEAK=True 時全程蹲著，所以不再用「蹲下+按鈕3」）
  滑鼠按鈕 4            開 / 關（關閉時完全不碰滑鼠和視角，你可以自己操作）
  F9                    真正結束腳本（由 Minescript 負責，這裡不處理）

附近沒有礦時，會在「開啟位置」半徑 10 格內找礦，像人一樣走過去再挖（FAR_SEARCH）。
要同時挖多種方塊：編輯 mine_targets.json，把它們放進同一個群組的清單即可（執行中改檔會自動生效）。

用法（Minescript）：  \\auto_mine
需要同資料夾有 pest_utils.py、human_aim.py、human_walk.py、mine_targets.py
"""

import math
import os
import queue
import random
import threading
import time

import minescript
from pest_utils import (
    player_tracker, find_blocks_nearby, get_block_aim_point, aim_visibility_grid,
    _calc_yaw_pitch, _clamp,
)
import human_aim as HA
from human_aim import human_look, glide_look, AimHolder, IdleDrift, set_abort, me
from human_walk import walk_to_ore, classify
from mine_targets import TargetStore, normalize

# ─────────────────────────────────────────────
# 設定
# ─────────────────────────────────────────────
# 滑鼠按鍵編號（GLFW，從 0 算起）：0左 1右 2中鍵(滾輪按下) 3=側鍵「按鈕4」 4=側鍵「按鈕5」
# 這裡把「按鈕 N」當成從 1 算起：按鈕3 = 編號 2（中鍵），按鈕4 = 編號 3。
SWITCH_BUTTON  = 2              # 切換 / 蹲下+按 = 記錄
TOGGLE_BUTTON  = 3              # 開 / 關
RECORD_BUTTON  = 4              # 側鍵「按鈕5」：記錄準心對著的方塊（SNEAK=True 時蹲下一直按著，所以不能再用「蹲下+按鈕3」）
SNEAK          = True           # 近距離挖掘時蹲著；長距離趕路時不蹲（改用衝刺+跳）
START_ENABLED  = False          # 腳本啟動時是否直接開始挖（False = 先待命，按按鈕4才開始）
DEBUG_BUTTONS  = False          # True 會印出每個按下的滑鼠按鍵編號，用來確認上面兩個設定

TARGETS_FILE   = None           # None = 與本腳本同資料夾的 mine_targets.json
SWITCH_AFTER_RECORD = True      # 記錄新方塊後是否立刻切過去
RECORD_DISTANCE = 8.0           # 記錄時準心最遠可指到多遠的方塊

DEBUG          = True           # True 會在聊天欄印出除錯訊息（找不到目標的原因、每顆挖的過程）；正常使用後改 False

REACH          = 3.5            # 觸及範圍
MIN_MINE_SEC   = 0.25           # 至少按住這麼久才判定「挖完」，避免誤判造成一閃而過
MINE_TIMEOUT   = 6.0            # 單顆最長挖掘秒數，超過就放棄換下一顆
POLL_SEC       = 0.05           # 檢查方塊狀態的間隔
RETRY_SKIP_SEC = 3.0            # 逾時放棄的方塊，這段時間內不再選它
PICK_WEIGHTS   = [6.0, 2.5, 1.5]   # 選目標：最近 / 第二近 / 第三近 的權重（不一定都挑最近的）
# ── 找遠處的礦（尋路）──
FAR_SEARCH     = True           # 附近沒礦時，是否走去找遠一點的礦
LEASH_RADIUS   = 100.0           # 活動半徑：以「開啟位置」為中心，不會走出這個範圍
STAND_REACH    = 3.5            # 站位離礦的眼睛距離（保守一點，橫移時還有 1~2 格餘裕）
MIN_GAIN       = 3.0            # 開始挖/換礦時：找到的站位至少要多照顧這麼多顆礦才值得走過去
REEVAL_EVERY   = 25             # 每挖這麼多顆就重新評估一次站位
SNEAK_EYE      = 1.27           # 蹲下時的眼睛高度（錄製驗證過）
RECOVER_WAIT   = (2.5, 5.0)     # 附近剛挖過的方塊還在恢復時，先等這麼久才考慮走遠
WALK_GRACE     = (0.3, 1.0)     # 附近完全沒礦時，發呆多久才動身
WALK_COOLDOWN  = 3.0            # 找不到/走不到時，隔多久再試

REACT_BEFORE   = (0.0, 0.02)    # 轉到目標後的反應時間（錄製結果：左鍵 99.4% 時間都按著，換目標幾乎沒停頓）
REACT_AFTER    = (0.08, 0.18)    # 方塊變基岩後，換下一個目標前的反應時間（這段時間晃動照常繼續，然後從晃動的動量接著彎過去）
PREFETCH       = True            # 挖這顆時背景先挑下一顆。如果懷疑背景呼叫造成卡頓，先改 False 試試
PREFETCH_WAIT  = 0.5             # 背景還沒挑好下一顆時，最多再邊晃邊等這麼久（不會凍結視角）
HOLD_ATTACK    = True           # 挖完一顆不放開左鍵，直接轉向下一顆（跟你錄的一樣）

# ── 防呆（修：挖完還在挖基岩 / 沒挖完就跑掉 / 被打飛後對空氣打 / 掉進虛空）──
BREAK_RESULT   = ("minecraft:bedrock",)   # 方塊被挖掉後會變成什麼（你的遊戲設計：變基岩）。看到它就立刻算挖完
CONFIRM_SEC    = 0.4            # 不是 BREAK_RESULT 的「變了」，要連續穩定這麼久才算挖完（擋掉客戶端預測、伺服器退回前短暫閃一下）
REACH_SLACK    = 1.6            # 眼睛離目標方塊中心超過 REACH + 這個值，而且比剛開始挖時又遠了 KNOCK_DIST 以上（被擊退/推開），才放棄重新站位
KNOCK_DIST     = 1.5
GUARD_FAR      = True           # 被打飛偵測（出問題可關掉）
GUARD_LOST     = True           # 準心偏離偵測（出問題可關掉）
RECENT_GUARD   = 1.0            # 剛挖完的方塊，這段時間內不再選（避免舊的搜尋結果又把它選回來）
MAX_TURN_DEG   = 100.0          # 選目標時，需要轉超過這個角度的（在背後）排到最後，除非前面完全沒有
TURN_COST_DEG  = 60.0           # 排序時：每多轉這麼多度，等於多 1 格距離
FALL_LIMIT     = 15.0           # 比開啟位置低超過這麼多格 = 掉下去了，立刻停止並放開所有按鍵

# ── 邊挖邊橫移（錄製結果：A/D 交替按、每次約 0.5~1.2 秒，偶爾點一下 W，人幾乎待在原地附近）──
STRAFE          = False
STRAFE_HOLD     = (0.45, 1.2)   # A 或 D 每次按住多久
STRAFE_W_CHANCE = 0.3           # 換向時順便點一下 W 的機率
STRAFE_W_HOLD   = (0.12, 0.40)
STRAFE_RADIUS   = 1.6           # 離「站位」超過這麼遠就往回走
# 橫移不能讓目標被擋住：鎖定目標時算出「站在哪些位置準心還打得到它的那個面」，橫移只在這個範圍內進行
VIS_HALF        = 1.8           # 可見範圍的取樣半徑（格）
VIS_STEP        = 0.2           # 取樣間距（格）
VIS_LEAD        = 0.35          # 往移動方向多看這麼遠：下一步也要還看得到，才准繼續走（吸收按鍵延遲與滑行）

# ─────────────────────────────────────────────
# 狀態
# ─────────────────────────────────────────────
_enabled = START_ENABLED
_gen = 0                 # 目標版本號：切換群組/改 JSON 造成目標變動時 +1，用來中斷進行中的動作
_active_gen = [0]
_store = None
_strafer = None
_origin_y = None


def _block_raw(c):
    try:
        return str(minescript.getblock(*c))
    except Exception:
        return "minecraft:stone"


def _set_sneak(on):
    """蹲下/站起，並同步眼睛高度（蹲下 1.27）。"""
    if not SNEAK:
        return
    try:
        minescript.player_press_sneak(bool(on))
    except Exception:
        pass
    HA.FORCE_EYE = SNEAK_EYE if on else None


# ─────────────────────────────────────────────
# 非阻塞按鍵：player_press_* 是同步呼叫，在視角迴圈裡呼叫會讓視角停一下（轉向時特別明顯）。
# 所有橫移按鍵改丟進佇列，由背景執行緒依序送出；視角迴圈只做一次 put，不會被卡住。
# ─────────────────────────────────────────────
_key_q = queue.Queue()
_key_thread = None


def _key_worker():
    while True:
        fn, v = _key_q.get()
        try:
            fn(v)
        except Exception:
            pass
        finally:
            _key_q.task_done()


def _key_put(fn, v):
    global _key_thread
    if _key_thread is None or not _key_thread.is_alive():
        _key_thread = threading.Thread(target=_key_worker, daemon=True)
        _key_thread.start()
    _key_q.put((fn, v))


_echo_q = queue.Queue()
_echo_thread = None


def _echo_worker():
    while True:
        msg = _echo_q.get()
        try:
            minescript.echo(msg)
        except Exception:
            pass


def _echo(msg):
    """聊天欄訊息。minescript.echo 是同步呼叫（要等遊戲回應），在視角迴圈旁邊呼叫會讓視角凍結；改丟佇列由背景送出。"""
    global _echo_thread
    if _echo_thread is None or not _echo_thread.is_alive():
        _echo_thread = threading.Thread(target=_echo_worker, daemon=True)
        _echo_thread.start()
    _echo_q.put(msg)


def _key_flush(timeout=0.8):
    """等佇列裡的按鍵都送完（走路/關閉前要確保放開的指令已經生效，不然晚到的放開會蓋掉後來按下的鍵）。"""
    t_end = time.time() + timeout
    while _key_q.unfinished_tasks and time.time() < t_end:
        time.sleep(0.005)


class Strafer:
    """蹲著邊挖邊左右橫移：A/D 交替、偶爾點 W；離站位太遠就往回；前方有牆就換向，不撞牆。"""

    def __init__(self):
        self.anchor = None
        self.key = None            # 目前按住的方向鍵："left" / "right"
        self.until = 0.0
        self.w_until = 0.0
        self.w_down = False
        self.last = 0.0
        self._cls = {}
        self._ck, self._ct = None, 0.0
        self.target = None         # (方塊座標, 瞄準點)：目前鎖定的目標
        self.grid = None           # 可見範圍格點（aim_visibility_grid 的回傳）

    def set_target(self, pos, aim, grid=None, have_grid=False):
        """鎖定新目標：同步算一次可見範圍。算不出來就站著不動（寧可不橫移，也不要把目標晃丟）。"""
        self.target = (pos, aim)
        self.grid = grid if have_grid else aim_visibility_grid(pos, aim, VIS_HALF, VIS_STEP)
        if DEBUG:
            if self.grid is None:
                _echo("[橫移] %s 算不出可見範圍，這顆站著挖" % (pos,))
            else:
                _, _, st, N, cells = self.grid
                _echo("[橫移] %s 可站的位置 %d / %d 格" % (pos, len(cells), (2 * N + 1) ** 2))

    def clear_target(self):
        self.target = None
        self.grid = None

    def _vis(self, x, z):
        """(x, z) 這個位置看得到目標嗎？周圍四個取樣點都要看得到才算（保守）。"""
        g = self.grid
        if g is None:
            return False
        bx0, bz0, st, N, cells = g
        fx, fz = (x - bx0) / st, (z - bz0) / st
        i0, j0 = math.floor(fx), math.floor(fz)
        for i in (i0, i0 + 1):
            for j in (j0, j0 + 1):
                if (i, j) not in cells:
                    return False
        return True

    def _nogo(self, pos, dx, dz):
        """往 (dx,dz) 走會撞牆/掉下去，或走下一步就看不到目標了。"""
        if self._blocked(pos, dx, dz):
            return True
        if self.target is not None:
            return not self._vis(pos[0] + dx * VIS_LEAD, pos[2] + dz * VIS_LEAD)
        return False

    @staticmethod
    def _press(name, v):
        fn = getattr(minescript, "player_press_" + name, None)
        if fn:
            _key_put(fn, v)

    def _cell_class(self, c):
        v = self._cls.get(c)
        if v is None:                       # 快取還沒涵蓋到（剛啟動/剛移動）：退回單格查詢
            if len(self._cls) > 3000:
                self._cls.clear()
            v = classify(_block_raw(c))
            self._cls[c] = v
        return v

    def refresh(self):
        """背景執行：一次批次讀玩家周圍的方塊，橫移判斷就不必在視角迴圈裡一格一格同步查詢。"""
        now = time.time()
        if now - self.last > 0.6:
            return                          # 橫移沒在運作
        pos = _player_pos()
        cx, cy, cz = math.floor(pos[0]), math.floor(pos[1] + 0.01), math.floor(pos[2])
        key = (cx, cy, cz)
        if key == self._ck and now - self._ct < 1.0:
            return
        cells = [(x, y, z) for x in range(cx - 3, cx + 4) for z in range(cz - 3, cz + 4)
                 for y in (cy - 2, cy - 1, cy, cy + 1)]
        raws = _blocks_raw(cells)
        if len(self._cls) > 3000:
            self._cls.clear()
        for c, r in zip(cells, raws):
            self._cls[c] = classify(r)
        self._ck, self._ct = key, now

    def _blocked(self, pos, dx, dz):
        """
        往 (dx,dz) 方向走會不會出事：
          1. 身體有寬度（半寬 0.3）：前緣左中右三個點，腳和頭的位置有沒有實心/危險方塊
          2. 前方腳下有沒有地板：兩層都不是實心 = 虛空/深坑，不能走
        """
        fy = math.floor(pos[1] + 0.01)
        px, pz = -dz, dx
        for d in (0.4, 0.8):
            for off in (-0.3, 0.0, 0.3):
                cx = math.floor(pos[0] + dx * d + px * off)
                cz = math.floor(pos[2] + dz * d + pz * off)
                for yy in (fy, fy + 1):
                    if self._cell_class((cx, yy, cz)) in ("S", "T", "H"):
                        return True
        cx, cz = math.floor(pos[0] + dx * 0.6), math.floor(pos[2] + dz * 0.6)
        if self._cell_class((cx, fy - 1, cz)) != "S" and self._cell_class((cx, fy - 2, cz)) != "S":
            return True
        return False

    def reset(self):
        self.release()
        self.anchor = None
        self._cls.clear()
        self.clear_target()
        _key_flush()

    def release(self):
        if self.key:
            self._press(self.key, False)
            self.key = None
        if self.w_down:
            self._press("forward", False)
            self.w_down = False

    def step(self):
        now = time.time()
        if now - self.last < 0.03:
            return
        self.last = now
        pos = _player_pos()
        if self.anchor is None:
            self.anchor = pos
        yr = math.radians(HA.cur_view()[0])
        right = (-math.cos(yr), -math.sin(yr))          # 往右（D）在世界座標的方向
        fwd = (-math.sin(yr), math.cos(yr))
        dirs = {"right": right, "left": (-right[0], -right[1])}

        if self.target is not None and not self._vis(pos[0], pos[2]):
            self.release()                                # 現在的位置已經看不到目標：停下，別再亂動
            self.until = now + 0.15
            return

        if self.w_down and (now >= self.w_until or self._nogo(pos, *fwd)):
            self._press("forward", False)
            self.w_down = False
        if self.key and self._nogo(pos, *dirs[self.key]):
            self.until = 0.0                              # 前面是牆 / 再走就看不到目標 → 立刻換向
        if now < self.until:
            return

        back = (self.anchor[0] - pos[0], self.anchor[2] - pos[2])
        dist_back = math.hypot(*back)
        far = dist_back > STRAFE_RADIUS
        if far:
            order = ["right", "left"] if (right[0] * back[0] + right[1] * back[1]) > 0 else ["left", "right"]
        elif self.key is None:
            order = random.sample(["left", "right"], 2)
        else:
            order = ["left", "right"] if self.key == "right" else ["right", "left"]
        key = None
        for k in order:
            if not self._nogo(pos, *dirs[k]):
                key = k
                break
        if key is None:                                   # 兩邊都是牆 → 站著不動一下
            if self.key:
                self._press(self.key, False)
                self.key = None
            self.until = now + 0.4
            return
        if self.key and self.key != key:
            self._press(self.key, False)
        if self.key != key:
            self._press(key, True)
        self.key = key
        self.until = now + random.uniform(0.3 if far else STRAFE_HOLD[0], STRAFE_HOLD[1])
        if (not far and not self.w_down and dist_back < STRAFE_RADIUS * 0.6
                and random.random() < STRAFE_W_CHANCE and not self._nogo(pos, *fwd)):
            self._press("forward", True)
            self.w_down = True
            self.w_until = now + random.uniform(*STRAFE_W_HOLD)


def _default_targets_path():
    try:
        base = os.path.dirname(os.path.abspath(__file__))
    except NameError:
        base = os.getcwd()
    return os.path.join(base, "mine_targets.json")


# ─────────────────────────────────────────────
# 方塊工具
# ─────────────────────────────────────────────
def _block_at(pos) -> str:
    """回傳方塊 id（含 minecraft: 前綴、不含狀態）；失敗回傳空字串。"""
    try:
        return normalize(minescript.getblock(*pos))
    except Exception:
        return ""


def _is_target(pos, names) -> bool:
    """該位置現在還是不是目標方塊（變基岩/空氣都會回傳 False）。"""
    return _block_at(pos) in names


def _player_pos():
    try:
        return HA.SAMPLER.position()
    except Exception:
        return player_tracker.position()


def _blocks_raw(cells):
    """一次讀多格（一個呼叫），失敗退回逐格。回傳原始 id 字串列表。"""
    try:
        res = minescript.getblocklist([list(c) for c in cells])
        if res is not None and len(res) == len(cells):
            return [str(r) for r in res]
    except Exception:
        pass
    return [_block_raw(c) for c in cells]


def _check_fall(pp):
    """掉到開啟位置下方太多 = 掉進虛空：直接關閉並中斷所有動作（按鍵由各處的 finally / 關閉流程放開）。"""
    global _enabled, _gen
    if _enabled and _origin_y is not None and pp[1] < _origin_y - FALL_LIMIT:
        _enabled = False
        _gen += 1
        _echo("[保護] 掉到開啟位置下方 %.0f 格，已自動暫停" % (_origin_y - pp[1]))
        return True
    return False


# ─────────────────────────────────────────────
# 按鍵事件：切換 / 記錄 / 停止
# ─────────────────────────────────────────────
def _record_target():
    """記錄準心對著的方塊。"""
    try:
        tb = minescript.player_get_targeted_block(RECORD_DISTANCE)
    except Exception:
        tb = None
    if tb is None:
        _echo("[記錄] 準心前沒有方塊")
        return False
    pos = tuple(int(v) for v in tb.position)
    bid = _block_at(pos) or normalize(getattr(tb, "type", ""))
    status, name = _store.add_block(bid, switch=SWITCH_AFTER_RECORD)
    if status == "banned":
        _echo("[記錄] 這個方塊不能當目標: %s" % (bid or "?"))
        return False
    if status == "exists":
        _echo("[記錄] %s 已經在清單裡" % name)
    else:
        _echo("[記錄] 已新增 %s" % name)
    return SWITCH_AFTER_RECORD


def _on_switch_pressed():
    """回傳 True 表示目標變了。"""
    if not SNEAK and player_tracker.is_sneaking():
        return _record_target()
    name = _store.cycle()
    _echo("[切換] %s" % _store.summary())
    return True


def _poll(eq):
    """處理滑鼠事件：開關 / 切換 / 記錄。"""
    global _enabled, _gen
    while True:
        try:
            ev = eq.get(block=False)
        except queue.Empty:
            return
        except Exception:
            return
        if ev is None:
            return
        button = getattr(ev, "button", None)
        action = getattr(ev, "action", None)
        if button is None or action != 1:   # 只處理「按下」
            continue
        if DEBUG_BUTTONS:
            _echo("滑鼠按鍵編號: %s" % button)
        if button == TOGGLE_BUTTON:
            _enabled = not _enabled
            _gen += 1                        # 中斷進行中的轉頭/挖掘
            _echo("[開關] 已%s" % ("開始" if _enabled else "暫停"))
        elif button == SWITCH_BUTTON:
            if _on_switch_pressed():
                _gen += 1
        elif button == RECORD_BUTTON:
            if _record_target():
                _gen += 1


# ─────────────────────────────────────────────
# 挑目標 / 挖
# ─────────────────────────────────────────────
def _recovering(recent: dict, now: float) -> bool:
    """附近是否有剛挖過、還在恢復的方塊（挖完不到 15 秒、仍在觸及範圍內）。"""
    pp = _player_pos()
    eye = (pp[0], pp[1] + HA.eye_height(), pp[2])
    return any(now - t < 15.0 and math.dist(eye, (p[0] + .5, p[1] + .5, p[2] + .5)) <= REACH + 0.5
               for p, t in recent.items())


def _looks_done(bid: str) -> bool:
    """這個 id 代表「已經被挖掉/還沒恢復」：基岩、空氣。"""
    return bid in BREAK_RESULT or bid.endswith(":air") or bid.endswith("_air")


_ID_CACHE = {}      # {座標: (方塊id, 時間)}：挑目標時順便讀到的，給 _mine_one 當起始 id


def _pick_target(skip: dict, names, recent=None):
    """
    挑目標：先排序（近 + 不用大轉頭），再依權重在最前面幾顆裡隨機選，直到找到「看得到」的。
    - 搜尋結果可能是舊的：每顆候選都用即時的 getblock 再確認一次，已經變基岩的直接丟掉
    - 剛挖完的方塊 RECENT_GUARD 秒內不再選
    - 在背後（要轉很大角度）的排到最後
    回傳 (座標, 瞄準點) 或 None。
    """
    now = time.time()
    cands = [p for p in find_blocks_nearby(names, reach=REACH)
             if skip.get(p, 0) <= now and (not recent or now - recent.get(p, 0.0) > RECENT_GUARD)]
    if not cands:
        return None

    pp = _player_pos()
    eh = HA.eye_height()
    eye = (pp[0], pp[1] + eh, pp[2])
    cur_yaw = HA.cur_view()[0]
    scored = []
    for p in cands:
        c = (p[0] + .5, p[1] + .5, p[2] + .5)
        yaw, _ = _calc_yaw_pitch(pp, c, eh)
        scored.append((math.dist(eye, c), abs(HA._adiff(cur_yaw, yaw)), p))
    front = [t for t in scored if t[1] <= MAX_TURN_DEG]
    pool = front if front else scored
    pool.sort(key=lambda t: t[0] + t[1] / TURN_COST_DEG)

    top = [p for _, _, p in pool[:14]]
    ids = _blocks_raw(top)                     # 一次呼叫確認這幾顆現在還是不是目標（不要逐顆同步查，會讓視角停住）
    _t_ids = time.time()
    for _p, _r in zip(top, ids):
        _ID_CACHE[tuple(_p)] = (normalize(_r), _t_ids)
    if len(_ID_CACHE) > 200:
        for _k in [k for k, v in _ID_CACHE.items() if _t_ids - v[1] > 5.0]:
            _ID_CACHE.pop(_k, None)
    live = [p for p, r in zip(top, ids) if not _looks_done(normalize(r))]
    if not live:
        return None

    head, tail = live[:len(PICK_WEIGHTS)], live[len(PICK_WEIGHTS):]
    weights = PICK_WEIGHTS[:len(head)]
    order = []
    while head:
        i = random.choices(range(len(head)), weights)[0]
        order.append(head.pop(i))
        weights.pop(i)
    order += tail

    for pos in order[:8]:
        aim = get_block_aim_point(*pos)
        if aim is not None:
            return pos, aim
    return None


def _mine_one(pos, holder, eq, names, gen) -> str:
    """
    對 pos 按住攻擊，期間持續做小動作，直到方塊「變了」。
    回傳：
      "done"    挖完了（變成 BREAK_RESULT，或「穩定地不是原本的方塊」超過 CONFIRM_SEC）
      "timeout" 太久沒挖掉
      "switch"  被切換目標群組/關閉而中斷
      "stale"   開始挖的時候它就已經是基岩/空氣（搜尋結果過期）
      "far"     被擊退/推開，已經超出觸及範圍
      "lost"    準心連續偏離目標（面被擋、被打飛、方塊不見…），不要再對著空氣打
    """
    _c = _ID_CACHE.pop(tuple(pos), None)
    if _c is not None and time.time() - _c[1] < 4.0:
        start_id = _c[0]              # 剛挑目標時讀過：不要在這裡再同步讀一次（會讓剛轉好的視角停住）
    else:
        start_id = _block_at(pos)
    if start_id and _looks_done(start_id):
        if DEBUG:
            _echo("[略過] %s 已經是 %s" % (pos, start_id))
        return "stale"
    if DEBUG:
        _echo("[挖] %s %s" % (pos, start_id or "?"))
    center = (pos[0] + .5, pos[1] + .5, pos[2] + .5)
    _p0 = _player_pos()
    d0 = math.dist((_p0[0], _p0[1] + HA.eye_height(), _p0[2]), center)
    watch = {"id": start_id}
    use_bg = HA.SAMPLER.running
    if use_bg:
        def _watch():
            watch["id"] = _block_at(pos)
        HA.SAMPLER.add_job("block", POLL_SEC, _watch)      # 方塊狀態在背景查，視角迴圈不用等
    _key_put(minescript.player_press_attack, True)
    keep = False
    t0 = last = time.time()
    changed_id, changed_since = None, 0.0
    try:
        while True:
            _poll(eq)
            if _gen != gen:
                return "switch"
            now = time.time()
            if now - last >= POLL_SEC:
                last = now
                pp = _player_pos()
                if _check_fall(pp):
                    return "switch"
                eye = (pp[0], pp[1] + HA.eye_height(), pp[2])
                dnow = math.dist(eye, center)
                if GUARD_FAR and dnow > REACH + REACH_SLACK and dnow > d0 + KNOCK_DIST:
                    if DEBUG:
                        _echo("[超出範圍] %s 離 %.1f 格，放棄這顆重新站位" % (pos, math.dist(eye, center)))
                    return "far"
                if GUARD_LOST and now - t0 > 0.8 and holder.lost():
                    if DEBUG:
                        _echo("[瞄丟了] %s 準心不在方塊上，重新瞄準" % (pos,))
                    return "lost"

                cur = watch["id"] if use_bg else _block_at(pos)
                broke = False
                if cur:                                  # "" = 這次讀取失敗，不當成「變了」
                    if cur in BREAK_RESULT:
                        broke = True
                    else:
                        differs = (cur != start_id) if start_id else (cur not in names)
                        if not differs:
                            changed_id = None
                        elif cur != changed_id:            # 剛變 / 又變成別的：重新計時
                            changed_id, changed_since = cur, now
                        broke = differs and now - changed_since >= CONFIRM_SEC
                if broke and now - t0 >= MIN_MINE_SEC:
                    if DEBUG:
                        _echo("[完成] %s → %s（%.2fs）" % (pos, cur or "?", now - t0))
                    keep = HOLD_ATTACK            # 不放開左鍵，直接轉向下一顆
                    return "done"
                if now - t0 > MINE_TIMEOUT:
                    if DEBUG:
                        _echo("[逾時] %s 仍是 %s，放棄這顆" % (pos, cur or "?"))
                    return "timeout"
            if _strafer:
                _strafer.step()
            holder.step()    # 橢圓晃動 + 微顫
    finally:
        if use_bg:
            HA.SAMPLER.remove_job("block")
        if not keep:
            minescript.player_press_attack(False)   # 只放開我們自己按的左鍵


class Prefetch:
    """挖目前這顆的同時，在背景先挑好下一顆（含瞄準點與橫移可見範圍），挖完直接取用，視角就不用凍結等搜尋。"""

    def __init__(self):
        self.done = True
        self.res = None            # ((座標, 瞄準點), 可見範圍, gen)
        self._id = 0

    def start(self, skip, names, recent, exclude, gen):
        if not PREFETCH:
            return
        self._id += 1
        my = self._id
        self.done = False
        self.res = None
        sk = dict(skip)
        sk[tuple(exclude)] = time.time() + 30.0     # 正在挖的這顆不能再選
        rc = dict(recent)
        nm = list(names)

        def run():
            r = None
            try:
                picked = _pick_target(sk, nm, rc)
                if picked is not None:
                    grid = aim_visibility_grid(picked[0], picked[1], VIS_HALF, VIS_STEP) if STRAFE else None
                    r = (picked, grid, gen)
            except Exception:
                r = None
            if self._id == my:
                self.res = r
                self.done = True

        threading.Thread(target=run, daemon=True).start()

    def cancel(self):
        self._id += 1
        self.res = None
        self.done = True

    def take(self, gen, skip, recent):
        r, self.res = self.res, None
        if r is None or r[2] != gen:
            return None
        pos = r[0][0]
        now = time.time()
        if skip.get(pos, 0) > now or now - recent.get(pos, 0.0) <= RECENT_GUARD:
            return None
        return r


_pref = Prefetch()


def _hold_for(holder, secs, eq, gen, fidget=True):
    t_end = time.time() + secs
    while time.time() < t_end and _gen == gen:
        _poll(eq)
        if _strafer:
            _strafer.step()
        holder.step(fidget=fidget)


def _travel(names, origin, skip, known, eq, improve_min):
    """走去能瞄準最多礦的站位：不蹲、直線衝刺+跳；到站（或不用走）後回到蹲姿。"""
    _pref.cancel()

    def _go():
        if _strafer:
            _strafer.reset()
        minescript.player_press_attack(False)
        _set_sneak(False)

    # 規劃路線要讀很多方塊、可能花好幾秒：這段時間腳本卡住，沒放開的 A/D/左鍵會一直按著，
    # 人物就會一路橫著走下去（走進虛空）。所以先放開再算。
    minescript.player_press_attack(False)
    if _strafer:
        _strafer.release()
        _key_flush()

    now = time.time()
    skip_cells = [p for p, t in skip.items() if t > now]
    walk_gen = _gen
    status, why, ore = walk_to_ore(
        names, origin, LEASH_RADIUS,
        lambda: (_poll(eq), _gen != walk_gen or not _enabled)[1],
        skip=skip_cells, stand_reach=STAND_REACH, known=known,
        mine_eye=(SNEAK_EYE if SNEAK else None), improve_min=improve_min, on_start=_go,
        dbg=(lambda m: _echo("[尋路] " + m)) if DEBUG else None)
    if _enabled:
        _set_sneak(True)
    return status, why, ore


# ─────────────────────────────────────────────
# 主程式
# ─────────────────────────────────────────────
def main():
    global _store, _gen, _strafer, _origin_y
    _store = TargetStore(TARGETS_FILE or _default_targets_path())
    if _store.error:
        _echo(_store.error)

    player_tracker.start()
    HA.SAMPLER.start()
    time.sleep(0.5)  # 等追蹤器收到第一筆玩家狀態

    skip = {}        # {座標: 解除跳過的時間}
    last_gen = _gen
    mined = 0
    was_enabled = False
    last_dbg = 0.0
    origin = None                 # 開啟位置（尋路活動範圍的圓心）
    recent = {}                   # {座標: 挖完時間}：用來判斷附近是否有方塊正在恢復
    idle_since = None
    wait_s = 0.0
    far_cooldown = 0.0
    need_vantage = False          # 開始/換礦/每挖一批後，先評估站位
    known = set()                 # 挖過、會恢復的方塊座標（評估站位時算半顆）
    idle = IdleDrift()
    prev_holder = None            # 剛挖完那顆的 AimHolder：用來把晃動的動量接到下一次轉向
    _echo("自動挖掘已載入（%s）。目前目標: %s"
                    % ("執行中" if _enabled else "待命中", _store.summary()))
    _echo("按鈕4=開/關  按鈕3=切換目標  按鈕5=記錄眼前方塊  F9=結束腳本")

    with minescript.EventQueue() as eq:
        eq.register_mouse_listener()
        # 轉頭到一半也能立刻響應 開關/切換
        set_abort(lambda: (_poll(eq), _gen != _active_gen[0])[1])
        try:
            while True:
                _poll(eq)

                # JSON 被手動改過 → 重載；目標內容有變就中斷目前動作
                before = tuple(_store.current_blocks())
                if _store.reload_if_changed():
                    if _store.error:
                        _echo(_store.error)
                    elif tuple(_store.current_blocks()) != before:
                        _gen += 1
                        _echo("[重載] 目標: %s" % _store.summary())

                # ── 關閉狀態：完全不碰視角和按鍵，讓玩家自己操作 ──
                if not _enabled:
                    _pref.cancel()
                    prev_holder = None
                    if was_enabled:
                        minescript.player_press_attack(False)
                        _set_sneak(False)
                        if _strafer:
                            _strafer.reset()
                        _echo("已暫停，這次共挖了 %d 顆" % mined)
                        was_enabled = False
                    time.sleep(0.05)
                    continue
                if not was_enabled:
                    idle.reset()
                    mined = 0
                    was_enabled = True
                    _set_sneak(True)
                    need_vantage = True
                    if STRAFE:
                        _strafer = Strafer()
                        HA.SAMPLER.add_job("strafe", 0.25, _strafer.refresh)
                    origin = _player_pos()
                    _origin_y = origin[1]
                    idle_since = None
                    if DEBUG:
                        _echo("[開啟位置] (%.1f, %.1f, %.1f)，活動半徑 %.0f 格" % (*origin, LEASH_RADIUS))

                if _check_fall(_player_pos()):
                    continue
                names = _store.current_blocks()
                gen = _gen
                _active_gen[0] = gen
                if gen != last_gen:
                    skip.clear()
                    known.clear()
                    need_vantage = True
                    last_gen = gen

                if need_vantage and FAR_SEARCH:
                    need_vantage = False
                    status, why, ore = _travel(names, origin or _player_pos(), skip, known, eq, MIN_GAIN)
                    if DEBUG and why:
                        _echo("[站位] %s" % why)
                    if status in ("arrived", "aborted"):
                        idle_since = None
                        continue

                if _strafer:
                    _strafer.clear_target()
                got_grid, grid = False, None
                r_ = _pref.take(gen, skip, recent)
                if r_ is not None:                      # 背景已經挑好了：直接用，視角不凍結
                    picked, grid, _g = r_
                    got_grid = True
                else:
                    if DEBUG and PREFETCH and mined > 0:
                        _echo("[預選] 沒有現成的，改成同步挑（視角會停一下）")
                    if _strafer:
                        _strafer.release()              # 同步搜尋會卡住幾百毫秒，先放開橫移鍵
                    picked = _pick_target(skip, names, recent)
                if picked is None:
                    if _strafer:
                        _strafer.release()
                    now = time.time()
                    if idle_since is None:
                        idle_since = now
                        recovering = _recovering(recent, now)
                        wait_s = (random.uniform(*RECOVER_WAIT) if recovering
                                  else random.uniform(*WALK_GRACE))
                    if DEBUG and now - last_dbg > 3.0:
                        last_dbg = now
                        status, n = find_blocks_nearby.last_status
                        why = {"ok": "搜到 %d 顆（被跳過或看不到）" % n,
                               "bridge_failed": "搜尋腳本沒有回應/逾時",
                               "bad_names": "目標名稱不合法"}.get(status, status)
                        _echo("[除錯] 範圍內沒有可挖目標｜找 %s｜%s" % (
                            ",".join(n_.split(":")[-1] for n_ in names), why))

                    if FAR_SEARCH and now - idle_since >= wait_s and now >= far_cooldown:
                        # 附近沒礦（或等過了恢復時間）：走去找遠一點的礦
                        idle.reset()
                        minescript.player_press_attack(False)
                        if _strafer:
                            _strafer.reset()
                        status, why, ore = _travel(names, origin or _player_pos(), skip, known, eq, 0.0)
                        if status == "arrived":
                            idle_since = None
                        elif status == "aborted":
                            pass
                        else:                       # none / failed
                            far_cooldown = time.time() + WALK_COOLDOWN
                            if ore is not None:
                                skip[ore] = time.time() + 20.0
                            if DEBUG:
                                _echo("[尋路] %s" % (why or "走不到，先放棄"))
                        continue

                    idle.step()          # 還在等 / 沒目標：微顫 + 偶爾東張西望
                    continue
                idle_since = None
                idle.reset()
                pos, aim = picked
                if _strafer:
                    _strafer.set_target(pos, aim, grid, got_grid)     # 橫移只在「還看得到這顆」的範圍內進行

                # 擬人轉頭（可能轉過頭再修正／中途抬滑鼠）
                ppos = _player_pos()
                eh = HA.eye_height()
                yaw, pitch = _calc_yaw_pitch(ppos, aim, eh)
                dist = math.dist((ppos[0], ppos[1] + eh, ppos[2]), aim)
                # 容忍範圍 ≈ 方塊面在視野中的張角：終點誤差落在方塊內就不必修正
                tol = _clamp(math.degrees(math.atan(0.28 / max(dist, 1.0))), 0.8, 6.0)
                if prev_holder is not None and prev_holder.fresh():
                    # 剛挖完上一顆：從晃動的動量直接彎向下一顆，不停頓、不重新起步（橫移照常，可見範圍已限制好）
                    glide_look(yaw, pitch, tol=tol, v0=prev_holder.velocity(),
                               tick=(_strafer.step if _strafer else None))
                    if DEBUG:
                        _gt, _gg = glide_look.stats
                        _echo("[轉向] %.0fms，最大間隔 %.0fms%s" % (
                            _gt * 1000, _gg * 1000, "  ← 有卡頓" if _gg > 0.04 else ""))
                else:
                    if _strafer:
                        _strafer.release()      # 從靜止轉頭：先停橫移，位置才不會在轉頭時變動
                    human_look(yaw, pitch, tol=tol)
                prev_holder = None
                if _gen != gen or not _enabled:
                    continue

                holder = AimHolder(pos, aim, REACH)
                _hold_for(holder, random.uniform(*REACT_BEFORE) / me.tempo, eq, gen, fidget=False)  # 反應時間
                if _gen != gen or not _enabled:
                    continue

                _pref.start(skip, names, recent, pos, gen)      # 挖這顆的同時，背景先挑好下一顆
                result = _mine_one(pos, holder, eq, names, gen)
                if result == "done":
                    mined += 1
                    known.add(tuple(pos))
                    if mined % REEVAL_EVERY == 0:
                        need_vantage = True
                    recent[pos] = time.time()
                    if len(recent) > 64:
                        for k in [k for k, t in recent.items() if time.time() - t > 30.0]:
                            del recent[k]
                elif result == "timeout":     # 先別再選這顆
                    skip[pos] = time.time() + RETRY_SKIP_SEC
                elif result == "stale":       # 搜尋結果過期（其實已經是基岩）：一下子別再選
                    skip[pos] = time.time() + 1.0
                    recent[pos] = time.time()
                    continue
                elif result == "lost":        # 準心對不上：換一顆，這顆晚一點再試
                    skip[pos] = time.time() + 1.5
                    continue
                elif result == "far":         # 被擊退/推開：重新站位（走回能挖到的地方）
                    skip[pos] = time.time() + 2.0
                    if _strafer:
                        _strafer.reset()
                    need_vantage = True
                    continue
                else:                          # switch：直接回到迴圈頂端重新判斷
                    continue

                # 剛挖完：還盯著原處晃一下才反應過來（晃動不中斷）；背景還沒挑好就邊晃邊等
                _hold_for(holder, random.uniform(*REACT_AFTER) / me.tempo, eq, gen)
                t_lim = time.time() + PREFETCH_WAIT
                while not _pref.done and time.time() < t_lim and _gen == gen and _enabled:
                    _poll(eq)
                    if _strafer:
                        _strafer.step()
                    holder.step()
                prev_holder = holder
        finally:
            _pref.cancel()
            set_abort(None)
            minescript.player_press_attack(False)
            _set_sneak(False)
            if _strafer:
                _strafer.reset()
            HA.SAMPLER.stop()
            player_tracker.stop()


main()