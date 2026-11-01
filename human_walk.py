"""
human_walk.py — 擬人尋路與走路

  walk_to_ore(names, origin, leash, abort)
      在「開啟位置 origin」半徑 leash 格內找目標方塊，規劃路徑走到能挖到它的位置。

流程：
  1. Snapshot     把附近的方塊一次讀進來並分類（可通行 / 實心 / 水 / 危險 / 高欄杆）
  2. 規劃         Dijkstra：支援斜走、上 1 階（跳）、下 1~2 階；避開危險、偏好寬敞、
                  轉彎有成本（路線比較順）、每格有一點雜訊（每次走法略有不同）；
                  終點是「眼睛能看到並碰到礦」的站位，並非總是選最優
  3. 平順化       同一高度的路徑拉直成斜線，路點加一點橫向偏移
  4. 走路控制     只用 W/Sprint/Jump + 視角，像真人：
                  視角追著「前方預視點」走（有慣性、不是對準格子中心）、轉彎時放慢、
                  直線才衝刺、在階梯前才跳、快到時提早放開 W（滑行）、
                  最後幾格視線先飄向礦（預判）；卡住會跳、再卡就重新規劃
"""

import heapq
import math
import random
import time

import minescript
from pest_utils import player_tracker, _perlin_1d, _clamp, _calc_yaw_pitch
import human_aim as HA
from mine_targets import normalize

_angle_diff = HA._adiff     # 自己的最短角度差（不依賴 pest_utils 的實作，避免突然轉 360）

# ─────────────────────────────────────────────
# 方塊分類
# ─────────────────────────────────────────────
# P 可穿過  S 實心  W 水  H 危險  T 太高(圍欄/牆，不能進也不能站)
_P_EXACT = {
    "air", "cave_air", "void_air", "structure_void", "light", "snow",
    "torch", "wall_torch", "soul_torch", "soul_wall_torch", "redstone_torch", "redstone_wall_torch",
    "lever", "tripwire", "tripwire_hook", "redstone_wire", "vine", "glow_lichen", "sculk_vein",
    "dead_bush", "short_grass", "grass", "tall_grass", "fern", "large_fern", "sugar_cane",
    "wheat", "carrots", "potatoes", "beetroots", "nether_wart", "red_mushroom", "brown_mushroom",
    "dandelion", "poppy", "blue_orchid", "allium", "azure_bluet", "oxeye_daisy", "cornflower",
    "lily_of_the_valley", "sunflower", "lilac", "rose_bush", "peony", "torchflower", "pitcher_plant",
    "crimson_roots", "warped_roots", "nether_sprouts", "hanging_roots", "moss_carpet", "pink_petals",
}
_P_SUFFIX = ("_sapling", "_button", "_pressure_plate", "_sign", "_hanging_sign", "_carpet",
             "rail", "_banner", "_tulip", "_roots")
_H_EXACT = {
    "lava", "fire", "soul_fire", "magma_block", "cactus", "sweet_berry_bush", "campfire",
    "soul_campfire", "wither_rose", "powder_snow", "cobweb", "end_portal", "nether_portal",
    "end_gateway", "pointed_dripstone",
}
_W_EXACT = {"water", "seagrass", "tall_seagrass", "kelp", "kelp_plant", "bubble_column"}
_T_SUFFIX = ("_fence", "_wall", "_fence_gate")

_CLS_CACHE = {}


def classify(raw_id) -> str:
    c = _CLS_CACHE.get(raw_id)
    if c is not None:
        return c
    name = normalize(raw_id)
    name = name.split(":", 1)[1] if ":" in name else name
    if name in _H_EXACT:
        c = "H"
    elif name in _W_EXACT:
        c = "W"
    elif name in _P_EXACT or name.endswith(_P_SUFFIX) or (
            "grass" in name and "block" not in name and "path" not in name):
        c = "P"
    elif name.endswith(_T_SUFFIX):
        c = "T"
    else:
        c = "S"
    _CLS_CACHE[raw_id] = c
    return c


# ─────────────────────────────────────────────
# 世界快照
# ─────────────────────────────────────────────
def _fetch(cells):
    """批次讀方塊。優先用 getblocklist，沒有就退回逐格 getblock。"""
    try:
        res = minescript.getblocklist([list(c) for c in cells])
        if res is not None and len(res) == len(cells):
            return [str(r) for r in res]
    except Exception:
        pass
    out = []
    for c in cells:
        try:
            out.append(str(minescript.getblock(*c)))
        except Exception:
            out.append("minecraft:stone")
    return out


class Snapshot:
    CHUNK = 2500

    def __init__(self, center_cell, rxz, ry):
        cx, cy, cz = center_cell
        self.box = (cx - rxz, cx + rxz, cy - ry, cy + ry, cz - rxz, cz + rxz)
        self.grid = {}     # cell -> 分類字元
        self.ids = {}      # cell -> 正規化後的方塊 id
        self._walk = {}
        self._ec = {}
        self._load()

    def _load(self):
        x0, x1, y0, y1, z0, z1 = self.box
        cells = [(x, y, z) for y in range(y0, y1 + 1)
                 for x in range(x0, x1 + 1) for z in range(z0, z1 + 1)]
        for i in range(0, len(cells), self.CHUNK):
            chunk = cells[i:i + self.CHUNK]
            for c, raw in zip(chunk, _fetch(chunk)):
                self.grid[c] = classify(raw)
                self.ids[c] = normalize(raw)

    def at(self, x, y, z):
        return self.grid.get((x, y, z), "S")      # 範圍外當成牆，不往外走

    def body_free(self, x, y, z):
        """腳和頭的位置都能穿過（不含水中的頭）。"""
        return self.at(x, y, z) in "PW" and self.at(x, y + 1, z) == "P"

    def walkable(self, x, y, z):
        """(x,y,z) 是否能站人：腳踩實心、腳/頭可穿過。水只允許淺水（頭在水面上）。"""
        k = (x, y, z)
        r = self._walk.get(k)
        if r is None:
            r = (self.at(x, y - 1, z) == "S"
                 and self.at(x, y, z) in "PW"
                 and self.at(x, y + 1, z) == "P")
            self._walk[k] = r
        return r


# ─────────────────────────────────────────────
# 規劃
# ─────────────────────────────────────────────
_DIRS8 = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)]


def _inside(c, origin, leash):
    return (c[0] + 0.5 - origin[0]) ** 2 + (c[1] - origin[1]) ** 2 + (c[2] + 0.5 - origin[2]) ** 2 <= leash ** 2


def _moves(snap, c):
    """從 c 能走到的相鄰站位 [(cell, 基本成本)]。"""
    x, y, z = c
    out = []
    for dx, dz in _DIRS8:
        diag = dx != 0 and dz != 0
        nx, nz = x + dx, z + dz
        if snap.walkable(nx, y, nz):
            if diag and not (snap.body_free(x + dx, y, z) and snap.body_free(x, y, z + dz)):
                continue                                  # 斜走不能切過牆角
            out.append(((nx, y, nz), 1.414 if diag else 1.0))
        if diag:
            continue
        if snap.walkable(nx, y + 1, nz) and snap.at(x, y + 2, z) == "P":
            out.append(((nx, y + 1, nz), 2.2))            # 跳上一階
        for drop in (1, 2):
            ny = y - drop
            if snap.walkable(nx, ny, nz) and all(snap.at(nx, t, nz) == "P" for t in range(ny + 1, y + 2)):
                out.append(((nx, ny, nz), 1.4 + 0.5 * (drop - 1)))   # 往下走
                break
    return out


def _static_cost(snap, c):
    """與雜訊無關的成本（每個格子只算一次，快取在快照上）。"""
    r = snap._ec.get(c)
    if r is not None:
        return r
    x, y, z = c
    cost = 0.0
    if snap.at(x, y, z) == "W":
        cost += 1.5                                       # 涉水較慢
    # 離危險方塊遠一點：貼著（含斜角）很貴，隔一格還是有點貴
    near = far = False
    for dx in range(-2, 3):
        for dz in range(-2, 3):
            if dx == 0 and dz == 0:
                continue
            for t in (y - 1, y, y + 1):
                if snap.at(x + dx, t, z + dz) == "H":
                    if max(abs(dx), abs(dz)) == 1:
                        near = True
                    else:
                        far = True
    cost += 4.0 if near else (1.2 if far else 0.0)
    # 偏好寬敞：身邊每一面牆都加一點成本，路線自然離牆角遠一點
    solid = sum(1 for dx, dz in ((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1))
                if snap.at(x + dx, y, z + dz) in "ST")
    cost += 0.3 * solid
    snap._ec[c] = cost
    return cost


def _extra_cost(snap, c, seed):
    return _static_cost(snap, c) + (hash((c[0], c[1], c[2], seed)) % 1000) / 1000.0 * 0.2   # 每條路略有不同


def _los_clear(snap, eye, target, ignore):
    """眼睛到目標中心的連線沒有被實心方塊擋住。"""
    ex, ey, ez = eye
    tx, ty, tz = target
    L = math.dist(eye, target)
    n = max(2, int(L / 0.2))
    for i in range(1, n):
        f = i / n
        c = (math.floor(ex + (tx - ex) * f), math.floor(ey + (ty - ey) * f), math.floor(ez + (tz - ez) * f))
        if c in ignore:
            continue
        if snap.at(*c) in "ST":
            return False
    return True


def build_goals(snap, ores, origin, leash, eye_h, stand_reach):
    """每顆礦周圍「能站、眼睛碰得到、看得到」的站位。回傳 {站位: (礦, 眼睛距離)}。"""
    goals = {}
    for o in ores:
        center = (o[0] + 0.5, o[1] + 0.5, o[2] + 0.5)
        for sx in range(o[0] - 4, o[0] + 5):
            for sz in range(o[2] - 4, o[2] + 5):
                for sy in range(o[1] - 5, o[1] + 3):
                    c = (sx, sy, sz)
                    if not snap.walkable(sx, sy, sz) or not _inside(c, origin, leash):
                        continue
                    eye = (sx + 0.5, sy + eye_h, sz + 0.5)
                    d = math.dist(eye, center)
                    if d > stand_reach:
                        continue
                    if not _los_clear(snap, eye, center, {o, c, (sx, sy + 1, sz)}):
                        continue
                    if c not in goals or d < goals[c][1]:
                        goals[c] = (o, d)
    return goals


def plan_path(snap, start, goals, origin, leash, seed, want=6, max_exp=30000):
    """
    Dijkstra。回傳 (路徑 cell 列表, 終點 cell, 對應的礦) 或 None。
    收集前幾個到得了的終點，再依「路徑成本 + 離礦的距離偏好」加權隨機挑一個（人不會總選最優）。
    """
    dist = {start: 0.0}
    parent = {start: None}
    heap = [(0.0, 0, start)]
    counter = 0
    found = []
    best = None
    exp = 0
    while heap and exp < max_exp:
        cst, _, cell = heapq.heappop(heap)
        if cst > dist.get(cell, 1e18):
            continue
        exp += 1
        if cell in goals:
            found.append((cst, cell))
            if best is None:
                best = cst
            if len(found) >= want:
                break
        if best is not None and cst > best + 4.0:
            break
        p = parent[cell]
        pd = (cell[0] - p[0], cell[2] - p[2]) if p else None
        in_cur = _inside(cell, origin, leash)
        d_cur = (cell[0] + 0.5 - origin[0]) ** 2 + (cell[2] + 0.5 - origin[2]) ** 2
        for nc, base in _moves(snap, cell):
            if not _inside(nc, origin, leash):
                d_n = (nc[0] + 0.5 - origin[0]) ** 2 + (nc[2] + 0.5 - origin[2]) ** 2
                if in_cur or d_n >= d_cur:
                    continue                                  # 不能走出活動範圍（已在範圍外時只允許往回走）
            step = base + _extra_cost(snap, nc, seed)
            if pd is not None:
                nd = (nc[0] - cell[0], nc[2] - cell[2])
                n1 = math.hypot(*pd) * math.hypot(*nd)
                if n1 > 0:
                    cosv = (pd[0] * nd[0] + pd[1] * nd[1]) / n1
                    step += 0.3 * (1 - cosv)                  # 轉彎有成本 → 路線比較順
            ncost = cst + step
            if ncost < dist.get(nc, 1e18):
                dist[nc] = ncost
                parent[nc] = cell
                counter += 1
                heapq.heappush(heap, (ncost, counter, nc))
    if not found:
        return None
    scored = [(c + 0.5 * abs(goals[g][1] - 3.0), g) for c, g in found]
    lo = min(s for s, _ in scored)
    weights = [math.exp(-(s - lo) / 1.2) for s, _ in scored]
    goal = random.choices([g for _, g in scored], weights)[0]
    path = []
    c = goal
    while c is not None:
        path.append(c)
        c = parent[c]
    path.reverse()
    return path, goal, goals[goal][0]


def build_cover(snap, ores, weights, origin, leash, eye_h, stand_reach):
    """
    每個「能站、眼睛碰得到、看得到」的站位，能同時照顧到幾顆礦（加權）。
    回傳 (cover{站位: 分數}, near{站位: (最近的礦, 距離)})。
    """
    cover, near = {}, {}
    for o in ores:
        w = weights.get(o, 1.0)
        center = (o[0] + 0.5, o[1] + 0.5, o[2] + 0.5)
        for sx in range(o[0] - 4, o[0] + 5):
            for sz in range(o[2] - 4, o[2] + 5):
                for sy in range(o[1] - 5, o[1] + 3):
                    c = (sx, sy, sz)
                    if not snap.walkable(sx, sy, sz) or not _inside(c, origin, leash):
                        continue
                    eye = (sx + 0.5, sy + eye_h, sz + 0.5)
                    d = math.dist(eye, center)
                    if d > stand_reach:
                        continue
                    if not _los_clear(snap, eye, center, {o, c, (sx, sy + 1, sz)}):
                        continue
                    cover[c] = cover.get(c, 0.0) + w
                    if c not in near or d < near[c][1]:
                        near[c] = (o, d)
    return cover, near


def plan_vantage(snap, start, cover, near, origin, leash, seed, spread=25.0, max_exp=20000, per_cover=10.0):
    """
    Dijkstra 展開到「比最近的候選站位多走 spread 成本」為止，
    再從所有候選站位挑「能照顧的礦數 − 路程/per_cover」最高的（加一點隨機）。
    回傳 (路徑, 終點, 最近的礦, 該站位分數) 或 None。
    """
    dist = {start: 0.0}
    parent = {start: None}
    heap = [(0.0, 0, start)]
    counter = 0
    found = []
    best = None
    exp = 0
    while heap and exp < max_exp:
        cst, _, cell = heapq.heappop(heap)
        if cst > dist.get(cell, 1e18):
            continue
        exp += 1
        if cell in cover:
            found.append((cst, cell))
            if best is None:
                best = cst
        if best is not None and cst > best + spread:
            break
        p = parent[cell]
        pd = (cell[0] - p[0], cell[2] - p[2]) if p else None
        in_cur = _inside(cell, origin, leash)
        d_cur = (cell[0] + 0.5 - origin[0]) ** 2 + (cell[2] + 0.5 - origin[2]) ** 2
        for nc, base in _moves(snap, cell):
            if not _inside(nc, origin, leash):
                d_n = (nc[0] + 0.5 - origin[0]) ** 2 + (nc[2] + 0.5 - origin[2]) ** 2
                if in_cur or d_n >= d_cur:
                    continue
            step = base + _extra_cost(snap, nc, seed)
            if pd is not None:
                nd = (nc[0] - cell[0], nc[2] - cell[2])
                n1 = math.hypot(*pd) * math.hypot(*nd)
                if n1 > 0:
                    step += 0.3 * (1 - (pd[0] * nd[0] + pd[1] * nd[1]) / n1)
            ncost = cst + step
            if ncost < dist.get(nc, 1e18):
                dist[nc] = ncost
                parent[nc] = cell
                counter += 1
                heapq.heappush(heap, (ncost, counter, nc))
    if not found:
        return None
    scored = [(cover[g] - c / per_cover, g) for c, g in found]
    top = max(sc for sc, _ in scored)
    weights = [math.exp((sc - top) / 0.6) for sc, _ in scored]
    goal = random.choices([g for _, g in scored], weights)[0]
    path = []
    c = goal
    while c is not None:
        path.append(c)
        c = parent[c]
    path.reverse()
    return path, goal, near[goal][0], cover[goal]


def _flat_clear(snap, path, i, j):
    y = path[i][1]
    if any(path[k][1] != y for k in range(i, j + 1)):
        return False
    ax, az = path[i][0] + 0.5, path[i][2] + 0.5
    bx, bz = path[j][0] + 0.5, path[j][2] + 0.5
    L = math.hypot(bx - ax, bz - az)
    if L < 1e-6:
        return True
    px, pz = -(bz - az) / L, (bx - ax) / L
    n = max(2, int(L / 0.15))
    for s in range(n + 1):
        f = s / n
        cx, cz = ax + (bx - ax) * f, az + (bz - az) * f
        for off in (0.0, 0.34, -0.34):        # 身體半寬 0.3，再留一點餘裕
            if not snap.walkable(math.floor(cx + px * off), y, math.floor(cz + pz * off)):
                return False
    return True


def smooth_path(snap, path):
    """同高度的路徑拉直成斜線；路點加一點橫向偏移（終點不動）。回傳 [(x,y,z)] 浮點座標。"""
    n = len(path)
    keep = [0]
    i = 0
    while i < n - 1:
        j = n - 1
        while j > i + 1 and not _flat_clear(snap, path, i, j):
            j -= 1
        keep.append(j)
        i = j
    pts = [(path[k][0] + 0.5, float(path[k][1]), path[k][2] + 0.5) for k in keep]
    out = [pts[0]]
    for a in range(1, len(pts) - 1):
        x, y, z = pts[a]
        dx, dz = pts[a + 1][0] - pts[a - 1][0], pts[a + 1][2] - pts[a - 1][2]
        L = math.hypot(dx, dz) or 1.0
        off = random.uniform(-0.14, 0.14)
        nx, nz = x - dz / L * off, z + dx / L * off
        # 只檢查中心格不夠：身體半寬 0.3，偏移後四個角都要踩得住、頭過得去，否則在窄通道/門口會卡牆
        if all(snap.walkable(math.floor(nx + ex), int(y), math.floor(nz + ez))
               for ex in (-0.32, 0.32) for ez in (-0.32, 0.32)):
            x, z = nx, nz
        out.append((x, y, z))
    if len(pts) > 1:
        out.append(pts[-1])
    return out


def seg_body_clear(snap, ax, az, bx, bz, level, half=0.3):
    """從 (ax,az) 走直線到 (bx,bz)，整個身體寬度（左右各 half）都踩得住、過得去嗎？"""
    L = math.hypot(bx - ax, bz - az)
    if L < 1e-6:
        return True
    px, pz = -(bz - az) / L, (bx - ax) / L
    n = max(1, int(L / 0.15))
    for i in range(n + 1):
        f = i / n
        cx, cz = ax + (bx - ax) * f, az + (bz - az) * f
        for off in (0.0, half, -half):
            if not snap.walkable(math.floor(cx + px * off), level, math.floor(cz + pz * off)):
                return False
    return True


def _seg_lateral(x, z, a, b):
    """點 (x,z) 到線段 a→b 的距離，以及線段上最近的點。"""
    abx, abz = b[0] - a[0], b[2] - a[2]
    L2 = abx * abx + abz * abz
    if L2 < 1e-9:
        return math.hypot(x - a[0], z - a[2]), (a[0], a[2])
    t = _clamp(((x - a[0]) * abx + (z - a[2]) * abz) / L2, 0.0, 1.0)
    px, pz = a[0] + abx * t, a[2] + abz * t
    return math.hypot(x - px, z - pz), (px, pz)


# ─────────────────────────────────────────────
# 走路控制
# ─────────────────────────────────────────────
def _yaw_to(x, z, tx, tz):
    return math.degrees(math.atan2(-(tx - x), tz - z))


def _lookahead(x, z, wps, idx, L):
    px, pz = x, z
    rem = L
    for i in range(idx, len(wps)):
        wx, wz = wps[i][0], wps[i][2]
        seg = math.hypot(wx - px, wz - pz)
        if seg >= rem and seg > 1e-6:
            f = rem / seg
            return px + (wx - px) * f, pz + (wz - pz) * f
        rem -= seg
        px, pz = wx, wz
    return wps[-1][0], wps[-1][2]


def _press(name, v):
    fn = getattr(minescript, "player_press_" + name, None)
    if fn:
        try:
            fn(v)
        except Exception:
            pass


def follow(waypoints, gaze, abort, eye_h=1.62, max_time=30.0, on_stuck=None, dbg=None, sneak=False, hop=None,
           clear=None):
    """
    沿 waypoints 走到最後一個點。回傳 "arrived" / "aborted" / "failed"。
    gaze: 抵達前視線會逐漸飄向的點（礦），讓到站後只需要小幅修正。
    abort(): 回傳 True 立刻放開所有按鍵並結束（視角停在當下，不補完）。
    on_stuck(pos): 卡住時呼叫，回傳新的 waypoints 就改走新路，回傳 None 則放棄。
    clear(x, z, tx, tz, level): 從目前位置直線走到 (tx,tz)，整個身體寬度都過得去嗎？
                  用來避免視線追著「前方預視點」切過牆角、貼著門框硬頂。
    """
    wps = list(waypoints)
    goal = wps[-1]
    # sneak=True：呼叫者已經按住蹲下；這裡只在要往下跳時暫時放開，落地後再按回去
    held = {"forward": False, "sprint": False, "jump": False, "sneak": bool(sneak)}

    def key(name, v):
        if held[name] != v:
            held[name] = v
            _press(name, v)

    yaw, pitch = HA.cur_view()
    base_pitch = random.uniform(5.0, 12.0)           # 走路時習慣的俯仰角
    tau = _clamp(random.uniform(0.11, 0.20) / HA.me.tempo, 0.08, 0.30)   # 視角追隨的慣性
    idx = 1
    t_start = last = time.perf_counter()
    best_rem, last_prog = 1e9, last
    jump_until = last_jump = 0.0
    sprinting = False
    prev = None
    speed_est = 0.0
    arrived_at = None
    idle_since = None
    stuck_n = 0
    recenter_until = 0.0     # 這段時間內改成「先橫移回路線上」
    fwd_since = None         # W 連續按住的起點
    try:
        while True:
            if abort():
                return "aborted"
            now = time.perf_counter()
            dt = _clamp(now - last, 0.001, 0.06)
            last = now
            if now - t_start > max_time:
                if dbg:
                    dbg("走太久，放棄")
                return "failed"

            x, y, z = minescript.player_position()
            vy = 0.0
            if prev is not None:
                speed_est += (math.hypot(x - prev[0], z - prev[2]) / dt - speed_est) * 0.3
                vy = (y - prev[1]) / dt
            prev = (x, y, z)

            if y < goal[1] - 4.5 or vy < -18.0:       # 掉下虛空/摔下去：立刻放開所有按鍵，不要一路走下去
                if dbg:
                    dbg("掉下去了，放棄")
                return "failed"

            while idx < len(wps) - 1 and math.hypot(x - wps[idx][0], z - wps[idx][2]) < 0.5 \
                    and abs(y - wps[idx][1]) < 1.3:
                idx += 1
            rem = math.hypot(x - goal[0], z - goal[2])
            stop_dist = 0.30 + 0.16 * speed_est             # 速度越快越早放開 W，靠滑行停下
            if arrived_at is None and rem < stop_dist and abs(y - goal[1]) < 1.5:
                arrived_at = now
            if arrived_at is None and rem < 0.9 and abs(y - goal[1]) < 1.5 and speed_est < 0.3 \
                    and not held["forward"]:
                idle_since = idle_since or now           # 夠近了，沒在走也沒在動
                if now - idle_since > 0.4:
                    arrived_at = now
            else:
                idle_since = None

            # ── 視線與視角 ──
            L = 1.6 * (1.25 if sprinting else 1.0)
            seg_a = wps[max(idx - 1, 0)]
            seg_b = wps[min(idx, len(wps) - 1)]
            lat, (cx_, cz_) = _seg_lateral(x, z, seg_a, seg_b)
            L *= _clamp(1.0 - lat / 0.6, 0.25, 1.0)    # 偏離路線越多，預視越短（先回到線上，不要斜著衝）
            if now < recenter_until and lat > 0.1:
                lx, lz = cx_, cz_                      # 貼牆卡住：先橫移回路線上最近的點
            else:
                lx, lz = _lookahead(x, z, wps, idx, L)
                if (clear is not None and abs(seg_a[1] - seg_b[1]) < 0.5 and abs(y - seg_b[1]) < 0.9):
                    lvl = int(round(seg_b[1]))
                    if not clear(x, z, lx, lz, lvl):   # 預視點的連線會切過牆角（身體過不去）
                        lx, lz = seg_b[0], seg_b[2]
                        if not clear(x, z, lx, lz, lvl):
                            lx, lz = seg_a[0], seg_a[2]   # 連下一個路點都過不去 → 先回上一個路點（格子中心）置中
            path_yaw = _yaw_to(x, z, lx, lz)
            ex, ey, ez = x, y + eye_h, z
            g_yaw, g_pitch = _calc_yaw_pitch((ex, ey - eye_h, ez), gaze, eye_h)
            if arrived_at is None:
                w = _clamp((4.0 - rem) / 2.5, 0.0, 1.0)          # 最後幾格視線先飄向礦
                # 只用 W 走路時，視線偏離前進方向就會被帶偏，所以偏移量隨接近終點縮小
                lim = 25.0 * _clamp((rem - 0.6) / 2.0, 0.25, 1.0)
                yaw_t = path_yaw + w * _clamp(_angle_diff(path_yaw, g_yaw), -lim, lim)
                pitch_t = base_pitch + (g_pitch - base_pitch) * w
            else:
                yaw_t, pitch_t = g_yaw, g_pitch                    # 到站後完全看向礦
            t = HA._now()
            yaw_t += 1.2 * _perlin_1d(t * 0.7, 41)
            pitch_t += 1.5 * _perlin_1d(t * 0.5, 42)
            a = 1 - math.exp(-dt / tau)
            step = _clamp(_angle_diff(yaw, yaw_t) * a, -520 * dt, 520 * dt)
            yaw += step
            pitch += (pitch_t - pitch) * a
            ty, tp = HA.tremor()
            HA._set(yaw + ty, pitch + tp)

            # ── 按鍵 ──
            if arrived_at is None:
                err = abs(_angle_diff(yaw, path_yaw))
                # 轉彎幅度大就先放開 W 把頭轉過去再走（遲滯：放開要 >lim_off，重按要 <lim_on），
                # 靠近終點時更保守，不會衝過頭又繞回來
                lim_off, lim_on = 38.0, 22.0
                want_w = (err < lim_on) if not held["forward"] else (err < lim_off)
                if sprinting:
                    sprinting = want_w and rem > 4.5 and err < 25.0
                else:
                    sprinting = (want_w and rem > 5.5 and err < 15.0 and HA.me.tempo > 0.6)
                if sneak:
                    sprinting = False                      # 蹲著不能衝刺
                key("forward", want_w)
                key("sprint", sprinting)
                if held["forward"]:
                    fwd_since = fwd_since if fwd_since is not None else now
                    if now - fwd_since > 0.45 and speed_est < 0.3 and now > recenter_until:
                        recenter_until = now + 0.7      # 頂著牆不動：先橫移置中，再繼續走
                        fwd_since = now + 0.7
                        if dbg:
                            dbg("貼牆，重新置中")
                else:
                    fwd_since = None
                if sneak:
                    nx_ = wps[min(idx, len(wps) - 1)]
                    dropping = nx_[1] - y < -0.6 and math.hypot(x - nx_[0], z - nx_[2]) < 1.6
                    key("sneak", not dropping)             # 蹲著走不下高低差，下階前放開一下

                nxt = wps[min(idx, len(wps) - 1)]
                rising = nxt[1] - y > 0.6 and math.hypot(x - nxt[0], z - nxt[2]) < 1.3
                if rising and now - last_jump > 0.45:
                    jump_until = now + random.uniform(0.12, 0.20)
                    last_jump = now
                # 直線、前方平坦且頭上 3 格都空 → 衝刺跳（落地就接著跳）
                grounded = abs(vy) < 0.5 and abs(y - wps[min(idx, len(wps) - 1)][1]) < 0.06
                if (hop and sprinting and not sneak and rem > 5.0 and err < 10.0 and not rising
                        and grounded and now - last_jump > 0.30 and hop(x, y, z, path_yaw)):
                    jump_until = now + random.uniform(0.10, 0.16)
                    last_jump = now
                key("jump", now < jump_until)

                if rem < best_rem - 0.08:
                    best_rem, last_prog = rem, now
                elif want_w and now - last_prog > 0.7 and now - last_jump > 0.5:
                    jump_until = now + random.uniform(0.12, 0.2)    # 卡住：先跳一下
                    last_jump = now
                if now - last_prog > 1.8:
                    stuck_n += 1
                    new = on_stuck((x, y, z)) if (on_stuck and stuck_n <= 2) else None
                    if not new:
                        if dbg:
                            dbg("卡住，放棄")
                        return "failed"
                    wps = list(new)
                    goal = wps[-1]
                    idx, best_rem, last_prog = 1, 1e9, now
            else:
                key("forward", False)
                key("sprint", False)
                key("jump", False)
                if sneak:
                    key("sneak", True)
                if now - arrived_at > 0.6 or (now - arrived_at > 0.15 and speed_est < 0.4):
                    return "arrived"

            time.sleep(random.uniform(HA.TICK_MIN, HA.TICK_MAX))
    finally:
        for k in list(held):
            if k == "sneak":
                if sneak and not held[k]:
                    _press("sneak", True)      # 結束時回到蹲下狀態，交還給主程式
                continue
            if held[k]:
                _press(k, False)


# ─────────────────────────────────────────────
# 高階：走到礦旁邊
# ─────────────────────────────────────────────
def _start_cell(snap, pos):
    x, y, z = pos
    for dy in (0, 1, -1):
        c = (math.floor(x), math.floor(y - 1e-6) + dy, math.floor(z))
        if snap.walkable(*c):
            return c
    return None


SCAN_RADII = (10, 20, 36, 60)     # 由近到遠分層讀取方塊；近處有礦就不用讀遠處
SCAN_RY    = 7                    # 上下讀幾層
MAX_ORES   = 40                   # 評估站位時最多考慮幾顆礦
STAND_EYE  = 1.62                 # 站著（趕路）的眼睛高度


def _prepare(names, origin, leash, skip, eye_h, stand_reach, pos, dbg=None,
             known=(), mine_eye=None, improve_min=0.0):
    """
    由近到遠分層讀方塊；在每一層裡評估「站在哪裡能同時照顧最多顆礦」，
    （礦數 − 路程）最高的站位就是目的地。已知會恢復的方塊（known）也算半顆。
    若現在站的位置已經差不多好（差距 < improve_min）就回傳 "__here__"。
    """
    ox, oy, oz = origin
    want = set(normalize(n) for n in names)
    skip = set(skip)
    known = set(tuple(k) for k in known)
    full = int(leash) + 3
    radii = [r for r in SCAN_RADII if r < full] + [full]
    pc = (math.floor(pos[0]), math.floor(pos[1]), math.floor(pos[2]))
    m_eye = mine_eye if mine_eye else eye_h
    why = "沒有符合的礦（活動範圍內）"

    def inleash(c):
        return (c[0] + 0.5 - ox) ** 2 + (c[1] + 0.5 - oy) ** 2 + (c[2] + 0.5 - oz) ** 2 <= leash ** 2

    for r in radii:
        t0 = time.time()

        def load(rr):
            sn = Snapshot(pc, rr, SCAN_RY)
            pr = [c for c, idn in sn.ids.items() if idn in want and c not in skip and inleash(c)]
            ps = set(pr)
            ex = [c for c in known if c in sn.ids and c not in ps and c not in skip and inleash(c)]
            wt = {c: 1.0 for c in pr}
            wt.update({c: 0.5 for c in ex})
            od = sorted(wt, key=lambda c: (c[0] + 0.5 - pos[0]) ** 2 + (c[2] + 0.5 - pos[2]) ** 2)[:MAX_ORES]
            return sn, pr, ex, wt, od

        snap, present, extra, weights, ores = load(r)
        if present and r < full:
            # 剛好在這一層找到礦：再往外多讀一圈，免得礦群被層的邊界切掉而低估站位
            snap, present, extra, weights, ores = load(min(full, r + 10))
        if dbg:
            dbg("掃描半徑 %d：讀 %d 格花 %.1fs，現有 %d 顆、已知會恢復 %d 顆" % (
                r, len(snap.grid), time.time() - t0, len(present), len(extra)))
        if not present:
            continue
        cover, near = build_cover(snap, ores, weights, origin, leash, m_eye, stand_reach)
        if not cover:
            why = "找到 %d 顆礦，但沒有能站著挖到的位置" % len(present)
            continue
        start = _start_cell(snap, pos)
        if start is None:
            return snap, None, "目前站的位置不在可行走範圍（腳下不是實心方塊？）"
        plan = plan_vantage(snap, start, cover, near, origin, leash, random.randrange(1 << 20))
        if plan is None:
            why = "找到 %d 顆礦，但走不到（被擋住或超出活動範圍）" % len(present)
            continue
        path, goal, ore, cv = plan
        here = cover.get(start, 0.0)
        if dbg:
            dbg("最佳站位 %s 可照顧 %.1f 顆（這裡 %.1f 顆），要走 %d 格" % (goal, cv, here, len(path) - 1))
        if goal == start or cv < here + improve_min:
            return snap, None, "__here__"
        return snap, (path, goal, ore), ""
    return None, None, why


def walk_to_ore(names, origin, leash, abort, skip=(), stand_reach=3.5, dbg=None, sneak=False,
                known=(), mine_eye=None, improve_min=0.0, on_start=None):
    """
    走到「能同時瞄準最多顆礦」的站位。趕路時不蹲：直線上衝刺 + 跳。
    回傳 (狀態, 說明, 礦的座標或 None)。
    狀態："arrived" / "aborted" / "failed" / "none" / "here"（現在的位置已經夠好，不用走）。
    on_start: 確定要走、開始走之前呼叫（用來放開蹲下、停止橫移等）。
    """
    eye_h = STAND_EYE
    pos = minescript.player_position()
    snap, plan, why = _prepare(names, origin, leash, skip, eye_h, stand_reach, pos, dbg,
                               known, mine_eye, improve_min)
    if plan is None:
        if why == "__here__":
            return "here", "這裡已經是最好的位置", None
        return "none", why, None
    path, goal, ore = plan
    wps = smooth_path(snap, path)
    gaze = (ore[0] + 0.5, ore[1] + 0.5, ore[2] + 0.5)
    cur = [snap]
    if dbg:
        dbg("目標礦 %s，約 %d 格路，%d 個路點" % (ore, len(path) - 1, len(wps)))

    def hop_ok(x, y, z, yaw):
        """衝刺跳要的條件：往前 ~4 格都是同高度可站的平地、頭上 3 格都空、沒有水。"""
        s_ = cur[0]
        yr = math.radians(yaw)
        dx, dz = -math.sin(yr), math.cos(yr)
        fy = int(round(y))
        for d in (0.0, 1.0, 2.0, 3.0, 4.2):
            c = (math.floor(x + dx * d), fy, math.floor(z + dz * d))
            if not s_.walkable(*c) or s_.at(c[0], fy + 2, c[2]) != "P" or s_.at(c[0], fy, c[2]) == "W":
                return False
        return True

    def clear_ok(x, z, tx, tz, level):
        return seg_body_clear(cur[0], x, z, tx, tz, level, 0.3)

    def replan(cur_pos):
        _snap, _plan, _why = _prepare(names, origin, leash, skip, eye_h, stand_reach, cur_pos, None,
                                      known, mine_eye, 0.0)
        if _plan is None:
            return None
        cur[0] = _snap
        if dbg:
            dbg("重新規劃路線")
        return smooth_path(_snap, _plan[0])

    if on_start:
        on_start()
    status = follow(wps, gaze, abort, eye_h=eye_h,
                    max_time=8.0 + 1.0 * len(path),
                    on_stuck=replan, dbg=dbg, sneak=False, hop=hop_ok, clear=clear_ok)
    return status, "", ore