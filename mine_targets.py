"""
mine_targets.py — 挖掘目標清單（JSON）

檔案格式 (mine_targets.json)：
{
  "current": "黑曜石+鑽石",              ← 目前使用的群組名稱
  "groups": {
    "gold_block":   ["minecraft:gold_block"],
    "黑曜石+鑽石":  ["minecraft:obsidian", "minecraft:diamond_block"]   ← 一個群組可放多種方塊，會同時挖
  }
}
- 群組名稱隨便取；按切換鍵時依 groups 的順序輪流切換。
- 方塊用遊戲內部名稱（minecraft: 前綴可省略）。
- 腳本執行中直接改這個檔案也會生效（約 1 秒內自動重載）。
"""

import copy
import json
import os
import time

_README = ("current=目前群組；groups=群組名稱→方塊清單（同一群組的方塊會一起挖）；"
           "切換鍵依 groups 順序輪流；執行中修改此檔會自動重載")

_DEFAULT_GROUPS = {"coal_block": ["minecraft:coal_block"]}

# 不能當成目標記錄的方塊（空氣、水、基岩——挖掘後會變基岩，記到就沒意義）
_BANNED = {
    "minecraft:air", "minecraft:cave_air", "minecraft:void_air",
    "minecraft:water", "minecraft:lava", "minecraft:bedrock",
}


def normalize(block_id) -> str:
    """'Block{minecraft:obsidian}[x=1]' / 'obsidian' / 'minecraft:obsidian' → 'minecraft:obsidian'"""
    s = str(block_id).strip().lower()
    if "{" in s and "}" in s:
        s = s[s.index("{") + 1:s.index("}")]
    s = s.split("[")[0].strip()
    if s and ":" not in s:
        s = "minecraft:" + s
    return s


def short_name(block_id: str) -> str:
    return block_id.split(":", 1)[1] if ":" in block_id else block_id


class TargetStore:
    def __init__(self, path):
        self.path = path
        self.groups = {}
        self.current = None
        self.error = None
        self._mtime = 0.0
        self._last_check = 0.0
        self._loaded_once = False
        self.load()

    # ── 讀寫 ──────────────────────────────────
    def _apply(self, data: dict):
        groups = {}
        for name, blocks in (data.get("groups") or {}).items():
            if isinstance(blocks, str):
                blocks = [blocks]
            norm = [normalize(b) for b in blocks if str(b).strip()]
            norm = [b for b in dict.fromkeys(norm) if b]     # 去重、保持順序
            if norm:
                groups[str(name)] = norm
        if not groups:
            groups = copy.deepcopy(_DEFAULT_GROUPS)
        cur = data.get("current")
        if cur not in groups:
            cur = next(iter(groups))
        self.groups, self.current = groups, cur

    def load(self):
        """讀檔。不存在就建立預設檔；壞掉的 JSON 不會被覆蓋，沿用上一份好的設定。"""
        self.error = None
        try:
            with open(self.path, encoding="utf-8") as f:
                data = json.load(f)
            self._apply(data)
            self._loaded_once = True
        except FileNotFoundError:
            self._apply({"groups": copy.deepcopy(_DEFAULT_GROUPS)})
            self._loaded_once = True
            self.save()
        except Exception as e:
            self.error = "目標檔讀取失敗（沿用上一份設定）: %s" % e
            if not self._loaded_once:
                self._apply({"groups": copy.deepcopy(_DEFAULT_GROUPS)})
        try:
            self._mtime = os.path.getmtime(self.path)
        except OSError:
            self._mtime = 0.0

    def save(self):
        data = {"_readme": _README, "current": self.current, "groups": self.groups}
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp, self.path)
        try:
            self._mtime = os.path.getmtime(self.path)   # 自己寫的不要再觸發重載
        except OSError:
            pass

    def reload_if_changed(self, min_interval=1.0) -> bool:
        """檔案被外部修改就重載，回傳是否重載了。"""
        now = time.time()
        if now - self._last_check < min_interval:
            return False
        self._last_check = now
        try:
            m = os.path.getmtime(self.path)
        except OSError:
            return False
        if m == self._mtime:
            return False
        self.load()
        return True

    # ── 查詢 ──────────────────────────────────
    def current_blocks(self) -> list:
        return list(self.groups.get(self.current, []))

    def summary(self) -> str:
        return "%s → %s" % (self.current, ", ".join(short_name(b) for b in self.current_blocks()))

    # ── 操作 ──────────────────────────────────
    def cycle(self) -> str:
        """切到下一個群組並存檔，回傳新群組名稱。"""
        names = list(self.groups)
        i = names.index(self.current) if self.current in names else -1
        self.current = names[(i + 1) % len(names)]
        self.save()
        return self.current

    def add_block(self, block_id, switch=True):
        """
        記錄方塊成為一個新群組（群組名 = 方塊短名）。
        回傳 (狀態, 群組名)：狀態為 "added" / "exists" / "banned"。
        """
        bid = normalize(block_id)
        if not bid or bid in _BANNED:
            return "banned", short_name(bid) if bid else ""
        name = short_name(bid)
        if name in self.groups:
            if switch:
                self.current = name
                self.save()
            return "exists", name
        self.groups[name] = [bid]
        if switch:
            self.current = name
        self.save()
        return "added", name
