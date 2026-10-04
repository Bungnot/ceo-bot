# app.py — LINE Bungfai Bot (Flask + line-bot-sdk)
# (c) SITTIPONG — hardened, anti-abuse, anti-kick, 1-bill-per-round, @mention admin/mod, uid lookup

from dotenv import load_dotenv
load_dotenv()


from waitress import serve

import os, re, time, base64, json, tempfile
from datetime import datetime
from hmac import new as hmac_new, compare_digest
from hashlib import sha256
from html import escape as html_escape
from math import ceil, floor
from collections import deque
from functools import lru_cache
import threading


from contextlib import contextmanager

# ==== REGEX (precompiled) ====
R_PARSE_BET = re.compile(r"^([ลสยต])\s*[\/\s]*([0-9]+)$", re.IGNORECASE)
R_O         = re.compile(r"^\s*o\b", re.IGNORECASE)
R_ANN = re.compile(
    r"^\s*([^\s].+?)\s*ล\s*(\d+)\s*[-/]\s*(\d+)\s*ย\s*(\d+)\s*[-/]\s*(\d+)\s*$",
    re.IGNORECASE
)
R_O_ANN = re.compile(
    r"^\s*o\s+(.+?)\s*ล\s*(\d+)\s*[-/]\s*(\d+)\s*ย\s*(\d+)\s*[-/]\s*(\d+)\s*$",
    re.IGNORECASE
)
R_CLEAR     = re.compile(r"^(clear|reset)\b", re.IGNORECASE)
R_CM        = re.compile(r"^cm$", re.IGNORECASE)
R_CALL      = re.compile(r"^call$", re.IGNORECASE)
R_UID       = re.compile(r"^uid\b", re.IGNORECASE)
R_SET_RESULT= re.compile(r"^[sS]\s*(.+)$")
R_MUTING    = re.compile(r"^(ban|unban|mute|unmute)\b(?:\s+(.*))?$", re.IGNORECASE)
R_CANCEL_BY_CID = re.compile(r"^x\s+(\d+)$", re.IGNORECASE)
R_ADMIN_ADD = re.compile(
    r"^\s*(?:admin(?:\s+add)?|เพิ่มแอดมิน)(?:\s+|(?=@)|$)",
    re.IGNORECASE
)
R_ADMIN_DEL   = re.compile(r"^\s*(?:admin\s+del|ลบแอดมิน)\b", re.IGNORECASE)
R_ADMIN_LIST  = re.compile(r"^\s*(?:admin\s+list|เช็คแอดมิน|รายชื่อแอดมิน)\s*$", re.IGNORECASE)
R_CLOSE_TH    = re.compile(r"^(ปิดรอบ|หยุดแทง|ปิด)$")
R_YCONFIRM    = re.compile(r"^(?:T/|/Y|Y)\s*$", re.IGNORECASE)
R_CLEAR_PROFIT = re.compile(r"^ล้างกำไร$", re.IGNORECASE)
R_GETID = re.compile(r"^getid\b", re.IGNORECASE)
R_DEL_USER = re.compile(r"^del\s+(\d+)$", re.IGNORECASE)



# ====== GLOBAL LOCKS ======
_users_lock = threading.RLock()
_rooms_lock = threading.RLock()

# ====== WEBHOOK IDEMPOTENCY / กัน LINE retry ประมวลผลซ้ำ ======
# LINE อาจส่ง event เดิมซ้ำได้ ถ้า webhook ตอบช้า/timeout
_processed_msg_lock = threading.RLock()
_processed_msg_ids = {}  # message_id -> timestamp
PROCESSED_MSG_TTL_SEC = int(os.getenv("PROCESSED_MSG_TTL_SEC", "900"))

def already_processed_message(message_id: str) -> bool:
    """คืน True ถ้า message id นี้เคยถูกประมวลผลแล้ว"""
    if not message_id:
        return False
    now = time.time()
    with _processed_msg_lock:
        # เก็บ cache ให้เล็ก ไม่ให้ RAM บวม
        for mid, ts in list(_processed_msg_ids.items()):
            if now - ts > PROCESSED_MSG_TTL_SEC:
                _processed_msg_ids.pop(mid, None)

        if message_id in _processed_msg_ids:
            return True

        _processed_msg_ids[message_id] = now
        return False


def has_active_bet(uid):
    for stx in rooms.values():
        if uid in stx.get("bet_index", {}):
            return True
    return False


@contextmanager
def with_users_lock():
    _users_lock.acquire()
    try:
        yield
    finally:
        _users_lock.release()

@contextmanager
def with_rooms_lock():
    _rooms_lock.acquire()
    try:
        yield
    finally:
        _rooms_lock.release()


from flask import Flask, request, make_response
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError
from linebot.models import (
    MessageEvent, TextMessage, TextSendMessage,
    FlexSendMessage, UnsendEvent,
    MemberJoinedEvent, MemberLeftEvent,
    ImageMessage,   # <<< เพิ่มบรรทัดนี้
)


# ====== CONFIG (ปรับได้) ======
DEPOSIT_URL = os.getenv("DEPOSIT_URL", "https://page.line.me/957gvogc")
PROFIT_RATE = float(os.getenv("PROFIT_RATE", "0.95"))   # ชนะหัก 5% = จ่ายสุทธิ 1:0.95
MIDDLE_FEE  = float(os.getenv("MIDDLE_FEE",  "0.03"))   # หักเมื่อคืนเงิน (กลาง/เสมอแบบหัก)
MIN_BET = int(os.getenv("MIN_BET", "30"))
MAX_BET = int(os.getenv("MAX_BET", "10000"))
USER_SIDE_CAP = {"HI": 10000, "LO": 10000}
SIDE_CAP      = {"HI": 50000, "LO": 30000}
ROUND_CAP     = 80000

# ====== SIMPLE PER-USER COOLDOWN (anti-spam reply gap) ======
REPLY_COOLDOWN_SEC = int(os.getenv("REPLY_COOLDOWN_SEC", "6"))
_LAST_REPLIED_AT = {}        # scope_key -> epoch seconds
_COOLDOWN_LOCK = threading.Lock()  # <<< เพิ่มตัวล็อก

def _should_reply_now(scope_key: str) -> bool:
    """
    ป้องกันตอบถี่เกินไปแบบอะตอมิก: เช็ค + อัปเดต ภายใต้ล็อกเดียวกัน
    scope_key = คีย์สำหรับคูลดาวน์ (เช่น uid:room)
    """
    if REPLY_COOLDOWN_SEC <= 0:
        return True
    now = _now()
    with _COOLDOWN_LOCK:  # <<< ล็อกกันชนกันข้ามเธรด
        last = _LAST_REPLIED_AT.get(scope_key, 0)
        if (now - last) < REPLY_COOLDOWN_SEC:
            return False
        _LAST_REPLIED_AT[scope_key] = now
        return True



# ====== PERSISTENCE (users + nextCustomerId) ======
DATA_DIR = os.getenv("DATA_DIR", "./data")
os.makedirs(DATA_DIR, exist_ok=True)

# Copy default data files if not exists
import shutil
for _fname in ["users.json", "admins.json"]:
    _src = os.path.join("data", _fname)
    _dst = os.path.join(DATA_DIR, _fname)
    if not os.path.exists(_dst) and os.path.exists(_src):
        shutil.copy2(_src, _dst)
        
# ====== LAST SETTLE (free backoffice) ======
LAST_SETTLE_JSON = os.path.join(DATA_DIR, "last_settle_global.json")

def save_last_settle(payload: dict):
    """เก็บสรุปล่าสุดไว้ให้หลังบ้านเรียกดูได้ โดยไม่ต้อง push (ประหยัดโควต้า)"""
    try:
        _atomic_write_json(LAST_SETTLE_JSON, payload)
    except Exception:
        app.logger.exception("save_last_settle failed")

def load_last_settle():
    try:
        if not os.path.exists(LAST_SETTLE_JSON):
            return None
        with open(LAST_SETTLE_JSON, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        app.logger.exception("load_last_settle failed")
        return None

def settle_payload_to_text(p: dict) -> str:
    """แปลง payload เป็นข้อความสั้น ๆ (Text)
    หมายเหตุ: แสดง 'ได้เสีย' = payout - stake (มุมมองลูกค้า)
             และ 'กำไรรอบนี้' = มุมมองเจ้ามือ (profit = stake - payout)
    """
    try:
        def _fmt(n):
            try:
                # รองรับ int/float/str
                if n is None:
                    n = 0
                n = float(n)
                if n.is_integer():
                    return f"{int(n):,}"
                return f"{n:,.2f}"
            except Exception:
                return str(n)

        def _signed(n):
            try:
                n = float(n or 0)
            except Exception:
                n = 0
            return f"+{_fmt(n)}" if n >= 0 else f"-{_fmt(abs(n))}"

        round_no = p.get("round")
        camp = p.get("camp_name") or "-"
        code = p.get("code") or "-"
        profit = p.get("profit", 0)  # มุมมองเจ้ามือ
        accum = p.get("accum") or {}
        net = accum.get("net", 0)
        ts = p.get("ts_iso") or ""

        rows = p.get("rows") or []
        lines = []
        for r in rows[:12]:  # กันยาวเกิน
            name = r.get("name") or r.get("uid") or "-"
            stake = r.get("stake", 0) or 0
            payout = r.get("payout", 0) or 0
            pl = payout - stake  # มุมมองลูกค้า (ได้เสีย)
            # ถ้ามี bet ก็แสดงแบบสั้น ๆ
            bet = (r.get("bet") or "").strip()
            bet_txt = f" [{bet}]" if bet else ""
            lines.append(f"- {name}{bet_txt} {_signed(pl)}")
        if len(rows) > 12:
            lines.append(f"...และอีก {len(rows)-12} ราย")

        return (
            f"📌 สรุปผลรอบ {round_no} | ค่าย: {camp} | ผล: {code}\n"
            f"ลูกค้า: {len(rows)} คน\n"
            f"💰 กำไรรอบนี้ (เจ้ามือ): {_signed(profit)}\n"
            f"🧮 กำไรสุทธิสะสม: {_signed(net)}\n"
            f"🕒 เวลา: {ts}\n\n"
            + ("\n".join(lines) if lines else "")
        ).strip()
    except Exception:
        app.logger.exception("settle_payload_to_text failed")
        return "📌 สรุปผลล่าสุด (แปลงข้อความไม่สำเร็จ)"


USERS_JSON = os.path.join(DATA_DIR, "users.json")
_user_store_lock = threading.Lock()


# --- JSON encoder/decoder with orjson fallback ---
try:
    import orjson as _orjson
    def _dumps_bytes(obj) -> bytes:
        return _orjson.dumps(obj)               # ได้ bytes เลย
    def _loads_bytes(buf: bytes):
        return _orjson.loads(buf)
except Exception:
    import json as _json
    def _dumps_bytes(obj) -> bytes:
        # ให้ได้ bytes เหมือน orjson
        return _json.dumps(
            obj,
            ensure_ascii=False,
            separators=(",", ":")
        ).encode("utf-8")
    def _loads_bytes(buf: bytes):
        return _json.loads(buf.decode("utf-8"))

def _atomic_write_json(path: str, data: dict):
    dirname = os.path.dirname(path) or "."
    fd, tmp = tempfile.mkstemp(prefix=".tmp_", dir=dirname)
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(_dumps_bytes(data))
        os.replace(tmp, path)  # atomic replace
    except Exception:
        try:
            os.remove(tmp)
        except Exception:
            pass
        raise


# ====== ADMIN ACTION GUARD ======
# กันแอดมินกดคำสั่งซ้อน ทั้งในระดับ thread และ process เดียวกัน
# ใช้ไฟล์ state เพื่อกันเคสที่ server มีหลาย worker แล้ว memory rooms ไม่ sync กัน
_ADMIN_ACTION_STATE_JSON = os.path.join(DATA_DIR, "admin_action_state.json")
_ADMIN_ACTION_LOCK_FILE = os.path.join(DATA_DIR, ".admin_action.lock")
_ADMIN_ACTION_TTL_SEC = int(os.getenv("ADMIN_ACTION_TTL_SEC", "86400"))
_admin_action_thread_lock = threading.RLock()

@contextmanager
def _admin_action_file_lock():
    os.makedirs(DATA_DIR, exist_ok=True)
    with _admin_action_thread_lock:
        with open(_ADMIN_ACTION_LOCK_FILE, "a+b") as f:
            locked = False
            try:
                try:
                    import fcntl
                    fcntl.flock(f.fileno(), fcntl.LOCK_EX)
                    locked = True
                except Exception:
                    # Windows หรือ environment ที่ไม่มี fcntl จะยังกันซ้อนใน process ด้วย thread lock
                    locked = False
                yield
            finally:
                if locked:
                    try:
                        import fcntl
                        fcntl.flock(f.fileno(), fcntl.LOCK_UN)
                    except Exception:
                        pass

def _load_admin_action_state() -> dict:
    try:
        if not os.path.exists(_ADMIN_ACTION_STATE_JSON):
            return {}
        with open(_ADMIN_ACTION_STATE_JSON, "rb") as f:
            data = _loads_bytes(f.read())
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def _save_admin_action_state(data: dict):
    _atomic_write_json(_ADMIN_ACTION_STATE_JSON, data)

def _admin_action_key(action: str, room_id: str, pair_no) -> str:
    raw = f"{action}|{room_id}|{pair_no}".encode("utf-8")
    return sha256(raw).hexdigest()

def claim_round_action(action: str, room_id: str, pair_no, uid: str = None):
    """จอง action ต่อห้อง/รอบแบบ atomic
    return (True, None) ถ้าจองสำเร็จ
    return (False, old_info) ถ้ามีคนทำ action นี้ไปแล้ว
    """
    if not room_id or not pair_no:
        return True, None

    now = time.time()
    with _admin_action_file_lock():
        data = _load_admin_action_state()

        # ล้างข้อมูลเก่า กันไฟล์โตและกันรอบเก่าค้างข้ามวัน
        for k, v in list(data.items()):
            try:
                if now - float(v.get("ts", 0)) > _ADMIN_ACTION_TTL_SEC:
                    data.pop(k, None)
            except Exception:
                data.pop(k, None)

        k = _admin_action_key(action, str(room_id), pair_no)
        old = data.get(k)
        if old:
            _save_admin_action_state(data)
            return False, old

        data[k] = {
            "action": action,
            "room_id": str(room_id),
            "pair_no": pair_no,
            "uid": uid,
            "ts": now,
            "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        }
        _save_admin_action_state(data)
        return True, None

def release_round_action(action: str, room_id: str, pair_no):
    """ปลดล็อก action เฉพาะกรณีตั้งใจกลับมาเปิดรอบเดิม เช่น R/RESUME"""
    if not room_id or not pair_no:
        return
    with _admin_action_file_lock():
        data = _load_admin_action_state()
        data.pop(_admin_action_key(action, str(room_id), pair_no), None)
        _save_admin_action_state(data)

def has_round_action(action: str, room_id: str, pair_no) -> bool:
    """เช็คว่า action ของห้อง/รอบนี้เคยถูกจองไว้แล้วหรือยัง"""
    if not room_id or not pair_no:
        return False
    now = time.time()
    with _admin_action_file_lock():
        data = _load_admin_action_state()

        changed = False
        for k, v in list(data.items()):
            try:
                if now - float(v.get("ts", 0)) > _ADMIN_ACTION_TTL_SEC:
                    data.pop(k, None)
                    changed = True
            except Exception:
                data.pop(k, None)
                changed = True

        if changed:
            _save_admin_action_state(data)

        return _admin_action_key(action, str(room_id), pair_no) in data

def get_active_round_action(action: str, room_id: str):
    """คืน action ที่ยังค้างอยู่ของห้องนี้ 1 รายการ เช่น rollback ค้างรอบใดอยู่"""
    if not room_id:
        return None
    now = time.time()
    room_id = str(room_id)
    with _admin_action_file_lock():
        data = _load_admin_action_state()

        changed = False
        for k, v in list(data.items()):
            try:
                if now - float(v.get("ts", 0)) > _ADMIN_ACTION_TTL_SEC:
                    data.pop(k, None)
                    changed = True
            except Exception:
                data.pop(k, None)
                changed = True

        if changed:
            _save_admin_action_state(data)

        candidates = [
            v for v in data.values()
            if v.get("action") == action and str(v.get("room_id")) == room_id
        ]
        if not candidates:
            return None
        # เอารายการล่าสุด/ใหญ่สุดตามเวลา เพื่อกันกรณีข้อมูลเก่าหลงเหลือ
        candidates.sort(key=lambda x: float(x.get("ts", 0) or 0), reverse=True)
        return candidates[0]


def _pending_rollback_snapshot_path(room_id: str) -> str:
    raw = str(room_id or "").encode("utf-8")
    h = sha256(raw).hexdigest()
    return os.path.join(DATA_DIR, f"pending_rollback_{h}.json")


def save_pending_rollback_snapshot(room_id: str, round_no: int, uid: str, st: dict):
    """เก็บสถานะก่อนย้อน เพื่อให้คำสั่ง 'ยกเลิกย้อน <รอบ>' คืนกลับได้อย่างปลอดภัย"""
    if not room_id or not round_no:
        return
    try:
        with with_users_lock():
            users_snapshot = _loads_bytes(_dumps_bytes(users))
        room_snapshot = _loads_bytes(_dumps_bytes(st))
        payload = {
            "round_no": int(round_no),
            "room_id": str(room_id),
            "uid": uid,
            "ts": time.time(),
            "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "users": users_snapshot,
            "room_state": room_snapshot,
            "metrics": _loads_bytes(_dumps_bytes(METRICS)),
            "last_settle": load_last_settle(),
        }
        _atomic_write_json(_pending_rollback_snapshot_path(room_id), payload)
    except Exception:
        app.logger.exception("save_pending_rollback_snapshot failed")
        raise


def load_pending_rollback_snapshot(room_id: str):
    try:
        path = _pending_rollback_snapshot_path(room_id)
        if not os.path.exists(path):
            return None
        with open(path, "rb") as f:
            data = _loads_bytes(f.read())
        return data if isinstance(data, dict) else None
    except Exception:
        app.logger.exception("load_pending_rollback_snapshot failed")
        return None


def clear_pending_rollback_snapshot(room_id: str):
    try:
        path = _pending_rollback_snapshot_path(room_id)
        if os.path.exists(path):
            os.remove(path)
    except Exception:
        app.logger.exception("clear_pending_rollback_snapshot failed")


def clear_round_action_guard(room_id: str = None):
    """ใช้ตอน clear/reset เพื่อล้าง guard ที่ค้างอยู่"""
    with _admin_action_file_lock():
        data = _load_admin_action_state()
        if room_id is None:
            data.clear()
        else:
            room_id = str(room_id)
            data = {k: v for k, v in data.items() if str(v.get("room_id")) != room_id}
        _save_admin_action_state(data)





def save_users_persist():
    # ไม่เขียนทันที — แค่จุด event ให้ worker ไปเขียนเป็นก้อน
    _save_event.set()



def load_users_persist():
    global nextCustomerId, users
    try:
        if not os.path.exists(USERS_JSON): return
        with _user_store_lock:
            with open(USERS_JSON, "rb") as f:
                data = _loads_bytes(f.read())


        disk_users = data.get("users", {})
        disk_next = int(data.get("nextCustomerId", 0) or 0)
        with with_users_lock():
            if isinstance(disk_users, dict):
                users.clear()
                for k, v in disk_users.items():
                    users[k] = {
                        "uid": v.get("uid", k),
                        "cid": int(v.get("cid", 0) or 0),
                        "name": v.get("name", "ผู้เล่น"),
                        "pictureUrl": v.get("pictureUrl"),
                        "credit": int(v.get("credit", 0) or 0),
                    }
            if disk_next > 0:
                nextCustomerId = disk_next
    except Exception:
        try:
            app.logger.exception("load_users_persist failed")
        except Exception:
            pass





# ====== LINE BOOTSTRAP ======
CHANNEL_ACCESS_TOKEN = os.getenv("LINE_CHANNEL_ACCESS_TOKEN", "REPLACE_ME")
CHANNEL_SECRET = os.getenv("LINE_CHANNEL_SECRET", "REPLACE_ME")

ADMIN_IDS = [s.strip() for s in os.getenv(
    "ADMIN_IDS", "U8e996c055ed55573b042f8119bcc5844,U3ae8e637f4da0559d906847535e35fbb,U24298c1e9f43986904ee6d3e3d10267d,Ua139e5d2bcd9606877829acc2fdcd1ec,Ua4dfc588cd253940e13c4e81188d69e8,U458603076cc4dee45ff1273e1f634ef2"
).split(",") if s.strip()]

BACKOFFICE_GROUP_IDS = {  # กลุ่มหลังบ้าน (รับสรุปพร้อมกำไรสุทธิ) — ตั้งใน env คั่นด้วย ,
    s.strip() for s in os.getenv("BACKOFFICE_GROUP_IDS", "Cab9fd7703ec00d036fa8ee94e4a59b80").split(",") if s.strip()
}

BASE_URL = os.getenv("BASE_URL", "https://example.ngrok-free.app")

BANK = {
    "brand": os.getenv("BANK_BRAND", "กสิกรไทย"),
    "accountNo": os.getenv("BANK_ACCOUNT", "115-336-6086"),
    "owner": os.getenv("BANK_OWNER", "กิตติพงษ์ ราชวันดี"),
}
PORT = int(os.getenv("PORT", "5000"))

# ====== LINE BOT API TIMEOUT (แก้ safe_reply timeout ไป api.line.me) ======
# ค่าเริ่มต้นของ SDK มักสั้นเกินไป ทำให้ SSL/read timeout ง่ายตอนเน็ตช้า
LINE_API_TIMEOUT = (
    int(os.getenv("LINE_CONNECT_TIMEOUT", "15")),  # connect timeout (เพิ่มจาก 10 → 15)
    int(os.getenv("LINE_READ_TIMEOUT", "30")),     # read timeout
)
LINE_API_RETRY = int(os.getenv("LINE_API_RETRY", "2"))  # จำนวนครั้ง retry เมื่อ timeout

line_bot_api = LineBotApi(CHANNEL_ACCESS_TOKEN, timeout=LINE_API_TIMEOUT)
handler = WebhookHandler(CHANNEL_SECRET)
app = Flask(__name__)

# ====== STATE ======
rooms = {}   # room_key -> state
users = {}   # uid -> {uid,cid,name,pictureUrl,credit}
nextCustomerId = 201


PLAY_HELP_TEXT = (
"กติกาการเล่น\n"
"ต/1000 = แทงต่ำ 1000 บาท\n"
"ย/1000 = แทงต่ำ 1000 บาท\n"
"ล/1000 = แทงสูง 1000 บาท\n"
"ส/1000 = แทงสูง 1000 บาท\n"
"สามารถใส่เครื่องหมาย /\n"
"หรือไม่ใส่ก็ได้ \n\n"
"✅ ชนะหัก 5% (จ่ายสุทธิ 1:0.95)\n"
"⛔ ตส หัก 3%\n"
"⛔ ตจ หัก 3%\n"
"⛔ ม = ไม่หัก\n\n"

"___________________\n\n"

"👉 รับสูงสุดยั้ง 30,000 ต่อ 1 บั้ง\n"
"👉 รับสูงสุดไล่ 50,000 ต่อ 1 บั้ง\n"
"👉 แทงขั้นต่ำ ยั้ง 30-10,000 ต่อ \n"
"1คน\n"
"🫱🏻 แทงขั้นต่ำ ไล่ 30-10,000 ต่อ 1คน\n\n"
"📢 เพิ่ม ID ตัวเอง พิมพ์ ADD\n"
"📢 ดูยอดบัญชีตัวเอง กด C\n"
"📢 ยกเลิกการแทง กด X\n\n\n"
"***ห้ามเว้นวรรค ***\n"
"🙏พิมพ์ยอดการเล่นให้ถูกต้องด้วยนะครับ🙏\n"
"ตัวอย่าง:\n"
"ล/1000 ส/1000 ล1000 ส1000=ไล่\n"
"ย/1000 ต/1000 ย1000 ต1000=ยั้ง\n"
"(ไม่ต้องเว้นวรรค)\n\n"
"หมายเหตุ // 💥กรณีออกราคา บั้งไฟ หลังปิด ถือว่า จาวทุกรณี\n"
"และสนามราคารูด ทางกลุ่มจะไม่เปิดราคา จาวทุกกรณี 💥"
)

PLAY_HELP_COMMANDS = {
    "วิธีเล่น",
    "เล่นยังไง",
    "เล่นไง",
    "วิธีการเล่น",
    "เล่นแบบใด",
}

# ====== PEH / เปะ ======
TARGET_GROUP_NAME = os.getenv(
    "TARGET_GROUP_NAME",
    "🚀เซิ้งบั้งไฟ V2 •"
).strip()

PEH_LIST = {}   # dict[source_key] = ["ข้อความ..."]

# ====== สถานะของรายการ "เปะ" ======
PEH_STATUS = {
    "✅": {"key": "win",  "label": "ชนะ"},
    "❌": {"key": "lose", "label": "แพ้"},
    "⛔": {"key": "draw", "label": "จาว"},
}

# จำนวนรายการต่อ 1 หน้าใน Carousel
PEH_ITEMS_PER_PAGE = 20

# LINE Carousel รองรับสูงสุด 12 bubbles ต่อ 1 carousel
PEH_MAX_BUBBLES_PER_CAROUSEL = 12

# ===== Debounced Saver =====
_save_event = threading.Event()

def _save_users_snapshot():
    with with_users_lock():
        payload = {"nextCustomerId": nextCustomerId, "users": users}
    _atomic_write_json(USERS_JSON, payload)

def _persist_worker():
    while True:
        _save_event.wait()
        time.sleep(0.35)  # รวมคำสั่งภายใน 350ms ก่อนเขียน
        _save_users_snapshot()
        _save_event.clear()

threading.Thread(target=_persist_worker, daemon=True).start()


# โหลดข้อมูลลูกค้า+เครดิตจากดิสก์ (ถ้ามี)
load_users_persist()


# ====== AUTO DELETE: ลบไฟล์ Backup_round เมื่อครบ 1 วัน แบบไม่ต้องเช็คทุกชั่วโมง ======
# วิธีทำงาน:
# - ตอนสร้างไฟล์ backup_round_*.json จะตั้ง Timer ให้ลบไฟล์นั้นหลังครบ 24 ชั่วโมงพอดี
# - ตอนเปิดบอท จะสแกนไฟล์ backup_round ที่ค้างอยู่ 1 ครั้ง แล้วตั้งเวลาลบตามอายุไฟล์ที่เหลือ
# - ไม่มี worker เช็คซ้ำทุก 1 ชั่วโมง
BACKUP_ROUND_KEEP_SEC = int(os.getenv("BACKUP_ROUND_KEEP_SEC", str(24 * 60 * 60)))
BACKUP_ROUND_PREFIXES = ("backup_round", "backup-round")
_backup_round_timers = {}
_backup_round_timers_lock = threading.RLock()


def _is_backup_round_file(filename: str) -> bool:
    low = (filename or "").lower()
    return low.endswith(".json") and low.startswith(BACKUP_ROUND_PREFIXES)


def _delete_backup_round_file(path: str):
    """ลบไฟล์ backup_round 1 ไฟล์ เมื่อครบเวลา โดยไม่แตะไฟล์อื่นใน data"""
    try:
        filename = os.path.basename(path)
        if not _is_backup_round_file(filename):
            return

        if os.path.isfile(path):
            os.remove(path)
            app.logger.info("Deleted backup_round after 1 day: %s", filename)

    except FileNotFoundError:
        pass
    except Exception:
        app.logger.exception("delete backup_round failed: %s", path)
    finally:
        with _backup_round_timers_lock:
            _backup_round_timers.pop(path, None)


def schedule_backup_round_delete(path: str):
    """ตั้งเวลาลบไฟล์ backup_round เมื่ออายุครบ 1 วันพอดี"""
    try:
        if not path:
            return

        filename = os.path.basename(path)
        if not _is_backup_round_file(filename):
            return

        if not os.path.isfile(path):
            return

        age_sec = time.time() - os.path.getmtime(path)
        delay_sec = max(0, BACKUP_ROUND_KEEP_SEC - age_sec)

        # ถ้าไฟล์เกิน 1 วันแล้ว ให้ลบทันที
        if delay_sec <= 0:
            _delete_backup_round_file(path)
            return

        with _backup_round_timers_lock:
            old_timer = _backup_round_timers.pop(path, None)
            if old_timer:
                old_timer.cancel()

            timer = threading.Timer(delay_sec, _delete_backup_round_file, args=(path,))
            timer.daemon = True
            _backup_round_timers[path] = timer
            timer.start()

        app.logger.info("Scheduled backup_round delete: %s in %.0f sec", filename, delay_sec)

    except Exception:
        app.logger.exception("schedule_backup_round_delete failed: %s", path)


def schedule_existing_backup_round_deletes():
    """ตอนเปิดบอท: ตั้งเวลาลบ backup_round ที่มีอยู่เดิม 1 ครั้งเท่านั้น"""
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        for filename in os.listdir(DATA_DIR):
            if not _is_backup_round_file(filename):
                continue
            schedule_backup_round_delete(os.path.join(DATA_DIR, filename))
    except Exception:
        app.logger.exception("schedule_existing_backup_round_deletes failed")


schedule_existing_backup_round_deletes()

# ====== ACCUMULATED METRICS (backoffice) ======
METRICS = {"profit_sum": 0, "loss_sum": 0}
def net_profit(): return METRICS["profit_sum"] - METRICS["loss_sum"]

def fmt(n: int) -> str: return f"{n:,}"

msgCache = {}
CACHE_TTL_SEC = 900

# --- Rounding policy helpers ---
def _round_refund(x: float) -> int:
    # เลือกได้: floor = ปัดลง, ceil = ปัดขึ้น
    return floor(x)

def _round_profit(x: float) -> int:
    # กำไรก็ใช้ policy เดียวกันเพื่อความคงเส้นคงวา
    return floor(x)


# ====== RESULT DEFINITIONS ======
RESULT_DEFS = {
    # ปกติ: ฝั่งชนะจ่ายกำไรสุทธิ PROFIT_RATE, ฝั่งแพ้เสียเต็ม (แต่เรา “ตัดตอนวางบิลแล้ว” จึงไม่ต้องหักเพิ่มตอนสรุป)
    "ส":  {"label": "สูงชนะ (จ่าย 1 : %.2f)" % PROFIT_RATE, "winner": "HI"},
    "ต":  {"label": "ต่ำชนะ (จ่าย 1 : %.2f)" % PROFIT_RATE, "winner": "LO"},

    # กลาง/จาว/เสมอ-หาย
    "ก":  {"label": "กลาง (หัก %.0f%%)" % (MIDDLE_FEE*100), "special": "MIDDLE_FEE"},
    "จ":  {"label": "จาว (คืนเต็ม ไม่หัก)", "special": "DRAW_0"},
    "ม":  {"label": "เสมอ-หาย (คืนเต็ม ไม่หัก)", "special": "DRAW_0"},

    # เคสนโยบายพิเศษ
    "ตจ": {"label": "ต่ำเสมอ (หัก %.0f%%) / สูงเสียเต็ม" % (MIDDLE_FEE*100), "special": "LOW_DRAWFEE_HIGH_LOSE"},
    "ตส": {"label": "ต่ำเสียเต็ม / สูงเสมอ (หัก %.0f%%)" % (MIDDLE_FEE*100), "special": "LOW_LOSE_HIGH_DRAWFEE"},
}

def normalize_result_code(code: str) -> str:
    code = (code or "").strip()
    if code.startswith(("S", "s")) and len(code) >= 2:
        return code[1:].strip()
    return code

# ====== HELPERS ======
def room_key(src):
    return getattr(src, "group_id", None) or getattr(src, "room_id", None) or getattr(src, "user_id", None)

def in_group_or_room(src) -> bool:
    return bool(
        getattr(src, "group_id", None)
        or getattr(src, "room_id", None)
        or getattr(src, "user_id", None)
    )


def is_backoffice_group_id(gid): return gid in BACKOFFICE_GROUP_IDS

def start_state():
    return {
        "phase": "NONE",  # NONE | OPEN | PAUSED
        "pairNo": 0,
        "note": None,
        "pendingCode": None,
        "totals": {"HI": 0, "LO": 0},
        "bet_index": {},  # uid -> {uid,name,side,amount}
        "funds": {},      # uid -> ทุนรอบนี้
        "price": {"camp": None, "HI": (None, None), "LO": (None, None)},
        "escrow": {},     # เงินที่ถูกหักออกไปทันทีเมื่อรับบิล uid -> amount
    }

# แก้ไขในฟังก์ชัน start_state()
def start_state():
    return {
        "phase": "NONE",  # NONE | OPEN | PAUSED
        "pairNo": 0,
        "note": None,
        "pendingCode": None,
        "totals": {"HI": 0, "LO": 0},
        "bet_index": {},  
        "funds": {},      
        "price": {"camp": None, "HI": (None, None), "LO": (None, None)},
        "escrow": {},
        "score_history": [],  # เก็บประวัติผลสกอบั้งไฟวันนี้
        "settling": False,
        "last_closed_pairNo": None,
        "last_settled_pairNo": None,
    }

_profile_cache = {}           # uid -> (display_name, picture_url, ts)
_PROFILE_CACHE_TTL = int(os.getenv("PROFILE_CACHE_TTL", "300"))  # 5 นาที (ปรับใน .env ได้)
_NAME_SYNC_TTL = int(os.getenv("NAME_SYNC_TTL", "3600"))  # sync ชื่อ LINE ทุก 1 ชั่วโมง
_name_sync_ts = {}  # uid -> last sync timestamp


def get_profile_display(src, user_id):
    now = time.time()
    cached = _profile_cache.get(user_id)
    if cached and (now - cached[2]) < _PROFILE_CACHE_TTL:
        return cached[0], cached[1]
    try:
        if getattr(src, "group_id", None):
            p = line_bot_api.get_group_member_profile(src.group_id, user_id)
        elif getattr(src, "room_id", None):
            p = line_bot_api.get_room_member_profile(src.room_id, user_id)
        else:
            p = line_bot_api.get_profile(user_id)
        result = (p.display_name, p.picture_url)
    except Exception:
        result = ("ผู้เล่น", None)
    _profile_cache[user_id] = (*result, now)
    return result

def parse_bet(text):
    m = R_PARSE_BET.match(text)
    if not m: return None
    ch = m.group(1).lower()
    amount = int(m.group(2))
    side = "HI" if ch in ("ล", "ส") else "LO"
    return {"side": side, "amount": amount}


def get_user_bet(state, uid): return state["bet_index"].get(uid)
def user_stake_this_round(state, uid): return get_user_bet(state, uid)["amount"] if get_user_bet(state, uid) else 0

def user_fund_remain(state, uid):
    u = users.get(uid)
    if not u: return 0
    return max(u.get("credit", 0), 0)

# ==== 1 บิล/รอบ + กันแทงสวน ====
def can_bet(state, uid, side, amount):
    if state["phase"] != "OPEN":
        return (False, "ยังไม่เปิดรอบ")

    existing = get_user_bet(state, uid)
    if existing:
        exist_side_th = "สูง" if existing["side"] == "HI" else "ต่ำ"
        if side != existing["side"]:
            return (False, f"❌ ห้ามแทงสวน — คุณมีบิลเดิม: {exist_side_th} {fmt(existing['amount'])}  (พิมพ์ X เพื่อยกเลิกก่อน)")
        # ฝั่งเดิม = ลงเพิ่มได้ (รวมกับยอดเดิม) จนกว่าจะเต็มเพดานต่อคน

    already = existing["amount"] if existing else 0
    user_cap = min(MAX_BET, USER_SIDE_CAP[side])

    if amount < MIN_BET:
        return (False, f"ขั้นต่ำ {MIN_BET}")
    if already + amount > user_cap:
        left = max(user_cap - already, 0)
        if already:
            return (False, f"เกินสูงสุด {fmt(user_cap)} ต่อคน — มีอยู่ {fmt(already)} ลงเพิ่มได้อีก {fmt(left)}")
        return (False, f"สูงสุด {fmt(user_cap)}")

    remain = user_fund_remain(state, uid)
    if remain < amount:
        return (False, f"ทุนคงเหลือไม่พอ (มี {fmt(remain)})")

    # ✅ เช็คเพดานต่อฝั่ง (ย้ายออกมาให้อยู่นอก if ด้านบน)
    if state["totals"][side] + amount > SIDE_CAP[side]:
        side_th = "สูง" if side == "HI" else "ต่ำ"
        side_cap = SIDE_CAP[side]
        side_total = state["totals"][side]
        remain_to_cap = max(side_cap - side_total, 0)
        return (
            False,
            f"❌รับบิลไม่ได้❌: ฝั่ง{side_th} เต็ม {fmt(side_cap)} - เหลือรับได้อีก {fmt(remain_to_cap)}"
        )

    # ✅ เช็คเพดานรวมรอบ + แจ้งคงเหลือ
    round_total = state["totals"]["HI"] + state["totals"]["LO"]
    if round_total + amount > ROUND_CAP:
        remain_round = max(ROUND_CAP - round_total, 0)
        return (False, f"❌รับบิลไม่ได้❌: รอบนี้เต็ม {fmt(ROUND_CAP)} - เหลือรับได้อีก {fmt(remain_round)}")

    return (True, "")

# ==== mention helpers ====
def first_mentioned_uid(event):
    try:
        m = getattr(event.message, "mention", None)
        if not m: return None
        for me in (getattr(m, "mentionees", None) or []):
            uid = getattr(me, "user_id", None) or getattr(me, "userId", None)
            if uid and str(uid).lower() != "all":
                return uid
    except Exception:
        pass
    return None

def format_user_table(data):
    if not data:
        return "ไม่มีข้อมูล"

    import re

    def clean_name(name):
        return re.sub(r'[^\w\sก-๙]', '', name or "")

    ID_W = 4
    NAME_W = 16
    CREDIT_W = 8

    header = f"{'ID':<{ID_W}} | {'ชื่อ':<{NAME_W}} | {'เครดิต':>{CREDIT_W}}"
    sep = "-" * len(header)

    lines = []
    lines.append("📋 รายชื่อสมาชิก")
    lines.append(sep)
    lines.append(header)
    lines.append(sep)

    total_credit = 0

    for u in data:
        cid = str(u.get("cid", ""))
        name = clean_name(u.get("name", ""))[:NAME_W]
        credit = u.get("credit", 0)

        total_credit += credit

        line = f"{cid:<{ID_W}} | {name:<{NAME_W}} | {credit:>{CREDIT_W},}"
        lines.append(line)

    lines.append(sep)

    # ===== รวมเครดิต =====
    lines.append(f"💰 รวมเครดิตทั้งหมด: {total_credit:,} บาท")

    return "\n".join(lines)


# ====== FLEX ======
# ====================================================================
# ====== THEME: Light & Clean v2 — หัวการ์ดสีทึบ ตัวหนังสือเข้ม อ่านง่าย ======
# ====================================================================
# ไล่ / สูง = ฟ้า   •   ยั้ง / ต่ำ = แดง   •   เปิด = เขียว   •   พัก = ส้ม   •   ปิด = แดง
TH = {
    "bg": "#FFFFFF", "page": "#F3F4F6", "line": "#E5E7EB",
    "text": "#111827", "sub": "#374151", "muted": "#4B5563", "faint": "#6B7280",
    "green": "#15803D", "green_bg": "#E8F7EE",
    "blue": "#1D4ED8", "blue_bg": "#E8F0FE",
    "red": "#C81E1E", "red_bg": "#FDECEC",
    "amber": "#B45309", "amber_bg": "#FEF3C7",
    "purple": "#6D28D9", "purple_bg": "#F1EAFE",
    "gray": "#374151", "gray_bg": "#F3F4F6",
}
TONE = {k: (TH[k], TH[k + "_bg"]) for k in ("green", "blue", "red", "amber", "purple", "gray")}
SIDE_TONE = {"HI": "blue", "LO": "red"}
SIDE_TH = {"HI": "สูง", "LO": "ต่ำ"}


def _t(text, size="sm", color=None, weight=None, align=None, wrap=True, flex=None, margin=None, **kw):
    d = {"type": "text", "text": str(text if text not in (None, "") else " "), "size": size,
         "color": color or TH["text"], "wrap": wrap}
    if weight: d["weight"] = weight
    if align: d["align"] = align
    if flex is not None: d["flex"] = flex
    if margin: d["margin"] = margin
    d.update(kw)
    return d


def _box(contents, layout="vertical", **kw):
    d = {"type": "box", "layout": layout, "contents": contents}
    d.update(kw)
    return d


def _sep(margin="md"):
    return {"type": "separator", "margin": margin, "color": TH["line"]}


def _header(title, subtitle=None, tone="green"):
    """แถบหัวสีทึบ ตัวหนังสือขาว + ป้ายรอบด้านขวา"""
    fg, _ = TONE[tone]
    row = [_t(title, size="lg", weight="bold", color="#FFFFFF", flex=1, gravity="center")]
    if subtitle:
        row.append(_box([_t(subtitle, size="xs", weight="bold", color=fg, align="center", wrap=False)],
                        backgroundColor="#FFFFFF", cornerRadius="12px", flex=0,
                        paddingTop="3px", paddingBottom="3px", paddingStart="10px", paddingEnd="10px",
                        justifyContent="center"))
    return _box(row, layout="horizontal", backgroundColor=fg, paddingAll="14px",
                paddingStart="16px", paddingEnd="14px", alignItems="center")


def _kv(label, value, value_color=None, bold=True, size="sm", ratio=(5, 5)):
    return _box([
        _t(label, size=size, color=TH["muted"], flex=ratio[0]),
        _t(value, size=size, color=value_color or TH["text"], weight="bold" if bold else None,
           align="end", flex=ratio[1]),
    ], layout="horizontal", margin="sm")


def _pill(text, tone="gray", size="xs"):
    fg, bg = TONE[tone]
    return _box([_t(text, size=size, color=fg, weight="bold", align="center", wrap=False)],
                backgroundColor=bg, cornerRadius="12px", paddingTop="3px", paddingBottom="3px",
                paddingStart="10px", paddingEnd="10px", flex=0)


def _camp_title(camp):
    return _box([
        _t("ชื่อค่าย", size="xs", color=TH["faint"], align="center"),
        _t(f"🚀 {camp}", size="xl", weight="bold", align="center", margin="xs"),
    ])


def _side_row(label, value, tone, size="xl"):
    """แถวเต็มความกว้าง: ป้ายฝั่งซ้าย ตัวเลขใหญ่ขวา (ไม่ถูกตัด)"""
    fg, bg = TONE[tone]
    return _box([
        _t(label, size="md", weight="bold", color=fg, flex=4, gravity="center"),
        _t(value, size=size, weight="bold", color=fg, align="end", flex=6, gravity="center", wrap=False),
    ], layout="horizontal", backgroundColor=bg, cornerRadius="10px",
        paddingAll="12px", paddingStart="14px", paddingEnd="14px", alignItems="center")


def _key_chip(key, label):
    return _box([
        _box([_t(key, size="xs", weight="bold", color="#FFFFFF", align="center")],
             backgroundColor=TH["gray"], cornerRadius="6px", width="22px", height="22px",
             justifyContent="center"),
        _t(label, size="xs", color=TH["sub"], margin="sm", gravity="center", wrap=False),
    ], layout="horizontal", alignItems="center", flex=0)


def _player_footer(disclaimer=True):
    rows = [_box([_key_chip("X", "ยกเลิกบิล"), _box([], flex=1), _key_chip("C", "ดูยอดคงเหลือ")],
                 layout="horizontal", alignItems="center")]
    if disclaimer:
        rows.append(_t("บอทไม่จับ ไม่ได้เสีย ทุกกรณี", size="xs", color=TH["faint"], align="center", margin="md"))
    return _box(rows, backgroundColor=TH["page"], paddingAll="12px", paddingStart="16px", paddingEnd="16px")


def _note_footer(text):
    return _box([_t(text, size="xs", color=TH["faint"], align="center")],
                backgroundColor=TH["page"], paddingAll="12px")


def _bubble(header, body, footer=None, size="mega"):
    b = {
        "type": "bubble", "size": size,
        "header": header,
        "body": _box(body, backgroundColor=TH["bg"], paddingAll="16px", spacing="md"),
        "styles": {"body": {"backgroundColor": TH["bg"]}},
    }
    if footer:
        b["footer"] = footer
        b["styles"]["footer"] = {"backgroundColor": TH["page"]}
    return b


# ---------- เปิดรอบ (ยังไม่มีราคา) ----------
def flex_open(pair_no, note=None):
    body = []
    if note:
        body += [_camp_title(note), _sep()]
    body += [
        _t("เปิดรับแทงแล้ว", size="xxl", weight="bold", color=TH["green"], align="center"),
        _t("รอแอดมินออกราคาสักครู่", size="md", color=TH["sub"], align="center"),
    ]
    return FlexSendMessage(
        alt_text=f"เริ่มแทงได้ รอบที่ {pair_no}",
        contents=_bubble(_header("🟢 เปิดรอบ", f"รอบ {pair_no}", "green"), body, _player_footer()),
    )


# ---------- กลับมาเปิดรอบ ----------
def flex_resume(pair_no: int, camp: str):
    body = [
        _camp_title(camp), _sep(),
        _t("เปิดให้แทงต่อแล้ว", size="xxl", weight="bold", color=TH["green"], align="center"),
        _t("ฮ่ำมันเข้าไปคักๆ หมานๆนะสมาชิก", size="md", color=TH["sub"], align="center"),
    ]
    return FlexSendMessage(
        alt_text=f"กลับมาเปิดรอบ {pair_no}",
        contents=_bubble(_header("🟢 เปิดรับแทงอีกครั้ง", f"รอบ {pair_no}", "green"), body, _player_footer()),
    )


# ---------- ออกราคา ----------
def flex_open_with_prices(pair_no, camp, hi_min, hi_max, lo_min, lo_max):
    hi_txt = f"{hi_min}-{hi_max}" if hi_min is not None and hi_max is not None else "-"
    lo_txt = f"{lo_min}-{lo_max}" if lo_min is not None and lo_max is not None else "-"

    rules = _box([
        _kv("แทงต่อคน", f"{MIN_BET} - {fmt(MAX_BET)} บาท"),
        _kv("รับรวมฝั่งสูง", f"{fmt(SIDE_CAP['HI'])} บาท"),
        _kv("รับรวมฝั่งต่ำ", f"{fmt(SIDE_CAP['LO'])} บาท"),
        _kv("ชนะจ่าย", f"1 : {PROFIT_RATE:.2f}"),
        _kv("ออกกลาง", f"หัก {int(MIDDLE_FEE*100)}%"),
        _kv("ซุ แตก คาฐาน หาย", "จาว", ratio=(8, 2)),
    ], backgroundColor=TH["page"], cornerRadius="10px", paddingAll="12px", spacing="xs")

    notes = _box([
        _t("• ราคาแอดมินกำหนดตามความเหมาะสม", size="xs", color=TH["muted"]),
        _t("• ออกราคาหลังปิด ถือว่าจาวทุกกรณี", size="xs", color=TH["muted"]),
        _t("• หน้าฐานราคารูดผิดปกติ แอดมินแจ้งยกเลิกได้", size="xs", color=TH["amber"], weight="bold"),
    ], spacing="xs")

    body = [
        _camp_title(camp),
        _side_row("ไล่ (สูง)", hi_txt, "blue", size="xxl"),
        _side_row("ยั้ง (ต่ำ)", lo_txt, "red", size="xxl"),
        rules,
        notes,
    ]
    return FlexSendMessage(
        alt_text=f"ราคามาแล้ว รอบ {pair_no} • {camp} ไล่ {hi_txt} ยั้ง {lo_txt}",
        contents=_bubble(_header("🎯 ราคามาแล้ว", f"รอบ {pair_no}", "green"), body, _player_footer()),
    )


# ---------- ปิดรอบ ----------
def flex_close_notice(pair_no):
    body = [
        _t("⛔ หยุดแทง", size="xxl", weight="bold", color=TH["red"], align="center"),
        _t("ระบบปิดรับบิลแล้ว กรุณารอสรุปผล", size="md", color=TH["sub"], align="center"),
    ]
    return FlexSendMessage(
        alt_text=f"ปิดรอบ #{pair_no}",
        contents=_bubble(_header("ปิดรับแทง", f"รอบ {pair_no}", "red"), body,
                         _note_footer("บอทไม่จับ ไม่ได้เสีย ทุกกรณี")),
    )


# ---------- พักรอบ ----------
def flex_pause_notice(pair_no: int, camp: str):
    body = [
        _camp_title(camp or "ไม่ระบุค่าย"), _sep(),
        _t("⏸ หยุดแทงชั่วคราว", size="xl", weight="bold", color=TH["amber"], align="center"),
        _t("ระหว่างนี้แทงหรือยกเลิกบิลไม่ได้\nรอแอดมินเปิดอีกครั้ง", size="sm", color=TH["sub"], align="center"),
    ]
    return FlexSendMessage(
        alt_text=f"พักรอบชั่วคราว #{pair_no}",
        contents=_bubble(_header("พักรอบ", f"รอบ {pair_no}", "amber"), body),
    )


# ---------- บัตรสมาชิก (C) ----------
def _avatar(user, size=40):
    r = f"{size // 2}px"
    pic = user.get("pictureUrl")
    if pic:
        return _box([{"type": "image", "url": pic, "size": "full", "aspectMode": "cover", "aspectRatio": "1:1"}],
                    width=f"{size}px", height=f"{size}px", cornerRadius=r, flex=0)
    initial = (user.get("name") or "?").strip()[:1] or "?"
    return _box([_t(initial, size="md", weight="bold", color=TH["green"], align="center", gravity="center")],
                width=f"{size}px", height=f"{size}px", cornerRadius=r, backgroundColor=TH["green_bg"],
                justifyContent="center", flex=0)


def flex_customer_card(st, user):
    """บัตรสมาชิกแบบกะทัดรัด: รูป • ชื่อ/ID • เครดิต อยู่แถวเดียว"""
    if not user:
        return TextSendMessage(text="กรุณาพิมพ์ add เพื่อรับไอดีก่อน")

    credit = int(user.get("credit", 0) or 0)
    bet = get_user_bet(st, user["uid"])

    top = _box([
        _avatar(user),
        _box([
            _t(user.get("name", "ผู้เล่น"), size="sm", weight="bold", wrap=False),
            _t(f"ID {user['cid']}", size="xs", weight="bold", color=TH["green"]),
        ], margin="md", flex=1, justifyContent="center"),
        _box([
            _t("คงเหลือ", size="xxs", color=TH["faint"], align="end"),
            _t(f"{fmt(credit)} ฿", size="lg", weight="bold", align="end", wrap=False),
        ], flex=0, justifyContent="center"),
    ], layout="horizontal", alignItems="center")

    contents = [top]
    if bet:
        fg, bg = TONE[SIDE_TONE[bet["side"]]]
        contents.append(_box([
            _t(f"บิลรอบนี้ • {SIDE_TH[bet['side']]}", size="xs", weight="bold", color=fg, flex=1, gravity="center"),
            _t(f"{fmt(bet['amount'])} ฿", size="sm", weight="bold", color=fg, align="end", flex=0),
        ], layout="horizontal", backgroundColor=bg, cornerRadius="8px",
            paddingAll="8px", paddingStart="10px", paddingEnd="10px", margin="md"))

    return FlexSendMessage(
        alt_text=f"ID {user['cid']} • เครดิต {fmt(credit)} บาท",
        contents={"type": "bubble", "size": "kilo",
                  "body": _box(contents, backgroundColor=TH["bg"], paddingAll="12px")},
    )



def flex_register_success(cid: int):
    body = [
        _t("ID ของคุณ", size="sm", color=TH["muted"], align="center"),
        _t(str(cid), size="3xl", weight="bold", align="center"),
        _t("พิมพ์ C เพื่อดูบัตรสมาชิก", size="sm", color=TH["sub"], align="center"),
    ]
    return FlexSendMessage(
        alt_text=f"ลงทะเบียนสำเร็จ ID {cid}",
        contents={"type": "bubble", "size": "kilo",
                  "header": _header("✅ ลงทะเบียนสำเร็จ", None, "green"),
                  "body": _box(body, backgroundColor=TH["bg"], paddingAll="16px", spacing="sm")},
    )


# ---------- ตัวอย่างผล (ก่อน /y) ----------
_RESULT_META = {
    "ส": ("สูงชนะ", "blue", f"ฝั่งสูงได้ 1 : {PROFIT_RATE:.2f}"),
    "ต": ("ต่ำชนะ", "red", f"ฝั่งต่ำได้ 1 : {PROFIT_RATE:.2f}"),
    "ก": ("กลาง", "amber", f"คืนเงินทั้งสองฝั่ง หัก {int(MIDDLE_FEE*100)}%"),
    "จ": ("จาว", "green", "คืนเงินเต็มจำนวน"),
    "ม": ("เสมอ-หาย", "green", "คืนเงินเต็มจำนวน"),
    "ตจ": ("ต่ำเสมอ / สูงเสียเต็ม", "purple", f"ฝั่งต่ำคืน หัก {int(MIDDLE_FEE*100)}%"),
    "ตส": ("ต่ำเสียเต็ม / สูงเสมอ", "purple", f"ฝั่งสูงคืน หัก {int(MIDDLE_FEE*100)}%"),
}


def flex_result_preview(code: str, pair_no: int):
    title, tone, desc = _RESULT_META.get(code, ("รหัสผลไม่ถูกต้อง", "gray", "พิมพ์ s ตามด้วยรหัสผลใหม่"))
    fg, bg = TONE[tone]
    body = [
        _box([_t(title, size="xl", weight="bold", color=fg, align="center"),
              _t(desc, size="sm", color=TH["sub"], align="center", margin="xs")],
             backgroundColor=bg, cornerRadius="12px", paddingAll="14px"),
    ]
    if code in _RESULT_META:
        body.append(_t("พิมพ์ /y เพื่อยืนยันผล", size="md", weight="bold", align="center"))
    body.append(_t("ต้องการเปลี่ยนผล พิมพ์ s<รหัสผล> ใหม่", size="sm", color=TH["muted"], align="center"))
    return FlexSendMessage(
        alt_text=f"ตรวจผลรอบ {pair_no}: {title}",
        contents=_bubble(_header("ตรวจผลก่อนยืนยัน", f"รอบ {pair_no}", tone), body),
    )


# ---------- สรุปผลรอบ ----------
def flex_settle(pair_no, rows, footer_text,
                show_profit=False, profit_value=0,
                balance_map=None, accum=None, camp_name=None):
    def _signed(n):
        return f"+{fmt(n)}" if n > 0 else (f"-{fmt(abs(n))}" if n < 0 else "0")

    has_balance = bool(balance_map)
    result_text = (footer_text or "").replace("ผล:", "").strip() or "-"

    body = []
    if camp_name:
        body.append(_camp_title(camp_name))
    body.append(_box([_t("ผลออก", size="sm", color=TH["muted"], flex=0, gravity="center"),
                      _t(result_text, size="md", weight="bold", color=TH["green"], align="end", flex=1)],
                     layout="horizontal", backgroundColor=TH["green_bg"], cornerRadius="10px", paddingAll="12px"))

    if rows:
        cols = [_t("ผู้เล่น", size="xs", weight="bold", color=TH["muted"], flex=5),
                _t("เล่น", size="xs", weight="bold", color=TH["muted"], align="end", flex=3),
                _t("ได้เสีย", size="xs", weight="bold", color=TH["muted"], align="end", flex=3)]
        if has_balance:
            cols.append(_t("คงเหลือ", size="xs", weight="bold", color=TH["muted"], align="end", flex=4))
        table = [_box(cols, layout="horizontal", backgroundColor=TH["page"], cornerRadius="6px", paddingAll="8px")]
        for r in rows:
            pl = (r.get("payout", 0) or 0) - (r.get("stake", 0) or 0)
            pl_color = TH["green"] if pl > 0 else (TH["red"] if pl < 0 else TH["muted"])
            line = [_t(r.get("name") or "-", size="sm", flex=5, wrap=False),
                    _t(fmt(r.get("stake", 0)), size="sm", color=TH["sub"], align="end", flex=3),
                    _t(_signed(pl), size="sm", weight="bold", color=pl_color, align="end", flex=3)]
            if has_balance:
                line.append(_t(fmt(balance_map.get(r["uid"], 0)), size="sm", align="end", flex=4))
            table.append(_box(line, layout="horizontal", paddingStart="8px", paddingEnd="8px",
                              paddingTop="6px", paddingBottom="6px"))
            table.append(_sep("none"))
        table.pop()
        body.append(_box(table))
    else:
        body.append(_t("ไม่มีผู้เล่นในรอบนี้", size="sm", color=TH["faint"], align="center"))

    if show_profit:
        prof = [_kv("กำไรรอบนี้", _signed(profit_value), TH["green"] if profit_value >= 0 else TH["red"])]
        if accum:
            prof += [_kv("สะสมกำไร / ขาดทุน", f"{fmt(accum['profit_sum'])} / {fmt(accum['loss_sum'])}"),
                     _kv("สุทธิสะสม", _signed(accum["net"]), TH["green"] if accum["net"] >= 0 else TH["red"])]
        body.append(_box(prof, backgroundColor=TH["page"], cornerRadius="10px", paddingAll="12px"))

    return FlexSendMessage(
        alt_text=f"สรุปผล รอบ {pair_no}",
        contents=_bubble(_header("📊 สรุปผล", f"รอบ {pair_no}", "green"), body,
                         _note_footer(f"{len(rows or [])} ผู้เล่น  •  พิมพ์ C เพื่อดูยอดคงเหลือ")),
    )


# ---------- สกอบั้งไฟ (10 รอบล่าสุด) ----------
_SCORE_MAP = {
    "ส": ("สูง ✅", "blue"), "ต": ("ต่ำ ✅", "red"), "ก": ("กลาง", "amber"),
    "จ": ("จาว", "green"), "ม": ("เสมอ", "green"),
    "ตจ": ("ต่ำเสมอ", "purple"), "ตส": ("สูงเสมอ", "purple"),
}


def flex_scoreboard(history_list):
    latest = {}
    for h in history_list or []:
        if h.get("round") is not None:
            latest[h["round"]] = h
    recent = [latest[r] for r in sorted(latest)][-10:]

    if recent:
        table = [_box([_t("รอบ", size="xs", weight="bold", color=TH["muted"], flex=2),
                       _t("ค่าย", size="xs", weight="bold", color=TH["muted"], flex=6),
                       _t("ผล", size="xs", weight="bold", color=TH["muted"], align="end", flex=4)],
                      layout="horizontal", backgroundColor=TH["page"], cornerRadius="6px", paddingAll="8px")]
        for h in recent:
            label, tone = _SCORE_MAP.get(h.get("code") or "?", (h.get("code") or "?", "gray"))
            table.append(_box([
                _t(str(h["round"]), size="sm", color=TH["muted"], flex=2, gravity="center"),
                _t(h.get("camp") or "-", size="sm", flex=6, wrap=False, gravity="center"),
                _box([_pill(label, tone)], layout="horizontal", justifyContent="flex-end", flex=4),
            ], layout="horizontal", alignItems="center", paddingAll="8px"))
            table.append(_sep("none"))
        table.pop()
        body = [_box(table)]
    else:
        body = [_t("ยังไม่มีประวัติ", size="sm", color=TH["faint"], align="center")]

    return FlexSendMessage(
        alt_text="สกอบั้งไฟล่าสุด",
        contents=_bubble(_header("📜 สกอบั้งไฟ", "10 รอบล่าสุด", "blue"), body),
    )


# ---------- สรุปบิล (ตอนปิด/พักรอบ) ----------
def flex_summary(st, event=None):
    """สรุปบิล (ตอนปิด/พักรอบ) — ธีมสว่าง แสดงแค่ ชื่อ / ฝั่ง / ยอดเงิน"""
    bets = list(st["bet_index"].values())

    body = [_box([
        _t("ผู้เล่น", size="xs", weight="bold", color=TH["muted"], flex=6),
        _t("ฝั่ง", size="xs", weight="bold", color=TH["muted"], align="center", flex=2),
        _t("ยอดเงิน", size="xs", weight="bold", color=TH["muted"], align="end", flex=3),
    ], layout="horizontal", backgroundColor=TH["page"], cornerRadius="6px", paddingAll="8px")]

    if bets:
        table = []
        for b in sorted(bets, key=lambda x: (x["side"], -x["amount"])):
            fg = TONE[SIDE_TONE[b["side"]]][0]
            table.append(_box([
                _t(b["name"], size="sm", flex=6, wrap=False),
                _t(SIDE_TH[b["side"]], size="sm", color=fg, weight="bold", align="center", flex=2),
                _t(fmt(b["amount"]), size="sm", weight="bold", align="end", flex=3),
            ], layout="horizontal", paddingAll="8px"))
            table.append(_sep("none"))
        table.pop()
        body.append(_box(table))
    else:
        body.append(_t("ยังไม่มีบิล", size="sm", color=TH["faint"], align="center"))

    return FlexSendMessage(
        alt_text=f"สรุปการแทง รอบ {st['pairNo']} ({len(bets)} บิล)",
        contents=_bubble(_header("📋 สรุปบิล", f"รอบ {st['pairNo']}", "gray"), body),
    )


# ---------- รายชื่อสมาชิก + เครดิต (คำสั่ง call ในกลุ่มหลังบ้าน) ----------
MEMBER_ROWS_PER_PAGE = 25


def flex_member_list(rows, total_credit, total_count):
    """ตารางสมาชิก: ID / ชื่อ / เครดิต — แบ่งหน้าละ 25 คน (carousel)"""
    pages = [rows[i:i + MEMBER_ROWS_PER_PAGE] for i in range(0, len(rows), MEMBER_ROWS_PER_PAGE)] or [[]]
    now_txt = datetime.now().strftime("%d/%m %H:%M")
    bubbles = []
    for pi, chunk in enumerate(pages, start=1):
        body = []
        if pi == 1:
            body.append(_box([
                _box([_t("ลูกค้ามีเครดิต", size="xs", color=TH["muted"], align="center"),
                      _t(f"{fmt(total_count)} คน", size="lg", weight="bold", align="center")],
                     backgroundColor=TH["page"], cornerRadius="10px", paddingAll="10px", flex=1),
                _box([_t("เครดิตรวม", size="xs", color=TH["green"], align="center"),
                      _t(f"{fmt(total_credit)} ฿", size="lg", weight="bold", color=TH["green"], align="center",
                         wrap=False)],
                     backgroundColor=TH["green_bg"], cornerRadius="10px", paddingAll="10px", flex=1),
            ], layout="horizontal", spacing="sm"))
        body.append(_box([
            _t("ID", size="xs", weight="bold", color=TH["muted"], flex=2),
            _t("ชื่อ", size="xs", weight="bold", color=TH["muted"], flex=6),
            _t("เครดิต", size="xs", weight="bold", color=TH["muted"], align="end", flex=4),
        ], layout="horizontal", backgroundColor=TH["page"], cornerRadius="6px", paddingAll="8px"))
        table = []
        for u in chunk:
            table.append(_box([
                _t(str(u.get("cid", "-")), size="sm", weight="bold", color=TH["green"], flex=2),
                _t(u.get("name") or "-", size="sm", flex=6, wrap=False),
                _t(fmt(int(u.get("credit", 0) or 0)), size="sm", weight="bold", align="end", flex=4),
            ], layout="horizontal", paddingAll="7px"))
            table.append(_sep("none"))
        if table:
            table.pop()
            body.append(_box(table))
        sub = f"หน้า {pi}/{len(pages)}" if len(pages) > 1 else now_txt
        bubbles.append(_bubble(_header("💰 รายชื่อสมาชิก", sub, "gray"), body,
                               _note_footer(f"อัปเดต {now_txt}" + (f"  •  แสดง {len(rows)} จาก {total_count} คน"
                                                                    if len(rows) < total_count else ""))))
    # LINE จำกัดขนาด 50KB/ข้อความ → ส่งเป็นหลายข้อความ ข้อความละ 2 หน้า (ตอบได้สูงสุด 5 ข้อความ)
    msgs = []
    for i in range(0, min(len(bubbles), 10), 2):
        grp = bubbles[i:i + 2]
        contents = grp[0] if len(grp) == 1 else {"type": "carousel", "contents": grp}
        msgs.append(FlexSendMessage(alt_text=f"รายชื่อสมาชิก {total_count} คน • เครดิตรวม {fmt(total_credit)} บาท",
                                    contents=contents))
    return msgs[0] if len(msgs) == 1 else msgs















def text_bank():
    return TextSendMessage(
        text=(
            "📌 CEO บั้งไฟน้อย\n\n"
            "⚠️แจ้งเลขบัญชีฝาก⚠️\n\n"
            "🏳️ XXXXXXX   \n"
            "💰 XXXX\n"
            "💳 XXXX XXX\n\n"
            "📌 เพื่อป้องกันมิจฉาชีพ ชื่อผู้ฝาก-ถอน ต้องเป็นชื่อเดียวกันเท่านั้น⚠️\n"
            "📌 กด C ดูไอดีตัวเองส่งให้แอดมินได้เลย\n"
        )
    )


def flex_backoffice_button(url: str, label: str = "เปิดหน้าฝากเงิน"):
    """ปุ่ม Flex สำหรับเปิดหน้าแจ้งฝาก/ฝากเงิน (ลิงก์ DEPOSIT_URL)

    แก้ปัญหา NameError: flex_backoffice_button ไม่ถูกประกาศ
    """
    u = (url or '').strip() or DEPOSIT_URL
    # กันพิมพ์ลิงก์แบบไม่มี scheme
    if not re.match(r'^https?://', u, re.IGNORECASE):
        u = 'https://' + u.lstrip('/')

    return FlexSendMessage(
        alt_text='ฝากเงิน/แจ้งโอน',
        contents={
            'type': 'bubble',
            'size': 'mega',
            'styles': {'body': {'backgroundColor': '#F3F4F6'}},
            'body': {
                'type': 'box',
                'layout': 'vertical',
                'paddingAll': '12px',
                'contents': [
                    {
                        'type': 'box',
                        'layout': 'vertical',
                        'backgroundColor': '#FFFFFF',
                        'cornerRadius': '16px',
                        'paddingAll': '16px',
                        'spacing': '10px',
                        'contents': [
                            {
                                'type': 'text',
                                'text': '💳 ฝากเงิน / แจ้งโอน',
                                'weight': 'bold',
                                'size': 'lg',
                                'align': 'center',
                                'color': '#111827'
                            },
                            {
                                'type': 'text',
                                'text': 'กดปุ่มด้านล่างเพื่อไปหน้าแจ้งฝาก/แนบสลิป',
                                'size': 'sm',
                                'align': 'center',
                                'wrap': True,
                                'color': '#6B7280'
                            },
                            {'type': 'separator', 'margin': 'md', 'color': '#E5E7EB'},
                            {
                                'type': 'button',
                                'style': 'primary',
                                'color': '#16A34A',
                                'height': 'sm',
                                'action': {'type': 'uri', 'label': label, 'uri': u}
                            }
                        ]
                    }
                ]
            }
        }
    )








def flex_call_pages(user_rows, title="ตารางเครดิตลูกค้า", per_page=30):
    pages = []
    total = len(user_rows)
    num_pages = max(1, ceil(total / per_page))
    sum_credit_all = sum(int(r.get("credit", 0) or 0) for r in user_rows)

    def fmt2(n):
        try:
            return f"{int(float(n or 0)):,}"
        except:
            return "0"

    updated_at = datetime.now().strftime("%d/%m/%Y %H:%M")

    # ========== HEAD TABLE: ขนาดเล็กลง 100% ทำงานได้ ==========
    def table_head():
        return {
            "type": "box",
            "layout": "horizontal",
            "paddingAll": "6px",
            "backgroundColor": "#E6F0FF",
            "contents": [
                {"type": "text", "text": "ID", "flex": 3, "size": "xs", "weight": "bold", "color": "#1E3A8A"},
                {"type": "text", "text": "ชื่อ", "flex": 6, "size": "xs", "weight": "bold", "color": "#1E3A8A"},
                {"type": "text", "text": "เครดิต", "flex": 3, "size": "xs", "weight": "bold", "align": "end", "color": "#1E3A8A"},
            ]
        }

    for i in range(num_pages):
        chunk = user_rows[i * per_page:(i + 1) * per_page]
        page_credit = sum(int(r.get("credit", 0) or 0) for r in chunk)

        header = {
            "type": "box",
            "layout": "vertical",
            "paddingAll": "6px",
            "contents": [
                {"type": "text", "text": title, "weight": "bold", "size": "sm", "align": "center"},
                {"type": "text", "text": f"หน้า {i+1}/{num_pages} • อัปเดต {updated_at}", "size": "xs", "align": "center", "color": "#6B7280"}
            ]
        }

        rows = []
        rows.append(table_head())
        rows.append({"type": "separator", "margin": "md", "color": "#D1D5DB"})

        # ========== ROWS ==========
        if chunk:
            for idx, r in enumerate(chunk):
                cid = str(r.get("cid", "-"))
                name = str(r.get("name", "-"))
                cred = int(r.get("credit", 0) or 0)

                row_bg = "#FFFFFF"

                rows.append({
                    "type": "box",
                    "layout": "horizontal",
                    "paddingAll": "4px",   # ลด padding แต่ไม่ถึงขั้นพัง
                    "backgroundColor": row_bg,
                    "contents": [
                        {"type": "text", "text": cid, "flex": 3, "size": "xs", "color": "#111827"},
                        {"type": "text", "text": name, "flex": 6, "size": "xs", "wrap": True, "color": "#111827"},
                        {"type": "text", "text": fmt2(cred), "flex": 3, "size": "xs", "align": "end", "color": "#111827"},
                    ]
                })

                if idx != len(chunk) - 1:
                    rows.append({"type": "separator", "margin": "md", "color": "#E5E7EB"})
        else:
            rows.append({
                "type": "box",
                "layout": "vertical",
                "paddingAll": "8px",
                "contents": [{"type": "text", "text": "(ยังไม่มีข้อมูล)", "align": "center", "size": "xs", "color": "#9CA3AF"}]
            })

        # ========== SUMMARY ==========
        summary = {
            "type": "box",
            "layout": "vertical",
            "spacing": "4px",
            "paddingAll": "6px",
            "contents": [
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "ลูกค้าในหน้านี้", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": str(len(chunk)), "flex": 6, "size": "xs", "align": "end"},
                ]},
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "รวมเครดิต (หน้านี้)", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": fmt2(page_credit), "flex": 6, "size": "xs", "align": "end", "color": "#16A34A"},
                ]},
                {"type": "separator", "margin": "md"},
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "รวมเครดิต (ทั้งหมด)", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": fmt2(sum_credit_all), "flex": 6, "size": "xs", "align": "end", "color": "#16A34A"},
                ]}
            ]
        }

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "4px",
                "paddingAll": "8px",
                "contents": [
                    header,
                    {"type": "box", "layout": "vertical", "contents": rows},
                    summary
                ]
            }
        }

        pages.append(FlexSendMessage(
            alt_text=f"{title} {i+1}/{num_pages}",
            contents=bubble
        ))

    return pages




@lru_cache(maxsize=None)
def rules_text() -> str:
    return (
        "🎉🎊กติกา🎊🎉\n"
        f"✨แทงขั้นต่ำ{MIN_BET}-{fmt(MAX_BET)}บาท/คน/รอบ\n"
        "\n"
        "🏆การจ่าย🎖️\n"
        f"ชนะ จ่าย 1 : {PROFIT_RATE:.2f}\n"
        "\n"
        f"🔴อั้นต่ำ = {fmt(SIDE_CAP['LO'])}\n"
        f"🔵อั้นสูง = {fmt(SIDE_CAP['HI'])}\n"
        f"🟢ออกกลางเจ๊า หัก {int(MIDDLE_FEE*100)}%\n"
        "\n"
        "- ลงเพิ่มฝั่งเดิมได้ (รวมไม่เกินสูงสุดต่อคน) แต่ห้ามแทงสวน\n"
        "- พิมพ์ x เพื่อยกเลิกบิล / พิมพ์ C เพื่อดูบัตรสมาชิก\n"
    )


# ====== RESULT CALC (ตามโมเดล escrow) ======
def settle_by_code(st, code):
    """
    โมเดลเครดิต:
    - ตอนรับบิล: หักเครดิต = amount และเก็บ st['escrow'][uid] += amount
    - ตอนสรุป:
        * ชนะ: คืนต้นทุน + กำไรสุทธิ (amount + amount*PROFIT_RATE)
        * แพ้: ไม่คืนอะไร (ต้นทุนถูกหักไปแล้ว)
        * คืนเงินหัก fee: คืน amount*(1 - fee)
        * คืนเต็ม: คืน amount
    ฟังก์ชันนี้คืน rows: [{'uid','name','stake','payout'}...], footer_text
    """
    acc = {}
    def add(uid, name, stake, payout):
        row = acc.get(uid, {"uid": uid, "name": name, "stake": 0, "payout": 0})
        row["stake"] += stake
        row["payout"] += payout
        acc[uid] = row

    d = RESULT_DEFS.get(code)

    # DRAW (คืนเต็ม)
    if (not d) or d.get("special") == "DRAW_0":
        for b in st["bet_index"].values():
            add(b["uid"], b["name"], b["amount"], b["amount"])
        label = RESULT_DEFS.get(code, {"label": "จาว (คืนเต็ม)"} )["label"]
        return list(acc.values()), f"ผล: {label}"

    # กลางคืนเงิน หัก MIDDLE_FEE
    if d.get("special") == "MIDDLE_FEE":
        for b in st["bet_index"].values():
            refund = _round_refund(b["amount"] * (1 - MIDDLE_FEE))
            add(b["uid"], b["name"], b["amount"], refund)
        return list(acc.values()), f"ผล: กลาง (คืนเงิน หัก {int(MIDDLE_FEE*100)}%)"

    # ต่ำเสมอ (หัก fee) / สูงเสียเต็ม
    if d.get("special") == "LOW_DRAWFEE_HIGH_LOSE":
        for b in st["bet_index"].values():
            if b["side"] == "LO":
                refund = _round_refund(b["amount"] * (1 - MIDDLE_FEE))
                add(b["uid"], b["name"], b["amount"], refund)
            else:
                add(b["uid"], b["name"], b["amount"], 0)
        return list(acc.values()), f"ผล: ต่ำเสมอ (หัก {int(MIDDLE_FEE*100)}%) / สูงเสียเต็ม"

    # ต่ำเสียเต็ม / สูงเสมอ (หัก fee)
    if d.get("special") == "LOW_LOSE_HIGH_DRAWFEE":
        for b in st["bet_index"].values():
            if b["side"] == "HI":
                refund = round(b["amount"] * (1 - MIDDLE_FEE))
                add(b["uid"], b["name"], b["amount"], refund)
            else:
                add(b["uid"], b["name"], b["amount"], 0)
        return list(acc.values()), f"ผล: ต่ำเสียเต็ม / สูงเสมอ (หัก {int(MIDDLE_FEE*100)}%)"

    # ปกติ: มีฝั่งชนะ/แพ้
    win = d["winner"]
    for b in st["bet_index"].values():
        if b["side"] == win:
            payout = b["amount"] + _round_profit(b["amount"] * PROFIT_RATE)
            add(b["uid"], b["name"], b["amount"], payout)
        else:
            add(b["uid"], b["name"], b["amount"], 0)
    return list(acc.values()), f"ผล: {d['label']}"

# ========= HARDENING / SECURITY =========
MAX_BODY_BYTES = int(os.getenv("MAX_BODY_BYTES", "200000"))
WEBHOOK_DRIFT_SEC = int(os.getenv("WEBHOOK_DRIFT_SEC", "600"))  # DEV-friendly
REQUIRE_LINE_UA = os.getenv("REQUIRE_LINE_UA", "0") == "1"




RL_IP_LIMIT, RL_IP_PERIOD = int(os.getenv("RL_IP_LIMIT", "150")), int(os.getenv("RL_IP_PERIOD", "60"))
RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD = int(os.getenv("RL_UID_BURST_LIMIT", "20")), int(os.getenv("RL_UID_BURST_PERIOD", "10"))
RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD = int(os.getenv("RL_ROOM_BURST_LIMIT", "220")), int(os.getenv("RL_ROOM_BURST_PERIOD", "10"))
RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD = int(os.getenv("RL_UID_DAILY_LIMIT", "3000")), 86400

MUTE_SECONDS_DEFAULT = int(os.getenv("MUTE_SECONDS_DEFAULT", "300"))
ABUSE_STRIKE_TO_MUTE  = int(os.getenv("ABUSE_STRIKE_TO_MUTE", "3"))

ALLOW_GROUP_IDS = {s.strip() for s in os.getenv("ALLOW_GROUP_IDS", "").split(",") if s.strip()}
DENY_GROUP_IDS  = {s.strip() for s in os.getenv("DENY_GROUP_IDS", "").split(",") if s.strip()}

ADMIN_PIN = os.getenv("ADMIN_PIN", "1234")

PROTECTED_UIDS = {s.strip() for s in os.getenv("PROTECTED_UIDS", "").split(",") if s.strip()}
LOCKDOWN_SECONDS_DEFAULT = int(os.getenv("LOCKDOWN_SECONDS_DEFAULT", "900"))  # 15m

class RateLimiter:
    def __init__(self): self._buckets = {}
    def allow(self, key: str, limit: int, period: int) -> bool:
        now = time.time()
        dq = self._buckets.get(key)
        if dq is None:
            dq = deque(); self._buckets[key] = dq
        while dq and (now - dq[0]) > period:
            dq.popleft()
        if len(dq) >= limit:
            return False
        dq.append(now)
        return True

rl = RateLimiter()
MUTED_UNTIL = {}       # uid -> ts
BANNED_UIDS = set()    # uid
BANNED_GROUPS = set()  # gid
STRIKES = {}           # uid -> count
_last_notice_at = {}   # uid -> ts
LOCKDOWN_UNTIL = {}    # gid -> ts

@lru_cache(maxsize=1024)
def _safe_is_line_ua(ua: str) -> bool:
    if not ua: return False
    ua = ua.lower()
    return ("linebotwebhook" in ua) or ("line-bot-sdk" in ua) or ("line" in ua and "webhook" in ua)

def _client_ip():
    xff = request.headers.get("X-Forwarded-For", "")
    if xff:
        return xff.split(",")[0].strip()
    return request.remote_addr or "0.0.0.0"

def _now(): return int(time.time())
def _muted(uid: str) -> bool: return MUTED_UNTIL.get(uid, 0) > _now()
def _locked_group(gid: str) -> bool: return LOCKDOWN_UNTIL.get(gid, 0) > _now()

def _notice_throttled(uid: str) -> bool:
    last = _last_notice_at.get(uid, 0)
    if _now() - last >= 30:
        _last_notice_at[uid] = _now()
        return False
    return True

def _admin_auth_pin(text: str) -> str:
    m = re.search(r"(?:\s|!!)(\d{4,8})\s*$", text)
    return m.group(1) if m else ""

def is_allowed_group(gid: str) -> bool:
    if gid in DENY_GROUP_IDS or gid in BANNED_GROUPS: return False
    if ALLOW_GROUP_IDS: return gid in ALLOW_GROUP_IDS or gid in BACKOFFICE_GROUP_IDS
    return True

def safe_reply(event, messages):
    """Reply message แบบไม่ทำให้บอทล่ม + retry เมื่อ timeout"""
    import requests as _requests
    for attempt in range(1, LINE_API_RETRY + 2):
        try:
            line_bot_api.reply_message(
                event.reply_token,
                messages,
                timeout=LINE_API_TIMEOUT
            )
            return True
        except (_requests.exceptions.Timeout, _requests.exceptions.ConnectionError) as e:
            if attempt <= LINE_API_RETRY:
                app.logger.warning("safe_reply timeout attempt=%d, retrying... (%s)", attempt, e)
                time.sleep(0.5 * attempt)
            else:
                app.logger.error("safe_reply timeout หมด retry (%d ครั้ง): %s", LINE_API_RETRY, e)
                return False
        except Exception:
            app.logger.exception("safe_reply failed")
            return False

def safe_push(to_id, messages, label: str = "", return_reason: bool = False):
    """Push message แบบไม่ทำให้บอทล่ม + retry เมื่อ timeout
    - คืนค่า True/False (หรือ (True/False, reason) ถ้า return_reason=True)
    - reason: 'quota_exceeded' เมื่อเจอ 429 monthly limit
    """
    import requests as _requests
    for attempt in range(1, LINE_API_RETRY + 2):
        try:
            line_bot_api.push_message(
                to_id,
                messages,
                timeout=LINE_API_TIMEOUT
            )
            return (True, None) if return_reason else True
        except (_requests.exceptions.Timeout, _requests.exceptions.ConnectionError) as e:
            if attempt <= LINE_API_RETRY:
                app.logger.warning("safe_push timeout attempt=%d, retrying to=%s (%s)", attempt, to_id, e)
                time.sleep(0.5 * attempt)
            else:
                app.logger.error("safe_push timeout หมด retry (%d ครั้ง) to=%s", LINE_API_RETRY, to_id)
                return (False, None) if return_reason else False
        except Exception as e:
            reason = None
            try:
                status = getattr(e, "status_code", None)
                err_resp = getattr(e, "error_response", None)
                msg = ""
                if isinstance(err_resp, dict):
                    msg = (err_resp.get("message") or "")
                else:
                    msg = str(e)

                if status == 429 and ("monthly limit" in msg.lower() or "reached your monthly limit" in msg.lower()):
                    reason = "quota_exceeded"
            except Exception:
                pass

            try:
                app.logger.exception(f"safe_push failed to={to_id} {label} reason={reason}".strip())
            except Exception:
                pass

            return (False, reason) if return_reason else False


def _member_name(gid, uid):
    try:
        p = line_bot_api.get_group_member_profile(gid, uid)
        return p.display_name
    except Exception:
        return uid

def _lockdown_and_alert(gid, uid):
    """ป้องกัน kick สำคัญ: ล็อกดาวน์ + แจ้งเตือน (no-op safety)."""
    LOCKDOWN_UNTIL[gid] = _now() + LOCKDOWN_SECONDS_DEFAULT
    try:
        name = _member_name(gid, uid)
        safe_push(gid, TextSendMessage(f"⚠️ กลุ่มล็อกดาวน์ชั่วคราว {LOCKDOWN_SECONDS_DEFAULT} วินาที เพราะสมาชิกสำคัญออก: {name}"))
    except Exception:
        pass

# ====== ROUTES (secured webhook) ======
@app.route("/webhook", methods=["POST"])
@app.route("/callback", methods=["POST"])
def webhook():
    if request.content_length and request.content_length > MAX_BODY_BYTES:
        time.sleep(0.2)
        return "payload too large", 413

    if REQUIRE_LINE_UA:
        ua = request.headers.get("User-Agent", "")
        if not _safe_is_line_ua(ua):
            time.sleep(0.2)
            return "forbidden ua", 403

    ip = _client_ip()
    if not rl.allow(f"ip:{ip}", RL_IP_LIMIT, RL_IP_PERIOD):
        time.sleep(0.2)
        return "too many", 429

    body = request.get_data(as_text=True)
    ts_hdr = request.headers.get("X-Line-Request-Timestamp", "").strip()
    if ts_hdr.isdigit():
        try:
            tsv = int(ts_hdr)
            if tsv > 10**12: tsv = int(tsv / 1000)
            drift = abs(_now() - tsv)
            if drift > WEBHOOK_DRIFT_SEC:
                return "stale request", 401
        except Exception:
            pass

    sig = request.headers.get("X-Line-Signature", "")
    expected = base64.b64encode(hmac_new(CHANNEL_SECRET.encode(), body.encode(), sha256).digest()).decode()
    if not sig or not compare_digest(sig, expected):
        return "signature error", 400

    try:
        handler.handle(body, sig)
    except InvalidSignatureError:
        return "signature error", 400
    except Exception as e:
        app.logger.exception("err: %s", e)
        return "error", 500
    return "OK"

@app.get("/health")
def health(): return "OK", 200

@app.get("/copy/<acct>")
def copy_page(acct):
    acct = html_escape(acct.strip())
    logo_url = "https://image.tnews.co.th/uploads/images/contents/w1024/2025/01/CxaKtWLdkIgsdkMFfda3.webp?x-image-process=style/lg-webp"
    html = f"""<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>คัดลอกเลขบัญชี • กสิกรไทย</title>
<style>
  :root {{
    --bg:#0b1323; --card:#0f172a; --border:#334155; --text:#e5e7eb; --muted:#94a3b8;
    --brand:#16a34a; --brand-dark:#12803c; --warn:#f59e0b;
  }}
  html,body{{height:100%}}
  body{{margin:0;font-family:system-ui,-apple-system,"Segoe UI",Roboto,"Noto Sans Thai","Noto Sans",sans-serif;
       background:var(--bg);color:var(--text);display:flex;align-items:center;justify-content:center;padding:16px}}
  .card{{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:28px;max-width:520px;width:100%;
         box-shadow:0 10px 30px rgba(0,0,0,.35)}}
  .bank{{display:flex;align-items:center;gap:14px;margin-bottom:10px}}
  .bank-logo{{width:54px;height:54px;border-radius:50%;object-fit:cover;flex:0 0 54px;display:block}}
  .bank-title{{font-size:26px;font-weight:800;line-height:1.15}}
  .subtitle{{font-size:18px;color:var(--muted);margin-top:2px}}
  .acct-wrap{{margin:18px 0 8px;background:#091121;border:1px dashed var(--border);border-radius:14px;padding:18px;text-align:center}}
  .label{{font-size:18px;color:var(--muted);margin-bottom:6px}}
  .acct{{font-variant-numeric:tabular-nums;letter-spacing:.5px;font-size:34px;font-weight:800;color:#fde68a;word-break:break-word}}
  .help{{font-size:16px;color:var(--muted);margin:10px 0 18px}}
  .btns{{display:flex;gap:12px;flex-wrap:wrap}}
  button{{flex:1 1 180px;padding:16px 18px;border:0;border-radius:14px;cursor:pointer;font-size:20px;font-weight:800}}
  .primary{{background:var(--brand);color:#052e16}}
  .primary:hover{{background:var(--brand-dark)}}
  .secondary{{background:#0b1222;color:var(--text);border:1px solid var(--border)}}
  .status{{margin-top:16px;font-size:18px;font-weight:700}}
  .ok{{color:var(--brand)}} .warn{{color:var(--warn)}} .err{{color:#ef4444}}
  :is(button,.acct-wrap):focus-visible{{outline:3px solid #93c5fd;outline-offset:3px;border-radius:14px}}
  .sr{{position:absolute;left:-9999px}}
</style>
</head>
<body>
  <main class="card" role="main" aria-labelledby="title">
    <div class="bank">
      <img src="{logo_url}" alt="ธนาคารกสิกรไทย" class="bank-logo" loading="lazy" decoding="async"
           referrerpolicy="no-referrer"
           onerror="this.remove();document.getElementById('kbank-fallback').style.display='block';">
      <div>
        <div id="title" class="bank-title">ธนาคารกสิกรไทย</div>
        <div class="subtitle" aria-hidden="true">ธนาคารกสิกรไทย</div>
        <div id="kbank-fallback" class="subtitle" style="display:none">KBank</div>
      </div>
    </div>

    <div class="acct-wrap" tabindex="0" aria-live="polite" aria-atomic="true">
      <div class="label">เลขบัญชี</div>
      <div id="acct" class="acct" data-raw="{acct}"></div>
    </div>

    <p class="help">แตะ “คัดลอกเลขบัญชี” แล้วสลับไปที่แอปธนาคารเพื่อวางและโอนเงิน</p>

    <div class="btns">
      <button id="copyBtn" class="primary" aria-label="คัดลอกเลขบัญชี">คัดลอกเลขบัญชี</button>
      <button id="closeBtn" class="secondary" aria-label="ปิดหน้านี้">ปิดหน้านี้</button>
    </div>

    <div id="status" class="status warn">กำลังเตรียมคัดลอกให้อัตโนมัติ…</div>
    <p class="help" style="margin-top:14px">เคล็ดลับ: ถ้าคัดลอกไม่ติด ให้กดปุ่ม “คัดลอกเลขบัญชี” อีกครั้ง</p>
    <p class="sr" id="rawValue">{acct}</p>
  </main>

<script>
(function() {{
  const acctEl   = document.getElementById('acct');
  const statusEl = document.getElementById('status');
  const copyBtn  = document.getElementById('copyBtn');
  const closeBtn = document.getElementById('closeBtn');
  const raw      = (acctEl.getAttribute('data-raw') || '').trim();

  function formatReadable(v) {{
    const digits = v.replace(/\\D+/g,'');
    if (digits.length === 10) {{
      return digits.replace(/(\\d{{3}})(\\d)(\\d{{5}})(\\d)/, '$1-$2-$3-$4'); // 123-4-56789-0
    }}
    return digits.replace(/(\\d{{4}})(?=\\d)/g, '$1 ').trim();
  }}

  acctEl.textContent = formatReadable(raw);

  async function doCopy() {{
    const value = raw;
    try {{
      if (navigator.clipboard?.writeText) {{
        await navigator.clipboard.writeText(value);
      }} else {{
        const ta = document.createElement('textarea');
        ta.value = value; ta.style.position='fixed'; ta.style.opacity='0';
        document.body.appendChild(ta); ta.focus(); ta.select(); document.execCommand('copy'); ta.remove();
      }}
      statusEl.textContent = 'คัดลอกแล้ว ✓ นำไปวางในแอปธนาคารได้เลย';
      statusEl.className = 'status ok';
    }} catch(e) {{
      statusEl.textContent = 'คัดลอกไม่สำเร็จ กรุณากดปุ่ม “คัดลอกเลขบัญชี” อีกครั้ง';
      statusEl.className = 'status err';
    }}
  }}

  function robustClose() {{
    window.close();
    setTimeout(() => {{
      if (history.length > 1) {{
        history.back();
        return;
      }}
      const selfWin = window.open('', '_self');
      if (selfWin) {{
        try {{ selfWin.close(); }} catch(_) {{}}
      }}
      try {{
        location.replace('about:blank');
        statusEl.textContent = 'ปิดแท็บนี้ได้เลย';
        statusEl.className = 'status warn';
      }} catch(_) {{}}
    }}, 150);
  }}

  copyBtn.addEventListener('click', doCopy);
  closeBtn.addEventListener('click', robustClose);
  doCopy();
}})();
</script>
</body>
</html>"""
    resp = make_response(html, 200)
    resp.headers["Content-Type"] = "text/html; charset=utf-8"
    resp.headers["ngrok-skip-browser-warning"] = "true"
    return resp








from linebot.models import FlexSendMessage




_admin_ids_lock = threading.RLock()
ADMINS_JSON = os.path.join(DATA_DIR, "admins.json")

def _dedupe_admin_ids(ids):
    """คืน list แอดมินแบบตัดซ้ำ แต่คงลำดับเดิม"""
    seen = set()
    out = []
    for x in ids or []:
        x = (x or "").strip()
        if not x or x in seen:
            continue
        seen.add(x)
        out.append(x)
    return out

def save_admins_persist():
    """บันทึกรายชื่อแอดมินลงไฟล์ data/admins.json เพื่อให้ restart แล้วไม่หาย"""
    try:
        with _admin_ids_lock:
            payload = {"admins": _dedupe_admin_ids(ADMIN_IDS)}
        _atomic_write_json(ADMINS_JSON, payload)
    except Exception:
        try:
            app.logger.exception("save_admins_persist failed")
        except Exception:
            pass

def load_admins_persist():
    """โหลดรายชื่อแอดมินจาก data/admins.json มารวมกับ ADMIN_IDS ใน .env"""
    try:
        if not os.path.exists(ADMINS_JSON):
            return
        with open(ADMINS_JSON, "rb") as f:
            data = _loads_bytes(f.read())
        disk_admins = data.get("admins", []) if isinstance(data, dict) else data
        with _admin_ids_lock:
            for admin_uid in _dedupe_admin_ids(disk_admins):
                if admin_uid not in ADMIN_IDS:
                    ADMIN_IDS.append(admin_uid)
            ADMIN_IDS[:] = _dedupe_admin_ids(ADMIN_IDS)
    except Exception:
        try:
            app.logger.exception("load_admins_persist failed")
        except Exception:
            pass

def is_admin(uid):
    with _admin_ids_lock:
        return uid in ADMIN_IDS

def add_admin(uid):
    """เพิ่มแอดมินและบันทึกถาวร คืน True ถ้าเพิ่มใหม่ / False ถ้ามีอยู่แล้ว"""
    with _admin_ids_lock:
        if uid in ADMIN_IDS:
            return False
        ADMIN_IDS.append(uid)
        ADMIN_IDS[:] = _dedupe_admin_ids(ADMIN_IDS)
    save_admins_persist()
    return True

def remove_admin(uid):
    """ลบแอดมินและบันทึกถาวร คืน True ถ้าลบสำเร็จ / False ถ้าไม่พบ"""
    with _admin_ids_lock:
        if uid not in ADMIN_IDS:
            return False
        ADMIN_IDS.remove(uid)
    save_admins_persist()
    return True

# โหลดแอดมินที่เคยเพิ่มผ่านคำสั่งใน LINE ให้กลับมาหลัง restart/deploy
load_admins_persist()

def get_user_by_cid(cid_int):
    with with_users_lock():
        for u in users.values():
            if u["cid"] == cid_int:
                return u
    return None

def register_customer_by_uid(src, target_uid):
    """สมัครสมาชิกให้ target_uid และคืน (user_dict, created_new: bool)"""
    global nextCustomerId
    with with_users_lock():
        if target_uid in users:
            return users[target_uid], False
        name, pic = get_profile_display(src, target_uid)
        users[target_uid] = {
            "uid": target_uid,
            "cid": nextCustomerId,
            "name": name,
            "pictureUrl": pic,
            "credit": 0,
        }
        nextCustomerId += 1
        save_users_persist()
        return users[target_uid], True

def process_credit_command(text, uid):
    if not is_admin(uid):
        return "คำสั่งนี้ใช้ได้เฉพาะแอดมิน"
    m = re.match(r"^@([^\s]+)\s*/\s*(\d+)$", text)
    if not m: return "รูปแบบคำสั่งไม่ถูกต้อง (ตัวอย่าง: @สมชาย/500)"
    target_name, amt = m.group(1), int(m.group(2))

    with with_users_lock():
        target_user = next((u for u in users.values() if u["name"] == target_name), None)
        if not target_user:
            return f"ไม่พบผู้ใช้ {target_name}"
        target_user["credit"] = target_user.get("credit", 0) + amt
        save_users_persist()
        return (f"เติมเครดิต {fmt(amt)} บาท  "
                f"ID : {target_user['cid']}  {target_user['name']}  "
                f"คงเหลือ {fmt(target_user['credit'])} บาท")

def save_score_history_latest(state, round_no, camp, code):
    # ลบผลรอบเดิมออกทั้งหมด
    state["score_history"] = [
        h for h in state.get("score_history", [])
        if h.get("round") != round_no
    ]

    # ใส่ผลล่าสุดเท่านั้น
    state["score_history"].append({
        "round": round_no,
        "camp": camp,
        "code": code,
        "updated_at": datetime.now().isoformat()
    })






# ====== PEH HELPERS ======
def _peh_source_key(event):
    """คีย์ห้อง/กลุ่มสำหรับ PEH_LIST"""
    src = event.source
    return (
        getattr(src, "group_id", None)
        or getattr(src, "room_id", None)
        or getattr(src, "user_id", None)
        or "global"
    )


def _peh_extract_name(text: str) -> str:
    """
    ดึงส่วน "ชื่อ" ออกจากรายการเปะ โดยตัด emoji สถานะ, ตัวเลขท้าย,
    และวงเล็บ (n) ที่บอทเติมไว้ออก เพื่อใช้เปรียบเทียบความซ้ำ
    ตัวอย่าง:
      "สมชาย 300✅✅"  → "สมชาย"
      "สมหญิง(2) 500" → "สมหญิง"
      "เทสระบบ❌"      → "เทสระบบ"
    """
    raw = str(text or "").strip()
    # ลบ emoji สถานะ
    raw = re.sub(r"[✅❌⛔️\ufe0f]+", "", raw)
    # ลบตัวเลขท้าย (ยอดเงิน) พร้อม comma
    raw = re.sub(r"\s+[-+]?\d[\d,]*(?:\.\d+)?\s*$", "", raw)
    # ลบวงเล็บตัวเลข (n) ที่บอทเติม เช่น (2), (10)
    raw = re.sub(r"\s*\(\d+\)\s*$", "", raw)
    return raw.strip()


def _add_peh_item(event, text: str):
    """
    เพิ่มรายการ PEH ลงในห้อง/กลุ่ม/แชทนั้น ๆ
    ถ้าชื่อซ้ำกับรายการที่มีอยู่แล้ว จะเติม (2), (3), ... ต่อท้ายชื่อ
    """
    key = _peh_source_key(event)
    if key not in PEH_LIST:
        PEH_LIST[key] = []

    # ดึงชื่อของรายการใหม่
    new_name = _peh_extract_name(text)

    # นับว่าในรายการปัจจุบัน มีชื่อนี้อยู่กี่ครั้งแล้ว
    existing_count = sum(
        1 for item in PEH_LIST[key]
        if _peh_extract_name(item) == new_name
    )

    if existing_count > 0:
        # มีซ้ำ → เติม (n) ต่อท้ายชื่อ โดยไม่แตะส่วนตัวเลข/emoji
        # หา "จุดแทรก" = ก่อนตัวเลขท้ายหรือ emoji สถานะ
        # แยกส่วน suffix (ตัวเลข+emoji) ออกจากส่วนชื่อก่อน
        suffix_match = re.search(
            r"(\s+[-+]?\d[\d,]*(?:\.\d+)?\s*[✅❌⛔️\ufe0f]*)$",
            re.sub(r"[✅❌⛔️\ufe0f]+\s*$", lambda m: m.group(), text)
        )
        if suffix_match:
            body = text[:suffix_match.start()]
            suffix = text[suffix_match.start():]
        else:
            # ไม่มีตัวเลขท้าย อาจมีแค่ emoji หรือไม่มีเลย
            emoji_match = re.search(r"(\s*[✅❌⛔️\ufe0f]+\s*)$", text)
            if emoji_match:
                body = text[:emoji_match.start()]
                suffix = text[emoji_match.start():]
            else:
                body = text
                suffix = ""

        # ลบวงเล็บเก่าออกจาก body (กันกรณีแอดมินพิมพ์ซ้ำพร้อม (n) มาเอง)
        body = re.sub(r"\s*\(\d+\)\s*$", "", body.rstrip())
        text = f"{body}({existing_count + 1}){suffix}"

    PEH_LIST[key].append(text)
    return PEH_LIST[key]


def _peh_parse_status(item: str):
    """
    อ่านสถานะจาก emoji:
      ✅ = ชนะ  ❌ = แพ้  ⛔ = จาว
    กติกา: 1 รายการนับเป็น 1 ผล ยึดชนิดที่ปรากฏก่อนสุด
    """
    raw = str(item or "").strip()
    found = []
    for symbol in PEH_STATUS:
        pos = raw.find(symbol)
        if pos >= 0:
            found.append((pos, symbol))

    if not found:
        clean = re.sub(r"\s+", " ", raw).strip()
        return None, clean

    _, symbol = min(found, key=lambda x: x[0])
    clean_text = re.sub(r"[✅❌⛔]+", "", raw)
    clean_text = re.sub(r"\s+", " ", clean_text).strip()
    symbol_count = min(2, max(1, raw.count(symbol)))
    display_text = f"{clean_text}{symbol * symbol_count}"
    return symbol, display_text


def _peh_split_row(display_text: str, symbol):
    """แยกข้อความและตัวเลขสำหรับแสดงในตาราง"""
    text = str(display_text or "").strip()
    clean = re.sub(r"[✅❌⛔️\ufe0f]+", "", text)
    clean = re.sub(r"\s+", " ", clean).strip()
    m = re.match(r"^(.*?)(?:\s+)([-+]?\d[\d,]*(?:\.\d+)?)$", clean)
    emoji_text = ""
    if symbol:
        count = min(2, max(1, text.count(symbol)))
        emoji_text = symbol * count
    if m:
        left = m.group(1).strip()
        amount = m.group(2).strip()
        right = f"{amount}{emoji_text}" if emoji_text else amount
        return left, right
    return clean, emoji_text


def _peh_build_stats(items):
    stats = {"win": 0, "lose": 0, "draw": 0}
    parsed_items = []
    for item in items:
        symbol, display_text = _peh_parse_status(item)
        if symbol:
            stats[PEH_STATUS[symbol]["key"]] += 1
        parsed_items.append((display_text, symbol))
    return stats, parsed_items


def _peh_row(number: int, display_text: str, symbol) -> dict:
    """แถวตารางแบบมือถือ: [ลำดับ] [ชื่อ/ข้อความ] [ตัวเลข + emoji]"""
    number_color = {
        "✅": "#15803D",
        "❌": "#B91C1C",
        "⛔": "#A16207",
    }.get(symbol, "#60717C")
    left_text, right_text = _peh_split_row(display_text, symbol)
    return {
        "type": "box",
        "layout": "horizontal",
        "paddingTop": "5px",
        "paddingBottom": "5px",
        "alignItems": "center",
        "contents": [
            {
                "type": "text", "text": str(number),
                "size": "xs", "weight": "bold",
                "color": number_color, "align": "center", "flex": 1,
            },
            {
                "type": "text", "text": left_text,
                "size": "xs", "color": "#24313A",
                "wrap": True, "gravity": "center", "flex": 5,
            },
            {
                "type": "text", "text": right_text,
                "size": "xs", "weight": "bold",
                "color": "#24313A", "align": "end",
                "gravity": "center", "flex": 4,
                "wrap": False, "adjustMode": "shrink-to-fit",
            },
        ],
    }


def _peh_page_bubble(page_items, page_no: int, page_total: int, stats: dict, total: int):
    """1 bubble = 1 หน้า"""
    rows = []
    for idx, (display_text, symbol) in enumerate(page_items):
        global_no = (page_no - 1) * PEH_ITEMS_PER_PAGE + idx + 1
        rows.append(_peh_row(global_no, display_text, symbol))
        if idx != len(page_items) - 1:
            rows.append({"type": "separator", "color": "#EEF2F4"})

    if not rows:
        rows = [{
            "type": "text", "text": "ยังไม่มีรายการ",
            "size": "sm", "color": "#94A3AB",
            "align": "center", "margin": "lg",
        }]

    header_contents = [
        {
            "type": "box", "layout": "horizontal", "alignItems": "center",
            "contents": [
                {
                    "type": "box", "layout": "vertical",
                    "width": "5px", "height": "26px",
                    "cornerRadius": "8px", "backgroundColor": "#62B89B",
                    "contents": []
                },
                {
                    "type": "box", "layout": "vertical",
                    "margin": "sm", "flex": 1,
                    "contents": [
                        {
                            "type": "text", "text": "สกอบั้งไฟวันนี้",
                            "size": "md", "weight": "bold", "color": "#26353D",
                        },
                        {
                            "type": "text",
                            "text": f"ทั้งหมด {total} รายการ",
                            "size": "xxs", "color": "#8B989F", "margin": "xs",
                        },
                    ]
                },
                {
                    "type": "text",
                    "text": f"หน้า {page_no}/{page_total}",
                    "size": "xxs", "color": "#9AA5AB",
                    "align": "end", "gravity": "center", "flex": 0,
                },
            ],
        }
    ]

    if page_no == 1:
        header_contents += [
            {
                "type": "box", "layout": "horizontal",
                "spacing": "sm", "margin": "md",
                "contents": [
                    {
                        "type": "box", "layout": "vertical", "flex": 1,
                        "cornerRadius": "10px", "backgroundColor": "#F1FAF5",
                        "paddingAll": "7px",
                        "contents": [
                            {"type": "text", "text": "ชนะ", "size": "xxs", "color": "#708078", "align": "center"},
                            {"type": "text", "text": f"✅ {stats['win']}", "size": "sm", "weight": "bold", "color": "#267A55", "align": "center", "margin": "xs"},
                        ],
                    },
                    {
                        "type": "box", "layout": "vertical", "flex": 1,
                        "cornerRadius": "10px", "backgroundColor": "#FFF5F5",
                        "paddingAll": "7px",
                        "contents": [
                            {"type": "text", "text": "แพ้", "size": "xxs", "color": "#857474", "align": "center"},
                            {"type": "text", "text": f"❌ {stats['lose']}", "size": "sm", "weight": "bold", "color": "#B84A4A", "align": "center", "margin": "xs"},
                        ],
                    },
                    {
                        "type": "box", "layout": "vertical", "flex": 1,
                        "cornerRadius": "10px", "backgroundColor": "#FFF9EF",
                        "paddingAll": "7px",
                        "contents": [
                            {"type": "text", "text": "จาว", "size": "xxs", "color": "#837A68", "align": "center"},
                            {"type": "text", "text": f"⛔ {stats['draw']}", "size": "sm", "weight": "bold", "color": "#9A711F", "align": "center", "margin": "xs"},
                        ],
                    },
                ],
            }
        ]

    header_contents.append({
        "type": "separator", "margin": "md", "color": "#E8EDF0",
    })

    return {
        "type": "bubble",
        "size": "giga",
        "header": {
            "type": "box", "layout": "vertical",
            "backgroundColor": "#FFFFFF",
            "paddingStart": "14px", "paddingEnd": "14px",
            "paddingTop": "12px", "paddingBottom": "7px",
            "contents": header_contents,
        },
        "body": {
            "type": "box", "layout": "vertical",
            "backgroundColor": "#FFFFFF",
            "paddingStart": "14px", "paddingEnd": "14px",
            "paddingTop": "3px", "paddingBottom": "8px",
            "contents": rows,
        },
        "footer": {
            "type": "box", "layout": "vertical",
            "backgroundColor": "#FAFBFC", "paddingAll": "6px",
            "contents": [{
                "type": "text", "text": TARGET_GROUP_NAME,
                "size": "xxs", "color": "#98A4AA",
                "align": "center", "wrap": True,
            }],
        },
    }


def peh_flex_messages(event) -> list:
    """
    คืนค่าเป็น list ของ FlexSendMessage
    - 20 รายการ / bubble
    - สูงสุด 12 bubbles / carousel
    """
    key = _peh_source_key(event)
    items = PEH_LIST.get(key, [])
    total = len(items)
    stats, parsed_items = _peh_build_stats(items)

    if not parsed_items:
        pages = [[]]
    else:
        pages = [
            parsed_items[i:i + PEH_ITEMS_PER_PAGE]
            for i in range(0, len(parsed_items), PEH_ITEMS_PER_PAGE)
        ]

    page_total = len(pages)
    bubbles = [
        _peh_page_bubble(
            page_items=page_items,
            page_no=page_no,
            page_total=page_total,
            stats=stats,
            total=total,
        )
        for page_no, page_items in enumerate(pages, start=1)
    ]

    carousel_groups = [
        bubbles[i:i + PEH_MAX_BUBBLES_PER_CAROUSEL]
        for i in range(0, len(bubbles), PEH_MAX_BUBBLES_PER_CAROUSEL)
    ]

    messages = []
    for group in carousel_groups:
        if len(group) == 1:
            contents = group[0]
        else:
            contents = {"type": "carousel", "contents": group}
        messages.append(FlexSendMessage(
            alt_text=(
                f"สกอบั้งไฟวันนี้ • "
                f"ชนะ {stats['win']} แพ้ {stats['lose']} จาว {stats['draw']} "
                f"• รวม {total} รายการ"
            ),
            contents=contents,
        ))
    return messages


# ====== MESSAGE HANDLER ======
@handler.add(MessageEvent, message=TextMessage)
def on_message(event: MessageEvent):
    global nextCustomerId

    uid = event.source.user_id
    gid = getattr(event.source, "group_id", None)
    key = room_key(event.source)
    
    # [FIXED] กำหนด text ที่นี่ครั้งเดียว
    text = (event.message.text or "").strip()

    # กัน LINE retry / webhook ซ้ำ: message id เดิมต้องไม่ถูกประมวลผลซ้ำ
    if already_processed_message(getattr(event.message, "id", None)):
        return

    if not in_group_or_room(event.source):
     return

    # Group allow/deny/ban
    if gid:
        if gid in BANNED_GROUPS or gid in DENY_GROUP_IDS:
            return
        if not is_allowed_group(gid):
            return
        if _locked_group(gid) and not is_admin(uid):
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("ระบบ: กลุ่มกำลังล็อกดาวน์ชั่วคราว ติดต่อแอดมินเพื่อปลดล็อก"))
            return

    # user ban/mute
    if uid in BANNED_UIDS:
        return
    if MUTED_UNTIL.get(uid, 0) > _now():
        if not _notice_throttled(uid):
            safe_reply(event, TextSendMessage("ระบบ: คุณถูกจำกัดการส่งข้อความชั่วคราว (anti-spam)"))
        return

    # rate limit room/user
    if not rl.allow(f"room:{key}", RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD):
        return
    if not rl.allow(f"uid:{uid}:burst", RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD) or \
       not rl.allow(f"uid:{uid}:day", RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD):
        STRIKES[uid] = STRIKES.get(uid, 0) + 1
        if STRIKES[uid] >= ABUSE_STRIKE_TO_MUTE:
            MUTED_UNTIL[uid] = _now() + MUTE_SECONDS_DEFAULT
            STRIKES[uid] = 0
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage(f"ระบบ: มิวท์ {MUTE_SECONDS_DEFAULT} วินาที เนื่องจากข้อความถี่ผิดปกติ"))
        else:
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("ระบบ: ข้อความถี่เกินกำหนด ช่วยเว้นช่วงหน่อยนะ"))
        return

    # cache for unsend monitor
    msgCache[event.message.id] = {"text": (event.message.text or ""), "ts": time.time()}

    # ── auto sync ชื่อ LINE นานๆครั้ง (NAME_SYNC_TTL) ──
    if uid in users:
        _now_ts = time.time()
        if _now_ts - _name_sync_ts.get(uid, 0) > _NAME_SYNC_TTL:
            _name_sync_ts[uid] = _now_ts
            try:
                _new_name, _new_pic = get_profile_display(event.source, uid)
                if _new_name and _new_name != users[uid].get("name"):
                    with with_users_lock():
                        users[uid]["name"] = _new_name
                        users[uid]["pictureUrl"] = _new_pic
                    save_users_persist()
            except Exception:
                pass
    now = time.time()
    if len(msgCache) > 4000:
        for k, v in list(msgCache.items()):
            if now - v["ts"] > CACHE_TTL_SEC: msgCache.pop(k, None)

    # [FIXED] รวบรวมตรรกะทั้งหมดที่เกี่ยวข้องกับ Room State (st) ไว้ใน Lock เดียว
    with with_rooms_lock():
        if key not in rooms:
            rooms[key] = start_state()
        st = rooms[key]

        # [FIXED] ตรวจสอบ Cooldown ภายใน Lock
        if not is_admin(uid):
            whitelist = {"add", "c", "กต", "บช", "x", "xx", "x*", "ถอน", "วิธีเล่น", "วิธีการเล่น", "เล่น"}
            text_preview = text.lower()
            head = text_preview.split(" ", 1)[0] if text_preview else ""
            scope_key = f"{uid}:{key}"

            if head not in whitelist:
                if not _should_reply_now(scope_key):
                    # เงียบ: ไม่ตอบและไม่ประมวลผลคำสั่ง เพื่อกันรัวจริง ๆ
                    return
        # --- คำสั่งล้างกำไรทั้งหมด (เฉพาะ Admin) ---
        if R_CLEAR_PROFIT.match(text):
            if uid not in ADMIN_IDS:
                return  # ไม่ใช่แอดมินไม่ต้องตอบโต้
            
            with with_rooms_lock(): # ใช้ lock เพื่อความปลอดภัยของข้อมูล
                METRICS["profit_sum"] = 0
                METRICS["loss_sum"] = 0
                
            now = datetime.now().strftime("%H:%M:%S")
            reply_msg = (
                "✅ รีเซ็ตข้อมูลกำไรทั้งหมดเรียบร้อยแล้ว\n"
                f"🕒 เวลา: {now}\n"
                "💰 ยอดคงเหลือปัจจุบัน: 0"
            )
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=reply_msg))
            return
        


        # ===== วิธีเล่น / เล่นยังไง / เล่นไง / วิธีการเล่น / เล่นแบบใด =====
        t = text.strip()
        t2 = " ".join(t.split())  # บีบช่องว่างซ้ำให้เหลือ 1

        if t in PLAY_HELP_COMMANDS or t2 in PLAY_HELP_COMMANDS:
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return

        # กรณีผู้ใช้พิมพ์แบบมีเว้นวรรค เช่น "เล่น ยังไง"
        if t2.startswith("เล่น") and ("ยังไง" in t2 or "ไง" in t2 or "แบบใด" in t2):
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return

        if t2.startswith("วิธี") and ("เล่น" in t2):
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return
    

        # ===== Admin: add/del with @mention or Uxxxxxxxx + optional PIN =====
        # ใช้ได้ทั้ง: admin add @ชื่อ / admin @ชื่อ / เพิ่มแอดมิน @ชื่อไลน์
        if R_ADMIN_ADD.match(text):
            if not is_admin(uid):
                return

            target_uid = first_mentioned_uid(event)

            # เผื่อกรณีพิมพ์ UID ตรง ๆ เช่น: เพิ่มแอดมิน Uxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
            if not target_uid:
                m = re.search(r"\b([Uu][0-9a-f]{32})\b", text)
                if m:
                    target_uid = m.group(1)

            if not target_uid:
                safe_reply(event, TextSendMessage(
                    "❌ กรุณาแท็กชื่อผู้ใช้ที่ต้องการเพิ่ม\nตัวอย่าง: เพิ่มแอดมิน @ชื่อไลน์"
                ))
                return

            target_name, _ = get_profile_display(event.source, target_uid)

            if add_admin(target_uid):
                safe_reply(event, TextSendMessage(
                    f"✅ เพิ่มแอดมินสำเร็จ\n👤 {target_name}"
                ))
            else:
                safe_reply(event, TextSendMessage(
                    f"ℹ️ ผู้ใช้นี้เป็นแอดมินอยู่แล้ว\n👤 {target_name}"
                ))
            return

        if R_ADMIN_DEL.match(text):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            target_uid = first_mentioned_uid(event)
            if not target_uid:
                m = re.search(r"\b([Uu][0-9a-f]{32})\b", text)
                if m: target_uid = m.group(1)
            if not target_uid:
                safe_reply(event, TextSendMessage("โปรดแท็กผู้ใช้ หรือระบุ userId ที่ขึ้นต้นด้วย U...")); return
            pin = _admin_auth_pin(text)
            if ADMIN_PIN and not compare_digest(pin, ADMIN_PIN):
                safe_reply(event, TextSendMessage("PIN ไม่ถูกต้อง")); return
            if remove_admin(target_uid):
                safe_reply(event, TextSendMessage("ลบแอดมินสำเร็จ ✓"))
            else:
                safe_reply(event, TextSendMessage("ไม่พบไอดีนี้ในรายชื่อแอดมิน"))
            return
        
        # ===== Admin: ล้างแอดมินทั้งหมด (เหลือแค่คนที่สั่ง) — ล้างแอดมิน <PIN> =====
        if re.match(r"^ล้างแอดมิน\b", text):
            if not is_admin(uid):
                return
            pin = _admin_auth_pin(" " + text)
            if ADMIN_PIN and not compare_digest(pin, ADMIN_PIN):
                safe_reply(event, TextSendMessage("PIN ไม่ถูกต้อง\nรูปแบบ: ล้างแอดมิน <PIN>")); return
            with _admin_ids_lock:
                n_old = len(ADMIN_IDS)
                ADMIN_IDS[:] = [uid]  # เก็บคนสั่งไว้ กันไม่มีแอดมินเหลือ
            save_admins_persist()
            safe_reply(event, TextSendMessage(
                f"✅ ล้างแอดมินแล้ว ({n_old} → 1)\nเหลือแอดมินคือคุณคนเดียว\nเพิ่มใหม่: เพิ่มแอดมิน @ชื่อ"
            )); return

        # ===== Admin: ล้างข้อมูลลูกค้าทั้งหมด — ล้างลูกค้า <PIN> =====
        if re.match(r"^ล้างลูกค้า\b", text):
            if not is_admin(uid):
                return
            pin = _admin_auth_pin(" " + text)
            if ADMIN_PIN and not compare_digest(pin, ADMIN_PIN):
                safe_reply(event, TextSendMessage("PIN ไม่ถูกต้อง\nรูปแบบ: ล้างลูกค้า <PIN>")); return
            if any(stx.get("bet_index") for stx in rooms.values()):
                safe_reply(event, TextSendMessage("❌ ล้างไม่ได้: ยังมีบิลค้างอยู่ ให้สรุปผลหรือพิมพ์ xx ก่อน")); return
            with with_users_lock():
                n_old = len(users)
                total_credit = sum(int(u.get("credit", 0) or 0) for u in users.values())
                users.clear()
                nextCustomerId = 201
                _save_users_snapshot()  # เขียนทันที ไม่รอ debounce
            safe_reply(event, TextSendMessage(
                f"✅ ล้างข้อมูลลูกค้าทั้งหมดแล้ว\nลบ {n_old} คน • เครดิตรวมที่ถูกลบ {fmt(total_credit)} บาท\nID ใหม่จะเริ่มที่ 201"
            )); return

        # ===== Admin: list (เช็คแอดมิน / admin list) =====
        if R_ADMIN_LIST.match(text):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            with _admin_ids_lock:
                current_admins = list(ADMIN_IDS)
            if not current_admins:
                safe_reply(event, TextSendMessage("ℹ️ ยังไม่มีแอดมินในระบบ")); return
            lines = ["👑 รายชื่อแอดมินทั้งหมด\n"]
            for i, a_uid in enumerate(current_admins, 1):
                try:
                    profile = line_bot_api.get_profile(a_uid)
                    a_name = profile.display_name
                except Exception:
                    a_name = users.get(a_uid, {}).get("name", "(ไม่ทราบชื่อ)")
                lines.append(f"{i}. {a_name}\n   ID: {a_uid}")
            lines.append(f"\nรวม {len(current_admins)} คน")
            safe_reply(event, TextSendMessage("\n".join(lines)))
            return

        # ===== Admin: ตรวจประวัติสลิปที่เติมแล้ว (สลิป <transRef>) =====
        m_slip = re.match(r"^สลิป\s+(\S+)$", text)
        if m_slip:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            safe_reply(event, TextSendMessage(slip_lookup_text(m_slip.group(1)))); return

        # ===== Group ID (gid) =====
        if re.match(r"^gid\b", text, re.IGNORECASE):
            if not gid:
                safe_reply(event, TextSendMessage("ใช้คำสั่งนี้ได้เฉพาะในกลุ่ม/ห้อง"))
                return
            safe_reply(event, TextSendMessage(f"GID ของกลุ่มนี้: {gid}"))
            return


        # ==== ดูตารางรายการเดิมพัน (cm — เฉพาะกลุ่มหลังบ้าน) ====
        if text.lower() == "cm":
            if not gid or not is_backoffice_group_id(gid):
                return
            snapshot = [(rk, stx.copy()) for rk, stx in rooms.items()]  # shallow ก็พอ
            all_bets, total_hi, total_lo = [], 0, 0
            hi_count, lo_count = 0, 0
            active_round_labels = []
            seen_round_labels = set()

            for rk, stx in snapshot:
                pair_no = stx.get("pairNo", 0)
                camp_name = current_camp(stx)
                round_label = f"{camp_name} • รอบ {pair_no}"
                if pair_no and round_label not in seen_round_labels:
                    active_round_labels.append(round_label)
                    seen_round_labels.add(round_label)

                for b in stx.get("bet_index", {}).values():
                    all_bets.append({
                        "name": b["name"],
                        "side": b["side"],
                        "amount": b["amount"],
                        "pairNo": pair_no,
                        "camp": camp_name,
                    })
                    if b["side"] == "HI":
                        total_hi += b["amount"]
                        hi_count += 1
                    else:
                        total_lo += b["amount"]
                        lo_count += 1

            if not all_bets:
                safe_reply(event, TextSendMessage("(ยังไม่มีบิลในระบบ)"))
                return

            title_text = "ตารางบิลทั้งหมด"
            if len(active_round_labels) == 1:
                title_text = f"ตารางบิลทั้งหมด ({active_round_labels[0]})"
            elif len(active_round_labels) > 1:
                title_text = "ตารางบิลทั้งหมด (หลายค่าย/หลายรอบ)"

            rows = [
                {"type":"box","layout":"vertical","spacing":"xs","contents":[
                    {"type":"text","text":title_text,"weight":"bold","align":"center","size":"md","wrap":True},
                    {"type":"text","text":f"จำนวนบิลสูง {hi_count} บิล • จำนวนบิลต่ำ {lo_count} บิล","size":"sm","align":"center","weight":"bold","wrap":True,
                     "color":"#1565C0" if lo_count == 0 else "#374151"},
                ]},
                {"type":"separator","margin":"md"},
            ]

            if len(active_round_labels) > 1:
                rows.append({
                    "type":"box","layout":"vertical","spacing":"xs","contents":[
                        {"type":"text","text":"ค่าย / รอบที่เปิดอยู่","size":"sm","weight":"bold","color":"#374151"},
                        *[
                            {"type":"text","text":f"• {label}","size":"xs","wrap":True,"color":"#6B7280"}
                            for label in active_round_labels[:8]
                        ]
                    ]
                })
                rows.append({"type":"separator","margin":"md"})

            rows.extend([
                {"type":"box","layout":"horizontal","spacing":"sm","contents":[
                    {"type":"text","text":"ผู้เล่น","flex":5,"size":"xs","weight":"bold","wrap":True},
                    {"type":"text","text":"จำนวนเดิมพัน/กี่บาท","flex":5,"size":"xs","align":"center","weight":"bold","wrap":True},
                    {"type":"text","text":"รอบ","flex":2,"size":"xs","align":"center","weight":"bold","wrap":True},
                ]},
                {"type":"separator","margin":"sm"},
            ])

            def _short_name(name, limit=14):
                name = (name or "").strip()
                if len(name) <= limit:
                    return name
                return name[:limit-1].rstrip() + "…"

            sorted_bets = sorted(
                all_bets,
                key=lambda x: (
                    -(x.get("amount", 0) or 0),
                    x.get("pairNo", 0),
                    x.get("camp", "") or "",
                    x.get("name", "") or "",
                )
            )

            for b in sorted_bets:
                bet_text = f'{"สูง" if b["side"]=="HI" else "ต่ำ"} {fmt(b["amount"])} บาท'
                rows.append({"type":"box","layout":"horizontal","spacing":"sm","contents":[
                    {"type":"text","text":_short_name(b["name"]),"flex":5,"size":"xs","wrap":True},
                    {"type":"text","text":bet_text,
                     "flex":5,"size":"xs","align":"center",
                     "color":"#1565C0" if b["side"]=="HI" else "#E53935","wrap":True},
                    {"type":"text","text":str(b["pairNo"]),"flex":2,"size":"xs","align":"center","wrap":True},
                ]})
            rows.append({"type":"separator","margin":"md"})
            rows.append({"type":"text","text":f"รวมสูง: {fmt(total_hi)} บาท ({hi_count} บิล)","size":"sm","align":"end","weight":"bold","color":"#1565C0"})
            rows.append({"type":"text","text":f"รวมต่ำ: {fmt(total_lo)} บาท ({lo_count} บิล)","size":"sm","align":"end","weight":"bold","color":"#E53935"})
            safe_reply(event, FlexSendMessage(
                alt_text="ตารางบิลทั้งหมด",
                contents={"type":"bubble","size":"mega","body":{"type":"box","layout":"vertical","spacing":"sm","paddingAll":"12px","contents":rows}}
            ))
            return

        # ===== Moderator: ban/mute/unban/unmute =====
        m_cmd = re.match(r"^(ban|unban|mute|unmute)\b(?:\s+(.*))?$", text, re.IGNORECASE)
        if m_cmd:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            cmd = m_cmd.group(1).lower()
            args = (m_cmd.group(2) or "").strip()
            target_uid = first_mentioned_uid(event)
            sec = None
            if not target_uid:
                m_uid = re.match(r"^(U[0-9a-f]{32})\b(?:\s+(\d+))?$", args, re.IGNORECASE)
                if m_uid:
                    target_uid = m_uid.group(1)
                    sec = int(m_uid.group(2) or MUTE_SECONDS_DEFAULT) if cmd == "mute" else None
                else:
                    m_at = re.match(r"^@(.+?)(?:\s+(\d+))?$", args)
                    if m_at:
                        safe_reply(event, TextSendMessage("โปรดแท็กผู้ใช้จาก UI ของ LINE (ชื่อเป็นลิงก์สีน้ำเงิน)"))
                        return
            if not target_uid:
                safe_reply(event, TextSendMessage("รูปแบบ: mute @ผู้ใช้ [วินาที] / unmute @ผู้ใช้ / ban @ผู้ใช้ / unban @ผู้ใช้"))
                return
            if cmd == "mute":
                if sec is None:
                    m_sec = re.search(r"\b(\d+)\b$", args) if args else None
                    sec = int(m_sec.group(1)) if m_sec else MUTE_SECONDS_DEFAULT
                MUTED_UNTIL[target_uid] = _now() + max(1, sec); safe_reply(event, TextSendMessage(f"มิวท์ {sec} วินาทีแล้ว")); return
            if cmd == "unmute":
                MUTED_UNTIL.pop(target_uid, None); safe_reply(event, TextSendMessage("ปลดมิวท์แล้ว")); return
            if cmd == "ban":
                BANNED_UIDS.add(target_uid); safe_reply(event, TextSendMessage("แบนผู้ใช้แล้ว")); return
            if cmd == "unban":
                BANNED_UIDS.discard(target_uid); safe_reply(event, TextSendMessage("ปลดแบนแล้ว")); return

        # ===== Admin/User: เช็ค UID =====
        if re.match(r"^uid\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)
            # ถ้าไม่แท็กใคร: โชว์ UID ของตัวเอง (ไม่ต้องเป็นแอดมิน)
            if not target_uid or target_uid == uid:
                name, _ = get_profile_display(event.source, uid)
                safe_reply(event, TextSendMessage(f"UID ของคุณ ({name}): {uid}"))
                return
            # ถ้าจะดู UID คนอื่น ต้องเป็นแอดมิน
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("เฉพาะแอดมินเท่านั้นที่ดู UID คนอื่นได้")); 
                return
            name, _ = get_profile_display(event.source, target_uid)
            safe_reply(event, TextSendMessage(f"UID ของ {name}: {target_uid}"))
            return

                # ===== Backoffice (FREE): ดูสรุป/กำไรล่าสุด =====
        # ใช้ในกลุ่มหลังบ้านเท่านั้น (ไม่ต้อง push ลดโควต้า)
        if gid and gid in BACKOFFICE_GROUP_IDS and re.match(r"^(?:กำไรล่าสุด|ยอด|lastprofit|last)\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); 
                return
            p = load_last_settle()
            if not p:
                safe_reply(event, TextSendMessage("ยังไม่มีสรุปผลล่าสุดในระบบ")); 
                return
            safe_reply(event, TextSendMessage(settle_payload_to_text(p)))
            return

        # ===== Helper: คืน escrow ทุกคนในห้อง =====
        def _refund_all_escrow_to_users(st):
            refunded_map = {}  # uid -> amount
            for tuid, esc_amt in list(st.get("escrow", {}).items()):
                if esc_amt > 0 and tuid in users:
                    users[tuid]["credit"] = users[tuid].get("credit", 0) + esc_amt
                    refunded_map[tuid] = esc_amt
            st["escrow"].clear()
            return refunded_map
        
        # -

        text = (event.message.text or "").strip()

        # ====== GET GROUP ID ======
        if R_GETID.match(text):
            src = event.source

            group_id = getattr(src, "group_id", None)
            room_id = getattr(src, "room_id", None)

            if group_id:
                msg = f"Group ID: {group_id}"
            elif room_id:
                msg = f"Room ID: {room_id}"
            else:
                msg = "❌ คำสั่งนี้ใช้ได้เฉพาะในกลุ่มหรือห้องเท่านั้น"

            safe_reply(event, TextSendMessage(text=msg))
            return


        # ==== CLEAR / RESET ====
        if re.match(r"^(clear|reset)\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            total_refund_sum = 0
            total_refund_users = 0

            with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock() เพราะ with_rooms_lock() คลุมอยู่แล้ว
                if re.search(r"\ball\b", text, re.IGNORECASE):
                    # เคลียร์ทั้งระบบ — คืน escrow ทุกห้อง
                    for rk in list(rooms.keys()):
                        stx = rooms[rk]
                        refunded_map = _refund_all_escrow_to_users(stx)
                        total_refund_sum += sum(refunded_map.values())
                        total_refund_users += len(refunded_map)
                        rooms[rk] = start_state()

                    # 👉 เพิ่มบรรทัดนี้: รีเซ็ตกำไรสะสม
                    METRICS["profit_sum"] = 0
                    METRICS["loss_sum"] = 0
                    clear_round_action_guard()

                    msg = "เคลียร์ทั้งระบบ (รอบ/ทุน) สำเร็จ ✓"
                else:
                    # เคลียร์เฉพาะห้องนี้ — คืน escrow ห้องนี้
                    stx = rooms.get(key) or start_state()
                    refunded_map = _refund_all_escrow_to_users(stx)
                    total_refund_sum += sum(refunded_map.values())
                    total_refund_users += len(refunded_map)
                    rooms[key] = start_state()
                    clear_round_action_guard(key)
                    msg = "เคลียร์ห้องนี้ (รอบ/ทุน) สำเร็จ ✓"

                save_users_persist()

            msg += f"\nคืนเครดิต {fmt(total_refund_sum)} บาท ให้ {total_refund_users} คน"
            safe_reply(event, TextSendMessage(msg)); return

        # ==== เติม/ลบทุน+เครดิต แบบ $+ <cid> <amt> / $- <cid> <amt> ====
        m_add = re.match(r"^\$\+\s*(\d+)\s+(\d+)$", text)
        m_sub = re.match(r"^\$-\s*(\d+)\s+(\d+)$", text)
        if m_add or m_sub:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            cid = int((m_add or m_sub).group(1))
            amt = int((m_add or m_sub).group(2))
            with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock() เพราะ with_rooms_lock() คลุมอยู่แล้ว
                target = get_user_by_cid(cid)
                if not target:
                    safe_reply(event, TextSendMessage(f"ไม่พบ ID {cid}")); return
                tuid = target["uid"]
                # [FIXED] เข้าถึง rooms[key] ได้โดยตรง เพราะ with_rooms_lock() คลุมอยู่
                fund_before = rooms[key]["funds"].get(tuid, 0) 
                credit_before = target.get("credit", 0)

                if m_add:
                    target["credit"] = credit_before + amt
                    rooms[key]["funds"][tuid] = fund_before + amt
                    msg = f"✅เติมเครดิต {fmt(amt)} บาท  ID : {cid}  {target['name']}  คงเหลือ {fmt(target['credit'])} บาท"
                # แก้เป็น
                else:
                    if credit_before < amt:
                        safe_reply(event, TextSendMessage(
                            f"❌ เครดิตไม่พอ  ID : {cid}  {target['name']}  มีเพียง {fmt(credit_before)} บาท"
                        )); return
                    target["credit"] = credit_before - amt
                    rooms[key]["funds"][tuid] = max(fund_before - amt, 0)
                    msg = f"✅ลบเครดิต {fmt(amt)} บาท  ID : {cid}  {target['name']}  คงเหลือ {fmt(target['credit'])} บาท"

                save_users_persist()
            safe_reply(event, TextSendMessage(msg)); return
        



        m_del = R_DEL_USER.match(text)
        if m_del:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน"))
                return

            cid = int(m_del.group(1))

            with with_users_lock():
                target_uid = None
                target = None

                for u in users.values():
                    if u["cid"] == cid:
                        target_uid = u["uid"]
                        target = u
                        break

                if not target:
                    safe_reply(event, TextSendMessage(f"ไม่พบ ID {cid}"))
                    return

                if has_active_bet(target_uid):
                    safe_reply(event, TextSendMessage("❌ ลบไม่ได้: ลูกค้ามีบิลค้างอยู่"))
                    return

                users.pop(target_uid)
                save_users_persist()

            safe_reply(event, TextSendMessage(f"✅ ลบลูกค้า ID {cid} สำเร็จ"))
            return        



        # ===== เติมเครดิตรูปแบบ @ชื่อ/จำนวน =====
        if text.startswith("@") and "/" in text:
            msg = process_credit_command(text, uid)
            safe_reply(event, TextSendMessage(msg)); return

        # ==== ลูกค้า: สมัคร/การ์ด/บัญชี/กต ====
        if re.match(r"^add\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)

            # แอดมินสมัครสมาชิกแทนลูกค้าด้วยการแท็กชื่อ
            if target_uid and target_uid != uid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("เฉพาะแอดมินเท่านั้นที่สมัครสมาชิกแทนลูกค้าได้"))
                    return
                target_user, created = register_customer_by_uid(event.source, target_uid)
                if created:
                    safe_reply(event, TextSendMessage(
                        f"✅ สมัครสมาชิกให้ {target_user['name']} สำเร็จ\n🎫 ID: {target_user['cid']}\nพิมพ์ C @ชื่อไลน์ เพื่อดูบัตรสมาชิก"
                    ))
                else:
                    safe_reply(event, TextSendMessage(
                        f"ℹ️ {target_user['name']} มี ID อยู่แล้ว: {target_user['cid']}"
                    ))
                return

            # สมัครสมาชิกด้วยตัวเอง
            if text.lower() == "add":
                target_user, created = register_customer_by_uid(event.source, uid)
                if not created:
                    safe_reply(event, TextSendMessage(f"คุณมี ID แล้ว: {target_user['cid']}"))
                    return
                safe_reply(event, flex_register_success(target_user["cid"])); return

        # ลูกค้าพิมพ์ "ถอน" ที่ไหนก็ได้ในข้อความ → แสดงการ์ด C
        if "ถอน" in text:
            u = users.get(uid)
            if not u:
                safe_reply(event, TextSendMessage("พิมพ์ add เพื่อรับไอดีก่อน"))
                return
            safe_reply(event, flex_customer_card(st, u)); return




        if re.match(r"^c\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)

            # แอดมินดูบัตร/ID ของลูกค้าที่ถูกแท็ก
            if target_uid and target_uid != uid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("เฉพาะแอดมินเท่านั้นที่ดูข้อมูลลูกค้าคนอื่นได้"))
                    return
                u = users.get(target_uid)
                if not u:
                    safe_reply(event, TextSendMessage("ลูกค้ายังไม่ได้สมัครสมาชิก\nให้แอดมินพิมพ์ add @ชื่อไลน์ ก่อน"))
                    return
                safe_reply(event, flex_customer_card(st, u)); return

            # ลูกค้าดูบัตรของตัวเอง
            if text.lower() == "c":
                u = users.get(uid)
                if not u:
                    safe_reply(event, TextSendMessage("พิมพ์ add เพื่อรับไอดีก่อน"))
                    return
                safe_reply(event, flex_customer_card(st, u)); return

        if text.strip().lower() in ("บช", "บัญชี", "เลขบัญชี"):
            # ส่ง "ข้อความอย่างเดียว" ไม่ส่งปุ่ม Flex
            safe_reply(event, text_bank())
            return

        if text == "กต":
            safe_reply(event, TextSendMessage(rules_text())); return

        # ====== คำสั่ง "สกอ" ดูรายการทั้งหมด ======
        if text == "สกอ":
            peh_key = _peh_source_key(event)
            if not PEH_LIST.get(peh_key):
                safe_reply(event, TextSendMessage("📋 ยังไม่มีรายการในห้องนี้"))
                return
            msgs = peh_flex_messages(event)
            if msgs:
                safe_reply(event, msgs[0] if len(msgs) == 1 else msgs[:5])
            return

        # ====== PEH / "เปะ" (เฉพาะแอดมิน) ======
        if is_admin(uid) and "จึก" in text:
            peh_lines = text.split("\n")
            added = False
            for peh_line in peh_lines:
                m_peh = re.match(r"^จึก\s+(.+)$", peh_line.strip())
                if m_peh:
                    item_text = m_peh.group(1).strip()
                    _add_peh_item(event, item_text)
                    added = True
            if added:
                msgs = peh_flex_messages(event)
                safe_reply(event, msgs[0] if len(msgs) == 1 else msgs[:5])
                return

        # ====== ลบรายการ PEH ตามหมายเลข (เฉพาะแอดมิน) ======
        # รูปแบบ: ลบ 3  หรือ  ลบรายการ 3
        m_peh_del = re.match(r"^ลบ(?:รายการ)?\s+(\d+)$", text.strip())
        if m_peh_del and is_admin(uid):
            peh_key = _peh_source_key(event)
            items = PEH_LIST.get(peh_key, [])
            del_no = int(m_peh_del.group(1))
            if not items:
                safe_reply(event, TextSendMessage("ยังไม่มีรายการเปะในห้องนี้"))
                return
            if del_no < 1 or del_no > len(items):
                safe_reply(event, TextSendMessage(
                    f"❌ หมายเลขไม่ถูกต้อง (มีทั้งหมด {len(items)} รายการ)"
                ))
                return
            removed = items.pop(del_no - 1)
            PEH_LIST[peh_key] = items
            safe_reply(event, TextSendMessage(
                f"✅ ลบรายการที่ {del_no} แล้ว\n🗑 {removed}"
            ))
            return

        # ====== ล้างรายการ PEH (เฉพาะแอดมิน) ======
        if text == "ล้างรายการ" and is_admin(uid):
            peh_key = _peh_source_key(event)
            PEH_LIST[peh_key] = []
            safe_reply(event, TextSendMessage("ล้างรายการเรียบร้อย"))
            return

        # ==== ประกาศราคาแบบ "ส่งข้อความอย่างเดียว" (ไม่เปิดรอบ) ====
        # ==== ประกาศราคาแบบ "ส่งข้อความอย่างเดียว" (ไม่เปิดรอบ) ====
        m_announce = R_ANN.match(text)

        if m_announce and not re.match(r"^\s*o\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งประกาศราคานี้ใช้ได้เฉพาะแอดมิน"))
                return

            camp   = m_announce.group(1).strip()
            hi_min = int(m_announce.group(2)); hi_max = int(m_announce.group(3))
            lo_min = int(m_announce.group(4)); lo_max = int(m_announce.group(5))

            safe_reply(event, flex_open_with_prices(
                st["pairNo"], camp, hi_min, hi_max, lo_min, lo_max
            )); return

        # ==== เปิดรอบ (O) ====
        if re.match(r"^\s*o\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            if st["phase"] != "NONE":
                phase_th = "เปิดอยู่" if st["phase"] == "OPEN" else "พักรอบอยู่"
                safe_reply(
                    event,
                    TextSendMessage(
                        f"❌ เปิดรอบใหม่ไม่ได้: ยังมีรอบค้างอยู่ ({phase_th})\n"
                        f"ขั้นตอนที่ถูกต้อง: กด E เพื่อพัก → พิมพ์ s<รหัสผล> → /y เพื่อยืนยันผล\n"
                        f"เมื่อสรุปรอบเสร็จแล้ว จึงค่อยเปิดรอบใหม่ได้"
                    )
                ); return

            m = R_O_ANN.match(text)
            if m:
                camp = m.group(1).strip()
                hi_min, hi_max = int(m.group(2)), int(m.group(3))
                lo_min, lo_max = int(m.group(4)), int(m.group(5))

                st["pairNo"] += 1
                st["totals"] = {"HI": 0, "LO": 0}
                st["bet_index"] = {}
                st["pendingCode"] = None
                st["escrow"] = {}
                st["settling"] = False
                st["phase"] = "OPEN"
                st["price"] = {"camp": camp, "HI": (hi_min, hi_max), "LO": (lo_min, lo_max)}

                safe_reply(event, flex_open_with_prices(
                    st["pairNo"], camp, hi_min, hi_max, lo_min, lo_max
                )); return
            else:
                note = (re.match(r"^\s*o\b\s*(.*)$", text, re.IGNORECASE).group(1) or "").strip()

                st["pairNo"] += 1
                st["totals"] = {"HI": 0, "LO": 0}
                st["bet_index"] = {}
                st["pendingCode"] = None
                st["escrow"] = {}
                st["settling"] = False
                st["phase"] = "OPEN"
                st["note"] = note or st.get("note")

                safe_reply(event, flex_open(st["pairNo"], st.get("note"))); return

        t = text.upper()
        if t == "E":
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน"))
                return
            if st["phase"] != "OPEN":
                safe_reply(event, TextSendMessage("ไม่มีรอบที่เปิดอยู่"))
                return

            claimed, old_action = claim_round_action("close", key, st["pairNo"], uid)
            if not claimed:
                st["phase"] = "PAUSED"
                st["last_closed_pairNo"] = st["pairNo"]
                safe_reply(event, TextSendMessage(
                    f"⚠️ รอบ {st['pairNo']} ปิดรับบิลไปแล้ว ไม่ต้องปิดซ้ำ"
                ))
                return

            st["phase"] = "PAUSED"
            st["last_closed_pairNo"] = st["pairNo"]
            camp = current_camp(st)

            # ส่ง 2 ข้อความ: (1) การ์ดพักรอบ (2) สรุปบิล
            try:
                safe_reply(event, [
                    flex_pause_notice(st["pairNo"], camp),
                    flex_summary(st, event)
                ])
            except Exception as e:
                # กันตก ถ้ามีปัญหา Flex จะยังตอบเป็นข้อความได้
                safe_reply(event, TextSendMessage(f"พักรอบชั่วคราว #{st['pairNo']} — ค่าย {camp}"))
            return

        
        if t in ("R", "RESUME"):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); 
                return
            if st["phase"] != "PAUSED":
                safe_reply(event, TextSendMessage("ไม่มีรอบที่พักอยู่")); return
            release_round_action("close", key, st["pairNo"])
            st["phase"] = "OPEN"
            camp = current_camp(st)
            safe_reply(event, flex_resume(st["pairNo"], camp)); return




        

        
            # ==== ปิดรอบ (ข้อความไทย: ปิดรอบ / หยุดแทง / ปิด) ====
        if R_CLOSE_TH.match(text.strip()):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            # สำคัญ: ปิดได้เฉพาะตอน OPEN เท่านั้น
            # ถ้า PAUSED อยู่แล้ว ห้ามส่งการ์ดปิด/สรุปซ้ำ
            if st["phase"] != "OPEN":
                if st["phase"] == "PAUSED":
                    safe_reply(event, TextSendMessage(
                        f"⚠️ รอบ {st['pairNo']} ปิดรับบิลไปแล้ว ไม่ต้องปิดซ้ำ\n"
                        f"ขั้นตอนถัดไป: พิมพ์ s<รหัสผล> แล้วกดยืนยัน /y"
                    )); return
                if st["phase"] == "SETTLING" or st.get("settling"):
                    safe_reply(event, TextSendMessage("⏳ ระบบกำลังสรุปผลอยู่ กรุณารอสักครู่")); return

                safe_reply(event, TextSendMessage("ไม่มีรอบที่เปิดอยู่")); return

            claimed, old_action = claim_round_action("close", key, st["pairNo"], uid)
            if not claimed:
                st["phase"] = "PAUSED"
                st["last_closed_pairNo"] = st["pairNo"]
                safe_reply(event, TextSendMessage(
                    f"⚠️ รอบ {st['pairNo']} ปิดรับบิลไปแล้ว ไม่ต้องปิดซ้ำ\n"
                    f"ขั้นตอนถัดไป: พิมพ์ s<รหัสผล> แล้วกดยืนยัน /y"
                )); return

            # เปลี่ยนสถานะเป็นพักรอบทันที ก่อนส่งข้อความ เพื่อกันแอดมินอีกคนกดซ้อน
            st["phase"] = "PAUSED"
            st["last_closed_pairNo"] = st["pairNo"]

            # ส่งการ์ดแจ้งหยุดแทง + สรุปบิลรอบนี้
            safe_reply(event, [
                flex_close_notice(st["pairNo"]),
                flex_summary(st, event)
            ]); return


        # ==== ตั้งผล s... ====
        sm = re.match(r"^[sS]\s*(.+)$", text)
        if sm:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            if st["phase"] != "PAUSED":
                safe_reply(event, TextSendMessage("❌ ต้องกด E (พักรอบ) ก่อนจึงจะตั้งผลได้")); return
            st["pendingCode"] = normalize_result_code(sm.group(1))
            safe_reply(event, flex_result_preview(st["pendingCode"], st["pairNo"])); return

        # ==== ยืนยันผล: T/ หรือ /y ====
        if R_YCONFIRM.match(text.strip()):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            # กันแอดมินกด /y ซ้อน หรือ LINE retry ระหว่างกำลังคำนวณเครดิต
            if st.get("settling") or st["phase"] == "SETTLING":
                safe_reply(event, TextSendMessage("⏳ ระบบกำลังสรุปผลอยู่ คำสั่งยืนยันซ้ำถูกยกเลิก")); return

            if st["phase"] != "PAUSED":
                if st.get("last_settled_pairNo") == st.get("pairNo"):
                    safe_reply(event, TextSendMessage(f"⚠️ รอบ {st['pairNo']} สรุปผลไปแล้ว ไม่สามารถยืนยันซ้ำได้")); return
                safe_reply(event, TextSendMessage("❌ ต้องกด E (พักรอบ) ก่อนจึงจะสามารถสรุปผลได้")); return

            if not st.get("pendingCode"):
                safe_reply(event, TextSendMessage(
                    f"❌ ยังไม่ได้ตั้งผลรอบ {st['pairNo']}\n"
                    f"กรุณาพิมพ์ s<รหัสผล> ก่อน แล้วค่อยกดยืนยัน /y"
                )); return

            code = normalize_result_code(st["pendingCode"])
            if code not in RESULT_DEFS:
                safe_reply(event, TextSendMessage("❌ ไม่สามารถยืนยันผลได้: โค้ดผลไม่ถูกต้อง")); return

            claimed, old_action = claim_round_action("settle", key, st["pairNo"], uid)
            if not claimed:
                st["phase"] = "NONE"
                st["settling"] = False
                safe_reply(event, TextSendMessage(
                    f"⚠️ รอบ {st['pairNo']} กำลังถูกสรุปผล หรือสรุปผลไปแล้ว คำสั่งยืนยันซ้ำถูกยกเลิก"
                )); return

            # ล็อกสถานะทันที ก่อนเริ่ม backup/คำนวณ/คืนเครดิต
            st["phase"] = "SETTLING"
            st["settling"] = True


            # ================= [เริ่มส่วนที่เพิ่ม] =================
            # 1. บันทึกประวัติลง State
            current_camp_name = current_camp(st)
            if "score_history" not in st: 
                st["score_history"] = []
                
            st["score_history"].append({
                "round": st["pairNo"],
                "camp": current_camp_name,
                "code": code
            })

            # === [เพิ่มใหม่] บันทึก snapshot เครดิต + สถานะห้อง ก่อนสรุปผล ===
            try:
                backup_path = os.path.join(DATA_DIR, f"backup_round_{st['pairNo']}.json")
                with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock()
                    snapshot = {
                        "round": st["pairNo"],
                        "users": users,
                        "room_state": st.copy(),   # ✅ st อยู่ใน with_rooms_lock() อยู่แล้ว
                        "metrics": METRICS.copy(), 
                    }
                    _atomic_write_json(backup_path, snapshot)

                # ตั้งเวลาลบ backup_round ไฟล์นี้เมื่อครบ 1 วัน โดยไม่ต้องเช็คทุกชั่วโมง
                schedule_backup_round_delete(backup_path)

                app.logger.info(f"[Backup] บันทึกเครดิตก่อนสรุปผล รอบ {st['pairNo']} สำเร็จ")
            except Exception as e:
                app.logger.warning(f"[Backup] ไม่สามารถบันทึก snapshot รอบ {st['pairNo']}: {e}")
            # === [จบส่วนเพิ่มใหม่] ===


            # คำนวณยอด และคืนเครดิตให้ผู้เล่น
            sum_stake = sum(b["amount"] for b in st["bet_index"].values())
            rows, footer = settle_by_code(st, code)

            with with_users_lock():
                for r in rows:
                    u = users.get(r["uid"])
                    if u:
                        u["credit"] = max(u.get("credit", 0) + r["payout"], 0)
                save_users_persist()

            # ล้าง state ห้อง หลังสรุปผลสำเร็จ
            st["last_settled_pairNo"] = st["pairNo"]
            st["settling"] = False
            st["phase"] = "NONE"
            st["pendingCode"] = None
            st["bet_index"].clear()
            st["totals"] = {"HI": 0, "LO": 0}
            st["escrow"].clear()

            # ถ้ารอบนี้เคยถูกย้อนแล้ว และตอนนี้ออกผลใหม่สำเร็จแล้ว
            # ให้ปลดล็อก rollback/pending snapshot เพื่อให้ย้อนผลรอบนี้ได้อีกครั้งเฉพาะหลังออกผลใหม่เท่านั้น
            release_round_action("rollback", key, st["pairNo"])
            clear_pending_rollback_snapshot(key)

            sum_payout = sum(r["payout"] for r in rows)
            profit = sum_stake - sum_payout
            if profit >= 0:
                METRICS["profit_sum"] += profit
            else:
                METRICS["loss_sum"] += (-profit)

            accum_now = {"profit_sum": METRICS["profit_sum"], "loss_sum": METRICS["loss_sum"], "net": net_profit()}
            balance_map = {r["uid"]: users.get(r["uid"], {}).get("credit", 0) for r in rows}
            # 1. ดึงชื่อค่ายมารอไว้
            current_camp_name = current_camp(st)

            # [FREE] เก็บสรุปล่าสุดไว้ให้หลังบ้านเรียกดูได้ (ไม่ต้อง push = ประหยัดโควต้า)
            try:
                rows_payload = []
                for r in rows:
                    rr = dict(r)
                    rr["name"] = users.get(r.get("uid"), {}).get("name")
                    rows_payload.append(rr)

                save_last_settle({
                    "round": st["pairNo"],
                    "camp_name": current_camp_name,
                    "code": code,
                    "profit": profit,
                    "accum": accum_now,
                    "rows": rows_payload,
                    "footer": footer,
                    "ts": _now(),
                    "ts_iso": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                })
            except Exception:
                app.logger.exception("build/save last_settle failed")

            # 2. ส่งให้ห้องลูกค้า (แสดงชื่อค่ายด้วย)
            safe_reply(event, [
                flex_settle(st["pairNo"], rows, footer,
                            show_profit=False,
                            balance_map=balance_map,
                            camp_name=current_camp_name),
                flex_scoreboard(st["score_history"])
            ]);

            # 3) หลังบ้านแบบฟรี (แนะนำ): ให้พิมพ์ "กำไรล่าสุด" ในกลุ่มหลังบ้านเพื่อดึงผลล่าสุด
            #    * ถ้าจำเป็นต้องส่งอัตโนมัติจริง ๆ ให้ตั้ง env: BACKOFFICE_PUSH_ENABLED=1
            if os.getenv("BACKOFFICE_PUSH_ENABLED", "0") == "1":
                p = load_last_settle()
                if p:
                    msg = TextSendMessage(settle_payload_to_text(p))
                    # ส่งแค่ 1 กลุ่มแรก เพื่อลดโควต้า (ปรับได้ถ้าต้องการ)
                    bo_targets = list(BACKOFFICE_GROUP_IDS)[:1]
                    for gid_to in bo_targets:
                        safe_push(gid_to, msg, label="backoffice_text")

            return
        # ==== ยกเลิกย้อนผล (Cancel Rollback) ====
        m_cancel_rollback = re.match(r"^(?:ยกเลิกย้อน|cancel\s+rollback|cancelrollback)\s*(\d+)$", text.strip(), re.IGNORECASE)
        if m_cancel_rollback:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            round_no = int(m_cancel_rollback.group(1))
            active_rb = get_active_round_action("rollback", key)
            if not active_rb:
                safe_reply(event, TextSendMessage(
                    f"ℹ️ ตอนนี้ไม่มีรายการย้อนผลค้างอยู่ จึงไม่ต้องยกเลิกย้อน {round_no}"
                )); return

            active_round = int(active_rb.get("pair_no") or 0)
            if active_round != round_no:
                safe_reply(event, TextSendMessage(
                    f"⚠️ ตอนนี้รายการย้อนผลที่ค้างอยู่คือรอบ {active_round}\n"
                    f"ถ้าจะยกเลิก ให้พิมพ์: ยกเลิกย้อน {active_round}\n"
                    f"ยังไม่สามารถยกเลิกย้อน {round_no} ได้"
                )); return

            snap = load_pending_rollback_snapshot(key)
            if not snap or int(snap.get("round_no") or 0) != round_no:
                safe_reply(event, TextSendMessage(
                    f"❌ ไม่พบสถานะก่อนย้อนของรอบ {round_no}\n"
                    f"เพื่อป้องกันเครดิตเพี้ยน กรุณาตั้งผลรอบ {round_no} ใหม่ด้วย s<รหัสผล> แล้วกดยืนยัน /y ให้เสร็จก่อน"
                )); return

            try:
                # คืนสถานะกลับไปก่อนคำสั่งย้อนผล เหมือนยกเลิกการย้อนจริง ๆ
                with with_users_lock():
                    users.clear()
                    users.update(snap.get("users") or {})
                save_users_persist()

                st.clear()
                st.update(snap.get("room_state") or start_state())

                if "metrics" in snap:
                    METRICS.clear()
                    METRICS.update(snap["metrics"])

                if snap.get("last_settle") is not None:
                    save_last_settle(snap.get("last_settle"))

                release_round_action("rollback", key, round_no)
                # กลับสถานะเป็นออกผลแล้ว จึงต้องล็อก settle รอบนี้ไว้เหมือนเดิม
                if not has_round_action("settle", key, round_no):
                    claim_round_action("settle", key, round_no, uid)
                clear_pending_rollback_snapshot(key)

                safe_reply(event, TextSendMessage(
                    f"✅ ยกเลิกย้อนผลรอบ {round_no} สำเร็จแล้ว\n"
                    f"ระบบคืนสถานะกลับไปก่อนย้อนผลเรียบร้อย\n"
                    f"ตอนนี้สามารถย้อนผลรอบอื่นได้แล้ว"
                )); return
            except Exception:
                app.logger.exception("cancel rollback failed")
                safe_reply(event, TextSendMessage(
                    f"❌ ยกเลิกย้อนผลรอบ {round_no} ไม่สำเร็จ\n"
                    f"เพื่อความปลอดภัย กรุณาตั้งผลรอบ {round_no} ใหม่ด้วย s<รหัสผล> แล้ว /y ให้จบก่อน"
                )); return

        # ==== ย้อนผล (Rollback) ====
        m_rollback = re.match(r"^(?:ย้อนผล|rollback)\s*(\d+)$", text.strip(), re.IGNORECASE)
        if m_rollback:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            round_no = int(m_rollback.group(1))

            # ห้ามย้อนตอนระบบกำลังสรุปผล เพื่อกันเครดิต/ไฟล์ snapshot ชนกัน
            if st.get("settling") or st.get("phase") == "SETTLING":
                safe_reply(event, TextSendMessage(
                    f"⏳ ระบบกำลังสรุปผลรอบ {st.get('pairNo')} อยู่ ห้ามย้อนผลระหว่างนี้"
                )); return

            # ล็อก global ต่อห้อง: ถ้าย้อนรอบใดค้างอยู่ ห้ามย้อนรอบอื่นจนกว่าจะออกผลใหม่หรือยกเลิกย้อน
            active_rb = get_active_round_action("rollback", key)
            if active_rb:
                active_round = int(active_rb.get("pair_no") or 0)
                if active_round == round_no:
                    safe_reply(event, TextSendMessage(
                        f"⚠️ รอบ {round_no} ถูกย้อนผลไปแล้ว\n"
                        f"ต้องตั้งผลรอบ {round_no} ใหม่ด้วย s<รหัสผล> แล้วกดยืนยัน /y ให้เสร็จก่อน\n"
                        f"หรือพิมพ์: ยกเลิกย้อน {round_no}\n"
                        f"ห้ามพิมพ์ย้อนผลซ้ำ"
                    )); return
                else:
                    safe_reply(event, TextSendMessage(
                        f"⚠️ ตอนนี้มีรายการย้อนผลรอบ {active_round} ค้างอยู่\n"
                        f"ต้องจัดการรอบ {active_round} ให้เสร็จก่อน จึงจะย้อนผลรอบ {round_no} ได้\n"
                        f"ทางเลือก 1: ตั้งผลรอบ {active_round} ใหม่ด้วย s<รหัสผล> แล้วกดยืนยัน /y\n"
                        f"ทางเลือก 2: พิมพ์ ยกเลิกย้อน {active_round} แล้วค่อยย้อนผลรอบ {round_no}"
                    )); return

            # ถ้ายังไม่เคยสรุปผลรอบนี้จริง ห้ามย้อน เพราะไม่มีผลให้ย้อน
            if not has_round_action("settle", key, round_no):
                safe_reply(event, TextSendMessage(
                    f"❌ รอบ {round_no} ยังไม่ได้ออกผล หรือยังไม่มีรายการสรุปผลที่ยืนยันแล้ว\n"
                    f"ย้อนผลได้เฉพาะรอบที่ออกผลแล้วเท่านั้น"
                )); return

            backup_file = os.path.join(DATA_DIR, f"backup_round_{round_no}.json")
            if not os.path.exists(backup_file):
                safe_reply(event, TextSendMessage(
                    f"❌ ไม่พบข้อมูลสำรองของรอบ {round_no}\n"
                    f"ไม่สามารถย้อนผลได้ เพื่อป้องกันเครดิตเพี้ยน"
                )); return

            # เก็บ snapshot ปัจจุบันไว้ก่อน rollback เพื่อให้คำสั่ง 'ยกเลิกย้อน <รอบ>' คืนกลับได้
            try:
                save_pending_rollback_snapshot(key, round_no, uid, st)
            except Exception:
                safe_reply(event, TextSendMessage(
                    f"❌ เตรียมข้อมูลยกเลิกย้อนรอบ {round_no} ไม่สำเร็จ\n"
                    f"ระบบยังไม่ย้อนผล เพื่อป้องกันเครดิตเพี้ยน"
                )); return

            claimed, old_action = claim_round_action("rollback", key, round_no, uid)
            if not claimed:
                clear_pending_rollback_snapshot(key)
                safe_reply(event, TextSendMessage(
                    f"⚠️ รอบ {round_no} ถูกย้อนผลไปแล้ว หรือกำลังถูกย้อนผลอยู่\n"
                    f"ต้องออกผลรอบ {round_no} ใหม่ให้เสร็จก่อน ห้ามย้อนซ้ำ"
                )); return

            try:
                with open(backup_file, "rb") as f:
                    data = _loads_bytes(f.read())

                # ✅ คืนเครดิตทั้งหมด
                with with_users_lock():
                    users.clear()
                    users.update(data["users"])
                save_users_persist()

                # ✅ คืนสถานะห้อง (บิล, ยอดรวม ฯลฯ)
                st.update(data.get("room_state", {}))
                st["phase"] = "PAUSED"
                st["settling"] = False
                st["pendingCode"] = None  # บังคับให้แอดมินตั้งผลใหม่ ไม่ใช้ผลเก่าโดยไม่ตั้งใจ

                # ✅ คืนค่ากำไรสะสม (METRICS)
                if "metrics" in data:
                    METRICS.clear()
                    METRICS.update(data["metrics"])

                # ปลดล็อก settle เดิม เพราะรอบนี้ถูกย้อนกลับมาแล้ว ต้องอนุญาตให้ออกผลใหม่ได้
                release_round_action("settle", key, round_no)

                safe_reply(event, TextSendMessage(
                    f"✅ ย้อนเครดิตและข้อมูลรอบ {round_no} สำเร็จแล้ว\n"
                    f"ขั้นตอนต่อไป: พิมพ์ s<รหัสผล> แล้วกดยืนยัน /y\n"
                    f"ถ้าไม่ต้องการย้อนแล้ว ให้พิมพ์: ยกเลิกย้อน {round_no}\n"
                    f"ระหว่างนี้ห้ามย้อนรอบอื่นจนกว่าจะจัดการรอบ {round_no} ให้เสร็จ"
                )); return
            except Exception:
                # ถ้าย้อนล้มเหลว ให้ปลดล็อก rollback เพื่อให้แก้ไข/ลองใหม่ได้ ไม่ให้ค้างถาวร
                release_round_action("rollback", key, round_no)
                clear_pending_rollback_snapshot(key)
                app.logger.exception("rollback failed")
                safe_reply(event, TextSendMessage(
                    f"❌ ย้อนผลรอบ {round_no} ไม่สำเร็จ ระบบยกเลิกคำสั่งนี้แล้ว"
                )); return



        if text.strip().lower() == "call":
            if not gid or not is_backoffice_group_id(gid):
                return

            with with_users_lock():
                table = [u for u in users.values() if int(u.get("credit", 0) or 0) > 0]

            if not table:
                safe_reply(event, TextSendMessage("ยังไม่มีลูกค้าที่มีเครดิต"))
                return

            total_credit = sum(int(u.get("credit", 0) or 0) for u in table)
            total_count = len(table)
            table = sorted(table, key=lambda x: (-int(x.get("credit", 0) or 0), int(x.get("cid", 0) or 0)))
            table = table[:100]

            try:
                safe_reply(event, flex_member_list(table, total_credit, total_count))
            except Exception:
                app.logger.exception("flex_member_list failed")
                safe_reply(event, TextSendMessage(format_user_table(table)))
            return


        # ==== ยกเลิกบิล ====
        m_cancel_by_cid = re.match(r"^x\s+(\d+)$", text.strip(), re.IGNORECASE)
        # เช็คว่าเป็นคำสั่งยกเลิกหรือไม่
        if text.strip().lower() in ("xx", "x*") or m_cancel_by_cid or text.strip().upper() == "X":
            if st["phase"] == "NONE":
                safe_reply(event, TextSendMessage("ยกเลิกไม่ได้: รอบนี้สรุปจบแล้ว")); return

            # แอดมินยกเลิกทั้งหมด
            if text.strip().lower() in ("xx", "x*"):
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
                n = len(st["bet_index"])
                # คืน escrow ทุกคน
                with with_users_lock():
                    for tuid, esc_amt in list(st["escrow"].items()):
                        if esc_amt > 0 and tuid in users:
                            users[tuid]["credit"] = users[tuid].get("credit", 0) + esc_amt
                    st["escrow"].clear()
                    st["bet_index"].clear()
                    st["totals"] = {"HI": 0, "LO": 0}
                    save_users_persist()
                extra = " (กำลังพักรอบ)" if st["phase"] == "PAUSED" else ""
                safe_reply(event, TextSendMessage(f"ยกเลิกบิลทั้งหมดสำเร็จ{extra} ({n} บิล)")); return

            # แอดมินยกเลิกตาม ID ลูกค้า
            if m_cancel_by_cid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
                cid = int(m_cancel_by_cid.group(1))
                with with_users_lock():
                    target = get_user_by_cid(cid)
                    if not target:
                        safe_reply(event, TextSendMessage(f"ไม่พบ ID {cid}")); return
                    tuid = target["uid"]
                    bet = st["bet_index"].pop(tuid, None)
                    if not bet:
                        safe_reply(event, TextSendMessage(f"ID {cid} ไม่มีบิลในรอบนี้")); return

                    st["totals"][bet["side"]] -= bet["amount"]
                    esc = st["escrow"].get(tuid, 0)
                    refund = min(esc, bet["amount"])
                    if refund > 0:
                        users[tuid]["credit"] = users[tuid].get("credit", 0) + refund
                        st["escrow"][tuid] = esc - refund
                        if st["escrow"][tuid] <= 0:
                            st["escrow"].pop(tuid, None)
                    save_users_persist()
                extra = " (กำลังพักรอบ)" if st["phase"] == "PAUSED" else ""
                safe_reply(event, TextSendMessage(f"ยกเลิกบิลของ ID {cid} สำเร็จ{extra} ({'สูง' if bet['side']=='HI' else 'ต่ำ'} {fmt(bet['amount'])})")); return

            # ลูกค้ายกเลิกบิลตัวเอง
            if text.strip().upper() == "X":
                if st["phase"] == "PAUSED":
                    safe_reply(event, TextSendMessage("กำลังพักรอบ: ลูกค้าไม่สามารถยกเลิกได้ โปรดให้แอดมินดำเนินการ")); return
                bet = st["bet_index"].pop(uid, None)
                if not bet:
                    safe_reply(event, TextSendMessage("คุณยังไม่มีการเดิมพันในรอบนี้")); return

                with with_users_lock():
                    st["totals"][bet["side"]] -= bet["amount"]
                    esc = st["escrow"].get(uid, 0)
                    refund = min(esc, bet["amount"])
                    if refund > 0:
                        users[uid]["credit"] = users[uid].get("credit", 0) + refund
                        st["escrow"][uid] = esc - refund
                        if st["escrow"][uid] <= 0:
                            st["escrow"].pop(uid, None)
                    save_users_persist()
                
                try:
                    profile = line_bot_api.get_profile(uid)
                    line_name = profile.display_name
                except Exception:
                    line_name = users.get(uid, {}).get("name", "ไม่ทราบชื่อ")
                safe_reply(event, TextSendMessage(f"คุณ {line_name} ❌ยกเลิกการเดิมพันเดิมสำเร็จ❌ ({'สูง' if bet['side']=='HI' else 'ต่ำ'} {fmt(bet['amount'])})")); return

        # ==== FAST PATH: ส่วนนี้ต้องอยู่นอก if ด้านบน ====
        bet = parse_bet(text)
        if bet:
            # แอดมินเล่นได้ (ปิดการเช็ค is_admin ไว้แล้ว)
            # if is_admin(uid):
            #     return
            
            with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock()
                if uid not in users:
                    safe_reply(event, TextSendMessage("กรุณาพิมพ์ add เพื่อรับไอดีก่อนวางบิล")); return

                ok, why = can_bet(st, uid, bet["side"], bet["amount"])
                if not ok:
                    safe_reply(event, TextSendMessage(f"❌รับบิลไม่ได้❌: {why}")); return

                u = users[uid]
                if u.get("credit", 0) < bet["amount"]:
                    safe_reply(event, TextSendMessage(f"ทุนคงเหลือไม่พอ (มี {fmt(u.get('credit',0))})")); return

                u["credit"] -= bet["amount"]
                st["escrow"][uid] = st["escrow"].get(uid, 0) + bet["amount"]
                save_users_persist()

                name = u["name"]
                prev = st["bet_index"].get(uid)
                total_amt = (prev["amount"] if prev else 0) + bet["amount"]
                st["bet_index"][uid] = {"uid": uid, "name": name, "side": bet["side"], "amount": total_amt}
                st["totals"][bet["side"]] += bet["amount"]

                side_th = "สูง" if bet["side"] == "HI" else "ต่ำ"
                safe_reply(event, TextSendMessage(
                    (f"คุณ {name} ✅ ลงเพิ่ม {side_th} +{fmt(bet['amount'])} • รวม {fmt(total_amt)} • ยอดเงินคงเหลือ {fmt(u['credit'])}"
                     if prev else
                     f"คุณ {name} ✅ เล่น {side_th} = {fmt(bet['amount'])} • ยอดเงินคงเหลือ {fmt(u['credit'])}")
                )); return


    # ----- ที่เหลือค่อยไปเช็คคำสั่งแอดมิน/ยูทิลต่างๆ เหมือนเดิม -----

# ====================================================================
# ====== AUTO TOPUP: ตรวจสลิปด้วย EasySlip API v2 แล้วเติมเครดิตอัตโนมัติ ======
# ====================================================================
# ตั้งค่าใน .env
#   EASYSLIP_ENABLED=1
#   EASYSLIP_API_KEY=xxxxxxxx                (จาก developer.easyslip.com)
#   EASYSLIP_MATCH_ACCOUNT=1                 (แนะนำ: ต้องผูกบัญชีรับเงินในหน้า EasySlip ก่อน)
#   SLIP_RECEIVER_NAMES=วรรณวิไล,WANWILAI    (สำรอง: ชื่อผู้รับที่ยอมรับ คั่นด้วย ,)
#   SLIP_MAX_AGE_MIN=120                     (สลิปเก่ากว่านี้ไม่รับ หน่วยนาที)
#   SLIP_MIN_AMOUNT=1  /  SLIP_MAX_AMOUNT=0  (0 = ไม่จำกัด)
#   SLIP_NOTIFY_BACKOFFICE=0                 (1 = push แจ้งกลุ่มหลังบ้าน ใช้โควต้า push)
import requests as _slip_requests

EASYSLIP_ENABLED = os.getenv("EASYSLIP_ENABLED", "0") == "1"
EASYSLIP_API_KEY = os.getenv("EASYSLIP_API_KEY", "").strip()
EASYSLIP_URL = os.getenv("EASYSLIP_URL", "https://api.easyslip.com/v2/verify/bank")
EASYSLIP_TIMEOUT = (10, 30)
EASYSLIP_MATCH_ACCOUNT = os.getenv("EASYSLIP_MATCH_ACCOUNT", "1") == "1"
SLIP_RECEIVER_NAMES = [s.strip().lower() for s in os.getenv("SLIP_RECEIVER_NAMES", "").split(",") if s.strip()]
SLIP_MAX_AGE_MIN = int(os.getenv("SLIP_MAX_AGE_MIN", "120"))
SLIP_MIN_AMOUNT = int(os.getenv("SLIP_MIN_AMOUNT", "1"))
SLIP_MAX_AMOUNT = int(os.getenv("SLIP_MAX_AMOUNT", "0"))
SLIP_NOTIFY_BACKOFFICE = os.getenv("SLIP_NOTIFY_BACKOFFICE", "0") == "1"

SLIPS_USED_JSON = os.path.join(DATA_DIR, "slips_used.json")
_slips_lock = threading.RLock()
_slips_used = {}  # transRef -> {uid, cid, amount, ts, ...}


def _load_slips_used():
    global _slips_used
    try:
        if os.path.exists(SLIPS_USED_JSON):
            with open(SLIPS_USED_JSON, "rb") as f:
                data = _loads_bytes(f.read())
            if isinstance(data, dict):
                _slips_used = data
    except Exception:
        app.logger.exception("load slips_used failed")


_load_slips_used()


def _norm_name(s: str) -> str:
    s = (s or "").lower()
    for p in ("นางสาว", "น.ส.", "นาย", "นาง", "mr.", "mrs.", "ms.", "miss"):
        s = s.replace(p, "")
    return re.sub(r"[\s.]+", "", s)


def easyslip_verify_image(image_bytes: bytes):
    """ส่งรูปไป EasySlip v2 → คืน (ok, data_or_None, error_code, error_message)"""
    form = {"checkDuplicate": "true"}
    if EASYSLIP_MATCH_ACCOUNT:
        form["matchAccount"] = "true"
    last_code, last_msg = "NETWORK_ERROR", "เชื่อมต่อ EasySlip ไม่ได้"
    for attempt in range(3):
        try:
            r = _slip_requests.post(
                EASYSLIP_URL,
                headers={"Authorization": f"Bearer {EASYSLIP_API_KEY}"},
                files={"image": ("slip.jpg", image_bytes, "image/jpeg")},
                data=form,
                timeout=EASYSLIP_TIMEOUT,
            )
            try:
                res = r.json()
            except Exception:
                res = {}
            if res.get("success"):
                return True, res.get("data") or {}, None, None
            err = res.get("error") or {}
            last_code = err.get("code") or f"HTTP_{r.status_code}"
            last_msg = err.get("message") or r.text[:200]
            # retry เฉพาะ error ชั่วคราว
            if last_code in ("API_SERVER_ERROR", "INTERNAL_SERVER_ERROR", "RATE_LIMIT_EXCEEDED") or r.status_code >= 500:
                wait = int(r.headers.get("Retry-After", "0") or 0) or (1 + attempt)
                time.sleep(min(wait, 5))
                continue
            return False, None, last_code, last_msg
        except (_slip_requests.exceptions.Timeout, _slip_requests.exceptions.ConnectionError) as e:
            last_msg = str(e)
            time.sleep(1 + attempt)
    return False, None, last_code, last_msg


_SLIP_ERR_TH = {
    "SLIP_NOT_FOUND": "❌ ไม่พบ QR ในสลิป หรือสลิปไม่ถูกต้อง\nกรุณาส่งรูปสลิปที่ชัดเจน (ไม่ครอป QR)",
    "SLIP_PENDING": "⏳ สลิปธนาคารกรุงเทพยังไม่เข้าระบบ\nรอ 5 นาทีแล้วส่งสลิปเดิมใหม่อีกครั้ง",
    "IMAGE_SIZE_TOO_LARGE": "❌ รูปใหญ่เกิน 4MB กรุณาส่งรูปใหม่",
    "INVALID_IMAGE_FORMAT": "❌ ไฟล์รูปไม่ถูกต้อง กรุณาส่งใหม่",
}


def _slip_check_receiver(data: dict):
    """ตรวจว่าโอนเข้าบัญชีร้านจริง → (ok, reason)"""
    if EASYSLIP_MATCH_ACCOUNT:
        if data.get("matchedAccount"):
            return True, ""
        return False, "บัญชีผู้รับไม่ตรงกับบัญชีของร้าน"
    if SLIP_RECEIVER_NAMES:
        acc = ((data.get("rawSlip") or {}).get("receiver") or {}).get("account") or {}
        nm = acc.get("name") or {}
        cand = _norm_name(f"{nm.get('th', '')}|{nm.get('en', '')}")
        for want in SLIP_RECEIVER_NAMES:
            if _norm_name(want) and _norm_name(want) in cand:
                return True, ""
        return False, "ชื่อผู้รับไม่ตรงกับบัญชีของร้าน"
    # ไม่ได้ตั้งค่าอะไรเลย → ไม่ยอมเติมอัตโนมัติ (กันโอนเข้าบัญชีอื่นแล้วเอาสลิปมาเติม)
    return False, "ระบบยังไม่ได้ตั้งค่าบัญชีรับเงิน (แจ้งแอดมิน)"


def _slip_check_age(raw: dict):
    if SLIP_MAX_AGE_MIN <= 0:
        return True, ""
    ds = (raw.get("date") or "").replace("Z", "+00:00")
    try:
        dt = datetime.fromisoformat(ds)
        age_min = (time.time() - dt.timestamp()) / 60
        if age_min > SLIP_MAX_AGE_MIN:
            return False, f"สลิปเก่าเกิน {SLIP_MAX_AGE_MIN} นาที"
        return True, ""
    except Exception:
        return False, "อ่านวันที่ในสลิปไม่ได้"


def process_slip_topup(event, uid: str):
    """ดาวน์โหลดรูปจาก LINE → ตรวจ EasySlip → เติมเครดิต (กันสลิปซ้ำ) → ตอบกลับ"""
    try:
        content = line_bot_api.get_message_content(event.message.id, timeout=LINE_API_TIMEOUT)
        image_bytes = content.content
    except Exception:
        app.logger.exception("slip: download image failed")
        safe_reply(event, TextSendMessage("❌ โหลดรูปสลิปไม่สำเร็จ กรุณาส่งใหม่อีกครั้ง"))
        return

    ok, data, code, msg = easyslip_verify_image(image_bytes)
    if not ok:
        app.logger.warning("slip: easyslip error uid=%s code=%s msg=%s", uid, code, msg)
        if code in _SLIP_ERR_TH:
            safe_reply(event, TextSendMessage(_SLIP_ERR_TH[code]))
        else:
            safe_reply(event, TextSendMessage("⚠️ ระบบตรวจสลิปขัดข้องชั่วคราว\nแอดมินจะตรวจสอบและเติมให้ครับ"))
        return

    raw = data.get("rawSlip") or {}
    trans_ref = (raw.get("transRef") or "").strip()
    try:
        amount = int(floor(float((raw.get("amount") or {}).get("amount") or data.get("amountInSlip") or 0)))
    except Exception:
        amount = 0
    sender_name = (((raw.get("sender") or {}).get("account") or {}).get("name") or {}).get("th") or "-"

    if not trans_ref or amount <= 0:
        safe_reply(event, TextSendMessage("❌ อ่านข้อมูลสลิปไม่ครบ กรุณาติดต่อแอดมิน"))
        return

    rc_ok, rc_why = _slip_check_receiver(data)
    if not rc_ok:
        safe_reply(event, TextSendMessage(f"❌ ไม่สามารถเติมอัตโนมัติ: {rc_why}"))
        return

    age_ok, age_why = _slip_check_age(raw)
    if not age_ok:
        safe_reply(event, TextSendMessage(f"❌ ไม่สามารถเติมอัตโนมัติ: {age_why}\nกรุณาติดต่อแอดมิน"))
        return

    if amount < SLIP_MIN_AMOUNT:
        safe_reply(event, TextSendMessage(f"❌ ยอดฝากขั้นต่ำ {fmt(SLIP_MIN_AMOUNT)} บาท"))
        return
    if SLIP_MAX_AMOUNT and amount > SLIP_MAX_AMOUNT:
        safe_reply(event, TextSendMessage(
            f"⚠️ ยอด {fmt(amount)} บาท เกินวงเงินเติมอัตโนมัติ\nแอดมินจะตรวจสอบและเติมให้ครับ"))
        return

    # ===== เช็คสลิปซ้ำ + เติมเครดิต (atomic) =====
    with _slips_lock:
        used = _slips_used.get(trans_ref)
        if used:
            safe_reply(event, TextSendMessage(
                f"❌ สลิปนี้ถูกใช้เติมไปแล้ว (ID {used.get('cid')} เวลา {used.get('time')})"))
            return
        if data.get("isDuplicate"):
            # EasySlip เคยเห็นสลิปนี้ แต่ระบบเรายังไม่เคยเติม → ให้แอดมินตรวจเอง ไม่เติมอัตโนมัติ
            safe_reply(event, TextSendMessage(
                "⚠️ สลิปนี้เคยถูกตรวจแล้ว ระบบไม่เติมอัตโนมัติ\nแอดมินจะตรวจสอบให้ครับ"))
            return

        with with_users_lock():
            u = users.get(uid)
            if not u:
                safe_reply(event, TextSendMessage("กรุณาพิมพ์ add เพื่อรับไอดีก่อน"))
                return
            # บันทึกสลิปลงไฟล์ก่อน (ถ้าเขียนไม่ได้ = ไม่เติม กันเติมซ้ำ)
            _slips_used[trans_ref] = {
                "uid": uid,
                "cid": u.get("cid"),
                "amount": amount,
                "sender": sender_name,
                "slip_date": raw.get("date"),
                "ts": time.time(),
                "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            }
            try:
                _atomic_write_json(SLIPS_USED_JSON, _slips_used)
            except Exception:
                _slips_used.pop(trans_ref, None)
                app.logger.exception("slip: save slips_used failed")
                safe_reply(event, TextSendMessage("⚠️ ระบบบันทึกสลิปไม่สำเร็จ แอดมินจะตรวจสอบให้ครับ"))
                return

            u["credit"] = int(u.get("credit", 0) or 0) + amount
            new_credit = u["credit"]
            cid, name = u.get("cid"), u.get("name")
        save_users_persist()

    app.logger.info("slip: topup ok uid=%s cid=%s amount=%s ref=%s", uid, cid, amount, trans_ref)
    safe_reply(event, TextSendMessage(
        f"✅ เติมเครดิตอัตโนมัติสำเร็จ\n"
        f"🎫 ID : {cid}  {name}\n"
        f"💰 ยอดฝาก {fmt(amount)} บาท\n"
        f"👤 ผู้โอน: {sender_name}\n"
        f"💳 คงเหลือ {fmt(new_credit)} บาท"
    ))

    if SLIP_NOTIFY_BACKOFFICE and BACKOFFICE_GROUP_IDS:
        safe_push(next(iter(BACKOFFICE_GROUP_IDS)), TextSendMessage(
            f"💵 ฝากอัตโนมัติ ID {cid} {name} +{fmt(amount)} (คงเหลือ {fmt(new_credit)})\n"
            f"ผู้โอน: {sender_name}\nRef: {trans_ref}"
        ), label="slip_topup")


def slip_lookup_text(trans_ref: str) -> str:
    with _slips_lock:
        r = _slips_used.get(trans_ref)
    if not r:
        return f"ไม่พบสลิป Ref {trans_ref} ในระบบ"
    return (f"🧾 Ref {trans_ref}\nID {r.get('cid')} • ยอด {fmt(r.get('amount', 0))}\n"
            f"ผู้โอน: {r.get('sender')}\nเติมเมื่อ: {r.get('time')}")


@handler.add(MessageEvent, message=ImageMessage)
def on_image(event: MessageEvent):
    uid = event.source.user_id
    gid = getattr(event.source, "group_id", None)
    key = room_key(event.source)

    # กัน LINE retry / webhook ซ้ำ: message id เดิมต้องไม่ถูกประมวลผลซ้ำ
    if already_processed_message(getattr(event.message, "id", None)):
        return

    # ต้องอยู่ในกลุ่ม/ห้องเท่านั้น
    if not in_group_or_room(event.source):
        return

    # ตรวจ allow/deny/lockdown ของกลุ่ม
    if gid:
        if gid in BANNED_GROUPS or gid in DENY_GROUP_IDS:
            return
        if not is_allowed_group(gid):
            return
        if _locked_group(gid) and not is_admin(uid):
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("ระบบ: กลุ่มกำลังล็อกดาวน์ชั่วคราว ติดต่อแอดมินเพื่อปลดล็อก"))
            return

    # ตรวจสถานะผู้ใช้ ban/mute
    if uid in BANNED_UIDS:
        return
    if _muted(uid):
        if not _notice_throttled(uid):
            safe_reply(event, TextSendMessage("ระบบ: คุณถูกจำกัดการส่งข้อความชั่วคราว (anti-spam)"))
        return

    # rate limit แบบเดียวกับข้อความตัวหนังสือ
    if not rl.allow(f"room:{key}", RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD):
        return
    if not rl.allow(f"uid:{uid}:burst", RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD) or \
       not rl.allow(f"uid:{uid}:day", RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD):
        STRIKES[uid] = STRIKES.get(uid, 0) + 1
        if STRIKES[uid] >= ABUSE_STRIKE_TO_MUTE:
            MUTED_UNTIL[uid] = _now() + MUTE_SECONDS_DEFAULT
            STRIKES[uid] = 0
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage(f"ระบบ: มิวท์ {MUTE_SECONDS_DEFAULT} วินาที เนื่องจากกิจกรรมถี่ผิดปกติ"))
        else:
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("ระบบ: กิจกรรมถี่เกินกำหนด ช่วยเว้นช่วงหน่อยนะ"))
        return

    # เตรียม state ห้อง
    with with_rooms_lock():
        if key not in rooms:
            rooms[key] = start_state()
        st = rooms[key]

    # ต้องมีข้อมูลผู้ใช้ก่อน (พิมพ์ add มาก่อน)
    with with_users_lock():
        u = users.get(uid)

    if not u:
        safe_reply(event, TextSendMessage("กรุณาพิมพ์ add เพื่อรับไอดีก่อน"))
        return

    # ===== AUTO TOPUP: ถ้าเปิด EasySlip ให้ตรวจสลิปแล้วเติมเครดิต (ทำใน background thread ไม่ให้ webhook ค้าง) =====
    if EASYSLIP_ENABLED and EASYSLIP_API_KEY:
        if gid and is_backoffice_group_id(gid):
            return  # ไม่ตรวจรูปในกลุ่มหลังบ้าน
        threading.Thread(target=process_slip_topup, args=(event, uid), daemon=True).start()
        return

    # ตอบการ์ด C ของผู้ที่ส่งรูป
    try:
        safe_reply(event, flex_customer_card(st, u))
    except Exception:
        # กันตก ถ้า Flex error ให้ตอบข้อความธรรมดา โดยไม่ให้พังซ้ำถ้า u หาย
        app.logger.exception("on_image flex_customer_card failed uid=%s", uid)
        cid = u.get('cid', '-') if isinstance(u, dict) else '-'
        name = u.get('name', 'ผู้เล่น') if isinstance(u, dict) else 'ผู้เล่น'
        credit = u.get('credit', 0) if isinstance(u, dict) else 0
        safe_reply(event, TextSendMessage(
            f"ID {cid} • {name} • เครดิต {fmt(credit)} บ."
        ))


def current_camp(st):
    return (st.get("price", {}) or {}).get("camp") or (st.get("note") or "ไม่ระบุค่าย")

def push_batch(to_id, messages, batch=5):
    for i in range(0, len(messages), batch):
        safe_push(to_id, messages[i:i+batch])



# ====== ANTI-KICK MONITOR ======
@handler.add(MemberLeftEvent)
def on_member_left(event: MemberLeftEvent):
    gid = getattr(event.source, "group_id", None)
    if not gid: return
    try:
        members = getattr(getattr(event, "left", None), "members", []) or []
    except Exception:
        members = []
    left_uids = []
    for m in members:
        uid = getattr(m, "user_id", None) or getattr(m, "mid", None) or getattr(m, "id", None)
        if uid: left_uids.append(uid)
    for lu in left_uids:
        if lu in PROTECTED_UIDS:
            _lockdown_and_alert(gid, lu)
            break
    


# ====== FREE BACKOFFICE VIEW (no LINE quota) ======
# เปิดดูสรุปล่าสุดผ่านเว็บ: /backoffice/latest?token=YOURTOKEN
# ตั้ง token ได้ด้วย env: BACKOFFICE_VIEW_TOKEN (ถ้าไม่ตั้ง จะเปิดได้เฉพาะในวงแลน/เครื่องตัวเองตามไฟร์วอลล์)
@app.route("/backoffice/latest", methods=["GET"])
def backoffice_latest():
    token = os.getenv("BACKOFFICE_VIEW_TOKEN", "").strip()
    if token:
        if request.args.get("token", "").strip() != token:
            return make_response("forbidden", 403)

    p = load_last_settle()
    if not p:
        return make_response(json.dumps({"ok": False, "message": "no last_settle yet"}, ensure_ascii=False),
                             404, {"Content-Type": "application/json; charset=utf-8"})

    return make_response(json.dumps({"ok": True, "data": p}, ensure_ascii=False),
                         200, {"Content-Type": "application/json; charset=utf-8"})

if __name__ == "__main__":
    port = int(os.getenv("PORT", 5000))
    print(f"Starting Waitress on 0.0.0.0:{port}")
    serve(
        app,
        host="0.0.0.0",
        port=port,
        threads=16,
        connection_limit=200,
        channel_timeout=60
    )
