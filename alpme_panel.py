"""
Alpme 注册控制台 · 三页面
============================================================
纯标准库。运行：
    python alpme_panel.py
浏览器打开  http://127.0.0.1:8080

三个页面（顶部导航）：
    /register  注册：注册数量/并发 -> 开始/停止；注册目标/成功/失败 + 详细执行日志
    /accounts  账号管理：所有成功账号（邮箱----姓名----密码），搜索/复制/下载
    /proxies   代理配置：注册相隔秒数 + 代理池（添加/校验/复检/清空/移除）

仅供学习与技术研究使用。
"""

import json
import os
import random
import re
import string
import time
import threading
import argparse
import urllib.request
import urllib.error
import urllib.parse
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

try:
    import socks
    HAVE_SOCKS = True
except ImportError:
    HAVE_SOCKS = False

DEFAULT_TARGET = "https://alpme.com/api/auth/signup"
SUCCESS_FILE = "注册成功记录.txt"
SESSION_FILE = "登录态记录.txt"
PLAN_FILE = "套餐状态.txt"
PROXIES_FILE = "proxies.txt"
SETTINGS_FILE = "settings.json"
PROXY_FAIL_THRESHOLD = 3
PROXY_RL_THRESHOLD = 2
HEADERS = {
    "Content-Type": "application/json",
    "Accept": "application/json",
    "Origin": "https://alpme.com",
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/120.0 Safari/537.36"),
}
FIRST_NAMES = ["James","Mary","John","Patricia","Robert","Jennifer","Michael","Linda",
               "William","Elizabeth","David","Barbara","Richard","Susan","Joseph","Jessica",
               "Thomas","Sarah","Charles","Karen","Chris","Alex","Taylor","Jordan",
               "Morgan","Casey","Riley","Jamie","Avery","Quinn"]
LAST_NAMES = ["Smith","Johnson","Williams","Brown","Jones","Garcia","Miller","Davis",
              "Rodriguez","Martinez","Hernandez","Lopez","Gonzalez","Wilson","Anderson",
              "Thomas","Taylor","Moore","Jackson","Martin","Lee","Perez","Thompson","White",
              "Harris","Clark","Lewis","Walker","Hall","Young"]

lock = threading.Lock()
settings = {"interval": 0.0, "concurrency": 10, "count": 200,
            "backoff_on": True, "backoff": 15.0, "backoff_max": 180.0,
            "promo_code": "ALP27", "auto_redeem": True}
plans = {}
job = {"running": False, "stop": threading.Event(), "target": DEFAULT_TARGET,
       "count": 200, "concurrency": 10, "interval": 0.0, "started_at": 0.0}
stats = {"success": 0, "exists": 0, "ratelimit": 0, "other": 0, "error": 0}
logs = deque(maxlen=2000)
accounts = []
proxies = []
seq = {"n": 0}
agg = {"dur_sum": 0, "dur_n": 0, "rl_streak": 0, "backoff_wait": 0.0,
       "no_proxy_warned": False}

SL_CN = {"success": "成功", "exists": "已存在", "ratelimit": "限流",
         "other": "其他", "error": "异常", "warn": "提示"}


class Rec:
    """记录一次注册尝试的每一步（步名 + 累计耗时 + 细节）"""

    def __init__(self):
        self.t0 = time.time()
        self.steps = []
        self.cookie = ""

    def step(self, name, detail=""):
        self.steps.append({"n": name, "ms": int((time.time() - self.t0) * 1000),
                           "d": detail})

    def ms(self):
        return int((time.time() - self.t0) * 1000)


HOST_RE = re.compile(r"^(?:\d{1,3}(?:\.\d{1,3}){3}|[A-Za-z0-9](?:[A-Za-z0-9.\-]*[A-Za-z0-9])?)$")
PROXY_HINT = "网关:端口@用户名:密码"


def _is_host(s):
    return bool(HOST_RE.match(s or ""))


def _is_port(s):
    return bool(s) and s.isdigit() and 0 < int(s) < 65536


def normalize_proxy(raw):
    """唯一格式：网关:端口@用户名:密码（无认证时只写 网关:端口）

    统一转成内部使用的 http://用户名:密码@网关:端口
    返回 (标准URL 或 None, 失败原因)
    """
    s = (raw or "").strip().strip('"').strip("'")
    if not s or s.startswith("#"):
        return None, "空行/注释"
    low = s.lower()
    if "socks" in low:
        return None, "当前只支持 HTTP 代理（" + PROXY_HINT + "）"
    for sch in ("http://", "https://"):
        if low.startswith(sch):
            s = s[len(sch):]
            break
    s = s.split("/")[0].split("?")[0].strip()

    if "@" not in s:
        cols = s.split(":")
        if len(cols) == 2 and _is_host(cols[0]) and _is_port(cols[1]):
            return f"http://{s}", ""
        return None, "格式应为 " + PROXY_HINT

    hostport, creds = s.split("@", 1)
    hp = hostport.rsplit(":", 1)
    if len(hp) != 2 or not _is_host(hp[0]) or not _is_port(hp[1]):
        return None, "@ 前面必须是 网关:端口（格式 " + PROXY_HINT + "）"
    if ":" not in creds:
        return None, "@ 后面必须是 用户名:密码"
    user, _, pwd = creds.partition(":")
    if not user or not pwd:
        return None, "用户名或密码为空"
    return f"http://{creds}@{hostport}", ""


def display_proxy(url):
    """把内部 URL 还原成页面展示用的 网关:端口@用户名:密码"""
    if "://" not in url:
        url = "http://" + url
    try:
        u = urllib.parse.urlparse(url)
        port = u.port or ""
        if u.username:
            return f"{u.hostname}:{port}@{u.username}:{u.password or ''}"
        return f"{u.hostname}:{port}"
    except Exception:
        return url


class Proxy:
    def __init__(self, url):
        self.url = url; self.active = True; self.validating = False
        self.fails = 0; self.ok = 0; self.last_err = ""
        self.used = 0; self.rl = 0; self.rl_streak = 0

    def mark_ok(self):
        self.ok += 1; self.fails = 0; self.rl_streak = 0; self.active = True

    def mark_fail(self, err=""):
        self.fails += 1; self.ok = 0; self.last_err = err
        if self.fails >= PROXY_FAIL_THRESHOLD:
            self.active = False

    def mark_ratelimit(self, msg=""):
        """该出口被限流：连续命中阈值即判定配额用尽，主动下线，不再浪费请求"""
        self.rl += 1; self.rl_streak += 1
        self.last_err = msg or "限流"
        if self.rl_streak >= PROXY_RL_THRESHOLD:
            self.active = False
            self.last_err = "配额用尽（限流）"

    def to_dict(self):
        return {"url": self.url, "disp": display_proxy(self.url),
                "active": self.active, "validating": self.validating,
                "ok": self.ok, "fails": self.fails, "last_err": self.last_err,
                "used": self.used, "rl": self.rl}


def rand_str(n, pool):
    return "".join(random.choices(pool, k=n))


def gen_email():
    if random.random() < 0.5:
        return rand_str(random.randint(6, 11), string.digits) + "@qq.com"
    return rand_str(random.randint(8, 14), string.ascii_lowercase + string.digits) + "@gmail.com"


def gen_name():
    return random.choice(FIRST_NAMES) + " " + random.choice(LAST_NAMES)


def gen_password():
    return rand_str(12, string.ascii_letters + string.digits)


def make_opener(proxy_url):
    if not proxy_url:
        return urllib.request.build_opener()
    return urllib.request.build_opener(
        urllib.request.ProxyHandler({"http": proxy_url, "https": proxy_url}))


def open_via_socks(url, proxy_url, data, timeout):
    import ssl, http.client
    p = urllib.parse.urlparse(proxy_url)
    u = urllib.parse.urlparse(url)
    dest_host = u.hostname
    dest_port = u.port or (443 if u.scheme == "https" else 80)
    s = socks.socksocket()
    s.set_proxy(socks.SOCKS5, p.hostname, p.port or 1080, rdns=True,
                username=p.username, password=p.password)
    s.settimeout(timeout)
    s.connect((dest_host, dest_port))
    if u.scheme == "https":
        s = ssl.create_default_context().wrap_socket(s, server_hostname=dest_host)
    h = http.client.HTTPConnection(dest_host, dest_port, timeout=timeout)
    h.sock = s
    path = (u.path or "/") + (("?" + u.query) if u.query else "")
    h.request("POST", path, body=data, headers=HEADERS)
    r = h.getresponse()
    return r.status, r.read(), r.getheaders()


def grab_cookie(headers):
    """从响应头取 Set-Cookie，拼成 cookie 串（优先 ai_sess）"""
    raw = []
    try:
        raw = headers.get_all("Set-Cookie") or []
    except AttributeError:
        try:
            raw = [v for k, v in headers if str(k).lower() == "set-cookie"]
        except Exception:
            raw = []
    items = []
    for c in raw:
        kv = str(c).split(";")[0].strip()
        if kv and "=" in kv:
            items.append(kv)
    items.sort(key=lambda x: 0 if x.startswith("ai_sess=") else 1)
    return "; ".join(items)


def classify(status, js):
    if isinstance(js, dict) and js.get("ok") and 200 <= (status or 0) < 400:
        return "success", ""
    msg = ""
    if isinstance(js, dict):
        msg = str(js.get("message") or js.get("error") or js.get("msg") or js)
    low = (msg + " " + str(status)).lower()
    if "rate" in low or "limit" in low or "too many" in low or status == 429:
        return "ratelimit", msg
    if "exist" in low or "taken" in low or "already" in low:
        return "exists", msg
    return "other", msg


def open_http(url, proxy_url, data, timeout):
    req = urllib.request.Request(url, data=data, method="POST", headers=HEADERS)
    try:
        r = make_opener(proxy_url).open(req, timeout=timeout)
        return r.status, r.read(), r.headers
    except urllib.error.HTTPError as e:
        return e.code, e.read(), e.headers


def short(raw, n=140):
    try:
        s = raw.decode("utf-8", errors="replace")
    except Exception:
        s = str(raw)
    s = " ".join(s.split())
    return s[:n]


def register(target, proxy_obj, fallback_note=""):
    """执行一次完整注册尝试，返回 (kind, msg, creds, status, rec)"""
    rec = Rec()
    email, name, pw = gen_email(), gen_name(), gen_password()
    rec.step("1/9 生成账号", f"{email} / {name} / 密码 {len(pw)} 位")

    body = json.dumps({"email": email, "password": pw, "name": name,
                       "ref": "", "promo": "", "captcha": ""}).encode("utf-8")
    rec.step("2/9 组装请求体", f"{len(body)} 字节 · 字段 email+password+name+ref+promo+captcha")

    purl = proxy_obj.url if proxy_obj else None
    if purl:
        rec.step("3/9 选择出口", display_proxy(purl))
    else:
        rec.step("3/9 选择出口", "本机 IP" + (f"（{fallback_note}）" if fallback_note else "（未配置代理）"))
    creds = (email, name, pw)

    status, raw, resp_headers = None, b"", None
    try:
        if purl and purl.startswith("socks"):
            if not HAVE_SOCKS:
                rec.step("4/9 连接失败", "socks5 需要 pip install pysocks")
                return "error", "socks5 需 pip install pysocks", creds, None, rec
            rec.step("4/9 建立连接", f"SOCKS5 拨号 {display_proxy(purl)}")
            status, raw, resp_headers = open_via_socks(target, purl, body, 20)
        else:
            rec.step("4/9 建立连接", (f"经 HTTP 代理 {display_proxy(purl)}" if purl else "直连 TLS 握手"))
            status, raw, resp_headers = open_http(target, purl, body, 20)
        rec.cookie = grab_cookie(resp_headers)
        rec.step("5/9 收到响应",
                 f"HTTP {status} · 响应体 {len(raw)} 字节"
                 + (" · 已下发登录态 Cookie" if rec.cookie else " · 无 Cookie"))
    except urllib.error.HTTPError as e:
        status, raw = e.code, e.read()
        rec.step("5/9 收到响应", f"HTTP {status} · 响应体 {len(raw)} 字节（错误响应）")
    except Exception as e:
        et = type(e).__name__
        detail = str(e)[:140] or et
        rec.step("4/9 连接失败", f"{et}: {detail}")
        return "error", f"{et}: {detail}", creds, None, rec

    js = {}
    try:
        js = json.loads(raw.decode("utf-8", errors="replace"))
        rec.step("6/9 解析响应", json.dumps(js, ensure_ascii=False)[:160])
    except Exception:
        rec.step("6/9 解析响应", "非 JSON：" + short(raw, 120))

    kind, msg = classify(status, js)
    rec.step("7/9 判定结果", SL_CN.get(kind, kind) + (f" · {msg[:130]}" if msg else ""))
    return kind, msg, creds, status, rec


def pick_proxy():
    """按使用次数最少优先轮换，让每个 IP 的注册配额都被均匀用满"""
    with lock:
        active = [p for p in proxies if p.active and not p.validating]
        if not active:
            return None
        fewest = min(p.used for p in active)
        cand = [p for p in active if p.used == fewest]
    p = random.choice(cand)
    with lock:
        p.used += 1
    return p


def worker(stop_ev):
    while not stop_ev.is_set():
        with lock:
            if job["count"] > 0 and sum(stats.values()) >= job["count"]:
                break
            target, interval = job["target"], job["interval"]
        wait = interval
        if settings.get("backoff_on") and agg["rl_streak"] > 0:
            base = float(settings.get("backoff", 15.0))
            cap = float(settings.get("backoff_max", 180.0))
            wait = max(wait, min(base * (2 ** (min(agg["rl_streak"], 5) - 1)), cap))
        if wait > 0:
            with lock:
                agg["backoff_wait"] = round(wait, 1)
            stop_ev.wait(wait)
            if stop_ev.is_set():
                break
            with lock:
                agg["backoff_wait"] = 0.0

        proxy_obj = pick_proxy()
        if proxy_obj is None and proxies:
            with lock:
                warn = not agg.get("no_proxy_warned")
                agg["no_proxy_warned"] = True
            if warn:
                r2 = Rec()
                r2.step("⚠ 出口已耗尽", f"{len(proxies)} 个代理全部不可用/配额用尽，已回退本机 IP")
                r2.step("⚠ 影响", "本机 IP 配额大概率已满，接下来的尝试多为限流；请补充代理")
                with lock:
                    seq["n"] += 1
                    logs.appendleft({"id": seq["n"], "ts": time.time(), "kind": "warn",
                                     "http": None, "email": "-", "name": "-", "password": "-",
                                     "reason": "无可用代理", "dur": 0, "proxy": "",
                                     "steps": r2.steps})
        kind, msg, creds, status, rec = register(
            target, proxy_obj, "代理全部不可用，已回退" if (proxies and not proxy_obj) else "")
        now = time.time()

        if kind == "success":
            with lock:
                accounts.append({"email": creds[0], "name": creds[1], "pw": creds[2],
                                 "ts": now, "sess": rec.cookie})
            try:
                with open(SUCCESS_FILE, "a", encoding="utf-8") as f:
                    f.write(f"{creds[0]}----{creds[1]}----{creds[2]}\n")
                rec.step("8/9 写入记录", f"已追加到 {SUCCESS_FILE}")
            except Exception as e:
                rec.step("8/9 写入记录", f"写入失败：{e}")
            if rec.cookie:
                try:
                    with open(SESSION_FILE, "a", encoding="utf-8") as f:
                        f.write(f"{creds[0]}----{rec.cookie}\n")
                    rec.step("8/9 保存登录态", f"Cookie 已存入 {SESSION_FILE}")
                except Exception as e:
                    rec.step("8/9 保存登录态", f"写入失败：{e}")
            else:
                rec.step("8/9 保存登录态", "本次响应未下发 Cookie")
            if settings.get("auto_redeem") and str(settings.get("promo_code") or "").strip() and rec.cookie:
                code_now = str(settings.get("promo_code")).strip().upper()
                rec.step("8/9 兑换套餐", f"用登录态提交兑换码 {code_now} → /dashboard/referrals")
                ok_r, msg_r, plan_r, label_r, _ = redeem_code(
                    creds[0], rec.cookie, code_now, proxy_obj.url if proxy_obj else None)
                if plan_r:
                    save_plan(creds[0], plan_r, label_r, ok_r)
                rec.step("8/9 兑换结果",
                         f"{'成功' if ok_r else '失败'} · {msg_r}"
                         + (f" · 当前套餐 {plan_r}" if plan_r else ""))
            if proxy_obj:
                proxy_obj.mark_ok()
        elif kind == "error":
            if proxy_obj:
                proxy_obj.mark_fail(msg)
                rec.step("8/9 代理状态", f"记录失败 {proxy_obj.fails}/{PROXY_FAIL_THRESHOLD}")
        elif kind == "ratelimit":
            if proxy_obj:
                proxy_obj.mark_ratelimit(msg)
                rec.step("8/9 代理状态", ("已下线（配额用尽，不再使用）" if not proxy_obj.active
                                        else f"限流 {proxy_obj.rl_streak}/{PROXY_RL_THRESHOLD}，再限流即下线"))
        else:
            if proxy_obj:
                proxy_obj.mark_ok()

        rec.step("9/9 完成", f"总耗时 {rec.ms()} ms")
        dur = rec.ms()
        with lock:
            seq["n"] += 1
            stats[kind] += 1
            agg["dur_sum"] += dur
            agg["dur_n"] += 1
            if kind == "ratelimit":
                agg["rl_streak"] += 1
            elif kind == "success":
                agg["rl_streak"] = 0
            logs.appendleft({"id": seq["n"], "ts": now, "kind": kind, "http": status,
                             "email": creds[0], "name": creds[1], "password": creds[2],
                             "reason": msg, "dur": dur,
                             "proxy": (display_proxy(proxy_obj.url) if proxy_obj else ""),
                             "steps": rec.steps})


def _run_job(stop_ev):
    threads = [threading.Thread(target=worker, args=(stop_ev,), daemon=True)
               for _ in range(job["concurrency"])]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    with lock:
        job["running"] = False


def start_job(count, concurrency):
    with lock:
        if job["running"]:
            return False, "任务进行中，请先停止"
        for k in stats:
            stats[k] = 0
        logs.clear()
        agg["dur_sum"] = 0; agg["dur_n"] = 0
        agg["rl_streak"] = 0; agg["backoff_wait"] = 0.0
        agg["no_proxy_warned"] = False
        seq["n"] = 0
        job["target"] = DEFAULT_TARGET
        job["count"] = int(count)
        job["concurrency"] = max(1, int(concurrency))
        job["interval"] = float(settings.get("interval", 0.0))
        job["stop"] = threading.Event()
        job["running"] = True
        job["started_at"] = time.time()
        stop_ev = job["stop"]
    threading.Thread(target=_run_job, args=(stop_ev,), daemon=True).start()
    return True, "已开始"


def stop_job():
    with lock:
        job["stop"].set()
    return True


def load_settings():
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        for k in ("interval", "concurrency", "count", "backoff_on", "backoff",
                  "backoff_max", "promo_code", "auto_redeem"):
            if k in d:
                settings[k] = d[k]
    except Exception:
        pass


def save_settings():
    try:
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(settings, f, ensure_ascii=False)
    except Exception:
        pass


def load_sessions():
    """email -> cookie"""
    m = {}
    try:
        with open(SESSION_FILE, "r", encoding="utf-8") as f:
            for line in f:
                line = line.rstrip("\n")
                if not line or line.startswith("#") or "----" not in line:
                    continue
                em, ck = line.split("----", 1)
                m[em] = ck
    except FileNotFoundError:
        pass
    return m


def load_accounts():
    global accounts
    sessions = load_sessions()
    try:
        with open(SUCCESS_FILE, "r", encoding="utf-8") as f:
            for line in f:
                line = line.rstrip("\n")
                if not line or line.startswith("#"):
                    continue
                parts = line.split("----")
                if len(parts) >= 3:
                    accounts.append({"email": parts[0], "name": parts[1], "pw": parts[2],
                                     "ts": 0, "sess": sessions.get(parts[0], "")})
    except FileNotFoundError:
        pass


def http_get(url, cookie="", proxy_url=None, timeout=15):
    h = dict(HEADERS)
    h.pop("Content-Type", None)
    h["Cookie"] = cookie
    req = urllib.request.Request(url, headers=h)
    try:
        r = make_opener(proxy_url).open(req, timeout=timeout)
        return r.status, r.read()
    except urllib.error.HTTPError as e:
        return e.code, e.read()
    except Exception as e:
        return None, str(e).encode()


def check_session(email, proxy_url=None):
    """用保存的 Cookie 验证登录态是否有效（读 /api/keys 的套餐与额度）"""
    with lock:
        acc = next((a for a in accounts if a["email"] == email), None)
        if proxy_url is None:
            p = next((x for x in proxies if x.active and not x.validating), None)
            proxy_url = p.url if p else None
    if not acc:
        return {"ok": False, "error": "账号不存在"}
    if not acc.get("sess"):
        return {"ok": False, "error": "该账号没有保存登录态 Cookie"}
    st, raw = http_get("https://alpme.com/api/keys", acc["sess"], proxy_url)
    if st is None:
        return {"ok": False, "error": raw.decode(errors="replace")[:120], "proxy": proxy_url or "本机IP"}
    try:
        js = json.loads(raw.decode(errors="replace"))
    except Exception:
        js = {}
    if st != 200 or not isinstance(js, dict) or "error" in js:
        return {"ok": False, "http": st, "error": str(js.get("error") or raw.decode(errors="replace")[:100]),
                "proxy": proxy_url or "本机IP"}
    q = js.get("quota") or {}
    plan = (q.get("plan") or {})
    return {"ok": True, "http": st, "proxy": proxy_url or "本机IP",
            "plan": plan.get("name") or plan.get("slug") or "-",
            "keys": len(js.get("keys") or []),
            "max_keys": q.get("max"), "left": q.get("left"),
            "window_5h": plan.get("window_5h"), "window_week": plan.get("window_week"),
            "canCreate": q.get("canCreate")}


def load_plans():
    """从 套餐状态.txt 读回兑换结果： 邮箱----套餐----说明"""
    try:
        with open(PLAN_FILE, "r", encoding="utf-8") as f:
            for line in f:
                line = line.rstrip("\n")
                if not line or line.startswith("#") or "----" not in line:
                    continue
                parts = line.split("----")
                if len(parts) >= 2:
                    plans[parts[0]] = {"plan": parts[1], "label": parts[2] if len(parts) > 2 else "",
                                       "ok": True, "ts": 0}
    except FileNotFoundError:
        pass


def save_plan(email, plan, label, ok=True):
    prev = plans.get(email) or {}
    if not ok and prev.get("plan") == plan and prev.get("label"):
        label = prev["label"]
    plans[email] = {"plan": plan, "label": label, "ok": ok, "ts": time.time()}
    try:
        old = {}
        try:
            with open(PLAN_FILE, "r", encoding="utf-8") as f:
                for line in f:
                    if "----" in line and not line.startswith("#"):
                        old[line.split("----")[0]] = line.rstrip("\n")
        except FileNotFoundError:
            pass
        old[email] = f"{email}----{plan}----{label}"
        with open(PLAN_FILE, "w", encoding="utf-8") as f:
            for v in old.values():
                f.write(v + "\n")
    except Exception:
        pass


def get_plan_info(email, cookie, proxy_url=None, timeout=20):
    """读 /api/keys 得到当前套餐"""
    st, raw = http_get("https://alpme.com/api/keys", cookie, proxy_url, timeout)
    try:
        js = json.loads(raw.decode(errors="replace"))
    except Exception:
        js = {}
    if st != 200 or not isinstance(js, dict) or "error" in js:
        return None
    p = ((js.get("quota") or {}).get("plan") or {})
    return {"plan": p.get("name") or p.get("slug") or "-",
            "w5": p.get("window_5h"), "wk": p.get("window_week"),
            "max_keys": p.get("max_keys")}


def redeem_code(email, cookie, code, proxy_url=None, timeout=25):
    """用登录态兑换兑换码，返回 (ok, 说明, 套餐名, http)"""
    h = dict(HEADERS)
    h["Cookie"] = cookie
    h["Origin"] = "https://alpme.com"
    h["Referer"] = "https://alpme.com/dashboard/referrals"
    body = json.dumps({"code": code}).encode()
    req = urllib.request.Request("https://alpme.com/api/promo/redeem", data=body,
                                 headers=h, method="POST")
    try:
        r = make_opener(proxy_url).open(req, timeout=timeout)
        st, raw = r.status, r.read()
    except urllib.error.HTTPError as e:
        st, raw = e.code, e.read()
    except Exception as e:
        return False, f"网络错误：{str(e)[:100]}", None, None
    try:
        js = json.loads(raw.decode(errors="replace"))
    except Exception:
        js = {}
    msg = js.get("message") or js.get("error") or raw.decode(errors="replace")[:120]
    label = js.get("rewardLabel") or ""
    if not label and "already" in str(msg).lower():
        st2, raw2 = http_get("https://alpme.com/api/promo", cookie, proxy_url, timeout)
        try:
            hist = (json.loads(raw2.decode(errors="replace")) or {}).get("history") or []
        except Exception:
            hist = []
        if hist:
            label = hist[0].get("rewardLabel") or ""
            msg = "该账号已兑换过此码，套餐仍然生效"
    info = get_plan_info(email, cookie, proxy_url, timeout)
    plan = info["plan"] if info else None
    if not label:
        label = msg
    ok = st == 200 and (js.get("ok") is True or "applied" in str(msg).lower()
                        or "already" in str(msg).lower())
    return ok, msg, plan, label, st


def redeem_batch(code, only_email=None):
    """对账号批量兑换兑换码（多线程，限制 5 并发）。返回启动的任务数"""
    code = (code or "").strip().upper()
    if not code:
        return 0, "兑换码不能为空"
    with lock:
        targets = [(a["email"], a.get("sess", "")) for a in accounts
                   if a.get("sess") and (only_email is None or a["email"] == only_email)]
    if not targets:
        return 0, "没有可用的登录态账号"
    for em, _ in targets:
        plans[em] = {"plan": "兑换中…", "label": "", "ok": None, "ts": time.time()}

    def one(em, ck):
        p = pick_proxy()
        purl = p.url if p else None
        ok, msg, plan, label, _st = redeem_code(em, ck, code, purl)
        with lock:
            seq["n"] += 1
            logs.appendleft({"id": seq["n"], "ts": time.time(), "kind": "success" if ok else "other",
                             "http": None, "email": em, "name": "-", "password": "-",
                             "reason": msg, "dur": 0, "proxy": display_proxy(purl) if purl else "",
                             "steps": [{"n": "兑换", "d": f"{code} → {'成功' if ok else '失败'}：{msg}", "ms": 0}]
                                      + ([{"n": "套餐", "d": plan, "ms": 0}] if plan else [])})
        if plan:
            save_plan(em, plan, label or msg, ok)
        elif not ok:
            plans[em] = {"plan": "未兑换", "label": msg[:60], "ok": False, "ts": time.time()}

    threads = []
    for em, ck in targets:
        t = threading.Thread(target=one, args=(em, ck), daemon=True)
        t.start()
        threads.append(t)
        if len(threads) % 5 == 0:
            time.sleep(0.15)
    return len(targets), ""


def save_proxies():
    with open(PROXIES_FILE, "w", encoding="utf-8") as f:
        for p in proxies:
            f.write(display_proxy(p.url) + "\n")


def validate_one(p):
    p.validating = True
    try:
        if p.url.startswith("socks"):
            if not HAVE_SOCKS:
                raise RuntimeError("缺少 PySocks")
            open_via_socks("https://alpme.com/", p.url, None, 10)
            p.mark_ok()
        else:
            make_opener(p.url).open(
                urllib.request.Request("https://alpme.com/", headers=HEADERS), timeout=10).close()
            p.mark_ok()
    except Exception as e:
        p.fails += 1
        p.last_err = str(e)[:90]
        p.active = False
    finally:
        p.validating = False


def add_proxies(text):
    """接受任意常见写法，自动归一化后加入；返回识别明细"""
    raw_lines = [x for x in re.split(r"[\r\n,;\t ]+", (text or "")) if x.strip()]
    added, bad, notes, dup = [], [], [], 0
    with lock:
        existing = {p.url for p in proxies}
        for raw in raw_lines:
            if raw.strip().startswith("#"):
                continue
            url, note = normalize_proxy(raw)
            if not url:
                bad.append({"raw": raw.strip(), "reason": note})
                continue
            if url in existing:
                dup += 1
                continue
            p = Proxy(url)
            p.validating = True
            proxies.append(p)
            added.append(p)
            existing.add(url)
            disp = display_proxy(url)
            if disp != raw.strip():
                notes.append({"raw": raw.strip(), "url": disp})
    for p in added:
        threading.Thread(target=validate_one, args=(p,), daemon=True).start()
    if added:
        save_proxies()
    return {"added": len(added), "dup": dup, "notes": notes, "bad": bad[:20],
            "bad_count": len(bad)}


def remove_proxy(url):
    global proxies
    with lock:
        proxies = [p for p in proxies if p.url != url]
    save_proxies()


def clear_proxies():
    global proxies
    with lock:
        proxies = []
    save_proxies()


def validate_all():
    with lock:
        items = list(proxies)
    for p in items:
        threading.Thread(target=validate_one, args=(p,), daemon=True).start()


def load_proxies():
    global proxies
    try:
        with open(PROXIES_FILE, "r", encoding="utf-8") as f:
            lines = [l.strip() for l in f if l.strip() and not l.strip().startswith("#")]
    except FileNotFoundError:
        lines = []
    urls = []
    for l in lines:
        u, _ = normalize_proxy(l)
        if u and u not in urls:
            urls.append(u)
    with lock:
        proxies = [Proxy(u) for u in urls]
    for p in proxies:
        threading.Thread(target=validate_one, args=(p,), daemon=True).start()


SHARED_CSS = r'''
:root{--bg:#0d1117;--card:#161b22;--in:#0d1117;--bd:#30363d;--tx:#e6edf3;--mut:#8b949e;
  --ok:#3fb950;--warn:#d29922;--err:#f85149;--acc:#58a6ff;}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--tx);font-size:13px;
  font-family:system-ui,-apple-system,"Segoe UI",Roboto,"PingFang SC","Microsoft YaHei",sans-serif}
header{padding:0 20px;height:52px;border-bottom:1px solid var(--bd);display:flex;align-items:center;gap:14px}
header h1{font-size:15px;margin:0;font-weight:600;white-space:nowrap}
header .dot{width:8px;height:8px;border-radius:50%;background:var(--mut)}
header .dot.on{background:var(--ok);box-shadow:0 0 8px var(--ok)}
nav{display:flex;gap:4px;margin-left:10px}
.navlink{color:var(--mut);text-decoration:none;padding:6px 12px;border-radius:7px;font-size:13px}
.navlink:hover{background:#21262d;color:var(--tx)}
.navlink.active{background:#1f6feb;color:#fff}
#runText{margin-left:auto}
main{padding:16px;max-width:1180px;margin:0 auto;display:flex;flex-direction:column;gap:14px}
.card{background:var(--card);border:1px solid var(--bd);border-radius:10px;padding:14px}
.card h3{margin:0 0 10px;font-size:13px;color:var(--mut);font-weight:500}
.row{display:flex;gap:10px;flex-wrap:wrap;align-items:flex-end}
.fld{display:flex;flex-direction:column;gap:4px}
.fld label{font-size:12px;color:var(--mut)}
input,textarea{background:var(--in);border:1px solid var(--bd);color:var(--tx);
  border-radius:7px;padding:8px 10px;font-size:13px;font-family:inherit}
input{height:36px}
input:focus,textarea:focus{outline:none;border-color:var(--acc)}
.grow{flex:1;min-width:200px}
button,.btn{border:1px solid var(--bd);background:#21262d;color:var(--tx);border-radius:7px;
  padding:8px 16px;font-size:13px;cursor:pointer;height:36px;text-decoration:none;display:inline-flex;align-items:center}
button:hover{border-color:var(--acc)}
button.primary{background:#1f6feb;border-color:#1f6feb;color:#fff}
button.danger{background:#da3633;border-color:#da3633;color:#fff}
button.sm{height:26px;padding:2px 10px;font-size:12px}
button:disabled{opacity:.45;cursor:not-allowed}
.ok{color:var(--ok)} .err{color:var(--err)} .mut{color:var(--mut)}
.strip{display:grid;grid-template-columns:repeat(4,1fr);gap:12px}
.sitem{background:var(--card);border:1px solid var(--bd);border-radius:10px;padding:14px}
.sitem .l{color:var(--mut);font-size:12px;margin-bottom:6px}
.sitem .v{font-size:26px;font-weight:700}
.tbl{max-height:56vh;overflow:auto;border:1px solid var(--bd);border-radius:8px}
table{width:100%;border-collapse:collapse;font-size:12px}
th,td{text-align:left;padding:6px 10px;border-bottom:1px solid var(--bd);white-space:nowrap}
th{color:var(--mut);font-weight:500;position:sticky;top:0;background:var(--card);z-index:1}
.mono{font-family:ui-monospace,Menlo,Consolas,monospace}
.tag{display:inline-block;padding:1px 8px;border-radius:20px;font-size:11px}
.s-success{background:rgba(63,185,80,.15);color:var(--ok)}
.s-ratelimit{background:rgba(210,153,34,.15);color:var(--warn)}
.s-exists{background:rgba(139,148,158,.15);color:var(--mut)}
.s-other{background:rgba(88,166,255,.15);color:var(--acc)}
.s-error{background:rgba(248,81,73,.15);color:var(--err)}
.s-on{background:rgba(63,185,80,.15);color:var(--ok)}
.s-off{background:rgba(248,81,73,.15);color:var(--err)}
.s-ing{background:rgba(210,153,34,.15);color:var(--warn)}
.hint{color:var(--mut);font-size:11px}
.strip2{display:grid;grid-template-columns:repeat(4,1fr);gap:12px}
.sitem.sm{padding:10px 12px}
.sitem.sm .v{font-size:18px}
.chk{display:inline-flex;align-items:center;gap:6px;color:var(--mut);font-size:12px;height:36px;white-space:nowrap}
.chk input{height:14px;width:14px}
.logbox{height:60vh;overflow:auto;background:#0a0d12;border:1px solid var(--bd);border-radius:8px;
  padding:8px 10px;font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12px;line-height:1.75}
.logitem{padding:3px 2px 5px;border-bottom:1px dashed #1b2027}
.loghead{display:flex;gap:10px;white-space:nowrap}
.logline{display:flex;gap:10px;white-space:nowrap;padding:1px 4px;border-radius:4px}
.logitem:hover{background:#11161d}
.lt{color:#6e7681;flex:none}
.lk{flex:none;min-width:46px}
.lem{color:#c9d1d9;flex:none}
.lr{color:#8b949e;overflow:hidden;text-overflow:ellipsis}
.steps{margin:1px 0 2px 86px;display:flex;flex-direction:column}
.step{display:flex;gap:8px;white-space:nowrap;line-height:1.6}
.step .st{color:#484f58;min-width:62px;text-align:right;flex:none}
.step .sn{color:#7d8590;min-width:96px;flex:none}
.step .sd{color:#5a6472;overflow:hidden;text-overflow:ellipsis;max-width:720px}
.k-success .lk{color:var(--ok)}
.k-ratelimit .lk{color:var(--warn)}
.k-exists .lk{color:var(--mut)}
.k-other .lk{color:var(--acc)}
.k-error .lk{color:var(--err)}
.toast{position:fixed;right:18px;bottom:18px;max-width:520px;background:#1f2937;border:1px solid var(--bd);
  color:var(--tx);padding:10px 14px;border-radius:8px;font-size:12px;opacity:0;transform:translateY(8px);
  transition:.18s;pointer-events:none;z-index:99;box-shadow:0 8px 24px rgba(0,0,0,.4)}
.toast.show{opacity:1;transform:translateY(0)}
.toast.terr{border-color:var(--err);color:#ffb4ae}
.k-warn .lk{color:#d29922}
.k-warn .loghead{background:rgba(210,153,34,.08);border-radius:4px}
.k-success .loghead{background:rgba(63,185,80,.06);border-radius:4px}
.k-error .loghead{background:rgba(248,81,73,.06);border-radius:4px}
'''

COMMON_JS = r'''
const SL={success:"成功",exists:"已存在",ratelimit:"限流",other:"其他",error:"异常",warn:"提示"};
function esc(s){return (s==null?"":String(s)).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]))}
function ts(ms){return new Date(ms).toLocaleTimeString("zh-CN",{hour12:false})}
function fmt(n){return (n||0).toLocaleString()}
async function getJSON(u){try{return await (await fetch(u,{cache:"no-store"})).json()}catch(e){return null}}
async function post(u,b){try{return await (await fetch(u,{method:"POST",headers:{"content-type":"application/json"},body:JSON.stringify(b||{})})).json()}catch(e){return {}}}
function setRun(d){document.getElementById("runDot").className="dot"+(d.running?" on":"");document.getElementById("runText").textContent=d.running?"运行中":"空闲"}
'''

PAGE_PROXY_BODY = r'''
<section class="card"><h3>注册设置</h3>
  <div class="row">
    <div class="fld"><label>注册相隔（秒）</label>
      <input id="interval" type="number" step="0.1" min="0" value="0" style="width:130px"/></div>
    <div class="fld"><label>限流退避（秒）</label>
      <input id="backoff" type="number" step="1" min="0" value="15" style="width:130px"/></div>
    <div class="fld"><label>退避上限（秒）</label>
      <input id="backoffMax" type="number" step="1" min="0" value="180" style="width:130px"/></div>
    <label class="chk"><input type="checkbox" id="backoffOn" checked/> 限流时自动退避</label>
    <button class="primary" id="saveSet">保存设置</button>
    <span class="hint" id="smsg"></span>
  </div>
</section>
<section class="card"><h3>代理列表</h3>
  <textarea id="proxyBox" rows="4" style="width:100%" placeholder="每行一个：网关:端口@用户名:密码"></textarea>
  <div class="row" style="margin-top:10px">
    <button class="primary" id="addProxyBtn">添加并校验</button>
    <button id="revalidateBtn">全部复检</button>
    <button id="clearProxyBtn">清空</button>
    <span class="hint" id="proxySummary">0 个</span>
    <span id="msg" class="hint" style="color:var(--acc)"></span>
  </div>
  <div id="addResult" class="hint" style="margin-top:8px"></div>
  <div class="tbl" style="margin-top:12px"><table>
    <thead><tr><th>代理</th><th>状态</th><th>成功</th><th>已用</th><th>连续限流</th><th>连续失败</th><th>最近错误</th><th></th></tr></thead>
    <tbody id="proxyBody"><tr><td colspan="8" class="hint">无代理（使用本机 IP）</td></tr></tbody>
  </table></div>
</section>
'''

PAGE_PROXY_JS = r'''
document.getElementById("saveSet").onclick=async()=>{
  const v=+document.getElementById("interval").value||0;
  const bk=+document.getElementById("backoff").value||0;
  const bm=+document.getElementById("backoffMax").value||0;
  const on=document.getElementById("backoffOn").checked;
  await post("/api/settings",{interval:v,backoff:bk,backoff_max:bm,backoff_on:on});
  document.getElementById("smsg").textContent="已保存（相隔 "+v+"s · 退避 "+bk+"s/上限 "+bm+"s · "+(on?"开启":"关闭")+"）";
};
document.getElementById("addProxyBtn").onclick=async()=>{
  const t=document.getElementById("proxyBox").value; if(!t.trim())return;
  const r=await post("/api/proxies/add",{text:t});
  document.getElementById("proxyBox").value="";
  let html="新增 "+r.added+" 个，校验中…";
  if(r.dup) html+=" · 重复跳过 "+r.dup+" 个";
  if(r.notes&&r.notes.length){
    html+="<br/><span style='color:var(--acc)'>已统一为 "+r.notes.length+" 条：</span><br/>"+
      r.notes.slice(0,8).map(n=>"&nbsp;&nbsp;"+esc(n.raw)+" → "+esc(n.url)).join("<br/>");
  }
  if(r.bad&&r.bad.length){
    html+="<br/><span style='color:var(--err)'>格式不对 "+r.bad_count+" 条：</span><br/>"+
      r.bad.slice(0,8).map(n=>"&nbsp;&nbsp;"+esc(n.raw)+" <span style='color:var(--mut)'>("+esc(n.reason)+")</span>").join("<br/>");
  }
  document.getElementById("addResult").innerHTML=html;
};
document.getElementById("revalidateBtn").onclick=async()=>{await post("/api/proxies/validate");document.getElementById("msg").textContent="已触发复检";};
document.getElementById("clearProxyBtn").onclick=async()=>{await post("/api/proxies/clear");document.getElementById("msg").textContent="已清空";};
async function rmProxy(url){await post("/api/proxies/remove",{url:url});}
window.rmProxy=rmProxy;
async function tick(){
  const d=await getJSON("/api/stats"); if(!d)return;
  const fill=(id,v)=>{const el=document.getElementById(id);if(document.activeElement!==el)el.value=v;};
  fill("interval",d.settings.interval);
  fill("backoff",d.settings.backoff);
  fill("backoffMax",d.settings.backoff_max);
  document.getElementById("backoffOn").checked=!!d.settings.backoff_on;
  document.getElementById("proxySummary").textContent=`${d.proxies.total} 个 · 可用 ${d.proxies.active}`;
  const pb=document.getElementById("proxyBody");
  if(!d.proxies.list.length){pb.innerHTML='<tr><td colspan="8" class="hint">无代理（使用本机 IP）</td></tr>';return;}
  pb.innerHTML=d.proxies.list.map(p=>{
    const st=p.validating?'<span class="tag s-ing">校验中</span>':(p.active?'<span class="tag s-on">可用</span>':'<span class="tag s-off">失效</span>');
    return `<tr><td class="mono" style="max-width:280px;overflow:hidden;text-overflow:ellipsis">${esc(p.disp||p.url)}</td>
      <td>${st}</td><td>${p.ok}</td><td>${p.used||0}</td><td>${p.rl||0}</td><td>${p.fails}</td>
      <td class="hint" style="max-width:240px;overflow:hidden;text-overflow:ellipsis">${esc(p.last_err||"-")}</td>
      <td><button class="sm" onclick="rmProxy('${esc(p.url)}')">移除</button></td></tr>`;}).join("");
}
tick();setInterval(tick,1000);
'''

PAGE_REG_BODY = r'''
<section class="card">
  <div class="row">
    <div class="fld"><label>注册数量（0=无限）</label><input id="count" type="number" value="200" style="width:150px"/></div>
    <div class="fld"><label>并发</label><input id="conc" type="number" value="10" style="width:110px"/></div>
    <button class="primary" id="startBtn">开始注册</button>
    <button class="danger" id="stopBtn" disabled>停止</button>
    <button id="clearLogBtn">清空日志</button>
    <label class="chk"><input type="checkbox" id="showSteps" checked/> 显示每一步</label>
    <span id="msg" class="hint" style="color:var(--acc)"></span>
  </div>
</section>
<section class="strip">
  <div class="sitem"><div class="l">注册目标</div><div class="v" id="p_target">-</div></div>
  <div class="sitem"><div class="l">成功</div><div class="v ok" id="p_success">0</div></div>
  <div class="sitem"><div class="l">失败</div><div class="v err" id="p_fail">0</div></div>
  <div class="sitem"><div class="l">总请求</div><div class="v" id="p_total">0</div></div>
</section>
<section class="strip2">
  <div class="sitem sm"><div class="l">成功率</div><div class="v" id="p_rate">0%</div></div>
  <div class="sitem sm"><div class="l">平均耗时</div><div class="v" id="p_avg">0 ms</div></div>
  <div class="sitem sm"><div class="l">限流次数</div><div class="v" id="p_rl">0</div></div>
  <div class="sitem sm"><div class="l">退避等待</div><div class="v" id="p_wait">0 s</div></div>
</section>
<section class="card"><h3>执行日志（最新在上 · 每次尝试的每一步都有记录 · 最近 60 次）</h3>
  <div class="logbox" id="logBox"><div class="hint">等待开始…</div></div>
</section>
'''

PAGE_REG_JS = r'''
let SHOW_STEPS = localStorage.getItem("showSteps") !== "0";
const cb = document.getElementById("showSteps");
cb.checked = SHOW_STEPS;
cb.onchange = () => { SHOW_STEPS = cb.checked; localStorage.setItem("showSteps", cb.checked ? "1" : "0"); lastSig = ""; };

document.getElementById("startBtn").onclick=async()=>{
  const r=await post("/api/start",{count:+document.getElementById("count").value,
    concurrency:+document.getElementById("conc").value});
  document.getElementById("msg").textContent=r.ok?"已开始注册":(r.msg||"启动失败");
  lastSig="";
};
document.getElementById("stopBtn").onclick=async()=>{
  await post("/api/stop");document.getElementById("msg").textContent="已发送停止";
};
document.getElementById("clearLogBtn").onclick=async()=>{
  if(!confirm("确定清空执行日志并重置统计（成功/失败/总请求归零）？\n已保存的账号记录不受影响。"))return;
  const r=await post("/api/logs/clear",{reset_stats:true});
  document.getElementById("msg").textContent="已清空日志（"+((r&&r.cleared)||0)+" 条）";
  lastSig="";
};
let lastSig="";
function renderLog(d){
  document.getElementById("startBtn").disabled=d.running;
  document.getElementById("stopBtn").disabled=!d.running;
  document.getElementById("p_target").textContent=(d.target===0?"无限":d.target);
  document.getElementById("p_success").textContent=fmt(d.stats.success);
  document.getElementById("p_fail").textContent=fmt(d.fail);
  document.getElementById("p_total").textContent=fmt(d.total);
  document.getElementById("p_rate").textContent=(d.success_rate*100).toFixed(1)+"%";
  document.getElementById("p_rate").className="v "+((d.success_rate>=0.5)?"ok":(d.success_rate>0?"":"err"));
  document.getElementById("p_avg").textContent=d.avg_ms+" ms";
  document.getElementById("p_rl").textContent=fmt(d.stats.ratelimit);
  document.getElementById("p_wait").textContent=(d.backoff_wait>0?d.backoff_wait+" s(连续限流)":"0 s");
  const box=document.getElementById("logBox");
  const sig=(d.logs[0]?d.logs[0].id:0)+"/"+d.logs.length+"/"+SHOW_STEPS+"/"+d.running;
  if(sig===lastSig)return;
  lastSig=sig;
  if(!d.logs.length){box.innerHTML='<div class="hint">等待开始…（点上方「开始注册」）</div>';return;}
  box.innerHTML=d.logs.map(l=>{
    const http=l.http?(" · HTTP "+l.http):"";
    const reason=l.reason?(" · "+esc(l.reason)):"";
    const out=l.proxy?(" · 出口 "+esc(l.proxy)):" · 出口 本机IP";
    const steps=(SHOW_STEPS&&l.steps)?l.steps.map(s=>
      `<div class="step"><span class="st">+${s.ms}ms</span><span class="sn">${esc(s.n)}</span><span class="sd">${esc(s.d||"")}</span></div>`).join(""):"";
    return `<div class="logitem k-${l.kind}">
      <div class="loghead">
        <span class="lt">${ts(l.ts)}</span>
        <span class="lk">[${SL[l.kind]||l.kind}]</span>
        <span class="lem">#${l.id} ${esc(l.email)} / ${esc(l.name)} / ${esc(l.password)}</span>
        <span class="lr">${l.dur}ms${http}${out}${reason}</span>
      </div>${steps}</div>`;}).join("");
}
async function tick(){
  const d=await getJSON("/api/stats"); if(!d)return; setRun(d); renderLog(d);
}
tick();setInterval(tick,1000);
'''

PAGE_ACC_BODY = r'''
<section class="card">
  <h3>兑换码</h3>
  <div class="row">
    <div class="fld"><label>兑换码</label><input id="promoCode" value="ALP27" style="width:150px" class="mono"/></div>
    <button class="primary" id="redeemAll">全部兑换</button>
    <label class="hint" style="display:flex;align-items:center;gap:6px;margin-left:6px">
      <input type="checkbox" id="autoRedeem" style="width:auto"/> 注册成功后自动兑换
    </label>
    <span class="hint" id="rmsg"></span>
  </div>
</section>
<section class="card">
  <div class="row">
    <div class="fld grow"><label>搜索（邮箱/姓名/套餐）</label><input id="q" placeholder="输入关键词过滤"/></div>
    <a class="btn" href="/api/download/success">下载账号</a>
    <button id="copyAll">复制账号</button>
    <span class="hint" id="accSummary">共 0 个</span>
  </div>
</section>
<section class="card"><h3>账号列表（邮箱——姓名——密码 · 当前套餐）</h3>
  <div class="tbl" style="max-height:60vh"><table>
    <thead><tr><th>#</th><th>邮箱</th><th>姓名</th><th>密码</th><th>当前套餐</th><th>时间</th><th></th></tr></thead>
    <tbody id="accBody"><tr><td colspan="7" class="hint">暂无成功账号</td></tr></tbody>
  </table></div>
</section>
'''

PAGE_ACC_JS = r'''
let ACC=[];
function line(a){return a.email+"----"+a.name+"----"+a.pw}
function copyText(t){if(navigator.clipboard){navigator.clipboard.writeText(t).then(()=>toast("已复制"),()=>fallback(t))}else{fallback(t)}}
function fallback(t){const ta=document.createElement("textarea");ta.value=t;document.body.appendChild(ta);ta.select();try{document.execCommand("copy")}catch(e){}document.body.removeChild(ta);toast("已复制")}
function toast(msg,err){
  let t=document.getElementById("toast");
  if(!t){t=document.createElement("div");t.id="toast";document.body.appendChild(t);}
  t.className="toast show"+(err?" terr":"");t.textContent=msg;
  clearTimeout(window._tt);window._tt=setTimeout(()=>{t.className="toast";},3200);
}
async function redeemOne(i,btn){
  const a=ACC[i];btn.disabled=true;btn.textContent="兑换中";
  const r=await post("/api/redeem",{email:a.email,code:document.getElementById("promoCode").value||"ALP27"});
  btn.disabled=false;btn.textContent="兑换";
  if(r&&r.ok){toast("已提交兑换，正在读取套餐…");}else{toast("兑换失败："+((r&&r.msg)||"未知错误"),true);}
}
function planBadge(a){
  if(a.plan==="兑换中…") return '<span class="tag s-ing">兑换中…</span>';
  if(a.plan && a.plan!=="未兑换"){
    const cls=String(a.plan).toLowerCase()==="ultra"?"s-on":"s-ing";
    return `<span class="tag ${cls}">${esc(a.plan)}</span>`+(a.plan_label?` <span class="hint">${esc(a.plan_label)}</span>`:"");
  }
  if(a.plan==="未兑换") return `<span class="tag s-off">未兑换</span> <span class="hint">${esc(a.plan_label||"")}</span>`;
  return '<span class="hint">—</span>';
}
async function tick(){
  const d=await getJSON("/api/accounts"); if(!d)return;
  const q=(document.getElementById("q").value||"").toLowerCase();
  ACC=d.accounts.filter(a=>!q||(a.email+" "+a.name+" "+(a.plan||"")).toLowerCase().includes(q));
  document.getElementById("accSummary").textContent=
    `共 ${d.accounts.length} 个 · Ultra ${d.ultra||0} 个 · 兑换码 ${d.promo_code||"-"}`;
  const ar=document.getElementById("autoRedeem");
  if(!ar.dataset.touched) ar.checked=!!d.auto_redeem;
  const pc=document.getElementById("promoCode");
  if(!pc.dataset.touched && d.promo_code) pc.value=d.promo_code;
  const rb=document.getElementById("accBody");
  if(!ACC.length){rb.innerHTML='<tr><td colspan="7" class="hint">暂无成功账号</td></tr>';return;}
  rb.innerHTML=ACC.map((a,i)=>`<tr>
      <td class="mut">${i+1}</td>
      <td class="mono">${esc(a.email)}</td>
      <td>${esc(a.name)}</td>
      <td class="mono">${esc(a.pw)}</td>
      <td>${planBadge(a)}</td>
      <td class="mut mono">${a.ts?ts(a.ts):"—"}</td>
      <td><button class="sm" data-r="${i}">兑换</button> <button class="sm" data-i="${i}">复制</button></td></tr>`).join("");
  rb.querySelectorAll("button[data-i]").forEach(b=>b.onclick=()=>copyText(line(ACC[+b.dataset.i])));
  rb.querySelectorAll("button[data-r]").forEach(b=>b.onclick=()=>redeemOne(+b.dataset.r,b));
}
document.getElementById("q").oninput=tick;
document.getElementById("promoCode").oninput=e=>{e.target.dataset.touched="1";};
document.getElementById("copyAll").onclick=()=>copyText(ACC.map(line).join("\n"));
document.getElementById("redeemAll").onclick=async()=>{
  const code=document.getElementById("promoCode").value.trim()||"ALP27";
  const n=ACC.length;
  if(!n){toast("没有账号可兑换",true);return;}
  const r=await post("/api/redeem",{code:code});
  document.getElementById("rmsg").textContent=r.ok?`已提交 ${r.count} 个账号兑换（${r.code}），稍候刷新查看套餐`:(r.msg||"提交失败");
  if(r.ok) toast(`已提交 ${r.count} 个账号兑换`);
};
document.getElementById("autoRedeem").onchange=async e=>{
  e.target.dataset.touched="1";
  await post("/api/settings",{auto_redeem:e.target.checked});
  toast(e.target.checked?"注册成功后将自动兑换":"已关闭自动兑换");
};
tick();setInterval(tick,1500);
'''

NAV = [("register", "注册"), ("accounts", "账号管理"), ("proxies", "代理配置")]

PAGES = {
    "proxies": {"title": "代理配置", "body": PAGE_PROXY_BODY, "script": PAGE_PROXY_JS},
    "register": {"title": "注册", "body": PAGE_REG_BODY, "script": PAGE_REG_JS},
    "accounts": {"title": "账号管理", "body": PAGE_ACC_BODY, "script": PAGE_ACC_JS},
}


def render_page(active):
    pg = PAGES[active]
    nav = "".join(
        f'<a class="navlink{" active" if k == active else ""}" href="/{k}">{name}</a>'
        for k, name in NAV)
    return (
        '<!DOCTYPE html><html lang="zh-CN"><head><meta charset="utf-8"/>'
        '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
        f'<title>{pg["title"]} · Alpme</title>'
        f'<style>{SHARED_CSS}</style></head><body>'
        '<header><span class="dot" id="runDot"></span><h1>Alpme</h1>'
        f'<nav>{nav}</nav><span id="runText" class="hint">空闲</span></header>'
        f'<main>{pg["body"]}</main>'
        f'<script>{COMMON_JS}</script>'
        f'<script>{pg["script"]}</script>'
        '</body></html>'
    )


class Handler(BaseHTTPRequestHandler):
    def _send(self, code, body, ctype="application/json", extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        if extra:
            for k, v in extra.items():
                self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _body(self):
        n = int(self.headers.get("Content-Length", 0) or 0)
        raw = self.rfile.read(n) if n else b""
        try:
            return json.loads(raw.decode("utf-8")) if raw else {}
        except Exception:
            return {}

    def do_GET(self):
        path = self.path.split("?")[0]
        if path == "/" or path == "/register":
            self._send(200, render_page("register"), "text/html; charset=utf-8")
        elif path == "/proxies":
            self._send(200, render_page("proxies"), "text/html; charset=utf-8")
        elif path == "/accounts":
            self._send(200, render_page("accounts"), "text/html; charset=utf-8")
        elif path == "/api/stats":
            with lock:
                s = dict(stats)
                total = sum(s.values())
                log_list = list(logs)[:60]
                plist = [p.to_dict() for p in proxies]
                jb = {"count": job["count"], "concurrency": job["concurrency"],
                      "interval": job["interval"]}
                running = job["running"]
                dur_sum, dur_n = agg["dur_sum"], agg["dur_n"]
                rl_streak, bw = agg["rl_streak"], agg["backoff_wait"]
            self._send(200, json.dumps({
                "running": running, "stats": s, "total": total,
                "success": s["success"], "fail": total - s["success"],
                "success_rate": (s["success"] / total if total else 0),
                "avg_ms": (int(dur_sum / dur_n) if dur_n else 0),
                "rl_streak": rl_streak, "backoff_wait": bw,
                "target": jb["count"], "logs": log_list, "job": jb,
                "settings": settings,
                "proxies": {"total": len(plist),
                            "active": sum(1 for p in plist if p["active"] and not p["validating"]),
                            "list": plist},
            }))
        elif path == "/api/accounts":
            with lock:
                accs = []
                for a in accounts:
                    d = dict(a)
                    d.pop("sess", None)
                    pl = plans.get(a["email"])
                    d["plan"] = (pl or {}).get("plan") or ""
                    d["plan_label"] = (pl or {}).get("label") or ""
                    d["plan_ok"] = (pl or {}).get("ok")
                    accs.append(d)
                cnt_ultra = sum(1 for a in accs if a["plan"] and a["plan"].lower() == "ultra")
            self._send(200, json.dumps({"accounts": accs[::-1], "count": len(accs),
                                        "ultra": cnt_ultra,
                                        "promo_code": settings.get("promo_code", ""),
                                        "auto_redeem": settings.get("auto_redeem", False)},
                                       ensure_ascii=False))
        elif path == "/api/download/success":
            try:
                with open(SUCCESS_FILE, "rb") as f:
                    data = f.read()
            except FileNotFoundError:
                data = b""
            self._send(200, data, "text/plain; charset=utf-8",
                       {"Content-Disposition": "attachment; filename=success.txt"})
        elif path == "/api/download/sessions":
            try:
                with open(SESSION_FILE, "rb") as f:
                    data = f.read()
            except FileNotFoundError:
                data = b""
            self._send(200, data, "text/plain; charset=utf-8",
                       {"Content-Disposition": "attachment; filename=sessions.txt"})
        else:
            self._send(404, "not found")

    def do_POST(self):
        b = self._body()
        path = self.path.split("?")[0]
        if path == "/api/start":
            ok, msg = start_job(b.get("count", 200), b.get("concurrency", 10))
            self._send(200, json.dumps({"ok": ok, "msg": msg}))
        elif path == "/api/stop":
            stop_job(); self._send(200, json.dumps({"ok": True}))
        elif path == "/api/settings":
            if "interval" in b:
                settings["interval"] = max(0.0, float(b["interval"] or 0))
            if "backoff" in b:
                settings["backoff"] = max(0.0, float(b["backoff"] or 0))
            if "backoff_max" in b:
                settings["backoff_max"] = max(0.0, float(b["backoff_max"] or 0))
            if "backoff_on" in b:
                settings["backoff_on"] = bool(b["backoff_on"])
            if "promo_code" in b:
                settings["promo_code"] = str(b["promo_code"] or "").strip()
            if "auto_redeem" in b:
                settings["auto_redeem"] = bool(b["auto_redeem"])
            if "concurrency" in b:
                settings["concurrency"] = int(b["concurrency"])
            if "count" in b:
                settings["count"] = int(b["count"])
            save_settings()
            self._send(200, json.dumps({"ok": True, "settings": settings}))
        elif path == "/api/logs/clear":
            with lock:
                n = len(logs)
                logs.clear()
                seq["n"] = 0
                if b.get("reset_stats", True):
                    for k in stats:
                        stats[k] = 0
                    agg["dur_sum"] = 0; agg["dur_n"] = 0
                    agg["rl_streak"] = 0
            self._send(200, json.dumps({"ok": True, "cleared": n}))
        elif path == "/api/proxies/add":
            r = add_proxies(b.get("text", ""))
            r["ok"] = True
            self._send(200, json.dumps(r, ensure_ascii=False))
        elif path == "/api/proxies/remove":
            remove_proxy(b.get("url", "")); self._send(200, json.dumps({"ok": True}))
        elif path == "/api/proxies/clear":
            clear_proxies(); self._send(200, json.dumps({"ok": True}))
        elif path == "/api/proxies/validate":
            validate_all(); self._send(200, json.dumps({"ok": True}))
        elif path == "/api/accounts/check":
            self._send(200, json.dumps(check_session(b.get("email", ""), b.get("proxy")),
                                       ensure_ascii=False))
        elif path == "/api/redeem":
            code = b.get("code") or settings.get("promo_code") or ""
            only = b.get("email") or None
            n, err = redeem_batch(code, only)
            self._send(200, json.dumps({"ok": n > 0, "count": n, "code": str(code).upper(),
                                        "msg": err}, ensure_ascii=False))
        else:
            self._send(404, "not found")

    def log_message(self, *a):
        pass


def main():
    ap = argparse.ArgumentParser(description="Alpme 注册三页面控制台")
    ap.add_argument("--port", type=int, default=8080)
    ap.add_argument("--host", default="127.0.0.1")
    args = ap.parse_args()

    open(SUCCESS_FILE, "a", encoding="utf-8").close()
    load_settings()
    load_accounts()
    load_plans()
    load_proxies()

    srv = ThreadingHTTPServer((args.host, args.port), Handler)
    print("=" * 52)
    print(f"  控制台已启动： http://127.0.0.1:{args.port}")
    print("  页面：/register(注册)  /accounts(账号管理)  /proxies(代理配置)")
    print(f"  成功记录： {SUCCESS_FILE}  已载入 {len(accounts)} 个账号")
    print(f"  代理文件： {PROXIES_FILE}  已载入 {len(proxies)} 个")
    print("  按 Ctrl+C 退出")
    print("=" * 52)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\n已退出")


if __name__ == "__main__":
    main()
