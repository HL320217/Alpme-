"""
Alpme 注册脚本 v2（协议级 + 代理池管理 + 实时仪表盘）
============================================================
功能：
  1. 协议级注册：POST /api/auth/signup（无需验证码/CSRF/邀请码）
  2. 代理池管理：启动前自动校验可用性；连续失败自动剔除；实时健康度
  3. 实时仪表盘：内置 HTTP 服务，浏览器查看 QPS / 成功率 / 状态分布 / 代理健康
  4. 随机数据：@qq.com 与 @gmail.com 混合、随机姓名、随机 12 位密码
  5. 成功记录写入「邮箱----姓名----密码」

注意：
  * 站点有「单 IP 注册上限」，单机单 IP 很快被限流（接口返回限流即验证生效）。
    想继续注册，请把代理按行填进 proxies.txt（http/https 直连；socks5 需 pip install pysocks）。
  * 仅供学习与技术研究使用。

用法：
  python alpme_register.py -n 200 -c 10        # 注册 200 个，并发 10，开仪表盘
  python alpme_register.py -n 0 -c 20          # 无限循环（网页点「停止」或 Ctrl+C）
  python alpme_register.py --port 9090 -n 500  # 自定义仪表盘端口
  python alpme_register.py --no-dashboard      # 关闭仪表盘，纯终端模式
"""

import json
import random
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

TARGET_URL   = "https://alpme.com/api/auth/signup"
OUTPUT_FILE  = "注册成功记录.txt"
FAIL_FILE    = "注册失败记录.txt"
MAX_REGISTER = 200
CONCURRENCY  = 10
JITTER       = 0.0
PROXIES_FILE = "proxies.txt"
QQ_RATIO     = 0.5
DASHBOARD_PORT = 8080
PROXY_FAIL_THRESHOLD = 3
PROXY_TEST   = True

FIRST_NAMES = ["James","Mary","John","Patricia","Robert","Jennifer","Michael","Linda",
               "William","Elizabeth","David","Barbara","Richard","Susan","Joseph","Jessica",
               "Thomas","Sarah","Charles","Karen","Chris","Alex","Taylor","Jordan",
               "Morgan","Casey","Riley","Jamie","Avery","Quinn"]
LAST_NAMES = ["Smith","Johnson","Williams","Brown","Jones","Garcia","Miller","Davis",
              "Rodriguez","Martinez","Hernandez","Lopez","Gonzalez","Wilson","Anderson",
              "Thomas","Taylor","Moore","Jackson","Martin","Lee","Perez","Thompson","White",
              "Harris","Clark","Lewis","Walker","Hall","Young"]

HEADERS = {
    "Content-Type": "application/json",
    "Accept": "application/json",
    "Origin": "https://alpme.com",
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/120.0 Safari/537.36"),
}

lock = threading.Lock()
stop = threading.Event()
stats = {"success": 0, "exists": 0, "ratelimit": 0, "other": 0, "error": 0}
history = deque(maxlen=180)
_last = {"total": 0, "success": 0}
_last_sample_time = time.time()
proxies = []


class Proxy:
    def __init__(self, url):
        self.url = url
        self.active = True
        self.fails = 0
        self.ok = 0
        self.last_err = ""

    def mark_ok(self):
        self.ok += 1
        self.fails = 0

    def mark_fail(self, err=""):
        self.fails += 1
        self.ok = 0
        self.last_err = err
        if self.fails >= PROXY_FAIL_THRESHOLD:
            self.active = False

    def to_dict(self):
        return {"url": self.url, "active": self.active,
                "ok": self.ok, "fails": self.fails, "last_err": self.last_err}


def rand_str(n, pool):
    return "".join(random.choices(pool, k=n))


def gen_email():
    if random.random() < QQ_RATIO:
        digits = rand_str(random.randint(6, 11), string.digits)
        return digits + "@qq.com"
    local = rand_str(random.randint(8, 14), string.ascii_lowercase + string.digits)
    return local + "@gmail.com"


def gen_name():
    return random.choice(FIRST_NAMES) + " " + random.choice(LAST_NAMES)


def gen_password():
    return rand_str(12, string.ascii_letters + string.digits)


def make_opener(proxy_url):
    """为 http/https 代理构造 opener（自动处理 https 的 CONNECT 隧道）。"""
    if not proxy_url:
        return urllib.request.build_opener()
    handler = urllib.request.ProxyHandler({"http": proxy_url, "https": proxy_url})
    return urllib.request.build_opener(handler)


def open_via_socks(url, proxy_url, data, timeout):
    """socks5 代理专用（需 PySocks）。返回 (status, body_bytes)。"""
    import ssl
    import http.client
    p = urllib.parse.urlparse(proxy_url)
    phost, pport = p.hostname, p.port or 1080
    user, pw = p.username, p.password
    u = urllib.parse.urlparse(url)
    dest_host = u.hostname
    dest_port = u.port or (443 if u.scheme == "https" else 80)
    s = socks.socksocket()
    s.set_proxy(socks.SOCKS5, phost, pport, rdns=True, username=user, password=pw)
    s.settimeout(timeout)
    s.connect((dest_host, dest_port))
    if u.scheme == "https":
        ctx = ssl.create_default_context()
        s = ctx.wrap_socket(s, server_hostname=dest_host)
    h = http.client.HTTPConnection(dest_host, dest_port, timeout=timeout)
    h.sock = s
    path = u.path or "/"
    if u.query:
        path += "?" + u.query
    h.request("POST", path, body=data, headers=HEADERS)
    resp = h.getresponse()
    return resp.status, resp.read()


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


def register(proxy_obj):
    """执行一次注册。返回 (类别, 原因, (邮箱, 姓名, 密码))。"""
    email, name, pw = gen_email(), gen_name(), gen_password()
    body = json.dumps({
        "email": email, "password": pw, "name": name,
        "ref": "", "promo": "", "captcha": ""
    }).encode("utf-8")
    status, js, net_err = None, None, ""
    purl = proxy_obj.url if proxy_obj else None
    try:
        if purl and purl.startswith("socks"):
            if not HAVE_SOCKS:
                return "error", "socks5 需要 pip install pysocks", (email, name, pw)
            status, raw = open_via_socks(TARGET_URL, purl, body, 20)
            try:
                js = json.loads(raw.decode(errors="replace"))
            except Exception:
                js = {}
        else:
            opener = make_opener(purl)
            req = urllib.request.Request(TARGET_URL, data=body, method="POST", headers=HEADERS)
            r = opener.open(req, timeout=20)
            status = r.status
            try:
                js = json.loads(r.read().decode(errors="replace"))
            except Exception:
                js = {}
    except urllib.error.HTTPError as e:
        status = e.code
        try:
            js = json.loads(e.read().decode(errors="replace"))
        except Exception:
            js = {}
    except Exception as e:
        net_err = str(e)[:160]
        return "error", net_err, (email, name, pw)

    kind, msg = classify(status, js)
    return kind, msg, (email, name, pw)


def pick_proxy():
    with lock:
        active = [p for p in proxies if p.active]
    if not active:
        return None
    return random.choice(active)


def worker():
    while not stop.is_set():
        with lock:
            if MAX_REGISTER > 0 and sum(stats.values()) >= MAX_REGISTER:
                break
        proxy_obj = pick_proxy()
        kind, msg, creds = register(proxy_obj)
        with lock:
            stats[kind] += 1
        if kind == "success":
            with open(OUTPUT_FILE, "a", encoding="utf-8") as f:
                f.write(f"{creds[0]}----{creds[1]}----{creds[2]}\n")
            if proxy_obj:
                proxy_obj.mark_ok()
        elif kind == "error":
            if proxy_obj:
                proxy_obj.mark_fail(msg)
        else:
            if proxy_obj:
                proxy_obj.mark_ok()
            with open(FAIL_FILE, "a", encoding="utf-8") as f:
                f.write(f"[{kind}] {creds[0]} | {msg}\n")
        if JITTER:
            time.sleep(random.uniform(0, JITTER))


def sampler():
    """每秒采样，计算 QPS 并写入 history。"""
    global _last, _last_sample_time
    while not stop.is_set():
        time.sleep(1)
        now = time.time()
        with lock:
            total = sum(stats.values())
            succ = stats["success"]
        dt = max(now - _last_sample_time, 0.001)
        qps = (total - _last["total"]) / dt
        sqps = (succ - _last["success"]) / dt
        history.append([int(now * 1000), round(qps, 2), round(sqps, 2)])
        _last = {"total": total, "success": succ}
        _last_sample_time = now


def validate_proxy(p):
    """校验单个代理能否连通目标主机。"""
    try:
        if p.url.startswith("socks"):
            if not HAVE_SOCKS:
                p.active = False
                p.last_err = "缺少 PySocks"
                return
            try:
                open_via_socks("https://alpme.com/", p.url, None, 10)
                p.mark_ok()
            except Exception as e:
                p.mark_fail(str(e)[:80])
        else:
            opener = make_opener(p.url)
            req = urllib.request.Request("https://alpme.com/", headers=HEADERS)
            opener.open(req, timeout=10).close()
            p.mark_ok()
    except Exception as e:
        p.mark_fail(str(e)[:80])


def load_proxies(path):
    urls = []
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    urls.append(line)
    except FileNotFoundError:
        pass
    objs = [Proxy(u) for u in urls]
    if PROXY_TEST and objs:
        print(f"校验代理中（{len(objs)} 个）...")
        threads = []
        for p in objs:
            t = threading.Thread(target=validate_proxy, args=(p,), daemon=True)
            t.start()
            threads.append(t)
        for t in threads:
            t.join()
        alive = [p for p in objs if p.active]
        dead = [p for p in objs if not p.active]
        print(f"代理校验完成：可用 {len(alive)}，失效 {len(dead)}")
        for p in dead:
            print(f"  ✗ {p.url}  ({p.last_err})")
        objs = alive
    return objs


DASHBOARD_HTML = r"""<!DOCTYPE html>
<html lang="zh-CN"><head><meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>Alpme 注册仪表盘</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.1/dist/chart.umd.min.js"></script>
<style>
  :root{--bg:#0d1117;--card:#161b22;--bd:#30363d;--tx:#e6edf3;--mut:#8b949e;
        --ok:#3fb950;--warn:#d29922;--err:#f85149;--acc:#58a6ff;}
  *{box-sizing:border-box} body{margin:0;background:var(--bg);color:var(--tx);
    font-family:system-ui,-apple-system,"Segoe UI",Roboto,"PingFang SC","Microsoft YaHei",sans-serif}
  header{padding:14px 20px;border-bottom:1px solid var(--bd);display:flex;
    align-items:center;justify-content:space-between}
  header h1{font-size:16px;margin:0;font-weight:600}
  .wrap{padding:18px;display:grid;grid-template-columns:repeat(4,1fr);gap:14px;max-width:1200px;margin:0 auto}
  .card{background:var(--card);border:1px solid var(--bd);border-radius:10px;padding:16px}
  .card .label{color:var(--mut);font-size:12px;margin-bottom:6px}
  .card .val{font-size:26px;font-weight:700}
  .v-ok{color:var(--ok)} .v-warn{color:var(--warn)} .v-err{color:var(--err)} .v-acc{color:var(--acc)}
  .grid2{grid-column:1/-1;display:grid;grid-template-columns:2fr 1fr;gap:14px}
  .chart-box{background:var(--card);border:1px solid var(--bd);border-radius:10px;padding:14px}
  .chart-box h3{margin:0 0 10px;font-size:13px;color:var(--mut);font-weight:500}
  .controls{padding:0 18px 18px;max-width:1200px;margin:0 auto}
  button{background:var(--err);color:#fff;border:0;border-radius:8px;padding:8px 16px;
    font-size:13px;cursor:pointer}
  table{width:100%;border-collapse:collapse;font-size:12px}
  th,td{text-align:left;padding:6px 8px;border-bottom:1px solid var(--bd)}
  th{color:var(--mut);font-weight:500}
  .tag{display:inline-block;padding:1px 8px;border-radius:20px;font-size:11px}
  .tag-on{background:rgba(63,185,80,.15);color:var(--ok)}
  .tag-off{background:rgba(248,81,73,.15);color:var(--err)}
  .status{font-size:12px;color:var(--mut)}
</style></head>
<body>
<header><h1>Alpme 注册仪表盘</h1>
  <span class="status" id="runState">运行中</span></header>
<div class="wrap">
  <div class="card"><div class="label">总尝试</div><div class="val" id="k_total">0</div></div>
  <div class="card"><div class="label">成功注册</div><div class="val v-ok" id="k_success">0</div></div>
  <div class="card"><div class="label">当前 QPS</div><div class="val v-acc" id="k_qps">0</div></div>
  <div class="card"><div class="label">成功率</div><div class="val v-warn" id="k_rate">0%</div></div>
  <div class="grid2">
    <div class="chart-box"><h3>实时吞吐（请求/秒 · 成功/秒）</h3>
      <canvas id="qpsChart" height="90"></canvas></div>
    <div class="chart-box"><h3>状态分布</h3>
      <canvas id="pieChart" height="90"></canvas></div>
  </div>
  <div class="card" style="grid-column:1/-1">
    <h3 style="margin:0 0 10px;font-size:13px;color:var(--mut);font-weight:500">代理健康度</h3>
    <table><thead><tr><th>代理</th><th>状态</th><th>成功</th><th>连续失败</th><th>最近错误</th></tr></thead>
      <tbody id="proxyBody"><tr><td colspan="5" style="color:var(--mut)">无代理（使用本机 IP）</td></tr></tbody></table>
  </div>
</div>
<div class="controls"><button id="stopBtn">停止</button>
  <span class="status" id="msg"></span></div>
<script>
const cOk='#3fb950',cWarn='#d29922',cErr='#f85149',cAcc='#58a6ff',cMut='#8b949e';
const qctx=document.getElementById('qpsChart').getContext('2d');
const qpsChart=new Chart(qctx,{type:'line',data:{labels:[],datasets:[
  {label:'请求/秒',data:[],borderColor:cAcc,backgroundColor:'rgba(88,166,255,.12)',fill:true,tension:.3,pointRadius:0},
  {label:'成功/秒',data:[],borderColor:cOk,backgroundColor:'rgba(63,185,80,.12)',fill:true,tension:.3,pointRadius:0}]},
  options:{animation:false,responsive:true,scales:{x:{ticks:{color:cMut,maxTicksLimit:8},grid:{color:'#21262d'}},
    y:{ticks:{color:cMut,beginAtZero:true},grid:{color:'#21262d'}}},plugins:{legend:{labels:{color:cMut}}}}});
const pctx=document.getElementById('pieChart').getContext('2d');
const pieChart=new Chart(pctx,{type:'doughnut',data:{labels:['成功','已存在','限流','其他','异常'],
  datasets:[{data:[0,0,0,0,0],backgroundColor:[cOk,cMut,cWarn,cAcc,cErr]}]},
  options:{animation:false,plugins:{legend:{labels:{color:cMut,boxWidth:12}}}}});
function fmt(n){return n.toLocaleString()}
async function tick(){
  try{
    const r=await fetch('/api/stats',{cache:'no-store'});
    const d=await r.json();
    document.getElementById('k_total').textContent=fmt(d.totals.total);
    document.getElementById('k_success').textContent=fmt(d.totals.success);
    document.getElementById('k_qps').textContent=d.qps.toFixed(1);
    document.getElementById('k_rate').textContent=(d.success_rate*100).toFixed(1)+'%';
    const labels=d.history.map(h=>new Date(h[0]).toLocaleTimeString());
    qpsChart.data.labels=labels;
    qpsChart.data.datasets[0].data=d.history.map(h=>h[1]);
    qpsChart.data.datasets[1].data=d.history.map(h=>h[2]);
    qpsChart.update();
    pieChart.data.datasets[0].data=[d.totals.success,d.totals.exists,d.totals.ratelimit,d.totals.other,d.totals.error];
    pieChart.update();
    const pb=document.getElementById('proxyBody');
    if(!d.proxies.list.length){pb.innerHTML='<tr><td colspan="5" style="color:#8b949e">无代理（使用本机 IP）</td></tr>';}
    else{pb.innerHTML=d.proxies.list.map(p=>`<tr><td>${p.url}</td>
      <td><span class="tag ${p.active?'tag-on':'tag-off'}">${p.active?'可用':'失效'}</span></td>
      <td>${p.ok}</td><td>${p.fails}</td><td style="color:#8b949e">${p.last_err||'-'}</td></tr>`).join('');}
    document.getElementById('runState').textContent=d.running?'运行中':'已停止';
  }catch(e){}
}
setInterval(tick,1000);tick();
document.getElementById('stopBtn').onclick=async()=>{
  await fetch('/api/stop',{method:'POST'});
  document.getElementById('msg').textContent='已发送停止指令';
};
</script></body></html>"""


class Handler(BaseHTTPRequestHandler):
    def _send(self, code, body, ctype="application/json"):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path == "/" or self.path.startswith("/index"):
            self._send(200, DASHBOARD_HTML, "text/html; charset=utf-8")
        elif self.path == "/api/stats":
            with lock:
                s = dict(stats)
                plist = [p.to_dict() for p in proxies]
            total = sum(s.values())
            succ = s["success"]
            rate = (succ / total) if total else 0
            qps = history[-1][1] if history else 0
            data = {
                "totals": s, "total": total, "success_rate": rate, "qps": qps,
                "history": list(history),
                "proxies": {"total": len(plist),
                            "active": sum(1 for p in plist if p["active"]),
                            "list": plist},
                "running": not stop.is_set(),
            }
            self._send(200, json.dumps(data))
        else:
            self._send(404, "not found")

    def do_POST(self):
        if self.path == "/api/stop":
            stop.set()
            self._send(200, json.dumps({"ok": True}))
        else:
            self._send(404, "not found")

    def log_message(self, *a):
        pass


def run_server(port):
    srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    srv.serve_forever()


def main():
    global MAX_REGISTER, CONCURRENCY, OUTPUT_FILE, proxies
    ap = argparse.ArgumentParser(description="Alpme 注册脚本 v2")
    ap.add_argument("-n", "--count", type=int, default=MAX_REGISTER, help="注册数量，0=无限")
    ap.add_argument("-c", "--concurrency", type=int, default=CONCURRENCY, help="并发线程数")
    ap.add_argument("-o", "--output", default=OUTPUT_FILE, help="成功记录文件")
    ap.add_argument("-p", "--proxies", default=PROXIES_FILE, help="代理池文件")
    ap.add_argument("--port", type=int, default=DASHBOARD_PORT, help="仪表盘端口")
    ap.add_argument("--no-dashboard", action="store_true", help="关闭仪表盘")
    args = ap.parse_args()

    MAX_REGISTER = args.count
    CONCURRENCY = max(1, args.concurrency)
    OUTPUT_FILE = args.output

    proxies = load_proxies(args.proxies)
    mode = "无限循环(网页停止/Ctrl+C)" if MAX_REGISTER == 0 else f"目标 {MAX_REGISTER} 个"
    print("=== Alpme 注册 v2 ===")
    print(f"接口   : {TARGET_URL}")
    print(f"模式   : {mode} | 并发 {CONCURRENCY}")
    print(f"代理   : {'无(本机IP)' if not proxies else f'{len(proxies)} 个可用'}"
          + ("" if HAVE_SOCKS else "  (socks5 需要 pip install pysocks)"))
    print(f"成功记录: {OUTPUT_FILE}")

    server_thread = None
    if not args.no_dashboard:
        server_thread = threading.Thread(target=run_server, args=(args.port,), daemon=True)
        server_thread.start()
        print(f"仪表盘 : http://127.0.0.1:{args.port}  (已打开浏览器)")

    threading.Thread(target=sampler, daemon=True).start()

    try:
        threads = []
        for _ in range(CONCURRENCY):
            th = threading.Thread(target=worker, daemon=True)
            th.start()
            threads.append(th)
        if MAX_REGISTER > 0:
            for th in threads:
                th.join()
            print("\n注册阶段完成。仪表盘仍在运行，按 Ctrl+C 退出查看。")
            try:
                while True:
                    time.sleep(1)
            except KeyboardInterrupt:
                stop.set()
        else:
            print("无限模式运行中，Ctrl+C 停止。")
            try:
                while not stop.is_set():
                    time.sleep(0.5)
            except KeyboardInterrupt:
                stop.set()
    except KeyboardInterrupt:
        stop.set()

    with lock:
        s = dict(stats)
    total = sum(s.values())
    print(f"\n=== 完成 ===  总 {total} | 成功 {s['success']} | 已存在 {s['exists']} "
          f"| 限流 {s['ratelimit']} | 其他 {s['other']} | 异常 {s['error']}")
    if s["ratelimit"] and not proxies:
        print("⚠️ 大量限流：单 IP 已达上限。想继续注册请往 proxies.txt 填代理。")


if __name__ == "__main__":
    main()
