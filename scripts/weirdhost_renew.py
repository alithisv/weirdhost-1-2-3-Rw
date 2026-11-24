#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import sys
import time
import asyncio
import aiohttp
import base64
import random
import re
import subprocess
import json
import socket
import tempfile
import urllib.request
from datetime import datetime
from urllib.parse import unquote, urlparse, parse_qs

from seleniumbase import SB

try:
    from nacl import encoding, public
    NACL_AVAILABLE = True
except ImportError:
    NACL_AVAILABLE = False

sys.stdout.reconfigure(line_buffering=True)

BASE_URL = "https://hub.weirdhost.xyz/server/"
API_BASE_URL = "https://hub.weirdhost.xyz/api/client"
DOMAIN = "hub.weirdhost.xyz"
MAX_COOKIE_COUNT = 10

RENEWAL_BUTTON_SELECTORS = [
    "//button//span[contains(text(), '연장하기')]/parent::button",
    "//button[contains(text(), '연장하기')]",
    "//button//span[contains(text(), '시간추가')]/parent::button",
    "//button[contains(text(), '시간추가')]",
    "//button//span[contains(text(), '시간 추가')]/parent::button",
    "//button[contains(text(), '시간 추가')]",
]


# ============================================================
#  工具函数
# ============================================================

def mask_sensitive(text, show_chars=3):
    if not text:
        return "***"
    text = str(text)
    if len(text) <= show_chars * 2:
        return "*" * len(text)
    return text[:show_chars] + "*" * (len(text) - show_chars * 2) + text[-show_chars:]


def mask_email(email):
    if not email or "@" not in email:
        return mask_sensitive(email)
    local, domain = email.rsplit("@", 1)
    if len(local) <= 2:
        masked_local = "*" * len(local)
    else:
        masked_local = local[0] + "*" * (len(local) - 2) + local[-1]
    return f"{masked_local}@{domain}"


def mask_remark(remark):
    if not remark:
        return "***"
    if "@" in remark:
        return mask_email(remark)
    return mask_sensitive(remark)


def mask_server_id(server_id):
    if not server_id:
        return "***"
    if len(server_id) <= 4:
        return "*" * len(server_id)
    return server_id[:2] + "*" * (len(server_id) - 4) + server_id[-2:]


def mask_ip(ip):
    if not ip:
        return "Unknown"
    if "." in ip:
        parts = ip.split(".")
        if len(parts) == 4:
            return f"{parts[0]}.{parts[1]}.*.*"
    if ":" in ip:
        parts = ip.split(":")
        return ":".join(parts[:2]) + ":*:*"
    return mask_sensitive(ip, 2)


def random_delay(min_sec=0.5, max_sec=2.0):
    time.sleep(random.uniform(min_sec, max_sec))


def calculate_remaining_time(expiry_str):
    try:
        for fmt in ["%Y-%m-%d %H:%M:%S", "%Y-%m-%d"]:
            try:
                expiry_dt = datetime.strptime(expiry_str.strip(), fmt)
                diff = expiry_dt - datetime.now()
                if diff.total_seconds() < 0:
                    return "已过期"
                days = diff.days
                hours = diff.seconds // 3600
                minutes = (diff.seconds % 3600) // 60
                parts = []
                if days > 0:
                    parts.append(f"{days}天")
                if hours > 0:
                    parts.append(f"{hours}小时")
                if minutes > 0 and days == 0:
                    parts.append(f"{minutes}分钟")
                return " ".join(parts) if parts else "不到1分钟"
            except ValueError:
                continue
        return "无法解析"
    except Exception:
        return "计算失败"


def parse_expiry_to_datetime(expiry_str):
    if not expiry_str or expiry_str == "Unknown":
        return None
    for fmt in ["%Y-%m-%d %H:%M:%S", "%Y-%m-%d"]:
        try:
            return datetime.strptime(expiry_str.strip(), fmt)
        except ValueError:
            continue
    return None


def get_remaining_days(expiry_str):
    expiry_dt = parse_expiry_to_datetime(expiry_str)
    if not expiry_dt:
        return None
    diff = expiry_dt - datetime.now()
    return diff.total_seconds() / 86400


def format_remaining_days(rd):
    if rd is None:
        return "?"
    return f"{rd:.1f}"


def parse_weirdhost_cookie(cookie_str):
    if not cookie_str:
        return (None, None)
    cookie_str = cookie_str.strip()
    if "=" in cookie_str:
        parts = cookie_str.split("=", 1)
        if len(parts) == 2:
            return (parts[0].strip(), unquote(parts[1].strip()))
    return (None, None)


def build_server_url(server_id):
    if not server_id:
        return None
    server_id = server_id.strip()
    return server_id if server_id.startswith("http") else f"{BASE_URL}{server_id}"


# ============================================================
#  sing-box 节点解析与本地代理管理
# ============================================================

def _b64_decode(data):
    data = data.strip().replace("-", "+").replace("_", "/")
    data += "=" * (-len(data) % 4)
    return base64.b64decode(data).decode("utf-8", errors="ignore")


def _get_qs_first(qs, key, default=""):
    vals = qs.get(key)
    return vals[0] if vals else default


def _parse_bool(val):
    return str(val).strip().lower() in ("1", "true", "yes", "on")


def _build_transport(net_type, path="", host="", service_name=""):
    net_type = (net_type or "tcp").lower()
    if net_type == "ws":
        t = {"type": "ws", "path": path or "/"}
        if host:
            t["headers"] = {"Host": host}
        return t
    if net_type == "grpc":
        return {"type": "grpc", "service_name": service_name or path or ""}
    if net_type == "httpupgrade":
        t = {"type": "httpupgrade", "path": path or "/"}
        if host:
            t["host"] = host
        return t
    if net_type in ("h2", "http"):
        t = {"type": "http", "path": path or "/"}
        if host:
            t["host"] = [h.strip() for h in host.split(",") if h.strip()]
        return t
    return None


def parse_proxy_uri(uri):
    """解析常见代理节点链接为 sing-box outbound 配置，返回 (outbound_dict, label)"""
    if not uri:
        return None, None
    uri = uri.strip()
    if not uri or uri.startswith("#"):
        return None, None

    scheme = uri.split("://", 1)[0].lower() if "://" in uri else ""

    try:
        # 1. Hysteria2: hy2:// 或 hysteria2://
        if scheme in ("hy2", "hysteria2"):
            parsed = urlparse(uri)
            qs = parse_qs(parsed.query)
            host = parsed.hostname
            port = parsed.port or 443
            password = unquote(parsed.username or "")
            if parsed.password:
                password = f"{password}:{unquote(parsed.password)}"
            sni = _get_qs_first(qs, "sni") or _get_qs_first(qs, "peer") or host
            insecure = _parse_bool(_get_qs_first(qs, "insecure") or _get_qs_first(qs, "allowInsecure"))
            alpn = _get_qs_first(qs, "alpn")

            outbound = {
                "type": "hysteria2",
                "tag": "proxy",
                "server": host,
                "server_port": int(port),
                "password": password,
                "tls": {
                    "enabled": True,
                    "server_name": sni,
                    "insecure": insecure,
                },
            }
            if alpn:
                outbound["tls"]["alpn"] = [a.strip() for a in alpn.split(",") if a.strip()]

            obfs = _get_qs_first(qs, "obfs")
            obfs_pw = _get_qs_first(qs, "obfs-password")
            if obfs and obfs.lower() != "none":
                outbound["obfs"] = {"type": obfs, "password": obfs_pw}

            label = unquote(parsed.fragment) or f"hy2-{mask_sensitive(host, 2)}"
            return outbound, label

        # 2. VLESS: vless://
        if scheme == "vless":
            parsed = urlparse(uri)
            qs = parse_qs(parsed.query)
            host = parsed.hostname
            port = parsed.port or 443
            uuid = unquote(parsed.username or "")
            security = (_get_qs_first(qs, "security") or "none").lower()
            sni = _get_qs_first(qs, "sni") or _get_qs_first(qs, "peer") or host
            fp = _get_qs_first(qs, "fp") or "chrome"
            flow = _get_qs_first(qs, "flow")
            net_type = _get_qs_first(qs, "type") or "tcp"
            path = unquote(_get_qs_first(qs, "path"))
            ws_host = _get_qs_first(qs, "host")
            service_name = _get_qs_first(qs, "serviceName")
            alpn = _get_qs_first(qs, "alpn")
            insecure = _parse_bool(_get_qs_first(qs, "allowInsecure") or _get_qs_first(qs, "insecure"))

            outbound = {
                "type": "vless",
                "tag": "proxy",
                "server": host,
                "server_port": int(port),
                "uuid": uuid,
            }
            if flow:
                outbound["flow"] = flow

            if security == "reality":
                pbk = _get_qs_first(qs, "pbk")
                sid = _get_qs_first(qs, "sid")
                outbound["tls"] = {
                    "enabled": True,
                    "server_name": sni,
                    "utls": {"enabled": True, "fingerprint": fp},
                    "reality": {"enabled": True, "public_key": pbk, "short_id": sid},
                }
            elif security == "tls":
                tls_cfg = {
                    "enabled": True,
                    "server_name": sni,
                    "insecure": insecure,
                }
                if fp:
                    tls_cfg["utls"] = {"enabled": True, "fingerprint": fp}
                if alpn:
                    tls_cfg["alpn"] = [a.strip() for a in alpn.split(",") if a.strip()]
                outbound["tls"] = tls_cfg

            transport = _build_transport(net_type, path, ws_host, service_name)
            if transport:
                outbound["transport"] = transport

            label = unquote(parsed.fragment) or f"vless-{mask_sensitive(host, 2)}"
            return outbound, label

        # 3. VMess: vmess://
        if scheme == "vmess":
            raw_b64 = uri[len("vmess://"):].split("#", 1)[0]
            cfg = json.loads(_b64_decode(raw_b64))
            host = cfg.get("add", "")
            port = int(cfg.get("port", 443))
            uuid = cfg.get("id", "")
            aid = int(cfg.get("aid", 0) or 0)
            scy = cfg.get("scy") or "auto"
            net_type = cfg.get("net") or "tcp"
            ws_host = cfg.get("host", "")
            path = cfg.get("path", "")
            tls_val = str(cfg.get("tls", "")).lower()
            sni = cfg.get("sni") or ws_host or host
            fp = cfg.get("fp", "")
            alpn = cfg.get("alpn", "")

            outbound = {
                "type": "vmess",
                "tag": "proxy",
                "server": host,
                "server_port": port,
                "uuid": uuid,
                "security": scy,
                "alter_id": aid,
            }
            if tls_val in ("tls", "1", "true"):
                tls_cfg = {
                    "enabled": True,
                    "server_name": sni,
                    "insecure": True,
                }
                if fp:
                    tls_cfg["utls"] = {"enabled": True, "fingerprint": fp}
                if alpn:
                    tls_cfg["alpn"] = [a.strip() for a in alpn.split(",") if a.strip()]
                outbound["tls"] = tls_cfg

            transport = _build_transport(net_type, path, ws_host, path)
            if transport:
                outbound["transport"] = transport

            label = cfg.get("ps") or f"vmess-{mask_sensitive(host, 2)}"
            return outbound, label

        # 4. Trojan: trojan://
        if scheme == "trojan":
            parsed = urlparse(uri)
            qs = parse_qs(parsed.query)
            host = parsed.hostname
            port = parsed.port or 443
            password = unquote(parsed.username or "")
            sni = _get_qs_first(qs, "sni") or _get_qs_first(qs, "peer") or host
            fp = _get_qs_first(qs, "fp")
            alpn = _get_qs_first(qs, "alpn")
            insecure = _parse_bool(_get_qs_first(qs, "allowInsecure") or _get_qs_first(qs, "insecure"))
            net_type = _get_qs_first(qs, "type") or "tcp"
            path = unquote(_get_qs_first(qs, "path"))
            ws_host = _get_qs_first(qs, "host")
            service_name = _get_qs_first(qs, "serviceName")

            tls_cfg = {
                "enabled": True,
                "server_name": sni,
                "insecure": insecure,
            }
            if fp:
                tls_cfg["utls"] = {"enabled": True, "fingerprint": fp}
            if alpn:
                tls_cfg["alpn"] = [a.strip() for a in alpn.split(",") if a.strip()]

            outbound = {
                "type": "trojan",
                "tag": "proxy",
                "server": host,
                "server_port": int(port),
                "password": password,
                "tls": tls_cfg,
            }
            transport = _build_transport(net_type, path, ws_host, service_name)
            if transport:
                outbound["transport"] = transport

            label = unquote(parsed.fragment) or f"trojan-{mask_sensitive(host, 2)}"
            return outbound, label

        # 5. Shadowsocks: ss://
        if scheme == "ss":
            body = uri[len("ss://"):]
            frag = ""
            if "#" in body:
                body, frag = body.split("#", 1)
            body = body.split("?", 1)[0]
            if "@" in body:
                userinfo, hostport = body.rsplit("@", 1)
                if ":" not in userinfo:
                    userinfo = _b64_decode(userinfo)
                method, password = userinfo.split(":", 1)
                parsed_hp = urlparse(f"//{hostport}")
                host, port = parsed_hp.hostname, parsed_hp.port
            else:
                decoded = _b64_decode(body)
                userinfo, hostport = decoded.rsplit("@", 1)
                method, password = userinfo.split(":", 1)
                parsed_hp = urlparse(f"//{hostport}")
                host, port = parsed_hp.hostname, parsed_hp.port

            outbound = {
                "type": "shadowsocks",
                "tag": "proxy",
                "server": host,
                "server_port": int(port),
                "method": unquote(method),
                "password": unquote(password),
            }
            label = unquote(frag) or f"ss-{mask_sensitive(host, 2)}"
            return outbound, label

        # 6. SOCKS5 / HTTP: socks5:// socks:// http:// https://
        if scheme in ("socks5", "socks", "http", "https"):
            parsed = urlparse(uri)
            host = parsed.hostname
            port = parsed.port or (1080 if "socks" in scheme else 8080)
            outbound = {
                "type": "socks" if "socks" in scheme else "http",
                "tag": "proxy",
                "server": host,
                "server_port": int(port),
            }
            if parsed.username:
                outbound["username"] = unquote(parsed.username)
            if parsed.password:
                outbound["password"] = unquote(parsed.password)
            if scheme == "https":
                outbound["tls"] = {"enabled": True, "server_name": host}

            label = unquote(parsed.fragment) or f"{scheme}-{mask_sensitive(host, 2)}"
            return outbound, label

    except Exception as e:
        print(f"[ERROR] 代理节点解析失败 ({scheme}): {e}")
        return None, None

    print(f"[WARN] 不支持的代理协议: {scheme}")
    return None, None


def _find_free_port():
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


class SingBoxProxyManager:
    """为单个账号启动独立的 sing-box 本地 mixed 代理"""

    def __init__(self, proxy_uri):
        self.proxy_uri = proxy_uri
        self.process = None
        self.config_path = None
        self.local_port = None
        self.label = ""
        self.egress_ip = None

    def start(self, verify_timeout=12):
        outbound, label = parse_proxy_uri(self.proxy_uri)
        if not outbound:
            return False, "节点链接解析失败"

        self.label = label
        self.local_port = _find_free_port()

        config = {
            "log": {"level": "warn", "timestamp": False},
            "inbounds": [
                {
                    "type": "mixed",
                    "tag": "mixed-in",
                    "listen": "127.0.0.1",
                    "listen_port": self.local_port,
                }
            ],
            "outbounds": [
                outbound,
                {"type": "direct", "tag": "direct"},
            ],
            "route": {
                "final": "proxy"
            },
        }

        fd, self.config_path = tempfile.mkstemp(prefix="singbox_", suffix=".json")
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(config, f, ensure_ascii=False, indent=2)

        try:
            self.process = subprocess.Popen(
                ["sing-box", "run", "-c", self.config_path],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
        except FileNotFoundError:
            self.stop()
            return False, "未找到 sing-box 可执行文件，请检查工作流安装步骤"
        except Exception as e:
            self.stop()
            return False, f"sing-box 启动异常: {e}"

        # 等待本地端口就绪
        port_ready = False
        for _ in range(30):
            if self.process.poll() is not None:
                err_out = (self.process.stderr.read() or "").strip()[:300]
                self.stop()
                return False, f"sing-box 启动后立即退出: {err_out}"
            try:
                with socket.create_connection(("127.0.0.1", self.local_port), timeout=0.3):
                    port_ready = True
                    break
            except OSError:
                time.sleep(0.2)

        if not port_ready:
            self.stop()
            return False, "sing-box 本地端口监听超时"

        # 连通性与出口 IP 预检
        proxy_url = f"http://127.0.0.1:{self.local_port}"
        opener = urllib.request.build_opener(
            urllib.request.ProxyHandler({"http": proxy_url, "https": proxy_url})
        )
        check_urls = [
            "https://api.ipify.org",
            "https://ifconfig.me/ip",
            "http://ip-api.com/line/?fields=query",
        ]
        last_err = ""
        for url in check_urls:
            try:
                req = urllib.request.Request(url, headers={"User-Agent": "curl/8.0"})
                with opener.open(req, timeout=verify_timeout) as resp:
                    ip = resp.read().decode("utf-8", errors="ignore").strip().splitlines()[0]
                    if ip:
                        self.egress_ip = ip
                        return True, ip
            except Exception as e:
                last_err = str(e)
                continue

        self.stop()
        return False, f"节点连通性测试失败: {last_err[:120]}"

    def stop(self):
        if self.process:
            try:
                self.process.terminate()
                self.process.wait(timeout=3)
            except Exception:
                try:
                    self.process.kill()
                except Exception:
                    pass
            self.process = None

        if self.config_path and os.path.exists(self.config_path):
            try:
                os.remove(self.config_path)
            except Exception:
                pass
            self.config_path = None


def load_proxy_pool():
    raw = os.environ.get("PROXY_NODES", "").strip()
    if not raw:
        return []
    return [line.strip() for line in raw.splitlines() if line.strip() and not line.strip().startswith("#")]


def get_proxy_for_account(account_index, proxy_pool):
    """优先读取 PROXY_NODE_{i}，其次从 PROXY_NODES 按序号轮询分配"""
    dedicated = os.environ.get(f"PROXY_NODE_{account_index}", "").strip()
    if dedicated:
        return dedicated, f"PROXY_NODE_{account_index}"
    if proxy_pool:
        node = proxy_pool[(account_index - 1) % len(proxy_pool)]
        return node, f"PROXY_NODES[{(account_index - 1) % len(proxy_pool) + 1}]"
    return None, None


# ============================================================
#  账号自动检测
# ============================================================

def parse_account_config(raw_value):
    if not raw_value:
        return None
    raw_value = raw_value.strip()

    remark = ""
    cookie_str = ""

    if "-----" in raw_value:
        parts = raw_value.split("-----", 1)
        remark = parts[0].strip()
        cookie_str = parts[1].strip() if len(parts) > 1 else ""
    else:
        cookie_str = raw_value

    if not cookie_str or "=" not in cookie_str:
        return None

    cookie_name, cookie_value = parse_weirdhost_cookie(cookie_str)
    if not cookie_name or not cookie_name.startswith("remember_web"):
        return None

    return {
        "remark": remark,
        "cookie_str": cookie_str,
        "cookie_name": cookie_name,
        "cookie_value": cookie_value,
    }


def detect_accounts():
    accounts = []
    proxy_pool = load_proxy_pool()
    if proxy_pool:
        print(f"[INFO] 检测到公共节点池 PROXY_NODES: 共 {len(proxy_pool)} 个节点")

    for i in range(1, MAX_COOKIE_COUNT + 1):
        env_name = f"WEIRDHOST_COOKIE_{i}"
        raw = os.environ.get(env_name, "").strip()
        if not raw:
            continue

        config = parse_account_config(raw)
        if not config:
            print(f"[WARN] {env_name} 格式错误，跳过")
            print("       正确格式: 备注-----remember_web_xxx=yyy")
            continue

        remark = config["remark"] or f"账号{i}"
        proxy_uri, proxy_source = get_proxy_for_account(i, proxy_pool)
        proxy_hint = f" | 代理: {proxy_source}" if proxy_uri else " | 代理: 直连"
        print(f"[INFO] 检测到 {env_name}: {mask_remark(remark)}{proxy_hint}")

        accounts.append({
            "index": i,
            "cookie_env": env_name,
            "remark": remark,
            "cookie_str": config["cookie_str"],
            "cookie_name": config["cookie_name"],
            "cookie_value": config["cookie_value"],
            "proxy_uri": proxy_uri,
            "proxy_source": proxy_source,
        })

    return accounts


# ============================================================
#  Telegram 通知
# ============================================================

async def tg_notify(message):
    token = os.environ.get("TG_BOT_TOKEN")
    chat_id = os.environ.get("TG_CHAT_ID")
    if not token or not chat_id:
        print("[INFO] 未配置 TG_BOT_TOKEN 或 TG_CHAT_ID，跳过通知")
        return
    async with aiohttp.ClientSession() as session:
        try:
            await session.post(
                f"https://api.telegram.org/bot{token}/sendMessage",
                json={"chat_id": chat_id, "text": message, "parse_mode": "HTML"}
            )
        except Exception as e:
            print(f"[ERROR] TG 发送失败: {e}")


async def tg_notify_photo(photo_path, caption=""):
    token = os.environ.get("TG_BOT_TOKEN")
    chat_id = os.environ.get("TG_CHAT_ID")
    if not token or not chat_id or not os.path.exists(photo_path):
        return
    async with aiohttp.ClientSession() as session:
        try:
            with open(photo_path, "rb") as f:
                data = aiohttp.FormData()
                data.add_field("chat_id", chat_id)
                data.add_field("photo", f, filename=os.path.basename(photo_path))
                data.add_field("caption", caption)
                data.add_field("parse_mode", "HTML")
                await session.post(f"https://api.telegram.org/bot{token}/sendPhoto", data=data)
        except Exception as e:
            print(f"[ERROR] TG 图片发送失败: {e}")


def sync_tg_notify(message):
    asyncio.run(tg_notify(message))


def sync_tg_notify_photo(photo_path, caption=""):
    asyncio.run(tg_notify_photo(photo_path, caption))


# ============================================================
#  GitHub Secret
# ============================================================

def encrypt_secret(public_key, secret_value):
    pk = public.PublicKey(public_key.encode("utf-8"), encoding.Base64Encoder())
    sealed_box = public.SealedBox(pk)
    encrypted = sealed_box.encrypt(secret_value.encode("utf-8"))
    return base64.b64encode(encrypted).decode("utf-8")


async def update_github_secret(secret_name, secret_value):
    repo_token = os.environ.get("REPO_TOKEN", "").strip()
    repository = os.environ.get("GITHUB_REPOSITORY", "").strip()
    if not repo_token or not repository or not NACL_AVAILABLE:
        return False
    headers = {
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {repo_token}",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    async with aiohttp.ClientSession() as session:
        try:
            pk_url = f"https://api.github.com/repos/{repository}/actions/secrets/public-key"
            async with session.get(pk_url, headers=headers) as resp:
                if resp.status != 200:
                    return False
                pk_data = await resp.json()
            encrypted_value = encrypt_secret(pk_data["key"], secret_value)
            secret_url = f"https://api.github.com/repos/{repository}/actions/secrets/{secret_name}"
            async with session.put(secret_url, headers=headers, json={
                "encrypted_value": encrypted_value, "key_id": pk_data["key_id"]
            }) as resp:
                return resp.status in (201, 204)
        except Exception:
            return False


# ============================================================
#  基于 Selenium 的浏览器内 API 调用
# ============================================================

def api_fetch_json(sb, url, xsrf_token=None):
    headers = {
        "Accept": "application/json",
        "X-Requested-With": "XMLHttpRequest",
        "Referer": f"https://{DOMAIN}/",
    }
    if xsrf_token:
        headers["X-XSRF-TOKEN"] = xsrf_token

    script = """
        var done = arguments[arguments.length - 1];
        fetch(arguments[0], {
            headers: arguments[1]
        })
        .then(resp => {
            if (resp.status === 401) return {_error: 'unauthorized'};
            return resp.json();
        })
        .then(data => done(data))
        .catch(err => done({_error: err.toString()}));
    """
    result = sb.driver.execute_async_script(script, url, headers)
    if isinstance(result, dict) and "_error" in result:
        print(f"[ERROR]   fetch 失败: {result['_error']}")
        return None
    return result


def get_xsrf_token_from_cookies(sb):
    try:
        cookies = sb.get_cookies()
        for c in cookies:
            if c.get("name") == "XSRF-TOKEN":
                return unquote(c.get("value", ""))
    except Exception:
        pass
    return None


# ============================================================
#  Turnstile 处理（登录阶段）
# ============================================================

def ts_exists(sb):
    try:
        return sb.execute_script("""
            return !!(
                document.querySelector('input[name="cf-turnstile-response"]') ||
                document.querySelector('.cf-turnstile') ||
                document.querySelector('iframe[src*="challenges.cloudflare.com"]')
            );
        """)
    except Exception:
        return False


def ts_solved(sb):
    try:
        return sb.execute_script("""
            var i = document.querySelector('input[name="cf-turnstile-response"]');
            return i && i.value && i.value.length > 20;
        """)
    except Exception:
        return False


def expand_turnstile(sb):
    try:
        sb.execute_script("""
            (function() {
                var ti = document.querySelector('input[name="cf-turnstile-response"]');
                if (!ti) return;
                var el = ti;
                for (var i = 0; i < 20; i++) {
                    el = el.parentElement;
                    if (!el) break;
                    var s = window.getComputedStyle(el);
                    if (s.overflow === 'hidden') el.style.overflow = 'visible';
                    el.style.minWidth = 'max-content';
                }
                document.querySelectorAll('.cf-turnstile').forEach(function(c) {
                    c.style.overflow = 'visible';
                    c.style.width = '300px';
                    c.style.height = '65px';
                });
                document.querySelectorAll('iframe').forEach(function(f) {
                    if (f.src && f.src.includes('challenges.cloudflare.com')) {
                        f.style.width = '300px';
                        f.style.height = '65px';
                        f.style.visibility = 'visible';
                        f.style.opacity = '1';
                    }
                });
            })();
        """)
    except Exception:
        pass


def focus_turnstile_area(sb):
    try:
        sb.execute_script("""
            const selectors = [
                '.cf-turnstile',
                'iframe[src*="challenges.cloudflare"]',
                'input[name="cf-turnstile-response"]',
                'label.cb-lb',
                '.cb-lb',
                'input[type="checkbox"]'
            ];
            for (const selector of selectors) {
                const el = document.querySelector(selector);
                if (el) {
                    el.scrollIntoView({block: 'center', inline: 'center'});
                    return true;
                }
            }
            window.scrollTo(0, Math.max(0, document.body.scrollHeight * 0.45));
            return false;
        """)
        time.sleep(0.5)
    except Exception:
        pass


def handle_turnstile(sb, timeout=120):
    if not ts_exists(sb):
        return True
    print("[INFO]   检测到 Turnstile，尝试自动解决...")
    try:
        sb.uc_gui_handle_captcha()
        if ts_solved(sb) or not ts_exists(sb):
            print("[INFO]   自动解决成功 ✅")
            return True
    except Exception:
        pass

    print("[INFO]   自动解决未完成，进入手动处理 ...")
    start = time.time()
    last_action = 0
    while time.time() - start < timeout:
        if ts_solved(sb):
            print("[INFO]   Turnstile 令牌已生成 ✅")
            return True
        if not ts_exists(sb):
            print("[INFO]   Turnstile 元素消失，可能已通过")
            return True

        expand_turnstile(sb)
        focus_turnstile_area(sb)

        now = time.time()
        if now - last_action > 4:
            clicked = False
            try:
                iframes = sb.driver.find_elements("css selector", "iframe")
                for iframe in iframes:
                    try:
                        sb.driver.switch_to.frame(iframe)
                        for sel in ["input[type='checkbox']", "label.cb-lb", ".cb-lb input"]:
                            try:
                                elem = sb.driver.find_element("css selector", sel)
                                if elem.is_displayed():
                                    elem.click()
                                    clicked = True
                                    print(f"[INFO]   在 iframe 中点击了 {sel}")
                                    break
                            except Exception:
                                pass
                        if clicked:
                            break
                    except Exception:
                        pass
                    finally:
                        sb.driver.switch_to.default_content()
            except Exception as e:
                print(f"[WARN]   iframe 点击异常: {e}")
            finally:
                try:
                    sb.driver.switch_to.default_content()
                except Exception:
                    pass

            if not clicked:
                try:
                    sb.uc_gui_click_captcha()
                    print("[INFO]   已调用 uc_gui_click_captcha（备用）")
                except Exception:
                    pass
            last_action = now

        time.sleep(2)

    print("[ERROR]  Turnstile 手动处理超时 ❌")
    return False


# ============================================================
#  Turnstile 处理（续期阶段）
# ============================================================

def check_turnstile_exists_popup(sb):
    try:
        return sb.execute_script(
            'return document.querySelector(\'input[name="cf-turnstile-response"]\') !== null;'
        )
    except Exception:
        return False


def check_turnstile_solved_popup(sb):
    try:
        return sb.execute_script("""
            var input = document.querySelector('input[name="cf-turnstile-response"]');
            return input && input.value && input.value.length > 20;
        """)
    except Exception:
        return False


EXPAND_POPUP_JS = """
(function() {
    var turnstileInput = document.querySelector('input[name="cf-turnstile-response"]');
    if (!turnstileInput) return 'no turnstile input';
    var el = turnstileInput;
    for (var i = 0; i < 20; i++) {
        el = el.parentElement;
        if (!el) break;
        var style = window.getComputedStyle(el);
        if (style.overflow === 'hidden' || style.overflowX === 'hidden' || style.overflowY === 'hidden') {
            el.style.overflow = 'visible';
        }
        el.style.minWidth = 'max-content';
    }
    var turnstileContainers = document.querySelectorAll('[class*="sc-fKFyDc"], [class*="nwOmR"]');
    turnstileContainers.forEach(function(container) {
        container.style.overflow = 'visible';
        container.style.width = '300px';
        container.style.minWidth = '300px';
        container.style.height = '65px';
    });
    var iframes = document.querySelectorAll('iframe');
    iframes.forEach(function(iframe) {
        if (iframe.src && iframe.src.includes('challenges.cloudflare.com')) {
            iframe.style.width = '300px';
            iframe.style.height = '65px';
            iframe.style.minWidth = '300px';
            iframe.style.visibility = 'visible';
            iframe.style.opacity = '1';
        }
    });
    return 'done';
})();
"""


def get_turnstile_checkbox_coords(sb):
    try:
        return sb.execute_script("""
            var iframes = document.querySelectorAll('iframe');
            for (var i = 0; i < iframes.length; i++) {
                var src = iframes[i].src || '';
                if (src.includes('cloudflare') || src.includes('turnstile')) {
                    var rect = iframes[i].getBoundingClientRect();
                    if (rect.width > 0 && rect.height > 0) {
                        return {x:rect.x, y:rect.y, width:rect.width, height:rect.height,
                                click_x:Math.round(rect.x+30), click_y:Math.round(rect.y+rect.height/2)};
                    }
                }
            }
            var input = document.querySelector('input[name="cf-turnstile-response"]');
            if (input) {
                var container = input.parentElement;
                for (var j = 0; j < 5; j++) {
                    if (!container) break;
                    var rect = container.getBoundingClientRect();
                    if (rect.width > 100 && rect.height > 30) {
                        return {x:rect.x, y:rect.y, width:rect.width, height:rect.height,
                                click_x:Math.round(rect.x+30), click_y:Math.round(rect.y+rect.height/2)};
                    }
                    container = container.parentElement;
                }
            }
            return null;
        """)
    except Exception:
        return None


def activate_browser_window():
    try:
        result = subprocess.run(
            ["xdotool", "search", "--onlyvisible", "--class", "chrome"],
            capture_output=True, text=True, timeout=3
        )
        window_ids = result.stdout.strip().split('\n')
        if window_ids and window_ids[0]:
            subprocess.run(
                ["xdotool", "windowactivate", window_ids[0]],
                timeout=2, stderr=subprocess.DEVNULL
            )
            time.sleep(0.2)
            return True
    except Exception:
        pass
    return False


def xdotool_click(x, y):
    x, y = int(x), int(y)
    activate_browser_window()
    try:
        subprocess.run(["xdotool", "mousemove", str(x), str(y)], timeout=2, stderr=subprocess.DEVNULL)
        time.sleep(0.15)
        subprocess.run(["xdotool", "click", "1"], timeout=2, stderr=subprocess.DEVNULL)
        return True
    except Exception:
        pass
    try:
        os.system(f"xdotool mousemove {x} {y} click 1 2>/dev/null")
        return True
    except Exception:
        return False


def click_turnstile_checkbox(sb):
    coords = get_turnstile_checkbox_coords(sb)
    if not coords:
        print("[WARN] 无法获取 Turnstile 坐标")
        return False
    try:
        window_info = sb.execute_script("""
            return {screenX:window.screenX||0, screenY:window.screenY||0,
                    outerHeight:window.outerHeight, innerHeight:window.innerHeight};
        """)
        chrome_bar_height = window_info["outerHeight"] - window_info["innerHeight"]
        abs_x = coords["click_x"] + window_info["screenX"]
        abs_y = coords["click_y"] + window_info["screenY"] + chrome_bar_height
        return xdotool_click(abs_x, abs_y)
    except Exception as e:
        print(f"[ERROR] 坐标计算失败: {e}")
        return False


def check_result_popup(sb):
    try:
        return sb.execute_script("""
            var buttons = document.querySelectorAll('button');
            var hasNextBtn = false;
            for (var i = 0; i < buttons.length; i++) {
                if (buttons[i].innerText.includes('NEXT') || buttons[i].innerText.includes('Next')) {
                    hasNextBtn = true; break;
                }
            }
            var bodyText = document.body.innerText || '';
            var hasSuccessTitle = bodyText.includes('Success');
            var hasSuccessContent = bodyText.includes('성공') || bodyText.includes('갱신') || bodyText.includes('연장');
            var hasCooldown = bodyText.includes('아직') || bodyText.includes('Error');
            if (hasNextBtn || hasSuccessTitle) {
                if (hasCooldown && bodyText.includes('아직')) return 'cooldown';
                if (hasSuccessTitle && hasSuccessContent) return 'success';
                if (hasNextBtn) {
                    if (hasCooldown) return 'cooldown';
                    if (hasSuccessContent) return 'success';
                }
            }
            return null;
        """)
    except Exception:
        return None


def check_popup_still_open(sb):
    try:
        return sb.execute_script("""
            var t = document.querySelector('input[name="cf-turnstile-response"]');
            if (!t) return false;
            var buttons = document.querySelectorAll('button');
            for (var i = 0; i < buttons.length; i++) {
                var text = buttons[i].innerText || '';
                if ((text.includes('시간추가') || text.includes('시간 추가') || text.includes('연장하기'))
                    && !text.includes('DELETE')) {
                    var rect = buttons[i].getBoundingClientRect();
                    if (rect.x > 200 && rect.width > 0) return true;
                }
            }
            return false;
        """)
    except Exception:
        return False


def click_next_button(sb):
    try:
        for sel in [
            "//button[contains(text(), 'NEXT')]",
            "//button[contains(text(), 'Next')]",
            "//button//span[contains(text(), 'NEXT')]",
        ]:
            if sb.is_element_visible(sel):
                sb.click(sel)
                print("[INFO] 已点击 NEXT 按钮")
                return True
    except Exception:
        pass
    return False


def handle_renewal_popup(sb, screenshot_prefix="", timeout=90):
    screenshot_name = f"{screenshot_prefix}_popup.png" if screenshot_prefix else "popup_fixed.png"

    print("[INFO]   [阶段1] 等待弹窗和 Turnstile...")

    turnstile_ready = False
    for _ in range(20):
        result = check_result_popup(sb)
        if result == "cooldown":
            print("[INFO]   检测到冷却期弹窗")
            sb.save_screenshot(screenshot_name)
            return {"status": "cooldown", "screenshot": screenshot_name}
        if result == "success":
            print("[INFO]   检测到成功弹窗")
            sb.save_screenshot(screenshot_name)
            return {"status": "success", "screenshot": screenshot_name}
        if check_turnstile_exists_popup(sb):
            turnstile_ready = True
            print("[INFO]   检测到 Turnstile")
            break
        time.sleep(1)

    if not turnstile_ready:
        print("[WARN]   未检测到 Turnstile")
        sb.save_screenshot(screenshot_name)
        return {"status": "error", "message": "未检测到 Turnstile", "screenshot": screenshot_name}

    print("[INFO]   [阶段2] 修复弹窗样式...")
    for _ in range(3):
        sb.execute_script(EXPAND_POPUP_JS)
        time.sleep(0.5)
    sb.save_screenshot(screenshot_name)

    print("[INFO]   [阶段3] 点击 Turnstile...")
    for attempt in range(6):
        if check_turnstile_solved_popup(sb):
            print("[INFO]   Turnstile 已通过!")
            break
        sb.execute_script(EXPAND_POPUP_JS)
        time.sleep(0.3)
        click_turnstile_checkbox(sb)
        for _ in range(8):
            time.sleep(0.5)
            if check_turnstile_solved_popup(sb):
                print("[INFO]   Turnstile 已通过!")
                break
        if check_turnstile_solved_popup(sb):
            break
        sb.save_screenshot(
            f"{screenshot_prefix}_turnstile_{attempt}.png" if screenshot_prefix
            else f"turnstile_attempt_{attempt}.png"
        )

    print("[INFO]   等待提交结果...")
    result_start = time.time()
    last_screenshot_time = 0

    while time.time() - result_start < 45:
        result = check_result_popup(sb)
        if result == "success":
            print("[INFO]   续期成功!")
            sb.save_screenshot(screenshot_name)
            time.sleep(1)
            click_next_button(sb)
            return {"status": "success", "screenshot": screenshot_name}
        if result == "cooldown":
            print("[INFO]   冷却期内")
            sb.save_screenshot(screenshot_name)
            time.sleep(1)
            click_next_button(sb)
            return {"status": "cooldown", "screenshot": screenshot_name}
        if not check_popup_still_open(sb):
            time.sleep(2)
            result = check_result_popup(sb)
            if result:
                sb.save_screenshot(screenshot_name)
                if result == "success":
                    click_next_button(sb)
                    return {"status": "success", "screenshot": screenshot_name}
                elif result == "cooldown":
                    click_next_button(sb)
                    return {"status": "cooldown", "screenshot": screenshot_name}
        if time.time() - last_screenshot_time > 5:
            sb.save_screenshot(screenshot_name)
            last_screenshot_time = time.time()
        time.sleep(1)

    print("[WARN]   等待结果超时")
    sb.save_screenshot(screenshot_name)
    return {"status": "timeout", "screenshot": screenshot_name}


# ============================================================
#  SeleniumBase 页面交互（通用）
# ============================================================

def get_expiry_from_page(sb):
    try:
        page_text = sb.get_page_source()
        match = re.search(r'유통기한\s*(\d{4}-\d{2}-\d{2}\s+\d{2}:\d{2}:\d{2})', page_text)
        if match:
            return match.group(1).strip()
        match = re.search(r'(\d{4}-\d{2}-\d{2}\s+\d{2}:\d{2}:\d{2})', page_text)
        if match:
            return match.group(1).strip()
        return "Unknown"
    except Exception:
        return "Unknown"


def find_renewal_button(sb):
    for selector in RENEWAL_BUTTON_SELECTORS:
        try:
            if sb.is_element_present(selector):
                return selector
        except Exception:
            continue
    return None


def check_renewal_button_enabled(sb):
    xpath = find_renewal_button(sb)
    if not xpath:
        return (False, False, None, "页面上未找到续期按钮")

    try:
        is_disabled = sb.execute_script(f"""
            var btn = document.evaluate("{xpath}", document, null,
                XPathResult.FIRST_ORDERED_NODE_TYPE, null).singleNodeValue;
            if (!btn) return null;
            return btn.disabled || btn.getAttribute('aria-disabled') === 'true'
                   || btn.classList.contains('disabled');
        """)
        if is_disabled is None:
            return (False, False, None, "按钮元素无法访问")
        if is_disabled:
            return (True, False, xpath, "续期按钮已禁用（可能在冷却期）")
    except Exception:
        pass

    return (True, True, xpath, "")


def is_logged_in(sb):
    try:
        url = sb.get_current_url()
        if "/login" in url or "/auth" in url:
            return False
        if get_expiry_from_page(sb) != "Unknown":
            return True
        if find_renewal_button(sb):
            return True
        if sb.is_element_present("//div[contains(@class,'ServerControls')]") or \
           sb.is_element_present("//a[contains(@href,'/server/')]"):
            return True
        return False
    except Exception:
        return False


def check_and_update_cookie(sb, cookie_env, original_cookie_value, remark=""):
    """检查 Cookie 是否变化；返回 (updated: bool, latest_cookie_value: str)"""
    try:
        cookies = sb.get_cookies()
        for cookie in cookies:
            if cookie.get("name", "").startswith("remember_web"):
                new_val = cookie.get("value", "")
                c_name = cookie.get("name", "")
                if new_val and new_val != original_cookie_value:
                    new_cookie_str = f"{c_name}={new_val}"
                    if remark:
                        new_secret_value = f"{remark}-----{new_cookie_str}"
                    else:
                        new_secret_value = new_cookie_str
                    print(f"[INFO]   Cookie 已变化，更新 {cookie_env}...")
                    if asyncio.run(update_github_secret(cookie_env, new_secret_value)):
                        print(f"[INFO]   ✅ {cookie_env} 已更新")
                        return True, new_val
                    else:
                        print(f"[ERROR]  ❌ {cookie_env} 更新失败")
                        return False, original_cookie_value
                break
    except Exception as e:
        print(f"[ERROR]  Cookie 检查失败: {e}")
    return False, original_cookie_value


# ============================================================
#  单个服务器续期处理
# ============================================================

def process_single_server(sb, server_info, cookie_name, cookie_value, cookie_str,
                          cookie_env, remark, screenshot_prefix):
    server_id = server_info.get("identifier", "Unknown")
    server_uuid = server_info.get("uuid", "")
    server_type = server_info.get("server_type", "notfree")
    server_name = server_info.get("name", "")
    api_expiry = server_info.get("expire", "Unknown")

    srv_result = {
        "server_id": server_id,
        "server_uuid": server_uuid,
        "server_type": server_type,
        "server_name": server_name,
        "status": "unknown",
        "original_expiry": api_expiry,
        "new_expiry": api_expiry,
        "message": "",
        "screenshot": None,
        "cookie_updated": False,
        "latest_cookie_value": cookie_value,
    }

    server_url = build_server_url(server_id)
    rd = get_remaining_days(api_expiry)
    dd = format_remaining_days(rd)

    print(f"\n  {'─' * 50}")
    print(f"  [INFO] 服务器: {mask_server_id(server_id)} [{server_type}] {server_name}")
    print(f"  [INFO] 到期: {api_expiry} | 剩余: {calculate_remaining_time(api_expiry)} ({dd}天)")
    print("  [INFO] 访问服务器页面...")

    try:
        sb.uc_open_with_reconnect(server_url, reconnect_time=5)
        time.sleep(3)

        if not is_logged_in(sb):
            sb.add_cookie({"name": cookie_name, "value": cookie_value, "domain": DOMAIN, "path": "/"})
            sb.uc_open_with_reconnect(server_url, reconnect_time=5)
            time.sleep(3)

        if not is_logged_in(sb):
            ss_path = f"{screenshot_prefix}_login_fail.png"
            sb.save_screenshot(ss_path)
            srv_result.update(status="error", message="浏览器登录失败", screenshot=ss_path)
            print("  [ERROR] 浏览器登录失败")
            return srv_result

        print("  [INFO] 登录成功")

        page_expiry = get_expiry_from_page(sb)
        if page_expiry != "Unknown":
            srv_result["original_expiry"] = page_expiry

        print("  [INFO] 检查续期按钮...")
        btn_found, btn_enabled, btn_xpath, btn_reason = check_renewal_button_enabled(sb)

        if not btn_found:
            print(f"  [WARN] {btn_reason}")
            ss_path = f"{screenshot_prefix}_no_btn.png"
            sb.save_screenshot(ss_path)
            srv_result.update(status="skipped", message=btn_reason, screenshot=ss_path)
            return srv_result

        if not btn_enabled:
            print(f"  [WARN] {btn_reason}")
            ss_path = f"{screenshot_prefix}_btn_disabled.png"
            sb.save_screenshot(ss_path)
            srv_result.update(status="skipped", message=btn_reason, screenshot=ss_path)
            return srv_result

        print("  [INFO] 续期按钮可用，执行续期")

        random_delay(1.0, 2.0)
        sb.click(btn_xpath)
        print("  [INFO] 已点击续期按钮，等待弹窗...")
        time.sleep(3)

        popup_result = handle_renewal_popup(sb, screenshot_prefix=screenshot_prefix, timeout=90)
        srv_result["screenshot"] = popup_result.get("screenshot")

        # 验证到期时间
        time.sleep(3)
        xsrf_token = get_xsrf_token_from_cookies(sb)
        if server_uuid:
            ep = f"/freeservers/{server_uuid}/info" if server_type == "free" else f"/notfreeservers/{server_uuid}/info"
            new_info = api_fetch_json(sb, f"{API_BASE_URL}{ep}", xsrf_token)
            if new_info and new_info.get("success"):
                new_expiry = new_info.get("data", {}).get("expire", srv_result["original_expiry"])
            else:
                sb.uc_open_with_reconnect(server_url, reconnect_time=3)
                time.sleep(3)
                new_expiry = get_expiry_from_page(sb)
        else:
            sb.uc_open_with_reconnect(server_url, reconnect_time=3)
            time.sleep(3)
            new_expiry = get_expiry_from_page(sb)

        srv_result["new_expiry"] = new_expiry

        original_dt = parse_expiry_to_datetime(srv_result["original_expiry"])
        new_dt = parse_expiry_to_datetime(new_expiry)

        if popup_result["status"] == "cooldown":
            srv_result.update(status="cooldown", message="冷却期内")
            print("  [INFO] 冷却期内")
        elif original_dt and new_dt and new_dt > original_dt:
            diff_h = (new_dt - original_dt).total_seconds() / 3600
            srv_result.update(status="success", message=f"延长了 {diff_h:.1f} 小时")
            print(f"  [INFO] ✅ 续期成功！延长 {diff_h:.1f} 小时")
        elif popup_result["status"] == "success":
            srv_result.update(status="success", message="操作完成")
            print("  [INFO] ✅ 续期成功")
        else:
            srv_result.update(status=popup_result["status"], message=popup_result.get("message", "未知"))
            print(f"  [WARN] 结果: {popup_result['status']}")

        updated, latest_val = check_and_update_cookie(sb, cookie_env, cookie_value, remark)
        if updated:
            srv_result["cookie_updated"] = True
            srv_result["latest_cookie_value"] = latest_val

        if not srv_result["screenshot"] or not os.path.exists(srv_result["screenshot"]):
            final_ss = f"{screenshot_prefix}_final.png"
            sb.save_screenshot(final_ss)
            srv_result["screenshot"] = final_ss

    except Exception as e:
        import traceback
        print(f"  [ERROR] 异常: {repr(e)}")
        traceback.print_exc()
        srv_result.update(status="error", message=str(e)[:100])
        try:
            ss_path = f"{screenshot_prefix}_error.png"
            sb.save_screenshot(ss_path)
            srv_result["screenshot"] = ss_path
        except Exception:
            pass

    return srv_result


# ============================================================
#  单个账号处理（独立代理 + 独立浏览器实例）
# ============================================================

def process_single_account(sb, account, account_index, proxy_desc="直连"):
    remark = account.get("remark", f"账号{account_index + 1}")
    cookie_env = account.get("cookie_env", "")
    cookie_str = account.get("cookie_str", "")
    cookie_name = account.get("cookie_name", "")
    cookie_value = account.get("cookie_value", "")

    result = {
        "remark": remark,
        "cookie_env": cookie_env,
        "email": "Unknown",
        "status": "unknown",
        "message": "",
        "servers": [],
        "cookie_updated": False,
        "proxy_desc": proxy_desc,
    }

    # Step 1: Turnstile (登录阶段)
    print("[INFO] [步骤1] 访问站点并处理 Cloudflare 验证...")
    sb.uc_open_with_reconnect(f"https://{DOMAIN}/", reconnect_time=5)
    if not handle_turnstile(sb):
        print("[ERROR] Turnstile 验证失败")
        result["status"] = "error"
        result["message"] = "Cloudflare Turnstile 验证失败"
        return result
    print("[INFO] ✅ CF 验证通过")

    # Step 2: 注入 Cookie 并登录
    print("[INFO] [步骤2] 注入 Cookie 并登录...")
    sb.add_cookie({"name": cookie_name, "value": cookie_value, "domain": DOMAIN, "path": "/"})
    sb.uc_open_with_reconnect(f"https://{DOMAIN}/", reconnect_time=5)
    time.sleep(3)

    if not is_logged_in(sb):
        print("[WARN]   未检测到登录状态，尝试刷新...")
        sb.uc_open_with_reconnect(f"https://{DOMAIN}/server/", reconnect_time=5)
        time.sleep(3)

    if not is_logged_in(sb):
        ss_path = f"acc{account_index + 1}_login_fail.png"
        sb.save_screenshot(ss_path)
        result["status"] = "cookie_invalid"
        result["message"] = "Cookie 失效或登录失败（Turnstile 通过后仍无法登录）"
        return result

    xsrf_token = get_xsrf_token_from_cookies(sb)
    print("[INFO]   登录成功，已获取会话 Cookie")

    # Step 3: 获取信息
    print("[INFO] [步骤3] 获取账号信息...")
    server_data = api_fetch_json(sb, f"{API_BASE_URL}?page=1", xsrf_token)
    if not server_data or server_data.get("error") == "unauthorized":
        print("[ERROR]   获取服务器列表失败")
        result["status"] = "error"
        result["message"] = "无法获取服务器列表"
        return result

    email_data = api_fetch_json(
        sb,
        f"{API_BASE_URL}/account/activity?sort=-timestamp&page=1&include[]=actor",
        xsrf_token
    )
    email = None
    if email_data:
        for item in email_data.get("data", []):
            actor = item.get("attributes", {}).get("relationships", {}).get("actor", {})
            if actor.get("object") == "user":
                email = actor.get("attributes", {}).get("email")
                if email:
                    break
    result["email"] = email or "Unknown"

    servers = []
    for s in server_data.get("data", []):
        attrs = s.get("attributes", {})
        stype = attrs.get("server_type", "")
        info = {
            "identifier": attrs.get("identifier", ""),
            "uuid": attrs.get("uuid", ""),
            "name": attrs.get("name", ""),
            "server_type": stype,
            "expire": "Unknown",
            "add_hours": "Unknown",
        }
        if attrs.get("uuid") and stype in ("notfree", "free"):
            ep = f"/freeservers/{attrs['uuid']}/info" if stype == "free" else f"/notfreeservers/{attrs['uuid']}/info"
            si = api_fetch_json(sb, f"{API_BASE_URL}{ep}", xsrf_token)
            if si and si.get("success"):
                d = si.get("data", {})
                info["expire"] = d.get("expire", "Unknown")
                info["add_hours"] = d.get("addHours", "Unknown")
        servers.append(info)

    result["servers"] = servers

    if email and email != "Unknown":
        print(f"[INFO] 邮箱: {mask_email(email)}")

    if not servers:
        print("[WARN] 该账号下没有服务器")
        result["status"] = "no_server"
        result["message"] = "该账号下没有服务器"
        return result

    print(f"[INFO] 找到 {len(servers)} 个服务器:")
    for s in servers:
        print(f"  - {mask_server_id(s['identifier'])} [{s['server_type']}] {s['name']} | 到期: {s['expire']}")

    # Step 4: 逐个处理服务器
    print("[INFO] [步骤4] 逐个处理服务器续期...")
    server_results = []
    current_cookie_value = cookie_value
    for srv_idx, server in enumerate(servers):
        ss_prefix = f"acc{account_index + 1}_srv{srv_idx + 1}"
        srv_result = process_single_server(
            sb, server, cookie_name, current_cookie_value, cookie_str, cookie_env, remark, ss_prefix
        )
        server_results.append(srv_result)
        if srv_result.get("cookie_updated"):
            result["cookie_updated"] = True
            current_cookie_value = srv_result.get("latest_cookie_value", current_cookie_value)
        if srv_idx < len(servers) - 1:
            wait = random.randint(2, 4) if srv_result.get("status") == "skipped" else random.randint(5, 10)
            print(f"\n  [INFO] 等待 {wait} 秒后处理下一个服务器...")
            time.sleep(wait)

    result["servers"] = server_results

    statuses = [s["status"] for s in server_results]
    if "success" in statuses:
        result["status"] = "success"
        result["message"] = f"{statuses.count('success')}/{len(statuses)} 个服务器续期成功"
    elif all(s == "skipped" for s in statuses):
        result["status"] = "skipped"
        result["message"] = "所有服务器均跳过"
    elif "cooldown" in statuses:
        result["status"] = "cooldown"
        result["message"] = "冷却期内"
    elif "error" in statuses or "timeout" in statuses:
        result["status"] = "error"
        err_count = statuses.count("error") + statuses.count("timeout")
        result["message"] = f"{err_count}/{len(statuses)} 个服务器失败"
    else:
        result["status"] = statuses[0] if statuses else "unknown"

    return result


def run_account_isolated(account, account_index):
    """为单个账号准备独立 sing-box 代理和独立浏览器实例"""
    remark = account.get("remark", f"账号{account_index + 1}")
    cookie_env = account.get("cookie_env", "")
    proxy_uri = account.get("proxy_uri")
    fallback_direct = _parse_bool(os.environ.get("PROXY_FALLBACK_DIRECT", "true"))

    print(f"\n{'=' * 60}")
    print(f"[INFO] 处理账号 [{account_index + 1}]: {mask_remark(remark)} ({cookie_env})")
    print(f"{'=' * 60}")

    proxy_mgr = None
    sb_proxy_arg = None
    proxy_desc = "直连"

    if proxy_uri:
        print(f"[INFO] 正在通过 sing-box 启动独立代理 ({account.get('proxy_source')})...")
        proxy_mgr = SingBoxProxyManager(proxy_uri)
        ok, info = proxy_mgr.start()
        if ok:
            sb_proxy_arg = f"127.0.0.1:{proxy_mgr.local_port}"
            proxy_desc = f"{proxy_mgr.label} ({mask_ip(proxy_mgr.egress_ip)})"
            print(f"[INFO] ✅ 代理就绪 | 端口: {proxy_mgr.local_port} | 出口 IP: {mask_ip(proxy_mgr.egress_ip)}")
        else:
            print(f"[WARN] ⚠️ 代理启动失败: {info}")
            proxy_mgr = None
            if not fallback_direct:
                return {
                    "remark": remark,
                    "cookie_env": cookie_env,
                    "email": "Unknown",
                    "status": "error",
                    "message": f"代理启动失败且未启用直连回退: {info}",
                    "servers": [],
                    "cookie_updated": False,
                    "proxy_desc": "代理失败",
                }
            print("[WARN] 已启用 PROXY_FALLBACK_DIRECT，回退到直连模式")
            proxy_desc = "直连(代理回退)"

    try:
        sb_kwargs = {
            "uc": True,
            "test": True,
            "locale": "ko",
            "headless": False,
            "chromium_arg": (
                "--disable-dev-shm-usage,--no-sandbox,--disable-gpu,"
                "--disable-software-rasterizer,--disable-background-timer-throttling"
            ),
        }
        if sb_proxy_arg:
            sb_kwargs["proxy"] = sb_proxy_arg

        with SB(**sb_kwargs) as sb:
            print(f"[INFO] 独立浏览器已启动 | 出口: {proxy_desc}")
            return process_single_account(sb, account, account_index, proxy_desc=proxy_desc)

    except Exception as e:
        import traceback
        print(f"[ERROR] 账号 {mask_remark(remark)} 浏览器异常: {repr(e)}")
        traceback.print_exc()
        return {
            "remark": remark,
            "cookie_env": cookie_env,
            "email": "Unknown",
            "status": "error",
            "message": f"浏览器异常: {str(e)[:100]}",
            "servers": [],
            "cookie_updated": False,
            "proxy_desc": proxy_desc,
        }
    finally:
        if proxy_mgr:
            proxy_mgr.stop()
            print("[INFO] sing-box 代理已关闭")


# ============================================================
#  单账号 TG 通知
# ============================================================

def send_account_notification(result):
    email = result.get("email", "Unknown")
    remark = result.get("remark", "")
    cookie_updated = result.get("cookie_updated", False)
    servers = result.get("servers", [])
    status = result.get("status", "unknown")
    proxy_desc = result.get("proxy_desc", "直连")

    account_display = email if email and email != "Unknown" else remark
    lines = [
        f"账号：{account_display}",
        f"出口：{proxy_desc}",
    ]

    if status == "cookie_invalid":
        lines.append("状态：⚠️ Cookie 已失效，请及时更新 WEIRDHOST_COOKIE_*")
    elif status == "no_server":
        lines.append("状态：⚠️ 没有服务器")
    elif status == "error" and not servers:
        lines.append(f"状态：❌ {result.get('message', '未知错误')}")
    else:
        for s in servers:
            lines.append("")
            lines.append(f"服务器：{s.get('server_id', '')}")
            srv_status = s["status"]

            if srv_status == "success":
                lines.append("状态：🟢 续期成功")
                new_exp = s.get("new_expiry", "Unknown")
                lines.append(f"剩余：{calculate_remaining_time(new_exp)}")
                msg = s.get("message", "")
                if msg and "延长" in msg:
                    lines.append(f"延长：{msg}")
                else:
                    orig = s.get("original_expiry", "Unknown")
                    new = s.get("new_expiry", "Unknown")
                    if orig != "Unknown" and new != "Unknown":
                        odt = parse_expiry_to_datetime(orig)
                        ndt = parse_expiry_to_datetime(new)
                        if odt and ndt and ndt > odt:
                            diff_h = (ndt - odt).total_seconds() / 3600
                            lines.append(f"延长：延长{diff_h:.1f}h")
            elif srv_status == "cooldown":
                lines.append("状态：⏳ 冷却期")
                expiry = s.get("original_expiry", "Unknown")
                lines.append(f"剩余：{calculate_remaining_time(expiry)}")
                lines.append("提示：冷却中，请稍后再试")
            elif srv_status == "skipped":
                lines.append("状态：⏭️ 跳过")
                expiry = s.get("original_expiry", s.get("new_expiry", "Unknown"))
                lines.append(f"剩余：{calculate_remaining_time(expiry)}")
                lines.append(f"原因：{s.get('message', '未知')}")
            else:
                lines.append(f"状态：❌ {srv_status}")
                lines.append(f"信息：{s.get('message', '未知')}")

    if cookie_updated:
        lines.append("")
        lines.append("🔑 Cookie 已自动更新")

    lines.append("")
    lines.append("Weirdhost Auto Renew")

    message = "\n".join(lines)

    screenshot = None
    for s in servers:
        if s["status"] in ("success", "cooldown", "error", "timeout"):
            if s.get("screenshot") and os.path.exists(s["screenshot"]):
                screenshot = s["screenshot"]
                break

    if screenshot:
        sync_tg_notify_photo(screenshot, message)
    else:
        sync_tg_notify(message)


# ============================================================
#  主函数
# ============================================================

def add_server_time():
    accounts = detect_accounts()

    if not accounts:
        print("\n" + "=" * 60)
        print("[ERROR] 未检测到任何有效的账号配置")
        print("=" * 60)
        print("\n请在 GitHub Secrets 中设置 WEIRDHOST_COOKIE_1 ~ WEIRDHOST_COOKIE_5")
        print("\n格式: 备注-----remember_web_xxx=yyy")
        print("示例: 我的账号-----remember_web_59ba36addc2b2f940CCCC=XXXXXXXXXXX")
        print("=" * 60)

        sync_tg_notify(
            "🔔 <b>Weirdhost 续期</b>\n\n"
            "❌ 未检测到任何有效的 WEIRDHOST_COOKIE_N\n\n"
            "请在 GitHub Secrets 中设置:\n"
            "<code>WEIRDHOST_COOKIE_1</code>\n"
            "格式: <code>备注-----remember_web_xxx=yyy</code>"
        )
        return

    print("=" * 60)
    print("[INFO] Weirdhost 多账号自动续期 (独立浏览器 + sing-box 代理隔离)")
    print(f"[INFO] 共 {len(accounts)} 个账号")
    print("=" * 60)

    results = []
    for i, account in enumerate(accounts):
        result = run_account_isolated(account, i)
        results.append(result)
        send_account_notification(result)

        if i < len(accounts) - 1:
            wait_time = random.randint(2, 4) if result.get("status") == "skipped" else random.randint(5, 10)
            print(f"\n[INFO] 等待 {wait_time} 秒后处理下一个账号...")
            time.sleep(wait_time)

    print(f"\n{'=' * 60}")
    print("[INFO] 全部处理完成")
    print(f"{'=' * 60}")
    icons = {
        "success": "🟢", "cooldown": "🟡", "skipped": "🔵",
        "cookie_invalid": "🔒", "no_server": "📭",
        "error": "❌", "timeout": "⚠️",
    }
    for r in results:
        icon = icons.get(r["status"], "❓")
        srv_count = len(r.get("servers", []))
        email_display = mask_email(r.get("email", ""))
        remark_display = mask_remark(r.get("remark", "?"))
        print(f"  {icon} {remark_display} ({email_display}) | 出口: {r.get('proxy_desc', '直连')} | "
              f"{srv_count} 个服务器 | {r['status']} | {r.get('message', '')}")


if __name__ == "__main__":
    add_server_time()
