"""
Telegram: публикация графика сбоев СПб в канал при всплесках.

Детекция всплесков (3 уровня):
  • Быстрый — скачок за 5 мин (точка vs точка), ×2+
  • Медленный — среднее за 15 мин vs среднее за предыдущий час, ×2.5+
  • Абсолютный — жалоб > 50 при норме < 15

Cooldown: после алерта тишина минимум 30 мин.

pip install python-telegram-bot requests python-dotenv matplotlib
"""

import os
import re
import io
import json
import base64
import logging
import asyncio
from datetime import datetime, timezone, timedelta
from collections import deque
from dataclasses import dataclass, field
from urllib.parse import quote

import requests
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from matplotlib.dates import DateFormatter

from dotenv import load_dotenv
from telegram import Update, Bot, BotCommand
from telegram.ext import Application, CommandHandler, ContextTypes

load_dotenv()

import random

# ─── Конфигурация ────────────────────────────────────────────────────

TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
CHANNEL_ID = os.getenv("CHANNEL_ID", "")

SERVICE_NAME = "[78] Санкт-Петербург"
DATA_URL = "https://detector404.ru/data.js?service={}&summ=15"

POLL_INTERVAL = 300       # 5 минут между проверками
POINT_INTERVAL = 300      # 5 минут между точками графика

# ─── Пороги детекции ─────────────────────────────────────────────────

# Быстрый всплеск: текущая точка / предыдущая точка
FAST_SPIKE_RATIO = 2.0        # ×2 за 5 минут
FAST_SPIKE_MIN = 15           # минимум жалоб чтобы считать

# Медленный всплеск: среднее за 15 мин / среднее за предыдущий час
SLOW_SPIKE_RATIO = 2.5        # ×2.5 рост средней
SLOW_SPIKE_MIN = 20           # минимум средней за 15 мин

# Абсолютный порог: сейчас > HIGH и раньше было < LOW
ABS_THRESHOLD_HIGH = 50       # текущие жалобы выше этого
ABS_THRESHOLD_LOW = 15        # при норме ниже этого

# Cooldown: не слать алерт чаще чем раз в N минут
ALERT_COOLDOWN_MIN = 30

MSK = timezone(timedelta(hours=3))

logging.basicConfig(
    format="%(asctime)s [%(levelname)s] %(message)s",
    level=logging.INFO,
)
log = logging.getLogger(__name__)

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 Chrome/124.0 Safari/537.36"
    ),
}

# ─── RC4 расшифровка ─────────────────────────────────────────────────

def _rc4_decrypt(encoded_b64: str) -> dict:
    data = bytearray(base64.b64decode(encoded_b64))
    key = bytes(data[-16:])
    S = list(range(256))
    j = 0
    for i in range(256):
        d = S[i]
        j = (j + d + key[i & 0xF]) & 0xFF
        S[i], S[j] = S[j], S[i]
    for idx in range(len(data)):
        i = idx & 0xFF
        d = S[i]
        j = (j + d) & 0xFF
        swap = S[j]
        S[i] = swap
        S[j] = d
        data[idx] ^= S[(d + swap) & 0xFF]
    return json.loads(data[:-16].decode("utf-8"))


# ─── Получение данных ────────────────────────────────────────────────

def fetch_data() -> tuple[list[int], list[float]] | None:
    url = DATA_URL.format(quote(SERVICE_NAME))
    try:
        resp = requests.get(url, headers=HEADERS, timeout=20)
        resp.raise_for_status()
    except requests.RequestException as e:
        log.error("Ошибка загрузки: %s", e)
        return None

    text = resp.text

    m = re.search(r'tgdown\.push\("([^"]+)"\)', text)
    if not m:
        return None
    try:
        tgdown = _rc4_decrypt(m.group(1))
    except Exception as e:
        log.error("Ошибка расшифровки tgdown: %s", e)
        return None

    complaints = tgdown.get(SERVICE_NAME) or next(iter(tgdown.values()), [])

    errors = []
    m2 = re.search(r'errors\.push\("([^"]+)"\)', text)
    if m2:
        try:
            err_data = _rc4_decrypt(m2.group(1))
            errors = err_data.get(SERVICE_NAME) or next(iter(err_data.values()), [])
        except Exception:
            pass

    if not complaints:
        return None

    log.info("Данные: %d точек, последняя: %d", len(complaints), complaints[-1])
    return complaints, errors


# ─── Детекция всплесков ──────────────────────────────────────────────

@dataclass
class SpikeResult:
    is_spike: bool = False
    alerts: list = field(default_factory=list)
    spike_type: str = ""  # "fast", "slow", "absolute"


@dataclass
class RecoveryResult:
    is_recovery: bool = False
    recovery_type: str = ""  # "partial", "full"
    avg_30m_current: float = 0
    avg_30m_prev: float = 0


def detect_spike(complaints: list[int]) -> SpikeResult:
    """
    Анализирует массив точек и определяет, есть ли всплеск.

    Логика:
      1. Быстрый: последняя точка vs предпоследняя (×2 за 5 мин)
      2. Медленный: avg(последние 3 точки = 15мин) vs avg(предшествующие 12 точек = 1ч)
      3. Абсолютный: сейчас > 50 при норме < 15
    """
    result = SpikeResult()
    if len(complaints) < 15:
        return result

    current = complaints[-1]
    prev = complaints[-2]

    # Средние
    avg_15m = sum(complaints[-3:]) / 3           # последние 15 мин
    avg_1h_before = sum(complaints[-15:-3]) / 12  # час до этого (без последних 15 мин)

    # 1. Быстрый всплеск
    if current >= FAST_SPIKE_MIN and prev > 0:
        ratio = current / prev
        if ratio >= FAST_SPIKE_RATIO:
            pct = int((ratio - 1) * 100)
            result.is_spike = True
            result.spike_type = "fast"
            result.alerts.append(
                f"Быстрый скачок: {prev} → {current} (+{pct}% за 5 мин)"
            )

    # 2. Медленный всплеск
    if avg_15m >= SLOW_SPIKE_MIN and avg_1h_before > 0:
        ratio = avg_15m / avg_1h_before
        if ratio >= SLOW_SPIKE_RATIO:
            pct = int((ratio - 1) * 100)
            result.is_spike = True
            result.spike_type = result.spike_type or "slow"
            result.alerts.append(
                f"📈 Медленный рост: среднее {avg_1h_before:.0f} → {avg_15m:.0f} "
                f"(+{pct}% за 15 мин vs час)"
            )

    # 3. Абсолютный порог
    if current >= ABS_THRESHOLD_HIGH and avg_1h_before < ABS_THRESHOLD_LOW:
        if not result.is_spike:  # не дублируем если уже сработало
            result.is_spike = True
            result.spike_type = result.spike_type or "absolute"
            result.alerts.append(
                f"🔴 Аномалия: {current} жалоб (норма была ~{avg_1h_before:.0f})"
            )

    return result


def detect_recovery(complaints: list[int]) -> RecoveryResult:
    """
    Детектирует падение активности (восстановление после сбоя).

    Логика:
      Среднее за последние 30 мин vs среднее за предыдущие 30 мин.
      Если текущее меньше на 20%+ — восстановление.
      Тип:
        "partial" — текущее среднее ещё >= 100
        "full"    — текущее среднее < 100
    """
    result = RecoveryResult()
    # нужно минимум 12 точек (1 час данных)
    if len(complaints) < 12:
        return result

    avg_30m_current = sum(complaints[-6:]) / 6    # последние 30 мин
    avg_30m_prev = sum(complaints[-12:-6]) / 6    # предыдущие 30 мин

    if avg_30m_prev <= 0:
        return result

    drop_ratio = avg_30m_current / avg_30m_prev

    # падение на 20%+ (ratio < 0.8) и предыдущий период был значимым
    if drop_ratio <= 0.8 and avg_30m_prev >= 50:
        result.is_recovery = True
        result.avg_30m_current = avg_30m_current
        result.avg_30m_prev = avg_30m_prev
        result.recovery_type = "full" if avg_30m_current < 100 else "partial"

    return result


# ─── Рендер графика ──────────────────────────────────────────────────

def render_graph(complaints: list[int], errors: list[float],
                 spike: SpikeResult | None = None) -> io.BytesIO:
    now = datetime.now(MSK)
    n = len(complaints)
    times = [now - timedelta(seconds=(n - 1 - i) * POINT_INTERVAL) for i in range(n)]

    fig, ax1 = plt.subplots(figsize=(12, 5))
    fig.patch.set_facecolor("#1a1a2e")
    ax1.set_facecolor("#1a1a2e")

    # Жалобы
    ax1.plot(times, complaints, color="#ff2d55", linewidth=1.5, zorder=3)
    ax1.fill_between(times, complaints, alpha=0.25, color="#ff2d55", zorder=2)

    # Сетевые сбои
    if errors and len(errors) == n:
        ax2 = ax1.twinx()
        ax2.plot(times, errors, color="#7b68ee", linewidth=1.2, alpha=0.8, zorder=1)
        ax2.fill_between(times, errors, alpha=0.15, color="#7b68ee", zorder=0)
        ax2.set_ylabel("сетевые сбои, %", color="#7b68ee", fontsize=10)
        ax2.tick_params(axis="y", colors="#7b68ee", labelsize=9)
        for spine in ax2.spines.values():
            spine.set_visible(False)

    # Маркер пика
    peak = max(complaints)
    peak_idx = complaints.index(peak)
    ax1.annotate(
        f"{peak}",
        xy=(times[peak_idx], peak),
        xytext=(0, 10), textcoords="offset points",
        ha="center", fontsize=9, color="#ff6b8a", fontweight="bold",
    )

    # Маркер текущего значения
    current = complaints[-1]
    ax1.plot(times[-1], current, "o", color="#ff2d55", markersize=6, zorder=5)
    ax1.annotate(
        f"  {current}",
        xy=(times[-1], current),
        ha="left", va="center", fontsize=9, color="#ff6b8a",
    )

    # Пунктир средней за час
    if len(complaints) >= 12:
        avg_1h = sum(complaints[-12:]) / 12
        ax1.axhline(y=avg_1h, color="#ff6b8a", linestyle="--", alpha=0.3, linewidth=1)
        ax1.text(times[0], avg_1h, f"  avg/1h: {avg_1h:.0f}",
                 color="#ff6b8a", alpha=0.5, fontsize=8, va="bottom")

    # Оформление
    ax1.set_ylabel("жалобы пользователей", color="#ff2d55", fontsize=10)
    ax1.tick_params(axis="y", colors="#ff2d55", labelsize=9)
    ax1.tick_params(axis="x", colors="#888888", labelsize=9)
    ax1.xaxis.set_major_formatter(DateFormatter("%H:%M", tz=MSK))
    ax1.xaxis.set_major_locator(mdates.HourLocator(interval=2, tz=MSK))

    for spine in ax1.spines.values():
        spine.set_visible(False)
    ax1.grid(axis="y", color="#333355", alpha=0.5, linewidth=0.5)
    ax1.grid(axis="x", color="#333355", alpha=0.3, linewidth=0.5)

    # Заголовок
    peak_time = times[peak_idx].strftime("%H:%M")
    alert_label = "ALERT" if spike and spike.is_spike else ""
    title = f"Санкт-Петербург  •  сейчас: {current}  •  пик: {peak} ({peak_time})"
    if alert_label:
        title = f"[{alert_label}]  {title}"
    ax1.set_title(title, color="#ffffff", fontsize=12, pad=12, loc="left")

    fig.text(0.99, 0.01, now.strftime("%d.%m.%Y %H:%M МСК") + "  •  detector404.ru",
             ha="right", va="bottom", fontsize=8, color="#555555")

    plt.tight_layout()

    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=150, bbox_inches="tight",
                facecolor=fig.get_facecolor(), edgecolor="none")
    plt.close(fig)
    buf.seek(0)
    return buf


# ─── Генераторы шапок ────────────────────────────────────────────────

CHAOS_EMOJI = ["🔥", "💥", "🚨", "⚠️", "☠️", "🤯", "😱", "🫠", "💀", "🌋"]
NEUTRAL_EMOJI = ["😐", "🙄", "😑", "🤔", "😶", "🫤", "😒", "🧐", "😮‍💨", "🫥"]
RELIEF_EMOJI = ["🌿", "🍃", "💚", "🌬️", "🌱", "😮‍💨", "🫁", "☁️", "🕊️", "🌊"]


def chaos_header() -> str:
    e1, e2 = random.sample(CHAOS_EMOJI, 2)
    return f"{e1} ЕБАНУЛИ!!! {e2}"


def recovery_header(recovery_type: str) -> str:
    if recovery_type == "partial":
        e1, e2 = random.sample(NEUTRAL_EMOJI, 2)
        return f"{e1} УДАВКУ ОСЛАБИЛИ... {e2}"
    else:
        e1, e2 = random.sample(RELIEF_EMOJI, 2)
        return f"{e1} ДАЛИ ПОДЫШАТЬ!!! {e2}"


def format_caption(complaints: list[int], spike: SpikeResult,
                   recovery: RecoveryResult | None = None) -> str:
    current = complaints[-1]
    peak = max(complaints)
    avg_1h = sum(complaints[-12:]) / 12 if len(complaints) >= 12 else current

    lines = []

    if spike.is_spike:
        lines.append(chaos_header())
        lines.append("")
        for a in spike.alerts:
            lines.append(a)
        lines.append("")
    elif recovery and recovery.is_recovery:
        lines.append(recovery_header(recovery.recovery_type))
        lines.append("")
        drop_pct = int((1 - recovery.avg_30m_current / recovery.avg_30m_prev) * 100)
        lines.append(
            f"Среднее за полчаса: {recovery.avg_30m_prev:.0f} → {recovery.avg_30m_current:.0f} "
            f"(−{drop_pct}%)"
        )
        lines.append("")

    lines.append(f"Жалоб сейчас: {current}")
    lines.append(f"Среднее за час: {avg_1h:.0f}")
    lines.append(f"Пик за сегодня: {peak}")
    lines.append("")

    return "\n".join(lines)


# ─── Фоновый мониторинг → канал ──────────────────────────────────────

last_alert_time: datetime | None = None
last_recovery_time: datetime | None = None


async def poll_loop(app):
    global last_alert_time, last_recovery_time

    if not CHANNEL_ID:
        log.info("CHANNEL_ID не задан — фоновый мониторинг выключен")
        return

    log.info("Мониторинг → канал %s (каждые %d сек)", CHANNEL_ID, POLL_INTERVAL)

    while True:
        try:
            result = await asyncio.get_event_loop().run_in_executor(None, fetch_data)
            if result is None:
                await asyncio.sleep(POLL_INTERVAL)
                continue

            complaints, errors = result
            spike = detect_spike(complaints)
            recovery = detect_recovery(complaints)
            now = datetime.now(MSK)

            if spike.is_spike:
                cooldown_ok = (
                    last_alert_time is None
                    or (now - last_alert_time) > timedelta(minutes=ALERT_COOLDOWN_MIN)
                )
                if cooldown_ok:
                    buf = render_graph(complaints, errors, spike)
                    caption = format_caption(complaints, spike)
                    try:
                        await app.bot.send_photo(
                            chat_id=CHANNEL_ID,
                            photo=buf,
                            caption=caption,
                        )
                        last_alert_time = now
                        log.info("Алерт в канал: %s", spike.alerts)
                    except Exception as e:
                        log.error("Ошибка публикации: %s", e)
                else:
                    remaining = ALERT_COOLDOWN_MIN - (now - last_alert_time).seconds // 60
                    log.info("Cooldown (%d мин): %s", remaining, spike.alerts)

            elif recovery.is_recovery:
                cooldown_ok = (
                    last_recovery_time is None
                    or (now - last_recovery_time) > timedelta(minutes=ALERT_COOLDOWN_MIN)
                )
                if cooldown_ok:
                    buf = render_graph(complaints, errors)
                    caption = format_caption(complaints, SpikeResult(), recovery)
                    try:
                        await app.bot.send_photo(
                            chat_id=CHANNEL_ID,
                            photo=buf,
                            caption=caption,
                        )
                        last_recovery_time = now
                        log.info(
                            "Recovery в канал: %s → %s (%s)",
                            recovery.avg_30m_prev, recovery.avg_30m_current,
                            recovery.recovery_type,
                        )
                    except Exception as e:
                        log.error("Ошибка публикации recovery: %s", e)
                else:
                    log.info("Recovery cooldown, пропускаем")

            else:
                log.debug("Норма: %d жалоб", complaints[-1])

        except Exception as e:
            log.exception("Ошибка poll_loop: %s", e)

        await asyncio.sleep(POLL_INTERVAL)


# ─── Команды бота ────────────────────────────────────────────────────

async def cmd_start(update: Update, ctx):
    await update.message.reply_text(
        "👋 Мониторинг сбоев в СПб\n/status — график жалоб за 24ч"
    )


async def cmd_status(update: Update, ctx):
    msg = await update.message.reply_text("⏳ Рисую график...")
    result = await asyncio.get_event_loop().run_in_executor(None, fetch_data)
    if result is None:
        await msg.edit_text("❌ Не удалось загрузить данные.")
        return

    complaints, errors = result
    spike = detect_spike(complaints)
    buf = await asyncio.get_event_loop().run_in_executor(
        None, render_graph, complaints, errors, spike,
    )
    caption = format_caption(complaints, spike)

    await msg.delete()
    await update.message.reply_photo(photo=buf, caption=caption)


async def cmd_test_channel(update: Update, ctx):
    """Секретная команда: отправляет тестовый ЕБАНУЛИ-пост в канал."""
    if not CHANNEL_ID:
        await update.message.reply_text("CHANNEL_ID не задан.")
        return

    await update.message.reply_text("⏳ Отправляю тест в канал...")

    result = await asyncio.get_event_loop().run_in_executor(None, fetch_data)
    if result is None:
        await update.message.reply_text("❌ Не удалось загрузить данные.")
        return

    complaints, errors = result

    # Принудительно делаем spike для теста
    fake_spike = SpikeResult(
        is_spike=True,
        spike_type="test",
        alerts=["🧪 Тестовый алерт"],
    )

    buf = await asyncio.get_event_loop().run_in_executor(
        None, render_graph, complaints, errors, fake_spike,
    )
    caption = format_caption(complaints, fake_spike)

    try:
        await ctx.bot.send_photo(
            chat_id=CHANNEL_ID,
            photo=buf,
            caption=caption,
        )
        await update.message.reply_text("✅ Тест отправлен в канал.")
    except Exception as e:
        await update.message.reply_text(f"❌ Ошибка: {e}")


# ─── Запуск ──────────────────────────────────────────────────────────

async def post_init(app):
    await app.bot.set_my_commands([
        BotCommand("status", "График сбоев за 24ч"),
    ])
    asyncio.create_task(poll_loop(app))


def main():
    if not TELEGRAM_BOT_TOKEN:
        print("=" * 55)
        print("  НАСТРОЙКА")
        print("=" * 55)
        print()
        print("1. @BotFather → /newbot → токен")
        print("2. Создайте .env:")
        print("   TELEGRAM_BOT_TOKEN=123456:ABC-DEF...")
        print("   CHANNEL_ID=-1003781101504")
        print()
        print("3. pip install python-telegram-bot requests \\")
        print("              python-dotenv matplotlib")
        print("4. python detector404_bot.py")
        print("=" * 55)
        return

    app = (
        Application.builder()
        .token(TELEGRAM_BOT_TOKEN)
        .post_init(post_init)
        .build()
    )

    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("status", cmd_status))
    app.add_handler(CommandHandler("testchannel", cmd_test_channel))

    log.info("Бот запускается...")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
