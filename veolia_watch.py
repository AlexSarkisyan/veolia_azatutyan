#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
veolia_watch.py — следит за каналом @VeoliaJur и пересылает в Telegram
только те посты, где встречается ключевое слово (по умолчанию Ազատության).

Настройка через переменные окружения:
    VEOLIA_BOT_TOKEN   токен бота от @BotFather
    VEOLIA_CHAT_ID     id чата, куда слать (свой личный id)
    VEOLIA_KEYWORDS    ключи через запятую (по умолчанию Ազատության)
    VEOLIA_STATE       путь к файлу состояния (по умолчанию рядом со скриптом)

Запуск:
    python veolia_watch.py --selftest     проверка парсера на фикстуре, без сети
    python veolia_watch.py --dry-run      сходить в канал, показать находки, не слать
    python veolia_watch.py                один проход: найти новое и отправить
    python veolia_watch.py --loop 600     бесконечный цикл с паузой 600 секунд

Первый запуск ничего не отправляет: он только запоминает текущую позицию
в канале, чтобы не прилететь пачкой из двадцати старых постов.
Чтобы всё-таки отправить найденное на первом проходе — флаг --send-first.
"""

import argparse
import hashlib
import json
import os
import re
import sys
import time
import unicodedata
from datetime import datetime, timedelta, timezone
from pathlib import Path

import requests
from bs4 import BeautifulSoup

CHANNEL = "VeoliaJur"
BASE_URL = f"https://t.me/s/{CHANNEL}"
POST_URL = f"https://t.me/{CHANNEL}/{{}}"
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 " \
     "(KHTML, like Gecko) Chrome/126.0 Safari/537.36"

DEFAULT_KEYWORDS = ["Ազատության"]

# Армения не переходит на летнее время, поэтому фиксированный сдвиг корректен
# круглый год и не тянет за собой пакет tzdata на Windows.
YEREVAN = timezone(timedelta(hours=4))
HASH_KEEP = 60          # сколько последних постов держим для отлова правок
MAX_PAGES = 10          # предохранитель от бесконечной пагинации
TG_LIMIT = 3900         # запас до лимита Telegram в 4096 символов


# ---------------------------------------------------------------- утилиты

def norm(s: str) -> str:
    """NFC + схлопывание пробелов. Армянский текст с сайта бывает в разных
    формах нормализации, без этого подстрока может не найтись."""
    return re.sub(r"\s+", " ", unicodedata.normalize("NFC", s)).strip()


def log(msg: str) -> None:
    print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}", flush=True)


def local_time(iso: str) -> str:
    """Время публикации в ереванском поясе с явной подписью.

    Telegram отдаёт datetime в UTC. Без перевода сообщение «отключение
    с 09:00» соседствовало бы с меткой 05:40, и это сбивает с толку.
    """
    try:
        dt = datetime.fromisoformat(iso)
    except ValueError:
        return iso or "время неизвестно"
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(YEREVAN).strftime("%Y-%m-%d %H:%M") + " (Ереван)"


def text_hash(text: str) -> str:
    """Отпечаток текста поста. По его изменению ловим правку задним числом:
    id поста при редактировании не меняется, поэтому иначе правку не увидеть."""
    return hashlib.sha1(norm(text).encode("utf-8")).hexdigest()[:16]


# ---------------------------------------------------------------- парсер

def parse_posts(html: str):
    """Достаёт из HTML страницы t.me/s/<channel> список постов.

    Возвращает список словарей: id (int), text (str), date (str).
    """
    soup = BeautifulSoup(html, "html.parser")
    posts = []

    for box in soup.select("div.tgme_widget_message"):
        data_post = box.get("data-post", "")          # вида "VeoliaJur/14426"
        m = re.search(r"/(\d+)$", data_post)
        if not m:
            continue
        post_id = int(m.group(1))

        node = box.select_one("div.tgme_widget_message_text")
        if node is None:
            continue                                   # пост без текста, напр. фото

        # <br> в переносы строк, остальную разметку выкидываем
        for br in node.find_all("br"):
            br.replace_with("\n")
        text = node.get_text("\n")
        # get_text добавляет свой разделитель поверх уже вставленных \n,
        # поэтому подряд идущие пустые строки схлопываем до одной
        text = re.sub(r"\n{3,}", "\n\n", text)

        tnode = box.select_one("a.tgme_widget_message_date time")
        date = tnode.get("datetime", "") if tnode else ""

        posts.append({"id": post_id, "text": text, "date": date})

    posts.sort(key=lambda p: p["id"])
    return posts


def matches(text: str, keywords) -> list:
    """Какие из ключей встретились в тексте. Регистр игнорируем."""
    hay = norm(text).casefold()
    return [k for k in keywords if norm(k).casefold() in hay]


# ---------------------------------------------------------------- сеть

def fetch(url: str, timeout: int = 20) -> str:
    r = requests.get(url, headers={"User-Agent": UA}, timeout=timeout)
    r.raise_for_status()
    return r.text


class ParserBroken(Exception):
    """Страница отдалась, но постов в ней не нашлось. Значит вёрстка Telegram
    поменялась и селекторы больше не совпадают. Молчать об этом нельзя:
    внешне всё выглядит рабочим, а уведомления просто перестают приходить."""


def fetch_since(last_id: int):
    """Забирает посты новее last_id.

    Возвращает пару: (новые посты, все посты базовой страницы). Вторая
    половина нужна для отлова правок — редактирование не меняет id, так что
    отследить его можно только сравнением содержимого уже виденных постов.

    Базовая страница отдаёт последние ~20 постов и служит заодно проверкой
    живости парсера. Если между запусками канал успел выдать больше, чем
    помещается на странице, недостающее добираем через ?after=.
    """
    base = parse_posts(fetch(BASE_URL))
    if not base:
        raise ParserBroken("на базовой странице канала не найдено ни одного поста")

    if not last_id:
        return base, base                 # первый запуск: только позиция

    collected = {p["id"]: p for p in base if p["id"] > last_id}

    # разрыв: самый старый пост страницы новее, чем следующий за обработанным
    if min(p["id"] for p in base) > last_id + 1:
        cursor = last_id
        for _ in range(MAX_PAGES):
            page = parse_posts(fetch(f"{BASE_URL}?after={cursor}"))
            fresh = [p for p in page if p["id"] > last_id]
            if not fresh:
                break
            for p in fresh:
                collected[p["id"]] = p
            new_cursor = max(p["id"] for p in fresh)
            if new_cursor <= cursor:
                break
            cursor = new_cursor

    return [collected[k] for k in sorted(collected)], base


def send(token: str, chat_id: str, text: str) -> bool:
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = {
        "chat_id": chat_id,
        "text": text[:TG_LIMIT],
        "disable_web_page_preview": True,
    }
    try:
        r = requests.post(url, json=payload, timeout=20)
        if r.status_code != 200:
            log(f"ОШИБКА Telegram {r.status_code}: {r.text[:200]}")
            return False
        return True
    except requests.RequestException as e:
        log(f"ОШИБКА сети при отправке: {e}")
        return False


# ---------------------------------------------------------------- состояние

def load_state(path: Path):
    """Возвращает (last_id, {id поста: отпечаток текста}).

    Старый формат {"last_id": N} читается как есть — отпечатков в нём просто
    нет, и правки начнут отслеживаться со следующего запуска."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        hashes = {int(k): v for k, v in (data.get("hashes") or {}).items()}
        return int(data["last_id"]), hashes
    except Exception:
        return 0, {}


def save_state(path: Path, last_id: int, hashes: dict) -> None:
    # держим отпечатки только последних постов, иначе файл растёт без предела
    keep = dict(sorted(hashes.items())[-HASH_KEEP:])
    payload = {"last_id": last_id,
               "hashes": {str(k): v for k, v in keep.items()}}
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=1),
                   encoding="utf-8")
    tmp.replace(path)                  # атомарная замена, файл не побьётся


# ---------------------------------------------------------------- проход

def run_once(cfg, dry_run=False, send_first=False) -> int:
    last_id, known = load_state(cfg["state"])
    first_run = last_id == 0

    try:
        posts, base = fetch_since(last_id)
    except ParserBroken as e:
        log(f"ПАРСЕР СЛОМАН: {e}")
        raise                          # наружу, чтобы запуск упал и пришло письмо
    except requests.RequestException as e:
        log(f"канал недоступен: {e}")
        return last_id

    new_max = max([p["id"] for p in posts] + [last_id])

    # новые посты
    hits = [(p, k, False) for p in posts
            if (k := matches(p["text"], cfg["keywords"]))]

    # правки: пост уже видели, но текст стал другим
    edited = 0
    for p in base:
        if p["id"] > last_id:
            continue                   # это не правка, а новый пост
        old = known.get(p["id"])
        if old and old != text_hash(p["text"]):
            edited += 1
            if k := matches(p["text"], cfg["keywords"]):
                hits.append((p, k, True))

    hits.sort(key=lambda h: h[0]["id"])
    log(f"постов получено: {len(posts)} | правок: {edited} | "
        f"к отправке: {len(hits)}")

    fresh_hashes = {**known, **{p["id"]: text_hash(p["text"]) for p in base}}

    if first_run and not send_first and not dry_run:
        log(f"первый запуск, отправку пропускаю. Позиция: {new_max}")
        save_state(cfg["state"], new_max, fresh_hashes)
        return new_max

    for p, keys, was_edited in hits:
        head = "Veolia Jur — ОБНОВЛЕНО — " if was_edited else "Veolia Jur — "
        msg = (f"{head}{', '.join(keys)}\n"
               f"{local_time(p['date'])}\n\n"
               f"{p['text'].strip()}\n\n"
               f"{POST_URL.format(p['id'])}")
        if dry_run:
            print("-" * 60)
            print(msg)
        else:
            ok = send(cfg["token"], cfg["chat_id"], msg)
            mark = " (правка)" if was_edited else ""
            log(f"пост {p['id']}{mark}: {'отправлен' if ok else 'НЕ отправлен'}")
            time.sleep(1)              # не долбим Bot API

    if not dry_run:
        save_state(cfg["state"], new_max, fresh_hashes)
    return new_max


# ---------------------------------------------------------------- самотест

FIXTURE = """
<div class="tgme_widget_message" data-post="VeoliaJur/14409">
  <div class="tgme_widget_message_text">Վթարային ջրանջատում Երևանի Արաբկիր
  վարչական շրջանում<br>կդադարեցվի Աղբյուր Սերոբ փողոցի ջրամատակարարումը:</div>
  <a class="tgme_widget_message_date"><time datetime="2026-08-27T05:47:00+00:00"></time></a>
</div>
<div class="tgme_widget_message" data-post="VeoliaJur/14410">
  <div class="tgme_widget_message_text">Պլանային ջրանջատում Քանաքեռ-Զեյթուն
  վարչական շրջանում<br>կդադարեցվի Ազատության պող. 24, 26 շենքերի
  ջրամատակարարումը:</div>
  <a class="tgme_widget_message_date"><time datetime="2026-08-27T06:12:00+00:00"></time></a>
</div>
<div class="tgme_widget_message" data-post="VeoliaJur/14411">
  <div class="tgme_widget_message_text">Վթարային ջրանջատում Կենտրոն
  վարչական շրջանում Ազատության հրապարակ հարակից տարածքում:</div>
  <a class="tgme_widget_message_date"><time datetime="2026-08-27T07:00:00+00:00"></time></a>
</div>
<div class="tgme_widget_message" data-post="VeoliaJur/14412">
  <a class="tgme_widget_message_date"><time datetime="2026-08-27T08:00:00+00:00"></time></a>
</div>
"""


def selftest() -> int:
    posts = parse_posts(FIXTURE)
    assert len(posts) == 3, f"постов с текстом должно быть 3, получено {len(posts)}"
    assert [p["id"] for p in posts] == [14409, 14410, 14411], "id или порядок не те"
    assert posts[0]["date"].startswith("2026-08-27"), "дата не распозналась"

    hit = [p["id"] for p in posts if matches(p["text"], DEFAULT_KEYWORDS)]
    assert hit == [14410, 14411], f"по ключу должны найтись 14410 и 14411, найдено {hit}"

    assert "\n" in posts[0]["text"], "перенос строки из <br> потерян"
    assert matches("АЗԱՏՈՒԹՅԱՆ պող.".replace("АЗ", "Ազ"), ["ազատության"]), "регистр не игнорируется"
    assert not matches("Աղբյուր Սերոբ փողոց", DEFAULT_KEYWORDS), "ложное срабатывание"

    print("парсер: 4 блока -> 3 поста с текстом, id и даты верны")
    print("фильтр: 14410 (проспект) и 14411 (площадь) — оба содержат ключ")
    print("        14409 (Աղբյուր Սերոբ) отсеян")

    # --- поведение сети подменяем, чтобы проверить логику без выхода наружу
    # именно текущий модуль: повторный импорт создал бы второй его экземпляр,
    # и ParserBroken оказался бы другим классом, который except не поймает
    M = sys.modules[__name__]

    def block(_url, timeout=20):
        raise AssertionError("лишний сетевой запрос: " + _url)

    real_fetch, real_send = M.fetch, M.send

    # 1) пустая страница должна возбуждать ParserBroken
    M.fetch = lambda url, timeout=20: "<html><body>ничего</body></html>"
    try:
        M.fetch_since(0)
        raise AssertionError("пустая страница не распознана как поломка")
    except ParserBroken:
        pass
    print("детект поломки: пустая страница -> ParserBroken")

    # 2) разрыв больше страницы -> добор через ?after=
    def paged(url, timeout=20):
        if "after=" in url:
            return "".join(FIXTURE.split("<div class=\"tgme_widget_message\"")[1:2]
                           and [f'<div class="tgme_widget_message" data-post="VeoliaJur/{i}">'
                                f'<div class="tgme_widget_message_text">Ազատության {i}</div>'
                                f'<a class="tgme_widget_message_date"><time datetime="2026-08-27T05:00:00+00:00">'
                                f'</time></a></div>' for i in (14405, 14406)])
        return "".join(f'<div class="tgme_widget_message" data-post="VeoliaJur/{i}">'
                       f'<div class="tgme_widget_message_text">пост {i}</div>'
                       f'<a class="tgme_widget_message_date"><time datetime="2026-08-27T09:00:00+00:00">'
                       f'</time></a></div>' for i in (14409, 14410))

    M.fetch = paged
    got = [p["id"] for p in M.fetch_since(14404)[0]]
    assert got == [14405, 14406, 14409, 14410], f"добор пропусков не сработал: {got}"
    print("добор пропусков: разрыв 14405-14406 подтянут через ?after=")

    # 3) без разрыва второй запрос делаться не должен
    def once(url, timeout=20):
        if "after=" in url:
            block(url)
        return "".join(f'<div class="tgme_widget_message" data-post="VeoliaJur/{i}">'
                       f'<div class="tgme_widget_message_text">пост {i}</div>'
                       f'<a class="tgme_widget_message_date"><time datetime="2026-08-27T09:00:00+00:00">'
                       f'</time></a></div>' for i in (14409, 14410))

    M.fetch = once
    got = [p["id"] for p in M.fetch_since(14408)[0]]
    assert got == [14409, 14410], f"лишние или потерянные посты: {got}"
    print("экономия запросов: без разрыва вторая страница не запрашивается")

    M.fetch = real_fetch

    # 4) перевод времени: UTC 05:40 -> Ереван 09:40
    got = local_time("2026-09-04T05:40:00+00:00")
    assert got == "2026-09-04 09:40 (Ереван)", f"перевод времени неверен: {got}"
    assert local_time("") == "время неизвестно", "пустая дата не обработана"
    print("время: 05:40 UTC -> 09:40 (Ереван)")

    # 5) сквозной прогон: новый пост, затем его правка
    import tempfile

    def page_with(text):
        return (f'<div class="tgme_widget_message" data-post="VeoliaJur/14600">'
                f'<div class="tgme_widget_message_text">{text}</div>'
                f'<a class="tgme_widget_message_date">'
                f'<time datetime="2026-09-04T05:40:00+00:00"></time></a></div>')

    sent = []
    M.send = lambda token, chat, msg: (sent.append(msg), True)[1]

    with tempfile.TemporaryDirectory() as tmp:
        cfg = {"token": "x", "chat_id": "1", "keywords": DEFAULT_KEYWORDS,
               "state": Path(tmp) / "state.json"}

        # первый проход: позиция запоминается, отправки нет
        M.fetch = lambda url, timeout=20: page_with("Ազատության 1-2 шенкери")
        M.run_once(cfg)
        assert sent == [], "первый запуск не должен ничего слать"
        lid, hashes = load_state(cfg["state"])
        assert lid == 14600 and 14600 in hashes, f"позиция/отпечаток не легли: {lid}"

        # второй проход: текст тот же -> тишина
        M.run_once(cfg)
        assert sent == [], "неизменённый пост не должен уходить повторно"

        # третий проход: пост отредактирован -> уходит с пометкой
        M.fetch = lambda url, timeout=20: page_with("Ազատության 1-2, 4-4/2 шенкери")
        M.run_once(cfg)
        assert len(sent) == 1, f"правка не отправлена, сообщений: {len(sent)}"
        assert "ОБНОВЛЕНО" in sent[0], "нет пометки об обновлении"
        assert "09:40 (Ереван)" in sent[0], "в сообщении не ереванское время"

        # четвёртый проход: повторов быть не должно
        M.run_once(cfg)
        assert len(sent) == 1, "правка ушла повторно"

    print("правки: новый -> тишина -> правка с пометкой -> тишина")
    M.fetch, M.send = real_fetch, real_send
    print("selftest OK")
    return 0


# ---------------------------------------------------------------- точка входа

def main() -> int:
    ap = argparse.ArgumentParser(description="Слежение за отключениями воды Veolia Jur")
    ap.add_argument("--dry-run", action="store_true", help="показать находки, не отправлять")
    ap.add_argument("--send-first", action="store_true", help="отправить и на первом запуске")
    ap.add_argument("--loop", type=int, metavar="СЕК", help="крутиться в цикле с паузой")
    ap.add_argument("--selftest", action="store_true", help="проверить парсер без сети")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    kw = os.environ.get("VEOLIA_KEYWORDS", "")
    cfg = {
        "token": os.environ.get("VEOLIA_BOT_TOKEN", ""),
        "chat_id": os.environ.get("VEOLIA_CHAT_ID", ""),
        "keywords": [k.strip() for k in kw.split(",") if k.strip()] or DEFAULT_KEYWORDS,
        "state": Path(os.environ.get(
            "VEOLIA_STATE", Path(__file__).with_name("veolia_state.json"))),
    }

    if not args.dry_run and not (cfg["token"] and cfg["chat_id"]):
        print("Не заданы VEOLIA_BOT_TOKEN и/или VEOLIA_CHAT_ID.", file=sys.stderr)
        print("Проверить парсер без них: python veolia_watch.py --dry-run", file=sys.stderr)
        return 2

    log(f"ключи: {', '.join(cfg['keywords'])} | состояние: {cfg['state']}")

    if args.loop:
        while True:
            try:
                run_once(cfg, args.dry_run, args.send_first)
            except Exception as e:                      # цикл не должен падать
                log(f"необработанная ошибка: {e!r}")
            time.sleep(args.loop)
    else:
        run_once(cfg, args.dry_run, args.send_first)
    return 0


if __name__ == "__main__":
    sys.exit(main())
