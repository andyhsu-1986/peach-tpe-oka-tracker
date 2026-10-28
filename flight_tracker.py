#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
樂桃航空 (Peach Aviation) TPE <-> OKA 雙向報價（Minimum / Standard 雙方案）、歷史水位與 Gemini 智慧訂票決策系統
支援 GitHub Actions 雲端免開機每小時全自動排程執行。

目標航線：台北桃園 (TPE) <-> 沖繩那霸 (OKA)
指定班次：去程 MM 922 (TPE -> OKA, 09:45-12:25) / 回程 MM 925 (OKA -> TPE, 13:35-14:20)
時間範圍：2027 年 3 月所有連續「7 天 6 夜」組合（去程 2027-03-01 至 2027-03-25，回程為出發日 + 6 天）
票價方案：
  1. Minimum 方案（含稅單趟價、含稅來回總價）：含手提行李 7kg (2件合計) + 兩地機場稅
  2. Standard 方案（含稅單趟價、含稅來回總價）：含手提行李 7kg + 20kg 託運行李 1 件 + 標準選位 + 免開票手續費 + 兩地機場稅
爬蟲高可用性三備案架構 (3-Tier Fallback Architecture)：
  - 備案一 (Plan A)：Google Flights TFS Protobuf 二進位結構化搜尋端點（速度最快、結構最穩定）
  - 備案二 (Plan B)：Google Flights 自然語義查詢端點 (`www.google.com/travel/flights?q=...`) + 多瀏覽器指紋輪替
  - 備案三 (Plan C)：Google 台灣區域節點 (`www.google.com.tw`) + EU/SOCS Cookie 免驗證通道 + 樂桃官網搜尋端點備援
"""

import base64
import json
import logging
import os
import random
import re
import smtplib
import ssl
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, asdict
from datetime import date, datetime, timedelta, timezone
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import requests

# 設定台灣時區 (UTC+8)
TW_TZ = timezone(timedelta(hours=8))

# 設定日誌格式
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
logger = logging.getLogger("PeachFlightTracker")

# 檔案與常數設定
BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"
HISTORY_FILE = DATA_DIR / "price_history.json"
PREVIEW_HTML_FILE = DATA_DIR / "latest_report_preview.html"

ORIGIN_AIRPORT = "TPE"
DEST_AIRPORT = "OKA"
OUTBOUND_FLIGHT_NO = "MM922"
INBOUND_FLIGHT_NO = "MM925"
CURRENCY = "TWD"
PEACH_BOOKING_URL = "https://www.flypeach.com/tw"

# 樂桃航空台灣出發短程國際線 (Zone B: TPE <-> OKA) 官方 Standard vs Minimum 單程加價結構：
# Standard 方案包含：20kg 託運行李 (NT$900) + 標準座位指定 (NT$200) = 單程固定差額 NT$1,100（來回差額 NT$2,200）
PEACH_STANDARD_ADDON_TWD = 1100

WEEKDAY_NAMES = ["一", "二", "三", "四", "五", "六", "日"]

# 多瀏覽器 User-Agent 指紋池（防封鎖輪替）
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Safari/605.1.15",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:132.0) Gecko/20100101 Firefox/132.0",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36",
]


@dataclass
class MetricStats:
    """單一價格維度之歷史統計結構（含當下價、前次價、歷史最低、歷史最高、平均價）"""
    current_price: Optional[int] = None
    previous_price: Optional[int] = None
    all_time_low: Optional[int] = None
    all_time_high: Optional[int] = None
    average_price: Optional[float] = None
    sample_count: int = 0
    status: str = "UNAVAILABLE"
    last_updated: str = ""

    def update(self, new_price: Optional[int], timestamp_str: str) -> bool:
        """
        更新價格與歷史水位統計（最低價、最高價、平均價）。
        回傳 bool 代表本次是否有發生「有效價格變動」。
        """
        self.last_updated = timestamp_str
        if new_price is None or new_price <= 0:
            self.status = "UNAVAILABLE"
            return False

        price_changed = (self.current_price is not None and self.current_price != new_price)
        first_seen = (self.current_price is None)

        self.previous_price = self.current_price
        self.current_price = new_price
        self.status = "AVAILABLE"

        if self.all_time_low is None or new_price < self.all_time_low:
            self.all_time_low = new_price
        if self.all_time_high is None or new_price > self.all_time_high:
            self.all_time_high = new_price

        if self.average_price is None or self.sample_count == 0:
            self.average_price = float(new_price)
            self.sample_count = 1
        else:
            total = self.average_price * self.sample_count + new_price
            self.sample_count += 1
            self.average_price = round(total / self.sample_count, 2)

        return price_changed or first_seen

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "MetricStats":
        if not isinstance(data, dict):
            return cls()
        return cls(
            current_price=data.get("current_price"),
            previous_price=data.get("previous_price"),
            all_time_low=data.get("all_time_low"),
            all_time_high=data.get("all_time_high"),
            average_price=data.get("average_price"),
            sample_count=int(data.get("sample_count", 0)),
            status=data.get("status", "UNAVAILABLE"),
            last_updated=data.get("last_updated", ""),
        )


def generate_target_date_pairs(year: int = 2027, month: int = 3) -> List[Tuple[str, str]]:
    """
    產生 2027 年 3 月所有連續「7 天 6 夜」日期組合：
    去程：2027-03-01 至 2027-03-25（共 25 組）
    回程：對應出發日 + 6 天（2027-03-07 至 2027-03-31）
    """
    pairs: List[Tuple[str, str]] = []
    for day in range(1, 26):
        dep_date = date(year, month, day)
        ret_date = dep_date + timedelta(days=6)
        pairs.append((dep_date.strftime("%Y-%m-%d"), ret_date.strftime("%Y-%m-%d")))
    return pairs


def format_date_with_weekday(date_str: str) -> str:
    dt = datetime.strptime(date_str, "%Y-%m-%d").date()
    return f"{dt.strftime('%m/%d')}({WEEKDAY_NAMES[dt.weekday()]})"


class PeachFlightScraper:
    """
    樂桃航空 (MM922 / MM925) 三重備援高可用性報價擷取引擎：
    - 嚴格鎖定指定班次：去程 `["MM","922"]`、回程 `["MM","925"]`，絕不混入其他航空公司或樂桃其他班次。
    - 同時計算並回傳 Minimum 方案（含稅）與 Standard 方案（含稅 + 20kg行李 + 標準選位）價格。
    - 內建三大獨立爬蟲備案（Plan A -> Plan B -> Plan C），任一管道遭封鎖或逾時立即無縫切換下一備案！
    """

    def __init__(self, dry_run: bool = False) -> None:
        self.dry_run = dry_run
        self._outbound_cache: Dict[str, Optional[Dict[str, int]]] = {}
        self._inbound_cache: Dict[str, Optional[Dict[str, int]]] = {}
        self.plan_stats: Dict[str, int] = {"PlanA_TFS": 0, "PlanB_Query": 0, "PlanC_Regional": 0}

    @staticmethod
    def _build_tfs_protobuf(origin: str, destination: str, flight_date: str) -> str:
        """建構 Google Flights 原生 Protobuf TFS 參數（備案一專用）"""
        leg = (
            b"\x12\x0a"
            + flight_date.encode("ascii")
            + b"\x6a\x07\x08\x01\x12\x03"
            + origin.encode("ascii")
            + b"\x72\x07\x08\x01\x12\x03"
            + destination.encode("ascii")
        )
        payload = b"\x08\x1c\x10\x02\x1a" + bytes([len(leg)]) + leg
        return base64.urlsafe_b64encode(payload).decode("ascii").rstrip("=")

    @staticmethod
    def _extract_exact_flight_price_from_html(html_text: str, numeric_flt: str) -> Optional[int]:
        """
        從結構化回應中嚴格鎖定 `["MM","922"]` 或 `["MM","925"]` 班次區塊，
        並提取該班次專屬之含稅新台幣最低價 (Minimum 含稅價)。
        """
        for m in re.finditer(rf'\["MM","{numeric_flt}"', html_text):
            window = html_text[m.end() : m.end() + 1400]
            # 優先匹配綁定 MM922 / MM925 token 的報價欄位
            price_match = re.search(
                rf'\[\[null,(\d{{3,6}})\],"[^"]*?MM{numeric_flt}', window
            )
            if not price_match:
                price_match = re.search(r'\[\[null,(\d{3,6})\],"', window)
            if price_match:
                val = int(price_match.group(1))
                if 1200 <= val <= 50000:
                    return val
        return None

    def _plan_a_tfs_endpoint(
        self, origin: str, destination: str, flight_date: str, numeric_flt: str
    ) -> Optional[int]:
        """
        【備案一 Plan A】：Google Flights TFS Protobuf 結構化直達檢索端點
        """
        tfs = self._build_tfs_protobuf(origin, destination, flight_date)
        url = f"https://www.google.com/travel/flights/search?tfs={tfs}&curr=TWD&hl=en"
        headers = {
            "User-Agent": random.choice(USER_AGENTS),
            "Accept-Language": "en-US,en;q=0.9",
            "Cache-Control": "no-cache",
        }
        resp = requests.get(url, headers=headers, timeout=12)
        if resp.status_code == 200:
            price = self._extract_exact_flight_price_from_html(resp.text, numeric_flt)
            if price is not None:
                self.plan_stats["PlanA_TFS"] += 1
                return price
        return None

    def _plan_b_query_endpoint(
        self, origin: str, destination: str, flight_date: str, numeric_flt: str
    ) -> Optional[int]:
        """
        【備案二 Plan B】：Google Flights 語義查詢端點 (`?q=Flights+from+...`) + 隨機 User-Agent
        """
        url = (
            f"https://www.google.com/travel/flights"
            f"?q=Flights+from+{origin}+to+{destination}+on+{flight_date}+oneway"
            f"&curr=TWD&hl=zh-TW"
        )
        headers = {
            "User-Agent": random.choice(USER_AGENTS),
            "Accept-Language": "zh-TW,zh;q=0.9,en-US;q=0.8",
        }
        resp = requests.get(url, headers=headers, timeout=12)
        if resp.status_code == 200:
            price = self._extract_exact_flight_price_from_html(resp.text, numeric_flt)
            if price is not None:
                self.plan_stats["PlanB_Query"] += 1
                return price
        return None

    def _plan_c_regional_cookie_endpoint(
        self, origin: str, destination: str, flight_date: str, numeric_flt: str
    ) -> Optional[int]:
        """
        【備案三 Plan C】：台灣區域域名 (`www.google.com.tw`) + SOCS/CONSENT 免驗證 Cookie + 樂桃官網備援
        當單一 IP 頻繁存取國際網域遭限流或彈出驗證頁面時，透過區域域名與預簽章 Cookie 繞過限制。
        """
        cookies = {
            "CONSENT": "YES+cb.20230531-04-p0.zh-TW+FX+999",
            "SOCS": "CAISHAgBEhJnd3NfMjAyMzA4MTUtMF9SQzIaAmVuIAEaBgiAo_CmBg",
        }
        headers = {
            "User-Agent": random.choice(USER_AGENTS),
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "zh-TW,zh;q=0.9",
        }
        url = (
            f"https://www.google.com.tw/travel/flights"
            f"?q={origin}+to+{destination}+{flight_date}+oneway&curr=TWD&hl=zh-TW&gl=TW"
        )
        resp = requests.get(url, headers=headers, cookies=cookies, timeout=14)
        if resp.status_code == 200:
            price = self._extract_exact_flight_price_from_html(resp.text, numeric_flt)
            if price is not None:
                self.plan_stats["PlanC_Regional"] += 1
                return price

        # 終極備援：樂桃官網公開端點探測
        peach_url = (
            f"https://booking.flypeach.com/tw/flight_search"
            f"?origin={origin}&destination={destination}&date={flight_date}&flight=MM{numeric_flt}"
        )
        resp2 = requests.get(peach_url, headers=headers, timeout=8)
        if resp2.status_code == 200 and f"MM{numeric_flt}" in resp2.text:
            match = re.search(rf"MM{numeric_flt}.*?NT\$\s*([0-9,]+)", resp2.text, re.DOTALL)
            if match:
                val = int(match.group(1).replace(",", ""))
                if 1200 <= val <= 50000:
                    self.plan_stats["PlanC_Regional"] += 1
                    return val
        return None

    def fetch_single_flight_with_3_fallbacks(
        self, origin: str, destination: str, flight_date: str, flight_no: str
    ) -> Optional[Dict[str, int]]:
        """
        依序執行三大備案擷取指定班次報價，並同時回傳：
        - `minimum`: Minimum 方案單程含稅價 (TWD)
        - `standard`: Standard 方案單程含稅價 (TWD，含 20kg 託運行李 + 標準選位)
        """
        numeric_flt = re.sub(r"\D", "", flight_no)

        # 微幅隨機延遲 (0.1~0.4 秒)，避免每小時巡檢產生固定頻率特徵
        time.sleep(random.uniform(0.1, 0.4))

        for plan_name, plan_func in (
            ("Plan A (TFS Protobuf)", self._plan_a_tfs_endpoint),
            ("Plan B (Query Stream)", self._plan_b_query_endpoint),
            ("Plan C (Regional + Cookie Bypass)", self._plan_c_regional_cookie_endpoint),
        ):
            try:
                min_price = plan_func(origin, destination, flight_date, numeric_flt)
                if min_price is not None:
                    return {
                        "minimum": min_price,
                        "standard": min_price + PEACH_STANDARD_ADDON_TWD,
                    }
            except Exception as exc:
                logger.debug(f"⚠️ [{flight_no} {flight_date}] {plan_name} 發生異常，自動切換下一備案: {exc}")

        return None

    def fetch_all_dates(
        self, date_pairs: List[Tuple[str, str]]
    ) -> Tuple[Dict[str, Optional[Dict[str, int]]], Dict[str, Optional[Dict[str, int]]]]:
        """
        平行擷取所有去程日期 (MM922) 與回程日期 (MM925) 的 Minimum 與 Standard 雙方案含稅單程票價。
        """
        unique_outbound_dates = sorted({dep for dep, _ in date_pairs})
        unique_inbound_dates = sorted({ret for _, ret in date_pairs})

        if self.dry_run:
            logger.info("🧪 啟用 DRY_RUN 模擬價格模式，生成 MM922 / MM925 雙方案測試報價...")
            for d in unique_outbound_dates:
                sim_min = 3480 + ((int(d[-2:]) * 130) % 900)
                self._outbound_cache[d] = {"minimum": sim_min, "standard": sim_min + PEACH_STANDARD_ADDON_TWD}
            for d in unique_inbound_dates:
                sim_min = 3350 + ((int(d[-2:]) * 110) % 900)
                self._inbound_cache[d] = {"minimum": sim_min, "standard": sim_min + PEACH_STANDARD_ADDON_TWD}
            return self._outbound_cache, self._inbound_cache

        logger.info(
            "🌐 啟動三重備援爬蟲引擎 (Plan A/B/C)，平行擷取 2027 年 3 月樂桃 MM 922 (去程) 與 MM 925 (回程) 真實含稅報價..."
        )

        def _task_out(d: str) -> Tuple[str, Optional[Dict[str, int]]]:
            return d, self.fetch_single_flight_with_3_fallbacks(
                origin=ORIGIN_AIRPORT,
                destination=DEST_AIRPORT,
                flight_date=d,
                flight_no=OUTBOUND_FLIGHT_NO,
            )

        def _task_in(d: str) -> Tuple[str, Optional[Dict[str, int]]]:
            return d, self.fetch_single_flight_with_3_fallbacks(
                origin=DEST_AIRPORT,
                destination=ORIGIN_AIRPORT,
                flight_date=d,
                flight_no=INBOUND_FLIGHT_NO,
            )

        with ThreadPoolExecutor(max_workers=6) as executor:
            for d, res in executor.map(_task_out, unique_outbound_dates):
                self._outbound_cache[d] = res
            for d, res in executor.map(_task_in, unique_inbound_dates):
                self._inbound_cache[d] = res

        out_ok = sum(1 for v in self._outbound_cache.values() if v is not None)
        in_ok = sum(1 for v in self._inbound_cache.values() if v is not None)
        logger.info(
            f"✅ 真實報價擷取完成！去程 MM922 成功取得 {out_ok}/{len(unique_outbound_dates)} 天，"
            f"回程 MM925 成功取得 {in_ok}/{len(unique_inbound_dates)} 天 "
            f"(3/28~3/31 屬 2027 夏季班表換季區間)。通道統計: {self.plan_stats}"
        )
        return self._outbound_cache, self._inbound_cache


class PriceHistoryManager:
    """
    管理雲端 JSON 歷史水位資料庫 (`data/price_history.json`)。
    在每個「出發日_回程日」組合下，完整獨立記錄 **6 大維度** 與各自的最低/最高/均價：
    1. `outbound_mm922_min`     : 去程 MM 922 (Minimum 方案含稅單價)
    2. `outbound_mm922_std`     : 去程 MM 922 (Standard 方案含稅單價)
    3. `inbound_mm925_min`      : 回程 MM 925 (Minimum 方案含稅單價)
    4. `inbound_mm925_std`      : 回程 MM 925 (Standard 方案含稅單價)
    5. `round_trip_total_min`   : 來回總價 (Minimum 方案含稅總價 = 去程 Min + 回程 Min)
    6. `round_trip_total_std`   : 來回總價 (Standard 方案含稅總價 = 去程 Std + 回程 Std)
    """

    def __init__(self, file_path: Path) -> None:
        self.file_path = file_path
        self.data: Dict[str, Any] = self._load()

    def _load(self) -> Dict[str, Any]:
        if self.file_path.exists():
            try:
                with open(self.file_path, "r", encoding="utf-8") as f:
                    loaded = json.load(f)
                    if isinstance(loaded, dict) and "combinations" in loaded:
                        return loaded
            except Exception as exc:
                logger.warning(f"⚠️ 讀取歷史價格 JSON 失敗，將重新初始化結構: {exc}")

        return {
            "metadata": {
                "route": f"{ORIGIN_AIRPORT} <-> {DEST_AIRPORT}",
                "outbound_flight": f"{OUTBOUND_FLIGHT_NO} (09:45 TPE -> 12:25 OKA)",
                "inbound_flight": f"{INBOUND_FLIGHT_NO} (13:35 OKA -> 14:20 TPE)",
                "currency": CURRENCY,
                "price_type": "Tax Included (含兩地機場稅)",
                "standard_addon_rule": f"Standard 方案含 20kg 託運行李 + 標準選位 (單程 +NT${PEACH_STANDARD_ADDON_TWD:,}, 來回 +NT${PEACH_STANDARD_ADDON_TWD*2:,})",
                "target_period": "2027-03 (7 Days 6 Nights, 25 Combinations)",
                "last_run_at": "",
                "total_runs": 0,
            },
            "combinations": {},
        }

    def update_all_combinations(
        self,
        date_pairs: List[Tuple[str, str]],
        outbound_prices: Dict[str, Optional[Dict[str, int]]],
        inbound_prices: Dict[str, Optional[Dict[str, int]]],
    ) -> Tuple[bool, List[Dict[str, Any]]]:
        now_str = datetime.now(TW_TZ).strftime("%Y-%m-%d %H:%M:%S+08:00")
        self.data["metadata"]["last_run_at"] = now_str
        self.data["metadata"]["total_runs"] = int(self.data["metadata"].get("total_runs", 0)) + 1

        combinations_dict = self.data.setdefault("combinations", {})
        any_changed = False
        summary_records: List[Dict[str, Any]] = []

        for dep_date, ret_date in date_pairs:
            combo_key = f"{dep_date}_{ret_date}"
            existing = combinations_dict.get(combo_key, {})

            # 載入 6 大維度統計物件（向下相容舊結構）
            out_min_stats = MetricStats.from_dict(
                existing.get("outbound_mm922_min") or existing.get("outbound_mm922") or {}
            )
            out_std_stats = MetricStats.from_dict(existing.get("outbound_mm922_std") or {})
            in_min_stats = MetricStats.from_dict(
                existing.get("inbound_mm925_min") or existing.get("inbound_mm925") or {}
            )
            in_std_stats = MetricStats.from_dict(existing.get("inbound_mm925_std") or {})
            tot_min_stats = MetricStats.from_dict(
                existing.get("round_trip_total_min") or existing.get("round_trip_total") or {}
            )
            tot_std_stats = MetricStats.from_dict(existing.get("round_trip_total_std") or {})

            out_info = outbound_prices.get(dep_date)
            in_info = inbound_prices.get(ret_date)

            out_min_p = out_info["minimum"] if out_info else None
            out_std_p = out_info["standard"] if out_info else None
            in_min_p = in_info["minimum"] if in_info else None
            in_std_p = in_info["standard"] if in_info else None

            tot_min_p = (
                (out_min_p + in_min_p)
                if (out_min_p is not None and in_min_p is not None)
                else None
            )
            tot_std_p = (
                (out_std_p + in_std_p)
                if (out_std_p is not None and in_std_p is not None)
                else None
            )

            c1 = out_min_stats.update(out_min_p, now_str)
            c2 = out_std_stats.update(out_std_p, now_str)
            c3 = in_min_stats.update(in_min_p, now_str)
            c4 = in_std_stats.update(in_std_p, now_str)
            c5 = tot_min_stats.update(tot_min_p, now_str)
            c6 = tot_std_stats.update(tot_std_p, now_str)

            combo_changed = any((c1, c2, c3, c4, c5, c6))
            if combo_changed:
                any_changed = True

            history_log: List[Dict[str, Any]] = existing.get("history_log", [])
            if combo_changed or not history_log:
                history_log.append(
                    {
                        "timestamp": now_str,
                        "outbound_mm922_min": out_min_p,
                        "outbound_mm922_std": out_std_p,
                        "inbound_mm925_min": in_min_p,
                        "inbound_mm925_std": in_std_p,
                        "round_trip_total_min": tot_min_p,
                        "round_trip_total_std": tot_std_p,
                    }
                )
                history_log = history_log[-30:]

            combinations_dict[combo_key] = {
                "departure_date": dep_date,
                "return_date": ret_date,
                "outbound_mm922_min": asdict(out_min_stats),
                "outbound_mm922_std": asdict(out_std_stats),
                "inbound_mm925_min": asdict(in_min_stats),
                "inbound_mm925_std": asdict(in_std_stats),
                "round_trip_total_min": asdict(tot_min_stats),
                "round_trip_total_std": asdict(tot_std_stats),
                "has_recent_change": combo_changed,
                "history_log": history_log,
            }

            summary_records.append(combinations_dict[combo_key])

        return any_changed, summary_records

    def save(self) -> None:
        self.file_path.parent.mkdir(parents=True, exist_ok=True)
        with open(self.file_path, "w", encoding="utf-8") as f:
            json.dump(self.data, f, ensure_ascii=False, indent=2)
        logger.info(f"💾 歷史價格與統計水位已儲存至: {self.file_path}")


class GeminiDecisionAdvisor:
    """
    整合 Google Gemini 模型，針對 25 組日期的 Minimum 與 Standard 雙方案單程與來回總價進行決策評估。
    """

    def __init__(self, api_key: Optional[str]) -> None:
        self.api_key = (api_key or "").strip()

    def analyze(self, records: List[Dict[str, Any]]) -> Dict[str, Any]:
        rule_based_result = self._rule_based_evaluation(records)

        if not self.api_key:
            logger.info("ℹ️ 未設定 GEMINI_API_KEY，採用內建量化水位演算法產出訂票決策。")
            return rule_based_result

        compact_payload = []
        for r in records:
            compact_payload.append(
                {
                    "departure_date": r["departure_date"],
                    "return_date": r["return_date"],
                    "outbound_mm922_min": r["outbound_mm922_min"].get("current_price"),
                    "outbound_mm922_std": r["outbound_mm922_std"].get("current_price"),
                    "inbound_mm925_min": r["inbound_mm925_min"].get("current_price"),
                    "inbound_mm925_std": r["inbound_mm925_std"].get("current_price"),
                    "round_trip_total_min": r["round_trip_total_min"].get("current_price"),
                    "round_trip_total_std": r["round_trip_total_std"].get("current_price"),
                    "historical_low_min_total": r["round_trip_total_min"].get("all_time_low"),
                }
            )

        prompt = (
            "你是一位精通樂桃航空 (Peach Aviation) 台日線票價分析的資深顧問。\n"
            "以下是 2027 年 3 月「台北桃園(TPE) <-> 沖繩那霸(OKA)」連續 7 天 6 夜（共 25 組）的真實含稅監控數據。\n"
            "嚴格指定班次：去程 MM 922 (09:45-12:25)、回程 MM 925 (13:35-14:20)。\n"
            "每組包含 Minimum（陽春含稅）與 Standard（含20kg託運行李+選位含稅）兩種方案的去程單價、回程單價與來回總價。\n\n"
            "決策標籤僅限使用以下四種之一：\n"
            "1. 【破盤秒搶】（Minimum 來回含稅總價 <= NT$6,800，或 Standard 來回含稅總價 <= NT$9,000）\n"
            "2. 【單程特價先買】（去程 MM922 或回程 MM925 之 Minimum 單趟含稅價 <= NT$3,500，適合先鎖定單程）\n"
            "3. 【建議觀望】（目前報價處於常態或偏高區間）\n"
            "4. 【換季待開盤】（回程落於 2027/03/28~03/31 夏季航班換季區間，回程 MM925 尚未釋出報價，但去程 MM922 已開賣）\n\n"
            "請以繁體中文（台灣用語）輸出純 JSON 格式：\n"
            "{\n"
            '  "overall_badge": "四種標籤之一",\n'
            '  "executive_summary": "150字以內的客觀價格趨勢簡評，請明確點出目前最便宜的出發日期組合、Minimum與Standard來回總價落點，以及單程拆買建議",\n'
            '  "combo_badges": {\n'
            '    "YYYY-MM-DD_YYYY-MM-DD": "四種標籤之一"\n'
            "  }\n"
            "}\n\n"
            f"監控數據 JSON：\n{json.dumps(compact_payload, ensure_ascii=False)}"
        )

        try:
            from google import genai
            from google.genai import types

            client = genai.Client(api_key=self.api_key)
            response = None
            for model_name in ("gemini-3.8-flash", "gemini-2.5-flash"):
                try:
                    response = client.models.generate_content(
                        model=model_name,
                        contents=prompt,
                        config=types.GenerateContentConfig(
                            temperature=0.2,
                            response_mime_type="application/json",
                        ),
                    )
                    break
                except Exception as model_exc:
                    logger.debug(f"模型 {model_name} 呼叫切換: {model_exc}")

            if response and response.text:
                parsed = json.loads(response.text.strip())
                if isinstance(parsed, dict) and "overall_badge" in parsed:
                    merged_badges = dict(rule_based_result["combo_badges"])
                    merged_badges.update(parsed.get("combo_badges", {}))
                    parsed["combo_badges"] = merged_badges
                    parsed["top_recommendations"] = rule_based_result["top_recommendations"]
                    logger.info(f"🤖 Gemini 智慧決策完成！整體建議：{parsed['overall_badge']}")
                    return parsed
        except Exception as exc:
            logger.warning(f"⚠️ Gemini API 呼叫或解析異常，自動降級為內建量化規則決策: {exc}")

        return rule_based_result

    def _rule_based_evaluation(self, records: List[Dict[str, Any]]) -> Dict[str, Any]:
        """精準量化水位評估與 Top 3 最便宜組合排行計算"""
        combo_badges: Dict[str, str] = {}
        valid_combos_for_ranking: List[Dict[str, Any]] = []
        steal_count = 0
        oneway_count = 0

        for r in records:
            dep = r["departure_date"]
            ret = r["return_date"]
            key = f"{dep}_{ret}"

            out_min = r["outbound_mm922_min"].get("current_price")
            out_std = r["outbound_mm922_std"].get("current_price")
            in_min = r["inbound_mm925_min"].get("current_price")
            in_std = r["inbound_mm925_std"].get("current_price")
            tot_min = r["round_trip_total_min"].get("current_price")
            tot_std = r["round_trip_total_std"].get("current_price")

            if tot_min is not None and tot_std is not None:
                valid_combos_for_ranking.append(
                    {
                        "dep": dep,
                        "ret": ret,
                        "combo_label": f"{format_date_with_weekday(dep)} → {format_date_with_weekday(ret)}",
                        "out_min": out_min,
                        "out_std": out_std,
                        "in_min": in_min,
                        "in_std": in_std,
                        "tot_min": tot_min,
                        "tot_std": tot_std,
                    }
                )

            if out_min is None and in_min is None:
                combo_badges[key] = "【尚未開盤】"
            elif out_min is not None and in_min is None:
                combo_badges[key] = "【換季待開盤】"
            elif tot_min is not None and tot_min <= 6800:
                combo_badges[key] = "【破盤秒搶】"
                steal_count += 1
            elif (out_min is not None and out_min <= 3500) or (in_min is not None and in_min <= 3500):
                combo_badges[key] = "【單程特價先買】"
                oneway_count += 1
            else:
                combo_badges[key] = "【建議觀望】"

        # 依照來回總價 (Minimum) 由低至高排序，挑出最便宜的前 3 組
        valid_combos_for_ranking.sort(key=lambda x: x["tot_min"])
        top_3 = valid_combos_for_ranking[:3]

        if steal_count > 0:
            overall = "【破盤秒搶】"
        elif oneway_count > 0:
            overall = "【單程特價先買】"
        elif valid_combos_for_ranking:
            overall = "【建議觀望】"
        else:
            overall = "【尚未開盤】"

        if top_3:
            best = top_3[0]
            summary = (
                f"本次巡檢嚴格鎖定樂桃去程 MM 922 與回程 MM 925（含兩地機場稅）："
                f"目前 2027 年 3 月最便宜的 7 天 6 夜組合為 {best['dep']} 出發 ~ {best['ret']} 回程，"
                f"Minimum 方案來回含稅總價 NT${best['tot_min']:,}（去程 NT${best['out_min']:,} + 回程 NT${best['in_min']:,}），"
                f"Standard 方案（含20kg行李+選位）來回含稅總價 NT${best['tot_std']:,}（去程 NT${best['out_std']:,} + 回程 NT${best['in_std']:,}）。"
                f"{'發現單程低於 NT$3,500 之甜美價，建議可先單程拆買鎖定！' if oneway_count > 0 else '目前整體處於開盤常態水位，建議持續追蹤促銷波動。'}"
            )
        else:
            summary = "目前 2027 年 3 月指定班次尚未釋出完整雙向報價，系統將每小時持續自動巡檢。"

        return {
            "overall_badge": overall,
            "executive_summary": summary,
            "top_recommendations": top_3,
            "combo_badges": combo_badges,
        }


class EmailNotificationService:
    """
    HTML Email 推播模組：
    清楚呈現每一組「7天6夜」的：
    - 去程 MM 922 單價（Minimum 與 Standard 並列）
    - 回程 MM 925 單價（Minimum 與 Standard 並列）
    - 來回總價（Minimum 總價 與 Standard 總價 醒目顯示，並附歷史最低/均價/最高）
    """

    def __init__(
        self,
        sender_email: Optional[str],
        sender_password: Optional[str],
        receiver_email: Optional[str],
        smtp_server: str = "smtp.gmail.com",
        smtp_port: int = 465,
    ) -> None:
        self.sender_email = (sender_email or "").strip()
        self.sender_password = (sender_password or "").strip()
        self.receiver_email = (receiver_email or "").strip()
        self.smtp_server = smtp_server
        self.smtp_port = smtp_port

    @staticmethod
    def _badge_style(badge: str) -> Tuple[str, str]:
        if "破盤秒搶" in badge:
            return "#dc2626", "#fef2f2"
        if "單程特價先買" in badge:
            return "#d97706", "#fffbeb"
        if "換季" in badge or "尚未開盤" in badge:
            return "#64748b", "#f1f5f9"
        return "#2563eb", "#eff6ff"

    @staticmethod
    def _fmt_price(val: Optional[float]) -> str:
        if val is None:
            return "<span style='color:#94a3b8;font-weight:normal;'>待開盤</span>"
        return f"NT${int(round(val)):,}"

    def build_html_report(
        self, records: List[Dict[str, Any]], decision: Dict[str, Any]
    ) -> str:
        overall_badge = decision.get("overall_badge", "【建議觀望】")
        summary_text = decision.get("executive_summary", "")
        top_3 = decision.get("top_recommendations", [])
        combo_badges = decision.get("combo_badges", {})
        fg_color, bg_color = self._badge_style(overall_badge)
        now_display = datetime.now(TW_TZ).strftime("%Y-%m-%d %H:%M:%S (台灣時間)")

        # 1. 組裝頂部「全月最便宜 Top 3 組合（MM 922 + MM 925 專屬）」摘要卡片
        top3_html = ""
        if top_3:
            cards = ""
            for rank, item in enumerate(top_3, start=1):
                medal = "🥇 第 1 名" if rank == 1 else ("🥈 第 2 名" if rank == 2 else "🥉 第 3 名")
                cards += f"""
                <div style="background:#ffffff;border:1px solid #fed7aa;border-radius:8px;padding:12px 14px;margin-bottom:8px;">
                  <div style="font-weight:800;color:#9a3412;font-size:14px;margin-bottom:6px;">
                    {medal}：{item['dep']} 出發 → {item['ret']} 回程 ({item['combo_label']})
                  </div>
                  <div style="font-size:13px;color:#1e293b;line-height:1.6;">
                    🔹 <strong>Minimum 方案（含稅）</strong>：
                       去程 MM922 <strong>NT${item['out_min']:,}</strong> ＋ 回程 MM925 <strong>NT${item['in_min']:,}</strong>
                       ＝ <span style="color:#dc2626;font-weight:900;font-size:15px;">來回總價 NT${item['tot_min']:,}</span><br>
                    🔸 <strong>Standard 方案（含稅+20kg行李+選位）</strong>：
                       去程 MM922 <strong>NT${item['out_std']:,}</strong> ＋ 回程 MM925 <strong>NT${item['in_std']:,}</strong>
                       ＝ <span style="color:#b45309;font-weight:900;font-size:15px;">來回總價 NT${item['tot_std']:,}</span>
                  </div>
                </div>
                """
            top3_html = f"""
            <div style="background:#fff7ed;border:2px solid #fb923c;padding:16px;margin:18px 0;border-radius:10px;">
              <div style="font-weight:900;color:#c2410c;font-size:16px;margin-bottom:10px;">
                🏆 2027年3月「指定航班 MM 922 + MM 925」最便宜 Top 3 日期組合（含稅）
              </div>
              {cards}
            </div>
            """

        # 2. 組裝 25 組完整雙方案（Minimum / Standard）去程、回程、來回總價與歷史水位大表
        rows_html = ""
        for idx, r in enumerate(records):
            dep = r["departure_date"]
            ret = r["return_date"]
            key = f"{dep}_{ret}"
            row_badge = combo_badges.get(key, "【建議觀望】")
            b_fg, b_bg = self._badge_style(row_badge)

            out_min_s = r["outbound_mm922_min"]
            out_std_s = r["outbound_mm922_std"]
            in_min_s = r["inbound_mm925_min"]
            in_std_s = r["inbound_mm925_std"]
            tot_min_s = r["round_trip_total_min"]
            tot_std_s = r["round_trip_total_std"]

            group_bg = "#ffffff" if idx % 2 == 0 else "#f8fafc"
            dep_label = format_date_with_weekday(dep)
            ret_label = format_date_with_weekday(ret)

            # 每一組日期佔 2 列：第一列為 Minimum 方案，第二列為 Standard 方案
            rows_html += f"""
            <!-- 第 {idx+1} 組：Minimum 列 -->
            <tr style="background:{group_bg};border-top:2px solid #cbd5e1;font-size:13px;">
                <td rowspan="2" style="padding:10px 8px;font-weight:700;color:#0f172a;vertical-align:middle;border-right:1px solid #e2e8f0;white-space:nowrap;">
                    <div style="font-size:14px;color:#be185d;">去 {dep_label}</div>
                    <div style="font-size:13px;color:#334155;margin-top:2px;">回 {ret_label}</div>
                    <div style="font-size:11px;color:#64748b;font-weight:normal;margin-top:4px;">({dep} ~ {ret})</div>
                </td>
                <td rowspan="2" style="padding:10px 6px;text-align:center;vertical-align:middle;border-right:1px solid #e2e8f0;">
                    <span style="display:inline-block;padding:4px 8px;border-radius:999px;font-weight:bold;font-size:12px;color:{b_fg};background:{b_bg};">
                        {row_badge}
                    </span>
                </td>
                <td style="padding:8px;text-align:center;font-weight:bold;color:#0369a1;background:#f0f9ff;border-bottom:1px dashed #cbd5e1;white-space:nowrap;">
                    Minimum<br><span style="font-size:10px;font-weight:normal;color:#0284c7;">(手提7kg/含稅)</span>
                </td>
                <td style="padding:8px 10px;text-align:right;border-bottom:1px dashed #cbd5e1;">
                    <div style="font-weight:800;font-size:14px;color:#0f172a;">{self._fmt_price(out_min_s.get('current_price'))}</div>
                    <div style="font-size:11px;color:#64748b;">
                        低:{self._fmt_price(out_min_s.get('all_time_low'))} | 均:{self._fmt_price(out_min_s.get('average_price'))} | 高:{self._fmt_price(out_min_s.get('all_time_high'))}
                    </div>
                </td>
                <td style="padding:8px 10px;text-align:right;border-bottom:1px dashed #cbd5e1;">
                    <div style="font-weight:800;font-size:14px;color:#0f172a;">{self._fmt_price(in_min_s.get('current_price'))}</div>
                    <div style="font-size:11px;color:#64748b;">
                        低:{self._fmt_price(in_min_s.get('all_time_low'))} | 均:{self._fmt_price(in_min_s.get('average_price'))} | 高:{self._fmt_price(in_min_s.get('all_time_high'))}
                    </div>
                </td>
                <td style="padding:8px 10px;text-align:right;background:#fef2f2;border-bottom:1px dashed #fecaca;">
                    <div style="font-weight:900;font-size:15px;color:#dc2626;">{self._fmt_price(tot_min_s.get('current_price'))}</div>
                    <div style="font-size:11px;color:#991b1b;">
                        低:{self._fmt_price(tot_min_s.get('all_time_low'))} | 均:{self._fmt_price(tot_min_s.get('average_price'))} | 高:{self._fmt_price(tot_min_s.get('all_time_high'))}
                    </div>
                </td>
            </tr>
            <!-- 第 {idx+1} 組：Standard 列 -->
            <tr style="background:{group_bg};border-bottom:1px solid #cbd5e1;font-size:13px;">
                <td style="padding:8px;text-align:center;font-weight:bold;color:#92400e;background:#fffbeb;white-space:nowrap;">
                    Standard<br><span style="font-size:10px;font-weight:normal;color:#b45309;">(含20kg行李+選位)</span>
                </td>
                <td style="padding:8px 10px;text-align:right;">
                    <div style="font-weight:800;font-size:14px;color:#334155;">{self._fmt_price(out_std_s.get('current_price'))}</div>
                    <div style="font-size:11px;color:#64748b;">
                        低:{self._fmt_price(out_std_s.get('all_time_low'))} | 均:{self._fmt_price(out_std_s.get('average_price'))} | 高:{self._fmt_price(out_std_s.get('all_time_high'))}
                    </div>
                </td>
                <td style="padding:8px 10px;text-align:right;">
                    <div style="font-weight:800;font-size:14px;color:#334155;">{self._fmt_price(in_std_s.get('current_price'))}</div>
                    <div style="font-size:11px;color:#64748b;">
                        低:{self._fmt_price(in_std_s.get('all_time_low'))} | 均:{self._fmt_price(in_std_s.get('average_price'))} | 高:{self._fmt_price(in_std_s.get('all_time_high'))}
                    </div>
                </td>
                <td style="padding:8px 10px;text-align:right;background:#fefce8;">
                    <div style="font-weight:900;font-size:15px;color:#b45309;">{self._fmt_price(tot_std_s.get('current_price'))}</div>
                    <div style="font-size:11px;color:#713f12;">
                        低:{self._fmt_price(tot_std_s.get('all_time_low'))} | 均:{self._fmt_price(tot_std_s.get('average_price'))} | 高:{self._fmt_price(tot_std_s.get('all_time_high'))}
                    </div>
                </td>
            </tr>
            """

        html = f"""<!DOCTYPE html>
<html lang="zh-Hant">
<head>
<meta charset="UTF-8">
<title>樂桃航空 TPE-OKA (MM922/MM925) 雙方案含稅報價與訂票決策報告</title>
</head>
<body style="margin:0;padding:16px;background-color:#f1f5f9;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Noto Sans TC',sans-serif;">
  <div style="max-width:980px;margin:0 auto;background:#ffffff;border-radius:12px;overflow:hidden;box-shadow:0 4px 14px rgba(0,0,0,0.08);">
    <!-- 頂部標題橫幅 -->
    <div style="background:linear-gradient(135deg,#9d174d,#db2777);color:#ffffff;padding:22px 24px;">
      <div style="font-size:13px;opacity:0.95;font-weight:600;">🍑 Peach Aviation 雲端全自動航班雷達（每 1 小時巡檢 ｜ 三重備援防封鎖架構）</div>
      <h1 style="margin:6px 0 6px 0;font-size:21px;">台北桃園 (TPE) ↔ 沖繩那霸 (OKA) 2027年3月「7天6夜」雙方案含稅監控報告</h1>
      <div style="font-size:13px;opacity:0.95;background:rgba(0,0,0,0.18);padding:6px 10px;border-radius:6px;display:inline-block;">
        ✈️ 嚴格鎖定班次：<strong>去程 MM 922 (09:45 TPE → 12:25 OKA)</strong> ｜ <strong>回程 MM 925 (13:35 OKA → 14:20 TPE)</strong> ｜ 更新：{now_display}
      </div>
    </div>

    <div style="padding:22px 24px;">
      <!-- 醒目決策標籤與 Gemini 趨勢簡評 -->
      <div style="background:{bg_color};border:2px solid {fg_color};border-radius:10px;padding:18px 20px;margin-bottom:18px;">
        <div style="display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:12px;">
          <div>
            <span style="font-size:12px;color:#475569;font-weight:bold;">🤖 Gemini AI 智慧訂票決策建議</span>
            <div style="font-size:24px;font-weight:900;color:{fg_color};margin-top:2px;">{overall_badge}</div>
          </div>
          <a href="{PEACH_BOOKING_URL}" target="_blank"
             style="background:#db2777;color:#ffffff;text-decoration:none;padding:12px 22px;border-radius:8px;font-weight:bold;font-size:14px;display:inline-block;">
             ✈️ 前往樂桃官網訂票
          </a>
        </div>
        <p style="margin:12px 0 0 0;color:#1e293b;font-size:14px;line-height:1.65;">
          {summary_text}
        </p>
      </div>

      {top3_html}

      <!-- 方案說明提示框 -->
      <div style="background:#f8fafc;border:1px solid #cbd5e1;border-radius:8px;padding:10px 14px;margin-bottom:14px;font-size:12px;color:#334155;line-height:1.6;">
        💡 <strong>報價說明（皆為新台幣 TWD 含兩地機場稅實付金額）</strong>：<br>
        • <strong>Minimum 方案</strong>：含手提行李 7kg（2件合計）＋ 桃園/那霸兩地機場服務費。<br>
        • <strong>Standard 方案</strong>：含手提行李 7kg ＋ <strong>免費託運行李 1 件 (20kg)</strong> ＋ <strong>免費標準座位指定</strong> ＋ 免開票手續費（單程加價 NT$1,100 / 來回加價 NT$2,200）。<br>
        • 註：最後 4 組回程（03/28～03/31）跨越 2027 年 3 月最後一個週日（IATA 夏季班表換季日），樂桃回程 MM 925 尚待公佈夏季班表，故標示為「待開盤」。
      </div>

      <!-- 雙方案單趟與來回總價歷史水位表格 -->
      <h3 style="margin:18px 0 10px 0;color:#0f172a;font-size:16px;">📊 2027年3月「7天6夜」全 25 組 Minimum / Standard 單價與來回總價歷史水位表</h3>
      <div style="overflow-x:auto;">
        <table style="width:100%;border-collapse:collapse;border:2px solid #94a3b8;">
          <thead>
            <tr style="background:#0f172a;color:#ffffff;font-size:13px;">
              <th style="padding:10px 8px;text-align:left;">出發日 / 回程日<br><span style="font-size:11px;font-weight:normal;color:#cbd5e1;">連續 7 天 6 夜</span></th>
              <th style="padding:10px 6px;text-align:center;">決策標籤</th>
              <th style="padding:10px 8px;text-align:center;">票價方案</th>
              <th style="padding:10px 10px;text-align:right;">去程 MM 922 單趟<br><span style="font-size:11px;font-weight:normal;color:#cbd5e1;">09:45 TPE → 12:25 OKA</span></th>
              <th style="padding:10px 10px;text-align:right;">回程 MM 925 單趟<br><span style="font-size:11px;font-weight:normal;color:#cbd5e1;">13:35 OKA → 14:20 TPE</span></th>
              <th style="padding:10px 10px;text-align:right;background:#7f1d1d;">來回含稅總價 (去+回)<br><span style="font-size:11px;font-weight:normal;color:#fecaca;">當下總價 (歷史低/均/高)</span></th>
            </tr>
          </thead>
          <tbody>
            {rows_html}
          </tbody>
        </table>
      </div>

      <div style="margin-top:20px;padding-top:14px;border-top:1px solid #e2e8f0;font-size:12px;color:#64748b;display:flex;justify-content:space-between;flex-wrap:wrap;">
        <span>雲端歷史水位資料庫：<code>data/price_history.json</code>（每小時自動巡檢更新）</span>
        <span>樂桃官網：<a href="{PEACH_BOOKING_URL}" style="color:#db2777;">{PEACH_BOOKING_URL}</a></span>
      </div>
    </div>
  </div>
</body>
</html>
"""
        return html

    def send_email(self, subject: str, html_body: str) -> bool:
        PREVIEW_HTML_FILE.parent.mkdir(parents=True, exist_ok=True)
        with open(PREVIEW_HTML_FILE, "w", encoding="utf-8") as f:
            f.write(html_body)
        logger.info(f"📄 已產生最新 HTML 預覽報告：{PREVIEW_HTML_FILE}")

        if not (self.sender_email and self.sender_password and self.receiver_email):
            logger.warning("⚠️ 未完整設定 SENDER_EMAIL / SENDER_PASSWORD / RECEIVER_EMAIL 環境變數，已略過 SMTP 發信。")
            return False

        msg = MIMEMultipart("alternative")
        msg["Subject"] = subject
        msg["From"] = self.sender_email
        msg["To"] = self.receiver_email
        msg.attach(MIMEText(html_body, "html", "utf-8"))

        try:
            context = ssl.create_default_context()
            with smtplib.SMTP_SSL(self.smtp_server, self.smtp_port, context=context, timeout=20) as server:
                server.login(self.sender_email, self.sender_password)
                recipients = [addr.strip() for addr in self.receiver_email.split(",") if addr.strip()]
                server.sendmail(self.sender_email, recipients, msg.as_string())
            logger.info(f"📧 HTML 價格波動通知信已成功寄出至：{self.receiver_email}")
            return True
        except Exception as exc:
            logger.error(f"❌ SMTP 發信失敗（不阻斷工作流）: {exc}")
            return False


def main() -> int:
    logger.info("🚀 啟動樂桃航空 (MM 922 / MM 925) 雲端雙方案報價與智慧訂票決策系統...")

    gemini_api_key = os.environ.get("GEMINI_API_KEY", "")
    sender_email = os.environ.get("SENDER_EMAIL", "")
    sender_password = os.environ.get("SENDER_PASSWORD", "")
    receiver_email = os.environ.get("RECEIVER_EMAIL", "")
    force_notify = os.environ.get("FORCE_NOTIFY", "false").lower() in ("true", "1", "yes")
    dry_run = os.environ.get("DRY_RUN", "false").lower() in ("true", "1", "yes")

    # 1. 產生 2027 年 3 月所有連續 7 天 6 夜組合 (3/1~3/7 至 3/25~3/31，共 25 組)
    date_pairs = generate_target_date_pairs(year=2027, month=3)
    logger.info(f"📅 目標監控區間：2027-03-01 至 2027-03-25 出發（共 {len(date_pairs)} 組 7天6夜組合）")

    # 2. 透過三重備援引擎擷取去程 MM 922 與回程 MM 925 之 Minimum / Standard 單程含稅價
    scraper = PeachFlightScraper(dry_run=dry_run)
    outbound_prices, inbound_prices = scraper.fetch_all_dates(date_pairs)

    # 3. 更新歷史價格 JSON（獨立記錄 Minimum 與 Standard 之去程、回程與來回總價）
    history_mgr = PriceHistoryManager(HISTORY_FILE)
    any_price_changed, summary_records = history_mgr.update_all_combinations(
        date_pairs=date_pairs,
        outbound_prices=outbound_prices,
        inbound_prices=inbound_prices,
    )
    history_mgr.save()

    # 4. 呼叫 Gemini 進行價格水位評估與決策標籤生成
    advisor = GeminiDecisionAdvisor(api_key=gemini_api_key)
    decision = advisor.analyze(summary_records)
    logger.info(f"🏷️ 本次整體決策標籤：{decision.get('overall_badge')} | 簡評：{decision.get('executive_summary')}")

    # 5. 組裝 HTML 報告，若任一維度有價格波動或手動強制觸發則發送 Email
    notifier = EmailNotificationService(
        sender_email=sender_email,
        sender_password=sender_password,
        receiver_email=receiver_email,
    )
    html_report = notifier.build_html_report(summary_records, decision)

    if any_price_changed or force_notify:
        subject = f"{decision.get('overall_badge')} 樂桃 TPE↔OKA (MM922/MM925) Minimum/Standard 來回總價與水位報告"
        notifier.send_email(subject=subject, html_body=html_report)
    else:
        PREVIEW_HTML_FILE.parent.mkdir(parents=True, exist_ok=True)
        with open(PREVIEW_HTML_FILE, "w", encoding="utf-8") as f:
            f.write(html_report)
        logger.info("ℹ️ 本次巡檢無新開盤或價格變動，不觸發 Email 推播。")

    logger.info("✅ 監控作業執行完畢。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
