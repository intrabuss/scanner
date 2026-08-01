"""
IntraBuss Scanner Backend — consolidated server version.
Everything built step-by-step in Colab today, combined into one
persistent script for a real server (DigitalOcean droplet).

WHAT'S NEW vs the Colab version:
- No more copy-pasting auth codes by hand. Visit /login each morning,
  log in on Upstox's page (mobile + PIN + TOTP, same as always), and
  Upstox redirects back here automatically — the server captures and
  stores the token itself.
- No ngrok. This server has a real public IP, so it's reachable directly.
- Runs continuously — daily cache + ORB cache rebuild themselves
  automatically at the right times each trading day (see the
  scheduler at the bottom), no manual cell-running needed.

ONE-TIME SETUP before running:
1. In your Upstox Developer App settings, change the Redirect URL to:
     http://YOUR_SERVER_IP/callback
   (must match exactly what's used below)
2. Fill in your real values in the CONFIG section right below.
3. On the server: pip install -r requirements.txt
4. Run: python3 main.py
5. Each trading morning: open http://YOUR_SERVER_IP/login in a browser,
   log in with your Upstox credentials + TOTP. That's the whole daily
   routine now — no Colab, no code copy-pasting.
"""

import os
import re
import json
import time
import threading
import datetime
import requests
import pandas as pd
import xml.etree.ElementTree as ET
from email.utils import parsedate_to_datetime
from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse, RedirectResponse
from fastapi.middleware.cors import CORSMiddleware
from ta.trend import ADXIndicator, MACD
from ta.volatility import AverageTrueRange
import uvicorn

# ============================================================
# CONFIG — fill in your real values here (only on your server,
# never share this file with these filled in)
# ============================================================
API_KEY = ""
API_SECRET = ""
SERVER_PUBLIC_IP = ""
REDIRECT_URI = "https://143-110-***-***.nip.io/callback"

ORB_WINDOW_MINUTES = 15   # mutable at runtime via POST /config
DRB_WINDOW_MINUTES = 15   # confirmation delay after market open before DRB signals count
SCAN_MODE = "full"        # "nifty500" (curated ~500, fast) or "full" (~4,500, slower) — mutable via POST /config/scan-mode
universe_rebuild_status = {"state": "idle", "mode": None, "started_at": None}  # for frontend polling during a manual rebuild
RVOL_DISPLAY_CAP = 10.0

# Allow your GitHub Pages dashboard to call this API.
# Tighten this to your exact URL once everything's confirmed working:
#   ALLOWED_ORIGINS = ["https://yourusername.github.io"]
ALLOWED_ORIGINS = ["*"]

# ============================================================
# GLOBAL STATE (in-memory — resets if the server restarts,
# same as it did in Colab; you'd just log in again via /login)
# ============================================================
access_token = None
headers = None
master_df = None
stocks_to_test = []
orb_stocks_to_test = []  # curated known-sector subset (~500) — ORB's per-symbol
                          # sequential sweep can't keep its 3-min cadence across
                          # the full ~4,500-stock universe, so it stays scoped here
                          # while general scanning/DRB use the full stocks_to_test
daily_cache = {}
orb_cache = {}
break_log = {"ORB": {}, "DRB": {}}     # {symbol: [{"time","rvol","dir"}, ...]} — every crossing today, per strategy
break_state = {"ORB": {}, "DRB": {}}   # {symbol: "up"|"down"|None} — current side, used to detect new crossings
candle_break_state = {}  # {symbol: "up"|"down"|None} — ORB only: confirmed by an actual 3-min candle CLOSE, not just a live tick poke

# Index instrument keys — best-effort names; if one's wrong it just gets
# skipped (see build_index_cache), doesn't break anything else
INDEX_KEYS = {
    "NIFTY 50": "NSE_INDEX|Nifty 50",
    "BANKNIFTY": "NSE_INDEX|Nifty Bank",
    "FINNIFTY": "NSE_INDEX|Nifty Fin Service",
    "MIDCAP": "NSE_INDEX|NIFTY MIDCAP 100",
    "SENSEX": "BSE_INDEX|SENSEX",
    "INDIA VIX": "NSE_INDEX|India VIX",
}
index_cache = {}  # {display_name: {"prev_close": float}} — built once/day alongside daily_cache
MAX_BREAK_LOG_ENTRIES = 5

# Global indices — Upstox (an Indian broker) doesn't carry these, so they're
# pulled separately from Yahoo Finance's free public chart endpoint instead
# of the Upstox quote/historical-candle flow above. No auth needed for this
# one, which is why it doesn't hang off `headers`/`access_token` at all.
GLOBAL_INDEX_KEYS = {
    "Dow Jones": "^DJI",
    "S&P 500": "^GSPC",
    "Nasdaq": "^IXIC",
    "FTSE": "^FTSE",
    "CAC": "^FCHI",
    "DAX": "^GDAXI",
    "Nikkei 225": "^N225",
    "Straits Times": "^STI",
    "Hang Seng": "^HSI",
    "Taiwan Weighted": "^TWII",
    "KOSPI": "^KS11",
    "SET Composite": "^SET.BK",
    "Jakarta Composite": "^JKSE",
    "Shanghai Composite": "000001.SS",
}
GLOBAL_INDEX_CACHE_TTL = 30  # seconds — short-lived cache so the dashboard's poll loop doesn't hammer Yahoo
_global_index_cache = {"ts": 0, "data": [], "updated_at": None}

# FII/DII — NSE publishes this once per trading day (provisional figures land in
# the evening, ~5:30pm IST onwards; get refined the next morning). No Upstox
# equivalent, so this hits NSE's own (unofficial) endpoint directly. NSE blocks
# bare API calls without a browser-like session, so we grab cookies from the
# homepage first, then reuse that session for the actual data call.
NSE_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": "https://www.nseindia.com/",
}
FII_DII_CACHE_TTL = 900  # 15 min — this data doesn't move intraday, no reason to hit NSE more often
_fii_dii_cache = {"ts": 0, "data": None, "updated_at": None}

SYMBOL_SECTOR_MAP = {"3MINDIA":"Services","ABB":"Industrial Manufacturing","ACC":"Cement & Cement Products","AIAENG":"Industrial Manufacturing","APLAPOLLO":"Metals","AUBANK":"Financial Services","AAVAS":"Financial Services","ADANIGREEN":"Energy","ADANIPORTS":"Services","ADANIPOWER":"Energy","ADANITRANS":"Energy","ABCAPITAL":"Financial Services","ABFRL":"Consumer Goods","ADVENZYMES":"Consumer Goods","AEGISCHEM":"Energy","AJANTPHARM":"Pharma","AKZOINDIA":"Consumer Goods","APLLTD":"Pharma","ALKEM":"Pharma","ALBK":"Financial Services","ALLCARGO":"Services","AMARAJABAT":"Automobile","AMBUJACEM":"Cement & Cement Products","ANDHRABANK":"Financial Services","APOLLOHOSP":"Healthcare Services","APOLLOTYRE":"Automobile","ASHOKLEY":"Automobile","ASHOKA":"Construction","ASIANPAINT":"Consumer Goods","ASTERDM":"Healthcare Services","ASTRAZEN":"Pharma","ASTRAL":"Industrial Manufacturing","ATUL":"Chemicals","AUROPHARMA":"Pharma","AVANTIFEED":"Consumer Goods","DMART":"Consumer Goods","AXISBANK":"Financial Services","BASF":"Chemicals","BEML":"Industrial Manufacturing","BSE":"Financial Services","BAJAJ-AUTO":"Automobile","BAJAJCON":"Consumer Goods","BAJAJELEC":"Consumer Goods","BAJFINANCE":"Financial Services","BAJAJFINSV":"Financial Services","BAJAJHLDNG":"Financial Services","BALKRISIND":"Automobile","BALMLAWRIE":"Services","BALRAMCHIN":"Consumer Goods","BANDHANBNK":"Financial Services","BANKBARODA":"Financial Services","BANKINDIA":"Financial Services","MAHABANK":"Financial Services","BATAINDIA":"Consumer Goods","BERGEPAINT":"Consumer Goods","BDL":"Industrial Manufacturing","BEL":"Industrial Manufacturing","BHARATFORG":"Industrial Manufacturing","BHEL":"Industrial Manufacturing","BPCL":"Energy","BHARTIARTL":"Telecom","INFRATEL":"Telecom","BIOCON":"Pharma","BIRLACORPN":"Cement & Cement Products","BLISSGVS":"Pharma","BLUEDART":"Services","BLUESTARCO":"Consumer Goods","BBTC":"Consumer Goods","BOMDYEING":"Textiles","BOSCHLTD":"Automobile","BRIGADE":"Construction","BRITANNIA":"Consumer Goods","CARERATING":"Financial Services","CCL":"Consumer Goods","CESC":"Energy","CGPOWER":"Industrial Manufacturing","CRISIL":"Financial Services","CADILAHC":"Pharma","CANFINHOME":"Financial Services","CANBK":"Financial Services","CAPLIPOINT":"Pharma","CARBORUNIV":"Industrial Manufacturing","CASTROLIND":"Energy","CEATLTD":"Automobile","CENTRALBK":"Financial Services","CDSL":"Financial Services","CENTURYPLY":"Consumer Goods","CERA":"Construction","CHAMBLFERT":"Fertilisers & Pesticides","CHENNPETRO":"Energy","CHOLAHLDNG":"Financial Services","CHOLAFIN":"Financial Services","CIPLA":"Pharma","CUB":"Financial Services","COALINDIA":"Metals","COCHINSHIP":"Industrial Manufacturing","COFFEEDAY":"Consumer Goods","COLPAL":"Consumer Goods","CONCOR":"Services","COROMANDEL":"Fertilisers & Pesticides","CORPBANK":"Financial Services","COX&KINGS":"Services","CREDITACC":"Financial Services","CROMPTON":"Consumer Goods","CUMMINSIND":"Industrial Manufacturing","CYIENT":"IT","DBCORP":"Media & Entertainment","DCBBANK":"Financial Services","DCMSHRIRAM":"Consumer Goods","DLF":"Construction","DABUR":"Consumer Goods","DEEPAKFERT":"Chemicals","DEEPAKNTR":"Chemicals","DELTACORP":"Services","DHFL":"Financial Services","DBL":"Construction","DISHTV":"Media & Entertainment","DCAL":"Pharma","DIVISLAB":"Pharma","DIXON":"Consumer Goods","LALPATHLAB":"Healthcare Services","DRREDDY":"Pharma","EIDPARRY":"Fertilisers & Pesticides","EIHOTEL":"Services","EDELWEISS":"Financial Services","EICHERMOT":"Automobile","ELGIEQUIP":"Industrial Manufacturing","EMAMILTD":"Consumer Goods","ENDURANCE":"Automobile","ENGINERSIN":"Construction","EQUITAS":"Financial Services","ERIS":"Pharma","ESCORTS":"Automobile","ESSELPACK":"Industrial Manufacturing","EXIDEIND":"Automobile","FDC":"Pharma","FEDERALBNK":"Financial Services","FINEORG":"Chemicals","FINCABLES":"Industrial Manufacturing","FINPIPE":"Industrial Manufacturing","FSL":"IT","FORTIS":"Healthcare Services","FCONSUMER":"Consumer Goods","FLFL":"Consumer Goods","FRETAIL":"Consumer Goods","GAIL":"Energy","GEPIL":"Industrial Manufacturing","GET&D":"Industrial Manufacturing","GHCL":"Chemicals","GMRINFRA":"Construction","GALAXYSURF":"Chemicals","GDL":"Services","GAYAPROJ":"Construction","GICRE":"Financial Services","GILLETTE":"Consumer Goods","GSKCONS":"Consumer Goods","GLAXO":"Pharma","GLENMARK":"Pharma","GODFRYPHLP":"Consumer Goods","GODREJAGRO":"Consumer Goods","GODREJCP":"Consumer Goods","GODREJIND":"Consumer Goods","GODREJPROP":"Construction","GRANULES":"Pharma","GRAPHITE":"Industrial Manufacturing","GRASIM":"Cement & Cement Products","GESHIP":"Services","GREAVESCOT":"Industrial Manufacturing","GRINDWELL":"Industrial Manufacturing","GRUH":"Financial Services","GUJALKALI":"Chemicals","GUJFLUORO":"Chemicals","GUJGASLTD":"Energy","GMDCLTD":"Metals","GNFC":"Chemicals","GPPL":"Services","GSFC":"Fertilisers & Pesticides","GSPL":"Energy","GULFOILLUB":"Energy","HEG":"Industrial Manufacturing","HCLTECH":"IT","HDFCAMC":"Financial Services","HDFCBANK":"Financial Services","HDFCLIFE":"Financial Services","HATHWAY":"Media & Entertainment","HATSUN":"Consumer Goods","HAVELLS":"Consumer Goods","HEIDELBERG":"Cement & Cement Products","HERITGFOOD":"Consumer Goods","HEROMOTOCO":"Automobile","HEXAWARE":"IT","HFCL":"Telecom","HSCL":"Chemicals","HIMATSEIDE":"Textiles","HINDALCO":"Metals","HAL":"Industrial Manufacturing","HINDCOPPER":"Metals","HINDPETRO":"Energy","HINDUNILVR":"Consumer Goods","HINDZINC":"Metals","HONAUT":"Industrial Manufacturing","HUDCO":"Financial Services","HDFC":"Financial Services","ICICIBANK":"Financial Services","ICICIGI":"Financial Services","ICICIPRULI":"Financial Services","ISEC":"Financial Services","ICRA":"Financial Services","IDBI":"Financial Services","IDFCFIRSTB":"Financial Services","IDFC":"Financial Services","IFBIND":"Consumer Goods","IFCI":"Financial Services","IRB":"Construction","IRCON":"Construction","ITC":"Consumer Goods","ITDCEM":"Construction","ITI":"Telecom","INDIACEM":"Cement & Cement Products","ITDC":"Services","IBULHSGFIN":"Financial Services","IBULISL":"IT","IBREALEST":"Construction","IBVENTURES":"Financial Services","INDIANB":"Financial Services","IEX":"Financial Services","INDHOTEL":"Services","IOC":"Energy","IOB":"Financial Services","INDOSTAR":"Financial Services","INDOCO":"Pharma","IGL":"Energy","INDUSINDBK":"Financial Services","INFIBEAM":"IT","NAUKRI":"IT","INFY":"IT","INOXLEISUR":"Media & Entertainment","INOXWIND":"Industrial Manufacturing","INTELLECT":"IT","INDIGO":"Services","IPCALAB":"Pharma","JBCHEPHARM":"Pharma","JKCEMENT":"Cement & Cement Products","JKLAKSHMI":"Cement & Cement Products","JKPAPER":"Paper","JKTYRE":"Automobile","JMFINANCIL":"Financial Services","JSWENERGY":"Energy","JSWSTEEL":"Metals","JAGRAN":"Media & Entertainment","JAICORPLTD":"Industrial Manufacturing","JISLJALEQS":"Industrial Manufacturing","JPASSOCIAT":"Cement & Cement Products","J&KBANK":"Financial Services","JAMNAAUTO":"Automobile","JETAIRWAYS":"Services","JINDALSAW":"Metals","JSLHISAR":"Metals","JSL":"Metals","JINDALSTEL":"Metals","JUBLFOOD":"Consumer Goods","JUBILANT":"Pharma","JUSTDIAL":"IT","JYOTHYLAB":"Consumer Goods","KPRMILL":"Textiles","KEI":"Industrial Manufacturing","KIOCL":"Metals","KNRCON":"Construction","KRBL":"Consumer Goods","KAJARIACER":"Construction","KALPATPOWR":"Energy","KANSAINER":"Consumer Goods","KTKBANK":"Financial Services","KARURVYSYA":"Financial Services","KSCL":"Consumer Goods","KEC":"Construction","KIRLOSENG":"Industrial Manufacturing","KOLTEPATIL":"Construction","KOTAKBANK":"Financial Services","L&TFH":"Financial Services","LTTS":"IT","LICHSGFIN":"Financial Services","LAXMIMACH":"Industrial Manufacturing","LAKSHVILAS":"Financial Services","LTI":"IT","LT":"Construction","LAURUSLABS":"Pharma","LEMONTREE":"Services","LINDEINDIA":"Chemicals","LUPIN":"Pharma","LUXIND":"Textiles","MASFIN":"Financial Services","MMTC":"Services","MOIL":"Metals","MRF":"Automobile","MAGMA":"Financial Services","MGL":"Energy","MAHSCOOTER":"Automobile","MAHSEAMLES":"Metals","M&MFIN":"Financial Services","M&M":"Automobile","MAHINDCIE":"Industrial Manufacturing","MHRIL":"Services","MAHLOG":"Services","MANAPPURAM":"Financial Services","MRPL":"Energy","MARICO":"Consumer Goods","MARUTI":"Automobile","MFSL":"Financial Services","MAXINDIA":"Healthcare Services","MINDTREE":"IT","MINDACORP":"Automobile","MINDAIND":"Automobile","MONSANTO":"Fertilisers & Pesticides","MOTHERSUMI":"Automobile","MOTILALOFS":"Financial Services","MPHASIS":"IT","MUTHOOTFIN":"Financial Services","NATCOPHARM":"Pharma","NBCC":"Construction","NCC":"Construction","NESCO":"Services","NHPC":"Energy","NIITTECH":"IT","NLCINDIA":"Energy","NMDC":"Metals","NTPC":"Energy","NH":"Healthcare Services","NATIONALUM":"Metals","NFL":"Fertilisers & Pesticides","NBVENTURES":"Energy","NAVINFLUOR":"Chemicals","NETWORK18":"Media & Entertainment","NILKAMAL":"Industrial Manufacturing","OBEROIRLTY":"Construction","ONGC":"Energy","OIL":"Energy","OMAXE":"Construction","OFSS":"IT","ORIENTCEM":"Cement & Cement Products","ORIENTELEC":"Consumer Goods","ORIENTBANK":"Financial Services","PCJEWELLER":"Consumer Goods","PIIND":"Fertilisers & Pesticides","PNBHOUSING":"Financial Services","PNCINFRA":"Construction","PTC":"Energy","PVR":"Media & Entertainment","PAGEIND":"Textiles","PARAGMILK":"Consumer Goods","PERSISTENT":"IT","PETRONET":"Energy","PFIZER":"Pharma","PHILIPCARB":"Chemicals","PHOENIXLTD":"Construction","PIDILITIND":"Chemicals","PEL":"Pharma","PFC":"Financial Services","POWERGRID":"Energy","PRAJIND":"Industrial Manufacturing","PRESTIGE":"Construction","PRSMJOHNSN":"Cement & Cement Products","PGHL":"Pharma","PGHH":"Consumer Goods","PNB":"Financial Services","QUESS":"Services","RBLBANK":"Financial Services","RECLTD":"Financial Services","RITES":"Construction","RADICO":"Consumer Goods","RAIN":"Chemicals","RAJESHEXPO":"Consumer Goods","RALLIS":"Fertilisers & Pesticides","RKFORGE":"Industrial Manufacturing","RCF":"Fertilisers & Pesticides","RAYMOND":"Textiles","REDINGTON":"Services","RELAXO":"Consumer Goods","RELCAPITAL":"Financial Services","RCOM":"Telecom","RHFL":"Financial Services","RELIANCE":"Energy","RELINFRA":"Energy","RNAM":"Financial Services","RPOWER":"Energy","REPCOHOME":"Financial Services","RUPA":"Textiles","SHK":"Consumer Goods","SBILIFE":"Financial Services","SJVN":"Energy","SKFINDIA":"Industrial Manufacturing","SREINFRA":"Financial Services","SRF":"Textiles","SADBHAV":"Construction","SANOFI":"Pharma","SCHAEFFLER":"Industrial Manufacturing","SIS":"Services","SHANKARA":"Metals","SHARDACROP":"Fertilisers & Pesticides","SFL":"Consumer Goods","SHILPAMED":"Pharma","SCI":"Services","SHOPERSTOP":"Consumer Goods","SHREECEM":"Cement & Cement Products","RENUKA":"Consumer Goods","SHRIRAMCIT":"Financial Services","SRTRANSFIN":"Financial Services","SIEMENS":"Industrial Manufacturing","SPTL":"Industrial Manufacturing","SOBHA":"Construction","SOLARINDS":"Chemicals","SONATSOFTW":"IT","SOUTHBANK":"Financial Services","STARCEMENT":"Cement & Cement Products","SBIN":"Financial Services","SAIL":"Metals","STRTECH":"Telecom","STAR":"Pharma","SUDARSCHEM":"Chemicals","SPARC":"Pharma","SUNPHARMA":"Pharma","SUNTV":"Media & Entertainment","SUNCLAYLTD":"Automobile","SUNDARMFIN":"Financial Services","SUNDRMFAST":"Automobile","SUNTECK":"Construction","SUPRAJIT":"Automobile","SUPREMEIND":"Industrial Manufacturing","SUVEN":"Pharma","SUZLON":"Industrial Manufacturing","SWANENERGY":"Textiles","SYMPHONY":"Consumer Goods","SYNDIBANK":"Financial Services","SYNGENE":"Pharma","TCNSBRANDS":"Textiles","TTKPRESTIG":"Consumer Goods","TVTODAY":"Media & Entertainment","TV18BRDCST":"Media & Entertainment","TVSMOTOR":"Automobile","TAKE":"IT","TNPL":"Paper","TATACHEM":"Chemicals","TATACOFFEE":"Consumer Goods","TCS":"IT","TATAELXSI":"IT","TATAGLOBAL":"Consumer Goods","TATAINVEST":"Financial Services","TATAMTRDVR":"Automobile","TATAMOTORS":"Automobile","TATAPOWER":"Energy","TATASTEEL":"Metals","TEAMLEASE":"Services","TECHM":"IT","NIACL":"Financial Services","RAMCOCEM":"Cement & Cement Products","THERMAX":"Industrial Manufacturing","THOMASCOOK":"Services","THYROCARE":"Healthcare Services","TIMETECHNO":"Industrial Manufacturing","TIMKEN":"Industrial Manufacturing","TITAN":"Consumer Goods","TORNTPHARM":"Pharma","TORNTPOWER":"Energy","TRENT":"Consumer Goods","TRIDENT":"Textiles","TRITURBINE":"Industrial Manufacturing","TIINDIA":"Automobile","UCOBANK":"Financial Services","UFLEX":"Industrial Manufacturing","UPL":"Fertilisers & Pesticides","UJJIVAN":"Financial Services","ULTRACEMCO":"Cement & Cement Products","UNIONBANK":"Financial Services","UBL":"Consumer Goods","MCDOWELL-N":"Consumer Goods","VGUARD":"Consumer Goods","VMART":"Consumer Goods","VIPIND":"Consumer Goods","VRLLOG":"Services","VSTIND":"Consumer Goods","WABAG":"Services","VAKRANGEE":"IT","VTL":"Textiles","VARROC":"Automobile","VBL":"Consumer Goods","VEDL":"Metals","VENKEYS":"Consumer Goods","VINATIORGA":"Chemicals","IDEA":"Telecom","VOLTAS":"Consumer Goods","WABCOINDIA":"Automobile","WELCORP":"Metals","WELSPUNIND":"Textiles","WHIRLPOOL":"Consumer Goods","WIPRO":"IT","WOCKPHARMA":"Pharma","YESBANK":"Financial Services","ZEEL":"Media & Entertainment","ZENSARTECH":"IT","ZYDUSWELL":"Consumer Goods","ECLERX":"IT"}

# ============================================================
# AUTH
# ============================================================
def build_login_url():
    return (
        f"https://api.upstox.com/v2/login/authorization/dialog"
        f"?response_type=code&client_id={API_KEY}&redirect_uri={REDIRECT_URI}"
    )

def exchange_code_for_token(code):
    global access_token, headers
    resp = requests.post(
        "https://api.upstox.com/v2/login/authorization/token",
        data={
            "code": code,
            "client_id": API_KEY,
            "client_secret": API_SECRET,
            "redirect_uri": REDIRECT_URI,
            "grant_type": "authorization_code",
        },
    )
    data = resp.json()
    if resp.status_code == 200 and "access_token" in data:
        access_token = data["access_token"]
        headers = {"Authorization": f"Bearer {access_token}", "Accept": "application/json"}
        return True, data
    return False, data

# ============================================================
# SETUP: instrument master + stock universe (run once at startup)
# ============================================================
def load_universe():
    global master_df, stocks_to_test, orb_stocks_to_test
    master_df = pd.read_csv("https://assets.upstox.com/market-quote/instruments/exchange/NSE.csv.gz")

    # "Go all-in": scan every liquid NSE equity Upstox lists, not just the
    # hardcoded Nifty 500 set. instrument_type == "EQUITY" is Upstox's
    # regular cash-market equity series (confirmed live against the real
    # file — this excludes options, futures, indices, and currency
    # contracts). If this file's columns ever change shape (Upstox has
    # flagged the CSV instrument files as being deprecated in favour of
    # JSON), fall back to a regex heuristic on the ticker itself so a
    # schema change degrades gracefully instead of crashing startup.
    if "instrument_type" in master_df.columns:
        # lot_size == 1 separates NSE main-board equities (always traded in
        # single-share lots) from the SME/Emerge platform, which shares the
        # same instrument_type="EQUITY" label but is a much smaller, far
        # less liquid universe — without this, "EQUITY" alone pulled in
        # ~9,500 rows, nowhere close to a liquid main-board count (~2,100).
        eq_df = master_df[(master_df["instrument_type"] == "EQUITY") & (master_df["lot_size"] == 1)]
    else:
        print("[startup] WARNING: 'instrument_type' column missing from instrument file — "
              "falling back to a ticker-pattern filter. Check Upstox's CSV schema hasn't changed.")
        looks_like_equity = master_df["tradingsymbol"].astype(str).str.match(r"^[A-Z0-9&\-]{1,20}$")
        not_derivative = ~master_df["tradingsymbol"].astype(str).str.contains(r"\d{2}[A-Z]{3}\d|CE$|PE$|FUT$")
        eq_df = master_df[looks_like_equity & not_derivative]

    matched = []
    seen = set()
    for _, row in eq_df.iterrows():
        symbol = row["tradingsymbol"]
        if symbol in seen or pd.isna(symbol):
            continue
        seen.add(symbol)
        # Known Nifty 500 names keep their real sector; anything else
        # (the long tail of mid/small caps) is labelled "Other" since
        # there's no sector master for those — dashboard groups them
        # into an "Other" bucket rather than guessing.
        sector = SYMBOL_SECTOR_MAP.get(symbol, "Other")
        matched.append((symbol, row["instrument_key"], sector))

    stocks_to_test = matched
    orb_stocks_to_test = [s for s in matched if s[2] != "Other"]
    known_sector_count = len(orb_stocks_to_test)
    print(f"[startup] Universe loaded: {len(stocks_to_test)} stocks "
          f"({known_sector_count} with a known sector, {len(stocks_to_test) - known_sector_count} labelled 'Other'). "
          f"ORB sweep scoped to the {known_sector_count} known-sector stocks to keep its 3-min cadence.")

# ============================================================
# DAILY CACHE — indicators from daily candles, rebuilt once/day
# ============================================================
def build_daily_cache(reset_break_log=True):
    global daily_cache, break_log, break_state, candle_break_state
    if not headers:
        print("[daily_cache] Skipped — not logged in yet today")
        return

    if reset_break_log:
        break_log = {"ORB": {}, "DRB": {}}
        break_state = {"ORB": {}, "DRB": {}}  # fresh day, fresh breakout-log tracking
        candle_break_state = {}

    new_cache = {}
    source_list = orb_stocks_to_test if SCAN_MODE == "nifty500" else stocks_to_test
    for symbol, ikey, sector in source_list:
        try:
            to_date = datetime.date.today().strftime("%Y-%m-%d")
            from_date = (datetime.date.today() - datetime.timedelta(days=60)).strftime("%Y-%m-%d")
            hist_url = f"https://api.upstox.com/v2/historical-candle/{ikey}/day/{to_date}/{from_date}"
            candles = requests.get(hist_url, headers=headers).json()["data"]["candles"]
            df = pd.DataFrame(list(reversed(candles)), columns=["timestamp","open","high","low","close","volume","oi"])
            df[["open","high","low","close","volume"]] = df[["open","high","low","close","volume"]].astype(float)

            df["ema9"] = df["close"].ewm(span=9, adjust=False).mean()
            delta = df["close"].diff()
            gain, loss = delta.where(delta > 0, 0), -delta.where(delta < 0, 0)
            rs = gain.rolling(14).mean() / loss.rolling(14).mean()
            df["rsi14"] = 100 - (100 / (1 + rs))
            df["adx14"] = ADXIndicator(df["high"], df["low"], df["close"], window=14).adx()
            macd_calc = MACD(close=df["close"])
            df["macd"], df["macd_signal"] = macd_calc.macd(), macd_calc.macd_signal()
            df["atr14"] = AverageTrueRange(df["high"], df["low"], df["close"], window=14).average_true_range()

            hl2 = (df["high"] + df["low"]) / 2
            upperband, lowerband = hl2 + 3*df["atr14"], hl2 - 3*df["atr14"]
            supertrend = [True] * len(df)
            for i in range(1, len(df)):
                if df["close"].iloc[i] > upperband.iloc[i-1]: supertrend[i] = True
                elif df["close"].iloc[i] < lowerband.iloc[i-1]: supertrend[i] = False
                else: supertrend[i] = supertrend[i-1]
            df["supertrend_dir"] = ["Uptrend" if s else "Downtrend" for s in supertrend]

            latest, yesterday = df.iloc[-1], df.iloc[-2]
            pivot = (yesterday["high"] + yesterday["low"] + yesterday["close"]) / 3
            name_row = master_df[master_df["tradingsymbol"] == symbol]
            company_name = name_row["name"].values[0] if len(name_row) else symbol

            new_cache[symbol] = {
                "instrument_key": ikey, "sector": sector, "name": company_name,
                "ema9": latest["ema9"], "rsi14": latest["rsi14"], "adx14": latest["adx14"],
                "macd": latest["macd"], "macd_signal": latest["macd_signal"],
                "supertrend_dir": latest["supertrend_dir"], "pivot": pivot,
                "yesterday_close": yesterday["close"], "yesterday_high": yesterday["high"],
                "yesterday_low": yesterday["low"],
                "avg_daily_volume": df["volume"].iloc[-16:-1].mean(),
            }
        except Exception as e:
            print(f"[daily_cache] {symbol} failed: {e}")
        time.sleep(0.1)

    daily_cache = new_cache
    print(f"[daily_cache] Built for {len(daily_cache)} of {len(source_list)} stocks (mode: {SCAN_MODE})")
    build_index_cache()
    populate_stale_orb_breaklog()

def populate_stale_orb_breaklog():
    """
    The live ORB Break Log only fills in from the real-time sweep, which only
    runs during actual market hours — so on a closed day (weekend/holiday) or
    before today's session opens, it would otherwise just stay empty all day.
    This reuses the exact same day-walk logic /backtest uses, automatically
    targeted at the most recent real trading day, so there's always something
    real to look at instead of a blank column.
    """
    now = datetime.datetime.now()
    market_is_live_now = (now.weekday() < 5) and (datetime.time(9,15) <= now.time() <= datetime.time(15,30))
    if market_is_live_now:
        return  # the real sweep handles this live, no need for a stand-in

    print("[stale_breaklog] Market not live — reconstructing last trading day's ORB break log…")
    for days_back in range(0, 8):
        candidate_date = now.date() - datetime.timedelta(days=days_back)
        if candidate_date.weekday() >= 5:
            continue  # skip weekends
        date_str = candidate_date.strftime("%Y-%m-%d")
        results = run_backtest(date_str, "ORB")
        if results:
            filled = 0
            for row in results:
                if row["break_log"]:
                    break_log["ORB"][row["symbol"]] = row["break_log"]
                    filled += 1
            print(f"[stale_breaklog] Populated from {date_str} — {filled} of {len(results)} stocks had break activity")
            return
    print("[stale_breaklog] Could not find a usable recent trading day within the last week")

# ============================================================
# ORB CACHE — opening range, captured once/day after the window closes
# ============================================================
def build_orb_cache():
    global orb_cache
    if not headers:
        print("[orb_cache] Skipped — not logged in yet today")
        return

    market_open = datetime.datetime.combine(datetime.date.today(), datetime.time(9,15))
    window_end = market_open + datetime.timedelta(minutes=ORB_WINDOW_MINUTES)
    new_cache = {}

    for symbol, ikey, sector in orb_stocks_to_test:
        try:
            intraday_url = f"https://api.upstox.com/v2/historical-candle/intraday/{ikey}/1minute"
            icandles = requests.get(intraday_url, headers=headers).json()["data"]["candles"]
            if not icandles:
                continue
            idf = pd.DataFrame(icandles, columns=["timestamp","open","high","low","close","volume","oi"])
            idf["ts"] = pd.to_datetime(idf["timestamp"]).dt.tz_localize(None)
            window_rows = idf[(idf["ts"] >= market_open) & (idf["ts"] <= window_end)]
            if len(window_rows) == 0:
                continue
            new_cache[symbol] = {
                "orb_high": window_rows["high"].astype(float).max(),
                "orb_low": window_rows["low"].astype(float).min(),
            }
        except Exception as e:
            print(f"[orb_cache] {symbol} failed: {e}")
        time.sleep(0.1)

    orb_cache = new_cache
    print(f"[orb_cache] Captured for {len(orb_cache)} of {len(orb_stocks_to_test)} stocks")

def check_orb_candle_breaks():
    """
    Runs periodically (every ~3 min during market hours). For each stock with
    a captured opening range, looks at the most recently CLOSED 3-minute
    candle and checks whether its close price is beyond the ORB high/low —
    that's what counts as a real, confirmed break (not just a live tick
    poking across the line for a moment).

    If a stock was already confirmed broken and a later 3-min candle closes
    back inside the range, the break is cancelled — logged as a distinct
    "reversed" entry in the Break Log, not silently erased.
    """
    global candle_break_state
    if not headers or not orb_cache:
        return

    now = datetime.datetime.now()
    for symbol, info in orb_cache.items():
        if symbol not in daily_cache:
            continue
        ikey = daily_cache[symbol]["instrument_key"]
        try:
            intraday_url = f"https://api.upstox.com/v2/historical-candle/intraday/{ikey}/1minute"
            icandles = requests.get(intraday_url, headers=headers).json()["data"]["candles"]
            if not icandles or len(icandles) < 3:
                continue

            idf = pd.DataFrame(icandles, columns=["timestamp","open","high","low","close","volume","oi"])
            idf["ts"] = pd.to_datetime(idf["timestamp"]).dt.tz_localize(None)
            idf = idf.sort_values("ts")
            idf["close"] = idf["close"].astype(float)
            idf = idf.set_index("ts")

            # Resample into 3-min bars; use only the most recently fully-CLOSED one
            bars_3min = idf["close"].resample("3min").last().dropna()
            if len(bars_3min) < 2:
                continue
            last_closed_bar = bars_3min.iloc[-2]  # -1 would be the still-forming, incomplete bar

            orb_high, orb_low = info["orb_high"], info["orb_low"]
            confirmed_dir = "up" if last_closed_bar > orb_high else ("down" if last_closed_bar < orb_low else None)
            prev_dir = candle_break_state.get(symbol)

            if confirmed_dir != prev_dir:
                candle_break_state[symbol] = confirmed_dir
                log = break_log["ORB"].setdefault(symbol, [])
                if confirmed_dir is not None:
                    log.append({"time": now.strftime("%H:%M"), "rvol": None, "dir": confirmed_dir})
                elif prev_dir is not None:
                    # Was broken, now closed back inside the range — log the reversal distinctly
                    log.append({"time": now.strftime("%H:%M"), "rvol": None, "dir": "reversed"})
                del log[:-MAX_BREAK_LOG_ENTRIES]
        except Exception as e:
            print(f"[orb_candle_check] {symbol} failed: {e}")
        time.sleep(0.1)

    print(f"[orb_candle_check] Swept {len(orb_cache)} stocks — {sum(1 for v in candle_break_state.values() if v)} currently confirmed-broken")

# ============================================================
# LIVE REFRESH — one batched quote call, combined with cached indicators
# ============================================================
# ============================================================
# INDEX CACHE — real Nifty/BankNifty/Sensex/VIX etc, replacing
# the dashboard's old mock numbers
# ============================================================
def build_index_cache():
    global index_cache
    if not headers:
        return
    new_cache = {}
    today = datetime.date.today()
    to_date = today.strftime("%Y-%m-%d")
    from_date = (today - datetime.timedelta(days=15)).strftime("%Y-%m-%d")
    is_weekend_today = today.weekday() >= 5

    for display_name, ikey in INDEX_KEYS.items():
        try:
            hist_url = f"https://api.upstox.com/v2/historical-candle/{ikey}/day/{to_date}/{from_date}"
            candles = requests.get(hist_url, headers=headers).json()["data"]["candles"]
            if not candles:
                continue

            most_recent_date = pd.to_datetime(candles[0][0]).date()

            # If today already has a finished candle (market's closed for the day),
            # or today isn't even a trading day (weekend), the live quote mirrors
            # candles[0] exactly — comparing against it would always show 0.00%.
            # Use the session before that instead, so there's a real number to show.
            if (most_recent_date == today or is_weekend_today) and len(candles) > 1:
                prev_close = float(candles[1][4])
            else:
                prev_close = float(candles[0][4])

            new_cache[display_name] = {"prev_close": prev_close}
        except Exception as e:
            print(f"[index_cache] {display_name} ({ikey}) failed — skipping: {e}")
    index_cache = new_cache
    print(f"[index_cache] Built for {len(index_cache)} of {len(INDEX_KEYS)} indices")

def get_live_indices():
    if not headers or not index_cache:
        return []
    keys_param = ",".join(INDEX_KEYS[name] for name in index_cache.keys())
    try:
        quote_data = requests.get(
            "https://api.upstox.com/v2/market-quote/quotes",
            headers=headers, params={"instrument_key": keys_param}
        ).json().get("data", {})
    except Exception:
        return []

    results = []
    key_to_name = {v: k for k, v in INDEX_KEYS.items()}
    for entry in quote_data.values():
        ikey = entry.get("instrument_token")
        name = key_to_name.get(ikey)
        if not name or name not in index_cache:
            continue
        prev_close = index_cache[name]["prev_close"]
        last_price = entry["last_price"]
        chg_pct = ((last_price - prev_close) / prev_close) * 100 if prev_close else 0
        results.append({"name": name, "value": round(last_price, 2), "chg": round(chg_pct, 2)})
    return results

def fetch_global_indices():
    """Dow, S&P, FTSE, Nikkei etc — same {name, value, chg} shape as get_live_indices(),
    so the dashboard can render both with the same card component. Cached briefly since
    it's an unauthenticated public endpoint and we don't want to hit it on every poll."""
    global _global_index_cache
    now = time.time()
    if now - _global_index_cache["ts"] < GLOBAL_INDEX_CACHE_TTL and _global_index_cache["data"]:
        return _global_index_cache["data"]

    results = []
    for display_name, symbol in GLOBAL_INDEX_KEYS.items():
        try:
            url = f"https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
            resp = requests.get(
                url,
                headers={"User-Agent": "Mozilla/5.0"},
                params={"interval": "1d", "range": "1d"},
                timeout=5,
            )
            meta = resp.json()["chart"]["result"][0]["meta"]
            last_price = meta.get("regularMarketPrice")
            prev_close = meta.get("previousClose") or meta.get("chartPreviousClose")
            if last_price is None or not prev_close:
                continue
            chg_pct = ((last_price - prev_close) / prev_close) * 100
            results.append({"name": display_name, "value": round(last_price, 2), "chg": round(chg_pct, 2)})
        except Exception as e:
            print(f"[global_index] {display_name} ({symbol}) failed — skipping: {e}")

    # Only overwrite the cache if we got at least something back — a total Yahoo
    # outage shouldn't blank the dashboard, it should just keep showing stale numbers.
    if results:
        _global_index_cache = {"ts": now, "data": results, "updated_at": datetime.datetime.utcnow().isoformat() + "Z"}
    return _global_index_cache["data"]

def fetch_fii_dii():
    """Returns {"date", "fii": {"buy","sell","net"}, "dii": {...}} (values in Rs Cr, as NSE reports them),
    or None if NSE couldn't be reached / blocked the request. Cached — see FII_DII_CACHE_TTL above."""
    global _fii_dii_cache
    now = time.time()
    if now - _fii_dii_cache["ts"] < FII_DII_CACHE_TTL and _fii_dii_cache["data"]:
        return _fii_dii_cache["data"]

    try:
        session = requests.Session()
        session.headers.update(NSE_HEADERS)
        session.get("https://www.nseindia.com/", timeout=8)  # picks up cookies NSE requires before the API call
        resp = session.get("https://www.nseindia.com/api/fiidiiTradeReact", timeout=8)
        rows = resp.json()

        fii_row = next((r for r in rows if "FII" in r.get("category", "")), None)
        dii_row = next((r for r in rows if "DII" in r.get("category", "")), None)
        if not fii_row or not dii_row:
            print("[fii_dii] unexpected response shape — serving last known data")
            return _fii_dii_cache["data"]

        data = {
            "date": fii_row.get("date"),
            "fii": {
                "buy": float(fii_row["buyValue"]),
                "sell": float(fii_row["sellValue"]),
                "net": float(fii_row["netValue"]),
            },
            "dii": {
                "buy": float(dii_row["buyValue"]),
                "sell": float(dii_row["sellValue"]),
                "net": float(dii_row["netValue"]),
            },
        }
        _fii_dii_cache = {"ts": now, "data": data, "updated_at": datetime.datetime.utcnow().isoformat() + "Z"}
    except Exception as e:
        print(f"[fii_dii] fetch failed — serving last known data: {e}")

    return _fii_dii_cache["data"]

# ============================================================
# BACKTEST — same scoring logic, but for a chosen past date
# instead of "right now". DRB is reliable (daily candles only).
# ORB is best-effort (needs that day's 1-min candles, which
# aren't always available for older dates).
# ============================================================
def run_backtest(target_date_str, strategy="DRB", limit=None):
    if not headers:
        return []

    try:
        target_date = datetime.datetime.strptime(target_date_str, "%Y-%m-%d").date()
    except ValueError:
        return []

    stock_list = stocks_to_test[:limit] if limit else stocks_to_test

    results = []
    for symbol, ikey, sector in stock_list:
        try:
            to_date = target_date.strftime("%Y-%m-%d")
            from_date = (target_date - datetime.timedelta(days=180)).strftime("%Y-%m-%d")
            hist_url = f"https://api.upstox.com/v2/historical-candle/{ikey}/day/{to_date}/{from_date}"
            candles = requests.get(hist_url, headers=headers).json()["data"]["candles"]
            df = pd.DataFrame(list(reversed(candles)), columns=["timestamp","open","high","low","close","volume","oi"])
            df[["open","high","low","close","volume"]] = df[["open","high","low","close","volume"]].astype(float)
            df["date_only"] = pd.to_datetime(df["timestamp"]).dt.date

            if target_date not in set(df["date_only"]):
                continue  # not a trading day, or no data that far back for this stock
            target_idx = df.index[df["date_only"] == target_date][0]
            if target_idx < 60:
                continue  # not enough history for MACD/ADX/Supertrend to genuinely converge

            df = df.iloc[:target_idx + 1]  # only use data up to and including the target date

            df["ema9"] = df["close"].ewm(span=9, adjust=False).mean()
            df["ema20"] = df["close"].ewm(span=20, adjust=False).mean()
            delta = df["close"].diff()
            gain, loss = delta.where(delta > 0, 0), -delta.where(delta < 0, 0)
            rs = gain.rolling(14).mean() / loss.rolling(14).mean()
            df["rsi14"] = 100 - (100 / (1 + rs))
            df["adx14"] = ADXIndicator(df["high"], df["low"], df["close"], window=14).adx()
            macd_calc = MACD(close=df["close"])
            df["macd"], df["macd_signal"] = macd_calc.macd(), macd_calc.macd_signal()
            df["atr14"] = AverageTrueRange(df["high"], df["low"], df["close"], window=14).average_true_range()

            hl2 = (df["high"] + df["low"]) / 2
            upperband, lowerband = hl2 + 3*df["atr14"], hl2 - 3*df["atr14"]
            supertrend = [True] * len(df)
            for i in range(1, len(df)):
                if df["close"].iloc[i] > upperband.iloc[i-1]: supertrend[i] = True
                elif df["close"].iloc[i] < lowerband.iloc[i-1]: supertrend[i] = False
                else: supertrend[i] = supertrend[i-1]
            df["supertrend_dir"] = ["Uptrend" if s else "Downtrend" for s in supertrend]

            target_row, prior_row = df.iloc[-1], df.iloc[-2]
            pivot = (prior_row["high"] + prior_row["low"] + prior_row["close"]) / 3
            gap_pct = ((target_row["open"] - prior_row["close"]) / prior_row["close"]) * 100
            pct_change = ((target_row["close"] - prior_row["close"]) / prior_row["close"]) * 100
            avg_daily_volume = df["volume"].iloc[-16:-1].mean()
            rvol = target_row["volume"] / avg_daily_volume if avg_daily_volume else 0
            rvol_capped = round(min(rvol, RVOL_DISPLAY_CAP), 2)

            # Best-effort: fetch that specific day's 1-min candles, used for VWAP
            # (both strategies) and full break-log reconstruction (ORB only)
            orb_note = None
            vwap = None
            bt_break_log = []
            walk_dir = None
            try:
                intraday_url = f"https://api.upstox.com/v2/historical-candle/{ikey}/1minute/{to_date}/{to_date}"
                icandles = requests.get(intraday_url, headers=headers).json()["data"]["candles"]
                if not icandles:
                    raise ValueError("no intraday data for this date")

                idf = pd.DataFrame(icandles, columns=["timestamp","open","high","low","close","volume","oi"])
                idf["ts"] = pd.to_datetime(idf["timestamp"]).dt.tz_localize(None)
                idf = idf.sort_values("ts")
                idf[["close","volume"]] = idf[["close","volume"]].astype(float)

                total_vol = idf["volume"].sum()
                vwap = round((idf["close"] * idf["volume"]).sum() / total_vol, 2) if total_vol else None

                if strategy == "ORB":
                    idf_indexed = idf.set_index("ts")
                    window_start = datetime.datetime.combine(target_date, datetime.time(9,15))
                    window_end = window_start + datetime.timedelta(minutes=ORB_WINDOW_MINUTES)
                    window_rows = idf_indexed[(idf_indexed.index >= window_start) & (idf_indexed.index <= window_end)]
                    if len(window_rows) == 0:
                        raise ValueError("no candles in opening window")
                    orb_high = window_rows["high"].astype(float).max()
                    orb_low = window_rows["low"].astype(float).min()

                    # Walk the WHOLE day's 3-min bars chronologically, replaying
                    # the same confirm/reversal logic the live sweep uses
                    bars_3min = idf_indexed["close"].resample("3min").last().dropna()
                    market_open_dt = window_start - datetime.timedelta(minutes=ORB_WINDOW_MINUTES)  # actual 9:15 open
                    for bar_time, bar_close in bars_3min.items():
                        if bar_time < window_end:
                            continue  # still inside the opening range window itself
                        new_dir = "up" if bar_close > orb_high else ("down" if bar_close < orb_low else None)
                        if new_dir != walk_dir:
                            walk_dir = new_dir
                            if new_dir is not None or len(bt_break_log) > 0:
                                # Real point-in-time RVOL: cumulative volume so far today
                                # vs what's normally expected by this time of day
                                cum_vol = idf_indexed[idf_indexed.index <= bar_time]["volume"].sum()
                                elapsed_min = max((bar_time - market_open_dt).total_seconds() / 60, 1)
                                frac = min(max(elapsed_min / (6*60+15), 0.02), 1.0)
                                expected_vol = avg_daily_volume * frac
                                rvol_at_bar = round(min(cum_vol / expected_vol, RVOL_DISPLAY_CAP), 2) if expected_vol else 0
                                dir_label = new_dir if new_dir is not None else "reversed"
                                bt_break_log.append({"time": bar_time.strftime("%H:%M"), "rvol": rvol_at_bar, "dir": dir_label})
                    bt_break_log = bt_break_log[-5:]
            except Exception:
                if strategy == "ORB":
                    orb_note = "no_intraday_data"

            if strategy == "ORB":
                broke_high = walk_dir == "up"
                broke_low = walk_dir == "down"
            else:
                broke_high = target_row["close"] > prior_row["high"]
                broke_low = target_row["close"] < prior_row["low"]

            score = sum([
                1 if target_row["close"] > target_row["ema9"] else -1,
                1 if target_row["supertrend_dir"] == "Uptrend" else -1,
                1 if target_row["macd"] > target_row["macd_signal"] else -1,
                1 if target_row["rsi14"] > 55 else (-1 if target_row["rsi14"] < 45 else 0),
                1 if target_row["close"] > pivot else -1,
                1 if gap_pct > 0 else -1,
                1 if broke_high else (-1 if broke_low else 0),
            ])
            score_100 = int(((score + 7) / 14) * 100)
            signal = "BUY" if score_100 >= 65 else ("SELL" if score_100 <= 35 else "WATCH")
            if target_row["adx14"] < 20 or rvol < 1.0:
                signal = "WATCH"

            name_row = master_df[master_df["tradingsymbol"] == symbol]
            company_name = name_row["name"].values[0] if len(name_row) else symbol

            results.append({
                "symbol": symbol, "name": company_name, "sector": sector,
                "price": round(target_row["close"],2), "chg": round(pct_change,2),
                "score": score_100, "adx": round(target_row["adx14"],1),
                "rvol": rvol_capped, "signal": signal,
                "orb_note": orb_note,
                "break_log": bt_break_log,
                "technicals": {
                    "ema9": round(target_row["ema9"], 2),
                    "ema20": round(target_row["ema20"], 2),
                    "rsi14": round(target_row["rsi14"], 1),
                    "macd": round(target_row["macd"], 2),
                    "macd_signal": round(target_row["macd_signal"], 2),
                    "supertrend": target_row["supertrend_dir"],
                    "atr14": round(target_row["atr14"], 2),
                    "vwap": vwap,
                    "pivot": round(pivot, 2),
                },
            })
        except Exception as e:
            print(f"[backtest] {symbol} failed: {e}")
        time.sleep(0.1)

    return sorted(results, key=lambda r: r["rvol"], reverse=True)

def get_live_rows(strategy="ORB"):
    if not headers or not daily_cache:
        return pd.DataFrame()

    # Upstox's quotes endpoint caps out at 500 instrument keys per call.
    # This worked fine unbatched at 422 stocks, but silently breaks (or
    # gets truncated/rejected) once the universe grows past 500 — so this
    # now fires one request per 500-key chunk and merges the results.
    instrument_keys = [info["instrument_key"] for info in daily_cache.values()]
    quote_data = {}
    for i in range(0, len(instrument_keys), 500):
        chunk = instrument_keys[i:i+500]
        try:
            resp = requests.get(
                "https://api.upstox.com/v2/market-quote/quotes",
                headers=headers, params={"instrument_key": ",".join(chunk)}
            ).json().get("data", {})
            quote_data.update(resp)
        except Exception as e:
            print(f"[get_live_rows] quote batch {i}-{i+500} failed: {e}")

    now = datetime.datetime.now()
    market_is_live = (now.weekday() < 5) and (datetime.time(9,15) <= now.time() <= datetime.time(15,30))

    results = []
    for entry in quote_data.values():
        symbol = entry["symbol"]
        if symbol not in daily_cache:
            continue
        cache = daily_cache[symbol]

        live_price = entry["last_price"]
        today_volume = entry["volume"]
        today_open = entry["ohlc"]["open"]

        gap_pct = ((today_open - cache["yesterday_close"]) / cache["yesterday_close"]) * 100
        pct_change = ((live_price - cache["yesterday_close"]) / cache["yesterday_close"]) * 100

        if strategy == "ORB":
            # Use the candle-CLOSE-confirmed state (from check_orb_candle_breaks),
            # not a raw live-tick comparison — a brief poke across the line
            # that immediately reverses should never count as a real break
            confirmed = candle_break_state.get(symbol)
            broke_high = confirmed == "up"
            broke_low = confirmed == "down"
        else:
            broke_high = live_price > cache["yesterday_high"]
            broke_low = live_price < cache["yesterday_low"]

        elapsed_min = (now.hour*60+now.minute) - (9*60+15) if market_is_live else None

        if market_is_live:
            frac = min(max(elapsed_min / (6*60+15), 0.02), 1.0)
            expected_vol = cache["avg_daily_volume"] * frac
        else:
            expected_vol = cache["avg_daily_volume"]
        rvol = today_volume / expected_vol if expected_vol else 0
        rvol_capped = round(min(rvol, RVOL_DISPLAY_CAP), 2)

        # DRB still logs breaks the old way (live-tick, instant) — ORB's break
        # log is written separately by check_orb_candle_breaks() using actual
        # candle closes, so we only backfill this poll's RVOL into any entry
        # that was logged without one (candle-confirmed entries don't have
        # live quote data available at the moment they're detected)
        if strategy == "DRB":
            current_dir = "up" if broke_high else ("down" if broke_low else None)
            prev_dir = break_state[strategy].get(symbol)
            if current_dir != prev_dir:
                break_state[strategy][symbol] = current_dir
                if current_dir is not None:
                    log = break_log[strategy].setdefault(symbol, [])
                    log.append({"time": now.strftime("%H:%M"), "rvol": rvol_capped, "dir": current_dir})
                    del log[:-MAX_BREAK_LOG_ENTRIES]
        else:
            log = break_log["ORB"].get(symbol, [])
            for entry in log:
                if entry["rvol"] is None:
                    entry["rvol"] = rvol_capped

        score = sum([
            1 if live_price > cache["ema9"] else -1,
            1 if cache["supertrend_dir"] == "Uptrend" else -1,
            1 if cache["macd"] > cache["macd_signal"] else -1,
            1 if cache["rsi14"] > 55 else (-1 if cache["rsi14"] < 45 else 0),
            1 if live_price > cache["pivot"] else -1,
            1 if gap_pct > 0 else -1,
            1 if broke_high else (-1 if broke_low else 0),
        ])
        score_100 = int(((score + 7) / 14) * 100)
        signal = "BUY" if score_100 >= 65 else ("SELL" if score_100 <= 35 else "WATCH")
        if cache["adx14"] < 20 or rvol < 1.0:
            signal = "WATCH"

        # DRB confirmation delay: don't trust a DRB breakout in the first few
        # minutes after open (gap-driven, not a real intraday breakout yet)
        if strategy == "DRB" and market_is_live and elapsed_min < DRB_WINDOW_MINUTES:
            signal = "WATCH"

        results.append({
            "symbol": symbol, "name": cache["name"], "sector": cache["sector"],
            "price": round(live_price,2), "chg": round(pct_change,2),
            "score": score_100, "adx": round(cache["adx14"],1),
            "rvol": rvol_capped, "signal": signal, "live": market_is_live,
            "break_log": break_log[strategy].get(symbol, []),
            "level_high": round(orb_cache[symbol]["orb_high"], 2) if strategy == "ORB" and symbol in orb_cache else round(cache["yesterday_high"], 2),
            "level_low": round(orb_cache[symbol]["orb_low"], 2) if strategy == "ORB" and symbol in orb_cache else round(cache["yesterday_low"], 2)
        })

    return pd.DataFrame(results).sort_values("rvol", ascending=False) if results else pd.DataFrame()

# ============================================================
# BACKGROUND SCHEDULER — rebuilds caches at the right times,
# automatically, no manual cell-running needed
# ============================================================
def scheduler_loop():
    last_daily_build_date = None
    orb_built_today = False
    last_candle_check_minute = None

    while True:
        now = datetime.datetime.now()
        today = now.date()

        if headers and last_daily_build_date != today and now.time() >= datetime.time(9, 0):
            build_daily_cache()
            last_daily_build_date = today
            orb_built_today = False

        if headers and not orb_built_today and now.time() >= datetime.time(9, 30):
            build_orb_cache()
            orb_built_today = True

        market_is_live = (now.weekday() < 5) and (datetime.time(9, 30) <= now.time() <= datetime.time(15, 30))
        if headers and market_is_live and orb_built_today and now.minute % 3 == 0 and now.minute != last_candle_check_minute:
            last_candle_check_minute = now.minute
            check_orb_candle_breaks()

        time.sleep(60)

# ============================================================
# FASTAPI APP
# ============================================================
app = FastAPI()
app.add_middleware(CORSMiddleware, allow_origins=ALLOWED_ORIGINS, allow_methods=["*"], allow_headers=["*"])

# ============================================================
# ACCESS CONTROL — mobile numbers allowed to log in
# -------------------------------------------------------------------
# This used to live only in the frontend's localStorage, which meant
# a number the admin "added" only ever existed in the admin's own
# browser — nobody else's device ever saw it, so their login always
# failed. Source of truth now lives here on the backend (persisted to
# a JSON file so it survives restarts) and every client reads/writes
# through these endpoints instead.
# ============================================================
ADMIN_MOBILE = "7093508906"
ALLOWED_MOBILES_FILE = "allowed_mobiles.json"
DEFAULT_ALLOWED_MOBILES = [ADMIN_MOBILE, "9876543210", "9123456780", "9998887770"]

def load_allowed_mobiles():
    if os.path.exists(ALLOWED_MOBILES_FILE):
        try:
            with open(ALLOWED_MOBILES_FILE) as f:
                data = json.load(f)
            if isinstance(data, list) and data:
                return data
        except Exception as e:
            print(f"[allowed_mobiles] failed to read file, reseeding: {e}")
    save_allowed_mobiles(DEFAULT_ALLOWED_MOBILES)
    return list(DEFAULT_ALLOWED_MOBILES)

def save_allowed_mobiles(lst):
    with open(ALLOWED_MOBILES_FILE, "w") as f:
        json.dump(lst, f)

allowed_mobiles = load_allowed_mobiles()

@app.get("/allowed-mobiles")
def get_allowed_mobiles():
    return {"mobiles": allowed_mobiles}

@app.post("/allowed-mobiles")
async def add_allowed_mobile(request: Request):
    global allowed_mobiles
    body = await request.json()
    mobile = str(body.get("mobile", "")).strip()
    if not re.match(r"^[0-9]{10}$", mobile):
        return {"success": False, "error": "invalid_mobile"}
    if mobile not in allowed_mobiles:
        allowed_mobiles.append(mobile)
        save_allowed_mobiles(allowed_mobiles)
    return {"success": True, "mobiles": allowed_mobiles}

@app.delete("/allowed-mobiles/{mobile}")
def remove_allowed_mobile(mobile: str):
    global allowed_mobiles
    if mobile == ADMIN_MOBILE:
        return {"success": False, "error": "cannot_remove_admin"}
    allowed_mobiles = [m for m in allowed_mobiles if m != mobile]
    save_allowed_mobiles(allowed_mobiles)
    return {"success": True, "mobiles": allowed_mobiles}

# ============================================================
# NEWS — crisp per-symbol headlines, free (Google News RSS, no API key)
# -------------------------------------------------------------------
# Uses the company name from daily_cache (falls back to the raw symbol)
# so the search is specific enough to avoid unrelated same-name noise.
# Cached in-memory per symbol for NEWS_CACHE_TTL seconds so a burst of
# chart-modal opens for the same stock doesn't refetch every time.
# ============================================================
_news_cache = {}  # {symbol: (fetched_at_epoch, [articles])}
NEWS_CACHE_TTL = 300  # 5 minutes

def fetch_stock_news(symbol, limit=5):
    now = time.time()
    cached = _news_cache.get(symbol)
    if cached and now - cached[0] < NEWS_CACHE_TTL:
        return cached[1]

    company = daily_cache.get(symbol, {}).get("name", symbol)
    query = requests.utils.quote(f"{company} share NSE")
    url = f"https://news.google.com/rss/search?q={query}&hl=en-IN&gl=IN&ceid=IN:en"

    articles = []
    try:
        resp = requests.get(url, timeout=6, headers={"User-Agent": "Mozilla/5.0"})
        resp.raise_for_status()
        root = ET.fromstring(resp.content)
        for item in root.findall(".//item")[:limit]:
            title = (item.findtext("title") or "").strip()
            link = (item.findtext("link") or "").strip()
            pub_date = item.findtext("pubDate")
            source_el = item.find("source")
            source = source_el.text.strip() if source_el is not None and source_el.text else ""
            # Google News titles are usually "Headline - Source" — drop the
            # trailing source since we already surface it separately.
            if source and title.endswith(f" - {source}"):
                title = title[: -(len(source) + 3)].strip()

            time_ago = ""
            if pub_date:
                try:
                    dt = parsedate_to_datetime(pub_date)
                    delta = datetime.datetime.now(dt.tzinfo) - dt
                    hours = delta.total_seconds() / 3600
                    if hours < 1:
                        time_ago = f"{max(1, int(delta.total_seconds() / 60))}m ago"
                    elif hours < 24:
                        time_ago = f"{int(hours)}h ago"
                    else:
                        time_ago = f"{int(hours / 24)}d ago"
                except Exception:
                    time_ago = ""

            articles.append({"title": title, "source": source, "time_ago": time_ago, "link": link})
    except Exception as e:
        print(f"[news] {symbol} failed: {e}")

    _news_cache[symbol] = (now, articles)
    return articles

@app.get("/", response_class=HTMLResponse)
def home():
    status = "Logged in ✅" if access_token else "Not logged in — visit /login"
    return f"<h2>IntraBuss Scanner Backend</h2><p>Status: {status}</p><p><a href='/login'>Log in to Upstox</a></p>"

@app.get("/login")
def login():
    return RedirectResponse(build_login_url())

@app.get("/exchange")
def exchange(code: str):
    success, data = exchange_code_for_token(code)
    if success:
        threading.Thread(target=build_daily_cache, daemon=True).start()
        return {"success": True, "user": data.get("user_name", "")}
    return {"success": False, "error": data}

@app.get("/callback")
def callback(request: Request):
    code = request.query_params.get("code")
    if not code:
        return HTMLResponse("<h3>No code received. <a href='/login'>Try again</a></h3>")
    success, data = exchange_code_for_token(code)
    if success:
        threading.Thread(target=build_daily_cache, daemon=True).start()
        return HTMLResponse(f"<h3>✅ Logged in as {data.get('user_name','')}. You can close this tab.</h3>")
    return HTMLResponse(f"<h3>❌ Login failed: {data}</h3>")

@app.get("/scan/orb")
def scan_orb():
    return get_live_rows("ORB").to_dict(orient="records")

@app.get("/scan/drb")
def scan_drb():
    return get_live_rows("DRB").to_dict(orient="records")

@app.get("/indices")
def indices():
    return get_live_indices()

@app.get("/indices/global")
def indices_global():
    data = fetch_global_indices()
    return {"data": data, "updated_at": _global_index_cache["updated_at"]}

@app.get("/fii-dii")
def fii_dii():
    data = fetch_fii_dii()
    if not data:
        return {"available": False}
    return {"available": True, "updated_at": _fii_dii_cache["updated_at"], **data}

@app.get("/news/{symbol}")
def news(symbol: str):
    return {"symbol": symbol, "articles": fetch_stock_news(symbol)}

@app.get("/backtest")
def backtest(date: str, strategy: str = "DRB", limit: int = None):
    if strategy not in ("ORB", "DRB"):
        return {"error": "strategy must be ORB or DRB"}
    if not headers:
        return {"error": "not_logged_in"}
    return run_backtest(date, strategy, limit)

@app.get("/health")
def health():
    return {
        "logged_in": access_token is not None,
        "universe_size": len(stocks_to_test),
        "daily_cache_size": len(daily_cache),
        "orb_cache_size": len(orb_cache),
        "index_cache_size": len(index_cache),
        "global_index_cache_size": len(_global_index_cache["data"]),
        "fii_dii_available": _fii_dii_cache["data"] is not None,
        "orb_window_minutes": ORB_WINDOW_MINUTES,
        "drb_window_minutes": DRB_WINDOW_MINUTES,
        "scan_mode": SCAN_MODE,
        "scan_mode_sizes": {"nifty500": len(orb_stocks_to_test), "full": len(stocks_to_test)},
        "universe_rebuild": universe_rebuild_status,
    }

@app.post("/config")
async def update_config(request: Request):
    global ORB_WINDOW_MINUTES, DRB_WINDOW_MINUTES
    body = await request.json()
    if "orb_window_minutes" in body:
        ORB_WINDOW_MINUTES = int(body["orb_window_minutes"])
    if "drb_window_minutes" in body:
        DRB_WINDOW_MINUTES = int(body["drb_window_minutes"])
    return {"orb_window_minutes": ORB_WINDOW_MINUTES, "drb_window_minutes": DRB_WINDOW_MINUTES}

def _rebuild_daily_cache_in_background(mode):
    global universe_rebuild_status
    try:
        build_daily_cache(reset_break_log=False)
    finally:
        universe_rebuild_status = {"state": "idle", "mode": mode, "started_at": None}

@app.post("/config/scan-mode")
async def update_scan_mode(request: Request):
    global SCAN_MODE, universe_rebuild_status
    body = await request.json()
    mode = body.get("mode")
    if mode not in ("nifty500", "full"):
        return {"error": "mode must be 'nifty500' or 'full'"}
    if not headers:
        return {"error": "Not logged in yet today — can't rebuild until after login."}
    if universe_rebuild_status["state"] == "rebuilding":
        return {"error": "A rebuild is already in progress — wait for it to finish first."}

    SCAN_MODE = mode
    universe_rebuild_status = {
        "state": "rebuilding", "mode": mode,
        "started_at": datetime.datetime.now().strftime("%H:%M:%S"),
    }
    # Rebuilds a full daily cache pass (~3 min for nifty500, ~20-25 min for
    # full) — runs in the background so this request returns immediately;
    # the frontend polls /health for universe_rebuild.state to know when
    # it's done, and daily_cache stays serving the old data meanwhile.
    threading.Thread(target=_rebuild_daily_cache_in_background, args=(mode,), daemon=True).start()
    return {"scan_mode": SCAN_MODE, "status": "rebuild started"}

# ============================================================
# AI CHAT (Google Gemini) — asks a question about the stock
# currently open in the chart modal. The API key lives only in
# this server's environment (GEMINI_API_KEY) and is never sent
# to the frontend — the browser only ever talks to this endpoint.
# ============================================================
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "")
GEMINI_MODEL = "gemini-2.0-flash"

@app.post("/ai/ask")
async def ai_ask(request: Request):
    if not GEMINI_API_KEY:
        return {"error": "AI chat isn't configured yet — GEMINI_API_KEY isn't set on the server."}

    body = await request.json()
    question = (body.get("question") or "").strip()
    context = (body.get("context") or "").strip()
    if not question:
        return {"error": "No question provided."}
    if len(question) > 500:
        return {"error": "Question too long — keep it under 500 characters."}

    prompt = (
        "You are a trading assistant embedded in a personal NSE intraday scanner dashboard. "
        "Answer the user's question using ONLY the stock data given below — don't invent numbers. "
        "Be concise (3-5 sentences), plain language, no headers or bullet lists. "
        "This is informational, not financial advice — don't tell the user to buy/sell, just explain what the data shows.\n\n"
        f"--- Stock data ---\n{context}\n\n"
        f"--- Question ---\n{question}"
    )

    try:
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent?key={GEMINI_API_KEY}"
        resp = requests.post(url, json={"contents": [{"parts": [{"text": prompt}]}]}, timeout=20)
        resp.raise_for_status()
        data = resp.json()
        answer = data["candidates"][0]["content"]["parts"][0]["text"].strip()
        return {"answer": answer}
    except requests.exceptions.HTTPError:
        detail = ""
        try:
            detail = resp.json().get("error", {}).get("message", "")
        except Exception:
            pass
        return {"error": f"Gemini request failed ({resp.status_code}). {detail}"}
    except Exception as e:
        return {"error": f"Gemini request failed: {e}"}

# ============================================================
# STARTUP
# ============================================================
if __name__ == "__main__":
    load_universe()
    threading.Thread(target=scheduler_loop, daemon=True).start()
    uvicorn.run(app, host="0.0.0.0", port=8000)
