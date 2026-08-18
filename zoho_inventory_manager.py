"""
Maharani Inventory Tool — zoho_inventory_manager.py
======================================================
Streamlit app to create and update Items and Composite Packs
directly in Zoho Inventory (India) via REST API.

Run: streamlit run zoho_inventory_manager.py

ANTI-CIRCULAR-LOOP ARCHITECTURE
─────────────────────────────────
• st.session_state["items_list"] / ["composites_list"] written ONLY on form submit.
• st.data_editor with key="tbl_*" — edits live inside Streamlit's own key.
• Push buttons consume the data_editor return value directly at click time.
• "push_log" is append-only; cleared only by an explicit "Clear Log" button.
• NO DELETE endpoints are called anywhere in this file.

REQUIRED OAUTH SCOPE
─────────────────────
ZohoInventory.items.CREATE,ZohoInventory.items.READ,ZohoInventory.items.UPDATE,
ZohoInventory.compositeitems.CREATE,ZohoInventory.compositeitems.READ,
ZohoInventory.compositeitems.UPDATE,ZohoInventory.salesorders.READ,
ZohoInventory.salesorders.UPDATE,ZohoInventory.contacts.READ,
ZohoInventory.invoices.READ,ZohoInventory.packages.CREATE,
ZohoInventory.packages.READ,ZohoInventory.packages.UPDATE
"""

import os
import re
import time
import json
import random
import zipfile
from datetime import datetime, date, timedelta
from io import BytesIO

import base64
import uuid
import requests
import pandas as pd
import streamlit as st
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm
from reportlab.pdfgen import canvas as rl_canvas
from reportlab.graphics.barcode import code128 as bc_code128
from reportlab.pdfbase.pdfmetrics import stringWidth as bc_stringWidth

# ── PAGE CONFIG ───────────────────────────────────────────────────────────────
st.set_page_config(
    page_title="Maharani Inventory Tool",
    page_icon="🏺",
    layout="wide",
)

# ── CONSTANTS ─────────────────────────────────────────────────────────────────
# Looks for zoho_config.json next to this file, then falls back to parent dir
_HERE        = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE  = os.path.join(_HERE, "zoho_config.json")
if not os.path.exists(CONFIG_FILE):
    CONFIG_FILE = os.path.join(os.path.dirname(_HERE), "zoho_config.json")

ORG_ID         = "60056515070"
ZOHO_TOKEN_URL = "https://accounts.zoho.in/oauth/v2/token"
API_BASE       = "https://www.zohoapis.in/inventory/v1"
REQUIRED_SCOPE = (
    "ZohoInventory.items.CREATE,ZohoInventory.items.READ,ZohoInventory.items.UPDATE,"
    "ZohoInventory.compositeitems.CREATE,ZohoInventory.compositeitems.READ,"
    "ZohoInventory.compositeitems.UPDATE,"
    "ZohoInventory.salesorders.READ,ZohoInventory.salesorders.UPDATE,"
    "ZohoInventory.contacts.READ,ZohoInventory.invoices.READ,"
    "ZohoInventory.packages.CREATE,ZohoInventory.packages.READ,"
    "ZohoInventory.packages.UPDATE,"
    "ZohoInventory.shipmentorders.CREATE,ZohoInventory.shipmentorders.READ"
)

# ── LABEL CONSTANTS ───────────────────────────────────────────────────────────
LBL_FROM_HEADER = "From,"
LBL_FROM_NAME   = "Maharani Shrungar Material,"
LBL_FROM_LINES  = [
    "201, Ashashankar Plaza,",
    "Vidyanagar, Pimple Gurav,",
    "Pune - 411061",
    "Mob: 9429535959",
]
LBL_ALL_FROM = [LBL_FROM_HEADER, LBL_FROM_NAME] + LBL_FROM_LINES

_PAGE_W, _PAGE_H = A4
_LBL_MARGIN = 6 * mm
_LBL_W = (_PAGE_W - 2 * _LBL_MARGIN) / 2
_LBL_H = (_PAGE_H - 2 * _LBL_MARGIN) / 2
_LBL_POSITIONS = [
    (_LBL_MARGIN,           _LBL_MARGIN + _LBL_H),
    (_LBL_MARGIN + _LBL_W, _LBL_MARGIN + _LBL_H),
    (_LBL_MARGIN,           _LBL_MARGIN),
    (_LBL_MARGIN + _LBL_W, _LBL_MARGIN),
]

LBL_TABLE_COLS = ["✓", "Date", "Order #", "Name", "Address", "City/State", "Pincode", "Phone", "Amount"]

RATE_DELAY     = 0.3   # seconds between API calls — HTTP round-trip (~0.3s) + this stays under 100/min
CALL_WARN      = 70    # warn in sidebar above this many calls
CALL_HARD_STOP = 90    # refuse further writes until counter is reset

def _gen_sku() -> int:
    """
    Generate a 10-digit SKU matching Maharani's existing format (14xxxxxxxx).
    Uses 8 random digits after the '14' prefix.
    Collision probability for a batch of 100 items: ~0.0006% — negligible.
    The SKU is editable in the table before push.
    """
    return int(f"14{random.randint(10_000_000, 99_999_999)}")

# ── COLUMN DEFINITIONS ────────────────────────────────────────────────────────
ITEM_COLS = [
    "Item Name", "SKU", "Unit", "Selling Price (₹)", "Purchase Price (₹)",
    "Product Type", "Item Type", "HSN/SAC", "Sales Description",
    "Sales Account", "Purchase Account", "Inventory Account",
    "Preferred Vendor", "Reorder Level",
]

COMP_COLS = [
    "Composite Item Name", "SKU", "Unit", "Selling Price (₹)", "Purchase Price (₹)",
    "Mapped Item Name", "Mapped Item SKU", "Mapped Quantity", "Combo Type",
]

# ── SESSION STATE INIT ────────────────────────────────────────────────────────
_defaults: dict = {
    "items_list":      [],
    "composites_list": [],
    "push_log":        [],
    "item_id_map":     {},    # item_name → zoho_item_id
    "check_items":     None,
    "check_comps":     None,
    "lbl_order_df":    None,  # label tab: loaded order DataFrame
    "lbl_oid_list":    [],    # label tab: salesorder_id per row (parallel to lbl_order_df)
    "lbl_fetch_dates": (date.today(), date.today()),
    "api_call_times":  [],  # sliding window: list of timestamps (float) for last 60s
    "token":           None,
    "token_expiry":    0.0,
    # ── Existing Zoho Item search (czf_ prefix) ──
    "czf_results":     [],    # cached search results
    "czf_query":       "",    # last search query shown
    "czf_selected":    [],    # list of selected base item dicts (multi-select)
}
for _k, _v in _defaults.items():
    if _k not in st.session_state:
        st.session_state[_k] = _v


# ════════════════════════════════════════════════════════════════════════════════
# AUTH LAYER
# ════════════════════════════════════════════════════════════════════════════════
def load_cfg() -> dict:
    # Session-state override — set by save_cfg when filesystem is read-only (Streamlit Cloud)
    if st.session_state.get("_cfg_override"):
        return st.session_state["_cfg_override"]
    # Try local JSON file (local dev / Windows install)
    if os.path.exists(CONFIG_FILE):
        raw = open(CONFIG_FILE).read().strip()
        if raw:
            try:
                return json.loads(raw)
            except Exception:
                pass
    # Fall back to Streamlit Cloud secrets
    try:
        sec = st.secrets.get("zoho", {})
        if sec:
            return {
                "client_id":     sec.get("client_id", ""),
                "client_secret": sec.get("client_secret", ""),
                "refresh_token": sec.get("refresh_token", ""),
            }
    except Exception:
        pass
    return {}


def save_cfg(cfg: dict):
    try:
        with open(CONFIG_FILE, "w") as f:
            json.dump(cfg, f, indent=2)
    except Exception:
        # Streamlit Cloud has a read-only filesystem — persist in session state for this session
        st.session_state["_cfg_override"] = cfg
        st.warning(
            "⚠️ Running on Streamlit Cloud — credentials saved for this session only. "
            "To make permanent, go to your app's **Manage app → Secrets** and update: "
            f" under .",
            icon="⚠️",
        )


def get_token() -> str:
    """Return a valid Zoho access token. Caches in session state for 55 min."""
    if (st.session_state["token"]
            and time.time() < st.session_state["token_expiry"] - 120):
        return st.session_state["token"]

    cfg = load_cfg()
    missing = [k for k in ("client_id", "client_secret", "refresh_token") if not cfg.get(k)]
    if missing:
        raise ValueError(
            f"zoho_config.json is missing: {missing}. "
            "Configure credentials in the sidebar → Setup / Re-authorize."
        )

    resp = requests.post(ZOHO_TOKEN_URL, data={
        "refresh_token": cfg["refresh_token"],
        "client_id":     cfg["client_id"],
        "client_secret": cfg["client_secret"],
        "grant_type":    "refresh_token",
    }, timeout=15)
    data = resp.json()
    if "access_token" not in data:
        raise ValueError(f"Token refresh failed: {data}")

    st.session_state["token"]        = data["access_token"]
    st.session_state["token_expiry"] = time.time() + 3600  # Zoho tokens live 1 hr
    return st.session_state["token"]


def _hdrs(token: str) -> dict:
    return {
        "Authorization": f"Zoho-oauthtoken {token}",
        "Content-Type":  "application/json",
    }


def _is_auth_error(resp_json: dict) -> bool:
    """Detect Zoho 'not authorized' errors regardless of how they're phrased."""
    msg = str(resp_json.get("message", "")).lower()
    code = resp_json.get("code", 0)
    return "not authorized" in msg or "unauthorized" in msg or code == 57


def _raise_if_auth_error(resp_json: dict, context: str = ""):
    """Raise a clear, actionable error when the token lacks required scopes."""
    if _is_auth_error(resp_json):
        raise PermissionError(
            f"❌ Not authorized{f' ({context})' if context else ''}. "
            "The saved token is missing write scopes.\n\n"
            "**Fix:** Sidebar → Setup / Re-authorize → generate a new code at "
            "api-console.zoho.in with the full scope shown there → Exchange Code."
        )


def _tick():
    """Track one API call and enforce rate-limit delay."""
    st.session_state["api_call_times"].append(time.time())
    time.sleep(RATE_DELAY)


def _call_guard():
    """Block if >= CALL_HARD_STOP calls were made in the last 60 seconds (sliding window)."""
    now    = time.time()
    recent = [t for t in st.session_state["api_call_times"] if now - t < 60]
    st.session_state["api_call_times"] = recent          # prune expired entries
    if len(recent) >= CALL_HARD_STOP:
        wait_s = max(1, int(60 - (now - min(recent))) + 1)
        raise RuntimeError(
            f"Rate limit: {len(recent)} calls in the last 60 s (max {CALL_HARD_STOP}). "
            f"Wait ~{wait_s}s and try again, or click Reset in the sidebar."
        )


# ════════════════════════════════════════════════════════════════════════════════
# ZOHO API — READ (GET)
# ════════════════════════════════════════════════════════════════════════════════
def find_item(token: str, name: str) -> tuple:
    """Returns (item_id, item_dict) or (None, None)."""
    _call_guard()
    resp = requests.get(
        f"{API_BASE}/items",
        params={"organization_id": ORG_ID, "name": name},
        headers=_hdrs(token), timeout=15,
    )
    _tick()
    for item in resp.json().get("items", []):
        if item.get("name", "").strip().lower() == name.strip().lower():
            return item["item_id"], item
    return None, None


def find_composite(token: str, name: str) -> tuple:
    """Returns (composite_item_id, item_dict) or (None, None)."""
    _call_guard()
    resp = requests.get(
        f"{API_BASE}/compositeitems",
        params={"organization_id": ORG_ID, "name": name},
        headers=_hdrs(token), timeout=15,
    )
    _tick()
    for item in resp.json().get("composite_items", []):
        if item.get("name", "").strip().lower() == name.strip().lower():
            return item["composite_item_id"], item
    return None, None


def find_item_by_sku(token: str, sku: str) -> str | None:
    """Returns item_id by SKU lookup."""
    if not sku or sku == "nan":
        return None
    _call_guard()
    resp = requests.get(
        f"{API_BASE}/items",
        params={"organization_id": ORG_ID, "sku": str(sku)},
        headers=_hdrs(token), timeout=15,
    )
    _tick()
    items = resp.json().get("items", [])
    return items[0]["item_id"] if items else None


# ════════════════════════════════════════════════════════════════════════════════
# ZOHO API — WRITE (POST / PUT)   ← NO DELETE anywhere
# ════════════════════════════════════════════════════════════════════════════════
def create_item(token: str, payload: dict) -> dict:
    _call_guard()
    resp = requests.post(
        f"{API_BASE}/items",
        params={"organization_id": ORG_ID},
        json=payload, headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, "POST /items")
    return data


def update_item(token: str, item_id: str, payload: dict) -> dict:
    _call_guard()
    resp = requests.put(
        f"{API_BASE}/items/{item_id}",
        params={"organization_id": ORG_ID},
        json=payload, headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, "PUT /items")
    return data


def create_composite(token: str, payload: dict) -> dict:
    _call_guard()
    resp = requests.post(
        f"{API_BASE}/compositeitems",
        params={"organization_id": ORG_ID},
        json=payload, headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, "POST /compositeitems")
    return data


def update_composite(token: str, comp_id: str, payload: dict) -> dict:
    _call_guard()
    resp = requests.put(
        f"{API_BASE}/compositeitems/{comp_id}",
        params={"organization_id": ORG_ID},
        json=payload, headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, "PUT /compositeitems")
    return data


def fetch_salesorders_by_date(token: str, d: date, status: str) -> list:
    """Fetch sales orders for a single calendar date (label tab uses this)."""
    _call_guard()
    params: dict = {"organization_id": ORG_ID, "date": d.isoformat(), "per_page": 200}
    if status.lower() != "all":
        params["status"] = status.lower()
    resp = requests.get(f"{API_BASE}/salesorders", params=params,
                        headers=_hdrs(token), timeout=15)
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, "GET /salesorders (by date)")
    return data.get("salesorders", [])


def fetch_salesorders(token: str, status: str = "confirmed", per_page: int = 50) -> list:
    _call_guard()
    resp = requests.get(
        f"{API_BASE}/salesorders",
        params={
            "organization_id": ORG_ID,
            "status":          status,
            "per_page":        per_page,
            "sort_column":     "date",
            "sort_order":      "D",
        },
        headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, "GET /salesorders")
    return data.get("salesorders", [])


def get_salesorder_detail(token: str, order_id: str) -> dict:
    _call_guard()
    resp = requests.get(
        f"{API_BASE}/salesorders/{order_id}",
        params={"organization_id": ORG_ID},
        headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, f"GET /salesorders/{order_id}")
    return data.get("salesorder", {})


def get_packages_for_order(token: str, salesorder_id: str) -> list:
    """GET /packages?filter_by=salesorder_id — returns packages for a specific SO.
    Zoho ignores salesorder_id as a bare param on the list endpoint; use filter_by.
    Falls back to checking each package's salesorder_id field if needed.
    """
    _call_guard()
    resp = requests.get(
        f"{API_BASE}/packages",
        params={
            "organization_id": ORG_ID,
            "filter_by":       f"SalesOrder.salesorder_id={salesorder_id}",
        },
        headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, f"GET /packages (filter so_id={salesorder_id})")
    pkgs = data.get("packages", [])
    # Extra safety: filter locally in case filter_by returns unrelated packages
    return [p for p in pkgs if str(p.get("salesorder_id", "")) == str(salesorder_id)]


def create_package(token: str, salesorder_id: str, line_items: list,
                   pkg_date: str = "", notes: str = "") -> dict:
    """POST /packages — salesorder_id is a URL query param, NOT a body field (per Zoho docs)."""
    _call_guard()
    payload: dict = {
        "date":       pkg_date or datetime.now().strftime("%Y-%m-%d"),
        "line_items": line_items,
    }
    if notes:
        payload["notes"] = notes
    resp = requests.post(
        f"{API_BASE}/packages",
        params={"organization_id": ORG_ID, "salesorder_id": salesorder_id},
        json=payload,
        headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, f"POST /packages (so_id={salesorder_id})")
    return data


def create_shipment(token: str, salesorder_id: str, package_id: str,
                    carrier: str = "", tracking_number: str = "",
                    shipping_charge: float = 0.0, ship_date: str = "",
                    notes: str = "") -> dict:
    """POST /shipmentorders.
    package_ids must be a plain ID string in the URL query param (no JSON encoding).
    salesorder_id also in query params. organization_id required.
    """
    _call_guard()
    today = datetime.now().strftime("%Y-%m-%d")
    payload: dict = {
        "date":            ship_date or today,
        "delivery_method": carrier or "Others",
        "tracking_number": tracking_number or "",
    }
    if shipping_charge > 0:
        payload["shipping_charge"] = shipping_charge
    if notes:
        payload["notes"] = notes
    resp = requests.post(
        f"{API_BASE}/shipmentorders",
        params={
            "organization_id": ORG_ID,
            "salesorder_id":   salesorder_id,
            "package_ids":     package_id,   # plain ID string — confirmed correct format
        },
        json=payload,
        headers=_hdrs(token), timeout=15,
    )
    _tick()
    data = resp.json()
    _raise_if_auth_error(data, f"POST /shipmentorders (pkg={package_id})")
    return data


# ════════════════════════════════════════════════════════════════════════════════
# PAYLOAD BUILDERS
# ════════════════════════════════════════════════════════════════════════════════
def _f(v) -> float:
    """Safe float from any value (strips INR, commas etc.)."""
    return float(re.sub(r"[^\d.]", "", str(v or 0)) or 0)


def build_item_payload(row: dict) -> dict:
    return {
        "name":          str(row.get("Item Name", "")).strip(),
        "sku":           str(row.get("SKU", "")).strip(),
        "unit":          str(row.get("Unit", "pcs")).strip(),
        "rate":          _f(row.get("Selling Price (₹)", 0)),
        "purchase_rate": _f(row.get("Purchase Price (₹)", 0)),
        "product_type":  str(row.get("Product Type", "goods")).strip().lower(),
        "item_type":     str(row.get("Item Type", "inventory")).strip().lower(),
        "description":   str(row.get("Sales Description", "")).strip(),
        "hsn_or_sac":    str(row.get("HSN/SAC", "")).strip(),
        "reorder_level": int(row.get("Reorder Level", 0) or 0),
    }


def build_composite_payload(row: dict, component_item_id: str) -> dict:
    # Zoho item_type rules for composite items:
    #   kit      → "sales"     (bundle; component stock deducted on sale)
    #   assembly → "inventory" (finished good tracked as its own stock)
    combo_type = str(row.get("Combo Type", "Kit")).strip().lower()
    item_type  = "sales" if combo_type == "kit" else "inventory"
    return {
        "name":          str(row.get("Composite Item Name", "")).strip(),
        "sku":           str(row.get("SKU", "")).strip(),
        "unit":          str(row.get("Unit", "pack size")).strip(),
        "rate":          _f(row.get("Selling Price (₹)", 0)),
        "purchase_rate": _f(row.get("Purchase Price (₹)", 0)),
        "item_type":     item_type,
        "combo_type":    combo_type,
        "mapped_items": [
            {
                "item_id":  component_item_id,
                "quantity": float(row.get("Mapped Quantity", 1) or 1),
            }
        ],
    }


# ════════════════════════════════════════════════════════════════════════════════
# PUSH LOG
# ════════════════════════════════════════════════════════════════════════════════
_STATUS_COLORS = {
    "✅ Created":  "#d4edda",
    "✅ Updated":  "#cce5ff",
    "⏭️ Skipped": "#fff3cd",
    "❌ Error":    "#f8d7da",
    "🔬 Dry Run":  "#ede0f5",
}


def _log(name: str, action: str, status: str, item_id: str = "", note: str = ""):
    st.session_state["push_log"].append({
        "Time":    datetime.now().strftime("%H:%M:%S"),
        "Item":    name,
        "Action":  action,
        "Status":  status,
        "Item ID": item_id,
        "Note":    note,
    })


def _show_log():
    if not st.session_state["push_log"]:
        return
    df = pd.DataFrame(st.session_state["push_log"])

    def _color(row):
        c = _STATUS_COLORS.get(row["Status"], "")
        return [f"background-color: {c}"] * len(row)

    st.dataframe(
        df.style.apply(_color, axis=1),
        use_container_width=True,
        hide_index=True,
    )


# ════════════════════════════════════════════════════════════════════════════════
# SIDEBAR
# ════════════════════════════════════════════════════════════════════════════════
def _sidebar() -> tuple:
    """Returns (auth_ok: bool, dry_run: bool)."""
    st.sidebar.title("🏺 Maharani Inventory Tool")

    # ── Auth status ──
    cfg      = load_cfg()
    auth_ok  = all(cfg.get(k) for k in ("client_id", "client_secret", "refresh_token"))
    if auth_ok:
        st.sidebar.success("✅ Zoho credentials loaded")
    else:
        st.sidebar.error("❌ Not configured — see Setup below")

    # ── Dry Run toggle ──
    dry_run = st.sidebar.toggle("🔬 Dry Run (simulate, no writes)", value=False)

    # ── API call counter (sliding 60-second window) ──
    _now    = time.time()
    _recent = [t for t in st.session_state["api_call_times"] if _now - t < 60]
    st.session_state["api_call_times"] = _recent
    n = len(_recent)
    color = "green" if n < CALL_WARN else ("orange" if n < CALL_HARD_STOP else "red")
    st.sidebar.markdown(f"**API calls (last 60 s):** :{color}[{n} / {CALL_HARD_STOP}]")
    if n >= CALL_WARN:
        st.sidebar.warning(f"Approaching rate limit — {CALL_HARD_STOP - n} calls remaining this window.")
    if st.sidebar.button("🔄 Reset call counter"):
        st.session_state["api_call_times"] = []
        st.rerun()

    st.sidebar.divider()

    # ── Auth setup ──
    with st.sidebar.expander("🔧 Setup / Re-authorize", expanded=not auth_ok):
        st.caption(
            "Generate a Self Client at [api-console.zoho.in](https://api-console.zoho.in) "
            "with the scope below and paste the one-time code here."
        )
        st.code(REQUIRED_SCOPE, language=None)

        cid   = st.text_input("Client ID",     value=cfg.get("client_id", ""),     key="sb_cid")
        csec  = st.text_input("Client Secret", value=cfg.get("client_secret", ""), key="sb_cs", type="password")
        rtoken = st.text_input("Refresh Token (if you have one)", value="",          key="sb_rt", type="password")
        code  = st.text_input("One-time Code",                    value="",          key="sb_code")

        if st.button("🔑 Exchange Code → Refresh Token"):
            if cid and csec and code:
                try:
                    r = requests.post(ZOHO_TOKEN_URL, data={
                        "code":         code,
                        "client_id":    cid,
                        "client_secret":csec,
                        "redirect_uri": "https://www.zoho.in",
                        "grant_type":   "authorization_code",
                    }, timeout=15)
                    d = r.json()
                    if "refresh_token" in d:
                        save_cfg({"client_id": cid, "client_secret": csec, "refresh_token": d["refresh_token"]})
                        st.success("✅ Authorized! Refresh token saved.")
                        st.rerun()
                    else:
                        st.error(f"Exchange failed: {d}")
                except Exception as exc:
                    st.error(str(exc))
            else:
                st.warning("Fill in Client ID, Client Secret, and the one-time Code.")

        if st.button("💾 Save Credentials (refresh token already known)"):
            if cid and csec and rtoken:
                save_cfg({"client_id": cid, "client_secret": csec, "refresh_token": rtoken})
                st.success("Saved.")
                st.rerun()
            else:
                st.warning("All three fields are required.")

    return auth_ok, dry_run


# ════════════════════════════════════════════════════════════════════════════════
# ITEM-ID RESOLVER (used by composite & group push)
# ════════════════════════════════════════════════════════════════════════════════
def _resolve_item_id(token: str, item_name: str, item_sku: str) -> str | None:
    """
    Get the Zoho item_id for a base item.
    Priority: in-memory map → name lookup → SKU lookup.
    """
    item_name = (item_name or "").strip()
    item_sku  = str(item_sku or "").strip()

    if item_name and item_name in st.session_state["item_id_map"]:
        return st.session_state["item_id_map"][item_name]

    if item_name:
        iid, _ = find_item(token, item_name)
        if iid:
            st.session_state["item_id_map"][item_name] = iid
            return iid

    if item_sku and item_sku not in ("", "nan"):
        iid = find_item_by_sku(token, item_sku)
        if iid:
            if item_name:
                st.session_state["item_id_map"][item_name] = iid
            return iid

    return None


def _resolve_composite_id(token: str, comp_name: str) -> str | None:
    """
    Get the Zoho composite_item_id by name (used for composite CRUD operations).
    Cached with '__comp__' prefix.
    """
    comp_name = (comp_name or "").strip()
    if not comp_name:
        return None
    cache_key = f"__comp__{comp_name}"
    if cache_key in st.session_state["item_id_map"]:
        return st.session_state["item_id_map"][cache_key]
    cid, _ = find_composite(token, comp_name)
    if cid:
        st.session_state["item_id_map"][cache_key] = cid
    return cid




# ════════════════════════════════════════════════════════════════════════════════
# TAB 5 — BARCODE GENERATOR
# Self-contained: no Zoho auth needed. Upload any CSV, map columns, print labels.
# ════════════════════════════════════════════════════════════════════════════════

_BC_OVERRIDES_FILE     = "bc_label_overrides.json"
_BC_PRESETS_FILE       = "bc_layout_presets.json"
_BC_Y_RANGE            = (-5.0, 5.0)
_BC_DEFAULT_THRESHOLD  = 28
_BC_SHORT_PRESET = {
    "item_name_size": 9.0, "price_size": 8.5, "barcode_text_size": 7.5,
    "bar_width": 0.25, "bar_height": 7.0,
    "item_name_y": 1.0, "price_y": 1.5, "barcode_y": 2.75,
    "barcode_text_y": 1.75, "company_y": 1.25,
}
_BC_LONG_PRESET = {
    "item_name_size": 9.0, "price_size": 8.0, "barcode_text_size": 7.5,
    "bar_width": 0.27, "bar_height": 7.0,
    "item_name_y": 1.0, "price_y": 0.5, "barcode_y": 2.75,
    "barcode_text_y": 1.75, "company_y": 1.25,
}
_BC_MAPPING_FIELDS = [
    ("item_name",          "Item Name",       "Unknown Item", "text"),
    ("rate",               "Price / Rate",    "0",            "text"),
    ("unit",               "Unit",            "pcs",          "text"),
    ("sku",                "Barcode / SKU",   "",             "text"),
    ("quantity_purchased", "Print Count",     "1",            "number"),
]
_BC_COL_ALIASES = {
    "item_name":          ["item_name", "name", "product", "product_name", "description", "item"],
    "rate":               ["rate", "price", "mrp", "selling_price", "amount", "cost"],
    "unit":               ["unit", "uom", "unit_of_measure", "measure"],
    "sku":                ["sku", "barcode", "code", "product_code", "item_code", "upc", "ean"],
    "quantity_purchased": ["quantity_purchased", "qty", "quantity", "count", "print_count", "units"],
}


def _bc_load_overrides():
    if os.path.exists(_BC_OVERRIDES_FILE):
        try:
            return json.load(open(_BC_OVERRIDES_FILE))
        except Exception:
            pass
    return {}


def _bc_save_overrides(ov):
    try:
        json.dump(ov, open(_BC_OVERRIDES_FILE, "w"), indent=2)
    except Exception as e:
        st.warning(f"Could not save barcode overrides: {e}")


def _bc_load_presets():
    if os.path.exists(_BC_PRESETS_FILE):
        try:
            d = json.load(open(_BC_PRESETS_FILE))
            if "threshold" in d and "short" in d and "long" in d:
                return d
        except Exception:
            pass
    return {"threshold": _BC_DEFAULT_THRESHOLD,
            "short": dict(_BC_SHORT_PRESET),
            "long":  dict(_BC_LONG_PRESET)}


def _bc_save_presets(p):
    try:
        json.dump(p, open(_BC_PRESETS_FILE, "w"), indent=2)
    except Exception as e:
        st.warning(f"Could not save layout presets: {e}")


def _bc_fit_font(text, font, max_w, floor_s, ceil_s, step=0.5):
    s = ceil_s
    while s >= floor_s:
        if bc_stringWidth(text, font, s) <= max_w:
            return s
        s -= step
    return floor_s


def _bc_auto_defaults(item_name):
    p = st.session_state["bc_presets"]
    bucket = "short" if len(str(item_name)) <= p["threshold"] else "long"
    return dict(p[bucket])


def _bc_resolve_size(text, font, max_w, preferred, floor_s):
    if bc_stringWidth(text, font, preferred) <= max_w:
        return preferred
    return _bc_fit_font(text, font, max_w, floor_s, preferred)


def _bc_draw_item_name(c, name, pw, mw, font, floor_s, ceil_s,
                       forced=None, y_off=0.0):
    base_s = (19.5 + y_off) * mm
    base_1 = (20.5 + y_off) * mm
    base_2 = (17.5 + y_off) * mm

    if forced is not None:
        if bc_stringWidth(name, font, forced) <= mw:
            c.setFont(font, forced)
            c.drawCentredString(pw / 2.0, base_s, name)
            return
        wrap = forced
    else:
        best = _bc_fit_font(name, font, mw, floor_s, ceil_s)
        if best > floor_s and bc_stringWidth(name, font, best) <= mw:
            c.setFont(font, best); c.drawCentredString(pw / 2.0, base_s, name); return
        elif bc_stringWidth(name, font, floor_s) <= mw:
            c.setFont(font, floor_s); c.drawCentredString(pw / 2.0, base_s, name); return
        wrap = floor_s

    words, line1_w, split_i = name.split(), [], len(name.split())
    for i, w in enumerate(words):
        cand = " ".join(line1_w + [w])
        if bc_stringWidth(cand, font, wrap) <= mw:
            line1_w.append(w)
        else:
            split_i = i; break
    else:
        split_i = len(words)

    line2_w = []
    for w in words[split_i:]:
        cand = " ".join(line2_w + [w])
        if bc_stringWidth(cand, font, wrap) <= mw:
            line2_w.append(w)
        else:
            line2_w.append(".."); break

    c.setFont(font, wrap)
    c.drawCentredString(pw / 2.0, base_1, " ".join(line1_w))
    c.drawCentredString(pw / 2.0, base_2, " ".join(line2_w))


def _bc_generate_pdf(data, single_preview=False, overrides=None, live_override=None):
    overrides = overrides or {}
    buf = BytesIO()
    pw, ph = 38 * mm, 25 * mm
    c = rl_canvas.Canvas(buf, pagesize=(pw, ph))

    for _, row in data.iterrows():
        count   = 1 if single_preview else int(row["Print Count"])
        bkey    = str(row["Barcode Number"]).strip()
        iname   = str(row["Item Name"])
        if single_preview and live_override is not None:
            sett = live_override
        else:
            sett = overrides.get(bkey) or _bc_auto_defaults(iname)

        for _ in range(count):
            font, mw = "Helvetica", pw - 2 * mm
            _bc_draw_item_name(c, iname, pw, mw, font, 7.5, 11.0,
                               forced=sett["item_name_size"],
                               y_off=sett.get("item_name_y", 0.0))

            price_str  = str(row["Price"])
            price_size = _bc_resolve_size(price_str, font, mw, sett["price_size"], 6.0)
            c.setFont(font, price_size)
            c.drawCentredString(pw / 2.0, (15.0 + sett.get("price_y", 0.0)) * mm, price_str)

            bstr = bkey if (bkey and bkey.lower() != "nan") else "000000"
            bar  = bc_code128.Code128(bstr,
                                      barHeight=sett["bar_height"] * mm,
                                      barWidth=sett["bar_width"] * mm)
            bar.drawOn(c, (pw - bar.width) / 2.0, (4.8 + sett.get("barcode_y", 0.0)) * mm)

            bt_size = _bc_resolve_size(bstr, font, mw, sett["barcode_text_size"], 5.5)
            c.setFont(font, bt_size)
            c.drawCentredString(pw / 2.0, (3.0 + sett.get("barcode_text_y", 0.0)) * mm, bstr)

            co_size = _bc_fit_font("Maharani Shrungar", font, mw, 5.0, 7.5)
            c.setFont(font, co_size)
            c.drawCentredString(pw / 2.0, (1.0 + sett.get("company_y", 0.0)) * mm, "Maharani Shrungar")
            c.showPage()

    c.save(); buf.seek(0); return buf


def _bc_show_pdf_preview(buf):
    """Render a single-page PDF label as a PNG image via pymupdf.
    Avoids all sandbox/plugin restrictions in Streamlit's iframe.
    """
    try:
        import fitz  # pymupdf
        pdf_bytes = buf.read()
        doc = fitz.open(stream=pdf_bytes, filetype="pdf")
        page = doc[0]
        pix = page.get_pixmap(matrix=fitz.Matrix(5, 5))  # 5x zoom → crisp preview
        img_bytes = pix.tobytes("png")
        doc.close()
        st.image(img_bytes, use_container_width=True)
    except Exception as e:
        st.warning(f"Preview unavailable: {e}")


def _bc_apply_mapping(raw_df, mapping):
    def gcol(fk):
        m = mapping[fk]
        if m["col"] and m["col"] in raw_df.columns:
            return raw_df[m["col"]].astype(str)
        return pd.Series([m["default"]] * len(raw_df))

    iname = gcol("item_name").fillna("Unknown")
    rate  = gcol("rate").fillna("0")
    unit  = gcol("unit").fillna("pcs")
    sku   = gcol("sku").fillna("").str.replace(r"\.0$", "", regex=True)

    qm = mapping["quantity_purchased"]
    if qm["col"] and qm["col"] in raw_df.columns:
        try:
            pcount = raw_df[qm["col"]].fillna(1).astype(float).astype(int)
        except Exception:
            pcount = pd.Series([1] * len(raw_df))
    else:
        try:
            pcount = pd.Series([int(float(qm["default"]))] * len(raw_df))
        except Exception:
            pcount = pd.Series([1] * len(raw_df))

    return pd.DataFrame({
        "Select":         False,
        "Preview":        False,
        "Item Name":      iname.values,
        "Price":          ("Rs." + rate + " / " + unit).values,
        "Barcode Number": sku.values,
        "Print Count":    pcount.values,
    })


def _bc_auto_detect(field_key, csv_cols):
    for alias in _BC_COL_ALIASES.get(field_key, []):
        for col in csv_cols:
            if col.strip().lower() == alias:
                return col
    return None


@st.dialog("🎛️ Customize Barcode Label", width="large")
def _bc_customize_dialog(row):
    bkey  = str(row["Barcode Number"]).strip()
    saved = st.session_state["bc_overrides"].get(bkey)
    auto  = _bc_auto_defaults(row["Item Name"])
    defs  = dict(saved) if saved else dict(auto)
    for k, v in auto.items():
        defs.setdefault(k, v)

    rev  = st.session_state["bc_dialog_rev"]
    skeys = {k: f"bcov_{k}_{bkey}_{rev}" for k in auto}
    st.caption(f"**{row['Item Name']}**  •  Barcode: `{bkey or '000000'}`")
    sc, pc = st.columns([3, 2])

    with sc:
        st.markdown("##### Size")
        ns  = st.slider("Item Name Size",       6.0, 14.0, defs["item_name_size"],    0.5,  key=skeys["item_name_size"])
        ps  = st.slider("Price Size",           5.0, 12.0, defs["price_size"],        0.5,  key=skeys["price_size"])
        bts = st.slider("Barcode Number Size",  4.0, 10.0, defs["barcode_text_size"], 0.5,  key=skeys["barcode_text_size"])
        bw  = st.slider("Bar Width (mm)",       0.15, 0.40, defs["bar_width"],        0.01, key=skeys["bar_width"])
        bh  = st.slider("Bar Height (mm)",      5.0, 12.0, defs["bar_height"],        0.5,  key=skeys["bar_height"])
        st.markdown("##### Position (mm)")
        iny = st.slider("Item Name Y",  *_BC_Y_RANGE, defs["item_name_y"],    0.25, key=skeys["item_name_y"])
        py  = st.slider("Price Y",      *_BC_Y_RANGE, defs["price_y"],        0.25, key=skeys["price_y"])
        by  = st.slider("Barcode Y",    *_BC_Y_RANGE, defs["barcode_y"],      0.25, key=skeys["barcode_y"])
        bty = st.slider("Barcode Txt Y",*_BC_Y_RANGE, defs["barcode_text_y"], 0.25, key=skeys["barcode_text_y"])
        cy  = st.slider("Company Y",    *_BC_Y_RANGE, defs["company_y"],      0.25, key=skeys["company_y"])

    live = {"item_name_size": ns, "price_size": ps, "barcode_text_size": bts,
            "bar_width": bw, "bar_height": bh,
            "item_name_y": iny, "price_y": py, "barcode_y": by,
            "barcode_text_y": bty, "company_y": cy}

    with pc:
        st.markdown("##### Live Preview")
        _bc_show_pdf_preview(_bc_generate_pdf(pd.DataFrame([row]), single_preview=True, live_override=live))
        st.caption("🎨 Custom saved" if bkey in st.session_state["bc_overrides"] else "⚙️ Auto layout")

    st.divider()
    s1, s2, s3 = st.columns(3)
    with s1:
        if st.button("💾 Save", type="primary", use_container_width=True):
            st.session_state["bc_overrides"][bkey] = live
            _bc_save_overrides(st.session_state["bc_overrides"])
            st.toast(f"Saved for {row['Item Name']}")
            st.rerun()
    with s2:
        def _bc_reset(bk=bkey, ks=skeys, ad=auto):
            st.session_state["bc_overrides"].pop(bk, None)
            _bc_save_overrides(st.session_state["bc_overrides"])
            for f, kn in ks.items():
                st.session_state[kn] = ad[f]
        st.button("↺ Reset to Auto", use_container_width=True, on_click=_bc_reset)
    with s3:
        if st.button("✖️ Close", use_container_width=True):
            st.rerun()


def tab_barcode_generator():
    st.subheader("🏷️ Barcode Label Generator")
    st.caption("Upload any CSV, map columns to label fields, generate & download a printable PDF.")

    # ── Init session state ────────────────────────────────────────────────────
    bc_defaults = {
        "bc_inventory":   pd.DataFrame(),
        "bc_uploaded_df": None,
        "bc_uploaded_name": "",
        "bc_editor_key":  0,
        "bc_master_sel":  False,
        "bc_overrides":   None,
        "bc_presets":     None,
        "bc_dialog_rev":  0,
    }
    for k, v in bc_defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v
    if st.session_state["bc_overrides"] is None:
        st.session_state["bc_overrides"] = _bc_load_overrides()
    if st.session_state["bc_presets"] is None:
        st.session_state["bc_presets"] = _bc_load_presets()

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 1+2 — Upload & column mapping
    # ══════════════════════════════════════════════════════════════════════════
    if st.session_state["bc_inventory"].empty:
        uploaded = st.file_uploader("📂 Upload CSV", type=["csv"],
                                    help="Any CSV — Zoho export, Excel save-as-CSV, etc.")
        if uploaded is not None:
            try:
                st.session_state["bc_uploaded_df"]   = pd.read_csv(uploaded)
                st.session_state["bc_uploaded_name"] = uploaded.name
            except Exception as e:
                st.error(f"Could not read CSV: {e}"); return

        if st.session_state["bc_uploaded_df"] is None:
            st.info("Upload a CSV to get started — any column layout works.")
            return

        raw_df   = st.session_state["bc_uploaded_df"]
        csv_cols = list(raw_df.columns)
        none_opt = "(none — use default)"
        col_opts = [none_opt] + csv_cols

        st.subheader("🗂️ Map Columns")
        st.caption(
            f"**{st.session_state['bc_uploaded_name']}** — {len(raw_df)} rows, "
            f"{len(csv_cols)} columns. Pick the CSV column for each label field. "
            "If a column doesn't exist, leave it as '(none)' and set a default."
        )
        with st.expander("👁️ Preview CSV (first 5 rows)", expanded=False):
            st.dataframe(raw_df.head(5), use_container_width=True)

        st.divider()
        mapping = {}
        for (fk, label, default_val, input_type) in _BC_MAPPING_FIELDS:
            auto = _bc_auto_detect(fk, csv_cols)
            st.markdown(f"**{label}**")
            c1, c2 = st.columns([2, 2])
            with c1:
                idx = col_opts.index(auto) if auto and auto in col_opts else 0
                sel = st.selectbox(f"col_{fk}", col_opts, index=idx,
                                   key=f"bc_map_col_{fk}", label_visibility="collapsed")
                chosen = None if sel == none_opt else sel
            with c2:
                if chosen is None:
                    if input_type == "number":
                        dv = st.number_input(f"def_{fk}", min_value=1,
                                             value=int(default_val), step=1,
                                             key=f"bc_map_def_{fk}", label_visibility="collapsed")
                        default_used = str(int(dv))
                    else:
                        default_used = st.text_input(f"def_{fk}", value=default_val,
                                                     key=f"bc_map_def_{fk}",
                                                     placeholder=f"Default for {label}",
                                                     label_visibility="collapsed")
                else:
                    sample = raw_df[chosen].dropna().astype(str)
                    st.caption(f"Sample: `{sample.iloc[0] if not sample.empty else '—'}`")
                    default_used = default_val
            mapping[fk] = {"col": chosen, "default": default_used}

        st.divider()
        ca, cb = st.columns([2, 1])
        with ca:
            if st.button("✅ Apply Mapping & Generate Labels", type="primary", use_container_width=True):
                try:
                    st.session_state["bc_inventory"]  = _bc_apply_mapping(raw_df, mapping)
                    st.session_state["bc_editor_key"] += 1
                    st.rerun()
                except Exception as e:
                    st.error(f"Mapping error: {e}")
        with cb:
            if st.button("🔄 Upload Different File", use_container_width=True):
                st.session_state["bc_uploaded_df"]   = None
                st.session_state["bc_uploaded_name"] = ""
                st.rerun()
        return

    # ══════════════════════════════════════════════════════════════════════════
    # STEP 3 — Label editor
    # ══════════════════════════════════════════════════════════════════════════
    tb1, tb2, tb3 = st.columns([4, 2, 2])
    with tb1:
        if st.session_state["bc_uploaded_name"]:
            st.caption(f"📄 **{st.session_state['bc_uploaded_name']}**")
    with tb2:
        if st.button("⚙️ Layout Presets", use_container_width=True, key="bc_presets_btn"):
            st.session_state["bc_dialog_rev"] += 1
            _bc_presets_dialog()
    with tb3:
        if st.button("📂 Upload New CSV", use_container_width=True, key="bc_upload_new"):
            st.session_state["bc_inventory"]    = pd.DataFrame()
            st.session_state["bc_uploaded_df"]  = None
            st.session_state["bc_uploaded_name"] = ""
            st.session_state["bc_editor_key"]   += 1
            st.rerun()

    st.write("1. Check **Preview** to see a label. 2. Check **Select** + set **Quantity**. 3. Click Generate.")

    master = st.checkbox("☑️ Select / Unselect All", value=st.session_state["bc_master_sel"],
                         key="bc_master_chk")

    edited = st.data_editor(
        st.session_state["bc_inventory"],
        key=f"bc_editor_{st.session_state['bc_editor_key']}",
        num_rows="dynamic",
        column_config={
            "Select":         st.column_config.CheckboxColumn("Print?",     width="small",  default=False),
            "Preview":        st.column_config.CheckboxColumn("Preview",    width="small",  default=False),
            "Print Count":    st.column_config.NumberColumn("Qty",          width="small",  min_value=0, step=1, format="%d", default=1),
            "Item Name":      st.column_config.TextColumn("Item Name",      width="large",  default="New Item"),
            "Price":          st.column_config.TextColumn("Price",          width="small",  default="Rs.0 / pcs"),
            "Barcode Number": st.column_config.TextColumn("Barcode Number", width="medium", default=""),
        },
        hide_index=True, use_container_width=True, height=380,
    )

    needs_rerun = False
    if master != st.session_state["bc_master_sel"]:
        st.session_state["bc_master_sel"] = master
        st.session_state["bc_inventory"]  = edited.copy()
        st.session_state["bc_inventory"]["Select"] = master
        st.session_state["bc_editor_key"] += 1
        needs_rerun = True

    ac, _ = st.columns([1, 5])
    with ac:
        if st.button("➕ Add Row", key="bc_add_row"):
            st.session_state["bc_inventory"] = pd.concat(
                [edited.copy(), pd.DataFrame([{
                    "Select": False, "Preview": False,
                    "Item Name": "New Item", "Price": "Rs.0 / pcs",
                    "Barcode Number": "", "Print Count": 1,
                }])], ignore_index=True)
            st.session_state["bc_editor_key"] += 1
            needs_rerun = True

    # Previews
    previews = edited[edited["Preview"] == True]
    if not previews.empty:
        st.subheader("👁️ Previews")
        cols = st.columns(3)
        for i, (idx, row) in enumerate(previews.iterrows()):
            with cols[i % 3]:
                h1, h2 = st.columns([5, 1])
                with h1:
                    st.caption(f"**{row['Item Name']}**")
                with h2:
                    if st.button("❌", key=f"bc_close_{idx}"):
                        st.session_state["bc_inventory"] = edited.copy()
                        st.session_state["bc_inventory"].loc[idx, "Preview"] = False
                        st.session_state["bc_editor_key"] += 1
                        needs_rerun = True
                bkey = str(row["Barcode Number"]).strip()
                saved = st.session_state["bc_overrides"].get(bkey)
                _bc_show_pdf_preview(_bc_generate_pdf(pd.DataFrame([row]), single_preview=True, live_override=saved))
                st.caption("🎨 Custom" if saved else "⚙️ Auto")
                if st.button("🎛️ Customize", key=f"bc_cust_{idx}", use_container_width=True):
                    st.session_state["bc_dialog_rev"] += 1
                    _bc_customize_dialog(row)

    if needs_rerun:
        st.rerun()

    st.divider()
    if st.button("🖨️ Generate PDF Labels", type="primary", key="bc_gen_pdf"):
        to_print = edited[(edited["Select"] == True) & (edited["Print Count"] > 0)]
        if to_print.empty:
            st.warning("Select at least one item with Qty > 0.")
        else:
            with st.spinner("Generating PDF..."):
                buf = _bc_generate_pdf(to_print, overrides=st.session_state["bc_overrides"])
                total = to_print["Print Count"].sum()
            st.success(f"✅ {total} stickers generated!")
            st.download_button("⬇️ Download Barcodes PDF", data=buf,
                               file_name="maharani_barcodes.pdf", mime="application/pdf",
                               key="bc_dl_btn")


@st.dialog("⚙️ Barcode Label Layout Presets", width="large")
def _bc_presets_dialog():
    p   = st.session_state["bc_presets"]
    rev = st.session_state["bc_dialog_rev"]
    st.caption("Items without a saved per-barcode override use one of these presets, chosen by name length.")
    thr = st.slider("Name-length cutoff", 10, 60, p["threshold"], step=1, key=f"bc_thr_{rev}",
                    help="Names ≤ this length → Short preset; longer → Long preset.")
    sc, lc = st.columns(2)
    with sc:
        st.markdown("###### Short Names")
        sv = {f: st.slider(f, *((6.0,14.0) if "size" in f and "bar" not in f else
                                (5.0,12.0) if f=="price_size" else
                                (4.0,10.0) if f=="barcode_text_size" else
                                (0.15,0.40) if f=="bar_width" else
                                (5.0,12.0) if f=="bar_height" else
                                _BC_Y_RANGE),
                           value=p["short"][f],
                           step=(0.5 if "size" in f or "height" in f else 0.01 if "width" in f else 0.25),
                           key=f"bc_sp_{f}_{rev}") for f in p["short"]}
    with lc:
        st.markdown("###### Long Names")
        lv = {f: st.slider(f, *((6.0,14.0) if "size" in f and "bar" not in f else
                                (5.0,12.0) if f=="price_size" else
                                (4.0,10.0) if f=="barcode_text_size" else
                                (0.15,0.40) if f=="bar_width" else
                                (5.0,12.0) if f=="bar_height" else
                                _BC_Y_RANGE),
                           value=p["long"][f],
                           step=(0.5 if "size" in f or "height" in f else 0.01 if "width" in f else 0.25),
                           key=f"bc_lp_{f}_{rev}") for f in p["long"]}

    st.divider()
    s1, s2, s3 = st.columns(3)
    with s1:
        if st.button("💾 Save Presets", type="primary", use_container_width=True, key=f"bc_save_p_{rev}"):
            st.session_state["bc_presets"] = {"threshold": thr, "short": sv, "long": lv}
            _bc_save_presets(st.session_state["bc_presets"])
            st.toast("Presets saved"); st.rerun()
    with s2:
        def _bc_reset_p(r=rev):
            st.session_state["bc_presets"] = {"threshold": _BC_DEFAULT_THRESHOLD,
                                               "short": dict(_BC_SHORT_PRESET),
                                               "long":  dict(_BC_LONG_PRESET)}
            _bc_save_presets(st.session_state["bc_presets"])
        st.button("↺ Factory Defaults", use_container_width=True, on_click=_bc_reset_p, key=f"bc_rst_p_{rev}")
    with s3:
        if st.button("✖️ Close", use_container_width=True, key=f"bc_cls_p_{rev}"):
            st.rerun()


# ════════════════════════════════════════════════════════════════════════════════
# TAB 1 — STANDARD ITEMS
# ════════════════════════════════════════════════════════════════════════════════
def tab_standard_items(auth_ok: bool, dry_run: bool):
    st.subheader("Generate & Push Base Item Variations")

    # ── Build form ──
    with st.form("item_form", clear_on_submit=True):
        c1, c2, c3 = st.columns(3)
        with c1:
            base_name  = st.text_input("Base Item Name", placeholder="e.g., Stone Lotus")
            attributes = st.text_area("Variants (comma separated)", placeholder="Red, Blue, Green")
        with c2:
            s_price = st.number_input("Selling Price (₹)", min_value=0.0, step=1.0)
            p_price = st.number_input("Purchase Price (₹)", min_value=0.0, step=1.0)
        with c3:
            unit          = st.text_input("Unit", value="pcs")
            vendor        = st.text_input("Preferred Vendor")
            hsn           = st.text_input("HSN/SAC", placeholder="e.g. 7117 (optional for GST)")
            reorder_point = st.number_input("Reorder Point", min_value=0, value=48, step=1,
                                            help="Zoho will alert when stock falls below this.")

        if st.form_submit_button("➕ Add Variations to List"):
            if base_name and attributes:
                count = 0
                for attr in [a.strip() for a in attributes.split(",") if a.strip()]:
                    st.session_state["items_list"].append({
                        "Item Name":          f"{base_name} {attr}",
                        "SKU":                _gen_sku(),
                        "Unit":               unit,
                        "Selling Price (₹)":  s_price,
                        "Purchase Price (₹)": p_price,
                        "Product Type":       "goods",
                        "Item Type":          "inventory",
                        "HSN/SAC":            hsn,
                        "Sales Description":  "",
                        "Sales Account":      "Sales",
                        "Purchase Account":   "Cost of Goods Sold",
                        "Inventory Account":  "Inventory Asset",
                        "Preferred Vendor":   vendor,
                        "Reorder Level":      reorder_point,
                    })
                    count += 1
                st.success(f"✅ {count} variation(s) added.")
            else:
                st.warning("Enter a base name and at least one variant.")

    if not st.session_state["items_list"]:
        return

    st.divider()
    st.write("### Review & Edit Before Push")
    edited_df = st.data_editor(
        pd.DataFrame(st.session_state["items_list"]),
        key="tbl_items",
        num_rows="dynamic",
        use_container_width=True,
    )

    ba, bb, bc = st.columns([2, 2, 2])
    with ba:
        check_btn = st.button(
            "🔍 Check Zoho (existence)",
            disabled=not auth_ok,
            help="Checks each item name against Zoho before you push.",
        )
    with bb:
        st.download_button(
            "📥 Download CSV",
            edited_df.to_csv(index=False).encode("utf-8"),
            "items.csv", "text/csv",
        )
    with bc:
        if st.button("🗑️ Clear Items List"):
            st.session_state["items_list"]  = []
            st.session_state["check_items"] = None
            st.rerun()

    if check_btn:
        _check_items(edited_df)

    # ── Check results & push buttons ──
    if st.session_state["check_items"] is not None:
        checks  = st.session_state["check_items"]
        new_c   = sum(1 for r in checks if "New"    in r["status"])
        exist_c = sum(1 for r in checks if "Exists" in r["status"])
        st.info(f"🟢 **{new_c} new** &nbsp;|&nbsp; 🟡 **{exist_c} already in Zoho**")
        st.dataframe(pd.DataFrame(checks), use_container_width=True, hide_index=True)

        pa, pb = st.columns(2)
        with pa:
            if st.button(
                f"🚀 Push {new_c} New Item(s) to Zoho",
                disabled=not auth_ok or new_c == 0,
                type="primary",
            ):
                _push_items(edited_df, overwrite=False, dry_run=dry_run)

        with pb:
            if exist_c > 0 and st.button(
                f"♻️ Overwrite {exist_c} Existing Item(s)",
                disabled=not auth_ok,
                help="Calls PUT /items — updates in place, nothing is deleted.",
            ):
                _push_items(edited_df, overwrite=True, dry_run=dry_run)


def _check_items(df: pd.DataFrame):
    try:
        token   = get_token()
        rows    = df.to_dict("records")
        results = []
        prog    = st.progress(0, "Checking existence in Zoho…")
        for i, row in enumerate(rows):
            name = str(row.get("Item Name", "")).strip()
            if not name:
                continue
            item_id, _ = find_item(token, name)
            if item_id:
                st.session_state["item_id_map"][name] = item_id
            results.append({
                "name":    name,
                "status":  "🟢 New" if not item_id else "🟡 Exists",
                "item_id": item_id or "",
            })
            prog.progress((i + 1) / max(len(rows), 1), f"Checked: {name}")
        prog.empty()
        st.session_state["check_items"] = results
    except Exception as exc:
        st.error(str(exc))


def _push_items(df: pd.DataFrame, overwrite: bool, dry_run: bool):
    try:
        token = get_token()
        rows  = df.to_dict("records")
        prog  = st.progress(0, "Pushing items…")
        for i, row in enumerate(rows):
            name = str(row.get("Item Name", "")).strip()
            if not name:
                continue
            payload = build_item_payload(row)
            item_id, _ = find_item(token, name)

            if item_id:
                if overwrite:
                    if dry_run:
                        _log(name, "UPDATE", "🔬 Dry Run", item_id, "Would PUT /items")
                    else:
                        resp = update_item(token, item_id, payload)
                        if resp.get("code") == 0:
                            _log(name, "UPDATE", "✅ Updated", item_id)
                        else:
                            _log(name, "UPDATE", "❌ Error", item_id, str(resp.get("message", resp)))
                else:
                    _log(name, "SKIP", "⏭️ Skipped", item_id, "Already exists — use Overwrite to update")
            else:
                if dry_run:
                    _log(name, "CREATE", "🔬 Dry Run", "", "Would POST /items")
                else:
                    resp = create_item(token, payload)
                    if resp.get("code") == 0:
                        new_id = resp.get("item", {}).get("item_id", "")
                        st.session_state["item_id_map"][name] = new_id
                        _log(name, "CREATE", "✅ Created", new_id)
                    else:
                        _log(name, "CREATE", "❌ Error", "", str(resp.get("message", resp)))

            prog.progress((i + 1) / max(len(rows), 1))

        prog.empty()
        st.session_state["check_items"] = None
        st.success("Push complete — check the Push Log tab for details.")
        st.rerun()
    except Exception as exc:
        st.error(str(exc))


# ════════════════════════════════════════════════════════════════════════════════
# TAB 2 — COMPOSITE PACKS
# ════════════════════════════════════════════════════════════════════════════════
def tab_composite_items(auth_ok: bool, dry_run: bool):
    st.subheader("Create Composite Packs")

    # ── Direct composite CSV loader ───────────────────────────────────────────
    # NOTE: parsed on every upload event (not on button click) to avoid
    # Streamlit's file-uploader-loses-reference-on-rerun bug.
    with st.expander("📂 Load composites from existing CSV",
                     expanded=not st.session_state["composites_list"]):
        comp_csv_upload = st.file_uploader(
            "Upload composites.csv — columns needed: "
            "'Composite Item Name', 'Mapped Item Name', 'Mapped Quantity'",
            type="csv", key="direct_comp_upf",
        )

        if comp_csv_upload is not None:
            # Parse immediately while the file reference is valid
            try:
                df_in = pd.read_csv(comp_csv_upload)

                # Rename "Name" → "Composite Item Name" if needed
                if "Composite Item Name" not in df_in.columns and "Name" in df_in.columns:
                    df_in = df_in.rename(columns={"Name": "Composite Item Name"})

                # Normalise price columns (handles both "26.0" and "INR 26.00")
                for src_col, dst_col in [
                    ("Selling Price",   "Selling Price (₹)"),
                    ("Purchase Price",  "Purchase Price (₹)"),
                ]:
                    if src_col in df_in.columns and dst_col not in df_in.columns:
                        df_in[dst_col] = (
                            df_in[src_col].astype(str)
                            .apply(lambda x: re.sub(r"[^\d.]", "", x))
                            .apply(lambda x: float(x) if x else 0.0)
                        )
                    elif dst_col in df_in.columns:
                        df_in[dst_col] = (
                            df_in[dst_col].astype(str)
                            .apply(lambda x: re.sub(r"[^\d.]", "", x))
                            .apply(lambda x: float(x) if x else 0.0)
                        )

                # Fill missing columns with sensible defaults
                for col in COMP_COLS:
                    if col not in df_in.columns:
                        df_in[col] = 1 if col == "Mapped Quantity" else ""

                parsed_rows = df_in[COMP_COLS].to_dict("records")

                # Show preview so user can verify before committing
                st.write(f"**{len(parsed_rows)} row(s) detected — preview:**")
                st.dataframe(df_in[COMP_COLS].head(5), use_container_width=True, hide_index=True)

                if st.button("⬆️ Confirm & load into table", type="primary"):
                    st.session_state["composites_list"] = parsed_rows
                    st.success(f"✅ {len(parsed_rows)} row(s) loaded.")
                    st.rerun()

            except Exception as exc:
                st.error(f"Could not read CSV: {exc}")

    st.divider()

    # ── Existing Zoho Item Search (feeds the generator below as a source) ────────
    with st.expander("🔗 Existing Zoho Item Search", expanded=False):
        if not auth_ok:
            st.warning("⚠️ Connect Zoho credentials first (sidebar) to use this feature.")
        else:
            st.caption(
                "Search Zoho for existing base items and tick the ones you want. "
                "Then select **Existing Zoho Item** below to feed them into the composite generator."
            )

            # ── Search bar ────────────────────────────────────────────────────
            sc1, sc2 = st.columns([5, 1])
            with sc1:
                czf_query_input = st.text_input(
                    "Search item name (min 2 chars)",
                    key="czf_query_input",
                    placeholder="e.g. moti pearl, kundan, crystal...",
                )
            with sc2:
                st.write("")
                st.write("")
                czf_search_btn = st.button(
                    "🔍 Search",
                    key="czf_search_btn",
                    disabled=len(czf_query_input.strip()) < 2,
                    use_container_width=True,
                )

            if czf_search_btn and len(czf_query_input.strip()) >= 2:
                try:
                    _call_guard()
                    _tok = get_token()
                    _resp = requests.get(
                        f"{API_BASE}/items",
                        params={
                            "organization_id": ORG_ID,
                            "search_text":     czf_query_input.strip(),
                            "per_page":        25,
                            "filter_by":       "Status.Active",
                        },
                        headers=_hdrs(_tok), timeout=15,
                    )
                    _tick()
                    _data = _resp.json()
                    _raise_if_auth_error(_data, "GET /items (search)")
                    st.session_state["czf_results"] = _data.get("items", [])
                    st.session_state["czf_query"]   = czf_query_input.strip()
                    # Keep existing selections that are still in the new results
                    prev_ids = {r["item_id"] for r in st.session_state["czf_selected"]}
                    st.session_state["czf_selected"] = [
                        r for r in st.session_state["czf_results"]
                        if r["item_id"] in prev_ids
                    ]
                    if not st.session_state["czf_results"]:
                        st.info(f"No active items found for '{czf_query_input}'. Try a different search.")
                except Exception as _e:
                    st.error(f"Search failed: {_e}")

            # ── Checkbox results ──────────────────────────────────────────────
            czf_results = st.session_state["czf_results"]
            if czf_results:
                _q = st.session_state["czf_query"]
                st.caption(
                    f"🔎 **{len(czf_results)} result(s)** for `{_q}`"
                    + ("  ·  showing first 25" if len(czf_results) == 25 else "")
                )
                _selected_ids = {r["item_id"] for r in st.session_state["czf_selected"]}
                _new_selected = []
                for _r in czf_results:
                    _label = (
                        f"**{_r['name']}**  ·  "
                        f"SKU: `{_r.get('sku') or '—'}`  ·  "
                        f"₹{_r.get('rate', 0)}"
                    )
                    _checked = st.checkbox(
                        _label,
                        value=_r["item_id"] in _selected_ids,
                        key=f"czf_cb_{_r['item_id']}",
                    )
                    if _checked:
                        _new_selected.append(_r)
                st.session_state["czf_selected"] = _new_selected

                if _new_selected:
                    st.success(
                        f"✅ **{len(_new_selected)} item(s) selected** — "
                        "choose *Existing Zoho Item* below to generate composite rows."
                    )

    st.divider()
    # ── Source for base items (used by the generator form below) ─────────────
    source = st.radio(
        "Base items source:",
        ["Current Session (Tab 1)", "Upload Items CSV", "Existing Zoho Item"],
        horizontal=True, key="comp_src",
    )
    source_df = pd.DataFrame()
    if source == "Current Session (Tab 1)":
        source_df = pd.DataFrame(st.session_state["items_list"])
    elif source == "Upload Items CSV":
        upf = st.file_uploader("Upload Items CSV (must have 'Item Name' column)", type="csv", key="comp_upf")
        if upf:
            source_df = pd.read_csv(upf)
            # Normalize price column from Zoho export ("INR 35.00" → 35.0)
            for price_col in ("Selling Price", "Selling Price (₹)"):
                if price_col in source_df.columns:
                    source_df["Selling Price (₹)"] = (
                        source_df[price_col].astype(str)
                        .apply(lambda x: re.sub(r"[^\d.]", "", x))
                        .apply(lambda x: float(x) if x else 0.0)
                    )
    else:  # Existing Zoho Item
        czf_sel_list = st.session_state["czf_selected"]
        if not czf_sel_list:
            st.info(
                "No Zoho items selected yet. "
                "Open the **🔗 Existing Zoho Item Search** expander above, "
                "search, and tick the base items you want to pack."
            )
        else:
            # Build source_df so the generator form below works unchanged
            source_df = pd.DataFrame([
                {
                    "Item Name":        r["name"],
                    "SKU":              r.get("sku", "") or "",
                    "Selling Price (₹)": float(r.get("rate", 0)),
                }
                for r in czf_sel_list
            ])
            # Pre-populate item_id_map → _resolve_item_id finds IDs instantly (0 extra API calls)
            for r in czf_sel_list:
                st.session_state["item_id_map"][r["name"]] = r["item_id"]
            st.caption(
                f"Using **{len(czf_sel_list)} Zoho item(s)**: "
                + ", ".join(f"`{r['name']}`" for r in czf_sel_list)
            )

    # ── Generator form (only shown when a base-items source is available) ────────
    # If composites were already loaded via the CSV expander above, we skip
    # straight to the table.  If nothing is loaded at all, we show the hint.
    has_source = not source_df.empty and "Item Name" in source_df.columns

    if has_source:
        selected_bases = st.multiselect(
            "Select base items to pack:",
            source_df["Item Name"].unique().tolist(),
        )

        with st.form("comp_builder", clear_on_submit=True):
            cc1, cc2, cc3 = st.columns(3)
            with cc1:
                pack_types = st.text_input(
                    "Pack Types (suffix, comma separated)",
                    value="pack 6, pack 12",
                    help="The number inside each suffix becomes Mapped Quantity.",
                )
            with cc2:
                comp_s = st.number_input("Selling Price per Pack (₹)", min_value=0.0, step=1.0)
                comp_p = st.number_input("Purchase Price per Pack (₹)", min_value=0.0, step=1.0)
            with cc3:
                comp_unit = st.text_input("Unit", value="pack size")

            if st.form_submit_button("➕ Generate Composite Rows"):
                if not selected_bases or not pack_types:
                    st.warning("Select at least one base item and enter pack types.")
                else:
                    # Build lookup of existing names so we overwrite instead of duplicate
                    existing = {r["Composite Item Name"]: i
                                for i, r in enumerate(st.session_state["composites_list"])}
                    added = updated = 0
                    for b_name in selected_bases:
                        b_row = source_df[source_df["Item Name"] == b_name].iloc[0]
                        b_sku = str(b_row.get("SKU", "")).strip()
                        for pt in [p.strip() for p in pack_types.split(",") if p.strip()]:
                            qty_m = re.search(r"\d+", pt)
                            qty   = int(qty_m.group()) if qty_m else 1
                            comp_name = f"{b_name} {pt}"
                            new_row = {
                                "Composite Item Name": comp_name,
                                "SKU":                 _gen_sku(),
                                "Unit":                comp_unit,
                                "Selling Price (₹)":   comp_s,
                                "Purchase Price (₹)":  comp_p,
                                "Mapped Item Name":    b_name,
                                "Mapped Item SKU":     b_sku,
                                "Mapped Quantity":     qty,
                                "Combo Type":          "Kit",
                            }
                            if comp_name in existing:
                                # Overwrite existing row (keep original SKU)
                                idx = existing[comp_name]
                                new_row["SKU"] = st.session_state["composites_list"][idx]["SKU"]
                                st.session_state["composites_list"][idx] = new_row
                                updated += 1
                            else:
                                st.session_state["composites_list"].append(new_row)
                                existing[comp_name] = len(st.session_state["composites_list"]) - 1
                                added += 1
                    msg = []
                    if added:   msg.append(f"✅ {added} added")
                    if updated: msg.append(f"♻️ {updated} updated (duplicate names overwritten)")
                    st.success(" · ".join(msg))

    elif not st.session_state["composites_list"]:
        # No generator source AND nothing loaded from CSV — nothing to show
        st.info("No items available. Add items in Tab 1, upload a CSV above, or load composites via the CSV expander.")
        return

    st.divider()
    st.write("### Review & Edit Before Push")
    edited_comp = st.data_editor(
        pd.DataFrame(st.session_state["composites_list"]),
        key="tbl_comp",
        num_rows="dynamic",
        use_container_width=True,
    )

    ca, cb, cc = st.columns([2, 2, 2])
    with ca:
        check_comp_btn = st.button("🔍 Check Zoho (composites)", disabled=not auth_ok)
    with cb:
        st.download_button(
            "📥 Download CSV",
            edited_comp.to_csv(index=False).encode("utf-8"),
            "composites.csv", "text/csv",
        )
    with cc:
        if st.button("🗑️ Clear Composites List"):
            st.session_state["composites_list"] = []
            st.session_state["check_comps"]     = None
            st.rerun()

    if check_comp_btn:
        _check_composites(edited_comp)

    if st.session_state["check_comps"] is not None:
        checks  = st.session_state["check_comps"]
        new_c   = sum(1 for r in checks if "New"    in r["status"])
        exist_c = sum(1 for r in checks if "Exists" in r["status"])
        st.info(f"🟢 **{new_c} new** &nbsp;|&nbsp; 🟡 **{exist_c} already in Zoho**")
        st.dataframe(pd.DataFrame(checks), use_container_width=True, hide_index=True)

        pa, pb = st.columns(2)
        with pa:
            if st.button(
                f"🚀 Push {new_c} New Composite(s) to Zoho",
                disabled=not auth_ok or new_c == 0,
                type="primary",
            ):
                _push_composites(edited_comp, overwrite=False, dry_run=dry_run)
        with pb:
            if exist_c > 0 and st.button(
                f"♻️ Overwrite {exist_c} Existing Composite(s)",
                disabled=not auth_ok,
                help="Calls PUT /compositeitems — no deletion.",
            ):
                _push_composites(edited_comp, overwrite=True, dry_run=dry_run)


def _check_composites(df: pd.DataFrame):
    try:
        token   = get_token()
        rows    = df.to_dict("records")
        results = []
        prog    = st.progress(0, "Checking composites in Zoho…")
        for i, row in enumerate(rows):
            name = str(row.get("Composite Item Name", "")).strip()
            if not name:
                continue
            comp_id, _ = find_composite(token, name)
            results.append({
                "name":    name,
                "status":  "🟢 New" if not comp_id else "🟡 Exists",
                "comp_id": comp_id or "",
            })
            prog.progress((i + 1) / max(len(rows), 1), f"Checked: {name}")
        prog.empty()
        st.session_state["check_comps"] = results
    except Exception as exc:
        st.error(str(exc))


def _push_composites(df: pd.DataFrame, overwrite: bool, dry_run: bool):
    try:
        token = get_token()
        rows  = df.to_dict("records")
        prog  = st.progress(0, "Pushing composites…")
        for i, row in enumerate(rows):
            name = str(row.get("Composite Item Name", "")).strip()
            if not name:
                continue

            # Resolve base item's Zoho item_id
            base_item_id = _resolve_item_id(
                token,
                str(row.get("Mapped Item Name", "")),
                str(row.get("Mapped Item SKU", "")),
            )
            if not base_item_id:
                _log(name, "CREATE", "❌ Error", "",
                     f"Base item not found in Zoho: '{row.get('Mapped Item Name')}' "
                     f"(SKU: {row.get('Mapped Item SKU')}). Push base items first.")
                prog.progress((i + 1) / max(len(rows), 1))
                continue

            payload = build_composite_payload(row, base_item_id)
            comp_id, _ = find_composite(token, name)

            if comp_id:
                if overwrite:
                    if dry_run:
                        _log(name, "UPDATE", "🔬 Dry Run", comp_id, "Would PUT /compositeitems")
                    else:
                        resp = update_composite(token, comp_id, payload)
                        if resp.get("code") == 0:
                            _log(name, "UPDATE", "✅ Updated", comp_id)
                        else:
                            _log(name, "UPDATE", "❌ Error", comp_id, str(resp.get("message", resp)))
                else:
                    _log(name, "SKIP", "⏭️ Skipped", comp_id, "Already exists")
            else:
                if dry_run:
                    _log(name, "CREATE", "🔬 Dry Run", "", "Would POST /compositeitems")
                else:
                    resp = create_composite(token, payload)
                    if resp.get("code") == 0:
                        new_id = resp.get("composite_item", {}).get("composite_item_id", "")
                        _log(name, "CREATE", "✅ Created", new_id)
                    else:
                        _log(name, "CREATE", "❌ Error", "", str(resp.get("message", resp)))

            prog.progress((i + 1) / max(len(rows), 1))

        prog.empty()
        st.session_state["check_comps"] = None
        st.success("Push complete — check the Push Log tab.")
        st.rerun()
    except Exception as exc:
        st.error(str(exc))


# ════════════════════════════════════════════════════════════════════════════════
# TAB 3 — PUSH LOG
# ════════════════════════════════════════════════════════════════════════════════
def tab_push_log():
    st.subheader("Push Log")
    if not st.session_state["push_log"]:
        st.info("Nothing pushed yet. Log appears here after any Zoho operation.")
        return

    col1, col2 = st.columns([1, 5])
    with col1:
        if st.button("🗑️ Clear Log"):
            st.session_state["push_log"] = []
            st.rerun()
    with col2:
        log_df = pd.DataFrame(st.session_state["push_log"])
        st.download_button(
            "📥 Download Log CSV",
            log_df.to_csv(index=False).encode("utf-8"),
            f"push_log_{datetime.now().strftime('%Y%m%d_%H%M')}.csv",
            "text/csv",
        )

    _show_log()

    # Summary counts
    log_df = pd.DataFrame(st.session_state["push_log"])
    st.divider()
    sc = st.columns(5)
    for col, label in zip(sc, ["✅ Created", "✅ Updated", "⏭️ Skipped", "❌ Error", "🔬 Dry Run"]):
        col.metric(label, int((log_df["Status"] == label).sum()))



# ════════════════════════════════════════════════════════════════════════════════
# TAB 4 — LABELS & SHIPPING
# ════════════════════════════════════════════════════════════════════════════════

# ── Label helpers (ported from label_app.py) ──────────────────────────────────
def _lbl_s(v) -> str:
    return str(v).strip() if v is not None else ""


def _lbl_wrap(text: str, max_chars: int) -> list:
    if not text:
        return []
    words, lines, cur = str(text).split(), [], ""
    for w in words:
        cand = (cur + " " + w) if cur else w
        if len(cand) <= max_chars:
            cur = cand
        else:
            if cur:
                lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    return lines


def _lbl_order_to_row(o: dict) -> dict:
    addr  = o.get("shipping_address") or {}
    st1   = _lbl_s(addr.get("address") or addr.get("street1"))
    st2   = _lbl_s(addr.get("street2"))
    full  = " ".join(filter(None, [st1, st2])).strip()
    cs    = ", ".join(filter(None, [_lbl_s(addr.get("city")), _lbl_s(addr.get("state"))]))
    phone = _lbl_s(addr.get("phone") or o.get("phone") or o.get("contact_phone"))
    name  = _lbl_s(addr.get("attention") or o.get("customer_name"))
    return {
        "✓":         True,
        "Date":       _lbl_s(o.get("_fetch_date") or o.get("date")),
        "Order #":    _lbl_s(o.get("salesorder_number")),
        "Name":       name,
        "Address":    full,
        "City/State": cs,
        "Pincode":    _lbl_s(addr.get("zip")),
        "Phone":      phone,
        "Amount":     f"₹{float(o.get('total') or 0):,.0f}",
    }


def _lbl_draw_label(c, x: float, y: float, row: dict, fs: int = 8):
    PAD     = 4 * mm
    LS_TO   = (fs + 1.5) * 0.42 * mm
    LS_FROM = max(3.5 * mm, fs * 0.42 * mm)
    MC      = max(20, int(40 * 8 / max(fs, 6)))

    c.setStrokeColor(colors.black)
    c.setLineWidth(1)
    c.rect(x, y, _LBL_W, _LBL_H)

    div_y = y + _LBL_H * 0.40
    c.setLineWidth(0.5)
    c.line(x, div_y, x + _LBL_W, div_y)

    cy = y + _LBL_H - 8 * mm
    c.setFont("Helvetica-Bold", fs + 2)
    c.drawString(x + PAD, cy, "To,")
    cy -= LS_TO + 1 * mm

    c.setFont("Helvetica-Bold", fs + 1)
    c.drawString(x + PAD, cy, _lbl_s(row.get("Name")))
    cy -= LS_TO

    c.setFont("Helvetica-Bold", fs)
    for field in ["Address", "City/State", "Pincode", "Phone"]:
        val = _lbl_s(row.get(field))
        if not val:
            continue
        for line in _lbl_wrap(val, MC):
            if cy > div_y + 3 * mm:
                c.drawString(x + PAD, cy, line)
                cy -= LS_TO
            else:
                break

    fs_from = max(6, fs - 1)
    c.setFont("Helvetica-Bold", fs_from)
    fy = div_y - 5 * mm
    for line in LBL_ALL_FROM:
        c.drawString(x + 18 * mm, fy, line)
        fy -= LS_FROM


def _lbl_generate_pdf(rows: list, fs: int = 8) -> bytes:
    buf = BytesIO()
    c = rl_canvas.Canvas(buf, pagesize=A4)
    for i, row in enumerate(rows):
        _lbl_draw_label(c, *_LBL_POSITIONS[i % 4], row, fs)
        if i % 4 == 3 and i < len(rows) - 1:
            c.showPage()
    c.save()
    buf.seek(0)
    return buf.read()


def _lbl_preview_html(row: dict, fs: int = 8) -> str:
    to_lines = "<br>".join(filter(None, [
        f"<strong>{_lbl_s(row.get('Name'))}</strong>",
        _lbl_s(row.get("Address")),
        _lbl_s(row.get("City/State")),
        _lbl_s(row.get("Pincode")),
        _lbl_s(row.get("Phone")),
    ]))
    from_block = "<br>".join(LBL_ALL_FROM)
    px = fs + 2
    px_from = max(8, fs)
    return f"""
<div style="border:2px solid #333;width:390px;height:270px;
  font-family:'Courier New',monospace;background:white;
  display:flex;flex-direction:column;border-radius:4px;
  overflow:hidden;box-shadow:0 2px 10px rgba(0,0,0,.18);">
  <div style="flex:0 0 58%;padding:12px 14px 6px 14px;
    border-bottom:1px solid #666;font-size:{px}px;line-height:1.6;overflow:hidden;">
    <span style="color:#555">To,</span><br>{to_lines}
  </div>
  <div style="flex:0 0 42%;padding:8px 14px 6px 50px;
    font-size:{px_from}px;line-height:1.5;color:#444;overflow:hidden;">
    {from_block}
  </div>
</div>
<p style="font-size:11px;color:#999;margin-top:5px;">
  Order: {row.get('Order #', '—')} &nbsp;|&nbsp; Font: {fs}pt
</p>"""


def _mark_orders_shipped(
    order_ids: list,
    order_nums: list,
    carrier: str,
    tracking_number: str,
    shipping_charge: float,
    dispatch_date: str,
    pkg_notes: str,
    dry_run: bool,
):
    """Create package + shipment for each selected order via Zoho API."""
    prog  = st.progress(0, "Marking orders as shipped…")
    total = max(len(order_ids), 1)
    try:
        token = get_token()
        for idx, (oid, onum) in enumerate(zip(order_ids, order_nums)):
            try:
                if dry_run:
                    _log(onum, "SHIP", "\U0001f52c Dry Run", "",
                         f"Would ship via {carrier or 'manual'} | "
                         f"Track: {tracking_number or '—'} | "
                         f"Date: {dispatch_date} | Charge: ₹{shipping_charge:.0f}")
                    prog.progress((idx + 1) / total)
                    continue

                _log(onum, "SHIP", "🔄 Attempting", oid, f"salesorder_id={oid}")
                detail = get_salesorder_detail(token, oid)
                order_status = detail.get("status", "")
                is_fulfilled  = detail.get("is_manually_fulfilled", False)
                # Log SO detail keys to reveal package-related fields
                pkg_keys = [k for k in detail.keys() if "pack" in k.lower() or "ship" in k.lower()]
                _log(onum, "SHIP", "🔑 Detail Keys", oid,
                     f"pkg/ship keys: {pkg_keys} | "
                     f"packages_in_detail: {detail.get('packages', 'NOT_FOUND')}")
                _log(onum, "SHIP", "ℹ️ Order State", oid,
                     f"status={order_status} | "
                     f"shipment_status={detail.get('shipment_status')} | "
                     f"line_items={len(detail.get('line_items',[]))} | "
                     f"is_manually_fulfilled={is_fulfilled}")
                # Skip orders already fulfilled or shipped
                if order_status in ("fulfilled", "shipped") or is_fulfilled:
                    _log(onum, "SHIP", "⏭️ Skipped", oid,
                         f"Already {order_status} — no package needed.")
                    prog.progress((idx + 1) / total)
                    continue
                # Use quantity (ordered) — quantity_backordered can equal
                # full order amount pre-fulfillment, causing code 36012
                line_items = [
                    {
                        "so_line_item_id": li.get("line_item_id"),
                        "quantity":        float(li.get("quantity") or 0),
                    }
                    for li in detail.get("line_items", [])
                    if float(li.get("quantity") or 0) > 0
                ]
                _log(onum, "SHIP", "📦 Line Items", oid,
                     f"{len(line_items)} items | "
                     + ", ".join(f"{li['so_line_item_id']}\u00d7{li['quantity']}"
                                 for li in line_items[:3])
                     + ("\u2026" if len(line_items) > 3 else ""))
                if not line_items:
                    _log(onum, "SHIP", "⏭️ Skipped", "", "No shippable quantities.")
                    prog.progress((idx + 1) / total)
                    continue

                # Zoho Commerce auto-creates packages — pull from SO detail directly.
                # This is faster and correct; avoid GET /packages which doesn't filter reliably.
                detail_pkgs = detail.get("packages", [])
                if detail_pkgs:
                    pkg_id = detail_pkgs[0].get("package_id", "")
                    _log(onum, "SHIP", "ℹ️ Reusing Package", pkg_id,
                         f"Found {len(detail_pkgs)} package(s) in SO detail — "
                         f"shipment_status={detail_pkgs[0].get('shipment_status')}")
                else:
                    pkg_resp = create_package(
                        token, oid, line_items,
                        pkg_date=dispatch_date,
                        notes=pkg_notes,
                    )
                    if pkg_resp.get("code") != 0:
                        _log(onum, "SHIP", "❌ Error", "", f"Package: {pkg_resp.get('message')} | {pkg_resp}")
                        prog.progress((idx + 1) / total)
                        continue
                    pkg_id = (pkg_resp.get("package") or {}).get("package_id", "")
                    _log(onum, "SHIP", "✅ Package Created", pkg_id, "New package created.")

                if not pkg_id:
                    _log(onum, "SHIP", "❌ Error", "", "Could not determine package_id — no packages in SO detail.")
                    prog.progress((idx + 1) / total)
                    continue
                shp_resp = create_shipment(
                    token,
                    salesorder_id=oid,
                    package_id=pkg_id,
                    carrier=carrier,
                    tracking_number=tracking_number,
                    shipping_charge=shipping_charge,
                    ship_date=dispatch_date,
                    notes=pkg_notes,
                )
                if shp_resp.get("code") == 0:
                    _log(onum, "SHIP", "✅ Shipped", pkg_id,
                         f"{carrier or 'manual'} | "
                         f"Track: {tracking_number or '—'} | "
                         f"₹{shipping_charge:.0f} | {dispatch_date}")
                else:
                    _log(onum, "SHIP", "❌ Error", pkg_id,
                         f"Shipment: {shp_resp.get('message')} | {shp_resp}")
            except Exception as row_exc:
                _log(onum, "SHIP", "❌ Error", "", str(row_exc))
            prog.progress((idx + 1) / total)

        prog.empty()
        st.success("Done — check the Push Log tab.")
        st.rerun()
    except Exception as exc:
        st.error(str(exc))


def tab_labels_shipping(auth_ok: bool, dry_run: bool):
    st.subheader("\U0001f4ee Label Generator & Shipping")
    st.caption("Zoho Inventory → edit table → preview → 4-up A4 PDF → mark as shipped")

    # ── Controls ──────────────────────────────────────────────────────────────
    with st.expander("\U0001f50d Fetch Orders", expanded=st.session_state["lbl_order_df"] is None):
        fc1, fc2, fc3 = st.columns([2, 1, 1])
        with fc1:
            raw_dates = st.date_input(
                "Date Range",
                value=st.session_state["lbl_fetch_dates"],
                help="Select same date twice for a single day.",
                key="lbl_date_range",
            )
            if isinstance(raw_dates, date):
                sel_dates = (raw_dates, raw_dates)
            elif len(raw_dates) == 1:
                sel_dates = (raw_dates[0], raw_dates[0])
            else:
                sel_dates = (raw_dates[0], raw_dates[1])
        with fc2:
            sel_status = st.selectbox(
                "Status",
                ["All", "Confirmed", "Invoiced", "Draft", "Void"],
                index=1, key="lbl_status",
            )
            font_size = st.slider("Font size (pt)", 6, 14, 8, 1, key="lbl_fs")
        with fc3:
            st.write(""); st.write("")
            if st.button("\U0001f504 Fetch from Zoho", type="primary",
                         disabled=not auth_ok, use_container_width=True):
                start_d, end_d = sel_dates
                all_dates, d = [], start_d
                while d <= end_d:
                    all_dates.append(d)
                    d += timedelta(days=1)
                lbl = (f"{start_d.strftime('%d %b')} – {end_d.strftime('%d %b %Y')}"
                       if start_d != end_d else start_d.strftime("%d %b %Y"))
                with st.spinner(f"Fetching {lbl}…"):
                    try:
                        token   = get_token()
                        all_raw = []
                        for dd in all_dates:
                            for o in fetch_salesorders_by_date(token, dd, sel_status):
                                o["_fetch_date"] = dd.isoformat()
                                all_raw.append(o)

                        # Auto-fetch full details if any order is missing street address
                        needs = [o for o in all_raw
                                 if not (o.get("shipping_address") or {}).get("address")]
                        if needs:
                            prog2 = st.progress(0, "Loading full order details…")
                            detailed = []
                            for idx2, o in enumerate(all_raw):
                                try:
                                    det = get_salesorder_detail(token, o["salesorder_id"])
                                    det["_fetch_date"] = o.get("_fetch_date", "")
                                    detailed.append(det)
                                except Exception:
                                    detailed.append(o)
                                prog2.progress((idx2 + 1) / len(all_raw),
                                               text=f"Loading {idx2+1}/{len(all_raw)}…")
                            prog2.empty()
                            all_raw = detailed

                        oid_list = [o.get("salesorder_id", "") for o in all_raw]
                        rows     = [_lbl_order_to_row(o) for o in all_raw]
                        st.session_state["lbl_order_df"]    = (
                            pd.DataFrame(rows) if rows
                            else pd.DataFrame(columns=LBL_TABLE_COLS)
                        )
                        st.session_state["lbl_oid_list"]    = oid_list
                        st.session_state["lbl_fetch_dates"] = sel_dates
                        st.rerun()
                    except Exception as exc:
                        st.error(str(exc))

    order_df = st.session_state["lbl_order_df"]
    if order_df is None:
        st.info(
            "\U0001f448 Pick a date range and click **Fetch from Zoho**.\n\n"
            "Or click Fetch once (even with 0 results) then use the ➕ "
            "in the table to enter orders manually."
        )
        return

    fd         = st.session_state["lbl_fetch_dates"]
    date_label = (f"{fd[0].strftime('%d %b')} – {fd[1].strftime('%d %b %Y')}"
                  if fd[0] != fd[1] else fd[0].strftime("%d %b %Y"))
    file_sfx   = (f"{fd[0].isoformat()}_{fd[1].isoformat()}"
                  if fd[0] != fd[1] else fd[0].isoformat())
    font_size  = st.session_state.get("lbl_fs", 8)

    st.success(f"✅ **{len(order_df)} order(s)** loaded · {date_label}")

    # ── Editable table ────────────────────────────────────────────────────────
    st.subheader("\U0001f4cb Orders — Edit, Add, Select")
    st.caption(
        "• Edit any cell  |  "
        "• ➕ at table bottom to add a manual row  |  "
        "• Uncheck **Print?** to exclude a row from PDF  |  "
        "• Unchecked rows also excluded from Mark as Shipped"
    )


    # Bulk select / deselect
    ba1, ba2, _ = st.columns([1, 1, 6])
    with ba1:
        if st.button("☑️ Select All", use_container_width=True):
            st.session_state["lbl_order_df"] = st.session_state["lbl_order_df"].copy()
            st.session_state["lbl_order_df"]["✓"] = True
            st.session_state.pop("tbl_lbl", None)  # clear editor delta
            st.rerun()
    with ba2:
        if st.button("⬜ Deselect All", use_container_width=True):
            st.session_state["lbl_order_df"] = st.session_state["lbl_order_df"].copy()
            st.session_state["lbl_order_df"]["✓"] = False
            st.session_state.pop("tbl_lbl", None)  # clear editor delta
            st.rerun()
    edited_df = st.data_editor(
        order_df,
        key="tbl_lbl",
        hide_index=True,
        use_container_width=True,
        num_rows="dynamic",
        column_config={
            "✓":          st.column_config.CheckboxColumn("Print?",     default=True,  width=60),
            "Date":       st.column_config.TextColumn("Date",            width=100),
            "Order #":    st.column_config.TextColumn("Order #",         width=110),
            "Name":       st.column_config.TextColumn("Name",            width=170),
            "Address":    st.column_config.TextColumn("Address",         width=260),
            "City/State": st.column_config.TextColumn("City / State",    width=160),
            "Pincode":    st.column_config.TextColumn("Pincode",         width=90),
            "Phone":      st.column_config.TextColumn("Phone",           width=140),
            "Amount":     st.column_config.TextColumn("Amount",          width=90),
        },
    )

    # ── Label preview ─────────────────────────────────────────────────────────
    valid = (edited_df
             .dropna(subset=["Name"])
             .query("Name.str.strip() != ''", engine="python")
             .reset_index(drop=True))

    if not valid.empty:
        st.divider()
        st.subheader("\U0001f50d Label Preview")
        st.caption("Select any order to see exactly how its label will look.")
        options  = [f"{r.get('Order #', '—') or 'Manual'} — {r.get('Name', '')}"
                    for _, r in valid.iterrows()]
        sel_idx  = st.selectbox("Preview order:", range(len(options)),
                                format_func=lambda i: options[i], key="lbl_prev_sel")
        col_prev, col_detail = st.columns([1, 1])
        with col_prev:
            st.markdown(_lbl_preview_html(valid.iloc[sel_idx].to_dict(), font_size),
                        unsafe_allow_html=True)
        with col_detail:
            st.markdown("**Fields that will print:**")
            pr = valid.iloc[sel_idx]
            for field in ["Name", "Address", "City/State", "Pincode", "Phone"]:
                val  = str(pr.get(field, "")).strip()
                icon = "✅" if val else "⚠️ empty"
                st.markdown(f"`{field}` {icon}  {val}")
            st.caption(f"Font: **{font_size}pt**")

    # ── PDF generation ────────────────────────────────────────────────────────
    st.divider()
    st.subheader("\U0001f5a8️ Generate PDF Labels")

    selected_df = (edited_df[edited_df.get("✓", True) == True]
                   .dropna(subset=["Name"])
                   .query("Name.str.strip() != ''", engine="python"))
    selected_rows = selected_df.to_dict("records")
    n_pages = max(1, (len(selected_rows) + 3) // 4)

    if not selected_rows:
        st.warning("No rows checked (Print? column), or all checked rows have empty Name.")
    else:
        m1, m2, m3, m4 = st.columns(4)
        m1.metric("Labels",   len(selected_rows))
        m2.metric("A4 Pages", n_pages)
        m3.metric("Font",     f"{font_size}pt")
        m4.metric("Date",     date_label)

        confirmed = st.checkbox(
            f"✅ Confirm — generate **{len(selected_rows)} label(s)** "
            f"across **{n_pages} page(s)** at **{font_size}pt**",
            value=False, key="lbl_confirm",
        )
        if confirmed:
            if st.button("\U0001f4c4 Generate PDF", type="primary", use_container_width=True):
                with st.spinner("Building PDF…"):
                    pdf_bytes = _lbl_generate_pdf(selected_rows, font_size)
                st.success(
                    f"✅ PDF ready — {len(selected_rows)} labels, "
                    f"{n_pages} page(s), font {font_size}pt."
                )
                st.download_button(
                    label=f"⬇️ Download shipping_labels_{file_sfx}.pdf",
                    data=pdf_bytes,
                    file_name=f"shipping_labels_{file_sfx}.pdf",
                    mime="application/pdf",
                    use_container_width=True,
                    type="primary",
                )
        else:
            st.info("Tick the confirmation checkbox above to enable PDF generation.")

    # ── Mark as Shipped ───────────────────────────────────────────────────────
    st.divider()
    st.subheader("✅ Mark as Shipped in Zoho")
    st.caption(
        "Checked rows with a valid Order # will be packaged and marked as shipped. "
        "Manually added rows (no Order #) are skipped automatically."
    )

    oid_list = st.session_state["lbl_oid_list"]

    # Use positional index (enumerate) — iterrows() idx label can diverge from
    # oid_list position after edits/adds, causing wrong or empty salesorder_id.
    ship_oids  = []
    ship_onums = []
    rows_list  = list(edited_df.iterrows())
    for pos, (_, row) in enumerate(rows_list):
        if not row.get("✓", False):
            continue
        onum = str(row.get("Order #", "")).strip()
        if not onum:
            continue                         # manually added row — no Zoho ID
        oid = oid_list[pos] if pos < len(oid_list) else ""
        if oid:
            ship_oids.append(oid)
            ship_onums.append(onum)
        else:
            st.warning(f"Row {pos+1} (Order {onum}): no salesorder_id found — skipped.")

    if not ship_oids:
        st.info("No checked rows have a valid Order # to ship.")
    else:
        # ── Row 1: Carrier + Dispatch Date ────────────────────────────────────
        sc1, sc2, sc3 = st.columns([3, 2, 2])
        with sc1:
            carrier = st.text_input(
                "Carrier",
                placeholder="Delhivery / Trackon / Shree Maruti",
                key="ship_carrier",
            )
        with sc2:
            dispatch_date = st.date_input(
                "Dispatch Date",
                value=date.today(),
                key="ship_dispatch_date",
                help="Package date + shipment date sent to Zoho. Default: today.",
            )
        with sc3:
            shipping_charge = st.number_input(
                "Shipping Charge (₹)",
                min_value=0.0, value=0.0, step=10.0,
                key="ship_charge",
                help="Optional. Logged against the shipment in Zoho.",
            )

        # ── Row 2: Tracking + Notes ───────────────────────────────────────────
        sn1, sn2 = st.columns([2, 3])
        with sn1:
            tracking_number = st.text_input(
                "Tracking / Docket No.",
                placeholder="e.g. 123456789012",
                key="ship_tracking",
                help="Delhivery / Trackon docket number — stored in Zoho shipment.",
            )
        with sn2:
            pkg_notes = st.text_input(
                "Package Notes (optional)",
                placeholder="e.g. Handle with care",
                key="ship_notes",
            )

        st.write("")
        if st.button(
            f"\U0001f69a Mark {len(ship_oids)} Order(s) as Shipped",
            disabled=not auth_ok,
            type="secondary",
            use_container_width=True,
        ):
            _mark_orders_shipped(
                ship_oids, ship_onums,
                carrier=carrier,
                tracking_number=tracking_number,
                shipping_charge=float(shipping_charge),
                dispatch_date=dispatch_date.isoformat(),
                pkg_notes=pkg_notes,
                dry_run=dry_run,
            )


# ════════════════════════════════════════════════════════════════════════════════
# MAIN
# ════════════════════════════════════════════════════════════════════════════════
def main():
    st.title("🏺 Maharani Inventory Tool")
    st.caption(
        "Build standard items, composite packs, and item groups — "
        "review them in an editable table, check against Zoho, then push directly via API."
    )

    auth_ok, dry_run = _sidebar()

    if dry_run:
        st.warning(
            "🔬 **Dry Run mode is ON.** "
            "All write operations are simulated — nothing will be created or changed in Zoho.",
            icon="🔬",
        )

    t1, t2, t3, t4, t5, t6 = st.tabs([
        "📦 Standard Items",
        "🏗️ Composite Packs",
        "📮 Labels & Shipping",
        "📋 Push Log",
        "🏷️ Barcode Generator",
        "🖼️ WebP Converter",
    ])

    with t1: tab_standard_items(auth_ok=auth_ok, dry_run=dry_run)
    with t2: tab_composite_items(auth_ok=auth_ok, dry_run=dry_run)
    with t3: tab_labels_shipping(auth_ok=auth_ok, dry_run=dry_run)
    with t4: tab_push_log()
    with t5: tab_barcode_generator()
    with t6: tab_webp_converter()


# ══════════════════════════════════════════════════════════════════════════════
# TAB 6 — WEBP CONVERTER
# ══════════════════════════════════════════════════════════════════════════════

def tab_webp_converter():
    """Convert PNG / JPG images to WebP — single image or batch ZIP."""
    from PIL import Image as _PILImage, ImageOps as _PILImageOps

    st.header("🖼️ WebP Converter")
    st.caption(
        "Convert PNG or JPG images to WebP for faster website loading. "
        "Single image → download .webp. Multiple images → download ZIP."
    )

    mode = st.radio(
        "Conversion mode",
        ["🖼️ Single Image", "📁 Batch (Multiple Images)"],
        horizontal=True,
        key="wc_mode",
    )

    quality = st.slider(
        "WebP Quality",
        min_value=1, max_value=100, value=80,
        key="wc_quality",
        help="80 = recommended for product images (great quality, ~60% smaller than PNG).",
    )

    st.divider()

    # ── SINGLE IMAGE ──────────────────────────────────────────────────────────
    if mode == "🖼️ Single Image":
        uploaded = st.file_uploader(
            "Upload image — drag & drop or browse",
            type=["png", "jpg", "jpeg"],
            key="wc_single_upload",
        )

        if uploaded:
            # Read bytes once — prevents file-pointer exhaustion when PIL opens
            # the same stream that st.image() already consumed
            raw_bytes = uploaded.read()
            orig_size  = len(raw_bytes)

            # Apply EXIF rotation before showing the original preview too
            _prev_img = _PILImageOps.exif_transpose(_PILImage.open(BytesIO(raw_bytes)))
            _prev_buf = BytesIO()
            _prev_fmt = "PNG" if _prev_img.mode in ("RGBA", "LA") else "JPEG"
            _prev_img.save(_prev_buf, format=_prev_fmt)

            col_orig, col_conv = st.columns(2)
            with col_orig:
                st.caption(f"**Original:** `{uploaded.name}`  ·  {orig_size / 1024:.1f} KB")
                st.image(_prev_buf.getvalue(), use_container_width=True)

            if st.button("⚡ Convert to WebP", type="primary", key="wc_single_btn"):
                try:
                    img = _PILImage.open(BytesIO(raw_bytes))   # fresh BytesIO — no pointer issue
                    img = _PILImageOps.exif_transpose(img)     # fix phone camera EXIF rotation
                    buf = BytesIO()
                    # Preserve transparency for PNG, otherwise convert to RGB
                    if img.mode in ("RGBA", "LA"):
                        img.save(buf, format="WEBP", quality=quality, lossless=False)
                    else:
                        img.convert("RGB").save(buf, format="WEBP", quality=quality)
                    webp_bytes = buf.getvalue()

                    out_name    = os.path.splitext(uploaded.name)[0] + ".webp"
                    saving_pct  = (1 - len(webp_bytes) / orig_size) * 100

                    with col_conv:
                        st.caption(
                            f"**Converted:** `{out_name}`  ·  {len(webp_bytes) / 1024:.1f} KB"
                        )
                        st.image(webp_bytes, use_container_width=True)

                    st.success(
                        f"✅ Done!  Size reduced by **{saving_pct:.1f}%** "
                        f"({orig_size // 1024} KB → {len(webp_bytes) // 1024} KB)"
                    )
                    st.download_button(
                        label=f"⬇️ Download {out_name}",
                        data=webp_bytes,
                        file_name=out_name,
                        mime="image/webp",
                        type="primary",
                        key="wc_single_dl",
                    )
                except Exception as e:
                    st.error(f"Conversion failed: {e}")

    # ── BATCH MODE ────────────────────────────────────────────────────────────
    else:
        uploaded_files = st.file_uploader(
            "Upload images — drag & drop multiple files or browse",
            type=["png", "jpg", "jpeg"],
            accept_multiple_files=True,
            key="wc_batch_upload",
            help="All converted files will be bundled in a ZIP named {folder}_webp.zip",
        )

        if uploaded_files:
            total_kb = sum(f.size for f in uploaded_files) / 1024
            st.caption(
                f"📁 **{len(uploaded_files)} file(s)** selected  ·  {total_kb:.1f} KB total"
            )

            folder_name = st.text_input(
                "Output name (ZIP will be saved as: {name}_webp.zip)",
                value="images",
                key="wc_folder_name",
            )

            with st.expander(f"📋 Files queued for conversion ({len(uploaded_files)})", expanded=True):
                for f in uploaded_files:
                    st.write(f"• `{f.name}` — {f.size / 1024:.1f} KB")

            if st.button("⚡ Convert All to WebP", type="primary", key="wc_batch_btn"):
                try:
                    zip_buf   = BytesIO()
                    converted = 0
                    skipped   = []
                    progress  = st.progress(0, text="Starting conversion…")

                    with zipfile.ZipFile(zip_buf, "w", zipfile.ZIP_DEFLATED) as zf:
                        for i, f in enumerate(uploaded_files):
                            try:
                                img     = _PILImage.open(BytesIO(f.read()))  # BytesIO avoids pointer exhaustion
                                img     = _PILImageOps.exif_transpose(img)   # fix phone camera EXIF rotation
                                img_buf = BytesIO()
                                if img.mode in ("RGBA", "LA"):
                                    img.save(img_buf, format="WEBP", quality=quality)
                                else:
                                    img.convert("RGB").save(img_buf, format="WEBP", quality=quality)
                                out_name = os.path.splitext(f.name)[0] + ".webp"
                                zf.writestr(out_name, img_buf.getvalue())
                                converted += 1
                            except Exception as ex:
                                skipped.append(f"{f.name} ({ex})")
                            progress.progress(
                                (i + 1) / len(uploaded_files),
                                text=f"Converting {i + 1}/{len(uploaded_files)}: {f.name}",
                            )

                    zip_buf.seek(0)
                    progress.empty()
                    zip_name = f"{folder_name}_webp.zip"

                    if skipped:
                        st.warning(f"Skipped {len(skipped)} file(s): {', '.join(skipped)}")
                    st.success(f"✅ Converted {converted}/{len(uploaded_files)} images!")

                    st.download_button(
                        label=f"⬇️ Download {zip_name}",
                        data=zip_buf.getvalue(),
                        file_name=zip_name,
                        mime="application/zip",
                        type="primary",
                        key="wc_batch_dl",
                    )
                except Exception as e:
                    st.error(f"Batch conversion failed: {e}")


if __name__ == "__main__":
    main()
