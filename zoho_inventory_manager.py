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
from datetime import datetime, date, timedelta
from io import BytesIO

import requests
import pandas as pd
import streamlit as st
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm
from reportlab.pdfgen import canvas as rl_canvas

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

RATE_DELAY     = 0.7   # seconds between API calls — keeps us safely under 100/min
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
    "api_calls":       0,
    "token":           None,
    "token_expiry":    0.0,
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
    st.session_state["api_calls"] += 1
    time.sleep(RATE_DELAY)


def _call_guard():
    """Raise if we're approaching the per-minute API limit."""
    if st.session_state["api_calls"] >= CALL_HARD_STOP:
        raise RuntimeError(
            f"API call count reached {CALL_HARD_STOP}. "
            "Reset the counter in the sidebar before continuing."
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

    # ── API call counter ──
    n = st.session_state["api_calls"]
    color = "green" if n < CALL_WARN else ("orange" if n < CALL_HARD_STOP else "red")
    st.sidebar.markdown(f"**API calls this session:** :{color}[{n} / {CALL_HARD_STOP}]")
    if n >= CALL_WARN:
        st.sidebar.warning("Approaching rate limit. Writes will stop at 90 calls.")
    if st.sidebar.button("🔄 Reset call counter"):
        st.session_state["api_calls"] = 0
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
    # ── Source for base items (used by the generator form below) ─────────────
    source = st.radio(
        "Base items source:",
        ["Current Session (Tab 1)", "Upload Items CSV"],
        horizontal=True, key="comp_src",
    )
    source_df = pd.DataFrame()
    if source == "Current Session (Tab 1)":
        source_df = pd.DataFrame(st.session_state["items_list"])
    else:
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

    t1, t2, t3, t4 = st.tabs([
        "📦 Standard Items",
        "🏗️ Composite Packs",
        "📮 Labels & Shipping",
        "📋 Push Log",
    ])

    with t1: tab_standard_items(auth_ok=auth_ok, dry_run=dry_run)
    with t2: tab_composite_items(auth_ok=auth_ok, dry_run=dry_run)
    with t3: tab_labels_shipping(auth_ok=auth_ok, dry_run=dry_run)
    with t4: tab_push_log()


if __name__ == "__main__":
    main()
