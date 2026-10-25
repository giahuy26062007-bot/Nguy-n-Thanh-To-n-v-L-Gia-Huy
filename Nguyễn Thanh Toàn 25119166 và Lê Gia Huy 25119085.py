
import sys, os, re, csv, json, zipfile, math, copy, random, heapq, queue, threading, traceback, argparse

if hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

# MÀU CƠ BẢN CỦA PROTEUS
PROTEUS_COLORS = {
    "BG": "#0F0F0F",
    "GRID": "#1E1E1E",
    "BOARD_EDGE": "#FFFF00",
    "SILK": "#00FFFF",
    "PAD": "#8E44AD",
    "PAD_HOLE": "#FFFFFF",
    "PIN_TEXT": "#FFFFFF",
    "REF_TEXT": "#00FFFF",
    "RATS_NEST": "#00FF00",
    "TOP_COPPER": "#0088FF",
    "BOT_COPPER": "#FF0000"
}
try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
    HAVE_TK = True
except Exception:
    HAVE_TK = False

GRID = 25
MM = 1000.0 / 25.4
PAD_D = 60
HOLE_D = 32
VIA_D = 60
SQRT2 = math.sqrt(2.0)
DIRS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
DIRS8 = [(1, 0), (0, 1), (-1, 0), (0, -1), (1, 1), (-1, 1), (-1, -1), (1, -1)]
STEP_COST8 = (1.0, 1.0, 1.0, 1.0, SQRT2, SQRT2, SQRT2, SQRT2)

DEFAULT_CLASSES = {
    "SIGNAL":       {"w": 25,  "c": 20},
    "POWER":        {"w": 60,  "c": 20},
    "HIGH_CURRENT": {"w": 110, "c": 25},
    "HV_AC":        {"w": 40,  "c": 60},
}
POWER_RE = re.compile(r"^(?:[AD]?GND|VSS|VCC|VDD|VEE|VBAT|VIN|V[+-]|0|[+-]\d.*)$", re.I)
GND_RE = re.compile(r"^(?:[AD]?GND|VSS|0|COM)$", re.I)
HV_RE = re.compile(r"(MAINS|^AC|AC_|_AC|^HV|220V|230V|^L1$|NEUTRAL)", re.I)
HI_RE = re.compile(r"(MOTOR|LOAD|PWR_OUT|HICUR|HI_CUR)", re.I)
EDGE_COMP_RE = re.compile(r"^(?:J\d|JP\d|CON|CN\d|P\d|SW|BTN|KEY|USB|DC|PWR|TERM|TBLOCK|DOMINO|KF301|HDR|HEADER|PINHDR|JACK)", re.I)
IC_REF_RE = re.compile(r"^(?:U\d|IC\d|MCU|ESP|ARD|MOD)", re.I)
BYPASS_VAL_RE = re.compile(r"(?:100N|0\.?1U|104|10N|103|47N|22N|1U|0\.?47U|BYPASS|DECOUP)", re.I)
NONPOLAR_REF_RE = re.compile(r"^(?:R\d|RN\d|L\d|FB\d|F\d|SW\d|BTN\d)", re.I)
POLAR_CAP_RE = re.compile(r"(?:ELEC|POL|TANT|CAPPR|ELCO)", re.I)


def classify(name):
    if HV_RE.search(name):
        return "HV_AC"
    if HI_RE.search(name):
        return "HIGH_CURRENT"
    if POWER_RE.match(name):
        return "POWER"
    return "SIGNAL"


def snap(v):
    return int(round(v / float(GRID))) * GRID


def rotpt(dx, dy, r):
    return [(dx, dy), (-dy, dx), (-dx, -dy), (dy, -dx)][r % 4]


FOOTPRINT_DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "footprint_db.json")

BUILTIN_FOOTPRINTS = {
    "MODULE_ESP32C3_SUPERMINI_TH": {
        "desc": "ESP32-C3 SuperMini 16-pin (2x8, row pitch 600 mil / 15.24mm)",
        "pads": [
            [600, 700], [600, 600], [600, 500], [600, 400],
            [600, 200], [600, 300], [0, 0],     [600, 0],
            [0, 100],   [0, 200],   [0, 300],   [0, 400],
            [0, 500],   [0, 600],   [0, 700],   [600, 100]
        ],
        "body": [-65, -120, 665, 800],
        "pin_map": {
            "0": 0, "IO0": 0,
            "1": 1, "IO1": 1,
            "2": 2, "IO2": 2,
            "3": 3, "IO3": 3,
            "3_3": 4, "3V3": 4, "3.3V": 4,
            "4": 5, "IO4": 5,
            "5": 6, "IO5": 6,
            "5V": 7, "VCC": 7,
            "6": 8, "IO6": 8,
            "7": 9, "IO7": 9,
            "8": 10, "IO8": 10,
            "9": 11, "IO9": 11,
            "10": 12, "IO10": 12,
            "20": 13, "IO20": 13, "RX": 13,
            "21": 14, "IO21": 14, "TX": 14,
            "G": 15, "GND": 15
        }
    },
    "ESP32C3_SUPERMINI_TH": {
        "alias": "MODULE_ESP32C3_SUPERMINI_TH"
    },
    "MODULE_DFR0299": {
        "desc": "DFPlayer Mini MP3 Module DIP-16 (row pitch 710 mil / 18.034mm)",
        "pads": (
            [[0, i * 100] for i in range(8)] +
            [[700, (7 - j) * 100] for j in range(8)]
        ),
        "exact_pads": (
            [[0.0, float(i * 100)] for i in range(8)] +
            [[710.0, float((7 - j) * 100)] for j in range(8)]
        ),
        "origin": [355.0, 350.0],
        "square_pins": [0],
        "body": [-75, -60, 785, 760],
        "pin_map": {str(i): i - 1 for i in range(1, 17)}
    },
    "DFR0299": {
        "alias": "MODULE_DFR0299"
    },
    "INMP441": {
        "desc": "Module Mic I2S INMP441 6-pin (2x3, row pitch 200 mil / 5.08mm)",
        "pads": [
            [0, 0],   [100, 0],   [200, 0],
            [0, 200], [100, 200], [200, 200]
        ],
        "exact_pads": [
            [0.0, 0.0],   [100.0, 0.0],   [200.0, 0.0],
            [0.0, 200.0], [100.0, 200.0], [200.0, 200.0]
        ],
        "origin": [0.0, 0.0],
        "square_pins": [0],
        "body": [-80, -80, 280, 280],
        "pin_map": {"1": 0, "2": 1, "3": 2, "4": 3, "5": 4, "6": 5}
    },
    "JST_B2BPHKS": {
        "desc": "Connector JST B2B-PH-K-S 2-pin (pitch 2.00mm / 78.74 mil)",
        "pads": [[75, 0], [0, 0]],
        "exact_pads": [[78.74, 0.0], [0.0, 0.0]],
        "origin": [39.37, -21.65],
        "square_pins": [0],
        "body": [-77, -201, 156, 47],
        "pin_map": {"1": 0, "2": 1, "+": 0, "-": 1}
    },
    "TBLOCK-I2": {
        "desc": "Domino / Terminal Block 2-pin (pitch 200 mil / 5.08mm)",
        "pads": [[0, 0], [200, 0]],
        "body": [-60, -80, 260, 80],
        "pin_map": {"1": 0, "2": 1, "+": 0, "-": 1}
    },
    "CONN-SIL3": {
        "desc": "Header đơn 3 chân (pitch 100 mil / 2.54mm)",
        "pads": [[0, 0], [100, 0], [200, 0]],
        "body": [-50, -50, 250, 50],
        "pin_map": {"1": 0, "2": 1, "3": 2}
    },
    "CONN-SIL4": {
        "desc": "Header đơn 4 chân (pitch 100 mil / 2.54mm)",
        "pads": [[0, 0], [100, 0], [200, 0], [300, 0]],
        "body": [-50, -50, 350, 50],
        "pin_map": {"1": 0, "2": 1, "3": 2, "4": 3}
    },
    "RES40": {
        "desc": "Điện trở cắm đứng/nằm 400 mil (10.16mm)",
        "pads": [[0, 0], [400, 0]],
        "body": [60, -40, 340, 40],
        "pin_map": {"1": 0, "2": 1}
    },
    "CAP10": {
        "desc": "Tụ điện 100 mil (2.54mm)",
        "pads": [[0, 0], [100, 0]],
        "body": [-40, -70, 140, 70],
        "pin_map": {"1": 0, "2": 1, "+": 0, "-": 1}
    },
    "CAP30": {
        "desc": "Tụ điện 300 mil (7.62mm)",
        "pads": [[0, 0], [300, 0]],
        "body": [-40, -70, 340, 70],
        "pin_map": {"1": 0, "2": 1, "+": 0, "-": 1}
    },
    "LED": {
        "desc": "LED 5mm (pitch 100 mil / 2.54mm)",
        "pads": [[0, 0], [100, 0]],
        "body": [-40, -80, 140, 80],
        "pin_map": {"1": 0, "2": 1, "A": 0, "K": 1, "+": 0, "-": 1}
    },
    "TO92": {
        "desc": "Transistor TO-92 3 chân",
        "pads": [[0, 0], [100, 0], [200, 0]],
        "body": [-40, -120, 240, 40],
        "pin_map": {"1": 0, "2": 1, "3": 2, "E": 0, "B": 1, "C": 2}
    }
}


class FootprintLibrary:
    def __init__(self, path=FOOTPRINT_DB_PATH):
        self.path = path
        self.db = {}
        self.reload()

    @staticmethod
    def norm_key(name):
        return (name or "").strip().upper().replace(" ", "")

    def reload(self):
        self.db = copy.deepcopy(BUILTIN_FOOTPRINTS)
        if os.path.isfile(self.path):
            try:
                with open(self.path, "r", encoding="utf-8") as f:
                    user_db = json.load(f)
                if isinstance(user_db, dict):
                    for k, v in user_db.items():
                        if str(k).startswith("_"):
                            self.db[k] = v
                            continue
                        nk = self.norm_key(k)
                        if nk in self.db and isinstance(self.db[nk], dict) and isinstance(v, dict):
                            merged = copy.deepcopy(self.db[nk])
                            merged.update(v)
                            if "pads" in v:
                                merged.pop("alias", None)
                                if "pin_map" in v and v["pin_map"]:
                                    merged["pin_map"] = copy.deepcopy(v["pin_map"])
                            elif "pin_map" in self.db[nk] and "pin_map" in v:
                                pm = copy.deepcopy(self.db[nk]["pin_map"])
                                pm.update(v["pin_map"])
                                merged["pin_map"] = pm
                            self.db[nk] = merged
                        else:
                            self.db[nk] = v
            except Exception:
                pass
        else:
            self.save()

    def save(self):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self.db, f, indent=2, ensure_ascii=False)
        except Exception:
            pass

    def get(self, name):
        k = self.norm_key(name)
        if not k or k.startswith("_"):
            return None
        visited = set()
        while k in self.db and k not in visited:
            visited.add(k)
            entry = self.db[k]
            if isinstance(entry, dict) and "alias" in entry and "pads" not in entry:
                k = self.norm_key(entry["alias"])
            else:
                return entry if isinstance(entry, dict) and "pads" in entry else None
        for db_key, entry in self.db.items():
            if db_key.startswith("_") or not isinstance(entry, dict) or "pads" not in entry:
                continue
            if k.startswith(db_key + "_") or k.endswith("_" + db_key):
                return entry
        return None

    def register(self, name, pads, body, pin_map=None, desc="", save_now=True,
                 exact_pads=None, origin=None, square_pins=None, source=""):
        k = self.norm_key(name)
        if not k or k.startswith("_"):
            return
        existing = self.db.get(k, {})

        if isinstance(existing, dict) and existing.get("source") == "pdif" and source == "edf":
            if pin_map and "pin_map" in existing:
                for pk, pv in pin_map.items():
                    existing["pin_map"].setdefault(str(pk), int(pv))
            return
        pm = {} if source == "pdif" else (copy.deepcopy(existing.get("pin_map", {})) if isinstance(existing, dict) else {})

        if pin_map:
            for pk, pv in pin_map.items():
                pm[str(pk)] = int(pv)
        entry = {
            "desc": desc or (existing.get("desc", "") if isinstance(existing, dict) else ""),
            "pads": [[int(round(px)), int(round(py))] for px, py in pads],
            "body": [int(round(b)) for b in body] if body else [-50, -50, 150, 50],
            "pin_map": pm
        }
        if exact_pads is not None:
            entry["exact_pads"] = [[round(float(px), 2), round(float(py), 2)] for px, py in exact_pads]
        elif isinstance(existing, dict) and "exact_pads" in existing and len(existing["exact_pads"]) == len(pads):
            entry["exact_pads"] = existing["exact_pads"]
        if origin is not None:
            entry["origin"] = [round(float(origin[0]), 2), round(float(origin[1]), 2)]
        elif isinstance(existing, dict) and "origin" in existing:
            entry["origin"] = existing["origin"]
        if square_pins is not None:
            entry["square_pins"] = [int(i) for i in square_pins]
        elif isinstance(existing, dict) and "square_pins" in existing:
            entry["square_pins"] = existing["square_pins"]
        if source:
            entry["source"] = source
        elif isinstance(existing, dict) and "source" in existing:
            entry["source"] = existing["source"]
        self.db[k] = entry
        if save_now:
            self.save()

FOOTPRINT_DB = FootprintLibrary()

def _snap_pads_distinct(raw_pads_mil):
    if not raw_pads_mil:
        return [(0, 0)]
    min_x = min(p[0] for p in raw_pads_mil)
    min_y = min(p[1] for p in raw_pads_mil)
    snapped = []
    used = set()
    for x, y in raw_pads_mil:
        sx = snap(x - min_x)
        sy = snap(y - min_y)
        if (sx, sy) in used:
            best_cell = None
            for r in range(1, 10):
                for dx in range(-r, r + 1):
                    for dy in range(-r, r + 1):
                        cand = (sx + dx * GRID, sy + dy * GRID)
                        if cand not in used:
                            dist = math.hypot(cand[0] - (x - min_x), cand[1] - (y - min_y))
                            if best_cell is None or dist < best_cell[0]:
                                best_cell = (dist, cand)
                if best_cell:
                    sx, sy = best_cell[1]
                    break
        used.add((sx, sy))
        snapped.append((sx, sy))
    return snapped


def _parse_snapeda_ipc(n, npins):
    m = re.match(r"^DIP(\d+)W\d+P(\d+)L(\d+)H\d+Q(\d+)", n)
    if m:
        span = max(GRID, snap(int(m.group(1)) * 0.01 * MM))
        pitch = max(GRID, snap(int(m.group(2)) * 0.01 * MM))
        k = max(npins, int(m.group(4)))
        half = (k + 1) // 2
        pads = [(0, i * pitch) for i in range(half)] + [(span, (half - 1 - j) * pitch) for j in range(k - half)]
        return pads, (-50, -50, span + 50, (half - 1) * pitch + 50)


    m = re.match(r"^(?:RESAD|DIOAD)(\d+)W\d+L(\d+)D(\d+)", n)
    if m:
        pitch = max(100, snap(int(m.group(1)) * 0.01 * MM))
        rad = max(35, int(round(int(m.group(3)) * 0.01 * MM / 2.0)))
        return [(0, 0), (pitch, 0)], (50, -rad, pitch - 50, rad)

    m = re.match(r"^CAPP?RD(\d+)W\d+D(\d+)", n)
    if m:
        pitch = max(50, snap(int(m.group(1)) * 0.01 * MM))
        r = max(50, int(round(int(m.group(2)) * 0.01 * MM / 2.0)))
        return [(0, 0), (pitch, 0)], (-40, -r, pitch + 40, r)

    m = re.match(r"^HDRV(\d+)W\d+P(\d+)(?:_(\d+)X(\d+))?", n)
    if m:
        k = max(npins, int(m.group(1)))
        pitch = max(GRID, snap(int(m.group(2)) * 0.01 * MM))
        rows = int(m.group(3)) if m.group(3) else 1
        cols = int(m.group(4)) if m.group(4) else k
        if rows == 2 and cols >= 1:
            pads = [(0, i * pitch) for i in range(cols)] + [(pitch, i * pitch) for i in range(cols)]
            return pads, (-50, -50, pitch + 50, (cols - 1) * pitch + 50)
        pads = [(i * pitch, 0) for i in range(k)]
        return pads, (-50, -50, (k - 1) * pitch + 50, 50)

    return None


def make_footprint(name, npins):
    n = FootprintLibrary.norm_key(name)

    db_entry = FOOTPRINT_DB.get(n)
    if db_entry and "pads" in db_entry:
        pads = [tuple(p) for p in db_entry["pads"]]
        body = tuple(db_entry.get("body", (-50, -50, 150, 50)))
        if len(pads) >= npins:
            return pads, body

    ipc = _parse_snapeda_ipc(n, npins)
    if ipc is not None:
        return ipc

    def sil(k, pitch=100):
        k = max(1, k)
        pads = [(i * pitch, 0) for i in range(k)]
        return pads, (-50, -50, (k - 1) * pitch + 50, 50)

    def two(pitch, bw=60):
        return [(0, 0), (pitch, 0)], (bw, -40, pitch - bw, 40)

    def dip(k, row_spacing=600):
        k = max(2, k)
        half = (k + 1) // 2
        pads = [(0, i * 100) for i in range(half)] + [(row_spacing, (half - 1 - j) * 100) for j in range(k - half)]
        body = (-50, -50, row_spacing + 50, max(50, (half - 1) * 100 + 50))
        return pads, body

    pads = body = None
    m = re.search(r"(?:DIP|DIL|PDIP|CDIP)[-_]?(\d+)", n)

    if "ESP32" in n or "SUPERMINI" in n or "DFR0299" in n or "DFPLAYER" in n:
        pads, body = dip(max(npins, 16), row_spacing=600)
    elif "INMP441" in n:
        pads = [(0, 0), (100, 0), (200, 0), (0, 200), (100, 200), (200, 200)]
        body = (-80, -80, 280, 280)
    elif "JST" in n or "B2B" in n or "PHK" in n or "XH" in n:
        pads, body = sil(max(npins, 2), pitch=100)
    elif "TBLOCK" in n or "DOMINO" in n or "KF301" in n:
        mm_tb = re.search(r"(\d+)$", n)
        k_tb = int(mm_tb.group(1)) if mm_tb else max(npins, 2)
        pads, body = sil(max(npins, k_tb), pitch=200)
    elif "MODULE" in n or "ARDUINO" in n or "A000067" in n or n.startswith("CONN-DIL") or n.startswith("HEADER2X"):
        pads, body = dip(npins, row_spacing=600 if npins >= 14 else 300)
    elif m and int(m.group(1)) >= 4:
        k = int(m.group(1))
        pads, body = dip(k, row_spacing=600 if k >= 24 else 300)
    elif re.match(r"^(RES|MINRES|AXIAL|DIODE|DO|RESISTOR|R\d|1N)", n):
        pads, body = two(400)
    elif n.startswith("LED"):
        pads, body = two(100, 0)
        body = (-40, -80, 140, 80)
    elif n.startswith("CAP") or n.startswith("C-") or n.startswith("ELEC"):
        m_cap = re.search(r"CAP(\d+)", n)
        pitch = int(m_cap.group(1)) * 10 if (m_cap and 10 <= int(m_cap.group(1)) <= 100) else 100
        pads, body = two(pitch, 0)
        body = (-40, -70, pitch + 40, 70)
    elif re.match(r"^TO-?(92|126|220|202)", n):
        pads = [(0, 0), (100, 0), (200, 0)]
        body = (-40, -120, 240, 40)
    elif re.search(r"(BUTTON|TACT|SW-?PB|PUSH)", n):
        pads = [(0, 0), (200, 0), (0, 200), (200, 200)]
        body = (50, 50, 150, 150)
    else:
        mm = re.search(r"(?:SIL|HEADER|HDR|PINHDR|JP|CONN)\D*?(\d+)", n)
        if mm and int(mm.group(1)) >= 1:
            pads, body = sil(int(mm.group(1)))
        elif npins > 4 and "SIL" not in n:
            pads, body = dip(npins, row_spacing=600)
        elif npins == 2 or npins == 0:
            pads, body = two(400)
        else:
            pads, body = sil(npins)

    if len(pads) < npins:
        pads, body = sil(npins)
    return pads, body


PIN_SYNONYMS = {
    "+": "1", "-": "2",
    "A": "1", "ANODE": "1", "K": "2", "CATHODE": "2",
    "E": "1", "B": "2", "C": "3",
}


class Comp:
    def __init__(self, ref, fp, value=""):
        self.ref, self.fp, self.value = ref, fp, value
        self.x = self.y = 0
        self.rot = 0
        self.fixed = False
        self.edge_pref = False
        self.swappable_pins = False
        self.label_offset = None
        self.label_rot_ref = None
        self.group = "G0"
        self.pads, self.body, self.labels, self.pin_net = [], None, {}, {}
        self.exact_pads = []
        self.origin = (0.0, 0.0)
        self.square_pins = set()
        self.pad_names = {}
        self.R, self.R_exact, self.bb = [], [], []

    def build(self, labels):
        db_entry = FOOTPRINT_DB.get(self.fp) or FOOTPRINT_DB.get(self.value)
        pin_map = {}
        if db_entry and isinstance(db_entry.get("pin_map"), dict):
            pin_map = {str(k).upper(): int(v) for k, v in db_entry["pin_map"].items()}

        self.labels = {}
        used_indices = set()
        unmapped = []

        for orig in labels:
            s_orig = str(orig).strip()
            s_up = s_orig.upper()
            if s_up in pin_map:
                idx = pin_map[s_up]
                self.labels[orig] = idx
                used_indices.add(idx)
            elif s_up.startswith("EDF_") and s_up[4:].isdigit():
                idx = int(s_up[4:])
                self.labels[orig] = idx
                used_indices.add(idx)
            else:
                unmapped.append(orig)

        mapped_unmapped = [PIN_SYNONYMS.get(str(l).strip().upper(), str(l).strip()) for l in unmapped]
        nums = {int(m) for m in mapped_unmapped if m.isdigit() and int(m) > 0}
        names = [orig for orig, m in zip(unmapped, mapped_unmapped) if not (m.isdigit() and int(m) > 0)]

        total_logical_pins = len(used_indices) + len(nums) + len(names)
        max_num = max(nums, default=0)

        if not db_entry and max_num > max(total_logical_pins + 4, 8):
            effective_max_num = total_logical_pins
        else:
            effective_max_num = max_num

        max_pin_num = max(
            max(used_indices, default=-1) + 1,
            effective_max_num,
            total_logical_pins
        )
        fp_key = self.fp if FOOTPRINT_DB.get(self.fp) else (self.value if FOOTPRINT_DB.get(self.value) else self.fp)
        self.pads, self.body = make_footprint(fp_key, max_pin_num)


        if len(self.pads) < max_pin_num:
            for extra_i in range(len(self.pads), max_pin_num):
                self.pads.append((extra_i * 100, 0))


        for orig, m in zip(unmapped, mapped_unmapped):
            if m.isdigit() and int(m) > 0:
                idx = int(m) - 1
                if idx not in used_indices and idx < len(self.pads):
                    self.labels[orig] = idx
                    self.labels[m] = idx
                    used_indices.add(idx)


        free = [i for i in range(len(self.pads)) if i not in used_indices]
        free_idx = 0
        for orig in labels:
            if orig not in self.labels:
                if free_idx < len(free):
                    idx = free[free_idx]
                    free_idx += 1
                else:
                    idx = len(self.pads)
                    self.pads.append((idx * 100, 0))
                self.labels[orig] = idx
                used_indices.add(idx)

        self.pad_names = {i: str(i + 1) for i in range(len(self.pads))}
        for k, v in pin_map.items():
            if not k.isdigit() and not k.startswith("EDF_") and v in self.pad_names:
                self.pad_names[v] = k
        for orig, idx in self.labels.items():
            s = str(orig)
            if not s.upper().startswith("EDF_"):
                self.pad_names[idx] = s

        if db_entry and isinstance(db_entry.get("exact_pads"), list) and len(db_entry["exact_pads"]) == len(self.pads):
            self.exact_pads = [(float(p[0]), float(p[1])) for p in db_entry["exact_pads"]]
        else:
            self.exact_pads = [(float(p[0]), float(p[1])) for p in self.pads]

        if db_entry and isinstance(db_entry.get("origin"), list) and len(db_entry["origin"]) == 2:
            self.origin = (float(db_entry["origin"][0]), float(db_entry["origin"][1]))
        else:
            self.origin = (0.0, 0.0)

        if db_entry and isinstance(db_entry.get("square_pins"), list) and db_entry["square_pins"]:
            self.square_pins = {int(i) for i in db_entry["square_pins"]}
        else:
            sq = set()
            for idx, pname in self.pad_names.items():
                if str(pname).strip().upper() in ("1", "A", "+", "VCC", "3_3", "3V3"):
                    sq.add(idx)
            self.square_pins = sq if sq else {0}


        self.R = [[rotpt(dx, dy, r) for dx, dy in self.pads] for r in range(4)]
        self.R_exact = [[rotpt(dx, dy, r) for dx, dy in self.exact_pads] for r in range(4)]
        pts = list(self.pads)
        if self.body:
            b = self.body
            pts += [(b[0], b[1]), (b[2], b[1]), (b[2], b[3]), (b[0], b[3])]
        self.bb = []
        for r in range(4):
            rp = [rotpt(x, y, r) for x, y in pts]
            xs = [p[0] for p in rp]
            ys = [p[1] for p in rp]
            self.bb.append((min(xs), min(ys), max(xs), max(ys)))

        self.pin_net = {}
        ref_u = (self.ref or "").strip().upper()
        fp_u = (self.fp or "").strip().upper()
        val_u = (self.value or "").strip().upper()
        self.edge_pref = bool(
            EDGE_COMP_RE.search(ref_u)
            or EDGE_COMP_RE.search(fp_u)
            or EDGE_COMP_RE.search(val_u)
        )
        is_nonpolar_cap = ref_u.startswith("C") and len(self.pads) == 2 and not (
            POLAR_CAP_RE.search(fp_u) or POLAR_CAP_RE.search(val_u)
            or any(str(l).strip() in ("+", "-") for l in labels)
        )
        self.swappable_pins = (len(self.pads) == 2) and (
            bool(NONPOLAR_REF_RE.match(ref_u)) or is_nonpolar_cap
        )

    def rotate_around_center(self, new_rot):
        old_bb = self.bb[self.rot]
        cx = self.x + (old_bb[0] + old_bb[2]) / 2.0
        cy = self.y + (old_bb[1] + old_bb[3]) / 2.0
        self.rot = new_rot % 4
        new_bb = self.bb[self.rot]
        self.x = snap(cx - (new_bb[0] + new_bb[2]) / 2.0)
        self.y = snap(cy - (new_bb[1] + new_bb[3]) / 2.0)

    def label_abs(self):
        if self.label_offset is not None and self.label_rot_ref == self.rot:
            return self.x + self.label_offset[0], self.y + self.label_offset[1]
        bb = self.bb[self.rot]
        return self.x + (bb[0] + bb[2]) / 2.0, self.y + (bb[1] + bb[3]) / 2.0

    def pad_abs(self, i):
        o = self.R[self.rot][i]
        return self.x + o[0], self.y + o[1]

    def pad_exact_abs(self, i):
        if hasattr(self, "R_exact") and self.R_exact and i < len(self.R_exact[self.rot]):
            o = self.R_exact[self.rot][i]
            return self.x + o[0], self.y + o[1]
        return self.pad_abs(i)

    def origin_abs(self):
        ox, oy = getattr(self, "origin", (0.0, 0.0))
        rx, ry = rotpt(ox, oy, self.rot)
        return self.x + rx, self.y + ry

    def is_square_pin(self, i):
        sq = getattr(self, "square_pins", None)
        if sq:
            return i in sq
        return i == 0

    def body_poly(self):
        if not self.body:
            return []
        b = self.body
        pts = [(b[0], b[1]), (b[2], b[1]), (b[2], b[3]), (b[0], b[3])]
        out = []
        for x, y in pts:
            ox, oy = rotpt(x, y, self.rot)
            out.append((self.x + ox, self.y + oy))
        return out


class Net:
    def __init__(self, name, pins):
        self.name, self.pins, self.cls = name, pins, classify(name)


class Design:
    def __init__(self):
        self.comps, self.nets, self.comp_list, self.net_pins = {}, {}, [], {}
        self.W, self.H = 3000, 2000

    def load(self, comps, nets, extra_pins=None, placements=None):
        self.comps, self.nets = {}, {}
        for item in comps:
            ref, fp, val = item[0], item[1] if len(item) > 1 else "", item[2] if len(item) > 2 else ""
            self.comps[ref] = Comp(ref, fp, val)

        labs = {r: [] for r in self.comps}

        if extra_pins:
            for ref, lab in extra_pins:
                if ref not in self.comps:
                    self.comps[ref] = Comp(ref, "")
                    labs[ref] = []
                if lab not in labs[ref]:
                    labs[ref].append(lab)

        for name, pins in nets.items():
            clean_pins = []
            for ref, lab in pins:
                if ref not in self.comps:
                    self.comps[ref] = Comp(ref, "")
                    labs[ref] = []
                if lab not in labs[ref]:
                    labs[ref].append(lab)
                clean_pins.append((ref, lab))

            if len(clean_pins) >= 2:
                self.nets[name] = Net(name, clean_pins)

        for r, c in self.comps.items():
            c.build(labs[r])
        self.comp_list = list(self.comps.values())
        self.net_pins = {}
        for n in self.nets.values():
            lst = []
            for ref, lab in n.pins:
                c = self.comps[ref]
                idx = c.labels[lab]
                lst.append((c, idx))
                c.pin_net[idx] = n.name
            self.net_pins[n.name] = lst
        self.auto_groups()
        self.suggest_board()
        if placements:
            self._apply_initial_placements(placements)

    def _apply_initial_placements(self, placements):
        xs = [v[0] for v in placements.values()]
        ys = [v[1] for v in placements.values()]
        if not xs or not ys:
            return
        min_x, max_x = min(xs), max(xs)
        min_y, max_y = min(ys), max(ys)
        span_x = (max_x - min_x) * MM
        span_y = (max_y - min_y) * MM
        if span_x > 200 and span_y > 200:
            self.W = max(self.W, int(round((span_x + 800) / 50.0)) * 50)
            self.H = max(self.H, int(round((span_y + 800) / 50.0)) * 50)
        for ref, (x_mm, y_mm, rot_deg) in placements.items():
            if ref in self.comps:
                c = self.comps[ref]
                c.x = snap((x_mm - min_x) * MM + 300)
                c.y = snap((max_y - y_mm) * MM + 300)
                c.rot = int(round((rot_deg % 360) / 90.0)) % 4

    def auto_groups(self):
        parent = {c.ref: c.ref for c in self.comp_list}

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        for n in self.nets.values():
            if n.cls == "POWER":
                continue
            refs = list({r for r, _ in n.pins})
            if 2 <= len(refs) <= 4:
                for r in refs[1:]:
                    parent[find(r)] = find(refs[0])
        ids = {}
        for c in self.comp_list:
            root = find(c.ref)
            ids.setdefault(root, "G%d" % (len(ids) + 1))
            c.group = ids[root]

    def suggest_board(self):
        area = 0
        for c in self.comp_list:
            b = c.bb[0]
            area += (b[2] - b[0] + 160) * (b[3] - b[1] + 160)
        side = math.sqrt(max(area, 1) * 2.2)
        self.W = max(600, int(round(side * 1.2 / 50)) * 50)
        self.H = max(600, int(round(side * 0.9 / 50)) * 50)
        x = y = 100
        rowh = 0
        for c in self.comp_list:
            b = c.bb[0]
            w = b[2] - b[0] + 160; h = b[3] - b[1] + 160
            if x + w > self.W - 100:
                x = 100; y += rowh; rowh = 0
            c.x, c.y = snap(x - b[0] + 80), snap(y - b[1] + 80)
            x += w; rowh = max(rowh, h)


def parse_tango(txt):
    lines = [l.strip() for l in txt.splitlines()]
    comps, nets, i = [], {}, 0
    while i < len(lines):
        l = lines[i]
        if l == "[":
            blk = []; i += 1
            while i < len(lines) and lines[i] != "]":
                if lines[i]:
                    blk.append(lines[i])
                i += 1
            if blk:
                comps.append((blk[0], blk[1] if len(blk) > 1 else "", blk[2] if len(blk) > 2 else ""))
        elif l == "(":
            blk = []; i += 1
            while i < len(lines) and lines[i] != ")":
                if lines[i]:
                    blk.append(lines[i])
                i += 1
            if blk:
                pins = []
                for p in blk[1:]:
                    if "," in p:
                        r, k = p.rsplit(",", 1)
                        pins.append((r.strip(), k.strip()))
                    elif "-" in p:
                        r, k = p.rsplit("-", 1)
                        pins.append((r.strip(), k.strip()))
                nets.setdefault(blk[0], []).extend(pins)
        i += 1
    return comps, nets, []


def parse_pads(txt):
    comps, nets, mode, cur = [], {}, None, None
    for line in txt.splitlines():
        s = line.strip()
        u = s.upper()
        if u.startswith("*PART*"):
            mode = "part"; continue
        if u.startswith("*NET*"):
            mode = "net"; continue
        if u.startswith("*SIGNAL*"):
            t = s.split()
            cur = t[1] if len(t) > 1 else "N%d" % len(nets)
            nets.setdefault(cur, []); continue
        if u.startswith("*"):
            continue
        t = s.split()
        if not t:
            continue
        if mode == "part":
            comps.append((t[0], t[1].split("@")[0] if len(t) > 1 else "", ""))
        elif mode == "net" and cur:
            for tok in t:
                if "." in tok:
                    r, k = tok.rsplit(".", 1); nets[cur].append((r, k))
    return comps, nets, []

def parse_proteus_isis_sdf(txt):
    comps = []
    nets = {}
    extra_pins = []
    section = None
    cur_net = None

    for raw_line in txt.splitlines():
        line = raw_line.strip()
        if not line:
            cur_net = None
            continue
        up = line.upper()
        if up.startswith("*PARTLIST"):
            section = "PARTS"
            cur_net = None
            continue
        elif up.startswith("*NETLIST"):
            section = "NETS"
            cur_net = None
            continue
        elif up.startswith("*"):
            section = None
            cur_net = None
            continue

        if section == "PARTS":
            parts = [p.strip() for p in line.split(",")]
            if not parts:
                continue
            ref = parts[0]
            model = parts[1] if len(parts) > 1 else ""
            val = parts[2] if len(parts) > 2 else model
            pkg = ""
            for p in parts[3:]:
                if p.upper().startswith("PACKAGE="):
                    pkg = p.split("=", 1)[1].strip()
                    break
            if not pkg:
                pkg = model
            comps.append((ref, pkg, val))

        elif section == "NETS":
            parts = [p.strip() for p in line.split(",")]
            if len(parts) < 2:
                continue
            if parts[1].isdigit() and (len(parts) == 2 or any(p.upper().startswith("CLASS=") for p in parts[2:])):
                cur_net = parts[0]
                nets.setdefault(cur_net, [])
                continue

            if cur_net is not None:
                if len(parts) == 2 and parts[1].upper() in ("LBL", "PR", " bus"):
                    continue
                if len(parts) >= 3:
                    ref, _ptype, pin_name = parts[0], parts[1], parts[2]
                    nets[cur_net].append((ref, pin_name))
                    extra_pins.append((ref, pin_name))

    return comps, nets, extra_pins


def parse_sdf(txt):
    if "*PARTLIST" in txt.upper() or "ISIS SCHEMATIC DESCRIPTION FORMAT" in txt.upper():
        return parse_proteus_isis_sdf(txt)

    comps, nets = [], {}
    for m in re.finditer(r'\(\s*(?:INSTANCE|COMPONENT)\s+"?([^\s")]+)"?[^()]*?(?:\(\s*(?:TYPE|PACKAGE|FOOTPRINT|PCB)\s+"?([^\s")]+)"?)?', txt, re.I):
        comps.append((m.group(1), m.group(2) or "", ""))
    for m in re.finditer(r'\(\s*NET\s+"?([^\s")]+)"?(.*?)\)\s*(?=\(\s*(?:NET|INSTANCE)|\)\s*\)|$)', txt, re.I | re.S):
        pins = [(a, b) for a, b in re.findall(r'\(\s*(?:NODE|PIN)\s+"?([^\s")]+)"?\s+"?([^\s")]+)"?\s*\)', m.group(2), re.I)]
        if not pins:
            pins = [tuple(t.rsplit("-", 1)) for t in re.findall(r'[A-Za-z]+\d+-\w+', m.group(2))]
        if pins:
            nets.setdefault(m.group(1), []).extend(pins)
    return comps, nets, []


def _sexpr_parse(txt):
    txt_clean = re.sub(r";[^\n]*", "", txt)
    toks = re.findall(r'(?:"[^"]*"|[^\s()"]+)+|[()]', txt_clean)
    stack, cur = [], []
    for t in toks:
        if t == "(":
            stack.append(cur); cur = []
        elif t == ")":
            if stack:
                node = cur; cur = stack.pop(); cur.append(node)
        else:
            cur.append(t[1:-1] if (t.startswith('"') and t.endswith('"') and '"' not in t[1:-1]) else t)
    return cur[0] if len(cur) == 1 else cur


def parse_proteus_edf_dsn(txt, auto_save_db=True):
    root = _sexpr_parse(txt)
    if not isinstance(root, list):
        return [], {}, [], {}

    def find_sections(node, head):
        out = []
        if isinstance(node, list) and node:
            if str(node[0]).lower() == head:
                out.append(node)
            for sub in node[1:]:
                if isinstance(sub, list):
                    out.extend(find_sections(sub, head))
        return out

    comp_defs = []
    placements = {}
    img_to_refs = {}
    for pl in find_sections(root, "placement"):
        for cnode in pl[1:]:
            if isinstance(cnode, list) and len(cnode) >= 3 and str(cnode[0]).lower() == "component":
                img_name = str(cnode[1])
                for pnode in cnode[2:]:
                    if isinstance(pnode, list) and len(pnode) >= 4 and str(pnode[0]).lower() == "place":
                        ref = str(pnode[1])
                        try:
                            x_mm = float(pnode[2])
                            y_mm = float(pnode[3])
                        except ValueError:
                            x_mm = y_mm = 0.0
                        rot = 0.0
                        for tok in pnode[4:]:
                            try:
                                rot = float(tok)
                                break
                            except (ValueError, TypeError):
                                pass
                        fp_name = img_name
                        if img_name.endswith("_" + ref):
                            fp_name = img_name[:-(len(ref) + 1)]
                        comp_defs.append((ref, fp_name, fp_name))
                        placements[ref] = (x_mm, y_mm, rot)
                        img_to_refs.setdefault(img_name, []).append((ref, fp_name))

    extra_pins = []
    for lib in find_sections(root, "library"):
        rect_ps_names = set()
        for ps in find_sections(lib, "padstack"):
            if len(ps) >= 2 and (find_sections(ps, "rect") or find_sections(ps, "square")):
                rect_ps_names.add(str(ps[1]).strip())

        for img in lib[1:]:
            if isinstance(img, list) and len(img) >= 2 and str(img[0]).lower() == "image":
                img_name = str(img[1])
                raw_pins = []
                outline_pts = []
                for item in img[2:]:
                    if isinstance(item, list) and item:
                        tag = str(item[0]).lower()
                        if tag == "pin":

                            flat_toks = [x for x in item[1:] if not isinstance(x, list)]
                            if len(flat_toks) >= 4:
                                ps_name = str(flat_toks[0]).strip()
                                pid = str(flat_toks[-3])
                                try:
                                    px_mm = float(flat_toks[-2])
                                    py_mm = float(flat_toks[-1])
                                    raw_pins.append((pid, px_mm * MM, -py_mm * MM, ps_name))
                                except ValueError:
                                    pass
                        elif tag == "outline":
                            for sub in item[1:]:
                                if isinstance(sub, list) and len(sub) >= 6 and str(sub[0]).lower() == "rect":
                                    try:
                                        x0, y0, x1, y1 = float(sub[2]) * MM, -float(sub[3]) * MM, float(sub[4]) * MM, -float(sub[5]) * MM
                                        outline_pts.extend([(x0, y0), (x1, y1)])
                                    except ValueError:
                                        pass
                if raw_pins:
                    min_x = min(p[1] for p in raw_pins)
                    min_y = min(p[2] for p in raw_pins)
                    pads_snapped = _snap_pads_distinct([(p[1], p[2]) for p in raw_pins])
                    exact_pads = [(round(p[1] - min_x, 2), round(p[2] - min_y, 2)) for p in raw_pins]
                    origin = (round(-min_x, 2), round(-min_y, 2))
                    square_pins = [idx for idx, p in enumerate(raw_pins) if p[3] in rect_ps_names]
                    if not square_pins:
                        square_pins = [0]
                    if outline_pts:
                        bx0 = int(round(min(p[0] for p in outline_pts) - min_x))
                        by0 = int(round(min(p[1] for p in outline_pts) - min_y))
                        bx1 = int(round(max(p[0] for p in outline_pts) - min_x))
                        by1 = int(round(max(p[1] for p in outline_pts) - min_y))
                        body = (bx0, by0, bx1, by1)
                    else:
                        xs = [p[0] for p in pads_snapped]
                        ys = [p[1] for p in pads_snapped]
                        body = (min(xs) - 50, min(ys) - 50, max(xs) + 50, max(ys) + 50)
                    pin_map = {}
                    for idx, (pid, _, _, _) in enumerate(raw_pins):
                        pin_map["EDF_" + pid] = idx
                        if not pid.isdigit():
                            pin_map[pid] = idx
                    target_names = {img_name}
                    for ref, fp_name in img_to_refs.get(img_name, []):
                        target_names.add(fp_name)
                        for pid, _, _, _ in raw_pins:
                            extra_pins.append((ref, "EDF_" + pid))
                    for tname in target_names:
                        FOOTPRINT_DB.register(
                            tname, pads_snapped, body, pin_map=pin_map,
                            desc="Học tự động từ Proteus ARES EDF/DSN",
                            save_now=False, exact_pads=exact_pads,
                            origin=origin, square_pins=square_pins, source="edf"
                        )
    if auto_save_db:
        FOOTPRINT_DB.save()

    nets = {}
    for net_sec in find_sections(root, "network"):
        for nnode in net_sec[1:]:
            if isinstance(nnode, list) and len(nnode) >= 2 and str(nnode[0]).lower() == "net":
                net_name = str(nnode[1])
                pins = []
                for sub in nnode[2:]:
                    if isinstance(sub, list) and sub and str(sub[0]).lower() == "pins":
                        for tok in sub[1:]:
                            if isinstance(tok, str) and "-" in tok:
                                r, p = tok.rsplit("-", 1)
                                pins.append((r.strip('"'), "EDF_" + p.strip('"')))
                if pins:
                    nets.setdefault(net_name, []).extend(pins)

    return comp_defs, nets, extra_pins, placements


def learn_footprints_from_sdf_and_edf(sdf_path, edf_path):
    with open(edf_path, "r", encoding="utf-8", errors="ignore") as f:
        edf_txt = f.read()
    edf_comps, edf_nets, _, _ = parse_proteus_edf_dsn(edf_txt, auto_save_db=False)

    learned_count = len(edf_comps)
    if sdf_path and os.path.isfile(sdf_path):
        with open(sdf_path, "r", encoding="utf-8", errors="ignore") as f:
            sdf_txt = f.read()
        sdf_comps, sdf_nets, _ = parse_sdf(sdf_txt)
        ref_to_fp = {r: fp for r, fp, _ in sdf_comps}

        for net_name, sdf_pins in sdf_nets.items():
            edf_pins = edf_nets.get(net_name, [])
            if not edf_pins:
                continue
            sdf_by_ref = {}
            for r, p in sdf_pins:
                sdf_by_ref.setdefault(r, []).append(p)
            edf_by_ref = {}
            for r, p in edf_pins:
                edf_by_ref.setdefault(r, []).append(p)
            for ref in set(sdf_by_ref) & set(edf_by_ref):
                if len(sdf_by_ref[ref]) == 1 and len(edf_by_ref[ref]) == 1:
                    sdf_pin = str(sdf_by_ref[ref][0])
                    edf_pin = str(edf_by_ref[ref][0])
                    fp_name = ref_to_fp.get(ref, "")
                    entry = FOOTPRINT_DB.get(fp_name)
                    if entry and "pin_map" in entry:
                        idx = entry["pin_map"].get(edf_pin.upper())
                        if idx is not None:
                            entry["pin_map"][sdf_pin.upper()] = idx
    FOOTPRINT_DB.save()
    return learned_count


def parse_snapeda_pdif(txt, save_now=True):
    root = _sexpr_parse(txt)
    if not isinstance(root, list) or not root or str(root[0]).upper() != "PDIF":
        return 0

    def find_nodes(node, head):
        out = []
        if isinstance(node, list) and node:
            if str(node[0]).lower() == head:
                out.append(node)
            for sub in node[1:]:
                if isinstance(sub, list):
                    out.extend(find_nodes(sub, head))
        return out


    pkg_to_parts = {}
    pkg_to_desc = {}
    pkg_pin_aliases = {}

    for pnode in find_nodes(root, "part"):
        if len(pnode) < 2:
            continue
        part_name = str(pnode[1]).strip()
        pkg_name = ""
        desc = ""
        aliases = {part_name}
        leg_labels = {}

        for sub in pnode[2:]:
            if not isinstance(sub, list) or not sub:
                continue
            tag = str(sub[0]).lower()
            if tag == "package" and len(sub) >= 2:
                pkg_name = str(sub[1]).strip()
            elif tag == "description" and len(sub) >= 2:
                desc = str(sub[1]).replace("_", " ").strip()
            elif tag == "attribute" and len(sub) >= 3:
                attr_k = str(sub[1]).upper()
                attr_v = str(sub[2]).strip()
                if attr_k == "PKG_TYPE" and attr_v and not pkg_name:
                    pkg_name = attr_v
                elif attr_k == "MP" and attr_v:
                    aliases.add(attr_v)
            elif tag == "gate":
                for gsub in sub[1:]:
                    if isinstance(gsub, list) and len(gsub) >= 3 and str(gsub[0]).lower() == "pin":
                        pin_label = str(gsub[1]).strip()
                        leg_id = str(gsub[2]).strip()
                        leg_labels.setdefault(leg_id.upper(), set()).add(pin_label.upper())

        if not pkg_name:
            pkg_name = part_name
        pk_norm = FootprintLibrary.norm_key(pkg_name)
        pkg_to_parts.setdefault(pk_norm, set()).update(aliases)
        if desc:
            pkg_to_desc[pk_norm] = desc
        if leg_labels:
            amap = pkg_pin_aliases.setdefault(pk_norm, {})
            for lid, lset in leg_labels.items():
                amap.setdefault(lid, set()).update(lset)


    count = 0
    for pkg in find_nodes(root, "package"):
        if len(pkg) <= 2:
            continue
        pkg_name = str(pkg[1]).strip()
        pk_norm = FootprintLibrary.norm_key(pkg_name)
        scale = 1.0
        raw_legs = []
        outline_pts = []
        square_ps_ids = set()

        for ps_node in find_nodes(pkg, "padstack"):
            if len(ps_node) >= 3:
                ps_id = str(ps_node[1]).strip()
                if find_nodes(ps_node, "square") or find_nodes(ps_node, "rect"):
                    square_ps_ids.add(ps_id)

        for item in pkg[2:]:
            if not isinstance(item, list) or not item:
                continue
            tag = str(item[0]).lower()
            if tag == "units" and len(item) >= 2:
                u = str(item[1]).upper()
                scale = MM if u == "MM" else 1.0
            elif tag == "leg" and len(item) >= 3:
                leg_id = str(item[1]).strip()
                leg_ps = ""
                px = py = None
                for sub in item[2:]:
                    if isinstance(sub, list) and sub:
                        stag = str(sub[0]).lower()
                        if stag == "pt" and len(sub) >= 3 and px is None:
                            try:
                                px = float(sub[1]) * scale
                                py = -float(sub[2]) * scale
                            except ValueError:
                                pass
                        elif stag == "padstack" and len(sub) >= 2:
                            leg_ps = str(sub[1]).strip()
                if px is not None and py is not None:
                    raw_legs.append((leg_id, px, py, leg_ps))
            elif tag == "layer" and len(item) >= 2:
                lname = str(item[1]).upper()
                if lname in ("TSLK", "TASM", "OCCA"):
                    for pt_node in find_nodes(item, "pt"):
                        if len(pt_node) >= 3:
                            try:
                                ox = float(pt_node[1]) * scale
                                oy = -float(pt_node[2]) * scale
                                outline_pts.append((ox, oy))
                            except ValueError:
                                pass

        if not raw_legs:
            continue

        min_x = min(p[1] for p in raw_legs)
        min_y = min(p[2] for p in raw_legs)
        pads_snapped = _snap_pads_distinct([(p[1], p[2]) for p in raw_legs])
        exact_pads = [(round(p[1] - min_x, 2), round(p[2] - min_y, 2)) for p in raw_legs]
        origin = (round(-min_x, 2), round(-min_y, 2))
        if outline_pts:
            bx0 = int(round(min(p[0] for p in outline_pts) - min_x))
            by0 = int(round(min(p[1] for p in outline_pts) - min_y))
            bx1 = int(round(max(p[0] for p in outline_pts) - min_x))
            by1 = int(round(max(p[1] for p in outline_pts) - min_y))
            body = (bx0, by0, bx1, by1)
        else:
            xs = [p[0] for p in pads_snapped]
            ys = [p[1] for p in pads_snapped]
            body = (min(xs) - 50, min(ys) - 50, max(xs) + 50, max(ys) + 50)

        pin_map = {}
        alias_map = pkg_pin_aliases.get(pk_norm, {})
        square_pins = []
        for idx, (leg_id, _, _, leg_ps) in enumerate(raw_legs):
            lid_up = leg_id.upper()
            pin_map[lid_up] = idx
            for lbl_up in alias_map.get(lid_up, ()):
                pin_map[lbl_up] = idx
            if leg_ps and leg_ps in square_ps_ids:
                square_pins.append(idx)
        if not square_pins:
            for idx, (leg_id, _, _, _) in enumerate(raw_legs):
                lid_up = leg_id.upper()
                lbls = {lid_up} | set(alias_map.get(lid_up, ()))
                if lbls & {"1", "A", "+", "VCC", "3_3", "3V3"}:
                    square_pins.append(idx)
                    break
        if not square_pins:
            square_pins = [0]

        desc = pkg_to_desc.get(pk_norm, "SnapEDA PDIF (" + pkg_name + ")")
        all_names = {pkg_name} | pkg_to_parts.get(pk_norm, set())
        for name_key in all_names:
            FOOTPRINT_DB.register(
                name_key, pads_snapped, body, pin_map=pin_map, desc=desc,
                save_now=False, exact_pads=exact_pads, origin=origin,
                square_pins=square_pins, source="pdif"
            )
        count += 1

    if count and save_now:
        FOOTPRINT_DB.save()
    return count


def import_snapeda_file(path, save_now=True, use_cache=False):
    ext = os.path.splitext(path)[1].lower()
    total = 0
    try:
        st = os.stat(path)
        if ext == ".zip" and st.st_size > 2 * 1024 * 1024:
            return 0
        norm_p = os.path.normcase(os.path.abspath(path))
        cache = FOOTPRINT_DB.db.setdefault("_SCANNED_FILES", {})
        sig = f"{int(st.st_mtime)}:{st.st_size}"
        if use_cache and isinstance(cache, dict) and cache.get(norm_p) == sig:
            return 0

        if ext == ".pdif":
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                total += parse_snapeda_pdif(f.read(), save_now=False)
        elif ext == ".zip" and zipfile.is_zipfile(path):
            with zipfile.ZipFile(path, "r") as zf:
                for name in zf.namelist():
                    if name.lower().endswith(".pdif"):
                        raw = zf.read(name).decode("utf-8", errors="ignore")
                        total += parse_snapeda_pdif(raw, save_now=False)
        elif ext in (".edf", ".dsn"):
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                comps, _, _, _ = parse_proteus_edf_dsn(f.read(), auto_save_db=False)
                total += len(comps)

        if isinstance(cache, dict):
            cache[norm_p] = sig
    except Exception:
        pass
    if total and save_now:
        FOOTPRINT_DB.save()
    return total


def scan_snapeda_folder(folder_path, recursive=True, save_now=True, use_cache=False, max_depth=2):
    if not folder_path or not os.path.isdir(folder_path):
        return 0
    total = 0
    base_depth = folder_path.rstrip("\\/").count(os.sep)
    cache_before = len(FOOTPRINT_DB.db.get("_SCANNED_FILES", {}))
    try:
        if recursive:
            for root_dir, dirs, files in os.walk(folder_path):
                cur_depth = root_dir.rstrip("\\/").count(os.sep) - base_depth
                if cur_depth >= max_depth:
                    dirs[:] = []
                for fn in files:
                    low = fn.lower()
                    if low.endswith(".pdif") or low.endswith(".zip"):
                        total += import_snapeda_file(os.path.join(root_dir, fn), save_now=False, use_cache=use_cache)
        else:
            for fn in os.listdir(folder_path):
                low = fn.lower()
                if low.endswith(".pdif") or low.endswith(".zip"):
                    total += import_snapeda_file(os.path.join(folder_path, fn), save_now=False, use_cache=use_cache)
    except Exception:
        pass
    cache_after = len(FOOTPRINT_DB.db.get("_SCANNED_FILES", {}))
    if (total or cache_after != cache_before) and save_now:
        FOOTPRINT_DB.save()
    return total


def auto_sync_snapeda_dirs(extra_dirs=None):
    cand_dirs = [
        os.path.dirname(os.path.abspath(__file__)),
        r"D:\Downloads",
        os.path.join(os.path.expanduser("~"), "Downloads"),
    ]
    if extra_dirs:
        cand_dirs.extend(extra_dirs)
    seen = set()
    total = 0
    cache_before = len(FOOTPRINT_DB.db.get("_SCANNED_FILES", {}))
    for d in cand_dirs:
        if not d:
            continue
        nd = os.path.normcase(os.path.abspath(d))
        if nd in seen or not os.path.isdir(d):
            continue
        seen.add(nd)
        total += scan_snapeda_folder(d, recursive=True, save_now=False, use_cache=True, max_depth=2)
    cache_after = len(FOOTPRINT_DB.db.get("_SCANNED_FILES", {}))
    if total or cache_after != cache_before:
        FOOTPRINT_DB.save()
    return total

auto_sync_snapeda_dirs()


def parse_netlist(path):
    netlist_dir = os.path.dirname(os.path.abspath(path))
    scan_snapeda_folder(netlist_dir, recursive=False, save_now=True)

    with open(path, "r", encoding="utf-8", errors="ignore") as f:
        txt = f.read()
    up = txt.upper()

    if up.lstrip().startswith("(PCB") or ("(HOST_CAD ARES)" in up and "(LIBRARY" in up):
        comps, nets, extra_pins, placements = parse_proteus_edf_dsn(txt, auto_save_db=True)
        if comps or nets:
            return comps, nets, extra_pins, placements
    if "*PARTLIST" in up or "ISIS SCHEMATIC DESCRIPTION FORMAT" in up:
        base, _ = os.path.splitext(path)
        for ext in (".EDF", ".edf", ".DSN", ".dsn"):
            cand_edf = base + ext
            if os.path.isfile(cand_edf):
                try:
                    learn_footprints_from_sdf_and_edf(path, cand_edf)
                except Exception:
                    pass
                break
        comps, nets, extra_pins = parse_proteus_isis_sdf(txt)
        if comps or nets:
            return comps, nets, extra_pins, None

    if "*SIGNAL*" in up or "*PADS" in up:
        comps, nets, extra_pins = parse_pads(txt)
        return comps, nets, extra_pins, None

    if re.search(r"^\s*\[\s*$", txt, re.M):
        comps, nets, extra_pins = parse_tango(txt)
        if comps or nets:
            return comps, nets, extra_pins, None

    comps, nets, extra_pins = parse_sdf(txt)
    if not comps and not nets:
        raise ValueError(
            "Không nhận dạng được netlist. Hiện hỗ trợ:\n"
            "- Proteus ISIS Schematic (.SDF / .TXT)\n"
            "- Proteus ARES Specctra (.EDF / .DSN)\n"
            "- PADS ASCII / Tango Netlist"
        )
    return comps, nets, extra_pins, None


def demo_design():
    comps = [("U1", "DIP8", "NE555"), ("R1", "RES40", "10k"), ("R2", "RES40", "47k"),
             ("R3", "RES40", "470"), ("R4", "RES40", "1k"), ("C1", "CAP10", "10u"),
             ("C2", "CAP10", "10n"), ("C3", "CAP10", "100n"), ("D1", "LED", "LED"),
             ("Q1", "TO92", "2N2222"), ("J1", "HEADER2", "PWR"), ("J2", "HEADER2", "LOAD")]
    nets = {
        "GND": [("U1", "1"), ("C1", "2"), ("C2", "2"), ("C3", "2"), ("D1", "2"), ("Q1", "3"), ("J1", "2")],
        "VCC": [("U1", "8"), ("U1", "4"), ("R1", "1"), ("C3", "1"), ("J1", "1"), ("J2", "1")],
        "DIS": [("U1", "7"), ("R1", "2"), ("R2", "1")],
        "TH": [("U1", "6"), ("U1", "2"), ("R2", "2"), ("C1", "1")],
        "CTRL": [("U1", "5"), ("C2", "1")],
        "OUT": [("U1", "3"), ("R3", "1"), ("R4", "1")],
        "LEDA": [("R3", "2"), ("D1", "1")],
        "BASE": [("R4", "2"), ("Q1", "2")],
        "LOAD": [("Q1", "1"), ("J2", "2")],
    }
    d = Design(); d.load(comps, nets)
    return d

def ratsnest(d):
    E = []
    for name, pins in d.net_pins.items():
        pts = list(dict.fromkeys(c.pad_abs(i) for c, i in pins))
        if len(pts) < 2:
            continue
        tree, rest = [pts[0]], pts[1:]
        while rest:
            best = None
            for a in rest:
                for b in tree:
                    dd = abs(a[0] - b[0]) + abs(a[1] - b[1])
                    if best is None or dd < best[0]:
                        best = (dd, a, b)
            E.append((name, best[2], best[1])); tree.append(best[1]); rest.remove(best[1])
    return E


def _ccw(a, b, c):
    return (c[1] - a[1]) * (b[0] - a[0]) - (b[1] - a[1]) * (c[0] - a[0])


def count_cross(E):
    n = 0
    for i in range(len(E)):
        ni, p1, p2 = E[i]
        for j in range(i + 1, len(E)):
            nj, q1, q2 = E[j]
            if ni == nj or p1 in (q1, q2) or p2 in (q1, q2):
                continue
            if _ccw(p1, p2, q1) * _ccw(p1, p2, q2) < 0 and _ccw(q1, q2, p1) * _ccw(q1, q2, p2) < 0:
                n += 1
    return n

def auto_place_silkscreen(d, res=None):
    if not d or not d.comp_list:
        return
    all_pads = []
    for c in d.comp_list:
        for i in range(len(c.pads)):
            px, py = c.pad_exact_abs(i)
            all_pads.append((px, py, PAD_D / 2.0 + 14.0))
    if res:
        for vx, vy, _n in getattr(res, "vias", []):
            all_pads.append((vx, vy, VIA_D / 2.0 + 12.0))
        for _n, a, b in getattr(res, "jumps", []):
            all_pads.append((a[0], a[1], VIA_D / 2.0 + 12.0))
            all_pads.append((b[0], b[1], VIA_D / 2.0 + 12.0))

    placed_labels = []
    for c in d.comp_list:
        bb = c.bb[c.rot]
        bx0, by0, bx1, by1 = c.x + bb[0], c.y + bb[1], c.x + bb[2], c.y + bb[3]
        bcx, bcy = (bx0 + bx1) / 2.0, (by0 + by1) / 2.0
        tw = max(85.0, len(c.ref) * 52.0)
        th = 72.0
        pad_m = 24.0

        cands = [
            (bcx, by0 - th * 0.55 - pad_m, 0.0),
            (bcx, by1 + th * 0.55 + pad_m, 2.0),
            (bx0 - tw * 0.55 - pad_m, bcy, 4.0),
            (bx1 + tw * 0.55 + pad_m, bcy, 4.0),
            (bcx, bcy, 8.0 if (bx1 - bx0 > tw + 60 and by1 - by0 > th + 60) else 45.0),
            (bx0, by0 - th * 0.55 - pad_m, 10.0),
            (bx1, by0 - th * 0.55 - pad_m, 10.0),
            (bx0, by1 + th * 0.55 + pad_m, 12.0),
            (bx1, by1 + th * 0.55 + pad_m, 12.0),
        ]

        best = None
        for lx, ly, base_pen in cands:
            tx0, ty0, tx1, ty1 = lx - tw / 2.0, ly - th / 2.0, lx + tw / 2.0, ly + th / 2.0
            pen = base_pen
            if tx0 < 25 or ty0 < 25 or tx1 > d.W - 25 or ty1 > d.H - 25:
                pen += 5000.0
            for px, py, pr in all_pads:
                if (tx0 - pr <= px <= tx1 + pr) and (ty0 - pr <= py <= ty1 + pr):
                    ox = min(tx1, px + pr) - max(tx0, px - pr)
                    oy = min(ty1, py + pr) - max(ty0, py - pr)
                    if ox > 0 and oy > 0:
                        pen += 1500.0 + ox * oy * 0.5
            for ox0, oy0, ox1, oy1 in placed_labels:
                ix = min(tx1, ox1) - max(tx0, ox0)
                iy = min(ty1, oy1) - max(ty0, oy0)
                if ix > 0 and iy > 0:
                    pen += 900.0 + ix * iy * 0.4
            for o in d.comp_list:
                if o is c:
                    continue
                obb = o.bb[o.rot]
                obx0, oby0, obx1, oby1 = o.x + obb[0], o.y + obb[1], o.x + obb[2], o.y + obb[3]
                ix = min(tx1, obx1) - max(tx0, obx0)
                iy = min(ty1, oby1) - max(ty0, oby0)
                if ix > 0 and iy > 0:
                    pen += 220.0
            if best is None or pen < best[0]:
                best = (pen, lx, ly, (tx0, ty0, tx1, ty1))

        _, best_lx, best_ly, best_box = best
        c.label_offset = (best_lx - c.x, best_ly - c.y)
        c.label_rot_ref = c.rot
        placed_labels.append(best_box)

OV_W, OUT_W, CL_W, EDGE_W, DECOUP_W = 0.32, 25.0, 0.25, 0.85, 0.80

class Placer:
    def __init__(self, d, P, cancel):
        self.d, self.P, self.cancel = d, P, cancel
        self.W, self.H = d.W, d.H
        self.m = P["solder_mm"] * MM / 2.0
        self.E = P["edge_mm"] * MM
        self.comps = d.comp_list
        self.use_cluster = P.get("cluster", True)
        self.use_force = P.get("force_init", True)
        self.use_edge = P.get("edge_constraint", True)
        self.use_decouple = P.get("decouple_pair", True)
        self.use_pinswap = P.get("pin_swap", True)
        self.iters = P.get("sa_iters", 15000)
        self.cnets = {c.ref: [] for c in self.comps}
        for name, pins in d.net_pins.items():
            wt = 0.4 if d.nets[name].cls == "POWER" else 1.0
            seen = set()
            for c, i in pins:
                if c.ref not in seen:
                    seen.add(c.ref); self.cnets[c.ref].append((name, wt))
        self.groups = {}
        for c in self.comps:
            self.groups.setdefault(c.group, []).append(c)

        self.decouple_map = {}
        self.ic_decouple = {}
        if self.use_decouple:
            self._detect_decouple_pairs()

    def _detect_decouple_pairs(self):
        ics = [c for c in self.comps if IC_REF_RE.match(c.ref) or len(c.pads) >= 6]
        if not ics:
            return
        caps = [c for c in self.comps if c.ref.upper().startswith("C") and len(c.pads) == 2]
        for cap in caps:
            n0 = cap.pin_net.get(0)
            n1 = cap.pin_net.get(1)
            if not n0 and not n1:
                continue
            is_bypass_val = bool(BYPASS_VAL_RE.search(cap.value or ""))
            has_gnd = bool((n0 and GND_RE.match(n0)) or (n1 and GND_RE.match(n1)))
            has_pwr = bool((n0 and self.d.nets.get(n0) and self.d.nets[n0].cls == "POWER") or
                           (n1 and self.d.nets.get(n1) and self.d.nets[n1].cls == "POWER"))
            if not (has_pwr or is_bypass_val):
                continue
            best_pair = None
            for ic in ics:
                for ic_pin, ic_net in ic.pin_net.items():
                    if not ic_net:
                        continue
                    for cap_pin, cap_net in ((0, n0), (1, n1)):
                        if cap_net == ic_net:
                            score = 0 if GND_RE.match(ic_net) else (3 if self.d.nets[ic_net].cls != "POWER" else 2)
                            if best_pair is None or score > best_pair[0]:
                                best_pair = (score, ic, ic_pin, cap_pin)
            if best_pair and best_pair[0] > 0:
                _, ic, ic_pin, cap_pin = best_pair
                self.decouple_map[cap.ref] = (ic, ic_pin, cap_pin)
                self.ic_decouple.setdefault(ic.ref, []).append((cap, ic_pin, cap_pin))

    def hp(self, name):
        pins = self.d.net_pins[name]
        if len(pins) < 2:
            return 0
        x0 = y0 = 1e9; x1 = y1 = -1e9
        for c, i in pins:
            o = c.R[c.rot][i]; x = c.x + o[0]; y = c.y + o[1]
            if x < x0: x0 = x
            if x > x1: x1 = x
            if y < y0: y0 = y
            if y > y1: y1 = y
        return (x1 - x0) + (y1 - y0)

    def out_of_board(self, c):
        bb = c.bb[c.rot]; e = PAD_D / 2.0; E = self.E
        return (max(0, E - (c.x + bb[0] - e)) + max(0, (c.x + bb[2] + e) - (self.W - E)) +
                max(0, E - (c.y + bb[1] - e)) + max(0, (c.y + bb[3] + e) - (self.H - E)))

    def inside(self, c):
        return self.out_of_board(c) < 0.5

    def rect(self, c):
        bb = c.bb[c.rot]; e = PAD_D / 2.0 + self.m
        return c.x + bb[0] - e, c.y + bb[1] - e, c.x + bb[2] + e, c.y + bb[3] + e

    def overlap(self, c):
        a = self.rect(c)
        for o in self.comps:
            if o is c:
                continue
            b = self.rect(o)
            if min(a[2], b[2]) - max(a[0], b[0]) > 0.5 and min(a[3], b[3]) - max(a[1], b[1]) > 0.5:
                return True
        return False

    def legal(self):
        return all(self.inside(c) and not self.overlap(c) for c in self.comps)

    def center(self, c):
        bb = c.bb[c.rot]
        return c.x + (bb[0] + bb[2]) / 2.0, c.y + (bb[1] + bb[3]) / 2.0

    def edge_dist(self, c):
        bb = c.bb[c.rot]; e = PAD_D / 2.0; E = self.E
        d_left = max(0.0, (c.x + bb[0] - e) - E)
        d_right = max(0.0, (self.W - E) - (c.x + bb[2] + e))
        d_top = max(0.0, (c.y + bb[1] - e) - E)
        d_bot = max(0.0, (self.H - E) - (c.y + bb[3] + e))
        return min(d_left, d_right, d_top, d_bot)

    def local(self, c):
        cost = 0.0
        for name, wt in self.cnets[c.ref]:
            cost += wt * self.hp(name)
        a = self.rect(c)
        for o in self.comps:
            if o is c:
                continue
            b = self.rect(o)
            ox = min(a[2], b[2]) - max(a[0], b[0])
            if ox > 0:
                oy = min(a[3], b[3]) - max(a[1], b[1])
                if oy > 0:
                    cost += OV_W * ox * oy
        cost += OUT_W * self.out_of_board(c)
        if self.use_cluster:
            g = self.groups[c.group]
            if len(g) > 1:
                sx = sy = 0.0
                for o in g:
                    if o is not c:
                        cx, cy = self.center(o); sx += cx; sy += cy
                sx /= (len(g) - 1); sy /= (len(g) - 1)
                cx, cy = self.center(c)
                cost += CL_W * (abs(cx - sx) + abs(cy - sy))
        if self.use_edge and getattr(c, "edge_pref", False):
            cost += EDGE_W * max(0.0, self.edge_dist(c) - 100.0)
        if self.use_decouple:
            if c.ref in self.decouple_map:
                ic, ic_pin, cap_pin = self.decouple_map[c.ref]
                ix, iy = ic.pad_abs(ic_pin)
                px, py = c.pad_abs(cap_pin)
                cost += DECOUP_W * max(0.0, abs(px - ix) + abs(py - iy) - 150.0)
            if c.ref in self.ic_decouple:
                for cap, ic_pin, cap_pin in self.ic_decouple[c.ref]:
                    ix, iy = c.pad_abs(ic_pin)
                    px, py = cap.pad_abs(cap_pin)
                    cost += DECOUP_W * max(0.0, abs(px - ix) + abs(py - iy) - 150.0)
        return cost

    def clamp(self, c):
        bb = c.bb[c.rot]; e = PAD_D / 2.0
        minx = self.E + e - bb[0]; maxx = self.W - self.E - e - bb[2]
        miny = self.E + e - bb[1]; maxy = self.H - self.E - e - bb[3]
        if maxx < minx: maxx = minx
        if maxy < miny: maxy = miny
        x = snap(min(max(c.x, minx), maxx)); y = snap(min(max(c.y, miny), maxy))
        if x < minx: x += GRID
        if x > maxx: x -= GRID
        if y < miny: y += GRID
        if y > maxy: y -= GRID
        c.x, c.y = x, y

    def force_directed_init(self, mov):
        for c in mov:
            c.rot = random.randrange(4)
            c.x = random.randint(int(self.W * 0.15), int(self.W * 0.85))
            c.y = random.randint(int(self.H * 0.15), int(self.H * 0.85))
            self.clamp(c)

        steps = 45
        for step in range(steps):
            if self.cancel.is_set():
                break
            alpha = 0.42 * (1.0 - step / float(steps + 5))
            fx_map = {c.ref: 0.0 for c in mov}
            fy_map = {c.ref: 0.0 for c in mov}

            for name, pins in self.d.net_pins.items():
                if len(pins) < 2:
                    continue
                wt = (0.35 if self.d.nets[name].cls == "POWER" else 1.2) / max(1.0, len(pins) - 1.0)
                mx = sum(c.pad_abs(i)[0] for c, i in pins) / float(len(pins))
                my = sum(c.pad_abs(i)[1] for c, i in pins) / float(len(pins))
                for c, i in pins:
                    if c.fixed:
                        continue
                    px, py = c.pad_abs(i)
                    fx_map[c.ref] += wt * (mx - px)
                    fy_map[c.ref] += wt * (my - py)

            if self.use_decouple:
                for cap_ref, (ic, ic_pin, cap_pin) in self.decouple_map.items():
                    cap = self.d.comps[cap_ref]
                    if not cap.fixed:
                        ix, iy = ic.pad_abs(ic_pin)
                        px, py = cap.pad_abs(cap_pin)
                        fx_map[cap.ref] += 1.6 * (ix - px)
                        fy_map[cap.ref] += 1.6 * (iy - py)

            for i in range(len( self.comps )):
                c1 = self.comps[i]
                r1 = self.rect(c1)
                c1x, c1y = (r1[0] + r1[2]) * 0.5, (r1[1] + r1[3]) * 0.5
                w1, h1 = r1[2] - r1[0], r1[3] - r1[1]
                for j in range(i + 1, len(self.comps)):
                    c2 = self.comps[j]
                    r2 = self.rect(c2)
                    c2x, c2y = (r2[0] + r2[2]) * 0.5, (r2[1] + r2[3]) * 0.5
                    w2, h2 = r2[2] - r2[0], r2[3] - r2[1]
                    dx, dy = c1x - c2x, c1y - c2y
                    ox = (w1 + w2) * 0.55 - abs(dx)
                    oy = (h1 + h2) * 0.55 - abs(dy)
                    if ox > 0 and oy > 0:
                        if abs(dx) < 1.0 and abs(dy) < 1.0:
                            dx, dy = random.uniform(-10, 10), random.uniform(-10, 10)
                        dist = math.hypot(dx, dy) or 1.0
                        rep = min(600.0, (ox * oy) * 0.04 + 90.0)
                        rx, ry = (dx / dist) * rep, (dy / dist) * rep
                        if not c1.fixed:
                            fx_map[c1.ref] += rx; fy_map[c1.ref] += ry
                        if not c2.fixed:
                            fx_map[c2.ref] -= rx; fy_map[c2.ref] -= ry

            if self.use_edge:
                for c in mov:
                    if getattr(c, "edge_pref", False):
                        cx, cy = self.center(c)
                        dists = [
                            (cx - self.E, -1.0, 0.0),
                            (self.W - self.E - cx, 1.0, 0.0),
                            (cy - self.E, 0.0, -1.0),
                            (self.H - self.E - cy, 0.0, 1.0),
                        ]
                        d_min, ux, uy = min(dists, key=lambda t: t[0])
                        fx_map[c.ref] += ux * d_min * 1.35
                        fy_map[c.ref] += uy * d_min * 1.35

            for c in mov:
                dx = max(-350.0, min(350.0, fx_map[c.ref] * alpha))
                dy = max(-350.0, min(350.0, fy_map[c.ref] * alpha))
                c.x = snap(c.x + dx)
                c.y = snap(c.y + dy)
                self.clamp(c)

    def run(self, warm, T0scale=1.0):
        mov = [c for c in self.comps if not c.fixed]
        if not mov:
            return
        if not warm:
            if self.use_force:
                self.force_directed_init(mov)
            else:
                for c in mov:
                    c.rot = random.randrange(4)
                    c.x = random.randint(0, int(self.W)); c.y = random.randint(0, int(self.H))
                    self.clamp(c)
        else:
            for c in mov:
                self.clamp(c)
        T0 = 150.0 * T0scale
        iters = self.iters
        alpha = (1.0 / T0) ** (1.0 / max(1, iters))
        T = T0
        span0 = max(self.W, self.H) / float(GRID)
        for it in range(iters):
            if (it & 255) == 0 and self.cancel.is_set():
                break
            c = random.choice(mov)
            r = random.random()
            if r < 0.15 and len(mov) > 1:
                o = random.choice(mov)
                if o is c:
                    continue
                old = self.local(c) + self.local(o)
                c.x, c.y, o.x, o.y = o.x, o.y, c.x, c.y
                self.clamp(c); self.clamp(o)
                new = self.local(c) + self.local(o)
                dlt = new - old
                if dlt > 0 and random.random() >= math.exp(-dlt / T):
                    c.x, c.y, o.x, o.y = o.x, o.y, c.x, c.y
                    self.clamp(c); self.clamp(o)
            else:
                ox, oy, orot = c.x, c.y, c.rot
                old = self.local(c)
                if r < 0.35:
                    c.rotate_around_center((c.rot + random.choice((1, 2, 3))) % 4)
                    self.clamp(c)
                else:
                    R = max(1, int(span0 * 0.3 * T / T0))
                    c.x = snap(c.x + random.randint(-R, R) * GRID)
                    c.y = snap(c.y + random.randint(-R, R) * GRID)
                    self.clamp(c)
                new = self.local(c)
                dlt = new - old
                if dlt > 0 and random.random() >= math.exp(-dlt / T):
                    c.x, c.y, c.rot = ox, oy, orot
            T *= alpha

    def find_slot(self, c):
        ox, oy, orot = c.x, c.y, c.rot
        maxr = 35
        for rot in [orot] + [r for r in range(4) if r != orot]:
            c.rot = rot
            for rr in range(0, maxr):
                cands = []
                for dx in range(-rr, rr + 1):
                    dys = (-rr, rr) if abs(dx) != rr else range(-rr, rr + 1)
                    for dy in dys:
                        c.x = snap(ox + dx * 2 * GRID); c.y = snap(oy + dy * 2 * GRID)
                        if self.inside(c) and not self.overlap(c):
                            sc = sum(w * self.hp(n) for n, w in self.cnets[c.ref])
                            if self.use_edge and getattr(c, "edge_pref", False):
                                sc += EDGE_W * self.edge_dist(c)
                            cands.append((sc, c.x, c.y))
                if cands:
                    _, c.x, c.y = min(cands)
                    return True
        c.x, c.y, c.rot = ox, oy, orot
        return False

    def legalize(self):
        mov = [c for c in self.comps if not c.fixed]
        mov.sort(key=lambda c: -(c.bb[0][2] - c.bb[0][0]) * (c.bb[0][3] - c.bb[0][1]))
        for _ in range(4):
            bad = [c for c in mov if not self.inside(c) or self.overlap(c)]
            if not bad:
                return
            for c in bad:
                self.find_slot(c)

    def _swap_2pin_nets(self, c):
        if len(c.pads) != 2:
            return
        n0, n1 = c.pin_net.get(0), c.pin_net.get(1)
        if n0 == n1:
            return
        if n0 is not None:
            c.pin_net[1] = n0
        else:
            c.pin_net.pop(1, None)
        if n1 is not None:
            c.pin_net[0] = n1
        else:
            c.pin_net.pop(0, None)
        for k, v in list(c.labels.items()):
            if v == 0:
                c.labels[k] = 1
            elif v == 1:
                c.labels[k] = 0
        for net_name in (n0, n1):
            if net_name and net_name in self.d.net_pins:
                new_lst = []
                for comp_obj, p_idx in self.d.net_pins[net_name]:
                    if comp_obj is c:
                        new_lst.append((c, 1 if p_idx == 0 else 0))
                    else:
                        new_lst.append((comp_obj, p_idx))
                self.d.net_pins[net_name] = new_lst

    def polish_rotation(self):
        mov = [c for c in self.comps if not c.fixed]
        for _pass in range(2):
            improved = False
            for c in mov:
                ox, oy, orot = c.x, c.y, c.rot
                best_sc = sum(w * self.hp(n) for n, w in self.cnets[c.ref]) + 60.0 * count_cross(ratsnest(self.d))
                best_state = (ox, oy, orot)
                for r in range(4):
                    c.x, c.y, c.rot = ox, oy, orot
                    c.rotate_around_center(r)
                    self.clamp(c)
                    if not (self.inside(c) and not self.overlap(c)):
                        continue
                    sc = sum(w * self.hp(n) for n, w in self.cnets[c.ref]) + 60.0 * count_cross(ratsnest(self.d))
                    if sc < best_sc - 1e-6:
                        best_sc = sc
                        best_state = (c.x, c.y, c.rot)
                        improved = True
                c.x, c.y, c.rot = best_state

                if self.use_pinswap and getattr(c, "swappable_pins", False):
                    sc_before = sum(w * self.hp(n) for n, w in self.cnets[c.ref]) + 60.0 * count_cross(ratsnest(self.d))
                    self._swap_2pin_nets(c)
                    sc_after = sum(w * self.hp(n) for n, w in self.cnets[c.ref]) + 60.0 * count_cross(ratsnest(self.d))
                    if sc_after >= sc_before - 1e-6:
                        self._swap_2pin_nets(c)
                    else:
                        improved = True
            if not improved:
                break


def auto_place(d, P, cancel, log, warm=False, T0scale=1.0):
    seeds = 1 if warm else max(1, int(P.get("multi_seeds", 1)))
    best_snapshot = None
    base_state = random.getstate()

    for s_idx in range(seeds):
        if cancel.is_set():
            break
        if s_idx > 0:
            random.seed(random.randint(1, 999999))
        pl = Placer(d, P, cancel)
        pl.run(warm, T0scale)
        pl.legalize()
        pl.polish_rotation()
        legal = pl.legal()
        cr = count_cross(ratsnest(d))
        hpwl = sum(pl.hp(n) for n in d.nets)
        key = (0 if legal else 1, cr, hpwl)
        snap_data = (
            key,
            legal,
            cr,
            {c.ref: (c.x, c.y, c.rot, dict(c.pin_net), dict(c.labels)) for c in d.comp_list},
            {n: [(c.ref, idx) for c, idx in pins] for n, pins in d.net_pins.items()},
        )
        if best_snapshot is None or key < best_snapshot[0]:
            best_snapshot = snap_data

    if best_snapshot is not None:
        _, legal, cr, comp_pos, net_pins_snap = best_snapshot
        for c in d.comp_list:
            c.x, c.y, c.rot, pnet, labs = comp_pos[c.ref]
            c.pin_net = pnet
            c.labels = labs
        for n, ref_idx_list in net_pins_snap.items():
            d.net_pins[n] = [(d.comps[r], idx) for r, idx in ref_idx_list]
    else:
        legal = Placer(d, P, cancel).legal()
        cr = count_cross(ratsnest(d))

    auto_place_silkscreen(d, None)
    log("  Placement: %s | giao cắt rat's nest: %d | bo %.1f x %.1f mm%s" %
        ("HỢP LỆ" if legal else "CÒN CHỒNG LẤN", cr, d.W / MM, d.H / MM,
         (" (chọn tốt nhất từ %d seed)" % seeds) if seeds > 1 else ""))
    return legal


class RouteResult:
    def __init__(self, two_layers=False):
        self.two_layers = bool(two_layers)
        self.segs, self.vias, self.jumps, self.tears, self.failed = [], [], [], [], []


class Router:
    BEND, VIA_COST, JUMP_COST, TOP_PEN = 0.55, 12.0, 28.0, 0.3
    MAX_EXP = 240000

    def __init__(self, d, P, cancel):
        self.d, self.P, self.cancel = d, P, cancel
        self.W, self.H = d.W, d.H
        self.two = P["two_layers"]
        self.use_45 = P.get("use_45", True)
        self.L = 2 if self.two else 1
        self.nx = int(self.W // GRID) + 1
        self.ny = int(self.H // GRID) + 1
        self.size = self.nx * self.ny
        cl = P["classes"]
        self.wn = {n: cl[net.cls]["w"] for n, net in d.nets.items()}
        self.cn = {n: cl[net.cls]["c"] for n, net in d.nets.items()}
        self.jl = [] if (self.two or not P["jumpers"]) else \
            sorted({max(2, int(round(l / GRID))) for l in P["jumper_mils"]})
        self.offc = {}
        self.pad_list = []
        self.net_cells = {n: [] for n in d.nets}
        for c in d.comp_list:
            for i in range(len(c.pads)):
                x, y = c.pad_abs(i)
                cell = (int(round(x / GRID)), int(round(y / GRID)))
                net = c.pin_net.get(i)
                self.pad_list.append((cell[0], cell[1], net))
                if net and cell not in self.net_cells[net]:
                    self.net_cells[net].append(cell)
        self.padcells = {(a, b) for a, b, _ in self.pad_list}
        self.pz = {}
        for a, b, n in self.pad_list:
            self.add_pz(a, b, n)
        self.base_pz = copy.deepcopy(self.pz)
        self.keep = set()
        if not P["under"]:
            for c in d.comp_list:
                poly = c.body_poly()
                if not poly:
                    continue
                xs = [p[0] for p in poly]; ys = [p[1] for p in poly]
                for cx in range(int(min(xs) // GRID) + 1, int(max(xs) // GRID) + 1):
                    for cy in range(int(min(ys) // GRID) + 1, int(max(ys) // GRID) + 1):
                        if min(xs) < cx * GRID < max(xs) and min(ys) < cy * GRID < max(ys) \
                                and (cx, cy) not in self.padcells:
                            self.keep.add((cx, cy))

        self.turn_pen = [[0.0] * 8 for _ in range(9)]
        for pd in range(8):
            vx1, vy1 = DIRS8[pd]
            l1 = math.hypot(vx1, vy1)
            for nd in range(8):
                if pd == nd:
                    self.turn_pen[pd][nd] = 0.0
                else:
                    vx2, vy2 = DIRS8[nd]
                    l2 = math.hypot(vx2, vy2)
                    cos_a = (vx1 * vx2 + vy1 * vy2) / (l1 * l2)
                    if cos_a > 0.5:
                        self.turn_pen[pd][nd] = self.BEND * 0.42
                    elif cos_a > -0.1:
                        self.turn_pen[pd][nd] = self.BEND
                    elif cos_a > -0.85:
                        self.turn_pen[pd][nd] = self.BEND * 3.2
                    else:
                        self.turn_pen[pd][nd] = 1e6

        self.hist = [[0.0] * self.size for _ in range(self.L)]
        self.reset()

    def add_pz(self, cx, cy, net):
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                k = (cx + dx, cy + dy)
                v = self.pz.get(k)
                self.pz[k] = net if v is None or v == net else "*"

    def offs(self, req):
        key = round(req, 2)
        if key not in self.offc:
            n = int(req // GRID) + 1
            self.offc[key] = [(dx, dy) for dx in range(-n, n + 1) for dy in range(-n, n + 1)
                              if math.hypot(dx * GRID, dy * GRID) < req - 1e-6]
        return self.offc[key]

    def reset(self):
        self.titems = [dict() for _ in range(self.L)]
        self.titems_diag = [dict() for _ in range(self.L)]
        self.holes = []
        self.jtop = {}
        self.pz = copy.deepcopy(self.base_pz)
        self.segs, self.vias, self.jumps = [], [], []

    def rebuild_pz(self):
        self.pz = copy.deepcopy(self.base_pz)
        for x, y, net in self.holes:
            self.add_pz(x, y, net)

    def blocked(self, net, w=None):
        w = self.wn[net] if w is None else w
        c = self.cn[net]
        nx, ny = self.nx, self.ny
        B = [bytearray(self.size) for _ in range(self.L)]
        pads = [(a, b, n) for a, b, n in self.pad_list] + self.holes
        for cx, cy, pn in pads:
            if pn == net:
                continue
            clr = max(c, self.cn.get(pn, c))
            for dx, dy in self.offs(PAD_D / 2.0 + w / 2.0 + clr):
                xx, yy = cx + dx, cy + dy
                if 0 <= xx < nx and 0 <= yy < ny:
                    idx = xx * ny + yy
                    for l in range(self.L):
                        B[l][idx] = 1
        for l in range(self.L):
            bl = B[l]
            for (cx, cy, pn), pw in self.titems[l].items():
                if pn == net:
                    continue
                clr = max(c, self.cn[pn])
                for dx, dy in self.offs((w + pw) / 2.0 + clr):
                    xx, yy = cx + dx, cy + dy
                    if 0 <= xx < nx and 0 <= yy < ny:
                        bl[xx * ny + yy] = 1
            for (mx, my, pn), pw in self.titems_diag[l].items():
                if pn == net:
                    continue
                req = (w + pw) / 2.0 + max(c, self.cn[pn])
                r_cells = int(req // GRID) + 2
                icx, icy = int(mx), int(my)
                for xx in range(max(0, icx - r_cells), min(nx, icx + r_cells + 1)):
                    for yy in range(max(0, icy - r_cells), min(ny, icy + r_cells + 1)):
                        if math.hypot((xx - mx) * GRID, (yy - my) * GRID) < req - 1e-6:
                            bl[xx * ny + yy] = 1
        if self.keep:
            b0 = B[0]
            for kx, ky in self.keep:
                if 0 <= kx < nx and 0 <= ky < ny:
                    b0[kx * ny + ky] = 1
        return B

    def astar(self, B, Bv, own, tg, net):
        nx, ny, L = self.nx, self.ny, self.L
        tl = list(tg)
        tg_idx_set = {a * ny + b for a, b in tl}
        own_idx_set = {x * ny + y for x, y, _ in own}
        use_45 = self.use_45
        ndirs = 8 if use_45 else 4
        turn_pen = self.turn_pen
        hist = self.hist

        if use_45:
            def h(x, y):
                best_d = 1e18
                for a, b in tl:
                    dx = abs(x - a); dy = abs(y - b)
                    d_oct = (dx + dy) + (SQRT2 - 2.0) * (dx if dx < dy else dy)
                    if d_oct < best_d:
                        best_d = d_oct
                return best_d
        else:
            def h(x, y):
                return min(abs(x - a) + abs(y - b) for a, b in tl)

        heap, best, par, cnt = [], {}, {}, 0
        for (x, y, l) in own:
            st = (x, y, l, 8)
            best[st] = 0.0
            heapq.heappush(heap, (h(x, y), 0.0, cnt, st)); cnt += 1
        expanded = 0
        while heap:
            f, g, _, st = heapq.heappop(heap)
            if g > best.get(st, 1e18):
                continue
            x, y, l, d = st
            xy_idx = x * ny + y
            if xy_idx in tg_idx_set:
                path = []
                while st in par:
                    pst, kind = par[st]; path.append((st, kind)); st = pst
                path.append((st, None)); path.reverse()
                return path
            expanded += 1
            if expanded > self.MAX_EXP or ((expanded & 1023) == 0 and self.cancel.is_set()):
                return None
            bl = B[l]
            hl = hist[l]
            t_pen = turn_pen[d]
            top_p = self.TOP_PEN if l == 1 else 0.0
            for nd in range(ndirs):
                dx, dy = DIRS8[nd]
                xx, yy = x + dx, y + dy
                if xx < 1 or yy < 1 or xx > nx - 2 or yy > ny - 2:
                    continue
                n_idx = xx * ny + yy
                if bl[n_idx] and n_idx not in tg_idx_set:
                    continue
                if nd >= 4:
                    idx1 = (x + dx) * ny + y
                    idx2 = x * ny + (y + dy)
                    if (bl[idx1] and idx1 not in tg_idx_set and idx1 not in own_idx_set) or \
                       (bl[idx2] and idx2 not in tg_idx_set and idx2 not in own_idx_set):
                        continue
                step_c = STEP_COST8[nd] + t_pen[nd] + top_p + hl[n_idx]
                cost = g + step_c
                ns = (xx, yy, l, nd)
                if cost < best.get(ns, 1e18):
                    best[ns] = cost; par[ns] = (st, "T")
                    heapq.heappush(heap, (cost + h(xx, yy), cost, cnt, ns)); cnt += 1
            if L == 2 and (x, y) not in self.padcells and not Bv[0][xy_idx] and not Bv[1][xy_idx]:
                ns = (x, y, 1 - l, 8); cost = g + self.VIA_COST + hist[1 - l][xy_idx]
                if cost < best.get(ns, 1e18):
                    best[ns] = cost; par[ns] = (st, "V")
                    heapq.heappush(heap, (cost + h(x, y), cost, cnt, ns)); cnt += 1
            if self.jl and l == 0 and ((x, y) in self.padcells or not Bv[0][xy_idx]) and self.jtop.get((x, y), net) == net:
                for nd in range(4):
                    dx, dy = DIRS[nd]
                    for k in self.jl:
                        lx, ly = x + dx * k, y + dy * k
                        if lx < 1 or ly < 1 or lx > nx - 2 or ly > ny - 2:
                            continue
                        l_idx = lx * ny + ly
                        if Bv[0][l_idx] or (lx, ly) in self.padcells or self.jtop.get((lx, ly), net) != net:
                            continue
                        ok = True
                        for i in range(1, k):
                            cc = (x + dx * i, y + dy * i)
                            if self.pz.get(cc, net) != net or self.jtop.get(cc, net) != net:
                                ok = False; break
                        if not ok:
                            continue
                        ns = (lx, ly, 0, nd); cost = g + k + self.JUMP_COST
                        if cost < best.get(ns, 1e18):
                            best[ns] = cost; par[ns] = (st, "J")
                            heapq.heappush(heap, (cost + h(lx, ly), cost, cnt, ns)); cnt += 1
        return None

    @staticmethod
    def compress(pts):
        if len(pts) <= 2:
            return pts
        out = [pts[0]]
        for i in range(1, len(pts) - 1):
            a, b, c = out[-1], pts[i], pts[i + 1]
            if (b[0] - a[0]) * (c[1] - b[1]) != (b[1] - a[1]) * (c[0] - b[0]):
                out.append(b)
        out.append(pts[-1])
        return out

    def commit(self, net, path):
        w = self.wn[net]
        cur, curl, prev = [], 0, None

        def flush():
            for idx_p, (cx, cy) in enumerate(cur):
                self.titems[curl][(cx, cy, net)] = w
                if idx_p > 0:
                    px_, py_ = cur[idx_p - 1]
                    if abs(cx - px_) == 1 and abs(cy - py_) == 1:
                        self.titems_diag[curl][((cx + px_) * 0.5, (cy + py_) * 0.5, net)] = w
            if len(cur) >= 2:
                pts = [(a * GRID, b * GRID) for a, b in self.compress(cur)]
                self.segs.append((net, curl, pts, w))
        for st, kind in path:
            x, y, l, d = st
            if kind is None:
                cur, curl = [(x, y)], l
            elif kind == "T":
                cur.append((x, y))
            elif kind == "V":
                flush(); self.vias.append((x * GRID, y * GRID, net))
                self.holes.append((x, y, net)); self.add_pz(x, y, net)
                cur, curl = [(x, y)], l
            elif kind == "J":
                flush()
                px, py = prev
                self.jumps.append((net, (px * GRID, py * GRID), (x * GRID, y * GRID)))
                for hx, hy in ((px, py), (x, y)):
                    self.holes.append((hx, hy, net)); self.add_pz(hx, hy, net)
                n = max(abs(x - px), abs(y - py))
                for i in range(n + 1):
                    self.jtop[(px + (x - px) // n * i if x != px else px, py + (y - py) // n * i if y != py else py)] = net
                cur, curl = [(x, y)], l
            prev = (x, y)
        flush()

    def rip(self, net):
        self.segs = [s for s in self.segs if s[0] != net]
        self.vias = [v for v in self.vias if v[2] != net]
        self.jumps = [j for j in self.jumps if j[0] != net]
        self.holes = [h for h in self.holes if h[2] != net]
        for l in range(self.L):
            for k in [k for k in self.titems[l] if k[2] == net]:
                del self.titems[l][k]
            for k in [k for k in self.titems_diag[l] if k[2] == net]:
                del self.titems_diag[l][k]
        for k in [k for k, v in self.jtop.items() if v == net]:
            del self.jtop[k]
        self.rebuild_pz()

    def _find_blocking_nets(self, net):
        pins = self.net_cells[net]
        if len(pins) < 2:
            return []
        xs = [p[0] for p in pins]; ys = [p[1] for p in pins]
        x0, x1 = max(1, min(xs) - 3), min(self.nx - 2, max(xs) + 3)
        y0, y1 = max(1, min(ys) - 3), min(self.ny - 2, max(ys) + 3)
        counts = {}
        ny = self.ny
        for px, py in pins:
            for dx in range(-3, 4):
                for dy in range(-3, 4):
                    xx, yy = px + dx, py + dy
                    if 0 <= xx < self.nx and 0 <= yy < ny:
                        idx = xx * ny + yy
                        for l in range(self.L):
                            self.hist[l][idx] = min(18.0, self.hist[l][idx] + 0.65)
        for l in range(self.L):
            for (cx, cy, pn) in self.titems[l]:
                if pn == net:
                    continue
                if x0 <= cx <= x1 and y0 <= cy <= y1:
                    w_score = 1
                    for px, py in pins:
                        if abs(cx - px) + abs(cy - py) <= 4:
                            w_score += 4
                    counts[pn] = counts.get(pn, 0) + w_score
                    self.hist[l][cx * ny + cy] = min(18.0, self.hist[l][cx * ny + cy] + 0.45)
        return [pn for pn, _ in sorted(counts.items(), key=lambda kv: -kv[1])[:2]]

    def route_net(self, net):
        pins = self.net_cells[net]
        if len(pins) < 2:
            return True
        cx_avg = sum(p[0] for p in pins) / float(len(pins))
        cy_avg = sum(p[1] for p in pins) / float(len(pins))
        ordered_pins = sorted(pins, key=lambda p: abs(p[0] - cx_avg) + abs(p[1] - cy_avg))
        B = self.blocked(net)
        Bv = self.blocked(net, VIA_D) if (self.L == 2 or self.jl) else B
        own = {(ordered_pins[0][0], ordered_pins[0][1], l) for l in range(self.L)}
        remaining = set(ordered_pins[1:])
        while remaining:
            path = self.astar(B, Bv, own, remaining, net)
            if path is None:
                self.rip(net)
                return False
            end = path[-1][0]
            self.commit(net, path)
            for st, _ in path:
                own.add((st[0], st[1], st[2]))
            for l in range(self.L):
                own.add((end[0], end[1], l))
            remaining.discard((end[0], end[1]))
        return True

    def make_teardrops(self):
        out = []
        R = PAD_D / 2.0
        pads = {(a, b) for a, b, n in self.pad_list if n}
        for net, l, pts, w in self.segs:
            if w >= PAD_D - 6:
                continue
            for end, nxt in ((pts[0], pts[1]), (pts[-1], pts[-2])):
                if (end[0] // GRID, end[1] // GRID) not in pads:
                    continue
                dx, dy = nxt[0] - end[0], nxt[1] - end[1]
                ln = math.hypot(dx, dy)
                if ln < 1e-6:
                    continue
                ux, uy = dx / ln, dy / ln; nx_, ny_ = -uy, ux
                Lt = min(R * 2.4, ln * 0.9)
                if Lt < R * 1.1:
                    continue
                c = end
                out.append((l, [(c[0] + nx_ * R, c[1] + ny_ * R),
                                (c[0] + ux * Lt + nx_ * w / 2, c[1] + uy * Lt + ny_ * w / 2),
                                (c[0] + ux * Lt - nx_ * w / 2, c[1] + uy * Lt - ny_ * w / 2),
                                (c[0] - nx_ * R, c[1] - ny_ * R)]))
        return out

    def run(self, log):
        d = self.d
        hpw = {}
        for n, pins in d.net_pins.items():
            xs = [c.pad_abs(i)[0] for c, i in pins]; ys = [c.pad_abs(i)[1] for c, i in pins]
            hpw[n] = (max(xs) - min(xs) + max(ys) - min(ys)) if xs else 0
        order = sorted([n for n in d.nets if len(self.net_cells[n]) >= 2], key=lambda n: (-self.wn[n], hpw[n]))
        failed = []
        passes = max(1, self.P.get("passes", 3))
        best_snap = None

        for p in range(passes):
            self.reset(); failed = []
            routed_set = set()
            for n in order:
                if self.cancel.is_set():
                    break
                if self.route_net(n):
                    routed_set.add(n)
                else:
                    blockers = [bn for bn in self._find_blocking_nets(n) if bn in routed_set]
                    resolved = False
                    if blockers and not self.cancel.is_set():
                        saved_segs = list(self.segs)
                        saved_vias = list(self.vias)
                        saved_jumps = list(self.jumps)
                        saved_holes = list(self.holes)
                        saved_titems = [dict(t) for t in self.titems]
                        saved_tdiag = [dict(t) for t in self.titems_diag]
                        saved_jtop = dict(self.jtop)
                        for bn in blockers:
                            self.rip(bn)
                        if self.route_net(n):
                            all_re = True
                            for bn in blockers:
                                if not self.route_net(bn):
                                    all_re = False
                                    break
                            if all_re:
                                resolved = True
                                routed_set.add(n)
                        if not resolved:
                            self.segs, self.vias, self.jumps, self.holes = saved_segs, saved_vias, saved_jumps, saved_holes
                            self.titems, self.titems_diag, self.jtop = saved_titems, saved_tdiag, saved_jtop
                            self.rebuild_pz()
                    if not resolved:
                        failed.append(n)

            length_cur = sum(math.hypot(pt[i][0] - pt[i + 1][0], pt[i][1] - pt[i + 1][1])
                             for _, _, pt, _ in self.segs for i in range(len(pt) - 1))
            key = (len(failed), len(self.jumps), len(self.vias), length_cur)
            if best_snap is None or key < best_snap[0]:
                best_snap = (key, list(self.segs), list(self.vias), list(self.jumps), list(failed))
            if not failed or self.cancel.is_set():
                break
            order = failed + [n for n in order if n not in failed]

        if best_snap is not None:
            _, self.segs, self.vias, self.jumps, failed = best_snap
        res = RouteResult(two_layers=self.two)
        res.segs, res.vias, res.jumps, res.failed = list(self.segs), list(self.vias), list(self.jumps), failed
        if self.P["teardrop"]:
            res.tears = self.make_teardrops()
        auto_place_silkscreen(d, res)
        tot = sum(len(self.net_cells[n]) >= 2 for n in d.nets)
        length = sum(math.hypot(p[i][0] - p[i + 1][0], p[i][1] - p[i + 1][1])
                     for _, _, p, _ in res.segs for i in range(len(p) - 1))
        log("  Routing%s: %d/%d net xong | jumper %d | via %d | teardrop %d | dây dài %.0f mm%s" %
            (" (45°)" if self.use_45 else " (90°)", tot - len(failed), tot, len(res.jumps), len(res.vias),
             len(res.tears), length / MM, (" | LỖI: " + ", ".join(failed)) if failed else ""))
        return res

def _pt_seg_dist(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    l2 = dx * dx + dy * dy
    if l2 <= 1e-9:
        return math.hypot(px - ax, py - ay), ax, ay
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / l2))
    qx, qy = ax + t * dx, ay + t * dy
    return math.hypot(px - qx, py - qy), qx, qy


def _seg_seg_dist(a1, a2, b1, b2):
    if _ccw(a1, a2, b1) * _ccw(a1, a2, b2) < 0 and _ccw(b1, b2, a1) * _ccw(b1, b2, a2) < 0:
        mx = (a1[0] + a2[0] + b1[0] + b2[0]) * 0.25
        my = (a1[1] + a2[1] + b1[1] + b2[1]) * 0.25
        return 0.0, mx, my
    cands = [
        _pt_seg_dist(a1[0], a1[1], b1[0], b1[1], b2[0], b2[1]),
        _pt_seg_dist(a2[0], a2[1], b1[0], b1[1], b2[0], b2[1]),
        _pt_seg_dist(b1[0], b1[1], a1[0], a1[1], a2[0], a2[1]),
        _pt_seg_dist(b2[0], b2[1], a1[0], a1[1], a2[0], a2[1]),
    ]
    return min(cands, key=lambda x: x[0])


def run_drc(d, res, P):
    issues = []
    if not d:
        return issues
    E = P.get("edge_mm", 1.5) * MM
    m = P.get("solder_mm", 2.0) * MM / 2.0
    cl = P.get("classes", DEFAULT_CLASSES)

    comps = d.comp_list
    for i, c1 in enumerate(comps):
        bb1 = c1.bb[c1.rot]; e1 = PAD_D / 2.0
        r1 = (c1.x + bb1[0] - e1 - m, c1.y + bb1[1] - e1 - m, c1.x + bb1[2] + e1 + m, c1.y + bb1[3] + e1 + m)
        if (c1.x + bb1[0] - e1 < E - 1.0 or c1.x + bb1[2] + e1 > d.W - E + 1.0 or
                c1.y + bb1[1] - e1 < E - 1.0 or c1.y + bb1[3] + e1 > d.H - E + 1.0):
            cx, cy = c1.x + (bb1[0] + bb1[2]) * 0.5, c1.y + (bb1[1] + bb1[3]) * 0.5
            issues.append({
                "sev": "WARN", "type": "EDGE_COMP", "target": c1.ref,
                "desc": f"Linh kiện {c1.ref} vi phạm lề mép bo ({P.get('edge_mm', 1.5):.1f} mm)",
                "x": cx, "y": cy
            })
        for j in range(i + 1, len(comps)):
            c2 = comps[j]
            bb2 = c2.bb[c2.rot]
            r2 = (c2.x + bb2[0] - e1 - m, c2.y + bb2[1] - e1 - m, c2.x + bb2[2] + e1 + m, c2.y + bb2[3] + e1 + m)
            ox = min(r1[2], r2[2]) - max(r1[0], r2[0])
            oy = min(r1[3], r2[3]) - max(r1[1], r2[1])
            if ox > 1.0 and oy > 1.0:
                mx = (max(r1[0], r2[0]) + min(r1[2], r2[2])) * 0.5
                my = (max(r1[1], r2[1]) + min(r1[3], r2[3])) * 0.5
                issues.append({
                    "sev": "ERROR", "type": "OVERLAP", "target": f"{c1.ref} ↔ {c2.ref}",
                    "desc": f"Chồng lấn vùng linh kiện ({ox / MM:.2f} x {oy / MM:.2f} mm)",
                    "x": mx, "y": my
                })

    if res is None:
        for n, pins in d.net_pins.items():
            if len(pins) >= 2:
                p0 = pins[0][0].pad_abs(pins[0][1])
                issues.append({
                    "sev": "WARN", "type": "UNROUTED", "target": n,
                    "desc": f"Net '{n}' ({len(pins)} chân) chưa chạy Auto-Routing",
                    "x": p0[0], "y": p0[1]
                })
        return issues

    for fn in getattr(res, "failed", []):
        pins = d.net_pins.get(fn, [])
        px, py = pins[0][0].pad_abs(pins[0][1]) if pins else (d.W * 0.5, d.H * 0.5)
        issues.append({
            "sev": "ERROR", "type": "UNROUTED", "target": fn,
            "desc": f"Net '{fn}' chưa đi dây thành công",
            "x": px, "y": py
        })

    pads_info = []
    for c in comps:
        for i in range(len(c.pads)):
            px, py = c.pad_abs(i)
            pnet = c.pin_net.get(i)
            pcls = d.nets[pnet].cls if (pnet and pnet in d.nets) else "SIGNAL"
            pads_info.append((px, py, pnet, PAD_D * 0.5, cl[pcls]["c"], f"{c.ref}.{i+1}"))
    for vx, vy, vnet in getattr(res, "vias", []):
        vcls = d.nets[vnet].cls if (vnet and vnet in d.nets) else "SIGNAL"
        pads_info.append((vx, vy, vnet, VIA_D * 0.5, cl[vcls]["c"], f"VIA({vnet})"))

    flat_segs = []
    for net, l, pts, w in getattr(res, "segs", []):
        ncls = d.nets[net].cls if net in d.nets else "SIGNAL"
        nclr = cl[ncls]["c"]
        for k in range(len(pts) - 1):
            flat_segs.append((net, l, pts[k], pts[k + 1], w * 0.5, nclr))

    own_pad_coords = {
        n: [c.pad_abs(i) for c, i in pins]
        for n, pins in d.net_pins.items()
    }

    def _near_own_pad(net_name, qx, qy):
        for opx, opy in own_pad_coords.get(net_name, ()):
            if math.hypot(qx - opx, qy - opy) <= GRID * 1.6:
                return True
        return False

    seen_pairs = set()
    for net, l, p1, p2, hw, nclr in flat_segs:
        for px, py, pnet, pr, pclr, plab in pads_info:
            if pnet == net:
                continue
            pair_key = ("PT", min(net, str(plab)), max(net, str(plab)))
            if pair_key in seen_pairs:
                continue
            dist, qx, qy = _pt_seg_dist(px, py, p1[0], p1[1], p2[0], p2[1])
            req = hw + pr + max(nclr, pclr)
            if dist < req - 2.5:
                gap = max(0.0, dist - hw - pr)
                if gap >= 12.0 and _near_own_pad(net, qx, qy):
                    continue
                seen_pairs.add(pair_key)
                issues.append({
                    "sev": "ERROR", "type": "CLEARANCE", "target": f"{net} ↔ {plab}",
                    "desc": f"Khoảng hở dây-pad quá hẹp: {gap:.1f} mil (yêu cầu ≥ {max(nclr, pclr)} mil)",
                    "x": (px + qx) * 0.5, "y": (py + qy) * 0.5
                })

    for i in range(len(flat_segs)):
        n1, l1, a1, a2, hw1, c1_clr = flat_segs[i]
        for j in range(i + 1, len(flat_segs)):
            n2, l2, b1, b2, hw2, c2_clr = flat_segs[j]
            if l1 != l2 or n1 == n2:
                continue
            pair_key = ("TT", l1, min(n1, n2), max(n1, n2))
            if pair_key in seen_pairs:
                continue
            dist, qx, qy = _seg_seg_dist(a1, a2, b1, b2)
            req = hw1 + hw2 + max(c1_clr, c2_clr)
            if dist < req - 2.5:
                gap = max(0.0, dist - hw1 - hw2)
                if gap >= 12.0 and (_near_own_pad(n1, qx, qy) or _near_own_pad(n2, qx, qy)):
                    continue
                seen_pairs.add(pair_key)
                issues.append({
                    "sev": "ERROR", "type": "CLEARANCE", "target": f"{n1} ↔ {n2} (L{l1+1})",
                    "desc": f"Khoảng hở 2 đường mạch quá hẹp: {gap:.1f} mil (yêu cầu ≥ {max(c1_clr, c2_clr)} mil)",
                    "x": qx, "y": qy
                })
    return issues

def optimize_board(d, P, cancel, log, post=None):
    W0, H0 = d.W, d.H
    sn = lambda v: max(200, int(round(v / 50.0)) * 50)
    best = None
    area = sum((c.bb[0][2] - c.bb[0][0] + 100) * (c.bb[0][3] - c.bb[0][1] + 100) for c in d.comp_list)

    def save_comp_state():
        return {c.ref: (c.x, c.y, c.rot, dict(c.pin_net), dict(c.labels), c.label_offset, c.label_rot_ref)
                for c in d.comp_list}, {n: [(c.ref, idx) for c, idx in pins] for n, pins in d.net_pins.items()}

    def restore_comp_state(c_state, n_state):
        for c in d.comp_list:
            c.x, c.y, c.rot, pnet, labs, loff, lrot = c_state[c.ref]
            c.pin_net = dict(pnet)
            c.labels = dict(labs)
            c.label_offset = loff
            c.label_rot_ref = lrot
        for n, lst in n_state.items():
            d.net_pins[n] = [(d.comps[r], idx) for r, idx in lst]

    def trial(s, warm, T0s):
        if best:
            bw, bh, c_state, n_state, _ = best
            restore_comp_state(c_state, n_state)
            d.W, d.H = sn(W0 * s), sn(H0 * s)
            for c in d.comp_list:
                x, y = c_state[c.ref][0], c_state[c.ref][1]
                if not c.fixed:
                    c.x, c.y = x * d.W / float(bw), y * d.H / float(bh)
                    c.x, c.y = snap(c.x), snap(c.y)
        else:
            d.W, d.H = sn(W0 * s), sn(H0 * s)
        log("▶ Thử bo %.1f x %.1f mm (%.0f%%)" % (d.W / MM, d.H / MM, s * 100))
        legal = auto_place(d, P, cancel, log, warm, T0s)
        if cancel.is_set():
            return None, None
        if not legal:
            return False, None
        res = Router(d, P, cancel).run(log)
        return (not res.failed), res

    ok, res = trial(1.0, False, 1.0)
    if ok is None:
        return None
    c_st, n_st = save_comp_state()
    if not ok:
        log("⚠ Chưa đi dây được 100%% ở kích thước ban đầu. Hãy tăng kích thước bo, giảm Trace/Clearance, bật 2 mặt hoặc jumper.")
        return res
    best = (d.W, d.H, c_st, n_st, res)
    if post:
        post(d, res)
    lo = max(0.15, math.sqrt(area / float(W0 * H0)) * 0.9); hi = 1.0
    for it in range(P.get("bs_iters", 6)):
        if hi - lo < 0.02 or cancel.is_set():
            break
        mid = (lo + hi) / 2.0
        ok, res = trial(mid, True, 0.35)
        if ok is None:
            break
        if ok:
            c_st, n_st = save_comp_state()
            best = (d.W, d.H, c_st, n_st, res)
            hi = mid
            if post:
                post(d, res)
        else:
            lo = mid
    bw, bh, c_st, n_st, res = best
    d.W, d.H = bw, bh
    restore_comp_state(c_st, n_st)
    auto_place_silkscreen(d, res)
    log("✔ Kích thước nhỏ nhất đi dây 100%%: %.1f x %.1f mm  (giảm %.0f%% diện tích)" %
        (bw / MM, bh / MM, 100.0 * (1 - bw * bh / float(W0 * H0))))
    return res


def optimize_board_placement_only(d, P, cancel, log, post=None):
    W0, H0 = d.W, d.H
    sn = lambda v: max(200, int(round(v / 50.0)) * 50)
    best = None
    area = sum((c.bb[0][2] - c.bb[0][0] + 100) * (c.bb[0][3] - c.bb[0][1] + 100) for c in d.comp_list)

    def save_comp_state():
        return {c.ref: (c.x, c.y, c.rot, dict(c.pin_net), dict(c.labels), c.label_offset, c.label_rot_ref)
                for c in d.comp_list}, {n: [(c.ref, idx) for c, idx in pins] for n, pins in d.net_pins.items()}

    def restore_comp_state(c_state, n_state):
        for c in d.comp_list:
            c.x, c.y, c.rot, pnet, labs, loff, lrot = c_state[c.ref]
            c.pin_net = dict(pnet)
            c.labels = dict(labs)
            c.label_offset = loff
            c.label_rot_ref = lrot
        for n, lst in n_state.items():
            d.net_pins[n] = [(d.comps[r], idx) for r, idx in lst]

    def trial(s, warm, T0s):
        if best:
            bw, bh, c_state, n_state = best
            restore_comp_state(c_state, n_state)
            d.W, d.H = sn(W0 * s), sn(H0 * s)
            for c in d.comp_list:
                x, y = c_state[c.ref][0], c_state[c.ref][1]
                if not c.fixed:
                    c.x, c.y = x * d.W / float(bw), y * d.H / float(bh)
                    c.x, c.y = snap(c.x), snap(c.y)
        else:
            d.W, d.H = sn(W0 * s), sn(H0 * s)
        log("▶ Thử nén bo %.1f x %.1f mm (%.0f%%)" % (d.W / MM, d.H / MM, s * 100))
        legal = auto_place(d, P, cancel, log, warm, T0s)
        if cancel.is_set():
            return None
        return legal

    ok = trial(1.0, False, 1.0)
    if ok is None:
        return None
    c_st, n_st = save_comp_state()
    if not ok:
        log("⚠ Linh kiện đang chồng lấn ở kích thước ban đầu. Hãy tăng kích thước bo hoặc giảm lề mép.")
        return None
    best = (d.W, d.H, c_st, n_st)
    if post:
        post(d, None)
    lo = max(0.12, math.sqrt(area / float(W0 * H0)) * 0.85); hi = 1.0
    for it in range(P.get("bs_iters", 6)):
        if hi - lo < 0.02 or cancel.is_set():
            break
        mid = (lo + hi) / 2.0
        ok = trial(mid, True, 0.35)
        if ok is None:
            break
        if ok:
            c_st, n_st = save_comp_state()
            best = (d.W, d.H, c_st, n_st)
            hi = mid
            if post:
                post(d, None)
        else:
            lo = mid
    bw, bh, c_st, n_st = best
    d.W, d.H = bw, bh
    restore_comp_state(c_st, n_st)
    auto_place_silkscreen(d, None)
    log("✔ Kích thước bo nhỏ nhất xếp vừa linh kiện: %.1f x %.1f mm  (giảm %.0f%% diện tích bo)" %
        (bw / MM, bh / MM, 100.0 * (1 - bw * bh / float(W0 * H0))))
    return None

def export_csv(d, path):
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["Ref", "Value", "Footprint", "X_mm", "Y_mm", "Rotation_deg", "X_mil", "Y_mil", "Fixed", "Anchor_X_mm", "Anchor_Y_mm"])
        for c in d.comp_list:
            ox_abs, oy_abs = c.origin_abs()
            x, y = ox_abs, d.H - oy_abs
            ax, ay = c.x, d.H - c.y
            ang = (360 - 90 * c.rot) % 360
            w.writerow([c.ref, c.value, c.fp, "%.3f" % (x / MM), "%.3f" % (y / MM), ang,
                        "%.1f" % x, "%.1f" % y, int(c.fixed), "%.3f" % (ax / MM), "%.3f" % (ay / MM)])

def _seg_poly(p, q, w):
    dx, dy = q[0] - p[0], q[1] - p[1]
    L = math.hypot(dx, dy) or 1.0
    ux, uy = dx / L, dy / L; nx, ny = -uy * w / 2, ux * w / 2; e = w / 2.0
    p2 = (p[0] - ux * e, p[1] - uy * e); q2 = (q[0] + ux * e, q[1] + uy * e)
    return [(p2[0] + nx, p2[1] + ny), (q2[0] + nx, q2[1] + ny), (q2[0] - nx, q2[1] - ny), (p2[0] - nx, p2[1] - ny)]

def _circle(cx, cy, r, n=16):
    return [(cx + r * math.cos(2 * math.pi * i / n), cy + r * math.sin(2 * math.pi * i / n)) for i in range(n)]

def _square(cx, cy, r):
    return [(cx - r, cy - r), (cx + r, cy - r), (cx + r, cy + r), (cx - r, cy + r)]

def _pad_snap_to_exact_map(d):
    mp = {}
    for c in d.comp_list:
        for i in range(len(c.pads)):
            sx, sy = c.pad_abs(i)
            ex, ey = c.pad_exact_abs(i)
            mp[(int(round(sx)), int(round(sy)))] = (ex, ey)
    return mp

def _adjust_seg_pts(pts, pad_map):
    if not pts:
        return pts
    out = list(pts)
    k0 = (int(round(out[0][0])), int(round(out[0][1])))
    if k0 in pad_map:
        out[0] = pad_map[k0]
    k1 = (int(round(out[-1][0])), int(round(out[-1][1])))
    if k1 in pad_map:
        out[-1] = pad_map[k1]
    return out


def geometry(d, res):
    g = {"BOTTOM_COPPER": [], "TOP_COPPER": [], "BOARD_EDGE": [], "TOP_SILK": []}
    drills, lines, texts = [], [], []
    g["BOARD_EDGE"].append([(0, 0), (d.W, 0), (d.W, d.H), (0, d.H)])
    two = bool(res and (getattr(res, "two_layers", False)
                        or any(s[1] == 1 for s in res.segs)
                        or res.vias))
    pad_map = _pad_snap_to_exact_map(d)
    for c in d.comp_list:
        for i in range(len(c.pads)):
            x, y = c.pad_exact_abs(i)
            poly = _square(x, y, PAD_D / 2.0) if c.is_square_pin(i) else _circle(x, y, PAD_D / 2.0)
            g["BOTTOM_COPPER"].append(poly)
            if two:
                g["TOP_COPPER"].append(poly)
            drills.append((x, y, HOLE_D / 2.0))
        bp = c.body_poly()
        if bp:
            g["TOP_SILK"].append(bp)
        cx, cy = c.label_abs()
        texts.append((c.ref, cx, cy))
    if res:
        for net, l, pts, w in res.segs:
            layer = "BOTTOM_COPPER" if l == 0 else "TOP_COPPER"
            adj_pts = _adjust_seg_pts(pts, pad_map)
            for a, b in zip(adj_pts, adj_pts[1:]):
                g[layer].append(_seg_poly(a, b, w))
        for l, poly in res.tears:
            g["BOTTOM_COPPER" if l == 0 else "TOP_COPPER"].append(poly)
        for x, y, net in res.vias:
            g["BOTTOM_COPPER"].append(_circle(x, y, VIA_D / 2.0)); g["TOP_COPPER"].append(_circle(x, y, VIA_D / 2.0))
            drills.append((x, y, HOLE_D / 2.0))
        for net, a, b in res.jumps:
            lines.append((a, b))
            for p in (a, b):
                g["BOTTOM_COPPER"].append(_circle(p[0], p[1], VIA_D / 2.0)); drills.append((p[0], p[1], HOLE_D / 2.0))
    return g, drills, lines, texts


def export_dxf(d, res, path):
    g, drills, lines, texts = geometry(d, res)
    H = d.H
    X = lambda x: x / MM
    Y = lambda y: (H - y) / MM
    Wm, Hm = X(d.W), X(d.H)
    colors = {"BOARD_EDGE": 2, "BOTTOM_COPPER": 1, "TOP_COPPER": 5, "TOP_SILK": 7, "DRILL": 3, "JUMPER": 3}
    with open(path, "w", encoding="utf-8") as f:
        f.write("0\nSECTION\n2\nHEADER\n9\n$ACADVER\n1\nAC1009\n"
                "9\n$INSUNITS\n70\n4\n"
                "9\n$EXTMIN\n10\n0.0\n20\n0.0\n30\n0.0\n"
                "9\n$EXTMAX\n10\n%.4f\n20\n%.4f\n30\n0.0\n"
                "9\n$LIMMIN\n10\n0.0\n20\n0.0\n"
                "9\n$LIMMAX\n10\n%.4f\n20\n%.4f\n0\nENDSEC\n" % (Wm, Hm, Wm, Hm))
        f.write("0\nSECTION\n2\nTABLES\n0\nTABLE\n2\nLAYER\n70\n%d\n" % len(colors))
        for n, col in colors.items():
            f.write("0\nLAYER\n2\n%s\n70\n0\n62\n%d\n6\nCONTINUOUS\n" % (n, col))
        f.write("0\nENDTAB\n0\nENDSEC\n0\nSECTION\n2\nENTITIES\n")
        for layer, polys in g.items():
            for poly in polys:
                f.write("0\nPOLYLINE\n8\n%s\n66\n1\n70\n1\n10\n0.0\n20\n0.0\n30\n0.0\n" % layer)
                for x, y in poly:
                    f.write("0\nVERTEX\n8\n%s\n10\n%.4f\n20\n%.4f\n30\n0.0\n" % (layer, X(x), Y(y)))
                f.write("0\nSEQEND\n8\n%s\n" % layer)
        for x, y, r in drills:
            f.write("0\nCIRCLE\n8\nDRILL\n10\n%.4f\n20\n%.4f\n30\n0.0\n40\n%.4f\n" % (X(x), Y(y), r / MM))
        for a, b in lines:
            f.write("0\nLINE\n8\nJUMPER\n10\n%.4f\n20\n%.4f\n30\n0.0\n11\n%.4f\n21\n%.4f\n31\n0.0\n" %
                    (X(a[0]), Y(a[1]), X(b[0]), Y(b[1])))
        for t, x, y in texts:
            f.write("0\nTEXT\n8\nTOP_SILK\n10\n%.4f\n20\n%.4f\n30\n0.0\n40\n1.0\n1\n%s\n" % (X(x), Y(y), t))
        f.write("0\nENDSEC\n0\nEOF\n")


def export_svg_bottom_mirror(d, res, path):
    g, drills, lines, _ = geometry(d, res)
    Wm, Hm = d.W / MM, d.H / MM
    with open(path, "w", encoding="utf-8") as f:
        f.write('<svg xmlns="http://www.w3.org/2000/svg" width="%.2fmm" height="%.2fmm" viewBox="0 0 %.3f %.3f">\n' % (Wm, Hm, Wm, Hm))
        f.write('<rect width="100%" height="100%" fill="white"/>\n<g fill="black">\n')
        for poly in g["BOTTOM_COPPER"]:
            f.write('<polygon points="%s"/>\n' % " ".join("%.3f,%.3f" % ((d.W - x) / MM, y / MM) for x, y in poly))
        f.write('</g>\n<g fill="white">\n')
        for x, y, r in drills:
            f.write('<circle cx="%.3f" cy="%.3f" r="%.3f"/>\n' % ((d.W - x) / MM, y / MM, r / MM))
        f.write('</g>\n<rect x="0" y="0" width="%.3f" height="%.3f" fill="none" stroke="#999" stroke-width="0.1"/>\n</svg>\n' % (Wm, Hm))

_VEC_FONT = {
    "0": [(0, 0, 4, 0), (4, 0, 4, 6), (4, 6, 0, 6), (0, 6, 0, 0)],
    "1": [(2, 0, 2, 6), (1, 5, 2, 6), (0, 0, 4, 0)],
    "2": [(0, 5, 4, 6), (4, 6, 4, 3), (4, 3, 0, 0), (0, 0, 4, 0)],
    "3": [(0, 6, 4, 6), (4, 6, 4, 0), (0, 3, 4, 3), (0, 0, 4, 0)],
    "4": [(0, 6, 0, 3), (0, 3, 4, 3), (3, 6, 3, 0)],
    "5": [(4, 6, 0, 6), (0, 6, 0, 3), (0, 3, 4, 3), (4, 3, 4, 0), (4, 0, 0, 0)],
    "6": [(4, 6, 0, 6), (0, 6, 0, 0), (0, 0, 4, 0), (4, 0, 4, 3), (4, 3, 0, 3)],
    "7": [(0, 6, 4, 6), (4, 6, 1, 0)],
    "8": [(0, 0, 4, 0), (4, 0, 4, 6), (4, 6, 0, 6), (0, 6, 0, 0), (0, 3, 4, 3)],
    "9": [(4, 3, 0, 3), (0, 3, 0, 6), (0, 6, 4, 6), (4, 6, 4, 0), (4, 0, 0, 0)],
    "A": [(0, 0, 2, 6), (2, 6, 4, 0), (1, 2, 3, 2)],
    "B": [(0, 0, 0, 6), (0, 6, 3, 6), (3, 6, 4, 4), (4, 4, 0, 3), (0, 3, 4, 2), (4, 2, 3, 0), (3, 0, 0, 0)],
    "C": [(4, 6, 0, 6), (0, 6, 0, 0), (0, 0, 4, 0)],
    "D": [(0, 0, 0, 6), (0, 6, 3, 6), (3, 6, 4, 3), (4, 3, 3, 0), (3, 0, 0, 0)],
    "E": [(4, 6, 0, 6), (0, 6, 0, 0), (0, 0, 4, 0), (0, 3, 3, 3)],
    "F": [(4, 6, 0, 6), (0, 6, 0, 0), (0, 3, 3, 3)],
    "G": [(4, 6, 0, 6), (0, 6, 0, 0), (0, 0, 4, 0), (4, 0, 4, 3), (4, 3, 2, 3)],
    "H": [(0, 0, 0, 6), (4, 0, 4, 6), (0, 3, 4, 3)],
    "I": [(1, 6, 3, 6), (2, 6, 2, 0), (1, 0, 3, 0)],
    "J": [(4, 6, 4, 1), (4, 1, 2, 0), (2, 0, 0, 1)],
    "K": [(0, 0, 0, 6), (4, 6, 0, 3), (0, 3, 4, 0)],
    "L": [(0, 6, 0, 0), (0, 0, 4, 0)],
    "M": [(0, 0, 0, 6), (0, 6, 2, 3), (2, 3, 4, 6), (4, 6, 4, 0)],
    "N": [(0, 0, 0, 6), (0, 6, 4, 0), (4, 0, 4, 6)],
    "O": [(0, 0, 4, 0), (4, 0, 4, 6), (4, 6, 0, 6), (0, 6, 0, 0)],
    "P": [(0, 0, 0, 6), (0, 6, 4, 6), (4, 6, 4, 3), (4, 3, 0, 3)],
    "Q": [(0, 0, 4, 0), (4, 0, 4, 6), (4, 6, 0, 6), (0, 6, 0, 0), (2, 2, 4, 0)],
    "R": [(0, 0, 0, 6), (0, 6, 4, 6), (4, 6, 4, 3), (4, 3, 0, 3), (2, 3, 4, 0)],
    "S": [(4, 6, 0, 6), (0, 6, 0, 3), (0, 3, 4, 3), (4, 3, 4, 0), (4, 0, 0, 0)],
    "T": [(0, 6, 4, 6), (2, 6, 2, 0)],
    "U": [(0, 6, 0, 0), (0, 0, 4, 0), (4, 0, 4, 6)],
    "V": [(0, 6, 2, 0), (2, 0, 4, 6)],
    "W": [(0, 6, 1, 0), (1, 0, 2, 3), (2, 3, 3, 0), (3, 0, 4, 6)],
    "X": [(0, 6, 4, 0), (0, 0, 4, 6)],
    "Y": [(0, 6, 2, 3), (4, 6, 2, 3), (2, 3, 2, 0)],
    "Z": [(0, 6, 4, 6), (4, 6, 0, 0), (0, 0, 4, 0)],
    "-": [(1, 3, 3, 3)],
    "_": [(0, 0, 4, 0)],
    ".": [(2, 0, 2, 1)],
}


def _ares_trace_style(w_mil):
    for th in (8, 10, 12, 15, 20, 25, 30, 40, 50, 60, 70, 80, 90, 100):
        if w_mil <= th + 2:
            return f"T{th}"
    return "T50"


def export_proteus_rgn(d, res, path):
    U = lambda x_mil: int(round(x_mil * 2540.0))
    UY = lambda y_mil: int(round((d.H - y_mil) * 2540.0))
    W_u, H_u = U(d.W), U(d.H)

    with open(path, "w", encoding="utf-8") as f:
        f.write("ARES REGION FILE\n\n")
        f.write("*HEADER\n")
        f.write("VERSION 300 410\n")
        f.write("UNITS 10nm\n")
        f.write("AREA  0 0 %-10d %-10d\n\n" % (W_u, H_u))
        f.write("*TRACESTYLES\n")
        f.write("*END_TRACESTYLES\n")
        f.write("*OBJECTS\n")

        f.write("GRAPHIC ED LINE 4 0 %d %d %d\n" % (H_u, W_u, H_u))
        f.write("GRAPHIC ED LINE 4 %d %d %d 0\n" % (W_u, H_u, W_u))
        f.write("GRAPHIC ED LINE 4 %d 0 0 0\n" % W_u)
        f.write("GRAPHIC ED LINE 4 0 0 0 %d\n" % H_u)

        pad_map = _pad_snap_to_exact_map(d)

        for c in d.comp_list:
            for i in range(len(c.pads)):
                px, py = c.pad_exact_abs(i)
                pname = str(c.pad_names.get(i, i + 1)).replace('"', '')[:7]
                pstyle = "S-70-30" if c.is_square_pin(i) else "C-70-30"
                f.write('PAD "%s" "%s" ALL %d %d 0\n' % (pname, pstyle, U(px), UY(py)))

            bp = c.body_poly()
            if bp and len(bp) >= 3:
                for k in range(len(bp)):
                    x1, y1 = bp[k]
                    x2, y2 = bp[(k + 1) % len(bp)]
                    if U(x1) != U(x2) or UY(y1) != UY(y2):
                        f.write("GRAPHIC TS LINE 4 %d %d %d %d\n" % (U(x1), UY(y1), U(x2), UY(y2)))

            cx_mil, cy_mil = c.label_abs()
            label = c.ref.upper()
            scale_u = 18000
            step_u = 5 * scale_u
            start_x = U(cx_mil) - (len(label) * step_u) // 2
            base_y = UY(cy_mil) - 3 * scale_u
            for ch_i, ch in enumerate(label):
                ox = start_x + ch_i * step_u
                for sx1, sy1, sx2, sy2 in _VEC_FONT.get(ch, []):
                    f.write("GRAPHIC TS LINE 4 %d %d %d %d\n" % (
                        ox + sx1 * scale_u, base_y + sy1 * scale_u,
                        ox + sx2 * scale_u, base_y + sy2 * scale_u
                    ))

        if res:
            for net, a, b in res.jumps:
                f.write("GRAPHIC TS LINE 4 %d %d %d %d\n" % (U(a[0]), UY(a[1]), U(b[0]), UY(b[1])))
                f.write('PAD "J" "C-60-30" ALL %d %d 0\n' % (U(a[0]), UY(a[1])))
                f.write('PAD "J" "C-60-30" ALL %d %d 0\n' % (U(b[0]), UY(b[1])))

        f.write("*END_OBJECTS\n")

        if res and res.vias:
            f.write("*VIAS\n")
            for vx, vy, _net in res.vias:
                f.write('"V50" [TOP,BOT] %d %d\n' % (U(vx), UY(vy)))
            f.write("*END_VIAS\n")

        if res and res.segs:
            for l_idx, l_name in ((0, "BOT"), (1, "TOP")):
                l_segs = [(pts, w) for _net, l, pts, w in res.segs if l == l_idx and len(pts) >= 2]
                if not l_segs:
                    continue
                f.write("*LAYER %s\n" % l_name)
                for pts, w in l_segs:
                    adj_pts = _adjust_seg_pts(pts, pad_map)
                    tstyle = _ares_trace_style(w)
                    coords_str = " ".join("%d %d" % (U(px), UY(py)) for px, py in adj_pts)
                    f.write('"%s" S %d %s\n' % (tstyle, len(adj_pts) - 1, coords_str))
                f.write("*END_LAYER\n")


def import_fixed_csv(d, path):
    n = 0
    with open(path, newline="", encoding="utf-8-sig") as f:
        rd = csv.DictReader(f)
        for row in rd:
            k = {a.strip().lower(): v for a, v in row.items() if a}
            ref = k.get("ref") or k.get("designator") or k.get("refdes")
            c = d.comps.get(ref)
            if not c:
                continue
            ang = float(k.get("rotation_deg") or k.get("rotation") or k.get("rot") or 0)
            rot = int(round(((360 - ang) % 360) / 90.0)) % 4
            c.rot = rot
            if "anchor_x_mm" in k and "anchor_y_mm" in k and k.get("anchor_x_mm") and k.get("anchor_y_mm"):
                ax = float(k.get("anchor_x_mm"))
                ay = float(k.get("anchor_y_mm"))
                c.x, c.y = snap(ax * MM), snap(d.H - ay * MM)
            else:
                x = float(k.get("x_mm") or k.get("x") or 0)
                y = float(k.get("y_mm") or k.get("y") or 0)
                ox, oy = getattr(c, "origin", (0.0, 0.0))
                rox, roy = rotpt(ox, oy, rot)
                c.x, c.y = snap(x * MM - rox), snap(d.H - y * MM - roy)
            c.fixed = True; n += 1
    return n

class App:
    def __init__(self, root):
        self.root = root
        root.title("PCB AutoTool")
        root.geometry("1540x920")
        self.design, self.route = None, None
        self.cancel = threading.Event(); self.q = queue.Queue(); self.worker = None
        self.view = [0.15, 30, 30]; self.drag = None; self.pan = None
        self.undo_stack, self.redo_stack = [], []
        self.drc_issues = []
        self.drc_marker = None
        self._vars()
        self._ui()
        self.load_demo()
        root.after(100, self.poll)

    def _vars(self):
        self.v_w = tk.DoubleVar(value=80); self.v_h = tk.DoubleVar(value=50)
        self.v_edge = tk.DoubleVar(value=2.5); self.v_solder = tk.DoubleVar(value=2.5)
        self.v_cls_w = {k: tk.IntVar(value=v["w"]) for k, v in DEFAULT_CLASSES.items()}
        self.v_cls_c = {k: tk.IntVar(value=v["c"]) for k, v in DEFAULT_CLASSES.items()}
        self.v_two = tk.BooleanVar(value=False); self.v_under = tk.BooleanVar(value=True)
        self.v_45 = tk.BooleanVar(value=True)
        self.v_tear = tk.BooleanVar(value=True); self.v_jump = tk.BooleanVar(value=True)
        self.v_jlen = tk.StringVar(value="200,300"); self.v_pass = tk.IntVar(value=3)
        self.v_sa = tk.IntVar(value=15000); self.v_bs = tk.IntVar(value=6)
        self.v_seed = tk.IntVar(value=1); self.v_multiseed = tk.IntVar(value=2)
        self.v_cluster = tk.BooleanVar(value=True)
        self.v_force = tk.BooleanVar(value=True)
        self.v_edge_lock = tk.BooleanVar(value=True)
        self.v_decouple = tk.BooleanVar(value=True)
        self.v_pinswap = tk.BooleanVar(value=True)
        self.show = {k: tk.BooleanVar(value=True) for k in ("bot", "top", "tear", "jump", "court", "rats", "label")}
        self.show["rats"].set(False)
        self.e_x = tk.DoubleVar(); self.e_y = tk.DoubleVar(); self.e_rot = tk.IntVar(value=0)
        self.e_fix = tk.BooleanVar(); self.e_edge = tk.BooleanVar()
        self.e_grp = tk.StringVar(); self.e_cls = tk.StringVar(value="SIGNAL")

    def _ui(self):
        left = ttk.Frame(self.root, padding=4); left.pack(side=tk.LEFT, fill=tk.Y)
        nb = ttk.Notebook(left); nb.pack(fill=tk.X)
        t1 = ttk.Frame(nb, padding=6); nb.add(t1, text="Dữ liệu / Bo")
        for txt, cmd in (("Mở Netlist (.SDF/.EDF/.DSN/.PADS)…", self.open_netlist),
                         ("Kho Footprint SnapEDA (Quản lý / Học)…", self.open_footprint_db_dialog),
                         ("Nạp mạch mẫu NE555", self.load_demo),
                         ("Nạp vị trí CỐ ĐỊNH từ CSV…", self.load_fixed),
                         ("Xuất sang Proteus ARES (.RGN)…", self.exp_rgn),
                         ("Xuất CSV Pick & Place…", self.exp_csv), ("Xuất DXF Vector…", self.exp_dxf),
                         ("Xuất SVG mirror lớp Bottom…", self.exp_svg)):
            ttk.Button(t1, text=txt, command=cmd).pack(fill=tk.X, pady=1)
        f = ttk.LabelFrame(t1, text="Khung board mạch", padding=4); f.pack(fill=tk.X, pady=4)

        for i, (lab, var) in enumerate((("Rộng (mm)", self.v_w), ("Dài (mm)", self.v_h),
                                        ("Lề mép board (mm)", self.v_edge), ("Lề mỏ hàn (mm)", self.v_solder))):
            ttk.Label(f, text=lab).grid(row=i, column=0, sticky="w")
            sp = ttk.Spinbox(f, from_=0, to=500, increment=0.5, width=8, textvariable=var, command=self._sync_board_size)
            sp.grid(row=i, column=1, padx=4)
            sp.bind("<Return>", lambda _e: self._sync_board_size())
            sp.bind("<FocusOut>", lambda _e: self._sync_board_size())
        ttk.Button(f, text="✂ Thu nhỏ board ôm sát", command=self.fit_board_to_components).grid(row=4, column=0, columnspan=2, sticky="we", pady=3)
        ttk.Label(t1, text="Kéo linh kiện trên canvas (Rat's nest động).\nPhím R: Xoay 90° | Ctrl+Z/Y: Undo/Redo.",
                  foreground="#666").pack(anchor="w", pady=4)

        t2 = ttk.Frame(nb, padding=6); nb.add(t2, text="Design Rules")
        ttk.Label(t2, text="Lớp net").grid(row=0, column=0); ttk.Label(t2, text="Trace (mil)").grid(row=0, column=1)
        ttk.Label(t2, text="Clearance (mil)").grid(row=0, column=2)
        names = {"SIGNAL": "Tín hiệu", "POWER": "Nguồn / Mass", "HIGH_CURRENT": "Công suất", "HV_AC": "AC / Cao áp"}
        for i, k in enumerate(DEFAULT_CLASSES, 1):
            ttk.Label(t2, text=names[k]).grid(row=i, column=0, sticky="w")
            ttk.Spinbox(t2, from_=10, to=150, increment=5, width=6, textvariable=self.v_cls_w[k]).grid(row=i, column=1, padx=3, pady=2)
            ttk.Spinbox(t2, from_=0, to=80, increment=1, width=6, textvariable=self.v_cls_c[k]).grid(row=i, column=2, padx=3)
        r = len(DEFAULT_CLASSES) + 1
        for txt, var in (("Đi dây vát góc 45° (Octilinear)", self.v_45),
                         ("Đi dây 2 mặt (via thủ công)", self.v_two),
                         ("Đi dây dưới thân linh kiện", self.v_under),
                         ("Tự chèn Jumper (1 mặt)", self.v_jump),
                         ("Bơm Teardrop", self.v_tear)):
            ttk.Checkbutton(t2, text=txt, variable=var).grid(row=r, column=0, columnspan=3, sticky="w"); r += 1
        ttk.Label(t2, text="Chiều dài jumper (mil):").grid(row=r, column=0, columnspan=2, sticky="w")
        ttk.Entry(t2, textvariable=self.v_jlen, width=10).grid(row=r, column=2); r += 1
        ttk.Label(t2, text="Số lượt rip-up/reroute:").grid(row=r, column=0, columnspan=2, sticky="w")
        ttk.Spinbox(t2, from_=1, to=10, width=6, textvariable=self.v_pass).grid(row=r, column=2)

        t3 = ttk.Frame(nb, padding=6); nb.add(t3, text="Tối ưu")
        for i, (lab, var, lo, hi, inc) in enumerate((("Vòng lặp SA", self.v_sa, 1000, 200000, 1000),
                                                     ("Vòng Binary Search", self.v_bs, 1, 12, 1),
                                                     ("Seed ngẫu nhiên", self.v_seed, 0, 9999, 1),
                                                     ("Số Seed thăm dò", self.v_multiseed, 1, 10, 1))):
            ttk.Label(t3, text=lab).grid(row=i, column=0, sticky="w")
            ttk.Spinbox(t3, from_=lo, to=hi, increment=inc, width=8, textvariable=var).grid(row=i, column=1, pady=2)
        r_opt = 4
        for txt, var in (("Khởi tạo Force-Directed (Lực lò xo)", self.v_force),
                         ("Gom cụm chức năng (Clustering)", self.v_cluster),
                         ("Ràng buộc Connector sát mép bo", self.v_edge_lock),
                         ("Ghép tụ lọc sát chân nguồn IC", self.v_decouple),
                         ("Đổi chân tương đương (Pin-Swap)", self.v_pinswap)):
            ttk.Checkbutton(t3, text=txt, variable=var).grid(row=r_opt, column=0, columnspan=2, sticky="w")
            r_opt += 1

        rf = ttk.LabelFrame(left, text="Chạy", padding=4); rf.pack(fill=tk.X, pady=6)
        for txt, cmd in (("1. Auto-Placement", self.run_place),
                         ("2. Auto-Routing", self.run_route),
                         ("3. Thu nhỏ board ôm sát (Tức thì)", self.fit_board_to_components),
                         ("4. Tự động nén board (Chỉ xếp LK)", self.run_shrink_placement_only),
                         ("5. TẤT CẢ + Thu nhỏ board (BS)", self.run_all),
                         ("Kiểm tra luật thiết kế (DRC)", self.check_drc),
                         ("Dừng", self.stop), ("Xóa đường dây", self.clear_route)):
            ttk.Button(rf, text=txt, command=cmd).pack(fill=tk.X, pady=1)
        self.status = ttk.Label(left, text="Sẵn sàng", foreground="#0a7", wraplength=240); self.status.pack(anchor="w")

        right = ttk.Frame(self.root, padding=4); right.pack(side=tk.RIGHT, fill=tk.Y)
        self.rn = ttk.Notebook(right); self.rn.pack(fill=tk.BOTH, expand=True)
        tc = ttk.Frame(self.rn); self.rn.add(tc, text="Linh kiện")
        self.tc = ttk.Treeview(tc, columns=("ref", "fp", "x", "y", "rot", "fix", "edge", "grp"), show="headings", height=14)
        for k, t, w in (("ref", "Ref", 45), ("fp", "Footprint", 75), ("x", "X mm", 50), ("y", "Y mm", 50),
                        ("rot", "Góc", 38), ("fix", "Cố định", 48), ("edge", "Mép", 38), ("grp", "Nhóm", 42)):
            self.tc.heading(k, text=t); self.tc.column(k, width=w, anchor="center")
        self.tc.pack(fill=tk.BOTH, expand=True); self.tc.bind("<<TreeviewSelect>>", self.on_comp_sel)
        ef = ttk.Frame(tc, padding=3); ef.pack(fill=tk.X)
        ttk.Label(ef, text="X").grid(row=0, column=0); ttk.Entry(ef, textvariable=self.e_x, width=7).grid(row=0, column=1)
        ttk.Label(ef, text="Y").grid(row=0, column=2); ttk.Entry(ef, textvariable=self.e_y, width=7).grid(row=0, column=3)
        ttk.Label(ef, text="Góc").grid(row=1, column=0)
        ttk.Combobox(ef, textvariable=self.e_rot, values=(0, 90, 180, 270), width=5).grid(row=1, column=1)
        ttk.Checkbutton(ef, text="Cố định", variable=self.e_fix).grid(row=1, column=2)
        ttk.Checkbutton(ef, text="Sát mép", variable=self.e_edge).grid(row=1, column=3)
        ttk.Label(ef, text="Nhóm").grid(row=2, column=0); ttk.Entry(ef, textvariable=self.e_grp, width=7).grid(row=2, column=1)
        ttk.Button(ef, text="Áp dụng", command=self.apply_comp).grid(row=2, column=2, columnspan=2, sticky="we")

        tn = ttk.Frame(self.rn); self.rn.add(tn, text="Nets")
        self.tn = ttk.Treeview(tn, columns=("net", "cls", "pins"), show="headings", height=14, selectmode="extended")
        for k, t, w in (("net", "Net", 90), ("cls", "Lớp", 100), ("pins", "Chân", 40)):
            self.tn.heading(k, text=t); self.tn.column(k, width=w, anchor="center")
        self.tn.pack(fill=tk.BOTH, expand=True)
        nf = ttk.Frame(tn, padding=3); nf.pack(fill=tk.X)
        ttk.Combobox(nf, textvariable=self.e_cls, values=list(DEFAULT_CLASSES), width=14, state="readonly").pack(side=tk.LEFT)
        ttk.Button(nf, text="Gán lớp", command=self.apply_cls).pack(side=tk.LEFT, padx=4)

        tdrc = ttk.Frame(self.rn); self.rn.add(tdrc, text="DRC (Lỗi)")
        self.tdrc = ttk.Treeview(tdrc, columns=("sev", "target", "desc", "pos"), show="headings", height=14)
        for k, t, w in (("sev", "Mức", 50), ("target", "Đối tượng", 80), ("desc", "Chi tiết vi phạm", 175), ("pos", "Tọa độ", 70)):
            self.tdrc.heading(k, text=t); self.tdrc.column(k, width=w, anchor="w" if k == "desc" else "center")
        self.tdrc.pack(fill=tk.BOTH, expand=True)
        self.tdrc.bind("<<TreeviewSelect>>", self.on_drc_sel)
        self.tdrc.bind("<Double-1>", self.on_drc_dblclick)
        drc_bar = ttk.Frame(tdrc, padding=3); drc_bar.pack(fill=tk.X)
        ttk.Button(drc_bar, text="Quét DRC ngay", command=self.check_drc).pack(side=tk.LEFT, padx=2)
        ttk.Button(drc_bar, text="Xóa đánh dấu", command=self.clear_drc_marker).pack(side=tk.RIGHT, padx=2)


        mid = ttk.Frame(self.root); mid.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tb = ttk.Frame(mid); tb.pack(fill=tk.X)
        for k, t in (("bot", "Bottom"), ("top", "Top"), ("tear", "Teardrop"), ("jump", "Jumper"),
                     ("court", "Courtyard"), ("rats", "Rat's nest"), ("label", "Nhãn")):
            ttk.Checkbutton(tb, text=t, variable=self.show[k], command=self.redraw).pack(side=tk.LEFT, padx=3)
        ttk.Button(tb, text="Vừa khung", command=self.fit).pack(side=tk.RIGHT, padx=2)
        ttk.Button(tb, text="✂ Thu nhỏ bo", command=self.fit_board_to_components).pack(side=tk.RIGHT, padx=2)
        ttk.Button(tb, text="DRC", command=self.check_drc).pack(side=tk.RIGHT, padx=2)
        ttk.Button(tb, text="⟳ 90°", command=self.rotate_selected).pack(side=tk.RIGHT, padx=1)
        ttk.Button(tb, text="↷ Redo", command=self.redo).pack(side=tk.RIGHT, padx=2)
        ttk.Button(tb, text="↶ Undo", command=self.undo).pack(side=tk.RIGHT, padx=2)

        self.cv = tk.Canvas(mid, bg=PROTEUS_COLORS["BG"], highlightthickness=0); self.cv.pack(fill=tk.BOTH, expand=True)
        self.log_t = tk.Text(mid, height=9, bg="#111", fg="#cfd8dc", font=("Consolas", 9)); self.log_t.pack(fill=tk.X)
        self.cv.bind("<ButtonPress-1>", self.on_press); self.cv.bind("<B1-Motion>", self.on_motion)
        self.cv.bind("<ButtonRelease-1>", self.on_release); self.cv.bind("<MouseWheel>", self.on_wheel)
        self.cv.bind("<Button-3>", lambda _e: self.rotate_selected())
        self.cv.bind("<Button-4>", lambda e: self.zoom(e, 1.15)); self.cv.bind("<Button-5>", lambda e: self.zoom(e, 1 / 1.15))
        self.cv.bind("<Configure>", lambda e: self.redraw())
        self.root.bind("<Control-z>", lambda _e: self.undo())
        self.root.bind("<Control-y>", lambda _e: self.redo())
        self.root.bind("<Key-r>", self._on_key_r)
        self.root.bind("<Key-R>", self._on_key_r)

    def _on_key_r(self, e):
        if isinstance(e.widget, (tk.Entry, ttk.Entry, ttk.Spinbox, ttk.Combobox, tk.Text)):
            return
        self.rotate_selected()


    def _capture_state(self):
        if not self.design:
            return None
        return (copy.deepcopy(self.design), copy.deepcopy(self.route))

    def push_undo(self):
        st = self._capture_state()
        if st is None:
            return
        self.undo_stack.append(st)
        if len(self.undo_stack) > 35:
            self.undo_stack.pop(0)
        self.redo_stack.clear()

    def undo(self):
        if not self.undo_stack or self.busy():
            return
        cur = self._capture_state()
        if cur:
            self.redo_stack.append(cur)
        d, r = self.undo_stack.pop()
        self.design, self.route = d, r
        self.v_w.set(round(d.W / MM, 1)); self.v_h.set(round(d.H / MM, 1))
        self.refresh_tables(); self.redraw()
        self.status.config(text="Đã hoàn tác (Undo)", foreground="#0a7")

    def redo(self):
        if not self.redo_stack or self.busy():
            return
        cur = self._capture_state()
        if cur:
            self.undo_stack.append(cur)
        d, r = self.redo_stack.pop()
        self.design, self.route = d, r
        self.v_w.set(round(d.W / MM, 1)); self.v_h.set(round(d.H / MM, 1))
        self.refresh_tables(); self.redraw()
        self.status.config(text="Đã làm lại (Redo)", foreground="#0a7")

    def rotate_selected(self):
        if not self.design or self.busy():
            return
        s = self.tc.selection()
        if not s:
            return
        c = self.design.comps.get(s[0])
        if not c:
            return
        self.push_undo()
        c.rotate_around_center((c.rot + 1) % 4)
        self.route = None
        auto_place_silkscreen(self.design, None)
        self.refresh_tables(); self.tc.selection_set(c.ref); self.on_comp_sel(); self.redraw()

    def check_drc(self):
        if not self._need():
            return
        self.drc_issues = run_drc(self.design, self.route, self.params())
        self.tdrc.delete(*self.tdrc.get_children())
        for idx, it in enumerate(self.drc_issues):
            pos_str = "%.1f, %.1f" % (it["x"] / MM, it["y"] / MM)
            self.tdrc.insert("", tk.END, iid=str(idx), values=(it["sev"], it["target"], it["desc"], pos_str))
        self.rn.select(2)
        err_cnt = sum(1 for it in self.drc_issues if it["sev"] == "ERROR")
        warn_cnt = sum(1 for it in self.drc_issues if it["sev"] != "ERROR")
        if not self.drc_issues:
            self.drc_marker = None
            self.log("✔ DRC hoàn tất: 0 lỗi, 0 cảnh báo. Bo mạch đạt chuẩn thiết kế!")
            self.status.config(text="DRC: Đạt chuẩn (0 lỗi)", foreground="#0a7")
        else:
            self.log(f"⚠ DRC phát hiện {err_cnt} lỗi (ERROR) và {warn_cnt} cảnh báo (WARN). Click đúp vào dòng lỗi để phóng tới vị trí.")
            self.status.config(text=f"DRC: {err_cnt} lỗi, {warn_cnt} cảnh báo", foreground="#d33" if err_cnt else "#d80")
        self.redraw()

    def clear_drc_marker(self):
        self.drc_marker = None
        self.redraw()

    def on_drc_sel(self, _e=None):
        sel = self.tdrc.selection()
        if not sel:
            return
        idx = int(sel[0])
        if 0 <= idx < len(self.drc_issues):
            it = self.drc_issues[idx]
            self.drc_marker = (it["x"], it["y"], f"{it['target']}: {it['desc']}")
            self.redraw()

    def on_drc_dblclick(self, _e=None):
        sel = self.tdrc.selection()
        if not sel:
            return
        idx = int(sel[0])
        if 0 <= idx < len(self.drc_issues):
            it = self.drc_issues[idx]
            wx, wy = it["x"], it["y"]
            self.drc_marker = (wx, wy, f"{it['target']}: {it['desc']}")
            cw = max(self.cv.winfo_width(), 200); ch = max(self.cv.winfo_height(), 200)
            sc = max(self.view[0], 0.42)
            self.view = [sc, cw * 0.5 - wx * sc, ch * 0.5 - wy * sc]
            self.redraw()

    def _sync_board_size(self):
        if not self.design or self.busy():
            return
        try:
            w = snap(max(10.0, float(self.v_w.get())) * MM)
            h = snap(max(10.0, float(self.v_h.get())) * MM)
            if w != self.design.W or h != self.design.H:
                self.design.W, self.design.H = w, h
                self.redraw()
        except Exception:
            pass

    def log(self, m):
        self.log_t.insert(tk.END, m + "\n"); self.log_t.see(tk.END)

    def params(self):
        try:
            jl = [float(x) for x in self.v_jlen.get().replace(";", ",").split(",") if x.strip()]
        except ValueError:
            jl = [200, 300]
        cls = {k: {"w": max(10, min(150, self.v_cls_w[k].get())), "c": max(0, min(80, self.v_cls_c[k].get()))}
               for k in DEFAULT_CLASSES}
        return {"classes": cls, "two_layers": self.v_two.get(), "under": self.v_under.get(),
                "use_45": self.v_45.get(), "jumpers": self.v_jump.get(), "jumper_mils": jl or [200, 300],
                "teardrop": self.v_tear.get(), "passes": self.v_pass.get(), "sa_iters": self.v_sa.get(),
                "bs_iters": self.v_bs.get(), "multi_seeds": self.v_multiseed.get(),
                "cluster": self.v_cluster.get(), "force_init": self.v_force.get(),
                "edge_constraint": self.v_edge_lock.get(), "decouple_pair": self.v_decouple.get(),
                "pin_swap": self.v_pinswap.get(), "solder_mm": self.v_solder.get(), "edge_mm": self.v_edge.get()}

    def set_design(self, d, route=None):
        auto_place_silkscreen(d, route)
        self.design, self.route = d, route
        self.drc_marker = None
        self.v_w.set(round(d.W / MM, 1)); self.v_h.set(round(d.H / MM, 1))
        self.refresh_tables(); self.fit()

    def refresh_tables(self):
        d = self.design
        self.tc.delete(*self.tc.get_children()); self.tn.delete(*self.tn.get_children())
        if not d:
            return
        for c in d.comp_list:
            self.tc.insert("", tk.END, iid=c.ref, values=(c.ref, c.fp, "%.2f" % (c.x / MM), "%.2f" % (c.y / MM),
                                                           c.rot * 90, "✔" if c.fixed else "",
                                                           "✔" if getattr(c, "edge_pref", False) else "", c.group))
        for n in d.nets.values():
            self.tn.insert("", tk.END, iid=n.name, values=(n.name, n.cls, len(n.pins)))

    def load_demo(self):
        self.undo_stack.clear(); self.redo_stack.clear()
        self.set_design(demo_design()); self.log("Đã nạp mạch mẫu NE555 (12 linh kiện, 9 net).")

    def open_netlist(self):
        p = filedialog.askopenfilename(
            title="Chọn Netlist Proteus (.SDF / .TXT / .EDF / .DSN / .PADS / .Tango)",
            filetypes=[
                ("Proteus / Netlist", "*.sdf *.txt *.edf *.dsn *.net *.tango *.asc *.pads"),
                ("Proteus Schematic SDF", "*.sdf *.txt"),
                ("Proteus ARES Specctra EDF/DSN", "*.edf *.dsn"),
                ("Tất cả", "*.*")
            ]
        )
        if not p:
            return
        try:
            comps, nets, extra_pins, placements = parse_netlist(p)
            d = Design()
            d.load(comps, nets, extra_pins=extra_pins, placements=placements)
            if not d.nets:
                raise ValueError("Không nhận dạng được net kết nối (>= 2 chân) nào trong file.")
            self.set_design(d)
            known = sum(1 for c in d.comp_list if FOOTPRINT_DB.get(c.fp) or FOOTPRINT_DB.get(c.value))
            self.log("Đã đọc %s: %d linh kiện (%d khớp kho SnapEDA/Footprint), %d net đi dây." %
                     (os.path.basename(p), len(d.comps), known, len(d.nets)))
        except Exception as ex:
            messagebox.showerror("Lỗi đọc netlist", str(ex))

    def open_footprint_db_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("Kho Dữ Liệu Footprint (SnapEDA / Proteus Library)")
        win.geometry("760x520")
        win.transient(self.root)

        top = ttk.Frame(win, padding=6)
        top.pack(fill=tk.X)
        ttk.Label(top, text="File kho: " + FOOTPRINT_DB.path, foreground="#555").pack(side=tk.LEFT)

        cols = ("name", "pins", "size", "desc")
        tv = ttk.Treeview(win, columns=cols, show="headings", height=14)
        tv.heading("name", text="Tên Footprint (PACKAGE)")
        tv.heading("pins", text="Số chân")
        tv.heading("size", text="Kích thước (mm)")
        tv.heading("desc", text="Mô tả / Ánh xạ chân")
        tv.column("name", width=210)
        tv.column("pins", width=65, anchor="center")
        tv.column("size", width=110, anchor="center")
        tv.column("desc", width=340)
        tv.pack(fill=tk.BOTH, expand=True, padx=6, pady=4)

        def refresh_db_view():
            tv.delete(*tv.get_children())
            for k in sorted(FOOTPRINT_DB.db.keys()):
                entry = FOOTPRINT_DB.db[k]
                if str(k).startswith("_") or not isinstance(entry, dict) or "pads" not in entry:
                    continue
                pads = entry.get("pads", [])
                body = entry.get("body", [-50, -50, 150, 50])
                w_mm = (body[2] - body[0]) / MM
                h_mm = (body[3] - body[1]) / MM
                pm = entry.get("pin_map", {})
                pm_preview = ", ".join(f"{pk}->{pv+1}" for pk, pv in list(pm.items())[:6] if not str(pk).startswith("EDF_"))
                desc = entry.get("desc", "")
                if pm_preview:
                    desc = (desc + " | Map: " + pm_preview).strip(" |")
                tv.insert("", tk.END, iid=k, values=(k, len(pads), "%.1f x %.1f" % (w_mm, h_mm), desc))

        refresh_db_view()

        frm = ttk.LabelFrame(win, text="Thêm / Cập nhật nhanh Footprint vào kho", padding=6)
        frm.pack(fill=tk.X, padx=6, pady=4)
        v_fp_name = tk.StringVar()
        v_fp_type = tk.StringVar(value="DIP / Module 2 hàng")
        v_fp_pins = tk.IntVar(value=16)
        v_fp_span = tk.DoubleVar(value=15.24)
        v_fp_pitch = tk.DoubleVar(value=2.54)
        v_fp_map = tk.StringVar(value="")

        ttk.Label(frm, text="Tên PACKAGE:").grid(row=0, column=0, sticky="w")
        ttk.Entry(frm, textvariable=v_fp_name, width=24).grid(row=0, column=1, padx=4, pady=2)
        ttk.Label(frm, text="Kiểu:").grid(row=0, column=2, sticky="w")
        ttk.Combobox(frm, textvariable=v_fp_type, values=("DIP / Module 2 hàng", "Header 1 hàng (SIL)", "2 chân (R/C/LED/Domino)"),
                     state="readonly", width=20).grid(row=0, column=3, padx=4)
        ttk.Label(frm, text="Số chân:").grid(row=0, column=4, sticky="w")
        ttk.Spinbox(frm, from_=2, to=128, textvariable=v_fp_pins, width=6).grid(row=0, column=5, padx=4)

        ttk.Label(frm, text="Khoảng cách 2 hàng (mm):").grid(row=1, column=0, sticky="w")
        ttk.Entry(frm, textvariable=v_fp_span, width=10).grid(row=1, column=1, sticky="w", padx=4, pady=2)
        ttk.Label(frm, text="Pitch chân (mm):").grid(row=1, column=2, sticky="w")
        ttk.Entry(frm, textvariable=v_fp_pitch, width=10).grid(row=1, column=3, sticky="w", padx=4)
        ttk.Label(frm, text="Pin map (VD: 0:1,3_3:5,G:16):").grid(row=2, column=0, sticky="w")
        ttk.Entry(frm, textvariable=v_fp_map, width=52).grid(row=2, column=1, columnspan=4, sticky="we", padx=4, pady=2)

        def save_custom_fp():
            name = v_fp_name.get().strip()
            if not name:
                messagebox.showwarning("Thiếu tên", "Hãy nhập tên PACKAGE (như khai báo trong Proteus).", parent=win)
                return
            k = max(2, int(v_fp_pins.get()))
            pitch = max(GRID, snap(float(v_fp_pitch.get()) * MM))
            span = max(GRID, snap(float(v_fp_span.get()) * MM))
            tp = v_fp_type.get()
            if "SIL" in tp:
                pads = [(i * pitch, 0) for i in range(k)]
                body = (-50, -50, (k - 1) * pitch + 50, 50)
            elif "2 chân" in tp:
                pads = [(0, 0), (span, 0)]
                body = (-50, -60, span + 50, 60)
            else:
                half = (k + 1) // 2
                pads = [(0, i * pitch) for i in range(half)] + [(span, (half - 1 - j) * pitch) for j in range(k - half)]
                body = (-60, -60, span + 60, (half - 1) * pitch + 60)
            pm = {}
            for pair in v_fp_map.get().split(","):
                if ":" in pair:
                    pk, pv = pair.split(":", 1)
                    try:
                        pm[pk.strip().upper()] = int(pv.strip()) - 1
                    except ValueError:
                        pass
            FOOTPRINT_DB.register(name, pads, body, pin_map=pm, desc="Tùy chỉnh người dùng", save_now=True)
            refresh_db_view()
            self.log(f"Đã lưu footprint '{name}' ({k} chân) vào kho dữ liệu.")

        ttk.Button(frm, text="Lưu vào Kho", command=save_custom_fp).grid(row=2, column=5, padx=4)

        btn_bar = ttk.Frame(win, padding=6)
        btn_bar.pack(fill=tk.X)

        def import_pdif_files():
            paths = filedialog.askopenfilenames(
                parent=win,
                title="Chọn các file SnapEDA (.pdif / .zip) hoặc Proteus (.edf / .dsn)",
                filetypes=[("SnapEDA / Proteus Library", "*.pdif *.zip *.edf *.dsn"), ("Tất cả", "*.*")]
            )
            if not paths:
                return
            cnt = sum(import_snapeda_file(p, save_now=False) for p in paths)
            FOOTPRINT_DB.save()
            refresh_db_view()
            messagebox.showinfo("Hoàn tất", f"Đã nạp {cnt} footprint SnapEDA vào kho dữ liệu!", parent=win)
            self.log(f"Đã nạp {cnt} footprint từ {len(paths)} file SnapEDA vào kho.")

        def scan_folder_btn():
            folder = filedialog.askdirectory(parent=win, title="Chọn thư mục chứa các file tải về từ SnapEDA (.pdif / .zip)")
            if not folder:
                return
            cnt = scan_snapeda_folder(folder, recursive=True, save_now=True)
            refresh_db_view()
            messagebox.showinfo("Hoàn tất", f"Đã quét thư mục và nạp {cnt} footprint SnapEDA vào kho!", parent=win)
            self.log(f"Đã quét '{folder}': nạp {cnt} footprint vào {FOOTPRINT_DB.path}")

        def learn_from_files():
            edf_p = filedialog.askopenfilename(
                parent=win,
                title="Chọn file .EDF / .DSN xuất từ Proteus ARES (chứa Footprint SnapEDA)",
                filetypes=[("Proteus ARES EDF/DSN", "*.edf *.dsn"), ("Tất cả", "*.*")]
            )
            if not edf_p:
                return
            sdf_p = filedialog.askopenfilename(
                parent=win,
                title="(Tùy chọn) Chọn thêm file .SDF/.TXT Schematic tương ứng để học ánh xạ tên chân (Bấm Cancel nếu bỏ qua)",
                filetypes=[("Proteus ISIS SDF/TXT", "*.sdf *.txt"), ("Tất cả", "*.*")]
            )
            try:
                cnt = learn_footprints_from_sdf_and_edf(sdf_p if sdf_p else None, edf_p)
                refresh_db_view()
                messagebox.showinfo("Thành công", f"Đã học và cập nhật {cnt} linh kiện từ file vào kho Footprint!", parent=win)
                self.log(f"Đã học {cnt} footprint từ {os.path.basename(edf_p)} vào {FOOTPRINT_DB.path}")
            except Exception as ex:
                messagebox.showerror("Lỗi", str(ex), parent=win)

        ttk.Button(btn_bar, text="📦 Nạp file SnapEDA (.pdif/.zip)…", command=import_pdif_files).pack(side=tk.LEFT, padx=3)
        ttk.Button(btn_bar, text="🔍 Quét thư mục SnapEDA…", command=scan_folder_btn).pack(side=tk.LEFT, padx=3)
        ttk.Button(btn_bar, text="📥 Học từ .EDF/.DSN (+ .SDF)…", command=learn_from_files).pack(side=tk.LEFT, padx=3)
        ttk.Button(btn_bar, text="Đóng", command=win.destroy).pack(side=tk.RIGHT, padx=4)

    def load_fixed(self):
        if not self.design:
            return
        p = filedialog.askopenfilename(filetypes=[("CSV", "*.csv")])
        if p:
            try:
                n = import_fixed_csv(self.design, p); self.route = None
                self.refresh_tables(); self.redraw(); self.log("Đã đặt cố định %d linh kiện từ CSV." % n)
            except Exception as ex:
                messagebox.showerror("Lỗi", str(ex))

    def _need(self):
        if not self.design:
            messagebox.showinfo("Thiếu dữ liệu", "Hãy nạp netlist trước."); return False
        self._sync_board_size()
        return True

    def exp_rgn(self):
        if self._need():
            p = filedialog.asksaveasfilename(
                defaultextension=".RGN",
                initialfile="proteus_layout.RGN",
                filetypes=[("Proteus ARES Region File", "*.RGN *.rgn"), ("Tất cả", "*.*")]
            )
            if p:
                export_proteus_rgn(self.design, self.route, p)
                self.log("Đã xuất Proteus ARES Region: " + p + " (Trong ARES: File -> Import Project Clip -> chọn V7 Region Files *.RGN)")

    def exp_csv(self):
        if self._need():
            p = filedialog.asksaveasfilename(defaultextension=".csv", initialfile="pick_place.csv")
            if p: export_csv(self.design, p); self.log("Đã xuất " + p)

    def exp_dxf(self):
        if self._need():
            p = filedialog.asksaveasfilename(defaultextension=".dxf", initialfile="traces.dxf")
            if p: export_dxf(self.design, self.route, p); self.log("Đã xuất " + p + "  (đơn vị mm, Y hướng lên)")

    def exp_svg(self):
        if self._need():
            p = filedialog.asksaveasfilename(defaultextension=".svg", initialfile="bottom_mirror.svg")
            if p: export_svg_bottom_mirror(self.design, self.route, p); self.log("Đã xuất " + p)

    def on_comp_sel(self, _e=None):
        s = self.tc.selection()
        if s and self.design:
            c = self.design.comps[s[0]]
            self.e_x.set(round(c.x / MM, 2)); self.e_y.set(round(c.y / MM, 2))
            self.e_rot.set(c.rot * 90); self.e_fix.set(c.fixed)
            self.e_edge.set(getattr(c, "edge_pref", False)); self.e_grp.set(c.group)

    def apply_comp(self):
        s = self.tc.selection()
        if not s or not self.design:
            return
        self.push_undo()
        c = self.design.comps[s[0]]
        c.x, c.y = snap(self.e_x.get() * MM), snap(self.e_y.get() * MM)
        c.rot = (int(self.e_rot.get()) // 90) % 4
        c.fixed = self.e_fix.get()
        c.edge_pref = self.e_edge.get()
        c.group = self.e_grp.get() or "G0"
        self.route = None
        auto_place_silkscreen(self.design, None)
        self.refresh_tables(); self.tc.selection_set(c.ref); self.redraw()

    def apply_cls(self):
        if not self.tn.selection() or not self.design:
            return
        self.push_undo()
        for iid in self.tn.selection():
            self.design.nets[iid].cls = self.e_cls.get()
        self.route = None; self.refresh_tables()

    def busy(self):
        return self.worker is not None and self.worker.is_alive()

    def start(self, job, name):
        if not self._need():
            return
        if self.busy():
            messagebox.showinfo("Đang chạy", "Hãy đợi hoặc bấm Dừng."); return
        self.push_undo()
        d = copy.deepcopy(self.design)
        d.W, d.H = snap(self.v_w.get() * MM), snap(self.v_h.get() * MM)
        P = self.params(); random.seed(self.v_seed.get()); self.cancel.clear()
        self.status.config(text="Đang chạy: " + name, foreground="#d80")
        self.log("=== " + name + " ===")

        def wrap():
            try:
                res = job(d, P)
                self.q.put(("done", d, res))
            except Exception:
                self.q.put(("err", traceback.format_exc()))
        self.worker = threading.Thread(target=wrap, daemon=True); self.worker.start()

    def post(self, d, res):
        self.q.put(("snap", copy.deepcopy(d), copy.deepcopy(res)))

    def lg(self, m):
        self.q.put(("log", m))

    def run_place(self):
        def job(d, P):
            auto_place(d, P, self.cancel, self.lg); return None
        self.start(job, "Auto-Placement")

    def run_route(self):
        def job(d, P):
            return Router(d, P, self.cancel).run(self.lg)
        self.start(job, "Auto-Routing")

    def run_all(self):
        def job(d, P):
            return optimize_board(d, P, self.cancel, self.lg, self.post)
        self.start(job, "Placement + Routing + Thu nhỏ bo")

    def run_shrink_placement_only(self):
        def job(d, P):
            return optimize_board_placement_only(d, P, self.cancel, self.lg, self.post)
        self.start(job, "Tự động nén & thu nhỏ bo (Placement)")

    def fit_board_to_components(self):
        if not self.design or not self.design.comp_list:
            return
        if self.busy():
            messagebox.showinfo("Đang bận", "Hãy đợi tác vụ hiện tại hoàn tất hoặc bấm Dừng.")
            return
        self.push_undo()
        d = self.design
        E = max(0.5, float(self.v_edge.get())) * MM

        min_x = min(c.x + c.bb[c.rot][0] - PAD_D / 2.0 for c in d.comp_list)
        min_y = min(c.y + c.bb[c.rot][1] - PAD_D / 2.0 for c in d.comp_list)
        max_x = max(c.x + c.bb[c.rot][2] + PAD_D / 2.0 for c in d.comp_list)
        max_y = max(c.y + c.bb[c.rot][3] + PAD_D / 2.0 for c in d.comp_list)

        if self.route:
            for _net, _l, pts, _w in getattr(self.route, "segs", []):
                for px, py in pts:
                    if px < min_x: min_x = px
                    if px > max_x: max_x = px
                    if py < min_y: min_y = py
                    if py > max_y: max_y = py
            for vx, vy, _n in getattr(self.route, "vias", []):
                min_x = min(min_x, vx - VIA_D / 2.0)
                max_x = max(max_x, vx + VIA_D / 2.0)
                min_y = min(min_y, vy - VIA_D / 2.0)
                max_y = max(max_y, vy + VIA_D / 2.0)
            for _n, a, b in getattr(self.route, "jumps", []):
                min_x = min(min_x, a[0] - VIA_D / 2.0, b[0] - VIA_D / 2.0)
                max_x = max(max_x, a[0] + VIA_D / 2.0, b[0] + VIA_D / 2.0)
                min_y = min(min_y, a[1] - VIA_D / 2.0, b[1] - VIA_D / 2.0)
                max_y = max(max_y, a[1] + VIA_D / 2.0, b[1] + VIA_D / 2.0)

        shift_x = snap(E - min_x)
        shift_y = snap(E - min_y)

        for c in d.comp_list:
            c.x = snap(c.x + shift_x)
            c.y = snap(c.y + shift_y)

        if self.route:
            new_segs = []
            for net, l, pts, w in self.route.segs:
                new_segs.append((net, l, [(p[0] + shift_x, p[1] + shift_y) for p in pts], w))
            self.route.segs = new_segs
            self.route.vias = [(v[0] + shift_x, v[1] + shift_y, v[2]) for v in self.route.vias]
            self.route.jumps = [(j[0], (j[1][0] + shift_x, j[1][1] + shift_y), (j[2][0] + shift_x, j[2][1] + shift_y))
                                for j in self.route.jumps]
            if hasattr(self.route, "tears"):
                self.route.tears = [(l, [(p[0] + shift_x, p[1] + shift_y) for p in poly])
                                    for l, poly in self.route.tears]

        new_w = max(400, int(round((max_x - min_x + 2 * E) / 50.0)) * 50)
        new_h = max(400, int(round((max_y - min_y + 2 * E) / 50.0)) * 50)
        old_w, old_h = d.W, d.H
        d.W, d.H = new_w, new_h
        self.v_w.set(round(d.W / MM, 1))
        self.v_h.set(round(d.H / MM, 1))
        auto_place_silkscreen(d, self.route)
        self.refresh_tables()
        self.fit()
        self.redraw()
        pct = 100.0 * (1.0 - (new_w * new_h) / float(old_w * old_h)) if (old_w * old_h) > 0 else 0.0
        self.log("✂ Đã thu nhỏ bo ôm sát: %.1f x %.1f mm (giảm %.0f%% diện tích bo)." %
                 (new_w / MM, new_h / MM, pct))
        self.status.config(text=f"Đã thu nhỏ bo: {new_w/MM:.1f} x {new_h/MM:.1f} mm", foreground="#0a7")

    def stop(self):
        self.cancel.set(); self.log("Đã yêu cầu dừng…")

    def clear_route(self):
        if self.route is not None:
            self.push_undo()
        self.route = None; self.redraw()

    def poll(self):
        try:
            while True:
                m = self.q.get_nowait()
                if m[0] == "log":
                    self.log(m[1])
                elif m[0] == "snap":
                    self.design, self.route = m[1], m[2]; self.redraw()
                elif m[0] == "done":
                    self.set_design(m[1], m[2]); self.status.config(text="Hoàn tất", foreground="#0a7")
                elif m[0] == "err":
                    self.log(m[1]); self.status.config(text="Lỗi", foreground="#d33")
        except queue.Empty:
            pass
        self.root.after(100, self.poll)

    def fit(self):
        d = self.design
        if not d:
            return
        w = max(self.cv.winfo_width(), 200); h = max(self.cv.winfo_height(), 200)
        sc = min((w - 40) / float(d.W), (h - 40) / float(d.H))
        self.view = [sc, (w - d.W * sc) / 2, (h - d.H * sc) / 2]; self.redraw()

    def s2w(self, sx, sy):
        sc, ox, oy = self.view
        return (sx - ox) / sc, (sy - oy) / sc

    def zoom(self, e, f):
        sc, ox, oy = self.view
        wx, wy = self.s2w(e.x, e.y)
        sc = max(0.02, min(5.0, sc * f)); self.view = [sc, e.x - wx * sc, e.y - wy * sc]; self.redraw()

    def on_wheel(self, e):
        self.zoom(e, 1.15 if e.delta > 0 else 1 / 1.15)

    def hit(self, wx, wy):
        for c in reversed(self.design.comp_list):
            bb = c.bb[c.rot]
            if c.x + bb[0] - 30 <= wx <= c.x + bb[2] + 30 and c.y + bb[1] - 30 <= wy <= c.y + bb[3] + 30:
                return c
        return None

    def on_press(self, e):
        self.drag = self.pan = None
        if not self.design or self.busy():
            return
        wx, wy = self.s2w(e.x, e.y); c = self.hit(wx, wy)
        if c:
            self.drag = (c, wx - c.x, wy - c.y, c.x, c.y, self._capture_state())
            self.tc.selection_set(c.ref); self.tc.see(c.ref)
            self.on_comp_sel()
            self.redraw()
        else:
            self.pan = (e.x, e.y, self.view[1], self.view[2])

    def on_motion(self, e):
        if self.drag:
            c, dx, dy, _ox, _oy, _st = self.drag
            wx, wy = self.s2w(e.x, e.y)
            nx_pos, ny_pos = snap(wx - dx), snap(wy - dy)
            if nx_pos != c.x or ny_pos != c.y:
                c.x, c.y = nx_pos, ny_pos
                self.route = None
                E_rats = ratsnest(self.design)
                cr = count_cross(E_rats)
                self.status.config(
                    text=f"Đang kéo {c.ref} ({c.x/MM:.1f}, {c.y/MM:.1f} mm) | Giao cắt Rat's nest: {cr}",
                    foreground="#00bcd4"
                )
                self.redraw()
        elif self.pan:
            x0, y0, ox, oy = self.pan; self.view[1] = ox + e.x - x0; self.view[2] = oy + e.y - y0; self.redraw()

    def on_release(self, _e):
        if self.drag:
            c, _dx, _dy, ox, oy, pre_state = self.drag
            if (c.x != ox or c.y != oy) and pre_state is not None:
                self.undo_stack.append(pre_state)
                if len(self.undo_stack) > 35:
                    self.undo_stack.pop(0)
                self.redo_stack.clear()
                auto_place_silkscreen(self.design, None)
            self.drag = None
            self.refresh_tables(); self.tc.selection_set(c.ref); self.on_comp_sel(); self.redraw()
        self.pan = None

    def redraw(self):
        cv = self.cv; cv.delete("all"); d = self.design
        if not d:
            return
        sc, ox, oy = self.view
        X = lambda x: ox + x * sc
        Y = lambda y: oy + y * sc
        cv.create_rectangle(X(0), Y(0), X(d.W), Y(d.H), outline=PROTEUS_COLORS["BOARD_EDGE"], width=2)
        s = {k: v.get() for k, v in self.show.items()}
        m = (self.v_solder.get() * MM / 2.0)
        dragging_c = self.drag[0] if self.drag else None

        for c in d.comp_list:
            bb = c.bb[c.rot]; e = PAD_D / 2.0 + m
            if s["court"]:
                outline_col = "#00e5ff" if c is dragging_c else ("#e67e22" if c.fixed else ("#2ecc71" if getattr(c, "edge_pref", False) else "#566573"))
                cv.create_rectangle(X(c.x + bb[0] - e), Y(c.y + bb[1] - e), X(c.x + bb[2] + e), Y(c.y + bb[3] + e),
                                    outline=outline_col, dash=(3, 3))
            bp = c.body_poly()
            if bp:
                cv.create_polygon([v for p in bp for v in (X(p[0]), Y(p[1]))], outline=PROTEUS_COLORS["SILK"], fill="", width=1)
        r = self.route
        pad_map = _pad_snap_to_exact_map(d)
        if r:
            for net, l, pts, w in r.segs:
                if (l == 0 and s["bot"]) or (l == 1 and s["top"]):
                    adj_pts = _adjust_seg_pts(pts, pad_map)
                    cv.create_line([v for p in adj_pts for v in (X(p[0]), Y(p[1]))], width=max(1, w * sc),
                                   fill=PROTEUS_COLORS["BOT_COPPER"] if l == 0 else PROTEUS_COLORS["TOP_COPPER"],
                                   capstyle=tk.ROUND, joinstyle=tk.ROUND)
            if s["tear"]:
                for l, poly in r.tears:
                    cv.create_polygon([v for p in poly for v in (X(p[0]), Y(p[1]))],
                                      fill=PROTEUS_COLORS["BOT_COPPER"] if l == 0 else PROTEUS_COLORS["TOP_COPPER"], outline="")
            for x, y, n in r.vias:
                cv.create_oval(X(x) - VIA_D / 2 * sc, Y(y) - VIA_D / 2 * sc, X(x) + VIA_D / 2 * sc, Y(y) + VIA_D / 2 * sc, fill="#9b59b6", outline="")
            if s["jump"]:
                for n, a, b in r.jumps:
                    cv.create_line(X(a[0]), Y(a[1]), X(b[0]), Y(b[1]), fill="#2ecc71", width=max(2, 8 * sc), capstyle=tk.ROUND)
                    for p in (a, b):
                        cv.create_oval(X(p[0]) - 30 * sc, Y(p[1]) - 30 * sc, X(p[0]) + 30 * sc, Y(p[1]) + 30 * sc, fill="#d4ac0d", outline="")
        for c in d.comp_list:
            for i in range(len(c.pads)):
                x, y = c.pad_exact_abs(i); rr = PAD_D / 2.0 * sc; hh = HOLE_D / 2.0 * sc
                if c.is_square_pin(i):
                    cv.create_rectangle(X(x) - rr, Y(y) - rr, X(x) + rr, Y(y) + rr, fill=PROTEUS_COLORS["PAD"], outline="")
                else:
                    cv.create_oval(X(x) - rr, Y(y) - rr, X(x) + rr, Y(y) + rr, fill=PROTEUS_COLORS["PAD"], outline="")
                cv.create_oval(X(x) - hh, Y(y) - hh, X(x) + hh, Y(y) + hh, fill=PROTEUS_COLORS["PAD_HOLE"], outline="")
                if s["label"] and sc >= 0.22:
                    pin_txt = c.pad_names.get(i, str(i + 1))
                    cv.create_text(X(x), Y(y) - rr - 5, text=pin_txt, fill=PROTEUS_COLORS["PIN_TEXT"],
                                   font=("Consolas", max(6, int(22 * sc))))

        if dragging_c is not None:
            active_nets = set(dragging_c.pin_net.values())
            for n, a, b in ratsnest(d):
                is_act = n in active_nets
                if s["rats"] or is_act:
                    cv.create_line(
                        X(a[0]), Y(a[1]), X(b[0]), Y(b[1]),
                        fill="#00FF66" if is_act else "#3a7a40",
                        width=1.8 if is_act else 1.0,
                        dash=(3, 2) if is_act else (2, 3)
                    )
        elif s["rats"]:
            bad = set(r.failed) if r else None
            for n, a, b in ratsnest(d):
                if bad is None or n in bad:
                    cv.create_line(X(a[0]), Y(a[1]), X(b[0]), Y(b[1]),
                                   fill="#f39c12" if bad else PROTEUS_COLORS["RATS_NEST"], dash=(2, 2))
        elif r and r.failed:
            for n, a, b in ratsnest(d):
                if n in r.failed:
                    cv.create_line(X(a[0]), Y(a[1]), X(b[0]), Y(b[1]), fill="#f39c12", dash=(2, 2))

        if s["label"]:
            for c in d.comp_list:
                lx, ly = c.label_abs()
                cv.create_text(X(lx), Y(ly), text=c.ref,
                               fill=PROTEUS_COLORS["REF_TEXT"], font=("Arial", max(7, int(65 * sc)), "bold"))

        if self.drc_marker:
            mx, my, mdesc = self.drc_marker
            sx, sy = X(mx), Y(my)
            r1 = max(14, 95 * sc)
            r2 = max(22, 150 * sc)
            cv.create_oval(sx - r1, sy - r1, sx + r1, sy + r1, outline="#ff1744", width=2.5)
            cv.create_oval(sx - r2, sy - r2, sx + r2, sy + r2, outline="#ffea00", width=1.8, dash=(4, 3))
            cv.create_line(sx - r2 - 6, sy, sx + r2 + 6, sy, fill="#ffea00", width=1)
            cv.create_line(sx, sy - r2 - 6, sx, sy + r2 + 6, fill="#ffea00", width=1)
            cv.create_text(sx, sy - r2 - 12, text=mdesc, fill="#ffea00", font=("Consolas", 9, "bold"))

def headless(netlist=None, outdir="out"):
    if netlist:
        comps, nets, extra_pins, placements = parse_netlist(netlist)
        d = Design()
        d.load(comps, nets, extra_pins=extra_pins, placements=placements)
    else:
        d = demo_design()
    P = {"classes": copy.deepcopy(DEFAULT_CLASSES), "two_layers": False, "under": True, "use_45": True,
         "jumpers": True, "jumper_mils": [200, 300], "teardrop": True, "passes": 3, "sa_iters": 15000,
         "bs_iters": 6, "multi_seeds": 2, "cluster": True, "force_init": True,
         "edge_constraint": True, "decouple_pair": True, "pin_swap": True,
         "solder_mm": 2.0, "edge_mm": 1.5}
    random.seed(1); ev = threading.Event()
    res = optimize_board(d, P, ev, print)
    issues = run_drc(d, res, P)
    print(f"  DRC Check: {len(issues)} cảnh báo/lỗi.")
    os.makedirs(outdir, exist_ok=True)
    export_csv(d, os.path.join(outdir, "pick_place.csv"))
    export_dxf(d, res, os.path.join(outdir, "traces.dxf"))
    export_svg_bottom_mirror(d, res, os.path.join(outdir, "bottom_mirror.svg"))
    export_proteus_rgn(d, res, os.path.join(outdir, "proteus_layout.RGN"))
    print("Đã xuất file vào", outdir)
    return d, res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--headless", action="store_true")
    ap.add_argument("args", nargs="*")
    a = ap.parse_args()
    if a.headless:
        headless(a.args[0] if a.args else None, a.args[1] if len(a.args) > 1 else "out"); return
    if not HAVE_TK:
        print("Máy chưa có tkinter. Linux: sudo apt install python3-tk  |  hoặc dùng --headless"); return
    root = tk.Tk(); App(root); root.mainloop()


if __name__ == "__main__":
    main()

