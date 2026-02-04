import sys
import os
import glob
import json
import shutil
import colorsys
import platform
import numpy as np
import tkinter as tk
from tkinter import filedialog, ttk, Menu, messagebox
import xml.etree.ElementTree as ET
from functools import lru_cache
from pathlib import Path
import io

import matplotlib

matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from PIL import Image

import ctypes
from ctypes import wintypes


# =============================================================================
# 1. 
# =============================================================================

def _lname(tag): return tag.split("}", 1)[1] if "}" in tag else tag


def _parent_map(root): return {c: p for p in root.iter() for c in p}


def _extract_counts(root):
    for el in root.iter():
        if _lname(el.tag) in ("counts", "intensities"):
            txt = (el.text or "").strip()
            if txt:
                arr = np.fromstring(" ".join(txt.split()), sep=" ")
                if arr.size > 0: return el, arr
    raise ValueError("counts/intensities not found")


def _find_positions(root, counts_el, pmap):
    anc = []
    cur = counts_el
    while cur in pmap:
        cur = pmap[cur]
        anc.append(cur)

    def _search(node):
        cands = []
        for el in node.iter():
            if _lname(el.tag) == "positions":
                axis = (el.attrib.get("axis") or "").lower()
                cands.append((("2theta" in axis), el))
        for prefer in (True, False):
            for is2t, pos in cands:
                if prefer and not is2t: continue
                s = e = None
                for ch in pos:
                    tag = _lname(ch.tag)
                    if tag == "startPosition":
                        s = ch
                    elif tag == "endPosition":
                        e = ch
                if s is not None and e is not None:
                    def to_deg(x):
                        v = float((x.text or "").strip())
                        u = (x.attrib.get("unit") or "").lower()
                        return np.degrees(v) if u in ("rad", "radian", "radians") else v

                    return to_deg(s), to_deg(e)
        return None

    for a in anc:
        if _lname(a.tag) == "positions":
            r = _search(a)
            if r: return r
    for a in anc:
        if _lname(a.tag) == "dataPoints": r = _search(a);
        if r: return r
    for a in anc:
        if _lname(a.tag) == "scan": r = _search(a);
        if r: return r
    r = _search(root)
    if r is None: raise ValueError("Positions not found")
    return r


@lru_cache(maxsize=256)
def load_xrdml(path):
    try:
        tree = ET.parse(path)
        root = tree.getroot()
        pmap = _parent_map(root)
        c_el, counts = _extract_counts(root)
        s, e = _find_positions(root, c_el, pmap)
        tt = np.linspace(s, e, counts.size)
        return tt.astype(float), counts.astype(float)
    except Exception as e:
        print(f"Read Error {os.path.basename(path)}: {e}")
        return np.array([]), np.array([])


# --- DATA STORAGE ---
SUBSTRATES = {}
FILES = {}

# Load Substrates
if getattr(sys, "frozen", False):
    BASE_DIR = os.path.dirname(sys.executable)
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
SUB_DIR = os.path.join(BASE_DIR, "substrates")
if not os.path.exists(SUB_DIR):
    try:
        os.makedirs(SUB_DIR)
    except:
        pass
else:
    for f in glob.glob(os.path.join(SUB_DIR, "*.xrdml")):
        nm = os.path.splitext(os.path.basename(f))[0]
        tt, ii = load_xrdml(f)
        if tt.size > 0: SUBSTRATES[nm] = {"mode": "curve", "two_theta_deg": tt, "intensity": ii}

if not SUBSTRATES:
    SUBSTRATES["No_Substrates"] = {"mode": "curve", "two_theta_deg": np.linspace(10, 80, 100),
                                   "intensity": np.zeros(100)}

# Presets
PRESET_PATH = Path(BASE_DIR) / "substrate_view_presets.json"
PRESETS = {}
if PRESET_PATH.exists():
    try:
        PRESETS = json.loads(PRESET_PATH.read_text("utf-8"))
    except:
        pass


def get_preset(name):
    if name in PRESETS: return PRESETS[name]
    for k in sorted(PRESETS.keys(), key=len, reverse=True):
        if name.startswith(k):
            s = name[len(k):]
            if s == "_copy" or (s.startswith("_") and s[1:].isdigit()): return PRESETS[k]
    return None


def get_xy(kind, name):
    if kind == "substrate":
        d = SUBSTRATES.get(name)
        return (d["two_theta_deg"], d["intensity"], "substrate") if d else ([], [], "")
    p = FILES.get(name)
    if not p: return [], [], "file"
    t, i = load_xrdml(p)
    return t, i, "file"


def get_palette(n, base):
    if n <= len(base): return base[:n]
    return base + [matplotlib.colors.to_hex(colorsys.hsv_to_rgb((i + 0.15) / (n - len(base) + 0.3), 0.7, 0.9)) for i in
                   range(n - len(base))]


# =============================================================================
# 2. 
# =============================================================================

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("XRD Tool")
        self.geometry("1000x700")

        # --- STATE ---
        self.items = []
        self.item_by_btn = {}
        self.groups = {}
        self.group_active = {}
        self.next_gid = 1
        self.drag_data = {"btn": None, "sx": 0, "sy": 0, "moved": False}
        self.reset_counter = 0  # <--- СЧЕТЧИК ПАСХАЛКИ

        self.next_sub_y = 40
        self.next_file_y = 40
        self.col_sub_x = 20
        self.col_file_x = 400

        # --- GUI STRUCTURE ---
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill="both", expand=True)

        # TAB 1: WORKSPACE
        self.tab_ws = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_ws, text="  📍 Workspace  ")

        self.ctrl_panel = ttk.Frame(self.tab_ws, padding=5, relief="raised")
        self.ctrl_panel.pack(side="left", fill="y")

        ttk.Button(self.ctrl_panel, text="📄 Load Files...", command=self.load_files).pack(fill="x", pady=2)
        ttk.Button(self.ctrl_panel, text="📂 Load Folder...", command=self.load_folder).pack(fill="x", pady=2)
        ttk.Separator(self.ctrl_panel, orient="horizontal").pack(fill="x", pady=10)

        self.btn_reset = ttk.Button(self.ctrl_panel, text="Reset Layout", command=self.reset_layout)
        self.btn_reset.pack(fill="x", pady=5)

        self.ws_area = tk.Frame(self.tab_ws, bg="#f0f0f0")
        self.ws_area.pack(side="right", fill="both", expand=True)

        tk.Label(self.ws_area, text="Substrates (Right-Click to Clone)", bg="#f0f0f0",
                 font=("Arial", 10, "bold")).place(x=self.col_sub_x, y=10)
        tk.Label(self.ws_area, text="Files (Drag to Connect)", bg="#f0f0f0", font=("Arial", 10, "bold")).place(
            x=self.col_file_x, y=10)

        # TAB 2: GALLERY
        self.tab_gal = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_gal, text="  📊 Gallery & Results  ")

        self.gal_canvas = tk.Canvas(self.tab_gal)
        self.gal_scroll = ttk.Scrollbar(self.tab_gal, orient="vertical", command=self.gal_canvas.yview)
        self.gal_frame = ttk.Frame(self.gal_canvas)

        self.gal_frame.bind("<Configure>",
                            lambda e: self.gal_canvas.configure(scrollregion=self.gal_canvas.bbox("all")))
        self.gal_canvas.create_window((0, 0), window=self.gal_frame, anchor="nw")
        self.gal_canvas.configure(yscrollcommand=self.gal_scroll.set)

        self.gal_canvas.pack(side="top", fill="both", expand=True)
        self.gal_scroll.pack(side="right", fill="y", in_=self.gal_canvas)

        self.bot_bar = ttk.Frame(self.tab_gal, padding=5)
        self.bot_bar.pack(side="bottom", fill="x")
        ttk.Button(self.bot_bar, text="Load Presets", command=self.load_presets_dialog).pack(side="left", padx=5)
        ttk.Button(self.bot_bar, text="Save Presets", command=self.save_presets_dialog).pack(side="left", padx=5)
        ttk.Button(self.bot_bar, text="Update Gallery", command=self.refresh_gallery).pack(side="right", padx=5)

        self.init_substrates()
        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_change)

        self.ctx_menu = Menu(self, tearoff=0)
        self.ctx_menu.add_command(label="Duplicate", command=self.duplicate_substrate_action)

    # --- LOGIC ---

    class Item:
        def __init__(self, kind, name, btn, x, y):
            self.kind = kind;
            self.name = name;
            self.btn = btn
            self.group = None;
            self.active = False
            self.x, self.y = x, y;
            self.hx, self.hy = x, y

    def make_btn(self, txt, x, y, kind):
        b = tk.Button(self.ws_area, text=txt, width=28, pady=6, bg="#d0d0d0", relief="raised")
        b.place(x=x, y=y)
        it = self.Item(kind, txt, b, x, y)
        self.items.append(it)
        self.item_by_btn[b] = it

        b.bind("<Button-1>", lambda e, btn=b: self.on_press(e, btn))
        b.bind("<B1-Motion>", lambda e, btn=b: self.on_motion(e, btn))
        b.bind("<ButtonRelease-1>", lambda e, btn=b: self.on_release(e, btn))

        if kind == "substrate":
            b.bind("<Button-3>", lambda e, n=txt: self.show_ctx_menu(e, n))
        return b

    def init_substrates(self):
        for nm in sorted(SUBSTRATES.keys()):
            self.make_btn(nm, self.col_sub_x, self.next_sub_y, "substrate")
            self.next_sub_y += 36

    def load_files(self):
        paths = filedialog.askopenfilenames(title="Select .xrdml files",
                                            filetypes=[("XRDML", "*.xrdml"), ("All", "*.*")])
        if not paths: return
        for p in paths:
            nm = os.path.basename(p)
            if nm not in FILES:
                FILES[nm] = p
                self.make_btn(nm, self.col_file_x, self.next_file_y, "file")
                self.next_file_y += 36

    def load_folder(self):
        d = filedialog.askdirectory(title="Select Folder with XRDML")
        if not d: return
        for f in os.listdir(d):
            if f.lower().endswith(".xrdml"):
                p = os.path.join(d, f)
                nm = os.path.basename(p)
                if nm not in FILES:
                    FILES[nm] = p
                    self.make_btn(nm, self.col_file_x, self.next_file_y, "file")
                    self.next_file_y += 36

    def show_ctx_menu(self, event, name):
        self.ctx_menu.entryconfigure(0, label=f"Duplicate '{name}'")
        self.ctx_menu.post(event.x_root, event.y_root)

    def duplicate_substrate_action(self):
        src = self.ctx_menu.entrycget(0, "label").replace("Duplicate '", "").replace("'", "")
        if src not in SUBSTRATES: return
        cnt = 1
        new_name = f"{src}_{cnt}"
        while new_name in SUBSTRATES:
            cnt += 1;
            new_name = f"{src}_{cnt}"
        SUBSTRATES[new_name] = SUBSTRATES[src]
        self.make_btn(new_name, self.col_sub_x, self.next_sub_y, "substrate")
        self.next_sub_y += 36

    def reset_layout(self):
        # 1. Основная функция - сброс
        self.groups.clear();
        self.group_active.clear()
        for it in self.items:
            it.group = None;
            it.active = False
            it.btn.configure(bg="#d0d0d0", relief="raised", bd=1)
            it.x, it.y = it.hx, it.hy
            it.btn.place(x=it.x, y=it.y)

        self.reset_counter += 1
        if self.reset_counter == 10:
            self.show_easter_egg()
            self.reset_counter = 0  # Сброс после активации

    def show_easter_egg(self):
        top = tk.Toplevel(self)
        top.title("About Author")
        top.geometry("350x200")
        top.resizable(False, False)

        x = self.winfo_x() + (self.winfo_width() // 2) - 175
        y = self.winfo_y() + (self.winfo_height() // 2) - 100
        top.geometry(f"+{x}+{y}")

        style_font = ("Consolas", 11)
        bg_col = "#202020"
        fg_col = "#00ff00"  # Hacker style green

        top.configure(bg=bg_col)

        tk.Label(top, text="CREATED BY", font=("Arial", 8, "bold"), fg="#808080", bg=bg_col).pack(pady=(20, 5))
        tk.Label(top, text="Mikhail D. Mirus(h)chenko", font=("Arial", 14, "bold"), fg="#ffffff", bg=bg_col).pack()
        tk.Label(top, text="ofussr", font=style_font, fg=fg_col, bg=bg_col).pack(pady=5)
        tk.Label(top, text="miruschenko98@gmail.com", font=("Arial", 10), fg="#a0a0a0", bg=bg_col).pack(pady=10)

        tk.Button(top, text="Close", command=top.destroy, bg="#404040", fg="white", relief="flat").pack(pady=10)

    def on_press(self, e, btn):
        btn.lift()
        self.drag_data.update(
            {"btn": btn, "sx": btn.winfo_x() - e.x_root, "sy": btn.winfo_y() - e.y_root, "moved": False,
             "px": btn.winfo_x(), "py": btn.winfo_y()})

    def on_motion(self, e, btn):
        if self.drag_data["btn"] is not btn: return
        nx, ny = self.drag_data["sx"] + e.x_root, self.drag_data["sy"] + e.y_root
        if abs(nx - self.drag_data["px"]) > 3 or abs(ny - self.drag_data["py"]) > 3: self.drag_data["moved"] = True
        btn.place(x=nx, y=ny)
        self.item_by_btn[btn].x, self.item_by_btn[btn].y = nx, ny

    def on_release(self, e, btn):
        src = self.item_by_btn[btn]
        if not self.drag_data["moved"]:
            if src.group:
                self.set_group_active(src.group, not self.group_active[src.group])
            else:
                self.set_item_active(src, not src.active)
            self.drag_data["btn"] = None;
            return

        hits = []
        ax1, ay1, ax2, ay2 = btn.winfo_x(), btn.winfo_y(), btn.winfo_x() + btn.winfo_width(), btn.winfo_y() + btn.winfo_height()
        for it in self.items:
            if it is src: continue
            bx1, by1, bx2, by2 = it.btn.winfo_x(), it.btn.winfo_y(), it.btn.winfo_x() + it.btn.winfo_width(), it.btn.winfo_y() + it.btn.winfo_height()
            if not (ax2 <= bx1 or bx2 <= ax1 or ay2 <= by1 or by2 <= ay1):
                area = max(0, min(ax2, bx2) - max(ax1, bx1)) * max(0, min(ay2, by2) - max(ay1, by1))
                hits.append((it, area))
        hits.sort(key=lambda x: x[1], reverse=True)

        if hits:
            tgt = hits[0][0]
            if not src.group and not tgt.group:
                gid = self.create_group(src, tgt)
            elif src.group and not tgt.group:
                self.add_to_group(src.group, tgt); gid = src.group
            elif not src.group and tgt.group:
                self.add_to_group(tgt.group, src); gid = tgt.group
            else:
                gid = self.merge_groups(src.group, tgt.group)
            self.layout_group(gid, tgt.btn.winfo_x(), min(src.btn.winfo_y(), tgt.btn.winfo_y()))
        else:
            if src.group:
                overlaps = False
                for other in self.groups[src.group]:
                    if other is src: continue
                    bx1, by1, bx2, by2 = other.btn.winfo_x(), other.btn.winfo_y(), other.btn.winfo_x() + other.btn.winfo_width(), other.btn.winfo_y() + other.btn.winfo_height()
                    if not (ax2 <= bx1 or bx2 <= ax1 or ay2 <= by1 or by2 <= ay1): overlaps = True; break
                if not overlaps: self.remove_from_group(src)
        self.drag_data["btn"] = None

    def set_item_active(self, it, v):
        it.active = v;
        it.btn.configure(bg="#2ecc71" if v else "#d0d0d0", relief="solid" if v else "raised", bd=2 if v else 1)

    def set_group_active(self, gid, v):
        self.group_active[gid] = v
        for it in self.groups[gid]: self.set_item_active(it, v)

    def layout_group(self, gid, ax, ay):
        mems = sorted(list(self.groups[gid]), key=lambda i: (0 if i.kind == "file" else 1, i.name))
        y = ay
        for m in mems:
            m.x, m.y = ax, y
            m.btn.place(x=ax, y=y);
            y += m.btn.winfo_height()

    def create_group(self, *mems):
        gid = self.next_gid;
        self.next_gid += 1
        self.groups[gid] = set(mems);
        self.group_active[gid] = True
        for m in mems: m.group = gid; self.set_item_active(m, True)
        self.layout_group(gid, mems[0].btn.winfo_x(), mems[0].btn.winfo_y())
        return gid

    def add_to_group(self, gid, it):
        self.groups[gid].add(it);
        it.group = gid
        self.set_item_active(it, self.group_active[gid])
        self.layout_group(gid, next(iter(self.groups[gid])).btn.winfo_x(), next(iter(self.groups[gid])).btn.winfo_y())

    def merge_groups(self, ga, gb):
        if ga == gb: return ga
        for m in list(self.groups[gb]): m.group = ga; self.groups[ga].add(m)
        self.group_active[ga] = self.group_active[ga] or self.group_active[gb]
        del self.groups[gb];
        del self.group_active[gb]
        self.layout_group(ga, next(iter(self.groups[ga])).btn.winfo_x(), next(iter(self.groups[ga])).btn.winfo_y())
        return ga

    def remove_from_group(self, it):
        gid = it.group;
        self.groups[gid].discard(it);
        it.group = None
        self.layout_group(gid, next(iter(self.groups[gid])).btn.winfo_x(), next(iter(self.groups[gid])).btn.winfo_y())
        if len(self.groups[gid]) < 2:
            rem = next(iter(self.groups[gid]));
            rem.group = None
            del self.groups[gid];
            del self.group_active[gid]
            self.set_item_active(rem, False)

    def on_tab_change(self, event):
        if self.notebook.index("current") == 1: self.refresh_gallery()

    def refresh_gallery(self):
        for w in self.gal_frame.winfo_children(): w.destroy()
        assemblies = []
        for gid, mems in self.groups.items():
            if not self.group_active[gid]: continue
            assemblies.append({
                "label": " + ".join([m.name for m in mems]),
                "items": [{"kind": m.kind, "name": m.name} for m in mems],
                "view": {}
            })
        if not assemblies:
            ttk.Label(self.gal_frame, text="No active groups created in Workspace.").pack(pady=20)
            return
        cols = 2
        for i, asm in enumerate(assemblies):
            r, c = divmod(i, cols)
            fr = ttk.Frame(self.gal_frame, relief="groove", padding=5)
            fr.grid(row=r, column=c, padx=10, pady=10, sticky="nsew")
            ttk.Label(fr, text=asm["label"][:45], font=("Arial", 9, "bold")).pack(anchor="w")
            fig = plt.Figure(figsize=(4, 2.2), dpi=80)
            ax = fig.add_subplot(111)
            fig.subplots_adjust(left=0.1, right=0.95, top=0.95, bottom=0.15)
            self.plot_assembly(ax, asm, thumb=True)
            cv = FigureCanvasTkAgg(fig, fr)
            cv.get_tk_widget().pack(fill="both", expand=True)
            cv.get_tk_widget().bind("<Button-1>", lambda e, a=asm: self.open_viewer(a))
            b_row = ttk.Frame(fr)
            b_row.pack(fill="x", pady=2)
            ttk.Button(b_row, text="Open", command=lambda a=asm: self.open_viewer(a)).pack(side="right")
            ttk.Button(b_row, text="Copy", command=lambda a=asm: self.copy_clipboard(a)).pack(side="right", padx=5)
        for i in range(cols): self.gal_frame.columnconfigure(i, weight=1)

    def plot_assembly(self, ax, asm, view=None, thumb=False):
        view = view or asm.get("view", {})
        ymode = view.get("ymode", "log")
        ax.clear()
        files = [i for i in asm["items"] if i["kind"] == "file"]
        subs = [i for i in asm["items"] if i["kind"] == "substrate"]
        fc = get_palette(len(files),
                         ["#e31a1c"] if len(files) == 1 else ["#a6cee3", "#1f78b4", "#b2df8a", "#33a02c", "#fb9a99"])
        sc = get_palette(len(subs), ["#000000"] if len(subs) == 1 else ["#000000", "#404040", "#7f7f7f"])
        cmap = {**dict(zip([f["name"] for f in files], fc)), **dict(zip([s["name"] for s in subs], sc))}
        for it in sorted(asm["items"], key=lambda x: 0 if x["kind"] == "substrate" else 1):
            x, y, k = get_xy(it["kind"], it["name"])
            if len(x) == 0: continue
            if ymode == "log":
                eps = max(1e-12, float(np.nanmin(y[y > 0])) * 1e-6 if np.any(y > 0) else 1e-12)
                y = np.clip(y, eps, None)
            elif ymode == "exp":
                y = np.exp(y / (np.nanmax(y) or 1.))
            elif ymode == "square":
                y = np.power(np.maximum(y, 0), 2)
            ax.plot(x, y, label=it["name"], color=cmap.get(it["name"], "k"),
                    lw=1.0 if thumb else 1.3, zorder=2 if k == "substrate" else 3)
        if view.get("xlim"):
            ax.set_xlim(view["xlim"]); ax.set_ylim(view["ylim"])
        else:
            found = False
            for s in subs:
                p = get_preset(s["name"])
                if p: ax.set_xlim(p["xlim"]); ax.set_ylim(p["ylim"]); found = True; break
            if not found: ax.autoscale(True, "both")
        if ymode == "log": ax.set_yscale("log")
        if not thumb: ax.legend(loc="upper left")

    def open_viewer(self, asm):
        top = tk.Toplevel(self)
        top.title(asm["label"])
        top.geometry("800x600")
        fig = plt.Figure(figsize=(5, 4), dpi=100)
        ax = fig.add_subplot(111)
        fig.subplots_adjust(left=0.1, right=0.95, top=0.95, bottom=0.1)
        cv = FigureCanvasTkAgg(fig, top)
        cv.get_tk_widget().pack(fill="both", expand=True)
        NavigationToolbar2Tk(cv, top).pack(fill="x")
        ctr = ttk.Frame(top);
        ctr.pack(fill="x", pady=5)
        ex0, ex1 = tk.StringVar(), tk.StringVar()
        ey0, ey1 = tk.StringVar(), tk.StringVar()
        ttk.Label(ctr, text="X:").pack(side="left")
        ttk.Entry(ctr, width=8, textvariable=ex0).pack(side="left")
        ttk.Entry(ctr, width=8, textvariable=ex1).pack(side="left")
        ttk.Label(ctr, text="Y:").pack(side="left")
        ttk.Entry(ctr, width=8, textvariable=ey0).pack(side="left")
        ttk.Entry(ctr, width=8, textvariable=ey1).pack(side="left")

        def update_lims():
            try:
                ax.set_xlim(float(ex0.get()), float(ex1.get())); ax.set_ylim(float(ey0.get()),
                                                                             float(ey1.get())); cv.draw_idle()
            except:
                pass

        ttk.Button(ctr, text="Set", command=update_lims).pack(side="left", padx=5)
        ym = tk.StringVar(value=asm.get("view", {}).get("ymode", "log"))

        def toggle_y():
            modes = ["linear", "log", "exp", "square"]
            ym.set(modes[(modes.index(ym.get()) + 1) % 4])
            self.plot_assembly(ax, asm, {**asm.get("view", {}), "ymode": ym.get()})
            cv.draw_idle()

        ttk.Button(ctr, text="Mode Y", command=toggle_y).pack(side="left")

        def save():
            asm["view"] = {"xlim": ax.get_xlim(), "ylim": ax.get_ylim(), "ymode": ym.get()}
            for it in asm["items"]:
                if it["kind"] == "substrate": PRESETS[it["name"]] = {"xlim": ax.get_xlim(), "ylim": ax.get_ylim()}
            try:
                Path(PRESET_PATH).write_text(json.dumps(PRESETS), "utf-8")
            except:
                pass
            top.destroy();
            self.refresh_gallery()

        ttk.Button(ctr, text="Save & Close", command=save).pack(side="right", padx=5)
        self.plot_assembly(ax, asm, asm.get("view", {}))
        xl, yl = ax.get_xlim(), ax.get_ylim()
        ex0.set(f"{xl[0]:.1f}");
        ex1.set(f"{xl[1]:.1f}")
        ey0.set(f"{yl[0]:.1f}");
        ey1.set(f"{yl[1]:.1f}")

    def copy_clipboard(self, asm):
        buf = io.BytesIO()
        fig = plt.Figure(figsize=(7, 4), dpi=150)
        ax = fig.add_subplot(111)
        fig.subplots_adjust(left=0.1, right=0.95, top=0.95, bottom=0.15)
        self.plot_assembly(ax, asm, asm.get("view", {}))
        fig.savefig(buf, format="png", dpi=150)
        plt.close(fig);
        buf.seek(0)
        try:
            if platform.system() == "Windows":
                img = Image.open(buf)
                out = io.BytesIO();
                img.save(out, "BMP");
                data = out.getvalue()[14:]
                k32 = ctypes.windll.kernel32;
                u32 = ctypes.windll.user32
                k32.GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t];
                k32.GlobalAlloc.restype = ctypes.c_void_p
                k32.GlobalLock.argtypes = [ctypes.c_void_p];
                k32.GlobalLock.restype = ctypes.c_void_p
                k32.GlobalUnlock.argtypes = [ctypes.c_void_p]
                u32.SetClipboardData.argtypes = [wintypes.UINT, ctypes.c_void_p]
                u32.OpenClipboard.argtypes = [ctypes.c_void_p]
                if u32.OpenClipboard(None):
                    u32.EmptyClipboard()
                    h = k32.GlobalAlloc(0x0002, len(data))
                    if h:
                        p = k32.GlobalLock(h)
                        ctypes.memmove(p, data, len(data))
                        k32.GlobalUnlock(h)
                        u32.SetClipboardData(8, h)
                    u32.CloseClipboard()
            elif platform.system() == "Darwin":
                import subprocess, tempfile
                with tempfile.NamedTemporaryFile(delete=False, suffix=".png") as tf:
                    tf.write(buf.getvalue()); n = tf.name
                subprocess.run(["osascript", "-e", f'set the clipboard to (read (POSIX file "{n}") as «class PNGf»)'])
                os.unlink(n)
            else:
                import shutil, subprocess
                c = ["xclip", "-sel", "clip", "-t", "image/png"] if shutil.which("xclip") else ["wl-copy", "-t",
                                                                                                "image/png"]
                subprocess.run(c, input=buf.getvalue())
        except Exception as e:
            print(e)

    def load_presets_dialog(self):
        p = filedialog.askopenfilename(filetypes=[("JSON", "*.json")])
        if p:
            try:
                PRESETS.update(json.loads(Path(p).read_text("utf-8"))); self.refresh_gallery()
            except Exception as e:
                print(e)

    def save_presets_dialog(self):
        p = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", "*.json")])
        if p:
            try:
                Path(p).write_text(json.dumps(PRESETS, indent=2), "utf-8")
            except Exception as e:
                print(e)


if __name__ == "__main__":
    app = App()
    app.mainloop()
