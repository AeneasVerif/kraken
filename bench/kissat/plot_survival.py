#!/usr/bin/env python3
"""Generate a compact 4-way Kissat survival-curve SVG (dual- or single-arch).

Supports two input modes:
  1. Pre-stripped dual-architecture timing CSV (`--csv`):
       python3 bench/kissat/plot_survival.py \\
         --csv bench/kissat/data/kissat_e190f461_survival.csv \\
         --commit e190f461 \\
         -o img/kissat_dual_arch_survival.svg

  2. One or more `results.json` files (`--x64` and/or `--arm64`), compatible
     with `bench/kissat/run_4way_stage1.py --out-json`:
       python3 bench/kissat/plot_survival.py \\
         --x64 /tmp/kissat_4way.json \\
         -o /tmp/kissat_survival.svg

Plots SMT-COMP style survival curves (% of instances solved vs. log wall-clock
time) with explicit geometric-mean (`GM`) ratios against `C1`, and compacts the
SVG (Ramer-Douglas-Peucker simplification, 1-decimal relative/axis path commands,
merged gridlines/ticks, deduplicated CSS classes, and an opaque `#ffffff`
background for dark-mode legibility).
"""
from __future__ import annotations

import argparse
import csv
import gzip
import io
import json
import math
import re
import xml.etree.ElementTree as ET
from collections import Counter
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np

# Deterministic, lightweight text SVG output across runs.
plt.rcParams["svg.fonttype"] = "none"
plt.rcParams["svg.hashsalt"] = "leanqbe-kissat-survival"
plt.rcParams["font.family"] = "DejaVu Sans"

# Okabe-Ito colorblind-safe palette with distinct line styles.
STYLES: dict[str, dict[str, Any]] = {
    "c1": dict(
        label="C1: Upstream Kissat (clang -O3)",
        color="#111827",
        linestyle="-",
        linewidth=2.3,
        zorder=5,
    ),
    "c0direct": dict(
        label="C0-direct: Verified C0 (clang -O3)",
        color="#0072B2",
        linestyle="--",
        linewidth=2.1,
        zorder=4,
    ),
    "c3b": dict(
        label="C3b: Lowered IR -> C++20 (clang++)",
        color="#009E73",
        linestyle="-.",
        linewidth=2.1,
        zorder=3,
    ),
    "c4": dict(
        label="C4: LeanQbe verified native",
        color="#D55E00",
        linestyle="-",
        linewidth=2.3,
        zorder=6,
    ),
}
SOLVER_ORDER = ("c1", "c0direct", "c3b", "c4")
X_MIN_S = 0.010
GM_FLOOR_S = 0.020


def solved_time_from_json(entry: dict[str, Any], timeout_s: float) -> float | None:
    if not entry or entry.get("status") not in (10, 20):
        return None
    if (
        not entry.get("verdict_ok", False)
        or not entry.get("model_ok", True)
        or entry.get("timed_out", False)
    ):
        return None
    ms = entry.get("wall_ms")
    if ms is None:
        return None
    t = float(ms) / 1000.0
    if not math.isfinite(t) or t <= 0.0 or t > timeout_s + 1e-6:
        return None
    return min(t, timeout_s)


def load_json_times(paths: list[Path], timeout_s: float) -> list[dict[str, float | None]]:
    """Load per-instance solve times (seconds, or None on timeout) from JSON files."""
    rows: list[dict[str, float | None]] = []
    for path in paths:
        data = json.loads(path.read_text(encoding="utf-8"))
        for item in data["results"]:
            solvers = item.get("solvers", {})
            rows.append(
                {k: solved_time_from_json(solvers.get(k, {}), timeout_s) for k in SOLVER_ORDER}
            )
    if not rows:
        raise ValueError(f"No benchmark rows found in {paths}")
    return rows


def parse_csv_time(raw: str | None, timeout_s: float) -> float | None:
    if raw is None:
        return None
    s = raw.strip()
    if not s:
        return None
    t = float(s)
    if not math.isfinite(t) or t <= 0.0 or t > timeout_s + 1e-6:
        return None
    return min(t, timeout_s)


def load_csv_times(
    csv_path: Path, timeout_s: float
) -> tuple[list[dict[str, float | None]], list[dict[str, float | None]]]:
    """Load dual-arch per-instance solve times (seconds) from a stripped CSV."""
    x64_rows: list[dict[str, float | None]] = []
    arm64_rows: list[dict[str, float | None]] = []
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            x64_rows.append(
                {k: parse_csv_time(row.get(f"x64_{k}_s"), timeout_s) for k in SOLVER_ORDER}
            )
            arm64_rows.append(
                {k: parse_csv_time(row.get(f"arm64_{k}_s"), timeout_s) for k in SOLVER_ORDER}
            )
    if not x64_rows:
        raise ValueError(f"No rows found in CSV {csv_path}")
    return x64_rows, arm64_rows


def compute_curve(
    rows: list[dict[str, float | None]], key: str, timeout_s: float
) -> tuple[np.ndarray, np.ndarray, int, int, float]:
    n = len(rows)
    times: list[float] = []
    par2_sum = 0.0
    for row in rows:
        t = row.get(key)
        if t is not None:
            times.append(t)
            par2_sum += t
        else:
            par2_sum += 2.0 * timeout_s
    times.sort()
    xs = [X_MIN_S]
    ys = [0.0]
    for idx, t in enumerate(times, start=1):
        xs.append(max(t, X_MIN_S))
        ys.append(100.0 * idx / n)
    xs.append(timeout_s)
    ys.append(100.0 * len(times) / n)
    return np.array(xs), np.array(ys), len(times), n, par2_sum / n


def gm_ratio_vs_c1(rows: list[dict[str, float | None]], key: str) -> float | None:
    if key == "c1":
        return None
    logs: list[float] = []
    for row in rows:
        t_a = row.get(key)
        t_b = row.get("c1")
        if t_a is not None and t_b is not None:
            logs.append(math.log(max(GM_FLOOR_S, t_a) / max(GM_FLOOR_S, t_b)))
    return math.exp(sum(logs) / len(logs)) if logs else None


def style_axes(ax: Any, n_total: int, timeout_s: float, right_axis: bool) -> None:
    ax.set_xscale("log")
    ax.set_xlim(X_MIN_S, timeout_s * 1.08)
    ax.set_ylim(-1.0, 103.0)
    ticks = [t for t in (0.01, 0.1, 1.0, 10.0) if t < timeout_s * 0.9] + [timeout_s]
    tick_labels = [
        f"{int(round(t * 1000))} ms" if t < 1.0 else f"{int(round(t))} s" for t in ticks
    ]
    ax.set_xticks(ticks)
    ax.set_xticklabels(tick_labels, fontsize=9.5)
    ax.xaxis.set_minor_locator(
        mticker.LogLocator(base=10.0, subs=np.arange(2, 10) * 0.1, numticks=12)
    )
    ax.xaxis.set_minor_formatter(mticker.NullFormatter())
    ax.set_yticks([0, 20, 40, 60, 80, 100])
    ax.yaxis.set_major_formatter(mticker.FormatStrFormatter("%d%%"))
    ax.tick_params(axis="both", labelsize=9.5, colors="#1F2937")
    ax.grid(True, which="major", color="#D1D5DB", linestyle="-", linewidth=0.7)
    ax.grid(True, which="minor", color="#F3F4F6", linestyle="-", linewidth=0.5)
    ax.axvline(timeout_s, color="#9CA3AF", linestyle=":", linewidth=1.2, zorder=1)
    ax.text(
        timeout_s * 0.90,
        42,
        f"timeout ({int(round(timeout_s))} s)",
        rotation=90,
        va="center",
        ha="right",
        fontsize=8.5,
        color="#6B7280",
    )
    for spine in ("top", "right"):
        ax.spines[spine].set_visible(False)
    for spine in ("left", "bottom"):
        ax.spines[spine].set_color("#9CA3AF")

    if right_axis:
        ax_r = ax.twinx()
        ax_r.set_ylim(-1.0, 103.0)
        ax_r.set_yticks([0, 20, 40, 60, 80, 100])
        ax_r.set_yticklabels(
            [f"{round(p * n_total / 100)}" for p in (0, 20, 40, 60, 80, 100)]
        )
        ax_r.set_ylabel("Instances solved (count)", fontsize=10, color="#374151")
        ax_r.tick_params(axis="y", labelsize=9, colors="#4B5563")
        ax_r.spines["top"].set_visible(False)
        ax_r.spines["left"].set_visible(False)
        ax_r.spines["right"].set_color("#9CA3AF")


def render_raw_svg(
    panel_specs: list[tuple[list[dict[str, float | None]], str]],
    commit: str | None,
    timeout_s: float,
) -> str:
    n_panels = len(panel_specs)
    figsize = (13.6, 5.2) if n_panels == 2 else (7.2, 5.0)
    fig, axes_raw = plt.subplots(
        1, n_panels, figsize=figsize, sharey=(n_panels > 1), facecolor="white"
    )
    axes = list(axes_raw) if n_panels > 1 else [axes_raw]
    for idx, (ax, (rows, title)) in enumerate(zip(axes, panel_specs)):
        ax.set_facecolor("white")
        for key in SOLVER_ORDER:
            st = STYLES[key]
            xs, ys, solved, n, par2 = compute_curve(rows, key, timeout_s)
            gm = gm_ratio_vs_c1(rows, key)
            tail = "ref" if gm is None else f"{gm:.2f}x GM"
            lbl = (
                f"{st['label']}: {100 * solved / n:.1f}% ({solved}/{n}) | "
                f"PAR-2 {par2:.2f}s | {tail}"
            )
            ax.step(
                xs,
                ys,
                where="post",
                color=st["color"],
                linestyle=st["linestyle"],
                linewidth=st["linewidth"],
                zorder=st["zorder"],
                label=lbl,
            )
            ax.scatter(
                [timeout_s],
                [ys[-1]],
                color=st["color"],
                s=18,
                zorder=st["zorder"] + 1,
            )
        style_axes(ax, len(rows), timeout_s, right_axis=(idx == n_panels - 1))
        ax.set_title(title, fontsize=11, fontweight="bold", color="#111827", pad=10)
        ax.set_xlabel("Wall solve time (log scale)", fontsize=10, color="#1F2937")
        leg = ax.legend(
            loc="lower right",
            frameon=True,
            framealpha=0.96,
            facecolor="white",
            edgecolor="#D1D5DB",
            fontsize=7.5,
            borderpad=0.5,
            handlelength=2.1,
        )
        leg.set_zorder(20)
    axes[0].set_ylabel("% of instances solved", fontsize=10, color="#1F2937")
    n_lbl = f"N = {len(panel_specs[0][0]):,} CNFs"
    suptitle = (
        f"Kissat 4-Way Survival Curves — {n_lbl} (commit {commit})"
        if commit
        else f"Kissat 4-Way Survival Curves — {n_lbl}"
    )
    fig.suptitle(suptitle, fontsize=12.6, fontweight="bold", color="#111827", y=0.985)
    fig.tight_layout(rect=[0.0, 0.0, 1.0, 0.935])
    buf = io.StringIO()
    fig.savefig(buf, format="svg", facecolor="white", metadata={"Date": None})
    plt.close(fig)
    return buf.getvalue()


# --- SVG compaction utilities ---

_ML_RE = re.compile(
    r"^\s*M\s*([-\d.eE]+)\s+([-\d.eE]+)(?:\s+L\s*[-\d.eE]+\s+[-\d.eE]+)+\s*$"
)
_NUM_PAIR_RE = re.compile(r"([ML])\s*([-\d.eE]+)\s+([-\d.eE]+)")


def fmt1(v: float) -> str:
    r = round(v, 1)
    if r == 0.0:
        return "0"
    s = f"{r:.1f}"
    return s[:-2] if s.endswith(".0") else s


def rdp(pts: list[tuple[float, float]], eps: float) -> list[tuple[float, float]]:
    if len(pts) <= 2:
        return pts
    keep = [False] * len(pts)
    keep[0] = keep[-1] = True
    stack = [(0, len(pts) - 1)]
    eps2 = eps * eps
    while stack:
        a, b = stack.pop()
        if b - a <= 1:
            continue
        x1, y1 = pts[a]
        x2, y2 = pts[b]
        dx, dy = x2 - x1, y2 - y1
        len2 = dx * dx + dy * dy
        max_d2 = -1.0
        idx = a
        for i in range(a + 1, b):
            px, py = pts[i]
            if len2 == 0.0:
                d2 = (px - x1) ** 2 + (py - y1) ** 2
            else:
                t = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / len2))
                qx, qy = x1 + t * dx, y1 + t * dy
                d2 = (px - qx) ** 2 + (py - qy) ** 2
            if d2 > max_d2:
                max_d2 = d2
                idx = i
        if max_d2 > eps2:
            keep[idx] = True
            stack.append((a, idx))
            stack.append((idx, b))
    return [p for p, k in zip(pts, keep) if k]


def encode_polyline(pts: list[tuple[float, float]]) -> str:
    if not pts:
        return ""
    rpts: list[tuple[float, float]] = []
    for x, y in pts:
        rx, ry = round(x, 1), round(y, 1)
        if not rpts or (rx != rpts[-1][0] or ry != rpts[-1][1]):
            rpts.append((rx, ry))
    out = [f"M{fmt1(rpts[0][0])} {fmt1(rpts[0][1])}"]
    cx, cy = rpts[0]
    for nx, ny in rpts[1:]:
        dx = round(nx - cx, 1)
        dy = round(ny - cy, 1)
        if dx == 0.0 and dy == 0.0:
            continue
        if dy == 0.0:
            c_abs, c_rel = f"H{fmt1(nx)}", f"h{fmt1(dx)}"
            out.append(c_rel if len(c_rel) < len(c_abs) else c_abs)
        elif dx == 0.0:
            c_abs, c_rel = f"V{fmt1(ny)}", f"v{fmt1(dy)}"
            out.append(c_rel if len(c_rel) < len(c_abs) else c_abs)
        else:
            c_abs, c_rel = f"L{fmt1(nx)} {fmt1(ny)}", f"l{fmt1(dx)} {fmt1(dy)}"
            out.append(c_rel if len(c_rel) < len(c_abs) else c_abs)
        cx, cy = nx, ny
    return "".join(out)


def compact_path_d(d: str, rdp_eps: float) -> str:
    if _ML_RE.match(d):
        pts = [(float(m.group(2)), float(m.group(3))) for m in _NUM_PAIR_RE.finditer(d)]
        if len(pts) > 20 and rdp_eps > 0.0:
            pts = rdp(pts, rdp_eps)
        return encode_polyline(pts)
    d2 = re.sub(r"-?\d+\.\d+", lambda m: fmt1(float(m.group(0))), d)
    d2 = re.sub(r"\s+", " ", d2).strip()
    return re.sub(r"\s*([MLHVCSQTAZmlhvcsqtaz])\s*", r"\1", d2)


def compact_svg_text(raw_svg: str, rdp_eps: float = 0.45) -> str:
    svg_ns = "http://www.w3.org/2000/svg"
    xlink_ns = "http://www.w3.org/1999/xlink"
    ET.register_namespace("", svg_ns)
    ET.register_namespace("xlink", xlink_ns)

    root = ET.fromstring(raw_svg)

    # 1. Drop <metadata>.
    for el in list(root):
        if el.tag == f"{{{svg_ns}}}metadata":
            root.remove(el)

    def find_referenced_ids(node: ET.Element) -> set[str]:
        refs: set[str] = set()
        for el in node.iter():
            for k, v in el.attrib.items():
                for m in re.finditer(r"url\(#([^)]+)\)", v):
                    refs.add(m.group(1))
                if k.endswith("href") and v.startswith("#"):
                    refs.add(v[1:])
        return refs

    # 2. Compact path geometry & strip no-op rotate(-0 ...) transforms.
    for el in root.iter():
        tag = el.tag.split("}")[-1]
        if tag == "path" and "d" in el.attrib:
            el.set("d", compact_path_d(el.attrib["d"], rdp_eps))
        if "transform" in el.attrib:
            tr = el.attrib["transform"].strip()
            tr = re.sub(r"rotate\(-?0(?:\.0+)?(?:\s+[-\d.]+\s+[-\d.]+)?\)", "", tr).strip()
            tr = re.sub(r"-?\d+\.\d+", lambda m: fmt1(float(m.group(0))), tr)
            if tr:
                el.set("transform", tr)
            else:
                del el.attrib["transform"]
        for attr in ("x", "y", "width", "height"):
            if attr in el.attrib and re.fullmatch(r"-?\d+\.\d+", el.attrib[attr]):
                el.set(attr, fmt1(float(el.attrib[attr])))

    # 3. Collect compacted tick definitions so <use> ticks can be expanded & merged.
    defs_paths: dict[str, str] = {}
    for defs in root.iter(f"{{{svg_ns}}}defs"):
        for child in defs:
            cid = child.get("id")
            if cid and child.tag == f"{{{svg_ns}}}path" and child.get("d"):
                defs_paths[cid] = child.get("d", "")

    def merge_paths(parent: ET.Element) -> None:
        for ch in list(parent):
            merge_paths(ch)

        new_children: list[ET.Element] = []
        for ch in list(parent):
            ctag = ch.tag.split("}")[-1]
            if (
                ctag == "g"
                and not ch.get("transform")
                and not ch.get("clip-path")
                and not ch.get("style")
                and (
                    ch.get("id", "").startswith(("xtick_", "ytick_", "line2d_", "patch_"))
                    or not ch.get("id")
                )
            ):
                sub = list(ch)
                if len(sub) == 1 and sub[0].tag.split("}")[-1] in ("path", "use"):
                    new_children.append(sub[0])
                    continue
                if (
                    all(s.tag.split("}")[-1] in ("g", "path", "use", "text") for s in sub)
                    and ch.get("id", "").startswith(("xtick_", "ytick_"))
                ):
                    for s in sub:
                        if (
                            s.tag.split("}")[-1] == "g"
                            and not s.get("transform")
                            and not s.get("clip-path")
                            and not s.get("style")
                        ):
                            new_children.extend(list(s))
                        else:
                            new_children.append(s)
                    continue
            new_children.append(ch)
        if len(new_children) != len(list(parent)) or any(
            a is not b for a, b in zip(new_children, list(parent))
        ):
            for ch in list(parent):
                parent.remove(ch)
            for ch in new_children:
                parent.append(ch)

        replaced: list[ET.Element] = []
        for ch in list(parent):
            if ch.tag == f"{{{svg_ns}}}use":
                href = ch.get(f"{{{xlink_ns}}}href") or ch.get("href") or ""
                if href.startswith("#") and href[1:] in defs_paths:
                    m_tick = re.fullmatch(r"M0 0([HV])([-\d.]+)", defs_paths[href[1:]])
                    if m_tick:
                        ux = float(ch.get("x", "0"))
                        uy = float(ch.get("y", "0"))
                        cmd, delta = m_tick.group(1), float(m_tick.group(2))
                        p_el = ET.Element(f"{{{svg_ns}}}path")
                        op = "v" if cmd == "V" else "h"
                        p_el.set("d", f"M{fmt1(ux)} {fmt1(uy)}{op}{fmt1(delta)}")
                        if ch.get("style"):
                            p_el.set("style", ch.get("style", ""))
                        replaced.append(p_el)
                        continue
            replaced.append(ch)
        if any(a is not b for a, b in zip(replaced, list(parent))):
            for ch in list(parent):
                parent.remove(ch)
            for ch in replaced:
                parent.append(ch)

        buckets: dict[tuple[str, str], ET.Element] = {}
        final_children: list[ET.Element] = []
        for ch in list(parent):
            if ch.tag == f"{{{svg_ns}}}path":
                st = ch.get("style", "")
                cp = ch.get("clip-path", "")
                d_val = ch.get("d", "")
                if (
                    (
                        "fill: none" in st
                        or "fill:none" in st
                        or ("stroke:" in st and "fill:" not in st)
                    )
                    and len(d_val) <= 32
                    and "Q" not in d_val
                    and "C" not in d_val
                ):
                    key = (st, cp)
                    if key in buckets:
                        buckets[key].set("d", buckets[key].get("d", "") + d_val)
                        continue
                    buckets[key] = ch
            final_children.append(ch)
        if len(final_children) != len(list(parent)):
            for ch in list(parent):
                parent.remove(ch)
            for ch in final_children:
                parent.append(ch)

    merge_paths(root)

    # 4. Drop unreferenced IDs, unused <defs> entries, and empty <defs>.
    refs = find_referenced_ids(root)
    for parent in root.iter():
        for defs in list(parent):
            if defs.tag == f"{{{svg_ns}}}defs":
                for child in list(defs):
                    cid = child.get("id")
                    if (cid and cid not in refs) or child.tag == f"{{{svg_ns}}}style":
                        defs.remove(child)
                if len(defs) == 0:
                    parent.remove(defs)
    refs = find_referenced_ids(root)
    for el in root.iter():
        eid = el.get("id")
        if eid and eid not in refs:
            del el.attrib["id"]

    # 5. Deduplicate repeated inline style="..." into compact CSS classes.
    style_counts: Counter[str] = Counter()
    for el in root.iter():
        st = el.get("style")
        if st:
            st_norm = re.sub(r"\s*:\s*", ":", st.strip())
            st_norm = re.sub(r"\s*;\s*", ";", st_norm).rstrip(";")
            st_norm = re.sub(
                r"font:([^;]+)'DejaVu Sans'[^;]*",
                r"font:\1DejaVu Sans,sans-serif",
                st_norm,
            )
            el.set("style", st_norm)
            style_counts[st_norm] += 1

    css_rules: list[str] = []
    style_to_cls: dict[str, str] = {}
    for st_norm, cnt in style_counts.most_common():
        if cnt >= 2 and len(st_norm) > 10:
            cname = f"s{len(style_to_cls)}"
            style_to_cls[st_norm] = cname
            css_rules.append(f".{cname}{{{st_norm}}}")

    for el in root.iter():
        st = el.get("style")
        if st in style_to_cls:
            el.set("class", style_to_cls[st])
            del el.attrib["style"]

    base_css = "*{stroke-linejoin:round;stroke-linecap:butt}"
    full_css = base_css + "".join(css_rules)
    style_el = root.find(f"{{{svg_ns}}}style")
    if style_el is not None:
        style_el.text = full_css
    else:
        style_el = ET.Element(f"{{{svg_ns}}}style")
        style_el.set("type", "text/css")
        style_el.text = full_css
        root.insert(0, style_el)

    # 6. Insert opaque white background right after <style>, behind all plot groups.
    bg_rect = ET.Element(f"{{{svg_ns}}}rect")
    bg_rect.set("width", "100%")
    bg_rect.set("height", "100%")
    bg_rect.set("fill", "#ffffff")
    root.insert(1, bg_rect)

    # 7. Strip insignificant whitespace, ensure clean line breaks, and validate XML.
    for el in root.iter():
        if el.tag not in (f"{{{svg_ns}}}text", f"{{{svg_ns}}}style"):
            if el.text and not el.text.strip():
                el.text = None
        if el.tail and not el.tail.strip():
            el.tail = None

    xml_str = ET.tostring(root, encoding="unicode", xml_declaration=False)
    xml_str = xml_str.replace("><", ">\n<")
    xml_str = "\n".join(line.rstrip() for line in xml_str.splitlines()) + "\n"
    ET.fromstring(xml_str)
    return xml_str


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Generate a compact 4-way Kissat survival SVG (dual- or single-arch)."
    )
    ap.add_argument(
        "--csv",
        type=Path,
        default=None,
        help="Stripped dual-arch timing CSV (columns: id,verdict,x64_*_s,arm64_*_s).",
    )
    ap.add_argument(
        "--x64",
        nargs="+",
        type=Path,
        default=None,
        help="One or more x86-64 JSON files (run_4way_stage1.py --out-json or results.json).",
    )
    ap.add_argument(
        "--arm64",
        nargs="+",
        type=Path,
        default=None,
        help="One or more AArch64 JSON files (run_4way_stage1.py --out-json or results.json).",
    )
    ap.add_argument(
        "--commit",
        default=None,
        help="Short commit SHA to display in the plot title (e.g. e190f461).",
    )
    ap.add_argument(
        "--x64-cpu",
        default="AMD EPYC Zen 5",
        help="x86-64 CPU label for the panel title.",
    )
    ap.add_argument(
        "--arm64-cpu",
        default="Arm Neoverse-V2",
        help="AArch64 CPU label for the panel title.",
    )
    ap.add_argument(
        "--timeout",
        type=float,
        default=30.0,
        help="Per-instance wall-clock timeout in seconds (default: 30.0).",
    )
    ap.add_argument(
        "--rdp-tol",
        type=float,
        default=0.45,
        help="Ramer-Douglas-Peucker simplification tolerance in points (default: 0.45).",
    )
    ap.add_argument(
        "-o",
        "--out",
        type=Path,
        required=True,
        help="Output SVG file path.",
    )
    args = ap.parse_args()
    if args.csv is not None and (args.x64 or args.arm64):
        ap.error("--csv cannot be combined with --x64 or --arm64")
    if args.csv is None and not args.x64 and not args.arm64:
        ap.error("specify --csv or at least one of --x64 / --arm64")
    return args


def main() -> None:
    args = parse_args()
    panels: list[tuple[list[dict[str, float | None]], str]] = []
    if args.csv is not None:
        x64_rows, arm64_rows = load_csv_times(args.csv, args.timeout)
        panels.append(
            (x64_rows, f"x86-64 — {args.x64_cpu}\nCombined Corpus (N = {len(x64_rows):,})")
        )
        panels.append(
            (arm64_rows, f"AArch64 — {args.arm64_cpu}\nCombined Corpus (N = {len(arm64_rows):,})")
        )
    else:
        if args.x64:
            x64_rows = load_json_times(args.x64, args.timeout)
            panels.append(
                (x64_rows, f"x86-64 — {args.x64_cpu}\nCombined Corpus (N = {len(x64_rows):,})")
            )
        if args.arm64:
            arm64_rows = load_json_times(args.arm64, args.timeout)
            panels.append(
                (
                    arm64_rows,
                    f"AArch64 — {args.arm64_cpu}\nCombined Corpus (N = {len(arm64_rows):,})",
                )
            )
    raw_svg = render_raw_svg(panels, commit=args.commit, timeout_s=args.timeout)
    compact = compact_svg_text(raw_svg, rdp_eps=args.rdp_tol)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(compact, encoding="utf-8")
    raw_b = len(raw_svg.encode("utf-8"))
    out_b = len(compact.encode("utf-8"))
    gz_b = len(gzip.compress(compact.encode("utf-8"), compresslevel=9))
    print(
        f"Wrote {args.out}: {raw_b:,} B -> {out_b:,} B "
        f"({gz_b:,} B gzipped, {compact.count(chr(10))} lines)"
    )


if __name__ == "__main__":
    main()
