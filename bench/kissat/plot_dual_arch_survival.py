#!/usr/bin/env python3
"""Reproducible dual-architecture Kissat survival curve exporter and SVG plotter.

Separates large per-instance timing datasets (`artifacts` branch) from lightweight
checked-in plotting code and compact `< 40 KB` SVGs (`leanqbe/main`):

  1. Export compact `.csv.xz` (integer milliseconds + `#` metadata header) and
     `manifest.json` from DevRez `results.json`, `results.csv`, or combined CSVs:
       python3 bench/kissat/plot_dual_arch_survival.py export \\
         --x64 path/to/x86_64/stage1/results.json \\
         --arm64 path/to/aarch64/stage1/results.json \\
         --run-tag gate_g4_stage1 --commit <sha> \\
         --out-dir /tmp/results/gate_g4_stage1

  2. Plot a decimated `< 40 KB` dual-arch SVG directly from `artifacts` via `git show`
     (without checking out the `artifacts` branch), from `--results-dir`, or from
     explicit `--csv` / `--x64` / `--arm64` inputs:
       python3 bench/kissat/plot_dual_arch_survival.py plot \\
         --git-ref artifacts --git-path bench/results/gate_g4_stage1 \\
         -o /tmp/kissat_dual_arch_survival.svg

       python3 bench/kissat/plot_dual_arch_survival.py \\
         --results-dir /tmp/results/gate_g4_stage1 \\
         -o /tmp/kissat_dual_arch_survival.svg
"""
from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import io
import json
import lzma
import math
import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from collections import Counter
from pathlib import Path
from typing import Any, Iterable, Sequence

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np

# Deterministic, lightweight text SVG output across runs.
plt.rcParams["svg.fonttype"] = "none"
plt.rcParams["svg.hashsalt"] = "leanqbe-kissat-survival"
plt.rcParams["font.family"] = "DejaVu Sans"

DEFAULT_X64_CPU = "AMD EPYC Zen 5"
DEFAULT_ARM64_CPU = "Arm Neoverse-V2"
DEFAULT_GIT_REF = "artifacts"
DEFAULT_TIMEOUT_S = 30.0
DEFAULT_GM_FLOOR_MS = 20.0
DEFAULT_TARGET_VERTICES = 320
DEFAULT_MAX_VERTICES = 400
MAX_SVG_BYTES = 40 * 1024 - 1  # strictly < 40 KB (40,960 B)
MAX_DATASET_BYTES = 1000 * 1000 - 1  # strictly < 1 MB
X_MIN_S = 0.010

# Okabe-Ito colorblind-safe palette with distinct line styles.
CANONICAL_STYLES: dict[str, dict[str, Any]] = {
    "c1": dict(
        label="C1 (Upstream, clang -O3)",
        color="#111827",
        linestyle="-",
        linewidth=2.3,
        zorder=5,
    ),
    "c0direct": dict(
        label="C0-direct (clang -O3)",
        color="#0072B2",
        linestyle="--",
        linewidth=2.1,
        zorder=4,
    ),
    "c3b": dict(
        label="C3b (IR -> clang++ -O3)",
        color="#009E73",
        linestyle="-.",
        linewidth=2.1,
        zorder=3,
    ),
    "c4": dict(
        label="C4 (LeanQbe verified)",
        color="#D55E00",
        linestyle="-",
        linewidth=2.3,
        zorder=6,
    ),
    "c4_g4_full": dict(
        label="C4 G4 (LeanQbe verified)",
        color="#D55E00",
        linestyle="-",
        linewidth=2.3,
        zorder=6,
    ),
    "c4_g3": dict(
        label="C4 G3 (LeanQbe verified)",
        color="#CC79A7",
        linestyle=":",
        linewidth=2.0,
        zorder=4,
    ),
    "c4_g4_w62_pasm": dict(
        label="C4 G4+PASM (LeanQbe)",
        color="#E69F00",
        linestyle=(0, (3, 1.5)),
        linewidth=2.0,
        zorder=5,
    ),
}
CANONICAL_SOLVER_ORDER = ("c1", "c0direct", "c3b", "c4", "c4_g4_full", "c4_g3")
FALLBACK_PALETTE = ("#CC79A7", "#E69F00", "#56B4E9", "#6B7280", "#7C3AED", "#B91C1C")
FALLBACK_LINESTYLES = (":", "--", "-.", (0, (3, 1.5)), "-")

# Enforce strict terminology rules case-insensitively without repeating banned terms verbatim.
_FORBIDDEN_TERM_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("forbidden-arm-brand", re.compile(r"a" r"xion", re.IGNORECASE)),
    ("forbidden-host-term", re.compile(r"bare[- ]?metal", re.IGNORECASE)),
)
_UNLABELED_RATIO_RE = re.compile(r"(?<![WI-])\b(?:GM|AM)\b")


def validate_style_text(text: str, context: str = "output") -> None:
    """Reject forbidden CPU/hosting terms in text outputs or labels."""
    for rule_name, pat in _FORBIDDEN_TERM_PATTERNS:
        m = pat.search(text)
        if m:
            raise ValueError(
                f"Style policy violation ({rule_name}) in {context}: found disallowed term {m.group(0)!r}"
            )


def validate_svg_document(svg_text: str, max_vertices: int = DEFAULT_MAX_VERTICES) -> dict[str, Any]:
    """Validate XML well-formedness, size, ratio labels, forbidden terms, and curve vertices."""
    validate_style_text(svg_text, context="SVG output")

    root = ET.fromstring(svg_text)
    svg_ns = "http://www.w3.org/2000/svg"
    for text_el in root.iter(f"{{{svg_ns}}}text"):
        txt = "".join(text_el.itertext())
        if _UNLABELED_RATIO_RE.search(txt):
            raise ValueError(f"Unlabeled GM/AM ratio in SVG text element: {txt!r}")

    curve_vertices: list[int] = []
    for path_el in root.iter(f"{{{svg_ns}}}path"):
        if path_el.get("data-survival-curve") == "1":
            d = path_el.get("d", "")
            v_cnt = len(re.findall(r"[MLHVmlhv]", d))
            curve_vertices.append(v_cnt)
            if v_cnt > max_vertices:
                raise ValueError(
                    f"Survival curve exceeded vertex cap: {v_cnt} > {max_vertices}"
                )

    svg_bytes = len(svg_text.encode("utf-8"))
    if svg_bytes > MAX_SVG_BYTES:
        raise ValueError(f"SVG exceeds 40 KB budget: {svg_bytes} bytes > {MAX_SVG_BYTES}")

    return {
        "bytes": svg_bytes,
        "curve_vertices": curve_vertices,
        "max_curve_vertices": max(curve_vertices, default=0),
        "min_curve_vertices": min(curve_vertices, default=0),
    }


def sanitize_cpu_label(raw: str | None, arch: str, allow_hw_alias: bool = False) -> str:
    """Validate and normalize CPU labels for AMD EPYC Zen 5 and Arm Neoverse-V2."""
    default = DEFAULT_X64_CPU if arch == "x64" else DEFAULT_ARM64_CPU
    if not raw or not raw.strip():
        return default
    cleaned = raw.strip()
    if allow_hw_alias:
        low = cleaned.lower()
        if arch == "arm64":
            if any(tok in low for tok in ("neoverse", "maple", "athena", "a" "xion")):
                return DEFAULT_ARM64_CPU
        elif any(tok in low for tok in ("epyc", "zen 5", "zen5", "turin", "9b45", "astoria")):
            return DEFAULT_X64_CPU
    validate_style_text(cleaned, context=f"{arch} CPU label")
    return cleaned


def parse_solver_map(specs: Sequence[str] | None) -> tuple[dict[str, str], dict[str, dict[str, str]]]:
    """Parse `raw=canonical` or `arch:raw=canonical` (or JSON dict) solver mappings."""
    global_map: dict[str, str] = {}
    arch_map: dict[str, dict[str, str]] = {"x64": {}, "arm64": {}}
    if not specs:
        return global_map, arch_map
    for spec in specs:
        s = spec.strip()
        if not s:
            continue
        if s.startswith("{"):
            obj = json.loads(s)
            if not isinstance(obj, dict):
                raise ValueError(f"Expected JSON object for --solver-map, got {type(obj).__name__}")
            for k, v in obj.items():
                global_map[str(k)] = str(v)
            continue
        if "=" not in s:
            raise ValueError(f"Invalid --solver-map entry {spec!r}; expected raw=canonical")
        lhs, rhs = s.split("=", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        if not lhs or not rhs:
            raise ValueError(f"Invalid --solver-map entry {spec!r}; empty key or value")
        if ":" in lhs:
            arch_raw, skey = lhs.split(":", 1)
            arch_norm = _norm_arch(arch_raw)
            arch_map[arch_norm][skey.strip()] = rhs
        else:
            global_map[lhs] = rhs
    return global_map, arch_map


def parse_solver_labels(specs: Sequence[str] | None) -> dict[str, str]:
    labels: dict[str, str] = {}
    if not specs:
        return labels
    for spec in specs:
        if "=" not in spec:
            raise ValueError(f"Invalid --solver-label entry {spec!r}; expected key=label")
        k, v = spec.split("=", 1)
        k, v = k.strip(), v.strip()
        validate_style_text(v, context=f"solver label for {k}")
        labels[k] = v
    return labels


def _norm_arch(raw: str) -> str:
    low = raw.strip().lower()
    if low in ("x64", "x86_64", "x86-64", "amd64"):
        return "x64"
    if low in ("arm64", "aarch64", "arm"):
        return "arm64"
    raise ValueError(f"Unknown architecture {raw!r}; expected x64/x86_64 or arm64/aarch64")


def order_solvers(solvers: Iterable[str]) -> list[str]:
    seen: list[str] = []
    for s in solvers:
        if s not in seen:
            seen.append(s)
    canonical = [s for s in CANONICAL_SOLVER_ORDER if s in seen]
    rest = [s for s in seen if s not in canonical]
    return canonical + rest


def style_for_solver(key: str, idx: int, label_overrides: dict[str, str] | None = None) -> dict[str, Any]:
    if key in CANONICAL_STYLES:
        st = dict(CANONICAL_STYLES[key])
    else:
        st = {
            "label": key,
            "color": FALLBACK_PALETTE[idx % len(FALLBACK_PALETTE)],
            "linestyle": FALLBACK_LINESTYLES[idx % len(FALLBACK_LINESTYLES)],
            "linewidth": 2.0,
            "zorder": 3 + (idx % 4),
        }
    if label_overrides and key in label_overrides:
        st["label"] = label_overrides[key]
    validate_style_text(str(st["label"]), context=f"solver style label ({key})")
    return st


def _open_text_maybe_xz(path: Path) -> str:
    if path.suffix == ".xz":
        return lzma.decompress(path.read_bytes()).decode("utf-8")
    return path.read_text(encoding="utf-8")


def _parse_bool(raw: Any, default: bool = False) -> bool:
    if isinstance(raw, bool):
        return raw
    if raw is None:
        return default
    s = str(raw).strip().lower()
    if s in ("true", "1", "yes"):
        return True
    if s in ("false", "0", "no", ""):
        return False
    return default


def _solved_ms_from_json_entry(
    entry: dict[str, Any], timeout_s: float, metric: str = "wall_ms"
) -> int | None:
    if not entry or entry.get("status") not in (10, 20):
        return None
    if (
        not entry.get("verdict_ok", False)
        or not entry.get("model_ok", True)
        or entry.get("timed_out", False)
    ):
        return None
    val_ms = entry.get(metric)
    if val_ms is None and metric != "wall_ms":
        val_ms = entry.get("wall_ms")
    if val_ms is None:
        return None
    ms_f = float(val_ms)
    timeout_ms = timeout_s * 1000.0
    if not math.isfinite(ms_f) or ms_f <= 0.0 or ms_f > timeout_ms + 1e-3:
        return None
    return max(1, min(int(round(timeout_ms)), int(round(ms_f))))


def _parse_time_ms(raw: str | None, unit: str, timeout_s: float) -> int | None:
    if raw is None:
        return None
    s = raw.strip()
    if not s:
        return None
    val = float(s)
    ms_f = val if unit == "ms" else val * 1000.0
    timeout_ms = timeout_s * 1000.0
    if not math.isfinite(ms_f) or ms_f <= 0.0 or ms_f > timeout_ms + 1e-3:
        return None
    return max(1, min(int(round(timeout_ms)), int(round(ms_f))))


def _infer_verdict_from_json_item(item: dict[str, Any], solvers: dict[str, Any]) -> str:
    exp = str(item.get("expected") or item.get("verdict") or "").strip().lower()
    if exp in ("sat", "unsat"):
        return exp
    statuses = {
        e.get("status")
        for e in solvers.values()
        if isinstance(e, dict) and e.get("verdict_ok", True) and e.get("status") in (10, 20)
    }
    if statuses == {10}:
        return "sat"
    if statuses == {20}:
        return "unsat"
    return "unknown"


def _extract_meta_from_json(data: dict[str, Any], arch: str) -> dict[str, Any]:
    meta = data.get("meta", {}) if isinstance(data.get("meta"), dict) else {}
    devrez = meta.get("devrez", {}) if isinstance(meta.get("devrez"), dict) else {}
    ent = devrez.get("entity", {}) if isinstance(devrez.get("entity"), dict) else {}
    lscpu = devrez.get("lscpu_guard", {}) if isinstance(devrez.get("lscpu_guard"), dict) else {}
    raw_cpu = (
        ent.get("CPU Type")
        or lscpu.get("model")
        or meta.get("cpu_model")
        or meta.get("cpu")
        or ""
    )
    timeout_s = meta.get("timeout_s") or devrez.get("timeout_s")
    suite = meta.get("suite") or devrez.get("suite") or meta.get("stage_arg") or ""
    commit = meta.get("git_rev") or meta.get("commit") or ""
    hostname = meta.get("hostname") or devrez.get("compute_fqdn") or ""
    return {
        "cpu_label": sanitize_cpu_label(str(raw_cpu), arch, allow_hw_alias=True),
        "timeout_s": float(timeout_s) if timeout_s is not None else None,
        "suite": str(suite).strip() if suite else "",
        "commit": str(commit).strip()[:8] if commit else "",
        "hostname": str(hostname).strip(),
        "solvers": list(meta.get("solvers") or []),
    }


def _remap_solver_key(
    raw: str, arch: str, global_map: dict[str, str], arch_map: dict[str, dict[str, str]]
) -> str:
    if arch in arch_map and raw in arch_map[arch]:
        return arch_map[arch][raw]
    return global_map.get(raw, raw)


def _load_single_arch_json_text(
    text: str,
    arch: str,
    timeout_override: float | None,
    metric: str,
    global_map: dict[str, str],
    arch_map: dict[str, dict[str, str]],
) -> tuple[list[dict[str, Any]], list[str], dict[str, Any]]:
    data = json.loads(text)
    meta_info = _extract_meta_from_json(data, arch)
    eff_timeout = float(
        timeout_override
        if timeout_override is not None
        else (meta_info["timeout_s"] or DEFAULT_TIMEOUT_S)
    )
    raw_solvers: list[str] = list(meta_info["solvers"])
    results = data.get("results", [])
    if not raw_solvers and results:
        raw_solvers = list(results[0].get("solvers", {}).keys())

    mapped_solvers = order_solvers(
        _remap_solver_key(s, arch, global_map, arch_map) for s in raw_solvers
    )
    rows: list[dict[str, Any]] = []
    for item in results:
        sol_dict = item.get("solvers", {})
        item_to = float(
            timeout_override
            if timeout_override is not None
            else (item.get("timeout_s") or eff_timeout)
        )
        times_ms: dict[str, int | None] = {s: None for s in mapped_solvers}
        for raw_s, entry in sol_dict.items():
            mskey = _remap_solver_key(raw_s, arch, global_map, arch_map)
            if mskey not in times_ms:
                times_ms[mskey] = None
                if mskey not in mapped_solvers:
                    mapped_solvers.append(mskey)
            val = _solved_ms_from_json_entry(entry, item_to, metric=metric)
            if times_ms[mskey] is None or val is not None:
                times_ms[mskey] = val
        rows.append(
            {
                "id": str(item["id"]),
                "suite": str(item.get("stage_origin") or item.get("corpus") or item.get("suite") or meta_info["suite"] or ""),
                "verdict": _infer_verdict_from_json_item(item, sol_dict),
                "times_ms": times_ms,
                "timeout_s": item_to,
            }
        )
    meta_info["timeout_s"] = eff_timeout
    return rows, order_solvers(mapped_solvers), meta_info


def _split_csv_comments_and_body(text: str) -> tuple[dict[str, str], str]:
    headers: dict[str, str] = {}
    body_lines: list[str] = []
    in_header = True
    for line in text.splitlines():
        if in_header and line.startswith("#"):
            content = line[1:].strip()
            if ":" in content:
                k, v = content.split(":", 1)
                headers[k.strip().lower()] = v.strip()
        elif in_header and not line.strip():
            continue
        else:
            in_header = False
            body_lines.append(line)
    return headers, "\n".join(body_lines)


def _load_single_arch_csv_text(
    text: str,
    arch: str,
    timeout_override: float | None,
    metric: str,
    global_map: dict[str, str],
    arch_map: dict[str, dict[str, str]],
) -> tuple[list[dict[str, Any]], list[str], dict[str, Any]]:
    headers, body = _split_csv_comments_and_body(text)
    if not body.strip():
        raise ValueError("Empty CSV body")
    reader = csv.DictReader(io.StringIO(body))
    if not reader.fieldnames:
        raise ValueError("CSV missing header row")
    fields = list(reader.fieldnames)

    eff_timeout = float(
        timeout_override
        if timeout_override is not None
        else (float(headers["timeout_s"]) if "timeout_s" in headers else DEFAULT_TIMEOUT_S)
    )

    # Detect DevRez per-arch `results.csv` (`<solver>_wall_ms` / `<solver>_status`)
    # vs combined dual-arch CSV (`x64_<solver>_ms` / `arm64_<solver>_s`).
    metric_suffix = f"_{metric}"
    devrez_solvers = [
        f[: -len(metric_suffix)]
        for f in fields
        if f.endswith(metric_suffix) and not f.startswith(("x64_", "arm64_"))
    ]
    if not devrez_solvers and metric != "wall_ms":
        devrez_solvers = [
            f[: -len("_wall_ms")]
            for f in fields
            if f.endswith("_wall_ms") and not f.startswith(("x64_", "arm64_"))
        ]
        use_col_suffix = "_wall_ms"
    else:
        use_col_suffix = metric_suffix

    rows: list[dict[str, Any]] = []
    if devrez_solvers:
        mapped_solvers = order_solvers(
            _remap_solver_key(s, arch, global_map, arch_map) for s in devrez_solvers
        )
        for row in reader:
            times_ms: dict[str, int | None] = {s: None for s in mapped_solvers}
            for raw_s in devrez_solvers:
                mskey = _remap_solver_key(raw_s, arch, global_map, arch_map)
                status_raw = row.get(f"{raw_s}_status", "").strip()
                status_ok = int(status_raw) in (10, 20) if status_raw else True
                timed_out = _parse_bool(row.get(f"{raw_s}_timed_out"), default=False)
                verdict_ok = _parse_bool(row.get(f"{raw_s}_verdict_ok"), default=True)
                model_ok = _parse_bool(row.get(f"{raw_s}_model_ok"), default=True)
                val_raw = row.get(f"{raw_s}{use_col_suffix}", "")
                val: int | None = None
                if status_ok and not timed_out and verdict_ok and model_ok:
                    val = _parse_time_ms(val_raw, unit="ms", timeout_s=eff_timeout)
                times_ms[mskey] = val
            verdict = str(row.get("expected") or row.get("verdict") or "unknown").strip().lower()
            if verdict not in ("sat", "unsat"):
                verdict = "unknown"
            rows.append(
                {
                    "id": str(row.get("id") or f"row_{len(rows)}"),
                    "suite": str(row.get("stage_origin") or row.get("suite") or ""),
                    "verdict": verdict,
                    "times_ms": times_ms,
                    "timeout_s": eff_timeout,
                }
            )
        meta_info = {
            "cpu_label": sanitize_cpu_label(headers.get(f"{arch}_cpu"), arch),
            "timeout_s": eff_timeout,
            "suite": headers.get("suite", ""),
            "commit": headers.get("commit", ""),
            "hostname": "",
            "solvers": mapped_solvers,
        }
        return rows, mapped_solvers, meta_info

    # Combined dual-arch CSV slice for `arch`.
    x64_rows, arm64_rows, x64_sols, arm64_sols, dual_meta = parse_dual_csv_text(
        text, timeout_override=timeout_override, global_map=global_map, arch_map=arch_map
    )
    if arch == "x64":
        return x64_rows, x64_sols, {
            "cpu_label": dual_meta["x64_cpu"],
            "timeout_s": dual_meta["timeout_s"],
            "suite": dual_meta["suite"],
            "commit": dual_meta["commit"],
            "hostname": "",
            "solvers": x64_sols,
        }
    return arm64_rows, arm64_sols, {
        "cpu_label": dual_meta["arm64_cpu"],
        "timeout_s": dual_meta["timeout_s"],
        "suite": dual_meta["suite"],
        "commit": dual_meta["commit"],
        "hostname": "",
        "solvers": arm64_sols,
    }


def parse_dual_csv_text(
    text: str,
    timeout_override: float | None = None,
    global_map: dict[str, str] | None = None,
    arch_map: dict[str, dict[str, str]] | None = None,
) -> tuple[
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[str],
    list[str],
    dict[str, Any],
]:
    """Parse a combined dual-arch CSV (`.csv` or `.csv.xz` decompressed text)."""
    global_map = global_map or {}
    arch_map = arch_map or {"x64": {}, "arm64": {}}
    headers, body = _split_csv_comments_and_body(text)
    if not body.strip():
        raise ValueError("Empty CSV body")
    reader = csv.DictReader(io.StringIO(body))
    if not reader.fieldnames:
        raise ValueError("CSV missing header row")
    fields = list(reader.fieldnames)

    eff_timeout = float(
        timeout_override
        if timeout_override is not None
        else (float(headers["timeout_s"]) if "timeout_s" in headers else DEFAULT_TIMEOUT_S)
    )

    arch_cols: dict[str, list[tuple[str, str, str]]] = {"x64": [], "arm64": []}
    pat = re.compile(r"^(x64|arm64)_(.+)_(ms|s)$")
    for f in fields:
        m = pat.match(f)
        if m:
            arch_cols[m.group(1)].append((f, m.group(2), m.group(3)))

    if not arch_cols["x64"] and not arch_cols["arm64"]:
        raise ValueError(f"CSV does not contain x64_*_{{ms,s}} or arm64_*_{{ms,s}} columns: {fields}")

    x64_sols = order_solvers(
        _remap_solver_key(raw_s, "x64", global_map, arch_map) for _, raw_s, _ in arch_cols["x64"]
    )
    arm64_sols = order_solvers(
        _remap_solver_key(raw_s, "arm64", global_map, arch_map) for _, raw_s, _ in arch_cols["arm64"]
    )

    x64_rows: list[dict[str, Any]] = []
    arm64_rows: list[dict[str, Any]] = []
    for idx, row in enumerate(reader):
        rid = str(row.get("id") or f"row_{idx}")
        suite = str(row.get("suite") or row.get("stage_origin") or "")
        verdict = str(row.get("verdict") or row.get("expected") or "unknown").strip().lower()
        if verdict not in ("sat", "unsat"):
            verdict = "unknown"

        if arch_cols["x64"]:
            tmap_x64: dict[str, int | None] = {s: None for s in x64_sols}
            for col, raw_s, unit in arch_cols["x64"]:
                mskey = _remap_solver_key(raw_s, "x64", global_map, arch_map)
                tmap_x64[mskey] = _parse_time_ms(row.get(col), unit=unit, timeout_s=eff_timeout)
            x64_rows.append(
                {"id": rid, "suite": suite, "verdict": verdict, "times_ms": tmap_x64, "timeout_s": eff_timeout}
            )
        if arch_cols["arm64"]:
            tmap_arm64: dict[str, int | None] = {s: None for s in arm64_sols}
            for col, raw_s, unit in arch_cols["arm64"]:
                mskey = _remap_solver_key(raw_s, "arm64", global_map, arch_map)
                tmap_arm64[mskey] = _parse_time_ms(row.get(col), unit=unit, timeout_s=eff_timeout)
            arm64_rows.append(
                {"id": rid, "suite": suite, "verdict": verdict, "times_ms": tmap_arm64, "timeout_s": eff_timeout}
            )

    if not x64_rows and not arm64_rows:
        raise ValueError("No benchmark rows found in dual-arch CSV")

    meta_info = {
        "run_tag": headers.get("run_tag", ""),
        "commit": headers.get("commit", ""),
        "suite": headers.get("suite", ""),
        "timeout_s": eff_timeout,
        "x64_cpu": sanitize_cpu_label(headers.get("x64_cpu"), "x64"),
        "arm64_cpu": sanitize_cpu_label(headers.get("arm64_cpu"), "arm64"),
        "metric": headers.get("metric", "wall_ms"),
    }
    return x64_rows, arm64_rows, x64_sols, arm64_sols, meta_info


def load_arch_inputs(
    paths: Sequence[Path],
    arch: str,
    timeout_override: float | None = None,
    metric: str = "wall_ms",
    global_map: dict[str, str] | None = None,
    arch_map: dict[str, dict[str, str]] | None = None,
    dedup: str = "id",
) -> tuple[list[dict[str, Any]], list[str], dict[str, Any]]:
    """Load and merge one or more `.json` / `.csv` / `.csv.xz` files for a single arch."""
    global_map = global_map or {}
    arch_map = arch_map or {"x64": {}, "arm64": {}}
    merged_rows: list[dict[str, Any]] = []
    seen_keys: set[str] = set()
    solvers_union: list[str] = []
    cpu_label = DEFAULT_X64_CPU if arch == "x64" else DEFAULT_ARM64_CPU
    suites_seen: list[str] = []
    commits_seen: list[str] = []
    hostnames_seen: list[str] = []
    timeouts_seen: list[float] = []

    for p in paths:
        if not p.is_file():
            raise FileNotFoundError(f"Missing input file: {p}")
        text = _open_text_maybe_xz(p)
        if p.suffix == ".json":
            rows, sols, minfo = _load_single_arch_json_text(
                text, arch, timeout_override, metric, global_map, arch_map
            )
        else:
            rows, sols, minfo = _load_single_arch_csv_text(
                text, arch, timeout_override, metric, global_map, arch_map
            )

        cpu_label = minfo.get("cpu_label") or cpu_label
        if minfo.get("suite") and minfo["suite"] not in suites_seen:
            suites_seen.append(minfo["suite"])
        if minfo.get("commit") and minfo["commit"] not in commits_seen:
            commits_seen.append(minfo["commit"])
        if minfo.get("hostname") and minfo["hostname"] not in hostnames_seen:
            hostnames_seen.append(minfo["hostname"])
        if minfo.get("timeout_s") is not None:
            timeouts_seen.append(float(minfo["timeout_s"]))

        for s in sols:
            if s not in solvers_union:
                solvers_union.append(s)

        for row in rows:
            if dedup == "none":
                key = f"__row_{len(merged_rows)}"
            elif dedup == "suite-id":
                key = f"{row.get('suite', '')}::{row['id']}"
            else:
                key = row["id"]
            if key in seen_keys:
                continue
            seen_keys.add(key)
            merged_rows.append(row)

    if not merged_rows:
        raise ValueError(f"No rows loaded from {paths}")

    eff_timeout = float(
        timeout_override
        if timeout_override is not None
        else (min(timeouts_seen) if timeouts_seen else DEFAULT_TIMEOUT_S)
    )
    if timeout_override is None and len({round(t, 6) for t in timeouts_seen}) > 1:
        # Clamp times to the minimum timeout across merged files for soundness.
        eff_ms = int(round(eff_timeout * 1000.0))
        for row in merged_rows:
            for k, v in row["times_ms"].items():
                if v is not None and v > eff_ms:
                    row["times_ms"][k] = None
            row["timeout_s"] = eff_timeout

    solvers_ordered = order_solvers(solvers_union)
    for row in merged_rows:
        for s in solvers_ordered:
            row["times_ms"].setdefault(s, None)

    return merged_rows, solvers_ordered, {
        "cpu_label": sanitize_cpu_label(cpu_label, arch),
        "timeout_s": eff_timeout,
        "suite": " + ".join(suites_seen) if suites_seen else "",
        "commit": commits_seen[0] if commits_seen else "",
        "hostname": ", ".join(hostnames_seen),
    }


def compute_solver_summary(
    rows: Sequence[dict[str, Any]],
    solvers: Sequence[str],
    timeout_s: float,
    ref_solver: str | None = None,
    gm_floor_ms: float = DEFAULT_GM_FLOOR_MS,
) -> dict[str, dict[str, Any]]:
    """Compute solved counts, PAR-2, W-GM, and W-AM vs ref_solver."""
    n = len(rows)
    if n == 0:
        raise ValueError("Cannot compute survival statistics on empty dataset")

    ref = ref_solver
    if ref not in solvers:
        ref = "c1" if "c1" in solvers else ("c0direct" if "c0direct" in solvers else solvers[0])

    floor_s = gm_floor_ms / 1000.0
    out: dict[str, dict[str, Any]] = {}
    for s in solvers:
        times_s: list[float] = []
        sat_cnt = 0
        unsat_cnt = 0
        par2_sum = 0.0
        wgm_logs: list[float] = []
        sum_a = 0.0
        sum_b = 0.0
        n_mut = 0
        for row in rows:
            t_ms = row["times_ms"].get(s)
            if t_ms is not None and t_ms <= timeout_s * 1000.0 + 1e-3:
                t_s = min(timeout_s, t_ms / 1000.0)
                times_s.append(t_s)
                par2_sum += t_s
                v = row.get("verdict", "unknown")
                if v == "sat":
                    sat_cnt += 1
                elif v == "unsat":
                    unsat_cnt += 1
                if s != ref:
                    r_ms = row["times_ms"].get(ref)
                    if r_ms is not None and r_ms <= timeout_s * 1000.0 + 1e-3:
                        r_s = min(timeout_s, r_ms / 1000.0)
                        n_mut += 1
                        wgm_logs.append(math.log(max(floor_s, t_s) / max(floor_s, r_s)))
                        sum_a += t_s
                        sum_b += r_s
            else:
                par2_sum += 2.0 * timeout_s

        times_s.sort()
        w_gm = math.exp(sum(wgm_logs) / len(wgm_logs)) if wgm_logs else (1.0 if s == ref else None)
        w_am = (sum_a / sum_b) if (n_mut > 0 and sum_b > 0.0) else (1.0 if s == ref else None)
        out[s] = {
            "n_total": n,
            "solved": len(times_s),
            "pct": 100.0 * len(times_s) / n,
            "sat": sat_cnt,
            "unsat": unsat_cnt,
            "par2_s": par2_sum / n,
            "ref": ref,
            "n_mut": n_mut if s != ref else len(times_s),
            "w_gm": w_gm,
            "w_am": w_am,
            "times_s": times_s,
        }
    return out


def export_dataset(
    out_dir: Path,
    x64_rows: list[dict[str, Any]] | None,
    arm64_rows: list[dict[str, Any]] | None,
    x64_solvers: list[str],
    arm64_solvers: list[str],
    run_tag: str,
    commit: str | None,
    suite: str,
    timeout_s: float,
    x64_cpu: str,
    arm64_cpu: str,
    metric: str = "wall_ms",
    solver_map_used: dict[str, Any] | None = None,
    solver_labels: dict[str, str] | None = None,
    filename: str = "survival.csv.xz",
    x64_host: str = "",
    arm64_host: str = "",
    gm_floor_ms: float = DEFAULT_GM_FLOOR_MS,
) -> tuple[Path, Path, dict[str, Any]]:
    """Export integer-ms `.csv.xz` + `manifest.json` into `out_dir`."""
    x64_cpu = sanitize_cpu_label(x64_cpu, "x64")
    arm64_cpu = sanitize_cpu_label(arm64_cpu, "arm64")
    validate_style_text(run_tag, "run_tag")
    validate_style_text(suite, "suite")
    if commit:
        validate_style_text(commit, "commit")

    if not filename.endswith(".csv.xz"):
        raise ValueError(f"--filename must end with .csv.xz, got {filename!r}")

    # Align rows by instance ID (preserving order from x64, then any arm64-only IDs).
    by_id: dict[str, dict[str, Any]] = {}
    ordered_ids: list[str] = []

    def ingest(rows: list[dict[str, Any]] | None, arch: str) -> None:
        if not rows:
            return
        for row in rows:
            rid = row["id"]
            if rid not in by_id:
                by_id[rid] = {
                    "id": rid,
                    "suite": row.get("suite") or suite,
                    "verdict": row.get("verdict") or "unknown",
                    "x64": {},
                    "arm64": {},
                }
                ordered_ids.append(rid)
            else:
                if by_id[rid]["verdict"] == "unknown" and row.get("verdict") in ("sat", "unsat"):
                    by_id[rid]["verdict"] = row["verdict"]
                if not by_id[rid]["suite"] and row.get("suite"):
                    by_id[rid]["suite"] = row["suite"]
            by_id[rid][arch] = dict(row["times_ms"])

    ingest(x64_rows, "x64")
    ingest(arm64_rows, "arm64")

    if not ordered_ids:
        raise ValueError("Cannot export empty dataset")

    all_solvers = order_solvers([*x64_solvers, *arm64_solvers])

    header_lines = [
        "# leanqbe-dual-arch-survival v1",
        f"# run_tag: {run_tag}",
        f"# commit: {commit or ''}",
        f"# suite: {suite}",
        f"# timeout_s: {timeout_s:g}",
        f"# metric: {metric}",
        "# time_unit: ms",
        f"# x64_cpu: {x64_cpu}",
        f"# arm64_cpu: {arm64_cpu}",
        f"# solvers: {','.join(all_solvers)}",
    ]
    csv_buf = io.StringIO()
    for hl in header_lines:
        validate_style_text(hl, "CSV header")
        csv_buf.write(hl + "\n")

    cols = ["id", "suite", "verdict"]
    cols.extend(f"x64_{s}_ms" for s in x64_solvers)
    cols.extend(f"arm64_{s}_ms" for s in arm64_solvers)

    writer = csv.writer(csv_buf, lineterminator="\n")
    writer.writerow(cols)
    for rid in ordered_ids:
        rec = by_id[rid]
        out_row = [rec["id"], rec["suite"], rec["verdict"]]
        for s in x64_solvers:
            v = rec["x64"].get(s)
            out_row.append("" if v is None else str(int(v)))
        for s in arm64_solvers:
            v = rec["arm64"].get(s)
            out_row.append("" if v is None else str(int(v)))
        writer.writerow(out_row)

    csv_bytes = csv_buf.getvalue().encode("utf-8")
    xz_bytes = lzma.compress(csv_bytes, preset=9, check=lzma.CHECK_CRC64)
    if len(xz_bytes) > MAX_DATASET_BYTES:
        raise ValueError(
            f"Exported dataset {filename} exceeds 1 MB cap: {len(xz_bytes)} B > {MAX_DATASET_BYTES}"
        )

    sha256_hex = hashlib.sha256(xz_bytes).hexdigest()
    summary: dict[str, Any] = {}
    for arch, rows, sols in (
        ("x64", x64_rows, x64_solvers),
        ("arm64", arm64_rows, arm64_solvers),
    ):
        if rows and sols:
            st_map = compute_solver_summary(rows, sols, timeout_s, gm_floor_ms=gm_floor_ms)
            summary[arch] = {
                s: {k: v for k, v in st.items() if k != "times_s"}
                for s, st in st_map.items()
            }

    manifest: dict[str, Any] = {
        "schema_version": 1,
        "run_tag": run_tag,
        "commit": commit or "",
        "suite": suite,
        "dataset_file": filename,
        "dataset_sha256": sha256_hex,
        "dataset_bytes": len(xz_bytes),
        "uncompressed_bytes": len(csv_bytes),
        "row_count": len(ordered_ids),
        "timeout_s": timeout_s,
        "gm_floor_ms": gm_floor_ms,
        "metric": metric,
        "time_unit": "ms",
        "hosts": {},
        "solvers": all_solvers,
        "x64_solvers": x64_solvers,
        "arm64_solvers": arm64_solvers,
        "solver_map": solver_map_used or {},
        "solver_labels": solver_labels or {},
        "summary": summary,
    }
    if x64_rows:
        manifest["hosts"]["x64"] = {
            "arch": "x86_64",
            "cpu_label": x64_cpu,
            **({"hostname": x64_host} if x64_host else {}),
        }
    if arm64_rows:
        manifest["hosts"]["arm64"] = {
            "arch": "aarch64",
            "cpu_label": arm64_cpu,
            **({"hostname": arm64_host} if arm64_host else {}),
        }

    manifest_str = json.dumps(manifest, indent=2, sort_keys=False) + "\n"
    validate_style_text(manifest_str, "manifest.json")

    out_dir.mkdir(parents=True, exist_ok=True)
    xz_path = out_dir / filename
    manifest_path = out_dir / "manifest.json"
    xz_path.write_bytes(xz_bytes)
    manifest_path.write_text(manifest_str, encoding="utf-8")
    return xz_path, manifest_path, manifest


# --- Survival Curve Rendering & Adaptive SVG Compaction ---


def compute_curve_points(
    times_s: Sequence[float], n_total: int, timeout_s: float
) -> tuple[np.ndarray, np.ndarray]:
    xs = [X_MIN_S]
    ys = [0.0]
    for idx, t in enumerate(times_s, start=1):
        xs.append(max(float(t), X_MIN_S))
        ys.append(100.0 * idx / n_total)
    xs.append(timeout_s)
    ys.append(100.0 * len(times_s) / n_total)
    return np.array(xs), np.array(ys)


def format_ratio_tail(stats: dict[str, Any], solver: str) -> str:
    if solver == stats["ref"]:
        return "ref"
    w_gm = stats["w_gm"]
    w_am = stats["w_am"]
    if w_gm is None or w_am is None:
        return "W-GM n/a / W-AM n/a"
    return f"{w_gm:.2f}x W-GM / {w_am:.2f}x W-AM"


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
    panel_specs: list[dict[str, Any]],
    commit: str | None,
    timeout_s: float,
    ref_solver: str | None = None,
    gm_floor_ms: float = DEFAULT_GM_FLOOR_MS,
    solver_labels: dict[str, str] | None = None,
    title_prefix: str | None = None,
) -> str:
    n_panels = len(panel_specs)
    figsize = (13.6, 5.2) if n_panels == 2 else (7.2, 5.0)
    fig, axes_raw = plt.subplots(
        1, n_panels, figsize=figsize, sharey=(n_panels > 1), facecolor="white"
    )
    axes = list(axes_raw) if n_panels > 1 else [axes_raw]

    for idx, (ax, spec) in enumerate(zip(axes, panel_specs)):
        rows = spec["rows"]
        solvers = spec["solvers"]
        title = spec["title"]
        validate_style_text(title, "panel title")
        summary = compute_solver_summary(
            rows, solvers, timeout_s, ref_solver=ref_solver, gm_floor_ms=gm_floor_ms
        )
        ax.set_facecolor("white")
        for s_idx, key in enumerate(solvers):
            st = style_for_solver(key, s_idx, solver_labels)
            stats = summary[key]
            xs, ys = compute_curve_points(stats["times_s"], stats["n_total"], timeout_s)
            tail = format_ratio_tail(stats, key)
            lbl = (
                f"{st['label']}: {stats['pct']:.1f}% ({stats['solved']}/{stats['n_total']}) | "
                f"PAR-2 {stats['par2_s']:.2f}s | {tail}"
            )
            lines = ax.step(
                xs,
                ys,
                where="post",
                color=st["color"],
                linestyle=st["linestyle"],
                linewidth=st["linewidth"],
                zorder=st["zorder"],
                label=lbl,
            )
            lines[0].set_gid(f"survival_curve_{idx}_{key}")
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
        leg_fs = 7.0 if len(solvers) <= 4 else max(5.9, 7.0 - 0.35 * (len(solvers) - 4))
        leg = ax.legend(
            loc="lower right",
            frameon=True,
            framealpha=0.96,
            facecolor="white",
            edgecolor="#D1D5DB",
            fontsize=leg_fs,
            borderpad=0.45,
            handlelength=2.0,
        )
        leg.set_zorder(20)

    axes[0].set_ylabel("% of instances solved", fontsize=10, color="#1F2937")
    counts = [len(p["rows"]) for p in panel_specs]
    if len(set(counts)) == 1:
        n_lbl = f"N = {counts[0]:,} CNFs"
    else:
        n_lbl = "N = " + " / ".join(f"{c:,}" for c in counts) + " CNFs"
    if title_prefix is None:
        if all(len(p["solvers"]) == 4 for p in panel_specs):
            eff_title = "Kissat 4-Way Survival Curves"
        elif n_panels == 2:
            eff_title = "Kissat Dual-Arch Survival Curves"
        else:
            eff_title = "Kissat Survival Curves"
    else:
        eff_title = title_prefix
    validate_style_text(eff_title, "suptitle")
    suptitle = (
        f"{eff_title} — {n_lbl} (commit {commit})"
        if commit
        else f"{eff_title} — {n_lbl}"
    )
    fig.suptitle(suptitle, fontsize=12.6, fontweight="bold", color="#111827", y=0.985)
    fig.tight_layout(rect=[0.0, 0.0, 1.0, 0.935])
    buf = io.StringIO()
    fig.savefig(buf, format="svg", facecolor="white", metadata={"Date": None})
    plt.close(fig)
    return buf.getvalue()


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
    if len(pts) <= 2 or eps <= 0.0:
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


def _dedup_rounded(pts: list[tuple[float, float]]) -> list[tuple[float, float]]:
    rpts: list[tuple[float, float]] = []
    for x, y in pts:
        rx, ry = round(x, 1), round(y, 1)
        if not rpts or (rx != rpts[-1][0] or ry != rpts[-1][1]):
            rpts.append((rx, ry))
    return rpts


def encode_polyline(pts: list[tuple[float, float]]) -> tuple[str, int]:
    if not pts:
        return "", 0
    rpts = _dedup_rounded(pts)
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
    return "".join(out), len(out)


def _decimate_points_adaptive(
    pts: list[tuple[float, float]],
    target_vertices: int,
    max_vertices: int,
    fixed_eps: float | None,
) -> tuple[str, int]:
    base = _dedup_rounded(pts)
    if fixed_eps is not None:
        simplified = rdp(base, fixed_eps) if len(base) > 20 and fixed_eps > 0.0 else base
        return encode_polyline(simplified)

    if len(base) <= max_vertices:
        # Preserve small/medium curves closely (only negligible collinear smoothing if > 250).
        if len(base) <= 250:
            return encode_polyline(base)
        return encode_polyline(rdp(base, 0.05))

    # Binary search RDP epsilon so dense curves land cleanly near `target_vertices` (<= `max_vertices`).
    lo, hi = 0.01, 4.0
    best_d, best_cnt = encode_polyline(rdp(base, hi))
    best_diff = abs(best_cnt - target_vertices)
    for _ in range(20):
        mid = 0.5 * (lo + hi)
        d_mid, cnt_mid = encode_polyline(rdp(base, mid))
        if cnt_mid > max_vertices:
            lo = mid
        else:
            diff = abs(cnt_mid - target_vertices)
            if best_cnt > max_vertices or diff < best_diff:
                best_d, best_cnt, best_diff = d_mid, cnt_mid, diff
            if cnt_mid < target_vertices:
                hi = mid
            else:
                lo = mid
    if best_cnt > max_vertices:
        best_d, best_cnt = encode_polyline(rdp(base, 8.0))
    return best_d, best_cnt


def compact_path_d(
    d: str,
    is_curve: bool,
    target_vertices: int,
    max_vertices: int,
    fixed_eps: float | None,
) -> tuple[str, int | None]:
    if _ML_RE.match(d):
        pts = [(float(m.group(2)), float(m.group(3))) for m in _NUM_PAIR_RE.finditer(d)]
        if is_curve:
            return _decimate_points_adaptive(pts, target_vertices, max_vertices, fixed_eps)
        eps = fixed_eps if fixed_eps is not None else 0.45
        if len(pts) > 20 and eps > 0.0:
            pts = rdp(pts, eps)
        enc, _ = encode_polyline(pts)
        return enc, None
    d2 = re.sub(r"-?\d+\.\d+", lambda m: fmt1(float(m.group(0))), d)
    d2 = re.sub(r"\s+", " ", d2).strip()
    return re.sub(r"\s*([MLHVCSQTAZmlhvcsqtaz])\s*", r"\1", d2), None


def compact_svg_text(
    raw_svg: str,
    target_vertices: int = DEFAULT_TARGET_VERTICES,
    max_vertices: int = DEFAULT_MAX_VERTICES,
    rdp_eps: float | None = None,
) -> str:
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

    # Identify survival curve paths before stripping unreferenced IDs.
    curve_elems: set[ET.Element] = set()
    for g_el in root.iter(f"{{{svg_ns}}}g"):
        gid = g_el.get("id", "")
        if gid.startswith("survival_curve_"):
            for child in g_el:
                if child.tag == f"{{{svg_ns}}}path":
                    curve_elems.add(child)

    # 2. Compact path geometry & strip no-op rotate(-0 ...) transforms.
    for el in root.iter():
        tag = el.tag.split("}")[-1]
        if tag == "path" and "d" in el.attrib:
            is_curve = el in curve_elems
            comp_d, _ = compact_path_d(
                el.attrib["d"],
                is_curve=is_curve,
                target_vertices=target_vertices,
                max_vertices=max_vertices,
                fixed_eps=rdp_eps,
            )
            el.set("d", comp_d)
            if is_curve:
                el.set("data-survival-curve", "1")
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
                    ch.get("id", "").startswith(("xtick_", "ytick_", "line2d_", "patch_", "survival_curve_"))
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
            if ch.tag == f"{{{svg_ns}}}path" and ch.get("data-survival-curve") != "1":
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
    for st_norm, cnt in sorted(style_counts.items(), key=lambda kv: (-kv[1], kv[0])):
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


def render_and_compact_svg(
    panel_specs: list[dict[str, Any]],
    commit: str | None,
    timeout_s: float,
    ref_solver: str | None = None,
    gm_floor_ms: float = DEFAULT_GM_FLOOR_MS,
    solver_labels: dict[str, str] | None = None,
    title_prefix: str | None = None,
    target_vertices: int = DEFAULT_TARGET_VERTICES,
    max_vertices: int = DEFAULT_MAX_VERTICES,
    rdp_eps: float | None = None,
) -> tuple[str, str, dict[str, Any]]:
    raw_svg = render_raw_svg(
        panel_specs=panel_specs,
        commit=commit,
        timeout_s=timeout_s,
        ref_solver=ref_solver,
        gm_floor_ms=gm_floor_ms,
        solver_labels=solver_labels,
        title_prefix=title_prefix,
    )
    budget_target = target_vertices
    budget_max = max_vertices
    compact = compact_svg_text(
        raw_svg, target_vertices=budget_target, max_vertices=budget_max, rdp_eps=rdp_eps
    )
    # If many curves push SVG above 40 KB, tighten per-curve budget automatically unless rdp_eps forced.
    while len(compact.encode("utf-8")) > MAX_SVG_BYTES and rdp_eps is None and budget_max > 60:
        budget_max = max(60, int(budget_max * 0.72))
        budget_target = min(budget_target, int(budget_max * 0.85))
        compact = compact_svg_text(
            raw_svg, target_vertices=budget_target, max_vertices=budget_max, rdp_eps=None
        )
    metrics = validate_svg_document(compact, max_vertices=max_vertices)
    return raw_svg, compact, metrics


# --- Git Ref & Results Dir Loading ---


def _git_run(repo: Path, args: Sequence[str]) -> bytes:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed (rc={proc.returncode}): {proc.stderr.decode('utf-8', 'replace').strip()}"
        )
    return proc.stdout


def load_from_git_ref(
    git_ref: str,
    git_path: str,
    git_repo: Path,
) -> tuple[dict[str, Any] | None, str]:
    """Load optional `manifest.json` and dataset CSV text from `<git_ref>:<git_path>`."""
    rel = git_path.strip().lstrip("./").rstrip("/")
    manifest: dict[str, Any] | None = None

    # Support either directory path (`bench/results/<tag>`) or direct file path (`.../survival.csv.xz`).
    if rel.endswith((".csv", ".csv.xz")):
        raw_bytes = _git_run(git_repo, ["show", f"{git_ref}:{rel}"])
        if rel.endswith(".xz"):
            return None, lzma.decompress(raw_bytes).decode("utf-8")
        return None, raw_bytes.decode("utf-8")

    # Try manifest.json first.
    try:
        m_bytes = _git_run(git_repo, ["show", f"{git_ref}:{rel}/manifest.json"])
        manifest = json.loads(m_bytes.decode("utf-8"))
    except RuntimeError:
        manifest = None

    dataset_name = manifest.get("dataset_file") if manifest else None
    if not dataset_name:
        tree_out = _git_run(git_repo, ["ls-tree", "--name-only", f"{git_ref}:{rel}"]).decode("utf-8")
        candidates = [line.strip() for line in tree_out.splitlines() if line.strip()]
        for preferred in ("survival.csv.xz",):
            if preferred in candidates:
                dataset_name = preferred
                break
        if not dataset_name:
            xz_files = sorted(c for c in candidates if c.endswith(".csv.xz"))
            csv_files = sorted(c for c in candidates if c.endswith(".csv"))
            if xz_files:
                dataset_name = xz_files[0]
            elif csv_files:
                dataset_name = csv_files[0]
    if not dataset_name:
        raise FileNotFoundError(
            f"No .csv.xz or .csv dataset found at {git_ref}:{rel}"
        )

    raw_bytes = _git_run(git_repo, ["show", f"{git_ref}:{rel}/{dataset_name}"])
    if dataset_name.endswith(".xz"):
        csv_text = lzma.decompress(raw_bytes).decode("utf-8")
    else:
        csv_text = raw_bytes.decode("utf-8")
    return manifest, csv_text


def load_from_results_dir(results_dir: Path) -> tuple[dict[str, Any] | None, str]:
    if not results_dir.is_dir():
        raise FileNotFoundError(f"Results directory does not exist: {results_dir}")
    manifest_path = results_dir / "manifest.json"
    manifest = (
        json.loads(manifest_path.read_text(encoding="utf-8"))
        if manifest_path.is_file()
        else None
    )
    dataset_path: Path | None = None
    if manifest and manifest.get("dataset_file"):
        cand = results_dir / str(manifest["dataset_file"])
        if cand.is_file():
            dataset_path = cand
    if dataset_path is None:
        preferred = results_dir / "survival.csv.xz"
        if preferred.is_file():
            dataset_path = preferred
    if dataset_path is None:
        xzs = sorted(results_dir.glob("*.csv.xz"))
        csvs = sorted(results_dir.glob("*.csv"))
        if xzs:
            dataset_path = xzs[0]
        elif csvs:
            dataset_path = csvs[0]
    if dataset_path is None:
        raise FileNotFoundError(f"No .csv.xz or .csv dataset found in {results_dir}")
    return manifest, _open_text_maybe_xz(dataset_path)


# --- CLI Entrypoints ---


def _filter_solvers(
    present: list[str], requested: Sequence[str] | None
) -> list[str]:
    if not requested:
        return present
    missing = [s for s in requested if s not in present]
    if missing:
        # Keep only solvers that exist for this arch if another arch requested them,
        # unless NONE of the requested solvers exist.
        kept = [s for s in requested if s in present]
        if not kept:
            raise ValueError(f"Requested solvers {requested} not found in available {present}")
        return kept
    return list(requested)


def _add_common_input_args(ap: argparse.ArgumentParser) -> None:
    ap.add_argument(
        "--csv",
        type=Path,
        default=None,
        help="Combined dual-arch timing CSV or `.csv.xz`.",
    )
    ap.add_argument(
        "--x64",
        nargs="+",
        type=Path,
        default=None,
        help="One or more x86-64 `.json`, `.csv`, or `.csv.xz` files.",
    )
    ap.add_argument(
        "--arm64",
        nargs="+",
        type=Path,
        default=None,
        help="One or more AArch64 `.json`, `.csv`, or `.csv.xz` files.",
    )
    ap.add_argument(
        "--solvers",
        nargs="+",
        default=None,
        help="Ordered subset of solver keys to include.",
    )
    ap.add_argument(
        "--solver-map",
        nargs="+",
        default=None,
        help="Optional solver rename mappings (`raw=canonical` or `arch:raw=canonical`).",
    )
    ap.add_argument(
        "--solver-label",
        nargs="+",
        default=None,
        help="Optional legend label overrides (`solver=Display Label`).",
    )
    ap.add_argument(
        "--commit",
        default=None,
        help="Short commit SHA to record/display (e.g. e190f461).",
    )
    ap.add_argument(
        "--suite",
        default=None,
        help="Suite display label (e.g. 'Combined Corpus', 'Stage-1', 'Canary').",
    )
    ap.add_argument(
        "--x64-cpu",
        default=None,
        help=f"x86-64 CPU label (default: {DEFAULT_X64_CPU!r}).",
    )
    ap.add_argument(
        "--arm64-cpu",
        default=None,
        help=f"AArch64 CPU label (default: {DEFAULT_ARM64_CPU!r}).",
    )
    ap.add_argument(
        "--timeout",
        type=float,
        default=None,
        help="Per-instance wall-clock timeout in seconds (default: inferred or 30.0).",
    )
    ap.add_argument(
        "--metric",
        choices=["wall_ms", "internal_ms"],
        default="wall_ms",
        help="Timing metric to extract from JSON/DevRez CSV (default: wall_ms).",
    )
    ap.add_argument(
        "--gm-floor-ms",
        type=float,
        default=DEFAULT_GM_FLOOR_MS,
        help=f"Timing floor in ms for W-GM ratio (default: {DEFAULT_GM_FLOOR_MS}).",
    )
    ap.add_argument(
        "--dedup",
        choices=["id", "suite-id", "none"],
        default="id",
        help="Deduplication strategy when merging multiple inputs per arch (default: id).",
    )


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(
        description="Export compressed dual-arch Kissat results and plot <40 KB survival SVGs."
    )
    sub = ap.add_subparsers(dest="command", required=True)

    ap_exp = sub.add_parser(
        "export",
        help="Export compact integer-ms `.csv.xz` (<1 MB) + `manifest.json` into `--out-dir`.",
    )
    _add_common_input_args(ap_exp)
    ap_exp.add_argument(
        "--out-dir",
        type=Path,
        required=True,
        help="Destination directory (e.g. bench/results/<run_tag>/ on branch `artifacts`).",
    )
    ap_exp.add_argument(
        "--run-tag",
        default=None,
        help="Run tag recorded in manifest/header (default: derived from --out-dir name).",
    )
    ap_exp.add_argument(
        "--filename",
        default="survival.csv.xz",
        help="Output `.csv.xz` filename inside `--out-dir` (default: survival.csv.xz).",
    )

    ap_plt = sub.add_parser(
        "plot",
        help="Render a decimated `<40 KB` dual-arch survival SVG (default subcommand).",
    )
    _add_common_input_args(ap_plt)
    ap_plt.add_argument(
        "--results-dir",
        type=Path,
        default=None,
        help="Directory containing `manifest.json` + `.csv.xz` / `.csv`.",
    )
    ap_plt.add_argument(
        "--git-ref",
        default=DEFAULT_GIT_REF,
        help=f"Git branch/ref holding bench artifacts (default: {DEFAULT_GIT_REF!r}).",
    )
    ap_plt.add_argument(
        "--git-path",
        default=None,
        help="Path under `--git-ref` (e.g. `bench/results/<run_tag>`), read via `git show`.",
    )
    ap_plt.add_argument(
        "--git-repo",
        type=Path,
        default=Path("."),
        help="Git repository root for `--git-ref`/`--git-path` (default: current directory).",
    )
    ap_plt.add_argument(
        "--ref",
        default=None,
        help="Reference solver for W-GM and W-AM ratios (default: c1, else c0direct, else first).",
    )
    ap_plt.add_argument(
        "--title",
        default=None,
        help="Optional main title prefix (default: auto based on solver/panel count).",
    )
    ap_plt.add_argument(
        "--target-vertices",
        type=int,
        default=DEFAULT_TARGET_VERTICES,
        help=f"Target vertices per dense curve (default: {DEFAULT_TARGET_VERTICES}).",
    )
    ap_plt.add_argument(
        "--max-vertices",
        type=int,
        default=DEFAULT_MAX_VERTICES,
        help=f"Hard vertex cap per survival curve (default: {DEFAULT_MAX_VERTICES}).",
    )
    ap_plt.add_argument(
        "--rdp-tol",
        type=float,
        default=None,
        help="Optional fixed Ramer-Douglas-Peucker tolerance in points (overrides adaptive).",
    )
    ap_plt.add_argument(
        "-o",
        "--out",
        type=Path,
        required=True,
        help="Output SVG file path.",
    )
    return ap


def _load_dual_inputs_from_args(args: argparse.Namespace) -> dict[str, Any]:
    for flag, val in (
        ("--x64-cpu", args.x64_cpu),
        ("--arm64-cpu", args.arm64_cpu),
        ("--suite", args.suite),
        ("--commit", args.commit),
        ("--title", getattr(args, "title", None)),
        ("--run-tag", getattr(args, "run_tag", None)),
    ):
        if val:
            validate_style_text(val, context=flag)

    global_map, arch_map = parse_solver_map(args.solver_map)
    solver_labels = parse_solver_labels(args.solver_label)

    has_git = getattr(args, "git_path", None) is not None
    has_dir = getattr(args, "results_dir", None) is not None
    has_csv = args.csv is not None
    has_arch = bool(args.x64 or args.arm64)

    modes = sum([has_git, has_dir, has_csv, has_arch])
    if modes == 0:
        raise ValueError(
            "Specify one input source: --results-dir, --git-path [--git-ref], --csv, or --x64/--arm64"
        )
    if modes > 1:
        raise ValueError(
            "Input sources --results-dir, --git-path, --csv, and --x64/--arm64 are mutually exclusive"
        )

    manifest: dict[str, Any] | None = None
    x64_rows: list[dict[str, Any]] | None = None
    arm64_rows: list[dict[str, Any]] | None = None
    x64_sols: list[str] = []
    arm64_sols: list[str] = []
    x64_host = ""
    arm64_host = ""

    if has_git or has_dir:
        if has_git:
            manifest, csv_text = load_from_git_ref(args.git_ref, args.git_path, args.git_repo)
        else:
            manifest, csv_text = load_from_results_dir(args.results_dir)
        x64_r, arm64_r, x64_s, arm64_s, csv_meta = parse_dual_csv_text(
            csv_text,
            timeout_override=args.timeout,
            global_map=global_map,
            arch_map=arch_map,
        )
        if x64_r:
            x64_rows, x64_sols = x64_r, x64_s
        if arm64_r:
            arm64_rows, arm64_sols = arm64_r, arm64_s
        m_hosts = manifest.get("hosts", {}) if manifest else {}
        inferred_timeout = (
            args.timeout
            if args.timeout is not None
            else float((manifest or {}).get("timeout_s") or csv_meta["timeout_s"])
        )
        inferred_commit = args.commit or (manifest or {}).get("commit") or csv_meta["commit"] or None
        inferred_suite = args.suite or (manifest or {}).get("suite") or csv_meta["suite"] or "Combined Corpus"
        x64_cpu = args.x64_cpu or m_hosts.get("x64", {}).get("cpu_label") or csv_meta["x64_cpu"]
        arm64_cpu = args.arm64_cpu or m_hosts.get("arm64", {}).get("cpu_label") or csv_meta["arm64_cpu"]
        if manifest and manifest.get("solver_labels"):
            merged_labels = dict(manifest["solver_labels"])
            merged_labels.update(solver_labels)
            solver_labels = merged_labels
    elif has_csv:
        if not args.csv.is_file():
            raise FileNotFoundError(f"Missing CSV file: {args.csv}")
        csv_text = _open_text_maybe_xz(args.csv)
        x64_r, arm64_r, x64_s, arm64_s, csv_meta = parse_dual_csv_text(
            csv_text,
            timeout_override=args.timeout,
            global_map=global_map,
            arch_map=arch_map,
        )
        if x64_r:
            x64_rows, x64_sols = x64_r, x64_s
        if arm64_r:
            arm64_rows, arm64_sols = arm64_r, arm64_s
        inferred_timeout = args.timeout if args.timeout is not None else csv_meta["timeout_s"]
        inferred_commit = args.commit or csv_meta["commit"] or None
        inferred_suite = args.suite or csv_meta["suite"] or "Combined Corpus"
        x64_cpu = args.x64_cpu or csv_meta["x64_cpu"]
        arm64_cpu = args.arm64_cpu or csv_meta["arm64_cpu"]
    else:
        timeouts: list[float] = []
        suites: list[str] = []
        commits: list[str] = []
        x64_cpu = args.x64_cpu or DEFAULT_X64_CPU
        arm64_cpu = args.arm64_cpu or DEFAULT_ARM64_CPU
        if args.x64:
            x64_rows, x64_sols, minfo = load_arch_inputs(
                args.x64,
                "x64",
                timeout_override=args.timeout,
                metric=args.metric,
                global_map=global_map,
                arch_map=arch_map,
                dedup=args.dedup,
            )
            timeouts.append(minfo["timeout_s"])
            if minfo["suite"]:
                suites.append(minfo["suite"])
            if minfo["commit"]:
                commits.append(minfo["commit"])
            x64_cpu = args.x64_cpu or minfo["cpu_label"]
            x64_host = minfo["hostname"]
        if args.arm64:
            arm64_rows, arm64_sols, minfo = load_arch_inputs(
                args.arm64,
                "arm64",
                timeout_override=args.timeout,
                metric=args.metric,
                global_map=global_map,
                arch_map=arch_map,
                dedup=args.dedup,
            )
            timeouts.append(minfo["timeout_s"])
            if minfo["suite"] and minfo["suite"] not in suites:
                suites.append(minfo["suite"])
            if minfo["commit"] and minfo["commit"] not in commits:
                commits.append(minfo["commit"])
            arm64_cpu = args.arm64_cpu or minfo["cpu_label"]
            arm64_host = minfo["hostname"]
        inferred_timeout = float(args.timeout if args.timeout is not None else (min(timeouts) if timeouts else DEFAULT_TIMEOUT_S))
        inferred_commit = args.commit or (commits[0] if commits else None)
        inferred_suite = args.suite or (" + ".join(suites) if suites else "Combined Corpus")

    if x64_sols:
        x64_sols = _filter_solvers(x64_sols, args.solvers)
    if arm64_sols:
        arm64_sols = _filter_solvers(arm64_sols, args.solvers)

    return {
        "x64_rows": x64_rows,
        "arm64_rows": arm64_rows,
        "x64_solvers": x64_sols,
        "arm64_solvers": arm64_sols,
        "timeout_s": inferred_timeout,
        "commit": inferred_commit,
        "suite": inferred_suite,
        "x64_cpu": sanitize_cpu_label(x64_cpu, "x64"),
        "arm64_cpu": sanitize_cpu_label(arm64_cpu, "arm64"),
        "x64_host": x64_host,
        "arm64_host": arm64_host,
        "solver_map": {"global": global_map, **{k: v for k, v in arch_map.items() if v}},
        "solver_labels": solver_labels,
    }


def cmd_export(args: argparse.Namespace) -> int:
    loaded = _load_dual_inputs_from_args(args)
    run_tag = args.run_tag or args.out_dir.name or "dual_arch"
    xz_path, manifest_path, manifest = export_dataset(
        out_dir=args.out_dir,
        x64_rows=loaded["x64_rows"],
        arm64_rows=loaded["arm64_rows"],
        x64_solvers=loaded["x64_solvers"],
        arm64_solvers=loaded["arm64_solvers"],
        run_tag=run_tag,
        commit=loaded["commit"],
        suite=loaded["suite"],
        timeout_s=loaded["timeout_s"],
        x64_cpu=loaded["x64_cpu"],
        arm64_cpu=loaded["arm64_cpu"],
        metric=args.metric,
        solver_map_used=loaded["solver_map"],
        solver_labels=loaded["solver_labels"],
        filename=args.filename,
        x64_host=loaded["x64_host"],
        arm64_host=loaded["arm64_host"],
        gm_floor_ms=args.gm_floor_ms,
    )
    print(
        f"Exported {xz_path} ({manifest['dataset_bytes']:,} B, "
        f"{manifest['row_count']} rows, sha256={manifest['dataset_sha256'][:12]}) + {manifest_path}"
    )
    return 0


def cmd_plot(args: argparse.Namespace) -> int:
    if args.max_vertices > 400:
        raise ValueError(f"--max-vertices must be <= 400, got {args.max_vertices}")
    loaded = _load_dual_inputs_from_args(args)
    panels: list[dict[str, Any]] = []
    suite = loaded["suite"] or "Combined Corpus"
    if loaded["x64_rows"]:
        n = len(loaded["x64_rows"])
        panels.append(
            {
                "rows": loaded["x64_rows"],
                "solvers": loaded["x64_solvers"],
                "title": f"x86-64 — {loaded['x64_cpu']}\n{suite} (N = {n:,})",
            }
        )
    if loaded["arm64_rows"]:
        n = len(loaded["arm64_rows"])
        panels.append(
            {
                "rows": loaded["arm64_rows"],
                "solvers": loaded["arm64_solvers"],
                "title": f"AArch64 — {loaded['arm64_cpu']}\n{suite} (N = {n:,})",
            }
        )
    if not panels:
        raise ValueError("No benchmark data loaded for either x86-64 or AArch64")

    raw_svg, compact, metrics = render_and_compact_svg(
        panel_specs=panels,
        commit=loaded["commit"],
        timeout_s=loaded["timeout_s"],
        ref_solver=args.ref,
        gm_floor_ms=args.gm_floor_ms,
        solver_labels=loaded["solver_labels"],
        title_prefix=args.title,
        target_vertices=args.target_vertices,
        max_vertices=args.max_vertices,
        rdp_eps=args.rdp_tol,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(compact, encoding="utf-8")
    raw_b = len(raw_svg.encode("utf-8"))
    gz_b = len(gzip.compress(compact.encode("utf-8"), compresslevel=9))
    print(
        f"Wrote {args.out}: {raw_b:,} B -> {metrics['bytes']:,} B "
        f"({gz_b:,} B gzipped, vertices={metrics['curve_vertices']})"
    )
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    raw_argv = list(sys.argv[1:] if argv is None else argv)
    if raw_argv and raw_argv[0] not in ("export", "plot", "-h", "--help"):
        raw_argv = ["plot", *raw_argv]
    ap = build_parser()
    args = ap.parse_args(raw_argv)
    if args.command == "export":
        return cmd_export(args)
    return cmd_plot(args)


if __name__ == "__main__":
    sys.exit(main())
