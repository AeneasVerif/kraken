#!/usr/bin/env python3
"""Deterministic event-trace lockstep comparator & first-divergence bisector.

Compares canonical sorted-DIMACS event traces (DEC, CONFL, LEARN, RST, MODE,
RED, INPROC, UNIT0, END) between upstream Kissat 4.0.4 and C0 (Plain/Full*).
Supports:
  - --plain : 11-rung CDCL flag ladder (--plain -> ... -> +eagersubsume)
  - --coarse: coarse timeline diff (UNIT0/INPROC/MODE/RED/RST/END)
  - C3b wrapper generation & zero-perturbation verification
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True

DEFAULT_KISSAT_REF = (
    "/usr/local/google/home/andreser/.gemini/jetski/brain/"
    "f0cea481-7468-44ed-8bb8-8bc2c8436b38/scratch/kissat-ref-clang/build/kissat"
)
DEFAULT_KISSAT_SRC = (
    "/usr/local/google/home/andreser/.gemini/jetski/brain/"
    "f0cea481-7468-44ed-8bb8-8bc2c8436b38/scratch/kissat-ref-clang"
)
COARSE_KINDS = {"UNIT0", "INPROC", "MODE", "RED", "RST", "END"}

PLAIN_LADDER = [
    ("plain", []),
    ("+shrink", ["--shrink=3"]),
    ("+restart", ["--restart=1"]),
    ("+stable", ["--stable=1"]),
    ("+reduce", ["--reduce=1"]),
    ("+target", ["--target=1"]),
    ("+rephase", ["--rephase=1"]),
    ("+bumpreasons", ["--bumpreasons=1"]),
    ("+otfs", ["--otfs=1"]),
    ("+chrono", ["--chrono=1"]),
    ("+eagersubsume", ["--eagersubsume=1"]),
]

PLAIN_BASE_FLAGS = [
    "--plain", "--seed=0", "--phase=1", "--forcephase=0",
    "--preprocess=0", "--simplify=0", "--lucky=0", "--warmup=0",
    "--chrono=0", "--otfs=0", "--bumpreasons=0", "--eagersubsume=0",
    "--rephase=0", "--target=0", "--stable=2", "--reduce=0",
    "--restart=0", "--shrink=0", "--minimize=1", "--minimizedepth=1000",
    "--tumble=0", "--reorder=0", "--randec=0",
]

HOOKED_FNS = [
    "kissat_solve_bytes", "full_init_state", "plain_init_state",
    "full_preprocess", "full_search",
    "full_parse_body", "full_ingest_cl", "full_propagate_ignore",
    "full_prop_lit", "full_assign_lvl", "full_decide", "full_one_lit_confl",
    "full_det_new_level", "full_learn_clause", "full_otfs_subsume",
    "full_restart", "full_switch_mode", "full_reduce", "full_arena_sweep",
    "full_add_unit", "full_substitute", "full_congruence_dense",
    "full_sweep_dense", "full_transitive", "full_probe_run", "full_vivify",
    "full_forward_sub", "full_elim_bve", "full_factor", "full_backbone",
    "full_probe", "full_eliminate", "full_compact",
    "full_kitten_solve", "full_k512_solve", "full_m4_sweep_dense",
    "plain_parse_body", "plain_propagate", "plain_assign", "plain_decide",
    "plain_analyze", "plain_ema_update", "plain_restart_due",
    "plain_switch_mode", "plain_reduce",
]

C3B_RUNNER_CPP = r"""
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

#include "tqbe_rt.hpp"
#include "kissat_verify.h"

namespace tqbe_gen {
#include "__GEN_HPP__"
}

static uint64_t rd64(const void *p, size_t w) {
  uint64_t x = 0;
  std::memcpy(&x, static_cast<const uint8_t *>(p) + w * 8ULL, 8ULL);
  return x;
}

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  uint64_t work_bytes = 67108864ULL;
  uint64_t fuel = 2000000000ULL;
  for (int i = 2; i < argc; ++i) {
    if (std::strncmp(argv[i], "--work-bytes=", 13) == 0) {
      work_bytes = std::strtoull(argv[i] + 13, nullptr, 10);
    } else if (std::strncmp(argv[i], "--fuel=", 7) == 0) {
      fuel = std::strtoull(argv[i] + 7, nullptr, 10);
    }
  }
  FILE *f = std::fopen(argv[1], "rb");
  if (!f) return 2;
  std::fseek(f, 0, SEEK_END);
  long sz = std::ftell(f);
  std::rewind(f);
  std::vector<uint8_t> cnf(sz > 0 ? static_cast<size_t>(sz) : 0);
  if (sz > 0 && std::fread(cnf.data(), 1, static_cast<size_t>(sz), f)
                != static_cast<size_t>(sz)) {
    std::fclose(f);
    return 2;
  }
  std::fclose(f);

  std::vector<uint8_t> work(static_cast<size_t>(work_bytes), 0);
  ::tqbe::Mem mem;
  uint64_t cnf_addr = reinterpret_cast<uint64_t>(cnf.data());
  uint64_t raw_ptr = reinterpret_cast<uint64_t>(work.data());
  uint64_t pad = (8ULL - (raw_ptr & 7ULL)) & 7ULL;
  uint64_t hdr_addr = raw_ptr + pad;
  uint64_t avail = work_bytes > pad ? (work_bytes - pad) : 0ULL;

  auto t0 = std::chrono::steady_clock::now();
  uint64_t st = tqbe_gen::kissat_solve_bytes(
      mem, ::tqbe::bits<64>(cnf_addr), ::tqbe::bits<64>(cnf.size()),
      ::tqbe::bits<64>(hdr_addr), ::tqbe::bits<64>(avail),
      ::tqbe::bits<64>(fuel)).data;
  auto t1 = std::chrono::steady_clock::now();
  double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();

  const uint8_t *hp = work.data() + pad;
  if (st == 10ULL) {
    uint64_t mv = rd64(hp, 0);
    const int8_t *vals =
        reinterpret_cast<const int8_t *>(static_cast<uintptr_t>(rd64(hp, 8)));
    if (kissat_verify_dimacs_model(
            reinterpret_cast<const char *>(cnf.data()),
            static_cast<uint64_t>(cnf.size()), vals, mv) != 1) {
      st = 3ULL;
    }
  }
  std::printf(
      "{\"status\":%llu,\"ms\":%.3f,\"conflicts\":%llu,\"learned_lits\":%llu,"
      "\"min_removed\":%llu,\"search_ticks\":%llu,\"oom\":%llu}\n",
      (unsigned long long)st, ms,
      (unsigned long long)rd64(hp, 42),
      (unsigned long long)rd64(hp, 43),
      (unsigned long long)rd64(hp, 44),
      (unsigned long long)rd64(hp, 75),
      (unsigned long long)rd64(hp, 95));
  return 0;
}
"""


def _build_wrapper_block(present):
    """Build C++20 inline wrappers inside namespace tqbe_gen."""
    is_full = "true" if "full_decide" in present else "false"
    lines = [
        "",
        "}  // namespace tqbe_gen",
        "#include \"c3b_lockstep_trace.hpp\"",
        "namespace tqbe_gen {",
        "",
    ]
    for ifn in ("full_init_state", "plain_init_state"):
        if ifn in present:
            lines.append(
                f"template <typename... A> inline auto {ifn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> cp, ::tqbe::bits<64> ce, "
                f"::tqbe::bits<64> h, A... a) {{\n"
                f"  auto r = raw_{ifn}(mem, cp, ce, h, a...);\n"
                f"  if (r) ::c3b_trace::on_init_exit(h.data, {is_full});\n"
                f"  return r;\n"
                f"}}"
            )
    for sfn in ("full_preprocess", "full_search"):
        if sfn in present:
            lines.append(
                f"inline ::tqbe::bits<64> {sfn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h) {{\n"
                f"  auto r = raw_{sfn}(mem, h);\n"
                f"  ::c3b_trace::flush_ext_telem(h.data);\n"
                f"  return r;\n"
                f"}}"
            )
    if "full_parse_body" in present:
        lines.append(
            "template <typename... A> inline auto full_parse_body("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h, A... a) {\n"
            "  ::c3b_trace::on_parse_enter(h.data);\n"
            "  ::c3b_trace::UnitSrcScope us(\"parse\");\n"
            "  ::c3b_trace::PropScope ps(h.data);\n"
            "  return raw_full_parse_body(mem, h, a...);\n"
            "}"
        )
    if "plain_parse_body" in present:
        lines.append(
            "template <typename... A> inline auto plain_parse_body("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h, A... a) {\n"
            "  ::c3b_trace::on_parse_enter(h.data);\n"
            "  ::c3b_trace::UnitSrcScope us(\"parse\");\n"
            "  ::c3b_trace::PropScope ps(h.data);\n"
            "  return raw_plain_parse_body(mem, h, a...);\n"
            "}"
        )
    if "full_ingest_cl" in present:
        lines.append(
            "template <typename... A> inline auto full_ingest_cl("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h, A... a) {\n"
            "  ::c3b_trace::UnitSrcScope us(\"parse\");\n"
            "  return raw_full_ingest_cl(mem, h, a...);\n"
            "}"
        )
    for pfn in ("full_propagate_ignore", "full_prop_lit", "plain_propagate"):
        if pfn in present:
            lines.append(
                f"template <typename... A> inline auto {pfn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h, A... a) {{\n"
                f"  ::c3b_trace::PropScope ps(h.data);\n"
                f"  return raw_{pfn}(mem, h, a...);\n"
                f"}}"
            )
    for afn in ("full_assign_lvl", "plain_assign", "full_add_unit", "full_arena_sweep"):
        if afn in present:
            lines.append(
                f"template <typename... A> inline auto {afn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h, A... a) {{\n"
                f"  uint64_t te0 = ::c3b_trace::detail::rd64(h.data, 18);\n"
                f"  auto r = raw_{afn}(mem, h, a...);\n"
                f"  uint64_t te1 = ::c3b_trace::detail::rd64(h.data, 18);\n"
                f"  ::c3b_trace::emit_unit0_range(h.data, te0, te1, \"prop\");\n"
                f"  return r;\n"
                f"}}"
            )
    for dfn in ("full_decide", "plain_decide"):
        if dfn in present:
            lines.append(
                f"inline ::tqbe::bits<64> {dfn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h) {{\n"
                f"  uint64_t te0 = ::c3b_trace::detail::rd64(h.data, 18);\n"
                f"  uint64_t lv0 = ::c3b_trace::detail::rd64(h.data, 20);\n"
                f"  auto r = raw_{dfn}(mem, h);\n"
                f"  ::c3b_trace::on_decide_exit(h.data, te0, lv0, r.data);\n"
                f"  return r;\n"
                f"}}"
            )
    for cfn in ("full_one_lit_confl", "plain_analyze"):
        if cfn in present:
            lines.append(
                f"inline ::tqbe::bits<64> {cfn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h) {{\n"
                f"  ::c3b_trace::on_confl_enter(h.data);\n"
                f"  return raw_{cfn}(mem, h);\n"
                f"}}"
            )
    if "full_det_new_level" in present:
        lines.append(
            "inline ::tqbe::bits<64> full_det_new_level("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h, ::tqbe::bits<64> j) {\n"
            "  auto r = raw_full_det_new_level(mem, h, j);\n"
            "  ::c3b_trace::on_det_new_level_exit(h.data, j.data, r.data);\n"
            "  return r;\n"
            "}"
        )
    if "full_learn_clause" in present:
        lines.append(
            "inline ::tqbe::bits<64> full_learn_clause("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h, ::tqbe::bits<64> g) {\n"
            "  ::c3b_trace::on_learn_enter(h.data, g.data, true);\n"
            "  ::c3b_trace::UnitSrcScope us(\"learn\");\n"
            "  uint64_t te0 = ::c3b_trace::detail::rd64(h.data, 18);\n"
            "  auto r = raw_full_learn_clause(mem, h, g);\n"
            "  uint64_t te1 = ::c3b_trace::detail::rd64(h.data, 18);\n"
            "  ::c3b_trace::emit_unit0_range(h.data, te0, te1, \"learn\");\n"
            "  return r;\n"
            "}"
        )
    if "plain_ema_update" in present:
        lines.append(
            "inline ::std::tuple<> plain_ema_update("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h, ::tqbe::bits<64> g) {\n"
            "  ::c3b_trace::on_learn_enter(h.data, g.data, false);\n"
            "  return raw_plain_ema_update(mem, h, g);\n"
            "}"
        )
    if "full_otfs_subsume" in present:
        lines.append(
            "template <typename... A> inline auto full_otfs_subsume("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h, A... a) {\n"
            "  ::c3b_trace::on_otfs_subsume();\n"
            "  return raw_full_otfs_subsume(mem, h, a...);\n"
            "}"
        )
    if "full_restart" in present:
        lines.append(
            "inline ::std::tuple<> full_restart("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h) {\n"
            "  raw_full_restart(mem, h);\n"
            "  ::c3b_trace::on_restart_exit(h.data);\n"
            "  return {};\n"
            "}"
        )
    if "plain_restart_due" in present:
        lines.append(
            "inline ::tqbe::bits<64> plain_restart_due("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h) {\n"
            "  auto r = raw_plain_restart_due(mem, h);\n"
            "  if (r.data != 0ULL) ::c3b_trace::on_restart_exit(h.data, false);\n"
            "  return r;\n"
            "}"
        )
    for mfn in ("full_switch_mode", "plain_switch_mode"):
        if mfn in present:
            lines.append(
                f"inline ::std::tuple<> {mfn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h) {{\n"
                f"  uint64_t sw0 = ::c3b_trace::detail::rd64(h.data, 70);\n"
                f"  raw_{mfn}(mem, h);\n"
                f"  ::c3b_trace::on_switch_mode_exit(h.data, sw0);\n"
                f"  return {{}};\n"
                f"}}"
            )
    for rfn in ("full_reduce", "plain_reduce"):
        if rfn in present:
            lines.append(
                f"inline ::tqbe::bits<64> {rfn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h, bool force) {{\n"
                f"  uint64_t rc0 = ::c3b_trace::count_active_redundant(h.data);\n"
                f"  auto r = raw_{rfn}(mem, h, force);\n"
                f"  ::c3b_trace::on_reduce_exit(h.data, rc0);\n"
                f"  return r;\n"
                f"}}"
            )
    inproc_specs = [
        ("full_substitute", "subst", "PASS_SUBST"),
        ("full_congruence_dense", "cong", "PASS_CONG"),
        ("full_sweep_dense", "sweep", "PASS_SWEEP"),
        ("full_m4_sweep_dense", "sweep", "PASS_SWEEP"),
        ("full_transitive", "trans", "PASS_TRANS"),
        ("full_probe_run", "probe", "PASS_PROBE"),
        ("full_vivify", "viv", "PASS_VIVIFY"),
        ("full_forward_sub", "fwd", "PASS_FWD"),
        ("full_elim_bve", "bve", "PASS_ELIM"),
        ("full_factor", "bva", "PASS_FACTOR"),
        ("full_backbone", "backbone", "PASS_BACKBONE"),
        ("full_probe", None, "PASS_NONE"),
        ("full_eliminate", None, "PASS_NONE"),
    ]
    for fn, pname, pkind in inproc_specs:
        if fn in present:
            pname_c = f"\"{pname}\"" if pname else "nullptr"
            lines.append(
                f"template <typename... A> inline auto {fn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h, A... a) {{\n"
                f"  ::c3b_trace::PassScope ps(h.data, {pname_c}, "
                f"::c3b_trace::{pkind});\n"
                f"  return raw_{fn}(mem, h, a...);\n"
                f"}}"
            )
    if "full_compact" in present:
        lines.append(
            "inline ::tqbe::bits<64> full_compact("
            "::tqbe::Mem& mem, ::tqbe::bits<64> h) {\n"
            "  ::c3b_trace::PassScope ps(h.data, nullptr, "
            "::c3b_trace::PASS_COMPACT);\n"
            "  auto r = raw_full_compact(mem, h);\n"
            "  ::c3b_trace::sync_dimacs_after_compact(h.data);\n"
            "  return r;\n"
            "}"
        )
    for kfn, tick_off in (("full_kitten_solve", 270), ("full_k512_solve", 2315)):
        if kfn in present:
            lines.append(
                f"template <typename... A> inline auto {kfn}("
                f"::tqbe::Mem& mem, ::tqbe::bits<64> h, A... a) {{\n"
                f"  ::c3b_trace::KittenScope ks(h.data, {tick_off}ULL);\n"
                f"  return raw_{kfn}(mem, h, a...);\n"
                f"}}"
            )
    if "kissat_solve_bytes" in present:
        lines.append(
            "inline ::tqbe::bits<64> kissat_solve_bytes(\n"
            "    ::tqbe::Mem& mem, ::tqbe::bits<64> cp, ::tqbe::bits<64> cl,\n"
            "    ::tqbe::bits<64> wp, ::tqbe::bits<64> wc, ::tqbe::bits<64> fuel) {\n"
            "  uint64_t pad = (8ULL - (wp.data & 7ULL)) & 7ULL;\n"
            "  uint64_t hdr = wp.data + pad;\n"
            f"  ::c3b_trace::on_solve_enter(hdr, {is_full});\n"
            "  auto r = raw_kissat_solve_bytes(mem, cp, cl, wp, wc, fuel);\n"
            "  ::c3b_trace::on_solve_exit(hdr, r.data);\n"
            "  return r;\n"
            "}"
        )
    lines.append("")
    return "\n".join(lines)


def prepare_c3b_wrapped_hpp(gen_hpp, out_hpp):
    """Rewrite declarations/definitions in gen_hpp to raw_* and inject hooks."""
    with open(gen_hpp, "r", encoding="utf-8") as f:
        lines = f.readlines()
    hook_set = set(HOOKED_FNS)
    decl_re = re.compile(
        r"^(\S+\s+)(" + "|".join(re.escape(x) for x in HOOKED_FNS) + r")\(::tqbe::Mem& mem"
    )
    present = set()
    out_lines = []
    proto_end_idx = -1
    for i, line in enumerate(lines):
        m = decl_re.match(line)
        if m:
            fn = m.group(2)
            if fn in hook_set:
                present.add(fn)
                line = decl_re.sub(r"\1raw_\2(::tqbe::Mem& mem", line, count=1)
        if proto_end_idx < 0 and line.strip().endswith("{"):
            proto_end_idx = len(out_lines)
        out_lines.append(line)
    if proto_end_idx < 0:
        proto_end_idx = len(out_lines)
    wrappers = _build_wrapper_block(present) + "\n"
    final_lines = out_lines[:proto_end_idx] + [wrappers] + out_lines[proto_end_idx:]
    with open(out_hpp, "w", encoding="utf-8") as f:
        f.writelines(final_lines)
    return out_hpp


def compile_c3b_driver(gen_hpp, tmp_dir, repo_root, traced=True, ext_telem=False,
                       tag="c3b"):
    """Compile C3b runner binary (traced/telem or plain)."""
    hpp_abs = os.path.abspath(gen_hpp)
    use_hpp = hpp_abs
    if traced or ext_telem:
        use_hpp = os.path.join(tmp_dir, f"{tag}_wrapped.hpp")
        prepare_c3b_wrapped_hpp(hpp_abs, use_hpp)
    cpp_path = os.path.join(tmp_dir, f"{tag}_driver.cpp")
    bin_path = os.path.join(tmp_dir, f"{tag}_driver")
    with open(cpp_path, "w", encoding="utf-8") as f:
        f.write(C3B_RUNNER_CPP.replace("__GEN_HPP__", use_hpp))
    cmd = [
        "timeout", "180", "clang++", "-std=c++20", "-O3",
        "-Wall", "-Wextra", "-Werror", "-DTQBE_NATIVE_MEM",
        f"-I{os.path.join(repo_root, 'LeanQbe', 'T', 'Runtime')}",
        f"-I{os.path.join(repo_root, 'test', 'kissat')}",
        f"-I{os.path.join(repo_root, 'bench', 'kissat')}",
        f"-I{os.path.dirname(use_hpp)}",
        f"-I{os.path.dirname(hpp_abs)}",
    ]
    if traced:
        cmd.append("-DKISSAT_LOCKSTEP_TRACE")
    if ext_telem:
        cmd.append("-DKISSAT_EXTENDED_TELEM")
    cmd.extend([cpp_path, "-o", bin_path])
    subprocess.run(cmd, check=True)
    return bin_path


def parse_trace(path, coarse=False, ignore_noop_inproc=False):
    """Parse canonical trace lines into list of event dicts."""
    events = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s.startswith("E "):
                continue
            parts = s.split()
            if len(parts) < 3:
                continue
            kind = parts[2]
            if coarse and kind not in COARSE_KINDS:
                continue
            fields = {}
            for tok in parts[3:]:
                if "=" in tok:
                    k, v = tok.split("=", 1)
                    fields[k] = v
            if (ignore_noop_inproc and kind == "INPROC"
                    and fields.get("units") == "0"
                    and fields.get("bins") == "0"
                    and fields.get("elim") == "0"):
                continue
            events.append({"seq": int(parts[1]), "kind": kind, "fields": fields, "raw": s})
    return events


def _events_match(ek, ec, strict_glue=False):
    """Return (True, None) if canonical events match, else (False, reason)."""
    if ek["kind"] != ec["kind"]:
        return False, f"kind mismatch: kissat={ek['kind']} vs c0={ec['kind']}"
    k = ek["kind"]
    fk, fc = ek["fields"], ec["fields"]
    if k == "DEC":
        if fk.get("lvl") != fc.get("lvl") or fk.get("lit") != fc.get("lit"):
            return False, f"DEC mismatch: kissat=({fk}) vs c0=({fc})"
        if fk.get("mode") != fc.get("mode"):
            return False, f"DEC mode mismatch: kissat={fk.get('mode')} vs c0={fc.get('mode')}"
        return True, None
    if k == "CONFL":
        keys = ("c", "lvl", "sz", "hash")
        for key in keys:
            if fk.get(key) != fc.get(key):
                return False, f"CONFL {key} mismatch: kissat={fk.get(key)} vs c0={fc.get(key)}"
        return True, None
    if k == "LEARN":
        keys = ("c", "sz", "uip", "jlvl", "nlvl", "hash")
        for key in keys:
            if fk.get(key) != fc.get(key):
                return False, f"LEARN {key} mismatch: kissat={fk.get(key)} vs c0={fc.get(key)}"
        if strict_glue and fk.get("glue") != fc.get("glue"):
            return False, f"LEARN glue mismatch: kissat={fk.get('glue')} vs c0={fc.get('glue')}"
        return True, None
    if k == "RST":
        for key in ("c", "reuse", "mode"):
            if fk.get(key) != fc.get(key):
                return False, f"RST {key} mismatch: kissat={fk.get(key)} vs c0={fc.get(key)}"
        return True, None
    if k == "MODE":
        for key in ("c", "to_stable"):
            if fk.get(key) != fc.get(key):
                return False, f"MODE {key} mismatch: kissat={fk.get(key)} vs c0={fc.get(key)}"
        return True, None
    if k == "RED":
        for key in ("c", "tier1", "tier2", "del"):
            if fk.get(key) != fc.get(key):
                return False, f"RED {key} mismatch: kissat={fk.get(key)} vs c0={fc.get(key)}"
        return True, None
    if k == "INPROC":
        for key in ("pass", "units", "bins", "elim"):
            if fk.get(key) != fc.get(key):
                return False, f"INPROC {key} mismatch: kissat={fk.get(key)} vs c0={fc.get(key)}"
        return True, None
    if k == "UNIT0":
        if fk.get("lit") != fc.get("lit"):
            return False, f"UNIT0 lit mismatch: kissat={fk.get('lit')} vs c0={fc.get('lit')}"
        return True, None
    if k == "END":
        for key in ("status", "conflicts"):
            if fk.get(key) != fc.get(key):
                return False, f"END {key} mismatch: kissat={fk.get(key)} vs c0={fc.get(key)}"
        return True, None
    return fk == fc, None if fk == fc else "field mismatch"


def diagnostic_hint(ek, ec, prev_matches):
    """Produce a concrete algorithmic hint for the first divergence event."""
    if ek is None and ec is None:
        return "Exact lockstep: 0 divergences across all events."
    if ek is None or ec is None:
        side = "Kissat" if ec is None else "C0"
        ev = ek if ec is None else ec
        return (
            f"{side} emitted extra event {ev['kind']} while peer ended "
            "(check fuel/OOM/termination or extra pass)."
        )
    kk, ck = ek["kind"], ec["kind"]
    fk, fc = ek["fields"], ec["fields"]
    if kk != ck:
        if "UNIT0" in (kk, ck):
            u = ek if kk == "UNIT0" else ec
            who = "Kissat" if kk == "UNIT0" else "C0"
            return (
                f"{who} derived level-0 unit {u['fields'].get('lit')} via "
                f"src={u['fields'].get('src')} where peer did not."
            )
        if "INPROC" in (kk, ck):
            inp = ek if kk == "INPROC" else ec
            return (
                f"Inprocessing schedule/pass mismatch around "
                f"pass={inp['fields'].get('pass')} (check FullFastSched gates "
                f"or pass ordering in probe/eliminate)."
            )
        return (
            f"Control-flow divergence ({kk} vs {ck}) after "
            f"{len(prev_matches)} matching events."
        )
    if kk == "DEC":
        kl, cl = int(fk.get("lit", 0)), int(fc.get("lit", 0))
        if abs(kl) == abs(cl) and kl != cl:
            return (
                f"Same decision var {abs(kl)}, opposite phase ({kl} vs {cl}): "
                "check initialphase, target/best saving, rephase, or lucky."
            )
        mode = fk.get("mode", "0")
        if mode == "0":
            return (
                f"Focused decision var mismatch ({kl} vs {cl}): check VMTF "
                "queue order, q_search_idx reset, or unsorted MTF bumping."
            )
        return (
            f"Stable decision var mismatch ({kl} vs {cl}): check VSIDS "
            "u64 fixed-point rescaling (>>28) vs f64 1e150, or bump order."
        )
    if kk == "CONFL":
        return (
            "Conflict clause mismatch after identical decisions: check 2WL "
            "watch order, chrono lits[1] swap, or one_lit_confl."
        )
    if kk == "LEARN":
        if fk.get("hash") != fc.get("hash"):
            return (
                "Learned clause hash mismatch on identical conflict: check "
                "minimize/shrink (full_min_shrink), OTFS, or bumpreasons."
            )
        return (
            "Same learned clause, jump/backtrack level mismatch: check "
            "chronolevels (det_new_level)."
        )
    if kk == "RST":
        return (
            "Restart timing or reuse_trail mismatch: check EMA Q24 vs f64 "
            "or score/stamp comparison in full_restart."
        )
    if kk == "MODE":
        return (
            "Mode switch mismatch: check mode_confl_lim/mode_tick_lim or "
            "cache-line search_ticks accounting."
        )
    if kk == "RED":
        return (
            "Reduce DB mismatch: check glue promotion (promote.c), used "
            "aging, or reduce fraction."
        )
    if kk == "INPROC":
        p = fk.get("pass")
        return (
            f"Inprocessing effect mismatch in pass={p} "
            f"(K={fk} vs C0={fc}): check pass budget, arity/pure-3-CNF "
            "gates, or kitten var limits."
        )
    if kk == "UNIT0":
        return (
            f"Different level-0 unit derived (K={fk.get('lit')} src={fk.get('src')}"
            f" vs C0={fc.get('lit')} src={fc.get('src')})."
        )
    return (
        f"Outcome/END mismatch (K={fk} vs C0={fc}): check fuel/OOM/extend_cap."
    )


def bisect_traces(k_events, c0_events, strict_glue=False):
    """Compare two event lists and return a structured bisection dict."""
    n = min(len(k_events), len(c0_events))
    div_idx = None
    reason = None
    for i in range(n):
        ok, why = _events_match(k_events[i], c0_events[i], strict_glue)
        if not ok:
            div_idx = i
            reason = why
            break
    if div_idx is None and len(k_events) != len(c0_events):
        div_idx = n
        reason = f"trace length mismatch: kissat={len(k_events)} vs c0={len(c0_events)}"
    if div_idx is None:
        return {
            "exact_match": True,
            "matched_events": len(k_events),
            "total_kissat": len(k_events),
            "total_c0": len(c0_events),
            "last_5_matches": [e["raw"] for e in k_events[-5:]],
            "first_div_idx": None,
            "kissat_event": None,
            "c0_event": None,
            "reason": None,
            "hint": diagnostic_hint(None, None, k_events),
        }
    ek = k_events[div_idx] if div_idx < len(k_events) else None
    ec = c0_events[div_idx] if div_idx < len(c0_events) else None
    prev = k_events[max(0, div_idx - 5):div_idx]
    return {
        "exact_match": False,
        "matched_events": div_idx,
        "total_kissat": len(k_events),
        "total_c0": len(c0_events),
        "last_5_matches": [e["raw"] for e in prev],
        "first_div_idx": div_idx,
        "kissat_event": ek["raw"] if ek else "<EOF>",
        "c0_event": ec["raw"] if ec else "<EOF>",
        "reason": reason,
        "hint": diagnostic_hint(ek, ec, prev),
    }


def run_kissat_traced(kbin, cnf_path, flags, trace_path, timeout_s):
    """Run traced Kissat binary and return (returncode, trace_events)."""
    if os.path.exists(trace_path):
        os.remove(trace_path)
    env = os.environ.copy()
    env["KISSAT_LOCKSTEP_TRACE"] = trace_path
    cmd = ["timeout", str(timeout_s), kbin, "-q"] + flags + [cnf_path]
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True)
    evs = parse_trace(trace_path) if os.path.exists(trace_path) else []
    return proc.returncode, evs


def run_c3b_traced(bin_path, cnf_path, work_bytes, fuel, trace_path, timeout_s,
                   coarse=False, ignore_noop=False):
    """Run C3b binary (traced or untraced) and return (rec_dict, trace_events)."""
    if trace_path and os.path.exists(trace_path):
        os.remove(trace_path)
    env = os.environ.copy()
    if trace_path:
        env["KISSAT_LOCKSTEP_TRACE"] = trace_path
    else:
        env.pop("KISSAT_LOCKSTEP_TRACE", None)
    cmd = [
        "timeout", str(timeout_s), bin_path, cnf_path,
        f"--work-bytes={work_bytes}", f"--fuel={fuel}",
    ]
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True)
    rec = {"status": -1, "timeout": proc.returncode == 124}
    if proc.returncode == 0:
        for line in proc.stdout.splitlines():
            if line.strip().startswith("{"):
                rec = json.loads(line.strip())
                rec["timeout"] = False
                break
    evs = (parse_trace(trace_path, coarse=coarse, ignore_noop_inproc=ignore_noop)
           if trace_path and os.path.exists(trace_path) else [])
    return rec, evs


def ensure_traced_kissat(args, tmp_dir, bench_dir):
    """Ensure a KISSAT_LOCKSTEP_TRACE-capable Kissat binary is available."""
    if args.traced_kissat:
        return args.traced_kissat
    probe_tr = os.path.join(tmp_dir, "probe.trace")
    probe_cnf = os.path.join(tmp_dir, "probe.cnf")
    with open(probe_cnf, "w", encoding="utf-8") as f:
        f.write("p cnf 1 1\n1 0\n")
    if args.kissat and os.path.isfile(args.kissat):
        _, evs = run_kissat_traced(args.kissat, probe_cnf, [], probe_tr, 5)
        if evs:
            return args.kissat
    traced_out = os.path.join(tmp_dir, "kissat-traced")
    script = os.path.join(bench_dir, "build_traced_kissat.sh")
    subprocess.run(
        ["timeout", "180", "bash", script, args.kissat_src, traced_out],
        check=True,
    )
    return traced_out


def print_bisection(label, res):
    """Print readable first-divergence report."""
    print(f"=== {label} ===")
    if res["exact_match"]:
        print(f"  EXACT MATCH ({res['matched_events']} events)")
        return
    print(
        f"  FIRST DIVERGENCE at event #{res['first_div_idx']} "
        f"(matched={res['matched_events']}, "
        f"K={res['total_kissat']}, C0={res['total_c0']})"
    )
    print(f"  Reason: {res['reason']}")
    print("  Last 5 matching events:")
    for ln in res["last_5_matches"]:
        print(f"    {ln}")
    print(f"  Kissat: {res['kissat_event']}")
    print(f"  C0    : {res['c0_event']}")
    print(f"  Hint  : {res['hint']}")


def main():
    ap = argparse.ArgumentParser(
        description="Deterministic Kissat vs C0 event-trace bisector."
    )
    ap.add_argument("cnfs", nargs="*", help="CNF files to bisect")
    ap.add_argument("--kissat", default=DEFAULT_KISSAT_REF, help="Ref Kissat binary")
    ap.add_argument("--traced-kissat", default="", help="Traced Kissat binary")
    ap.add_argument("--kissat-src", default=DEFAULT_KISSAT_SRC, help="Kissat 4.0.4 src")
    ap.add_argument("--gen-hpp", default="", help="C3b *_gen.hpp path")
    ap.add_argument("--c3b-bin", default="", help="Prebuilt traced C3b binary")
    ap.add_argument("--plain", action="store_true", help="Run 11-rung --plain ladder")
    ap.add_argument("--coarse", action="store_true", help="Diff coarse timeline only")
    ap.add_argument("--ignore-noop-inproc", action="store_true",
                    help="Skip 0-effect INPROC events when comparing")
    ap.add_argument("--strict-glue", action="store_true", help="Check LEARN glue match")
    ap.add_argument("--verify-zero-perturbation", action="store_true",
                    help="Verify traced C3b matches untraced C3b identically")
    ap.add_argument("--work-bytes", type=int, default=67108864, help="C0 work bytes")
    ap.add_argument("--fuel", type=int, default=2000000000, help="C0 fuel")
    ap.add_argument("--timeout", type=int, default=15, help="Per-run timeout (s)")
    ap.add_argument("--wrap-hpp", nargs=2, metavar=("IN", "OUT"),
                    help="Rewrite IN *_gen.hpp to wrapped OUT and exit")
    ap.add_argument("--trace-k", default="", help="Offline Kissat trace file")
    ap.add_argument("--trace-c0", default="", help="Offline C0 trace file")
    ap.add_argument("--json-out", default="", help="Write JSON report")
    args = ap.parse_args()

    if args.wrap_hpp:
        prepare_c3b_wrapped_hpp(args.wrap_hpp[0], args.wrap_hpp[1])
        return

    if args.trace_k and args.trace_c0:
        ke = parse_trace(args.trace_k, coarse=args.coarse,
                         ignore_noop_inproc=args.ignore_noop_inproc)
        ce = parse_trace(args.trace_c0, coarse=args.coarse,
                         ignore_noop_inproc=args.ignore_noop_inproc)
        res = bisect_traces(ke, ce, strict_glue=args.strict_glue)
        print_bisection("offline", res)
        return

    if not args.cnfs:
        ap.error("pass at least one CNF path (or --trace-k/--trace-c0)")
    if not args.gen_hpp and not args.c3b_bin:
        ap.error("pass --gen-hpp or --c3b-bin")

    bench_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.abspath(os.path.join(bench_dir, "..", ".."))
    reports = []

    with tempfile.TemporaryDirectory(prefix="kissat-lockstep-") as tmp_dir:
        kbin = ensure_traced_kissat(args, tmp_dir, bench_dir)
        c3b_tr = (
            args.c3b_bin if args.c3b_bin
            else compile_c3b_driver(args.gen_hpp, tmp_dir, repo_root,
                                    traced=True, tag="tr")
        )
        c3b_un = (
            compile_c3b_driver(args.gen_hpp, tmp_dir, repo_root,
                               traced=False, tag="un")
            if (args.verify_zero_perturbation and args.gen_hpp) else None
        )

        for idx, cnf in enumerate(args.cnfs):
            cname = os.path.basename(cnf)
            c0_tr_path = os.path.join(tmp_dir, f"c0_{idx}.trace")
            c0_rec, c0_evs = run_c3b_traced(
                c3b_tr, cnf, args.work_bytes, args.fuel, c0_tr_path, args.timeout,
                coarse=args.coarse, ignore_noop=args.ignore_noop_inproc,
            )
            if c3b_un:
                un_rec, _ = run_c3b_traced(
                    c3b_un, cnf, args.work_bytes, args.fuel, None, args.timeout
                )
                for k in ("status", "conflicts", "learned_lits",
                          "min_removed", "search_ticks"):
                    if c0_rec.get(k) != un_rec.get(k):
                        raise RuntimeError(
                            f"Perturbation on {cname} {k}: "
                            f"traced={c0_rec.get(k)} != untraced={un_rec.get(k)}"
                        )
                print(f"[zero-perturbation OK] {cname}: st={c0_rec['status']} "
                      f"confl={c0_rec['conflicts']} ticks={c0_rec['search_ticks']}")

            if args.plain:
                ladder_rows = []
                cur_flags = list(PLAIN_BASE_FLAGS)
                for rname, add_f in PLAIN_LADDER:
                    for flg in add_f:
                        key = flg.split("=")[0]
                        cur_flags = [x for x in cur_flags
                                     if x.split("=")[0] != key]
                        cur_flags.append(flg)
                    k_tr = os.path.join(tmp_dir, f"k_{idx}_{rname}.trace")
                    krc, k_evs_all = run_kissat_traced(
                        kbin, cnf, cur_flags, k_tr, args.timeout
                    )
                    k_evs = parse_trace(
                        k_tr, coarse=args.coarse,
                        ignore_noop_inproc=args.ignore_noop_inproc,
                    ) if os.path.exists(k_tr) else []
                    res = bisect_traces(k_evs, c0_evs, args.strict_glue)
                    res["rung"] = rname
                    res["kissat_rc"] = krc
                    ladder_rows.append(res)
                    print_bisection(f"{cname} [{rname}]", res)
                reports.append({
                    "cnf": cnf, "c0": c0_rec, "mode": "plain-ladder",
                    "rungs": ladder_rows,
                })
            else:
                k_tr = os.path.join(tmp_dir, f"k_{idx}.trace")
                krc, _ = run_kissat_traced(
                    kbin, cnf, ["--seed=0", "--phase=1"], k_tr, args.timeout
                )
                k_evs = parse_trace(
                    k_tr, coarse=args.coarse,
                    ignore_noop_inproc=args.ignore_noop_inproc,
                ) if os.path.exists(k_tr) else []
                res = bisect_traces(k_evs, c0_evs, args.strict_glue)
                res["kissat_rc"] = krc
                print_bisection(f"{cname} [{'coarse' if args.coarse else 'full'}]", res)
                reports.append({
                    "cnf": cnf, "c0": c0_rec,
                    "mode": "coarse" if args.coarse else "full",
                    "bisection": res,
                })

    if args.json_out:
        out_dir = os.path.dirname(os.path.abspath(args.json_out))
        if out_dir:
            os.makedirs(out_dir, exist_ok=True)
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump({"reports": reports}, f, indent=2)


if __name__ == "__main__":
    main()
