#!/usr/bin/env bash
# Stage 4 (D-Full) 300+ CNF Inprocessing Stress & Differential Verification Suite.
#
# Tests selected LeanQbe Kissat module(s) (`--module CorePlus | Plain | Full`, default:
# `CorePlus` + `Plain`, plus `Full` automatically when `LeanQbe/T/Examples/Kissat/Full.lean`
# exists) across:
#   1. PrintCpp + clang++ -std=c++20 -O2 -fsanitize=undefined,address -DTQBE_CATCH_UB
#      (stratified representative CNFs across all 9 families + unaligned work_ptr & edge checks)
#   2. Native x64 (`x64Target`) with mmap guard pages + DIMACS model verifier (300+ CNFs)
#   3. Native Arm64 (`armTarget` via `qemu-aarch64`) with mmap guard pages + verifier (300+ CNFs)
#   4. Reference Kissat 4.0.4 (`--plain` & default), built in `/tmp` if not already present, or
#      skipped cleanly with a diagnostic if unavailable or `--no-kissat` is passed.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

MODULES=()
NO_KISSAT=0
NO_CPP=0
WITH_KTEST=0
WORK_BYTES="${WORK_BYTES:-8388608}"
FUEL="${FUEL:-400000}"
CPP_FUEL="${CPP_FUEL:-10000}"
CPP_CASES="${CPP_CASES:-36}"

usage() {
  cat <<'EOF'
usage: bench/kissat/run_full.sh [options]
  --module <Plain|KissatFidelity|KissatM8Opt|FullM7Fidelity|CorePlus|Full|All>
                                       Module(s) to test (repeatable or comma-separated;
                                       aliases: fid, fidelity, m8opt, opt, m8, m7fid)
  --no-kissat                          Skip reference Kissat 4.0.4 build & comparison
  --no-cpp                             Skip PrintCpp C++20 ASan/UBSan check
  --with-ktest                         Also include stock kissat test/cnf/*.cnf if available
  --work-bytes <N>                     Solver workspace bytes (default: 8388608)
  --fuel <N>                           Native x64/Arm64 fuel budget (default: 400000)
  --cpp-fuel <N>                       PrintCpp ASan/UBSan fuel budget (default: 10000)
  --cpp-cases <N>                      PrintCpp representative CNF count (default: 36)
  -h, --help                           Show this help
EOF
}

norm_mod() {
  case "${1,,}" in
    coreplus) echo "CorePlus" ;;
    plain|kissatplain) echo "Plain" ;;
    full) echo "Full" ;;
    kissatfidelity|fullfidelity|fidelity|fid) echo "KissatFidelity" ;;
    kissatm8opt|fullm8opt|m8opt|opt|fullm8|m8) echo "KissatM8Opt" ;;
    fullm7fidelity|m7fidelity|m7fid) echo "FullM7Fidelity" ;;
    all) echo "All" ;;
    *) echo "ERROR: unknown module '$1' (expected Plain|KissatFidelity|KissatM8Opt|FullM7Fidelity|CorePlus|Full|All)" >&2; exit 2 ;;
  esac
}

append_all_modules() {
  [ -f "$ROOT/LeanQbe/T/Examples/Kissat/Plain.lean" ] && MODULES+=(Plain)
  if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean" ]; then
    MODULES+=(KissatFidelity)
  elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean" ]; then
    MODULES+=(FullM7Fidelity)
  fi
  [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8OptAssembly.lean" ] && MODULES+=(KissatM8Opt)
}

while [ $# -gt 0 ]; do
  case "$1" in
    --module)
      [ $# -ge 2 ] || { echo "ERROR: --module requires an argument" >&2; exit 2; }
      IFS=',' read -r -a parts <<< "$2"
      for p in "${parts[@]}"; do
        nm="$(norm_mod "$p")"
        if [ "$nm" = "All" ]; then
          append_all_modules
        else
          MODULES+=("$nm")
        fi
      done
      shift 2
      ;;
    --module=*)
      IFS=',' read -r -a parts <<< "${1#--module=}"
      for p in "${parts[@]}"; do
        nm="$(norm_mod "$p")"
        if [ "$nm" = "All" ]; then
          append_all_modules
        else
          MODULES+=("$nm")
        fi
      done
      shift
      ;;
    --no-kissat) NO_KISSAT=1; shift ;;
    --no-cpp) NO_CPP=1; shift ;;
    --with-ktest) WITH_KTEST=1; shift ;;
    --work-bytes) WORK_BYTES="$2"; shift 2 ;;
    --fuel) FUEL="$2"; shift 2 ;;
    --cpp-fuel) CPP_FUEL="$2"; shift 2 ;;
    --cpp-cases) CPP_CASES="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "ERROR: unknown option '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

FULL_LEAN="$ROOT/LeanQbe/T/Examples/Kissat/Full.lean"
has_full_module() {
  [ -f "$FULL_LEAN" ] && grep -q 'LeanQbe\.T\.Examples\.Kissat\.Full' "$ROOT/LeanQbe.lean"
}

if [ ${#MODULES[@]} -eq 0 ]; then
  if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean" ]; then
    MODULES=(Plain KissatFidelity)
  elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean" ]; then
    MODULES=(Plain FullM7Fidelity)
  else
    MODULES=(CorePlus Plain)
    if has_full_module; then
      MODULES+=(Full)
    fi
  fi
fi

# Deduplicate preserving order
UNIQ_MODULES=()
for m in "${MODULES[@]}"; do
  seen=0
  for u in "${UNIQ_MODULES[@]:-}"; do
    [ "$u" = "$m" ] && seen=1 && break
  done
  [ $seen -eq 0 ] && UNIQ_MODULES+=("$m")
done
MODULES=("${UNIQ_MODULES[@]}")

for m in "${MODULES[@]}"; do
  if [ "$m" = "Full" ] && ! has_full_module; then
    echo "ERROR: --module Full requested, but LeanQbe.T.Examples.Kissat.Full is not landed yet." >&2
    exit 2
  elif [ "$m" = "KissatFidelity" ] && [ ! -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean" ]; then
    echo "ERROR: --module KissatFidelity requested, but FullFidelityAssembly.lean is not landed yet." >&2
    exit 2
  elif [ "$m" = "KissatM8Opt" ] && [ ! -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8OptAssembly.lean" ]; then
    echo "ERROR: --module KissatM8Opt requested, but FullM8OptAssembly.lean is not landed yet." >&2
    exit 2
  elif [ "$m" = "FullM7Fidelity" ] && [ ! -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean" ]; then
    echo "ERROR: --module FullM7Fidelity requested, but FullM7FidelityAssembly.lean is not landed yet." >&2
    exit 2
  fi
done

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-kissat-full.XXXXXX")}"
cleanup() {
  if [ -z "$OUT_USER" ] && [ -z "${KEEP_OUT:-}" ]; then
    rm -rf "$OUT"
  fi
}
trap cleanup EXIT
mkdir -p "$OUT/cnfs/gen" "$OUT/cnfs/kissat_test"
echo "outputs in $OUT (modules: ${MODULES[*]})"

echo "== 1. Generate 300+ inprocessing & search-stress DIMACS CNFs =="
timeout 60 python3 -B bench/kissat/gen_inproc_cnfs.py "$OUT/cnfs/gen" --summary

KISSAT_SRC="${KISSAT_SRC:-}"
if [ -z "$KISSAT_SRC" ] && [ -d "$ROOT/scratch/kissat/src" ]; then
  KISSAT_SRC="$ROOT/scratch/kissat"
fi

if [ "$WITH_KTEST" -eq 1 ] && [ -n "$KISSAT_SRC" ] && [ -d "$KISSAT_SRC/test/cnf" ]; then
  for f in "$KISSAT_SRC/test/cnf"/*.cnf; do
    [ -f "$f" ] && [ ! -L "$f" ] || continue
    cp "$f" "$OUT/cnfs/kissat_test/"
  done
fi

echo "== 2. Resolve or build reference Kissat 4.0.4 in /tmp =="
check_kissat_bin() {
  local bin="$1"
  [ -x "$bin" ] || return 1
  local rc=0
  printf 'p cnf 0 0\n' | timeout 10 "$bin" --plain -q >/dev/null 2>&1 || rc=$?
  [ "$rc" -eq 10 ]
}

if [ "$NO_KISSAT" -eq 1 ]; then
  KISSAT_BIN=""
  echo "NOTE: --no-kissat passed; skipping reference Kissat 4.0.4 comparison."
else
  KISSAT_BIN="${KISSAT_BIN:-}"
  if [ -n "$KISSAT_BIN" ] && ! check_kissat_bin "$KISSAT_BIN"; then
    echo "NOTE: KISSAT_BIN=$KISSAT_BIN does not support --plain; ignoring." >&2
    KISSAT_BIN=""
  fi
  if [ -z "$KISSAT_BIN" ]; then
    for cand in /tmp/kissat-4.0.4 /tmp/kissat-ref /tmp/kissat; do
      if check_kissat_bin "$cand"; then
        KISSAT_BIN="$cand"
        break
      fi
    done
  fi
  if [ -z "$KISSAT_BIN" ] && [ -n "$KISSAT_SRC" ]; then
    SRC_DIR=""
    ROOT_DIR=""
    if [ -f "$KISSAT_SRC/configure" ] && [ -d "$KISSAT_SRC/src" ]; then
      ROOT_DIR="$KISSAT_SRC"
    elif [ -f "$KISSAT_SRC/kissat.h" ] && [ -f "$KISSAT_SRC/../configure" ]; then
      ROOT_DIR="$(cd "$KISSAT_SRC/.." && pwd)"
    elif [ -d "$KISSAT_SRC" ] && [ -f "$KISSAT_SRC/main.c" ]; then
      SRC_DIR="$KISSAT_SRC"
    fi
    if [ -n "$ROOT_DIR" ]; then
      cp -a "$ROOT_DIR" "$OUT/kissat-src"
      (
        cd "$OUT/kissat-src"
        rm -rf build makefile
        timeout 60 ./configure >/dev/null
        timeout 180 make -j"$(nproc)" >/dev/null
      )
      cp "$OUT/kissat-src/build/kissat" "$OUT/kissat-ref"
      KISSAT_BIN="$OUT/kissat-ref"
    elif [ -n "$SRC_DIR" ]; then
      mkdir -p "$OUT/kissat-build"
      cat > "$OUT/kissat-build/build.h" <<'HDR'
#define VERSION "4.0.4"
#define COMPILER "gcc"
#define ID "leanqbe-ref"
#define BUILD "tmp"
#define DIR "/tmp"
HDR
      timeout 180 gcc -O2 -W -Wall -DCOMPACT -DNDEBUG -I"$OUT/kissat-build" -I"$SRC_DIR" \
        "$SRC_DIR"/*.c -lm -o "$OUT/kissat-ref"
      KISSAT_BIN="$OUT/kissat-ref"
    fi
  fi
  if [ -z "$KISSAT_BIN" ]; then
    SYS_KISSAT="$(command -v kissat || true)"
    if [ -n "$SYS_KISSAT" ] && check_kissat_bin "$SYS_KISSAT"; then
      KISSAT_BIN="$SYS_KISSAT"
    fi
  fi
  if [ -n "$KISSAT_BIN" ] && check_kissat_bin "$KISSAT_BIN"; then
    echo "Using reference Kissat 4.0.4: $KISSAT_BIN"
  else
    KISSAT_BIN=""
    echo "NOTE: reference Kissat 4.0.4 not available or lacks --plain (set KISSAT_BIN or KISSAT_SRC); skipping reference comparison."
  fi
fi

mod_lean() {
  case "$1" in
    CorePlus|Plain|Full) echo "LeanQbe.T.Examples.Kissat.$1" ;;
    KissatFidelity)
      local deps=("LeanQbe.T.Examples.Kissat.FullFidelityAssembly")
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityInl.lean" ]; then
        deps+=("LeanQbe.T.Examples.Kissat.FullFidelityInl")
      elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityInlPolicy.lean" ]; then
        deps+=("LeanQbe.T.MainInline" "LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy")
      fi
      echo "${deps[*]}" ;;
    KissatM8Opt)
      local deps=("LeanQbe.T.Examples.Kissat.FullM8OptAssembly")
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8OptInl.lean" ]; then
        deps+=("LeanQbe.T.Examples.Kissat.FullM8OptInl")
      elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8InlPolicy.lean" ]; then
        deps+=("LeanQbe.T.MainInline" "LeanQbe.T.Examples.Kissat.FullM8InlPolicy")
      fi
      echo "${deps[*]}" ;;
    FullM7Fidelity)
      local deps=("LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly")
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityInl.lean" ]; then
        deps+=("LeanQbe.T.Examples.Kissat.FullM7FidelityInl")
      elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean" ]; then
        deps+=("LeanQbe.T.MainInline" "LeanQbe.T.Examples.Kissat.FullM7InlPolicy")
      fi
      echo "${deps[*]}" ;;
  esac
}

mod_expr() {
  case "$1" in
    CorePlus) echo "LeanQbe.T.Examples.Kissat.CorePlus.coreplusModule" ;;
    Plain) echo "LeanQbe.T.Examples.Kissat.Plain.plainModule" ;;
    Full) echo "LeanQbe.T.Examples.Kissat.Full.fullModule" ;;
    KissatFidelity) echo "LeanQbe.T.Examples.Kissat.FullFidelityAssembly.fidModule" ;;
    KissatM8Opt) echo "LeanQbe.T.Examples.Kissat.FullM8OptAssembly.m8OptModule" ;;
    FullM7Fidelity) echo "LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityModule" ;;
  esac
}

mod_fns_expr() {
  case "$1" in
    CorePlus) echo "(LeanQbe.T.Examples.Kissat.CorePlus.coreplusModule).fns" ;;
    Plain) echo "(LeanQbe.T.Examples.Kissat.Plain.plainModule).fns" ;;
    Full) echo "(LeanQbe.T.Examples.Kissat.Full.fullModule).fns" ;;
    KissatFidelity)
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityInl.lean" ]; then
        echo "LeanQbe.T.Examples.Kissat.FullFidelityInl.fidInlFns"
      elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityInlPolicy.lean" ]; then
        echo "((LeanQbe.T.Examples.Kissat.FullFidelityAssembly.fidModule).optInlinePolicy LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy.fidInlPolicy).fns"
      else
        echo "(LeanQbe.T.Examples.Kissat.FullFidelityAssembly.fidModule).fns"
      fi ;;
    KissatM8Opt)
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8OptInl.lean" ]; then
        echo "LeanQbe.T.Examples.Kissat.FullM8OptInl.m8OptInlFns"
      elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8InlPolicy.lean" ]; then
        echo "((LeanQbe.T.Examples.Kissat.FullM8OptAssembly.m8OptModule).optInlinePolicy LeanQbe.T.Examples.Kissat.FullM8InlPolicy.m8InlPolicy).fns"
      else
        echo "(LeanQbe.T.Examples.Kissat.FullM8OptAssembly.m8OptModule).fns"
      fi ;;
    FullM7Fidelity)
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityInl.lean" ]; then
        echo "LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns"
      elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean" ]; then
        echo "((LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityModule).optInlinePolicy LeanQbe.T.Examples.Kissat.FullM7InlPolicy.m7InlPolicy).fns"
      else
        echo "(LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityModule).fns"
      fi ;;
  esac
}

mod_tel_flag() {
  case "$1" in
    CorePlus|KissatFidelity|KissatM8Opt|FullM7Fidelity) echo "--telemetry" ;;
    Plain) echo "--plain-telemetry" ;;
    Full) echo "" ;;
  esac
}

mod_edge_work() {
  case "$1" in
    Plain|CorePlus|Full) echo "4096" ;;
    *) echo "6144" ;;
  esac
}

echo "== 3. Build requested LeanQbe Kissat module(s) & codegen drivers =="
LAKE_TARGETS=(
  LeanQbe.T.PrintCpp LeanQbe.T.Driver
  LeanQbe.T.Amd64.Targ LeanQbe.T.Arm64.Targ
  LeanQbe.T.Amd64.PrintATTAlign Kraken.AArch64.Print
)
for m in "${MODULES[@]}"; do
  # shellcheck disable=SC2046
  LAKE_TARGETS+=($(mod_lean "$m"))
done
timeout 600 lake build --wfail "${LAKE_TARGETS[@]}"

KTEST_INC="$ROOT/test/kissat"
RT_INC="$ROOT/LeanQbe/T/Runtime"
COMMON_C="-O2 -Wall -Wextra -Werror -I$KTEST_INC"
COMMON_CXX="-std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=undefined,address -fno-sanitize-recover=all -DTQBE_CATCH_UB -I$RT_INC -I$KTEST_INC -I$OUT"

for m in "${MODULES[@]}"; do
  expr="$(mod_expr "$m")"
  fns_expr="$(mod_fns_expr "$m")"
  edge_work="$(mod_edge_work "$m")"
  imports=""
  for lm in $(mod_lean "$m"); do
    imports+="import $lm"$'\n'
  done
  echo "== 4[$m]. Emit PrintCpp header + native x64 + Arm64 assembly =="
  cat > "$OUT/emit_${m}_cpp_x64.lean" <<LEAN
${imports}import LeanQbe.T.PrintCpp
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let [cppPath, x64Path] := args | throw (IO.userError "usage: <cpp> <x64>")
  let m := ${expr}
  let cpp ← match ppTModule m with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  IO.FS.writeFile cppPath cpp
  let fns := ${fns_expr}
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  IO.FS.writeFile x64Path (Driver.emitAsm (fun c => toATTAligned c ++ "\n") fns dirs)
LEAN

  cat > "$OUT/emit_${m}_arm64.lean" <<LEAN
${imports}import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let [armPath] := args | throw (IO.userError "usage: <arm64>")
  let fns := ${fns_expr}
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    ".p2align 2\n" ++ String.intercalate "\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile armPath (Driver.emitAsm (fun c => pp c ++ "\n") fns dirs)
LEAN

  timeout 900 lake env lean --run "$OUT/emit_${m}_cpp_x64.lean" \
    "$OUT/${m}_gen.hpp" "$OUT/${m}_x64.s"
  timeout 900 lake env lean --run "$OUT/emit_${m}_arm64.lean" "$OUT/${m}_arm64.s"

  timeout 60 gcc $COMMON_C -no-pie bench/kissat/bench_main.c "$OUT/${m}_x64.s" \
    -o "$OUT/bench_${m}_x64"
  timeout 60 aarch64-linux-gnu-gcc $COMMON_C bench/kissat/bench_main.c "$OUT/${m}_arm64.s" \
    -o "$OUT/bench_${m}_arm64" 2>"$OUT/${m}_arm64_cc.log" || {
      cat "$OUT/${m}_arm64_cc.log" >&2; exit 1
    }
  grep -v -e 'SFrame' "$OUT/${m}_arm64_cc.log" >&2 || true

  if [ "$NO_CPP" -eq 0 ]; then
    cat > "$OUT/cpp_${m}_driver.cpp" <<CPP
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include "${m}_gen.hpp"
#include "kissat_verify.h"

static uint64_t run_bytes(
    const uint8_t *cnf, size_t cnf_len, size_t work_len, uint64_t fuel,
    uint64_t align_off, const char *label) {
  ::tqbe::Mem mem;
  const uint64_t cnf_ptr = 0x10000ULL;
  const uint64_t work_ptr = 0x100000ULL + align_off;
  if (cnf_len > 0) {
    mem.alloc(cnf_ptr, cnf_len, 0x5A);
    for (size_t k = 0; k < cnf_len; ++k) {
      ::tqbe::store<::tqbe::bits<8>>(mem, ::tqbe::bits<64>(cnf_ptr + k),
        ::tqbe::bits<8>(cnf[k]));
    }
  }
  if (work_len > 0) mem.alloc(work_ptr, work_len, 0xA5);
  uint64_t got = kissat_solve_bytes(mem, ::tqbe::bits<64>(cnf_ptr),
    ::tqbe::bits<64>(cnf_len), ::tqbe::bits<64>(work_ptr),
    ::tqbe::bits<64>(work_len), ::tqbe::bits<64>(fuel)).word(0);
  if (got != 0ULL && got != 10ULL && got != 20ULL) {
    std::fprintf(stderr, "FAIL [cpp %s] invalid status=%llu\n", label, (unsigned long long)got);
    std::exit(1);
  }
  for (size_t k = 0; k < cnf_len; ++k) {
    uint8_t b = (uint8_t)::tqbe::load<::tqbe::bits<8>>(
      mem, ::tqbe::bits<64>(cnf_ptr + k)).word(0);
    if (b != cnf[k]) {
      std::fprintf(stderr, "FAIL [cpp %s] mutated cnf[%zu]\n", label, k);
      std::exit(1);
    }
  }
  if (got == 10ULL) {
    uint64_t pad = (work_ptr & 7ULL) ? (8ULL - (work_ptr & 7ULL)) : 0ULL;
    uint64_t hdr = work_ptr + pad;
    if (work_len >= pad + 8ULL &&
        ::tqbe::load<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(hdr)).word(0) ==
          0x4D36484452455831ULL) {
      /* M6 extended work header (FullM6Hdr, "M6HDREX1"): FullHdr starts at word 288, i.e.
         288 * 8 = 2304 bytes in (same skip as bench_main.c and kissat_cli.c). */
      if (work_len < pad + 2304ULL) {
        std::fprintf(stderr, "FAIL [cpp %s] truncated M6 header\n", label);
        std::exit(1);
      }
      pad += 2304ULL;
      hdr += 2304ULL;
    }
    if (work_len < pad + 72ULL) {
      std::fprintf(stderr, "FAIL [cpp %s] truncated SAT header\n", label);
      std::exit(1);
    }
    uint64_t mv = ::tqbe::load<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(hdr)).word(0);
    uint64_t vp = ::tqbe::load<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(hdr + 64)).word(0);
    uint64_t ws_hi = work_ptr + work_len;
    if (vp < hdr + 72ULL || vp > ws_hi || mv > (ws_hi - vp) / 2ULL) {
      std::fprintf(stderr, "FAIL [cpp %s] invalid SAT model pointer\n", label);
      std::exit(1);
    }
    std::vector<int8_t> vals(mv * 2ULL, 0);
    for (uint64_t j = 0; j < mv * 2ULL; ++j) {
      vals[j] = (int8_t)::tqbe::load<::tqbe::bits<8>>(mem, ::tqbe::bits<64>(vp + j)).word(0);
    }
    if (!kissat_verify_dimacs_model((const char *)cnf, cnf_len, vals.data(), mv)) {
      std::fprintf(stderr, "FAIL [cpp %s] invalid SAT model\n", label);
      std::exit(1);
    }
  }
  return got;
}

static void check_edge(const char *name, const char *cnf, size_t work_len,
                       uint64_t fuel, uint64_t exp, uint64_t off) {
  uint64_t got = run_bytes((const uint8_t *)cnf, std::strlen(cnf), work_len, fuel, off, name);
  if (got != exp) {
    std::fprintf(stderr, "FAIL [cpp edge %s off=%llu work=%zu] got=%llu exp=%llu\n",
      name, (unsigned long long)off, work_len, (unsigned long long)got,
      (unsigned long long)exp);
    std::exit(1);
  }
}

int main(int argc, char **argv) {
  const size_t ew = ${edge_work}ULL;
  check_edge("empty_0", "p cnf 0 0\n", ew, 100, 10, 0);
  check_edge("empty_0_unaligned", "p cnf 0 0\n", ew, 100, 10, 3);
  check_edge("empty_clause", "p cnf 1 1\n0\n", ew, 100, 20, 3);
  check_edge("fuel_0", "p cnf 1 2\n1 0\n-1 0\n", ew, 0, 0, 0);
  check_edge("tiny_work_0", "p cnf 1 2\n1 0\n-1 0\n", 0, 100, 0, 0);
  check_edge("tiny_work_127", "p cnf 1 2\n1 0\n-1 0\n", 127, 100, 0, 0);
  check_edge("bad_oob_var", "p cnf 1 1\n2 0\n", ew, 100, 0, 0);
  check_edge("bad_empty", "", ew, 100, 0, 0);

  if (argc < 4) return 0;
  size_t work_len = (size_t)std::strtoull(argv[1], nullptr, 10);
  uint64_t fuel = (uint64_t)std::strtoull(argv[2], nullptr, 10);
  for (int i = 3; i < argc; ++i) {
    const char *path = argv[i];
    std::FILE *f = std::fopen(path, "rb");
    if (!f) { std::fprintf(stderr, "cannot open %s\n", path); return 2; }
    std::fseek(f, 0, SEEK_END);
    long sz = std::ftell(f);
    std::rewind(f);
    std::vector<uint8_t> buf((size_t)(sz > 0 ? sz : 1), 0);
    if (sz > 0 && std::fread(buf.data(), 1, (size_t)sz, f) != (size_t)sz) return 2;
    std::fclose(f);
    uint64_t off = ((i - 3) % 4 == 0) ? 3ULL : 0ULL;
    uint64_t st = run_bytes(buf.data(), (size_t)sz, work_len, fuel, off, path);
    std::printf("%s\t%llu\n", path, (unsigned long long)st);
  }
  return 0;
}
CPP
    timeout 300 clang++ $COMMON_CXX "$OUT/cpp_${m}_driver.cpp" -o "$OUT/cpp_${m}_asan"
  fi
done

echo "== 5. Run differential verification across C++20 ASan/UBSan, x64, Arm64 QEMU, and Kissat =="
MOD_SPECS=()
for m in "${MODULES[@]}"; do
  tel="$(mod_tel_flag "$m")"
  cpp_bin=""
  [ "$NO_CPP" -eq 0 ] && cpp_bin="$OUT/cpp_${m}_asan"
  MOD_SPECS+=("${m}|${tel}|$OUT/bench_${m}_x64|$OUT/bench_${m}_arm64|${cpp_bin}")
done

timeout 300 python3 -B - "$OUT" "$WORK_BYTES" "$FUEL" "$CPP_FUEL" "$CPP_CASES" \
  "$KISSAT_BIN" "${MOD_SPECS[@]}" <<'PY'
import glob
import os
import statistics
import subprocess
import sys
import time

out, work_bytes, fuel, cpp_fuel, cpp_cases_n, kissat_bin = sys.argv[1:7]
cpp_cases_n = int(cpp_cases_n)
mod_specs = [s.split("|") for s in sys.argv[7:]]

gen_cnfs = sorted(glob.glob(os.path.join(out, "cnfs/gen/*.cnf")))
ktest_cnfs = sorted(glob.glob(os.path.join(out, "cnfs/kissat_test/*.cnf")))
assert len(gen_cnfs) >= 300, f"Expected >= 300 generated CNFs, found {len(gen_cnfs)}"

all_cnfs = [(p, "gen/" + os.path.basename(p)) for p in gen_cnfs] + [
    (p, "ktest/" + os.path.basename(p)) for p in ktest_cnfs
]
paths = [p for p, _ in all_cnfs]

FAMILIES = [
    ("php", lambda l: l.startswith("gen/php_")),
    ("tseitin", lambda l: l.startswith("gen/tseitin_")),
    ("xor", lambda l: l.startswith("gen/xor_")),
    ("miter", lambda l: l.startswith("gen/miter_")),
    ("big", lambda l: l.startswith("gen/big_")),
    ("subsume_viv", lambda l: l.startswith(("gen/subsume_", "gen/viv_"))),
    ("bva", lambda l: l.startswith("gen/bva_")),
    ("search_stress", lambda l: l.startswith("gen/search_")),
    ("rand3sat", lambda l: l.startswith("gen/r3sat_")),
    ("kissat_test", lambda l: l.startswith("ktest/")),
]

# Select stratified small/medium CNFs across all 9 generated families for PrintCpp ASan/UBSan
cpp_subset = []
per_fam = max(1, (cpp_cases_n + 8) // 9)
for fam, pred in FAMILIES:
    if fam == "kissat_test":
        continue
    cands = [p for p, l in all_cnfs if pred(l)]
    cands.sort(key=lambda p: (os.path.getsize(p), p))
    # Pick both sat and unsat smallest where available
    picked = []
    for tag in ("_unsat_", "_sat_"):
        tagged = [p for p in cands if tag in os.path.basename(p)]
        if tagged:
            picked.extend(tagged[: max(1, per_fam // 2)])
    for p in cands:
        if len(picked) >= per_fam:
            break
        if p not in picked:
            picked.append(p)
    cpp_subset.extend(picked[:per_fam])
cpp_subset = cpp_subset[:cpp_cases_n]

def parse_bench(stdout_text, plain_tel):
    res = {}
    for line in stdout_text.strip().splitlines():
        parts = line.split("\t")
        if plain_tel:
            if len(parts) != 10:
                raise RuntimeError(f"bad plain bench line: {line!r}")
            p, st, ms, conf, lrn, mrem, rst, red, rph, sw = parts
            res[p] = (int(st), float(ms), int(conf), int(lrn), int(mrem),
                      int(rst), int(red), int(rph), int(sw))
        else:
            if len(parts) != 6:
                raise RuntimeError(f"bad bench line: {line!r}")
            p, st, ms, conf, lrn, mrem = parts
            res[p] = (int(st), float(ms), int(conf), int(lrn), int(mrem), 0, 0, 0, 0)
    return res

def run_native(cmd_prefix, cnf_paths, tel_flag):
    args = list(cmd_prefix) + ([tel_flag] if tel_flag else []) + [work_bytes, fuel] + cnf_paths
    proc = subprocess.run(args, capture_output=True, text=True, timeout=180)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise SystemExit(f"solver failed ({proc.returncode}): {' '.join(cmd_prefix)}")
    return parse_bench(proc.stdout, tel_flag == "--plain-telemetry")

def run_cpp(cpp_bin, cnf_paths):
    args = [cpp_bin, str(min(int(work_bytes), 2097152)), cpp_fuel] + cnf_paths
    proc = subprocess.run(args, capture_output=True, text=True, timeout=180)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise SystemExit(f"PrintCpp ASan/UBSan failed ({proc.returncode}): {cpp_bin}")
    res = {}
    for line in proc.stdout.strip().splitlines():
        p, st = line.split("\t")
        res[p] = int(st)
    return res

def run_kissat_mode(flags, cnf_paths):
    out_map = {}
    for p in cnf_paths:
        t0 = time.monotonic()
        r = subprocess.run(["timeout", "3", kissat_bin] + flags + ["-q", p], capture_output=True)
        ms = (time.monotonic() - t0) * 1000.0
        st = r.returncode if r.returncode in (10, 20) else 0
        out_map[p] = (st, ms, 0, 0, 0, 0, 0, 0, 0)
    return out_map

w_mib = int(work_bytes) // 1048576
print(
    f"Inprocessing corpus: {len(gen_cnfs)} generated + {len(ktest_cnfs)} stock-test"
    f" = {len(paths)} CNFs (work={w_mib}MiB, fuel={fuel}, cpp_subset={len(cpp_subset)})"
)

solvers = []
mod_x64 = {}
mod_arm = {}
mod_cpp = {}
for m, tel_flag, x64_bin, arm_bin, cpp_bin in mod_specs:
    xr = run_native([x64_bin], paths, tel_flag)
    ar = run_native(["qemu-aarch64", "-L", "/usr/aarch64-linux-gnu", arm_bin], paths, tel_flag)
    mod_x64[m] = xr
    mod_arm[m] = ar
    solvers.append((f"{m} (x64)", m, xr))
    solvers.append((f"{m} (Arm64 qemu)", m, ar))
    if cpp_bin:
        mod_cpp[m] = run_cpp(cpp_bin, cpp_subset)

k_plain = None
k_def = None
if kissat_bin:
    k_plain = run_kissat_mode(["--plain"], paths)
    k_def = run_kissat_mode([], paths)
    solvers.append(("kissat --plain", "", k_plain))
    solvers.append(("kissat (default)", "", k_def))

disagree = 0
for p, label in all_cnfs:
    bn = os.path.basename(p)
    for m, _, _, _, _ in mod_specs:
        xs = mod_x64[m][p][0]
        as_ = mod_arm[m][p][0]
        if xs != as_:
            print(f"ARM64 PARITY MISMATCH [{m}] {label}: x64={xs} arm64={as_}", file=sys.stderr)
            disagree += 1
        if m in mod_cpp and p in mod_cpp[m]:
            cs = mod_cpp[m][p]
            if cs in (10, 20) and xs in (10, 20) and cs != xs:
                print(f"PRINTCPP MISMATCH [{m}] {label}: cpp={cs} x64={xs}", file=sys.stderr)
                disagree += 1
            if "_unsat_" in bn and cs == 10:
                print(f"SOUNDNESS MISMATCH [cpp {m}] {label}: got SAT on _unsat_", file=sys.stderr)
                disagree += 1
            if "_sat_" in bn and cs == 20:
                print(f"SOUNDNESS MISMATCH [cpp {m}] {label}: got UNSAT on _sat_", file=sys.stderr)
                disagree += 1

    verdicts = {name: tbl[p][0] for name, _, tbl in solvers if tbl[p][0] in (10, 20)}
    if len(set(verdicts.values())) > 1:
        print(f"DISAGREEMENT {label}: {verdicts}", file=sys.stderr)
        disagree += 1
    if "_unsat_" in bn and 10 in verdicts.values():
        print(f"EXPECTED-UNSAT VIOLATION {label}: {verdicts}", file=sys.stderr)
        disagree += 1
    if "_sat_" in bn and 20 in verdicts.values():
        print(f"EXPECTED-SAT VIOLATION {label}: {verdicts}", file=sys.stderr)
        disagree += 1

assert disagree == 0, f"Found {disagree} disagreements!"

print("\n== Overall Solver Comparison ==")
hdr = (
    f"{'Solver':<24} {'Solved':>9} {'SAT':>5} {'UNSAT':>5}"
    f" {'Avg(ms)':>9} {'Max(ms)':>9}  Notes / Telemetry"
)
print(hdr)
print("-" * (len(hdr) + 34))
tot = len(paths)
for name, m, tbl in solvers:
    solved = [v for v in tbl.values() if v[0] in (10, 20)]
    nsat = sum(1 for v in solved if v[0] == 10)
    nunsat = sum(1 for v in solved if v[0] == 20)
    ms_list = [v[1] for v in tbl.values()]
    avg_ms = statistics.mean(ms_list)
    max_ms = max(ms_list)
    note = ""
    if m == "Plain":
        confs = sum(tbl[p][2] for p in paths)
        lrn = sum(tbl[p][3] for p in paths)
        mrem = sum(tbl[p][4] for p in paths)
        rst = sum(tbl[p][5] for p in paths)
        red = sum(tbl[p][6] for p in paths)
        sw = sum(tbl[p][8] for p in paths)
        pct = (100.0 * mrem / (lrn + mrem)) if (lrn + mrem) > 0 else 0.0
        note = f"confl={confs} lrn={lrn} rem={mrem}({pct:.1f}%) rst={rst} red={red} sw={sw}"
    elif m in ("CorePlus", "KissatFidelity", "KissatM8Opt", "FullM7Fidelity"):
        confs = sum(tbl[p][2] for p in paths)
        lrn = sum(tbl[p][3] for p in paths)
        mrem = sum(tbl[p][4] for p in paths)
        pct = (100.0 * mrem / (lrn + mrem)) if (lrn + mrem) > 0 else 0.0
        note = f"confl={confs} lrn={lrn} min_rem={mrem}({pct:.1f}%)"
        if "x64" in name and m in mod_cpp:
            note += f" cpp_asan={len(mod_cpp.get(m, {}))}"
    elif m == "Full" and "x64" in name:
        note = f"cpp_asan={len(mod_cpp.get(m, {}))} cases"
    print(
        f"{name:<24} {len(solved):>4}/{tot:<4} {nsat:>5} {nunsat:>5}"
        f" {avg_ms:>9.2f} {max_ms:>9.2f}  {note}"
    )

print("\n== Per-Family Solved Breakdown ==")
cols_hdr = "  ".join(f"{m:>8}" for m, _, _, _, _ in mod_specs)
k_hdr = f"  {'KPlain':>8}  {'Kissat':>8}" if kissat_bin else ""
print(f"{'Family':<14} {'N':>4}  {cols_hdr}{k_hdr}")
for fam, pred in FAMILIES:
    sub = [p for p, l in all_cnfs if pred(l)]
    if not sub:
        continue
    row = [f"{sum(1 for p in sub if mod_x64[m][p][0] in (10, 20)):>8}" for m, _, _, _, _ in mod_specs]
    k_cols = ""
    if kissat_bin:
        kp = sum(1 for p in sub if k_plain[p][0] in (10, 20))
        kd = sum(1 for p in sub if k_def[p][0] in (10, 20))
        k_cols = f"  {kp:>8}  {kd:>8}"
    print(f"{fam:<14} {len(sub):>4}  {'  '.join(row)}{k_cols}")

if mod_cpp:
    print(
        f"\nPrintCpp ASan/UBSan + TQBE_CATCH_UB: PASS "
        f"({len(mod_cpp)} module(s) x {len(cpp_subset)} stratified CNFs + 8 edge checks, 0 UB/ASan)"
    )
print(
    f"PASS: 0 SAT/UNSAT disagreements across {len(solvers)} solver configurations on {tot} CNFs."
)
PY

echo "== bench/kissat/run_full.sh: ALL DIFFERENTIAL & INPROCESSING CHECKS PASSED =="
