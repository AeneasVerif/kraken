#!/usr/bin/env bash
# Differential verification suite for LeanQbe.T.Examples.Kissat:
# Compares across:
#   1. Pure-Lean cdclSolve reference model (verified during artifact generation)
#   2. PrintCpp + g++ -std=c++20 -O2 -DTQBE_CATCH_UB (aligned + unaligned work_ptr)
#   3. PrintCpp + clang++ -std=c++20 -O2 -fsanitize=undefined,address -DTQBE_CATCH_UB
#   4. Native x64 assembly (x64Target) + mmap guard pages + DIMACS model verifier
#   5. Native Arm64 assembly (armTarget) via qemu-aarch64 + mmap guard pages + model verifier
#   6. Stock QBE (amd64_sysv + arm64 via qemu-aarch64) when stock QBE source/binary exists
#   7. Reference kissat CLI (--basic --lucky=0) when kissat exists in PATH or scratch/
#   8-9. Legacy FullM3 + FullM4 unified differential checks (gated behind KISSAT_INCLUDE_LEGACY=1)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-kissat.XXXXXX")}"
cleanup() {
  if [ -z "$OUT_USER" ]; then
    rm -rf "$OUT"
  fi
}
trap cleanup EXIT
mkdir -p "$OUT/logs"
echo "outputs in $OUT"

run_lean() {
  local secs="$1"; shift
  if [ -n "${STAGE_LEAN_PATH:-}" ]; then
    LEAN_PATH="$STAGE_LEAN_PATH:$ROOT/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}" \
      timeout "$secs" lean "$@"
  else
    timeout "$secs" lake env lean "$@"
  fi
}

echo "== 1. build Kissat Solver/Test and generate C++20 / QBE / corpus artifacts =="
if [ -z "${STAGE_LEAN_PATH:-}" ] && [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 600 lake build --wfail LeanQbe.T.Examples.Kissat.Solver LeanQbe.T.Driver \
    LeanQbe.T.Amd64.Targ LeanQbe.T.Amd64.PrintATTAlign LeanQbe.T.Arm64.Targ \
    LeanQbeTest.T.KissatC0Test
fi
run_lean 120 --run LeanQbeTest/T/KissatC0Test.lean "$OUT"

RT_INC="$ROOT/LeanQbe/T/Runtime"
KTEST_INC="$ROOT/test/kissat"
COMMON_CXX="-std=c++20 -O2 -Wall -Wextra -Werror -I$RT_INC -I$KTEST_INC -I$OUT"
COMMON_C="-O1 -Wall -Wextra -Werror -I$KTEST_INC -I$OUT"

if [ -z "${QBE:-}" ]; then
  qbe_rc=0
  QBE="$("$ROOT/scripts/ensure_qbe.sh")" || qbe_rc=$?
  if [ "$qbe_rc" -ne 0 ] && [ "$qbe_rc" -ne 2 ]; then
    exit "$qbe_rc"
  fi
  if [ "$qbe_rc" -eq 2 ]; then
    QBE=""
  fi
fi

KISSAT_BIN="${KISSAT_BIN:-$(command -v kissat || true)}"
if [ -z "$KISSAT_BIN" ] && [ -x "$ROOT/scratch/kissat" ]; then
  KISSAT_BIN="$ROOT/scratch/kissat"
fi

echo "== 2-7. parallel PrintCpp (g++/clang++ ASan), native x64 + Arm64, QBE, and kissat checks =="
step_names=()
step_pids=()
launch_step() {
  local name="$1"; shift
  "$@" >"$OUT/logs/$name.log" 2>&1 &
  step_names+=("$name")
  step_pids+=($!)
}

job_gpp() {
  timeout 60 g++ $COMMON_CXX -DTQBE_CATCH_UB "$OUT/kissat_driver.cpp" -o "$OUT/kissat_gpp"
  timeout 60 "$OUT/kissat_gpp"
}

job_asan() {
  timeout 60 clang++ $COMMON_CXX -fsanitize=undefined,address -DTQBE_CATCH_UB \
    "$OUT/kissat_driver.cpp" -o "$OUT/kissat_asan"
  timeout 60 "$OUT/kissat_asan"
}

job_native_both() {
  timeout 120 python3 -B test/common/emit.py --both-arches --suite kissat \
    --x64-arg "$OUT/kissat_x64.s" --arm64-arg "$OUT/kissat_arm64.s"
  (
    timeout 60 gcc $COMMON_C -no-pie test/kissat/kissat_main.c "$OUT/kissat_x64.s" \
      -o "$OUT/kissat_x64"
    timeout 60 "$OUT/kissat_x64" > "$OUT/x64.out"
  ) &
  local px=$!
  (
    timeout 60 aarch64-linux-gnu-gcc $COMMON_C test/kissat/kissat_main.c "$OUT/kissat_arm64.s" \
      -o "$OUT/kissat_arm64" 2>"$OUT/arm64_cc.log" || { cat "$OUT/arm64_cc.log" >&2; exit 1; }
    grep -v -e 'SFrame' "$OUT/arm64_cc.log" >&2 || true
    timeout 60 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/kissat_arm64" > "$OUT/arm64.out"
  ) &
  local pa=$!
  wait "$px"
  wait "$pa"
}

job_qbe_both() {
  (
    timeout 60 "$QBE" -t amd64_sysv -o "$OUT/kissat_qbe_x64.s" "$OUT/kissat.ssa"
    timeout 60 gcc $COMMON_C -no-pie test/kissat/kissat_main.c "$OUT/kissat_qbe_x64.s" \
      -o "$OUT/kissat_qbe_x64"
    timeout 60 "$OUT/kissat_qbe_x64" > "$OUT/qbe_x64.out"
  ) &
  local pqx=$!
  (
    timeout 60 "$QBE" -t arm64 -o "$OUT/kissat_qbe_arm64.s" "$OUT/kissat.ssa"
    timeout 60 aarch64-linux-gnu-gcc $COMMON_C test/kissat/kissat_main.c \
      "$OUT/kissat_qbe_arm64.s" -o "$OUT/kissat_qbe_arm64" \
      2>"$OUT/qbe_arm64_cc.log" || { cat "$OUT/qbe_arm64_cc.log" >&2; exit 1; }
    grep -v -e 'SFrame' "$OUT/qbe_arm64_cc.log" >&2 || true
    timeout 60 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/kissat_qbe_arm64" \
      > "$OUT/qbe_arm64.out"
  ) &
  local pqa=$!
  wait "$pqx"
  wait "$pqa"
}

job_ref_kissat() {
  timeout 120 python3 -B - "$KISSAT_BIN" "$OUT/kissat_cases.h" "$OUT" <<'PY'
import re, subprocess, sys
kbin, hdr, out = sys.argv[1], sys.argv[2], sys.argv[3]
src = open(hdr).read()
pat = r'\{"([^"]+)",\s*"((?:[^"\\]|\\.)*)",\s*\d+ULL,\s*\d+ULL,\s*\d+ULL,\s*(\d+)ULL\}'
for m in re.finditer(pat, src):
    nm, cnf_esc, exp = m.group(1), m.group(2), int(m.group(3))
    if exp not in (10, 20) or nm.startswith(("fuel_", "tiny_", "bad_")):
        continue
    cnf = bytes(cnf_esc, "utf-8").decode("unicode_escape").encode("latin1")
    p = f"{out}/{nm}.cnf"
    open(p, "wb").write(cnf)
    r = subprocess.run(
        ["timeout", "30", kbin, "--basic", "--lucky=0", "-q", p], capture_output=True)
    if r.returncode != exp:
        raise SystemExit(f"kissat mismatch on {nm}: got {r.returncode}, exp {exp}")
print("PASS: reference kissat cross-check")
PY
}

launch_step gpp job_gpp
launch_step asan job_asan
launch_step native job_native_both
if [ -n "${QBE:-}" ]; then
  launch_step qbe job_qbe_both
fi
if [ -n "${KISSAT_BIN:-}" ]; then
  launch_step ref_kissat job_ref_kissat
fi

solver_fail=0
for i in "${!step_pids[@]}"; do
  if ! wait "${step_pids[$i]}"; then
    echo "FAIL: Solver step '${step_names[$i]}' failed:" >&2
    cat "$OUT/logs/${step_names[$i]}.log" >&2 || true
    solver_fail=1
  fi
done
if [ "$solver_fail" -ne 0 ]; then
  exit 1
fi

for name in "${step_names[@]}"; do
  [ -s "$OUT/logs/$name.log" ] && cat "$OUT/logs/$name.log"
done
tail -n 1 "$OUT/x64.out"
diff -u "$OUT/x64.out" "$OUT/arm64.out"
if [ -n "${QBE:-}" ]; then
  diff -u "$OUT/x64.out" "$OUT/qbe_x64.out"
  diff -u "$OUT/x64.out" "$OUT/qbe_arm64.out"
else
  echo "NOTE: stock QBE not found (set QBE, QBE_SRC, or place checkout at $ROOT/qbe); skipping step 6."
fi

if [ "${KISSAT_INCLUDE_LEGACY:-0}" = "1" ]; then
  echo "== 8-9. Legacy FullM3 + FullM4 unified differential checks (KISSAT_INCLUDE_LEGACY=1) =="
  if [ -z "${STAGE_LEAN_PATH:-}" ] && [ "${SKIP_BUILD:-0}" != "1" ]; then
    timeout 600 lake build --wfail LeanQbe.T.Examples.Kissat.FullM3 \
      LeanQbe.T.Examples.Kissat.FullM4 LeanQbe.T.PrintCpp \
      LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Arm64.Targ \
      Kraken.X64.PrintATT Kraken.AArch64.Print LeanQbe.T.Amd64.PrintATTAlign
  fi

  write_bridge() {
    local gen_hdr="$1" out_cpp="$2"
    cat > "$out_cpp" <<CPP
#include <cstdint>
#include "tqbe_rt.hpp"

namespace tqbe_gen {
#include "$gen_hdr"
}

extern "C" uint64_t kissat_solve_bytes(
    const uint8_t *cnf_ptr, uint64_t cnf_len,
    uint8_t *work_ptr, uint64_t work_len, uint64_t fuel) {
  ::tqbe::Mem mem;
  return tqbe_gen::kissat_solve_bytes(
      mem,
      ::tqbe::bits<64>(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(cnf_ptr))),
      ::tqbe::bits<64>(cnf_len),
      ::tqbe::bits<64>(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(work_ptr))),
      ::tqbe::bits<64>(work_len),
      ::tqbe::bits<64>(fuel)).word(0);
}
CPP
  }
  write_bridge "m3_gen.hpp" "$OUT/m3_bridge.cpp"
  write_bridge "m4_gen.hpp" "$OUT/m4_bridge.cpp"

  # Compile bench_main.o once (x64 + arm64) and generate shared canary CNFs once,
  # overlapped with FullM3 x64+Arm64 emission.
  mkdir -p "$OUT/legacy_cnfs"
  timeout 60 gcc -std=c99 -O2 -Wall -Wextra -Werror -I"$KTEST_INC" \
    -c bench/kissat/bench_main.c -o "$OUT/bench_main.o" &
  pid_bm_x64=$!
  (
    timeout 60 aarch64-linux-gnu-gcc -std=c99 -O2 -Wall -Wextra -Werror -I"$KTEST_INC" \
      -c bench/kissat/bench_main.c -o "$OUT/bench_main_arm64.o" 2>"$OUT/bm_arm64_cc.log" || {
        cat "$OUT/bm_arm64_cc.log" >&2; exit 1; }
    grep -v -e 'SFrame' "$OUT/bm_arm64_cc.log" >&2 || true
  ) &
  pid_bm_arm64=$!
  timeout 60 python3 -B bench/kissat/gen_canary_cnfs.py "$OUT/legacy_cnfs" >/dev/null &
  pid_cnfs=$!
  timeout 180 python3 -B test/common/emit.py --both-arches --suite m3 \
    --x64-arg "$OUT/m3_x64.s" --x64-arg "$OUT/m3_gen.hpp" --arm64-arg "$OUT/m3_arm64.s" &
  pid_m3_emit=$!

  wait "$pid_bm_x64"; wait "$pid_bm_arm64"; wait "$pid_m3_emit"

  # Overlap FullM3 C/C++ compiles with FullM4 x64+Arm64 emission.
  timeout 240 clang++ -std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=undefined,address \
    -DTQBE_NATIVE_MEM -I"$RT_INC" -I"$OUT" "$OUT/m3_bridge.cpp" "$OUT/bench_main.o" \
    -o "$OUT/m3_asan" &
  pid_m3_asan=$!
  timeout 60 gcc -std=c99 -O2 -Wall -Wextra -Werror -no-pie -I"$KTEST_INC" \
    "$OUT/bench_main.o" "$OUT/m3_x64.s" -o "$OUT/m3_x64" &
  pid_m3_x64=$!
  (
    timeout 60 aarch64-linux-gnu-gcc -std=c99 -O2 -Wall -Wextra -Werror -I"$KTEST_INC" \
      "$OUT/bench_main_arm64.o" "$OUT/m3_arm64.s" -o "$OUT/m3_arm64" 2>"$OUT/m3_arm64_cc.log" || {
        cat "$OUT/m3_arm64_cc.log" >&2; exit 1; }
    grep -v -e 'SFrame' "$OUT/m3_arm64_cc.log" >&2 || true
  ) &
  pid_m3_arm64=$!
  timeout 300 python3 -B test/common/emit.py --both-arches --suite m4 \
    --x64-arg "$OUT/m4_x64.s" --x64-arg "$OUT/m4_gen.hpp" --arm64-arg "$OUT/m4_arm64.s" &
  pid_m4_emit=$!

  wait "$pid_m3_asan"; wait "$pid_m3_x64"; wait "$pid_m3_arm64"; wait "$pid_m4_emit"; wait "$pid_cnfs"

  # Compile FullM4 binaries in parallel (reusing bench_main.o / bench_main_arm64.o).
  timeout 240 clang++ -std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=undefined,address \
    -DTQBE_NATIVE_MEM -I"$RT_INC" -I"$OUT" "$OUT/m4_bridge.cpp" "$OUT/bench_main.o" \
    -o "$OUT/m4_asan" &
  pid_m4_asan=$!
  timeout 60 gcc -std=c99 -O2 -Wall -Wextra -Werror -no-pie -I"$KTEST_INC" \
    "$OUT/bench_main.o" "$OUT/m4_x64.s" -o "$OUT/m4_x64" &
  pid_m4_x64=$!
  (
    timeout 60 aarch64-linux-gnu-gcc -std=c99 -O2 -Wall -Wextra -Werror -I"$KTEST_INC" \
      "$OUT/bench_main_arm64.o" "$OUT/m4_arm64.s" -o "$OUT/m4_arm64" 2>"$OUT/m4_arm64_cc.log" || {
        cat "$OUT/m4_arm64_cc.log" >&2; exit 1; }
    grep -v -e 'SFrame' "$OUT/m4_arm64_cc.log" >&2 || true
  ) &
  pid_m4_arm64=$!

  wait "$pid_m4_asan"; wait "$pid_m4_x64"; wait "$pid_m4_arm64"

  timeout 300 python3 -B - "$OUT" <<'PY'
import concurrent.futures, glob, os, subprocess, sys

out = sys.argv[1]
cdir = os.path.join(out, "legacy_cnfs")
cases = [
    ("edge_empty.cnf", "", 64, 1000, 0),
    ("edge_bad_hdr.cnf", "p sat 1 1\n", 65536, 1000, 0),
    ("edge_bad_lit.cnf", "p cnf 1 1\n2 0\n", 65536, 1000, 0),
    ("tiny_work.cnf", "p cnf 1 1\n1 0\n", 64, 1000, 0),
    ("sat_unit.cnf", "p cnf 1 1\n1 0\n", 1 << 20, 10000, 10),
    ("unsat_unit.cnf", "p cnf 1 2\n1 0\n-1 0\n", 1 << 20, 10000, 20),
    ("sat_chain.cnf",
     "p cnf 4 4\n-1 2 0\n-2 3 0\n-3 4 0\n1 2 3 4 0\n", 1 << 20, 10000, 10),
    ("unsat_php3.cnf",
     "p cnf 6 9\n1 2 0\n3 4 0\n5 6 0\n-1 -3 0\n-1 -5 0\n-3 -5 0\n-2 -4 0\n-2 -6 0\n-4 -6 0\n",
     1 << 20, 50000, 20),
]

for name, txt, _w, _f, _e in cases:
    with open(os.path.join(cdir, name), "w") as fh:
        fh.write(txt)

pats = ("_small", "6_5", "500", "256", "c02_", "c03_", "c04_", "c05_", "c06_", "c07_")
canary_paths = [
    p for p in sorted(glob.glob(os.path.join(cdir, "c*.cnf")))
    if any(k in os.path.basename(p) for k in pats)
]

def run_tel(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True, check=True)
    toks = r.stdout.strip().split("\t")
    kv = dict(t.split("=", 1) for t in toks[3:] if "=" in t)
    return (int(toks[1]), kv.get("conflicts"), kv.get("learned_lits"),
            kv.get("min_removed"), kv.get("search_ticks"))

def check_one(item):
    tag, path, work, fuel, exp, allow_unk = item
    args = ["--full-telemetry-m2", str(work), str(fuel), path]
    t_asan = run_tel(["timeout", "20", f"{out}/{tag}_asan"] + args)
    t_x64 = run_tel(["timeout", "20", f"{out}/{tag}_x64"] + args)
    t_arm = run_tel(["timeout", "20", "qemu-aarch64", "-L", "/usr/aarch64-linux-gnu",
                     f"{out}/{tag}_arm64"] + args)
    if not (t_asan == t_x64 == t_arm):
        raise RuntimeError(
            f"{tag.upper()} parity mismatch on {path}: asan={t_asan} x64={t_x64} arm={t_arm}"
        )
    st = t_x64[0]
    if exp is not None and not (allow_unk and st == 0) and st != exp:
        raise RuntimeError(f"{tag.upper()} status mismatch on {path}: got={st}, exp={exp}")

work_items = []
for tag in ("m3", "m4"):
    for name, _txt, work, fuel, exp in cases:
        work_items.append((tag, os.path.join(cdir, name), work, fuel, exp, False))
    for p in canary_paths:
        work_items.append((tag, p, 8 << 20, 300000, 20, True))

with concurrent.futures.ThreadPoolExecutor(8) as ex:
    for _ in ex.map(check_one, work_items):
        pass

print("PASS: FullM3 3-way differential verification (PrintCpp ASan/UBSan == x64 == Arm64)")
print("PASS: FullM4 3-way differential verification (PrintCpp ASan/UBSan == x64 == Arm64)")
PY
else
  echo "NOTE: skipping legacy FullM3/FullM4 steps 8-9 (set KISSAT_INCLUDE_LEGACY=1 to run)"
fi

echo "== test/kissat/run.sh: ALL DIFFERENTIAL CHECKS PASSED =="
