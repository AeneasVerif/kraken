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

echo "== test/kissat/run.sh: ALL DIFFERENTIAL CHECKS PASSED =="
