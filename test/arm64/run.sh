#!/usr/bin/env bash
# AArch64 litmus and union-find tests. For each test/*_main.c and test/arm64/*_main.c:
#  1. ours: emit <name>.s with leanqbe-arm64 (Arm64.isa), cross-assemble with the harness,
#     run under qemu-aarch64;
#  2. stock QBE: print <name>.ssa with `leanqbe-arm64 --il`, compile with stock QBE `-t arm64`, run.
# Stock QBE is built from a copy of the reference checkout (never inside it) unless $QBE is set;
# set NOQBE=1 to skip step 2. Exit code 0 iff every run exits 0. Everything under timeout.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-arm64.XXXXXX")}"
CC="${CC_AARCH64:-aarch64-linux-gnu-gcc}"
RUN="qemu-aarch64 -L /usr/aarch64-linux-gnu"
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  if ! timeout 1800 lake build leanqbe-arm64 >"$OUT/build.log" 2>&1; then
    tail -20 "$OUT/build.log"
    exit 1
  fi
fi
if [ -z "${NOQBE:-}" ] && [ -z "${QBE:-}" ]; then
  if ! QBE="$("$ROOT/scripts/ensure_qbe.sh")"; then
    echo "FAIL: could not locate or build stock QBE (set QBE, QBE_SRC, or NOQBE=1)" >&2
    exit 1
  fi
fi

# ld of the cross toolchain warns about the SFrame format of crtbeginS.o; harmless.
link_logged() {
  local out_bin="$1" src_c="$2" src_s="$3" log="$4"
  rm -f "$out_bin"
  timeout 120 "$CC" -O1 -o "$out_bin" "$src_c" "$src_s" 2>&1 | { grep -v -e 'SFrame' || true; } >>"$log"
  [ -x "$out_bin" ]
}

run_harness() {
  local h="$1" name log rc=0
  name="$(basename "$h" _main.c)"
  log="$OUT/$name.log"
  : > "$log"
  # A harness whose program leanqbe-arm64 does not know fails here: the program table is the one
  # of leanqbe, so there is nothing to skip.
  if timeout 60 .lake/build/bin/leanqbe-arm64 "$name" >"$OUT/$name.s" &&
     link_logged "$OUT/$name" "$h" "$OUT/$name.s" "$log"; then
    if timeout 60 $RUN "$OUT/$name" >"$OUT/$name.out" 2>&1; then
      echo "PASS $name (arm64)" >>"$log"
    else
      echo "FAIL $name (arm64): run" >>"$log"
      cat "$OUT/$name.out" >>"$log"
      rc=1
    fi
  else
    echo "FAIL $name (arm64): emit, assemble or link" >>"$log"
    rc=1
  fi
  if [ -z "${NOQBE:-}" ]; then
    if timeout 60 .lake/build/bin/leanqbe-arm64 --il "$name" >"$OUT/$name.ssa" &&
       timeout 60 "$QBE" -t arm64 -o "$OUT/$name.qbe.s" "$OUT/$name.ssa" &&
       link_logged "$OUT/$name.qbe" "$h" "$OUT/$name.qbe.s" "$log"; then
      if timeout 60 $RUN "$OUT/$name.qbe" >"$OUT/$name.qbe.out" 2>&1; then
        echo "PASS $name (stock qbe arm64)" >>"$log"
      else
        echo "FAIL $name (stock qbe arm64): run" >>"$log"
        cat "$OUT/$name.qbe.out" >>"$log"
        rc=1
      fi
    else
      echo "FAIL $name (stock qbe arm64): print, qbe or link" >>"$log"
      rc=1
    fi
  fi
  return "$rc"
}

MAX_JOBS="${TEST_JOBS:-8}"
fail=0
running=0
logs=()
for h in test/*_main.c test/arm64/*_main.c; do
  [ -f "$h" ] || continue
  while [ "$running" -ge "$MAX_JOBS" ]; do
    wait -n || fail=1
    running=$((running - 1))
  done
  name="$(basename "$h" _main.c)"
  logs+=("$OUT/$name.log")
  run_harness "$h" &
  running=$((running + 1))
done
while [ "$running" -gt 0 ]; do
  wait -n || fail=1
  running=$((running - 1))
done
for log in "${logs[@]}"; do
  cat "$log"
done
echo "outputs in $OUT"
exit $fail
