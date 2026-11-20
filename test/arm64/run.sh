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
timeout 1800 lake build leanqbe-arm64 >"$OUT/build.log" 2>&1 || { tail -20 "$OUT/build.log"; exit 1; }
if [ -z "${NOQBE:-}" ] && [ -z "${QBE:-}" ]; then
  QBE_SRC="${QBE_SRC:-$ROOT/qbe}"
  if [ -d "$QBE_SRC" ]; then
    rm -rf "$OUT/qbe-src" && cp -r "$QBE_SRC" "$OUT/qbe-src"
    if timeout 300 make -C "$OUT/qbe-src" -j8 >"$OUT/qbe-build.log" 2>&1; then QBE="$OUT/qbe-src/qbe"
    else echo "FAIL: could not build stock QBE (see $OUT/qbe-build.log)"; exit 1; fi
  elif QBE="$(command -v qbe || true)" && [ -n "$QBE" ]; then
    echo "Using stock qbe from PATH: $QBE"
  else
    echo "FAIL: stock QBE not found (set QBE, QBE_SRC, place checkout at $ROOT/qbe, or set NOQBE=1)" >&2
    exit 1
  fi
fi
# ld of the cross toolchain warns about the SFrame format of crtbeginS.o; harmless.
link() { rm -f "$1"; timeout 120 "$CC" -O1 -o "$1" "$2" "$3" 2>&1 | grep -v -e 'SFrame' >&2; [ -x "$1" ]; }
fail=0
run() { # $1 = label, $2 = binary
  if timeout 60 $RUN "$2" >"$2.out" 2>&1; then echo "PASS $1"; else echo "FAIL $1: run"; cat "$2.out"; fail=1; fi
}
for h in test/*_main.c test/arm64/*_main.c; do
  [ -f "$h" ] || continue
  name="$(basename "$h" _main.c)"
  # A harness whose program leanqbe-arm64 does not know fails here: the program table is the one
  # of leanqbe, so there is nothing to skip.
  if timeout 60 .lake/build/bin/leanqbe-arm64 "$name" >"$OUT/$name.s" &&
     link "$OUT/$name" "$h" "$OUT/$name.s"; then
    run "$name (arm64)" "$OUT/$name"
  else echo "FAIL $name (arm64): emit, assemble or link"; fail=1; fi
  if [ -z "${NOQBE:-}" ]; then
    if timeout 60 .lake/build/bin/leanqbe-arm64 --il "$name" >"$OUT/$name.ssa" &&
       timeout 60 "$QBE" -t arm64 -o "$OUT/$name.qbe.s" "$OUT/$name.ssa" &&
       link "$OUT/$name.qbe" "$h" "$OUT/$name.qbe.s"; then
      run "$name (stock qbe arm64)" "$OUT/$name.qbe"
    else echo "FAIL $name (stock qbe arm64): print, qbe or link"; fail=1; fi
  fi
done
echo "outputs in $OUT"
exit $fail
