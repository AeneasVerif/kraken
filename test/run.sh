#!/usr/bin/env bash
# Litmus tests. For each test/<name>_main.c:
#  1. ours: emit <name>.s with leanqbe, assemble, link with the harness, run;
#  2. stock QBE: print <name>.ssa with `leanqbe --il`, compile it with stock QBE, link, run.
# Stock QBE is built from a copy of the reference checkout (never inside it) unless $QBE is set;
# set NOQBE=1 to skip step 2. Exit code 0 iff every run exits 0. Everything under timeout.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-test.XXXXXX")}"
timeout 1800 lake build leanqbe >"$OUT/build.log" 2>&1 || { tail -20 "$OUT/build.log"; exit 1; }
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
fail=0
run() { # $1 = label, $2 = binary
  if timeout 60 "$2" >"$2.out" 2>&1; then echo "PASS $1"; else echo "FAIL $1: run"; cat "$2.out"; fail=1; fi
}
for h in test/*_main.c; do
  name="$(basename "$h" _main.c)"
  if timeout 60 .lake/build/bin/leanqbe "$name" >"$OUT/$name.s" &&
     timeout 60 cc -O1 -o "$OUT/$name" "$h" "$OUT/$name.s"; then
    run "$name (leanqbe)" "$OUT/$name"
  else echo "FAIL $name (leanqbe): emit or link"; fail=1; fi
  if [ -z "${NOQBE:-}" ]; then
    if timeout 60 .lake/build/bin/leanqbe --il "$name" >"$OUT/$name.ssa" &&
       timeout 60 "$QBE" -o "$OUT/$name.qbe.s" "$OUT/$name.ssa" &&
       timeout 60 cc -O1 -o "$OUT/$name.qbe" "$h" "$OUT/$name.qbe.s"; then
      run "$name (stock qbe)" "$OUT/$name.qbe"
    else echo "FAIL $name (stock qbe): print, qbe or link"; fail=1; fi
  fi
done
echo "outputs in $OUT"
exit $fail
