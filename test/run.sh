#!/usr/bin/env bash
# Litmus tests, native run: for each test/<name>_main.c, emit <name>.s with leanqbe, assemble, link
# with the harness, run. Exit code 0 iff every harness exits 0. Everything under timeout.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-test.XXXXXX")}"
timeout 1800 lake build leanqbe >"$OUT/build.log" 2>&1 || { tail -20 "$OUT/build.log"; exit 1; }
fail=0
for h in test/*_main.c; do
  name="$(basename "$h" _main.c)"
  if ! timeout 60 .lake/build/bin/leanqbe "$name" >"$OUT/$name.s"; then
    echo "FAIL $name: leanqbe"; fail=1; continue
  fi
  if ! timeout 60 cc -O1 -o "$OUT/$name" "$h" "$OUT/$name.s"; then
    echo "FAIL $name: cc"; fail=1; continue
  fi
  if timeout 60 "$OUT/$name"; then echo "PASS $name"; else echo "FAIL $name: run"; fail=1; fi
done
echo "outputs in $OUT"
exit $fail
