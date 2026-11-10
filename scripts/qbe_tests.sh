#!/usr/bin/env bash
# QBE's own test programs through our front end: parse (LeanQbe.Parse) -> PHOAS -> print (LeanQbe.Print)
# -> stock QBE -> link with the test's C driver -> run (exit 0 = pass). The original file through stock
# QBE is run too, as the baseline. Files outside the integer subset are reported as SKIP with the reason.
# Usage: scripts/qbe_tests.sh [workdir]; $QBE = stock qbe binary (else built from a copy of ./qbe).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
W="${1:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-qbetests.XXXXXX")}"
mkdir -p "$W"
QBE_SRC="${QBE_SRC:-$ROOT/qbe}"
[ -d "$QBE_SRC" ] || QBE_SRC=/usr/local/google/home/andreser/lean-qbe/qbe
if [ -z "${QBE:-}" ]; then
  rm -rf "$W/qbe-src" && cp -r "$QBE_SRC" "$W/qbe-src"
  timeout 300 make -C "$W/qbe-src" -j8 >/dev/null 2>&1
  QBE="$W/qbe-src/qbe"
fi
cd "$ROOT"
timeout 600 lake build LeanQbe.Parse LeanQbe.Print >/dev/null || { echo "build failed"; exit 1; }
timeout 900 lake env lean --run scripts/QbeTests.lean "$W/out" "$QBE_SRC"/test/*.ssa > "$W/parse.txt" || { cat "$W/parse.txt"; echo "QbeTests.lean failed"; exit 1; }
grep '^SKIP' "$W/parse.txt"
pass=0; fail=0
for name in $(sed -n 's/^OK \([^:]*\):.*/\1/p' "$W/parse.txt"); do
  d="$W/out"
  ok_ours=FAIL; ok_orig=FAIL
  if timeout 60 "$QBE" -o "$d/$name.s" "$d/$name.ssa" 2>"$d/$name.qbe.err" &&
     timeout 120 cc -o "$d/$name" "$d/${name}_driver.c" "$d/${name}_addr.c" "$d/$name.s" 2>"$d/$name.cc.err" &&
     timeout 30 "$d/$name" > "$d/$name.out" 2>&1; then ok_ours=PASS; fi
  if timeout 60 "$QBE" -o "$d/$name.orig.s" "$QBE_SRC/test/$name.ssa" 2>/dev/null &&
     timeout 120 cc -o "$d/$name.orig" "$d/${name}_driver.c" "$d/$name.orig.s" 2>/dev/null &&
     timeout 30 "$d/$name.orig" > "$d/$name.orig.out" 2>&1; then ok_orig=PASS; fi
  echo "$name: ours=$ok_ours stock=$ok_orig"
  if [ $ok_ours = PASS ]; then pass=$((pass+1)); else fail=$((fail+1)); fi
done
echo "parsed and passed: $pass, parsed and failed: $fail, skipped: $(grep -c '^SKIP' "$W/parse.txt")"
[ $fail -eq 0 ]
