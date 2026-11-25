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
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 1800 lake build leanqbe >"$OUT/build.log" 2>&1 || { tail -20 "$OUT/build.log"; exit 1; }
fi
if [ -z "${NOQBE:-}" ] && [ -z "${QBE:-}" ]; then
  if ! QBE="$("$ROOT/scripts/ensure_qbe.sh")"; then
    echo "FAIL: could not locate or build stock QBE (set QBE, QBE_SRC, or NOQBE=1)" >&2
    exit 1
  fi
fi

run_harness() {
  local h="$1" name log rc=0
  name="$(basename "$h" _main.c)"
  log="$OUT/$name.log"
  : > "$log"
  if timeout 60 .lake/build/bin/leanqbe "$name" >"$OUT/$name.s" &&
     timeout 60 cc -O1 -o "$OUT/$name" "$h" "$OUT/$name.s"; then
    if timeout 60 "$OUT/$name" >"$OUT/$name.out" 2>&1; then
      echo "PASS $name (leanqbe)" >>"$log"
    else
      echo "FAIL $name (leanqbe): run" >>"$log"
      cat "$OUT/$name.out" >>"$log"
      rc=1
    fi
  else
    echo "FAIL $name (leanqbe): emit or link" >>"$log"
    rc=1
  fi
  if [ -z "${NOQBE:-}" ]; then
    if timeout 60 .lake/build/bin/leanqbe --il "$name" >"$OUT/$name.ssa" &&
       timeout 60 "$QBE" -o "$OUT/$name.qbe.s" "$OUT/$name.ssa" &&
       timeout 60 cc -O1 -o "$OUT/$name.qbe" "$h" "$OUT/$name.qbe.s"; then
      if timeout 60 "$OUT/$name.qbe" >"$OUT/$name.qbe.out" 2>&1; then
        echo "PASS $name (stock qbe)" >>"$log"
      else
        echo "FAIL $name (stock qbe): run" >>"$log"
        cat "$OUT/$name.qbe.out" >>"$log"
        rc=1
      fi
    else
      echo "FAIL $name (stock qbe): print, qbe or link" >>"$log"
      rc=1
    fi
  fi
  return "$rc"
}

MAX_JOBS="${TEST_JOBS:-8}"
fail=0
running=0
logs=()
for h in test/*_main.c; do
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
