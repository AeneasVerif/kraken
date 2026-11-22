#!/usr/bin/env bash
# Tier-3 periodic / pre-milestone audit:
#   1. Builds `LeanQbeLegacy{Amd64,Arm64,Test}` and `LeanQbeBootstrap0{,Test}` (when declared
#      in `lakefile.toml`) with `--wfail` and scans build output for `sorry`.
#   2. Runs `CHECK_SCOPE=full INCLUDE_LEGACY=1 CHECK_TIMES=1 ./scripts/check.sh`.
#   3. Runs `ALL_JOBS=4 ./scripts/all.sh` across all repository test/differential/bench suites.
#
# Usage: scripts/tier3_check.sh
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BUILD_TIMEOUT="${BUILD_TIMEOUT:-3600}"
CHECK_TIMEOUT="${CHECK_TIMEOUT:-7200}"
ALL_TIMEOUT="${ALL_TIMEOUT:-7200}"
ALL_JOBS="${ALL_JOBS:-4}"

fail=0
err() { echo "FAIL: $*" >&2; fail=1; }

extra_targets=()
for t in LeanQbeLegacyAmd64 LeanQbeLegacyArm64 LeanQbeLegacyTest \
         LeanQbeBootstrap0 LeanQbeBootstrap0Test; do
  if grep -qE "^name[[:space:]]*=[[:space:]]*\"${t}\"" lakefile.toml 2>/dev/null; then
    extra_targets+=("$t")
  fi
done

if [ "${#extra_targets[@]}" -gt 0 ]; then
  echo "== tier3 1. build legacy + bootstrap0 targets (--wfail): ${extra_targets[*]}"
  TMP_LOG="$(mktemp "${TMPDIR:-/tmp}/leanqbe-tier3.XXXXXX")"
  trap 'rm -f "$TMP_LOG"' EXIT
  timeout "$BUILD_TIMEOUT" env ${LAKE_JOBS:+LEAN_NUM_THREADS="$LAKE_JOBS"} \
    lake build --wfail "${extra_targets[@]}" >"$TMP_LOG" 2>&1
  rc=$?
  grep -E '^(✖|error|warning)|warning:|error:' "$TMP_LOG" | head -n 100 || true
  tail -n 1 "$TMP_LOG" || true
  [ "$rc" -eq 0 ] || err "legacy/bootstrap0 lake build exited with $rc (124 = timeout)"
  if grep -n "declaration uses 'sorry'\|declaration uses \`sorry\`\|sorryAx" "$TMP_LOG"; then
    err "sorry in legacy/bootstrap0 build"
  fi
else
  echo "== tier3 1. no LeanQbeLegacy*/LeanQbeBootstrap0* targets in lakefile.toml; skipping =="
fi

echo "== tier3 2. full check.sh (INCLUDE_LEGACY=1 CHECK_TIMES=1)"
timeout "$CHECK_TIMEOUT" env CHECK_SCOPE=full INCLUDE_LEGACY=1 CHECK_TIMES=1 ./scripts/check.sh \
  || err "scripts/check.sh failed (rc=$?)"

echo "== tier3 3. parallel all.sh (ALL_JOBS=$ALL_JOBS)"
timeout "$ALL_TIMEOUT" env ALL_JOBS="$ALL_JOBS" CHECK_SCOPE=full INCLUDE_LEGACY=1 ./scripts/all.sh \
  || err "scripts/all.sh failed (rc=$?)"

if [ "$fail" -eq 0 ]; then
  echo "== tier3_check.sh: ALL PASSED =="
else
  echo "== tier3_check.sh: FAILED ==" >&2
fi
exit "$fail"
