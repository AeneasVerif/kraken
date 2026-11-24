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

export LAKE_ARTIFACT_CACHE="${LAKE_ARTIFACT_CACHE:-true}"
export LAKE_RESTORE_ARTIFACTS="${LAKE_RESTORE_ARTIFACTS:-true}"

BUILD_TIMEOUT="${BUILD_TIMEOUT:-3600}"
CHECK_TIMEOUT="${CHECK_TIMEOUT:-7200}"
ALL_TIMEOUT="${ALL_TIMEOUT:-7200}"
ALL_JOBS="${ALL_JOBS:-4}"
LAKE_JOBS="${LAKE_JOBS:-${LEAN_NUM_THREADS:-6}}"
CHECK_LOCK_FILE="${CHECK_LOCK_FILE:-/tmp/leanqbe_check_build.lock}"
CHECK_MEM_MAX="${CHECK_MEM_MAX:-48G}"
CHECK_NO_LOCK="${CHECK_NO_LOCK:-0}"
CHECK_NO_SCOPE="${CHECK_NO_SCOPE:-0}"

fail=0
err() { echo "FAIL: $*" >&2; fail=1; }

extra_targets=()
for t in LeanQbeLegacyAmd64 LeanQbeLegacyArm64 LeanQbeLegacyTest \
         LeanQbeBootstrap0 LeanQbeBootstrap0Test; do
  if grep -qE "^name[[:space:]]*=[[:space:]]*\"${t}\"" lakefile.toml 2>/dev/null; then
    extra_targets+=("$t")
  fi
done

TMP_LOG=""
SCOPE_UNIT=""
build_pid=""
cleanup() {
  if [ -n "$SCOPE_UNIT" ]; then
    systemctl --user stop "$SCOPE_UNIT" >/dev/null 2>&1 || true
  fi
  if [ -n "$build_pid" ]; then
    kill "$build_pid" 2>/dev/null || true
  fi
  [ -n "$TMP_LOG" ] && rm -f "$TMP_LOG"
}
trap cleanup EXIT
trap 'cleanup; exit 130' INT
trap 'cleanup; exit 143' TERM
trap 'cleanup; exit 129' HUP

if [ "${#extra_targets[@]}" -gt 0 ]; then
  echo "== tier3 1. build legacy + bootstrap0 targets (--wfail, LAKE_JOBS=$LAKE_JOBS): ${extra_targets[*]}"
  TMP_LOG="$(mktemp "${TMPDIR:-/tmp}/leanqbe-tier3.XXXXXX")"
  build_cmd=(timeout --foreground "$BUILD_TIMEOUT" env "LEAN_NUM_THREADS=$LAKE_JOBS" lake build --wfail "${extra_targets[@]}")
  if [ "$CHECK_NO_SCOPE" != "1" ] \
      && command -v systemd-run >/dev/null 2>&1 \
      && systemd-run --user --scope true >/dev/null 2>&1; then
    SCOPE_UNIT="leanqbe-tier3-${$}-$(date +%s).scope"
    build_cmd=(systemd-run --user --scope --quiet --unit="$SCOPE_UNIT" \
      -p "MemoryMax=$CHECK_MEM_MAX" -p OOMPolicy=kill "${build_cmd[@]}")
  fi
  if [ "$CHECK_NO_LOCK" != "1" ] && command -v flock >/dev/null 2>&1; then
    if ! flock -n "$CHECK_LOCK_FILE" true 2>/dev/null; then
      echo "   waiting for build lock: $CHECK_LOCK_FILE"
    fi
    flock -F "$CHECK_LOCK_FILE" "${build_cmd[@]}" >"$TMP_LOG" 2>&1 &
    build_pid=$!
    wait "$build_pid"
    rc=$?
  else
    "${build_cmd[@]}" >"$TMP_LOG" 2>&1 &
    build_pid=$!
    wait "$build_pid"
    rc=$?
  fi
  build_pid=""
  if [ -n "$SCOPE_UNIT" ]; then
    systemctl --user stop "$SCOPE_UNIT" >/dev/null 2>&1 || true
    SCOPE_UNIT=""
  fi
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
