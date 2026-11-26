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

# Uses scripts/common.sh run_cgroup (--slice=leanqbe-builds.slice, MemorySwapMax=0, OOMPolicy=kill).
# shellcheck source=scripts/common.sh
source "$ROOT/scripts/common.sh"
leanqbe_export_lake_cache
leanqbe_register_traps

BUILD_TIMEOUT="${BUILD_TIMEOUT:-3600}"
CHECK_TIMEOUT="${CHECK_TIMEOUT:-7200}"
ALL_TIMEOUT="${ALL_TIMEOUT:-7200}"
ALL_JOBS="${ALL_JOBS:-4}"
LAKE_JOBS="${LAKE_JOBS:-${LEAN_NUM_THREADS:-6}}"
CHECK_LOCK_FILE="${CHECK_LOCK_FILE:-/tmp/leanqbe_check_build.lock}"
CHECK_MEM_MAX="${CHECK_MEM_MAX:-48G}"

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
  echo "== tier3 1. build legacy + bootstrap0 targets (--wfail, LAKE_JOBS=$LAKE_JOBS): ${extra_targets[*]}"
  TMP_LOG="$(mktemp "${TMPDIR:-/tmp}/leanqbe-tier3.XXXXXX")"
  _LEANQBE_CLEANUP_PATHS+=("$TMP_LOG")
  rc=0
  run_cgroup --mem "$CHECK_MEM_MAX" --unit-prefix leanqbe-tier3 \
    --timeout "$BUILD_TIMEOUT" --log "$TMP_LOG" --lock "$CHECK_LOCK_FILE" -- \
    env "LEAN_NUM_THREADS=$LAKE_JOBS" lake build --wfail "${extra_targets[@]}" || rc=$?
  leanqbe_print_build_summary "$TMP_LOG"
  [ "$rc" -eq 0 ] || err "legacy/bootstrap0 lake build exited with $rc (124 = timeout)"
  if leanqbe_has_sorry_in_log "$TMP_LOG"; then
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
