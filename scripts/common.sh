#!/usr/bin/env bash
# Shared shell helpers for LeanQbe gate, build, and CI scripts.

_LEANQBE_SCOPE_UNIT=""
_LEANQBE_BUILD_PID=""
_LEANQBE_LOCK_FD=""
_LEANQBE_CLEANUP_PATHS=()

leanqbe_export_lake_cache() {
  export LAKE_ARTIFACT_CACHE="${LAKE_ARTIFACT_CACHE:-true}"
  export LAKE_RESTORE_ARTIFACTS="${LAKE_RESTORE_ARTIFACTS:-true}"
}

leanqbe_cleanup() {
  [ -n "${_LEANQBE_SCOPE_UNIT:-}" ] && { systemctl --user stop "$_LEANQBE_SCOPE_UNIT" >/dev/null 2>&1 || true; _LEANQBE_SCOPE_UNIT=""; }
  [ -n "${_LEANQBE_BUILD_PID:-}" ] && { kill "$_LEANQBE_BUILD_PID" 2>/dev/null || true; _LEANQBE_BUILD_PID=""; }
  [ "${_LEANQBE_LOCK_FD:-}" = "9" ] && { exec 9>&- 2>/dev/null || true; _LEANQBE_LOCK_FD=""; }
  if [ "${#_LEANQBE_CLEANUP_PATHS[@]}" -gt 0 ]; then
    rm -rf "${_LEANQBE_CLEANUP_PATHS[@]}"
    _LEANQBE_CLEANUP_PATHS=()
  fi
}

leanqbe_register_traps() {
  trap leanqbe_cleanup EXIT
  trap 'leanqbe_cleanup; exit 130' INT
  trap 'leanqbe_cleanup; exit 143' TERM
  trap 'leanqbe_cleanup; exit 129' HUP
}

leanqbe_scope_available() {
  [ "${CHECK_NO_SCOPE:-0}" != "1" ] && command -v systemd-run >/dev/null 2>&1 && systemd-run --user --scope true >/dev/null 2>&1
}

build_cgroup_cmd() {
  local _leanqbe_out_var="$1" _mem_max="$2" _unit="$3" _slice="$4"
  shift 4; [ "${1:-}" = "--" ] && shift
  local -a _res=()
  if [ "${LEANQBE_FORCE_SCOPE:-0}" = "1" ] || leanqbe_scope_available; then
    _res=(systemd-run --user --scope --quiet)
    [ -n "$_unit" ] && _res+=("--unit=$_unit")
    _res+=("--slice=$_slice" -p "MemoryMax=$_mem_max" -p MemorySwapMax=0 -p OOMPolicy=kill)
  fi
  _res+=("$@")
  local -n _leanqbe_out_ref="$_leanqbe_out_var"
  _leanqbe_out_ref=("${_res[@]}")
}

run_cgroup() {
  local mem="${CHECK_MEM_MAX:-48G}" slice="leanqbe-builds.slice" unit="" unit_prefix="leanqbe-cgroup"
  local timeout_sec="" log_path="" lock_file="" fast_lock_prefix=""
  while [ $# -gt 0 ]; do
    case "$1" in
      --mem) mem="$2"; shift 2 ;;
      --slice) slice="$2"; shift 2 ;;
      --unit) unit="$2"; shift 2 ;;
      --unit-prefix) unit_prefix="$2"; shift 2 ;;
      --timeout) timeout_sec="$2"; shift 2 ;;
      --log) log_path="$2"; shift 2 ;;
      --lock) lock_file="$2"; shift 2 ;;
      --fast-lock) fast_lock_prefix="$2"; shift 2 ;;
      --) shift; break ;;
      *) break ;;
    esac
  done
  [ $# -gt 0 ] || { echo "run_cgroup: missing command" >&2; return 2; }

  local -a inner_cmd=("$@") cgroup_cmd=()
  [ -n "$timeout_sec" ] && [ "$timeout_sec" != "0" ] && inner_cmd=(timeout --foreground "$timeout_sec" "${inner_cmd[@]}")
  local candidate_unit="${unit:-${unit_prefix}-${$}-$(date +%s)}"
  build_cgroup_cmd cgroup_cmd "$mem" "$candidate_unit" "$slice" -- "${inner_cmd[@]}"
  _LEANQBE_SCOPE_UNIT=""
  [ "${cgroup_cmd[0]}" = "systemd-run" ] && _LEANQBE_SCOPE_UNIT="$candidate_unit"

  local use_lock=0 active_lock="" slot cand
  if [ "${CHECK_NO_LOCK:-0}" != "1" ] && command -v flock >/dev/null 2>&1; then
    if [ -n "$fast_lock_prefix" ]; then
      use_lock=1; mkdir -p "$(dirname "$fast_lock_prefix")" 2>/dev/null || true
      for slot in 0 1; do
        cand="${fast_lock_prefix}_${slot}.lock"; exec 9>>"$cand"
        if flock -n 9; then active_lock="$cand"; _LEANQBE_LOCK_FD=9; break; fi
        exec 9>&-
      done
      if [ -z "$active_lock" ]; then
        active_lock="${fast_lock_prefix}_$(( $$ % 2 )).lock"
        echo "   waiting for fast build lock: $active_lock"
        exec 9>>"$active_lock"; flock 9; _LEANQBE_LOCK_FD=9
      fi
    elif [ -n "$lock_file" ]; then
      use_lock=1; mkdir -p "$(dirname "$lock_file")" 2>/dev/null || true
      flock -n "$lock_file" true 2>/dev/null || echo "   waiting for build lock: $lock_file"
      exec 9>>"$lock_file"; flock 9; _LEANQBE_LOCK_FD=9
    fi
  fi

  local rc=0
  if [ -n "$log_path" ]; then "${cgroup_cmd[@]}" 9>&- >"$log_path" 2>&1 & else "${cgroup_cmd[@]}" 9>&- & fi
  _LEANQBE_BUILD_PID=$!
  wait "$_LEANQBE_BUILD_PID" || rc=$?
  _LEANQBE_BUILD_PID=""
  [ "$use_lock" -eq 1 ] && [ "${_LEANQBE_LOCK_FD:-}" = "9" ] && { exec 9>&- 2>/dev/null || true; _LEANQBE_LOCK_FD=""; }
  [ -n "${_LEANQBE_SCOPE_UNIT:-}" ] && { systemctl --user stop "$_LEANQBE_SCOPE_UNIT" >/dev/null 2>&1 || true; _LEANQBE_SCOPE_UNIT=""; }
  return "$rc"
}

leanqbe_print_build_summary() {
  grep -E '^(✖|error|warning)|warning:|error:' "$1" | head -n 100 || true
  tail -n 1 "$1" || true
}

leanqbe_has_sorry_in_log() {
  grep -n "declaration uses 'sorry'\|declaration uses \`sorry\`\|sorryAx" "$1"
}

leanqbe_throttle_jobs() {
  while [ "$(jobs -rp | wc -l)" -ge "$1" ]; do wait -n 2>/dev/null || true; done
}
