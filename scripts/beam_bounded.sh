#!/usr/bin/env bash
# Bounded, swarm-safe wrapper around leanprover/lean-beam (v3).
# - Locates lean-beam via $LEAN_BEAM_BIN, PATH, or ~/.local/share/lean-beam/bin/lean-beam.
# - Isolates session state under /tmp/lean-beam-$USER/<sha16(root)> (never pollutes <wt>/.beam/).
# - Runs daemon + idle watchdog inside a detached transient systemd user service under
#   leanqbe-builds.slice (MemoryMax=${MEM}, OOMPolicy=kill) so it persists across separate shell calls.
# - Auto-starts on sync/diag/goals/run-at (and query/edit-loop commands) if not running.
# - Never overlap with `lake build` / `scripts/build_bounded.sh`: always run `stop` first.
set -euo pipefail

DEFAULT_BEAM_BIN="${HOME}/.local/share/lean-beam/bin/lean-beam"

usage() {
  cat <<'EOF'
Usage: scripts/beam_bounded.sh <command> [args...]

Daemon lifecycle:
  start [-m 24G] [--idle-min 15]   Start detached daemon under leanqbe-builds.slice
  stop                             Stop daemon, remove transient systemd unit & session dir
  status                           Report daemon state (absent/running/...)
  doctor [--json]                  Check lean-beam runtime/toolchain health

Interactive proof loop (auto-starts daemon if not running):
  diag [--max N] [--errors-only] <file.lean>
                                   Run sync and print concise file:line:col [severity]: msg
  sync <file.lean> [+all-diagnostics]
                                   Sync saved file and print full JSON result + version
  goals <before|after> <file.lean> <version> <line0> <col0>
                                   Inspect proof state at 0-based LSP line/col
  run-at <file.lean> <version> <line0> <col0> [--profile] (--stdin | --text-file <p> | <text>)
                                   Probe tactics in-memory without editing disk
  hover <file.lean> <version> <line0> <col0>
                                   Inspect type/docstring at 0-based LSP line/col

Additional pass-through commands:
  update, refresh, save, close, close-save, signature-help, definition, references,
  document-symbols, workspace-symbols, todo, run-at-handle, run-with, run-with-linear,
  release, open-files, stats, cancel, recover

Environment:
  LEAN_BEAM_BIN           Explicit path to lean-beam wrapper/executable
  LEAN_BEAM_TIMEOUT       Client call timeout in seconds (default: 120)
  LEAN_BEAM_MEM           Default start MemoryMax (default: 24G)
  LEAN_BEAM_IDLE_MIN      Idle shutdown timeout in minutes (default: 15)
  LEAN_BEAM_DIAG_MAX      Max diagnostics printed by `diag` (default: 30; 0 = unlimited)
  LEAN_BEAM_MIN_AVAIL_MIB Minimum host MemAvailable MiB required to start (default: 18432)
EOF
}

cmd="${1:-help}"
if [[ $# -gt 0 ]]; then
  shift
fi

case "$cmd" in
  help|-h|--help)
    usage
    exit 0
    ;;
esac

resolve_beam_bin() {
  if [[ -n "${LEAN_BEAM_BIN:-}" ]]; then
    if [[ -x "$LEAN_BEAM_BIN" ]]; then
      printf '%s\n' "$LEAN_BEAM_BIN"
      return 0
    fi
    echo "beam_bounded.sh: error: LEAN_BEAM_BIN='$LEAN_BEAM_BIN' is not executable" >&2
    return 127
  fi
  local found=""
  if found="$(command -v lean-beam 2>/dev/null)" && [[ -x "$found" ]]; then
    printf '%s\n' "$found"
    return 0
  fi
  if [[ -x "$DEFAULT_BEAM_BIN" ]]; then
    printf '%s\n' "$DEFAULT_BEAM_BIN"
    return 0
  fi
  echo "beam_bounded.sh: error: lean-beam not found (checked \$LEAN_BEAM_BIN, PATH, and $DEFAULT_BEAM_BIN); fall back to lake env lean or scripts/build_bounded.sh" >&2
  return 127
}

BEAM_BIN="$(resolve_beam_bin)"
CLIENT_TIMEOUT="${LEAN_BEAM_TIMEOUT:-120}"

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd -P)"
ROOT="$(cd "$ROOT" && pwd -P)"
USER_NAME="${USER:-$(id -un)}"
HASH="$(printf '%s' "$ROOT" | sha256sum | cut -c1-16)"
UNIT="lean-beam-${HASH}.service"
BASE_DIR="/tmp/lean-beam-${USER_NAME}"
SESS_DIR="${BASE_DIR}/${HASH}"
LOCK_FILE="${BASE_DIR}/${HASH}.lock"

mkdir -p "$BASE_DIR"
chmod 700 "$BASE_DIR" 2>/dev/null || true

export BEAM_SESSION_ROOT="$BASE_DIR"

touch_activity() {
  mkdir -p "$SESS_DIR"
  date +%s > "${SESS_DIR}/last_active"
}

probe_timeout() {
  if (( CLIENT_TIMEOUT < 10 )); then
    printf '%s\n' "$CLIENT_TIMEOUT"
  else
    printf '10\n'
  fi
}

is_running() {
  [[ -d "$SESS_DIR" ]] || return 1
  local st
  st="$(timeout "$(probe_timeout)" "$BEAM_BIN" --root "$ROOT" --session-dir "$SESS_DIR" status </dev/null 2>/dev/null || true)"
  [[ "$st" == *'"state":"running"'* ]]
}

stop_daemon() {
  local stop_t=15
  if (( CLIENT_TIMEOUT < stop_t )); then
    stop_t="$CLIENT_TIMEOUT"
  fi
  if [[ -d "$SESS_DIR" ]]; then
    timeout "$stop_t" "$BEAM_BIN" --root "$ROOT" --session-dir "$SESS_DIR" stop </dev/null >/dev/null 2>&1 || true
  fi
  systemctl --user stop "$UNIT" >/dev/null 2>&1 || true
  systemctl --user reset-failed "$UNIT" >/dev/null 2>&1 || true
  for _ in $(seq 1 30); do
    if ! systemctl --user is-active --quiet "$UNIT" 2>/dev/null && ! pgrep -f "$SESS_DIR" >/dev/null 2>&1; then
      break
    fi
    sleep 0.1
  done
  if ! pgrep -f "$SESS_DIR" >/dev/null 2>&1; then
    rm -rf "$SESS_DIR" 2>/dev/null || true
  else
    rm -f "${SESS_DIR}/ready.log" "${SESS_DIR}/serve.err" "${SESS_DIR}/systemd.err" "${SESS_DIR}/runner.sh" 2>/dev/null || true
  fi
  if [[ -e "${ROOT}/.beam" ]] && ! git -C "$ROOT" ls-files --error-unmatch .beam >/dev/null 2>&1; then
    rm -rf "${ROOT}/.beam" 2>/dev/null || true
  fi
}

start_daemon() {
  local mem="$1"
  local idle_min="$2"
  local emit_json="${3:-1}"

  if is_running; then
    touch_activity
    if [[ "$emit_json" == "1" ]]; then
      echo "{\"status\":\"already_running\",\"root\":\"$ROOT\",\"session_dir\":\"$SESS_DIR\",\"unit\":\"$UNIT\"}"
    fi
    return 0
  fi

  exec 9>"$LOCK_FILE"
  if ! flock -w 30 9; then
    exec 9>&-
    echo "beam_bounded.sh: error: timed out waiting for start lock $LOCK_FILE" >&2
    return 1
  fi

  if is_running; then
    touch_activity
    exec 9>&-
    if [[ "$emit_json" == "1" ]]; then
      echo "{\"status\":\"already_running\",\"root\":\"$ROOT\",\"session_dir\":\"$SESS_DIR\",\"unit\":\"$UNIT\"}"
    fi
    return 0
  fi

  local min_avail_mib="${LEAN_BEAM_MIN_AVAIL_MIB:-18432}"
  local avail_mib
  avail_mib="$(awk '/MemAvailable:/ {printf "%d", $2/1024}' /proc/meminfo)"
  if [[ "${avail_mib:-0}" -lt "$min_avail_mib" ]]; then
    exec 9>&-
    echo "beam_bounded.sh: error: MemAvailable=${avail_mib} MiB < ${min_avail_mib} MiB; refusing to start lean-beam daemon" >&2
    return 1
  fi

  stop_daemon
  mkdir -p "$SESS_DIR"
  chmod 700 "$SESS_DIR" 2>/dev/null || true
  touch_activity
  local ready_log="${SESS_DIR}/ready.log"
  local err_log="${SESS_DIR}/serve.err"
  local sd_err="${SESS_DIR}/systemd.err"
  local runner="${SESS_DIR}/runner.sh"
  : > "$ready_log"
  : > "$err_log"
  : > "$sd_err"
  local idle_sec=$(( idle_min * 60 ))

  local q_base q_beam q_root q_sess q_ready q_err
  q_base="$(printf '%q' "$BASE_DIR")"
  q_beam="$(printf '%q' "$BEAM_BIN")"
  q_root="$(printf '%q' "$ROOT")"
  q_sess="$(printf '%q' "$SESS_DIR")"
  q_ready="$(printf '%q' "$ready_log")"
  q_err="$(printf '%q' "$err_log")"

  cat > "$runner" <<EOF
#!/usr/bin/env bash
set -euo pipefail
export BEAM_SESSION_ROOT=${q_base}
FIFO=${q_sess}/owner.fifo
rm -f "\$FIFO"
mkfifo "\$FIFO"
exec 3<>"\$FIFO"
${q_beam} --root ${q_root} --session-dir ${q_sess} serve <&3 >${q_ready} 2>${q_err} &
SPID=\$!
trap 'timeout 10 ${q_beam} --root ${q_root} --session-dir ${q_sess} stop </dev/null >/dev/null 2>&1 || true; exec 3>&- 2>/dev/null || true; wait "\$SPID" 2>/dev/null || true' EXIT TERM INT
while kill -0 "\$SPID" 2>/dev/null; do
  sleep 20
  if [[ ! -d ${q_root} ]]; then
    break
  fi
  now="\$(date +%s)"
  last="\$(cat ${q_sess}/last_active 2>/dev/null || echo "\$now")"
  if (( now - last >= ${idle_sec} )); then
    break
  fi
done
EOF
  chmod 700 "$runner"

  if ! systemd-run --user --unit="$UNIT" --collect \
    --property=Slice=leanqbe-builds.slice \
    -p "MemoryMax=${mem}" \
    -p OOMPolicy=kill \
    --property="WorkingDirectory=${ROOT}" \
    "$runner" 9>&- </dev/null >/dev/null 2>"$sd_err"; then
    exec 9>&-
    echo "beam_bounded.sh: error: systemd-run failed for $UNIT" >&2
    cat "$sd_err" >&2 || true
    stop_daemon
    return 1
  fi

  local i
  for i in $(seq 1 300); do
    if [[ -s "$ready_log" ]] && is_running; then
      exec 9>&-
      if [[ "$emit_json" == "1" ]]; then
        head -n 1 "$ready_log"
      fi
      return 0
    fi
    if (( i > 10 )) && ! systemctl --user is-active --quiet "$UNIT" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  exec 9>&-
  echo "beam_bounded.sh: error: lean-beam serve did not become ready" >&2
  cat "$sd_err" >&2 || true
  cat "$err_log" >&2 || true
  stop_daemon
  return 1
}

ensure_running() {
  if is_running; then
    touch_activity
    return 0
  fi
  local mem="${LEAN_BEAM_MEM:-24G}"
  local idle_min="${LEAN_BEAM_IDLE_MIN:-15}"
  echo "beam_bounded.sh: auto-starting daemon ($UNIT, mem=${mem})" >&2
  start_daemon "$mem" "$idle_min" 0
}

run_diag() {
  local max_diags="${LEAN_BEAM_DIAG_MAX:-30}"
  local scope="+all-diagnostics"
  local file=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --max)
        [[ $# -ge 2 ]] || { echo "beam_bounded.sh: error: --max requires an integer" >&2; return 2; }
        max_diags="$2"; shift 2 ;;
      --max=*)
        max_diags="${1#--max=}"; shift ;;
      --errors-only)
        scope=""; shift ;;
      +all-diagnostics)
        scope="+all-diagnostics"; shift ;;
      -h|--help)
        echo "Usage: scripts/beam_bounded.sh diag [--max N] [--errors-only] <file.lean>" >&2
        return 0 ;;
      -*)
        echo "beam_bounded.sh: error: unknown diag flag '$1'" >&2
        return 2 ;;
      *)
        if [[ -n "$file" ]]; then
          echo "beam_bounded.sh: error: diag expects a single <file.lean> argument" >&2
          return 2
        fi
        file="$1"; shift ;;
    esac
  done
  if [[ -z "$file" ]]; then
    echo "beam_bounded.sh: error: diag requires <file.lean>" >&2
    return 2
  fi
  if ! [[ "$max_diags" =~ ^[0-9]+$ ]]; then
    echo "beam_bounded.sh: error: --max must be a non-negative integer, got '$max_diags'" >&2
    return 2
  fi

  ensure_running
  touch_activity

  local tmp_dir out_json err_log sync_rc=0 py_rc=0
  tmp_dir="$(mktemp -d "${SESS_DIR}/diag.XXXXXX")"
  out_json="${tmp_dir}/out.json"
  err_log="${tmp_dir}/err.log"

  local -a sync_args=("$file")
  if [[ -n "$scope" ]]; then
    sync_args+=("$scope")
  fi

  BEAM_PROGRESS=0 timeout "$CLIENT_TIMEOUT" \
    "$BEAM_BIN" --root "$ROOT" --session-dir "$SESS_DIR" sync "${sync_args[@]}" \
    </dev/null >"$out_json" 2>"$err_log" || sync_rc=$?

  python3 -B - "$file" "$out_json" "$err_log" "$max_diags" "$sync_rc" "$CLIENT_TIMEOUT" <<'PY' || py_rc=$?
import json
import re
import sys

file_arg, out_path, err_path, max_str, rc_str, timeout_str = sys.argv[1:7]
max_diags = int(max_str)
sync_rc = int(rc_str)

DIAG_RE = re.compile(
    r"^beam(?:\[[^\]]*\])?: diagnostic (\S+?)(?: completionBlocking=true)? (.+?):(\d+):(\d+): (.*)$"
)
LAKE_PREFIXES = ("✔ [", "✖ [", "⚠ [", "ℹ [")
LAKE_VERBS = (
    " Ran ", " Running ",
    " Reused ", " Reusing ",
    " Replayed ", " Replaying ",
    " Unpacked ", " Unpacking ",
    " Fetched ", " Fetching ",
    " Built ", " Building ",
)

def condense(text: str, limit: int = 300) -> str:
    parts = [ln.strip() for ln in text.splitlines() if ln.strip()]
    joined = " / ".join(parts) if parts else text.strip()
    if len(joined) > limit:
        return joined[: limit - 3] + "..."
    return joined

def is_lake_progress(sev: str, line: int, col: int, msg: str) -> bool:
    if sev != "info" or line != 1 or col != 1:
        return False
    stripped = msg.lstrip()
    return stripped.startswith(LAKE_PREFIXES) and any(v in stripped for v in LAKE_VERBS)

with open(out_path, encoding="utf-8", errors="replace") as fh:
    raw_out = fh.read()
with open(err_path, encoding="utf-8", errors="replace") as fh:
    raw_err = fh.read()

streamed = []
seen = set()
other_err = []
for raw_line in raw_err.splitlines():
    m = DIAG_RE.match(raw_line)
    if m:
        sev, path, ln_s, col_s, msg = m.groups()
        ln, col = int(ln_s), int(col_s)
        if is_lake_progress(sev, ln, col, msg):
            continue
        cmsg = condense(msg)
        key = (path, ln, col, sev, cmsg)
        if key not in seen:
            seen.add(key)
            streamed.append((path, ln, col, sev, cmsg))
    elif raw_line.strip():
        other_err.append(raw_line.strip())

if sync_rc == 124:
    for line in other_err[:10]:
        print(line, file=sys.stderr)
    print(f"diag: {file_arg} TIMEOUT after {timeout_str}s", file=sys.stderr)
    sys.exit(124)

payload = None
for ln in reversed(raw_out.splitlines()):
    ln = ln.strip()
    if ln:
        try:
            payload = json.loads(ln)
            break
        except json.JSONDecodeError:
            pass

if not isinstance(payload, dict):
    for line in other_err[:15]:
        print(line, file=sys.stderr)
    print(f"diag: {file_arg} failed (exit={sync_rc}, no valid JSON)", file=sys.stderr)
    sys.exit(sync_rc or 1)

if not payload.get("ok"):
    err_obj = payload.get("error", {})
    code = err_obj.get("code", "error")
    msg = condense(str(err_obj.get("message", "")), 400)
    data = err_obj.get("data") or {}
    for bd in data.get("completion_blocking_diagnostics", []) or []:
        start = (bd.get("range") or {}).get("start") or {}
        ln = int(start.get("line", 0)) + 1
        col = int(start.get("character", 0)) + 1
        sev = bd.get("severity", "error")
        cmsg = condense(str(bd.get("message", "")))
        print(f"{file_arg}:{ln}:{col} [{sev}]: {cmsg}")
    print(f"diag: {file_arg} FAILED [{code}]: {msg}", file=sys.stderr)
    plan = data.get("recovery_plan") or []
    if plan:
        print("recovery_plan: " + "; then ".join(plan), file=sys.stderr)
    sys.exit(sync_rc or 1)

res = payload.get("result", {})
path = res.get("path", file_arg)
version = res.get("version", "?")
readiness = res.get("readiness") or {}
save_ready = readiness.get("save_ready", False)
counts = (res.get("diagnostics") or {}).get("counts") or {}
n_err = int(counts.get("error", 0))
n_warn = int(counts.get("warning", 0))
n_info = int(counts.get("information", 0))
n_hint = int(counts.get("hint", 0))

for bd in readiness.get("blocking_diagnostics") or []:
    start = (bd.get("range") or {}).get("start") or {}
    ln = int(start.get("line", 0)) + 1
    col = int(start.get("character", 0)) + 1
    sev = bd.get("severity", "error")
    cmsg = condense(str(bd.get("message", "")))
    key = (path, ln, col, sev, cmsg)
    if key not in seen:
        seen.add(key)
        streamed.append(key)

for bm in readiness.get("blocking_messages") or []:
    cmsg = condense(str(bm.get("message", "")))
    key = (path, 1, 1, "error", cmsg)
    if key not in seen:
        seen.add(key)
        streamed.append(key)

sev_rank = {"error": 0, "warning": 1, "info": 2, "information": 2, "hint": 3}
streamed.sort(key=lambda d: (sev_rank.get(d[3], 4), d[1], d[2]))

shown = streamed if max_diags == 0 else streamed[:max_diags]
for d_path, d_ln, d_col, d_sev, d_msg in shown:
    print(f"{d_path}:{d_ln}:{d_col} [{d_sev}]: {d_msg}")

if max_diags > 0 and len(streamed) > max_diags:
    omitted = len(streamed) - max_diags
    print(f"... ({omitted} more diagnostic(s) omitted; set LEAN_BEAM_DIAG_MAX=0 for all)")

extra = []
if n_info:
    extra.append(f"{n_info} info")
if n_hint:
    extra.append(f"{n_hint} hint")
extra_str = (", " + ", ".join(extra)) if extra else ""
ready_str = "true" if save_ready else "false"
print(f"diag: {path} (version={version}, save_ready={ready_str}): {n_err} error(s), {n_warn} warning(s){extra_str}")
sys.exit(sync_rc)
PY
  rm -rf "$tmp_dir"
  return "$py_rc"
}

case "$cmd" in
  start)
    MEM="${LEAN_BEAM_MEM:-24G}"
    IDLE_MIN="${LEAN_BEAM_IDLE_MIN:-15}"
    while [[ $# -gt 0 ]]; do
      case "$1" in
        -m|--mem)
          [[ $# -ge 2 ]] || { echo "beam_bounded.sh: error: $1 requires a size" >&2; exit 2; }
          MEM="$2"; shift 2 ;;
        --idle-min)
          [[ $# -ge 2 ]] || { echo "beam_bounded.sh: error: $1 requires minutes" >&2; exit 2; }
          IDLE_MIN="$2"; shift 2 ;;
        *)
          echo "beam_bounded.sh: error: unknown start flag: $1" >&2
          exit 2 ;;
      esac
    done
    start_daemon "$MEM" "$IDLE_MIN" 1
    ;;

  stop)
    stop_daemon
    echo "{\"status\":\"stopped\",\"root\":\"$ROOT\",\"session_dir\":\"$SESS_DIR\",\"unit\":\"$UNIT\"}"
    ;;

  status)
    exec timeout "$CLIENT_TIMEOUT" "$BEAM_BIN" --root "$ROOT" --session-dir "$SESS_DIR" status "$@"
    ;;

  diag)
    run_diag "$@"
    ;;

  sync|goals|run-at|hover|update|refresh|save|todo|definition|references|signature-help|document-symbols|workspace-symbols|run-at-handle)
    ensure_running
    touch_activity
    exec timeout "$CLIENT_TIMEOUT" "$BEAM_BIN" --root "$ROOT" --session-dir "$SESS_DIR" "$cmd" "$@"
    ;;

  close|close-save|run-with|run-with-linear|release|open-files|stats|doctor|cancel|recover)
    if is_running; then
      touch_activity
    fi
    exec timeout "$CLIENT_TIMEOUT" "$BEAM_BIN" --root "$ROOT" --session-dir "$SESS_DIR" "$cmd" "$@"
    ;;

  *)
    usage >&2
    exit 2
    ;;
esac
