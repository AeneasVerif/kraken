#!/usr/bin/env bash
# Zero-rebuild fast landing script from a staging worktree into `leanqbe/main` (or `main`).
# Usage:
#   scripts/fast_land.sh [--fast|--skip-tests] [--dry-run] <staging_worktree> <branch_or_commit>
set -uo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/fast_land.sh [--fast|--skip-tests] [--dry-run] <staging_worktree> <branch_or_commit>
  --fast, --skip-tests  Run scripts/check.sh only; skip parallel runtime test suites.
  --dry-run             Verify git state and print actions without mutating repo or running checks.
Env:
  LAND_BRANCH           Target branch name for validation / detached CAS update (default: leanqbe/main)
  CHECK_SCOPE           Passed to scripts/check.sh (default: auto)
  FAST_LAND_RSYNC=1     Opt in to legacy 6-pass rsync of .lake/build (default: Lake artifact cache)
EOF
}

SKIP_TESTS=0
DRY_RUN=0
POSITIONAL=()
while [ $# -gt 0 ]; do
  case "$1" in
    --fast|--skip-tests) SKIP_TESTS=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "fast_land: unknown option: $1" >&2; usage >&2; exit 2 ;;
    *) POSITIONAL+=("$1"); shift ;;
  esac
done

if [ "${#POSITIONAL[@]}" -ne 2 ]; then
  usage >&2
  exit 2
fi

STAGING="${POSITIONAL[0]}"
TARGET="${POSITIONAL[1]}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

# shellcheck source=scripts/common.sh
source "$ROOT/scripts/common.sh"
leanqbe_export_lake_cache
leanqbe_register_traps

CHECK_TIMEOUT="${CHECK_TIMEOUT:-3600}"
TEST_TIMEOUT="${TEST_TIMEOUT:-1800}"
RSYNC_TIMEOUT="${RSYNC_TIMEOUT:-300}"

LOG_DIR=""

[ -d "$STAGING" ] || { echo "fast_land: staging worktree not found: $STAGING" >&2; exit 2; }
STAGING="$(cd "$STAGING" && pwd)"

LAND_BRANCH="${LAND_BRANCH:-leanqbe/main}"
cur_branch="$(git symbolic-ref --short HEAD 2>/dev/null || true)"
DETACHED_MODE=0
if [ -z "$cur_branch" ]; then
  DETACHED_MODE=1
  echo "== fast_land: running on detached HEAD (will CAS-update refs/heads/$LAND_BRANCH)"
elif [ "$cur_branch" != "$LAND_BRANCH" ] && [ "$cur_branch" != "main" ]; then
  echo "fast_land: must run on '$LAND_BRANCH', 'main', or detached HEAD (currently '$cur_branch')" >&2
  exit 1
fi

if [ -n "$(git status --porcelain)" ]; then
  echo "fast_land: working tree is dirty; commit or stash first" >&2
  git status --short >&2
  exit 1
fi

MAIN_SHA="$(git rev-parse HEAD)"
if [ "$DETACHED_MODE" -eq 1 ]; then
  REF_SHA="$(git rev-parse --verify "refs/heads/$LAND_BRANCH^{commit}" 2>/dev/null || true)"
  if [ -n "$REF_SHA" ] && [ "$REF_SHA" != "$MAIN_SHA" ]; then
    echo "fast_land: detached HEAD ($MAIN_SHA) != refs/heads/$LAND_BRANCH ($REF_SHA)" >&2
    exit 1
  fi
fi
TARGET_SHA="$(git rev-parse --verify "${TARGET}^{commit}" 2>/dev/null)" || {
  echo "fast_land: cannot resolve target commit: $TARGET" >&2
  exit 1
}

if git merge-base --is-ancestor "$MAIN_SHA" "$TARGET_SHA"; then
  echo "== fast_land: $TARGET ($TARGET_SHA) fast-forwards main ($MAIN_SHA)"
else
  echo "fast_land: main ($MAIN_SHA) is not an ancestor of $TARGET ($TARGET_SHA)" >&2
  if git merge-tree --write-tree "$MAIN_SHA" "$TARGET_SHA" >/dev/null 2>&1; then
    echo "fast_land: merge/rebase onto main would be clean; rebase staging branch first" >&2
  else
    echo "fast_land: merge/rebase onto main has conflicts:" >&2
    git merge-tree --write-tree "$MAIN_SHA" "$TARGET_SHA" >&2 || true
  fi
  exit 1
fi

run_cmd() {
  if [ "$DRY_RUN" -eq 1 ]; then
    echo "[dry-run] $*"
  else
    "$@"
  fi
}

sync_warm_build() {
  local src="${1%/}"
  local dst="${2%/}"
  mkdir -p "$dst"
  find "$dst" -type d -exec chmod u+wx {} + 2>/dev/null || true
  find "$dst" \( -name '*.trace' -o -name '*.hash' -o -name '*.setup.json' \
    -o -name '*.arts' -o -name '*.rsp' -o -name '*.nobuild' \) \
    -exec chmod u+w {} + 2>/dev/null || true

  timeout "$RSYNC_TIMEOUT" rsync -a --delete \
    --exclude='*.trace' --exclude='*.hash' --exclude='*.setup.json' \
    --exclude='*.arts' --exclude='*.rsp' --exclude='*.nobuild' \
    --link-dest="$src" "$src/" "$dst/" || return 1

  find "$dst" \( -name '*.trace' -o -name '*.hash' -o -name '*.setup.json' \
    -o -name '*.arts' -o -name '*.rsp' -o -name '*.nobuild' \) \
    -delete 2>/dev/null || true

  timeout "$RSYNC_TIMEOUT" rsync -a \
    --include='*/' --include='*.trace' --include='*.hash' \
    --include='*.arts' --include='*.rsp' \
    --include='*.nobuild' --exclude='*' \
    "$src/" "$dst/" || return 1

  find "$dst" -type d -exec chmod u+rwx {} +
  find "$dst" \( -name '*.trace' -o -name '*.hash' -o -name '*.setup.json' \
    -o -name '*.arts' -o -name '*.rsp' -o -name '*.nobuild' \) \
    -exec chmod u+rw {} +
}

if [ "$MAIN_SHA" != "$TARGET_SHA" ]; then
  if [ "$DETACHED_MODE" -eq 1 ]; then
    run_cmd git checkout --detach "$TARGET_SHA" || exit 1
    run_cmd git update-ref "refs/heads/$LAND_BRANCH" "$TARGET_SHA" "$MAIN_SHA" || exit 1
  else
    run_cmd git merge --ff-only "$TARGET_SHA" || exit 1
  fi
else
  echo "== fast_land: $LAND_BRANCH already at $TARGET_SHA"
fi

STAGING_TREE="$(git -C "$STAGING" rev-parse 'HEAD^{tree}' 2>/dev/null || true)"
TARGET_TREE="$(git rev-parse "${TARGET_SHA}^{tree}")"
STAGING_DIRTY="$(git -C "$STAGING" status --porcelain 2>/dev/null || echo dirty)"

# Prefer Lake 5.0 cross-worktree artifact cache (zero rsync of 30k .olean/.trace files).
# Only hardlink-seed executables unless FAST_LAND_RSYNC=1 is explicitly requested.
if [ "${FAST_LAND_RSYNC:-0}" = "1" ] && [ -d "$STAGING/.lake/build" ]; then
  if [ -z "$STAGING_DIRTY" ] && [ "$STAGING_TREE" = "$TARGET_TREE" ]; then
    echo "== fast_land: syncing warm .lake/build (exact tree match) from $STAGING"
  else
    echo "== fast_land: syncing warm .lake/build (partial/trace-checked) from $STAGING"
  fi
  if [ "$DRY_RUN" -eq 1 ]; then
    echo "[dry-run] sync_warm_build $STAGING/.lake/build $ROOT/.lake/build"
  else
    sync_warm_build "$STAGING/.lake/build" "$ROOT/.lake/build" || exit 1
  fi
elif [ -d "$STAGING/.lake/build/bin" ]; then
  if [ "$DRY_RUN" -eq 1 ]; then
    echo "[dry-run] hardlink-seed .lake/build/bin from $STAGING (LAKE_ARTIFACT_CACHE=$LAKE_ARTIFACT_CACHE)"
  else
    mkdir -p "$ROOT/.lake/build/bin"
    rsync -a --link-dest="$STAGING/.lake/build/bin" \
      "$STAGING/.lake/build/bin/" "$ROOT/.lake/build/bin/" || true
  fi
else
  echo "== fast_land: relying on Lake artifact cache (LAKE_ARTIFACT_CACHE=$LAKE_ARTIFACT_CACHE)"
fi

LAND_CHECK_SCOPE="${CHECK_SCOPE:-auto}"
echo "== fast_land: running scripts/check.sh (CHECK_SCOPE=$LAND_CHECK_SCOPE, CHECK_BASE=$MAIN_SHA)"
if [ "$DRY_RUN" -eq 1 ]; then
  echo "[dry-run] CHECK_BASE=$MAIN_SHA CHECK_SCOPE=$LAND_CHECK_SCOPE timeout $CHECK_TIMEOUT ./scripts/check.sh"
else
  CHECK_BASE="$MAIN_SHA" CHECK_SCOPE="$LAND_CHECK_SCOPE" timeout "$CHECK_TIMEOUT" ./scripts/check.sh || {
    echo "fast_land: scripts/check.sh failed (rc=$?)" >&2
    exit 1
  }
fi

if [ "$SKIP_TESTS" -eq 1 ]; then
  echo "== fast_land: --fast/--skip-tests set; skipping runtime test suites"
  exit 0
fi

# Path-gated suite selection (skips all runtime suites on proof-only/doc-only diffs!)
mapfile -t cmds < <(timeout 30 python3 -B "$ROOT/scripts/select_tests.py" --root "$ROOT" "$MAIN_SHA" "$TARGET_SHA")
if [ "${#cmds[@]}" -eq 0 ]; then
  echo "== fast_land: proof-only/doc-only diff (0 runtime suites needed) — ALL PASSED"
  exit 0
fi

if [ "$DRY_RUN" -eq 1 ]; then
  echo "[dry-run] selected runtime suites (${#cmds[@]}): ${cmds[*]}"
  exit 0
fi

unset OUT
LOG_DIR="$(mktemp -d "${TMPDIR:-/tmp}/fast-land-tests.XXXXXX")"
_LEANQBE_CLEANUP_PATHS+=("$LOG_DIR")

needs_qbe=0
needs_kissat_warm=0
for c in "${cmds[@]}"; do
  case "$c" in
    "./test/run.sh"|"./test/arm64/run.sh"|"./test/t_qbe/run.sh"|"./test/lrc/run.sh"|"./test/lcnf/run.sh")
      needs_qbe=1 ;;
    "./test/kissat/run.sh")
      needs_kissat_warm=1 ;;
  esac
done

if [ "$needs_kissat_warm" -eq 1 ]; then
  echo "== fast_land: warming extra kissat test imports"
  run_cgroup --mem "${CHECK_MEM_MAX:-48G}" --unit-prefix leanqbe-land \
    --timeout "$CHECK_TIMEOUT" --log "$LOG_DIR/prebuild.log" -- \
    env "LEAN_NUM_THREADS=${LAKE_JOBS:-${LEAN_NUM_THREADS:-6}}" lake build --wfail \
    LeanQbe.T.Examples.Kissat.Solver LeanQbe.T.Examples.Kissat.FullM3 \
    LeanQbe.T.PrintCpp LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Arm64.Targ \
    LeanQbeTest.T.KissatC0Test Kraken.X64.PrintATT Kraken.AArch64.Print \
    || { cat "$LOG_DIR/prebuild.log" >&2; exit 1; }
fi

if [ "$needs_qbe" -eq 1 ] && [ -z "${NOQBE:-}" ] && [ -z "${QBE:-}" ] && [ -x "$ROOT/scripts/ensure_qbe.sh" ]; then
  qbe_rc=0
  QBE_BIN="$("$ROOT/scripts/ensure_qbe.sh")" || qbe_rc=$?
  if [ "$qbe_rc" -eq 0 ] && [ -n "$QBE_BIN" ]; then
    export QBE="$QBE_BIN"
  elif [ "$qbe_rc" -ne 2 ]; then
    echo "fast_land: scripts/ensure_qbe.sh failed (rc=$qbe_rc)" >&2
    exit "$qbe_rc"
  fi
fi

echo "== fast_land: running ${#cmds[@]} selected runtime suite(s) in parallel (logs in $LOG_DIR): ${cmds[*]}"

pids=()
for i in "${!cmds[@]}"; do
  c="${cmds[$i]}"
  read -ra argv <<<"$c"
  if [ "$LAND_CHECK_SCOPE" = "full" ]; then
    SKIP_BUILD=1 timeout "$TEST_TIMEOUT" "${argv[@]}" >"$LOG_DIR/suite_${i}.log" 2>&1 &
  else
    timeout "$TEST_TIMEOUT" "${argv[@]}" >"$LOG_DIR/suite_${i}.log" 2>&1 &
  fi
  pids+=("$!")
done

fail=0
for i in "${!cmds[@]}"; do
  c="${cmds[$i]}"
  pid="${pids[$i]}"
  if wait "$pid"; then
    echo "PASS  $c"
  else
    rc=$?
    echo "FAIL  $c (rc=$rc)" >&2
    tail -n 60 "$LOG_DIR/suite_${i}.log" >&2 || true
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "== fast_land: ALL PASSED"
else
  echo "== fast_land: FAILED" >&2
fi
exit "$fail"
