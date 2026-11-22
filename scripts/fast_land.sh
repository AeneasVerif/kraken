#!/usr/bin/env bash
# Zero-rebuild fast landing script from a staging worktree into `main`.
# Usage:
#   scripts/fast_land.sh [--fast|--skip-tests] [--dry-run] <staging_worktree> <branch_or_commit>
set -uo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/fast_land.sh [--fast|--skip-tests] [--dry-run] <staging_worktree> <branch_or_commit>
  --fast, --skip-tests  Run scripts/check.sh only; skip parallel runtime test suites.
  --dry-run             Verify git state and print actions without mutating repo or running checks.
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

CHECK_TIMEOUT="${CHECK_TIMEOUT:-3600}"
TEST_TIMEOUT="${TEST_TIMEOUT:-1800}"
RSYNC_TIMEOUT="${RSYNC_TIMEOUT:-300}"

LOG_DIR=""
cleanup() {
  if [ -n "$LOG_DIR" ] && [ -d "$LOG_DIR" ]; then
    rm -rf "$LOG_DIR"
  fi
}
trap cleanup EXIT

[ -d "$STAGING" ] || { echo "fast_land: staging worktree not found: $STAGING" >&2; exit 2; }
STAGING="$(cd "$STAGING" && pwd)"

cur_branch="$(git symbolic-ref --short HEAD 2>/dev/null || true)"
[ "$cur_branch" = "main" ] || {
  echo "fast_land: must run on 'main' (currently '$cur_branch')" >&2
  exit 1
}

if [ -n "$(git status --porcelain)" ]; then
  echo "fast_land: 'main' working tree is dirty; commit or stash first" >&2
  git status --short >&2
  exit 1
fi

MAIN_SHA="$(git rev-parse HEAD)"
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
    --include='*.setup.json' --include='*.arts' --include='*.rsp' \
    --include='*.nobuild' --exclude='*' \
    "$src/" "$dst/" || return 1

  find "$dst" -type d -exec chmod u+rwx {} +
  find "$dst" \( -name '*.trace' -o -name '*.hash' -o -name '*.setup.json' \
    -o -name '*.arts' -o -name '*.rsp' -o -name '*.nobuild' \) \
    -exec chmod u+rw {} +
}

if [ "$MAIN_SHA" != "$TARGET_SHA" ]; then
  run_cmd git merge --ff-only "$TARGET_SHA" || exit 1
else
  echo "== fast_land: main already at $TARGET_SHA"
fi

STAGING_TREE="$(git -C "$STAGING" rev-parse 'HEAD^{tree}' 2>/dev/null || true)"
TARGET_TREE="$(git rev-parse "${TARGET_SHA}^{tree}")"
STAGING_DIRTY="$(git -C "$STAGING" status --porcelain 2>/dev/null || echo dirty)"

if [ -d "$STAGING/.lake/build" ]; then
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
else
  echo "== fast_land: skipping .lake/build rsync (missing $STAGING/.lake/build)"
fi

echo "== fast_land: running scripts/check.sh (CHECK_SCOPE=full)"
if [ "$DRY_RUN" -eq 1 ]; then
  echo "[dry-run] CHECK_SCOPE=full timeout $CHECK_TIMEOUT ./scripts/check.sh"
else
  CHECK_SCOPE=full timeout "$CHECK_TIMEOUT" ./scripts/check.sh || {
    echo "fast_land: scripts/check.sh failed (rc=$?)" >&2
    exit 1
  }
fi

if [ "$SKIP_TESTS" -eq 1 ]; then
  echo "== fast_land: --fast/--skip-tests set; skipping runtime test suites"
  exit 0
fi

if [ "$DRY_RUN" -eq 1 ]; then
  echo "[dry-run] prebuild extra kissat test targets & resolve QBE via scripts/ensure_qbe.sh"
  echo "[dry-run] SKIP_BUILD=1 unset OUT && parallel timeout $TEST_TIMEOUT:" \
    "./test/run.sh, ./test/arm64/run.sh, ./test/kissat/run.sh"
  exit 0
fi

unset OUT
LOG_DIR="$(mktemp -d "${TMPDIR:-/tmp}/fast-land-tests.XXXXXX")"

echo "== fast_land: warming extra test imports & resolving shared stock qbe"
timeout "$CHECK_TIMEOUT" lake build --wfail \
  LeanQbe.T.Examples.Kissat.Solver LeanQbe.T.Examples.Kissat.FullM3 \
  LeanQbe.T.PrintCpp LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Arm64.Targ \
  LeanQbeTest.T.KissatC0Test Kraken.X64.PrintATT Kraken.AArch64.Print \
  >"$LOG_DIR/prebuild.log" 2>&1 || {
  cat "$LOG_DIR/prebuild.log" >&2
  exit 1
}

if [ -z "${NOQBE:-}" ] && [ -z "${QBE:-}" ] && [ -x "$ROOT/scripts/ensure_qbe.sh" ]; then
  qbe_rc=0
  QBE_BIN="$("$ROOT/scripts/ensure_qbe.sh")" || qbe_rc=$?
  if [ "$qbe_rc" -eq 0 ] && [ -n "$QBE_BIN" ]; then
    export QBE="$QBE_BIN"
  elif [ "$qbe_rc" -ne 2 ]; then
    echo "fast_land: scripts/ensure_qbe.sh failed (rc=$qbe_rc)" >&2
    exit "$qbe_rc"
  fi
fi

echo "== fast_land: running test suites in parallel (logs in $LOG_DIR)"

suites=(run arm64 kissat)
cmds=("./test/run.sh" "./test/arm64/run.sh" "./test/kissat/run.sh")
pids=()

for i in "${!suites[@]}"; do
  s="${suites[$i]}"
  c="${cmds[$i]}"
  SKIP_BUILD=1 timeout "$TEST_TIMEOUT" "$c" >"$LOG_DIR/$s.log" 2>&1 &
  pids+=("$!")
done

fail=0
for i in "${!suites[@]}"; do
  s="${suites[$i]}"
  c="${cmds[$i]}"
  pid="${pids[$i]}"
  if wait "$pid"; then
    echo "PASS  $c"
  else
    rc=$?
    echo "FAIL  $c (rc=$rc)" >&2
    tail -n 60 "$LOG_DIR/$s.log" >&2 || true
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "== fast_land: ALL PASSED"
else
  echo "== fast_land: FAILED" >&2
fi
exit "$fail"
