#!/usr/bin/env bash
# Every check of the repository in one command. Run from anywhere: scripts/all.sh
#
#   scripts/check.sh         build with warnings as errors, sorry and native-tactic scan, import
#                            closures, axiom audit
#   test/run.sh              x64 litmus tests: leanqbe and stock QBE
#   test/arm64/run.sh        AArch64 litmus tests under qemu: leanqbe-arm64 and stock QBE
#   test/cpp/run.sh          C++20 PrintCpp differential and trap-default tests
#   tool/test_lrat_check.sh  lrat_check: unit, command-line and differential tests
#   bench/run.sh             benchmark table; every row must print the C baseline's result hashes
#   test/c0/run.sh           C0 frontend layout, C99/C++20 differential & 111 probe tests
#   test/t_lrat/run.sh       typed-IR LRAT bytes checker C++20 differential & ASan/UBSan tests
#   test/t_bignum/run.sh     typed-IR bignum x64 + AArch64 native differential tests
#   test/t_chacha/run.sh     typed-IR ChaCha20 x64 + AArch64 RFC 8439 & differential tests
#   test/t_qbe/run.sh        typed-IR PrintQbe stock QBE (x64 + arm64) round-trip tests
#   test/lrc/run.sh          Lean λRC / Lean.IR -> LeanQbe.T C++/x64/arm64/QBE differential tests
#   test/kissat/run.sh       Kissat C0 SAT solver differential & native tests
#   test/lcnf/run.sh         LeanLCNF impure LCNF -> LeanQbe.T C++/x64/arm64 differential & bench tests
#
# Runs scripts/check.sh first, then runs the remaining thirteen scripts (sequentially when
# ALL_JOBS=1, or up to ALL_JOBS in parallel when ALL_JOBS > 1, each with isolated OUT and
# shared read-only QBE). Prints one line per script (`PASS` or `FAIL`) and exits 0 iff all
# fourteen passed.
#
# There is no timeout here: the fourteen scripts run their commands under `timeout`. For one bound on
# the whole run, put all.sh under an outer `timeout`, as with the scripts themselves.
#
# Environment knobs:
#   ALL_JOBS=1|4|...   Parallel jobs for the 13 post-check test suites (default: 1).
#   SKIP_CHECK=1       Skip running scripts/check.sh first (e.g. if caller just ran it).
#   SKIP_BUILD=1       Forwarded to test scripts (set automatically when check.sh succeeds).
#   QBE, QBE_SRC, CC_AARCH64, BUILD_TIMEOUT, ...
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2
# shellcheck source=scripts/common.sh
source "$ROOT/scripts/common.sh"
[ -z "${NOQBE:-}" ] ||
  { echo "all.sh: NOQBE is set, which skips the stock-QBE half of the litmus tests; unset it" >&2; exit 2; }
unset OUT

ALL_JOBS="${ALL_JOBS:-1}"
SKIP_CHECK="${SKIP_CHECK:-0}"
USER_SKIP_BUILD="${SKIP_BUILD+set}"

TEST_SCRIPTS=(
  test/run.sh
  test/arm64/run.sh
  test/cpp/run.sh
  tool/test_lrat_check.sh
  bench/run.sh
  test/c0/run.sh
  test/t_lrat/run.sh
  test/t_bignum/run.sh
  test/t_chacha/run.sh
  test/t_qbe/run.sh
  test/lrc/run.sh
  test/kissat/run.sh
  test/lcnf/run.sh
)

verdicts=()
failed=0

if [ "$SKIP_CHECK" != "1" ]; then
  echo "== all.sh: scripts/check.sh"
  if CHECK_SCOPE="${CHECK_SCOPE:-full}" ./scripts/check.sh; then
    verdicts+=("PASS  scripts/check.sh")
    if [ -z "$USER_SKIP_BUILD" ] && [ "${CHECK_SCOPE:-full}" = "full" ]; then
      export SKIP_BUILD=1
    fi
  else
    rc=$?
    verdicts+=("FAIL  scripts/check.sh (exit code $rc)")
    failed=1
  fi
fi

# Warm stock QBE once into shared read-only cache before parallel suites
if [ -z "${QBE:-}" ]; then
  qbe_rc=0
  QBE="$("$ROOT/scripts/ensure_qbe.sh")" || qbe_rc=$?
  if [ "$qbe_rc" -eq 0 ] && [ -n "$QBE" ]; then
    export QBE
  elif [ "$qbe_rc" -ne 2 ]; then
    echo "all.sh: failed to build stock QBE (rc=$qbe_rc)" >&2
    failed=1
  fi
fi

if [ "$ALL_JOBS" -le 1 ]; then
  for s in "${TEST_SCRIPTS[@]}"; do
    echo "== all.sh: $s"
    if (unset OUT; "./$s"); then
      verdicts+=("PASS  $s")
    else
      rc=$?
      verdicts+=("FAIL  $s (exit code $rc)")
      failed=1
    fi
  done
else
  LOG_DIR="$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-all.XXXXXX")"
  trap 'rm -rf "$LOG_DIR"' EXIT
  echo "== all.sh: ${#TEST_SCRIPTS[@]} suites (ALL_JOBS=$ALL_JOBS, SKIP_BUILD=${SKIP_BUILD:-0})"
  for i in "${!TEST_SCRIPTS[@]}"; do
    s="${TEST_SCRIPTS[$i]}"
    leanqbe_throttle_jobs "$ALL_JOBS"
    (
      unset OUT
      rc=0
      "./$s" >"$LOG_DIR/$i.log" 2>&1 || rc=$?
      echo "$rc" >"$LOG_DIR/$i.rc"
    ) &
  done
  wait
  for i in "${!TEST_SCRIPTS[@]}"; do
    s="${TEST_SCRIPTS[$i]}"
    rc="$(cat "$LOG_DIR/$i.rc" 2>/dev/null || echo 1)"
    if [ "$rc" -eq 0 ]; then
      echo "PASS  $s"
      verdicts+=("PASS  $s")
    else
      echo "FAIL  $s (exit code $rc)"
      cat "$LOG_DIR/$i.log" >&2 || true
      verdicts+=("FAIL  $s (exit code $rc)")
      failed=1
    fi
  done
fi

echo "== all.sh: verdicts"
printf '%s\n' "${verdicts[@]}"
exit $failed
