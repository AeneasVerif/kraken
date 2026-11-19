#!/usr/bin/env bash
# Every check of the repository in one command. Run from anywhere: scripts/all.sh
#
#   scripts/check.sh         build with warnings as errors, sorry and native-tactic scan, import
#                            closures, axiom audit
#   test/run.sh              x64 litmus tests: leanqbe and stock QBE
#   test/arm64/run.sh        AArch64 litmus tests under qemu: leanqbe-arm64 and stock QBE
#   test/cpp/run.sh          C++20 PrintCpp differential and Rule A6 trap-default tests
#   tool/test_lrat_check.sh  lrat_check: unit, command-line and differential tests
#   bench/run.sh             benchmark table; every row must print the C baseline's result hashes
#   test/c0/run.sh           C0 frontend V1 layout, C99/C++20 differential & 111 probe tests
#   test/t_lrat/run.sh       typed-IR LRAT bytes checker C++20 differential & ASan/UBSan tests
#   test/t_bignum/run.sh     typed-IR bignum x64 + AArch64 native differential tests
#   test/t_chacha/run.sh     typed-IR ChaCha20 x64 + AArch64 RFC 8439 & differential tests
#   test/t_qbe/run.sh        typed-IR PrintQbe stock QBE (x64 + arm64) round-trip tests
#   test/lrc/run.sh          Lean λRC / Lean.IR -> LeanQbe.T C++/x64/arm64/QBE differential tests
#
# Runs the twelve scripts in this order, the later ones also after a failure, then prints one line
# per script, `PASS` or `FAIL`. A script passes iff it exits 0: all.sh does not read its output.
# The exit code of all.sh is 0 iff all twelve passed.
#
# There is no timeout here: the twelve scripts run their commands under `timeout`. For one bound on
# the whole run, put all.sh under an outer `timeout`, as with the scripts themselves; when that
# expires, the command that is running goes on until it ends or its own `timeout` expires.
#
# The scripts get the caller's environment (QBE, QBE_SRC, CC_AARCH64, BUILD_TIMEOUT, …), with two
# exceptions: OUT is unset, so that each script makes an output directory of its own, and NOQBE is
# refused, because it would skip the stock-QBE half of the litmus tests.
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 2
[ -z "${NOQBE:-}" ] ||
  { echo "all.sh: NOQBE is set, which skips the stock-QBE half of the litmus tests; unset it" >&2; exit 2; }
unset OUT

verdicts=()
failed=0
for s in scripts/check.sh test/run.sh test/arm64/run.sh test/cpp/run.sh tool/test_lrat_check.sh bench/run.sh test/c0/run.sh test/t_lrat/run.sh test/t_bignum/run.sh test/t_chacha/run.sh test/t_qbe/run.sh test/lrc/run.sh; do
  echo "== all.sh: $s"
  if "./$s"; then verdicts+=("PASS  $s"); else verdicts+=("FAIL  $s (exit code $?)"); failed=1; fi
done
echo "== all.sh: verdicts"
printf '%s\n' "${verdicts[@]}"
exit $failed
