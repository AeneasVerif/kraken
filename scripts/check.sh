#!/usr/bin/env bash
# lean-qbe quality gate. Run from anywhere: scripts/check.sh
#
#  1. Builds every library and both executables (`leanqbe`, `leanqbe-arm64`) with warnings as errors
#     (`lake build --wfail`).
#  2. Fails on any `sorry` (build log, and `sorryAx` in any axiom report), and on `bv_decide`,
#     `native_decide` and friends anywhere in a tracked .lean file (native axioms).
#  3. Checks import closures: the generic `LeanQbe` root imports neither `Kraken.X64` nor
#     `Kraken.AArch64`, and every module file under `LeanQbe/` is reachable from its library root
#     (`LeanQbe/Amd64/*` and `LeanQbe/Examples/Litmus*` from `LeanQbeAmd64`, `LeanQbe/Arm64/*` from `LeanQbeArm64`, the rest from
#     `LeanQbe`), so that step 1 really built it. Only files known to git are checked.
#  4. Axiom audit: `#print axioms` for every theorem listed in scripts/headline.txt, plus every
#     `#print axioms` already in the build log (any module that step 1 builds, for example a test
#     under LeanQbeTest/). Allowed: propext, Classical.choice, Quot.sound. A report that is not one
#     complete line fails: Lean breaks a long report over several lines, and then it cannot be read.
#     So does a headline theorem without a report, and a headline.txt that is missing or lists none.
#
# Every command runs under `timeout`. Exit code 0 iff all checks pass.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BUILD_TIMEOUT="${BUILD_TIMEOUT:-3600}"
LEAN_TIMEOUT="${LEAN_TIMEOUT:-600}"
TARGETS=(LeanQbe LeanQbeAmd64 LeanQbeArm64 LeanQbeTest leanqbe leanqbe-arm64)
ALLOWED="propext Classical.choice Quot.sound"

TMP="$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-check.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
fail=0
err() { echo "FAIL: $*"; fail=1; }

echo "== 1. build (warnings as errors): ${TARGETS[*]}"
timeout "$BUILD_TIMEOUT" lake build --wfail "${TARGETS[@]}" >"$TMP/build.log" 2>&1
rc=$?
grep -E '^(✖|error|warning)|warning:|error:' "$TMP/build.log" | head -100
tail -n 1 "$TMP/build.log"
[ $rc -eq 0 ] || err "lake build exited with $rc (124 = timeout); full log: rerun 'lake build --wfail ${TARGETS[*]}'"

echo "== 2. sorry"
if grep -n "declaration uses 'sorry'\|declaration uses \`sorry\`\|sorryAx" "$TMP/build.log"; then
  err "sorry in the build"
fi

echo "== 2b. native-code tactics (their axioms Lean.ofReduceBool etc. fail the bar, even off-headline)"
git ls-files -z '*.lean' ':(exclude)Kraken' ':(exclude)Kraken*.lean' ':(exclude)Att2Intel.lean' ':(exclude)Bedrock2C.lean' >"$TMP/lean-files" || err "git ls-files failed; steps 2b and 3 check only the files known to git"
# A line printed here is a failure whatever the commands exit with (grep: 2 if a tracked file is
# missing from the working tree; xargs: 123 if it runs grep twice and one run finds nothing), so
# this one pipeline runs without `pipefail`.
if (set +o pipefail; xargs -0 grep -HnE '\b(bv_decide|native_decide)\b|decide \+native|ofReduceBool|ofReduceNat' <"$TMP/lean-files" 2>/dev/null \
    | grep -vE '^[^:]+:[0-9]+:\s*--'); then
  err "native-code tactic in a tracked .lean file"
fi

echo "== 3. import closures"
closure() { # $1 = root module; prints the module names in its import closure
  cat >"$TMP/Closure_$1.lean" <<EOF
import Lean
import $1
open Lean in
#eval show CoreM Unit from do
  for n in (← getEnv).header.moduleNames do
    IO.println s!"MOD {n}"
EOF
  timeout "$LEAN_TIMEOUT" lake env lean "$TMP/Closure_$1.lean" 2>&1 | sed -n 's/^MOD //p'
}
for r in LeanQbe LeanQbeAmd64 LeanQbeArm64; do closure "$r" | sort >"$TMP/closure_$r.txt"; done
if grep -E '^Kraken\.(X64|AArch64)(\.|$)' "$TMP/closure_LeanQbe.txt"; then
  err "the generic LeanQbe imports an architecture (modules above)"
fi
if grep -q '^LeanQbe$' "$TMP/closure_LeanQbe.txt"; then :; else err "could not compute the closure of LeanQbe"; fi
while IFS= read -r f; do
  m="${f%.lean}"; m="${m//\//.}"
  case "$m" in
    LeanQbe.Amd64.*|LeanQbe.Examples.Litmus*) r=LeanQbeAmd64 ;;
    LeanQbe.Arm64.*) r=LeanQbeArm64 ;;
    *) r=LeanQbe ;;
  esac
  grep -qx "$m" "$TMP/closure_$r.txt" || err "$f is not imported by the root $r.lean (so it is not built)"
done < <(git ls-files --cached 'LeanQbe/*.lean' 'LeanQbe/**/*.lean' | sort -u)

echo "== 4. axiom audit"
# Build log: every `#print axioms` that the build printed.
grep -E "depends on axioms|does not depend on any axioms" "$TMP/build.log" >"$TMP/axioms.txt" || true
# Headline theorems: lines `<Module> <constant>` in scripts/headline.txt, grouped by module so that
# x64 and AArch64 modules are never imported together.
n=0
if [ -f scripts/headline.txt ]; then
  for mod in $(grep -vE '^\s*(#|$)' scripts/headline.txt | awk '{print $1}' | sort -u); do
    n=$((n + 1))
    f="$TMP/Audit_$n.lean"
    echo "import $mod" >"$f"
    grep -vE '^\s*(#|$)' scripts/headline.txt | awk -v m="$mod" '$1 == m {print "#print axioms " $2}' >>"$f"
    if ! timeout "$LEAN_TIMEOUT" lake env lean "$f" >"$TMP/audit_$n.out" 2>&1; then
      cat "$TMP/audit_$n.out"; err "axiom audit of $mod failed to elaborate"
    fi
    sed 's/^/headline: /' "$TMP/audit_$n.out"
    cat "$TMP/audit_$n.out" >>"$TMP/axioms.txt"
  done
fi
[ $n -gt 0 ] || err "no headline theorem to audit: scripts/headline.txt is missing or lists none"
# Every headline theorem must have one complete report: the loop below fails on the lines that are
# not a complete report, and this count fails if a report is missing.
want="$(grep -vcE '^\s*(#|$)' scripts/headline.txt 2>/dev/null)"; want="${want:-0}"
got="$(cat "$TMP"/audit_*.out 2>/dev/null | grep -cE 'depends on axioms: \[.*\]$|does not depend on any axioms$')"
echo "$(grep -c . "$TMP/axioms.txt") lines of axiom reports; $got complete reports for $want headline theorems"
[ "$got" -eq "$want" ] || err "$got complete one-line axiom reports for $want headline theorems"
while IFS= read -r line; do
  case "$line" in
    *"does not depend on any axioms") continue ;;
    *"depends on axioms: ["*"]") ;;
    *) err "axiom report is not one complete line (Lean breaks a long report over lines), so its axioms cannot be read: $line"; continue ;;
  esac
  axs="$(sed -n 's/.*depends on axioms: \[\(.*\)\].*/\1/p' <<<"$line" | tr -d ' ' | tr ',' ' ')"
  for a in $axs; do
    case " $ALLOWED " in *" $a "*) ;; *) err "disallowed axiom $a: $line" ;; esac
  done
done <"$TMP/axioms.txt"

if [ $fail -eq 0 ]; then echo "== check.sh: ALL PASSED"; else echo "== check.sh: FAILED"; fi
exit $fail
