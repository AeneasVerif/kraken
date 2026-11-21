#!/usr/bin/env bash
# Build a native `kissat-leanqbe` binary from the verified LeanQbe Kissat solver.
#
#   bash bench/kissat/build_solver.sh [--module Full|FullFast|FullM3|Plain] [--arch x64|arm64] \
#     [--inline-max <N>] [-o <output_bin>]
#
# 1. `lake build`s the solver module `LeanQbe.T.Examples.Kissat.<Module>` and the code generator
#    (skipped when `STAGE_LEAN_PATH` is set).
# 2. Applies `Module.optInline <N>` (default `40`; `0` disables) and compiles `<Module>Module`
#    with `LeanQbe.T.compile` for x86-64 (`Kraken.X64.PrintATT`) or AArch64
#    (`Kraken.AArch64.Print`) into a `.s` file.
# 3. Links that assembly with bench/kissat/kissat_cli.c into <output_bin>.
#
# Defaults: --module Full --arch x64 --inline-max 40 -o /tmp/kissat-leanqbe-<module>[-arm64]. All
# intermediate files live in a temporary directory removed on exit; the repository is never written
# to except for Lake's own .lake/ build cache. For --arch arm64 on a non-AArch64 host the binary
# is built with aarch64-linux-gnu-gcc (override with CC=...) and runs under qemu-aarch64, e.g.
#   qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-full-arm64 input.cnf
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CALLER_PWD="$PWD"
MODULE=Full
ARCH=x64
INLINE_MAX="${INLINE_MAX:-40}"
OUTPUT=""

usage() {
  echo "usage: bash bench/kissat/build_solver.sh" \
    "[--module Full|FullFast|FullM3|Plain] [--arch x64|arm64] [--inline-max <N>] [-o <output_bin>]"
}

while [ $# -gt 0 ]; do
  case "$1" in
    --module|--arch|--inline-max|-o)
      [ $# -ge 2 ] || { echo "ERROR: $1 requires an argument" >&2; usage >&2; exit 2; }
      case "$1" in
        --module) MODULE="$2" ;;
        --arch) ARCH="$2" ;;
        --inline-max) INLINE_MAX="$2" ;;
        -o) OUTPUT="$2" ;;
      esac
      shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "ERROR: unknown argument '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

case "${MODULE,,}" in
  full) MODULE=Full; EXPR=LeanQbe.T.Examples.Kissat.Full.fullModule ;;
  fullfast) MODULE=FullFast; EXPR=LeanQbe.T.Examples.Kissat.FullFast.fastModule ;;
  fullm3|m3) MODULE=FullM3; EXPR=LeanQbe.T.Examples.Kissat.FullM3.m3Module ;;
  plain) MODULE=Plain; EXPR=LeanQbe.T.Examples.Kissat.Plain.plainModule ;;
  *) echo "ERROR: unknown module '$MODULE' (expected Full | FullFast | FullM3 | Plain)" >&2; exit 2 ;;
esac
case "${ARCH,,}" in
  x64|amd64|x86_64) ARCH=x64; SUFFIX="" ;;
  arm64|aarch64) ARCH=arm64; SUFFIX="-arm64" ;;
  *) echo "ERROR: unknown arch '$ARCH' (expected x64 | arm64)" >&2; exit 2 ;;
esac
OUTPUT="${OUTPUT:-/tmp/kissat-leanqbe-${MODULE,,}$SUFFIX}"
case "$OUTPUT" in /*) ;; *) OUTPUT="$CALLER_PWD/$OUTPUT" ;; esac

if [ "$ARCH" = x64 ]; then
  CC="${CC:-gcc}"
  CFLAGS_ARCH=(-no-pie)
  IMPORTS="import LeanQbe.T.Amd64.Targ
import Kraken.X64.PrintATT"
  OPENS="open LeanQbe.T LeanQbe.T.Amd64"
  TGT=x64Target; LEGAL=x64LegalTarget
  PRINT='fun c => Kraken.X64.toATT c ++ "\n"'
  LAKE_EXTRA=(LeanQbe.T.Amd64.Targ Kraken.X64.PrintATT)
else
  if [ "$(uname -m)" = aarch64 ]; then CC="${CC:-gcc}"; else CC="${CC:-aarch64-linux-gnu-gcc}"; fi
  CFLAGS_ARCH=()
  IMPORTS="import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print"
  OPENS="open LeanQbe.T LeanQbe.T.Arm64"
  TGT=armTarget; LEGAL=armLegalTarget
  PRINT='fun c => ".p2align 2\n" ++ String.intercalate "\n" (c.map Kraken.AArch64.Print.directive) ++ "\n"'
  LAKE_EXTRA=(LeanQbe.T.Arm64.Targ Kraken.AArch64.Print)
fi
command -v "$CC" >/dev/null || { echo "ERROR: C compiler '$CC' not found (set CC=...)" >&2; exit 1; }

TMP="$(mktemp -d "${TMPDIR:-/tmp}/kissat-leanqbe-build.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
cd "$ROOT"

if [ -z "${STAGE_LEAN_PATH:-}" ]; then
  echo "== [1/3] lake build LeanQbe.T.Examples.Kissat.$MODULE (+ code generator)"
  timeout 3600 lake build "LeanQbe.T.Examples.Kissat.$MODULE" LeanQbe.T.Opt \
    LeanQbe.T.Driver "${LAKE_EXTRA[@]}"
else
  echo "== [1/3] Using prebuilt STAGE_LEAN_PATH=$STAGE_LEAN_PATH (0 lake build) =="
fi

echo "== [2/3] emit $ARCH assembly for ${EXPR} (optInline maxSize=$INLINE_MAX)"
cat >"$TMP/Emit.lean" <<LEAN
import LeanQbe.T.Examples.Kissat.$MODULE
import LeanQbe.T.Opt
import LeanQbe.T.Driver
$IMPORTS

$OPENS

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "usage: <out.s>")
  let m := $EXPR
  let fns := if $INLINE_MAX > 0 then (m.optInline $INLINE_MAX).fns else m.fns
  let hints := fns.map (Fn.computeHints $TGT.toIsa $LEGAL)
  let dirs ← match LeanQbe.T.compile $TGT.toIsa $LEGAL fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  IO.FS.writeFile out (Driver.emitAsm ($PRINT) fns dirs)
LEAN
if [ -n "${STAGE_LEAN_PATH:-}" ]; then
  LEAN_PATH="$STAGE_LEAN_PATH" timeout 600 lean --run "$TMP/Emit.lean" "$TMP/solver.s"
else
  timeout 600 lake env lean --run "$TMP/Emit.lean" "$TMP/solver.s"
fi

echo "== [3/3] $CC: kissat_cli.c + solver.s -> $OUTPUT"
timeout 300 "$CC" -std=c99 -O2 -Wall -Wextra -Werror "${CFLAGS_ARCH[@]}" \
  bench/kissat/kissat_cli.c "$TMP/solver.s" -o "$TMP/kissat-leanqbe" 2>"$TMP/cc.log" || {
    cat "$TMP/cc.log" >&2; exit 1; }
grep -v -e 'SFrame' "$TMP/cc.log" >&2 || true
mkdir -p "$(dirname "$OUTPUT")"
mv "$TMP/kissat-leanqbe" "$OUTPUT"
echo "built $OUTPUT ($MODULE, $ARCH)"
echo "usage: $OUTPUT [--work-mb <MB>] [--fuel <N>] <input.cnf | ->"
