#!/usr/bin/env bash
# Build a native `kissat-leanqbe` binary from the verified LeanQbe Kissat solver.
#
#   bash bench/kissat/build_solver.sh [--module FullM3|Plain|Full|FullFast|FullM4] \
#     [--arch x64|arm64] [--inline-max <N>] [--allow-uncertified] [--debug|-g] \
#     [--keep-asm] [--save-asm <path>] [-o <output_bin>]
#
# 1. `lake build`s the solver module `LeanQbe.T.Examples.Kissat.<Module>` and the code generator
#    (skipped when `STAGE_LEAN_PATH` is set).
# 2. Compiles `<Module>Module` with `LeanQbe.T.compile` for x86-64 (`Kraken.X64.PrintATT`) or
#    AArch64 (`Kraken.AArch64.Print`) into a `.s` file. Default `--inline-max 0` emits the exact IR
#    certified by `LinkedCert`; `--inline-max <N>` (`N > 0`) and `--debug` apply uncertified
#    transforms outside the `LinkedCert` proof.
# 3. Links that assembly with `bench/kissat/kissat_cli.c` into `<output_bin>`. For all modules
#    except `Plain`, compiles `kissat_cli.c` with `-DKISSAT_UNSAT_ONLY=1` so uncertified `10`
#    returns print `s UNKNOWN` and exit `0`. `FullM4` has source-level `ModuleOk` only (no native
#    `LinkedCert` yet) and requires `--allow-uncertified`.
#
# Defaults: --module FullM3 --arch x64 --inline-max 0 -o /tmp/kissat-leanqbe-<module>[-arm64]. All
# intermediate files live in a temporary directory removed on exit; the repository is never written
# to except for Lake's own .lake/ build cache. For --arch arm64 on a non-AArch64 host the binary
# is built with aarch64-linux-gnu-gcc (override with CC=...) and runs under qemu-aarch64, e.g.
#   qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-fullm3-arm64 input.cnf
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CALLER_PWD="$PWD"
MODULE=FullM3
ARCH=x64
INLINE_MAX="${INLINE_MAX:-0}"
OUTPUT=""
DEBUG=0
KEEP_ASM=0
SAVE_ASM=""
ALLOW_UNCERTIFIED=0

usage() {
  echo "usage: bash bench/kissat/build_solver.sh" \
    "[--module FullM3|Plain|Full|FullFast|FullM4] [--arch x64|arm64]" \
    "[--inline-max <N>] [--allow-uncertified] [--debug|-g] [--keep-asm]" \
    "[--save-asm <path>] [-o <output_bin>]"
  echo "  note: --inline-max > 0 and --debug rewrite IR/directives outside LinkedCert;" \
    "FullM4 requires --allow-uncertified."
}

while [ $# -gt 0 ]; do
  case "$1" in
    --module|--arch|--inline-max|--save-asm|-o)
      [ $# -ge 2 ] || { echo "ERROR: $1 requires an argument" >&2; usage >&2; exit 2; }
      case "$1" in
        --module) MODULE="$2" ;;
        --arch) ARCH="$2" ;;
        --inline-max) INLINE_MAX="$2" ;;
        --save-asm) SAVE_ASM="$2" ;;
        -o) OUTPUT="$2" ;;
      esac
      shift 2 ;;
    --allow-uncertified|--allow-uncertified-codegen) ALLOW_UNCERTIFIED=1; shift ;;
    --debug|-g) DEBUG=1; shift ;;
    --keep-asm) KEEP_ASM=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "ERROR: unknown argument '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

case "$INLINE_MAX" in
  ''|*[!0-9]*)
    echo "ERROR: --inline-max expects a non-negative integer, got '$INLINE_MAX'" >&2
    exit 2 ;;
esac

case "${MODULE,,}" in
  full) MODULE=Full; EXPR=LeanQbe.T.Examples.Kissat.Full.fullModule ;;
  fullfast) MODULE=FullFast; EXPR=LeanQbe.T.Examples.Kissat.FullFast.fastModule ;;
  fullm3|m3) MODULE=FullM3; EXPR=LeanQbe.T.Examples.Kissat.FullM3.m3Module ;;
  fullm4|m4) MODULE=FullM4; EXPR=LeanQbe.T.Examples.Kissat.FullM4.m4Module ;;
  plain) MODULE=Plain; EXPR=LeanQbe.T.Examples.Kissat.Plain.plainModule ;;
  *)
    echo "ERROR: unknown module '$MODULE' (expected FullM3|Plain|Full|FullFast|FullM4)" >&2
    exit 2 ;;
esac

if [ "$MODULE" = Full ] || [ "$MODULE" = FullFast ]; then
  echo "WARNING: --module $MODULE is a retired legacy solver (moved to LeanQbeLegacy*;" \
    "superseded by FullM3)." >&2
fi
if [ "$MODULE" = FullM4 ]; then
  if [ "$ALLOW_UNCERTIFIED" != 1 ]; then
    echo "ERROR: --module FullM4 has source-level ModuleOk only and no native LinkedCert yet;" \
      "pass --allow-uncertified to build uncertified codegen." >&2
    exit 2
  fi
  echo "WARNING: --module FullM4 has source-level ModuleOk only and NO native LinkedCert" \
    "(--allow-uncertified)." >&2
fi
if [ "$INLINE_MAX" -gt 0 ]; then
  echo "WARNING: --inline-max $INLINE_MAX applies Module.optInline; emitted assembly diverges" \
    "from the kernel-checked LinkedCert (which certifies inline=0 only)." >&2
fi
if [ "$DEBUG" = 1 ]; then
  echo "WARNING: --debug applies DebugAsm label-scrubbing and CFI directives outside the" \
    "kernel-checked LinkedCert." >&2
fi
case "${ARCH,,}" in
  x64|amd64|x86_64) ARCH=x64; SUFFIX="" ;;
  arm64|aarch64) ARCH=arm64; SUFFIX="-arm64" ;;
  *) echo "ERROR: unknown arch '$ARCH' (expected x64 | arm64)" >&2; exit 2 ;;
esac
OUTPUT="${OUTPUT:-/tmp/kissat-leanqbe-${MODULE,,}$SUFFIX}"
case "$OUTPUT" in /*) ;; *) OUTPUT="$CALLER_PWD/$OUTPUT" ;; esac

CFLAGS_DEBUG=()
if [ "$DEBUG" = 1 ]; then
  CFLAGS_DEBUG=(-g)
fi

if [ "$ARCH" = x64 ]; then
  CC="${CC:-gcc}"
  CFLAGS_ARCH=(-no-pie)
  IMPORTS="import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign"
  OPENS="open LeanQbe.T LeanQbe.T.Amd64"
  TGT=x64Target; LEGAL=x64LegalTarget
  PRINT='fun c => toATTAligned c ++ "\n"'
  LAKE_EXTRA=(LeanQbe.T.Amd64.Targ LeanQbe.T.Amd64.PrintATTAlign)
  if [ "$DEBUG" = 1 ]; then
    IMPORTS="$IMPORTS
import LeanQbe.T.Amd64.DebugAsm"
    EMIT_ASM='emitX64DebugAsm fns dirs (comments := true)'
    LAKE_EXTRA+=(LeanQbe.T.Amd64.DebugAsm)
  else
    EMIT_ASM="Driver.emitAsm ($PRINT) fns dirs"
  fi
else
  if [ "$(uname -m)" = aarch64 ]; then CC="${CC:-gcc}"; else CC="${CC:-aarch64-linux-gnu-gcc}"; fi
  CFLAGS_ARCH=()
  IMPORTS="import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print"
  OPENS="open LeanQbe.T LeanQbe.T.Arm64"
  TGT=armTarget; LEGAL=armLegalTarget
  PRINT='fun c => ".p2align 2\n" ++ String.intercalate "\n" (c.map Kraken.AArch64.Print.directive) ++ "\n"'
  LAKE_EXTRA=(LeanQbe.T.Arm64.Targ Kraken.AArch64.Print)
  if [ "$DEBUG" = 1 ]; then
    IMPORTS="$IMPORTS
import LeanQbe.T.Arm64.DebugAsm"
    EMIT_ASM='emitArm64DebugAsm fns dirs (comments := true)'
    LAKE_EXTRA+=(LeanQbe.T.Arm64.DebugAsm)
  else
    EMIT_ASM="Driver.emitAsm ($PRINT) fns dirs"
  fi
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

echo "== [2/3] emit $ARCH assembly for ${EXPR} (inline-max=$INLINE_MAX)"
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
  IO.FS.writeFile out ($EMIT_ASM)
LEAN
if [ -n "${STAGE_LEAN_PATH:-}" ]; then
  LEAN_PATH="$STAGE_LEAN_PATH" timeout 600 lean --run "$TMP/Emit.lean" "$TMP/solver.s"
else
  timeout 600 lake env lean --run "$TMP/Emit.lean" "$TMP/solver.s"
fi

CFLAGS_SAT=()
SAT_MODE="SAT+UNSAT"
if [ "$MODULE" != Plain ]; then
  CFLAGS_SAT=(-DKISSAT_UNSAT_ONLY=1)
  SAT_MODE="UNSAT-only (-DKISSAT_UNSAT_ONLY=1)"
fi

echo "== [3/3] $CC: kissat_cli.c ($SAT_MODE) + solver.s -> $OUTPUT"
ASM_SRC="$TMP/solver.s"
if [ -n "$SAVE_ASM" ] || [ "$KEEP_ASM" = 1 ] || [ "$DEBUG" = 1 ]; then
  if [ -n "$SAVE_ASM" ]; then
    case "$SAVE_ASM" in /*) ASM_SRC="$SAVE_ASM" ;; *) ASM_SRC="$CALLER_PWD/$SAVE_ASM" ;; esac
  elif [ -n "$OUTPUT" ]; then
    case "$OUTPUT" in /*) ASM_SRC="${OUTPUT}.s" ;; *) ASM_SRC="$CALLER_PWD/${OUTPUT}.s" ;; esac
  else
    ASM_SRC="/tmp/kissat-${MODULE}-${ARCH}.s"
  fi
  mkdir -p "$(dirname "$ASM_SRC")"
  cp "$TMP/solver.s" "$ASM_SRC"
  echo "== kept assembly: $ASM_SRC"
fi
timeout 300 "$CC" -std=c99 -O2 -Wall -Wextra -Werror "${CFLAGS_ARCH[@]}" "${CFLAGS_DEBUG[@]}" \
  "${CFLAGS_SAT[@]}" bench/kissat/kissat_cli.c "$ASM_SRC" -o "$TMP/kissat-leanqbe" \
  2>"$TMP/cc.log" || {
    cat "$TMP/cc.log" >&2; exit 1; }
grep -v -e 'SFrame' "$TMP/cc.log" >&2 || true
mkdir -p "$(dirname "$OUTPUT")"
mv "$TMP/kissat-leanqbe" "$OUTPUT"
echo "built $OUTPUT ($MODULE, $ARCH, $SAT_MODE, inline-max=$INLINE_MAX)"
echo "usage: $OUTPUT [--work-mb <MB>] [--fuel <N>] <input.cnf | ->"
