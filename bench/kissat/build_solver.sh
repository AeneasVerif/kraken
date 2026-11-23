#!/usr/bin/env bash
# Build a native `kissat-leanqbe` binary from the verified LeanQbe Kissat solver.
#
#   bash bench/kissat/build_solver.sh
#     [--module FullM5|FullM6|FullM7|FullM7Plus|FullM7Fidelity|FullM4|FullM3|Plain|Full|FullFast]
#     [--arch x64|arm64] [--inline-max <N>] [--allow-uncertified] [--debug|-g]
#     [--keep-asm] [--save-asm <path>] [-o <output_bin>]
#
# 1. `lake build`s the solver module `LeanQbe.T.Examples.Kissat.<Module>` and the code generator
#    (skipped when `STAGE_LEAN_PATH` is set).
# 2. Compiles `<Module>Module` with `Driver.compileFns` (matching `LinkedCert`) for x86-64
#    (`toATTAligned`) or AArch64 (`Kraken.AArch64.Print.directive`) into a `.s` file. Default
#    `--inline-max 0` emits the exact certified policy/IR (`InlinePolicy.b5` for `FullM5`,
#    `FullM6Inl.m6InlFns` matching `kissatM6_compiled_{x64,arm64}.code` for `FullM6`,
#    `FullM7Inl.m7InlFns`/`InlinePolicy.b5` for `FullM7`, `inline=0` elsewhere);
#    `--inline-max <N>` (`N > 0`) and `--debug` apply uncertified transforms outside `LinkedCert`.
# 3. Links that assembly with `bench/kissat/kissat_cli.c` into `<output_bin>`. `Plain`, `FullM5`,
#    and `FullM4` (via `KissatM4Sound`) build with certified `SAT+UNSAT`; `FullM6` (via dual-arch
#    `KissatM6` `LinkedCert`s) builds with certified UNSAT + runtime-checked SAT (`kissat_check_model`)
#    without needing `--allow-uncertified`; `FullM7` requires `--allow-uncertified` until `KissatM7`
#    certs land; `FullM3`/`Full`/`FullFast` compile with `-DKISSAT_UNSAT_ONLY=1` so `10` returns UNKNOWN.
#
# Defaults: --module FullM5 --arch x64 --inline-max 0 -o /tmp/kissat-leanqbe-<module>[-arm64].
# Intermediate files live in a temp directory removed on exit; the repository is never written to
# except for Lake's .lake/ build cache. For --arch arm64 on a non-AArch64 host, builds with
# aarch64-linux-gnu-gcc (override with CC=...) and runs under qemu-aarch64, e.g.
#   qemu-aarch64 -L /usr/aarch64-linux-gnu /tmp/kissat-leanqbe-fullm5-arm64 input.cnf
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CALLER_PWD="$PWD"
MODULE=FullM5
ARCH=x64
INLINE_MAX="${INLINE_MAX:-0}"
OUTPUT=""
DEBUG=0
KEEP_ASM=0
SAVE_ASM=""
ALLOW_UNCERTIFIED=0

usage() {
  echo "usage: bash bench/kissat/build_solver.sh" \
    "[--module FullM5|FullM6|FullM7|FullM7Plus|FullM7Fidelity|FullM4|FullM3|Plain|Full|FullFast]" \
    "[--arch x64|arm64] [--inline-max <N>] [--allow-uncertified] [--debug|-g]" \
    "[--keep-asm] [--save-asm <path>] [-o <output_bin>]"
  echo "  aliases: m5, m6, m7, m7plus, m7fidelity, m7fid, m4, m3 (case-insensitive)."
  echo "  note: --inline-max > 0 and --debug rewrite IR/directives outside LinkedCert;" \
    "uncertified modules require --allow-uncertified."
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

LEAN_MOD=""
case "${MODULE,,}" in
  full) MODULE=Full; LEAN_MOD=Full; EXPR=LeanQbe.T.Examples.Kissat.Full.fullModule ;;
  fullfast) MODULE=FullFast; LEAN_MOD=FullFast; EXPR=LeanQbe.T.Examples.Kissat.FullFast.fastModule ;;
  fullm3|m3) MODULE=FullM3; LEAN_MOD=FullM3; EXPR=LeanQbe.T.Examples.Kissat.FullM3.m3Module ;;
  fullm4|m4) MODULE=FullM4; LEAN_MOD=FullM4; EXPR=LeanQbe.T.Examples.Kissat.FullM4.m4Module ;;
  fullm5|m5) MODULE=FullM5; LEAN_MOD=FullM5; EXPR=LeanQbe.T.Examples.Kissat.FullM5.m5Module ;;
  fullm6|m6) MODULE=FullM6; LEAN_MOD=FullM6; EXPR=LeanQbe.T.Examples.Kissat.FullM6.m6Module ;;
  fullm7|m7) MODULE=FullM7; LEAN_MOD=FullM7; EXPR=LeanQbe.T.Examples.Kissat.FullM7.m7Module ;;
  fullm7plus|m7plus)
    MODULE=FullM7Plus; LEAN_MOD=FullM7PlusAssembly
    EXPR=LeanQbe.T.Examples.Kissat.FullM7Plus.m7PlusModule ;;
  fullm7fidelity|m7fidelity|m7fid)
    MODULE=FullM7Fidelity; LEAN_MOD=FullM7FidelityAssembly
    EXPR=LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityModule ;;
  plain) MODULE=Plain; LEAN_MOD=Plain; EXPR=LeanQbe.T.Examples.Kissat.Plain.plainModule ;;
  *)
    echo "ERROR: unknown module '$MODULE'" \
      "(expected FullM5|FullM6|FullM7|FullM7Plus|FullM7Fidelity|FullM4|FullM3|Plain|Full|FullFast)" >&2
    exit 2 ;;
esac

case "${ARCH,,}" in
  x64|amd64|x86_64) ARCH=x64; ARCH_DIR=Amd64; SUFFIX="" ;;
  arm64|aarch64) ARCH=arm64; ARCH_DIR=Arm64; SUFFIX="-arm64" ;;
  *) echo "ERROR: unknown arch '$ARCH' (expected x64 | arm64)" >&2; exit 2 ;;
esac
OUTPUT="${OUTPUT:-/tmp/kissat-leanqbe-${MODULE,,}$SUFFIX}"
case "$OUTPUT" in /*) ;; *) OUTPUT="$CALLER_PWD/$OUTPUT" ;; esac

if [ "$MODULE" = Full ] || [ "$MODULE" = FullFast ]; then
  echo "WARNING: --module $MODULE is a retired legacy solver (moved to LeanQbeLegacy*;" \
    "superseded by FullM5)." >&2
fi

CFLAGS_SAT=()
SAT_MODE="SAT+UNSAT"
case "$MODULE" in
  Plain)
    CFLAGS_SAT=(-DKISSAT_CLI_PLAIN_LAYOUT=1)
    SAT_MODE="SAT+UNSAT"
    ;;
  FullM5)
    SAT_MODE="SAT+UNSAT"
    ;;
  FullM3|Full|FullFast)
    CFLAGS_SAT=(-DKISSAT_UNSAT_ONLY=1)
    SAT_MODE="UNSAT-only (-DKISSAT_UNSAT_ONLY=1)"
    ;;
  FullM4)
    if [ -f "$ROOT/LeanQbe/T/$ARCH_DIR/KissatM4Sound.lean" ]; then
      SAT_MODE="SAT+UNSAT"
    elif [ "$ALLOW_UNCERTIFIED" = 1 ]; then
      echo "WARNING: --module FullM4 has source-level ModuleOk only and NO native" \
        "LinkedCert for $ARCH yet (--allow-uncertified)." >&2
      CFLAGS_SAT=(-DKISSAT_UNSAT_ONLY=1)
      SAT_MODE="UNSAT-only (-DKISSAT_UNSAT_ONLY=1)"
    else
      echo "ERROR: --module FullM4 has source-level ModuleOk only and no native" \
        "LinkedCert for $ARCH yet; pass --allow-uncertified to build uncertified codegen." >&2
      exit 2
    fi
    ;;
  FullM6|FullM7|FullM7Plus|FullM7Fidelity)
    CERT_PFX="Kissat${MODULE#Full}"
    SOUND_LEAN="$ROOT/LeanQbe/T/$ARCH_DIR/${CERT_PFX}Sound.lean"
    CERT_LEAN="$ROOT/LeanQbe/T/$ARCH_DIR/${CERT_PFX}.lean"
    if [ -f "$SOUND_LEAN" ]; then
      SAT_MODE="SAT+UNSAT"
    elif [ -f "$CERT_LEAN" ]; then
      SAT_MODE="certified UNSAT + runtime-checked SAT"
    elif [ "$ALLOW_UNCERTIFIED" = 1 ]; then
      echo "WARNING: --module $MODULE has NO native ${CERT_PFX} LinkedCert for" \
        "$ARCH yet (--allow-uncertified; SAT uses C0 kissat_check_model)." >&2
      SAT_MODE="SAT+UNSAT (uncertified)"
    else
      echo "ERROR: --module $MODULE has no native ${CERT_PFX} LinkedCert for" \
        "$ARCH ($ARCH_DIR) yet; pass --allow-uncertified to build uncertified codegen." >&2
      exit 2
    fi
    ;;
esac

if [ -z "${STAGE_LEAN_PATH:-}" ] && \
   [ ! -f "$ROOT/LeanQbe/T/Examples/Kissat/$LEAN_MOD.lean" ]; then
  echo "ERROR: LeanQbe/T/Examples/Kissat/$LEAN_MOD.lean is not present in $ROOT yet." >&2
  exit 2
fi

if [ "$INLINE_MAX" -gt 0 ]; then
  echo "WARNING: --inline-max $INLINE_MAX applies Module.optInline; emitted assembly" \
    "diverges from the kernel-checked LinkedCert." >&2
fi
if [ "$DEBUG" = 1 ]; then
  echo "WARNING: --debug applies DebugAsm label-scrubbing and CFI directives outside" \
    "the kernel-checked LinkedCert." >&2
fi

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
  PRINT='fun c => ".p2align 2\n" ++'
  PRINT="$PRINT"' String.intercalate "\n" (c.map Kraken.AArch64.Print.directive) ++ "\n"'
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
command -v "$CC" >/dev/null || {
  echo "ERROR: C compiler '$CC' not found (set CC=...)" >&2
  exit 1
}

if [ "$INLINE_MAX" -gt 0 ]; then
  FNS_EXPR="(($EXPR).optInline $INLINE_MAX).fns"
  INL_DESC="inline-max=$INLINE_MAX"
elif [ "$MODULE" = FullM5 ]; then
  IMPORTS="$IMPORTS
import LeanQbe.T.MainInline"
  LAKE_EXTRA+=(LeanQbe.T.MainInline)
  FNS_EXPR="(($EXPR).optInlinePolicy InlinePolicy.b5).fns"
  INL_DESC="inline-policy=b5"
elif [ "$MODULE" = FullM6 ]; then
  IMPORTS="$IMPORTS
import LeanQbe.T.Examples.Kissat.FullM6Inl"
  LAKE_EXTRA+=(LeanQbe.T.Examples.Kissat.FullM6Inl)
  FNS_EXPR="LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns"
  INL_DESC="inline-policy=m6InlPolicy (FullM6Inl; matches kissatM6_compiled_${ARCH}.code)"
elif [ "$MODULE" = FullM7 ]; then
  if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7Inl.lean" ]; then
    IMPORTS="$IMPORTS
import LeanQbe.T.Examples.Kissat.FullM7Inl"
    LAKE_EXTRA+=(LeanQbe.T.Examples.Kissat.FullM7Inl)
    FNS_EXPR="LeanQbe.T.Examples.Kissat.FullM7Inl.m7InlFns"
    INL_DESC="inline-policy=FullM7Inl"
  elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean" ]; then
    IMPORTS="$IMPORTS
import LeanQbe.T.MainInline
import LeanQbe.T.Examples.Kissat.FullM7InlPolicy"
    LAKE_EXTRA+=(LeanQbe.T.MainInline LeanQbe.T.Examples.Kissat.FullM7InlPolicy)
    FNS_EXPR="(($EXPR).optInlinePolicy LeanQbe.T.Examples.Kissat.FullM7InlPolicy.m7InlPolicy).fns"
    INL_DESC="inline-policy=m7InlPolicy"
  else
    IMPORTS="$IMPORTS
import LeanQbe.T.MainInline"
    LAKE_EXTRA+=(LeanQbe.T.MainInline)
    FNS_EXPR="(($EXPR).optInlinePolicy InlinePolicy.b5).fns"
    INL_DESC="inline-policy=b5"
  fi
elif [ "$MODULE" = FullM7Plus ]; then
  IMPORTS="$IMPORTS
import LeanQbe.T.Examples.Kissat.FullM7PlusInl"
  LAKE_EXTRA+=(LeanQbe.T.Examples.Kissat.FullM7PlusInl)
  FNS_EXPR="LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlFns"
  INL_DESC="inline-policy=m7InlPolicy (FullM7PlusInl)"
elif [ "$MODULE" = FullM7Fidelity ]; then
  IMPORTS="$IMPORTS
import LeanQbe.T.Examples.Kissat.FullM7FidelityInl"
  LAKE_EXTRA+=(LeanQbe.T.Examples.Kissat.FullM7FidelityInl)
  FNS_EXPR="LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlFns"
  INL_DESC="inline-policy=m7InlPolicy (FullM7FidelityInl)"
else
  FNS_EXPR="($EXPR).fns"
  INL_DESC="inline-max=0"
fi

TMP="$(mktemp -d "${TMPDIR:-/tmp}/kissat-leanqbe-build.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
cd "$ROOT"

if [ -z "${STAGE_LEAN_PATH:-}" ]; then
  echo "== [1/3] lake build LeanQbe.T.Examples.Kissat.$LEAN_MOD (+ code generator)"
  timeout 3600 lake build "LeanQbe.T.Examples.Kissat.$LEAN_MOD" LeanQbe.T.Opt \
    LeanQbe.T.Driver "${LAKE_EXTRA[@]}"
else
  echo "== [1/3] Using prebuilt STAGE_LEAN_PATH=$STAGE_LEAN_PATH (0 lake build) =="
fi

echo "== [2/3] emit $ARCH assembly for ${EXPR} ($INL_DESC)"
cat >"$TMP/Emit.lean" <<LEAN
import LeanQbe.T.Examples.Kissat.$LEAN_MOD
import LeanQbe.T.Opt
import LeanQbe.T.Driver
$IMPORTS

$OPENS

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "usage: <out.s>")
  let fns := $FNS_EXPR
  let dirs ← match Driver.compileFns $TGT.toIsa $LEGAL fns with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  IO.FS.writeFile out ($EMIT_ASM)
LEAN
if [ -n "${STAGE_LEAN_PATH:-}" ]; then
  LEAN_PATH="$STAGE_LEAN_PATH" timeout 600 lean --run "$TMP/Emit.lean" "$TMP/solver.s"
else
  timeout 600 lake env lean --run "$TMP/Emit.lean" "$TMP/solver.s"
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
echo "built $OUTPUT ($MODULE, $ARCH, $SAT_MODE, $INL_DESC)"
echo "usage: $OUTPUT [--work-mb <MB>] [--fuel <N>] [-n|--no-model] <input.cnf | ->"
