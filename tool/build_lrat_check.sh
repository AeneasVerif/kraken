#!/usr/bin/env bash
# Build the standalone `lrat_check` CLI wrapper around `lrat_check_bytes`.
# Usage:
#   tool/build_lrat_check.sh [--qbe] [--rebuild] [--out <path>]
#
# By default, emits `lrat_bytes.s` via `.lake/build/bin/leanqbe lrat_bytes` (building
# `leanqbe` first if missing or `--rebuild` is given) and compiles `tool/lrat_check.rs`
# with `rustc --edition 2021 -O` into `.lake/build/bin/lrat_check`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CALLER_PWD="$PWD"

USE_QBE="${USE_QBE:-0}"
REBUILD="${REBUILD:-0}"
OUT="${OUT:-$ROOT/.lake/build/bin/lrat_check}"

while [ $# -gt 0 ]; do
  case "$1" in
    --qbe) USE_QBE=1; shift ;;
    --rebuild) REBUILD=1; shift ;;
    --out)
      [ $# -ge 2 ] || { echo "missing path after --out" >&2; exit 2; }
      OUT="$2"; shift 2 ;;
    -h|--help)
      echo "usage: tool/build_lrat_check.sh [--qbe] [--rebuild] [--out <path>]"
      exit 0 ;;
    *)
      echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

case "$OUT" in
  /*) ;;
  *) OUT="$CALLER_PWD/$OUT" ;;
esac

cd "$ROOT"

TMP="$(mktemp -d "${TMPDIR:-/tmp}/lrat-check-build.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

if [ "$REBUILD" = "1" ] || [ ! -x "$ROOT/.lake/build/bin/leanqbe" ]; then
  timeout 1800 lake build leanqbe
fi

if [ "$USE_QBE" = "1" ]; then
  if [ -z "${QBE:-}" ]; then
    QBE_SRC="${QBE_SRC:-$ROOT/qbe}"
    if [ -d "$QBE_SRC" ]; then
      cp -r "$QBE_SRC" "$TMP/qbe-src"
      timeout 300 make -C "$TMP/qbe-src" -j8 >/dev/null
      QBE="$TMP/qbe-src/qbe"
    elif QBE="$(command -v qbe || true)" && [ -n "$QBE" ]; then
      :
    else
      echo "FAIL: stock QBE not found (set QBE, QBE_SRC, or place checkout at $ROOT/qbe)" >&2
      exit 1
    fi
  fi
  timeout 60 "$ROOT/.lake/build/bin/leanqbe" --il lrat_bytes >"$TMP/lrat_bytes.ssa"
  timeout 60 "$QBE" -o "$TMP/lrat_bytes.s" "$TMP/lrat_bytes.ssa"
else
  timeout 60 "$ROOT/.lake/build/bin/leanqbe" lrat_bytes >"$TMP/lrat_bytes.s"
fi

timeout 60 cc -c "$TMP/lrat_bytes.s" -o "$TMP/lrat_bytes.o"
mkdir -p "$(dirname "$OUT")"
timeout 120 rustc --edition 2021 -O -C link-arg="$TMP/lrat_bytes.o" \
  "$ROOT/tool/lrat_check.rs" -o "$OUT"
echo "built $OUT"
