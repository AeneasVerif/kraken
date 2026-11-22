#!/usr/bin/env bash
# Build stock QBE at most once into a read-only content/commit-addressed cache
# (`${XDG_CACHE_HOME:-$HOME/.cache}/lean-qbe/qbe-<sha>/qbe`) under `flock`, and
# print the executable path to stdout.
#
# Exit codes:
#   0  QBE binary is ready; path printed to stdout.
#   1  Explicit $QBE is invalid, or building stock QBE failed.
#   2  Stock QBE source directory and system `qbe` binary were not found.
set -euo pipefail

if [ -n "${QBE:-}" ]; then
  if [ -x "$QBE" ]; then
    printf '%s\n' "$QBE"
    exit 0
  fi
  echo "ensure_qbe: QBE='$QBE' is not executable" >&2
  exit 1
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QBE_SRC="${QBE_SRC:-}"
if [ -z "$QBE_SRC" ]; then
  if [ -d "$ROOT/qbe" ]; then
    QBE_SRC="$ROOT/qbe"
  else
    COMMON_GIT_DIR="$(git -C "$ROOT" rev-parse --git-common-dir 2>/dev/null || true)"
    if [ -n "$COMMON_GIT_DIR" ]; then
      case "$COMMON_GIT_DIR" in
        /*) COMMON_ROOT="$(cd "$COMMON_GIT_DIR/.." 2>/dev/null && pwd || true)" ;;
        *)  COMMON_ROOT="$(cd "$ROOT/$COMMON_GIT_DIR/.." 2>/dev/null && pwd || true)" ;;
      esac
      if [ -n "$COMMON_ROOT" ] && [ -d "$COMMON_ROOT/qbe" ]; then
        QBE_SRC="$COMMON_ROOT/qbe"
      fi
    fi
  fi
fi

if [ -z "$QBE_SRC" ] || [ ! -d "$QBE_SRC" ]; then
  if QBE_CMD="$(command -v qbe || true)" && [ -n "$QBE_CMD" ] && [ -x "$QBE_CMD" ]; then
    printf '%s\n' "$QBE_CMD"
    exit 0
  fi
  echo "ensure_qbe: stock QBE not found (set QBE, QBE_SRC, or place checkout at $ROOT/qbe)" >&2
  exit 2
fi

if [ -d "$QBE_SRC/.git" ] && git -C "$QBE_SRC" rev-parse HEAD >/dev/null 2>&1 \
   && [ -z "$(git -C "$QBE_SRC" status --porcelain 2>/dev/null || echo dirty)" ]; then
  QBE_SHA="$(git -C "$QBE_SRC" rev-parse --short=12 HEAD)"
else
  QBE_SHA="$(find "$QBE_SRC" -maxdepth 3 -type f \
    \( -name '*.c' -o -name '*.h' -o -name 'Makefile' -o -name '*.s' \) \
    | LC_ALL=C sort | xargs sha256sum | sha256sum | awk '{print substr($1, 1, 12)}')"
fi

CACHE_ROOT="${XDG_CACHE_HOME:-$HOME/.cache}/lean-qbe"
QBE_DIR="$CACHE_ROOT/qbe-$QBE_SHA"
QBE_BIN="$QBE_DIR/qbe"
LOCK_FILE="$CACHE_ROOT/qbe-$QBE_SHA.lock"

mkdir -p "$CACHE_ROOT"

if [ -x "$QBE_BIN" ]; then
  printf '%s\n' "$QBE_BIN"
  exit 0
fi

(
  flock 9
  if [ ! -x "$QBE_BIN" ]; then
    BUILD_TMP="$(mktemp -d "$CACHE_ROOT/qbe-build.XXXXXX")"
    trap 'rm -rf "$BUILD_TMP"' EXIT
    cp -a "$QBE_SRC/." "$BUILD_TMP/src"
    chmod -R u+w "$BUILD_TMP/src"
    timeout 300 make -C "$BUILD_TMP/src" clean >/dev/null 2>&1 || true
    if ! timeout 300 make -C "$BUILD_TMP/src" -j"$(nproc)" >"$BUILD_TMP/build.log" 2>&1; then
      echo "ensure_qbe: failed to build stock QBE from $QBE_SRC:" >&2
      tail -n 40 "$BUILD_TMP/build.log" >&2 || true
      exit 1
    fi
    mkdir -p "$QBE_DIR"
    chmod 555 "$BUILD_TMP/src/qbe"
    mv -f "$BUILD_TMP/src/qbe" "$QBE_BIN"
    rm -rf "$BUILD_TMP"
    trap - EXIT
  fi
) 9>"$LOCK_FILE" || exit 1

printf '%s\n' "$QBE_BIN"
