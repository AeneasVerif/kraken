#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

SDE_PLATFORM="$(uname -sm)"
case "$SDE_PLATFORM" in
  "Linux x86_64") ;;
  *) echo "Intel SDE requires Linux x86_64; found $SDE_PLATFORM" >&2; exit 1 ;;
esac

SDE_DIR="sde-external-10.13.1-2026-07-28-lin"
SDE_URL="https://downloadmirror.intel.com/924984/$SDE_DIR.tar.xz"
SDE_SHA256="94e97d623fec54385686e1e7ba65ebc9941748c05ee451423948334892bf2b50"

if [[ -e sde && ! -L sde ]]; then
  echo "Cannot replace tool/sde: it is not a symlink" >&2
  exit 1
fi

if [[ ! -x "$SDE_DIR/sde64" ]]; then
  if [[ -e "$SDE_DIR" || -L "$SDE_DIR" ]]; then
    echo "Incomplete SDE installation at tool/$SDE_DIR; remove it and retry" >&2
    exit 1
  fi
  SDE_TMP="$(mktemp -d ./sde-external-download.XXXXXX)"
  trap 'rm -rf -- "$SDE_TMP"' EXIT
  curl --fail --show-error --location --retry 3 --connect-timeout 15 --max-time 180 \
    --output "$SDE_TMP/sde.tar.xz" "$SDE_URL"
  printf '%s  %s\n' "$SDE_SHA256" "$SDE_TMP/sde.tar.xz" | sha256sum --check -
  tar -xJf "$SDE_TMP/sde.tar.xz" -C "$SDE_TMP"
  if [[ ! -x "$SDE_TMP/$SDE_DIR/sde64" ]]; then
    echo "Downloaded SDE archive does not contain an executable sde64" >&2
    exit 1
  fi
  mv "$SDE_TMP/$SDE_DIR" "$SDE_DIR"
fi
ln -sfn "$SDE_DIR" sde
