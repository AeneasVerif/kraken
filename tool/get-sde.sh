#!/bin/sh
set -euo pipefail
cd "$(dirname "$0")"

case "$(uname -s)" in
  Linux*)     PLATFORM="lin" ;;
  *)          echo "Unsupported OS: $OS" >&2; exit 1 ;;
esac

SDE_URL="$(curl -s "https://www.intel.com/content/www/us/en/download/684897/intel-software-development-emulator.html" \
  | grep -iEo "https://[^\"]*sde-external-[^\"]*-${PLATFORM}\.tar\.xz" \
  | head -n 1)"
exec curl -sL "$SDE_URL" | tar xJ

SDE_ARCHIVE="$(basename "$SDE_URL")"
unlink sde || true
ln -s "${SDE_ARCHIVE%.tar.xz}" sde
