#!/usr/bin/env bash
# Run a single assembly test comparing AS execution against Kraken's eval
# Usage: ./run_asm_test.sh <test.S>
#
# Flow:
#   1. Assemble and link the test with GNU as/ld
#   2. Run to capture final register state (136 bytes)
#   3. Call krakentest to compare AS result against Kraken's eval
#   4. Report PASS/FAIL

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
KRAKEN_ROOT="$SCRIPT_DIR/.."
KRAKENTEST="$KRAKEN_ROOT/.lake/build/bin/krakentest"

if [ $# -lt 1 ]; then
    echo "Usage: $0 <test.S>"
    exit 1
fi

ASM_FILE="$1"
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

# Check krakentest exists
if [ ! -x "$KRAKENTEST" ]; then
    echo "Error: krakentest not found. Run 'lake build krakentest' first."
    exit 1
fi

# Cross-compile on ARM64 Apple
if [[ $(uname) == "Darwin" ]]; then
  if ! which gstat &>/dev/null; then
    echo "Missing gstat; please run `brew install coreutils`"
    exit 1
  fi
  ASFLAGS="-target x86_64-apple-darwin"
  LDFLAGS="-lSystem -L$(xcode-select -p)/SDKs/MacOSX.sdk/usr/lib"
  STAT=gstat
else
  STAT=stat
fi

# Assemble the assembly
TMP_ASM_FILE="$TMPDIR"/$(basename $ASM_FILE)
touch $TMP_ASM_FILE

PROLOGUE=$KRAKEN_ROOT/asm-tests/prologue-$(uname).S
EPILOGUE=$KRAKEN_ROOT/asm-tests/epilogue-$(uname).S

cat $PROLOGUE >> $TMP_ASM_FILE
cat $ASM_FILE >> $TMP_ASM_FILE
cat $EPILOGUE >> $TMP_ASM_FILE

# Step 1: Assemble and link
as $ASFLAGS -o "$TMPDIR/test.o" "$TMP_ASM_FILE" || {
    echo "FAIL: Assembly failed for $TMP_ASM_FILE"
    exit 1
}

ld -o "$TMPDIR/test" "$TMPDIR/test.o" $LDFLAGS || {
    echo "FAIL: Linking failed for $ASM_FILE"
    exit 1
}

# Step 2: Run and capture output (136 bytes: registers + flags)
"$TMPDIR/test" > "$TMPDIR/output.bin"

# Check we got enough output
if [[ ! -f "$TMPDIR/output.bin" ]] || [[ $($STAT -c%s "$TMPDIR/output.bin") -lt 136 ]]; then
    echo "FAIL: Test execution didn't produce expected output"
    exit 1
fi

# Step 3: Run krakentest to compare AS vs Kraken
"$KRAKENTEST" "$ASM_FILE" "$TMPDIR/output.bin" || {
  cp "$TMPDIR/output.bin" output.bin
  cp $TMP_ASM_FILE input.S
  echo "Left output.bin and input.S in the working directory to help debug"
}
