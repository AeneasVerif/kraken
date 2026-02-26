#!/bin/bash
# Test that AsmInterp.Core builds with Lean 4.22.0
# This ensures backward compatibility for downstream projects.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_DIR="$(dirname "$SCRIPT_DIR")"
cd "$REPO_DIR"

# Save original toolchain
ORIG_TOOLCHAIN=$(cat lean-toolchain)

cleanup() {
    echo "Restoring original toolchain: $ORIG_TOOLCHAIN"
    echo "$ORIG_TOOLCHAIN" > lean-toolchain
}

# Always restore toolchain on exit (success, failure, or interrupt)
trap cleanup EXIT

echo "=== Testing v4.22.0 Compatibility ==="
echo "Original toolchain: $ORIG_TOOLCHAIN"

# Switch to test toolchain
echo "leanprover/lean4:v4.22.0" > lean-toolchain
echo "Switched to: $(cat lean-toolchain)"

# Clean build artifacts (but keep packages)
rm -rf .lake/build

# Update dependencies and fetch cache if available
echo "Updating dependencies..."
lake update 2>/dev/null || true
lake exe cache get 2>/dev/null || echo "(No cache available, building from source)"

# Build the v4.22.0-compatible modules
echo "Building AsmInterp.Semantics..."
lake build AsmInterp.Semantics

echo "Building AsmInterp..."
lake build AsmInterp

echo ""
echo "✓ v4.22.0 compatibility test PASSED"
