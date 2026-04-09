#!/bin/bash
# Run all assembly tests comparing AS execution against Kraken's eval
# Usage: ./run_all_asm_tests.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ASM_TESTS_DIR="$SCRIPT_DIR/../asm-tests"

PASSED=0
FAILED=0
FAILED_TESTS=""

echo "========================================"
echo "Kraken Assembly Test Suite"
echo "========================================"
echo ""

for test_file in "$ASM_TESTS_DIR"/test_*.S; do
    name=$(basename "${test_file%.S}")
    echo -n "Running $name... "

    if "$SCRIPT_DIR/run_asm_test.sh" "$test_file" > /tmp/test_output.txt 2>&1; then
        if grep -q "^PASS" /tmp/test_output.txt; then
            echo "✓"
            PASSED=$((PASSED + 1))
        else
            echo "✗"
            FAILED=$((FAILED + 1))
            FAILED_TESTS="$FAILED_TESTS\n  $name: $result"
        fi
    else
        echo "✗ (execution error)"
        FAILED=$((FAILED + 1))
        FAILED_TESTS="$FAILED_TESTS\n  $name: $(cat /tmp/test_output.txt)"
    fi
done

echo ""
echo "========================================"
echo "Results: $PASSED passed, $FAILED failed"
echo "========================================"

if [ $FAILED -gt 0 ]; then
    echo -e "\nFailed tests:$FAILED_TESTS"
    exit 1
fi

exit 0
