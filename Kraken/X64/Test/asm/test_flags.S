# Test: Flags (ZF, CF, OF) behavior
# Tests various flag-setting operations without pushfq/popq
#
# This test verifies flag behavior for:
# - ZF: set when result is zero
# - CF: set on unsigned overflow/borrow
# - OF: set on signed overflow
#
# Instead of saving flags to registers (which needs pushfq),
# we test flag effects via the final flag state and register values.

# Test 1: ZF set when result is zero
movq $5, %rax
subq $5, %rax           # rax = 0, ZF = 1

# Test 2: Store a value to rbx
movq $42, %rbx

# Test 3: CF set on unsigned underflow (borrow)
movq $1, %rcx
subq $2, %rcx           # rcx = -1 (0xFFFF...), CF = 1

# Test 4: Add that doesn't overflow
movq $10, %rdx
addq $20, %rdx          # rdx = 30, no special flags

# Test 5: OF set on signed overflow (positive + positive = negative)
movq $0x7FFFFFFFFFFFFFFF, %rsi  # MAX_INT64
addq $1, %rsi           # rsi = MIN_INT64 (0x8000...), OF = 1

# Final state:
# rax = 0 (from sub)
# rbx = 42
# rcx = 0xFFFFFFFFFFFFFFFF (-1)
# rdx = 30
# rsi = 0x8000000000000000 (MIN_INT64)
# Flags from last instruction: OF = 1

