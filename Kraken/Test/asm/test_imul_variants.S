# Undefined flags: af, sf, zf, pf

# Test: IMUL Variants (Regression test for parser backtracking bug)
#
# Expected results:
#   rax = 35 (imulq 2-operand)
#   rbx = 50 (imulq 3-operand)
#   r8 = 48 (imul 2-operand unsuffixed)

# 1. Test 2-operand suffixed (This used to fail if attempt was missing)
movq $5, %rax
movq $7, %rdx
imulq %rdx, %rax

# 2. Test 3-operand suffixed
movq $5, %rcx
imulq $10, %rcx, %rbx

# 3. Test 2-operand unsuffixed
movq $6, %r8
movq $8, %r9
imul %r9, %r8

# Restore rax for output consistency if needed, but state check verifies all registers.
