# Undefined flags: af, sf, zf, pf

# Test: IMUL Variants (Regression test for parser backtracking bug and single-operand support)
#
# Expected results:
#   rax = -45 (after test 5)
#   rbx = 50 (imulq 3-operand)
#   r8 = 48 (imul 2-operand unsuffixed)
#   rdx = -1 (after test 5)

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

# 4. Test 1-operand suffixed
movq $5, %rax
movq $9, %rcx
imulq %rcx
# Expected: rax = 45, rdx = 0

# 5. Test 1-operand unsuffixed (negative)
movq $-5, %rax
movq $9, %r10
imul %r10
# Expected: rax = -45, rdx = -1
