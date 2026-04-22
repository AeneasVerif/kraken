# Undefined flags: af, sf, zf, pf

# Test: IMUL Variants (Regression test for parser backtracking bug and single-operand support)
#
# Expected results:
#   rbx = 50 (imulq 3-operand)
#   r8 = 48 (imul 2-operand unsuffixed)
#   r11 = 1 (Test 6 CF)
#   r13 = 0 (Test 7 CF)
#   r15 = 1 (Test 8 CF)
#   rax = 0 (Test 8 low 32 bits)
#   rdx = 1 (Test 8 high 32 bits)

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

# setc is used to save the carry flag accross these tests
# so they can all be checked at the end
# 6. Test 8-bit imul with overflow
movb $100, %al
movb $10, %cl
xorq %r11, %r11
imul %cl
setc %r11b

# 7. Test 16-bit imul without overflow
movw $100, %ax
movw $10, %cx
xorq %r13, %r13
imul %cx
setc %r13b

# 8. Test 32-bit imul with overflow
movl $0x10000, %eax
movl $0x10000, %ecx
xorq %r15, %r15
imul %ecx
setc %r15b
