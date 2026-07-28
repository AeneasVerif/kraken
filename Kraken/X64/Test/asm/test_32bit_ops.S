# Undefined flags: af, of

# Test 32-bit arithmetic and bitwise operations
# Tests: addl, subl, negl, xorl, andl, orl
#
# Expected final values:
#   rax: result of xorl %eax, %eax = 0
#   rbx: result of 32-bit ops
#   rcx: 50 (from subl test)

# ----- 32-bit addition (addl) -----
movl $10, %eax
movl $5, %ebx
addl %ebx, %eax
# Expected: eax = 15

# Test zero-extension
movq $0xFFFFFFFFFFFFFFFF, %rcx
movl $1, %ecx           # Clears upper 32 bits
addl $1, %ecx
# Expected: rcx = 2 (zero-extended)

# ----- 32-bit subtraction (subl) -----
movl $100, %edx
subl $50, %edx
# Expected: edx = 50

# ----- 32-bit XOR (xorl) -----
movl $0xAAAAAAAA, %esi
xorl $0x55555555, %esi
# Expected: esi = 0xFFFFFFFF

# Common pattern: xorl %eax, %eax clears register
xorl %eax, %eax
# Expected: eax = 0

# ----- 32-bit AND (andl) -----
movl $0xFFFF0000, %edi
andl $0x0000FFFF, %edi
# Expected: edi = 0

# ----- 32-bit OR (orl) -----
movl $0xFF00FF00, %r8d
orl $0x00FF00FF, %r8d
# Expected: r8 = 0xFFFFFFFF

# ----- 32-bit negate (negl) -----
movl $42, %r9d
negl %r9d
# Expected: r9d = -42 (two's complement, zero-extended)

# ----- 32-bit NOT (notl) -----
movl $0xAAAAAAAA, %r10d
notl %r10d
# Expected: r10d = 0x55555555

# ----- 32-bit decrement (decl) -----
movl $100, %r11d
decl %r11d
# Expected: r11d = 99

# ----- 32-bit LEA (leal) -----
movq $10, %r12
leal 5(%r12), %r13d
# Expected: r13 = 15 (zero-extended)

# ----- 32-bit compare (cmpl) -----
movl $50, %r14d
cmpl $50, %r14d
# Expected: ZF=1

# ----- 32-bit shift left (shll) -----
movl $1, %r15d
shll $4, %r15d
# Expected: r15d = 16
