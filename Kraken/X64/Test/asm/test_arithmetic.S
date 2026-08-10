# Test: Arithmetic Operations
# Tests: addq, subq, adcq, sbbq, negq, decq

# Test addq
movq $10, %rax
addq $5, %rax           # rax = 15

# Test subq
movq $20, %rbx
subq $7, %rbx           # rbx = 13

# Test adcq (add with carry)
xorq %rcx, %rcx         # Clear rcx and CF
movq $3, %rcx
addq $2, %rcx           # rcx = 5, CF = 0
adcq $1, %rcx           # rcx = 5 + 1 + 0 = 6

# Test negq
movq $42, %rdx
negq %rdx               # rdx = -42 (two's complement)

# Test decq
movq $100, %rsi
decq %rsi               # rsi = 99

# Test sbbq (subtract with borrow)
movq $10, %rdi
subq $20, %rdi          # rdi = -10, CF = 1
movq $100, %r8
sbbq $5, %r8            # r8 = 100 - 5 - 1 = 94

# Test adcxq (ADX: add with carry, only affects CF)
xorq %r9, %r9
movq $0xFFFFFFFFFFFFFFFF, %r9
addq $1, %r9            # r9 = 0, CF = 1
movq $10, %r10
adcxq %r9, %r10         # r10 = 10 + 0 + 1 = 11

# Test adoxq (ADX: add with overflow flag)
xorq %r11, %r11
movq $5, %r11
adoxq %r9, %r11         # r11 = 5 + 0 + OF (OF from prev)

# Test mulxq (BMI2: mulxq src, lo, hi means hi:lo = rdx * src)
movq $100, %rdx
movq $3, %r12
mulxq %r12, %r13, %r14  # r14:r13 = 100 * 3 = 300 (r13=300, r14=0)

# Test cmpq (64-bit compare)
movq $50, %r15
cmpq $50, %r15          # Should set ZF=1
