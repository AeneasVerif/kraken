# Undefined flags: cf, of, sf, zf, af, pf

# Test: div at every width with a register divisor

# 64 bits: rdx:rax = rbx * (2^64 - 1) + (rbx - 1), so the quotient is exactly the maximum.
movabsq $0x123456789abcdef0, %rbx
movabsq $0x123456789abcdeef, %rdx
movq $-1, %rax
divq %rbx
movq %rax, %r8
movq %rdx, %r9

# 32 bits: the upper halves of rax and rdx are ignored on input and cleared on output.
movabsq $0xaaaaaaaa00000006, %rax
movabsq $0xbbbbbbbb00000001, %rdx
movl $3, %ecx
divl %ecx
movq %rax, %r10
movq %rdx, %r11

# 16 bits: dx:ax = 0x0001ffff over 0x1234, bits above 16 kept.
movabsq $0x111111111111ffff, %rax
movabsq $0x2222222222220001, %rdx
movw $0x1234, %si
divw %si
movq %rax, %r12
movq %rdx, %r13

# 8 bits: ax = 0x01ff over 2, quotient 0xff in al, remainder 1 in ah, bits above 16 kept.
movabsq $0x33333333333301ff, %rax
movb $2, %dil
divb %dil
movq %rax, %r14

# An exact division leaves a zero remainder.
movq $0, %rdx
movq $1000000, %rax
movq $1000, %r15
divq %r15
