# Undefined flags: cf, pf, af, zf, sf, of

# 64 bits: the quotient rounds towards zero, the remainder has the dividend's sign
movq $-1000000007, %rax
movq $-1, %rdx
movq $10, %rbx
idivq %rbx
movq %rax, %r8
movq %rdx, %r9

# 64 bits: positive dividend 2^64 + 7, negative divisor
movq $7, %rax
movq $1, %rdx
movq $-3, %rbx
idivq %rbx
movq %rax, %r10
movq %rdx, %r11

# 32 bits: edx:eax = -2^32, quotient -2^31 still fits; the upper halves are cleared
movabsq $0x12345678ffffffff, %rdx
movabsq $0x9abcdef000000000, %rax
movl $2, %ecx
idivl %ecx
movq %rax, %r12
movq %rdx, %r13

# 16 bits: dx:ax = -30000, divisor -7
movw $-1, %dx
movw $-30000, %ax
movw $-7, %si
idivw %si
movq %rax, %r14
movq %rdx, %r15

# 8 bits: ax = -100, divisor 7
movw $-100, %ax
movb $7, %bl
idivb %bl
movq %rax, %rdi

# Memory operand, 8 bits: ax = -256, quotient -128 still fits
movb $2, -8(%rsp)
movw $-256, %ax
idivb -8(%rsp)
movq %rax, %rbp

# Memory operand, 32 bits: edx:eax = -7, divisor 2
movl $2, -16(%rsp)
movl $-1, %edx
movl $-7, %eax
idivl -16(%rsp)
