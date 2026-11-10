# Undefined flags: cf, pf, af, zf, sf, of

# 64 bits: rdx:rax = 5 * 2^64 + 123
movq $5, %rdx
movq $123, %rax
movabsq $0x1234567890, %rbx
divq %rbx
movq %rax, %r8
movq %rdx, %r9

# 32 bits: the dividend is edx:eax, and the upper halves of rax and rdx are cleared
movabsq $0xdeadbeef00000003, %rdx
movabsq $0xcafebabe12345678, %rax
movl $0x10000, %ecx
divl %ecx
movq %rax, %r10
movq %rdx, %r11

# 16 bits: the dividend is dx:ax, and the rest of rax and rdx is preserved
movabsq $0x1111111111110012, %rdx
movabsq $0x2222222222223456, %rax
movw $0x1234, %si
divw %si
movq %rax, %r12
movq %rdx, %r13

# 8 bits: ax = 1000; quotient to al, remainder to ah, rdx untouched
movabsq $0x33333333333303e8, %rax
movb $7, %bl
divb %bl
movq %rax, %r14

# Memory operands
movq $1000003, -8(%rsp)
movq $0, %rdx
movabsq $0x123456789abcdef, %rax
divq -8(%rsp)
movq %rax, %r15
movb $200, -16(%rsp)
movw $50000, %ax
divb -16(%rsp)
