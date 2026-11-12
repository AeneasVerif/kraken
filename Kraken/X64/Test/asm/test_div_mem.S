# Undefined flags: cf, of, sf, zf, af, pf

# Test: div at every width with a memory divisor

subq $0x20, %rsp
movabsq $0xfedcba9876543210, %rcx
movq %rcx, 0(%rsp)

# 64 bits: (2^64 + 7) over 0xfedcba9876543210.
movq $1, %rdx
movq $7, %rax
divq 0(%rsp)
movq %rax, %r8
movq %rdx, %r9

# 32 bits: the divisor is 0x76543210.
movl $0x12345678, %edx
movl $0x9abcdef0, %eax
divl 0(%rsp)
movq %rax, %r10
movq %rdx, %r11

# 16 bits: the divisor is 0x3210.
movw $0x0abc, %dx
movw $0xdef0, %ax
divw 0(%rsp)
movq %rax, %r12
movq %rdx, %r13

# 8 bits: the divisor is the byte 0xba.
movw $0x7fff, %ax
divb 5(%rsp)
movq %rax, %r14

addq $0x20, %rsp
