# Test: pxor, pand and pandn combine 128 bits, and keep the bits above them

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x40, %rsp
movq $0x0123456789abcdef, %rax
movq %rax, 0(%rsp)
movq $0xfedcba9876543210, %rax
movq %rax, 8(%rsp)
movq $0x00ff00ff0f0f0f0f, %rax
movq %rax, 16(%rsp)
movq $0xffff0000aaaa5555, %rax
movq %rax, 24(%rsp)
movq $0x5a5a5a5a5a5a5a5a, %rax
movq %rax, 32(%rsp)
movq %rax, 40(%rsp)
movq %rax, 48(%rsp)
movq %rax, 56(%rsp)

movdqa 16(%rsp), %xmm1

movdqa 0(%rsp), %xmm0
pxor %xmm1, %xmm0
movdqa 0(%rsp), %xmm2
pxor 16(%rsp), %xmm2

movdqa 0(%rsp), %xmm3
pand %xmm1, %xmm3
movdqa 0(%rsp), %xmm4
pand 16(%rsp), %xmm4

# pandn complements the destination, not the source.
movdqa 0(%rsp), %xmm5
pandn %xmm1, %xmm5
movdqa 0(%rsp), %xmm6
pandn 16(%rsp), %xmm6

# A register with itself: pxor and pandn clear it, pand keeps it.
movdqa 0(%rsp), %xmm7
pxor %xmm7, %xmm7
movdqa 0(%rsp), %xmm8
pandn %xmm8, %xmm8
movdqa 0(%rsp), %xmm9
pand %xmm9, %xmm9

# Legacy SSE keeps the bits above 128.
vmovdqu 32(%rsp), %ymm10
pxor %xmm1, %xmm10
vmovdqu 32(%rsp), %ymm11
pand %xmm1, %xmm11
vmovdqu 32(%rsp), %ymm12
pandn %xmm1, %xmm12

addq $0x40, %rsp
