# Test: palignr shifts the destination above the source right by whole bytes

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x20, %rsp
movq $0x0706050403020100, %rax
movq %rax, 0(%rsp)
movq $0x0f0e0d0c0b0a0908, %rax
movq %rax, 8(%rsp)
movq $0x1716151413121110, %rax
movq %rax, 16(%rsp)
movq $0x1f1e1d1c1b1a1918, %rax
movq %rax, 24(%rsp)

# Shifts inside the source, across both, inside the destination, and past both.
movdqa 16(%rsp), %xmm0
palignr $4, 0(%rsp), %xmm0
movdqa 16(%rsp), %xmm1
movdqa 0(%rsp), %xmm5
palignr $8, %xmm5, %xmm1
movdqa 16(%rsp), %xmm2
palignr $20, %xmm5, %xmm2
movdqa 16(%rsp), %xmm3
palignr $32, %xmm5, %xmm3

addq $0x20, %rsp
