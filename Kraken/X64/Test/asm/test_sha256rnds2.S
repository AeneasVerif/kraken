# Test: sha256rnds2 runs two SHA-256 rounds from the initial state

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x30, %rsp
# A, B, E, F, from the top dword down.
movq $0x510e527f9b05688c, %rax
movq %rax, 0(%rsp)
movq $0x6a09e667bb67ae85, %rax
movq %rax, 8(%rsp)
# C, D, G, H, from the top dword down.
movq $0x1f83d9ab5be0cd19, %rax
movq %rax, 16(%rsp)
movq $0x3c6ef372a54ff53a, %rax
movq %rax, 24(%rsp)
# The two words plus constants; the upper half is ignored.
movq $0x9abcdef012345678, %rax
movq %rax, 32(%rsp)
movq $-1, %rax
movq %rax, 40(%rsp)

movdqa 32(%rsp), %xmm0
movdqa 0(%rsp), %xmm2
movdqa 16(%rsp), %xmm1
sha256rnds2 %xmm0, %xmm2, %xmm1
movdqa 16(%rsp), %xmm3
sha256rnds2 0(%rsp), %xmm3

addq $0x30, %rsp
