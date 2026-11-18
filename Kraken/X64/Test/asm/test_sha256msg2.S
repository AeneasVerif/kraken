# Test: sha256msg2 finishes four schedule words, each new word feeding the one two places on

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x20, %rsp
# The partial sums.
movq $0x1111111122222222, %rax
movq %rax, 0(%rsp)
movq $0x3333333344444444, %rax
movq %rax, 8(%rsp)
# Words 14 and 15 in the two top dwords; the rest is ignored.
movq $-1, %rax
movq %rax, 16(%rsp)
movq $0x0000000180000018, %rax
movq %rax, 24(%rsp)

movdqa 0(%rsp), %xmm0
movdqa 16(%rsp), %xmm1
sha256msg2 %xmm1, %xmm0
movdqa 0(%rsp), %xmm2
sha256msg2 16(%rsp), %xmm2

addq $0x20, %rsp
