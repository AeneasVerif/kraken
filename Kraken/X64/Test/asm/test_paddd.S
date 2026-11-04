# Test: paddd adds four dwords, each wrapping on its own

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x20, %rsp
movq $0x00000001ffffffff, %rax
movq %rax, 0(%rsp)
movq $0x7fffffff80000000, %rax
movq %rax, 8(%rsp)
movq $0x0000000100000001, %rax
movq %rax, 16(%rsp)
movq $0x0000000180000000, %rax
movq %rax, 24(%rsp)

movdqa 0(%rsp), %xmm0
movdqa 16(%rsp), %xmm1
paddd %xmm1, %xmm0
movdqa 0(%rsp), %xmm2
paddd 16(%rsp), %xmm2

addq $0x20, %rsp
