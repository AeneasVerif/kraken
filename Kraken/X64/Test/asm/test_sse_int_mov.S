# Test: SSE2 integer moves, aligned and unaligned

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x40, %rsp
movq $0x1122334455667788, %rax
movq %rax, 0(%rsp)
movq $0x99aabbccddeeff00, %rax
movq %rax, 8(%rsp)

movdqa 0(%rsp), %xmm0
movdqu 4(%rsp), %xmm1
movdqa %xmm0, 16(%rsp)
movdqu %xmm1, 33(%rsp)
movdqa %xmm1, %xmm2
movq 16(%rsp), %rbx
movq 24(%rsp), %rcx
movq 33(%rsp), %rdx
movq 41(%rsp), %rsi

addq $0x40, %rsp
