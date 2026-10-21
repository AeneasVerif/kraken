# Test: pshufd picks each dword by two bits of the immediate

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x10, %rsp
movq $0x2222222211111111, %rax
movq %rax, 0(%rsp)
movq $0x4444444433333333, %rax
movq %rax, 8(%rsp)

movdqa 0(%rsp), %xmm0
pshufd $0x1b, %xmm0, %xmm1
pshufd $0xb1, %xmm0, %xmm2
pshufd $0x0e, 0(%rsp), %xmm3
pshufd $0x00, %xmm0, %xmm4
# A negative immediate is its low byte: -1 picks dword 3 everywhere.
pshufd $-1, %xmm0, %xmm5

addq $0x10, %rsp
