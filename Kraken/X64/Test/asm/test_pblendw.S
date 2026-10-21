# Test: pblendw takes each word from the source where its immediate bit is set

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x20, %rsp
movq $0x1111111111111111, %rax
movq %rax, 0(%rsp)
movq %rax, 8(%rsp)
movq $0x2222222222222222, %rax
movq %rax, 16(%rsp)
movq %rax, 24(%rsp)

movdqa 0(%rsp), %xmm0
movdqa 16(%rsp), %xmm1
pblendw $0xf0, %xmm1, %xmm0
movdqa 0(%rsp), %xmm2
pblendw $0x5a, 16(%rsp), %xmm2
# A negative immediate is its low byte: -128 takes word 7 only.
movdqa 0(%rsp), %xmm3
pblendw $-128, %xmm1, %xmm3

addq $0x20, %rsp
