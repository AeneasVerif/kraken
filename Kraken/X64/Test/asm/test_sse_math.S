# Test: SSE legacy math insns

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x20, %rsp
movl $0xbf800000, 28(%rsp)  # -1.0f
movl $0x3f800000, 24(%rsp)  # 1.0f
movl $0x3f800000, 20(%rsp)  # 1.0f
movl $0xbf800000, 16(%rsp)  # -1.0f  <-1.0f, 1.0f, 1.0f, -1.0f>
movl $0x3f800000, 12(%rsp)  # 1.0f
movl $0x40000000, 8(%rsp)   # 2.0f
movl $0x3fc00000, 4(%rsp)   # 1.5f
movl $0x3f000000, 0(%rsp)   # 0.5f   <0.5f, 1.5f, 2.0f, 1.0f>

movaps 0(%rsp), %xmm0
movaps 0(%rsp), %xmm1
movaps 16(%rsp), %xmm2
addps %xmm1, %xmm2

movaps 0(%rsp), %xmm3
movaps 0(%rsp), %xmm4
movaps 16(%rsp), %xmm5
subps %xmm4, %xmm5

addq $0x20, %rsp
