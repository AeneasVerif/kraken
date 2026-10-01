# Test: SSE NaN propagation. A NaN operand propagates quieted (the destination winning), and an
# invalid operation (inf - inf) gives the default NaN 0xffc00000.
subq $0x20, %rsp
movl $0x3f800000, 28(%rsp)  # 1.0f
movl $0x7f800000, 24(%rsp)  # +inf
movl $0x3f800000, 20(%rsp)  # 1.0f
movl $0x7f800001, 16(%rsp)  # SNaN   <SNaN, 1.0f, +inf, 1.0f>
movl $0x3f800000, 12(%rsp)  # 1.0f
movl $0xff800000, 8(%rsp)   # -inf
movl $0xffc12345, 4(%rsp)   # QNaN
movl $0x7fc00042, 0(%rsp)   # QNaN   <QNaN, QNaN, -inf, 1.0f>

movaps 16(%rsp), %xmm0
movaps 0(%rsp), %xmm1
addps %xmm1, %xmm0          # <0x7fc00001, 0xffc12345, 0xffc00000, 2.0f>
movaps 16(%rsp), %xmm2
subps %xmm1, %xmm2          # <0x7fc00001, 0xffc12345, +inf, 0.0f>
movaps 0(%rsp), %xmm3
addps 16(%rsp), %xmm3       # <0x7fc00042, 0xffc12345, 0xffc00000, 2.0f>

addq $0x20, %rsp
