# Test: vmovd moves 32 bits between a vector register and a GPR or memory, clearing the rest

# The stack is filled with 0xff, so these loads set every bit of ymm0 to ymm2.
subq $0x40, %rsp
vmovdqu (%rsp), %ymm0
vmovdqu (%rsp), %ymm1
vmovdqu (%rsp), %ymm2
movq $0x1122334455667788, %rax
movl $0x0badf00d, 8(%rsp)

vmovd %eax, %xmm0
vmovd 8(%rsp), %xmm1
vmovd %xmm0, %r9d
vmovd %xmm1, 16(%rsp)
movq 16(%rsp), %r10

addq $0x40, %rsp
