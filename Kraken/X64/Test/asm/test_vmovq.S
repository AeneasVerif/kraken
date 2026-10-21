# Test: vmovq moves 64 bits between a vector register and a GPR, memory, or another vector register

# The stack is filled with 0xff, so these loads set every bit of ymm0 to ymm3.
subq $0x40, %rsp
vmovdqu (%rsp), %ymm0
vmovdqu (%rsp), %ymm1
vmovdqu (%rsp), %ymm2
vmovdqu (%rsp), %ymm3
movq $0x1122334455667788, %rax
movq $0x0badf00ddeadbeef, %rbx
movq %rbx, 8(%rsp)

vmovq %rax, %xmm0
vmovq 8(%rsp), %xmm1
vmovq %xmm3, %xmm2
vmovq %xmm0, %r9
vmovq %xmm1, 24(%rsp)
movq 24(%rsp), %r10
movq 32(%rsp), %r11

addq $0x40, %rsp
