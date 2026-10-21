# Test: vpternlogd computes a bitwise function of three registers from its truth table
# Requires: avx512f

subq $0x100, %rsp
movq $0x0123456789abcdef, %rax
movq $0xfedcba9876543210, %rbx
movq %rax, 0(%rsp)
movq %rbx, 8(%rsp)
movq $0x00000001ffffffff, %rcx
movq %rcx, 16(%rsp)
movq $0x7fffffff80000000, %rcx
movq %rcx, 24(%rsp)
movq %rbx, 32(%rsp)
movq %rax, 40(%rsp)
movq $0x8000000080000000, %rcx
movq %rcx, 48(%rsp)
movq $0x0000000100000003, %rcx
movq %rcx, 56(%rsp)
movq $0xf0f0f0f0f0f0f0f0, %rcx
movq %rcx, 64(%rsp)
movq %rcx, 72(%rsp)
movq %rax, 80(%rsp)
movq %rbx, 88(%rsp)
movq $0x5555555555555555, %rcx
movq %rcx, 96(%rsp)
movq %rax, 104(%rsp)
movq %rbx, 112(%rsp)
movq $0xffffffff00000000, %rcx
movq %rcx, 120(%rsp)

vmovdqu32 0(%rsp), %zmm0
vmovdqu32 64(%rsp), %zmm1
vmovdqu32 4(%rsp), %zmm2
vmovdqu32 %zmm0, %zmm3
vpternlogd $0xca, %zmm2, %zmm1, %zmm3
vmovdqu32 %zmm0, %zmm4
vpternlogd $0x96, %zmm2, %zmm1, %zmm4
vmovdqu32 %zmm0, %zmm5
vpternlogd $0xe8, 64(%rsp), %zmm2, %zmm5
vmovdqu32 %zmm0, %zmm6
vpternlogd $0x00, %zmm2, %zmm1, %zmm6
vmovdqu32 %zmm0, %zmm7
vpternlogd $0xff, %zmm2, %zmm1, %zmm7
vmovdqu32 %zmm0, %zmm8
vpternlogd $0x5b, %ymm2, %ymm1, %ymm8
vmovdqu32 %zmm0, %zmm9
vpternlogd $0x2c, %xmm2, %xmm1, %xmm9

addq $0x100, %rsp
