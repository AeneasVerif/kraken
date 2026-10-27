# Test: vpsrld shifts each dword right by an immediate, and a count above 31 gives zero
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
vpsrld $3, %zmm0, %zmm1
vpsrld $10, 64(%rsp), %zmm2
vpsrld $31, %zmm0, %zmm3
vpsrld $32, %zmm0, %zmm4
vpsrld $200, %zmm0, %zmm5
vpsrld $0, %zmm0, %zmm6
vpsrld $7, %ymm0, %ymm7
vpsrld $7, %xmm0, %xmm8

addq $0x100, %rsp
