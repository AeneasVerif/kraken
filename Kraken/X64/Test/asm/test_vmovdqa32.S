# Test: vmovdqa32 on aligned 64-, 32-, and 16-byte operands
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

vmovdqa32 0(%rsp), %zmm0
vmovdqa32 %zmm0, 128(%rsp)
vmovdqa32 32(%rsp), %ymm1
vmovdqa32 48(%rsp), %xmm2
vmovdqa32 %zmm0, %zmm31
movq 184(%rsp), %rdx

addq $0x100, %rsp
