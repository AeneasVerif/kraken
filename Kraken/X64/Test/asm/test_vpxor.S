# Test: vpxor XORs at 128 and 256 bits, zeroing the bits above

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


vmovdqu 0(%rsp), %ymm0
vmovdqu 32(%rsp), %ymm1
vmovdqu 64(%rsp), %ymm15
vpxor %ymm1, %ymm0, %ymm2
vpxor 64(%rsp), %ymm0, %ymm3
vpxor 96(%rsp), %ymm1, %ymm4
vmovdqu %ymm15, %ymm5
vpxor %xmm1, %xmm0, %xmm5
vmovdqu %ymm15, %ymm6
vpxor 64(%rsp), %xmm0, %xmm6
vmovdqu %ymm15, %ymm7
vpxor %ymm7, %ymm7, %ymm7

addq $0x100, %rsp
