# Test: vmovups on zmm registers, including the upper half and zmm16..31
# Requires: avx512f

subq $0x80, %rsp
movq $0x1111111111111111, %rax
movq %rax, 0(%rsp)
movq $0x2222222222222222, %rax
movq %rax, 24(%rsp)
movq $0x3333333333333333, %rax
movq %rax, 40(%rsp)
movq $0x4444444444444444, %rax
movq %rax, 56(%rsp)

vmovups (%rsp), %zmm3
vmovups %zmm3, %zmm31
vmovups %zmm31, 64(%rsp)
movq 120(%rsp), %rbx

addq $0x80, %rsp
