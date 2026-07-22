# Test: movups on AVX registers
#
# Need to check xmm status

# The stack should be dqword-aligned.
pushq %rax  # 24
pushq %rax  # 16
pushq $42   # 8
pushq $43   # 0

# Test legacy movups (non-zeroing); note size suffixes aren't used and only the xmms work.
movups (%rsp), %xmm0
movups %xmm0, 16(%rsp)
movq 16(%rsp), %rsi  # 43
movq 24(%rsp), %rdi  # 42

# Test avx vmovups (zeroing)
# addq $16, %rsp  # causes a disagreement about pf and sf?
popq %rcx
popq %rcx
pushq $44
pushq $45
vmovups (%rsp), %xmm1
vmovups %xmm1, 16(%rsp)
movq 16(%rsp), %rcx  # 45
movq 24(%rsp), %rdx  # 44

# Test avx vmovups with ymms
popq %rcx
popq %rcx
popq %rcx
popq %rcx

pushq %rax  # 0x38
pushq %rax  # 0x30
pushq %rax  # 0x28
pushq %rax  # 0x20
pushq $10   # 0x18
pushq $11   # 0x10
pushq $12   # 0x8
pushq $13   # 0x0

vmovups (%rsp), %ymm2
vmovups %ymm2, 0x20(%rsp)
movq 0x20(%rsp), %r13  # 13
movq 0x28(%rsp), %r12  # 12
movq 0x30(%rsp), %r11  # 11
movq 0x38(%rsp), %r10  # 10

# TODO: zmms neeed avx512 support in the test harness
