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
