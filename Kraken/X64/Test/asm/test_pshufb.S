# Test: pshufb picks bytes by index, and zeroes a byte whose index has its top bit set

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x20, %rsp
movq $0x0706050403020100, %rax
movq %rax, 0(%rsp)
movq $0x0f0e0d0c0b0a0908, %rax
movq %rax, 8(%rsp)
# Indices: reversal in the low half; zeroing, wrapping, and repeats in the high half.
movq $0x08090a0b0c0d0e0f, %rax
movq %rax, 16(%rsp)
movq $0x8011ff1f00000000, %rax
movq %rax, 24(%rsp)

movdqa 0(%rsp), %xmm0
movdqa 16(%rsp), %xmm1
pshufb %xmm1, %xmm0
movdqa 0(%rsp), %xmm2
pshufb 16(%rsp), %xmm2

addq $0x20, %rsp
