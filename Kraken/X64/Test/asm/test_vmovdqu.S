# Test AVX unaligned packed integer move instruction
# Tests: vmovdqu (128-bit and 256-bit unaligned load, store, register move, upper-lane zeroing)

# Allocate 64 bytes on the 256-byte-aligned stack
pushq $11                        # 56(%rsp)
pushq $22                        # 48(%rsp)
pushq $33                        # 40(%rsp)
pushq $44                        # 32(%rsp)
pushq $55                        # 24(%rsp)
pushq $66                        # 16(%rsp)
pushq $77                        # 8(%rsp)
pushq $88                        # 0(%rsp)

# Unaligned 256-bit load and store
vmovdqu 8(%rsp), %ymm0           # loads (77, 66, 55, 44)
vmovdqu %ymm0, %ymm1
vmovdqu %ymm1, 24(%rsp)
movq 24(%rsp), %rax              # 77
movq 32(%rsp), %rbx              # 66
movq 40(%rsp), %rcx              # 55
movq 48(%rsp), %rdx              # 44

# 128-bit vmovdqu zeros upper 128 bits of ymm1
vmovdqu 8(%rsp), %xmm1

# Restore stack
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
