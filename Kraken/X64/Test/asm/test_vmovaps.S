# Test AVX aligned packed single-precision move instruction
# Tests: vmovaps (128-bit and 256-bit load, store, register move, upper-lane zeroing)

# Allocate 64 bytes on the 256-byte-aligned stack (rsp remains 64-byte aligned)
pushq $11                        # 56(%rsp)
pushq $22                        # 48(%rsp)
pushq $33                        # 40(%rsp)
pushq $44                        # 32(%rsp)
pushq $55                        # 24(%rsp)
pushq $66                        # 16(%rsp)
pushq $77                        # 8(%rsp)
pushq $88                        # 0(%rsp)

vmovaps (%rsp), %ymm0
vmovaps %ymm0, %ymm1
vmovaps %ymm1, 32(%rsp)
movq 32(%rsp), %rax              # 88
movq 40(%rsp), %rbx              # 77
movq 48(%rsp), %rcx              # 66
movq 56(%rsp), %rdx              # 55

# 128-bit vmovaps zeros upper 128 bits of ymm1
vmovaps 16(%rsp), %xmm1

# Restore stack
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
