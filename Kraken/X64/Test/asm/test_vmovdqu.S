# Test: vmovdqu loads, stores, and copies 16 or 32 bytes, unaligned, clearing the rest

subq $0x60, %rsp
vmovdqu (%rsp), %ymm0
movq $0x1122334455667788, %rax
movq %rax, 3(%rsp)
movq $0x99aabbccddeeff00, %rax
movq %rax, 11(%rsp)

vmovdqu 3(%rsp), %xmm0
vmovdqu 1(%rsp), %ymm1
vmovdqu %ymm1, %ymm2
vmovdqu %xmm0, %xmm3
vmovdqu %ymm1, 37(%rsp)
movq 37(%rsp), %rbx
movq 45(%rsp), %rcx
movq 53(%rsp), %rdx
movq 61(%rsp), %rsi

addq $0x60, %rsp

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
