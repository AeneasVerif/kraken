# Test vector move and state instructions
# Tests: vmovaps, movdqa, vmovdqa, movdqu, vmovdqu, vzeroupper

# Allocate 64 bytes on the 256-byte-aligned stack (rsp remains 64-byte aligned)
pushq $11                        # 56(%rsp)
pushq $22                        # 48(%rsp)
pushq $33                        # 40(%rsp)
pushq $44                        # 32(%rsp)
pushq $55                        # 24(%rsp)
pushq $66                        # 16(%rsp)
pushq $77                        # 8(%rsp)
pushq $88                        # 0(%rsp)

# ----- vmovaps (256-bit load/store & 128-bit upper-lane zeroing) -----
vmovaps (%rsp), %ymm0
vmovaps %ymm0, 32(%rsp)
movq 32(%rsp), %rax              # 88
movq 40(%rsp), %rbx              # 77
movq 48(%rsp), %rcx              # 66
movq 56(%rsp), %rdx              # 55

# ----- vmovdqa (256-bit) & movdqa (128-bit legacy preserves upper 128 bits) -----
vmovdqa (%rsp), %ymm1
pushq $99
pushq $111
movdqa (%rsp), %xmm1             # updates low 128 bits of ymm1 to (111, 99), keeps high 128 bits (66, 55)
popq %rsi
popq %rsi

# ----- vmovdqu (unaligned 256-bit) & movdqu (unaligned 128-bit) -----
vmovdqu 8(%rsp), %ymm2           # loads (77, 66, 55, 88)
movdqu 8(%rsp), %xmm3            # loads (77, 66) into low 128 bits of ymm3
vmovdqu 16(%rsp), %xmm2          # loads (66, 55) and zeros upper 128 bits of ymm2

# ----- vzeroupper (zeros upper 128 bits of ymm0..ymm15, preserves low 128 bits) -----
vmovdqa (%rsp), %ymm4            # ymm4 has non-zero upper 128 bits (66, 55)
vzeroupper                       # clears upper 128 bits of ymm0..ymm15, keeps xmm0..xmm4 low 128 bits

# Restore stack
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
popq %rsi
