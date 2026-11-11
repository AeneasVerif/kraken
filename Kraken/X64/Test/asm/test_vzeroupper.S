# Test: vzeroupper clears bits 128 and up of every register, keeping the low 128

# The stack is filled with 0xff: set every bit, then a known low half.
subq $0x40, %rsp
movq $0x1122334455667788, %rax
movq %rax, 0(%rsp)
vmovdqu 32(%rsp), %ymm0
vmovdqu 32(%rsp), %ymm7
vmovdqu 32(%rsp), %ymm15
vmovdqu 0(%rsp), %ymm8

vzeroupper

addq $0x40, %rsp

pushq $55                        # 24(%rsp)
pushq $66                        # 16(%rsp)
pushq $77                        # 8(%rsp)
pushq $88                        # 0(%rsp)

vmovdqa (%rsp), %ymm0            # ymm0 has non-zero upper 128 bits (66, 55) and low 128 bits (88, 77)
vmovdqa (%rsp), %ymm15           # ymm15 has non-zero upper 128 bits (66, 55) and low 128 bits (88, 77)
vzeroupper                       # clears upper 128 bits of ymm0..ymm15, preserves xmm0..xmm15

popq %rsi
popq %rsi
popq %rsi
popq %rsi
