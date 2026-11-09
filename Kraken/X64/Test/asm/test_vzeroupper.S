# Test AVX vzeroupper instruction
# Tests: vzeroupper (zeros upper 128 bits of ymm0..ymm15 while preserving low 128 bits)

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
