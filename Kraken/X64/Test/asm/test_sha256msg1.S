# Test: sha256msg1 adds to each word the mixing of the word after it

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x20, %rsp
# Words 0 to 3.
movq $0x8000000061626380, %rax
movq %rax, 0(%rsp)
movq $0x0123456789abcdef, %rax
movq %rax, 8(%rsp)
# Word 4 in the low dword; the rest is ignored.
movq $0xffffffffdeadbeef, %rax
movq %rax, 16(%rsp)
movq $-1, %rax
movq %rax, 24(%rsp)

movdqa 0(%rsp), %xmm0
movdqa 16(%rsp), %xmm1
sha256msg1 %xmm1, %xmm0
movdqa 0(%rsp), %xmm2
sha256msg1 16(%rsp), %xmm2

addq $0x20, %rsp
