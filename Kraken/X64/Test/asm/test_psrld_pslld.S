# Test: psrld and pslld shift each dword by an immediate, clear it from 32 on, and keep the bits above 128

# The stack should be dqword-aligned (so all m128 ops are OK)
subq $0x40, %rsp
movq $0x8000000112345678, %rax
movq %rax, 0(%rsp)
movq $0xffffffff7fffffff, %rax
movq %rax, 8(%rsp)
movq $0x5a5a5a5a5a5a5a5a, %rax
movq %rax, 16(%rsp)
movq %rax, 24(%rsp)
movq %rax, 32(%rsp)
movq %rax, 40(%rsp)

movdqa 0(%rsp), %xmm0
psrld $0, %xmm0
movdqa 0(%rsp), %xmm1
psrld $1, %xmm1
movdqa 0(%rsp), %xmm2
psrld $31, %xmm2
movdqa 0(%rsp), %xmm3
psrld $32, %xmm3
movdqa 0(%rsp), %xmm4
psrld $255, %xmm4

movdqa 0(%rsp), %xmm5
pslld $0, %xmm5
movdqa 0(%rsp), %xmm6
pslld $1, %xmm6
movdqa 0(%rsp), %xmm7
pslld $31, %xmm7
movdqa 0(%rsp), %xmm8
pslld $32, %xmm8
movdqa 0(%rsp), %xmm9
pslld $200, %xmm9

# Legacy SSE keeps the bits above 128, even when the count clears the low 128.
vmovdqu 16(%rsp), %ymm10
movdqa 0(%rsp), %xmm10
psrld $4, %xmm10
vmovdqu 16(%rsp), %ymm11
movdqa 0(%rsp), %xmm11
pslld $33, %xmm11
vmovdqu 16(%rsp), %ymm15
movdqa 0(%rsp), %xmm15
psrld $9, %xmm15

addq $0x40, %rsp
