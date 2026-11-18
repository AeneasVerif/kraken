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
