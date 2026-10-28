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
