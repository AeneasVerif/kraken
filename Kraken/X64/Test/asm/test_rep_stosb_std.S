# Test: with DF set, rep stosb stores al rcx times backward, stepping rdi and rcx down

subq $0x40, %rsp
movq $0, 0(%rsp)
movq $0, 8(%rsp)
movq $0, 16(%rsp)
movq $0, 24(%rsp)

std
movq $0x11223344556677aa, %rax
leaq 11(%rsp), %rdi
movq $9, %rcx
rep stosb
movq 0(%rsp), %rbx
movq 8(%rsp), %rdx

# One quadword, then a repeated word.
leaq 24(%rsp), %rdi
stosq
movq $3, %rcx
rep stosw
movq 16(%rsp), %r8
movq 24(%rsp), %r9
cld

# The pointer relative to the stack, which differs between runs.
subq %rsp, %rdi
addq $0x40, %rsp
