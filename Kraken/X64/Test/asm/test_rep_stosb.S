# Test: rep stosb stores al rcx times forward, stepping rdi up and rcx down

subq $0x40, %rsp
movq $0, 0(%rsp)
movq $0, 8(%rsp)
movq $0, 16(%rsp)

movq $0x11223344556677aa, %rax
leaq 3(%rsp), %rdi
movq $9, %rcx
rep stosb
movq 0(%rsp), %rbx
movq 8(%rsp), %rdx

# A zero count stores nothing.
movq $0, %rcx
rep stosb

# One quadword, then a repeated word.
leaq 16(%rsp), %rdi
stosq
movq $3, %rcx
rep stosw
movq 16(%rsp), %r8
movq 24(%rsp), %r9

# The pointer relative to the stack, which differs between runs.
subq %rsp, %rdi
addq $0x40, %rsp
