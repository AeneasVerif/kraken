# Test: with DF set, rep movsb copies rcx bytes backward, stepping rsi and rdi down and rcx down

subq $0x40, %rsp
movq $0x0706050403020100, %rax
movq %rax, 0(%rsp)
movq $0x0f0e0d0c0b0a0908, %rax
movq %rax, 8(%rsp)
movq $0, 0x20(%rsp)
movq $0, 0x28(%rsp)

# Eleven bytes, from the last byte of each buffer down.
std
leaq 10(%rsp), %rsi
leaq 0x2a(%rsp), %rdi
movq $11, %rcx
rep movsb
movq 0x20(%rsp), %rbx
movq 0x28(%rsp), %rdx

# Overlapping, one byte up: a backward byte loop shifts without repeating.
leaq 5(%rsp), %rsi
leaq 6(%rsp), %rdi
movq $6, %rcx
rep movsb
movq 0(%rsp), %r8

# One quadword, without a prefix.
leaq 8(%rsp), %rsi
leaq 0x30(%rsp), %rdi
movsq
movq 0x30(%rsp), %r9
cld

# The pointers relative to the stack, which differs between runs.
subq %rsp, %rsi
subq %rsp, %rdi
addq $0x40, %rsp
