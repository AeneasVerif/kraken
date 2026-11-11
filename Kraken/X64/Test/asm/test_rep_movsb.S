# Test: rep movsb copies rcx bytes forward, stepping rsi and rdi up and rcx down

subq $0x40, %rsp
movq $0x0706050403020100, %rax
movq %rax, 0(%rsp)
movq $0x0f0e0d0c0b0a0908, %rax
movq %rax, 8(%rsp)

# Eleven bytes, to a separate buffer.
leaq 0(%rsp), %rsi
leaq 0x20(%rsp), %rdi
movq $11, %rcx
rep movsb
movq 0x20(%rsp), %rbx
movq 0x28(%rsp), %rdx

# A zero count copies nothing and moves no register.
movq $0, %rcx
rep movsb

# Overlapping, one byte up: a forward byte loop repeats the first byte.
leaq 0(%rsp), %rsi
leaq 1(%rsp), %rdi
movq $6, %rcx
rep movsb
movq 0(%rsp), %r8

# One quadword, without a prefix.
leaq 8(%rsp), %rsi
leaq 0x30(%rsp), %rdi
movsq
movq 0x30(%rsp), %r9

# The pointers relative to the stack, which differs between runs.
subq %rsp, %rsi
subq %rsp, %rdi
addq $0x40, %rsp
