# Test: cpuid zero-extends its four 32-bit outputs and leaves every other register and the flags
# alone. The answer itself depends on the processor, so only the upper halves of rax, rbx, rcx and
# rdx are kept, read back through the stack because a shift would change the flags.

movabsq $0x1111111111111111, %rsi
movabsq $0x2222222222222222, %rdi
movabsq $0x8888888888888888, %r8
movabsq $0x9999999999999999, %r9
movabsq $0xaaaaaaaaaaaaaaaa, %r10
movabsq $0xbbbbbbbbbbbbbbbb, %r11
movabsq $0xcccccccccccccccc, %r12
movabsq $0xdddddddddddddddd, %r13
movabsq $0xeeeeeeeeeeeeeeee, %r14
movabsq $0xf0f0f0f0f0f0f0f0, %r15
movabsq $0xf0f0f0f0f0f0f0f0, %rbx
movabsq $0xf0f0f0f0f0f0f0f0, %rdx

# A mix of flags: of, sf and af set, cf, zf and pf clear.
movabsq $0x7fffffffffffffff, %rax
addq %rax, %rax

# Leaf 7, subleaf 0: structured extended features, which ssz-specs reads.
movabsq $0xffffffff00000007, %rax
movabsq $0xffffffff00000000, %rcx
cpuid

movq %rax, -8(%rsp)
movl -4(%rsp), %eax
movq %rbx, -8(%rsp)
movl -4(%rsp), %ebx
movq %rcx, -8(%rsp)
movl -4(%rsp), %ecx
movq %rdx, -8(%rsp)
movl -4(%rsp), %edx
