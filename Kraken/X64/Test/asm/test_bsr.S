# Undefined flags: cf, of, sf, pf, af

# Test bit scan reverse instruction
# Tests: bsrw, bsrl, bsrq on non-zero and zero register and memory operands

# ----- 64-bit bsrq -----
movq $0x0010000000000080, %rax
bsrq %rax, %rbx                  # rbx = 52 (highest set bit)

movq $0x8000000000000000, %rax
bsrq %rax, %rcx                  # rcx = 63

movq $1, %rax
bsrq %rax, %rdx                  # rdx = 0

# ----- 32-bit bsrl (clears upper 32 bits when non-zero) -----
movq $0xFFFFFFFF00000000, %rsi
movl $0x00080400, %eax
bsrl %eax, %esi                  # rsi = 19

# ----- 16-bit bsrw (preserves upper 48 bits) -----
movq $0xAABBCCDDEEFF0000, %rdi
movw $0x0240, %ax
bsrw %ax, %di                    # rdi low 16 = 9

# ----- Zero source leaves destination unmodified (even upper 32 bits on bsrl) and sets ZF=1 -----
movq $0, %rax
movq $0x1122334455667788, %r9
movq $0x99AABBCCDDEEFF11, %r10
movq $0x123456789ABCDEF0, %r11
bsrq %rax, %r9                   # r9 unmodified, ZF = 1
bsrl %eax, %r10d                 # r10 unmodified (including upper 32 bits), ZF = 1
bsrw %ax, %r11w                  # r11 unmodified, ZF = 1

# ----- Memory operand -----
movq $0x0000001000000000, %rax
pushq %rax
bsrq (%rsp), %r8                 # r8 = 36, ZF = 0
popq %rax
