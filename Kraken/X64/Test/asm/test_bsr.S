# Undefined flags: cf, of, sf, pf, af

# Test bit scan reverse instruction
# Tests: bsrw, bsrl, bsrq on non-zero register and memory operands

# ----- 64-bit bsrq -----
movq $0x0010000000000080, %rax
bsrq %rax, %rbx                  # rbx = 52 (highest set bit)

movq $0x8000000000000000, %rax
bsrq %rax, %rcx                  # rcx = 63

movq $1, %rax
bsrq %rax, %rdx                  # rdx = 0

# ----- 32-bit bsrl (clears upper 32 bits) -----
movq $0xFFFFFFFF00000000, %rsi
movl $0x00080400, %eax
bsrl %eax, %esi                  # rsi = 19

# ----- 16-bit bsrw (preserves upper 48 bits) -----
movq $0xAABBCCDDEEFF0000, %rdi
movw $0x0240, %ax
bsrw %ax, %di                    # rdi low 16 = 9

# ----- Memory operand -----
movq $0x0000001000000000, %rax
pushq %rax
bsrq (%rsp), %r8                 # r8 = 36, ZF = 0
popq %rax
