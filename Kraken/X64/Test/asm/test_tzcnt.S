# Undefined flags: of, sf, pf, af

# Test trailing zero count instruction (BMI1)
# Tests: tzcntw, tzcntl, tzcntq

# ----- 64-bit tzcntq (register) -----
movq $0x0010000000000080, %rax
tzcntq %rax, %rbx                # rbx = 7

# ----- 64-bit zero input (returns 64, sets CF=1, ZF=0) -----
movq $0, %rax
tzcntq %rax, %rdx                # rdx = 64

# ----- 32-bit tzcntl (zero-extends upper 32 bits) -----
movq $0xFFFFFFFF00000000, %rdi
movl $0x00800400, %eax
tzcntl %eax, %edi                # rdi = 10

# ----- 16-bit tzcntw (preserves upper 48 bits) -----
movq $0x1122334455660000, %r9
movw $0x0240, %ax
tzcntw %ax, %r9w                 # r9w = 6

# ----- Memory operand & final flag check (ZF=1, CF=0 when LSB=1) -----
movq $0x0000800000000001, %rax
pushq %rax
tzcntq (%rsp), %r12              # r12 = 0, CF = 0, ZF = 1
popq %rax
