# Undefined flags: of, sf, pf, af

# Test trailing and leading zero count instructions (BMI1 / ABM)
# Tests: tzcntw, tzcntl, tzcntq, lzcntw, lzcntl, lzcntq

# ----- 64-bit tzcntq / lzcntq (register) -----
movq $0x0010000000000080, %rax
tzcntq %rax, %rbx                # rbx = 7
lzcntq %rax, %rcx                # rcx = 11

# ----- 64-bit zero input (returns 64) -----
xorq %rax, %rax
tzcntq %rax, %rdx                # rdx = 64
lzcntq %rax, %rsi                # rsi = 64

# ----- 32-bit tzcntl / lzcntl (zero-extends upper 32 bits) -----
movq $0xFFFFFFFF00000000, %rdi
movq $0xFFFFFFFF00000000, %r8
movl $0x00800400, %eax
tzcntl %eax, %edi                # rdi = 10
lzcntl %eax, %r8d                # r8  = 8

# ----- 16-bit tzcntw / lzcntw (preserves upper 48 bits) -----
movq $0x1122334455660000, %r9
movq $0x1122334455660000, %r10
movw $0x0240, %ax
tzcntw %ax, %r9w                 # r9w = 6
lzcntw %ax, %r10w                # r10w = 6

# ----- Memory operand tests & final flag check (ZF=1, CF=0 when LSB=1) -----
movq $0x0000800000000001, %rax
pushq %rax
lzcntq (%rsp), %r11              # r11 = 16
tzcntq (%rsp), %r12              # r12 = 0, CF = 0, ZF = 1
popq %rax
