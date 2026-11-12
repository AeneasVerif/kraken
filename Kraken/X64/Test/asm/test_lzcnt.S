# Undefined flags: of, sf, pf, af

# Test leading zero count instruction (ABM / LZCNT)
# Tests: lzcntw, lzcntl, lzcntq

# ----- 64-bit lzcntq (register) -----
movq $0x0010000000000080, %rax
lzcntq %rax, %rcx                # rcx = 11

# ----- 64-bit zero input (returns 64, sets CF=1, ZF=0) -----
movq $0, %rax
lzcntq %rax, %rsi                # rsi = 64

# ----- 32-bit lzcntl (zero-extends upper 32 bits) -----
movq $0xFFFFFFFF00000000, %r8
movl $0x00800400, %eax
lzcntl %eax, %r8d                # r8 = 8

# ----- 16-bit lzcntw (preserves upper 48 bits) -----
movq $0x1122334455660000, %r10
movw $0x0240, %ax
lzcntw %ax, %r10w                # r10w = 6

# ----- Memory operand & final flag check (ZF=1, CF=0 when MSB=1) -----
movq $0x8000000000000001, %rax
pushq %rax
lzcntq (%rsp), %r11              # r11 = 0, CF = 0, ZF = 1
popq %rax
