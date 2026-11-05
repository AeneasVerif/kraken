# Test population count instruction
# Tests: popcntw, popcntl, popcntq (all flags defined: CF=OF=SF=AF=PF=0, ZF=(src==0))

# ----- 64-bit popcntq -----
movq $0x5555555555555555, %rax
popcntq %rax, %rbx               # rbx = 32, ZF = 0

movq $0xFFFFFFFFFFFFFFFF, %rax
popcntq %rax, %rcx               # rcx = 64, ZF = 0

# ----- 32-bit popcntl (clears upper 32 bits) -----
movq $0xFFFFFFFF00000000, %rdx
movl $0x0F0F0F0F, %eax
popcntl %eax, %edx               # rdx = 16, ZF = 0

# ----- 16-bit popcntw (preserves upper 48 bits) -----
movq $0x123456789ABC0000, %rsi
movw $0xF0F0, %ax
popcntw %ax, %si                 # rsi low 16 = 8, ZF = 0

# ----- Memory operand & zero input (sets ZF=1, clears CF/OF/SF/AF/PF) -----
movq $0x0101010101010101, %rax
pushq %rax
popcntq (%rsp), %rdi             # rdi = 8
movq $0, (%rsp)
popcntq (%rsp), %r8              # r8 = 0, ZF = 1
popq %rax
