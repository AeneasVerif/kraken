# Undefined flags: af

# Test: Logical Operations
# Tests: xorq, andq, orq
#
# Expected results:
#   rax: 0xFF00 XOR 0x0F0F = 0xF00F
#   rbx: 0xFF00 AND 0x0F0F = 0x0F00
#   rcx: 0xFF00 OR 0x0F0F = 0xFF0F
#   rdx: XOR with self = 0

# Test xorq
movq $0xFF00, %rax
xorq $0x0F0F, %rax      # rax = 0xF00F

# Test andq
movq $0xFF00, %rbx
andq $0x0F0F, %rbx      # rbx = 0x0F00

# Test orq
movq $0xFF00, %rcx
orq $0x0F0F, %rcx       # rcx = 0xFF0F

# Test xorq for zeroing (common idiom)
movq $12345, %rdx
xorq %rdx, %rdx         # rdx = 0, ZF = 1
