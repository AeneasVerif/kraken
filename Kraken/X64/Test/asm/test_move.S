# Test: Move and LEA Operations
# Tests: movq, leaq (without 32-bit operations that need edx)
#
# Avoids: movl (32-bit ops), large immediates out of Int64 range
#
# Expected results:
#   rax: 42
#   rbx: leaq 8(%rax, %rcx, 4) = 42 + 10*4 + 8 = 90
#   rcx: 10
#   rdx: 999
#   rsi: 142

# Test movq (64-bit immediate)
movq $42, %rax          # rax = 42

# Test movq (register to register)
movq $10, %rcx          # rcx = 10

# Test leaq (address calculation without memory access)
leaq 8(%rax, %rcx, 4), %rbx  # rbx = 42 + 10*4 + 8 = 90

# Test movq with another immediate
movq $999, %rdx         # rdx = 999

# Test leaq with just displacement
leaq 100(%rax), %rsi    # rsi = 42 + 100 = 142

