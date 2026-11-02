# Test byte swap instructions
# Tests: bswapq (64-bit), bswapl (32-bit)
#
# Expected final values:
#   rax: 0x0807060504030201 (bswap of 0x0102030405060708)
#   rbx: 0xBEBAFECAEFBEADDE (bswap of 0xDEADBEEFCAFEBABE)
#   rcx: 0x00000000EFBEADDE (bswapl of 0xDEADBEEF)

# ----- 64-bit byte swap -----
movq $0x0102030405060708, %rax
bswapq %rax
# Expected: rax = 0x0807060504030201

# Another 64-bit test
movq $0xDEADBEEFCAFEBABE, %rbx
bswapq %rbx
# Expected: rbx = 0xBEBAFECAEFBEADDE

# ----- 32-bit byte swap -----
movl $0xDEADBEEF, %ecx
bswapl %ecx
# Expected: ecx = 0xEFBEADDE (upper 32 bits cleared)

# Test that 32-bit bswap properly zero-extends
movq $0xFFFFFFFF00000000, %rdx
movl $0x01020304, %edx           # Clears upper 32 bits
bswapl %edx
# Expected: rdx = 0x0000000004030201

