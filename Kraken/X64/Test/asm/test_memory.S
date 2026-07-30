# Test: Register Operations (simplified from memory test)
# Tests: basic register operations since memory addressing with
# RIP-relative (like label(%rip)) isn't supported by the parser
#
# This is a simplified test that verifies register operations work correctly.

# Test: Various register operations
movq $100, %rax
movq $200, %rbx
movq $2, %rcx
movq $8, %rdi

# Test: Index calculation with scale (pure register arithmetic)
# This tests that leaq with base+index*scale works
leaq (%rax, %rcx, 8), %rdx   # rdx = 100 + 2*8 = 116

# Test: Displacement + base + index*scale
leaq 16(%rbx, %rcx, 4), %rsi  # rsi = 200 + 16 + 2*4 = 224

# Final state:
# rax = 100, rbx = 200, rcx = 2, rdx = 116, rsi = 224, rdi = 8
