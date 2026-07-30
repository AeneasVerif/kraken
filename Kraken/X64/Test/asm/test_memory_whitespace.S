# Test: Memory operand parsing with whitespace between displacement and parenthesis
# Tests: This specifically tests the bug where `0 (%rdi)` (space before paren) failed to parse
#
# The GNU assembler accepts whitespace between displacement and parenthesis, e.g.:
#   leaq 0 (%rdi), %rax
#   leaq 16 (%rbx, %rcx, 4), %rsi
#
# This test ensures Kraken's parser also accepts this syntax.
# Uses only register operations (no RIP-relative memory) for parser compatibility.

# Setup base values
movq $100, %rdi
movq $200, %rbx
movq $2, %rcx

# Test 1: leaq with space between displacement and paren
leaq 0 (%rdi), %rax          # Space between 0 and ( -> rax = 100

# Test 2: leaq with larger displacement and space
leaq 8 (%rdi), %r8           # Space between 8 and ( -> r8 = 108

# Test 3: leaq with displacement + base + index*scale, with spacing
leaq 16 (%rbx, %rcx, 4), %rsi # Space between 16 and ( -> rsi = 200 + 16 + 2*4 = 224

# Test 4: Zero displacement with index and scale, with spacing
leaq 0 (%rdi, %rcx, 8), %rdx  # Space between 0 and ( -> rdx = 100 + 2*8 = 116

# Final expected state:
# rax = 100 (from leaq 0 (%rdi), %rax)
# rbx = 200
# rcx = 2
# rdx = 116 (from leaq 0 (%rdi, %rcx, 8), %rdx)
# rsi = 224 (from leaq 16 (%rbx, %rcx, 4), %rsi)
# rdi = 100
# r8 = 108 (from leaq 8 (%rdi), %r8)

