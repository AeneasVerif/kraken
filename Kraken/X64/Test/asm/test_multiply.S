# Undefined flags: af, sf, zf, pf

# Test: Multiplication Operations
# Tests: mulq, imulq
#
# Expected results:
#   rdx:rax = 10 * 20 = 200 (mulq puts result in rdx:rax)
#   r8 = 5 * 7 = 35 (imulq two-operand form)

# Test mulq (unsigned multiply, result in rdx:rax)
movq $10, %rax
movq $20, %rbx
mulq %rbx               # rdx:rax = 10 * 20 = 200
# rax = 200, rdx = 0 (no overflow for small numbers)

# Save mulq result
movq %rax, %rcx         # rcx = 200 (low part)
movq %rdx, %rsi         # rsi = 0 (high part)

# Test imulq (signed multiply, two-operand form)
movq $5, %r8
movq $7, %r9
imulq %r9, %r8          # r8 = 5 * 7 = 35

# Restore rax for output
movq %rcx, %rax
