# Undefined flags: af, sf, zf, pf

# Test: Suffixed mul instruction variants
# Commit: 20d9d63 - Parser fixes for missing instruction variants
# Tests: mulq, mull (suffixed one-operand multiply, which were previously
#        missing from the parser)
#
# `mulq %reg` performs unsigned rdx:rax = rax * reg (64-bit)
# `mull %reg` performs unsigned edx:eax = eax * reg (32-bit)

# ----- Test 1: mulq (64-bit, suffixed) -----
movq $100, %rax
movq $7, %rbx
mulq %rbx                        # rdx:rax = 100 * 7 = 700
# Expected: rax = 700 (0x2BC), rdx = 0

# Save results
movq %rax, %r8                   # r8 = 700
movq %rdx, %r9                   # r9 = 0

# ----- Test 2: mulq with larger values producing high bits -----
movq $0x100000000, %rax          # 2^32
movq $0x100000000, %rcx          # 2^32
mulq %rcx                        # rdx:rax = 2^64
# Expected: rax = 0, rdx = 1

# Save results
movq %rax, %r10                  # r10 = 0
movq %rdx, %r11                  # r11 = 1

# ----- Test 3: mull (32-bit, suffixed) -----
movl $50, %eax
movl $6, %esi
mull %esi                        # edx:eax = 50 * 6 = 300
# Expected: eax = 300 (0x12C), edx = 0

# Save results
movq %rax, %r12                  # r12 = 300
movq %rdx, %r13                  # r13 = 0

# ----- Test 4: Unsuffixed mul still works -----
movq $25, %rax
movq $4, %rdi
mul %rdi                         # rdx:rax = 25 * 4 = 100
# Expected: rax = 100, rdx = 0

# Restore saved values for capture
movq %rax, %r14                  # r14 = 100
movq %rdx, %r15                  # r15 = 0
movq %r8, %rax                   # rax = 700 (test 1 result)
movq %r9, %rbx                   # rbx = 0   (test 1 high)
movq %r10, %rcx                  # rcx = 0   (test 2 low)
movq %r11, %rdx                  # rdx = 1   (test 2 high)
# rsi = clobbered by mull, but we saved to r12
# rdi = 4 (from test 4)

