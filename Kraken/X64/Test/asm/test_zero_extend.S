# Test zero-extension move instructions
# Tests: movzbl, movzwl, movzbq with register sources
#
# Note: movz* require register sources in AT&T syntax, not immediates

# ----- movzbl with register source -----
# Load a value into al, then zero-extend to 32/64-bit
movq $0x00000000000000AB, %rax   # al = 0xAB
movq $0xFFFFFFFFFFFFFFFF, %rbx   # Fill rbx with 1s
movzbl %al, %ebx                 # ebx = 0x000000AB, clears upper 32 bits
# Expected: rbx = 0x00000000000000AB

# ----- movzwl with register source -----
movq $0x000000000000CDEF, %rcx   # cx = 0xCDEF
movq $0xFFFFFFFFFFFFFFFF, %rdx
movzwl %cx, %edx                 # edx = 0x0000CDEF, clears upper 32 bits
# Expected: rdx = 0x000000000000CDEF

# ----- movzbq with register source -----
movq $0x00000000000000FF, %rsi   # sil = 0xFF
movq $0xFFFFFFFFFFFFFFFF, %rdi
movzbq %sil, %rdi                # rdi = 0x00000000000000FF
# Expected: rdi = 0x00000000000000FF

# ----- Test that zero-extend properly clears high bits -----
movq $0xFFFFFFFFFFFF0042, %r8    # r8b = 0x42
movq $0xDEADBEEFDEADBEEF, %r9
movzbl %r8b, %r9d                # r9 = 0x0000000000000042
# Expected: r9 = 0x42

