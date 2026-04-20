# Test conditional instructions
# Tests: setc, setnc, test
#
# Note: Avoiding cmov and push/pop which may need more parser support

# ----- TEST instruction -----
movq $0xFF, %rax
testq %rax, %rax                 # Sets ZF=0 (non-zero)
# ZF should be 0

# ----- SETC / SETNC (set byte on carry) -----
# First, create carry condition
movq $0xFFFFFFFFFFFFFFFF, %rbx
addq $1, %rbx                    # Overflow sets CF
setc %cl                         # cl = 1 (CF was set)
# Expected: rcx = 1

xorq %rdx, %rdx
addq $1, %rdx                    # No overflow
setc %dl                         # dl = 0 (CF not set)
# Expected: rdx = 0

movq $0, %rsi
setnc %sil                       # sil = 1 (CF not set after last addq)
# Expected: rsi = 1

# Initialize remaining registers
movq $300, %r9
movq $400, %r10
movq $500, %r11
movq $600, %r12
movq $700, %r13
movq $800, %r14
movq $42, %r15
