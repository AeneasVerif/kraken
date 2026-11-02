# Test 8-bit and 16-bit operations
# Tests: setc, setnc, cmpb, movw, 8-bit register reads via setc/setnc
#
# Per Intel SDM:
# - setc/setnc write a byte (0 or 1) to 8-bit register
# - 16-bit writes (movw) preserve upper 48 bits

# ----- 16-bit register writes preserve upper bits (movw) -----
movq $0xFFFFFFFFFFFF0000, %rax
movw $0x1234, %ax
# Expected: rax = 0xFFFFFFFFFFFF1234 (upper bits preserved)

# ----- setc: set byte based on carry flag -----
# First clear rbx completely
xorq %rbx, %rbx
# Create carry by overflow
movq $0xFFFFFFFFFFFFFFFF, %rcx
addq $1, %rcx                    # Sets CF=1
setc %bl                         # bl = 1
# Expected: rbx = 1

# ----- setnc: set byte based on NOT carry flag -----
xorq %rdx, %rdx                  # Clear rdx
xorq %rsi, %rsi
addq $1, %rsi                    # No carry (0+1=1), CF=0
setnc %dl                        # dl = 1 (CF=0)
# Expected: rdx = 1

# ----- cmpb: 8-bit compare -----
# Use setc to load 8-bit values first
movq $100, %rdi
movq $100, %r8
cmpb %r8b, %dil                  # Compare low bytes: 100 - 100 = 0, ZF=1
# ZF should be set
