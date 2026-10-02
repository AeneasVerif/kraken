# Test newly added x86 condition codes: o, no, s, ns, p, np, ge, g
# Tests both true and false outcomes using setcc and cmovcc into distinct registers.

# Initialize registers with baseline values so cmov false leaves them untouched
movq $0x100, %rax
movq $0x200, %rbx
movq $0x300, %rcx
movq $0x400, %rdx
movq $0x500, %rsi
movq $0x600, %rdi
movq $0x700, %r8
movq $0x800, %r9
movq $0x900, %r10
movq $0xa00, %r11
movq $0xb00, %r12
movq $0xc00, %r13
movq $0xd00, %r14
movq $0xe00, %r15

# Source value for cmovcc operations
movq $0x42, %r15

# 1. Overflow Flag (OF): o, no
# Cause signed overflow: 0x7FFFFFFFFFFFFFFF + 1 -> OF=1, SF=1
movq $0x7FFFFFFFFFFFFFFF, %rax
addq $1, %rax
seto %al              # OF is 1 -> al = 1
setno %bl             # OF is 1 -> bl = 0
cmovo %r15, %rcx      # OF is 1 -> rcx becomes 0x42
cmovno %r15, %rdx     # OF is 1 -> rdx remains 0x400

# Clear overflow: 10 + 20 -> OF=0, SF=0
movq $10, %rax
addq $20, %rax
seto %sil             # OF is 0 -> sil = 0
setno %dil            # OF is 0 -> dil = 1
cmovo %r15, %r8       # OF is 0 -> r8 remains 0x700
cmovno %r15, %r9      # OF is 0 -> r9 becomes 0x42

# 2. Sign Flag (SF): s, ns
# Negative result: 0 - 5 -> SF=1, OF=0, ZF=0
movq $0, %rax
subq $5, %rax
sets %r10b            # SF is 1 -> r10b = 1
setns %r11b           # SF is 1 -> r11b = 0
cmovs %r15, %r12      # SF is 1 -> r12 becomes 0x42
cmovns %r15, %r13     # SF is 1 -> r13 remains 0xd00

# Positive result: 10 - 5 -> SF=0, OF=0, ZF=0
movq $10, %rax
subq $5, %rax
sets %r14b            # SF is 0 -> r14b = 0
cmovs %r15, %rax      # SF is 0 -> rax remains 5
cmovns %r15, %rbx     # SF is 0 -> rbx (was 0x200 with low byte 0) becomes 0x42

# 3. Parity Flag (PF): p, np
# PF is computed from the low 8 bits of the result.
# 3 has two 1-bits (parity even) -> PF=1
movq $0, %rax
addq $3, %rax         # low 8 bits: 3 (0b00000011, two 1-bits) -> PF=1
setp %cl              # PF is 1 -> cl = 1
setnp %dl             # PF is 1 -> dl = 0

# 1 has one 1-bit (parity odd) -> PF=0
movq $0, %rax
addq $1, %rax         # low 8 bits: 1 (0b00000001, one 1-bit) -> PF=0
setp %sil             # PF is 0 -> sil = 0
setnp %dil            # PF is 0 -> dil = 1

# 4. Greater/Equal (GE: SF == OF) and Greater (G: ~ZF & SF == OF)
# Test cmp 10, 20 (i.e. 20 - 10 = 10): > 0, so SF=0, OF=0, ZF=0 -> GE=1, G=1
movq $10, %rax
cmpq %rax, %r15       # 0x42 - 10 = positive, no overflow: SF=0, OF=0, ZF=0
setge %r10b           # SF == OF -> r10b = 1
setg %r11b            # !ZF && SF == OF -> r11b = 1
cmovge %r15, %r13     # SF == OF -> r13 becomes 0x42
cmovg %r15, %r14      # !ZF && SF == OF -> r14 becomes 0x42

# Test cmp equal: 10 vs 10 (10 - 10 = 0): SF=0, OF=0, ZF=1 -> GE=1, G=0
movq $10, %rax
cmpq $10, %rax        # ZF=1, SF=0, OF=0
setge %r8b            # SF == OF -> r8b = 1
setg %r9b             # !ZF is false -> r9b = 0

# Test cmp less: 5 vs 10 (5 - 10 = -5): SF=1, OF=0, ZF=0 -> GE=0, G=0
movq $5, %rax
cmpq $10, %rax        # 5 - 10: SF=1, OF=0, ZF=0
setge %al             # SF != OF -> al = 0
setg %bl              # G is false -> bl = 0
cmovge %r15, %rdx     # GE is false -> rdx remains untouched
cmovg %r15, %rdx      # G is false -> rdx remains untouched
