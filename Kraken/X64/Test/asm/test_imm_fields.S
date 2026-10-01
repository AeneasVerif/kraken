# Immediate fields: as truncates immediates that overflow a field as wide as
# the operand (with a "shortened" warning), so the model must use the same
# encoded value; 64-bit operations sign-extend an imm32, except movabs.

movq $0x1111111111111111, %rax
addw $0x123456789, %ax           # encoded as $0x6789
movq $0x2222222222222222, %rbx
addl $0x100000005, %ebx          # encoded as $0x5
movq $0x3333333333333333, %rcx
addb $0x1ff, %cl                 # encoded as $0xff
movq $1, %rdx
shlb $258, %dl                   # count encoded as $0x2
movq $0x8000000000000001, %rsi
rorq $-1, %rsi                   # count encoded as $0xff, masked to 63
movabsq $0x123456789, %rdi
movq $0x7fffffff00000000, %r8
addq $0xffffffff80000000, %r8    # sign-extended imm32
