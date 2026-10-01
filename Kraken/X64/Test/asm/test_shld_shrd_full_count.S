# Undefined flags: of, af

# Test 16-bit shldw and shrdw when the masked shift count equals the operand width (16).
# Per Intel SDM and AMD APM, DEST and flags are undefined only when COUNT > SIZE.
# At COUNT == 16 on 16-bit operands:
# - DEST receives SRC
# - CF receives the last bit shifted out of original DEST (bit 0 for SHLD, bit 15 for SHRD)
# - SF, ZF, PF are set from the result

# 1. shldw $16: bit 0 of dst (0x1235) is 1 -> CF=1; src is 0x0000 -> dst=0, ZF=1
movw $0x1235, %ax
movw $0x0000, %bx
shldw $16, %bx, %ax
setc %r8b
setz %r9b

# 2. shldw %cl (count = 16): bit 0 of dst (0xfffe) is 0 -> CF=0; src is 0x8003 -> dst=0x8003, ZF=0
movb $16, %cl
movw $0xfffe, %ax
movw $0x8003, %dx
shldw %cl, %dx, %ax
setc %r10b
setz %r11b

# 3. shrdw $16: bit 15 of dst (0x8000) is 1 -> CF=1; src is 0x0000 -> dst=0, ZF=1
movw $0x8000, %si
movw $0x0000, %bx
shrdw $16, %bx, %si
setc %r12b
setz %r13b

# 4. shrdw %cl (count = 48, masked to 16): bit 15 of dst (0x7fff) is 0 -> CF=0;
#    src is 0x8001 -> dst=0x8001, SF=1, ZF=0, PF=0 (low byte 0x01 has odd parity)
movb $48, %cl
movw $0x7fff, %di
movw $0x8001, %dx
shrdw %cl, %dx, %di
setc %r14b
setz %r15b
