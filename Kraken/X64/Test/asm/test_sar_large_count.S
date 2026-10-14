# Undefined flags: af, of

# Test 8-bit and 16-bit SAR with shift counts >= operand width (8, >8, 16, >16, 31)
# using both immediate and %cl counts on negative and non-negative inputs.
# Accumulate each resulting CF into %r12 via rclq $1, %r12.

# ----- 8-bit SAR with immediate counts (8, 9, 31) -----
# Negative inputs (MSB = 1 -> result = 0xff, CF = 1)
movb $0x80, %al
sarb $8, %al
rclq $1, %r12

movb $0x80, %bl
sarb $9, %bl
rclq $1, %r12

movb $0x80, %dl
sarb $31, %dl
rclq $1, %r12

# Non-negative inputs (MSB = 0 -> result = 0x00, CF = 0)
movb $0x7f, %sil
sarb $8, %sil
rclq $1, %r12

movb $0x7f, %dil
sarb $9, %dil
rclq $1, %r12

movb $0x7f, %r8b
sarb $31, %r8b
rclq $1, %r12

# ----- 8-bit SAR with %cl counts (8, 13, 31) -----
# Negative inputs (MSB = 1 -> result = 0xff, CF = 1)
movb $8, %cl
movb $0x80, %al
sarb %cl, %al
rclq $1, %r12

movb $13, %cl
movb $0x80, %bl
sarb %cl, %bl
rclq $1, %r12

movb $31, %cl
movb $0x80, %dl
sarb %cl, %dl
rclq $1, %r12

# Non-negative inputs (MSB = 0 -> result = 0x00, CF = 0)
movb $8, %cl
movb $0x7f, %sil
sarb %cl, %sil
rclq $1, %r12

movb $13, %cl
movb $0x7f, %dil
sarb %cl, %dil
rclq $1, %r12

movb $31, %cl
movb $0x7f, %r8b
sarb %cl, %r8b
rclq $1, %r12

# ----- 16-bit SAR with immediate counts (16, 17, 31) -----
# Negative inputs (MSB = 1 -> result = 0xffff, CF = 1)
movw $0x8000, %ax
sarw $16, %ax
rclq $1, %r12

movw $0x8000, %bx
sarw $17, %bx
rclq $1, %r12

movw $0x8000, %dx
sarw $31, %dx
rclq $1, %r12

# Non-negative inputs (MSB = 0 -> result = 0x0000, CF = 0)
movw $0x7fff, %si
sarw $16, %si
rclq $1, %r12

movw $0x7fff, %di
sarw $17, %di
rclq $1, %r12

movw $0x7fff, %r8w
sarw $31, %r8w
rclq $1, %r12

# ----- 16-bit SAR with %cl counts (16, 23, 31) -----
# Negative inputs (MSB = 1 -> result = 0xffff, CF = 1)
movb $16, %cl
movw $0x8000, %r9w
sarw %cl, %r9w
rclq $1, %r12

movb $23, %cl
movw $0x8000, %r10w
sarw %cl, %r10w
rclq $1, %r12

movb $31, %cl
movw $0x8000, %r11w
sarw %cl, %r11w
rclq $1, %r12

# Non-negative inputs (MSB = 0 -> result = 0x0000, CF = 0)
movb $16, %cl
movw $0x7fff, %r13w
sarw %cl, %r13w
rclq $1, %r12

movb $23, %cl
movw $0x7fff, %r14w
sarw %cl, %r14w
rclq $1, %r12

movb $31, %cl
movw $0x7fff, %r15w
sarw %cl, %r15w
rclq $1, %r12

# Leave final flags from a large-count SAR live (non-negative -> CF = 0, SF = 0, ZF = 1, PF = 1)
movw $0x7fff, %ax
sarw $16, %ax
