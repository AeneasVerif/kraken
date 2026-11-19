# Test BMI2 flagless shifts and rotate: shlx, shrx, sarx, and rorx (32/64-bit, reg & mem)

# Accumulator r12 holds a rolling hash of results; r13..r15 track observed flags.
xorl %r12d, %r12d
xorl %r13d, %r13d
xorl %r14d, %r14d
xorl %r15d, %r15d

# Stack memory sources
movabsq $0x8000000000000005, %rax
movq %rax, -8(%rsp)
movl $0x80000003, -16(%rsp)
movl $0x7fffffff, -24(%rsp)
movabsq $0x0123456789abcdef, %rax
movq %rax, -32(%rsp)

# ----- 64-bit shlx / shrx / sarx across counts 0, 1, 31, 32, 63, 64, 0xff -----
movabsq $0x8000000000000005, %rsi

movq $0, %rcx
shlxq %rcx, %rsi, %rdx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $1, %rcx
shlxq %rcx, -8(%rsp), %rdx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $31, %rcx
shlxq %rcx, %rsi, %rdx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $32, %rcx
shrxq %rcx, %rsi, %rdx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $63, %rcx
shrxq %rcx, -8(%rsp), %rdx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $64, %rcx
shrxq %rcx, %rsi, %rdx          # count 64 masks to 0
imulq $131, %r12, %r12
addq %rdx, %r12

movq $0xff, %rcx
shrxq %rcx, %rsi, %rdx          # count 0xff masks to 63
imulq $131, %r12, %r12
addq %rdx, %r12

# sarx 64-bit: negative and positive sign extension
movq $1, %rcx
sarxq %rcx, %rsi, %rdx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $32, %rcx
sarxq %rcx, -8(%rsp), %rdx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $63, %rcx
sarxq %rcx, %rsi, %rdx          # all ones
imulq $131, %r12, %r12
addq %rdx, %r12

movq $64, %rcx
sarxq %rcx, %rsi, %rdx          # count 64 masks to 0
imulq $131, %r12, %r12
addq %rdx, %r12

movabsq $0x7fffffffffffffff, %rdi
movq $0xff, %rcx
sarxq %rcx, %rdi, %rdx          # positive -> 0
imulq $131, %r12, %r12
addq %rdx, %r12

# ----- 32-bit shlx / shrx / sarx (count masked mod 32, upper 32 bits zero-extended) -----
movl $0x80000003, %esi

movq $-1, %rdx
movl $0, %ecx
shlxl %ecx, %esi, %edx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $-1, %rdx
movl $31, %ecx
shlxl %ecx, -16(%rsp), %edx
imulq $131, %r12, %r12
addq %rdx, %r12

movq $-1, %rdx
movl $32, %ecx
shrxl %ecx, %esi, %edx          # count 32 masks to 0
imulq $131, %r12, %r12
addq %rdx, %r12

movq $-1, %rdx
movl $0xff, %ecx
shrxl %ecx, -16(%rsp), %edx     # count 0xff masks to 31
imulq $131, %r12, %r12
addq %rdx, %r12

movq $-1, %rdx
movl $1, %ecx
sarxl %ecx, -16(%rsp), %edx     # negative -> 0x00000000c0000001 (upper 32 zeroed)
imulq $131, %r12, %r12
addq %rdx, %r12

movq $-1, %rdx
movl $63, %ecx
sarxl %ecx, %esi, %edx          # count 63 masks to 31 -> 0x00000000ffffffff
imulq $131, %r12, %r12
addq %rdx, %r12

movq $-1, %rdx
movl $64, %ecx
sarxl %ecx, -24(%rsp), %edx     # count 64 masks to 0
imulq $131, %r12, %r12
addq %rdx, %r12

# ----- rorx 64-bit and 32-bit (reg & mem, counts 0, 1, 31, 32, 63, 64, 0xff) -----
movabsq $0x0123456789abcdef, %rsi

rorxq $0, %rsi, %r8
imulq $131, %r12, %r12
addq %r8, %r12

rorxq $1, -32(%rsp), %r8
imulq $131, %r12, %r12
addq %r8, %r12

rorxq $31, %rsi, %r8
imulq $131, %r12, %r12
addq %r8, %r12

rorxq $32, -32(%rsp), %r8
imulq $131, %r12, %r12
addq %r8, %r12

rorxq $63, %rsi, %r8
imulq $131, %r12, %r12
addq %r8, %r12

rorxq $64, %rsi, %r8
imulq $131, %r12, %r12
addq %r8, %r12

rorxq $0xff, -32(%rsp), %r8
imulq $131, %r12, %r12
addq %r8, %r12

movq $-1, %r9
rorxl $0, %esi, %r9d
imulq $131, %r12, %r12
addq %r9, %r12

movq $-1, %r9
rorxl $1, -16(%rsp), %r9d
imulq $131, %r12, %r12
addq %r9, %r12

movq $-1, %r9
rorxl $31, %esi, %r9d
imulq $131, %r12, %r12
addq %r9, %r12

movq $-1, %r9
rorxl $32, -16(%rsp), %r9d       # masks to 0
imulq $131, %r12, %r12
addq %r9, %r12

movq $-1, %r9
rorxl $63, %esi, %r9d           # masks to 31
imulq $131, %r12, %r12
addq %r9, %r12

movq $-1, %r9
rorxl $64, %esi, %r9d           # masks to 0
imulq $131, %r12, %r12
addq %r9, %r12

movq $-1, %r9
rorxl $0xff, -16(%rsp), %r9d    # masks to 31
imulq $131, %r12, %r12
addq %r9, %r12

# ----- Explicit RFLAGS preservation -----
# Set CF=1, OF=1, ZF=1, PF=1 and verify BMI2 shifts/rotate leave them intact.
movb $0x80, %al
addb $0x80, %al
movl $5, %ecx
shlxl %ecx, %esi, %r10d
shrxl %ecx, -16(%rsp), %r10d
sarxl %ecx, %esi, %r10d
rorxl $5, -16(%rsp), %r10d
setc %r13b
seto %r14b
setz %r15b
setp %r11b
leaq (%r13, %r14, 2), %r13
leaq (%r13, %r15, 4), %r13
leaq (%r13, %r11, 8), %r13

# Finally set CF=1, AF=1, SF=1, PF=1 via cmpb and verify all 6 flags survive at exit.
movb $0x80, %al
movl $7, %ecx
cmpb $0x81, %al
shlxq %rcx, %rsi, %r8
shrxq %rcx, -8(%rsp), %r9
sarxq %rcx, %rsi, %r10
rorxq $7, -32(%rsp), %r11
