# Test bit-counting instructions: lzcnt, tzcnt, and popcnt (16/32/64-bit, reg & mem)

# Initialize accumulators:
#   r12 = rolling hash of instruction results (r12 * 131 + result)
#   r13, r14 = scratch bytes for CF/ZF/OF/SF/PF capture
#   r15 = bitstream of observed (cf, zf) pairs across lzcnt/tzcnt/popcnt cases
xorl %r12d, %r12d
xorl %r13d, %r13d
xorl %r14d, %r14d
xorl %r15d, %r15d

# Memory test inputs on the stack
movq $0, -8(%rsp)
movq $1, -16(%rsp)
movabsq $0x8000000000000000, %rax
movq %rax, -24(%rsp)
movq $-1, -32(%rsp)
movw $0x8000, -40(%rsp)
movl $0x80000000, -48(%rsp)
movw $0x0010, -56(%rsp)

# ----- lzcnt: 64-bit -----
xorl %eax, %eax
lzcntq %rax, %rcx               # 0 -> 64, cf=1, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

movq $1, %rax
lzcntq %rax, %rcx               # 1 -> 63, cf=0, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

lzcntq -24(%rsp), %rcx          # MSB (mem) -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

movq $-1, %rax
lzcntq %rax, %rcx               # all ones -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

# ----- lzcnt: 32-bit (zero-extends to 64 bits) -----
movq $-1, %rcx
lzcntl -8(%rsp), %ecx           # 0 (mem) -> 32, upper 32 cleared, cf=1, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

movl $1, %eax
lzcntl %eax, %ecx               # 1 -> 31, cf=0, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

movq $-1, %rcx
lzcntl -48(%rsp), %ecx          # MSB (mem) -> 0, upper 32 cleared, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

movl $-1, %eax
lzcntl %eax, %ecx               # all ones -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

# ----- lzcnt: 16-bit (preserves upper 48 bits) -----
movabsq $0x123456789abcdef0, %rcx
xorl %eax, %eax
lzcntw %ax, %cx                 # 0 -> 16, upper 48 preserved, cf=1, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

movw $1, %ax
lzcntw %ax, %cx                 # 1 -> 15, cf=0, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

lzcntw -40(%rsp), %cx           # MSB (mem) -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

movw $-1, %ax
lzcntw %ax, %cx                 # all ones -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rcx, %r12

# ----- tzcnt: 64-bit -----
tzcntq -8(%rsp), %rdx           # 0 (mem) -> 64, cf=1, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

movq $1, %rax
tzcntq %rax, %rdx               # 1 -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

movabsq $0x8000000000000000, %rax
tzcntq %rax, %rdx               # MSB -> 63, cf=0, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

tzcntq -32(%rsp), %rdx          # all ones (mem) -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

# ----- tzcnt: 32-bit (zero-extends to 64 bits) -----
movq $-1, %rdx
xorl %eax, %eax
tzcntl %eax, %edx               # 0 -> 32, upper 32 cleared, cf=1, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

tzcntl -16(%rsp), %edx          # 1 (mem) -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

movl $0x80000000, %eax
tzcntl %eax, %edx               # MSB -> 31, cf=0, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

movl $-1, %eax
tzcntl %eax, %edx               # all ones -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

# ----- tzcnt: 16-bit (preserves upper 48 bits) -----
movabsq $0xfedcba9876543210, %rdx
xorl %eax, %eax
tzcntw %ax, %dx                 # 0 -> 16, upper 48 preserved, cf=1, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

movw $1, %ax
tzcntw %ax, %dx                 # 1 -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

tzcntw -40(%rsp), %dx           # MSB (mem) -> 15, cf=0, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

tzcntw -56(%rsp), %dx           # 0x0010 (mem) -> 4, cf=0, zf=0
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

movw $-1, %ax
tzcntw %ax, %dx                 # all ones -> 0, cf=0, zf=1
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15
imulq $131, %r12, %r12
addq %rdx, %r12

# ----- popcnt: 16/32/64-bit, reg & mem, and full RFLAGS clearing -----
# First clear undefined flags left by lzcnt/tzcnt and check popcnt clearing OF/AF and setting ZF=1.
movb $0x80, %al
subb $1, %al                    # 0x80 - 1 = 0x7f -> OF=1, AF=1, CF=0, PF=0, ZF=0, SF=0
popcntq -8(%rsp), %rsi          # 0 (mem) -> 0, ZF=1, all other flags cleared
seto %r13b                      # should be 0
setz %r14b                      # should be 1
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15

# 32-bit zero-extension and clearing CF/AF/SF/PF on nonzero input
movq $-1, %r8
movl $0x80000001, %edi
movb $0x80, %al
subb $0x81, %al                 # 0x80 - 0x81 = 0xff -> CF=1, AF=1, SF=1, PF=1, ZF=0, OF=0
popcntl %edi, %r8d              # r8 = 2 (upper 32 cleared), ZF=0, all other flags cleared
setc %r13b
setz %r14b
leaq (%r15, %r15, 1), %r15
addq %r13, %r15
leaq (%r15, %r15, 1), %r15
addq %r14, %r15

# 16-bit upper-48 preservation and memory source
movabsq $0xdeadbeefcafebabe, %r9
movw $-1, %ax
popcntw %ax, %r9w               # r9 = 0xdeadbeefcafe0010
popcntw -56(%rsp), %r10w        # 0x0010 (mem) -> 1 (folded below)
movzwq %r10w, %rax
imulq $131, %r12, %r12
addq %rax, %r12

# 32-bit all-ones (mem) and 64-bit mixed/all-ones (reg)
popcntl -32(%rsp), %r10d        # 0xffffffff -> 32
movq $-1, %rax
popcntq %rax, %r11              # 0xffffffffffffffff -> 64
movabsq $0x0123456789abcdef, %rax
popcntq %rax, %rbx              # 32

# Final check: set CF/AF/SF/PF and verify final popcntq leaves CF=PF=AF=SF=OF=0 and ZF=1
movb $0x80, %al
subb $0x81, %al
popcntq -8(%rsp), %rdi
