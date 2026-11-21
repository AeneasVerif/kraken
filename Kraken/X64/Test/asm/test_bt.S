# Undefined flags: of, sf, af, pf
xorl %ebx, %ebx
xorl %edx, %edx
xorl %edi, %edi
xorl %r8d, %r8d
xorl %r10d, %r10d
xorl %r12d, %r12d
xorl %r14d, %r14d
movabsq $0xdeadbeef00000001, %rax
movq $64, %rcx
btq %rcx, %rax
setc %bl
setz %dl
btl $32, %eax
setc %r8b
movabsq $0xdeadbeef00000001, %rsi
movl $63, %ecx
btsl %ecx, %esi
setc %dil
movabsq $0xdeadbeef00000001, %r9
btsw $255, %r9w
setc %r10b
movq $1, %r11
btsq %r11, %r11
setc %r12b
movabsq $0x8000000000000000, %r13
movq $-1, %rcx
btq %rcx, %r13
setc %r14b
movq $1, %r15
btsq $255, %r15
movl $31, %ecx
btw %cx, %r9w
btq $255, %r15
