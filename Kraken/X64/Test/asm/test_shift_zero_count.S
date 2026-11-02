# 32-bit shifts/rotates by a (masked) count of 0 still write the destination, zero-extending it.
movabsq $0xffffffff12345678, %rax
movq %rax, %rbx
movq %rax, %rdx
movq %rax, %rsi
movq %rax, %rdi
movq %rax, %r8
movq %rax, %r9
movl $32, %ecx
shll $0, %eax
shrl %cl, %ebx
sarl $0, %edx
roll %cl, %esi
rorl $0, %edi
shldl $0, %eax, %r8d
shrdl %cl, %eax, %r9d
