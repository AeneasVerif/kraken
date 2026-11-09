# Test BMI2 shift logical left without affecting flags
# Tests: shlxl, shlxq

movq $0x0001020304050607, %rax
movq $72, %rdx                   # 72 & 63 = 8
shlxq %rdx, %rax, %rsi           # rsi = 0x0102030405060700

movq $0xFFFFFFFF00000000, %rdi
movl $0x00112233, %eax
movl $36, %edx                   # 36 & 31 = 4
shlxl %edx, %eax, %edi           # rdi = 0x0000000001122330

# Memory source
movq $0x0102030405060708, %rax
pushq %rax
movq $4, %rdx
shlxq %rdx, (%rsp), %r8          # r8 = 0x1020304050607080
popq %rax
