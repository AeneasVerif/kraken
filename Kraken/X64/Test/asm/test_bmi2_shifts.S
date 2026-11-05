# Test BMI2 shift and rotate instructions (do not modify flags)
# Tests: rorxl, rorxq, shlxl, shlxq, shrxl, shrxq, sarxl, sarxq

# ----- rorxq & rorxl -----
movq $0x0123456789ABCDEF, %rax
rorxq $8, %rax, %rbx             # rbx = 0xEF0123456789ABCD
movq $0xFFFFFFFF00000000, %rcx
movl $0x12345678, %eax
rorxl $36, %eax, %ecx            # 36 & 31 = 4 -> rcx = 0x0000000081234567

# ----- shlxq & shlxl -----
movq $0x0001020304050607, %rax
movq $72, %rdx                   # 72 & 63 = 8
shlxq %rdx, %rax, %rsi           # rsi = 0x0102030405060700
movq $0xFFFFFFFF00000000, %rdi
movl $0x00112233, %eax
movl $36, %edx                   # 36 & 31 = 4
shlxl %edx, %eax, %edi           # rdi = 0x0000000001122330

# ----- shrxq & shrxl -----
movq $0xF000000000000100, %rax
movq $4, %rdx
shrxq %rdx, %rax, %r8            # r8 = 0x0F00000000000010
movq $0xFFFFFFFF00000000, %r9
movl $0xF0000100, %eax
shrxl %edx, %eax, %r9d           # r9 = 0x000000000F000010

# ----- sarxq & sarxl (sign-extending) + memory source -----
movq $0xF000000000000100, %rax
pushq %rax
sarxq %rdx, (%rsp), %r10         # r10 = 0xFF00000000000010
movl $0xF0000100, (%rsp)
sarxl %edx, (%rsp), %r11d        # r11 = 0x00000000FF000010
popq %rax                        # restores rsp, leaves all flags untouched
