# Test BMI2 shift arithmetic right without affecting flags
# Tests: sarxl, sarxq

movq $0xF000000000000100, %rax
movq $68, %rdx                   # 68 & 63 = 4
sarxq %rdx, %rax, %r8            # r8 = 0xFF00000000000010

movq $0xFFFFFFFF00000000, %r9
movl $0xF0000100, %eax
movl $36, %edx                   # 36 & 31 = 4
sarxl %edx, %eax, %r9d           # r9 = 0x00000000FF000010

# Memory source
movq $0xF000000000000100, %rax
pushq %rax
movq $4, %rdx
sarxq %rdx, (%rsp), %r10         # r10 = 0xFF00000000000010
movl $0xF0000100, (%rsp)
sarxl %edx, (%rsp), %r11d        # r11 = 0x00000000FF000010
popq %rax
