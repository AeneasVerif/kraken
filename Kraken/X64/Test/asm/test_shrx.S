# Test BMI2 shift logical right without affecting flags
# Tests: shrxl, shrxq

movq $0xF000000000000100, %rax
movq $4, %rdx
shrxq %rdx, %rax, %r8            # r8 = 0x0F00000000000010

movq $0xFFFFFFFF00000000, %r9
movl $0xF0000100, %eax
movl $36, %edx                   # 36 & 31 = 4
shrxl %edx, %eax, %r9d           # r9 = 0x000000000F000010

# Memory source
movq $0x8000000000000080, %rax
pushq %rax
movq $68, %rdx                   # 68 & 63 = 4
shrxq %rdx, (%rsp), %r10         # r10 = 0x0800000000000008
popq %rax
