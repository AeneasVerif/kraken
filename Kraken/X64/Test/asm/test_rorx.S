# Test BMI2 rotate right logical without affecting flags
# Tests: rorxl, rorxq

movq $0x0123456789ABCDEF, %rax
rorxq $8, %rax, %rbx             # rbx = 0xEF0123456789ABCD

movq $0xFFFFFFFF00000000, %rcx
movl $0x12345678, %eax
rorxl $36, %eax, %ecx            # 36 & 31 = 4 -> rcx = 0x0000000081234567

# Memory source
movq $0xFEDCBA9876543210, %rax
pushq %rax
rorxq $72, (%rsp), %rdx          # 72 & 63 = 8 -> rdx = 0x10FEDCBA98765432
popq %rax
