# The 32-to-64-bit sign extension: Intel `movsxd`, AT&T `movslq`.
movl $0x80000001, %eax
movslq %eax, %rbx
movl $0x7ffffffe, %ecx
movslq %ecx, %rdx
movslq %r13d, %rcx
