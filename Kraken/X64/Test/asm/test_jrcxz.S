# Test jrcxz and jecxz, both taken and not taken
jrcxz .Lzero          # taken: rcx = 0
movq $1, %rax         # skipped
.Lzero:
movabsq $0x100000000, %rcx  # rcx = 2^32, ecx = 0
jecxz .Lecx_zero      # taken: ecx = 0
movq $2, %rbx         # skipped
.Lecx_zero:
jrcxz .Lend           # not taken: rcx != 0
movq $3, %rdx         # runs
.Lend:
