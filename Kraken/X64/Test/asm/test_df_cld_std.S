# Test: cld/std set and clear DF (RFLAGS bit 10) and leave the status flags alone.

std                     # DF = 1
movq $1, %rax
subq $2, %rax           # CF = SF = 1; DF stays 1
cld                     # DF = 0, CF/SF unchanged
std                     # DF = 1, CF/SF unchanged

# Final state: rax = -1, CF = SF = 1, DF = 1
