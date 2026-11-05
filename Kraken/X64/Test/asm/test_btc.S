# Undefined flags: of, sf, af, pf

# Test bit test and complement instruction
# Tests: btcw, btcl, btcq (register/memory, immediate/register bit index, CF and ZF preservation)

# ----- 64-bit btcq with immediate and register bit index -----
xorq %rax, %rax                  # ZF = 1
movq $0x0000000000000008, %rbx
btcq $3, %rbx                    # toggles bit 3 (1 -> 0): rbx = 0, CF = 1, ZF preserved (1)
movq $67, %rcx                   # 67 mod 64 = 3
btcq %rcx, %rbx                  # toggles bit 3 (0 -> 1): rbx = 8, CF = 0, ZF preserved (1)

# ----- 32-bit btcl (clears upper 32 bits on reg) -----
movq $0xFFFFFFFF00000001, %rdx
btcl $0, %edx                    # edx = 0 (upper 32 cleared), CF = 1

# ----- 16-bit btcw (preserves upper 48 bits on reg) -----
movq $0x1122334455660000, %rsi
btcw $15, %si                    # si = 0x8000, CF = 0

# ----- Memory bit-string indexing with register bit offset -----
pushq $0                         # 8(%rsp)
pushq $0                         # 0(%rsp)
movq $37, %rcx                   # word 1 (byte +4), bit 5 in 32-bit mode; bit 37 in 64-bit mode
btcl %ecx, (%rsp)                # sets bit 5 of 4(%rsp), CF = 0
btcq $37, (%rsp)                 # toggles bit 37 of 0(%rsp) back to 0, CF = 1
popq %rdi                        # rdi = 0
popq %r8                         # r8 = 0
