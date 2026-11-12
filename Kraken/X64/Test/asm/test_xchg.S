# Test exchange register/memory instruction
# Tests: xchgb, xchgw, xchgl, xchgq (register-register, register-memory, address aliasing, flag preservation)

# ----- 64-bit xchgq register-register -----
movq $0x1111222233334444, %rax
movq $0x5555666677778888, %rbx
xchgq %rax, %rbx                 # rax = 0x5555666677778888, rbx = 0x1111222233334444

# ----- 32-bit xchgl (zero-extends both registers) -----
movq $0xFFFFFFFF00000010, %rcx
movq $0xFFFFFFFF00000020, %rdx
xchgl %ecx, %edx                 # rcx = 0x20, rdx = 0x10

# ----- 16-bit xchgw and 8-bit xchgb -----
movq $0xAABBCCDD00001234, %rsi
movq $0xEEFF001100005678, %rdi
xchgw %si, %di                   # rsi low 16 = 0x5678, rdi low 16 = 0x1234
xchgb %sil, %dil                 # swaps low bytes: rsi low 16 = 0x5634, rdi low 16 = 0x1278

# ----- Memory operand (both operand orders & base-register aliasing) -----
movq $0xCAFEBABE12345678, %r8
pushq %r8
movq $0xDEADBEEF87654321, %r8
xchgq %r8, (%rsp)                # r8 = 0xCAFEBABE12345678, (%rsp) = 0xDEADBEEF87654321
xchgq (%rsp), %r8                # r8 = 0xDEADBEEF87654321, (%rsp) = 0xCAFEBABE12345678

# Address aliasing: base register of memory operand is the exchanged register
movq %rsp, %r9
xchgq %r9, (%r9)                 # (%rsp) receives old %r9 (rsp), %r9 receives 0xCAFEBABE12345678
popq %r10                        # r10 = rsp
subq %rsp, %r10                  # r10 = 0 (proves (%r9) used original %r9 address)
