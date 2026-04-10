# Test: Suffixed mul instruction variants
# Commit: 20d9d63 - Parser fixes for missing instruction variants
# Tests: mulq, mull (suffixed one-operand multiply, which were previously
#        missing from the parser)
#
# `mulq %reg` performs unsigned rdx:rax = rax * reg (64-bit)
# `mull %reg` performs unsigned edx:eax = eax * reg (32-bit)

.data
.align 8
final_rax: .quad 0
final_rbx: .quad 0
final_rcx: .quad 0
final_rdx: .quad 0
final_rsi: .quad 0
final_rdi: .quad 0
final_rsp: .quad 0
final_rbp: .quad 0
final_r8: .quad 0
final_r9: .quad 0
final_r10: .quad 0
final_r11: .quad 0
final_r12: .quad 0
final_r13: .quad 0
final_r14: .quad 0
final_r15: .quad 0
final_flags: .quad 0

.text
.globl _start
_start:
    # ----- Test 1: mulq (64-bit, suffixed) -----
    movq $100, %rax
    movq $7, %rbx
    mulq %rbx                        # rdx:rax = 100 * 7 = 700
    # Expected: rax = 700 (0x2BC), rdx = 0

    # Save results
    movq %rax, %r8                   # r8 = 700
    movq %rdx, %r9                   # r9 = 0

    # ----- Test 2: mulq with larger values producing high bits -----
    movq $0x100000000, %rax          # 2^32
    movq $0x100000000, %rcx          # 2^32
    mulq %rcx                        # rdx:rax = 2^64
    # Expected: rax = 0, rdx = 1

    # Save results
    movq %rax, %r10                  # r10 = 0
    movq %rdx, %r11                  # r11 = 1

    # ----- Test 3: mull (32-bit, suffixed) -----
    movl $50, %eax
    movl $6, %esi
    mull %esi                        # edx:eax = 50 * 6 = 300
    # Expected: eax = 300 (0x12C), edx = 0

    # Save results
    movq %rax, %r12                  # r12 = 300
    movq %rdx, %r13                  # r13 = 0

    # ----- Test 4: Unsuffixed mul still works -----
    movq $25, %rax
    movq $4, %rdi
    mul %rdi                         # rdx:rax = 25 * 4 = 100
    # Expected: rax = 100, rdx = 0

    # Restore saved values for capture
    movq %rax, %r14                  # r14 = 100
    movq %rdx, %r15                  # r15 = 0
    movq %r8, %rax                   # rax = 700 (test 1 result)
    movq %r9, %rbx                   # rbx = 0   (test 1 high)
    movq %r10, %rcx                  # rcx = 0   (test 2 low)
    movq %r11, %rdx                  # rdx = 1   (test 2 high)
    # rsi = clobbered by mull, but we saved to r12
    # rdi = 4 (from test 4)

    jmp _kraken_capture

# ====== KRAKEN CAPTURE EPILOGUE ======
_kraken_capture:
    movq %rax, final_rax(%rip)
    movq %rbx, final_rbx(%rip)
    movq %rcx, final_rcx(%rip)
    movq %rdx, final_rdx(%rip)
    movq %rsi, final_rsi(%rip)
    movq %rdi, final_rdi(%rip)
    movq %rsp, final_rsp(%rip)
    movq %rbp, final_rbp(%rip)
    movq %r8,  final_r8(%rip)
    movq %r9,  final_r9(%rip)
    movq %r10, final_r10(%rip)
    movq %r11, final_r11(%rip)
    movq %r12, final_r12(%rip)
    movq %r13, final_r13(%rip)
    movq %r14, final_r14(%rip)
    movq %r15, final_r15(%rip)
    pushfq
    popq %rax
    movq %rax, final_flags(%rip)

    movq $1, %rax
    movq $1, %rdi
    leaq final_rax(%rip), %rsi
    movq $136, %rdx
    syscall

    movq $60, %rax
    xorq %rdi, %rdi
    syscall
