# Test: Multiplication Operations
# Tests: mulq, imulq
#
# Expected results:
#   rdx:rax = 10 * 20 = 200 (mulq puts result in rdx:rax)
#   r8 = 5 * 7 = 35 (imulq two-operand form)

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
    # Test mulq (unsigned multiply, result in rdx:rax)
    movq $10, %rax
    movq $20, %rbx
    mulq %rbx               # rdx:rax = 10 * 20 = 200
    # rax = 200, rdx = 0 (no overflow for small numbers)

    # Save mulq result
    movq %rax, %rcx         # rcx = 200 (low part)
    movq %rdx, %rsi         # rsi = 0 (high part)

    # Test imulq (signed multiply, two-operand form)
    movq $5, %r8
    movq $7, %r9
    imulq %r9, %r8          # r8 = 5 * 7 = 35

    # Test imulq with immediate (two-operand form with immediate)
    movq $6, %r10
    imulq $11, %r10         # r10 = 6 * 11 = 66

    # Restore rax for output
    movq %rcx, %rax

    jmp _kraken_capture

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
