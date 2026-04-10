# Test: Displacement-parenthesis whitespace tolerance
# Commit: 2b0af28 - Parser whitespace fix
# Tests: Tolerate spaces between displacement and open parenthesis in memory
#        operands, e.g. `leaq 0 (%rdi), %rax` instead of `leaq 0(%rdi), %rax`
#
# GNU AS accepts whitespace between displacement and '(' in memory operands.
# This test uses leaq to exercise the parser fix without requiring actual
# memory access (Kraken has limited memory support).

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
    # Setup base values
    movq $1000, %rdi
    movq $2000, %rbx
    movq $3, %rcx

    # Test 1: leaq with space between 0 and (
    leaq 0 (%rdi), %rax             # rax = 1000

    # Test 2: leaq with space between displacement and (
    leaq 8 (%rdi), %rdx             # rdx = 1008

    # Test 3: leaq with displacement + base + index*scale, with spacing
    leaq 16 (%rbx, %rcx, 4), %rsi   # rsi = 2000 + 16 + 3*4 = 2028

    # Test 4: Negative displacement with space
    leaq -8 (%rdi), %r8             # r8 = 992

    # Test 5: Large displacement with space
    leaq 256 (%rbx), %r9            # r9 = 2256

    # Test 6: Zero displacement with index and scale, with spacing
    leaq 0 (%rdi, %rcx, 8), %r10    # r10 = 1000 + 3*8 = 1024

    # Test 7: addq to put a deterministic value in r11 (so we test more regs)
    movq $42, %r11

    # Final expected:
    # rax = 1000, rbx = 2000, rcx = 3, rdx = 1008
    # rsi = 2028, rdi = 1000
    # r8 = 992, r9 = 2256, r10 = 1024, r11 = 42

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
