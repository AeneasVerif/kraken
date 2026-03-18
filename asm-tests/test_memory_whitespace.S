# Test: Memory operand parsing with whitespace between displacement and parenthesis
# Tests: This specifically tests the bug where `0 (%rdi)` (space before paren) failed to parse
#
# The GNU assembler accepts whitespace between displacement and parenthesis, e.g.:
#   leaq 0 (%rdi), %rax
#   leaq 16 (%rbx, %rcx, 4), %rsi
#
# This test ensures Kraken's parser also accepts this syntax.
# Uses only register operations (no RIP-relative memory) for parser compatibility.

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
    movq $100, %rdi
    movq $200, %rbx
    movq $2, %rcx

    # Test 1: leaq with space between displacement and paren
    leaq 0 (%rdi), %rax          # Space between 0 and ( -> rax = 100

    # Test 2: leaq with larger displacement and space
    leaq 8 (%rdi), %r8           # Space between 8 and ( -> r8 = 108

    # Test 3: leaq with displacement + base + index*scale, with spacing
    leaq 16 (%rbx, %rcx, 4), %rsi # Space between 16 and ( -> rsi = 200 + 16 + 2*4 = 224

    # Test 4: Zero displacement with index and scale, with spacing
    leaq 0 (%rdi, %rcx, 8), %rdx  # Space between 0 and ( -> rdx = 100 + 2*8 = 116

    # Final expected state:
    # rax = 100 (from leaq 0 (%rdi), %rax)
    # rbx = 200
    # rcx = 2
    # rdx = 116 (from leaq 0 (%rdi, %rcx, 8), %rdx)
    # rsi = 224 (from leaq 16 (%rbx, %rcx, 4), %rsi)
    # rdi = 100
    # r8 = 108 (from leaq 8 (%rdi), %r8)

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
