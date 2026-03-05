# Test conditional instructions
# Tests: setc, setnc, test
#
# Note: Avoiding cmov and push/pop which may need more parser support

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
    # ----- TEST instruction (64-bit) -----
    movq $0xFF, %rax
    testq %rax, %rax                 # Sets ZF=0 (non-zero)
    # ZF should be 0

    # ----- TESTB instruction (8-bit) -----
    # Test 8-bit immediate against al
    movq $0x55, %rax                 # al = 0x55 (01010101)
    testb $0xAA, %al                 # AND with 0xAA (10101010) = 0, ZF=1
    setnc %r9b                       # r9b = 1 (CF=0 after testb)
    # Expected: ZF=1, r9 has low byte set

    # Test 8-bit reg against 8-bit reg
    movq $0xFF, %rcx                 # cl = 0xFF
    movq $0x0F, %rdx                 # dl = 0x0F
    testb %dl, %cl                   # AND cl with dl = 0x0F, ZF=0
    # Expected: ZF=0 (result non-zero)

    # ----- SETC / SETNC (set byte on carry) -----
    # First, create carry condition
    movq $0xFFFFFFFFFFFFFFFF, %rbx
    addq $1, %rbx                    # Overflow sets CF
    setc %cl                         # cl = 1 (CF was set)
    # Expected: rcx = 1

    xorq %rdx, %rdx
    addq $1, %rdx                    # No overflow
    setc %dl                         # dl = 0 (CF not set)
    # Expected: rdx = 0

    movq $0, %rsi
    setnc %sil                       # sil = 1 (CF not set after last addq)
    # Expected: rsi = 1

    # ----- PUSH / POP -----
    movq $0x1234567890ABCDEF, %rdi
    push %rdi
    pop %r8
    # Expected: r8 = 0x1234567890ABCDEF

    # ----- CMOVC (conditional move if carry) -----
    # Test 1: CF=1 case (move should happen)
    movq $0xFFFFFFFFFFFFFFFF, %r9
    addq $1, %r9                     # Causes overflow, sets CF=1
    movq $0x1111, %r10
    movq $0x2222, %r11
    cmovc %r10, %r11                 # CF=1, so r11 = r10 = 0x1111
    # Expected: r11 = 0x1111

    # Test 2: CF=0 case (no move)
    xorq %rax, %rax                  # Clears CF
    movq $0x3333, %r12
    movq $0x4444, %r13
    cmovc %r12, %r13                 # CF=0, so r13 stays 0x4444
    # Expected: r13 = 0x4444

    # ----- CMOVE (conditional move if zero) -----
    # Test 3: ZF=1 case (move should happen)
    movq $0x5555, %r14
    xorq %rax, %rax                  # Sets ZF=1
    movq $0x6666, %rbp
    cmove %r14, %rbp                 # ZF=1, so rbp = r14 = 0x5555
    # Expected: rbp = 0x5555

    # Initialize remaining register
    movq $42, %r15

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
