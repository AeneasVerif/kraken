# Test: Single-argument shift/rotate syntax (implicit count = 1)
# Commit: 9e82042 - Support GNU AS single argument shift syntax
# Tests: shl, shr, sar, sal, rol, ror with no explicit shift count
#
# GNU AS allows `shr %reg` as shorthand for `shr $1, %reg`.
# This test verifies all shift/rotate families in both suffixed and
# unsuffixed forms.
#
# Note: The last flag-setting instruction is `addq $0` which sets AF
# deterministically, avoiding the known AF-undefined issue with shifts.

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
    # ----- SHR single-arg (implicit $1) -----
    movq $0x8000000000000004, %rax
    shrq %rax                        # rax >>= 1
    # Expected: rax = 0x4000000000000002

    # ----- SHL single-arg (implicit $1) -----
    movq $0x4000000000000001, %rbx
    shlq %rbx                        # rbx <<= 1
    # Expected: rbx = 0x8000000000000002

    # ----- SAR single-arg (sign-extending) -----
    movq $0x8000000000000004, %rcx
    sarq %rcx                        # arithmetic shift right by 1
    # Expected: rcx = 0xC000000000000002 (sign bit preserved)

    # ----- SAL single-arg (same as SHL) -----
    movq $0x4000000000000001, %rdx
    salq %rdx                        # rdx <<= 1
    # Expected: rdx = 0x8000000000000002

    # ----- ROL single-arg (rotate left by 1) -----
    movq $0x8000000000000001, %rsi
    rolq %rsi
    # Expected: rsi = 0x0000000000000003 (MSB wraps to LSB)

    # ----- ROR single-arg (rotate right by 1) -----
    movq $0x8000000000000001, %rdi
    rorq %rdi
    # Expected: rdi = 0xC000000000000000 (LSB wraps to MSB + sign)

    # ----- 32-bit single-arg shift (shrl) -----
    movl $0x80000004, %r8d
    shrl %r8d
    # Expected: r8d = 0x40000002 -> r8 = 0x40000002

    # ----- Unsuffixed single-arg shift -----
    movq $0x100, %r9
    shr %r9                          # unsuffixed, implicit $1
    # Expected: r9 = 0x80

    # ----- Unsuffixed single-arg rotate -----
    movq $0x8000000000000001, %r10
    rol %r10
    # Expected: r10 = 0x0000000000000003

    # ----- Verify two-arg still works alongside single-arg -----
    movq $0xFF, %r11
    shrq $4, %r11                    # explicit $4
    # Expected: r11 = 0x0F

    # Set flags deterministically: AF is undefined after shifts,
    # Kraken models this as `true` but for some real hardware it will be false.
    # The test harness compares all flags including AF. Use addq $0 to reset
    # AF to a known state matching both hardware and Kraken.
    addq $0, %r11

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
