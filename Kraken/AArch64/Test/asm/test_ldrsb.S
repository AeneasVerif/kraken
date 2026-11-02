# Undefined flags: n, z, c, v

// Pre-decrement store: allocate 32 bytes on stack, store byte from random w1 at [SP]
strb w1, [sp, #-32]!

// Store random bytes across 32-byte frame [SP, SP+31]
strb w2, [sp, #1]
sturb w3, [sp, #2]
strb w4, [sp, #3]
sturb w5, [sp, #4]
sturb w6, [sp, #16]
sturb w7, [sp, #31]

// Sign-extended byte loads into 32-bit and 64-bit registers
ldrsb w8, [sp, #0]
ldrsb x9, [sp, #0]
ldrsb w10, [sp, #1]
ldrsb x11, [sp, #1]
ldursb w12, [sp, #2]
ldursb x13, [sp, #2]
ldrsb w14, [sp, #3]
ldrsb x15, [sp, #3]
ldursb w16, [sp, #4]
ldursb x17, [sp, #4]
ldrsb w18, [sp, #16]
ldrsb x19, [sp, #16]
ldursb w20, [sp, #31]
ldursb x21, [sp, #31]

// Post-increment load: load sign-extended byte from [SP], then SP = SP + 16
ldrsb w22, [sp], #16

// Negative offset loads relative to new SP
ldrsb w23, [sp, #-16]
ldrsb x24, [sp, #-16]
ldursb w25, [sp, #-15]
ldursb x26, [sp, #-15]

// Pre-decrement load: SP = SP - 16 (SP returns to base of 32-byte frame)
ldrsb x27, [sp, #-16]!

// Register offset loads
mov x28, #3
ldrsb w29, [sp, x28]
ldrsb x30, [sp, x28]

mov w1, #4
ldrsb w2, [sp, w1, uxtw]
ldrsb x3, [sp, w1, uxtw]
ldrsb w4, [sp, w1, sxtw]
ldrsb x5, [sp, w1, sxtw]

// Clean up stack pointer: SP = SP + 32
ldr xzr, [sp], #32
