# Undefined flags: n, z, c, v

// Pre-decrement store: allocate 32 bytes on stack, store word from random w1 at [SP]
str w1, [sp, #-32]!

// Store random words across 32-byte frame [SP, SP+31]
str w2, [sp, #4]
stur w3, [sp, #8]
str w4, [sp, #12]
stur w5, [sp, #16]
str w6, [sp, #20]
stur w7, [sp, #28]

// Sign-extended word loads into 64-bit registers
ldrsw x8, [sp, #0]
ldrsw x9, [sp, #4]
ldursw x10, [sp, #8]
ldrsw x11, [sp, #12]
ldursw x12, [sp, #16]
ldrsw x13, [sp, #20]
ldursw x14, [sp, #28]

// Post-increment load: load sign-extended word from [SP], then SP = SP + 16
ldrsw x15, [sp], #16

// Relative loads from new SP
ldrsw x16, [sp, #-16]
ldrsw x17, [sp, #-12]
ldursw x18, [sp, #-8]
ldrsw x19, [sp, #0]
ldursw x20, [sp, #12]

// Pre-decrement load: SP = SP - 16 (SP returns to base of 32-byte frame)
ldrsw x21, [sp, #-16]!

// Register offset loads
mov x22, #1
ldrsw x23, [sp, x22, lsl #2]

mov w24, #2
ldrsw x25, [sp, w24, uxtw #2]
ldrsw x26, [sp, w24, sxtw #2]

// Clean up stack pointer: SP = SP + 32
ldr xzr, [sp], #32
