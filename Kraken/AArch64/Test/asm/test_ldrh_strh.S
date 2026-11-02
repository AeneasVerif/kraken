# Undefined flags: n, z, c, v

// Pre-decrement store: allocate 32 bytes on stack, store halfword from random w1 at [SP]
strh w1, [sp, #-32]!

// Scaled and unscaled halfword stores across 32-byte frame [SP, SP+31]
strh w2, [sp, #2]
strh w3, [sp, #4]
strh w4, [sp, #6]
sturh w5, [sp, #8]
sturh w6, [sp, #10]
sturh w7, [sp, #16]
sturh w8, [sp, #30]
sturh w9, [sp, #13]

// Read back from exact offsets written
ldrh w10, [sp, #0]
ldrh w11, [sp, #2]
ldrh w12, [sp, #4]
ldrh w13, [sp, #6]
ldurh w14, [sp, #8]
ldurh w15, [sp, #10]
ldurh w16, [sp, #13]
ldrh w17, [sp, #16]
ldurh w18, [sp, #30]

// Post-increment load: load halfword from [SP], then SP = SP + 16
ldrh w19, [sp], #16

// Relative loads from new SP (old SP+16)
ldrh w20, [sp, #0]
ldurh w21, [sp, #14]
ldrh w22, [sp, #-16]
ldurh w23, [sp, #-10]

// Pre-decrement load: SP = SP - 16 (SP returns to base of 32-byte frame)
ldrh w24, [sp, #-16]!

// Register offset stores and loads
mov x25, #2
strh w26, [sp, x25, lsl #1]
ldrh w27, [sp, x25, lsl #1]

mov w28, #3
strh w29, [sp, w28, uxtw #1]
ldrh w30, [sp, w28, uxtw #1]
strh w1, [sp, w28, sxtw #1]
ldrh w2, [sp, w28, sxtw #1]

// Clean up stack pointer: SP = SP + 32
ldr xzr, [sp], #32
