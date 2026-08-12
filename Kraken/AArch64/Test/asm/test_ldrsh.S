# Undefined flags: n, z, c, v

// Pre-decrement store: allocate 32 bytes on stack, store halfword from random w1 at [SP]
strh w1, [sp, #-32]!

// Store random halfwords across 32-byte frame [SP, SP+31]
strh w2, [sp, #2]
sturh w3, [sp, #4]
strh w4, [sp, #6]
sturh w5, [sp, #8]
strh w6, [sp, #16]
sturh w7, [sp, #30]
sturh w8, [sp, #11]

// Sign-extended halfword loads into 32-bit and 64-bit registers
ldrsh w9, [sp, #0]
ldrsh x10, [sp, #0]
ldrsh w11, [sp, #2]
ldrsh x12, [sp, #2]
ldursh w13, [sp, #4]
ldursh x14, [sp, #4]
ldrsh w15, [sp, #6]
ldrsh x16, [sp, #6]
ldursh w17, [sp, #8]
ldursh x18, [sp, #8]
ldrsh w19, [sp, #16]
ldrsh x20, [sp, #16]
ldursh w21, [sp, #30]
ldursh x22, [sp, #30]
ldursh w23, [sp, #11]
ldursh x24, [sp, #11]

// Post-increment load: load sign-extended halfword from [SP], then SP = SP + 16
ldrsh w25, [sp], #16

// Negative offset loads relative to new SP
ldrsh w26, [sp, #-16]
ldrsh x27, [sp, #-16]
ldursh w28, [sp, #-12]
ldursh x29, [sp, #-12]

// Pre-decrement load: SP = SP - 16 (SP returns to base of 32-byte frame)
ldrsh x30, [sp, #-16]!

// Register offset loads
mov x1, #3
ldrsh w2, [sp, x1, lsl #1]
ldrsh x3, [sp, x1, lsl #1]

mov w4, #1
ldrsh w5, [sp, w4, uxtw #1]
ldrsh x6, [sp, w4, uxtw #1]
ldrsh w7, [sp, w4, sxtw #1]
ldrsh x8, [sp, w4, sxtw #1]

// Clean up stack pointer: SP = SP + 32
ldr xzr, [sp], #32
