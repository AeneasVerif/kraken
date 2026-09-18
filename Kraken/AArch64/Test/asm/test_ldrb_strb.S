# Undefined flags: n, z, c, v

// Pre-decrement store: allocate 32 bytes on stack, store byte from random w1 at [SP]
strb w1, [sp, #-32]!

// Write to various offsets in the allocated 32-byte frame [SP, SP+31]
strb w2, [sp, #1]
sturb w3, [sp, #2]
strb w4, [sp, #3]
strb w5, [sp, #4]
sturb w6, [sp, #5]
strb w7, [sp, #6]
sturb w8, [sp, #7]
strb w9, [sp, #8]
sturb w10, [sp, #15]
strb w11, [sp, #16]
sturb w12, [sp, #31]

// Read back from the exact offsets written
ldrb w13, [sp, #0]
ldrb w14, [sp, #1]
ldurb w15, [sp, #2]
ldrb w16, [sp, #3]
ldrb w17, [sp, #4]
ldurb w18, [sp, #5]
ldrb w19, [sp, #6]
ldurb w20, [sp, #7]
ldrb w21, [sp, #8]
ldurb w22, [sp, #15]
ldrb w23, [sp, #16]
ldurb w24, [sp, #31]

// Post-increment load: load byte from [SP] (offset 0), then SP = SP + 16
ldrb w25, [sp], #16

// Now SP is at old SP+16. Read using both positive and negative offsets:
ldrb w26, [sp, #0]
ldurb w27, [sp, #15]
ldrb w28, [sp, #-16]
ldurb w29, [sp, #-9]

// Pre-decrement load: SP = SP - 16 (SP returns to base of 32-byte frame)
ldrb w30, [sp, #-16]!

// Register offset stores and loads within initialized range
mov x1, #2
strb w2, [sp, x1]
ldrb w3, [sp, x1]

mov w4, #4
strb w5, [sp, w4, uxtw]
ldrb w6, [sp, w4, uxtw]

mov w7, #6
strb w8, [sp, w7, sxtw]
ldrb w9, [sp, w7, sxtw]

// Clean up stack pointer: SP = SP + 32
ldr xzr, [sp], #32
