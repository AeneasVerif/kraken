# Undefined flags: n, z, c, v

// Pre-decrement store: allocate 32 bytes on stack, store pair from random (w1, w2)
stp w1, w2, [sp, #-32]!

// Store random word pairs across 32-byte frame [SP, SP+31]
stp w3, w4, [sp, #8]
stp w5, w6, [sp, #16]
stp w7, w8, [sp, #24]

// Standard offset ldpsw into 64-bit registers
ldpsw x9, x10, [sp, #0]
ldpsw x11, x12, [sp, #8]
ldpsw x13, x14, [sp, #16]
ldpsw x15, x16, [sp, #24]

// Pre-increment ldpsw: SP = SP + 16
ldpsw x17, x18, [sp, #16]!

// Relative ldpsw loads from new SP
ldpsw x19, x20, [sp, #-16]
ldpsw x21, x22, [sp, #-8]
ldpsw x23, x24, [sp, #0]
ldpsw x25, x26, [sp, #8]

// Post-increment ldpsw: load from [SP], then SP = SP + 16
ldpsw x27, x28, [sp], #16

// Pre-decrement ldpsw: SP = SP - 32
ldpsw x29, x30, [sp, #-32]!

// Post-increment ldpsw to restore SP: SP = SP + 32
ldpsw x1, x2, [sp], #32
