# Undefined flags: n, z, c, v

// Allocate 32 bytes on stack: SP = SP - 32 (16-byte aligned SP)
str x1, [sp, #-32]!

// 1. Explicit LDUR and STUR mnemonics with positive offsets
stur x1, [sp, #8]
ldur x2, [sp, #8]

// 2. Explicit LDUR and STUR mnemonics with negative offsets
stur x1, [sp, #-8]
ldur x3, [sp, #-8]

// 3. Automatic STR -> STUR and LDR -> LDUR conversion with negative offsets
str x1, [sp, #-16]
ldr x4, [sp, #-16]

// Restore SP: SP = SP + 32
ldr xzr, [sp], #32
