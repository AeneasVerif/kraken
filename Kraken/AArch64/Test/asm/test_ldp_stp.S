# Undefined flags: n, z, c, v

// Pre-decrement STP: SP = SP - 32, store pair (x1, x2) at [SP]
stp x1, x2, [sp, #-32]!

// Offset STP: store pair (w3, w4) at [SP + 16]
stp w3, w4, [sp, #16]

// Pre-increment LDP: SP = SP + 16, load pair (w7, w8) from [SP]
ldp w7, w8, [sp, #16]!

// Pre-decrement LDP: SP = SP - 16, load pair (x5, x6) from [SP]
ldp x5, x6, [sp, #-16]!

// Post-increment LDP: load pair (x9, x10) from [SP], then SP = SP + 32
ldp x9, x10, [sp], #32
