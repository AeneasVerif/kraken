# Undefined flags: n, z, c, v

// Pre-decrement store: SP = SP - 32, store x1 at [SP]
str x1, [sp, #-32]!
str x2, [sp, #16]

// Post-increment store: store w3 at [SP], then SP = SP + 16 (SP becomes S - 16)
str w3, [sp], #16

// Pre-decrement load: SP = SP - 16 (SP becomes S - 32), load x4 from [SP]
ldr x4, [sp, #-16]!

// Pre-increment load: SP = SP + 16 (SP becomes S - 16), load x0 from [SP]
ldr x0, [sp, #16]!

// Post-increment load: load x6 from [SP], then SP = SP + 16 (SP becomes S)
ldr x6, [sp], #16
