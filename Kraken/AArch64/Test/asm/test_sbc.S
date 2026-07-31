// 128-bit sub: (x1:x0) - (x3:x2) -> (x5:x4)
subs x4, x0, x2
sbc  x5, x1, x3

// 64-bit sub (32-bit regs): (w1:w0) - (w3:w2) -> (w7:w6)
subs w6, w0, w2
sbcs w7, w1, w3

// Borrow propagate: x8 = x4 - x5 - !C
sbcs x8, x4, x5
