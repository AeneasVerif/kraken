// 128-bit add: (x1:x0) + (x3:x2) -> (x5:x4)
adds x4, x0, x2
adc  x5, x1, x3

// 64-bit add (32-bit regs): (w1:w0) + (w3:w2) -> (w5:w4)
adds w4, w0, w2
adcs w5, w1, w3

// Carry propagate: x6 = x4 + x5 + C
adcs x6, x4, x5
