# Undefined flags: n, z, c, v
# Construct a full 64-bit constant 0x123456789abcdef0 in x0:
movz x0, #0xdef0, lsl #0
movk x0, #0x9abc, lsl #16
movk x0, #0x5678, lsl #32
movk x0, #0x1234, lsl #48

# Construct a 32-bit constant 0xdeadbeef in w1:
movz w1, #0xbeef, lsl #0
movk w1, #0xdead, lsl #16

# Construct a 64-bit constant with inverted base and movk overrides in x2:
movn x2, #0, lsl #0
movk x2, #0x0000, lsl #16
movk x2, #0x1234, lsl #32
