# Undefined flags: n, z, c, v
# Set Z flag (EQ is true, NE is false)
cmp xzr, xzr
csel x0, x1, x2, eq
csel x3, x1, x2, ne
csel w4, w1, w2, eq
csel w5, w1, w2, ne
