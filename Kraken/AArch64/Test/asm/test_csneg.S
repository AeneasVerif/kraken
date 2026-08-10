# Undefined flags: n, z, c, v
# Set Z flag (EQ is true, NE is false)
cmp xzr, xzr
csneg x0, x1, x2, eq
csneg x3, x1, x2, ne
cneg x4, x1, eq
cneg x5, x1, ne
cneg w6, w1, eq
cneg w7, w1, ne
