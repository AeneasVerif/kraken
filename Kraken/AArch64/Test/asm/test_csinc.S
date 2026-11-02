# Undefined flags: n, z, c, v
# Set Z flag (EQ is true, NE is false)
cmp xzr, xzr
csinc x0, x1, x2, eq
csinc x3, x1, x2, ne
cset x4, eq
cset x5, ne
cinc x6, x1, eq
cinc x7, x1, ne
cset w8, eq
cinc w9, w1, ne
