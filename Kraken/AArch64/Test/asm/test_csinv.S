# Undefined flags: n, z, c, v
# Set Z flag (EQ is true, NE is false)
cmp xzr, xzr
csinv x0, x1, x2, eq
csinv x3, x1, x2, ne
csetm x4, eq
csetm x5, ne
cinv x6, x1, eq
cinv x7, x1, ne
csetm w8, eq
cinv w9, w1, ne
