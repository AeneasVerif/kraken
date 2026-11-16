# Test: vinserti64x4 replaces the 256-bit half the immediate picks
# Requires: avx512f

subq $0x100, %rsp
movq $0x706050403020100, %rcx
movq %rcx, 0(%rsp)
movq $0xf0e0d0c0b0a0908, %rcx
movq %rcx, 8(%rsp)
movq $0x1716151413121110, %rcx
movq %rcx, 16(%rsp)
movq $0x1f1e1d1c1b1a1918, %rcx
movq %rcx, 24(%rsp)
movq $0x2726252423222120, %rcx
movq %rcx, 32(%rsp)
movq $0x2f2e2d2c2b2a2928, %rcx
movq %rcx, 40(%rsp)
movq $0x3736353433323130, %rcx
movq %rcx, 48(%rsp)
movq $0x3f3e3d3c3b3a3938, %rcx
movq %rcx, 56(%rsp)
movq $0x5756555453525150, %rcx
movq %rcx, 64(%rsp)
movq $0x5f5e5d5c5b5a5958, %rcx
movq %rcx, 72(%rsp)
movq $0x6766656463626160, %rcx
movq %rcx, 80(%rsp)
movq $0x6f6e6d6c6b6a6968, %rcx
movq %rcx, 88(%rsp)
movq $0x7776757473727170, %rcx
movq %rcx, 96(%rsp)
movq $0x7f7e7d7c7b7a7978, %rcx
movq %rcx, 104(%rsp)
movq $0x8786858483828180, %rcx
movq %rcx, 112(%rsp)
movq $0x8f8e8d8c8b8a8988, %rcx
movq %rcx, 120(%rsp)

vmovdqu32 0(%rsp), %zmm0
vmovdqu32 64(%rsp), %zmm1
vinserti64x4 $0, %ymm1, %zmm0, %zmm2
vinserti64x4 $1, %ymm1, %zmm0, %zmm3
vinserti64x4 $1, 96(%rsp), %zmm0, %zmm4
vinserti64x4 $3, %ymm1, %zmm0, %zmm5

addq $0x100, %rsp
