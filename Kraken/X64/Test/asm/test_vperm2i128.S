# Test: vperm2i128 picks each 128-bit half from the four halves of its sources, or zeroes it

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

vmovdqu 0(%rsp), %ymm0
vmovdqu 64(%rsp), %ymm1
vperm2i128 $0x20, %ymm1, %ymm0, %ymm2
vperm2i128 $0x31, %ymm1, %ymm0, %ymm3
vperm2i128 $0x13, %ymm1, %ymm0, %ymm4
vperm2i128 $0x02, %ymm1, %ymm0, %ymm5
vperm2i128 $0x88, %ymm1, %ymm0, %ymm6
vperm2i128 $0x38, %ymm1, %ymm0, %ymm7
vperm2i128 $0x81, %ymm1, %ymm0, %ymm8
vperm2i128 $0x46, %ymm1, %ymm0, %ymm9
vperm2i128 $0xf7, %ymm1, %ymm0, %ymm10
vperm2i128 $0x21, 64(%rsp), %ymm0, %ymm11
vperm2i128 $0x03, 64(%rsp), %ymm0, %ymm12
vperm2i128 $0x12, %ymm0, %ymm0, %ymm13

addq $0x100, %rsp
