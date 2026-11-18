#include "../../LeanQbe/T/Frontend/C0/c0.h"

typedef C0_RET2(u64, bool) u64_b;
typedef C0_RET3(u32, u32, u32) u32_t3;

u32 test_intrinsics(u32 x32, u64 x64, f64 d) {
  u32 r32 = c0_rotl32(x32, 7u) ^ c0_rotr32(x32, 5u);
  u32 c32 = c0_clz32(x32) + c0_ctz32(x32) + c0_popcnt32(x32);
  u64 r64 = c0_rotl64(x64, 13ULL) ^ c0_rotr64(x64, 9ULL);
  u64 c64 = c0_clz64(x64) + c0_ctz64(x64) + c0_popcnt64(x64);
  u64 s1 = 0ULL; bool co1 = false;
  C0_TIE2(s1, co1, c0_addc64(x64, 0xFFFFFFFFFFFFFF00ULL, (x32 & 1u) != 0u));
  u64 d1 = 0ULL; bool bo1 = false;
  C0_TIE2(d1, bo1, c0_subb64(x64, 100ULL, (x32 & 2u) != 0u));
  u64 lo = 0ULL; u64 hi = 0ULL;
  C0_TIE2(lo, hi, c0_umul128(x64, 0x100000003ULL));
  u64 fb = c0_f64_to_bits(d);
  f64 d2 = c0_bits_to_f64(fb);
  u64 sat = c0_f64_to_u64_sat(d2);
  u64 res = (u64)(r32 ^ c32) ^ r64 ^ c64 ^ s1 ^ d1 ^ lo ^ hi ^ fb ^ sat ^ (u64)co1 ^ (u64)bo1;
  return (u32)(res ^ (res >> 32));
}

u32_t3 test_switch_loops(u32 mode, u32 n) {
  u32 a = 0u;
  u32 b = 1u;
  u32 c = 0u;
  u32 i = 0u;
  do {
    switch (mode & 3u) {
      case 0:
        a = a + 10u;
        fallthrough;
      case 1:
        b = b + i;
        break;
      case 2:
        c = c + 3u;
        break;
      default:
        a = a + 1u;
        b = b + 2u;
        c = c + 3u;
        break;
    }
    i = i + 1u;
  } while (i < n);
  for (u32 k = 0u; k < n; k++) {
    if ((k & 1u) == 0u) continue;
    c = c + k;
  }
  return C0_TUP3(u32_t3, a, b, c);
}
