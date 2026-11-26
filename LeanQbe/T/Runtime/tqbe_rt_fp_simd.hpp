#pragma once

#include "tqbe_rt_core.hpp"

namespace tqbe {

// ============================================================================
// Bit counting / reversal (Lean OpCode clz, cls, rbit, ctz, popcnt take bits<N>)
// ============================================================================

template <size_t N>
constexpr bits<N> op_clz(bits<N> a) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    if (a.data == 0) return bits<N>(N);
    uint64_t shifted = a.data << (64 - N);
    return bits<N>(static_cast<uint64_t>(std::countl_zero(shifted)));
  } else {
    uint64_t cnt = 0;
    for (size_t i = N; i > 0; --i) {
      if (a.bit(i - 1)) break;
      ++cnt;
    }
    return bits<N>(cnt);
  }
}

template <size_t N>
constexpr bits<N> op_ctz(bits<N> a) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    if (a.data == 0) return bits<N>(N);
    return bits<N>(static_cast<uint64_t>(std::countr_zero(a.data)));
  } else {
    uint64_t cnt = 0;
    for (size_t i = 0; i < N; ++i) {
      if (a.bit(i)) break;
      ++cnt;
    }
    return bits<N>(cnt);
  }
}

template <size_t N>
constexpr bits<N> op_cls(bits<N> a) {
  if constexpr (N == 0) {
    return {};
  } else {
    bits<N> x = bv_sign_bit(a) ? bv_not(a) : a;
    return bv_sub(op_clz(x), bits<N>(1ULL));
  }
}

template <size_t N>
constexpr bits<N> op_rbit(bits<N> a) {
  if constexpr (N == 0) {
    return {};
  } else {
    bits<N> r{};
    for (size_t i = 0; i < N; ++i) {
      if (a.bit(i)) r.set_bit(N - 1 - i, true);
    }
    return r;
  }
}

template <size_t N>
constexpr bits<N> op_popcnt(bits<N> a) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(static_cast<uint64_t>(std::popcount(a.data)));
  } else {
    uint64_t cnt = 0;
    for (uint64_t w : a.data) cnt += static_cast<uint64_t>(std::popcount(w));
    return bits<N>(cnt);
  }
}

// ============================================================================
// Division, remainder, carry/borrow, widening multiply
// ============================================================================

template <size_t N>
constexpr pair<bits<N>, bits<N>> bv_udiv_rem(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return {{}, {}};
  } else if constexpr (N <= 64) {
    return {bits<N>(a.data / b.data), bits<N>(a.data % b.data)};
  } else {
    bits<N> q{};
    bits<N> rem{};
    for (size_t i = N; i > 0; --i) {
      bool carry = bv_sign_bit(rem);
      rem = bv_shl_amt(rem, 1);
      if (a.bit(i - 1)) rem.set_bit(0, true);
      if (carry || !bv_ult(rem, b)) {
        rem = bv_sub(rem, b);
        q.set_bit(i - 1, true);
      }
    }
    return {q, rem};
  }
}

template <size_t N>
inline bits<N> op_udiv(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    (void)a; (void)b; TQBE_UB("udiv bits<0>");
  } else {
    if (bv_is_zero(b)) TQBE_UB("udiv by zero");
    return bv_udiv_rem(a, b).first;
  }
}

template <size_t N>
inline bits<N> op_urem(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    (void)a; (void)b; TQBE_UB("urem bits<0>");
  } else {
    if (bv_is_zero(b)) TQBE_UB("urem by zero");
    return bv_udiv_rem(a, b).second;
  }
}

template <size_t N>
inline bits<N> op_udiv0(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    (void)a; (void)b; return {};
  } else {
    if (bv_is_zero(b)) return {};
    return bv_udiv_rem(a, b).first;
  }
}

template <size_t N>
inline bits<N> op_sdiv(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    (void)a; (void)b; TQBE_UB("sdiv bits<0>");
  } else {
    if (bv_is_zero(b)) TQBE_UB("sdiv by zero");
    if (a == bv_int_min<N>() && b == bv_all_ones<N>()) {
      TQBE_UB("sdiv signed overflow");
    }
    bool sa = bv_sign_bit(a), sb = bv_sign_bit(b);
    bits<N> q = bv_udiv_rem(sa ? bv_neg(a) : a, sb ? bv_neg(b) : b).first;
    return (sa != sb) ? bv_neg(q) : q;
  }
}

template <size_t N>
inline bits<N> op_srem(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    (void)a; (void)b; TQBE_UB("srem bits<0>");
  } else {
    if (bv_is_zero(b)) TQBE_UB("srem by zero");
    if (a == bv_int_min<N>() && b == bv_all_ones<N>()) {
      TQBE_UB("srem signed overflow");
    }
    bool sa = bv_sign_bit(a), sb = bv_sign_bit(b);
    bits<N> r = bv_udiv_rem(sa ? bv_neg(a) : a, sb ? bv_neg(b) : b).second;
    return sa ? bv_neg(r) : r;
  }
}

template <size_t N>
inline bits<N> op_sdiv0(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    (void)a; (void)b; return {};
  } else {
    if (bv_is_zero(b)) return {};
    bool sa = bv_sign_bit(a), sb = bv_sign_bit(b);
    bits<N> q = bv_udiv_rem(sa ? bv_neg(a) : a, sb ? bv_neg(b) : b).first;
    return (sa != sb) ? bv_neg(q) : q;
  }
}

template <size_t N>
inline pair<bits<N>, bool> op_addc(bits<N> a, bits<N> b, bool cin) {
  if constexpr (N == 0) {
    (void)a; (void)b;
    return {{}, cin};
  } else if constexpr (N < 64) {
    uint64_t sum = a.data + b.data + (cin ? 1ULL : 0ULL);
    return {bits<N>(sum), ((sum >> N) & 1ULL) != 0ULL};
  } else {
    bits<N + 1> s = bv_add(bv_add(op_zext<N, N + 1>(a), op_zext<N, N + 1>(b)),
                           bits<N + 1>(cin ? 1ULL : 0ULL));
    return {op_trunc<N + 1, N>(s), bv_sign_bit(s)};
  }
}

template <size_t N>
inline pair<bits<N>, bool> op_subb(bits<N> a, bits<N> b, bool bin) {
  if constexpr (N == 0) {
    (void)a; (void)b;
    return {{}, bin};
  } else {
    bits<N> d = bv_sub(bv_sub(a, b), bits<N>(bin ? 1ULL : 0ULL));
    bool borrow = bin ? !bv_ult(b, a) : bv_ult(a, b);
    return {d, borrow};
  }
}

template <size_t N>
inline pair<bits<N>, bits<N>> op_umulw(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    (void)a; (void)b;
    return {{}, {}};
  } else {
    bits<2 * N> p = bv_mul(op_zext<N, 2 * N>(a), op_zext<N, 2 * N>(b));
    return {op_trunc<2 * N, N>(p), op_trunc<2 * N, N>(bv_lshr_amt(p, N))};
  }
}

template <size_t N>
inline pair<bits<N>, bits<N>> op_smulw(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    (void)a; (void)b;
    return {{}, {}};
  } else {
    bits<2 * N> p = bv_mul(op_sext<N, 2 * N>(a), op_sext<N, 2 * N>(b));
    return {op_trunc<2 * N, N>(p), op_trunc<2 * N, N>(bv_lshr_amt(p, N))};
  }
}

// ============================================================================
// Floating-point conversions & IEEE-754 operations (h, s, d, q)
// ============================================================================

namespace detail {

inline float u32_to_f32(uint32_t u) { return std::bit_cast<float>(u); }
inline uint32_t f32_to_u32(float f) { return std::bit_cast<uint32_t>(f); }
inline double u64_to_f64(uint64_t u) { return std::bit_cast<double>(u); }
inline uint64_t f64_to_u64(double f) { return std::bit_cast<uint64_t>(f); }

inline float f16_bits_to_f32(uint16_t h) {
  uint32_t sign = (static_cast<uint32_t>(h) & 0x8000U) << 16;
  uint32_t exp = (static_cast<uint32_t>(h) >> 10) & 0x1FU;
  uint32_t mant = static_cast<uint32_t>(h) & 0x03FFU;
  uint32_t out = 0;
  if (exp == 0) {
    if (mant == 0) {
      out = sign;
    } else {
      int e = -14;
      while ((mant & 0x0400U) == 0) {
        mant <<= 1;
        --e;
      }
      mant &= 0x03FFU;
      out = sign | (static_cast<uint32_t>(e + 127) << 23) | (mant << 13);
    }
  } else if (exp == 0x1FU) {
    if (mant == 0) {
      out = sign | 0x7F800000U;
    } else {
      out = sign | 0x7FC00000U | (mant << 13);
    }
  } else {
    out = sign | ((exp + 112U) << 23) | (mant << 13);
  }
  return u32_to_f32(out);
}

inline uint16_t f32_to_f16_bits(float f) {
  uint32_t u = f32_to_u32(f);
  uint16_t sign = static_cast<uint16_t>((u >> 16) & 0x8000U);
  int exp = static_cast<int>((u >> 23) & 0xFFU) - 127;
  uint32_t mant = u & 0x7FFFFFU;
  if (((u >> 23) & 0xFFU) == 0xFFU) {
    if (mant == 0) return static_cast<uint16_t>(sign | 0x7C00U);
    uint16_t nm = static_cast<uint16_t>(mant >> 13);
    return static_cast<uint16_t>(sign | 0x7E00U | nm);
  }
  if (exp > 15) return static_cast<uint16_t>(sign | 0x7C00U);
  if (exp >= -14) {
    uint32_t rem = mant & 0x1FFFU;
    uint32_t m16 = mant >> 13;
    uint32_t e16 = static_cast<uint32_t>(exp + 15);
    if (rem > 0x1000U || (rem == 0x1000U && (m16 & 1U) != 0U)) {
      ++m16;
      if (m16 == 0x0400U) {
        m16 = 0;
        ++e16;
        if (e16 >= 0x1FU) return static_cast<uint16_t>(sign | 0x7C00U);
      }
    }
    return static_cast<uint16_t>(sign | (e16 << 10) | m16);
  }
  if (exp < -25) return sign;
  uint32_t sig = 0x800000U | mant;
  int shift = -(exp + 1);
  uint32_t m16 = sig >> shift;
  uint32_t rem = sig & ((1U << shift) - 1U);
  uint32_t half = 1U << (shift - 1);
  if (rem > half || (rem == half && (m16 & 1U) != 0U)) {
    ++m16;
  }
  return static_cast<uint16_t>(sign | m16);
}

inline uint16_t f64_to_f16_bits(double d) {
  // Collapse bits below float32 precision with sticky bit before calling f32_to_f16_bits.
  uint64_t u = f64_to_u64(d);
  uint64_t sign64 = u >> 63;
  uint64_t be64 = (u >> 52) & 0x7FFULL;
  uint64_t m64 = u & 0xFFFFFFFFFFFFFULL;
  if (be64 == 0x7FFULL) {
    if (m64 == 0) return static_cast<uint16_t>((sign64 << 15) | 0x7C00U);
    return static_cast<uint16_t>((sign64 << 15) | 0x7E00U | (m64 >> 42));
  }
  uint32_t s32 = static_cast<uint32_t>(sign64) << 31;
  if (be64 == 0 && m64 == 0) return static_cast<uint16_t>(s32 >> 16);
  int32_t exp = (be64 == 0) ? -1022 : (static_cast<int32_t>(be64) - 1023);
  if (be64 == 0) {
    while ((m64 & (1ULL << 52)) == 0) { m64 <<= 1; --exp; }
  } else {
    m64 |= (1ULL << 52);
  }
  if (exp > 15) return static_cast<uint16_t>((sign64 << 15) | 0x7C00U);
  if (exp < -25) return static_cast<uint16_t>(sign64 << 15);
  // All finite binary16 magnitudes fit cleanly inside normalized float32 with sticky preserved.
  uint64_t m24 = m64 >> 29;
  if ((m64 & ((1ULL << 29) - 1ULL)) != 0ULL) m24 |= 1ULL;
  uint32_t u32 = s32 | (static_cast<uint32_t>(exp + 127) << 23) |
                 static_cast<uint32_t>(m24 & 0x7FFFFFULL);
  return f32_to_f16_bits(u32_to_f32(u32));
}

#if (defined(__SIZEOF_FLOAT128__) || defined(__FLT128_MANT_DIG__)) && !defined(TQBE_NO_FLOAT128)
#define TQBE_HAS_FLOAT128 1
using f128_t = __float128;
#elif defined(__SIZEOF_LONG_DOUBLE__) && (__SIZEOF_LONG_DOUBLE__ == 16) && \
    defined(__LDBL_MANT_DIG__) && (__LDBL_MANT_DIG__ == 113) && !defined(TQBE_NO_FLOAT128)
#define TQBE_HAS_FLOAT128 1
using f128_t = long double;
#else
#define TQBE_HAS_FLOAT128 0
#endif

#if TQBE_HAS_FLOAT128
inline f128_t u128_bits_to_f128(bits<128> b) {
  f128_t out{};
  uint64_t words[2] = {b.data[0], b.data[1]};
  std::memcpy(&out, words, 16);
  return out;
}

inline bits<128> f128_to_u128_bits(f128_t f) {
  uint64_t words[2]{};
  std::memcpy(words, &f, 16);
  return bits<128>::from_array({words[0], words[1]});
}
#endif

inline bool f128_is_nan(bits<128> b) {
  uint64_t exp = (b.data[1] >> 48) & 0x7FFFULL;
  uint64_t mhi = b.data[1] & 0xFFFFFFFFFFFFULL;
  return exp == 0x7FFFULL && (mhi != 0 || b.data[0] != 0);
}

// Exact IEEE binary128 sqrt without -lquadmath via 228-bit integer sqrt.
inline bits<128> f128_sqrt_bits(bits<128> b) {
  bool sign = (b.data[1] >> 63) != 0;
  uint64_t exp = (b.data[1] >> 48) & 0x7FFFULL;
  uint64_t mhi = b.data[1] & 0xFFFFFFFFFFFFULL;
  uint64_t mlo = b.data[0];

  if (exp == 0x7FFFULL) {
    if (mhi != 0 || mlo != 0) {
      b.data[1] |= (1ULL << 47);
      return b;
    }
    if (sign) return bits<128>::from_words({0ULL, 0x7FFF800000000000ULL});
    return b;
  }
  if (exp == 0 && mhi == 0 && mlo == 0) {
    return b;
  }
  if (sign) {
    return bits<128>::from_words({0ULL, 0x7FFF800000000000ULL});
  }

  int32_t e = static_cast<int32_t>(exp) - 16383;
  bits<128> m = bits<128>::from_words({mlo, mhi});
  if (exp == 0) {
    e = -16382;
    while (!m.bit(112)) {
      m = bv_shl_amt(m, 1);
      --e;
    }
  } else {
    m.set_bit(112, true);
  }
  if ((e & 1) != 0) {
    m = bv_shl_amt(m, 1);
    --e;
  }
  int32_t out_e = (e / 2) + 16383;

  bits<256> rad = bv_shl_amt(op_zext<128, 256>(m), 114);
  bits<256> root{};
  bits<256> rem{};
  for (int pair_idx = 113; pair_idx >= 0; --pair_idx) {
    rem = bv_shl_amt(rem, 2);
    if (rad.bit(static_cast<size_t>(2 * pair_idx + 1))) rem.set_bit(1, true);
    if (rad.bit(static_cast<size_t>(2 * pair_idx))) rem.set_bit(0, true);
    bits<256> trial = bv_or(bv_shl_amt(root, 2), bits<256>(1ULL));
    root = bv_shl_amt(root, 1);
    if (!bv_ult(rem, trial)) {
      rem = bv_sub(rem, trial);
      root.set_bit(0, true);
    }
  }
  bool round_bit = root.bit(0);
  bool sticky = !bv_is_zero(rem);
  bits<128> sig = op_trunc<256, 128>(bv_lshr_amt(root, 1));
  bool lsb = sig.bit(0);
  if (round_bit && (sticky || lsb)) {
    sig = bv_add(sig, bits<128>(1ULL));
    if (sig.bit(113)) {
      sig = bv_lshr_amt(sig, 1);
      ++out_e;
    }
  }
  sig.set_bit(112, false);
  uint64_t hi = (static_cast<uint64_t>(out_e) << 48) | sig.data[1];
  return bits<128>::from_words({sig.data[0], hi});
}

template <Fmt F>
auto to_fp(fval<F> v) {
  if constexpr (F == Fmt::h) return f16_bits_to_f32(static_cast<uint16_t>(v.raw.data));
  else if constexpr (F == Fmt::s) return u32_to_f32(static_cast<uint32_t>(v.raw.data));
  else if constexpr (F == Fmt::d) return u64_to_f64(v.raw.data);
  else {
#if TQBE_HAS_FLOAT128
    return u128_bits_to_f128(v.raw);
#else
    (void)v;
    TQBE_UB("f128 operations require IEEE binary128 support");
    return 0.0;
#endif
  }
}

template <Fmt F, typename Fp>
fval<F> from_fp(Fp x) {
  if constexpr (F == Fmt::h) {
#if TQBE_HAS_FLOAT128
    if constexpr (std::is_same_v<Fp, f128_t>) {
      return fval<F>{bits<16>(f64_to_f16_bits(static_cast<double>(x)))};
    } else
#endif
    if constexpr (std::is_same_v<Fp, double>) {
      return fval<F>{bits<16>(f64_to_f16_bits(x))};
    } else {
      return fval<F>{bits<16>(f32_to_f16_bits(static_cast<float>(x)))};
    }
  } else if constexpr (F == Fmt::s) {
    return fval<F>{bits<32>(f32_to_u32(static_cast<float>(x)))};
  } else if constexpr (F == Fmt::d) {
    return fval<F>{bits<64>(f64_to_u64(static_cast<double>(x)))};
  } else {
#if TQBE_HAS_FLOAT128
    return fval<F>{f128_to_u128_bits(static_cast<f128_t>(x))};
#else
    (void)x;
    TQBE_UB("f128 operations require IEEE binary128 support");
    return fval<F>{};
#endif
  }
}

template <Fmt F>
bool fp_is_nan(fval<F> v) {
  if constexpr (F == Fmt::q) return f128_is_nan(v.raw);
  else return std::isnan(to_fp(v));
}

template <Fmt F>
struct fp_parts {
  bool sign = false;
  bool special = false;
  bool zero = false;
  bool inf = false;
  int32_t exp = 0;
  bits<128> sig{};
};

template <Fmt F>
inline fp_parts<F> unpack_fp_parts(fval<F> v) {
  fp_parts<F> p{};
  if constexpr (F == Fmt::q) {
    p.sign = (v.raw.data[1] >> 63) != 0;
    uint64_t be = (v.raw.data[1] >> 48) & 0x7FFFULL;
    uint64_t mhi = v.raw.data[1] & 0xFFFFFFFFFFFFULL;
    uint64_t mlo = v.raw.data[0];
    if (be == 0x7FFFULL) {
      p.special = true;
      p.inf = (mhi == 0 && mlo == 0);
      return p;
    }
    if (be == 0 && mhi == 0 && mlo == 0) { p.zero = true; return p; }
    p.sig = bits<128>::from_words({mlo, mhi});
    if (be == 0) {
      p.exp = -16382;
      while (!p.sig.bit(112)) { p.sig = bv_shl_amt(p.sig, 1); --p.exp; }
    } else {
      p.exp = static_cast<int32_t>(be) - 16383;
      p.sig.set_bit(112, true);
    }
    return p;
  } else {
    double d = static_cast<double>(to_fp(v));
    uint64_t u = f64_to_u64(d);
    p.sign = (u >> 63) != 0;
    uint64_t be = (u >> 52) & 0x7FFULL;
    uint64_t m = u & 0xFFFFFFFFFFFFFULL;
    if (be == 0x7FFULL) {
      p.special = true;
      p.inf = (m == 0);
      return p;
    }
    if (be == 0 && m == 0) { p.zero = true; return p; }
    if (be == 0) {
      p.exp = -1022;
      while ((m & (1ULL << 52)) == 0) { m <<= 1; --p.exp; }
    } else {
      p.exp = static_cast<int32_t>(be) - 1023;
      m |= (1ULL << 52);
    }
    p.sig = bv_shl_amt(bits<128>(m), 60);
    return p;
  }
}

// Single-round IEEE binary128 FMA without -lquadmath.
inline fval<Fmt::q> f128_fma(fval<Fmt::q> a, fval<Fmt::q> b, fval<Fmt::q> c) {
  auto pa = unpack_fp_parts(a);
  auto pb = unpack_fp_parts(b);
  auto pc = unpack_fp_parts(c);
  if (pa.special && !pa.inf) return a;
  if (pb.special && !pb.inf) return b;
  if (pc.special && !pc.inf) return c;
  bool p_sign = pa.sign ^ pb.sign;
  if ((pa.inf && pb.zero) || (pb.inf && pa.zero)) {
    return fval<Fmt::q>{bits<128>::from_words({0ULL, 0x7FFF800000000000ULL})};
  }
  if (pa.inf || pb.inf) {
    if (pc.inf && pc.sign != p_sign) {
      return fval<Fmt::q>{bits<128>::from_words({0ULL, 0x7FFF800000000000ULL})};
    }
    uint64_t hi_inf = p_sign ? 0xFFFF000000000000ULL : 0x7FFF000000000000ULL;
    return fval<Fmt::q>{bits<128>::from_words({0ULL, hi_inf})};
  }
  if (pc.inf) return c;
  if (pa.zero || pb.zero) {
    if (pc.zero) {
      bool zs = p_sign && pc.sign;
      return fval<Fmt::q>{bits<128>::from_words({0ULL, zs ? (1ULL << 63) : 0ULL})};
    }
    return c;
  }
  // Exact 113x113 product in bits<512> at exponent p_exp = pa.exp + pb.exp - 224.
  bits<512> prod = bv_mul(op_zext<128, 512>(pa.sig), op_zext<128, 512>(pb.sig));
  int32_t p_exp = pa.exp + pb.exp;
  // prod has top bit at bit 224 or 225.
  if (prod.bit(225)) ++p_exp;
  // Normalize product MSB to bit 224 in value = sig * 2^(p_exp - 224) if bit 225 wasn't set.
  bits<512> p_mant = prod.bit(225) ? prod : bv_shl_amt(prod, 1);
  // Now p_mant has MSB at bit 225 representing 1.xxx * 2^p_exp, i.e., LSB = 2^(p_exp - 225).
  if (pc.zero) {
    bits<512> s = bv_shl_amt(p_mant, 25); // align MSB to bit 250
    // Round to 113 bits (top bit 250 down to 138, round=137, sticky=0..136).
    bool round = s.bit(137);
    bool sticky = !bv_is_zero(op_trunc<512, 137>(s));
    bits<128> sig = op_trunc<512, 128>(bv_lshr_amt(s, 138));
    bool lsb = sig.bit(0);
    if (round && (sticky || lsb)) {
      sig = bv_add(sig, bits<128>(1ULL));
      if (sig.bit(113)) { sig = bv_lshr_amt(sig, 1); ++p_exp; }
    }
    int32_t be = p_exp + 16383;
    if (be >= 0x7FFF) {
      uint64_t hi_inf = p_sign ? 0xFFFF000000000000ULL : 0x7FFF000000000000ULL;
      return fval<Fmt::q>{bits<128>::from_words({0ULL, hi_inf})};
    }
    if (be <= 0) {
      int sh = 1 - be;
      if (sh >= 115) {
        return fval<Fmt::q>{bits<128>::from_words({0ULL, p_sign ? (1ULL << 63) : 0ULL})};
      }
      bits<128> sub = bv_lshr_amt(sig, static_cast<uint64_t>(sh));
      sub.set_bit(112, false);
      uint64_t sbit = p_sign ? (1ULL << 63) : 0ULL;
      return fval<Fmt::q>{bits<128>::from_words({sub.data[0], sbit | sub.data[1]})};
    }
    sig.set_bit(112, false);
    uint64_t hi = (p_sign ? (1ULL << 63) : 0ULL) |
                  (static_cast<uint64_t>(be) << 48) | sig.data[1];
    return fval<Fmt::q>{bits<128>::from_words({sig.data[0], hi})};
  }
  // Align c (pc.sig has MSB at bit 112 representing value * 2^pc.exp) and p_mant (MSB at bit 225)
  // in wide 512-bit space with headroom up to bit 490.
  int32_t top_exp = (p_exp > pc.exp) ? p_exp : pc.exp;
  int32_t shift_p = 480 - 225 - (top_exp - p_exp);
  int32_t shift_c = 480 - 112 - (top_exp - pc.exp);
  bits<512> vp{};
  bool p_sticky = false;
  if (shift_p >= 0) {
    vp = bv_shl_amt(p_mant, static_cast<uint64_t>(shift_p));
  } else {
    uint64_t rsh = static_cast<uint64_t>(-shift_p);
    if (rsh >= 512) { p_sticky = !bv_is_zero(p_mant); }
    else {
      bits<512> lost = bv_shl_amt(p_mant, 512 - rsh);
      p_sticky = !bv_is_zero(lost);
      vp = bv_lshr_amt(p_mant, rsh);
    }
  }
  bits<512> vc{};
  bool c_sticky = false;
  bits<512> cm = op_zext<128, 512>(pc.sig);
  if (shift_c >= 0) {
    vc = bv_shl_amt(cm, static_cast<uint64_t>(shift_c));
  } else {
    uint64_t rsh = static_cast<uint64_t>(-shift_c);
    if (rsh >= 512) { c_sticky = !bv_is_zero(cm); }
    else {
      bits<512> lost = bv_shl_amt(cm, 512 - rsh);
      c_sticky = !bv_is_zero(lost);
      vc = bv_lshr_amt(cm, rsh);
    }
  }
  // Add/sub with sticky preservation at bit 0.
  if (p_sticky) vp.set_bit(0, true);
  if (c_sticky) vc.set_bit(0, true);
  bool res_sign = p_sign;
  bits<512> sum{};
  if (p_sign == pc.sign) {
    sum = bv_add(vp, vc);
  } else if (!bv_ult(vp, vc)) {
    sum = bv_sub(vp, vc);
    res_sign = p_sign;
  } else {
    sum = bv_sub(vc, vp);
    res_sign = pc.sign;
  }
  if (bv_is_zero(sum)) {
    return fval<Fmt::q>{bits<128>{}}; // IEEE +0.0 for exact cancellation under RNE
  }
  // Find MSB of sum (value = sum * 2^(top_exp - 480))
  int32_t msb = 511;
  while (msb > 0 && !sum.bit(static_cast<size_t>(msb))) --msb;
  int32_t res_exp = top_exp + (msb - 480);
  int32_t be = res_exp + 16383;
  if (be >= 0x7FFF) {
    uint64_t hi_inf = res_sign ? 0xFFFF000000000000ULL : 0x7FFF000000000000ULL;
    return fval<Fmt::q>{bits<128>::from_words({0ULL, hi_inf})};
  }
  int32_t shift_needed = msb - 112;
  if (be <= 0) {
    shift_needed += (1 - be);
    be = 0;
  }
  bits<128> sig{};
  bool round_bit = false;
  bool sticky = false;
  if (shift_needed <= 0) {
    sig = bv_shl_amt(op_trunc<512, 128>(sum), static_cast<uint64_t>(-shift_needed));
  } else if (shift_needed >= 512) {
    sticky = !bv_is_zero(sum);
  } else {
    round_bit = sum.bit(static_cast<size_t>(shift_needed - 1));
    if (shift_needed > 1) {
      bits<512> one_sh = bv_shl_amt(bits<512>(1ULL),
                                    static_cast<uint64_t>(shift_needed - 1));
      bits<512> mask_rem = bv_sub(one_sh, bits<512>(1ULL));
      sticky = !bv_is_zero(bv_and(sum, mask_rem));
    }
    sig = op_trunc<512, 128>(bv_lshr_amt(sum, static_cast<uint64_t>(shift_needed)));
  }
  bool lsb = sig.bit(0);
  if (round_bit && (sticky || lsb)) {
    sig = bv_add(sig, bits<128>(1ULL));
    if (be == 0 && sig.bit(112)) {
      be = 1;
    } else if (sig.bit(113)) {
      sig = bv_lshr_amt(sig, 1);
      ++be;
      if (be >= 0x7FFF) {
        uint64_t hi_inf = res_sign ? 0xFFFF000000000000ULL : 0x7FFF000000000000ULL;
        return fval<Fmt::q>{bits<128>::from_words({0ULL, hi_inf})};
      }
    }
  }
  sig.set_bit(112, false);
  uint64_t hi = (res_sign ? (1ULL << 63) : 0ULL) |
                (static_cast<uint64_t>(be) << 48) | sig.data[1];
  return fval<Fmt::q>{bits<128>::from_words({sig.data[0], hi})};
}

} // namespace detail

template <typename T>
inline T op_fadd(const T& a, const T& b) {
  if constexpr (!is_float_tree<T>()) { (void)a; (void)b; TQBE_UB("fadd nonfloat"); }
  else if constexpr (std::is_same_v<T, fval<Fmt::h>>) {
    return detail::from_fp<Fmt::h>(static_cast<double>(detail::to_fp(a)) +
                                   static_cast<double>(detail::to_fp(b)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::s>>) {
    return detail::from_fp<Fmt::s>(detail::to_fp(a) + detail::to_fp(b));
  } else if constexpr (std::is_same_v<T, fval<Fmt::d>>) {
    return detail::from_fp<Fmt::d>(detail::to_fp(a) + detail::to_fp(b));
  } else if constexpr (std::is_same_v<T, fval<Fmt::q>>) {
    return detail::from_fp<Fmt::q>(detail::to_fp(a) + detail::to_fp(b));
  } else {
    return T{op_fadd(a.first, b.first), op_fadd(a.second, b.second)};
  }
}

template <typename T>
inline T op_fsub(const T& a, const T& b) {
  if constexpr (!is_float_tree<T>()) { (void)a; (void)b; TQBE_UB("fsub nonfloat"); }
  else if constexpr (std::is_same_v<T, fval<Fmt::h>>) {
    return detail::from_fp<Fmt::h>(static_cast<double>(detail::to_fp(a)) -
                                   static_cast<double>(detail::to_fp(b)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::s>>) {
    return detail::from_fp<Fmt::s>(detail::to_fp(a) - detail::to_fp(b));
  } else if constexpr (std::is_same_v<T, fval<Fmt::d>>) {
    return detail::from_fp<Fmt::d>(detail::to_fp(a) - detail::to_fp(b));
  } else if constexpr (std::is_same_v<T, fval<Fmt::q>>) {
    return detail::from_fp<Fmt::q>(detail::to_fp(a) - detail::to_fp(b));
  } else {
    return T{op_fsub(a.first, b.first), op_fsub(a.second, b.second)};
  }
}

template <typename T>
inline T op_fmul(const T& a, const T& b) {
  if constexpr (!is_float_tree<T>()) { (void)a; (void)b; TQBE_UB("fmul nonfloat"); }
  else if constexpr (std::is_same_v<T, fval<Fmt::h>>) {
    return detail::from_fp<Fmt::h>(static_cast<double>(detail::to_fp(a)) *
                                   static_cast<double>(detail::to_fp(b)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::s>>) {
    return detail::from_fp<Fmt::s>(detail::to_fp(a) * detail::to_fp(b));
  } else if constexpr (std::is_same_v<T, fval<Fmt::d>>) {
    return detail::from_fp<Fmt::d>(detail::to_fp(a) * detail::to_fp(b));
  } else if constexpr (std::is_same_v<T, fval<Fmt::q>>) {
    return detail::from_fp<Fmt::q>(detail::to_fp(a) * detail::to_fp(b));
  } else {
    return T{op_fmul(a.first, b.first), op_fmul(a.second, b.second)};
  }
}

template <typename T>
inline T op_fdiv(const T& a, const T& b) {
  if constexpr (!is_float_tree<T>()) { (void)a; (void)b; TQBE_UB("fdiv nonfloat"); }
  else if constexpr (std::is_same_v<T, fval<Fmt::h>>) {
    return detail::from_fp<Fmt::h>(static_cast<double>(detail::to_fp(a)) /
                                   static_cast<double>(detail::to_fp(b)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::s>>) {
    return detail::from_fp<Fmt::s>(detail::to_fp(a) / detail::to_fp(b));
  } else if constexpr (std::is_same_v<T, fval<Fmt::d>>) {
    return detail::from_fp<Fmt::d>(detail::to_fp(a) / detail::to_fp(b));
  } else if constexpr (std::is_same_v<T, fval<Fmt::q>>) {
    return detail::from_fp<Fmt::q>(detail::to_fp(a) / detail::to_fp(b));
  } else {
    return T{op_fdiv(a.first, b.first), op_fdiv(a.second, b.second)};
  }
}

template <typename T>
inline T op_ffma(const T& a, const T& b, const T& c) {
  if constexpr (!is_float_tree<T>()) { (void)a; (void)b; (void)c; TQBE_UB("ffma nonfloat"); }
  else if constexpr (std::is_same_v<T, fval<Fmt::h>>) {
    double pa = static_cast<double>(detail::to_fp(a));
    double pb = static_cast<double>(detail::to_fp(b));
    double pc = static_cast<double>(detail::to_fp(c));
    return detail::from_fp<Fmt::h>((pa * pb) + pc);
  } else if constexpr (std::is_same_v<T, fval<Fmt::s>>) {
    return detail::from_fp<Fmt::s>(std::fmaf(detail::to_fp(a), detail::to_fp(b), detail::to_fp(c)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::d>>) {
    return detail::from_fp<Fmt::d>(std::fma(detail::to_fp(a), detail::to_fp(b), detail::to_fp(c)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::q>>) {
    return detail::f128_fma(a, b, c);
  } else {
    return T{op_ffma(a.first, b.first, c.first), op_ffma(a.second, b.second, c.second)};
  }
}

template <typename T>
inline T op_fneg(const T& a) {
  if constexpr (!is_float_tree<T>()) { (void)a; TQBE_UB("fneg nonfloat"); }
  else if constexpr (ty_traits<T>::is_fval) {
    bits<T::width> r = a.raw;
    r.set_bit(T::width - 1, !r.bit(T::width - 1));
    return T{r};
  } else {
    return T{op_fneg(a.first), op_fneg(a.second)};
  }
}

template <typename T>
inline T op_fabs(const T& a) {
  if constexpr (!is_float_tree<T>()) { (void)a; TQBE_UB("fabs nonfloat"); }
  else if constexpr (ty_traits<T>::is_fval) {
    bits<T::width> r = a.raw;
    r.set_bit(T::width - 1, false);
    return T{r};
  } else {
    return T{op_fabs(a.first), op_fabs(a.second)};
  }
}

template <typename T>
inline T op_fsqrt(const T& a) {
  if constexpr (!is_float_tree<T>()) { (void)a; TQBE_UB("fsqrt nonfloat"); }
  else if constexpr (std::is_same_v<T, fval<Fmt::h>>) {
    return detail::from_fp<Fmt::h>(std::sqrt(detail::to_fp(a)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::s>>) {
    return detail::from_fp<Fmt::s>(std::sqrtf(detail::to_fp(a)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::d>>) {
    return detail::from_fp<Fmt::d>(std::sqrt(detail::to_fp(a)));
  } else if constexpr (std::is_same_v<T, fval<Fmt::q>>) {
    return fval<Fmt::q>{detail::f128_sqrt_bits(a.raw)};
  } else {
    return T{op_fsqrt(a.first), op_fsqrt(a.second)};
  }
}

template <FCmpOp Op, typename T>
inline mask_t<T> op_fcmp(const T& a, const T& b) {
  if constexpr (!is_float_tree<T>()) {
    (void)a; (void)b;
    TQBE_UB("fcmp nonfloat");
  } else if constexpr (ty_traits<T>::is_fval) {
    bool nan_either = detail::fp_is_nan(a) || detail::fp_is_nan(b);
    auto xa = detail::to_fp(a), xb = detail::to_fp(b);
    if constexpr (Op == FCmpOp::ord) return !nan_either;
    else if constexpr (Op == FCmpOp::uno) return nan_either;
    else if constexpr (Op == FCmpOp::ne) return nan_either || (xa != xb);
    else if constexpr (Op == FCmpOp::eq) return !nan_either && (xa == xb);
    else if constexpr (Op == FCmpOp::lt) return !nan_either && (xa < xb);
    else if constexpr (Op == FCmpOp::le) return !nan_either && (xa <= xb);
    else if constexpr (Op == FCmpOp::gt) return !nan_either && (xa > xb);
    else return !nan_either && (xa >= xb);
  } else {
    return mask_t<T>{op_fcmp<Op>(a.first, b.first), op_fcmp<Op>(a.second, b.second)};
  }
}

template <Fmt Src, Fmt Dst>
inline fval<Dst> op_fcvt(fval<Src> a) {
  if constexpr (Src == Dst) {
    return a;
  } else if constexpr (Src == Fmt::q) {
#if TQBE_HAS_FLOAT128
    detail::f128_t x = detail::to_fp(a);
    if constexpr (Dst == Fmt::d) return detail::from_fp<Fmt::d>(static_cast<double>(x));
    else if constexpr (Dst == Fmt::s) return detail::from_fp<Fmt::s>(static_cast<float>(x));
    else return detail::from_fp<Fmt::h>(x);
#else
    (void)a;
    TQBE_UB("f128 operations require IEEE binary128 support");
    return fval<Dst>{};
#endif
  } else if constexpr (Dst == Fmt::q) {
#if TQBE_HAS_FLOAT128
    return detail::from_fp<Fmt::q>(static_cast<detail::f128_t>(detail::to_fp(a)));
#else
    (void)a;
    TQBE_UB("f128 operations require IEEE binary128 support");
    return fval<Dst>{};
#endif
  } else if constexpr (Src == Fmt::h && Dst == Fmt::d) {
    return detail::from_fp<Fmt::d>(static_cast<double>(detail::to_fp(a)));
  } else if constexpr (Src == Fmt::d && Dst == Fmt::h) {
    return detail::from_fp<Fmt::h>(detail::to_fp(a));
  } else {
    return detail::from_fp<Dst>(detail::to_fp(a));
  }
}

template <size_t N, Fmt F>
inline fval<F> op_uitofp(bits<N> a) {
  if constexpr (N == 0) {
    return detail::from_fp<F>(0.0);
  } else if constexpr (N <= 64) {
    if constexpr (F == Fmt::q) {
#if TQBE_HAS_FLOAT128
      return detail::from_fp<Fmt::q>(static_cast<detail::f128_t>(a.data));
#else
      (void)a;
      TQBE_UB("f128 operations require IEEE binary128 support");
      return fval<F>{};
#endif
    } else if constexpr (F == Fmt::d) {
      return detail::from_fp<Fmt::d>(static_cast<double>(a.data));
    } else if constexpr (F == Fmt::s) {
      return detail::from_fp<Fmt::s>(static_cast<float>(a.data));
    } else {
      return detail::from_fp<Fmt::h>(static_cast<double>(a.data));
    }
  } else {
#if TQBE_HAS_FLOAT128
    detail::f128_t acc = static_cast<detail::f128_t>(0.0);
    detail::f128_t scale = static_cast<detail::f128_t>(1.0);
    const detail::f128_t step = static_cast<detail::f128_t>(18446744073709551616.0);
    for (size_t i = 0; i < bits<N>::words; ++i) {
      acc += static_cast<detail::f128_t>(a.data[i]) * scale;
      scale *= step;
    }
    if constexpr (F == Fmt::q) return detail::from_fp<Fmt::q>(acc);
    else if constexpr (F == Fmt::d) return detail::from_fp<Fmt::d>(static_cast<double>(acc));
    else if constexpr (F == Fmt::s) return detail::from_fp<Fmt::s>(static_cast<float>(acc));
    else return detail::from_fp<Fmt::h>(acc);
#else
    (void)a;
    TQBE_UB("wide uitofp requires IEEE binary128 support");
    return fval<F>{};
#endif
  }
}

template <size_t N, Fmt F>
inline fval<F> op_sitofp(bits<N> a) {
  if constexpr (N == 0) {
    return detail::from_fp<F>(0.0);
  } else {
    bool neg = bv_sign_bit(a);
    bits<N> mag = neg ? bv_neg(a) : a;
    fval<F> res = op_uitofp<N, F>(mag);
    return neg ? op_fneg(res) : res;
  }
}

namespace detail {

template <size_t N>
inline bits<N> shift_sig_to_uint(bits<128> sig, int32_t exp) {
  if (exp < 0) return {};
  uint32_t shift_left = static_cast<uint32_t>(exp);
  if (shift_left >= 112) {
    return bv_shl_amt(op_zext<128, N>(sig), shift_left - 112);
  } else {
    return op_trunc<128, N>(bv_lshr_amt(sig, 112U - shift_left));
  }
}

} // namespace detail

template <Fmt F, size_t N>
inline bits<N> op_fptoui(fval<F> a) {
  auto p = detail::unpack_fp_parts(a);
  if (p.special) TQBE_UB("fptoui NaN or Inf");
  if (p.zero) return {};
  if constexpr (N == 0) {
    if (p.exp >= 0) TQBE_UB("fptoui overflow bits<0>");
    return {};
  } else {
    if (p.sign) {
      if (p.exp >= 0) TQBE_UB("fptoui negative");
      return {};
    }
    if (p.exp < 0) return {};
    if (static_cast<size_t>(p.exp) >= N) TQBE_UB("fptoui overflow");
    if constexpr (N <= 128) {
      if (p.exp >= 112) {
        return op_trunc<128, N>(bv_shl_amt(p.sig, static_cast<uint64_t>(p.exp - 112)));
      } else {
        return op_trunc<128, N>(bv_lshr_amt(p.sig, static_cast<uint64_t>(112 - p.exp)));
      }
    } else {
      return detail::shift_sig_to_uint<N>(p.sig, p.exp);
    }
  }
}

template <Fmt F, size_t N>
inline bits<N> op_fptosi(fval<F> a) {
  auto p = detail::unpack_fp_parts(a);
  if (p.special) TQBE_UB("fptosi NaN or Inf");
  if constexpr (N == 0) {
    (void)a;
    TQBE_UB("fptosi overflow bits<0>");
  } else {
    if (p.zero || p.exp < 0) return {};
    if (!p.sign) {
      if (static_cast<size_t>(p.exp) >= N - 1) TQBE_UB("fptosi positive overflow");
    } else {
      if (static_cast<size_t>(p.exp) > N - 1) TQBE_UB("fptosi negative overflow");
      if (static_cast<size_t>(p.exp) == N - 1) {
        bits<128> min_sig{};
        min_sig.set_bit(112, true);
        if (p.sig != min_sig) TQBE_UB("fptosi negative overflow");
        return bv_int_min<N>();
      }
    }
    bits<N> mag{};
    if constexpr (N <= 128) {
      if (p.exp >= 112) {
        mag = op_trunc<128, N>(bv_shl_amt(p.sig, static_cast<uint64_t>(p.exp - 112)));
      } else {
        mag = op_trunc<128, N>(bv_lshr_amt(p.sig, static_cast<uint64_t>(112 - p.exp)));
      }
    } else {
      mag = detail::shift_sig_to_uint<N>(p.sig, p.exp);
    }
    return p.sign ? bv_neg(mag) : mag;
  }
}

// ============================================================================
// SIMD shuffle / align / blendw / SHA-256 operations
// ============================================================================

template <typename T>
inline T op_shufd(const T& a, uint8_t imm) {
  constexpr size_t N = bit_size<T>();
  if constexpr (N == 0 || N % 128 != 0) {
    (void)a; (void)imm;
    TQBE_UB("shufd invalid bit width");
  } else {
    bits<N> src = pack_bits(a);
    bits<N> dst{};
    constexpr size_t lanes128 = N / 128;
    for (size_t l = 0; l < lanes128; ++l) {
      for (size_t i = 0; i < 4; ++i) {
        size_t sel = (imm >> (2 * i)) & 3U;
        uint64_t dw = (src.word(l * 2 + sel / 2) >> ((sel % 2) * 32)) & 0xFFFFFFFFULL;
        size_t dst_word = l * 2 + i / 2;
        dst.data[dst_word] |= (dw << ((i % 2) * 32));
      }
    }
    dst.normalize();
    return unpack_bits<T>(dst);
  }
}

template <typename T>
inline T op_shufb(const T& a, const T& idx) {
  constexpr size_t N = bit_size<T>();
  if constexpr (N == 0 || N % 128 != 0) {
    (void)a; (void)idx;
    TQBE_UB("shufb invalid bit width");
  } else {
    bits<N> src = pack_bits(a);
    bits<N> ctrl = pack_bits(idx);
    bits<N> dst{};
    constexpr size_t lanes128 = N / 128;
    for (size_t l = 0; l < lanes128; ++l) {
      for (size_t i = 0; i < 16; ++i) {
        size_t cb_idx = l * 16 + i;
        uint8_t c = static_cast<uint8_t>((ctrl.word(cb_idx / 8) >> ((cb_idx % 8) * 8)) & 0xFFU);
        uint8_t out_b = 0;
        if ((c & 0x80U) == 0) {
          size_t sb_idx = l * 16 + (c & 0x0FU);
          out_b = static_cast<uint8_t>((src.word(sb_idx / 8) >> ((sb_idx % 8) * 8)) & 0xFFU);
        }
        dst.data[cb_idx / 8] |= (static_cast<uint64_t>(out_b) << ((cb_idx % 8) * 8));
      }
    }
    return unpack_bits<T>(dst);
  }
}

template <typename T>
inline T op_alignr(const T& hi_v, const T& lo_v, uint8_t imm) {
  constexpr size_t N = bit_size<T>();
  if constexpr (N == 0 || N % 128 != 0) {
    (void)hi_v; (void)lo_v; (void)imm;
    TQBE_UB("alignr invalid bit width");
  } else {
    bits<N> hi = pack_bits(hi_v);
    bits<N> lo = pack_bits(lo_v);
    bits<N> dst{};
    constexpr size_t lanes128 = N / 128;
    for (size_t l = 0; l < lanes128; ++l) {
      for (size_t i = 0; i < 16; ++i) {
        size_t k = static_cast<size_t>(imm) + i;
        uint8_t out_b = 0;
        if (k < 16) {
          size_t idx = l * 16 + k;
          out_b = static_cast<uint8_t>((lo.word(idx / 8) >> ((idx % 8) * 8)) & 0xFFU);
        } else if (k < 32) {
          size_t idx = l * 16 + (k - 16);
          out_b = static_cast<uint8_t>((hi.word(idx / 8) >> ((idx % 8) * 8)) & 0xFFU);
        }
        size_t dst_b = l * 16 + i;
        dst.data[dst_b / 8] |= (static_cast<uint64_t>(out_b) << ((dst_b % 8) * 8));
      }
    }
    return unpack_bits<T>(dst);
  }
}

template <typename T>
inline T op_blendw(const T& a, const T& b, uint8_t imm) {
  constexpr size_t N = bit_size<T>();
  if constexpr (N == 0 || N % 128 != 0) {
    (void)a; (void)b; (void)imm;
    TQBE_UB("blendw invalid bit width");
  } else {
    bits<N> pa = pack_bits(a);
    bits<N> pb = pack_bits(b);
    bits<N> dst{};
    constexpr size_t lanes128 = N / 128;
    for (size_t l = 0; l < lanes128; ++l) {
      for (size_t i = 0; i < 8; ++i) {
        bool pick_b = ((imm >> i) & 1U) != 0;
        const bits<N>& src = pick_b ? pb : pa;
        size_t w16_idx = l * 8 + i;
        uint64_t val16 = (src.word(w16_idx / 4) >> ((w16_idx % 4) * 16)) & 0xFFFFULL;
        dst.data[w16_idx / 4] |= (val16 << ((w16_idx % 4) * 16));
      }
    }
    return unpack_bits<T>(dst);
  }
}

namespace detail {

constexpr uint32_t rotr32(uint32_t x, unsigned n) {
  n &= 31U;
  return (n == 0) ? x : ((x >> n) | (x << (32U - n)));
}

constexpr uint32_t sha256_ch(uint32_t x, uint32_t y, uint32_t z) {
  return (x & y) ^ ((~x) & z);
}

constexpr uint32_t sha256_maj(uint32_t x, uint32_t y, uint32_t z) {
  return (x & y) ^ (x & z) ^ (y & z);
}

constexpr uint32_t sha256_S0(uint32_t x) {
  return rotr32(x, 2) ^ rotr32(x, 13) ^ rotr32(x, 22);
}

constexpr uint32_t sha256_S1(uint32_t x) {
  return rotr32(x, 6) ^ rotr32(x, 11) ^ rotr32(x, 25);
}

constexpr uint32_t sha256_s0(uint32_t x) {
  return rotr32(x, 7) ^ rotr32(x, 18) ^ (x >> 3);
}

constexpr uint32_t sha256_s1(uint32_t x) {
  return rotr32(x, 17) ^ rotr32(x, 19) ^ (x >> 10);
}

inline uint32_t get_lane32(const v4i32& v, size_t idx) {
  switch (idx) {
    case 0: return static_cast<uint32_t>(v.first.first.data);
    case 1: return static_cast<uint32_t>(v.first.second.data);
    case 2: return static_cast<uint32_t>(v.second.first.data);
    default: return static_cast<uint32_t>(v.second.second.data);
  }
}

inline v4i32 make_v4i32(uint32_t d0, uint32_t d1, uint32_t d2, uint32_t d3) {
  return {{bits<32>(d0), bits<32>(d1)}, {bits<32>(d2), bits<32>(d3)}};
}

} // namespace detail

inline v4i32 op_sha256rnds2(const v4i32& cdgh, const v4i32& abef, const v4i32& wk) {
  uint32_t A0 = detail::get_lane32(abef, 3);
  uint32_t B0 = detail::get_lane32(abef, 2);
  uint32_t E0 = detail::get_lane32(abef, 1);
  uint32_t F0 = detail::get_lane32(abef, 0);
  uint32_t C0 = detail::get_lane32(cdgh, 3);
  uint32_t D0 = detail::get_lane32(cdgh, 2);
  uint32_t G0 = detail::get_lane32(cdgh, 1);
  uint32_t H0 = detail::get_lane32(cdgh, 0);
  uint32_t WK0 = detail::get_lane32(wk, 0);
  uint32_t WK1 = detail::get_lane32(wk, 1);

  uint32_t T1 = detail::sha256_ch(E0, F0, G0) + detail::sha256_S1(E0) + WK0 + H0;
  uint32_t A1 = T1 + detail::sha256_maj(A0, B0, C0) + detail::sha256_S0(A0);
  uint32_t E1 = T1 + D0;
  uint32_t T2 = detail::sha256_ch(E1, E0, F0) + detail::sha256_S1(E1) + WK1 + G0;
  uint32_t A2 = T2 + detail::sha256_maj(A1, A0, B0) + detail::sha256_S0(A1);
  uint32_t E2 = T2 + C0;
  return detail::make_v4i32(E1, E2, A1, A2);
}

inline v4i32 op_sha256msg1(const v4i32& w0123, const v4i32& w4) {
  uint32_t W[5] = {
      detail::get_lane32(w0123, 0), detail::get_lane32(w0123, 1),
      detail::get_lane32(w0123, 2), detail::get_lane32(w0123, 3),
      detail::get_lane32(w4, 0)};
  return detail::make_v4i32(
      W[0] + detail::sha256_s0(W[1]),
      W[1] + detail::sha256_s0(W[2]),
      W[2] + detail::sha256_s0(W[3]),
      W[3] + detail::sha256_s0(W[4]));
}

inline v4i32 op_sha256msg2(const v4i32& sums, const v4i32& w) {
  uint32_t s0 = detail::get_lane32(sums, 0);
  uint32_t s1 = detail::get_lane32(sums, 1);
  uint32_t s2 = detail::get_lane32(sums, 2);
  uint32_t s3 = detail::get_lane32(sums, 3);
  uint32_t w2 = detail::get_lane32(w, 2);
  uint32_t w3 = detail::get_lane32(w, 3);
  uint32_t W16 = s0 + detail::sha256_s1(w2);
  uint32_t W17 = s1 + detail::sha256_s1(w3);
  uint32_t W18 = s2 + detail::sha256_s1(W16);
  uint32_t W19 = s3 + detail::sha256_s1(W17);
  return detail::make_v4i32(W16, W17, W18, W19);
}

// ============================================================================
// External exit signaling
// ============================================================================

struct ExitException {
  std::string target;
  std::vector<std::vector<uint8_t>> args;
};

template <typename T>
inline std::vector<uint8_t> encode_exit_arg(const T& v) {
  constexpr size_t N = bit_size<T>();
  constexpr size_t B = byte_size<T>();
  std::vector<uint8_t> bytes(B, 0);
  if constexpr (N > 0) {
    bits<N> pk = pack_bits(v);
    for (size_t i = 0; i < B; ++i) {
      bytes[i] = static_cast<uint8_t>((pk.word(i / 8) >> ((i % 8) * 8)) & 0xFFULL);
    }
  }
  return bytes;
}

template <typename T>
inline T decode_exit_arg(const std::vector<uint8_t>& bytes) {
  constexpr size_t N = bit_size<T>();
  constexpr size_t B = byte_size<T>();
  if constexpr (N == 0) {
    return unpack_bits<T>(bits<0>{});
  } else {
    bits<N> pk{};
    for (size_t i = 0; i < B && i < bytes.size(); ++i) {
      uint64_t b = static_cast<uint64_t>(bytes[i]);
      if constexpr (N <= 64) {
        pk.data |= (b << ((i % 8) * 8));
      } else {
        pk.data[i / 8] |= (b << ((i % 8) * 8));
      }
    }
    pk.normalize();
    return unpack_bits<T>(pk);
  }
}

template <typename... Args>
[[noreturn]] inline void exit_call(const char* name, const Args&... args) {
  ExitException ex;
  ex.target = name ? name : "";
  (ex.args.push_back(encode_exit_arg(args)), ...);
  throw std::move(ex);
}

} // namespace tqbe
