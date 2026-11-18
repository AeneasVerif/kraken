#ifndef TQBE_CATCH_UB
#error "test_catch_ub.cpp must be compiled with -DTQBE_CATCH_UB"
#endif

#include "gen_suite.hpp"

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <vector>

using tqbe::CmpOp;
using tqbe::ExitException;
using tqbe::FCmpOp;
using tqbe::Fmt;
using tqbe::Mem;
using tqbe::UbException;
using tqbe::bits;
using tqbe::fval;
using tqbe::op_cmp;
using tqbe::pair;
using tqbe::v4i32;

// Compile-time checks on critical edge cases in tqbe_rt.hpp
static_assert(tqbe::bool_cmp<CmpOp::slt>(true, false) == true,
              "bool signed compare: slt(true, false) must be true");
static_assert(tqbe::bool_cmp<CmpOp::sle>(true, false) == true);
static_assert(tqbe::bool_cmp<CmpOp::sgt>(false, true) == true);
static_assert(tqbe::bool_cmp<CmpOp::sge>(false, true) == true);
static_assert(tqbe::bool_cmp<CmpOp::slt>(false, true) == false);
static_assert(tqbe::bool_cmp<CmpOp::ult>(true, false) == false);
static_assert(tqbe::bit_size<pair<bool, bits<8>>>() == 9);
static_assert(tqbe::byte_size<pair<bool, bits<8>>>() == 2);
static_assert(tqbe::bit_size<pair<bool, bool>>() == 2);
static_assert(tqbe::byte_size<pair<bool, bool>>() == 1);
static_assert(tqbe::bswap_ok<bits<32>>() == true);
static_assert(tqbe::bswap_ok<pair<bits<16>, bits<16>>>() == true);
static_assert(tqbe::bswap_ok<pair<bits<4>, bits<4>>>() == false);
static_assert(tqbe::bswap_ok<bool>() == false);

#define ASSERT_EQ(a, b)                                                       \
  do {                                                                        \
    auto _va = (a);                                                           \
    auto _vb = (b);                                                           \
    if (!(_va == _vb)) {                                                      \
      std::fprintf(stderr, "ASSERT_EQ failed at line %d\n", __LINE__);        \
      std::abort();                                                           \
    }                                                                         \
  } while (0)

#define ASSERT_TRUE(cond)                                                     \
  do {                                                                        \
    if (!(cond)) {                                                            \
      std::fprintf(stderr, "ASSERT_TRUE failed at line %d: %s\n", __LINE__,   \
                   #cond);                                                    \
      std::abort();                                                           \
    }                                                                         \
  } while (0)

#define ASSERT_THROWS_UB(expr)                                                \
  do {                                                                        \
    bool _caught = false;                                                     \
    try {                                                                     \
      (void)(expr);                                                           \
    } catch (const UbException&) {                                            \
      _caught = true;                                                         \
    }                                                                         \
    if (!_caught) {                                                           \
      std::fprintf(stderr, "ASSERT_THROWS_UB failed at line %d: %s\n",        \
                   __LINE__, #expr);                                          \
      std::abort();                                                           \
    }                                                                         \
  } while (0)

namespace {

// Reference Union-Find model in C++ for differential testing
struct RefUF {
  std::vector<uint64_t> parent;
  explicit RefUF(size_t n) : parent(n) {
    for (size_t i = 0; i < n; ++i) parent[i] = i;
  }
  uint64_t find(uint64_t x) {
    while (parent[x] != x) {
      parent[x] = parent[parent[x]];
      x = parent[x];
    }
    return x;
  }
  void unite(uint64_t x, uint64_t y) {
    uint64_t rx = find(x), ry = find(y);
    if (rx != ry) parent[rx] = ry;
  }
};

template <auto FnFind, auto FnUnion, auto FnUnionInline>
void test_uf_target(const char* name) {
  (void)name;
  constexpr uint64_t BASE = 0x10000ULL;
  constexpr size_t N = 64;

  auto init_mem = [&](Mem& m) {
    m.alloc(BASE, N * 8, 0);
    for (size_t i = 0; i < N; ++i) {
      tqbe::store<bits<64>>(m, bits<64>(BASE + i * 8), bits<64>(i));
    }
  };

  Mem m1, m2;
  init_mem(m1);
  init_mem(m2);
  RefUF ref(N);

  // Path chain 0 -> 1 -> ... -> 15 compression test, then union / find stress
  uint64_t rng = 0x9E3779B97F4A7C15ULL;
  auto next_rng = [&]() -> uint64_t {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
  };

  for (int step = 0; step < 250; ++step) {
    uint64_t a = next_rng() % N;
    uint64_t b = next_rng() % N;
    if (step % 3 == 0) {
      FnUnion(m1, bits<64>(BASE), bits<64>(a), bits<64>(b));
      FnUnionInline(m2, bits<64>(BASE), bits<64>(a), bits<64>(b));
      ref.unite(a, b);
    } else {
      uint64_t ra1 = FnFind(m1, bits<64>(BASE), bits<64>(a)).data;
      uint64_t rb1 = FnFind(m1, bits<64>(BASE), bits<64>(b)).data;
      uint64_t ra2 = FnFind(m2, bits<64>(BASE), bits<64>(a)).data;
      uint64_t rb2 = FnFind(m2, bits<64>(BASE), bits<64>(b)).data;
      ASSERT_EQ((ra1 == rb1), (ref.find(a) == ref.find(b)));
      ASSERT_EQ((ra2 == rb2), (ref.find(a) == ref.find(b)));
    }
  }
  for (size_t i = 0; i < N; ++i) {
    for (size_t j = 0; j < N; ++j) {
      bool c1 = FnFind(m1, bits<64>(BASE), bits<64>(i)).data ==
                FnFind(m1, bits<64>(BASE), bits<64>(j)).data;
      bool c2 = FnFind(m2, bits<64>(BASE), bits<64>(i)).data ==
                FnFind(m2, bits<64>(BASE), bits<64>(j)).data;
      ASSERT_EQ(c1, (ref.find(i) == ref.find(j)));
      ASSERT_EQ(c2, (ref.find(i) == ref.find(j)));
    }
  }
  // Out-of-bounds read must throw UbException
  ASSERT_THROWS_UB(FnFind(m1, bits<64>(BASE), bits<64>(N)));
}

inline void verify_pair_edge_result(
    const Mem& pm,
    bool p1_0, bits<8> p1_1, bool p2_0, bool p2_1,
    bits<8> pAdd_0, bits<8> pAdd_1, bool pCmp_0, bool pCmp_1,
    bits<16> pSwap_0, bits<16> pSwap_1) {
  ASSERT_EQ(p1_0, true);
  ASSERT_EQ(p1_1.data, 0xAAULL);
  ASSERT_EQ(pm.read_byte(0x2000), 0x55U); /* (0xAA << 1) | 1 = 0x155 */
  ASSERT_EQ(pm.read_byte(0x2001), 0x01U);
  ASSERT_TRUE(!pm.is_mapped(0x2002));
  ASSERT_EQ(p2_0, true);
  ASSERT_EQ(p2_1, false);
  ASSERT_EQ(pm.read_byte(0x3000), 0x01U);
  ASSERT_TRUE(!pm.is_mapped(0x3001));
  ASSERT_EQ(pAdd_0.data, 0ULL);
  ASSERT_EQ(pAdd_1.data, 0ULL); /* no carry across pair! */
  ASSERT_EQ(pCmp_0, true);
  ASSERT_EQ(pCmp_1, true);
  ASSERT_EQ(pSwap_0.data, 0x3412ULL);
  ASSERT_EQ(pSwap_1.data, 0x7856ULL);
}

inline void verify_simd_sha_results(
    const v4i32& sd, const v4i32& sb, const v4i32& al, const v4i32& bw,
    const v4i32& r2, const v4i32& m1, const v4i32& m2) {
  auto chk = [](const v4i32& v, uint64_t lo, uint64_t hi, int line) {
    bits<128> pk = tqbe::pack_bits(v);
    if (pk.data[0] != lo || pk.data[1] != hi) {
      std::fprintf(stderr, "SIMD mismatch at line %d: got {%llx, %llx}\n",
                   line, (unsigned long long)pk.data[0],
                   (unsigned long long)pk.data[1]);
      std::abort();
    }
  };
  chk(sd, 0x99aabbccddeeff00ULL, 0x1122334455667788ULL, __LINE__);
  chk(sb, 0x8877665544332211ULL, 0xffeedd00bbaa99ULL, __LINE__);
  chk(al, 0x80090a0b04050607ULL, 0x112233440c0d0e0fULL, __LINE__);
  chk(bw, 0x405778800013344ULL, 0xc0dff008009bbccULL, __LINE__);
  chk(r2, 0xb755690e1d2e296dULL, 0xd555c24396d39b87ULL, __LINE__);
  chk(m1, 0x7a5b9bec99064a8bULL, 0x246fe1443f70f131ULL, __LINE__);
  chk(m2, 0x7c2bdc4cb586e58bULL, 0x739fba6748048996ULL, __LINE__);
}

template <typename Ops, bool IsLegal, bool HasSimd>
void run_core_edge_suite() {
  Mem mem;
  // 1. bool_edge: slt true false = true
  {
    auto [slt, sle, sgt, ult, xadd, shlK] = Ops::bool_edge(mem, true, false);
    ASSERT_EQ(slt, true);
    ASSERT_EQ(sle, true);
    ASSERT_EQ(sgt, false);
    ASSERT_EQ(ult, false);
    ASSERT_EQ(xadd, true);
    ASSERT_EQ(shlK, true);
    auto [slt2, sle2, sgt2, ult2, xadd2, shlK2] =
        Ops::bool_edge(mem, false, true);
    ASSERT_EQ(slt2, false);
    ASSERT_EQ(sle2, false);
    ASSERT_EQ(sgt2, true);
    ASSERT_EQ(ult2, true);
    ASSERT_EQ(xadd2, true);
    ASSERT_EQ(shlK2, false);
  }
  // 2. div_edge: sdiv0(INT64_MIN, -1), (x, 0), and sdiv/udiv/srem UB
  {
    using DivArgT = std::conditional_t<IsLegal, bits<8>, bits<4>>;
    bits<64> i64min(0x8000000000000000ULL);
    bits<64> neg1(0xFFFFFFFFFFFFFFFFULL);
    auto [sd0, ud0, sd4, sr] = Ops::div_edge(mem, i64min, neg1, DivArgT(0));
    ASSERT_EQ(sd0.data, 0x8000000000000000ULL);
    ASSERT_EQ(ud0.data, 0ULL);
    ASSERT_EQ(sd4.data, 8ULL); // 4-bit INT_MIN / -1 wraps to 8
    ASSERT_EQ(sr.data, 0xFFFFFFFFFFFFFFFFULL); // -7 % 3 = -1
    auto [sdz, udz, sd4b, srb] =
        Ops::div_edge(mem, bits<64>(12345), bits<64>(0), DivArgT(0));
    ASSERT_EQ(sdz.data, 0ULL);
    ASSERT_EQ(udz.data, 0ULL);
    (void)sd4b; (void)srb;
    ASSERT_THROWS_UB(Ops::div_edge(mem, i64min, neg1, DivArgT(1)));
    ASSERT_THROWS_UB(Ops::div_edge(mem, bits<64>(1), bits<64>(0), DivArgT(1)));
    ASSERT_THROWS_UB(Ops::div_edge(mem, i64min, neg1, DivArgT(2)));
    ASSERT_THROWS_UB(Ops::div_edge(mem, bits<64>(1), bits<64>(0), DivArgT(3)));
  }
  // 3. shift_edge: s == 0, s == 64 (mod), s == 65, negative ashr
  {
    bits<64> x(0x8000000000000003ULL);
    auto [v1, v2, v3, v4, v5, v6, v7] = Ops::shift_edge(mem, x, bits<64>(0));
    ASSERT_EQ(v1, x);
    ASSERT_EQ(v2, x);
    ASSERT_EQ(v3, x);
    ASSERT_EQ(v4, x);
    ASSERT_EQ(v5, x);
    ASSERT_EQ(v6, x);
    ASSERT_EQ(v7, x);
    auto r64 = Ops::shift_edge(mem, x, bits<64>(64));
    ASSERT_EQ(std::get<0>(r64), x);
    ASSERT_EQ(std::get<1>(r64), x);
    ASSERT_EQ(std::get<2>(r64), x);
    ASSERT_EQ(std::get<3>(r64), x);
    ASSERT_EQ(std::get<4>(r64), x);
    auto r1 = Ops::shift_edge(mem, x, bits<64>(1));
    ASSERT_EQ(std::get<0>(r1).data, 0x0000000000000006ULL);
    ASSERT_EQ(std::get<1>(r1).data, 0x4000000000000001ULL);
    ASSERT_EQ(std::get<2>(r1).data, 0xC000000000000001ULL);
    ASSERT_EQ(std::get<3>(r1).data, 0x0000000000000007ULL);
    ASSERT_EQ(std::get<4>(r1).data, 0xC000000000000001ULL);
    ASSERT_EQ(std::get<5>(r1).data, 0x0000000000000006ULL);
    ASSERT_EQ(std::get<6>(r1).data, 0x4000000000000001ULL);
    ASSERT_EQ(Ops::shift_edge(mem, x, bits<64>(65)), r1);
  }
  // 4. pair_edge: packed 9-bit & 2-bit layout + lane-wise pair ops
  {
    Mem pm;
    pm.alloc(0x2000, 2, 0x5A);
    pm.alloc(0x3000, 1, 0x5A);
    if constexpr (IsLegal) {
      auto [p1a, p1b, p2a, p2b, paa, pab, pca, pcb, psa, psb] =
          Ops::pair_edge(pm, bits<64>(0x2000), bits<64>(0x3000));
      verify_pair_edge_result(pm, p1a, p1b, p2a, p2b, paa, pab, pca, pcb,
                              psa, psb);
    } else {
      auto [p1, p2, pAdd, pCmp, pSwap] =
          Ops::pair_edge(pm, bits<64>(0x2000), bits<64>(0x3000));
      verify_pair_edge_result(pm, p1.first, p1.second, p2.first, p2.second,
                              pAdd.first, pAdd.second, pCmp.first,
                              pCmp.second, pSwap.first, pSwap.second);
    }
  }
  // 5. jnz_hlt
  {
    ASSERT_EQ(Ops::jnz_hlt(mem, true, bits<64>(10)).data, 52ULL);
    ASSERT_THROWS_UB(Ops::jnz_hlt(mem, false, bits<64>(10)));
  }
  // 6. mem_ub_edge
  {
    Mem mm;
    mm.map_byte(0x4000, 0);
    mm.map_byte(0x4001, 1);
    mm.map_byte(0x4002, 2);
    mm.alloc(0x4100, 7, 0x77);
    ASSERT_EQ(Ops::mem_ub_edge(mm, true, bits<64>(0x4000)), false);
    ASSERT_EQ(Ops::mem_ub_edge(mm, true, bits<64>(0x4001)), true);
    ASSERT_THROWS_UB(Ops::mem_ub_edge(mm, true, bits<64>(0x4002)));
    ASSERT_THROWS_UB(Ops::mem_ub_edge(mm, true, bits<64>(0x4003)));
    ASSERT_THROWS_UB(Ops::mem_ub_edge(mm, false, bits<64>(0x4100)));
    ASSERT_EQ(mm.read_byte(0x4100), 0x77U); // atomic store check
  }
  // 7. wide_bit_ops
  {
    auto [as, ac, sd, sb, ul, uh, sl, sh, cl, ct, cs, pp] =
        Ops::wide_bit_ops(mem, bits<64>(~0ULL), bits<64>(1), false);
    ASSERT_EQ(as.data, 0ULL);
    ASSERT_EQ(ac, true);
    ASSERT_EQ(sd.data, 0xFFFFFFFFFFFFFFFEULL);
    ASSERT_EQ(sb, false);
    ASSERT_EQ(ul.data, ~0ULL);
    ASSERT_EQ(uh.data, 0ULL);
    ASSERT_EQ(sl.data, ~0ULL);
    ASSERT_EQ(sh.data, ~0ULL);
    ASSERT_EQ(cl.data, 0ULL);
    ASSERT_EQ(ct.data, 0ULL);
    ASSERT_EQ(cs.data, 63ULL);
    ASSERT_EQ(pp.data, 64ULL);
    auto r0 = Ops::wide_bit_ops(mem, bits<64>(5), bits<64>(5), true);
    ASSERT_EQ(std::get<2>(r0).data, ~0ULL);
    ASSERT_EQ(std::get<3>(r0), true); // 5 < 5 + 1 -> borrow!
    auto rz = Ops::wide_bit_ops(mem, bits<64>(0), bits<64>(0), true);
    ASSERT_EQ(std::get<8>(rz).data, 64ULL);
    ASSERT_EQ(std::get<9>(rz).data, 64ULL);
    ASSERT_EQ(std::get<10>(rz).data, 63ULL);
    ASSERT_EQ(std::get<11>(rz).data, 0ULL);
  }
  // 8. fib_swap (parallel block-param swap)
  {
    ASSERT_EQ(Ops::fib_swap(mem, bits<64>(0)).data, 0ULL);
    ASSERT_EQ(Ops::fib_swap(mem, bits<64>(1)).data, 1ULL);
    ASSERT_EQ(Ops::fib_swap(mem, bits<64>(10)).data, 55ULL);
    ASSERT_EQ(Ops::fib_swap(mem, bits<64>(20)).data, 6765ULL);
  }
  // 9. call_keywords (even/odd + keyword escaping + dot collision + 0ret)
  {
    Mem km;
    km.alloc(0x5000, 8, 0);
    auto [ev, sum] = Ops::call_keywords(km, bits<64>(10), bits<64>(0x5000));
    ASSERT_EQ(ev, true);
    ASSERT_EQ(sum.data, 10ULL + 7 + 100 + 200 + 301);
    ASSERT_EQ(tqbe::load<bits<64>>(km, bits<64>(0x5000)).data, 0xCAFEULL);
    auto [ev2, sum2] = Ops::call_keywords(km, bits<64>(11), bits<64>(0x5000));
    ASSERT_EQ(ev2, false);
    ASSERT_EQ(sum2.data, 11ULL + 7 + 100 + 200 + 301);
  }
  // 10. float_std (NaN ordered/unordered + fma + sqrt + fptoui/fptosi UB)
  {
    fval<Fmt::s> s_two = fval<Fmt::s>::from_u64(0x40000000ULL);
    fval<Fmt::d> d_three = fval<Fmt::d>::from_u64(0x4008000000000000ULL);
    fval<Fmt::d> d_neg5 = fval<Fmt::d>::from_u64(0xC014000000000000ULL);
    fval<Fmt::d> d_nine = fval<Fmt::d>::from_u64(0x4022000000000000ULL);
    auto [fmaV, sqV, neV, eqV, u64, s64] =
        Ops::float_std(mem, s_two, d_three, d_neg5, d_nine);
    ASSERT_EQ(fmaV.raw.data, 0x3FF0000000000000ULL); // 2*3 - 5 = 1.0
    ASSERT_EQ(sqV.raw.data, 0x4008000000000000ULL);  // sqrt(9) = 3.0
    ASSERT_EQ(neV, true);
    ASSERT_EQ(eqV, false);
    ASSERT_EQ(u64.data, 3ULL);
    ASSERT_EQ(s64.data, static_cast<uint64_t>(-5LL));
    fval<Fmt::d> d_nan = fval<Fmt::d>::from_u64(0x7FF8000000000000ULL);
    ASSERT_THROWS_UB(Ops::float_std(mem, s_two, d_nan, d_neg5, d_nine));
    ASSERT_THROWS_UB(Ops::float_std(mem, s_two, d_neg5, d_neg5, d_nine));
  }
  // 11. simd_sha (vs exact Lean ground-truth constants)
  {
    v4i32 a = {{bits<32>(0x11223344), bits<32>(0x55667788)},
               {bits<32>(0x99AABBCC), bits<32>(0xDDEEFF00)}};
    v4i32 b = {{bits<32>(0x00010203), bits<32>(0x04050607)},
               {bits<32>(0x80090A0B), bits<32>(0x0C0D0E0F)}};
    v4i32 c = {{bits<32>(0x428A2F98), bits<32>(0x71374491)},
               {bits<32>(0xB5C0FBCF), bits<32>(0xE9B5DBA5)}};
    if constexpr (HasSimd) {
      auto [sd, sb, al, bw, r2, m1, m2] = Ops::simd_sha(mem, a, b, c);
      verify_simd_sha_results(sd, sb, al, bw, r2, m1, m2);
    } else {
      auto [sd0, sd1, sd2, sd3, sb0, sb1, sb2, sb3, al0, al1, al2, al3,
            bw0, bw1, bw2, bw3, r20, r21, r22, r23, m10, m11, m12, m13,
            m20, m21, m22, m23] =
          Ops::simd_sha(mem,
                        a.first.first, a.first.second,
                        a.second.first, a.second.second,
                        b.first.first, b.first.second,
                        b.second.first, b.second.second,
                        c.first.first, c.first.second,
                        c.second.first, c.second.second);
      auto mk = [](bits<32> w0, bits<32> w1, bits<32> w2, bits<32> w3) {
        return v4i32{{w0, w1}, {w2, w3}};
      };
      verify_simd_sha_results(
          mk(sd0, sd1, sd2, sd3), mk(sb0, sb1, sb2, sb3),
          mk(al0, al1, al2, al3), mk(bw0, bw1, bw2, bw3),
          mk(r20, r21, r22, r23), mk(m10, m11, m12, m13),
          mk(m20, m21, m22, m23));
    }
  }
}

#define MAKE_EDGE_OPS(NS)                                                     \
  struct EdgeOps_##NS {                                                       \
    static constexpr auto bool_edge = &NS::bool_edge;                         \
    static constexpr auto div_edge = &NS::div_edge;                           \
    static constexpr auto shift_edge = &NS::shift_edge;                       \
    static constexpr auto pair_edge = &NS::pair_edge;                         \
    static constexpr auto jnz_hlt = &NS::jnz_hlt;                             \
    static constexpr auto mem_ub_edge = &NS::mem_ub_edge;                     \
    static constexpr auto wide_bit_ops = &NS::wide_bit_ops;                   \
    static constexpr auto fib_swap = &NS::fib_swap;                           \
    static constexpr auto call_keywords = &NS::call_keywords;                 \
    static constexpr auto float_std = &NS::float_std;                         \
    static constexpr auto simd_sha = &NS::simd_sha;                           \
  };

MAKE_EDGE_OPS(edge_pre)
MAKE_EDGE_OPS(edge_aarch64)
MAKE_EDGE_OPS(edge_scalar64)
MAKE_EDGE_OPS(edge_avx2)
MAKE_EDGE_OPS(edge_avx512)

void test_ext_pre() {
  Mem mem;
  // bits0_128: s=0, clz128(0)=128, cls128(INT128_MIN)=0, sdiv0(INT128_MIN,-1)=INT128_MIN, udiv128
  {
    bits<128> i128min = bits<128>::from_words({0ULL, 0x8000000000000000ULL});
    bits<128> neg1 = bits<128>::from_words({~0ULL, ~0ULL});
    auto [z0, clz1, cls1, sd0, sh1, ud1] =
        edge_pre::bits0_128(mem, bits<0>{}, i128min, neg1, false);
    ASSERT_EQ(z0, bits<0>{});
    ASSERT_EQ(clz1.data[0], 0ULL);
    ASSERT_EQ(cls1.data[0], 0ULL);
    ASSERT_EQ(sd0, i128min);
    ASSERT_EQ(sh1.data[0], 0ULL);
    ASSERT_EQ(sh1.data[1], 0ULL);
    ASSERT_EQ(ud1.data[0], 0ULL);
    ASSERT_EQ(ud1.data[1], 0ULL); // INT128_MIN / UINT128_MAX = 0

    // clz<128>(0) == 128, shift s == 0, udiv(2^100, 2^30) == 2^70
    bits<128> p100 = bits<128>::from_words({0ULL, 1ULL << 36});
    bits<128> p30 = bits<128>::from_words({1ULL << 30, 0ULL});
    auto [z0b, clz2, cls2, sd2, sh2, ud2] =
        edge_pre::bits0_128(mem, bits<0>{}, bits<128>(0), p30, false);
    ASSERT_EQ(clz2.data[0], 128ULL);
    ASSERT_EQ(cls2.data[0], 127ULL);
    ASSERT_EQ(sd2.data[0], 0ULL);
    ASSERT_EQ(sh2, bits<128>(0));
    ASSERT_EQ(ud2.data[0], 0ULL);
    ASSERT_EQ(ud2.data[1], 0ULL);
    (void)z0b;

    auto [z0c, clz3, cls3, sd3, sh3, ud3] =
        edge_pre::bits0_128(mem, bits<0>{}, p100, p30, false);
    ASSERT_EQ(ud3, bits<128>::from_words({0ULL, 1ULL << 6})); // 2^70
    ASSERT_EQ(sh3, bits<128>::from_words({0ULL, 1ULL << (36 + 0)})); // shift mod 128 = 0!
    (void)z0c; (void)clz3; (void)cls3; (void)sd3;

    ASSERT_THROWS_UB(edge_pre::bits0_128(mem, bits<0>{}, p100, p30, true)); // udiv<0> UB
  }

  // float_hq: binary16 add + binary128 FMA cancellation + sqrt + fptoui<q, 128>
  {
    fval<Fmt::h> h_15 = fval<Fmt::h>::from_u64(0x3E00ULL);  // 1.5
    fval<Fmt::h> h_225 = fval<Fmt::h>::from_u64(0x4080ULL); // 2.25
    // q0 = 1 + 2^-60, q1 = 1 - 2^-60, q2 = -1.0 -> single-round FMA = -2^-120!
    // Exp = 16383 -> +1, +2^-60 means bit (112 - 60 = 52) set!
    // q1 = 1 - 2^-60 -> exp 16382, sig = (2^113 - 2^54) => bit 112..54 all 1, 53..0 wait:
    // 1 - 2^-60 = (2^60 - 1) * 2^-60 = (2^113 - 2^53) * 2^-113 => exp 16382, mhi = 0xFFFFFFFFFFFF, mlo = ~((1ULL << 53) - 1)
    fval<Fmt::q> q0{bits<128>::from_words({1ULL << 52, 0x3FFF000000000000ULL})};
    fval<Fmt::q> q1{bits<128>::from_words({~((1ULL << 53) - 1ULL), 0x3FFEFFFFFFFFFFFFULL})};
    fval<Fmt::q> q2{bits<128>::from_words({0ULL, 0xBFFF000000000000ULL})}; // -1.0
    // Wait: fptoui<q, 128> on q2=-1.0 is UB, so test cancellation directly and test fptoui on +2^100 separately:
    auto q_fma = tqbe::op_ffma(q0, q1, q2);
    // Expected -2^-120: sign=1, exp=16383-120=16263=0x3F87, sig=0 -> hi = 0xBF87_0000_0000_0000
    ASSERT_EQ(q_fma.raw.data[0], 0ULL);
    ASSERT_EQ(q_fma.raw.data[1], 0xBF87000000000000ULL);

    fval<Fmt::q> q_pos2{bits<128>::from_words({0ULL, 0x4063000000000000ULL})}; // 2^100 (exp=16383+100=0x4063)
    fval<Fmt::q> q_four{bits<128>::from_words({0ULL, 0x4001000000000000ULL})}; // 4.0
    fval<Fmt::h> h_one = fval<Fmt::h>::from_u64(0x3C00ULL);
    fval<Fmt::h> h_three = fval<Fmt::h>::from_u64(0x4200ULL);
    auto [hs, qf, qsq, u128] = edge_pre::float_hq(mem, h_one, h_three, q_four, q_four, q_pos2);
    ASSERT_EQ(hs.raw.data, 0x4400ULL); // 4.0 in binary16
    (void)qf;
    ASSERT_EQ(qsq.raw.data[0], 0ULL);
    ASSERT_EQ(qsq.raw.data[1], 0x4000000000000000ULL); // sqrt(4.0) = 2.0
    ASSERT_EQ(u128, bits<128>::from_words({0ULL, 1ULL << 36})); // 2^100!
    (void)h_15; (void)h_225;
  }

  // dead_dynamic_ub: branch 0 succeeds, branches 1..5 throw UbException
  {
    ASSERT_EQ(edge_pre::dead_dynamic_ub(mem, bits<8>(0)).data, 777ULL);
    for (uint64_t m = 1; m <= 5; ++m) {
      ASSERT_THROWS_UB(edge_pre::dead_dynamic_ub(mem, bits<8>(m)));
    }
  }

  // exit_edge: 0-arg exit & fval<q> + bool + bits<0> + pair<bool, u8> + escaped string
  {
    bool caught0 = false;
    try {
      edge_pre::exit_edge(mem, true, fval<Fmt::q>{});
    } catch (const ExitException& ex) {
      caught0 = true;
      ASSERT_EQ(ex.target, std::string("abort_zero"));
      ASSERT_EQ(ex.args.size(), size_t(0));
    }
    ASSERT_TRUE(caught0);

    bool caught1 = false;
    fval<Fmt::q> qv{bits<128>::from_words({0x1122334455667788ULL, 0x99AABBCCDDEEFF00ULL})};
    try {
      edge_pre::exit_edge(mem, false, qv);
    } catch (const ExitException& ex) {
      caught1 = true;
      ASSERT_EQ(ex.target, std::string("ext\"line\n1"));
      ASSERT_EQ(ex.args.size(), size_t(4));
      ASSERT_EQ(tqbe::decode_exit_arg<fval<Fmt::q>>(ex.args[0]), qv);
      ASSERT_EQ(tqbe::decode_exit_arg<bool>(ex.args[1]), true);
      ASSERT_EQ(ex.args[2].size(), size_t(0));
      auto p = tqbe::decode_exit_arg<pair<bool, bits<8>>>(ex.args[3]);
      ASSERT_EQ(p.first, true);
      ASSERT_EQ(p.second.data, 0xABULL);
    }
    ASSERT_TRUE(caught1);
  }

  // float_pair_ternlog: elementwise float pair + NaN fcmp + blend + ternlog 0xE8 (majority)
  {
    fval<Fmt::s> s_nan = fval<Fmt::s>::from_u64(0x7FC00000ULL);
    fval<Fmt::s> s_2 = fval<Fmt::s>::from_u64(0x40000000ULL);
    fval<Fmt::d> d_5 = fval<Fmt::d>::from_u64(0x4014000000000000ULL);
    fval<Fmt::d> d_1 = fval<Fmt::d>::from_u64(0x3FF0000000000000ULL);
    pair<fval<Fmt::s>, fval<Fmt::d>> p0{s_nan, d_5};
    pair<fval<Fmt::s>, fval<Fmt::d>> p1{s_2, d_1};
    auto [fpSum, fpGt, fpBlend, maj3] = edge_pre::float_pair_ternlog(
        mem, p0, p1, bits<64>(0xF0F0), bits<64>(0xCCCC), bits<64>(0xAAAA));
    ASSERT_EQ(fpGt.first, false); // NaN > 2.0 is false
    ASSERT_EQ(fpGt.second, true); // 5.0 > 1.0 is true
    ASSERT_EQ(fpBlend.first, s_2);
    ASSERT_EQ(fpBlend.second, d_5);
    ASSERT_EQ(fpSum.second.raw.data, 0x4018000000000000ULL); // 6.0
    ASSERT_EQ(maj3.data, 0xE8E8ULL); // majority(F0F0, CCCC, AAAA) = E8E8
  }

  // quad_huge_fptoui: must NOT trigger UBSan float-cast-overflow before throwing UbException
  {
    fval<Fmt::q> q_1e100{bits<128>::from_words({0ULL, 0x4149000000000000ULL})}; // ~2^332
    ASSERT_THROWS_UB(edge_pre::quad_huge_fptoui(mem, q_1e100));
    fval<Fmt::q> q_neg05{bits<128>::from_words({0ULL, 0xBFFE000000000000ULL})}; // -0.5 -> 0
    ASSERT_EQ(edge_pre::quad_huge_fptoui(mem, q_neg05).data, 0ULL);
    fval<Fmt::q> q_neg1{bits<128>::from_words({0ULL, 0xBFFF000000000000ULL})}; // -1.0 -> UB
    ASSERT_THROWS_UB(edge_pre::quad_huge_fptoui(mem, q_neg1));
  }

  // dag_reachable: 6-block diamond DAG must preserve tail seed L_5 and all intermediate edges
  {
    ASSERT_EQ(edge_pre::dag_reachable(mem, bits<64>(1)).data, 11ULL);
    ASSERT_EQ(edge_pre::dag_reachable(mem, bits<64>(2)).data, 32ULL);
    ASSERT_EQ(edge_pre::dag_reachable(mem, bits<64>(3)).data, 33ULL);
    ASSERT_EQ(edge_pre::dag_reachable(mem, bits<64>(4)).data, 34ULL);
    ASSERT_EQ(edge_pre::dag_reachable(mem, bits<64>(15)).data, 515ULL);
  }

  // exit_escapes: octal non-greedy escapes before 'a'/'7' + multi-byte UTF-8 round-trip
  {
    bool caughtEsc = false;
    try {
      edge_pre::exit_escapes(mem);
    } catch (const ExitException& ex) {
      caughtEsc = true;
      ASSERT_EQ(ex.target,
                std::string("ext\x01" "abc\x01" "7caf\xC3\xA9\xE2\x82\xAC"));
      ASSERT_EQ(ex.args.size(), size_t(0));
    }
    ASSERT_TRUE(caughtEsc);
  }
}

} // namespace

int main() {
  test_uf_target<uf_pre::find, uf_pre::fn_union, uf_pre::unionInline>("uf_pre");
  test_uf_target<uf_aarch64::find, uf_aarch64::fn_union, uf_aarch64::unionInline>("uf_aarch64");
  test_uf_target<uf_scalar64::find, uf_scalar64::fn_union, uf_scalar64::unionInline>("uf_scalar64");
  test_uf_target<uf_avx2::find, uf_avx2::fn_union, uf_avx2::unionInline>("uf_avx2");

  run_core_edge_suite<EdgeOps_edge_pre, false, true>();
  run_core_edge_suite<EdgeOps_edge_aarch64, true, false>();
  run_core_edge_suite<EdgeOps_edge_scalar64, true, false>();
  run_core_edge_suite<EdgeOps_edge_avx2, true, true>();
  run_core_edge_suite<EdgeOps_edge_avx512, true, true>();

  test_ext_pre();

  std::printf("ALL CATCH_UB TESTS PASSED (UF pre/aarch64/scalar64/avx2 + edge pre/aarch64/scalar64/avx2/avx512)\n");
  return 0;
}
