#ifndef LEANQBE_T_FRONTEND_C0_H
#define LEANQBE_T_FRONTEND_C0_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* Fixed-width C0 scalar types (SysV LP64) */
typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef int8_t   i8;
typedef int16_t  i16;
typedef int32_t  i32;
typedef int64_t  i64;
typedef double   f64;
typedef u32      ref;

/* Explicit switch fallthrough annotation (valid in C99/C11/C++20 under -Wextra -Werror) */
#if defined(__cplusplus) && __cplusplus >= 201703L
#define fallthrough [[fallthrough]]
#elif defined(__GNUC__) || defined(__clang__)
#define fallthrough __attribute__((fallthrough))
#else
#define fallthrough ((void)0)
#endif

/* Assume and checked-abort primitives matching LeanQbe.T (.hlt / .exit "c0_abort") */
#define c0_assume(c)          \
  do {                        \
    if (!(c)) __builtin_trap(); \
  } while (0)

#ifdef C0_EXTERN_ABORT
#ifdef __cplusplus
extern "C" {
#endif
void c0_abort(i32 line);
#ifdef __cplusplus
}
#endif
#else
static inline void c0_abort(i32 line) {
  (void)line;
  __builtin_trap();
}
#endif

#define check(c)                  \
  do {                            \
    if (!(c)) c0_abort((i32)__LINE__); \
  } while (0)

/* Multi-return C99/C++20 struct & tuple helpers */
#define C0_RET2(T0, T1) struct { T0 _0; T1 _1; }
#define C0_RET3(T0, T1, T2) struct { T0 _0; T1 _1; T2 _2; }

#ifdef __cplusplus
#define C0_TUP2(Ty, a, b) (Ty{ (a), (b) })
#define C0_TUP3(Ty, a, b, c) (Ty{ (a), (b), (c) })
#define C0_TIE2(x0, x1, expr)             \
  do {                                    \
    auto _c0_r = (expr);                  \
    (x0) = _c0_r._0;                      \
    (x1) = _c0_r._1;                      \
  } while (0)
#define C0_TIE3(x0, x1, x2, expr)         \
  do {                                    \
    auto _c0_r = (expr);                  \
    (x0) = _c0_r._0;                      \
    (x1) = _c0_r._1;                      \
    (x2) = _c0_r._2;                      \
  } while (0)
#else
#define C0_TUP2(Ty, a, b) ((Ty){ (a), (b) })
#define C0_TUP3(Ty, a, b, c) ((Ty){ (a), (b), (c) })
#define C0_TIE2(x0, x1, expr)             \
  do {                                    \
    __typeof__(expr) _c0_r = (expr);      \
    (x0) = _c0_r._0;                      \
    (x1) = _c0_r._1;                      \
  } while (0)
#define C0_TIE3(x0, x1, x2, expr)         \
  do {                                    \
    __typeof__(expr) _c0_r = (expr);      \
    (x0) = _c0_r._0;                      \
    (x1) = _c0_r._1;                      \
    (x2) = _c0_r._2;                      \
  } while (0)
#endif

typedef C0_RET2(u64, bool) c0_u64_bool;
typedef C0_RET2(u64, u64)  c0_u64_u64;
typedef C0_RET2(u32, bool) c0_u32_bool;
typedef C0_RET2(u32, u32)  c0_u32_u32;

/* Core C0 bit/arithmetic/float intrinsics (exact parity with LeanQbe.T.OpCode) */
static inline u32 c0_rotl32(u32 x, u32 s) {
  u32 k = s & 31u;
  return (k == 0u) ? x : ((x << k) | (x >> (32u - k)));
}

static inline u32 c0_rotr32(u32 x, u32 s) {
  u32 k = s & 31u;
  return (k == 0u) ? x : ((x >> k) | (x << (32u - k)));
}

static inline u64 c0_rotl64(u64 x, u64 s) {
  u64 k = s & 63ULL;
  return (k == 0ULL) ? x : ((x << k) | (x >> (64ULL - k)));
}

static inline u64 c0_rotr64(u64 x, u64 s) {
  u64 k = s & 63ULL;
  return (k == 0ULL) ? x : ((x >> k) | (x << (64ULL - k)));
}

static inline u32 c0_clz32(u32 x) {
  return (x == 0u) ? 32u : (u32)__builtin_clz(x);
}

static inline u64 c0_clz64(u64 x) {
  return (x == 0ULL) ? 64ULL : (u64)__builtin_clzll(x);
}

static inline u32 c0_ctz32(u32 x) {
  return (x == 0u) ? 32u : (u32)__builtin_ctz(x);
}

static inline u64 c0_ctz64(u64 x) {
  return (x == 0ULL) ? 64ULL : (u64)__builtin_ctzll(x);
}

static inline u32 c0_popcnt32(u32 x) {
  return (u32)__builtin_popcount(x);
}

static inline u64 c0_popcnt64(u64 x) {
  return (u64)__builtin_popcountll(x);
}

static inline c0_u64_bool c0_addc64(u64 a, u64 b, bool cin) {
  u64 c = cin ? (u64)1 : (u64)0;
  u64 s1 = a + b;
  bool c1 = s1 < a;
  u64 s2 = s1 + c;
  bool c2 = s2 < s1;
  return C0_TUP2(c0_u64_bool, s2, (bool)(c1 || c2));
}

static inline c0_u64_bool c0_subb64(u64 a, u64 b, bool bin) {
  u64 borrow_in = bin ? (u64)1 : (u64)0;
  u64 d = a - b - borrow_in;
  bool b_out = bin ? (a <= b) : (a < b);
  return C0_TUP2(c0_u64_bool, d, b_out);
}

static inline c0_u64_u64 c0_umul128(u64 a, u64 b) {
  u64 a_lo = a & 0xFFFFFFFFULL;
  u64 a_hi = a >> 32;
  u64 b_lo = b & 0xFFFFFFFFULL;
  u64 b_hi = b >> 32;
  u64 p00 = a_lo * b_lo;
  u64 p01 = a_lo * b_hi;
  u64 p10 = a_hi * b_lo;
  u64 p11 = a_hi * b_hi;
  u64 mid = (p00 >> 32) + (p01 & 0xFFFFFFFFULL) + (p10 & 0xFFFFFFFFULL);
  u64 lo = (p00 & 0xFFFFFFFFULL) | (mid << 32);
  u64 hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
  return C0_TUP2(c0_u64_u64, lo, hi);
}

static inline u64 c0_f64_to_bits(f64 d) {
  u64 u = 0;
  memcpy(&u, &d, sizeof(u));
  return u;
}

static inline f64 c0_bits_to_f64(u64 u) {
  f64 d = 0.0;
  memcpy(&d, &u, sizeof(d));
  return d;
}

static inline u64 c0_f64_to_u64_sat(f64 d) {
  if (!(d >= 0.0)) return (u64)0;
  if (!(d < 18446744073709551616.0)) return ~(u64)0;
  return (u64)d;
}

#endif /* LEANQBE_T_FRONTEND_C0_H */
