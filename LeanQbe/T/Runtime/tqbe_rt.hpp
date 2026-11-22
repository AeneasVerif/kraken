#pragma once

#include <array>
#include <bit>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <initializer_list>
#include <limits>
#include <stdexcept>
#include <string>
#include <tuple>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

namespace tqbe {

static_assert(std::endian::native == std::endian::little,
              "tqbe_rt.hpp assumes little-endian host");

// Rule A6: `.hlt` / `TQBE_UB` MUST trap via `__builtin_trap()` by default
// (never `__builtin_unreachable()`, so unproved binaries fail loudly instead of
// exploiting UB). Throw `UbException` ONLY when `-DTQBE_CATCH_UB` is defined.
struct UbException : std::runtime_error {
  explicit UbException(const char* msg) : std::runtime_error(msg) {}
};

#ifdef TQBE_CATCH_UB
[[noreturn]] inline void ub(const char* msg) {
  throw UbException(msg);
}
#define TQBE_UB(msg) ::tqbe::ub(msg)
#define TQBE_HLT() ::tqbe::ub("hlt")
#else
[[noreturn]] inline void ub(const char*) {
  __builtin_trap();
}
#define TQBE_UB(msg) __builtin_trap()
#define TQBE_HLT() __builtin_trap()
#endif

// ============================================================================
// Core value types corresponding to LeanQbe.T.Ty / Fmt
// ============================================================================

enum class Fmt { h, s, d, q };

template <size_t N>
consteval uint64_t mask64() {
  if constexpr (N == 0) {
    return 0ULL;
  } else if constexpr (N >= 64) {
    return ~0ULL;
  } else {
    return (1ULL << N) - 1ULL;
  }
}

template <size_t N>
struct bits;

template <>
struct bits<0> {
  static constexpr size_t width = 0;
  constexpr bits() = default;
  constexpr explicit bits(uint64_t) {}
  static constexpr bits from_words(std::initializer_list<uint64_t>) { return {}; }
  static constexpr bits from_array(const std::array<uint64_t, 0>&) { return {}; }
  constexpr uint64_t word(size_t) const { return 0ULL; }
  constexpr bool bit(size_t) const { return false; }
  constexpr void set_bit(size_t, bool) {}
  constexpr bool operator==(const bits&) const = default;
};

template <size_t N>
struct bits {
  static constexpr size_t width = N;
  static constexpr bool single_word = (N <= 64);
  static constexpr size_t words = (N + 63) / 64;
  static constexpr uint64_t top_mask =
      (N % 64 == 0) ? ~0ULL : ((1ULL << (N % 64)) - 1ULL);

  std::conditional_t<single_word, uint64_t, std::array<uint64_t, words>> data{};

  constexpr bits() = default;

  constexpr explicit bits(uint64_t x) : data{} {
    if constexpr (single_word) {
      data = x & mask64<N>();
    } else {
      data[0] = x;
      normalize();
    }
  }

  static constexpr bits from_words(std::initializer_list<uint64_t> il) {
    bits r{};
    size_t i = 0;
    for (uint64_t x : il) {
      if constexpr (single_word) {
        if (i == 0) r.data = x;
      } else {
        if (i < words) r.data[i] = x;
      }
      ++i;
    }
    r.normalize();
    return r;
  }

  static constexpr bits from_array(const std::array<uint64_t, words>& arr) {
    bits r{};
    if constexpr (single_word) {
      r.data = arr[0];
    } else {
      r.data = arr;
    }
    r.normalize();
    return r;
  }

  constexpr void normalize() {
    if constexpr (single_word) {
      data &= mask64<N>();
    } else {
      data[words - 1] &= top_mask;
    }
  }

  constexpr uint64_t word(size_t i) const {
    if constexpr (single_word) {
      return (i == 0) ? data : 0ULL;
    } else {
      return (i < words) ? data[i] : 0ULL;
    }
  }

  constexpr void set_word(size_t i, uint64_t v) {
    if constexpr (single_word) {
      if (i == 0) data = v & mask64<N>();
    } else {
      if (i < words) {
        data[i] = v;
        if (i == words - 1) data[i] &= top_mask;
      }
    }
  }

  constexpr bool bit(size_t idx) const {
    if (idx >= N) return false;
    return ((word(idx / 64) >> (idx % 64)) & 1ULL) != 0ULL;
  }

  constexpr void set_bit(size_t idx, bool val) {
    if (idx >= N) return;
    uint64_t m = 1ULL << (idx % 64);
    size_t wi = idx / 64;
    if constexpr (single_word) {
      if (val) data |= m; else data &= ~m;
      data &= mask64<N>();
    } else {
      if (val) data[wi] |= m; else data[wi] &= ~m;
      data[words - 1] &= top_mask;
    }
  }

  constexpr bool operator==(const bits&) const = default;
};

consteval size_t fmt_bits(Fmt f) {
  switch (f) {
    case Fmt::h:
      return 16;
    case Fmt::s:
      return 32;
    case Fmt::d:
      return 64;
    case Fmt::q:
      return 128;
  }
  return 0;
}

template <Fmt F>
struct fval {
  static constexpr size_t width = fmt_bits(F);
  bits<width> raw{};

  constexpr fval() = default;
  constexpr explicit fval(bits<width> b) : raw(b) {}
  static constexpr fval from_bits(bits<width> b) { return fval{b}; }
  static constexpr fval from_u64(uint64_t x) { return fval{bits<width>(x)}; }

  constexpr bool operator==(const fval&) const = default;
};

template <typename A, typename B>
struct pair {
  A first{};
  B second{};

  constexpr pair() = default;
  constexpr pair(A a, B b) : first(std::move(a)), second(std::move(b)) {}
  constexpr bool operator==(const pair&) const = default;
};

using v4i32 = pair<pair<bits<32>, bits<32>>, pair<bits<32>, bits<32>>>;

// ============================================================================
// Type traits corresponding to LeanQbe.T.Ty properties
// ============================================================================

template <typename T>
struct ty_traits;

template <>
struct ty_traits<bool> {
  static constexpr size_t bit_size = 1;
  static constexpr bool has_float = false;
  static constexpr bool is_float_tree = false;
  static constexpr bool bswap_ok = false;
  static constexpr bool is_bits = false;
  static constexpr bool is_fval = false;
  static constexpr bool is_pair = false;
  using mask_type = bool;
};

template <size_t N>
struct ty_traits<bits<N>> {
  static constexpr size_t bit_size = N;
  static constexpr bool has_float = false;
  static constexpr bool is_float_tree = false;
  static constexpr bool bswap_ok = (N % 8 == 0);
  static constexpr bool is_bits = true;
  static constexpr bool is_fval = false;
  static constexpr bool is_pair = false;
  using mask_type = bool;
};

template <Fmt F>
struct ty_traits<fval<F>> {
  static constexpr size_t bit_size = fmt_bits(F);
  static constexpr bool has_float = true;
  static constexpr bool is_float_tree = true;
  static constexpr bool bswap_ok = false;
  static constexpr bool is_bits = false;
  static constexpr bool is_fval = true;
  static constexpr bool is_pair = false;
  using mask_type = bool;
};

template <typename A, typename B>
struct ty_traits<pair<A, B>> {
  static constexpr size_t bit_size =
      ty_traits<A>::bit_size + ty_traits<B>::bit_size;
  static constexpr bool has_float =
      ty_traits<A>::has_float || ty_traits<B>::has_float;
  static constexpr bool is_float_tree =
      ty_traits<A>::is_float_tree && ty_traits<B>::is_float_tree;
  static constexpr bool bswap_ok =
      ty_traits<A>::bswap_ok && ty_traits<B>::bswap_ok;
  static constexpr bool is_bits = false;
  static constexpr bool is_fval = false;
  static constexpr bool is_pair = true;
  using mask_type = pair<typename ty_traits<A>::mask_type,
                         typename ty_traits<B>::mask_type>;
};

template <typename T>
using mask_t = typename ty_traits<T>::mask_type;

template <typename T>
consteval size_t bit_size() {
  return ty_traits<T>::bit_size;
}

template <typename T>
consteval size_t byte_size() {
  return (bit_size<T>() + 7) / 8;
}

template <typename T>
consteval bool has_float() {
  return ty_traits<T>::has_float;
}

template <typename T>
consteval bool is_float_tree() {
  return ty_traits<T>::is_float_tree;
}

template <typename T>
consteval bool bswap_ok() {
  return ty_traits<T>::bswap_ok;
}

// ============================================================================
// Core bitvector operations (all guarded for N == 0, s == 0, s >= N)
// ============================================================================

template <size_t N>
constexpr bool bv_is_zero(bits<N> a) {
  if constexpr (N == 0) {
    return true;
  } else if constexpr (N <= 64) {
    return a.data == 0ULL;
  } else {
    for (uint64_t x : a.data) {
      if (x != 0ULL) return false;
    }
    return true;
  }
}

template <size_t N>
constexpr bits<N> bv_all_ones() {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(mask64<N>());
  } else {
    bits<N> r{};
    for (size_t i = 0; i < bits<N>::words; ++i) r.data[i] = ~0ULL;
    r.normalize();
    return r;
  }
}

template <size_t N>
constexpr bits<N> bv_int_min() {
  if constexpr (N == 0) {
    return {};
  } else {
    bits<N> r{};
    r.set_bit(N - 1, true);
    return r;
  }
}

template <size_t N>
constexpr bool bv_sign_bit(bits<N> a) {
  if constexpr (N == 0) {
    return false;
  } else {
    return a.bit(N - 1);
  }
}

template <size_t N>
constexpr bits<N> bv_not(bits<N> a) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(~a.data);
  } else {
    bits<N> r{};
    for (size_t i = 0; i < bits<N>::words; ++i) r.data[i] = ~a.data[i];
    r.normalize();
    return r;
  }
}

template <size_t N>
constexpr bits<N> bv_and(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(a.data & b.data);
  } else {
    bits<N> r{};
    for (size_t i = 0; i < bits<N>::words; ++i) r.data[i] = a.data[i] & b.data[i];
    return r;
  }
}

template <size_t N>
constexpr bits<N> bv_or(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(a.data | b.data);
  } else {
    bits<N> r{};
    for (size_t i = 0; i < bits<N>::words; ++i) r.data[i] = a.data[i] | b.data[i];
    return r;
  }
}

template <size_t N>
constexpr bits<N> bv_xor(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(a.data ^ b.data);
  } else {
    bits<N> r{};
    for (size_t i = 0; i < bits<N>::words; ++i) r.data[i] = a.data[i] ^ b.data[i];
    return r;
  }
}

template <size_t N>
constexpr bits<N> bv_add(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(a.data + b.data);
  } else {
    bits<N> r{};
    uint64_t carry = 0;
    for (size_t i = 0; i < bits<N>::words; ++i) {
      uint64_t s1 = a.data[i] + b.data[i];
      uint64_t c1 = (s1 < a.data[i]) ? 1ULL : 0ULL;
      uint64_t s2 = s1 + carry;
      uint64_t c2 = (s2 < s1) ? 1ULL : 0ULL;
      r.data[i] = s2;
      carry = c1 | c2;
    }
    r.normalize();
    return r;
  }
}

template <size_t N>
constexpr bits<N> bv_sub(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(a.data - b.data);
  } else {
    bits<N> r{};
    uint64_t borrow = 0;
    for (size_t i = 0; i < bits<N>::words; ++i) {
      uint64_t d1 = a.data[i] - b.data[i];
      uint64_t b1 = (a.data[i] < b.data[i]) ? 1ULL : 0ULL;
      uint64_t d2 = d1 - borrow;
      uint64_t b2 = (d1 < borrow) ? 1ULL : 0ULL;
      r.data[i] = d2;
      borrow = b1 | b2;
    }
    r.normalize();
    return r;
  }
}

template <size_t N>
constexpr bits<N> bv_neg(bits<N> a) {
  return bv_sub(bits<N>{}, a);
}

constexpr void mul64_wide(uint64_t a, uint64_t b, uint64_t& lo, uint64_t& hi) {
  uint64_t a0 = a & 0xFFFFFFFFULL;
  uint64_t a1 = a >> 32;
  uint64_t b0 = b & 0xFFFFFFFFULL;
  uint64_t b1 = b >> 32;
  uint64_t p00 = a0 * b0;
  uint64_t p01 = a0 * b1;
  uint64_t p10 = a1 * b0;
  uint64_t p11 = a1 * b1;
  uint64_t mid = (p00 >> 32) + (p01 & 0xFFFFFFFFULL) + (p10 & 0xFFFFFFFFULL);
  lo = (p00 & 0xFFFFFFFFULL) | (mid << 32);
  hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
}

template <size_t N>
constexpr bits<N> bv_mul(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return {};
  } else if constexpr (N <= 64) {
    return bits<N>(a.data * b.data);
  } else {
    bits<N> r{};
    for (size_t i = 0; i < bits<N>::words; ++i) {
      uint64_t carry = 0;
      for (size_t j = 0; i + j < bits<N>::words; ++j) {
        uint64_t lo = 0, hi = 0;
        mul64_wide(a.data[i], b.data[j], lo, hi);
        uint64_t s1 = r.data[i + j] + lo;
        uint64_t c1 = (s1 < r.data[i + j]) ? 1ULL : 0ULL;
        uint64_t s2 = s1 + carry;
        uint64_t c2 = (s2 < s1) ? 1ULL : 0ULL;
        r.data[i + j] = s2;
        carry = hi + c1 + c2;
      }
    }
    r.normalize();
    return r;
  }
}

template <size_t N>
constexpr bits<N> bv_shl_amt(bits<N> a, uint64_t s) {
  if constexpr (N == 0) {
    return {};
  } else {
    if (s == 0) return a;
    if (s >= N) return {};
    if constexpr (N <= 64) {
      return bits<N>(a.data << s);
    } else {
      size_t ws = static_cast<size_t>(s / 64);
      unsigned bs = static_cast<unsigned>(s % 64);
      bits<N> r{};
      if (bs == 0) {
        for (size_t i = ws; i < bits<N>::words; ++i) {
          r.data[i] = a.data[i - ws];
        }
      } else {
        for (size_t i = ws; i < bits<N>::words; ++i) {
          uint64_t v = a.data[i - ws] << bs;
          if (i > ws) v |= (a.data[i - ws - 1] >> (64U - bs));
          r.data[i] = v;
        }
      }
      r.normalize();
      return r;
    }
  }
}

template <size_t N>
constexpr bits<N> bv_lshr_amt(bits<N> a, uint64_t s) {
  if constexpr (N == 0) {
    return {};
  } else {
    if (s == 0) return a;
    if (s >= N) return {};
    if constexpr (N <= 64) {
      return bits<N>(a.data >> s);
    } else {
      size_t ws = static_cast<size_t>(s / 64);
      unsigned bs = static_cast<unsigned>(s % 64);
      bits<N> r{};
      if (bs == 0) {
        for (size_t i = 0; i + ws < bits<N>::words; ++i) {
          r.data[i] = a.data[i + ws];
        }
      } else {
        for (size_t i = 0; i + ws < bits<N>::words; ++i) {
          uint64_t v = a.data[i + ws] >> bs;
          if (i + ws + 1 < bits<N>::words) {
            v |= (a.data[i + ws + 1] << (64U - bs));
          }
          r.data[i] = v;
        }
      }
      return r;
    }
  }
}

template <size_t N>
constexpr bits<N> bv_ashr_amt(bits<N> a, uint64_t s) {
  if constexpr (N == 0) {
    return {};
  } else {
    bool neg = bv_sign_bit(a);
    if (s == 0) return a;
    if (s >= N) return neg ? bv_all_ones<N>() : bits<N>{};
    if (!neg) return bv_lshr_amt(a, s);
    return bv_not(bv_lshr_amt(bv_not(a), s));
  }
}

template <size_t N>
constexpr bits<N> bv_rotl_amt(bits<N> a, uint64_t s) {
  if constexpr (N <= 1) {
    return a;
  } else {
    uint64_t k = s % N;
    if (k == 0) return a;
    return bv_or(bv_shl_amt(a, k), bv_lshr_amt(a, N - k));
  }
}

template <size_t N>
constexpr bits<N> bv_rotr_amt(bits<N> a, uint64_t s) {
  if constexpr (N <= 1) {
    return a;
  } else {
    uint64_t k = s % N;
    if (k == 0) return a;
    return bv_or(bv_lshr_amt(a, k), bv_shl_amt(a, N - k));
  }
}

template <size_t M>
constexpr uint64_t bv_mod_u64(bits<M> s, uint64_t mod) {
  if (mod == 0) return 0;
  if constexpr (M == 0) {
    return 0;
  } else if constexpr (M <= 64) {
    return s.data % mod;
  } else {
    uint64_t acc = 0;
    for (size_t i = M; i > 0; --i) {
      uint64_t b = s.bit(i - 1) ? 1ULL : 0ULL;
      uint64_t rem = mod - acc;
      if (acc >= rem) {
        acc = (acc - rem) + b;
        if (acc >= mod) acc -= mod;
      } else {
        acc = (acc + acc) + b;
        if (acc >= mod) acc -= mod;
      }
    }
    return acc;
  }
}

// ============================================================================
// Comparisons
// ============================================================================

enum class CmpOp { eq, ne, ult, ule, ugt, uge, slt, sle, sgt, sge };
enum class FCmpOp { eq, ne, lt, le, gt, ge, ord, uno };

template <size_t N>
constexpr bool bv_ult(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return false;
  } else if constexpr (N <= 64) {
    return a.data < b.data;
  } else {
    for (size_t i = bits<N>::words; i > 0; --i) {
      size_t wi = i - 1;
      if (a.data[wi] != b.data[wi]) return a.data[wi] < b.data[wi];
    }
    return false;
  }
}

template <size_t N>
constexpr bool bv_ule(bits<N> a, bits<N> b) {
  return bv_ult(a, b) || (a == b);
}

template <size_t N>
constexpr bool bv_slt(bits<N> a, bits<N> b) {
  if constexpr (N == 0) {
    return false;
  } else {
    bool sa = bv_sign_bit(a);
    bool sb = bv_sign_bit(b);
    if (sa != sb) return sa;
    return bv_ult(a, b);
  }
}

template <size_t N>
constexpr bool bv_sle(bits<N> a, bits<N> b) {
  return bv_slt(a, b) || (a == b);
}

template <CmpOp Op, size_t N>
constexpr bool bv_cmp(bits<N> a, bits<N> b) {
  if constexpr (Op == CmpOp::eq) return a == b;
  else if constexpr (Op == CmpOp::ne) return a != b;
  else if constexpr (Op == CmpOp::ult) return bv_ult(a, b);
  else if constexpr (Op == CmpOp::ule) return bv_ule(a, b);
  else if constexpr (Op == CmpOp::ugt) return bv_ult(b, a);
  else if constexpr (Op == CmpOp::uge) return bv_ule(b, a);
  else if constexpr (Op == CmpOp::slt) return bv_slt(a, b);
  else if constexpr (Op == CmpOp::sle) return bv_sle(a, b);
  else if constexpr (Op == CmpOp::sgt) return bv_slt(b, a);
  else return bv_sle(b, a);
}

template <CmpOp Op>
constexpr bool bool_cmp(bool a, bool b) {
  if constexpr (Op == CmpOp::eq) return a == b;
  else if constexpr (Op == CmpOp::ne) return a != b;
  else if constexpr (Op == CmpOp::ult) return !a && b;
  else if constexpr (Op == CmpOp::ule) return !a || b;
  else if constexpr (Op == CmpOp::ugt) return a && !b;
  else if constexpr (Op == CmpOp::uge) return a || !b;
  else if constexpr (Op == CmpOp::slt) return a && !b; // true (-1) < false (0)
  else if constexpr (Op == CmpOp::sle) return a || !b;
  else if constexpr (Op == CmpOp::sgt) return !a && b;
  else return !a || b; // sge
}

// ============================================================================
// Width extensions / truncations
// ============================================================================

template <size_t M, size_t N>
inline bits<N> op_zext(bits<M> a) {
  if constexpr (M > N) {
    (void)a;
    TQBE_UB("zext invalid direction");
  } else if constexpr (M == 0 || N == 0) {
    return bits<N>{};
  } else if constexpr (M == N) {
    return a;
  } else if constexpr (N <= 64) {
    return bits<N>(a.data);
  } else {
    bits<N> r{};
    if constexpr (M <= 64) {
      r.data[0] = a.data;
    } else {
      for (size_t i = 0; i < bits<M>::words; ++i) r.data[i] = a.data[i];
    }
    r.normalize();
    return r;
  }
}

template <size_t M, size_t N>
inline bits<N> op_sext(bits<M> a) {
  if constexpr (M > N) {
    (void)a;
    TQBE_UB("sext invalid direction");
  } else if constexpr (M == 0 || N == 0) {
    return bits<N>{};
  } else if constexpr (M == N) {
    return a;
  } else {
    bits<N> r = op_zext<M, N>(a);
    if (bv_sign_bit(a)) {
      if constexpr (N <= 64) {
        r.data |= (mask64<N>() & ~mask64<M>());
      } else {
        size_t full_words = M / 64;
        unsigned rem_bits = static_cast<unsigned>(M % 64);
        if constexpr (M <= 64) {
          if (M < 64) r.data[0] |= ~mask64<M>();
          for (size_t i = 1; i < bits<N>::words; ++i) r.data[i] = ~0ULL;
        } else {
          if (rem_bits != 0) {
            r.data[full_words] |= (~0ULL << rem_bits);
            for (size_t i = full_words + 1; i < bits<N>::words; ++i) r.data[i] = ~0ULL;
          } else {
            for (size_t i = full_words; i < bits<N>::words; ++i) r.data[i] = ~0ULL;
          }
        }
        r.normalize();
      }
    }
    return r;
  }
}

template <size_t M, size_t N>
inline bits<N> op_trunc(bits<M> a) {
  if constexpr (M < N) {
    (void)a;
    TQBE_UB("trunc invalid direction");
  } else if constexpr (N == 0) {
    return bits<0>{};
  } else if constexpr (M == N) {
    return a;
  } else if constexpr (N <= 64) {
    return bits<N>(a.word(0));
  } else {
    bits<N> r{};
    for (size_t i = 0; i < bits<N>::words; ++i) r.data[i] = a.word(i);
    r.normalize();
    return r;
  }
}

// ============================================================================
// Bit-packing / unpacking across bool, bits<N>, fval<F>, pair<A, B>
// ============================================================================

template <typename T>
inline bits<bit_size<T>()> pack_bits(const T& v) {
  if constexpr (std::is_same_v<T, bool>) {
    return bits<1>(v ? 1ULL : 0ULL);
  } else if constexpr (ty_traits<T>::is_fval) {
    return v.raw;
  } else if constexpr (ty_traits<T>::is_bits) {
    return v;
  } else {
    using A = std::decay_t<decltype(v.first)>;
    using B = std::decay_t<decltype(v.second)>;
    constexpr size_t NA = bit_size<A>();
    constexpr size_t NB = bit_size<B>();
    constexpr size_t N = NA + NB;
    bits<N> lo = op_zext<NA, N>(pack_bits(v.first));
    bits<N> hi = bv_shl_amt(op_zext<NB, N>(pack_bits(v.second)), NA);
    return bv_or(lo, hi);
  }
}

template <typename T>
inline T unpack_bits(bits<bit_size<T>()> b) {
  if constexpr (std::is_same_v<T, bool>) {
    return (b.data & 1ULL) != 0ULL;
  } else if constexpr (ty_traits<T>::is_fval) {
    return T{b};
  } else if constexpr (ty_traits<T>::is_bits) {
    return b;
  } else {
    using A = std::decay_t<decltype(std::declval<T>().first)>;
    using B = std::decay_t<decltype(std::declval<T>().second)>;
    constexpr size_t NA = bit_size<A>();
    constexpr size_t NB = bit_size<B>();
    constexpr size_t N = NA + NB;
    A a = unpack_bits<A>(op_trunc<N, NA>(b));
    B bval = unpack_bits<B>(op_trunc<N, NB>(bv_lshr_amt(b, NA)));
    return T{std::move(a), std::move(bval)};
  }
}

// ============================================================================
// Memory model
//   Default: sparse paged byte map; unmapped read/write is TQBE_UB.
//   Opt-in `-DTQBE_NATIVE_MEM`: direct host-pointer load/store via std::memcpy
//   for apples-to-apples C3b (`PrintCpp` -> `clang++ -O3`) benchmarking.
// ============================================================================

#if defined(TQBE_NATIVE_MEM) && TQBE_NATIVE_MEM

class Mem {
 public:
  void alloc(uint64_t base, uint64_t len, uint8_t init = 0) {
    if (len > 0) {
      std::memset(reinterpret_cast<void*>(static_cast<uintptr_t>(base)), init, len);
    }
  }

  void map_bytes(uint64_t base, const uint8_t* src, size_t len) {
    if (len > 0) {
      std::memcpy(reinterpret_cast<void*>(static_cast<uintptr_t>(base)), src, len);
    }
  }

  void map_byte(uint64_t addr, uint8_t v = 0) {
    *reinterpret_cast<uint8_t*>(static_cast<uintptr_t>(addr)) = v;
  }

  uint8_t read_byte(uint64_t addr) const {
    return *reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(addr));
  }

  void write_byte(uint64_t addr, uint8_t v) {
    *reinterpret_cast<uint8_t*>(static_cast<uintptr_t>(addr)) = v;
  }

  bool is_mapped(uint64_t) const { return true; }

  template <typename T>
  void init_val(uint64_t base, const T& val) {
    constexpr size_t B = byte_size<T>();
    if constexpr (B > 0) {
      auto* dst = reinterpret_cast<uint8_t*>(static_cast<uintptr_t>(base));
      bits<bit_size<T>()> pk = pack_bits(val);
      if constexpr (bit_size<T>() <= 64) {
        std::memcpy(dst, &pk.data, B);
      } else {
        std::memcpy(dst, pk.data.data(), B);
      }
    }
  }
};

template <typename T>
inline T load(Mem&, bits<64> addr) {
  constexpr size_t N = bit_size<T>();
  constexpr size_t B = byte_size<T>();
  const auto* ptr = reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(addr.data));
  if constexpr (std::is_same_v<T, bool>) {
    uint8_t b0 = *ptr;
    if (b0 > 1) TQBE_UB("load invalid bool byte");
    return b0 != 0;
  } else if constexpr (N == 0) {
    return unpack_bits<T>(bits<0>{});
  } else if constexpr (N <= 64) {
    uint64_t acc = 0;
    std::memcpy(&acc, ptr, B);
    return unpack_bits<T>(bits<N>(acc));
  } else {
    bits<N> acc{};
    std::memcpy(acc.data.data(), ptr, B);
    acc.normalize();
    return unpack_bits<T>(acc);
  }
}

template <typename T>
inline void store(Mem&, bits<64> addr, const T& val) {
  constexpr size_t N = bit_size<T>();
  constexpr size_t B = byte_size<T>();
  if constexpr (N == 0) {
    (void)addr;
    (void)val;
    return;
  } else {
    auto* ptr = reinterpret_cast<uint8_t*>(static_cast<uintptr_t>(addr.data));
    bits<N> pk = pack_bits(val);
    if constexpr (N <= 64) {
      std::memcpy(ptr, &pk.data, B);
    } else {
      std::memcpy(ptr, pk.data.data(), B);
    }
  }
}

#else

class Mem {
 public:
  static constexpr uint64_t PAGE_SHIFT = 12;
  static constexpr uint64_t PAGE_SIZE = 1ULL << PAGE_SHIFT;
  static constexpr uint64_t PAGE_MASK = PAGE_SIZE - 1ULL;

  struct Page {
    std::array<uint8_t, PAGE_SIZE> bytes{};
    std::array<uint64_t, PAGE_SIZE / 64> valid{};
  };

  void alloc(uint64_t base, uint64_t len, uint8_t init = 0) {
    for (uint64_t i = 0; i < len; ++i) {
      map_byte(base + i, init);
    }
  }

  void map_bytes(uint64_t base, const uint8_t* src, size_t len) {
    for (size_t i = 0; i < len; ++i) {
      map_byte(base + i, src[i]);
    }
  }

  void map_byte(uint64_t addr, uint8_t v = 0) {
    Page& p = pages_[addr >> PAGE_SHIFT];
    uint64_t off = addr & PAGE_MASK;
    p.bytes[off] = v;
    p.valid[off >> 6] |= (1ULL << (off & 63ULL));
  }

  uint8_t read_byte(uint64_t addr) const {
    auto it = pages_.find(addr >> PAGE_SHIFT);
    if (it == pages_.end()) TQBE_UB("load from unmapped page");
    uint64_t off = addr & PAGE_MASK;
    if (((it->second.valid[off >> 6] >> (off & 63ULL)) & 1ULL) == 0ULL) {
      TQBE_UB("load from unmapped byte");
    }
    return it->second.bytes[off];
  }

  void write_byte(uint64_t addr, uint8_t v) {
    auto it = pages_.find(addr >> PAGE_SHIFT);
    if (it == pages_.end()) TQBE_UB("store to unmapped page");
    uint64_t off = addr & PAGE_MASK;
    if (((it->second.valid[off >> 6] >> (off & 63ULL)) & 1ULL) == 0ULL) {
      TQBE_UB("store to unmapped byte");
    }
    it->second.bytes[off] = v;
  }

  bool is_mapped(uint64_t addr) const {
    auto it = pages_.find(addr >> PAGE_SHIFT);
    if (it == pages_.end()) return false;
    uint64_t off = addr & PAGE_MASK;
    return ((it->second.valid[off >> 6] >> (off & 63ULL)) & 1ULL) != 0ULL;
  }

  template <typename T>
  void init_val(uint64_t base, const T& val) {
    constexpr size_t B = byte_size<T>();
    bits<bit_size<T>()> pk = pack_bits(val);
    for (size_t i = 0; i < B; ++i) {
      uint8_t byte_val = static_cast<uint8_t>((pk.word(i / 8) >> ((i % 8) * 8)) & 0xFFULL);
      map_byte(base + i, byte_val);
    }
  }

 private:
  std::unordered_map<uint64_t, Page> pages_;
};

template <typename T>
inline T load(Mem& mem, bits<64> addr) {
  constexpr size_t N = bit_size<T>();
  constexpr size_t B = byte_size<T>();
  uint64_t a = addr.data;
  if constexpr (std::is_same_v<T, bool>) {
    uint8_t b0 = mem.read_byte(a);
    if (b0 > 1) TQBE_UB("load invalid bool byte");
    return b0 != 0;
  } else if constexpr (N == 0) {
    return unpack_bits<T>(bits<0>{});
  } else if constexpr (N <= 64) {
    uint64_t acc = 0;
    for (size_t i = 0; i < B; ++i) {
      acc |= (static_cast<uint64_t>(mem.read_byte(a + i)) << (i * 8));
    }
    return unpack_bits<T>(bits<N>(acc));
  } else {
    bits<N> acc{};
    for (size_t i = 0; i < B; ++i) {
      uint64_t byte_v = static_cast<uint64_t>(mem.read_byte(a + i));
      acc.data[i / 8] |= (byte_v << ((i % 8) * 8));
    }
    acc.normalize();
    return unpack_bits<T>(acc);
  }
}

template <typename T>
inline void store(Mem& mem, bits<64> addr, const T& val) {
  constexpr size_t N = bit_size<T>();
  constexpr size_t B = byte_size<T>();
  uint64_t a = addr.data;
  if constexpr (N == 0) {
    (void)val;
    return;
  } else {
    bits<N> pk = pack_bits(val);
    for (size_t i = 0; i < B; ++i) {
      if (!mem.is_mapped(a + i)) TQBE_UB("store to unmapped byte");
    }
    for (size_t i = 0; i < B; ++i) {
      uint8_t byte_v =
          static_cast<uint8_t>((pk.word(i / 8) >> ((i % 8) * 8)) & 0xFFULL);
      mem.write_byte(a + i, byte_v);
    }
  }
}

#endif  // TQBE_NATIVE_MEM

// ============================================================================
// Integer & tree-lifted arithmetic / bitwise / comparison ops (matching Ops.lean)
// ============================================================================

template <typename T>
inline T op_copy(const T& a) {
  return a;
}

template <typename T>
inline T op_add(const T& a, const T& b) {
  if constexpr (has_float<T>()) {
    (void)a; (void)b; TQBE_UB("add on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    return a != b;
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_add(a, b);
  } else {
    return T{op_add(a.first, b.first), op_add(a.second, b.second)};
  }
}

template <typename T>
inline T op_sub(const T& a, const T& b) {
  if constexpr (has_float<T>()) {
    (void)a; (void)b; TQBE_UB("sub on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    return a != b;
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_sub(a, b);
  } else {
    return T{op_sub(a.first, b.first), op_sub(a.second, b.second)};
  }
}

template <typename T>
inline T op_mul(const T& a, const T& b) {
  if constexpr (has_float<T>()) {
    (void)a; (void)b; TQBE_UB("mul on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    return a && b;
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_mul(a, b);
  } else {
    return T{op_mul(a.first, b.first), op_mul(a.second, b.second)};
  }
}

template <typename T>
inline T op_neg(const T& a) {
  if constexpr (has_float<T>()) {
    (void)a; TQBE_UB("neg on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    return a;
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_neg(a);
  } else {
    return T{op_neg(a.first), op_neg(a.second)};
  }
}

template <typename T>
inline T op_and(const T& a, const T& b) {
  if constexpr (std::is_same_v<T, bool>) {
    return a && b;
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_and(a, b);
  } else if constexpr (ty_traits<T>::is_fval) {
    return T{bv_and(a.raw, b.raw)};
  } else {
    return T{op_and(a.first, b.first), op_and(a.second, b.second)};
  }
}

template <typename T>
inline T op_or(const T& a, const T& b) {
  if constexpr (std::is_same_v<T, bool>) {
    return a || b;
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_or(a, b);
  } else if constexpr (ty_traits<T>::is_fval) {
    return T{bv_or(a.raw, b.raw)};
  } else {
    return T{op_or(a.first, b.first), op_or(a.second, b.second)};
  }
}

template <typename T>
inline T op_xor(const T& a, const T& b) {
  if constexpr (std::is_same_v<T, bool>) {
    return a != b;
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_xor(a, b);
  } else if constexpr (ty_traits<T>::is_fval) {
    return T{bv_xor(a.raw, b.raw)};
  } else {
    return T{op_xor(a.first, b.first), op_xor(a.second, b.second)};
  }
}

template <typename T>
inline T op_not(const T& a) {
  if constexpr (std::is_same_v<T, bool>) {
    return !a;
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_not(a);
  } else if constexpr (ty_traits<T>::is_fval) {
    return T{bv_not(a.raw)};
  } else {
    return T{op_not(a.first), op_not(a.second)};
  }
}

template <typename T>
inline T op_ternlog(const T& a, const T& b, const T& c, uint8_t imm) {
  if constexpr (std::is_same_v<T, bool>) {
    unsigned idx = (a ? 4U : 0U) | (b ? 2U : 0U) | (c ? 1U : 0U);
    return ((imm >> idx) & 1U) != 0;
  } else if constexpr (ty_traits<T>::is_bits) {
    bits<T::width> acc{};
    for (unsigned k = 0; k < 8U; ++k) {
      if (((imm >> k) & 1U) == 0) continue;
      bits<T::width> pa = ((k >> 2) & 1U) ? a : bv_not(a);
      bits<T::width> pb = ((k >> 1) & 1U) ? b : bv_not(b);
      bits<T::width> pc = (k & 1U) ? c : bv_not(c);
      acc = bv_or(acc, bv_and(pa, bv_and(pb, pc)));
    }
    return acc;
  } else if constexpr (ty_traits<T>::is_fval) {
    return T{op_ternlog(a.raw, b.raw, c.raw, imm)};
  } else {
    return T{op_ternlog(a.first, b.first, c.first, imm),
             op_ternlog(a.second, b.second, c.second, imm)};
  }
}

template <typename T>
inline T op_shl(const T& a, const T& s) {
  if constexpr (has_float<T>()) {
    (void)a; (void)s; TQBE_UB("shl on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    (void)s; return a;
  } else if constexpr (ty_traits<T>::is_bits) {
    if constexpr (T::width == 0) return a;
    else return bv_shl_amt(a, bv_mod_u64(s, T::width));
  } else {
    return T{op_shl(a.first, s.first), op_shl(a.second, s.second)};
  }
}

template <typename T>
inline T op_lshr(const T& a, const T& s) {
  if constexpr (has_float<T>()) {
    (void)a; (void)s; TQBE_UB("lshr on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    (void)s; return a;
  } else if constexpr (ty_traits<T>::is_bits) {
    if constexpr (T::width == 0) return a;
    else return bv_lshr_amt(a, bv_mod_u64(s, T::width));
  } else {
    return T{op_lshr(a.first, s.first), op_lshr(a.second, s.second)};
  }
}

template <typename T>
inline T op_ashr(const T& a, const T& s) {
  if constexpr (has_float<T>()) {
    (void)a; (void)s; TQBE_UB("ashr on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    (void)s; return a;
  } else if constexpr (ty_traits<T>::is_bits) {
    if constexpr (T::width == 0) return a;
    else return bv_ashr_amt(a, bv_mod_u64(s, T::width));
  } else {
    return T{op_ashr(a.first, s.first), op_ashr(a.second, s.second)};
  }
}

template <typename T>
inline T op_rotl(const T& a, const T& s) {
  if constexpr (has_float<T>()) {
    (void)a; (void)s; TQBE_UB("rotl on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    (void)s; return a;
  } else if constexpr (ty_traits<T>::is_bits) {
    if constexpr (T::width <= 1) { (void)s; return a; }
    else return bv_rotl_amt(a, bv_mod_u64(s, T::width));
  } else {
    return T{op_rotl(a.first, s.first), op_rotl(a.second, s.second)};
  }
}

template <typename T>
inline T op_rotr(const T& a, const T& s) {
  if constexpr (has_float<T>()) {
    (void)a; (void)s; TQBE_UB("rotr on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    (void)s; return a;
  } else if constexpr (ty_traits<T>::is_bits) {
    if constexpr (T::width <= 1) { (void)s; return a; }
    else return bv_rotr_amt(a, bv_mod_u64(s, T::width));
  } else {
    return T{op_rotr(a.first, s.first), op_rotr(a.second, s.second)};
  }
}

template <size_t N>
inline bits<N> op_fshl(bits<N> a, bits<N> b, bits<N> c) {
  if constexpr (N == 0) {
    (void)a; (void)b; (void)c;
    return {};
  } else {
    uint64_t k = bv_mod_u64(c, N);
    if (k == 0) return a;
    return bv_or(bv_shl_amt(a, k), bv_lshr_amt(b, N - k));
  }
}

template <size_t N>
inline bits<N> op_fshr(bits<N> a, bits<N> b, bits<N> c) {
  if constexpr (N == 0) {
    (void)a; (void)b; (void)c;
    return {};
  } else {
    uint64_t k = bv_mod_u64(c, N);
    if (k == 0) return b;
    return bv_or(bv_shl_amt(a, N - k), bv_lshr_amt(b, k));
  }
}

template <CmpOp Op, typename T>
inline mask_t<T> op_cmp(const T& a, const T& b) {
  if constexpr (has_float<T>()) {
    (void)a; (void)b; TQBE_UB("int cmp on float ty");
  } else if constexpr (std::is_same_v<T, bool>) {
    return bool_cmp<Op>(a, b);
  } else if constexpr (ty_traits<T>::is_bits) {
    return bv_cmp<Op>(a, b);
  } else {
    return mask_t<T>{op_cmp<Op>(a.first, b.first), op_cmp<Op>(a.second, b.second)};
  }
}

template <typename T>
inline T op_select(bool c, const T& a, const T& b) {
  return c ? a : b;
}

template <typename T>
inline T op_blend(const mask_t<T>& m, const T& a, const T& b) {
  if constexpr (ty_traits<T>::is_pair) {
    return T{op_blend(m.first, a.first, b.first),
             op_blend(m.second, a.second, b.second)};
  } else {
    return m ? a : b;
  }
}

template <typename T>
inline T op_bswap(const T& a) {
  if constexpr (!bswap_ok<T>()) {
    (void)a; TQBE_UB("bswap on invalid ty");
  } else if constexpr (ty_traits<T>::is_pair) {
    return T{op_bswap(a.first), op_bswap(a.second)};
  } else if constexpr (T::width == 0) {
    return a;
  } else {
    constexpr size_t B = T::width / 8;
    bits<T::width> out{};
    for (size_t i = 0; i < B; ++i) {
      uint64_t byte_v = (a.word(i / 8) >> ((i % 8) * 8)) & 0xFFULL;
      size_t j = B - 1 - i;
      if constexpr (T::width <= 64) {
        out.data |= (byte_v << ((j % 8) * 8));
      } else {
        out.data[j / 8] |= (byte_v << ((j % 8) * 8));
      }
    }
    out.normalize();
    return out;
  }
}

template <typename Dst, typename Src>
inline Dst op_bitcast(const Src& a) {
  static_assert(bit_size<Dst>() == bit_size<Src>(), "bitcast width mismatch");
  return unpack_bits<Dst>(pack_bits(a));
}

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
  uint32_t u32 = s32 | (static_cast<uint32_t>(exp + 127) << 23) | static_cast<uint32_t>(m24 & 0x7FFFFFULL);
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
    return fval<Fmt::q>{bits<128>::from_words({0ULL, (p_sign ? 0xFFFF000000000000ULL : 0x7FFF000000000000ULL)})};
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
      return fval<Fmt::q>{bits<128>::from_words({0ULL, (p_sign ? 0xFFFF000000000000ULL : 0x7FFF000000000000ULL)})};
    }
    if (be <= 0) {
      int sh = 1 - be;
      if (sh >= 115) return fval<Fmt::q>{bits<128>::from_words({0ULL, p_sign ? (1ULL << 63) : 0ULL})};
      bits<128> sub = bv_lshr_amt(sig, static_cast<uint64_t>(sh));
      sub.set_bit(112, false);
      return fval<Fmt::q>{bits<128>::from_words({sub.data[0], (p_sign ? (1ULL << 63) : 0ULL) | sub.data[1]})};
    }
    sig.set_bit(112, false);
    return fval<Fmt::q>{bits<128>::from_words({sig.data[0], (p_sign ? (1ULL << 63) : 0ULL) | (static_cast<uint64_t>(be) << 48) | sig.data[1]})};
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
    return fval<Fmt::q>{bits<128>::from_words({0ULL, (res_sign ? 0xFFFF000000000000ULL : 0x7FFF000000000000ULL)})};
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
      bits<512> mask_rem = bv_sub(bv_shl_amt(bits<512>(1ULL), static_cast<uint64_t>(shift_needed - 1)), bits<512>(1ULL));
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
        return fval<Fmt::q>{bits<128>::from_words({0ULL, (res_sign ? 0xFFFF000000000000ULL : 0x7FFF000000000000ULL)})};
      }
    }
  }
  sig.set_bit(112, false);
  return fval<Fmt::q>{bits<128>::from_words({sig.data[0], (res_sign ? (1ULL << 63) : 0ULL) | (static_cast<uint64_t>(be) << 48) | sig.data[1]})};
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
