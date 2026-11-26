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

} // namespace tqbe
