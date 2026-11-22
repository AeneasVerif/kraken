#ifndef LEANQBE_TEST_KISSAT_CHECK_C3B_INVARIANTS_HPP
#define LEANQBE_TEST_KISSAT_CHECK_C3B_INVARIANTS_HPP

// Opt-in structural invariant checker for C3b Kissat FullHdr solver states.
// Compile with -DKISSAT_C3B_CHECK_INV to enable runtime checks; when omitted,
// all hooks compile away to trivial inline no-ops with zero runtime overhead.

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

namespace kissat_c3b_inv {

enum FullHdrWord : uint64_t {
  W_ARENA_CAP = 4,
  W_WCAP = 5,
  W_ARENA_LEN = 6,
  W_WLEN = 7,
  W_VALUES = 8,
  W_LEVEL = 10,
  W_WATCH_VEC = 13,
  W_ARENA = 14,
  W_WATCH_STK = 15,
  W_TRAIL_END = 18,
  W_PROPAGATED = 19,
  W_CUR_LEVEL = 20,
  W_SCORE = 27,
  W_REL_WAIT = 38,
  W_PROBING = 65,
  W_SEARCH_TICKS = 75,
  W_Q_CUR_STAMP = 80,
  W_EMA_FAST_B = 91,
  W_EMA_FAST_E = 92,
  W_EMA_SLOW_B = 93,
  W_EMA_SLOW_E = 94,
  W_OOM = 95,
  W_MAX_VARS = 96,
  W_CUR_VARS = 97,
  W_FLAGS = 100,
  W_EXT_CAP = 113,
  W_EXT_LEN = 114,
  W_SCRATCH_BUF = 115,
  W_SCRATCH_CAP = 116,
  W_DENSE_MODE = 127,
  W_INCONSISTENT = 128,
};

struct ProbeIsoSnapshot {
#ifdef KISSAT_C3B_CHECK_INV
  uint64_t cur_vars = 0;
  uint64_t search_ticks = 0;
  uint64_t q_cur_stamp = 0;
  uint64_t ema_fast_biased = 0;
  uint64_t ema_fast_exp = 0;
  uint64_t ema_slow_biased = 0;
  uint64_t ema_slow_exp = 0;
  uint64_t rel_wait = 0;
  std::vector<uint64_t> scores;
  bool valid = false;
#else
  uint8_t unused = 0;
#endif
};

#ifndef KISSAT_C3B_CHECK_INV

inline bool check_2wl(const void*, std::string* = nullptr) { return true; }
inline bool check_bins(const void*, std::string* = nullptr) { return true; }
inline bool check_kitten(const void*, std::string* = nullptr) { return true; }

template <typename MemT>
inline bool check_2wl(const MemT&, uint64_t, std::string* = nullptr) {
  return true;
}

template <typename MemT>
inline bool check_bins(const MemT&, uint64_t, std::string* = nullptr) {
  return true;
}

template <typename MemT>
inline bool check_kitten(const MemT&, uint64_t, std::string* = nullptr) {
  return true;
}

inline ProbeIsoSnapshot check_probe_iso_begin(const void*) { return {}; }

template <typename MemT>
inline ProbeIsoSnapshot check_probe_iso_begin(const MemT&, uint64_t) {
  return {};
}

inline bool check_probe_iso_end(
    const void*, const ProbeIsoSnapshot&, std::string* = nullptr) {
  return true;
}

template <typename MemT>
inline bool check_probe_iso_end(
    const MemT&, uint64_t, const ProbeIsoSnapshot&, std::string* = nullptr) {
  return true;
}

inline bool check_probe_iso(
    const ProbeIsoSnapshot&, const void*, std::string* = nullptr) {
  return true;
}

template <typename MemT>
inline bool check_probe_iso(
    const ProbeIsoSnapshot&, const MemT&, uint64_t, std::string* = nullptr) {
  return true;
}

#else

namespace detail {

inline constexpr uint32_t kPhGarb = 0x00080000u;
inline constexpr uint32_t kPhShrk = 0x00800000u;
inline constexpr uint32_t kPwBinFlag = 0x80000000u;
inline constexpr uint32_t kPwLitMask = 0x7FFFFFFFu;

inline constexpr uint32_t kBase = 256u;
inline constexpr uint32_t kMaxV = 128u;
inline constexpr uint32_t kMaxOrig = 512u;
inline constexpr uint32_t kMaxCl = 896u;
inline constexpr uint32_t kArenaOff = 8608u;

struct HostView {
  template <typename T>
  T load(uint64_t addr) const {
    T val{};
    std::memcpy(&val, reinterpret_cast<const void*>(static_cast<uintptr_t>(addr)), sizeof(T));
    return val;
  }
};

template <typename MemT>
struct MemView {
  const MemT& mem;
  template <typename T>
  T load(uint64_t addr) const {
    uint8_t buf[sizeof(T)]{};
    for (size_t i = 0; i < sizeof(T); ++i) {
      buf[i] = mem.read_byte(addr + i);
    }
    T val{};
    std::memcpy(&val, buf, sizeof(T));
    return val;
  }
};

template <typename View>
inline uint64_t rd_word(const View& v, uint64_t hdr, FullHdrWord w) {
  return v.template load<uint64_t>(hdr + static_cast<uint64_t>(w) * 8ULL);
}

template <typename View>
inline uint32_t rd_u32(const View& v, uint64_t base, uint64_t idx) {
  return v.template load<uint32_t>(base + idx * 4ULL);
}

inline bool fail(std::string* err, const std::string& msg) {
  if (err) *err = msg;
  return false;
}

template <typename View>
inline uint64_t arena_step(const View& v, uint64_t arena, uint64_t len, uint64_t p) {
  uint32_t hdr = rd_u32(v, arena, p);
  uint32_t sz = rd_u32(v, arena, p + 2ULL);
  uint64_t q = p + 3ULL + static_cast<uint64_t>(sz);
  if ((hdr & kPhShrk) != 0u) {
    while (q < len && rd_u32(v, arena, q) != 0xFFFFFFFFu) {
      ++q;
    }
    if (q < len) ++q;
  }
  return q <= len ? q : len;
}

template <typename View>
inline bool check_2wl_impl(const View& v, uint64_t hdr, std::string* err) {
  uint64_t mv = rd_word(v, hdr, W_MAX_VARS);
  uint64_t cv = rd_word(v, hdr, W_CUR_VARS);
  uint64_t acap = rd_word(v, hdr, W_ARENA_CAP);
  uint64_t alen = rd_word(v, hdr, W_ARENA_LEN);
  uint64_t wcap = rd_word(v, hdr, W_WCAP);
  uint64_t wlen = rd_word(v, hdr, W_WLEN);
  uint64_t trl_end = rd_word(v, hdr, W_TRAIL_END);
  uint64_t prop = rd_word(v, hdr, W_PROPAGATED);
  uint64_t cur_lvl = rd_word(v, hdr, W_CUR_LEVEL);
  uint64_t vals_ptr = rd_word(v, hdr, W_VALUES);
  uint64_t lvl_ptr = rd_word(v, hdr, W_LEVEL);
  bool check_val_lvl = (prop == trl_end && vals_ptr != 0ULL && lvl_ptr != 0ULL &&
                        rd_word(v, hdr, W_INCONSISTENT) == 0ULL &&
                        rd_word(v, hdr, W_OOM) == 0ULL);
  if (cv > mv) return fail(err, "cur_vars > max_vars");
  if (alen > acap || wlen > wcap) return fail(err, "arena/watch len exceeds cap");
  if (trl_end > cv) return fail(err, "trail_end > cur_vars");
  if (prop > trl_end) return fail(err, "propagated > trail_end");
  if (cur_lvl > mv) return fail(err, "cur_level > max_vars");
  if (rd_word(v, hdr, W_DENSE_MODE) != 0ULL) return true;

  uint64_t wvec = rd_word(v, hdr, W_WATCH_VEC);
  uint64_t wstk = rd_word(v, hdr, W_WATCH_STK);
  uint64_t arena = rd_word(v, hdr, W_ARENA);
  if (wvec == 0 || wstk == 0 || arena == 0) return fail(err, "null 2WL buffers");
  uint64_t nlits = cv * 2ULL;

  std::vector<uint8_t> watch_mask(alen, 0);
  std::vector<uint32_t> blk0(check_val_lvl ? alen : 0ULL, 0xFFFFFFFFu);
  std::vector<uint32_t> blk1(check_val_lvl ? alen : 0ULL, 0xFFFFFFFFu);
  for (uint64_t l = 0; l < nlits; ++l) {
    uint64_t off = rd_u32(v, wvec, l * 2ULL);
    uint64_t sz = rd_u32(v, wvec, l * 2ULL + 1ULL);
    if (sz == 0) continue;
    if (off == 0 || off + sz > wlen || off + sz > wcap) {
      return fail(err, "watch slice out of bounds at lit " + std::to_string(l));
    }
    uint64_t k = 0;
    while (k < sz) {
      uint32_t w0 = rd_u32(v, wstk, off + k);
      if (w0 == 0xFFFFFFFFu) return fail(err, "free sentinel inside active watch slice");
      if ((w0 & kPwBinFlag) != 0u) {
        uint32_t ot = w0 & kPwLitMask;
        if (ot >= nlits || ot == l || ot == (l ^ 1ULL)) {
          return fail(err, "invalid binary watch lit " + std::to_string(l));
        }
        k += 1;
        continue;
      }
      if (k + 1 >= sz) return fail(err, "truncated large watch at lit " + std::to_string(l));
      uint32_t blk = w0 & kPwLitMask;
      uint32_t cr = rd_u32(v, wstk, off + k + 1);
      if (blk >= nlits) return fail(err, "invalid blocker lit");
      if (static_cast<uint64_t>(cr) + 3ULL > alen) {
        return fail(err, "watch cref past arena_len");
      }
      uint32_t chdr = rd_u32(v, arena, cr);
      uint32_t csz = rd_u32(v, arena, cr + 2ULL);
      if ((chdr & kPhGarb) != 0u || csz < 3u || static_cast<uint64_t>(cr) + 3ULL + csz > alen) {
        return fail(err, "watch points to garbage or invalid clause");
      }
      uint32_t l0 = rd_u32(v, arena, cr + 3ULL);
      uint32_t l1 = rd_u32(v, arena, cr + 4ULL);
      uint8_t bit = (l == l0) ? 1u : ((l == l1) ? 2u : 0u);
      if (bit == 0u || (watch_mask[cr] & bit) != 0u) {
        return fail(err, "large watch mismatched/duplicate for cref " + std::to_string(cr));
      }
      watch_mask[cr] |= bit;
      if (check_val_lvl) {
        if (bit == 1u) blk0[cr] = blk;
        else blk1[cr] = blk;
      }
      k += 2;
    }
  }

  for (uint64_t p = 0; p + 3ULL <= alen;) {
    uint32_t chdr = rd_u32(v, arena, p);
    uint32_t csz = rd_u32(v, arena, p + 2ULL);
    if ((chdr & kPhGarb) == 0u && csz >= 3u) {
      if (p + 3ULL + csz > alen) return fail(err, "clause extends past arena_len");
      uint32_t l0 = rd_u32(v, arena, p + 3ULL);
      uint32_t l1 = rd_u32(v, arena, p + 4ULL);
      if (l0 == l1 || l0 >= nlits || l1 >= nlits || watch_mask[p] != 3u) {
        return fail(err, "live large clause missing 2WL at cref " + std::to_string(p));
      }
      if (check_val_lvl) {
        int8_t v0 = v.template load<int8_t>(vals_ptr + static_cast<uint64_t>(l0));
        int8_t v1 = v.template load<int8_t>(vals_ptr + static_cast<uint64_t>(l1));
        auto chk_watch = [&](
            uint32_t w, int8_t vw, uint32_t o, int8_t vo, uint32_t blk) -> bool {
          if (vw >= 0) return true;
          uint32_t lw = rd_u32(v, lvl_ptr, static_cast<uint64_t>(w >> 1));
          uint32_t lo = rd_u32(v, lvl_ptr, static_cast<uint64_t>(o >> 1));
          if (lw > cur_lvl) return fail(err, "watch level exceeds cur_level");
          if (vo > 0 && lo <= lw) return true;
          bool blk_sat = false;
          bool bad_nw = false;
          for (uint32_t k = 2; k < csz; ++k) {
            uint32_t lk = rd_u32(v, arena, p + 3ULL + static_cast<uint64_t>(k));
            if (lk >= nlits) return fail(err, "clause literal out of range");
            int8_t vk = v.template load<int8_t>(vals_ptr + static_cast<uint64_t>(lk));
            uint32_t llk = rd_u32(v, lvl_ptr, static_cast<uint64_t>(lk >> 1));
            if (lk == blk && vk > 0 && llk <= lw) blk_sat = true;
            if (vk >= 0 || llk > lw) bad_nw = true;
          }
          if (bad_nw && !blk_sat) {
            return fail(err, "2WL value/level violation at cref " + std::to_string(p));
          }
          return true;
        };
        if (!chk_watch(l0, v0, l1, v1, blk0[p]) || !chk_watch(l1, v1, l0, v0, blk1[p])) {
          return false;
        }
      }
    }
    uint64_t np = arena_step(v, arena, alen, p);
    if (np <= p) return fail(err, "non-advancing arena step");
    p = np;
  }
  return true;
}

template <typename View>
inline bool check_bins_impl(const View& v, uint64_t hdr, std::string* err) {
  uint64_t cv = rd_word(v, hdr, W_CUR_VARS);
  uint64_t mv = rd_word(v, hdr, W_MAX_VARS);
  if (cv > mv) return fail(err, "cur_vars > max_vars");
  if (rd_word(v, hdr, W_DENSE_MODE) != 0ULL) return true;
  uint64_t wvec = rd_word(v, hdr, W_WATCH_VEC);
  uint64_t wstk = rd_word(v, hdr, W_WATCH_STK);
  uint64_t wlen = rd_word(v, hdr, W_WLEN);
  uint64_t wcap = rd_word(v, hdr, W_WCAP);
  if (wvec == 0 || wstk == 0) return fail(err, "null watch buffers in check_bins");
  uint64_t nlits = cv * 2ULL;

  std::vector<uint64_t> edges;
  for (uint64_t l = 0; l < nlits; ++l) {
    uint64_t off = rd_u32(v, wvec, l * 2ULL);
    uint64_t sz = rd_u32(v, wvec, l * 2ULL + 1ULL);
    if (sz == 0) continue;
    if (off == 0 || off + sz > wlen || off + sz > wcap) {
      return fail(err, "binary watch slice out of bounds");
    }
    for (uint64_t k = 0; k < sz;) {
      uint32_t w0 = rd_u32(v, wstk, off + k);
      if (w0 == 0xFFFFFFFFu) return fail(err, "sentinel in binary watch slice");
      if ((w0 & kPwBinFlag) == 0u) {
        if (k + 1 >= sz) return fail(err, "truncated large watch in check_bins");
        k += 2;
        continue;
      }
      uint32_t ot = w0 & kPwLitMask;
      if (ot >= nlits || ot == l || ot == (l ^ 1ULL)) {
        return fail(err, "invalid/tautological binary watch");
      }
      edges.push_back((l << 32) | static_cast<uint64_t>(ot));
      k += 1;
    }
  }
  std::vector<uint64_t> rev;
  rev.reserve(edges.size());
  for (uint64_t e : edges) {
    rev.push_back(((e & 0xFFFFFFFFULL) << 32) | (e >> 32));
  }
  std::sort(edges.begin(), edges.end());
  std::sort(rev.begin(), rev.end());
  if (edges != rev) {
    return fail(err, "asymmetric binary implication watch pair");
  }
  return true;
}

template <typename View>
inline bool check_kitten_impl(const View& v, uint64_t hdr, std::string* err) {
  uint64_t sbuf = rd_word(v, hdr, W_SCRATCH_BUF);
  uint64_t scap = rd_word(v, hdr, W_SCRATCH_CAP);
  if (sbuf == 0 || scap < kBase + kArenaOff) {
    return fail(err, "scratch_buf unallocated/too small for kitten");
  }
  uint64_t kbase = sbuf + static_cast<uint64_t>(kBase) * 4ULL;
  auto kr = [&](uint64_t off) { return rd_u32(v, kbase, off); };

  uint32_t nv = kr(0u);
  uint32_t nc = kr(1u);
  uint32_t orig_nc = kr(2u);
  uint32_t lvl = kr(3u);
  uint32_t prop = kr(4u);
  uint32_t trl_end = kr(5u);
  uint32_t unass = kr(6u);
  uint32_t qfirst = kr(10u);
  uint32_t qlast = kr(11u);
  uint32_t qsearch = kr(12u);
  uint32_t alen = kr(16u);
  uint32_t acap = kr(17u);
  uint32_t nassump = kr(18u);
  uint32_t nunits = kr(19u);

  if (nv > kMaxV || nc > kMaxCl || orig_nc > nc || orig_nc > kMaxOrig) {
    return fail(err, "kitten variable/clause count out of bounds");
  }
  if (trl_end > nv || prop > trl_end || lvl > trl_end ||
      static_cast<uint64_t>(unass) + static_cast<uint64_t>(trl_end) != static_cast<uint64_t>(nv)) {
    return fail(err, "kitten trail/level/unassigned mismatch");
  }
  if (alen > acap ||
      static_cast<uint64_t>(kBase) + static_cast<uint64_t>(kArenaOff) +
              static_cast<uint64_t>(acap) > scap ||
      nassump > nv || nunits > 256u) {
    return fail(err, "kitten arena/assump/units bounds invalid");
  }

  std::vector<uint8_t> on_trl(nv, 0);
  for (uint32_t i = 0; i < trl_end; ++i) {
    uint32_t lit = kr(672u + i);
    if (lit >= nv * 2u) return fail(err, "kitten trail literal out of range");
    uint32_t var = lit >> 1;
    if (on_trl[var]) return fail(err, "duplicate variable in kitten trail");
    on_trl[var] = 1;
    if (kr(928u + lit) != 1u || kr(928u + (lit ^ 1u)) != 2u || kr(32u + var) > lvl) {
      return fail(err, "kitten trail assignment value/level mismatch");
    }
  }
  for (uint32_t var = 0; var < nv; ++var) {
    if (!on_trl[var] && (kr(928u + var * 2u) != 0u || kr(928u + var * 2u + 1u) != 0u)) {
      return fail(err, "unassigned kitten variable has non-zero value");
    }
  }

  if (nv == 0u) {
    if (qfirst != 0xFFFFFFFFu || qlast != 0xFFFFFFFFu || qsearch != 0xFFFFFFFFu) {
      return fail(err, "non-empty kitten queue sentinels when nv == 0");
    }
  } else {
    if (qsearch >= nv) return fail(err, "kitten qsearch out of range");
    std::vector<uint8_t> seen(nv, 0);
    uint32_t cur = qfirst;
    uint32_t prev = 0xFFFFFFFFu;
    uint32_t cnt = 0;
    while (cur < nv && cnt <= nv) {
      if (seen[cur]) return fail(err, "cycle in kitten VMTF queue");
      if (kr(288u + cur) != prev) return fail(err, "kitten VMTF prev link broken");
      seen[cur] = 1;
      prev = cur;
      cur = kr(416u + cur);
      ++cnt;
    }
    if (cnt != nv || prev != qlast || cur != 0xFFFFFFFFu) {
      return fail(err, "kitten VMTF queue incomplete");
    }
  }

  for (uint32_t cid = 0; cid < nc; ++cid) {
    uint64_t off = static_cast<uint64_t>(kr(5920ULL + static_cast<uint64_t>(cid)));
    uint64_t sz = static_cast<uint64_t>(kr(6816ULL + static_cast<uint64_t>(cid)) & 0xFFFFu);
    if (off + sz > static_cast<uint64_t>(alen)) {
      return fail(err, "kitten clause exceeds arena_len");
    }
    for (uint64_t j = 0; j < sz; ++j) {
      uint64_t lit = static_cast<uint64_t>(kr(static_cast<uint64_t>(kArenaOff) + off + j));
      if (lit >= static_cast<uint64_t>(nv) * 2ULL) {
        return fail(err, "kitten clause literal out of bounds");
      }
    }
  }
  for (uint32_t lit = 0; lit < nv * 2u; ++lit) {
    uint32_t w = kr(2080u + lit);
    uint32_t steps = 0;
    while (w != 0xFFFFFFFFu) {
      if (w >= nc * 2u || steps >= nc * 2u) return fail(err, "corrupt kitten watch list");
      w = kr(2336u + w);
      ++steps;
    }
  }
  return true;
}

template <typename View>
inline ProbeIsoSnapshot probe_iso_begin_impl(const View& v, uint64_t hdr) {
  ProbeIsoSnapshot snap;
  snap.cur_vars = rd_word(v, hdr, W_CUR_VARS);
  snap.search_ticks = rd_word(v, hdr, W_SEARCH_TICKS);
  snap.q_cur_stamp = rd_word(v, hdr, W_Q_CUR_STAMP);
  snap.ema_fast_biased = rd_word(v, hdr, W_EMA_FAST_B);
  snap.ema_fast_exp = rd_word(v, hdr, W_EMA_FAST_E);
  snap.ema_slow_biased = rd_word(v, hdr, W_EMA_SLOW_B);
  snap.ema_slow_exp = rd_word(v, hdr, W_EMA_SLOW_E);
  snap.rel_wait = rd_word(v, hdr, W_REL_WAIT);
  uint64_t score_ptr = rd_word(v, hdr, W_SCORE);
  if (score_ptr != 0ULL) {
    snap.scores.resize(snap.cur_vars);
    for (uint64_t i = 0; i < snap.cur_vars; ++i) {
      snap.scores[i] = v.template load<uint64_t>(score_ptr + i * 8ULL);
    }
  }
  snap.valid = true;
  return snap;
}

template <typename View>
inline bool probe_iso_end_impl(
    const View& v, uint64_t hdr, const ProbeIsoSnapshot& snap, std::string* err) {
  if (!snap.valid) return fail(err, "uninitialized ProbeIsoSnapshot");
  if (rd_word(v, hdr, W_SEARCH_TICKS) != snap.search_ticks) {
    return fail(err, "probing modified search_ticks");
  }
  if (rd_word(v, hdr, W_Q_CUR_STAMP) != snap.q_cur_stamp) {
    return fail(err, "probing modified q_cur_stamp");
  }
  if (rd_word(v, hdr, W_EMA_FAST_B) != snap.ema_fast_biased ||
      rd_word(v, hdr, W_EMA_FAST_E) != snap.ema_fast_exp ||
      rd_word(v, hdr, W_EMA_SLOW_B) != snap.ema_slow_biased ||
      rd_word(v, hdr, W_EMA_SLOW_E) != snap.ema_slow_exp) {
    return fail(err, "probing modified EMA state");
  }
  if (rd_word(v, hdr, W_REL_WAIT) != snap.rel_wait) {
    return fail(err, "probing modified reluctant wait");
  }
  uint64_t cv = rd_word(v, hdr, W_CUR_VARS);
  uint64_t score_ptr = rd_word(v, hdr, W_SCORE);
  if (!snap.scores.empty() && score_ptr != 0ULL) {
    uint64_t n = cv < snap.scores.size() ? cv : snap.scores.size();
    for (uint64_t i = 0; i < n; ++i) {
      if (v.template load<uint64_t>(score_ptr + i * 8ULL) != snap.scores[i]) {
        return fail(err, "probing modified VSIDS score at var " + std::to_string(i));
      }
    }
  }
  return true;
}

}  // namespace detail

inline bool check_2wl(const void* hdr, std::string* err = nullptr) {
  return detail::check_2wl_impl(
      detail::HostView{}, static_cast<uint64_t>(reinterpret_cast<uintptr_t>(hdr)), err);
}

template <typename MemT>
inline bool check_2wl(const MemT& mem, uint64_t hdr_addr, std::string* err = nullptr) {
  return detail::check_2wl_impl(detail::MemView<MemT>{mem}, hdr_addr, err);
}

inline bool check_bins(const void* hdr, std::string* err = nullptr) {
  return detail::check_bins_impl(
      detail::HostView{}, static_cast<uint64_t>(reinterpret_cast<uintptr_t>(hdr)), err);
}

template <typename MemT>
inline bool check_bins(const MemT& mem, uint64_t hdr_addr, std::string* err = nullptr) {
  return detail::check_bins_impl(detail::MemView<MemT>{mem}, hdr_addr, err);
}

inline bool check_kitten(const void* hdr, std::string* err = nullptr) {
  return detail::check_kitten_impl(
      detail::HostView{}, static_cast<uint64_t>(reinterpret_cast<uintptr_t>(hdr)), err);
}

template <typename MemT>
inline bool check_kitten(const MemT& mem, uint64_t hdr_addr, std::string* err = nullptr) {
  return detail::check_kitten_impl(detail::MemView<MemT>{mem}, hdr_addr, err);
}

inline ProbeIsoSnapshot check_probe_iso_begin(const void* hdr) {
  return detail::probe_iso_begin_impl(
      detail::HostView{}, static_cast<uint64_t>(reinterpret_cast<uintptr_t>(hdr)));
}

template <typename MemT>
inline ProbeIsoSnapshot check_probe_iso_begin(const MemT& mem, uint64_t hdr_addr) {
  return detail::probe_iso_begin_impl(detail::MemView<MemT>{mem}, hdr_addr);
}

inline bool check_probe_iso_end(
    const void* hdr, const ProbeIsoSnapshot& snap, std::string* err = nullptr) {
  return detail::probe_iso_end_impl(
      detail::HostView{}, static_cast<uint64_t>(reinterpret_cast<uintptr_t>(hdr)), snap, err);
}

template <typename MemT>
inline bool check_probe_iso_end(
    const MemT& mem, uint64_t hdr_addr, const ProbeIsoSnapshot& snap, std::string* err = nullptr) {
  return detail::probe_iso_end_impl(detail::MemView<MemT>{mem}, hdr_addr, snap, err);
}

inline bool check_probe_iso(
    const ProbeIsoSnapshot& snap, const void* hdr, std::string* err = nullptr) {
  return check_probe_iso_end(hdr, snap, err);
}

template <typename MemT>
inline bool check_probe_iso(
    const ProbeIsoSnapshot& snap, const MemT& mem, uint64_t hdr_addr, std::string* err = nullptr) {
  return check_probe_iso_end(mem, hdr_addr, snap, err);
}

#endif  // KISSAT_C3B_CHECK_INV

}  // namespace kissat_c3b_inv

#endif
