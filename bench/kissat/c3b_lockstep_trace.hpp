#ifndef BENCH_KISSAT_C3B_LOCKSTEP_TRACE_HPP
#define BENCH_KISSAT_C3B_LOCKSTEP_TRACE_HPP

// Opt-in diagnostic hook for PrintCpp C3b Kissat builds:
//   -DKISSAT_LOCKSTEP_TRACE : emit canonical sorted-DIMACS event trace to
//     getenv("KISSAT_LOCKSTEP_TRACE") (file path or "stderr"/"-").
//   -DKISSAT_EXTENDED_TELEM : collect §3 Layer 2 extended per-pass counters
//     into the unused h->delayed[0..31] u64 buffer (0 verified-proof churn).
// When neither macro is defined, all hooks compile away to empty inline no-ops.

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

namespace c3b_trace {

inline constexpr uint64_t kExtTelemMagic = 0x4B54454C4D303031ULL;  // "KTELM001"
inline constexpr uint64_t kExtTelemWords = 32ULL;

enum ExtSlot : size_t {
  EXT_MAGIC = 0,
  EXT_DECISIONS = 1,
  EXT_PROPAGATIONS = 2,
  EXT_CHRONO_BT_CNT = 3,
  EXT_KITTEN_CALLS = 4,
  EXT_KITTEN_TICKS = 5,
  EXT_BACKBONE_UNITS = 6,
  EXT_REDUCED_CLAUSES = 7,
  EXT_PROBE_TICKS = 8,
  EXT_PROBE_WALL_NS = 9,
  EXT_ELIM_TICKS = 10,
  EXT_ELIM_WALL_NS = 11,
  EXT_VIVIFY_TICKS = 12,
  EXT_VIVIFY_WALL_NS = 13,
  EXT_SWEEP_TICKS = 14,
  EXT_SWEEP_WALL_NS = 15,
  EXT_CONG_TICKS = 16,
  EXT_CONG_WALL_NS = 17,
  EXT_FACTOR_TICKS = 18,
  EXT_FACTOR_WALL_NS = 19,
  EXT_SUBST_WALL_NS = 20,
  EXT_TRANS_WALL_NS = 21,
  EXT_BACKBONE_WALL_NS = 22,
  EXT_FWD_SUB_WALL_NS = 23,
  EXT_COMPACT_CNT = 24,
  EXT_COMPACT_WALL_NS = 25,
  EXT_OTFS_SUBSUME = 26,
  EXT_RESTART_REUSE_LVLS = 27,
  EXT_STABLE_DECISIONS = 28,
  EXT_FOCUSED_DECISIONS = 29,
  EXT_PROBE_CALLS = 30,
  EXT_VIVIFY_CALLS = 31,
};

enum PassKind : int {
  PASS_NONE = 0,
  PASS_PROBE,
  PASS_ELIM,
  PASS_VIVIFY,
  PASS_SWEEP,
  PASS_CONG,
  PASS_FACTOR,
  PASS_SUBST,
  PASS_TRANS,
  PASS_BACKBONE,
  PASS_FWD,
  PASS_COMPACT,
};

namespace detail {

inline uint64_t rd64(uint64_t hdr_addr, size_t w) {
  uint64_t v = 0;
  if (hdr_addr) {
    std::memcpy(&v, reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(hdr_addr)) + w * 8ULL,
                8ULL);
  }
  return v;
}

inline uint32_t rd32_arr(uint64_t ptr_addr, size_t idx) {
  uint32_t v = 0;
  std::memcpy(&v, reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(ptr_addr)) + idx * 4ULL,
              4ULL);
  return v;
}

inline int8_t rd8_arr(uint64_t ptr_addr, size_t idx) {
  int8_t v = 0;
  std::memcpy(&v, reinterpret_cast<const uint8_t*>(static_cast<uintptr_t>(ptr_addr)) + idx, 1ULL);
  return v;
}

}  // namespace detail

#if defined(KISSAT_LOCKSTEP_TRACE) || defined(KISSAT_EXTENDED_TELEM)

struct State {
  bool is_full = true;
  uint64_t orig_mv = 0;
  uint64_t ext_len_seen = 0;
  std::vector<int32_t> dimacs_var;
  std::vector<uint8_t> unit0_emitted;
  const char* unit_src = nullptr;
  const char* inproc_src = nullptr;
  FILE* fp = nullptr;
  bool fp_init = false;
  uint64_t seq = 0;
  uint64_t counters[kExtTelemWords]{};
  uint64_t prop_depth = 0;
};

inline State& state() {
  static State s;
  return s;
}

inline void ensure_dimacs_init(uint64_t hdr_addr) {
  State& s = state();
  if (s.orig_mv != 0ULL) return;
  uint64_t mv = detail::rd64(hdr_addr, 0);
  if (mv == 0ULL) return;
  s.orig_mv = mv;
  s.dimacs_var.resize(static_cast<size_t>(mv));
  for (uint64_t v = 0; v < mv; ++v) {
    s.dimacs_var[static_cast<size_t>(v)] = static_cast<int32_t>(v + 1ULL);
  }
  s.unit0_emitted.assign(static_cast<size_t>(mv + 1ULL), 0);
}

inline void reset_state(uint64_t, bool is_full) {
  State& s = state();
  s.is_full = is_full;
  s.orig_mv = 0ULL;
  s.ext_len_seen = 0;
  s.dimacs_var.clear();
  s.unit0_emitted.clear();
  s.unit_src = nullptr;
  s.inproc_src = nullptr;
  s.seq = 0;
  std::memset(s.counters, 0, sizeof(s.counters));
  s.counters[EXT_MAGIC] = kExtTelemMagic;
  s.prop_depth = 0;
}

inline void flush_ext_telem(uint64_t hdr_addr) {
#ifdef KISSAT_EXTENDED_TELEM
  State& s = state();
  uint64_t delayed = detail::rd64(hdr_addr, 16);
  uint64_t dcap = detail::rd64(hdr_addr, 56);
  if (delayed && dcap >= 22ULL && s.is_full) {
    std::memcpy(reinterpret_cast<void*>(static_cast<uintptr_t>(delayed)), s.counters,
                sizeof(s.counters));
  }
#else
  (void)hdr_addr;
#endif
}

inline int32_t export_lit(uint32_t ilit) {
  const State& s = state();
  uint32_t v = ilit >> 1;
  int32_t ev = (v < s.dimacs_var.size()) ? s.dimacs_var[v]
                                         : static_cast<int32_t>(1000000000u + v);
  return (ilit & 1u) ? -ev : ev;
}

inline FILE* trace_fp() {
#ifdef KISSAT_LOCKSTEP_TRACE
  State& s = state();
  if (!s.fp_init) {
    s.fp_init = true;
    const char* p = std::getenv("KISSAT_LOCKSTEP_TRACE");
    if (p && p[0]) {
      if (std::strcmp(p, "stderr") == 0 || std::strcmp(p, "-") == 0) {
        s.fp = stderr;
      } else {
        s.fp = std::fopen(p, "w");
      }
    }
  }
  return s.fp;
#else
  return nullptr;
#endif
}

inline uint64_t fnv64_sorted_lits(const uint32_t* lits, size_t n) {
  std::vector<int32_t> buf(n);
  for (size_t i = 0; i < n; ++i) {
    buf[i] = export_lit(lits[i]);
  }
  std::sort(buf.begin(), buf.end());
  uint64_t h = 14695981039346656037ULL;
  for (size_t i = 0; i < n; ++i) {
    uint32_t x = static_cast<uint32_t>(buf[i]);
    for (int b = 0; b < 4; ++b) {
      h ^= (x >> (b * 8)) & 0xffu;
      h *= 1099511628211ULL;
    }
  }
  return h;
}

inline void sync_dimacs_after_compact(uint64_t hdr_addr) {
  State& s = state();
  if (!s.is_full) return;
  uint64_t ext_stk = detail::rd64(hdr_addr, 112);
  uint64_t ext_len = detail::rd64(hdr_addr, 114);
  if (!ext_stk || ext_len <= s.ext_len_seen) return;
  constexpr uint32_t kExtBlkFlag = 0x80000000u;
  constexpr uint32_t kExtCompactFlag = 0x40000000u;
  constexpr uint32_t kExtCntMask = 0x3FFFFFFFu;
  uint64_t p = s.ext_len_seen;
  while (p < ext_len) {
    uint32_t w = detail::rd32_arr(ext_stk, static_cast<size_t>(p));
    if ((w & kExtBlkFlag) != 0u && (w & kExtCompactFlag) != 0u) {
      uint64_t ncv = static_cast<uint64_t>(w & kExtCntMask);
      if (p + 1ULL + ncv <= ext_len) {
        std::vector<int32_t> next_map(static_cast<size_t>(ncv));
        for (uint64_t k = 0; k < ncv; ++k) {
          uint32_t ov = detail::rd32_arr(ext_stk, static_cast<size_t>(p + 1ULL + k));
          next_map[static_cast<size_t>(k)] =
              (ov < s.dimacs_var.size()) ? s.dimacs_var[ov]
                                         : static_cast<int32_t>(1000000000u + ov);
        }
        s.dimacs_var.swap(next_map);
        p += 1ULL + ncv;
        continue;
      }
    }
    ++p;
  }
  s.ext_len_seen = ext_len;
}

inline void emit_unit0_range(uint64_t hdr_addr, uint64_t te_begin, uint64_t te_end,
                             const char* fallback_src) {
  State& s = state();
  if (te_end <= te_begin) return;
  uint64_t trl = detail::rd64(hdr_addr, 12);
  uint64_t lvl = detail::rd64(hdr_addr, 10);
  uint64_t cv = s.is_full ? detail::rd64(hdr_addr, 97) : detail::rd64(hdr_addr, 0);
  const char* src = s.unit_src ? s.unit_src : (s.inproc_src ? s.inproc_src : fallback_src);
  FILE* fp = trace_fp();
  for (uint64_t i = te_begin; i < te_end; ++i) {
    uint32_t lit = detail::rd32_arr(trl, static_cast<size_t>(i));
    uint32_t v = lit >> 1;
    if (v >= cv || detail::rd32_arr(lvl, v) != 0u) continue;
    int32_t dlit = export_lit(lit);
    uint64_t dvar = static_cast<uint64_t>(dlit < 0 ? -dlit : dlit);
    bool fresh = true;
    if (dvar < 1000000000ULL) {
      if (dvar >= s.unit0_emitted.size()) s.unit0_emitted.resize(dvar + 1ULL, 0);
      if (s.unit0_emitted[dvar]) fresh = false;
      s.unit0_emitted[dvar] = 1;
    }
    if (fresh) {
      if (s.inproc_src && std::strcmp(s.inproc_src, "backbone") == 0) {
        s.counters[EXT_BACKBONE_UNITS]++;
      }
      if (fp) {
        std::fprintf(fp, "E %llu UNIT0 lit=%d src=%s\n",
                     static_cast<unsigned long long>(s.seq++), static_cast<int>(dlit), src);
      }
    }
  }
}

inline void on_parse_enter(uint64_t hdr_addr) {
  ensure_dimacs_init(hdr_addr);
}

inline void on_solve_enter(uint64_t hdr_addr, bool is_full) {
  reset_state(hdr_addr, is_full);
}

inline void on_init_exit(uint64_t hdr_addr, bool is_full) {
  reset_state(hdr_addr, is_full);
  ensure_dimacs_init(hdr_addr);
}

inline void on_solve_exit(uint64_t hdr_addr, uint64_t status) {
  uint64_t conflicts = detail::rd64(hdr_addr, 42);
  uint64_t ticks = detail::rd64(hdr_addr, 75);
  flush_ext_telem(hdr_addr);
#ifdef KISSAT_LOCKSTEP_TRACE
  State& s = state();
  FILE* fp = trace_fp();
  if (fp) {
    std::fprintf(fp, "E %llu END status=%llu conflicts=%llu decisions=%llu props=%llu ticks=%llu\n",
                 static_cast<unsigned long long>(s.seq++),
                 static_cast<unsigned long long>(status),
                 static_cast<unsigned long long>(conflicts),
                 static_cast<unsigned long long>(s.counters[EXT_DECISIONS]),
                 static_cast<unsigned long long>(s.counters[EXT_PROPAGATIONS]),
                 static_cast<unsigned long long>(ticks));
    std::fflush(fp);
    if (fp != stderr) std::fclose(fp);
    s.fp = nullptr;
    s.fp_init = false;
  }
#else
  (void)status;
  (void)conflicts;
  (void)ticks;
#endif
}

inline void on_decide_exit(uint64_t hdr_addr, uint64_t prev_te, uint64_t prev_lvl, uint64_t ret) {
  if (ret != 1ULL) return;
  uint64_t te = detail::rd64(hdr_addr, 18);
  uint64_t lvl = detail::rd64(hdr_addr, 20);
  if (te <= prev_te || lvl <= prev_lvl) return;
  State& s = state();
  s.counters[EXT_DECISIONS]++;
  uint64_t stable = detail::rd64(hdr_addr, 69);
  if (stable) s.counters[EXT_STABLE_DECISIONS]++;
  else s.counters[EXT_FOCUSED_DECISIONS]++;
#ifdef KISSAT_LOCKSTEP_TRACE
  FILE* fp = trace_fp();
  if (fp) {
    uint64_t trl = detail::rd64(hdr_addr, 12);
    uint32_t lit = detail::rd32_arr(trl, static_cast<size_t>(te - 1ULL));
    std::fprintf(fp, "E %llu DEC lvl=%llu lit=%d mode=%llu\n",
                 static_cast<unsigned long long>(s.seq++),
                 static_cast<unsigned long long>(lvl),
                 static_cast<int>(export_lit(lit)),
                 static_cast<unsigned long long>(stable ? 1ULL : 0ULL));
  }
#endif
}

inline void on_confl_enter(uint64_t hdr_addr) {
  if (detail::rd64(hdr_addr, 65) != 0ULL) return;  // probing
  uint64_t lvl = detail::rd64(hdr_addr, 20);
  if (lvl == 0ULL) return;
#ifdef KISSAT_LOCKSTEP_TRACE
  FILE* fp = trace_fp();
  if (!fp) return;
  uint64_t ctype = detail::rd64(hdr_addr, 66);
  std::vector<uint32_t> lits;
  if (ctype == 1ULL) {
    lits.push_back(static_cast<uint32_t>(detail::rd64(hdr_addr, 67)));
    lits.push_back(static_cast<uint32_t>(detail::rd64(hdr_addr, 68)));
  } else {
    uint64_t cref = detail::rd64(hdr_addr, 22);
    uint64_t ar = detail::rd64(hdr_addr, 14);
    uint64_t alen = detail::rd64(hdr_addr, 6);
    if (cref + 3ULL <= alen) {
      uint32_t sz = detail::rd32_arr(ar, static_cast<size_t>(cref + 2ULL));
      if (cref + 3ULL + sz <= alen) {
        lits.resize(sz);
        for (uint32_t i = 0; i < sz; ++i) {
          lits[i] = detail::rd32_arr(ar, static_cast<size_t>(cref + 3ULL + i));
        }
      }
    }
  }
  if (lits.empty()) return;
  uint64_t h = fnv64_sorted_lits(lits.data(), lits.size());
  uint64_t c = detail::rd64(hdr_addr, 42) + 1ULL;
  State& s = state();
  std::fprintf(fp, "E %llu CONFL c=%llu lvl=%llu sz=%zu hash=%016llx\n",
               static_cast<unsigned long long>(s.seq++),
               static_cast<unsigned long long>(c),
               static_cast<unsigned long long>(lvl),
               lits.size(),
               static_cast<unsigned long long>(h));
#else
  (void)hdr_addr;
#endif
}

inline void on_learn_enter(uint64_t hdr_addr, uint64_t glue, bool compute_nlvl) {
  if (detail::rd64(hdr_addr, 65) != 0ULL) return;
#ifdef KISSAT_LOCKSTEP_TRACE
  FILE* fp = trace_fp();
  if (!fp) return;
  uint64_t tlen = detail::rd64(hdr_addr, 24);
  if (tlen == 0ULL) return;
  uint64_t tmp = detail::rd64(hdr_addr, 17);
  uint64_t lvl_arr = detail::rd64(hdr_addr, 10);
  uint64_t cur_lvl = detail::rd64(hdr_addr, 20);
  std::vector<uint32_t> lits(static_cast<size_t>(tlen));
  uint64_t jlvl = 0ULL;
  for (uint64_t i = 0; i < tlen; ++i) {
    lits[static_cast<size_t>(i)] = detail::rd32_arr(tmp, static_cast<size_t>(i));
    if (i > 0ULL) {
      uint64_t lv = detail::rd32_arr(lvl_arr, lits[static_cast<size_t>(i)] >> 1);
      if (lv > jlvl) jlvl = lv;
    }
  }
  if (cur_lvl > 0ULL && jlvl >= cur_lvl) jlvl = cur_lvl - 1ULL;
  uint64_t nlvl = jlvl;
  if (compute_nlvl && state().is_full && cur_lvl > 0ULL) {
    uint64_t back = cur_lvl - 1ULL;
    uint64_t clim = detail::rd64(hdr_addr, 119);
    if (jlvl < back && back - jlvl > clim) nlvl = back;
  }
  uint64_t h = fnv64_sorted_lits(lits.data(), lits.size());
  uint64_t c = detail::rd64(hdr_addr, 42);
  State& s = state();
  std::fprintf(fp, "E %llu LEARN c=%llu sz=%llu glue=%llu uip=%d jlvl=%llu nlvl=%llu hash=%016llx\n",
               static_cast<unsigned long long>(s.seq++),
               static_cast<unsigned long long>(c),
               static_cast<unsigned long long>(tlen),
               static_cast<unsigned long long>(glue),
               static_cast<int>(export_lit(lits[0])),
               static_cast<unsigned long long>(jlvl),
               static_cast<unsigned long long>(nlvl),
               static_cast<unsigned long long>(h));
#else
  (void)hdr_addr;
  (void)glue;
  (void)compute_nlvl;
#endif
}

inline void on_restart_exit(uint64_t hdr_addr) {
  uint64_t reuse = detail::rd64(hdr_addr, 20);
  State& s = state();
  s.counters[EXT_RESTART_REUSE_LVLS] += reuse;
#ifdef KISSAT_LOCKSTEP_TRACE
  FILE* fp = trace_fp();
  if (fp) {
    std::fprintf(fp, "E %llu RST c=%llu reuse=%llu mode=%llu ticks=%llu\n",
                 static_cast<unsigned long long>(s.seq++),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 42)),
                 static_cast<unsigned long long>(reuse),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 69) ? 1ULL : 0ULL),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 75)));
  }
#endif
}

inline void on_switch_mode_exit(uint64_t hdr_addr, uint64_t prev_sw) {
  uint64_t sw = detail::rd64(hdr_addr, 70);
  if (sw == prev_sw) return;
#ifdef KISSAT_LOCKSTEP_TRACE
  FILE* fp = trace_fp();
  if (fp) {
    State& s = state();
    std::fprintf(fp, "E %llu MODE c=%llu to_stable=%llu ticks=%llu\n",
                 static_cast<unsigned long long>(s.seq++),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 42)),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 69) ? 1ULL : 0ULL),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 75)));
  }
#else
  (void)hdr_addr;
#endif
}

inline uint64_t count_active_redundant(uint64_t hdr_addr) {
  uint64_t ar = detail::rd64(hdr_addr, 14);
  uint64_t alen = detail::rd64(hdr_addr, 6);
  uint64_t cnt = 0ULL;
  uint64_t p = 0ULL;
  while (p + 3ULL <= alen) {
    uint32_t hdr = detail::rd32_arr(ar, static_cast<size_t>(p));
    uint32_t sz = detail::rd32_arr(ar, static_cast<size_t>(p + 2ULL));
    if ((hdr & 0x00400000u) != 0u && (hdr & 0x00080000u) == 0u) ++cnt;
    uint64_t nxt = p + 3ULL + static_cast<uint64_t>(sz);
    if (nxt > alen) break;
    if ((hdr & 0x00800000u) != 0u) {
      while (nxt < alen && detail::rd32_arr(ar, static_cast<size_t>(nxt)) != 0xFFFFFFFFu) ++nxt;
      if (nxt < alen) ++nxt;
    }
    p = nxt;
  }
  return cnt;
}

inline void on_reduce_exit(uint64_t hdr_addr, uint64_t prev_red) {
  uint64_t cur_red = count_active_redundant(hdr_addr);
  uint64_t del = (prev_red > cur_red) ? (prev_red - cur_red) : 0ULL;
  State& s = state();
  s.counters[EXT_REDUCED_CLAUSES] += del;
#ifdef KISSAT_LOCKSTEP_TRACE
  FILE* fp = trace_fp();
  if (fp) {
    std::fprintf(fp, "E %llu RED c=%llu tier1=%llu tier2=%llu del=%llu kept=%llu\n",
                 static_cast<unsigned long long>(s.seq++),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 42)),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 87)),
                 static_cast<unsigned long long>(detail::rd64(hdr_addr, 88)),
                 static_cast<unsigned long long>(del),
                 static_cast<unsigned long long>(cur_red));
  }
#endif
}

inline void on_det_new_level_exit(uint64_t hdr_addr, uint64_t jump, uint64_t ret) {
  uint64_t cur_lvl = detail::rd64(hdr_addr, 20);
  if (cur_lvl > 0ULL && ret > jump && ret == cur_lvl - 1ULL) {
    state().counters[EXT_CHRONO_BT_CNT]++;
  }
}

struct PassScope {
  uint64_t hdr_addr;
  const char* name;
  PassKind kind;
  const char* prev_inproc;
  uint64_t u0, b0, e0, t0, f0;
  std::chrono::steady_clock::time_point clk0;

  PassScope(uint64_t h, const char* n, PassKind k)
      : hdr_addr(h), name(n), kind(k), prev_inproc(state().inproc_src) {
    State& s = state();
    u0 = detail::rd64(h, 18);
    b0 = detail::rd64(h, 63);
    e0 = s.is_full ? detail::rd64(h, 136) : 0ULL;
    t0 = detail::rd64(h, 75);
    f0 = detail::rd64(h, 21);  // fuel
    if (n) s.inproc_src = n;
    if (k == PASS_PROBE) s.counters[EXT_PROBE_CALLS]++;
    else if (k == PASS_VIVIFY) s.counters[EXT_VIVIFY_CALLS]++;
    else if (k == PASS_COMPACT) s.counters[EXT_COMPACT_CNT]++;
    clk0 = std::chrono::steady_clock::now();
  }

  ~PassScope() {
    auto clk1 = std::chrono::steady_clock::now();
    uint64_t wall_ns = static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(clk1 - clk0).count());
    State& s = state();
    uint64_t u1 = detail::rd64(hdr_addr, 18);
    uint64_t b1 = detail::rd64(hdr_addr, 63);
    uint64_t e1 = s.is_full ? detail::rd64(hdr_addr, 136) : 0ULL;
    uint64_t t1 = detail::rd64(hdr_addr, 75);
    uint64_t f1 = detail::rd64(hdr_addr, 21);
    uint64_t ticks_delta = (t1 >= t0 ? (t1 - t0) : 0ULL) + (f0 >= f1 ? (f0 - f1) : 0ULL);
    switch (kind) {
      case PASS_PROBE:
        s.counters[EXT_PROBE_TICKS] += ticks_delta;
        s.counters[EXT_PROBE_WALL_NS] += wall_ns;
        break;
      case PASS_ELIM:
        s.counters[EXT_ELIM_TICKS] += ticks_delta;
        s.counters[EXT_ELIM_WALL_NS] += wall_ns;
        break;
      case PASS_VIVIFY:
        s.counters[EXT_VIVIFY_TICKS] += ticks_delta;
        s.counters[EXT_VIVIFY_WALL_NS] += wall_ns;
        break;
      case PASS_SWEEP:
        s.counters[EXT_SWEEP_TICKS] += ticks_delta;
        s.counters[EXT_SWEEP_WALL_NS] += wall_ns;
        break;
      case PASS_CONG:
        s.counters[EXT_CONG_TICKS] += ticks_delta;
        s.counters[EXT_CONG_WALL_NS] += wall_ns;
        break;
      case PASS_FACTOR:
        s.counters[EXT_FACTOR_TICKS] += ticks_delta;
        s.counters[EXT_FACTOR_WALL_NS] += wall_ns;
        break;
      case PASS_SUBST:
        s.counters[EXT_SUBST_WALL_NS] += wall_ns;
        break;
      case PASS_TRANS:
        s.counters[EXT_TRANS_WALL_NS] += wall_ns;
        break;
      case PASS_BACKBONE:
        s.counters[EXT_BACKBONE_WALL_NS] += wall_ns;
        break;
      case PASS_FWD:
        s.counters[EXT_FWD_SUB_WALL_NS] += wall_ns;
        break;
      case PASS_COMPACT:
        s.counters[EXT_COMPACT_WALL_NS] += wall_ns;
        break;
      default:
        break;
    }
    emit_unit0_range(hdr_addr, u0, u1, name ? name : "prop");
    s.inproc_src = prev_inproc;
#ifdef KISSAT_LOCKSTEP_TRACE
    FILE* fp = trace_fp();
    if (fp && name && kind != PASS_COMPACT) {
      int64_t du = static_cast<int64_t>(u1) - static_cast<int64_t>(u0);
      int64_t db = static_cast<int64_t>(b1) - static_cast<int64_t>(b0);
      int64_t de = static_cast<int64_t>(e1) - static_cast<int64_t>(e0);
      std::fprintf(fp, "E %llu INPROC c=%llu pass=%s units=%lld bins=%lld elim=%lld ticks=%llu\n",
                   static_cast<unsigned long long>(s.seq++),
                   static_cast<unsigned long long>(detail::rd64(hdr_addr, 42)),
                   name,
                   static_cast<long long>(du),
                   static_cast<long long>(db),
                   static_cast<long long>(de),
                   static_cast<unsigned long long>(t1));
    }
#else
    (void)b1;
    (void)e1;
#endif
  }
};

struct PropScope {
  uint64_t hdr_addr;
  uint64_t p0;
  uint64_t te0;
  bool top;

  explicit PropScope(uint64_t h) : hdr_addr(h) {
    State& s = state();
    top = (s.prop_depth == 0ULL);
    s.prop_depth++;
    p0 = detail::rd64(h, 19);
    te0 = detail::rd64(h, 18);
  }

  ~PropScope() {
    State& s = state();
    s.prop_depth--;
    if (top) {
      uint64_t p1 = detail::rd64(hdr_addr, 19);
      uint64_t te1 = detail::rd64(hdr_addr, 18);
      if (p1 > p0) s.counters[EXT_PROPAGATIONS] += (p1 - p0);
      emit_unit0_range(hdr_addr, te0, te1, "prop");
    }
  }
};

struct UnitSrcScope {
  const char* prev;
  explicit UnitSrcScope(const char* src) : prev(state().unit_src) { state().unit_src = src; }
  ~UnitSrcScope() { state().unit_src = prev; }
};

inline void on_kitten_solve_enter() { state().counters[EXT_KITTEN_CALLS]++; }
inline void on_otfs_subsume() { state().counters[EXT_OTFS_SUBSUME]++; }

#else

inline void on_parse_enter(uint64_t) {}
inline void on_init_exit(uint64_t, bool) {}
inline void flush_ext_telem(uint64_t) {}
inline void on_solve_enter(uint64_t, bool) {}
inline void on_solve_exit(uint64_t, uint64_t) {}
inline void on_decide_exit(uint64_t, uint64_t, uint64_t, uint64_t) {}
inline void on_confl_enter(uint64_t) {}
inline void on_learn_enter(uint64_t, uint64_t, bool) {}
inline void on_restart_exit(uint64_t) {}
inline void on_switch_mode_exit(uint64_t, uint64_t) {}
inline uint64_t count_active_redundant(uint64_t) { return 0ULL; }
inline void on_reduce_exit(uint64_t, uint64_t) {}
inline void on_det_new_level_exit(uint64_t, uint64_t, uint64_t) {}
inline void sync_dimacs_after_compact(uint64_t) {}
inline void emit_unit0_range(uint64_t, uint64_t, uint64_t, const char*) {}
inline void on_kitten_solve_enter() {}
inline void on_otfs_subsume() {}

struct PassScope {
  PassScope(uint64_t, const char*, PassKind) {}
};
struct PropScope {
  explicit PropScope(uint64_t) {}
};
struct UnitSrcScope {
  explicit UnitSrcScope(const char*) {}
};

#endif

}  // namespace c3b_trace

#endif
