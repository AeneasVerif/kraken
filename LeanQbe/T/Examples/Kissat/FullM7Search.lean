module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M7 Search Parity C0 Overrides (`FullM7Search`)

Strictly additive Kissat 4.0.4 search-fidelity module closing `audit-quick60-gaps` Gaps #2, #3,
#5, and #7 (`0` edits to `FullHdr` / `144` words frozen, `0` edits to `Full1..6*`):
1. `full_lucky_late_m7` & `full_lucky_polar_m7` (`src/lucky.c`, `src/search.c:188-189`):
   post-preprocessing level-0 late lucky assignment checks (level-0 unit propagation guard,
   polarity sweeps skipping already-satisfied clauses, plus forward/backward `full_lucky_scan`
   without corrupting level-0 trail/assignments when not SAT).
2. `full_tumble_clause_m7`, `full_tumble_clauses_m7`, `full_tumble_m7` (`src/tumble.c`):
   clause-literal tumbling shuffling `lits[2..sz-1]` with upstream Knuth LCG (`full_lcg_next_m7`),
   resetting saved search position `ar[cref + 1] = 2u`, and preserving `lits[0..1]` and literal
   multiset identically.
3. `full_randec_step_m7`, `full_randec_var_m7`, `full_decide_m7` (`src/decide.c:57-124, 178-187`):
   faithful decision selection with upstream `randec` bursts in focused mode (`stable == 0`,
   Knuth LCG + `10 * log10(count + 9)` length / `500 * log10(count + 9)` conflict cadence) and
   upstream focused initial phase alternation `(switched >> 1) & 7` (`1 -> +1`, `3 -> -1`) before
   consulting saved phases.
4. `full_ema_swap_m7`, `full_switch_mode_m7` (`src/mode.c:69-70`, `src/averages.c`):
   mode switching preserving/swapping per-mode `(ema_fast_biased, ema_fast_exp, ema_slow_biased,
   ema_slow_exp)` inside `h->glue_used[36..63]` (`full_m7_state_init` / `full_m7_*64`), avoiding
   focused/stable EMA wipe-induced restart storms.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7Search

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

/-! ## 1. Layout & Search-Parity Constants (`h->glue_used[36..63]`) -/

/-- Magic identifier stored at `gu[36..37]` (`"M7SEARCH"`). -/
def m7SearchMagic : BitVec 64 := 0x4D37534541524348#64

/-- Initial/default Q32 EMA normalization denominator (`1 << 32`). -/
def m7EmaInitExp : BitVec 64 := 1#64 <<< 32

/-- Knuth 64-bit LCG multiplier (`src/random.h`). -/
def m7LcgMul : BitVec 64 := 6364136223846793005#64

/-- Knuth 64-bit LCG additive constant (`src/random.h`). -/
def m7LcgInc : BitVec 64 := 1442695040888963407#64

/-- Base conflict interval before first random decision burst (`options.h:105-106`). -/
def m7RandecInitLim : Nat := 500

/-- Base burst length multiplier `randeclength = 10` (`options.h:107`). -/
def m7RandecLen : Nat := 10

/-- `u32` word indices inside `h->glue_used[36..63]` (`28` words = `14` `u64` slots). -/
def m7GuMagicIdx : Nat := 36
def m7GuEmaMaskIdx : Nat := 38
def m7GuEma0FbIdx : Nat := 40
def m7GuEma0FeIdx : Nat := 42
def m7GuEma0SbIdx : Nat := 44
def m7GuEma0SeIdx : Nat := 46
def m7GuEma1FbIdx : Nat := 48
def m7GuEma1FeIdx : Nat := 50
def m7GuEma1SbIdx : Nat := 52
def m7GuEma1SeIdx : Nat := 54
def m7GuRandecRemIdx : Nat := 56
def m7GuRandecLimIdx : Nat := 58
def m7GuRandecSeqIdx : Nat := 60
def m7GuRandecConflIdx : Nat := 62

/-! ## 2. C0 Implementation (`m7Search`) -/

kissat_c0! m7Search "
typedef struct {
  u64 mv, nc, cur, val;
} KissatDimacs;

typedef struct {
  KissatDimacs d;
  u64 arena_cap, wcap, arena_len, wlen;
  u64 values, mark, level, reason, trail;
  u64 watch_vec, arena, watch_stk, delayed, tmp_lits;
  u64 trail_end, propagated, cur_level, fuel, confl_ref;
  u64 tmp_cnt, tmp_len, heap, pos, score;
  u64 phases, min_stk, min_clr, heap_len, scinc;
  u64 min_depth, min_clr_len, min_clr_full, rel_period, rel_limit;
  u64 rel_wait, rel_u, rel_v, rel_trigger, conflicts;
  u64 learned_lits, min_removed, trail_pos, q_prev, q_next;
  u64 q_stamp, phases_target, phases_best, wsort, shrink_stk;
  u64 red_refs, glue_used, red_cap, delayed_cap, delayed_len;
  u64 wusable, arena_garbage, first_reducible, num_irred, num_redundant;
  u64 num_binary, unflushed, probing, confl_type, confl_lit0;
  u64 confl_lit1, stable, switched, mode_count, mode_confl_lim;
  u64 mode_tick_lim, mode_saved_ticks, search_ticks, q_first, q_last;
  u64 q_search_idx, q_search_stamp, q_cur_stamp, target_assigned, best_assigned;
  u64 rephase_limit, rephased, reduce_limit, reductions, tier1;
  u64 tier2, restarts, restart_limit, ema_fast_biased, ema_fast_exp;
  u64 ema_slow_biased, ema_slow_exp, oom;
  u64 max_vars, cur_vars, bva_cap, unassigned;
  u64 flags, lit_mark, repr, sim_sig;
  u64 frame_trail, frame_dec, work_stk1, work_stk2;
  u64 tarjan_mark, tarjan_reach, walk_vals, walk_best;
  u64 extend_stk, extend_cap, extend_len;
  u64 scratch_buf, scratch_cap, last_learned;
  u64 rng_state, chrono_levels, otfs_cnt, eager_sub_cnt;
  u64 probe_limit, probings, elim_limit, eliminations;
  u64 elim_bound, dense_mode, inconsistent, iterating;
  u64 hbr_cnt, trans_cnt, viv_cnt, subst_cnt;
  u64 cong_cnt, sweep_cnt, bve_cnt, bce_cnt;
  u64 bva_cnt, walk_cnt_stat, fwd_sub_cnt, fwd_str_cnt;
  u64 ant_sz, res_sz;
} FullHdr;

#define PH_GARB           0x00080000u
#define PH_RED            0x00400000u
#define PW_BIN_FLAG       0x80000000u
#define PW_LIT_MASK       0x7FFFFFFFu
#define FL_ACTIVE         1u

#define M7_SEARCH_MAGIC   0x4D37534541524348ULL
#define M7_GU_MAGIC       36ULL
#define M7_GU_EMA_MASK    38ULL
#define M7_GU_EMA0_FB     40ULL
#define M7_GU_EMA0_FE     42ULL
#define M7_GU_EMA0_SB     44ULL
#define M7_GU_EMA0_SE     46ULL
#define M7_GU_EMA1_FB     48ULL
#define M7_GU_EMA1_FE     50ULL
#define M7_GU_EMA1_SB     52ULL
#define M7_GU_EMA1_SE     54ULL
#define M7_GU_RANDEC_REM  56ULL
#define M7_GU_RANDEC_LIM  58ULL
#define M7_GU_RANDEC_SEQ  60ULL
#define M7_GU_RANDEC_CFL  62ULL

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern u64 full_ilog10(u64 x);
extern void full_heap_down(FullHdr *h, u32 v);
extern u64 full_next_dec_var(FullHdr *h);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_propagate(FullHdr *h);
extern u64 full_lucky_scan(FullHdr *h, bool pos_mode, bool fwd);

u64 full_lcg_next_m7(FullHdr *h) {
  u64 x = h->rng_state;
  x = x * 6364136223846793005ULL + 1442695040888963407ULL;
  h->rng_state = x;
  return x >> 32;
}

u64 full_m7_get64(FullHdr *h, u64 idx) {
  if (idx >= 63ULL) { return 0ULL; }
  u32 *gu = (u32 *)h->glue_used;
  return ((u64)gu[idx]) | (((u64)gu[idx + 1ULL]) << 32);
}

void full_m7_set64(FullHdr *h, u64 idx, u64 val) {
  if (idx >= 63ULL) { return; }
  u32 *gu = (u32 *)h->glue_used;
  gu[idx] = (u32)val;
  gu[idx + 1ULL] = (u32)(val >> 32);
}

void full_m7_state_init(FullHdr *h) {
  if (full_m7_get64(h, M7_GU_MAGIC) == M7_SEARCH_MAGIC) { return; }
  full_m7_set64(h, M7_GU_MAGIC, M7_SEARCH_MAGIC);
  u64 cm = (h->stable != 0ULL) ? 1ULL : 0ULL;
  full_m7_set64(h, M7_GU_EMA_MASK, 1ULL << cm);
  u64 init_exp = 1ULL << 32;
  if (cm == 0ULL) {
    full_m7_set64(h, M7_GU_EMA0_FB, h->ema_fast_biased);
    full_m7_set64(h, M7_GU_EMA0_FE, h->ema_fast_exp);
    full_m7_set64(h, M7_GU_EMA0_SB, h->ema_slow_biased);
    full_m7_set64(h, M7_GU_EMA0_SE, h->ema_slow_exp);
    full_m7_set64(h, M7_GU_EMA1_FB, 0ULL);
    full_m7_set64(h, M7_GU_EMA1_FE, init_exp);
    full_m7_set64(h, M7_GU_EMA1_SB, 0ULL);
    full_m7_set64(h, M7_GU_EMA1_SE, init_exp);
  } else {
    full_m7_set64(h, M7_GU_EMA1_FB, h->ema_fast_biased);
    full_m7_set64(h, M7_GU_EMA1_FE, h->ema_fast_exp);
    full_m7_set64(h, M7_GU_EMA1_SB, h->ema_slow_biased);
    full_m7_set64(h, M7_GU_EMA1_SE, h->ema_slow_exp);
    full_m7_set64(h, M7_GU_EMA0_FB, 0ULL);
    full_m7_set64(h, M7_GU_EMA0_FE, init_exp);
    full_m7_set64(h, M7_GU_EMA0_SB, 0ULL);
    full_m7_set64(h, M7_GU_EMA0_SE, init_exp);
  }
  full_m7_set64(h, M7_GU_RANDEC_REM, 0ULL);
  full_m7_set64(h, M7_GU_RANDEC_LIM, 500ULL);
  full_m7_set64(h, M7_GU_RANDEC_SEQ, 0ULL);
  full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
}

u64 full_log10_q16_m7(u64 x) {
  if (x <= 1ULL) { return 0ULL; }
  u64 d = 0ULL;
  u64 pow10 = 1ULL;
  while (x / 10ULL >= pow10 && d < 19ULL) {
    d = d + 1ULL;
    pow10 = pow10 * 10ULL;
  }
  u64 xm = x;
  u64 pm = pow10;
  if (pm > 100000000ULL) {
    u64 sc = pm / 100000000ULL;
    xm = xm / sc;
    pm = 100000000ULL;
  }
  u64 m = (xm << 32) / pm;
  u64 lim10 = 10ULL << 32;
  u64 frac = 0ULL;
  u64 i = 0ULL;
  while (i < 16ULL) {
    u64 m_hi = m >> 16;
    u64 m_lo = m & 0xFFFFULL;
    u64 q = (m_lo * m_lo) >> 16;
    u64 mid = (2ULL * m_hi * m_lo) + q;
    m = (m_hi * m_hi) + (mid >> 16);
    frac = frac << 1;
    if (m >= lim10) {
      m = m / 10ULL;
      frac = frac + 1ULL;
    }
    i = i + 1ULL;
  }
  return (d << 16) + frac;
}

bool full_tumble_clause_m7(FullHdr *h, u32 cref) {
  if ((u64)cref + 3ULL > h->arena_len) { return false; }
  u32 *ar = (u32 *)h->arena;
  u32 hdr = ar[cref];
  u32 sz = ar[(u64)cref + 2ULL];
  if ((hdr & PH_GARB) != 0u || sz < 4u ||
      (u64)cref + 3ULL + (u64)sz > h->arena_len) {
    return false;
  }
  ar[(u64)cref + 1ULL] = 2u;
  u32 i = sz - 1u;
  while (i > 2u) {
    u64 r = full_lcg_next_m7(h);
    u32 span = i - 1u;
    u32 j = 2u + (u32)(r % (u64)span);
    u32 li = ar[(u64)cref + 3ULL + (u64)i];
    u32 lj = ar[(u64)cref + 3ULL + (u64)j];
    ar[(u64)cref + 3ULL + (u64)i] = lj;
    ar[(u64)cref + 3ULL + (u64)j] = li;
    i = i - 1u;
  }
  return true;
}

u64 full_tumble_clauses_m7(FullHdr *h, u64 budget) {
  u64 p = 0ULL;
  u64 done = 0ULL;
  while (p < h->arena_len && done < budget) {
    u64 np = (u64)full_arena_next(h, (u32)p);
    if (full_tumble_clause_m7(h, (u32)p)) { done = done + 1ULL; }
    if (np <= p) { break; }
    p = np;
  }
  return done;
}

u64 full_tumble_m7(FullHdr *h) {
  return full_tumble_clauses_m7(h, h->arena_len);
}

u64 full_lucky_polar_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  bool has_neg = false;
  bool has_pos = false;
  u64 p = 0ULL;
  while (p < h->arena_len && (!has_neg || !has_pos)) {
    u64 np = (u64)full_arena_next(h, (u32)p);
    if (p + 3ULL <= h->arena_len) {
      u32 hdr = ar[p];
      u32 sz = ar[p + 2ULL];
      if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) == 0u &&
          sz >= 3u && p + 3ULL + (u64)sz <= h->arena_len) {
        bool sat = false;
        bool ap = false;
        bool an = false;
        u32 k = 0u;
        while (k < sz) {
          u32 l = ar[p + 3ULL + (u64)k];
          if ((u64)l < nlits) {
            i8 vl = vals[l];
            if (vl > (i8)0) { sat = true; break; }
            if (vl >= (i8)0) {
              if ((l & 1u) == 0u) { ap = true; } else { an = true; }
            }
          }
          k = k + 1u;
        }
        if (!sat) {
          if (!ap) { has_neg = true; }
          if (!an) { has_pos = true; }
        }
      }
    }
    if (np <= p) { break; }
    p = np;
  }
  u64 v = 0ULL;
  while (v < cv && (!has_neg || !has_pos)) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u32 nl = (u32)((v << 1) | 1ULL);
      u64 off = (u64)wvec[(u64)nl << 1];
      u64 sz = (u64)wvec[((u64)nl << 1) + 1ULL];
      if (off <= h->wlen && sz <= h->wlen - off) {
        u64 end = off + sz;
        while (off < end && !has_neg) {
          u32 w0 = wstk[off];
          if ((w0 & PW_BIN_FLAG) != 0u) {
            u32 ot = w0 & PW_LIT_MASK;
            if ((u64)ot < nlits) {
              i8 vo = vals[ot];
              if (vo < (i8)0 || (vo == (i8)0 && (ot & 1u) != 0u)) {
                has_neg = true;
              }
            }
            off = off + 1ULL;
          } else {
            off = off + 2ULL;
          }
        }
      }
      u32 pl = (u32)(v << 1);
      u64 off2 = (u64)wvec[(u64)pl << 1];
      u64 sz2 = (u64)wvec[((u64)pl << 1) + 1ULL];
      if (off2 <= h->wlen && sz2 <= h->wlen - off2) {
        u64 end2 = off2 + sz2;
        while (off2 < end2 && !has_pos) {
          u32 w0 = wstk[off2];
          if ((w0 & PW_BIN_FLAG) != 0u) {
            u32 ot = w0 & PW_LIT_MASK;
            if ((u64)ot < nlits) {
              i8 vo = vals[ot];
              if (vo < (i8)0 || (vo == (i8)0 && (ot & 1u) == 0u)) {
                has_pos = true;
              }
            }
            off2 = off2 + 1ULL;
          } else {
            off2 = off2 + 2ULL;
          }
        }
      }
    }
    v = v + 1ULL;
  }
  if (has_neg && has_pos) { return 0ULL; }
  return has_neg ? 2ULL : 1ULL;
}

u64 full_lucky_late_m7(FullHdr *h) {
  if (h->inconsistent != 0ULL) { h->probing = 0ULL; return 20ULL; }
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if (h->propagated < h->trail_end) {
    u64 pr0 = full_propagate(h);
    if (pr0 == 1ULL) { h->inconsistent = 1ULL; h->probing = 0ULL; return 20ULL; }
    if (pr0 == 2ULL) { h->probing = 0ULL; return 2ULL; }
  }
  h->probing = 1ULL;
  u64 pol = full_lucky_polar_m7(h);
  if (pol != 0ULL) {
    bool set_pos = (pol == 1ULL);
    i8 *vals = (i8 *)h->values;
    u32 *fl = (u32 *)h->flags;
    u32 *ftrl = (u32 *)h->frame_trail;
    u32 *fdec = (u32 *)h->frame_dec;
    u64 v = 0ULL;
    while (v < h->cur_vars) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        if (h->fuel == 0ULL) {
          full_backtrack(h, 0ULL); h->probing = 0ULL; return 2ULL;
        }
        h->fuel = h->fuel - 1ULL;
        u32 lit = set_pos ? (u32)(v << 1) : ((u32)(v << 1) | 1u);
        u64 nlvl = h->cur_level + 1ULL;
        if (nlvl > h->max_vars) {
          full_backtrack(h, 0ULL); h->probing = 0ULL; return 0ULL;
        }
        ftrl[nlvl] = (u32)h->trail_end;
        fdec[nlvl] = lit;
        h->cur_level = nlvl;
        full_assign(h, lit, 0xFFFFFFFFu);
        u64 pr = full_propagate(h);
        if (pr == 2ULL) {
          full_backtrack(h, 0ULL); h->probing = 0ULL; return 2ULL;
        }
        if (pr == 1ULL) {
          full_backtrack(h, 0ULL); h->probing = 0ULL; return 0ULL;
        }
      }
      v = v + 1ULL;
    }
    h->probing = 0ULL;
    return 10ULL;
  }
  u64 r = full_lucky_scan(h, false, true);
  if (r == 0ULL) { r = full_lucky_scan(h, true, true); }
  if (r == 0ULL) { r = full_lucky_scan(h, false, false); }
  if (r == 0ULL) { r = full_lucky_scan(h, true, false); }
  h->probing = 0ULL;
  return r;
}

void full_randec_step_m7(FullHdr *h) {
  full_m7_state_init(h);
  u64 rem = full_m7_get64(h, M7_GU_RANDEC_REM);
  if (rem > 0ULL) {
    full_m7_set64(h, M7_GU_RANDEC_REM, rem - 1ULL);
  }
  full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
}

u64 full_randec_var_m7(FullHdr *h) {
  u64 cv = h->cur_vars;
  if (cv == 0ULL || h->stable != 0ULL || h->probing != 0ULL) {
    return 0xFFFFFFFFFFFFFFFFULL;
  }
  full_m7_state_init(h);
  u64 rem = full_m7_get64(h, M7_GU_RANDEC_REM);
  u64 lc = full_m7_get64(h, M7_GU_RANDEC_CFL);
  if (h->conflicts > lc) {
    u64 dc = h->conflicts - lc;
    rem = (rem > dc) ? (rem - dc) : 0ULL;
    full_m7_set64(h, M7_GU_RANDEC_REM, rem);
    full_m7_set64(h, M7_GU_RANDEC_CFL, h->conflicts);
  }
  if (rem == 0ULL) {
    if (h->cur_level > 0ULL) { return 0xFFFFFFFFFFFFFFFFULL; }
    u64 lim = full_m7_get64(h, M7_GU_RANDEC_LIM);
    if (h->conflicts < lim) { return 0xFFFFFFFFFFFFFFFFULL; }
    u64 cnt = full_m7_get64(h, M7_GU_RANDEC_SEQ) + 1ULL;
    full_m7_set64(h, M7_GU_RANDEC_SEQ, cnt);
    u64 qarg = (cnt < 1000000000000ULL) ? (cnt + 9ULL) : 1000000000009ULL;
    u64 lg = full_log10_q16_m7(qarg);
    u64 len = (10ULL * lg) >> 16;
    if (len < 10ULL) { len = 10ULL; }
    u64 delta = (500ULL * lg) >> 16;
    full_m7_set64(h, M7_GU_RANDEC_REM, len);
    full_m7_set64(h, M7_GU_RANDEC_LIM, h->conflicts + delta);
    rem = len;
  }
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u64 max_tries = (cv < 4096ULL) ? (cv * 4ULL + 16ULL) : 16384ULL;
  u64 tries = 0ULL;
  while (tries < max_tries) {
    u64 idx = full_lcg_next_m7(h) % cv;
    if ((fl[idx] & FL_ACTIVE) != 0u && vals[idx << 1] == (i8)0) {
      return idx;
    }
    tries = tries + 1ULL;
  }
  return 0xFFFFFFFFFFFFFFFFULL;
}

u64 full_decide_m7(FullHdr *h) {
  u64 chosen = full_randec_var_m7(h);
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) {
    chosen = full_next_dec_var(h);
  }
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) { return 0ULL; }
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 dph = (i8)0;
  if (h->stable == 0ULL) {
    u64 sw3 = (h->switched >> 1) & 7ULL;
    if (sw3 == 1ULL) { dph = (i8)1; }
    else if (sw3 == 3ULL) { dph = (i8)(-1); }
  }
  if (dph == (i8)0 && h->stable != 0ULL && ptgt[chosen] != (i8)0) {
    dph = ptgt[chosen];
  }
  if (dph == (i8)0) { dph = ph[chosen]; }
  u32 lit = (dph < (i8)0) ? ((u32)(chosen << 1) | 1u) : (u32)(chosen << 1);
  u64 nlvl = h->cur_level + 1ULL;
  if (nlvl > h->max_vars) { return 0ULL; }
  ftrl[nlvl] = (u32)h->trail_end;
  fdec[nlvl] = lit;
  h->cur_level = nlvl;
  full_assign(h, lit, 0xFFFFFFFFu);
  return 1ULL;
}

void full_ema_swap_m7(FullHdr *h, u64 old_m, u64 new_m) {
  u64 om = (old_m != 0ULL) ? 1ULL : 0ULL;
  u64 nm = (new_m != 0ULL) ? 1ULL : 0ULL;
  h->stable = om;
  full_m7_state_init(h);
  h->stable = nm;
  u64 old_base = (om == 0ULL) ? M7_GU_EMA0_FB : M7_GU_EMA1_FB;
  full_m7_set64(h, old_base, h->ema_fast_biased);
  full_m7_set64(h, old_base + 2ULL, h->ema_fast_exp);
  full_m7_set64(h, old_base + 4ULL, h->ema_slow_biased);
  full_m7_set64(h, old_base + 6ULL, h->ema_slow_exp);
  u64 mask = full_m7_get64(h, M7_GU_EMA_MASK) | (1ULL << om);
  u64 new_base = (nm == 0ULL) ? M7_GU_EMA0_FB : M7_GU_EMA1_FB;
  u64 bit = 1ULL << nm;
  if ((mask & bit) != 0ULL) {
    h->ema_fast_biased = full_m7_get64(h, new_base);
    h->ema_fast_exp = full_m7_get64(h, new_base + 2ULL);
    h->ema_slow_biased = full_m7_get64(h, new_base + 4ULL);
    h->ema_slow_exp = full_m7_get64(h, new_base + 6ULL);
  } else {
    u64 init_exp = 1ULL << 32;
    h->ema_fast_biased = 0ULL;
    h->ema_fast_exp = init_exp;
    h->ema_slow_biased = 0ULL;
    h->ema_slow_exp = init_exp;
    full_m7_set64(h, new_base, 0ULL);
    full_m7_set64(h, new_base + 2ULL, init_exp);
    full_m7_set64(h, new_base + 4ULL, 0ULL);
    full_m7_set64(h, new_base + 6ULL, init_exp);
    mask = mask | bit;
  }
  full_m7_set64(h, M7_GU_EMA_MASK, mask);
}

void full_switch_mode_m7(FullHdr *h) {
  u64 old_m = 0ULL;
  u64 new_m = 1ULL;
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    old_m = 0ULL;
    new_m = 1ULL;
    h->stable = 1ULL;
    u64 dticks = (h->search_ticks > h->mode_saved_ticks) ?
      (h->search_ticks - h->mode_saved_ticks) : 0ULL;
    h->mode_tick_lim = h->search_ticks + dticks;
    h->mode_saved_ticks = h->search_ticks;
    u64 rp = h->rel_period;
    if (h->rel_limit > 0ULL && rp > h->rel_limit) { rp = h->rel_limit; }
    h->rel_wait = rp;
    h->rel_u = 1ULL;
    h->rel_v = 1ULL;
    h->rel_trigger = 0ULL;
    u64 cv = h->cur_vars;
    i8 *vals = (i8 *)h->values;
    u32 *fl = (u32 *)h->flags;
    u32 *hp = (u32 *)h->heap;
    u32 *ps = (u32 *)h->pos;
    u64 n = 0ULL;
    u64 v = 0ULL;
    while (v < cv) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        hp[n] = (u32)v;
        ps[v] = (u32)n;
        n = n + 1ULL;
      } else {
        ps[v] = 0xFFFFFFFFu;
      }
      v = v + 1ULL;
    }
    h->heap_len = n;
    u64 s = n >> 1;
    while (s > 0ULL) { s = s - 1ULL; full_heap_down(h, hp[s]); }
  } else {
    if (h->search_ticks < h->mode_tick_lim) { return; }
    old_m = 1ULL;
    new_m = 0ULL;
    h->stable = 0ULL;
    u64 cnt = (h->switched >> 1) + 1ULL;
    u64 cc = (cnt < 1000000000000ULL) ? cnt : 1000000000000ULL;
    u64 q = full_log10_q16_m7(cc + 9ULL);
    u64 l2 = (q * q) >> 16;
    u64 l4 = (l2 * l2) >> 16;
    u64 scaled = 0ULL;
    if (cnt <= 1000000ULL) {
      scaled = (1000ULL * cnt * l4) >> 16;
    } else {
      u64 clim = (cnt > 100000000ULL) ? 100000000ULL : cnt;
      scaled = ((1000ULL * clim) >> 16) * l4;
    }
    h->mode_confl_lim = h->conflicts + scaled;
    h->mode_saved_ticks = h->search_ticks;
    h->q_search_idx = h->q_last;
    if (h->q_search_idx < h->cur_vars) {
      u32 *qs = (u32 *)h->q_stamp;
      h->q_search_stamp = (u64)qs[h->q_search_idx];
    }
  }
  h->switched = h->switched + 1ULL;
  h->mode_count = h->mode_count + 1ULL;
  full_ema_swap_m7(h, old_m, new_m);
  if (h->stable == 0ULL) {
    u64 delta = 1ULL;
    u64 rst = h->restarts;
    if (rst > 0ULL) {
      u64 rc = (rst < 1000000000000ULL) ? rst : 1000000000000ULL;
      u64 d10 = full_ilog10(rc + 9ULL);
      delta = (d10 > 1ULL) ? (d10 - 1ULL) : 1ULL;
    }
    h->restart_limit = h->conflicts + delta;
  }
}
"

/-- External canonical `FullSpec` callees referenced by `m7Search_fns` (`8` externs). -/
def m7SearchExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_heap_down", [i64, i32], []⟩
  , ⟨"full_next_dec_var", [i64], [i64]⟩
  , ⟨"full_assign", [i64, i32, i32], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_propagate", [i64], [i64]⟩
  , ⟨"full_lucky_scan", [i64, .bool, .bool], [i64]⟩ ]

/-- Standalone M7 search-parity module (`15` functions + `8` externs, `0` exits). -/
def m7SearchModule : LeanQbe.T.Module :=
  { fns := m7Search_fns, externs := m7SearchExterns, exits := [] }

theorem full_lcg_next_m7_wf : Func.Wf full_lcg_next_m7_body := by t_wf_reify
theorem full_m7_get64_wf : Func.Wf full_m7_get64_body := by t_wf_reify
theorem full_m7_set64_wf : Func.Wf full_m7_set64_body := by t_wf_reify
theorem full_m7_state_init_wf : Func.Wf full_m7_state_init_body := by t_wf_reify
theorem full_log10_q16_m7_wf : Func.Wf full_log10_q16_m7_body := by t_wf_reify
theorem full_tumble_clause_m7_wf : Func.Wf full_tumble_clause_m7_body := by t_wf_reify
theorem full_tumble_clauses_m7_wf : Func.Wf full_tumble_clauses_m7_body := by t_wf_reify
theorem full_tumble_m7_wf : Func.Wf full_tumble_m7_body := by t_wf_reify
theorem full_lucky_polar_m7_wf : Func.Wf full_lucky_polar_m7_body := by t_wf_reify
theorem full_lucky_late_m7_wf : Func.Wf full_lucky_late_m7_body := by t_wf_reify
theorem full_randec_step_m7_wf : Func.Wf full_randec_step_m7_body := by t_wf_reify
theorem full_randec_var_m7_wf : Func.Wf full_randec_var_m7_body := by t_wf_reify
theorem full_decide_m7_wf : Func.Wf full_decide_m7_body := by t_wf_reify
theorem full_ema_swap_m7_wf : Func.Wf full_ema_swap_m7_body := by t_wf_reify
theorem full_switch_mode_m7_wf : Func.Wf full_switch_mode_m7_body := by t_wf_reify

theorem m7Search_fns_wf : ∀ f ∈ m7Search_fns, f.Wf := by
  simp only [m7Search_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_lcg_next_m7_wf, full_m7_get64_wf, full_m7_set64_wf, full_m7_state_init_wf,
    full_log10_q16_m7_wf, full_tumble_clause_m7_wf, full_tumble_clauses_m7_wf, full_tumble_m7_wf,
    full_lucky_polar_m7_wf, full_lucky_late_m7_wf, full_randec_step_m7_wf, full_randec_var_m7_wf,
    full_decide_m7_wf, full_ema_swap_m7_wf, full_switch_mode_m7_wf⟩

theorem m7Search_acyclic : m7SearchModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7Search
