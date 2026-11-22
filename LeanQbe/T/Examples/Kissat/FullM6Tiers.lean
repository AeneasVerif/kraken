module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Wave 2 `PR-W2A` (`RC-19`): Mode-Split Tiers, `used[2].glue[128]`, `delay[4]`, Watermarks

Purely additive C0 extension module on top of frozen `FullHdr` (`144` `u64` words = `1152` bytes;
zero edits to `Full1..3`, `FullM4*`, `FullM5*`, `M5Hub.lean`, or `FullHdr`):

1. **`FullM6Hdr` / `M6HdrExt` Layout Constants (`144` base + `288` ext = `432` `u64` words):**
   - Explicitly defines `M6HdrExt` (`2304` bytes) and `FullM6Hdr` (`FullHdr base; M6HdrExt ext;`,
     `3456` bytes) extending the `144`-word `FullHdr` cleanly while reserving `48` bytes
     (`w2b_delayed_reserved[6]` = `12` `u32` words) for `w2b` (`FullM6MinShrink`) `decision_rate`.
   - At runtime against frozen `FullMem`, when `h->delayed_cap >= fullM6DelMinCap` (`200`),
     `M6HdrExt` state is stored inside `h->delayed[16 .. 565]` (`del[0..15]` = `64` bytes left
     untouched for `w2b`'s `del[0..11]`), falling back safely to `FullHdr` when tiny.
2. **Mode-Split Tiers & `used[2].glue[128]` (`tiers.c`, `deduce.c`, `analyze.c`):**
   - `full_m6_recompute_tiers_mode` & `full_recompute_tiers_m6` over `128` glue bins per mode
     (`focused=0`, `stable=1`) using upstream `50%` / `90%` cumulative thresholds (`tiers.c`),
     maintaining `total_used[2]` and syncing `h->tier1` / `h->tier2 = max(tier1[0], tier2[1])`.
   - `full_m6_record_used` & `full_m6_update_tier_limits` (`limits.glue.interval` doubling
     `2..65536` per `analyze.c:519-525`).
3. **`delay[4]` Backoff (`kimits.h` / `kimits.c`):**
   - `full_m6_delaying`, `full_m6_bump_delay`, `full_m6_reduce_delay`, `full_m6_reset_delay`
     over `4` independent slots (`0=bumpreasons/autarky`, `1=congruence`, `2=sweep/eliminate`,
     `3=vivifyirr/vivify`).
4. **Separate Tick Watermarks & Mode Budgeting (`probe.c`, `eliminate.c`, `reduce.c`, `mode.c`):**
   - Dedicated `last_probe_ticks`, `last_elim_ticks`, `last_reduce_confl`, `last_reduce_ticks`,
     `last_rephase_ticks`, `probing_ticks`, `mode_focused_ticks`, `mode_stable_ticks` (removing
     `fwd_sub_cnt`/`fwd_str_cnt` aliasing) plus upgraded `full_switch_mode_m6`, `full_rephase_m6`,
     `full_reduce_m6`, `full_analyze_rsn_m6`, `full_analyze_m6`, `full_probe_m6`,
     `full_eliminate_m6`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6Tiers

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

/-! ## 1. Extended `FullM6Hdr` & `M6HdrExt` Layout Constants -/

/-- Base `FullHdr` word count (`144` `u64` words = `4` DIMACS + `140` tail words, unchanged). -/
def fullM6HdrBaseWords : Nat := 144

/-- Base `FullHdr` byte size (`144 * 8 = 1152` bytes). -/
def fullM6HdrBaseBytes : Nat := 1152

/-- Extended `M6HdrExt` `u64` word count (`288` words = `32` header/state + `256` glue bins). -/
def fullM6ExtWords : Nat := 288

/-- Extended `M6HdrExt` byte size (`288 * 8 = 2304` bytes). -/
def fullM6ExtBytes : Nat := 2304

/-- Total unified `FullM6Hdr` word count (`144 + 288 = 432` `u64` words). -/
def fullM6HdrTotalWords : Nat := 432

/-- Total unified `FullM6Hdr` byte size (`1152 + 2304 = 3456` bytes). -/
def fullM6HdrTotalBytes : Nat := 3456

/-- Byte size reserved inside `M6HdrExt` / `delayed` for `w2b` (`12 * u32` `decision_rate`). -/
def fullM6W2bReservedBytes : Nat := 48

/-- First `u32` index inside `h->delayed` used by `M6HdrExt` (`del[0..15]` left free for `w2b`). -/
def fullM6DelExtStartU32 : Nat := 16

/-- Total `u32` words spanned inside `h->delayed[0 .. 565]` (`16` reserved + `550` `M6HdrExt`). -/
def fullM6DelTotalU32s : Nat := 566

/-- Minimum `h->delayed_cap` (`3 * 200 = 600 >= 566` `u32` words) to enable `M6HdrExt`. -/
def fullM6DelMinCap : Nat := 200

/-- Initialization magic stored at `del[16..17]` (`"M6TIERS1"`). -/
def fullM6Magic : BitVec 64 := 0x4D36544945525331#64

/-- Number of glue histogram bins per mode (`0..127`, `MAX_GLUE_USED = 127`). -/
def fullM6NumGlueBins : Nat := 128

/-- Delay slot index `0`: `bumpreasons` (upstream `kimits.h`) / `autarky`. -/
def fullM6DelayBumpReasons : Nat := 0

/-- Delay slot index `1`: `congruence`. -/
def fullM6DelayCongruence : Nat := 1

/-- Delay slot index `2`: `sweep` (upstream `kimits.h`) / `eliminate`. -/
def fullM6DelaySweep : Nat := 2

/-- Delay slot index `3`: `vivifyirr` (upstream `kimits.h`) / `vivify`. -/
def fullM6DelayVivifyIrr : Nat := 3

/-- Watermark selector constants for `full_m6_{get,set}_watermark`. -/
def fullM6WmProbeTicks : Nat := 0
def fullM6WmElimTicks : Nat := 1
def fullM6WmReduceConfl : Nat := 2
def fullM6WmReduceTicks : Nat := 3
def fullM6WmRephaseTicks : Nat := 4
def fullM6WmProbingTicks : Nat := 5
def fullM6WmFocusedTicks : Nat := 6
def fullM6WmStableTicks : Nat := 7

/-! ### Exact `M6HdrExt` Struct Byte Offsets (relative to `M6HdrExt` start = byte `1152`) -/

def m6ExtOffMagic : Nat := 0
def m6ExtOffFlags : Nat := 8
def m6ExtOffW2bReserved : Nat := 16
def m6ExtOffTier1 : Nat := 64
def m6ExtOffTier2 : Nat := 80
def m6ExtOffGlueNextConfl : Nat := 96
def m6ExtOffGlueInterval : Nat := 104
def m6ExtOffTotalUsed : Nat := 112
def m6ExtOffDelayCnt : Nat := 128
def m6ExtOffDelayCur : Nat := 160
def m6ExtOffLastProbeTicks : Nat := 192
def m6ExtOffLastElimTicks : Nat := 200
def m6ExtOffLastReduceConfl : Nat := 208
def m6ExtOffLastReduceTicks : Nat := 216
def m6ExtOffLastRephaseTicks : Nat := 224
def m6ExtOffProbingTicks : Nat := 232
def m6ExtOffModeFocusedTicks : Nat := 240
def m6ExtOffModeStableTicks : Nat := 248
def m6ExtOffUsed0 : Nat := 256
def m6ExtOffUsed1 : Nat := 1280

/-! ### Runtime `h->delayed` `u32` Offsets (`del[16 .. 565]`, leaving `del[0..15]` for `w2b`) -/

def m6DelMagicIdx : Nat := 16
def m6DelTier1Base : Nat := 18
def m6DelTier2Base : Nat := 20
def m6DelGlueNextIdx : Nat := 22
def m6DelGlueIntervalIdx : Nat := 24
def m6DelTotalUsed0Idx : Nat := 26
def m6DelTotalUsed1Idx : Nat := 28
def m6DelDelayCntBase : Nat := 30
def m6DelDelayCurBase : Nat := 34
def m6DelWmBase : Nat := 38
def m6DelUsed0Base : Nat := 54
def m6DelUsed1Base : Nat := 310

/-! ## 2. C0 Implementation (`m6Tiers`) -/

kissat_c0! m6Tiers "
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

typedef struct {
  u64 m6_magic;
  u64 m6_flags;
  u64 w2b_delayed_reserved[6];
  u64 tier1[2];
  u64 tier2[2];
  u64 glue_next_confl;
  u64 glue_interval;
  u64 total_used[2];
  u64 delay_cnt[4];
  u64 delay_cur[4];
  u64 last_probe_ticks;
  u64 last_elim_ticks;
  u64 last_reduce_confl;
  u64 last_reduce_ticks;
  u64 last_rephase_ticks;
  u64 probing_ticks;
  u64 mode_focused_ticks;
  u64 mode_stable_ticks;
  u64 used_0[128];
  u64 used_1[128];
} M6HdrExt;

typedef struct {
  FullHdr base;
  M6HdrExt ext;
} FullM6Hdr;

#define FL_ACTIVE             1u
#define PH_GLUE_MASK          0x7FFFFu
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u

#define M6_EXT_MAGIC          0x4D36544945525331ULL
#define M6_DEL_MIN_CAP        200ULL
#define M6_DEL_TOTAL_U32S     566ULL
#define M6_DEL_MAGIC          16ULL
#define M6_DEL_TIER1_BASE     18ULL
#define M6_DEL_TIER2_BASE     20ULL
#define M6_DEL_GLUE_NEXT      22ULL
#define M6_DEL_GLUE_INTV      24ULL
#define M6_DEL_TOTAL_USED0    26ULL
#define M6_DEL_TOTAL_USED1    28ULL
#define M6_DEL_DELAY_CNT      30ULL
#define M6_DEL_DELAY_CUR      34ULL
#define M6_DEL_WM_BASE        38ULL
#define M6_DEL_USED0_BASE     54ULL
#define M6_DEL_USED1_BASE     310ULL

#define M6_GLUE_BINS          128ULL
#define M6_GLUE_INTERVAL_MAX  65536ULL
#define M6_MIN_EFFORT         4000ULL

#define M6_DELAY_BUMPREASONS  0ULL
#define M6_DELAY_AUTARKY      0ULL
#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL
#define M6_DELAY_ELIMINATE    2ULL
#define M6_DELAY_VIVIFYIRR    3ULL
#define M6_DELAY_VIVIFY       3ULL

#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_ELIM_TICKS      1ULL
#define M6_WM_REDUCE_CONFL    2ULL
#define M6_WM_REDUCE_TICKS    3ULL
#define M6_WM_REPHASE_TICKS   4ULL
#define M6_WM_PROBING_TICKS   5ULL
#define M6_WM_FOCUSED_TICKS   6ULL
#define M6_WM_STABLE_TICKS    7ULL

extern u64 full_ilog10(u64 x);
extern void full_heap_down(FullHdr *h, u32 v);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern void full_walk(FullHdr *h);
extern u64 full_reduce(FullHdr *h, bool force);
extern bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var);
extern u64 full_analyze(FullHdr *h);
extern u64 full_substitute(FullHdr *h);
extern u64 full_congruence(FullHdr *h);
extern u64 full_sweep_sat(FullHdr *h);
extern u64 full_transitive(FullHdr *h);
extern u64 full_probe_run(FullHdr *h, u64 budget);
extern u64 full_vivify(FullHdr *h, u64 tier_mode);
extern bool full_enter_dense(FullHdr *h);
extern u64 full_forward_sub(FullHdr *h);
extern u64 full_bve_var(FullHdr *h, u32 v);
extern u64 full_factor(FullHdr *h);
extern u64 full_rebuild_watches(FullHdr *h);

u64 full_m6_hdr_sizeof(void) {
  return sizeof(FullM6Hdr);
}

u64 full_m6_ext_sizeof(void) {
  return sizeof(M6HdrExt);
}

u64 full_m6_get64(u32 *del, u64 idx) {
  return (u64)del[idx] | ((u64)del[idx + 1ULL] << 32);
}

void full_m6_set64(u32 *del, u64 idx, u64 val) {
  del[idx] = (u32)val;
  del[idx + 1ULL] = (u32)(val >> 32);
}

bool full_m6_ext_ready(FullHdr *h) {
  if (h->delayed_cap < M6_DEL_MIN_CAP) { return false; }
  u32 *del = (u32 *)h->delayed;
  if (full_m6_get64(del, M6_DEL_MAGIC) == M6_EXT_MAGIC) { return true; }
  u64 i = 18ULL;
  while (i < M6_DEL_TOTAL_U32S) {
    del[i] = 0u;
    i = i + 1ULL;
  }
  del[M6_DEL_TIER1_BASE] = 2u;
  del[M6_DEL_TIER1_BASE + 1ULL] = 2u;
  del[M6_DEL_TIER2_BASE] = 6u;
  del[M6_DEL_TIER2_BASE + 1ULL] = 6u;
  full_m6_set64(del, M6_DEL_GLUE_INTV, 2ULL);
  full_m6_set64(del, M6_DEL_WM_BASE + 0ULL, h->fwd_sub_cnt);
  full_m6_set64(del, M6_DEL_WM_BASE + 2ULL, h->fwd_str_cnt);
  full_m6_set64(del, M6_DEL_MAGIC, M6_EXT_MAGIC);
  return true;
}

void full_m6_sync_legacy_tiers(FullHdr *h) {
  if (!full_m6_ext_ready(h)) { return; }
  u32 *del = (u32 *)h->delayed;
  u64 t1 = (u64)del[M6_DEL_TIER1_BASE];
  u64 t2 = (u64)del[M6_DEL_TIER2_BASE + 1ULL];
  if (t2 < t1) { t2 = t1; }
  h->tier1 = t1;
  h->tier2 = t2;
}

void full_m6_recompute_tiers_legacy(FullHdr *h) {
  u32 *gu = (u32 *)h->glue_used;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < 64ULL) {
    u64 u = (u64)gu[g];
    if (total <= 0xFFFFFFFFFFFFFFFFULL - u) { total = total + u; }
    else { total = 0xFFFFFFFFFFFFFFFFULL; }
    g = g + 1ULL;
  }
  u64 t1 = 2ULL; u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = (total == 1ULL) ? 1ULL : (total >> 1);
    u64 lim2 = (total == 1ULL) ? 1ULL :
      ((total / 10ULL) * 9ULL + (((total % 10ULL) * 9ULL) / 10ULL));
    u64 acc = 0ULL; bool got1 = false; bool got2 = false;
    g = 0ULL;
    while (g < 64ULL) {
      u64 u = (u64)gu[g];
      if (acc <= 0xFFFFFFFFFFFFFFFFULL - u) { acc = acc + u; }
      else { acc = 0xFFFFFFFFFFFFFFFFULL; }
      if (!got1 && acc >= lim1) { t1 = g; got1 = true; }
      if (!got2 && acc >= lim2) { t2 = g; got2 = true; break; }
      g = g + 1ULL;
    }
    if (!got1) { t1 = 2ULL; t2 = 6ULL; }
    else if (!got2) { t2 = t1; }
  }
  if (t2 < t1) { t2 = t1; }
  h->tier1 = t1; h->tier2 = t2;
}

void full_m6_recompute_tiers_ext(FullHdr *h, u64 mode) {
  u32 *del = (u32 *)h->delayed;
  u64 base = (mode == 0ULL) ? M6_DEL_USED0_BASE : M6_DEL_USED1_BASE;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < M6_GLUE_BINS) {
    u64 u = full_m6_get64(del, base + (g << 1));
    if (total <= 0xFFFFFFFFFFFFFFFFULL - u) { total = total + u; }
    else { total = 0xFFFFFFFFFFFFFFFFULL; }
    g = g + 1ULL;
  }
  full_m6_set64(del, (mode == 0ULL) ? M6_DEL_TOTAL_USED0 : M6_DEL_TOTAL_USED1, total);
  u64 t1 = 2ULL; u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = (total == 1ULL) ? 1ULL : (total >> 1);
    u64 lim2 = (total == 1ULL) ? 1ULL :
      ((total / 10ULL) * 9ULL + (((total % 10ULL) * 9ULL) / 10ULL));
    u64 acc = 0ULL; bool got1 = false; bool got2 = false;
    g = 0ULL;
    while (g < M6_GLUE_BINS) {
      u64 u = full_m6_get64(del, base + (g << 1));
      if (acc <= 0xFFFFFFFFFFFFFFFFULL - u) { acc = acc + u; }
      else { acc = 0xFFFFFFFFFFFFFFFFULL; }
      if (!got1 && acc >= lim1) { t1 = g; got1 = true; }
      if (!got2 && acc >= lim2) { t2 = g; got2 = true; break; }
      g = g + 1ULL;
    }
    if (!got1) { t1 = 2ULL; t2 = 6ULL; }
    else if (!got2) { t2 = t1; }
  }
  if (t2 < t1) { t2 = t1; }
  del[M6_DEL_TIER1_BASE + mode] = (u32)t1;
  del[M6_DEL_TIER2_BASE + mode] = (u32)t2;
  full_m6_sync_legacy_tiers(h);
}

void full_m6_recompute_tiers_mode(FullHdr *h, u64 st) {
  u64 mode = (st != 0ULL) ? 1ULL : 0ULL;
  if (!full_m6_ext_ready(h)) {
    full_m6_recompute_tiers_legacy(h);
    return;
  }
  full_m6_recompute_tiers_ext(h, mode);
}

void full_recompute_tiers_m6(FullHdr *h) {
  full_m6_recompute_tiers_mode(h, (h->stable != 0ULL) ? 1ULL : 0ULL);
}

void full_m6_update_tier_limits(FullHdr *h) {
  if (!full_m6_ext_ready(h)) {
    if (h->conflicts > 0ULL && (h->conflicts & (h->conflicts - 1ULL)) == 0ULL) {
      full_recompute_tiers_m6(h);
    }
    return;
  }
  u32 *del = (u32 *)h->delayed;
  u64 next_c = full_m6_get64(del, M6_DEL_GLUE_NEXT);
  if (h->conflicts > next_c) {
    full_recompute_tiers_m6(h);
    u64 iv = full_m6_get64(del, M6_DEL_GLUE_INTV);
    if (iv == 0ULL) { iv = 2ULL; }
    else if (iv < M6_GLUE_INTERVAL_MAX) { iv = iv << 1; }
    full_m6_set64(del, M6_DEL_GLUE_INTV, iv);
    full_m6_set64(del, M6_DEL_GLUE_NEXT, h->conflicts + iv);
  }
}

void full_m6_record_used(FullHdr *h, u64 glue) {
  if (!full_m6_ext_ready(h)) {
    u32 *gu = (u32 *)h->glue_used;
    u64 gi = (glue > 63ULL) ? 63ULL : glue;
    if (gu[gi] < 0xFFFFFFFFu) { gu[gi] = gu[gi] + 1u; }
    return;
  }
  u32 *del = (u32 *)h->delayed;
  u64 st = (h->stable != 0ULL) ? 1ULL : 0ULL;
  u64 gi = (glue >= M6_GLUE_BINS) ? (M6_GLUE_BINS - 1ULL) : glue;
  u64 base = (st == 0ULL) ? M6_DEL_USED0_BASE : M6_DEL_USED1_BASE;
  u64 u = full_m6_get64(del, base + (gi << 1));
  if (u < 0xFFFFFFFFFFFFFFFFULL) { full_m6_set64(del, base + (gi << 1), u + 1ULL); }
  u64 tu_idx = (st == 0ULL) ? M6_DEL_TOTAL_USED0 : M6_DEL_TOTAL_USED1;
  u64 tu = full_m6_get64(del, tu_idx);
  if (tu < 0xFFFFFFFFFFFFFFFFULL) { full_m6_set64(del, tu_idx, tu + 1ULL); }
}

u64 full_m6_get_tier1(FullHdr *h, bool vivify_mode) {
  if (!full_m6_ext_ready(h)) { return h->tier1; }
  u32 *del = (u32 *)h->delayed;
  u64 st = vivify_mode ? 0ULL : ((h->stable != 0ULL) ? 1ULL : 0ULL);
  return (u64)del[M6_DEL_TIER1_BASE + st];
}

u64 full_m6_get_tier2(FullHdr *h, bool vivify_mode) {
  if (!full_m6_ext_ready(h)) { return h->tier2; }
  u32 *del = (u32 *)h->delayed;
  u64 t1 = (u64)del[M6_DEL_TIER1_BASE];
  u64 st = vivify_mode ? 0ULL : 1ULL;
  u64 t2 = (u64)del[M6_DEL_TIER2_BASE + st];
  return (t2 < t1) ? t1 : t2;
}

bool full_m6_delaying(FullHdr *h, u64 id) {
  if (id >= 4ULL || !full_m6_ext_ready(h)) { return false; }
  u32 *del = (u32 *)h->delayed;
  u32 cnt = del[M6_DEL_DELAY_CNT + id];
  if (cnt > 0u) {
    del[M6_DEL_DELAY_CNT + id] = cnt - 1u;
    return true;
  }
  return false;
}

void full_m6_bump_delay(FullHdr *h, u64 id) {
  if (id >= 4ULL || !full_m6_ext_ready(h)) { return; }
  u32 *del = (u32 *)h->delayed;
  u32 cur = del[M6_DEL_DELAY_CUR + id];
  if (cur < 0xFFFFFFFFu) { cur = cur + 1u; }
  del[M6_DEL_DELAY_CUR + id] = cur;
  del[M6_DEL_DELAY_CNT + id] = cur;
}

void full_m6_reduce_delay(FullHdr *h, u64 id) {
  if (id >= 4ULL || !full_m6_ext_ready(h)) { return; }
  u32 *del = (u32 *)h->delayed;
  u32 cur = del[M6_DEL_DELAY_CUR + id] >> 1;
  del[M6_DEL_DELAY_CUR + id] = cur;
  del[M6_DEL_DELAY_CNT + id] = cur;
}

void full_m6_reset_delay(FullHdr *h, u64 id) {
  if (id >= 4ULL || !full_m6_ext_ready(h)) { return; }
  u32 *del = (u32 *)h->delayed;
  del[M6_DEL_DELAY_CUR + id] = 0u;
  del[M6_DEL_DELAY_CNT + id] = 0u;
}

u64 full_m6_get_watermark(FullHdr *h, u64 kind) {
  if (kind >= 8ULL) { return 0ULL; }
  if (!full_m6_ext_ready(h)) {
    if (kind == M6_WM_PROBE_TICKS) { return h->fwd_sub_cnt; }
    if (kind == M6_WM_ELIM_TICKS) { return h->fwd_str_cnt; }
    return 0ULL;
  }
  u32 *del = (u32 *)h->delayed;
  return full_m6_get64(del, M6_DEL_WM_BASE + (kind << 1));
}

void full_m6_set_watermark(FullHdr *h, u64 kind, u64 val) {
  if (kind >= 8ULL) { return; }
  if (!full_m6_ext_ready(h)) {
    if (kind == M6_WM_PROBE_TICKS) { h->fwd_sub_cnt = val; }
    else if (kind == M6_WM_ELIM_TICKS) { h->fwd_str_cnt = val; }
    return;
  }
  u32 *del = (u32 *)h->delayed;
  full_m6_set64(del, M6_DEL_WM_BASE + (kind << 1), val);
}

void full_m6_add_ticks(FullHdr *h, u64 ticks) {
  if (h->probing != 0ULL) {
    if (full_m6_ext_ready(h)) {
      u64 pt = full_m6_get_watermark(h, M6_WM_PROBING_TICKS);
      full_m6_set_watermark(h, M6_WM_PROBING_TICKS, pt + ticks);
    }
    return;
  }
  h->search_ticks = h->search_ticks + ticks;
  if (full_m6_ext_ready(h)) {
    u64 mk = (h->stable != 0ULL) ? M6_WM_STABLE_TICKS : M6_WM_FOCUSED_TICKS;
    u64 cur = full_m6_get_watermark(h, mk);
    full_m6_set_watermark(h, mk, cur + ticks);
  }
}

u64 full_log10_q16_m6(u64 x) {
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

u64 full_scale_delta_m6(FullHdr *h, u64 delta) {
  u64 clauses = h->num_irred + h->num_binary;
  u64 l = full_log10_q16_m6(clauses + 10ULL);
  if (l < 65536ULL) { l = 65536ULL; }
  u64 l2 = (l * l) >> 16;
  u64 dlim = (delta > 1000000000ULL) ? 1000000000ULL : delta;
  return (dlim * l2) >> 16;
}

u64 full_probe_dticks_m6(FullHdr *h, bool initial) {
  u64 clauses = h->num_irred + h->num_binary;
  u64 last_p = full_m6_get_watermark(h, M6_WM_PROBE_TICKS);
  u64 raw = (h->search_ticks > last_p) ? (h->search_ticks - last_p) : 0ULL;
  u64 dticks = initial ? ((h->cur_vars + clauses) * 8ULL) : raw;
  return (dticks > M6_MIN_EFFORT) ? dticks : M6_MIN_EFFORT;
}

u64 full_elim_dticks_m6(FullHdr *h, bool initial) {
  if (initial) { return (h->cur_vars + h->num_irred + h->num_binary) * 12ULL; }
  u64 last_e = full_m6_get_watermark(h, M6_WM_ELIM_TICKS);
  return (h->search_ticks > last_e) ? (h->search_ticks - last_e) : 0ULL;
}

void full_switch_mode_m6(FullHdr *h) {
  if (h->stable == 0ULL) {
    if (h->conflicts < h->mode_confl_lim) { return; }
    h->stable = 1ULL;
    u64 dticks = (h->search_ticks > h->mode_saved_ticks) ?
      (h->search_ticks - h->mode_saved_ticks) : 0ULL;
    if (full_m6_ext_ready(h)) {
      u64 ft = full_m6_get_watermark(h, M6_WM_FOCUSED_TICKS);
      full_m6_set_watermark(h, M6_WM_FOCUSED_TICKS, ft + dticks);
    }
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
    h->stable = 0ULL;
    u64 dticks = (h->search_ticks > h->mode_saved_ticks) ?
      (h->search_ticks - h->mode_saved_ticks) : 0ULL;
    if (full_m6_ext_ready(h)) {
      u64 st = full_m6_get_watermark(h, M6_WM_STABLE_TICKS);
      full_m6_set_watermark(h, M6_WM_STABLE_TICKS, st + dticks);
    }
    u64 cnt = (h->switched >> 1) + 1ULL;
    u64 cc = (cnt < 1000000000000ULL) ? cnt : 1000000000000ULL;
    u64 q = full_log10_q16_m6(cc + 9ULL);
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
  h->ema_fast_biased = 0ULL;
  h->ema_fast_exp = 1ULL << 32;
  h->ema_slow_biased = 0ULL;
  h->ema_slow_exp = 1ULL << 32;
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

void full_rephase_m6(FullHdr *h) {
  if (h->stable == 0ULL) {
    h->rephase_limit = h->mode_confl_lim;
    return;
  }
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  h->rephased = h->rephased + 1ULL;
  u64 sel = h->rephased & 3ULL;
  u64 cv = h->cur_vars;
  i8 *ph = (i8 *)h->phases;
  i8 *pt = (i8 *)h->phases_target;
  i8 *pb = (i8 *)h->phases_best;
  if (sel == 0ULL) {
    u64 k = 0ULL;
    while (k < cv) {
      if (pb[k] != (i8)0) { ph[k] = pb[k]; }
      k = k + 1ULL;
    }
    h->best_assigned = 0ULL;
  } else if (sel == 1ULL) {
    full_walk(h);
  } else if (sel == 2ULL) {
    u64 k = 0ULL;
    while (k < cv) { ph[k] = (i8)1; k = k + 1ULL; }
  } else {
    u64 k = 0ULL;
    while (k < cv) { ph[k] = (i8)(-1); k = k + 1ULL; }
  }
  u64 k2 = 0ULL;
  while (k2 < cv) { pt[k2] = ph[k2]; k2 = k2 + 1ULL; }
  h->target_assigned = 0ULL;
  u64 n = h->rephased;
  u64 nc = (n < 1000000000000ULL) ? n : 1000000000000ULL;
  u64 q = full_log10_q16_m6(nc + 9ULL);
  u64 l2 = (q * q) >> 16;
  u64 l3 = (l2 * q) >> 16;
  u64 scaled = 0ULL;
  if (n <= 1000000ULL) {
    scaled = (1000ULL * n * l3) >> 16;
  } else {
    u64 nlim = (n > 100000000ULL) ? 100000000ULL : n;
    scaled = ((1000ULL * nlim) >> 16) * l3;
  }
  h->rephase_limit = h->conflicts + scaled;
  full_m6_set_watermark(h, M6_WM_REPHASE_TICKS, h->search_ticks);
}

u64 full_reduce_m6(FullHdr *h, bool force) {
  full_recompute_tiers_m6(h);
  u64 rr = full_reduce(h, force);
  full_m6_set_watermark(h, M6_WM_REDUCE_CONFL, h->conflicts);
  full_m6_set_watermark(h, M6_WM_REDUCE_TICKS, h->search_ticks);
  return rr;
}

bool full_analyze_rsn_m6(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) == 0u && (u64)rsn + 3ULL <= h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    u32 hdr = ar[rsn];
    u32 sz = ar[(u64)rsn + 2ULL];
    if (sz >= 3u && (u64)rsn + 3ULL + (u64)sz <= h->arena_len && (hdr & PH_RED) != 0u) {
      full_m6_record_used(h, (u64)(hdr & PH_GLUE_MASK));
    }
  }
  return full_analyze_rsn(h, rsn, skip_var);
}

u64 full_analyze_m6(FullHdr *h) {
  full_m6_update_tier_limits(h);
  return full_analyze(h);
}

u64 full_probe_m6(FullHdr *h, bool initial) {
  if (!initial && full_m6_ext_ready(h) &&
      full_m6_get_watermark(h, M6_WM_REDUCE_CONFL) == h->conflicts) {
    return 1ULL;
  }
  u64 dticks = full_probe_dticks_m6(h, initial);
  if (!initial) {
    h->probings = h->probings + 1ULL;
    u64 logp = full_ilog10(h->probings + 9ULL);
    h->probe_limit = h->conflicts + full_scale_delta_m6(h, 120ULL * h->probings * logp);
  }
  h->probing = 1ULL;
  if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
    h->probing = 0ULL; return 20ULL;
  }
  bool do_dense = (h->num_binary >= 4ULL && (initial || h->num_binary * 3ULL >= h->num_irred));
  if (do_dense) {
    if (!full_m6_delaying(h, M6_DELAY_CONGRUENCE)) {
      u64 cb = h->cong_cnt;
      u64 cr = full_congruence(h);
      if (cr == 20ULL) { h->probing = 0ULL; return 20ULL; }
      if ((h->cong_cnt > cb) && (h->cong_cnt - cb) * 1000ULL >= h->unassigned) {
        full_m6_reduce_delay(h, M6_DELAY_CONGRUENCE);
      } else {
        full_m6_bump_delay(h, M6_DELAY_CONGRUENCE);
      }
    }
    if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
      h->probing = 0ULL; return 20ULL;
    }
    if (!full_m6_delaying(h, M6_DELAY_SWEEP)) {
      u64 sb = h->sweep_cnt;
      u64 sr = full_sweep_sat(h);
      if (sr == 20ULL) { h->probing = 0ULL; return 20ULL; }
      if ((h->sweep_cnt > sb) && (h->sweep_cnt - sb) * 1000ULL >= h->unassigned) {
        full_m6_reduce_delay(h, M6_DELAY_SWEEP);
      } else {
        full_m6_bump_delay(h, M6_DELAY_SWEEP);
      }
    }
  }
  if (h->num_binary > 0ULL && full_substitute(h) == 20ULL) {
    h->probing = 0ULL; return 20ULL;
  }
  if (!initial) {
    if (h->num_binary > 0ULL && full_transitive(h) == 20ULL) {
      h->probing = 0ULL; return 20ULL;
    }
    u64 pbud = 8ULL + (dticks >> 10);
    if (pbud > 64ULL) { pbud = 64ULL; }
    if (h->num_binary > 0ULL && full_probe_run(h, pbud) == 20ULL) {
      h->probing = 0ULL; return 20ULL;
    }
    if (full_vivify(h, 1ULL) == 20ULL) { h->probing = 0ULL; return 20ULL; }
    if (full_vivify(h, 2ULL) == 20ULL) { h->probing = 0ULL; return 20ULL; }
    if (!full_m6_delaying(h, M6_DELAY_VIVIFYIRR)) {
      u64 vb = h->viv_cnt;
      u64 vr = full_vivify(h, 0ULL);
      if (vr == 20ULL) { h->probing = 0ULL; return 20ULL; }
      if (h->viv_cnt > vb) {
        full_m6_reduce_delay(h, M6_DELAY_VIVIFYIRR);
      } else {
        full_m6_bump_delay(h, M6_DELAY_VIVIFYIRR);
      }
    }
  } else if (h->cur_level > 0ULL) {
    full_backtrack(h, 0ULL);
  }
  h->probing = 0ULL;
  full_m6_set_watermark(h, M6_WM_PROBE_TICKS, h->search_ticks);
  return 1ULL;
}

u64 full_probe(FullHdr *h) {
  return full_probe_m6(h, false);
}

u64 full_elim_bve_m6(FullHdr *h, u64 bve_lim) {
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u64 cv = h->cur_vars;
  u64 v = 0ULL;
  u64 tried = 0ULL;
  u64 res = 1ULL;
  while (v < cv && tried < bve_lim && h->oom == 0ULL && h->fuel > 0ULL) {
    if ((fl[v] & (FL_ACTIVE | 16u)) == (FL_ACTIVE | 16u) && vals[v << 1] == (i8)0) {
      fl[v] = fl[v] & (~16u);
      tried = tried + 1ULL;
      u64 br = full_bve_var(h, (u32)v);
      if (br == 20ULL) { res = 20ULL; break; }
      if (br == 2ULL) { break; }
    }
    v = v + 1ULL;
  }
  return res;
}

u64 full_eliminate_m6(FullHdr *h, bool initial) {
  if (!initial && full_m6_ext_ready(h) &&
      full_m6_get_watermark(h, M6_WM_REDUCE_CONFL) == h->conflicts) {
    return 1ULL;
  }
  u64 dticks = full_elim_dticks_m6(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 loge = full_ilog10(h->eliminations + 9ULL);
    h->elim_limit = h->conflicts + full_scale_delta_m6(h, 250ULL * h->eliminations * loge);
    if (h->eliminations >= 2ULL && h->elim_bound < 8ULL) {
      h->elim_bound = h->elim_bound + 2ULL;
    }
  }
  if (!full_enter_dense(h)) {
    full_m6_set_watermark(h, M6_WM_ELIM_TICKS, h->search_ticks);
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fs = full_forward_sub(h);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) { full_rebuild_watches(h); return 20ULL; }
  u64 bve_lim = initial ? (h->cur_vars + 256ULL) : (64ULL + (dticks >> 7));
  if (bve_lim > h->cur_vars) { bve_lim = h->cur_vars; }
  u64 res = full_elim_bve_m6(h, bve_lim);
  if (res == 1ULL && (h->num_binary > 0ULL || h->num_irred <= 1024ULL)) {
    full_factor(h);
  }
  u64 rr = full_rebuild_watches(h);
  full_m6_set_watermark(h, M6_WM_ELIM_TICKS, h->search_ticks);
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_eliminate(FullHdr *h) {
  return full_eliminate_m6(h, false);
}
"

/-- External canonical `FullSpec` callees referenced by `m6Tiers_fns` (`18` fns). -/
def m6TiersExterns : List Extern :=
  [ ⟨"full_ilog10", [i64], [i64]⟩
  , ⟨"full_heap_down", [i64, i32], []⟩
  , ⟨"full_backtrack", [i64, i64], []⟩
  , ⟨"full_walk", [i64], []⟩
  , ⟨"full_reduce", [i64, .bool], [i64]⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool]⟩
  , ⟨"full_analyze", [i64], [i64]⟩
  , ⟨"full_substitute", [i64], [i64]⟩
  , ⟨"full_congruence", [i64], [i64]⟩
  , ⟨"full_sweep_sat", [i64], [i64]⟩
  , ⟨"full_transitive", [i64], [i64]⟩
  , ⟨"full_probe_run", [i64, i64], [i64]⟩
  , ⟨"full_vivify", [i64, i64], [i64]⟩
  , ⟨"full_enter_dense", [i64], [.bool]⟩
  , ⟨"full_forward_sub", [i64], [i64]⟩
  , ⟨"full_bve_var", [i64, i32], [i64]⟩
  , ⟨"full_factor", [i64], [i64]⟩
  , ⟨"full_rebuild_watches", [i64], [i64]⟩ ]

/-- Drop-in replacement `Fn` handles for future `FullM6` unification. -/
def m6RecomputeTiersFn : Fn := ⟨"full_recompute_tiers", [i64], [], full_recompute_tiers_m6_body⟩
def m6SwitchModeFn : Fn := ⟨"full_switch_mode", [i64], [], full_switch_mode_m6_body⟩
def m6RephaseFn : Fn := ⟨"full_rephase", [i64], [], full_rephase_m6_body⟩
def m6ReduceFn : Fn := ⟨"full_reduce", [i64, .bool], [i64], full_reduce_m6_body⟩
def m6AnalyzeRsnFn : Fn := ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], full_analyze_rsn_m6_body⟩
def m6AnalyzeFn : Fn := ⟨"full_analyze", [i64], [i64], full_analyze_m6_body⟩
def m6ProbeFn : Fn := ⟨"full_probe", [i64], [i64], full_probe_body⟩
def m6EliminateFn : Fn := ⟨"full_eliminate", [i64], [i64], full_eliminate_body⟩

/-- Standalone Wave-2 `PR-W2A` module (`35` functions + `18` externs, `0` exits). -/
def m6TiersModule : LeanQbe.T.Module :=
  { fns := m6Tiers_fns, externs := m6TiersExterns, exits := [] }

theorem full_m6_hdr_sizeof_wf : Func.Wf full_m6_hdr_sizeof_body := by t_wf_reify
theorem full_m6_ext_sizeof_wf : Func.Wf full_m6_ext_sizeof_body := by t_wf_reify
theorem full_m6_get64_wf : Func.Wf full_m6_get64_body := by t_wf_reify
theorem full_m6_set64_wf : Func.Wf full_m6_set64_body := by t_wf_reify
theorem full_m6_ext_ready_wf : Func.Wf full_m6_ext_ready_body := by t_wf_reify
theorem full_m6_sync_legacy_tiers_wf : Func.Wf full_m6_sync_legacy_tiers_body := by t_wf_reify
theorem full_m6_recompute_tiers_legacy_wf :
    Func.Wf full_m6_recompute_tiers_legacy_body := by t_wf_reify
theorem full_m6_recompute_tiers_ext_wf :
    Func.Wf full_m6_recompute_tiers_ext_body := by t_wf_reify
theorem full_m6_recompute_tiers_mode_wf :
    Func.Wf full_m6_recompute_tiers_mode_body := by t_wf_reify
theorem full_recompute_tiers_m6_wf : Func.Wf full_recompute_tiers_m6_body := by t_wf_reify
theorem full_m6_update_tier_limits_wf : Func.Wf full_m6_update_tier_limits_body := by t_wf_reify
theorem full_m6_record_used_wf : Func.Wf full_m6_record_used_body := by t_wf_reify
theorem full_m6_get_tier1_wf : Func.Wf full_m6_get_tier1_body := by t_wf_reify
theorem full_m6_get_tier2_wf : Func.Wf full_m6_get_tier2_body := by t_wf_reify
theorem full_m6_delaying_wf : Func.Wf full_m6_delaying_body := by t_wf_reify
theorem full_m6_bump_delay_wf : Func.Wf full_m6_bump_delay_body := by t_wf_reify
theorem full_m6_reduce_delay_wf : Func.Wf full_m6_reduce_delay_body := by t_wf_reify
theorem full_m6_reset_delay_wf : Func.Wf full_m6_reset_delay_body := by t_wf_reify
theorem full_m6_get_watermark_wf : Func.Wf full_m6_get_watermark_body := by t_wf_reify
theorem full_m6_set_watermark_wf : Func.Wf full_m6_set_watermark_body := by t_wf_reify
theorem full_m6_add_ticks_wf : Func.Wf full_m6_add_ticks_body := by t_wf_reify
theorem full_log10_q16_m6_wf : Func.Wf full_log10_q16_m6_body := by t_wf_reify
theorem full_scale_delta_m6_wf : Func.Wf full_scale_delta_m6_body := by t_wf_reify
theorem full_probe_dticks_m6_wf : Func.Wf full_probe_dticks_m6_body := by t_wf_reify
theorem full_elim_dticks_m6_wf : Func.Wf full_elim_dticks_m6_body := by t_wf_reify
theorem full_switch_mode_m6_wf : Func.Wf full_switch_mode_m6_body := by t_wf_reify
theorem full_rephase_m6_wf : Func.Wf full_rephase_m6_body := by t_wf_reify
theorem full_reduce_m6_wf : Func.Wf full_reduce_m6_body := by t_wf_reify
theorem full_analyze_rsn_m6_wf : Func.Wf full_analyze_rsn_m6_body := by t_wf_reify
theorem full_analyze_m6_wf : Func.Wf full_analyze_m6_body := by t_wf_reify
theorem full_probe_m6_wf : Func.Wf full_probe_m6_body := by t_wf_reify
theorem full_probe_wf : Func.Wf full_probe_body := by t_wf_reify
theorem full_elim_bve_m6_wf : Func.Wf full_elim_bve_m6_body := by t_wf_reify
theorem full_eliminate_m6_wf : Func.Wf full_eliminate_m6_body := by t_wf_reify
theorem full_eliminate_wf : Func.Wf full_eliminate_body := by t_wf_reify

theorem m6Tiers_fns_wf : ∀ f ∈ m6Tiers_fns, f.Wf := by
  simp only [m6Tiers_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_m6_hdr_sizeof_wf, full_m6_ext_sizeof_wf, full_m6_get64_wf, full_m6_set64_wf,
    full_m6_ext_ready_wf, full_m6_sync_legacy_tiers_wf, full_m6_recompute_tiers_legacy_wf,
    full_m6_recompute_tiers_ext_wf, full_m6_recompute_tiers_mode_wf,
    full_recompute_tiers_m6_wf, full_m6_update_tier_limits_wf, full_m6_record_used_wf,
    full_m6_get_tier1_wf, full_m6_get_tier2_wf, full_m6_delaying_wf, full_m6_bump_delay_wf,
    full_m6_reduce_delay_wf, full_m6_reset_delay_wf, full_m6_get_watermark_wf,
    full_m6_set_watermark_wf, full_m6_add_ticks_wf, full_log10_q16_m6_wf,
    full_scale_delta_m6_wf, full_probe_dticks_m6_wf, full_elim_dticks_m6_wf,
    full_switch_mode_m6_wf, full_rephase_m6_wf, full_reduce_m6_wf,
    full_analyze_rsn_m6_wf, full_analyze_m6_wf, full_probe_m6_wf, full_probe_wf,
    full_elim_bve_m6_wf, full_eliminate_m6_wf, full_eliminate_wf⟩

theorem m6Tiers_acyclic : m6TiersModule.checkAcyclic = true := by t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6Tiers
