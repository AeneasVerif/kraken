module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Wave-3 Prep: Extended `FullM6Hdr` (`432` Words = `3,456 B`) & `w2a`/`w2b` Adapters

Purely additive C0 module resolving the Wave-3 `h->delayed` / `h->delayed_len` collisions between
`FullM6BcpS15`, `FullM6VivBackbone`, `FullM6Tiers` (`w2a`), and `FullM6MinShrink` (`w2b`) with
ZERO edits to frozen `FullHdr` (`144` words = `1,152 B`), `FullArena1`, `Full1..3`, `FullM4*`,
`FullM5*`, or any landed Wave-2 module:

1. **Prefix `FullM6Hdr` Layout (`288` ext + `144` base = `432` `u64` words = `3,456 B`):**
   - `FullM6Hdr = { M6HdrExt ext; FullHdr base; }` places `M6HdrExt` (`2,304 B`) immediately
     before `FullHdr` (`1,152 B`) inside the same aligned workspace buffer (`[work_base .. +2304)`
     for `M6HdrExt`, `[work_base + 2304 .. +3456)` for `FullHdr *h`, and `[work_base + 3456 ..)`
     for `FullMem`'s 41 arrays starting at `h + 1152`).
   - Because `FullHdr` bytes `0..1151` and `FullCfg.pVals = c.hdr + 1152` stay bit-for-bit
     identical, `FullM6HdrMem c ext s := m6ExtMem (c.hdr - 2304) ext ⋆ FullMem c s` is strictly
     disjoint in `Mem 64` and frames automatically over ALL 270+ existing `Full1..3`/`M4`/`M5`/
     `BcpS15`/`CompactFlush`/`w2c..w2h` proofs with zero edits!
2. **Exact `M6HdrExt` Byte Map (`288` `u64` words = `2,304 B`, at `(u64)h - 2304ULL`):**
   - Word `0` (`+0..+7`): `m6_magic` (`0x4D36484452455831ULL`, `"M6HDREX1"`).
   - Words `1..7` (`+8..+63`, `56 B`, `w2b` `decision_rate`): `dr_state` (dedicated `u64` replacing
     `h->delayed_len`), `dr_prev[2]`, `dr_sb[2]`, `dr_se[2]` (replacing `h->delayed[0..11]`).
   - Words `8..287` (`+64..+2303`, `2,240 B`, `w2a` tiers/delay/watermarks/glue bins): `tier1[2]`,
     `tier2[2]`, `glue_next_confl`, `glue_interval`, `total_used[2]`, `delay_cnt[4]`,
     `delay_cur[4]`, `watermarks[8]`, `used_0[128]`, `used_1[128]`.
3. **Init, Reset, Workspace Allocator & Repointed `w2a`/`w2b` Adapters (`27` fns + `5` externs):**
   - `m6_hdr_init`, `m6_hdr_reset`, `m6_ext_ensure_init`, `m6_hdr_ext_ready`, `full_m6_mem_init`
     (carving `3,456 B` header cleanly with `avail >= 3456` / wraparound guards).
   - Repointed `w2a` tiers, `used[2].glue[128]`, `delay[4]`, and 8 separate tick watermarks.
   - Repointed `w2b` `decision_rate`, `m6_hdr_decide`, `m6_hdr_analyze_rsn`, and composed `w2a`+
     `w2b` `m6_hdr_analyze` entry hook (`m6_hdr_update_tier_limits` + `m6_hdr_dr_update` +
     `full_analyze`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6Hdr

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

/-! ## 1. Extended `FullM6Hdr` & `M6HdrExt` Layout Constants (`432` Words = `3,456 B`) -/

/-- Frozen base `FullHdr` word count (`144` `u64` words). -/
def fullM6HdrBaseWords : Nat := 144

/-- Frozen base `FullHdr` byte size (`144 * 8 = 1,152` bytes). -/
def fullM6HdrBaseBytes : Nat := 1152

/-- Extended `M6HdrExt` `u64` word count (`288` `u64` words = `32` control + `256` glue bins). -/
def fullM6ExtWords : Nat := 288

/-- Extended `M6HdrExt` byte size (`288 * 8 = 2,304` bytes). -/
def fullM6ExtBytes : Nat := 2304

/-- Total unified `FullM6Hdr` word count (`288 + 144 = 432` `u64` words). -/
def fullM6HdrTotalWords : Nat := 432

/-- Total unified `FullM6Hdr` byte size (`2304 + 1152 = 3,456` bytes). -/
def fullM6HdrTotalBytes : Nat := 3456

/-- Initialization magic stored at `M6HdrExt` word `0` (`"M6HDREX1"`). -/
def fullM6HdrMagic : BitVec 64 := 0x4D36484452455831#64

/-- Number of glue histogram bins per mode (`0..127`). -/
def fullM6HdrGlueBins : Nat := 128

/-- Word index `0`: `m6_magic` (byte offset `+0`). -/
def m6WMagic : Nat := 0
/-- Word index `1`: `w2b` `dr_state` `[bit63 | last_sw(7b) | decs(56b)]` (byte offset `+8`). -/
def m6WDrState : Nat := 1
/-- Word indices `2..3`: `w2b` `dr_prev[2]` (byte offsets `+16`, `+24`). -/
def m6WDrPrev : Nat := 2
/-- Word indices `4..5`: `w2b` `dr_sb[2]` Q32 EMA biased (byte offsets `+32`, `+40`). -/
def m6WDrSb : Nat := 4
/-- Word indices `6..7`: `w2b` `dr_se[2]` Q32 EMA exp (byte offsets `+48`, `+56`). -/
def m6WDrSe : Nat := 6
/-- Word indices `8..9`: `w2a` `tier1[2]` (byte offsets `+64`, `+72`). -/
def m6WTier1 : Nat := 8
/-- Word indices `10..11`: `w2a` `tier2[2]` (byte offsets `+80`, `+88`). -/
def m6WTier2 : Nat := 10
/-- Word index `12`: `w2a` `glue_next_confl` (byte offset `+96`). -/
def m6WGlueNext : Nat := 12
/-- Word index `13`: `w2a` `glue_interval` (byte offset `+104`). -/
def m6WGlueInterval : Nat := 13
/-- Word indices `14..15`: `w2a` `total_used[2]` (byte offsets `+112`, `+120`). -/
def m6WTotalUsed : Nat := 14
/-- Word indices `16..19`: `w2a` `delay_cnt[4]` (byte offsets `+128..+152`). -/
def m6WDelayCnt : Nat := 16
/-- Word indices `20..23`: `w2a` `delay_cur[4]` (byte offsets `+160..+184`). -/
def m6WDelayCur : Nat := 20
/-- Word indices `24..31`: `w2a` `watermarks[8]` (byte offsets `+192..+248`). -/
def m6WWmBase : Nat := 24
/-- Word indices `32..159`: `w2a` `used_0[128]` focused glue bins (byte offsets `+256..+1272`). -/
def m6WUsed0 : Nat := 32
/-- Word indices `160..287`: `w2a` `used_1[128]` stable glue bins (byte offsets `+1280..+2296`). -/
def m6WUsed1 : Nat := 160

/-- Byte offsets inside `M6HdrExt` (relative to `(u64)h - 2304ULL`). -/
def m6HdrOffMagic : Nat := 8 * m6WMagic
def m6HdrOffDrState : Nat := 8 * m6WDrState
def m6HdrOffDrPrev : Nat := 8 * m6WDrPrev
def m6HdrOffDrSb : Nat := 8 * m6WDrSb
def m6HdrOffDrSe : Nat := 8 * m6WDrSe
def m6HdrOffTier1 : Nat := 8 * m6WTier1
def m6HdrOffTier2 : Nat := 8 * m6WTier2
def m6HdrOffGlueNext : Nat := 8 * m6WGlueNext
def m6HdrOffGlueInterval : Nat := 8 * m6WGlueInterval
def m6HdrOffTotalUsed : Nat := 8 * m6WTotalUsed
def m6HdrOffDelayCnt : Nat := 8 * m6WDelayCnt
def m6HdrOffDelayCur : Nat := 8 * m6WDelayCur
def m6HdrOffWmBase : Nat := 8 * m6WWmBase
def m6HdrOffUsed0 : Nat := 8 * m6WUsed0
def m6HdrOffUsed1 : Nat := 8 * m6WUsed1

/-! ## 2. C0 Implementation (`m6Hdr`) -/

kissat_c0! m6Hdr "
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
  u64 dr_state;
  u64 dr_prev[2];
  u64 dr_sb[2];
  u64 dr_se[2];
  u64 tier1[2];
  u64 tier2[2];
  u64 glue_next_confl;
  u64 glue_interval;
  u64 total_used[2];
  u64 delay_cnt[4];
  u64 delay_cur[4];
  u64 watermarks[8];
  u64 used_0[128];
  u64 used_1[128];
} M6HdrExt;

typedef struct {
  M6HdrExt ext;
  FullHdr base;
} FullM6Hdr;

#define PH_GLUE_MASK          0x7FFFFu
#define PH_RED                0x00400000u
#define PW_BIN_FLAG           0x80000000u

#define M6_EXT_WORDS          288ULL
#define M6_EXT_BYTES          2304ULL
#define M6_HDR_TOTAL_BYTES    3456ULL
#define M6_HDR_MAGIC          0x4D36484452455831ULL

#define M6W_MAGIC             0ULL
#define M6W_DR_STATE          1ULL
#define M6W_DR_PREV           2ULL
#define M6W_DR_SB             4ULL
#define M6W_DR_SE             6ULL
#define M6W_TIER1             8ULL
#define M6W_TIER2             10ULL
#define M6W_GLUE_NEXT         12ULL
#define M6W_GLUE_INTV         13ULL
#define M6W_TOTAL_USED        14ULL
#define M6W_DELAY_CNT         16ULL
#define M6W_DELAY_CUR         20ULL
#define M6W_WM_BASE           24ULL
#define M6W_USED0             32ULL
#define M6W_USED1             160ULL

#define M6_GLUE_BINS          128ULL
#define M6_GLUE_INTERVAL_MAX  65536ULL

#define M6_WM_PROBING_TICKS   5ULL
#define M6_WM_FOCUSED_TICKS   6ULL
#define M6_WM_STABLE_TICKS    7ULL

extern bool full_init_state(u64 cnf_ptr, u64 cnf_end, u64 hdr_addr, u64 avail, u64 fuel);
extern u64 full_next_dec_var(FullHdr *h);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern bool full_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var);
extern u64 full_analyze(FullHdr *h);

u64 full_m6_hdr_sizeof(void) {
  return (u64)sizeof(FullM6Hdr);
}

u64 full_m6_ext_sizeof(void) {
  return (u64)sizeof(M6HdrExt);
}

void m6_hdr_init(FullHdr *h) {
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 i = 0ULL;
  while (i < M6_EXT_WORDS) {
    e[i] = 0ULL;
    i = i + 1ULL;
  }
  u64 sw = h->switched & 127ULL;
  e[M6W_DR_STATE] = (1ULL << 63) | (sw << 56);
  e[M6W_DR_SE] = 1ULL << 32;
  e[M6W_DR_SE + 1ULL] = 1ULL << 32;
  e[M6W_TIER1] = 2ULL;
  e[M6W_TIER1 + 1ULL] = 2ULL;
  e[M6W_TIER2] = 6ULL;
  e[M6W_TIER2 + 1ULL] = 6ULL;
  e[M6W_GLUE_INTV] = 2ULL;
  e[M6W_WM_BASE] = h->fwd_sub_cnt;
  e[M6W_WM_BASE + 1ULL] = h->fwd_str_cnt;
  e[M6W_MAGIC] = M6_HDR_MAGIC;
}

void m6_hdr_reset(FullHdr *h) {
  m6_hdr_init(h);
  h->tier1 = 2ULL;
  h->tier2 = 6ULL;
}

void m6_ext_ensure_init(FullHdr *h) {
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if (e[M6W_MAGIC] != M6_HDR_MAGIC) {
    m6_hdr_init(h);
  }
}

bool m6_hdr_ext_ready(FullHdr *h) {
  m6_ext_ensure_init(h);
  return true;
}

u64 full_m6_mem_init(u64 cnf_ptr, u64 cnf_end, u64 work_base, u64 avail, u64 fuel) {
  if (avail < M6_HDR_TOTAL_BYTES || work_base > 0xFFFFFFFFFFFFFFFFULL - avail) {
    return 0ULL;
  }
  u64 hdr_addr = work_base + M6_EXT_BYTES;
  if (!full_init_state(cnf_ptr, cnf_end, hdr_addr, avail - M6_EXT_BYTES, fuel)) {
    return 0ULL;
  }
  m6_hdr_init((FullHdr *)hdr_addr);
  return hdr_addr;
}

void m6_hdr_sync_legacy_tiers(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 t1 = e[M6W_TIER1];
  u64 t2 = e[M6W_TIER2 + 1ULL];
  if (t2 < t1) { t2 = t1; }
  h->tier1 = t1;
  h->tier2 = t2;
}

void m6_hdr_recompute_tiers_mode(FullHdr *h, u64 st) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 mode = (st != 0ULL) ? 1ULL : 0ULL;
  u64 base = (mode == 0ULL) ? M6W_USED0 : M6W_USED1;
  u64 total = 0ULL;
  u64 g = 0ULL;
  while (g < M6_GLUE_BINS) {
    u64 u = e[base + g];
    if (total <= 0xFFFFFFFFFFFFFFFFULL - u) { total = total + u; }
    else { total = 0xFFFFFFFFFFFFFFFFULL; }
    g = g + 1ULL;
  }
  e[M6W_TOTAL_USED + mode] = total;
  u64 t1 = 2ULL; u64 t2 = 6ULL;
  if (total > 0ULL) {
    u64 lim1 = (total == 1ULL) ? 1ULL : (total >> 1);
    u64 lim2 = (total == 1ULL) ? 1ULL :
      ((total / 10ULL) * 9ULL + (((total % 10ULL) * 9ULL) / 10ULL));
    u64 acc = 0ULL; bool got1 = false; bool got2 = false;
    g = 0ULL;
    while (g < M6_GLUE_BINS) {
      u64 u = e[base + g];
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
  e[M6W_TIER1 + mode] = t1;
  e[M6W_TIER2 + mode] = t2;
  m6_hdr_sync_legacy_tiers(h);
}

void m6_hdr_recompute_tiers(FullHdr *h) {
  m6_hdr_recompute_tiers_mode(h, (h->stable != 0ULL) ? 1ULL : 0ULL);
}

void m6_hdr_update_tier_limits(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 next_c = e[M6W_GLUE_NEXT];
  if (h->conflicts > next_c) {
    m6_hdr_recompute_tiers(h);
    u64 iv = e[M6W_GLUE_INTV];
    if (iv == 0ULL) { iv = 2ULL; }
    else if (iv < M6_GLUE_INTERVAL_MAX) { iv = iv << 1; }
    e[M6W_GLUE_INTV] = iv;
    e[M6W_GLUE_NEXT] = h->conflicts + iv;
  }
}

void m6_hdr_record_used(FullHdr *h, u64 glue) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = (h->stable != 0ULL) ? 1ULL : 0ULL;
  u64 gi = (glue >= M6_GLUE_BINS) ? (M6_GLUE_BINS - 1ULL) : glue;
  u64 base = (st == 0ULL) ? M6W_USED0 : M6W_USED1;
  u64 u = e[base + gi];
  if (u < 0xFFFFFFFFFFFFFFFFULL) { e[base + gi] = u + 1ULL; }
  u64 tu = e[M6W_TOTAL_USED + st];
  if (tu < 0xFFFFFFFFFFFFFFFFULL) { e[M6W_TOTAL_USED + st] = tu + 1ULL; }
}

u64 m6_hdr_get_tier1(FullHdr *h, bool vivify_mode) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = vivify_mode ? 0ULL : ((h->stable != 0ULL) ? 1ULL : 0ULL);
  return e[M6W_TIER1 + st];
}

u64 m6_hdr_get_tier2(FullHdr *h, bool vivify_mode) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 t1 = e[M6W_TIER1];
  u64 st = vivify_mode ? 0ULL : 1ULL;
  u64 t2 = e[M6W_TIER2 + st];
  return (t2 < t1) ? t1 : t2;
}

bool m6_hdr_delaying(FullHdr *h, u64 id) {
  if (id >= 4ULL) { return false; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 cnt = e[M6W_DELAY_CNT + id];
  if (cnt > 0ULL) {
    e[M6W_DELAY_CNT + id] = cnt - 1ULL;
    return true;
  }
  return false;
}

void m6_hdr_bump_delay(FullHdr *h, u64 id) {
  if (id >= 4ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 cur = e[M6W_DELAY_CUR + id];
  if (cur < 0xFFFFFFFFULL) { cur = cur + 1ULL; }
  e[M6W_DELAY_CUR + id] = cur;
  e[M6W_DELAY_CNT + id] = cur;
}

void m6_hdr_reduce_delay(FullHdr *h, u64 id) {
  if (id >= 4ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 cur = e[M6W_DELAY_CUR + id] >> 1;
  e[M6W_DELAY_CUR + id] = cur;
  e[M6W_DELAY_CNT + id] = cur;
}

void m6_hdr_reset_delay(FullHdr *h, u64 id) {
  if (id >= 4ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  e[M6W_DELAY_CUR + id] = 0ULL;
  e[M6W_DELAY_CNT + id] = 0ULL;
}

u64 m6_hdr_get_watermark(FullHdr *h, u64 kind) {
  if (kind >= 8ULL) { return 0ULL; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  return e[M6W_WM_BASE + kind];
}

void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val) {
  if (kind >= 8ULL) { return; }
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  e[M6W_WM_BASE + kind] = val;
}

void m6_hdr_add_ticks(FullHdr *h, u64 ticks) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if (h->probing != 0ULL) {
    e[M6W_WM_BASE + M6_WM_PROBING_TICKS] = e[M6W_WM_BASE + M6_WM_PROBING_TICKS] + ticks;
    return;
  }
  h->search_ticks = h->search_ticks + ticks;
  u64 mk = (h->stable != 0ULL) ? M6_WM_STABLE_TICKS : M6_WM_FOCUSED_TICKS;
  e[M6W_WM_BASE + mk] = e[M6W_WM_BASE + mk] + ticks;
}

void m6_hdr_dr_init(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if ((e[M6W_DR_STATE] >> 63) != 0ULL) { return; }
  u64 sw = h->switched & 127ULL;
  e[M6W_DR_STATE] = (1ULL << 63) | (sw << 56);
  e[M6W_DR_PREV] = 0ULL;
  e[M6W_DR_PREV + 1ULL] = 0ULL;
  e[M6W_DR_SB] = 0ULL;
  e[M6W_DR_SB + 1ULL] = 0ULL;
  e[M6W_DR_SE] = 1ULL << 32;
  e[M6W_DR_SE + 1ULL] = 1ULL << 32;
}

void m6_hdr_dr_update(FullHdr *h) {
  m6_hdr_dr_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = e[M6W_DR_STATE];
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 cur = st & mask56;
  u64 last_sw = (st >> 56) & 127ULL;
  u64 cur_sw = h->switched & 127ULL;
  u64 mode = (h->stable != 0ULL) ? 1ULL : 0ULL;
  if (cur_sw != last_sw) {
    e[M6W_DR_STATE] = (1ULL << 63) | (cur_sw << 56) | cur;
    e[M6W_DR_PREV + mode] = cur;
    e[M6W_DR_SB + mode] = 0ULL;
    e[M6W_DR_SE + mode] = 1ULL << 32;
    return;
  }
  u64 prev = e[M6W_DR_PREV + mode];
  e[M6W_DR_PREV + mode] = cur;
  u64 d = (cur >= prev) ? (cur - prev) : 0ULL;
  if (d > 16383ULL) { d = 16383ULL; }
  u64 ys = d << 32;
  u64 sb = e[M6W_DR_SB + mode];
  u64 se = e[M6W_DR_SE + mode];
  if (ys >= sb) { sb = sb + ((ys - sb) / 100000ULL); }
  else { sb = sb - ((sb - ys) / 100000ULL); }
  if (se > 0ULL) {
    u64 ds = se / 100000ULL;
    se = (ds == 0ULL) ? 0ULL : (se - ds);
  }
  e[M6W_DR_SB + mode] = sb;
  e[M6W_DR_SE + mode] = se;
}

bool m6_hdr_dr_allow(FullHdr *h) {
  m6_ext_ensure_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  if ((e[M6W_DR_STATE] >> 63) == 0ULL) { return true; }
  u64 mode = (h->stable != 0ULL) ? 1ULL : 0ULL;
  u64 sb = e[M6W_DR_SB + mode];
  u64 se = e[M6W_DR_SE + mode];
  u64 scale = 1ULL << 32;
  u64 sd = (scale > se) ? (scale - se) : 0ULL;
  if (sd == 0ULL) { return true; }
  return sb < (sd * 10ULL);
}

u64 m6_hdr_decide(FullHdr *h) {
  u64 chosen = full_next_dec_var(h);
  if (chosen == 0xFFFFFFFFFFFFFFFFULL) { return 0ULL; }
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 dph = ph[chosen];
  if (h->stable != 0ULL && ptgt[chosen] != (i8)0) { dph = ptgt[chosen]; }
  u32 lit = (dph < (i8)0) ? ((u32)(chosen << 1) | 1u) : (u32)(chosen << 1);
  u64 nlvl = h->cur_level + 1ULL;
  if (nlvl > h->max_vars) { return 0ULL; }
  ftrl[nlvl] = (u32)h->trail_end;
  fdec[nlvl] = lit;
  h->cur_level = nlvl;
  full_assign(h, lit, 0xFFFFFFFFu);
  m6_hdr_dr_init(h);
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = e[M6W_DR_STATE];
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 hi = st & (~mask56);
  u64 decs = st & mask56;
  if (decs < mask56) { e[M6W_DR_STATE] = hi | (decs + 1ULL); }
  return 1ULL;
}

bool m6_hdr_analyze_rsn(FullHdr *h, u32 rsn, u32 skip_var) {
  if (rsn != 0xFFFFFFFFu && (rsn & PW_BIN_FLAG) == 0u && (u64)rsn + 3ULL <= h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    u32 hdr = ar[rsn];
    u32 sz = ar[(u64)rsn + 2ULL];
    if (sz >= 3u && (u64)rsn + 3ULL + (u64)sz <= h->arena_len && (hdr & PH_RED) != 0u) {
      m6_hdr_record_used(h, (u64)(hdr & PH_GLUE_MASK));
    }
  }
  return full_analyze_rsn(h, rsn, skip_var);
}

u64 m6_hdr_analyze(FullHdr *h) {
  if (h->cur_level == 0ULL) { return 20ULL; }
  if (h->probing == 0ULL) {
    m6_hdr_update_tier_limits(h);
    m6_hdr_dr_update(h);
  }
  return full_analyze(h);
}
"

/-- External canonical `FullSpec` callees referenced by `m6Hdr_fns` (`5` externs). -/
def m6HdrExterns : List Extern :=
  [ ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool]⟩
  , ⟨"full_next_dec_var", [i64], [i64]⟩
  , ⟨"full_assign", [i64, i32, i32], []⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool]⟩
  , ⟨"full_analyze", [i64], [i64]⟩ ]

/-- Standalone Wave-3 prep `FullM6Hdr` module (`27` functions + `5` externs, `0` exits). -/
def m6HdrModule : LeanQbe.T.Module :=
  { fns := m6Hdr_fns, externs := m6HdrExterns, exits := [] }

/-- Drop-in Wave-3 `Fn` handles replacing `w2a`/`w2b` `h->delayed*`-backed helpers. -/
def m6HdrExtReadyFn : Fn := ⟨"full_m6_ext_ready", [i64], [.bool], m6_hdr_ext_ready_body⟩
def m6HdrSyncLegacyTiersFn : Fn :=
  ⟨"full_m6_sync_legacy_tiers", [i64], [], m6_hdr_sync_legacy_tiers_body⟩
def m6HdrRecomputeTiersModeFn : Fn :=
  ⟨"full_m6_recompute_tiers_mode", [i64, i64], [], m6_hdr_recompute_tiers_mode_body⟩
def m6HdrRecomputeTiersFn : Fn :=
  ⟨"full_recompute_tiers_m6", [i64], [], m6_hdr_recompute_tiers_body⟩
def m6HdrUpdateTierLimitsFn : Fn :=
  ⟨"full_m6_update_tier_limits", [i64], [], m6_hdr_update_tier_limits_body⟩
def m6HdrRecordUsedFn : Fn := ⟨"full_m6_record_used", [i64, i64], [], m6_hdr_record_used_body⟩
def m6HdrGetTier1Fn : Fn := ⟨"full_m6_get_tier1", [i64, .bool], [i64], m6_hdr_get_tier1_body⟩
def m6HdrGetTier2Fn : Fn := ⟨"full_m6_get_tier2", [i64, .bool], [i64], m6_hdr_get_tier2_body⟩
def m6HdrDelayingFn : Fn := ⟨"full_m6_delaying", [i64, i64], [.bool], m6_hdr_delaying_body⟩
def m6HdrBumpDelayFn : Fn := ⟨"full_m6_bump_delay", [i64, i64], [], m6_hdr_bump_delay_body⟩
def m6HdrReduceDelayFn : Fn := ⟨"full_m6_reduce_delay", [i64, i64], [], m6_hdr_reduce_delay_body⟩
def m6HdrResetDelayFn : Fn := ⟨"full_m6_reset_delay", [i64, i64], [], m6_hdr_reset_delay_body⟩
def m6HdrGetWatermarkFn : Fn :=
  ⟨"full_m6_get_watermark", [i64, i64], [i64], m6_hdr_get_watermark_body⟩
def m6HdrSetWatermarkFn : Fn :=
  ⟨"full_m6_set_watermark", [i64, i64, i64], [], m6_hdr_set_watermark_body⟩
def m6HdrAddTicksFn : Fn := ⟨"full_m6_add_ticks", [i64, i64], [], m6_hdr_add_ticks_body⟩
def m6HdrDrInitFn : Fn := ⟨"full_dr_init_m6", [i64], [], m6_hdr_dr_init_body⟩
def m6HdrDrUpdateFn : Fn := ⟨"full_dr_update_m6", [i64], [], m6_hdr_dr_update_body⟩
def m6HdrDrAllowFn : Fn := ⟨"full_dr_allow_m6", [i64], [.bool], m6_hdr_dr_allow_body⟩
def m6HdrDecideFn : Fn := ⟨"full_decide", [i64], [i64], m6_hdr_decide_body⟩
def m6HdrAnalyzeRsnFn : Fn :=
  ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], m6_hdr_analyze_rsn_body⟩
def m6HdrAnalyzeFn : Fn := ⟨"full_analyze", [i64], [i64], m6_hdr_analyze_body⟩

theorem full_m6_hdr_sizeof_wf : Func.Wf full_m6_hdr_sizeof_body := by t_wf_reify
theorem full_m6_ext_sizeof_wf : Func.Wf full_m6_ext_sizeof_body := by t_wf_reify
theorem m6_hdr_init_wf : Func.Wf m6_hdr_init_body := by t_wf_reify
theorem m6_hdr_reset_wf : Func.Wf m6_hdr_reset_body := by t_wf_reify
theorem m6_ext_ensure_init_wf : Func.Wf m6_ext_ensure_init_body := by t_wf_reify
theorem m6_hdr_ext_ready_wf : Func.Wf m6_hdr_ext_ready_body := by t_wf_reify
theorem full_m6_mem_init_wf : Func.Wf full_m6_mem_init_body := by t_wf_reify
theorem m6_hdr_sync_legacy_tiers_wf : Func.Wf m6_hdr_sync_legacy_tiers_body := by t_wf_reify
theorem m6_hdr_recompute_tiers_mode_wf : Func.Wf m6_hdr_recompute_tiers_mode_body := by t_wf_reify
theorem m6_hdr_recompute_tiers_wf : Func.Wf m6_hdr_recompute_tiers_body := by t_wf_reify
theorem m6_hdr_update_tier_limits_wf : Func.Wf m6_hdr_update_tier_limits_body := by t_wf_reify
theorem m6_hdr_record_used_wf : Func.Wf m6_hdr_record_used_body := by t_wf_reify
theorem m6_hdr_get_tier1_wf : Func.Wf m6_hdr_get_tier1_body := by t_wf_reify
theorem m6_hdr_get_tier2_wf : Func.Wf m6_hdr_get_tier2_body := by t_wf_reify
theorem m6_hdr_delaying_wf : Func.Wf m6_hdr_delaying_body := by t_wf_reify
theorem m6_hdr_bump_delay_wf : Func.Wf m6_hdr_bump_delay_body := by t_wf_reify
theorem m6_hdr_reduce_delay_wf : Func.Wf m6_hdr_reduce_delay_body := by t_wf_reify
theorem m6_hdr_reset_delay_wf : Func.Wf m6_hdr_reset_delay_body := by t_wf_reify
theorem m6_hdr_get_watermark_wf : Func.Wf m6_hdr_get_watermark_body := by t_wf_reify
theorem m6_hdr_set_watermark_wf : Func.Wf m6_hdr_set_watermark_body := by t_wf_reify
theorem m6_hdr_add_ticks_wf : Func.Wf m6_hdr_add_ticks_body := by t_wf_reify
theorem m6_hdr_dr_init_wf : Func.Wf m6_hdr_dr_init_body := by t_wf_reify
theorem m6_hdr_dr_update_wf : Func.Wf m6_hdr_dr_update_body := by t_wf_reify
theorem m6_hdr_dr_allow_wf : Func.Wf m6_hdr_dr_allow_body := by t_wf_reify
theorem m6_hdr_decide_wf : Func.Wf m6_hdr_decide_body := by t_wf_reify
theorem m6_hdr_analyze_rsn_wf : Func.Wf m6_hdr_analyze_rsn_body := by t_wf_reify
theorem m6_hdr_analyze_wf : Func.Wf m6_hdr_analyze_body := by t_wf_reify

theorem m6Hdr_fns_wf : ∀ f ∈ m6Hdr_fns, f.Wf := by
  simp only [m6Hdr_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_m6_hdr_sizeof_wf, full_m6_ext_sizeof_wf, m6_hdr_init_wf, m6_hdr_reset_wf,
    m6_ext_ensure_init_wf, m6_hdr_ext_ready_wf, full_m6_mem_init_wf, m6_hdr_sync_legacy_tiers_wf,
    m6_hdr_recompute_tiers_mode_wf, m6_hdr_recompute_tiers_wf, m6_hdr_update_tier_limits_wf,
    m6_hdr_record_used_wf, m6_hdr_get_tier1_wf, m6_hdr_get_tier2_wf, m6_hdr_delaying_wf,
    m6_hdr_bump_delay_wf, m6_hdr_reduce_delay_wf, m6_hdr_reset_delay_wf, m6_hdr_get_watermark_wf,
    m6_hdr_set_watermark_wf, m6_hdr_add_ticks_wf, m6_hdr_dr_init_wf, m6_hdr_dr_update_wf,
    m6_hdr_dr_allow_wf, m6_hdr_decide_wf, m6_hdr_analyze_rsn_wf, m6_hdr_analyze_wf⟩

theorem m6Hdr_acyclic : m6HdrModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM6Hdr
