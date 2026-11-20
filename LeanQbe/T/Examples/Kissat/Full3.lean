module

public import LeanQbe.T.Examples.Kissat.Full2

set_option autoImplicit false

@[expose] public section

/-!
# Kissat `D-Full` C0 Solver — Part 3 (`Lucky`, `Probe/HBR`, `Transitive`, `Vivify`, `Substitute`)

Implements:
1. Binary/unit helpers (`full_has_bin`, `full_add_bin`, `full_delete_binary`, `full_add_unit`)
   and `full_lucky` (`full_lucky_scan`, `full_lucky_polar`, `full_lucky`).
2. Level-1 Probing + Hyper-Binary Resolution (`HBR` via 1UIP dominator) + cross-branch
   backbone unit discovery (`full_probe_run`).
3. Binary Implication Graph (BIG) transitive reduction (`full_trans_lit`, `full_transitive`).
4. Tiered clause vivification (`tier1`/`tier2`/`tier3`/`irred`, `PH_VIV`/`PH_SHRK`).
5. BIG Tarjan SCC equivalence substitution (`full_tarjan_scc`, `full_subst_*`, `full_substitute`)
   with `x ≡ ¬x -> 20` clash detection and `extend_stk` witness pushing.
6. Dense occurrence enter & sparse 2WL watch rebuild (`full_enter_dense`, `full_rebuild_watches`).
-/

namespace LeanQbe.T.Examples.Kissat.Full

open LeanQbe.T
open LeanQbe.T.Examples.Kissat

kissat_c0! full3 "
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

#define PH_GLUE_MASK 0x7FFFFu
#define PH_GARB 0x00080000u
#define PH_VIV  0x00100000u
#define PH_RSN  0x00200000u
#define PH_RED  0x00400000u
#define PH_SHRK 0x00800000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define FL_ACTIVE  1u
#define FL_ELIM    2u
#define FL_SUBST   4u
#define FL_SUBSUME 8u
#define FL_ELIM_C  16u
#define FL_BONE0   128u
#define FL_BONE1   256u
#define FL_TRANS   512u

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void full_backtrack(FullHdr *h, u64 target_lvl);
extern u64 full_find_repl(FullHdr *h, u64 cref);
extern u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref);
extern u64 full_propagate(FullHdr *h);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_sweep_bins(FullHdr *h);
extern u64 full_arena_sweep(FullHdr *h);
extern u64 full_analyze(FullHdr *h);
extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);

bool full_has_bin(FullHdr *h, u32 a, u32 b) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)a >= nlits || (u64)b >= nlits || a == b || a == (b ^ 1u)) { return false; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 sa = (u64)wvec[((u64)a << 1) + 1ULL];
  u64 sb = (u64)wvec[((u64)b << 1) + 1ULL];
  u32 src = (sa <= sb) ? a : b;
  u32 tgt = (sa <= sb) ? b : a;
  u64 off = (u64)wvec[(u64)src << 1];
  u64 end = off + (u64)wvec[((u64)src << 1) + 1ULL];
  u64 p = off;
  while (p < end) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if ((w0 & PW_LIT_MASK) == tgt) { return true; }
      p = p + 1ULL;
    } else { p = p + 2ULL; }
  }
  return false;
}

u64 full_add_bin(FullHdr *h, u32 a, u32 b) {
  u64 nlits = h->cur_vars << 1;
  if ((u64)a >= nlits || (u64)b >= nlits || a == (b ^ 1u)) { return 0ULL; }
  i8 *vals = (i8 *)h->values;
  if (vals[a] > (i8)0 || vals[b] > (i8)0) { return 0ULL; }
  if (vals[a] < (i8)0 && vals[b] < (i8)0) { h->inconsistent = 1ULL; return 20ULL; }
  if (vals[a] < (i8)0 || a == b) { full_assign_lvl(h, b, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (vals[b] < (i8)0) { full_assign_lvl(h, a, 0xFFFFFFFFu, 0u); return 1ULL; }
  if (full_has_bin(h, a, b)) { return 0ULL; }
  u32 b0 = (b & PW_LIT_MASK) | PW_BIN_FLAG;
  u32 b1 = (a & PW_LIT_MASK) | PW_BIN_FLAG;
  if (!full_watch_push(h, a, b0, 0u, 1u) || !full_watch_push(h, b, b1, 0u, 1u)) {
    h->oom = 1ULL; return 2ULL;
  }
  h->num_binary = h->num_binary + 1ULL;
  return 1ULL;
}

void full_delete_bin_side(FullHdr *h, u32 lit, u32 other) {
  if ((u64)lit >= (h->cur_vars << 1)) { return; }
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 sz = (u64)wvec[((u64)lit << 1) + 1ULL];
  if (sz == 0ULL) { return; }
  u64 p = off; u64 q = off; u64 end = off + sz;
  bool removed = false;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      if (!removed && (w0 & PW_LIT_MASK) == other) { removed = true; }
      else { wstk[q] = w0; q = q + 1ULL; }
    } else if (p < end) {
      u32 cr = wstk[p]; p = p + 1ULL;
      wstk[q] = w0; wstk[q + 1ULL] = cr; q = q + 2ULL;
    }
  }
  u64 k = q;
  while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)lit << 1) + 1ULL] = (u32)(q - off);
  h->wusable = h->wusable + (end - q);
}

void full_delete_binary(FullHdr *h, u32 a, u32 b) {
  full_delete_bin_side(h, a, b);
  full_delete_bin_side(h, b, a);
  if (h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
}

void full_set_inactive(FullHdr *h, u32 v, u32 flag) {
  if ((u64)v >= h->cur_vars) { return; }
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  if ((fl[v] & FL_ACTIVE) != 0u && vals[(u64)v << 1] == (i8)0 && h->unassigned > 0ULL) {
    h->unassigned = h->unassigned - 1ULL;
  }
  fl[v] = (fl[v] & (~FL_ACTIVE)) | flag;
}

bool full_add_unit(FullHdr *h, u32 lit) {
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  if ((u64)(lit >> 1) >= h->cur_vars) { return false; }
  i8 *vals = (i8 *)h->values;
  if (vals[lit] > (i8)0) { return true; }
  if (vals[lit] < (i8)0) { h->inconsistent = 1ULL; return false; }
  full_assign_lvl(h, lit, 0xFFFFFFFFu, 0u);
  return true;
}

u64 full_lucky_scan(FullHdr *h, bool pos_mode, bool fwd) {
  u64 cv = h->cur_vars;
  i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  u64 i = 0ULL;
  while (i < cv) {
    u64 v = fwd ? i : (cv - 1ULL - i);
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      h->fuel = h->fuel - 1ULL;
      u32 lit = pos_mode ? (u32)(v << 1) : ((u32)(v << 1) | 1u);
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); return 0ULL; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit; h->cur_level = nlvl;
      full_assign(h, lit, 0xFFFFFFFFu);
      u64 pr = full_propagate(h);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) {
        if (h->cur_level > 1ULL) {
          full_backtrack(h, h->cur_level - 1ULL);
          if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          h->fuel = h->fuel - 1ULL;
          nlvl = h->cur_level + 1ULL;
          if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); return 0ULL; }
          ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
          full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
          u64 pr2 = full_propagate(h);
          if (pr2 == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          if (pr2 == 1ULL) { full_backtrack(h, 0ULL); return 0ULL; }
        } else {
          u64 ast = full_analyze(h);
          if (ast == 20ULL) { return 20ULL; }
          if (ast != 1ULL) { full_backtrack(h, 0ULL); return 2ULL; }
          u64 pr3 = full_propagate(h);
          if (pr3 == 1ULL) { return 20ULL; }
          if (pr3 == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
        }
      }
    }
    i = i + 1ULL;
  }
  return 10ULL;
}

u64 full_lucky_polar(FullHdr *h) {
  u64 cv = h->cur_vars; i8 *vals = (i8 *)h->values;
  u32 *ar = (u32 *)h->arena; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  bool has_neg = false; bool has_pos = false;
  u64 p = 0ULL;
  while (p < h->arena_len && (!has_neg || !has_pos)) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) == 0u && sz >= 3u) {
      bool ap = false; bool an = false; u32 k = 0u;
      while (k < sz) {
        u32 l = ar[p + 3ULL + (u64)k];
        if (vals[l] >= (i8)0) { if ((l & 1u) == 0u) { ap = true; } else { an = true; } }
        k = k + 1u;
      }
      if (!ap) { has_neg = true; }
      if (!an) { has_pos = true; }
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  u64 v = 0ULL;
  while (v < cv && (!has_neg || !has_pos)) {
    if (vals[v << 1] == (i8)0) {
      u32 nl = (u32)((v << 1) | 1ULL);
      u64 off = (u64)wvec[(u64)nl << 1]; u64 end = off + (u64)wvec[((u64)nl << 1) + 1ULL];
      while (off < end && !has_neg) {
        u32 w0 = wstk[off];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((ot & 1u) != 0u && vals[ot] >= (i8)0) { has_neg = true; }
          off = off + 1ULL;
        } else { off = off + 2ULL; }
      }
      u32 pl = (u32)(v << 1);
      off = (u64)wvec[(u64)pl << 1]; end = off + (u64)wvec[((u64)pl << 1) + 1ULL];
      while (off < end && !has_pos) {
        u32 w0 = wstk[off];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 ot = w0 & PW_LIT_MASK;
          if ((ot & 1u) == 0u && vals[ot] >= (i8)0) { has_pos = true; }
          off = off + 1ULL;
        } else { off = off + 2ULL; }
      }
    }
    v = v + 1ULL;
  }
  if (has_neg && has_pos) { return 0ULL; }
  return has_neg ? 2ULL : 1ULL;
}

u64 full_lucky(FullHdr *h) {
  h->probing = 1ULL;
  u64 pol = full_lucky_polar(h);
  if (pol != 0ULL) {
    bool set_pos = (pol == 1ULL);
    i8 *vals = (i8 *)h->values; u32 *fl = (u32 *)h->flags;
    u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
    u64 v = 0ULL;
    while (v < h->cur_vars) {
      if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
        if (h->fuel == 0ULL) { full_backtrack(h, 0ULL); h->probing = 0ULL; return 2ULL; }
        h->fuel = h->fuel - 1ULL;
        u32 lit = set_pos ? (u32)(v << 1) : ((u32)(v << 1) | 1u);
        u64 nlvl = h->cur_level + 1ULL;
        if (nlvl > h->max_vars) { full_backtrack(h, 0ULL); h->probing = 0ULL; return 0ULL; }
        ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit; h->cur_level = nlvl;
        full_assign(h, lit, 0xFFFFFFFFu);
        if (full_propagate(h) != 0ULL) { full_backtrack(h, 0ULL); h->probing = 0ULL; return 0ULL; }
      }
      v = v + 1ULL;
    }
    h->probing = 0ULL; return 10ULL;
  }
  u64 r = full_lucky_scan(h, false, true);
  if (r == 0ULL) { r = full_lucky_scan(h, true, true); }
  if (r == 0ULL) { r = full_lucky_scan(h, false, false); }
  if (r == 0ULL) { r = full_lucky_scan(h, true, false); }
  h->probing = 0ULL;
  return r;
}

u32 full_hbr_dom(FullHdr *h, u32 cref, u32 implied) {
  u32 *ar = (u32 *)h->arena; u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail; u32 *clr = (u32 *)h->min_clr;
  u64 cv = h->cur_vars; u32 sz = ar[(u64)cref + 2ULL];
  u64 clen = 0ULL; u64 open = 0ULL; u32 i = 0u;
  while (i < sz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i]; u32 v = l >> 1;
    if (l != implied && (u64)v < cv && lvl[v] == 1u && mrk[v] == (u8)0) {
      mrk[v] = (u8)1; clr[clen] = v; clen = clen + 1ULL; open = open + 1ULL;
    }
    i = i + 1u;
  }
  u32 dom = 0xFFFFFFFFu;
  if (open >= 2ULL) {
    u64 idx = h->trail_end;
    while (open > 0ULL && idx > 0ULL) {
      idx = idx - 1ULL;
      u32 p = trl[idx]; u32 pv = p >> 1;
      if ((u64)pv >= cv || lvl[pv] != 1u || mrk[pv] == (u8)0) { continue; }
      open = open - 1ULL;
      if (open == 0ULL) { dom = p; break; }
      u32 rsn = rsns[pv];
      if (rsn == 0xFFFFFFFFu) { break; }
      if ((rsn & PW_BIN_FLAG) != 0u) {
        u32 ov = (rsn & PW_LIT_MASK) >> 1;
        if ((u64)ov < cv && lvl[ov] == 1u && mrk[ov] == (u8)0 && clen < cv) {
          mrk[ov] = (u8)1; clr[clen] = ov; clen = clen + 1ULL; open = open + 1ULL;
        }
      } else if ((u64)rsn + 3ULL <= h->arena_len) {
        u32 rsz = ar[(u64)rsn + 2ULL]; u32 j = 0u;
        while (j < rsz && (u64)rsn + 3ULL + (u64)rsz <= h->arena_len) {
          u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
          if (ov != pv && (u64)ov < cv && lvl[ov] == 1u && mrk[ov] == (u8)0 && clen < cv) {
            mrk[ov] = (u8)1; clr[clen] = ov; clen = clen + 1ULL; open = open + 1ULL;
          }
          j = j + 1u;
        }
      }
    }
  }
  u64 k = 0ULL;
  while (k < clen) { mrk[clr[k]] = (u8)0; k = k + 1ULL; }
  return dom;
}

bool full_probe_prop_lit(FullHdr *h, u32 lit) {
  u32 not_lit = lit ^ 1u; u64 nlits = h->cur_vars << 1;
  if ((u64)not_lit >= nlits) { return true; }
  i8 *vals = (i8 *)h->values;
  if (vals[not_lit] >= (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena; u32 *hstk = (u32 *)h->work_stk2;
  u64 off = (u64)wvec[(u64)not_lit << 1]; u64 sz = (u64)wvec[((u64)not_lit << 1) + 1ULL];
  if (sz == 0ULL) { return true; }
  u64 p = off; u64 q = off; u64 end = off + sz; bool confl = false;
  u32 bin_rsn = (not_lit & PW_LIT_MASK) | PW_BIN_FLAG;
  while (p < end) {
    u32 w0 = wstk[p]; p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      wstk[q] = w0; q = q + 1ULL;
      u32 ot = w0 & PW_LIT_MASK;
      if ((u64)ot >= nlits || vals[ot] > (i8)0) { continue; }
      if (vals[ot] < (i8)0) {
        h->confl_type = 1ULL; h->confl_lit0 = (u64)not_lit;
        h->confl_lit1 = (u64)ot; confl = true; break;
      }
      full_assign_lvl(h, ot, bin_rsn, 1u);
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p]; p = p + 1ULL; u32 blk = w0 & PW_LIT_MASK;
    if ((u64)blk < nlits && vals[blk] > (i8)0) {
      wstk[q] = w0; wstk[q + 1ULL] = cr; q = q + 2ULL; continue;
    }
    if ((u64)cr + 3ULL > h->arena_len) { continue; }
    u32 hdr = ar[cr]; u32 csz = ar[(u64)cr + 2ULL];
    if ((hdr & PH_GARB) != 0u || csz < 3u || (u64)cr + 3ULL + (u64)csz > h->arena_len) {
      continue;
    }
    u32 l0 = ar[(u64)cr + 3ULL]; u32 l1 = ar[(u64)cr + 4ULL];
    if (l0 == not_lit) { ar[(u64)cr + 3ULL] = l1; ar[(u64)cr + 4ULL] = not_lit; l0 = l1; }
    else if (l1 != not_lit) { continue; }
    if ((u64)l0 >= nlits) { continue; }
    i8 ov = vals[l0];
    if (ov > (i8)0) { wstk[q] = l0 & PW_LIT_MASK; wstk[q + 1ULL] = cr; q = q + 2ULL; continue; }
    u64 ri = full_find_repl(h, (u64)cr);
    if (ri != 0xFFFFFFFFULL) {
      u32 repl = ar[(u64)cr + 3ULL + ri];
      ar[(u64)cr + 4ULL] = repl; ar[(u64)cr + 3ULL + ri] = not_lit;
      u64 pr = p - off; u64 qr = q - off; u64 er = end - off;
      bool pok = full_watch_push(h, repl, l0 & PW_LIT_MASK, cr, 2u);
      off = (u64)wvec[(u64)not_lit << 1]; p = off + pr; q = off + qr; end = off + er;
      if (!pok) {
        ar[(u64)cr + 4ULL] = not_lit; ar[(u64)cr + 3ULL + ri] = repl;
        wstk[q] = w0; wstk[q + 1ULL] = cr; q = q + 2ULL; h->oom = 1ULL; confl = true; break;
      }
      continue;
    }
    wstk[q] = l0 & PW_LIT_MASK; wstk[q + 1ULL] = cr; q = q + 2ULL;
    if (ov < (i8)0) { h->confl_type = 2ULL; h->confl_ref = (u64)cr; confl = true; break; }
    u32 dom = full_hbr_dom(h, cr, l0);
    if (dom != 0xFFFFFFFFu && h->tmp_cnt < h->cur_vars) {
      u64 hn = h->tmp_cnt; hstk[hn << 1] = dom ^ 1u; hstk[(hn << 1) + 1ULL] = l0;
      h->tmp_cnt = hn + 1ULL;
    }
    full_assign_lvl(h, l0, cr, 1u);
  }
  while (p < end) { wstk[q] = wstk[p]; q = q + 1ULL; p = p + 1ULL; }
  u64 k = q;
  while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
  wvec[((u64)not_lit << 1) + 1ULL] = (u32)(q - off);
  h->wusable = h->wusable + (end - q);
  return !confl;
}

u64 full_probe_prop(FullHdr *h) {
  u32 *trl = (u32 *)h->trail;
  while (h->propagated < h->trail_end) {
    if (h->oom != 0ULL || h->fuel == 0ULL) { return 2ULL; }
    h->fuel = h->fuel - 1ULL;
    u32 lit = trl[h->propagated];
    h->propagated = h->propagated + 1ULL;
    if (!full_probe_prop_lit(h, lit)) {
      return (h->oom != 0ULL) ? 2ULL : 1ULL;
    }
  }
  return 0ULL;
}

u64 full_probe_flush_hbr(FullHdr *h, u64 hbr_n) {
  u32 *hstk = (u32 *)h->work_stk2;
  u64 i = 0ULL;
  while (i < hbr_n) {
    u32 a = hstk[i << 1]; u32 b = hstk[(i << 1) + 1ULL];
    u64 ar = full_add_bin(h, a, b);
    if (ar == 20ULL) { return 20ULL; }
    if (ar == 1ULL) { h->hbr_cnt = h->hbr_cnt + 1ULL; }
    if (h->oom != 0ULL) { return 2ULL; }
    i = i + 1ULL;
  }
  if (full_propagate(h) == 1ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_probe_assume_pair(FullHdr *h, u32 lit) {
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  u32 *trl = (u32 *)h->trail; u8 *lm = (u8 *)h->lit_mark;
  u32 *sav = (u32 *)h->work_stk1; u64 cv = h->cur_vars;
  h->tmp_cnt = 0ULL; u64 t0 = h->trail_end;
  ftrl[1] = (u32)t0; fdec[1] = lit; h->cur_level = 1ULL;
  full_assign(h, lit, 0xFFFFFFFFu);
  u64 pr = full_probe_prop(h);
  u64 hbr0 = h->tmp_cnt;
  if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
  if (pr == 1ULL) {
    u64 ast = full_analyze(h);
    if (ast == 20ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    return full_probe_flush_hbr(h, hbr0);
  }
  u64 sn = 0ULL; u64 k = t0;
  while (k < h->trail_end && sn < cv) {
    u32 tl = trl[k]; lm[tl] = (u8)1; sav[sn] = tl; sn = sn + 1ULL; k = k + 1ULL;
  }
  full_backtrack(h, 0ULL);
  u64 fh = full_probe_flush_hbr(h, hbr0);
  if (fh != 1ULL) {
    k = 0ULL; while (k < sn) { lm[sav[k]] = (u8)0; k = k + 1ULL; }
    return fh;
  }
  i8 *vals = (i8 *)h->values; u32 *bones = (u32 *)h->tmp_lits; u64 bn = 0ULL;
  h->tmp_cnt = 0ULL;
  if (vals[lit ^ 1u] == (i8)0) {
    u64 t1 = h->trail_end;
    ftrl[1] = (u32)t1; fdec[1] = lit ^ 1u; h->cur_level = 1ULL;
    full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
    u64 pr2 = full_probe_prop(h);
    u64 hbr1 = h->tmp_cnt;
    if (pr2 == 1ULL) {
      k = 0ULL; while (k < sn) { lm[sav[k]] = (u8)0; k = k + 1ULL; }
      u64 ast = full_analyze(h);
      if (ast == 20ULL) { return 20ULL; }
      if (full_propagate(h) == 1ULL) { return 20ULL; }
      return full_probe_flush_hbr(h, hbr1);
    }
    if (pr2 == 0ULL) {
      k = t1;
      while (k < h->trail_end && bn < cv) {
        u32 tl = trl[k];
        if (lm[tl] != (u8)0) { bones[bn] = tl; bn = bn + 1ULL; }
        k = k + 1ULL;
      }
    }
    full_backtrack(h, 0ULL);
    h->tmp_cnt = hbr1;
  }
  u64 hbr1 = h->tmp_cnt;
  k = 0ULL; while (k < sn) { lm[sav[k]] = (u8)0; k = k + 1ULL; }
  k = 0ULL;
  while (k < bn) {
    if (!full_add_unit(h, bones[k])) { return 20ULL; }
    k = k + 1ULL;
  }
  if (full_probe_flush_hbr(h, hbr1) == 20ULL) { return 20ULL; }
  return 1ULL;
}

u64 full_probe_run(FullHdr *h, u64 budget) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *fl = (u32 *)h->flags; i8 *vals = (i8 *)h->values;
  u64 cv = h->cur_vars; u64 done = 0ULL; u64 v = 0ULL;
  u64 res = 1ULL;
  while (v < cv && done < budget && h->fuel > 0ULL && h->oom == 0ULL) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) {
      u64 st = full_probe_assume_pair(h, (u32)(v << 1));
      done = done + 1ULL;
      if (st == 20ULL) { res = 20ULL; break; }
      if (st == 2ULL) { break; }
    }
    v = v + 1ULL;
  }
  if (h->cur_level > 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 0ULL;
  return res;
}

bool full_trans_lit(FullHdr *h, u32 src) {
  i8 *vals = (i8 *)h->values;
  if (vals[src] != (i8)0) { return true; }
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *trl = (u32 *)h->trail; u64 nlits = h->cur_vars << 1;
  u64 off = (u64)wvec[(u64)src << 1]; u64 sz = (u64)wvec[((u64)src << 1) + 1ULL];
  if (sz == 0ULL) { return true; }
  u32 not_src = src ^ 1u; bool failed = false; u64 reduced = 0ULL;
  u64 p = off; u64 end = off + sz;
  while (p < end && !failed && h->ant_sz > 0ULL) {
    u32 w0 = wstk[p];
    if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2ULL; continue; }
    u32 dst = w0 & PW_LIT_MASK;
    if ((u64)dst >= nlits || vals[dst] != (i8)0) { p = p + 1ULL; continue; }
    h->ant_sz = h->ant_sz - 1ULL;
    u64 saved = h->trail_end; u64 prop = saved; bool trans = false;
    vals[not_src] = (i8)1; vals[src] = (i8)(-1); trl[h->trail_end] = not_src;
    h->trail_end = h->trail_end + 1ULL;
    while (!trans && !failed && prop < h->trail_end) {
      u32 lit = trl[prop]; prop = prop + 1ULL; u32 nl = lit ^ 1u;
      u64 loff = (u64)wvec[(u64)nl << 1]; u64 lend = loff + (u64)wvec[((u64)nl << 1) + 1ULL];
      u64 q = loff;
      while (q < lend) {
        u32 qw = wstk[q];
        if ((qw & PW_BIN_FLAG) == 0u) { q = q + 2ULL; continue; }
        if (nl == src && q == p) { q = q + 1ULL; continue; }
        u32 ot = qw & PW_LIT_MASK;
        if (ot == dst) { trans = true; break; }
        if ((u64)ot < nlits) {
          if (vals[ot] < (i8)0) { failed = true; break; }
          if (vals[ot] == (i8)0 && h->trail_end < h->max_vars) {
            vals[ot] = (i8)1; vals[ot ^ 1u] = (i8)(-1);
            trl[h->trail_end] = ot; h->trail_end = h->trail_end + 1ULL;
          }
        }
        q = q + 1ULL;
      }
    }
    while (h->trail_end > saved) {
      h->trail_end = h->trail_end - 1ULL; u32 ul = trl[h->trail_end];
      vals[ul] = (i8)0; vals[ul ^ 1u] = (i8)0;
    }
    if (trans) {
      full_delete_bin_side(h, dst, src);
      wstk[p] = 0xFFFFFFFFu; reduced = reduced + 1ULL;
      h->trans_cnt = h->trans_cnt + 1ULL;
    }
    p = p + 1ULL;
  }
  if (reduced > 0ULL) {
    u64 q = off; p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      if (w0 == 0xFFFFFFFFu) { p = p + 1ULL; }
      else if ((w0 & PW_BIN_FLAG) != 0u) { wstk[q] = w0; q = q + 1ULL; p = p + 1ULL; }
      else if (p + 1ULL < end) {
        wstk[q] = w0; wstk[q + 1ULL] = wstk[p + 1ULL]; q = q + 2ULL; p = p + 2ULL;
      } else { p = p + 1ULL; }
    }
    while (q < end) { wstk[q] = 0xFFFFFFFFu; q = q + 1ULL; }
    wvec[((u64)src << 1) + 1ULL] = (u32)((end - off) - reduced);
    h->wusable = h->wusable + reduced;
    if (h->num_binary >= reduced) { h->num_binary = h->num_binary - reduced; }
  }
  if (failed) { h->trans_cnt = h->trans_cnt + 1ULL; return full_add_unit(h, src); }
  return true;
}

u64 full_transitive(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *fl = (u32 *)h->flags; u64 cv = h->cur_vars;
  h->ant_sz = 100000ULL; u64 v = 0ULL; u64 res = 1ULL;
  while (v < cv && h->ant_sz > 0ULL && h->oom == 0ULL) {
    if ((fl[v] & (FL_ACTIVE | FL_TRANS)) == (FL_ACTIVE | FL_TRANS)) {
      fl[v] = fl[v] & (~FL_TRANS);
      if (!full_trans_lit(h, (u32)(v << 1))) { res = 20ULL; break; }
      if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
      if (!full_trans_lit(h, (u32)((v << 1) | 1ULL))) { res = 20ULL; break; }
      if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
    }
    v = v + 1ULL;
  }
  if (h->wusable * 2ULL > h->wcap) { full_wstack_defrag(h); }
  h->probing = 0ULL;
  return res;
}

u64 full_viv_simplify(FullHdr *h, u32 cref) {
  u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u32 hdr = ar[cref]; u32 old_sz = ar[(u64)cref + 2ULL];
  u32 k = 0u; u32 i = 0u;
  while (i < old_sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[lit] > (i8)0) {
      full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
      full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
      ar[cref] = hdr | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
      return 1ULL;
    }
    if (vals[lit] == (i8)0) { k = k + 1u; }
    i = i + 1u;
  }
  if (k == old_sz) { return 0ULL; }
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  u32 nsz = 0u; i = 0u;
  while (i < old_sz) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)i];
    if (vals[lit] == (i8)0) { ar[(u64)cref + 3ULL + (u64)nsz] = lit; nsz = nsz + 1u; }
    i = i + 1u;
  }
  if (nsz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
  if (nsz == 1u) {
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    return full_add_unit(h, ar[(u64)cref + 3ULL]) ? 1ULL : 20ULL;
  }
  if (nsz == 2u) {
    u64 br = full_add_bin(h, ar[(u64)cref + 3ULL], ar[(u64)cref + 4ULL]);
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    return (br == 20ULL) ? 20ULL : 1ULL;
  }
  ar[(u64)cref + 2ULL] = nsz; ar[(u64)cref + 1ULL] = 2u;
  if ((hdr & PH_SHRK) == 0u) {
    ar[cref] = hdr | PH_SHRK; ar[(u64)cref + 3ULL + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
  }
  u32 l0 = ar[(u64)cref + 3ULL]; u32 l1 = ar[(u64)cref + 4ULL];
  if (!full_watch_push(h, l0, l1 & PW_LIT_MASK, cref, 2u) ||
      !full_watch_push(h, l1, l0 & PW_LIT_MASK, cref, 2u)) { h->oom = 1ULL; }
  return 0ULL;
}

void full_viv_sort_lits(FullHdr *h, u32 *lits, u32 sz) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 i = 1u;
  while (i < sz) {
    u32 x = lits[i]; u32 dx = wvec[((u64)x << 1) + 1ULL];
    u32 j = i;
    while (j > 0u) {
      u32 prev = lits[j - 1u]; u32 dp = wvec[((u64)prev << 1) + 1ULL];
      if (dp > dx || (dp == dx && prev < x)) { break; }
      lits[j] = prev; j = j - 1u;
    }
    lits[j] = x; i = i + 1u;
  }
}

u32 full_viv_deduce(FullHdr *h, u32 cref, u32 implied, u32 *out) {
  u32 *ar = (u32 *)h->arena; u8 *mrk = (u8 *)h->mark;
  u32 *lvl = (u32 *)h->level; u32 *rsns = (u32 *)h->reason;
  u32 *qstk = (u32 *)h->work_stk1; u64 cv = h->cur_vars;
  u64 qlen = 0ULL; u64 qi = 0ULL; u32 olen = 0u;
  h->res_sz = 0ULL;
  if (implied != 0xFFFFFFFFu) {
    u32 iv = implied >> 1;
    if ((u64)iv < cv && lvl[iv] > 0u) { mrk[iv] = (u8)1; qstk[qlen] = iv; qlen = qlen + 1ULL; }
    out[olen] = implied; olen = olen + 1u;
  } else {
    u32 src_cr = (h->confl_type == 2ULL) ? (u32)h->confl_ref : cref;
    if (h->confl_type == 1ULL) {
      u32 a = (u32)h->confl_lit0; u32 b = (u32)h->confl_lit1;
      if (lvl[a >> 1] > 0u && mrk[a >> 1] == (u8)0 && qlen < cv) {
        mrk[a >> 1] = (u8)1; qstk[qlen] = a >> 1; qlen = qlen + 1ULL;
      }
      if (lvl[b >> 1] > 0u && mrk[b >> 1] == (u8)0 && qlen < cv) {
        mrk[b >> 1] = (u8)1; qstk[qlen] = b >> 1; qlen = qlen + 1ULL;
      }
    } else if ((u64)src_cr + 3ULL <= h->arena_len) {
      if (src_cr != cref && (ar[src_cr] & PH_RED) != 0u) { h->res_sz = 1ULL; }
      u32 csz = ar[(u64)src_cr + 2ULL]; u32 i = 0u;
      while (i < csz) {
        u32 lv = ar[(u64)src_cr + 3ULL + (u64)i] >> 1;
        if ((u64)lv < cv && lvl[lv] > 0u && mrk[lv] == (u8)0 && qlen < cv) {
          mrk[lv] = (u8)1; qstk[qlen] = lv; qlen = qlen + 1ULL;
        }
        i = i + 1u;
      }
    }
  }
  u32 *trl = (u32 *)h->trail; u32 *tpos = (u32 *)h->trail_pos;
  while (qi < qlen) {
    u32 v = qstk[qi]; qi = qi + 1ULL;
    u32 rsn = rsns[v];
    if (rsn == 0xFFFFFFFFu) {
      u32 tl = trl[tpos[v]];
      if (tl != implied && (u64)olen < cv) { out[olen] = tl ^ 1u; olen = olen + 1u; }
    } else if ((rsn & PW_BIN_FLAG) != 0u) {
      u32 ov = (rsn & PW_LIT_MASK) >> 1;
      if ((u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && qlen < cv) {
        mrk[ov] = (u8)1; qstk[qlen] = ov; qlen = qlen + 1ULL;
      }
    } else if ((u64)rsn + 3ULL <= h->arena_len) {
      if ((ar[rsn] & PH_RED) != 0u) { h->res_sz = 1ULL; }
      u32 rsz = ar[(u64)rsn + 2ULL]; u32 j = 0u;
      while (j < rsz && (u64)rsn + 3ULL + (u64)rsz <= h->arena_len) {
        u32 ov = ar[(u64)rsn + 3ULL + (u64)j] >> 1;
        if (ov != v && (u64)ov < cv && lvl[ov] > 0u && mrk[ov] == (u8)0 && qlen < cv) {
          mrk[ov] = (u8)1; qstk[qlen] = ov; qlen = qlen + 1ULL;
        }
        j = j + 1u;
      }
    }
  }
  qi = 0ULL; while (qi < qlen) { mrk[qstk[qi]] = (u8)0; qi = qi + 1ULL; }
  return olen;
}

u64 full_viv_commit(FullHdr *h, u32 cref, u32 *out, u32 olen, bool used_red) {
  u32 *ar = (u32 *)h->arena; u32 hdr = ar[cref]; u32 old_sz = ar[(u64)cref + 2ULL];
  if (olen >= old_sz) { return 1ULL; }
  h->viv_cnt = h->viv_cnt + 1ULL;
  if (olen == 0u) { h->inconsistent = 1ULL; return 20ULL; }
  full_unwatch_large(h, ar[(u64)cref + 3ULL], cref);
  full_unwatch_large(h, ar[(u64)cref + 4ULL], cref);
  if (olen == 1u) {
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    return full_add_unit(h, out[0]) ? 1ULL : 20ULL;
  }
  if (olen == 2u) {
    ar[cref] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)old_sz;
    u64 br = full_add_bin(h, out[0], out[1]);
    return (br == 20ULL) ? 20ULL : 1ULL;
  }
  u32 i = 0u;
  while (i < olen) { ar[(u64)cref + 3ULL + (u64)i] = out[i]; i = i + 1u; }
  ar[(u64)cref + 2ULL] = olen; ar[(u64)cref + 1ULL] = 2u;
  u32 nhdr = hdr;
  if (!used_red && (nhdr & PH_RED) != 0u) {
    nhdr = nhdr & (~PH_RED);
    if (h->num_redundant > 0ULL) { h->num_redundant = h->num_redundant - 1ULL; }
    h->num_irred = h->num_irred + 1ULL;
  }
  if ((nhdr & PH_SHRK) == 0u) {
    ar[(u64)cref + 3ULL + (u64)old_sz - 1ULL] = 0xFFFFFFFFu;
    nhdr = nhdr | PH_SHRK;
  }
  ar[cref] = nhdr;
  u32 l0 = out[0]; u32 l1 = out[1];
  if (!full_watch_push(h, l0, l1 & PW_LIT_MASK, cref, 2u) ||
      !full_watch_push(h, l1, l0 & PW_LIT_MASK, cref, 2u)) { h->oom = 1ULL; return 2ULL; }
  return 1ULL;
}

u64 full_viv_clause(FullHdr *h, u32 cref) {
  u64 sr = full_viv_simplify(h, cref);
  if (sr != 0ULL) { return (sr == 20ULL) ? 20ULL : 1ULL; }
  u32 *ar = (u32 *)h->arena; u32 sz = ar[(u64)cref + 2ULL];
  if (sz < 3u || (u64)sz > h->cur_vars) { return 1ULL; }
  ar[cref] = ar[cref] | PH_VIV;
  u32 *tmp = (u32 *)h->tmp_lits; u32 *out = (u32 *)h->work_stk2;
  u32 *ftrl = (u32 *)h->frame_trail; u32 *fdec = (u32 *)h->frame_dec;
  i8 *vals = (i8 *)h->values;
  u32 i = 0u;
  while (i < sz) { tmp[i] = ar[(u64)cref + 3ULL + (u64)i]; i = i + 1u; }
  full_viv_sort_lits(h, tmp, sz);
  h->confl_type = 0ULL; h->confl_ref = 0xFFFFFFFFULL;
  bool confl = false; u32 implied = 0xFFFFFFFFu;
  i = 0u;
  while (i < sz) {
    u32 lit = tmp[i]; i8 lv = vals[lit];
    if (lv > (i8)0) { implied = lit; break; }
    if (lv == (i8)0) {
      u64 nlvl = h->cur_level + 1ULL;
      if (nlvl > h->max_vars) { break; }
      ftrl[nlvl] = (u32)h->trail_end; fdec[nlvl] = lit ^ 1u; h->cur_level = nlvl;
      full_assign(h, lit ^ 1u, 0xFFFFFFFFu);
      u64 pr = full_propagate_ignore(h, (u64)cref);
      if (pr == 2ULL) { full_backtrack(h, 0ULL); return 2ULL; }
      if (pr == 1ULL) { confl = true; break; }
    }
    i = i + 1u;
  }
  u32 olen = sz;
  h->res_sz = 0ULL;
  if (confl || implied != 0xFFFFFFFFu || i == sz) {
    olen = full_viv_deduce(h, cref, confl ? 0xFFFFFFFFu : implied, out);
  }
  bool used_red = (h->res_sz != 0ULL);
  full_backtrack(h, 0ULL);
  if (olen < sz) { return full_viv_commit(h, cref, out, olen, used_red); }
  return 1ULL;
}

u64 full_vivify(FullHdr *h, u64 tier_mode) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  h->probing = 1ULL;
  u32 *ar = (u32 *)h->arena; u64 budget = 1024ULL;
  u64 p = 0ULL; u64 res = 1ULL;
  while (p < h->arena_len && budget > 0ULL && h->oom == 0ULL && h->fuel > 0ULL) {
    u32 hdr = ar[p]; u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & (PH_GARB | PH_VIV)) == 0u) {
      bool is_red = ((hdr & PH_RED) != 0u);
      u64 glue = (u64)(hdr & PH_GLUE_MASK);
      bool take = false;
      if (tier_mode == 0ULL) { take = !is_red; }
      else if (tier_mode == 1ULL) { take = is_red && glue <= h->tier1; }
      else if (tier_mode == 2ULL) { take = is_red && glue > h->tier1 && glue <= h->tier2; }
      else { take = is_red && glue > h->tier2; }
      if (take) {
        budget = budget - 1ULL;
        u64 vc = full_viv_clause(h, (u32)p);
        if (vc == 20ULL) { res = 20ULL; break; }
        if (full_propagate(h) == 1ULL) { res = 20ULL; break; }
      }
    }
    p = np;
  }
  if (res == 1ULL) {
    p = 0ULL;
    while (p < h->arena_len) {
      ar[p] = ar[p] & (~PH_VIV);
      p = (u64)full_arena_next(h, (u32)p);
    }
  }
  h->probing = 0ULL;
  return res;
}

bool full_tarjan_pop_scc(FullHdr *h, u32 root_lit, u32 lit, u32 mark_root) {
  u32 *scc = (u32 *)h->work_stk1; u32 *repr = (u32 *)h->repr;
  u32 *trc = (u32 *)h->tarjan_reach; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *units = (u32 *)h->shrink_stk;
  u64 scc_top = h->tmp_cnt;
  u64 k = scc_top;
  u32 min_lit = lit;
  while (k > 0ULL) {
    k = k - 1ULL; u32 x = scc[k];
    if (x < min_lit) { min_lit = x; }
    if (x == lit) { break; }
  }
  bool failed = (mark_root == 0xFFFFFFFFu);
  u64 j = k;
  while (j < scc_top) {
    u32 other = scc[j]; repr[other] = min_lit; trc[other] = 0xFFFFFFFFu;
    u32 ro = repr[other ^ 1u];
    if (ro == min_lit) {
      if (h->res_sz < h->max_vars) { units[h->res_sz] = min_lit; h->res_sz = h->res_sz + 1ULL; }
      h->inconsistent = 1ULL; break;
    }
    if (ro != 0xFFFFFFFFu && !failed && mark_root <= tmk[other ^ 1u]) {
      if (h->res_sz < h->max_vars) {
        units[h->res_sz] = root_lit ^ 1u; h->res_sz = h->res_sz + 1ULL;
      }
      failed = true;
    }
    j = j + 1ULL;
  }
  h->tmp_cnt = k;
  return failed;
}

u64 full_tarjan_scc(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *repr = (u32 *)h->repr; u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *trc = (u32 *)h->tarjan_reach; u32 *scc = (u32 *)h->work_stk1;
  u32 *dv = (u32 *)h->work_stk2; u32 *dpos = (u32 *)h->wsort;
  u32 *wvec = (u32 *)h->watch_vec; u32 *wstk = (u32 *)h->watch_stk;
  u32 *fl = (u32 *)h->flags;
  u64 i = 0ULL;
  while (i < nlits) { repr[i] = 0xFFFFFFFFu; tmk[i] = 0u; trc[i] = 0u; i = i + 1ULL; }
  u32 reached = 0u; h->tmp_cnt = 0ULL; h->res_sz = 0ULL;
  u64 root = 0ULL;
  while (root < nlits && h->inconsistent == 0ULL) {
    if (tmk[root] == 0u && (fl[root >> 1] & FL_ACTIVE) != 0u) {
      bool failed = false; u32 mroot = reached + 1u;
      u64 dsp = 1ULL; dv[0] = (u32)root; dpos[0] = 0u;
      reached = reached + 1u; tmk[root] = reached; trc[root] = reached;
      scc[h->tmp_cnt] = (u32)root; h->tmp_cnt = h->tmp_cnt + 1ULL;
      while (dsp > 0ULL && h->inconsistent == 0ULL) {
        u32 lit = dv[dsp - 1ULL]; u32 nl = lit ^ 1u;
        u32 pos = dpos[dsp - 1ULL];
        u64 off = (u64)wvec[(u64)nl << 1]; u32 sz = wvec[((u64)nl << 1) + 1ULL];
        if (pos < sz) {
          u32 w0 = wstk[off + (u64)pos];
          if ((w0 & PW_BIN_FLAG) == 0u) { dpos[dsp - 1ULL] = pos + 2u; continue; }
          dpos[dsp - 1ULL] = pos + 1u;
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && (fl[ot >> 1] & FL_ACTIVE) != 0u && tmk[ot] == 0u) {
            reached = reached + 1u; tmk[ot] = reached; trc[ot] = reached;
            scc[h->tmp_cnt] = ot; h->tmp_cnt = h->tmp_cnt + 1ULL;
            dv[dsp] = ot; dpos[dsp] = 0u; dsp = dsp + 1ULL;
          }
          continue;
        }
        u32 p = 0u; u32 rlit = trc[lit];
        while (p < sz) {
          u32 w0 = wstk[off + (u64)p];
          if ((w0 & PW_BIN_FLAG) == 0u) { p = p + 2u; continue; }
          u32 ot = w0 & PW_LIT_MASK;
          if ((u64)ot < nlits && (fl[ot >> 1] & FL_ACTIVE) != 0u && trc[ot] < rlit) {
            rlit = trc[ot];
          }
          p = p + 1u;
        }
        dsp = dsp - 1ULL;
        if (rlit != tmk[lit]) { trc[lit] = rlit; }
        else {
          u32 mr = failed ? 0xFFFFFFFFu : mroot;
          if (full_tarjan_pop_scc(h, (u32)root, lit, mr)) { failed = true; }
        }
      }
    }
    root = root + 1ULL;
  }
  i = 0ULL; while (i < nlits) { if (repr[i] == 0xFFFFFFFFu) { repr[i] = (u32)i; } i = i + 1ULL; }
  return h->res_sz;
}

bool full_subst_elim_vars(FullHdr *h, u64 ucnt) {
  u32 *units = (u32 *)h->shrink_stk;
  u64 k = 0ULL;
  while (k < ucnt) {
    if (!full_add_unit(h, units[k])) { return false; }
    k = k + 1ULL;
  }
  if (full_propagate(h) == 1ULL || h->inconsistent != 0ULL) { return false; }
  u32 *repr = (u32 *)h->repr; u32 *fl = (u32 *)h->flags;
  u64 cv = h->cur_vars; u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u) {
      u32 lit = (u32)(v << 1); u32 rep = repr[lit];
      if (rep != lit) {
        if (h->extend_len + 4ULL <= h->extend_cap) {
          full_extend_push2(h, lit ^ 1u, rep);
          full_extend_push2(h, lit, rep ^ 1u);
          full_set_inactive(h, (u32)v, FL_SUBST);
          h->subst_cnt = h->subst_cnt + 1ULL;
        } else {
          repr[lit] = lit; repr[lit ^ 1u] = lit ^ 1u;
        }
      }
    }
    v = v + 1ULL;
  }
  return true;
}

bool full_subst_rewrite_bins(FullHdr *h) {
  u64 nlits = h->cur_vars << 1;
  u32 *repr = (u32 *)h->repr; u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk; u8 *lm = (u8 *)h->lit_mark;
  u32 *pa = (u32 *)h->work_stk1; u32 *pb = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1]; u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) { l = l + 1ULL; continue; }
    u32 rl = repr[l]; u64 pn = 0ULL;
    u64 p = off; u64 q = off; u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p]; p = p + 1ULL;
      if ((w0 & PW_BIN_FLAG) == 0u) {
        if (p < end) { wstk[q] = w0; wstk[q + 1ULL] = wstk[p]; q = q + 2ULL; p = p + 1ULL; }
        continue;
      }
      u32 ot = w0 & PW_LIT_MASK; u32 rot = ((u64)ot < nlits) ? repr[ot] : ot;
      if (rl == (u32)l && rot == ot) {
        if (lm[ot] == (u8)0) { lm[ot] = (u8)1; wstk[q] = w0; q = q + 1ULL; }
        else if (l < (u64)ot && h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
      } else {
        if (l < (u64)ot) {
          if (h->num_binary > 0ULL) { h->num_binary = h->num_binary - 1ULL; }
          if (rl != (rot ^ 1u) && pn < nlits) { pa[pn] = rl; pb[pn] = rot; pn = pn + 1ULL; }
        }
      }
    }
    u64 c = off;
    while (c < q) {
      if ((wstk[c] & PW_BIN_FLAG) != 0u) { lm[wstk[c] & PW_LIT_MASK] = (u8)0; }
      c = c + 1ULL;
    }
    c = q; while (c < end) { wstk[c] = 0xFFFFFFFFu; c = c + 1ULL; }
    wvec[(l << 1) + 1ULL] = (u32)(q - off); h->wusable = h->wusable + (end - q);
    c = 0ULL;
    while (c < pn) {
      if (pa[c] == pb[c]) { if (!full_add_unit(h, pa[c])) { return false; } }
      else if (full_add_bin(h, pa[c], pb[c]) == 20ULL) { return false; }
      c = c + 1ULL;
    }
    l = l + 1ULL;
  }
  return true;
}

bool full_subst_rewrite_ar(FullHdr *h) {
  u32 *ar = (u32 *)h->arena; u32 *repr = (u32 *)h->repr;
  u8 *lm = (u8 *)h->lit_mark; u64 nlits = h->cur_vars << 1;
  u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL]; u64 np = (u64)full_arena_next(h, (u32)p);
    if ((hdr & PH_GARB) != 0u || sz < 3u) { p = np; continue; }
    bool chg = false; u32 k = 0u;
    while (k < sz) {
      u32 l = ar[p + 3ULL + (u64)k];
      if ((u64)l < nlits && repr[l] != l) { chg = true; break; }
      k = k + 1u;
    }
    if (!chg) { p = np; continue; }
    bool taut = false; u32 nsz = 0u; k = 0u;
    while (k < sz) {
      u32 rl = repr[ar[p + 3ULL + (u64)k]];
      if (lm[rl ^ 1u] != (u8)0) { taut = true; break; }
      if (lm[rl] == (u8)0) { lm[rl] = (u8)1; ar[p + 3ULL + (u64)nsz] = rl; nsz = nsz + 1u; }
      k = k + 1u;
    }
    k = 0u; while (k < nsz) { lm[ar[p + 3ULL + (u64)k]] = (u8)0; k = k + 1u; }
    if (taut || nsz <= 2u) {
      ar[p] = hdr | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
      if (!taut && nsz == 0u) { h->inconsistent = 1ULL; return false; }
      if (!taut && nsz == 1u && !full_add_unit(h, ar[p + 3ULL])) { return false; }
      if (!taut && nsz == 2u && full_add_bin(h, ar[p + 3ULL], ar[p + 4ULL]) == 20ULL) {
        return false;
      }
    } else if (nsz < sz) {
      ar[p + 2ULL] = nsz; ar[p + 1ULL] = 2u;
      if ((hdr & PH_SHRK) == 0u) {
        ar[p] = hdr | PH_SHRK; ar[p + 3ULL + (u64)sz - 1ULL] = 0xFFFFFFFFu;
      }
    }
    p = np;
  }
  return true;
}

u64 full_substitute(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  u64 round = 0ULL;
  while (round < 4ULL && h->inconsistent == 0ULL && h->oom == 0ULL) {
    u64 before = h->subst_cnt;
    u64 ucnt = full_tarjan_scc(h);
    if (h->inconsistent != 0ULL) { return 20ULL; }
    if (!full_subst_elim_vars(h, ucnt)) { return 20ULL; }
    if (h->subst_cnt == before) { break; }
    if (!full_subst_rewrite_bins(h)) { return 20ULL; }
    if (!full_subst_rewrite_ar(h)) { return 20ULL; }
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    round = round + 1ULL;
  }
  return 1ULL;
}

bool full_enter_dense(FullHdr *h) {
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->dense_mode != 0ULL) { return true; }
  full_sweep_bins(h);
  u32 *ar = (u32 *)h->arena; u64 p = 0ULL;
  while (p < h->arena_len) {
    u32 hdr = ar[p]; u32 sz = ar[p + 2ULL];
    if ((hdr & (PH_GARB | PH_RED)) == 0u && sz >= 3u) {
      u32 k = 0u;
      while (k < sz) {
        u32 lit = ar[p + 3ULL + (u64)k];
        if (!full_watch_push(h, lit, sz & PW_LIT_MASK, (u32)p, 2u)) {
          h->oom = 0ULL; full_arena_sweep(h); return false;
        }
        k = k + 1u;
      }
    }
    p = (u64)full_arena_next(h, (u32)p);
  }
  h->dense_mode = 1ULL;
  return true;
}

u64 full_rebuild_watches(FullHdr *h) {
  h->dense_mode = 0ULL;
  while (true) {
    u64 sr = full_arena_sweep(h);
    if (sr == 2ULL) { return 20ULL; }
    if (sr == 3ULL) { return 0ULL; }
    if (full_propagate(h) == 1ULL) { return 20ULL; }
    if (sr == 0ULL) { break; }
  }
  return 1ULL;
}
"

def full3Module : LeanQbe.T.Module :=
  { fns := dimacs_fns ++ full1_fns ++ full2_fns ++ full3_fns, externs := [], exits := [] }

theorem full_has_bin_wf : Func.Wf full_has_bin_body := by t_wf_reify
theorem full_add_bin_wf : Func.Wf full_add_bin_body := by t_wf_reify
theorem full_delete_bin_side_wf : Func.Wf full_delete_bin_side_body := by t_wf_reify
theorem full_delete_binary_wf : Func.Wf full_delete_binary_body := by t_wf_reify
theorem full_set_inactive_wf : Func.Wf full_set_inactive_body := by t_wf_reify
theorem full_add_unit_wf : Func.Wf full_add_unit_body := by t_wf_reify
theorem full_lucky_scan_wf : Func.Wf full_lucky_scan_body := by t_wf_reify
theorem full_lucky_polar_wf : Func.Wf full_lucky_polar_body := by t_wf_reify
theorem full_lucky_wf : Func.Wf full_lucky_body := by t_wf_reify
theorem full_hbr_dom_wf : Func.Wf full_hbr_dom_body := by t_wf_reify
theorem full_probe_prop_lit_wf : Func.Wf full_probe_prop_lit_body := by t_wf_reify
theorem full_probe_prop_wf : Func.Wf full_probe_prop_body := by t_wf_reify
theorem full_probe_flush_hbr_wf : Func.Wf full_probe_flush_hbr_body := by t_wf_reify
theorem full_probe_assume_pair_wf : Func.Wf full_probe_assume_pair_body := by t_wf_reify
theorem full_probe_run_wf : Func.Wf full_probe_run_body := by t_wf_reify
theorem full_trans_lit_wf : Func.Wf full_trans_lit_body := by t_wf_reify
theorem full_transitive_wf : Func.Wf full_transitive_body := by t_wf_reify
theorem full_viv_simplify_wf : Func.Wf full_viv_simplify_body := by t_wf_reify
theorem full_viv_sort_lits_wf : Func.Wf full_viv_sort_lits_body := by t_wf_reify
theorem full_viv_deduce_wf : Func.Wf full_viv_deduce_body := by t_wf_reify
theorem full_viv_commit_wf : Func.Wf full_viv_commit_body := by t_wf_reify
theorem full_viv_clause_wf : Func.Wf full_viv_clause_body := by t_wf_reify
theorem full_vivify_wf : Func.Wf full_vivify_body := by t_wf_reify
theorem full_tarjan_pop_scc_wf : Func.Wf full_tarjan_pop_scc_body := by t_wf_reify
theorem full_tarjan_scc_wf : Func.Wf full_tarjan_scc_body := by t_wf_reify
theorem full_subst_elim_vars_wf : Func.Wf full_subst_elim_vars_body := by t_wf_reify
theorem full_subst_rewrite_bins_wf : Func.Wf full_subst_rewrite_bins_body := by t_wf_reify
theorem full_subst_rewrite_ar_wf : Func.Wf full_subst_rewrite_ar_body := by t_wf_reify
theorem full_substitute_wf : Func.Wf full_substitute_body := by t_wf_reify
theorem full_enter_dense_wf : Func.Wf full_enter_dense_body := by t_wf_reify
theorem full_rebuild_watches_wf : Func.Wf full_rebuild_watches_body := by t_wf_reify

theorem full3_fns_wf : ∀ f ∈ full3_fns, f.Wf := by
  simp only [full3_fns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨full_has_bin_wf, full_add_bin_wf, full_delete_bin_side_wf, full_delete_binary_wf,
    full_set_inactive_wf, full_add_unit_wf, full_lucky_scan_wf, full_lucky_polar_wf,
    full_lucky_wf, full_hbr_dom_wf, full_probe_prop_lit_wf, full_probe_prop_wf,
    full_probe_flush_hbr_wf, full_probe_assume_pair_wf, full_probe_run_wf, full_trans_lit_wf,
    full_transitive_wf, full_viv_simplify_wf, full_viv_sort_lits_wf, full_viv_deduce_wf,
    full_viv_commit_wf, full_viv_clause_wf, full_vivify_wf, full_tarjan_pop_scc_wf,
    full_tarjan_scc_wf, full_subst_elim_vars_wf, full_subst_rewrite_bins_wf,
    full_subst_rewrite_ar_wf, full_substitute_wf, full_enter_dense_wf, full_rebuild_watches_wf⟩

theorem full3_acyclic : full3Module.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.Full
