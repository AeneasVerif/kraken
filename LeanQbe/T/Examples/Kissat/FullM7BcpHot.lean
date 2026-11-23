module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.Examples.Kissat.Full1

/-!
# Kissat M7 Hot-Path Fused BCP (`FullM7BcpHot`)

Drop-in fused hot propagation kernel closing the upstream Kissat 4.0.4 `PROPAGATE_LITERAL`
gap (`propsearch.c:35-42` + `proplit.h:34-187`) inside `FullM7BcpHot`:
1. Hoists hot solver pointers/scalars once before the `prop < trail_end` outer loop.
2. Swaps `c[0]/c[1]` only when `l0 == not_lit` to preserve `[other, not_lit]` 2WL & vivify
   order, then checks `vals[other] > 0` before replacement search (`0` repl writes on `ov > 0`).
3. Performs direct inline watch push onto `repl ^ 1` (plus `rw == not_lit` in-slice keep),
   keeping `h->delayed` untouched so `full_propagate_ignore_hot` satisfies canonical
   `FullPropDecSpecs.fullPropagateIgnoreSpec` directly, with cold `full_prop_lit_ovf_hot`.
4. Drops redundant inner-loop bounds checks already implied by `FullWitnessInv`
   (`trail_lits_lt`, `WatchSliceOk.bin`, `FullArenaClausesInv.refs_wf` & `lits_lt`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpHot

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! full_m7_bcp_hot "
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

extern void full_wstack_defrag(FullHdr *h);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);

#define PH_GARB 0x00080000u
#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu
#define FL_ACTIVE 1u

bool full_prop_lit_ovf_hot(FullHdr *h, u32 rw, u32 w0, u32 cref) {
  return full_watch_push(h, rw, w0, cref, 2u);
}

bool full_prop_chrono_hot(FullHdr *h, u64 t0) {
  u64 te = h->trail_end;
  u64 nlits = h->cur_vars << 1;
  if (t0 >= te) { return true; }
  u32 *lvl = (u32 *)h->level;
  u32 *trl = (u32 *)h->trail;
  u32 *rsns = (u32 *)h->reason;
  u32 *ar = (u32 *)h->arena;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 alen = h->arena_len;
  u64 t = t0;
  while (t < te) {
    u32 ol = trl[t];
    t = t + 1ULL;
    if ((u64)ol >= nlits) { continue; }
    u32 r = rsns[ol >> 1];
    if (r == 0xFFFFFFFFu || (r & PW_BIN_FLAG) != 0u) { continue; }
    if ((u64)r + 3ULL > alen) { continue; }
    u32 hdr = ar[r];
    u32 csz = ar[(u64)r + 2ULL];
    u64 cb = (u64)r + 3ULL;
    if ((hdr & PH_GARB) != 0u || csz < 3u || cb + (u64)csz > alen) { continue; }
    if (ar[cb] != ol) { continue; }
    u32 l1 = ar[cb + 1ULL];
    if ((u64)l1 >= nlits) { continue; }
    u32 best = lvl[l1 >> 1];
    u32 bi = 1u;
    u32 k = 2u;
    while (k < csz) {
      u32 ck = ar[cb + (u64)k];
      if ((u64)ck < nlits) {
        u32 kl = lvl[ck >> 1];
        if (kl > best) { best = kl; bi = k; }
      }
      k = k + 1u;
    }
    if (bi != 1u) {
      u32 nw = ar[cb + (u64)bi];
      if (h->wcap - h->wlen < 2ULL) {
        if (h->wusable > 0ULL) { full_wstack_defrag(h); }
        if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return false; }
      }
      if (!full_watch_push(h, nw, ol & PW_LIT_MASK, r, 2u)) {
        h->oom = 1ULL;
        return false;
      }
      ar[cb + 1ULL] = nw;
      ar[cb + (u64)bi] = l1;
      full_unwatch_large(h, l1, r);
      u64 off = (u64)wvec[(u64)ol << 1];
      u64 sz = (u64)wvec[((u64)ol << 1) + 1ULL];
      if (sz >= 2ULL) {
        u64 p = off + sz;
        u64 off2 = off + 2ULL;
        while (p >= off2) {
          u32 w = wstk[p - 1ULL];
          if (w == r) { wstk[p - 2ULL] = nw & PW_LIT_MASK; break; }
          p = p - 2ULL + (u64)(w >> 31);
        }
      }
    }
  }
  return true;
}

u64 full_propagate_ignore_hot(FullHdr *h, u64 ignore_ref) {
  u64 prop = h->propagated;
  u64 tend = h->trail_end;
  if (prop >= tend) { return 0ULL; }
  if (h->oom != 0ULL) { return 2ULL; }
  i8 *vals = (i8 *)h->values;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  i8 *ph = (i8 *)h->phases;
  u64 nlits = h->cur_vars << 1;
  u64 clvl = h->cur_level;
  u32 clvl32 = (u32)clvl;
  bool rec_ph = (h->probing == 0ULL);
  u64 unass = h->unassigned;
  u64 unfl = h->unflushed;
  u64 ticks = 0ULL;
  while (prop < tend) {
    u64 fl_rem = h->fuel;
    if (fl_rem == 0ULL) {
      h->propagated = prop;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      if (rec_ph) { h->search_ticks = h->search_ticks + ticks; }
      return 2ULL;
    }
    h->fuel = fl_rem - 1ULL;
    u32 lit = trl[prop];
    u32 not_lit = lit ^ 1u;
    u32 *wvec0 = (u32 *)h->watch_vec;
    u64 nl64 = (u64)not_lit << 1;
    u64 off = (u64)wvec0[nl64];
    u64 sz = (u64)wvec0[nl64 + 1ULL];
    if (sz == 0ULL) {
      prop = prop + 1ULL;
      continue;
    }
    ticks = ticks + 1ULL + ((sz + 31ULL) >> 5ULL);
    u64 t0 = 0xFFFFFFFFFFFFFFFFULL;
    if (clvl != 0ULL && (u64)lit < nlits && (u64)lvl[lit >> 1] < clvl) {
      t0 = tend;
    }
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    u64 brk = 0ULL;
    bool ovf = true;
    while (ovf) {
      ovf = false;
      u32 ovf_rw = 0u;
      u32 ovf_other = 0u;
      u32 ovf_cref = 0u;
      u64 ovf_ri = 0ULL;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          p = p + 1ULL;
          u32 blk = w0 & PW_LIT_MASK;
          i8 bv = vals[blk];
          wstk[q] = w0;
          q = q + 1ULL;
          if (bv > (i8)0) { continue; }
          if (bv < (i8)0) {
            brk = 1ULL;
            h->confl_type = 1ULL;
            h->confl_lit0 = (u64)not_lit;
            h->confl_lit1 = (u64)blk;
            break;
          }
          ticks = ticks + 1ULL;
          u32 alvl = lvl[not_lit >> 1];
          u64 bv64 = (u64)(blk >> 1);
          vals[blk] = (i8)1;
          vals[blk ^ 1u] = (i8)(-1);
          if ((fl[bv64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
          if (rec_ph) {
            if ((blk & 1u) != 0u) { ph[bv64] = (i8)(-1); }
            else { ph[bv64] = (i8)1; }
          }
          lvl[bv64] = alvl;
          if (alvl == 0u) {
            rsns[bv64] = 0xFFFFFFFFu;
            fl[bv64] = fl[bv64] & (~FL_ACTIVE);
            unfl = unfl + 1ULL;
          } else {
            rsns[bv64] = PW_BIN_FLAG | not_lit;
          }
          tpos[bv64] = (u32)tend;
          trl[tend] = blk;
          tend = tend + 1ULL;
          continue;
        }
        if ((u64)w0 < nlits && vals[w0] > (i8)0) {
          u32 cref0 = wstk[p + 1ULL];
          p = p + 2ULL;
          wstk[q] = w0;
          wstk[q + 1ULL] = cref0;
          q = q + 2ULL;
          continue;
        }
        u32 cref = wstk[p + 1ULL];
        p = p + 2ULL;
      ticks = ticks + 1ULL;
      u32 chdr = ar[cref];
      if ((chdr & PH_GARB) != 0u) { continue; }
      u64 cbase = (u64)cref + 3ULL;
      u32 l0 = ar[cbase];
      u32 l1 = ar[cbase + 1ULL];
      if (l0 != not_lit && l1 != not_lit) { continue; }
      u32 other = l0 ^ l1 ^ not_lit;
      if (l0 == not_lit) {
        ar[cbase] = other;
        ar[cbase + 1ULL] = not_lit;
      }
      i8 ov = vals[other];
      if (ov > (i8)0) {
        wstk[q] = other;
        wstk[q + 1ULL] = cref;
        q = q + 2ULL;
        continue;
      }
      u64 csz = (u64)ar[(u64)cref + 2ULL];
      u64 srch = (u64)ar[(u64)cref + 1ULL];
      if (srch < 2ULL || srch >= csz) { srch = 2ULL; }
      u64 ri = srch;
      u32 repl = 0u;
      bool found = false;
      while (ri < csz) {
        u32 cand = ar[cbase + ri];
        if (vals[cand] >= (i8)0) { repl = cand; found = true; break; }
        ri = ri + 1ULL;
      }
      if (!found) {
        ri = 2ULL;
        while (ri < srch) {
          u32 cand = ar[cbase + ri];
          if (vals[cand] >= (i8)0) { repl = cand; found = true; break; }
          ri = ri + 1ULL;
        }
      }
      if (found) {
        ticks = ticks + 1ULL;
        ar[(u64)cref + 1ULL] = (u32)ri;
        u32 rw = repl;
        if (rw == not_lit) {
          ar[cbase] = other;
          ar[cbase + 1ULL] = repl;
          ar[cbase + ri] = not_lit;
          wstk[q] = other;
          wstk[q + 1ULL] = cref;
          q = q + 2ULL;
        } else {
          u32 *wvec = (u32 *)h->watch_vec;
          u64 wcap = h->wcap;
          u64 wlen = h->wlen;
          u64 rw64 = (u64)rw << 1;
          u64 roff = (u64)wvec[rw64];
          u64 rsz = (u64)wvec[rw64 + 1ULL];
          if (rsz == 0ULL && wlen + 2ULL <= wcap) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            wvec[rw64] = (u32)wlen;
            wvec[rw64 + 1ULL] = 2u;
            wstk[wlen] = other;
            wstk[wlen + 1ULL] = cref;
            h->wlen = wlen + 2ULL;
          } else if (rsz > 0ULL && roff + rsz == wlen && wlen + 2ULL <= wcap) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            wstk[wlen] = other;
            wstk[wlen + 1ULL] = cref;
            h->wlen = wlen + 2ULL;
            wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
          } else if (rsz > 0ULL && roff + rsz + 2ULL <= wlen &&
                     wstk[roff + rsz] == 0xFFFFFFFFu &&
                     wstk[roff + rsz + 1ULL] == 0xFFFFFFFFu) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            wstk[roff + rsz] = other;
            wstk[roff + rsz + 1ULL] = cref;
            wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
            u64 wu = h->wusable;
            if (wu >= 2ULL) { h->wusable = wu - 2ULL; }
          } else {
            ovf_rw = rw;
            ovf_other = other;
            ovf_cref = cref;
            ovf_ri = ri;
            ovf = true;
            break;
          }
        }
        continue;
      }
      wstk[q] = other;
      wstk[q + 1ULL] = cref;
      q = q + 2ULL;
      if ((u64)cref == ignore_ref) { continue; }
      if (ov < (i8)0) {
        brk = 1ULL;
        h->confl_type = 2ULL;
        h->confl_ref = (u64)cref;
        break;
      }
      ticks = ticks + 1ULL;
      u32 nl_lvl = lvl[not_lit >> 1];
      u32 alvl = nl_lvl;
      if (nl_lvl < clvl32) {
        u32 mx = 0u;
        u64 bi = 0ULL;
        while (bi < csz) {
          u32 clit = ar[cbase + bi];
          if (clit != other) {
            u32 lv = lvl[clit >> 1];
            if (lv > mx) { mx = lv; }
          }
          bi = bi + 1ULL;
        }
        alvl = mx;
      }
      u64 ov64 = (u64)(other >> 1);
      vals[other] = (i8)1;
      vals[other ^ 1u] = (i8)(-1);
      if ((fl[ov64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
      if (rec_ph) {
        if ((other & 1u) != 0u) { ph[ov64] = (i8)(-1); }
        else { ph[ov64] = (i8)1; }
      }
      lvl[ov64] = alvl;
      if (alvl == 0u) {
        rsns[ov64] = 0xFFFFFFFFu;
        fl[ov64] = fl[ov64] & (~FL_ACTIVE);
        unfl = unfl + 1ULL;
      } else {
        rsns[ov64] = cref;
      }
      tpos[ov64] = (u32)tend;
      trl[tend] = other;
      tend = tend + 1ULL;
      }
      if (ovf) {
        bool pushed = full_prop_lit_ovf_hot(h, ovf_rw, ovf_other, ovf_cref);
        u32 *wvec2 = (u32 *)h->watch_vec;
        u64 noff = (u64)wvec2[(u64)not_lit << 1];
        if (noff != off) {
          q = noff + (q - off);
          p = noff + (p - off);
          end = noff + (end - off);
          off = noff;
        }
        if (!pushed) {
          wstk[q] = ovf_other;
          wstk[q + 1ULL] = ovf_cref;
          q = q + 2ULL;
          brk = 2ULL;
          break;
        }
        u64 obase = (u64)ovf_cref + 3ULL;
        ar[obase] = ovf_other;
        ar[obase + 1ULL] = ovf_rw;
        ar[obase + ovf_ri] = not_lit;
      }
    }
    while (p < end) {
      wstk[q] = wstk[p];
      q = q + 1ULL;
      p = p + 1ULL;
    }
    u32 *wvec1 = (u32 *)h->watch_vec;
    wvec1[((u64)not_lit << 1) + 1ULL] = (u32)(q - off);
    if (q < end) {
      h->wusable = h->wusable + (end - q);
      u64 k = q;
      while (k < end) {
        wstk[k] = 0xFFFFFFFFu;
        k = k + 1ULL;
      }
    }
    if (brk != 2ULL && t0 < tend) {
      h->trail_end = tend;
      if (!full_prop_chrono_hot(h, t0)) { brk = 2ULL; }
    }
    if (brk != 0ULL) {
      if (brk == 2ULL) { h->oom = 1ULL; }
      h->propagated = prop + 1ULL;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      if (rec_ph) { h->search_ticks = h->search_ticks + ticks; }
      return brk;
    }
    prop = prop + 1ULL;
  }
  h->propagated = prop;
  h->trail_end = tend;
  h->unassigned = unass;
  h->unflushed = unfl;
  if (rec_ph) { h->search_ticks = h->search_ticks + ticks; }
  return 0ULL;
}

u64 full_bcp_hot(FullHdr *h) {
  return full_propagate_ignore_hot(h, 0xFFFFFFFFULL);
}
"

def m7BcpHot_fns : List Fn := full_m7_bcp_hot_fns

def m7BcpHotModule : LeanQbe.T.Module :=
  { fns := m7BcpHot_fns
    externs :=
      [ ⟨"full_wstack_defrag", [i64], []⟩
      , ⟨"full_unwatch_large", [i64, i32, i32], []⟩
      , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool]⟩ ]
    exits := [] }

theorem full_prop_lit_ovf_hot_wf : Func.Wf full_prop_lit_ovf_hot_body := by t_wf_reify
theorem full_prop_chrono_hot_wf : Func.Wf full_prop_chrono_hot_body := by t_wf_reify
theorem full_propagate_ignore_hot_wf : Func.Wf full_propagate_ignore_hot_body := by
  t_wf_reify
theorem full_bcp_hot_wf : Func.Wf full_bcp_hot_body := by t_wf_reify

theorem m7BcpHot_fns_wf : ∀ f ∈ m7BcpHot_fns, f.Wf := by
  simp only [m7BcpHot_fns, full_m7_bcp_hot_fns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨full_prop_lit_ovf_hot_wf, full_prop_chrono_hot_wf,
    full_propagate_ignore_hot_wf, full_bcp_hot_wf⟩

theorem m7BcpHot_acyclic : m7BcpHotModule.checkAcyclic = true := by
  t_kernel_rfl

/-- Canonical drop-in `Fn` handles for `FullM5` / `FullM7` module splicing. -/
def m7PropLitOvfFn : Fn :=
  ⟨"full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool], full_prop_lit_ovf_hot_body⟩

def m7PropChronoFn : Fn :=
  ⟨"full_prop_chrono_hot", [i64, i64], [.bool], full_prop_chrono_hot_body⟩

def m7PropIgnoreFn : Fn :=
  ⟨"full_propagate_ignore", [i64, i64], [i64], full_propagate_ignore_hot_body⟩

kissat_c0! full_m7_canon_wrap "
typedef struct {
  u64 mv, nc, cur, val;
} KissatDimacs;
typedef struct { KissatDimacs d; } FullHdr;
extern u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref);
u64 full_propagate(FullHdr *h) {
  return full_propagate_ignore(h, 0xFFFFFFFFULL);
}
"

def m7PropFn : Fn :=
  ⟨"full_propagate", [i64], [i64], full_propagate_body⟩

theorem full_propagate_canon_wf : Func.Wf full_propagate_body := by t_wf_reify

end LeanQbe.T.Examples.Kissat.FullM7BcpHot
