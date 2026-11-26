/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Learned Clause Emission, Eager Subsumption & OOM Recovery (`Src/Learn.lean`)

Mirrors upstream `kissat/src/learn.c` (`5` live functions, DAG level `L4`):
- `full_det_new_level` (R4: `kissat_determine_new_level`)
- `full_one_lit_confl` (R4: `kissat_one_literal_on_conflict_level`)
- `full_eager_subsume` (R4: `kissat_eagerly_subsume_last_learned`)
- `full_learn_clause` (R4: `kissat_learn_clause_basic`)
- `full_learn_clause_m6` (R4: `kissat_learn_clause`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Learn

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! learn "
#include \"kissat_internal.h\"

extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_unwatch_large(FullHdr *h, u32 lit, u32 cref);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_backtrack_ac_fid(FullHdr *h, u64 target_lvl);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern u64 full_reduce(FullHdr *h, bool force);
extern u64 full_reduce_m6(FullHdr *h, bool force);
extern u64 full_reduce_purge_c0(FullHdr *h);

u64 full_det_new_level(FullHdr *h, u64 jump) {
  if (h->cur_level == 0ULL) { return 0ULL; }
  u64 back = h->cur_level - 1ULL;
  if (jump >= back) { return jump; }
  if (back - jump > h->chrono_levels) { return back; }
  return jump;
}

u64 full_one_lit_confl(FullHdr *h) {
  u32 *lvl = (u32 *)h->level;
  u32 *ar = (u32 *)h->arena;
  if (h->confl_type == 1ULL) {
    u32 a = (u32)h->confl_lit0; u32 b = (u32)h->confl_lit1;
    u32 la = lvl[a >> 1]; u32 lb = lvl[b >> 1];
    u64 clvl = (la >= lb) ? (u64)la : (u64)lb;
    if (clvl == 0ULL) { return 20ULL; }
    if (clvl < h->cur_level) { full_backtrack_ac_fid(h, clvl); }
    if (la == lb) { return 0ULL; }
    u32 forced = (la > lb) ? a : b;
    u32 other = (la > lb) ? b : a;
    u64 jlvl = (la > lb) ? (u64)lb : (u64)la;
    u64 nlvl = full_det_new_level(h, jlvl);
    full_backtrack_ac_fid(h, nlvl);
    full_assign_lvl(h, forced, (other & PW_LIT_MASK) | PW_BIN_FLAG, (u32)jlvl);
    return 1ULL;
  }
  u32 cref = (u32)h->confl_ref;
  if ((u64)cref + 3ULL > h->arena_len) { return 2ULL; }
  u32 csz = ar[(u64)cref + 2ULL];
  u64 clvl = 0ULL; u64 jlvl = 0ULL; u64 cnt = 0ULL; u32 forced = 0xFFFFFFFFu;
  u32 i = 0u;
  while (i < csz) {
    u32 l = ar[(u64)cref + 3ULL + (u64)i]; u64 ll = (u64)lvl[l >> 1];
    if (cnt == 0ULL || ll > clvl) {
      jlvl = (cnt == 0ULL) ? 0ULL : clvl; clvl = ll; cnt = 1ULL; forced = l;
    } else if (ll == clvl) {
      if (clvl > jlvl) { jlvl = ll; } cnt = cnt + 1ULL;
    } else if (ll > jlvl) { jlvl = ll; }
    i = i + 1u;
  }
  if (clvl == 0ULL) { return 20ULL; }
  if (clvl < h->cur_level) { full_backtrack_ac_fid(h, clvl); }
  u32 pos = 0u;
  while (pos < 2u) {
    u32 lit = ar[(u64)cref + 3ULL + (u64)pos];
    u32 hl = lvl[lit >> 1];
    u32 hp = pos;
    u32 j = pos + 1u;
    while (j < csz) {
      u32 cand = ar[(u64)cref + 3ULL + (u64)j];
      u32 cl = lvl[cand >> 1];
      if (cl > hl) { hl = cl; hp = j; }
      j = j + 1u;
    }
    if (hp != pos) {
      u32 high_lit = ar[(u64)cref + 3ULL + (u64)hp];
      if (hp > 1u) {
        u32 other = ar[(u64)cref + 3ULL + (u64)(pos ^ 1u)];
        if (h->wcap - h->wlen < 2ULL) {
          if (h->wusable > 0ULL) { full_wstack_defrag(h); }
          if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return 2ULL; }
        }
        if (!full_watch_push(h, high_lit, other & PW_LIT_MASK, cref, 2u)) {
          h->oom = 1ULL; return 2ULL;
        }
        ar[(u64)cref + 3ULL + (u64)pos] = high_lit;
        ar[(u64)cref + 3ULL + (u64)hp] = lit;
        full_unwatch_large(h, lit, cref);
      } else {
        ar[(u64)cref + 3ULL + (u64)pos] = high_lit;
        ar[(u64)cref + 3ULL + (u64)hp] = lit;
      }
    }
    pos = pos + 1u;
  }
  if (cnt > 1ULL) { return 0ULL; }
  u64 nlvl = full_det_new_level(h, jlvl);
  full_backtrack_ac_fid(h, nlvl);
  full_assign_lvl(h, forced, cref, (u32)jlvl);
  return 1ULL;
}

void full_eager_subsume(FullHdr *h, u64 new_ref) {
  u8 *lm = (u8 *)h->lit_mark;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *ar = (u32 *)h->arena;
  u32 *ll = (u32 *)h->last_learned;
  i8 *vals = (i8 *)h->values;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u64 tlen = h->tmp_len;
  u64 i = 0ULL;
  while (i < tlen) { lm[tmp[i]] = (u8)1; i = i + 1ULL; }
  bool subsumed = false;
  i = 0ULL;
  while (i < 4ULL) {
    u32 cr = ll[i];
    if (cr != 0xFFFFFFFFu && (u64)cr + 3ULL <= h->arena_len) {
      u32 hdr = ar[cr]; u32 csz = ar[(u64)cr + 2ULL];
      if ((hdr & PH_GARB) == 0u && (hdr & PH_RED) != 0u && (u64)csz > tlen &&
          (u64)cr + 3ULL + (u64)csz <= h->arena_len) {
        u64 need = tlen; u64 rem = (u64)csz; u32 j = 0u;
        while (j < csz) {
          if (lm[ar[(u64)cr + 3ULL + (u64)j]] != (u8)0) {
            need = need - 1ULL; if (need == 0ULL) { break; }
          } else { rem = rem - 1ULL; if (rem < need) { break; } }
          j = j + 1u;
        }
        if (need == 0ULL) {
          bool act = false; u32 rj = 0u;
          while (rj < csz) {
            u32 rl = ar[(u64)cr + 3ULL + (u64)rj];
            if ((u64)rl < (h->cur_vars << 1) && vals[rl] > (i8)0 &&
                lvl[rl >> 1] > 0u && rsns[rl >> 1] == cr) { act = true; break; }
            rj = rj + 1u;
          }
          if (!act) {
            ar[cr] = hdr | PH_GARB;
            h->arena_garbage = h->arena_garbage + 3ULL + (u64)csz;
            ll[i] = 0xFFFFFFFFu;
            h->eager_sub_cnt = h->eager_sub_cnt + 1ULL;
            subsumed = true;
          }
        }
      }
    }
    i = i + 1ULL;
  }
  i = 0ULL;
  while (i < tlen) { lm[tmp[i]] = (u8)0; i = i + 1ULL; }
  if (subsumed) {
    u64 q = 0ULL; u64 p = 0ULL;
    while (p < 4ULL) {
      u32 cr = ll[p];
      if (cr != 0xFFFFFFFFu) { ll[q] = cr; q = q + 1ULL; }
      p = p + 1ULL;
    }
    while (q < 4ULL) { ll[q] = 0xFFFFFFFFu; q = q + 1ULL; }
  }
  if (new_ref < 0x80000000ULL) {
    u64 k = 3ULL;
    while (k > 0ULL) { ll[k] = ll[k - 1ULL]; k = k - 1ULL; }
    ll[0] = (u32)new_ref;
  }
}

u64 full_learn_clause(FullHdr *h, u64 glue) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  i8 *vals = (i8 *)h->values;
  u32 uip_lit = tmp[0];
  if (h->tmp_len == 1ULL) {
    full_backtrack_ac_fid(h, 0ULL);
    if (vals[uip_lit] != (i8)0) { return 0ULL; }
    full_assign_lvl(h, uip_lit, 0xFFFFFFFFu, 0u);
    return 1ULL;
  }
  u64 tlen = h->tmp_len;
  if (tlen > 2ULL) {
    u64 lo = 1ULL;
    u64 hi = tlen - 1ULL;
    while (lo < hi) {
      u32 sw = tmp[lo]; tmp[lo] = tmp[hi]; tmp[hi] = sw;
      lo = lo + 1ULL;
      hi = hi - 1ULL;
    }
    u64 rb = 1ULL;
    while (rb < tlen) {
      u32 rl = lvl[((u64)tmp[rb]) >> 1];
      u64 re = rb + 1ULL;
      while (re < tlen && lvl[((u64)tmp[re]) >> 1] == rl) {
        re = re + 1ULL;
      }
      u64 rl_i = rb;
      u64 rh_i = re - 1ULL;
      while (rl_i < rh_i) {
        u32 sw = tmp[rl_i]; tmp[rl_i] = tmp[rh_i]; tmp[rh_i] = sw;
        rl_i = rl_i + 1ULL;
        rh_i = rh_i - 1ULL;
      }
      rb = re;
    }
  }
  u64 i = 2ULL;
  while (i < tlen) {
    u32 x = tmp[i];
    u32 lx = lvl[((u64)x) >> 1];
    u64 j = i;
    while (j > 1ULL && lvl[((u64)tmp[j - 1ULL]) >> 1] < lx) {
      tmp[j] = tmp[j - 1ULL];
      j = j - 1ULL;
    }
    tmp[j] = x;
    i = i + 1ULL;
  }
  u64 max_lvl = (u64)lvl[((u64)tmp[1]) >> 1];
  if (max_lvl >= h->cur_level) { max_lvl = h->cur_level - 1ULL; }
  u64 nlvl = full_det_new_level(h, max_lvl);
  full_backtrack_ac_fid(h, nlvl);
  if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap || h->wcap - h->wlen < 32ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap) {
      u64 rr = full_reduce(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
  if (new_ref == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) { return 0ULL; }
  if (new_ref != 0xFFFFFFFEULL && new_ref < h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    ar[new_ref] = ar[new_ref] | (31u << 27);
  }
  u32 rsn = (new_ref == 0xFFFFFFFEULL)
    ? ((tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG) : (u32)new_ref;
  full_assign_lvl(h, uip_lit, rsn, (u32)max_lvl);
  full_eager_subsume(h, new_ref);
  return 1ULL;
}

u64 full_learn_clause_m6(FullHdr *h, u64 glue) {
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *lvl = (u32 *)h->level;
  i8 *vals = (i8 *)h->values;
  u32 uip_lit = tmp[0];
  if (h->tmp_len == 1ULL) {
    full_backtrack_ac_fid(h, 0ULL);
    if (vals[uip_lit] != (i8)0) { return 0ULL; }
    full_assign_lvl(h, uip_lit, 0xFFFFFFFFu, 0u);
    return 1ULL;
  }
  u64 tlen = h->tmp_len;
  if (tlen > 2ULL) {
    u64 lo = 1ULL;
    u64 hi = tlen - 1ULL;
    while (lo < hi) {
      u32 sw = tmp[lo]; tmp[lo] = tmp[hi]; tmp[hi] = sw;
      lo = lo + 1ULL;
      hi = hi - 1ULL;
    }
    u64 rb = 1ULL;
    while (rb < tlen) {
      u32 rl = lvl[((u64)tmp[rb]) >> 1];
      u64 re = rb + 1ULL;
      while (re < tlen && lvl[((u64)tmp[re]) >> 1] == rl) {
        re = re + 1ULL;
      }
      u64 rl_i = rb;
      u64 rh_i = re - 1ULL;
      while (rl_i < rh_i) {
        u32 sw = tmp[rl_i]; tmp[rl_i] = tmp[rh_i]; tmp[rh_i] = sw;
        rl_i = rl_i + 1ULL;
        rh_i = rh_i - 1ULL;
      }
      rb = re;
    }
  }
  u64 i = 2ULL;
  while (i < tlen) {
    u32 x = tmp[i];
    u32 lx = lvl[((u64)x) >> 1];
    u64 j = i;
    while (j > 1ULL && lvl[((u64)tmp[j - 1ULL]) >> 1] < lx) {
      tmp[j] = tmp[j - 1ULL];
      j = j - 1ULL;
    }
    tmp[j] = x;
    i = i + 1ULL;
  }
  u64 max_lvl = (u64)lvl[((u64)tmp[1]) >> 1];
  if (max_lvl >= h->cur_level) { max_lvl = h->cur_level - 1ULL; }
  u64 nlvl = full_det_new_level(h, max_lvl);
  full_backtrack_ac_fid(h, nlvl);
  if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap || h->wcap - h->wlen < 32ULL) {
    if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    if (h->arena_len + h->tmp_len + 8ULL > h->arena_cap) {
      u64 rr = full_reduce_m6(h, true);
      if (rr == 20ULL) { return 20ULL; }
      if (rr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
  }
  u64 new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
  u64 step = 0ULL;
  while (new_ref == 0xFFFFFFFFULL && step < 3ULL) {
    if (step == 0ULL) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
    } else {
      u64 gr = (step == 1ULL) ? full_reduce_m6(h, true) : full_reduce_purge_c0(h);
      if (gr == 20ULL) { return 20ULL; }
      if (gr != 1ULL) { return 0ULL; }
      if (h->cur_level != nlvl || vals[uip_lit] != (i8)0) { return 1ULL; }
    }
    new_ref = full_add_clause(h, (u32)h->tmp_len, (u32)glue, true);
    step = step + 1ULL;
  }
  if (new_ref == 0xFFFFFFFFULL || vals[uip_lit] != (i8)0) { return 0ULL; }
  if (new_ref != 0xFFFFFFFEULL && new_ref < h->arena_len) {
    u32 *ar = (u32 *)h->arena;
    ar[new_ref] = ar[new_ref] | (31u << 27);
  }
  u32 rsn = (new_ref == 0xFFFFFFFEULL)
    ? ((tmp[1] & PW_LIT_MASK) | PW_BIN_FLAG) : (u32)new_ref;
  full_assign_lvl(h, uip_lit, rsn, (u32)max_lvl);
  full_eager_subsume(h, new_ref);
  return 1ULL;
}
"

/-- Ordered live functions of `Src/Learn.lean` (`5` fns). -/
def fns : List Fn := learn_fns

end

public section

theorem full_det_new_level_wf : Func.Wf full_det_new_level_body := by kissat_wf_reify
theorem full_one_lit_confl_wf : Func.Wf full_one_lit_confl_body := by kissat_wf_reify
theorem full_eager_subsume_wf : Func.Wf full_eager_subsume_body := by kissat_wf_reify
theorem full_learn_clause_wf : Func.Wf full_learn_clause_body := by kissat_wf_reify
theorem full_learn_clause_m6_wf : Func.Wf full_learn_clause_m6_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, learn_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact full_det_new_level_wf
  · exact full_one_lit_confl_wf
  · exact full_eager_subsume_wf
  · exact full_learn_clause_wf
  · exact full_learn_clause_m6_wf

end

end LeanQbe.T.Examples.Kissat.Src.Learn
