/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Variable Compaction & Remapping (`Src/Compact.lean`)

Mirrors upstream `kissat/src/compact.c` (`13` live functions, DAG level `L3`):
- `full_compact_needed` (R4: `kissat_compacting`)
- `full_compact_flush` (R4: `kissat_compact_flush_trail`)
- `full_compact_mark_live` (R4: `kissat_compact_mark_live`)
- `full_compact_assign_map` (R4: `kissat_compact_assign_map`)
- `full_compact_record_ext` (R4: `kissat_compact_record_extend`)
- `full_compact_bins` (R4: `kissat_compact_binaries`)
- `full_compact_arena` (R4: `kissat_compact_arena`)
- `full_compact_vars` (R4: `kissat_compact_variables`)
- `full_compact_sift_q` (R4: `kissat_compact_queue_sift`)
- `full_compact_vmtf` (R4: `kissat_compact_queue`)
- `full_compact_sift_h` (R4: `kissat_compact_heap_sift`)
- `full_compact_heap` (R4: `kissat_compact_heap`)
- `full_compact` (R4: `kissat_compact`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Compact

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! compact "
#include \"kissat_internal.h\"

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern u64 full_flush_trail(FullHdr *h);
extern bool full_rewatch_arena(FullHdr *h, u64 dst);

bool full_compact_needed(FullHdr *h) {
  if (h->cur_level != 0ULL || h->dense_mode != 0ULL) { return false; }
  u64 cv = h->cur_vars;
  if (cv < 128ULL || cv <= h->unassigned) { return false; }
  u64 dead = cv - h->unassigned;
  return (dead * 10ULL > cv);
}

u64 full_compact_flush(FullHdr *h) {
  return full_flush_trail(h);
}

void full_compact_mark_live(FullHdr *h) {
  u64 cv = h->cur_vars;
  u64 nlits = cv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *map = (u32 *)h->work_stk1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u64 v = 0ULL;
  while (v < cv) {
    map[v] = 0u;
    v = v + 1ULL;
  }
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 end = off + (u64)wvec[(l << 1) + 1ULL];
    u32 lneg = ((u32)l) ^ 1u;
    u64 p = off;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        if ((u64)ot < nlits && ot != lneg &&
            vals[l] == (i8)0 && vals[ot] == (i8)0 &&
            (fl[l >> 1] & FL_ACTIVE) != 0u &&
            (fl[ot >> 1] & FL_ACTIVE) != 0u) {
          map[l >> 1] = 1u;
          map[ot >> 1] = 1u;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    l = l + 1ULL;
  }
  u64 alen = h->arena_len;
  u64 pos = 0ULL;
  while (pos < alen) {
    if (pos + 3ULL > alen) { break; }
    u32 hdr = ar[pos];
    u32 csz = ar[pos + 2ULL];
    u64 npos = (u64)full_arena_next(h, (u32)pos);
    if ((hdr & PH_GARB) == 0u && csz >= 3u && pos + 3ULL + (u64)csz <= alen) {
      bool sat = false;
      bool has_dead = false;
      u32 ucnt = 0u;
      u32 i = 0u;
      while (i < csz) {
        u32 lit = ar[pos + 3ULL + (u64)i];
        if ((u64)lit < nlits) {
          i8 lv = vals[lit];
          if (lv > (i8)0) { sat = true; break; }
          if (lv == (i8)0) {
            if ((fl[lit >> 1] & FL_ACTIVE) == 0u) {
              has_dead = true;
            } else {
              ucnt = ucnt + 1u;
            }
          }
        }
        i = i + 1u;
      }
      if (!sat && !((hdr & PH_RED) != 0u && has_dead) && ucnt >= 1u) {
        i = 0u;
        while (i < csz) {
          u32 lit = ar[pos + 3ULL + (u64)i];
          if ((u64)lit < nlits && vals[lit] == (i8)0 &&
              (fl[lit >> 1] & FL_ACTIVE) != 0u) {
            map[lit >> 1] = 1u;
          }
          i = i + 1u;
        }
      }
    }
    pos = npos;
  }
}

u64 full_compact_assign_map(FullHdr *h) {
  u64 cv = h->cur_vars;
  i8 *vals = (i8 *)h->values;
  u32 *map = (u32 *)h->work_stk1;
  u32 *inv = (u32 *)h->work_stk2;
  u64 ncv = 0ULL;
  u64 v = 0ULL;
  while (v < cv) {
    if (map[v] != 0u && vals[v << 1] == (i8)0) {
      map[v] = (u32)ncv;
      inv[ncv] = (u32)v;
      ncv = ncv + 1ULL;
    } else {
      map[v] = 0xFFFFFFFFu;
    }
    v = v + 1ULL;
  }
  return ncv;
}

bool full_compact_record_ext(FullHdr *h, u64 old_cv, u64 ncv) {
  if (ncv >= old_cv || h->extend_len > h->extend_cap) { return false; }
  i8 *vals = (i8 *)h->values;
  u32 *inv = (u32 *)h->work_stk2;
  u32 *ext = (u32 *)h->extend_stk;
  u64 nfix = 0ULL;
  u64 v = 0ULL;
  while (v < old_cv) {
    if (vals[v << 1] != (i8)0) { nfix = nfix + 1ULL; }
    v = v + 1ULL;
  }
  u64 need = nfix + ncv + 1ULL;
  if (need > h->extend_cap - h->extend_len) { return false; }
  u64 p = h->extend_len;
  v = 0ULL;
  while (v < old_cv) {
    i8 vv = vals[v << 1];
    if (vv != (i8)0) {
      u32 lit = ((u32)(v << 1)) | ((vv < (i8)0) ? 1u : 0u);
      ext[p] = lit | EXT_BLK_FLAG;
      p = p + 1ULL;
    }
    v = v + 1ULL;
  }
  ext[p] = EXT_BLK_FLAG | EXT_COMPACT_FLAG | ((u32)ncv & 0x3FFFFFFFu);
  p = p + 1ULL;
  u64 nv = 0ULL;
  while (nv < ncv) {
    ext[p] = inv[nv];
    p = p + 1ULL;
    nv = nv + 1ULL;
  }
  h->extend_len = p;
  return true;
}

void full_compact_bins(FullHdr *h, u64 old_cv, u64 ncv) {
  u64 nlits = old_cv << 1;
  i8 *vals = (i8 *)h->values;
  u32 *map = (u32 *)h->work_stk1;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 kept = 0ULL;
  u64 l = 0ULL;
  while (l < nlits) {
    u64 off = (u64)wvec[l << 1];
    u64 sz = (u64)wvec[(l << 1) + 1ULL];
    if (sz == 0ULL) {
      wvec[l << 1] = 0u;
      l = l + 1ULL;
      continue;
    }
    bool keep_l = (map[l >> 1] != 0xFFFFFFFFu && vals[l] == (i8)0);
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    while (p < end) {
      u32 w0 = wstk[p];
      if ((w0 & PW_BIN_FLAG) != 0u) {
        u32 ot = w0 & PW_LIT_MASK;
        if (keep_l && (u64)ot < nlits && map[ot >> 1] != 0xFFFFFFFFu && vals[ot] == (i8)0) {
          u32 not_l = (map[ot >> 1] << 1) | (ot & 1u);
          wstk[q] = (not_l & PW_LIT_MASK) | PW_BIN_FLAG;
          q = q + 1ULL;
          kept = kept + 1ULL;
        }
        p = p + 1ULL;
      } else {
        p = p + 2ULL;
      }
    }
    u64 k = q;
    while (k < end) { wstk[k] = 0xFFFFFFFFu; k = k + 1ULL; }
    if (q == off) {
      wvec[l << 1] = 0u;
      wvec[(l << 1) + 1ULL] = 0u;
    } else {
      wvec[(l << 1) + 1ULL] = (u32)(q - off);
    }
    h->wusable = h->wusable + (end - q);
    l = l + 1ULL;
  }
  h->num_binary = kept >> 1;
  u64 v = 0ULL;
  while (v < old_cv) {
    u32 nv = map[v];
    if (nv != 0xFFFFFFFFu && (u64)nv != v) {
      u64 sw = v << 2;
      u64 dw = (u64)nv << 2;
      wvec[dw] = wvec[sw];
      wvec[dw + 1ULL] = wvec[sw + 1ULL];
      wvec[dw + 2ULL] = wvec[sw + 2ULL];
      wvec[dw + 3ULL] = wvec[sw + 3ULL];
    }
    v = v + 1ULL;
  }
  v = ncv;
  while (v < old_cv) {
    u64 wb = v << 2;
    wvec[wb] = 0u;
    wvec[wb + 1ULL] = 0u;
    wvec[wb + 2ULL] = 0u;
    wvec[wb + 3ULL] = 0u;
    v = v + 1ULL;
  }
}

u64 full_compact_arena(FullHdr *h, u64 old_cv) {
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *map = (u32 *)h->work_stk1;
  u64 nlits = old_cv << 1;
  u64 alen = h->arena_len;
  u64 src = 0ULL;
  u64 dst = 0ULL;
  u64 first_red = 0xFFFFFFFFULL;
  u64 irred = 0ULL;
  u64 redd = 0ULL;
  u64 status = 0ULL;
  while (src < alen) {
    if (src + 3ULL > alen) { break; }
    u32 hdr = ar[src];
    u32 old_sz = ar[src + 2ULL];
    u64 nsrc = (u64)full_arena_next(h, (u32)src);
    if ((hdr & PH_GARB) != 0u || old_sz < 3u || src + 3ULL + (u64)old_sz > alen) {
      src = nsrc;
      continue;
    }
    bool sat = false;
    u32 new_sz = 0u;
    u32 i = 0u;
    while (i < old_sz) {
      u32 lit = ar[src + 3ULL + (u64)i];
      if ((u64)lit < nlits) {
        i8 lv = vals[lit];
        if (lv > (i8)0) { sat = true; break; }
        if (lv == (i8)0) {
          u32 nv = map[lit >> 1];
          if (nv == 0xFFFFFFFFu) { sat = true; break; }
          ar[dst + 3ULL + (u64)new_sz] = (nv << 1) | (lit & 1u);
          new_sz = new_sz + 1u;
        }
      }
      i = i + 1u;
    }
    if (sat) { src = nsrc; continue; }
    if (new_sz == 0u) { status = 2ULL; break; }
    if (new_sz == 1u) { src = nsrc; continue; }
    if (new_sz == 2u) {
      u32 l0 = ar[dst + 3ULL];
      u32 l1 = ar[dst + 4ULL];
      u32 b0 = (l1 & PW_LIT_MASK) | PW_BIN_FLAG;
      u32 b1 = (l0 & PW_LIT_MASK) | PW_BIN_FLAG;
      if (!full_watch_push(h, l0, b0, 0u, 1u) ||
          !full_watch_push(h, l1, b1, 0u, 1u)) {
        h->oom = 1ULL;
        status = 3ULL;
        break;
      }
      h->num_binary = h->num_binary + 1ULL;
      src = nsrc;
      continue;
    }
    ar[dst] = hdr & (~(PH_SHRK | PH_RSN));
    ar[dst + 1ULL] = 2u;
    ar[dst + 2ULL] = new_sz;
    if ((hdr & PH_RED) != 0u) {
      if (first_red == 0xFFFFFFFFULL) { first_red = dst; }
      redd = redd + 1ULL;
    } else {
      irred = irred + 1ULL;
    }
    dst = dst + 3ULL + (u64)new_sz;
    src = nsrc;
  }
  h->arena_len = dst;
  h->arena_garbage = 0ULL;
  h->first_reducible = first_red;
  h->num_irred = irred;
  h->num_redundant = redd;
  u32 *ll = (u32 *)h->last_learned;
  u64 li = 0ULL;
  while (li < 16ULL) { ll[li] = 0xFFFFFFFFu; li = li + 1ULL; }
  return status;
}

void full_compact_vars(FullHdr *h, u64 old_cv, u64 ncv) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *ftrl = (u32 *)h->frame_trail;
  u32 *fdec = (u32 *)h->frame_dec;
  i8 *ph = (i8 *)h->phases;
  i8 *ptgt = (i8 *)h->phases_target;
  i8 *pbst = (i8 *)h->phases_best;
  i8 *wbst = (i8 *)h->walk_best;
  u64 *sc = (u64 *)h->score;
  u32 *qs = (u32 *)h->q_stamp;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *ps = (u32 *)h->pos;
  u32 *inv = (u32 *)h->work_stk2;
  u64 l = 0ULL;
  u64 nlits = old_cv << 1;
  while (l < nlits) { vals[l] = (i8)0; l = l + 1ULL; }
  u64 tgt_asg = 0ULL;
  u64 bst_asg = 0ULL;
  u64 nv = 0ULL;
  while (nv < ncv) {
    u32 ov = inv[nv];
    fl[nv] = fl[ov];
    ph[nv] = ph[ov];
    i8 tv = ptgt[ov];
    i8 bv = pbst[ov];
    ptgt[nv] = tv;
    pbst[nv] = bv;
    if (tv != (i8)0) { tgt_asg = tgt_asg + 1ULL; }
    if (bv != (i8)0) { bst_asg = bst_asg + 1ULL; }
    wbst[nv] = wbst[ov];
    sc[nv] = sc[ov];
    qs[nv] = qs[ov];
    lvl[nv] = 0u;
    rsns[nv] = 0xFFFFFFFFu;
    nv = nv + 1ULL;
  }
  u64 v = ncv;
  while (v < old_cv) {
    fl[v] = 0u;
    lvl[v] = 0u;
    rsns[v] = 0xFFFFFFFFu;
    sc[v] = 0ULL;
    qs[v] = 0u;
    qp[v] = 0xFFFFFFFFu;
    qn[v] = 0xFFFFFFFFu;
    ps[v] = 0xFFFFFFFFu;
    v = v + 1ULL;
  }
  ftrl[0] = 0u;
  fdec[0] = 0xFFFFFFFFu;
  h->trail_end = 0ULL;
  h->propagated = 0ULL;
  h->cur_level = 0ULL;
  h->unflushed = 0ULL;
  h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL;
  h->target_assigned = tgt_asg;
  h->best_assigned = bst_asg;
  h->cur_vars = ncv;
  h->unassigned = ncv;
  if (ncv < h->d.mv) { h->d.mv = ncv; h->bva_cap = h->max_vars - ncv; }
}

void full_compact_sift_q(u32 *qs, u32 *ws, u64 start, u64 n) {
  u64 root = start;
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    u32 cv = ws[ch];
    u32 cs = qs[cv];
    if (ch + 1ULL < n) {
      u32 sv = ws[ch + 1ULL];
      u32 ss = qs[sv];
      if (ss > cs) { ch = ch + 1ULL; cv = sv; cs = ss; }
    }
    u32 rv = ws[root];
    if (qs[rv] >= cs) { break; }
    ws[root] = cv;
    ws[ch] = rv;
    root = ch;
  }
}

void full_compact_vmtf(FullHdr *h, u64 ncv) {
  if (ncv == 0ULL) {
    h->q_first = 0xFFFFFFFFULL;
    h->q_last = 0xFFFFFFFFULL;
    h->q_search_idx = 0xFFFFFFFFULL;
    h->q_search_stamp = 0ULL;
    h->q_cur_stamp = 0ULL;
    return;
  }
  u32 *qs = (u32 *)h->q_stamp;
  u32 *qp = (u32 *)h->q_prev;
  u32 *qn = (u32 *)h->q_next;
  u32 *ws = (u32 *)h->wsort;
  u64 i = 0ULL;
  while (i < ncv) { ws[i] = (u32)i; i = i + 1ULL; }
  if (ncv > 1ULL) {
    u64 start = ncv >> 1;
    while (start > 0ULL) {
      start = start - 1ULL;
      full_compact_sift_q(qs, ws, start, ncv);
    }
    u64 end = ncv - 1ULL;
    while (end > 0ULL) {
      u32 tmp = ws[0];
      ws[0] = ws[end];
      ws[end] = tmp;
      full_compact_sift_q(qs, ws, 0ULL, end);
      end = end - 1ULL;
    }
  }
  i = 0ULL;
  while (i < ncv) {
    u32 v = ws[i];
    qp[v] = (i == 0ULL) ? 0xFFFFFFFFu : ws[i - 1ULL];
    qn[v] = (i + 1ULL >= ncv) ? 0xFFFFFFFFu : ws[i + 1ULL];
    qs[v] = (u32)(i + 1ULL);
    i = i + 1ULL;
  }
  h->q_first = (u64)ws[0];
  h->q_last = (u64)ws[ncv - 1ULL];
  h->q_search_idx = h->q_last;
  h->q_search_stamp = ncv;
  h->q_cur_stamp = ncv;
}

void full_compact_sift_h(u64 *sc, u32 *hp, u32 *ps, u64 start, u64 n) {
  u64 root = start;
  u32 rv = hp[start];
  u64 rsc = sc[rv];
  while (true) {
    u64 ch = (root << 1) + 1ULL;
    if (ch >= n) { break; }
    u32 cv = hp[ch];
    u64 cs = sc[cv];
    if (ch + 1ULL < n) {
      u32 sv = hp[ch + 1ULL];
      u64 ss = sc[sv];
      if (ss > cs) { ch = ch + 1ULL; cv = sv; cs = ss; }
    }
    if (rsc >= cs) { break; }
    hp[root] = cv;
    ps[cv] = (u32)root;
    root = ch;
  }
  hp[root] = rv;
  ps[rv] = (u32)root;
}

void full_compact_heap(FullHdr *h, u64 ncv) {
  u64 *sc = (u64 *)h->score;
  u32 *hp = (u32 *)h->heap;
  u32 *ps = (u32 *)h->pos;
  u64 v = 0ULL;
  while (v < ncv) {
    hp[v] = (u32)v;
    ps[v] = (u32)v;
    v = v + 1ULL;
  }
  h->heap_len = ncv;
  if (ncv > 1ULL) {
    u64 start = ncv >> 1;
    while (start > 0ULL) {
      start = start - 1ULL;
      full_compact_sift_h(sc, hp, ps, start, ncv);
    }
  }
}

u64 full_compact(FullHdr *h) {
  if (h->dense_mode != 0ULL) { return 1ULL; }
  u64 fst = full_compact_flush(h);
  if (fst != 1ULL) { return fst; }
  u64 old_cv = h->cur_vars;
  if (old_cv == 0ULL) { return 1ULL; }
  full_compact_mark_live(h);
  u64 ncv = full_compact_assign_map(h);
  if (ncv == old_cv) { return 1ULL; }
  if (!full_compact_record_ext(h, old_cv, ncv)) { return 1ULL; }
  full_compact_bins(h, old_cv, ncv);
  full_wstack_defrag(h);
  u64 ast = full_compact_arena(h, old_cv);
  full_compact_vars(h, old_cv, ncv);
  full_compact_vmtf(h, ncv);
  full_compact_heap(h, ncv);
  if (ast == 2ULL) { h->inconsistent = 1ULL; return 20ULL; }
  if (ast == 3ULL) { h->oom = 1ULL; return 0ULL; }
  if (!full_rewatch_arena(h, h->arena_len)) { h->oom = 1ULL; return 0ULL; }
  return 1ULL;
}
"

/-- Ordered live functions of `Src/Compact.lean` (`13` fns). -/
def fns : List Fn := compact_fns

end

public section

theorem full_compact_needed_wf : Func.Wf full_compact_needed_body := by kissat_wf_reify
theorem full_compact_flush_wf : Func.Wf full_compact_flush_body := by kissat_wf_reify
theorem full_compact_mark_live_wf : Func.Wf full_compact_mark_live_body := by kissat_wf_reify
theorem full_compact_assign_map_wf : Func.Wf full_compact_assign_map_body := by kissat_wf_reify
theorem full_compact_record_ext_wf : Func.Wf full_compact_record_ext_body := by kissat_wf_reify
theorem full_compact_bins_wf : Func.Wf full_compact_bins_body := by kissat_wf_reify
theorem full_compact_arena_wf : Func.Wf full_compact_arena_body := by kissat_wf_reify
theorem full_compact_vars_wf : Func.Wf full_compact_vars_body := by kissat_wf_reify
theorem full_compact_sift_q_wf : Func.Wf full_compact_sift_q_body := by kissat_wf_reify
theorem full_compact_vmtf_wf : Func.Wf full_compact_vmtf_body := by kissat_wf_reify
theorem full_compact_sift_h_wf : Func.Wf full_compact_sift_h_body := by kissat_wf_reify
theorem full_compact_heap_wf : Func.Wf full_compact_heap_body := by kissat_wf_reify
theorem full_compact_wf : Func.Wf full_compact_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, compact_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_compact_needed_wf
  · exact full_compact_flush_wf
  · exact full_compact_mark_live_wf
  · exact full_compact_assign_map_wf
  · exact full_compact_record_ext_wf
  · exact full_compact_bins_wf
  · exact full_compact_arena_wf
  · exact full_compact_vars_wf
  · exact full_compact_sift_q_wf
  · exact full_compact_vmtf_wf
  · exact full_compact_sift_h_wf
  · exact full_compact_heap_wf
  · exact full_compact_wf

end

end LeanQbe.T.Examples.Kissat.Src.Compact
