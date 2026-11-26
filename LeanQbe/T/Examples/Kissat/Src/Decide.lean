/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Decision Variable Selection & Phase Choice (`Src/Decide.lean`)

Mirrors upstream `kissat/src/decide.c` (`4` live functions, DAG level `L2`):
- `full_next_dec_var` (R4: `kissat_next_decision_variable`)
- `full_randec_var_m7` (R4: `kissat_next_random_decision`)
- `full_decide_m7` (R4: `kissat_decide_core`)
- `m6_hdr_decide_fid` (R4: `kissat_decide`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Decide

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! decide "
#include \"kissat_internal.h\"

extern u64 full_log10_q16_m7(u64 x);
extern u64 full_lcg_next_m7(FullHdr *h);
extern u64 full_m7_get64(FullHdr *h, u64 idx);
extern void full_m7_set64(FullHdr *h, u64 idx, u64 val);
extern void full_m7_state_init(FullHdr *h);
extern u64 full_heap_pop(FullHdr *h);
extern void full_assign(FullHdr *h, u32 lit, u32 rsn);
extern void m6_hdr_dr_init(FullHdr *h);

u64 full_next_dec_var(FullHdr *h) {
  i8 *vals = (i8 *)h->values;
  u32 *fl = (u32 *)h->flags;
  u64 cv = h->cur_vars;
  if (h->stable != 0ULL) {
    u32 *hp = (u32 *)h->heap;
    u64 hlen = h->heap_len;
    while (hlen > 0ULL && hlen <= cv) {
      u32 top = hp[0];
      if ((u64)top >= cv) { break; }
      if ((fl[top] & FL_ACTIVE) != 0u && vals[(u64)top << 1] == (i8)0) { return (u64)top; }
      full_heap_pop(h);
      hlen = h->heap_len;
    }
  } else {
    u32 *qp = (u32 *)h->q_prev;
    u64 cur = h->q_search_idx;
    u64 steps = 0ULL;
    while (cur < cv && steps < cv) {
      if ((fl[cur] & FL_ACTIVE) != 0u && vals[cur << 1] == (i8)0) {
        u32 *qs = (u32 *)h->q_stamp;
        h->q_search_idx = cur;
        h->q_search_stamp = (u64)qs[cur];
        return cur;
      }
      cur = (u64)qp[cur];
      steps = steps + 1ULL;
    }
    cur = h->q_last;
    steps = 0ULL;
    while (cur < cv && steps < cv) {
      if ((fl[cur] & FL_ACTIVE) != 0u && vals[cur << 1] == (i8)0) {
        u32 *qs = (u32 *)h->q_stamp;
        h->q_search_idx = cur;
        h->q_search_stamp = (u64)qs[cur];
        return cur;
      }
      cur = (u64)qp[cur];
      steps = steps + 1ULL;
    }
  }
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & FL_ACTIVE) != 0u && vals[v << 1] == (i8)0) { return v; }
    v = v + 1ULL;
  }
  return 0xFFFFFFFFFFFFFFFFULL;
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

u64 m6_hdr_decide_fid(FullHdr *h) {
  if (full_decide_m7(h) == 0ULL) { return 0ULL; }
  u64 *e = (u64 *)((u64)h - M6_EXT_BYTES);
  u64 st = e[M6W_DR_STATE];
  if (e[M6W_MAGIC] != M6_HDR_MAGIC || (st >> 63) == 0ULL) {
    m6_hdr_dr_init(h);
    st = e[M6W_DR_STATE];
  }
  u64 mask56 = (1ULL << 56) - 1ULL;
  u64 hi = st & (~mask56);
  u64 decs = st & mask56;
  if (decs < mask56) { e[M6W_DR_STATE] = hi | (decs + 1ULL); }
  return 1ULL;
}
"

/-- Ordered live functions of `Src/Decide.lean` (`4` fns). -/
def fns : List Fn := decide_fns

end

public section

theorem full_next_dec_var_wf : Func.Wf full_next_dec_var_body := by kissat_wf_reify
theorem full_randec_var_m7_wf : Func.Wf full_randec_var_m7_body := by kissat_wf_reify
theorem full_decide_m7_wf : Func.Wf full_decide_m7_body := by kissat_wf_reify
theorem m6_hdr_decide_fid_wf : Func.Wf m6_hdr_decide_fid_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, decide_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact full_next_dec_var_wf
  · exact full_randec_var_m7_wf
  · exact full_decide_m7_wf
  · exact m6_hdr_decide_fid_wf

end

end LeanQbe.T.Examples.Kissat.Src.Decide
