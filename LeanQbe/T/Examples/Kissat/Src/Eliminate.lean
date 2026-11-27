/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Bounded Variable Elimination (BVE) & Resolution (`Src/Eliminate.lean`)

Mirrors upstream `kissat/src/eliminate.c, resolve.c` (`16` live functions, DAG level `L5`):
- `full_bve_collect_m7` (R4: `kissat_bve_collect_occurrences`)
- `full_bve_resolve_pair` (R4: `kissat_generate_resolvent_pair`)
- `full_bve_weaken` (R4: `kissat_bve_weaken_clauses`)
- `full_bve_commit_res` (R4: `kissat_bve_commit_resolvents`)
- `full_bve_ext_need` (R4: `kissat_bve_extend_need`)
- `full_bve_weaken_unit_fid` (R4: `kissat_bve_weaken_unit`)
- `full_bve_var_m7` (R4: `kissat_eliminate_variable`)
- `full_bve_var_key_m7` (R4: `kissat_eliminate_variable_score`)
- `full_bve_heap_up_m7` (R4: `kissat_elim_heap_up`)
- `full_bve_heap_down_m7` (R4: `kissat_elim_heap_down`)
- `full_bve_heap_push_m7` (R4: `kissat_elim_heap_push`)
- `full_bve_heap_pop_m7` (R4: `kissat_elim_heap_pop`)
- `full_bve_collect_nbrs_m7` (R4: `kissat_elim_collect_neighbors`)
- `full_elim_bve_m7` (R4: `kissat_eliminate_variables`)
- `full_has_elim_cands_fid`
- `full_eliminate_m6` (R4: `kissat_eliminate`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Eliminate

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! eliminate "
#include \"kissat_internal.h\"

extern bool full_extend_push2(FullHdr *h, u32 blk_lit, u32 other);
extern void full_delete_binary(FullHdr *h, u32 a, u32 b);
extern bool full_extend_push_cl(FullHdr *h, u32 blk_lit, u32 cref);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_alloc_cl(FullHdr *h, u32 sz, u32 glue, bool red);
extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_set_inactive(FullHdr *h, u32 v, u32 flag);
extern void full_bve_gates_fid(FullHdr *h, u32 v, u32 np, u32 nn);
extern void full_bve_gates_m7(FullHdr *h, u32 v, u32 np, u32 nn);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_wstack_defrag(FullHdr *h);
extern bool full_dense_flush_units_m7(FullHdr *h);
extern u64 full_dense_occ_cnt_fid(FullHdr *h, u32 lit, u64 cap);
extern u64 f64u_to_u64(u64 a);
extern u64 full_elim_dticks(FullHdr *h, bool initial);
extern u64 f64u_mul(u64 a, u64 b);
extern u64 f64u_nlogpown(u64 count, u64 exponent);
extern u64 full_scale_delta(FullHdr *h, u64 delta);
extern bool full_enter_dense_ex_fid(FullHdr *h, bool connect_large);
extern u64 full_forward_sub_m7(FullHdr *h, u64 budget);
extern u64 full_rebuild_watches(FullHdr *h);
extern void full_update_classify_fid(FullHdr *h);

u32 full_bve_collect_m7(FullHdr *h, u32 lit, u32 *out, u32 cap) {
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u64 off = (u64)wvec[(u64)lit << 1];
  u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
  u64 p = off;
  u32 cnt = 0u;
  while (p < end) {
    u32 w0 = wstk[p];
    p = p + 1ULL;
    if ((w0 & PW_BIN_FLAG) != 0u) {
      u32 ot = w0 & PW_LIT_MASK;
      if (vals[ot] > (i8)0) { continue; }
      if (cnt >= cap) { return 0xFFFFFFFFu; }
      out[cnt] = w0;
      cnt = cnt + 1u;
      continue;
    }
    if (p >= end) { break; }
    u32 cr = wstk[p];
    p = p + 1ULL;
    if ((ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
    if (ar[(u64)cr + 2ULL] > 100u) { return 0xFFFFFFFFu; }
    if (cnt >= cap) { return 0xFFFFFFFFu; }
    out[cnt] = cr;
    cnt = cnt + 1u;
  }
  return cnt;
}

bool full_bve_resolve_pair(FullHdr *h, u32 v, u32 pc, u32 nc) {
  u32 *ar = (u32 *)h->arena; u8 *lm = (u8 *)h->lit_mark; u32 *tmp = (u32 *)h->tmp_lits;
  i8 *vals = (i8 *)h->values; u32 pl = v << 1; u32 nl = pl | 1u;
  u32 rlen = 0u; bool taut = false;
  if ((pc & PW_BIN_FLAG) != 0u) {
    u32 l = pc & PW_LIT_MASK; if (vals[l] > (i8)0) { taut = true; }
    else if (vals[l] == (i8)0) { lm[l] = (u8)1; tmp[rlen] = l; rlen = rlen + 1u; }
  } else {
    u32 psz = ar[(u64)pc + 2ULL]; u32 i = 0u;
    while (i < psz) {
      u32 l = ar[(u64)pc + 3ULL + (u64)i];
      if (l != pl) {
        if (vals[l] > (i8)0 || lm[l ^ 1u] != (u8)0) { taut = true; break; }
        if (vals[l] == (i8)0 && lm[l] == (u8)0) { lm[l] = (u8)1; tmp[rlen] = l; rlen = rlen + 1u; }
      }
      i = i + 1u;
    }
  }
  if (!taut) {
    if ((nc & PW_BIN_FLAG) != 0u) {
      u32 l = nc & PW_LIT_MASK;
      if (vals[l] > (i8)0 || lm[l ^ 1u] != (u8)0) { taut = true; }
      else if (vals[l] == (i8)0 && lm[l] == (u8)0) {
        lm[l] = (u8)1; tmp[rlen] = l; rlen = rlen + 1u;
      }
    } else {
      u32 nsz = ar[(u64)nc + 2ULL]; u32 i = 0u;
      while (i < nsz) {
        u32 l = ar[(u64)nc + 3ULL + (u64)i];
        if (l != nl) {
          if (vals[l] > (i8)0 || lm[l ^ 1u] != (u8)0) { taut = true; break; }
          if (vals[l] == (i8)0 && lm[l] == (u8)0) {
            lm[l] = (u8)1; tmp[rlen] = l; rlen = rlen + 1u;
          }
        }
        i = i + 1u;
      }
    }
  }
  u32 k = 0u; while (k < rlen) { lm[tmp[k]] = (u8)0; k = k + 1u; }
  h->tmp_len = (u64)rlen; return !taut;
}

bool full_bve_weaken(FullHdr *h, u32 blk_lit, u32 off, u32 cnt) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *ar = (u32 *)h->arena; u32 i = 0u;
  while (i < cnt) {
    u32 w = scr[off + i];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      if (!full_extend_push2(h, blk_lit, ot)) { return false; }
      full_delete_binary(h, blk_lit, ot);
    } else {
      if (!full_extend_push_cl(h, blk_lit, w)) { return false; }
      ar[w] = ar[w] | PH_GARB; h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)w + 2ULL];
    }
    i = i + 1u;
  }
  return true;
}

u64 full_bve_commit_res(FullHdr *h, u64 r_off, u64 r_end) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *fl = (u32 *)h->flags;
  u64 cv = h->cur_vars;
  u64 p = r_off;
  while (p < r_end) {
    u32 sz = scr[p]; p = p + 1ULL;
    if (sz == 0u) { h->inconsistent = 1ULL; return 20ULL; }
    if (sz == 1u) { if (!full_add_unit(h, scr[p])) { return 20ULL; } }
    else if (sz == 2u) {
      u32 l0 = scr[p]; u32 l1 = scr[p + 1ULL];
      u64 br = full_add_bin(h, l0, l1);
      if (br == 20ULL) { return 20ULL; }
      if (br == 2ULL) { return 2ULL; }
      u32 v0 = l0 >> 1; u32 v1 = l1 >> 1;
      if ((u64)v0 < cv) {
        fl[v0] = fl[v0] | FL_SUBSUME | FL_ELIM_C | (((l0 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      }
      if ((u64)v1 < cv) {
        fl[v1] = fl[v1] | FL_SUBSUME | FL_ELIM_C | (((l1 & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
      }
    } else {
      u64 cr = full_alloc_cl(h, sz, 0u, false);
      if (cr == 0xFFFFFFFFULL) { h->oom = 1ULL; return 2ULL; }
      u32 *ar = (u32 *)h->arena;
      ar[cr] = ar[cr] | PH_SUBSUME;
      u32 k = 0u;
      while (k < sz) {
        u32 lk = scr[p + (u64)k];
        ar[cr + 3ULL + (u64)k] = lk;
        u32 vk = lk >> 1;
        if ((u64)vk < cv) {
          fl[vk] = fl[vk] | FL_SUBSUME | FL_ELIM_C | (((lk & 1u) != 0u) ? FL_FACT_N : FL_FACT_P);
        }
        k = k + 1u;
      }
      k = 0u;
      while (k < sz) {
        if (!full_watch_push(h, ar[cr + 3ULL + (u64)k], sz & PW_LIT_MASK, (u32)cr, 2u)) {
          ar[cr] = ar[cr] | PH_GARB;
          h->arena_garbage = h->arena_garbage + 3ULL + (u64)sz;
          h->oom = 1ULL; return 2ULL;
        }
        k = k + 1u;
      }
      h->num_irred = h->num_irred + 1ULL;
    }
    p = p + (u64)sz;
  }
  return 1ULL;
}

u64 full_bve_ext_need(FullHdr *h, u32 off, u32 cnt) {
  u32 *scr = (u32 *)h->scratch_buf; u32 *ar = (u32 *)h->arena;
  u64 need = 0ULL; u32 i = 0u;
  while (i < cnt) {
    u32 w = scr[off + i];
    if ((w & PW_BIN_FLAG) != 0u) { need = need + 2ULL; }
    else { need = need + (u64)ar[(u64)w + 2ULL] + 1ULL; }
    i = i + 1u;
  }
  return need;
}

bool full_bve_weaken_unit_fid(FullHdr *h, u32 blk_lit, u32 off, u32 cnt) {
  if (cnt == 0u) { return true; }
  if (h->extend_len >= h->extend_cap) { return false; }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  u32 i = 0u;
  while (i < cnt) {
    u32 w = scr[off + i];
    if ((w & PW_BIN_FLAG) != 0u) {
      u32 ot = w & PW_LIT_MASK;
      full_delete_binary(h, blk_lit, ot);
    } else {
      ar[w] = ar[w] | PH_GARB;
      h->arena_garbage = h->arena_garbage + 3ULL + (u64)ar[(u64)w + 2ULL];
    }
    i = i + 1u;
  }
  u32 *ext = (u32 *)h->extend_stk;
  u64 p = h->extend_len;
  ext[p] = (blk_lit & PW_LIT_MASK) | EXT_BLK_FLAG;
  h->extend_len = p + 1ULL;
  return true;
}

u64 full_bve_var_m7(FullHdr *h, u32 v) {
  u64 scap = h->scratch_cap;
  if (scap < 2048ULL) { return 1ULL; }
  bool use_m8 = (scap >= FID_K6_MIN_SCR);
  u32 occ_lim = use_m8 ? M8_OCC_LIM : 512u;
  u32 neg_off = use_m8 ? M8_NEG_OFF : 512u;
  u32 pos_mask = use_m8 ? M8_POS_MASK : 1024u;
  u32 neg_mask = use_m8 ? M8_NEG_MASK : 1040u;
  u32 gf_idx = use_m8 ? M8_GF_IDX : 1056u;
  u32 rg_idx = use_m8 ? M8_RG_IDX : 1057u;
  u64 r_off = use_m8 ? (u64)M8_RES_OFF : 1088ULL;
  u32 *scr = (u32 *)h->scratch_buf;
  i8 *vals = (i8 *)h->values;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *wvec = (u32 *)h->watch_vec;
  u64 cv2 = h->cur_vars << 1;
  u64 acap = h->arena_cap;
  u64 wcap = h->wcap;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 np = full_bve_collect_m7(h, pl, scr, occ_lim);
  u32 nn = full_bve_collect_m7(h, nl, scr + neg_off, occ_lim);
  if (np == 0xFFFFFFFFu || nn == 0xFFFFFFFFu) { return 1ULL; }
  if (np > 0u && nn > 0u && (u64)np + (u64)nn > 2000ULL) { return 1ULL; }
  u64 ext_p = (np > 0u) ? full_bve_ext_need(h, 0u, np) : 0ULL;
  u64 ext_n = (nn > 0u) ? full_bve_ext_need(h, neg_off, nn) : 0ULL;
  bool push_pos = (ext_p <= ext_n);
  u64 ext_need = 0ULL;
  if (np == 0u || nn == 0u) {
    ext_need = (np > 0u || nn > 0u) ? 1ULL : 0ULL;
  } else {
    ext_need = (push_pos ? ext_p : ext_n) + 1ULL;
  }
  bool ext_ok = (h->extend_len <= h->extend_cap && ext_need <= h->extend_cap - h->extend_len);
  if (ext_ok && (np == 0u || nn == 0u)) {
    if ((np > 0u && !full_bve_weaken_unit_fid(h, pl, 0u, np)) ||
        (nn > 0u && !full_bve_weaken_unit_fid(h, nl, neg_off, nn))) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    return 1ULL;
  }
  u64 rp = r_off;
  u64 r_cnt = 0ULL;
  u64 w_est = 0ULL;
  u64 lim_cls = (u64)np + (u64)nn + h->elim_bound;
  bool fit = ext_ok;
  if (fit) {
    if (use_m8) { full_bve_gates_fid(h, v, np, nn); }
    else { full_bve_gates_m7(h, v, np, nn); }
    if (h->inconsistent != 0ULL) { return 20ULL; }
    if (vals[pl] != (i8)0) { return 1ULL; }
    bool gf = (scr[gf_idx] != 0u);
    bool rg = (scr[rg_idx] != 0u);
    u64 res_sz = h->res_sz;
    u32 i = 0u;
    while (i < np && fit) {
      bool pi = ((scr[pos_mask + (i >> 5)] >> (i & 31u)) & 1u) != 0u;
      u32 j = 0u;
      while (j < nn && fit) {
        bool nj = ((scr[neg_mask + (j >> 5)] >> (j & 31u)) & 1u) != 0u;
        bool need_pair = !gf || (rg ? (pi || nj) : (pi != nj));
        if (need_pair) {
          res_sz = res_sz + 1ULL;
          if (full_bve_resolve_pair(h, v, scr[i], scr[neg_off + j])) {
            u64 rlen = h->tmp_len;
            if (rlen == 0ULL) {
              h->res_sz = res_sz;
              h->inconsistent = 1ULL;
              return 20ULL;
            }
            if (rlen == 1ULL) {
              u32 ul = tmp[0];
              if ((u64)ul < cv2) {
                i8 uv = vals[ul];
                if (uv < (i8)0) {
                  h->res_sz = res_sz;
                  h->inconsistent = 1ULL;
                  return 20ULL;
                }
                if (uv == (i8)0) { full_assign_lvl(h, ul, 0xFFFFFFFFu, 0u); }
              }
              j = j + 1u;
              continue;
            }
            r_cnt = r_cnt + 1ULL;
            if (rlen > 100ULL || r_cnt > lim_cls || rp + 1ULL + rlen > scap) {
              fit = false;
              break;
            }
            scr[rp] = (u32)rlen;
            u32 k = 0u;
            while ((u64)k < rlen) {
              u32 lk = tmp[k];
              scr[rp + 1ULL + (u64)k] = lk;
              if (rlen >= 2ULL && (u64)lk < cv2) {
                w_est = w_est + (((u64)wvec[((u64)lk << 1) + 1ULL]) << 1) + 4ULL;
              }
              k = k + 1u;
            }
            rp = rp + 1ULL + rlen;
          }
        }
        j = j + 1u;
      }
      i = i + 1u;
    }
    h->res_sz = res_sz;
  }
  if (fit) {
    u64 ar_need = (rp - r_off) + (r_cnt * 2ULL) + 16ULL;
    u64 w_need = w_est + (r_cnt * 4ULL) + 16ULL;
    if (ar_need > acap - h->arena_len) {
      fit = false;
    } else if (w_need > wcap - h->wlen) {
      if (h->wusable > 0ULL) { full_wstack_defrag(h); }
      if (w_need > wcap - h->wlen) { fit = false; }
    }
  }
  if (fit) {
    bool wok = false;
    if (push_pos) {
      wok = full_bve_weaken(h, pl, 0u, np) &&
            full_bve_weaken_unit_fid(h, nl, neg_off, nn);
    } else {
      wok = full_bve_weaken(h, nl, neg_off, nn) &&
            full_bve_weaken_unit_fid(h, pl, 0u, np);
    }
    if (!wok) {
      h->oom = 1ULL;
      return 2ULL;
    }
    full_set_inactive(h, v, FL_ELIM);
    h->bve_cnt = h->bve_cnt + 1ULL;
    u64 cr = full_bve_commit_res(h, r_off, rp);
    if (cr == 20ULL) { return 20ULL; }
    if (cr == 1ULL && !full_dense_flush_units_m7(h)) { return 20ULL; }
    return cr;
  }
  return 1ULL;
}

u64 full_bve_var_key_m7(FullHdr *h, u32 v) {
  if ((u64)v >= h->cur_vars) { return 0ULL; }
  u32 *wvec = (u32 *)h->watch_vec;
  u64 pos = full_dense_occ_cnt_fid(h, v << 1, 2000ULL);
  u64 neg = full_dense_occ_cnt_fid(h, (v << 1) | 1u, 2000ULL);
  if (pos > 2000ULL) { pos = 2000ULL; }
  if (neg > 2000ULL) { neg = 2000ULL; }
  u64 base = (4004000ULL + pos + neg) - (pos * neg);
  u64 rel = 0ULL;
  if (h->stable != 0ULL) {
    u64 *sc = (u64 *)h->score;
    rel = f64u_to_u64(sc[v]);
    if (rel > (1ULL << 61)) { rel = 1ULL << 61; }
  } else {
    u32 *qs = (u32 *)h->q_stamp;
    rel = (u64)qs[v];
  }
  if (rel > (1ULL << 61)) { rel = 1ULL << 61; }
  return ((1ULL << 62) + base) - rel;
}

void full_bve_heap_up_m7(FullHdr *h, u64 hlen, u32 v) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if ((u64)v >= cv || hlen > cv) { return; }
  u32 *hp = (u32 *)h->work_stk1;
  u64 *keys = (u64 *)h->sim_sig;
  u64 p = (u64)hp[mv + (u64)v];
  if (p >= hlen) { return; }
  u64 kv = keys[v];
  while (p > 0ULL) {
    u64 par = (p - 1ULL) >> 1;
    u32 pv = hp[par];
    if ((u64)pv >= cv || keys[pv] >= kv) { break; }
    hp[p] = pv;
    hp[mv + (u64)pv] = (u32)p;
    p = par;
  }
  hp[p] = v;
  hp[mv + (u64)v] = (u32)p;
}

void full_bve_heap_down_m7(FullHdr *h, u64 hlen, u32 v) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if ((u64)v >= cv || hlen > cv) { return; }
  u32 *hp = (u32 *)h->work_stk1;
  u64 *keys = (u64 *)h->sim_sig;
  u64 p = (u64)hp[mv + (u64)v];
  if (p >= hlen) { return; }
  u64 kv = keys[v];
  while (true) {
    u64 l = (p << 1) + 1ULL;
    if (l >= hlen) { break; }
    u32 bv = hp[l];
    if ((u64)bv >= cv) { break; }
    u64 bk = keys[bv];
    u64 best = l;
    u64 r = l + 1ULL;
    if (r < hlen) {
      u32 rv = hp[r];
      if ((u64)rv < cv && keys[rv] > bk) {
        best = r;
        bv = rv;
        bk = keys[rv];
      }
    }
    if (kv >= bk) { break; }
    hp[p] = bv;
    hp[mv + (u64)bv] = (u32)p;
    p = best;
  }
  hp[p] = v;
  hp[mv + (u64)v] = (u32)p;
}

u64 full_bve_heap_push_m7(FullHdr *h, u64 hlen, u32 v) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if ((u64)v >= cv || hlen > cv) { return hlen; }
  u32 *hp = (u32 *)h->work_stk1;
  u64 *keys = (u64 *)h->sim_sig;
  u64 nk = full_bve_var_key_m7(h, v);
  u64 old_k = keys[v];
  keys[v] = nk;
  u64 cur_p = (u64)hp[mv + (u64)v];
  if (cur_p < hlen) {
    if (nk > old_k) { full_bve_heap_up_m7(h, hlen, v); }
    else if (nk < old_k) { full_bve_heap_down_m7(h, hlen, v); }
    return hlen;
  }
  if (hlen >= cv) { return hlen; }
  hp[hlen] = v;
  hp[mv + (u64)v] = (u32)hlen;
  u64 nlen = hlen + 1ULL;
  full_bve_heap_up_m7(h, nlen, v);
  return nlen;
}

u32 full_bve_heap_pop_m7(FullHdr *h, u64 hlen) {
  u64 cv = h->cur_vars;
  u64 mv = h->max_vars;
  if (hlen == 0ULL || hlen > cv) { return 0xFFFFFFFFu; }
  u32 *hp = (u32 *)h->work_stk1;
  u32 top = hp[0];
  if ((u64)top < cv) { hp[mv + (u64)top] = 0xFFFFFFFFu; }
  u64 nlen = hlen - 1ULL;
  if (nlen > 0ULL) {
    u32 last = hp[nlen];
    hp[0] = last;
    if ((u64)last < cv) {
      hp[mv + (u64)last] = 0u;
      full_bve_heap_down_m7(h, nlen, last);
    }
  }
  return ((u64)top < cv) ? top : 0xFFFFFFFFu;
}

u64 full_bve_collect_nbrs_m7(FullHdr *h, u32 v) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *mclr = (u32 *)h->min_clr;
  u32 *nbrs = (u32 *)h->work_stk2;
  u64 nn = 0ULL;
  u32 side = 0u;
  while (side < 2u) {
    u32 lit = (v << 1) | side;
    if ((u64)lit < (cv << 1)) {
      u64 off = (u64)wvec[(u64)lit << 1];
      u64 end = off + (u64)wvec[((u64)lit << 1) + 1ULL];
      u64 p = off;
      while (p < end) {
        u32 w0 = wstk[p];
        p = p + 1ULL;
        if ((w0 & PW_BIN_FLAG) != 0u) {
          u32 u = (w0 & PW_LIT_MASK) >> 1;
          if (u != v && (u64)u < cv && (fl[u] & FL_ACTIVE) != 0u &&
              vals[(u64)u << 1] == (i8)0 && mclr[u] == 0u && nn < cv) {
            mclr[u] = 1u;
            nbrs[nn] = u;
            nn = nn + 1ULL;
          }
          continue;
        }
        if (p >= end) { break; }
        u32 cr = wstk[p];
        p = p + 1ULL;
        if ((ar[cr] & (PH_GARB | PH_RED)) != 0u) { continue; }
        u32 sz = ar[(u64)cr + 2ULL];
        u32 k = 0u;
        while (k < sz) {
          u32 u = ar[(u64)cr + 3ULL + (u64)k] >> 1;
          if (u != v && (u64)u < cv && (fl[u] & FL_ACTIVE) != 0u &&
              vals[(u64)u << 1] == (i8)0 && mclr[u] == 0u && nn < cv) {
            mclr[u] = 1u;
            nbrs[nn] = u;
            nn = nn + 1ULL;
          }
          k = k + 1u;
        }
      }
    }
    side = side + 1u;
  }
  u64 c = 0ULL;
  while (c < nn) { mclr[nbrs[c]] = 0u; c = c + 1ULL; }
  return nn;
}

u64 full_elim_bve_m7(FullHdr *h, u64 res_lim) {
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u32 *hp = (u32 *)h->work_stk1;
  u32 *nbrs = (u32 *)h->work_stk2;
  u64 mv = h->max_vars;
  u32 *mclr = (u32 *)h->min_clr;
  u64 cv0 = h->cur_vars;
  u64 ci = 0ULL;
  while (ci < cv0) { mclr[ci] = 0u; ci = ci + 1ULL; }
  h->res_sz = 0ULL;
  bool hit_lim = false;
  u64 hlen = 0ULL;
  bool last_round_elim = false;
  u64 round = 0ULL;
  while (round < 2ULL && !hit_lim && h->res_sz <= res_lim && h->fuel > 0ULL &&
         h->oom == 0ULL && h->inconsistent == 0ULL) {
    if (!full_dense_flush_units_m7(h)) { return 20ULL; }
    u64 cv = h->cur_vars;
    u64 i = 0ULL;
    while (i < cv) { hp[mv + i] = 0xFFFFFFFFu; i = i + 1ULL; }
    hlen = 0ULL;
    i = 0ULL;
    while (i < cv) {
      if ((fl[i] & (FL_ACTIVE | FL_ELIM_C)) == (FL_ACTIVE | FL_ELIM_C) &&
          vals[i << 1] == (i8)0) {
        hlen = full_bve_heap_push_m7(h, hlen, (u32)i);
      }
      i = i + 1ULL;
    }
    if (hlen == 0ULL) { last_round_elim = false; break; }
    bool round_elim = false;
    while (hlen > 0ULL && h->fuel > 0ULL && h->oom == 0ULL && h->inconsistent == 0ULL) {
      if (h->res_sz > res_lim) { hit_lim = true; break; }
      u32 v = full_bve_heap_pop_m7(h, hlen);
      hlen = hlen - 1ULL;
      u64 cv1 = h->cur_vars;
      if (v == 0xFFFFFFFFu || (u64)v >= cv1) { continue; }
      if ((fl[v] & (FL_ACTIVE | FL_ELIM_C)) != (FL_ACTIVE | FL_ELIM_C) ||
          vals[(u64)v << 1] != (i8)0) { continue; }
      fl[v] = fl[v] & (~FL_ELIM_C);
      h->fuel = h->fuel - 1ULL;
      u64 nn = full_bve_collect_nbrs_m7(h, v);
      u64 b0 = h->bve_cnt;
      u64 st = full_bve_var_m7(h, v);
      if (st == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
      if (st == 2ULL) { break; }
      if (!full_dense_flush_units_m7(h)) { return 20ULL; }
      if (h->bve_cnt > b0) {
        round_elim = true;
        u64 cv2 = h->cur_vars;
        u64 k = 0ULL;
        while (k < nn) {
          u32 u = nbrs[k];
          if ((u64)u < cv2 && (fl[u] & FL_ACTIVE) != 0u && vals[(u64)u << 1] == (i8)0) {
            fl[u] = fl[u] | FL_ELIM_C;
            hlen = full_bve_heap_push_m7(h, hlen, u);
          }
          k = k + 1ULL;
        }
      }
    }
    last_round_elim = round_elim;
    if (!round_elim) { break; }
    round = round + 1ULL;
  }
  if (h->inconsistent == 0ULL) {
    u64 cvf = h->cur_vars;
    bool complete = (!hit_lim && h->res_sz <= res_lim && hlen == 0ULL &&
        !last_round_elim && h->oom == 0ULL && h->fuel > 0ULL);
    if (complete) {
      u64 cur_b = h->elim_bound;
      if (cur_b < 16ULL) {
        u64 next_b = (cur_b == 0ULL) ? 1ULL : (cur_b << 1);
        if (next_b > 16ULL) { next_b = 16ULL; }
        h->elim_bound = next_b;
        u64 k = 0ULL;
        while (k < cvf) { fl[k] = fl[k] | FL_ELIM_C; k = k + 1ULL; }
      }
    } else {
      u64 k = 0ULL;
      while (k < cvf) { fl[k] = fl[k] & (~FL_ELIM_C); k = k + 1ULL; }
    }
  }
  return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
}

bool full_has_elim_cands_fid(FullHdr *h) {
  u64 cv = h->cur_vars;
  u32 *fl = (u32 *)h->flags;
  i8 *vals = (i8 *)h->values;
  u64 v = 0ULL;
  while (v < cv) {
    if ((fl[v] & 1u) != 0u && vals[v << 1] == (i8)0 && (fl[v] & (8u | 16u)) != 0u) {
      return true;
    }
    v = v + 1ULL;
  }
  return false;
}

u64 full_eliminate_m6(FullHdr *h, bool initial) {
  u64 saved_st = h->search_ticks;
  u64 dticks = full_elim_dticks(h, initial);
  if (!initial) {
    h->eliminations = h->eliminations + 1ULL;
    u64 nloge = f64u_to_u64(
      f64u_mul(0x407F400000000000ULL, f64u_nlogpown(h->eliminations, 2ULL)));
    u64 delta = full_scale_delta(h, nloge);
    h->elim_limit = h->conflicts + delta;
  }
  if (!initial && !full_has_elim_cands_fid(h)) {
    h->fwd_str_cnt = h->search_ticks;
    return 1ULL;
  }
  if (!full_enter_dense_ex_fid(h, false)) {
    h->fwd_str_cnt = h->search_ticks;
    return (h->inconsistent != 0ULL) ? 20ULL : 1ULL;
  }
  u64 saved_pt = h->fwd_sub_cnt;
  u64 fbase = (dticks >= 10000000ULL) ? dticks : 10000000ULL;
  u64 fbud = fbase / 10ULL;
  u64 fs = full_forward_sub_m7(h, fbud);
  h->fwd_sub_cnt = saved_pt;
  if (fs == 20ULL) {
    full_rebuild_watches(h);
    return 20ULL;
  }
  u32 *tmk = (u32 *)h->tarjan_mark;
  u64 cv = h->cur_vars;
  u64 ti = 0ULL;
  while (ti < cv) { tmk[ti] = 0u; ti = ti + 1ULL; }
  u64 base_t = (dticks >= 10000000ULL) ? dticks : 10000000ULL;
  u64 res_lim = base_t / 10ULL;
  u64 res = full_elim_bve_m7(h, res_lim);
  u64 rr = full_rebuild_watches(h);
  h->search_ticks = saved_st;
  full_update_classify_fid(h);
  h->fwd_str_cnt = h->search_ticks;
  if (res == 20ULL || rr == 20ULL || h->inconsistent != 0ULL) { return 20ULL; }
  return 1ULL;
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Eliminate
