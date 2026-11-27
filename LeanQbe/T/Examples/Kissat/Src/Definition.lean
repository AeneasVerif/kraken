/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Semantic Gate Definition Extraction via Kitten (`Src/Definition.lean`)

Mirrors upstream `kissat/src/definition.c` (`26` live functions, DAG level `L2`):
- `full_k6_watch_m7` (R4: `kissat_def_kitten_watch_fallback`)
- `full_k6_assign_m7` (R4: `kissat_def_kitten_assign_fallback`)
- `full_k6_mtf_m7` (R4: `kissat_def_kitten_mtf_fallback`)
- `full_k6_backtrack_m7` (R4: `kissat_def_kitten_backtrack_fallback`)
- `full_k6_prop_m7` (R4: `kissat_def_kitten_propagate_fallback`)
- `full_k6_ana_cl_m7` (R4: `kissat_def_kitten_analyze_clause_fallback`)
- `full_k6_analyze_m7` (R4: `kissat_def_kitten_analyze_fallback`)
- `full_k6_solve_m7` (R4: `kissat_def_kitten_solve_fallback`)
- `full_k6_core_m7` (R4: `kissat_def_kitten_core_fallback`)
- `full_bve_def_k6_m7` (R4: `kissat_find_definition_fallback`)
- `full_bve_gates_m7` (R4: `kissat_find_gates_fallback`)
- `full_bve_k6_mv_fid` (R4: `kissat_def_kitten_max_vars`)
- `full_fid_k6_add_ticks` (R4: `kissat_def_kitten_add_ticks`)
- `full_k6_watch_fid` (R4: `kissat_def_kitten_watch`)
- `full_k6_assign_fid` (R4: `kissat_def_kitten_assign`)
- `full_k6_mtf_fid` (R4: `kissat_def_kitten_mtf`)
- `full_k6_backtrack_fid` (R4: `kissat_def_kitten_backtrack`)
- `full_k6_prop_fid` (R4: `kissat_def_kitten_propagate`)
- `full_k6_ana_cl_fid` (R4: `kissat_def_kitten_analyze_clause`)
- `full_k6_analyze_fid` (R4: `kissat_def_kitten_analyze`)
- `full_k6_solve_fid` (R4: `kissat_def_kitten_solve`)
- `full_k6_core_fid` (R4: `kissat_def_kitten_core`)
- `full_k6_extract_and_solve_fid` (R4: `kissat_def_kitten_extract_and_solve`)
- `full_bve_certify_unit_fid` (R4: `kissat_def_certify_unit`)
- `full_bve_def_k6_fid` (R4: `kissat_find_definition`)
- `full_bve_gates_fid` (R4: `kissat_find_gates`)-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Definition

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! definition "
#include \"kissat_internal.h\"

#define KM_CORE_M7            0x20000000u
#define KM_CORE_FID           0x80000000u
#define KM_CORE               0x80000000u

extern bool full_bve_find_equiv_m7(FullHdr *h, u32 np, u32 nn);
extern bool full_bve_find_and_m7(FullHdr *h, u32 lit, u32 lit_n, u32 opp_n);
extern bool full_bve_find_ite_m7(FullHdr *h, u32 v, u32 np, u32 nn);
extern bool full_bve_find_xor_m7(FullHdr *h, u32 v, u32 np, u32 nn);
extern u64 full_m6_max_v(u64 cap);
extern void full_assign_lvl(FullHdr *h, u32 lit, u32 rsn, u32 alvl);
extern void full_k6_init(FullHdr *h, u32 nv);
extern bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz);
extern u64 full_k6_solve(FullHdr *h, u64 tick_lim);
extern bool full_bve_find_equiv_m8(FullHdr *h, u32 np, u32 nn);
extern bool full_bve_find_and_m8(FullHdr *h, u32 lit, u32 lit_n, u32 opp_n);
extern bool full_bve_find_ite_m8(FullHdr *h, u32 v, u32 np, u32 nn);

void full_k6_watch_m7(u32 *k, u32 cid, u32 l0, u32 l1, u32 sz) {
  if (cid >= K6_MC || l0 >= 128u || l1 >= 128u) { return; }
  u32 bf = (sz == 2u) ? K6_BIN_FLAG : 0u;
  u32 w0 = cid << 1;
  u32 w1 = w0 | 1u;
  k[KO_WBLIT + w0] = l1 | bf;
  k[KO_WNEXT + w0] = k[KO_WHEAD + l0];
  k[KO_WHEAD + l0] = w0;
  k[KO_WBLIT + w1] = l0 | bf;
  k[KO_WNEXT + w1] = k[KO_WHEAD + l1];
  k[KO_WHEAD + l1] = w1;
}

void full_k6_assign_m7(u32 *k, u32 lit, u32 rsn_cid) {
  u32 te = k[KH_TRL_END];
  if (lit >= 128u || te >= K6_MV) { return; }
  u32 v = lit >> 1;
  k[KO_VALS + lit] = 1u;
  k[KO_VALS + (lit ^ 1u)] = 2u;
  k[KO_LVL + v] = k[KH_LVL];
  k[KO_RSN + v] = rsn_cid;
  k[KO_TRL + te] = lit;
  k[KH_TRL_END] = te + 1u;
  if (k[KH_UNASS] > 0u) { k[KH_UNASS] = k[KH_UNASS] - 1u; }
  u32 fl = k[KO_FLAGS + v];
  k[KO_FLAGS + v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

void full_k6_mtf_m7(u32 *k, u32 v) {
  u32 nv = k[KH_NV];
  if (nv > K6_MV || v >= nv || v == k[KH_QLAST]) { return; }
  u32 pv = k[KO_QPREV + v];
  u32 nxt = k[KO_QNEXT + v];
  if (k[KO_VALS + (v << 1)] != 0u && v == k[KH_QSEARCH]) {
    if (pv < nv) { k[KH_QSEARCH] = pv; }
    else if (nxt < nv) { k[KH_QSEARCH] = nxt; }
  }
  if (pv >= nv) { k[KH_QFIRST] = nxt; } else { k[KO_QNEXT + pv] = nxt; }
  if (nxt >= nv) { k[KH_QLAST] = pv; } else { k[KO_QPREV + nxt] = pv; }
  u32 ol = k[KH_QLAST];
  k[KO_QPREV + v] = ol;
  k[KO_QNEXT + v] = 0xFFFFFFFFu;
  k[KH_QLAST] = v;
  if (ol >= nv) { k[KH_QFIRST] = v; } else { k[KO_QNEXT + ol] = v; }
  if (k[KH_QSTAMP] < 0xFFFFFFF0u) {
    k[KH_QSTAMP] = k[KH_QSTAMP] + 1u;
    k[KO_QST + v] = k[KH_QSTAMP];
  }
  if (k[KO_VALS + (v << 1)] == 0u) { k[KH_QSEARCH] = v; }
}

void full_k6_backtrack_m7(u32 *k, u32 target_lvl) {
  u32 nv = k[KH_NV];
  if (nv > K6_MV) { return; }
  u32 te = k[KH_TRL_END];
  if (te > K6_MV) { te = K6_MV; }
  u32 best_st = 0u;
  if (k[KH_QSEARCH] < nv) { best_st = k[KO_QST + k[KH_QSEARCH]]; }
  while (te > 0u) {
    u32 lit = k[KO_TRL + te - 1u];
    if (lit >= (nv << 1)) { break; }
    u32 v = lit >> 1;
    if (k[KO_LVL + v] <= target_lvl) { break; }
    te = te - 1u;
    k[KO_VALS + lit] = 0u;
    k[KO_VALS + (lit ^ 1u)] = 0u;
    k[KO_LVL + v] = 0u;
    k[KO_RSN + v] = 0xFFFFFFFFu;
    k[KH_UNASS] = k[KH_UNASS] + 1u;
    if (k[KO_QST + v] > best_st) { best_st = k[KO_QST + v]; k[KH_QSEARCH] = v; }
  }
  k[KH_TRL_END] = te;
  if (k[KH_PROP] > te) { k[KH_PROP] = te; }
  k[KH_LVL] = target_lvl;
}

u32 full_k6_prop_m7(u32 *k) {
  u64 ticks = 0ULL;
  u32 nc = k[KH_NC];
  u32 nv = k[KH_NV];
  u32 acap = k[KH_ACAP];
  if (nc > K6_MC || nv > K6_MV) { return 0xFFFFFFFFu; }
  while (k[KH_PROP] < k[KH_TRL_END] && k[KH_PROP] < K6_MV) {
    u32 lit = k[KO_TRL + k[KH_PROP]];
    k[KH_PROP] = k[KH_PROP] + 1u;
    if (lit >= (nv << 1)) { continue; }
    u32 nl = lit ^ 1u;
    u64 visits = 0ULL;
    u32 prev = 0xFFFFFFFFu;
    u32 w = k[KO_WHEAD + nl];
    u32 wsteps = 0u;
    while (w < (nc << 1) && wsteps < 512u) {
      wsteps = wsteps + 1u;
      u32 nxt = k[KO_WNEXT + w];
      visits = visits + 1ULL;
      u32 wb = k[KO_WBLIT + w];
      u32 bv = wb & K6_LIT_MASK;
      if (bv >= (nv << 1)) { prev = w; w = nxt; continue; }
      u32 bvv = k[KO_VALS + bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          k[KH_TICKS] = k[KH_TICKS] + (u32)(ticks + (visits >> 7) + 1ULL);
          return cid;
        }
        if (bvv == 0u) { full_k6_assign_m7(k, bv, cid); }
        prev = w;
        w = nxt;
        continue;
      }
      u32 slot = w & 1u;
      u32 off = k[KO_CL_OFF + cid];
      u32 sz = k[KO_CL_META + cid] & 0xFFFFu;
      if (sz < 2u || off + sz > acap) { prev = w; w = nxt; continue; }
      u32 other = k[KO_ARENA + off + (slot ^ 1u)];
      if (other >= (nv << 1)) { prev = w; w = nxt; continue; }
      if (k[KO_VALS + other] == 1u) {
        k[KO_WBLIT + w] = other;
        prev = w;
        w = nxt;
        continue;
      }
      ticks = ticks + 1ULL;
      u32 r = 2u;
      u32 ri = 0xFFFFFFFFu;
      u32 repl = 0u;
      while (r < sz) {
        u32 cand = k[KO_ARENA + off + r];
        if (cand < (nv << 1) && k[KO_VALS + cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        k[KO_ARENA + off + slot] = repl;
        k[KO_ARENA + off + ri] = nl;
        if (prev >= (nc << 1)) { k[KO_WHEAD + nl] = nxt; }
        else { k[KO_WNEXT + prev] = nxt; }
        k[KO_WBLIT + w] = other;
        k[KO_WNEXT + w] = k[KO_WHEAD + repl];
        k[KO_WHEAD + repl] = w;
        w = nxt;
        continue;
      }
      k[KO_WBLIT + w] = other;
      prev = w;
      w = nxt;
      u32 ov = k[KO_VALS + other];
      if (ov == 2u) {
        k[KH_TICKS] = k[KH_TICKS] + (u32)(ticks + (visits >> 7) + 1ULL);
        return cid;
      }
      if (ov == 0u) { full_k6_assign_m7(k, other, cid); }
    }
    ticks = ticks + (visits >> 7) + 1ULL;
  }
  k[KH_TICKS] = k[KH_TICKS] + (u32)ticks;
  return 0xFFFFFFFFu;
}

void full_k6_ana_cl_m7(u32 *k, u32 cid, u32 skip_v) {
  u32 nc = k[KH_NC];
  u32 nv = k[KH_NV];
  u32 acap = k[KH_ACAP];
  if (cid >= nc || nc > K6_MC || nv > K6_MV) { return; }
  u32 clvl = k[KH_LVL];
  u32 off = k[KO_CL_OFF + cid];
  u32 sz = k[KO_CL_META + cid] & 0xFFFFu;
  if (off + sz > acap) { return; }
  if (k[KH_NRES] < 128u) { k[KO_RES + k[KH_NRES]] = cid; k[KH_NRES] = k[KH_NRES] + 1u; }
  else { k[KH_NRES] = 129u; }
  u32 i = 0u;
  while (i < sz) {
    u32 l = k[KO_ARENA + off + i];
    u32 v = l >> 1;
    if (v < nv && v != skip_v && (k[KO_FLAGS + v] & 2u) == 0u) {
      k[KO_FLAGS + v] = k[KO_FLAGS + v] | 2u;
      if (k[KH_NANA] < K6_MV) { k[KO_ANA + k[KH_NANA]] = v; k[KH_NANA] = k[KH_NANA] + 1u; }
      u32 vlvl = k[KO_LVL + v];
      if (vlvl == 0u) {
        u32 r0 = k[KO_RSN + v];
        if (r0 != 0xFFFFFFFFu) {
          if (k[KH_NRES] < 128u) { k[KO_RES + k[KH_NRES]] = r0; k[KH_NRES] = k[KH_NRES] + 1u; }
          else { k[KH_NRES] = 129u; }
        }
      } else if (vlvl == clvl) {
        k[KH_OPEN] = k[KH_OPEN] + 1u;
      } else if (k[KH_NKL] < K6_MV) {
        k[KO_KL + k[KH_NKL]] = l;
        k[KH_NKL] = k[KH_NKL] + 1u;
      }
    }
    i = i + 1u;
  }
}

bool full_k6_analyze_m7(u32 *k, u32 confl_cid) {
  u32 nv = k[KH_NV];
  if (nv > K6_MV) { return false; }
  k[KH_NKL] = 1u;
  k[KH_NANA] = 0u;
  k[KH_NRES] = 0u;
  k[KH_OPEN] = 0u;
  full_k6_ana_cl_m7(k, confl_cid, 0xFFFFFFFFu);
  u32 clvl = k[KH_LVL];
  u32 idx = k[KH_TRL_END];
  if (idx > K6_MV) { idx = K6_MV; }
  u32 uip = 0xFFFFFFFFu;
  while (k[KH_OPEN] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = k[KO_TRL + idx];
    u32 pv = p >> 1;
    if (pv < nv && (k[KO_FLAGS + pv] & 2u) != 0u && k[KO_LVL + pv] == clvl) {
      k[KH_OPEN] = k[KH_OPEN] - 1u;
      if (k[KH_OPEN] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = k[KO_RSN + pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_k6_ana_cl_m7(k, rsn, pv);
    }
  }
  u32 nana = k[KH_NANA];
  if (nana > K6_MV) { nana = K6_MV; }
  u32 ai = 0u;
  while (ai < nana) {
    u32 av = k[KO_ANA + ai];
    if (av < nv) { k[KO_FLAGS + av] = k[KO_FLAGS + av] & (~2u); }
    ai = ai + 1u;
  }
  u32 nres = k[KH_NRES];
  u32 nkl = k[KH_NKL];
  if (uip == 0xFFFFFFFFu || uip >= (nv << 1) || nres > 128u || nkl == 0u || nkl > K6_MV) {
    return false;
  }
  k[KO_KL] = uip;
  u32 jlvl = 0u;
  u32 wi = 1u;
  u32 i = 1u;
  while (i < nkl) {
    u32 kv = k[KO_KL + i] >> 1;
    if (kv < nv) {
      u32 il = k[KO_LVL + kv];
      if (il > jlvl) { jlvl = il; wi = i; }
    }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) {
    u32 t = k[KO_KL + 1u];
    k[KO_KL + 1u] = k[KO_KL + wi];
    k[KO_KL + wi] = t;
  }
  full_k6_backtrack_m7(k, jlvl);
  ai = 0u;
  while (ai < nana) { full_k6_mtf_m7(k, k[KO_ANA + ai]); ai = ai + 1u; }
  u32 nc = k[KH_NC];
  u32 off = k[KH_ALEN];
  if (nc >= K6_MC || off + nkl + nres > k[KH_ACAP]) { return false; }
  i = 0u;
  while (i < nkl) { k[KO_ARENA + off + i] = k[KO_KL + i]; i = i + 1u; }
  i = 0u;
  while (i < nres) { k[KO_ARENA + off + nkl + i] = k[KO_RES + i]; i = i + 1u; }
  k[KH_ALEN] = off + nkl + nres;
  k[KO_CL_OFF + nc] = off;
  k[KO_CL_META + nc] = nkl | KM_LRN;
  k[KO_CL_AUX + nc] = nres;
  k[KH_NC] = nc + 1u;
  if (nkl == 1u) { full_k6_assign_m7(k, uip, nc); return true; }
  full_k6_watch_m7(k, nc, k[KO_KL], k[KO_KL + 1u], nkl);
  full_k6_assign_m7(k, uip, nc);
  return true;
}

u64 full_k6_solve_m7(FullHdr *h, u32 *k, u32 tick_lim) {
  full_k6_backtrack_m7(k, 0u);
  if (k[KH_INCONS] != 0xFFFFFFFFu) { return 20ULL; }
  k[KH_TICK_LIM] = tick_lim;
  k[KH_TICKS] = 0u;
  u32 nv = k[KH_NV];
  u32 nc = k[KH_NC];
  u32 acap = k[KH_ACAP];
  u32 nunits = k[KH_NUNITS];
  if (nv > K6_MV || nc > K6_MC || nunits > K6_MAX_ORIG) { return 0ULL; }
  u32 ui = 0u;
  while (ui < nunits) {
    u32 ucid = k[KO_UNITS + ui];
    if (ucid < nc) {
      u32 off = k[KO_CL_OFF + ucid];
      if (off < acap) {
        u32 ul = k[KO_ARENA + off];
        if (ul < (nv << 1)) {
          u32 uv = k[KO_VALS + ul];
          if (uv == 2u) { k[KH_INCONS] = ucid; return 20ULL; }
          if (uv == 0u) { full_k6_assign_m7(k, ul, ucid); }
        }
      }
    }
    ui = ui + 1u;
  }
  u32 confl = full_k6_prop_m7(k);
  if (confl != 0xFFFFFFFFu) { k[KH_INCONS] = confl; return 20ULL; }
  while (k[KH_TICKS] < k[KH_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (k[KH_LVL] == 0u) { k[KH_INCONS] = confl; return 20ULL; }
      if (!full_k6_analyze_m7(k, confl)) { return 0ULL; }
      confl = full_k6_prop_m7(k);
      continue;
    }
    if (k[KH_UNASS] == 0u) { return 10ULL; }
    u32 cur = k[KH_QSEARCH];
    u32 pick = 0xFFFFFFFFu;
    u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
      cur = k[KO_QPREV + cur];
      steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = k[KH_QLAST];
      steps = 0u;
      while (cur < nv && steps < nv) {
        if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = k[KO_QPREV + cur];
        steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) {
        if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = cur + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) { return 10ULL; }
    k[KH_QSEARCH] = pick;
    u32 ph = (k[KO_FLAGS + pick] ^ k[KH_PHASE]) & 1u;
    k[KH_LVL] = k[KH_LVL] + 1u;
    full_k6_assign_m7(k, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_k6_prop_m7(k);
  }
  return 0ULL;
}

void full_k6_core_m7(u32 *k) {
  u32 nc = k[KH_NC];
  u32 nv = k[KH_NV];
  u32 acap = k[KH_ACAP];
  if (nc > K6_MC || nv > K6_MV) { return; }
  u32 i = 0u;
  while (i < nc) { k[KO_CL_META + i] = k[KO_CL_META + i] & (~KM_CORE); i = i + 1u; }
  u32 inc = k[KH_INCONS];
  if (inc < nc) {
    i = 0u;
    while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
    k[KO_CL_META + inc] = k[KO_CL_META + inc] | KM_CORE;
    u32 off = k[KO_CL_OFF + inc];
    u32 sz = k[KO_CL_META + inc] & 0xFFFFu;
    if (off + sz <= acap) {
      u32 j = 0u;
      while (j < sz) {
        u32 lv = k[KO_ARENA + off + j] >> 1;
        if (lv < nv) { k[KO_FLAGS + lv] = k[KO_FLAGS + lv] | 2u; }
        j = j + 1u;
      }
    }
    u32 ti = k[KH_TRL_END];
    if (ti > K6_MV) { ti = K6_MV; }
    while (ti > 0u) {
      ti = ti - 1u;
      u32 v = k[KO_TRL + ti] >> 1;
      if (v >= nv || (k[KO_FLAGS + v] & 2u) == 0u) { continue; }
      k[KO_FLAGS + v] = k[KO_FLAGS + v] & (~2u);
      u32 rsn = k[KO_RSN + v];
      if (rsn >= nc) { continue; }
      k[KO_CL_META + rsn] = k[KO_CL_META + rsn] | KM_CORE;
      u32 roff = k[KO_CL_OFF + rsn];
      u32 rsz = k[KO_CL_META + rsn] & 0xFFFFu;
      if (roff + rsz <= acap) {
        u32 j = 0u;
        while (j < rsz) {
          u32 lv = k[KO_ARENA + roff + j] >> 1;
          if (lv < nv && lv != v) { k[KO_FLAGS + lv] = k[KO_FLAGS + lv] | 2u; }
          j = j + 1u;
        }
      }
    }
    i = 0u;
    while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
  }
  u32 pass = 0u;
  bool changed = true;
  while (changed && pass < nc) {
    changed = false;
    pass = pass + 1u;
    u32 cid = nc;
    while (cid > 0u) {
      cid = cid - 1u;
      u32 meta = k[KO_CL_META + cid];
      if ((meta & KM_CORE) != 0u) {
        u32 off = k[KO_CL_OFF + cid];
        u32 sz = meta & 0xFFFFu;
        if ((meta & KM_LRN) != 0u) {
          u32 na = k[KO_CL_AUX + cid];
          if (off + sz + na <= acap) {
            u32 j = 0u;
            while (j < na) {
              u32 ant = k[KO_ARENA + off + sz + j];
              if (ant < nc && (k[KO_CL_META + ant] & KM_CORE) == 0u) {
                k[KO_CL_META + ant] = k[KO_CL_META + ant] | KM_CORE;
                changed = true;
              }
              j = j + 1u;
            }
          }
        }
        if (off + sz <= acap) {
          u32 j = 0u;
          while (j < sz) {
            u32 lv = k[KO_ARENA + off + j] >> 1;
            if (lv < nv && k[KO_LVL + lv] == 0u) {
              u32 r0 = k[KO_RSN + lv];
              if (r0 < nc && (k[KO_CL_META + r0] & KM_CORE) == 0u) {
                k[KO_CL_META + r0] = k[KO_CL_META + r0] | KM_CORE;
                changed = true;
              }
            }
            j = j + 1u;
          }
        }
      }
    }
  }
}

void full_bve_def_k6_m7(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (h->scratch_cap < 8192ULL || np == 0u || nn == 0u || np + nn < 3u ||
      np + nn > K6_MAX_ORIG) {
    return;
  }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *exp = (u32 *)h->wsort;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 *k = scr + K6_BASE;
  u32 acap = (u32)(h->scratch_cap - (u64)(K6_BASE + KO_ARENA));
  u32 max_csz = (h->max_vars < 100ULL) ? (u32)h->max_vars : 100u;
  u32 nv = 0u;
  u32 nc = 0u;
  u32 alen = 0u;
  u32 nunits = 0u;
  u32 trivial_eid = 0xFFFFFFFFu;
  bool abort_def = false;
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  u32 side = 0u;
  while (side < 2u && !abort_def && trivial_eid == 0xFFFFFFFFu) {
    u32 cnt = (side == 0u) ? np : nn;
    u32 off_s = (side == 0u) ? 0u : 512u;
    u32 except = (side == 0u) ? pl : nl;
    u32 idx = 0u;
    while (idx < cnt && !abort_def) {
      u32 w = scr[off_s + idx];
      u32 eid = (side << 10) | idx;
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        i8 lv_val = vals[l];
        if (lv_val < (i8)0) { trivial_eid = eid; break; }
        if (lv_val == (i8)0) {
          u32 lv = l >> 1;
          if (tmk[lv] == 0u) {
            if (nv >= K6_MV || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
            exp[nv] = lv;
            nv = nv + 1u;
            tmk[lv] = nv;
          }
          if (nc >= K6_MAX_ORIG || alen + 1u > acap) { abort_def = true; break; }
          k[KO_ARENA + alen] = ((tmk[lv] - 1u) << 1) | (l & 1u);
          k[KO_CL_OFF + nc] = alen;
          k[KO_CL_META + nc] = 1u;
          k[KO_CL_AUX + nc] = eid;
          k[KO_UNITS + nunits] = nc;
          nunits = nunits + 1u;
          nc = nc + 1u;
          alen = alen + 1u;
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false;
        u32 csz = 0u;
        u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != except) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= K6_MV || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
                exp[nv] = lv;
                nv = nv + 1u;
                tmk[lv] = nv;
              }
              if (csz >= max_csz) { abort_def = true; break; }
              tmp[csz] = ((tmk[lv] - 1u) << 1) | (l & 1u);
              csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (abort_def) { break; }
        if (!sat) {
          if (csz == 0u) { trivial_eid = eid; break; }
          if (nc >= K6_MAX_ORIG || alen + csz > acap) { abort_def = true; break; }
          m = 0u;
          while (m < csz) { k[KO_ARENA + alen + m] = tmp[m]; m = m + 1u; }
          k[KO_CL_OFF + nc] = alen;
          k[KO_CL_META + nc] = csz;
          k[KO_CL_AUX + nc] = eid;
          if (csz == 1u) {
            k[KO_UNITS + nunits] = nc;
            nunits = nunits + 1u;
          }
          nc = nc + 1u;
          alen = alen + csz;
        }
      }
      idx = idx + 1u;
    }
    side = side + 1u;
  }
  u32 ci = 0u;
  while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (trivial_eid != 0xFFFFFFFFu) {
    u32 idx = trivial_eid & 0x3FFu;
    u32 mbase = ((trivial_eid >> 10) == 0u) ? 1024u : 1040u;
    scr[mbase + (idx >> 5)] = 1u << (idx & 31u);
    scr[1056] = 1u;
    scr[1057] = 1u;
    return;
  }
  if (abort_def || nv == 0u || nc < 2u) { return; }
  k[KH_NV] = nv;
  k[KH_NC] = nc;
  k[KH_ORIG_NC] = nc;
  k[KH_LVL] = 0u;
  k[KH_PROP] = 0u;
  k[KH_TRL_END] = 0u;
  k[KH_UNASS] = nv;
  k[KH_INCONS] = 0xFFFFFFFFu;
  k[KH_QFIRST] = 0u;
  k[KH_QLAST] = nv - 1u;
  k[KH_QSEARCH] = nv - 1u;
  k[KH_QSTAMP] = nv;
  k[KH_TICKS] = 0u;
  k[KH_TICK_LIM] = 512u;
  k[KH_ALEN] = alen;
  k[KH_ACAP] = acap;
  k[KH_NANA] = 0u;
  k[KH_NKL] = 0u;
  k[KH_NRES] = 0u;
  k[KH_NUNITS] = nunits;
  k[KH_OPEN] = 0u;
  k[KH_PHASE] = 0u;
  u32 i = 0u;
  while (i < nv) {
    k[KO_LVL + i] = 0u;
    k[KO_RSN + i] = 0xFFFFFFFFu;
    k[KO_FLAGS + i] = 0u;
    k[KO_QST + i] = i + 1u;
    k[KO_QPREV + i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    k[KO_QNEXT + i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  i = 0u;
  while (i < (nv << 1)) {
    k[KO_VALS + i] = 0u;
    k[KO_WHEAD + i] = 0xFFFFFFFFu;
    i = i + 1u;
  }
  i = 0u;
  while (i < nc) {
    u32 sz = k[KO_CL_META + i] & 0xFFFFu;
    if (sz >= 2u) {
      u32 off = k[KO_CL_OFF + i];
      full_k6_watch_m7(k, i, k[KO_ARENA + off], k[KO_ARENA + off + 1u], sz);
    }
    i = i + 1u;
  }
  if (full_k6_solve_m7(h, k, 512u) != 20ULL) { return; }
  full_k6_core_m7(k);
  bool any = false;
  u32 onc = k[KH_ORIG_NC];
  i = 0u;
  while (i < onc) {
    if ((k[KO_CL_META + i] & KM_CORE_M7) != 0u) {
      u32 eid = k[KO_CL_AUX + i];
      u32 idx = eid & 0x3FFu;
      u32 mbase = ((eid >> 10) == 0u) ? 1024u : 1040u;
      u32 widx = mbase + (idx >> 5);
      scr[widx] = scr[widx] | (1u << (idx & 31u));
      any = true;
    }
    i = i + 1u;
  }
  if (any) {
    scr[1056] = 1u;
    scr[1057] = 1u;
  }
}

void full_bve_gates_m7(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 k = 0u;
  while (k < 34u) { scr[1024u + k] = 0u; k = k + 1u; }
  if (np == 0u || nn == 0u) { return; }
  if (full_bve_find_equiv_m7(h, np, nn)) { return; }
  u32 pl = v << 1;
  u32 nl = pl | 1u;
  if (full_bve_find_and_m7(h, pl, np, nn)) { return; }
  if (full_bve_find_and_m7(h, nl, nn, np)) { return; }
  if (full_bve_find_ite_m7(h, v, np, nn)) { return; }
  if (full_bve_find_xor_m7(h, v, np, nn)) { return; }
  full_bve_def_k6_m7(h, v, np, nn);
}

u64 full_bve_k6_mv_fid(u64 cap) {
  if (cap < FID_K6_MIN_SCR) { return 0ULL; }
  if (cap >= 524288ULL) { return FID_K6_MAX_V; }
  u64 raw = ((cap - 4224ULL) / 64ULL) & 0xFFFFFFFFFFFFFFC0ULL;
  if (raw < 256ULL) { return 256ULL; }
  if (raw > FID_K6_MAX_V) { return FID_K6_MAX_V; }
  return raw;
}

void full_fid_k6_add_ticks(FullHdr *h, u64 delta) {
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cur = (u64)scr[FKH_TICKS];
  u64 rem = 0xFFFFFFFFULL - cur;
  scr[FKH_TICKS] = (delta >= rem) ? 0xFFFFFFFFu : (u32)(cur + delta);
}

void full_k6_watch_fid(FullHdr *h, u32 cid, u32 l0, u32 l1, u32 sz) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 mc = mv << 2;
  if (mv < 256u || mv > 8192u || cid >= mc || l0 >= (mv << 1) || l1 >= (mv << 1)) { return; }
  u32 o_whead = 4224u + 11u * mv;
  u32 o_wnext = 4224u + 13u * mv;
  u32 o_wblit = 4224u + 21u * mv;
  u32 bf = (sz == 2u) ? K6_BIN_FLAG : 0u;
  u32 w0 = cid << 1; u32 w1 = w0 | 1u;
  scr[o_wblit + w0] = l1 | bf;
  scr[o_wnext + w0] = scr[o_whead + l0]; scr[o_whead + l0] = w0;
  scr[o_wblit + w1] = l0 | bf;
  scr[o_wnext + w1] = scr[o_whead + l1]; scr[o_whead + l1] = w1;
}

void full_k6_assign_fid(FullHdr *h, u32 lit, u32 rsn_cid) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 te = scr[FKH_TRL_END];
  if (mv < 256u || mv > 8192u || lit >= (mv << 1) || te >= mv) { return; }
  u32 v = lit >> 1;
  u32 o_rsn = 4224u + mv;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_vals = 4224u + 9u * mv;
  scr[o_vals + lit] = 1u; scr[o_vals + (lit ^ 1u)] = 2u;
  scr[4224u + v] = scr[FKH_LVL]; scr[o_rsn + v] = rsn_cid;
  scr[o_trl + te] = lit; scr[FKH_TRL_END] = te + 1u;
  if (scr[FKH_UNASS] > 0u) { scr[FKH_UNASS] = scr[FKH_UNASS] - 1u; }
  u32 fl = scr[o_flags + v];
  scr[o_flags + v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

void full_k6_mtf_fid(FullHdr *h, u32 v) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nv = scr[FKH_NV];
  if (mv < 256u || mv > 8192u || v >= nv || nv > mv) { return; }
  u32 o_qprev = 4224u + 2u * mv;
  u32 o_qnext = 4224u + 3u * mv;
  u32 o_qst = 4224u + 4u * mv;
  u32 ql = scr[FKH_QLAST];
  if (v != ql) {
    u32 pv = scr[o_qprev + v]; u32 nx = scr[o_qnext + v];
    if (pv < nv) { scr[o_qnext + pv] = nx; } else { scr[FKH_QFIRST] = nx; }
    if (nx < nv) { scr[o_qprev + nx] = pv; } else { scr[FKH_QLAST] = pv; }
    u32 old_last = scr[FKH_QLAST];
    scr[o_qprev + v] = old_last; scr[o_qnext + v] = 0xFFFFFFFFu;
    if (old_last < nv) { scr[o_qnext + old_last] = v; } else { scr[FKH_QFIRST] = v; }
    scr[FKH_QLAST] = v;
  }
  u32 st = scr[FKH_QSTAMP] + 1u;
  scr[FKH_QSTAMP] = st; scr[o_qst + v] = st; scr[FKH_QSEARCH] = v;
}

void full_k6_backtrack_fid(FullHdr *h, u32 target_lvl) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nv = scr[FKH_NV];
  if (mv < 256u || mv > 8192u || nv > mv) { return; }
  u32 o_rsn = 4224u + mv;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_vals = 4224u + 9u * mv;
  u32 te = scr[FKH_TRL_END];
  if (te > mv) { te = mv; }
  while (te > 0u) {
    u32 lit = scr[o_trl + te - 1u]; u32 v = lit >> 1;
    if (v >= nv || scr[4224u + v] <= target_lvl) { break; }
    te = te - 1u;
    scr[o_vals + lit] = 0u; scr[o_vals + (lit ^ 1u)] = 0u;
    scr[4224u + v] = 0u; scr[o_rsn + v] = 0xFFFFFFFFu;
    scr[FKH_UNASS] = scr[FKH_UNASS] + 1u;
  }
  scr[FKH_TRL_END] = te; scr[FKH_LVL] = target_lvl;
  if (scr[FKH_PROP] > te) { scr[FKH_PROP] = te; }
}

u32 full_k6_prop_fid(FullHdr *h) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nv = scr[FKH_NV]; u32 nc = scr[FKH_NC]; u32 acap = scr[FKH_ACAP];
  if (mv < 256u || mv > 8192u || nv > mv || nc > (mv << 2)) { return 0xFFFFFFFFu; }
  u32 mc = mv << 2;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_vals = 4224u + 9u * mv;
  u32 o_whead = 4224u + 11u * mv;
  u32 o_wnext = 4224u + 13u * mv;
  u32 o_wblit = 4224u + 21u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u64 ticks = 0ULL;
  while (scr[FKH_PROP] < scr[FKH_TRL_END] && scr[FKH_PROP] < mv) {
    u32 lit = scr[o_trl + scr[FKH_PROP]]; scr[FKH_PROP] = scr[FKH_PROP] + 1u;
    if (lit >= (nv << 1)) { continue; }
    u32 nl = lit ^ 1u; u64 visits = 0ULL; u32 prev = 0xFFFFFFFFu;
    u32 w = scr[o_whead + nl]; u32 wsteps = 0u;
    while (w < (nc << 1) && wsteps < (mc << 1)) {
      wsteps = wsteps + 1u;
      u32 nxt = scr[o_wnext + w]; visits = visits + 1ULL;
      u32 wb = scr[o_wblit + w]; u32 bv = wb & K6_LIT_MASK;
      if (bv >= (nv << 1)) { prev = w; w = nxt; continue; }
      u32 bvv = scr[o_vals + bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          full_fid_k6_add_ticks(h, ticks + (visits >> 4) + 1ULL);
          return cid;
        }
        if (bvv == 0u) { full_k6_assign_fid(h, bv, cid); }
        prev = w; w = nxt; continue;
      }
      u32 slot = w & 1u; u32 off = scr[o_cl_off + cid];
      u32 sz = scr[o_cl_meta + cid] & 0xFFFFu;
      if (sz < 2u || off + sz > acap) { prev = w; w = nxt; continue; }
      u32 other = scr[o_arena + off + (slot ^ 1u)];
      if (other >= (nv << 1)) { prev = w; w = nxt; continue; }
      ticks = ticks + 1ULL;
      if (scr[o_vals + other] == 1u) {
        scr[o_wblit + w] = other; prev = w; w = nxt; continue;
      }
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = scr[o_arena + off + r];
        if (cand < (nv << 1) && scr[o_vals + cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        scr[o_arena + off + slot] = repl; scr[o_arena + off + ri] = nl;
        if (prev >= (nc << 1)) { scr[o_whead + nl] = nxt; }
        else { scr[o_wnext + prev] = nxt; }
        scr[o_wblit + w] = other;
        scr[o_wnext + w] = scr[o_whead + repl];
        scr[o_whead + repl] = w;
        w = nxt; continue;
      }
      scr[o_wblit + w] = other; prev = w; w = nxt;
      u32 ov = scr[o_vals + other];
      if (ov == 2u) {
        full_fid_k6_add_ticks(h, ticks + (visits >> 4) + 1ULL);
        return cid;
      }
      if (ov == 0u) { full_k6_assign_fid(h, other, cid); }
    }
    ticks = ticks + (visits >> 4) + 1ULL;
  }
  full_fid_k6_add_ticks(h, ticks);
  return 0xFFFFFFFFu;
}

void full_k6_ana_cl_fid(FullHdr *h, u32 cid, u32 skip_v) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nc = scr[FKH_NC]; u32 nv = scr[FKH_NV]; u32 acap = scr[FKH_ACAP];
  if (mv < 256u || mv > 8192u || cid >= nc || nc > (mv << 2) || nv > mv) { return; }
  u32 max_orig = mv << 1;
  u32 o_rsn = 4224u + mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_ana = 4224u + 7u * mv;
  u32 o_kl = 4224u + 8u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_res = 4224u + 43u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u32 clvl = scr[FKH_LVL]; u32 off = scr[o_cl_off + cid];
  u32 sz = scr[o_cl_meta + cid] & 0xFFFFu;
  if (off + sz > acap) { return; }
  if (scr[FKH_NRES] < max_orig) {
    scr[o_res + scr[FKH_NRES]] = cid; scr[FKH_NRES] = scr[FKH_NRES] + 1u;
  } else { scr[FKH_NRES] = max_orig + 1u; }
  u32 i = 0u;
  while (i < sz) {
    u32 l = scr[o_arena + off + i]; u32 v = l >> 1;
    if (v < nv && v != skip_v && (scr[o_flags + v] & 2u) == 0u) {
      scr[o_flags + v] = scr[o_flags + v] | 2u;
      if (scr[FKH_NANA] < mv) {
        scr[o_ana + scr[FKH_NANA]] = v; scr[FKH_NANA] = scr[FKH_NANA] + 1u;
      }
      u32 vlvl = scr[4224u + v];
      if (vlvl == 0u) {
        u32 r0 = scr[o_rsn + v];
        if (r0 != 0xFFFFFFFFu) {
          if (scr[FKH_NRES] < max_orig) {
            scr[o_res + scr[FKH_NRES]] = r0; scr[FKH_NRES] = scr[FKH_NRES] + 1u;
          } else { scr[FKH_NRES] = max_orig + 1u; }
        }
      } else if (vlvl == clvl) {
        scr[FKH_OPEN] = scr[FKH_OPEN] + 1u;
      } else if (scr[FKH_NKL] < mv) {
        scr[o_kl + scr[FKH_NKL]] = l; scr[FKH_NKL] = scr[FKH_NKL] + 1u;
      }
    }
    i = i + 1u;
  }
}

bool full_k6_analyze_fid(FullHdr *h, u32 confl_cid) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nv = scr[FKH_NV];
  if (mv < 256u || mv > 8192u || nv > mv) { return false; }
  u32 mc = mv << 2; u32 max_orig = mv << 1;
  u32 o_rsn = 4224u + mv;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_ana = 4224u + 7u * mv;
  u32 o_kl = 4224u + 8u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_cl_aux = 4224u + 37u * mv;
  u32 o_res = 4224u + 43u * mv;
  u32 o_arena = 4224u + 45u * mv;
  scr[FKH_NKL] = 1u; scr[FKH_NANA] = 0u; scr[FKH_NRES] = 0u; scr[FKH_OPEN] = 0u;
  full_k6_ana_cl_fid(h, confl_cid, 0xFFFFFFFFu);
  u32 clvl = scr[FKH_LVL]; u32 idx = scr[FKH_TRL_END];
  if (idx > mv) { idx = mv; }
  u32 uip = 0xFFFFFFFFu;
  while (scr[FKH_OPEN] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = scr[o_trl + idx]; u32 pv = p >> 1;
    if (pv < nv && (scr[o_flags + pv] & 2u) != 0u && scr[4224u + pv] == clvl) {
      scr[FKH_OPEN] = scr[FKH_OPEN] - 1u;
      if (scr[FKH_OPEN] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = scr[o_rsn + pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_k6_ana_cl_fid(h, rsn, pv);
    }
  }
  u32 nana = scr[FKH_NANA]; if (nana > mv) { nana = mv; }
  u32 ai = 0u;
  while (ai < nana) {
    u32 av = scr[o_ana + ai];
    if (av < nv) { scr[o_flags + av] = scr[o_flags + av] & (~2u); }
    ai = ai + 1u;
  }
  u32 nres = scr[FKH_NRES]; u32 nkl = scr[FKH_NKL];
  if (uip == 0xFFFFFFFFu || uip >= (nv << 1) ||
      nres > max_orig || nkl == 0u || nkl > mv) {
    return false;
  }
  scr[o_kl] = uip;
  u32 jlvl = 0u; u32 wi = 1u; u32 i = 1u;
  while (i < nkl) {
    u32 kv = scr[o_kl + i] >> 1;
    if (kv < nv) { u32 il = scr[4224u + kv]; if (il > jlvl) { jlvl = il; wi = i; } }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) {
    u32 t = scr[o_kl + 1u]; scr[o_kl + 1u] = scr[o_kl + wi]; scr[o_kl + wi] = t;
  }
  full_k6_backtrack_fid(h, jlvl);
  ai = 0u; while (ai < nana) { full_k6_mtf_fid(h, scr[o_ana + ai]); ai = ai + 1u; }
  u32 nc = scr[FKH_NC]; u32 off = scr[FKH_ALEN];
  if (nc >= mc || off + nkl + nres > scr[FKH_ACAP]) { return false; }
  i = 0u; while (i < nkl) { scr[o_arena + off + i] = scr[o_kl + i]; i = i + 1u; }
  i = 0u; while (i < nres) { scr[o_arena + off + nkl + i] = scr[o_res + i]; i = i + 1u; }
  scr[FKH_ALEN] = off + nkl + nres;
  scr[o_cl_off + nc] = off;
  scr[o_cl_meta + nc] = nkl | KM_LRN; scr[o_cl_aux + nc] = nres;
  scr[FKH_NC] = nc + 1u;
  if (nkl == 1u) { full_k6_assign_fid(h, uip, nc); return true; }
  full_k6_watch_fid(h, nc, scr[o_kl], scr[o_kl + 1u], nkl);
  full_k6_assign_fid(h, uip, nc);
  return true;
}

u64 full_k6_solve_fid(FullHdr *h, u32 tick_lim) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  if (mv < 256u || mv > 8192u) { return 0ULL; }
  full_k6_backtrack_fid(h, 0u);
  if (scr[FKH_INCONS] != 0xFFFFFFFFu) { return 20ULL; }
  scr[FKH_TICK_LIM] = tick_lim; scr[FKH_TICKS] = 0u;
  u32 nv = scr[FKH_NV]; u32 nc = scr[FKH_NC];
  u32 acap = scr[FKH_ACAP]; u32 nunits = scr[FKH_NUNITS];
  u32 mc = mv << 2; u32 max_orig = mv << 1;
  if (nv > mv || nc > mc || nunits > max_orig) { return 0ULL; }
  u32 o_qprev = 4224u + 2u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_vals = 4224u + 9u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_units = 4224u + 41u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u32 ui = 0u;
  while (ui < nunits) {
    u32 ucid = scr[o_units + ui];
    if (ucid < nc) {
      u32 off = scr[o_cl_off + ucid];
      if (off < acap) {
        u32 ul = scr[o_arena + off];
        if (ul < (nv << 1)) {
          u32 uv = scr[o_vals + ul];
          if (uv == 2u) { scr[FKH_INCONS] = ucid; return 20ULL; }
          if (uv == 0u) { full_k6_assign_fid(h, ul, ucid); }
        }
      }
    }
    ui = ui + 1u;
  }
  u32 confl = full_k6_prop_fid(h);
  if (confl != 0xFFFFFFFFu) { scr[FKH_INCONS] = confl; return 20ULL; }
  while (scr[FKH_TICKS] < scr[FKH_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (scr[FKH_LVL] == 0u) { scr[FKH_INCONS] = confl; return 20ULL; }
      if (!full_k6_analyze_fid(h, confl)) { return 0ULL; }
      confl = full_k6_prop_fid(h);
      continue;
    }
    if (scr[FKH_UNASS] == 0u) { return 10ULL; }
    u32 cur = scr[FKH_QSEARCH]; u32 pick = 0xFFFFFFFFu; u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (scr[o_vals + (cur << 1)] == 0u) { pick = cur; break; }
      cur = scr[o_qprev + cur]; steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = scr[FKH_QLAST]; steps = 0u;
      while (cur < nv && steps < nv) {
        if (scr[o_vals + (cur << 1)] == 0u) { pick = cur; break; }
        cur = scr[o_qprev + cur]; steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) {
        if (scr[o_vals + (cur << 1)] == 0u) { pick = cur; break; }
        cur = cur + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) { return 10ULL; }
    scr[FKH_QSEARCH] = pick;
    u32 ph = (scr[o_flags + pick] ^ scr[FKH_PHASE]) & 1u;
    scr[FKH_LVL] = scr[FKH_LVL] + 1u;
    full_k6_assign_fid(h, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_k6_prop_fid(h);
  }
  return 0ULL;
}

void full_k6_core_fid(FullHdr *h) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 mv = scr[FKH_MAX_V];
  u32 nc = scr[FKH_NC]; u32 nv = scr[FKH_NV]; u32 acap = scr[FKH_ACAP];
  if (mv < 256u || mv > 8192u || nc > (mv << 2) || nv > mv) { return; }
  u32 o_rsn = 4224u + mv;
  u32 o_trl = 4224u + 5u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_cl_aux = 4224u + 37u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u32 i = 0u;
  while (i < nc) { scr[o_cl_meta + i] = scr[o_cl_meta + i] & (~KM_CORE); i = i + 1u; }
  u32 inc = scr[FKH_INCONS];
  if (inc < nc) {
    i = 0u; while (i < nv) { scr[o_flags + i] = scr[o_flags + i] & (~2u); i = i + 1u; }
    scr[o_cl_meta + inc] = scr[o_cl_meta + inc] | KM_CORE;
    u32 off = scr[o_cl_off + inc]; u32 sz = scr[o_cl_meta + inc] & 0xFFFFu;
    if (off + sz <= acap) {
      u32 j = 0u;
      while (j < sz) {
        u32 lv = scr[o_arena + off + j] >> 1;
        if (lv < nv) { scr[o_flags + lv] = scr[o_flags + lv] | 2u; }
        j = j + 1u;
      }
    }
    u32 ti = scr[FKH_TRL_END]; if (ti > mv) { ti = mv; }
    while (ti > 0u) {
      ti = ti - 1u;
      u32 v = scr[o_trl + ti] >> 1;
      if (v >= nv || (scr[o_flags + v] & 2u) == 0u) { continue; }
      scr[o_flags + v] = scr[o_flags + v] & (~2u);
      u32 rsn = scr[o_rsn + v];
      if (rsn >= nc) { continue; }
      scr[o_cl_meta + rsn] = scr[o_cl_meta + rsn] | KM_CORE;
      u32 roff = scr[o_cl_off + rsn]; u32 rsz = scr[o_cl_meta + rsn] & 0xFFFFu;
      if (roff + rsz <= acap) {
        u32 j = 0u;
        while (j < rsz) {
          u32 lv = scr[o_arena + roff + j] >> 1;
          if (lv < nv && lv != v) { scr[o_flags + lv] = scr[o_flags + lv] | 2u; }
          j = j + 1u;
        }
      }
    }
    i = 0u; while (i < nv) { scr[o_flags + i] = scr[o_flags + i] & (~2u); i = i + 1u; }
  }
  u32 pass = 0u; bool changed = true;
  while (changed && pass < nc) {
    changed = false; pass = pass + 1u;
    u32 cid = nc;
    while (cid > 0u) {
      cid = cid - 1u;
      u32 meta = scr[o_cl_meta + cid];
      if ((meta & KM_CORE) != 0u) {
        u32 off = scr[o_cl_off + cid]; u32 sz = meta & 0xFFFFu;
        if ((meta & KM_LRN) != 0u) {
          u32 na = scr[o_cl_aux + cid];
          if (off + sz + na <= acap) {
            u32 j = 0u;
            while (j < na) {
              u32 ant = scr[o_arena + off + sz + j];
              if (ant < nc && (scr[o_cl_meta + ant] & KM_CORE) == 0u) {
                scr[o_cl_meta + ant] = scr[o_cl_meta + ant] | KM_CORE; changed = true;
              }
              j = j + 1u;
            }
          }
        }
        if (off + sz <= acap) {
          u32 j = 0u;
          while (j < sz) {
            u32 lv = scr[o_arena + off + j] >> 1;
            if (lv < nv && scr[4224u + lv] == 0u) {
              u32 r0 = scr[o_rsn + lv];
              if (r0 < nc && (scr[o_cl_meta + r0] & KM_CORE) == 0u) {
                scr[o_cl_meta + r0] = scr[o_cl_meta + r0] | KM_CORE; changed = true;
              }
            }
            j = j + 1u;
          }
        }
      }
    }
  }
}

bool full_k6_extract_and_solve_fid(
    FullHdr *h, u32 v, u32 np, u32 nn, bool second_pass, u32 tick_lim) {
  u32 mv = (u32)full_bve_k6_mv_fid(h->scratch_cap);
  if (mv == 0u) { return false; }
  u32 mc = mv << 2; u32 max_orig = mv << 1;
  u32 o_rsn = 4224u + mv;
  u32 o_qprev = 4224u + 2u * mv;
  u32 o_qnext = 4224u + 3u * mv;
  u32 o_qst = 4224u + 4u * mv;
  u32 o_flags = 4224u + 6u * mv;
  u32 o_vals = 4224u + 9u * mv;
  u32 o_whead = 4224u + 11u * mv;
  u32 o_cl_off = 4224u + 29u * mv;
  u32 o_cl_meta = 4224u + 33u * mv;
  u32 o_cl_aux = 4224u + 37u * mv;
  u32 o_units = 4224u + 41u * mv;
  u32 o_arena = 4224u + 45u * mv;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *exp = (u32 *)h->wsort;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 acap = (u32)(h->scratch_cap - (u64)o_arena);
  u32 max_csz = (h->max_vars < 65535ULL) ? (u32)h->max_vars : 65535u;
  u32 nv = 0u; u32 nc = 0u; u32 alen = 0u; u32 nunits = 0u;
  u32 trivial_eid = 0xFFFFFFFFu; bool abort_def = false;
  u32 pl = v << 1; u32 nl = pl | 1u;
  u32 s_step = 0u;
  while (s_step < 2u && !abort_def && trivial_eid == 0xFFFFFFFFu) {
    u32 side = second_pass ? (1u - s_step) : s_step;
    u32 cnt = (side == 0u) ? np : nn;
    u32 off_s = (side == 0u) ? 0u : M8_NEG_OFF;
    u32 mb = (side == 0u) ? M8_POS_MASK : M8_NEG_MASK;
    u32 except = (side == 0u) ? pl : nl;
    u32 step = 0u;
    while (step < cnt && !abort_def) {
      u32 idx = second_pass ? (cnt - 1u - step) : step;
      step = step + 1u;
      if (second_pass && ((scr[mb + (idx >> 5)] >> (idx & 31u)) & 1u) == 0u) { continue; }
      u32 w = scr[off_s + idx];
      u32 eid = (side << 11) | idx;
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        i8 lv_val = vals[l];
        if (lv_val < (i8)0) { trivial_eid = eid; break; }
        if (lv_val == (i8)0) {
          u32 lv = l >> 1;
          if (tmk[lv] == 0u) {
            if (nv >= mv || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
            exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
          }
          if (nc >= max_orig || alen + 1u > acap) { abort_def = true; break; }
          scr[o_arena + alen] = ((tmk[lv] - 1u) << 1) | (l & 1u);
          scr[o_cl_off + nc] = alen; scr[o_cl_meta + nc] = 1u; scr[o_cl_aux + nc] = eid;
          scr[o_units + nunits] = nc; nunits = nunits + 1u; nc = nc + 1u; alen = alen + 1u;
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != except) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= mv || (u64)nv >= (h->cur_vars << 1)) { abort_def = true; break; }
                exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              if (csz >= max_csz) { abort_def = true; break; }
              tmp[csz] = ((tmk[lv] - 1u) << 1) | (l & 1u); csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (abort_def) { break; }
        if (!sat) {
          if (csz == 0u) { trivial_eid = eid; break; }
          if (nc >= max_orig || alen + csz > acap) { abort_def = true; break; }
          m = 0u; while (m < csz) { scr[o_arena + alen + m] = tmp[m]; m = m + 1u; }
          scr[o_cl_off + nc] = alen; scr[o_cl_meta + nc] = csz;
          scr[o_cl_aux + nc] = eid;
          if (csz == 1u) { scr[o_units + nunits] = nc; nunits = nunits + 1u; }
          nc = nc + 1u; alen = alen + csz;
        }
      }
    }
    s_step = s_step + 1u;
  }
  u32 ci = 0u;
  while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (trivial_eid != 0xFFFFFFFFu) {
    u32 idx = trivial_eid & 0x7FFu;
    u32 mbase = ((trivial_eid >> 11) == 0u) ? M8_POS_MASK : M8_NEG_MASK;
    u32 z = 0u; while (z < 128u) { scr[M8_POS_MASK + z] = 0u; z = z + 1u; }
    scr[mbase + (idx >> 5)] = 1u << (idx & 31u);
    scr[M8_GF_IDX] = 1u; scr[M8_RG_IDX] = 1u;
    return true;
  }
  if (abort_def || nv == 0u || nc < 2u) { return false; }
  scr[FKH_NV] = nv; scr[FKH_NC] = nc; scr[FKH_ORIG_NC] = nc;
  scr[FKH_LVL] = 0u; scr[FKH_PROP] = 0u; scr[FKH_TRL_END] = 0u; scr[FKH_UNASS] = nv;
  scr[FKH_INCONS] = 0xFFFFFFFFu;
  scr[FKH_QFIRST] = 0u; scr[FKH_QLAST] = nv - 1u;
  scr[FKH_QSEARCH] = nv - 1u; scr[FKH_QSTAMP] = nv;
  scr[FKH_TICKS] = 0u; scr[FKH_TICK_LIM] = tick_lim;
  scr[FKH_ALEN] = alen; scr[FKH_ACAP] = acap;
  scr[FKH_NANA] = 0u; scr[FKH_NKL] = 0u; scr[FKH_NRES] = 0u; scr[FKH_NUNITS] = nunits;
  scr[FKH_OPEN] = 0u; scr[FKH_PHASE] = 0u;
  scr[FKH_MAX_V] = mv; scr[FKH_MAX_CL] = mc; scr[FKH_MAX_ORIG] = max_orig;
  u32 i = 0u;
  while (i < nv) {
    scr[4224u + i] = 0u; scr[o_rsn + i] = 0xFFFFFFFFu; scr[o_flags + i] = 0u;
    scr[o_qst + i] = i + 1u;
    scr[o_qprev + i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    scr[o_qnext + i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  i = 0u;
  while (i < (nv << 1)) {
    scr[o_vals + i] = 0u; scr[o_whead + i] = 0xFFFFFFFFu; i = i + 1u;
  }
  i = 0u;
  while (i < nc) {
    u32 sz = scr[o_cl_meta + i] & 0xFFFFu;
    if (sz >= 2u) {
      u32 off = scr[o_cl_off + i];
      full_k6_watch_fid(h, i, scr[o_arena + off], scr[o_arena + off + 1u], sz);
    }
    i = i + 1u;
  }
  if (full_k6_solve_fid(h, tick_lim) != 20ULL) { return false; }
  full_k6_core_fid(h);
  u32 z = 0u; while (z < 128u) { scr[M8_POS_MASK + z] = 0u; z = z + 1u; }
  bool any = false; u32 onc = scr[FKH_ORIG_NC]; i = 0u;
  while (i < onc) {
    if ((scr[o_cl_meta + i] & KM_CORE_FID) != 0u) {
      u32 eid = scr[o_cl_aux + i];
      u32 idx = eid & 0x7FFu;
      u32 mbase = ((eid >> 11) == 0u) ? M8_POS_MASK : M8_NEG_MASK;
      u32 widx = mbase + (idx >> 5);
      scr[widx] = scr[widx] | (1u << (idx & 31u));
      any = true;
    }
    i = i + 1u;
  }
  if (any) { scr[M8_GF_IDX] = 1u; scr[M8_RG_IDX] = 1u; }
  return any;
}

bool full_bve_certify_unit_fid(
    FullHdr *h, u32 v, u32 unit, u32 side_off, u32 side_cnt, u32 side_mask) { (void)v;
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark;
  u32 *exp = (u32 *)h->wsort;
  u32 *tmp = (u32 *)h->tmp_lits;
  u32 mv_sw = (u32)full_m6_max_v(h->scratch_cap);
  u32 max_csz = (h->max_vars < 65535ULL) ? (u32)h->max_vars : 65535u;
  u32 nv = 0u;
  bool direct_entail = false;
  bool abort_c = false;
  u32 idx = 0u;
  while (idx < side_cnt && !direct_entail && !abort_c) {
    if (((scr[side_mask + (idx >> 5)] >> (idx & 31u)) & 1u) != 0u) {
      u32 w = scr[side_off + idx];
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        i8 lv_val = vals[l];
        if (lv_val < (i8)0) { direct_entail = true; break; }
        if (lv_val == (i8)0) {
          u32 lv = l >> 1;
          if (tmk[lv] == 0u) {
            if (nv >= mv_sw || (u64)nv >= h->cur_vars) { abort_c = true; break; }
            exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
          }
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != unit) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= mv_sw || (u64)nv >= h->cur_vars) { abort_c = true; break; }
                exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (abort_c) { break; }
        if (!sat) {
          if (csz == 0u) { direct_entail = true; break; }
          if (csz > max_csz) { abort_c = true; break; }
        }
      }
    }
    idx = idx + 1u;
  }
  if (direct_entail) {
    u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
    i8 uv = vals[unit];
    if (uv < (i8)0) { h->inconsistent = 1ULL; }
    else if (uv == (i8)0) { full_assign_lvl(h, unit, 0xFFFFFFFFu, 0u); }
    return true;
  }
  if (abort_c || nv == 0u || mv_sw == 0u || 1280u + (mv_sw << 1) < 4192u) {
    u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
    return false;
  }
  ((u32 *)h->glue_used)[33] = 0xFFFFFFFFu;
  full_k6_init(h, nv);
  bool ok = true;
  idx = 0u;
  while (idx < side_cnt && ok) {
    if (((scr[side_mask + (idx >> 5)] >> (idx & 31u)) & 1u) != 0u) {
      u32 w = scr[side_off + idx];
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK;
        if (vals[l] == (i8)0) {
          u32 loc = tmk[l >> 1];
          if (loc == 0u || loc > nv) { ok = false; break; }
          tmp[0] = ((loc - 1u) << 1) | (l & 1u);
          if (!full_k6_add_clause(h, tmp, 1u)) { ok = false; break; }
        }
      } else {
        u32 sz = ar[(u64)w + 2ULL];
        bool sat = false; u32 csz = 0u; u32 m = 0u;
        while (m < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)m];
          if (l != unit) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 loc = tmk[l >> 1];
              if (loc == 0u || loc > nv || csz >= max_csz) { ok = false; break; }
              tmp[csz] = ((loc - 1u) << 1) | (l & 1u); csz = csz + 1u;
            }
          }
          m = m + 1u;
        }
        if (!ok) { break; }
        if (!sat) {
          if (!full_k6_add_clause(h, tmp, csz)) { ok = false; break; }
        }
      }
    }
    idx = idx + 1u;
  }
  u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (!ok) { return false; }
  if (full_k6_solve(h, (u64)FID_K6_TICK_P1) != 20ULL) { return false; }
  i8 uv = vals[unit];
  if (uv < (i8)0) { h->inconsistent = 1ULL; }
  else if (uv == (i8)0) { full_assign_lvl(h, unit, 0xFFFFFFFFu, 0u); }
  return true;
}

void full_bve_def_k6_fid(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 mv = (u32)full_bve_k6_mv_fid(h->scratch_cap);
  if (mv == 0u || np == 0u || nn == 0u || np + nn > (mv << 1)) { return; }
  if (!full_k6_extract_and_solve_fid(h, v, np, nn, false, FID_K6_TICK_P1)) { return; }
  u32 *scr = (u32 *)h->scratch_buf;
  if (!full_k6_extract_and_solve_fid(h, v, np, nn, true, FID_K6_TICK_P2)) {
    scr[M8_GF_IDX] = 0u; scr[M8_RG_IDX] = 0u;
    return;
  }
  bool has_pos = false; bool has_neg = false; u32 mi = 0u;
  while (mi < 64u) {
    if (scr[M8_POS_MASK + mi] != 0u) { has_pos = true; }
    if (scr[M8_NEG_MASK + mi] != 0u) { has_neg = true; }
    mi = mi + 1u;
  }
  u32 pl = v << 1; u32 nl = pl | 1u;
  if (!has_pos && has_neg) {
    if (!full_bve_certify_unit_fid(h, v, nl, M8_NEG_OFF, nn, M8_NEG_MASK)) {
      scr[M8_GF_IDX] = 0u; scr[M8_RG_IDX] = 0u;
    }
  } else if (has_pos && !has_neg) {
    if (!full_bve_certify_unit_fid(h, v, pl, 0u, np, M8_POS_MASK)) {
      scr[M8_GF_IDX] = 0u; scr[M8_RG_IDX] = 0u;
    }
  }
}

void full_bve_gates_fid(FullHdr *h, u32 v, u32 np, u32 nn) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 k = 0u;
  while (k < 130u) { scr[M8_POS_MASK + k] = 0u; k = k + 1u; }
  if (np == 0u || nn == 0u) { return; }
  if (full_bve_find_equiv_m8(h, np, nn)) { return; }
  u32 pl = v << 1; u32 nl = pl | 1u;
  if (full_bve_find_and_m8(h, pl, np, nn)) { return; }
  if (full_bve_find_and_m8(h, nl, nn, np)) { return; }
  if (full_bve_find_ite_m8(h, v, np, nn)) { return; }
  full_bve_def_k6_fid(h, v, np, nn);
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Definition
