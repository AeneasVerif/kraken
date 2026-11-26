/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Embedded Kitten Sub-Solver (K6) (`Src/Kitten.lean`)

Mirrors upstream `kissat/src/kitten.c` (`14` live functions, DAG level `L0`):
- `full_m6_max_v` (R4: `kitten_max_vars`)
- `full_k6_add_ticks` (R4: `kitten_add_ticks`)
- `full_k6_init` (R4: `kitten_init`)
- `full_k6_watch` (R4: `kitten_watch_clause`)
- `full_k6_assign` (R4: `kitten_assign`)
- `full_k6_add_clause` (R4: `kitten_add_clause`)
- `full_k6_mtf` (R4: `kitten_move_to_front`)
- `full_k6_backtrack` (R4: `kitten_backtrack`)
- `full_k6_propagate` (R4: `kitten_propagate`)
- `full_k6_ana_clause` (R4: `kitten_analyze_clause`)
- `full_k6_analyze` (R4: `kitten_analyze`)
- `full_k6_solve` (R4: `kitten_solve`)
- `full_k6_flip` (R4: `kitten_flip_literal`)
- `full_k512_add_live_m6` (R4: `kitten_add_live_clause`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Kitten

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! kitten "
#include \"kissat_internal.h\"

u64 full_m6_max_v(u64 cap) {
  if (cap < K6_MIN_SCR) { return 0ULL; }
  if (cap >= 524288ULL) { return K6_MAX_V; }
  u64 raw = ((cap - 1312ULL) / 45ULL) & 0xFFFFFFFFFFFFFFC0ULL;
  if (raw < 512ULL) { return 512ULL; }
  if (raw > K6_MAX_V) { return K6_MAX_V; }
  return raw;
}

void full_k6_add_ticks(u32 *k, u64 delta) {
  u64 cur = (u64)k[K6H_TICKS];
  u64 rem = 0xFFFFFFFFULL - cur;
  k[K6H_TICKS] = (delta >= rem) ? 0xFFFFFFFFu : (u32)(cur + delta);
}

void full_k6_init(FullHdr *h, u32 nv) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u || nv > mv) { return; }
  u32 base = 1280u + (mv << 1);
  u32 *k = ((u32 *)h->scratch_buf) + base;
  u32 i = 0u;
  while (i < 32u) { k[i] = 0u; i = i + 1u; }
  k[K6H_NV] = nv; k[K6H_UNASS] = nv;
  k[K6H_TICK_LIM] = 16384u;
  k[K6H_MAX_V] = mv; k[K6H_MAX_ORIG] = mv * 3u; k[K6H_MAX_CL] = mv * 4u;
  k[K6H_ACAP] = (u32)(h->scratch_cap - (u64)(base + 32u + 38u * mv));
  if (nv == 0u) {
    k[K6H_QFIRST] = 0xFFFFFFFFu; k[K6H_QLAST] = 0xFFFFFFFFu; k[K6H_QSEARCH] = 0xFFFFFFFFu;
  } else {
    k[K6H_QFIRST] = 0u; k[K6H_QLAST] = nv - 1u; k[K6H_QSEARCH] = nv - 1u; k[K6H_QSTAMP] = nv;
  }
  u32 *lvl = k + 32u; u32 *rsn = k + (32u + mv);
  u32 *qprev = k + (32u + 2u * mv); u32 *qnext = k + (32u + 3u * mv);
  u32 *qst = k + (32u + 4u * mv); u32 *flags = k + (32u + 6u * mv);
  i = 0u;
  while (i < nv) {
    lvl[i] = 0u; rsn[i] = 0xFFFFFFFFu; flags[i] = 0u; qst[i] = i + 1u;
    qprev[i] = (i == 0u) ? 0xFFFFFFFFu : (i - 1u);
    qnext[i] = (i + 1u >= nv) ? 0xFFFFFFFFu : (i + 1u);
    i = i + 1u;
  }
  u32 *vals = k + (32u + 10u * mv); u32 *whead = k + (32u + 12u * mv);
  u32 nl = nv << 1; i = 0u;
  while (i < nl) { vals[i] = 0u; whead[i] = 0xFFFFFFFFu; i = i + 1u; }
}

void full_k6_watch(u32 *k, u32 cid, u32 l0, u32 l1) {
  u32 mv = k[K6H_MAX_V];
  u32 *whead = k + (32u + 12u * mv); u32 *wnext = k + (32u + 14u * mv);
  u32 *wblit = k + (32u + 22u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 bf = (cl_sz[cid] == 2u) ? K6_BIN_FLAG : 0u;
  u32 w0 = cid << 1; u32 w1 = w0 | 1u;
  wblit[w0] = l1 | bf; wnext[w0] = whead[l0]; whead[l0] = w0;
  wblit[w1] = l0 | bf; wnext[w1] = whead[l1]; whead[l1] = w1;
}

void full_k6_assign(u32 *k, u32 lit, u32 rsn_cid) {
  u32 mv = k[K6H_MAX_V]; u32 v = lit >> 1; u32 te = k[K6H_TRL_END];
  u32 *lvl = k + 32u; u32 *rsn = k + (32u + mv); u32 *trl = k + (32u + 5u * mv);
  u32 *flags = k + (32u + 6u * mv); u32 *vals = k + (32u + 10u * mv);
  vals[lit] = 1u; vals[lit ^ 1u] = 2u;
  lvl[v] = k[K6H_LVL]; rsn[v] = rsn_cid;
  trl[te] = lit; k[K6H_TRL_END] = te + 1u;
  if (k[K6H_UNASS] > 0u) { k[K6H_UNASS] = k[K6H_UNASS] - 1u; }
  u32 fl = flags[v];
  flags[v] = ((lit & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
}

bool full_k6_add_clause(FullHdr *h, u32 *lits, u32 sz) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return false; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  if (sz == 0u) { k[K6H_INCONS] = 1u; return true; }
  if (sz == 1u) {
    u32 *vals = k + (32u + 10u * mv);
    u32 ul = lits[0]; u32 uv = vals[ul];
    if (uv == 2u) { k[K6H_INCONS] = 1u; }
    else if (uv == 0u) { full_k6_assign(k, ul, 0xFFFFFFFFu); }
    return true;
  }
  u32 nc = k[K6H_NC]; u32 off = k[K6H_ALEN];
  if (nc >= k[K6H_MAX_CL] || off + sz > k[K6H_ACAP]) { return false; }
  u32 *cl_off = k + (32u + 30u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 *arena = k + (32u + 38u * mv);
  u32 i = 0u;
  while (i < sz) { arena[off + i] = lits[i]; i = i + 1u; }
  k[K6H_ALEN] = off + sz;
  cl_off[nc] = off; cl_sz[nc] = sz;
  k[K6H_NC] = nc + 1u;
  full_k6_add_ticks(k, 1ULL);
  full_k6_watch(k, nc, lits[0], lits[1]);
  return true;
}

void full_k6_mtf(u32 *k, u32 v) {
  u32 nv = k[K6H_NV];
  if (v >= nv || v == k[K6H_QLAST]) { return; }
  u32 mv = k[K6H_MAX_V];
  u32 *qprev = k + (32u + 2u * mv); u32 *qnext = k + (32u + 3u * mv);
  u32 *qst = k + (32u + 4u * mv); u32 *vals = k + (32u + 10u * mv);
  u32 pv = qprev[v]; u32 nxt = qnext[v];
  if (vals[v << 1] != 0u && v == k[K6H_QSEARCH]) {
    if (pv < nv) { k[K6H_QSEARCH] = pv; } else if (nxt < nv) { k[K6H_QSEARCH] = nxt; }
  }
  if (pv >= nv) { k[K6H_QFIRST] = nxt; } else { qnext[pv] = nxt; }
  if (nxt >= nv) { k[K6H_QLAST] = pv; } else { qprev[nxt] = pv; }
  u32 ol = k[K6H_QLAST];
  qprev[v] = ol; qnext[v] = 0xFFFFFFFFu; k[K6H_QLAST] = v;
  if (ol >= nv) { k[K6H_QFIRST] = v; } else { qnext[ol] = v; }
  if (k[K6H_QSTAMP] < 0xFFFFFFF0u) {
    k[K6H_QSTAMP] = k[K6H_QSTAMP] + 1u; qst[v] = k[K6H_QSTAMP];
  }
  if (vals[v << 1] == 0u) { k[K6H_QSEARCH] = v; }
}

void full_k6_backtrack(u32 *k, u32 target_lvl) {
  u32 mv = k[K6H_MAX_V];
  u32 *lvl = k + 32u; u32 *rsn = k + (32u + mv);
  u32 *qst = k + (32u + 4u * mv); u32 *trl = k + (32u + 5u * mv);
  u32 *vals = k + (32u + 10u * mv);
  u32 te = k[K6H_TRL_END]; u32 best_st = 0u;
  if (k[K6H_QSEARCH] < k[K6H_NV]) { best_st = qst[k[K6H_QSEARCH]]; }
  while (te > 0u) {
    u32 lit = trl[te - 1u]; u32 v = lit >> 1;
    if (lvl[v] <= target_lvl) { break; }
    te = te - 1u;
    vals[lit] = 0u; vals[lit ^ 1u] = 0u;
    lvl[v] = 0u; rsn[v] = 0xFFFFFFFFu;
    k[K6H_UNASS] = k[K6H_UNASS] + 1u;
    if (qst[v] > best_st) { best_st = qst[v]; k[K6H_QSEARCH] = v; }
  }
  k[K6H_TRL_END] = te;
  if (k[K6H_PROP] > te) { k[K6H_PROP] = te; }
  k[K6H_LVL] = target_lvl;
}

u32 full_k6_propagate(u32 *k) {
  u32 mv = k[K6H_MAX_V];
  u32 mv2 = mv << 1;
  u32 mv4 = mv << 2;
  u32 mv8 = mv << 3;
  u32 *lvl = k + 32u;
  u32 *rsn = lvl + mv;
  u32 *trl = rsn + mv4;
  u32 *flags = trl + mv;
  u32 *vals = flags + mv4;
  u32 *whead = vals + mv2;
  u32 *wnext = whead + mv2;
  u32 *wblit = wnext + mv8;
  u32 *cl_off = wblit + mv8;
  u32 *cl_sz = cl_off + mv4;
  u32 *arena = cl_sz + mv4;
  u32 prop = k[K6H_PROP];
  u32 te = k[K6H_TRL_END];
  u32 klvl = k[K6H_LVL];
  u32 unass = k[K6H_UNASS];
  u64 ticks = 0ULL;
  while (prop < te) {
    u32 lit = trl[prop];
    prop = prop + 1u;
    u32 nl = lit ^ 1u;
    u64 visits = 0ULL;
    u32 prev = 0xFFFFFFFFu;
    u32 w = whead[nl];
    while (w != 0xFFFFFFFFu) {
      u32 nxt = wnext[w];
      visits = visits + 1ULL;
      u32 wb = wblit[w];
      u32 bv = wb & K6_LIT_MASK;
      u32 bvv = vals[bv];
      if (bvv == 1u) { prev = w; w = nxt; continue; }
      u32 cid = w >> 1;
      if ((wb & K6_BIN_FLAG) != 0u) {
        if (bvv == 2u) {
          k[K6H_PROP] = prop;
          k[K6H_TRL_END] = te;
          k[K6H_UNASS] = unass;
          u64 cur_t = (u64)k[K6H_TICKS];
          u64 dt = ticks + (visits >> 4) + 1ULL;
          u64 rem = 0xFFFFFFFFULL - cur_t;
          k[K6H_TICKS] = (dt >= rem) ? 0xFFFFFFFFu : (u32)(cur_t + dt);
          return cid;
        }
        if (bvv == 0u) {
          u32 v = bv >> 1;
          vals[bv] = 1u; vals[bv ^ 1u] = 2u;
          lvl[v] = klvl; rsn[v] = cid;
          trl[te] = bv; te = te + 1u;
          if (unass > 0u) { unass = unass - 1u; }
          u32 fl = flags[v];
          flags[v] = ((bv & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
        }
        prev = w; w = nxt; continue;
      }
      u32 slot = w & 1u;
      u32 off = cl_off[cid];
      u32 sz = cl_sz[cid];
      u32 *cl = arena + off;
      u32 other = cl[slot ^ 1u];
      ticks = ticks + 1ULL;
      if (vals[other] == 1u) { wblit[w] = other; prev = w; w = nxt; continue; }
      u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
      while (r < sz) {
        u32 cand = cl[r];
        if (vals[cand] != 2u) { ri = r; repl = cand; break; }
        r = r + 1u;
      }
      if (ri != 0xFFFFFFFFu) {
        cl[slot] = repl; cl[ri] = nl;
        if (prev == 0xFFFFFFFFu) { whead[nl] = nxt; } else { wnext[prev] = nxt; }
        wblit[w] = other; wnext[w] = whead[repl]; whead[repl] = w;
        w = nxt; continue;
      }
      wblit[w] = other; prev = w; w = nxt;
      u32 ov = vals[other];
      if (ov == 2u) {
        k[K6H_PROP] = prop;
        k[K6H_TRL_END] = te;
        k[K6H_UNASS] = unass;
        u64 cur_t = (u64)k[K6H_TICKS];
        u64 dt = ticks + (visits >> 4) + 1ULL;
        u64 rem = 0xFFFFFFFFULL - cur_t;
        k[K6H_TICKS] = (dt >= rem) ? 0xFFFFFFFFu : (u32)(cur_t + dt);
        return cid;
      }
      if (ov == 0u) {
        u32 v = other >> 1;
        vals[other] = 1u; vals[other ^ 1u] = 2u;
        lvl[v] = klvl; rsn[v] = cid;
        trl[te] = other; te = te + 1u;
        if (unass > 0u) { unass = unass - 1u; }
        u32 fl = flags[v];
        flags[v] = ((other & 1u) != 0u) ? (fl | 1u) : (fl & (~1u));
      }
    }
    ticks = ticks + (visits >> 4) + 1ULL;
  }
  k[K6H_PROP] = prop;
  k[K6H_TRL_END] = te;
  k[K6H_UNASS] = unass;
  u64 cur_t = (u64)k[K6H_TICKS];
  u64 rem = 0xFFFFFFFFULL - cur_t;
  k[K6H_TICKS] = (ticks >= rem) ? 0xFFFFFFFFu : (u32)(cur_t + ticks);
  return 0xFFFFFFFFu;
}

void full_k6_ana_clause(u32 *k, u32 cid, u32 skip_v) {
  u32 mv = k[K6H_MAX_V];
  u32 *lvl = k + 32u; u32 *flags = k + (32u + 6u * mv);
  u32 *ana = k + (32u + 7u * mv); u32 *kl = k + (32u + 8u * mv);
  u32 *cl_off = k + (32u + 30u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 *arena = k + (32u + 38u * mv);
  u32 clvl = k[K6H_LVL]; u32 off = cl_off[cid]; u32 sz = cl_sz[cid];
  u32 i = 0u;
  while (i < sz) {
    u32 l = arena[off + i]; u32 v = l >> 1;
    if (v != skip_v) {
      u32 vlvl = lvl[v];
      if (vlvl > 0u && (flags[v] & 2u) == 0u) {
        flags[v] = flags[v] | 2u;
        if (k[K6H_NANA] < mv) { ana[k[K6H_NANA]] = v; k[K6H_NANA] = k[K6H_NANA] + 1u; }
        if (vlvl == clvl) { k[K6H_OPEN] = k[K6H_OPEN] + 1u; }
        else if (k[K6H_NKL] < mv) { kl[k[K6H_NKL]] = l; k[K6H_NKL] = k[K6H_NKL] + 1u; }
      }
    }
    i = i + 1u;
  }
}

bool full_k6_analyze(u32 *k, u32 confl_cid) {
  u32 mv = k[K6H_MAX_V];
  u32 *lvl = k + 32u; u32 *rsn_arr = k + (32u + mv); u32 *trl = k + (32u + 5u * mv);
  u32 *flags = k + (32u + 6u * mv); u32 *ana = k + (32u + 7u * mv);
  u32 *kl = k + (32u + 8u * mv); u32 *cl_off = k + (32u + 30u * mv);
  u32 *cl_sz = k + (32u + 34u * mv); u32 *arena = k + (32u + 38u * mv);
  k[K6H_NKL] = 1u; k[K6H_NANA] = 0u; k[K6H_OPEN] = 0u;
  full_k6_ana_clause(k, confl_cid, 0xFFFFFFFFu);
  u32 clvl = k[K6H_LVL]; u32 idx = k[K6H_TRL_END]; u32 uip = 0xFFFFFFFFu;
  while (k[K6H_OPEN] > 0u) {
    if (idx == 0u) { break; }
    idx = idx - 1u;
    u32 p = trl[idx]; u32 pv = p >> 1;
    if ((flags[pv] & 2u) != 0u && lvl[pv] == clvl) {
      k[K6H_OPEN] = k[K6H_OPEN] - 1u;
      if (k[K6H_OPEN] == 0u) { uip = p ^ 1u; break; }
      u32 rsn = rsn_arr[pv];
      if (rsn == 0xFFFFFFFFu) { uip = p ^ 1u; break; }
      full_k6_ana_clause(k, rsn, pv);
    }
  }
  u32 ai = 0u;
  while (ai < k[K6H_NANA]) {
    u32 av = ana[ai]; flags[av] = flags[av] & (~2u); ai = ai + 1u;
  }
  if (uip == 0xFFFFFFFFu) { return false; }
  kl[0] = uip;
  u32 nkl = k[K6H_NKL]; u32 jlvl = 0u; u32 wi = 1u; u32 i = 1u;
  while (i < nkl) {
    u32 il = lvl[kl[i] >> 1];
    if (il > jlvl) { jlvl = il; wi = i; }
    i = i + 1u;
  }
  if (nkl >= 2u && wi != 1u) { u32 t = kl[1]; kl[1] = kl[wi]; kl[wi] = t; }
  full_k6_backtrack(k, jlvl);
  ai = 0u; while (ai < k[K6H_NANA]) { full_k6_mtf(k, ana[ai]); ai = ai + 1u; }
  if (nkl == 1u) { full_k6_assign(k, uip, 0xFFFFFFFFu); return true; }
  u32 nc = k[K6H_NC]; u32 off = k[K6H_ALEN]; u32 cap = k[K6H_ACAP];
  if (nc >= k[K6H_MAX_CL] || off + nkl > cap) { return false; }
  i = 0u; while (i < nkl) { arena[off + i] = kl[i]; i = i + 1u; }
  k[K6H_ALEN] = off + nkl;
  cl_off[nc] = off; cl_sz[nc] = nkl; k[K6H_NC] = nc + 1u;
  full_k6_watch(k, nc, kl[0], kl[1]);
  full_k6_assign(k, uip, nc);
  return true;
}

u64 full_k6_solve(FullHdr *h, u64 tick_lim) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 0ULL; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  full_k6_backtrack(k, 0u);
  if (k[K6H_INCONS] != 0u) { k[K6H_STATUS] = 20u; return 20ULL; }
  u64 cur_t = (u64)k[K6H_TICKS];
  u64 rem_t = 0xFFFFFFFFULL - cur_t;
  k[K6H_TICK_LIM] = (tick_lim >= rem_t) ? 0xFFFFFFFFu : (u32)(cur_t + tick_lim);
  k[K6H_STATUS] = 0u;
  u32 confl = full_k6_propagate(k);
  if (confl != 0xFFFFFFFFu) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; return 20ULL; }
  u32 *qprev = k + (32u + 2u * mv); u32 *flags = k + (32u + 6u * mv);
  u32 *assump = k + (32u + 9u * mv); u32 *vals = k + (32u + 10u * mv);
  while (k[K6H_TICKS] < k[K6H_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (k[K6H_LVL] == 0u) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; return 20ULL; }
      if (!full_k6_analyze(k, confl)) { k[K6H_STATUS] = 0u; return 0ULL; }
      confl = full_k6_propagate(k);
      continue;
    }
    u32 ad = 0u; u32 na = k[K6H_NASSUMP]; bool did_assump = false;
    while (ad < na) {
      u32 a = assump[ad]; u32 av = vals[a];
      if (av == 2u) { k[K6H_STATUS] = 20u; return 20ULL; }
      if (av == 0u) {
        k[K6H_LVL] = k[K6H_LVL] + 1u; full_k6_assign(k, a, 0xFFFFFFFFu);
        confl = full_k6_propagate(k); did_assump = true; break;
      }
      ad = ad + 1u;
    }
    if (did_assump) { continue; }
    if (k[K6H_UNASS] == 0u) { k[K6H_STATUS] = 10u; return 10ULL; }
    u32 cur = k[K6H_QSEARCH]; u32 nv = k[K6H_NV]; u32 pick = 0xFFFFFFFFu; u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (vals[cur << 1] == 0u) { pick = cur; break; }
      cur = qprev[cur]; steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = k[K6H_QLAST]; steps = 0u;
      while (cur < nv && steps < nv) {
        if (vals[cur << 1] == 0u) { pick = cur; break; }
        cur = qprev[cur]; steps = steps + 1u;
      }
    }
    if (pick == 0xFFFFFFFFu) {
      cur = 0u;
      while (cur < nv) { if (vals[cur << 1] == 0u) { pick = cur; break; } cur = cur + 1u; }
    }
    if (pick == 0xFFFFFFFFu) { k[K6H_STATUS] = 10u; return 10ULL; }
    k[K6H_QSEARCH] = pick;
    u32 ph = (flags[pick] ^ k[K6H_PHASE]) & 1u;
    k[K6H_LVL] = k[K6H_LVL] + 1u;
    full_k6_assign(k, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_k6_propagate(k);
  }
  k[K6H_STATUS] = 0u;
  return 0ULL;
}

bool full_k6_flip(FullHdr *h, u32 lit) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return false; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  u32 v = lit >> 1;
  u32 *lvl = k + 32u; u32 *vals = k + (32u + 10u * mv);
  if (k[K6H_STATUS] != 10u || v >= k[K6H_NV] || vals[lit] != 1u || lvl[v] == 0u) {
    return false;
  }
  u32 *whead = k + (32u + 12u * mv); u32 *wnext = k + (32u + 14u * mv);
  u32 *wblit = k + (32u + 22u * mv); u32 *cl_off = k + (32u + 30u * mv);
  u32 *cl_sz = k + (32u + 34u * mv); u32 *arena = k + (32u + 38u * mv);
  u32 w = whead[lit]; u32 prev = 0xFFFFFFFFu;
  u64 visits = 0ULL; u64 ticks = 1ULL; bool ok = true;
  while (w != 0xFFFFFFFFu) {
    u32 nxt = wnext[w]; visits = visits + 1ULL;
    u32 wb = wblit[w]; u32 bv = wb & K6_LIT_MASK;
    if ((wb & K6_BIN_FLAG) != 0u) {
      if (bv == lit || vals[bv] != 1u) { ok = false; break; }
      prev = w; w = nxt; continue;
    }
    if (bv != lit && vals[bv] == 1u) { prev = w; w = nxt; continue; }
    ticks = ticks + 1ULL;
    u32 cid = w >> 1; u32 slot = w & 1u; u32 off = cl_off[cid]; u32 sz = cl_sz[cid];
    u32 other = arena[off + (slot ^ 1u)];
    if (other != lit && vals[other] == 1u) {
      wblit[w] = other; prev = w; w = nxt; continue;
    }
    u32 r = 2u; u32 ri = 0xFFFFFFFFu; u32 repl = 0u;
    while (r < sz) {
      u32 cand = arena[off + r];
      if (cand != lit && vals[cand] == 1u) { ri = r; repl = cand; break; }
      r = r + 1u;
    }
    if (ri == 0xFFFFFFFFu) { ok = false; break; }
    arena[off + slot] = repl; arena[off + ri] = lit;
    if (prev == 0xFFFFFFFFu) { whead[lit] = nxt; } else { wnext[prev] = nxt; }
    wblit[w] = other; wnext[w] = whead[repl]; whead[repl] = w;
    w = nxt;
  }
  full_k6_add_ticks(k, ticks + (visits >> 4));
  if (!ok) { return false; }
  vals[lit] = 2u; vals[lit ^ 1u] = 1u;
  return true;
}

void full_k512_add_live_m6(FullHdr *h, u32 a, u32 b) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return; }
  u32 *k = ((u32 *)h->scratch_buf) + (1280u + (mv << 1));
  if (k[K6H_STATUS] == 10u || k[K6H_LVL] != 0u) {
    full_k6_backtrack(k, 0u);
    k[K6H_STATUS] = 0u;
  }
  if (k[K6H_INCONS] != 0u) { k[K6H_STATUS] = 20u; return; }
  u32 *vals = k + (32u + 10u * mv);
  if (b == 0xFFFFFFFFu) {
    u32 va = vals[a];
    if (va == 2u) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; return; }
    if (va == 0u) { full_k6_assign(k, a, 0xFFFFFFFFu); }
    if (full_k6_propagate(k) != 0xFFFFFFFFu) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; }
    return;
  }
  u32 nc = k[K6H_NC]; u32 off = k[K6H_ALEN];
  if (nc >= k[K6H_MAX_CL] || off + 2u > k[K6H_ACAP]) { return; }
  u32 *cl_off = k + (32u + 30u * mv); u32 *cl_sz = k + (32u + 34u * mv);
  u32 *arena = k + (32u + 38u * mv);
  arena[off] = a; arena[off + 1u] = b;
  k[K6H_ALEN] = off + 2u; cl_off[nc] = off; cl_sz[nc] = 2u;
  k[K6H_NC] = nc + 1u;
  full_k6_watch(k, nc, a, b);
  u32 va = vals[a]; u32 vb = vals[b];
  if (va == 2u) {
    if (vb == 2u) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; return; }
    if (vb == 0u) { full_k6_assign(k, b, nc); }
  } else if (vb == 2u && va == 0u) {
    full_k6_assign(k, a, nc);
  }
  if (full_k6_propagate(k) != 0xFFFFFFFFu) { k[K6H_INCONS] = 1u; k[K6H_STATUS] = 20u; }
}
"

/-- Ordered live functions of `Src/Kitten.lean` (`14` fns). -/
def fns : List Fn := kitten_fns

end

public section

theorem full_m6_max_v_wf : Func.Wf full_m6_max_v_body := by kissat_wf_reify
theorem full_k6_add_ticks_wf : Func.Wf full_k6_add_ticks_body := by kissat_wf_reify
theorem full_k6_init_wf : Func.Wf full_k6_init_body := by kissat_wf_reify
theorem full_k6_watch_wf : Func.Wf full_k6_watch_body := by kissat_wf_reify
theorem full_k6_assign_wf : Func.Wf full_k6_assign_body := by kissat_wf_reify
theorem full_k6_add_clause_wf : Func.Wf full_k6_add_clause_body := by kissat_wf_reify
theorem full_k6_mtf_wf : Func.Wf full_k6_mtf_body := by kissat_wf_reify
theorem full_k6_backtrack_wf : Func.Wf full_k6_backtrack_body := by kissat_wf_reify
theorem full_k6_propagate_wf : Func.Wf full_k6_propagate_body := by kissat_wf_reify
theorem full_k6_ana_clause_wf : Func.Wf full_k6_ana_clause_body := by kissat_wf_reify
theorem full_k6_analyze_wf : Func.Wf full_k6_analyze_body := by kissat_wf_reify
theorem full_k6_solve_wf : Func.Wf full_k6_solve_body := by kissat_wf_reify
theorem full_k6_flip_wf : Func.Wf full_k6_flip_body := by kissat_wf_reify
theorem full_k512_add_live_m6_wf : Func.Wf full_k512_add_live_m6_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, kitten_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_m6_max_v_wf
  · exact full_k6_add_ticks_wf
  · exact full_k6_init_wf
  · exact full_k6_watch_wf
  · exact full_k6_assign_wf
  · exact full_k6_add_clause_wf
  · exact full_k6_mtf_wf
  · exact full_k6_backtrack_wf
  · exact full_k6_propagate_wf
  · exact full_k6_ana_clause_wf
  · exact full_k6_analyze_wf
  · exact full_k6_solve_wf
  · exact full_k6_flip_wf
  · exact full_k512_add_live_m6_wf

end

end LeanQbe.T.Examples.Kissat.Src.Kitten
