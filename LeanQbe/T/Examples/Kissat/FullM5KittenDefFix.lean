module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat `M5`: Kitten Safety, VMTF Queue, & `full_find_definition` Fixes

Standalone drop-in replacements for `[170] full_find_definition` and `FullKitten`
(`full_kitten_{add_clause,ana_clause,build_failing,solve,core}`), `0` edits to `FullKitten.lean`,
`FullDefSweep.lean`, `Full1..3`, or `FullM4.lean`:

1. **`full_kitten_add_clause_m5`**: rejects unit clauses cleanly (`return false`) when
   `k[KH_NUNITS] >= 256u` before mutating arena/`nc`/`orig_nc`, preventing silent unit drops.
2. **`full_kitten_ana_clause_m5`**: marks level-`0` variables (`KO_FLAGS[v] |= 2u`,
   pushed to `KO_ANA`) so each level-`0` reason is recorded in `KO_RES` at most once.
3. **`full_kitten_build_failing_m5` & `full_kitten_core_m5`**: clears stale `KM_CORE`
   bits across `0 .. k[KH_NC]` on BOTH `INCONS` and `FAILING` paths before seeding the core.
4. **`full_kitten_solve_m5`**: saturates `u32` `KH_TICK_LIM` at `0xFFFFFFFFu` without
   modulo-`2^32` wraparound, loops strictly on `k[KH_TICKS] < k[KH_TICK_LIM]`, clears stale
   `KH_FAILING` on pre-existing `KH_INCONS`, and delegates failing assumptions to
   `full_kitten_build_failing_m5`.
5. **`full_find_definition_m5`**: repairs VMTF queue pointers
   (`QLAST = QSEARCH = nv - 1u`, `QSTAMP = nv`, `QNEXT[nv - 1u] = 0xFFFFFFFFu`) after finalizing
   `nv > 0`, and snapshots the valid 1st-core `pmask`/`nmask` before `full_kitten_shrink` so a
   2nd-solve timeout preserves the already-proven gate core.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5KittenDefFix

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m5KittenDefFix "
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

#define PW_BIN_FLAG 0x80000000u
#define PW_LIT_MASK 0x7FFFFFFFu

#define K_BASE 256u
#define K_MAX_V 128u
#define K_MAX_L 256u
#define K_MAX_ORIG 512u
#define K_MAX_CL 896u

#define KH_NV 0u
#define KH_NC 1u
#define KH_ORIG_NC 2u
#define KH_LVL 3u
#define KH_PROP 4u
#define KH_TRL_END 5u
#define KH_UNASS 6u
#define KH_INCONS 7u
#define KH_FAILING 8u
#define KH_ANTE 9u
#define KH_QFIRST 10u
#define KH_QLAST 11u
#define KH_QSEARCH 12u
#define KH_QSTAMP 13u
#define KH_TICKS 14u
#define KH_TICK_LIM 15u
#define KH_ALEN 16u
#define KH_ACAP 17u
#define KH_NASSUMP 18u
#define KH_NUNITS 19u
#define KH_NRES 20u
#define KH_NKL 21u
#define KH_NANA 22u
#define KH_STATUS 23u
#define KH_PHASE 24u

#define KO_LVL 32u
#define KO_RSN 160u
#define KO_QPREV 288u
#define KO_QNEXT 416u
#define KO_QSTAMP 544u
#define KO_TRL 672u
#define KO_FLAGS 800u
#define KO_VALS 928u
#define KO_ASSUMP 1184u
#define KO_ANA 1312u
#define KO_KL 1440u
#define KO_UNITS 1568u
#define KO_RES 1824u
#define KO_WHEAD 2080u
#define KO_WNEXT 2336u
#define KO_WBLIT 4128u
#define KO_CL_OFF 5920u
#define KO_CL_META 6816u
#define KO_CL_AUX 7712u
#define KO_ARENA 8608u

#define KM_CORE 0x10000u
#define KM_LRN 0x20000u

extern void full_kitten_init(FullHdr *h, u32 nv, u32 track_ante);
extern void full_kitten_watch(u32 *k, u32 cid, u32 l0, u32 l1);
extern void full_kitten_assign(u32 *k, u32 lit, u32 rsn);
extern void full_kitten_backtrack(u32 *k, u32 target_lvl);
extern u32 full_kitten_propagate(u32 *k);
extern bool full_kitten_analyze(u32 *k, u32 confl_cid);
extern void full_kitten_shrink(FullHdr *h);

bool full_kitten_add_clause_m5(FullHdr *h, u32 id, u32 *lits, u32 sz) {
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE;
  u32 nc = k[KH_NC]; u32 off = k[KH_ALEN];
  if (nc >= K_MAX_ORIG || off + sz > k[KH_ACAP]) { return false; }
  if (sz == 1u && k[KH_NUNITS] >= 256u) { return false; }
  if (sz == 0u) {
    k[KO_CL_OFF + nc] = off; k[KO_CL_META + nc] = 0u; k[KO_CL_AUX + nc] = id;
    if (k[KH_INCONS] == 0xFFFFFFFFu) { k[KH_INCONS] = nc; }
    k[KH_NC] = nc + 1u; k[KH_ORIG_NC] = nc + 1u; return true;
  }
  u32 i = 0u;
  while (i < sz) { k[KO_ARENA + off + i] = lits[i]; i = i + 1u; }
  k[KH_ALEN] = off + sz;
  k[KO_CL_OFF + nc] = off; k[KO_CL_META + nc] = sz; k[KO_CL_AUX + nc] = id;
  k[KH_NC] = nc + 1u; k[KH_ORIG_NC] = nc + 1u;
  if (sz == 1u) {
    u32 nu = k[KH_NUNITS];
    k[KO_UNITS + nu] = nc; k[KH_NUNITS] = nu + 1u;
    return true;
  }
  full_kitten_watch(k, nc, lits[0], lits[1]);
  return true;
}

void full_kitten_ana_clause_m5(u32 *k, u32 cid, u32 skip_v) {
  u32 clvl = k[KH_LVL]; u32 off = k[KO_CL_OFF + cid];
  u32 sz = k[KO_CL_META + cid] & 0xFFFFu;
  if (k[KH_ANTE] != 0u) {
    u32 nr = k[KH_NRES];
    if (nr < 256u) { k[KO_RES + nr] = cid; k[KH_NRES] = nr + 1u; }
    else if (nr == 256u) { k[KH_NRES] = 257u; }
  }
  u32 i = 0u;
  while (i < sz) {
    u32 l = k[KO_ARENA + off + i]; u32 v = l >> 1;
    if (v != skip_v && (k[KO_FLAGS + v] & 2u) == 0u) {
      k[KO_FLAGS + v] = k[KO_FLAGS + v] | 2u;
      if (k[KH_NANA] < 128u) { k[KO_ANA + k[KH_NANA]] = v; k[KH_NANA] = k[KH_NANA] + 1u; }
      u32 vlvl = k[KO_LVL + v];
      if (vlvl == 0u) {
        u32 r0 = k[KO_RSN + v];
        if (k[KH_ANTE] != 0u && r0 != 0xFFFFFFFFu) {
          u32 nr = k[KH_NRES];
          if (nr < 256u) { k[KO_RES + nr] = r0; k[KH_NRES] = nr + 1u; }
          else if (nr == 256u) { k[KH_NRES] = 257u; }
        }
      } else if (vlvl == clvl) {
        k[KH_STATUS] = k[KH_STATUS] + 1u;
      } else if (k[KH_NKL] < 128u) {
        k[KO_KL + k[KH_NKL]] = l; k[KH_NKL] = k[KH_NKL] + 1u;
      }
    }
    i = i + 1u;
  }
}

void full_kitten_build_failing_m5(u32 *k, u32 alit) {
  u32 nc = k[KH_NC]; u32 ci = 0u;
  while (ci < nc) { k[KO_CL_META + ci] = k[KO_CL_META + ci] & (~KM_CORE); ci = ci + 1u; }
  u32 nv = k[KH_NV]; u32 i = 0u;
  while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
  k[KO_FLAGS + (alit >> 1)] = k[KO_FLAGS + (alit >> 1)] | 2u;
  i = k[KH_TRL_END];
  while (i > 0u) {
    i = i - 1u;
    u32 lit = k[KO_TRL + i]; u32 v = lit >> 1;
    if ((k[KO_FLAGS + v] & 2u) == 0u) { continue; }
    k[KO_FLAGS + v] = k[KO_FLAGS + v] & (~2u);
    u32 rsn = k[KO_RSN + v];
    if (rsn == 0xFFFFFFFFu) { continue; }
    k[KO_CL_META + rsn] = k[KO_CL_META + rsn] | KM_CORE;
    u32 off = k[KO_CL_OFF + rsn]; u32 sz = k[KO_CL_META + rsn] & 0xFFFFu; u32 j = 0u;
    while (j < sz) {
      u32 lv = k[KO_ARENA + off + j] >> 1;
      if (lv != v) { k[KO_FLAGS + lv] = k[KO_FLAGS + lv] | 2u; }
      j = j + 1u;
    }
  }
  i = 0u; while (i < nv) { k[KO_FLAGS + i] = k[KO_FLAGS + i] & (~2u); i = i + 1u; }
  k[KH_FAILING] = 1u;
}

u64 full_kitten_solve_m5(FullHdr *h, u64 tick_lim) {
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE;
  full_kitten_backtrack(k, 0u);
  if (k[KH_INCONS] != 0xFFFFFFFFu) { k[KH_FAILING] = 0xFFFFFFFFu; return 20ULL; }
  u64 cur_t = (u64)k[KH_TICKS];
  u64 rem_t = 0xFFFFFFFFULL - cur_t;
  k[KH_TICK_LIM] = (tick_lim >= rem_t) ? 0xFFFFFFFFu : (u32)(cur_t + tick_lim);
  k[KH_FAILING] = 0xFFFFFFFFu;
  u32 ui = 0u;
  while (ui < k[KH_NUNITS]) {
    u32 ucid = k[KO_UNITS + ui]; u32 ul = k[KO_ARENA + k[KO_CL_OFF + ucid]];
    u32 uv = k[KO_VALS + ul];
    if (uv == 2u) { k[KH_INCONS] = ucid; return 20ULL; }
    if (uv == 0u) { full_kitten_assign(k, ul, ucid); }
    ui = ui + 1u;
  }
  u32 confl = full_kitten_propagate(k);
  if (confl == 0xFFFFFFFEu) { return 0ULL; }
  if (confl != 0xFFFFFFFFu) { k[KH_INCONS] = confl; return 20ULL; }
  while (k[KH_TICKS] < k[KH_TICK_LIM] && h->fuel > 0ULL) {
    h->fuel = h->fuel - 1ULL;
    if (confl != 0xFFFFFFFFu) {
      if (k[KH_LVL] == 0u) { k[KH_INCONS] = confl; return 20ULL; }
      if (!full_kitten_analyze(k, confl)) { return 0ULL; }
      confl = full_kitten_propagate(k);
      if (confl == 0xFFFFFFFEu) { return 0ULL; }
      continue;
    }
    u32 ad = 0u; u32 na = k[KH_NASSUMP]; bool did_assump = false;
    while (ad < na) {
      u32 a = k[KO_ASSUMP + ad]; u32 av = k[KO_VALS + a];
      if (av == 2u) { full_kitten_build_failing_m5(k, a); return 20ULL; }
      if (av == 0u) {
        k[KH_LVL] = k[KH_LVL] + 1u; full_kitten_assign(k, a, 0xFFFFFFFFu);
        confl = full_kitten_propagate(k); did_assump = true; break;
      }
      ad = ad + 1u;
    }
    if (confl == 0xFFFFFFFEu) { return 0ULL; }
    if (did_assump) { continue; }
    if (k[KH_UNASS] == 0u) { return 10ULL; }
    u32 cur = k[KH_QSEARCH]; u32 nv = k[KH_NV]; u32 pick = 0xFFFFFFFFu; u32 steps = 0u;
    while (cur < nv && steps < nv) {
      if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
      cur = k[KO_QPREV + cur]; steps = steps + 1u;
    }
    if (pick == 0xFFFFFFFFu) {
      cur = k[KH_QLAST]; steps = 0u;
      while (cur < nv && steps < nv) {
        if (k[KO_VALS + (cur << 1)] == 0u) { pick = cur; break; }
        cur = k[KO_QPREV + cur]; steps = steps + 1u;
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
    full_kitten_assign(k, (pick << 1) | ph, 0xFFFFFFFFu);
    confl = full_kitten_propagate(k);
    if (confl == 0xFFFFFFFEu) { return 0ULL; }
  }
  return 0ULL;
}

u32 full_kitten_core_m5(FullHdr *h) {
  u32 *k = ((u32 *)h->scratch_buf) + K_BASE; u32 nc = k[KH_NC];
  if (k[KH_INCONS] != 0xFFFFFFFFu) {
    u32 i = 0u;
    while (i < nc) { k[KO_CL_META + i] = k[KO_CL_META + i] & (~KM_CORE); i = i + 1u; }
    u32 inc = k[KH_INCONS];
    k[KO_CL_META + inc] = k[KO_CL_META + inc] | KM_CORE;
    u32 off = k[KO_CL_OFF + inc]; u32 sz = k[KO_CL_META + inc] & 0xFFFFu;
    u32 j = 0u;
    while (j < sz) {
      u32 r0 = k[KO_RSN + (k[KO_ARENA + off + j] >> 1)];
      if (r0 != 0xFFFFFFFFu) { k[KO_CL_META + r0] = k[KO_CL_META + r0] | KM_CORE; }
      j = j + 1u;
    }
  }
  u32 cid = nc;
  while (cid > 0u) {
    cid = cid - 1u; u32 meta = k[KO_CL_META + cid];
    if ((meta & KM_CORE) != 0u && (meta & KM_LRN) != 0u) {
      u32 off = k[KO_CL_OFF + cid]; u32 sz = meta & 0xFFFFu; u32 na = k[KO_CL_AUX + cid];
      u32 j = 0u;
      while (j < na) {
        u32 ant = k[KO_ARENA + off + sz + j];
        if (ant < nc) { k[KO_CL_META + ant] = k[KO_CL_META + ant] | KM_CORE; }
        j = j + 1u;
      }
    }
  }
  u32 csz = 0u; u32 i = 0u;
  while (i < k[KH_ORIG_NC]) {
    if ((k[KO_CL_META + i] & KM_CORE) != 0u) { csz = csz + 1u; }
    i = i + 1u;
  }
  return csz;
}

void full_find_definition_m5(FullHdr *h, u32 v, u32 np, u32 nn) {
  if (h->scratch_cap < 10240ULL || np == 0u || nn == 0u || np + nn < 3u) { return; }
  u32 *scr = (u32 *)h->scratch_buf; u32 *ar = (u32 *)h->arena; i8 *vals = (i8 *)h->values;
  u32 *tmk = (u32 *)h->tarjan_mark; u32 *exp = (u32 *)h->wsort; u32 *tmp = (u32 *)h->tmp_lits;
  full_kitten_init(h, 128u, 1u);
  u32 nv = 0u; u32 pl = v << 1; u32 nl = pl | 1u; bool abort_def = false;
  u32 trivial_side = 0xFFFFFFFFu; u32 side = 0u;
  while (side < 2u && !abort_def && trivial_side == 0xFFFFFFFFu) {
    u32 cnt = (side == 0u) ? np : nn; u32 off_s = (side == 0u) ? 0u : 64u;
    u32 except = (side == 0u) ? pl : nl; u32 idx = 0u;
    while (idx < cnt && !abort_def) {
      u32 w = scr[off_s + idx]; u32 eid = off_s + idx;
      if ((w & PW_BIN_FLAG) != 0u) {
        u32 l = w & PW_LIT_MASK; u32 lv = l >> 1;
        if (vals[l] == (i8)0) {
          if (tmk[lv] == 0u) {
            if (nv >= 128u) { abort_def = true; break; }
            exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
          }
          tmp[0] = ((tmk[lv] - 1u) << 1) | (l & 1u);
          if (!full_kitten_add_clause_m5(h, eid, tmp, 1u)) { abort_def = true; break; }
        } else if (vals[l] < (i8)0) { trivial_side = eid; break; }
      } else {
        u32 sz = ar[(u64)w + 2ULL]; bool sat = false; u32 csz = 0u; u32 k = 0u;
        while (k < sz) {
          u32 l = ar[(u64)w + 3ULL + (u64)k];
          if (l != except) {
            i8 lv_val = vals[l];
            if (lv_val > (i8)0) { sat = true; break; }
            if (lv_val == (i8)0) {
              u32 lv = l >> 1;
              if (tmk[lv] == 0u) {
                if (nv >= 128u) { abort_def = true; break; }
                exp[nv] = lv; nv = nv + 1u; tmk[lv] = nv;
              }
              if ((u64)csz < h->cur_vars) {
                tmp[csz] = ((tmk[lv] - 1u) << 1) | (l & 1u); csz = csz + 1u;
              } else { abort_def = true; break; }
            }
          }
          k = k + 1u;
        }
        if (abort_def) { break; }
        if (!sat) {
          if (csz == 0u) { trivial_side = eid; break; }
          if (!full_kitten_add_clause_m5(h, eid, tmp, csz)) { abort_def = true; break; }
        }
      }
      idx = idx + 1u;
    }
    side = side + 1u;
  }
  u32 ci = 0u; while (ci < nv) { tmk[exp[ci]] = 0u; ci = ci + 1u; }
  if (trivial_side != 0xFFFFFFFFu) {
    u64 pm = (trivial_side < 64u) ? (1ULL << (u64)trivial_side) : 0ULL;
    u64 nm = (trivial_side >= 64u) ? (1ULL << (u64)(trivial_side - 64u)) : 0ULL;
    scr[128] = (u32)pm; scr[129] = (u32)(pm >> 32);
    scr[130] = (u32)nm; scr[131] = (u32)(nm >> 32);
    return;
  }
  if (abort_def || nv == 0u) { return; }
  u32 *k = scr + 256;
  k[KH_NV] = nv; k[KH_UNASS] = nv; k[KH_NASSUMP] = 0u;
  k[KH_QLAST] = nv - 1u; k[KH_QSEARCH] = nv - 1u;
  k[KH_QSTAMP] = nv; k[KO_QNEXT + nv - 1u] = 0xFFFFFFFFu;
  u64 st = full_kitten_solve_m5(h, 8192ULL);
  if (st != 20ULL) { return; }
  u32 red = full_kitten_core_m5(h);
  if (red == 0u) { return; }
  u64 pmask = 0ULL; u64 nmask = 0ULL; u32 onc = k[KH_ORIG_NC]; ci = 0u;
  while (ci < onc) {
    if ((k[KO_CL_META + ci] & KM_CORE) != 0u) {
      u32 eid = k[KO_CL_AUX + ci];
      if (eid < 64u) { pmask = pmask | (1ULL << (u64)eid); }
      else if (eid < 128u) { nmask = nmask | (1ULL << (u64)(eid - 64u)); }
    }
    ci = ci + 1u;
  }
  full_kitten_shrink(h);
  if (full_kitten_solve_m5(h, 16384ULL) == 20ULL) {
    red = full_kitten_core_m5(h);
    u64 pmask2 = 0ULL; u64 nmask2 = 0ULL; u32 onc2 = k[KH_ORIG_NC]; ci = 0u;
    while (ci < onc2) {
      if ((k[KO_CL_META + ci] & KM_CORE) != 0u) {
        u32 eid = k[KO_CL_AUX + ci];
        if (eid < 64u) { pmask2 = pmask2 | (1ULL << (u64)eid); }
        else if (eid < 128u) { nmask2 = nmask2 | (1ULL << (u64)(eid - 64u)); }
      }
      ci = ci + 1u;
    }
    if (pmask2 != 0ULL || nmask2 != 0ULL) { pmask = pmask2; nmask = nmask2; }
  }
  if (pmask != 0ULL || nmask != 0ULL) {
    scr[128] = (u32)pmask; scr[129] = (u32)(pmask >> 32);
    scr[130] = (u32)nmask; scr[131] = (u32)(nmask >> 32);
  }
}
"

def m5KittenDefFixExterns : List Extern :=
  [ ⟨"full_kitten_init", [i64, i32, i32], []⟩
  , ⟨"full_kitten_watch", [i64, i32, i32, i32], []⟩
  , ⟨"full_kitten_assign", [i64, i32, i32], []⟩
  , ⟨"full_kitten_backtrack", [i64, i32], []⟩
  , ⟨"full_kitten_propagate", [i64], [i32]⟩
  , ⟨"full_kitten_analyze", [i64, i32], [.bool]⟩
  , ⟨"full_kitten_shrink", [i64], []⟩
  ]

def m5KittenDefFixModule : Module :=
  { externs := m5KittenDefFixExterns, exits := [], fns := m5KittenDefFix_fns }

theorem full_kitten_add_clause_m5_wf : Func.Wf full_kitten_add_clause_m5_body := by t_wf_reify
theorem full_kitten_ana_clause_m5_wf : Func.Wf full_kitten_ana_clause_m5_body := by t_wf_reify
theorem full_kitten_build_failing_m5_wf : Func.Wf full_kitten_build_failing_m5_body := by
  t_wf_reify
theorem full_kitten_solve_m5_wf : Func.Wf full_kitten_solve_m5_body := by t_wf_reify
theorem full_kitten_core_m5_wf : Func.Wf full_kitten_core_m5_body := by t_wf_reify
theorem full_find_definition_m5_wf : Func.Wf full_find_definition_m5_body := by t_wf_reify

theorem m5KittenDefFixModule_acyclic : m5KittenDefFixModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
