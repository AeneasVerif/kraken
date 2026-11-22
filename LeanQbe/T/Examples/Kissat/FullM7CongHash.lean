module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat Wave-4 Dynamic Congruence Hash Table (`FullM7CongHash`)

Strictly additive C0 helpers closing Gap #4 from `#3254` (`ht_sz <= 4096` / `3,072`-gate ceiling):
- `full_cong_ht_init_m7(h, ctrl_off, ht_off, max_sz)`: initializes the hash-table slice inside
  `h->scratch_buf[ht_off ..< ht_off + sz)` (`sz ∈ [16, 131072]` power of 2, capping gracefully at
  the largest fitting power of 2 in `h->scratch_cap - ht_off`), records `ht_off`/`sz` in
  `scr[ctrl_off + 6 .. + 7]`, and clears `h->res_sz = 0`.
- `full_cong_ht_grow_m7(h, ctrl_off)`: doubles `ht_sz` up to `131072` (supporting `<= 96k` gates
  at 75% load, e.g. `4096 -> 8192 -> 16384 -> 32768 -> 65536 -> 131072`) via a bounds-guarded
  in-place tagged rehash (`0x80000000u` migrated bit) inside `h->scratch_buf`, capping gracefully
  at the current `ht_sz` when `scratch_cap` is tight (`0` OOM, `0` silent table wipe).
- `full_cong_ht_lookup_m7(h, ctrl_off, htag, harity)`: probes `h->scratch_buf` for a gate record
  matching `(htag, harity, h->tmp[0 ..< harity])` with linear probing.
- `full_cong_ht_insert_m7(h, ctrl_off, ent)`: inserts gate record `ent` (auto-growing at 75% load
  via `full_cong_ht_grow_m7` before probing) and returns `ent`, an existing congruent entry, or
  `0xFFFFFFFFu` on invalid bounds / exhausted capacity.

Zero edits to frozen `Full1..6*`, `0` externs, `0` exits, `checkAcyclic = true`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7CongHash

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat

kissat_c0! m7CongHash "
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

u64 full_cong_ht_hash_ent_m7(FullHdr *h, u32 ent, u64 ht_off) {
  u64 e = (u64)ent;
  if (e + 2ULL > ht_off || ht_off > h->scratch_cap) {
    return 0ULL;
  }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 meta = scr[e + 1ULL];
  u64 htag = (u64)(meta >> 28);
  u64 harity = (u64)(meta & 0xFFu);
  if (harity > 31ULL || e + 2ULL + harity > ht_off) {
    return 0ULL;
  }
  u64 hv = htag * 0x9E3779B1ULL + harity;
  u64 i = 0ULL;
  while (i < harity) {
    hv = hv * 0x85EBCA77ULL + (u64)scr[e + 2ULL + i] + 1ULL;
    i = i + 1ULL;
  }
  return hv;
}

u64 full_cong_ht_init_m7(FullHdr *h, u64 ctrl_off, u64 ht_off, u64 max_sz) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) {
    return 0ULL;
  }
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) {
    return 0ULL;
  }
  u64 avail = cap - ht_off;
  if (avail < 16ULL) {
    return 0ULL;
  }
  u64 lim = (max_sz == 0ULL) ? 131072ULL : max_sz;
  if (lim > 131072ULL) {
    lim = 131072ULL;
  }
  if (lim < 16ULL) {
    lim = 16ULL;
  }
  u64 top = (lim < avail) ? lim : avail;
  u64 sz = 16ULL;
  while (sz * 2ULL <= top) {
    sz = sz << 1;
  }
  u32 *scr = (u32 *)h->scratch_buf;
  scr[ctrl_off + 6ULL] = (u32)ht_off;
  scr[ctrl_off + 7ULL] = (u32)sz;
  u64 k = 0ULL;
  while (k < sz) {
    scr[ht_off + k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  h->res_sz = 0ULL;
  return sz;
}

u64 full_cong_ht_grow_m7(FullHdr *h, u64 ctrl_off) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) {
    return 0ULL;
  }
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ht_off = (u64)scr[ctrl_off + 6ULL];
  u64 old_sz = (u64)scr[ctrl_off + 7ULL];
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) {
    return 0ULL;
  }
  if (old_sz < 16ULL || old_sz > 131072ULL || (old_sz & (old_sz - 1ULL)) != 0ULL ||
      old_sz > cap - ht_off) {
    return 0ULL;
  }
  if (old_sz == 131072ULL) {
    return old_sz;
  }
  u64 new_sz = old_sz << 1;
  if (new_sz > cap - ht_off) {
    return old_sz;
  }
  u64 k = old_sz;
  while (k < new_sz) {
    scr[ht_off + k] = 0xFFFFFFFFu;
    k = k + 1ULL;
  }
  u64 i = 0ULL;
  while (i < old_sz) {
    u32 raw = scr[ht_off + i];
    if (raw != 0xFFFFFFFFu && (raw & 0x80000000u) == 0u && (u64)raw < ht_off) {
      scr[ht_off + i] = 0xFFFFFFFFu;
      u32 cur = raw;
      u64 hops = 0ULL;
      while (hops < new_sz) {
        u64 hv = full_cong_ht_hash_ent_m7(h, cur, ht_off);
        u64 slot = hv & (new_sz - 1ULL);
        u64 p = 0ULL;
        while (p < new_sz) {
          u32 dst = scr[ht_off + slot];
          if (dst == 0xFFFFFFFFu) {
            scr[ht_off + slot] = cur | 0x80000000u;
            cur = 0xFFFFFFFFu;
            break;
          }
          if ((dst & 0x80000000u) == 0u) {
            scr[ht_off + slot] = cur | 0x80000000u;
            cur = ((u64)dst < ht_off) ? dst : 0xFFFFFFFFu;
            break;
          }
          slot = (slot + 1ULL) & (new_sz - 1ULL);
          p = p + 1ULL;
        }
        if (cur == 0xFFFFFFFFu) {
          break;
        }
        hops = hops + 1ULL;
      }
    }
    i = i + 1ULL;
  }
  u64 j = 0ULL;
  while (j < new_sz) {
    u32 v = scr[ht_off + j];
    if (v != 0xFFFFFFFFu) {
      scr[ht_off + j] = v & 0x7FFFFFFFu;
    }
    j = j + 1ULL;
  }
  scr[ctrl_off + 7ULL] = (u32)new_sz;
  return new_sz;
}

u32 full_cong_ht_lookup_m7(FullHdr *h, u64 ctrl_off, u32 htag, u32 harity) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) {
    return 0xFFFFFFFFu;
  }
  u64 ha = (u64)harity;
  if (ha > 31ULL || ha > h->max_vars) {
    return 0xFFFFFFFFu;
  }
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ht_off = (u64)scr[ctrl_off + 6ULL];
  u64 ht_sz = (u64)scr[ctrl_off + 7ULL];
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) {
    return 0xFFFFFFFFu;
  }
  if (ht_sz < 16ULL || ht_sz > 131072ULL || (ht_sz & (ht_sz - 1ULL)) != 0ULL ||
      ht_sz > cap - ht_off) {
    return 0xFFFFFFFFu;
  }
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 hv = (u64)htag * 0x9E3779B1ULL + ha;
  u64 hi = 0ULL;
  while (hi < ha) {
    hv = hv * 0x85EBCA77ULL + (u64)tmp[hi] + 1ULL;
    hi = hi + 1ULL;
  }
  u64 slot = hv & (ht_sz - 1ULL);
  u64 p = 0ULL;
  while (p < ht_sz) {
    u32 ent = scr[ht_off + slot];
    if (ent == 0xFFFFFFFFu) {
      return 0xFFFFFFFFu;
    }
    u64 e = (u64)ent;
    if (e + 2ULL + ha <= ht_off) {
      u32 meta = scr[e + 1ULL];
      if ((meta >> 28) == htag && (meta & 0xFFu) == harity) {
        u32 eq = 1u;
        u64 k = 0ULL;
        while (k < ha) {
          if (scr[e + 2ULL + k] != tmp[k]) {
            eq = 0u;
            break;
          }
          k = k + 1ULL;
        }
        if (eq != 0u) {
          return ent;
        }
      }
    }
    slot = (slot + 1ULL) & (ht_sz - 1ULL);
    p = p + 1ULL;
  }
  return 0xFFFFFFFFu;
}

u32 full_cong_ht_insert_m7(FullHdr *h, u64 ctrl_off, u32 ent) {
  u64 cap = h->scratch_cap;
  if (ctrl_off > cap || 8ULL > cap - ctrl_off) {
    return 0xFFFFFFFFu;
  }
  u32 *scr = (u32 *)h->scratch_buf;
  u64 ht_off = (u64)scr[ctrl_off + 6ULL];
  u64 ht_sz = (u64)scr[ctrl_off + 7ULL];
  if (ht_off < ctrl_off + 8ULL || ht_off >= cap || ht_off > 0x7FFFFFFFULL) {
    return 0xFFFFFFFFu;
  }
  if (ht_sz < 16ULL || ht_sz > 131072ULL || (ht_sz & (ht_sz - 1ULL)) != 0ULL ||
      ht_sz > cap - ht_off) {
    return 0xFFFFFFFFu;
  }
  u64 e = (u64)ent;
  if (e + 2ULL > ht_off) {
    return 0xFFFFFFFFu;
  }
  u32 meta = scr[e + 1ULL];
  u32 etag = meta >> 28;
  u32 earity = meta & 0xFFu;
  u64 ea = (u64)earity;
  if (ea > 31ULL || e + 2ULL + ea > ht_off) {
    return 0xFFFFFFFFu;
  }
  if (ht_sz <= 131072ULL && (h->res_sz >= ht_sz || h->res_sz * 4ULL >= ht_sz * 3ULL)) {
    u64 grown = full_cong_ht_grow_m7(h, ctrl_off);
    if (grown >= 16ULL && (grown & (grown - 1ULL)) == 0ULL && grown <= cap - ht_off) {
      ht_sz = grown;
    }
  }
  u64 hv = full_cong_ht_hash_ent_m7(h, ent, ht_off);
  u64 slot = hv & (ht_sz - 1ULL);
  u64 p = 0ULL;
  while (p < ht_sz) {
    u32 cur = scr[ht_off + slot];
    if (cur == 0xFFFFFFFFu) {
      scr[ht_off + slot] = ent;
      h->res_sz = h->res_sz + 1ULL;
      return ent;
    }
    if (cur == ent) {
      return ent;
    }
    u64 c = (u64)cur;
    if (c + 2ULL + ea <= ht_off) {
      u32 cmeta = scr[c + 1ULL];
      if ((cmeta >> 28) == etag && (cmeta & 0xFFu) == earity) {
        u32 eq = 1u;
        u64 k = 0ULL;
        while (k < ea) {
          if (scr[c + 2ULL + k] != scr[e + 2ULL + k]) {
            eq = 0u;
            break;
          }
          k = k + 1ULL;
        }
        if (eq != 0u) {
          return cur;
        }
      }
    }
    slot = (slot + 1ULL) & (ht_sz - 1ULL);
    p = p + 1ULL;
  }
  return 0xFFFFFFFFu;
}
"

/-- Minimum congruence hash-table bucket count (`16`). -/
def m7CongHashMinSz : Nat := 16

/-- Maximum congruence hash-table bucket count (`131072`, supporting `<= 96k` gates at 75%
load without wiping or OOM). -/
def m7CongHashMaxSz : Nat := 131072

/-- Empty hash-table slot sentinel (`0xFFFFFFFF`). -/
def m7CongHashEmpty : BitVec 32 := 0xFFFFFFFF#32

/-- All `5` functions in `FullM7CongHash`. -/
def m7CongHashFns : List Fn := m7CongHash_fns

/-- External callee declarations (`0` externs: standalone congruence hash module). -/
def m7CongHashExterns : List Extern := []

/-- Standalone acyclic `LeanQbe.T.Module` (`0` exits, `0` externs). -/
def m7CongHashModule : LeanQbe.T.Module :=
  { fns := m7CongHashFns, externs := m7CongHashExterns, exits := [] }

/-- Canonical drop-in function handles for downstream orchestration (`FullM6Orch`). -/
def m7CongHtHashEntFn : Fn := full_cong_ht_hash_ent_m7
def m7CongHtInitFn : Fn := full_cong_ht_init_m7
def m7CongHtGrowFn : Fn := full_cong_ht_grow_m7
def m7CongHtLookupFn : Fn := full_cong_ht_lookup_m7
def m7CongHtInsertFn : Fn := full_cong_ht_insert_m7

theorem full_cong_ht_hash_ent_m7_wf : Func.Wf full_cong_ht_hash_ent_m7_body := by t_wf_reify
theorem full_cong_ht_init_m7_wf : Func.Wf full_cong_ht_init_m7_body := by t_wf_reify
theorem full_cong_ht_grow_m7_wf : Func.Wf full_cong_ht_grow_m7_body := by t_wf_reify
theorem full_cong_ht_lookup_m7_wf : Func.Wf full_cong_ht_lookup_m7_body := by t_wf_reify
theorem full_cong_ht_insert_m7_wf : Func.Wf full_cong_ht_insert_m7_body := by t_wf_reify

theorem m7CongHashFns_wf : ∀ f ∈ m7CongHashFns, f.Wf := by
  intro f hf
  simp only [m7CongHashFns, m7CongHash_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact full_cong_ht_hash_ent_m7_wf
  · exact full_cong_ht_init_m7_wf
  · exact full_cong_ht_grow_m7_wf
  · exact full_cong_ht_lookup_m7_wf
  · exact full_cong_ht_insert_m7_wf

theorem m7CongHash_acyclic : m7CongHashModule.checkAcyclic = true := by t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7CongHash
