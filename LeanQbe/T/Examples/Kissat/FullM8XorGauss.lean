/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Frontend.C0

/-!
# Kissat M8 Inprocessing XOR Extraction & $\mathbb{F}_2$ Gauss-Jordan Elimination (`FullM8XorGauss`)

Purely additive C0 subsystem (`Class S`, zero changes to `FullHdr` layout or `FullM7*` modules)
implementing sparse-mode root-level XOR extraction, degree-2 chain merging, connected-component
partitioning, bit-packed $\mathbb{F}_2$ Gauss-Jordan elimination (`c0_ctz64`, Kernighan weight
counts), and
entailed lemma/contradiction emission:

1. `full_xor_sort5` / `full_xor_parity_mask` / `full_xor_ht_insert`: sorted canonicalization and
   open-addressed `seen_mask` hash collector over `scratch_buf` for `k ∈ 3..5` XOR clauses.
2. `full_xor_collect_arena` / `full_xor_collect_bins`: extracts `3..5`-XORs from `arena`
   (stripping level-0 falsified literals) and `2`-XOR binary equivalence pairs from `watch_stk`,
   compacting complete XORs in-place inside `scratch_buf[0 .. eq_end)`.
3. `full_xor_compact_pool` / `full_xor_merge_two` / `full_xor_chain_merge`: iterative degree-2
   variable elimination via sorted symmetric difference (collapsing Tseitin/circuit wire chains
   and detecting immediate `0 = 1` contradictions).
4. `full_xor_uf_find` / `full_xor_read_u64` / `full_xor_write_u64` / `full_xor_swap_rows` /
   `full_xor_xor_rows` / `full_xor_build_mat` / `full_xor_rref`: component union-find and
   packed logical `u64`-word (stored as `u32` pairs in `scratch_buf`) Gauss-Jordan RREF.
5. `full_xor_emit_pool_small` / `full_xor_emit_mat` / `full_xor_gauss`: emits `h->inconsistent = 1`
   (`20ULL`), units (`full_add_unit`), binary equivalences (`full_add_bin`), and OOM-guarded
   short entailed clauses (`wt ∈ 3..4`, `full_add_clause`), followed by `full_propagate`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM8XorGauss

open LeanQbe.T
open LeanQbe.T.Frontend.C0

kissat_c0! m8XorGauss "
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

extern u32 full_arena_next(FullHdr *h, u32 cref);
extern bool full_has_bin(FullHdr *h, u32 a, u32 b);
extern bool full_has_ternary(FullHdr *h, u32 a, u32 b, u32 cl);
extern bool full_add_unit(FullHdr *h, u32 lit);
extern u64 full_add_bin(FullHdr *h, u32 a, u32 b);
extern u64 full_add_clause(FullHdr *h, u32 len, u32 glue, bool red);
extern u64 full_propagate(FullHdr *h);

bool full_xor_sort5(u32 *tmp, u32 k, u32 cv) {
  u32 i = 0u;
  while (i < k) {
    if ((tmp[i] >> 1u) >= cv) {
      return false;
    }
    i = i + 1u;
  }
  i = 0u;
  while (i < k) {
    u32 j = i + 1u;
    while (j < k) {
      u32 a = tmp[i];
      u32 b = tmp[j];
      if ((b >> 1u) < (a >> 1u)) {
        tmp[i] = b;
        tmp[j] = a;
      }
      j = j + 1u;
    }
    i = i + 1u;
  }
  u32 p = 0u;
  while (p + 1u < k) {
    if ((tmp[p] >> 1u) >= (tmp[p + 1u] >> 1u)) {
      return false;
    }
    p = p + 1u;
  }
  return true;
}

u32 full_xor_parity_mask(u32 k, bool odd_p) {
  if (k == 3u) {
    if (odd_p) { return 0x96u; }
    return 0x69u;
  }
  if (k == 4u) {
    if (odd_p) { return 0x6996u; }
    return 0x9669u;
  }
  if (k == 5u) {
    if (odd_p) { return 0x96696996u; }
    return 0x69969669u;
  }
  return 0u;
}

u64 full_xor_ht_insert(u32 *scr, u32 *tmp, u64 ht_cap, u64 used, u32 k) {
  if (ht_cap == 0ULL || k < 3u || k > 5u) {
    return used;
  }
  u32 v0 = tmp[0] >> 1u;
  u32 v1 = tmp[1] >> 1u;
  u32 v2 = tmp[2] >> 1u;
  u32 v3 = 0u;
  u32 v4 = 0u;
  if (k >= 4u) { v3 = tmp[3] >> 1u; }
  if (k >= 5u) { v4 = tmp[4] >> 1u; }
  u32 smask = 0u;
  u32 si = 0u;
  while (si < k) {
    if ((tmp[si] & 1u) != 0u) {
      smask = smask | (1u << si);
    }
    si = si + 1u;
  }
  u64 hval = ((u64)v0 * 2654435761ULL) ^ ((u64)v1 * 2246822519ULL) ^
             ((u64)v2 * 3266489917ULL) ^ ((u64)v3 * 668265263ULL) ^
             ((u64)v4 * 374761393ULL);
  u64 mask = ht_cap - 1ULL;
  u64 max_slots = (ht_cap * 3ULL) >> 2ULL;
  u64 probe = 0ULL;
  while (probe < 64ULL) {
    u64 slot = (hval + probe) & mask;
    u64 sb = slot * 7ULL;
    u32 sk = scr[sb];
    if (sk == 0u) {
      if (used < max_slots) {
        scr[sb] = k;
        scr[sb + 1ULL] = 1u << smask;
        scr[sb + 2ULL] = v0;
        scr[sb + 3ULL] = v1;
        scr[sb + 4ULL] = v2;
        scr[sb + 5ULL] = v3;
        scr[sb + 6ULL] = v4;
        return used + 1ULL;
      }
      return used;
    }
    if (sk == k && scr[sb + 2ULL] == v0 && scr[sb + 3ULL] == v1 &&
        scr[sb + 4ULL] == v2 && (k < 4u || scr[sb + 5ULL] == v3) &&
        (k < 5u || scr[sb + 6ULL] == v4)) {
      scr[sb + 1ULL] = scr[sb + 1ULL] | (1u << smask);
      return used;
    }
    probe = probe + 1ULL;
  }
  return used;
}

u64 full_xor_collect_arena(FullHdr *h, u64 ht_cap) {
  if (ht_cap == 0ULL) {
    return 0ULL;
  }
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *ar = (u32 *)h->arena;
  i8 *vals = (i8 *)h->values;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 cv = h->cur_vars;
  u64 alen = h->arena_len;
  u64 s = 0ULL;
  while (s < ht_cap) {
    scr[s * 7ULL] = 0u;
    s = s + 1ULL;
  }
  u64 p = 0ULL;
  u64 used = 0ULL;
  while (p < alen) {
    if (p + 3ULL > alen) {
      break;
    }
    u32 hdr = ar[p];
    u32 sz = ar[p + 2ULL];
    u64 next_p = (u64)full_arena_next(h, (u32)p);
    if ((hdr & 0x00080000u) == 0u && sz >= 3u && sz <= 16u && p + 3ULL + (u64)sz <= alen) {
      u32 k = 0u;
      bool sat = false;
      u32 j = 0u;
      while (j < sz) {
        u32 l = ar[p + 3ULL + (u64)j];
        if ((u64)l >= 2ULL * cv) {
          sat = true;
          break;
        }
        i8 dv = vals[l];
        if (dv == (i8)1) {
          sat = true;
          break;
        }
        if (dv == (i8)0) {
          if (k < 5u && (u64)k < cv) {
            tmp[k] = l;
            k = k + 1u;
          } else {
            k = 6u;
            break;
          }
        }
        j = j + 1u;
      }
      if (!sat && k >= 3u && k <= 5u) {
        if (full_xor_sort5(tmp, k, (u32)cv)) {
          used = full_xor_ht_insert(scr, tmp, ht_cap, used, k);
        }
      }
    }
    if (next_p <= p) {
      break;
    }
    p = next_p;
  }
  u64 out = 0ULL;
  s = 0ULL;
  while (s < ht_cap) {
    u64 sb = s * 7ULL;
    u32 k = scr[sb];
    if (k >= 3u && k <= 5u) {
      u32 seen = scr[sb + 1ULL];
      u32 pm_ev = full_xor_parity_mask(k, false);
      u32 pm_od = full_xor_parity_mask(k, true);
      bool has_t = (seen & pm_ev) == pm_ev;
      bool has_f = (seen & pm_od) == pm_od;
      if (has_t && has_f) {
        h->inconsistent = 1ULL;
        return 0xFFFFFFFFFFFFFFFFULL;
      }
      if (has_t || has_f) {
        u32 rhs_bit = 0u;
        if (has_t) { rhs_bit = 1u; }
        u32 v0 = scr[sb + 2ULL];
        u32 v1 = scr[sb + 3ULL];
        u32 v2 = scr[sb + 4ULL];
        u32 v3 = scr[sb + 5ULL];
        u32 v4 = scr[sb + 6ULL];
        scr[out] = k | (k << 16u) | (rhs_bit << 31u);
        scr[out + 1ULL] = v0;
        scr[out + 2ULL] = v1;
        scr[out + 3ULL] = v2;
        if (k >= 4u) { scr[out + 4ULL] = v3; }
        if (k >= 5u) { scr[out + 5ULL] = v4; }
        out = out + 1ULL + (u64)k;
      }
    }
    s = s + 1ULL;
  }
  return out;
}

u64 full_xor_collect_bins(FullHdr *h, u64 eq_end) {
  u64 cv = h->cur_vars;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  i8 *vals = (i8 *)h->values;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cap = h->scratch_cap;
  u64 wlen = h->wlen;
  u64 v = 0ULL;
  while (v < cv) {
    u32 lit = (u32)(v << 1ULL);
    if (vals[lit] == (i8)0) {
      u64 w_off = (u64)wvec[2ULL * (u64)lit];
      u64 w_sz = (u64)wvec[2ULL * (u64)lit + 1ULL];
      if (w_off + w_sz <= wlen) {
        u64 wi = 0ULL;
        while (wi < w_sz) {
          u32 entry = wstk[w_off + wi];
          if ((entry & 0x80000000u) != 0u) {
            if (entry != 0xFFFFFFFFu) {
              u32 ot = entry & 0x7FFFFFFFu;
              u64 ov = (u64)(ot >> 1u);
              if (v < ov && ov < cv && vals[ot] == (i8)0) {
                if (full_has_bin(h, lit ^ 1u, ot ^ 1u)) {
                  if (eq_end + 3ULL <= cap) {
                    u32 rhs_bit = (ot & 1u) ^ 1u;
                    scr[eq_end] = 2u | (2u << 16u) | (rhs_bit << 31u);
                    scr[eq_end + 1ULL] = (u32)v;
                    scr[eq_end + 2ULL] = (u32)ov;
                    eq_end = eq_end + 3ULL;
                  }
                }
              }
            }
            wi = wi + 1ULL;
          } else {
            if (wi + 2ULL > w_sz) {
              break;
            }
            wi = wi + 2ULL;
          }
        }
      }
    }
    v = v + 1ULL;
  }
  return eq_end;
}

u64 full_xor_compact_pool(u32 *scr, u64 eq_end) {
  u64 p = 0ULL;
  u64 out = 0ULL;
  while (p < eq_end) {
    u32 hdr = scr[p];
    u64 stride = (u64)((hdr >> 16u) & 0x7FFFu);
    u32 clen = hdr & 0xFFFFu;
    if (p + 1ULL + stride > eq_end) {
      break;
    }
    if (clen > 0u && (u64)clen <= stride) {
      u32 rhs_flag = hdr & 0x80000000u;
      scr[out] = clen | (clen << 16u) | rhs_flag;
      u64 i = 0ULL;
      while (i < (u64)clen) {
        scr[out + 1ULL + i] = scr[p + 1ULL + i];
        i = i + 1ULL;
      }
      out = out + 1ULL + (u64)clen;
    }
    p = p + 1ULL + stride;
  }
  return out;
}

u64 full_xor_merge_two(u32 *scr, u64 p1, u64 p2, u64 dst) {
  u32 h1 = scr[p1];
  u32 h2 = scr[p2];
  u64 len1 = (u64)(h1 & 0xFFFFu);
  u64 len2 = (u64)(h2 & 0xFFFFu);
  u32 rhs1 = h1 >> 31u;
  u32 rhs2 = h2 >> 31u;
  u32 new_rhs = rhs1 ^ rhs2;
  u64 i = 0ULL;
  u64 j = 0ULL;
  u64 out_n = 0ULL;
  while (i < len1 && j < len2) {
    u32 va = scr[p1 + 1ULL + i];
    u32 vb = scr[p2 + 1ULL + j];
    if (va < vb) {
      scr[dst + 1ULL + out_n] = va;
      out_n = out_n + 1ULL;
      i = i + 1ULL;
    } else if (vb < va) {
      scr[dst + 1ULL + out_n] = vb;
      out_n = out_n + 1ULL;
      j = j + 1ULL;
    } else {
      i = i + 1ULL;
      j = j + 1ULL;
    }
  }
  while (i < len1) {
    scr[dst + 1ULL + out_n] = scr[p1 + 1ULL + i];
    out_n = out_n + 1ULL;
    i = i + 1ULL;
  }
  while (j < len2) {
    scr[dst + 1ULL + out_n] = scr[p2 + 1ULL + j];
    out_n = out_n + 1ULL;
    j = j + 1ULL;
  }
  scr[p1] = h1 & 0x7FFF0000u;
  scr[p2] = h2 & 0x7FFF0000u;
  if (out_n == 0ULL) {
    if (new_rhs != 0u) {
      return 0xFFFFFFFFFFFFFFFFULL;
    }
    return dst;
  }
  u32 nl = (u32)out_n;
  scr[dst] = nl | (nl << 16u) | (new_rhs << 31u);
  return dst + 1ULL + out_n;
}

u64 full_xor_chain_merge(FullHdr *h, u64 eq_end) {
  u64 cv = h->cur_vars;
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cap = h->scratch_cap;
  u32 *occ = (u32 *)h->work_stk1;
  u32 *eq1 = (u32 *)h->work_stk2;
  u32 *eq2 = (u32 *)h->tarjan_reach;
  u64 round = 0ULL;
  while (round < 16ULL) {
    u64 v = 0ULL;
    while (v < cv) {
      occ[v] = 0u;
      eq1[v] = 0xFFFFFFFFu;
      eq2[v] = 0xFFFFFFFFu;
      v = v + 1ULL;
    }
    u64 p = 0ULL;
    while (p < eq_end) {
      u32 hdr = scr[p];
      u64 stride = (u64)((hdr >> 16u) & 0x7FFFu);
      u64 clen = (u64)(hdr & 0xFFFFu);
      if (p + 1ULL + stride > eq_end) {
        break;
      }
      if (clen > 0ULL && clen <= stride) {
        u64 i = 0ULL;
        while (i < clen) {
          u32 x = scr[p + 1ULL + i];
          if ((u64)x < cv) {
            u32 c_occ = occ[x];
            if (c_occ == 0u) {
              eq1[x] = (u32)p;
            } else if (c_occ == 1u) {
              eq2[x] = (u32)p;
            }
            occ[x] = c_occ + 1u;
          }
          i = i + 1ULL;
        }
      }
      p = p + 1ULL + stride;
    }
    u64 merges = 0ULL;
    v = 0ULL;
    while (v < cv) {
      if (occ[v] == 2u) {
        u64 p1 = (u64)eq1[v];
        u64 p2 = (u64)eq2[v];
        if (p1 < eq_end && p2 < eq_end && p1 != p2) {
          u32 h1 = scr[p1];
          u32 h2 = scr[p2];
          u64 l1 = (u64)(h1 & 0xFFFFu);
          u64 l2 = (u64)(h2 & 0xFFFFu);
          u64 s1 = (u64)((h1 >> 16u) & 0x7FFFu);
          u64 s2 = (u64)((h2 >> 16u) & 0x7FFFu);
          if (l1 > 0ULL && l2 > 0ULL && l1 <= s1 && l2 <= s2 &&
              p1 + 1ULL + l1 <= eq_end && p2 + 1ULL + l2 <= eq_end &&
              l1 + l2 <= 512ULL) {
            if (eq_end + 1ULL + l1 + l2 <= cap) {
              u64 next_dst = full_xor_merge_two(scr, p1, p2, eq_end);
              if (next_dst == 0xFFFFFFFFFFFFFFFFULL) {
                h->inconsistent = 1ULL;
                return 0xFFFFFFFFFFFFFFFFULL;
              }
              eq_end = next_dst;
              merges = merges + 1ULL;
            }
          }
        }
      }
      v = v + 1ULL;
    }
    eq_end = full_xor_compact_pool(scr, eq_end);
    if (merges == 0ULL) {
      break;
    }
    round = round + 1ULL;
  }
  return eq_end;
}

u32 full_xor_uf_find(u32 *par, u32 x, u64 cv) {
  u64 step = 0ULL;
  while (step < cv && (u64)x < cv) {
    u32 px = par[x];
    if (px == x || (u64)px >= cv) {
      return x;
    }
    u32 ppx = par[px];
    if ((u64)ppx < cv) {
      par[x] = ppx;
    }
    x = px;
    step = step + 1ULL;
  }
  return x;
}

u64 full_xor_read_u64(u32 *scr, u64 idx) {
  u64 lo = (u64)scr[idx];
  u64 hi = (u64)scr[idx + 1ULL];
  return lo | (hi << 32ULL);
}

void full_xor_write_u64(u32 *scr, u64 idx, u64 val) {
  scr[idx] = (u32)(val & 0xFFFFFFFFULL);
  scr[idx + 1ULL] = (u32)(val >> 32ULL);
}

void full_xor_swap_rows(u32 *scr, u64 mat, u64 r1, u64 r2, u64 row_u32s) {
  u64 b1 = mat + r1 * row_u32s;
  u64 b2 = mat + r2 * row_u32s;
  u64 i = 0ULL;
  while (i < row_u32s) {
    u32 t = scr[b1 + i];
    scr[b1 + i] = scr[b2 + i];
    scr[b2 + i] = t;
    i = i + 1ULL;
  }
}

void full_xor_xor_rows(u32 *scr, u64 mat, u64 dst_r, u64 src_r, u64 words64) {
  u64 row_u32s = words64 << 1ULL;
  u64 bd = mat + dst_r * row_u32s;
  u64 bs = mat + src_r * row_u32s;
  u64 w = 0ULL;
  while (w < words64) {
    u64 idx = w << 1ULL;
    u64 vd = full_xor_read_u64(scr, bd + idx);
    u64 vs = full_xor_read_u64(scr, bs + idx);
    full_xor_write_u64(scr, bd + idx, vd ^ vs);
    w = w + 1ULL;
  }
}

void full_xor_set_bit(u32 *scr, u64 rbase, u64 c) {
  u64 w = c >> 6ULL;
  u64 b = c & 63ULL;
  u64 idx = rbase + (w << 1ULL);
  u64 val = full_xor_read_u64(scr, idx);
  full_xor_write_u64(scr, idx, val | (1ULL << b));
}

u64 full_xor_build_mat(FullHdr *h, u64 root, u64 eq_end, u64 ncols) {
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cap = h->scratch_cap;
  u64 cv = h->cur_vars;
  u32 *par = (u32 *)h->work_stk1;
  u32 *var_col = (u32 *)h->tarjan_reach;
  u64 words64 = (ncols + 64ULL) >> 6ULL;
  u64 row_u32s = words64 << 1ULL;
  if (eq_end >= cap || row_u32s == 0ULL) {
    return 0ULL;
  }
  u64 max_rows = (cap - eq_end) / row_u32s;
  if (max_rows == 0ULL) {
    return 0ULL;
  }
  u64 mat = eq_end;
  u64 nrows = 0ULL;
  u64 p = 0ULL;
  while (p < eq_end && nrows < max_rows) {
    u32 hdr = scr[p];
    u64 stride = (u64)((hdr >> 16u) & 0x7FFFu);
    u64 clen = (u64)(hdr & 0xFFFFu);
    if (p + 1ULL + stride > eq_end) {
      break;
    }
    if (clen > 0ULL && clen <= stride) {
      u32 v0 = scr[p + 1ULL];
      if ((u64)v0 < cv && (u64)par[v0] == root) {
        u64 rbase = mat + nrows * row_u32s;
        u64 zi = 0ULL;
        while (zi < row_u32s) {
          scr[rbase + zi] = 0u;
          zi = zi + 1ULL;
        }
        u64 k = 0ULL;
        while (k < clen) {
          u32 vx = scr[p + 1ULL + k];
          if ((u64)vx < cv) {
            u64 col = (u64)var_col[vx];
            if (col < ncols) {
              full_xor_set_bit(scr, rbase, col);
            }
          }
          k = k + 1ULL;
        }
        if ((hdr >> 31u) != 0u) {
          full_xor_set_bit(scr, rbase, ncols);
        }
        nrows = nrows + 1ULL;
      }
    }
    p = p + 1ULL + stride;
  }
  return nrows;
}

void full_xor_rref(u32 *scr, u64 mat, u64 nrows, u64 ncols) {
  u64 words64 = (ncols + 64ULL) >> 6ULL;
  u64 row_u32s = words64 << 1ULL;
  u64 rank = 0ULL;
  u64 col = 0ULL;
  while (col < ncols && rank < nrows) {
    u64 widx = col >> 6ULL;
    u64 bmask = 1ULL << (col & 63ULL);
    u64 woff = widx << 1ULL;
    u64 piv = nrows;
    u64 r = rank;
    while (r < nrows) {
      u64 rw = full_xor_read_u64(scr, mat + r * row_u32s + woff);
      if ((rw & bmask) != 0ULL) {
        piv = r;
        break;
      }
      r = r + 1ULL;
    }
    if (piv < nrows) {
      if (piv != rank) {
        full_xor_swap_rows(scr, mat, rank, piv, row_u32s);
      }
      r = 0ULL;
      while (r < nrows) {
        if (r != rank) {
          u64 rw = full_xor_read_u64(scr, mat + r * row_u32s + woff);
          if ((rw & bmask) != 0ULL) {
            full_xor_xor_rows(scr, mat, r, rank, words64);
          }
        }
        r = r + 1ULL;
      }
      rank = rank + 1ULL;
    }
    col = col + 1ULL;
  }
}

u64 full_xor_emit_mat(FullHdr *h, u64 mat, u64 nrows, u64 ncols) {
  u32 *scr = (u32 *)h->scratch_buf;
  u32 *c2v = (u32 *)h->work_stk2;
  u32 *tmp = (u32 *)h->tmp_lits;
  u64 cv = h->cur_vars;
  u64 words64 = (ncols + 64ULL) >> 6ULL;
  u64 row_u32s = words64 << 1ULL;
  u64 last_w = ncols >> 6ULL;
  u64 rhs_sh = ncols & 63ULL;
  u64 last_mask = (1ULL << rhs_sh) - 1ULL;
  u64 emitted_cl = 0ULL;
  u64 r = 0ULL;
  while (r < nrows) {
    u64 rbase = mat + r * row_u32s;
    u64 rhs_word = full_xor_read_u64(scr, rbase + (last_w << 1ULL));
    u64 rhs_bit = (rhs_word >> rhs_sh) & 1ULL;
    u64 wt = 0ULL;
    u64 w = 0ULL;
    while (w < words64) {
      u64 wv = full_xor_read_u64(scr, rbase + (w << 1ULL));
      if (w == last_w) {
        wv = wv & last_mask;
      }
      u64 wv_t = wv;
      while (wv_t != 0ULL && wt <= 4ULL) {
        wt = wt + 1ULL;
        wv_t = wv_t & (wv_t - 1ULL);
      }
      if (wt > 4ULL) {
        break;
      }
      w = w + 1ULL;
    }
    if (wt == 0ULL) {
      if (rhs_bit != 0ULL) {
        h->inconsistent = 1ULL;
        return 20ULL;
      }
    } else if (wt <= 4ULL) {
      u64 c0 = 0ULL;
      u64 c1 = 0ULL;
      u64 c2 = 0ULL;
      u64 c3 = 0ULL;
      u64 nbits = 0ULL;
      w = 0ULL;
      while (w < words64) {
        u64 wv = full_xor_read_u64(scr, rbase + (w << 1ULL));
        if (w == last_w) {
          wv = wv & last_mask;
        }
        while (wv != 0ULL) {
          if (nbits >= 4ULL) {
            nbits = 5ULL;
            break;
          }
          u64 b = c0_ctz64(wv);
          u64 col = (w << 6ULL) + b;
          if (nbits == 0ULL) { c0 = col; }
          else if (nbits == 1ULL) { c1 = col; }
          else if (nbits == 2ULL) { c2 = col; }
          else { c3 = col; }
          nbits = nbits + 1ULL;
          wv = wv & (wv - 1ULL);
        }
        if (nbits > 4ULL) {
          break;
        }
        w = w + 1ULL;
      }
      if (nbits == 1ULL && c0 < ncols) {
        u32 v0 = c2v[c0];
        if ((u64)v0 < cv) {
          u32 lit = (v0 << 1u) | (u32)(rhs_bit ^ 1ULL);
          if (!full_add_unit(h, lit)) {
            return 20ULL;
          }
        }
      } else if (nbits == 2ULL && c0 < ncols && c1 < ncols) {
        u32 v0 = c2v[c0];
        u32 v1 = c2v[c1];
        if ((u64)v0 < cv && (u64)v1 < cv) {
          u32 a1 = (v0 << 1u) | (u32)rhs_bit;
          u32 b1 = (v1 << 1u) | 1u;
          if (!full_has_bin(h, a1, b1)) {
            if (h->wlen + 8ULL >= h->wcap) { return 1ULL; }
            u64 br1 = full_add_bin(h, a1, b1);
            if (br1 == 20ULL) { return 20ULL; }
            if (br1 == 2ULL) { h->oom = 0ULL; return 1ULL; }
          }
          u32 a2 = (v0 << 1u) | (u32)(rhs_bit ^ 1ULL);
          u32 b2 = v1 << 1u;
          if (!full_has_bin(h, a2, b2)) {
            if (h->wlen + 8ULL >= h->wcap) { return 1ULL; }
            u64 br2 = full_add_bin(h, a2, b2);
            if (br2 == 20ULL) { return 20ULL; }
            if (br2 == 2ULL) { h->oom = 0ULL; return 1ULL; }
          }
        }
      } else if ((nbits == 3ULL || nbits == 4ULL) &&
                 emitted_cl < 64ULL && nbits <= cv &&
                 h->arena_len + 64ULL < h->arena_cap &&
                 h->wlen + 64ULL < h->wcap) {
        u32 v0 = c2v[c0];
        u32 v1 = c2v[c1];
        u32 v2 = c2v[c2];
        u32 v3 = 0u;
        if (nbits == 4ULL) { v3 = c2v[c3]; }
        if ((u64)v0 < cv && (u64)v1 < cv && (u64)v2 < cv &&
            v0 != v1 && v0 != v2 && v1 != v2 &&
            (nbits < 4ULL || ((u64)v3 < cv && v3 != v0 && v3 != v1 && v3 != v2))) {
          u64 lim = 1ULL << nbits;
          u64 m = 0ULL;
          while (m < lim) {
            if (((m ^ (m >> 1ULL) ^ (m >> 2ULL) ^ (m >> 3ULL)) & 1ULL) != rhs_bit) {
              tmp[0] = (v0 << 1u) | (u32)(m & 1ULL);
              tmp[1] = (v1 << 1u) | (u32)((m >> 1ULL) & 1ULL);
              tmp[2] = (v2 << 1u) | (u32)((m >> 2ULL) & 1ULL);
              if (nbits == 4ULL) {
                tmp[3] = (v3 << 1u) | (u32)((m >> 3ULL) & 1ULL);
              }
              bool skip = false;
              if (nbits == 3ULL) {
                if (full_has_ternary(h, tmp[0], tmp[1], tmp[2])) {
                  skip = true;
                }
              }
              if (!skip) {
                u64 cr = full_add_clause(h, (u32)nbits, 0u, false);
                if (cr == 0xFFFFFFFFULL) {
                  return 1ULL;
                }
                emitted_cl = emitted_cl + 1ULL;
              }
            }
            m = m + 1ULL;
          }
        }
      }
    }
    r = r + 1ULL;
  }
  return 1ULL;
}

u64 full_xor_emit_pool_small(FullHdr *h, u64 eq_end) {
  u32 *scr = (u32 *)h->scratch_buf;
  u64 cv = h->cur_vars;
  u64 p = 0ULL;
  while (p < eq_end) {
    u32 hdr = scr[p];
    u64 stride = (u64)((hdr >> 16u) & 0x7FFFu);
    u64 clen = (u64)(hdr & 0xFFFFu);
    if (p + 1ULL + stride > eq_end) {
      break;
    }
    if (clen == 1ULL && clen <= stride) {
      u32 v0 = scr[p + 1ULL];
      u32 rhs_bit = hdr >> 31u;
      if ((u64)v0 < cv) {
        u32 lit = (v0 << 1u) | (rhs_bit ^ 1u);
        if (!full_add_unit(h, lit)) {
          return 20ULL;
        }
      }
    } else if (clen == 2ULL && clen <= stride) {
      u32 v0 = scr[p + 1ULL];
      u32 v1 = scr[p + 2ULL];
      u32 rhs_bit = hdr >> 31u;
      if ((u64)v0 < cv && (u64)v1 < cv && v0 != v1) {
        u32 a1 = (v0 << 1u) | rhs_bit;
        u32 b1 = (v1 << 1u) | 1u;
        if (!full_has_bin(h, a1, b1) && h->wlen + 8ULL < h->wcap) {
          u64 br1 = full_add_bin(h, a1, b1);
          if (br1 == 20ULL) { return 20ULL; }
          if (br1 == 2ULL) { h->oom = 0ULL; return 1ULL; }
        }
        u32 a2 = (v0 << 1u) | (rhs_bit ^ 1u);
        u32 b2 = v1 << 1u;
        if (!full_has_bin(h, a2, b2) && h->wlen + 8ULL < h->wcap) {
          u64 br2 = full_add_bin(h, a2, b2);
          if (br2 == 20ULL) { return 20ULL; }
          if (br2 == 2ULL) { h->oom = 0ULL; return 1ULL; }
        }
      }
    }
    p = p + 1ULL + stride;
  }
  return 1ULL;
}

u64 full_xor_gauss(FullHdr *h) {
  if (h->inconsistent != 0ULL) {
    return 20ULL;
  }
  if (h->cur_level != 0ULL || h->dense_mode != 0ULL ||
      h->cur_vars == 0ULL || h->scratch_cap < 3ULL) {
    return 1ULL;
  }
  u64 cap = h->scratch_cap;
  u64 ht_cap = 0ULL;
  if (cap >= 448ULL) {
    ht_cap = 64ULL;
    while ((ht_cap << 1ULL) * 7ULL <= cap && ht_cap < 4096ULL) {
      ht_cap = ht_cap << 1ULL;
    }
  }
  u64 eq_end = full_xor_collect_arena(h, ht_cap);
  if (eq_end == 0xFFFFFFFFFFFFFFFFULL) {
    return 20ULL;
  }
  eq_end = full_xor_collect_bins(h, eq_end);
  if (eq_end == 0ULL) {
    return 1ULL;
  }
  eq_end = full_xor_chain_merge(h, eq_end);
  if (eq_end == 0xFFFFFFFFFFFFFFFFULL) {
    return 20ULL;
  }
  if (eq_end > 0ULL) {
    if (full_xor_emit_pool_small(h, eq_end) == 20ULL) {
      return 20ULL;
    }
    u64 cv = h->cur_vars;
    u32 *scr = (u32 *)h->scratch_buf;
    u32 *par = (u32 *)h->work_stk1;
    u32 *c2v = (u32 *)h->work_stk2;
    u32 *var_col = (u32 *)h->tarjan_reach;
    u32 *comp_eq_cnt = (u32 *)h->wsort;
    u64 v = 0ULL;
    while (v < cv) {
      par[v] = (u32)v;
      var_col[v] = 0xFFFFFFFFu;
      comp_eq_cnt[v] = 0u;
      v = v + 1ULL;
    }
    u64 p = 0ULL;
    while (p < eq_end) {
      u32 hdr = scr[p];
      u64 stride = (u64)((hdr >> 16u) & 0x7FFFu);
      u64 clen = (u64)(hdr & 0xFFFFu);
      if (p + 1ULL + stride > eq_end) {
        break;
      }
      if (clen > 0ULL && clen <= stride) {
        u32 v0 = scr[p + 1ULL];
        if ((u64)v0 < cv) {
          u32 r0 = full_xor_uf_find(par, v0, cv);
          u64 k = 1ULL;
          while (k < clen) {
            u32 vk = scr[p + 1ULL + k];
            if ((u64)vk < cv) {
              u32 rk = full_xor_uf_find(par, vk, cv);
              if (rk != r0 && (u64)rk < cv && (u64)r0 < cv) {
                if (rk < r0) {
                  par[r0] = rk;
                  r0 = rk;
                } else {
                  par[rk] = r0;
                }
              }
            }
            k = k + 1ULL;
          }
        }
      }
      p = p + 1ULL + stride;
    }
    v = 0ULL;
    while (v < cv) {
      par[v] = full_xor_uf_find(par, (u32)v, cv);
      v = v + 1ULL;
    }
    p = 0ULL;
    while (p < eq_end) {
      u32 hdr = scr[p];
      u64 stride = (u64)((hdr >> 16u) & 0x7FFFu);
      u64 clen = (u64)(hdr & 0xFFFFu);
      if (p + 1ULL + stride > eq_end) {
        break;
      }
      if (clen > 0ULL && clen <= stride) {
        u32 v0 = scr[p + 1ULL];
        if ((u64)v0 < cv) {
          u32 rt = par[v0];
          if ((u64)rt < cv) {
            comp_eq_cnt[rt] = comp_eq_cnt[rt] + 1u;
          }
        }
      }
      p = p + 1ULL + stride;
    }
    u64 budget = 0ULL;
    u64 root = 0ULL;
    while (root < cv && budget < 4000000ULL) {
      if ((u64)par[root] == root && comp_eq_cnt[root] >= 2u) {
        u64 ncols = 0ULL;
        v = 0ULL;
        while (v < cv) {
          if ((u64)par[v] == root) {
            var_col[v] = (u32)ncols;
            c2v[ncols] = (u32)v;
            ncols = ncols + 1ULL;
          }
          v = v + 1ULL;
        }
        if (ncols > 0ULL) {
          u64 nrows = full_xor_build_mat(h, root, eq_end, ncols);
          budget = budget + nrows + eq_end;
          if (nrows >= 2ULL) {
            full_xor_rref(scr, eq_end, nrows, ncols);
            u64 er = full_xor_emit_mat(h, eq_end, nrows, ncols);
            if (er == 20ULL) {
              return 20ULL;
            }
          }
        }
      }
      root = root + 1ULL;
    }
  }
  if (h->propagated < h->trail_end) {
    u64 pr = full_propagate(h);
    if (pr == 1ULL) {
      h->inconsistent = 1ULL;
      return 20ULL;
    }
  }
  return 1ULL;
}
"

def m8XorGaussFns : List Fn := m8XorGauss_fns

def m8XorGaussExterns : List Extern :=
  [ ⟨"full_arena_next", [i64, i32], [i32]⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool]⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool]⟩
  , ⟨"full_add_unit", [i64, i32], [.bool]⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64]⟩
  , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64]⟩
  , ⟨"full_propagate", [i64], [i64]⟩ ]

def m8XorGaussModule : LeanQbe.T.Module :=
  { fns := m8XorGaussFns, externs := m8XorGaussExterns, exits := [] }

theorem m8XorGaussFns_wf : ∀ f ∈ m8XorGaussFns, f.Wf := by
  intro f hf
  simp only [m8XorGaussFns, m8XorGauss_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    t_wf_reify

theorem m8XorGauss_acyclic : m8XorGaussModule.checkAcyclic = true := by
  unfold m8XorGaussModule m8XorGaussFns m8XorGauss_fns
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM8XorGauss
