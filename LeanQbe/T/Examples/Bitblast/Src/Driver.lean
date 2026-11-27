/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Header

/-!
# Bitblast Evaluator Dispatch & Top-Level `bv_solve_bytes` (`Bitblast/Src/Driver.lean`)

Provides:
- MVP core AST evaluator (`const`, `var`, `not`, `gate` `.and`/`.xor`/`.beq`/`.or`, `ite`, `literal`
  `.getLsbD`/`.eq`), with clean dispatch hooks (`bv_eval_ops_core`, `bv_eval_ops_shift_mul`,
  `bv_eval_ops_div_cpop`) for Shards `S3`–`S5`
- `bv_init_workspace`: partitions `[work_base, work_base + avail)` into `BVHdr`, `atom_base`,
  `slice_off`, `aig`, `ht`, and `lits`
- `bv_solve_bytes(prog_ptr, prog_len, work_ptr, work_cap, fuel)`: validates `BVP1`, bitblasts,
  handles trivial UNSAT (`root == 0 -> 20`) and trivial SAT (`root == 1` ->
  `BV_TRIVIAL_SAT_MAGIC`, `10`), otherwise runs COI + DIMACS emission and calls extern
  `kissat_solve_bytes`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src.Driver

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

bitblast_c0! driver "
#include \"bitblast_internal.h\"

extern u32 bv_read_u32(u64 prog_ptr, u64 idx);
extern u64 bv_count_atoms(u64 prog_ptr, u32 n_vars);
extern bool bv_validate(u64 prog_ptr, u64 prog_len);
extern void bv_aig_init(BVHdr *h, u64 aig_ptr, u32 aig_cap,
                        u64 ht_ptr, u32 ht_mask, u32 num_atoms);
extern u32 bv_mk_and(BVHdr *h, u32 lhs, u32 rhs);
extern u32 bv_aig_not(u32 l);
extern u32 bv_aig_or(BVHdr *h, u32 a, u32 b);
extern u32 bv_aig_xor(BVHdr *h, u32 a, u32 b);
extern u32 bv_aig_beq(BVHdr *h, u32 a, u32 b);
extern u32 bv_aig_ite(BVHdr *h, u32 c, u32 t, u32 f);
extern u32 bv_lits_alloc(BVHdr *h, u32 count);
extern void bv_coi_mark(BVHdr *h, u32 root);
extern bool bv_dimacs_write(BVHdr *h, u32 root);
extern u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len,
                              u64 work_ptr, u64 work_cap, u64 fuel);

bool bv_eval_ops_core(BVHdr *h, u32 node_idx) {
  u64 nodes_w = BV_NODES_OFF(h->n_vars, h->n_cwords);
  u64 base = nodes_w + (u64)node_idx * 5ULL;
  u32 op = bv_read_u32(h->prog_ptr, base);
  u32 w = bv_read_u32(h->prog_ptr, base + 1ULL);
  u32 a = bv_read_u32(h->prog_ptr, base + 2ULL);
  u32 b = bv_read_u32(h->prog_ptr, base + 3ULL);
  u32 *slice_off = (u32 *)h->slice_off_ptr;
  if (op == BV_OP_VAR) {
    u32 off = bv_lits_alloc(h, w);
    if (h->oom != 0u) { return false; }
    u32 *lits = (u32 *)h->lits_ptr;
    u32 ab = ((u32 *)h->atom_base_ptr)[a];
    u32 j = 0u;
    while (j < w) {
      lits[off + j] = (ab + j) << 1;
      j = j + 1u;
    }
    slice_off[node_idx] = off;
    return true;
  }
  if (op == BV_OP_CONST) {
    u32 off = bv_lits_alloc(h, w);
    if (h->oom != 0u) { return false; }
    u32 *lits = (u32 *)h->lits_ptr;
    u64 cw_off = BV_CWORDS_OFF(h->n_vars) + (u64)a;
    u32 cur_word = 0u;
    u32 j = 0u;
    while (j < w) {
      if ((j & 31u) == 0u) {
        cur_word = bv_read_u32(h->prog_ptr, cw_off + (u64)(j >> 5));
      }
      lits[off + j] = (cur_word >> (j & 31u)) & 1u;
      j = j + 1u;
    }
    slice_off[node_idx] = off;
    return true;
  }
  if (op == BV_OP_NOT) {
    u32 off = bv_lits_alloc(h, w);
    if (h->oom != 0u) { return false; }
    u32 *lits = (u32 *)h->lits_ptr;
    u32 a_off = slice_off[a];
    u32 j = 0u;
    while (j < w) {
      lits[off + j] = bv_aig_not(lits[a_off + j]);
      j = j + 1u;
    }
    slice_off[node_idx] = off;
    return true;
  }
  if (op == BV_OP_GETLSBD) {
    u32 ew = bv_read_u32(h->prog_ptr, nodes_w + (u64)a * 5ULL + 1ULL);
    u32 res = 0u;
    if (b < ew) {
      u32 a_off = slice_off[a];
      res = ((u32 *)h->lits_ptr)[a_off + b];
    }
    slice_off[node_idx] = res;
    return true;
  }
  if (op == BV_OP_EQ) {
    u32 ew = bv_read_u32(h->prog_ptr, nodes_w + (u64)a * 5ULL + 1ULL);
    u32 *lits = (u32 *)h->lits_ptr;
    u32 a_off = slice_off[a];
    u32 b_off = slice_off[b];
    u32 acc = 1u;
    u32 j = 0u;
    while (j < ew) {
      u32 eqj = bv_aig_beq(h, lits[a_off + j], lits[b_off + j]);
      acc = bv_mk_and(h, acc, eqj);
      if (h->oom != 0u) { return false; }
      j = j + 1u;
    }
    slice_off[node_idx] = acc;
    return true;
  }
  return false;
}

bool bv_eval_ops_shift_mul(BVHdr *h, u32 node_idx) {
  (void)h;
  (void)node_idx;
  return false;
}

bool bv_eval_ops_div_cpop(BVHdr *h, u32 node_idx) {
  (void)h;
  (void)node_idx;
  return false;
}

bool bv_eval_node(BVHdr *h, u32 node_idx) {
  u64 base = BV_NODES_OFF(h->n_vars, h->n_cwords) + (u64)node_idx * 5ULL;
  u32 op = bv_read_u32(h->prog_ptr, base);
  u32 a = bv_read_u32(h->prog_ptr, base + 2ULL);
  u32 b = bv_read_u32(h->prog_ptr, base + 3ULL);
  u32 c = bv_read_u32(h->prog_ptr, base + 4ULL);
  u32 *slice_off = (u32 *)h->slice_off_ptr;
  if (op == BV_OP_BCONST) {
    slice_off[node_idx] = a & 1u;
    return true;
  }
  if (op == BV_OP_BNOT) {
    slice_off[node_idx] = bv_aig_not(slice_off[a]);
    return true;
  }
  if (op == BV_OP_GATE_AND) {
    u32 res = bv_mk_and(h, slice_off[a], slice_off[b]);
    if (h->oom != 0u) { return false; }
    slice_off[node_idx] = res;
    return true;
  }
  if (op == BV_OP_GATE_XOR) {
    u32 res = bv_aig_xor(h, slice_off[a], slice_off[b]);
    if (h->oom != 0u) { return false; }
    slice_off[node_idx] = res;
    return true;
  }
  if (op == BV_OP_GATE_BEQ) {
    u32 res = bv_aig_beq(h, slice_off[a], slice_off[b]);
    if (h->oom != 0u) { return false; }
    slice_off[node_idx] = res;
    return true;
  }
  if (op == BV_OP_GATE_OR) {
    u32 res = bv_aig_or(h, slice_off[a], slice_off[b]);
    if (h->oom != 0u) { return false; }
    slice_off[node_idx] = res;
    return true;
  }
  if (op == BV_OP_ITE) {
    u32 res = bv_aig_ite(h, slice_off[a], slice_off[b], slice_off[c]);
    if (h->oom != 0u) { return false; }
    slice_off[node_idx] = res;
    return true;
  }
  if (op <= BV_OP_ADD || op == BV_OP_NOT || op == BV_OP_APPEND ||
      op == BV_OP_EQ || op == BV_OP_ULT || op == BV_OP_GETLSBD) {
    return bv_eval_ops_core(h, node_idx);
  }
  if (op == BV_OP_UDIV || op == BV_OP_UMOD || op == BV_OP_CPOP) {
    return bv_eval_ops_div_cpop(h, node_idx);
  }
  return bv_eval_ops_shift_mul(h, node_idx);
}

bool bv_eval_program(BVHdr *h) {
  u32 n_nodes = h->n_nodes;
  u32 i = 0u;
  while (i < n_nodes) {
    if (!bv_eval_node(h, i)) {
      return false;
    }
    i = i + 1u;
  }
  return true;
}

bool bv_init_workspace(BVHdr *h, u64 work_base, u64 avail, u64 prog_ptr) {
  if (avail < BV_HDR_BYTES) { return false; }
  u32 n_vars = bv_read_u32(prog_ptr, 2ULL);
  u32 n_nodes = bv_read_u32(prog_ptr, 3ULL);
  u32 n_cwords = bv_read_u32(prog_ptr, 4ULL);
  u32 root_node = bv_read_u32(prog_ptr, 5ULL);
  u64 atom_end = bv_count_atoms(prog_ptr, n_vars);
  if (atom_end == 0ULL) { return false; }
  u32 num_atoms = (u32)(atom_end - 1ULL);
  u64 atom_bytes = (((u64)n_vars << 2) + 7ULL) & ~7ULL;
  u64 slice_bytes = (((u64)n_nodes << 2) + 7ULL) & ~7ULL;
  u64 fixed_bytes = BV_HDR_BYTES + atom_bytes + slice_bytes;
  if (avail <= fixed_bytes || avail - fixed_bytes < 64ULL) { return false; }
  u64 rem = avail - fixed_bytes;
  u64 acap64 = rem >> 5;
  if (acap64 >= BV_DIMACS_BOUND) { acap64 = BV_DIMACS_BOUND - 1ULL; }
  if ((u64)num_atoms >= acap64) { return false; }
  u64 aig_bytes = acap64 << 3;
  u64 ht_budget = rem >> 1;
  u64 ht_slots = 1ULL;
  while ((ht_slots << 3) <= ht_budget && ht_slots < 0x40000000ULL) {
    ht_slots = ht_slots << 1;
  }
  u64 ht_bytes = ht_slots << 2;
  if (rem < aig_bytes + ht_bytes) { return false; }
  u64 dyn_base = work_base + fixed_bytes;
  u64 aig_ptr = dyn_base;
  u64 ht_ptr = dyn_base + aig_bytes;
  u64 lits_ptr = ht_ptr + ht_bytes;
  u64 lits_bytes = (work_base + avail) - lits_ptr;
  u64 lcap64 = lits_bytes >> 2;
  if (lcap64 >= 0xFFFFFFFFULL) { lcap64 = 0xFFFFFFFEULL; }
  h->work_base = work_base;
  h->work_end = work_base + avail;
  h->prog_ptr = prog_ptr;
  h->atom_base_ptr = work_base + BV_HDR_BYTES;
  h->slice_off_ptr = work_base + BV_HDR_BYTES + atom_bytes;
  h->lits_ptr = lits_ptr;
  h->marks_ptr = 0ULL;
  h->dimacs_start = 0ULL;
  h->n_vars = n_vars;
  h->n_nodes = n_nodes;
  h->n_cwords = n_cwords;
  h->root_node = root_node;
  h->lits_len = 0u;
  h->lits_cap = (u32)lcap64;
  h->dimacs_len = 0u;
  u32 *atom_base = (u32 *)h->atom_base_ptr;
  u32 cur_atom = 1u;
  u32 k = 0u;
  while (k < n_vars) {
    atom_base[k] = cur_atom;
    u32 vw = bv_read_u32(prog_ptr, BV_VARS_OFF + ((u64)k << 1) + 1ULL);
    cur_atom = cur_atom + vw;
    k = k + 1u;
  }
  bv_aig_init(h, aig_ptr, (u32)acap64, ht_ptr, (u32)(ht_slots - 1ULL), num_atoms);
  return true;
}

u64 bv_solve_bytes(u64 prog_ptr, u64 prog_len, u64 work_ptr, u64 work_cap, u64 fuel) {
  if (fuel == 0ULL || prog_ptr == 0ULL || work_ptr == 0ULL) { return 0ULL; }
  if (work_cap > 0xFFFFFFFFFFFFFFFFULL - work_ptr) { return 0ULL; }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_cap < pad + BV_HDR_BYTES) { return 0ULL; }
  u64 work_base = work_ptr + pad;
  u64 avail = work_cap - pad;
  if (!bv_validate(prog_ptr, prog_len)) {
    *(u64 *)work_base = 0ULL;
    return 0ULL;
  }
  BVHdr *h = (BVHdr *)work_base;
  if (!bv_init_workspace(h, work_base, avail, prog_ptr)) {
    *(u64 *)work_base = 0ULL;
    return 0ULL;
  }
  if (!bv_eval_program(h)) {
    *(u64 *)work_base = 0ULL;
    return 0ULL;
  }
  u32 root_lit = ((u32 *)h->slice_off_ptr)[h->root_node];
  if (root_lit == 0u) {
    return 20ULL;
  }
  if (root_lit == 1u) {
    *(u64 *)work_base = BV_TRIVIAL_SAT_MAGIC;
    return 10ULL;
  }
  h->marks_ptr = h->aig_ptr + ((u64)h->aig_len << 3);
  if (h->marks_ptr > h->work_end || (u64)h->aig_len > h->work_end - h->marks_ptr) {
    *(u64 *)work_base = 0ULL;
    return 0ULL;
  }
  bv_coi_mark(h, root_lit);
  if (!bv_dimacs_write(h, root_lit)) {
    *(u64 *)work_base = 0ULL;
    return 0ULL;
  }
  u64 dstart = h->dimacs_start;
  u64 dlen = (u64)h->dimacs_len;
  u64 kcap = dstart - work_base;
  *(u64 *)work_base = 0ULL;
  return kissat_solve_bytes(dstart, dlen, work_base, kcap, fuel);
}
"

/-- Ordered live functions of `Bitblast/Src/Driver.lean` (`7` fns). -/
def fns : List Fn := driver_fns

end

public section

theorem bv_eval_ops_core_wf : Func.Wf bv_eval_ops_core_body := by bitblast_wf_reify
theorem bv_eval_ops_shift_mul_wf : Func.Wf bv_eval_ops_shift_mul_body := by bitblast_wf_reify
theorem bv_eval_ops_div_cpop_wf : Func.Wf bv_eval_ops_div_cpop_body := by bitblast_wf_reify
theorem bv_eval_node_wf : Func.Wf bv_eval_node_body := by bitblast_wf_reify
theorem bv_eval_program_wf : Func.Wf bv_eval_program_body := by bitblast_wf_reify
theorem bv_init_workspace_wf : Func.Wf bv_init_workspace_body := by bitblast_wf_reify
theorem bv_solve_bytes_wf : Func.Wf bv_solve_bytes_body := by bitblast_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, driver_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bv_eval_ops_core_wf
  · exact bv_eval_ops_shift_mul_wf
  · exact bv_eval_ops_div_cpop_wf
  · exact bv_eval_node_wf
  · exact bv_eval_program_wf
  · exact bv_init_workspace_wf
  · exact bv_solve_bytes_wf

end

end LeanQbe.T.Examples.Bitblast.Src.Driver
