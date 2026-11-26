/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Header

/-!
# `BVP1` Structural, Bounds, and Overflow Validator (`Bitblast/Src/Validate.lean`)

Validates raw `BVP1` byte/word streams read-only matching `Bitblast.Ref.BVProg.parseWords`
plus variable-table prefix-sum `atom_base` overflow checks (`< BV_DIMACS_BOUND`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src.Validate

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

bitblast_c0! validate "
#include \"bitblast_internal.h\"

u32 bv_read_u32(u64 prog_ptr, u64 idx) {
  u8 *p = (u8 *)(prog_ptr + (idx << 2));
  u32 b0 = (u32)p[0];
  u32 b1 = (u32)p[1];
  u32 b2 = (u32)p[2];
  u32 b3 = (u32)p[3];
  return b0 | (b1 << 8) | (b2 << 16) | (b3 << 24);
}

u64 bv_count_atoms(u64 prog_ptr, u32 n_vars) {
  u64 atom_end = 1ULL;
  u32 k = 0u;
  while (k < n_vars) {
    u32 vw = bv_read_u32(prog_ptr, BV_VARS_OFF + ((u64)k << 1) + 1ULL);
    if ((u64)vw >= BV_DIMACS_BOUND || atom_end > BV_DIMACS_BOUND - 1ULL - (u64)vw) {
      return 0ULL;
    }
    atom_end = atom_end + (u64)vw;
    k = k + 1u;
  }
  return atom_end;
}

bool bv_validate_node(u64 prog_ptr, u64 nodes_w, u32 n_vars, u32 n_cwords, u32 i) {
  u64 base = nodes_w + (u64)i * 5ULL;
  u32 op = bv_read_u32(prog_ptr, base);
  u32 w = bv_read_u32(prog_ptr, base + 1ULL);
  u32 a = bv_read_u32(prog_ptr, base + 2ULL);
  u32 b = bv_read_u32(prog_ptr, base + 3ULL);
  u32 c = bv_read_u32(prog_ptr, base + 4ULL);
  if (op >= 32u) { return false; }
  if (op == BV_OP_VAR) {
    if (a >= n_vars) { return false; }
    u32 vw = bv_read_u32(prog_ptr, BV_VARS_OFF + ((u64)a << 1) + 1ULL);
    return vw == w;
  }
  if (op == BV_OP_CONST) {
    u64 nw = ((u64)w + 31ULL) >> 5;
    if (nw > 0ULL) {
      if ((u64)a > (u64)n_cwords || nw > (u64)n_cwords - (u64)a) {
        return false;
      }
    }
    return true;
  }
  if (op == BV_OP_EXTRACT) {
    if (b >= i) { return false; }
    u32 bop = bv_read_u32(prog_ptr, nodes_w + (u64)b * 5ULL);
    return bop < BV_OP_EQ;
  }
  if (op <= BV_OP_UMOD) {
    if (a >= i || b >= i) { return false; }
    u64 ab = nodes_w + (u64)a * 5ULL;
    u64 bb = nodes_w + (u64)b * 5ULL;
    u32 aop = bv_read_u32(prog_ptr, ab);
    u32 aw = bv_read_u32(prog_ptr, ab + 1ULL);
    u32 bop = bv_read_u32(prog_ptr, bb);
    u32 bw = bv_read_u32(prog_ptr, bb + 1ULL);
    return aop < BV_OP_EQ && bop < BV_OP_EQ && aw == w && bw == w;
  }
  if (op <= BV_OP_CPOP) {
    if (a >= i) { return false; }
    u64 ab = nodes_w + (u64)a * 5ULL;
    u32 aop = bv_read_u32(prog_ptr, ab);
    u32 aw = bv_read_u32(prog_ptr, ab + 1ULL);
    return aop < BV_OP_EQ && aw == w;
  }
  if (op == BV_OP_APPEND) {
    if (a >= i || b >= i) { return false; }
    u64 ab = nodes_w + (u64)a * 5ULL;
    u64 bb = nodes_w + (u64)b * 5ULL;
    u32 aop = bv_read_u32(prog_ptr, ab);
    u32 aw = bv_read_u32(prog_ptr, ab + 1ULL);
    u32 bop = bv_read_u32(prog_ptr, bb);
    u32 bw = bv_read_u32(prog_ptr, bb + 1ULL);
    return aop < BV_OP_EQ && bop < BV_OP_EQ && ((u64)aw + (u64)bw) == (u64)w;
  }
  if (op == BV_OP_REPLICATE) {
    if (a >= i) { return false; }
    u64 ab = nodes_w + (u64)a * 5ULL;
    u32 aop = bv_read_u32(prog_ptr, ab);
    u32 aw = bv_read_u32(prog_ptr, ab + 1ULL);
    return aop < BV_OP_EQ && ((u64)aw * (u64)b) == (u64)w;
  }
  if (op <= BV_OP_ASHR) {
    if (a >= i || b >= i) { return false; }
    u64 ab = nodes_w + (u64)a * 5ULL;
    u64 bb = nodes_w + (u64)b * 5ULL;
    u32 aop = bv_read_u32(prog_ptr, ab);
    u32 aw = bv_read_u32(prog_ptr, ab + 1ULL);
    u32 bop = bv_read_u32(prog_ptr, bb);
    return aop < BV_OP_EQ && bop < BV_OP_EQ && aw == w;
  }
  if (w != 1u) { return false; }
  if (op <= BV_OP_ULT) {
    if (a >= i || b >= i) { return false; }
    u64 ab = nodes_w + (u64)a * 5ULL;
    u64 bb = nodes_w + (u64)b * 5ULL;
    u32 aop = bv_read_u32(prog_ptr, ab);
    u32 aw = bv_read_u32(prog_ptr, ab + 1ULL);
    u32 bop = bv_read_u32(prog_ptr, bb);
    u32 bw = bv_read_u32(prog_ptr, bb + 1ULL);
    return aop < BV_OP_EQ && bop < BV_OP_EQ && aw == bw;
  }
  if (op == BV_OP_GETLSBD) {
    if (a >= i) { return false; }
    u32 aop = bv_read_u32(prog_ptr, nodes_w + (u64)a * 5ULL);
    return aop < BV_OP_EQ;
  }
  if (op == BV_OP_BCONST) {
    return a < 2u;
  }
  if (op == BV_OP_BNOT) {
    if (a >= i) { return false; }
    u32 aop = bv_read_u32(prog_ptr, nodes_w + (u64)a * 5ULL);
    return aop >= BV_OP_EQ;
  }
  if (op <= BV_OP_GATE_OR) {
    if (a >= i || b >= i) { return false; }
    u32 aop = bv_read_u32(prog_ptr, nodes_w + (u64)a * 5ULL);
    u32 bop = bv_read_u32(prog_ptr, nodes_w + (u64)b * 5ULL);
    return aop >= BV_OP_EQ && bop >= BV_OP_EQ;
  }
  if (a >= i || b >= i || c >= i) { return false; }
  u32 aop = bv_read_u32(prog_ptr, nodes_w + (u64)a * 5ULL);
  u32 bop = bv_read_u32(prog_ptr, nodes_w + (u64)b * 5ULL);
  u32 cop = bv_read_u32(prog_ptr, nodes_w + (u64)c * 5ULL);
  return aop >= BV_OP_EQ && bop >= BV_OP_EQ && cop >= BV_OP_EQ;
}

bool bv_validate(u64 prog_ptr, u64 prog_len) {
  if (prog_ptr == 0ULL || prog_len < 32ULL) { return false; }
  if ((prog_len & 3ULL) != 0ULL) { return false; }
  if (prog_len > 0xFFFFFFFFFFFFFFFFULL - prog_ptr) { return false; }
  u32 magic = bv_read_u32(prog_ptr, 0ULL);
  u32 ver = bv_read_u32(prog_ptr, 1ULL);
  if (magic != BV_MAGIC || ver != BV_VERSION) { return false; }
  u32 n_vars = bv_read_u32(prog_ptr, 2ULL);
  u32 n_nodes = bv_read_u32(prog_ptr, 3ULL);
  u32 n_cwords = bv_read_u32(prog_ptr, 4ULL);
  u32 root = bv_read_u32(prog_ptr, 5ULL);
  if (n_nodes == 0u || root >= n_nodes) { return false; }
  u64 total_words = 8ULL + ((u64)n_vars << 1) + (u64)n_cwords + (u64)n_nodes * 5ULL;
  if ((total_words << 2) != prog_len) { return false; }
  if (bv_count_atoms(prog_ptr, n_vars) == 0ULL) { return false; }
  u64 nodes_w = BV_NODES_OFF(n_vars, n_cwords);
  u32 i = 0u;
  while (i < n_nodes) {
    if (!bv_validate_node(prog_ptr, nodes_w, n_vars, n_cwords, i)) {
      return false;
    }
    i = i + 1u;
  }
  u32 rop = bv_read_u32(prog_ptr, nodes_w + (u64)root * 5ULL);
  return rop >= BV_OP_EQ;
}
"

/-- Ordered live functions of `Bitblast/Src/Validate.lean` (`4` fns). -/
def fns : List Fn := validate_fns

end

public section

theorem bv_read_u32_wf : Func.Wf bv_read_u32_body := by bitblast_wf_reify
theorem bv_count_atoms_wf : Func.Wf bv_count_atoms_body := by bitblast_wf_reify
theorem bv_validate_node_wf : Func.Wf bv_validate_node_body := by bitblast_wf_reify
theorem bv_validate_wf : Func.Wf bv_validate_body := by bitblast_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, validate_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact bv_read_u32_wf
  · exact bv_count_atoms_wf
  · exact bv_validate_node_wf
  · exact bv_validate_wf

end

end LeanQbe.T.Examples.Bitblast.Src.Validate
