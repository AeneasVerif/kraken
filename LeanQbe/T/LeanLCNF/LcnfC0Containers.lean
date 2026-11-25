module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Module
public import LeanQbe.T.Wf
public meta import LeanQbe.T.Frontend.C0

/-!
# Pure C0 `ByteArray` & `Array` Runtime (`Milestone R2 Part 1`)

Self-contained, acyclic pure C0 implementation of Lean runtime `ByteArray` (`tag 248`,
`m_other = 1`) and `Array` (`tag 246`) COW primitives plus `lcnf_oob`, elaborated from
[lcnf_c0_containers.c](LeanQbe/T/LeanLCNF/c0/lcnf_c0_containers.c) aligned byte-for-byte with
R0's `LcnfC0Rt` (`sizeof = 33672`, `s.ba_empty @ 33544`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0

local elab "rt_r2_c0_file! " pfx:ident path:str : command => do
  let content ← IO.FS.readFile path.getString
  LeanQbe.T.Frontend.C0.elabC0Module (some pfx.getId) content
    (exits := ["lcnf_panic"]) (forceExpose := true)

rt_r2_c0_file! rtR2 "LeanQbe/T/LeanLCNF/c0/lcnf_c0_containers.c"

/-! ## Structural Well-Formedness (`Func.Wf`) & Acyclic Module Check -/

theorem r2_inc_obj_wf : Func.Wf r2_inc_obj_body := by t_wf_reify
theorem r2_dec_obj_wf : Func.Wf r2_dec_obj_body := by t_wf_reify
theorem r2_mem_copy_bytes_wf : Func.Wf r2_mem_copy_bytes_body := by t_wf_reify
theorem r2_cmp_byte_slices_wf : Func.Wf r2_cmp_byte_slices_body := by t_wf_reify
theorem lcnf_oob_wf : Func.Wf lcnf_oob_body := by t_wf_reify
theorem r2_alloc_sarray_wf : Func.Wf r2_alloc_sarray_body := by t_wf_reify
theorem r2_ensure_excl_ba_wf : Func.Wf r2_ensure_excl_ba_body := by t_wf_reify
theorem lcnf_ba_empty_wf : Func.Wf lcnf_ba_empty_body := by t_wf_reify
theorem lcnf_ba_mk_empty_wf : Func.Wf lcnf_ba_mk_empty_body := by t_wf_reify
theorem lcnf_ba_mk_wf : Func.Wf lcnf_ba_mk_body := by t_wf_reify
theorem lcnf_ba_get_wf : Func.Wf lcnf_ba_get_body := by t_wf_reify
theorem lcnf_ba_set_wf : Func.Wf lcnf_ba_set_body := by t_wf_reify
theorem lcnf_ba_push_wf : Func.Wf lcnf_ba_push_body := by t_wf_reify
theorem lcnf_ba_cmp_op_wf : Func.Wf lcnf_ba_cmp_op_body := by t_wf_reify
theorem r2_alloc_array_wf : Func.Wf r2_alloc_array_body := by t_wf_reify
theorem r2_ensure_excl_array_wf : Func.Wf r2_ensure_excl_array_body := by t_wf_reify
theorem lcnf_array_mk_empty_wf : Func.Wf lcnf_array_mk_empty_body := by t_wf_reify
theorem lcnf_array_get_wf : Func.Wf lcnf_array_get_body := by t_wf_reify
theorem lcnf_array_set_wf : Func.Wf lcnf_array_set_body := by t_wf_reify
theorem lcnf_array_push_wf : Func.Wf lcnf_array_push_body := by t_wf_reify
theorem lcnf_array_pop_wf : Func.Wf lcnf_array_pop_body := by t_wf_reify
theorem lcnf_array_swap_wf : Func.Wf lcnf_array_swap_body := by t_wf_reify

theorem rtR2_fns_wf : ∀ f ∈ rtR2_fns, Func.Wf f.body := by
  intro f hf
  simp only [rtR2_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r2_inc_obj_wf
  · exact r2_dec_obj_wf
  · exact r2_mem_copy_bytes_wf
  · exact r2_cmp_byte_slices_wf
  · exact lcnf_oob_wf
  · exact r2_alloc_sarray_wf
  · exact r2_ensure_excl_ba_wf
  · exact lcnf_ba_empty_wf
  · exact lcnf_ba_mk_empty_wf
  · exact lcnf_ba_mk_wf
  · exact lcnf_ba_get_wf
  · exact lcnf_ba_set_wf
  · exact lcnf_ba_push_wf
  · exact lcnf_ba_cmp_op_wf
  · exact r2_alloc_array_wf
  · exact r2_ensure_excl_array_wf
  · exact lcnf_array_mk_empty_wf
  · exact lcnf_array_get_wf
  · exact lcnf_array_set_wf
  · exact lcnf_array_push_wf
  · exact lcnf_array_pop_wf
  · exact lcnf_array_swap_wf

/-- R2 Part 1 verified C0 containers module (`ByteArray` + `Array` + `lcnf_oob`), calling R0
allocator/RC externs (`lcnf_alloc`, `lcnf_free_obj`, `lcnf_dec_ref_cold`, `lcnf_mark_persistent`)
and exiting via `lcnf_panic`. -/
def rtR2Mod : LeanQbe.T.Module :=
  { fns := rtR2_fns
    externs :=
      [ { name := "lcnf_alloc", as := [i64, i64], rs := [i64] }
      , { name := "lcnf_free_obj", as := [i64, i64], rs := [] }
      , { name := "lcnf_dec_ref_cold", as := [i64, i64], rs := [] }
      , { name := "lcnf_mark_persistent", as := [i64, i64], rs := [] } ]
    exits := ["lcnf_panic"] }

theorem rtR2_checkAcyclic : rtR2Mod.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.LeanLCNF
