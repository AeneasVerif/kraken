module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Module
public import LeanQbe.T.Wf
meta import LeanQbe.T.Frontend.C0

/-!
# LeanLCNF R2b Runtime (`LcnfC0Strings`)

Pure acyclic C0 implementation of the 13 remaining non-float `Lower.rtCalls` entries
(`lcnf_str_alloc`, `lcnf_nat_to_str`, `lcnf_char_op`, `lcnf_string_*`, `lcnf_ba_data`,
`lcnf_array_{mk,to_list,replicate}`), compiled from `c0/lcnf_c0_strings.c` with strict
C99 alignment, wrap-free UTF-8 decode bounds, saturating `inc_obj`, early `lcnf_string_cmp_op`
tag/op guard, alloc-before-dec `"0"` fast path, and `.exit` panic.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0

local elab "rt_r2b_c0_file!" path:str : command => do
  let src ← IO.FS.readFile path.getString
  elabC0Module (some `rtR2b) src (exits := ["lcnf_panic"]) (forceExpose := true)

rt_r2b_c0_file! "LeanQbe/T/LeanLCNF/c0/lcnf_c0_strings.c"

/-- R2b runtime module: 6 `r2b_*` helpers and 13 `lcnf_*` runtime functions (calling R2's
`r2_*` RC/memcpy/alloc helpers as externs). -/
def rtR2bMod : Module :=
  { rtR2b_module with
    externs := rtR2b_module.externs.filter (·.name != "lcnf_panic")
    exits := ["lcnf_panic"] }

/-- Well-formedness of every helper and exported function in `rtR2bMod`. -/
theorem r2b_alloc_mpz_wf : Func.Wf r2b_alloc_mpz_body := by t_wf_reify
theorem r2b_str_alloc_cap_wf : Func.Wf r2b_str_alloc_cap_body := by t_wf_reify
theorem r2b_utf8_len_wf : Func.Wf r2b_utf8_len_body := by t_wf_reify
theorem r2b_utf8_write_wf : Func.Wf r2b_utf8_write_body := by t_wf_reify
theorem r2b_utf8_decode_step_wf : Func.Wf r2b_utf8_decode_step_body := by t_wf_reify
theorem r2b_utf8_decode_cp_wf : Func.Wf r2b_utf8_decode_cp_body := by t_wf_reify

theorem lcnf_str_alloc_wf : Func.Wf lcnf_str_alloc_body := by t_wf_reify
theorem lcnf_char_op_wf : Func.Wf lcnf_char_op_body := by t_wf_reify
theorem lcnf_string_push_wf : Func.Wf lcnf_string_push_body := by t_wf_reify
theorem lcnf_string_append_wf : Func.Wf lcnf_string_append_body := by t_wf_reify
theorem lcnf_string_cmp_op_wf : Func.Wf lcnf_string_cmp_op_body := by t_wf_reify
theorem lcnf_string_pos_op_wf : Func.Wf lcnf_string_pos_op_body := by t_wf_reify
theorem lcnf_string_to_list_wf : Func.Wf lcnf_string_to_list_body := by t_wf_reify
theorem lcnf_string_mk_wf : Func.Wf lcnf_string_mk_body := by t_wf_reify
theorem lcnf_ba_data_wf : Func.Wf lcnf_ba_data_body := by t_wf_reify
theorem lcnf_array_mk_wf : Func.Wf lcnf_array_mk_body := by t_wf_reify
theorem lcnf_array_to_list_wf : Func.Wf lcnf_array_to_list_body := by t_wf_reify
theorem lcnf_array_replicate_wf : Func.Wf lcnf_array_replicate_body := by t_wf_reify
theorem lcnf_nat_to_str_wf : Func.Wf lcnf_nat_to_str_body := by t_wf_reify

/-- Well-formedness of every function in `rtR2bMod`. -/
theorem rtR2b_fns_wf : ∀ f ∈ rtR2bMod.fns, f.Wf := by
  intro f hf
  have hfn : rtR2bMod.fns =
      [r2b_alloc_mpz, r2b_str_alloc_cap, r2b_utf8_len, r2b_utf8_write, r2b_utf8_decode_step,
       r2b_utf8_decode_cp, lcnf_str_alloc, lcnf_char_op, lcnf_string_push, lcnf_string_append,
       lcnf_string_cmp_op, lcnf_string_pos_op, lcnf_string_to_list, lcnf_string_mk,
       lcnf_ba_data, lcnf_array_mk, lcnf_array_to_list, lcnf_array_replicate,
       lcnf_nat_to_str] := rfl
  rw [hfn] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact r2b_alloc_mpz_wf
  · exact r2b_str_alloc_cap_wf
  · exact r2b_utf8_len_wf
  · exact r2b_utf8_write_wf
  · exact r2b_utf8_decode_step_wf
  · exact r2b_utf8_decode_cp_wf
  · exact lcnf_str_alloc_wf
  · exact lcnf_char_op_wf
  · exact lcnf_string_push_wf
  · exact lcnf_string_append_wf
  · exact lcnf_string_cmp_op_wf
  · exact lcnf_string_pos_op_wf
  · exact lcnf_string_to_list_wf
  · exact lcnf_string_mk_wf
  · exact lcnf_ba_data_wf
  · exact lcnf_array_mk_wf
  · exact lcnf_array_to_list_wf
  · exact lcnf_array_replicate_wf
  · exact lcnf_nat_to_str_wf

/-- Check that `rtR2bMod` passes `Module.checkAcyclic`. -/
theorem rtR2b_checkAcyclic : rtR2bMod.checkAcyclic = true := by
  decide +kernel

end LeanQbe.T.LeanLCNF
