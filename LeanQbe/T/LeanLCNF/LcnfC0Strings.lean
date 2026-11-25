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

/-- R2b runtime module containing all 12 `r2b_*` helpers and 13 `lcnf_*` runtime functions. -/
def rtR2bMod : Module :=
  { rtR2b_module with
    externs := rtR2b_module.externs.filter (·.name != "lcnf_panic")
    exits := ["lcnf_panic"] }

/-- Well-formedness of every helper and exported function in `rtR2bMod`. -/
theorem r2b_inc_obj_wf : Func.Wf r2b_inc_obj_body := by t_wf_reify
theorem r2b_dec_obj_wf : Func.Wf r2b_dec_obj_body := by t_wf_reify
theorem r2b_mem_copy_bytes_wf : Func.Wf r2b_mem_copy_bytes_body := by t_wf_reify
theorem r2b_cmp_byte_slices_wf : Func.Wf r2b_cmp_byte_slices_body := by t_wf_reify
theorem r2b_alloc_sarray_wf : Func.Wf r2b_alloc_sarray_body := by t_wf_reify
theorem r2b_alloc_array_wf : Func.Wf r2b_alloc_array_body := by t_wf_reify
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

/-- Check that `rtR2bMod` passes `Module.checkAcyclic`. -/
theorem rtR2b_checkAcyclic : rtR2bMod.checkAcyclic = true := by
  decide +kernel

end LeanQbe.T.LeanLCNF
