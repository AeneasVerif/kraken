module

public import LeanQbe.T.LeanLCNF.LcnfC0Rt
public import LeanQbe.T.LeanLCNF.LcnfC0BigNum
public import LeanQbe.T.LeanLCNF.LcnfC0Containers
public import LeanQbe.T.LeanLCNF.LcnfC0Strings
public import LeanQbe.T.LeanLCNF.Lower
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Module
public import LeanQbe.T.Wf

/-!
# Unified Pure-C0 `LeanLCNF` Runtime (`LcnfC0Full`)

Combines all four verified, acyclic pure-C0 runtime modules into a single self-contained
`LeanQbe.T.Module` (`rtC0CoreMod` / `rtC0NoFloatMod`) covering **35 / 38 `Lower.rtCalls`**
(every non-float runtime entry point; only `lcnf_float_{bin,un,of_sci}` remain external):

- **R0 (`LcnfC0Rt`, 5 fns):** `lcnf_alloc`, `lcnf_free_obj`, `lcnf_dec_ref_cold`,
  `lcnf_mark_persistent`, `lcnf_clo_under`.
- **R1 (`LcnfC0BigNum`, 34 fns):** `lcnf_nat_alloc`, `lcnf_nat_slow`, `lcnf_int_op` + 31
  `rt_scratch*`/`bn_*`/`lcnf_{nat,int}_*` helpers.
- **R2 (`LcnfC0Containers`, 22 fns):** `lcnf_oob`, `lcnf_ba_{empty,mk_empty,mk,get,set,push,cmp}`,
  `lcnf_array_{mk_empty,get,set,push,pop,swap}` + 8 `r2_*` helpers.
- **R2b (`LcnfC0Strings`, 25 fns):** `lcnf_str_alloc`, `lcnf_char_op`, `lcnf_string_*`,
  `lcnf_ba_data`, `lcnf_array_{mk,to_list,replicate}`, `lcnf_nat_to_str` + 12 `r2b_*` helpers.

## Unified Header Layout (`LcnfC0FullRt` = `LcnfC0BigNumRt`, `33688` bytes)

`R1` appends two trailing `u64` fields (`scratch`, `scratch_cap`) directly after the `33672`-byte
`LcnfC0Rt` base slab while preserving offsets `0..33671` byte-for-byte with `LcnfC0Rt`,
`LcnfC0BaseRt`, and `test/lcnf/lcnf_rt.h`'s `LcnfRt`:

| Byte Range      | Field                     | Bytes | Notes                              |
|-----------------|---------------------------|-------|------------------------------------|
| `0..255`        | `extra_args[32]`          | 256   | `rtExtraOff = 0`                   |
| `256..33023`    | `globals[4096]`           | 32768 | `rtGlobalsOff = 256`               |
| `33024..33535`  | `free_list[64]`           | 512   | `rtFreeListOff = 33024`            |
| `33536..33607`  | `s.{large_free..chunks}`  | 72    | `rtHdrOff = 33536`, `ba_empty @ +8`|
| `33608..33671`  | `s.st.{allocs..bytes}`    | 64    | `rtStatsOff = 33608`               |
| `33672..33679`  | `scratch`                 | 8     | `rtScratchOff = 33672` (R1 BigNum) |
| `33680..33687`  | `scratch_cap`             | 8     | `rtScratchCapOff = 33680` (limbs)  |
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0 (TFlatFn)

@[expose] public section

/-! ## 1. Unified Header Struct & Layout Offsets -/

/-- Unified C0 runtime header struct (`LcnfC0BaseRt` `0..33671` + trailing R1 `scratch` fields
`33672..33687`, `sizeof = 33688`). -/
abbrev LcnfC0FullRt := LcnfC0BigNumRt

/-- Byte size of `LcnfC0FullRt` (`33688` bytes). -/
abbrev LcnfC0FullRt.sizeof : Nat := LcnfC0BigNumRt.sizeof

/-- Separation-logic footprint of the header words of `LcnfC0FullRt` (`33536..33687`). -/
abbrev LcnfC0FullRt.At : BitVec 64 → LcnfC0FullRt → Mem 64 → Prop := LcnfC0BigNumRt.At

/-- Byte offset of `free_list[0]` inside `LcnfC0FullRt` (`32*8 + 4096*8 = 33024`). -/
def rtFreeListOff : Nat := 33024

/-- Byte offset of `LcnfC0Hdr s` inside `LcnfC0FullRt` (`33024 + 64*8 = 33536`). -/
def rtHdrOff : Nat := 33536

/-- Byte offset of `s.ba_empty` inside `LcnfC0FullRt` (`33536 + 8 = 33544`). -/
def rtBaEmptyOff : Nat := 33544

/-- Byte offset of `s.cur` inside `LcnfC0FullRt` (`33536 + 16 = 33552`). -/
def rtCurOff : Nat := 33552

/-- Byte offset of `s.end` inside `LcnfC0FullRt` (`33536 + 24 = 33560`). -/
def rtEndOff : Nat := 33560

/-- Byte offset of `s.work` inside `LcnfC0FullRt` (`33536 + 32 = 33568`). -/
def rtWorkOff : Nat := 33568

/-- Byte offset of `s.work_cap` inside `LcnfC0FullRt` (`33536 + 40 = 33576`). -/
def rtWorkCapOff : Nat := 33576

/-- Byte offset of `s.st` (`LcnfC0Stats`) inside `LcnfC0FullRt` (`33536 + 72 = 33608`). -/
def rtStatsOff : Nat := 33608

/-- Byte offset of `s.st.live` inside `LcnfC0FullRt` (`33608 + 16 = 33624`). -/
def rtLiveOff : Nat := 33624

/-- Byte offset of `s.st.persistent` inside `LcnfC0FullRt` (`33608 + 32 = 33640`). -/
def rtPersistentOff : Nat := 33640

/-- Byte offset of trailing R1 `scratch` pointer inside `LcnfC0FullRt` (`33672`). -/
def rtScratchOff : Nat := 33672

/-- Byte offset of trailing R1 `scratch_cap` limb count inside `LcnfC0FullRt` (`33680`). -/
def rtScratchCapOff : Nat := 33680

/-- Project the `0..33671` `LcnfC0Rt` base header from `LcnfC0FullRt`. -/
def LcnfC0FullRt.toBaseRt (h : LcnfC0FullRt) : LcnfC0Rt :=
  { s_large_free := h.base_s_large_free
    s_ba_empty := h.base_s_ba_empty
    s_cur := h.base_s_cur
    s_end := h.base_s_end
    s_work := h.base_s_work
    s_work_cap := h.base_s_work_cap
    s_chunks := h.base_s_chunks
    s_nchunks := h.base_s_nchunks
    s_chunks_cap := h.base_s_chunks_cap
    s_st_allocs := h.base_s_st_allocs
    s_st_frees := h.base_s_st_frees
    s_st_live := h.base_s_st_live
    s_st_peak_live := h.base_s_st_peak_live
    s_st_persistent := h.base_s_st_persistent
    s_st_reused := h.base_s_st_reused
    s_st_cold_decs := h.base_s_st_cold_decs
    s_st_bytes := h.base_s_st_bytes }

/-- Construct `LcnfC0FullRt` from an `LcnfC0Rt` base header and R1 scratch metadata. -/
def LcnfC0FullRt.ofBaseRt (h : LcnfC0Rt) (scr scrCap : BitVec 64) : LcnfC0FullRt :=
  { base_s_large_free := h.s_large_free
    base_s_ba_empty := h.s_ba_empty
    base_s_cur := h.s_cur
    base_s_end := h.s_end
    base_s_work := h.s_work
    base_s_work_cap := h.s_work_cap
    base_s_chunks := h.s_chunks
    base_s_nchunks := h.s_nchunks
    base_s_chunks_cap := h.s_chunks_cap
    base_s_st_allocs := h.s_st_allocs
    base_s_st_frees := h.s_st_frees
    base_s_st_live := h.s_st_live
    base_s_st_peak_live := h.s_st_peak_live
    base_s_st_persistent := h.s_st_persistent
    base_s_st_reused := h.s_st_reused
    base_s_st_cold_decs := h.s_st_cold_decs
    base_s_st_bytes := h.s_st_bytes
    scratch := scr
    scratch_cap := scrCap }

/-! ## 2. Unified Pure-C0 Runtime Module (`rtC0CoreMod`) -/

/-- All 86 acyclic C0 runtime functions in callees-before-callers order:
R0 (`5`) ++ R1 (`34`) ++ R2 (`22`) ++ R2b (`25`). -/
def rtC0CoreFns : List Fn :=
  rtR0Mod.fns ++ rtR1Mod.fns ++ rtR2Mod.fns ++ rtR2bMod.fns

/-- Closed non-float pure-C0 runtime module (`86` functions, `0` externs, `exits = ["lcnf_panic"]`),
internalizing all cross-module calls (`lcnf_alloc`, `lcnf_free_obj`, `lcnf_dec_ref_cold`,
`lcnf_mark_persistent`) and covering all `35 / 38` non-float `Lower.rtCalls`. -/
def rtC0CoreMod : Module :=
  { fns := rtC0CoreFns, externs := [], exits := ["lcnf_panic"] }

/-- Alias emphasizing that `rtC0CoreMod` has `0` externs for non-float Lean programs. -/
abbrev rtC0NoFloatMod : Module := rtC0CoreMod

/-- The 3 remaining floating-point `Lower.rtCalls` externs not implemented in `rtC0CoreMod`. -/
def rtC0FloatExterns : List Extern :=
  [ { name := "lcnf_float_bin", as := [i64, i64, i64, i64], rs := [i64] }
  , { name := "lcnf_float_un", as := [i64, i64, i64], rs := [i64] }
  , { name := "lcnf_float_of_sci", as := [i64, i64, i64, i64], rs := [i64] } ]

/-- Pure-C0 runtime module paired with explicit float extern declarations for float-using programs.
-/
def rtC0WithFloatExternsMod : Module :=
  { fns := rtC0CoreFns, externs := rtC0FloatExterns, exits := ["lcnf_panic"] }

/-- All 35 `Lower.rtCalls` symbols implemented by `rtC0CoreMod`. -/
def rtC0CoreImplementedCalls : List Sym :=
  (rtCalls.map (·.1)).filter fun s => (rtC0CoreFns.map Fn.name).contains s

/-- Remaining `Lower.rtCalls` symbols not yet implemented by `rtC0CoreMod` (the 3 float ops). -/
def rtC0CoreMissingCalls : List Sym :=
  (rtCalls.map (·.1)).filter fun s => !(rtC0CoreFns.map Fn.name).contains s

/-- Link lowered `LeanLCNF` program functions (`tfs`) with the verified pure-C0 runtime
(`rtC0CoreFns`), removing all 35 verified runtime functions from `.externs`. When `withFloats` is
`false`, `.externs` is empty (`[]`); when `true`, only the 3 `lcnf_float_*` externs remain. -/
def linkLcnfWithRtC0 (tfs : List Frontend.C0.TFlatFn) (withFloats : Bool := false) : Module :=
  { fns := rtC0CoreFns ++ Frontend.C0.tflatFnsToFns tfs
    externs := if withFloats then rtC0FloatExterns else []
    exits := rtExitSyms }

end

/-! ## 3. Layout, Acyclicity, `Func.Wf`, and `Lower.rtCalls` Coverage Proofs -/

public section

theorem LcnfC0FullRt_sizeof_eq : LcnfC0FullRt.sizeof = 33688 := LcnfC0BigNumRt_sizeof_eq

theorem LcnfC0FullRt_base_compat :
    LcnfC0Rt.sizeof = 33672 ∧
    LcnfC0BaseRt.sizeof = LcnfC0Rt.sizeof ∧
    LcnfC0FullRt.sizeof = LcnfC0Rt.sizeof + 16 := by
  exact ⟨LcnfC0Rt_sizeof_eq, by rw [LcnfC0BaseRt_sizeof_eq, LcnfC0Rt_sizeof_eq],
    by rw [LcnfC0FullRt_sizeof_eq, LcnfC0Rt_sizeof_eq]⟩

theorem LcnfC0FullRt_offsets_ok :
    rtExtraOff = 0 ∧
    rtGlobalsOff = 256 ∧
    rtFreeListOff = 33024 ∧
    rtHdrOff = 33536 ∧
    rtBaEmptyOff = 33544 ∧
    rtCurOff = 33552 ∧
    rtEndOff = 33560 ∧
    rtWorkOff = 33568 ∧
    rtWorkCapOff = 33576 ∧
    rtStatsOff = 33608 ∧
    rtScratchOff = 33672 ∧
    rtScratchCapOff = 33680 ∧
    rtScratchCapOff + 8 = LcnfC0FullRt.sizeof := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [LcnfC0FullRt_sizeof_eq]; rfl

theorem LcnfC0FullRt_At_split (rt : BitVec 64) (h : LcnfC0FullRt) :
    LcnfC0FullRt.At rt h =
      (LcnfC0Rt.At rt h.toBaseRt ⋆
        cell (t := i64) (rt + 33672) h.scratch ⋆
        cell (t := i64) (rt + 33680) h.scratch_cap) := by
  dsimp only [LcnfC0FullRt.At]
  unfold LcnfC0BigNumRt.At LcnfC0Rt.At LcnfC0FullRt.toBaseRt
  simp only [Std.ExtHashMap.sep_assoc]

theorem rtC0CoreFns_length : rtC0CoreFns.length = 86 := by
  decide

theorem rtC0CoreMod_externs_nil : rtC0CoreMod.externs = [] := rfl

theorem rtC0CoreMod_exits_eq : rtC0CoreMod.exits = ["lcnf_panic"] := rfl

theorem rtC0CoreMod_checkAcyclic : rtC0CoreMod.checkAcyclic = true := by
  t_kernel_rfl

theorem rtC0WithFloatExternsMod_checkAcyclic : rtC0WithFloatExternsMod.checkAcyclic = true := by
  t_kernel_rfl

theorem rtC0CoreMod_namesNodup : rtC0CoreMod.namesNodup := by
  have h := rtC0CoreMod_checkAcyclic
  simp only [Module.checkAcyclic, Bool.and_eq_true] at h
  exact Module.namesNodup_of_checkNamesNodup h.1

theorem rtC0CoreMod_fns_names_nodup : (rtC0CoreMod.fns.map Fn.name).Nodup :=
  (List.nodup_append.mp rtC0CoreMod_namesNodup).1

private theorem symsNodup_of_nodup : ∀ (xs : List String), xs.Nodup → symsNodup xs = true
  | [], _ => rfl
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [symsNodup, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not]
    exact ⟨hnd.1, symsNodup_of_nodup xs hnd.2⟩

theorem rtC0CoreMod_symsNodup : symsNodup (rtC0CoreMod.fns.map Fn.name) = true :=
  symsNodup_of_nodup _ rtC0CoreMod_fns_names_nodup

theorem rtC0CoreMod_fns_wf : ∀ f ∈ rtC0CoreMod.fns, f.Wf := by
  intro f hf
  simp only [rtC0CoreMod, rtC0CoreFns, List.mem_append] at hf
  rcases hf with ((h0 | h1) | h2) | h2b
  · exact rtR0Mod_wf f h0
  · exact rtR1_fns_wf f h1
  · exact rtR2_fns_wf f h2
  · have hfn : rtR2bMod.fns =
        [r2b_inc_obj, r2b_dec_obj, r2b_mem_copy_bytes, r2b_cmp_byte_slices,
         r2b_alloc_sarray, r2b_alloc_array, r2b_alloc_mpz, r2b_str_alloc_cap,
         r2b_utf8_len, r2b_utf8_write, r2b_utf8_decode_step, r2b_utf8_decode_cp,
         lcnf_str_alloc, lcnf_char_op, lcnf_string_push, lcnf_string_append,
         lcnf_string_cmp_op, lcnf_string_pos_op, lcnf_string_to_list, lcnf_string_mk,
         lcnf_ba_data, lcnf_array_mk, lcnf_array_to_list, lcnf_array_replicate,
         lcnf_nat_to_str] := rfl
    rw [hfn] at h2b
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2b
    rcases h2b with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r2b_inc_obj_wf
    · exact r2b_dec_obj_wf
    · exact r2b_mem_copy_bytes_wf
    · exact r2b_cmp_byte_slices_wf
    · exact r2b_alloc_sarray_wf
    · exact r2b_alloc_array_wf
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

private theorem allFns_of_mem_full {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, allFns_of_mem_full (fun _ hm => h _ (List.mem_cons_of_mem _ hm))⟩

theorem rtC0CoreMod_allFns_wf : AllFns Fn.Wf rtC0CoreMod.fns :=
  allFns_of_mem_full rtC0CoreMod_fns_wf

theorem rtC0CoreMod_rtCalls_counts :
    rtCalls.length = 38 ∧
    rtC0CoreImplementedCalls.length = 35 ∧
    rtC0CoreMissingCalls = ["lcnf_float_bin", "lcnf_float_un", "lcnf_float_of_sci"] := by
  decide

/-- Every one of the 35 non-float `Lower.rtCalls` entries appears in `rtC0CoreMod.fns` with its
exact signature `(name, as, rs)`. -/
theorem rtC0CoreMod_rtCalls_sigs_match :
    ∀ entry ∈ rtCalls,
      entry.1 ∉ ["lcnf_float_bin", "lcnf_float_un", "lcnf_float_of_sci"] →
      entry ∈ rtC0CoreMod.fns.map Fn.sig := by
  decide

end

end LeanQbe.T.LeanLCNF
