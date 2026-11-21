module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Part 8a (`ProbeTrans`, `6` fns)

Bridges all `6` landed `FullProbeTransLemmas` functions (`Full3` #10–15, table indices `[106..111]`)
directly onto canonical `FullSpec2` / `FullSpec3` contracts and `SpecEntry.Impl fullEnv`:
- `106`: `full_hbr_dom`
- `107`: `full_probe_prop_lit`
- `108`: `full_probe_prop`
- `109`: `full_probe_flush_hbr`
- `110`: `full_probe_assume_pair`
- `111`: `full_probe_run`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat

/-! ## Part 1: Private `FullProbeTransSpecs` → canonical `FullSpec` adapters -/

section Adapters

private theorem ptOtfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem canon_to_ptOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem ptOtfsInvW_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullProbeTransSpecs.FullOtfsInvW c F0 F_cur s) :
    FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, ptOtfs_to_canon h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem canon_to_ptOtfsInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) :
    FullProbeTransSpecs.FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, canon_to_ptOtfs h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem ptBacktrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hpr hcl' hps hsc htrl' hvl hw_w hw_o hm' => ?_⟩
  have hshrk : sc'.shrink_stk = s.scratch.shrink_stk := by
    rcases hsc with ⟨_, _, _, _, _, _, _, _, _, rfl⟩; rfl
  exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hpr hcl' hps hshrk htrl'
    (fun ⟨F0, Fc, hwo⟩ => hvl ⟨F0, Fc, hwo.elim Or.inl (Or.inr ∘ ptOtfs_to_canon)⟩)
    hw_w (fun F0 Fc ho hlt => hw_o F0 Fc (ptOtfs_to_canon ho) hlt) hm'

private theorem ptAnalyze20_adapter {Γ : Env}
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullAnalyze20Spec a m Q X →
      Γ "full_analyze" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcf, hm, hQ⟩
  refine hAna _ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcf, hm,
    fun r s' m' hlen' hr hcv hfu ⟨hws2, h20o⟩ h20u h0 h1 hm' => ?_⟩
  exact hQ r s' m' hlen' hr hcv hfu hws2
    (fun h20 => ⟨h20u h20, canon_to_ptOtfsInvW (h20o h20).1⟩)
    (fun h0' => canon_to_ptOtfsInvW (h0 h0')) h1 hm'

private theorem ptAssumePair_adapter {Γ : Env}
    (hAp : ∀ a m Q X, fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, hQ⟩
  refine hAp _ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm,
    fun r s' m' h12 h20 hcv hfu hr hm' => ?_⟩
  exact hQ r s' m' h12
    (fun h => let ⟨hu, Fc, ho⟩ := h20 h; ⟨hu, Fc, canon_to_ptOtfsInvW ho⟩)
    hcv hfu hr hm'

end Adapters

/-! ## Part 2: Canonical `*_bridge_wp` theorems (`6` fns, indices `[106..111]`) -/

section Bridges

theorem full_hbr_dom_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullHbrDomSpec a m Q X → Func.wp Γ full_hbr_dom_body a m Q X :=
  full_hbr_dom_wp Γ

theorem full_probe_prop_lit_bridge_wp (Γ : Env)
    (hFindRepl : ∀ a m Q X, fullFindReplSpec a m Q X →
      Γ "full_find_repl" [i64, i64] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hHbrDom : ∀ a m Q X, fullHbrDomSpec a m Q X →
      Γ "full_hbr_dom" [i64, i32, i32] [i32] a m Q X)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullProbePropLitSpec a m Q X → Func.wp Γ full_probe_prop_lit_body a m Q X :=
  full_probe_prop_lit_ext_wp Γ hFindRepl hWatchPush hHbrDom hAssignLvl

theorem full_probe_prop_bridge_wp (Γ : Env)
    (hPropLit : ∀ a m Q X, fullProbePropLitSpec a m Q X →
      Γ "full_probe_prop_lit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullProbePropSpec a m Q X → Func.wp Γ full_probe_prop_body a m Q X :=
  full_probe_prop_ext_wp Γ hPropLit

theorem full_probe_flush_hbr_bridge_wp (Γ : Env)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullProbeFlushHbrSpec a m Q X → Func.wp Γ full_probe_flush_hbr_body a m Q X :=
  full_probe_flush_hbr_wp Γ hAddBin hProp

theorem full_probe_assume_pair_bridge_wp (Γ : Env)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProbeProp : ∀ a m Q X, fullProbePropSpec a m Q X →
      Γ "full_probe_prop" [i64] [i64] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X →
      Γ "full_analyze" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hFlushHbr : ∀ a m Q X, fullProbeFlushHbrSpec a m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullProbeAssumePairSpec a m Q X →
      Func.wp Γ full_probe_assume_pair_body a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, hQ⟩
  refine full_probe_assume_pair_wp Γ hAssign hProbeProp (ptBacktrack_adapter hBt)
    (ptAnalyze20_adapter hAna) hProp hFlushHbr hAddUnit _ m Q X
    ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, fun r s' m' h12 h20 hcv hfu hr hm' => ?_⟩
  exact hQ r s' m' h12
    (fun h => let ⟨hu, Fc, ho⟩ := h20 h; ⟨hu, Fc, ptOtfsInvW_to_canon ho⟩)
    hcv hfu hr hm'

theorem full_probe_run_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssumePair : ∀ a m Q X, fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullProbeRunSpec a m Q X → Func.wp Γ full_probe_run_body a m Q X :=
  full_probe_run_wp Γ (ptBacktrack_adapter hBt) (ptAssumePair_adapter hAssumePair)

end Bridges

/-! ## Part 3: Index-verified `SpecEntry.Impl fullEnv` summary (`6` fns) -/

section Summary

private theorem fullFns_nodup : (fullFns.map Fn.name).Nodup := by
  have hchk := full_acyclic
  simp only [fullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem fullSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((fullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (fullSpecTable mainSpec).map SpecEntry.name = fullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (fullSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]
  exact fullFns_nodup

private theorem mkFullEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (fullSpecTable_nodup mainSpec) (hno xs m Q X h)

/-- Canonical `fullFns` / `fullSpecTable` indices of the `6` `ProbeTrans` functions. -/
def fullBridge8aIndices : List Nat :=
  [106, 107, 108, 109, 110, 111]

/-- Index-verified `SpecEntry.Impl (mkFullEnv mainSpec)` summary covering all `6` `ProbeTrans`
functions (`full_hbr_dom`, `full_probe_prop_lit`, `full_probe_prop`, `full_probe_flush_hbr`,
`full_probe_assume_pair`, `full_probe_run`). -/
theorem full_bridge_8a_mk_ok (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ n ∈ fullBridge8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row := by
  let Γ := mkFullEnv mainSpec
  let hWatchPush := mkFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let hAssignLvl := mkFullEnv_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let hAssign := mkFullEnv_row_at (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let hBt := mkFullEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let hFindRepl := mkFullEnv_row_at (mainSpec := mainSpec) 45
    ⟨"full_find_repl", [i64, i64], [i64], fullFindReplSpec, true⟩
  let hProp := mkFullEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let hAna := mkFullEnv_row_at (mainSpec := mainSpec) 82
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  let hAddBin := mkFullEnv_row_at (mainSpec := mainSpec) 98
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let hAddUnit := mkFullEnv_row_at (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let hHbrDom := mkFullEnv_row_at (mainSpec := mainSpec) 106
    ⟨"full_hbr_dom", [i64, i32, i32], [i32], fullHbrDomSpec, true⟩
  let hPropLit := mkFullEnv_row_at (mainSpec := mainSpec) 107
    ⟨"full_probe_prop_lit", [i64, i32], [.bool], fullProbePropLitSpec, true⟩
  let hProbeProp := mkFullEnv_row_at (mainSpec := mainSpec) 108
    ⟨"full_probe_prop", [i64], [i64], fullProbePropSpec, true⟩
  let hFlushHbr := mkFullEnv_row_at (mainSpec := mainSpec) 109
    ⟨"full_probe_flush_hbr", [i64, i64], [i64], fullProbeFlushHbrSpec, true⟩
  let hAssumePair := mkFullEnv_row_at (mainSpec := mainSpec) 110
    ⟨"full_probe_assume_pair", [i64, i32], [i64], fullProbeAssumePairSpec, true⟩
  intro n hn
  simp only [fullBridge8aIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨full_hbr_dom, _, rfl, rfl, .of (full_hbr_dom_bridge_wp Γ)⟩
  · exact ⟨full_probe_prop_lit, _, rfl, rfl,
      .of (full_probe_prop_lit_bridge_wp Γ hFindRepl hWatchPush hHbrDom hAssignLvl)⟩
  · exact ⟨full_probe_prop, _, rfl, rfl, .of (full_probe_prop_bridge_wp Γ hPropLit)⟩
  · exact ⟨full_probe_flush_hbr, _, rfl, rfl,
      .of (full_probe_flush_hbr_bridge_wp Γ hAddBin hProp)⟩
  · exact ⟨full_probe_assume_pair, _, rfl, rfl,
      .of (full_probe_assume_pair_bridge_wp Γ hAssign hProbeProp hBt hAna hProp hFlushHbr hAddUnit)⟩
  · exact ⟨full_probe_run, _, rfl, rfl, .of (full_probe_run_bridge_wp Γ hBt hAssumePair)⟩

/-- Index-verified `SpecEntry.Impl fullEnv` summary covering all `6` `ProbeTrans` functions against
`fullSpecTable fullSolveBytesSpec`. -/
theorem full_bridge_8a_ok :
    ∀ n ∈ fullBridge8aIndices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl fullEnv fn row :=
  full_bridge_8a_mk_ok fullSolveBytesSpec

end Summary

end LeanQbe.T.Examples.Kissat.Full
