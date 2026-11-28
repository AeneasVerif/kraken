/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Src.Learn
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpOneLitHelpers
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpOneLitBin
import LeanQbe.T.Examples.Kissat.Proof.Learn.WpOneLitLarge

/-!
# WP Proof for `full_one_lit_confl` (`Proof.Learn.WpOneLit`)

Dispatches binary (`confl_type == 1`) vs large-clause (`confl_type != 1`) branches cleanly to
`oneLit_bin_branch_wp` and `oneLit_large_branch_wp` against `Spec.oneLitConflSpec`
(`0` legacy imports, `0` `@[expose]` on theorems/sections, `<= 100` cols).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Learn

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Learn
open Kraken.Bedrock2.Test

public section

/-- Canonical WP proof for `full_one_lit_confl` against `Spec.oneLitConflSpec`. -/
theorem full_one_lit_confl_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hDet : ∀ args m Q X, Spec.detNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hUnw : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, Spec.oneLitConflSpec args m Q X →
      Func.wp Γ full_one_lit_confl_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨F0, F_cur, cut⟩, R, rfl, _, ⟨hcutInv, hconfl⟩, hm, hQ⟩ := FullContract.elim hs
  obtain ⟨hlen, hw, hmarks, hnd, hext, hdm⟩ := hcutInv
  have hQ' : OneLitPost c F0 F_cur s R Q :=
    fun r s' m' hlen' hr hcv hfu hws2 hdm' _ hmk' hnd' hext' _ h20 h1 h2 h0 hm' =>
      hQ (r, ()) s' m' hlen'
        ⟨hr, hcv, hfu, hws2,
         (fun h20r => let ⟨hu, heq⟩ := h20 h20r
           ⟨hu, heq ▸ ⟨hlen, hw.toFullOtfsWitnessInv, hmarks, hnd, hext, hdm⟩,
             by rw [heq]; exact Nat.le_refl _, by rw [heq]⟩),
         (fun h1r => let ⟨hw', hlt⟩ := h1 h1r
           ⟨⟨hlen', hw', hmk', hnd', hext', hdm'⟩, hlt⟩),
         (fun h2r => ⟨hlen', h2 h2r, hmk', hnd', hext', hdm'⟩),
         (fun h0r => let ⟨cut', hcut'le, hw', hpos, hle, hcf'⟩ := h0 h0r
           ⟨cut', hcut'le, ⟨hlen', hw', hmk', hnd', hext', hdm'⟩, hpos, hle, hcf'⟩)⟩
        hm'
  by_cases hbin : s.core.confl_type = 1#64
  · exact oneLit_bin_branch_wp Γ hDet hBt hAss hlen hdm hw hmarks hnd hext hconfl hbin hm hQ'
  · exact oneLit_large_branch_wp Γ hDefrag hDet hBt hAss hUnw hPush hlen hdm hw hmarks hnd
      hext hw.cut_le hconfl hbin hm hQ'

end

end LeanQbe.T.Examples.Kissat.Proof.Learn
