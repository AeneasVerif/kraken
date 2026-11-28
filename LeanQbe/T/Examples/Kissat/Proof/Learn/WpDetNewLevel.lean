/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Src.Learn
import LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# WP Proof for `full_det_new_level` (`Proof.Learn.WpDetNewLevel`)

Proves `full_det_new_level_wp` against canonical `Proof.Spec.fullDetNewLevelSpec` (`0` legacy
imports, `0` `@[expose]` on theorems/sections).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Learn

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Learn
open LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Learn.Helpers

private theorem bv64_sub1_toNat' {f : BitVec 64} (h : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hp : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 => h (BitVec.eq_of_toNat_eq h0)
  bv_omega

public section

theorem full_det_new_level_wp (Γ : Env) :
    ∀ args m Q X, Proof.Spec.fullDetNewLevelSpec args m Q X →
      Func.wp Γ full_det_new_level_body args m Q X := by
  rintro ⟨h, jump, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl_lt, hm, hQ⟩
  unfold Func.wp full_det_new_level_body
  c0_hsteps
  · have h0 : s.core.cur_level = 0 := ofNat64_eq_zero hcl_lt ‹_›
    exact hQ 0#64 (fun _ => rfl) (fun hpos => by omega)
  · have hpos : 0 < s.core.cur_level := ofNat64_pos ‹_›
    exact hQ jump (fun h0 => by omega) (fun _ hlt => ⟨Nat.le_refl _, hlt⟩)
  · have hpos : 0 < s.core.cur_level := ofNat64_pos ‹_›
    have hsub1 : (BitVec.ofNat 64 s.core.cur_level - 1).toNat = s.core.cur_level - 1 := by
      simpa [Proof.Spec.bv64_ofNat_toNat hcl_lt] using
        bv64_sub1_toNat' (f := BitVec.ofNat 64 s.core.cur_level) ‹_›
    exact hQ (BitVec.ofNat 64 s.core.cur_level - 1) (fun h0 => by omega)
      (fun _ _ => by rw [hsub1]; constructor <;> omega)
  · have hpos : 0 < s.core.cur_level := ofNat64_pos ‹_›
    exact hQ jump (fun h0 => by omega) (fun _ hlt => ⟨Nat.le_refl _, hlt⟩)

end

end LeanQbe.T.Examples.Kissat.Proof.Learn
