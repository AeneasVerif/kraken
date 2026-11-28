/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Decide
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Decide.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Decide.Wp1
import LeanQbe.T.Examples.Kissat.Proof.Decide.Wp2

/-!
# Canonical Segment Certificate for `Kissat.Src.Decide` (`Proof.Decide.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and establishes
`cert : SegCert deps Src.Decide.fns Spec.specs` using `CanonicalEnv`
(`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Decide

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Decide
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Decide.Spec

/-- Upstream capability dependencies for `Src.Decide`. -/
@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Float64.Spec.specs ++ Heap.Spec.specs ++
  Limits.Spec.specs ++ Tiers.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Decide.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

private theorem nextDecVarSpec_xfree : Spec.nextDecVarSpec.XFree := by
  unfold Spec.nextDecVarSpec; exact FullContract.toSpec_xfree _

private theorem randecVarLvlSpec_xfree : Spec.randecVarLvlSpec.XFree := by
  unfold Spec.randecVarLvlSpec; exact FullContract.toSpec_xfree _

private theorem randecVarSpec_xfree : Spec.randecVarSpec.XFree := by
  unfold Spec.randecVarSpec; exact FullContract.toSpec_xfree _

private theorem decideCoreSpec_xfree : Spec.decideCoreSpec.XFree := by
  unfold Spec.decideCoreSpec; exact FullContract.toSpec_xfree _

/-- Canonical segment certificate for `Kissat.Src.Decide` (`5` functions). -/
theorem cert : SegCert deps Src.Decide.fns Spec.specs := by
  intro Γ hdeps hSat
  have hBk : Γ.Sat Backtrack.Spec.specs := hdeps.left.left.left.left
  have hFl : Γ.Sat Float64.Spec.specs := hdeps.left.left.left.right
  have hHp : Γ.Sat Heap.Spec.specs := hdeps.left.left.right
  have hLim : Γ.Sat Limits.Spec.specs := hdeps.left.right
  have hTr : Γ.Sat Tiers.Spec.specs := hdeps.right
  have hAssign := Backtrack.Spec.has_full_assign hBk
  have hPop := Heap.Spec.has_full_heap_pop hHp
  have hDrInit := Tiers.Spec.has_m6_hdr_dr_init hTr
  have hMul := SpecTable.has_at hFl 4 rfl f64uPure2Spec_xfree
  have hTo := SpecTable.has_at hFl 8 rfl f64uPure1Spec_xfree
  have hLog := SpecTable.has_at hFl 10 rfl f64uPure1Spec_xfree
  have hLcg := SpecTable.has_at hLim 10 rfl m7LcgNextSpec_xfree
  have hGet64 := SpecTable.has_at hLim 11 rfl m7Get64Spec_xfree
  have hSet64 := SpecTable.has_at hLim 12 rfl m7Set64Spec_xfree
  have hInit := SpecTable.has_at hLim 13 rfl step13M7StateInitSpec_xfree
  have hNextDec := SpecTable.has_at hSat 0 rfl nextDecVarSpec_xfree
  have hRandecLvl := SpecTable.has_at hSat 1 rfl randecVarLvlSpec_xfree
  have hRandec := SpecTable.has_at hSat 2 rfl randecVarSpec_xfree
  have hDecide := SpecTable.has_at hSat 3 rfl decideCoreSpec_xfree
  exact
    ⟨ SpecEntry.Impl.of (full_next_dec_var_wp Γ hPop)
    , SpecEntry.Impl.of (full_randec_var_lvl_fid_wp Γ hInit hGet64 hSet64 hLog hMul hTo hLcg)
    , SpecEntry.Impl.of (full_randec_var_m7_wp Γ hRandecLvl)
    , SpecEntry.Impl.of (full_decide_m7_wp Γ hRandec hNextDec hAssign)
    , SpecEntry.Impl.of (m6_hdr_decide_fid_wp Γ hDecide hDrInit)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Decide
