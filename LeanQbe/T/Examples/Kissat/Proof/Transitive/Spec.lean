/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Transitive
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Transitive` (`Proof.Transitive.Spec`)

Canonical `SegCert` specifications for all `3` functions in `Src.Transitive.fns`:
- `full_trans_lit_m6` (`fullTransLitM6Spec`, `FullMem`)
- `full_trans_sort_m6` (`fullTransSortM6Spec`, `FullMem`)
- `full_transitive_m6` (`fullTransitiveM6Spec`, Step-13 Option-A `FullM6HdrMem`-threaded)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Transitive
open Kraken.Bedrock2.Test

/-- Canonical spec for `full_trans_lit_m6(h, src, stop_early)`. -/
@[expose] def fullTransLitM6Spec : Spec [i64, i32, .bool] [.bool] :=
  fun (h, src, _stop_early, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧
      src.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
        FullSparseInv c F0 s' → s'.core.cur_level = 0 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical spec for `full_trans_sort_m6(h, n)` (Shell sort of `work_stk1[0..<n)`). -/
@[expose] def fullTransSortM6Spec : Spec [i64, i64] [] :=
  fun (h, n, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ n.toNat ≤ s.core.cur_vars ∧
      (∀ i < n.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ws1' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
        ws1'.length = 2 * c.max_vars → FullSparseInv c F0 s' →
        (∀ i < n.toNat, (ws1'[i]?.getD 0#32).toNat < s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 Option-A `FullM6HdrMem`-threaded spec for `full_transitive_m6(h, tick_lim)`. -/
@[expose] def fullTransitiveM6Spec : Spec [i64, i64] [i64] :=
  fun (h, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInv c F0 s' →
        (s.core.cur_level = 0 → s'.core.cur_level = 0) →
        s'.core.probing = s.core.probing →
        (s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Direct dependency spec table for `Src.Transitive`. -/
@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Clause.Spec.specs ++ PropSearch.Spec.specs ++ Watch.Spec.specs

/-- Canonical exported specification rows matching `Src.Transitive.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_trans_lit_m6", [i64, i32, .bool], [.bool], fullTransLitM6Spec, true⟩
  , ⟨"full_trans_sort_m6", [i64, i64], [], fullTransSortM6Spec, true⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64], fullTransitiveM6Spec, true⟩
  ]

theorem specs_sigs : specs.map SpecEntry.sig = fns.map Fn.sig := by decide

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ specs, e.noExit = true := by decide

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> xfree

theorem has_full_trans_lit_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_trans_lit_m6" fullTransLitM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide)) (by xfree)

theorem has_full_trans_sort_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_trans_sort_m6" fullTransSortM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide)) (by xfree)

theorem has_full_transitive_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_transitive_m6" fullTransitiveM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide)) (by xfree)

end LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
