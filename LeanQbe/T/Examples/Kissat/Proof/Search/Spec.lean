/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv1
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Src.Search
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Search` (`Proof.Search.Spec`)

Canonical `SegCert` specifications for all `5` functions in `Src.Search.fns`:
- `full_preprocess_m6` (`fullM6PreprocessSpec`, `FullM6HdrMem`-threaded)
- `full_simplify_m6` (`fullM6SimplifySpec`, `FullM6HdrMem`-threaded)
- `full_search_m6` (`fullM6SearchSpec`, `FullM6HdrMem`-threaded)
- `kissat_solve_bytes_seeded` (`fullM6SolveBytesSeededSpec`)
- `kissat_solve_bytes` (`fullM6SolveBytesCoreModelSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Search.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-- Combined upstream specification table across the `19` `Proof.*.Spec` callees of
`Src.Search.fns` (`165` distinct symbols). -/
@[expose] def deps : List SpecEntry :=
  Internal.Spec.specs ++ Limits.Spec.specs ++ Extend.Spec.specs ++
  Collect.Spec.specs ++ Tiers.Spec.specs ++ Decide.Spec.specs ++
  Restart.Spec.specs ++ Reorder.Spec.specs ++ Walk.Spec.specs ++
  Compact.Spec.specs ++ Backtrack.Spec.specs ++ Reduce.Spec.specs ++
  Analyze.Spec.specs ++ Parse.Spec.specs ++ Dimacs.Spec.specs ++
  Probe.Spec.specs ++ Lucky.Spec.specs ++ Eliminate.Spec.specs ++
  PropSearch.Spec.specs

/-- `M6Hdr`-threaded in-processing simplification specification for `full_simplify_m6`. -/
@[expose] def fullM6SimplifySpec : LeanQbe.T.Spec [i64, .bool, .bool] [i64] :=
  fun (h, _do_probe, _do_elim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
        (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
        ∀ r c' ext' s' m',
          FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
          (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
          s'.core.fuel.toNat ≤ s.core.fuel.toNat →
          (r = 20#64 → F0.Unsat) →
          (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
          (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fullM6SimplifySpec_elim {xs : Tup Val [i64, .bool, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : fullM6SimplifySpec xs m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
        (R : Mem 64 → Prop),
      xs.fst = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
        ∀ r c' ext' s' m',
          FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
          (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
          s'.core.fuel.toNat ≤ s.core.fuel.toNat →
          (r = 20#64 → F0.Unsat) →
          (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
          (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m' := by
  rcases xs with ⟨h, dp, de, ⟨⟩⟩; exact hs

theorem fullM6SimplifySpec_of {dp de : Bool} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullM6SimplifySpec (c.hdr, dp, de, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hk⟩

/-- Seeded end-to-end solver contract mirroring `fullM6SolveBytesCoreModelSpec` for any
initial LCG seed. -/
@[expose] def fullM6SolveBytesSeededSpec :
    LeanQbe.T.Spec [i64, i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, _seed, ()) m Q X =>
    fullM6SolveBytesCoreModelSpec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q X

theorem fullM6PreprocessSpec_xfree : fullM6PreprocessSpec.XFree := by
  intro a m Q X X' h; exact fullM6PreprocessSpec_monoX h

theorem fullM6SimplifySpec_xfree : fullM6SimplifySpec.XFree := by
  intro a m Q X X' h; rcases a with ⟨_, _, _, ⟨⟩⟩; exact h

theorem fullM6SearchSpec_xfree : fullM6SearchSpec.XFree := by
  intro a m Q X X' h; exact fullM6SearchSpec_monoX h

theorem fullM6SolveBytesSeededSpec_xfree : fullM6SolveBytesSeededSpec.XFree := by
  intro a m Q X X' h
  rcases a with ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, seed, ⟨⟩⟩
  dsimp [fullM6SolveBytesSeededSpec] at h ⊢
  exact fullM6SolveBytesCoreModelSpec_monoX h

theorem fullM6SolveBytesCoreModelSpec_xfree : fullM6SolveBytesCoreModelSpec.XFree := by
  intro a m Q X X' h; exact fullM6SolveBytesCoreModelSpec_monoX h

/-- Canonical specification table for `Src.Search.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_preprocess_m6", [i64], [i64], fullM6PreprocessSpec, true⟩
  , ⟨"full_simplify_m6", [i64, .bool, .bool], [i64], fullM6SimplifySpec, true⟩
  , ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩
  , ⟨"kissat_solve_bytes_seeded",
      [i64, i64, i64, i64, i64, i64], [i64], fullM6SolveBytesSeededSpec, true⟩
  , ⟨"kissat_solve_bytes",
      [i64, i64, i64, i64, i64], [i64], fullM6SolveBytesCoreModelSpec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Src.Search.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact fullM6PreprocessSpec_xfree
  · exact fullM6SimplifySpec_xfree
  · exact fullM6SearchSpec_xfree
  · exact fullM6SolveBytesSeededSpec_xfree
  · exact fullM6SolveBytesCoreModelSpec_xfree

theorem has_full_preprocess_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_preprocess_m6" fullM6PreprocessSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide)) fullM6PreprocessSpec_xfree

theorem has_full_simplify_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_simplify_m6" fullM6SimplifySpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide)) fullM6SimplifySpec_xfree

theorem has_full_search_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_search_m6" fullM6SearchSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide)) fullM6SearchSpec_xfree

theorem has_kissat_solve_bytes_seeded {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_solve_bytes_seeded" fullM6SolveBytesSeededSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide))
    fullM6SolveBytesSeededSpec_xfree

theorem has_kissat_solve_bytes {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_solve_bytes" fullM6SolveBytesCoreModelSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide))
    fullM6SolveBytesCoreModelSpec_xfree

theorem has_kissat_solve_bytes_model {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_solve_bytes" fullM6SolveBytesSpec := by
  intro xs m Q X hs
  rcases xs with ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩
  refine has_kissat_solve_bytes h _ m Q X ?_
  exact fullM6SolveBytesCoreModelSpec_of_spec hs

end LeanQbe.T.Examples.Kissat.Proof.Search.Spec
