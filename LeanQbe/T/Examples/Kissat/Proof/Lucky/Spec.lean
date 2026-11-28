/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Lucky
public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Lucky` (`Proof.Lucky.Spec`)

Canonical flat-`Env` (`SegCert`) UNSAT-sound specifications (`0` legacy imports,
`0` `@[expose]` on theorems/lemmas/sections, `XPost`-polymorphic) for the `4`
functions of `Src.Lucky.fns`:
1. `full_lucky_ord_fid` (`fullLuckyOrdFidSpec`)
2. `full_lucky_scan` (`fullLuckyScanM6Spec`)
3. `full_lucky_polar_m7` (`fullLuckyPolarM7Spec := Proof.Spec.fullLuckyPolarSpec`)
4. `full_lucky_late_m7` (`fullLuckyLateM7Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. External Dependency Table (`deps`) -/

/-- Canonical upstream specification table covering all `extern` callees of
`Src.Lucky` (`Arena`, `Backtrack`, `PropSearch`, `Analyze`). -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++
  PropSearch.Spec.specs ++ Analyze.Spec.specs

/-! ## 2. Function Specifications (`4` fns in `Src.Lucky.fns`) -/

/-- Canonical `SafetySlice` specification for `full_lucky_ord_fid`: collects up to
`s.core.cur_vars` active unassigned variables into `tarjan_reach` while preserving
`FullExtScratchPres`. -/
@[expose] def fullLuckyOrdFidSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (n, ()) s s' => n.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s')

/-- Canonical `FullM6HdrMem`-threaded UNSAT-sound contract for `full_lucky_scan(h, pos, fwd)`. -/
@[expose] def fullLuckyScanM6Spec : Spec [i64, .bool, .bool] [i64] :=
  fun (h, _pos, _fwd, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        s'.LengthsOk c → M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 20#64 → F0.Unsat) →
        (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
        (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical polarity scan specification for `full_lucky_polar_m7(h)`
(reuses `Proof.Spec.fullLuckyPolarSpec`). -/
@[expose] def fullLuckyPolarM7Spec : Spec [i64] [i64] :=
  Proof.Spec.fullLuckyPolarSpec

/-- Canonical `FullM6HdrMem`-threaded UNSAT-sound contract for `full_lucky_late_m7(h)`
(`0`/`2`: level-0 `FullM6HdrInv`; `10`: `extend_len ≤ extend_cap`; `20`: `F0.Unsat`; always
clears `probing = 0#64`). -/
@[expose] def fullLuckyLateM7Spec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        s'.LengthsOk c → M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
        (r = 20#64 → F0.Unsat) →
        (r = 0#64 ∨ r = 2#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
        (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fullLuckyOrdFidSpec_xfree : Spec.XFree fullLuckyOrdFidSpec := by xfree
theorem fullLuckyScanM6Spec_xfree : Spec.XFree fullLuckyScanM6Spec := by xfree
theorem fullLuckyPolarM7Spec_xfree : Spec.XFree fullLuckyPolarM7Spec := by xfree
theorem fullLuckyLateM7Spec_xfree : Spec.XFree fullLuckyLateM7Spec := by xfree

theorem fullLuckyScanM6Spec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {pos fwd : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hsp : FullSparseInv c F0 s)
    (hcl0 : s.core.cur_level = 0) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullLuckyScanM6Spec (c.hdr, pos, fwd, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hcl0, hm, hQ⟩

theorem fullLuckyLateM7Spec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullLuckyLateM7Spec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩

/-! ## 3. Canonical `SpecEntry` Table, Invariants & `Env.Sat.has` Projections -/

/-- Canonical `SpecEntry` table matching `Src.Lucky.fns` `1:1` (`4` rows). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_lucky_ord_fid",   [i64],               [i64], fullLuckyOrdFidSpec,  true⟩
  , ⟨"full_lucky_scan",      [i64, .bool, .bool], [i64], fullLuckyScanM6Spec,  true⟩
  , ⟨"full_lucky_polar_m7",  [i64],               [i64], fullLuckyPolarM7Spec, true⟩
  , ⟨"full_lucky_late_m7",   [i64],               [i64], fullLuckyLateM7Spec,  true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Src.Lucky.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact fullLuckyOrdFidSpec_xfree
  · exact fullLuckyScanM6Spec_xfree
  · exact fullLuckyPolarM7Spec_xfree
  · exact fullLuckyLateM7Spec_xfree

theorem has_full_lucky_ord_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_lucky_ord_fid" fullLuckyOrdFidSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide))
    fullLuckyOrdFidSpec_xfree

theorem has_full_lucky_scan {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_lucky_scan" fullLuckyScanM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide))
    fullLuckyScanM6Spec_xfree

theorem has_full_lucky_polar_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_lucky_polar_m7" fullLuckyPolarM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide))
    fullLuckyPolarM7Spec_xfree

theorem has_full_lucky_late_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_lucky_late_m7" fullLuckyLateM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide))
    fullLuckyLateM7Spec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
