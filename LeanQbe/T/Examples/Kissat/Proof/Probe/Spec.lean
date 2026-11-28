/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Probe
public import LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Probe` (`Proof.Probe.Spec`)

Canonical flat-`Env` (`SegCert`) UNSAT-sound specifications (`0` legacy imports,
`0` `@[expose]` on theorems/lemmas/sections, `XPost`-polymorphic) for the `2`
functions of `Src.Probe.fns`:
1. `full_probe_dticks_m6_hdr` (`fullProbeDticksM6HdrSpec := m6HdrW2aSpec [.bool] [i64]`)
2. `full_probe_m6` (`fullProbeM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Probe.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. External Dependency Table (`deps`) -/

/-- Canonical upstream specification table covering all `extern` callees of
`Src.Probe`. -/
@[expose] def deps : List SpecEntry :=
  Tiers.Spec.specs ++ Internal.Spec.specs ++ Dense.Spec.specs ++
  Congruence.Spec.specs ++ Forward.Spec.specs ++ Substitute.Spec.specs ++
  Backbone.Spec.specs ++ Sweep.Spec.specs ++ Factor.Spec.specs ++
  Vivify.Spec.specs ++ Transitive.Spec.specs ++ Float64.Spec.specs ++
  Limits.Spec.specs

/-! ## 2. Function Specifications (`2` fns in `Src.Probe.fns`) -/

/-- Canonical `FullM6HdrMem` specification for `full_probe_dticks_m6_hdr`. -/
@[expose] def fullProbeDticksM6HdrSpec : Spec [i64, .bool] [i64] :=
  m6HdrW2aSpec [.bool] [i64]

/-- Canonical `FullM6HdrMem`-threaded UNSAT-sound contract for
`full_probe_m6(h, initial)` (`1`: done at level 0; `20`: `F0.Unsat`). -/
@[expose] def fullProbeM6Spec : Spec [i64, .bool] [i64] :=
  fun (h, _initial, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        s'.LengthsOk c → M6HdrExtOk ext' →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fullProbeDticksM6HdrSpec_xfree : Spec.XFree fullProbeDticksM6HdrSpec :=
  fun _ _ _ _ _ h => m6HdrW2aSpec_monoX h

theorem fullProbeM6Spec_xfree : Spec.XFree fullProbeM6Spec := by xfree

theorem fullProbeM6Spec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {initial : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullProbeM6Spec (c.hdr, initial, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem fullProbeM6Spec_elim {h : BitVec 64} {initial : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : fullProbeM6Spec (h, initial, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        s'.LengthsOk c → M6HdrExtOk ext' →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
  hs

/-! ## 3. Canonical `SpecEntry` Table, Invariants & `Env.Sat.has` Projections -/

/-- Canonical `SpecEntry` table matching `Src.Probe.fns` `1:1` (`2` rows). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64],
      fullProbeDticksM6HdrSpec, true⟩
  , ⟨"full_probe_m6", [i64, .bool], [i64], fullProbeM6Spec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Src.Probe.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact fullProbeDticksM6HdrSpec_xfree
  · exact fullProbeM6Spec_xfree

theorem has_full_probe_dticks_m6_hdr {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_probe_dticks_m6_hdr" fullProbeDticksM6HdrSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide))
    fullProbeDticksM6HdrSpec_xfree

theorem has_full_probe_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_probe_m6" fullProbeM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide))
    fullProbeM6Spec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
