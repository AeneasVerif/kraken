/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Float64
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Float64` (`Kissat.Proof.Float64.Spec`)

Single canonical `Spec` per function of `Src.Float64.fns` (`14` functions, `0` externs):
1. Pure 1-arg / 2-arg soft-float contracts (`f64uPure1Spec`, `f64uPure2Spec`), bounded MSB contract
   (`f64uMsb64Spec`), and 128-bit multiply contract (`u64Mul128Spec`).
2. `m6_wm4_get` read-only contract (`m6Wm4GetSpec`, preserving `FullM6HdrMem c ext s` verbatim)
   and `m6_wm4_set` reuse of canonical `Proof.Spec.m6HdrW2aSpec [i64] []`.
3. `Spec.XFree` proofs (`by xfree`), `.Le` / `Env.Has` weakenings (`f64uPure1Spec_le_msb64`,
   `m6HdrW2a_le_m6Wm4Get`), `specs` table matching `Src.Float64.fns` 1:1, and `specs_sigs`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Float64.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Float64

@[expose] public section

/-- Pure memory-preserving contract for 1-arg `f64u_*` soft-float helpers. -/
def f64uPure1Spec : Spec [i64] [i64] :=
  fun _ m Q _ => ∀ r : BitVec 64, Q (r, ()) m

/-- Pure memory-preserving contract for 2-arg `f64u_*` soft-float helpers. -/
def f64uPure2Spec : Spec [i64, i64] [i64] :=
  fun _ m Q _ => ∀ r : BitVec 64, Q (r, ()) m

/-- Bounded `f64u_msb64(x)` contract: pure, and when `x ≠ 0#64` returns true MSB index `< 64`. -/
def f64uMsb64Spec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ =>
    ∀ r : BitVec 64,
      (x ≠ 0#64 → r.toNat < 64 ∧ 2 ^ r.toNat ≤ x.toNat ∧ x.toNat < 2 ^ (r.toNat + 1)) →
      Q (r, ()) m

/-- Pure memory-preserving contract for `u64_mul128(a, b)` returning `(lo, hi)`. -/
def u64Mul128Spec : Spec [i64, i64] [i64, i64] :=
  fun _ m Q _ => ∀ lo hi : BitVec 64, Q (lo, hi, ()) m

/-- Pure read-only contract for `m6_wm4_get(h)`: preserves `FullM6HdrMem c ext s` verbatim. -/
def m6Wm4GetSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r : BitVec 64, (FullM6HdrMem c ext s ⋆ R) m → Q (r, ()) m

/-- Canonical `14`-row specification table aligned 1:1 with `Src.Float64.fns`. -/
def specs : List SpecEntry :=
  [ ⟨"f64u_msb64",     [i64],      [i64],      f64uMsb64Spec,       true⟩
  , ⟨"f64u_round_pack",[i64, i64], [i64],      f64uPure2Spec,       true⟩
  , ⟨"f64u_add",       [i64, i64], [i64],      f64uPure2Spec,       true⟩
  , ⟨"f64u_sub",       [i64, i64], [i64],      f64uPure2Spec,       true⟩
  , ⟨"f64u_mul",       [i64, i64], [i64],      f64uPure2Spec,       true⟩
  , ⟨"f64u_div",       [i64, i64], [i64],      f64uPure2Spec,       true⟩
  , ⟨"f64u_inv_u64",   [i64],      [i64],      f64uPure1Spec,       true⟩
  , ⟨"f64u_from_u64",  [i64],      [i64],      f64uPure1Spec,       true⟩
  , ⟨"f64u_to_u64",    [i64],      [i64],      f64uPure1Spec,       true⟩
  , ⟨"u64_mul128",     [i64, i64], [i64, i64], u64Mul128Spec,       true⟩
  , ⟨"f64u_log10_u64", [i64],      [i64],      f64uPure1Spec,       true⟩
  , ⟨"f64u_nlogpown",  [i64, i64], [i64],      f64uPure2Spec,       true⟩
  , ⟨"m6_wm4_get",     [i64],      [i64],      m6Wm4GetSpec,        true⟩
  , ⟨"m6_wm4_set",     [i64, i64], [],         m6HdrW2aSpec [i64] [], true⟩
  ]

end

public section

theorem f64uPure1Spec_xfree : Spec.XFree f64uPure1Spec := by xfree
theorem f64uPure2Spec_xfree : Spec.XFree f64uPure2Spec := by xfree
theorem f64uMsb64Spec_xfree : Spec.XFree f64uMsb64Spec := by xfree
theorem u64Mul128Spec_xfree : Spec.XFree u64Mul128Spec := by xfree
theorem m6Wm4GetSpec_xfree : Spec.XFree m6Wm4GetSpec := by xfree
theorem m6Wm4SetSpec_xfree : Spec.XFree (m6HdrW2aSpec [i64] []) :=
  fun _ _ _ _ _ h => m6HdrW2aSpec_monoX h

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact f64uMsb64Spec_xfree
  · exact f64uPure2Spec_xfree
  · exact f64uPure2Spec_xfree
  · exact f64uPure2Spec_xfree
  · exact f64uPure2Spec_xfree
  · exact f64uPure2Spec_xfree
  · exact f64uPure1Spec_xfree
  · exact f64uPure1Spec_xfree
  · exact f64uPure1Spec_xfree
  · exact u64Mul128Spec_xfree
  · exact f64uPure1Spec_xfree
  · exact f64uPure2Spec_xfree
  · exact m6Wm4GetSpec_xfree
  · exact m6Wm4SetSpec_xfree

theorem f64uPure1Spec_le_msb64 : f64uPure1Spec.Le f64uMsb64Spec := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ r _; exact hQ r

theorem has_f64uMsb64_to_pure {Γ : Env} (h : Γ.Has "f64u_msb64" f64uMsb64Spec) :
    Γ.Has "f64u_msb64" f64uPure1Spec :=
  h.of_le f64uPure1Spec_le_msb64

theorem m6HdrW2a_le_m6Wm4Get : (m6HdrW2aSpec [] [i64]).Le m6Wm4GetSpec := by
  rintro ⟨h, ⟨⟩⟩ m Q X hW
  obtain ⟨c, ext, s, R, hc, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hW
  exact ⟨c, ext, s, R, hc, hcfg, hext, hlen, hm, fun r hm' =>
    hQ (r, ()) ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm'⟩

theorem has_m6Wm4Get_to_w2a {Γ : Env} (h : Γ.Has "m6_wm4_get" m6Wm4GetSpec) :
    Γ.Has "m6_wm4_get" (m6HdrW2aSpec [] [i64]) :=
  h.of_le m6HdrW2a_le_m6Wm4Get

theorem specs_sigs : specs.map SpecEntry.sig = Src.Float64.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

end

end LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
