module

public import LeanQbe.T.Main
import LeanQbe.T.MainLemmas

/-!
# Shared SSA Tier (`Unified.Ssa`)

Provides `SSpec`, `ssa`, `legalTr`, `midEnd_ok`, and `midEnd_sound` over `LeanQbe.T.Fn` /
`Fn.Wf` / `Func.spec` behind the module-system proof firewall (`import LeanQbe.T.MainLemmas` stays
private) for `Unified.CfgRecovery*` and `Unified.CfgContify*`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T

universe u v

/-- An IR tier: programs, well-formedness `Ok`, specs (with `top`), and satisfaction `Sat`. -/
structure Tier : Type (max (u + 1) (v + 1)) where
  Prog : Type u
  Ok : Prog → Prop
  Spec : Type v
  top : Spec
  Sat : Prog → Spec → Prop

/-- Signature-indexed contract family plus callee environment for the SSA tier. -/
structure SSpec : Type 1 where
  Γ : Env
  C : (as rs : List Ty) → Spec as rs

/-- The shared SSA tier over `LeanQbe.T.Fn` / `Fn.Wf` / `Func.spec`. -/
@[expose] def ssa : Tier.{1, 1} where
  Prog := Fn
  Ok := Fn.Wf
  Spec := SSpec
  top := ⟨fun _ _ _ _ _ _ _ => False, fun _ _ _ _ _ _ => False⟩
  Sat fn s := ∀ xs m Q X, s.C fn.as fn.rs xs m Q X → Func.spec s.Γ fn.body xs m Q X

/-- Translated contract after `Legal`: arguments/results are re-encoded by `encodeTup`. -/
@[expose] def legalTr (t : LegalTarget) (fn : Fn) (s : SSpec) : SSpec where
  Γ := legalEnv t s.Γ
  C as' rs' ys m Q' X' :=
    ∃ (h₁ : t.legalSig fn.as = as') (h₂ : t.legalSig fn.rs = rs') (xs : Tup Val fn.as)
      (Q : Post fn.rs) (X : XPost), s.C fn.as fn.rs xs m Q X ∧
      cast (congrArg (Tup Val) h₁) (encodeTup t fn.as xs) = ys ∧
      cast (congrArg Post h₂) (legalPost t Q) = Q' ∧ legalXPost t X = X'

theorem midEnd_ok (t : LegalTarget) (fn q : Fn) (hf : ssa.Ok fn)
    (h : (if (fn.earlyOpt).body.supportsSource t then Except.ok (fn.mid t)
      else Except.error "mid: unsupported") = .ok q) : ssa.Ok q := by
  by_cases hs : (fn.earlyOpt).body.supportsSource t = true
  · simp only [hs, ↓reduceIte] at h; cases h; exact fn_mid_wf hf
  · simp [hs] at h

theorem midEnd_sound (t : LegalTarget) (fn q : Fn) (s : SSpec) (hf : ssa.Ok fn)
    (h : (if (fn.earlyOpt).body.supportsSource t then Except.ok (fn.mid t)
      else Except.error "mid: unsupported") = .ok q) (hsat : ssa.Sat fn s) :
    ssa.Sat q (legalTr t fn s) := by
  by_cases hs : (fn.earlyOpt).body.supportsSource t = true
  · simp only [hs, ↓reduceIte] at h
    cases h
    rintro ys m Q' X' ⟨h₁, h₂, xs, Q, X, hC, rfl, rfl, rfl⟩
    exact fn_mid_spec hf hs s.Γ rfl (fun _ _ hq => hq) (fun _ _ _ _ hx => hx)
      (hsat xs m Q X hC)
  · simp [hs] at h

end LeanQbe.T.Unified
