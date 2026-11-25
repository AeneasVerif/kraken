module

public import LeanQbe.T.Unified.Core
public import LeanQbe.T.Main
public import LeanQbe.T.Dce
import LeanQbe.T.OptLemmas
import LeanQbe.T.DceLemmas
import LeanQbe.T.LegalMemLemmas
import LeanQbe.T.LegalWfOpsLemmas
import LeanQbe.T.MainLemmas

/-!
# Shared SSA Tier (`Unified.Ssa`)

Instantiates `Unified.Tier` on `LeanQbe.T.Fn` / `Fn.Wf` / `Func.spec` and connects the production
mid-end passes behind the module-system proof firewall (`import` of `*Lemmas` stays private):

* `SSpec`, `ssa`, `ssaPass`.
* `optP`, `earlyOptP`, `lateOptP`, `dceP`, `midEarly`.
* `legalTr`, `legalStage`, `midEndFine`, and production `midEnd` (`Fn.mid` via `fn_mid_wf` /
  `fn_mid_spec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T

/-- Signature-indexed contract family plus callee environment for the SSA tier. -/
structure SSpec : Type 1 where
  Γ : Env
  C : (as rs : List Ty) → Spec as rs

/-- The shared SSA tier: every SSA frontend lowers here. -/
@[expose] def ssa : Tier.{1, 1} where
  Prog := Fn
  Ok := Fn.Wf
  Spec := SSpec
  top := ⟨fun _ _ _ _ _ _ _ => False, fun _ _ _ _ _ _ => False⟩
  Sat fn s := ∀ xs m Q X, s.C fn.as fn.rs xs m Q X → Func.spec s.Γ fn.body xs m Q X

/-- Adapter turning any `(f, f_wf, f_spec)` triple into a `Pass ssa`. -/
@[expose] def ssaPass (f : ∀ {as rs : List Ty}, Func as rs → Func as rs)
    (hwf : ∀ {as rs : List Ty} {g : Func as rs}, g.Wf → (f g).Wf)
    (hsp : ∀ {as rs : List Ty} {g : Func as rs}, g.Wf → ∀ {Γ : Env} {xs : Tup Val as}
      {m : Mem 64} {Q : Post rs} {X : XPost}, Func.spec Γ g xs m Q X →
      Func.spec Γ (f g) xs m Q X) : Pass ssa where
  run fn := ⟨fn.name, fn.as, fn.rs, f fn.body⟩
  ok _ h := hwf h
  sound _ _ h hs xs m Q X hC := hsp h (hs xs m Q X hC)

theorem ssa_opt_wf {as rs : List Ty} {g : Func as rs} (h : g.Wf) :
    (Func.opt g).Wf :=
  Func.opt_wf h

theorem ssa_opt_spec {as rs : List Ty} {g : Func as rs} (h : g.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hs : Func.spec Γ g xs m Q X) : Func.spec Γ (Func.opt g) xs m Q X :=
  Func.opt_spec h hs

theorem ssa_earlyOpt_wf {as rs : List Ty} {g : Func as rs} (h : g.Wf) :
    (Func.earlyOpt g).Wf :=
  Func.earlyOpt_wf h

theorem ssa_earlyOpt_spec {as rs : List Ty} {g : Func as rs} (h : g.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hs : Func.spec Γ g xs m Q X) : Func.spec Γ (Func.earlyOpt g) xs m Q X :=
  Func.earlyOpt_spec h hs

theorem ssa_lateOpt_wf {as rs : List Ty} {g : Func as rs} (h : g.Wf) :
    (Func.lateOpt g).Wf :=
  Func.lateOpt_wf h

theorem ssa_lateOpt_spec {as rs : List Ty} {g : Func as rs} (h : g.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hs : Func.spec Γ g xs m Q X) : Func.spec Γ (Func.lateOpt g) xs m Q X :=
  Func.lateOpt_spec h hs

theorem ssa_dce_wf {as rs : List Ty} {g : Func as rs} (h : g.Wf) :
    (Func.dce g).Wf :=
  Func.dce_wf h

theorem ssa_dce_spec {as rs : List Ty} {g : Func as rs} (h : g.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hs : Func.spec Γ g xs m Q X) : Func.spec Γ (Func.dce g) xs m Q X :=
  Func.dce_spec h hs

@[expose] def optP : Pass ssa := ssaPass Func.opt ssa_opt_wf ssa_opt_spec
@[expose] def earlyOptP : Pass ssa := ssaPass Func.earlyOpt ssa_earlyOpt_wf ssa_earlyOpt_spec
@[expose] def lateOptP : Pass ssa := ssaPass Func.lateOpt ssa_lateOpt_wf ssa_lateOpt_spec
@[expose] def dceP : Pass ssa := ssaPass Func.dce ssa_dce_wf ssa_dce_spec

/-- Shared pre-`Legal` mid-end pass sequence. -/
@[expose] def midEarly : Pass ssa := Pass.seq [earlyOptP, optP]

/-- Translated contract after `Legal`: arguments/results are re-encoded by `encodeTup`. -/
@[expose] def legalTr (t : LegalTarget) (fn : Fn) (s : SSpec) : SSpec where
  Γ := legalEnv t s.Γ
  C as' rs' ys m Q' X' :=
    ∃ (h₁ : t.legalSig fn.as = as') (h₂ : t.legalSig fn.rs = rs') (xs : Tup Val fn.as)
      (Q : Post fn.rs) (X : XPost), s.C fn.as fn.rs xs m Q X ∧
      cast (congrArg (Tup Val) h₁) (encodeTup t fn.as xs) = ys ∧
      cast (congrArg Post h₂) (legalPost t Q) = Q' ∧ legalXPost t X = X'

theorem legalStage_ok (t : LegalTarget) (fn q : Fn) (hf : ssa.Ok fn)
    (h : (if fn.body.supportsSource t then Except.ok (fn.legal t)
      else Except.error "legal: unsupported") = .ok q) : ssa.Ok q := by
  by_cases hs : fn.body.supportsSource t = true
  · simp only [hs, ↓reduceIte] at h; cases h; exact Fn.legal_wf t hf
  · simp [hs] at h

theorem legalStage_sound (t : LegalTarget) (fn q : Fn) (s : SSpec) (hf : ssa.Ok fn)
    (h : (if fn.body.supportsSource t then Except.ok (fn.legal t)
      else Except.error "legal: unsupported") = .ok q) (hsat : ssa.Sat fn s) :
    ssa.Sat q (legalTr t fn s) := by
  by_cases hs : fn.body.supportsSource t = true
  · simp only [hs, ↓reduceIte] at h
    cases h
    rintro ys m Q' X' ⟨h₁, h₂, xs, Q, X, hC, rfl, rfl, rfl⟩
    exact Fn.legal_spec t fn hf hs s.Γ xs m Q X (hsat xs m Q X hC)
  · simp [hs] at h

/-- `Legal` as a shared, checked, signature-changing `Stage`. -/
@[expose] def legalStage (t : LegalTarget) : Stage ssa ssa where
  run fn := if fn.body.supportsSource t then .ok (fn.legal t) else .error "legal: unsupported"
  tr := legalTr t
  ok := legalStage_ok t
  sound := legalStage_sound t

/-- Fine-grained mid-end assembled from `midEarly`, `legalStage`, `lateOptP`, and `dceP`. -/
@[expose] def midEndFine (t : LegalTarget) : Stage ssa ssa :=
  midEarly.toStage ≫ legalStage t ≫ (Pass.seq [lateOptP, dceP]).toStage

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

/-- The production mid-end shared by every SSA frontend: exactly `Fn.mid t`. -/
@[expose] def midEnd (t : LegalTarget) : Stage ssa ssa where
  run fn := if (fn.earlyOpt).body.supportsSource t then .ok (fn.mid t)
    else .error "mid: unsupported"
  tr := legalTr t
  ok := midEnd_ok t
  sound := midEnd_sound t

end LeanQbe.T.Unified
