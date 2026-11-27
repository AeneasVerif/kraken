/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.OptFlatPlanKit

/-!
# `OptFlatSimKit`: Shared Simulation Combinators & Corollary Helpers for `OptFlat*`

Provides reusable proof combinators, tuple/context lemmas, pipeline stage composition,
and corollary macros shared across `OptFlat*Lemmas*.lean` and `MainFlatLemmas.lean`:

1. Context and tuple-freshness bridge lemmas (`listGet?_append_self`,
   `tupFreshWith_*_eq_mkFreshTup`, `tupMap_levels_eq_mkFreshTup`,
   `trieCtxMatch_singleton`, `trieRelMatch_singleton`).
2. `FlatStage` pipeline composition and corollary helpers/macros (`flat_pass_corollaries`).
3. `klSim_mutual` and `StdKLSpec` / `stdKLSim_mutual` for `(W, KL)` forward passes.
4. `relSim_mutual` for custom-label forward passes.
5. `scanSim_mutual` for level-indexed scans and plan validators.
-/

namespace LeanQbe.T.OptFlatSimKit

open LeanQbe.T
open LeanQbe.T.OptFlatPlanKit

public section

/-! ## 1. List, Tuple, and Context Bridge Lemmas -/

theorem listGet?_append_self {α : Type} (l₁ : List α) (x : α) (l₂ : List α) :
    listGet? (l₁ ++ x :: l₂) l₁.length = some x := by
  have h := PassFlatKit.listGet?_append_right l₁ (ys := x :: l₂) 0
  dsimp only [listGet?] at h
  simpa only [Nat.add_zero] using h

theorem tupFreshWith_const_eq_mkFreshTup {W : Ty → Type}
    (f : {t : Ty} → K t → Nat → W t) (mkW : (t : Ty) → Nat → Nat → W t)
    (hmk : ∀ t inD outD n, f (t := t) (outD : K t) n = mkW t inD outD) :
    ∀ (ts : List Ty) (inD outD n : Nat),
      tupFreshWith f ts (Tup.levels ts outD) n = OptFlatPlanKit.mkFreshTup mkW ts inD outD
  | [], _, _, _ => rfl
  | t :: ts, inD, outD, n => by
    dsimp only [Tup.levels, tupFreshWith, OptFlatPlanKit.mkFreshTup]
    rw [hmk t inD outD n,
      tupFreshWith_const_eq_mkFreshTup f mkW hmk ts (inD + 1) (outD + 1) (n + 1)]

theorem tupFreshWith_pair_eq_mkFreshTup {W : Ty → Type}
    (f : {t : Ty} → K t → Nat → W t) (mkW : (t : Ty) → Nat → Nat → W t)
    (hmk : ∀ t inD outD, f (t := t) (outD : K t) inD = mkW t inD outD) :
    ∀ (ts : List Ty) (inD outD : Nat),
      tupFreshWith f ts (Tup.levels ts outD) inD = OptFlatPlanKit.mkFreshTup mkW ts inD outD
  | [], _, _ => rfl
  | t :: ts, inD, outD => by
    dsimp only [Tup.levels, tupFreshWith, OptFlatPlanKit.mkFreshTup]
    rw [hmk t inD outD,
      tupFreshWith_pair_eq_mkFreshTup f mkW hmk ts (inD + 1) (outD + 1)]

theorem tupFreshWith_self_eq_mkFreshTup {W : Ty → Type}
    (f : {t : Ty} → K t → Nat → W t) (mkW : (t : Ty) → Nat → Nat → W t)
    (hmk : ∀ t inD outD, f (t := t) (outD : K t) outD = mkW t inD outD) :
    ∀ (ts : List Ty) (inD outD : Nat),
      tupFreshWith f ts (Tup.levels ts outD) outD = OptFlatPlanKit.mkFreshTup mkW ts inD outD
  | [], _, _ => rfl
  | t :: ts, inD, outD => by
    dsimp only [Tup.levels, tupFreshWith, OptFlatPlanKit.mkFreshTup]
    rw [hmk t inD outD,
      tupFreshWith_self_eq_mkFreshTup f mkW hmk ts (inD + 1) (outD + 1)]

theorem insertTupEnv_mkFreshTup_eq_insertFreshWith {W : Ty → Type}
    (mkW : (t : Ty) → Nat → Nat → W t) :
    ∀ (ts : List Ty) (inD outD : Nat) (inE : Trie ((t : Ty) × W t)),
      OptFlatPlanKit.insertTupEnv inD inE (OptFlatPlanKit.mkFreshTup mkW ts inD outD) =
        OptFlatPlanKit.insertFreshWith mkW inD outD ts inE
  | [], _, _, inE => rfl
  | t :: ts, inD, outD, inE => by
    dsimp only [OptFlatPlanKit.mkFreshTup, OptFlatPlanKit.insertTupEnv,
      OptFlatPlanKit.insertFreshWith]
    exact insertTupEnv_mkFreshTup_eq_insertFreshWith mkW ts (inD + 1) (outD + 1)
      (inE.insert inD ⟨t, mkW t inD outD⟩)

theorem tupMap_levels_eq_mkFreshTup {W : Ty → Type}
    (f : (t : Ty) → K t → W t) (mkW : (t : Ty) → Nat → Nat → W t)
    (hmk : ∀ t inD outD, f t (outD : K t) = mkW t inD outD) :
    ∀ (ts : List Ty) (inD outD : Nat),
      Tup.map f (Tup.levels ts outD) = OptFlatPlanKit.mkFreshTup mkW ts inD outD
  | [], _, _ => rfl
  | t :: ts, inD, outD => by
    dsimp only [Tup.levels, Tup.map, OptFlatPlanKit.mkFreshTup]
    rw [hmk t inD outD,
      tupMap_levels_eq_mkFreshTup f mkW hmk ts (inD + 1) (outD + 1)]

theorem trieCtxMatch_singleton {α : Type} {W : α → Type}
    {inD : Nat} {inE : Trie ((a : α) × W a)} {vs : List ((a : α) × W a)}
    (hm : TrieCtxMatch inD inE vs) (a : α) (w : W a) :
    TrieCtxMatch (inD + 1) (inE.insert inD ⟨a, w⟩) (⟨a, w⟩ :: vs) := by
  have h := OptFlatPlanKit.trieCtxMatch_insertTupEnv hm (ts := [a]) (w, ())
  dsimp only [OptFlatPlanKit.insertTupEnv, pushTup, List.length] at h
  exact h

theorem trieRelMatch_singleton {α : Type} {f₁ f₂ : α → Type}
    {R : (a : α) → f₁ a → f₂ a → Prop}
    {d : Nat} {env : Trie ((a : α) × f₁ a)} {vs : List ((a : α) × f₂ a)}
    (hm : OptFlatPlanKit.TrieRelMatch R d env vs) {a : α} {x₁ : f₁ a} {x₂ : f₂ a}
    (hr : R a x₁ x₂) :
    OptFlatPlanKit.TrieRelMatch R (d + 1) (env.insert d ⟨a, x₁⟩) (⟨a, x₂⟩ :: vs) :=
  OptFlatPlanKit.TrieRelMatch.cons hm hr

theorem wf_let {rs ts : List Ty} {Γ Δ} {op : Op K ts} {k : TFlat rs}
    (h : (TFlat.let_ op k).wfCheck Γ Δ = true) :
    checkArgs Γ op.args = true ∧ k.wfCheck (pushTypes ts Γ) Δ = true := by
  dsimp only [TFlat.wfCheck] at h; simpa only [Bool.and_eq_true] using h

theorem wf_load {rs : List Ty} {Γ Δ} {t : Ty} {a : Arg K i64} {k : TFlat rs}
    (h : (TFlat.load t a k).wfCheck Γ Δ = true) :
    checkArg Γ i64 a = true ∧ k.wfCheck (t :: Γ) Δ = true := by
  dsimp only [TFlat.wfCheck] at h; simpa only [Bool.and_eq_true] using h

theorem wf_store {rs : List Ty} {t : Ty} {Γ Δ} {v : Arg K t} {a : Arg K i64} {k : TFlat rs}
    (h : (TFlat.store v a k).wfCheck Γ Δ = true) :
    checkArg Γ t v = true ∧ checkArg Γ i64 a = true ∧ k.wfCheck Γ Δ = true := by
  dsimp only [TFlat.wfCheck] at h; simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem wf_call {rs as : List Ty} {Γ Δ} {f : Sym} {bs : List Ty}
    {args : Tup (Arg K) as} {k : TFlat rs}
    (h : (TFlat.call f bs args k).wfCheck Γ Δ = true) :
    checkArgs Γ args = true ∧ k.wfCheck (pushTypes bs Γ) Δ = true := by
  dsimp only [TFlat.wfCheck] at h; simpa only [Bool.and_eq_true] using h

theorem wf_jnz {rs : List Ty} {Γ Δ} {c : Arg K .bool} {t e : TFlat rs}
    (h : (TFlat.jnz c t e).wfCheck Γ Δ = true) :
    checkArg Γ .bool c = true ∧ t.wfCheck Γ Δ = true ∧ e.wfCheck Γ Δ = true := by
  dsimp only [TFlat.wfCheck] at h; simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem wf_jump {rs ts : List Ty} {Γ Δ} {j : Nat} {args : Tup (Arg K) ts}
    (h : (TFlat.jump (rs := rs) j args).wfCheck Γ Δ = true) :
    (match listGet? Δ j with
      | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
      | none => false) = true ∧ checkArgs Γ args = true := by
  dsimp only [TFlat.wfCheck] at h; rw [Bool.and_eq_true] at h; exact h

theorem wf_group {rs : List Ty} {sig : List (List Ty)} {Γ Δ}
    {bodies : TBlocks rs sig} {k : TFlat rs}
    (h : (TFlat.group bodies k).wfCheck Γ Δ = true) :
    bodies.wfCheck Γ (pushTypes sig Δ) = true ∧ k.wfCheck Γ (pushTypes sig Δ) = true := by
  dsimp only [TFlat.wfCheck] at h; simpa only [Bool.and_eq_true] using h

theorem wf_cons {rs ts : List Ty} {sig : List (List Ty)} {Γ Δ}
    {b : TFlat rs} {bs : TBlocks rs sig}
    (h : (TBlocks.cons (ts := ts) b bs).wfCheck Γ Δ = true) :
    b.wfCheck (pushTypes ts Γ) Δ = true ∧ bs.wfCheck Γ Δ = true := by
  dsimp only [TBlocks.wfCheck] at h; simpa only [Bool.and_eq_true] using h

/-! ## 2. Corollary Helpers & Pipeline Stage Composition -/

theorem denoteFunc_of_flat_eq {as rs : List Ty} {flat : TFlat rs → TFlat rs}
    {phoas : Func as rs → Func as rs}
    (hPwf : ∀ {f : Func as rs}, f.Wf → (phoas f).Wf)
    (tf : TFlat rs) (_hwf : tf.wfCheck (pushTypes as []) [] = true)
    (heq : flat tf = reifyFunc (phoas (denoteFunc tf))) :
    denoteFunc (as := as) (flat tf) = phoas (denoteFunc (as := as) tf) := by
  rw [heq]
  exact Func.renorm_eq_self (hPwf (Func.wf_of_denote tf rfl))

theorem wfCheck_of_flat_eq {as rs : List Ty} {flat : TFlat rs → TFlat rs}
    {phoas : Func as rs → Func as rs}
    (hPwf : ∀ {f : Func as rs}, f.Wf → (phoas f).Wf)
    (tf : TFlat rs) (_hwf : tf.wfCheck (pushTypes as []) [] = true)
    (heq : flat tf = reifyFunc (phoas (denoteFunc tf))) :
    (flat tf).wfCheck (pushTypes as []) [] = true := by
  rw [heq]
  exact PassFlatKit.reifyFunc_wfCheck (hPwf (Func.wf_of_denote tf rfl))

theorem fn_toFn_of_denoteFunc
    {flatBody : List Ty → {rs : List Ty} → TFlat rs → TFlat rs}
    {phoas : ∀ {as rs : List Ty}, Func as rs → Func as rs}
    (hden : ∀ {as rs : List Ty} (tf : TFlat rs),
      tf.wfCheck (pushTypes as []) [] = true →
      denoteFunc (as := as) (flatBody as tf) = phoas (denoteFunc (as := as) tf))
    (f : TFlatFn) (hwf : f.wfCheck = true) :
    ({ f with body := flatBody f.as f.body } : TFlatFn).toFn =
      ⟨f.name, f.as, f.rs, phoas f.toFn.body⟩ := by
  dsimp only [TFlatFn.toFn]
  rw [hden f.body hwf]

/-- Bundled compiler pass stage with preserved well-formedness and PHOAS denotation. -/
structure FlatStage (as rs : List Ty) where
  flat : TFlat rs → TFlat rs
  phoas : Func as rs → Func as rs
  wf : ∀ tf, tf.wfCheck (pushTypes as []) [] = true →
    (flat tf).wfCheck (pushTypes as []) [] = true
  denote_eq : ∀ tf, tf.wfCheck (pushTypes as []) [] = true →
    denoteFunc (as := as) (flat tf) = phoas (denoteFunc (as := as) tf)

@[expose] def FlatStage.ofEq {as rs : List Ty}
    (flat : TFlat rs → TFlat rs) (phoas : Func as rs → Func as rs)
    (heq : ∀ tf, tf.wfCheck (pushTypes as []) [] = true →
      flat tf = reifyFunc (phoas (denoteFunc tf)))
    (hPwf : ∀ {f : Func as rs}, f.Wf → (phoas f).Wf) : FlatStage as rs where
  flat := flat
  phoas := phoas
  wf tf hwf := wfCheck_of_flat_eq hPwf tf hwf (heq tf hwf)
  denote_eq tf hwf := denoteFunc_of_flat_eq hPwf tf hwf (heq tf hwf)

@[expose] def FlatStage.run {as rs : List Ty} (stages : List (FlatStage as rs))
    (tf : TFlat rs) : TFlat rs :=
  stages.foldl (fun cur st => st.flat cur) tf

@[expose] def FlatStage.runPhoas {as rs : List Ty} (stages : List (FlatStage as rs))
    (f : Func as rs) : Func as rs :=
  stages.foldl (fun cur st => st.phoas cur) f

theorem FlatStage.run_wfCheck {as rs : List Ty} :
    ∀ (stages : List (FlatStage as rs)) (tf : TFlat rs),
      tf.wfCheck (pushTypes as []) [] = true →
      (FlatStage.run stages tf).wfCheck (pushTypes as []) [] = true
  | [], _, hwf => hwf
  | st :: rest, tf, hwf => FlatStage.run_wfCheck rest (st.flat tf) (st.wf tf hwf)

theorem FlatStage.run_denoteFunc {as rs : List Ty} :
    ∀ (stages : List (FlatStage as rs)) (tf : TFlat rs),
      tf.wfCheck (pushTypes as []) [] = true →
      denoteFunc (as := as) (FlatStage.run stages tf) =
        FlatStage.runPhoas stages (denoteFunc (as := as) tf)
  | [], _, _ => rfl
  | st :: rest, tf, hwf => by
    change denoteFunc (as := as) (FlatStage.run rest (st.flat tf)) =
      FlatStage.runPhoas rest (st.phoas (denoteFunc (as := as) tf))
    rw [FlatStage.run_denoteFunc rest (st.flat tf) (st.wf tf hwf), st.denote_eq tf hwf]

/-- Generate `denoteFunc_*`, `*_wfCheck`, `*Fn_toFn`, and `*Fn_wfCheck` from `*_eq`. -/
macro "flat_pass_corollaries" flat:term "," phoas:term "," phoasWf:term ","
    eqThm:ident "," denoteThm:ident "," wfThm:ident ","
    fnFlat:term "," fnToFnThm:ident "," fnWfThm:ident : command => `(
  theorem $denoteThm {as rs : List Ty} (tf : TFlat rs)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      denoteFunc (as := as) ($flat as tf) = $phoas (denoteFunc (as := as) tf) :=
    LeanQbe.T.OptFlatSimKit.denoteFunc_of_flat_eq
      (fun hf => $phoasWf hf) tf hwf ($eqThm tf hwf)

  theorem $wfThm {as rs : List Ty} (tf : TFlat rs)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      ($flat as tf).wfCheck (pushTypes as []) [] = true :=
    LeanQbe.T.OptFlatSimKit.wfCheck_of_flat_eq
      (fun hf => $phoasWf hf) tf hwf ($eqThm tf hwf)

  theorem $fnToFnThm (f : TFlatFn) (hwf : f.wfCheck = true) :
      ($fnFlat f).toFn = ⟨f.name, f.as, f.rs, $phoas f.toFn.body⟩ :=
    LeanQbe.T.OptFlatSimKit.fn_toFn_of_denoteFunc
      (flatBody := fun as _ tf => $flat as tf)
      (phoas := fun g => $phoas g)
      (fun tf h => $denoteThm tf h) f hwf

  theorem $fnWfThm (f : TFlatFn) (hwf : f.wfCheck = true) :
      ($fnFlat f).wfCheck = true :=
    $wfThm f.body hwf
)

/-! ## 3. `(W, KL)` Forward-Pass Simulation Combinators -/

private abbrev CoreP (rs : List Ty) (W : Ty → Type) (L₁ L₂ : List Ty → Type) (S : Type) :=
  S → TFlat rs → List Ty → List (List Ty) → List ((t : Ty) × W t) →
    List ((ts : List Ty) × L₂ ts) → Nat → Trie ((t : Ty) × W t) → Nat →
    Trie ((ts : List Ty) × L₁ ts) → Nat → Nat → Prop

private abbrev CorePB (rs : List Ty) (W : Ty → Type) (L₁ L₂ : List Ty → Type) (SB : Type) :=
  ∀ {sig : List (List Ty)}, SB → TBlocks rs sig → List Ty → List (List Ty) →
    List ((t : Ty) × W t) → List ((ts : List Ty) × L₂ ts) → Nat → Trie ((t : Ty) × W t) →
    Nat → Trie ((ts : List Ty) × L₁ ts) → Nat → Nat → Prop

private structure CoreSteps {rs : List Ty} (W : Ty → Type) (L₁ L₂ : List Ty → Type) (S SB : Type)
    (VM : List Ty → Nat → Trie ((t : Ty) × W t) → List ((t : Ty) × W t) → Prop)
    (LR : List (List Ty) → Nat → Trie ((ts : List Ty) × L₁ ts) →
      List ((ts : List Ty) × L₂ ts) → Prop)
    (P : CoreP rs W L₁ L₂ S) (PB : CorePB rs W L₁ L₂ SB) : Prop where
  onLet : ∀ {ts Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (op : Op K ts) (k : TFlat rs),
    CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls → (TFlat.let_ op k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      VM Γ' inVD' inVE' vs' → LR Δ inLD' inLE' ls → k.wfCheck Γ' Δ = true →
      P s' k Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    P s (.let_ op k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onLoad : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (t : Ty) (a : Arg K i64)
    (k : TFlat rs), CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.load t a k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      VM Γ' inVD' inVE' vs' → LR Δ inLD' inLE' ls → k.wfCheck Γ' Δ = true →
      P s' k Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    P s (.load t a k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onStore : ∀ {t Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (v : Arg K t)
    (a : Arg K i64) (k : TFlat rs), CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.store v a k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      VM Γ' inVD' inVE' vs' → LR Δ inLD' inLE' ls → k.wfCheck Γ' Δ = true →
      P s' k Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    P s (.store v a k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onCall : ∀ {as Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (f : Sym) (bs : List Ty)
    (args : Tup (Arg K) as) (k : TFlat rs), CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.call f bs args k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      VM Γ' inVD' inVE' vs' → LR Δ inLD' inLE' ls → k.wfCheck Γ' Δ = true →
      P s' k Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    P s (.call f bs args k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onJnz : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (c : Arg K .bool) (t e : TFlat rs),
    CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls → (TFlat.jnz c t e).wfCheck Γ Δ = true →
    (∀ (s' : S), t.wfCheck Γ Δ = true → P s' t Γ Δ vs ls inVD inVE inLD inLE outVD outLD) →
    (∀ (s' : S), e.wfCheck Γ Δ = true → P s' e Γ Δ vs ls inVD inVE inLD inLE outVD outLD) →
    P s (.jnz c t e) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onJump : ∀ {ts Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (j : Nat)
    (args : Tup (Arg K) ts), CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.jump (rs := rs) j args).wfCheck Γ Δ = true →
    P s (.jump j args) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onRet : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (vs' : Tup (Arg K) rs),
    CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls → (TFlat.ret vs').wfCheck Γ Δ = true →
    P s (.ret vs') Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onExit : ∀ {as Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (f : Sym)
    (args : Tup (Arg K) as), CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.exit (rs := rs) f args).wfCheck Γ Δ = true →
    P s (.exit f args) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onHlt : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S),
    CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.hlt (rs := rs)).wfCheck Γ Δ = true → P s .hlt Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onGroup : ∀ {sig Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (bodies : TBlocks rs sig)
    (k : TFlat rs), CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.group bodies k).wfCheck Γ Δ = true →
    (∀ {Δ' ls' inLD' inLE' outLD'} (sb' : SB), LR Δ' inLD' inLE' ls' → bodies.wfCheck Γ Δ' = true →
      PB sb' bodies Γ Δ' vs ls' inVD inVE inLD' inLE' outVD outLD') →
    (∀ {Δ' ls' inLD' inLE' outLD'} (s' : S), LR Δ' inLD' inLE' ls' → k.wfCheck Γ Δ' = true →
      P s' k Γ Δ' vs ls' inVD inVE inLD' inLE' outVD outLD') →
    P s (.group bodies k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onNil : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sb : SB),
    CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TBlocks.nil (rs := rs)).wfCheck Γ Δ = true →
    PB (sig := []) sb .nil Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onCons : ∀ {ts sig Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sb : SB) (b : TFlat rs)
    (bs : TBlocks rs sig), CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
    (TBlocks.cons (ts := ts) b bs).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      VM Γ' inVD' inVE' vs' → LR Δ inLD' inLE' ls → b.wfCheck Γ' Δ = true →
      P s' b Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    (∀ (sb' : SB), bs.wfCheck Γ Δ = true → PB sb' bs Γ Δ vs ls inVD inVE inLD inLE outVD outLD) →
    PB (sig := ts :: sig) sb (.cons b bs) Γ Δ vs ls inVD inVE inLD inLE outVD outLD

end

mutual
private theorem coreSim_go {rs : List Ty} {W : Ty → Type} {L₁ L₂ : List Ty → Type} {S SB : Type}
    {VM LR} {P : CoreP rs W L₁ L₂ S} {PB : CorePB rs W L₁ L₂ SB}
    (st : CoreSteps (rs := rs) W L₁ L₂ S SB VM LR P PB) :
    ∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S),
      CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
      tf.wfCheck Γ Δ = true → P s tf Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  | .let_ op k, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf =>
    st.onLet s op k hΓ hmV hmL hwf (fun s' hΓ' hmV' hmL' hk => coreSim_go st k s' hΓ' hmV' hmL' hk)
  | .load t a k, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf =>
    st.onLoad s t a k hΓ hmV hmL hwf
      (fun s' hΓ' hmV' hmL' hk => coreSim_go st k s' hΓ' hmV' hmL' hk)
  | .store v a k, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf =>
    st.onStore s v a k hΓ hmV hmL hwf
      (fun s' hΓ' hmV' hmL' hk => coreSim_go st k s' hΓ' hmV' hmL' hk)
  | .call f bs args k, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf =>
    st.onCall s f bs args k hΓ hmV hmL hwf
      (fun s' hΓ' hmV' hmL' hk => coreSim_go st k s' hΓ' hmV' hmL' hk)
  | .jnz c t e, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf =>
    have ⟨_, ht, he⟩ := wf_jnz hwf
    st.onJnz s c t e hΓ hmV hmL hwf
      (fun s' _ => coreSim_go st t s' hΓ hmV hmL ht)
      (fun s' _ => coreSim_go st e s' hΓ hmV hmL he)
  | .jump j args, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf =>
    st.onJump s j args hΓ hmV hmL hwf
  | .ret vs', _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf => st.onRet s vs' hΓ hmV hmL hwf
  | .exit f args, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf =>
    st.onExit s f args hΓ hmV hmL hwf
  | .hlt, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf => st.onHlt s hΓ hmV hmL hwf
  | .group bodies k, _, _, _, _, _, _, _, _, _, _, s, hΓ, hmV, hmL, hwf =>
    st.onGroup s bodies k hΓ hmV hmL hwf
      (fun sb' hmL' hb => coreSim_goB st bodies sb' hΓ hmV hmL' hb)
      (fun s' hmL' hk => coreSim_go st k s' hΓ hmV hmL' hk)

private theorem coreSim_goB {rs : List Ty} {W : Ty → Type} {L₁ L₂ : List Ty → Type} {S SB : Type}
    {VM LR} {P : CoreP rs W L₁ L₂ S} {PB : CorePB rs W L₁ L₂ SB}
    (st : CoreSteps (rs := rs) W L₁ L₂ S SB VM LR P PB) :
    ∀ {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE}
      (sb : SB), CtxTypes Γ vs → VM Γ inVD inVE vs → LR Δ inLD inLE ls →
      tb.wfCheck Γ Δ = true → PB sb tb Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  | [], .nil, _, _, _, _, _, _, _, _, _, _, sb, hΓ, hmV, hmL, hwf =>
    st.onNil sb hΓ hmV hmL hwf
  | ts :: sig, .cons b bs, _, _, _, _, _, _, _, _, _, _, sb, hΓ, hmV, hmL, hwf =>
    st.onCons (ts := ts) (sig := sig) sb b bs hΓ hmV hmL hwf
      (fun s' hΓ' hmV' hmL' hb => coreSim_go st b s' hΓ' hmV' hmL' hb)
      (fun sb' hbs => coreSim_goB st bs sb' hΓ hmV hmL hbs)
end

public section

/-- Bundles the inductive step handlers for `klSim_mutual`. -/
structure KLSteps (W : Ty → Type) (S SB : Type)
    (P : ∀ {rs : List Ty}, S → TFlat rs → List Ty → List (List Ty) → List ((t : Ty) × W t) →
      List ((ts : List Ty) × KL ts) → Nat → Trie ((t : Ty) × W t) → Nat → Prop)
    (PB : ∀ {rs : List Ty} {sig : List (List Ty)}, SB → TBlocks rs sig → List Ty → List (List Ty) →
      List ((t : Ty) × W t) → List ((ts : List Ty) × KL ts) → Nat → Trie ((t : Ty) × W t) → Nat →
      Prop) : Prop where
  onLet : ∀ {rs ts Γ Δ vs ls inD outD inE} (s : S) (op : Op K ts) (k : TFlat rs),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TFlat.let_ op k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inD' outD' inE'} (s' : S), CtxTypes Γ' vs' → TrieCtxMatch inD' inE' vs' →
      k.wfCheck Γ' Δ = true → P s' k Γ' Δ vs' ls inD' inE' outD') →
    P s (.let_ op k) Γ Δ vs ls inD inE outD
  onLoad : ∀ {rs Γ Δ vs ls inD outD inE} (s : S) (t : Ty) (a : Arg K i64) (k : TFlat rs),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TFlat.load t a k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inD' outD' inE'} (s' : S), CtxTypes Γ' vs' → TrieCtxMatch inD' inE' vs' →
      k.wfCheck Γ' Δ = true → P s' k Γ' Δ vs' ls inD' inE' outD') →
    P s (.load t a k) Γ Δ vs ls inD inE outD
  onStore : ∀ {rs t Γ Δ vs ls inD outD inE} (s : S) (v : Arg K t) (a : Arg K i64) (k : TFlat rs),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TFlat.store v a k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inD' outD' inE'} (s' : S), CtxTypes Γ' vs' → TrieCtxMatch inD' inE' vs' →
      k.wfCheck Γ' Δ = true → P s' k Γ' Δ vs' ls inD' inE' outD') →
    P s (.store v a k) Γ Δ vs ls inD inE outD
  onCall : ∀ {rs as Γ Δ vs ls inD outD inE} (s : S) (f : Sym) (bs : List Ty)
    (args : Tup (Arg K) as) (k : TFlat rs), CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inD inE vs → (TFlat.call f bs args k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inD' outD' inE'} (s' : S), CtxTypes Γ' vs' → TrieCtxMatch inD' inE' vs' →
      k.wfCheck Γ' Δ = true → P s' k Γ' Δ vs' ls inD' inE' outD') →
    P s (.call f bs args k) Γ Δ vs ls inD inE outD
  onJnz : ∀ {rs Γ Δ vs ls inD outD inE} (s : S) (c : Arg K .bool) (t e : TFlat rs),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TFlat.jnz c t e).wfCheck Γ Δ = true →
    (∀ (s' : S), t.wfCheck Γ Δ = true → P s' t Γ Δ vs ls inD inE outD) →
    (∀ (s' : S), e.wfCheck Γ Δ = true → P s' e Γ Δ vs ls inD inE outD) →
    P s (.jnz c t e) Γ Δ vs ls inD inE outD
  onJump : ∀ {rs ts Γ Δ vs ls inD outD inE} (s : S) (j : Nat) (args : Tup (Arg K) ts),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TFlat.jump (rs := rs) j args).wfCheck Γ Δ = true →
    P (rs := rs) s (.jump j args) Γ Δ vs ls inD inE outD
  onRet : ∀ {rs Γ Δ vs ls inD outD inE} (s : S) (vs' : Tup (Arg K) rs),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TFlat.ret vs').wfCheck Γ Δ = true → P s (.ret vs') Γ Δ vs ls inD inE outD
  onExit : ∀ {rs as Γ Δ vs ls inD outD inE} (s : S) (f : Sym) (args : Tup (Arg K) as),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TFlat.exit (rs := rs) f args).wfCheck Γ Δ = true →
    P (rs := rs) s (.exit f args) Γ Δ vs ls inD inE outD
  onHlt : ∀ {rs Γ Δ vs ls inD outD inE} (s : S), CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inD inE vs → (TFlat.hlt (rs := rs)).wfCheck Γ Δ = true →
    P (rs := rs) s .hlt Γ Δ vs ls inD inE outD
  onGroup : ∀ {rs sig Γ Δ vs ls inD outD inE} (s : S) (bodies : TBlocks rs sig) (k : TFlat rs),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TFlat.group bodies k).wfCheck Γ Δ = true →
    (∀ {Δ' ls'} (sb' : SB), CtxTypes Δ' ls' → CtxLevels ls' → bodies.wfCheck Γ Δ' = true →
      PB sb' bodies Γ Δ' vs ls' inD inE outD) →
    (∀ {Δ' ls'} (s' : S), CtxTypes Δ' ls' → CtxLevels ls' → k.wfCheck Γ Δ' = true →
      P s' k Γ Δ' vs ls' inD inE outD) →
    P s (.group bodies k) Γ Δ vs ls inD inE outD
  onNil : ∀ {rs Γ Δ vs ls inD outD inE} (sb : SB), CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inD inE vs → (TBlocks.nil (rs := rs)).wfCheck Γ Δ = true →
    PB (rs := rs) (sig := []) sb .nil Γ Δ vs ls inD inE outD
  onCons : ∀ {rs ts sig Γ Δ vs ls inD outD inE} (sb : SB) (b : TFlat rs) (bs : TBlocks rs sig),
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
    (TBlocks.cons (ts := ts) b bs).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inD' outD' inE'} (s' : S), CtxTypes Γ' vs' → TrieCtxMatch inD' inE' vs' →
      b.wfCheck Γ' Δ = true → P s' b Γ' Δ vs' ls inD' inE' outD') →
    (∀ (sb' : SB), bs.wfCheck Γ Δ = true → PB sb' bs Γ Δ vs ls inD inE outD) →
    PB (rs := rs) (sig := ts :: sig) sb (.cons b bs) Γ Δ vs ls inD inE outD

/-- Mutual structural induction combinator for `(W, KL)` forward passes on `TFlat`/`TBlocks`. -/
theorem klSim_mutual {W : Ty → Type} {S SB : Type}
    {P : ∀ {rs : List Ty}, S → TFlat rs → List Ty → List (List Ty) → List ((t : Ty) × W t) →
      List ((ts : List Ty) × KL ts) → Nat → Trie ((t : Ty) × W t) → Nat → Prop}
    {PB : ∀ {rs : List Ty} {sig : List (List Ty)}, SB → TBlocks rs sig → List Ty → List (List Ty) →
      List ((t : Ty) × W t) → List ((ts : List Ty) × KL ts) → Nat → Trie ((t : Ty) × W t) → Nat →
      Prop}
    (st : KLSteps W S SB P PB) :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (s : S),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inD inE vs →
      tf.wfCheck Γ Δ = true → P s tf Γ Δ vs ls inD inE outD) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD outD inE} (sb : SB), CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true → PB sb tb Γ Δ vs ls inD inE outD) := by
  have h : ∀ {rs : List Ty},
      CoreSteps (rs := rs) W KL KL S SB (fun _ => TrieCtxMatch)
        (fun Δ _ _ ls => CtxTypes Δ ls ∧ CtxLevels ls)
        (fun s tf Γ Δ vs ls inD inE _ _ outD _ => P s tf Γ Δ vs ls inD inE outD)
        (fun sb tb Γ Δ vs ls inD inE _ _ outD _ => PB sb tb Γ Δ vs ls inD inE outD) :=
    fun {rs} => ⟨
      fun s op k hΓ hm hll hwf ih => st.onLet s op k hΓ hll.1 hll.2 hm hwf
        (fun s' hΓ' hm' hk => ih (inLD' := 0) (inLE' := .empty) (outLD' := 0) s' hΓ' hm' hll hk),
      fun s t a k hΓ hm hll hwf ih => st.onLoad s t a k hΓ hll.1 hll.2 hm hwf
        (fun s' hΓ' hm' hk => ih (inLD' := 0) (inLE' := .empty) (outLD' := 0) s' hΓ' hm' hll hk),
      fun s v a k hΓ hm hll hwf ih => st.onStore s v a k hΓ hll.1 hll.2 hm hwf
        (fun s' hΓ' hm' hk => ih (inLD' := 0) (inLE' := .empty) (outLD' := 0) s' hΓ' hm' hll hk),
      fun s f bs args k hΓ hm hll hwf ih => st.onCall s f bs args k hΓ hll.1 hll.2 hm hwf
        (fun s' hΓ' hm' hk => ih (inLD' := 0) (inLE' := .empty) (outLD' := 0) s' hΓ' hm' hll hk),
      fun s c t e hΓ hm hll hwf iht ihe => st.onJnz s c t e hΓ hll.1 hll.2 hm hwf iht ihe,
      fun s j args hΓ hm hll hwf => st.onJump s j args hΓ hll.1 hll.2 hm hwf,
      fun s vs' hΓ hm hll hwf => st.onRet s vs' hΓ hll.1 hll.2 hm hwf,
      fun s f args hΓ hm hll hwf => st.onExit s f args hΓ hll.1 hll.2 hm hwf,
      fun s hΓ hm hll hwf => st.onHlt s hΓ hll.1 hll.2 hm hwf,
      fun s bodies k hΓ hm hll hwf ihB ihK => st.onGroup s bodies k hΓ hll.1 hll.2 hm hwf
        (fun sb' hΔ' hll' hb => ihB (inLD' := 0) (inLE' := .empty) (outLD' := 0) sb' ⟨hΔ', hll'⟩ hb)
        (fun s' hΔ' hll' hk => ihK (inLD' := 0) (inLE' := .empty) (outLD' := 0) s' ⟨hΔ', hll'⟩ hk),
      fun sb hΓ hm hll hwf => st.onNil sb hΓ hll.1 hll.2 hm hwf,
      fun sb b bs hΓ hm hll hwf ihb ihbs => st.onCons sb b bs hΓ hll.1 hll.2 hm hwf
        (fun s' hΓ' hm' hb =>
          ihb (inLD' := 0) (inLE' := .empty) (outLD' := 0) s' hΓ' hm' hll hb) ihbs⟩
  exact ⟨fun tf _ _ _ _ _ _ _ s hΓ hΔ hll hm hwf =>
      coreSim_go h tf s hΓ hm ⟨hΔ, hll⟩ hwf (inLD := 0) (inLE := .empty) (outLD := 0),
    fun tb _ _ _ _ _ _ _ sb hΓ hΔ hll hm hwf =>
      coreSim_goB h tb sb hΓ hm ⟨hΔ, hll⟩ hwf (inLD := 0) (inLE := .empty) (outLD := 0)⟩

/-! ## 4. General `(W, L)` Rel-Simulation Combinator -/

/-- Bundles the inductive step handlers for `relSim_mutual`. -/
structure RelSteps {rs : List Ty} (W : Ty → Type) (L₁ L₂ : List Ty → Type) (S SB : Type)
    (LR : List (List Ty) → Nat → Trie ((ts : List Ty) × L₁ ts) →
      List ((ts : List Ty) × L₂ ts) → Prop)
    (P : S → TFlat rs → List Ty → List (List Ty) → List ((t : Ty) × W t) →
      List ((ts : List Ty) × L₂ ts) → Nat → Trie ((t : Ty) × W t) → Nat →
      Trie ((ts : List Ty) × L₁ ts) → Nat → Nat → Prop)
    (PB : ∀ {sig : List (List Ty)}, SB → TBlocks rs sig → List Ty → List (List Ty) →
      List ((t : Ty) × W t) → List ((ts : List Ty) × L₂ ts) → Nat → Trie ((t : Ty) × W t) →
      Nat → Trie ((ts : List Ty) × L₁ ts) → Nat → Nat → Prop) : Prop where
  onLet : ∀ {ts Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (op : Op K ts) (k : TFlat rs),
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.let_ op k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      TrieCtxMatch inVD' inVE' vs' → LR Δ inLD' inLE' ls → k.wfCheck Γ' Δ = true →
      P s' k Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    P s (.let_ op k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onLoad : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (t : Ty) (a : Arg K i64)
    (k : TFlat rs), CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    LR Δ inLD inLE ls → (TFlat.load t a k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      TrieCtxMatch inVD' inVE' vs' → LR Δ inLD' inLE' ls → k.wfCheck Γ' Δ = true →
      P s' k Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    P s (.load t a k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onStore : ∀ {t Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (v : Arg K t)
    (a : Arg K i64) (k : TFlat rs), CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    LR Δ inLD inLE ls → (TFlat.store v a k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      TrieCtxMatch inVD' inVE' vs' → LR Δ inLD' inLE' ls → k.wfCheck Γ' Δ = true →
      P s' k Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    P s (.store v a k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onCall : ∀ {as Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (f : Sym) (bs : List Ty)
    (args : Tup (Arg K) as) (k : TFlat rs), CtxTypes Γ vs → CtxTypes Δ ls →
    TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls → (TFlat.call f bs args k).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      TrieCtxMatch inVD' inVE' vs' → LR Δ inLD' inLE' ls → k.wfCheck Γ' Δ = true →
      P s' k Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    P s (.call f bs args k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onJnz : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (c : Arg K .bool) (t e : TFlat rs),
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.jnz c t e).wfCheck Γ Δ = true →
    (∀ (s' : S), t.wfCheck Γ Δ = true → P s' t Γ Δ vs ls inVD inVE inLD inLE outVD outLD) →
    (∀ (s' : S), e.wfCheck Γ Δ = true → P s' e Γ Δ vs ls inVD inVE inLD inLE outVD outLD) →
    P s (.jnz c t e) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onJump : ∀ {ts Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (j : Nat)
    (args : Tup (Arg K) ts), CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    LR Δ inLD inLE ls → (TFlat.jump (rs := rs) j args).wfCheck Γ Δ = true →
    P s (.jump j args) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onRet : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (vs' : Tup (Arg K) rs),
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.ret vs').wfCheck Γ Δ = true → P s (.ret vs') Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onExit : ∀ {as Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (f : Sym)
    (args : Tup (Arg K) as), CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    LR Δ inLD inLE ls → (TFlat.exit (rs := rs) f args).wfCheck Γ Δ = true →
    P s (.exit f args) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onHlt : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S), CtxTypes Γ vs → CtxTypes Δ ls →
    TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls → (TFlat.hlt (rs := rs)).wfCheck Γ Δ = true →
    P s .hlt Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onGroup : ∀ {sig Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S) (bodies : TBlocks rs sig)
    (k : TFlat rs), CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls →
    (TFlat.group bodies k).wfCheck Γ Δ = true →
    (∀ {Δ' ls' inLD' inLE' outLD'} (sb' : SB), CtxTypes Δ' ls' → LR Δ' inLD' inLE' ls' →
      bodies.wfCheck Γ Δ' = true → PB sb' bodies Γ Δ' vs ls' inVD inVE inLD' inLE' outVD outLD') →
    (∀ {Δ' ls' inLD' inLE' outLD'} (s' : S), CtxTypes Δ' ls' → LR Δ' inLD' inLE' ls' →
      k.wfCheck Γ Δ' = true → P s' k Γ Δ' vs ls' inVD inVE inLD' inLE' outVD outLD') →
    P s (.group bodies k) Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onNil : ∀ {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sb : SB), CtxTypes Γ vs →
    CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls →
    (TBlocks.nil (rs := rs)).wfCheck Γ Δ = true →
    PB (sig := []) sb .nil Γ Δ vs ls inVD inVE inLD inLE outVD outLD
  onCons : ∀ {ts sig Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sb : SB) (b : TFlat rs)
    (bs : TBlocks rs sig), CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    LR Δ inLD inLE ls → (TBlocks.cons (ts := ts) b bs).wfCheck Γ Δ = true →
    (∀ {Γ' vs' inVD' outVD' inLD' outLD' inVE' inLE'} (s' : S), CtxTypes Γ' vs' →
      TrieCtxMatch inVD' inVE' vs' → LR Δ inLD' inLE' ls → b.wfCheck Γ' Δ = true →
      P s' b Γ' Δ vs' ls inVD' inVE' inLD' inLE' outVD' outLD') →
    (∀ (sb' : SB), bs.wfCheck Γ Δ = true → PB sb' bs Γ Δ vs ls inVD inVE inLD inLE outVD outLD) →
    PB (sig := ts :: sig) sb (.cons b bs) Γ Δ vs ls inVD inVE inLD inLE outVD outLD

end

public section

/-- Mutual structural induction combinator for custom-label `(W, L₁/L₂)` forward passes. -/
theorem relSim_mutual {rs : List Ty} {W : Ty → Type} {L₁ L₂ : List Ty → Type} {S SB : Type}
    {LR : List (List Ty) → Nat → Trie ((ts : List Ty) × L₁ ts) →
      List ((ts : List Ty) × L₂ ts) → Prop}
    {P : S → TFlat rs → List Ty → List (List Ty) →
      List ((t : Ty) × W t) → List ((ts : List Ty) × L₂ ts) →
      Nat → Trie ((t : Ty) × W t) → Nat → Trie ((ts : List Ty) × L₁ ts) → Nat → Nat → Prop}
    {PB : ∀ {sig : List (List Ty)}, SB → TBlocks rs sig → List Ty →
      List (List Ty) → List ((t : Ty) × W t) → List ((ts : List Ty) × L₂ ts) →
      Nat → Trie ((t : Ty) × W t) → Nat → Trie ((ts : List Ty) × L₁ ts) → Nat → Nat → Prop}
    (st : RelSteps (rs := rs) W L₁ L₂ S SB LR P PB) :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : S),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls →
      tf.wfCheck Γ Δ = true → P s tf Γ Δ vs ls inVD inVE inLD inLE outVD outLD) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sb : SB), CtxTypes Γ vs → CtxTypes Δ ls →
      TrieCtxMatch inVD inVE vs → LR Δ inLD inLE ls → tb.wfCheck Γ Δ = true →
      PB sb tb Γ Δ vs ls inVD inVE inLD inLE outVD outLD) := by
  have h : CoreSteps (rs := rs) W L₁ L₂ S SB (fun _ => TrieCtxMatch)
      (fun Δ inLD inLE ls => CtxTypes Δ ls ∧ LR Δ inLD inLE ls) P PB := ⟨
    fun s op k hΓ hm hlr hwf ih => st.onLet s op k hΓ hlr.1 hm hlr.2 hwf
      (fun s' hΓ' hm' hmr hk => ih s' hΓ' hm' ⟨hlr.1, hmr⟩ hk),
    fun s t a k hΓ hm hlr hwf ih => st.onLoad s t a k hΓ hlr.1 hm hlr.2 hwf
      (fun s' hΓ' hm' hmr hk => ih s' hΓ' hm' ⟨hlr.1, hmr⟩ hk),
    fun s v a k hΓ hm hlr hwf ih => st.onStore s v a k hΓ hlr.1 hm hlr.2 hwf
      (fun s' hΓ' hm' hmr hk => ih s' hΓ' hm' ⟨hlr.1, hmr⟩ hk),
    fun s f bs args k hΓ hm hlr hwf ih => st.onCall s f bs args k hΓ hlr.1 hm hlr.2 hwf
      (fun s' hΓ' hm' hmr hk => ih s' hΓ' hm' ⟨hlr.1, hmr⟩ hk),
    fun s c t e hΓ hm hlr hwf iht ihe => st.onJnz s c t e hΓ hlr.1 hm hlr.2 hwf iht ihe,
    fun s j args hΓ hm hlr hwf => st.onJump s j args hΓ hlr.1 hm hlr.2 hwf,
    fun s vs' hΓ hm hlr hwf => st.onRet s vs' hΓ hlr.1 hm hlr.2 hwf,
    fun s f args hΓ hm hlr hwf => st.onExit s f args hΓ hlr.1 hm hlr.2 hwf,
    fun s hΓ hm hlr hwf => st.onHlt s hΓ hlr.1 hm hlr.2 hwf,
    fun s bodies k hΓ hm hlr hwf ihB ihK => st.onGroup s bodies k hΓ hlr.1 hm hlr.2 hwf
      (fun sb' hΔ' hmr hb => ihB sb' ⟨hΔ', hmr⟩ hb)
      (fun s' hΔ' hmr hk => ihK s' ⟨hΔ', hmr⟩ hk),
    fun sb hΓ hm hlr hwf => st.onNil sb hΓ hlr.1 hm hlr.2 hwf,
    fun sb b bs hΓ hm hlr hwf ihb ihbs => st.onCons sb b bs hΓ hlr.1 hm hlr.2 hwf
      (fun s' hΓ' hm' hmr hb => ihb s' hΓ' hm' ⟨hlr.1, hmr⟩ hb) ihbs⟩
  exact ⟨fun tf _ _ _ _ _ _ _ _ _ _ s hΓ hΔ hm hlr hwf => coreSim_go h tf s hΓ hm ⟨hΔ, hlr⟩ hwf,
    fun tb _ _ _ _ _ _ _ _ _ _ sb hΓ hΔ hm hlr hwf => coreSim_goB h tb sb hΓ hm ⟨hΔ, hlr⟩ hwf⟩

/-! ## 5. Level-Indexed Scan & Plan-Validator Combinator -/

/-- Bundles the inductive step handlers for `scanSim_mutual`. -/
structure ScanSteps (L₁ L₂ : List Ty → Type) (S SB : Type)
    (LR : List (List Ty) → Nat → Trie ((ts : List Ty) × L₁ ts) →
      List ((ts : List Ty) × L₂ ts) → Prop)
    (P : ∀ {rs : List Ty}, S → TFlat rs → List Ty → List (List Ty) →
      List ((t : Ty) × K t) → List ((ts : List Ty) × L₂ ts) →
      Nat → Trie ((ts : List Ty) × L₁ ts) → Prop)
    (PB : ∀ {rs : List Ty} {sig : List (List Ty)}, SB → TBlocks rs sig → List Ty →
      List (List Ty) → List ((t : Ty) × K t) → List ((ts : List Ty) × L₂ ts) →
      Nat → Trie ((ts : List Ty) × L₁ ts) → Prop) : Prop where
  onLet : ∀ {rs ts Γ Δ vs ls inLD inLE} (s : S) (op : Op K ts) (k : TFlat rs),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls → (TFlat.let_ op k).wfCheck Γ Δ = true →
    (∀ (s' : S), P s' k (pushTypes ts Γ) Δ (pushTup (Tup.levels ts vs.length) vs) ls inLD inLE) →
    P s (.let_ op k) Γ Δ vs ls inLD inLE
  onLoad : ∀ {rs Γ Δ vs ls inLD inLE} (s : S) (t : Ty) (a : Arg K i64) (k : TFlat rs),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls → (TFlat.load t a k).wfCheck Γ Δ = true →
    (∀ (s' : S), P s' k (t :: Γ) Δ (⟨t, vs.length⟩ :: vs) ls inLD inLE) →
    P s (.load t a k) Γ Δ vs ls inLD inLE
  onStore : ∀ {rs t Γ Δ vs ls inLD inLE} (s : S) (v : Arg K t) (a : Arg K i64) (k : TFlat rs),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls → (TFlat.store v a k).wfCheck Γ Δ = true →
    (∀ (s' : S), P s' k Γ Δ vs ls inLD inLE) → P s (.store v a k) Γ Δ vs ls inLD inLE
  onCall : ∀ {rs as Γ Δ vs ls inLD inLE} (s : S) (f : Sym) (bs : List Ty)
    (args : Tup (Arg K) as) (k : TFlat rs), CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls →
    (TFlat.call f bs args k).wfCheck Γ Δ = true →
    (∀ (s' : S), P s' k (pushTypes bs Γ) Δ (pushTup (Tup.levels bs vs.length) vs) ls inLD inLE) →
    P s (.call f bs args k) Γ Δ vs ls inLD inLE
  onJnz : ∀ {rs Γ Δ vs ls inLD inLE} (s : S) (c : Arg K .bool) (t e : TFlat rs),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls → (TFlat.jnz c t e).wfCheck Γ Δ = true →
    (∀ (s' : S), P s' t Γ Δ vs ls inLD inLE) → (∀ (s' : S), P s' e Γ Δ vs ls inLD inLE) →
    P s (.jnz c t e) Γ Δ vs ls inLD inLE
  onJump : ∀ {rs ts Γ Δ vs ls inLD inLE} (s : S) (j : Nat) (args : Tup (Arg K) ts),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls →
    (TFlat.jump (rs := rs) j args).wfCheck Γ Δ = true →
    P (rs := rs) s (.jump j args) Γ Δ vs ls inLD inLE
  onRet : ∀ {rs Γ Δ vs ls inLD inLE} (s : S) (vs' : Tup (Arg K) rs),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls → (TFlat.ret vs').wfCheck Γ Δ = true →
    P s (.ret vs') Γ Δ vs ls inLD inLE
  onExit : ∀ {rs as Γ Δ vs ls inLD inLE} (s : S) (f : Sym) (args : Tup (Arg K) as),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls →
    (TFlat.exit (rs := rs) f args).wfCheck Γ Δ = true →
    P (rs := rs) s (.exit f args) Γ Δ vs ls inLD inLE
  onHlt : ∀ {rs Γ Δ vs ls inLD inLE} (s : S), CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls →
    (TFlat.hlt (rs := rs)).wfCheck Γ Δ = true → P (rs := rs) s .hlt Γ Δ vs ls inLD inLE
  onGroup : ∀ {rs sig Γ Δ vs ls inLD inLE} (s : S) (bodies : TBlocks rs sig) (k : TFlat rs),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls →
    (TFlat.group bodies k).wfCheck Γ Δ = true →
    (∀ {Δ' ls' inLD' inLE'} (sb' : SB), LR Δ' inLD' inLE' ls' → bodies.wfCheck Γ Δ' = true →
      PB sb' bodies Γ Δ' vs ls' inLD' inLE') →
    (∀ {Δ' ls' inLD' inLE'} (s' : S), LR Δ' inLD' inLE' ls' → k.wfCheck Γ Δ' = true →
      P s' k Γ Δ' vs ls' inLD' inLE') →
    P s (.group bodies k) Γ Δ vs ls inLD inLE
  onNil : ∀ {rs Γ Δ vs ls inLD inLE} (sb : SB), CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls →
    (TBlocks.nil (rs := rs)).wfCheck Γ Δ = true →
    PB (rs := rs) (sig := []) sb .nil Γ Δ vs ls inLD inLE
  onCons : ∀ {rs ts sig Γ Δ vs ls inLD inLE} (sb : SB) (b : TFlat rs) (bs : TBlocks rs sig),
    CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls →
    (TBlocks.cons (ts := ts) b bs).wfCheck Γ Δ = true →
    (∀ (s' : S), P s' b (pushTypes ts Γ) Δ (pushTup (Tup.levels ts vs.length) vs) ls inLD inLE) →
    (∀ (sb' : SB), PB sb' bs Γ Δ vs ls inLD inLE) →
    PB (rs := rs) (sig := ts :: sig) sb (.cons b bs) Γ Δ vs ls inLD inLE

/-- Mutual structural induction combinator for level-indexed scans and plan validators. -/
theorem scanSim_mutual {L₁ L₂ : List Ty → Type} {S SB : Type}
    {LR : List (List Ty) → Nat → Trie ((ts : List Ty) × L₁ ts) →
      List ((ts : List Ty) × L₂ ts) → Prop}
    {P : ∀ {rs : List Ty}, S → TFlat rs → List Ty → List (List Ty) →
      List ((t : Ty) × K t) → List ((ts : List Ty) × L₂ ts) →
      Nat → Trie ((ts : List Ty) × L₁ ts) → Prop}
    {PB : ∀ {rs : List Ty} {sig : List (List Ty)}, SB → TBlocks rs sig → List Ty →
      List (List Ty) → List ((t : Ty) × K t) → List ((ts : List Ty) × L₂ ts) →
      Nat → Trie ((ts : List Ty) × L₁ ts) → Prop}
    (st : ScanSteps L₁ L₂ S SB LR P PB) :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inLD inLE} (s : S),
      CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls → tf.wfCheck Γ Δ = true →
      P s tf Γ Δ vs ls inLD inLE) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inLD inLE} (sb : SB),
      CtxTypes Γ vs → CtxLevels vs → LR Δ inLD inLE ls → tb.wfCheck Γ Δ = true →
      PB sb tb Γ Δ vs ls inLD inLE) := by
  have h : ∀ {rs : List Ty},
      CoreSteps (rs := rs) K L₁ L₂ S SB (fun _ _ _ vs => CtxLevels vs) LR
        (fun s tf Γ Δ vs ls _ _ inLD inLE _ _ => P s tf Γ Δ vs ls inLD inLE)
        (fun sb tb Γ Δ vs ls _ _ inLD inLE _ _ => PB sb tb Γ Δ vs ls inLD inLE) :=
    fun {rs} => ⟨
      fun s op k hΓ hvl hlr hwf ih => st.onLet s op k hΓ hvl hlr hwf (fun s' =>
        ih (inVD' := 0) (outVD' := 0) (inLD' := _) (outLD' := 0) (inVE' := .empty) (inLE' := _)
          s' (OptFlatPlanKit.ctxTypes_pushTup_rev _ hΓ) hvl.pushTup hlr (wf_let hwf).2),
      fun s t a k hΓ hvl hlr hwf ih => st.onLoad s t a k hΓ hvl hlr hwf (fun s' =>
        ih (inVD' := 0) (outVD' := 0) (inLD' := _) (outLD' := 0) (inVE' := .empty) (inLE' := _)
          s' (.cons hΓ) (hvl.cons t) hlr (wf_load hwf).2),
      fun s v a k hΓ hvl hlr hwf ih => st.onStore s v a k hΓ hvl hlr hwf (fun s' =>
        ih (inVD' := 0) (outVD' := 0) (inLD' := _) (outLD' := 0) (inVE' := .empty) (inLE' := _)
          s' hΓ hvl hlr (wf_store hwf).2.2),
      fun s f bs args k hΓ hvl hlr hwf ih => st.onCall s f bs args k hΓ hvl hlr hwf (fun s' =>
        ih (inVD' := 0) (outVD' := 0) (inLD' := _) (outLD' := 0) (inVE' := .empty) (inLE' := _)
          s' (OptFlatPlanKit.ctxTypes_pushTup_rev _ hΓ) hvl.pushTup hlr (wf_call hwf).2),
      fun s c t e hΓ hvl hlr hwf iht ihe => st.onJnz s c t e hΓ hvl hlr hwf
        (fun s' => iht s' (wf_jnz hwf).2.1) (fun s' => ihe s' (wf_jnz hwf).2.2),
      fun s j args hΓ hvl hlr hwf => st.onJump s j args hΓ hvl hlr hwf,
      fun s vs' hΓ hvl hlr hwf => st.onRet s vs' hΓ hvl hlr hwf,
      fun s f args hΓ hvl hlr hwf => st.onExit s f args hΓ hvl hlr hwf,
      fun s hΓ hvl hlr hwf => st.onHlt s hΓ hvl hlr hwf,
      fun s bodies k hΓ hvl hlr hwf ihB ihK => st.onGroup s bodies k hΓ hvl hlr hwf
        (fun sb' hlr' hb => ihB (outLD' := 0) sb' hlr' hb)
        (fun s' hlr' hk => ihK (outLD' := 0) s' hlr' hk),
      fun sb hΓ hvl hlr hwf => st.onNil sb hΓ hvl hlr hwf,
      fun sb b bs hΓ hvl hlr hwf ihb ihbs => st.onCons sb b bs hΓ hvl hlr hwf
        (fun s' => ihb (inVD' := 0) (outVD' := 0) (inLD' := _) (outLD' := 0)
          (inVE' := .empty) (inLE' := _) s'
          (OptFlatPlanKit.ctxTypes_pushTup_rev _ hΓ) hvl.pushTup hlr (wf_cons hwf).1)
        (fun sb' => ihbs sb' (wf_cons hwf).2)⟩
  constructor
  · intro _ tf _ _ _ _ _ _ s hΓ hvl hlr hwf
    exact coreSim_go h tf s hΓ hvl hlr hwf
      (inVD := 0) (inVE := .empty) (outVD := 0) (outLD := 0)
  · intro _ _ tb _ _ _ _ _ _ sb hΓ hvl hlr hwf
    exact coreSim_goB h tb sb hΓ hvl hlr hwf
      (inVD := 0) (inVE := .empty) (outVD := 0) (outLD := 0)

/-! ## 6. `SweepKL` PHOAS Simulation Combinators (`sweepKLSim_mutual`) -/

/-- PHOAS half of a `StdKLSpec` paired with an executable `SweepKL`. -/
structure SweepSim {W : Ty → Type} {S : Type} (sw : OptFlatPlanKit.SweepKL W S) where
  mkW : (t : Ty) → Nat → Nat → W t
  bindSingle : {t : Ty} → Nat → K t → W t
  bindTup : (ts : List Ty) → Nat → Tup K ts → Tup W ts
  mkW_eq : ∀ t inD outD, sw.freshLoad outD t = mkW t inD outD
  bindSingle_eq : ∀ t inD outD, bindSingle (t := t) outD outD = mkW t inD outD
  bindTup_eq : ∀ ts inD outD,
    bindTup ts outD (Tup.levels ts outD) = OptFlatPlanKit.mkFreshTup mkW ts inD outD
  freshTup_eq : ∀ ts outD, sw.freshTup ts outD = bindTup ts outD (Tup.levels ts outD)
  outArgs : {ts : List Ty} → S → Tup (Arg W) ts → Tup (Arg K) ts
  outArgs_eq : ∀ s {ts} (args : Tup (Arg W) ts),
    outArgs s args = OptFlatPlanKit.mapArgTup sw.argOut args
  phoasE : {rs : List Ty} → S → Nat → Expr W KL rs → Expr K KL rs
  phoasB : {rs : List Ty} → {sig : List (List Ty)} → S → Nat →
    Blocks W KL rs sig → Blocks K KL rs sig
  hlt_p : ∀ {rs} (s : S) (outD : Nat), phoasE (rs := rs) s outD .hlt = .hlt
  ret_p : ∀ {rs} (s : S) (outD : Nat) (vs' : Tup (Arg W) rs),
    phoasE (rs := rs) s outD (.ret vs') = .ret (sw.termArgs s vs')
  exit_p : ∀ {rs as} (s : S) (outD : Nat) (f : Sym) (args : Tup (Arg W) as),
    phoasE (rs := rs) s outD (.exit f args) = .exit f (sw.termArgs s args)
  jump_p : ∀ {rs ts} (s : S) (outD : Nat) (l : KL ts) (args : Tup (Arg W) ts),
    phoasE (rs := rs) s outD (.jump l args) = .jump l (sw.termArgs s args)
  store_p : ∀ {rs t} (s : S) (outD : Nat) (v : Arg W t) (a : Arg W i64) (k : Expr W KL rs),
    phoasE s outD (.store v a k) = .store (sw.argOut v) (sw.argOut a) (phoasE s outD k)
  load_p : ∀ {rs} (s : S) (outD : Nat) (t : Ty) (a : Arg W i64) (k : W t → Expr W KL rs),
    phoasE s outD (.load t a k) =
      .load t (sw.argOut a) (fun x => phoasE s (outD + 1) (k (bindSingle outD x)))
  call_p : ∀ {rs as bs} (s : S) (outD : Nat) (f : Sym) (args : Tup (Arg W) as)
      (k : Tup W bs → Expr W KL rs),
    phoasE s outD (.call f args k) =
      .call f (outArgs s args) (fun xs => phoasE s (outD + bs.length) (k (bindTup bs outD xs)))
  group_p : ∀ {rs sig} (s : S) (outD : Nat)
      (bs : Tup KL sig → Blocks W KL rs sig) (k : Tup KL sig → Expr W KL rs),
    phoasE s outD (.group bs k) =
      .group (fun ls' => phoasB s outD (bs ls')) (fun ls' => phoasE s outD (k ls'))
  nil_p : ∀ {rs} (s : S) (outD : Nat), phoasB (rs := rs) s outD .nil = .nil
  cons_p : ∀ {rs ts sig} (s : S) (outD : Nat)
      (b : Tup W ts → Expr W KL rs) (bs : Blocks W KL rs sig),
    phoasB s outD (.cons b bs) =
      .cons (fun xs => phoasE s (outD + ts.length) (b (bindTup ts outD xs))) (phoasB s outD bs)

/-- Derive `SweepKL` mutual simulation from `SweepSim`, `.let_`, and `.jnz` obligations. -/
theorem sweepKLSim_mutual {W : Ty → Type} {S : Type} {sw : OptFlatPlanKit.SweepKL W S}
    (sp : SweepSim sw)
    (hLet : ∀ {rs ts : List Ty} (s : S) (op : Op K ts) (k : TFlat rs)
      {Γ Δ vs ls inD outD inE},
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → checkArgs Γ op.args = true →
      k.wfCheck (pushTypes ts Γ) Δ = true →
      (∀ {Γ' vs' inD' outD' inE'} (s' : S),
        CtxTypes Γ' vs' → TrieCtxMatch inD' inE' vs' → k.wfCheck Γ' Δ = true →
        toTFlat (sp.phoasE s' outD' (denote W KL k vs' ls)) outD' ls.length =
          sw.run k inD' inE' outD' s') →
      toTFlat (sp.phoasE s outD (denote W KL (.let_ op k) vs ls)) outD ls.length =
        sw.run (.let_ op k) inD inE outD s)
    (hJnz : ∀ {rs : List Ty} (s : S) (c : Arg K .bool) (t e : TFlat rs)
      {Γ Δ vs ls inD outD inE},
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → checkArg Γ .bool c = true →
      t.wfCheck Γ Δ = true → e.wfCheck Γ Δ = true →
      (∀ (s' : S), t.wfCheck Γ Δ = true →
        toTFlat (sp.phoasE s' outD (denote W KL t vs ls)) outD ls.length =
          sw.run t inD inE outD s') →
      (∀ (s' : S), e.wfCheck Γ Δ = true →
        toTFlat (sp.phoasE s' outD (denote W KL e vs ls)) outD ls.length =
          sw.run e inD inE outD s') →
      toTFlat (sp.phoasE s outD (denote W KL (.jnz c t e) vs ls)) outD ls.length =
        sw.run (.jnz c t e) inD inE outD s) :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (s : S),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (sp.phoasE s outD (denote W KL tf vs ls)) outD ls.length =
        sw.run tf inD inE outD s) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD outD inE} (s : S),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (sp.phoasB s outD (denoteB W KL tb vs ls)) outD ls.length =
        sw.runB tb inD inE outD s) := by
  refine klSim_mutual ⟨
    fun s op k hΓ hΔ hll hm hwf ih => by
      have ⟨ha, hk⟩ := wf_let hwf
      exact hLet s op k hΓ hΔ hll hm ha hk ih,
    @fun _ _ _ _ _ inD _ _ s t a k hΓ _ _ hm hwf ih => by
      have ⟨ha, hk⟩ := wf_load hwf
      simp only [denote]
      rw [OptFlatPlanKit.denoteArg_eq_some_resolveEnvArg hΓ hm a ha sw.dflt]
      dsimp only [OptFlatPlanKit.SweepKL.run]
      rw [sp.load_p, sp.mkW_eq t inD _]; simp only [toTFlat]; rw [sp.bindSingle_eq]
      exact congrArg (TFlat.load t _)
        (ih s (CtxTypes.cons hΓ) (trieCtxMatch_singleton hm _ _) hk),
    fun s v a k hΓ _ _ hm hwf ih => by
      have ⟨hv, ha, hk⟩ := wf_store hwf
      simp only [denote]
      rw [OptFlatPlanKit.denoteArg_eq_some_resolveEnvArg hΓ hm v hv sw.dflt,
          OptFlatPlanKit.denoteArg_eq_some_resolveEnvArg hΓ hm a ha sw.dflt]
      dsimp only [OptFlatPlanKit.SweepKL.run]
      rw [sp.store_p]; simp only [toTFlat]
      exact congrArg (TFlat.store _ _) (ih s hΓ hm hk),
    fun s f bs args k hΓ _ _ hm hwf ih => by
      have ⟨ha, hk⟩ := wf_call hwf
      simp only [denote]
      rw [OptFlatPlanKit.denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha sw.dflt]
      dsimp only [OptFlatPlanKit.SweepKL.run]
      rw [sp.call_p, sp.outArgs_eq s _, sp.freshTup_eq]; simp only [toTFlat]
      exact congrArg (TFlat.call f bs _)
        (ih s (OptFlatPlanKit.ctxTypes_pushTup_rev _ hΓ)
          (OptFlatPlanKit.trieCtxMatch_insertTupEnv hm _) hk),
    fun s c t e hΓ hΔ hll hm hwf iht ihe => by
      have ⟨hc, ht, he⟩ := wf_jnz hwf
      exact hJnz s c t e hΓ hΔ hll hm hc ht he iht ihe,
    fun s j args hΓ hΔ hll hm hwf => by
      have ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨lvl, hlvl, hidx⟩ := OptFlatPlanKit.lookupL_jump_eq hΔ hll hj
      simp only [denote]
      rw [hlvl, OptFlatPlanKit.denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha sw.dflt]
      dsimp only [OptFlatPlanKit.SweepKL.run]
      rw [sp.jump_p]; simp only [toTFlat]; rw [hidx],
    fun s vs' hΓ _ _ hm hwf => by
      simp only [denote]
      rw [OptFlatPlanKit.denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf sw.dflt]
      dsimp only [OptFlatPlanKit.SweepKL.run]
      rw [sp.ret_p]; rfl,
    fun s f args hΓ _ _ hm hwf => by
      simp only [denote]
      rw [OptFlatPlanKit.denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf sw.dflt]
      dsimp only [OptFlatPlanKit.SweepKL.run]
      rw [sp.exit_p]; rfl,
    fun s _ _ _ _ _ => by
      simp only [denote]; dsimp only [OptFlatPlanKit.SweepKL.run]; rw [sp.hlt_p]; rfl,
    fun s bodies k _ hΔ hll _ hwf ihB ihK => by
      have ⟨hb_wf, hk_wf⟩ := wf_group hwf
      simp only [denote]; dsimp only [OptFlatPlanKit.SweepKL.run]; rw [sp.group_p]
      simp only [toTFlat]
      have hb := ihB s (OptFlatPlanKit.ctxTypes_pushTup_rev _ hΔ) hll.pushTup hb_wf
      have hk := ihK s (OptFlatPlanKit.ctxTypes_pushTup_rev _ hΔ) hll.pushTup hk_wf
      simp only [pushTup_length] at hb hk; rw [hb, hk],
    fun sb _ _ _ _ _ => by
      simp only [denoteB]; dsimp only [OptFlatPlanKit.SweepKL.runB]; rw [sp.nil_p]; rfl,
    fun sb b bs hΓ _ _ hm hwf ihb ihbs => by
      have ⟨hb, hbs⟩ := wf_cons hwf
      simp only [denoteB]; dsimp only [OptFlatPlanKit.SweepKL.runB]
      rw [sp.cons_p, sp.freshTup_eq]; simp only [toTBlocks]
      rw [ihb sb (OptFlatPlanKit.ctxTypes_pushTup_rev _ hΓ)
        (OptFlatPlanKit.trieCtxMatch_insertTupEnv hm _) hb, ihbs sb hbs]⟩

/-- Discharges `hJnz` for `sweepKLSim_mutual` when `.jnz` emits `(sw.argOut c)`. -/
theorem sweepKL_jnz_plain {W : Ty → Type} {S : Type} {sw : OptFlatPlanKit.SweepKL W S}
    (sp : SweepSim sw) (hOn : ∀ s c, sw.onJnz s c = .emit (sw.argOut c) s s)
    (hp : ∀ {rs} s outD (c : Arg W .bool) (t e : Expr W KL rs),
      sp.phoasE s outD (.jnz c t e) =
        .jnz (sw.argOut c) (sp.phoasE s outD t) (sp.phoasE s outD e))
    {rs : List Ty} (s : S) (c : Arg K .bool) (t e : TFlat rs)
    {Γ Δ vs ls inD outD inE}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inD inE vs) (hc : checkArg Γ .bool c = true)
    (ht : t.wfCheck Γ Δ = true) (he : e.wfCheck Γ Δ = true)
    (iht : ∀ (s' : S), t.wfCheck Γ Δ = true →
      toTFlat (sp.phoasE s' outD (denote W KL t vs ls)) outD ls.length =
        sw.run t inD inE outD s')
    (ihe : ∀ (s' : S), e.wfCheck Γ Δ = true →
      toTFlat (sp.phoasE s' outD (denote W KL e vs ls)) outD ls.length =
        sw.run e inD inE outD s') :
    toTFlat (sp.phoasE s outD (denote W KL (.jnz c t e) vs ls)) outD ls.length =
      sw.run (.jnz c t e) inD inE outD s := by
  simp only [denote]
  rw [OptFlatPlanKit.denoteArg_eq_some_resolveEnvArg hΓ hm c hc sw.dflt]
  dsimp only [OptFlatPlanKit.SweepKL.run]
  rw [hp, hOn]; simp only [toTFlat]; rw [iht s ht, ihe s he]

/-- Discharges `hJnz` for `sweepKLSim_mutual` when `.jnz` folds constant `sw.argOut c`. -/
theorem sweepKL_jnz_const {W : Ty → Type} {S : Type} {sw : OptFlatPlanKit.SweepKL W S}
    (sp : SweepSim sw) (pushT : S → S := id) (pushF : S → S := id)
    (hOn : ∀ s c, sw.onJnz s c = match sw.argOut c with
      | .imm true => .takeT (pushT s)
      | .imm false => .takeF (pushF s)
      | .var v => .emit (.var v) (pushT s) (pushF s))
    (hp : ∀ {rs} s outD (c : Arg W .bool) (t e : Expr W KL rs),
      sp.phoasE s outD (.jnz c t e) =
        match sw.argOut c with
        | .imm true => sp.phoasE (pushT s) outD t
        | .imm false => sp.phoasE (pushF s) outD e
        | .var v =>
          .jnz (.var v) (sp.phoasE (pushT s) outD t) (sp.phoasE (pushF s) outD e))
    {rs : List Ty} (s : S) (c : Arg K .bool) (t e : TFlat rs)
    {Γ Δ vs ls inD outD inE}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inD inE vs) (hc : checkArg Γ .bool c = true)
    (ht : t.wfCheck Γ Δ = true) (he : e.wfCheck Γ Δ = true)
    (iht : ∀ (s' : S), t.wfCheck Γ Δ = true →
      toTFlat (sp.phoasE s' outD (denote W KL t vs ls)) outD ls.length =
        sw.run t inD inE outD s')
    (ihe : ∀ (s' : S), e.wfCheck Γ Δ = true →
      toTFlat (sp.phoasE s' outD (denote W KL e vs ls)) outD ls.length =
        sw.run e inD inE outD s') :
    toTFlat (sp.phoasE s outD (denote W KL (.jnz c t e) vs ls)) outD ls.length =
      sw.run (.jnz c t e) inD inE outD s := by
  simp only [denote]
  rw [OptFlatPlanKit.denoteArg_eq_some_resolveEnvArg hΓ hm c hc sw.dflt]
  dsimp only [OptFlatPlanKit.SweepKL.run]
  rw [hp, hOn]
  cases sw.argOut (OptFlatPlanKit.resolveEnvArg inD inE c sw.dflt) with
  | imm b => cases b with | true => exact iht (pushT s) ht | false => exact ihe (pushF s) he
  | var _ => simp only [toTFlat]; rw [iht (pushT s) ht, ihe (pushF s) he]

end
end LeanQbe.T.OptFlatSimKit
