/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.OptFlatValue
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.FoldLemmas
import LeanQbe.T.CopyLemmas
import LeanQbe.T.CanonLemmas
import LeanQbe.T.GvnLemmas

/-!
# `OptFlatValueLemmas`: Simulation & Equivalence Proofs for `OptFlatValue`

Proves exact `TFlat` structural correspondence (`reifyFunc (Func.<pass> (denoteFunc tf))`),
`wfCheck` preservation, and `denoteFunc` congruence for `foldFlat`, `copyFlat`, `canonFlat`,
and `gvnFlat` via `OptFlatSimKit.sweepKLSim_mutual`.
-/

set_option autoImplicit false

namespace LeanQbe.T
namespace OptFlatValue

open OptFlatPlanKit OptFlatSimKit

private theorem recMap_eq_mapArgTup {W : Ty → Type}
    (f : ∀ {t : Ty}, Arg W t → Arg K t)
    (g : {ts : List Ty} → Tup (Arg W) ts → Tup (Arg K) ts)
    (hnil : g (ts := []) () = ())
    (hcons : ∀ {t ts} (a : Arg W t) (as : Tup (Arg W) ts),
      g (ts := t :: ts) (a, as) = (f a, g as)) :
    ∀ {ts : List Ty} (args : Tup (Arg W) ts), g args = mapArgTup f args
  | [], () => hnil
  | _ :: _, (a, as) => by rw [hcons, recMap_eq_mapArgTup f g hnil hcons as]; rfl

private theorem tupMapArg_fout_eq {ts : List Ty} (args : Tup (Arg (FVal K)) ts) :
    tupMapArg (fun _ => Arg.fout) args = mapArgTup Arg.fout args :=
  recMap_eq_mapArgTup Arg.fout _ rfl (fun _ _ => rfl) args

/-! ## 1. `foldFlat` Simulation Proofs -/

private theorem fold_let_eq {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (op : Op (FVal V) ts) (k : Tup (FVal V) ts → Expr (FVal V) L rs) :
    fold next (.let_ op k) =
      match op.simpAct with
      | some act => fold next (k (act.apply op.args))
      | none =>
        match op.simpProv? with
        | some res => fold next (k res)
        | none =>
          .let_ op.foldRewrite fun xs => fold (next + ts.length) (k (op.foldWrap next xs)) := by
  rw [fold.eq_def]; dsimp only
  cases op.simpAct with
  | some _ => rfl
  | none => cases op.simpProv? <;> rfl

private abbrev foldSpec : SweepSim foldSweep where
  mkW _ _ o := FVal.fresh o o
  bindSingle d v := FVal.fresh v d
  bindTup ts d xs := freshFVals ts xs d
  mkW_eq _ _ _ := rfl
  bindSingle_eq _ _ _ := rfl
  bindTup_eq := tupFreshWith_self_eq_mkFreshTup (fun {t} => FVal.fresh) _ (fun _ _ _ => rfl)
  freshTup_eq _ _ := rfl
  outArgs _ args := tupMapArg (fun _ => Arg.fout) args
  outArgs_eq _ {_} args := by dsimp only [foldSweep]; exact tupMapArg_fout_eq args
  phoasE _ d e := fold d e
  phoasB _ d b := foldB d b
  hlt_p _ _ := by rw [fold.eq_def]
  ret_p _ _ _ := by rw [fold.eq_def]; simp only [foldSweep, tupMapArg_fout_eq]
  exit_p _ _ _ _ := by rw [fold.eq_def]; simp only [foldSweep, tupMapArg_fout_eq]
  jump_p _ _ _ _ := by rw [fold.eq_def]; simp only [foldSweep, tupMapArg_fout_eq]
  store_p _ _ _ _ _ := by rw [fold.eq_def]; rfl
  load_p _ _ _ _ _ := by rw [fold.eq_def]; rfl
  call_p _ _ _ _ _ := by rw [fold.eq_def]
  group_p _ _ _ _ := by rw [fold.eq_def]
  nil_p _ _ := by rw [foldB.eq_def]
  cons_p _ _ _ _ := by rw [foldB.eq_def]

private theorem foldFlatAux_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (fold outD (denote (FVal K) KL tf vs ls)) outD ls.length =
        foldSweep.run tf inD inE outD ()) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD outD inE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (foldB outD (denoteB (FVal K) KL tb vs ls)) outD ls.length =
        foldSweep.runB tb inD inE outD ()) := by
  refine sweepKLSim_mutual foldSpec ?_ ?_
  · intro rs ts _ op k Γ Δ vs ls inD outD inE hΓ _ _ hm hargs hk ih
    simp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hargs]
    dsimp only [SweepKL.run, foldSweep]
    rw [fold_let_eq]; dsimp only
    let fOp : Op (FVal K) ts := ⟨op.code, resolveEnvArgs inD inE op.args⟩
    cases hs : fOp.simpAct with
    | some act =>
      dsimp only
      exact ih () (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk
    | none =>
      dsimp only
      cases hp : fOp.simpProv? with
      | some res =>
        dsimp only
        exact ih () (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk
      | none =>
        simp only [toTFlat]
        exact congrArg (TFlat.let_ _)
          (ih () (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk)
  · intro rs _ c t e Γ Δ vs ls inD outD inE hΓ _ _ hm hc ht he iht ihe
    exact sweepKL_jnz_const foldSpec id id
      (fun _ _ => rfl)
      (fun _ _ c t e => by
        dsimp only; rw [fold.eq_def]; dsimp only [foldSweep]
        cases c.fout with | imm b => cases b <;> rfl | var _ => rfl)
      () c t e hΓ hm hc ht he iht ihe

public section

theorem foldFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    foldFlat as tf = reifyFunc (Func.fold (denoteFunc (as := as) tf)) :=
  (foldFlatAux_both.1 tf () (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv FVal.fresh as) hwf).symm

flat_pass_corollaries foldFlat, Func.fold, Func.fold_wf,
  foldFlat_eq, denoteFunc_foldFlat, foldFlat_wfCheck,
  foldFlatFn, foldFlatFn_toFn, foldFlatFn_wfCheck

end

/-! ## 2. `copyFlat` Simulation Proofs -/

private theorem mkpairEmitStep_emit_next {V : Ty → Type} {b next' : Nat} {a b' : Ty}
    {cx : CVal V a} {cy : CVal V b'} {op' : Op V [.pair a b']}
    {wrap : Tup V [.pair a b'] → Tup (CVal V) [.pair a b']}
    (h : mkpairEmitStep b a b' cx cy = .emit op' next' wrap) :
    next' = b + ([Ty.pair a b']).length := by
  dsimp only [mkpairEmitStep] at h; cases h; rfl

private theorem mkpairProjStep_emit_next {V : Ty → Type} {b next' : Nat} {a b' : Ty}
    {cx : CVal V a} {cy : CVal V b'} {op' : Op V [.pair a b']}
    {wrap : Tup V [.pair a b'] → Tup (CVal V) [.pair a b']}
    (h : mkpairProjStep b a b' cx cy = .emit op' next' wrap) :
    next' = b + ([Ty.pair a b']).length := by
  dsimp only [mkpairProjStep] at h
  split at h
  · split at h
    · split at h
      · cases h
      · exact mkpairEmitStep_emit_next h
    · exact mkpairEmitStep_emit_next h
  · exact mkpairEmitStep_emit_next h

private theorem copyLet_emit_next {V : Ty → Type} {ts : List Ty} (op : Op (CVal V) ts)
    (b next' : Nat) (op' : Op V ts) (wrap : Tup V ts → Tup (CVal V) ts)
    (h : op.copyLet b = .emit op' next' wrap) :
    next' = b + ts.length := by
  rcases op with ⟨code, args⟩
  cases code with
  | copy _ => rcases args with ⟨_, ⟨⟩⟩; dsimp only [Op.copyLet] at h; cases h
  | unpair a b' =>
    rcases args with ⟨p, ⟨⟩⟩; dsimp only [Op.copyLet] at h
    cases hp : p.toCVal.parts <;> simp only [hp] at h
    · cases h; rfl
    · cases h
  | mkpair a b' =>
    rcases args with ⟨x, y, ⟨⟩⟩; dsimp only [Op.copyLet, mkpairStep] at h
    split at h
    · cases h
    · exact mkpairProjStep_emit_next h
  | _ => all_goals (dsimp only [Op.copyLet] at h; cases h; rfl)

private theorem copy_let_eq {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (op : Op (CVal V) ts) (k : Tup (CVal V) ts → Expr (CVal V) L rs) :
    copy next (.let_ op k) =
      match op.copyLet next with
      | .elim res => copy next (k res)
      | .emit op' next' wrap => .let_ op' fun xs => copy next' (k (wrap xs)) := by
  rw [copy.eq_def]; dsimp only
  cases op.copyLet next <;> rfl

private theorem tupCOut_eq {ts : List Ty} (args : Tup (Arg (CVal K)) ts) :
    tupCOut args = mapArgTup Arg.cout args :=
  recMap_eq_mapArgTup Arg.cout _ rfl (fun _ _ => rfl) args

private abbrev copySpec : SweepSim copySweep where
  mkW _ _ o := CVal.fresh o o
  bindSingle d v := CVal.fresh v d
  bindTup ts d xs := freshCVals ts xs d
  mkW_eq _ _ _ := rfl
  bindSingle_eq _ _ _ := rfl
  bindTup_eq := tupFreshWith_self_eq_mkFreshTup (fun {t} => CVal.fresh) _ (fun _ _ _ => rfl)
  freshTup_eq _ _ := rfl
  outArgs _ args := tupCOut args
  outArgs_eq _ {_} args := by dsimp only [copySweep]; exact tupCOut_eq args
  phoasE _ d e := copy d e
  phoasB _ d b := copyB d b
  hlt_p _ _ := by rw [copy.eq_def]
  ret_p _ _ _ := by rw [copy.eq_def]; simp only [copySweep, tupCOut_eq]
  exit_p _ _ _ _ := by rw [copy.eq_def]; simp only [copySweep, tupCOut_eq]
  jump_p _ _ _ _ := by rw [copy.eq_def]; simp only [copySweep, tupCOut_eq]
  store_p _ _ _ _ _ := by rw [copy.eq_def]; rfl
  load_p _ _ _ _ _ := by rw [copy.eq_def]; rfl
  call_p _ _ _ _ _ := by rw [copy.eq_def]
  group_p _ _ _ _ := by rw [copy.eq_def]
  nil_p _ _ := by rw [copyB.eq_def]
  cons_p _ _ _ _ := by rw [copyB.eq_def]

private theorem copyFlatAux_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (copy outD (denote (CVal K) KL tf vs ls)) outD ls.length =
        copySweep.run tf inD inE outD ()) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD outD inE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (copyB outD (denoteB (CVal K) KL tb vs ls)) outD ls.length =
        copySweep.runB tb inD inE outD ()) := by
  refine sweepKLSim_mutual copySpec ?_ ?_
  · intro rs ts _ op k Γ Δ vs ls inD outD inE hΓ _ _ hm hargs hk ih
    simp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hargs]
    dsimp only [SweepKL.run, copySweep]
    rw [copy_let_eq]
    cases hst : ({ code := op.code, args := resolveEnvArgs inD inE op.args } :
        Op (CVal K) ts).copyLet outD with
    | elim res =>
      dsimp only
      exact ih () (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk
    | emit op' next' wrap =>
      have hnext := copyLet_emit_next _ outD next' op' wrap hst
      simp only [toTFlat]; rw [← hnext]
      exact congrArg (TFlat.let_ _)
        (ih () (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk)
  · intro rs _ c t e Γ Δ vs ls inD outD inE hΓ _ _ hm hc ht he iht ihe
    exact sweepKL_jnz_plain copySpec (fun _ _ => rfl)
      (fun _ _ _ _ _ => by dsimp only; rw [copy.eq_def]; rfl)
      () c t e hΓ hm hc ht he iht ihe

public section

theorem copyFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    copyFlat as tf = reifyFunc (Func.copy (denoteFunc (as := as) tf)) :=
  (copyFlatAux_both.1 tf () (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv CVal.fresh as) hwf).symm

flat_pass_corollaries copyFlat, Func.copy, Func.copy_wf,
  copyFlat_eq, denoteFunc_copyFlat, copyFlat_wfCheck,
  copyFlatFn, copyFlatFn_toFn, copyFlatFn_wfCheck

end

/-! ## 3. `canonFlat` Simulation Proofs -/

private theorem tupCnOut_eq {ts : List Ty} (args : Tup (Arg (CanonVal K)) ts) :
    tupCnOut args = mapArgTup Arg.cnout args :=
  recMap_eq_mapArgTup Arg.cnout _ rfl (fun _ _ => rfl) args

private abbrev canonSpec : SweepSim canonSweep where
  mkW _ _ o := CanonVal.fresh o o
  bindSingle d v := CanonVal.fresh v d
  bindTup ts d xs := freshCanonVals ts xs d
  mkW_eq _ _ _ := rfl
  bindSingle_eq _ _ _ := rfl
  bindTup_eq := tupFreshWith_self_eq_mkFreshTup (fun {t} => CanonVal.fresh) _ (fun _ _ _ => rfl)
  freshTup_eq _ _ := rfl
  outArgs _ args := tupCnOut args
  outArgs_eq _ {_} args := by dsimp only [canonSweep]; exact tupCnOut_eq args
  phoasE _ d e := canon d e
  phoasB _ d b := canonB d b
  hlt_p _ _ := by rw [canon.eq_def]
  ret_p _ _ _ := by rw [canon.eq_def]; simp only [canonSweep, tupCnOut_eq]
  exit_p _ _ _ _ := by rw [canon.eq_def]; simp only [canonSweep, tupCnOut_eq]
  jump_p _ _ _ _ := by rw [canon.eq_def]; simp only [canonSweep, tupCnOut_eq]
  store_p _ _ _ _ _ := by rw [canon.eq_def]; rfl
  load_p _ _ _ _ _ := by rw [canon.eq_def]; rfl
  call_p _ _ _ _ _ := by rw [canon.eq_def]
  group_p _ _ _ _ := by rw [canon.eq_def]
  nil_p _ _ := by rw [canonB.eq_def]
  cons_p _ _ _ _ := by rw [canonB.eq_def]

private theorem canonFlatAux_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (canon outD (denote (CanonVal K) KL tf vs ls)) outD ls.length =
        canonSweep.run tf inD inE outD ()) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD outD inE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (canonB outD (denoteB (CanonVal K) KL tb vs ls)) outD ls.length =
        canonSweep.runB tb inD inE outD ()) := by
  refine sweepKLSim_mutual canonSpec ?_ ?_
  · intro rs ts _ op k Γ Δ vs ls inD outD inE hΓ _ _ hm hargs hk ih
    simp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hargs]
    dsimp only [SweepKL.run, canonSweep]
    rw [canon.eq_def]
    simp only [toTFlat]
    exact congrArg (TFlat.let_ _)
      (ih () (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk)
  · intro rs _ c t e Γ Δ vs ls inD outD inE hΓ _ _ hm hc ht he iht ihe
    exact sweepKL_jnz_plain canonSpec (fun _ _ => rfl)
      (fun _ _ _ _ _ => by dsimp only; rw [canon.eq_def]; rfl)
      () c t e hΓ hm hc ht he iht ihe

public section

theorem canonFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    canonFlat as tf = reifyFunc (Func.canon (denoteFunc (as := as) tf)) :=
  (canonFlatAux_both.1 tf () (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv CanonVal.fresh as) hwf).symm

flat_pass_corollaries canonFlat, Func.canon, Func.canon_wf,
  canonFlat_eq, denoteFunc_canonFlat, canonFlat_wfCheck,
  canonFlatFn, canonFlatFn_toFn, canonFlatFn_wfCheck

end

/-! ## 4. `gvnFlat` Simulation Proofs -/

private theorem gvn_let_eq {V : Ty → Type} {L : List Ty → Type} {sig ts rs : List Ty}
    (next : Nat) (tbl : GvnTbl V) (code : OpCode sig ts) (args : Tup (Arg (GVal V)) sig)
    (k : Tup (GVal V) ts → Expr (GVal V) L rs) :
    gvn next tbl (.let_ ⟨code, args⟩ k) =
      match tbl.find sig ts code (tupGKey args) with
      | some cached => gvn next tbl (k cached)
      | none =>
        .let_ ⟨code, tupGOut args⟩ fun xs =>
          let gs := freshGVals ts xs next
          gvn (next + ts.length) (tbl.insert sig ts code (tupGKey args) gs) (k gs) := by
  rw [gvn.eq_def]; dsimp only
  cases tbl.find sig ts code (tupGKey args) <;> rfl

private theorem tupGOut_eq {ts : List Ty} (args : Tup (Arg (GVal K)) ts) :
    tupGOut args = mapArgTup Arg.gout args :=
  recMap_eq_mapArgTup Arg.gout _ rfl (fun _ _ => rfl) args

private abbrev gvnSpec : SweepSim gvnSweep where
  mkW _ _ o := (o, o)
  bindSingle d v := (v, d)
  bindTup ts d xs := freshGVals ts xs d
  mkW_eq _ _ _ := rfl
  bindSingle_eq _ _ _ := rfl
  bindTup_eq := tupFreshWith_self_eq_mkFreshTup (fun {t} x n => (x, n)) _ (fun _ _ _ => rfl)
  freshTup_eq _ _ := rfl
  outArgs _ args := tupGOut args
  outArgs_eq _ {_} args := by dsimp only [gvnSweep]; exact tupGOut_eq args
  phoasE tbl d e := gvn d tbl e
  phoasB tbl d b := gvnB d tbl b
  hlt_p _ _ := by rw [gvn.eq_def]
  ret_p _ _ _ := by rw [gvn.eq_def]; simp only [gvnSweep, tupGOut_eq]
  exit_p _ _ _ _ := by rw [gvn.eq_def]; simp only [gvnSweep, tupGOut_eq]
  jump_p _ _ _ _ := by rw [gvn.eq_def]; simp only [gvnSweep, tupGOut_eq]
  store_p _ _ _ _ _ := by rw [gvn.eq_def]; rfl
  load_p _ _ _ _ _ := by rw [gvn.eq_def]; rfl
  call_p _ _ _ _ _ := by rw [gvn.eq_def]
  group_p _ _ _ _ := by rw [gvn.eq_def]
  nil_p _ _ := by rw [gvnB.eq_def]
  cons_p _ _ _ _ := by rw [gvnB.eq_def]

private theorem gvnFlatAux_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (tbl : GvnTbl K),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (gvn outD tbl (denote (GVal K) KL tf vs ls)) outD ls.length =
        gvnSweep.run tf inD inE outD tbl) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD outD inE} (tbl : GvnTbl K),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (gvnB outD tbl (denoteB (GVal K) KL tb vs ls)) outD ls.length =
        gvnSweep.runB tb inD inE outD tbl) := by
  refine sweepKLSim_mutual gvnSpec ?_ ?_
  · intro rs ts tbl op k Γ Δ vs ls inD outD inE hΓ _ _ hm hargs hk ih
    simp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hargs]
    dsimp only [SweepKL.run, gvnSweep]
    rw [gvn_let_eq]
    cases hf : tbl.find op.sig ts op.code (tupGKey (resolveEnvArgs inD inE op.args)) with
    | some cached =>
      dsimp only
      exact ih tbl (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk
    | none =>
      simp only [toTFlat]
      exact congrArg (TFlat.let_ _)
        (ih _ (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk)
  · intro rs tbl c t e Γ Δ vs ls inD outD inE hΓ _ _ hm hc ht he iht ihe
    exact sweepKL_jnz_plain gvnSpec (fun _ _ => rfl)
      (fun _ _ _ _ _ => by dsimp only; rw [gvn.eq_def]; rfl)
      tbl c t e hΓ hm hc ht he iht ihe

public section

theorem gvnFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    gvnFlat as tf = reifyFunc (Func.gvn (denoteFunc (as := as) tf)) :=
  (gvnFlatAux_both.1 tf .empty (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv (fun x next => (x, next)) as) hwf).symm

flat_pass_corollaries gvnFlat, Func.gvn, Func.gvn_wf,
  gvnFlat_eq, denoteFunc_gvnFlat, gvnFlat_wfCheck,
  gvnFlatFn, gvnFlatFn_toFn, gvnFlatFn_wfCheck

end

end OptFlatValue
end LeanQbe.T
