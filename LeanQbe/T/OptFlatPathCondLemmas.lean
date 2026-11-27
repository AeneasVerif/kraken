/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.OptFlatPathCond
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.CondThreadOptLemmas1

/-!
# `OptFlatPathCondLemmas`: Simulation & Equivalence Proofs for `OptFlatPathCond`

Proves exact `TFlat` structural parity (`pathCondOptFlat_eq`), `denoteFunc` congruence
(`denoteFunc_pathCondOptFlat`), and `wfCheck` preservation (`pathCondOptFlat_wfCheck`) for
`pathCondOptFlat` via `OptFlatSimKit.sweepKLSim_mutual`.
-/

set_option autoImplicit false

namespace LeanQbe.T
namespace OptFlatPathCond

open CondThreadOpt OptFlatPlanKit OptFlatSimKit

private theorem pathCondOpt_let_eq {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (facts : List BoolFact) (op : Op (PVal V) ts)
    (k : Tup (PVal V) ts → Expr (PVal V) L rs) :
    CondThreadOpt.pathCondOpt next facts (.let_ op k) =
      match pcStep op facts next with
      | .elim res => CondThreadOpt.pathCondOpt next facts (k res)
      | .emit op' wrap =>
        .let_ op' fun xs => CondThreadOpt.pathCondOpt (next + ts.length) facts (k (wrap xs)) := by
  rw [CondThreadOpt.pathCondOpt.eq_def]; dsimp only
  cases pcStep op facts next <;> rfl

private theorem pathCondOpt_jnz_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (facts : List BoolFact)
    (c : Arg (PVal V) .bool) (t e : Expr (PVal V) L rs) :
    CondThreadOpt.pathCondOpt next facts (.jnz c t e) =
      match resolveBool? facts c with
      | some true => CondThreadOpt.pathCondOpt next facts t
      | some false => CondThreadOpt.pathCondOpt next facts e
      | none =>
        let info := pInfo c
        .jnz (pOut c)
          (CondThreadOpt.pathCondOpt next (pushFacts info.tf facts) t)
          (CondThreadOpt.pathCondOpt next (pushFacts info.ff facts) e) := by
  rw [CondThreadOpt.pathCondOpt.eq_def]; dsimp only
  cases resolveBool? facts c with | none => rfl | some b => cases b <;> rfl

private theorem tupPOut_eq :
    {ts : List Ty} → (args : Tup (Arg (PVal K)) ts) → tupPOut args = mapArgTup pOut args
  | [], () => rfl
  | _ :: _, (_, as) => congrArg (_, ·) (tupPOut_eq as)

private abbrev pathCondSpec : SweepSim pathCondSweep where
  mkW t _ o := PVal.fresh t o o
  bindSingle {t} d v := PVal.fresh t v d
  bindTup ts d xs := freshPVals ts xs d
  mkW_eq _ _ _ := rfl
  bindSingle_eq _ _ _ := rfl
  bindTup_eq :=
    tupFreshWith_self_eq_mkFreshTup (fun {t} x n => PVal.fresh t x n) _ (fun _ _ _ => rfl)
  freshTup_eq _ _ := rfl
  outArgs _ args := tupPOut args
  outArgs_eq _ {_} args := by dsimp only [pathCondSweep]; exact tupPOut_eq args
  phoasE facts d e := CondThreadOpt.pathCondOpt d facts e
  phoasB facts d b := CondThreadOpt.pathCondOptB d facts b
  hlt_p _ _ := by rw [CondThreadOpt.pathCondOpt.eq_def]
  ret_p _ _ _ := by rw [CondThreadOpt.pathCondOpt.eq_def]; rfl
  exit_p _ _ _ _ := by rw [CondThreadOpt.pathCondOpt.eq_def]; rfl
  jump_p _ _ _ _ := by rw [CondThreadOpt.pathCondOpt.eq_def]; rfl
  store_p _ _ _ _ _ := by rw [CondThreadOpt.pathCondOpt.eq_def]; rfl
  load_p _ _ _ _ _ := by rw [CondThreadOpt.pathCondOpt.eq_def]; rfl
  call_p _ _ _ _ _ := by rw [CondThreadOpt.pathCondOpt.eq_def]
  group_p _ _ _ _ := by rw [CondThreadOpt.pathCondOpt.eq_def]
  nil_p _ _ := by rw [CondThreadOpt.pathCondOptB.eq_def]
  cons_p _ _ _ _ := by rw [CondThreadOpt.pathCondOptB.eq_def]

private theorem pathCondOptFlatAux_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (facts : List BoolFact),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (CondThreadOpt.pathCondOpt outD facts (denote (PVal K) KL tf vs ls))
          outD ls.length =
        pathCondSweep.run tf inD inE outD facts) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD outD inE} (facts : List BoolFact),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (CondThreadOpt.pathCondOptB outD facts (denoteB (PVal K) KL tb vs ls))
          outD ls.length =
        pathCondSweep.runB tb inD inE outD facts) := by
  refine sweepKLSim_mutual pathCondSpec ?_ ?_
  · intro rs ts facts op k Γ Δ vs ls inD outD inE hΓ _ _ hm hargs hk ih
    simp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hargs]
    dsimp only [SweepKL.run, pathCondSweep]
    rw [pathCondOpt_let_eq]
    cases hst : pcStep ⟨op.code, resolveEnvArgs inD inE op.args⟩ facts outD with
    | elim res =>
      dsimp only
      exact ih facts (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk
    | emit op' wrap =>
      simp only [toTFlat]
      exact congrArg (TFlat.let_ _)
        (ih facts (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk)
  · intro rs facts c t e Γ Δ vs ls inD outD inE hΓ _ _ hm hc ht he iht ihe
    simp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hc]
    dsimp only [SweepKL.run, pathCondSweep]
    rw [pathCondOpt_jnz_eq]; dsimp only
    cases hc' : resolveBool? facts (resolveEnvArg inD inE c) with
    | some b =>
      cases b with
      | true => exact iht facts ht
      | false => exact ihe facts he
    | none =>
      simp only [toTFlat]
      rw [iht _ ht, ihe _ he]
      rfl

public section

theorem pathCondOptFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    pathCondOptFlat as tf = reifyFunc (Func.pathCondOpt (denoteFunc (as := as) tf)) :=
  (pathCondOptFlatAux_both.1 tf [] (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv (fun {t} x n => PVal.fresh t x n) as) hwf).symm

flat_pass_corollaries pathCondOptFlat, Func.pathCondOpt, Func.pathCondOpt_wf,
  pathCondOptFlat_eq, denoteFunc_pathCondOptFlat, pathCondOptFlat_wfCheck,
  pathCondOptFlatFn, pathCondOptFlatFn_toFn, pathCondOptFlatFn_wfCheck

end

end OptFlatPathCond
end LeanQbe.T
