module

public import LeanQbe.T.OptFlatPathCond
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.CondThreadOptLemmas1

/-!
# Equivalence Proofs for `OptFlatPathCond` (`pathCondOptFlat_eq`)

Proves exact `=` correspondence (`std3` axioms only) between the native `TFlat` pass
`OptFlatPathCond.pathCondOptFlat` and `Func.pathCondOpt`:

* `OptFlatPathCond.pathCondOptFlat_eq`
* `OptFlatPathCond.denoteFunc_pathCondOptFlat`
* `OptFlatPathCond.pathCondOptFlat_wfCheck`
* `OptFlatPathCond.pathCondOptFlatFn_toFn`
* `OptFlatPathCond.pathCondOptFlatFn_wfCheck`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatPathCond

open OptFlatPlanKit
open CondThreadOpt

private theorem pathCondOpt_let_eq {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (facts : List BoolFact) (op : Op (PVal V) ts)
    (k : Tup (PVal V) ts → Expr (PVal V) L rs) :
    CondThreadOpt.pathCondOpt next facts (.let_ op k) =
      match pcStep op facts next with
      | .elim res => CondThreadOpt.pathCondOpt next facts (k res)
      | .emit op' wrap =>
        .let_ op' fun xs => CondThreadOpt.pathCondOpt (next + ts.length) facts (k (wrap xs)) := by
  rw [CondThreadOpt.pathCondOpt.eq_def]
  dsimp only
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
  rw [CondThreadOpt.pathCondOpt.eq_def]
  dsimp only
  cases resolveBool? facts c with
  | none => rfl
  | some b => cases b <;> rfl

mutual
private theorem pathCondOptFlatAux_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × PVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {facts : List BoolFact} → {inDepth depth : Nat} →
    {inEnv : Trie ((t : Ty) × PVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tf.wfCheck Γ Δ = true →
    toTFlat (CondThreadOpt.pathCondOpt depth facts (denote (PVal K) KL tf vs ls))
        depth ls.length =
      pathCondOptFlatAux facts tf inDepth inEnv depth
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, facts, inDepth, depth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [pathCondOptFlatAux.eq_def]
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1]
    dsimp only
    rw [pathCondOpt_let_eq]
    cases hst : pcStep ⟨op.code, resolveEnvArgs inDepth inEnv op.args⟩ facts depth with
    | elim res =>
      dsimp only
      exact pathCondOptFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm _) hwf.2
    | emit op' wrap =>
      dsimp only [toTFlat]
      exact congrArg (TFlat.let_ _)
        (pathCondOptFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll
          (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .load t a k, Γ, Δ, vs, ls, facts, inDepth, depth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [pathCondOptFlatAux, denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1]
    dsimp only; rw [CondThreadOpt.pathCondOpt.eq_def]; dsimp only [toTFlat]
    exact congrArg (TFlat.load t _)
      (pathCondOptFlatAux_eq k (.cons hΓ) hΔ hll (hm.cons t _) hwf.2)
  | .store v a k, Γ, Δ, vs, ls, facts, inDepth, depth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [pathCondOptFlatAux, denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1.2]
    dsimp only; rw [CondThreadOpt.pathCondOpt.eq_def]; dsimp only [toTFlat]
    exact congrArg (TFlat.store _ _) (pathCondOptFlatAux_eq k hΓ hΔ hll hm hwf.2)
  | .call f bs args k, Γ, Δ, vs, ls, facts, inDepth, depth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [pathCondOptFlatAux, denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.1]
    dsimp only; rw [CondThreadOpt.pathCondOpt.eq_def]; dsimp only [toTFlat]
    exact congrArg (TFlat.call f bs _)
      (pathCondOptFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .jnz c t e, Γ, Δ, vs, ls, facts, inDepth, depth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [pathCondOptFlatAux.eq_def]
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1]
    dsimp only
    rw [pathCondOpt_jnz_eq]
    cases hc : resolveBool? facts (resolveEnvArg inDepth inEnv c) with
    | some b =>
      cases b with
      | true => exact pathCondOptFlatAux_eq t hΓ hΔ hll hm hwf.1.2
      | false => exact pathCondOptFlatAux_eq e hΓ hΔ hll hm hwf.2
    | none =>
      dsimp only [toTFlat]
      rw [pathCondOptFlatAux_eq t hΓ hΔ hll hm hwf.1.2,
        pathCondOptFlatAux_eq e hΓ hΔ hll hm hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, facts, inDepth, depth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    dsimp only [pathCondOptFlatAux, denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.2]
    dsimp only; rw [CondThreadOpt.pathCondOpt.eq_def]; dsimp only [toTFlat]
    rw [hidx]
  | .ret vs', Γ, _, vs, ls, facts, inDepth, depth, inEnv, hΓ, _, _, hm, hwf => by
    dsimp only [pathCondOptFlatAux, denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf]
    rfl
  | .exit f args, Γ, _, vs, ls, facts, inDepth, depth, inEnv, hΓ, _, _, hm, hwf => by
    dsimp only [pathCondOptFlatAux, denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, facts, inDepth, depth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [pathCondOptFlatAux, denote]
    rw [CondThreadOpt.pathCondOpt.eq_def]; dsimp only [toTFlat]
    have hb := pathCondOptFlatAuxB_eq bodies hΓ
      (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hm hwf.1
      (facts := facts) (depth := depth)
    have hk := pathCondOptFlatAux_eq k hΓ
      (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hm hwf.2
      (facts := facts) (depth := depth)
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    rw [hb, hk]

private theorem pathCondOptFlatAuxB_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × PVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {facts : List BoolFact} → {inDepth depth : Nat} →
    {inEnv : Trie ((t : Ty) × PVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tb.wfCheck Γ Δ = true →
    toTBlocks (CondThreadOpt.pathCondOptB depth facts (denoteB (PVal K) KL tb vs ls))
        depth ls.length =
      pathCondOptFlatAuxB facts tb inDepth inEnv depth
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, facts, inDepth, depth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [pathCondOptFlatAuxB, denoteB, CondThreadOpt.pathCondOptB, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact pathCondOptFlatAux_eq b (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm _) hwf.1
    · exact pathCondOptFlatAuxB_eq bs hΓ hΔ hll hm hwf.2
end

/-- `pathCondOptFlat as tf = reifyFunc (Func.pathCondOpt (denoteFunc tf))` under
`wfCheck = true`. -/
theorem pathCondOptFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    pathCondOptFlat as tf = reifyFunc (Func.pathCondOpt (denoteFunc (as := as) tf)) := by
  dsimp only [pathCondOptFlat, Func.pathCondOpt]
  have h := pathCondOptFlatAux_eq tf (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv (fun {t} x next => PVal.fresh t x next) as) hwf
    (facts := []) (depth := as.length)
  exact h.symm

/-- `denoteFunc (pathCondOptFlat as tf) = Func.pathCondOpt (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_pathCondOptFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (pathCondOptFlat as tf) =
      Func.pathCondOpt (denoteFunc (as := as) tf) := by
  rw [pathCondOptFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.pathCondOpt_wf (Func.wf_of_denote tf rfl))

/-- `pathCondOptFlat` preserves `wfCheck`. -/
theorem pathCondOptFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (pathCondOptFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [pathCondOptFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.pathCondOpt_wf (Func.wf_of_denote tf rfl))

/-- `(pathCondOptFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.pathCondOpt f.toFn.body⟩`
under `wfCheck = true`. -/
theorem pathCondOptFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (pathCondOptFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.pathCondOpt f.toFn.body⟩ := by
  dsimp only [pathCondOptFlatFn, TFlatFn.toFn]
  rw [denoteFunc_pathCondOptFlat f.body hwf]

/-- `pathCondOptFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem pathCondOptFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (pathCondOptFlatFn f).wfCheck = true :=
  pathCondOptFlat_wfCheck f.body hwf

end OptFlatPathCond
end LeanQbe.T
