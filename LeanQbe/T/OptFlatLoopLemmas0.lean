module

public import LeanQbe.T.OptFlatLoop
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.LicmLemmas
import LeanQbe.T.LicmRoLemmas

/-!
# LICM Equivalence Proofs for `OptFlatLoop` (`licmFlat_eq`)

Proves exact `=` correspondence (`std3` axioms only) between native `TFlat`
`OptFlatLoop.licmPureFlat` / `OptFlatLoop.licmFlat` and `Func.licmPure` / `Func.licm`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatLoop

open OptFlatPlanKit

/-! ## 1. Pure-Total LICM Equivalence (`licmPureFlat_eq`) -/

private theorem emitHoistsFlat_eq {rs : List Ty} :
    (hs : List HoistOp) → (next : Nat) → (env : VEnv K) → (tbl : GvnTbl K) →
    (outD lD : Nat) →
    (cont : Nat → VEnv K → GvnTbl K → Expr K KL rs) →
    (contFlat : Nat → VEnv K → GvnTbl K → Nat → TFlat rs) →
    (let r : HoistEmitRes rs := emitHoistsFlat hs next env tbl outD;
      toTFlat (cont r.next r.env r.tbl) r.outDepth lD =
        contFlat r.next r.env r.tbl r.outDepth) →
    toTFlat (emitHoists hs next env tbl cont) outD lD =
      let r : HoistEmitRes rs := emitHoistsFlat hs next env tbl outD
      r.wrap (contFlat r.next r.env r.tbl r.outDepth)
  | [], _, _, _, _, _, _, _, hcont => hcont
  | h :: rest, next, env, tbl, outD, lD, cont, contFlat, hcont => by
    dsimp only [emitHoists, emitHoistsFlat]
    dsimp only [emitHoistsFlat] at hcont
    cases hp : h.code.isLicmPure
    · simp only [hp] at hcont
      simpa [hp] using emitHoistsFlat_eq rest next env tbl outD lD cont contFlat hcont
    · simp only [hp, ite_true] at hcont
      simp only [ite_true]
      cases hf : tbl.find h.sig h.ts h.code h.args with
      | some _ =>
        rw [hf] at hcont; dsimp only at hcont
        exact emitHoistsFlat_eq rest next env tbl outD lD cont contFlat hcont
      | none =>
        rw [hf] at hcont; dsimp only at hcont
        cases hr : resolveArgs env h.args with
        | none =>
          rw [hr] at hcont; dsimp only at hcont
          exact emitHoistsFlat_eq rest next env tbl outD lD cont contFlat hcont
        | some vArgs =>
          rw [hr] at hcont; dsimp only at hcont
          dsimp only [toTFlat]
          refine congrArg (TFlat.let_ ⟨h.code, idxArgs outD vArgs⟩) ?_
          exact emitHoistsFlat_eq rest (next + h.ts.length)
            (envInsertTup env next (Tup.levels h.ts outD))
            (tbl.insert h.sig h.ts h.code h.args (freshGVals h.ts (Tup.levels h.ts outD) next))
            (outD + h.ts.length) lD cont contFlat hcont

private theorem insertTupEnv_eq_envInsertTup :
    {ts : List Ty} → (n : Nat) → (env : VEnv K) → (xs : Tup K ts) →
    insertTupEnv n env xs = envInsertTup env n xs
  | [], _, _, () => rfl
  | _ :: _, n, env, (x, xs) =>
    insertTupEnv_eq_envInsertTup (n + 1) (env.insert n ⟨_, x⟩) xs

mutual
private theorem licmSweepFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × GVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {next inD outD : Nat} → {env : VEnv K} → {tbl : GvnTbl K} →
    {inE : Trie ((t : Ty) × GVal K t)} → (plan : HoistPlan) →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
    toTFlat (licmSweep next env tbl plan (denote (GVal K) KL tf vs ls)) outD ls.length =
      licmSweepFlat next env tbl plan tf inD inE outD
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1
    dsimp only [denote, licmSweepFlat]
    rw [hargs]
    dsimp only
    rw [licmSweep.eq_def]
    dsimp only
    cases hfind : tbl.find op.sig ts op.code (tupGKey (resolveEnvArgs inD inE op.args)) with
    | some cached =>
      dsimp only
      exact licmSweepFlat_eq k _ (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm cached) hwf.2
    | none =>
      dsimp only [toTFlat]
      refine congrArg (TFlat.let_ _) ?_
      exact licmSweepFlat_eq k _ (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm (freshGVals ts (Tup.levels ts outD) next)) hwf.2
  | .load t a k, Γ, Δ, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1
    dsimp only [denote, licmSweepFlat]
    rw [ha]
    dsimp only
    rw [licmSweep.eq_def]
    dsimp only [toTFlat]
    refine congrArg (TFlat.load t _) ?_
    exact licmSweepFlat_eq k _ (.cons hΓ) hΔ hll
      (hm.cons t (outD, next)) hwf.2
  | .store v a k, Γ, Δ, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hv := denoteArg_eq_some_resolveEnvArg hΓ hm v hwf.1.1
    have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1.2
    dsimp only [denote, licmSweepFlat]
    rw [hv, ha]
    dsimp only
    rw [licmSweep.eq_def]
    dsimp only [toTFlat]
    exact congrArg (TFlat.store _ _) (licmSweepFlat_eq k _ hΓ hΔ hll hm hwf.2)
  | .call f bs args k, Γ, Δ, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.1
    dsimp only [denote, licmSweepFlat]
    rw [hargs]
    dsimp only
    rw [licmSweep.eq_def]
    dsimp only [toTFlat]
    refine congrArg (TFlat.call f bs _) ?_
    exact licmSweepFlat_eq k _ (CtxTypes.push _ hΓ) hΔ hll
      (trieCtxMatch_insertTupEnv hm (freshGVals bs (Tup.levels bs outD) next)) hwf.2
  | .jnz c t e, Γ, Δ, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hc := denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1
    dsimp only [denote, licmSweepFlat]
    rw [hc]
    dsimp only
    rw [licmSweep.eq_def]
    dsimp only [toTFlat]
    exact congr (congrArg (TFlat.jnz _) (licmSweepFlat_eq t _ hΓ hΔ hll hm hwf.1.2))
      (licmSweepFlat_eq e _ hΓ hΔ hll hm hwf.2)
  | .jump j args, Γ, Δ, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.2
    dsimp only [denote, licmSweepFlat]
    rw [hlk, hargs]
    dsimp only
    rw [licmSweep.eq_def]
    dsimp only [toTFlat]
    rw [hidx]
  | .ret vs', Γ, _, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, _, _, hm, hwf => by
    have hvs := denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf
    dsimp only [denote, licmSweepFlat]
    rw [hvs]
    dsimp only
    rw [licmSweep.eq_def]
    rfl
  | .exit f args, Γ, _, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, _, _, hm, hwf => by
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf
    dsimp only [denote, licmSweepFlat]
    rw [hargs]
    dsimp only
    rw [licmSweep.eq_def]
    dsimp only
    rfl
  | .hlt, _, _, _, ls, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote, licmSweepFlat]
    rw [licmSweep.eq_def]
    rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, next, inD, outD, env, tbl, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote, licmSweepFlat]
    rw [licmSweep.eq_def]
    dsimp only
    let p := match plan with
      | .groupNode hs bsP kP => (hs, bsP, kP)
      | _ => ([], .nil, .leaf)
    refine emitHoistsFlat_eq p.1 next env tbl outD ls.length _
      (fun n' e' t' od' =>
        .group (licmSweepBFlat n' e' t' p.2.1 bodies inD inE od')
          (licmSweepFlat n' e' t' p.2.2 k inD inE od')) ?_
    dsimp only [toTFlat]
    have hb := licmSweepBFlat_eq bodies p.2.1 hΓ
      (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hm hwf.1
      (next := (emitHoistsFlat (rs := rs) p.1 next env tbl outD).next)
      (env := (emitHoistsFlat (rs := rs) p.1 next env tbl outD).env)
      (tbl := (emitHoistsFlat (rs := rs) p.1 next env tbl outD).tbl)
      (outD := (emitHoistsFlat (rs := rs) p.1 next env tbl outD).outDepth)
    have hk := licmSweepFlat_eq k p.2.2 hΓ
      (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hm hwf.2
      (next := (emitHoistsFlat (rs := rs) p.1 next env tbl outD).next)
      (env := (emitHoistsFlat (rs := rs) p.1 next env tbl outD).env)
      (tbl := (emitHoistsFlat (rs := rs) p.1 next env tbl outD).tbl)
      (outD := (emitHoistsFlat (rs := rs) p.1 next env tbl outD).outDepth)
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    exact congr (congrArg TFlat.group hb) hk

private theorem licmSweepBFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × GVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {next inD outD : Nat} → {env : VEnv K} → {tbl : GvnTbl K} →
    {inE : Trie ((t : Ty) × GVal K t)} → (bsPlan : HoistBlocks) →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
    toTBlocks (licmSweepB next env tbl bsPlan (denoteB (GVal K) KL tb vs ls)) outD ls.length =
      licmSweepBFlat next env tbl bsPlan tb inD inE outD
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, next, inD, outD, env, tbl, inE, bsPlan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, licmSweepBFlat, licmSweepB, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact licmSweepFlat_eq b _ (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm (freshGVals ts (Tup.levels ts outD) next)) hwf.1
    · exact licmSweepBFlat_eq bs _ hΓ hΔ hll hm hwf.2
end

private theorem trieCtxMatch_init_licm (as : List Ty) :
    TrieCtxMatch as.length (initEnv (fun {t} (x : K t) next => ((x, next) : GVal K t)) as)
      (pushTup (freshGVals as (Tup.levels as 0) 0) []) := by
  -- Check if `freshGVals as (Tup.levels as 0) 0` agrees with `trieCtxMatch_initEnv`!
  have h := trieCtxMatch_initEnv (fun {t} (x : K t) next => ((x, next) : GVal K t)) as
  exact h

/-- `licmPureFlat as tf = reifyFunc (Func.licmPure (denoteFunc tf))` under `wfCheck = true`. -/
theorem licmPureFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    licmPureFlat as tf = reifyFunc (Func.licmPure (denoteFunc (as := as) tf)) := by
  dsimp only [licmPureFlat, Func.licmPure]
  have hr : reifyFunc (denoteFunc (as := as) tf) = tf := reifyFunc_denoteFunc_eq tf hwf
  rw [hr]
  split
  · have h := licmSweepFlat_eq tf (Licm.buildHoistPlan as.length tf)
      (CtxTypes.push _ .nil) .nil CtxLevels.nil (trieCtxMatch_init_licm as) hwf
      (next := as.length) (env := insertTupEnv 0 .empty (Tup.levels as 0))
      (tbl := .empty) (outD := as.length)
    dsimp only [reifyFunc, denoteFunc]
    rw [← insertTupEnv_eq_envInsertTup]
    exact h.symm
  · exact hr.symm

/-- `licmPureFlat` preserves `wfCheck`. -/
theorem licmPureFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (licmPureFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [licmPureFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.licmPure_wf (Func.wf_of_denote tf rfl))

/-! ## 2. Read-Only Load LICM Equivalence (`roSweepFlat_eq`, `licmFlat_eq`) -/

private theorem emitRoHoistsFlat_eq {rs : List Ty} :
    (hs : List HoistLoad) → (next : Nat) → (env : VEnv K) → (outD lD : Nat) →
    (cont : Nat → VEnv K → Expr K KL rs) →
    (contFlat : Nat → VEnv K → Nat → TFlat rs) →
    (let r : RoEmitRes rs := emitRoHoistsFlat hs next env outD;
      toTFlat (cont r.next r.env) r.outDepth lD = contFlat r.next r.env r.outDepth) →
    toTFlat (emitRoHoists hs next env cont) outD lD =
      let r : RoEmitRes rs := emitRoHoistsFlat hs next env outD
      r.wrap (contFlat r.next r.env r.outDepth)
  | [], _, _, _, _, _, _, hcont => hcont
  | h :: rest, next, env, outD, lD, cont, contFlat, hcont => by
    dsimp only [emitRoHoists, emitRoHoistsFlat]
    dsimp only [emitRoHoistsFlat] at hcont
    cases hres : resolveArg env h.addr with
    | none =>
      rw [hres] at hcont; dsimp only at hcont
      exact emitRoHoistsFlat_eq rest next env outD lD cont contFlat hcont
    | some va =>
      rw [hres] at hcont; dsimp only at hcont
      dsimp only [toTFlat]
      refine congrArg (TFlat.load h.ty _) ?_
      exact emitRoHoistsFlat_eq rest (next + 1) (env.insert next ⟨h.ty, outD⟩)
        (outD + 1) lD cont contFlat hcont

mutual
private theorem roSweepFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {next inD outD : Nat} → {env : VEnv K} →
    {inE : Trie ((t : Ty) × K t)} → (plan : RoPlan) →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
    toTFlat (roSweep next env plan (denote K KL tf vs ls)) outD ls.length =
      roSweepFlat next env plan tf inD inE outD
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1
    dsimp only [denote, roSweepFlat]
    rw [hargs]
    dsimp only
    rw [roSweep.eq_def]
    dsimp only [toTFlat]
    refine congrArg (TFlat.let_ _) ?_
    exact roSweepFlat_eq k _ (CtxTypes.push _ hΓ) hΔ hll
      (trieCtxMatch_insertTupEnv hm (Tup.levels ts outD)) hwf.2
  | .load t a k, Γ, Δ, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1
    dsimp only [denote]
    rw [ha]
    dsimp only
    rw [roSweep.eq_def]
    cases plan with
    | fwdLoad lvl kPlan =>
      dsimp only [roSweepFlat]
      cases hfind : env.find? lvl with
      | none =>
        dsimp only [toTFlat]
        refine congrArg (TFlat.load t _) ?_
        exact roSweepFlat_eq k kPlan (.cons hΓ) hΔ hll (hm.cons t outD) hwf.2
      | some p =>
        rcases p with ⟨t', v⟩
        dsimp only
        split
        · exact roSweepFlat_eq k kPlan (.cons hΓ) hΔ hll (hm.cons t _) hwf.2
        · dsimp only [toTFlat]
          refine congrArg (TFlat.load t _) ?_
          exact roSweepFlat_eq k kPlan (.cons hΓ) hΔ hll (hm.cons t outD) hwf.2
    | leaf | node1 _ | node2 _ _ | groupNode _ _ _ =>
      dsimp only [roSweepFlat, toTFlat]
      refine congrArg (TFlat.load t _) ?_
      exact roSweepFlat_eq k _ (.cons hΓ) hΔ hll (hm.cons t outD) hwf.2
  | .store v a k, Γ, Δ, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hv := denoteArg_eq_some_resolveEnvArg hΓ hm v hwf.1.1
    have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1.2
    dsimp only [denote, roSweepFlat]
    rw [hv, ha]
    dsimp only
    rw [roSweep.eq_def]
    dsimp only [toTFlat]
    exact congrArg (TFlat.store _ _) (roSweepFlat_eq k _ hΓ hΔ hll hm hwf.2)
  | .call f bs args k, Γ, Δ, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.1
    dsimp only [denote, roSweepFlat]
    rw [hargs]
    dsimp only
    rw [roSweep.eq_def]
    dsimp only [toTFlat]
    refine congrArg (TFlat.call f bs _) ?_
    exact roSweepFlat_eq k _ (CtxTypes.push _ hΓ) hΔ hll
      (trieCtxMatch_insertTupEnv hm (Tup.levels bs outD)) hwf.2
  | .jnz c t e, Γ, Δ, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hc := denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1
    dsimp only [denote, roSweepFlat]
    rw [hc]
    dsimp only
    rw [roSweep.eq_def]
    dsimp only [toTFlat]
    exact congr (congrArg (TFlat.jnz _) (roSweepFlat_eq t _ hΓ hΔ hll hm hwf.1.2))
      (roSweepFlat_eq e _ hΓ hΔ hll hm hwf.2)
  | .jump j args, Γ, Δ, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.2
    dsimp only [denote, roSweepFlat]
    rw [hlk, hargs]
    dsimp only
    rw [roSweep.eq_def]
    dsimp only [toTFlat]
    rw [hidx]
  | .ret vs', Γ, _, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, _, _, hm, hwf => by
    have hvs := denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf
    dsimp only [denote, roSweepFlat]
    rw [hvs]
    dsimp only
    rw [roSweep.eq_def]
    rfl
  | .exit f args, Γ, _, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, _, _, hm, hwf => by
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf
    dsimp only [denote, roSweepFlat]
    rw [hargs]
    dsimp only
    rw [roSweep.eq_def]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote, roSweepFlat]
    rw [roSweep.eq_def]
    rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote, roSweepFlat]
    rw [roSweep.eq_def]
    dsimp only
    let p := match plan with
      | .groupNode hs bsP kP => (hs, bsP, kP)
      | _ => ([], .nil, .leaf)
    refine emitRoHoistsFlat_eq p.1 next env outD ls.length _
      (fun n' e' od' =>
        .group (roSweepBFlat n' e' p.2.1 bodies inD inE od')
          (roSweepFlat n' e' p.2.2 k inD inE od')) ?_
    dsimp only [toTFlat]
    have hb := roSweepBFlat_eq bodies p.2.1 hΓ
      (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hm hwf.1
      (next := (emitRoHoistsFlat (rs := rs) p.1 next env outD).next)
      (env := (emitRoHoistsFlat (rs := rs) p.1 next env outD).env)
      (outD := (emitRoHoistsFlat (rs := rs) p.1 next env outD).outDepth)
    have hk := roSweepFlat_eq k p.2.2 hΓ
      (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hm hwf.2
      (next := (emitRoHoistsFlat (rs := rs) p.1 next env outD).next)
      (env := (emitRoHoistsFlat (rs := rs) p.1 next env outD).env)
      (outD := (emitRoHoistsFlat (rs := rs) p.1 next env outD).outDepth)
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    exact congr (congrArg TFlat.group hb) hk

private theorem roSweepBFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {next inD outD : Nat} → {env : VEnv K} →
    {inE : Trie ((t : Ty) × K t)} → (plan : RoBlocks) →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
    toTBlocks (roSweepB next env plan (denoteB K KL tb vs ls)) outD ls.length =
      roSweepBFlat next env plan tb inD inE outD
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, next, inD, outD, env, inE, plan,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, roSweepBFlat, roSweepB, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact roSweepFlat_eq b _ (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm (Tup.levels ts outD)) hwf.1
    · exact roSweepBFlat_eq bs _ hΓ hΔ hll hm hwf.2
end

/-- `licmFlat as tf = reifyFunc (Func.licm (denoteFunc tf))` under `wfCheck = true`. -/
theorem licmFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    licmFlat as tf = reifyFunc (Func.licm (denoteFunc (as := as) tf)) := by
  dsimp only [licmFlat, Func.licm]
  have hwf1 : (licmPureFlat as tf).wfCheck (pushTypes as []) [] = true :=
    licmPureFlat_wfCheck tf hwf
  have hp1 := licmPureFlat_eq tf hwf
  have hf1 : Func.licmPure (denoteFunc (as := as) tf) =
      denoteFunc (as := as) (licmPureFlat as tf) := by
    rw [hp1]
    exact (Func.renorm_eq_self (Func.licmPure_wf (Func.wf_of_denote tf rfl))).symm
  rw [hf1]
  rw [reifyFunc_denoteFunc_eq (licmPureFlat as tf) hwf1]
  split
  · have hr := roSweepFlat_eq (licmPureFlat as tf)
      (Licm.buildRoPlan as.length (licmPureFlat as tf))
      (CtxTypes.push _ .nil) .nil CtxLevels.nil
      (trieCtxMatch_insertTupEnv .empty (Tup.levels as 0)) hwf1
      (next := as.length) (env := insertTupEnv 0 .empty (Tup.levels as 0)) (outD := as.length)
    let tf2 := roSweepFlat as.length (insertTupEnv 0 .empty (Tup.levels as 0))
      (Licm.buildRoPlan as.length (licmPureFlat as tf)) (licmPureFlat as tf)
      as.length (insertTupEnv 0 .empty (Tup.levels as 0)) as.length
    have hro : reifyFunc (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs)
        (Licm.buildRoPlan as.length (licmPureFlat as tf))
        (denoteFunc (as := as) (licmPureFlat as tf) V L xs)) = tf2 := by
      dsimp only [reifyFunc, denoteFunc]
      rw [← insertTupEnv_eq_envInsertTup]
      simpa using hr
    have hwfRo : Func.Wf (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs)
        (Licm.buildRoPlan as.length (licmPureFlat as tf))
        (denoteFunc (as := as) (licmPureFlat as tf) V L xs)) := by
      have hwfF : (denoteFunc (as := as) (licmPureFlat as tf)).Wf :=
        Func.wf_of_denote (as := as) (licmPureFlat as tf) rfl
      have h := roSweepFunc_wf hwfF
      rwa [reifyFunc_denoteFunc_eq (licmPureFlat as tf) hwf1] at h
    have hwf2 : tf2.wfCheck (pushTypes as []) [] = true := by
      rw [← hro]
      exact PassFlatKit.reifyFunc_wfCheck hwfRo
    have hdf2 : (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs)
        (Licm.buildRoPlan as.length (licmPureFlat as tf))
        (denoteFunc (as := as) (licmPureFlat as tf) V L xs)) =
        denoteFunc (as := as) tf2 := by
      rw [← hro]
      exact (Func.renorm_eq_self hwfRo).symm
    change licmPureFlat as tf2 = _
    rw [hdf2]
    exact licmPureFlat_eq tf2 hwf2
  · exact (reifyFunc_denoteFunc_eq (licmPureFlat as tf) hwf1).symm

/-- `denoteFunc (licmFlat as tf) = Func.licm (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_licmFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (licmFlat as tf) = Func.licm (denoteFunc (as := as) tf) := by
  rw [licmFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.licm_wf (Func.wf_of_denote tf rfl))

/-- `licmFlat` preserves `wfCheck`. -/
theorem licmFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (licmFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [licmFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.licm_wf (Func.wf_of_denote tf rfl))

/-- `(licmFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.licm f.toFn.body⟩` under `wfCheck = true`. -/
theorem licmFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (licmFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.licm f.toFn.body⟩ := by
  dsimp only [licmFlatFn, TFlatFn.toFn]
  rw [denoteFunc_licmFlat f.body hwf]

/-- `licmFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem licmFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (licmFlatFn f).wfCheck = true :=
  licmFlat_wfCheck f.body hwf

end OptFlatLoop
end LeanQbe.T
