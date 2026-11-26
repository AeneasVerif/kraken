module

public import LeanQbe.T.OptFlatAddrRange
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.AddrRangeOptLemmas

/-!
# Equivalence Proofs for `OptFlatAddrRange` (`addrRangeOptFlat_eq`)

Proves exact `=` correspondence (`std3` axioms only) between the native `TFlat` pass
`OptFlatAddrRange.addrRangeOptFlat` and `Func.addrRangeOpt`:

* `OptFlatAddrRange.addrRangeOptFlat_eq`
* `OptFlatAddrRange.denoteFunc_addrRangeOptFlat`
* `OptFlatAddrRange.addrRangeOptFlat_wfCheck`
* `OptFlatAddrRange.addrRangeOptFlatFn_toFn`
* `OptFlatAddrRange.addrRangeOptFlatFn_wfCheck`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatAddrRange

open OptFlatPlanKit

private theorem idxArg_imm_eq {t : Ty} (d : Nat) (c : Val t) :
    idxArg d (.imm c : Arg K t) = .imm c := rfl

private theorem idxArg_succ_self {t : Ty} (d : Nat) :
    idxArg (d + 1) (.var d : Arg K t) = .var 0 := by
  dsimp only [idxArg]
  have hlt : d < d + 1 := by omega
  simp [hlt]

private theorem idxArg_add2_self {t : Ty} (d : Nat) :
    idxArg (d + 1 + 1) (.var d : Arg K t) = .var 1 := by
  dsimp only [idxArg]
  have hlt : d < d + 1 + 1 := by omega
  simp [hlt]

private theorem arSweep_let_eq {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (curD next : Nat) (plan : LoopTree) (op : Op (ARVal V) ts)
    (k : Tup (ARVal V) ts → Expr (ARVal V) L rs) :
    addrRangeSweep curD next plan (.let_ op k) =
      let kPlan := plan.step1
      match op.arStep curD next with
      | .elim res => addrRangeSweep curD next kPlan (k res)
      | .emit1 op' wrap =>
        .let_ op' fun xs => addrRangeSweep curD (next + ts.length) kPlan (k (wrap xs))
      | .rangeSubCmp w o x lo width outD =>
        .let_ (op2 (.sub (.bits w)) x (.imm lo)) fun (t, ()) =>
        .let_ (op2 (.cmp o (.bits w)) (.var t) (.imm width)) fun (r, ()) =>
        addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh r next outD, ()))
      | .addrShl n isSub base inv iv ivD sh _ disp =>
        .let_ (op2 (.shl (.bits n)) inv (.imm (BitVec.ofNat n sh))) fun (t1, ()) =>
        .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base (.var t1))
          fun (t2, ()) =>
        .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
        if disp == 0#n then
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t4 next ivD, ()))
        else
          .let_ (op2 (.add (.bits n)) (.var t4) (.imm disp)) fun (t5, ()) =>
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t5 next ivD, ()))
      | .addrPlain n isSub base inv iv invD ivD disp =>
        .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base inv) fun (t1, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
        if disp == 0#n then
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t2, .var next, ivD,
              { addr? := some (.addVV (.var t1) invD iv ivD 0#n) }⟩, ()))
        else
          .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t3, ()) =>
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t3, .var next, ivD,
              { addr? := some (.addVV (.var t1) invD iv ivD disp) }⟩, ())) := by
  rw [addrRangeSweep.eq_def]
  dsimp only
  cases op.arStep curD next <;> rfl

private theorem arSweep_jnz_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (curD next : Nat) (plan : LoopTree) (c : Arg (ARVal V) .bool) (t e : Expr (ARVal V) L rs) :
    addrRangeSweep curD next plan (.jnz c t e) =
      let (pt, pe) := plan.step2
      match c.arOut with
      | .imm true => addrRangeSweep curD next pt t
      | .imm false => addrRangeSweep curD next pe e
      | .var v => .jnz (.var v) (addrRangeSweep curD next pt t)
          (addrRangeSweep curD next pe e) := by
  rw [addrRangeSweep.eq_def]
  dsimp only
  cases c.arOut with
  | imm b => cases b <;> rfl
  | var _ => rfl

mutual
private theorem addrRangeSweepFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × ARVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {curD next inDepth outDepth : Nat} → {plan : LoopTree} →
    {inEnv : Trie ((t : Ty) × ARVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tf.wfCheck Γ Δ = true →
    toTFlat (addrRangeSweep curD next plan (denote (ARVal K) KL tf vs ls)) outDepth ls.length =
      addrRangeSweepFlat curD next plan tf inDepth inEnv outDepth
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [addrRangeSweepFlat.eq_def]
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1]
    dsimp only
    rw [arSweep_let_eq]
    cases hst : (⟨op.code, resolveEnvArgs inDepth inEnv op.args⟩ : Op (ARVal K) ts).arStep
        curD next with
    | elim res =>
      dsimp only [applyARStep, id]
      exact addrRangeSweepFlat_eq k (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm _) hwf.2
    | emit1 op' wrap =>
      dsimp only [applyARStep, toTFlat]
      exact congrArg (TFlat.let_ _)
        (addrRangeSweepFlat_eq k (CtxTypes.push _ hΓ) hΔ hll
          (trieCtxMatch_insertTupEnv hm _) hwf.2)
    | rangeSubCmp w o x lo width outD =>
      simp only [applyARStep, toTFlat, idxArgs, op2, Tup.levels, List.length,
        idxArg_imm_eq, idxArg_succ_self, Nat.zero_add, Nat.add_assoc]
      exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
        (addrRangeSweepFlat_eq k (CtxTypes.push _ hΓ) hΔ hll
          (trieCtxMatch_insertTupEnv hm (ts := [.bool]) _) hwf.2))
    | addrShl n isSub base inv iv ivD sh hsh disp =>
      by_cases hdisp : (disp == 0#n) = true
      · simp only [applyARStep, hdisp, ↓reduceIte, toTFlat, idxArgs, op2, Tup.levels,
          List.length, idxArg_imm_eq, idxArg_succ_self, idxArg_add2_self,
          Nat.zero_add, Nat.add_assoc,
          show (1 : Nat) + 1 = 2 from rfl, show (1 : Nat) + 2 = 3 from rfl]
        exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
          (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
            (addrRangeSweepFlat_eq k (CtxTypes.push _ hΓ) hΔ hll
              (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hwf.2))))
      · simp only [applyARStep, hdisp, Bool.false_eq_true, ↓reduceIte, toTFlat, idxArgs,
          op2, Tup.levels, List.length, idxArg_imm_eq, idxArg_succ_self, idxArg_add2_self,
          Nat.zero_add, Nat.add_assoc,
          show (1 : Nat) + 1 = 2 from rfl, show (1 : Nat) + 3 = 4 from rfl]
        exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
          (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
            (addrRangeSweepFlat_eq k (CtxTypes.push _ hΓ) hΔ hll
              (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hwf.2)))))
    | addrPlain n isSub base inv iv invD ivD disp =>
      by_cases hdisp : (disp == 0#n) = true
      · simp only [applyARStep, hdisp, ↓reduceIte, toTFlat, idxArgs, op2, Tup.levels,
          List.length, idxArg_succ_self, Nat.zero_add, Nat.add_assoc]
        exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
          (addrRangeSweepFlat_eq k (CtxTypes.push _ hΓ) hΔ hll
            (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hwf.2))
      · simp only [applyARStep, hdisp, Bool.false_eq_true, ↓reduceIte, toTFlat, idxArgs,
          op2, Tup.levels, List.length, idxArg_imm_eq, idxArg_succ_self,
          Nat.zero_add, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl]
        exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
          (addrRangeSweepFlat_eq k (CtxTypes.push _ hΓ) hΔ hll
            (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hwf.2)))
  | .load t a k, Γ, Δ, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [addrRangeSweepFlat, denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1]
    dsimp only; rw [addrRangeSweep.eq_def]; dsimp only [toTFlat]
    exact congrArg (TFlat.load t _)
      (addrRangeSweepFlat_eq k (.cons hΓ) hΔ hll (hm.cons t _) hwf.2)
  | .store v a k, Γ, Δ, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [addrRangeSweepFlat, denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1.2]
    dsimp only; rw [addrRangeSweep.eq_def]; dsimp only [toTFlat]
    exact congrArg (TFlat.store _ _) (addrRangeSweepFlat_eq k hΓ hΔ hll hm hwf.2)
  | .call f bs args k, Γ, Δ, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [addrRangeSweepFlat, denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.1]
    dsimp only; rw [addrRangeSweep.eq_def]; dsimp only [toTFlat]
    exact congrArg (TFlat.call f bs _)
      (addrRangeSweepFlat_eq k (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .jnz c t e, Γ, Δ, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [addrRangeSweepFlat.eq_def]
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1]
    dsimp only
    rw [arSweep_jnz_eq]
    cases hc : (resolveEnvArg inDepth inEnv c).arOut with
    | imm b =>
      cases b with
      | true => exact addrRangeSweepFlat_eq t hΓ hΔ hll hm hwf.1.2
      | false => exact addrRangeSweepFlat_eq e hΓ hΔ hll hm hwf.2
    | var v =>
      dsimp only [toTFlat]
      rw [addrRangeSweepFlat_eq t hΓ hΔ hll hm hwf.1.2,
        addrRangeSweepFlat_eq e hΓ hΔ hll hm hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    dsimp only [addrRangeSweepFlat, denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.2]
    dsimp only; rw [addrRangeSweep.eq_def]; dsimp only [toTFlat]
    rw [hidx]
  | .ret vs', Γ, _, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, _, _, hm, hwf => by
    dsimp only [addrRangeSweepFlat, denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf]
    rfl
  | .exit f args, Γ, _, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, _, _, hm, hwf => by
    dsimp only [addrRangeSweepFlat, denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, curD, next, inDepth, outDepth, plan, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [addrRangeSweepFlat, denote]
    rw [addrRangeSweep.eq_def]; dsimp only [toTFlat]
    have hb := addrRangeSweepBFlat_eq bodies hΓ
      (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hm hwf.1
      (curD := curD) (next := next) (outDepth := outDepth) (bsPlan := plan.stepGroup.1)
    have hk := addrRangeSweepFlat_eq k hΓ
      (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hm hwf.2
      (curD := curD) (next := next) (outDepth := outDepth) (plan := plan.stepGroup.2)
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    rw [hb, hk]

private theorem addrRangeSweepBFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × ARVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {curD next inDepth outDepth : Nat} → {bsPlan : LoopBlocks} →
    {inEnv : Trie ((t : Ty) × ARVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tb.wfCheck Γ Δ = true →
    toTBlocks (addrRangeSweepB curD next bsPlan (denoteB (ARVal K) KL tb vs ls))
        outDepth ls.length =
      addrRangeSweepBFlat curD next bsPlan tb inDepth inEnv outDepth
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, curD, next, inDepth, outDepth, bsPlan, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [addrRangeSweepBFlat, denoteB, addrRangeSweepB, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact addrRangeSweepFlat_eq b (CtxTypes.push _ hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm _) hwf.1
    · exact addrRangeSweepBFlat_eq bs hΓ hΔ hll hm hwf.2
end

/-- `addrRangeOptFlat as tf = reifyFunc (Func.addrRangeOpt (denoteFunc tf))` under
`wfCheck = true`. -/
theorem addrRangeOptFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    addrRangeOptFlat as tf = reifyFunc (Func.addrRangeOpt (denoteFunc (as := as) tf)) := by
  dsimp only [addrRangeOptFlat, Func.addrRangeOpt]
  rw [reifyFunc_denoteFunc_eq tf hwf]
  by_cases hw : (AddrRangeOpt.buildLoopTree false tf).2 = true
  · simp only [hw, ↓reduceIte]
    have h := addrRangeSweepFlat_eq tf (CtxTypes.push _ .nil) .nil CtxLevels.nil
      (trieCtxMatch_initEnv (fun x next => ARVal.fresh x next 0) as) hwf
      (curD := 0) (next := as.length) (outDepth := as.length)
      (plan := (AddrRangeOpt.buildLoopTree false tf).1)
    exact h.symm
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    exact (reifyFunc_denoteFunc_eq tf hwf).symm

/-- `denoteFunc (addrRangeOptFlat as tf) = Func.addrRangeOpt (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_addrRangeOptFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (addrRangeOptFlat as tf) =
      Func.addrRangeOpt (denoteFunc (as := as) tf) := by
  rw [addrRangeOptFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.addrRangeOpt_wf (Func.wf_of_denote tf rfl))

/-- `addrRangeOptFlat` preserves `wfCheck`. -/
theorem addrRangeOptFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (addrRangeOptFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [addrRangeOptFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.addrRangeOpt_wf (Func.wf_of_denote tf rfl))

/-- `(addrRangeOptFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.addrRangeOpt f.toFn.body⟩`
under `wfCheck = true`. -/
theorem addrRangeOptFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (addrRangeOptFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.addrRangeOpt f.toFn.body⟩ := by
  dsimp only [addrRangeOptFlatFn, TFlatFn.toFn]
  rw [denoteFunc_addrRangeOptFlat f.body hwf]

/-- `addrRangeOptFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem addrRangeOptFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (addrRangeOptFlatFn f).wfCheck = true :=
  addrRangeOptFlat_wfCheck f.body hwf

end OptFlatAddrRange
end LeanQbe.T
