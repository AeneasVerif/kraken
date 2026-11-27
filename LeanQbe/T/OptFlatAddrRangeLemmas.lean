/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.OptFlatAddrRange
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.AddrRangeOptLemmas

/-!
# `OptFlatAddrRangeLemmas`: Simulation & Equivalence Proofs for `OptFlatAddrRange`

Proves exact `=` correspondence (`std3` axioms only) between the native `TFlat` pass
`OptFlatAddrRange.addrRangeOptFlat` and `Func.addrRangeOpt` via `OptFlatSimKit.klSim_mutual`.
-/

set_option autoImplicit false

namespace LeanQbe.T
namespace OptFlatAddrRange

open OptFlatPlanKit OptFlatSimKit

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
      let foldD := plan.foldDisp
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
        if disp == 0#n then
          .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t4 next ivD, ()))
        else if foldD then
          .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t2d, ()) =>
          .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t2d) (.var t3)) fun (t4, ()) =>
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t4 next ivD, ()))
        else
          .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t4) (.imm disp)) fun (t5, ()) =>
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t5 next ivD, ()))
      | .addrPlain n isSub base inv iv invD ivD disp =>
        .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base inv) fun (t1, ()) =>
        if disp == 0#n then
          .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t2, .var next, ivD,
              { addr? := some (.addVV (.var t1) invD iv ivD 0#n) }⟩, ()))
        else if foldD then
          .let_ (op2 (.add (.bits n)) (.var t1) (.imm disp)) fun (t1d, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t1d) iv) fun (t2, ()) =>
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t2, .var next, ivD,
              { addr? := some (.addVV (.var t1d) invD iv ivD 0#n) }⟩, ()))
        else
          .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
          .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t3, ()) =>
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t3, .var next, ivD,
              { addr? := some (.addVV (.var t1) invD iv ivD disp) }⟩, ())) := by
  rw [addrRangeSweep.eq_def]; dsimp only
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
  rw [addrRangeSweep.eq_def]; dsimp only
  cases c.arOut with | imm b => cases b <;> rfl | var _ => rfl

private theorem addrRangeSweepFlat_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE}
      (s : Nat × Nat × LoopTree),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (addrRangeSweep s.1 s.2.1 s.2.2 (denote (ARVal K) KL tf vs ls)) outD ls.length =
        addrRangeSweepFlat s.1 s.2.1 s.2.2 tf inD inE outD) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD outD inE} (sb : Nat × Nat × LoopBlocks),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (addrRangeSweepB sb.1 sb.2.1 sb.2.2 (denoteB (ARVal K) KL tb vs ls))
          outD ls.length =
        addrRangeSweepBFlat sb.1 sb.2.1 sb.2.2 tb inD inE outD) := by
  refine klSim_mutual ⟨
    fun ⟨curD, next, plan⟩ op k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      simp only [denote]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args ha]
      dsimp only; rw [addrRangeSweepFlat.eq_def, arSweep_let_eq]; dsimp only
      cases hst : ({ code := op.code, args := resolveEnvArgs _ _ op.args } : Op (ARVal K) _).arStep
          curD next with
      | elim res =>
        dsimp only
        exact ih (curD, next, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
          (trieCtxMatch_insertTupEnv hm _) hk
      | emit1 op' wrap =>
        simp only [applyARStep, toTFlat]
        exact congrArg (TFlat.let_ _) (ih (curD, next + _, plan.step1)
          (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk)
      | rangeSubCmp w o x lo width outD' =>
        simp only [applyARStep, toTFlat, idxArgs, op2, Tup.levels, List.length,
          idxArg_imm_eq, idxArg_succ_self, Nat.zero_add, Nat.add_assoc]
        exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
          (ih (curD, next + 1, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
            (trieCtxMatch_insertTupEnv hm (ts := [.bool]) _) hk))
      | addrShl n isSub base inv iv ivD sh _ disp =>
        by_cases hdisp : (disp == 0#n) = true
        · simp only [applyARStep, hdisp, ↓reduceIte, toTFlat, idxArgs, op2, Tup.levels,
            List.length, idxArg_imm_eq, idxArg_succ_self, idxArg_add2_self,
            Nat.zero_add, Nat.add_assoc,
            show (1 : Nat) + 1 = 2 from rfl, show (1 : Nat) + 2 = 3 from rfl]
          exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
            (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
              (ih (curD, next + 1, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
                (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hk))))
        · by_cases hfold : plan.foldDisp = true
          · simp only [applyARStep, hdisp, hfold, Bool.false_eq_true, ↓reduceIte, toTFlat,
              idxArgs, op2, Tup.levels, List.length, idxArg_imm_eq, idxArg_succ_self,
              idxArg_add2_self, Nat.zero_add, Nat.add_assoc,
              show (1 : Nat) + 1 = 2 from rfl, show (1 : Nat) + 2 = 3 from rfl,
              show (1 : Nat) + 3 = 4 from rfl]
            exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
              (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
                (ih (curD, next + 1, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
                  (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hk)))))
          · simp only [applyARStep, hdisp, hfold, Bool.false_eq_true, ↓reduceIte, toTFlat,
              idxArgs, op2, Tup.levels, List.length, idxArg_imm_eq, idxArg_succ_self,
              idxArg_add2_self, Nat.zero_add, Nat.add_assoc,
              show (1 : Nat) + 1 = 2 from rfl, show (1 : Nat) + 3 = 4 from rfl]
            exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
              (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
                (ih (curD, next + 1, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
                  (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hk)))))
      | addrPlain n isSub base inv iv invD ivD disp =>
        by_cases hdisp : (disp == 0#n) = true
        · simp only [applyARStep, hdisp, ↓reduceIte, toTFlat, idxArgs, op2, Tup.levels,
            List.length, idxArg_succ_self, Nat.zero_add, Nat.add_assoc]
          exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
            (ih (curD, next + 1, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
              (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hk))
        · by_cases hfold : plan.foldDisp = true
          · simp only [applyARStep, hdisp, hfold, Bool.false_eq_true, ↓reduceIte, toTFlat,
              idxArgs, op2, Tup.levels, List.length, idxArg_imm_eq, idxArg_succ_self,
              Nat.zero_add, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl]
            exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
              (ih (curD, next + 1, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
                (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hk)))
          · simp only [applyARStep, hdisp, hfold, Bool.false_eq_true, ↓reduceIte, toTFlat,
              idxArgs, op2, Tup.levels, List.length, idxArg_imm_eq, idxArg_succ_self,
              Nat.zero_add, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl]
            exact congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _) (congrArg (TFlat.let_ _)
              (ih (curD, next + 1, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
                (trieCtxMatch_insertTupEnv hm (ts := [.bits n]) _) hk))),
    fun ⟨curD, next, plan⟩ t a k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      simp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hm a ha]
      dsimp only; rw [addrRangeSweepFlat.eq_def, addrRangeSweep.eq_def]; simp only [toTFlat]
      exact congrArg (TFlat.load t _)
        (ih (curD, next + 1, plan.step1) (.cons hΓ) (trieCtxMatch_singleton hm t _) hk),
    fun ⟨curD, next, plan⟩ v a k hΓ _ _ hm hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      simp only [denote]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hm v hv,
        denoteArg_eq_some_resolveEnvArg hΓ hm a ha]
      dsimp only; rw [addrRangeSweepFlat.eq_def, addrRangeSweep.eq_def]; simp only [toTFlat]
      exact congrArg (TFlat.store _ _) (ih (curD, next, plan.step1) hΓ hm hk),
    fun ⟨curD, next, plan⟩ f bs args k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      simp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha]
      dsimp only; rw [addrRangeSweepFlat.eq_def, addrRangeSweep.eq_def]; simp only [toTFlat]
      exact congrArg (TFlat.call f bs _)
        (ih (curD, next + bs.length, plan.step1) (ctxTypes_pushTup_rev _ hΓ)
          (trieCtxMatch_insertTupEnv hm _) hk),
    @fun rs Γ Δ vs ls inD outD inE ⟨curD, next, plan⟩ c t e hΓ _ _ hm hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      simp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hc]
      dsimp only; rw [addrRangeSweepFlat.eq_def, arSweep_jnz_eq]; dsimp only
      cases (resolveEnvArg inD inE c).arOut with
      | imm b => cases b with
        | true => exact iht (curD, next, plan.step2.1) ht
        | false => exact ihe (curD, next, plan.step2.2) he
      | var _ =>
        simp only [toTFlat]
        rw [iht (curD, next, plan.step2.1) ht, ihe (curD, next, plan.step2.2) he],
    fun _ j args hΓ hΔ hll hm hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hj
      simp only [denote]; rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha]
      dsimp only; rw [addrRangeSweepFlat.eq_def, addrRangeSweep.eq_def]
      simp only [toTFlat, hidx],
    fun _ vs' hΓ _ _ hm hwf => by
      simp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf]; rfl,
    fun _ f args hΓ _ _ hm hwf => by
      simp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf]; rfl,
    fun _ _ _ _ _ _ => rfl,
    fun ⟨curD, next, plan⟩ bodies k _ hΔ hll _ hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [addrRangeSweepFlat, denote]
      rw [addrRangeSweep.eq_def]; simp only [toTFlat]
      have hb' := ihB (curD, next, plan.stepGroup.1) (ctxTypes_pushTup_rev _ hΔ) hll.pushTup hb
      have hk' := ihK (curD, next, plan.stepGroup.2) (ctxTypes_pushTup_rev _ hΔ) hll.pushTup hk
      rw [pushTup_length] at hb' hk'
      rw [hb', hk'],
    fun _ _ _ _ _ _ => rfl,
    fun ⟨curD, next, bsPlan⟩ b bs hΓ _ _ hm hwf ihb ihbs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      dsimp only [addrRangeSweepBFlat, denoteB, addrRangeSweepB, toTBlocks]
      let bd := if bsPlan.stepCons.1 then curD + 1 else curD
      exact congr
        (congrArg TBlocks.cons
          (ihb (bd, next + _, bsPlan.stepCons.2.1) (ctxTypes_pushTup_rev _ hΓ)
            (trieCtxMatch_insertTupEnv hm _) hb))
        (ihbs (curD, next, bsPlan.stepCons.2.2) hbs)⟩

public section

theorem addrRangeOptFlatWith_eq (foldDisp : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    addrRangeOptFlatWith foldDisp as tf =
      reifyFunc (Func.addrRangeOptWith foldDisp (denoteFunc (as := as) tf)) := by
  dsimp only [addrRangeOptFlatWith, Func.addrRangeOptWith]
  rw [reifyFunc_denoteFunc_eq tf hwf]
  by_cases hw : (AddrRangeOpt.buildAddrPlan foldDisp as.length tf).2 = true
  · simp only [hw, ↓reduceIte]
    exact (addrRangeSweepFlat_both.1 tf
      (0, as.length, (AddrRangeOpt.buildAddrPlan foldDisp as.length tf).1)
      (CtxTypes.push _ .nil) .nil CtxLevels.nil
      (trieCtxMatch_initEnv (fun x next => ARVal.fresh x next 0) as) hwf).symm
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    exact (reifyFunc_denoteFunc_eq tf hwf).symm

theorem denoteFunc_addrRangeOptFlatWith (foldDisp : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (addrRangeOptFlatWith foldDisp as tf) =
      Func.addrRangeOptWith foldDisp (denoteFunc (as := as) tf) :=
  denoteFunc_of_flat_eq (Func.addrRangeOptWith_wf foldDisp) tf hwf
    (addrRangeOptFlatWith_eq foldDisp tf hwf)

theorem addrRangeOptFlatWith_wfCheck (foldDisp : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (addrRangeOptFlatWith foldDisp as tf).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq (Func.addrRangeOptWith_wf foldDisp) tf hwf
    (addrRangeOptFlatWith_eq foldDisp tf hwf)

theorem addrRangeOptFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    addrRangeOptFlat as tf = reifyFunc (Func.addrRangeOpt (denoteFunc (as := as) tf)) :=
  addrRangeOptFlatWith_eq false tf hwf

flat_pass_corollaries addrRangeOptFlat, Func.addrRangeOpt, Func.addrRangeOpt_wf,
  addrRangeOptFlat_eq, denoteFunc_addrRangeOptFlat, addrRangeOptFlat_wfCheck,
  addrRangeOptFlatFn, addrRangeOptFlatFn_toFn, addrRangeOptFlatFn_wfCheck

end

end OptFlatAddrRange
end LeanQbe.T
