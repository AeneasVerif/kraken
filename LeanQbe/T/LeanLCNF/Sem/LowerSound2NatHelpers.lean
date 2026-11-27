module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound2

/-!
# Tier-H `Nat.*` Lowering Soundness Helpers (`LowerSound2NatHelpers`)

Per-operation `natPrim` simulation lemmas for `pred`, `pow`, `gcd`, `add`, `sub`, `mul`, `div`,
and `mod`, consumed by `LowerSound2a.lean`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

theorem natPrim_pred_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg : LArg} {wa : Word}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natPrim rtArg "pred" [aArg] k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haId : argIdsBelow aArg n) (haW : EvalWordArg ρ aArg wa)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : HNatPrimWp rt "pred" [wa] K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  simp only [HNatPrimWp, natBinSlowInfo?] at hwp
  cases hwa : wa.toBV64? with
  | none => rw [hwa] at hwp; exact False.elim hwp
  | some va =>
    rw [hwa] at hwp
    dsimp only at hwp
    have haEv : LArg.eval ρ i64 aArg = some va := haW.toBV64? hwa
    unfold natPrim at hrun
    refine isScalarObj_wp hrun haEv ?_
    intro sArg ek1 ρ1 hek1 _ hagr1 hsEv
    let Inv : Val i64 → Mem 64 → Prop := fun v m1 =>
      ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m1 ∧ K (Word.i64 v) σ'
    refine withJoin1_wp (Inv := Inv) hek1 (hkMono _) ?_ ?_
    · intro r blk n2 J' hblk hr hJagr v m1 ⟨σ', hinv', hm', hK⟩ hagr rEv
      exact hk r blk _ J' (n + 4) n2 64 v σ' m1 (by omega) hblk hr
        ((hagr.mono (by omega : n ≤ n + 2)).trans hagr1)
        (hJagr.mono (by omega : n ≤ n + 2)) rEv hinv' hm' hK
    · intro j body n2 J' hn2 hbody _ hjok
      rw [lm_bind_run] at hbody
      rcases hbody with ⟨slowE, n3, hslowE, hrest⟩
      have hn23 : n2 ≤ n3 := rtCall1_mono (fun _ => pure_mono _) n2 slowE n3 hslowE
      rw [lm_bind_run] at hrest
      rcases hrest with ⟨fastE, n4, hfastE, hpure⟩
      rw [lm_pure_run] at hpure
      injection hpure with hpr
      have hbod : LExpr.jnz sArg fastE slowE = body := congrArg Prod.fst hpr
      have hn4 : n4 = n' := congrArg Prod.snd hpr
      subst hbod; subst hn4
      refine wp_jnz hsEv ?_ ?_
      · intro htrue
        have hsc : (va &&& 1#64) ≠ 0#64 := of_decide_eq_true htrue
        have hscb : ((va &&& 1#64) != 0#64) = true := bne_iff_ne.mpr hsc
        rw [hscb, ite_eq_left rfl] at hwp
        have ha1 : LArg.eval ρ1 i64 aArg = some va := (hagr1.eval haId).trans haEv
        refine cmpOp_wp hfastE ha1 (LArg.eval_imm_self ρ1 i64 1#64) ?_
        intro zArg ek2 ρ2 hek2 _ hagr2 hzEv
        rw [lm_bind_run] at hek2
        rcases hek2 with ⟨subE, _, hsubE, hp2⟩
        rw [lm_pure_run] at hp2
        injection hp2 with hpr2
        have hbod2 : LExpr.jnz zArg (j (imm64 1)) subE = ek2 := congrArg Prod.fst hpr2
        subst hbod2
        have hzEq : CmpOp.evalBits .eq va 1#64 = decide (va = 1#64) := rfl
        rw [hzEq] at hzEv
        refine wp_jnz hzEv ?_ ?_
        · intro hzT
          have h1 : va = 1#64 := of_decide_eq_true hzT
          rw [ite_eq_left h1] at hwp
          exact hjok J' (imm64 1) ρ2 mem 1#64 (JEnvAgreeBelow.refl _ J')
            (LArg.eval_imm_self ρ2 i64 1#64) ⟨σ, hinv, hm, hwp⟩
        · intro hzF
          have h1 : va ≠ 1#64 := of_decide_eq_false hzF
          rw [ite_eq_right h1] at hwp
          have ha2 : LArg.eval ρ2 i64 aArg = some va :=
            (hagr2.eval (argIdsBelow_mono (by omega) haId)).trans ha1
          refine sub64_wp hsubE ha2 (LArg.eval_imm_self ρ2 i64 2#64) ?_
          intro rArg ek3 ρ3 hek3 _ _ hrEv
          rw [lm_pure_run] at hek3
          injection hek3 with hp3
          have he3 : j rArg = ek3 := congrArg Prod.fst hp3
          subst he3
          exact hjok J' rArg ρ3 mem (va - 2#64) (JEnvAgreeBelow.refl _ J') hrEv
            ⟨σ, hinv, hm, hwp⟩
      · intro hfalse
        have hsc : ¬ ((va &&& 1#64) ≠ 0#64) := of_decide_eq_false hfalse
        have hscb : ((va &&& 1#64) != 0#64) = false := by
          cases h : (va &&& 1#64) != 0#64
          · rfl
          · exact False.elim (hsc (bne_iff_ne.mp h))
        rw [hscb] at hwp
        have hsp := natArithSlow_specR0 (by decide : 17 ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17])
          hinv hm hwp
        have ha1W : EvalRtArg ρ1 aArg va := (haW.agree hagr1 haId).toRtArgBV64 hwa
        refine natSlow_rtCall1_wp hΓ hslowE ((hagr1.eval hnrt).trans hrt)
          (argIdsBelow_mono (by omega) hnrt)
          (by
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro a (rfl | rfl | rfl)
            · exact argIdsBelow_imm _ _ _
            · exact argIdsBelow_mono (by omega) haId
            · exact argIdsBelow_imm _ _ _)
          (evalRtArgs_cons (evalRtArg_imm64 ρ1 17)
            (evalRtArgs_cons ha1W
              (evalRtArgs_cons (evalRtArg_imm64 ρ1 1) (evalRtArgs_nil ρ1))))
          hsp ?_
        intro r2 ekS ρS _ res σ' m' _ hekS _ _ hr2Ev hinv' hm' hK
        rw [lm_pure_run] at hekS
        injection hekS with hps
        have heS : j r2 = ekS := congrArg Prod.fst hps
        subst heS
        exact hjok J' r2 ρS m' res (JEnvAgreeBelow.refl _ J') hr2Ev ⟨σ', hinv', hm', hK⟩

theorem natPrim_pow_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg} {wa wb : Word}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natPrim rtArg "pow" [aArg, bArg] k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haId : argIdsBelow aArg n) (hbId : argIdsBelow bArg n)
    (haW : EvalWordArg ρ aArg wa) (hbW : EvalWordArg ρ bArg wb)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : HNatPrimWp rt "pow" [wa, wb] K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  simp only [HNatPrimWp, natBinSlowInfo?] at hwp
  cases hwa : wa.toBV64? with
  | none => rw [hwa] at hwp; exact False.elim hwp
  | some va =>
    cases hwb : wb.toBV64? with
    | none => rw [hwa, hwb] at hwp; exact False.elim hwp
    | some vb =>
      rw [hwa, hwb] at hwp
      rcases hwp with ⟨aVal, bVal, haRep, hbRep, hok, hkPow⟩
      have hm' : (bigNumRtInv rt σ.st σ.scr σ.scrLimbs ⋆ lcnfHeap σ.objs ⋆ R) mem := by
        rw [hstate_mem_unfold] at hm; exact hm
      let P : Post [i64] := fun (res, ()) m' =>
        ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 res) σ'
      have hsp : lcnfNatSlowSpec (rt, BitVec.ofNat 64 16, va, vb, ()) mem P
          (fun _ _ _ _ => False) := by
        refine ⟨σ.st, σ.scr, σ.scrLimbs, σ.objs, R, hinv, hm', ?_⟩
        have htoNat : (BitVec.ofNat 64 16).toNat = 16 := by decide
        rw [htoNat]
        simp only [List.mem_cons, List.not_mem_nil, or_false,
          show ¬(16 = 1 ∨ 16 = 2 ∨ 16 = 3 ∨ 16 = 4 ∨ 16 = 5 ∨ 16 = 6 ∨ 16 = 7 ∨
            16 = 8 ∨ 16 = 17) by decide,
          show ¬(16 = 9 ∨ 16 = 10 ∨ 16 = 11 ∨ 16 = 12 ∨ 16 = 13 ∨ 16 = 14 ∨
            16 = 15 ∨ 16 = 19) by decide, ↓reduceIte]
        refine ⟨aVal, bVal, haRep, hbRep, hok, fun res st' scr' objs' m' hpm hrem hwf'
            hres hkeep hmPost => ?_⟩
        let σ' : HState := { st := st', objs := objs', scr := σ.scr, scrLimbs := scr' }
        have hmOut : (σ'.mem rt ⋆ R) m' := by rw [hstate_mem_unfold]; exact hmPost
        exact ⟨σ', hwf', hmOut, hkPow res st' scr' objs' hpm hrem hwf' hres hkeep⟩
      unfold natPrim at hrun
      refine natSlow_rtCall1_wp hΓ hrun hrt hnrt
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro a (rfl | rfl | rfl)
          · exact argIdsBelow_imm _ _ _
          · exact haId
          · exact hbId)
        (evalRtArgs_cons (evalRtArg_imm64 ρ 16)
          (evalRtArgs_cons (haW.toRtArgBV64 hwa)
            (evalRtArgs_cons (hbW.toRtArgBV64 hwb) (evalRtArgs_nil ρ))))
        hsp ?_
      intro r ek ρ' nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK
      exact hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J)
        hrEv hinv' hm' hK

theorem natPrim_gcd_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg} {wa wb : Word}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natPrim rtArg "gcd" [aArg, bArg] k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haId : argIdsBelow aArg n) (hbId : argIdsBelow bArg n)
    (haW : EvalWordArg ρ aArg wa) (hbW : EvalWordArg ρ bArg wb)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : HNatPrimWp rt "gcd" [wa, wb] K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  simp only [HNatPrimWp, natBinSlowInfo?] at hwp
  cases hwa : wa.toBV64? with
  | none => rw [hwa] at hwp; exact False.elim hwp
  | some va =>
    cases hwb : wb.toBV64? with
    | none => rw [hwa, hwb] at hwp; exact False.elim hwp
    | some vb =>
      rw [hwa, hwb] at hwp
      rcases hwp with ⟨aVal, bVal, haRep, hbRep, hok, hkGcd⟩
      have hm' : (bigNumRtInv rt σ.st σ.scr σ.scrLimbs ⋆ lcnfHeap σ.objs ⋆ R) mem := by
        rw [hstate_mem_unfold] at hm; exact hm
      let P : Post [i64] := fun (res, ()) m' =>
        ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 res) σ'
      have hsp : lcnfNatSlowSpec (rt, BitVec.ofNat 64 18, va, vb, ()) mem P
          (fun _ _ _ _ => False) := by
        refine ⟨σ.st, σ.scr, σ.scrLimbs, σ.objs, R, hinv, hm', ?_⟩
        have htoNat : (BitVec.ofNat 64 18).toNat = 18 := by decide
        rw [htoNat]
        simp only [List.mem_cons, List.not_mem_nil, or_false, ↓reduceIte,
          show ¬(18 = 1 ∨ 18 = 2 ∨ 18 = 3 ∨ 18 = 4 ∨ 18 = 5 ∨ 18 = 6 ∨ 18 = 7 ∨
            18 = 8 ∨ 18 = 17) by decide,
          show ¬(18 = 9 ∨ 18 = 10 ∨ 18 = 11 ∨ 18 = 12 ∨ 18 = 13 ∨ 18 = 14 ∨
            18 = 15 ∨ 18 = 19) by decide,
          show (18 = 16) = False by decide]
        refine ⟨aVal, bVal, haRep, hbRep, hok, fun res st' scr' objs' m' hpm hrem hwf'
            hres hkeep hmPost => ?_⟩
        let σ' : HState := { st := st', objs := objs', scr := σ.scr, scrLimbs := scr' }
        have hmOut : (σ'.mem rt ⋆ R) m' := by rw [hstate_mem_unfold]; exact hmPost
        exact ⟨σ', hwf', hmOut, hkGcd res st' scr' objs' hpm hrem hwf' hres hkeep⟩
      unfold natPrim at hrun
      refine natSlow_rtCall1_wp hΓ hrun hrt hnrt
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro a (rfl | rfl | rfl)
          · exact argIdsBelow_imm _ _ _
          · exact haId
          · exact hbId)
        (evalRtArgs_cons (evalRtArg_imm64 ρ 18)
          (evalRtArgs_cons (haW.toRtArgBV64 hwa)
            (evalRtArgs_cons (hbW.toRtArgBV64 hwb) (evalRtArgs_nil ρ))))
        hsp ?_
      intro r ek ρ' nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK
      exact hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J)
        hrEv hinv' hm' hK

theorem natPrim_add_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natBin rtArg "add" 64 aArg bArg (fun slow j =>
      sub64 aArg (imm64 1) fun s => add64 s bArg fun r =>
      cmpOp .ult 64 r bArg fun ovf => do let sE ← slow; pure (.jnz ovf sE (j r))) k).run n =
      .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haEv : LArg.eval ρ i64 aArg = some va) (haId : argIdsBelow aArg n)
    (hbEv : LArg.eval ρ i64 bArg = some vb) (hbId : argIdsBelow bArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match natBinFast? "add" va vb with
      | some w => K w σ
      | none => HNatArithSlowWp rt 1 va vb 64 K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  dsimp only [natBin, natOpCode] at hrun
  refine tagBin_wp (R := R) (K := K) hΓ hrun
    (fun _ _ hslow => sub64_mono fun _ => add64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono hslow fun _ => pure_mono _)
    hkMono hrt hnrt haEv haId hbEv hbId ?_ ?_ ?_
  · intro hsc0
    have hnone : natBinFast? "add" va vb = none := by simp [natBinFast?, hsc0]
    rw [hnone] at hwp
    exact natArithSlow_specR0 (by decide) hinv hm hwp
  · intro hsc j body n2 _ J' ρ2 slow _ _ hbody hagr20 ha2 hb2 _ hnb2 hslowR hj
    refine sub64_wp hbody ha2 (LArg.eval_imm_self ρ2 i64 1#64) ?_
    intro sArg ek1 ρ1 hek1 _ hagr1 hsEv
    have hb1 : LArg.eval ρ1 i64 bArg = some vb := (hagr1.eval hnb2).trans hb2
    refine add64_wp hek1 hsEv hb1 ?_
    intro rArg ek2 ρ3 hek2 hrId hagr3 hrEv
    have hb3 : LArg.eval ρ3 i64 bArg = some vb :=
      (hagr3.eval (argIdsBelow_mono (by omega) hnb2)).trans hb1
    refine cmpOp_wp hek2 hrEv hb3 ?_
    intro ovfArg ek3 ρ4 hek3 _ hagr4 hovfEv
    rw [lm_bind_run] at hek3
    rcases hek3 with ⟨sE, nS, hsE, hp⟩
    rw [lm_pure_run] at hp
    injection hp with hpr
    have hbod : LExpr.jnz ovfArg sE (j rArg) = ek3 := congrArg Prod.fst hpr
    subst hbod
    have hovfEq : CmpOp.evalBits .ult ((va - 1#64) + vb) vb =
        decide (((va - 1#64) + vb) < vb) := rfl
    rw [hovfEq] at hovfEv
    refine wp_jnz hovfEv ?_ ?_
    · intro hovfT
      have hlt : ((va - 1#64) + vb) < vb := of_decide_eq_true hovfT
      have hnone : natBinFast? "add" va vb = none := by simp [natBinFast?, hsc, hlt]
      rw [hnone] at hwp
      have hagr40 : VEnvAgreeBelow n ρ4 ρ :=
        ((hagr4.mono (by omega : n ≤ n2 + 2)).trans
          ((hagr3.mono (by omega : n ≤ n2 + 1)).trans
            (hagr1.mono (by omega : n ≤ n2)))).trans hagr20
      exact hslowR (n2 + 3) nS sE ρ4 J' (by omega) hsE hagr40
        (JEnvAgreeBelow.refl _ J') (natArithSlow_specR0 (by decide) hinv hm hwp)
    · intro hovfF
      have hnlt : ¬ (((va - 1#64) + vb) < vb) := of_decide_eq_false hovfF
      have hsome : natBinFast? "add" va vb = some (Word.i64 ((va - 1#64) + vb)) := by
        simp [natBinFast?, hsc, hnlt]
      rw [hsome] at hwp
      have hr4 : LArg.eval ρ4 i64 rArg = some ((va - 1#64) + vb) :=
        (hagr4.eval hrId).trans hrEv
      exact hj J' rArg ρ4 mem _ σ (JEnvAgreeBelow.refl _ J') hr4 hinv hm hwp
  · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv hinv' hm' hK

theorem natPrim_sub_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natBin rtArg "sub" 64 aArg bArg (fun _ j =>
      cmpOp .ult 64 aArg bArg fun lt => do
        let e ← sub64 aArg bArg fun d => add64 d (imm64 1) fun r => pure (j r)
        pure (.jnz lt (j (imm64 1)) e)) k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haEv : LArg.eval ρ i64 aArg = some va) (haId : argIdsBelow aArg n)
    (hbEv : LArg.eval ρ i64 bArg = some vb) (hbId : argIdsBelow bArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match natBinFast? "sub" va vb with
      | some w => K w σ
      | none => HNatArithSlowWp rt 2 va vb 64 K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  dsimp only [natBin, natOpCode] at hrun
  refine tagBin_wp (R := R) (K := K) hΓ hrun
    (fun _ _ _ => cmpOp_mono fun _ =>
      bind_mono (sub64_mono fun _ => add64_mono fun _ => pure_mono _) fun _ => pure_mono _)
    hkMono hrt hnrt haEv haId hbEv hbId ?_ ?_ ?_
  · intro hsc0
    have hnone : natBinFast? "sub" va vb = none := by simp [natBinFast?, hsc0]
    rw [hnone] at hwp
    exact natArithSlow_specR0 (by decide) hinv hm hwp
  · intro hsc j body _ _ J' ρ2 _ _ _ hbody _ ha2 hb2 hna2 hnb2 _ hj
    refine cmpOp_wp hbody ha2 hb2 ?_
    intro ltArg ek1 ρ1 hek1 _ hagr1 hltEv
    rw [lm_bind_run] at hek1
    rcases hek1 with ⟨subE, _, hsubE, hp⟩
    rw [lm_pure_run] at hp
    injection hp with hpr
    have hbod : LExpr.jnz ltArg (j (imm64 1)) subE = ek1 := congrArg Prod.fst hpr
    subst hbod
    have hltEq : CmpOp.evalBits .ult va vb = decide (va < vb) := rfl
    rw [hltEq] at hltEv
    have hsome : natBinFast? "sub" va vb =
        some (Word.i64 (if va < vb then 1#64 else (va - vb) + 1#64)) := by
      simp [natBinFast?, hsc]
    rw [hsome] at hwp
    refine wp_jnz hltEv ?_ ?_
    · intro hltT
      have hlt : va < vb := of_decide_eq_true hltT
      rw [ite_eq_left hlt] at hwp
      exact hj J' (imm64 1) ρ1 mem 1#64 σ
        (JEnvAgreeBelow.refl _ J') (LArg.eval_imm_self ρ1 i64 1#64) hinv hm hwp
    · intro hltF
      have hnlt : ¬ (va < vb) := of_decide_eq_false hltF
      rw [ite_eq_right hnlt] at hwp
      have ha1 : LArg.eval ρ1 i64 aArg = some va := (hagr1.eval hna2).trans ha2
      have hb1 : LArg.eval ρ1 i64 bArg = some vb := (hagr1.eval hnb2).trans hb2
      refine sub64_wp hsubE ha1 hb1 ?_
      intro dArg ek2 ρ3 hek2 _ _ hdEv
      refine add64_wp hek2 hdEv (LArg.eval_imm_self ρ3 i64 1#64) ?_
      intro rArg ek3 ρ4 hek3 _ _ hrEv
      rw [lm_pure_run] at hek3
      injection hek3 with hp3
      have he3 : j rArg = ek3 := congrArg Prod.fst hp3
      subst he3
      exact hj J' rArg ρ4 mem ((va - vb) + 1#64) σ
        (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
  · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv hinv' hm' hK

theorem natPrim_mul_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natBin rtArg "mul" 64 aArg bArg (fun slow j =>
      lshr64 aArg (imm64 1) fun x => lshr64 bArg (imm64 1) fun y =>
      op2 i64 i64 (.umulw 64) [x, y] fun lo hi =>
      lshr64 lo (imm64 63) fun top => or64 hi top fun bad =>
      cmpOp .ne 64 bad (imm64 0) fun ovf => do
        let e ← boxSmall lo fun r => pure (j r)
        let sE ← slow
        pure (.jnz ovf sE e)) k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haEv : LArg.eval ρ i64 aArg = some va) (haId : argIdsBelow aArg n)
    (hbEv : LArg.eval ρ i64 bArg = some vb) (hbId : argIdsBelow bArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match natBinFast? "mul" va vb with
      | some w => K w σ
      | none => HNatArithSlowWp rt 3 va vb 64 K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  dsimp only [natBin, natOpCode] at hrun
  refine tagBin_wp (R := R) (K := K) hΓ hrun
    (fun _ _ hslow => lshr64_mono fun _ => lshr64_mono fun _ => op2_mono fun _ _ =>
      lshr64_mono fun _ => or64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono (boxSmall_mono fun _ => pure_mono _) fun _ =>
      bind_mono hslow fun _ => pure_mono _)
    hkMono hrt hnrt haEv haId hbEv hbId ?_ ?_ ?_
  · intro hsc0
    have hnone : natBinFast? "mul" va vb = none := by simp [natBinFast?, hsc0]
    rw [hnone] at hwp
    exact natArithSlow_specR0 (by decide) hinv hm hwp
  · intro hsc j body n2 _ J' ρ2 _ _ _ hbody hagr20 ha2 hb2 _ hnb2 hslowR hj
    refine lshr64_wp hbody ha2 (LArg.eval_imm_self ρ2 i64 1#64) ?_
    intro xArg ek1 ρ1 hek1 hxId hagr1 hxEv
    have hb1 : LArg.eval ρ1 i64 bArg = some vb := (hagr1.eval hnb2).trans hb2
    refine lshr64_wp hek1 hb1 (LArg.eval_imm_self ρ1 i64 1#64) ?_
    intro yArg ek2 ρ3 hek2 _ hagr3 hyEv
    have hx3 : LArg.eval ρ3 i64 xArg = some (va >>> 1) := by
      simpa using (hagr3.eval hxId).trans hxEv
    have hy3 : LArg.eval ρ3 i64 yArg = some (vb >>> 1) := by simpa using hyEv
    refine op2_wp hek2 (evalArgs_cons hx3 (evalArgs_cons hy3 (evalArgs_nil ρ3))) ?_
    intro ek3 hek3 hloId hhiId
    rw [OpCode.wp_umulw]
    let loV : Frontend.C0.LVar := { id := n2 + 1 + 1, name := "", ty := i64 }
    let hiV : Frontend.C0.LVar := { id := n2 + 1 + 1 + 1, name := "", ty := i64 }
    let loArg := vArg loV
    let hiArg := vArg hiV
    let loVal := (va >>> 1) * (vb >>> 1)
    let hiVal := BitVec.ofNat 64 ((va >>> 1).toNat * (vb >>> 1).toNat / 2 ^ 64)
    let ρ4 := (ρ3.set loV.id i64 loVal).set hiV.id i64 hiVal
    have hloEq : LArg.eval ρ4 i64 loArg = some loVal := by
      have hlo3 : argIdsBelow loArg (n2 + 3) := by show n2 + 2 < n2 + 3; omega
      exact (VEnvAgreeBelow.set (by dsimp only [hiV]; omega : n2 + 3 ≤ hiV.id) i64 hiVal
        |>.eval hlo3).trans (LArg.eval_vArg_set_self ρ3 loV loVal)
    have hhiEq : LArg.eval ρ4 i64 hiArg = some hiVal :=
      LArg.eval_vArg_set_self (ρ3.set loV.id i64 loVal) hiV hiVal
    have hagr4 : VEnvAgreeBelow (n2 + 2) ρ4 ρ3 :=
      (VEnvAgreeBelow.set (by dsimp only [hiV]; omega : n2 + 2 ≤ hiV.id) i64 hiVal).trans
        (VEnvAgreeBelow.set (Nat.le_refl (n2 + 2)) i64 loVal)
    refine lshr64_wp hek3 hloEq (LArg.eval_imm_self ρ4 i64 63#64) ?_
    intro topArg ek4 ρ5 hek4 _ hagr5 htopEv
    have hhi5 : LArg.eval ρ5 i64 hiArg = some hiVal :=
      (hagr5.eval hhiId).trans hhiEq
    have htop5 : LArg.eval ρ5 i64 topArg = some (((va >>> 1) * (vb >>> 1)) >>> 63) := by
      simpa using htopEv
    refine or64_wp hek4 hhi5 htop5 ?_
    intro badArg ek5 ρ6 hek5 _ hagr6 hbadEv
    refine cmpOp_wp hek5 hbadEv (LArg.eval_imm_self ρ6 i64 0#64) ?_
    intro ovfArg ek6 ρ7 hek6 _ hagr7 hovfEv
    rw [lm_bind_run] at hek6
    rcases hek6 with ⟨fastE, _, hfastE, hrest6⟩
    rw [lm_bind_run] at hrest6
    rcases hrest6 with ⟨sE, nS, hsE, hp⟩
    rw [lm_pure_run] at hp
    injection hp with hpr
    have hbod : LExpr.jnz ovfArg sE fastE = ek6 := congrArg Prod.fst hpr
    subst hbod
    have hiff := bv64_mul_fast_iff (va >>> 1) (vb >>> 1) (bv64_shr1_lt va) (bv64_shr1_lt vb)
    have hovfEq : CmpOp.evalBits .ne
        (BitVec.ofNat 64 ((va >>> 1).toNat * (vb >>> 1).toNat / 2 ^ 64) |||
          (((va >>> 1) * (vb >>> 1)) >>> 63)) 0#64 =
        decide (BitVec.ofNat 64 ((va >>> 1).toNat * (vb >>> 1).toNat / 2 ^ 64) |||
          (((va >>> 1) * (vb >>> 1)) >>> 63) ≠ 0#64) := rfl
    rw [hovfEq] at hovfEv
    have hagr70 : VEnvAgreeBelow n ρ7 ρ :=
      ((hagr7.mono (by omega : n ≤ n2 + 6)).trans
        ((hagr6.mono (by omega : n ≤ n2 + 5)).trans
          ((hagr5.mono (by omega : n ≤ n2 + 4)).trans
            ((hagr4.mono (by omega : n ≤ n2 + 2)).trans
              ((hagr3.mono (by omega : n ≤ n2 + 1)).trans
                (hagr1.mono (by omega : n ≤ n2))))))).trans hagr20
    refine wp_jnz hovfEv ?_ ?_
    · intro hovfT
      have hnotLt : ¬ ((va >>> 1).toNat * (vb >>> 1).toNat < 2 ^ 63) :=
        hiff.mp (of_decide_eq_true hovfT)
      have hnotLt' : ¬ ((va.toNat >>> 1) * (vb.toNat >>> 1) < 2 ^ 63) := by
        simpa [BitVec.toNat_ushiftRight] using hnotLt
      have hnone : natBinFast? "mul" va vb = none := by simp [natBinFast?, hsc, hnotLt']
      rw [hnone] at hwp
      have hnFast := boxSmall_mono (fun _ => pure_mono _) _ _ _ hfastE
      exact hslowR _ nS sE ρ7 J' (by omega) hsE hagr70
        (JEnvAgreeBelow.refl _ J') (natArithSlow_specR0 (by decide) hinv hm hwp)
    · intro hovfF
      have hneF := of_decide_eq_false hovfF
      have hmulLt : (va >>> 1).toNat * (vb >>> 1).toNat < 2 ^ 63 := by
        by_cases hmLt : (va >>> 1).toNat * (vb >>> 1).toNat < 2 ^ 63
        · exact hmLt
        · exact False.elim (hneF (hiff.mpr hmLt))
      have hmulLt' : (va.toNat >>> 1) * (vb.toNat >>> 1) < 2 ^ 63 := by
        simpa [BitVec.toNat_ushiftRight] using hmulLt
      have hsome : natBinFast? "mul" va vb =
          some (Word.i64 (BitVec.ofNat 64
            (2 * ((va >>> 1).toNat * (vb >>> 1).toNat) + 1))) := by
        simp [natBinFast?, hsc, hmulLt', BitVec.toNat_ushiftRight]
      rw [hsome] at hwp
      have hlo7 : LArg.eval ρ7 i64 loArg = some ((va >>> 1) * (vb >>> 1)) := by
        have h5 := (hagr5.eval hloId).trans hloEq
        have h6 := (hagr6.eval (argIdsBelow_mono (by omega) hloId)).trans h5
        exact (hagr7.eval (argIdsBelow_mono (by omega) hloId)).trans h6
      refine boxSmall_wp hfastE hlo7 ?_
      intro rArg ek7 ρ8 hek7 _ _ hrEv
      rw [lm_pure_run] at hek7
      injection hek7 with hp7
      have he7 : j rArg = ek7 := congrArg Prod.fst hp7
      subst he7
      have hprodEq : (((va >>> 1) * (vb >>> 1)) <<< 1) ||| 1#64 =
          BitVec.ofNat 64 (2 * ((va >>> 1).toNat * (vb >>> 1).toNat) + 1) := by
        have hlolt : ((va >>> 1) * (vb >>> 1)).toNat < 2 ^ 63 := by
          rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
          exact hmulLt
        have hbx := bv64_box_self_eq ((va >>> 1) * (vb >>> 1)) hlolt
        rwa [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)] at hbx
      rw [hprodEq] at hrEv
      exact hj J' rArg ρ8 mem _ σ (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
  · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv hinv' hm' hK

theorem natPrim_div_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natBin rtArg "div" 64 aArg bArg (fun _ j =>
      lshr64 bArg (imm64 1) fun y => cmpOp .eq 64 y (imm64 0) fun z => do
        let e ← lshr64 aArg (imm64 1) fun x =>
          op1 i64 (.udiv 64) [x, y] fun q => boxSmall q fun r => pure (j r)
        pure (.jnz z (j (imm64 1)) e)) k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haEv : LArg.eval ρ i64 aArg = some va) (haId : argIdsBelow aArg n)
    (hbEv : LArg.eval ρ i64 bArg = some vb) (hbId : argIdsBelow bArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match natBinFast? "div" va vb with
      | some w => K w σ
      | none => HNatArithSlowWp rt 4 va vb 64 K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  dsimp only [natBin, natOpCode] at hrun
  refine tagBin_wp (R := R) (K := K) hΓ hrun
    (fun _ _ _ => lshr64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono (lshr64_mono fun _ => op1_mono fun _ => boxSmall_mono fun _ => pure_mono _)
        fun _ => pure_mono _)
    hkMono hrt hnrt haEv haId hbEv hbId ?_ ?_ ?_
  · intro hsc0
    have hnone : natBinFast? "div" va vb = none := by simp [natBinFast?, hsc0]
    rw [hnone] at hwp
    exact natArithSlow_specR0 (by decide) hinv hm hwp
  · intro hsc j body n2 _ J' ρ2 _ _ _ hbody _ ha2 hb2 hna2 _ _ hj
    refine lshr64_wp hbody hb2 (LArg.eval_imm_self ρ2 i64 1#64) ?_
    intro yArg ek1 ρ1 hek1 hyId hagr1 hyEv
    have hyEq : LArg.eval ρ1 i64 yArg = some (vb >>> 1) := by simpa using hyEv
    refine cmpOp_wp hek1 hyEq (LArg.eval_imm_self ρ1 i64 0#64) ?_
    intro zArg ek2 ρ3 hek2 _ hagr3 hzEv
    rw [lm_bind_run] at hek2
    rcases hek2 with ⟨eDiv, _, heDiv, hp⟩
    rw [lm_pure_run] at hp
    injection hp with hpr
    have hbod : LExpr.jnz zArg (j (imm64 1)) eDiv = ek2 := congrArg Prod.fst hpr
    subst hbod
    have hzEq : CmpOp.evalBits .eq (vb >>> 1) 0#64 = decide (vb >>> 1 = 0#64) := rfl
    rw [hzEq] at hzEv
    have hsome : natBinFast? "div" va vb =
        some (Word.i64 (if (vb >>> 1).toNat = 0 then 1#64
          else BitVec.ofNat 64 (2 * ((va >>> 1).toNat / (vb >>> 1).toNat) + 1))) := by
      simp [natBinFast?, hsc]
    rw [hsome] at hwp
    refine wp_jnz hzEv ?_ ?_
    · intro hzT
      have hy0 : (vb >>> 1).toNat = 0 := by rw [of_decide_eq_true hzT]; decide
      rw [ite_eq_left hy0] at hwp
      exact hj J' (imm64 1) ρ3 mem 1#64 σ
        (JEnvAgreeBelow.refl _ J') (LArg.eval_imm_self ρ3 i64 1#64) hinv hm hwp
    · intro hzF
      have hyNe : vb >>> 1 ≠ 0#64 := of_decide_eq_false hzF
      have hyNatNe : (vb >>> 1).toNat ≠ 0 := fun h =>
        hyNe (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [ite_eq_right hyNatNe] at hwp
      have ha3 : LArg.eval ρ3 i64 aArg = some va :=
        (hagr3.eval (argIdsBelow_mono (by omega) hna2)).trans ((hagr1.eval hna2).trans ha2)
      refine lshr64_wp heDiv ha3 (LArg.eval_imm_self ρ3 i64 1#64) ?_
      intro xArg ek3 ρ4 hek3 _ hagr4 hxEv
      have hx4 : LArg.eval ρ4 i64 xArg = some (va >>> 1) := by simpa using hxEv
      have hy4 : LArg.eval ρ4 i64 yArg = some (vb >>> 1) :=
        (hagr4.eval (argIdsBelow_mono (by omega) hyId)).trans ((hagr3.eval hyId).trans hyEq)
      refine op1_wp hek3 (evalArgs_cons hx4 (evalArgs_cons hy4 (evalArgs_nil ρ4))) ?_
      intro ek4 hek4 _
      rw [OpCode.wp_udiv]
      refine ⟨hyNe, ?_⟩
      let q := (va >>> 1) / (vb >>> 1)
      let ρ5 := ρ4.set (n2 + 3) i64 q
      have hqEv : LArg.eval ρ5 i64 (vArg { id := n2 + 3, name := "", ty := i64 }) = some q :=
        LArg.eval_vArg_set_self ρ4 { id := n2 + 3, name := "", ty := i64 } q
      refine boxSmall_wp hek4 hqEv ?_
      intro rArg ek5 ρ6 hek5 _ _ hrEv
      rw [lm_pure_run] at hek5
      injection hek5 with hp5
      have he5 : j rArg = ek5 := congrArg Prod.fst hp5
      subst he5
      have hqlt : q.toNat < 2 ^ 63 := by
        have hxlt := bv64_shr1_lt va
        change ((va >>> 1).toNat / (vb >>> 1).toNat) < 2 ^ 63
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxlt
      have hbx := bv64_box_self_eq q hqlt
      change ((q <<< 1) ||| 1#64) =
          BitVec.ofNat 64 (2 * ((va >>> 1).toNat / (vb >>> 1).toNat) + 1) at hbx
      rw [hbx] at hrEv
      exact hj J' rArg ρ6 mem _ σ (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
  · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv hinv' hm' hK

theorem natPrim_mod_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natBin rtArg "mod" 64 aArg bArg (fun _ j =>
      lshr64 bArg (imm64 1) fun y => cmpOp .eq 64 y (imm64 0) fun z => do
        let e ← lshr64 aArg (imm64 1) fun x =>
          op1 i64 (.urem 64) [x, y] fun q => boxSmall q fun r => pure (j r)
        pure (.jnz z (j aArg) e)) k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haEv : LArg.eval ρ i64 aArg = some va) (haId : argIdsBelow aArg n)
    (hbEv : LArg.eval ρ i64 bArg = some vb) (hbId : argIdsBelow bArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match natBinFast? "mod" va vb with
      | some w => K w σ
      | none => HNatArithSlowWp rt 5 va vb 64 K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  dsimp only [natBin, natOpCode] at hrun
  refine tagBin_wp (R := R) (K := K) hΓ hrun
    (fun _ _ _ => lshr64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono (lshr64_mono fun _ => op1_mono fun _ => boxSmall_mono fun _ => pure_mono _)
        fun _ => pure_mono _)
    hkMono hrt hnrt haEv haId hbEv hbId ?_ ?_ ?_
  · intro hsc0
    have hnone : natBinFast? "mod" va vb = none := by simp [natBinFast?, hsc0]
    rw [hnone] at hwp
    exact natArithSlow_specR0 (by decide) hinv hm hwp
  · intro hsc j body n2 _ J' ρ2 _ _ _ hbody _ ha2 hb2 hna2 _ _ hj
    refine lshr64_wp hbody hb2 (LArg.eval_imm_self ρ2 i64 1#64) ?_
    intro yArg ek1 ρ1 hek1 hyId hagr1 hyEv
    have hyEq : LArg.eval ρ1 i64 yArg = some (vb >>> 1) := by simpa using hyEv
    refine cmpOp_wp hek1 hyEq (LArg.eval_imm_self ρ1 i64 0#64) ?_
    intro zArg ek2 ρ3 hek2 _ hagr3 hzEv
    rw [lm_bind_run] at hek2
    rcases hek2 with ⟨eMod, _, heMod, hp⟩
    rw [lm_pure_run] at hp
    injection hp with hpr
    have hbod : LExpr.jnz zArg (j aArg) eMod = ek2 := congrArg Prod.fst hpr
    subst hbod
    have hzEq : CmpOp.evalBits .eq (vb >>> 1) 0#64 = decide (vb >>> 1 = 0#64) := rfl
    rw [hzEq] at hzEv
    have hsome : natBinFast? "mod" va vb =
        some (Word.i64 (if (vb >>> 1).toNat = 0 then va
          else BitVec.ofNat 64 (2 * ((va >>> 1).toNat % (vb >>> 1).toNat) + 1))) := by
      simp [natBinFast?, hsc]
    rw [hsome] at hwp
    have ha3 : LArg.eval ρ3 i64 aArg = some va :=
      (hagr3.eval (argIdsBelow_mono (by omega) hna2)).trans ((hagr1.eval hna2).trans ha2)
    refine wp_jnz hzEv ?_ ?_
    · intro hzT
      have hy0 : (vb >>> 1).toNat = 0 := by rw [of_decide_eq_true hzT]; decide
      rw [ite_eq_left hy0] at hwp
      exact hj J' aArg ρ3 mem va σ (JEnvAgreeBelow.refl _ J') ha3 hinv hm hwp
    · intro hzF
      have hyNe : vb >>> 1 ≠ 0#64 := of_decide_eq_false hzF
      have hyNatNe : (vb >>> 1).toNat ≠ 0 := fun h =>
        hyNe (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [ite_eq_right hyNatNe] at hwp
      refine lshr64_wp heMod ha3 (LArg.eval_imm_self ρ3 i64 1#64) ?_
      intro xArg ek3 ρ4 hek3 _ hagr4 hxEv
      have hx4 : LArg.eval ρ4 i64 xArg = some (va >>> 1) := by simpa using hxEv
      have hy4 : LArg.eval ρ4 i64 yArg = some (vb >>> 1) :=
        (hagr4.eval (argIdsBelow_mono (by omega) hyId)).trans ((hagr3.eval hyId).trans hyEq)
      refine op1_wp hek3 (evalArgs_cons hx4 (evalArgs_cons hy4 (evalArgs_nil ρ4))) ?_
      intro ek4 hek4 _
      rw [OpCode.wp_urem]
      refine ⟨hyNe, ?_⟩
      let q := (va >>> 1) % (vb >>> 1)
      let ρ5 := ρ4.set (n2 + 3) i64 q
      have hqEv : LArg.eval ρ5 i64 (vArg { id := n2 + 3, name := "", ty := i64 }) = some q :=
        LArg.eval_vArg_set_self ρ4 { id := n2 + 3, name := "", ty := i64 } q
      refine boxSmall_wp hek4 hqEv ?_
      intro rArg ek5 ρ6 hek5 _ _ hrEv
      rw [lm_pure_run] at hek5
      injection hek5 with hp5
      have he5 : j rArg = ek5 := congrArg Prod.fst hp5
      subst he5
      have hqlt : q.toNat < 2 ^ 63 := by
        change ((va >>> 1).toNat % (vb >>> 1).toNat) < 2 ^ 63
        have hpos : 0 < (vb >>> 1).toNat := Nat.pos_of_ne_zero hyNatNe
        exact Nat.lt_trans (Nat.mod_lt _ hpos) (bv64_shr1_lt vb)
      have hbx := bv64_box_self_eq q hqlt
      change ((q <<< 1) ||| 1#64) =
          BitVec.ofNat 64 (2 * ((va >>> 1).toNat % (vb >>> 1).toNat) + 1) at hbx
      rw [hbx] at hrEv
      exact hj J' rArg ρ6 mem _ σ (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
  · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv hinv' hm' hK

end LeanQbe.T.LeanLCNF.Sem
