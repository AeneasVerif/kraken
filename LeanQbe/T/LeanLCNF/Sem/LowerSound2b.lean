module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound2

/-!
# Tier-H `UIntN.*` / `USize.*` Primitive Lowering Soundness (`LowerSound2b`)

Proves `LMMono` monotonicity and `LExpr.wp` simulation lemmas for `Lower.uintOfNat`,
`Lower.uintToNat`, and `Lower.uintPrim` across all `isPhase1UintPrim` operations (wrapping
arithmetic, bit shifts, bitwise ops, division & remainder, comparisons, casts, `ofNat`/`ofNatLT`,
`ofBitVec` with `emitDec1`, and `toNat`/`toBitVec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. `LMMono` Lemmas for `uintOfNat`, `uintToNat`, and `uintPrim` -/

theorem uintOfNat_mono {rtArg : LArg} {w : Nat} {aArg : LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (uintOfNat rtArg w aArg k) := by
  unfold uintOfNat
  refine isScalarObj_mono fun _ => withJoin1_mono hk fun _ => ?_
  refine bind_mono (call1_mono fun _ => convW_mono fun _ => pure_mono _) fun _ => ?_
  exact bind_mono (lshr64_mono fun _ => convW_mono fun _ => pure_mono _) fun _ => pure_mono _

theorem uintToNat_mono {rtArg : LArg} {w : Nat} {aArg : LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (uintToNat rtArg w aArg k) := by
  unfold uintToNat
  refine convW_mono fun _ => ?_
  split
  · exact boxSmall_mono hk
  · refine withJoin1_mono hk fun _ => ?_
    refine bind_mono (call1_mono fun _ => pure_mono _) fun _ => ?_
    refine bind_mono (boxSmall_mono fun _ => pure_mono _) fun _ => ?_
    exact lshr64_mono fun _ => cmpOp_mono fun _ => pure_mono _

theorem uintPrim_mono {rtArg : LArg} {w : Nat} {op : String} {args : List LArg}
    {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (uintPrim rtArg w op args k) := by
  unfold uintPrim
  dsimp only
  split
  all_goals first
    | exact lfail_mono
    | exact convW_mono fun _ => rtCall1_mono hk
    | exact convW_mono hk
    | exact uintToNat_mono fun _ => rtCall1_mono hk
    | exact uintToNat_mono hk
    | exact uintOfNat_mono fun _ => emitDec1_mono (hk _)
    | exact uintOfNat_mono hk
    | exact withJoin1_mono hk fun _ =>
        bind_mono (op1_mono fun _ => pure_mono _) fun _ => cmpOp_mono fun _ => pure_mono _
    | exact cmpOp_mono fun _ => boolToU8_mono hk
    | exact op1_mono fun _ => op1_mono hk
    | exact op1_mono hk

/-! ## 2. `uintOfNat_wp` and `uintToNat_wp` -/

theorem uintOfNat_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {w : Nat} {wa : Word} {aArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (uintOfNat rtArg w aArg k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haId : argIdsBelow aArg n) (haW : EvalWordArg ρ aArg wa)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : HUintOfNatWp rt w wa false K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk : Nat)
        (vr : BitVec w) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits w) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits w, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold HUintOfNatWp at hwp
  cases hwa : wa.toBV64? with
  | none => rw [hwa] at hwp; exact False.elim hwp
  | some va =>
    rw [hwa] at hwp
    dsimp only at hwp
    have haEv : LArg.eval ρ i64 aArg = some va := haW.toBV64? hwa
    unfold uintOfNat at hrun
    refine isScalarObj_wp hrun haEv ?_
    intro sArg ek1 ρ1 hek1 _ hagr1 hsEv
    let Inv : Val (.bits w) → Mem 64 → Prop := fun v m1 =>
      ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m1 ∧ K ⟨.bits w, v⟩ σ'
    refine withJoin1_wp (Inv := Inv) hek1 (hkMono _) ?_ ?_
    · intro r blk n2 J' hblk hr hJagr v m1 ⟨σ', hinv', hm', hK⟩ hagr rEv
      exact hk r blk _ J' (n + 4) n2 v σ' m1 (by omega) hblk hr
        ((hagr.mono (by omega : n ≤ n + 2)).trans hagr1)
        (hJagr.mono (by omega : n ≤ n + 2)) rEv hinv' hm' hK
    · intro j body _ J' _ hbody _ hjok
      rw [lm_bind_run] at hbody
      rcases hbody with ⟨slowE, _, hslowE, hrest⟩
      rw [lm_bind_run] at hrest
      rcases hrest with ⟨fastE, _, hfastE, hpure⟩
      rw [lm_pure_run] at hpure
      injection hpure with hpr
      have hbod : LExpr.jnz sArg fastE slowE = body := congrArg Prod.fst hpr
      subst hbod
      refine wp_jnz hsEv ?_ ?_
      · intro htrue
        have hsc : (va &&& 1#64) ≠ 0#64 := of_decide_eq_true htrue
        have hscb : ((va &&& 1#64) != 0#64) = true := bne_iff_ne.mpr hsc
        rw [hscb, ite_eq_left rfl] at hwp
        have ha1 : LArg.eval ρ1 i64 aArg = some va := (hagr1.eval haId).trans haEv
        refine lshr64_wp hfastE ha1 (LArg.eval_imm_self ρ1 i64 1#64) ?_
        intro xArg ek2 ρ2 hek2 hxId _ hxEv
        have hxEq : LArg.eval ρ2 i64 xArg = some (va >>> 1) := by simpa using hxEv
        refine convW_wp hek2 hxEq hxId ?_
        intro rArg ek3 ρ3 _ _ hek3 _ _ hrEv
        rw [lm_pure_run] at hek3
        injection hek3 with hp3
        have he3 : j rArg = ek3 := congrArg Prod.fst hp3
        subst he3
        exact hjok J' rArg ρ3 mem ((va >>> 1).setWidth w) (JEnvAgreeBelow.refl _ J')
          hrEv ⟨σ, hinv, hm, hwp⟩
      · intro hfalse
        have hsc : ¬ ((va &&& 1#64) ≠ 0#64) := of_decide_eq_false hfalse
        have hscb : ((va &&& 1#64) != 0#64) = false := by
          cases h : (va &&& 1#64) != 0#64
          · rfl
          · exact False.elim (hsc (bne_iff_ne.mp h))
        rw [hscb, ite_eq_right (by decide : ¬ false = true)] at hwp
        have hsp := natBitsSlow_specR0
          (by decide : 13 ∈ [9, 10, 11, 12, 13, 14, 15, 19]) hinv hm hwp
        refine natSlow_call1_conv_wp hΓ hslowE ((hagr1.eval hnrt).trans hrt)
          ((hagr1.eval haId).trans haEv) (LArg.eval_imm_self ρ1 i64 (BitVec.ofNat 64 w)) hsp ?_
        intro rArg ekS ρS _ vr σ' m' _ hekS _ _ hrEv hinv' hm' hK
        rw [lm_pure_run] at hekS
        injection hekS with hps
        have heS : j rArg = ekS := congrArg Prod.fst hps
        subst heS
        exact hjok J' rArg ρS m' vr (JEnvAgreeBelow.refl _ J') hrEv ⟨σ', hinv', hm', hK⟩

theorem uintToNat_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {w : Nat} {wa : Word} {aArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (uintToNat rtArg w aArg k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haId : argIdsBelow aArg n) (haW : EvalWordArg ρ aArg wa)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match wa.toBits? w with
      | none => False
      | some av =>
        let x := av.setWidth 64
        if w < 64 || (x >>> 63) == 0#64 then K (Word.i64 ((x <<< 1) ||| 1#64)) σ
        else HNatBitsSlowWp rt 14 x 0#64 64 K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk : Nat)
        (vr : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' i64 r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 vr) σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  cases hto : wa.toBits? w with
  | none => rw [hto] at hwp; exact False.elim hwp
  | some av =>
    rw [hto] at hwp
    dsimp only at hwp
    have haEv : LArg.eval ρ (.bits w) aArg = some av := haW.toBits? hto
    unfold uintToNat at hrun
    refine convW_wp hrun haEv haId ?_
    intro xArg ek1 ρ1 nr1 hnr1 hek1 hxId hagr1 hxEv
    by_cases hw : w < 64
    · rw [ite_eq_left hw] at hek1
      have hcond : (w < 64 || (av.setWidth 64 >>> 63) == 0#64) = true := by simp [hw]
      rw [ite_eq_left hcond] at hwp
      refine boxSmall_wp hek1 hxEv ?_
      intro rArg ek2 ρ2 hek2 hrId hagr2 hrEv
      exact hk rArg ek2 ρ2 J (nr1 + 2) n' ((av.setWidth 64 <<< 1) ||| 1#64) σ mem
        (by omega) hek2 hrId ((hagr2.mono hnr1).trans hagr1) (JEnvAgreeBelow.refl n J)
        hrEv hinv hm hwp
    · rw [ite_eq_right hw] at hek1
      let Inv : Val i64 → Mem 64 → Prop := fun v m1 =>
        ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m1 ∧ K (Word.i64 v) σ'
      refine withJoin1_wp (Inv := Inv) hek1 (hkMono _) ?_ ?_
      · intro r blk n2 J' hblk hr hJagr v m1 ⟨σ', hinv', hm', hK⟩ hagr rEv
        exact hk r blk _ J' (nr1 + 2) n2 v σ' m1 (by omega) hblk hr
          ((hagr.mono hnr1).trans hagr1) (hJagr.mono (by omega : n ≤ nr1)) rEv hinv' hm' hK
      · intro j body n2 J' hn2 hbody _ hjok
        rw [lm_bind_run] at hbody
        rcases hbody with ⟨slowE, n3, hslowE, hrest⟩
        have hn23 : n2 ≤ n3 := call1_mono (fun _ => pure_mono _) n2 slowE n3 hslowE
        rw [lm_bind_run] at hrest
        rcases hrest with ⟨fastE, n4, hfastE, hrest2⟩
        have hn34 : n3 ≤ n4 := boxSmall_mono (fun _ => pure_mono _) n3 fastE n4 hfastE
        refine lshr64_wp hrest2 hxEv (LArg.eval_imm_self ρ1 i64 63#64) ?_
        intro topArg ek2 ρ2 hek2 _ hagr2 htopEv
        have htopEq : LArg.eval ρ2 i64 topArg = some ((av.setWidth 64) >>> 63) := by
          simpa using htopEv
        refine cmpOp_wp hek2 htopEq (LArg.eval_imm_self ρ2 i64 0#64) ?_
        intro okArg ek3 ρ3 hek3 _ hagr3 hokEv
        rw [lm_pure_run] at hek3
        injection hek3 with hpr
        have hbod : LExpr.jnz okArg fastE slowE = ek3 := congrArg Prod.fst hpr
        subst hbod
        have hokEq : CmpOp.evalBits .eq ((av.setWidth 64) >>> 63) 0#64 =
            decide ((av.setWidth 64) >>> 63 = 0#64) := rfl
        rw [hokEq] at hokEv
        have hagr31 : VEnvAgreeBelow nr1 ρ3 ρ1 :=
          (hagr3.mono (by omega : nr1 ≤ n4 + 1)).trans (hagr2.mono (by omega : nr1 ≤ n4))
        have hagr30 : VEnvAgreeBelow n ρ3 ρ := (hagr31.mono hnr1).trans hagr1
        have hx3 : LArg.eval ρ3 i64 xArg = some (av.setWidth 64) :=
          (hagr31.eval hxId).trans hxEv
        refine wp_jnz hokEv ?_ ?_
        · intro hokT
          have hz : (av.setWidth 64) >>> 63 = 0#64 := of_decide_eq_true hokT
          have hcond : (w < 64 || ((av.setWidth 64) >>> 63) == 0#64) = true := by simp [hz]
          rw [ite_eq_left hcond] at hwp
          refine boxSmall_wp hfastE hx3 ?_
          intro rArg ek4 ρ4 hek4 _ _ hrEv
          rw [lm_pure_run] at hek4; injection hek4 with hp4
          have he4 : j rArg = ek4 := congrArg Prod.fst hp4; subst he4
          exact hjok J' rArg ρ4 mem (((av.setWidth 64) <<< 1) ||| 1#64)
            (JEnvAgreeBelow.refl _ J') hrEv ⟨σ, hinv, hm, hwp⟩
        · intro hokF
          have hnz : (av.setWidth 64) >>> 63 ≠ 0#64 := of_decide_eq_false hokF
          have hcond : (w < 64 || ((av.setWidth 64) >>> 63) == 0#64) = false := by
            simp [hw, hnz]
          rw [ite_eq_right (by simp [hcond])] at hwp
          have hsp := natBitsSlow_specR0
            (by decide : 14 ∈ [9, 10, 11, 12, 13, 14, 15, 19]) hinv hm hwp
          have hsig : ("lcnf_nat_slow", [i64, i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by
            decide
          have hrt3 : LArg.eval ρ3 i64 rtArg = some rt := (hagr30.eval hnrt).trans hrt
          refine call1_wp hslowE (evalArgs_cons hrt3 (evalArgs_cons (LArg.eval_imm_self ρ3 i64 _)
            (evalArgs_cons hx3 (evalArgs_cons (LArg.eval_imm_self ρ3 i64 0#64)
              (evalArgs_nil ρ3)))))
            (hΓ.rt hsig (lcnfNatSlowSpec_le_rtC0CoreEnv hsp))
            (fun _ _ _ _ hf => False.elim hf) ?_
          intro rArg ekS hekS _ res m' ⟨σ', hinv', hm', hK⟩ _ hrEv
          rw [lm_pure_run] at hekS; injection hekS with hps
          have heS : j rArg = ekS := congrArg Prod.fst hps; subst heS
          have hK' : K (Word.i64 res) σ' := by rw [BitVec.setWidth_eq] at hK; exact hK
          exact hjok J' rArg _ m' res (JEnvAgreeBelow.refl _ J') hrEv ⟨σ', hinv', hm', hK'⟩

/-! ## 3. `uintPrim_sound` Across All `isPhase1UintPrim` Ops -/

private theorem isPhase1UintPrim_1_mem {w : Nat} {op : String} {retTy : LcTy}
    (h : isPhase1UintPrim w op 1 retTy = true) :
    op = "complement" ∨ op = "neg" ∨ op = "ofNat" ∨ op = "ofNatLT" ∨ op = "ofBitVec" ∨
    op = "toUInt8" ∨ op = "toUInt16" ∨ op = "toUInt32" ∨ op = "toUInt64" ∨ op = "toUSize" ∨
    op = "toNat" ∨ op = "toBitVec" := by
  unfold isPhase1UintPrim at h
  split at h <;> simp_all

private theorem isPhase1UintPrim_2_mem {w : Nat} {op : String} {retTy : LcTy}
    (h : isPhase1UintPrim w op 2 retTy = true) :
    op = "add" ∨ op = "sub" ∨ op = "mul" ∨ op = "land" ∨ op = "lor" ∨ op = "xor" ∨
    op = "shiftLeft" ∨ op = "shiftRight" ∨ op = "div" ∨ op = "mod" ∨ op = "ofNatLT" ∨
    op = "decEq" ∨ op = "beq" ∨ op = "decLt" ∨ op = "blt" ∨ op = "decLe" ∨ op = "ble" := by
  unfold isPhase1UintPrim at h
  split at h <;> simp_all

private theorem huintPrimWp_pure_elim {rt : BitVec 64} {w : Nat} {op : String} {as : List Word}
    {r : Word} {K : HPost} {σ : HState}
    (hp : uintPure? w op as = some r) (h : HUintPrimWp rt w op as K σ) : K r σ := by
  simpa [HUintPrimWp, hp] using h

private theorem uintPrim_bin_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {w : Nat} {code : OpCode [.bits w, .bits w] [.bits w]}
    {f : BitVec w → BitVec w → BitVec w}
    {aArg bArg : LArg} {wa wb : Word} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hcode : ∀ av bv (P : Tup Val [.bits w] → Prop), code.wp (av, bv, ()) P ↔ P (f av bv, ()))
    (hrun : (op1 (.bits w) code [aArg, bArg] k).run n = .ok (e, n'))
    (haW : EvalWordArg ρ aArg wa) (hbW : EvalWordArg ρ bArg wb)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match wa.toBits? w, wb.toBits? w with
      | some av, some bv => K ⟨.bits w, f av bv⟩ σ
      | _, _ => False)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  cases hwa : wa.toBits? w with
  | none => rw [hwa] at hwp; exact False.elim hwp
  | some av =>
    cases hwb : wb.toBits? w with
    | none => rw [hwa, hwb] at hwp; exact False.elim hwp
    | some bv =>
      rw [hwa, hwb] at hwp
      dsimp only at hwp
      refine op1_wp hrun (evalArgs_cons (haW.toBits? hwa)
        (evalArgs_cons (hbW.toBits? hwb) (evalArgs_nil ρ))) ?_
      intro ek hek harg
      rw [hcode av bv]
      exact hk _ ek _ J (n + 1) n' w (f av bv) σ mem (Nat.le_succ n) hek harg
        (VEnvAgreeBelow.set (Nat.le_refl n) (.bits w) (f av bv))
        (JEnvAgreeBelow.refl n J)
        (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := .bits w } (f av bv))
        hinv hm hwp

private theorem uintPrim_divMod_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {w : Nat} {code : OpCode [.bits w, .bits w] [.bits w]}
    {f : BitVec w → BitVec w → BitVec w} {zFn : BitVec w → BitVec w}
    {aArg bArg zVal : LArg} {wa wb : Word}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hcode : ∀ av bv (P : Tup Val [.bits w] → Prop),
      code.wp (av, bv, ()) P ↔ (bv ≠ 0#w ∧ P (f av bv, ())))
    (hrun : (withJoin1 (.bits w) k fun j => do
      let e' ← op1 (.bits w) code [aArg, bArg] fun q => pure (j q)
      cmpOp .eq w bArg (imm w 0) fun z => pure (.jnz z (j zVal) e')).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (haId : argIdsBelow aArg n) (hbId : argIdsBelow bArg n)
    (haW : EvalWordArg ρ aArg wa) (hbW : EvalWordArg ρ bArg wb)
    (hz : ∀ (av : BitVec w) (ρ' : Frontend.C0.VEnv),
      LArg.eval ρ' (.bits w) aArg = some av →
      LArg.eval ρ' (.bits w) zVal = some (zFn av))
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match wa.toBits? w, wb.toBits? w with
      | some av, some bv => K ⟨.bits w, if bv = 0#w then zFn av else f av bv⟩ σ
      | _, _ => False)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  cases hwa : wa.toBits? w with
  | none => rw [hwa] at hwp; exact False.elim hwp
  | some av =>
    cases hwb : wb.toBits? w with
    | none => rw [hwa, hwb] at hwp; exact False.elim hwp
    | some bv =>
      rw [hwa, hwb] at hwp
      dsimp only at hwp
      have haEv := haW.toBits? hwa
      have hbEv := hbW.toBits? hwb
      let Inv : Val (.bits w) → Mem 64 → Prop := fun v m1 =>
        ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m1 ∧ K ⟨.bits w, v⟩ σ'
      refine withJoin1_wp (Inv := Inv) hrun (hkMono _) ?_ ?_
      · intro r blk n2 J' hblk hr hJagr v m1 ⟨σ', hinv', hm', hK⟩ hagr rEv
        exact hk r blk _ J' (n + 2) n2 w v σ' m1 (by omega) hblk hr hagr hJagr rEv hinv' hm' hK
      · intro j body n2 J' hn2 hbody _ hjok
        rw [lm_bind_run] at hbody
        rcases hbody with ⟨opE, n1, hopE, hrest⟩
        have hn21 : n2 ≤ n1 := op1_mono (fun _ => pure_mono _) n2 opE n1 hopE
        have hb0 : LArg.eval ρ (.bits w) bArg = some bv := hbEv
        refine cmpOp_wp hrest hb0 (LArg.eval_imm_self ρ (.bits w) (BitVec.ofNat w 0)) ?_
        intro zArg ek1 ρ1 hek1 _ hagr1 hzEv
        rw [lm_pure_run] at hek1
        injection hek1 with hpr
        have hbod : LExpr.jnz zArg (j zVal) opE = ek1 := congrArg Prod.fst hpr
        subst hbod
        have hzEq : CmpOp.evalBits .eq bv (BitVec.ofNat w 0) = decide (bv = 0#w) := rfl
        rw [hzEq] at hzEv
        refine wp_jnz hzEv ?_ ?_
        · intro hzT
          have hbZero : bv = 0#w := of_decide_eq_true hzT
          rw [ite_eq_left hbZero] at hwp
          have hagr10 : VEnvAgreeBelow n ρ1 ρ := hagr1.mono (by omega)
          have ha1 : LArg.eval ρ1 (.bits w) aArg = some av := (hagr10.eval haId).trans haEv
          exact hjok J' zVal ρ1 mem (zFn av) (JEnvAgreeBelow.refl _ J') (hz av ρ1 ha1)
            ⟨σ, hinv, hm, hwp⟩
        · intro hzF
          have hbNz : bv ≠ 0#w := of_decide_eq_false hzF
          rw [ite_eq_right hbNz] at hwp
          have hagr10 : VEnvAgreeBelow n ρ1 ρ := hagr1.mono (by omega)
          have ha1 : LArg.eval ρ1 (.bits w) aArg = some av := (hagr10.eval haId).trans haEv
          have hb1 : LArg.eval ρ1 (.bits w) bArg = some bv := (hagr10.eval hbId).trans hbEv
          refine op1_wp hopE (evalArgs_cons ha1 (evalArgs_cons hb1 (evalArgs_nil ρ1))) ?_
          intro ek2 hek2 _
          rw [hcode av bv]
          refine ⟨hbNz, ?_⟩
          rw [lm_pure_run] at hek2
          injection hek2 with hp2
          have he2 : j (vArg { id := n2, name := "", ty := .bits w }) = ek2 :=
            congrArg Prod.fst hp2
          subst he2
          exact hjok J' _ _ mem (f av bv) (JEnvAgreeBelow.refl _ J')
            (LArg.eval_vArg_set_self ρ1 { id := n2, name := "", ty := .bits w } (f av bv))
            ⟨σ, hinv, hm, hwp⟩

private theorem uintPrim_cmp_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {w : Nat} {o : CmpOp} {aArg bArg : LArg} {wa wb : Word}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hrun : (cmpOp o w aArg bArg fun c => boolToU8 c k).run n = .ok (e, n'))
    (haW : EvalWordArg ρ aArg wa) (hbW : EvalWordArg ρ bArg wb)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match wa.toBits? w, wb.toBits? w with
      | some av, some bv => K (Word.i8 (if o.evalBits av bv then 1#8 else 0#8)) σ
      | _, _ => False)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  cases hwa : wa.toBits? w with
  | none => rw [hwa] at hwp; exact False.elim hwp
  | some av =>
    cases hwb : wb.toBits? w with
    | none => rw [hwa, hwb] at hwp; exact False.elim hwp
    | some bv =>
      rw [hwa, hwb] at hwp
      dsimp only at hwp
      refine cmpOp_wp hrun (haW.toBits? hwa) (hbW.toBits? hwb) ?_
      intro cArg ek1 ρ1 hek1 _ hagr1 hcEv
      refine boolToU8_wp hek1 hcEv ?_
      intro rArg ek2 ρ2 hek2 hrId hagr2 hrEv
      exact hk rArg ek2 ρ2 J (n + 2) n' 8 _ σ mem (by omega) hek2 hrId
        ((hagr2.mono (Nat.le_succ n)).trans hagr1) (JEnvAgreeBelow.refl n J)
        hrEv hinv hm hwp

private theorem uintPrim_cast_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {w dst : Nat} {aArg : LArg} {wa : Word} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hrun : (convW w dst aArg k).run n = .ok (e, n'))
    (haId : argIdsBelow aArg n) (haW : EvalWordArg ρ aArg wa)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match wa.toBits? w with
      | some av => K ⟨.bits dst, av.setWidth dst⟩ σ
      | none => False)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  cases hwa : wa.toBits? w with
  | none => rw [hwa] at hwp; exact False.elim hwp
  | some av =>
    rw [hwa] at hwp
    dsimp only at hwp
    refine convW_wp hrun (haW.toBits? hwa) haId ?_
    intro rArg ek1 ρ1 nr1 hnr1 hek1 hrId hagr1 hrEv
    exact hk rArg ek1 ρ1 J nr1 n' dst (av.setWidth dst) σ mem hnr1 hek1 hrId hagr1
      (JEnvAgreeBelow.refl n J) hrEv hinv hm hwp

theorem uintPrim_sound {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {w : Nat} {op : String} {args : List LArg}
    {retTy : LcTy} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {ws : List Word} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (hprim : isPhase1UintPrim w op args.length retTy = true)
    (hrun : (uintPrim rtArg w op args k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hargsIds : ∀ a ∈ args, argIdsBelow a n) (hargsEv : EvalWordArgs ρ args ws)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : HUintPrimWp rt w op ws K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  have hnotF : (Ty.bits w).hasFloat = false := rfl
  rcases args with _ | ⟨aArg, _ | ⟨bArg, _ | _⟩⟩
  · simp [isPhase1UintPrim] at hprim
  · rcases ws with _ | ⟨wa, _ | _⟩
    · simp [EvalWordArgs] at hargsEv
    · have haId : argIdsBelow aArg n := hargsIds aArg List.mem_cons_self
      have haW : EvalWordArg ρ aArg wa := hargsEv.2 (aArg, wa) List.mem_cons_self
      rcases isPhase1UintPrim_1_mem hprim with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl
      · -- "complement"
        simp only [HUintPrimWp, uintPure?] at hwp
        cases hwa : wa.toBits? w with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some av =>
          rw [hwa] at hwp
          unfold uintPrim at hrun
          refine op1_wp hrun (evalArgs_cons (haW.toBits? hwa) (evalArgs_nil ρ)) ?_
          intro ek hek harg
          rw [OpCode.wp_not]
          exact hk _ ek _ J (n + 1) n' w (~~~av) σ mem (Nat.le_succ n) hek harg
            (VEnvAgreeBelow.set (Nat.le_refl n) (.bits w) (~~~av))
            (JEnvAgreeBelow.refl n J)
            (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := .bits w } (~~~av))
            hinv hm hwp
      · -- "neg"
        simp only [HUintPrimWp, uintPure?] at hwp
        cases hwa : wa.toBits? w with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some av =>
          rw [hwa] at hwp
          unfold uintPrim at hrun
          refine op1_wp hrun (evalArgs_cons (haW.toBits? hwa) (evalArgs_nil ρ)) ?_
          intro ek hek harg
          rw [OpCode.wp_neg, ite_eq_right (by simp [Ty.hasFloat])]
          exact hk _ ek _ J (n + 1) n' w (-av) σ mem (Nat.le_succ n) hek harg
            (VEnvAgreeBelow.set (Nat.le_refl n) (.bits w) (-av))
            (JEnvAgreeBelow.refl n J)
            (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := .bits w } (-av))
            hinv hm hwp
      · -- "ofNat"
        simp only [HUintPrimWp, uintPure?] at hwp
        unfold uintPrim at hrun
        exact uintOfNat_wp hΓ hrun hkMono hrt hnrt haId haW hinv hm hwp fun r ek ρ' J' nr nk vr
          σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK =>
          hk r ek ρ' J' nr nk w vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
      · -- "ofNatLT"
        simp only [HUintPrimWp, uintPure?] at hwp
        unfold uintPrim at hrun
        exact uintOfNat_wp hΓ hrun hkMono hrt hnrt haId haW hinv hm hwp fun r ek ρ' J' nr nk vr
          σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK =>
          hk r ek ρ' J' nr nk w vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
      · -- "ofBitVec"
        simp only [HUintPrimWp, uintPure?] at hwp
        unfold uintPrim at hrun
        cases hwa : wa.toBV64? with
        | none => simp [HUintOfNatWp, hwa] at hwp
        | some va =>
          have haEv : LArg.eval ρ i64 aArg = some va := haW.toBV64? hwa
          have hwp' : HUintOfNatWp rt w wa false
              (fun r σ' => HDecN va .tobject true 1 (K r) σ') σ := by
            simpa [HUintOfNatWp, hwa] using hwp
          refine uintOfNat_wp hΓ hrun (fun _ => emitDec1_mono (hkMono _))
            hrt hnrt haId haW hinv hm hwp' ?_
          intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hdec
          have hrt' : LArg.eval ρ' i64 rtArg = some rt := (hagr.eval hnrt).trans hrt
          have ha' : LArg.eval ρ' i64 aArg = some va := (hagr.eval haId).trans haEv
          refine emitDec1_wp hΓ hek (hkMono r) hrt' (argIdsBelow_mono hnr hnrt) ha'
            (argIdsBelow_mono hnr haId) hdec.1 hinv' hm' ?_
          intro ek2 ρ2 J2 nr2 nk2 σ'' m'' hnr2 hek2 hagr2 hJagr2 hinv'' hm'' hrel
          exact hk r ek2 ρ2 J2 nr2 nk2 w vr σ'' m'' (Nat.le_trans hnr hnr2) hek2
            (argIdsBelow_mono hnr2 hr) (hagr2.mono hnr |>.trans hagr)
            (hJagr2.mono hnr |>.trans hJagr) ((hagr2.eval hr).trans hrEv) hinv'' hm''
            (hdec.2 σ'' hrel)
      · -- "toUInt8"
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av =>
          have hK := huintPrimWp_pure_elim (r := ⟨.bits 8, av.setWidth 8⟩)
            (by simp [uintPure?, hwa, Word.i8]) hwp
          unfold uintPrim at hrun
          exact uintPrim_cast_wp hrun haId haW hinv hm (by simpa [hwa] using hK) hk
      · -- "toUInt16"
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av =>
          have hK := huintPrimWp_pure_elim (r := ⟨.bits 16, av.setWidth 16⟩)
            (by simp [uintPure?, hwa, Word.i16]) hwp
          unfold uintPrim at hrun
          exact uintPrim_cast_wp hrun haId haW hinv hm (by simpa [hwa] using hK) hk
      · -- "toUInt32"
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av =>
          have hK := huintPrimWp_pure_elim (r := ⟨.bits 32, av.setWidth 32⟩)
            (by simp [uintPure?, hwa, Word.i32]) hwp
          unfold uintPrim at hrun
          exact uintPrim_cast_wp hrun haId haW hinv hm (by simpa [hwa] using hK) hk
      · -- "toUInt64"
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av =>
          have hK := huintPrimWp_pure_elim (r := ⟨.bits 64, av.setWidth 64⟩)
            (by simp [uintPure?, hwa, Word.i64]) hwp
          unfold uintPrim at hrun
          exact uintPrim_cast_wp hrun haId haW hinv hm (by simpa [hwa] using hK) hk
      · -- "toUSize"
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av =>
          have hK := huintPrimWp_pure_elim (r := ⟨.bits 64, av.setWidth 64⟩)
            (by simp [uintPure?, hwa, Word.i64]) hwp
          unfold uintPrim at hrun
          exact uintPrim_cast_wp hrun haId haW hinv hm (by simpa [hwa] using hK) hk
      · -- "toNat"
        simp only [HUintPrimWp, uintPure?] at hwp
        unfold uintPrim at hrun
        exact uintToNat_wp hΓ hrun hkMono hrt hnrt haId haW hinv hm hwp fun r ek ρ' J' nr nk vr
          σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK =>
          hk r ek ρ' J' nr nk 64 vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
      · -- "toBitVec"
        simp only [HUintPrimWp, uintPure?] at hwp
        unfold uintPrim at hrun
        exact uintToNat_wp hΓ hrun hkMono hrt hnrt haId haW hinv hm hwp fun r ek ρ' J' nr nk vr
          σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK =>
          hk r ek ρ' J' nr nk 64 vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · rcases ws with _ | ⟨wa, _ | ⟨wb, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have haId : argIdsBelow aArg n := hargsIds aArg List.mem_cons_self
      have hbId : argIdsBelow bArg n := hargsIds bArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have haW : EvalWordArg ρ aArg wa := hargsEv.2 (aArg, wa) List.mem_cons_self
      have hbW : EvalWordArg ρ bArg wb :=
        hargsEv.2 (bArg, wb) (List.mem_cons_of_mem _ List.mem_cons_self)
      rcases isPhase1UintPrim_2_mem hprim with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine uintPrim_bin_wp (f := (· + ·)) (fun av bv P => by simp [hnotF, lift2])
          hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv => exact huintPrimWp_pure_elim (by simp [uintPure?, hwa, hwb]) hwp
      · refine uintPrim_bin_wp (f := (· - ·)) (fun av bv P => by simp [hnotF, lift2])
          hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv => exact huintPrimWp_pure_elim (by simp [uintPure?, hwa, hwb]) hwp
      · refine uintPrim_bin_wp (f := (· * ·)) (fun av bv P => by simp [hnotF, lift2])
          hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv => exact huintPrimWp_pure_elim (by simp [uintPure?, hwa, hwb]) hwp
      · refine uintPrim_bin_wp (f := (· &&& ·)) (fun av bv P => by simp [lift2])
          hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv => exact huintPrimWp_pure_elim (by simp [uintPure?, hwa, hwb]) hwp
      · refine uintPrim_bin_wp (f := (· ||| ·)) (fun av bv P => by simp [lift2])
          hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv => exact huintPrimWp_pure_elim (by simp [uintPure?, hwa, hwb]) hwp
      · refine uintPrim_bin_wp (f := (· ^^^ ·)) (fun av bv P => by simp [lift2])
          hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv => exact huintPrimWp_pure_elim (by simp [uintPure?, hwa, hwb]) hwp
      · -- "shiftLeft"
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av =>
          cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv =>
            have hK := huintPrimWp_pure_elim
              (r := ⟨.bits w, av <<< (bv &&& BitVec.ofNat w (w - 1))⟩)
              (by unfold uintPure?; simp only [hwa, hwb]) hwp
            unfold uintPrim at hrun
            refine op1_wp hrun (evalArgs_cons (hbW.toBits? hwb)
              (evalArgs_cons (LArg.eval_imm_self ρ (.bits w) _) (evalArgs_nil ρ))) ?_
            intro ek1 hek1 hsId
            rw [OpCode.wp_and]
            let sV : Frontend.C0.LVar := { id := n, name := "", ty := .bits w }
            let sv := bv &&& BitVec.ofNat w (w - 1)
            let ρ1 := ρ.set n (.bits w) sv
            have ha1 : LArg.eval ρ1 (.bits w) aArg = some av :=
              (VEnvAgreeBelow.set (Nat.le_refl n) (.bits w) sv |>.eval haId).trans
                (haW.toBits? hwa)
            have hs1 : LArg.eval ρ1 (.bits w) (vArg sV) = some sv :=
              LArg.eval_vArg_set_self ρ sV sv
            refine op1_wp hek1 (evalArgs_cons ha1 (evalArgs_cons hs1 (evalArgs_nil ρ1))) ?_
            intro ek2 hek2 hrId
            rw [OpCode.wp_shl, ite_eq_right (by simp [Ty.hasFloat])]
            dsimp only [lift2]
            have hmod : sv.toNat % w = sv.toNat := uint_shift_mod_eq hw bv
            rw [hmod]
            exact hk _ ek2 _ J (n + 2) n' w (av <<< sv) σ mem (by omega) hek2 hrId
              ((VEnvAgreeBelow.set (Nat.le_succ n) (.bits w) _).trans
                (VEnvAgreeBelow.set (Nat.le_refl n) (.bits w) sv))
              (JEnvAgreeBelow.refl n J)
              (LArg.eval_vArg_set_self ρ1 { id := n + 1, name := "", ty := .bits w } _)
              hinv hm hK
      · -- "shiftRight"
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av =>
          cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv =>
            have hK := huintPrimWp_pure_elim
              (r := ⟨.bits w, av >>> (bv &&& BitVec.ofNat w (w - 1))⟩)
              (by unfold uintPure?; simp only [hwa, hwb]) hwp
            unfold uintPrim at hrun
            refine op1_wp hrun (evalArgs_cons (hbW.toBits? hwb)
              (evalArgs_cons (LArg.eval_imm_self ρ (.bits w) _) (evalArgs_nil ρ))) ?_
            intro ek1 hek1 hsId
            rw [OpCode.wp_and]
            let sV : Frontend.C0.LVar := { id := n, name := "", ty := .bits w }
            let sv := bv &&& BitVec.ofNat w (w - 1)
            let ρ1 := ρ.set n (.bits w) sv
            have ha1 : LArg.eval ρ1 (.bits w) aArg = some av :=
              (VEnvAgreeBelow.set (Nat.le_refl n) (.bits w) sv |>.eval haId).trans
                (haW.toBits? hwa)
            have hs1 : LArg.eval ρ1 (.bits w) (vArg sV) = some sv :=
              LArg.eval_vArg_set_self ρ sV sv
            refine op1_wp hek1 (evalArgs_cons ha1 (evalArgs_cons hs1 (evalArgs_nil ρ1))) ?_
            intro ek2 hek2 hrId
            rw [OpCode.wp_lshr, ite_eq_right (by simp [Ty.hasFloat])]
            dsimp only [lift2]
            have hmod : sv.toNat % w = sv.toNat := uint_shift_mod_eq hw bv
            rw [hmod]
            exact hk _ ek2 _ J (n + 2) n' w (av >>> sv) σ mem (by omega) hek2 hrId
              ((VEnvAgreeBelow.set (Nat.le_succ n) (.bits w) _).trans
                (VEnvAgreeBelow.set (Nat.le_refl n) (.bits w) sv))
              (JEnvAgreeBelow.refl n J)
              (LArg.eval_vArg_set_self ρ1 { id := n + 1, name := "", ty := .bits w } _)
              hinv hm hK
      · -- "div"
        unfold uintPrim at hrun
        refine uintPrim_divMod_wp (f := (· / ·)) (zFn := fun _ => 0#w)
          (fun av bv P => by simp [OpCode.wp_udiv]) hrun hkMono haId hbId haW hbW
          (fun _ ρ' _ => LArg.eval_imm_self ρ' (.bits w) (BitVec.ofNat w 0))
          hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv => exact huintPrimWp_pure_elim (by simp [uintPure?, hwa, hwb]) hwp
      · -- "mod"
        unfold uintPrim at hrun
        refine uintPrim_divMod_wp (f := (· % ·)) (zFn := id)
          (fun av bv P => by simp [OpCode.wp_urem]) hrun hkMono haId hbId haW hbW
          (fun _ _ ha => ha) hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv => exact huintPrimWp_pure_elim (by simp [uintPure?, hwa, hwb]) hwp
      · -- "ofNatLT" (arity 2)
        simp only [HUintPrimWp, uintPure?] at hwp
        unfold uintPrim at hrun
        exact uintOfNat_wp hΓ hrun hkMono hrt hnrt haId haW hinv hm hwp fun r ek ρ' J' nr nk vr
          σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK =>
          hk r ek ρ' J' nr nk w vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
      · refine uintPrim_cmp_wp hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv =>
            simpa [hwa, hwb] using
              huintPrimWp_pure_elim (r := Word.i8 (if (av == bv) then 1#8 else 0#8))
                (by simp [uintPure?, hwa, hwb]) hwp
      · refine uintPrim_cmp_wp hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv =>
            simpa [hwa, hwb] using
              huintPrimWp_pure_elim (r := Word.i8 (if (av == bv) then 1#8 else 0#8))
                (by simp [uintPure?, hwa, hwb]) hwp
      · refine uintPrim_cmp_wp hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv =>
            dsimp only
            exact huintPrimWp_pure_elim
              (r := Word.i8 (if CmpOp.ult.evalBits av bv then 1#8 else 0#8))
              (by simp [uintPure?, hwa, hwb, CmpOp.evalBits, BitVec.ult, BitVec.lt_def]) hwp
      · refine uintPrim_cmp_wp hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv =>
            dsimp only
            exact huintPrimWp_pure_elim
              (r := Word.i8 (if CmpOp.ult.evalBits av bv then 1#8 else 0#8))
              (by simp [uintPure?, hwa, hwb, CmpOp.evalBits, BitVec.ult, BitVec.lt_def]) hwp
      · refine uintPrim_cmp_wp hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv =>
            dsimp only
            exact huintPrimWp_pure_elim
              (r := Word.i8 (if CmpOp.ule.evalBits av bv then 1#8 else 0#8))
              (by simp [uintPure?, hwa, hwb, CmpOp.evalBits, BitVec.ule, BitVec.le_def]) hwp
      · refine uintPrim_cmp_wp hrun haW hbW hinv hm ?_ hk
        cases hwa : wa.toBits? w with
        | none => simp [HUintPrimWp, uintPure?, hwa] at hwp
        | some av => cases hwb : wb.toBits? w with
          | none => simp [HUintPrimWp, uintPure?, hwa, hwb] at hwp
          | some bv =>
            dsimp only
            exact huintPrimWp_pure_elim
              (r := Word.i8 (if CmpOp.ule.evalBits av bv then 1#8 else 0#8))
              (by simp [uintPure?, hwa, hwb, CmpOp.evalBits, BitVec.ule, BitVec.le_def]) hwp
    · simp [EvalWordArgs] at hargsEv
  · simp [isPhase1UintPrim] at hprim

end LeanQbe.T.LeanLCNF.Sem
