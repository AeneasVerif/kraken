module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound2NatHelpers

/-!
# Tier-H `Nat.*` Primitive Lowering Soundness (`LowerSound2a`)

Proves `natPrim_sound` across all 21 `isPhase1NatPrim` operations using `LowerSound2` and
`LowerSound2NatHelpers`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

private theorem isPhase1NatPrim_1_mem {op : String} {retTy : LcTy}
    (h : isPhase1NatPrim op 1 retTy = true) :
    op = "pred" ∨ op = "log2" ∨ op = "reprFast" := by
  unfold isPhase1NatPrim at h
  split at h <;> simp_all

private theorem isPhase1NatPrim_2_mem {op : String} {retTy : LcTy}
    (h : isPhase1NatPrim op 2 retTy = true) :
    op = "add" ∨ op = "sub" ∨ op = "mul" ∨ op = "div" ∨ op = "mod" ∨
    op = "shiftRight" ∨ op = "land" ∨ op = "lor" ∨ op = "xor" ∨ op = "shiftLeft" ∨
    op = "pow" ∨ op = "gcd" ∨ op = "decEq" ∨ op = "beq" ∨ op = "decLt" ∨
    op = "blt" ∨ op = "decLe" ∨ op = "ble" := by
  unfold isPhase1NatPrim at h
  split at h <;> simp_all

private theorem natPrim_shr_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natBin rtArg "shiftRight" 64 aArg bArg (fun _ j =>
      lshr64 bArg (imm64 1) fun y => cmpOp .ult 64 y (imm64 63) fun ok => do
        let e ← add64 y (imm64 1) fun y1 =>
          lshr64 aArg y1 fun x => boxSmall x fun r => pure (j r)
        pure (.jnz ok e (j (imm64 1)))) k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haEv : LArg.eval ρ i64 aArg = some va) (haId : argIdsBelow aArg n)
    (hbEv : LArg.eval ρ i64 bArg = some vb) (hbId : argIdsBelow bArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match natBinFast? "shiftRight" va vb with
      | some w => K w σ
      | none => HNatBitsSlowWp rt 9 va vb 64 K σ)
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
      bind_mono (add64_mono fun _ => lshr64_mono fun _ => boxSmall_mono fun _ => pure_mono _)
        fun _ => pure_mono _)
    hkMono hrt hnrt haEv haId hbEv hbId ?_ ?_ ?_
  · intro hsc0
    have hnone : natBinFast? "shiftRight" va vb = none := by simp [natBinFast?, hsc0]
    rw [hnone] at hwp
    exact natBitsSlow_specR0 (by decide) hinv hm hwp
  · intro hsc j body _ _ J' ρ2 _ _ _ hbody _ ha2 hb2 hna2 _ _ hj
    refine lshr64_wp hbody hb2 (LArg.eval_imm_self ρ2 i64 1#64) ?_
    intro yArg ek1 ρ1 hek1 hyId hagr1 hyEv
    have hyEq : LArg.eval ρ1 i64 yArg = some (vb >>> 1) := by simpa using hyEv
    refine cmpOp_wp hek1 hyEq (LArg.eval_imm_self ρ1 i64 63#64) ?_
    intro okArg ek2 ρ3 hek2 _ hagr3 hokEv
    rw [lm_bind_run] at hek2
    rcases hek2 with ⟨eShr, _, heShr, hp⟩
    rw [lm_pure_run] at hp
    injection hp with hpr
    have hbod : LExpr.jnz okArg eShr (j (imm64 1)) = ek2 := congrArg Prod.fst hpr
    subst hbod
    have hokEq : CmpOp.evalBits .ult (vb >>> 1) 63#64 = decide (vb >>> 1 < 63#64) := rfl
    rw [hokEq] at hokEv
    have hsome : natBinFast? "shiftRight" va vb =
        some (Word.i64 (if (vb >>> 1).toNat < 63 then
          (((va >>> ((vb >>> 1).toNat + 1)) <<< 1) ||| 1#64) else 1#64)) := by
      simp [natBinFast?, hsc]
    rw [hsome] at hwp
    refine wp_jnz hokEv ?_ ?_
    · intro hokT
      have hy63 : (vb >>> 1).toNat < 63 := of_decide_eq_true hokT
      rw [ite_eq_left hy63] at hwp
      have hy3 : LArg.eval ρ3 i64 yArg = some (vb >>> 1) := (hagr3.eval hyId).trans hyEq
      refine add64_wp heShr hy3 (LArg.eval_imm_self ρ3 i64 1#64) ?_
      intro y1Arg ek3 ρ4 hek3 _ hagr4 hy1Ev
      have ha4 : LArg.eval ρ4 i64 aArg = some va :=
        (hagr4.eval (argIdsBelow_mono (by omega) hna2)).trans
          ((hagr3.eval (argIdsBelow_mono (by omega) hna2)).trans
            ((hagr1.eval hna2).trans ha2))
      refine lshr64_wp hek3 ha4 hy1Ev ?_
      intro xArg ek4 ρ5 hek4 _ _ hxEv
      refine boxSmall_wp hek4 hxEv ?_
      intro rArg ek5 ρ6 hek5 _ _ hrEv
      rw [lm_pure_run] at hek5
      injection hek5 with hp5
      have he5 : j rArg = ek5 := congrArg Prod.fst hp5
      subst he5
      rw [bv64_shr_fast_eq va (vb >>> 1) hy63] at hrEv
      exact hj J' rArg ρ6 mem _ σ (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
    · intro hokF
      have hny63 : ¬ ((vb >>> 1).toNat < 63) := fun h => of_decide_eq_false hokF h
      rw [ite_eq_right hny63] at hwp
      exact hj J' (imm64 1) ρ3 mem 1#64 σ (JEnvAgreeBelow.refl _ J')
        (LArg.eval_imm_self ρ3 i64 1#64) hinv hm hwp
  · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv hinv' hm' hK

private theorem natPrim_shl_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (natBin rtArg "shiftLeft" 64 aArg bArg (fun slow j =>
      lshr64 bArg (imm64 1) fun y => cmpOp .ult 64 y (imm64 63) fun ok => do
        let sh ← lshr64 aArg (imm64 1) fun x => shl64 x y fun z =>
          lshr64 z y fun x' => cmpOp .eq 64 x' x fun ok1 =>
          lshr64 z (imm64 63) fun top => cmpOp .eq 64 top (imm64 0) fun ok2 => do
            let boxed ← boxSmall z fun r => pure (j r)
            let sE2 ← slow
            let sE1 ← slow
            pure (.jnz ok1 (.jnz ok2 boxed sE2) sE1)
        let sE0 ← slow
        pure (.jnz ok sh sE0)) k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haEv : LArg.eval ρ i64 aArg = some va) (haId : argIdsBelow aArg n)
    (hbEv : LArg.eval ρ i64 bArg = some vb) (hbId : argIdsBelow bArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match natBinFast? "shiftLeft" va vb with
      | some w => K w σ
      | none => HNatBitsSlowWp rt 15 va vb 64 K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  dsimp only [natBin, natOpCode] at hrun
  refine tagBin_wp (R := R) (K := K) hΓ hrun
    (fun _ _ hslow => lshr64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono (lshr64_mono fun _ => shl64_mono fun _ => lshr64_mono fun _ =>
        cmpOp_mono fun _ => lshr64_mono fun _ => cmpOp_mono fun _ =>
          bind_mono (boxSmall_mono fun _ => pure_mono _) fun _ =>
          bind_mono hslow fun _ => bind_mono hslow fun _ => pure_mono _)
        fun _ => bind_mono hslow fun _ => pure_mono _)
    hkMono hrt hnrt haEv haId hbEv hbId ?_ ?_ ?_
  · intro hsc0
    have hnone : natBinFast? "shiftLeft" va vb = none := by simp [natBinFast?, hsc0]
    rw [hnone] at hwp
    exact natBitsSlow_specR0 (by decide) hinv hm hwp
  · intro hsc j body n2 _ J' ρ2 slow _ hslowEq hbody hagr20 ha2 hb2 hna2 _ hslowR hj
    refine lshr64_wp hbody hb2 (LArg.eval_imm_self ρ2 i64 1#64) ?_
    intro yArg ek1 ρ1 hek1 hyId hagr1 hyEv
    have hyEq : LArg.eval ρ1 i64 yArg = some (vb >>> 1) := by simpa using hyEv
    refine cmpOp_wp hek1 hyEq (LArg.eval_imm_self ρ1 i64 63#64) ?_
    intro okArg ek2 ρ3 hek2 _ hagr3 hokEv
    rw [lm_bind_run] at hek2
    rcases hek2 with ⟨shE, nSh, hshE, hrest2⟩
    rw [lm_bind_run] at hrest2
    rcases hrest2 with ⟨sE0, nS0, hsE0, hp2⟩
    rw [lm_pure_run] at hp2
    injection hp2 with hpr2
    have hbod2 : LExpr.jnz okArg shE sE0 = ek2 := congrArg Prod.fst hpr2
    subst hbod2
    have hokEq : CmpOp.evalBits .ult (vb >>> 1) 63#64 = decide (vb >>> 1 < 63#64) := rfl
    rw [hokEq] at hokEv
    have hagr30 : VEnvAgreeBelow n ρ3 ρ :=
      ((hagr3.mono (by omega : n ≤ n2 + 1)).trans (hagr1.mono (by omega : n ≤ n2))).trans hagr20
    refine wp_jnz hokEv ?_ ?_
    · intro hokT
      have hy63 : (vb >>> 1).toNat < 63 := of_decide_eq_true hokT
      have hyMod : (vb >>> 1).toNat % 64 = (vb >>> 1).toNat := Nat.mod_eq_of_lt (by omega)
      have ha3 : LArg.eval ρ3 i64 aArg = some va :=
        (hagr3.eval (argIdsBelow_mono (by omega) hna2)).trans ((hagr1.eval hna2).trans ha2)
      refine lshr64_wp hshE ha3 (LArg.eval_imm_self ρ3 i64 1#64) ?_
      intro xArg ek3 ρ4 hek3 hxId hagr4 hxEv
      have hxEq : LArg.eval ρ4 i64 xArg = some (va >>> 1) := by simpa using hxEv
      have hy4 : LArg.eval ρ4 i64 yArg = some (vb >>> 1) :=
        (hagr4.eval (argIdsBelow_mono (by omega) hyId)).trans ((hagr3.eval hyId).trans hyEq)
      refine shl64_wp hek3 hxEq hy4 ?_
      intro zArg ek4 ρ5 hek4 hzId hagr5 hzEv
      rw [hyMod] at hzEv
      let zVal := (va >>> 1) <<< (vb >>> 1).toNat
      have hy5 : LArg.eval ρ5 i64 yArg = some (vb >>> 1) :=
        (hagr5.eval (argIdsBelow_mono (by omega) hyId)).trans hy4
      refine lshr64_wp hek4 hzEv hy5 ?_
      intro xpArg ek5 ρ6 hek5 _ hagr6 hxpEv
      rw [hyMod] at hxpEv
      have hx6 : LArg.eval ρ6 i64 xArg = some (va >>> 1) :=
        (hagr6.eval (argIdsBelow_mono (by omega) hxId)).trans
          ((hagr5.eval (argIdsBelow_mono (by omega) hxId)).trans hxEq)
      refine cmpOp_wp hek5 hxpEv hx6 ?_
      intro ok1Arg ek6 ρ7 hek6 hok1Id hagr7 hok1Ev
      have hz7 : LArg.eval ρ7 i64 zArg = some zVal :=
        (hagr7.eval (argIdsBelow_mono (by omega) hzId)).trans
          ((hagr6.eval (argIdsBelow_mono (by omega) hzId)).trans hzEv)
      refine lshr64_wp hek6 hz7 (LArg.eval_imm_self ρ7 i64 63#64) ?_
      intro topArg ek7 ρ8 hek7 _ hagr8 htopEv
      refine cmpOp_wp hek7 htopEv (LArg.eval_imm_self ρ8 i64 0#64) ?_
      intro ok2Arg ek8 ρ9 hek8 _ hagr9 hok2Ev
      rw [lm_bind_run] at hek8
      rcases hek8 with ⟨boxedE, nBox, hboxedE, hrest8⟩
      rw [lm_bind_run] at hrest8
      rcases hrest8 with ⟨sE2, nS2, hsE2, hrest9⟩
      rw [lm_bind_run] at hrest9
      rcases hrest9 with ⟨sE1, nS1, hsE1, hp9⟩
      rw [lm_pure_run] at hp9
      injection hp9 with hpr9
      have hbod9 : LExpr.jnz ok1Arg (LExpr.jnz ok2Arg boxedE sE2) sE1 = ek8 :=
        congrArg Prod.fst hpr9
      subst hbod9
      have hagr90 : VEnvAgreeBelow n ρ9 ρ :=
        ((hagr9.mono (by omega : n ≤ n2 + 7)).trans
          ((hagr8.mono (by omega : n ≤ n2 + 6)).trans
            ((hagr7.mono (by omega : n ≤ n2 + 5)).trans
              ((hagr6.mono (by omega : n ≤ n2 + 4)).trans
                ((hagr5.mono (by omega : n ≤ n2 + 3)).trans
                  (hagr4.mono (by omega : n ≤ n2 + 2))))))).trans hagr30
      have hok1Eq : CmpOp.evalBits .eq (zVal >>> (vb >>> 1).toNat) (va >>> 1) =
          decide (zVal >>> (vb >>> 1).toNat = va >>> 1) := rfl
      rw [hok1Eq] at hok1Ev
      have hok1Ev9 :
          LArg.eval ρ9 .bool ok1Arg = some (decide (zVal >>> (vb >>> 1).toNat = va >>> 1)) :=
        (hagr9.eval (argIdsBelow_mono (by omega) hok1Id)).trans
          ((hagr8.eval (argIdsBelow_mono (by omega) hok1Id)).trans hok1Ev)
      have hok2Eq : CmpOp.evalBits .eq (zVal >>> 63) 0#64 = decide (zVal >>> 63 = 0#64) := rfl
      have htop63 : (63#64 : BitVec 64).toNat % 64 = 63 := by decide
      rw [htop63] at hok2Ev
      rw [hok2Eq] at hok2Ev
      have hiff := bv64_shl_fast_iff (va >>> 1) (vb >>> 1) (bv64_shr1_lt va) hy63
      have hy63' : vb.toNat >>> 1 < 63 := by simpa [BitVec.toNat_ushiftRight] using hy63
      have hslowM : LMMono slow := hslowEq ▸ call1_mono fun _ => convW_mono fun _ => pure_mono _
      have hnw : n2 + 8 ≤ nBox :=
        (boxSmall_mono fun _ => pure_mono _) (n2 + 8) boxedE nBox hboxedE
      have hnS2 : nBox ≤ nS2 := hslowM nBox sE2 nS2 hsE2
      refine wp_jnz hok1Ev9 ?_ ?_
      · intro hok1T
        have h1 : zVal >>> (vb >>> 1).toNat = va >>> 1 := of_decide_eq_true hok1T
        refine wp_jnz hok2Ev ?_ ?_
        · intro hok2T
          have h2 : zVal >>> 63 = 0#64 := of_decide_eq_true hok2T
          have hltShl : (va >>> 1).toNat <<< (vb >>> 1).toNat < 2 ^ 63 := hiff.mp ⟨h1, h2⟩
          have hltShl' : va.toNat >>> 1 <<< (vb.toNat >>> 1) < 2 ^ 63 := by
            simpa [BitVec.toNat_ushiftRight] using hltShl
          have hsome : natBinFast? "shiftLeft" va vb =
              some (Word.i64 (BitVec.ofNat 64
                (2 * ((va >>> 1).toNat <<< (vb >>> 1).toNat) + 1))) := by
            simp [natBinFast?, hsc, hy63', hltShl']
          rw [hsome] at hwp
          have hz9 : LArg.eval ρ9 i64 zArg = some zVal :=
            (hagr9.eval (argIdsBelow_mono (by omega) hzId)).trans
              ((hagr8.eval (argIdsBelow_mono (by omega) hzId)).trans hz7)
          refine boxSmall_wp hboxedE hz9 ?_
          intro rArg ek9 ρ10 hek9 _ _ hrEv
          rw [lm_pure_run] at hek9
          injection hek9 with hp10
          have he10 : j rArg = ek9 := congrArg Prod.fst hp10
          subst he10
          have hzNat : zVal.toNat = (va >>> 1).toNat <<< (vb >>> 1).toNat := by
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
            rw [Nat.shiftLeft_eq] at hltShl
            exact Nat.mod_eq_of_lt (Nat.lt_trans hltShl (by decide))
          have hbx := bv64_box_self_eq zVal (hzNat ▸ hltShl)
          rw [hzNat] at hbx
          rw [hbx] at hrEv
          exact hj J' rArg ρ10 mem _ σ (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
        · intro hok2F
          have h2 : ¬ (zVal >>> 63 = 0#64) := of_decide_eq_false hok2F
          have hnot : ¬ ((va >>> 1).toNat <<< (vb >>> 1).toNat < 2 ^ 63) := fun h =>
            h2 (hiff.mpr h).2
          have hnot' : ¬ (va.toNat >>> 1 <<< (vb.toNat >>> 1) < 2 ^ 63) := by
            simpa [BitVec.toNat_ushiftRight] using hnot
          have hnone : natBinFast? "shiftLeft" va vb = none := by
            simp [natBinFast?, hsc, hy63', hnot']
          rw [hnone] at hwp
          exact hslowR _ nS2 sE2 ρ9 J' (by omega) hsE2 hagr90
            (JEnvAgreeBelow.refl _ J') (natBitsSlow_specR0 (by decide) hinv hm hwp)
      · intro hok1F
        have h1 : ¬ (zVal >>> (vb >>> 1).toNat = va >>> 1) := of_decide_eq_false hok1F
        have hnot : ¬ ((va >>> 1).toNat <<< (vb >>> 1).toNat < 2 ^ 63) := fun h =>
          h1 (hiff.mpr h).1
        have hnot' : ¬ (va.toNat >>> 1 <<< (vb.toNat >>> 1) < 2 ^ 63) := by
          simpa [BitVec.toNat_ushiftRight] using hnot
        have hnone : natBinFast? "shiftLeft" va vb = none := by
          simp [natBinFast?, hsc, hy63', hnot']
        rw [hnone] at hwp
        exact hslowR _ nS1 sE1 ρ9 J' (by omega) hsE1 hagr90
          (JEnvAgreeBelow.refl _ J') (natBitsSlow_specR0 (by decide) hinv hm hwp)
    · intro hokF
      have hny63 : ¬ (vb.toNat >>> 1 < 63) := by
        have hnot : ¬ (vb >>> 1 < 63#64) := of_decide_eq_false hokF
        simpa [BitVec.lt_def, BitVec.toNat_ushiftRight] using hnot
      have hnone : natBinFast? "shiftLeft" va vb = none := by
        simp [natBinFast?, hsc, hny63]
      rw [hnone] at hwp
      have hslowM : LMMono slow := hslowEq ▸ call1_mono fun _ => convW_mono fun _ => pure_mono _
      have hshMono : LMMono (lshr64 aArg (imm64 1) fun x => shl64 x yArg fun z =>
          lshr64 z yArg fun x' => cmpOp .eq 64 x' x fun ok1 =>
          lshr64 z (imm64 63) fun top => cmpOp .eq 64 top (imm64 0) fun ok2 => do
            let boxed ← boxSmall z fun r => pure (j r)
            let sE2 ← slow
            let sE1 ← slow
            pure (.jnz ok1 (.jnz ok2 boxed sE2) sE1)) :=
        lshr64_mono fun _ => shl64_mono fun _ => lshr64_mono fun _ =>
          cmpOp_mono fun _ => lshr64_mono fun _ => cmpOp_mono fun _ =>
            bind_mono (boxSmall_mono fun _ => pure_mono _) fun _ =>
              bind_mono hslowM fun _ => bind_mono hslowM fun _ => pure_mono _
      have hnSh : n2 + 2 ≤ nSh := hshMono (n2 + 2) shE nSh hshE
      exact hslowR _ nS0 sE0 ρ3 J' (by omega) hsE0 hagr30
        (JEnvAgreeBelow.refl _ J') (natBitsSlow_specR0 (by decide) hinv hm hwp)
  · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv hinv' hm' hK

theorem natPrim_sound {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {op : String} {args : List LArg}
    {retTy : LcTy} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {ws : List Word} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hprim : isPhase1NatPrim op args.length retTy = true)
    (hrun : (natPrim rtArg op args k).run n = .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hargsIds : ∀ a ∈ args, argIdsBelow a n) (hargsEv : EvalWordArgs ρ args ws)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hwp : HNatPrimWp rt op ws K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases args with _ | ⟨aArg, _ | ⟨bArg, _ | ⟨_, _⟩⟩⟩
  · simp [isPhase1NatPrim] at hprim
  · rcases ws with _ | ⟨wa, _ | _⟩
    · simp [EvalWordArgs] at hargsEv
    · have haId : argIdsBelow aArg n := hargsIds aArg List.mem_cons_self
      have haW : EvalWordArg ρ aArg wa := hargsEv.2 (aArg, wa) List.mem_cons_self
      rcases isPhase1NatPrim_1_mem hprim with rfl | rfl | rfl
      · exact natPrim_pred_wp hΓ hrun hkMono hrt hnrt haId haW hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          rw [hwa] at hwp
          unfold natPrim at hrun
          have hsp := natBitsSlow_specR0
            (by decide : 19 ∈ [9, 10, 11, 12, 13, 14, 15, 19]) hinv hm hwp
          refine natSlow_rtCall1_wp hΓ hrun hrt hnrt
            (by
              simp only [List.mem_cons, List.not_mem_nil, or_false]
              rintro a (rfl | rfl | rfl)
              · exact argIdsBelow_imm _ _ _
              · exact haId
              · exact argIdsBelow_imm _ _ _)
            (evalRtArgs_cons (evalRtArg_imm64 ρ 19)
              (evalRtArgs_cons (haW.toRtArgBV64 hwa)
                (evalRtArgs_cons (evalRtArg_imm64 ρ 1) (evalRtArgs_nil ρ))))
            hsp ?_
          intro r ek ρ' nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK
          exact hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J)
            hrEv hinv' hm' hK
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          rw [hwa] at hwp
          unfold natPrim at hrun
          refine natReprFast_rtCall1_wp hΓ hrun hrt hnrt haId (haW.toRtArgBV64 hwa)
            hinv hm hX hwp ?_
          intro r ek ρ' nr res σ' m' hnr hek hr hagr hrEv hinv' hm' hK
          exact hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J)
            hrEv hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · rcases ws with _ | ⟨wa, _ | ⟨wb, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have haId : argIdsBelow aArg n := hargsIds aArg List.mem_cons_self
      have hbId : argIdsBelow bArg n := hargsIds bArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have haW : EvalWordArg ρ aArg wa := hargsEv.2 (aArg, wa) List.mem_cons_self
      have hbW : EvalWordArg ρ bArg wb :=
        hargsEv.2 (bArg, wb) (List.mem_cons_of_mem _ List.mem_cons_self)
      rcases isPhase1NatPrim_2_mem hprim with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            exact natPrim_add_wp hΓ hrun hkMono hrt hnrt (haW.toBV64? hwa) haId
              (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            exact natPrim_sub_wp hΓ hrun hkMono hrt hnrt (haW.toBV64? hwa) haId
              (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            exact natPrim_mul_wp hΓ hrun hkMono hrt hnrt (haW.toBV64? hwa) haId
              (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            exact natPrim_div_wp hΓ hrun hkMono hrt hnrt (haW.toBV64? hwa) haId
              (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            exact natPrim_mod_wp hΓ hrun hkMono hrt hnrt (haW.toBV64? hwa) haId
              (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            exact natPrim_shr_wp hΓ hrun hkMono hrt hnrt (haW.toBV64? hwa) haId
              (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some va =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some vb =>
            rw [hwa, hwb] at hwp
            dsimp only at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            refine tagBin_wp (R := R) (K := K) hΓ hrun
              (fun _ _ _ => and64_mono fun _ => pure_mono _) hkMono
              hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId ?_ ?_ ?_
            · intro hsc0
              have hnone : natBinFast? "land" va vb = none := by simp [natBinFast?, hsc0]
              rw [hnone] at hwp
              exact natBitsSlow_specR0 (by decide) hinv hm hwp
            · intro hsc j _ _ _ J' ρ2 _ _ _ hbody _ ha2 hb2 _ _ _ hj
              refine and64_wp hbody ha2 hb2 ?_
              intro rArg ek1 ρ1 hek1 _ _ hrEv
              rw [lm_pure_run] at hek1; injection hek1 with hp
              have hej : j rArg = ek1 := congrArg Prod.fst hp; subst hej
              have hsome : natBinFast? "land" va vb = some (Word.i64 (va &&& vb)) := by
                simp [natBinFast?, hsc]
              rw [hsome] at hwp
              exact hj J' rArg ρ1 mem (va &&& vb) σ
                (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
            · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
              exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv
                hinv' hm' hK
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some va =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some vb =>
            rw [hwa, hwb] at hwp
            dsimp only at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            refine tagBin_wp (R := R) (K := K) hΓ hrun
              (fun _ _ _ => or64_mono fun _ => pure_mono _) hkMono
              hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId ?_ ?_ ?_
            · intro hsc0
              have hnone : natBinFast? "lor" va vb = none := by simp [natBinFast?, hsc0]
              rw [hnone] at hwp
              exact natBitsSlow_specR0 (by decide) hinv hm hwp
            · intro hsc j _ _ _ J' ρ2 _ _ _ hbody _ ha2 hb2 _ _ _ hj
              refine or64_wp hbody ha2 hb2 ?_
              intro rArg ek1 ρ1 hek1 _ _ hrEv
              rw [lm_pure_run] at hek1; injection hek1 with hp
              have hej : j rArg = ek1 := congrArg Prod.fst hp; subst hej
              have hsome : natBinFast? "lor" va vb = some (Word.i64 (va ||| vb)) := by
                simp [natBinFast?, hsc]
              rw [hsome] at hwp
              exact hj J' rArg ρ1 mem (va ||| vb) σ
                (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
            · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
              exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv
                hinv' hm' hK
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some va =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some vb =>
            rw [hwa, hwb] at hwp
            dsimp only at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            refine tagBin_wp (R := R) (K := K) hΓ hrun
              (fun _ _ _ => op1_mono fun _ => or64_mono fun _ => pure_mono _) hkMono
              hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId ?_ ?_ ?_
            · intro hsc0
              have hnone : natBinFast? "xor" va vb = none := by simp [natBinFast?, hsc0]
              rw [hnone] at hwp
              exact natBitsSlow_specR0 (by decide) hinv hm hwp
            · intro hsc j _ n2 _ J' ρ2 _ _ _ hbody _ ha2 hb2 _ _ _ hj
              refine op1_wp hbody (evalArgs_cons ha2 (evalArgs_cons hb2 (evalArgs_nil ρ2))) ?_
              intro ek1 hek1 _
              rw [OpCode.wp_xor]
              simp only [lift2]
              refine or64_wp hek1
                (LArg.eval_vArg_set_self ρ2 { id := n2, name := "", ty := i64 } _)
                (LArg.eval_imm_self _ i64 1#64) ?_
              intro rArg ek2 ρ3 hek2 _ _ hrEv
              rw [lm_pure_run] at hek2; injection hek2 with hp
              have hej : j rArg = ek2 := congrArg Prod.fst hp; subst hej
              have hsome : natBinFast? "xor" va vb = some (Word.i64 ((va ^^^ vb) ||| 1#64)) := by
                simp [natBinFast?, hsc]
              rw [hsome] at hwp
              exact hj J' rArg ρ3 mem ((va ^^^ vb) ||| 1#64) σ
                (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
            · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
              exact hk r ek ρ' J' nr nk 64 vr σ' m' (by omega) hek hr hagr hJagr hrEv
                hinv' hm' hK
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            exact natPrim_shl_wp hΓ hrun hkMono hrt hnrt (haW.toBV64? hwa) haId
              (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · exact natPrim_pow_wp hΓ hrun hrt hnrt haId hbId haW hbW hinv hm hwp hk
      · exact natPrim_gcd_wp hΓ hrun hrt hnrt haId hbId haW hbW hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            exact tagBin_cmp_wp hΓ (by decide) (fun h => by simp [natBinFast?, h]) hrun hkMono
              hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            exact tagBin_cmp_wp hΓ (by decide) (fun h => by simp [natBinFast?, h]) hrun hkMono
              hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            exact tagBin_cmp_wp hΓ (by decide) (fun h => by simp [natBinFast?, h, BitVec.lt_def])
              hrun hkMono hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            exact tagBin_cmp_wp hΓ (by decide) (fun h => by simp [natBinFast?, h, BitVec.lt_def])
              hrun hkMono hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            exact tagBin_cmp_wp hΓ (by decide) (fun h => by simp [natBinFast?, h, BitVec.le_def])
              hrun hkMono hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId hinv hm hwp hk
      · simp only [HNatPrimWp, natBinSlowInfo?] at hwp
        cases hwa : wa.toBV64? with
        | none => rw [hwa] at hwp; exact False.elim hwp
        | some _ =>
          cases hwb : wb.toBV64? with
          | none => rw [hwa, hwb] at hwp; exact False.elim hwp
          | some _ =>
            rw [hwa, hwb] at hwp
            dsimp only [natPrim, natBin, natOpCode] at hrun
            exact tagBin_cmp_wp hΓ (by decide) (fun h => by simp [natBinFast?, h, BitVec.le_def])
              hrun hkMono hrt hnrt (haW.toBV64? hwa) haId (hbW.toBV64? hwb) hbId hinv hm hwp hk
    · simp [EvalWordArgs] at hargsEv
  · simp [isPhase1NatPrim] at hprim

end LeanQbe.T.LeanLCNF.Sem
