module

public import LeanQbe.T.LegalWpBaseLemmas1

/-!
# Legalization semantic preservation BitVec widening & shifts (`T5`, Part 1b)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalWp

/-! ### BitVec widening arithmetic, shift, bit-manipulation, comparison, and conversion lemmas -/

private theorem toNat_setWidth_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (a.setWidth w).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) hnw)

private theorem setWidth_inj_of_le {n w : Nat} (hnw : n ≤ w) {a b : BitVec n}
    (h : a.setWidth w = b.setWidth w) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← toNat_setWidth_of_le hnw a, ← toNat_setWidth_of_le hnw b, h]

private theorem setWidth_setWidth_lowMask {n w : Nat} (hnw : n ≤ w) (x : BitVec w) :
    (x.setWidth n).setWidth w = x &&& lowMask n w :=
  (lowMask_and hnw x).symm

private theorem setWidth_add_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w + b.setWidth w) &&& lowMask n w = (a + b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)

private theorem setWidth_mul_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w * b.setWidth w) &&& lowMask n w = (a * b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_mul,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)

private theorem setWidth_sub_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w - b.setWidth w) &&& lowMask n w = (a - b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_sub,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  have hdvd : 2 ^ n ∣ 2 ^ w := Nat.pow_dvd_pow 2 hnw
  rcases hdvd with ⟨k, hk⟩
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
    rw [hk0, Nat.mul_zero] at hk
    exact Nat.ne_of_gt (Nat.two_pow_pos w) hk
  have ha : a.toNat < 2 ^ n := a.isLt
  have hb : b.toNat < 2 ^ n := b.isLt
  have hk1 : 2 ^ n * k = 2 ^ n * (k - 1) + 2 ^ n := by
    calc 2 ^ n * k = 2 ^ n * (k - 1 + 1) := by rw [Nat.sub_add_cancel hkpos]
      _ = 2 ^ n * (k - 1) + 2 ^ n := Nat.mul_add_one _ _
  have h1 : 2 ^ w - b.toNat + a.toNat = (k - 1) * 2 ^ n + (2 ^ n - b.toNat + a.toNat) := by
    rw [hk, hk1, Nat.mul_comm (2 ^ n) (k - 1)]
    omega
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw), h1, Nat.mul_comm (k - 1), Nat.mul_add_mod]

private theorem setWidth_neg_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (-(a.setWidth w)) &&& lowMask n w = (-a).setWidth w := by
  have hz : (0#n).setWidth w = 0#w := BitVec.setWidth_zero w n
  have hsub := setWidth_sub_of_le hnw 0#n a
  rw [hz] at hsub
  simpa using hsub

private theorem setWidth_and_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w &&& b.setWidth w = (a &&& b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_or_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w ||| b.setWidth w = (a ||| b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_xor_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w ^^^ b.setWidth w = (a ^^^ b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_not_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (~~~(a.setWidth w)) &&& lowMask n w = (~~~a).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_of_lt_of_le hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_not, hi, hiw,
    decide_true, Bool.true_and]

private theorem setWidth_shl_of_lt {n w : Nat} (hnw : n < w) (a : BitVec n) (s : Nat) :
    ((a.setWidth w) <<< s) &&& lowMask n w = (a <<< s).setWidth w := by
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    hi, hiw, decide_true, Bool.true_and]
  have hlt : decide (i - s < w) = true := decide_eq_true (by omega)
  simp only [hlt, Bool.true_and]

private theorem setWidth_lshr_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) (s : Nat) :
    (a.setWidth w) >>> s = (a >>> s).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi]
  by_cases his : s + i < n
  · have hisw : s + i < w := Nat.lt_of_lt_of_le his hnw
    simp [his, hisw]
  · have hfalse : a.getLsbD (s + i) = false := BitVec.getLsbD_of_ge a (s + i) (by omega)
    simp [hfalse]

private theorem msb_signExtend_of_pos_le {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (a : BitVec n) :
    (a.signExtend w).msb = a.msb := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
  have hw0 : w - 1 < w := by omega
  have hnot : ¬ (w - 1 < n) ∨ n = w := by omega
  rcases hnot with hge | rfl
  · simp [hw0, hge, BitVec.msb_eq_getLsbD_last]
  · simp [hw0]

private theorem setWidth_ashr_signExtend_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a : BitVec n) (s : Nat) :
    ((a.signExtend w).sshiftRight s) &&& lowMask n w = (a.sshiftRight s).setWidth w := by
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and]
  rw [msb_signExtend_of_pos_le hn0 (Nat.le_of_lt hnw) a]
  have hnw1 : decide (w ≤ i) = false := decide_eq_false (by omega)
  have hnw2 : decide (n ≤ i) = false := decide_eq_false (by omega)
  by_cases hsn : s + i < n
  · have hsw : s + i < w := Nat.lt_trans hsn hnw
    simp [hnw1, hnw2, hsn, hsw]
  · by_cases hsw : s + i < w <;> simp [hnw1, hnw2, hsn, hsw]

private theorem setWidth_rotl_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a b : BitVec n) :
    let s := b.toNat % n
    (((a.setWidth w) <<< s) ||| ((a.setWidth w) >>> (n - s))) &&& lowMask n w =
      (a.rotateLeft (b.toNat % n)).setWidth w := by
  intro s
  have hsn : s < n := Nat.mod_lt _ hn0
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft,
    hi, hiw, decide_true, Bool.true_and]
  by_cases his : i < s
  · have h2 : n - s + i < n := by omega
    have h3 : n - s + i < w := Nat.lt_trans h2 hnw
    dsimp only [s] at his h3 ⊢
    simp [his, h3]
  · have hisn : i - s < n := by omega
    have hisw : i - s < w := Nat.lt_trans hisn hnw
    have hge : n ≤ n - s + i := by omega
    have hfalse : a.getLsbD (n - s + i) = false := BitVec.getLsbD_of_ge a (n - s + i) hge
    dsimp only [s] at his hisw hfalse ⊢
    simp [his, hisw, hfalse]

private theorem setWidth_rotr_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a b : BitVec n) :
    let s := b.toNat % n
    (((a.setWidth w) >>> s) ||| ((a.setWidth w) <<< (n - s))) &&& lowMask n w =
      (a.rotateRight (b.toNat % n)).setWidth w := by
  intro s
  have hsn : s < n := Nat.mod_lt _ hn0
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateRight,
    hi, hiw, decide_true, Bool.true_and]
  by_cases hsi : s + i < n
  · have hlt : i < n - s := by omega
    have hsw : s + i < w := Nat.lt_trans hsi hnw
    dsimp only [s] at hlt hsw ⊢
    simp [hlt, hsw]
  · have hns : ¬ (i < n - s) := by omega
    have hge : n ≤ s + i := by omega
    have hfalse : a.getLsbD (s + i) = false := BitVec.getLsbD_of_ge a (s + i) hge
    have hsub : i - (n - s) < n := by omega
    have hsubw : i - (n - s) < w := Nat.lt_trans hsub hnw
    dsimp only [s] at hns hfalse hsubw ⊢
    simp [hns, hfalse, hsubw]

private theorem countMod_toNat_mod {n w : Nat} (hn0 : 0 < n) (hnw : n < w) (b : BitVec n) :
    (BitVec.ofNat w (b.toNat % n)).toNat % w = b.toNat % n := by
  have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
  have hb : b.toNat % n < n := Nat.mod_lt _ hn0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hb (Nat.lt_trans hnw hpow)),
    Nat.mod_eq_of_lt (Nat.lt_trans hb hnw)]

private theorem ofNat_sub_toNat_mod {n w s : Nat} (hnw : n < w) (hs : s < n) :
    (BitVec.ofNat w n - BitVec.ofNat w s).toNat % w = n - s := by
  have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
  have h1 : (BitVec.ofNat w n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat w s).toNat = s := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdiff : (BitVec.ofNat w n - BitVec.ofNat w s).toNat = n - s := by
    rw [BitVec.toNat_sub, h1, h2]
    have hsplit : 2 ^ w - s + n = 2 ^ w + (n - s) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hdiff, Nat.mod_eq_of_lt (by omega)]

theorem legalBitsArith_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} {n : Nat} (hn : target.supportsTy (.bits n) = true)
    (c : OpCode [.bits n, .bits n] [.bits n])
    (hc : match c with
      | .add _ | .sub _ | .mul _ | .and _ | .or _ | .xor _
      | .shl _ | .lshr _ | .ashr _ | .rotl _ | .rotr _ => True
      | _ => False)
    (a' b' : Arg Val (.bits (target.widenWidth n))) (a b : BitVec n)
    (ha : a'.val = a.setWidth (target.widenWidth n))
    (hb : b'.val = b.setWidth (target.widenWidth n))
    {k : Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs} {m : Mem 64}
    (hk : Op.wp ⟨c, ((Arg.imm a : Arg Val (.bits n)), Arg.imm b, ())⟩
      (fun (res, ()) => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m)) :
    wp Γ Q X (legalBitsArith target n c a' b' k) m := by
  have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports hn
  dsimp only [legalBitsArith]
  by_cases hn0 : n = 0
  · subst hn0
    have ha0 : a = 0#0 := bitVec0_eq_zero a
    have hb0 : b = 0#0 := bitVec0_eq_zero b
    subst ha0; subst hb0
    simp only [beq_self_eq_true, ↓reduceIte]
    have h0 : ∀ v : BitVec 0, v.setWidth (target.widenWidth 0) = 0#(target.widenWidth 0) :=
      fun v => by rw [bitVec0_eq_zero v, BitVec.setWidth_zero _ 0]
    cases c <;> try exact hc.elim
    all_goals
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      exact hk (.imm 0#(target.widenWidth 0)) (by simp [h0])
  · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn0f : (n == 0) = false := beq_false_of_ne hn0
    simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
    cases c with
    | add _ =>
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val + b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_add_of_le hnw]
    | sub _ =>
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val - b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_sub_of_le hnw]
    | mul _ =>
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val * b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_mul_of_le hnw]
    | and _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val &&& b'.val = _; rw [ha, hb, setWidth_and_of_le])
    | or _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val ||| b'.val = _; rw [ha, hb, setWidth_or_of_le])
    | xor _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val ^^^ b'.val = _; rw [ha, hb, setWidth_xor_of_le])
    | shl _ =>
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val <<< (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change (a'.val <<< (cm.val.toNat % target.widenWidth n)) &&&
          lowMask n (target.widenWidth n) = _
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b]
        exact setWidth_shl_of_lt hlt a (b.toNat % n)
    | lshr _ =>
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val >>> (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        exact hk _ (by
          change a'.val >>> (cm.val.toNat % target.widenWidth n) = _
          rw [ha, hcm, countMod_toNat_mod hn0pos hlt b, setWidth_lshr_of_le hnw])
    | ashr _ =>
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.sshiftRight (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm =>
          emitSextToW_wp hn0pos hnw ha fun sa hsa => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change (sa.val.sshiftRight (cm.val.toNat % target.widenWidth n)) &&&
          lowMask n (target.widenWidth n) = _
        rw [hsa, hcm, countMod_toNat_mod hn0pos hlt b]
        exact setWidth_ashr_signExtend_of_lt hn0pos hlt a (b.toNat % n)
    | rotl _ =>
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.rotateLeft (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Arg.val_imm]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change ((a'.val <<< (cm.val.toNat % target.widenWidth n)) |||
          (a'.val >>>
            ((BitVec.ofNat (target.widenWidth n) n - cm.val).toNat % target.widenWidth n))) &&&
          lowMask n (target.widenWidth n) = (a.rotateLeft (b.toNat % n)).setWidth
            (target.widenWidth n)
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b,
          ofNat_sub_toNat_mod hlt (Nat.mod_lt _ hn0pos)]
        exact setWidth_rotl_of_lt hn0pos hlt a b
    | rotr _ =>
      dsimp only
        [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm,
          lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.rotateRight (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Arg.val_imm]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change ((a'.val >>> (cm.val.toNat % target.widenWidth n)) |||
          (a'.val <<<
            ((BitVec.ofNat (target.widenWidth n) n - cm.val).toNat % target.widenWidth n))) &&&
          lowMask n (target.widenWidth n) = (a.rotateRight (b.toNat % n)).setWidth
            (target.widenWidth n)
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b,
          ofNat_sub_toNat_mod hlt (Nat.mod_lt _ hn0pos)]
        exact setWidth_rotr_of_lt hn0pos hlt a b
    | _ => exact hc.elim

/-! ### Signed/unsigned compare widening and byte swap lemmas -/

theorem signExtend_eq_setWidth_of_msb_false {n w : Nat} (_hnw : n ≤ w)
    {a : BitVec n} (hm : a.msb = false) :
    a.signExtend w = a.setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · have hfa : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
    simp [hin, hm, hfa]

private theorem not_signExtend_of_pos_le {n w : Nat} (_hn0 : 0 < n) (_hnw : n ≤ w)
    {a : BitVec n} (hm : a.msb = true) :
    ~~~(a.signExtend w) = (~~~a).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_not, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · simp [hin, hm]

private theorem toNat_not_add {w : Nat} (x : BitVec w) :
    x.toNat + (~~~x).toNat = 2 ^ w - 1 := by
  have h : x + ~~~x = BitVec.allOnes w := BitVec.add_not_self x
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_allOnes] at hn
  have h1 : x.toNat < 2 ^ w := x.isLt
  have h2 : (~~~x).toNat < 2 ^ w := (~~~x).isLt
  by_cases hlt : x.toNat + (~~~x).toNat < 2 ^ w
  · rw [Nat.mod_eq_of_lt hlt] at hn
    exact hn
  · have hm : (x.toNat + (~~~x).toNat) % 2 ^ w = x.toNat + (~~~x).toNat - 2 ^ w := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm] at hn
    omega

private theorem two_mul_toNat_lt_iff_msb_false {n : Nat} (hn0 : 0 < n) (a : BitVec n) :
    2 * a.toNat < 2 ^ n ↔ a.msb = false := by
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc 2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn0]
      _ = 2 ^ (n - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  rw [BitVec.msb_eq_decide, h2n]
  constructor
  · intro h; simp only [decide_eq_false_iff_not]; omega
  · intro h; simp only [decide_eq_false_iff_not] at h; omega

private theorem toInt_signExtend_of_pos_le {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (a : BitVec n) :
    (a.signExtend w).toInt = a.toInt := by
  have hw0 : 0 < w := Nat.lt_of_lt_of_le hn0 hnw
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  by_cases hm : a.msb = true
  · have hms : (a.signExtend w).msb = true := by rwa [msb_signExtend_of_pos_le hn0 hnw]
    have hna : ¬ (2 * a.toNat < 2 ^ n) := by
      rw [two_mul_toNat_lt_iff_msb_false hn0, hm]; decide
    have hns : ¬ (2 * (a.signExtend w).toNat < 2 ^ w) := by
      rw [two_mul_toNat_lt_iff_msb_false hw0, hms]; decide
    simp only [hna, hns, ↓reduceIte]
    have hnot := not_signExtend_of_pos_le hn0 hnw hm
    have h1 := toNat_not_add (a.signExtend w)
    have h2 := toNat_not_add a
    rw [hnot, toNat_setWidth_of_le hnw] at h1
    omega
  · have hmf : a.msb = false := Bool.eq_false_iff.mpr hm
    have hms : (a.signExtend w).msb = false := by rwa [msb_signExtend_of_pos_le hn0 hnw]
    have hna : 2 * a.toNat < 2 ^ n := (two_mul_toNat_lt_iff_msb_false hn0 a).2 hmf
    have hns : 2 * (a.signExtend w).toNat < 2 ^ w :=
      (two_mul_toNat_lt_iff_msb_false hw0 (a.signExtend w)).2 hms
    simp only [hna, hns, ↓reduceIte]
    rw [signExtend_eq_setWidth_of_msb_false hnw hmf, toNat_setWidth_of_le hnw]

theorem evalBits_setWidth_unsigned {n w : Nat} (hnw : n ≤ w) (o : CmpOp)
    (ho : match o with | .slt | .sle | .sgt | .sge => False | _ => True)
    (a b : BitVec n) :
    o.evalBits (a.setWidth w) (b.setWidth w) = o.evalBits a b := by
  cases o with
  | eq => simp only [CmpOp.evalBits]; exact decide_eq_decide.2 ⟨setWidth_inj_of_le hnw, congrArg _⟩
  | ne =>
    simp only [CmpOp.evalBits]
    exact decide_eq_decide.2 (not_congr ⟨setWidth_inj_of_le hnw, congrArg _⟩)
  | ult | ule | ugt | uge =>
    simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, toNat_setWidth_of_le hnw]
  | _ => exact ho.elim

theorem evalBits_signExtend_signed {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (o : CmpOp)
    (ho : match o with | .slt | .sle | .sgt | .sge => True | _ => False) (a b : BitVec n) :
    o.evalBits (a.signExtend w) (b.signExtend w) = o.evalBits a b := by
  cases o with
  | slt | sgt => simp only [CmpOp.evalBits, BitVec.slt, toInt_signExtend_of_pos_le hn0 hnw]
  | sle | sge => simp only [CmpOp.evalBits, BitVec.sle, toInt_signExtend_of_pos_le hn0 hnw]
  | _ => exact ho.elim

private theorem getLsbD_bswapBits_go {w : Nat} :
    ∀ (m : Nat) (x : BitVec w) {i : Nat}, i < 8 * m →
      (bswapBits.go x m).getLsbD i = x.getLsbD (8 * (m - 1 - i / 8) + i % 8)
  | 0, _, _, hi => by omega
  | m + 1, x, i, hi => by
    dsimp only [bswapBits.go]
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hi8 : i < 8
    · have hq : i / 8 = 0 := Nat.div_eq_of_lt hi8
      have hr : i % 8 = i := Nat.mod_eq_of_lt hi8
      simp only [hi8, ↓reduceIte, hq, hr, Nat.sub_zero, Nat.add_sub_cancel]
      rw [BitVec.getLsbD_extractLsb']
      simp [hi8]
    · have hi8' : ¬ (i < 8) := hi8
      have him : i - 8 < 8 * m := by omega
      have ih := getLsbD_bswapBits_go m x him
      have hq : i / 8 = (i - 8) / 8 + 1 := by omega
      have hr : i % 8 = (i - 8) % 8 := by omega
      have hsub : m + 1 - 1 - i / 8 = m - 1 - (i - 8) / 8 := by omega
      simp only [hi8', ↓reduceIte, ih, hsub, ← hr]

theorem bswapBits_8 (x : BitVec 8) : bswapBits x = x := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, bswapBits, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_bswapBits_go 1 x hi]
  have hq : i / 8 = 0 := Nat.div_eq_of_lt hi
  have hr : i % 8 = i := Nat.mod_eq_of_lt hi
  simp [hq, hr]

theorem setWidth_bswap_of_lt {n w : Nat} (_hn0 : 0 < n) (hnw : n < w)
    (hn8 : n % 8 = 0) (hw8 : w % 8 = 0) (a : BitVec n) :
    (bswapBits (a.setWidth w)) >>> (w - n) = (bswapBits a).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    bswapBits, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · have hni : w - n + i < w := by omega
    have hnw8 : w - n + i < 8 * (w / 8) := by omega
    have hin8 : i < 8 * (n / 8) := by omega
    rw [decide_eq_true hni, decide_eq_true hin, Bool.true_and, Bool.true_and,
      getLsbD_bswapBits_go (w / 8) (a.setWidth w) hnw8,
      getLsbD_bswapBits_go (n / 8) a hin8]
    have hidx_eq : 8 * (w / 8 - 1 - (w - n + i) / 8) + (w - n + i) % 8 =
        8 * (n / 8 - 1 - i / 8) + i % 8 := by omega
    have hlt_w : 8 * (n / 8 - 1 - i / 8) + i % 8 < w := by omega
    rw [hidx_eq, BitVec.getLsbD_setWidth, decide_eq_true hlt_w, Bool.true_and]
  · have hge : ¬ (w - n + i < w) := by omega
    simp [decide_eq_false hge, decide_eq_false hin]

end LegalWp

end LeanQbe.T
