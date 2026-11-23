module

public import LeanQbe.T.LegalWpSimdLemmas1

/-!
# Legalization 128-bit SIMD/SHA-256 lowering `_wp` lemmas (Part 2b)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

section LegalWp

private theorem scalarShufb128_muxBytes_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (idx : Arg Val i8) :
    ∀ (bs : List (Arg Val i8)) (j : Nat)
      {k : Arg Val i8 → Expr Val Cont rs} {m : Mem 64},
      (∀ r : Arg Val i8,
        (bs ≠ [] → j ≤ idx.val.toNat → idx.val.toNat < j + bs.length →
          r.val = (bs.getD (idx.val.toNat - j) (.imm 0#8)).val) →
        wp Γ Q X (k r) m) →
      wp Γ Q X (scalarShufb128.muxBytes idx bs j k) m
  | [], j, k, m, hk => by
    dsimp only [scalarShufb128.muxBytes]
    exact hk (.imm 0#8) (fun hne _ _ => absurd rfl hne)
  | [b], j, k, m, hk => by
    dsimp only [scalarShufb128.muxBytes]
    apply hk b
    intro _ hle hlt
    simp only [List.length_singleton] at hlt
    have hsub : idx.val.toNat - j = 0 := by omega
    simp [hsub]
  | b :: b' :: bs, j, k, m, hk => by
    dsimp only [scalarShufb128.muxBytes]
    apply scalarShufb128_muxBytes_wp idx (b' :: bs) (j + 1)
    intro rest hRest
    dsimp only [wp, Op.wp, op2, op3, vals]
    rw [OpCode.wp_cmp]
    dsimp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, Arg.val_imm,
      eq_mp_eq_cast, cast_eq]
    rw [OpCode.wp_select]
    dsimp only [Arg.val_var]
    apply hk (.var _)
    intro _ hle hlt
    by_cases hjEq : idx.val.toNat = j
    · have hj256 : j < 256 := by omega
      have hbEq : idx.val = BitVec.ofNat 8 j := by
        apply BitVec.eq_of_toNat_eq
        simp [hjEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj256]
      have hsub : idx.val.toNat - j = 0 := by omega
      rw [hsub, hbEq]
      simp
    · have hgt : j + 1 ≤ idx.val.toNat := by omega
      have hne : idx.val ≠ BitVec.ofNat 8 j := by
        intro hEq
        apply hjEq
        have := congrArg BitVec.toNat hEq
        simp only [BitVec.toNat_ofNat] at this
        have hlt256 : j < 256 := by omega
        omega
      have hRestEq :=
        hRest (List.cons_ne_nil _ _) hgt (by simp only [List.length_cons] at hlt ⊢; omega)
      have hsub : idx.val.toNat - j = (idx.val.toNat - (j + 1)) + 1 := by omega
      simp [hne, hRestEq, hsub]

private theorem scalarShufb128_doBytes_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {abs mbs : List (Arg Val i8)} {a m128 : BitVec 128}
    (hAbsLen : abs.length = 16)
    (hAbs : ∀ p, p < 16 → (abs.getD p (.imm 0#8)).val = bvLane 8 p a)
    (hMbs : ∀ p, p < 16 → (mbs.getD p (.imm 0#8)).val = bvLane 8 p m128) :
    ∀ (k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs)
      (i : Nat) (acc : List (Arg Val i8)) (mem : Mem 64),
      acc.length = i →
      (∀ q, q < i → (acc.getD q (.imm 0#8)).val = bvLane 8 q (shuffleBytes a m128)) →
      (∀ r0 r1 r2 r3 : Arg Val i32,
        r0.val = bvLane 32 0 (shuffleBytes a m128) →
        r1.val = bvLane 32 1 (shuffleBytes a m128) →
        r2.val = bvLane 32 2 (shuffleBytes a m128) →
        r3.val = bvLane 32 3 (shuffleBytes a m128) →
        wp Γ Q X (k r0 r1 r2 r3) mem) →
      wp Γ Q X (scalarShufb128.doBytes k abs mbs i acc) mem := by
  intro k i
  suffices h : ∀ (n : Nat) (i : Nat), n = 16 - i →
      ∀ (acc : List (Arg Val i8)) (mem : Mem 64),
        acc.length = i →
        (∀ q, q < i → (acc.getD q (.imm 0#8)).val = bvLane 8 q (shuffleBytes a m128)) →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (shuffleBytes a m128) →
          r1.val = bvLane 32 1 (shuffleBytes a m128) →
          r2.val = bvLane 32 2 (shuffleBytes a m128) →
          r3.val = bvLane 32 3 (shuffleBytes a m128) →
          wp Γ Q X (k r0 r1 r2 r3) mem) →
        wp Γ Q X (scalarShufb128.doBytes k abs mbs i acc) mem by
    exact h (16 - i) i rfl
  intro n
  induction n with
  | zero =>
    intro i hi acc mem hLen hAcc hk
    rw [scalarShufb128.doBytes.eq_def]
    have hi16 : i ≥ 16 := by omega
    simp only [hi16, ↓reduceIte]
    apply bytes16ToDwords4_wp (fun p hp => hAcc p (by omega)) hk
  | succ n ih =>
    intro i hi acc mem hLen hAcc hk
    rw [scalarShufb128.doBytes.eq_def]
    have hiLt : i < 16 := by omega
    simp only [show ¬(i ≥ 16) by omega, ↓reduceIte]
    dsimp only [wp, Op.wp, op2, vals]
    rw [OpCode.wp_cmp]
    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, Arg.val_imm,
      cast_eq]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    apply scalarShufb128_muxBytes_wp (.var _) abs 0
    intro sel hSel
    dsimp only [wp, Op.wp, op3, vals]
    rw [OpCode.wp_select]
    dsimp only [Arg.val_var, Arg.val_imm]
    apply ih (i + 1) (by omega) _ mem (by simp [hLen])
    · intro q hq
      have hLaneEq : bvLane 8 i (shuffleBytes a m128) =
          let index := bvLane 8 i m128
          if index.msb then 0#8 else bvLane 8 (index.toNat % 16) a := by
        unfold shuffleBytes
        apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
        rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
        have hdiv : (8 * i + bit) / 8 = i := by omega
        have hmod : (8 * i + bit) % 8 = bit := by omega
        have hlt16 : i < 128 / 8 := by omega
        have hzero : i / 16 = 0 := by omega
        simp [hbit8, hdiv, hmod, hlt16, hzero]
      by_cases hqi : q < i
      · rw [list_getD_append_left acc [.var _] (.imm 0#8) (by omega)]
        exact hAcc q hqi
      · have hqEq : q = i := by omega
        subst hqEq
        rw [hLaneEq]
        have hGet : ∀ (v : Val i8) (d : Arg Val i8),
            ((acc ++ [Arg.var v]).getD q d).val = v := by
          intro v d
          rw [← hLen, list_getD_append_right_eq]; rfl
        rw [hGet]
        have hMb := hMbs q hiLt
        have hSlt : ((mbs.getD q (.imm 0#8)).val.slt 0#8) = (bvLane 8 q m128).msb := by
          rw [hMb]; exact BitVec.slt_zero_eq_msb
        rw [hSlt]
        by_cases hMsb : (bvLane 8 q m128).msb = true
        · simp [hMsb]
        · simp only [hMsb, Bool.false_eq_true, ↓reduceIte]
          have hIdxMod :
            ((mbs.getD q (.imm 0#8)).val &&& 15#8).toNat = (bvLane 8 q m128).toNat % 16 := by
            rw [hMb]
            have h1 : ((bvLane 8 q m128) &&& 15#8).toNat = (bvLane 8 q m128).toNat &&& 15 := by simp
            rw [h1, show (15 : Nat) = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
          have hIdxLt : ((mbs.getD q (.imm 0#8)).val &&& 15#8).toNat < 16 := by
            rw [hIdxMod]; exact Nat.mod_lt _ (by omega)
          have hAbsNe : abs ≠ [] := by intro h; simp [h] at hAbsLen
          have hSelEq := hSel hAbsNe (by omega) (by rw [hAbsLen]; exact hIdxLt)
          dsimp only [Arg.val_var] at hSelEq
          rw [Nat.sub_zero, hIdxMod] at hSelEq
          have hRes := hAbs ((bvLane 8 q m128).toNat % 16) (Nat.mod_lt _ (by omega))
          exact hSelEq.trans hRes
    · exact hk

private theorem scalarShufb128_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a0 a1 a2 a3 m0 m1 m2 m3 : Arg Val i32} {a m128 : BitVec 128}
    (ha0 : a0.val = bvLane 32 0 a) (ha1 : a1.val = bvLane 32 1 a)
    (ha2 : a2.val = bvLane 32 2 a) (ha3 : a3.val = bvLane 32 3 a)
    (hm0 : m0.val = bvLane 32 0 m128) (hm1 : m1.val = bvLane 32 1 m128)
    (hm2 : m2.val = bvLane 32 2 m128) (hm3 : m3.val = bvLane 32 3 m128)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {mem : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (shuffleBytes a m128) →
      r1.val = bvLane 32 1 (shuffleBytes a m128) →
      r2.val = bvLane 32 2 (shuffleBytes a m128) →
      r3.val = bvLane 32 3 (shuffleBytes a m128) →
      wp Γ Q X (k r0 r1 r2 r3) mem) :
    wp Γ Q X (scalarShufb128 a0 a1 a2 a3 m0 m1 m2 m3 k) mem := by
  unfold scalarShufb128
  apply dwords4ToBytes16_wp ha0 ha1 ha2 ha3; intro abs hAbsLen hAbs
  apply dwords4ToBytes16_wp hm0 hm1 hm2 hm3; intro mbs _ hMbs
  exact scalarShufb128_doBytes_wp hAbsLen hAbs hMbs k 0 [] mem rfl (fun _ h => absurd h (by omega))
    hk

private theorem emitRotr32_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (x : Arg Val i32) (n : Nat) (hn : n < 32)
    {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = x.val.rotateRight n → wp Γ Q X (k r) m) :
    wp Γ Q X (emitRotr32 x n k) m := by
  unfold emitRotr32
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_rotr]
  dsimp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
  have hmod : (BitVec.ofNat 32 n).toNat % 32 = n := by
    rw [BitVec.toNat_ofNat]; simp [Nat.mod_eq_of_lt hn]
  rw [hmod]
  exact hk (.var _) rfl

private theorem emitLshr32_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (x : Arg Val i32) (n : Nat) (hn : n < 32)
    {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = x.val >>> n → wp Γ Q X (k r) m) :
    wp Γ Q X (emitLshr32 x n k) m := by
  unfold emitLshr32
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_lshr]
  dsimp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
  have hmod : (BitVec.ofNat 32 n).toNat % 32 = n := by
    rw [BitVec.toNat_ofNat]; simp [Nat.mod_eq_of_lt hn]
  rw [hmod]
  exact hk (.var _) rfl

private theorem emitShaSig0_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (x : Arg Val i32) {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = Sha256.σ₀ x.val → wp Γ Q X (k r) m) :
    wp Γ Q X (emitShaSig0 x k) m := by
  simp only [emitShaSig0, emitShaMix3, ↓reduceIte, emitXor32]
  apply emitRotr32_wp x 7 (by omega); intro r7 hr7
  apply emitRotr32_wp x 18 (by omega); intro r18 hr18
  apply emitLshr32_wp x 3 (by omega); intro s3 hs3
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_xor]; dsimp only [lift2]
  rw [OpCode.wp_xor]; dsimp only [lift2, Arg.val_var]
  exact hk (.var _) (by simp [Sha256.σ₀, hr7, hr18, hs3])

private theorem emitShaSig1_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (x : Arg Val i32) {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = Sha256.σ₁ x.val → wp Γ Q X (k r) m) :
    wp Γ Q X (emitShaSig1 x k) m := by
  simp only [emitShaSig1, emitShaMix3, ↓reduceIte, emitXor32]
  apply emitRotr32_wp x 17 (by omega); intro r17 hr17
  apply emitRotr32_wp x 19 (by omega); intro r19 hr19
  apply emitLshr32_wp x 10 (by omega); intro s10 hs10
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_xor]; dsimp only [lift2]
  rw [OpCode.wp_xor]; dsimp only [lift2, Arg.val_var]
  exact hk (.var _) (by simp [Sha256.σ₁, hr17, hr19, hs10])

private theorem emitShaRound_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (a b c d e f g h wk : Arg Val i32)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
         Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs}
    {m : Mem 64}
    (hk : ∀ a' b' c' d' e' f' g' h' : Arg Val i32,
      a'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).a ∧
      b'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).b ∧
      c'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).c ∧
      d'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).d ∧
      e'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).e ∧
      f'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).f ∧
      g'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).g ∧
      h'.val = (Sha256.State.round { a := a.val, b := b.val, c := c.val, d := d.val,
                                     e := e.val, f := f.val, g := g.val, h := h.val } wk.val).h →
      wp Γ Q X (k a' b' c' d' e' f' g' h') m) :
    wp Γ Q X (emitShaRound a b c d e f g h wk k) m := by
  simp only [emitShaRound, emitShaCh, emitShaMaj, emitShaSigma0, emitShaSigma1, emitShaMix3,
    Bool.false_eq_true, ↓reduceIte, emitAnd32, emitNot32, emitXor32, emitAdd32]
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_and, OpCode.wp_not, OpCode.wp_and, OpCode.wp_xor];
    dsimp only [lift1, lift2, Arg.val_var]
  apply emitRotr32_wp e 6 (by omega); intro r6 hr6
  apply emitRotr32_wp e 11 (by omega); intro r11 hr11
  apply emitRotr32_wp e 25 (by omega); intro r25 hr25
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_xor, OpCode.wp_xor]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_add, OpCode.wp_add, OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_and, OpCode.wp_and, OpCode.wp_and, OpCode.wp_xor, OpCode.wp_xor]
  dsimp only [lift2, Arg.val_var]
  apply emitRotr32_wp a 2 (by omega); intro r2 hr2
  apply emitRotr32_wp a 13 (by omega); intro r13 hr13
  apply emitRotr32_wp a 22 (by omega); intro r22 hr22
  dsimp only [wp, Op.wp, op2, vals]
  rw [OpCode.wp_xor, OpCode.wp_xor]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_add, OpCode.wp_add, OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply hk
  simp [Sha256.State.round, Sha256.ch, Sha256.maj, Sha256.«Σ₀», Sha256.«Σ₁»,
    hr6, hr11, hr25, hr2, hr13, hr22]

theorem scalarSha256rnds2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 : Arg Val i32}
    {cdgh abef wk : BitVec 128}
    (hcd0 : cd0.val = bvLane 32 0 cdgh) (hcd1 : cd1.val = bvLane 32 1 cdgh)
    (hcd2 : cd2.val = bvLane 32 2 cdgh) (hcd3 : cd3.val = bvLane 32 3 cdgh)
    (hab0 : ab0.val = bvLane 32 0 abef) (hab1 : ab1.val = bvLane 32 1 abef)
    (hab2 : ab2.val = bvLane 32 2 abef) (hab3 : ab3.val = bvLane 32 3 abef)
    (hwk0 : wk0.val = bvLane 32 0 wk) (hwk1 : wk1.val = bvLane 32 1 wk)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (Sha256.rounds2 cdgh abef wk) →
      r1.val = bvLane 32 1 (Sha256.rounds2 cdgh abef wk) →
      r2.val = bvLane 32 2 (Sha256.rounds2 cdgh abef wk) →
      r3.val = bvLane 32 3 (Sha256.rounds2 cdgh abef wk) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 k) m := by
  unfold scalarSha256rnds2
  apply emitShaRound_wp; intro a1 b1 c1 d1 e1 f1 g1 h1 hSt1
  apply emitShaRound_wp; intro a2 b2 c2 d2 e2 f2 g2 h2 hSt2
  rcases hSt1 with ⟨ha1, hb1, hc1, hd1, he1, hf1, hg1, hh1⟩
  rcases hSt2 with ⟨ha2, _, _, _, he2, _, _, _⟩
  have hL : ∀ (idx : Nat), idx < 4 →
      bvLane 32 idx (Sha256.rounds2 cdgh abef wk) =
        let s : Sha256.State := { a := ab3.val, b := ab2.val, c := cd3.val, d := cd2.val,
                                  e := ab1.val, f := ab0.val, g := cd1.val, h := cd0.val }
        let s1 := s.round wk0.val
        let s2 := s1.round wk1.val
        if idx = 0 then s1.e else if idx = 1 then s2.e else if idx = 2 then s1.a else s2.a := by
    intro idx hIdx
    unfold Sha256.rounds2
    dsimp only
    rw [hab0, hab1, hab2, hab3, hcd0, hcd1, hcd2, hcd3, hwk0, hwk1]
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit32
    rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hdiv : (32 * idx + bit) / 32 = idx := by omega
    have hmod : (32 * idx + bit) % 32 = bit := by omega
    have hlt4 : idx < 128 / 32 := by omega
    simp only [hbit32, decide_true, Bool.true_and, hdiv, hmod, hlt4, ↓reduceIte]
    rcases idx with _ | _ | _ | _ | _ <;> first | omega | rfl
  apply hk e1 e2 a1 a2
  · rw [he1, hL 0 (by omega)]; rfl
  · rw [he2, hL 1 (by omega), ha1, hb1, hc1, hd1, he1, hf1, hg1, hh1]; rfl
  · rw [ha1, hL 2 (by omega)]; rfl
  · rw [ha2, hL 3 (by omega), ha1, hb1, hc1, hd1, he1, hf1, hg1, hh1]; rfl

theorem scalarSha256msg1_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {w0123 w4 : BitVec 128}
    (ha0 : a0.val = bvLane 32 0 w0123) (ha1 : a1.val = bvLane 32 1 w0123)
    (ha2 : a2.val = bvLane 32 2 w0123) (ha3 : a3.val = bvLane 32 3 w0123)
    (hb0 : b0.val = bvLane 32 0 w4)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (Sha256.msg1 w0123 w4) →
      r1.val = bvLane 32 1 (Sha256.msg1 w0123 w4) →
      r2.val = bvLane 32 2 (Sha256.msg1 w0123 w4) →
      r3.val = bvLane 32 3 (Sha256.msg1 w0123 w4) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold scalarSha256msg1 emitAdd32
  apply emitShaSig0_wp a1; intro s0 hs0
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig0_wp a2; intro s1 hs1
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig0_wp a3; intro s2 hs2
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig0_wp b0; intro s3 hs3
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  have hL : ∀ (idx : Nat) (hIdx : idx < 4),
      bvLane 32 idx (Sha256.msg1 w0123 w4) =
        bvLane 32 idx w0123 + Sha256.σ₀
          (if idx < 3 then bvLane 32 (idx + 1) w0123 else bvLane 32 0 w4) := by
    intro idx hIdx
    unfold Sha256.msg1
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit32
    rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hdiv : (32 * idx + bit) / 32 = idx := by omega
    have hmod : (32 * idx + bit) % 32 = bit := by omega
    have hlt4 : idx < 128 / 32 := by omega
    simp [hbit32, hdiv, hmod, hlt4]
  apply hk
  · dsimp only [Arg.val_var]; rw [hs0, ha0, ha1, hL 0 (by omega)]; simp
  · dsimp only [Arg.val_var]; rw [hs1, ha1, ha2, hL 1 (by omega)]; simp
  · dsimp only [Arg.val_var]; rw [hs2, ha2, ha3, hL 2 (by omega)]; simp
  · dsimp only [Arg.val_var]; rw [hs3, ha3, hb0, hL 3 (by omega)]; simp

theorem scalarSha256msg2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {s0 s1 s2 s3 w0 w1 w2 w3 : Arg Val i32} {sums w : BitVec 128}
    (hs0 : s0.val = bvLane 32 0 sums) (hs1 : s1.val = bvLane 32 1 sums)
    (hs2 : s2.val = bvLane 32 2 sums) (hs3 : s3.val = bvLane 32 3 sums)
    (hw2 : w2.val = bvLane 32 2 w) (hw3 : w3.val = bvLane 32 3 w)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (Sha256.msg2 sums w) →
      r1.val = bvLane 32 1 (Sha256.msg2 sums w) →
      r2.val = bvLane 32 2 (Sha256.msg2 sums w) →
      r3.val = bvLane 32 3 (Sha256.msg2 sums w) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 k) m := by
  unfold scalarSha256msg2 emitAdd32
  apply emitShaSig1_wp w2; intro sig2 hsig2
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig1_wp w3; intro sig3 hsig3
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig1_wp (.var _); intro sig16 hsig16
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  apply emitShaSig1_wp (.var _); intro sig17 hsig17
  dsimp only [wp, Op.wp, op2, vals]; rw [OpCode.wp_add]
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  have hL : ∀ (idx : Nat), idx < 4 →
      bvLane 32 idx (Sha256.msg2 sums w) =
        let w16 := bvLane 32 0 sums + Sha256.σ₁ (bvLane 32 2 w)
        let w17 := bvLane 32 1 sums + Sha256.σ₁ (bvLane 32 3 w)
        let w18 := bvLane 32 2 sums + Sha256.σ₁ w16
        let w19 := bvLane 32 3 sums + Sha256.σ₁ w17
        if idx = 0 then w16 else if idx = 1 then w17 else if idx = 2 then w18 else w19 := by
    intro idx hIdx
    unfold Sha256.msg2
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit32
    rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hdiv : (32 * idx + bit) / 32 = idx := by omega
    have hmod : (32 * idx + bit) % 32 = bit := by omega
    have hlt4 : idx < 128 / 32 := by omega
    simp only [hbit32, decide_true, Bool.true_and, hdiv, hmod, hlt4, ↓reduceIte]
    rcases idx with _ | _ | _ | _ | _ <;> first | omega | rfl
  apply hk
  · dsimp only [Arg.val_var]; rw [hsig2, hs0, hw2, hL 0 (by omega)]; rfl
  · dsimp only [Arg.val_var]; rw [hsig3, hs1, hw3, hL 1 (by omega)]; rfl
  · dsimp only [Arg.val_var]; rw [hsig16, hsig2, hs0, hs2, hw2, hL 2 (by omega)]; rfl
  · dsimp only [Arg.val_var]; rw [hsig17, hsig3, hs1, hs3, hw3, hL 3 (by omega)]; rfl

private theorem legalSimdScalar128_goWords_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (on128 : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
      Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
      (Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) → Expr Val Cont rs)
    (spec128 : BitVec 128 → BitVec 128 → BitVec 128)
    (h128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
      (k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (m : Mem 64),
      a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u →
        a3.val = bvLane 32 3 u →
      b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v →
        b3.val = bvLane 32 3 v →
      (∀ r0 r1 r2 r3 : Arg Val i32,
        r0.val = bvLane 32 0 (spec128 u v) →
        r1.val = bvLane 32 1 (spec128 u v) →
        r2.val = bvLane 32 2 (spec128 u v) →
        r3.val = bvLane 32 3 (spec128 u v) →
        wp Γ Q X (k r0 r1 r2 r3) m) →
      wp Γ Q X (on128 a0 a1 a2 a3 b0 b1 b2 b3 k) m)
    (t : Ty) (ht : target.supportsTy t = true) (hSize : t.size ≠ 0 ∧ t.size % 128 = 0)
    (xBits yBits specFull : BitVec t.size)
    (hChunks : ∀ q, q < t.size / 128 → ∀ j, j < 128 →
      specFull.getLsbD (128 * q + j) =
        (spec128 (BitVec.extractLsb' (128 * q) 128 xBits)
          (BitVec.extractLsb' (128 * q) 128 yBits)).getLsbD j) :
    ∀ (rem : Nat) (q : Nat), q + rem = t.size / 128 →
      ∀ (rx ry acc : List (Arg Val i64)) (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs)
        (m : Mem 64),
        rx.length = 2 * rem → ry.length = 2 * rem → acc.length = 2 * q →
        (∀ i, i < 128 * rem → words64GetLsb rx i = xBits.getLsbD (128 * q + i)) →
        (∀ i, i < 128 * rem → words64GetLsb ry i = yBits.getLsbD (128 * q + i)) →
        (∀ i, i < 128 * q → words64GetLsb acc i = specFull.getLsbD i) →
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t specFull) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalSimdScalar128.goWords target on128 t k rx ry acc) m
  | 0, q, hq, rx, ry, acc, k, m, hrxLen, hryLen, haccLen, _, _, hAcc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    have hrxNil : rx = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hryNil : ry = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hrxNil hryNil
    dsimp only
    apply unpackWords64ToLeaves_wp target hv t ht (words := acc) (off := 0) (v := ofBits t specFull)
    · intro i hi
      rw [Nat.zero_add, toBits_ofBits]
      exact hAcc i (by omega)
    · intro fres hFres
      exact packLeavesToLegal_wp target t ht fres (ofBits t specFull) hFres hk
  | rem + 1, q, hq, rx, ry, acc, k, m, hrxLen, hryLen, haccLen, hRx, hRy, hAcc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    rcases rx with _ | ⟨x0, _ | ⟨x1, rxs⟩⟩
    · simp at hrxLen
    · simp only [List.length_cons, List.length_nil] at hrxLen; omega
    · rcases ry with _ | ⟨y0, _ | ⟨y1, rys⟩⟩
      · simp at hryLen
      · simp only [List.length_cons, List.length_nil] at hryLen; omega
      · dsimp only
        have hx0 : x0.val = BitVec.extractLsb' 0 64 (BitVec.extractLsb' (128 * q) 128 xBits) := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
          have hw := hRx j (by omega)
          have hlt128 : j < 128 := by omega
          simpa [words64GetLsb, Nat.div_eq_of_lt hj64, Nat.mod_eq_of_lt hj64, hj64, hlt128] using hw
        have hx1 : x1.val = BitVec.extractLsb' 64 64 (BitVec.extractLsb' (128 * q) 128 xBits) := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
          have hw := hRx (64 + j) (by omega)
          have hdiv : (64 + j) / 64 = 1 := by omega
          have hmod : (64 + j) % 64 = j := by omega
          have hlt128 : 64 + j < 128 := by omega
          simpa [words64GetLsb, hdiv, hmod, hj64, hlt128, Nat.add_assoc] using hw
        have hy0 : y0.val = BitVec.extractLsb' 0 64 (BitVec.extractLsb' (128 * q) 128 yBits) := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
          have hw := hRy j (by omega)
          have hlt128 : j < 128 := by omega
          simpa [words64GetLsb, Nat.div_eq_of_lt hj64, Nat.mod_eq_of_lt hj64, hj64, hlt128] using hw
        have hy1 : y1.val = BitVec.extractLsb' 64 64 (BitVec.extractLsb' (128 * q) 128 yBits) := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
          have hw := hRy (64 + j) (by omega)
          have hdiv : (64 + j) / 64 = 1 := by omega
          have hmod : (64 + j) % 64 = j := by omega
          have hlt128 : 64 + j < 128 := by omega
          simpa [words64GetLsb, hdiv, hmod, hj64, hlt128, Nat.add_assoc] using hw
        apply words2ToDwords4_wp hx0 hx1; intro a0 a1 a2 a3 ha0 ha1 ha2 ha3
        apply words2ToDwords4_wp hy0 hy1; intro b0 b1 b2 b3 hb0 hb1 hb2 hb3
        apply h128 (u := BitVec.extractLsb' (128 * q) 128 xBits)
          (v := BitVec.extractLsb' (128 * q) 128 yBits) _ m ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
        intro r0 r1 r2 r3 hr0 hr1 hr2 hr3
        apply dwords4ToWords2_wp hr0 hr1 hr2 hr3; intro w0 w1 hw0 hw1
        apply legalSimdScalar128_goWords_wp target hv on128 spec128 h128 t ht hSize xBits yBits
          specFull
          hChunks rem (q + 1) (by omega) rxs rys (acc ++ [w0, w1]) k m
          (by simp only [List.length_cons] at hrxLen; omega)
          (by simp only [List.length_cons] at hryLen; omega)
          (by simp [haccLen]; omega)
        · intro i hi
          have h := hRx (128 + i) (by omega)
          have hdiv : (128 + i) / 64 = i / 64 + 2 := by omega
          have hmod : (128 + i) % 64 = i % 64 := by omega
          simp only [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_cons_succ] at h
          rwa [show 128 * (q + 1) + i = 128 * q + (128 + i) by omega]
        · intro i hi
          have h := hRy (128 + i) (by omega)
          have hdiv : (128 + i) / 64 = i / 64 + 2 := by omega
          have hmod : (128 + i) % 64 = i % 64 := by omega
          simp only [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_cons_succ] at h
          rwa [show 128 * (q + 1) + i = 128 * q + (128 + i) by omega]
        · intro i hi
          by_cases hltOld : i < 128 * q
          · rw [words64GetLsb_append_left acc [w0, w1] (by rw [haccLen]; omega)]
            exact hAcc i hltOld
          · have hChunkEq := hChunks q (by omega) (i - 128 * q) (by omega)
            rw [show 128 * q + (i - 128 * q) = i by omega] at hChunkEq
            rw [hChunkEq]
            by_cases hltMid : i < 128 * q + 64
            · have hdiv : i / 64 = acc.length := by rw [haccLen]; omega
              have hmod : i % 64 = i - 128 * q := by omega
              have hj64 : i - 128 * q < 64 := by omega
              simp only
                [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_append_right (Nat.le_refl _)]
              simp [hw0, hj64]
            · have hdiv : i / 64 = acc.length + 1 := by rw [haccLen]; omega
              have hmod : i % 64 = i - (128 * q + 64) := by omega
              have hj64 : i - (128 * q + 64) < 64 := by omega
              simp only
                [words64GetLsb, hdiv, hmod, List.getD,
                List.getElem?_append_right (by omega : acc.length ≤ acc.length + 1),
                show acc.length + 1 - acc.length = 1 by omega]
              simp [hw1, hj64, show 64 + (i - (128 * q + 64)) = i - 128 * q by omega]
        · exact hk

private theorem legalSimdScalar128_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (on128 : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
      Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 →
      (Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) → Expr Val Cont rs)
    (spec128 : BitVec 128 → BitVec 128 → BitVec 128)
    (h128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
      (k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (m : Mem 64),
      a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u →
        a3.val = bvLane 32 3 u →
      b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v →
        b3.val = bvLane 32 3 v →
      (∀ r0 r1 r2 r3 : Arg Val i32,
        r0.val = bvLane 32 0 (spec128 u v) →
        r1.val = bvLane 32 1 (spec128 u v) →
        r2.val = bvLane 32 2 (spec128 u v) →
        r3.val = bvLane 32 3 (spec128 u v) →
        wp Γ Q X (k r0 r1 r2 r3) m) →
      wp Γ Q X (on128 a0 a1 a2 a3 b0 b1 b2 b3 k) m)
    (t : Ty) (ht : target.supportsTy t = true) (hSize : t.size ≠ 0 ∧ t.size % 128 = 0)
    (xs ys : Tup (Arg Val) (target.legalTys t)) (x y : Val t)
    (hx : valsTup xs = encodeVal target t x) (hy : valsTup ys = encodeVal target t y)
    (specFull : BitVec t.size)
    (hChunks : ∀ q, q < t.size / 128 → ∀ j, j < 128 →
      specFull.getLsbD (128 * q + j) =
        (spec128 (BitVec.extractLsb' (128 * q) 128 (toBits t x))
                 (BitVec.extractLsb' (128 * q) 128 (toBits t y))).getLsbD j)
    (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64)
    (hk : ∀ res : Tup (Arg Val) (target.legalTys t),
      valsTup res = encodeVal target t (ofBits t specFull) → wp Γ Q X (k res) m) :
    wp Γ Q X (legalSimdScalar128 target on128 t xs ys k) m := by
  unfold legalSimdScalar128
  apply splitLegalToLeaves_wp target t ht xs x hx; intro fx hFx
  apply splitLegalToLeaves_wp target t ht ys y hy; intro fy hFy
  apply packLeavesToWords64_wp target hv t ht hFx; intro wx hWx _ hWxDiv
  apply packLeavesToWords64_wp target hv t ht hFy; intro wy hWy _ hWyDiv
  have hMod64 : t.size % 64 = 0 := by omega
  have hWxLen : wx.length = 2 * (t.size / 128) := by rw [hWxDiv hMod64]; omega
  have hWyLen : wy.length = 2 * (t.size / 128) := by rw [hWyDiv hMod64]; omega
  apply legalSimdScalar128_goWords_wp target hv on128 spec128 h128 t ht hSize (toBits t x)
    (toBits t y)
    specFull hChunks (t.size / 128) 0 (by omega) wx wy [] k m hWxLen hWyLen rfl
  · intro i hi; rw [Nat.zero_add]; exact hWx i (by omega)
  · intro i hi; rw [Nat.zero_add]; exact hWy i (by omega)
  · intro i hi; omega
  · exact hk

private theorem extractLsb_128_shuffleDwords {w : Nat} (hw : w % 128 = 0)
    (v : BitVec w) (q : Nat) (hq : q < w / 128) (imm : BitVec 8) :
    ∀ j, j < 128 →
      (shuffleDwords v imm).getLsbD (128 * q + j) =
        (shuffleDwords (BitVec.extractLsb' (128 * q) 128 v) imm).getLsbD j := by
  intro j hj
  unfold shuffleDwords
  have hLt : 128 * q + j < w := by omega
  rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
  have hW : w / 32 = 4 * (w / 128) := by omega
  have hdiv1 : (128 * q + j) / 32 = 4 * q + j / 32 := by omega
  have hmod1 : (128 * q + j) % 32 = j % 32 := by omega
  have hc1 : (128 * q + j) / 32 < w / 32 := by omega
  have hc2 : j / 32 < 128 / 32 := by omega
  have hInner : (4 * q + j / 32) / 4 = q + (j / 32) / 4 := by omega
  have hInnerZ : (j / 32) / 4 = 0 := by omega
  have hMod4 : (4 * q + j / 32) % 4 = (j / 32) % 4 := by omega
  rw [hdiv1] at hc1
  simp only [hc1, hc2, ↓reduceIte, hdiv1, hmod1, hInner, hInnerZ, hMod4, Nat.add_zero]
  rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
  have hj32 : j % 32 < 32 := Nat.mod_lt _ (by omega)
  have hm4 : imm.toNat >>> (2 * ((j / 32) % 4)) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hlt128 : 32 * (0 + imm.toNat >>> (2 * ((j / 32) % 4)) % 4) + j % 32 < 128 := by omega
  simp only [hj32, decide_true, Bool.true_and, hlt128]
  congr 1
  generalize imm.toNat >>> (2 * ((j / 32) % 4)) % 4 = laneIdx at *
  omega

private theorem extractLsb_128_blendWords {w : Nat} (hw : w % 128 = 0)
    (a b : BitVec w) (q : Nat) (hq : q < w / 128) (imm : BitVec 8) :
    ∀ j, j < 128 →
      (blendWords a b imm).getLsbD (128 * q + j) =
        (blendWords (BitVec.extractLsb' (128 * q) 128 a) (BitVec.extractLsb' (128 * q) 128 b)
          imm).getLsbD j := by
  intro j hj
  unfold blendWords
  have hLt : 128 * q + j < w := by omega
  rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
  have hdiv1 : (128 * q + j) / 16 = 8 * q + j / 16 := by omega
  have hmod1 : (128 * q + j) % 16 = j % 16 := by omega
  have hc1 : (128 * q + j) / 16 < w / 16 := by omega
  have hc2 : j / 16 < 128 / 16 := by omega
  have hMod8 : (8 * q + j / 16) % 8 = (j / 16) % 8 := by omega
  rw [hdiv1] at hc1
  simp only [hc1, hc2, ↓reduceIte, hdiv1, hmod1, hMod8]
  have hj16 : j % 16 < 16 := Nat.mod_lt _ (by omega)
  have hlt128 : 16 * (j / 16) + j % 16 < 128 := by omega
  cases imm.getLsbD (j / 16 % 8) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;>
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb'] <;>
    simp [hj16, hlt128, show 128 * q + (16 * (j / 16) + j % 16) = 16 * (8 * q + j / 16) + j % 16 by
      omega]

private theorem extractLsb_128_alignBytes {w : Nat} (hw : w % 128 = 0)
    (hi lo : BitVec w) (q : Nat) (hq : q < w / 128) (imm : BitVec 8) :
    ∀ j, j < 128 →
      (alignBytes hi lo imm).getLsbD (128 * q + j) =
        (alignBytes (BitVec.extractLsb' (128 * q) 128 hi) (BitVec.extractLsb' (128 * q) 128 lo)
          imm).getLsbD j := by
  intro j hj
  unfold alignBytes
  have hLt : 128 * q + j < w := by omega
  rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
  have hdiv1 : (128 * q + j) / 8 = 16 * q + j / 8 := by omega
  have hmod1 : (128 * q + j) % 8 = j % 8 := by omega
  have hc1 : (128 * q + j) / 8 < w / 8 := by omega
  have hc2 : j / 8 < 128 / 8 := by omega
  have hMod16 : (16 * q + j / 8) % 16 = (j / 8) % 16 := by omega
  have hDiv16 : (16 * q + j / 8) / 16 = q + (j / 8) / 16 := by omega
  have hDivZ : (j / 8) / 16 = 0 := by omega
  rw [hdiv1] at hc1
  simp only [hc1, hc2, ↓reduceIte, hdiv1, hmod1, hMod16, hDiv16, hDivZ, Nat.add_zero]
  by_cases h16 : j / 8 % 16 + imm.toNat < 16
  · simp only [h16, ↓reduceIte]
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    have hlt128 : 8 * (0 + (j / 8 % 16 + imm.toNat)) + j % 8 < 128 := by omega
    simp only [Nat.zero_add] at hlt128 ⊢
    simp [hj8, hlt128, show 128 * q + (8 * (j / 8 % 16 + imm.toNat) + j % 8) =
      8 * (16 * q + (j / 8 % 16 + imm.toNat)) + j % 8 by omega]
  · by_cases h32 : j / 8 % 16 + imm.toNat < 32
    · simp only [h16, h32, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
      have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
      have hlt128 : 8 * (0 + (j / 8 % 16 + imm.toNat) - 16) + j % 8 < 128 := by omega
      simp only [Nat.zero_add] at hlt128 ⊢
      simp [hj8, hlt128, show 128 * q + (8 * (j / 8 % 16 + imm.toNat - 16) + j % 8) =
        8 * (16 * q + (j / 8 % 16 + imm.toNat) - 16) + j % 8 by omega]
    · simp [h16, h32]

private theorem extractLsb_128_shuffleBytes {w : Nat} (hw : w % 128 = 0)
    (a m : BitVec w) (q : Nat) (hq : q < w / 128) :
    ∀ j, j < 128 →
      (shuffleBytes a m).getLsbD (128 * q + j) =
        (shuffleBytes (BitVec.extractLsb' (128 * q) 128 a)
          (BitVec.extractLsb' (128 * q) 128 m)).getLsbD j := by
  intro j hj
  unfold shuffleBytes
  have hLt : 128 * q + j < w := by omega
  rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
  have hdiv1 : (128 * q + j) / 8 = 16 * q + j / 8 := by omega
  have hmod1 : (128 * q + j) % 8 = j % 8 := by omega
  have hc1 : (128 * q + j) / 8 < w / 8 := by omega
  have hc2 : j / 8 < 128 / 8 := by omega
  have hDiv16 : (16 * q + j / 8) / 16 = q := by omega
  have hDivZ : (j / 8) / 16 = 0 := by omega
  rw [hdiv1] at hc1
  simp only [hc1, hc2, ↓reduceIte, hdiv1, hmod1, hDiv16, hDivZ, Nat.mul_zero, Nat.zero_add]
  have hIdxEq :
    bvLane 8 (16 * q + j / 8) m = bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m) := by
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
    have hlt128 : 8 * (j / 8) + bit < 128 := by omega
    simp [hbit8, hlt128, show 128 * q + (8 * (j / 8) + bit) = 8 * (16 * q + j / 8) + bit by omega]
  rw [hIdxEq]
  cases hmsb : (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    have hm16 : (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16 < 16 :=
      Nat.mod_lt _ (by omega)
    have hlt128 :
      8 * ((bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8 < 128 := by
      omega
    simp [hj8, hlt128,
      show 128 * q +
      (8 * ((bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8) =
      8 * (16 * q + (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8 by
        omega]
  · simp

private theorem simdPair_split_shuffleDwords (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (x : Val (.pair a b)) (imm : BitVec 8) :
    ofBits (.pair a b) (shuffleDwords (toBits (.pair a b) x) imm) =
      (ofBits a (shuffleDwords (toBits a x.1) imm),
       ofBits b (shuffleDwords (toBits b x.2) imm)) := by
  dsimp only [ofBits]
  congr 1
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and, Nat.zero_add]
    unfold shuffleDwords
    have hLt : j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : j / 32 < (a.pair b).size / 32 := by simp [Ty.size]; omega
    have hc2 : j / 32 < a.size / 32 := by omega
    have hSelLt : 4 * (j / 32 / 4) + imm.toNat >>> (2 * (j / 32 % 4)) % 4 < a.size / 32 := by
      have : j / 32 / 4 < a.size / 128 := by omega
      have : imm.toNat >>> (2 * (j / 32 % 4)) % 4 < 4 := Nat.mod_lt _ (by omega)
      omega
    simp only [hc1, hc2, ↓reduceIte]
    rw [getLsbD_bvLane, getLsbD_bvLane]
    have hj32 : j % 32 < 32 := Nat.mod_lt _ (by omega)
    have hBitLt :
      32 * (4 * (j / 32 / 4) + imm.toNat >>> (2 * (j / 32 % 4)) % 4) + j % 32 < a.size := by omega
    simp [hj32, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and]
    unfold shuffleDwords
    have hLt : a.size + j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : (a.size + j) / 32 < (a.pair b).size / 32 := by simp [Ty.size]; omega
    have hc2 : j / 32 < b.size / 32 := by omega
    have hdiv : (a.size + j) / 32 = a.size / 32 + j / 32 := by omega
    have hmod : (a.size + j) % 32 = j % 32 := by omega
    have hKa : (a.size / 32 + j / 32) / 4 = a.size / 128 + (j / 32) / 4 := by omega
    have hMod4 : (a.size / 32 + j / 32) % 4 = (j / 32) % 4 := by omega
    rw [hdiv] at hc1
    simp only [hc1, hc2, ↓reduceIte, hdiv, hmod, hKa, hMod4]
    rw [getLsbD_bvLane, getLsbD_bvLane]
    have hj32 : j % 32 < 32 := Nat.mod_lt _ (by omega)
    have hm4 : imm.toNat >>> (2 * (j / 32 % 4)) % 4 < 4 := Nat.mod_lt _ (by omega)
    have hNotLt :
      ¬(32 * (4 * (a.size / 128 + j / 32 / 4) + imm.toNat >>> (2 * (j / 32 % 4)) % 4) + j % 32 <
      a.size) := by omega
    simp only [hj32, decide_true, Bool.true_and, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append,
      hNotLt, ↓reduceIte]
    congr 1
    generalize imm.toNat >>> (2 * (j / 32 % 4)) % 4 = laneIdx at *
    omega

private theorem simdPair_split_blendWords (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (x y : Val (.pair a b)) (imm : BitVec 8) :
    ofBits (.pair a b) (blendWords (toBits (.pair a b) x) (toBits (.pair a b) y) imm) =
      (ofBits a (blendWords (toBits a x.1) (toBits a y.1) imm),
       ofBits b (blendWords (toBits b x.2) (toBits b y.2) imm)) := by
  dsimp only [ofBits]
  congr 1
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and, Nat.zero_add]
    unfold blendWords
    have hLt : j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : j / 16 < (a.pair b).size / 16 := by simp [Ty.size]; omega
    have hc2 : j / 16 < a.size / 16 := by omega
    simp only [hc1, hc2, ↓reduceIte]
    have hj16 : j % 16 < 16 := Nat.mod_lt _ (by omega)
    have hBitLt : 16 * (j / 16) + j % 16 < a.size := by omega
    cases imm.getLsbD (j / 16 % 8) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [getLsbD_bvLane, getLsbD_bvLane] <;>
      simp [hj16, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and]
    unfold blendWords
    have hLt : a.size + j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : (a.size + j) / 16 < (a.pair b).size / 16 := by simp [Ty.size]; omega
    have hc2 : j / 16 < b.size / 16 := by omega
    have hdiv : (a.size + j) / 16 = a.size / 16 + j / 16 := by omega
    have hmod : (a.size + j) % 16 = j % 16 := by omega
    have hMod8 : (a.size / 16 + j / 16) % 8 = (j / 16) % 8 := by omega
    rw [hdiv] at hc1
    simp only [hc1, hc2, ↓reduceIte, hdiv, hmod, hMod8]
    have hj16 : j % 16 < 16 := Nat.mod_lt _ (by omega)
    have hNotLt : ¬(16 * (a.size / 16 + j / 16) + j % 16 < a.size) := by omega
    cases imm.getLsbD (j / 16 % 8) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [getLsbD_bvLane, getLsbD_bvLane] <;>
      simp [hj16, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 16 * (a.size / 16 + j / 16) + j % 16 - a.size = 16 * (j / 16) + j % 16 by omega]

private theorem simdPair_split_alignBytes (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (hi lo : Val (.pair a b)) (imm : BitVec 8) :
    ofBits (.pair a b) (alignBytes (toBits (.pair a b) hi) (toBits (.pair a b) lo) imm) =
      (ofBits a (alignBytes (toBits a hi.1) (toBits a lo.1) imm),
       ofBits b (alignBytes (toBits b hi.2) (toBits b lo.2) imm)) := by
  dsimp only [ofBits]
  congr 1
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and, Nat.zero_add]
    unfold alignBytes
    have hLt : j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : j / 8 < (a.pair b).size / 8 := by simp [Ty.size]; omega
    have hc2 : j / 8 < a.size / 8 := by omega
    simp only [hc1, hc2, ↓reduceIte]
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    by_cases h16 : j / 8 % 16 + imm.toNat < 16
    · simp only [h16, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hBitLt : 8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 < a.size := by omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
    · by_cases h32 : j / 8 % 16 + imm.toNat < 32
      · simp only [h16, h32, ↓reduceIte]
        rw [getLsbD_bvLane, getLsbD_bvLane]
        have hBitLt : 8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 < a.size := by
          omega
        simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
      · simp [h16, h32]
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and]
    unfold alignBytes
    have hLt : a.size + j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : (a.size + j) / 8 < (a.pair b).size / 8 := by simp [Ty.size]; omega
    have hc2 : j / 8 < b.size / 8 := by omega
    have hdiv : (a.size + j) / 8 = a.size / 8 + j / 8 := by omega
    have hmod : (a.size + j) % 8 = j % 8 := by omega
    have hMod16 : (a.size / 8 + j / 8) % 16 = (j / 8) % 16 := by omega
    have hDiv16 : (a.size / 8 + j / 8) / 16 = a.size / 128 + (j / 8) / 16 := by omega
    rw [hdiv] at hc1
    simp only [hc1, hc2, ↓reduceIte, hdiv, hmod, hMod16, hDiv16]
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    by_cases h16 : j / 8 % 16 + imm.toNat < 16
    · simp only [h16, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hNotLt :
        ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 < a.size) := by
        omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 - a.size =
          8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 by omega]
    · by_cases h32 : j / 8 % 16 + imm.toNat < 32
      · simp only [h16, h32, ↓reduceIte]
        rw [getLsbD_bvLane, getLsbD_bvLane]
        have hNotLt :
          ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 <
          a.size) := by omega
        simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
          show 8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 -
            a.size =
            8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 by omega]
      · simp [h16, h32]

private theorem simdPair_split_shuffleBytes (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (x m : Val (.pair a b)) :
    ofBits (.pair a b) (shuffleBytes (toBits (.pair a b) x) (toBits (.pair a b) m)) =
      (ofBits a (shuffleBytes (toBits a x.1) (toBits a m.1)),
       ofBits b (shuffleBytes (toBits b x.2) (toBits b m.2))) := by
  dsimp only [ofBits]
  congr 1
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and, Nat.zero_add]
    unfold shuffleBytes
    have hLt : j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : j / 8 < (a.pair b).size / 8 := by simp [Ty.size]; omega
    have hc2 : j / 8 < a.size / 8 := by omega
    simp only [hc1, hc2, ↓reduceIte]
    have hIdxEq : bvLane 8 (j / 8) (toBits (a.pair b) m) = bvLane 8 (j / 8) (toBits a m.1) := by
      apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hBitLt : 8 * (j / 8) + bit < a.size := by omega
      simp [hbit8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
    rw [hIdxEq]
    cases (bvLane 8 (j / 8) (toBits a m.1)).msb
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
      have hm16 : (bvLane 8 (j / 8) (toBits a m.1)).toNat % 16 < 16 := Nat.mod_lt _ (by omega)
      have hBitLt :
        8 * (16 * (j / 8 / 16) + (bvLane 8 (j / 8) (toBits a m.1)).toNat % 16) + j % 8 < a.size :=
        by
        have : j / 8 / 16 < a.size / 128 := by omega
        omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hBitLt]
    · simp
  · congr 1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_extractLsb']; simp only [hj, decide_true, Bool.true_and]
    unfold shuffleBytes
    have hLt : a.size + j < (a.pair b).size := by simp [Ty.size]; omega
    rw [getLsbD_bvOfLanes (by omega) _ hLt, getLsbD_bvOfLanes (by omega) _ hj]
    have hc1 : (a.size + j) / 8 < (a.pair b).size / 8 := by simp [Ty.size]; omega
    have hc2 : j / 8 < b.size / 8 := by omega
    have hdiv : (a.size + j) / 8 = a.size / 8 + j / 8 := by omega
    have hmod : (a.size + j) % 8 = j % 8 := by omega
    have hDiv16 : (a.size / 8 + j / 8) / 16 = a.size / 128 + (j / 8) / 16 := by omega
    rw [hdiv] at hc1
    simp only [hc1, hc2, ↓reduceIte, hdiv, hmod, hDiv16]
    have hIdxEq :
      bvLane 8 (a.size / 8 + j / 8) (toBits (a.pair b) m) = bvLane 8 (j / 8) (toBits b m.2) := by
      apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hNotLt : ¬(8 * (a.size / 8 + j / 8) + bit < a.size) := by omega
      simp [hbit8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 8 * (a.size / 8 + j / 8) + bit - a.size = 8 * (j / 8) + bit by omega]
    rw [hIdxEq]
    cases (bvLane 8 (j / 8) (toBits b m.2)).msb
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [getLsbD_bvLane, getLsbD_bvLane]
      have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
      have hm16 : (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16 < 16 := Nat.mod_lt _ (by omega)
      have hNotLt :
        ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16) + j
        % 8 < a.size) := by omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 8 * (16 * (a.size / 128 + j / 8 / 16) + (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16) +
          j % 8 - a.size =
          8 * (16 * (j / 8 / 16) + (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16) + j % 8 by omega]
    · simp

theorem legalShufd_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (imm : BitVec 8) :
    ∀ (t : Ty), target.supportsTy t = true → t.size ≠ 0 → t.size % 128 = 0 →
    ∀ (xs : Tup (Arg Val) (target.legalTys t)) (x : Val t),
      valsTup xs = encodeVal target t x →
      ∀ (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t (shuffleDwords (toBits t x) imm)) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalShufd target imm t xs k) m
  | t, ht, hNe, hMod, xs, x, hx, k, m, hk => by
    have hBad : ∀ {u : Ty}, u.size ≠ 0 → u.size % 128 = 0 →
        (u.size == 0 || u.size % 128 != 0) = false := fun h1 h2 => by
      simp [beq_false_of_ne h1, h2]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u _v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs)
          (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u →
          a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 _v → b1.val = bvLane 32 1 _v → b2.val = bvLane 32 2 _v →
          b3.val = bvLane 32 3 _v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (shuffleDwords u imm) →
          r1.val = bvLane 32 1 (shuffleDwords u imm) →
          r2.val = bvLane 32 2 (shuffleDwords u imm) →
          r3.val = bvLane 32 3 (shuffleDwords u imm) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (match scalarShufd128 imm a0 a1 a2 a3 with | (r0, r1, r2, r3) => cont r0 r1 r2 r3)
          mem := by
      intro a0 a1 a2 a3 b0 b1 b2 b3 u _v cont mem ha0 ha1 ha2 ha3 _ _ _ _ hcont
      rcases scalarShufd128_eq imm ha0 ha1 ha2 ha3 with ⟨h0, h1, h2, h3⟩
      exact hcont _ _ _ _ h0 h1 h2 h3
    cases t with
    | bool | bits _ | float _ =>
      dsimp only [legalShufd]
      simp only [hBad hNe hMod, Bool.false_eq_true, ↓reduceIte]
      exact legalSimdScalar128_wp target hv _ (fun u _ => shuffleDwords u imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs xs x x hx hx _
        (fun q hq j hj => extractLsb_128_shuffleDwords hMod (toBits _ x) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only [legalShufd]
      simp only [hBad hNe hMod, Bool.false_eq_true, ↓reduceIte]
      by_cases hPack : target.keepsPacked (.pair a b) = true
      · simp only [hPack, ↓reduceDIte]
        by_cases hVec : target.vecIntOpSupported (.shufd (.pair a b) imm) (.pair a b) false = true
        · simp only [hVec, ↓reduceIte, wp, Op.wp, op1, vals]
          rw [OpCode.wp_shufd]
          refine ⟨hNe, hMod, ?_⟩
          have hx' : (packedToTup hPack xs).fst.val = x := by
            have h1 := valsTup_packedToTup_encode target hPack hx
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          rw [hx']
          apply hk
          exact valsTup_tupToPacked_encode target hPack rfl
        · simp only [hVec, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u _ => shuffleDwords u imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs xs x x hx hx _
            (fun q hq j hj =>
              extractLsb_128_shuffleDwords hMod (toBits (.pair a b) x) q hq imm j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 :
          (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
        · simp only [hSplit128, ↓reduceIte]
          rcases (by simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hSplit128 :
              ((a.size ≠ 0 ∧ a.size % 128 = 0) ∧ b.size ≠ 0) ∧ b.size % 128 = 0) with
            ⟨⟨⟨haNe, haMod⟩, hbNe⟩, hbMod⟩
          have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
            simpa [LegalTarget.supportsTy] using ht
          have hSplitXs := tupSplit_valsTup (fx := splitToTup hPackF xs)
          rw [valsTup_splitToTup_encode target hPackF hx] at hSplitXs
          have hxa : valsTup (tupSplit (splitToTup hPackF xs)).1 = encodeVal target a x.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitXs).symm
          have hxb : valsTup (tupSplit (splitToTup hPackF xs)).2 = encodeVal target b x.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitXs).symm
          apply legalShufd_wp target hv imm a hSupPair.1 haNe haMod _ x.1 hxa
          intro ra hRa
          apply legalShufd_wp target hv imm b hSupPair.2 hbNe hbMod _ x.2 hxb
          intro rb hRb
          apply hk
          apply valsTup_tupToSplit_encode target hPackF
          rw [simdPair_split_shuffleDwords a b ⟨haNe, haMod⟩ ⟨hbNe, hbMod⟩ x imm]
          rw [valsTup_tupAppend, hRa, hRb]
        · simp only [hSplit128, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u _ => shuffleDwords u imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs xs x x hx hx _
            (fun q hq j hj =>
              extractLsb_128_shuffleDwords hMod (toBits (.pair a b) x) q hq imm j hj)
            k m hk

theorem legalBlendw_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (imm : BitVec 8) :
    ∀ (t : Ty), target.supportsTy t = true → t.size ≠ 0 → t.size % 128 = 0 →
    ∀ (xs ys : Tup (Arg Val) (target.legalTys t)) (x y : Val t),
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      ∀ (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t (blendWords (toBits t x) (toBits t y) imm)) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalBlendw target imm t xs ys k) m
  | t, ht, hNe, hMod, xs, ys, x, y, hx, hy, k, m, hk => by
    have hBad : ∀ {u : Ty}, u.size ≠ 0 → u.size % 128 = 0 →
        (u.size == 0 || u.size % 128 != 0) = false := fun h1 h2 => by
      simp [beq_false_of_ne h1, h2]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs)
          (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u →
          a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v →
          b3.val = bvLane 32 3 v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (blendWords u v imm) →
          r1.val = bvLane 32 1 (blendWords u v imm) →
          r2.val = bvLane 32 2 (blendWords u v imm) →
          r3.val = bvLane 32 3 (blendWords u v imm) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (scalarBlendw128 imm a0 a1 a2 a3 b0 b1 b2 b3 cont) mem :=
      fun cont mem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont =>
        scalarBlendw128_wp imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    cases t with
    | bool | bits _ | float _ =>
      dsimp only [legalBlendw]
      simp only [hBad hNe hMod, Bool.false_eq_true, ↓reduceIte]
      exact legalSimdScalar128_wp target hv _ (fun u v => blendWords u v imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_blendWords hMod (toBits _ x) (toBits _ y) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only [legalBlendw]
      simp only [hBad hNe hMod, Bool.false_eq_true, ↓reduceIte]
      by_cases hPack : target.keepsPacked (.pair a b) = true
      · simp only [hPack, ↓reduceDIte]
        by_cases hVec : target.vecIntOpSupported (.blendw (.pair a b) imm) (.pair a b) false = true
        · simp only [hVec, ↓reduceIte, wp, Op.wp, op2, vals]
          rw [OpCode.wp_blendw]
          refine ⟨hNe, hMod, ?_⟩
          have hx' : (packedToTup hPack xs).fst.val = x := by
            have h1 := valsTup_packedToTup_encode target hPack hx
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          have hy' : (packedToTup hPack ys).fst.val = y := by
            have h1 := valsTup_packedToTup_encode target hPack hy
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          rw [hx', hy']
          apply hk
          exact valsTup_tupToPacked_encode target hPack rfl
        · simp only [hVec, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u v => blendWords u v imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj =>
              extractLsb_128_blendWords hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm
              j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 :
          (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
        · simp only [hSplit128, ↓reduceIte]
          rcases (by simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hSplit128 :
              ((a.size ≠ 0 ∧ a.size % 128 = 0) ∧ b.size ≠ 0) ∧ b.size % 128 = 0) with
            ⟨⟨⟨haNe, haMod⟩, hbNe⟩, hbMod⟩
          have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
            simpa [LegalTarget.supportsTy] using ht
          have hSplitXs := tupSplit_valsTup (fx := splitToTup hPackF xs)
          rw [valsTup_splitToTup_encode target hPackF hx] at hSplitXs
          have hSplitYs := tupSplit_valsTup (fx := splitToTup hPackF ys)
          rw [valsTup_splitToTup_encode target hPackF hy] at hSplitYs
          have hxa : valsTup (tupSplit (splitToTup hPackF xs)).1 = encodeVal target a x.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitXs).symm
          have hxb : valsTup (tupSplit (splitToTup hPackF xs)).2 = encodeVal target b x.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitXs).symm
          have hya : valsTup (tupSplit (splitToTup hPackF ys)).1 = encodeVal target a y.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitYs).symm
          have hyb : valsTup (tupSplit (splitToTup hPackF ys)).2 = encodeVal target b y.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitYs).symm
          apply legalBlendw_wp target hv imm a hSupPair.1 haNe haMod _ _ x.1 y.1 hxa hya
          intro ra hRa
          apply legalBlendw_wp target hv imm b hSupPair.2 hbNe hbMod _ _ x.2 y.2 hxb hyb
          intro rb hRb
          apply hk
          apply valsTup_tupToSplit_encode target hPackF
          rw [simdPair_split_blendWords a b ⟨haNe, haMod⟩ ⟨hbNe, hbMod⟩ x y imm]
          rw [valsTup_tupAppend, hRa, hRb]
        · simp only [hSplit128, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u v => blendWords u v imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj =>
              extractLsb_128_blendWords hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm
              j hj)
            k m hk

theorem legalAlignr_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (imm : BitVec 8) :
    ∀ (t : Ty), target.supportsTy t = true → t.size ≠ 0 → t.size % 128 = 0 →
    ∀ (xs ys : Tup (Arg Val) (target.legalTys t)) (x y : Val t),
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      ∀ (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t (alignBytes (toBits t x) (toBits t y) imm)) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalAlignr target imm t xs ys k) m
  | t, ht, hNe, hMod, xs, ys, x, y, hx, hy, k, m, hk => by
    have hBad : ∀ {u : Ty}, u.size ≠ 0 → u.size % 128 = 0 →
        (u.size == 0 || u.size % 128 != 0) = false := fun h1 h2 => by
      simp [beq_false_of_ne h1, h2]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs)
          (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u →
          a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v →
          b3.val = bvLane 32 3 v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (alignBytes u v imm) →
          r1.val = bvLane 32 1 (alignBytes u v imm) →
          r2.val = bvLane 32 2 (alignBytes u v imm) →
          r3.val = bvLane 32 3 (alignBytes u v imm) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (scalarAlignr128 imm a0 a1 a2 a3 b0 b1 b2 b3 cont) mem :=
      fun cont mem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont =>
        scalarAlignr128_wp imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    cases t with
    | bool | bits _ | float _ =>
      dsimp only [legalAlignr]
      simp only [hBad hNe hMod, Bool.false_eq_true, ↓reduceIte]
      exact legalSimdScalar128_wp target hv _ (fun u v => alignBytes u v imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_alignBytes hMod (toBits _ x) (toBits _ y) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only [legalAlignr]
      simp only [hBad hNe hMod, Bool.false_eq_true, ↓reduceIte]
      by_cases hPack : target.keepsPacked (.pair a b) = true
      · simp only [hPack, ↓reduceDIte]
        by_cases hVec : target.vecIntOpSupported (.alignr (.pair a b) imm) (.pair a b) false = true
        · simp only [hVec, ↓reduceIte, wp, Op.wp, op2, vals]
          rw [OpCode.wp_alignr]
          refine ⟨hNe, hMod, ?_⟩
          have hx' : (packedToTup hPack xs).fst.val = x := by
            have h1 := valsTup_packedToTup_encode target hPack hx
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          have hy' : (packedToTup hPack ys).fst.val = y := by
            have h1 := valsTup_packedToTup_encode target hPack hy
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          rw [hx', hy']
          apply hk
          exact valsTup_tupToPacked_encode target hPack rfl
        · simp only [hVec, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u v => alignBytes u v imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj =>
              extractLsb_128_alignBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm
              j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 :
          (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
        · simp only [hSplit128, ↓reduceIte]
          rcases (by simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hSplit128 :
              ((a.size ≠ 0 ∧ a.size % 128 = 0) ∧ b.size ≠ 0) ∧ b.size % 128 = 0) with
            ⟨⟨⟨haNe, haMod⟩, hbNe⟩, hbMod⟩
          have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
            simpa [LegalTarget.supportsTy] using ht
          have hSplitXs := tupSplit_valsTup (fx := splitToTup hPackF xs)
          rw [valsTup_splitToTup_encode target hPackF hx] at hSplitXs
          have hSplitYs := tupSplit_valsTup (fx := splitToTup hPackF ys)
          rw [valsTup_splitToTup_encode target hPackF hy] at hSplitYs
          have hxa : valsTup (tupSplit (splitToTup hPackF xs)).1 = encodeVal target a x.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitXs).symm
          have hxb : valsTup (tupSplit (splitToTup hPackF xs)).2 = encodeVal target b x.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitXs).symm
          have hya : valsTup (tupSplit (splitToTup hPackF ys)).1 = encodeVal target a y.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitYs).symm
          have hyb : valsTup (tupSplit (splitToTup hPackF ys)).2 = encodeVal target b y.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitYs).symm
          apply legalAlignr_wp target hv imm a hSupPair.1 haNe haMod _ _ x.1 y.1 hxa hya
          intro ra hRa
          apply legalAlignr_wp target hv imm b hSupPair.2 hbNe hbMod _ _ x.2 y.2 hxb hyb
          intro rb hRb
          apply hk
          apply valsTup_tupToSplit_encode target hPackF
          rw [simdPair_split_alignBytes a b ⟨haNe, haMod⟩ ⟨hbNe, hbMod⟩ x y imm]
          rw [valsTup_tupAppend, hRa, hRb]
        · simp only [hSplit128, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ (fun u v => alignBytes u v imm) hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj =>
              extractLsb_128_alignBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm
              j hj)
            k m hk

theorem legalShufb_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → t.size ≠ 0 → t.size % 128 = 0 →
    ∀ (xs ys : Tup (Arg Val) (target.legalTys t)) (x y : Val t),
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      ∀ (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
        (∀ res : Tup (Arg Val) (target.legalTys t),
          valsTup res = encodeVal target t (ofBits t (shuffleBytes (toBits t x) (toBits t y))) →
          wp Γ Q X (k res) m) →
        wp Γ Q X (legalShufb target t xs ys k) m
  | t, ht, hNe, hMod, xs, ys, x, y, hx, hy, k, m, hk => by
    have hBad : ∀ {u : Ty}, u.size ≠ 0 → u.size % 128 = 0 →
        (u.size == 0 || u.size % 128 != 0) = false := fun h1 h2 => by
      simp [beq_false_of_ne h1, h2]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs)
          (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u →
          a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v →
          b3.val = bvLane 32 3 v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (shuffleBytes u v) →
          r1.val = bvLane 32 1 (shuffleBytes u v) →
          r2.val = bvLane 32 2 (shuffleBytes u v) →
          r3.val = bvLane 32 3 (shuffleBytes u v) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (scalarShufb128 a0 a1 a2 a3 b0 b1 b2 b3 cont) mem :=
      fun cont mem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont =>
        scalarShufb128_wp ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    cases t with
    | bool | bits _ | float _ =>
      dsimp only [legalShufb]
      simp only [hBad hNe hMod, Bool.false_eq_true, ↓reduceIte]
      exact legalSimdScalar128_wp target hv _ shuffleBytes hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_shuffleBytes hMod (toBits _ x) (toBits _ y) q hq j hj)
        k m hk
    | pair a b =>
      dsimp only [legalShufb]
      simp only [hBad hNe hMod, Bool.false_eq_true, ↓reduceIte]
      by_cases hPack : target.keepsPacked (.pair a b) = true
      · simp only [hPack, ↓reduceDIte]
        by_cases hVec : target.vecIntOpSupported (.shufb (.pair a b)) (.pair a b) false = true
        · simp only [hVec, ↓reduceIte, wp, Op.wp, op2, vals]
          rw [OpCode.wp_shufb]
          refine ⟨hNe, hMod, ?_⟩
          have hx' : (packedToTup hPack xs).fst.val = x := by
            have h1 := valsTup_packedToTup_encode target hPack hx
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          have hy' : (packedToTup hPack ys).fst.val = y := by
            have h1 := valsTup_packedToTup_encode target hPack hy
            rw [valsTup_single] at h1
            exact congrArg Prod.fst h1
          rw [hx', hy']
          apply hk
          exact valsTup_tupToPacked_encode target hPack rfl
        · simp only [hVec, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ shuffleBytes hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj =>
              extractLsb_128_shuffleBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq j
              hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 :
          (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
        · simp only [hSplit128, ↓reduceIte]
          rcases (by simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hSplit128 :
              ((a.size ≠ 0 ∧ a.size % 128 = 0) ∧ b.size ≠ 0) ∧ b.size % 128 = 0) with
            ⟨⟨⟨haNe, haMod⟩, hbNe⟩, hbMod⟩
          have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
            simpa [LegalTarget.supportsTy] using ht
          have hSplitXs := tupSplit_valsTup (fx := splitToTup hPackF xs)
          rw [valsTup_splitToTup_encode target hPackF hx] at hSplitXs
          have hSplitYs := tupSplit_valsTup (fx := splitToTup hPackF ys)
          rw [valsTup_splitToTup_encode target hPackF hy] at hSplitYs
          have hxa : valsTup (tupSplit (splitToTup hPackF xs)).1 = encodeVal target a x.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitXs).symm
          have hxb : valsTup (tupSplit (splitToTup hPackF xs)).2 = encodeVal target b x.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitXs).symm
          have hya : valsTup (tupSplit (splitToTup hPackF ys)).1 = encodeVal target a y.1 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.fst hSplitYs).symm
          have hyb : valsTup (tupSplit (splitToTup hPackF ys)).2 = encodeVal target b y.2 := by
            simpa [tupSplit_tupAppend] using (congrArg Prod.snd hSplitYs).symm
          apply legalShufb_wp target hv a hSupPair.1 haNe haMod _ _ x.1 y.1 hxa hya
          intro ra hRa
          apply legalShufb_wp target hv b hSupPair.2 hbNe hbMod _ _ x.2 y.2 hxb hyb
          intro rb hRb
          apply hk
          apply valsTup_tupToSplit_encode target hPackF
          rw [simdPair_split_shuffleBytes a b ⟨haNe, haMod⟩ ⟨hbNe, hbMod⟩ x y]
          rw [valsTup_tupAppend, hRa, hRb]
        · simp only [hSplit128, Bool.false_eq_true, ↓reduceIte]
          exact legalSimdScalar128_wp target hv _ shuffleBytes hOn128
            (.pair a b) ht ⟨hNe, hMod⟩ xs ys x y hx hy _
            (fun q hq j hj =>
              extractLsb_128_shuffleBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq j
              hj)
            k m hk


end LegalWp

end LeanQbe.T
