module

public import LeanQbe.T.LegalWpBaseLemmas

/-!
# Legalization word-stream and 128-bit SIMD/SHA-256 lowering `_wp` lemmas (Part 2)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

section LegalWp


@[expose]
def words64GetLsb (ws : List (Arg Val i64)) (i : Nat) : Bool :=
  (ws.getD (i / 64) (.imm 0#64)).val.getLsbD (i % 64)

@[expose]
def Words64Stream (ws : List (Arg Val i64)) (acc : Arg Val i64)
    (accBits totalBits : Nat) (bits : Nat → Bool) : Prop :=
  accBits < 64 ∧
  totalBits = 64 * ws.length + accBits ∧
  (∀ j, accBits ≤ j → acc.val.getLsbD j = false) ∧
  (∀ i, i < 64 * ws.length → words64GetLsb ws i = bits i) ∧
  (∀ j, j < accBits → acc.val.getLsbD j = bits (64 * ws.length + j))

theorem list_getD_append_left {α : Type} (xs ys : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

theorem list_getD_append_right_eq {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD xs.length d = x := by
  simp [List.getD]

theorem words64GetLsb_append_left (ws ys : List (Arg Val i64)) {i : Nat}
    (hi : i < 64 * ws.length) :
    words64GetLsb (ws ++ ys) i = words64GetLsb ws i := by
  unfold words64GetLsb
  have hdiv : i / 64 < ws.length := Nat.div_lt_of_lt_mul (by omega)
  rw [list_getD_append_left ws ys (.imm 0#64) hdiv]

private theorem words64GetLsb_append_singleton_right (ws : List (Arg Val i64)) (x : Arg Val i64)
    {i : Nat} (hlo : 64 * ws.length ≤ i) (hhi : i < 64 * (ws.length + 1)) :
    words64GetLsb (ws ++ [x]) i = x.val.getLsbD (i - 64 * ws.length) := by
  unfold words64GetLsb
  have hdiv : i / 64 = ws.length := by
    apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmod : i % 64 = i - 64 * ws.length := by
    have := Nat.div_add_mod i 64
    rw [hdiv] at this
    omega
  rw [hdiv, list_getD_append_right_eq, hmod]

theorem Words64Stream.finish {ws : List (Arg Val i64)} {acc : Arg Val i64}
    {accBits totalBits : Nat} {bits : Nat → Bool}
    (hS : Words64Stream ws acc accBits totalBits bits) :
    let out := if accBits == 0 then ws else ws ++ [acc]
    (∀ i, i < totalBits → words64GetLsb out i = bits i) ∧
    out.length = (totalBits + 63) / 64 ∧
    (totalBits % 64 = 0 → out.length = totalBits / 64) := by
  rcases hS with ⟨hLt, hTot, _, hWs, hAcc⟩
  dsimp only
  by_cases h0 : accBits = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    rw [h0, Nat.add_zero] at hTot
    refine ⟨fun i hi => hWs i (hTot ▸ hi), ?_, fun _ => by rw [hTot]; omega⟩
    rw [hTot]; omega
  · have hne : (accBits == 0) = false := beq_false_of_ne h0
    simp only [hne, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      by_cases hlt : i < 64 * ws.length
      · rw [words64GetLsb_append_left ws [acc] hlt]
        exact hWs i hlt
      · have hge : 64 * ws.length ≤ i := Nat.le_of_not_lt hlt
        have hhi : i < 64 * (ws.length + 1) := by omega
        rw [words64GetLsb_append_singleton_right ws acc hge hhi]
        have hj : i - 64 * ws.length < accBits := by omega
        have := hAcc (i - 64 * ws.length) hj
        rwa [show 64 * ws.length + (i - 64 * ws.length) = i by omega] at this
    · rw [hTot]; omega
    · intro hmod
      exfalso
      have : accBits = 0 := by omega
      exact h0 this

private theorem words64GetLsb_ge (ws : List (Arg Val i64)) {i : Nat} (hi : 64 * ws.length ≤ i) :
    words64GetLsb ws i = false := by
  unfold words64GetLsb
  have hdiv : ws.length ≤ i / 64 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp [List.getD, hdiv]

private theorem Words64Stream.finish_all {ws : List (Arg Val i64)} {acc : Arg Val i64}
    {accBits totalBits : Nat} {bits : Nat → Bool}
    (hS : Words64Stream ws acc accBits totalBits bits) :
    let out := if accBits == 0 then ws else ws ++ [acc]
    (∀ i, words64GetLsb out i = if i < totalBits then bits i else false) ∧
    out.length = (totalBits + 63) / 64 ∧
    (totalBits % 64 = 0 → out.length = totalBits / 64) := by
  have ⟨hBits, hLen, hDiv⟩ := Words64Stream.finish hS
  rcases hS with ⟨hLt, hTot, hAccHi, _, _⟩
  refine ⟨fun i => ?_, hLen, hDiv⟩
  by_cases hi : i < totalBits
  · simp only [hi, ↓reduceIte]
    exact hBits i hi
  · simp only [hi, ↓reduceIte]
    by_cases h0 : accBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte]
      exact words64GetLsb_ge ws (by omega)
    · have hne : (accBits == 0) = false := beq_false_of_ne h0
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases hhi : i < 64 * (ws.length + 1)
      · rw [words64GetLsb_append_singleton_right ws acc (by omega) hhi]
        exact hAccHi (i - 64 * ws.length) (by omega)
      · exact words64GetLsb_ge (ws ++ [acc]) (by simp; omega)

theorem pushLeafWord64_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w : Nat} (hw : w ≤ 64) {leaf : Arg Val i64}
    {ws : List (Arg Val i64)} {acc : Arg Val i64} {accBits totalBits : Nat}
    {bits bits' : Nat → Bool}
    (hS : Words64Stream ws acc accBits totalBits bits)
    (hLeafHi : ∀ j, w ≤ j → leaf.val.getLsbD j = false)
    (hAgree : ∀ i, i < totalBits → bits' i = bits i)
    (hLeafBits : ∀ j, j < w → leaf.val.getLsbD j = bits' (totalBits + j))
    {k : List (Arg Val i64) → Arg Val i64 → Nat → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ ws' acc' accBits',
      Words64Stream ws' acc' accBits' (totalBits + w) bits' →
      wp Γ Q X (k ws' acc' accBits') m) :
    wp Γ Q X (pushLeafWord64 w leaf ws acc accBits k) m := by
  rcases hS with ⟨hAccLt, hTot, hAccHi, hWs, hAccBits⟩
  unfold pushLeafWord64
  by_cases hw0 : w = 0
  · subst hw0
    simp only [beq_self_eq_true, ↓reduceIte]
    apply hk
    refine ⟨hAccLt, by omega, hAccHi, ?_, ?_⟩
    · intro i hi
      rw [hAgree i (by omega)]
      exact hWs i hi
    · intro j hj
      rw [hAgree (64 * ws.length + j) (by omega)]
      exact hAccBits j hj
  · have hwNe : (w == 0) = false := beq_false_of_ne hw0
    simp only [hwNe, Bool.false_eq_true, ↓reduceIte]
    by_cases ha0 : accBits = 0
    · simp only [ha0, beq_self_eq_true, ↓reduceIte]
      rw [ha0, Nat.add_zero] at hTot
      by_cases hw64 : w ≥ 64
      · have hwEq : w = 64 := by omega
        subst hwEq
        simp only [ge_iff_le, Nat.le_refl, ↓reduceIte]
        apply hk
        refine ⟨by omega, by
          simp only [List.length_append, List.length_singleton]; omega, fun j _ => by
          simp, ?_, fun j hj => by omega⟩
        intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < 64 * ws.length
        · rw [words64GetLsb_append_left ws [leaf] hlt, hAgree i (by omega)]
          exact hWs i hlt
        · have hge : 64 * ws.length ≤ i := Nat.le_of_not_lt hlt
          rw [words64GetLsb_append_singleton_right ws leaf hge hi]
          have := hLeafBits (i - 64 * ws.length) (by omega)
          rwa [show totalBits + (i - 64 * ws.length) = i by omega] at this
      · have hwLt : w < 64 := by omega
        simp only [show ¬(w ≥ 64) by omega, ↓reduceIte]
        apply hk
        refine ⟨hwLt, by omega, hLeafHi, ?_, ?_⟩
        · intro i hi
          rw [hAgree i (by omega)]
          exact hWs i hi
        · intro j hj
          have := hLeafBits j hj
          rwa [← hTot]
    · have haNe : (accBits == 0) = false := beq_false_of_ne ha0
      simp only [haNe, Bool.false_eq_true, ↓reduceIte]
      dsimp only [wp, Op.wp, op2, vals]
      rw [OpCode.wp_shl]
      simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
      rw [OpCode.wp_or]
      dsimp only [lift2, Arg.val_var]
      have hModAcc : (BitVec.ofNat 64 accBits).toNat % 64 = accBits := by
        rw [BitVec.toNat_ofNat]
        simp [Nat.mod_eq_of_lt hAccLt]
      have hLoGet : ∀ j, j < 64 →
          (acc.val ||| leaf.val <<< ((BitVec.ofNat 64 accBits).toNat % 64)).getLsbD j =
            if j < accBits then bits' (64 * ws.length + j)
            else if j - accBits < w then bits' (64 * ws.length + j) else false := by
        intro j hj64
        rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hModAcc]
        by_cases hjAcc : j < accBits
        · simp [hjAcc, hAgree (64 * ws.length + j) (by omega), hAccBits j hjAcc]
        · rw [hAccHi j (by omega)]
          simp [hjAcc, hj64]
          by_cases hjw : j - accBits < w
          · simp only [hjw]
            have := hLeafBits (j - accBits) hjw
            rwa [show totalBits + (j - accBits) = 64 * ws.length + j by omega] at this
          · simp only [hjw]
            exact hLeafHi (j - accBits) (by omega)
      by_cases hSumLt : accBits + w < 64
      · simp only [hSumLt, ↓reduceIte]
        apply hk
        refine ⟨hSumLt, by omega, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hj64 : j < 64
          · dsimp only [Arg.val_var]
            rw [hLoGet j hj64]
            simp [show ¬(j < accBits) by omega, show ¬(j - accBits < w) by omega]
          · exact BitVec.getLsbD_of_ge _ j (by omega)
        · intro i hi
          rw [hAgree i (by omega)]
          exact hWs i hi
        · intro j hj
          dsimp only [Arg.val_var]
          rw [hLoGet j (by omega)]
          by_cases hjAcc : j < accBits <;> simp [hjAcc, show j - accBits < w by omega]
      · simp only [hSumLt, ↓reduceIte]
        by_cases hSumEq : accBits + w = 64
        · simp only [hSumEq, beq_self_eq_true, ↓reduceIte]
          apply hk
          refine ⟨by omega, by
            simp only [List.length_append, List.length_singleton]; omega, fun j _ => by
            simp, ?_, fun j hj => by omega⟩
          intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlt : i < 64 * ws.length
          · rw [words64GetLsb_append_left ws [.var _] hlt, hAgree i (by omega)]
            exact hWs i hlt
          · have hge : 64 * ws.length ≤ i := Nat.le_of_not_lt hlt
            rw [words64GetLsb_append_singleton_right ws (.var _) hge hi]
            dsimp only [Arg.val_var]
            have hj64 : i - 64 * ws.length < 64 := by omega
            rw [hLoGet (i - 64 * ws.length) hj64]
            by_cases hjAcc : i - 64 * ws.length < accBits
            · simp [hjAcc, show 64 * ws.length + (i - 64 * ws.length) = i by omega]
            · simp [hjAcc, show i - 64 * ws.length - accBits < w by omega,
                show 64 * ws.length + (i - 64 * ws.length) = i by omega]
        · have hSumGt : 64 < accBits + w := by omega
          have hSumNe : (accBits + w == 64) = false := beq_false_of_ne hSumEq
          simp only [hSumNe, Bool.false_eq_true, ↓reduceIte]
          dsimp only [wp, Op.wp, op2, vals]
          rw [OpCode.wp_lshr]
          simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
          have hModSub : (BitVec.ofNat 64 (64 - accBits)).toNat % 64 = 64 - accBits := by
            rw [BitVec.toNat_ofNat]
            have haPos : 0 < accBits := Nat.pos_of_ne_zero ha0
            simp [Nat.mod_eq_of_lt (by omega : 64 - accBits < 64)]
          apply hk
          refine ⟨by omega, by
            simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_⟩
          · intro j hj
            dsimp only [Arg.val_var]
            rw [BitVec.getLsbD_ushiftRight, hModSub]
            by_cases hhi64 : 64 - accBits + j < 64
            · exact hLeafHi (64 - accBits + j) (by omega)
            · exact BitVec.getLsbD_of_ge leaf.val _ (by omega)
          · intro i hi
            simp only [List.length_append, List.length_singleton] at hi
            by_cases hlt : i < 64 * ws.length
            · rw [words64GetLsb_append_left ws [.var _] hlt, hAgree i (by omega)]
              exact hWs i hlt
            · have hge : 64 * ws.length ≤ i := Nat.le_of_not_lt hlt
              rw [words64GetLsb_append_singleton_right ws (.var _) hge hi]
              dsimp only [Arg.val_var]
              have hj64 : i - 64 * ws.length < 64 := by omega
              rw [hLoGet (i - 64 * ws.length) hj64]
              by_cases hjAcc : i - 64 * ws.length < accBits
              · simp [hjAcc, show 64 * ws.length + (i - 64 * ws.length) = i by omega]
              · simp [hjAcc, show i - 64 * ws.length - accBits < w by omega,
                  show 64 * ws.length + (i - 64 * ws.length) = i by omega]
          · intro j hj
            dsimp only [Arg.val_var]
            rw [BitVec.getLsbD_ushiftRight, hModSub]
            have h1 := hLeafBits (64 - accBits + j) (by omega)
            simp only [List.length_append, List.length_singleton]
            rwa [show totalBits + (64 - accBits + j) = 64 * (ws.length + 1) + j by omega] at h1

theorem getLsbD_eq_rec {a b : Nat} (h : a = b) (x : BitVec a) (i : Nat) :
    (h ▸ x).getLsbD i = x.getLsbD i := by
  subst h; rfl

private theorem packLeavesToWords64_go_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (u : Ty), target.supportsTy u = true →
    ∀ {fx : Tup (Arg Val) (target.leafTys u)} {v : Val u}
      {ws : List (Arg Val i64)} {acc : Arg Val i64} {accBits totalBits : Nat}
      {bits bits' : Nat → Bool},
      valsTup fx = leafVals target u v →
      Words64Stream ws acc accBits totalBits bits →
      (∀ i, i < totalBits → bits' i = bits i) →
      (∀ j, j < u.size → (toBits u v).getLsbD j = bits' (totalBits + j)) →
      ∀ {k : List (Arg Val i64) → Arg Val i64 → Nat → Expr Val Cont rs} {m : Mem 64},
        (∀ ws' acc' accBits',
          Words64Stream ws' acc' accBits' (totalBits + u.size) bits' →
          wp Γ Q X (k ws' acc' accBits') m) →
        wp Γ Q X (packLeavesToWords64.go target u fx ws acc accBits k) m
  | .bool, _, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m, hk => by
    dsimp only [LegalTarget.leafTys] at fx hFx
    rcases fx with ⟨b, ⟨⟩⟩
    dsimp only [packLeavesToWords64.go]
    dsimp only [wp, Op.wp, op1, vals]
    rw [OpCode.wp_ofBool]
    dsimp only [Arg.val_var]
    have hb : b.val = v := by
      rw [valsTup_single] at hFx
      dsimp only [leafVals] at hFx
      exact congrArg Prod.fst hFx
    apply pushLeafWord64_wp (by omega) hS
    · intro j hj
      dsimp only [Arg.val_var]
      rw [hb, BitVec.getLsbD_ofNat]
      cases v <;> simp [Bool.toNat]
      intro _
      exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega : j ≠ 0))
    · exact hAgree
    · intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have h0 := hNew 0 (by simp [Ty.size])
      dsimp only [Arg.val_var]
      rw [Nat.add_zero] at h0 ⊢
      rw [← h0, hb]
      cases v <;> simp [toBits, Bool.toNat]
    · simpa [Ty.size] using hk
  | .bits n, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m,
      hk => by
    dsimp only [LegalTarget.leafTys] at fx hFx
    rcases fx with ⟨x, ⟨⟩⟩
    dsimp only [packLeavesToWords64.go]
    have hx : x.val = BitVec.setWidth (target.widenWidth n) v := by
      rw [valsTup_single] at hFx
      dsimp only [leafVals] at hFx
      exact congrArg Prod.fst hFx
    have hn64 : n ≤ 64 := (supportsTy_bits_iff.mp hSup).2
    have hnW : n ≤ target.widenWidth n := le_widenWidth_of_supports hSup
    have hWle64 := widenWidth_le_64_of_supports hv hSup
    by_cases hn0 : n = 0
    · subst hn0
      simp only [beq_self_eq_true, ↓reduceIte]
      apply hk
      rcases hS with ⟨hLt, hTot, hAccHi, hWs, hAcc⟩
      refine ⟨hLt, hTot, hAccHi, ?_, ?_⟩
      · intro i hi; rw [hAgree i (by omega)]; exact hWs i hi
      · intro j hj; rw [hAgree (64 * ws.length + j) (by omega)]; exact hAcc j hj
    · have hnNe : (n == 0) = false := beq_false_of_ne hn0
      simp only [hnNe, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left hn64]
      by_cases hwn64 : target.widenWidth n = 64
      · simp only [hwn64, ↓reduceDIte]
        have hCast : (castArgBits hwn64 x).val = BitVec.setWidth 64 v := by
          rw [val_castArgBits, hx]
          apply BitVec.eq_of_getLsbD_eq; intro j hj64
          rw [getLsbD_eq_rec, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
          by_cases hjn : j < n
          · simp [hj64, show j < target.widenWidth n by omega]
          · simp [BitVec.getLsbD_of_ge v j (by omega)]
        apply pushLeafWord64_wp hn64 hS
        · intro j hj
          rw [hCast, BitVec.getLsbD_setWidth]
          simp [BitVec.getLsbD_of_ge v j hj]
        · exact hAgree
        · intro j hj
          have h0 := hNew j (by simp [Ty.size]; exact hj)
          rw [← h0, hCast, BitVec.getLsbD_setWidth]
          simp [toBits, show j < 64 by omega]
        · simpa [Ty.size] using hk
      · have hwnLt64 : target.widenWidth n < 64 := by omega
        simp only [hwn64, hwnLt64, ↓reduceDIte, ↓reduceIte]
        dsimp only [wp, Op.wp, op1, vals]
        rw [OpCode.wp_zext]
        refine ⟨Nat.le_of_lt hwnLt64, ?_⟩
        dsimp only [Arg.val_var]
        have hZext : BitVec.setWidth 64 x.val = BitVec.setWidth 64 v := by
          apply BitVec.eq_of_getLsbD_eq
          intro j hj64
          rw [hx, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
          by_cases hjn : j < n
          · simp [hj64, show j < target.widenWidth n by omega]
          · simp [BitVec.getLsbD_of_ge v j (by omega)]
        apply pushLeafWord64_wp hn64 hS
        · intro j hj
          dsimp only [Arg.val_var]
          rw [hZext, BitVec.getLsbD_setWidth]
          simp [BitVec.getLsbD_of_ge v j hj]
        · exact hAgree
        · intro j hj
          have h0 := hNew j (by simp [Ty.size]; exact hj)
          dsimp only [Arg.val_var]
          rw [← h0, hZext, BitVec.getLsbD_setWidth]
          simp [toBits, show j < 64 by omega]
        · simpa [Ty.size] using hk
  | .float f, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m,
      hk => by
    dsimp only [LegalTarget.leafTys] at fx hFx
    rcases fx with ⟨x, ⟨⟩⟩
    dsimp only [packLeavesToWords64.go]
    have hx : x.val = v := by
      rw [valsTup_single] at hFx
      dsimp only [leafVals] at hFx
      exact congrArg Prod.fst hFx
    have hSupAnd : f ∈ target.floatFmts ∧ f.width ≤ 64 := by
      simpa [LegalTarget.supportsTy] using hSup
    have hFwSpec := valid_bitWidth_spec hv (valid_float_spec hv hSupAnd.1).1
    have hFwLe64 : f.width ≤ 64 := hFwSpec.2.2
    dsimp only [wp, Op.wp, op1, vals]
    rw [op1_bitcast_wp_top]
    dsimp only [toBits, ofBits, Arg.val_var]
    by_cases hfw64 : f.width = 64
    · simp only [hfw64, ↓reduceDIte]
      apply pushLeafWord64_wp (by omega) hS
      · intro j hj
        rw [val_castArgBits]
        exact BitVec.getLsbD_of_ge _ j (by omega)
      · exact hAgree
      · intro j hj
        have h0 := hNew j (by simp [Ty.size, hfw64]; exact hj)
        rw [← h0, val_castArgBits, getLsbD_eq_rec]
        dsimp only [Arg.val_var]
        rw [BitVec.getLsbD_cast]
        simp [toBits, hx]
      · simpa [hfw64] using hk
    · have hfwLt64 : f.width < 64 := by omega
      simp only [hfw64, hfwLt64, ↓reduceDIte, ↓reduceIte]
      dsimp only [wp, Op.wp, op1, vals]
      rw [OpCode.wp_zext]
      refine ⟨Nat.le_of_lt hfwLt64, ?_⟩
      dsimp only [Arg.val_var]
      apply pushLeafWord64_wp hFwLe64 hS
      · intro j hj
        dsimp only [Arg.val_var]
        rw [BitVec.getLsbD_setWidth]
        simp [BitVec.getLsbD_of_ge _ j hj]
      · exact hAgree
      · intro j hj
        have h0 := hNew j (by simp [Ty.size]; exact hj)
        dsimp only [Arg.val_var]
        rw [← h0, BitVec.getLsbD_setWidth, BitVec.getLsbD_cast]
        simp [toBits, hx, show j < 64 by omega]
      · simpa [Ty.size] using hk
  | .pair a b, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m,
      hk => by
    dsimp only [packLeavesToWords64.go]
    have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
      simpa [LegalTarget.supportsTy] using hSup
    dsimp only [LegalTarget.leafTys] at fx hFx
    have hSplitFx := tupSplit_valsTup (fx := fx)
    rw [hFx, leafVals_pair, tupSplit_tupAppend] at hSplitFx
    have hFst : valsTup (tupSplit fx).1 = leafVals target a v.1 :=
      (congrArg Prod.fst hSplitFx).symm
    have hSnd : valsTup (tupSplit fx).2 = leafVals target b v.2 :=
      (congrArg Prod.snd hSplitFx).symm
    apply packLeavesToWords64_go_wp target hv a hSupPair.1 hFst hS hAgree
    · intro j hj
      have h0 := hNew j (by simp [Ty.size]; omega)
      rw [← h0]
      simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hj]
    · intro ws1 acc1 bits1 hS1
      apply packLeavesToWords64_go_wp target hv b hSupPair.2 hSnd hS1 (fun _ _ => rfl)
      · intro j hj
        have h0 := hNew (a.size + j) (by simp [Ty.size]; omega)
        rw [← Nat.add_assoc] at h0
        rw [← h0]
        simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, show ¬(a.size + j < a.size) by
          omega]
      · intro ws2 acc2 bits2 hS2
        exact hk ws2 acc2 bits2 (by simpa [Ty.size, Nat.add_assoc] using hS2)

theorem packLeavesToWords64_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (ht : target.supportsTy t = true)
    {fx : Tup (Arg Val) (target.leafTys t)} {x : Val t}
    (hFx : valsTup fx = leafVals target t x)
    {k : List (Arg Val i64) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ words : List (Arg Val i64),
      (∀ i, i < t.size → words64GetLsb words i = (toBits t x).getLsbD i) →
      words.length = (t.size + 63) / 64 →
      (t.size % 64 = 0 → words.length = t.size / 64) →
      wp Γ Q X (k words) m) :
    wp Γ Q X (packLeavesToWords64 target t fx k) m := by
  unfold packLeavesToWords64
  have hS0 : Words64Stream ([] : List (Arg Val i64)) (.imm 0#64) 0 0 (fun _ => false) :=
    ⟨by omega, by simp, fun j _ => by simp, fun i hi => by simp at hi, fun j hj => by omega⟩
  apply packLeavesToWords64_go_wp target hv t ht hFx hS0
    (bits' := fun i => if i < t.size then (toBits t x).getLsbD i else false) (fun i hi => by omega)
  · intro j hj; simp [hj]
  · intro ws acc accBits hS
    have ⟨hBits, hLen, hDiv⟩ := Words64Stream.finish hS
    by_cases h0 : accBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hBits hLen hDiv ⊢
      apply hk ws
      · intro i hi
        have := hBits i (by omega)
        simpa [hi] using this
      · simpa using hLen
      · simpa using hDiv
    · have hne : (accBits == 0) = false := beq_false_of_ne h0
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hBits hLen hDiv ⊢
      apply hk (ws ++ [acc])
      · intro i hi
        have := hBits i (by omega)
        simpa [hi] using this
      · simpa using hLen
      · simpa using hDiv

theorem packLeavesToWords64_wp_all (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (ht : target.supportsTy t = true)
    {fx : Tup (Arg Val) (target.leafTys t)} {x : Val t}
    (hFx : valsTup fx = leafVals target t x)
    {k : List (Arg Val i64) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ words : List (Arg Val i64),
      (∀ i, words64GetLsb words i = if i < t.size then (toBits t x).getLsbD i else false) →
      words.length = (t.size + 63) / 64 →
      (t.size % 64 = 0 → words.length = t.size / 64) →
      wp Γ Q X (k words) m) :
    wp Γ Q X (packLeavesToWords64 target t fx k) m := by
  unfold packLeavesToWords64
  have hS0 : Words64Stream ([] : List (Arg Val i64)) (.imm 0#64) 0 0 (fun _ => false) :=
    ⟨by omega, by simp, fun j _ => by simp, fun i hi => by simp at hi, fun j hj => by omega⟩
  apply packLeavesToWords64_go_wp target hv t ht hFx hS0
    (bits' := fun i => if i < t.size then (toBits t x).getLsbD i else false) (fun i hi => by omega)
  · intro j hj; simp [hj]
  · intro ws acc accBits hS
    have ⟨hBits, hLen, hDiv⟩ := Words64Stream.finish_all hS
    by_cases h0 : accBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hBits hLen hDiv ⊢
      apply hk ws
      · intro i
        have := hBits i
        by_cases hi : i < t.size
        · simpa [hi] using this
        · simpa [hi] using this
      · simpa using hLen
      · simpa using hDiv
    · have hne : (accBits == 0) = false := beq_false_of_ne h0
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hBits hLen hDiv ⊢
      apply hk (ws ++ [acc])
      · intro i
        have := hBits i
        by_cases hi : i < t.size
        · simpa [hi] using this
        · simpa [hi] using this
      · simpa using hLen
      · simpa using hDiv

theorem extractBitsFromWords64_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {words : List (Arg Val i64)} {off w : Nat} (hw : w ≤ 64)
    {bits : Nat → Bool}
    (hW : ∀ i, i < w → words64GetLsb words (off + i) = bits i)
    {k : Arg Val i64 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ raw : Arg Val i64,
      (∀ i, raw.val.getLsbD i = (if i < w then bits i else false)) →
      wp Γ Q X (k raw) m) :
    wp Γ Q X (extractBitsFromWords64 words off w k) m := by
  unfold extractBitsFromWords64
  by_cases hw0 : w = 0
  · subst hw0
    simp only [beq_self_eq_true, ↓reduceIte]
    apply hk
    intro i; simp
  · have hwNe : (w == 0) = false := beq_false_of_ne hw0
    simp only [hwNe, Bool.false_eq_true, ↓reduceIte]
    have hBitLt : off % 64 < 64 := Nat.mod_lt off (by omega)
    have hOffEq : off = 64 * (off / 64) + off % 64 := by
      have := Nat.div_add_mod off 64
      omega
    have hLoStep :
        ∀ (cont : Arg Val i64 → Expr Val Cont rs),
        (∀ lo : Arg Val i64,
          (∀ j, j < 64 - off % 64 → lo.val.getLsbD j = words64GetLsb words (off + j)) →
          (∀ j, 64 - off % 64 ≤ j → lo.val.getLsbD j = false) →
          wp Γ Q X (cont lo) m) →
        wp Γ Q X (if (off % 64 == 0) = true then cont (words.getD (off / 64) (.imm 0#64))
          else Expr.let_
            (op2 (.lshr i64) (words.getD (off / 64) (.imm 0#64))
            (.imm (BitVec.ofNat 64 (off % 64))))
            fun r => cont (.var r.1)) m := by
      intro cont hcont
      by_cases hb0 : off % 64 = 0
      · simp only [hb0, beq_self_eq_true, ↓reduceIte]
        apply hcont
        · intro j hj
          have hdiv : (off + j) / 64 = off / 64 := by omega
          have hmod : (off + j) % 64 = j := by omega
          simp [words64GetLsb, hdiv, hmod]
        · intro j hj
          exact BitVec.getLsbD_of_ge _ j (by omega)
      · have hbNe : (off % 64 == 0) = false := beq_false_of_ne hb0
        simp only [hbNe, Bool.false_eq_true, ↓reduceIte, wp, Op.wp, op2, vals]
        rw [OpCode.wp_lshr]
        simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
        have hModBo : (BitVec.ofNat 64 (off % 64)).toNat % 64 = off % 64 := by
          rw [BitVec.toNat_ofNat]
          simp [Nat.mod_eq_of_lt hBitLt]
        apply hcont
        · intro j hj
          dsimp only [Arg.val_var]
          rw [BitVec.getLsbD_ushiftRight, hModBo]
          have hdiv : (off + j) / 64 = off / 64 := by omega
          have hmod : (off + j) % 64 = off % 64 + j := by omega
          simp [words64GetLsb, hdiv, hmod]
        · intro j hj
          dsimp only [Arg.val_var]
          rw [BitVec.getLsbD_ushiftRight, hModBo]
          exact BitVec.getLsbD_of_ge _ _ (by omega)
    apply hLoStep (fun lo =>
      if off % 64 + w ≤ 64 then emitMaskToN w 64 lo k
      else
        Expr.let_
          (op2 (.shl i64) (words.getD (off / 64 + 1) (.imm 0#64))
          (.imm (BitVec.ofNat 64 (64 - off % 64))))
          fun h => Expr.let_ (op2 (.or i64) lo (.var h.1)) fun lo' =>
            emitMaskToN w 64 (.var lo'.1) k)
    intro lo hLoGood hLoHi
    by_cases hFit : off % 64 + w ≤ 64
    · simp only [hFit, ↓reduceIte]
      apply emitMaskToN_wp hw rfl
      intro r hr
      apply hk
      intro i
      rw [hr, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
      by_cases hiw : i < w
      · have hi64 : i < 64 := by omega
        have hj : i < 64 - off % 64 := by omega
        rw [hLoGood i hj, hW i hiw]
        simp [hi64, hiw]
      · simp [hiw]
    · have hNotFit : ¬(off % 64 + w ≤ 64) := hFit
      have hBPos : 0 < off % 64 := by omega
      simp only [hNotFit, ↓reduceIte, wp, Op.wp, op2, vals]
      rw [OpCode.wp_shl]
      simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
      rw [OpCode.wp_or]
      dsimp only [lift2, Arg.val_var]
      have hModSub : (BitVec.ofNat 64 (64 - off % 64)).toNat % 64 = 64 - off % 64 := by
        rw [BitVec.toNat_ofNat]
        simp [Nat.mod_eq_of_lt (by omega : 64 - off % 64 < 64)]
      apply emitMaskToN_wp hw rfl
      intro r hr
      apply hk
      intro i
      rw [hr, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
      by_cases hiw : i < w
      · have hi64 : i < 64 := by omega
        simp only [hi64, hiw, decide_true, Bool.true_and]
        dsimp only [Arg.val_var]
        rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hModSub]
        by_cases hilt : i < 64 - off % 64
        · simp [hilt, hLoGood i hilt, hW i hiw]
        · have hfLo : lo.val.getLsbD i = false := hLoHi i (by omega)
          have ht1 : (decide (i < 64) && !decide (i < 64 - off % 64)) = true := by simp [hi64, hilt]
          simp only [hfLo, ht1, Bool.true_and, Bool.false_or]
          have hdiv : (off + i) / 64 = off / 64 + 1 := by omega
          have hmod : (off + i) % 64 = i - (64 - off % 64) := by omega
          have hw1 :
            (words.getD (off / 64 + 1) (.imm 0#64)).val.getLsbD (i - (64 - off % 64)) = bits i := by
            have := hW i hiw
            simpa [words64GetLsb, hdiv, hmod] using this
          exact hw1
      · simp [hiw]

theorem unpackWords64ToLeaves_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (u : Ty), target.supportsTy u = true →
    ∀ {words : List (Arg Val i64)} {off : Nat} {v : Val u},
      (∀ i, i < u.size → words64GetLsb words (off + i) = (toBits u v).getLsbD i) →
      ∀ {k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs} {m : Mem 64},
        (∀ fres : Tup (Arg Val) (target.leafTys u),
          valsTup fres = leafVals target u v →
          wp Γ Q X (k fres) m) →
        wp Γ Q X (unpackWords64ToLeaves target words off u k) m
  | .bool, _, words, off, v, hW, k, m, hk => by
    dsimp only [unpackWords64ToLeaves]
    apply extractBitsFromWords64_wp (by omega) (fun i hi => hW i (by simp [Ty.size]; omega))
    intro raw hRaw
    dsimp only [wp, Op.wp, op2, vals]
    rw [OpCode.wp_cmp]
    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, Arg.val_imm,
      cast_eq]
    have hEqVal : raw.val = if v then 1#64 else 0#64 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi64
      rw [hRaw i]
      by_cases hi0 : i = 0
      · subst hi0
        cases v <;> simp [toBits]
      · have hi1 : ¬(i < 1) := by omega
        cases v <;> simp [hi1, hi0]
    apply hk (.var _, ())
    dsimp only [LegalTarget.leafTys] at *
    rw [valsTup_single]
    dsimp only [leafVals, Arg.val_var]
    rw [hEqVal]
    cases v <;> decide
  | .bits n, hSup, words, off, v, hW, k, m, hk => by
    dsimp only [unpackWords64ToLeaves]
    have hn64 : n ≤ 64 := (supportsTy_bits_iff.mp hSup).2
    have hnW : n ≤ target.widenWidth n := le_widenWidth_of_supports hSup
    have hWle64 := widenWidth_le_64_of_supports hv hSup
    by_cases hn0 : n = 0
    · subst hn0
      simp only [beq_self_eq_true, ↓reduceIte]
      apply hk (.imm 0#(target.widenWidth 0), ())
      have hv0 : v = 0#0 := Subsingleton.elim v 0#0
      subst hv0
      simp only [LegalTarget.leafTys, leafVals]
      apply Prod.ext _ rfl
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp
    · have hnNe : (n == 0) = false := beq_false_of_ne hn0
      simp only [hnNe, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left hn64]
      apply extractBitsFromWords64_wp hn64 (fun i hi => hW i (by simp [Ty.size]; exact hi))
      intro raw hRaw
      have hRawEq : raw.val = BitVec.setWidth 64 v := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi64
        rw [hRaw i, BitVec.getLsbD_setWidth]
        by_cases hin : i < n
        · simp [hin, hi64, toBits]
        · simp only [hin, ↓reduceIte, BitVec.getLsbD_of_ge v i (by omega), Bool.and_false]
      by_cases hwn64 : target.widenWidth n = 64
      · simp only [hwn64, ↓reduceDIte]
        apply hk (castArgBits hwn64.symm raw, ())
        dsimp only [LegalTarget.leafTys] at *
        rw [valsTup_single]
        dsimp only [leafVals]
        congr 1
        rw [val_castArgBits, hRawEq]
        apply BitVec.eq_of_getLsbD_eq
        intro i hiW
        rw [getLsbD_eq_rec, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
        simp [hiW, show i < 64 by omega]
      · have hwnLt64 : target.widenWidth n < 64 := by omega
        simp only [hwn64, hwnLt64, ↓reduceDIte, ↓reduceIte]
        dsimp only [wp, Op.wp, op1, vals]
        rw [OpCode.wp_trunc]
        refine ⟨Nat.le_of_lt hwnLt64, ?_⟩
        apply hk (.var _, ())
        dsimp only [LegalTarget.leafTys] at *
        rw [valsTup_single]
        dsimp only [leafVals, Arg.val_var]
        rw [hRawEq]
        congr 1
        apply BitVec.eq_of_getLsbD_eq
        intro i hiW
        rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
        simp [hiW, show i < 64 by omega]
  | .float f, hSup, words, off, v, hW, k, m, hk => by
    dsimp only [unpackWords64ToLeaves]
    have hSupAnd : f ∈ target.floatFmts ∧ f.width ≤ 64 := by
      simpa [LegalTarget.supportsTy] using hSup
    have hFwSpec := valid_bitWidth_spec hv (valid_float_spec hv hSupAnd.1).1
    have hFwLe64 : f.width ≤ 64 := hFwSpec.2.2
    simp only [Nat.min_eq_left hFwLe64]
    apply extractBitsFromWords64_wp hFwLe64 (fun i hi => hW i (by simp [Ty.size]; exact hi))
    intro raw hRaw
    have hRawEq : raw.val = BitVec.setWidth 64 v := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi64
      rw [hRaw i, BitVec.getLsbD_setWidth]
      by_cases hif : i < f.width
      · simp [hif, hi64, toBits]
      · simp only [hif, ↓reduceIte, BitVec.getLsbD_of_ge v i (by omega), Bool.and_false]
    by_cases hfw64 : f.width = 64
    · simp only [hfw64, ↓reduceDIte]
      dsimp only [wp, Op.wp, op1, vals]
      rw [op1_bitcast_wp_top]
      dsimp only [toBits, ofBits]
      apply hk (.var _, ())
      dsimp only [LegalTarget.leafTys] at *
      rw [valsTup_single]
      dsimp only [leafVals, Arg.val_var]
      rw [hRawEq]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hi64 : i < 64 := by simpa [Ty.size, hfw64] using hi
      rw [BitVec.getLsbD_cast, BitVec.getLsbD_setWidth]
      simp [hi64]
    · have hfwLt64 : f.width < 64 := by omega
      simp only [hfw64, hfwLt64, ↓reduceDIte, ↓reduceIte]
      dsimp only [wp, Op.wp, op1, vals]
      rw [OpCode.wp_trunc]
      refine ⟨Nat.le_of_lt hfwLt64, ?_⟩
      rw [op1_bitcast_wp_top]
      dsimp only [toBits, ofBits, Arg.val_var]
      apply hk (.var _, ())
      dsimp only [LegalTarget.leafTys] at *
      rw [valsTup_single]
      dsimp only [leafVals, Arg.val_var]
      rw [hRawEq]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hif : i < f.width := by simpa [Ty.size] using hi
      rw [BitVec.getLsbD_cast, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
      simp [hif, show i < 64 by omega]
  | .pair a b, hSup, words, off, v, hW, k, m, hk => by
    dsimp only [unpackWords64ToLeaves]
    have hSupPair : target.supportsTy a = true ∧ target.supportsTy b = true := by
      simpa [LegalTarget.supportsTy] using hSup
    apply unpackWords64ToLeaves_wp target hv a hSupPair.1 (v := v.1)
    · intro i hi
      have h0 := hW i (by simp [Ty.size]; omega)
      rw [h0]
      simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hi]
    · intro fa hFa
      apply unpackWords64ToLeaves_wp target hv b hSupPair.2 (v := v.2)
      · intro i hi
        have h0 := hW (a.size + i) (by simp [Ty.size]; omega)
        rw [← Nat.add_assoc] at h0
        rw [h0]
        simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, show ¬(a.size + i < a.size) by
          omega]
      · intro fb hFb
        apply hk (tupAppend fa fb)
        dsimp only [LegalTarget.leafTys]
        rw [valsTup_tupAppend, hFa, hFb, leafVals_pair]

private theorem foldl_bvOfLanes_getLsbD (w c : Nat) (hc : 0 < c) (f : Nat → BitVec c) :
    ∀ (n : Nat) (init : BitVec w) (k : Nat),
      k < w →
      ((List.range n).foldl (fun acc i => acc ||| BitVec.setWidth w (f i) <<< (c * i)) init).getLsbD
        k =
        (init.getLsbD k || (if k / c < n then (f (k / c)).getLsbD (k % c) else false))
  | 0, init, k, _ => by simp
  | n + 1, init, k, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [BitVec.getLsbD_or, foldl_bvOfLanes_getLsbD w c hc f n init k hk]
    rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    simp only [hk, decide_true, Bool.true_and]
    by_cases hkc : k / c < n
    · have hk_lt : k < c * n := by rw [Nat.mul_comm]; exact (Nat.div_lt_iff_lt_mul hc).mp hkc
      have hlt_dec : decide (k < c * n) = true := decide_eq_true hk_lt
      have hkc1 : k / c < n + 1 := by omega
      simp [hkc, hkc1, hlt_dec]
    · by_cases heq : k / c = n
      · have hge : c * n ≤ k := by
          have := Nat.div_add_mod k c
          rw [heq] at this; omega
        have hsub : k - c * n = k % c := by
          have := Nat.div_add_mod k c
          rw [heq] at this; omega
        have hnot : decide (k < c * n) = false := decide_eq_false (by omega)
        have hmc : decide (k % c < w) = true :=
          decide_eq_true (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk)
        rw [hsub]
        simp [hnot, hmc, heq]
      · have hgt : n + 1 ≤ k / c := by omega
        have hnot1 : ¬(k / c < n + 1) := by omega
        have hdiff : c * (n + 1) ≤ k := by
          rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hc).mp hgt
        have hdiff' : c * n + c ≤ k := by simpa [Nat.mul_succ] using hdiff
        have hf : (f n).getLsbD (k - c * n) = false :=
          BitVec.getLsbD_of_ge (f n) (k - c * n) (by omega)
        simp [hkc, hnot1, hf]

theorem getLsbD_bvOfLanes {w c : Nat} (hc : 0 < c) (f : Nat → BitVec c) {k : Nat}
    (hk : k < w) :
    (bvOfLanes w c f).getLsbD k =
      (if k / c < w / c then (f (k / c)).getLsbD (k % c) else false) := by
  unfold bvOfLanes
  rw [foldl_bvOfLanes_getLsbD w c hc f (w / c) (0#w) k hk]
  simp

theorem getLsbD_bvLane {w : Nat} (c i : Nat) (v : BitVec w) (j : Nat) :
    (bvLane c i v).getLsbD j = (decide (j < c) && v.getLsbD (c * i + j)) := by
  unfold bvLane
  exact BitVec.getLsbD_extractLsb' (c * i) c v j

private theorem bvLane8_bvLane32 (v : BitVec 128) (q r : Nat) (hr : r < 4) :
    bvLane 8 r (bvLane 32 q v) = bvLane 8 (4 * q + r) v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi8
  rw [getLsbD_bvLane, getLsbD_bvLane, getLsbD_bvLane]
  have hi32 : 8 * r + i < 32 := by omega
  simp only [hi8, decide_true, Bool.true_and, hi32]
  rw [show 32 * q + (8 * r + i) = 8 * (4 * q + r) + i by omega]

theorem words2ToDwords4_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w0 w1 : Arg Val i64} {v : BitVec 128}
    (hw0 : w0.val = BitVec.extractLsb' 0 64 v)
    (hw1 : w1.val = BitVec.extractLsb' 64 64 v)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ d0 d1 d2 d3 : Arg Val i32,
      d0.val = bvLane 32 0 v →
      d1.val = bvLane 32 1 v →
      d2.val = bvLane 32 2 v →
      d3.val = bvLane 32 3 v →
      wp Γ Q X (k d0 d1 d2 d3) m) :
    wp Γ Q X (words2ToDwords4 w0 w1 k) m := by
  unfold words2ToDwords4
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  apply hk
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, hw0, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
    simp [hi, show i < 64 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hw0, BitVec.getLsbD_extractLsb',
      getLsbD_bvLane]
    have hmod : (32#64).toNat % 64 = 32 := by decide
    rw [hmod]
    simp [hi, show 32 + i < 64 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, hw1, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
    simp [hi, show i < 64 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hw1, BitVec.getLsbD_extractLsb',
      getLsbD_bvLane]
    have hmod : (32#64).toNat % 64 = 32 := by decide
    rw [hmod]
    simp [hi, show 32 + i < 64 by omega, show 64 + (32 + i) = 32 * 3 + i by omega]

theorem dwords4ToWords2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {d0 d1 d2 d3 : Arg Val i32} {v : BitVec 128}
    (hd0 : d0.val = bvLane 32 0 v)
    (hd1 : d1.val = bvLane 32 1 v)
    (hd2 : d2.val = bvLane 32 2 v)
    (hd3 : d3.val = bvLane 32 3 v)
    {k : Arg Val i64 → Arg Val i64 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ w0 w1 : Arg Val i64,
      w0.val = BitVec.extractLsb' 0 64 v →
      w1.val = BitVec.extractLsb' 64 64 v →
      wp Γ Q X (k w0 w1) m) :
    wp Γ Q X (dwords4ToWords2 d0 d1 d2 d3 k) m := by
  unfold dwords4ToWords2
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl];
    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  have hmod : (32#64).toNat % 64 = 32 := by decide
  apply hk
  · apply BitVec.eq_of_getLsbD_eq; intro i hi64
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hmod, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hd0, hd1, getLsbD_bvLane,
          getLsbD_bvLane]
    by_cases hi32 : i < 32
    · simp [hi64, hi32]
    · have ht32 : i - 32 < 32 := by omega
      have ht64 : i - 32 < 64 := by omega
      simp [hi64, hi32, ht32, ht64, show 32 + (i - 32) = i by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi64
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hmod, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hd2, hd3, getLsbD_bvLane,
          getLsbD_bvLane]
    by_cases hi32 : i < 32
    · simp [hi64, hi32]
    · have ht32 : i - 32 < 32 := by omega
      have ht64 : i - 32 < 64 := by omega
      simp [hi64, hi32, ht32, ht64, show 32 * 3 + (i - 32) = 64 + i by omega]

private theorem dwordToBytes4_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {d : Arg Val i32} {v : BitVec 32} (hd : d.val = v)
    {k : Arg Val i8 → Arg Val i8 → Arg Val i8 → Arg Val i8 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ b0 b1 b2 b3 : Arg Val i8,
      b0.val = bvLane 8 0 v →
      b1.val = bvLane 8 1 v →
      b2.val = bvLane 8 2 v →
      b3.val = bvLane 8 3 v →
      wp Γ Q X (k b0 b1 b2 b3) m) :
    wp Γ Q X (dwordToBytes4 d k) m := by
  unfold dwordToBytes4
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_lshr]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_trunc]; refine ⟨by omega, ?_⟩
  have hm8 : (8#32).toNat % 32 = 8 := by decide
  have hm16 : (16#32).toNat % 32 = 16 := by decide
  have hm24 : (24#32).toNat % 32 = 24 := by decide
  apply hk
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, hd, getLsbD_bvLane]; simp [hi]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hm8, hd, getLsbD_bvLane]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hm16, hd, getLsbD_bvLane]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hm24, hd, getLsbD_bvLane]

private theorem bytes4ToDword_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {b0 b1 b2 b3 : Arg Val i8} {v : BitVec 32}
    (hb0 : b0.val = bvLane 8 0 v) (hb1 : b1.val = bvLane 8 1 v)
    (hb2 : b2.val = bvLane 8 2 v) (hb3 : b3.val = bvLane 8 3 v)
    {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = v → wp Γ Q X (k r) m) :
    wp Γ Q X (bytes4ToDword b0 b1 b2 b3 k) m := by
  unfold bytes4ToDword
  dsimp only [wp, Op.wp, op1, op2, vals]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl];
    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  rw [OpCode.wp_zext]; refine ⟨by omega, ?_⟩
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2]
  rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
  have hm8 : (8#32).toNat % 32 = 8 := by decide
  have hm16 : (16#32).toNat % 32 = 16 := by decide
  have hm24 : (24#32).toNat % 32 = 24 := by decide
  apply hk
  apply BitVec.eq_of_getLsbD_eq; intro i hi32
  dsimp only [Arg.val_var]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hm8, hm16, hm24, hb0, hb1, hb2, hb3, getLsbD_bvLane, hi32, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · have h16 : decide (i < 16) = true := decide_eq_true (by omega)
    have h24 : decide (i < 24) = true := decide_eq_true (by omega)
    simp [h8, h16, h24]
  · by_cases h16 : i < 16
    · have ht1 : decide (i - 8 < 32) = true := decide_eq_true (by omega)
      have ht2 : decide (i - 8 < 8) = true := decide_eq_true (by omega)
      simp [h8, h16, ht1, ht2, show ¬(24 ≤ i) by omega, show 8 + (i - 8) = i by omega]
    · by_cases h24 : i < 24
      · have hf1 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
        have ht1 : decide (i - 16 < 32) = true := decide_eq_true (by omega)
        have ht2 : decide (i - 16 < 8) = true := decide_eq_true (by omega)
        simp [h8, h16, h24, hf1, ht1, ht2, show 16 + (i - 16) = i by omega]
      · have hf1 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
        have hf2 : decide (i - 16 < 8) = false := decide_eq_false (by omega)
        have ht1 : decide (i - 24 < 32) = true := decide_eq_true (by omega)
        have ht2 : decide (i - 24 < 8) = true := decide_eq_true (by omega)
        simp [h8, h16, h24, hf1, hf2, ht1, ht2, show 24 + (i - 24) = i by omega]

theorem dwords4ToBytes16_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {d0 d1 d2 d3 : Arg Val i32} {v : BitVec 128}
    (hd0 : d0.val = bvLane 32 0 v) (hd1 : d1.val = bvLane 32 1 v)
    (hd2 : d2.val = bvLane 32 2 v) (hd3 : d3.val = bvLane 32 3 v)
    {k : List (Arg Val i8) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ bs : List (Arg Val i8), bs.length = 16 →
      (∀ j, j < 16 → (bs.getD j (.imm 0#8)).val = bvLane 8 j v) →
      wp Γ Q X (k bs) m) :
    wp Γ Q X (dwords4ToBytes16 d0 d1 d2 d3 k) m := by
  unfold dwords4ToBytes16
  apply dwordToBytes4_wp hd0; intro b0 b1 b2 b3 h0 h1 h2 h3
  apply dwordToBytes4_wp hd1; intro b4 b5 b6 b7 h4 h5 h6 h7
  apply dwordToBytes4_wp hd2; intro b8 b9 b10 b11 h8 h9 h10 h11
  apply dwordToBytes4_wp hd3; intro b12 b13 b14 b15 h12 h13 h14 h15
  apply hk _ (by simp)
  intro j hj
  have := bvLane8_bvLane32 v
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
    j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0.trans (this 0 0 (by omega))
  · exact h1.trans (this 0 1 (by omega))
  · exact h2.trans (this 0 2 (by omega))
  · exact h3.trans (this 0 3 (by omega))
  · exact h4.trans (this 1 0 (by omega))
  · exact h5.trans (this 1 1 (by omega))
  · exact h6.trans (this 1 2 (by omega))
  · exact h7.trans (this 1 3 (by omega))
  · exact h8.trans (this 2 0 (by omega))
  · exact h9.trans (this 2 1 (by omega))
  · exact h10.trans (this 2 2 (by omega))
  · exact h11.trans (this 2 3 (by omega))
  · exact h12.trans (this 3 0 (by omega))
  · exact h13.trans (this 3 1 (by omega))
  · exact h14.trans (this 3 2 (by omega))
  · exact h15.trans (this 3 3 (by omega))

theorem bytes16ToDwords4_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {bs : List (Arg Val i8)} {v : BitVec 128}
    (hbs : ∀ j, j < 16 → (bs.getD j (.imm 0#8)).val = bvLane 8 j v)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ d0 d1 d2 d3 : Arg Val i32,
      d0.val = bvLane 32 0 v →
      d1.val = bvLane 32 1 v →
      d2.val = bvLane 32 2 v →
      d3.val = bvLane 32 3 v →
      wp Γ Q X (k d0 d1 d2 d3) m) :
    wp Γ Q X (bytes16ToDwords4 bs k) m := by
  unfold bytes16ToDwords4
  dsimp only
  have hb := fun q r (hq : q < 4) (hr : r < 4) =>
    (hbs (4 * q + r) (by omega)).trans (bvLane8_bvLane32 v q r hr).symm
  apply bytes4ToDword_wp (hb 0 0 (by omega) (by omega)) (hb 0 1 (by omega) (by omega))
    (hb 0 2 (by omega) (by omega)) (hb 0 3 (by omega) (by omega))
  intro d0 hd0
  apply bytes4ToDword_wp (hb 1 0 (by omega) (by omega)) (hb 1 1 (by omega) (by omega))
    (hb 1 2 (by omega) (by omega)) (hb 1 3 (by omega) (by omega))
  intro d1 hd1
  apply bytes4ToDword_wp (hb 2 0 (by omega) (by omega)) (hb 2 1 (by omega) (by omega))
    (hb 2 2 (by omega) (by omega)) (hb 2 3 (by omega) (by omega))
  intro d2 hd2
  apply bytes4ToDword_wp (hb 3 0 (by omega) (by omega)) (hb 3 1 (by omega) (by omega))
    (hb 3 2 (by omega) (by omega)) (hb 3 3 (by omega) (by omega))
  intro d3 hd3
  exact hk d0 d1 d2 d3 hd0 hd1 hd2 hd3

private theorem bvLane_32_shuffleDwords (v : BitVec 128) (imm : BitVec 8) (i : Nat) (hi : i < 4) :
    bvLane 32 i (shuffleDwords v imm) = bvLane 32 (imm.toNat >>> (2 * i) % 4) v := by
  unfold shuffleDwords
  apply BitVec.eq_of_getLsbD_eq
  intro j hj32
  rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
  have hjLt : 32 * i + j < 128 := by omega
  have hdiv : (32 * i + j) / 32 = i := by omega
  have hmod : (32 * i + j) % 32 = j := by omega
  have hi_lt : i < 128 / 32 := by omega
  have hzero : i / 4 = 0 := by omega
  simp [hj32, hdiv, hmod, hi_lt, hzero, Nat.mod_eq_of_lt hi]

theorem scalarShufd128_eq (imm : BitVec 8) {d0 d1 d2 d3 : Arg Val i32} {v : BitVec 128}
    (h0 : d0.val = bvLane 32 0 v) (h1 : d1.val = bvLane 32 1 v)
    (h2 : d2.val = bvLane 32 2 v) (h3 : d3.val = bvLane 32 3 v) :
    let (r0, r1, r2, r3) := scalarShufd128 imm d0 d1 d2 d3
    r0.val = bvLane 32 0 (shuffleDwords v imm) ∧
    r1.val = bvLane 32 1 (shuffleDwords v imm) ∧
    r2.val = bvLane 32 2 (shuffleDwords v imm) ∧
    r3.val = bvLane 32 3 (shuffleDwords v imm) := by
  unfold scalarShufd128
  dsimp only
  have hPick : ∀ i, i < 4 →
      (match imm.toNat >>> (2 * i) % 4 with | 0 => d0 | 1 => d1 | 2 => d2 | _ => d3).val =
      bvLane 32 i (shuffleDwords v imm) := by
    intro i hi
    rw [bvLane_32_shuffleDwords v imm i hi]
    have hm : imm.toNat >>> (2 * i) % 4 < 4 := Nat.mod_lt _ (by omega)
    rcases (by omega : imm.toNat >>> (2 * i) % 4 = 0 ∨ imm.toNat >>> (2 * i) % 4 = 1 ∨
        imm.toNat >>> (2 * i) % 4 = 2 ∨ imm.toNat >>> (2 * i) % 4 = 3) with hq | hq | hq | hq <;>
      simp [hq, h0, h1, h2, h3]
  exact ⟨hPick 0 (by omega), hPick 1 (by omega), hPick 2 (by omega), hPick 3 (by omega)⟩

private theorem scalarBlendwLane_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (imm : BitVec 8) (idx : Nat) (hIdx : idx < 4)
    {ai bi : Arg Val i32} {a b : BitVec 128}
    (ha : ai.val = bvLane 32 idx a) (hb : bi.val = bvLane 32 idx b)
    {k : Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r : Arg Val i32, r.val = bvLane 32 idx (blendWords a b imm) → wp Γ Q X (k r) m) :
    wp Γ Q X (scalarBlendwLane imm idx ai bi k) m := by
  unfold scalarBlendwLane
  dsimp only
  have hTarget : ∀ j, j < 32 →
      (bvLane 32 idx (blendWords a b imm)).getLsbD j =
        (if imm.getLsbD (2 * idx + (if j < 16 then 0 else 1)) then bi.val else ai.val).getLsbD j :=
          by
    intro j hj32
    unfold blendWords
    rw [getLsbD_bvLane, getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hi_lt : (32 * idx + j) / 16 < 128 / 16 := by omega
    simp only [hj32, decide_true, Bool.true_and, hi_lt, ↓reduceIte]
    by_cases hj16 : j < 16
    · have hd : (32 * idx + j) / 16 = 2 * idx := by omega
      have hm : (32 * idx + j) % 16 = j := by omega
      have h8 : (2 * idx) % 8 = 2 * idx := Nat.mod_eq_of_lt (by omega)
      simp only [hj16, ↓reduceIte, Nat.add_zero, hd, hm, h8]
      cases imm.getLsbD (2 * idx)
      · rw [ha]; simp [bvLane, hj32, hj16, show 16 * (2 * idx) + j = 32 * idx + j by omega]
      · rw [hb]; simp [bvLane, hj32, hj16, show 16 * (2 * idx) + j = 32 * idx + j by omega]
    · have hd : (32 * idx + j) / 16 = 2 * idx + 1 := by omega
      have hm : (32 * idx + j) % 16 = j - 16 := by omega
      have h8 : (2 * idx + 1) % 8 = 2 * idx + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hj16, ↓reduceIte, hd, hm, h8]
      cases imm.getLsbD (2 * idx + 1)
      · rw [ha]; simp [bvLane, hj32, show j - 16 < 16 by omega,
          show 16 * (2 * idx + 1) + (j - 16) = 32 * idx + j by omega]
      · rw [hb]; simp [bvLane, hj32, show j - 16 < 16 by omega,
          show 16 * (2 * idx + 1) + (j - 16) = 32 * idx + j by omega]
  cases hlo : imm.getLsbD (2 * idx) <;> cases hhi : imm.getLsbD (2 * idx + 1)
  · dsimp only
    apply hk
    apply BitVec.eq_of_getLsbD_eq; intro j hj32
    rw [hTarget j hj32]
    by_cases hj16 : j < 16 <;> simp [hj16, hlo, hhi]
  · dsimp only [wp, Op.wp, op2, vals]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
    apply hk
    apply BitVec.eq_of_getLsbD_eq; intro j hj32
    dsimp only [Arg.val_var]
    rw [hTarget j hj32, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and]
    by_cases hj16 : j < 16
    · have c1 : (65535#32).getLsbD j = true := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (65535 : Nat) = 2 ^ 16 - 1 := by decide
        rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hj16
      have c2 : (4294901760#32).getLsbD j = false := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
        rw [this, Nat.testBit_shiftLeft]; simp [show ¬(16 ≤ j) by omega]
      simp [hj16, hlo, c1, c2]
    · have c1 : (65535#32).getLsbD j = false := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (by decide : 65535 < 2 ^ 16)
            (Nat.pow_le_pow_right (by omega) (by omega)))
      have c2 : (4294901760#32).getLsbD j = true := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
        rw [this, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
        simp [show 16 ≤ j by omega, show j - 16 < 16 by omega]
      simp [hj16, hhi, c1, c2]
  · dsimp only [wp, Op.wp, op2, vals]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    rw [OpCode.wp_and]; dsimp only [lift2, Arg.val_imm]
    rw [OpCode.wp_or]; dsimp only [lift2, Arg.val_var]
    apply hk
    apply BitVec.eq_of_getLsbD_eq; intro j hj32
    dsimp only [Arg.val_var]
    rw [hTarget j hj32, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and]
    by_cases hj16 : j < 16
    · have c1 : (65535#32).getLsbD j = true := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (65535 : Nat) = 2 ^ 16 - 1 := by decide
        rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hj16
      have c2 : (4294901760#32).getLsbD j = false := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
        rw [this, Nat.testBit_shiftLeft]; simp [show ¬(16 ≤ j) by omega]
      simp [hj16, hlo, c1, c2]
    · have c1 : (65535#32).getLsbD j = false := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (by decide : 65535 < 2 ^ 16)
            (Nat.pow_le_pow_right (by omega) (by omega)))
      have c2 : (4294901760#32).getLsbD j = true := by
        rw [BitVec.getLsbD_ofNat]; simp [hj32]
        have : (4294901760 : Nat) = (2 ^ 16 - 1) <<< 16 := by decide
        rw [this, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
        simp [show 16 ≤ j by omega, show j - 16 < 16 by omega]
      simp [hj16, hhi, c1, c2]
  · dsimp only
    apply hk
    apply BitVec.eq_of_getLsbD_eq; intro j hj32
    rw [hTarget j hj32]
    by_cases hj16 : j < 16 <;> simp [hj16, hlo, hhi]

theorem scalarBlendw128_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (imm : BitVec 8) {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {a b : BitVec 128}
    (ha0 : a0.val = bvLane 32 0 a) (ha1 : a1.val = bvLane 32 1 a)
    (ha2 : a2.val = bvLane 32 2 a) (ha3 : a3.val = bvLane 32 3 a)
    (hb0 : b0.val = bvLane 32 0 b) (hb1 : b1.val = bvLane 32 1 b)
    (hb2 : b2.val = bvLane 32 2 b) (hb3 : b3.val = bvLane 32 3 b)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (blendWords a b imm) →
      r1.val = bvLane 32 1 (blendWords a b imm) →
      r2.val = bvLane 32 2 (blendWords a b imm) →
      r3.val = bvLane 32 3 (blendWords a b imm) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarBlendw128 imm a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold scalarBlendw128
  apply scalarBlendwLane_wp imm 0 (by omega) ha0 hb0; intro r0 hr0
  apply scalarBlendwLane_wp imm 1 (by omega) ha1 hb1; intro r1 hr1
  apply scalarBlendwLane_wp imm 2 (by omega) ha2 hb2; intro r2 hr2
  apply scalarBlendwLane_wp imm 3 (by omega) ha3 hb3; intro r3 hr3
  exact hk r0 r1 r2 r3 hr0 hr1 hr2 hr3

theorem scalarAlignr128_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (imm : BitVec 8) {h0 h1 h2 h3 l0 l1 l2 l3 : Arg Val i32} {hi lo : BitVec 128}
    (hh0 : h0.val = bvLane 32 0 hi) (hh1 : h1.val = bvLane 32 1 hi)
    (hh2 : h2.val = bvLane 32 2 hi) (hh3 : h3.val = bvLane 32 3 hi)
    (hl0 : l0.val = bvLane 32 0 lo) (hl1 : l1.val = bvLane 32 1 lo)
    (hl2 : l2.val = bvLane 32 2 lo) (hl3 : l3.val = bvLane 32 3 lo)
    {k : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r0 r1 r2 r3 : Arg Val i32,
      r0.val = bvLane 32 0 (alignBytes hi lo imm) →
      r1.val = bvLane 32 1 (alignBytes hi lo imm) →
      r2.val = bvLane 32 2 (alignBytes hi lo imm) →
      r3.val = bvLane 32 3 (alignBytes hi lo imm) →
      wp Γ Q X (k r0 r1 r2 r3) m) :
    wp Γ Q X (scalarAlignr128 imm h0 h1 h2 h3 l0 l1 l2 l3 k) m := by
  unfold scalarAlignr128
  apply dwords4ToBytes16_wp hl0 hl1 hl2 hl3; intro lbs _ hLbs
  apply dwords4ToBytes16_wp hh0 hh1 hh2 hh3; intro hbs _ hHbs
  apply bytes16ToDwords4_wp (v := alignBytes hi lo imm)
  · intro i hi16
    change Arg.val ((List.map (fun i =>
      if i + imm.toNat < 16 then lbs.getD (i + imm.toNat) (.imm 0#8)
      else if i + imm.toNat < 32 then hbs.getD (i + imm.toNat - 16) (.imm 0#8) else .imm 0#8)
      (List.range 16)).getD i (.imm 0#8)) = bvLane 8 i (alignBytes hi lo imm)
    have hMap : (List.map (fun i =>
      if i + imm.toNat < 16 then lbs.getD (i + imm.toNat) (.imm 0#8)
      else if i + imm.toNat < 32 then hbs.getD (i + imm.toNat - 16) (.imm 0#8) else .imm 0#8)
      (List.range 16)).getD i (.imm 0#8) =
      (if i + imm.toNat < 16 then lbs.getD (i + imm.toNat) (.imm 0#8)
       else if i + imm.toNat < 32 then hbs.getD (i + imm.toNat - 16) (.imm 0#8) else .imm 0#8) := by
      simp [List.getD, List.getElem?_map, List.getElem?_range hi16]
    rw [hMap]
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
    rw [getLsbD_bvLane]
    unfold alignBytes
    rw [getLsbD_bvOfLanes (by omega) _ (by omega)]
    have hdiv : (8 * i + bit) / 8 = i := by omega
    have hmod : (8 * i + bit) % 8 = bit := by omega
    have hlt16 : i < 128 / 8 := by omega
    have hzero : i / 16 = 0 := by omega
    have hmod16 : i % 16 = i := by omega
    simp only [hbit8, decide_true, Bool.true_and, hdiv, hmod, hlt16, ↓reduceIte, hzero, hmod16,
      Nat.mul_zero, Nat.zero_add]
    by_cases h16 : i + imm.toNat < 16
    · simp only [h16, ↓reduceIte]
      rw [hLbs (i + imm.toNat) h16]
    · by_cases h32 : i + imm.toNat < 32
      · simp only [h16, h32, ↓reduceIte]
        rw [hHbs (i + imm.toNat - 16) (by omega)]
      · simp [h16, h32]
  · exact hk


end LegalWp

end LeanQbe.T
