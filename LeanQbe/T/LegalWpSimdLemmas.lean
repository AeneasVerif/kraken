module

public import LeanQbe.T.LegalWpBaseLemmas

/-!
# Legalization word-stream and 128-bit SIMD/SHA-256 lowering `_wp` lemmas (`T5`, Part 2)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalWp


def words64GetLsb (ws : List (Arg Val i64)) (i : Nat) : Bool :=
  (ws.getD (i / 64) (.imm 0#64)).val.getLsbD (i % 64)

def Words64Stream (ws : List (Arg Val i64)) (acc : Arg Val i64)
    (accBits totalBits : Nat) (bits : Nat → Bool) : Prop :=
  accBits < 64 ∧
  totalBits = 64 * ws.length + accBits ∧
  (∀ j, accBits ≤ j → acc.val.getLsbD j = false) ∧
  (∀ i, i < 64 * ws.length → words64GetLsb ws i = bits i) ∧
  (∀ j, j < accBits → acc.val.getLsbD j = bits (64 * ws.length + j))

private theorem list_getD_append_left {α : Type} (xs ys : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private theorem list_getD_append_right_eq {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD xs.length d = x := by
  simp [List.getD]

private theorem words64GetLsb_append_left (ws ys : List (Arg Val i64)) {i : Nat}
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
        refine ⟨by omega, by simp only [List.length_append, List.length_singleton]; omega, fun j _ => by simp, ?_, fun j hj => by omega⟩
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
          refine ⟨by omega, by simp only [List.length_append, List.length_singleton]; omega, fun j _ => by simp, ?_, fun j hj => by omega⟩
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
          refine ⟨by omega, by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_⟩
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
    rw [packLeavesToWords64.go.eq_1]
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
  | .bits n, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m, hk => by
    dsimp only [LegalTarget.leafTys] at fx hFx
    rcases fx with ⟨x, ⟨⟩⟩
    rw [packLeavesToWords64.go.eq_2]
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
  | .float f, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m, hk => by
    dsimp only [LegalTarget.leafTys] at fx hFx
    rcases fx with ⟨x, ⟨⟩⟩
    rw [packLeavesToWords64.go.eq_3]
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
  | .pair a b, hSup, fx, v, ws, acc, accBits, totalBits, bits, bits', hFx, hS, hAgree, hNew, k, m, hk => by
    rw [packLeavesToWords64.go.eq_4]
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
        simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, show ¬(a.size + j < a.size) by omega]
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
          else Expr.let_ (op2 (.lshr i64) (words.getD (off / 64) (.imm 0#64)) (.imm (BitVec.ofNat 64 (off % 64))))
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
        Expr.let_ (op2 (.shl i64) (words.getD (off / 64 + 1) (.imm 0#64)) (.imm (BitVec.ofNat 64 (64 - off % 64))))
          fun h => Expr.let_ (op2 (.or i64) lo (.var h.1)) fun lo' => emitMaskToN w 64 (.var lo'.1) k)
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
          have hw1 : (words.getD (off / 64 + 1) (.imm 0#64)).val.getLsbD (i - (64 - off % 64)) = bits i := by
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
    rw [unpackWords64ToLeaves.eq_1]
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
    rw [unpackWords64ToLeaves.eq_2]
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
    rw [unpackWords64ToLeaves.eq_3]
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
    rw [unpackWords64ToLeaves.eq_4]
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
        simp [toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, show ¬(a.size + i < a.size) by omega]
      · intro fb hFb
        apply hk (tupAppend fa fb)
        dsimp only [LegalTarget.leafTys]
        rw [valsTup_tupAppend, hFa, hFb, leafVals_pair]

private theorem foldl_bvOfLanes_getLsbD (w c : Nat) (hc : 0 < c) (f : Nat → BitVec c) :
    ∀ (n : Nat) (init : BitVec w) (k : Nat),
      k < w →
      ((List.range n).foldl (fun acc i => acc ||| BitVec.setWidth w (f i) <<< (c * i)) init).getLsbD k =
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
        have hmc : decide (k % c < w) = true := decide_eq_true (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk)
        rw [hsub]
        simp [hnot, hmc, heq]
      · have hgt : n + 1 ≤ k / c := by omega
        have hnot1 : ¬(k / c < n + 1) := by omega
        have hdiff : c * (n + 1) ≤ k := by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hc).mp hgt
        have hdiff' : c * n + c ≤ k := by simpa [Nat.mul_succ] using hdiff
        have hf : (f n).getLsbD (k - c * n) = false :=
          BitVec.getLsbD_of_ge (f n) (k - c * n) (by omega)
        simp [hkc, hnot1, hf]

private theorem getLsbD_bvOfLanes {w c : Nat} (hc : 0 < c) (f : Nat → BitVec c) {k : Nat}
    (hk : k < w) :
    (bvOfLanes w c f).getLsbD k =
      (if k / c < w / c then (f (k / c)).getLsbD (k % c) else false) := by
  unfold bvOfLanes
  rw [foldl_bvOfLanes_getLsbD w c hc f (w / c) (0#w) k hk]
  simp

private theorem getLsbD_bvLane {w : Nat} (c i : Nat) (v : BitVec w) (j : Nat) :
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
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hw0, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
    have hmod : (32#64).toNat % 64 = 32 := by decide
    rw [hmod]
    simp [hi, show 32 + i < 64 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, hw1, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
    simp [hi, show i < 64 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hw1, BitVec.getLsbD_extractLsb', getLsbD_bvLane]
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
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
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
        BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hd0, hd1, getLsbD_bvLane, getLsbD_bvLane]
    by_cases hi32 : i < 32
    · simp [hi64, hi32]
    · have ht32 : i - 32 < 32 := by omega
      have ht64 : i - 32 < 64 := by omega
      simp [hi64, hi32, ht32, ht64, show 32 + (i - 32) = i by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi64
    dsimp only [Arg.val_var]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hmod, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hd2, hd3, getLsbD_bvLane, getLsbD_bvLane]
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
  rw [OpCode.wp_shl]; simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm, Arg.val_var]
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

private theorem dwords4ToBytes16_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem bytes16ToDwords4_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem scalarShufd128_eq (imm : BitVec 8) {d0 d1 d2 d3 : Arg Val i32} {v : BitVec 128}
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
        (if imm.getLsbD (2 * idx + (if j < 16 then 0 else 1)) then bi.val else ai.val).getLsbD j := by
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
          (Nat.lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by omega) (by omega)))
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
          (Nat.lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by omega) (by omega)))
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

private theorem scalarBlendw128_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem scalarAlignr128_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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
    rw [scalarShufb128.muxBytes.eq_def]
    exact hk (.imm 0#8) (fun hne _ _ => absurd rfl hne)
  | [b], j, k, m, hk => by
    rw [scalarShufb128.muxBytes.eq_def]
    apply hk b
    intro _ hle hlt
    simp only [List.length_singleton] at hlt
    have hsub : idx.val.toNat - j = 0 := by omega
    simp [hsub]
  | b :: b' :: bs, j, k, m, hk => by
    rw [scalarShufb128.muxBytes.eq_def]
    dsimp only
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
      have hRestEq := hRest (List.cons_ne_nil _ _) hgt (by simp only [List.length_cons] at hlt ⊢; omega)
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
          have hIdxMod : ((mbs.getD q (.imm 0#8)).val &&& 15#8).toNat = (bvLane 8 q m128).toNat % 16 := by
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
  exact scalarShufb128_doBytes_wp hAbsLen hAbs hMbs k 0 [] mem rfl (fun _ h => absurd h (by omega)) hk

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
  rw [OpCode.wp_and, OpCode.wp_not, OpCode.wp_and, OpCode.wp_xor]; dsimp only [lift1, lift2, Arg.val_var]
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
        bvLane 32 idx w0123 + Sha256.σ₀ (if idx < 3 then bvLane 32 (idx + 1) w0123 else bvLane 32 0 w4) := by
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
      a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
      b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
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
        (spec128 (BitVec.extractLsb' (128 * q) 128 xBits) (BitVec.extractLsb' (128 * q) 128 yBits)).getLsbD j) :
    ∀ (rem : Nat) (q : Nat), q + rem = t.size / 128 →
      ∀ (rx ry acc : List (Arg Val i64)) (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) (m : Mem 64),
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
        apply legalSimdScalar128_goWords_wp target hv on128 spec128 h128 t ht hSize xBits yBits specFull
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
              simp only [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_append_right (Nat.le_refl _)]
              simp [hw0, hj64]
            · have hdiv : i / 64 = acc.length + 1 := by rw [haccLen]; omega
              have hmod : i % 64 = i - (128 * q + 64) := by omega
              have hj64 : i - (128 * q + 64) < 64 := by omega
              simp only [words64GetLsb, hdiv, hmod, List.getD, List.getElem?_append_right (by omega : acc.length ≤ acc.length + 1),
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
      a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
      b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
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
  apply legalSimdScalar128_goWords_wp target hv on128 spec128 h128 t ht hSize (toBits t x) (toBits t y)
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
        (blendWords (BitVec.extractLsb' (128 * q) 128 a) (BitVec.extractLsb' (128 * q) 128 b) imm).getLsbD j := by
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
    simp [hj16, hlt128, show 128 * q + (16 * (j / 16) + j % 16) = 16 * (8 * q + j / 16) + j % 16 by omega]

private theorem extractLsb_128_alignBytes {w : Nat} (hw : w % 128 = 0)
    (hi lo : BitVec w) (q : Nat) (hq : q < w / 128) (imm : BitVec 8) :
    ∀ j, j < 128 →
      (alignBytes hi lo imm).getLsbD (128 * q + j) =
        (alignBytes (BitVec.extractLsb' (128 * q) 128 hi) (BitVec.extractLsb' (128 * q) 128 lo) imm).getLsbD j := by
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
        (shuffleBytes (BitVec.extractLsb' (128 * q) 128 a) (BitVec.extractLsb' (128 * q) 128 m)).getLsbD j := by
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
  have hIdxEq : bvLane 8 (16 * q + j / 8) m = bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m) := by
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit8
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
    have hlt128 : 8 * (j / 8) + bit < 128 := by omega
    simp [hbit8, hlt128, show 128 * q + (8 * (j / 8) + bit) = 8 * (16 * q + j / 8) + bit by omega]
  rw [hIdxEq]
  cases hmsb : (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [getLsbD_bvLane, getLsbD_bvLane, BitVec.getLsbD_extractLsb']
    have hj8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    have hm16 : (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16 < 16 := Nat.mod_lt _ (by omega)
    have hlt128 : 8 * ((bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8 < 128 := by omega
    simp [hj8, hlt128, show 128 * q + (8 * ((bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8) =
      8 * (16 * q + (bvLane 8 (j / 8) (BitVec.extractLsb' (128 * q) 128 m)).toNat % 16) + j % 8 by omega]
  · simp

private theorem simdPair_split_shuffleDwords (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (x : Val (.pair a b)) (imm : BitVec 8) :
    ofBits (.pair a b) (shuffleDwords (toBits (.pair a b) x) imm) =
      (ofBits a (shuffleDwords (toBits a x.1) imm),
       ofBits b (shuffleDwords (toBits b x.2) imm)) := by
  rw [ofBits.eq_4]
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
    have hBitLt : 32 * (4 * (j / 32 / 4) + imm.toNat >>> (2 * (j / 32 % 4)) % 4) + j % 32 < a.size := by omega
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
    have hNotLt : ¬(32 * (4 * (a.size / 128 + j / 32 / 4) + imm.toNat >>> (2 * (j / 32 % 4)) % 4) + j % 32 < a.size) := by omega
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
  rw [ofBits.eq_4]
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
  rw [ofBits.eq_4]
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
        have hBitLt : 8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 < a.size := by omega
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
      have hNotLt : ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 < a.size) := by omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 - a.size =
          8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat)) + j % 8 by omega]
    · by_cases h32 : j / 8 % 16 + imm.toNat < 32
      · simp only [h16, h32, ↓reduceIte]
        rw [getLsbD_bvLane, getLsbD_bvLane]
        have hNotLt : ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 < a.size) := by omega
        simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
          show 8 * (16 * (a.size / 128 + j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 - a.size =
            8 * (16 * (j / 8 / 16) + (j / 8 % 16 + imm.toNat) - 16) + j % 8 by omega]
      · simp [h16, h32]

private theorem simdPair_split_shuffleBytes (a b : Ty) (ha : a.size ≠ 0 ∧ a.size % 128 = 0)
    (hb : b.size ≠ 0 ∧ b.size % 128 = 0) (x m : Val (.pair a b)) :
    ofBits (.pair a b) (shuffleBytes (toBits (.pair a b) x) (toBits (.pair a b) m)) =
      (ofBits a (shuffleBytes (toBits a x.1) (toBits a m.1)),
       ofBits b (shuffleBytes (toBits b x.2) (toBits b m.2))) := by
  rw [ofBits.eq_4]
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
      have hBitLt : 8 * (16 * (j / 8 / 16) + (bvLane 8 (j / 8) (toBits a m.1)).toNat % 16) + j % 8 < a.size := by
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
    have hIdxEq : bvLane 8 (a.size / 8 + j / 8) (toBits (a.pair b) m) = bvLane 8 (j / 8) (toBits b m.2) := by
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
      have hNotLt : ¬(8 * (16 * (a.size / 128 + j / 8 / 16) + (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16) + j % 8 < a.size) := by omega
      simp [hj8, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hNotLt,
        show 8 * (16 * (a.size / 128 + j / 8 / 16) + (bvLane 8 (j / 8) (toBits b m.2)).toNat % 16) + j % 8 - a.size =
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
    rw [legalShufd.eq_def]
    have hBad : (t.size == 0 || t.size % 128 != 0) = false := by
      simp [beq_false_of_ne hNe, hMod]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u _v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 _v → b1.val = bvLane 32 1 _v → b2.val = bvLane 32 2 _v → b3.val = bvLane 32 3 _v →
        (∀ r0 r1 r2 r3 : Arg Val i32,
          r0.val = bvLane 32 0 (shuffleDwords u imm) →
          r1.val = bvLane 32 1 (shuffleDwords u imm) →
          r2.val = bvLane 32 2 (shuffleDwords u imm) →
          r3.val = bvLane 32 3 (shuffleDwords u imm) →
          wp Γ Q X (cont r0 r1 r2 r3) mem) →
        wp Γ Q X (match scalarShufd128 imm a0 a1 a2 a3 with | (r0, r1, r2, r3) => cont r0 r1 r2 r3) mem := by
      intro a0 a1 a2 a3 b0 b1 b2 b3 u _v cont mem ha0 ha1 ha2 ha3 _ _ _ _ hcont
      rcases scalarShufd128_eq imm ha0 ha1 ha2 ha3 with ⟨h0, h1, h2, h3⟩
      exact hcont _ _ _ _ h0 h1 h2 h3
    cases t with
    | bool | bits _ | float _ =>
      exact legalSimdScalar128_wp target hv _ (fun u _ => shuffleDwords u imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs xs x x hx hx _
        (fun q hq j hj => extractLsb_128_shuffleDwords hMod (toBits _ x) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only
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
            (fun q hq j hj => extractLsb_128_shuffleDwords hMod (toBits (.pair a b) x) q hq imm j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
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
            (fun q hq j hj => extractLsb_128_shuffleDwords hMod (toBits (.pair a b) x) q hq imm j hj)
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
    rw [legalBlendw.eq_def]
    have hBad : (t.size == 0 || t.size % 128 != 0) = false := by
      simp [beq_false_of_ne hNe, hMod]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
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
      exact legalSimdScalar128_wp target hv _ (fun u v => blendWords u v imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_blendWords hMod (toBits _ x) (toBits _ y) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only
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
            (fun q hq j hj => extractLsb_128_blendWords hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
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
            (fun q hq j hj => extractLsb_128_blendWords hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm j hj)
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
    rw [legalAlignr.eq_def]
    have hBad : (t.size == 0 || t.size % 128 != 0) = false := by
      simp [beq_false_of_ne hNe, hMod]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
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
      exact legalSimdScalar128_wp target hv _ (fun u v => alignBytes u v imm) hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_alignBytes hMod (toBits _ x) (toBits _ y) q hq imm j hj)
        k m hk
    | pair a b =>
      dsimp only
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
            (fun q hq j hj => extractLsb_128_alignBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
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
            (fun q hq j hj => extractLsb_128_alignBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq imm j hj)
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
    rw [legalShufb.eq_def]
    have hBad : (t.size == 0 || t.size % 128 != 0) = false := by
      simp [beq_false_of_ne hNe, hMod]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hOn128 : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : Arg Val i32} {u v : BitVec 128}
        (cont : Arg Val i32 → Arg Val i32 → Arg Val i32 → Arg Val i32 → Expr Val Cont rs) (mem : Mem 64),
        a0.val = bvLane 32 0 u → a1.val = bvLane 32 1 u → a2.val = bvLane 32 2 u → a3.val = bvLane 32 3 u →
        b0.val = bvLane 32 0 v → b1.val = bvLane 32 1 v → b2.val = bvLane 32 2 v → b3.val = bvLane 32 3 v →
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
      exact legalSimdScalar128_wp target hv _ shuffleBytes hOn128
        _ ht ⟨hNe, hMod⟩ xs ys x y hx hy _
        (fun q hq j hj => extractLsb_128_shuffleBytes hMod (toBits _ x) (toBits _ y) q hq j hj)
        k m hk
    | pair a b =>
      dsimp only
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
            (fun q hq j hj => extractLsb_128_shuffleBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq j hj)
            k m hk
      · have hPackF : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr hPack
        simp only [hPack]
        by_cases hSplit128 : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
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
            (fun q hq j hj => extractLsb_128_shuffleBytes hMod (toBits (.pair a b) x) (toBits (.pair a b) y) q hq j hj)
            k m hk


end LegalWp

end LeanQbe.T
