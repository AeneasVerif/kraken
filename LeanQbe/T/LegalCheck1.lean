module

public import LeanQbe.T.LegalCheck1a
public import LeanQbe.T.LegalEmit

/-!
# Target legality proofs for `LeanQbe.T.Legal` (Part 1b: Bit, Word64 & Memory Helpers)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalIsLegal

/-! ### Bit, bool, load/store, word64, and SIMD scalar helper lemmas -/

theorem emitMaskToN_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {n w : Nat} (hw : w ∈ target.bitWidths)
    (x : Arg K (.bits w)) (hx : ArgNormal target Γ (.bits w) x)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitMaskToN n w x k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  maskToNEmit_eq_emitMaskToN n w x k ▸
    (maskToNEmit n w).run_isLegal target (x, ()) (maskToNEmit_isLegal target hw) ⟨hx, trivial⟩ hk

theorem emitSextToW_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {n w : Nat} (hw : w ∈ target.bitWidths)
    (x : Arg K (.bits w)) (hx : ArgNormal target Γ (.bits w) x)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitSextToW n w x k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  sextToWEmit_eq_emitSextToW n w x k ▸
    (sextToWEmit n w).run_isLegal target (x, ()) (sextToWEmit_isLegal target hw) ⟨hx, trivial⟩ hk

theorem emitCountMod_isLegal (target : LegalTarget) (hv : target.valid = true)
    {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} {rs : List Ty} {n w : Nat}
      (hw : w ∈ target.bitWidths)
    (c : Arg K (.bits w)) (hc : ArgNormal target Γ (.bits w) c)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitCountMod n w c k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
  have hwpos : 0 < w := (valid_bitWidth_spec hv hw).1
  simp only [emitCountMod]
  cases c with
  | imm cb => exact hk Γ (.imm _) (CtxExtends.refl Γ) hleg
  | var _ =>
    refine isLegal_let_op2_normal target (.urem w) _ (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, hw, hwpos]) hc hleg hleg ?_
    exact hk ((.bits w, .normal) :: Γ) (.var Γ.length) (CtxExtends.cons _ _)
      (ArgNormal.head target Γ hleg)

theorem emitBoolCmp_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (o : CmpOp) (a b : Arg K .bool)
    (ha : ArgNormal target Γ .bool a) (hb : ArgNormal target Γ .bool b)
    {k : Arg K .bool → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k) :
    (toTFlat (emitBoolCmp o a b k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  (boolCmpEmit_bundle target o).isLegal_eq (a, b, ()) ⟨ha, hb, trivial⟩ hk
    (boolCmpEmit_eq_emitBoolCmp o a b k)

theorem emitBoolSelect_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (c a b : Arg K .bool)
    (hc : ArgNormal target Γ .bool c) (ha : ArgNormal target Γ .bool a)
      (hb : ArgNormal target Γ .bool b)
    {k : Arg K .bool → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k) :
    (toTFlat (emitBoolSelect c a b k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  (boolSelectEmit_bundle target).isLegal_eq (c, a, b, ()) ⟨hc, ha, hb, trivial⟩ hk rfl

theorem emitTernlogBool_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)}
    {Δ : List (List Ty)} {rs : List Ty} (a b c : Arg K .bool) (imm : BitVec 8)
    (ha : ArgNormal target Γ .bool a) (hb : ArgNormal target Γ .bool b)
    (hc : ArgNormal target Γ .bool c)
    {k : Arg K .bool → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k) :
    (toTFlat (emitTernlogBool a b c imm k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  (ternlogBoolEmit_bundle target imm).isLegal_eq (a, b, c, ()) ⟨ha, hb, hc, trivial⟩ hk
    (ternlogBoolEmit_eq_emitTernlogBool imm a b c k)

theorem emitTernlogBits_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)}
    {Δ : List (List Ty)} {rs : List Ty} {w : Nat} (hw : w ∈ target.bitWidths)
    (a b c : Arg K (.bits w)) (imm : BitVec 8)
    (ha : ArgNormal target Γ (.bits w) a) (hb : ArgNormal target Γ (.bits w) b)
    (hc : ArgNormal target Γ (.bits w) c)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitTernlogBits w a b c imm k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  (ternlogBitsEmit_bundle target hw imm).isLegal_eq (a, b, c, ()) ⟨ha, hb, hc, trivial⟩ hk
    (ternlogBitsEmit_eq_emitTernlogBits w imm a b c k)

theorem legalBitsArith_isLegal (target : LegalTarget) (hv : target.valid = true)
    {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} {rs : List Ty}
    {n : Nat} (hsn : target.supportsTy (.bits n) = true)
    (code : OpCode [.bits n, .bits n] [.bits n])
    (a b : Arg K (.bits (target.widenWidth n)))
    (ha : ArgNormal target Γ (.bits (target.widenWidth n)) a)
    (hb : ArgNormal target Γ (.bits (target.widenWidth n)) b)
    {k : Arg K (.bits (target.widenWidth n)) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits (target.widenWidth n)) r)
      k) :
    (toTFlat (legalBitsArith target n code a b k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hw : target.widenWidth n ∈ target.bitWidths := widenWidth_mem_of_supports hsn
  have hleg : target.isLegalTy (.bits (target.widenWidth n)) = true := by
    simpa [LegalTarget.isLegalTy] using hw
  simp only [legalBitsArith]
  by_cases hn0 : (n == 0) = true
  · simp only [hn0, ↓reduceIte]; exact hk Γ (.imm _) (CtxExtends.refl Γ) hleg
  · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
    cases code with
    | add _ =>
      refine isLegal_let_op2_normal target (.add (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
      exact emitMaskToN_isLegal target hw (.var Γ.length) (ArgNormal.head target Γ hleg)
        fun Γ' r hrExt hr => hk Γ' r ((CtxExtends.cons _ _).trans hrExt) hr
    | sub _ =>
      refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact emitMaskToN_isLegal target hw (.var Γ.length) (ArgNormal.head target Γ hleg)
        fun Γ' r hrExt hr => hk Γ' r ((CtxExtends.cons _ _).trans hrExt) hr
    | mul _ =>
      refine isLegal_let_op2_normal target (.mul (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact emitMaskToN_isLegal target hw (.var Γ.length) (ArgNormal.head target Γ hleg)
        fun Γ' r hrExt hr => hk Γ' r ((CtxExtends.cons _ _).trans hrExt) hr
    | and _ =>
      refine isLegal_let_op2_normal target (.and (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
    | or _ =>
      refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
    | xor _ =>
      refine isLegal_let_op2_normal target (.xor (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
    | shl _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) a c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono hcExt) hc hleg ?_
        exact emitMaskToN_isLegal target hw (.var Γ1.length) (ArgNormal.head target Γ1 hleg)
          fun Γ2 r hrExt hr => hk Γ2 r (hcExt.trans ((CtxExtends.cons _ _).trans hrExt)) hr
    | lshr _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) a c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono hcExt) hc hleg ?_
        exact hk _ (.var Γ1.length) (hcExt.trans (CtxExtends.cons _ _))
          (ArgNormal.head target Γ1 hleg)
    | ashr _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.ashr (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine emitSextToW_isLegal target hw a (ha.mono hcExt) fun Γ2 sa hsaExt hsa => ?_
        refine isLegal_let_op2_normal target (.ashr (.bits (target.widenWidth n))) sa c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hsa (hc.mono hsaExt) hleg ?_
        exact emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hleg)
          fun Γ3 r hrExt hr =>
            hk Γ3 r (hcExt.trans (hsaExt.trans ((CtxExtends.cons _ _).trans hrExt))) hr
    | rotl _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.rotl (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.imm _) c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hleg hc hleg ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h12 : CtxExtends Γ Γ2 := hcExt.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) a c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h12) (hc.mono (CtxExtends.cons _ _)) hleg
            ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h12.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) a
          (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h13)
            ((ArgNormal.head target Γ1 hleg).mono (CtxExtends.cons _ _)) hleg ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        have h14 : CtxExtends Γ Γ4 := h13.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length)
          (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw])
            ((ArgNormal.head target Γ2 hleg).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hleg) hleg ?_
        exact emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hleg)
          fun Γ5 r hrExt hr => hk Γ5 r (h14.trans ((CtxExtends.cons _ _).trans hrExt)) hr
    | rotr _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.rotr (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.imm _) c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hleg hc hleg ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h12 : CtxExtends Γ Γ2 := hcExt.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) a c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h12) (hc.mono (CtxExtends.cons _ _)) hleg
            ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h12.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) a (.var Γ1.length)
          _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h13)
            ((ArgNormal.head target Γ1 hleg).mono (CtxExtends.cons _ _)) hleg ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        have h14 : CtxExtends Γ Γ4 := h13.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length)
          (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw])
            ((ArgNormal.head target Γ2 hleg).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hleg) hleg ?_
        exact emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hleg)
          fun Γ5 r hrExt hr => hk Γ5 r (h14.trans ((CtxExtends.cons _ _).trans hrExt)) hr
    | _ => simp [toTFlat_hlt]

theorem ArgNormal_getD_i64 (target : LegalTarget) {Γ : List (Ty × VarKind)}
  (h64 : 64 ∈ target.bitWidths)
    (ws : List (Arg K i64)) (hws : ∀ x ∈ ws, ArgNormal target Γ i64 x) (i : Nat) :
    ArgNormal target Γ i64 (ws.getD i (.imm 0#64)) := by
  have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
  induction ws generalizing i with
  | nil => simp [List.getD]; exact hleg64
  | cons w ws ih =>
    cases i with
    | zero => exact hws w (by simp)
    | succ i => exact ih (fun x hx => hws x (by simp [hx])) i

theorem pushLeafWord64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h64 : 64 ∈ target.bitWidths) (w : Nat) :
    ∀ {Γ : List (Ty × VarKind)} (leaf : Arg K i64) (ws : List (Arg K i64)) (acc : Arg K i64)
      (accBits : Nat),
      ArgNormal target Γ i64 leaf → (∀ x ∈ ws, ArgNormal target Γ i64 x) →
        ArgNormal target Γ i64 acc →
      ∀ {k : List (Arg K i64) → Arg K i64 → Nat → Expr K KL rs},
      (∀ Γ' ws' acc' bits', CtxExtends Γ Γ' →
        (∀ x ∈ ws', ArgNormal target Γ' i64 x) → ArgNormal target Γ' i64 acc' →
        (toTFlat (k ws' acc' bits') Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (pushLeafWord64 w leaf ws acc accBits k) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, leaf, ws, acc, accBits, hleaf, hws, hacc, k, hk => by
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [pushLeafWord64]
    by_cases hw0 : (w == 0) = true
    · simp only [hw0, ↓reduceIte]; exact hk Γ ws acc accBits (CtxExtends.refl Γ) hws hacc
    · simp only [hw0, Bool.false_eq_true, ↓reduceIte]
      by_cases hab0 : (accBits == 0) = true
      · simp only [hab0, ↓reduceIte]
        by_cases hw64 : 64 ≤ w
        · simp only [hw64, ↓reduceIte]
          refine hk Γ (ws ++ [leaf]) (.imm 0#64) 0 (CtxExtends.refl Γ) (fun x hx => ?_) hleg64
          rcases List.mem_append.1 hx with hm | hm
          · exact hws x hm
          · simp only [List.mem_singleton] at hm; subst hm; exact hleaf
        · simp only [hw64, ↓reduceIte]; exact hk Γ ws leaf w (CtxExtends.refl Γ) hws hleaf
      · simp only [hab0, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.shl i64) leaf (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) hleaf hleg64 hleg64 ?_
        let Γ1 := (i64, VarKind.normal) :: Γ
        have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
        refine isLegal_let_op2_normal target (.or i64) acc (.var Γ.length) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) (hacc.mono hExt1) (ArgNormal.head target Γ hleg64)
            hleg64 ?_
        let Γ2 := (i64, VarKind.normal) :: Γ1
        have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
        have hlo := ArgNormal.head target Γ1 hleg64
        by_cases hlt : accBits + w < 64
        · simp only [hlt, ↓reduceIte]
          exact hk Γ2 ws (.var Γ1.length) (accBits + w) hExt2 (fun x hx => (hws x hx).mono hExt2)
            hlo
        · simp only [hlt, ↓reduceIte]
          by_cases heq : (accBits + w == 64) = true
          · simp only [heq, ↓reduceIte]
            refine hk Γ2 (ws ++ [.var Γ1.length]) (.imm 0#64) 0 hExt2 (fun x hx => ?_) hleg64
            rcases List.mem_append.1 hx with hm | hm
            · exact (hws x hm).mono hExt2
            · simp only [List.mem_singleton] at hm; subst hm; exact hlo
          · simp only [heq, Bool.false_eq_true, ↓reduceIte]
            refine isLegal_let_op2_normal target (.lshr i64) leaf (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, h64]) (hleaf.mono hExt2) hleg64 hleg64 ?_
            let Γ3 := (i64, VarKind.normal) :: Γ2
            have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
            refine hk Γ3 (ws ++ [.var Γ1.length]) (.var Γ2.length) (accBits + w - 64) hExt3
              (fun x hx => ?_) (ArgNormal.head target Γ2 hleg64)
            rcases List.mem_append.1 hx with hm | hm
            · exact (hws x hm).mono hExt3
            · simp only [List.mem_singleton] at hm; subst hm; exact hlo.mono (CtxExtends.cons _ _)

theorem packLeavesToWords64_go_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ (u : Ty) {Γ : List (Ty × VarKind)} (xs : Tup (Arg K) (target.leafTys u))
      (ws : List (Arg K i64)) (acc : Arg K i64) (accBits : Nat),
      target.supportsTy u = true →
      ArgsNormal target Γ xs → (∀ x ∈ ws, ArgNormal target Γ i64 x) → ArgNormal target Γ i64 acc →
      ∀ {k : List (Arg K i64) → Arg K i64 → Nat → Expr K KL rs},
      (∀ Γ' ws' acc' bits', CtxExtends Γ Γ' →
        (∀ x ∈ ws', ArgNormal target Γ' i64 x) → ArgNormal target Γ' i64 acc' →
        (toTFlat (k ws' acc' bits') Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (packLeavesToWords64.go target u xs ws acc accBits k) Γ.length Δ.length).isLegal
        target Γ Δ = true
  | .bool, Γ, (b, ()), ws, acc, accBits, _, hxs, hws, hacc, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [packLeavesToWords64.go]
    refine isLegal_let_op1_normal target (.ofBool 64) b _ rfl
      (by simp [LegalTarget.isLegalOp, h64]) hxs.1 hleg64 ?_
    exact pushLeafWord64_isLegal target h64 1 (.var Γ.length) ws acc accBits
      (ArgNormal.head target Γ hleg64) (fun x hx => (hws x hx).mono (CtxExtends.cons _ _))
      (hacc.mono (CtxExtends.cons _ _)) fun Γ' ws' acc' bits' hExt hws' hacc' =>
        hk Γ' ws' acc' bits' ((CtxExtends.cons _ _).trans hExt) hws' hacc'
  | .bits n, Γ, (x, ()), ws, acc, accBits, hsupp, hxs, hws, hacc, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hw := widenWidth_mem_of_supports hsupp
    have hw64 := widenWidth_le_64_of_supports hv hsupp
    simp only [packLeavesToWords64.go]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hk Γ ws acc accBits (CtxExtends.refl Γ) hws hacc
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      split
      · next heq =>
        exact pushLeafWord64_isLegal target h64 (min n 64) (castArgBits heq x) ws acc accBits
          (ArgNormal.cast heq hxs.1) hws hacc hk
      · next hne =>
        have hlt : target.widenWidth n < 64 := Nat.lt_of_le_of_ne hw64 hne
        simp only [hlt, ↓reduceIte]
        refine isLegal_let_op1_normal target (.zext (target.widenWidth n) 64) x _ rfl
          (by simp [LegalTarget.isLegalOp, hw, h64, hlt]) hxs.1 hleg64 ?_
        exact pushLeafWord64_isLegal target h64 n (.var Γ.length) ws acc accBits
          (ArgNormal.head target Γ hleg64) (fun z hz => (hws z hz).mono (CtxExtends.cons _ _))
          (hacc.mono (CtxExtends.cons _ _)) fun Γ' ws' acc' bits' hExt hws' hacc' =>
            hk Γ' ws' acc' bits' ((CtxExtends.cons _ _).trans hExt) hws' hacc'
  | .float f, Γ, (x, ()), ws, acc, accBits, hsupp, hxs, hws, hacc, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hsuppf : f ∈ target.floatFmts ∧ f.width ≤ 64 := by
      simpa [LegalTarget.supportsTy] using hsupp
    have hf := hsuppf.1
    have ⟨hfw, hfw64⟩ := valid_float_spec hv hf
    have hlegFw : target.isLegalTy (.bits f.width) = true := by
      simpa [LegalTarget.isLegalTy] using hfw
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [packLeavesToWords64.go]
    refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) x _ rfl
      (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) hxs.1 hlegFw ?_
    let Γ1 := (.bits f.width, VarKind.normal) :: Γ
    have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
    have hbi := ArgNormal.head target Γ hlegFw
    split
    · next heq =>
      exact pushLeafWord64_isLegal target h64 64 (castArgBits heq (.var Γ.length)) ws acc accBits
        (ArgNormal.cast heq hbi) (fun z hz => (hws z hz).mono hExt1) (hacc.mono hExt1)
        fun Γ' ws' acc' bits' hExt hws' hacc' => hk Γ' ws' acc' bits' (hExt1.trans hExt) hws' hacc'
    · next hne =>
      have hlt : f.width < 64 := Nat.lt_of_le_of_ne hfw64 hne
      simp only [hlt, ↓reduceIte]
      refine isLegal_let_op1_normal target (.zext f.width 64) (.var Γ.length) _ rfl
        (by simp [LegalTarget.isLegalOp, hfw, h64, hlt]) hbi hleg64 ?_
      let Γ2 := (i64, VarKind.normal) :: Γ1
      have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
      exact pushLeafWord64_isLegal target h64 f.width (.var Γ1.length) ws acc accBits
        (ArgNormal.head target Γ1 hleg64) (fun z hz => (hws z hz).mono hExt2) (hacc.mono hExt2)
        fun Γ' ws' acc' bits' hExt hws' hacc' => hk Γ' ws' acc' bits' (hExt2.trans hExt) hws' hacc'
  | .pair a b, Γ, xs, ws, acc, accBits, hsupp, hxs, hws, hacc, k, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hsupp
    obtain ⟨hfa, hfb⟩ := ArgsNormal_tupSplit hxs
    simp only [packLeavesToWords64.go]
    refine packLeavesToWords64_go_isLegal target hv a _ ws acc accBits hsupp.1 hfa hws hacc
      fun Γ1 ws1 acc1 bits1 hExt1 hws1 hacc1 => ?_
    refine packLeavesToWords64_go_isLegal target hv b _ ws1 acc1 bits1 hsupp.2 (hfb.mono hExt1) hws1
      hacc1
      fun Γ2 ws2 acc2 bits2 hExt2 hws2 hacc2 => ?_
    exact hk Γ2 ws2 acc2 bits2 (hExt1.trans hExt2) hws2 hacc2

theorem packLeavesToWords64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (t : Ty) {Γ : List (Ty × VarKind)}
    (ht : target.supportsTy t = true) (leaves : Tup (Arg K) (target.leafTys t))
    (hl : ArgsNormal target Γ leaves) {k : List (Arg K i64) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' ws => ∀ w ∈ ws, ArgNormal target Γ' i64 w) k) :
    (toTFlat (packLeavesToWords64 target t leaves k) Γ.length Δ.length).isLegal target Γ Δ = true :=
      by
  have h64 := valid_mem64 hv
  have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
  simp only [packLeavesToWords64]
  refine packLeavesToWords64_go_isLegal target hv t leaves [] (.imm 0#64) 0 ht hl
    (fun _ hx => by cases hx) hleg64 fun Γ' ws' acc' bits' hExt hws' hacc' => ?_
  by_cases hb0 : (bits' == 0) = true
  · simp only [hb0, ↓reduceIte]; exact hk Γ' ws' hExt hws'
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    refine hk Γ' (ws' ++ [acc']) hExt fun x hx => ?_
    rcases List.mem_append.1 hx with hm | hm
    · exact hws' x hm
    · simp only [List.mem_singleton] at hm; subst hm; exact hacc'

theorem extractBitsFromWords64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h64 : 64 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (words : List (Arg K i64)) (hwords : ∀ w ∈ words, ArgNormal target Γ i64 w)
    (off w : Nat) {k : Arg K i64 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i64 r) k) :
    (toTFlat (extractBitsFromWords64 words off w k) Γ.length Δ.length).isLegal target Γ Δ = true :=
      by
  have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
  simp only [extractBitsFromWords64]
  by_cases hw0 : (w == 0) = true
  · simp only [hw0, ↓reduceIte]; exact hk Γ (.imm 0#64) (CtxExtends.refl Γ) hleg64
  · simp only [hw0, Bool.false_eq_true, ↓reduceIte]
    have hw0n := ArgNormal_getD_i64 target h64 words hwords (off / 64)
    have tail_ok : ∀ {Γ1 : List (Ty × VarKind)} (lo : Arg K i64),
        CtxExtends Γ Γ1 → ArgNormal target Γ1 i64 lo →
        (toTFlat (if off % 64 + w ≤ 64 then emitMaskToN w 64 lo k
          else .let_
            (op2 (.shl i64) (words.getD (off / 64 + 1) (.imm 0#64))
            (.imm (BitVec.ofNat 64 (64 - off % 64))))
            fun (hi, ()) => .let_ (op2 (.or i64) lo (.var hi)) fun (comb, ()) =>
              emitMaskToN w 64 (.var comb) k)
          Γ1.length Δ.length).isLegal target Γ1 Δ = true := by
      intro Γ1 lo hExt1 hlo
      by_cases hle : off % 64 + w ≤ 64
      · simp only [hle, ↓reduceIte]
        exact emitMaskToN_isLegal target h64 lo hlo fun Γ2 r hExt2 hr =>
          hk Γ2 r (hExt1.trans hExt2) hr
      · simp only [hle, ↓reduceIte]
        have hw1n := (ArgNormal_getD_i64 target h64 words hwords (off / 64 + 1)).mono hExt1
        refine isLegal_let_op2_normal target (.shl i64) _ (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) hw1n hleg64 hleg64 ?_
        let Γ2 := (i64, VarKind.normal) :: Γ1
        have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.or i64) lo (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) (hlo.mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ1 hleg64) hleg64 ?_
        let Γ3 := (i64, VarKind.normal) :: Γ2
        have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
        exact emitMaskToN_isLegal target h64 (.var Γ2.length) (ArgNormal.head target Γ2 hleg64)
          fun Γ4 r hExt4 hr => hk Γ4 r (hExt3.trans hExt4) hr
    by_cases hs0 : (off % 64 == 0) = true
    · simp only [hs0, ↓reduceIte];
        exact tail_ok (words.getD (off / 64) (.imm 0#64)) (CtxExtends.refl Γ) hw0n
    · simp only [hs0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.lshr i64) (words.getD (off / 64) (.imm 0#64)) (.imm _)
        _ rfl
        (by simp [LegalTarget.isLegalOp, h64]) hw0n hleg64 hleg64 ?_
      exact tail_ok (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg64)

theorem unpackWords64ToLeaves_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ {Γ : List (Ty × VarKind)} (words : List (Arg K i64)),
      (∀ w ∈ words, ArgNormal target Γ i64 w) →
      ∀ (off : Nat) (u : Ty), target.supportsTy u = true →
      ∀ {k : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (unpackWords64ToLeaves target words off u k) Γ.length Δ.length).isLegal target Γ Δ =
        true
  | Γ, words, hwords, off, .bool, _, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [unpackWords64ToLeaves]
    refine extractBitsFromWords64_isLegal target h64 words hwords off 1 fun Γ1 raw hExt1 hraw => ?_
    refine isLegal_let_op2_normal target (.ne i64) raw (.imm 0#64) _ rfl
      (by simp [LegalTarget.isLegalOp, h64]) hraw hleg64 rfl ?_
    exact hk _ (.var Γ1.length, ()) (hExt1.trans (CtxExtends.cons _ _))
      ⟨ArgNormal.head target Γ1 rfl, trivial⟩
  | Γ, words, hwords, off, .bits n, hsupp, k, hk => by
    have h64 := valid_mem64 hv
    have hw := widenWidth_mem_of_supports hsupp
    have hw64 := widenWidth_le_64_of_supports hv hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [unpackWords64ToLeaves]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hk Γ (.imm 0#_, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine extractBitsFromWords64_isLegal target h64 words hwords off (min n 64) fun Γ1 raw hExt1
        hraw => ?_
      split
      · next heq =>
          exact hk Γ1 (castArgBits heq.symm raw, ()) hExt1 ⟨ArgNormal.cast heq.symm hraw, trivial⟩
      · next hne =>
        have hlt : target.widenWidth n < 64 := Nat.lt_of_le_of_ne hw64 hne
        simp only [hlt, ↓reduceIte]
        refine isLegal_let_op1_normal target (.trunc 64 (target.widenWidth n)) raw _ rfl
          (by simp [LegalTarget.isLegalOp, h64, hw, hlt]) hraw hlegW ?_
        exact hk _ (.var Γ1.length, ()) (hExt1.trans (CtxExtends.cons _ _))
          ⟨ArgNormal.head target Γ1 hlegW, trivial⟩
  | Γ, words, hwords, off, .float f, hsupp, k, hk => by
    have h64 := valid_mem64 hv
    have hsuppf : f ∈ target.floatFmts ∧ f.width ≤ 64 := by
      simpa [LegalTarget.supportsTy] using hsupp
    have hf := hsuppf.1
    have ⟨hfw, hfw64⟩ := valid_float_spec hv hf
    have hlegFw : target.isLegalTy (.bits f.width) = true := by
      simpa [LegalTarget.isLegalTy] using hfw
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [unpackWords64ToLeaves]
    refine extractBitsFromWords64_isLegal target h64 words hwords off (min f.width 64) fun Γ1 raw
      hExt1 hraw => ?_
    split
    · next heq =>
      refine isLegal_let_op1_normal target (.bitcast (.bits 64) (.float f) _) raw _ rfl
        (by simp [LegalTarget.isLegalOp, hleg64, hlegF, bne_iff_ne]) hraw hlegF ?_
      exact hk _ (.var Γ1.length, ()) (hExt1.trans (CtxExtends.cons _ _))
        ⟨ArgNormal.head target Γ1 hlegF, trivial⟩
    · next hne =>
      have hlt : f.width < 64 := Nat.lt_of_le_of_ne hfw64 hne
      simp only [hlt, ↓reduceIte]
      refine isLegal_let_op1_normal target (.trunc 64 f.width) raw _ rfl
        (by simp [LegalTarget.isLegalOp, h64, hfw, hlt]) hraw hlegFw ?_
      let Γ2 := (.bits f.width, VarKind.normal) :: Γ1
      refine isLegal_let_op1_normal target (.bitcast (.bits f.width) (.float f) rfl)
        (.var Γ1.length) _ rfl
        (by simp [LegalTarget.isLegalOp, hlegFw, hlegF, bne_iff_ne])
          (ArgNormal.head target Γ1 hlegFw) hlegF ?_
      exact hk _ (.var Γ2.length, ())
        (hExt1.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
        ⟨ArgNormal.head target Γ2 hlegF, trivial⟩
  | Γ, words, hwords, off, .pair a b, hsupp, k, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hsupp
    simp only [unpackWords64ToLeaves]
    refine unpackWords64ToLeaves_isLegal target hv words hwords off a hsupp.1 fun Γ1 fa hExt1 hfa =>
      ?_
    refine unpackWords64ToLeaves_isLegal target hv words (fun w hw => (hwords w hw).mono hExt1)
      (off + a.size) b hsupp.2 fun Γ2 fb hExt2 hfb => ?_
    exact hk Γ2 (tupAppend fa fb) (hExt1.trans hExt2) (ArgsNormal_tupAppend (hfa.mono hExt2) hfb)

theorem loadByteChunksToWords64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ {Γ : List (Ty × VarKind)} (ptr : Arg K i64) (byteOff : Nat) (cs : List Nat)
      (ws : List (Arg K i64)) (acc : Arg K i64) (accBits : Nat),
      ArgNormal target Γ i64 ptr →
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths) →
      (∀ x ∈ ws, ArgNormal target Γ i64 x) → ArgNormal target Γ i64 acc →
      ∀ {k : List (Arg K i64) → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' ws' => ∀ x ∈ ws', ArgNormal target Γ' i64 x) k →
      (toTFlat (loadByteChunksToWords64 ptr byteOff cs ws acc accBits k) Γ.length Δ.length).isLegal
        target Γ Δ = true
  | Γ, ptr, byteOff, [], ws, acc, accBits, _, _, hws, hacc, k, hk => by
    simp only [loadByteChunksToWords64]
    by_cases hb0 : (accBits == 0) = true
    · simp only [hb0, ↓reduceIte]; exact hk Γ ws (CtxExtends.refl Γ) hws
    · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
      refine hk Γ (ws ++ [acc]) (CtxExtends.refl Γ) fun x hx => ?_
      rcases List.mem_append.1 hx with hm | hm
      · exact hws x hm
      · simp only [List.mem_singleton] at hm; subst hm; exact hacc
  | Γ, ptr, byteOff, c :: cs, ws, acc, accBits, hptr, hcs, hws, hacc, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hcw : 8 * c ∈ target.bitWidths := (hcs c (by simp)).2
    have hcw64 : 8 * c ≤ 64 := (valid_bitWidth_spec hv hcw).2.2
    have hlegCw : target.isLegalTy (.bits (8 * c)) = true := by
      simpa [LegalTarget.isLegalTy] using hcw
    simp only [loadByteChunksToWords64]
    have afterAddr : ∀ {Γ1 : List (Ty × VarKind)} (ap : Arg K i64),
        CtxExtends Γ Γ1 → ArgNormal target Γ1 i64 ap →
        (toTFlat (.load (.bits (8 * c)) ap fun raw =>
          if h : 8 * c = 64 then
            pushLeafWord64 (min (8 * c) 64) (castArgBits h (.var raw)) ws acc accBits
              fun ws' acc' bits' => loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k
          else if 8 * c < 64 then
            .let_ (op1 (.zext (8 * c) 64) (.var raw)) fun (z, ()) =>
              pushLeafWord64 (min (8 * c) 64) (.var z) ws acc accBits
                fun ws' acc' bits' => loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k
          else
            .let_ (op1 (.trunc (8 * c) 64) (.var raw)) fun (z, ()) =>
              pushLeafWord64 (min (8 * c) 64) (.var z) ws acc accBits
                fun ws' acc' bits' => loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k)
          Γ1.length Δ.length).isLegal target Γ1 Δ = true := by
      intro Γ1 ap hExt1 hap
      refine isLegal_load_normal target (.bits (8 * c)) ap _ hlegCw hap ?_
      let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
      have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
      have hraw := ArgNormal.head target Γ1 hlegCw
      have afterWd : ∀ {Γ3 : List (Ty × VarKind)} (wd : Arg K i64),
          CtxExtends Γ2 Γ3 → ArgNormal target Γ3 i64 wd →
          (toTFlat (pushLeafWord64 (min (8 * c) 64) wd ws acc accBits fun ws' acc' bits' =>
            loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k)
              Γ3.length Δ.length).isLegal target Γ3 Δ = true := by
        intro Γ3 wd hExt3 hwd
        have hExt13 : CtxExtends Γ Γ3 := hExt2.trans hExt3
        refine pushLeafWord64_isLegal target h64 (min (8 * c) 64) wd ws acc accBits hwd
          (fun x hx => (hws x hx).mono hExt13) (hacc.mono hExt13)
          fun Γ4 ws' acc' bits' hExt4 hws' hacc' => ?_
        have hExt14 : CtxExtends Γ Γ4 := hExt13.trans hExt4
        exact loadByteChunksToWords64_isLegal target hv ptr (byteOff + c) cs ws' acc' bits'
          (hptr.mono hExt14) (fun x hx => hcs x (by simp [hx])) hws' hacc'
          fun Γ5 res hExt5 hres => hk Γ5 res (hExt14.trans hExt5) hres
      dsimp only
      split
      · next heq =>
          exact afterWd (castArgBits heq (.var Γ1.length)) (CtxExtends.refl Γ2)
            (ArgNormal.cast heq hraw)
      · next hne =>
        have hlt : 8 * c < 64 := Nat.lt_of_le_of_ne hcw64 hne
        simp only [hlt, ↓reduceIte]
        refine isLegal_let_op1_normal target (.zext (8 * c) 64) (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hcw, h64, hlt]) hraw hleg64 ?_
        exact afterWd (.var Γ2.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ2 hleg64)
    by_cases hbo : (byteOff == 0) = true
    · simp only [hbo, ↓reduceIte]; exact afterAddr ptr (CtxExtends.refl Γ) hptr
    · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, h64]) hptr hleg64 hleg64 ?_
      exact afterAddr (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg64)

theorem storeByteChunksFromWords64_isLegal (target : LegalTarget) {Δ : List (List Ty)}
  {rs : List Ty}
    (hv : target.valid = true) :
    ∀ {Γ : List (Ty × VarKind)} (words : List (Arg K i64)) (ptr : Arg K i64) (byteOff : Nat)
      (cs : List Nat) {k : Expr K KL rs},
      (∀ w ∈ words, ArgNormal target Γ i64 w) → ArgNormal target Γ i64 ptr →
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths) →
      (∀ Γ', CtxExtends Γ Γ' → (toTFlat k Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (storeByteChunksFromWords64 words ptr byteOff cs k) Γ.length Δ.length).isLegal target
        Γ Δ = true
  | Γ, _, _, _, [], _, _, _, _, hk => hk Γ (CtxExtends.refl Γ)
  | Γ, words, ptr, byteOff, c :: cs, k, hwords, hptr, hcs, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hcw : 8 * c ∈ target.bitWidths := (hcs c (by simp)).2
    have hcw64 : 8 * c ≤ 64 := (valid_bitWidth_spec hv hcw).2.2
    have hlegCw : target.isLegalTy (.bits (8 * c)) = true := by
      simpa [LegalTarget.isLegalTy] using hcw
    simp only [storeByteChunksFromWords64]
    refine extractBitsFromWords64_isLegal target h64 words hwords (8 * byteOff) (min (8 * c) 64)
      fun Γ1 raw hExt1 hraw => ?_
    have afterVal : ∀ {Γ2 : List (Ty × VarKind)} (val : Arg K (.bits (8 * c))),
        CtxExtends Γ1 Γ2 → ArgNormal target Γ2 (.bits (8 * c)) val →
        (toTFlat
          (if byteOff == 0 then .store (t := .bits (8 * c)) val ptr
          (storeByteChunksFromWords64 words ptr (byteOff + c) cs k)
          else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) =>
            .store (t := .bits (8 * c)) val (.var ap)
              (storeByteChunksFromWords64 words ptr (byteOff + c) cs k))
          Γ2.length Δ.length).isLegal target Γ2 Δ = true := by
      intro Γ2 val hExt2 hval
      have hExt12 : CtxExtends Γ Γ2 := hExt1.trans hExt2
      have storeAt : ∀ {Γ3 : List (Ty × VarKind)} (ap : Arg K i64),
          CtxExtends Γ2 Γ3 → ArgNormal target Γ3 i64 ap →
          (toTFlat
            (.store (t := .bits (8 * c)) val ap
            (storeByteChunksFromWords64 words ptr (byteOff + c) cs k))
            Γ3.length Δ.length).isLegal target Γ3 Δ = true := by
        intro Γ3 ap hExt3 hap
        have hExt13 : CtxExtends Γ Γ3 := hExt12.trans hExt3
        refine isLegal_store_normal target (.bits (8 * c)) val ap _ hlegCw (hval.mono hExt3) hap ?_
        exact storeByteChunksFromWords64_isLegal target hv words ptr (byteOff + c) cs
          (fun w hw => (hwords w hw).mono hExt13) (hptr.mono hExt13)
            (fun x hx => hcs x (by simp [hx]))
          (fun Γ4 hExt34 => hk Γ4 (hExt13.trans hExt34))
      by_cases hbo : (byteOff == 0) = true
      · simp only [hbo, ↓reduceIte]; exact storeAt ptr (CtxExtends.refl Γ2) (hptr.mono hExt12)
      · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt12) hleg64 hleg64 ?_
        exact storeAt (.var Γ2.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ2 hleg64)
    split
    · next heq =>
        exact afterVal (castArgBits heq.symm raw) (CtxExtends.refl Γ1)
          (ArgNormal.cast heq.symm hraw)
    · next hne =>
      have hlt : 8 * c < 64 := Nat.lt_of_le_of_ne hcw64 hne
      simp only [hlt, ↓reduceIte]
      refine isLegal_let_op1_normal target (.trunc 64 (8 * c)) raw _ rfl
        (by simp [LegalTarget.isLegalOp, h64, hcw, hlt]) hraw hlegCw ?_
      exact afterVal (.var Γ1.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ1 hlegCw)

theorem emitLoadBits_go_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {n w : Nat} (hw : w ∈ target.bitWidths) :
    ∀ {Γ : List (Ty × VarKind)} (ptr : Arg K i64) (byteOff : Nat) (cs : List Nat)
      (acc : Option (Arg K (.bits w))) {k : Arg K (.bits w) → Expr K KL rs},
      ArgNormal target Γ i64 ptr →
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths) →
      (∀ v, acc = some v → ArgNormal target Γ (.bits w) v) →
      IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k →
      (toTFlat (emitLoadBits.go n w ptr k byteOff cs acc) Γ.length Δ.length).isLegal target Γ Δ =
        true
  | Γ, ptr, byteOff, [], acc, k, _, _, hacc, hk => by
    have hlegW : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [emitLoadBits.go]
    cases acc with
    | none => exact hk Γ (.imm 0#w) (CtxExtends.refl Γ) hlegW
    | some v => exact emitMaskToN_isLegal target hw v (hacc v rfl) hk
  | Γ, ptr, byteOff, c :: rest, acc, k, hptr, hcs, hacc, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hlegW : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
    have hcw : 8 * c ∈ target.bitWidths := (hcs c (by simp)).2
    have hlegCw : target.isLegalTy (.bits (8 * c)) = true := by
      simpa [LegalTarget.isLegalTy] using hcw
    simp only [emitLoadBits.go]
    have afterSv : ∀ {Γ4 : List (Ty × VarKind)} (sv : Arg K (.bits w)),
        CtxExtends Γ Γ4 → ArgNormal target Γ4 (.bits w) sv →
        (acc = none →
          (toTFlat (emitLoadBits.go n w ptr k (byteOff + c) rest (some sv)) Γ4.length
          Δ.length).isLegal target Γ4 Δ = true) ∧
        (∀ prev, acc = some prev → (toTFlat (.let_ (op2 (.or (.bits w)) prev sv) fun (u, ()) =>
          emitLoadBits.go n w ptr k (byteOff + c) rest (some (.var u))) Γ4.length Δ.length).isLegal
            target Γ4 Δ = true) := by
      intro Γ4 sv hExt14 hsv
      refine ⟨fun hnone => ?_, fun prev hsome => ?_⟩
      · exact emitLoadBits_go_isLegal target hv hw ptr (byteOff + c) rest (some sv)
          (hptr.mono hExt14) (fun x hx => hcs x (by simp [hx]))
          (fun v hv' => by injection hv' with hv'; subst hv'; exact hsv)
          (fun Γ5 r hExt5 hr => hk Γ5 r (hExt14.trans hExt5) hr)
      · refine isLegal_let_op2_normal target (.or (.bits w)) prev sv _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ((hacc prev hsome).mono hExt14) hsv hlegW ?_
        let Γ5 := (.bits w, VarKind.normal) :: Γ4
        have hExt15 : CtxExtends Γ Γ5 := hExt14.trans (CtxExtends.cons _ _)
        exact emitLoadBits_go_isLegal target hv hw ptr (byteOff + c) rest (some (.var Γ4.length))
          (hptr.mono hExt15) (fun x hx => hcs x (by simp [hx]))
          (fun v hv' => by injection hv' with hv'; subst hv'; exact ArgNormal.head target Γ4 hlegW)
          (fun Γ6 r hExt6 hr => hk Γ6 r (hExt15.trans hExt6) hr)
    cases acc with
    | none =>
      have finishSv : ∀ {Γ4 : List (Ty × VarKind)} (sv : Arg K (.bits w)),
          CtxExtends Γ Γ4 → ArgNormal target Γ4 (.bits w) sv →
          (toTFlat (emitLoadBits.go n w ptr k (byteOff + c) rest (some sv)) Γ4.length
            Δ.length).isLegal target Γ4 Δ = true :=
        fun sv hExt hsv => (afterSv sv hExt hsv).1 rfl
      by_cases hbo : (byteOff == 0) = true
      · simp only [hbo, ↓reduceIte]
        refine isLegal_load_normal target (.bits (8 * c)) ptr _ hlegCw hptr ?_
        let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ
        have hraw := ArgNormal.head target Γ hlegCw
        split
        · next heq =>
            exact finishSv (castArgBits heq (.var Γ.length)) (CtxExtends.cons _ _)
              (ArgNormal.cast heq hraw)
        · next hne =>
          by_cases hlt : 8 * c < w
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (8 * c) w) (.var Γ.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hlt]) hraw hlegW ?_
            exact finishSv (.var Γ2.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
              (ArgNormal.head target Γ2 hlegW)
          · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
            simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (8 * c) w) (.var Γ.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hgt]) hraw hlegW ?_
            exact finishSv (.var Γ2.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
              (ArgNormal.head target Γ2 hlegW)
      · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) hptr hleg64 hleg64 ?_
        let Γ1 := (i64, VarKind.normal) :: Γ
        refine isLegal_load_normal target (.bits (8 * c)) (.var Γ.length) _ hlegCw
          (ArgNormal.head target Γ hleg64) ?_
        let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
        have hExt12 : CtxExtends Γ Γ2 := (CtxExtends.cons _ _).trans (CtxExtends.cons _ _)
        have hraw := ArgNormal.head target Γ1 hlegCw
        split
        · next heq =>
          refine isLegal_let_op2_normal target (.shl (.bits w)) (castArgBits heq (.var Γ1.length))
            (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.cast heq hraw) hlegW hlegW ?_
          exact finishSv (.var Γ2.length) (hExt12.trans (CtxExtends.cons _ _))
            (ArgNormal.head target Γ2 hlegW)
        · next hne =>
          by_cases hlt : 8 * c < w
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (8 * c) w) (.var Γ1.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hlt]) hraw hlegW ?_
            let Γ3 := (.bits w, VarKind.normal) :: Γ2
            refine isLegal_let_op2_normal target (.shl (.bits w)) (.var Γ2.length) (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ2 hlegW) hlegW hlegW ?_
            exact finishSv (.var Γ3.length)
              (hExt12.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
              (ArgNormal.head target Γ3 hlegW)
          · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
            simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (8 * c) w) (.var Γ1.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hgt]) hraw hlegW ?_
            let Γ3 := (.bits w, VarKind.normal) :: Γ2
            refine isLegal_let_op2_normal target (.shl (.bits w)) (.var Γ2.length) (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ2 hlegW) hlegW hlegW ?_
            exact finishSv (.var Γ3.length)
              (hExt12.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
              (ArgNormal.head target Γ3 hlegW)
    | some prev =>
      have finishSv : ∀ {Γ4 : List (Ty × VarKind)} (sv : Arg K (.bits w)),
          CtxExtends Γ Γ4 → ArgNormal target Γ4 (.bits w) sv →
          (toTFlat (.let_ (op2 (.or (.bits w)) prev sv) fun (u, ()) =>
            emitLoadBits.go n w ptr k (byteOff + c) rest (some (.var u))) Γ4.length
              Δ.length).isLegal target Γ4 Δ = true :=
        fun sv hExt hsv => (afterSv sv hExt hsv).2 prev rfl
      by_cases hbo : (byteOff == 0) = true
      · simp only [hbo, ↓reduceIte]
        refine isLegal_load_normal target (.bits (8 * c)) ptr _ hlegCw hptr ?_
        let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ
        have hraw := ArgNormal.head target Γ hlegCw
        split
        · next heq =>
            exact finishSv (castArgBits heq (.var Γ.length)) (CtxExtends.cons _ _)
              (ArgNormal.cast heq hraw)
        · next hne =>
          by_cases hlt : 8 * c < w
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (8 * c) w) (.var Γ.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hlt]) hraw hlegW ?_
            exact finishSv (.var Γ2.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
              (ArgNormal.head target Γ2 hlegW)
          · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
            simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (8 * c) w) (.var Γ.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hgt]) hraw hlegW ?_
            exact finishSv (.var Γ2.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
              (ArgNormal.head target Γ2 hlegW)
      · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) hptr hleg64 hleg64 ?_
        let Γ1 := (i64, VarKind.normal) :: Γ
        refine isLegal_load_normal target (.bits (8 * c)) (.var Γ.length) _ hlegCw
          (ArgNormal.head target Γ hleg64) ?_
        let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
        have hExt12 : CtxExtends Γ Γ2 := (CtxExtends.cons _ _).trans (CtxExtends.cons _ _)
        have hraw := ArgNormal.head target Γ1 hlegCw
        split
        · next heq =>
          refine isLegal_let_op2_normal target (.shl (.bits w)) (castArgBits heq (.var Γ1.length))
            (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.cast heq hraw) hlegW hlegW ?_
          exact finishSv (.var Γ2.length) (hExt12.trans (CtxExtends.cons _ _))
            (ArgNormal.head target Γ2 hlegW)
        · next hne =>
          by_cases hlt : 8 * c < w
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (8 * c) w) (.var Γ1.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hlt]) hraw hlegW ?_
            let Γ3 := (.bits w, VarKind.normal) :: Γ2
            refine isLegal_let_op2_normal target (.shl (.bits w)) (.var Γ2.length) (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ2 hlegW) hlegW hlegW ?_
            exact finishSv (.var Γ3.length)
              (hExt12.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
              (ArgNormal.head target Γ3 hlegW)
          · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
            simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (8 * c) w) (.var Γ1.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hgt]) hraw hlegW ?_
            let Γ3 := (.bits w, VarKind.normal) :: Γ2
            refine isLegal_let_op2_normal target (.shl (.bits w)) (.var Γ2.length) (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ2 hlegW) hlegW hlegW ?_
            exact finishSv (.var Γ3.length)
              (hExt12.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
              (ArgNormal.head target Γ3 hlegW)

theorem emitLoadBits_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {n w : Nat} (hw : w ∈ target.bitWidths)
    {Γ : List (Ty × VarKind)} (ptr : Arg K i64) (hptr : ArgNormal target Γ i64 ptr)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitLoadBits target.bitWidths n w ptr k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
  have hlegW : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
  simp only [emitLoadBits]
  by_cases hb0 : ((n + 7) / 8 == 0) = true
  · simp only [hb0, ↓reduceIte]; exact hk Γ (.imm 0#w) (CtxExtends.refl Γ) hlegW
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    refine emitLoadBits_go_isLegal target hv hw ptr 0 _ none hptr ?_ (fun _ h => by cases h) hk
    exact (chunkBytes_pos_mem_sum target.bitWidths (valid_mem8 hv) ((n + 7) / 8)).1

theorem emitStoreBits_go_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {w : Nat} (hw : w ∈ target.bitWidths) :
    ∀ {Γ : List (Ty × VarKind)} (v : Arg K (.bits w)) (ptr : Arg K i64) (byteOff : Nat)
      (cs : List Nat) {k : Expr K KL rs},
      ArgNormal target Γ (.bits w) v → ArgNormal target Γ i64 ptr →
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths) →
      (∀ Γ', CtxExtends Γ Γ' → (toTFlat k Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (emitStoreBits.go w v ptr k byteOff cs) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, _, _, _, [], _, _, _, _, hk => hk Γ (CtxExtends.refl Γ)
  | Γ, v, ptr, byteOff, c :: rest, k, hvarg, hptr, hcs, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hlegW : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
    have hcw : 8 * c ∈ target.bitWidths := (hcs c (by simp)).2
    have hlegCw : target.isLegalTy (.bits (8 * c)) = true := by
      simpa [LegalTarget.isLegalTy] using hcw
    simp only [emitStoreBits.go]
    have storeAt : ∀ {Γ3 : List (Ty × VarKind)} (val : Arg K (.bits (8 * c))) (ap : Arg K i64),
        CtxExtends Γ Γ3 → ArgNormal target Γ3 (.bits (8 * c)) val → ArgNormal target Γ3 i64 ap →
        (toTFlat
          (.store (t := .bits (8 * c)) val ap (emitStoreBits.go w v ptr k (byteOff + c) rest))
          Γ3.length Δ.length).isLegal target Γ3 Δ = true := by
      intro Γ3 val ap hExt13 hval hap
      refine isLegal_store_normal target (.bits (8 * c)) val ap _ hlegCw hval hap ?_
      exact emitStoreBits_go_isLegal target hv hw v ptr (byteOff + c) rest
        (hvarg.mono hExt13) (hptr.mono hExt13) (fun x hx => hcs x (by simp [hx]))
        (fun Γ4 hExt34 => hk Γ4 (hExt13.trans hExt34))
    by_cases hbo : (byteOff == 0) = true
    · simp only [hbo, ↓reduceIte]
      split
      · next heq =>
          exact storeAt (castArgBits heq.symm v) ptr (CtxExtends.refl Γ)
            (ArgNormal.cast heq.symm hvarg) hptr
      · next hne =>
        by_cases hlt : 8 * c < w
        · simp only [hlt, ↓reduceIte]
          refine isLegal_let_op1_normal target (.trunc w (8 * c)) v _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hcw, hlt]) hvarg hlegCw ?_
          exact storeAt (.var Γ.length) ptr (CtxExtends.cons _ _) (ArgNormal.head target Γ hlegCw)
            (hptr.mono (CtxExtends.cons _ _))
        · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
          simp only [hlt, ↓reduceIte]
          refine isLegal_let_op1_normal target (.zext w (8 * c)) v _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hcw, hgt]) hvarg hlegCw ?_
          exact storeAt (.var Γ.length) ptr (CtxExtends.cons _ _) (ArgNormal.head target Γ hlegCw)
            (hptr.mono (CtxExtends.cons _ _))
    · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.lshr (.bits w)) v (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) hvarg hlegW hlegW ?_
      let Γ1 := (.bits w, VarKind.normal) :: Γ
      have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
      have hsv := ArgNormal.head target Γ hlegW
      split
      · next heq =>
        refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt1) hleg64 hleg64 ?_
        let Γ2 := (i64, VarKind.normal) :: Γ1
        exact storeAt (castArgBits heq.symm (.var Γ.length)) (.var Γ1.length)
          (hExt1.trans (CtxExtends.cons _ _))
          ((ArgNormal.cast heq.symm hsv).mono (CtxExtends.cons _ _))
            (ArgNormal.head target Γ1 hleg64)
      · next hne =>
        by_cases hlt : 8 * c < w
        · simp only [hlt, ↓reduceIte]
          refine isLegal_let_op1_normal target (.trunc w (8 * c)) (.var Γ.length) _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hcw, hlt]) hsv hlegCw ?_
          let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
          have hExt12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
          refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt12) hleg64 hleg64 ?_
          let Γ3 := (i64, VarKind.normal) :: Γ2
          exact storeAt (.var Γ1.length) (.var Γ2.length) (hExt12.trans (CtxExtends.cons _ _))
            ((ArgNormal.head target Γ1 hlegCw).mono (CtxExtends.cons _ _))
              (ArgNormal.head target Γ2 hleg64)
        · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
          simp only [hlt, ↓reduceIte]
          refine isLegal_let_op1_normal target (.zext w (8 * c)) (.var Γ.length) _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hcw, hgt]) hsv hlegCw ?_
          let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
          have hExt12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
          refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt12) hleg64 hleg64 ?_
          let Γ3 := (i64, VarKind.normal) :: Γ2
          exact storeAt (.var Γ1.length) (.var Γ2.length) (hExt12.trans (CtxExtends.cons _ _))
            ((ArgNormal.head target Γ1 hlegCw).mono (CtxExtends.cons _ _))
              (ArgNormal.head target Γ2 hleg64)

theorem emitStoreBits_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {n w : Nat} (hw : w ∈ target.bitWidths)
    {Γ : List (Ty × VarKind)} (v : Arg K (.bits w)) (ptr : Arg K i64) {k : Expr K KL rs}
    (hvarg : ArgNormal target Γ (.bits w) v) (hptr : ArgNormal target Γ i64 ptr)
    (hk : ∀ Γ', CtxExtends Γ Γ' → (toTFlat k Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (emitStoreBits target.bitWidths n w v ptr k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
  simp only [emitStoreBits]
  by_cases hb0 : ((n + 7) / 8 == 0) = true
  · simp only [hb0, ↓reduceIte]; exact hk Γ (CtxExtends.refl Γ)
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    refine emitStoreBits_go_isLegal target hv hw v ptr 0 _ hvarg hptr ?_ hk
    exact (chunkBytes_pos_mem_sum target.bitWidths (valid_mem8 hv) ((n + 7) / 8)).1

theorem legalLoad_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)} (ptr : Arg K i64),
      target.supportsTy t = true → ArgNormal target Γ i64 ptr →
      ∀ {k : LVar target K t → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalLoad target t ptr k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, ptr, _, hptr, k, hk => by
    simp only [legalLoad]
    refine isLegal_load_normal target .bool ptr _ rfl hptr ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ rfl, trivial⟩
  | .bits n, Γ, ptr, hsupp, hptr, k, hk => by
    have hw := widenWidth_mem_of_supports hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalLoad]
    by_cases hnw : (n == target.widenWidth n) = true
    · simp only [hnw, ↓reduceIte]
      refine isLegal_load_normal target (.bits (target.widenWidth n)) ptr _ hlegW hptr ?_
      exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
    · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
      exact emitLoadBits_isLegal target hv hw ptr hptr fun Γ' r hExt hr =>
        hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .float f, Γ, ptr, hsupp, hptr, k, hk => by
    have hsuppf : f ∈ target.floatFmts ∧ f.width ≤ 64 := by
      simpa [LegalTarget.supportsTy] using hsupp
    have hf := hsuppf.1
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalLoad]
    refine isLegal_load_normal target (.float f) ptr _ hlegF hptr ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
  | .pair a b, Γ, ptr, hsupp, hptr, k, hk => by
    have hsupp' := hsupp
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hsupp'
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [legalLoad]
    split
    · next hp =>
      have hlegP : target.isLegalTy (.pair a b) = true := hp
      refine isLegal_load_normal target (.pair a b) ptr _ hlegP hptr ?_
      exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
        (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hlegP, trivial⟩)
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      split
      · refine legalLoad_isLegal target hv a ptr hsupp'.1 hptr fun Γ1 la hExt1 hla => ?_
        have afterPtr2 : ∀ {Γ2 : List (Ty × VarKind)} (p2 : Arg K i64),
            CtxExtends Γ1 Γ2 → ArgNormal target Γ2 i64 p2 →
            (toTFlat (legalLoad target b p2 fun lb => k (tupToSplit hf (tupAppend la lb)))
              Γ2.length Δ.length).isLegal target Γ2 Δ = true := by
          intro Γ2 p2 hExt2 hp2
          have hExt12 := hExt1.trans hExt2
          exact legalLoad_isLegal target hv b p2 hsupp'.2 hp2 fun Γ3 lb hExt3 hlb =>
            hk Γ3 (tupToSplit hf (tupAppend la lb)) (hExt12.trans hExt3)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hla.mono hExt2 |>.mono hExt3) hlb))
        by_cases hab : (a.bytes == 0) = true
        · simp only [hab, ↓reduceIte]; exact afterPtr2 ptr (CtxExtends.refl Γ1) (hptr.mono hExt1)
        · simp only [hab, Bool.false_eq_true, ↓reduceIte]
          refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt1) hleg64 hleg64 ?_
          exact afterPtr2 (.var Γ1.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ1 hleg64)
      · by_cases hb0 : ((a.pair b).bytes == 0) = true
        · simp only [hb0, ↓reduceIte]
          refine unpackWords64ToLeaves_isLegal target hv [] (fun _ h => by cases h) 0 (.pair a b)
            hsupp
            fun Γ1 fres hExt1 hfres => ?_
          exact packLeavesToLegal_isLegal target (.pair a b) fres hfres
            fun Γ2 res hExt2 hres => hk Γ2 res (hExt1.trans hExt2) hres
        · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
          refine loadByteChunksToWords64_isLegal target hv ptr 0 _ [] (.imm 0#64) 0 hptr ?_
            (fun _ h => by cases h) hleg64 fun Γ1 words hExt1 hwords => ?_
          · exact (chunkBytes_pos_mem_sum target.bitWidths (valid_mem8 hv) (a.pair b).bytes).1
          · refine unpackWords64ToLeaves_isLegal target hv words hwords 0 (.pair a b) hsupp
              fun Γ2 fres hExt2 hfres => ?_
            exact packLeavesToLegal_isLegal target (.pair a b) fres hfres
              fun Γ3 res hExt3 hres => hk Γ3 res ((hExt1.trans hExt2).trans hExt3) hres

theorem legalStore_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)} (v : LVar target K t) (ptr : Arg K i64) {k : Expr K KL rs},
      target.supportsTy t = true → ArgsNormal target Γ v → ArgNormal target Γ i64 ptr →
      (∀ Γ', CtxExtends Γ Γ' → (toTFlat k Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (legalStore target t v ptr k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, (v, ()), ptr, k, _, hvarg, hptr, hk => by
    simp only [legalStore]
    exact isLegal_store_normal target .bool v ptr k rfl hvarg.1 hptr (hk Γ (CtxExtends.refl Γ))
  | .bits n, Γ, (v, ()), ptr, k, hsupp, hvarg, hptr, hk => by
    have hw := widenWidth_mem_of_supports hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalStore]
    by_cases hnw : (n == target.widenWidth n) = true
    · simp only [hnw, ↓reduceIte]
      exact isLegal_store_normal target (.bits (target.widenWidth n)) v ptr k hlegW hvarg.1 hptr
        (hk Γ (CtxExtends.refl Γ))
    · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
      exact emitStoreBits_isLegal target hv hw v ptr hvarg.1 hptr hk
  | .float f, Γ, (v, ()), ptr, k, hsupp, hvarg, hptr, hk => by
    have hsuppf : f ∈ target.floatFmts ∧ f.width ≤ 64 := by
      simpa [LegalTarget.supportsTy] using hsupp
    have hf := hsuppf.1
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalStore]
    exact isLegal_store_normal target (.float f) v ptr k hlegF hvarg.1 hptr
      (hk Γ (CtxExtends.refl Γ))
  | .pair a b, Γ, xs, ptr, k, hsupp, hxs, hptr, hk => by
    have hsupp' := hsupp
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hsupp'
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [legalStore]
    split
    · next hp =>
      have hlegP : target.isLegalTy (.pair a b) = true := hp
      exact isLegal_store_normal target (.pair a b) (packedToTup hp xs).1 ptr k hlegP
        (ArgsNormal_packedToTup hp hxs).1 hptr (hk Γ (CtxExtends.refl Γ))
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      split
      · obtain ⟨hla, hlb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
        refine legalStore_isLegal target hv a (tupSplit (splitToTup hf xs)).1 ptr hsupp'.1 hla hptr
          fun Γ1 hExt1 => ?_
        by_cases hab : (a.bytes == 0) = true
        · simp only [hab, ↓reduceIte]
          exact legalStore_isLegal target hv b (tupSplit (splitToTup hf xs)).2 ptr hsupp'.2
            (hlb.mono hExt1) (hptr.mono hExt1)
            fun Γ2 hExt2 => hk Γ2 (hExt1.trans hExt2)
        · simp only [hab, Bool.false_eq_true, ↓reduceIte]
          refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt1) hleg64 hleg64 ?_
          let Γ2 := (i64, VarKind.normal) :: Γ1
          have hExt12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
          exact legalStore_isLegal target hv b (tupSplit (splitToTup hf xs)).2 (.var Γ1.length)
            hsupp'.2 (hlb.mono hExt12)
            (ArgNormal.head target Γ1 hleg64) fun Γ3 hExt3 => hk Γ3 (hExt12.trans hExt3)
      · by_cases hb0 : ((a.pair b).bytes == 0) = true
        · simp only [hb0, ↓reduceIte]; exact hk Γ (CtxExtends.refl Γ)
        · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
          refine splitLegalToLeaves_isLegal target (.pair a b) xs hxs fun Γ1 fx hExt1 hfx => ?_
          refine packLeavesToWords64_isLegal target hv (.pair a b) hsupp fx hfx
            fun Γ2 words hExt2 hwords => ?_
          have hExt12 := hExt1.trans hExt2
          refine storeByteChunksFromWords64_isLegal target hv words ptr 0 _ hwords
            (hptr.mono hExt12) ?_
            fun Γ3 hExt3 => hk Γ3 (hExt12.trans hExt3)
          exact (chunkBytes_pos_mem_sum target.bitWidths (valid_mem8 hv) (a.pair b).bytes).1

theorem legalFloatBit2_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true)
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (hmkOp : ∀ w unif, w ∈ target.bitWidths → target.isLegalOp (mkOp w) unif = true)
    (hmkFOp : ∀ f unif, target.scalarFloatBitwise = true → f ∈ target.floatFmts →
      target.isLegalOp (mkFOp f) unif = true)
    (hmkNe : ∀ w, (mkOp w).isPackBridge = false)
    (hmkFNe : ∀ f, (mkFOp f).isPackBridge = false)
    {Γ : List (Ty × VarKind)} (f : Fmt) (hf : f ∈ target.floatFmts)
    (x y : Arg K (.float f)) (hx : ArgNormal target Γ (.float f) x)
      (hy : ArgNormal target Γ (.float f) y)
    {k : Arg K (.float f) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.float f) r) k) :
    (toTFlat (legalFloatBit2 target mkOp mkFOp f x y k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
  have ⟨hfw, _⟩ := valid_float_spec hv hf
  have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
  have hlegFw : target.isLegalTy (.bits f.width) = true := by
    simpa [LegalTarget.isLegalTy] using hfw
  simp only [legalFloatBit2]
  by_cases hsb : target.scalarFloatBitwise = true
  · simp only [hsb, ↓reduceIte]
    refine isLegal_let_op2_normal target (mkFOp f) x y _ (hmkFNe f) (hmkFOp f _ hsb hf) hx hy hlegF
      ?_
    exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hlegF)
  · simp only [hsb, Bool.false_eq_true, ↓reduceIte]
    refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) x _ rfl
      (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) hx hlegFw ?_
    let Γ1 := (.bits f.width, VarKind.normal) :: Γ
    have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
    refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) y _ rfl
      (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) (hy.mono hExt1) hlegFw ?_
    let Γ2 := (.bits f.width, VarKind.normal) :: Γ1
    have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
    refine isLegal_let_op2_normal target (mkOp f.width) (.var Γ.length) (.var Γ1.length) _
      (hmkNe f.width)
      (hmkOp f.width _ hfw)
      ((ArgNormal.head target Γ hlegFw).mono (CtxExtends.cons _ _))
        (ArgNormal.head target Γ1 hlegFw) hlegFw ?_
    let Γ3 := (.bits f.width, VarKind.normal) :: Γ2
    have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
    refine isLegal_let_op1_normal target (.bitcast (.bits f.width) (.float f) rfl) (.var Γ2.length)
      _ rfl
      (by simp [LegalTarget.isLegalOp, hlegFw, hlegF, bne_iff_ne]) (ArgNormal.head target Γ2 hlegFw)
        hlegF ?_
    exact hk _ (.var Γ3.length) (hExt3.trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ3 hlegF)


end LegalIsLegal

end LeanQbe.T
