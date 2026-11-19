module

public import LeanQbe.T.LegalCheck1

/-!
# Target legality proofs for `LeanQbe.T.Legal` (Part 2: Scalarized SIMD/SHA & Tree Lifters)

Proves `TFlat.isLegal` for scalarized 128-bit SIMD and SHA-256 helpers, generic unary/binary/
ternary/cmp/select/blend/fcmp tree lifters, and explicit 128-bit shuffle/blendw/alignr/shufb.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalIsLegal

/-! ### Scalarized 128-bit SIMD & SHA-256 legality -/

theorem ArgNormal_getD_i8 (target : LegalTarget) {Γ : List (Ty × VarKind)} (h8 : 8 ∈ target.bitWidths)
    (bs : List (Arg K i8)) (hbs : ∀ x ∈ bs, ArgNormal target Γ i8 x) (i : Nat) :
    ArgNormal target Γ i8 (bs.getD i (.imm 0#8)) := by
  have hleg8 : target.isLegalTy i8 = true := by simpa [LegalTarget.isLegalTy] using h8
  induction bs generalizing i with
  | nil => simp [List.getD]; exact hleg8
  | cons b bs ih =>
    cases i with
    | zero => exact hbs b (by simp)
    | succ i => exact ih (fun x hx => hbs x (by simp [hx])) i

theorem CtxExtends.cons' {α : Type} {Γ Γ' : List α} (p : α) (h : CtxExtends Γ Γ') :
    CtxExtends Γ (p :: Γ') :=
  h.trans (CtxExtends.cons p Γ')

theorem words2ToDwords4_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) (h64 : 64 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (w0 w1 : Arg K i64) (hw0 : ArgNormal target Γ i64 w0) (hw1 : ArgNormal target Γ i64 w1)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' d0 d1 d2 d3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 d0 → ArgNormal target Γ' i32 d1 →
      ArgNormal target Γ' i32 d2 → ArgNormal target Γ' i32 d3 →
      (toTFlat (k d0 d1 d2 d3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (words2ToDwords4 w0 w1 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
  have hlt : 32 < 64 := by decide
  simp only [words2ToDwords4]
  refine isLegal_let_op1_normal target (.trunc 64 32) w0 _ rfl
    (by simp [LegalTarget.isLegalOp, h64, h32, hlt]) hw0 hleg32 ?_
  let Γ1 := (i32, VarKind.normal) :: Γ
  have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
  refine isLegal_let_op2_normal target (.lshr i64) w0 (.imm 32#64) _ rfl
    (by simp [LegalTarget.isLegalOp, h64]) (hw0.mono hExt1) hleg64 hleg64 ?_
  let Γ2 := (i64, VarKind.normal) :: Γ1
  have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.trunc 64 32) (.var Γ1.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h64, h32, hlt]) (ArgNormal.head target Γ1 hleg64) hleg32 ?_
  let Γ3 := (i32, VarKind.normal) :: Γ2
  have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.trunc 64 32) w1 _ rfl
    (by simp [LegalTarget.isLegalOp, h64, h32, hlt]) (hw1.mono hExt3) hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have hExt4 : CtxExtends Γ Γ4 := hExt3.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.lshr i64) w1 (.imm 32#64) _ rfl
    (by simp [LegalTarget.isLegalOp, h64]) (hw1.mono hExt4) hleg64 hleg64 ?_
  let Γ5 := (i64, VarKind.normal) :: Γ4
  have hExt5 : CtxExtends Γ Γ5 := hExt4.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.trunc 64 32) (.var Γ4.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h64, h32, hlt]) (ArgNormal.head target Γ4 hleg64) hleg32 ?_
  let Γ6 := (i32, VarKind.normal) :: Γ5
  have hExt6 : CtxExtends Γ Γ6 := hExt5.trans (CtxExtends.cons _ _)
  have hd0 : ArgNormal target Γ6 i32 (.var Γ.length) := (ArgNormal.head target Γ hleg32).mono ⟨[_, _, _, _, _], rfl⟩
  have hd1 : ArgNormal target Γ6 i32 (.var Γ2.length) := (ArgNormal.head target Γ2 hleg32).mono ⟨[_, _, _], rfl⟩
  have hd2 : ArgNormal target Γ6 i32 (.var Γ3.length) := (ArgNormal.head target Γ3 hleg32).mono ⟨[_, _], rfl⟩
  have hd3 := ArgNormal.head target Γ5 hleg32
  exact hk Γ6 (.var Γ.length) (.var Γ2.length) (.var Γ3.length) (.var Γ5.length) hExt6 hd0 hd1 hd2 hd3

theorem dwords4ToWords2_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) (h64 : 64 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (d0 d1 d2 d3 : Arg K i32)
    (hd0 : ArgNormal target Γ i32 d0) (hd1 : ArgNormal target Γ i32 d1)
    (hd2 : ArgNormal target Γ i32 d2) (hd3 : ArgNormal target Γ i32 d3)
    {k : Arg K i64 → Arg K i64 → Expr K KL rs}
    (hk : ∀ Γ' w0 w1, CtxExtends Γ Γ' → ArgNormal target Γ' i64 w0 → ArgNormal target Γ' i64 w1 →
      (toTFlat (k w0 w1) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (dwords4ToWords2 d0 d1 d2 d3 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
  have hlt : 32 < 64 := by decide
  simp only [dwords4ToWords2]
  refine isLegal_let_op1_normal target (.zext 32 64) d0 _ rfl (by simp [LegalTarget.isLegalOp, h32, h64, hlt]) hd0 hleg64 ?_
  let Γ1 := (i64, VarKind.normal) :: Γ
  have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
  refine isLegal_let_op1_normal target (.zext 32 64) d1 _ rfl (by simp [LegalTarget.isLegalOp, h32, h64, hlt]) (hd1.mono hExt1) hleg64 ?_
  let Γ2 := (i64, VarKind.normal) :: Γ1
  have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i64) (.var Γ1.length) (.imm 32#64) _ rfl
    (by simp [LegalTarget.isLegalOp, h64]) (ArgNormal.head target Γ1 hleg64) hleg64 hleg64 ?_
  let Γ3 := (i64, VarKind.normal) :: Γ2
  have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i64) (.var Γ.length) (.var Γ2.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h64]) ((ArgNormal.head target Γ hleg64).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ2 hleg64) hleg64 ?_
  let Γ4 := (i64, VarKind.normal) :: Γ3
  have hExt4 : CtxExtends Γ Γ4 := hExt3.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.zext 32 64) d2 _ rfl (by simp [LegalTarget.isLegalOp, h32, h64, hlt]) (hd2.mono hExt4) hleg64 ?_
  let Γ5 := (i64, VarKind.normal) :: Γ4
  have hExt5 : CtxExtends Γ Γ5 := hExt4.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.zext 32 64) d3 _ rfl (by simp [LegalTarget.isLegalOp, h32, h64, hlt]) (hd3.mono hExt5) hleg64 ?_
  let Γ6 := (i64, VarKind.normal) :: Γ5
  have hExt6 : CtxExtends Γ Γ6 := hExt5.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i64) (.var Γ5.length) (.imm 32#64) _ rfl
    (by simp [LegalTarget.isLegalOp, h64]) (ArgNormal.head target Γ5 hleg64) hleg64 hleg64 ?_
  let Γ7 := (i64, VarKind.normal) :: Γ6
  have hExt7 : CtxExtends Γ Γ7 := hExt6.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i64) (.var Γ4.length) (.var Γ6.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h64]) ((ArgNormal.head target Γ4 hleg64).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ6 hleg64) hleg64 ?_
  let Γ8 := (i64, VarKind.normal) :: Γ7
  have hExt8 : CtxExtends Γ Γ8 := hExt7.trans (CtxExtends.cons _ _)
  have hw0 : ArgNormal target Γ8 i64 (.var Γ3.length) := (ArgNormal.head target Γ3 hleg64).mono ⟨[_, _, _, _], rfl⟩
  exact hk Γ8 (.var Γ3.length) (.var Γ7.length) hExt8 hw0 (ArgNormal.head target Γ7 hleg64)

theorem dwordToBytes4_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (d : Arg K i32) (hd : ArgNormal target Γ i32 d)
    {k : Arg K i8 → Arg K i8 → Arg K i8 → Arg K i8 → Expr K KL rs}
    (hk : ∀ Γ' b0 b1 b2 b3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i8 b0 → ArgNormal target Γ' i8 b1 →
      ArgNormal target Γ' i8 b2 → ArgNormal target Γ' i8 b3 →
      (toTFlat (k b0 b1 b2 b3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (dwordToBytes4 d k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg8 : target.isLegalTy i8 = true := by simpa [LegalTarget.isLegalTy] using h8
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  have hlt : 8 < 32 := by decide
  simp only [dwordToBytes4]
  refine isLegal_let_op1_normal target (.trunc 32 8) d _ rfl (by simp [LegalTarget.isLegalOp, h32, h8, hlt]) hd hleg8 ?_
  let Γ1 := (i8, VarKind.normal) :: Γ
  have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
  refine isLegal_let_op2_normal target (.lshr i32) d (.imm 8#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (hd.mono hExt1) hleg32 hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.trunc 32 8) (.var Γ1.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32, h8, hlt]) (ArgNormal.head target Γ1 hleg32) hleg8 ?_
  let Γ3 := (i8, VarKind.normal) :: Γ2
  have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.lshr i32) d (.imm 16#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (hd.mono hExt3) hleg32 hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have hExt4 : CtxExtends Γ Γ4 := hExt3.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.trunc 32 8) (.var Γ3.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32, h8, hlt]) (ArgNormal.head target Γ3 hleg32) hleg8 ?_
  let Γ5 := (i8, VarKind.normal) :: Γ4
  have hExt5 : CtxExtends Γ Γ5 := hExt4.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.lshr i32) d (.imm 24#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (hd.mono hExt5) hleg32 hleg32 ?_
  let Γ6 := (i32, VarKind.normal) :: Γ5
  have hExt6 : CtxExtends Γ Γ6 := hExt5.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.trunc 32 8) (.var Γ5.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32, h8, hlt]) (ArgNormal.head target Γ5 hleg32) hleg8 ?_
  let Γ7 := (i8, VarKind.normal) :: Γ6
  have hExt7 : CtxExtends Γ Γ7 := hExt6.trans (CtxExtends.cons _ _)
  have hb0 : ArgNormal target Γ7 i8 (.var Γ.length) := (ArgNormal.head target Γ hleg8).mono ⟨[_, _, _, _, _, _], rfl⟩
  have hb1 : ArgNormal target Γ7 i8 (.var Γ2.length) := (ArgNormal.head target Γ2 hleg8).mono ⟨[_, _, _, _], rfl⟩
  have hb2 : ArgNormal target Γ7 i8 (.var Γ4.length) := (ArgNormal.head target Γ4 hleg8).mono ⟨[_, _], rfl⟩
  exact hk Γ7 (.var Γ.length) (.var Γ2.length) (.var Γ4.length) (.var Γ6.length) hExt7 hb0 hb1 hb2 (ArgNormal.head target Γ6 hleg8)

theorem bytes4ToDword_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (b0 b1 b2 b3 : Arg K i8)
    (hb0 : ArgNormal target Γ i8 b0) (hb1 : ArgNormal target Γ i8 b1)
    (hb2 : ArgNormal target Γ i8 b2) (hb3 : ArgNormal target Γ i8 b3)
    {k : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' d => ArgNormal target Γ' i32 d) k) :
    (toTFlat (bytes4ToDword b0 b1 b2 b3 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  have hlt : 8 < 32 := by decide
  simp only [bytes4ToDword]
  refine isLegal_let_op1_normal target (.zext 8 32) b0 _ rfl (by simp [LegalTarget.isLegalOp, h8, h32, hlt]) hb0 hleg32 ?_
  let Γ1 := (i32, VarKind.normal) :: Γ
  have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
  refine isLegal_let_op1_normal target (.zext 8 32) b1 _ rfl (by simp [LegalTarget.isLegalOp, h8, h32, hlt]) (hb1.mono hExt1) hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i32) (.var Γ1.length) (.imm 8#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (ArgNormal.head target Γ1 hleg32) hleg32 hleg32 ?_
  let Γ3 := (i32, VarKind.normal) :: Γ2
  have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i32) (.var Γ.length) (.var Γ2.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) ((ArgNormal.head target Γ hleg32).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ2 hleg32) hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have hExt4 : CtxExtends Γ Γ4 := hExt3.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.zext 8 32) b2 _ rfl (by simp [LegalTarget.isLegalOp, h8, h32, hlt]) (hb2.mono hExt4) hleg32 ?_
  let Γ5 := (i32, VarKind.normal) :: Γ4
  have hExt5 : CtxExtends Γ Γ5 := hExt4.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i32) (.var Γ4.length) (.imm 16#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (ArgNormal.head target Γ4 hleg32) hleg32 hleg32 ?_
  let Γ6 := (i32, VarKind.normal) :: Γ5
  have hExt6 : CtxExtends Γ Γ6 := hExt5.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i32) (.var Γ3.length) (.var Γ5.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) ((ArgNormal.head target Γ3 hleg32).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ5 hleg32) hleg32 ?_
  let Γ7 := (i32, VarKind.normal) :: Γ6
  have hExt7 : CtxExtends Γ Γ7 := hExt6.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.zext 8 32) b3 _ rfl (by simp [LegalTarget.isLegalOp, h8, h32, hlt]) (hb3.mono hExt7) hleg32 ?_
  let Γ8 := (i32, VarKind.normal) :: Γ7
  have hExt8 : CtxExtends Γ Γ8 := hExt7.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i32) (.var Γ7.length) (.imm 24#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (ArgNormal.head target Γ7 hleg32) hleg32 hleg32 ?_
  let Γ9 := (i32, VarKind.normal) :: Γ8
  have hExt9 : CtxExtends Γ Γ9 := hExt8.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i32) (.var Γ6.length) (.var Γ8.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) ((ArgNormal.head target Γ6 hleg32).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ8 hleg32) hleg32 ?_
  let Γ10 := (i32, VarKind.normal) :: Γ9
  have hExt10 : CtxExtends Γ Γ10 := hExt9.trans (CtxExtends.cons _ _)
  exact hk Γ10 (.var Γ9.length) hExt10 (ArgNormal.head target Γ9 hleg32)

theorem dwords4ToBytes16_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (d0 d1 d2 d3 : Arg K i32)
    (hd0 : ArgNormal target Γ i32 d0) (hd1 : ArgNormal target Γ i32 d1)
    (hd2 : ArgNormal target Γ i32 d2) (hd3 : ArgNormal target Γ i32 d3)
    {k : List (Arg K i8) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' bs => ∀ b ∈ bs, ArgNormal target Γ' i8 b) k) :
    (toTFlat (dwords4ToBytes16 d0 d1 d2 d3 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [dwords4ToBytes16]
  refine dwordToBytes4_isLegal target h8 h32 d0 hd0 fun Γ1 b0 b1 b2 b3 hExt1 hb0 hb1 hb2 hb3 => ?_
  refine dwordToBytes4_isLegal target h8 h32 d1 (hd1.mono hExt1) fun Γ2 b4 b5 b6 b7 hExt2 hb4 hb5 hb6 hb7 => ?_
  have hExt12 := hExt1.trans hExt2
  refine dwordToBytes4_isLegal target h8 h32 d2 (hd2.mono hExt12) fun Γ3 b8 b9 b10 b11 hExt3 hb8 hb9 hb10 hb11 => ?_
  have hExt13 := hExt12.trans hExt3
  refine dwordToBytes4_isLegal target h8 h32 d3 (hd3.mono hExt13) fun Γ4 b12 b13 b14 b15 hExt4 hb12 hb13 hb14 hb15 => ?_
  have hExt24 := hExt2.trans (hExt3.trans hExt4)
  have hExt34 := hExt3.trans hExt4
  refine hk Γ4 _ (hExt13.trans hExt4) fun b hb => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hb0.mono hExt24
  · exact hb1.mono hExt24
  · exact hb2.mono hExt24
  · exact hb3.mono hExt24
  · exact hb4.mono hExt34
  · exact hb5.mono hExt34
  · exact hb6.mono hExt34
  · exact hb7.mono hExt34
  · exact hb8.mono hExt4
  · exact hb9.mono hExt4
  · exact hb10.mono hExt4
  · exact hb11.mono hExt4
  · exact hb12
  · exact hb13
  · exact hb14
  · exact hb15

theorem bytes16ToDwords4_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (bs : List (Arg K i8)) (hbs : ∀ b ∈ bs, ArgNormal target Γ i8 b)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' d0 d1 d2 d3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 d0 → ArgNormal target Γ' i32 d1 →
      ArgNormal target Γ' i32 d2 → ArgNormal target Γ' i32 d3 →
      (toTFlat (k d0 d1 d2 d3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (bytes16ToDwords4 bs k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [bytes16ToDwords4]
  have gb := fun i => ArgNormal_getD_i8 target h8 bs hbs i
  refine bytes4ToDword_isLegal target h8 h32 _ _ _ _ (gb 0) (gb 1) (gb 2) (gb 3) fun Γ1 d0 hExt1 hd0 => ?_
  have gb1 := fun i => (gb i).mono hExt1
  refine bytes4ToDword_isLegal target h8 h32 _ _ _ _ (gb1 4) (gb1 5) (gb1 6) (gb1 7) fun Γ2 d1 hExt2 hd1 => ?_
  have hExt12 := hExt1.trans hExt2
  have gb2 := fun i => (gb i).mono hExt12
  refine bytes4ToDword_isLegal target h8 h32 _ _ _ _ (gb2 8) (gb2 9) (gb2 10) (gb2 11) fun Γ3 d2 hExt3 hd2 => ?_
  have hExt13 := hExt12.trans hExt3
  have gb3 := fun i => (gb i).mono hExt13
  refine bytes4ToDword_isLegal target h8 h32 _ _ _ _ (gb3 12) (gb3 13) (gb3 14) (gb3 15) fun Γ4 d3 hExt4 hd3 => ?_
  exact hk Γ4 d0 d1 d2 d3 (hExt13.trans hExt4)
    (hd0.mono (hExt2.trans (hExt3.trans hExt4))) (hd1.mono (hExt3.trans hExt4)) (hd2.mono hExt4) hd3

theorem ArgNormal_scalarShufd128 (target : LegalTarget) {Γ : List (Ty × VarKind)} (imm : BitVec 8)
    (d0 d1 d2 d3 : Arg K i32)
    (hd0 : ArgNormal target Γ i32 d0) (hd1 : ArgNormal target Γ i32 d1)
    (hd2 : ArgNormal target Γ i32 d2) (hd3 : ArgNormal target Γ i32 d3) :
    let r := scalarShufd128 imm d0 d1 d2 d3
    ArgNormal target Γ i32 r.1 ∧ ArgNormal target Γ i32 r.2.1 ∧
    ArgNormal target Γ i32 r.2.2.1 ∧ ArgNormal target Γ i32 r.2.2.2 := by
  have hpick : ∀ i, ArgNormal target Γ i32 (match (imm.toNat >>> (2 * i)) % 4 with | 0 => d0 | 1 => d1 | 2 => d2 | _ => d3) := by
    intro i; split <;> first | exact hd0 | exact hd1 | exact hd2 | exact hd3
  exact ⟨hpick 0, hpick 1, hpick 2, hpick 3⟩

theorem scalarBlendwLane_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (imm : BitVec 8) (idx : Nat)
    (ai bi : Arg K i32) (ha : ArgNormal target Γ i32 ai) (hb : ArgNormal target Γ i32 bi)
    {cont : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) cont) :
    (toTFlat (scalarBlendwLane imm idx ai bi cont) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [scalarBlendwLane]
  cases imm.getLsbD (2 * idx) <;> cases imm.getLsbD (2 * idx + 1)
  · exact hk Γ ai (CtxExtends.refl Γ) ha
  · refine isLegal_let_op2_normal target (.and i32) ai (.imm _) _ rfl (by simp [LegalTarget.isLegalOp, h32]) ha hleg32 hleg32 ?_
    let Γ1 := (i32, VarKind.normal) :: Γ
    have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
    refine isLegal_let_op2_normal target (.and i32) bi (.imm _) _ rfl (by simp [LegalTarget.isLegalOp, h32]) (hb.mono hExt1) hleg32 hleg32 ?_
    let Γ2 := (i32, VarKind.normal) :: Γ1
    have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
    refine isLegal_let_op2_normal target (.or i32) (.var Γ.length) (.var Γ1.length) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) ((ArgNormal.head target Γ hleg32).mono (CtxExtends.cons _ _))
      (ArgNormal.head target Γ1 hleg32) hleg32 ?_
    exact hk _ (.var Γ2.length) (hExt2.trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hleg32)
  · refine isLegal_let_op2_normal target (.and i32) ai (.imm _) _ rfl (by simp [LegalTarget.isLegalOp, h32]) ha hleg32 hleg32 ?_
    let Γ1 := (i32, VarKind.normal) :: Γ
    have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
    refine isLegal_let_op2_normal target (.and i32) bi (.imm _) _ rfl (by simp [LegalTarget.isLegalOp, h32]) (hb.mono hExt1) hleg32 hleg32 ?_
    let Γ2 := (i32, VarKind.normal) :: Γ1
    have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
    refine isLegal_let_op2_normal target (.or i32) (.var Γ.length) (.var Γ1.length) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) ((ArgNormal.head target Γ hleg32).mono (CtxExtends.cons _ _))
      (ArgNormal.head target Γ1 hleg32) hleg32 ?_
    exact hk _ (.var Γ2.length) (hExt2.trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hleg32)
  · exact hk Γ bi (CtxExtends.refl Γ) hb

theorem scalarBlendw128_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (imm : BitVec 8)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Arg K i32)
    (ha0 : ArgNormal target Γ i32 a0) (ha1 : ArgNormal target Γ i32 a1)
    (ha2 : ArgNormal target Γ i32 a2) (ha3 : ArgNormal target Γ i32 a3)
    (hb0 : ArgNormal target Γ i32 b0) (hb1 : ArgNormal target Γ i32 b1)
    (hb2 : ArgNormal target Γ i32 b2) (hb3 : ArgNormal target Γ i32 b3)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' r0 r1 r2 r3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 r0 → ArgNormal target Γ' i32 r1 →
      ArgNormal target Γ' i32 r2 → ArgNormal target Γ' i32 r3 →
      (toTFlat (k r0 r1 r2 r3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (scalarBlendw128 imm a0 a1 a2 a3 b0 b1 b2 b3 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [scalarBlendw128]
  refine scalarBlendwLane_isLegal target h32 imm 0 a0 b0 ha0 hb0 fun Γ1 r0 hExt1 hr0 => ?_
  refine scalarBlendwLane_isLegal target h32 imm 1 a1 b1 (ha1.mono hExt1) (hb1.mono hExt1) fun Γ2 r1 hExt2 hr1 => ?_
  have hExt12 := hExt1.trans hExt2
  refine scalarBlendwLane_isLegal target h32 imm 2 a2 b2 (ha2.mono hExt12) (hb2.mono hExt12) fun Γ3 r2 hExt3 hr2 => ?_
  have hExt13 := hExt12.trans hExt3
  refine scalarBlendwLane_isLegal target h32 imm 3 a3 b3 (ha3.mono hExt13) (hb3.mono hExt13) fun Γ4 r3 hExt4 hr3 => ?_
  exact hk Γ4 r0 r1 r2 r3 (hExt13.trans hExt4)
    (hr0.mono (hExt2.trans (hExt3.trans hExt4))) (hr1.mono (hExt3.trans hExt4)) (hr2.mono hExt4) hr3

theorem scalarAlignr128_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (imm : BitVec 8)
    (h0 h1 h2 h3 l0 l1 l2 l3 : Arg K i32)
    (hh0 : ArgNormal target Γ i32 h0) (hh1 : ArgNormal target Γ i32 h1)
    (hh2 : ArgNormal target Γ i32 h2) (hh3 : ArgNormal target Γ i32 h3)
    (hl0 : ArgNormal target Γ i32 l0) (hl1 : ArgNormal target Γ i32 l1)
    (hl2 : ArgNormal target Γ i32 l2) (hl3 : ArgNormal target Γ i32 l3)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' r0 r1 r2 r3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 r0 → ArgNormal target Γ' i32 r1 →
      ArgNormal target Γ' i32 r2 → ArgNormal target Γ' i32 r3 →
      (toTFlat (k r0 r1 r2 r3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (scalarAlignr128 imm h0 h1 h2 h3 l0 l1 l2 l3 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg8 : target.isLegalTy i8 = true := by simpa [LegalTarget.isLegalTy] using h8
  simp only [scalarAlignr128]
  refine dwords4ToBytes16_isLegal target h8 h32 l0 l1 l2 l3 hl0 hl1 hl2 hl3 fun Γ1 lbs hExt1 hlbs => ?_
  refine dwords4ToBytes16_isLegal target h8 h32 h0 h1 h2 h3 (hh0.mono hExt1) (hh1.mono hExt1)
    (hh2.mono hExt1) (hh3.mono hExt1) fun Γ2 hbs hExt2 hhbs => ?_
  have hExt12 := hExt1.trans hExt2
  refine bytes16ToDwords4_isLegal target h8 h32 _ ?_ fun Γ3 r0 r1 r2 r3 hExt3 hr0 hr1 hr2 hr3 =>
    hk Γ3 r0 r1 r2 r3 (hExt12.trans hExt3) hr0 hr1 hr2 hr3
  intro b hb
  simp only [List.mem_map] at hb
  rcases hb with ⟨i, _, rfl⟩
  split
  · exact ArgNormal_getD_i8 target h8 lbs (fun x hx => (hlbs x hx).mono hExt2) _
  · split
    · exact ArgNormal_getD_i8 target h8 hbs hhbs _
    · exact hleg8

theorem scalarShufb128_muxBytes_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (idx : Arg K i8) :
    ∀ (bs : List (Arg K i8)) (j : Nat) {cont : Arg K i8 → Expr K KL rs},
      ArgNormal target Γ i8 idx → (∀ b ∈ bs, ArgNormal target Γ i8 b) →
      IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i8 r) cont →
      (toTFlat (scalarShufb128.muxBytes idx bs j cont) Γ.length Δ.length).isLegal target Γ Δ = true
  | [], _, cont, _, _, hcont => by
    have hleg8 : target.isLegalTy i8 = true := by simpa [LegalTarget.isLegalTy] using h8
    simp only [scalarShufb128.muxBytes]
    exact hcont Γ (.imm 0#8) (CtxExtends.refl Γ) hleg8
  | [b], _, cont, _, hbs, hcont => by
    simp only [scalarShufb128.muxBytes]
    exact hcont Γ b (CtxExtends.refl Γ) (hbs b (by simp))
  | b :: b' :: bs, j, cont, hidx, hbs, hcont => by
    have hleg8 : target.isLegalTy i8 = true := by simpa [LegalTarget.isLegalTy] using h8
    simp only [scalarShufb128.muxBytes]
    refine scalarShufb128_muxBytes_isLegal target h8 idx (b' :: bs) (j + 1) hidx
      (fun x hx => hbs x (by simp [hx])) fun Γ1 rest hExt1 hrest => ?_
    refine isLegal_let_op2_normal target (.eq i8) idx (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, h8]) (hidx.mono hExt1) hleg8 rfl ?_
    let Γ2 := (.bool, VarKind.normal) :: Γ1
    have hExt12 : CtxExtends Γ Γ2 := CtxExtends.cons' _ hExt1
    refine isLegal_let_op3_normal target (.select i8) (.var Γ1.length) b rest _ rfl
      (by simp [LegalTarget.isLegalOp, h8]) (ArgNormal.head target Γ1 rfl)
      ((hbs b (by simp)).mono hExt12) (hrest.mono (CtxExtends.cons _ _)) hleg8 ?_
    let Γ3 := (i8, VarKind.normal) :: Γ2
    exact hcont Γ3 (.var Γ2.length) (CtxExtends.cons' _ hExt12) (ArgNormal.head target Γ2 hleg8)

theorem scalarShufb128_doBytes_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) (h32 : 32 ∈ target.bitWidths)
    (k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs) :
    ∀ {Γ : List (Ty × VarKind)} (abs mbs : List (Arg K i8)) (i : Nat) (acc : List (Arg K i8)),
      (∀ b ∈ abs, ArgNormal target Γ i8 b) → (∀ b ∈ mbs, ArgNormal target Γ i8 b) →
      (∀ b ∈ acc, ArgNormal target Γ i8 b) →
      (∀ Γ' r0 r1 r2 r3, CtxExtends Γ Γ' →
        ArgNormal target Γ' i32 r0 → ArgNormal target Γ' i32 r1 →
        ArgNormal target Γ' i32 r2 → ArgNormal target Γ' i32 r3 →
        (toTFlat (k r0 r1 r2 r3) Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (scalarShufb128.doBytes k abs mbs i acc) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, abs, mbs, i, acc, habs, hmbs, hacc, hk => by
    have hleg8 : target.isLegalTy i8 = true := by simpa [LegalTarget.isLegalTy] using h8
    rw [scalarShufb128.doBytes.eq_1]
    by_cases hi : 16 ≤ i
    · simp only [hi, ↓reduceIte]
      exact bytes16ToDwords4_isLegal target h8 h32 acc hacc hk
    · simp only [hi, ↓reduceIte]
      have hmb := ArgNormal_getD_i8 target h8 mbs hmbs i
      refine isLegal_let_op2_normal target (.slt i8) _ (.imm 0#8) _ rfl
        (by simp [LegalTarget.isLegalOp, h8]) hmb hleg8 rfl ?_
      let Γ1 := (.bool, VarKind.normal) :: Γ
      have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
      refine isLegal_let_op2_normal target (.and i8) _ (.imm 15#8) _ rfl
        (by simp [LegalTarget.isLegalOp, h8]) (hmb.mono hExt1) hleg8 hleg8 ?_
      let Γ2 := (i8, VarKind.normal) :: Γ1
      have hExt12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
      refine scalarShufb128_muxBytes_isLegal target h8 (.var Γ1.length) abs 0
        (ArgNormal.head target Γ1 hleg8) (fun b hb => (habs b hb).mono hExt12)
        fun Γ3 sel hExt3 hsel => ?_
      have hExt13 : CtxExtends Γ Γ3 := hExt12.trans hExt3
      have hneg : ArgNormal target Γ3 .bool (.var Γ.length) :=
        (ArgNormal.head target Γ rfl).mono ((CtxExtends.cons (i8, VarKind.normal) Γ1).trans hExt3)
      refine isLegal_let_op3_normal target (.select i8) (.var Γ.length) (.imm 0#8) sel _ rfl
        (by simp [LegalTarget.isLegalOp, h8]) hneg hleg8 hsel hleg8 ?_
      let Γ4 := (i8, VarKind.normal) :: Γ3
      have hExt14 : CtxExtends Γ Γ4 := CtxExtends.cons' _ hExt13
      exact scalarShufb128_doBytes_isLegal target h8 h32 k abs mbs (i + 1) (acc ++ [.var Γ3.length])
        (fun b hb => (habs b hb).mono hExt14) (fun b hb => (hmbs b hb).mono hExt14)
        (fun b hb => by
          rcases List.mem_append.1 hb with hm | hm
          · exact (hacc b hm).mono hExt14
          · simp only [List.mem_singleton] at hm; subst hm; exact ArgNormal.head target Γ3 hleg8)
        fun Γ' r0 r1 r2 r3 hExt' => hk Γ' r0 r1 r2 r3 (hExt14.trans hExt')

theorem scalarShufb128_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (a0 a1 a2 a3 m0 m1 m2 m3 : Arg K i32)
    (ha0 : ArgNormal target Γ i32 a0) (ha1 : ArgNormal target Γ i32 a1)
    (ha2 : ArgNormal target Γ i32 a2) (ha3 : ArgNormal target Γ i32 a3)
    (hm0 : ArgNormal target Γ i32 m0) (hm1 : ArgNormal target Γ i32 m1)
    (hm2 : ArgNormal target Γ i32 m2) (hm3 : ArgNormal target Γ i32 m3)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' r0 r1 r2 r3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 r0 → ArgNormal target Γ' i32 r1 →
      ArgNormal target Γ' i32 r2 → ArgNormal target Γ' i32 r3 →
      (toTFlat (k r0 r1 r2 r3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (scalarShufb128 a0 a1 a2 a3 m0 m1 m2 m3 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [scalarShufb128]
  refine dwords4ToBytes16_isLegal target h8 h32 a0 a1 a2 a3 ha0 ha1 ha2 ha3 fun Γ1 abs hExt1 habs => ?_
  refine dwords4ToBytes16_isLegal target h8 h32 m0 m1 m2 m3 (hm0.mono hExt1) (hm1.mono hExt1)
    (hm2.mono hExt1) (hm3.mono hExt1) fun Γ2 mbs hExt2 hmbs => ?_
  have hExt12 := hExt1.trans hExt2
  exact scalarShufb128_doBytes_isLegal target h8 h32 k abs mbs 0 []
    (fun b hb => (habs b hb).mono hExt2) hmbs (fun _ h => by cases h)
    fun Γ' r0 r1 r2 r3 hExt' => hk Γ' r0 r1 r2 r3 (hExt12.trans hExt')

section ShaIsLegal

theorem emitShaMix3_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (thirdLshr : Bool)
    (n1 n2 n3 : Nat) (x : Arg K i32)
    (hx : ArgNormal target Γ i32 x) {k : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) k) :
    (toTFlat (emitShaMix3 thirdLshr n1 n2 n3 x k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [emitShaMix3, emitRotr32, emitXor32]
  refine isLegal_let_op2_normal target (.rotr i32) x (.imm _) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) hx hleg32 hleg32 ?_
  let Γ1 := (i32, VarKind.normal) :: Γ
  refine isLegal_let_op2_normal target (.rotr i32) x (.imm _) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (hx.mono ⟨[_], rfl⟩) hleg32 hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  let Γ3 := (i32, VarKind.normal) :: Γ2
  let Γ4 := (i32, VarKind.normal) :: Γ3
  let Γ5 := (i32, VarKind.normal) :: Γ4
  have hXorTail :
      (toTFlat (.let_ (op2 (.xor i32) (.var Γ.length) (.var Γ1.length)) fun (t, ()) =>
        .let_ (op2 (.xor i32) (.var t) (.var Γ2.length)) fun (r', ()) => k (.var r'))
        Γ3.length Δ.length).isLegal target Γ3 Δ = true := by
    refine isLegal_let_op2_normal target (.xor i32) (.var Γ.length) (.var Γ1.length) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) ((ArgNormal.head target Γ hleg32).mono ⟨[_, _], rfl⟩)
      ((ArgNormal.head target Γ1 hleg32).mono ⟨[_], rfl⟩) hleg32 ?_
    refine isLegal_let_op2_normal target (.xor i32) (.var Γ3.length) (.var Γ2.length) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) (ArgNormal.head target Γ3 hleg32)
      ((ArgNormal.head target Γ2 hleg32).mono ⟨[_], rfl⟩) hleg32 ?_
    exact hk Γ5 (.var Γ4.length) ⟨[_, _, _, _, _], rfl⟩ (ArgNormal.head target Γ4 hleg32)
  cases thirdLshr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact isLegal_let_op2_normal target (.rotr i32) x (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) (hx.mono ⟨[_, _], rfl⟩) hleg32 hleg32 hXorTail
  · simp only [↓reduceIte]
    exact isLegal_let_op2_normal target (.lshr i32) x (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) (hx.mono ⟨[_, _], rfl⟩) hleg32 hleg32 hXorTail

theorem emitShaSigma0_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (x : Arg K i32)
    (hx : ArgNormal target Γ i32 x) {k : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) k) :
    (toTFlat (emitShaSigma0 x k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  emitShaMix3_isLegal target h32 false 2 13 22 x hx hk

theorem emitShaSigma1_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (x : Arg K i32)
    (hx : ArgNormal target Γ i32 x) {k : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) k) :
    (toTFlat (emitShaSigma1 x k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  emitShaMix3_isLegal target h32 false 6 11 25 x hx hk

theorem emitShaSig0_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (x : Arg K i32)
    (hx : ArgNormal target Γ i32 x) {k : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) k) :
    (toTFlat (emitShaSig0 x k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  emitShaMix3_isLegal target h32 true 7 18 3 x hx hk

theorem emitShaSig1_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (x : Arg K i32)
    (hx : ArgNormal target Γ i32 x) {k : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) k) :
    (toTFlat (emitShaSig1 x k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  emitShaMix3_isLegal target h32 true 17 19 10 x hx hk

theorem emitShaCh_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (x y z : Arg K i32)
    (hx : ArgNormal target Γ i32 x) (hy : ArgNormal target Γ i32 y) (hz : ArgNormal target Γ i32 z)
    {k : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) k) :
    (toTFlat (emitShaCh x y z k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [emitShaCh, emitAnd32, emitNot32, emitXor32]
  refine isLegal_let_op2_normal target (.and i32) x y _ rfl (by simp [LegalTarget.isLegalOp, h32]) hx hy hleg32 ?_
  let Γ1 := (i32, VarKind.normal) :: Γ
  refine isLegal_let_op1_normal target (.not i32) x _ rfl (by simp [LegalTarget.isLegalOp, h32]) (hx.mono ⟨[_], rfl⟩) hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  refine isLegal_let_op2_normal target (.and i32) (.var Γ1.length) z _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ArgNormal.head target Γ1 hleg32) (hz.mono ⟨[_, _], rfl⟩) hleg32 ?_
  let Γ3 := (i32, VarKind.normal) :: Γ2
  refine isLegal_let_op2_normal target (.xor i32) (.var Γ.length) (.var Γ2.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) ((ArgNormal.head target Γ hleg32).mono ⟨[_, _], rfl⟩)
    (ArgNormal.head target Γ2 hleg32) hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  exact hk Γ4 (.var Γ3.length) ⟨[_, _, _, _], rfl⟩ (ArgNormal.head target Γ3 hleg32)

theorem emitShaMaj_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (x y z : Arg K i32)
    (hx : ArgNormal target Γ i32 x) (hy : ArgNormal target Γ i32 y) (hz : ArgNormal target Γ i32 z)
    {k : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) k) :
    (toTFlat (emitShaMaj x y z k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [emitShaMaj, emitAnd32, emitXor32]
  refine isLegal_let_op2_normal target (.and i32) x y _ rfl (by simp [LegalTarget.isLegalOp, h32]) hx hy hleg32 ?_
  let Γ1 := (i32, VarKind.normal) :: Γ
  refine isLegal_let_op2_normal target (.and i32) x z _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (hx.mono ⟨[_], rfl⟩) (hz.mono ⟨[_], rfl⟩) hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  have h12 : CtxExtends Γ Γ2 := ⟨[_, _], rfl⟩
  refine isLegal_let_op2_normal target (.and i32) y z _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (hy.mono h12) (hz.mono h12) hleg32 ?_
  let Γ3 := (i32, VarKind.normal) :: Γ2
  refine isLegal_let_op2_normal target (.xor i32) (.var Γ.length) (.var Γ1.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) ((ArgNormal.head target Γ hleg32).mono ⟨[_, _], rfl⟩)
    ((ArgNormal.head target Γ1 hleg32).mono ⟨[_], rfl⟩) hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  refine isLegal_let_op2_normal target (.xor i32) (.var Γ3.length) (.var Γ2.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (ArgNormal.head target Γ3 hleg32)
    ((ArgNormal.head target Γ2 hleg32).mono ⟨[_], rfl⟩) hleg32 ?_
  let Γ5 := (i32, VarKind.normal) :: Γ4
  exact hk Γ5 (.var Γ4.length) ⟨[_, _, _, _, _], rfl⟩ (ArgNormal.head target Γ4 hleg32)

theorem emitShaRound_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (a b c d e f g h wk : Arg K i32)
    (ha : ArgNormal target Γ i32 a) (hb : ArgNormal target Γ i32 b)
    (hc' : ArgNormal target Γ i32 c) (hd : ArgNormal target Γ i32 d)
    (he : ArgNormal target Γ i32 e) (hf : ArgNormal target Γ i32 f)
    (hg : ArgNormal target Γ i32 g) (hh : ArgNormal target Γ i32 h)
    (hwk : ArgNormal target Γ i32 wk)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' r0 r1 r2 r3 r4 r5 r6 r7, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 r0 → ArgNormal target Γ' i32 r1 →
      ArgNormal target Γ' i32 r2 → ArgNormal target Γ' i32 r3 →
      ArgNormal target Γ' i32 r4 → ArgNormal target Γ' i32 r5 →
      ArgNormal target Γ' i32 r6 → ArgNormal target Γ' i32 r7 →
      (toTFlat (k r0 r1 r2 r3 r4 r5 r6 r7) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (emitShaRound a b c d e f g h wk k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [emitShaRound, emitAdd32]
  refine emitShaCh_isLegal target h32 e f g he hf hg fun Γ1 chv hExt1 hch => ?_
  refine emitShaSigma1_isLegal target h32 e (he.mono hExt1) fun Γ2 s1 hExt2 hs1 => ?_
  have h12 : CtxExtends Γ Γ2 := hExt1.trans hExt2
  refine isLegal_let_op2_normal target (.add i32) chv s1 _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (hch.mono hExt2) hs1 hleg32 ?_
  let Γ3 := (i32, VarKind.normal) :: Γ2
  have h13 : CtxExtends Γ Γ3 := CtxExtends.cons' _ h12
  refine isLegal_let_op2_normal target (.add i32) (.var Γ2.length) wk _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ArgNormal.head target Γ2 hleg32) (hwk.mono h13) hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have h14 : CtxExtends Γ Γ4 := CtxExtends.cons' _ h13
  refine isLegal_let_op2_normal target (.add i32) (.var Γ3.length) h _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ArgNormal.head target Γ3 hleg32) (hh.mono h14) hleg32 ?_
  let Γ5 := (i32, VarKind.normal) :: Γ4
  have h15 : CtxExtends Γ Γ5 := CtxExtends.cons' _ h14
  refine emitShaMaj_isLegal target h32 a b c (ha.mono h15) (hb.mono h15) (hc'.mono h15) fun Γ6 majv hExt6 hmaj => ?_
  have h16 : CtxExtends Γ Γ6 := h15.trans hExt6
  refine emitShaSigma0_isLegal target h32 a (ha.mono h16) fun Γ7 s0 hExt7 hs0 => ?_
  have h17 : CtxExtends Γ Γ7 := h16.trans hExt7
  have htExt : CtxExtends Γ5 Γ7 := hExt6.trans hExt7
  have ht : ArgNormal target Γ7 i32 (.var Γ4.length) :=
    (ArgNormal.head target Γ4 hleg32).mono htExt
  refine isLegal_let_op2_normal target (.add i32) (.var Γ4.length) majv _ rfl (by simp [LegalTarget.isLegalOp, h32])
    ht (hmaj.mono hExt7) hleg32 ?_
  let Γ8 := (i32, VarKind.normal) :: Γ7
  have h18 : CtxExtends Γ Γ8 := CtxExtends.cons' _ h17
  refine isLegal_let_op2_normal target (.add i32) (.var Γ7.length) s0 _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ArgNormal.head target Γ7 hleg32) (hs0.mono (CtxExtends.cons _ _)) hleg32 ?_
  let Γ9 := (i32, VarKind.normal) :: Γ8
  have h19 : CtxExtends Γ Γ9 := CtxExtends.cons' _ h18
  refine isLegal_let_op2_normal target (.add i32) (.var Γ4.length) d _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ht.mono ⟨[_, _], rfl⟩) (hd.mono h19) hleg32 ?_
  let Γ10 := (i32, VarKind.normal) :: Γ9
  have h110 : CtxExtends Γ Γ10 := CtxExtends.cons' _ h19
  exact hk Γ10 (.var Γ8.length) a b c (.var Γ9.length) e f g h110
    ((ArgNormal.head target Γ8 hleg32).mono ⟨[_], rfl⟩) (ha.mono h110) (hb.mono h110) (hc'.mono h110)
    (ArgNormal.head target Γ9 hleg32) (he.mono h110) (hf.mono h110) (hg.mono h110)

theorem scalarSha256rnds2_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 : Arg K i32)
    (hcd0 : ArgNormal target Γ i32 cd0) (hcd1 : ArgNormal target Γ i32 cd1)
    (hcd2 : ArgNormal target Γ i32 cd2) (hcd3 : ArgNormal target Γ i32 cd3)
    (hab0 : ArgNormal target Γ i32 ab0) (hab1 : ArgNormal target Γ i32 ab1)
    (hab2 : ArgNormal target Γ i32 ab2) (hab3 : ArgNormal target Γ i32 ab3)
    (hwk0 : ArgNormal target Γ i32 wk0) (hwk1 : ArgNormal target Γ i32 wk1)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' r0 r1 r2 r3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 r0 → ArgNormal target Γ' i32 r1 →
      ArgNormal target Γ' i32 r2 → ArgNormal target Γ' i32 r3 →
      (toTFlat (k r0 r1 r2 r3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 k)
      Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [scalarSha256rnds2]
  refine emitShaRound_isLegal target h32 ab3 ab2 cd3 cd2 ab1 ab0 cd1 cd0 wk0
    hab3 hab2 hcd3 hcd2 hab1 hab0 hcd1 hcd0 hwk0
    fun Γ1 a1 b1 c1 d1 e1 f1 g1 h1 hExt1 ha1 hb1 hc1 hd1 he1 hf1 hg1 hh1 => ?_
  refine emitShaRound_isLegal target h32 a1 b1 c1 d1 e1 f1 g1 h1 wk1
    ha1 hb1 hc1 hd1 he1 hf1 hg1 hh1 (hwk1.mono hExt1)
    fun Γ2 a2 _ _ _ e2 _ _ _ hExt2 ha2 _ _ _ he2 _ _ _ => ?_
  exact hk Γ2 e1 e2 a1 a2 (hExt1.trans hExt2) (he1.mono hExt2) he2 (ha1.mono hExt2) ha2

theorem scalarSha256msg1_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (a0 a1 a2 a3 b0 b1 b2 b3 : Arg K i32)
    (ha0 : ArgNormal target Γ i32 a0) (ha1 : ArgNormal target Γ i32 a1)
    (ha2 : ArgNormal target Γ i32 a2) (ha3 : ArgNormal target Γ i32 a3)
    (hb0 : ArgNormal target Γ i32 b0)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' r0 r1 r2 r3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 r0 → ArgNormal target Γ' i32 r1 →
      ArgNormal target Γ' i32 r2 → ArgNormal target Γ' i32 r3 →
      (toTFlat (k r0 r1 r2 r3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [scalarSha256msg1, emitAdd32]
  refine emitShaSig0_isLegal target h32 a1 ha1 fun Γ1 s0 hExt1 hs0 => ?_
  refine isLegal_let_op2_normal target (.add i32) a0 s0 _ rfl (by simp [LegalTarget.isLegalOp, h32]) (ha0.mono hExt1) hs0 hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  have h12 : CtxExtends Γ Γ2 := CtxExtends.cons' _ hExt1
  refine emitShaSig0_isLegal target h32 a2 (ha2.mono h12) fun Γ3 s1 hExt3 hs1 => ?_
  have h13 : CtxExtends Γ Γ3 := h12.trans hExt3
  refine isLegal_let_op2_normal target (.add i32) a1 s1 _ rfl (by simp [LegalTarget.isLegalOp, h32]) (ha1.mono h13) hs1 hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have h14 : CtxExtends Γ Γ4 := CtxExtends.cons' _ h13
  refine emitShaSig0_isLegal target h32 a3 (ha3.mono h14) fun Γ5 s2 hExt5 hs2 => ?_
  have h15 : CtxExtends Γ Γ5 := h14.trans hExt5
  refine isLegal_let_op2_normal target (.add i32) a2 s2 _ rfl (by simp [LegalTarget.isLegalOp, h32]) (ha2.mono h15) hs2 hleg32 ?_
  let Γ6 := (i32, VarKind.normal) :: Γ5
  have h16 : CtxExtends Γ Γ6 := CtxExtends.cons' _ h15
  refine emitShaSig0_isLegal target h32 b0 (hb0.mono h16) fun Γ7 s3 hExt7 hs3 => ?_
  have h17 : CtxExtends Γ Γ7 := h16.trans hExt7
  refine isLegal_let_op2_normal target (.add i32) a3 s3 _ rfl (by simp [LegalTarget.isLegalOp, h32]) (ha3.mono h17) hs3 hleg32 ?_
  let Γ8 := (i32, VarKind.normal) :: Γ7
  have h18 : CtxExtends Γ Γ8 := CtxExtends.cons' _ h17
  have h68 : CtxExtends Γ6 Γ8 := hExt7.trans (CtxExtends.cons (i32, VarKind.normal) Γ7)
  have h58 : CtxExtends Γ5 Γ8 := (CtxExtends.cons (i32, VarKind.normal) Γ5).trans h68
  have h48 : CtxExtends Γ4 Γ8 := hExt5.trans h58
  have h38 : CtxExtends Γ3 Γ8 := (CtxExtends.cons (i32, VarKind.normal) Γ3).trans h48
  have h28 : CtxExtends Γ2 Γ8 := hExt3.trans h38
  have hr0 : ArgNormal target Γ8 i32 (.var Γ1.length) := (ArgNormal.head target Γ1 hleg32).mono h28
  have hr1 : ArgNormal target Γ8 i32 (.var Γ3.length) := (ArgNormal.head target Γ3 hleg32).mono h48
  have hr2 : ArgNormal target Γ8 i32 (.var Γ5.length) := (ArgNormal.head target Γ5 hleg32).mono h68
  exact hk Γ8 (.var Γ1.length) (.var Γ3.length) (.var Γ5.length) (.var Γ7.length) h18
    hr0 hr1 hr2 (ArgNormal.head target Γ7 hleg32)

theorem scalarSha256msg2_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (s0 s1 s2 s3 w0 w1 w2 w3 : Arg K i32)
    (hs0 : ArgNormal target Γ i32 s0) (hs1 : ArgNormal target Γ i32 s1)
    (hs2 : ArgNormal target Γ i32 s2) (hs3 : ArgNormal target Γ i32 s3)
    (hw2 : ArgNormal target Γ i32 w2) (hw3 : ArgNormal target Γ i32 w3)
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs}
    (hk : ∀ Γ' r0 r1 r2 r3, CtxExtends Γ Γ' →
      ArgNormal target Γ' i32 r0 → ArgNormal target Γ' i32 r1 →
      ArgNormal target Γ' i32 r2 → ArgNormal target Γ' i32 r3 →
      (toTFlat (k r0 r1 r2 r3) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [scalarSha256msg2, emitAdd32]
  refine emitShaSig1_isLegal target h32 w2 hw2 fun Γ1 sig2 hExt1 hsig2 => ?_
  refine isLegal_let_op2_normal target (.add i32) s0 sig2 _ rfl (by simp [LegalTarget.isLegalOp, h32]) (hs0.mono hExt1) hsig2 hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  have h12 : CtxExtends Γ Γ2 := CtxExtends.cons' _ hExt1
  refine emitShaSig1_isLegal target h32 w3 (hw3.mono h12) fun Γ3 sig3 hExt3 hsig3 => ?_
  have h13 : CtxExtends Γ Γ3 := h12.trans hExt3
  refine isLegal_let_op2_normal target (.add i32) s1 sig3 _ rfl (by simp [LegalTarget.isLegalOp, h32]) (hs1.mono h13) hsig3 hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have h14 : CtxExtends Γ Γ4 := CtxExtends.cons' _ h13
  refine emitShaSig1_isLegal target h32 (.var Γ1.length) ((ArgNormal.head target Γ1 hleg32).mono (hExt3.trans (CtxExtends.cons (i32, VarKind.normal) Γ3)))
    fun Γ5 sig16 hExt5 hsig16 => ?_
  have h15 : CtxExtends Γ Γ5 := h14.trans hExt5
  refine isLegal_let_op2_normal target (.add i32) s2 sig16 _ rfl (by simp [LegalTarget.isLegalOp, h32]) (hs2.mono h15) hsig16 hleg32 ?_
  let Γ6 := (i32, VarKind.normal) :: Γ5
  have h16 : CtxExtends Γ Γ6 := CtxExtends.cons' _ h15
  refine emitShaSig1_isLegal target h32 (.var Γ3.length) ((ArgNormal.head target Γ3 hleg32).mono (hExt5.trans (CtxExtends.cons (i32, VarKind.normal) Γ5)))
    fun Γ7 sig17 hExt7 hsig17 => ?_
  have h17 : CtxExtends Γ Γ7 := h16.trans hExt7
  refine isLegal_let_op2_normal target (.add i32) s3 sig17 _ rfl (by simp [LegalTarget.isLegalOp, h32]) (hs3.mono h17) hsig17 hleg32 ?_
  let Γ8 := (i32, VarKind.normal) :: Γ7
  have h18 : CtxExtends Γ Γ8 := CtxExtends.cons' _ h17
  have h68 : CtxExtends Γ6 Γ8 := hExt7.trans (CtxExtends.cons (i32, VarKind.normal) Γ7)
  have h58 : CtxExtends Γ5 Γ8 := (CtxExtends.cons (i32, VarKind.normal) Γ5).trans h68
  have h48 : CtxExtends Γ4 Γ8 := hExt5.trans h58
  have h38 : CtxExtends Γ3 Γ8 := (CtxExtends.cons (i32, VarKind.normal) Γ3).trans h48
  have h28 : CtxExtends Γ2 Γ8 := hExt3.trans h38
  have hw16 : ArgNormal target Γ8 i32 (.var Γ1.length) := (ArgNormal.head target Γ1 hleg32).mono h28
  have hw17 : ArgNormal target Γ8 i32 (.var Γ3.length) := (ArgNormal.head target Γ3 hleg32).mono h48
  have hw18 : ArgNormal target Γ8 i32 (.var Γ5.length) := (ArgNormal.head target Γ5 hleg32).mono h68
  exact hk Γ8 (.var Γ1.length) (.var Γ3.length) (.var Γ5.length) (.var Γ7.length) h18
    hw16 hw17 hw18 (ArgNormal.head target Γ7 hleg32)

end ShaIsLegal

theorem legalSimdScalar128_goWords_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) (t : Ty) (ht : target.supportsTy t = true)
    (on128 : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 →
      (Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs) → Expr K KL rs)
    (hon128 : ∀ {Γ' : List (Ty × VarKind)} (a0 a1 a2 a3 b0 b1 b2 b3 : Arg K i32)
        (k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs),
      ArgNormal target Γ' i32 a0 → ArgNormal target Γ' i32 a1 → ArgNormal target Γ' i32 a2 → ArgNormal target Γ' i32 a3 →
      ArgNormal target Γ' i32 b0 → ArgNormal target Γ' i32 b1 → ArgNormal target Γ' i32 b2 → ArgNormal target Γ' i32 b3 →
      (∀ Γ'' r0 r1 r2 r3, CtxExtends Γ' Γ'' →
        ArgNormal target Γ'' i32 r0 → ArgNormal target Γ'' i32 r1 → ArgNormal target Γ'' i32 r2 → ArgNormal target Γ'' i32 r3 →
        (toTFlat (k r0 r1 r2 r3) Γ''.length Δ.length).isLegal target Γ'' Δ = true) →
      (toTFlat (on128 a0 a1 a2 a3 b0 b1 b2 b3 k) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (k : Tup (Arg K) (target.legalTys t) → Expr K KL rs) :
    ∀ {Γ : List (Ty × VarKind)} (wx wy acc : List (Arg K i64)),
      (∀ w ∈ wx, ArgNormal target Γ i64 w) → (∀ w ∈ wy, ArgNormal target Γ i64 w) →
      (∀ w ∈ acc, ArgNormal target Γ i64 w) →
      (∀ Γ' res, CtxExtends Γ Γ' → ArgsNormal target Γ' res → (toTFlat (k res) Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (legalSimdScalar128.goWords target on128 t k wx wy acc) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, x0 :: x1 :: rxs, y0 :: y1 :: rys, acc, hwx, hwy, hacc, hk => by
    have h64 := valid_mem64 hv
    rw [legalSimdScalar128.goWords.eq_1]
    refine words2ToDwords4_isLegal target h32 h64 x0 x1 (hwx x0 (by simp)) (hwx x1 (by simp))
      fun Γ1 a0 a1 a2 a3 hExt1 ha0 ha1 ha2 ha3 => ?_
    refine words2ToDwords4_isLegal target h32 h64 y0 y1 ((hwy y0 (by simp)).mono hExt1) ((hwy y1 (by simp)).mono hExt1)
      fun Γ2 b0 b1 b2 b3 hExt2 hb0 hb1 hb2 hb3 => ?_
    have h12 := hExt1.trans hExt2
    refine hon128 a0 a1 a2 a3 b0 b1 b2 b3 _ (ha0.mono hExt2) (ha1.mono hExt2) (ha2.mono hExt2) (ha3.mono hExt2)
      hb0 hb1 hb2 hb3 fun Γ3 r0 r1 r2 r3 hExt3 hr0 hr1 hr2 hr3 => ?_
    refine dwords4ToWords2_isLegal target h32 h64 r0 r1 r2 r3 hr0 hr1 hr2 hr3 fun Γ4 w0 w1 hExt4 hw0 hw1 => ?_
    have h14 := h12.trans (hExt3.trans hExt4)
    refine legalSimdScalar128_goWords_isLegal target hv h32 t ht on128 hon128 k rxs rys (acc ++ [w0, w1])
      (fun x hx => (hwx x (by simp [hx])).mono h14) (fun y hy => (hwy y (by simp [hy])).mono h14)
      (fun w hw => by
        rcases List.mem_append.1 hw with hm | hm
        · exact (hacc w hm).mono h14
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl <;> assumption)
      (fun Γ' res hExt' => hk Γ' res (h14.trans hExt'))
  | Γ, [], wy, acc, _, _, hacc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    refine unpackWords64ToLeaves_isLegal target hv acc hacc 0 t ht fun Γ1 fres hExt1 hfres => ?_
    exact packLeavesToLegal_isLegal target t fres hfres fun Γ2 res hExt2 => hk Γ2 res (hExt1.trans hExt2)
  | Γ, [x0], wy, acc, _, _, hacc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    refine unpackWords64ToLeaves_isLegal target hv acc hacc 0 t ht fun Γ1 fres hExt1 hfres => ?_
    exact packLeavesToLegal_isLegal target t fres hfres fun Γ2 res hExt2 => hk Γ2 res (hExt1.trans hExt2)
  | Γ, x0 :: x1 :: rxs, [], acc, _, _, hacc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    refine unpackWords64ToLeaves_isLegal target hv acc hacc 0 t ht fun Γ1 fres hExt1 hfres => ?_
    exact packLeavesToLegal_isLegal target t fres hfres fun Γ2 res hExt2 => hk Γ2 res (hExt1.trans hExt2)
  | Γ, x0 :: x1 :: rxs, [y0], acc, _, _, hacc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    refine unpackWords64ToLeaves_isLegal target hv acc hacc 0 t ht fun Γ1 fres hExt1 hfres => ?_
    exact packLeavesToLegal_isLegal target t fres hfres fun Γ2 res hExt2 => hk Γ2 res (hExt1.trans hExt2)

theorem legalSimdScalar128_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths)
    (on128 : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 →
      (Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs) → Expr K KL rs)
    (hon128 : ∀ {Γ' : List (Ty × VarKind)} (a0 a1 a2 a3 b0 b1 b2 b3 : Arg K i32)
        (k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs),
      ArgNormal target Γ' i32 a0 → ArgNormal target Γ' i32 a1 → ArgNormal target Γ' i32 a2 → ArgNormal target Γ' i32 a3 →
      ArgNormal target Γ' i32 b0 → ArgNormal target Γ' i32 b1 → ArgNormal target Γ' i32 b2 → ArgNormal target Γ' i32 b3 →
      (∀ Γ'' r0 r1 r2 r3, CtxExtends Γ' Γ'' →
        ArgNormal target Γ'' i32 r0 → ArgNormal target Γ'' i32 r1 → ArgNormal target Γ'' i32 r2 → ArgNormal target Γ'' i32 r3 →
        (toTFlat (k r0 r1 r2 r3) Γ''.length Δ.length).isLegal target Γ'' Δ = true) →
      (toTFlat (on128 a0 a1 a2 a3 b0 b1 b2 b3 k) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (t : Ty) {Γ : List (Ty × VarKind)} (ht : target.supportsTy t = true)
    (xs ys : Tup (Arg K) (target.legalTys t)) (hxs : ArgsNormal target Γ xs) (hys : ArgsNormal target Γ ys)
    {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k) :
    (toTFlat (legalSimdScalar128 target on128 t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [legalSimdScalar128]
  refine splitLegalToLeaves_isLegal target t xs hxs fun Γ1 fx hExt1 hfx => ?_
  refine splitLegalToLeaves_isLegal target t ys (hys.mono hExt1) fun Γ2 fy hExt2 hfy => ?_
  have h12 := hExt1.trans hExt2
  refine packLeavesToWords64_isLegal target hv t ht fx (hfx.mono hExt2) fun Γ3 wx hExt3 hwx => ?_
  have h13 := h12.trans hExt3
  refine packLeavesToWords64_isLegal target hv t ht fy (hfy.mono hExt3) fun Γ4 wy hExt4 hwy => ?_
  have h14 := h13.trans hExt4
  exact legalSimdScalar128_goWords_isLegal target hv h32 t ht on128 hon128 k wx wy []
    (fun w hw => (hwx w hw).mono hExt4) hwy (fun _ h => by cases h)
    fun Γ' res hExt' => hk Γ' res (h14.trans hExt')

/-! ### Tree lifters & explicit 128-bit SIMD legality -/

private theorem isUniformImmShift_idxArgs_eq_aux {as bs : List Ty} (code : OpCode as bs) :
    ∀ {u : Ty} (h : as = [u, u]) (nv : Nat) (x y : Arg K u),
      isUniformImmShift code (cast (congrArg (Tup (Arg K)) h.symm)
        (show Tup (Arg K) [u, u] from (idxArg nv x, idxArg nv y, ()))) =
        checkUniformImmShift u code y := by
  intro u h nv x y
  cases code <;> (try cases h) <;> cases y <;> rfl

theorem isUniformImmShift_idxArgs_eq (u : Ty) (code : OpCode [u, u] [u])
    (nv : Nat) (x y : Arg K u) :
    isUniformImmShift code (idxArg nv x, idxArg nv y, ()) = checkUniformImmShift u code y :=
  isUniformImmShift_idxArgs_eq_aux code rfl nv x y

theorem legalUnaryTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (P : Ty → Prop) (hP_pair : ∀ a b, P (.pair a b) → P a ∧ P b)
    (mkCode : (u : Ty) → OpCode [u] [u])
    (vecSupported : (u : Ty) → Bool)
    (hmkNe : ∀ u, (mkCode u).isPackBridge = false)
    (hvecOp : ∀ a b, P (.pair a b) → target.keepsPacked (.pair a b) = true →
      vecSupported (.pair a b) = true → target.isLegalOp (mkCode (.pair a b)) false = true)
    (onBool : Arg K .bool → (Arg K .bool → Expr K KL rs) → Expr K KL rs)
    (onBits : (n : Nat) → Arg K (.bits (target.widenWidth n)) → (Arg K (.bits (target.widenWidth n)) → Expr K KL rs) → Expr K KL rs)
    (onFloat : (f : Fmt) → Arg K (.float f) → (Arg K (.float f) → Expr K KL rs) → Expr K KL rs)
    (hB : P .bool → ∀ {Γ'} (x : Arg K .bool) (cont : Arg K .bool → Expr K KL rs),
      ArgNormal target Γ' .bool x → IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (onBool x cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hBi : ∀ n, P (.bits n) → ∀ {Γ'} (x : Arg K (.bits (target.widenWidth n)))
        (cont : Arg K (.bits (target.widenWidth n)) → Expr K KL rs),
      ArgNormal target Γ' (.bits (target.widenWidth n)) x →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.bits (target.widenWidth n)) r) cont →
      (toTFlat (onBits n x cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hF : ∀ f, P (.float f) → ∀ {Γ'} (x : Arg K (.float f)) (cont : Arg K (.float f) → Expr K KL rs),
      ArgNormal target Γ' (.float f) x →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.float f) r) cont →
      (toTFlat (onFloat f x cont) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, P t →
      (xs : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalUnaryTree target mkCode vecSupported onBool onBits onFloat t xs k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, hP, (x, ()), hxs, k, hk =>
    hB hP x _ hxs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .bits n, Γ, hP, (x, ()), hxs, k, hk =>
    hBi n hP x _ hxs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .float f, Γ, hP, (x, ()), hxs, k, hk =>
    hF f hP x _ hxs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .pair t1 t2, Γ, hP, xs, hxs, k, hk => by
    obtain ⟨hP1, hP2⟩ := hP_pair t1 t2 hP
    simp only [legalUnaryTree]
    split
    · next hp =>
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · simp only [hvs, ↓reduceIte]
        have hxs' := ArgsNormal_packedToTup hp hxs
        have hunif : isUniformImmShift (mkCode (.pair t1 t2)) (idxArg Γ.length (packedToTup hp xs).1, ()) = false := by
          cases mkCode (.pair t1 t2) <;> rfl
        have hcode : target.isLegalOp (mkCode (.pair t1 t2)) false = true := hvecOp t1 t2 hP hp hvs
        refine isLegal_let_op1_normal target (mkCode (.pair t1 t2)) (packedToTup hp xs).1 _
          (hmkNe _) hcode hxs'.1 hp ?_
        exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
          (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
      · have hvsf : vecSupported (.pair t1 t2) = false := Bool.eq_false_iff.mpr hvs
        simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
        have hgoS : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, P u →
            (fxu : Tup (Arg K) (target.leafTys u)) → ArgsNormal target Γ' fxu →
            ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
            IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
            (toTFlat (legalUnaryTree.goS target onBool onBits onFloat u fxu cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
          intro u
          induction u with
          | bool => intro Γ' hPu (a, ()) ha cont hcont; exact hB hPu a _ ha.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | bits n => intro Γ' hPu (a, ()) ha cont hcont; exact hBi n hPu a _ ha.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | float f => intro Γ' hPu (a, ()) ha cont hcont; exact hF f hPu a _ ha.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | pair u1 u2 ih1 ih2 =>
            intro Γ' hPu fxu hfxu cont hcont
            obtain ⟨hPu1, hPu2⟩ := hP_pair u1 u2 hPu
            obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
            refine ih1 hPu1 _ hx1 fun Γa r1 hExta hr1 => ?_
            exact ih2 hPu2 _ (hx2.mono hExta) fun Γb r2 hExtb hr2 =>
              hcont Γb (tupAppend r1 r2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
        refine hgoS (.pair t1 t2) hP fx hfx fun Γ2 fres hExt2 hfres => ?_
        exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
          fun Γ3 res hExt3 hres => hk Γ3 res ((hExt1.trans hExt2).trans hExt3) hres
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
      refine legalUnaryTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat hB hBi hF t1 hP1 _ hx1 fun Γ1 r1 hExt1 hr1 => ?_
      refine legalUnaryTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat hB hBi hF t2 hP2 _ (hx2.mono hExt1) fun Γ2 r2 hExt2 hr2 => ?_
      exact hk Γ2 (tupToSplit hf (tupAppend r1 r2)) (hExt1.trans hExt2)
        (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hr1.mono hExt2) hr2))

theorem Ty.bswapOk_pair (a b : Ty) : (a.pair b).bswapOk = true → a.bswapOk = true ∧ b.bswapOk = true := by
  simp [Ty.bswapOk, Bool.and_eq_true]

theorem legalBswapTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalBswapTree target t xs k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro t Γ hsupp xs hxs k hk
  have h64 := valid_mem64 hv
  simp only [legalBswapTree]
  by_cases hbs : t.bswapOk = true
  · simp only [hbs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine legalUnaryTree_isLegal target (fun u => target.supportsTy u = true ∧ u.bswapOk = true)
      (fun a b h => by
        simp only [LegalTarget.supportsTy, Ty.bswapOk, Bool.and_eq_true] at h
        exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
      .bswap (fun _ => false) (fun _ => rfl) (fun _ _ _ _ hf => by cases hf)
      _ _ _ (fun h => by have h2 := h.2; simp [Ty.bswapOk] at h2) ?_
      (fun f h => by have h2 := h.2; simp [Ty.bswapOk] at h2)
      t ⟨hsupp, hbs⟩ xs hxs hk
    intro n hPn Γ' x cont hx hcont
    have hw := widenWidth_mem_of_supports hPn.1
    have hwle := le_widenWidth_of_supports hPn.1
    have ⟨_, hw8, _⟩ := valid_bitWidth_spec hv hw
    have hn8 : n % 8 = 0 := by simpa [Ty.bswapOk] using hPn.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont Γ' (.imm 0#_) (CtxExtends.refl Γ') hlegW
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hn8' : (n == 8) = true
      · simp only [hn8', ↓reduceIte]; exact hcont Γ' x (CtxExtends.refl Γ') hx
      · simp only [hn8', Bool.false_eq_true, ↓reduceIte]
        have hn16 : 16 ≤ n := by
          have hne0 : n ≠ 0 := by simpa using hn0
          have hne8 : n ≠ 8 := by simpa using hn8'
          omega
        have hw8gt : 8 < target.widenWidth n := by omega
        by_cases hnw : (n == target.widenWidth n) = true
        · simp only [hnw, ↓reduceIte]
          refine isLegal_let_op1_normal target (.bswap (.bits (target.widenWidth n))) x _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hw8, hw8gt]) hx hlegW ?_
          exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegW)
        · simp only [hnw, Bool.false_eq_true, ↓reduceIte, hw8, beq_iff_eq, ↓reduceIte]
          refine isLegal_let_op1_normal target (.bswap (.bits (target.widenWidth n))) x _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hw8, hw8gt]) hx hlegW ?_
          let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ'
          refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) (.var Γ'.length) (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ' hlegW) hlegW hlegW ?_
          let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
          exact hcont Γ2 (.var Γ1.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
            (ArgNormal.head target Γ1 hlegW)
  · have hbsf : t.bswapOk = false := Bool.eq_false_iff.mpr hbs
    simp [hbsf, toTFlat_hlt]

theorem legalTernaryTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (P : Ty → Prop) (hP_pair : ∀ a b, P (.pair a b) → P a ∧ P b)
    (mkCode : (u : Ty) → OpCode [u, u, u] [u])
    (vecSupported : (u : Ty) → Bool)
    (hmkNe : ∀ u, (mkCode u).isPackBridge = false)
    (hvecOp : ∀ a b, P (.pair a b) → target.keepsPacked (.pair a b) = true →
      vecSupported (.pair a b) = true → target.isLegalOp (mkCode (.pair a b)) false = true)
    (onBool : Arg K .bool → Arg K .bool → Arg K .bool → (Arg K .bool → Expr K KL rs) → Expr K KL rs)
    (onBits : (n : Nat) → Arg K (.bits (target.widenWidth n)) → Arg K (.bits (target.widenWidth n)) →
      Arg K (.bits (target.widenWidth n)) → (Arg K (.bits (target.widenWidth n)) → Expr K KL rs) → Expr K KL rs)
    (onFloat : (f : Fmt) → Arg K (.float f) → Arg K (.float f) → Arg K (.float f) →
      (Arg K (.float f) → Expr K KL rs) → Expr K KL rs)
    (hB : P .bool → ∀ {Γ'} (a b c : Arg K .bool) (cont : Arg K .bool → Expr K KL rs),
      ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b → ArgNormal target Γ' .bool c →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (onBool a b c cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hBi : ∀ n, P (.bits n) → ∀ {Γ'} (a b c : Arg K (.bits (target.widenWidth n)))
        (cont : Arg K (.bits (target.widenWidth n)) → Expr K KL rs),
      ArgNormal target Γ' (.bits (target.widenWidth n)) a → ArgNormal target Γ' (.bits (target.widenWidth n)) b →
      ArgNormal target Γ' (.bits (target.widenWidth n)) c →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.bits (target.widenWidth n)) r) cont →
      (toTFlat (onBits n a b c cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hF : ∀ f, P (.float f) → ∀ {Γ'} (a b c : Arg K (.float f)) (cont : Arg K (.float f) → Expr K KL rs),
      ArgNormal target Γ' (.float f) a → ArgNormal target Γ' (.float f) b → ArgNormal target Γ' (.float f) c →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.float f) r) cont →
      (toTFlat (onFloat f a b c cont) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, P t →
      (xs ys zs : Tup (Arg K) (target.legalTys t)) →
      ArgsNormal target Γ xs → ArgsNormal target Γ ys → ArgsNormal target Γ zs →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalTernaryTree target mkCode vecSupported onBool onBits onFloat t xs ys zs k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, hP, (a, ()), (b, ()), (c, ()), hxs, hys, hzs, k, hk =>
    hB hP a b c _ hxs.1 hys.1 hzs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .bits n, Γ, hP, (a, ()), (b, ()), (c, ()), hxs, hys, hzs, k, hk =>
    hBi n hP a b c _ hxs.1 hys.1 hzs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .float f, Γ, hP, (a, ()), (b, ()), (c, ()), hxs, hys, hzs, k, hk =>
    hF f hP a b c _ hxs.1 hys.1 hzs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .pair t1 t2, Γ, hP, xs, ys, zs, hxs, hys, hzs, k, hk => by
    obtain ⟨hP1, hP2⟩ := hP_pair t1 t2 hP
    simp only [legalTernaryTree]
    split
    · next hp =>
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · simp only [hvs, ↓reduceIte]
        have hxs' := ArgsNormal_packedToTup hp hxs
        have hys' := ArgsNormal_packedToTup hp hys
        have hzs' := ArgsNormal_packedToTup hp hzs
        have hcode : target.isLegalOp (mkCode (.pair t1 t2)) false = true := hvecOp t1 t2 hP hp hvs
        refine isLegal_let_op3_normal target (mkCode (.pair t1 t2))
          (packedToTup hp xs).1 (packedToTup hp ys).1 (packedToTup hp zs).1 _
          (hmkNe _) hcode hxs'.1 hys'.1 hzs'.1 hp ?_
        exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
          (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
      · have hvsf : vecSupported (.pair t1 t2) = false := Bool.eq_false_iff.mpr hvs
        simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2 hfy => ?_
        have h12 := hExt1.trans hExt2
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) zs (hzs.mono h12) fun Γ3 fz hExt3 hfz => ?_
        have h13 := h12.trans hExt3
        have hgoS : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, P u →
            (fxu fyu fzu : Tup (Arg K) (target.leafTys u)) →
            ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu → ArgsNormal target Γ' fzu →
            ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
            IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
            (toTFlat (legalTernaryTree.goS target onBool onBits onFloat u fxu fyu fzu cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
          intro u
          induction u with
          | bool =>
            intro Γ' hPu (a, ()) (b, ()) (c, ()) ha hb hc cont hcont
            exact hB hPu a b c _ ha.1 hb.1 hc.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | bits n =>
            intro Γ' hPu (a, ()) (b, ()) (c, ()) ha hb hc cont hcont
            exact hBi n hPu a b c _ ha.1 hb.1 hc.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | float f =>
            intro Γ' hPu (a, ()) (b, ()) (c, ()) ha hb hc cont hcont
            exact hF f hPu a b c _ ha.1 hb.1 hc.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | pair u1 u2 ih1 ih2 =>
            intro Γ' hPu fxu fyu fzu hfxu hfyu hfzu cont hcont
            obtain ⟨hPu1, hPu2⟩ := hP_pair u1 u2 hPu
            obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
            obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
            obtain ⟨hz1, hz2⟩ := ArgsNormal_tupSplit hfzu
            refine ih1 hPu1 _ _ _ hx1 hy1 hz1 fun Γa r1 hExta hr1 => ?_
            exact ih2 hPu2 _ _ _ (hx2.mono hExta) (hy2.mono hExta) (hz2.mono hExta)
              fun Γb r2 hExtb hr2 => hcont Γb (tupAppend r1 r2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
        refine hgoS (.pair t1 t2) hP fx fy fz (hfx.mono (hExt2.trans hExt3)) (hfy.mono hExt3) hfz
          fun Γ4 fres hExt4 hfres => ?_
        exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
          fun Γ5 res hExt5 hres => hk Γ5 res ((h13.trans hExt4).trans hExt5) hres
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
      obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
      obtain ⟨hz1, hz2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hzs)
      refine legalTernaryTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat hB hBi hF t1 hP1 _ _ _ hx1 hy1 hz1 fun Γ1 r1 hExt1 hr1 => ?_
      refine legalTernaryTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat hB hBi hF t2 hP2 _ _ _ (hx2.mono hExt1) (hy2.mono hExt1) (hz2.mono hExt1)
        fun Γ2 r2 hExt2 hr2 => ?_
      exact hk Γ2 (tupToSplit hf (tupAppend r1 r2)) (hExt1.trans hExt2)
        (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hr1.mono hExt2) hr2))

theorem legalBinTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (P : Ty → Prop) (hP_pair : ∀ a b, P (.pair a b) → P a ∧ P b)
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (vecSupported : (u : Ty) → Bool → Bool)
    (hmkNe : ∀ u, (mkCode u).isPackBridge = false)
    (hvecOp : ∀ a b unif, P (.pair a b) → target.keepsPacked (.pair a b) = true →
      vecSupported (.pair a b) unif = true → target.isLegalOp (mkCode (.pair a b)) unif = true)
    (onBool : Arg K .bool → Arg K .bool → (Arg K .bool → Expr K KL rs) → Expr K KL rs)
    (onBits : (n : Nat) → Arg K (.bits (target.widenWidth n)) → Arg K (.bits (target.widenWidth n)) →
      (Arg K (.bits (target.widenWidth n)) → Expr K KL rs) → Expr K KL rs)
    (onFloat : (f : Fmt) → Arg K (.float f) → Arg K (.float f) → (Arg K (.float f) → Expr K KL rs) → Expr K KL rs)
    (uniformImmRhs : (u : Ty) → Arg (LVar target K) u → Bool)
    (hB : P .bool → ∀ {Γ'} (a b : Arg K .bool) (cont : Arg K .bool → Expr K KL rs),
      ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (onBool a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hBi : ∀ n, P (.bits n) → ∀ {Γ'} (a b : Arg K (.bits (target.widenWidth n)))
        (cont : Arg K (.bits (target.widenWidth n)) → Expr K KL rs),
      ArgNormal target Γ' (.bits (target.widenWidth n)) a → ArgNormal target Γ' (.bits (target.widenWidth n)) b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.bits (target.widenWidth n)) r) cont →
      (toTFlat (onBits n a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hF : ∀ f, P (.float f) → ∀ {Γ'} (a b : Arg K (.float f)) (cont : Arg K (.float f) → Expr K KL rs),
      ArgNormal target Γ' (.float f) a → ArgNormal target Γ' (.float f) b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.float f) r) cont →
      (toTFlat (onFloat f a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, P t →
      (xs ys : Tup (Arg K) (target.legalTys t)) → (rawRhs : Option (Arg (LVar target K) t)) →
      ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t xs ys rawRhs k)
        Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, hP, (a, ()), (b, ()), _, hxs, hys, k, hk =>
    hB hP a b _ hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .bits n, Γ, hP, (a, ()), (b, ()), _, hxs, hys, k, hk =>
    hBi n hP a b _ hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .float f, Γ, hP, (a, ()), (b, ()), _, hxs, hys, k, hk =>
    hF f hP a b _ hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .pair t1 t2, Γ, hP, xs, ys, rawRhs, hxs, hys, k, hk => by
    obtain ⟨hP1, hP2⟩ := hP_pair t1 t2 hP
    simp only [legalBinTree]
    split
    · next hp =>
      have hxs' := ArgsNormal_packedToTup hp hxs
      have hys' := ArgsNormal_packedToTup hp hys
      have hscalar : (toTFlat (
          splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
          splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
          legalBinTree.goS target onBool onBits onFloat (.pair t1 t2) fx fy fun fres =>
            packLeavesToLegal target (.pair t1 t2) fres k) Γ.length Δ.length).isLegal target Γ Δ = true := by
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2 hfy => ?_
        have h12 := hExt1.trans hExt2
        have hgoS : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, P u →
            (fxu fyu : Tup (Arg K) (target.leafTys u)) →
            ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu →
            ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
            IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
            (toTFlat (legalBinTree.goS target onBool onBits onFloat u fxu fyu cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
          intro u
          induction u with
          | bool => intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont; exact hB hPu a b _ ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | bits n => intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont; exact hBi n hPu a b _ ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | float f => intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont; exact hF f hPu a b _ ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | pair u1 u2 ih1 ih2 =>
            intro Γ' hPu fxu fyu hfxu hfyu cont hcont
            obtain ⟨hPu1, hPu2⟩ := hP_pair u1 u2 hPu
            obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
            obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
            refine ih1 hPu1 _ _ hx1 hy1 fun Γa r1 hExta hr1 => ?_
            exact ih2 hPu2 _ _ (hx2.mono hExta) (hy2.mono hExta) fun Γb r2 hExtb hr2 =>
              hcont Γb (tupAppend r1 r2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
        refine hgoS (.pair t1 t2) hP fx fy (hfx.mono hExt2) hfy fun Γ3 fres hExt3 hfres => ?_
        exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
          fun Γ4 res hExt4 hres => hk Γ4 res ((h12.trans hExt3).trans hExt4) hres
      by_cases hvs : vecSupported (.pair t1 t2) (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = true
      · simp only [hvs, ↓reduceIte]
        have hunif : isUniformImmShift (mkCode (.pair t1 t2))
            (idxArg Γ.length (packedToTup hp xs).1, idxArg Γ.length (packedToTup hp ys).1, ()) =
            checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1 :=
          isUniformImmShift_idxArgs_eq (.pair t1 t2) (mkCode (.pair t1 t2)) Γ.length _ _
        have hcode : target.isLegalOp (mkCode (.pair t1 t2))
            (isUniformImmShift (mkCode (.pair t1 t2)) (idxArg Γ.length (packedToTup hp xs).1, idxArg Γ.length (packedToTup hp ys).1, ())) = true := by
          rw [hunif]; exact hvecOp t1 t2 _ hP hp hvs
        refine isLegal_let_op2_normal target (mkCode (.pair t1 t2)) (packedToTup hp xs).1 (packedToTup hp ys).1 _
          (hmkNe _) hcode hxs'.1 hys'.1 hp ?_
        exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
          (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
      · have hvsf : vecSupported (.pair t1 t2) (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = false :=
          Bool.eq_false_iff.mpr hvs
        simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
        cases opShiftKind (mkCode (.pair t1 t2)) with
        | none => dsimp only; exact hscalar
        | some b =>
          cases hrr : rawRhs with
          | none => cases b <;> (dsimp only; exact hscalar)
          | some r =>
            cases r with
            | var _ => cases b <;> (dsimp only; exact hscalar)
            | imm c =>
              cases b with
              | true =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) c with
                | none => dsimp only; exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  by_cases hs0 : (s == 0) = true
                  · simp only [hs0, ↓reduceIte]
                    exact hk Γ (tupToPacked hp (packedToTup hp xs)) (CtxExtends.refl Γ) (ArgsNormal_tupToPacked hp hxs')
                  · have hs0f : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0f, Bool.false_eq_true, ↓reduceIte]
                    by_cases hsup : target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = true
                    · simp only [hsup, ↓reduceIte]
                      have husR := uniformShiftLeaf?_splatBits (.pair t1 t2) c (BitVec.ofNat w (w - s)) hus
                      have hunifR : isUniformImmShift (.rotr (.pair t1 t2))
                          (idxArg Γ.length (packedToTup hp xs).1, idxArg Γ.length (.imm (splatBits w (BitVec.ofNat w (w - s)) (.pair t1 t2))), ()) = true := by
                        simp [idxArg, isUniformImmShift, husR]
                      refine isLegal_let_op2_normal target (.rotr (.pair t1 t2)) (packedToTup hp xs).1 (.imm _) _ rfl
                        (by rw [hunifR]; simp [LegalTarget.isLegalOp, hp, hsup]) hxs'.1 hp hp ?_
                      exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
                        (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
                    · have hsupf : target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = false :=
                        Bool.eq_false_iff.mpr hsup
                      simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
                      exact hscalar
              | false =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) c with
                | none => dsimp only; exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  by_cases hs0 : (s == 0) = true
                  · simp only [hs0, ↓reduceIte]
                    exact hk Γ (tupToPacked hp (packedToTup hp xs)) (CtxExtends.refl Γ) (ArgsNormal_tupToPacked hp hxs')
                  · have hs0f : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0f, Bool.false_eq_true, ↓reduceIte]
                    by_cases hsup : (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                          target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) = true
                    · simp only [hsup, ↓reduceIte]
                      have hsup' := (Bool.and_eq_true _ _).mp hsup
                      have husR := uniformShiftLeaf?_splatBits (.pair t1 t2) c (BitVec.ofNat w (w - s)) hus
                      have hunifR : isUniformImmShift (.rotr (.pair t1 t2))
                          (idxArg Γ.length (packedToTup hp xs).1, idxArg Γ.length (.imm (splatBits w (BitVec.ofNat w (w - s)) (.pair t1 t2))), ()) = true := by
                        simp [idxArg, isUniformImmShift, husR]
                      refine isLegal_let_op2_normal target (.rotr (.pair t1 t2)) (packedToTup hp xs).1 (.imm _) _ rfl
                        (by rw [hunifR]; simp [LegalTarget.isLegalOp, hp, hsup'.1]) hxs'.1 hp hp ?_
                      let Γ1 := (.pair t1 t2, VarKind.normal) :: Γ
                      refine isLegal_let_op2_normal target (.and (.pair t1 t2)) (.var Γ.length) (.imm _) _ rfl
                        (by simp [LegalTarget.isLegalOp, isUniformImmShift, hp, hsup'.2]) (ArgNormal.head target Γ hp) hp hp ?_
                      let Γ2 := (.pair t1 t2, VarKind.normal) :: Γ1
                      exact hk Γ2 (tupToPacked hp (.var Γ1.length, ())) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
                        (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ1 hp, trivial⟩)
                    · have hsupf : (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                          target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) = false := Bool.eq_false_iff.mpr hsup
                      simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
                      exact hscalar
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
      obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
      refine legalBinTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat uniformImmRhs hB hBi hF t1 hP1 _ _ none hx1 hy1 fun Γ1 r1 hExt1 hr1 => ?_
      refine legalBinTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat uniformImmRhs hB hBi hF t2 hP2 _ _ none (hx2.mono hExt1) (hy2.mono hExt1) fun Γ2 r2 hExt2 hr2 => ?_
      exact hk Γ2 (tupToSplit hf (tupAppend r1 r2)) (hExt1.trans hExt2)
        (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hr1.mono hExt2) hr2))

theorem legalCmpTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (o : CmpOp) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t.mask) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalCmpTree target o t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro t Γ hsupp xs ys hxs hys k hk
  have leafBool : ∀ {Γ' : List (Ty × VarKind)} (a b : Arg K .bool) {cont : Arg K .bool → Expr K KL rs},
      ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (if target.boolCmp then .let_ (op2 (.cmp o .bool) a b) fun (r, ()) => cont (.var r)
        else emitBoolCmp o a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro Γ' a b cont ha hb hcont
    by_cases hbc : target.boolCmp = true
    · simp only [hbc, ↓reduceIte]
      refine isLegal_let_op2_normal target (.cmp o .bool) a b _ rfl (by simp [LegalTarget.isLegalOp, hbc]) ha hb rfl ?_
      exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
    · have hbcf : target.boolCmp = false := Bool.eq_false_iff.mpr hbc
      simp only [hbcf, Bool.false_eq_true, ↓reduceIte]
      exact emitBoolCmp_isLegal target o a b ha hb hcont
  have leafBits : ∀ (n : Nat) {Γ' : List (Ty × VarKind)} (a b : Arg K (.bits (target.widenWidth n)))
      {cont : Arg K .bool → Expr K KL rs},
      target.supportsTy (.bits n) = true →
      ArgNormal target Γ' (.bits (target.widenWidth n)) a → ArgNormal target Γ' (.bits (target.widenWidth n)) b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (let w := target.widenWidth n
        if n == 0 then cont (.imm (o.evalBits 0#0 0#0))
        else if n == w then .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => cont (.var r)
        else if (match o with | .slt | .sle | .sgt | .sge => true | _ => false) then
          emitSextToW n w a fun sa => emitSextToW n w b fun sb => .let_ (op2 (.cmp o (.bits w)) sa sb) fun (r, ()) => cont (.var r)
        else .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => cont (.var r)) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro n Γ' a b cont hsuppb ha hb hcont
    have hw := widenWidth_mem_of_supports hsuppb
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    dsimp only
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont Γ' (.imm _) (CtxExtends.refl Γ') rfl
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.cmp o (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb rfl ?_
        exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        have huns : (toTFlat (.let_ (op2 (.cmp o (.bits (target.widenWidth n))) a b) fun (r, ()) => cont (.var r))
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
          refine isLegal_let_op2_normal target (.cmp o (.bits (target.widenWidth n))) a b _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb rfl ?_
          exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
        have hsgn : (toTFlat (emitSextToW n (target.widenWidth n) a fun sa =>
            emitSextToW n (target.widenWidth n) b fun sb =>
            .let_ (op2 (.cmp o (.bits (target.widenWidth n))) sa sb) fun (r, ()) => cont (.var r))
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
          refine emitSextToW_isLegal target hw a ha fun Γ1 sa hExt1 hsa => ?_
          refine emitSextToW_isLegal target hw b (hb.mono hExt1) fun Γ2 sb hExt2 hsb => ?_
          refine isLegal_let_op2_normal target (.cmp o (.bits (target.widenWidth n))) sa sb _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExt2) hsb rfl ?_
          exact hcont _ (.var Γ2.length) ((hExt1.trans hExt2).trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 rfl)
        cases o <;> simp only [↓reduceIte, Bool.false_eq_true]
        · exact huns
        · exact huns
        · exact huns
        · exact huns
        · exact huns
        · exact huns
        · exact hsgn
        · exact hsgn
        · exact hsgn
        · exact hsgn
  cases t with
  | bool =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    simp only [legalCmpTree]
    exact leafBool a b hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | bits n =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    simp only [legalCmpTree]
    exact leafBits n a b hsupp hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | float _ => simp [legalCmpTree, toTFlat_hlt]
  | pair t1 t2 =>
    simp only [legalCmpTree]
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2 hfy => ?_
    have h12 := hExt1.trans hExt2
    have hgoMask : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, target.supportsTy u = true →
        (fxu fyu : Tup (Arg K) (target.leafTys u)) → ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu →
        ∀ {cont : Tup (Arg K) (target.leafTys u.mask) → Expr K KL rs},
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
        (toTFlat (legalCmpTree.goMask target o u fxu fyu cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro u
      induction u with
      | bool =>
        intro Γ' _ (a, ()) (b, ()) ha hb cont hcont
        exact leafBool a b ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
      | bits n =>
        intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont
        exact leafBits n a b hPu ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
      | float _ => intro _ _ _ _ _ _ _ _; simp [legalCmpTree.goMask, toTFlat_hlt]
      | pair u1 u2 ih1 ih2 =>
        intro Γ' hPu fxu fyu hfxu hfyu cont hcont
        simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hPu
        obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
        obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
        refine ih1 hPu.1 _ _ hx1 hy1 fun Γa m1 hExta hm1 => ?_
        exact ih2 hPu.2 _ _ (hx2.mono hExta) (hy2.mono hExta) fun Γb m2 hExtb hm2 =>
          hcont Γb (tupAppend m1 m2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hm1.mono hExtb) hm2)
    refine hgoMask (.pair t1 t2) hsupp fx fy (hfx.mono hExt2) hfy fun Γ3 mres hExt3 hmres => ?_
    exact packLeavesToLegal_isLegal target (Ty.mask (.pair t1 t2)) mres hmres
      fun Γ4 res hExt4 hres => hk Γ4 res ((h12.trans hExt3).trans hExt4) hres

theorem legalFCmpTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (o : FCmpOp) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t.mask) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalFCmpTree target o t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro t Γ hsupp xs ys hxs hys k hk
  cases t with
  | bool => simp [legalFCmpTree, toTFlat_hlt]
  | bits _ => simp [legalFCmpTree, toTFlat_hlt]
  | float f =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    simp only [legalFCmpTree]
    refine isLegal_let_op2_normal target (.fcmp o (.float f)) a b _ rfl (by simp [LegalTarget.isLegalOp, hf]) hxs.1 hys.1 rfl ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ rfl, trivial⟩
  | pair t1 t2 =>
    simp only [legalFCmpTree]
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2 hfy => ?_
    have h12 := hExt1.trans hExt2
    have hgoFCmp : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, target.supportsTy u = true →
        (fxu fyu : Tup (Arg K) (target.leafTys u)) → ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu →
        ∀ {cont : Tup (Arg K) (target.leafTys u.mask) → Expr K KL rs},
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
        (toTFlat (legalFCmpTree.goFCmp target o u fxu fyu cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro u
      induction u with
      | bool => intro _ _ _ _ _ _ _ _; simp [legalFCmpTree.goFCmp, toTFlat_hlt]
      | bits _ => intro _ _ _ _ _ _ _ _; simp [legalFCmpTree.goFCmp, toTFlat_hlt]
      | float f =>
        intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont
        have hfp : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hPu : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        simp only [legalFCmpTree.goFCmp]
        refine isLegal_let_op2_normal target (.fcmp o (.float f)) a b _ rfl (by simp [LegalTarget.isLegalOp, hfp]) ha.1 hb.1 rfl ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ' rfl, trivial⟩
      | pair u1 u2 ih1 ih2 =>
        intro Γ' hPu fxu fyu hfxu hfyu cont hcont
        simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hPu
        obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
        obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
        refine ih1 hPu.1 _ _ hx1 hy1 fun Γa m1 hExta hm1 => ?_
        exact ih2 hPu.2 _ _ (hx2.mono hExta) (hy2.mono hExta) fun Γb m2 hExtb hm2 =>
          hcont Γb (tupAppend m1 m2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hm1.mono hExtb) hm2)
    refine hgoFCmp (.pair t1 t2) hsupp fx fy (hfx.mono hExt2) hfy fun Γ3 mres hExt3 hmres => ?_
    exact packLeavesToLegal_isLegal target (Ty.mask (.pair t1 t2)) mres hmres
      fun Γ4 res hExt4 hres => hk Γ4 res ((h12.trans hExt3).trans hExt4) hres

theorem legalSelectTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    {Γ : List (Ty × VarKind)} (c : Arg K .bool) (hc : ArgNormal target Γ .bool c) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalSelectTree target c t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro t hsupp xs ys hxs hys k hk
  have leafBool : ∀ {Γ' : List (Ty × VarKind)} (c' a b : Arg K .bool) {cont : Arg K .bool → Expr K KL rs},
      ArgNormal target Γ' .bool c' → ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (if target.boolSelect then .let_ (op3 (.select .bool) c' a b) fun (r, ()) => cont (.var r)
        else emitBoolSelect c' a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro Γ' c' a b cont hc' ha hb hcont
    by_cases hbs : target.boolSelect = true
    · simp only [hbs, ↓reduceIte]
      refine isLegal_let_op3_normal target (.select .bool) c' a b _ rfl (by simp [LegalTarget.isLegalOp, hbs]) hc' ha hb rfl ?_
      exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
    · have hbsf : target.boolSelect = false := Bool.eq_false_iff.mpr hbs
      simp only [hbsf, Bool.false_eq_true, ↓reduceIte]
      exact emitBoolSelect_isLegal target c' a b hc' ha hb hcont
  cases t with
  | bool =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    simp only [legalSelectTree]
    exact leafBool c a b hc hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | bits n =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hw := widenWidth_mem_of_supports hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalSelectTree]
    refine isLegal_let_op3_normal target (.select (.bits (target.widenWidth n))) c a b _ rfl
      (by simp [LegalTarget.isLegalOp, hw]) hc hxs.1 hys.1 hlegW ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | float f =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalSelectTree]
    refine isLegal_let_op3_normal target (.select (.float f)) c a b _ rfl
      (by simp [LegalTarget.isLegalOp, hf]) hc hxs.1 hys.1 hlegF ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
  | pair t1 t2 =>
    simp only [legalSelectTree]
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2 hfy => ?_
    have h12 := hExt1.trans hExt2
    have hgoSel : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, target.supportsTy u = true →
        CtxExtends Γ Γ' →
        (fxu fyu : Tup (Arg K) (target.leafTys u)) → ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu →
        ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
        (toTFlat (legalSelectTree.goSel target c u fxu fyu cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro u
      induction u with
      | bool =>
        intro Γ' _ hExt' (a, ()) (b, ()) ha hb cont hcont
        exact leafBool c a b (hc.mono hExt') ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
      | bits n =>
        intro Γ' hPu hExt' (a, ()) (b, ()) ha hb cont hcont
        have hw := widenWidth_mem_of_supports hPu
        have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
        simp only [legalSelectTree.goSel]
        refine isLegal_let_op3_normal target (.select (.bits (target.widenWidth n))) c a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hc.mono hExt') ha.1 hb.1 hlegW ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ' hlegW, trivial⟩
      | float f =>
        intro Γ' hPu hExt' (a, ()) (b, ()) ha hb cont hcont
        have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hPu : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
        simp only [legalSelectTree.goSel]
        refine isLegal_let_op3_normal target (.select (.float f)) c a b _ rfl
          (by simp [LegalTarget.isLegalOp, hf]) (hc.mono hExt') ha.1 hb.1 hlegF ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ' hlegF, trivial⟩
      | pair u1 u2 ih1 ih2 =>
        intro Γ' hPu hExt' fxu fyu hfxu hfyu cont hcont
        simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hPu
        obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
        obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
        refine ih1 hPu.1 hExt' _ _ hx1 hy1 fun Γa r1 hExta hr1 => ?_
        exact ih2 hPu.2 (hExt'.trans hExta) _ _ (hx2.mono hExta) (hy2.mono hExta) fun Γb r2 hExtb hr2 =>
          hcont Γb (tupAppend r1 r2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
    refine hgoSel (.pair t1 t2) hsupp h12 fx fy (hfx.mono hExt2) hfy fun Γ3 fres hExt3 hfres => ?_
    exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
      fun Γ4 res hExt4 hres => hk Γ4 res ((h12.trans hExt3).trans hExt4) hres

theorem legalBlendTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty} :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (ms : Tup (Arg K) (target.legalTys t.mask)) → (xs ys : Tup (Arg K) (target.legalTys t)) →
      ArgsNormal target Γ ms → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalBlendTree target t ms xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro t Γ hsupp ms xs ys hms hxs hys k hk
  have leafBool : ∀ {Γ' : List (Ty × VarKind)} (c' a b : Arg K .bool) {cont : Arg K .bool → Expr K KL rs},
      ArgNormal target Γ' .bool c' → ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (if target.boolSelect then .let_ (op3 (.select .bool) c' a b) fun (r, ()) => cont (.var r)
        else emitBoolSelect c' a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro Γ' c' a b cont hc' ha hb hcont
    by_cases hbs : target.boolSelect = true
    · simp only [hbs, ↓reduceIte]
      refine isLegal_let_op3_normal target (.select .bool) c' a b _ rfl (by simp [LegalTarget.isLegalOp, hbs]) hc' ha hb rfl ?_
      exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
    · have hbsf : target.boolSelect = false := Bool.eq_false_iff.mpr hbs
      simp only [hbsf, Bool.false_eq_true, ↓reduceIte]
      exact emitBoolSelect_isLegal target c' a b hc' ha hb hcont
  cases t with
  | bool =>
    rcases ms with ⟨c, ⟨⟩⟩; rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    simp only [legalBlendTree]
    exact leafBool c a b hms.1 hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | bits n =>
    rcases ms with ⟨c, ⟨⟩⟩; rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hw := widenWidth_mem_of_supports hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalBlendTree]
    refine isLegal_let_op3_normal target (.select (.bits (target.widenWidth n))) c a b _ rfl
      (by simp [LegalTarget.isLegalOp, hw]) hms.1 hxs.1 hys.1 hlegW ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | float f =>
    rcases ms with ⟨c, ⟨⟩⟩; rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hsupp : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalBlendTree]
    refine isLegal_let_op3_normal target (.select (.float f)) c a b _ rfl
      (by simp [LegalTarget.isLegalOp, hf]) hms.1 hxs.1 hys.1 hlegF ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
  | pair t1 t2 =>
    simp only [legalBlendTree]
    refine splitLegalToLeaves_isLegal target (Ty.mask (.pair t1 t2)) ms hms fun Γ1 fm hExt1 hfm => ?_
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs (hxs.mono hExt1) fun Γ2 fx hExt2 hfx => ?_
    have h12 := hExt1.trans hExt2
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono h12) fun Γ3 fy hExt3 hfy => ?_
    have h13 := h12.trans hExt3
    have hgoBlend : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, target.supportsTy u = true →
        (fmu : Tup (Arg K) (target.leafTys u.mask)) → (fxu fyu : Tup (Arg K) (target.leafTys u)) →
        ArgsNormal target Γ' fmu → ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu →
        ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
        (toTFlat (legalBlendTree.goBlend target u fmu fxu fyu cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro u
      induction u with
      | bool =>
        intro Γ' _ (c, ()) (a, ()) (b, ()) hc ha hb cont hcont
        exact leafBool c a b hc.1 ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
      | bits n =>
        intro Γ' hPu (c, ()) (a, ()) (b, ()) hc ha hb cont hcont
        have hw := widenWidth_mem_of_supports hPu
        have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
        simp only [legalBlendTree.goBlend]
        refine isLegal_let_op3_normal target (.select (.bits (target.widenWidth n))) c a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hc.1 ha.1 hb.1 hlegW ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ' hlegW, trivial⟩
      | float f =>
        intro Γ' hPu (c, ()) (a, ()) (b, ()) hc ha hb cont hcont
        have hf : f ∈ target.floatFmts := (by simpa [LegalTarget.supportsTy] using hPu : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
        simp only [legalBlendTree.goBlend]
        refine isLegal_let_op3_normal target (.select (.float f)) c a b _ rfl
          (by simp [LegalTarget.isLegalOp, hf]) hc.1 ha.1 hb.1 hlegF ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ' hlegF, trivial⟩
      | pair u1 u2 ih1 ih2 =>
        intro Γ' hPu fmu fxu fyu hfmu hfxu hfyu cont hcont
        simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hPu
        obtain ⟨hm1, hm2⟩ := ArgsNormal_tupSplit hfmu
        obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
        obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
        refine ih1 hPu.1 _ _ _ hm1 hx1 hy1 fun Γa r1 hExta hr1 => ?_
        exact ih2 hPu.2 _ _ _ (hm2.mono hExta) (hx2.mono hExta) (hy2.mono hExta) fun Γb r2 hExtb hr2 =>
          hcont Γb (tupAppend r1 r2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
    refine hgoBlend (.pair t1 t2) hsupp fm fx fy
      (hfm.mono (hExt2.trans hExt3)) (hfx.mono hExt3) hfy fun Γ4 fres hExt4 hfres => ?_
    exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
      fun Γ5 res hExt5 hres => hk Γ5 res ((h13.trans hExt4).trans hExt5) hres

theorem legalShufd_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) (imm : BitVec 8) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalShufd target imm t xs k) Γ.length Δ.length).isLegal target Γ Δ = true
  | t, Γ, ht, xs, hxs, k, hk => by
    have h8 := valid_mem8 hv
    have hsc : ∀ {Γ' : List (Ty × VarKind)} (ys : Tup (Arg K) (target.legalTys t)),
        ArgsNormal target Γ' ys → IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) k →
        (toTFlat (legalSimdScalar128 target (fun a0 a1 a2 a3 _ _ _ _ cont =>
          let (r0, r1, r2, r3) := scalarShufd128 imm a0 a1 a2 a3; cont r0 r1 r2 r3) t ys ys k)
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro Γ' ys hys hk'
      refine legalSimdScalar128_isLegal target hv h32 _ (fun {Γa} a0 a1 a2 a3 _ _ _ _ cont ha0 ha1 ha2 ha3 _ _ _ _ hcont => ?_)
        t ht ys ys hys hys hk'
      have ⟨hr0, hr1, hr2, hr3⟩ := ArgNormal_scalarShufd128 target imm a0 a1 a2 a3 ha0 ha1 ha2 ha3
      exact hcont Γa _ _ _ _ (CtxExtends.refl Γa) hr0 hr1 hr2 hr3
    rw [legalShufd.eq_def]
    by_cases hsz : (t.size == 0 || t.size % 128 != 0) = true
    · simp [hsz, toTFlat_hlt]
    · have hszf : (t.size == 0 || t.size % 128 != 0) = false := Bool.eq_false_iff.mpr hsz
      simp only [hszf, Bool.false_eq_true, ↓reduceIte]
      have ⟨hsz0, hmod⟩ : (t.size != 0) = true ∧ (t.size % 128 == 0) = true := by
        simpa [Bool.or_eq_false_iff, Bool.not_eq_true', bne_iff_ne] using hszf
      cases t with
      | bool => exact hsc xs hxs hk
      | bits _ => exact hsc xs hxs hk
      | float _ => exact hsc xs hxs hk
      | pair a b =>
        dsimp only
        split
        · next hp =>
          by_cases hsup : target.vecIntOpSupported (.shufd (.pair a b) imm) (.pair a b) false = true
          · simp only [hsup, ↓reduceIte]
            have hxs' := ArgsNormal_packedToTup hp hxs
            refine isLegal_let_op1_normal target (.shufd (.pair a b) imm) (packedToTup hp xs).1 _ rfl
              (by simp [LegalTarget.isLegalOp, hp, hsz0, hmod, hsup]) hxs'.1 hp ?_
            exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
              (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
          · have hsupf : target.vecIntOpSupported (.shufd (.pair a b) imm) (.pair a b) false = false :=
              Bool.eq_false_iff.mpr hsup
            simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs hxs hk
        · next hnp =>
          have hf := Bool.eq_false_iff.mpr hnp
          by_cases hab : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
          · simp only [hab, ↓reduceIte]
            simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
            obtain ⟨xa, xb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
            refine legalShufd_isLegal target hv h32 imm a ht.1 _ xa fun Γ1 ra hExt1 hra => ?_
            refine legalShufd_isLegal target hv h32 imm b ht.2 _ (xb.mono hExt1) fun Γ2 rb hExt2 hrb => ?_
            exact hk Γ2 (tupToSplit hf (tupAppend ra rb)) (hExt1.trans hExt2)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hra.mono hExt2) hrb))
          · have habf : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = false :=
              Bool.eq_false_iff.mpr hab
            simp only [habf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs hxs hk

theorem legalBlendw_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) (imm : BitVec 8) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalBlendw target imm t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true
  | t, Γ, ht, xs, ys, hxs, hys, k, hk => by
    have hsc : ∀ {Γ' : List (Ty × VarKind)} (ys1 ys2 : Tup (Arg K) (target.legalTys t)),
        ArgsNormal target Γ' ys1 → ArgsNormal target Γ' ys2 →
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) k →
        (toTFlat (legalSimdScalar128 target (scalarBlendw128 imm) t ys1 ys2 k)
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro Γ' ys1 ys2 h1 h2 hk'
      refine legalSimdScalar128_isLegal target hv h32 _ (fun {Γa} a0 a1 a2 a3 b0 b1 b2 b3 cont ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont => ?_)
        t ht ys1 ys2 h1 h2 hk'
      exact scalarBlendw128_isLegal target h32 imm a0 a1 a2 a3 b0 b1 b2 b3 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    rw [legalBlendw.eq_def]
    by_cases hsz : (t.size == 0 || t.size % 128 != 0) = true
    · simp [hsz, toTFlat_hlt]
    · have hszf : (t.size == 0 || t.size % 128 != 0) = false := Bool.eq_false_iff.mpr hsz
      simp only [hszf, Bool.false_eq_true, ↓reduceIte]
      have ⟨hsz0, hmod⟩ : (t.size != 0) = true ∧ (t.size % 128 == 0) = true := by
        simpa [Bool.or_eq_false_iff, Bool.not_eq_true', bne_iff_ne] using hszf
      cases t with
      | bool => exact hsc xs ys hxs hys hk
      | bits _ => exact hsc xs ys hxs hys hk
      | float _ => exact hsc xs ys hxs hys hk
      | pair a b =>
        dsimp only
        split
        · next hp =>
          by_cases hsup : target.vecIntOpSupported (.blendw (.pair a b) imm) (.pair a b) false = true
          · simp only [hsup, ↓reduceIte]
            have hxs' := ArgsNormal_packedToTup hp hxs
            have hys' := ArgsNormal_packedToTup hp hys
            refine isLegal_let_op2_normal target (.blendw (.pair a b) imm)
              (packedToTup hp xs).1 (packedToTup hp ys).1 _ rfl
              (by simp [LegalTarget.isLegalOp, hp, hsz0, hmod, hsup]) hxs'.1 hys'.1 hp ?_
            exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
              (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
          · have hsupf : target.vecIntOpSupported (.blendw (.pair a b) imm) (.pair a b) false = false :=
              Bool.eq_false_iff.mpr hsup
            simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk
        · next hnp =>
          have hf := Bool.eq_false_iff.mpr hnp
          by_cases hab : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
          · simp only [hab, ↓reduceIte]
            simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
            obtain ⟨xa, xb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
            obtain ⟨ya, yb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
            refine legalBlendw_isLegal target hv h32 imm a ht.1 _ _ xa ya fun Γ1 ra hExt1 hra => ?_
            refine legalBlendw_isLegal target hv h32 imm b ht.2 _ _ (xb.mono hExt1) (yb.mono hExt1) fun Γ2 rb hExt2 hrb => ?_
            exact hk Γ2 (tupToSplit hf (tupAppend ra rb)) (hExt1.trans hExt2)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hra.mono hExt2) hrb))
          · have habf : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = false :=
              Bool.eq_false_iff.mpr hab
            simp only [habf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk

theorem legalAlignr_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) (imm : BitVec 8) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalAlignr target imm t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true
  | t, Γ, ht, xs, ys, hxs, hys, k, hk => by
    have h8 := valid_mem8 hv
    have hsc : ∀ {Γ' : List (Ty × VarKind)} (ys1 ys2 : Tup (Arg K) (target.legalTys t)),
        ArgsNormal target Γ' ys1 → ArgsNormal target Γ' ys2 →
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) k →
        (toTFlat (legalSimdScalar128 target (scalarAlignr128 imm) t ys1 ys2 k)
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro Γ' ys1 ys2 h1 h2 hk'
      refine legalSimdScalar128_isLegal target hv h32 _ (fun {Γa} a0 a1 a2 a3 b0 b1 b2 b3 cont ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont => ?_)
        t ht ys1 ys2 h1 h2 hk'
      exact scalarAlignr128_isLegal target h8 h32 imm a0 a1 a2 a3 b0 b1 b2 b3 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    rw [legalAlignr.eq_def]
    by_cases hsz : (t.size == 0 || t.size % 128 != 0) = true
    · simp [hsz, toTFlat_hlt]
    · have hszf : (t.size == 0 || t.size % 128 != 0) = false := Bool.eq_false_iff.mpr hsz
      simp only [hszf, Bool.false_eq_true, ↓reduceIte]
      have ⟨hsz0, hmod⟩ : (t.size != 0) = true ∧ (t.size % 128 == 0) = true := by
        simpa [Bool.or_eq_false_iff, Bool.not_eq_true', bne_iff_ne] using hszf
      cases t with
      | bool => exact hsc xs ys hxs hys hk
      | bits _ => exact hsc xs ys hxs hys hk
      | float _ => exact hsc xs ys hxs hys hk
      | pair a b =>
        dsimp only
        split
        · next hp =>
          by_cases hsup : target.vecIntOpSupported (.alignr (.pair a b) imm) (.pair a b) false = true
          · simp only [hsup, ↓reduceIte]
            have hxs' := ArgsNormal_packedToTup hp hxs
            have hys' := ArgsNormal_packedToTup hp hys
            refine isLegal_let_op2_normal target (.alignr (.pair a b) imm)
              (packedToTup hp xs).1 (packedToTup hp ys).1 _ rfl
              (by simp [LegalTarget.isLegalOp, hp, hsz0, hmod, hsup]) hxs'.1 hys'.1 hp ?_
            exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
              (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
          · have hsupf : target.vecIntOpSupported (.alignr (.pair a b) imm) (.pair a b) false = false :=
              Bool.eq_false_iff.mpr hsup
            simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk
        · next hnp =>
          have hf := Bool.eq_false_iff.mpr hnp
          by_cases hab : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
          · simp only [hab, ↓reduceIte]
            simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
            obtain ⟨xa, xb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
            obtain ⟨ya, yb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
            refine legalAlignr_isLegal target hv h32 imm a ht.1 _ _ xa ya fun Γ1 ra hExt1 hra => ?_
            refine legalAlignr_isLegal target hv h32 imm b ht.2 _ _ (xb.mono hExt1) (yb.mono hExt1) fun Γ2 rb hExt2 hrb => ?_
            exact hk Γ2 (tupToSplit hf (tupAppend ra rb)) (hExt1.trans hExt2)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hra.mono hExt2) hrb))
          · have habf : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = false :=
              Bool.eq_false_iff.mpr hab
            simp only [habf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk

theorem legalShufb_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalShufb target t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true
  | t, Γ, ht, xs, ys, hxs, hys, k, hk => by
    have h8 := valid_mem8 hv
    have hsc : ∀ {Γ' : List (Ty × VarKind)} (ys1 ys2 : Tup (Arg K) (target.legalTys t)),
        ArgsNormal target Γ' ys1 → ArgsNormal target Γ' ys2 →
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) k →
        (toTFlat (legalSimdScalar128 target scalarShufb128 t ys1 ys2 k)
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro Γ' ys1 ys2 h1 h2 hk'
      refine legalSimdScalar128_isLegal target hv h32 _ (fun {Γa} a0 a1 a2 a3 b0 b1 b2 b3 cont ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont => ?_)
        t ht ys1 ys2 h1 h2 hk'
      exact scalarShufb128_isLegal target h8 h32 a0 a1 a2 a3 b0 b1 b2 b3 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont
    rw [legalShufb.eq_def]
    by_cases hsz : (t.size == 0 || t.size % 128 != 0) = true
    · simp [hsz, toTFlat_hlt]
    · have hszf : (t.size == 0 || t.size % 128 != 0) = false := Bool.eq_false_iff.mpr hsz
      simp only [hszf, Bool.false_eq_true, ↓reduceIte]
      have ⟨hsz0, hmod⟩ : (t.size != 0) = true ∧ (t.size % 128 == 0) = true := by
        simpa [Bool.or_eq_false_iff, Bool.not_eq_true', bne_iff_ne] using hszf
      cases t with
      | bool => exact hsc xs ys hxs hys hk
      | bits _ => exact hsc xs ys hxs hys hk
      | float _ => exact hsc xs ys hxs hys hk
      | pair a b =>
        dsimp only
        split
        · next hp =>
          by_cases hsup : target.vecIntOpSupported (.shufb (.pair a b)) (.pair a b) false = true
          · simp only [hsup, ↓reduceIte]
            have hxs' := ArgsNormal_packedToTup hp hxs
            have hys' := ArgsNormal_packedToTup hp hys
            refine isLegal_let_op2_normal target (.shufb (.pair a b))
              (packedToTup hp xs).1 (packedToTup hp ys).1 _ rfl
              (by simp [LegalTarget.isLegalOp, hp, hsz0, hmod, hsup]) hxs'.1 hys'.1 hp ?_
            exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
              (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
          · have hsupf : target.vecIntOpSupported (.shufb (.pair a b)) (.pair a b) false = false :=
              Bool.eq_false_iff.mpr hsup
            simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk
        · next hnp =>
          have hf := Bool.eq_false_iff.mpr hnp
          by_cases hab : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
          · simp only [hab, ↓reduceIte]
            simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
            obtain ⟨xa, xb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
            obtain ⟨ya, yb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
            refine legalShufb_isLegal target hv h32 a ht.1 _ _ xa ya fun Γ1 ra hExt1 hra => ?_
            refine legalShufb_isLegal target hv h32 b ht.2 _ _ (xb.mono hExt1) (yb.mono hExt1) fun Γ2 rb hExt2 hrb => ?_
            exact hk Γ2 (tupToSplit hf (tupAppend ra rb)) (hExt1.trans hExt2)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hra.mono hExt2) hrb))
          · have habf : (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = false :=
              Bool.eq_false_iff.mpr hab
            simp only [habf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk


end LegalIsLegal

end LeanQbe.T
