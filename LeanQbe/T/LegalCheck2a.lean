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

theorem ArgNormal_getD_i8 (target : LegalTarget) {Γ : List (Ty × VarKind)}
  (h8 : 8 ∈ target.bitWidths)
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
  have hd0 : ArgNormal target Γ6 i32 (.var Γ.length) :=
    (ArgNormal.head target Γ hleg32).mono ⟨[_, _, _, _, _], rfl⟩
  have hd1 : ArgNormal target Γ6 i32 (.var Γ2.length) :=
    (ArgNormal.head target Γ2 hleg32).mono ⟨[_, _, _], rfl⟩
  have hd2 : ArgNormal target Γ6 i32 (.var Γ3.length) :=
    (ArgNormal.head target Γ3 hleg32).mono ⟨[_, _], rfl⟩
  have hd3 := ArgNormal.head target Γ5 hleg32
  exact hk Γ6 (.var Γ.length) (.var Γ2.length) (.var Γ3.length) (.var Γ5.length) hExt6 hd0 hd1 hd2
    hd3

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
  refine isLegal_let_op1_normal target (.zext 32 64) d0 _ rfl
    (by simp [LegalTarget.isLegalOp, h32, h64, hlt]) hd0 hleg64 ?_
  let Γ1 := (i64, VarKind.normal) :: Γ
  have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
  refine isLegal_let_op1_normal target (.zext 32 64) d1 _ rfl
    (by simp [LegalTarget.isLegalOp, h32, h64, hlt]) (hd1.mono hExt1) hleg64 ?_
  let Γ2 := (i64, VarKind.normal) :: Γ1
  have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i64) (.var Γ1.length) (.imm 32#64) _ rfl
    (by simp [LegalTarget.isLegalOp, h64]) (ArgNormal.head target Γ1 hleg64) hleg64 hleg64 ?_
  let Γ3 := (i64, VarKind.normal) :: Γ2
  have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i64) (.var Γ.length) (.var Γ2.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h64])
      ((ArgNormal.head target Γ hleg64).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ2 hleg64) hleg64 ?_
  let Γ4 := (i64, VarKind.normal) :: Γ3
  have hExt4 : CtxExtends Γ Γ4 := hExt3.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.zext 32 64) d2 _ rfl
    (by simp [LegalTarget.isLegalOp, h32, h64, hlt]) (hd2.mono hExt4) hleg64 ?_
  let Γ5 := (i64, VarKind.normal) :: Γ4
  have hExt5 : CtxExtends Γ Γ5 := hExt4.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.zext 32 64) d3 _ rfl
    (by simp [LegalTarget.isLegalOp, h32, h64, hlt]) (hd3.mono hExt5) hleg64 ?_
  let Γ6 := (i64, VarKind.normal) :: Γ5
  have hExt6 : CtxExtends Γ Γ6 := hExt5.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i64) (.var Γ5.length) (.imm 32#64) _ rfl
    (by simp [LegalTarget.isLegalOp, h64]) (ArgNormal.head target Γ5 hleg64) hleg64 hleg64 ?_
  let Γ7 := (i64, VarKind.normal) :: Γ6
  have hExt7 : CtxExtends Γ Γ7 := hExt6.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i64) (.var Γ4.length) (.var Γ6.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h64])
      ((ArgNormal.head target Γ4 hleg64).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ6 hleg64) hleg64 ?_
  let Γ8 := (i64, VarKind.normal) :: Γ7
  have hExt8 : CtxExtends Γ Γ8 := hExt7.trans (CtxExtends.cons _ _)
  have hw0 : ArgNormal target Γ8 i64 (.var Γ3.length) :=
    (ArgNormal.head target Γ3 hleg64).mono ⟨[_, _, _, _], rfl⟩
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
  refine isLegal_let_op1_normal target (.trunc 32 8) d _ rfl
    (by simp [LegalTarget.isLegalOp, h32, h8, hlt]) hd hleg8 ?_
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
  have hb0 : ArgNormal target Γ7 i8 (.var Γ.length) :=
    (ArgNormal.head target Γ hleg8).mono ⟨[_, _, _, _, _, _], rfl⟩
  have hb1 : ArgNormal target Γ7 i8 (.var Γ2.length) :=
    (ArgNormal.head target Γ2 hleg8).mono ⟨[_, _, _, _], rfl⟩
  have hb2 : ArgNormal target Γ7 i8 (.var Γ4.length) :=
    (ArgNormal.head target Γ4 hleg8).mono ⟨[_, _], rfl⟩
  exact hk Γ7 (.var Γ.length) (.var Γ2.length) (.var Γ4.length) (.var Γ6.length) hExt7 hb0 hb1 hb2
    (ArgNormal.head target Γ6 hleg8)

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
  refine isLegal_let_op1_normal target (.zext 8 32) b0 _ rfl
    (by simp [LegalTarget.isLegalOp, h8, h32, hlt]) hb0 hleg32 ?_
  let Γ1 := (i32, VarKind.normal) :: Γ
  have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
  refine isLegal_let_op1_normal target (.zext 8 32) b1 _ rfl
    (by simp [LegalTarget.isLegalOp, h8, h32, hlt]) (hb1.mono hExt1) hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i32) (.var Γ1.length) (.imm 8#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (ArgNormal.head target Γ1 hleg32) hleg32 hleg32 ?_
  let Γ3 := (i32, VarKind.normal) :: Γ2
  have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i32) (.var Γ.length) (.var Γ2.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
      ((ArgNormal.head target Γ hleg32).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ2 hleg32) hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have hExt4 : CtxExtends Γ Γ4 := hExt3.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.zext 8 32) b2 _ rfl
    (by simp [LegalTarget.isLegalOp, h8, h32, hlt]) (hb2.mono hExt4) hleg32 ?_
  let Γ5 := (i32, VarKind.normal) :: Γ4
  have hExt5 : CtxExtends Γ Γ5 := hExt4.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i32) (.var Γ4.length) (.imm 16#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (ArgNormal.head target Γ4 hleg32) hleg32 hleg32 ?_
  let Γ6 := (i32, VarKind.normal) :: Γ5
  have hExt6 : CtxExtends Γ Γ6 := hExt5.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i32) (.var Γ3.length) (.var Γ5.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
      ((ArgNormal.head target Γ3 hleg32).mono (by refine ⟨[_, _], rfl⟩))
    (ArgNormal.head target Γ5 hleg32) hleg32 ?_
  let Γ7 := (i32, VarKind.normal) :: Γ6
  have hExt7 : CtxExtends Γ Γ7 := hExt6.trans (CtxExtends.cons _ _)
  refine isLegal_let_op1_normal target (.zext 8 32) b3 _ rfl
    (by simp [LegalTarget.isLegalOp, h8, h32, hlt]) (hb3.mono hExt7) hleg32 ?_
  let Γ8 := (i32, VarKind.normal) :: Γ7
  have hExt8 : CtxExtends Γ Γ8 := hExt7.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.shl i32) (.var Γ7.length) (.imm 24#32) _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (ArgNormal.head target Γ7 hleg32) hleg32 hleg32 ?_
  let Γ9 := (i32, VarKind.normal) :: Γ8
  have hExt9 : CtxExtends Γ Γ9 := hExt8.trans (CtxExtends.cons _ _)
  refine isLegal_let_op2_normal target (.or i32) (.var Γ6.length) (.var Γ8.length) _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
      ((ArgNormal.head target Γ6 hleg32).mono (by refine ⟨[_, _], rfl⟩))
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
  refine dwordToBytes4_isLegal target h8 h32 d1 (hd1.mono hExt1) fun Γ2 b4 b5 b6 b7 hExt2 hb4 hb5
    hb6 hb7 => ?_
  have hExt12 := hExt1.trans hExt2
  refine dwordToBytes4_isLegal target h8 h32 d2 (hd2.mono hExt12) fun Γ3 b8 b9 b10 b11 hExt3 hb8 hb9
    hb10 hb11 => ?_
  have hExt13 := hExt12.trans hExt3
  refine dwordToBytes4_isLegal target h8 h32 d3 (hd3.mono hExt13) fun Γ4 b12 b13 b14 b15 hExt4 hb12
    hb13 hb14 hb15 => ?_
  have hExt24 := hExt2.trans (hExt3.trans hExt4)
  have hExt34 := hExt3.trans hExt4
  refine hk Γ4 _ (hExt13.trans hExt4) fun b hb => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
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
  refine bytes4ToDword_isLegal target h8 h32 _ _ _ _ (gb 0) (gb 1) (gb 2) (gb 3) fun Γ1 d0 hExt1
    hd0 => ?_
  have gb1 := fun i => (gb i).mono hExt1
  refine bytes4ToDword_isLegal target h8 h32 _ _ _ _ (gb1 4) (gb1 5) (gb1 6) (gb1 7) fun Γ2 d1 hExt2
    hd1 => ?_
  have hExt12 := hExt1.trans hExt2
  have gb2 := fun i => (gb i).mono hExt12
  refine bytes4ToDword_isLegal target h8 h32 _ _ _ _ (gb2 8) (gb2 9) (gb2 10) (gb2 11) fun Γ3 d2
    hExt3 hd2 => ?_
  have hExt13 := hExt12.trans hExt3
  have gb3 := fun i => (gb i).mono hExt13
  refine bytes4ToDword_isLegal target h8 h32 _ _ _ _ (gb3 12) (gb3 13) (gb3 14) (gb3 15) fun Γ4 d3
    hExt4 hd3 => ?_
  exact hk Γ4 d0 d1 d2 d3 (hExt13.trans hExt4)
    (hd0.mono (hExt2.trans (hExt3.trans hExt4))) (hd1.mono (hExt3.trans hExt4)) (hd2.mono hExt4) hd3

theorem ArgNormal_scalarShufd128 (target : LegalTarget) {Γ : List (Ty × VarKind)} (imm : BitVec 8)
    (d0 d1 d2 d3 : Arg K i32)
    (hd0 : ArgNormal target Γ i32 d0) (hd1 : ArgNormal target Γ i32 d1)
    (hd2 : ArgNormal target Γ i32 d2) (hd3 : ArgNormal target Γ i32 d3) :
    let r := scalarShufd128 imm d0 d1 d2 d3
    ArgNormal target Γ i32 r.1 ∧ ArgNormal target Γ i32 r.2.1 ∧
    ArgNormal target Γ i32 r.2.2.1 ∧ ArgNormal target Γ i32 r.2.2.2 := by
  have hpick : ∀ i,
    ArgNormal target Γ i32
    (match (imm.toNat >>> (2 * i)) % 4 with | 0 => d0 | 1 => d1 | 2 => d2 | _ => d3) := by
    intro i; split <;> first | exact hd0 | exact hd1 | exact hd2 | exact hd3
  exact ⟨hpick 0, hpick 1, hpick 2, hpick 3⟩

theorem scalarBlendwLane_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)} (imm : BitVec 8) (idx : Nat)
    (ai bi : Arg K i32) (ha : ArgNormal target Γ i32 ai) (hb : ArgNormal target Γ i32 bi)
    {cont : Arg K i32 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i32 r) cont) :
    (toTFlat (scalarBlendwLane imm idx ai bi cont) Γ.length Δ.length).isLegal target Γ Δ = true :=
      by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [scalarBlendwLane]
  cases imm.getLsbD (2 * idx) <;> cases imm.getLsbD (2 * idx + 1)
  · exact hk Γ ai (CtxExtends.refl Γ) ha
  · refine isLegal_let_op2_normal target (.and i32) ai (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) ha hleg32 hleg32 ?_
    let Γ1 := (i32, VarKind.normal) :: Γ
    have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
    refine isLegal_let_op2_normal target (.and i32) bi (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) (hb.mono hExt1) hleg32 hleg32 ?_
    let Γ2 := (i32, VarKind.normal) :: Γ1
    have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
    refine isLegal_let_op2_normal target (.or i32) (.var Γ.length) (.var Γ1.length) _ rfl
      (by simp [LegalTarget.isLegalOp, h32])
        ((ArgNormal.head target Γ hleg32).mono (CtxExtends.cons _ _))
      (ArgNormal.head target Γ1 hleg32) hleg32 ?_
    exact hk _ (.var Γ2.length) (hExt2.trans (CtxExtends.cons _ _))
      (ArgNormal.head target Γ2 hleg32)
  · refine isLegal_let_op2_normal target (.and i32) ai (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) ha hleg32 hleg32 ?_
    let Γ1 := (i32, VarKind.normal) :: Γ
    have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
    refine isLegal_let_op2_normal target (.and i32) bi (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, h32]) (hb.mono hExt1) hleg32 hleg32 ?_
    let Γ2 := (i32, VarKind.normal) :: Γ1
    have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
    refine isLegal_let_op2_normal target (.or i32) (.var Γ.length) (.var Γ1.length) _ rfl
      (by simp [LegalTarget.isLegalOp, h32])
        ((ArgNormal.head target Γ hleg32).mono (CtxExtends.cons _ _))
      (ArgNormal.head target Γ1 hleg32) hleg32 ?_
    exact hk _ (.var Γ2.length) (hExt2.trans (CtxExtends.cons _ _))
      (ArgNormal.head target Γ2 hleg32)
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
    (toTFlat (scalarBlendw128 imm a0 a1 a2 a3 b0 b1 b2 b3 k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
  simp only [scalarBlendw128]
  refine scalarBlendwLane_isLegal target h32 imm 0 a0 b0 ha0 hb0 fun Γ1 r0 hExt1 hr0 => ?_
  refine scalarBlendwLane_isLegal target h32 imm 1 a1 b1 (ha1.mono hExt1) (hb1.mono hExt1) fun Γ2 r1
    hExt2 hr1 => ?_
  have hExt12 := hExt1.trans hExt2
  refine scalarBlendwLane_isLegal target h32 imm 2 a2 b2 (ha2.mono hExt12) (hb2.mono hExt12) fun Γ3
    r2 hExt3 hr2 => ?_
  have hExt13 := hExt12.trans hExt3
  refine scalarBlendwLane_isLegal target h32 imm 3 a3 b3 (ha3.mono hExt13) (hb3.mono hExt13) fun Γ4
    r3 hExt4 hr3 => ?_
  exact hk Γ4 r0 r1 r2 r3 (hExt13.trans hExt4)
    (hr0.mono (hExt2.trans (hExt3.trans hExt4))) (hr1.mono (hExt3.trans hExt4)) (hr2.mono hExt4) hr3

theorem scalarAlignr128_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h8 : 8 ∈ target.bitWidths) (h32 : 32 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
      (imm : BitVec 8)
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
    (toTFlat (scalarAlignr128 imm h0 h1 h2 h3 l0 l1 l2 l3 k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
  have hleg8 : target.isLegalTy i8 = true := by simpa [LegalTarget.isLegalTy] using h8
  simp only [scalarAlignr128]
  refine dwords4ToBytes16_isLegal target h8 h32 l0 l1 l2 l3 hl0 hl1 hl2 hl3 fun Γ1 lbs hExt1 hlbs =>
    ?_
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
    (toTFlat (scalarShufb128 a0 a1 a2 a3 m0 m1 m2 m3 k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
  simp only [scalarShufb128]
  refine dwords4ToBytes16_isLegal target h8 h32 a0 a1 a2 a3 ha0 ha1 ha2 ha3 fun Γ1 abs hExt1 habs =>
    ?_
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
  refine isLegal_let_op2_normal target (.and i32) x y _ rfl (by simp [LegalTarget.isLegalOp, h32])
    hx hy hleg32 ?_
  let Γ1 := (i32, VarKind.normal) :: Γ
  refine isLegal_let_op1_normal target (.not i32) x _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (hx.mono ⟨[_], rfl⟩) hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  refine isLegal_let_op2_normal target (.and i32) (.var Γ1.length) z _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
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
  refine isLegal_let_op2_normal target (.and i32) x y _ rfl (by simp [LegalTarget.isLegalOp, h32])
    hx hy hleg32 ?_
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
    {k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 →
      Arg K i32 → Expr K KL rs}
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
  refine isLegal_let_op2_normal target (.add i32) chv s1 _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
    (hch.mono hExt2) hs1 hleg32 ?_
  let Γ3 := (i32, VarKind.normal) :: Γ2
  have h13 : CtxExtends Γ Γ3 := CtxExtends.cons' _ h12
  refine isLegal_let_op2_normal target (.add i32) (.var Γ2.length) wk _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
    (ArgNormal.head target Γ2 hleg32) (hwk.mono h13) hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have h14 : CtxExtends Γ Γ4 := CtxExtends.cons' _ h13
  refine isLegal_let_op2_normal target (.add i32) (.var Γ3.length) h _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
    (ArgNormal.head target Γ3 hleg32) (hh.mono h14) hleg32 ?_
  let Γ5 := (i32, VarKind.normal) :: Γ4
  have h15 : CtxExtends Γ Γ5 := CtxExtends.cons' _ h14
  refine emitShaMaj_isLegal target h32 a b c (ha.mono h15) (hb.mono h15) (hc'.mono h15) fun Γ6 majv
    hExt6 hmaj => ?_
  have h16 : CtxExtends Γ Γ6 := h15.trans hExt6
  refine emitShaSigma0_isLegal target h32 a (ha.mono h16) fun Γ7 s0 hExt7 hs0 => ?_
  have h17 : CtxExtends Γ Γ7 := h16.trans hExt7
  have htExt : CtxExtends Γ5 Γ7 := hExt6.trans hExt7
  have ht : ArgNormal target Γ7 i32 (.var Γ4.length) :=
    (ArgNormal.head target Γ4 hleg32).mono htExt
  refine isLegal_let_op2_normal target (.add i32) (.var Γ4.length) majv _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
    ht (hmaj.mono hExt7) hleg32 ?_
  let Γ8 := (i32, VarKind.normal) :: Γ7
  have h18 : CtxExtends Γ Γ8 := CtxExtends.cons' _ h17
  refine isLegal_let_op2_normal target (.add i32) (.var Γ7.length) s0 _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
    (ArgNormal.head target Γ7 hleg32) (hs0.mono (CtxExtends.cons _ _)) hleg32 ?_
  let Γ9 := (i32, VarKind.normal) :: Γ8
  have h19 : CtxExtends Γ Γ9 := CtxExtends.cons' _ h18
  refine isLegal_let_op2_normal target (.add i32) (.var Γ4.length) d _ rfl
    (by simp [LegalTarget.isLegalOp, h32])
    (ht.mono ⟨[_, _], rfl⟩) (hd.mono h19) hleg32 ?_
  let Γ10 := (i32, VarKind.normal) :: Γ9
  have h110 : CtxExtends Γ Γ10 := CtxExtends.cons' _ h19
  exact hk Γ10 (.var Γ8.length) a b c (.var Γ9.length) e f g h110
    ((ArgNormal.head target Γ8 hleg32).mono ⟨[_], rfl⟩) (ha.mono h110) (hb.mono h110)
      (hc'.mono h110)
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
    (toTFlat (scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [scalarSha256msg1, emitAdd32]
  refine emitShaSig0_isLegal target h32 a1 ha1 fun Γ1 s0 hExt1 hs0 => ?_
  refine isLegal_let_op2_normal target (.add i32) a0 s0 _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ha0.mono hExt1) hs0 hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  have h12 : CtxExtends Γ Γ2 := CtxExtends.cons' _ hExt1
  refine emitShaSig0_isLegal target h32 a2 (ha2.mono h12) fun Γ3 s1 hExt3 hs1 => ?_
  have h13 : CtxExtends Γ Γ3 := h12.trans hExt3
  refine isLegal_let_op2_normal target (.add i32) a1 s1 _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ha1.mono h13) hs1 hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have h14 : CtxExtends Γ Γ4 := CtxExtends.cons' _ h13
  refine emitShaSig0_isLegal target h32 a3 (ha3.mono h14) fun Γ5 s2 hExt5 hs2 => ?_
  have h15 : CtxExtends Γ Γ5 := h14.trans hExt5
  refine isLegal_let_op2_normal target (.add i32) a2 s2 _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ha2.mono h15) hs2 hleg32 ?_
  let Γ6 := (i32, VarKind.normal) :: Γ5
  have h16 : CtxExtends Γ Γ6 := CtxExtends.cons' _ h15
  refine emitShaSig0_isLegal target h32 b0 (hb0.mono h16) fun Γ7 s3 hExt7 hs3 => ?_
  have h17 : CtxExtends Γ Γ7 := h16.trans hExt7
  refine isLegal_let_op2_normal target (.add i32) a3 s3 _ rfl (by simp [LegalTarget.isLegalOp, h32])
    (ha3.mono h17) hs3 hleg32 ?_
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
    (toTFlat (scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
  have hleg32 : target.isLegalTy i32 = true := by simpa [LegalTarget.isLegalTy] using h32
  simp only [scalarSha256msg2, emitAdd32]
  refine emitShaSig1_isLegal target h32 w2 hw2 fun Γ1 sig2 hExt1 hsig2 => ?_
  refine isLegal_let_op2_normal target (.add i32) s0 sig2 _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (hs0.mono hExt1) hsig2 hleg32 ?_
  let Γ2 := (i32, VarKind.normal) :: Γ1
  have h12 : CtxExtends Γ Γ2 := CtxExtends.cons' _ hExt1
  refine emitShaSig1_isLegal target h32 w3 (hw3.mono h12) fun Γ3 sig3 hExt3 hsig3 => ?_
  have h13 : CtxExtends Γ Γ3 := h12.trans hExt3
  refine isLegal_let_op2_normal target (.add i32) s1 sig3 _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (hs1.mono h13) hsig3 hleg32 ?_
  let Γ4 := (i32, VarKind.normal) :: Γ3
  have h14 : CtxExtends Γ Γ4 := CtxExtends.cons' _ h13
  refine emitShaSig1_isLegal target h32 (.var Γ1.length)
    ((ArgNormal.head target Γ1 hleg32).mono
    (hExt3.trans (CtxExtends.cons (i32, VarKind.normal) Γ3)))
    fun Γ5 sig16 hExt5 hsig16 => ?_
  have h15 : CtxExtends Γ Γ5 := h14.trans hExt5
  refine isLegal_let_op2_normal target (.add i32) s2 sig16 _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (hs2.mono h15) hsig16 hleg32 ?_
  let Γ6 := (i32, VarKind.normal) :: Γ5
  have h16 : CtxExtends Γ Γ6 := CtxExtends.cons' _ h15
  refine emitShaSig1_isLegal target h32 (.var Γ3.length)
    ((ArgNormal.head target Γ3 hleg32).mono
    (hExt5.trans (CtxExtends.cons (i32, VarKind.normal) Γ5)))
    fun Γ7 sig17 hExt7 hsig17 => ?_
  have h17 : CtxExtends Γ Γ7 := h16.trans hExt7
  refine isLegal_let_op2_normal target (.add i32) s3 sig17 _ rfl
    (by simp [LegalTarget.isLegalOp, h32]) (hs3.mono h17) hsig17 hleg32 ?_
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

theorem legalSimdScalar128_goWords_isLegal (target : LegalTarget) {Δ : List (List Ty)}
  {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) (t : Ty)
      (ht : target.supportsTy t = true)
    (on128 : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 →
      Arg K i32 →
      (Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs) → Expr K KL rs)
    (hon128 : ∀ {Γ' : List (Ty × VarKind)} (a0 a1 a2 a3 b0 b1 b2 b3 : Arg K i32)
        (k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs),
      ArgNormal target Γ' i32 a0 → ArgNormal target Γ' i32 a1 → ArgNormal target Γ' i32 a2 →
        ArgNormal target Γ' i32 a3 →
      ArgNormal target Γ' i32 b0 → ArgNormal target Γ' i32 b1 → ArgNormal target Γ' i32 b2 →
        ArgNormal target Γ' i32 b3 →
      (∀ Γ'' r0 r1 r2 r3, CtxExtends Γ' Γ'' →
        ArgNormal target Γ'' i32 r0 → ArgNormal target Γ'' i32 r1 → ArgNormal target Γ'' i32 r2 →
          ArgNormal target Γ'' i32 r3 →
        (toTFlat (k r0 r1 r2 r3) Γ''.length Δ.length).isLegal target Γ'' Δ = true) →
      (toTFlat (on128 a0 a1 a2 a3 b0 b1 b2 b3 k) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (k : Tup (Arg K) (target.legalTys t) → Expr K KL rs) :
    ∀ {Γ : List (Ty × VarKind)} (wx wy acc : List (Arg K i64)),
      (∀ w ∈ wx, ArgNormal target Γ i64 w) → (∀ w ∈ wy, ArgNormal target Γ i64 w) →
      (∀ w ∈ acc, ArgNormal target Γ i64 w) →
      (∀ Γ' res, CtxExtends Γ Γ' → ArgsNormal target Γ' res →
        (toTFlat (k res) Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (legalSimdScalar128.goWords target on128 t k wx wy acc) Γ.length Δ.length).isLegal
        target Γ Δ = true
  | Γ, x0 :: x1 :: rxs, y0 :: y1 :: rys, acc, hwx, hwy, hacc, hk => by
    have h64 := valid_mem64 hv
    rw [legalSimdScalar128.goWords.eq_1]
    refine words2ToDwords4_isLegal target h32 h64 x0 x1 (hwx x0 (by simp)) (hwx x1 (by simp))
      fun Γ1 a0 a1 a2 a3 hExt1 ha0 ha1 ha2 ha3 => ?_
    refine words2ToDwords4_isLegal target h32 h64 y0 y1 ((hwy y0 (by simp)).mono hExt1)
      ((hwy y1 (by simp)).mono hExt1)
      fun Γ2 b0 b1 b2 b3 hExt2 hb0 hb1 hb2 hb3 => ?_
    have h12 := hExt1.trans hExt2
    refine hon128 a0 a1 a2 a3 b0 b1 b2 b3 _ (ha0.mono hExt2) (ha1.mono hExt2) (ha2.mono hExt2)
      (ha3.mono hExt2)
      hb0 hb1 hb2 hb3 fun Γ3 r0 r1 r2 r3 hExt3 hr0 hr1 hr2 hr3 => ?_
    refine dwords4ToWords2_isLegal target h32 h64 r0 r1 r2 r3 hr0 hr1 hr2 hr3 fun Γ4 w0 w1 hExt4 hw0
      hw1 => ?_
    have h14 := h12.trans (hExt3.trans hExt4)
    refine legalSimdScalar128_goWords_isLegal target hv h32 t ht on128 hon128 k rxs rys
      (acc ++ [w0, w1])
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
    exact packLeavesToLegal_isLegal target t fres hfres fun Γ2 res hExt2 =>
      hk Γ2 res (hExt1.trans hExt2)
  | Γ, [x0], wy, acc, _, _, hacc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    refine unpackWords64ToLeaves_isLegal target hv acc hacc 0 t ht fun Γ1 fres hExt1 hfres => ?_
    exact packLeavesToLegal_isLegal target t fres hfres fun Γ2 res hExt2 =>
      hk Γ2 res (hExt1.trans hExt2)
  | Γ, x0 :: x1 :: rxs, [], acc, _, _, hacc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    refine unpackWords64ToLeaves_isLegal target hv acc hacc 0 t ht fun Γ1 fres hExt1 hfres => ?_
    exact packLeavesToLegal_isLegal target t fres hfres fun Γ2 res hExt2 =>
      hk Γ2 res (hExt1.trans hExt2)
  | Γ, x0 :: x1 :: rxs, [y0], acc, _, _, hacc, hk => by
    rw [legalSimdScalar128.goWords.eq_def]
    refine unpackWords64ToLeaves_isLegal target hv acc hacc 0 t ht fun Γ1 fres hExt1 hfres => ?_
    exact packLeavesToLegal_isLegal target t fres hfres fun Γ2 res hExt2 =>
      hk Γ2 res (hExt1.trans hExt2)

theorem legalSimdScalar128_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths)
    (on128 : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 →
      Arg K i32 →
      (Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs) → Expr K KL rs)
    (hon128 : ∀ {Γ' : List (Ty × VarKind)} (a0 a1 a2 a3 b0 b1 b2 b3 : Arg K i32)
        (k : Arg K i32 → Arg K i32 → Arg K i32 → Arg K i32 → Expr K KL rs),
      ArgNormal target Γ' i32 a0 → ArgNormal target Γ' i32 a1 → ArgNormal target Γ' i32 a2 →
        ArgNormal target Γ' i32 a3 →
      ArgNormal target Γ' i32 b0 → ArgNormal target Γ' i32 b1 → ArgNormal target Γ' i32 b2 →
        ArgNormal target Γ' i32 b3 →
      (∀ Γ'' r0 r1 r2 r3, CtxExtends Γ' Γ'' →
        ArgNormal target Γ'' i32 r0 → ArgNormal target Γ'' i32 r1 → ArgNormal target Γ'' i32 r2 →
          ArgNormal target Γ'' i32 r3 →
        (toTFlat (k r0 r1 r2 r3) Γ''.length Δ.length).isLegal target Γ'' Δ = true) →
      (toTFlat (on128 a0 a1 a2 a3 b0 b1 b2 b3 k) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (t : Ty) {Γ : List (Ty × VarKind)} (ht : target.supportsTy t = true)
    (xs ys : Tup (Arg K) (target.legalTys t)) (hxs : ArgsNormal target Γ xs)
      (hys : ArgsNormal target Γ ys)
    {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k) :
    (toTFlat (legalSimdScalar128 target on128 t xs ys k) Γ.length Δ.length).isLegal target Γ Δ =
      true := by
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


end LegalIsLegal

end LeanQbe.T
