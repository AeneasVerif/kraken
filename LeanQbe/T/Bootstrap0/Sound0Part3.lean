module

public import LeanQbe.T.Bootstrap0.Sound0Part2
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.IselLemmas4

/-!
# Bootstrap Stage B (`Sound0Part3`): `emitOp0`, Linear Memory/Mul, & `.jnz` Specs

Proves x86-64 functional correctness (`x64ScalarMach.FallsTo` / `_root_.Program.wp`) for:
1. Scalar `emitOp0` dispatch (`un`, `bin`, `cmp`, `select`, `conv`, `div`/`rem`).
2. Linear memory & widening mul (`emitLinUmulw0_spec`, `emitLinLoad0_spec`, `emitLinStore0_spec`).
3. Conditional branch preparation (`jnzPrep0_spec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64

section

/-! ## 1. Scalar ALU, Shift, Compare/Select, Conv, & Div/Rem (`emitOp0_spec`) -/

private def alu0ToBinKind : AluKind0 → AluBinKind
  | .add => .add | .sub => .sub | .mul => .mul | .and => .and | .or => .or | .xor => .xor

private theorem alu0ToOp_eq (w : Width) (k : AluKind0) (rd rs : Reg64)
    (hwk : ¬(w = .W8 ∧ k = .mul)) :
    insW w (alu0ToOp w k rd rs) = aluBinIns w (alu0ToBinKind k) rd (.reg (regW w rs)) := by
  cases w <;> cases k <;> first | rfl | exact absurd ⟨rfl, rfl⟩ hwk

private def shift0ToShiftKind : ShiftKind0 → ShiftKind
  | .shl => .shl | .lshr => .lshr | .ashr => .ashr | .rotl => .rotl | .rotr => .rotr

private def bin0ToShift0 : BinOp0 → ShiftKind0
  | .shl => .shl | .lshr => .lshr | .ashr => .ashr | .rotl => .rotl | _ => .rotr

private def bin0ToAlu0 : BinOp0 → AluKind0
  | .add => .add | .sub => .sub | .mul => .mul | .and => .and | .or => .or | _ => .xor

private def selWidth0 : Ty0 → Width
  | .b64 => .W64 | _ => .W32

private theorem emitCmpSelect0_true_eq (co : CmpOp) (t : Ty0) :
    emitCmpSelect0 true co t [] =
      .cmovcc (selWidth0 t) .nz .rax .rsi ::
        pushDRR0 0 (selWidth0 t) .rax .rdx (pushDRR0 4 .W8 .rdi .rdi []) := by
  cases t <;> rfl

private theorem shift0_wp_bits (b : BinOp0) (w : Width)
    (hb : b = .shl ∨ b = .lshr ∨ b = .ashr ∨ b = .rotl ∨ b = .rotr) :
    match w with
    | .W8 => ∀ {va vb : BitVec 8} {P : Tup Val [.bits 8] → Prop},
      OpCode.wp (op0ToOpCode (.bin b .b8)) (va, vb, ()) P →
      P ((shift0ToShiftKind (bin0ToShift0 b)).eval va (vb.toNat % 8), ())
    | .W16 => ∀ {va vb : BitVec 16} {P : Tup Val [.bits 16] → Prop},
      OpCode.wp (op0ToOpCode (.bin b .b16)) (va, vb, ()) P →
      P ((shift0ToShiftKind (bin0ToShift0 b)).eval va (vb.toNat % 16), ())
    | .W32 => ∀ {va vb : BitVec 32} {P : Tup Val [.bits 32] → Prop},
      OpCode.wp (op0ToOpCode (.bin b .b32)) (va, vb, ()) P →
      P ((shift0ToShiftKind (bin0ToShift0 b)).eval va (vb.toNat % 32), ())
    | .W64 => ∀ {va vb : BitVec 64} {P : Tup Val [.bits 64] → Prop},
      OpCode.wp (op0ToOpCode (.bin b .b64)) (va, vb, ()) P →
      P ((shift0ToShiftKind (bin0ToShift0 b)).eval va (vb.toNat % 64), ()) := by
  cases w <;> intro va vb P hwp <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact hwp

private theorem fallsTo_shiftCl0 (w : Width) (sk : ShiftKind0) (s : MachineData) (k : Nat)
    (hk_lt : k < w.bits)
    (hk : (if w = .W64 then ((s.regs.get64 .rcx).take 8).toNat &&& 63
           else ((s.regs.get64 .rcx).take 8).toNat &&& 31) = k) :
    Directive.FallsTo (insW w (shift0ToOp w sk .rax)) s (fun s' =>
      ∃ rv status,
        rv.setWidth w.bits = (shift0ToShiftKind sk).eval ((s.regs.get64 .rax).setWidth w.bits) k ∧
        s' = { s with regs := s.regs.set64 .rax rv, status }) := by
  intro _ p _ _ _ hcont
  by_cases hk0 : k = 0
  · subst hk0
    cases w <;>
      simp only [Reg64s.get64, show (Width.W8 = .W64) ↔ False by decide,
        show (Width.W16 = .W64) ↔ False by decide, show (Width.W32 = .W64) ↔ False by decide,
        ↓reduceIte] at hk <;>
      cases sk <;>
      simp only [shift0ToOp, insW, regW, t_step_simp] <;>
      rw [hk] <;> simp only [beq_self_eq_true, ↓reduceIte] <;>
      { obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 _ s .rax _ s.status
        exact hcont _ ⟨rv, s.status, hrv.trans (ShiftKind.eval_zero _ _).symm, hs⟩ }
  · have hk0' : (k == 0) = false := beq_false_of_ne hk0
    have hrun : ∀ (lt_w : Bool), lt_w = decide (k < w.bits) → True := fun _ _ => trivial
    cases w <;>
      simp only [Reg64s.get64, show (Width.W8 = .W64) ↔ False by decide,
        show (Width.W16 = .W64) ↔ False by decide, show (Width.W32 = .W64) ↔ False by decide,
        ↓reduceIte] at hk hk_lt ⊢ <;>
      cases sk <;>
      simp only [shift0ToOp, insW, regW, t_step_simp, Effects.All] <;>
      rw [hk] <;>
      simp only [hk0', hk_lt, Bool.false_eq_true, ↓reduceIte] <;>
      (try intro af) <;>
      { by_cases hk1 : k = 1
        · subst hk1; simp only [beq_self_eq_true, ↓reduceIte]
          try dsimp only [ShiftKind.eval]
          obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 _ s .rax _ _
          exact hcont _ ⟨rv, _, hrv, hs⟩
        · simp only [beq_false_of_ne hk1, Bool.false_eq_true, ↓reduceIte]; intro _
          try dsimp only [ShiftKind.eval]
          obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 _ s .rax _ _
          exact hcont _ ⟨rv, _, hrv, hs⟩ }

private theorem emitUn0_neg_bits {symName : Sym0 → Sym} {h : Host} {k : Nat} (w : Width)
    {v : BitVec w.bits} {P : BitVec w.bits → Prop} {s : MachineData}
    {post : MachineState → Prop}
    (hs : s.regs.get64 .rdi = v.setWidth 64) (hwp : P (-v)) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitCanon0 w .rax
        (pushDUnary0 1 w .rax .rax (pushDRR0 0 .W64 .rax .rdi [])))))
      x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : BitVec w.bits, P rv ∧
        s'.regs.get64 .rax = rv.setWidth 64 ∧ s'.dmem = s.dmem) post := by
  have heq : emitCanon0 w .rax (pushDUnary0 1 w .rax .rax (pushDRR0 0 .W64 .rax .rdi [])) =
      emitCanon0 w .rax [] ++
        (pushDUnary0 1 w .rax .rax [] ++ pushDRR0 0 .W64 .rax .rdi []) := by
    rw [(emitCanon0_acc w .rax _).1, (pushDUnary0_acc 1 w .rax .rax _).1]
  rw [heq, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
  have h1 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))) [.rax] [] maskNone s
      (fun s1 => s1.regs.get64 .rax = v.setWidth 64 ∧ s1.dmem = s.dmem) post :=
    Machine.FallsTo.conseq (scalar_movD_fallsTo .rax .rdi s)
      (fun _ ⟨ha, hm⟩ _ => ⟨ha.trans hs, hm⟩)
  have hneg : ∀ (s1 : MachineData), s1.regs.get64 .rax = v.setWidth 64 → s1.dmem = s.dmem →
      x64ScalarMach.FallsTo x64CondReads h (k + (toAmd64Program symName
        (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))).length)
        (toAmd64Program symName (emitFwd0 (pushDUnary0 1 w .rax .rax [])))
        [.rax] [] maskAll s1
        (fun s2 => GprHolds (s2.regs.get64 .rax) (.bits w.bits) (-v) ∧ s2.dmem = s.dmem) post := by
    intro s1 hs1 hm1
    dsimp only [pushDUnary0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
      toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
    refine scalar_fallsTo_single (fallsTo_negW w s1 .rax) ?_
    rintro s2 ⟨rv, st, hrv, rfl⟩
    have hholds : GprHolds rv (.bits w.bits) (-v) := by
      apply (GprHolds.bits_iff w rv (-v)).2
      rw [hrv, hs1, setWidth_64_setWidth]
    exact ⟨⟨by simpa [Reg64s.get64_set64_same] using hholds, hm1⟩,
      scalarFrame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ .rax r _
        (fun e => hr (List.mem_singleton.mpr e.symm))) (scalarUpdFlags_maskAll _ _)⟩
  have h12 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
        toAmd64Program symName (emitFwd0 (pushDUnary0 1 w .rax .rax [])))
      ([.rax] ++ [.rax]) ([] ++ []) (maskNone ||| maskAll) s
      (fun s2 => GprHolds (s2.regs.get64 .rax) (.bits w.bits) (-v) ∧ s2.dmem = s.dmem) post :=
    Machine.FallsTo.comp h1 fun s1 ⟨ha1, hm1⟩ _ => hneg s1 ha1 hm1
  have h123 : x64ScalarMach.FallsTo x64CondReads h k
      ((toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
          toAmd64Program symName (emitFwd0 (pushDUnary0 1 w .rax .rax []))) ++
        toAmd64Program symName (emitFwd0 (emitCanon0 w .rax [])))
      (([.rax] ++ [.rax]) ++ [.rax]) (([] ++ []) ++ []) ((maskNone ||| maskAll) ||| maskNone) s
      (fun s3 => ∃ rv : BitVec w.bits, P rv ∧
        s3.regs.get64 .rax = rv.setWidth 64 ∧ s3.dmem = s.dmem) post :=
    Machine.FallsTo.comp h12 fun s2 ⟨hg2, hm2⟩ _ =>
      Machine.FallsTo.conseq (emitCanon0_spec w .rax) fun s3 ⟨ha3, hm3⟩ _ =>
        ⟨-v, hwp, ha3.trans (congrArg (BitVec.setWidth 64) ((GprHolds.bits_iff w _ _).1 hg2)),
          hm3.trans hm2⟩
  exact Machine.FallsTo.weaken h123
    (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)

private theorem emitUn0_not_bits {symName : Sym0 → Sym} {h : Host} {k : Nat} (w : Width)
    {v : BitVec w.bits} {P : BitVec w.bits → Prop} {s : MachineData}
    {post : MachineState → Prop}
    (hs : s.regs.get64 .rdi = v.setWidth 64) (hwp : P (~~~v)) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitCanon0 w .rax
        (pushDUnary0 0 w .rax .rax (pushDRR0 0 .W64 .rax .rdi [])))))
      x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : BitVec w.bits, P rv ∧
        s'.regs.get64 .rax = rv.setWidth 64 ∧ s'.dmem = s.dmem) post := by
  have heq : emitCanon0 w .rax (pushDUnary0 0 w .rax .rax (pushDRR0 0 .W64 .rax .rdi [])) =
      emitCanon0 w .rax [] ++
        (pushDUnary0 0 w .rax .rax [] ++ pushDRR0 0 .W64 .rax .rdi []) := by
    rw [(emitCanon0_acc w .rax _).1, (pushDUnary0_acc 0 w .rax .rax _).1]
  rw [heq, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
  have h1 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))) [.rax] [] maskNone s
      (fun s1 => s1.regs.get64 .rax = v.setWidth 64 ∧ s1.dmem = s.dmem) post :=
    Machine.FallsTo.conseq (scalar_movD_fallsTo .rax .rdi s)
      (fun _ ⟨ha, hm⟩ _ => ⟨ha.trans hs, hm⟩)
  have hnot : ∀ (s1 : MachineData), s1.regs.get64 .rax = v.setWidth 64 → s1.dmem = s.dmem →
      x64ScalarMach.FallsTo x64CondReads h (k + (toAmd64Program symName
        (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))).length)
        (toAmd64Program symName (emitFwd0 (pushDUnary0 0 w .rax .rax [])))
        [.rax] [] maskNone s1
        (fun s2 => GprHolds (s2.regs.get64 .rax) (.bits w.bits) (~~~v) ∧ s2.dmem = s.dmem)
        post := by
    intro s1 hs1 hm1
    dsimp only [pushDUnary0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
      toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
    refine scalar_fallsTo_single (fallsTo_notW w s1 .rax) ?_
    rintro s2 ⟨rv, hrv, rfl⟩
    have hholds : GprHolds rv (.bits w.bits) (~~~v) := by
      apply (GprHolds.bits_iff w rv (~~~v)).2
      rw [hrv, hs1, setWidth_64_setWidth]
    exact ⟨⟨by simpa [Reg64s.get64_set64_same] using hholds, hm1⟩,
      scalarFrame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ .rax r _
        (fun e => hr (List.mem_singleton.mpr e.symm)))
        (scalarUpdFlags_of_status_eq rfl _)⟩
  have h12 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
        toAmd64Program symName (emitFwd0 (pushDUnary0 0 w .rax .rax [])))
      ([.rax] ++ [.rax]) ([] ++ []) (maskNone ||| maskNone) s
      (fun s2 => GprHolds (s2.regs.get64 .rax) (.bits w.bits) (~~~v) ∧ s2.dmem = s.dmem) post :=
    Machine.FallsTo.comp h1 fun s1 ⟨ha1, hm1⟩ _ => hnot s1 ha1 hm1
  have h123 : x64ScalarMach.FallsTo x64CondReads h k
      ((toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
          toAmd64Program symName (emitFwd0 (pushDUnary0 0 w .rax .rax []))) ++
        toAmd64Program symName (emitFwd0 (emitCanon0 w .rax [])))
      (([.rax] ++ [.rax]) ++ [.rax]) (([] ++ []) ++ []) ((maskNone ||| maskNone) ||| maskNone) s
      (fun s3 => ∃ rv : BitVec w.bits, P rv ∧
        s3.regs.get64 .rax = rv.setWidth 64 ∧ s3.dmem = s.dmem) post :=
    Machine.FallsTo.comp h12 fun s2 ⟨hg2, hm2⟩ _ =>
      Machine.FallsTo.conseq (emitCanon0_spec w .rax) fun s3 ⟨ha3, hm3⟩ _ =>
        ⟨~~~v, hwp, ha3.trans (congrArg (BitVec.setWidth 64) ((GprHolds.bits_iff w _ _).1 hg2)),
          hm3.trans hm2⟩
  exact Machine.FallsTo.weaken h123
    (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)

private theorem emitUn0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (u : UnOp0) (t : Ty0)
    (hnu : ¬(u = .neg ∧ t = .bool)) {v : Val (ty0ToTy t)} {P : Tup Val [ty0ToTy t] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs : s.regs.get64 .rdi = toCanon64 t v)
    (hwp : OpCode.wp (op0ToOpCode (.un u t)) (v, ()) P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitUn0 u t []))) x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : Val (ty0ToTy t), P (rv, ()) ∧
        s'.regs.get64 .rax = toCanon64 t rv ∧ s'.dmem = s.dmem) post := by
  have h1 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))) [.rax] [] maskNone s
      (fun s1 => s1.regs.get64 .rax = toCanon64 t v ∧ s1.dmem = s.dmem) post :=
    Machine.FallsTo.conseq (scalar_movD_fallsTo .rax .rdi s)
      (fun _ ⟨ha, hm⟩ _ => ⟨ha.trans hs, hm⟩)
  cases u with
  | copy =>
    have hwp' : P (v, ()) := hwp
    dsimp only [emitUn0]
    rw [(emitCanon0_acc (tyWidth0 t) .rax _).1, emitFwd0_append, toAmd64Program_append]
    have hcomp : x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
          toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) .rax [])))
        ([.rax] ++ [.rax]) ([] ++ []) (maskNone ||| maskNone) s
        (fun s' => ∃ rv : Val (ty0ToTy t), P (rv, ()) ∧
          s'.regs.get64 .rax = toCanon64 t rv ∧ s'.dmem = s.dmem) post :=
      Machine.FallsTo.comp h1 fun s1 ⟨ha1, hm1⟩ _ => Machine.FallsTo.conseq
        (emitCanon0_ty_spec t .rax (by rw [ha1]; exact toCanon64_toGprHolds t v))
        fun _ ⟨ha2, hm2⟩ _ => ⟨v, hwp', ha2, hm2.trans hm1⟩
    exact Machine.FallsTo.weaken hcomp
      (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)
  | neg =>
    cases t with
    | bool => exact absurd ⟨rfl, rfl⟩ hnu
    | b8 | b16 | b32 | b64 =>
      dsimp only [emitUn0, tyWidth0, ty0ToTy, Val, op0ToOpCode, OpCode.wp, toCanon64] at *
      exact Machine.FallsTo.conseq
        (emitUn0_neg_bits _ (v := v) (P := fun rv => P (rv, ()))
          (by rw [hs]; try exact (BitVec.setWidth_eq v).symm) hwp)
        fun _ ⟨rv, hrv, hr, hm⟩ _ =>
          ⟨rv, hrv, by rw [hr]; try exact BitVec.setWidth_eq rv, hm⟩
  | not =>
    cases t with
    | bool =>
      have hwp' : P (!v, ()) := hwp
      dsimp only [emitUn0, pushDRR0, pushDUnary0, pushDImm0, emitFwd0, List.reverse_cons,
        List.reverse_nil, List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil,
        dir0ToAmd64, List.append_nil, alu0ToOp]
      apply scalar_fallsTo_of_wp; intro _ E
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD s .rax .rdi)) ?_; rintro _ rfl
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD _ .r11 1#64)) ?_; rintro _ rfl
      have halu := fallsTo_aluBinIns_reg .W32 .xor
        { s with regs := (s.regs.set64 .rax (s.regs.get64 .rdi)).set64 .r11 1#64 } .rax .r11
      rw [← show alu0ToBinKind .xor = .xor from rfl,
        ← alu0ToOp_eq .W32 .xor .rax .r11 (fun h => by cases h.1)] at halu
      refine Program.wp.cons (Directive.FallsTo.wp halu) ?_
      rintro _ ⟨rv3, st3, hrv3, rfl⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 _ .rax .rax)) ?_
      rintro _ rfl
      have hr_x : (((s.regs.set64 .rax (s.regs.get64 .rdi)).set64 .r11 1#64).get64 .rax) =
          toCanon64 .bool v := by
        rw [Reg64s.get64_set64_of_ne _ .r11 .rax _ (by decide), Reg64s.get64_set64_same, hs]
      have hr_11 : (((s.regs.set64 .rax (s.regs.get64 .rdi)).set64 .r11 1#64).get64 .r11) =
          1#64 := Reg64s.get64_set64_same ..
      have hlow : (rv3.setWidth 32) = (toCanon64 .bool v).setWidth 32 ^^^ 1#32 := by
        dsimp only [alu0ToBinKind] at hrv3
        simpa [AluBinKind.eval, Width.bits, hr_x, hr_11] using hrv3
      have hres : ((rv3.setWidth 8).setWidth 64) = toCanon64 .bool (!v) := by
        rw [← BitVec.setWidth_setWidth_of_le rv3 (by decide : 8 ≤ 32), hlow]
        cases v <;> decide
      refine ⟨⟨!v, hwp', by rw [Reg64s.get64_set64_same]; exact hres, rfl⟩,
        scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
      simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.2.2.2.2.2.2),
        Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]
    | b8 | b16 | b32 | b64 =>
      dsimp only [emitUn0, tyWidth0, ty0ToTy, Val, op0ToOpCode, OpCode.wp, toCanon64] at *
      exact Machine.FallsTo.conseq
        (emitUn0_not_bits _ (v := v) (P := fun rv => P (rv, ()))
          (by rw [hs]; try exact (BitVec.setWidth_eq v).symm) hwp)
        fun _ ⟨rv, hrv, hr, hm⟩ _ =>
          ⟨rv, hrv, by rw [hr]; try exact BitVec.setWidth_eq rv, hm⟩

private theorem fallsTo_shMaskCl0 (imm : UInt64) (s : MachineData) :
    Directive.FallsTo (ins32 (.and (.reg (d .rcx)) (.imm (.int64 (Int64.ofNat imm.toNat))))) s
      (fun s' => ∃ status', s' =
        { s with
          regs := s.regs.set64 .rcx
            ((((s.regs.get64 .rcx).setWidth 32) &&& BitVec.ofNat 32 imm.toNat).setWidth 64),
          status := status' }) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, ConstExpr.interp, Effects.All, Reg64s.set,
    BitVec.zeroExtend_eq_setWidth]
  intro _
  have htr : (Int64.ofNat imm.toNat).toBitVec.truncate 32 = BitVec.ofNat 32 imm.toNat := by
    rw [Int64_toBitVec_ofNat, BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide)]
  simp only [Width.bits, BitVec.truncate_eq_setWidth] at *
  rw [htr]
  exact hk _ ⟨_, rfl⟩

private theorem bitvec_take8_toNat (x : BitVec 64) : (x.take 8).toNat = x.toNat % 256 := by
  rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

private theorem emitBinShift0_bits {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (sk : ShiftKind0) (w : Width) {va vb : BitVec w.bits} {P : BitVec w.bits → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs1 : s.regs.get64 .rdi = va.setWidth 64)
    (hs2 : s.regs.get64 .rsi = vb.setWidth 64)
    (hwp : P ((shift0ToShiftKind sk).eval va (vb.toNat % w.bits))) :
    let dMask : List Dir0 := match w with
      | .W8 => pushDImm0 3 .rcx 7 [] | .W16 => pushDImm0 3 .rcx 15 [] | _ => []
    let body := emitCanon0 w .rax (pushDShift0 w sk .rax
      (dMask ++ pushDRR0 0 .W64 .rcx .rsi (pushDRR0 0 .W64 .rax .rdi [])))
    x64ScalarMach.FallsTo x64CondReads h k (toAmd64Program symName (emitFwd0 body))
      x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : BitVec w.bits, P rv ∧
        s'.regs.get64 .rax = rv.setWidth 64 ∧ s'.dmem = s.dmem) post := by
  let dMask : List Dir0 := match w with
    | .W8 => pushDImm0 3 .rcx 7 [] | .W16 => pushDImm0 3 .rcx 15 [] | _ => []
  let rv : BitVec w.bits := (shift0ToShiftKind sk).eval va (vb.toNat % w.bits)
  have hrv_p : P rv := hwp
  have hm_ax : ∀ (s0 : MachineData),
      x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))) [.rax] [] maskNone s0
        (fun s1 => s1.regs.get64 .rax = s0.regs.get64 .rdi ∧ s1.dmem = s0.dmem) post :=
    fun s0 => scalar_movD_fallsTo .rax .rdi s0
  have hsplit : emitCanon0 w .rax (pushDShift0 w sk .rax
        (dMask ++ pushDRR0 0 .W64 .rcx .rsi (pushDRR0 0 .W64 .rax .rdi []))) =
      emitCanon0 w .rax [] ++
        (pushDShift0 w sk .rax [] ++
          (dMask ++ (pushDRR0 0 .W64 .rcx .rsi [] ++ pushDRR0 0 .W64 .rax .rdi []))) := by
    rw [(emitCanon0_acc w .rax _).1]
    congr 1
  have hbody : emitFwd0 (emitCanon0 w .rax (pushDShift0 w sk .rax
        (dMask ++ pushDRR0 0 .W64 .rcx .rsi (pushDRR0 0 .W64 .rax .rdi [])))) =
      emitFwd0 (pushDRR0 0 .W64 .rax .rdi []) ++
        emitFwd0 (pushDRR0 0 .W64 .rcx .rsi []) ++
        emitFwd0 dMask ++
        emitFwd0 (pushDShift0 w sk .rax []) ++
        emitFwd0 (emitCanon0 w .rax []) := by
    rw [hsplit]; simp only [emitFwd0_append, List.append_assoc]
  have hload : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []) ++
        emitFwd0 (pushDRR0 0 .W64 .rcx .rsi [])))
      [.rax, .rcx] [] maskNone s
      (fun s2 => s2.regs.get64 .rax = va.setWidth 64 ∧
        s2.regs.get64 .rcx = vb.setWidth 64 ∧ s2.dmem = s.dmem) post := by
    rw [toAmd64Program_append]
    have hcomp : x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
          toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rcx .rsi [])))
        ([.rax] ++ [.rcx]) ([] ++ []) (maskNone ||| maskNone) s
        (fun s2 => s2.regs.get64 .rax = va.setWidth 64 ∧
          s2.regs.get64 .rcx = vb.setWidth 64 ∧ s2.dmem = s.dmem) post :=
      Machine.FallsTo.comp (hm_ax s) fun s1 ⟨ha1, hm1⟩ hfr1 => by
        have hrsi1 := hfr1.1 .rsi (by simp)
        dsimp only [x64ScalarMach] at hrsi1
        exact Machine.FallsTo.conseq (scalar_movD_fallsTo .rcx .rsi s1)
          fun s2 ⟨hc2, hm2⟩ hfr2 => by
            have hrax2 := hfr2.1 .rax (by simp)
            dsimp only [x64ScalarMach] at hrax2
            exact ⟨by rw [hrax2, ha1, hs1], hc2.trans (hrsi1.trans hs2), hm2.trans hm1⟩
    exact Machine.FallsTo.weaken hcomp
      (fun r hr => by simp_all) (fun _ hv => nomatch hv) (by decide)
  have hmask : ∀ (s2 : MachineData),
      s2.regs.get64 .rax = va.setWidth 64 → s2.regs.get64 .rcx = vb.setWidth 64 →
      s2.dmem = s.dmem →
      x64ScalarMach.FallsTo x64CondReads h
        (k + (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []) ++
          emitFwd0 (pushDRR0 0 .W64 .rcx .rsi []))).length)
        (toAmd64Program symName (emitFwd0 dMask))
        [.rcx] [] maskAll s2
        (fun s3 => s3.regs.get64 .rax = va.setWidth 64 ∧ s3.dmem = s.dmem ∧
          (if w = .W64 then ((s3.regs.get64 .rcx).take 8).toNat &&& 63
           else ((s3.regs.get64 .rcx).take 8).toNat &&& 31) = vb.toNat % w.bits)
        post := by
    intro s2 ha2 hc2 hm2
    have h5 : (31 : Nat) = 2 ^ 5 - 1 := rfl
    have h6 : (63 : Nat) = 2 ^ 6 - 1 := rfl
    cases w with
    | W8 =>
      dsimp only [dMask, pushDImm0, emitFwd0, List.reverse_cons, List.reverse_nil,
        List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64,
        List.append_nil]
      refine scalar_fallsTo_single (fallsTo_shMaskCl0 7 s2) ?_
      rintro s3 ⟨st3, rfl⟩
      refine ⟨⟨ha2, hm2, ?_⟩, scalarFrame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ .rcx r _
        (fun e => hr (List.mem_singleton.mpr e.symm))) (scalarUpdFlags_maskAll _ _)⟩
      have hlt := vb.isLt
      simp only [show (Width.W8 = .W64) ↔ False by decide, ↓reduceIte,
        Reg64s.get64_set64_same, bitvec_take8_toNat, hc2, BitVec.toNat_setWidth,
        BitVec.toNat_and, BitVec.toNat_ofNat, Width.bits] at hlt ⊢
      have hmask8 : (7 : UInt64).toNat % 2 ^ 32 = 2 ^ 3 - 1 := rfl
      rw [Nat.mod_eq_of_lt (by omega : vb.toNat < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : vb.toNat < 2 ^ 32), hmask8,
        Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (by omega : vb.toNat % 2 ^ 3 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : vb.toNat % 2 ^ 3 < 256),
        h5, Nat.and_two_pow_sub_one_eq_mod]
      omega
    | W16 =>
      dsimp only [dMask, pushDImm0, emitFwd0, List.reverse_cons, List.reverse_nil,
        List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64,
        List.append_nil]
      refine scalar_fallsTo_single (fallsTo_shMaskCl0 15 s2) ?_
      rintro s3 ⟨st3, rfl⟩
      refine ⟨⟨ha2, hm2, ?_⟩, scalarFrame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ .rcx r _
        (fun e => hr (List.mem_singleton.mpr e.symm))) (scalarUpdFlags_maskAll _ _)⟩
      have hlt := vb.isLt
      simp only [show (Width.W16 = .W64) ↔ False by decide, ↓reduceIte,
        Reg64s.get64_set64_same, bitvec_take8_toNat, hc2, BitVec.toNat_setWidth,
        BitVec.toNat_and, BitVec.toNat_ofNat, Width.bits] at hlt ⊢
      have hmask16 : (15 : UInt64).toNat % 2 ^ 32 = 2 ^ 4 - 1 := rfl
      rw [Nat.mod_eq_of_lt (by omega : vb.toNat < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : vb.toNat < 2 ^ 32), hmask16,
        Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (by omega : vb.toNat % 2 ^ 4 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : vb.toNat % 2 ^ 4 < 256),
        h5, Nat.and_two_pow_sub_one_eq_mod]
      omega
    | W32 =>
      dsimp only [dMask, emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
      refine Machine.FallsTo.nil ⟨ha2, hm2, ?_⟩
      simp only [show (Width.W32 = .W64) ↔ False by decide, ↓reduceIte, bitvec_take8_toNat,
        hc2, BitVec.toNat_setWidth, Width.bits]
      rw [h5, Nat.and_two_pow_sub_one_eq_mod]
      have hlt := vb.isLt
      omega
    | W64 =>
      dsimp only [dMask, emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
      refine Machine.FallsTo.nil ⟨ha2, hm2, ?_⟩
      simp only [↓reduceIte, bitvec_take8_toNat, hc2, BitVec.toNat_setWidth, Width.bits]
      rw [h6, Nat.and_two_pow_sub_one_eq_mod]
      have hlt := vb.isLt
      omega
  dsimp only [] at *
  rw [hbody, toAmd64Program_append, toAmd64Program_append, toAmd64Program_append]
  have hshift : ∀ (s3 : MachineData),
      s3.regs.get64 .rax = va.setWidth 64 → s3.dmem = s.dmem →
      (if w = .W64 then ((s3.regs.get64 .rcx).take 8).toNat &&& 63
       else ((s3.regs.get64 .rcx).take 8).toNat &&& 31) = vb.toNat % w.bits →
      x64ScalarMach.FallsTo x64CondReads h
        (k + (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []) ++
          emitFwd0 (pushDRR0 0 .W64 .rcx .rsi []) ++ emitFwd0 dMask)).length)
        (toAmd64Program symName (emitFwd0 (pushDShift0 w sk .rax [])))
        [.rax] [] maskAll s3
        (fun s4 => GprHolds (s4.regs.get64 .rax) (.bits w.bits) rv ∧ s4.dmem = s.dmem) post := by
    intro s3 ha3 hm3 hmod3
    dsimp only [pushDShift0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
      toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
    refine scalar_fallsTo_single (fallsTo_shiftCl0 w sk s3
      (vb.toNat % w.bits) (Nat.mod_lt _ (width_bits_pos w)) hmod3) ?_
    rintro s4 ⟨rv4, st4, hrv4, rfl⟩
    have hholds : GprHolds rv4 (.bits w.bits) rv := by
      apply (GprHolds.bits_iff w rv4 rv).2
      rw [hrv4, ha3, setWidth_64_setWidth]
    exact ⟨⟨by simpa [Reg64s.get64_set64_same] using hholds, hm3⟩, scalarFrame_of_eq
      (fun r hr => Reg64s.get64_set64_of_ne _ .rax r _
        (fun e => hr (List.mem_singleton.mpr e.symm)))
      (scalarUpdFlags_maskAll _ _)⟩
  have h12 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []) ++
        emitFwd0 (pushDRR0 0 .W64 .rcx .rsi [])) ++
        toAmd64Program symName (emitFwd0 dMask))
      ([.rax, .rcx] ++ [.rcx]) ([] ++ []) (maskNone ||| maskAll) s
      (fun s3 => s3.regs.get64 .rax = va.setWidth 64 ∧ s3.dmem = s.dmem ∧
        (if w = .W64 then ((s3.regs.get64 .rcx).take 8).toNat &&& 63
         else ((s3.regs.get64 .rcx).take 8).toNat &&& 31) = vb.toNat % w.bits) post :=
    Machine.FallsTo.comp hload fun s2 ⟨ha2, hc2, hm2⟩ _ => hmask s2 ha2 hc2 hm2
  have h123 : x64ScalarMach.FallsTo x64CondReads h k
      ((toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []) ++
          emitFwd0 (pushDRR0 0 .W64 .rcx .rsi [])) ++
          toAmd64Program symName (emitFwd0 dMask)) ++
        toAmd64Program symName (emitFwd0 (pushDShift0 w sk .rax [])))
      (([.rax, .rcx] ++ [.rcx]) ++ [.rax]) (([] ++ []) ++ [])
      ((maskNone ||| maskAll) ||| maskAll) s
      (fun s4 => GprHolds (s4.regs.get64 .rax) (.bits w.bits) rv ∧ s4.dmem = s.dmem) post :=
    Machine.FallsTo.comp h12 fun s3 ⟨ha3, hm3, hmod3⟩ _ => by
      simpa [toAmd64Program_append, List.length_append] using hshift s3 ha3 hm3 hmod3
  have hfull : x64ScalarMach.FallsTo x64CondReads h k
      (((toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []) ++
            emitFwd0 (pushDRR0 0 .W64 .rcx .rsi [])) ++
          toAmd64Program symName (emitFwd0 dMask)) ++
          toAmd64Program symName (emitFwd0 (pushDShift0 w sk .rax []))) ++
        toAmd64Program symName (emitFwd0 (emitCanon0 w .rax [])))
      ((([.rax, .rcx] ++ [.rcx]) ++ [.rax]) ++ [.rax]) ((([] ++ []) ++ []) ++ [])
      (((maskNone ||| maskAll) ||| maskAll) ||| maskNone) s
      (fun s' => ∃ rv : BitVec w.bits, P rv ∧
        s'.regs.get64 .rax = rv.setWidth 64 ∧ s'.dmem = s.dmem) post :=
    Machine.FallsTo.comp h123 fun s4 ⟨hg4, hm4⟩ _ =>
      Machine.FallsTo.conseq (emitCanon0_spec w .rax) fun s5 ⟨ha5, hm5⟩ _ =>
        ⟨rv, hrv_p, ha5.trans (congrArg (BitVec.setWidth 64) ((GprHolds.bits_iff w _ _).1 hg4)),
          hm5.trans hm4⟩
  exact Machine.FallsTo.weaken hfull (fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (((rfl | rfl) | rfl) | rfl) | rfl <;> simp [x64ScratchAndAbi])
    (fun _ hv => nomatch hv) (by decide)

private theorem emitBinShift0_body (b : BinOp0) (t : Ty0) :
    emitBinShift0 b t [] = emitCanon0 (tyWidth0 t) .rax
      (pushDShift0 (tyWidth0 t) (bin0ToShift0 b) .rax
        ((match tyWidth0 t with
          | .W8 => pushDImm0 3 .rcx 7 [] | .W16 => pushDImm0 3 .rcx 15 [] | _ => []) ++
         pushDRR0 0 .W64 .rcx .rsi (pushDRR0 0 .W64 .rax .rdi []))) := by
  dsimp only [emitBinShift0, bin0ToShift0]
  congr 2
  have hm2 : ∀ x, (match tyWidth0 t with
        | .W8 => pushDImm0 3 .rcx 7 x | .W16 => pushDImm0 3 .rcx 15 x | _ => x) =
      (match tyWidth0 t with
        | .W8 => pushDImm0 3 .rcx 7 [] | .W16 => pushDImm0 3 .rcx 15 [] | _ => []) ++ x := by
    intro x; cases tyWidth0 t <;>
      first | exact (pushDImm0_acc 3 .rcx _ _ x (Or.inl (by decide))).1 | rfl
  exact hm2 _

private theorem emitBinShift0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (b : BinOp0)
    (t : Ty0) (ht : t ≠ .bool)
    (hb : b = .shl ∨ b = .lshr ∨ b = .ashr ∨ b = .rotl ∨ b = .rotr)
    {va vb : Val (ty0ToTy t)} {P : Tup Val [ty0ToTy t] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs1 : s.regs.get64 .rdi = toCanon64 t va)
    (hs2 : s.regs.get64 .rsi = toCanon64 t vb)
    (hwp : OpCode.wp (op0ToOpCode (.bin b t)) (va, vb, ()) P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitBinShift0 b t []))) x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : Val (ty0ToTy t), P (rv, ()) ∧
        s'.regs.get64 .rax = toCanon64 t rv ∧ s'.dmem = s.dmem) post := by
  cases t with
  | bool => exact absurd rfl ht
  | b8 =>
    rw [emitBinShift0_body]
    exact emitBinShift0_bits (bin0ToShift0 b) .W8 (va := va) (vb := vb)
      (P := fun rv => P (rv, ())) hs1 hs2 (shift0_wp_bits b .W8 hb hwp)
  | b16 =>
    rw [emitBinShift0_body]
    exact emitBinShift0_bits (bin0ToShift0 b) .W16 (va := va) (vb := vb)
      (P := fun rv => P (rv, ())) hs1 hs2 (shift0_wp_bits b .W16 hb hwp)
  | b32 =>
    rw [emitBinShift0_body]
    exact emitBinShift0_bits (bin0ToShift0 b) .W32 (va := va) (vb := vb)
      (P := fun rv => P (rv, ())) hs1 hs2 (shift0_wp_bits b .W32 hb hwp)
  | b64 =>
    rw [emitBinShift0_body]
    dsimp only [ty0ToTy, Val, Width.bits, toCanon64] at va vb hs1 hs2 ⊢
    exact Machine.FallsTo.conseq
      (emitBinShift0_bits (bin0ToShift0 b) .W64 (va := va) (vb := vb)
        (P := fun rv => P (rv, ()))
        (by rw [hs1, BitVec.setWidth_eq]) (by rw [hs2, BitVec.setWidth_eq])
        (shift0_wp_bits b .W64 hb hwp))
      fun _ ⟨rv, hrv, hr, hm⟩ _ => ⟨rv, hrv, by rw [hr, BitVec.setWidth_eq], hm⟩

private theorem emitBinAlu0_bits {symName : Sym0 → Sym} {h : Host} {k : Nat} (b : BinOp0)
    (w : Width) (hw : w = .W16 ∨ w = .W32 ∨ w = .W64)
    (_hb : b = .add ∨ b = .sub ∨ b = .mul ∨ b = .and ∨ b = .or ∨ b = .xor)
    {va vb : BitVec w.bits} {P : BitVec w.bits → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs1 : s.regs.get64 .rdi = va.setWidth 64)
    (hs2 : s.regs.get64 .rsi = vb.setWidth 64)
    (hp_ok : P ((alu0ToBinKind (bin0ToAlu0 b)).eval va vb)) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitBinAlu0 b (widthTy0 w) [])))
      x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : BitVec w.bits, P rv ∧
        s'.regs.get64 .rax = rv.setWidth 64 ∧ s'.dmem = s.dmem) post := by
  let ak : AluKind0 := bin0ToAlu0 b
  let rv : BitVec w.bits := (alu0ToBinKind ak).eval va vb
  have hrv_p : P rv := hp_ok
  have hload : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))) [.rax] [] maskNone s
      (fun s1 => s1.regs.get64 .rax = va.setWidth 64 ∧
        s1.regs.get64 .rsi = vb.setWidth 64 ∧ s1.dmem = s.dmem) post :=
    Machine.FallsTo.conseq (scalar_movD_fallsTo .rax .rdi s)
      (fun s1 ⟨ha, hm⟩ hfr => ⟨ha.trans hs1, (hfr.1 .rsi (by simp)).trans hs2, hm⟩)
  have heq1 : emitBinAlu0 b (widthTy0 w) [] =
      emitCanon0 w .rax [] ++
        (pushDAlu0 w ak .rax .rsi [] ++ pushDRR0 0 .W64 .rax .rdi []) := by
    rcases hw with rfl | rfl | rfl <;>
    · dsimp only [emitBinAlu0, widthTy0, tyWidth0]
      rw [(emitCanon0_acc _ .rax _).1]; rfl
  rw [heq1, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
  have halu_step : ∀ (s1 : MachineData), s1.regs.get64 .rax = va.setWidth 64 →
      s1.regs.get64 .rsi = vb.setWidth 64 → s1.dmem = s.dmem →
      x64ScalarMach.FallsTo x64CondReads h (k + (toAmd64Program symName
        (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))).length)
        (toAmd64Program symName (emitFwd0 (pushDAlu0 w ak .rax .rsi [])))
        [.rax] [] maskAll s1
        (fun s2 => GprHolds (s2.regs.get64 .rax) (.bits w.bits) rv ∧ s2.dmem = s.dmem) post := by
    intro s1 ha1 hb1 hm1
    have hnw8 : ¬(w = .W8 ∧ ak = .mul) := fun hh => by
      rcases hw with rfl | rfl | rfl <;> cases hh.1
    have hd_eq : toAmd64Program symName (emitFwd0 (pushDAlu0 w ak .rax .rsi [])) =
        dir0ToAmd64 symName (.aluRR w ak .rax .rsi) := rfl
    rw [hd_eq]
    dsimp only [dir0ToAmd64]
    rw [alu0ToOp_eq w ak .rax .rsi hnw8]
    refine scalar_fallsTo_single (fallsTo_aluBinIns_reg w (alu0ToBinKind ak) s1 .rax .rsi) ?_
    rintro s2 ⟨rv2, st2, hrv2, rfl⟩
    have hholds : GprHolds rv2 (.bits w.bits) rv := by
      apply (GprHolds.bits_iff w rv2 rv).2
      rw [hrv2, ha1, hb1]
      rcases hw with rfl | rfl | rfl
      · rw [setWidth_64_setWidth .W16, setWidth_64_setWidth .W16]
      · rw [setWidth_64_setWidth .W32, setWidth_64_setWidth .W32]
      · dsimp only [Width.bits]; simp only [BitVec.setWidth_eq]; rfl
    exact ⟨⟨by simpa [Reg64s.get64_set64_same] using hholds, hm1⟩,
      scalarFrame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ .rax r _
        (Ne.symm (fun e => hr (e ▸ List.mem_cons_self)))) (scalarUpdFlags_maskAll _ _)⟩
  have hfull : x64ScalarMach.FallsTo x64CondReads h k
      ((toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
          toAmd64Program symName (emitFwd0 (pushDAlu0 w ak .rax .rsi []))) ++
        toAmd64Program symName (emitFwd0 (emitCanon0 w .rax [])))
      (([.rax] ++ [.rax]) ++ [.rax]) (([] ++ []) ++ []) ((maskNone ||| maskAll) ||| maskNone) s
      (fun s' => ∃ rv : BitVec w.bits, P rv ∧
        s'.regs.get64 .rax = rv.setWidth 64 ∧ s'.dmem = s.dmem) post :=
    Machine.FallsTo.comp (Machine.FallsTo.comp hload
        fun s1 ⟨ha1, hb1, hm1⟩ _ => halu_step s1 ha1 hb1 hm1) fun s2 ⟨hg2, hm2⟩ _ =>
      Machine.FallsTo.conseq (emitCanon0_spec w .rax)
        fun s3 ⟨ha3, hm3⟩ _ =>
          have h2 := (GprHolds.bits_iff w (s2.regs.get64 .rax) rv).1 hg2
          ⟨rv, hrv_p, ha3.trans (congrArg (BitVec.setWidth 64) h2), hm3.trans hm2⟩
  simp only [List.append_assoc] at hfull ⊢
  exact Machine.FallsTo.weaken hfull (fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [x64ScratchAndAbi])
    (fun _ hv => nomatch hv) (by decide)

private theorem emitBinAlu0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (b : BinOp0)
    (t : Ty0)
    (hb : b = .add ∨ b = .sub ∨ b = .mul ∨ b = .and ∨ b = .or ∨ b = .xor)
    (hbt : t = .bool → b = .and ∨ b = .or ∨ b = .xor)
    {va vb : Val (ty0ToTy t)} {P : Tup Val [ty0ToTy t] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs1 : s.regs.get64 .rdi = toCanon64 t va)
    (hs2 : s.regs.get64 .rsi = toCanon64 t vb)
    (hwp : OpCode.wp (op0ToOpCode (.bin b t)) (va, vb, ()) P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitBinAlu0 b t []))) x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : Val (ty0ToTy t), P (rv, ()) ∧
        s'.regs.get64 .rax = toCanon64 t rv ∧ s'.dmem = s.dmem) post := by
  let ak : AluKind0 := bin0ToAlu0 b
  have hload : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi []))) [.rax] [] maskNone s
      (fun s1 => s1.regs.get64 .rax = toCanon64 t va ∧
        s1.regs.get64 .rsi = toCanon64 t vb ∧ s1.dmem = s.dmem) post :=
    Machine.FallsTo.conseq (scalar_movD_fallsTo .rax .rdi s)
      (fun s1 ⟨ha, hm⟩ hfr => ⟨ha.trans hs1, (hfr.1 .rsi (by simp)).trans hs2, hm⟩)
  have htc : t = .bool ∨ t = .b8 ∨ (t = .b16 ∨ t = .b32 ∨ t = .b64) := by
    cases t <;> simp
  rcases htc with rfl | rfl | htge
  · have hwp_b : P (match b with | .and => va && vb | .or => va || vb | _ => xor va vb, ()) := by
      rcases hbt rfl with rfl | rfl | rfl <;> exact hwp
    let rv : Val (ty0ToTy .bool) :=
      match b with | .and => va && vb | .or => va || vb | _ => xor va vb
    rcases hbt rfl with rfl | rfl | rfl <;>
      dsimp only [emitBinAlu0, pushDAlu0] at *
    all_goals
      dsimp only [pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
        toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
      refine scalar_fallsTo_of_wp fun {_} _ => ?_
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD s .rax .rdi)) ?_; rintro _ rfl
      have halu := fallsTo_aluBinIns_reg .W32 (alu0ToBinKind ak)
        { s with regs := s.regs.set64 .rax (s.regs.get64 .rdi) } .rax .rsi
      rw [← alu0ToOp_eq .W32 ak .rax .rsi (fun h => by cases h.1)] at halu
      dsimp only [ak, bin0ToAlu0] at halu
      refine Program.wp.cons (Directive.FallsTo.wp halu) ?_
      rintro _ ⟨rv2, st2, hrv2, rfl⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 _ .rax .rax)) ?_
      rintro _ rfl
      rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .rax .rsi _ (by decide), hs1, hs2]
        at hrv2
      dsimp only [alu0ToBinKind, AluBinKind.eval, Width.bits, toCanon64] at hrv2
      refine ⟨⟨rv, hwp_b, ?_, rfl⟩,
        scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
      · dsimp only
        rw [Reg64s.get64_set64_same, Reg64s.get64_set64_same,
          ← BitVec.setWidth_setWidth_of_le rv2 (by decide : 8 ≤ 32), hrv2]
        dsimp only [rv, toCanon64]
        cases va <;> cases vb <;> decide
      · simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
          Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
          Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp only [emitBinAlu0, pushDAlu0, pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil,
        List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64,
        List.append_nil] <;>
      { refine scalar_fallsTo_of_wp fun {_} _ => ?_
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD s .rax .rdi)) ?_; rintro _ rfl
        first
        | (have halu := fallsTo_aluBinIns_reg .W8 (alu0ToBinKind ak)
             { s with regs := s.regs.set64 .rax (s.regs.get64 .rdi) } .rax .rsi
           rw [← alu0ToOp_eq .W8 ak .rax .rsi
             (fun hh => by dsimp only [ak, bin0ToAlu0] at hh; cases hh.2)] at halu
           dsimp only [ak, bin0ToAlu0] at halu
           refine Program.wp.cons (Directive.FallsTo.wp halu) ?_)
        | (have halu := fallsTo_aluBinIns_reg .W32 (alu0ToBinKind ak)
             { s with regs := s.regs.set64 .rax (s.regs.get64 .rdi) } .rax .rsi
           rw [← alu0ToOp_eq .W32 ak .rax .rsi (fun hh => by cases hh.1)] at halu
           dsimp only [ak, bin0ToAlu0] at halu
           refine Program.wp.cons (Directive.FallsTo.wp halu) ?_)
        rintro _ ⟨rv2, st2, hrv2, rfl⟩
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 _ .rax .rax)) ?_
        rintro _ rfl
        rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .rax .rsi _ (by decide), hs1, hs2]
          at hrv2
        dsimp only [ty0ToTy, Val, op0ToOpCode, OpCode.wp] at hwp
        have h8 : ∀ (x y : BitVec 8),
            toCanon64 .b8 va = x.setWidth 64 → toCanon64 .b8 vb = y.setWidth 64 →
            rv2.setWidth 8 = (alu0ToBinKind ak).eval x y := by
          intro x y hx hy
          first
          | (have h : rv2.setWidth 8 =
                (alu0ToBinKind ak).eval ((x.setWidth 64).setWidth 8)
                  ((y.setWidth 64).setWidth 8) := by
               dsimp only [Width.bits] at hrv2; rw [hx, hy] at hrv2; exact hrv2
             rw [h, setWidth_64_setWidth .W8, setWidth_64_setWidth .W8])
          | (have h : rv2.setWidth 32 =
                (alu0ToBinKind ak).eval ((x.setWidth 64).setWidth 32)
                  ((y.setWidth 64).setWidth 32) := by
               dsimp only [Width.bits] at hrv2; rw [hx, hy] at hrv2; exact hrv2
             dsimp only [ak, bin0ToAlu0, alu0ToBinKind, AluBinKind.eval] at h ⊢
             rw [← BitVec.setWidth_setWidth_of_le rv2 (by decide : 8 ≤ 32), h,
               setWidth_mul_le (by decide : 8 ≤ 32),
               BitVec.setWidth_setWidth_of_le (BitVec.setWidth 64 x) (by decide : 8 ≤ 32),
               BitVec.setWidth_setWidth_of_le (BitVec.setWidth 64 y) (by decide : 8 ≤ 32),
               setWidth_64_setWidth .W8, setWidth_64_setWidth .W8])
        have h8v := h8 va vb rfl rfl
        refine ⟨⟨(alu0ToBinKind ak).eval va vb, hwp,
          by dsimp only; rw [Reg64s.get64_set64_same, Reg64s.get64_set64_same, h8v]; rfl, rfl⟩,
          scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
        simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
          Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
          Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)] }
  · have hstep : ∀ (w : Width) (hw : w = .W16 ∨ w = .W32 ∨ w = .W64) (htw : t = widthTy0 w)
        {x y : BitVec w.bits} {Q : BitVec w.bits → Prop},
        s.regs.get64 .rdi = x.setWidth 64 → s.regs.get64 .rsi = y.setWidth 64 →
        Q ((alu0ToBinKind ak).eval x y) →
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitBinAlu0 b t [])))
          x64ScratchAndAbi [] maskAll s
          (fun s' => ∃ rv : BitVec w.bits, Q rv ∧
            s'.regs.get64 .rax = rv.setWidth 64 ∧ s'.dmem = s.dmem) post := by
      rintro w hw rfl x y Q hx hy hq
      exact emitBinAlu0_bits b w hw hb hx hy hq
    rcases htge with rfl | rfl | rfl
    · dsimp only [ty0ToTy, Val, op0ToOpCode, OpCode.wp, toCanon64, Width.bits] at *
      exact hstep .W16 (.inl rfl) rfl hs1 hs2
        (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hwp)
    · dsimp only [ty0ToTy, Val, op0ToOpCode, OpCode.wp, toCanon64, Width.bits] at *
      exact hstep .W32 (.inr (.inl rfl)) rfl hs1 hs2
        (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hwp)
    · dsimp only [ty0ToTy, Val, op0ToOpCode, OpCode.wp, toCanon64, Width.bits] at *
      exact Machine.FallsTo.conseq
        (hstep .W64 (.inr (.inr rfl)) rfl (x := va) (y := vb)
          (by rw [hs1]; exact (BitVec.setWidth_eq va).symm)
          (by rw [hs2]; exact (BitVec.setWidth_eq vb).symm)
          (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hwp))
        fun _ ⟨rv, hrv, hr, hm⟩ _ => ⟨rv, hrv, by rw [hr, BitVec.setWidth_eq], hm⟩

private theorem emitCmp0_bits {symName : Sym0 → Sym} {h : Host} {k : Nat} (co : CmpOp)
    (w : Width) {va vb : BitVec w.bits} {P : Bool → Prop} {s : MachineData}
    {post : MachineState → Prop}
    (hs1 : s.regs.get64 .rdi = va.setWidth 64)
    (hs2 : s.regs.get64 .rsi = vb.setWidth 64)
    (hwp : P (co.evalBits va vb)) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0
        (pushDRR0 1 .W8 .rax .rax (.setcc (condOf0 co) .rax :: .cmpRR w .rdi .rsi :: []))))
      x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : Bool, P rv ∧
        s'.regs.get64 .rax = toCanon64 .bool rv ∧ s'.dmem = s.dmem) post := by
  have hbits : w.bits = 8 ∨ w.bits = 16 ∨ w.bits = 32 ∨ w.bits = 64 := by
    cases w <;> simp [Width.bits]
  have hcond : condOf0 co = condOf co := by cases co <;> rfl
  dsimp only [pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
    toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64, List.append_nil]
  apply scalar_fallsTo_of_wp; intro _ E
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_cmp_reg w s .rdi .rsi)) ?_
  rintro _ rfl
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_setcc _ (condOf0 co) .rax)) ?_
  rintro _ rfl
  refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 _ .rax .rax)) ?_
  rintro _ rfl
  have hcc : (condOf0 co).interp (subFlags ((s.regs.get64 .rdi).setWidth w.bits)
      ((s.regs.get64 .rsi).setWidth w.bits)) = co.evalBits va vb := by
    rw [hcond, hs1, hs2, cond_subFlags hbits]
    simp [setWidth_64_setWidth]
  have hres :
      (((s.regs.get64 .rax).replaceLow (BitVec.ofNat 8 (co.evalBits va vb).toNat)).setWidth
        8).setWidth 64 =
      toCanon64 .bool (co.evalBits va vb) := by
    rw [replaceLow_setWidth_le (by decide)]
    cases co.evalBits va vb <;> decide
  refine ⟨⟨co.evalBits va vb, hwp, ?_, rfl⟩,
    scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
  · rw [Reg64s.get64_set64_same, Reg64s.get64_set64_same, hcc]; exact hres
  · simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
      Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]

private theorem emitCmpSelect0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (isSel : Bool)
    (co : CmpOp) (t : Ty0) (ht : isSel = false → t ≠ .bool) :
    match isSel with
    | false =>
      ∀ {va vb : Val (ty0ToTy t)} {P : Tup Val [.bool] → Prop} {s : MachineData}
        {post : MachineState → Prop},
        s.regs.get64 .rdi = toCanon64 t va → s.regs.get64 .rsi = toCanon64 t vb →
        OpCode.wp (op0ToOpCode (.cmp co t)) (va, vb, ()) P →
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitCmpSelect0 false co t [])))
          x64ScratchAndAbi [] maskAll s
          (fun s' => ∃ rv : Bool, P (rv, ()) ∧
            s'.regs.get64 .rax = toCanon64 .bool rv ∧ s'.dmem = s.dmem) post
    | true =>
      ∀ {c : Bool} {va vb : Val (ty0ToTy t)} {P : Tup Val [ty0ToTy t] → Prop} {s : MachineData}
        {post : MachineState → Prop},
        s.regs.get64 .rdi = toCanon64 .bool c → s.regs.get64 .rsi = toCanon64 t va →
        s.regs.get64 .rdx = toCanon64 t vb →
        OpCode.wp (op0ToOpCode (.select t)) (c, va, vb, ()) P →
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitCmpSelect0 true co t [])))
          x64ScratchAndAbi [] maskAll s
          (fun s' => ∃ rv : Val (ty0ToTy t), P (rv, ()) ∧
            s'.regs.get64 .rax = toCanon64 t rv ∧ s'.dmem = s.dmem) post := by
  cases isSel with
  | false =>
    intro va vb P s post hs1 hs2 hwp
    have hnt : t ≠ .bool := ht rfl
    cases t with
    | bool => exact absurd rfl hnt
    | b8 | b16 | b32 | b64 =>
      dsimp only [ty0ToTy, Val, op0ToOpCode, OpCode.wp] at va vb P hwp
      dsimp only [emitCmpSelect0]
      exact emitCmp0_bits co _ (va := va) (vb := vb) (P := fun rv => P (rv, ()))
        (by
          dsimp only [toCanon64, Width.bits] at hs1 ⊢
          rw [hs1]; try exact (BitVec.setWidth_eq va).symm)
        (by
          dsimp only [toCanon64, Width.bits] at hs2 ⊢
          rw [hs2]; try exact (BitVec.setWidth_eq vb).symm)
        hwp
  | true =>
    intro c va vb P s post hsc hs1 hs2 hwp
    have hwp' : P (if c then va else vb, ()) := hwp
    have hcw : selWidth0 t = .W32 ∨ selWidth0 t = .W64 := by cases t <;> simp [selWidth0]
    have hc_gh : GprHolds (s.regs.get64 .rdi) .bool c := op0_argsIn_to_regs_bool hsc
    rw [emitCmpSelect0_true_eq]
    dsimp only [pushDRR0, emitFwd0, List.reverse_cons, List.reverse_nil,
      List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64,
      List.append_nil]
    apply scalar_fallsTo_of_wp; intro _ E
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_testb_self s .rdi hc_gh)) ?_
    rintro _ ⟨st1, rfl, hnz⟩
    have hmov :
        Directive.FallsTo (insW (selWidth0 t)
            (.mov (.reg (regW (selWidth0 t) .rax)) (.reg (regW (selWidth0 t) .rdx))))
          { s with status := st1 }
          (fun s' => s' =
            { s with
              regs := s.regs.set64 .rax
                (((s.regs.get64 .rdx).setWidth (selWidth0 t).bits).setWidth 64),
              status := st1 }) := by
      cases t <;> first
        | exact fallsTo_movW .W64 { s with status := st1 } .rax .rdx
        | exact fallsTo_movW .W32 { s with status := st1 } .rax .rdx
    refine Program.wp.cons (Directive.FallsTo.wp hmov) ?_
    rintro _ rfl
    refine Program.wp.mono
      (Directive.FallsTo.wp (fallsTo_cmovcc (selWidth0 t) hcw .nz _ .rax .rsi)) ?_
    rintro _ rfl
    have hcan : ∀ (v : Val (ty0ToTy t)),
        ((toCanon64 t v).setWidth (selWidth0 t).bits).setWidth 64 = toCanon64 t v := fun v => by
      cases t with
      | b64 => simp [selWidth0, Width.bits, BitVec.setWidth_eq]
      | bool | b8 | b16 | b32 => exact canon64_setWidth32_64 (by intro h; cases h)
    have hres :
        (if CondCode.nz.interp st1 then
          (({ s with
              regs := s.regs.set64 .rax
                (((s.regs.get64 .rdx).setWidth (selWidth0 t).bits).setWidth 64),
              status := st1 }.regs.get64 .rsi).setWidth (selWidth0 t).bits)
         else
          (({ s with
              regs := s.regs.set64 .rax
                (((s.regs.get64 .rdx).setWidth (selWidth0 t).bits).setWidth 64),
              status := st1 }.regs.get64 .rax).setWidth (selWidth0 t).bits)).setWidth 64 =
        toCanon64 t (if c then va else vb) := by
      rw [Reg64s.get64_set64_of_ne _ .rax .rsi _ (by decide), hs1,
        Reg64s.get64_set64_same, hnz, hs2]
      cases c <;> simp [hcan]
    refine ⟨⟨if c then va else vb, hwp', ?_, rfl⟩,
      scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
    · rw [Reg64s.get64_set64_same]; exact hres
    · simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]

private theorem widthEq0_iff (a b : Width) : widthEq0 a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem emitConvZext0_bits {symName : Sym0 → Sym} {h : Host} {k : Nat} (m n : Width)
    (hmn : m.bits ≤ n.bits) {va : BitVec m.bits} {s : MachineData}
    {post : MachineState → Prop} (hs : s.regs.get64 .rdi = va.setWidth 64) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitConvZextTrunc0 .zext m n [])))
      x64ScratchAndAbi [] maskNone s
      (fun s' => s'.regs.get64 .rax = (va.setWidth n.bits).setWidth 64 ∧ s'.dmem = s.dmem)
      post := by
  dsimp only [emitConvZextTrunc0]
  by_cases hweq : widthEq0 m n = true
  · obtain rfl := (widthEq0_iff m n).1 hweq
    simp only [hweq, ↓reduceIte]
    have hhe : emitCanon0 m .rax (pushDRR0 0 .W64 .rax .rdi []) =
        emitCanon0 m .rax [] ++ pushDRR0 0 .W64 .rax .rdi [] := (emitCanon0_acc m .rax _).1
    rw [hhe, emitFwd0_append, toAmd64Program_append]
    have hm1 : x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])))
        [.rax] [] maskNone s
        (fun s1 => s1.regs.get64 .rax = va.setWidth 64 ∧ s1.dmem = s.dmem) post :=
      Machine.FallsTo.conseq (scalar_movD_fallsTo .rax .rdi s)
        (fun _ ⟨ha, hm⟩ _ => ⟨ha.trans hs, hm⟩)
    have hcomp : x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
          toAmd64Program symName (emitFwd0 (emitCanon0 m .rax [])))
        ([.rax] ++ [.rax]) ([] ++ []) (maskNone ||| maskNone) s
        (fun s' => s'.regs.get64 .rax = (va.setWidth m.bits).setWidth 64 ∧ s'.dmem = s.dmem)
        post :=
      Machine.FallsTo.comp hm1 fun s1 ⟨ha1, hm1'⟩ _ =>
        Machine.FallsTo.conseq (emitCanon0_spec m .rax) fun s2 ⟨ha2, hm2⟩ _ =>
          ⟨by rw [ha2, ha1, setWidth_64_setWidth, BitVec.setWidth_eq], hm2.trans hm1'⟩
    exact Machine.FallsTo.weaken hcomp
      (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)
  · have hmne : m ≠ n := fun h => hweq ((widthEq0_iff m n).2 h)
    simp only [hweq, Bool.false_eq_true, ↓reduceIte]
    cases m with
    | W8 =>
      refine Machine.FallsTo.weaken
        (Machine.FallsTo.conseq (scalar_movzx8_fallsTo .rax .rdi s) ?_)
        (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)
      intro s' ⟨hr, hm⟩ _
      refine ⟨?_, hm⟩
      rw [hr, hs, setWidth_64_setWidth .W8, setWidth_up_down hmn (width_bits_le_64 n)]
    | W16 =>
      refine Machine.FallsTo.weaken
        (Machine.FallsTo.conseq (scalar_movzx16_fallsTo .rax .rdi s) ?_)
        (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)
      intro s' ⟨hr, hm⟩ _
      refine ⟨?_, hm⟩
      rw [hr, hs, setWidth_64_setWidth .W16, setWidth_up_down hmn (width_bits_le_64 n)]
    | W32 =>
      refine Machine.FallsTo.weaken
        (Machine.FallsTo.conseq (scalar_movlD_fallsTo .rax .rdi s) ?_)
        (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)
      intro s' ⟨hr, hm⟩ _
      refine ⟨?_, hm⟩
      rw [hr, hs, setWidth_64_setWidth .W32, setWidth_up_down hmn (width_bits_le_64 n)]
    | W64 =>
      exfalso; cases n with
      | W8 | W16 | W32 => simp [Width.bits] at hmn
      | W64 => exact hmne rfl

private theorem setWidth_64_setWidth_le {m n : Width} (_hnm : n.bits ≤ m.bits) (v : BitVec m.bits) :
    (v.setWidth 64).setWidth n.bits = v.setWidth n.bits := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, Nat.lt_of_lt_of_le hi (width_bits_le_64 n)]

private theorem emitConvTrunc0_bits {symName : Sym0 → Sym} {h : Host} {k : Nat} (m n : Width)
    (hnm : n.bits ≤ m.bits) {va : BitVec m.bits} {s : MachineData}
    {post : MachineState → Prop} (hs : s.regs.get64 .rdi = va.setWidth 64) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitConvZextTrunc0 .trunc m n [])))
      x64ScratchAndAbi [] maskNone s
      (fun s' => s'.regs.get64 .rax = (va.setWidth n.bits).setWidth 64 ∧ s'.dmem = s.dmem)
      post := by
  dsimp only [emitConvZextTrunc0]
  have hhe : emitCanon0 n .rax (pushDRR0 0 .W64 .rax .rdi []) =
      emitCanon0 n .rax [] ++ pushDRR0 0 .W64 .rax .rdi [] := (emitCanon0_acc n .rax _).1
  rw [hhe, emitFwd0_append, toAmd64Program_append]
  have hm1 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])))
      [.rax] [] maskNone s
      (fun s1 => s1.regs.get64 .rax = va.setWidth 64 ∧ s1.dmem = s.dmem) post :=
    Machine.FallsTo.conseq (scalar_movD_fallsTo .rax .rdi s)
      (fun _ ⟨ha, hm⟩ _ => ⟨ha.trans hs, hm⟩)
  have hcomp : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
        toAmd64Program symName (emitFwd0 (emitCanon0 n .rax [])))
      ([.rax] ++ [.rax]) ([] ++ []) (maskNone ||| maskNone) s
      (fun s' => s'.regs.get64 .rax = (va.setWidth n.bits).setWidth 64 ∧ s'.dmem = s.dmem)
      post :=
    Machine.FallsTo.comp hm1 fun s1 ⟨ha1, hm1'⟩ _ =>
      Machine.FallsTo.conseq (emitCanon0_spec n .rax) fun s2 ⟨ha2, hm2⟩ _ =>
        ⟨by rw [ha2, ha1, setWidth_64_setWidth_le hnm], hm2.trans hm1'⟩
  exact Machine.FallsTo.weaken hcomp
    (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)

private theorem emitConvOfBool0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (m n : Width) {va : Bool} {P : Tup Val [ty0ToTy (widthTy0 n)] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs : s.regs.get64 .rdi = toCanon64 .bool va)
    (hwp : OpCode.wp (op0ToOpCode (.conv .ofBool m n)) (va, ()) P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitConvZextTrunc0 .ofBool m n [])))
      x64ScratchAndAbi [] maskNone s
      (fun s' => ∃ rv : Val (ty0ToTy (widthTy0 n)), P (rv, ()) ∧
        s'.regs.get64 .rax = toCanon64 (widthTy0 n) rv ∧ s'.dmem = s.dmem) post := by
  have hzx := scalar_movzx8_fallsTo (symName := symName) (h := h) (k := k)
    (post := post) .rax .rdi s
  refine Machine.FallsTo.weaken (Machine.FallsTo.conseq hzx ?_)
    (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)
  intro s' ⟨hr, hm⟩ _
  cases n <;>
    dsimp only [ty0ToTy, widthTy0, Val, op0ToOpCode, OpCode.wp, toCanon64] at * <;>
    exact ⟨BitVec.ofNat _ va.toNat, hwp, by rw [hr, hs]; cases va <;> decide, hm⟩

private theorem emitConvZext0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (m n : Width) {va : Val (ty0ToTy (widthTy0 m))} {P : Tup Val [ty0ToTy (widthTy0 n)] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs : s.regs.get64 .rdi = toCanon64 (widthTy0 m) va)
    (hwp : OpCode.wp (op0ToOpCode (.conv .zext m n)) (va, ()) P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitConvZextTrunc0 .zext m n [])))
      x64ScratchAndAbi [] maskNone s
      (fun s' => ∃ rv : Val (ty0ToTy (widthTy0 n)), P (rv, ()) ∧
        s'.regs.get64 .rax = toCanon64 (widthTy0 n) rv ∧ s'.dmem = s.dmem) post := by
  cases m <;> cases n <;>
    dsimp only [ty0ToTy, widthTy0, Val, op0ToOpCode, OpCode.wp, castWidth2Op0, toCanon64] at * <;>
    obtain ⟨hmn, hwp'⟩ := hwp <;>
    exact Machine.FallsTo.conseq
      (emitConvZext0_bits _ _ hmn (va := va)
        (by rw [hs]; try exact (BitVec.setWidth_eq va).symm))
      fun _ ⟨hr, hm⟩ _ =>
        ⟨_, hwp', by rw [hr]; try exact BitVec.setWidth_eq _, hm⟩

private theorem emitConvTrunc0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (m n : Width) {va : Val (ty0ToTy (widthTy0 m))} {P : Tup Val [ty0ToTy (widthTy0 n)] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs : s.regs.get64 .rdi = toCanon64 (widthTy0 m) va)
    (hwp : OpCode.wp (op0ToOpCode (.conv .trunc m n)) (va, ()) P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitConvZextTrunc0 .trunc m n [])))
      x64ScratchAndAbi [] maskNone s
      (fun s' => ∃ rv : Val (ty0ToTy (widthTy0 n)), P (rv, ()) ∧
        s'.regs.get64 .rax = toCanon64 (widthTy0 n) rv ∧ s'.dmem = s.dmem) post := by
  cases m <;> cases n <;>
    dsimp only [ty0ToTy, widthTy0, Val, op0ToOpCode, OpCode.wp, castWidth2Op0, toCanon64] at * <;>
    obtain ⟨hnm, hwp'⟩ := hwp <;>
    exact Machine.FallsTo.conseq
      (emitConvTrunc0_bits _ _ hnm (va := va)
        (by rw [hs]; try exact (BitVec.setWidth_eq va).symm))
      fun _ ⟨hr, hm⟩ _ =>
        ⟨_, hwp', by rw [hr]; try exact BitVec.setWidth_eq _, hm⟩

private theorem emitConvSext0_bits {symName : Sym0 → Sym} {h : Host} {k : Nat} (m n : Width)
    (hmn : m.bits ≤ n.bits) {va : BitVec m.bits} {s : MachineData}
    {post : MachineState → Prop} (hs : s.regs.get64 .rdi = va.setWidth 64) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitConvSext0 m n [])))
      x64ScratchAndAbi [] maskNone s
      (fun s' => s'.regs.get64 .rax = (va.signExtend n.bits).setWidth 64 ∧ s'.dmem = s.dmem)
      post := by
  dsimp only [emitConvSext0]
  by_cases hweq : widthEq0 m n = true
  · obtain rfl := (widthEq0_iff m n).1 hweq
    simp only [hweq, ↓reduceIte]
    have hhe : emitCanon0 m .rax (pushDRR0 0 .W64 .rax .rdi []) =
        emitCanon0 m .rax [] ++ pushDRR0 0 .W64 .rax .rdi [] := (emitCanon0_acc m .rax _).1
    rw [hhe, emitFwd0_append, toAmd64Program_append]
    have hm1 : x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])))
        [.rax] [] maskNone s
        (fun s1 => s1.regs.get64 .rax = va.setWidth 64 ∧ s1.dmem = s.dmem) post :=
      Machine.FallsTo.conseq (scalar_movD_fallsTo .rax .rdi s)
        (fun _ ⟨ha, hm⟩ _ => ⟨ha.trans hs, hm⟩)
    have hcomp : x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (pushDRR0 0 .W64 .rax .rdi [])) ++
          toAmd64Program symName (emitFwd0 (emitCanon0 m .rax [])))
        ([.rax] ++ [.rax]) ([] ++ []) (maskNone ||| maskNone) s
        (fun s' => s'.regs.get64 .rax = (va.signExtend m.bits).setWidth 64 ∧ s'.dmem = s.dmem)
        post :=
      Machine.FallsTo.comp hm1 fun s1 ⟨ha1, hm1'⟩ _ =>
        Machine.FallsTo.conseq (emitCanon0_spec m .rax) fun s2 ⟨ha2, hm2⟩ _ =>
          ⟨by rw [ha2, ha1, setWidth_64_setWidth,
            BitVec.eq_of_toInt_eq
              (BitVec.toInt_signExtend_of_le (x := va) (Nat.le_refl m.bits))],
            hm2.trans hm1'⟩
    exact Machine.FallsTo.weaken hcomp
      (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)
  · have hmne : m ≠ n := fun h => hweq ((widthEq0_iff m n).2 h)
    simp only [hweq, Bool.false_eq_true, ↓reduceIte]
    by_cases hn64 : widthEq0 n .W64 = true
    · obtain rfl := (widthEq0_iff n .W64).1 hn64
      simp only [hn64, ↓reduceIte]
      have hsx := scalar_movsx_fallsTo (symName := symName) (h := h) (k := k) (post := post)
        .W64 (.inr rfl) .rax m .rdi ⟨hmn, .inl rfl⟩ s
      refine Machine.FallsTo.weaken (Machine.FallsTo.conseq hsx ?_)
        (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)
      intro s' ⟨hr, hm⟩ _
      refine ⟨?_, hm⟩
      rw [hr, hs, setWidth_64_setWidth, BitVec.setWidth_eq]
    · have hn_ne64 : n ≠ .W64 := fun h => hn64 ((widthEq0_iff n .W64).2 h)
      have hm_lt32 : m = .W8 ∨ m = .W16 := by
        cases m <;> cases n <;> simp [Width.bits] at hmn hmne hn_ne64 <;> simp
      have hnle32 : n.bits ≤ 32 := by cases n <;> first | exact absurd rfl hn_ne64 | decide
      have hmle32 : m.bits ≤ 32 := by rcases hm_lt32 with rfl | rfl <;> decide
      simp only [hn64, Bool.false_eq_true, ↓reduceIte]
      have hhe : emitCanon0 n .rax (pushDMovsx0 .W32 .rax m .rdi []) =
          emitCanon0 n .rax [] ++ pushDMovsx0 .W32 .rax m .rdi [] := (emitCanon0_acc n .rax _).1
      rw [hhe, emitFwd0_append, toAmd64Program_append]
      have hsx : x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (pushDMovsx0 .W32 .rax m .rdi [])))
          [.rax] [] maskNone s
          (fun s1 => s1.regs.get64 .rax = ((va.signExtend 32).setWidth 64) ∧ s1.dmem = s.dmem)
          post := by
        refine Machine.FallsTo.conseq
          (scalar_movsx_fallsTo .W32 (.inl rfl) .rax m .rdi ⟨hmle32, .inr hm_lt32⟩ s) ?_
        intro s1 ⟨hr1, hm1⟩ _
        rw [hr1, hs, setWidth_64_setWidth]
        exact ⟨rfl, hm1⟩
      have hcomp : x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (pushDMovsx0 .W32 .rax m .rdi [])) ++
            toAmd64Program symName (emitFwd0 (emitCanon0 n .rax [])))
          ([.rax] ++ [.rax]) ([] ++ []) (maskNone ||| maskNone) s
          (fun s' => s'.regs.get64 .rax = (va.signExtend n.bits).setWidth 64 ∧ s'.dmem = s.dmem)
          post :=
        Machine.FallsTo.comp hsx fun s1 ⟨ha1, hm1'⟩ _ =>
          Machine.FallsTo.conseq (emitCanon0_spec n .rax) fun s2 ⟨ha2, hm2⟩ _ =>
            ⟨by rw [ha2, ha1, setWidth_64_setWidth_le (m := .W32) hnle32,
              setWidth_signExtend_of_le hmn hnle32], hm2.trans hm1'⟩
      exact Machine.FallsTo.weaken hcomp
        (fun r hr => by simp_all [x64ScratchAndAbi]) (fun _ hv => nomatch hv) (by decide)

private theorem emitConvSext0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (m n : Width)
    {va : Val (ty0ToTy (widthTy0 m))} {P : Tup Val [ty0ToTy (widthTy0 n)] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs : s.regs.get64 .rdi = toCanon64 (widthTy0 m) va)
    (hwp : OpCode.wp (op0ToOpCode (.conv .sext m n)) (va, ()) P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitConvSext0 m n [])))
      x64ScratchAndAbi [] maskNone s
      (fun s' => ∃ rv : Val (ty0ToTy (widthTy0 n)), P (rv, ()) ∧
        s'.regs.get64 .rax = toCanon64 (widthTy0 n) rv ∧ s'.dmem = s.dmem) post := by
  cases m <;> cases n <;>
    dsimp only [ty0ToTy, widthTy0, Val, op0ToOpCode, OpCode.wp, castWidth2Op0, toCanon64] at * <;>
    obtain ⟨hmn, hwp'⟩ := hwp <;>
    exact Machine.FallsTo.conseq
      (emitConvSext0_bits _ _ hmn (va := va)
        (by rw [hs]; try exact (BitVec.setWidth_eq va).symm))
      fun _ ⟨hr, hm⟩ _ =>
        ⟨_, hwp', by rw [hr]; try exact BitVec.setWidth_eq _, hm⟩

private def divExt32_0 (w : Width) (isSigned : Bool) (v : BitVec w.bits) : BitVec 32 :=
  if isSigned then v.signExtend 32 else v.setWidth 32

private theorem divExt32_props0 (w : Width) (hw : w = .W8 ∨ w = .W16 ∨ w = .W32)
    (isSigned isRem : Bool) (va vb : BitVec w.bits)
    (hdef : if isSigned then sdivDefined va vb = true else vb ≠ 0#w.bits) :
    (if isSigned then sdivDefined (divExt32_0 w isSigned va) (divExt32_0 w isSigned vb) = true
     else divExt32_0 w isSigned vb ≠ 0#32) ∧
    (if isSigned then
      if isRem then (divExt32_0 w isSigned va).srem (divExt32_0 w isSigned vb)
      else (divExt32_0 w isSigned va).sdiv (divExt32_0 w isSigned vb)
     else
      if isRem then divExt32_0 w isSigned va % divExt32_0 w isSigned vb
      else divExt32_0 w isSigned va / divExt32_0 w isSigned vb).setWidth w.bits =
      if isSigned then (if isRem then va.srem vb else va.sdiv vb)
      else (if isRem then va % vb else va / vb) := by
  have sub32 (hw816 : w = .W8 ∨ w = .W16) :
      (if isSigned then sdivDefined (divExt32_0 w isSigned va) (divExt32_0 w isSigned vb) = true
       else divExt32_0 w isSigned vb ≠ 0#32) ∧
      (if isSigned then
        if isRem then (divExt32_0 w isSigned va).srem (divExt32_0 w isSigned vb)
        else (divExt32_0 w isSigned va).sdiv (divExt32_0 w isSigned vb)
       else
        if isRem then divExt32_0 w isSigned va % divExt32_0 w isSigned vb
        else divExt32_0 w isSigned va / divExt32_0 w isSigned vb).setWidth w.bits =
        if isSigned then (if isRem then va.srem vb else va.sdiv vb)
        else (if isRem then va % vb else va / vb) := by
    have hwle : w.bits ≤ 32 := by rcases hw816 with rfl | rfl <;> decide
    have hpow : 2 ^ w.bits < 2 ^ 32 := by rcases hw816 with rfl | rfl <;> decide
    have ha := Nat.lt_trans va.isLt hpow; have hb := Nat.lt_trans vb.isLt hpow
    cases isSigned
    · refine ⟨fun h => hdef (BitVec.eq_of_toNat_eq (by
        have h1 := congrArg BitVec.toNat h
        simp only [divExt32_0, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_setWidth,
          BitVec.toNat_zero] at h1
        rwa [Nat.mod_eq_of_lt hb] at h1)), ?_⟩
      have hva32 : va.toNat % 2 ^ 32 = va.toNat := Nat.mod_eq_of_lt ha
      have hvb32 : vb.toNat % 2 ^ 32 = vb.toNat := Nat.mod_eq_of_lt hb
      cases isRem <;> dsimp only [divExt32_0] <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        apply BitVec.eq_of_toNat_eq
      · simp only [BitVec.toNat_setWidth, BitVec.udiv_def, BitVec.toNat_ofNat, hva32, hvb32]
        rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) va.isLt) hpow),
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) va.isLt)]
      · have hrem_lt : va.toNat % vb.toNat < 2 ^ w.bits :=
          Nat.lt_trans (Nat.mod_lt _
            (Nat.pos_of_ne_zero fun h => hdef (BitVec.eq_of_toNat_eq (by simpa using h)))) vb.isLt
        simp only [BitVec.toNat_setWidth, BitVec.umod_def, BitVec.toNat_ofNat, hva32, hvb32]
        rw [Nat.mod_eq_of_lt (Nat.lt_trans hrem_lt hpow), Nat.mod_eq_of_lt hrem_lt]
    · simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true',
        Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hdef
      refine ⟨?_, ?_⟩
      · simp only [divExt32_0, ↓reduceIte, sdivDefined, Bool.and_eq_true, bne_iff_ne,
          Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        refine ⟨fun h => hdef.1 (BitVec.toInt_inj.1 (by
          have := congrArg BitVec.toInt h
          rw [BitVec.toInt_signExtend_of_le hwle] at this; simpa using this)), Or.inl fun h1 => ?_⟩
        have h2 := congrArg BitVec.toInt h1
        rw [BitVec.toInt_signExtend_of_le hwle,
          show (BitVec.intMin 32).toInt = -2 ^ 31 by decide] at h2
        have ha2 := BitVec.le_toInt va
        rcases hw816 with rfl | rfl <;> dsimp only [Width.bits] at ha2 <;> omega
      · cases isRem <;> dsimp only [divExt32_0] <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · have h1 := BitVec.eq_of_toInt_eq
            ((BitVec.toInt_ofInt _).trans
              (BitVec.toInt_sdiv (va.signExtend 32) (vb.signExtend 32)).symm)
          rw [← h1, BitVec.toInt_signExtend_of_le hwle, BitVec.toInt_signExtend_of_le hwle,
            setWidth_ofInt_le hwle]
          exact BitVec.eq_of_toInt_eq ((BitVec.toInt_ofInt _).trans (BitVec.toInt_sdiv va vb).symm)
        · have h1 : (va.signExtend 32).srem (vb.signExtend 32) =
              BitVec.ofInt 32 ((va.signExtend 32).toInt.tmod (vb.signExtend 32).toInt) := by
            rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]
          rw [h1, BitVec.toInt_signExtend_of_le hwle, BitVec.toInt_signExtend_of_le hwle,
            setWidth_ofInt_le hwle, ← BitVec.toInt_srem, BitVec.ofInt_toInt]
  rcases hw with rfl | rfl | rfl
  · exact sub32 (.inl rfl)
  · exact sub32 (.inr rfl)
  · cases isSigned <;> refine ⟨by simpa [divExt32_0] using hdef,
      by cases isRem <;> simp [divExt32_0, BitVec.setWidth_eq]⟩

private theorem sshiftRight_last0 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.sshiftRight (w - 1) = if x.msb then BitVec.allOnes w else 0#w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  cases hi2 : decide (w - 1 + i < w)
  · have hge : ¬ (w - 1 + i < w) := by simp only [decide_eq_false_iff_not] at hi2; exact hi2
    cases x.msb <;> simp [hge, hi]
  · have hi0 : i = 0 := by simp only [decide_eq_true_eq] at hi2; omega
    subst hi0
    simp only [Nat.add_zero, show w - 1 < w by omega, ↓reduceIte, ← BitVec.msb_eq_getLsbD_last x]
    cases x.msb <;> simp [hi, show ¬ (w ≤ 0) by omega]

private theorem wp_divCore0 [Host] {E : Int64 → MachineData → Prop} (symName : Sym0 → Sym)
    (w : Width) (hw : w = .W32 ∨ w = .W64) (isSigned isRem : Bool) (rhs : Reg64) (hrhs : rhs ≠ .rdx)
    (s : MachineData) (va vb : BitVec w.bits)
    (hrax : (s.regs.get64 .rax).setWidth w.bits = va)
    (hrhs_val : (s.regs.get64 rhs).setWidth w.bits = vb)
    (hdef : if isSigned then sdivDefined va vb = true else vb ≠ 0#w.bits) :
    _root_.Program.wp (dir0ToAmd64 symName (.divCore w isSigned rhs)) (fun s' =>
      ∃ rax' rdx' status',
        (if isRem then rdx' else rax').setWidth w.bits =
          (if isSigned then (if isRem then va.srem vb else va.sdiv vb)
           else (if isRem then va % vb else va / vb)) ∧
        (w = .W32 → (if isRem then rdx' else rax') =
          (if isSigned then (if isRem then va.srem vb else va.sdiv vb)
           else (if isRem then va % vb else va / vb)).setWidth 64) ∧
        s' =
          { s with regs := (s.regs.set64 .rax rax').set64 .rdx rdx', status := status' }) E s := by
  have falls_core : ∀ (rdxVal : BitVec 64),
      rdxVal = (if isSigned then (if va.msb then BitVec.allOnes w.bits else 0#w.bits).setWidth 64
                else 0#64) →
      Directive.FallsTo (insW w (if isSigned then .idiv (.reg (regW w rhs))
          else .div (.reg (regW w rhs))))
        { s with regs := s.regs.set64 .rdx rdxVal }
        (fun s' => ∃ rax' rdx' status',
          rax'.setWidth w.bits = (if isSigned then va.sdiv vb else va / vb) ∧
          rdx'.setWidth w.bits = (if isSigned then va.srem vb else va % vb) ∧
          (w = .W32 → rax' = (if isSigned then va.sdiv vb else va / vb).setWidth 64 ∧
            rdx' = (if isSigned then va.srem vb else va % vb).setWidth 64) ∧
          s' = { s with regs := (s.regs.set64 .rax rax').set64 .rdx rdx', status := status' }) := by
    rintro rdxVal hrdxVal _ _ _ _ _ hk
    subst hrdxVal
    cases isSigned
    · have hrhs1 : ((s.regs.set64 .rdx 0#64).get64 rhs).setWidth w.bits = vb := by
        rw [Reg64s.get64_set64_of_ne _ .rdx rhs _ hrhs.symm, hrhs_val]
      have hrax1 : ((s.regs.set64 .rdx 0#64).get64 .rax).setWidth w.bits = va := by
        rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide), hrax]
      have hlo : (0#w.bits ++ va).toNat = va.toNat := by simp
      have hq_ok : BitVec.ofNat w.bits (va.toNat / vb.toNat) = va / vb :=
        BitVec.eq_of_toNat_eq (by simp [BitVec.udiv_def])
      have hr_ok : BitVec.ofNat w.bits (va.toNat % vb.toNat) = va % vb :=
        BitVec.eq_of_toNat_eq (by simp [BitVec.umod_def])
      have hbnz : (vb == 0) = false := beq_eq_false_iff_ne.2 hdef
      have hqlt : ¬ (2 ^ w.bits ≤ va.toNat / vb.toNat) :=
        Nat.not_le.2 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) va.isLt)
      rcases hw with rfl | rfl
      · dsimp only [Width.bits] at hrhs1 hrax1
        simp only [insW, regW, Width.bits, t_step_simp, show (Width.W32 == .W8) = false by decide,
          Bool.false_eq_true, ↓reduceIte, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_zero,
          Reg64s.get64_set64_same, hrhs1, hrax1, hbnz, hlo, hqlt, Effects.All]
        intro st
        refine hk _ ⟨(BitVec.ofNat 32 (va.toNat / vb.toNat)).setWidth 64,
          (BitVec.ofNat 32 (va.toNat % vb.toNat)).setWidth 64, st,
          by simp [hq_ok, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)],
          by simp [hr_ok, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)],
          fun _ => ⟨by simp [hq_ok], by simp [hr_ok]⟩, ?_⟩
        simp only [Reg64s.set64_set64_comm _ .rdx .rax _ _ (by decide), Reg64s.set64_set64_same]
      · dsimp only [Width.bits] at hrhs1 hrax1
        simp only [BitVec.setWidth_eq] at hrhs1 hrax1
        simp only [insW, regW, Width.bits, t_step_simp, show (Width.W64 == .W8) = false by decide,
          Bool.false_eq_true, ↓reduceIte, Reg64s.get64_set64_same, hrhs1, hrax1, hbnz, hlo, hqlt,
          Effects.All]
        intro st
        refine hk _ ⟨BitVec.ofNat 64 (va.toNat / vb.toNat),
          BitVec.ofNat 64 (va.toNat % vb.toNat), st, by simp [hq_ok], by simp [hr_ok],
          (fun h => by cases h), ?_⟩
        simp only [Reg64s.set64_set64_comm _ .rdx .rax _ _ (by decide), Reg64s.set64_set64_same]
    · have hrhs1 : ((s.regs.set64 .rdx ((if va.msb then BitVec.allOnes w.bits
          else 0#w.bits).setWidth 64)).get64 rhs).setWidth w.bits = vb := by
        rw [Reg64s.get64_set64_of_ne _ .rdx rhs _ hrhs.symm, hrhs_val]
      have hrax1 : ((s.regs.set64 .rdx ((if va.msb then BitVec.allOnes w.bits
          else 0#w.bits).setWidth 64)).get64 .rax).setWidth w.bits = va := by
        rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide), hrax]
      have hwpos : 0 < w.bits := width_bits_pos w
      obtain ⟨hb0, ⟨hq_ge, hq_lt⟩, _⟩ :=
        sdiv_bounds (by rcases hw with rfl | rfl <;> decide) va vb hdef
      have hn_eq :
          (((if va.msb then BitVec.allOnes w.bits else 0#w.bits).setWidth 64).setWidth w.bits ++
          va).toInt = va.toInt := by
        rw [setWidth_64_setWidth, ← sshiftRight_last0 hwpos va]
        exact concat_sshiftRight_toInt hwpos va
      have hq_ok : BitVec.ofInt w.bits (va.toInt.tdiv vb.toInt) = va.sdiv vb :=
        BitVec.eq_of_toInt_eq ((BitVec.toInt_ofInt _).trans (BitVec.toInt_sdiv _ _).symm)
      have hr_ok : BitVec.ofInt w.bits (va.toInt.tmod vb.toInt) = va.srem vb := by
        rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]
      have hguard : (vb == 0 || decide (va.toInt.tdiv vb.toInt < -2 ^ (w.bits - 1)) ||
          decide (2 ^ (w.bits - 1) ≤ va.toInt.tdiv vb.toInt)) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not, Int.not_lt,
          Int.not_le]; exact ⟨⟨hb0, hq_ge⟩, hq_lt⟩
      rcases hw with rfl | rfl
      · dsimp only [Width.bits] at hrhs1 hrax1 hn_eq hguard
        simp only [insW, regW, Width.bits, t_step_simp, ↓reduceIte,
          show (Width.W32 == .W8) = false by decide, Bool.false_eq_true,
          BitVec.zeroExtend_eq_setWidth, Reg64s.get64_set64_same, hrhs1, hrax1, hn_eq, hguard,
          Effects.All]
        intro st
        refine hk _ ⟨(BitVec.ofInt 32 (va.toInt.tdiv vb.toInt)).setWidth 64,
          (BitVec.ofInt 32 (va.toInt.tmod vb.toInt)).setWidth 64, st,
          by simp [hq_ok, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)],
          by simp [hr_ok, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)],
          fun _ => ⟨by simp [hq_ok], by simp [hr_ok]⟩, ?_⟩
        simp only [Reg64s.set64_set64_comm _ .rdx .rax _ _ (by decide), Reg64s.set64_set64_same]
      · dsimp only [Width.bits] at hrhs1 hrax1 hn_eq hguard
        simp only [BitVec.setWidth_eq] at hrhs1 hrax1 hn_eq
        simp only [insW, regW, Width.bits, t_step_simp, ↓reduceIte,
          show (Width.W64 == .W8) = false by decide, Bool.false_eq_true, BitVec.setWidth_eq,
          Reg64s.get64_set64_same, hrhs1, hrax1, hn_eq, hguard, Effects.All]
        intro st
        refine hk _ ⟨BitVec.ofInt 64 (va.toInt.tdiv vb.toInt),
          BitVec.ofInt 64 (va.toInt.tmod vb.toInt), st, by simp [hq_ok], by simp [hr_ok],
          (fun h => by cases h), ?_⟩
        simp only [Reg64s.set64_set64_comm _ .rdx .rax _ _ (by decide), Reg64s.set64_set64_same]
  have falls_sar : ∀ (s1 : MachineData),
      (s1.regs.get64 .rax).setWidth w.bits = va →
      s1.regs.get64 .rdx = (if w = .W64 then s1.regs.get64 .rax
        else (((s1.regs.get64 .rax).setWidth 32).setWidth 64)) →
      Directive.FallsTo (insW w (.sar (.reg (regW w .rdx))
          (.imm8 (.int64 (Int64.ofNat (w.bits - 1)))))) s1
        (fun s' => ∃ st',
          s' =
            { s1 with
              regs := s1.regs.set64 .rdx
                ((if va.msb then BitVec.allOnes w.bits else 0#w.bits).setWidth 64),
              status := st' }) := by
    intro s1 hra1 hrdx1 _ _ _ _ _ hk
    have hbit := sshiftRight_last0 (width_bits_pos w) va
    rcases hw with rfl | rfl
    · dsimp only [Width.bits] at hbit
      simp only [show (Width.W32 = .W64) ↔ False by decide, ↓reduceIte] at hrdx1
      have h32 : (va.setWidth 64).setWidth 32 = va := setWidth_64_setWidth .W32 va
      simp only [insW, regW, Width.bits, t_step_simp, hrdx1, BitVec.zeroExtend_eq_setWidth, h32,
        hra1, show (((Int64.ofNat 31).toBitVec.take 8).toNat &&& 31) = 31 by decide,
        show (31 == 0) = false by decide, show (31 == 1) = false by decide,
        Bool.false_eq_true, ↓reduceIte, Effects.All, Reg64s.set]
      intro _ _; rw [hbit]; exact hk _ ⟨_, rfl⟩
    · dsimp only [Width.bits] at hbit hra1
      simp only [BitVec.setWidth_eq] at hra1
      simp only [↓reduceIte] at hrdx1
      simp only [insW, regW, Width.bits, t_step_simp, hrdx1, hra1,
        show (((Int64.ofNat 63).toBitVec.take 8).toNat &&& 63) = 63 by decide,
        show (63 == 0) = false by decide, show (63 == 1) = false by decide,
        Bool.false_eq_true, ↓reduceIte, Effects.All, Reg64s.set]
      intro _ _
      have h64 : (if va.msb then BitVec.allOnes Width.W64.bits else 0#Width.W64.bits).setWidth 64 =
          if va.msb then BitVec.allOnes 64 else 0#64 := by
        dsimp only [Width.bits]; rw [BitVec.setWidth_eq]
      rw [h64] at hk
      rw [hbit]
      exact hk _ ⟨_, rfl⟩
  cases isSigned <;> rcases hw with rfl | rfl
  · dsimp only [dir0ToAmd64]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .rdx 0)) ?_
    rintro _ rfl
    refine Program.wp.mono (Directive.FallsTo.wp (falls_core 0#64 rfl)) ?_
    rintro _ ⟨a', d', st', ha, hd, hz, rfl⟩
    exact ⟨a', d', st', by cases isRem <;> first | exact hd | exact ha,
      fun h => by cases isRem <;> first | exact (hz h).2 | exact (hz h).1, rfl⟩
  · dsimp only [dir0ToAmd64]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .rdx 0)) ?_
    rintro _ rfl
    refine Program.wp.mono (Directive.FallsTo.wp (falls_core 0#64 rfl)) ?_
    rintro _ ⟨a', d', st', ha, hd, _, rfl⟩
    exact ⟨a', d', st', by cases isRem <;> first | exact hd | exact ha,
      (fun h => by cases h), rfl⟩
  · dsimp only [dir0ToAmd64]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movlD s .rdx .rax)) ?_
    rintro _ rfl
    refine Program.wp.cons (Directive.FallsTo.wp (falls_sar _
      (by rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide)]; exact hrax)
      (by rw [Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth]; rfl))) ?_
    rintro s2 ⟨st2, hs2⟩
    have hr_s2 : s2 =
        { s with
          regs := s.regs.set64 .rdx
            ((if va.msb then BitVec.allOnes 32 else 0#32).setWidth 64),
          status := st2 } := by
      rw [hs2, Reg64s.set64_set64_same]
    rw [hr_s2]
    refine Program.wp.mono (Directive.FallsTo.wp (falls_core _ rfl)) ?_
    rintro _ ⟨a', d', st', ha, hd, hz, rfl⟩
    exact ⟨a', d', st', by cases isRem <;> first | exact hd | exact ha,
      fun h => by cases isRem <;> first | exact (hz h).2 | exact (hz h).1, rfl⟩
  · dsimp only [dir0ToAmd64]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD s .rdx .rax)) ?_
    rintro _ rfl
    refine Program.wp.cons (Directive.FallsTo.wp (falls_sar _
      (by rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide)]; exact hrax)
      (by rw [Reg64s.get64_set64_same]; rfl))) ?_
    rintro s2 ⟨st2, hs2⟩
    have hr_s2 : s2 =
        { s with
          regs := s.regs.set64 .rdx
            ((if va.msb then BitVec.allOnes 64 else 0#64).setWidth 64),
          status := st2 } := by
      rw [hs2, Reg64s.set64_set64_same]
    rw [hr_s2]
    refine Program.wp.mono (Directive.FallsTo.wp (falls_core _ rfl)) ?_
    rintro _ ⟨a', d', st', ha, hd, _, rfl⟩
    exact ⟨a', d', st', by cases isRem <;> first | exact hd | exact ha,
      (fun h => by cases h), rfl⟩

private theorem emitDiv0_bits {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (op : DivOp0) (w : Width) {va vb : BitVec w.bits} {P : BitVec w.bits → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs1 : s.regs.get64 .rdi = va.setWidth 64)
    (hs2 : s.regs.get64 .rsi = vb.setWidth 64)
    (hdef_ok : if (match op with | .sdiv | .srem => true | _ => false)
        then sdivDefined va vb = true else vb ≠ 0#w.bits)
    (hp_ok : P (if (match op with | .sdiv | .srem => true | _ => false)
        then (if (match op with | .urem | .srem => true | _ => false)
              then va.srem vb else va.sdiv vb)
        else (if (match op with | .urem | .srem => true | _ => false)
              then va % vb else va / vb))) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitDiv0 op w []))) x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : BitVec w.bits, P rv ∧
        s'.regs.get64 .rax = rv.setWidth 64 ∧ s'.dmem = s.dmem) post := by
  let isS := match op with | .sdiv | .srem => true | _ => false
  let isR := match op with | .urem | .srem => true | _ => false
  have hd_ok : if isS then sdivDefined va vb = true else vb ≠ 0#w.bits := hdef_ok
  let resVal : BitVec w.bits :=
    if isS then (if isR then va.srem vb else va.sdiv vb)
    else (if isR then va % vb else va / vb)
  have hp_res : P resVal := hp_ok
  have fin_tail : ∀ [Host] (bR : Bool) (cw : Width) (s3 : MachineData) (rax' rdx' : BitVec 64)
      (st' : StatusFlags),
      cw = .W32 ∨ cw = .W64 → w.bits ≤ cw.bits → (w = .W32 → cw = .W32) →
      (if bR then rdx' else rax').setWidth w.bits = resVal →
      (w = .W32 → (if bR then rdx' else rax') = resVal.setWidth 64) →
      s3.dmem = s.dmem →
      _root_.Program.wp (toAmd64Program symName (emitFwd0
          (if bR then pushDRR0 0 cw .rax .rdx [] else [])))
        (fun s4 => GprHolds (s4.regs.get64 .rax) (.bits w.bits) resVal ∧
          (w = .W32 → s4.regs.get64 .rax = resVal.setWidth 64) ∧ s4.dmem = s.dmem ∧
          ∀ r, r ∉ x64ScratchAndAbi → s4.regs.get64 r = s3.regs.get64 r)
        (fun _ _ => False)
        { s3 with regs := (s3.regs.set64 .rax rax').set64 .rdx rdx', status := st' } := by
    intro _ bR cw s3 rax' rdx' st' hcw hw_le hw_cw hr_res hz32 hm3
    cases bR
    · refine _root_.Program.wp_nil ⟨(GprHolds.bits_iff w _ _).2 ?_, ?_, hm3, fun r hr => ?_⟩
      · rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide), Reg64s.get64_set64_same]
        exact hr_res
      · intro hw32
        rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide), Reg64s.get64_set64_same]
        exact hz32 hw32
      · simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ .rdx r _ (Ne.symm hr.2.2.1),
          Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]
    · have hmv : Directive.FallsTo (insW cw (.mov (.reg (regW cw .rax)) (.reg (regW cw .rdx))))
          { s3 with regs := (s3.regs.set64 .rax rax').set64 .rdx rdx', status := st' }
          (fun s4 => s4 =
            { s3 with
              regs := ((s3.regs.set64 .rax rax').set64 .rdx rdx').set64 .rax
                ((rdx'.setWidth cw.bits).setWidth 64),
              status := st' }) := by
        intro _
        let stBase : MachineData :=
          { s3 with regs := (s3.regs.set64 .rax rax').set64 .rdx rdx', status := st' }
        rcases hcw with rfl | rfl
        · have hmv0 := fallsTo_movlD stBase .rax .rdx
          dsimp only [stBase] at hmv0
          rw [Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth] at hmv0
          dsimp only [Width.bits, insW, regW]
          dsimp only [movlD, movlI] at hmv0
          exact hmv0
        · have hmv0 := fallsTo_movD stBase .rax .rdx
          dsimp only [stBase] at hmv0
          rw [Reg64s.get64_set64_same] at hmv0
          dsimp only [Width.bits, insW, regW]
          rw [BitVec.setWidth_eq, BitVec.setWidth_eq]
          dsimp only [movD, movI] at hmv0
          exact hmv0
      rcases hcw with rfl | rfl
      · dsimp only [↓reduceIte, List.append_nil, pushDRR0, emitFwd0, List.reverse_cons,
          List.reverse_nil, List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil,
          dir0ToAmd64]
        refine Program.wp.mono (Directive.FallsTo.wp hmv) ?_
        rintro _ rfl
        refine ⟨(GprHolds.bits_iff w _ _).2 ?_, ?_, hm3, fun r hr => ?_⟩
        · dsimp only [Width.bits] at *
          rw [Reg64s.get64_set64_same,
            BitVec.setWidth_setWidth_of_le (rdx'.setWidth 32) (width_bits_le_64 w),
            BitVec.setWidth_setWidth_of_le rdx' hw_le]
          exact hr_res
        · intro hw32; subst hw32; dsimp only [Width.bits] at hr_res ⊢
          simp only [↓reduceIte] at hr_res
          rw [Reg64s.get64_set64_same, hr_res]
        · simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
          rw [Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
            Reg64s.get64_set64_of_ne _ .rdx r _ (Ne.symm hr.2.2.1),
            Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]
      · dsimp only [↓reduceIte, List.append_nil, pushDRR0, emitFwd0, List.reverse_cons,
          List.reverse_nil, List.nil_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil,
          dir0ToAmd64]
        refine Program.wp.mono (Directive.FallsTo.wp hmv) ?_
        rintro _ rfl
        refine ⟨(GprHolds.bits_iff w _ _).2 ?_, fun hw32 => absurd (hw_cw hw32) (by decide),
          hm3, fun r hr => ?_⟩
        · dsimp only [Width.bits] at *
          rw [Reg64s.get64_set64_same,
            BitVec.setWidth_setWidth_of_le (rdx'.setWidth 64) (width_bits_le_64 w),
            BitVec.setWidth_setWidth_of_le rdx' (width_bits_le_64 w)]
          exact hr_res
        · simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
          rw [Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
            Reg64s.get64_set64_of_ne _ .rdx r _ (Ne.symm hr.2.2.1),
            Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]
  have hwc : w = .W64 ∨ w = .W32 ∨ (w = .W8 ∨ w = .W16) := by
    cases w <;> simp
  rcases hwc with rfl | rfl | hw816
  · dsimp only [emitDiv0]
    change x64ScalarMach.FallsTo x64CondReads h k (toAmd64Program symName (emitFwd0
      (if isR then pushDRR0 0 .W64 .rax .rdx
        (pushDUnary0 (if isS then 3 else 2) .W64 .rax .rsi (pushDRR0 0 .W64 .rax .rdi []))
       else pushDUnary0 (if isS then 3 else 2) .W64 .rax .rsi (pushDRR0 0 .W64 .rax .rdi []))))
      x64ScratchAndAbi [] maskAll s _ post
    have hsplit : (if isR then pushDRR0 0 .W64 .rax .rdx
        (pushDUnary0 (if isS then 3 else 2) .W64 .rax .rsi (pushDRR0 0 .W64 .rax .rdi []))
       else pushDUnary0 (if isS then 3 else 2) .W64 .rax .rsi (pushDRR0 0 .W64 .rax .rdi [])) =
        (if isR then pushDRR0 0 .W64 .rax .rdx [] else []) ++
          ((if isS then [.divCore .W64 true .rsi] else [.divCore .W64 false .rsi]) ++
            [.movRR .W64 .rax .rdi]) := by
      cases op <;> rfl
    rw [hsplit, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
    apply scalar_fallsTo_of_wp; intro _ E
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD s .rax .rdi)) ?_
    rintro _ rfl
    have hcore := wp_divCore0 (E := E) symName .W64 (.inr rfl) isS isR .rsi (by decide)
      { s with regs := s.regs.set64 .rax (s.regs.get64 .rdi) } va vb
      (by rw [Reg64s.get64_set64_same, hs1]; simp [Width.bits])
      (by rw [Reg64s.get64_set64_of_ne _ .rax .rsi _ (by decide), hs2]; simp [Width.bits]) hd_ok
    have hprog_eq : toAmd64Program symName (emitFwd0
        (if isS then [.divCore .W64 true .rsi] else [.divCore .W64 false .rsi])) =
        dir0ToAmd64 symName (.divCore .W64 isS .rsi) := by
      cases isS <;> rfl
    rw [hprog_eq]
    refine Program.wp.append hcore ?_
    rintro _ ⟨rax', rdx', st', hr_res, _, rfl⟩
    refine Program.wp.mono (Program.wp_mono (fun _ h => h) (fun _ _ => False.elim)
      (fin_tail isR .W64 { s with regs := s.regs.set64 .rax (s.regs.get64 .rdi) }
        rax' rdx' st' (.inr rfl) (Nat.le_refl 64) (fun h => by cases h)
        hr_res (fun h => by cases h) rfl)) ?_
    rintro s4 ⟨hgh, _, hm4, hfr4⟩
    have hcan : s4.regs.get64 .rax = resVal.setWidth 64 := by
      simpa [Width.bits, GprHolds] using hgh
    refine ⟨⟨resVal, hp_res, hcan, hm4⟩, scalarFrame_of_eq (fun r hr => ?_)
      (scalarUpdFlags_maskAll _ _)⟩
    have hnot_rax : r ≠ .rax := fun e => hr (e ▸ List.mem_cons_self)
    rw [hfr4 r hr, Reg64s.get64_set64_of_ne _ .rax r _ hnot_rax.symm]
  · dsimp only [emitDiv0]
    change x64ScalarMach.FallsTo x64CondReads h k (toAmd64Program symName (emitFwd0
      (if isR then pushDRR0 0 .W32 .rax .rdx
        (pushDUnary0 (if isS then 3 else 2) .W32 .rax .r11
          (pushDRR0 0 .W32 .r11 .rsi (pushDRR0 0 .W32 .rax .rdi [])))
       else pushDUnary0 (if isS then 3 else 2) .W32 .rax .r11
          (pushDRR0 0 .W32 .r11 .rsi (pushDRR0 0 .W32 .rax .rdi [])))))
      x64ScratchAndAbi [] maskAll s _ post
    have hsplit : (if isR then pushDRR0 0 .W32 .rax .rdx
        (pushDUnary0 (if isS then 3 else 2) .W32 .rax .r11
          (pushDRR0 0 .W32 .r11 .rsi (pushDRR0 0 .W32 .rax .rdi [])))
       else pushDUnary0 (if isS then 3 else 2) .W32 .rax .r11
          (pushDRR0 0 .W32 .r11 .rsi (pushDRR0 0 .W32 .rax .rdi []))) =
        (if isR then pushDRR0 0 .W32 .rax .rdx [] else []) ++
          ((if isS then [.divCore .W32 true .r11] else [.divCore .W32 false .r11]) ++
            [.movRR .W32 .r11 .rsi, .movRR .W32 .rax .rdi]) := by
      cases op <;> rfl
    rw [hsplit, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
    apply scalar_fallsTo_of_wp; intro _ E
    let s1 : MachineData :=
      { s with regs := s.regs.set64 .rax (((s.regs.get64 .rdi).zeroExtend 32).setWidth 64) }
    let s2 : MachineData :=
      { s1 with regs := s1.regs.set64 .r11 (((s1.regs.get64 .rsi).zeroExtend 32).setWidth 64) }
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movlD s .rax .rdi)) ?_
    rintro _ rfl
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movlD s1 .r11 .rsi)) ?_
    rintro _ rfl
    have hcore := wp_divCore0 (E := E) symName .W32 (.inl rfl) isS isR .r11 (by decide) s2 va vb
      (by dsimp only [s2, s1]
          rw [Reg64s.get64_set64_of_ne _ .r11 .rax _ (by decide), Reg64s.get64_set64_same,
            BitVec.zeroExtend_eq_setWidth, setWidth_64_setWidth .W32, hs1,
            setWidth_64_setWidth .W32])
      (by dsimp only [s2, s1]
          rw [Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth, setWidth_64_setWidth .W32,
            Reg64s.get64_set64_of_ne _ .rax .rsi _ (by decide), hs2,
            setWidth_64_setWidth .W32])
      hd_ok
    have hprog_eq : toAmd64Program symName (emitFwd0
        (if isS then [.divCore .W32 true .r11] else [.divCore .W32 false .r11])) =
        dir0ToAmd64 symName (.divCore .W32 isS .r11) := by
      cases isS <;> rfl
    rw [hprog_eq]
    refine Program.wp.append hcore ?_
    rintro _ ⟨rax', rdx', st', hr_res, hz, rfl⟩
    refine Program.wp.mono (Program.wp_mono (fun _ h => h) (fun _ _ => False.elim)
      (fin_tail isR .W32 s2 rax' rdx' st' (.inl rfl) (Nat.le_refl 32) (fun _ => rfl)
        hr_res (fun _ => hz rfl) rfl)) ?_
    rintro s4 ⟨_, h32, hm4, hfr4⟩
    refine ⟨⟨resVal, hp_res, h32 rfl, hm4⟩, scalarFrame_of_eq (fun r hr => ?_)
      (scalarUpdFlags_maskAll _ _)⟩
    simp only [x64ScratchAndAbi, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    rw [hfr4 r (by simp [x64ScratchAndAbi]; exact hr),
      Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.2.2.2.2.2.2),
      Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]
  · obtain ⟨hdef32, hres32⟩ := divExt32_props0 w (hw816.imp_right .inl) isS isR va vb hd_ok
    have hwle64 : w.bits ≤ 64 := width_bits_le_64 w
    have hwle32 : w.bits ≤ 32 := by rcases hw816 with rfl | rfl <;> decide
    have hzx_fn : ∀ {k0 : Nat} (rd rs : Reg64) (st0 : MachineData),
        x64ScalarMach.FallsTo x64CondReads h k0
          (toAmd64Program symName (emitFwd0 (pushDRR0 1 w rd rs [])))
          [rd] [] maskNone st0
          (fun s1 => s1.regs.get64 rd = ((st0.regs.get64 rs).setWidth w.bits).setWidth 64 ∧
            s1.dmem = st0.dmem) post := by
      intro _ rd rs st0
      rcases hw816 with rfl | rfl
      · exact scalar_movzx8_fallsTo rd rs st0
      · exact scalar_movzx16_fallsTo rd rs st0
    have hprep : x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0
          (if isS then pushDMovsx0 .W32 .r11 w .rsi (pushDMovsx0 .W32 .rax w .rdi [])
           else pushDRR0 1 w .r11 .rsi (pushDRR0 1 w .rax .rdi []))))
        [.rax, .r11] [] maskNone s
        (fun s2 => (s2.regs.get64 .rax).setWidth 32 = divExt32_0 w isS va ∧
          (s2.regs.get64 .r11).setWidth 32 = divExt32_0 w isS vb ∧ s2.dmem = s.dmem) post := by
      cases isS
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have h12 : pushDRR0 1 w .r11 .rsi (pushDRR0 1 w .rax .rdi []) =
            pushDRR0 1 w .r11 .rsi [] ++ pushDRR0 1 w .rax .rdi [] := rfl
        rw [h12, emitFwd0_append, toAmd64Program_append]
        have hstep1 : x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (pushDRR0 1 w .rax .rdi [])))
            [.rax] [] maskNone s
            (fun s1 => (s1.regs.get64 .rax).setWidth 32 = divExt32_0 w false va ∧
              s1.regs.get64 .rsi = s.regs.get64 .rsi ∧ s1.dmem = s.dmem) post := by
          refine Machine.FallsTo.conseq (hzx_fn .rax .rdi s) fun s1 ⟨hr1, hm1⟩ hfr => ?_
          refine ⟨?_, hfr.1 .rsi (by simp), hm1⟩
          rw [hr1, hs1, setWidth_64_setWidth w,
            BitVec.setWidth_setWidth_of_le va (by decide : 32 ≤ 64)]
          rcases hw816 with rfl | rfl <;> rfl
        have hcomp : x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (pushDRR0 1 w .rax .rdi [])) ++
              toAmd64Program symName (emitFwd0 (pushDRR0 1 w .r11 .rsi [])))
            ([.rax] ++ [.r11]) ([] ++ []) (maskNone ||| maskNone) s
            (fun s2 => (s2.regs.get64 .rax).setWidth 32 = divExt32_0 w false va ∧
              (s2.regs.get64 .r11).setWidth 32 = divExt32_0 w false vb ∧ s2.dmem = s.dmem)
            post :=
          Machine.FallsTo.comp hstep1 fun s1 ⟨ha1, hrsi1, hm1⟩ _ => by
            refine Machine.FallsTo.conseq (hzx_fn .r11 .rsi s1) fun s2 ⟨hr2, hm2⟩ hfr2 => ?_
            refine ⟨by rw [show s2.regs.get64 .rax = s1.regs.get64 .rax from hfr2.1 .rax (by simp),
              ha1], ?_, hm2.trans hm1⟩
            rw [hr2, hrsi1, hs2, setWidth_64_setWidth w,
              BitVec.setWidth_setWidth_of_le vb (by decide : 32 ≤ 64)]
            rcases hw816 with rfl | rfl <;> rfl
        exact Machine.FallsTo.weaken hcomp
          (fun r hr => by simp_all) (fun _ hv => nomatch hv) (by decide)
      · simp only [↓reduceIte]
        have h12 : pushDMovsx0 .W32 .r11 w .rsi (pushDMovsx0 .W32 .rax w .rdi []) =
            pushDMovsx0 .W32 .r11 w .rsi [] ++ pushDMovsx0 .W32 .rax w .rdi [] := rfl
        rw [h12, emitFwd0_append, toAmd64Program_append]
        have hstep1 : x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (pushDMovsx0 .W32 .rax w .rdi [])))
            [.rax] [] maskNone s
            (fun s1 => (s1.regs.get64 .rax).setWidth 32 = divExt32_0 w true va ∧
              s1.regs.get64 .rsi = s.regs.get64 .rsi ∧ s1.dmem = s.dmem) post := by
          refine Machine.FallsTo.conseq
            (scalar_movsx_fallsTo .W32 (.inl rfl) .rax w .rdi ⟨hwle32, .inr hw816⟩ s)
            fun s1 ⟨hr1, hm1⟩ hfr => ?_
          refine ⟨?_, hfr.1 .rsi (by simp), hm1⟩
          rw [hr1, hs1, setWidth_64_setWidth w,
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
          rcases hw816 with rfl | rfl <;> rfl
        have hcomp : x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (pushDMovsx0 .W32 .rax w .rdi [])) ++
              toAmd64Program symName (emitFwd0 (pushDMovsx0 .W32 .r11 w .rsi [])))
            ([.rax] ++ [.r11]) ([] ++ []) (maskNone ||| maskNone) s
            (fun s2 => (s2.regs.get64 .rax).setWidth 32 = divExt32_0 w true va ∧
              (s2.regs.get64 .r11).setWidth 32 = divExt32_0 w true vb ∧ s2.dmem = s.dmem)
            post :=
          Machine.FallsTo.comp hstep1 fun s1 ⟨ha1, hrsi1, hm1⟩ _ => by
            refine Machine.FallsTo.conseq
              (scalar_movsx_fallsTo .W32 (.inl rfl) .r11 w .rsi ⟨hwle32, .inr hw816⟩ s1)
              fun s2 ⟨hr2, hm2⟩ hfr2 => ?_
            refine ⟨by rw [show s2.regs.get64 .rax = s1.regs.get64 .rax from hfr2.1 .rax (by simp),
              ha1], ?_, hm2.trans hm1⟩
            rw [hr2, hrsi1, hs2, setWidth_64_setWidth w,
              BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
            rcases hw816 with rfl | rfl <;> rfl
        exact Machine.FallsTo.weaken hcomp
          (fun r hr => by simp_all) (fun _ hv => nomatch hv) (by decide)
    have hsplit : emitDiv0 op w [] =
        emitCanon0 w .rax [] ++
          ((if isR then pushDRR0 0 .W32 .rax .rdx [] else []) ++
            ((if isS then [.divCore .W32 true .r11] else [.divCore .W32 false .r11]) ++
              (if isS then pushDMovsx0 .W32 .r11 w .rsi (pushDMovsx0 .W32 .rax w .rdi [])
               else pushDRR0 1 w .r11 .rsi (pushDRR0 1 w .rax .rdi [])))) := by
      rcases hw816 with rfl | rfl <;>
      · dsimp only [emitDiv0]
        change emitCanon0 _ .rax _ = _
        rw [(emitCanon0_acc _ .rax _).1]
        congr 1
        cases op <;> rfl
    dsimp only [isR, isS] at hsplit hprep
    rw [hsplit, emitFwd0_append, emitFwd0_append, emitFwd0_append,
      toAmd64Program_append, toAmd64Program_append, toAmd64Program_append]
    have hmid : ∀ (s2 : MachineData),
        (s2.regs.get64 .rax).setWidth 32 = divExt32_0 w isS va →
        (s2.regs.get64 .r11).setWidth 32 = divExt32_0 w isS vb → s2.dmem = s.dmem →
        x64ScalarMach.FallsTo x64CondReads h
          (k + (toAmd64Program symName (emitFwd0
            (if isS then pushDMovsx0 .W32 .r11 w .rsi (pushDMovsx0 .W32 .rax w .rdi [])
             else pushDRR0 1 w .r11 .rsi (pushDRR0 1 w .rax .rdi [])))).length)
          (toAmd64Program symName (emitFwd0
            (if isS then [.divCore .W32 true .r11] else [.divCore .W32 false .r11])) ++
           toAmd64Program symName (emitFwd0
            (if isR then pushDRR0 0 .W32 .rax .rdx [] else [])))
          x64ScratchAndAbi [] maskAll s2
          (fun s3 =>
            GprHolds (s3.regs.get64 .rax) (.bits w.bits) resVal ∧ s3.dmem = s.dmem) post := by
      intro s2 ha2 hb2 hm2
      apply scalar_fallsTo_of_wp; intro _ E
      have hc := wp_divCore0 (E := E) symName .W32 (.inl rfl) isS isR .r11 (by decide) s2
        (divExt32_0 w isS va) (divExt32_0 w isS vb) ha2 hb2 hdef32
      have hprog_eq : toAmd64Program symName (emitFwd0
          (if isS then [.divCore .W32 true .r11] else [.divCore .W32 false .r11])) =
          dir0ToAmd64 symName (.divCore .W32 isS .r11) := by
        cases isS <;> rfl
      rw [hprog_eq]
      refine Program.wp.append hc ?_
      rintro _ ⟨rax', rdx', st', hr_res, _, rfl⟩
      have hr_w : (if isR then rdx' else rax').setWidth w.bits = resVal := by
        rw [← BitVec.setWidth_setWidth_of_le (if isR then rdx' else rax') hwle32, hr_res]
        exact hres32
      refine Program.wp.mono (Program.wp_mono (fun _ h => h) (fun _ _ => False.elim)
        (fin_tail isR .W32 s2 rax' rdx' st' (.inl rfl) hwle32
          (fun h => by rcases hw816 with rfl | rfl <;> cases h)
          hr_w (fun h => by rcases hw816 with rfl | rfl <;> cases h) hm2)) ?_
      rintro s4 ⟨hgh, _, hm4, hfr4⟩
      exact ⟨⟨hgh, hm4⟩, scalarFrame_of_eq (fun r hr => hfr4 r hr)
        (scalarUpdFlags_maskAll _ _)⟩
    have h12 : x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0
          (if isS then pushDMovsx0 .W32 .r11 w .rsi (pushDMovsx0 .W32 .rax w .rdi [])
           else pushDRR0 1 w .r11 .rsi (pushDRR0 1 w .rax .rdi []))) ++
         (toAmd64Program symName (emitFwd0
            (if isS then [.divCore .W32 true .r11] else [.divCore .W32 false .r11])) ++
           toAmd64Program symName (emitFwd0
            (if isR then pushDRR0 0 .W32 .rax .rdx [] else []))))
        ([.rax, .r11] ++ x64ScratchAndAbi) ([] ++ []) (maskNone ||| maskAll) s
        (fun s3 =>
          GprHolds (s3.regs.get64 .rax) (.bits w.bits) resVal ∧ s3.dmem = s.dmem) post := by
      refine Machine.FallsTo.comp hprep fun s2 ⟨ha2, hb2, hm2⟩ _ => ?_
      dsimp only [isR, isS] at hmid
      exact hmid s2 ha2 hb2 hm2
    have hfull : x64ScalarMach.FallsTo x64CondReads h k
        ((toAmd64Program symName (emitFwd0
            (if isS then pushDMovsx0 .W32 .r11 w .rsi (pushDMovsx0 .W32 .rax w .rdi [])
             else pushDRR0 1 w .r11 .rsi (pushDRR0 1 w .rax .rdi []))) ++
          (toAmd64Program symName (emitFwd0
            (if isS then [.divCore .W32 true .r11] else [.divCore .W32 false .r11])) ++
           toAmd64Program symName (emitFwd0
            (if isR then pushDRR0 0 .W32 .rax .rdx [] else [])))) ++
         toAmd64Program symName (emitFwd0 (emitCanon0 w .rax [])))
        (([.rax, .r11] ++ x64ScratchAndAbi) ++ [.rax]) (([] ++ []) ++ [])
        ((maskNone ||| maskAll) ||| maskNone) s
        (fun s4 => ∃ rv : BitVec w.bits, P rv ∧
          s4.regs.get64 .rax = rv.setWidth 64 ∧ s4.dmem = s.dmem) post :=
      Machine.FallsTo.comp h12 fun s3 ⟨hg3, hm3⟩ _ =>
        Machine.FallsTo.conseq (emitCanon0_spec w .rax)
          fun s4 ⟨ha4, hm4⟩ _ =>
            ⟨resVal, hp_res, ha4.trans (congrArg (BitVec.setWidth 64) hg3.2), hm4.trans hm3⟩
    dsimp only [isR, isS] at hfull
    simp only [List.append_assoc] at hfull ⊢
    exact Machine.FallsTo.weaken hfull (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | h | rfl <;> first | exact h | simp [x64ScratchAndAbi])
      (fun _ hv => nomatch hv) (by decide)

private theorem emitDiv0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (op : DivOp0) (w : Width)
    {va vb : Val (ty0ToTy (widthTy0 w))} {P : Tup Val [ty0ToTy (widthTy0 w)] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hs1 : s.regs.get64 .rdi = toCanon64 (widthTy0 w) va)
    (hs2 : s.regs.get64 .rsi = toCanon64 (widthTy0 w) vb)
    (hwp : OpCode.wp (op0ToOpCode (.div op w)) (va, vb, ()) P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitDiv0 op w []))) x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : Val (ty0ToTy (widthTy0 w)), P (rv, ()) ∧
        s'.regs.get64 .rax = toCanon64 (widthTy0 w) rv ∧ s'.dmem = s.dmem) post := by
  cases w <;> cases op <;>
    dsimp only [ty0ToTy, widthTy0, Val, op0ToOpCode, OpCode.wp, castWidthDiv0, toCanon64,
      Width.bits] at * <;>
    obtain ⟨hd, hp⟩ := hwp <;>
    exact Machine.FallsTo.conseq
      (emitDiv0_bits _ _ (va := va) (vb := vb) (P := fun rv => P (rv, ()))
        (by rw [hs1]; try exact (BitVec.setWidth_eq va).symm)
        (by rw [hs2]; try exact (BitVec.setWidth_eq vb).symm) hd hp)
      fun _ ⟨rv, hrv, hr, hm⟩ _ =>
        ⟨rv, hrv, by rw [hr]; try exact BitVec.setWidth_eq _, hm⟩

/-- Unwrap a single-result `OpCode0` postcondition without dependent type casts. -/
@[expose] def SingleRetPost0 :
    (op : OpCode0) → (Tup Val (ty0ListToTy (op0RetTys op)) → Prop) →
      Val (ty0ToTy (opRetTy0 op)) → Prop
  | .umulw64, _, _ => False
  | .un _ _, P, rv | .bin _ _, P, rv | .cmp _ _, P, rv
  | .select _, P, rv | .conv _ _ _, P, rv | .div _ _, P, rv => P (rv, ())

theorem singleRetPost0_pushTup {op : OpCode0} (hv : ValidOp0 op)
    {vs : List ((t : Ty) × Val t)} {K : List ((t : Ty) × Val t) → Prop}
    {rv : Val (ty0ToTy (opRetTy0 op))}
    (h : SingleRetPost0 op (fun rvs => K (pushTup rvs vs)) rv) :
    K (⟨ty0ToTy (opRetTy0 op), rv⟩ :: vs) := by
  cases op with
  | umulw64 => exact False.elim hv
  | un _ _ | bin _ _ | cmp _ _ | select _ | conv _ _ _ | div _ _ => exact h

theorem emitOp0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat} (op : OpCode0)
    (hv : ValidOp0 op) {argv : Tup Val (ty0ListToTy (op0ArgTys op))}
    {P : Tup Val (ty0ListToTy (op0RetTys op)) → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hin : OpArgsIn0 s op argv) (hwp : OpCode.wp (op0ToOpCode op) argv P) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitOp0 op []))) x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ rv : Val (ty0ToTy (opRetTy0 op)), SingleRetPost0 op P rv ∧
        s'.regs.get64 .rax = toCanon64 (opRetTy0 op) rv ∧ s'.dmem = s.dmem) post := by
  cases op with
  | un u t =>
    rcases argv with ⟨va, ⟨⟩⟩
    have hnu : ¬(u = .neg ∧ t = .bool) := by
      rintro ⟨rfl, rfl⟩; exact hv
    exact emitUn0_spec u t hnu hin hwp
  | bin b t =>
    rcases argv with ⟨va, vb, ⟨⟩⟩
    obtain ⟨hs1, hs2⟩ := hin
    cases b with
    | shl => exact emitBinShift0_spec .shl t (by rintro rfl; exact hv) (.inl rfl) hs1 hs2 hwp
    | lshr =>
      exact emitBinShift0_spec .lshr t (by rintro rfl; exact hv) (.inr (.inl rfl)) hs1 hs2 hwp
    | ashr =>
      exact emitBinShift0_spec .ashr t (by rintro rfl; exact hv)
        (.inr (.inr (.inl rfl))) hs1 hs2 hwp
    | rotl =>
      exact emitBinShift0_spec .rotl t (by rintro rfl; exact hv)
        (.inr (.inr (.inr (.inl rfl)))) hs1 hs2 hwp
    | rotr =>
      exact emitBinShift0_spec .rotr t (by rintro rfl; exact hv)
        (.inr (.inr (.inr (.inr rfl)))) hs1 hs2 hwp
    | add =>
      have hnt : t ≠ .bool := by rintro rfl; exact hv
      exact emitBinAlu0_spec .add t (.inl rfl) (fun ht => absurd ht hnt) hs1 hs2 hwp
    | sub =>
      have hnt : t ≠ .bool := by rintro rfl; exact hv
      exact emitBinAlu0_spec .sub t (.inr (.inl rfl)) (fun ht => absurd ht hnt) hs1 hs2 hwp
    | mul =>
      have hnt : t ≠ .bool := by rintro rfl; exact hv
      exact emitBinAlu0_spec .mul t (.inr (.inr (.inl rfl))) (fun ht => absurd ht hnt) hs1 hs2 hwp
    | and =>
      exact emitBinAlu0_spec .and t (.inr (.inr (.inr (.inl rfl))))
        (fun _ => .inl rfl) hs1 hs2 hwp
    | or =>
      exact emitBinAlu0_spec .or t (.inr (.inr (.inr (.inr (.inl rfl)))))
        (fun _ => .inr (.inl rfl)) hs1 hs2 hwp
    | xor =>
      exact emitBinAlu0_spec .xor t (.inr (.inr (.inr (.inr (.inr rfl)))))
        (fun _ => .inr (.inr rfl)) hs1 hs2 hwp
  | cmp co t =>
    rcases argv with ⟨va, vb, ⟨⟩⟩
    have hnt : t ≠ .bool := by rintro rfl; exact hv
    exact emitCmpSelect0_spec false co t (fun _ => hnt) hin.1 hin.2 hwp
  | select t =>
    rcases argv with ⟨vc, va, vb, ⟨⟩⟩
    exact emitCmpSelect0_spec true .eq t (fun h => by cases h) hin.1 hin.2.1 hin.2.2 hwp
  | conv c m n =>
    cases c with
    | ofBool =>
      rcases argv with ⟨va, ⟨⟩⟩
      exact Machine.FallsTo.weaken (emitConvOfBool0_spec m n hin hwp)
        (fun _ h => h) (fun _ h => h) (by decide)
    | zext =>
      rcases argv with ⟨va, ⟨⟩⟩
      exact Machine.FallsTo.weaken (emitConvZext0_spec m n hin hwp)
        (fun _ h => h) (fun _ h => h) (by decide)
    | trunc =>
      rcases argv with ⟨va, ⟨⟩⟩
      exact Machine.FallsTo.weaken (emitConvTrunc0_spec m n hin hwp)
        (fun _ h => h) (fun _ h => h) (by decide)
    | sext =>
      rcases argv with ⟨va, ⟨⟩⟩
      exact Machine.FallsTo.weaken (emitConvSext0_spec m n hin hwp)
        (fun _ h => h) (fun _ h => h) (by decide)
  | div d w =>
    rcases argv with ⟨va, vb, ⟨⟩⟩
    exact emitDiv0_spec d w hin.1 hin.2 hwp
  | umulw64 => exact False.elim hv

/-! ## 2. Linear Memory, Widening Mul, & `.jnz` Specifications -/

theorem emitLinUmulw0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (a b : Arg0) (cur : RegaTask0) (st : RegaSt0) {σ : List (BitVec 64)}
    {va vb : BitVec 64} {P : Tup Val [.bits 64, .bits 64] → Prop}
    {s : MachineData} {G : Mem 64 → Prop} {post : MachineState → Prop}
    (ha : ArgSlotVal64 cur.venv st.vslot σ a va)
    (hb : ArgSlotVal64 cur.venv st.vslot σ b vb)
    (hwp : OpCode.wp (OpCode.umulw 64) (va, vb, ()) P)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitLinUmulw0 a b cur { st with revDirs := [] })))
      x64ScratchAndAbi [] maskAll s
      (fun s' => ∃ lo hi : BitVec 64, P (lo, hi, ()) ∧
        s'.regs.get64 .rax = lo ∧ s'.regs.get64 .rdx = hi ∧ s'.dmem = s.dmem) post := by
  have hwp' : P (va * vb, BitVec.ofNat 64 (va.toNat * vb.toNat / 2 ^ 64), ()) := hwp
  dsimp only [emitLinUmulw0]
  have h1 := emitLoadArg0_spec (symName := symName) (h := h) (k := k) (post := post)
    .rdi (by decide) a cur.venv st.vslot ha hmem
  have hsplit : pushDRR0 5 .W64 .rsi .rsi (pushDRR0 0 .W64 .rax .rdi
      (emitLoadArg0 .rsi b cur.venv st.vslot (emitLoadArg0 .rdi a cur.venv st.vslot []))) =
      [.mulq .rsi, .movRR .W64 .rax .rdi] ++
        (emitLoadArg0 .rsi b cur.venv st.vslot [] ++
          emitLoadArg0 .rdi a cur.venv st.vslot []) := by
    rw [(emitLoadArg0_acc .rsi b cur.venv st.vslot _).1]; rfl
  rw [hsplit, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
  have hrsp_inv : ∀ s1 : MachineData,
      x64ScalarMach.Frame x64CondReads s s1 [.rdi, .r10] [] maskNone →
      s1.regs.get64 .rsp = s.regs.get64 .rsp :=
    fun _ hfr => hfr.1 .rsp (by simp)
  have h12 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitLoadArg0 .rdi a cur.venv st.vslot [])) ++
        toAmd64Program symName (emitFwd0 (emitLoadArg0 .rsi b cur.venv st.vslot [])))
      ([.rdi, .r10] ++ [.rsi, .r10]) ([] ++ []) (maskNone ||| maskNone) s
      (fun s2 => s2.regs.get64 .rdi = va ∧ s2.regs.get64 .rsi = vb ∧
        s2.dmem = s.dmem) post :=
    Machine.FallsTo.comp h1 fun s1 ⟨ha1, hm1⟩ hfr1 => by
      have hmem1 : s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ G := by
        rw [hm1, hrsp_inv s1 hfr1]; exact hmem
      exact Machine.FallsTo.conseq
        (emitLoadArg0_spec .rsi (by decide) b cur.venv st.vslot hb hmem1)
        fun s2 ⟨hb2, hm2⟩ hfr2 => by
          have hdi := hfr2.1 .rdi (by simp)
          dsimp only [x64ScalarMach] at hdi
          exact ⟨by rw [hdi, ha1], hb2, hm2.trans hm1⟩
  have hmul : ∀ (s2 : MachineData), s2.regs.get64 .rdi = va → s2.regs.get64 .rsi = vb →
      s2.dmem = s.dmem →
      x64ScalarMach.FallsTo x64CondReads h
        (k + (toAmd64Program symName (emitFwd0 (emitLoadArg0 .rdi a cur.venv st.vslot [])) ++
          toAmd64Program symName (emitFwd0 (emitLoadArg0 .rsi b cur.venv st.vslot []))).length)
        (toAmd64Program symName (emitFwd0 [.mulq .rsi, .movRR .W64 .rax .rdi]))
        [.rax, .rdx] [] maskAll s2
        (fun s' => ∃ lo hi : BitVec 64, P (lo, hi, ()) ∧
          s'.regs.get64 .rax = lo ∧ s'.regs.get64 .rdx = hi ∧ s'.dmem = s.dmem) post := by
    intro s2 ha2 hb2 hm2
    dsimp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, toAmd64Program, List.flatMap_cons, List.flatMap_nil, dir0ToAmd64,
      List.append_nil]
    apply scalar_fallsTo_of_wp; intro _ E
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD s2 .rax .rdi)) ?_
    rintro _ rfl
    have hmul_ft : Directive.FallsTo (ins (.mul (.reg (q .rsi))))
        { s2 with regs := s2.regs.set64 .rax (s2.regs.get64 .rdi) }
        (fun s3 => ∃ rax' rdx' st', rax' = va * vb ∧
          rdx' = BitVec.ofNat 64 (va.toNat * vb.toNat / 2 ^ 64) ∧
          s3 = { s2 with
            regs := ((s2.regs.set64 .rax (s2.regs.get64 .rdi)).set64 .rax rax').set64 .rdx rdx',
            status := st' }) := by
      intro _ _ _ _ _ hk
      simp only [t_step_simp, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
        Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .rax .rsi _ (by decide),
        ha2, hb2, show (Width.W64 == .W8) = false by decide, Bool.false_eq_true, ↓reduceIte]
      intro _ _ _ _
      exact hk _ ⟨_, _, _, BitVec.setWidth_eq _, by
        simp [umulw_hi], rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp hmul_ft) ?_
    rintro _ ⟨rax', rdx', st', rfl, rfl, rfl⟩
    refine ⟨⟨va * vb, BitVec.ofNat 64 (va.toNat * vb.toNat / 2 ^ 64), hwp',
      (Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide)).trans (Reg64s.get64_set64_same ..),
      Reg64s.get64_set64_same _ .rdx _, hm2⟩,
      scalarFrame_of_eq (fun r hr => ?_) (scalarUpdFlags_maskAll _ _)⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ .rdx r _ (Ne.symm hr.2),
      Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1),
      Reg64s.get64_set64_of_ne _ .rax r _ (Ne.symm hr.1)]
  have hfull : x64ScalarMach.FallsTo x64CondReads h k
      ((toAmd64Program symName (emitFwd0 (emitLoadArg0 .rdi a cur.venv st.vslot [])) ++
          toAmd64Program symName (emitFwd0 (emitLoadArg0 .rsi b cur.venv st.vslot []))) ++
        toAmd64Program symName (emitFwd0 [.mulq .rsi, .movRR .W64 .rax .rdi]))
      (([.rdi, .r10] ++ [.rsi, .r10]) ++ [.rax, .rdx]) (([] ++ []) ++ [])
      ((maskNone ||| maskNone) ||| maskAll) s
      (fun s' => ∃ lo hi : BitVec 64, P (lo, hi, ()) ∧
        s'.regs.get64 .rax = lo ∧ s'.regs.get64 .rdx = hi ∧ s'.dmem = s.dmem) post :=
    Machine.FallsTo.comp h12 fun s2 ⟨ha2, hb2, hm2⟩ _ => hmul s2 ha2 hb2 hm2
  exact Machine.FallsTo.weaken hfull (fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl) <;> simp [x64ScratchAndAbi])
    (fun _ hv => nomatch hv) (by decide)

theorem emitLinLoad0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (t : Ty0) (addr : Arg0) (cur : RegaTask0) (st : RegaSt0) {σ : List (BitVec 64)}
    {addrVal : BitVec 64} {v : Val (ty0ToTy t)} {s : MachineData} {G : Mem 64 → Prop}
    {post : MachineState → Prop}
    (ha : ArgSlotVal64 cur.venv st.vslot σ addr addrVal)
    (hlv : loadVal s.dmem (ty0ToTy t) addrVal = some v)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (pushDRR0 2 (tyWidth0 t) .rax .rdi
        (emitLoadArg0 .rdi addr cur.venv st.vslot []))))
      x64ScratchAndAbi [] maskNone s
      (fun s' => s'.regs.get64 .rax = toCanon64 t v ∧ s'.dmem = s.dmem) post := by
  have hsplit : pushDRR0 2 (tyWidth0 t) .rax .rdi (emitLoadArg0 .rdi addr cur.venv st.vslot []) =
      [.ldMem (tyWidth0 t) .rax .rdi] ++ emitLoadArg0 .rdi addr cur.venv st.vslot [] := rfl
  rw [hsplit, emitFwd0_append, toAmd64Program_append]
  have h1 := emitLoadArg0_spec (symName := symName) (h := h) (k := k) (post := post)
    .rdi (by decide) addr cur.venv st.vslot ha hmem
  have hcomp : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitLoadArg0 .rdi addr cur.venv st.vslot [])) ++
        toAmd64Program symName (emitFwd0 [.ldMem (tyWidth0 t) .rax .rdi]))
      ([.rdi, .r10] ++ [.rax]) ([] ++ []) (maskNone ||| maskNone) s
      (fun s' => s'.regs.get64 .rax = toCanon64 t v ∧ s'.dmem = s.dmem) post :=
    Machine.FallsTo.comp h1 fun s1 ⟨hr1, hm1⟩ _ => by
      have hlv1 : loadVal s1.dmem (ty0ToTy t) addrVal = some v := hm1 ▸ hlv
      refine scalar_fallsTo_of_wp fun {_} _ => ?_
      dsimp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append, toAmd64Program,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      cases t with
      | bool =>
        obtain ⟨i, hi, h01, hv⟩ := loadVal_bool_spec hlv1
        dsimp only [tyWidth0, dir0ToAmd64]
        refine Program.wp.mono (Directive.FallsTo.wp (Q := fun s2 =>
            s2 = { s1 with regs := s1.regs.set64 .rax (toCanon64 .bool v) }) (by
          intro _ _ _ _ _ hk
          simp only [t_step_simp, atReg_interp, hr1, MachineData.load,
            Effects.All_require_read_access, Width.bytes, hi]
          exact hk _ (by
            dsimp only [toCanon64, Width.bits]
            rw [hv]; congr 2; rcases h01 with rfl | rfl <;> decide))) ?_
        rintro _ rfl
        exact ⟨⟨by simp only [Reg64s.get64_set64_same], hm1⟩, scalarFrame_of_eq (fun r hr =>
          Reg64s.get64_set64_of_ne _ .rax r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
          (scalarUpdFlags_of_status_eq rfl _)⟩
      | b8 =>
        obtain ⟨i, hi, hv⟩ := loadVal_bits_spec (Or.inl rfl) hlv1
        dsimp only [tyWidth0, dir0ToAmd64]
        refine Program.wp.mono (Directive.FallsTo.wp (Q := fun s2 =>
            s2 = { s1 with regs := s1.regs.set64 .rax (toCanon64 .b8 v) }) (by
          intro _ _ _ _ _ hk
          simp only [t_step_simp, atReg_interp, hr1, MachineData.load,
            Effects.All_require_read_access, Width.bytes, Width.bits, hi,
            BitVec.zeroExtend_eq_setWidth,
            setWidth_up_down (m := 8) (n := 32) (k := 64) (by decide) (by decide)]
          exact hk _ (by dsimp only [toCanon64]; rw [hv]))) ?_
        rintro _ rfl
        exact ⟨⟨by simp only [Reg64s.get64_set64_same], hm1⟩, scalarFrame_of_eq (fun r hr =>
          Reg64s.get64_set64_of_ne _ .rax r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
          (scalarUpdFlags_of_status_eq rfl _)⟩
      | b16 =>
        obtain ⟨i, hi, hv⟩ := loadVal_bits_spec (Or.inr (Or.inl rfl)) hlv1
        dsimp only [tyWidth0, dir0ToAmd64]
        refine Program.wp.mono (Directive.FallsTo.wp (Q := fun s2 =>
            s2 = { s1 with regs := s1.regs.set64 .rax (toCanon64 .b16 v) }) (by
          intro _ _ _ _ _ hk
          simp only [t_step_simp, atReg_interp, hr1, MachineData.load,
            Effects.All_require_read_access, Width.bytes, Width.bits, hi,
            BitVec.zeroExtend_eq_setWidth,
            setWidth_up_down (m := 16) (n := 32) (k := 64) (by decide) (by decide)]
          exact hk _ (by dsimp only [toCanon64]; rw [hv]))) ?_
        rintro _ rfl
        exact ⟨⟨by simp only [Reg64s.get64_set64_same], hm1⟩, scalarFrame_of_eq (fun r hr =>
          Reg64s.get64_set64_of_ne _ .rax r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
          (scalarUpdFlags_of_status_eq rfl _)⟩
      | b32 =>
        obtain ⟨i, hi, hv⟩ := loadVal_bits_spec (Or.inr (Or.inr (Or.inl rfl))) hlv1
        dsimp only [tyWidth0, dir0ToAmd64]
        refine Program.wp.mono (Directive.FallsTo.wp (Q := fun s2 =>
            s2 = { s1 with regs := s1.regs.set64 .rax (toCanon64 .b32 v) }) (by
          intro _ _ _ _ _ hk
          simp only [t_step_simp, atReg_interp, hr1, MachineData.load,
            Effects.All_require_read_access, Width.bytes, Width.bits, hi,
            BitVec.zeroExtend_eq_setWidth]
          exact hk _ (by dsimp only [toCanon64]; rw [hv]))) ?_
        rintro _ rfl
        exact ⟨⟨by simp only [Reg64s.get64_set64_same], hm1⟩, scalarFrame_of_eq (fun r hr =>
          Reg64s.get64_set64_of_ne _ .rax r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
          (scalarUpdFlags_of_status_eq rfl _)⟩
      | b64 =>
        obtain ⟨i, hi, hv⟩ := loadVal_bits_spec (Or.inr (Or.inr (Or.inr rfl))) hlv1
        dsimp only [tyWidth0, dir0ToAmd64]
        refine Program.wp.mono (Directive.FallsTo.wp (Q := fun s2 =>
            s2 = { s1 with regs := s1.regs.set64 .rax (toCanon64 .b64 v) }) (by
          intro _ _ _ _ _ hk
          simp only [t_step_simp, atReg_interp, hr1, MachineData.load,
            Effects.All_require_read_access, Width.bytes, Width.bits, hi]
          exact hk _ (by dsimp only [toCanon64]; rw [hv]))) ?_
        rintro _ rfl
        exact ⟨⟨by simp only [Reg64s.get64_set64_same], hm1⟩, scalarFrame_of_eq (fun r hr =>
          Reg64s.get64_set64_of_ne _ .rax r _ (fun e => hr (List.mem_singleton.mpr e.symm)))
          (scalarUpdFlags_of_status_eq rfl _)⟩
  exact Machine.FallsTo.weaken hcomp (fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> simp [x64ScratchAndAbi])
    (fun _ hv => nomatch hv) (by decide)

theorem emitLinStore0_spec {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (t : Ty0) (val addr : Arg0) (cur : RegaTask0) (st : RegaSt0) {σ : List (BitVec 64)}
    {v : Val (ty0ToTy t)} {addrVal : BitVec 64} {s : MachineData} {G : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hv : ArgSlotVal64 cur.venv st.vslot σ val (toCanon64 t v))
    (ha : ArgSlotVal64 cur.venv st.vslot σ addr addrVal)
    (hok : storeOk s.dmem (ty0ToTy t) addrVal)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitLinStore0 t val addr cur { st with revDirs := [] })))
      x64ScratchAndAbi [] maskNone s
      (fun s' => s'.dmem = storeMem s.dmem (ty0ToTy t) addrVal v) post := by
  dsimp only [emitLinStore0]
  have h1 := emitLoadArg0_spec (symName := symName) (h := h) (k := k) (post := post)
    .rdi (by decide) val cur.venv st.vslot hv hmem
  have hsplit : pushDRR0 3 (tyWidth0 t) .rsi .rdi
      (emitLoadArg0 .rsi addr cur.venv st.vslot (emitLoadArg0 .rdi val cur.venv st.vslot [])) =
      [.stMem (tyWidth0 t) .rsi .rdi] ++
        (emitLoadArg0 .rsi addr cur.venv st.vslot [] ++
          emitLoadArg0 .rdi val cur.venv st.vslot []) := by
    rw [(emitLoadArg0_acc .rsi addr cur.venv st.vslot _).1]; rfl
  rw [hsplit, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
  have hrsp_inv : ∀ s1 : MachineData,
      x64ScalarMach.Frame x64CondReads s s1 [.rdi, .r10] [] maskNone →
      s1.regs.get64 .rsp = s.regs.get64 .rsp :=
    fun _ hfr => hfr.1 .rsp (by simp)
  have h12 : x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 (emitLoadArg0 .rdi val cur.venv st.vslot [])) ++
        toAmd64Program symName (emitFwd0 (emitLoadArg0 .rsi addr cur.venv st.vslot [])))
      ([.rdi, .r10] ++ [.rsi, .r10]) ([] ++ []) (maskNone ||| maskNone) s
      (fun s2 => s2.regs.get64 .rdi = toCanon64 t v ∧ s2.regs.get64 .rsi = addrVal ∧
        s2.dmem = s.dmem) post :=
    Machine.FallsTo.comp h1 fun s1 ⟨hr1, hm1⟩ hfr1 => by
      have hmem1 : s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ G := by
        rw [hm1, hrsp_inv s1 hfr1]; exact hmem
      exact Machine.FallsTo.conseq
        (emitLoadArg0_spec .rsi (by decide) addr cur.venv st.vslot ha hmem1)
        fun s2 ⟨hr2, hm2⟩ hfr2 => by
          have hdi := hfr2.1 .rdi (by simp)
          dsimp only [x64ScalarMach] at hdi
          exact ⟨by rw [hdi, hr1], hr2, hm2.trans hm1⟩
  have h123 : x64ScalarMach.FallsTo x64CondReads h k
      ((toAmd64Program symName (emitFwd0 (emitLoadArg0 .rdi val cur.venv st.vslot [])) ++
          toAmd64Program symName (emitFwd0 (emitLoadArg0 .rsi addr cur.venv st.vslot []))) ++
        toAmd64Program symName (emitFwd0 [.stMem (tyWidth0 t) .rsi .rdi]))
      (([.rdi, .r10] ++ [.rsi, .r10]) ++ x64Scratch) (([] ++ []) ++ [])
      ((maskNone ||| maskNone) ||| maskNone) s
      (fun s' => s'.dmem = storeMem s.dmem (ty0ToTy t) addrVal v) post :=
    Machine.FallsTo.comp h12 fun s2 ⟨hr1, hr2, hm2⟩ _ => by
      have hs0 : x64Gpr.store (ty0ToTy t) (.gpr .rdi) (.baseDisp .rsi 0) =
          some (toAmd64Program symName (emitFwd0 [.stMem (tyWidth0 t) .rsi .rdi]), maskNone) := by
        cases t <;> rfl
      have hpa : x64Mach.PArgHolds s2 (ty0ToTy t) (.gpr .rdi) v := by
        dsimp only [Machine.PArgHolds, x64Mach]
        rw [hr1]
        exact toCanon64_toGprHolds t v
      have heval : (AddrArg.baseDisp .rsi 0).eval s2.regs.get64 = addrVal := by
        dsimp only [AddrArg.eval]
        rw [hr2, show (0 : Int64).toBitVec = 0#64 from rfl, BitVec.add_zero]
      refine Machine.FallsTo.conseq
        (scalar_fallsTo_of_x64 (x64Gpr_store_spec hs0
          (fun r hr => by
            dsimp only [x64Scratch]
            simp only [PArg.gprs, AddrArg.regs, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at hr ⊢
            rcases hr with rfl | rfl <;> simp)
          hpa (by rw [hm2, heval]; exact hok)))
        fun s' hdm _ => by rw [hm2, heval] at hdm; exact hdm
  exact Machine.FallsTo.weaken h123 (fun r hr => by
    dsimp only [x64Scratch] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl) <;> simp [x64ScratchAndAbi])
    (fun _ hv => nomatch hv) (by decide)

theorem jnzPrep0_spec {symName : Sym0 → Sym} {h : Host} {k j : Nat}
    (esc : Array Nat) (c : Arg0) (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0)
    {σ : List (BitVec 64)} {cv : Bool} {s : MachineData} {G : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hc : ArgSlotVal64 cur.venv st.vslot σ c (toCanon64 .bool cv))
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G)
    (hlbl : x64ScalarMach.labelAddr h (label0ToSym symName (.loc ctrl.fnIdx ctrl.nextLbl)) =
      x64ScalarMach.addrOf h j)
    (hcode : (toAmd64Program symName (emitFwd0
        (jnzPrep0 esc c cur { st with revDirs := [] } ctrl).2)).IsInfixAt
      (x64ScalarMach.prog h) k)
    (hk : ∀ s', x64ScalarMach.Frame x64CondReads s s' x64ScratchAndAbi [] maskAll →
      s'.dmem = s.dmem →
      (cv = true → x64ScalarMach.Run h j s' post) ∧
      (cv = false → x64ScalarMach.Run h
        (k + (toAmd64Program symName (emitFwd0
          (jnzPrep0 esc c cur { st with revDirs := [] } ctrl).2)).length) s' post)) :
    x64ScalarMach.Run h k s post := by
  have hprep : (jnzPrep0 esc c cur { st with revDirs := [] } ctrl).2 =
      [.jcc .nz (.loc ctrl.fnIdx ctrl.nextLbl), .testbRR .rax .rax] ++
        emitLoadArg0 .rax c cur.venv st.vslot [] := rfl
  rw [hprep, emitFwd0_append, toAmd64Program_append] at hcode hk
  let p1 := toAmd64Program symName (emitFwd0 (emitLoadArg0 .rax c cur.venv st.vslot []))
  let p2 := toAmd64Program symName
    (emitFwd0 [.jcc .nz (.loc ctrl.fnIdx ctrl.nextLbl), .testbRR .rax .rax])
  have hp1_inf : p1.IsInfixAt (x64ScalarMach.prog h) k := hcode.append.1
  have hp2_inf : p2.IsInfixAt (x64ScalarMach.prog h) (k + p1.length) := hcode.append.2
  have hload := emitLoadArg0_spec (symName := symName) (h := h) (k := k) (post := post)
    .rax (by decide) c cur.venv st.vslot hc hmem
  refine hload hp1_inf fun s1 ⟨hr1, hm1⟩ hfr1 => ?_
  have hr1_gh : GprHolds (x64ScalarMach.getGpr s1 .rax) .bool cv :=
    op0_argsIn_to_regs_bool hr1
  have hp2_eq : p2 =
      (x64ScalarGpr.jnzGpr .rax (label0ToSym symName (.loc ctrl.fnIdx ctrl.nextLbl))).1 := rfl
  refine x64Scalar_gprSpec.jnzGpr_spec
    (hp2_eq ▸ hp2_inf) hlbl (by simp [x64Scratch]) hr1_gh
    (k := k + p1.length) (post := post) fun s2 hfr2 hm2 => ?_
  have hfr : x64ScalarMach.Frame x64CondReads s s2 x64ScratchAndAbi [] maskAll :=
    (hfr1.trans hfr2).weaken (fun r hr => by
      dsimp only [x64Scratch] at hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | (rfl | rfl) <;> simp [x64ScratchAndAbi])
      (fun _ hv => nomatch hv)
      (by rw [show ~~~maskAll = 0#8 by decide, BitVec.and_zero])
  have hrun := hk s2 hfr (hm2.trans hm1)
  refine ⟨fun ht => hrun.1 ht, fun hf => ?_⟩
  have hlen : k + p1.length + (x64ScalarGpr.jnzGpr .rax
      (label0ToSym symName (.loc ctrl.fnIdx ctrl.nextLbl))).1.length =
      k + (p1 ++ p2).length := by
    rw [← hp2_eq, List.length_append, Nat.add_assoc]
  rw [hlen]
  exact hrun.2 hf

end

end LeanQbe.T.Bootstrap0
