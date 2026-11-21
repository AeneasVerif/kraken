module

public import LeanQbe.T.Amd64.IselLemmas4
public import LeanQbe.T.LegalOpWpLemmas1
import Kraken.X64.Parser

/-!
# x64 Scalar Bit-Counting Proofs (`lzcnt`/`tzcnt`/`popcnt`/`cls`) & BMI2 Parser Checks

Proves `opBitcnt_spec` across all four bit-counting opcodes (`.clz`, `.cls`, `.ctz`, `.popcnt`)
and all four supported scalar widths (`8`, `16`, `32`, `64`), including `.imm` constant folding
(`maskNone`) and `.gpr` sequences (`maskAll`, `8`/`16`-bit widening to `.W32` and `.cls`
sign-mask lowering). Also verifies AT&T parser round-trips for BMI2 and bit-counting instructions.
-/

set_option autoImplicit false

namespace LeanQbe.T.Amd64

open LeanQbe.T

/-! ## 1. Kraken AT&T Parser Checks for BMI2 & Bit-Counting Instructions -/

section ParserChecks
open Kraken.X64.Parser

example : ⸨prog| shlxl %ecx, %esi, %eax ⸩ =
    [ins32 (.shlx (d .rax) (.reg (d .rsi)) (d .rcx))] := rfl
example : ⸨prog| shrxl %ecx, %esi, %eax ⸩ =
    [ins32 (.shrx (d .rax) (.reg (d .rsi)) (d .rcx))] := rfl
example : ⸨prog| sarxl %ecx, %esi, %eax ⸩ =
    [ins32 (.sarx (d .rax) (.reg (d .rsi)) (d .rcx))] := rfl
example : ⸨prog| shlxq %rcx, %rsi, %rax ⸩ =
    [ins (.shlx (q .rax) (.reg (q .rsi)) (q .rcx))] := rfl
example : ⸨prog| shrxq %rcx, %rsi, %rax ⸩ =
    [ins (.shrx (q .rax) (.reg (q .rsi)) (q .rcx))] := rfl
example : ⸨prog| sarxq %rcx, %rsi, %rax ⸩ =
    [ins (.sarx (q .rax) (.reg (q .rsi)) (q .rcx))] := rfl
example : ⸨prog| rorxl $5, %esi, %eax ⸩ =
    [ins32 (.rorx (d .rax) (.reg (d .rsi)) (.int64 5))] := rfl
example : ⸨prog| rorxq $59, %rsi, %rax ⸩ =
    [ins (.rorx (q .rax) (.reg (q .rsi)) (.int64 59))] := rfl
example : ⸨prog| lzcntl %esi, %eax ⸩ = [ins32 (.lzcnt (d .rax) (.reg (d .rsi)))] := rfl
example : ⸨prog| lzcntq %rsi, %rax ⸩ = [ins (.lzcnt (q .rax) (.reg (q .rsi)))] := rfl
example : ⸨prog| tzcntl %esi, %eax ⸩ = [ins32 (.tzcnt (d .rax) (.reg (d .rsi)))] := rfl
example : ⸨prog| tzcntq %rsi, %rax ⸩ = [ins (.tzcnt (q .rax) (.reg (q .rsi)))] := rfl
example : ⸨prog| popcntl %esi, %eax ⸩ = [ins32 (.popcnt (d .rax) (.reg (d .rsi)))] := rfl
example : ⸨prog| popcntq %rsi, %rax ⸩ = [ins (.popcnt (q .rax) (.reg (q .rsi)))] := rfl
example : ⸨prog| sarl $31, %r11d ⸩ =
    [ins32 (.sar (.reg (d .r11)) (.imm8 (.int64 31)))] := rfl
example : ⸨prog| sarq $63, %r11 ⸩ =
    [ins (.sar (.reg (q .r11)) (.imm8 (.int64 63)))] := rfl

end ParserChecks

@[expose] public section

/-! ## 2. Pure `BitVec` Helpers & Single-Directive `FallsTo` Lemmas -/

private theorem cpopNatRec__eq {w : Nat} (x : BitVec w) (pos acc : Nat) :
    x.cpopNatRec_ pos acc = x.cpopNatRec pos acc := by
  induction pos generalizing acc with
  | zero => rfl
  | succ n ih => exact ih _

theorem cpop__eq {w : Nat} (x : BitVec w) : x.cpop_ = x.cpop := by
  unfold BitVec.cpop_ BitVec.cpop
  rw [cpopNatRec__eq]

private theorem sshiftRight_sub_one_xor {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.sshiftRight (w - 1) ^^^ x = if x.msb = true then ~~~x else x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have hnot_i : (~~~x).getLsbD i = !x.getLsbD i := by
    rw [BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]
  by_cases h0 : i = 0
  · subst h0
    simp only [show ¬ (w ≤ 0) by omega, decide_false, Bool.not_false, Bool.true_and,
      show w - 1 + 0 = w - 1 by omega, show w - 1 < w by omega, ↓reduceIte]
    cases hmsb : x.getLsbD (w - 1) <;> cases h0b : x.getLsbD 0 <;> simp [hnot_i, h0b]
  · simp only [show ¬ (w ≤ i) by omega, decide_false, Bool.not_false, Bool.true_and]
    rw [show (if w - 1 + i < w then x.getLsbD (w - 1 + i) else x.getLsbD (w - 1)) =
        x.getLsbD (w - 1) from by
      by_cases hlt : w - 1 + i < w
      · exfalso; omega
      · simp [hlt]]
    cases hmsb : x.getLsbD (w - 1) <;> cases hib : x.getLsbD i <;> simp [hnot_i, hib]

private theorem cls_sub_33_eq {n : Nat} (hn : 0 < n) (hn32 : n < 32) (a : BitVec n) :
    (if (a.signExtend 32).msb = true then (~~~a.signExtend 32).clz else (a.signExtend 32).clz) -
        BitVec.ofNat 32 (33 - n) =
      BitVec.setWidth 32 ((if a.msb = true then (~~~a).clz else a.clz) - 1#n) := by
  have hsplit : BitVec.ofNat 32 (33 - n) = 1#32 + BitVec.ofNat 32 (32 - n) := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (show 33 - n < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show 32 - n < 2 ^ 32 by omega)]
    omega
  rw [hsplit, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.sub_eq_add_neg (-1#32),
    ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg, ← BitVec.sub_eq_add_neg]
  exact opWp_cls_widened hn hn32 a

private theorem setWidth_32_cancel {n : Nat} (hn : n ≤ 32) {rv : BitVec 64} {y : BitVec n}
    (h : rv.setWidth 32 = y.setWidth 32) : rv.setWidth n = y := by
  rw [← BitVec.setWidth_setWidth_of_le rv hn, h, BitVec.setWidth_setWidth_of_le y hn,
    BitVec.setWidth_eq]

private theorem fallsTo_lzcntW (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rs : Reg64) :
    Directive.FallsTo (insW w (.lzcnt (regW w rd) (.reg (regW w rs)))) s (fun s' =>
      ∃ rv st, rv.setWidth w.bits = ((s.regs.get64 rs).setWidth w.bits).clz ∧
        s' = { s with regs := s.regs.set64 rd rv, status := st }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl <;>
    simp only [insW, regW, t_step_simp, Reg64s.set, Effects.All] <;>
    intro _ _ _ _ <;>
    refine hk _ ⟨_, _, ?_, rfl⟩
  · simp [Width.bits]
  · simp [Width.bits, BitVec.setWidth_eq]

private theorem fallsTo_tzcntW (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rs : Reg64) :
    Directive.FallsTo (insW w (.tzcnt (regW w rd) (.reg (regW w rs)))) s (fun s' =>
      ∃ rv st, rv.setWidth w.bits = ((s.regs.get64 rs).setWidth w.bits).reverse.clz ∧
        s' = { s with regs := s.regs.set64 rd rv, status := st }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl <;>
    simp only [insW, regW, t_step_simp, Reg64s.set, Effects.All] <;>
    intro _ _ _ _ <;>
    refine hk _ ⟨_, _, ?_, rfl⟩
  · simp [Width.bits]
  · simp [Width.bits, BitVec.setWidth_eq]

private theorem fallsTo_popcntW (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rs : Reg64) :
    Directive.FallsTo (insW w (.popcnt (regW w rd) (.reg (regW w rs)))) s (fun s' =>
      ∃ rv st, rv.setWidth w.bits = ((s.regs.get64 rs).setWidth w.bits).cpop ∧
        s' = { s with regs := s.regs.set64 rd rv, status := st }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl <;>
    simp only [insW, regW, t_step_simp, Reg64s.set] <;>
    refine hk _ ⟨_, _, ?_, rfl⟩
  · rw [cpop__eq]; simp [Width.bits]
  · rw [cpop__eq]; simp [Width.bits, BitVec.setWidth_eq]

private theorem fallsTo_sarMaskW (w : Width) (hw : w = .W32 ∨ w = .W64)
    (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.sar (.reg (regW w rd))
        (.imm8 (.int64 (Int64.ofNat (w.bits - 1)))))) s (fun s' =>
      ∃ rv st, rv.setWidth w.bits = ((s.regs.get64 rd).setWidth w.bits).sshiftRight (w.bits - 1) ∧
        s' = { s with regs := s.regs.set64 rd rv, status := st }) := by
  intro _ _ _ _ _ hk
  have htk31 : ((Int64.ofNat 31).toBitVec.take 8).toNat = 31 := by decide
  have htk63 : ((Int64.ofNat 63).toBitVec.take 8).toNat = 63 := by decide
  rcases hw with rfl | rfl <;>
    simp only [insW, regW, Width.bits, show (32 - 1 : Nat) = 31 from rfl,
      show (64 - 1 : Nat) = 63 from rfl, t_step_simp, ShiftCountExpr.interpMasked,
      ShiftCountExpr.interp, ConstExpr.interp, htk31, htk63, Reg64s.set, Effects.All]
  · rw [show (31 &&& 31 : Nat) = 31 from rfl]
    simp only [show (31 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      show (31 == 1) = false from rfl]
    intro _ _; refine hk _ ⟨_, _, ?_, rfl⟩
    simp [Width.bits]
  · rw [show (63 &&& 63 : Nat) = 63 from rfl]
    simp only [show (63 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      show (63 == 1) = false from rfl]
    intro _ _; refine hk _ ⟨_, _, ?_, rfl⟩
    simp [Width.bits]

/-! ## 3. `opBitcnt_spec` across `.clz`, `.cls`, `.ctz`, `.popcnt` × `[8, 16, 32, 64]` -/

private theorem opBitcnt_narrow_zx_wp [Host] {E : Int64 → MachineData → Prop}
    (w : Width) (hw : w = .W8 ∨ w = .W16) (rd ra : Reg64) {va : BitVec w.bits}
    (s : MachineData) (hpa : (s.regs.get64 ra).setWidth w.bits = va) :
    _root_.Program.wp [movW w rd ra] (fun s1 =>
      ∃ st, (s1.regs.get64 rd).setWidth 32 = va.setWidth 32 ∧
        (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
        s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ st = s1.status) E s := by
  rcases hw with rfl | rfl
  · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 s rd ra)) ?_
    rintro s1 rfl
    refine ⟨s.status, ?_, fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl, rfl⟩
    rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), hpa]
  · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx16 s rd ra)) ?_
    rintro s1 rfl
    refine ⟨s.status, ?_, fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl, rfl⟩
    rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), hpa]

private theorem opBitcnt_narrow_sx_wp [Host] {E : Int64 → MachineData → Prop}
    (w : Width) (hw : w = .W8 ∨ w = .W16) (rd ra : Reg64) {va : BitVec w.bits}
    (s : MachineData) (hpa : (s.regs.get64 ra).setWidth w.bits = va) :
    _root_.Program.wp [match w with
      | .W8 => ins32 (.movsx (.reg (d rd)) (.reg (b8 ra)))
      | _   => ins32 (.movsx (.reg (d rd)) (.reg (h16 ra)))] (fun s1 =>
      (s1.regs.get64 rd).setWidth 32 = va.signExtend 32 ∧
      (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
      s1.dmem = s.dmem ∧ s1.zmms = s.zmms) E s := by
  rcases hw with rfl | rfl
  · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx8 .W32 (.inl rfl) s rd ra)) ?_
    rintro s1 rfl
    refine ⟨?_, fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl⟩
    rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq, hpa]
  · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx16 .W32 (.inl rfl) s rd ra)) ?_
    rintro s1 rfl
    refine ⟨?_, fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl⟩
    rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq, hpa]

private theorem bitcnt_wide_step_wp [Host] {E : Int64 → MachineData → Prop}
    (w : Width) (hw : w = .W32 ∨ w = .W64) (bk : BitcntKind) (ra rd : Reg64)
    {va : BitVec w.bits} {c : List Directive} (s : MachineData) (ha : ra ∉ x64Scratch)
    (hpa : (s.regs.get64 ra).setWidth w.bits = va)
    (hc : (match bk with
      | .popcnt => [insW w (.popcnt (regW w rd) (.reg (regW w ra)))]
      | .clz    => [insW w (.lzcnt (regW w rd) (.reg (regW w ra)))]
      | .ctz    => [insW w (.tzcnt (regW w rd) (.reg (regW w ra)))]
      | .cls    => [movW w .r11 ra,
                    insW w (.sar (.reg (regW w .r11)) (.imm8 (.int64 (Int64.ofNat (w.bits - 1))))),
                    aluBinIns w .xor .r11 (.reg (regW w ra)),
                    insW w (.lzcnt (regW w rd) (.reg (regW w .r11))),
                    insW w (.dec (.reg (regW w rd)))]) = c) :
    _root_.Program.wp c (OpPost1 (.bits w.bits) rd (bk.eval w va) maskAll s) E s := by
  subst hc
  cases bk with
  | popcnt =>
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_popcntW w hw s rd ra)) ?_
    rintro s' ⟨rv, st, hrv, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hpa]; rfl), rfl,
      x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_maskAll _ _)⟩
    simp only [List.mem_cons, not_or] at hr
    exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
  | clz =>
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_lzcntW w hw s rd ra)) ?_
    rintro s' ⟨rv, st, hrv, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hpa]; rfl), rfl,
      x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_maskAll _ _)⟩
    simp only [List.mem_cons, not_or] at hr
    exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
  | ctz =>
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_tzcntW w hw s rd ra)) ?_
    rintro s' ⟨rv, st, hrv, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hpa]; rfl), rfl,
      x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_maskAll _ _)⟩
    simp only [List.mem_cons, not_or] at hr
    exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
  | cls =>
    have hra11 : ra ≠ .r11 := (ne_of_not_mem_x64Scratch ha).2
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW w s .r11 ra)) ?_
    rintro s1 rfl
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_sarMaskW w hw _ .r11)) ?_
    rintro s2 ⟨rv11', st2, hrv11', rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_aluBinIns_reg w .xor _ .r11 ra)) ?_
    rintro s3 ⟨rv11'', st3, hrv11'', rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_lzcntW w hw _ rd .r11)) ?_
    rintro s4 ⟨rvd, st4, hrvd, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_decW w _ rd)) ?_
    rintro s5 ⟨rvd', st5, hrvd', _, rfl⟩
    let rv11 := ((s.regs.get64 ra).setWidth w.bits).setWidth 64
    have hrv11 : rv11.setWidth w.bits = va := by
      dsimp only [rv11]
      rw [BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w), BitVec.setWidth_eq, hpa]
    have ha1 : (((s.regs.set64 .r11 rv11).set64 .r11 rv11').get64 ra).setWidth w.bits = va := by
      rw [Reg64s.get64_set64_of_ne _ .r11 ra _ hra11.symm,
        Reg64s.get64_set64_of_ne _ .r11 ra _ hra11.symm, hpa]
    have h11_1 : (s.regs.set64 .r11 rv11).get64 .r11 = rv11 := Reg64s.get64_set64_same ..
    have h11_2 : ((s.regs.set64 .r11 rv11).set64 .r11 rv11').get64 .r11 = rv11' :=
      Reg64s.get64_set64_same ..
    have h11_3 : (((((s.regs.set64 .r11 rv11).set64 .r11 rv11')).set64 .r11 rv11'').get64
        .r11).setWidth w.bits = if va.msb = true then ~~~va else va := by
      rw [Reg64s.get64_set64_same, hrv11'']
      dsimp only [AluBinKind.eval]
      rw [h11_2, hrv11', h11_1, hrv11, ha1]
      exact sshiftRight_sub_one_xor (width_bits_pos w) va
    have hmsb_if : (if va.msb = true then ~~~va else va).clz =
        if va.msb = true then (~~~va).clz else va.clz := by cases va.msb <;> rfl
    refine ⟨(GprHolds.bits_iff w _ _).2 ?_, rfl, x64_frame_of_eq (fun r hr => ?_) rfl
        (updFlags_maskAll _ _)⟩
    · rw [Reg64s.get64_set64_same, hrvd', Reg64s.get64_set64_same, hrvd, h11_3, hmsb_if]; rfl
    · simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
        Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
        Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1)]

private theorem bitcnt_narrow_step_wp [Host] {E : Int64 → MachineData → Prop}
    (w : Width) (hw : w = .W8 ∨ w = .W16) (bk : BitcntKind) (ra rd : Reg64)
    {va : BitVec w.bits} {c : List Directive} (s : MachineData) (hrd : rd ∉ x64Scratch)
    (hpa : (s.regs.get64 ra).setWidth w.bits = va)
    (hc : (match bk with
      | .popcnt => [movW w rd ra, ins32 (.popcnt (d rd) (.reg (d rd)))]
      | .clz    => [movW w rd ra, ins32 (.lzcnt (d rd) (.reg (d rd))),
                    aluBinIns .W32 .sub rd (immBitsOp .W32 (BitVec.ofNat 32 (32 - w.bits)))]
      | .ctz    => [movW w rd ra,
                    aluBinIns .W32 .or rd (immBitsOp .W32 (BitVec.ofNat 32 (1 <<< w.bits))),
                    ins32 (.tzcnt (d rd) (.reg (d rd)))]
      | .cls    =>
        let movsx := match w with
          | .W8 => ins32 (.movsx (.reg (d rd)) (.reg (b8 ra)))
          | _   => ins32 (.movsx (.reg (d rd)) (.reg (h16 ra)))
        [movsx, movlD .r11 rd,
         ins32 (.sar (.reg (d .r11)) (.imm8 (.int64 31))),
         aluBinIns .W32 .xor rd (.reg (d .r11)),
         ins32 (.lzcnt (d rd) (.reg (d rd))),
         aluBinIns .W32 .sub rd (immBitsOp .W32 (BitVec.ofNat 32 (33 - w.bits)))]) = c) :
    _root_.Program.wp c (OpPost1 (.bits w.bits) rd (bk.eval w va) maskAll s) E s := by
  subst hc
  have hw_pos : 0 < w.bits := width_bits_pos w
  have hw_lt32 : w.bits < 32 := by rcases hw with rfl | rfl <;> decide
  have hw_le32 : w.bits ≤ 32 := Nat.le_of_lt hw_lt32
  have hrd11 : rd ≠ .r11 := (ne_of_not_mem_x64Scratch hrd).2
  cases bk with
  | popcnt =>
    refine Program.wp.append (opBitcnt_narrow_zx_wp w hw rd ra s hpa) ?_
    rintro s1 ⟨_, hrd1, hfr1, hm1, hz1, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_popcntW .W32 (.inl rfl) s1 rd rd)) ?_
    rintro s2 ⟨rv, st, hrv, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 ?_, hm1, x64_frame_of_eq (fun r hr => ?_) hz1
        (updFlags_maskAll _ _)⟩
    · apply setWidth_32_cancel hw_le32
      simp only [Width.bits] at hrv
      dsimp only
      rw [Reg64s.get64_set64_same, hrv, hrd1]
      exact opWp_popcnt_widened hw_le32 va
    · simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hfr1 r hr.1]
  | clz =>
    refine Program.wp.append (opBitcnt_narrow_zx_wp w hw rd ra s hpa) ?_
    rintro s1 ⟨_, hrd1, hfr1, hm1, hz1, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_lzcntW .W32 (.inl rfl) s1 rd rd)) ?_
    rintro s2 ⟨rv1, st1, hrv1, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp
      (fallsTo_aluBinIns_imm .W32 .sub _ rd (BitVec.ofNat 32 (32 - w.bits)))) ?_
    rintro s3 ⟨rv2, st2, hrv2, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 ?_, hm1, x64_frame_of_eq (fun r hr => ?_) hz1
        (updFlags_maskAll _ _)⟩
    · apply setWidth_32_cancel hw_le32
      simp only [Width.bits] at hrv1 hrv2
      dsimp only at hrv2 ⊢
      rw [Reg64s.get64_set64_same, hrv2, AluBinKind.eval, Reg64s.get64_set64_same, hrv1, hrd1]
      exact opWp_clz_widened hw_pos hw_lt32 va
    · simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hfr1 r hr.1]
  | ctz =>
    have hpow_sh : 1 <<< w.bits = 2 ^ w.bits := by rcases hw with rfl | rfl <;> decide
    refine Program.wp.append (opBitcnt_narrow_zx_wp w hw rd ra s hpa) ?_
    rintro s1 ⟨_, hrd1, hfr1, hm1, hz1, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp
      (fallsTo_aluBinIns_imm .W32 .or s1 rd (BitVec.ofNat 32 (1 <<< w.bits)))) ?_
    rintro s2 ⟨rv1, st1, hrv1, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_tzcntW .W32 (.inl rfl) _ rd rd)) ?_
    rintro s3 ⟨rv2, st2, hrv2, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 ?_, hm1, x64_frame_of_eq (fun r hr => ?_) hz1
        (updFlags_maskAll _ _)⟩
    · apply setWidth_32_cancel hw_le32
      simp only [Width.bits] at hrv1 hrv2
      dsimp only at hrv2 ⊢
      rw [Reg64s.get64_set64_same, hrv2, Reg64s.get64_set64_same, hrv1, AluBinKind.eval, hrd1,
        hpow_sh]
      exact opWp_ctz_widened hw_pos hw_lt32 va
    · simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hfr1 r hr.1]
  | cls =>
    refine Program.wp.append (opBitcnt_narrow_sx_wp w hw rd ra s hpa) ?_
    rintro s1 ⟨hrd1, hfr1, hm1, hz1⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movlD s1 .r11 rd)) ?_
    rintro s2 rfl
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_sarMaskW .W32 (.inl rfl) _ .r11)) ?_
    rintro s3 ⟨rv11, st3, hrv11, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp
      (fallsTo_aluBinIns_reg .W32 .xor _ rd .r11)) ?_
    rintro s4 ⟨rvd1, st4, hrvd1, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_lzcntW .W32 (.inl rfl) _ rd rd)) ?_
    rintro s5 ⟨rvd2, st5, hrvd2, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp
      (fallsTo_aluBinIns_imm .W32 .sub _ rd (BitVec.ofNat 32 (33 - w.bits)))) ?_
    rintro s6 ⟨rvd3, st6, hrvd3, rfl⟩
    simp only [Width.bits] at hrv11 hrvd1 hrvd2 hrvd3
    dsimp only at hrv11 hrvd1 hrvd2 hrvd3 ⊢
    have h11_2 : (s1.regs.set64 .r11 (((s1.regs.get64 rd).setWidth 32).zeroExtend 64)).get64
        .r11 = ((s1.regs.get64 rd).setWidth 32).zeroExtend 64 := Reg64s.get64_set64_same ..
    have hrd_2 : ((s1.regs.set64 .r11 (((s1.regs.get64 rd).setWidth 32).zeroExtend 64)).get64
        rd).setWidth 32 = va.signExtend 32 := by
      rw [Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm, hrd1]
    have hrd_3 : (((s1.regs.set64 .r11 (((s1.regs.get64 rd).setWidth 32).zeroExtend 64)).set64
        .r11 rv11).get64 rd).setWidth 32 = va.signExtend 32 := by
      rw [Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm, hrd_2]
    have h11_3 : (((s1.regs.set64 .r11 (((s1.regs.get64 rd).setWidth 32).zeroExtend 64)).set64
        .r11 rv11).get64 .r11).setWidth 32 = (va.signExtend 32).sshiftRight 31 := by
      rw [Reg64s.get64_set64_same, hrv11, h11_2, BitVec.zeroExtend_eq_setWidth,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, hrd1]
    have hrd_4 : rvd1.setWidth 32 =
        if (va.signExtend 32).msb = true then ~~~va.signExtend 32 else va.signExtend 32 := by
      rw [hrvd1, AluBinKind.eval, hrd_3, h11_3, BitVec.xor_comm]
      exact sshiftRight_sub_one_xor (by decide : 0 < 32) (va.signExtend 32)
    have hmsb_if : (if (va.signExtend 32).msb = true then ~~~va.signExtend 32
          else va.signExtend 32).clz =
        if (va.signExtend 32).msb = true then (~~~va.signExtend 32).clz
        else (va.signExtend 32).clz := by
      cases (va.signExtend 32).msb <;> rfl
    refine ⟨(GprHolds.bits_iff w _ _).2 ?_, hm1, x64_frame_of_eq (fun r hr => ?_) hz1
        (updFlags_maskAll _ _)⟩
    · apply setWidth_32_cancel hw_le32
      rw [Reg64s.get64_set64_same, hrvd3, AluBinKind.eval, Reg64s.get64_set64_same, hrvd2,
        Reg64s.get64_set64_same, hrd_4, hmsb_if]
      exact cls_sub_33_eq hw_pos hw_lt32 va
    · simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
        Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
        hfr1 r hr.1]

theorem opBitcnt_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (bk : BitcntKind)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opBitcntIns w bk pa rd = some (c, clob))
    (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (bk.eval w va) clob s) E s := by
  cases pa with
  | vec _ => simp [opBitcntIns] at hc
  | imm ca =>
    rcases hpa with rfl
    simp only [opBitcntIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
    rintro s' rfl
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, setWidth_64_setWidth]),
      rfl, x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_of_status_eq rfl _)⟩
    simp only [List.mem_cons, not_or] at hr
    exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
  | gpr ra =>
    have ha := hargs ra (by simp [PArg.gprs])
    have hpa' := (GprHolds.bits_iff w _ _).1 hpa
    dsimp only [opBitcntIns] at hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨hc_eq, rfl⟩
    cases w with
    | W8 =>
      refine bitcnt_narrow_step_wp .W8 (.inl rfl) bk ra rd s hrd hpa' ?_
      rw [← hc_eq]; cases bk <;> rfl
    | W16 =>
      refine bitcnt_narrow_step_wp .W16 (.inr rfl) bk ra rd s hrd hpa' ?_
      rw [← hc_eq]; cases bk <;> rfl
    | W32 =>
      refine bitcnt_wide_step_wp .W32 (.inl rfl) bk ra rd s ha hpa' ?_
      rw [← hc_eq]; cases bk <;> rfl
    | W64 =>
      refine bitcnt_wide_step_wp .W64 (.inr rfl) bk ra rd s ha hpa' ?_
      rw [← hc_eq]; cases bk <;> rfl

end

end LeanQbe.T.Amd64
