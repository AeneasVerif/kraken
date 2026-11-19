module

public import LeanQbe.T.Arm64.IselLemmas1

/-!
# AArch64 Scalar Instruction Selection Proofs — Part 2 (`T9`)

Weakest-precondition correctness invariants for core scalar `armOp` builders: `armBoolOp`,
`armCopyBits`, `armZextOp`, `armSextOp`, `armTruncOp`, `armOfBoolOp`, `armBinOp`, `neg`,
`not`, `armShiftOp`, and `armRotOp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

/-! ## 1. Operand-pair combinators & shared helpers -/

theorem not_not_eq_true {b : Bool} (h : ¬ ((!b) = true)) : b = true := by
  cases b <;> simp at h ⊢

theorem option_none_or_some {α : Type} (o : Option α) : o = none ∨ ∃ a, o = some a := by
  cases o <;> simp

private theorem setWidth8_and (a b : BitVec 32) : (a &&& b).setWidth 8 = a.setWidth 8 &&& b.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi, show i < 32 by omega]
private theorem setWidth8_or (a b : BitVec 32) : (a ||| b).setWidth 8 = a.setWidth 8 ||| b.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi, show i < 32 by omega]
private theorem setWidth8_xor (a b : BitVec 32) : (a ^^^ b).setWidth 8 = a.setWidth 8 ^^^ b.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi, show i < 32 by omega]

@[t_step_simp] theorem getRegOrSp_low_reg (regs : Reg64s) (r : XReg) (w : RegWidth) :
    regs.getRegOrSp (.low (.reg r) w) = (regs.getXReg r).toBitVec.setWidth w.bits := by
  cases w <;> simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take] <;> rfl

@[t_step_simp] theorem setRegOrSp_low_reg (regs : Reg64s) (r : XReg) (w : RegWidth) (v : BitVec w.bits) :
    regs.setRegOrSp (.low (.reg r) w) v = regs.setXReg r (v.setWidth 64) := by
  cases w <;> rfl

theorem mem_armWidths {n : Nat} (hn : n ∈ [8, 16, 32, 64]) :
    n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by simpa using hn

theorem mem_armWidths_le_64 {n : Nat} (hn : n ∈ [8, 16, 32, 64]) : n ≤ 64 := by
  rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> decide

theorem mem_armWidths_le_armWidth {n : Nat} (hn : n ∈ [8, 16, 32, 64]) :
    n ≤ (armWidthOf n).bits := by
  rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> decide

theorem trel1_inv {R : ∀ t, PArg Reg Empty ArmCond t → Val t → Prop} {t : Ty}
    {pa : PArg Reg Empty ArmCond t} {v : Val t} (h : TRel R (as := [t]) (pa, ()) (v, ())) :
    R t pa v := by
  cases h with | cons hx _ => exact hx

theorem trel2_inv {R : ∀ t, PArg Reg Empty ArmCond t → Val t → Prop} {t₁ t₂ : Ty}
    {pa : PArg Reg Empty ArmCond t₁} {pb : PArg Reg Empty ArmCond t₂}
    {va : Val t₁} {vb : Val t₂} (h : TRel R (as := [t₁, t₂]) (pa, pb, ()) (va, vb, ())) :
    R t₁ pa va ∧ R t₂ pb vb := by
  cases h with | cons hx h2 => cases h2 with | cons hy _ => exact ⟨hx, hy⟩

theorem trel3_inv {R : ∀ t, PArg Reg Empty ArmCond t → Val t → Prop} {t₁ t₂ t₃ : Ty}
    {pa : PArg Reg Empty ArmCond t₁} {pb : PArg Reg Empty ArmCond t₂} {pc : PArg Reg Empty ArmCond t₃}
    {va : Val t₁} {vb : Val t₂} {vc : Val t₃}
    (h : TRel R (as := [t₁, t₂, t₃]) (pa, pb, pc, ()) (va, vb, vc, ())) :
    R t₁ pa va ∧ R t₂ pb vb ∧ R t₃ pc vc := by
  cases h with | cons hx h2 => cases h2 with | cons hy h3 => cases h3 with | cons hz _ => exact ⟨hx, hy, hz⟩

theorem armFrame_scratch_to_dst {s s' : MachineData} {d : XReg} {clob : FlagMask}
    (h : armMach.Frame armCondReads s s' armScratch [] clob) :
    armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob :=
  h.weaken (fun _ hr => List.mem_cons_of_mem _ hr) (fun v => v.elim)
    (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp)

theorem armFrame_scratch_trans {s₁ s₂ s₃ : MachineData}
    (h1 : armMach.Frame armCondReads s₁ s₂ armScratch [] maskNone)
    (h2 : armMach.Frame armCondReads s₂ s₃ armScratch [] maskNone) :
    armMach.Frame armCondReads s₁ s₃ armScratch [] maskNone :=
  (h1.trans h2).weaken
    (fun _ hr => by simp only [List.mem_append] at hr; rcases hr with h | h <;> exact h)
    (fun v => v.elim) rfl

theorem armFrame_scratch_wr {s s₁ s₂ : MachineData} {d : XReg}
    (h1 : armMach.Frame armCondReads s s₁ armScratch [] maskNone)
    (h2 : armMach.Frame armCondReads s₁ s₂ (.reg d :: armScratch) [] maskNone) :
    armMach.Frame armCondReads s s₂ (.reg d :: armScratch) [] maskNone :=
  ((armFrame_scratch_to_dst (d := d) h1).trans h2).weaken
    (fun r hr => by
      simp only [List.mem_append, List.mem_cons, armScratch, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h) | (h | h | h) <;> simp [h])
    (fun v => v.elim) rfl

theorem armFrame_scratch2 {s s₁ s₂ : MachineData}
    (h1 : armMach.Frame armCondReads s s₁ [.reg .X16] [] maskNone)
    (h2 : armMach.Frame armCondReads s₁ s₂ [.reg .X17] [] maskNone) :
    armMach.Frame armCondReads s s₂ armScratch [] maskNone :=
  (h1.trans h2).weaken (fun _ hx => hx) (fun v => v.elim) rfl

theorem x16_mem_scratch : XRegOrSp.reg .X16 ∈ armScratch := by simp [armScratch]
theorem x17_mem_scratch : XRegOrSp.reg .X17 ∈ armScratch := by simp [armScratch]

theorem armScratch_cons [Host] {d : Directive} {p : _root_.Program}
    {s₀ s : MachineData} {x : XReg} {v : BitVec 64} {Q : MachineData → Prop}
    (hx : XRegOrSp.reg x ∈ armScratch) (hd : s.dmem = s₀.dmem)
    (hfr : armMach.Frame armCondReads s₀ s armScratch [] maskNone)
    (hd_wp : _root_.Program.wp [d] (fun s' => s' = wr s x v) (fun _ _ => False) s)
    (hk : ∀ s' : MachineData, s' = wr s x v → s'.dmem = s₀.dmem →
      armMach.Frame armCondReads s₀ s' armScratch [] maskNone →
      _root_.Program.wp p Q (fun _ _ => False) s') :
    _root_.Program.wp (d :: p) Q (fun _ _ => False) s :=
  armWp_cons hd_wp fun s' hs' => hk s' hs' (hs' ▸ hd) (hs' ▸ armFrame_scratch_trans hfr (frame_wr x v hx maskNone))

theorem armWrDst_of_eq [Host] {c : List Directive} {n : Nat} (hn : n ≤ 64) (d : XReg)
    {s : MachineData} {val64 : BitVec 64} {target : BitVec n}
    (hwp : _root_.Program.wp c (fun s' => s' = wr s d val64) (fun _ _ => False) s)
    (hval : val64.setWidth n = target) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) target ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ => False) s :=
  armWp_mono hwp fun s' hs' => by
    subst hs'; exact ⟨⟨hn, by simpa [get_wr_same] using hval⟩, rfl, frame_wr d _ List.mem_cons_self maskNone⟩

theorem armWrDst_after_scratch [Host] {c : List Directive} {n : Nat} (hn : n ≤ 64) (d : XReg)
    {s s₂ : MachineData} {val64 : BitVec 64} {target : BitVec n}
    (hwp : _root_.Program.wp c (fun s' => s' = wr s₂ d val64) (fun _ _ => False) s₂)
    (hd₂ : s₂.dmem = s.dmem)
    (hfr₂ : armMach.Frame armCondReads s s₂ armScratch [] maskNone)
    (hval : val64.setWidth n = target) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) target ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ => False) s₂ :=
  armWp_mono hwp fun s' hs' => by
    subst hs'; exact ⟨⟨hn, by simpa [get_wr_same] using hval⟩, hd₂,
      armFrame_scratch_wr hfr₂ (frame_wr d _ List.mem_cons_self maskNone)⟩

theorem armImmPool_wp [Host] {n : Nat} (hn : n ≤ 64) (d : XReg) (s : MachineData) (v : BitVec n) :
    _root_.Program.wp [armLdrPoolBv d (v.setWidth 64)] (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) v ∧ armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ => False) s :=
  armWrDst_of_eq hn d (armLdrPoolBv_wp d (v.setWidth 64) s)
    (by rw [BitVec.setWidth_setWidth_of_le v hn, BitVec.setWidth_eq])

theorem getLsbD_shiftMask_ge {n i : Nat} (hn : n = 8 ∨ n = 16) (hi : ¬ i < n) :
    (BitVec.ofNat 32 (n - 1)).getLsbD i = false := by
  change Nat.testBit ((n - 1) % 2 ^ 32) i = false
  rcases hn with rfl | rfl
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 7 % 2 ^ 32 < 2 ^ 8)
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)))
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 15 % 2 ^ 32 < 2 ^ 16)
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)))

theorem armArgs2_wp [Host] {n₁ n₂ : Nat} (hn₁ : n₁ ≤ 64) (hn₂ : n₂ ≤ 64)
    {pa : PArg Reg Empty ArmCond (.bits n₁)} {pb : PArg Reg Empty ArmCond (.bits n₂)}
    {va : BitVec n₁} {vb : BitVec n₂} {s : MachineData}
    {ca cb : List Directive} {ra rb : XReg}
    (ha : armArgIn .X16 pa = some (ca, ra)) (hb : armArgIn .X17 pb = some (cb, rb))
    (hpa : armMach.PArgHolds s (.bits n₁) pa va) (hpb : armMach.PArgHolds s (.bits n₂) pb vb)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch) :
    _root_.Program.wp (ca ++ cb) (fun s' =>
      (s'.regs.getXReg ra).toBitVec.setWidth n₁ = va ∧
      (s'.regs.getXReg rb).toBitVec.setWidth n₂ = vb ∧
      ra ≠ .X17 ∧ rb ≠ .X16 ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' armScratch [] maskNone) (fun _ _ => False) s := by
  have hneA : ra ≠ .X17 := by
    cases pa with
    | vec vr => exact vr.elim
    | imm _ => simp [armArgIn] at ha; rcases ha with ⟨rfl, rfl⟩; decide
    | gpr r => cases r with
      | SP => simp [armArgIn] at ha
      | reg x =>
        simp [armArgIn] at ha; rcases ha with ⟨rfl, rfl⟩
        exact (xreg_ne_scratch_of_not_mem (hga (.reg x) (by simp [PArg.gprs]))).2
  have hneB : rb ≠ .X16 := by
    cases pb with
    | vec vr => exact vr.elim
    | imm _ => simp [armArgIn] at hb; rcases hb with ⟨rfl, rfl⟩; decide
    | gpr r => cases r with
      | SP => simp [armArgIn] at hb
      | reg x =>
        simp [armArgIn] at hb; rcases hb with ⟨rfl, rfl⟩
        exact (xreg_ne_scratch_of_not_mem (hgb (.reg x) (by simp [PArg.gprs]))).1
  refine armWp_append (armArgIn_wp hn₁ ha hpa) ?_
  rintro s₁ ⟨hra₁, hdmem₁, hst₁, hfr₁⟩
  have hpb₁ : armMach.PArgHolds s₁ (.bits n₂) pb vb :=
    Machine.PArgHolds.frame hfr₁ hpb (fun r hr => by
      subst hr; have hg := hgb r (by simp [PArg.gprs])
      cases r with | SP => intro h; simp at h | reg x => simp [armScratch] at hg ⊢; exact hg.1)
      (fun v => v.elim) (fun _ ht => nomatch ht)
  refine armWp_mono (armArgIn_wp hn₂ hb hpb₁) ?_
  rintro s₂ ⟨hrb₂, hdmem₂, hst₂, hfr₂⟩
  have hra₂ : (s₂.regs.getXReg ra).toBitVec.setWidth n₁ = va := by
    cases pa with
    | vec vr => exact vr.elim
    | imm _ =>
      simp [armArgIn] at ha; rcases ha with ⟨rfl, rfl⟩
      have h16 := hfr₂.1 (.reg .X16) (fun h => by simp at h)
      simpa [get_reg] using (congrArg (BitVec.setWidth n₁) h16).trans hra₁
    | gpr r => cases r with
      | SP => simp [armArgIn] at ha
      | reg x =>
        simp [armArgIn] at ha; rcases ha with ⟨rfl, rfl⟩
        have hx := hfr₂.1 (.reg x) (fun h => (xreg_ne_scratch_of_not_mem
          (hga (.reg x) (by simp [PArg.gprs]))).2 (by simpa using h))
        simpa [get_reg] using (congrArg (BitVec.setWidth n₁) hx).trans hra₁
  exact ⟨hra₂, hrb₂, hneA, hneB, hdmem₂.trans hdmem₁, hst₂.trans hst₁, armFrame_scratch2 hfr₁ hfr₂⟩

theorem armBoolArgs2_wp [Host]
    {pa pb : PArg Reg Empty ArmCond .bool} {va vb : Bool} {s : MachineData}
    {ca cb : List Directive} {ra rb : XReg}
    (ha : armBoolArgIn .X16 pa = some (ca, ra)) (hb : armBoolArgIn .X17 pb = some (cb, rb))
    (hpa : armMach.PArgHolds s .bool pa va) (hpb : armMach.PArgHolds s .bool pb vb)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch) :
    _root_.Program.wp (ca ++ cb) (fun s' =>
      (s'.regs.getXReg ra).toBitVec.setWidth 8 = BitVec.ofNat 8 va.toNat ∧
      (s'.regs.getXReg rb).toBitVec.setWidth 8 = BitVec.ofNat 8 vb.toNat ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' armScratch [] maskNone) (fun _ _ => False) s := by
  refine armWp_append (armBoolArgIn_wp ha hpa) ?_
  rintro s₁ ⟨hra₁, hdmem₁, hst₁, hfr₁⟩
  have hpb₁ : armMach.PArgHolds s₁ .bool pb vb :=
    Machine.PArgHolds.frame hfr₁ hpb (fun r hr => by
      subst hr; have hg := hgb r (by simp [PArg.gprs])
      cases r with | SP => intro h; simp at h | reg x => simp [armScratch] at hg ⊢; exact hg.1)
      (fun v => v.elim) (fun c _ _ => by simp [maskNone])
  refine armWp_mono (armBoolArgIn_wp hb hpb₁) ?_
  rintro s₂ ⟨hrb₂, hdmem₂, hst₂, hfr₂⟩
  have hra₂ : (s₂.regs.getXReg ra).toBitVec.setWidth 8 = BitVec.ofNat 8 va.toNat := by
    cases pa with
    | vec vr => exact vr.elim
    | imm _ | flag _ =>
      simp [armBoolArgIn] at ha; rcases ha with ⟨rfl, rfl⟩
      have h16 := hfr₂.1 (.reg .X16) (fun h => by simp at h)
      simpa [get_reg] using (congrArg (BitVec.setWidth 8) h16).trans hra₁
    | gpr r => cases r with
      | SP => simp [armBoolArgIn] at ha
      | reg x =>
        simp [armBoolArgIn] at ha; rcases ha with ⟨rfl, rfl⟩
        have hx := hfr₂.1 (.reg x) (fun h => (xreg_ne_scratch_of_not_mem
          (hga (.reg x) (by simp [PArg.gprs]))).2 (by simpa using h))
        simpa [get_reg] using (congrArg (BitVec.setWidth 8) hx).trans hra₁
  exact ⟨hra₂, hrb₂, hdmem₂.trans hdmem₁, hst₂.trans hst₁, armFrame_scratch2 hfr₁ hfr₂⟩

theorem armExt32_wp [Host] (signed : Bool) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 32)
    (d src : XReg) (s : MachineData) (x : BitVec n)
    (hx : (s.regs.getXReg src).toBitVec.setWidth n = x) :
    _root_.Program.wp [armExt32 signed n d src] (fun s' =>
      s' = wr s d ((if signed then x.signExtend 32 else x.setWidth 32).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp P hk => by
    cases signed
    · simp only [armExt32, Bool.false_eq_true, ↓reduceIte, t_step_simp]
      rw [evalUBFM_low (w := .W32) _ hn0 hn]
      simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_setWidth_of_le _ hn, hx]; exact hk _ rfl
    · simp only [armExt32, ↓reduceIte, t_step_simp]
      rw [evalSBFM_low (w := .W32) _ hn0 hn]
      simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_setWidth_of_le _ hn, hx]; exact hk _ rfl

theorem armDstWr_mono [Host] {c : List Directive} {s : MachineData}
    {d : XReg} {t : Ty} {v : Val t} {fClob : FlagMask}
    (h : _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) t v ∧ s'.dmem = s.dmem ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] fClob) (fun _ _ => False) s) :
    _root_.Program.wp c (fun s' =>
      (∃ rvs : Tup Val [t], rvs = (v, ()) ∧
        TRel (armMach.PDstHolds s') ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond t), ()) rvs) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] fClob) (fun _ _ => False) s :=
  armWp_mono h fun _ ⟨hv, hd, hfr⟩ => ⟨⟨(v, ()), rfl, .cons hv .nil⟩, hd, hfr⟩

theorem armMovRegDir_wp [Host] (w : RegWidth) (d rx : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.ORR_s (zr d w) (xzr w) (sh rx))]
      (fun s' => s' = wr s d (((s.regs.getXReg rx).toBitVec.setWidth w.bits).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases w <;>
      (simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero, BitVec.zero_or,
         RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl)

private theorem armUbfmLow64_wp [Host] {m : Nat} (hm0 : 0 < m) (hm : m ≤ 64)
    (d rx : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.UBFM (zr d .W64) (zr rx .W64) 0 (m - 1))]
      (fun s' => s' = wr s d (((s.regs.getXReg rx).toBitVec.setWidth m).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    simp only [t_step_simp]; rw [evalUBFM_low (w := .W64) (n := m) _ hm0 hm]
    simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl

private theorem armSbfmLow64_wp [Host] {m : Nat} (hm0 : 0 < m) (hm : m ≤ 64)
    (d rx : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.SBFM (zr d .W64) (zr rx .W64) 0 (m - 1))]
      (fun s' => s' = wr s d (((s.regs.getXReg rx).toBitVec.setWidth m).signExtend 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    simp only [t_step_simp]; rw [evalSBFM_low (w := .W64) (n := m) _ hm0 hm]
    simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl

/-! ## 2. Boolean, conversion, unary, and binary ALU proofs -/

theorem armBoolOp_wp [Host] {sig : List Ty} (code : OpCode sig [.bool])
    (pas : Tup (PArg Reg Empty ArmCond) sig) (d : XReg) {c : List Directive} {clob : FlagMask}
    {vs : Tup Val sig} {P : Tup Val [.bool] → Prop} {s : MachineData}
    (hc : armBoolOp code pas d = some (c, clob)) (_ : XRegOrSp.reg d ∉ armScratch)
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ armScratch)
    (hrel : TRel (armMach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    _root_.Program.wp c (fun s' =>
      (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond .bool), ()) rvs) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  cases code with
  | copy _ =>
    rcases pas with ⟨pa, _⟩; rcases vs with ⟨b, _⟩
    have hpa := trel1_inv hrel; simp only [OpCode.wp] at hwp
    cases pa with
    | vec vr => exact vr.elim
    | gpr r => cases r with
      | SP => delta armBoolOp at hc; cases hc
      | reg x =>
        delta armBoolOp at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
        refine armWp_mono (armMovRegDir_wp .W32 d x s) ?_
        rintro s' rfl
        refine ⟨⟨(b, ()), hwp, .cons ?_ .nil⟩, rfl, frame_wr d _ List.mem_cons_self maskNone⟩
        simp only [Machine.PDstHolds, GprHolds, get_wr_same, RegWidth.bits, MemWidth.bits]
        simpa [Machine.PArgHolds, GprHolds, get_reg,
          BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
          BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)] using hpa
    | imm cb =>
      delta armBoolOp at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
      simp only [Machine.PArgHolds] at hpa; subst hpa
      refine armWp_mono (armLdrPoolBv_wp d (BitVec.ofNat 64 cb.toNat) s) ?_
      rintro s' rfl
      refine ⟨⟨(cb, ()), hwp, .cons ?_ .nil⟩, rfl, frame_wr d _ List.mem_cons_self maskNone⟩
      simp only [Machine.PDstHolds, GprHolds, get_wr_same]; cases cb <;> rfl
    | flag cond =>
      delta armBoolOp at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
      simp only [Machine.PArgHolds] at hpa
      refine armWp_mono (armCset64_wp d cond s) ?_
      rintro s' rfl
      refine ⟨⟨(b, ()), hwp, .cons ?_ .nil⟩, rfl, frame_wr d _ List.mem_cons_self maskNone⟩
      simp only [Machine.PDstHolds, GprHolds, get_wr_same, hpa]; cases b <;> rfl
  | not _ =>
    rcases pas with ⟨pa, _⟩; rcases vs with ⟨a, _⟩
    have hpa := trel1_inv hrel; simp only [OpCode.wp] at hwp
    change (armBoolArgIn .X16 pa >>= fun x =>
      some (x.1 ++ [ins (.EOR_i (.low (.reg d) .W32) (zr x.2 .W32) (.int64 1))], maskNone)) = some (c, clob) at hc
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨⟨ca, ra⟩, ha, rfl, rfl⟩
    refine armWp_append (armBoolArgIn_wp ha hpa) ?_
    rintro s₁ ⟨hra₁, hd₁, _, hfr₁⟩
    refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp, ConstExpr.interp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, RegWidth.bits]
      exact hk _ rfl) ?_
    rintro s' rfl
    refine ⟨⟨(!a, ()), hwp, .cons ?_ .nil⟩, hd₁,
      armFrame_scratch_wr (hfr₁.weaken (fun _ hr => by simp at hr ⊢; exact Or.inl hr) (fun v => v.elim) rfl)
        (frame_wr d _ List.mem_cons_self maskNone)⟩
    simp only [Machine.PDstHolds, GprHolds, get_reg, Reg64s.getXReg_setXReg_same]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), setWidth8_xor,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), hra₁]
    cases a <;> decide
  | and _ | or _ | xor _ =>
    rcases pas with ⟨pa, pb, _⟩; rcases vs with ⟨a, b, _⟩
    have ⟨hpa, hpb⟩ := trel2_inv hrel; simp only [OpCode.wp] at hwp
    first
    | change (armBoolArgIn .X16 pa >>= fun x => armBoolArgIn .X17 pb >>= fun y =>
        some (x.1 ++ y.1 ++ [ins (.AND_s (zr d .W32) (zr x.2 .W32) (sh y.2))], maskNone)) = some (c, clob) at hc
    | change (armBoolArgIn .X16 pa >>= fun x => armBoolArgIn .X17 pb >>= fun y =>
        some (x.1 ++ y.1 ++ [ins (.ORR_s (zr d .W32) (zr x.2 .W32) (sh y.2))], maskNone)) = some (c, clob) at hc
    | change (armBoolArgIn .X16 pa >>= fun x => armBoolArgIn .X17 pb >>= fun y =>
        some (x.1 ++ y.1 ++ [ins (.EOR_s (zr d .W32) (zr x.2 .W32) (sh y.2))], maskNone)) = some (c, clob) at hc
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl, rfl⟩
    have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr =>
      hargs r (by cases pa <;> simp [PArg.gprs, tupArgGprs] at hr ⊢; exact Or.inl hr)
    have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr =>
      hargs r (by cases pa <;> cases pb <;> simp [PArg.gprs, tupArgGprs] at hr ⊢ <;>
        first | exact hr | exact Or.inl hr | exact Or.inr hr)
    refine armWp_append (armBoolArgs2_wp ha hb hpa hpb hga hgb) ?_
    rintro s₂ ⟨hra, hrb, hd₂, _, hfr₂⟩
    refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero]
      exact hk _ rfl) ?_
    rintro s' rfl
    refine ⟨⟨(_, ()), hwp, .cons ?_ .nil⟩, hd₂, armFrame_scratch_wr hfr₂ (frame_wr d _ List.mem_cons_self maskNone)⟩
    simp only [Machine.PDstHolds, GprHolds, get_reg, Reg64s.getXReg_setXReg_same]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    first | rw [setWidth8_and] | rw [setWidth8_or] | rw [setWidth8_xor]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), hra,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), hrb]
    cases a <;> cases b <;> decide
  | _ => delta armBoolOp at hc; cases hc

theorem armCopyBits_wp [Host] {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    {pa : PArg Reg Empty ArmCond (.bits n)} {v : BitVec n} (d : XReg) {s : MachineData}
    {c : List Directive} {clob : FlagMask}
    (hc : armCopyBits n pa d = some (c, clob)) (hp : armMach.PArgHolds s (.bits n) pa v) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) v ∧ armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  have hn64 := mem_armWidths_le_64 hn
  have hnw := mem_armWidths_le_armWidth hn
  cases pa with
  | vec vr => exact vr.elim
  | imm cv =>
    simp only [armCopyBits, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
    exact armImmPool_wp hn64 d s cv
  | gpr r => cases r with
    | SP => simp [armCopyBits] at hc
    | reg rx =>
      simp only [armCopyBits, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      have hrx : (s.regs.getXReg rx).toBitVec.setWidth n = v := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
      exact armWrDst_of_eq hn64 d (armMovRegDir_wp (armWidthOf n) d rx s)
        (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_setWidth_of_le _ hnw, hrx])

theorem armZextOp_wp [Host] {m n : Nat} (pa : PArg Reg Empty ArmCond (.bits m))
    (d : XReg) {va : BitVec m} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : armZextOp m n pa d = some (c, clob))
    (hp : armMach.PArgHolds s (.bits m) pa va) (hle : m ≤ n) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.setWidth n) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armZextOp] at hc; split at hc
  · simp at hc
  · rename_i hok; replace hok := not_not_eq_true hok
    simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, Nat.ble_eq] at hok
    rcases hok with ⟨⟨hm, hn⟩, _⟩
    have hn64 := mem_armWidths_le_64 hn
    cases pa with
    | vec vr => exact vr.elim
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      exact armImmPool_wp hn64 d s _
    | gpr r => cases r with
      | SP => simp at hc
      | reg rx =>
        have hrx : (s.regs.getXReg rx).toBitVec.setWidth m = va := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
        rcases mem_armWidths hm with rfl | rfl | rfl | rfl
        · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact armWrDst_of_eq hn64 d (armUbfmLow64_wp (m := 8) (by decide) (by decide) d rx s)
            (by rw [BitVec.setWidth_setWidth_of_le _ hn64, hrx])
        · simp only [show (16 == 8) = false from rfl, Bool.false_eq_true, ↓reduceIte,
            beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact armWrDst_of_eq hn64 d (armUbfmLow64_wp (m := 16) (by decide) (by decide) d rx s)
            (by rw [BitVec.setWidth_setWidth_of_le _ hn64, hrx])
        · simp only [show (32 == 8) = false from rfl, show (32 == 16) = false from rfl,
            Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact armWrDst_of_eq hn64 d (armMovRegDir_wp .W32 d rx s)
            (by simp only [RegWidth.bits]; rw [BitVec.setWidth_setWidth_of_le _ hn64, hrx])
        · simp only [show (64 == 8) = false from rfl, show (64 == 16) = false from rfl,
            show (64 == 32) = false from rfl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          have hn64' : n = 64 := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> omega
          subst hn64'
          exact armWrDst_of_eq hn64 d (armMovRegDir_wp .W64 d rx s) (by simpa [BitVec.setWidth_eq] using hrx)

theorem armSextOp_wp [Host] {m n : Nat} (pa : PArg Reg Empty ArmCond (.bits m))
    (d : XReg) {va : BitVec m} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : armSextOp m n pa d = some (c, clob))
    (hp : armMach.PArgHolds s (.bits m) pa va) (hle : m ≤ n) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.signExtend n) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armSextOp] at hc; split at hc
  · simp at hc
  · rename_i hok; replace hok := not_not_eq_true hok
    simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, Nat.ble_eq] at hok
    rcases hok with ⟨⟨hm, hn⟩, _⟩
    have hn64 := mem_armWidths_le_64 hn
    cases pa with
    | vec vr => exact vr.elim
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      exact armImmPool_wp hn64 d s _
    | gpr r => cases r with
      | SP => simp at hc
      | reg rx =>
        have hrx : (s.regs.getXReg rx).toBitVec.setWidth m = va := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
        have hse_trunc : (va.signExtend 64).setWidth n = va.signExtend n := by
          apply BitVec.eq_of_getLsbD_eq; intro i hi
          simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
            show (i : Nat) < 64 by omega, decide_true, Bool.true_and]
          try (by_cases hm_lt : (i : Nat) < m <;> simp [hm_lt, show (i : Nat) < 64 by omega])
        rcases mem_armWidths hm with rfl | rfl | rfl | rfl
        · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact armWrDst_of_eq hn64 d (armSbfmLow64_wp (m := 8) (by decide) (by decide) d rx s)
            (by rw [hrx, hse_trunc])
        · simp only [show (16 == 8) = false from rfl, Bool.false_eq_true, ↓reduceIte,
            beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact armWrDst_of_eq hn64 d (armSbfmLow64_wp (m := 16) (by decide) (by decide) d rx s)
            (by rw [hrx, hse_trunc])
        · simp only [show (32 == 8) = false from rfl, show (32 == 16) = false from rfl,
            Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact armWrDst_of_eq hn64 d (armSbfmLow64_wp (m := 32) (by decide) (by decide) d rx s)
            (by rw [hrx, hse_trunc])
        · simp only [show (64 == 8) = false from rfl, show (64 == 16) = false from rfl,
            show (64 == 32) = false from rfl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          have hn64' : n = 64 := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> omega
          subst hn64'
          exact armWrDst_of_eq hn64 d (armMovRegDir_wp .W64 d rx s) (by simpa [BitVec.setWidth_eq] using hrx)

theorem armTruncOp_wp [Host] {m n : Nat} (pa : PArg Reg Empty ArmCond (.bits m))
    (d : XReg) {va : BitVec m} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : armTruncOp m n pa d = some (c, clob))
    (hp : armMach.PArgHolds s (.bits m) pa va) (hle : n ≤ m) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.setWidth n) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armTruncOp] at hc; split at hc
  · simp at hc
  · rename_i hok; replace hok := not_not_eq_true hok
    simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, Nat.ble_eq] at hok
    rcases hok with ⟨⟨_, hn⟩, _⟩
    have hn64 := mem_armWidths_le_64 hn
    have hnw := mem_armWidths_le_armWidth hn
    cases pa with
    | vec vr => exact vr.elim
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      exact armImmPool_wp hn64 d s _
    | gpr r => cases r with
      | SP => simp at hc
      | reg rx =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        have hrx : (s.regs.getXReg rx).toBitVec.setWidth m = va := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
        exact armWrDst_of_eq hn64 d (armMovRegDir_wp (armWidthOf n) d rx s) (by
          rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_setWidth_of_le _ hnw,
            ← BitVec.setWidth_setWidth_of_le (s.regs.getXReg rx).toBitVec hle, hrx])

theorem armOfBoolOp_wp [Host] {n : Nat} (pa : PArg Reg Empty ArmCond .bool)
    (d : XReg) {b : Bool} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : armOfBoolOp n pa d = some (c, clob)) (hp : armMach.PArgHolds s .bool pa b) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (BitVec.ofNat n b.toNat) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armOfBoolOp] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hn' := mem_armWidths hn
    cases pa with
    | vec vr => exact vr.elim
    | gpr r => cases r with
      | SP => simp at hc
      | reg rx =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        have hrx : (s.regs.getXReg rx).toBitVec.setWidth 8 = BitVec.ofNat 8 b.toNat := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hp
        exact armWrDst_of_eq hn64 d (armUbfmLow64_wp (m := 8) (by decide) (by decide) d rx s) (by
          rw [BitVec.setWidth_setWidth_of_le _ hn64, hrx]
          cases b <;> rcases hn' with rfl | rfl | rfl | rfl <;> decide)
    | imm cb =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      have hsw : (BitVec.ofNat n cb.toNat).setWidth 64 = BitVec.ofNat 64 cb.toNat := by
        cases cb <;> rcases hn' with rfl | rfl | rfl | rfl <;> rfl
      rw [← hsw]; exact armImmPool_wp hn64 d s (BitVec.ofNat n cb.toNat)
    | flag cond =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp
      exact armWrDst_of_eq hn64 d (armCset64_wp d cond s) (by
        rw [hp]; cases b <;> rcases hn' with rfl | rfl | rfl | rfl <;> decide)

def armBinEval (k : ArmBinK) {m : Nat} : BitVec m → BitVec m → BitVec m :=
  match k with
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·)
  | .and => (· &&& ·) | .or => (· ||| ·) | .xor => (· ^^^ ·)

theorem armBinDir_wp [Host] (k : ArmBinK) (w : RegWidth) (d ra rb : XReg) (s : MachineData) :
    _root_.Program.wp [armBinDir k w d ra rb] (fun s' =>
      s' = wr s d ((armBinEval k
        ((s.regs.getXReg ra).toBitVec.setWidth w.bits)
        ((s.regs.getXReg rb).toBitVec.setWidth w.bits)).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases k <;> cases w <;>
      (simp only [armBinDir, t_step_simp, Int64.toInt_zero, Int.toNat_zero,
         BitVec.shiftLeft_zero, BitVec.add_zero, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq];
       exact hk _ rfl)

private theorem armAddSubImm_wp [Host] {n : Nat} (_hn : n ≤ 64) (isSub : Bool) (w : RegWidth)
    (d rx : XReg) (c : BitVec n) (hc : c.toNat < 4096) (s : MachineData) :
    let ei : ExtOrImmReg := .imm { imm := .int64 (Int64.ofNat c.toNat), shift := .S0 }
    _root_.Program.wp [ins (if isSub then .SUB_e (.low (.reg d) w) (.low (.reg rx) w) ei
      else .ADD_e (.low (.reg d) w) (.low (.reg rx) w) ei)]
      (fun s' => s' = wr s d ((if isSub then (s.regs.getXReg rx).toBitVec.setWidth w.bits - c.setWidth w.bits
        else (s.regs.getXReg rx).toBitVec.setWidth w.bits + c.setWidth w.bits).setWidth 64))
      (fun _ _ => False) s := by
  intro ei
  have himm : BitVec.ofInt w.bits (Int64.ofNat c.toNat).toInt = c.setWidth w.bits := by
    rw [Int64.toInt_ofNat_of_lt (by omega : c.toNat < 2 ^ 63), BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq; simp
  cases isSub <;> cases w <;>
    exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [ei, ↓reduceIte, Bool.false_eq_true, t_step_simp]
      rw [himm]; simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl

theorem armBinOp_wp [Host] (k : ArmBinK) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb : BitVec n} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : armBinOp k n pa pb d = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (armBinEval k va vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armBinOp] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hnw := mem_armWidths_le_armWidth hn
    have hset : ∀ x y : BitVec (armWidthOf n).bits,
        x.setWidth n = va → y.setWidth n = vb →
        ((armBinEval k x y).setWidth 64).setWidth n = armBinEval k va vb := fun x y hx hy => by
      rw [BitVec.setWidth_setWidth_of_le _ hn64]
      rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> cases k <;> simp only [armBinEval] at hx hy ⊢
      all_goals first
        | (subst hx hy; exact setWidth_sub_of_le hnw x y)
        | (rw [← hx, ← hy]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul,
            Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)])
        | (subst hx hy; apply BitVec.eq_of_getLsbD_eq; intro i hi;
           simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or,
             BitVec.getLsbD_xor, hi, armWidthOf])
    have fallback : ∀ {ca ra cb rb}, armArgIn .X16 pa = some (ca, ra) → armArgIn .X17 pb = some (cb, rb) →
        c = ca ++ cb ++ [armBinDir k (armWidthOf n) d ra rb] → clob = maskNone →
        _root_.Program.wp c (fun s' => GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (armBinEval k va vb) ∧
          armMach.mem s' = armMach.mem s ∧ armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob)
          (fun _ _ => False) s := by
      intro ca ra cb rb ha hb hceq hclob; subst hceq; subst hclob
      refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
      rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
      exact armWrDst_after_scratch hn64 d (armBinDir_wp k (armWidthOf n) d ra rb s₂) hd₂ hfr₂
        (hset _ _ (by rwa [BitVec.setWidth_setWidth_of_le _ hnw]) (by rwa [BitVec.setWidth_setWidth_of_le _ hnw]))
    have imm12Step : ∀ (isSub isSwap : Bool) (_hvalid : isSub = false ∨ isSwap = false)
        (rx : XReg) (imm : BitVec n) {ei : ExtOrImmReg},
        armImm12? imm = some ei → (if isSub then k = .sub else k = .add) →
        (if isSwap then (armMach.PArgHolds s (.bits n) (.imm imm) va ∧ armMach.PArgHolds s (.bits n) (.gpr (.reg rx)) vb)
         else (armMach.PArgHolds s (.bits n) (.gpr (.reg rx)) va ∧ armMach.PArgHolds s (.bits n) (.imm imm) vb)) →
        c = [ins (if isSub then .SUB_e (.low (.reg d) (armWidthOf n)) (.low (.reg rx) (armWidthOf n)) ei
                  else .ADD_e (.low (.reg d) (armWidthOf n)) (.low (.reg rx) (armWidthOf n)) ei)] →
        clob = maskNone →
        _root_.Program.wp c (fun s' => GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (armBinEval k va vb) ∧
          armMach.mem s' = armMach.mem s ∧ armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob)
          (fun _ _ => False) s := by
      intro isSub isSwap hvalid rx imm ei hei hk' hps hc' hclob
      obtain ⟨rfl, hlt, _⟩ := armImm12_some hn64 hei; subst hc'; subst hclob
      refine armWrDst_of_eq hn64 d (armAddSubImm_wp hn64 isSub (armWidthOf n) d rx imm hlt s) ?_
      cases isSub <;> simp only [↓reduceIte, Bool.false_eq_true] at hk' ⊢ <;> subst hk'
      · cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hps
        · have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.1.2
          have him : imm = vb := by simpa [Machine.PArgHolds] using hps.2
          exact hset _ _ (by rw [BitVec.setWidth_setWidth_of_le _ hnw, hra])
            (by rw [BitVec.setWidth_setWidth_of_le imm hnw, BitVec.setWidth_eq, him])
        · have hrb : (s.regs.getXReg rx).toBitVec.setWidth n = vb := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.2.2
          have him : imm = va := by simpa [Machine.PArgHolds] using hps.1
          rw [BitVec.add_comm ((s.regs.getXReg rx).toBitVec.setWidth _) (imm.setWidth _)]
          exact hset _ _ (by rw [BitVec.setWidth_setWidth_of_le imm hnw, BitVec.setWidth_eq, him])
            (by rw [BitVec.setWidth_setWidth_of_le _ hnw, hrb])
      · cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hps
        · have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.1.2
          have him : imm = vb := by simpa [Machine.PArgHolds] using hps.2
          exact hset _ _ (by rw [BitVec.setWidth_setWidth_of_le _ hnw, hra])
            (by rw [BitVec.setWidth_setWidth_of_le imm hnw, BitVec.setWidth_eq, him])
        · rcases hvalid with h | h <;> cases h
    have hfbRun : (armArgIn .X16 pa >>= fun a => armArgIn .X17 pb >>= fun b =>
        some (a.1 ++ b.1 ++ [armBinDir k (armWidthOf n) d a.2 b.2], maskNone)) = some (c, clob) → _root_.Program.wp c
        (fun s' => GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (armBinEval k va vb) ∧
          armMach.mem s' = armMach.mem s ∧ armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob)
          (fun _ _ => False) s := fun h => by
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl, rfl⟩; exact fallback ha hb rfl rfl
    cases k with
    | mul | and | or | xor => dsimp only at hc; exact hfbRun hc
    | add =>
      cases pa with
      | vec vr => exact vr.elim
      | imm ca => cases pb with
        | vec vr => exact vr.elim
        | imm _ => dsimp only at hc; exact hfbRun hc
        | gpr r => cases r with
          | SP => dsimp only at hc; simp [armArgIn] at hc
          | reg rb =>
            dsimp only at hc
            rcases option_none_or_some (armImm12? ca) with hnone | ⟨ei, hei⟩
            · simp only [hnone, bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
              rcases hc with ⟨⟨ca', ra⟩, ha, rfl, rfl⟩
              exact fallback (cb := []) (rb := rb) ha rfl (by simp) rfl
            · simp only [hei, Option.some.injEq, Prod.mk.injEq] at hc
              exact imm12Step false true (Or.inl rfl) rb ca hei rfl ⟨hpa, hpb⟩ hc.1.symm hc.2.symm
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgIn] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ => dsimp only at hc; exact hfbRun hc
          | imm cb =>
            dsimp only at hc
            rcases option_none_or_some (armImm12? cb) with hnone | ⟨ei, hei⟩
            · simp only [hnone, bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
              rcases hc with ⟨⟨cb', rb⟩, hb, rfl, rfl⟩
              exact fallback (ca := []) (ra := ra) rfl hb rfl rfl
            · simp only [hei, Option.some.injEq, Prod.mk.injEq] at hc
              exact imm12Step false false (Or.inl rfl) ra cb hei rfl ⟨hpa, hpb⟩ hc.1.symm hc.2.symm
    | sub =>
      cases pa with
      | vec vr => exact vr.elim
      | imm _ => dsimp only at hc; exact hfbRun hc
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgIn] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ => dsimp only at hc; exact hfbRun hc
          | imm cb =>
            dsimp only at hc
            rcases option_none_or_some (armImm12? cb) with hnone | ⟨ei, hei⟩
            · simp only [hnone, bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
              rcases hc with ⟨⟨cb', rb⟩, hb, rfl, rfl⟩
              exact fallback (ca := []) (ra := ra) rfl hb rfl rfl
            · simp only [hei, Option.some.injEq, Prod.mk.injEq] at hc
              exact imm12Step true false (Or.inr rfl) ra cb hei rfl ⟨hpa, hpb⟩ hc.1.symm hc.2.symm

theorem armSubNegDir_wp [Host] (w : RegWidth) (d rx : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.SUB_s (zr d w) (xzr w) (sh rx))]
      (fun s' => s' = wr s d ((-(s.regs.getXReg rx).toBitVec.setWidth w.bits).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp P hk => by
    cases w <;>
      (simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
         BitVec.zero_sub, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl)

theorem armNegOp_wp [Host] {n : Nat} (pa : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va : BitVec n} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : (if ![8, 16, 32, 64].contains n then none
      else match pa with
        | .imm cv => some ([armLdrPoolBv d ((-cv).setWidth 64)], maskNone)
        | .gpr (.reg r) => some ([ins (.SUB_s (zr d (armWidthOf n)) (xzr (armWidthOf n)) (sh r))], maskNone)
        | .gpr .SP => none) = some (c, clob))
    (hp : armMach.PArgHolds s (.bits n) pa va) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (-va) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hnw := mem_armWidths_le_armWidth hn
    cases pa with
    | vec vr => exact vr.elim
    | imm cv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      exact armImmPool_wp hn64 d s (-cv)
    | gpr r => cases r with
      | SP => simp at hc
      | reg rx =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
        exact armWrDst_of_eq hn64 d (armSubNegDir_wp (armWidthOf n) d rx s) (by
          rw [BitVec.setWidth_setWidth_of_le _ hn64, setWidth_neg_of_le hnw,
            BitVec.setWidth_setWidth_of_le _ hnw, hra])

private theorem armOrnNotDir_wp [Host] (w : RegWidth) (d rx : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.ORN_s (zr d w) (xzr w) (sh rx))]
      (fun s' => s' = wr s d ((~~~(s.regs.getXReg rx).toBitVec.setWidth w.bits).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp P hk => by
    cases w <;>
      (simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
         BitVec.zero_or, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl)

theorem armNotOp_wp [Host] {n : Nat} (pa : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va : BitVec n} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : (if ![8, 16, 32, 64].contains n then none
      else match pa with
        | .imm cv => some ([armLdrPoolBv d ((~~~cv).setWidth 64)], maskNone)
        | .gpr (.reg r) => some ([ins (.ORN_s (zr d (armWidthOf n)) (xzr (armWidthOf n)) (sh r))], maskNone)
        | .gpr .SP => none) = some (c, clob))
    (hp : armMach.PArgHolds s (.bits n) pa va) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (~~~va) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    cases pa with
    | vec vr => exact vr.elim
    | imm cv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      exact armImmPool_wp hn64 d s (~~~cv)
    | gpr r => cases r with
      | SP => simp at hc
      | reg rx =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
        exact armWrDst_of_eq hn64 d (armOrnNotDir_wp (armWidthOf n) d rx s) (by
          apply BitVec.eq_of_getLsbD_eq; intro i hi
          rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp [hi, armWidthOf, ← hra])

/-! ## 3. Shifts (`armShiftOp`) and rotates (`armRotOp`) -/

def armShiftEval (k : ArmShiftK) {m : Nat} (a b : BitVec m) : BitVec m :=
  match k with | .shl => a <<< (b.toNat % m) | .lshr => a >>> (b.toNat % m) | .ashr => a.sshiftRight (b.toNat % m)

private theorem armShiftDir_wp [Host] (k : ArmShiftK) (w : RegWidth) (d ra rb : XReg) (s : MachineData) :
    _root_.Program.wp [match k with
      | .shl => ins (.LSLV (zr d w) (zr ra w) (zr rb w))
      | .lshr => ins (.LSRV (zr d w) (zr ra w) (zr rb w))
      | .ashr => ins (.ASRV (zr d w) (zr ra w) (zr rb w))]
      (fun s' => s' = wr s d ((armShiftEval k
        ((s.regs.getXReg ra).toBitVec.setWidth w.bits)
        ((s.regs.getXReg rb).toBitVec.setWidth w.bits)).setWidth 64))
      (fun _ _ => False) s := by
  cases k <;> cases w <;>
    exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp, BitVec.ushiftRight_eq, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
      exact hk _ rfl

private theorem armShiftImmDir_wp [Host] (k : ArmShiftK) (w : RegWidth) (d ra : XReg)
    (amt : Nat) (hlt : amt < w.bits) (s : MachineData) :
    _root_.Program.wp [match k with
      | .shl => ins (.UBFM (zr d w) (zr ra w) ((w.bits - amt) % w.bits) (w.bits - 1 - amt))
      | .lshr => ins (.UBFM (zr d w) (zr ra w) amt (w.bits - 1))
      | .ashr => ins (.SBFM (zr d w) (zr ra w) amt (w.bits - 1))]
      (fun s' => s' = wr s d ((match k with
        | .shl => ((s.regs.getXReg ra).toBitVec.setWidth w.bits) <<< amt
        | .lshr => ((s.regs.getXReg ra).toBitVec.setWidth w.bits) >>> amt
        | .ashr => ((s.regs.getXReg ra).toBitVec.setWidth w.bits).sshiftRight amt).setWidth 64))
      (fun _ _ => False) s := by
  cases k <;> cases w <;>
    exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp]
      try rw [evalUBFM_lsl _ hlt]
      try rw [evalUBFM_lsr _ hlt]
      try rw [evalSBFM_asr _ hlt]
      simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl

private theorem armAndiMask32_wp [Host] {n : Nat} (hn : n = 8 ∨ n = 16) (src : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.AND_i (.low (.reg .X17) .W32) (zr src .W32) (armShiftMaskConst n))]
      (fun s' => s' = wr s .X17 (((s.regs.getXReg src).toBitVec.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    have hmask : (BitVec.ofInt 32 (Int64.ofNat (n - 1)).toInt) = BitVec.ofNat 32 (n - 1) := by
      rcases hn with rfl | rfl <;> decide
    simp only [t_step_simp, ConstExpr.interp, armShiftMaskConst, hmask]; exact hk _ rfl

private theorem armAndiMask32_eq {n : Nat} (hn : n = 8 ∨ n = 16) {x : BitVec 32} {v : BitVec n}
    (hx : x.setWidth n = v) :
    x &&& BitVec.ofNat 32 (n - 1) = v.setWidth 32 &&& BitVec.ofNat 32 (n - 1) := by
  have hnw : n ≤ 32 := by rcases hn with rfl | rfl <;> decide
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp only [BitVec.getLsbD_and]
  by_cases hin : i < n
  · have hxi := congrArg (fun z => z.getLsbD i) hx
    simp [hin, show i < 32 by omega] at hxi ⊢
    rw [hxi]
  · simp [getLsbD_shiftMask_ge hn hin]

theorem armShiftOp_wp [Host] (k : ArmShiftK) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb : BitVec n} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : armShiftOp k n pa pb d = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (armShiftEval k va vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armShiftOp] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    split at hc
    · rename_i hn3264
      have hn' : n = 32 ∨ n = 64 := by simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
      have varFallback : ∀ {ca ra cb rb}, armArgIn .X16 pa = some (ca, ra) → armArgIn .X17 pb = some (cb, rb) →
          c = ca ++ cb ++ [match k with
            | .shl => ins (.LSLV (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))
            | .lshr => ins (.LSRV (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))
            | .ashr => ins (.ASRV (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))] →
          clob = maskNone →
          _root_.Program.wp c (fun s' => GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (armShiftEval k va vb) ∧
            armMach.mem s' = armMach.mem s ∧ armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob)
            (fun _ _ => False) s := by
        intro ca ra cb rb ha hb hceq hclob; subst hceq; subst hclob
        refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
        rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
        refine armWrDst_after_scratch hn64 d (armShiftDir_wp k (armWidthOf n) d ra rb s₂) hd₂ hfr₂ ?_
        rcases hn' with rfl | rfl
        · rw [show (armWidthOf 32).bits = 32 from rfl, hra, hrb, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]
        · rw [show (armWidthOf 64).bits = 64 from rfl, hra, hrb, BitVec.setWidth_eq, BitVec.setWidth_eq]
      cases pa with
      | vec vr => exact vr.elim
      | imm _ =>
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl, rfl⟩; exact varFallback ha hb rfl rfl
      | gpr r => cases r with
        | SP => simp [armArgIn] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ =>
            simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨⟨ca, ra'⟩, ha, ⟨cb, rb'⟩, hb, rfl, rfl⟩; exact varFallback ha hb rfl rfl
          | imm cb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
            have hcb : cb = vb := hpb
            have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
            rcases hn' with rfl | rfl
            · refine armWrDst_of_eq hn64 d
                (armShiftImmDir_wp k .W32 d ra (cb.toNat % 32) (Nat.mod_lt _ (by decide)) s) ?_
              simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]
              cases k <;> rfl
            · refine armWrDst_of_eq hn64 d
                (armShiftImmDir_wp k .W64 d ra (cb.toNat % 64) (Nat.mod_lt _ (by decide)) s) ?_
              simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb, BitVec.setWidth_eq, BitVec.setWidth_eq]
              cases k <;> rfl
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
      have hnw32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl, rfl⟩
      simp only [List.append_assoc]; rw [← List.append_assoc ca cb]
      refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
      rintro s₂ ⟨hra, hrb, hneA, hneB, hd₂, _, hfr₂⟩
      cases k <;> dsimp only
      · refine armScratch_cons x17_mem_scratch hd₂ hfr₂ (armAndiMask32_wp hn' rb s₂) fun s₃ hs₃ hd₃ hfr₃ => ?_
        refine armWrDst_after_scratch hn64 d (armShiftDir_wp .shl .W32 d ra .X17 s₃) hd₃ hfr₃ ?_
        have h17 : (s₃.regs.getXReg .X17).toBitVec.setWidth 32 = vb.setWidth 32 &&& BitVec.ofNat 32 (n - 1) := by
          rw [hs₃]; simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
          exact armAndiMask32_eq hn' (by rwa [BitVec.setWidth_setWidth_of_le _ hnw32])
        have hra3 : (s₃.regs.getXReg ra).toBitVec.setWidth n = va := by
          rw [hs₃, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneA.symm]; exact hra
        simp only [armShiftEval, RegWidth.bits, BitVec.setWidth_setWidth_of_le _ hn64, h17]
        have hres := shl_subword_mask hn' ((s₃.regs.getXReg ra).toBitVec.setWidth 32) vb
        rw [BitVec.setWidth_setWidth_of_le _ hnw32, hra3] at hres
        rw [← BitVec.setWidth_setWidth_of_le _ hnw32]; exact hres
      · refine armScratch_cons x16_mem_scratch hd₂ hfr₂ (armExt32_wp false hn0 hnw32 .X16 ra s₂ va hra) fun s₃ hs₃ hd₃ hfr₃ => ?_
        refine armScratch_cons x17_mem_scratch hd₃ hfr₃ (armAndiMask32_wp hn' rb s₃) fun s₄ hs₄ hd₄ hfr₄ => ?_
        refine armWrDst_after_scratch hn64 d (armShiftDir_wp .lshr .W32 d .X16 .X17 s₄) hd₄ hfr₄ ?_
        have h17 : (s₄.regs.getXReg .X17).toBitVec.setWidth 32 = vb.setWidth 32 &&& BitVec.ofNat 32 (n - 1) := by
          rw [hs₄]; simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
          exact armAndiMask32_eq hn' (by
            rw [hs₃, BitVec.setWidth_setWidth_of_le _ hnw32, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm, hrb])
        have h16 : (s₄.regs.getXReg .X16).toBitVec.setWidth 32 = va.setWidth 32 := by
          rw [hs₄, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide), hs₃]
          simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
        simp only [armShiftEval, RegWidth.bits, BitVec.setWidth_setWidth_of_le _ hn64, h17, h16]
        rw [← BitVec.setWidth_setWidth_of_le _ hnw32]; exact lshr_subword_mask hn' va vb
      · refine armScratch_cons x16_mem_scratch hd₂ hfr₂ (armExt32_wp true hn0 hnw32 .X16 ra s₂ va hra) fun s₃ hs₃ hd₃ hfr₃ => ?_
        refine armScratch_cons x17_mem_scratch hd₃ hfr₃ (armAndiMask32_wp hn' rb s₃) fun s₄ hs₄ hd₄ hfr₄ => ?_
        refine armWrDst_after_scratch hn64 d (armShiftDir_wp .ashr .W32 d .X16 .X17 s₄) hd₄ hfr₄ ?_
        have h17 : (s₄.regs.getXReg .X17).toBitVec.setWidth 32 = vb.setWidth 32 &&& BitVec.ofNat 32 (n - 1) := by
          rw [hs₄]; simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
          exact armAndiMask32_eq hn' (by
            rw [hs₃, BitVec.setWidth_setWidth_of_le _ hnw32, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm, hrb])
        have h16 : (s₄.regs.getXReg .X16).toBitVec.setWidth 32 = va.signExtend 32 := by
          rw [hs₄, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide), hs₃]
          simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
        simp only [armShiftEval, RegWidth.bits, BitVec.setWidth_setWidth_of_le _ hn64, h17, h16]
        rw [← BitVec.setWidth_setWidth_of_le _ hnw32]; exact ashr_subword_mask hn' va vb

private theorem armRorvDir_wp [Host] (w : RegWidth) (d ra rb : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.RORV (zr d w) (zr ra w) (zr rb w))]
      (fun s' => s' = wr s d ((((s.regs.getXReg ra).toBitVec.setWidth w.bits).rotateRight
        (((s.regs.getXReg rb).toBitVec.setWidth w.bits).toNat % w.bits)).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases w <;> (simp only [t_step_simp, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl)

private theorem armExtrDir_wp [Host] (w : RegWidth) (d ra : XReg) (k : Nat) (s : MachineData) :
    _root_.Program.wp [ins (.EXTR (zr d w) (zr ra w) (zr ra w) k)]
      (fun s' => s' = wr s d ((((s.regs.getXReg ra).toBitVec.setWidth w.bits).rotateRight k).setWidth 64))
      (fun _ _ => False) s := by
  cases w <;> exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
    simp only [t_step_simp]; rw [evalEXTR_rotr]
    simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]; exact hk _ rfl

theorem armRotOp_wp [Host] (isLeft : Bool) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb : BitVec n} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc : armRotOp isLeft n pa pb d = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n)
        (if isLeft then va.rotateLeft (vb.toNat % n) else va.rotateRight (vb.toNat % n)) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armRotOp] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    split at hc
    · rename_i hn3264
      have hn' : n = 32 ∨ n = 64 := by simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
      have hrot_mod : ∀ {x : BitVec n} (m : Nat), x.rotateRight (m % n) = x.rotateRight m := fun {x} m => by
        apply BitVec.eq_of_getLsbD_eq; intro i hi; rcases hn' with rfl | rfl <;> simp [hi]
      have hrot_neg : ∀ {x y : BitVec n}, x.rotateRight ((-y).toNat % n) = x.rotateLeft (y.toNat % n) := fun {x y} => by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        rcases hn' with rfl | rfl <;> simp [hi] <;> grind
      have hrot_sub : ∀ {x y : BitVec n}, x.rotateRight ((n - y.toNat % n) % n) = x.rotateLeft (y.toNat % n) := fun {x y} => by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        rcases hn' with rfl | rfl <;> simp [hi] <;> grind
      have varFallback : ∀ {ca ra cb rb}, armArgIn .X16 pa = some (ca, ra) → armArgIn .X17 pb = some (cb, rb) →
          c = ca ++ cb ++ (if isLeft then [ins (.SUB_s (zr .X17 (armWidthOf n)) (xzr (armWidthOf n)) (sh rb)),
            ins (.RORV (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr .X17 (armWidthOf n)))]
            else [ins (.RORV (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))]) →
          clob = maskNone →
          _root_.Program.wp c (fun s' => GprHolds (armMach.getGpr s' (.reg d)) (.bits n)
              (if isLeft then va.rotateLeft (vb.toNat % n) else va.rotateRight (vb.toNat % n)) ∧
            armMach.mem s' = armMach.mem s ∧ armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob)
            (fun _ _ => False) s := by
        intro ca ra cb rb ha hb hceq hclob; subst hceq; subst hclob
        refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
        rintro s₂ ⟨hra, hrb, hneA, _, hd₂, _, hfr₂⟩
        cases isLeft
        · refine armWrDst_after_scratch hn64 d (armRorvDir_wp (armWidthOf n) d ra rb s₂) hd₂ hfr₂ ?_
          rcases hn' with rfl | rfl
          · rw [show (armWidthOf 32).bits = 32 from rfl, hra, hrb, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]; rfl
          · rw [show (armWidthOf 64).bits = 64 from rfl, hra, hrb, BitVec.setWidth_eq, BitVec.setWidth_eq]; rfl
        · refine armScratch_cons x17_mem_scratch hd₂ hfr₂ (armSubNegDir_wp (armWidthOf n) .X17 rb s₂) fun s₃ hs₃ hd₃ hfr₃ => ?_
          refine armWrDst_after_scratch hn64 d (armRorvDir_wp (armWidthOf n) d ra .X17 s₃) hd₃ hfr₃ ?_
          rcases hn' with rfl | rfl
          · rw [hs₃, show (armWidthOf 32).bits = 32 from rfl]
            simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
              Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneA.symm, BitVec.setWidth_setWidth_of_le _ hn64]
            rw [hra, hrb, BitVec.setWidth_eq, BitVec.setWidth_eq, hrot_neg]; simp
          · rw [hs₃, show (armWidthOf 64).bits = 64 from rfl]
            simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
              Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneA.symm, BitVec.setWidth_setWidth_of_le _ hn64]
            rw [hra, hrb, BitVec.setWidth_eq, BitVec.setWidth_eq, hrot_neg]; simp
      cases pa with
      | vec vr => exact vr.elim
      | imm _ =>
        simp only [bind, Option.bind_eq_some_iff] at hc
        rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, htail⟩
        cases isLeft <;> simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at htail <;>
          rcases htail with ⟨rfl, rfl⟩ <;> exact varFallback ha hb rfl rfl
      | gpr r => cases r with
        | SP => simp [armArgIn] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ =>
            simp only [bind, Option.bind_eq_some_iff] at hc
            rcases hc with ⟨⟨ca, ra'⟩, ha, ⟨cb, rb'⟩, hb, htail⟩
            cases isLeft <;> simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at htail <;>
              rcases htail with ⟨rfl, rfl⟩ <;> exact varFallback ha hb rfl rfl
          | imm cb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
            have hcb : cb = vb := hpb
            have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
            rcases hn' with rfl | rfl
            · cases isLeft
              · refine armWrDst_of_eq hn64 d (armExtrDir_wp .W32 d ra _ s) ?_
                simp only [RegWidth.bits, MemWidth.bits, hcb, Bool.false_eq_true, ↓reduceIte]
                rw [hra, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq, hrot_mod]
              · refine armWrDst_of_eq hn64 d (armExtrDir_wp .W32 d ra _ s) ?_
                simp only [RegWidth.bits, MemWidth.bits, hcb]
                rw [hra, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]; exact hrot_sub
            · cases isLeft
              · refine armWrDst_of_eq hn64 d (armExtrDir_wp .W64 d ra _ s) ?_
                simp only [RegWidth.bits, MemWidth.bits, hcb, Bool.false_eq_true, ↓reduceIte]
                rw [hra, BitVec.setWidth_eq, BitVec.setWidth_eq, hrot_mod]
              · refine armWrDst_of_eq hn64 d (armExtrDir_wp .W64 d ra _ s) ?_
                simp only [RegWidth.bits, MemWidth.bits, hcb]
                rw [hra, BitVec.setWidth_eq, BitVec.setWidth_eq]; exact hrot_sub
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
      have hnw32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl, rfl⟩
      simp only [List.append_assoc]; rw [← List.append_assoc ca cb]
      refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
      rintro s₂ ⟨hra, hrb, _, hneB, hd₂, _, hfr₂⟩
      refine armScratch_cons x16_mem_scratch hd₂ hfr₂ (armExt32_wp false hn0 hnw32 .X16 ra s₂ va hra) fun s₂' hs₂' hd₂' hfr₂' => ?_
      refine armScratch_cons x16_mem_scratch hd₂' hfr₂'
        (show _root_.Program.wp
            [ins (.ORR_s (zr .X16 .W32) (zr .X16 .W32)
              { reg := zr .X16 .W32, amount := Int64.ofNat n, shift := .LSL })]
            (fun s' => s' = wr s₂' .X16 (BitVec.setWidth 64 (va.setWidth 32 ||| va.setWidth 32 <<< n)))
            (fun _ _ => False) s₂' from armDirFallsTo_wp fun {_} p next jmp Q hk => by
          simp only [t_step_simp, hs₂', Reg64s.getXReg_setXReg_same, RegWidth.bits, MemWidth.bits,
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
            Bool.false_eq_true, ↓reduceIte, Int64.toInt_ofNat_of_lt (by omega : n < 2 ^ 63),
            Int.toNat_natCast]
          exact hk _ (by rw [hs₂']; rfl)) fun s₃ hs₃ hd₃ hfr₃ => ?_
      have h16₃ : (s₃.regs.getXReg .X16).toBitVec.setWidth 32 = (va.setWidth 32 ||| (va.setWidth 32 <<< n)) := by
        rw [hs₃]; simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      have hrb₃ : (s₃.regs.getXReg rb).toBitVec.setWidth n = vb := by
        rw [hs₃, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm, hs₂',
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm]; exact hrb
      cases isLeft
      · refine armScratch_cons x17_mem_scratch hd₃ hfr₃ (armAndiMask32_wp hn' rb s₃) fun s₄ hs₄ hd₄ hfr₄ => ?_
        refine armWrDst_after_scratch hn64 d (armShiftDir_wp .lshr .W32 d .X16 .X17 s₄) hd₄ hfr₄ ?_
        have h17 : (s₄.regs.getXReg .X17).toBitVec.setWidth 32 = vb.setWidth 32 &&& BitVec.ofNat 32 (n - 1) := by
          rw [hs₄]; simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
          exact armAndiMask32_eq hn' (by rwa [BitVec.setWidth_setWidth_of_le _ hnw32])
        have h16 : (s₄.regs.getXReg .X16).toBitVec.setWidth 32 = (va.setWidth 32 ||| (va.setWidth 32 <<< n)) := by
          rw [hs₄, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide)]; exact h16₃
        simp only [armShiftEval, RegWidth.bits, BitVec.setWidth_setWidth_of_le _ hn64, h17, h16]
        rw [← BitVec.setWidth_setWidth_of_le _ hnw32]; exact rotr_subword_mask hn' va vb
      · refine armScratch_cons x17_mem_scratch hd₃ hfr₃ (armSubNegDir_wp .W32 .X17 rb s₃) fun s₃' hs₃' hd₃' hfr₃' => ?_
        refine armScratch_cons x17_mem_scratch hd₃' hfr₃' (armAndiMask32_wp hn' .X17 s₃') fun s₄ hs₄ hd₄ hfr₄ => ?_
        refine armWrDst_after_scratch hn64 d (armShiftDir_wp .lshr .W32 d .X16 .X17 s₄) hd₄ hfr₄ ?_
        have h17 : (s₄.regs.getXReg .X17).toBitVec.setWidth 32 = (0#32 - vb.setWidth 32) &&& BitVec.ofNat 32 (n - 1) := by
          rw [hs₄]; simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
          have hsub : (0#32 - vb.setWidth 32).setWidth n = -vb := by
            rw [BitVec.zero_sub, setWidth_neg_of_le hnw32, BitVec.setWidth_setWidth_of_le _ hnw32, BitVec.setWidth_eq]
          have h17' : ((s₃'.regs.getXReg .X17).toBitVec.setWidth 32).setWidth n = -vb := by
            rw [hs₃', Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, RegWidth.bits,
              BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_setWidth_of_le _ hnw32,
              setWidth_neg_of_le hnw32, BitVec.setWidth_setWidth_of_le _ hnw32, hrb₃]
          rw [armAndiMask32_eq hn' h17', ← armAndiMask32_eq hn' hsub]
        have h16 : (s₄.regs.getXReg .X16).toBitVec.setWidth 32 = (va.setWidth 32 ||| (va.setWidth 32 <<< n)) := by
          rw [hs₄, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide), hs₃',
            Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide)]; exact h16₃
        simp only [armShiftEval, RegWidth.bits, BitVec.setWidth_setWidth_of_le _ hn64, h17, h16]
        rw [← BitVec.setWidth_setWidth_of_le _ hnw32]; exact rotl_subword_mask hn' va vb

end LeanQbe.T.Arm64
