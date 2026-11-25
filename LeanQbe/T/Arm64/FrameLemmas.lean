module

public import LeanQbe.T.Arm64.Frame
public import LeanQbe.T.AbiLemmas
import Kraken.AArch64.Parser

/-!
# AAPCS64 Arm64 Frame Verification
Proves `armFrameSpec : FrameTarget armMach armFrame armCondReads`, `NoLab`, and `ParserChecks`
up to `armFrameSize ns ≤ 2 ^ 64`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Std Std.ExtHashMap

/-! ## 1. Frame size arithmetic, alignment, and address helpers -/

theorem armFrameSize_ge (ns : Nat) : 8 * ns + 8 ≤ armFrameSize ns := by
  dsimp only [armFrameSize]; omega
theorem armFrameSize_slots (ns : Nat) : 8 * ns ≤ armFrameSize ns := by
  have := armFrameSize_ge ns; omega
theorem armFrameSize_mod (ns : Nat) : armFrameSize ns % 16 = 0 := by
  dsimp only [armFrameSize]; omega

theorem armCheckSP_eq_false (s : MachineData) (hsp : (get s .SP).toNat % 16 = 0) :
    (s.regs.getRegOrSp RegOrSp.SP % 16#64 != 0#64) = false := by
  have h' : s.regs.SP.toBitVec % 16#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]; simpa [get_sp] using hsp
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take, h']

@[t_step_simp]
theorem armAtSp_eval [Labels] (s : MachineData) (o : Nat) (p : Std.Rco Int64) :
    (atOff .SP o).eval s p = (s.regs.SP.toBitVec + BitVec.ofNat 64 o, s) := by
  simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp_sp64, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt]
  rw [ofInt_toInt_ofNat]

@[t_step_simp]
theorem armAtSpIdx_eval [Labels] (s : MachineData) (r : XReg) (p : Std.Rco Int64) :
    (armAtSpIdx r).eval s p = (s.regs.SP.toBitVec + (s.regs.getXReg r).toBitVec, s) := by
  dsimp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend]
  simp only [Reg64s.getRegOrSp_sp64, BitVec.signed, Reg64s.getRegOrZr64, RegOrZr.base]
  exact congrArg (·, s) (ofInt_toInt_add_toNat _ _)

/-! ## 2. Frame helpers & shared building-block `Program.wp` lemmas -/

private theorem armFrame_upd_regs {s s' : MachineData} {gClob : List Reg} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r)
    (hflg : fClob = maskAll ∨ s'.status = s.status) :
    armMach.Frame armCondReads s s' gClob [] fClob := by
  refine ⟨hkeep, fun v => v.elim, ?_⟩
  rcases hflg with rfl | hst
  · intro c hd; cases c <;> (
      dsimp only [FlagMask.disjoint, armCondReads, maskAll, maskN, maskZ, maskC, maskV] at hd
      exact absurd hd (by decide))
  · intro c _; simp [hst]

private theorem Reg64s_getXReg_setSP (regs : Reg64s) (v : UInt64) (x : XReg) :
    ({ regs with SP := v } : Reg64s).getXReg x = regs.getXReg x := by cases x <;> rfl

private theorem armKeep_regs {s s' : MachineData} (gClob : List Reg)
    (hsp : .SP ∉ gClob → s'.regs.SP = s.regs.SP)
    (hx : ∀ x : XReg, .reg x ∉ gClob → s'.regs.getXReg x = s.regs.getXReg x) :
    ∀ r, r ∉ gClob → get s' r = get s r := fun r hr => by
  cases r with | SP => simp [get_sp, hsp hr] | reg x => simp [get_reg, hx x hr]

private theorem armFrame_keep_scratch {s s' : MachineData} (hsp : s'.regs.SP = s.regs.SP)
    (hx : ∀ x, x ≠ .X16 → x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x)
    (hst : s'.status = s.status) : armMach.Frame armCondReads s s' armScratch [] maskNone :=
  armFrame_upd_regs (armKeep_regs _ (fun _ => hsp) (fun y hy => by
    have h := ne_of_not_mem_armScratch hy
    exact hx y (fun e => h.1 (e ▸ rfl)) (fun e => h.2 (e ▸ rfl)))) (Or.inr hst)

private abbrev SpPost (v : BitVec 64) (s s' : MachineData) : Prop :=
  s'.regs.SP = UInt64.ofBitVec v ∧ (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
  s'.status = s.status ∧ s'.dmem = s.dmem

private theorem armSpOp_wp [Host] (isSub : Bool) (n : Nat) (s : MachineData) :
    _root_.Program.wp (if isSub then armSubSp n else armAddSp n)
      (SpPost (if isSub then get s .SP - BitVec.ofNat 64 n
               else get s .SP + BitVec.ofNat 64 n) s) (fun _ _ => False) s := by
  have pool (op : BitVec 64 → BitVec 64 → BitVec 64) (d : Directive)
      (hd : armDirFallsTo d (wr s .X16 (BitVec.ofNat 64 n)) (fun s' => s' =
        { (wr s .X16 (BitVec.ofNat 64 n)) with regs :=
          { (wr s .X16 (BitVec.ofNat 64 n)).regs with
            SP := UInt64.ofBitVec (op (get s .SP) (BitVec.ofNat 64 n)) } })) :
      _root_.Program.wp [armLdrPool .X16 n, d]
        (SpPost (op (get s .SP) (BitVec.ofNat 64 n)) s) (fun _ _ => False) s := by
    refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 n) s) ?_; rintro _ rfl
    refine armWp_mono (armDirFallsTo_wp hd) ?_; rintro _ rfl; exact ⟨by simp, fun x hx => by
      dsimp only; rw [Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm], rfl, rfl⟩
  cases isSub <;> (
    simp only [↓reduceIte, Bool.false_eq_true, armSubSp, armSubSpIns, armAddSp, armAddSpIns,
      emitClean_ite]; split
    · refine armWp_mono (armDirFallsTo_wp (fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits]
        rw [ofInt_toInt_ofNat]; exact hk _ rfl)) ?_
      rintro _ rfl; exact ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
    · exact pool _ _ (fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits,
          ExtRegExpr.interp, BitVec.apply_extend, BitVec.unsigned, Reg64s.getRegOrZr64,
          RegOrZr.base]; rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]; exact hk _ rfl))

private theorem armStAddr_fallsTo (r : XReg) (addr : AddrExpr) (a : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData) (hbase : addr.base = RegOrSp.SP)
    (hal : (get s .SP).toNat % 16 = 0)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), addr.eval s p = (a, s))
    (hmem : (region a 8 ⋆ R) s.dmem) : armDirFallsTo (ins (.STR (zr r .W64) addr)) s
      (fun s' => s'.regs = s.regs ∧ s'.status = s.status ∧
        (cell64 a (get s (.reg r)) ⋆ R) s'.dmem) := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem; intro _ p _ _ _ hk
  simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
    AddrExpr.checkSPAlignment, hbase, armCheckSP_eq_false s hal, Bool.false_eq_true, ↓reduceIte,
    haddr p, getRegOrZr_zr, RegWidth.bits, Effects.All]
  rw [store_All_of_sep _ _ .W64 _ _ _ bs R hbs hl]; refine hk _ ⟨rfl, rfl, ?_⟩; rw [get_reg]
  exact Mem.storeInt_sep _ 8 bs R s.dmem ⟨hbs, hl⟩ (s.regs.getXReg r).toBitVec.toInt

private theorem armLdAddr_fallsTo (rd : XReg) (addr : AddrExpr) (a v : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData) (hbase : addr.base = RegOrSp.SP)
    (hal : (get s .SP).toNat % 16 = 0)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), addr.eval s p = (a, s))
    (hmem : (cell64 a v ⋆ R) s.dmem) :
    armDirFallsTo (ins (.LDR (zr rd .W64) (.addr addr))) s (fun s' => s' = wr s rd v) := by
  intro _ p _ _ _ hk
  simp only [Directive.interp, Instr.interp, Operation.interp, AddrOrLit.interpLoad,
    AddrExpr.interpLoad, AddrExpr.checkSPAlignment, hbase, armCheckSP_eq_false s hal,
    Bool.false_eq_true, ↓reduceIte, haddr p, MachineData.setRegOrZr, setRegOrZr_zr, Effects.All]
  rw [load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) R hmem (Int.toBytes_length _ _)]
  simp only [MemWidth.bits, BitVec.ofInt_ofBytes_toBytes 64 8 rfl v, BitVec.setWidth_eq]
  exact hk _ rfl

private theorem armStSpXReg_wp [Host] (r : XReg) (o : Nat) {R : Mem 64 → Prop} (s : MachineData)
    (hr : r ≠ .X16) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 o) 8 ⋆ R) s.dmem) :
    _root_.Program.wp (armStSpXReg r o)
      (fun s' => s'.regs.SP = s.regs.SP ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧ s'.status = s.status ∧
        (cell64 (get s .SP + BitVec.ofNat 64 o) (get s (.reg r)) ⋆ R) s'.dmem)
      (fun _ _ => False) s := by
  dsimp only [armStSpXReg, armStSpXRegIns]; simp only [emitClean_ite]; split
  · refine armWp_mono (armDirFallsTo_wp (armStAddr_fallsTo r (atOff .SP o) _ s rfl hal
      (fun p => by rw [armAtSp_eval]; rfl) hmem)) ?_; rintro s' ⟨hr', hst, hm⟩
    exact ⟨congrArg Reg64s.SP hr', fun _ _ => congrFun (congrArg Reg64s.getXReg hr') _, hst, hm⟩
  · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 o) s) ?_; rintro _ rfl
    refine armWp_mono (armDirFallsTo_wp (armStAddr_fallsTo r (armAtSpIdx .X16) _
      (wr s .X16 (BitVec.ofNat 64 o)) rfl (by simpa [get_sp] using hal)
      (fun p => by rw [armAtSpIdx_eval]; simp [get_sp]) hmem)) ?_; rintro s' ⟨hr', hst, hm⟩
    rw [get_wr_of_ne s .X16 _ (.reg r) (fun e => hr (XRegOrSp.reg.inj e))] at hm
    exact ⟨by simp [hr'], fun x hx => by
      rw [hr']; simp [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm], hst, hm⟩

private theorem armLdSpXReg_wp [Host] (rd : XReg) (o : Nat) (v : BitVec 64) {R : Mem 64 → Prop}
    (s : MachineData) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (cell64 (get s .SP + BitVec.ofNat 64 o) v ⋆ R) s.dmem) :
    _root_.Program.wp (armLdSpXReg rd o)
      (fun s' => s'.regs.SP = s.regs.SP ∧ s'.regs.getXReg rd = UInt64.ofBitVec v ∧
        (∀ x, x ≠ rd → x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem) (fun _ _ => False) s := by
  dsimp only [armLdSpXReg, armLdSpXRegIns]; simp only [emitClean_ite]; split
  · refine armWp_mono (armDirFallsTo_wp (armLdAddr_fallsTo rd (atOff .SP o) _ v s rfl hal
      (fun p => by rw [armAtSp_eval]; rfl) hmem)) ?_; rintro _ rfl
    exact ⟨Reg64s.SP_setXReg _ _ _, Reg64s.getXReg_setXReg_same _ _ _,
      fun _ hx _ => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl, rfl⟩
  · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 o) s) ?_; rintro _ rfl
    refine armWp_mono (armDirFallsTo_wp (armLdAddr_fallsTo rd (armAtSpIdx .X16) _ v
      (wr s .X16 (BitVec.ofNat 64 o)) rfl (by simpa [get_sp] using hal)
      (fun p => by rw [armAtSpIdx_eval]; simp [get_sp]) hmem)) ?_; rintro _ rfl
    refine ⟨by simp, Reg64s.getXReg_setXReg_same _ _ _, fun x hxrd hx16 => ?_, rfl, rfl⟩
    rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hxrd.symm,
      Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]

private theorem arm_sp_add8 (sp : BitVec 64) (o : Nat) :
    sp + BitVec.ofNat 64 o + 8#64 = sp + BitVec.ofNat 64 (o + 8) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem armStpSpXReg_wp [Host] (r1 r2 : XReg) (o : Nat) {R : Mem 64 → Prop}
    (s : MachineData) (hr1 : r1 ≠ .X16) (hr2 : r2 ≠ .X16) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 o) 8 ⋆
      (region (get s .SP + BitVec.ofNat 64 (o + 8)) 8 ⋆ R)) s.dmem) :
    _root_.Program.wp (emitClean (armStpSpXRegIns r1 r2 o))
      (fun s' => s'.regs.SP = s.regs.SP ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧ s'.status = s.status ∧
        (cell64 (get s .SP + BitVec.ofNat 64 o) (get s (.reg r1)) ⋆
          (cell64 (get s .SP + BitVec.ofNat 64 (o + 8)) (get s (.reg r2)) ⋆ R)) s'.dmem)
      (fun _ _ => False) s := by
  have ho8 := arm_sp_add8 (get s .SP) o
  dsimp only [armStpSpXRegIns]; simp only [emitClean_ite]; split
  · have hm' : (region (get s .SP + BitVec.ofNat 64 o) 8 ⋆
        (region (get s .SP + BitVec.ofNat 64 o + 8#64) 8 ⋆ R)) s.dmem := by simpa only [ho8]
    obtain ⟨bs1, hl1, hbs1⟩ := region_sep_elim hm'
    refine armWp_mono (armDirFallsTo_wp (fun {_} _ _ _ _ hk => by
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.checkSPAlignment,
        armCheckSP_eq_false s hal, Bool.false_eq_true, ↓reduceIte, armAtSp_eval, ← get_sp,
        getRegOrZr_zr, RegWidth.bits, Effects.All, store_All_of_sep _ _ .W64 _ _ _ bs1 _ hbs1 hl1]
      have hm1 : (region (get s .SP + BitVec.ofNat 64 o + 8#64) 8 ⋆
          (cell64 (get s .SP + BitVec.ofNat 64 o) (get s (.reg r1)) ⋆ R)) (s.dmem.storeInt
          (get s .SP + BitVec.ofNat 64 o) 8 (s.regs.getXReg r1).toBitVec.toInt) := by
        rw [← get_reg]; exact sep_cast (Mem.storeInt_sep _ 8 bs1 _ s.dmem ⟨hbs1, hl1⟩
          (s.regs.getXReg r1).toBitVec.toInt) (by ac_rfl)
      obtain ⟨bs2, hl2, hbs2⟩ := region_sep_elim hm1
      rw [show RegWidth.W64.bytesv = 8#64 from rfl, store_All_of_sep _ _ .W64 _ _ _ bs2 _ hbs2 hl2]
      refine hk _ ⟨rfl, fun _ _ => rfl, rfl, ?_⟩; rw [← ho8]
      exact sep_cast (show (cell64 _ (get s (.reg r2)) ⋆ (cell64 _ (get s (.reg r1)) ⋆ R)) _ from
        Mem.storeInt_sep _ 8 bs2 _ _ ⟨hbs2, hl2⟩ (s.regs.getXReg r2).toBitVec.toInt)
        (by ac_rfl))) (fun _ h => h)
  · rw [emitClean_append]; refine armWp_append (armStSpXReg_wp r1 o s hr1 hal hmem) ?_
    rintro s₁ ⟨hsp1, hx1, hst1, hd1⟩; have hsp : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
    refine armWp_mono (armStSpXReg_wp r2 (o + 8)
      (R := cell64 (get s .SP + BitVec.ofNat 64 o) (get s (.reg r1)) ⋆ R) s₁ hr2 (hsp ▸ hal)
      (by rw [hsp]; exact sep_cast hd1 (by ac_rfl))) ?_
    rintro s' ⟨hsp2, hx2, hst2, hd2⟩
    rw [hsp, show get s₁ (.reg r2) = get s (.reg r2) by
      rw [get_reg, hx1 r2 hr2]; exact (get_reg s r2).symm] at hd2
    exact ⟨hsp2.trans hsp1, fun x hx => (hx2 x hx).trans (hx1 x hx),
      hst2.trans hst1, sep_cast hd2 (by ac_rfl)⟩

private theorem armLdpSpXReg_wp [Host] (rd1 rd2 : XReg) (o : Nat) (v1 v2 : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData) (hrd : rd1 ≠ rd2) (hrd1 : rd1 ≠ .X16)
    (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (cell64 (get s .SP + BitVec.ofNat 64 o) v1 ⋆
      (cell64 (get s .SP + BitVec.ofNat 64 (o + 8)) v2 ⋆ R)) s.dmem) :
    _root_.Program.wp (emitClean (armLdpSpXRegIns rd1 rd2 o))
      (fun s' => s'.regs.SP = s.regs.SP ∧
        s'.regs.getXReg rd1 = UInt64.ofBitVec v1 ∧ s'.regs.getXReg rd2 = UInt64.ofBitVec v2 ∧
        (∀ x, x ≠ rd1 → x ≠ rd2 → x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem) (fun _ _ => False) s := by
  have ho8 := arm_sp_add8 (get s .SP) o
  dsimp only [armLdpSpXRegIns]; simp only [emitClean_ite]; split
  · have hm' : (cell64 (get s .SP + BitVec.ofNat 64 o) v1 ⋆
        (cell64 (get s .SP + BitVec.ofNat 64 o + 8#64) v2 ⋆ R)) s.dmem := by simpa only [ho8]
    refine armWp_mono (armDirFallsTo_wp (fun {_} _ _ _ _ hk => by
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.checkSPAlignment,
        armCheckSP_eq_false s hal, Bool.false_eq_true, ↓reduceIte, armAtSp_eval, ← get_sp,
        Effects.All, load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v1.toInt) _ hm'
          (Int.toBytes_length _ _)]
      have hm2 : (cell64 (get s .SP + BitVec.ofNat 64 o + 8#64) v2 ⋆
          (cell64 (get s .SP + BitVec.ofNat 64 o) v1 ⋆ R)) s.dmem := sep_cast hm' (by ac_rfl)
      rw [show RegWidth.W64.bytesv = 8#64 from rfl,
        load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v2.toInt) _ hm2 (Int.toBytes_length _ _)]
      simp only [MachineData.setRegOrZr, setRegOrZr_zr, MemWidth.bits,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl v1, BitVec.ofInt_ofBytes_toBytes 64 8 rfl v2,
        BitVec.setWidth_eq]; exact hk (wr (wr s rd1 v1) rd2 v2) rfl)) ?_
    rintro _ rfl; refine ⟨by simp, by
      rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrd.symm, Reg64s.getXReg_setXReg_same],
      Reg64s.getXReg_setXReg_same _ _ _, fun x hx1 hx2 _ => by
        rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx2.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx1.symm], rfl, rfl⟩
  · rw [emitClean_append]; refine armWp_append (armLdSpXReg_wp rd1 o v1 s hal hmem) ?_
    rintro s₁ ⟨hsp1, hrd1_eq, hx1, hst1, hd1⟩
    have hsp : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
    refine armWp_mono (armLdSpXReg_wp rd2 (o + 8) v2
      (R := cell64 (get s .SP + BitVec.ofNat 64 o) v1 ⋆ R) s₁ (hsp ▸ hal)
      (by rw [hsp, hd1]; exact sep_cast hmem (by ac_rfl))) ?_
    rintro s' ⟨hsp2, hrd2_eq, hx2, hst2, hd2⟩
    exact ⟨hsp2.trans hsp1, by rw [hx2 rd1 hrd hrd1, hrd1_eq], hrd2_eq,
      fun x hx1' hx2' hx16 => by rw [hx2 x hx2' hx16, hx1 x hx1' hx16],
      hst2.trans hst1, hd2.trans hd1⟩

private theorem armCanonAbiXReg_wp [Host] {t : Ty} {x : XReg} {v : Val t} (s : MachineData)
    (ht : t = .bool ∨ ∃ n ∈ [8, 16, 32], t = .bits n) (hh : GprHolds (get s (.reg x)) t v) :
    _root_.Program.wp (armCanonAbiXReg t x)
      (fun s' => ∃ s'', s' = s'' ∧ s''.regs = (wr s x (get s'' (.reg x))).regs ∧
        s''.status = s.status ∧ s''.dmem = s.dmem ∧ AbiGprHolds (get s'' (.reg x)) t v)
      (fun _ _ => False) s := by
  have mkS : ∀ {d : Directive} {n : Nat},
      armDirFallsTo d s (fun s' => s' = wr s x (((get s (.reg x)).setWidth n).setWidth 64)) →
      AbiGprHolds (((get s (.reg x)).setWidth n).setWidth 64) t v →
      _root_.Program.wp [d] (fun s' => ∃ s'', s' = s'' ∧
        s''.regs = (wr s x (get s'' (.reg x))).regs ∧ s''.status = s.status ∧
        s''.dmem = s.dmem ∧ AbiGprHolds (get s'' (.reg x)) t v) (fun _ _ => False) s :=
    fun hd hAbi => armWp_mono (armDirFallsTo_wp hd) (by rintro _ rfl; exact
      ⟨wr s x _, rfl, by simp [wr, get_wr_same], rfl, rfl, by simpa [get_wr_same] using hAbi⟩)
  have ubfm (k : Nat) (hk8 : k = 7 ∨ k = 15) :
      armDirFallsTo (ins (.UBFM (zr x .W64) (zr x .W64) 0 k)) s
        (fun s' => s' = wr s x (((get s (.reg x)).setWidth (k + 1)).setWidth 64)) :=
    fun {_} _ _ _ _ hk => by
      simp only [t_step_simp]; rcases hk8 with rfl | rfl <;>
        exact hk _ (by simp [evalUBFM, BitVec.take, BitVec.zeroExtend]; rfl)
  rcases ht with rfl | ⟨n, hn, rfl⟩
  · exact mkS (ubfm 7 (Or.inl rfl)) (abiGprHolds_bool_of_gprHolds hh)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; rcases hn with rfl | rfl | rfl
    · exact mkS (ubfm 7 (Or.inl rfl)) (abiGprHolds_bits_of_gprHolds hh)
    · exact mkS (ubfm 15 (Or.inr rfl)) (abiGprHolds_bits_of_gprHolds hh)
    · exact mkS (fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, sh, Int64.toInt_zero, RegWidth.bits]
        rw [show ((0#32 ||| (s.regs.getXReg x).toBitVec.setWidth 32 <<< (0 : Int).toNat) :
          BitVec 32).setWidth 64 = ((get s (.reg x)).setWidth 32).setWidth 64 by simp [get_reg]]
        exact hk _ rfl) (abiGprHolds_bits_of_gprHolds hh)

/-! ## 3. `Arm64PairStepKit`: `STP`/`LDP` slot-pair frame induction -/

section Arm64PairStepKit

private abbrev SavePost (i : Nat) (rs : List Reg) (R : Mem 64 → Prop) (s s' : MachineData) : Prop :=
  s'.regs.SP = s.regs.SP ∧
  (∀ x, x ≠ .X16 → x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x) ∧ s'.status = s.status ∧
  (array64 (get s .SP + BitVec.ofNat 64 (8 * i)) (rs.map (get s)) ⋆ R) s'.dmem

private abbrev RestorePost (rs : List Reg) (s₀ s s' : MachineData) : Prop :=
  get s' .SP = get s .SP ∧ (∀ r ∈ rs, get s' r = get s₀ r) ∧
  (∀ x, .reg x ∉ rs → x ≠ .X16 → x ≠ .X17 → get s' (.reg x) = get s (.reg x)) ∧
  s'.status = s.status ∧ s'.dmem = s.dmem

private theorem arm_sp_slot8 (sp : BitVec 64) (i : Nat) :
    sp + BitVec.ofNat 64 (8 * i) + 8 = sp + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

private theorem arm_sp_slot8_plus (sp : BitVec 64) (i : Nat) :
    sp + BitVec.ofNat 64 (8 * i) + 8 = sp + BitVec.ofNat 64 (8 * i + 8) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp

private theorem arm_sp_slot16 (sp : BitVec 64) (i : Nat) :
    sp + BitVec.ofNat 64 (8 * i) + 8 + 8 = sp + BitVec.ofNat 64 (8 * (i + 2)) := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

private theorem arm_cs_ne_scratch {x : XReg} (hx : .reg x ∈ armFrame.calleeSaved) :
    x ≠ .X16 ∧ x ≠ .X17 := ⟨fun e => by subst e; simp at hx, fun e => by subst e; simp at hx⟩

private theorem arm_frame_pair_split {sp : BitVec 64} {i n : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} (hlen : 8 + (8 + 8 * n) ≤ 2 ^ 64)
    (h : (region (sp + BitVec.ofNat 64 (8 * i)) (8 + (8 + 8 * n)) ⋆ R) m) :
    (region (sp + BitVec.ofNat 64 (8 * i)) 8 ⋆ (region (sp + BitVec.ofNat 64 (8 * i + 8)) 8 ⋆
      (region (sp + BitVec.ofNat 64 (8 * (i + 2))) (8 * n) ⋆ R))) m := by
  rw [region_split hlen, region_split (by omega),
    show sp + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8 = sp + BitVec.ofNat 64 (8 * i + 8) from
      arm_sp_slot8_plus sp i,
    show sp + BitVec.ofNat 64 (8 * i + 8) + BitVec.ofNat 64 8 = sp + BitVec.ofNat 64 (8 * (i + 2))
      from by apply BitVec.eq_of_toNat_eq; simp; omega] at h
  exact sep_cast h (by ac_rfl)

private theorem arm_frame_pair_array64 {sp : BitVec 64} {i : Nat} {v1 v2 : BitVec 64}
    {vs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (sp + BitVec.ofNat 64 (8 * i)) (v1 :: v2 :: vs) ⋆ R) m) :
    (cell64 (sp + BitVec.ofNat 64 (8 * i)) v1 ⋆ (cell64 (sp + BitVec.ofNat 64 (8 * i + 8)) v2 ⋆
      (array64 (sp + BitVec.ofNat 64 (8 * (i + 2))) vs ⋆ R))) m := by
  simp only [array64_cons] at h; rw [arm_sp_slot16, arm_sp_slot8_plus] at h
  exact sep_cast h (by ac_rfl)

private theorem armSlotSt_wp [Host] (i : Nat) (r : Reg) {R : Mem 64 → Prop} (s : MachineData)
    (hr : r ∉ armScratch) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ R) s.dmem) :
    _root_.Program.wp (armSlotSt i r)
      (fun s' => s'.regs.SP = s.regs.SP ∧
        (∀ x, x ≠ .X16 → x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x) ∧ s'.status = s.status ∧
        (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s r) ⋆ R) s'.dmem)
      (fun _ _ => False) s := by
  cases r with
  | reg x =>
    exact armWp_mono (armStSpXReg_wp x (8 * i) s
      (fun e => (ne_of_not_mem_armScratch hr).1 (e ▸ rfl)) hal hmem)
      (fun _ ⟨hsp', hx', hst', hdmem'⟩ => ⟨hsp', fun y hy16 _ => hx' y hy16, hst', hdmem'⟩)
  | SP =>
    dsimp only [armSlotSt, armSlotStIns]; simp only [emitClean_append]
    refine armWp_cons (armMovToX_wp .X17 .SP s) ?_; rintro _ rfl
    refine armWp_mono (armStSpXReg_wp .X17 (8 * i) _ (by decide)
      (by simpa [get_sp] using hal) (by simpa [get_sp] using hmem)) ?_
    rintro s' ⟨hsp', hx', hst', hdmem'⟩
    rw [get_wr_same] at hdmem'; simp only [get_sp, Reg64s.SP_setXReg] at hsp' hdmem'
    exact ⟨hsp', fun y hy16 hy17 => by
      rw [hx' y hy16, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy17.symm], hst', hdmem'⟩

private theorem armSlotLd_wp [Host] (rd : Reg) (i : Nat) (v : BitVec 64) {R : Mem 64 → Prop}
    (s : MachineData) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) v ⋆ R) s.dmem) :
    _root_.Program.wp (armSlotLd rd i)
      (fun s' => get s' rd = v ∧ (∀ r, r ≠ rd → r ∉ armScratch → get s' r = get s r) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem) (fun _ _ => False) s := by
  cases rd with
  | reg x =>
    refine armWp_mono (armLdSpXReg_wp x (8 * i) v s hal hmem) ?_
    rintro s' ⟨hsp', hrx, hx', hst', hdmem'⟩
    refine ⟨by simp [get_reg, hrx], fun r hr1 hr2 => ?_, hst', hdmem'⟩
    cases r with | SP => simp [get_sp, hsp'] | reg y =>
      exact congrArg UInt64.toBitVec (hx' y (fun e => hr1 (e ▸ rfl))
        (fun e => hr2 (by simp [e, armScratch])))
  | SP =>
    dsimp only [armSlotLd, armSlotLdIns]; simp only [emitClean_append]
    refine armWp_append (armLdSpXReg_wp .X17 (8 * i) v s hal hmem) ?_
    rintro s₁ ⟨_, hx17, hx1, hst1, hdmem1⟩
    refine armWp_mono (armMovToSp_wp .X17 s₁) ?_; rintro _ rfl
    refine ⟨by simp [get_sp, get_reg, hx17], fun r hr1 hr2 => ?_, hst1, hdmem1⟩
    cases r with | SP => exact absurd rfl hr1 | reg y =>
      have hy := ne_of_not_mem_armScratch hr2; simp only [get_reg, Reg64s_getXReg_setSP]
      exact congrArg UInt64.toBitVec (hx1 y (fun e => hy.2 (e ▸ rfl)) (fun e => hy.1 (e ▸ rfl)))

private theorem arm_save_step_tl {i : Nat} {stepRs restRs : List Reg} {R Rmid : Mem 64 → Prop}
    {s s₁ s' : MachineData} (hrest : ∀ r ∈ restRs, r ∉ armScratch)
    (hsp1 : s₁.regs.SP = s.regs.SP) (hst1 : s₁.status = s.status) (hsp2 : s'.regs.SP = s₁.regs.SP)
    (hx1 : ∀ x, x ≠ .X16 → x ≠ .X17 → s₁.regs.getXReg x = s.regs.getXReg x)
    (hx2 : ∀ x, x ≠ .X16 → x ≠ .X17 → s'.regs.getXReg x = s₁.regs.getXReg x)
    (hst2 : s'.status = s₁.status) (hm2 : (array64 (get s₁ .SP + BitVec.ofNat 64
      (8 * (i + stepRs.length))) (restRs.map (get s₁)) ⋆ Rmid) s'.dmem)
    (harr : ∀ m, (array64 (get s .SP + BitVec.ofNat 64 (8 * (i + stepRs.length)))
      (restRs.map (get s)) ⋆ Rmid) m → (array64 (get s .SP + BitVec.ofNat 64 (8 * i))
      ((stepRs ++ restRs).map (get s)) ⋆ R) m) : SavePost i (stepRs ++ restRs) R s s' := by
  have hsp : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
  have hmap : restRs.map (get s₁) = restRs.map (get s) := List.map_congr_left fun r hr => by
    cases r with | SP => exact hsp | reg x =>
      have hx := ne_of_not_mem_armScratch (hrest _ hr)
      simp [get_reg, hx1 x (fun e => hx.1 (e ▸ rfl)) (fun e => hx.2 (e ▸ rfl))]
  rw [hsp, hmap] at hm2
  exact ⟨hsp2.trans hsp1, fun x a b => (hx2 x a b).trans (hx1 x a b), hst2.trans hst1, harr _ hm2⟩

private theorem arm_save_pair_step [Host] {i : Nat} {x1 x2 : XReg} {rs' : List Reg}
    {R : Mem 64 → Prop} {s : MachineData} (hr1 : x1 ≠ .X16) (hr2 : x2 ≠ .X16)
    (hrs : ∀ r ∈ rs', r ∉ armScratch) (hlen : 8 + (8 + 8 * rs'.length) ≤ 2 ^ 64)
    (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 (8 * i)) (8 + (8 + 8 * rs'.length)) ⋆ R) s.dmem)
    (ih : ∀ s₁ R₁, (get s₁ .SP).toNat % 16 = 0 →
      (region (get s₁ .SP + BitVec.ofNat 64 (8 * (i + 2))) (8 * rs'.length) ⋆ R₁) s₁.dmem →
      _root_.Program.wp (armSaveRegs (i + 2) rs') (SavePost (i + 2) rs' R₁ s₁)
        (fun _ _ => False) s₁) :
    _root_.Program.wp (armSaveRegs i (.reg x1 :: .reg x2 :: rs'))
      (SavePost i (.reg x1 :: .reg x2 :: rs') R s) (fun _ _ => False) s := by
  dsimp only [armSaveRegs, armSaveRegsIns]; rw [emitClean_append]
  refine armWp_append (armStpSpXReg_wp x1 x2 (8 * i) s hr1 hr2 hal
    (arm_frame_pair_split hlen hmem)) ?_; rintro s₁ ⟨hsp1, hx1, hst1, hdmem1⟩
  have hsp : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
  refine armWp_mono (ih s₁ (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s (.reg x1)) ⋆
      (cell64 (get s .SP + BitVec.ofNat 64 (8 * i + 8)) (get s (.reg x2)) ⋆ R))
    (hsp ▸ hal) (by rw [hsp]; exact sep_cast hdmem1 (by ac_rfl))) ?_
  rintro s' ⟨hsp2, hx2, hst2, hm2⟩
  exact arm_save_step_tl (stepRs := [.reg x1, .reg x2]) hrs hsp1 hst1 hsp2
    (fun x h16 _ => hx1 x h16) hx2 hst2 hm2 fun _ hm => by
      simp only [List.cons_append, List.nil_append, List.map_cons, array64_cons,
        List.length_cons, List.length_nil] at hm ⊢
      rw [arm_sp_slot16, arm_sp_slot8_plus]; exact sep_cast hm (by ac_rfl)

private theorem arm_save_single_step [Host] {i : Nat} {r1 : Reg} {rest : List Reg}
    {R : Mem 64 → Prop} {s : MachineData}
    (h1 : r1 ∉ armScratch) (hrest : ∀ r ∈ rest, r ∉ armScratch)
    (hi : armSaveRegsIns i (r1 :: rest) = armSlotStIns i r1 ++ armSaveRegsIns (i + 1) rest)
    (hl : 8 + 8 * rest.length ≤ 2 ^ 64) (hal : (get s .SP).toNat % 16 = 0)
    (hm : (region (get s .SP + BitVec.ofNat 64 (8 * i)) (8 + 8 * rest.length) ⋆ R) s.dmem)
    (ih : ∀ s₁ R₁, (get s₁ .SP).toNat % 16 = 0 →
      (region (get s₁ .SP + BitVec.ofNat 64 (8 * (i + 1))) (8 * rest.length) ⋆ R₁) s₁.dmem →
      _root_.Program.wp (armSaveRegs (i + 1) rest) (SavePost (i + 1) rest R₁ s₁)
        (fun _ _ => False) s₁) :
    _root_.Program.wp (armSaveRegs i (r1 :: rest))
      (SavePost i (r1 :: rest) R s) (fun _ _ => False) s := by
  dsimp only [armSaveRegs]; rw [hi, emitClean_append]
  rw [region_split hl, show get s .SP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8 =
    get s .SP + BitVec.ofNat 64 (8 * (i + 1)) from arm_sp_slot8 _ i] at hm
  refine armWp_append (armSlotSt_wp i r1
    (R := region (get s .SP + BitVec.ofNat 64 (8 * (i + 1))) (8 * rest.length) ⋆ R)
    s h1 hal (sep_cast hm (by ac_rfl))) ?_
  rintro s₁ ⟨hsp1, hx1, hst1, hdmem1⟩; have hsp : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
  refine armWp_mono (ih s₁ (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s r1) ⋆ R)
    (hsp ▸ hal) (by rw [hsp]; exact sep_cast hdmem1 (by ac_rfl))) ?_
  rintro s' ⟨hsp2, hx2, hst2, hm2⟩
  exact arm_save_step_tl (stepRs := [r1]) hrest hsp1 hst1 hsp2 hx1 hx2 hst2 hm2 fun _ hm' => by
    simp only [List.cons_append, List.nil_append, List.map_cons, array64_cons, List.length_cons,
      List.length_nil] at hm' ⊢; rw [arm_sp_slot8]; exact sep_cast hm' (by ac_rfl)

private theorem armSaveRegs_wp [Host] (i : Nat) (rs : List Reg) {R : Mem 64 → Prop}
    (s : MachineData) (hlen : 8 * i + 8 * rs.length ≤ 2 ^ 64)
    (hrs : ∀ r ∈ rs, r ∉ armScratch) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ R) s.dmem) :
    _root_.Program.wp (armSaveRegs i rs) (SavePost i rs R s) (fun _ _ => False) s := by
  match rs with
  | [] =>
    simp only [List.length_nil, Nat.mul_zero, region_zero, emp_sep] at hmem
    exact armWp_nil ⟨rfl, fun _ _ _ => rfl, rfl,
      by simpa [List.map_nil, array64_nil, emp_sep] using hmem⟩
  | [r] =>
    refine armWp_mono (armSlotSt_wp i r s (hrs r List.mem_cons_self) hal (by simpa using hmem)) ?_
    rintro s' ⟨hsp', hx', hst', hdmem'⟩; exact ⟨hsp', hx', hst',
      by simpa only [List.map_cons, List.map_nil, array64_cons, array64_nil, sep_emp] using hdmem'⟩
  | r1 :: r2 :: rs' =>
    have htl : ∀ r ∈ r2 :: rs', r ∉ armScratch := fun r hr => hrs r (List.mem_cons_of_mem _ hr)
    have h1 := hrs r1 List.mem_cons_self
    have hm1 : (region (get s .SP + BitVec.ofNat 64 (8 * i))
        (8 + 8 * (r2 :: rs').length) ⋆ R) s.dmem := by
      simpa only [show 8 * (r1 :: r2 :: rs').length = 8 + 8 * (r2 :: rs').length by
        simp only [List.length_cons]; omega] using hmem
    have step1 (hi : armSaveRegsIns i (r1 :: r2 :: rs') =
        armSlotStIns i r1 ++ armSaveRegsIns (i + 1) (r2 :: rs')) :=
      arm_save_single_step h1 htl hi (by simp only [List.length_cons] at hlen ⊢; omega) hal hm1
        (fun s₁ _ hal₁ h => armSaveRegs_wp (i + 1) (r2 :: rs') s₁
          (by simp only [List.length_cons] at hlen ⊢; omega) htl hal₁ h)
    cases r1 with
    | SP => exact step1 (by cases r2 <;> rfl)
    | reg x1 => cases r2 with
      | SP => exact step1 rfl
      | reg x2 =>
        have hrs' : ∀ r ∈ rs', r ∉ armScratch := fun r hr => htl r (List.mem_cons_of_mem _ hr)
        have hm_p : (region (get s .SP + BitVec.ofNat 64 (8 * i))
            (8 + (8 + 8 * rs'.length)) ⋆ R) s.dmem := by
          simpa only [show 8 * (XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs').length =
            8 + (8 + 8 * rs'.length) by simp only [List.length_cons]; omega] using hmem
        exact arm_save_pair_step (fun e => (ne_of_not_mem_armScratch h1).1 (e ▸ rfl))
          (fun e => (ne_of_not_mem_armScratch (htl _ List.mem_cons_self)).1 (e ▸ rfl))
          hrs' (by simp only [List.length_cons] at hlen; omega) hal hm_p (fun s₁ _ hal₁ h =>
            armSaveRegs_wp (i + 2) rs' s₁ (by simp only [List.length_cons] at hlen; omega)
              hrs' hal₁ h)
termination_by rs.length
decreasing_by all_goals simp only [List.length_cons]; omega

private theorem arm_restore_pair_step [Host] {i : Nat} {x1 x2 : XReg} {rs' : List Reg}
    {R : Mem 64 → Prop} {s₀ s : MachineData}
    (hnd : (XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs').Nodup)
    (hsub : ∀ r ∈ (XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs'), r ∈ armFrame.calleeSaved)
    (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (array64 (get s .SP + BitVec.ofNat 64 (8 * i))
      ((XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs').map (get s₀)) ⋆ R) s.dmem)
    (ih : ∀ s₁ R₁, (get s₁ .SP).toNat % 16 = 0 →
      (array64 (get s₁ .SP + BitVec.ofNat 64 (8 * (i + 2))) (rs'.map (get s₀)) ⋆ R₁) s₁.dmem →
      _root_.Program.wp (armRestoreRegs (i + 2) rs')
        (RestorePost rs' s₀ s₁) (fun _ _ => False) s₁) :
    _root_.Program.wp (armRestoreRegs i (.reg x1 :: .reg x2 :: rs'))
      (RestorePost (.reg x1 :: .reg x2 :: rs') s₀ s) (fun _ _ => False) s := by
  have hr12 : x1 ≠ x2 := fun e => (List.nodup_cons.mp hnd).1 (by simp [e])
  have ⟨hr1_16, hr1_17⟩ := arm_cs_ne_scratch (hsub (.reg x1) List.mem_cons_self)
  have ⟨hr2_16, hr2_17⟩ := arm_cs_ne_scratch
    (hsub (.reg x2) (List.mem_cons_of_mem _ List.mem_cons_self))
  have hmem' := arm_frame_pair_array64 (by simpa only [List.map_cons] using hmem)
  dsimp only [armRestoreRegs, armRestoreRegsIns]; rw [emitClean_append]
  refine armWp_append (armLdpSpXReg_wp x1 x2 (8 * i) (get s₀ (.reg x1)) (get s₀ (.reg x2)) s
    hr12 hr1_16 hal hmem') ?_; rintro s₁ ⟨hsp1, hr1_eq, hr2_eq, hx1, hst1, hd1⟩
  have hsp : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
  refine armWp_mono (ih s₁ (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s₀ (.reg x1)) ⋆
      (cell64 (get s .SP + BitVec.ofNat 64 (8 * i + 8)) (get s₀ (.reg x2)) ⋆ R))
    (hsp ▸ hal) (by rw [hsp, hd1]; exact sep_cast hmem' (by ac_rfl))) ?_
  rintro s' ⟨hsp2, hres2, hx2, hst2, hd2⟩
  refine ⟨hsp2.trans hsp, fun q hq => ?_, fun x hx h16 h17 => ?_, hst2.trans hst1, hd2.trans hd1⟩
  · rcases List.mem_cons.mp hq with rfl | hq
    · rw [hx2 x1 (fun hm => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hm)) hr1_16 hr1_17,
        get_reg, hr1_eq]
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [hx2 x2 (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hr2_16 hr2_17, get_reg, hr2_eq]
      · exact hres2 q hq
  · simp only [List.mem_cons, XRegOrSp.reg.injEq, not_or] at hx
    rw [hx2 x hx.2.2 h16 h17, get_reg, hx1 x hx.1 hx.2.1 h16]; rfl

private theorem armRestoreRegs_wp [Host] (i : Nat) (rs : List Reg) {R : Mem 64 → Prop}
    (s₀ s : MachineData) (hnd : rs.Nodup) (hsub : ∀ r ∈ rs, r ∈ armFrame.calleeSaved)
    (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (array64 (get s .SP + BitVec.ofNat 64 (8 * i)) (rs.map (get s₀)) ⋆ R) s.dmem) :
    _root_.Program.wp (armRestoreRegs i rs) (RestorePost rs s₀ s) (fun _ _ => False) s := by
  match rs with
  | [] =>
    exact armWp_nil ⟨rfl, fun _ h => False.elim (List.not_mem_nil h), fun _ _ _ _ => rfl, rfl, rfl⟩
  | [r] =>
    have hsp_ne : .SP ≠ r := fun e => by
      have h := hsub r List.mem_cons_self; rw [← e] at h; simp at h
    have hmem1 : (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s₀ r) ⋆ R) s.dmem := by
      simpa only [List.map_cons, List.map_nil, array64_cons, array64_nil, sep_emp] using hmem
    refine armWp_mono (armSlotLd_wp r i (get s₀ r) s hal hmem1) ?_; rintro s' ⟨hr, hk, hst', hd⟩
    refine ⟨hk .SP hsp_ne (by simp [armScratch]), fun q hq => ?_, fun x h1 h16 h17 => ?_, hst', hd⟩
    · simp only [List.mem_singleton] at hq; subst hq; exact hr
    · exact hk (.reg x) (fun e => h1 (by simp [e])) (fun h => by
        simp only [armScratch, List.mem_cons, List.not_mem_nil, or_false, XRegOrSp.reg.injEq] at h
        exact h.elim h16 h17)
  | .SP :: _ => exact absurd (hsub .SP List.mem_cons_self) (by simp)
  | .reg _ :: .SP :: _ =>
    exact absurd (hsub .SP (List.mem_cons_of_mem _ List.mem_cons_self)) (by simp)
  | .reg x1 :: .reg x2 :: rs' =>
    have hnd' : rs'.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
    have hsub' : ∀ r ∈ rs', r ∈ armFrame.calleeSaved := fun r hr =>
      hsub r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    exact arm_restore_pair_step hnd hsub hal hmem (fun s₁ _ hal₁ hm₁ =>
      armRestoreRegs_wp (i + 2) rs' s₀ s₁ hnd' hsub' hal₁ hm₁)
termination_by rs.length
decreasing_by simp only [List.length_cons]; omega

end Arm64PairStepKit

/-! ## 4. `FrameTarget` snippet specifications -/

private theorem armPrologue_spec {h : Host} {k ns : Nat} {s : MachineData} {ra : Int64}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hra : get s (.reg .X30) = ra.toBitVec) (hsp : (get s .SP).toNat % 16 = 0)
    (hF : armFrameSize ns ≤ 2 ^ 64)
    (hmem : s.dmem =⋆ region (get s .SP) 0 ⋆
      region (get s .SP - BitVec.ofNat 64 (armFrameSize ns)) (armFrameSize ns) ⋆ G) :
    armMach.FallsTo armCondReads h k (armPrologue ns).1 (.SP :: [.reg .X30] ++ armScratch) []
      (armPrologue ns).2 s (fun s' => get s' .SP = get s .SP - BitVec.ofNat 64 (armFrameSize ns) ∧
        (s'.dmem =⋆ (cell64 (get s .SP - BitVec.ofNat 64 (armFrameSize ns) + BitVec.ofNat 64
          (8 * ns)) ra.toBitVec ⋆ region (get s .SP - BitVec.ofNat 64 (armFrameSize ns) +
          BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8)) ⋆
          region (get s .SP - BitVec.ofNat 64 (armFrameSize ns)) (8 * ns) ⋆ G)) post := by
  letI := h; rw [region_zero, emp_sep, region_frame_split_ra (armFrameSize_ge ns) hF] at hmem
  let sp' := get s .SP - BitVec.ofNat 64 (armFrameSize ns)
  have hm' : s.dmem =⋆ region (sp' + BitVec.ofNat 64 (8 * ns)) 8 ⋆ (region sp' (8 * ns) ⋆
      region (sp' + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8) ⋆ G) :=
    sep_cast hmem (by dsimp only [sp']; ac_rfl)
  apply armFallsTo_of_wp; dsimp only [armPrologue, armPrologueIns]; rw [emitClean_append]
  refine armWp_append (armSpOp_wp true (armFrameSize ns) s) ?_; rintro s₁ ⟨hsp1, hx1, hst1, hd1⟩
  have hsp₁ : get s₁ .SP = sp' := by simp [get_sp, hsp1, sp']
  refine armWp_mono (armStSpXReg_wp .X30 (8 * ns) s₁ (by decide)
    (hsp₁ ▸ aligned16_sub hsp (armFrameSize_mod ns)) (by rw [hsp₁, hd1]; exact hm')) ?_
  rintro s' ⟨hsp2, hx2, hst2, hm2⟩
  rw [hsp₁, show get s₁ (.reg .X30) = ra.toBitVec by
    rw [get_reg, hx1 .X30 (by decide)]; exact hra] at hm2; dsimp only [sp'] at hm2
  refine ⟨⟨by simp [get_sp, hsp2, hsp1], sep_cast hm2 (by ac_rfl)⟩,
    armFrame_upd_regs (armKeep_regs _ (fun e => absurd List.mem_cons_self e) (fun x hx => by
      have h16 : x ≠ .X16 := fun e => hx (by simp [e, armScratch])
      rw [hx2 x h16, hx1 x h16])) (Or.inr (hst2.trans hst1))⟩

private theorem armEpilogue_spec {h : Host} {k ns : Nat} {s : MachineData} {ra : Int64}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hsp : (get s .SP).toNat % 16 = 0) (_hF : armFrameSize ns ≤ 2 ^ 64)
    (hmem : s.dmem =⋆ (cell64 (get s .SP + BitVec.ofNat 64 (armFrameSize ns) -
        BitVec.ofNat 64 (armFrameSize ns) + BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆
      region (get s .SP + BitVec.ofNat 64 (armFrameSize ns) - BitVec.ofNat 64 (armFrameSize ns) +
        BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8)) ⋆ G) :
    armMach.FallsTo armCondReads h k (armEpilogue ns).1 (.SP :: [.reg .X30] ++ armScratch) []
      (armEpilogue ns).2 s (fun s' => get s' .SP = get s .SP + BitVec.ofNat 64 (armFrameSize ns) ∧
        get s' (.reg .X30) = ra.toBitVec ∧ (s'.dmem =⋆ region (get s .SP +
          BitVec.ofNat 64 (armFrameSize ns)) 0 ⋆ region (get s .SP + BitVec.ofNat 64 (8 * ns))
          (armFrameSize ns - 8 * ns) ⋆ G)) post := by
  letI := h; rw [BitVec.add_sub_cancel] at hmem
  have hm' : (cell64 (get s .SP + BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆
      (region (get s .SP + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8) ⋆ G))
      s.dmem := sep_cast hmem (by ac_rfl)
  apply armFallsTo_of_wp; dsimp only [armEpilogue, armEpilogueIns]; rw [emitClean_append]
  refine armWp_append (armLdSpXReg_wp .X30 (8 * ns) ra.toBitVec s hsp hm') ?_
  rintro s₁ ⟨hsp1, hx30, hx1, hst1, hd1⟩
  refine armWp_mono (armSpOp_wp false (armFrameSize ns) s₁) ?_; rintro s' ⟨hsp2, hx2, hst2, hd2⟩
  have hge := armFrameSize_ge ns
  have hsp_eq : region (get s .SP + BitVec.ofNat 64 (8 * ns)) (armFrameSize ns - 8 * ns) =
      (region (get s .SP + BitVec.ofNat 64 (8 * ns)) 8 ⋆ region
        (get s .SP + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8)) := by
    conv => lhs; rw [show armFrameSize ns - 8 * ns = 8 + (armFrameSize ns - 8 * ns - 8) by omega]
    exact region_split (by omega)
  refine ⟨⟨by simp [get_sp, hsp2, hsp1], by rw [get_reg, hx2 .X30 (by decide), hx30], by
    rw [region_zero, emp_sep, hsp_eq]
    exact sep_cast (sep_mono (fun _ => cell64_region) (by rw [hd2, hd1]; exact hm')) (by ac_rfl)⟩,
    armFrame_upd_regs (armKeep_regs _ (fun e => absurd List.mem_cons_self e) (fun x hx => by
      have h16 : x ≠ .X16 := fun e => hx (by simp [e, armScratch])
      rw [hx2 x h16, hx1 x (fun e => hx (by simp [e])) h16])) (Or.inr (hst2.trans hst1))⟩

private theorem armSlotSt_spec {h : Host} {k i : Nat} {r : Reg} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hr : r ∉ armScratch) (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ G) :
    armMach.FallsTo armCondReads h k (armSlotSt i r) armScratch [] maskNone s
      (fun s' => s'.dmem =⋆ cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s r) ⋆ G) post :=
  letI := h; armFallsTo_of_wp (armWp_mono (armSlotSt_wp i r s hr hsp hmem)
    (fun _ ⟨hsp', hx', hst', hd⟩ => ⟨hd, armFrame_keep_scratch hsp' hx' hst'⟩))

private theorem armSlotLd_spec {h : Host} {k i : Nat} {rd : Reg} {v : BitVec 64} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (_hrd : rd ∉ armScratch) (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) v ⋆ G) :
    armMach.FallsTo armCondReads h k (armSlotLd rd i) (rd :: armScratch) [] maskNone s
      (fun s' => get s' rd = v ∧ s'.dmem = s.dmem) post :=
  letI := h; armFallsTo_of_wp (armWp_mono (armSlotLd_wp rd i v s hsp hmem)
    (fun _ ⟨hv, hk, hst', hd⟩ => ⟨⟨hv, hd⟩, armFrame_upd_regs (fun r hr => by
      rw [List.mem_cons, not_or] at hr; exact hk r hr.1 hr.2) (Or.inr hst')⟩))

private theorem armSaveRegs_spec {h : Host} {k i : Nat} {rs : List Reg} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hlen : 8 * i + 8 * rs.length ≤ 2 ^ 64) (hrs : ∀ r ∈ rs, r ∉ armScratch)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ G) :
    armMach.FallsTo armCondReads h k (armSaveRegs i rs) armScratch [] maskNone s
      (fun s' => s'.dmem =⋆ array64 (get s .SP + BitVec.ofNat 64 (8 * i)) (rs.map (get s)) ⋆ G)
      post :=
  letI := h; armFallsTo_of_wp (armWp_mono (armSaveRegs_wp i rs s hlen hrs hsp hmem)
    (fun _ ⟨hsp', hx', hst', hd⟩ => ⟨hd, armFrame_keep_scratch hsp' hx' hst'⟩))

private theorem armRestoreRegs_spec {h : Host} {k i : Nat} {rs : List Reg} {s₀ s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hnd : rs.Nodup) (hsub : ∀ r ∈ rs, r ∈ armFrame.calleeSaved)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ array64 (get s .SP + BitVec.ofNat 64 (8 * i)) (rs.map (get s₀)) ⋆ G) :
    armMach.FallsTo armCondReads h k (armRestoreRegs i rs) (rs ++ armScratch) [] maskNone s
      (fun s' => (∀ r ∈ rs, get s' r = get s₀ r) ∧ s'.dmem = s.dmem) post := by
  letI := h; refine armFallsTo_of_wp (armWp_mono (armRestoreRegs_wp i rs s₀ s hnd hsub hsp hmem) ?_)
  rintro s' ⟨hsp', hres, hx', hst', hd⟩; refine ⟨⟨hres, hd⟩, armFrame_upd_regs (fun r hr => ?_)
    (Or.inr hst')⟩; rw [List.mem_append, not_or] at hr
  cases r with | SP => exact hsp' | reg x =>
    have hsc := ne_of_not_mem_armScratch hr.2
    exact hx' x hr.1 (fun e => hsc.1 (e ▸ rfl)) (fun e => hsc.2 (e ▸ rfl))

private theorem armCanonAbi_spec {h : Host} {k : Nat} {t : Ty} {r : Reg} {v : Val t}
    {s : MachineData} {post : MachineState → Prop}
    (ht : t = .bool ∨ ∃ n ∈ [8, 16, 32, 64], t = .bits n)
    (_hr : r ∉ armScratch) (hh : GprHolds (get s r) t v) :
    armMach.FallsTo armCondReads h k (armCanonAbi t r).1 (r :: armScratch) []
      (armCanonAbi t r).2 s (fun s' => AbiGprHolds (get s' r) t v ∧ s'.dmem = s.dmem) post := by
  letI := h
  by_cases h64 : t = .bits 64
  · subst h64; cases r <;> exact Machine.FallsTo.nil ⟨abiGprHolds_bits64_of_gprHolds hh, rfl⟩
  · have htS : t = .bool ∨ ∃ n ∈ [8, 16, 32], t = .bits n := by
      rcases ht with rfl | ⟨n, hn, rfl⟩; · exact Or.inl rfl
      · refine Or.inr ⟨n, ?_, rfl⟩; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl <;> first | (simp; done) | exact absurd rfl h64
    cases r with
    | reg x =>
      apply armFallsTo_of_wp; refine armWp_mono (armCanonAbiXReg_wp s htS hh) ?_
      rintro _ ⟨s'', rfl, hregs, hst, hd, hAbi⟩; refine ⟨⟨hAbi, hd⟩, armFrame_upd_regs
        (armKeep_regs _ (fun _ => by rw [hregs]; exact Reg64s.SP_setXReg _ _ _) (fun y hy => by
          rw [hregs]
          exact Reg64s.getXReg_setXReg_of_ne _ _ _ _ (Ne.symm fun (e : y = x) => hy (by simp [e]))))
        (Or.inr hst)⟩
    | SP =>
      have hcan : armCanonAbi t .SP = (emitClean ([armMovToXI .X16 .SP] ++
          armCanonAbiXRegIns t .X16 ++ [armMovToSpI .X16]), maskNone) := by
        rcases htS with rfl | ⟨n, hn, rfl⟩; · rfl
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          have hc : (n == 8 || n == 16 || n == 32) = true := by
            rcases hn with rfl | rfl | rfl <;> decide
          simp [armCanonAbi, armCanonAbiIns, hc]
      apply armFallsTo_of_wp; rw [hcan]; dsimp only [Prod.fst, Prod.snd]
      simp only [emitClean_append]
      refine armWp_cons (armMovToX_wp .X16 .SP s) ?_; rintro _ rfl
      refine armWp_append (armCanonAbiXReg_wp _ htS (by simpa [get_wr_same] using hh)) ?_
      rintro s₂ ⟨s'', rfl, hregs, hst, hd, hAbi⟩
      refine armWp_mono (armMovToSp_wp .X16 s₂) ?_; rintro _ rfl
      refine ⟨⟨by simpa [get_sp] using hAbi, hd⟩, armFrame_upd_regs
        (armKeep_regs _ (fun e => absurd List.mem_cons_self e) (fun y hy => by
          have hy16 : y ≠ .X16 := fun e => hy (by simp [e, armScratch])
          change s₂.regs.getXReg y = s.regs.getXReg y
          rw [hregs, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy16.symm,
            Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy16.symm])) (Or.inr hst)⟩

private theorem armCall_spec {h : Host} {k : Nat} {sym : Sym} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop} (hc : [armCallD sym].IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ region (get s .SP - 0#64) 0 ⋆ G)
    (hk : ∀ s' : MachineData, get s' .SP = get s .SP - 0#64 →
      armMach.Frame armCondReads s s' (.SP :: [.reg .X30] ++ armScratch) [] maskAll →
      get s' (.reg .X30) = (Host.addrOf (k + 1)).toBitVec → (s'.dmem =⋆ region (get s' .SP) 0 ⋆ G) →
      Eventually (step1 Host.exe) post ⟨s', hostLabel h sym⟩) : armMach.Run h k s post := by
  letI := h; refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [armCallD]; simp only [t_step_simp, Reg64s.setRegOrZr_reg64]
  rw [show BitVec.ofInt 64 (Host.addrOf (k + 1)).toInt = (Host.addrOf (k + 1)).toBitVec by
    rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]]
  refine hk (wr s .X30 (Host.addrOf (k + 1)).toBitVec) (by simp [get_sp]) ?_
    (get_wr_same _ _ _) (by simpa [get_sp] using hmem)
  exact armFrame_upd_regs (armKeep_regs _ (fun _ => rfl) (fun y hy =>
    Reg64s.getXReg_setXReg_of_ne _ _ _ _ (fun e => hy (by simp [e])))) (Or.inl rfl)

private theorem armExitJmp_spec {h : Host} {k : Nat} {sym : Sym} {s : MachineData}
    {post : MachineState → Prop} (hc : [armJmpD sym].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData, armMach.Frame armCondReads s s' armScratch [] maskNone →
      s'.dmem = s.dmem → Eventually (step1 Host.exe) post ⟨s', hostLabel h sym⟩) :
    armMach.Run h k s post := by
  letI := h; refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [armJmpD]; simp only [t_step_simp]
  exact hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone) rfl

private theorem armRet_spec {h : Host} {k : Nat} {s : MachineData} {ra : Int64}
    {post : MachineState → Prop} (hc : [armRetD].IsInfixAt Host.prog k)
    (hra : get s (.reg .X30) = ra.toBitVec) (hk : ∀ s' : MachineData,
      armMach.KeepsGpr s s' (.SP :: armScratch) → armMach.KeepsVec s s' [] →
      get s' .SP = get s .SP + 0#64 → s'.dmem = s.dmem →
      Eventually (step1 Host.exe) post ⟨s', ra⟩) : armMach.Run h k s post := by
  letI := h; refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [armRetD]; simp only [t_step_simp, Reg64s.getRegOrZr_reg64]
  rw [show Int64.ofInt (s.regs.getXReg .X30).toBitVec.signed = ra by
    rw [show (s.regs.getXReg .X30).toBitVec = ra.toBitVec from hra]
    simp [BitVec.signed, Int64.toInt_toBitVec, Int64.ofInt_toInt]]
  exact hk s (fun _ _ => rfl) (fun v => v.elim) (by simp) rfl

theorem armSymAddrReg_spec {h : Host} {k : Nat} {sym : Sym} {rd : Reg} {s : MachineData}
    {post : MachineState → Prop} (hrd : rd ≠ armFrame.sp ∧ rd ∉ armFrame.scratch) :
    armMach.FallsTo armCondReads h k (armSymAddrReg sym rd) (rd :: armScratch) [] maskNone s
      (fun s' => armMach.getGpr s' rd = (armMach.labelAddr h sym).toBitVec ∧ s'.dmem = s.dmem)
      post := by
  cases rd with
  | SP => exact absurd rfl hrd.1
  | reg x =>
    exact Machine.FallsTo.weaken (armSymAddr_spec (h := h) (k := k) (d := x) (sym := sym))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact List.mem_cons_self)
      (fun _ hv => False.elim (List.not_mem_nil hv)) rfl

theorem armCallReg_spec {h : Host} {k : Nat} {r : Reg} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hr : r ∈ armFrame.allocatable)
    (hc : (armCallReg r).IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ region (get s .SP - 0#64) 0 ⋆ G)
    (hk : ∀ s' : MachineData,
      get s' .SP = get s .SP - 0#64 →
      armMach.Frame armCondReads s s' (.SP :: [.reg .X30] ++ armScratch) [] maskAll →
      get s' (.reg .X30) = (Host.addrOf (k + (armCallReg r).length)).toBitVec →
      (s'.dmem =⋆ region (get s' .SP) 0 ⋆ G) →
      Eventually (step1 Host.exe) post ⟨s', Int64.ofBitVec (get s r)⟩) :
    armMach.Run h k s post := by
  cases r with
  | SP => simp at hr
  | reg x =>
    letI := h
    refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
    simp only [t_step_simp, Reg64s.setRegOrZr_reg64, getRegOrZr_zr, RegWidth.bits,
      MemWidth.bits, BitVec.setWidth_eq]
    have hra : BitVec.ofInt 64 (Host.addrOf (k + 1)).toInt =
        (Host.addrOf (k + 1)).toBitVec := by
      rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
    have hpc : Int64.ofInt (s.regs.getXReg x).toBitVec.signed =
        Int64.ofBitVec (s.regs.getXReg x).toBitVec := by
      rw [← Int64.toBitVec_ofBitVec (s.regs.getXReg x).toBitVec]
      simp [BitVec.signed]
    rw [hra, hpc]
    refine hk (wr s .X30 (Host.addrOf (k + 1)).toBitVec) (by simp [get_sp]) ?_
      (get_wr_same _ _ _) (by simpa [get_sp] using hmem)
    refine armFrame_upd_regs (armKeep_regs _ (fun _ => rfl) (fun y hy => ?_)) (Or.inl rfl)
    have hy30 : y ≠ .X30 := fun e => hy (by simp [e])
    exact Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy30.symm

theorem armJmpReg_spec {h : Host} {k : Nat} {r : Reg} {s : MachineData}
    {post : MachineState → Prop}
    (hr : r ∈ armFrame.allocatable)
    (hc : (armJmpReg r).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      armMach.Frame armCondReads s s' armScratch [] maskNone → s'.dmem = s.dmem →
      Eventually (step1 Host.exe) post ⟨s', Int64.ofBitVec (get s r)⟩) :
    armMach.Run h k s post := by
  cases r with
  | SP => simp at hr
  | reg x =>
    letI := h
    refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
    simp only [t_step_simp, getRegOrZr_zr, RegWidth.bits, MemWidth.bits,
      BitVec.setWidth_eq]
    have hpc : Int64.ofInt (s.regs.getXReg x).toBitVec.signed =
        Int64.ofBitVec (s.regs.getXReg x).toBitVec := by
      rw [← Int64.toBitVec_ofBitVec (s.regs.getXReg x).toBitVec]
      simp [BitVec.signed]
    rw [hpc]
    exact hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone) rfl

/-! ## 5. `armFrameSpec : FrameTarget armMach armFrame armCondReads` -/

theorem armFrameSpec_spec : FrameSpec armMach armFrame armCondReads armFramePreds := {
  sp_disj := by simp, scratch_disj := by simp, cs_disj := by simp, ra_disj := by simp,
  argRegs_nodup := by decide, retRegs_nodup := by decide, retAddr_region := fun _ _ _ h => h,
  raReg_of_raRegs := fun _ _ _ h hra => by
    dsimp [armFramePreds] at hra ⊢; rw [← hra]; exact h (.reg .X30) (by simp),
  slots_le_frameSize := armFrameSize_slots,
  spOk_frame := fun _ ns h => aligned16_sub h (armFrameSize_mod ns),
  spEntry_call := fun _ ns h => by
    simpa [BitVec.sub_zero] using aligned16_sub h (armFrameSize_mod ns),
  labelAddr_eq := fun {h} {_} {_} hk hf => letI := h; Host.label_eq_addrOf hk hf,
  label_spec := fun {h} {_} {_} {_} {_} hi hrun => letI := h; Host.eventually_label hi hrun,
  prologue_spec := fun {h} {_} {_} {_} {_} {_} {_} hra hsp _ hm =>
    letI := h; armPrologue_spec hra hsp (by omega) hm,
  epilogue_spec := fun {h} {_} {_} {_} {_} {_} {_} hsp _ hm =>
    letI := h; armEpilogue_spec hsp (by omega) hm,
  slotSt_spec := fun {h} {_} {_} {_} {_} {_} {_} hr hsp hm => letI := h; armSlotSt_spec hr hsp hm,
  slotLd_spec := fun {h} {_} {_} {_} {_} {_} {_} {_} hrd hsp hm =>
    letI := h; armSlotLd_spec hrd hsp hm,
  saveRegs_spec := fun {fn h k i rs s G post} hfn hl hrs hsp hm => by
    cases hfn; letI := h; exact armSaveRegs_spec hl hrs hsp hm,
  restoreRegs_spec := fun {fn h k i rs s₀ s G post} hfn hnd hsub hsp hm => by
    cases hfn; letI := h; exact armRestoreRegs_spec hnd hsub hsp hm,
  canonAbi_spec := fun {h} {_} {_} {_} {_} {_} {_} ht hr hh =>
    letI := h; armCanonAbi_spec ht hr hh,
  call_spec := fun {h} {_} {_} {_} {_} {_} hc hm hk => letI := h; armCall_spec hc hm hk,
  exitJmp_spec := fun {h} {_} {_} {_} {_} hc hk => letI := h; armExitJmp_spec hc hk,
  ret_spec := fun {h} {_} {_} {_} {_} {_} hc hra _ hk => letI := h; armRet_spec hc hra hk }

@[expose] def armFrameSpec : FrameTarget armMach armFrame armCondReads where
  toFramePreds := armFramePreds; spec := armFrameSpec_spec

/-! ## 6. `NoLab` lemmas -/

section NoLab
open Kraken (Directive)
theorem armPrologue_noLab (ns : Nat) (l : Sym) :
    Directive.label l ∉ (armFrame.prologue ns).1 := emitClean_noLab _ l
theorem armEpilogue_noLab (ns : Nat) (l : Sym) :
    Directive.label l ∉ (armFrame.epilogue ns).1 := emitClean_noLab _ l
theorem armSlotSt_noLab (i : Nat) (r : Reg) (l : Sym) :
    Directive.label l ∉ armFrame.slotSt i r := emitClean_noLab _ l
theorem armSlotLd_noLab (rd : Reg) (i : Nat) (l : Sym) :
    Directive.label l ∉ armFrame.slotLd rd i := emitClean_noLab _ l
theorem armSaveRegs_noLab (base : Nat) (rs : List Reg) (l : Sym) :
    Directive.label l ∉ armSaveRegs base rs := emitClean_noLab _ l
theorem armRestoreRegs_noLab (base : Nat) (rs : List Reg) (l : Sym) :
    Directive.label l ∉ armRestoreRegs base rs := emitClean_noLab _ l
theorem armCanonAbi_noLab (t : Ty) (r : Reg) (l : Sym) :
    Directive.label l ∉ (armFrame.canonAbi t r).1 := emitClean_noLab _ l
theorem armCall_noLab (sym l : Sym) : Directive.label l ∉ armFrame.call sym := emitClean_noLab _ l
theorem armExitJmp_noLab (sym l : Sym) : Directive.label l ∉ armFrame.exitJmp sym :=
  emitClean_noLab _ l
theorem armRet_noLab (l : Sym) : Directive.label l ∉ armFrame.ret := emitClean_noLab _ l
theorem armSymAddrReg_noLab (sym : Sym) (rd : Reg) (l : Sym) :
    Directive.label l ∉ armSymAddrReg sym rd := by
  cases rd with
  | reg x => exact armSymAddr_noLab x sym l
  | SP => simp [armSymAddrReg]
theorem armCallReg_noLab (r : Reg) (l : Sym) : Directive.label l ∉ armCallReg r :=
  emitClean_noLab _ l
theorem armJmpReg_noLab (r : Reg) (l : Sym) : Directive.label l ∉ armJmpReg r :=
  emitClean_noLab _ l
end NoLab

/-! ## 7. `ParserChecks` (`Kraken.AArch64.Parser`) -/

section ParserChecks
open Kraken.AArch64.Parser

example : ⸨prog| sub sp, sp, #16
  str x30, [sp, #0] ⸩ = (armFrame.prologue 0).1 := rfl
example : ⸨prog| ldr x30, [sp, #0]
  add sp, sp, #16 ⸩ = (armFrame.epilogue 0).1 := rfl
example : ⸨prog| ldr x16, =4096
  sub sp, sp, x16
  str x30, [sp, #4080] ⸩ = (armFrame.prologue 510).1 := rfl
example : ⸨prog| ldr x16, =32784
  sub sp, sp, x16
  ldr x16, =32768
  str x30, [sp, x16] ⸩ = (armFrame.prologue 4096).1 := rfl
example : ⸨prog| ldr x16, =32768
  ldr x30, [sp, x16]
  ldr x16, =32784
  add sp, sp, x16 ⸩ = (armFrame.epilogue 4096).1 := rfl
example : ⸨prog| str x0, [sp, #8] ⸩ = armFrame.slotSt 1 (.reg .X0) := rfl
example : ⸨prog| ldr x0, [sp, #8] ⸩ = armFrame.slotLd (.reg .X0) 1 := rfl
example : ⸨prog| ldr x16, =32768
  str x0, [sp, x16] ⸩ = armFrame.slotSt 4096 (.reg .X0) := rfl
example : ⸨prog| ldr x16, =32768
  ldr x0, [sp, x16] ⸩ = armFrame.slotLd (.reg .X0) 4096 := rfl
example : ⸨prog| mov x17, sp
  str x17, [sp, #8] ⸩ = armFrame.slotSt 1 .SP := rfl
example : ⸨prog| ldr x17, [sp, #8]
  mov sp, x17 ⸩ = armFrame.slotLd .SP 1 := rfl
example : ⸨prog| stp x19, x20, [sp, #0]
  stp x21, x22, [sp, #16] ⸩ = armSaveRegs 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22] := rfl
example : ⸨prog| stp x19, x20, [sp, #8]
  str x21, [sp, #24] ⸩ = armSaveRegs 1 [.reg .X19, .reg .X20, .reg .X21] := rfl
example : ⸨prog| stp x19, x20, [sp, #504] ⸩ = armSaveRegs 63 [.reg .X19, .reg .X20] := rfl
example : ⸨prog| str x19, [sp, #512]
  str x20, [sp, #520] ⸩ = armSaveRegs 64 [.reg .X19, .reg .X20] := rfl
example : ⸨prog| ldp x19, x20, [sp, #0]
  ldp x21, x22, [sp, #16] ⸩ = armRestoreRegs 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22] := rfl
example : ⸨prog| ldp x19, x20, [sp, #8]
  ldr x21, [sp, #24] ⸩ = armRestoreRegs 1 [.reg .X19, .reg .X20, .reg .X21] := rfl
example : ⸨prog| ldp x19, x20, [sp, #504] ⸩ = armRestoreRegs 63 [.reg .X19, .reg .X20] := rfl
example : ⸨prog| ldr x19, [sp, #512]
  ldr x20, [sp, #520] ⸩ = armRestoreRegs 64 [.reg .X19, .reg .X20] := rfl
example : ⸨prog| uxtb x0, w0 ⸩ = (armFrame.canonAbi .bool (.reg .X0)).1 := rfl
example : ⸨prog| uxtb x0, w0 ⸩ = (armFrame.canonAbi i8 (.reg .X0)).1 := rfl
example : ⸨prog| uxth x0, w0 ⸩ = (armFrame.canonAbi i16 (.reg .X0)).1 := rfl
example : ⸨prog| mov w0, w0 ⸩ = (armFrame.canonAbi i32 (.reg .X0)).1 := rfl
example : ⸨prog| mov x16, sp
  uxtb x16, w16
  mov sp, x16 ⸩ = (armFrame.canonAbi i8 .SP).1 := rfl
example : ⸨prog| bl f ⸩ = armFrame.call "f" := rfl
example : ⸨prog| b f ⸩ = armFrame.exitJmp "f" := rfl
example : ⸨prog| ret ⸩ = armFrame.ret := rfl
example : ⸨prog|
  adrp x0, f
  add x0, x0, :lo12:f
⸩ = armSymAddrReg "f" (.reg .X0) := rfl
example : ⸨prog| blr x8 ⸩ = armCallReg (.reg .X8) := rfl
example : ⸨prog| br x8 ⸩ = armJmpReg (.reg .X8) := rfl

end ParserChecks

end LeanQbe.T.Arm64
