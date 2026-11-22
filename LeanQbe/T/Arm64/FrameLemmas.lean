module

public import LeanQbe.T.Arm64.Frame
public import LeanQbe.T.AbiLemmas
import Kraken.AArch64.Parser

/-!
# AAPCS64 Arm64 Frame Verification (`T11b`)

Proves `armFrameSpec : FrameTarget armMach armFrame armCondReads`, `NoLab` invariants for all
frame/slot/ABI/call snippets, and `ParserChecks` against `Kraken.AArch64.Parser`.
All frame and slot proofs hold unconditionally up to `armFrameSize ns ≤ 2 ^ 64` (using `.X16`
literal-pool + register-offset fallback for `4096 ≤ armFrameSize ns` and `32768 ≤ 8 * ns`, and
`.X16`/`.X17` routing when slot/ABI operations target `.SP`).
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
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
    simpa [get_sp] using hsp
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
  · intro c hdisj
    cases c <;> (
      dsimp only [FlagMask.disjoint, armCondReads, maskAll, maskN, maskZ, maskC, maskV] at hdisj
      exact absurd hdisj (by decide))
  · intro c _; simp [hst]

private theorem Reg64s_getXReg_setSP (regs : Reg64s) (v : UInt64) (x : XReg) :
    ({ regs with SP := v } : Reg64s).getXReg x = regs.getXReg x := by
  cases x <;> rfl

private theorem armKeep_regs {s s' : MachineData} (gClob : List Reg)
    (hsp : .SP ∉ gClob → s'.regs.SP = s.regs.SP)
    (hx : ∀ x : XReg, .reg x ∉ gClob → s'.regs.getXReg x = s.regs.getXReg x) :
    ∀ r, r ∉ gClob → get s' r = get s r := by
  intro r hr
  cases r with
  | SP => simp [get_sp, hsp hr]
  | reg x => simp [get_reg, hx x hr]

private theorem armSubSpImm_fallsTo (n : Nat) (s : MachineData) :
    armDirFallsTo
      (ins (.SUB_e (.low .SP .W64) (.low .SP .W64)
        (.imm { imm := .int64 (Int64.ofNat n), shift := .S0 }))) s
      (fun s' => s' = { s with regs := { s.regs with SP := UInt64.ofBitVec (get s .SP - BitVec.ofNat 64 n) } }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits]
  rw [ofInt_toInt_ofNat]
  exact hk _ rfl

private theorem armAddSpImm_fallsTo (n : Nat) (s : MachineData) :
    armDirFallsTo
      (ins (.ADD_e (.low .SP .W64) (.low .SP .W64)
        (.imm { imm := .int64 (Int64.ofNat n), shift := .S0 }))) s
      (fun s' => s' = { s with regs := { s.regs with SP := UInt64.ofBitVec (get s .SP + BitVec.ofNat 64 n) } }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits]
  rw [ofInt_toInt_ofNat]
  exact hk _ rfl

private theorem armSubSpX16_fallsTo (s : MachineData) :
    armDirFallsTo (ins (.SUB_e (.low .SP .W64) (.low .SP .W64) (.ext (armUxtx .X16)))) s
      (fun s' => s' = { s with regs := { s.regs with SP := UInt64.ofBitVec (get s .SP - get s (.reg .X16)) } }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits]
  dsimp only [ExtRegExpr.interp, BitVec.apply_extend, BitVec.unsigned]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  exact hk _ rfl

private theorem armAddSpX16_fallsTo (s : MachineData) :
    armDirFallsTo (ins (.ADD_e (.low .SP .W64) (.low .SP .W64) (.ext (armUxtx .X16)))) s
      (fun s' => s' = { s with regs := { s.regs with SP := UInt64.ofBitVec (get s .SP + get s (.reg .X16)) } }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits]
  dsimp only [ExtRegExpr.interp, BitVec.apply_extend, BitVec.unsigned]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  exact hk _ rfl

private theorem armSubSp_wp [Host] (n : Nat) (s : MachineData) :
    _root_.Program.wp (armSubSp n)
      (fun s' => s'.regs.SP = UInt64.ofBitVec (get s .SP - BitVec.ofNat 64 n) ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem) (fun _ _ => False) s := by
  dsimp only [armSubSp, armSubSpIns]
  simp only [emitClean_ite]
  split
  · refine armWp_mono (armDirFallsTo_wp (armSubSpImm_fallsTo n s)) ?_
    rintro s' rfl
    exact ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
  · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 n) s) ?_
    rintro s₁ rfl
    refine armWp_mono (armDirFallsTo_wp (armSubSpX16_fallsTo (wr s .X16 (BitVec.ofNat 64 n)))) ?_
    rintro s' rfl
    refine ⟨?_, fun x hx => ?_, rfl, rfl⟩
    · simp [get_sp, get_wr_same]
    · dsimp only
      rw [Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm]

private theorem armAddSp_wp [Host] (n : Nat) (s : MachineData) :
    _root_.Program.wp (armAddSp n)
      (fun s' => s'.regs.SP = UInt64.ofBitVec (get s .SP + BitVec.ofNat 64 n) ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem) (fun _ _ => False) s := by
  dsimp only [armAddSp, armAddSpIns]
  simp only [emitClean_ite]
  split
  · refine armWp_mono (armDirFallsTo_wp (armAddSpImm_fallsTo n s)) ?_
    rintro s' rfl
    exact ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
  · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 n) s) ?_
    rintro s₁ rfl
    refine armWp_mono (armDirFallsTo_wp (armAddSpX16_fallsTo (wr s .X16 (BitVec.ofNat 64 n)))) ?_
    rintro s' rfl
    refine ⟨?_, fun x hx => ?_, rfl, rfl⟩
    · simp [get_sp, get_wr_same]
    · dsimp only
      rw [Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm]

private theorem armStAddr_fallsTo (r : XReg) (addr : AddrExpr) (a : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData)
    (hbase : addr.base = RegOrSp.SP)
    (hal : (get s .SP).toNat % 16 = 0)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), addr.eval s p = (a, s))
    (hmem : (region a 8 ⋆ R) s.dmem) :
    armDirFallsTo (ins (.STR (zr r .W64) addr)) s
      (fun s' => s'.regs = s.regs ∧ s'.status = s.status ∧
        (cell64 a (get s (.reg r)) ⋆ R) s'.dmem) := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  intro _ p next jmp P hk
  simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
    AddrExpr.checkSPAlignment, hbase, armCheckSP_eq_false s hal, Bool.false_eq_true, ↓reduceIte,
    haddr p, getRegOrZr_zr, RegWidth.bits, Effects.All]
  rw [store_All_of_sep _ _ .W64 _ _ _ bs R hbs hl]
  refine hk _ ⟨rfl, rfl, ?_⟩
  rw [get_reg]
  exact Mem.storeInt_sep _ 8 bs R s.dmem ⟨hbs, hl⟩ (s.regs.getXReg r).toBitVec.toInt

private theorem armLdAddr_fallsTo (rd : XReg) (addr : AddrExpr) (a v : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData)
    (hbase : addr.base = RegOrSp.SP)
    (hal : (get s .SP).toNat % 16 = 0)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), addr.eval s p = (a, s))
    (hmem : (cell64 a v ⋆ R) s.dmem) :
    armDirFallsTo (ins (.LDR (zr rd .W64) (.addr addr))) s
      (fun s' => s' = wr s rd v) := by
  intro _ p next jmp P hk
  simp only [Directive.interp, Instr.interp, Operation.interp, AddrOrLit.interpLoad,
    AddrExpr.interpLoad, AddrExpr.checkSPAlignment, hbase, armCheckSP_eq_false s hal,
    Bool.false_eq_true, ↓reduceIte, haddr p, MachineData.setRegOrZr, setRegOrZr_zr, Effects.All]
  rw [load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) R hmem (Int.toBytes_length _ _)]
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  simp only [MemWidth.bits, hv, BitVec.setWidth_eq]
  exact hk _ rfl

private theorem armStSpXReg_wp [Host] (r : XReg) (o : Nat) {R : Mem 64 → Prop} (s : MachineData)
    (hr : r ≠ .X16) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 o) 8 ⋆ R) s.dmem) :
    _root_.Program.wp (armStSpXReg r o)
      (fun s' => s'.regs.SP = s.regs.SP ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧
        (cell64 (get s .SP + BitVec.ofNat 64 o) (get s (.reg r)) ⋆ R) s'.dmem)
      (fun _ _ => False) s := by
  dsimp only [armStSpXReg, armStSpXRegIns]
  simp only [emitClean_ite]
  split
  · refine armWp_mono
      (armDirFallsTo_wp (armStAddr_fallsTo r (atOff .SP o) (get s .SP + BitVec.ofNat 64 o) s
        rfl hal (fun p => by rw [armAtSp_eval]; rfl) hmem)) ?_
    rintro s' ⟨hregs, hst, hdmem⟩
    exact ⟨congrArg Reg64s.SP hregs, fun _ _ => congrFun (congrArg Reg64s.getXReg hregs) _,
      hst, hdmem⟩
  · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 o) s) ?_
    rintro s₁ rfl
    have hal1 : (get (wr s .X16 (BitVec.ofNat 64 o)) .SP).toNat % 16 = 0 := by
      simpa [get_sp] using hal
    have hmem1 : (region (get s .SP + BitVec.ofNat 64 o) 8 ⋆ R)
        (wr s .X16 (BitVec.ofNat 64 o)).dmem := hmem
    refine armWp_mono
      (armDirFallsTo_wp (armStAddr_fallsTo r (armAtSpIdx .X16) (get s .SP + BitVec.ofNat 64 o)
        (wr s .X16 (BitVec.ofNat 64 o)) rfl hal1 (fun p => by
          rw [armAtSpIdx_eval]
          simp [get_sp]) hmem1)) ?_
    rintro s' ⟨hregs, hst, hdmem⟩
    have hrval : get (wr s .X16 (BitVec.ofNat 64 o)) (.reg r) = get s (.reg r) :=
      get_wr_of_ne s .X16 _ (.reg r) (fun e => hr (XRegOrSp.reg.inj e))
    rw [hrval] at hdmem
    refine ⟨?_, fun x hx => ?_, hst, hdmem⟩
    · simp [hregs]
    · rw [hregs]; simp [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm]

private theorem armLdSpXReg_wp [Host] (rd : XReg) (o : Nat) (v : BitVec 64) {R : Mem 64 → Prop}
    (s : MachineData) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (cell64 (get s .SP + BitVec.ofNat 64 o) v ⋆ R) s.dmem) :
    _root_.Program.wp (armLdSpXReg rd o)
      (fun s' => s'.regs.SP = s.regs.SP ∧
        s'.regs.getXReg rd = UInt64.ofBitVec v ∧
        (∀ x, x ≠ rd → x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  dsimp only [armLdSpXReg, armLdSpXRegIns]
  simp only [emitClean_ite]
  split
  · refine armWp_mono
      (armDirFallsTo_wp (armLdAddr_fallsTo rd (atOff .SP o) (get s .SP + BitVec.ofNat 64 o) v s
        rfl hal (fun p => by rw [armAtSp_eval]; rfl) hmem)) ?_
    rintro s' rfl
    exact ⟨Reg64s.SP_setXReg _ _ _, Reg64s.getXReg_setXReg_same _ _ _,
      fun x hx _ => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl, rfl⟩
  · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 o) s) ?_
    rintro s₁ rfl
    have hal1 : (get (wr s .X16 (BitVec.ofNat 64 o)) .SP).toNat % 16 = 0 := by
      simpa [get_sp] using hal
    refine armWp_mono
      (armDirFallsTo_wp (armLdAddr_fallsTo rd (armAtSpIdx .X16) (get s .SP + BitVec.ofNat 64 o) v
        (wr s .X16 (BitVec.ofNat 64 o)) rfl hal1 (fun p => by
          rw [armAtSpIdx_eval]
          simp [get_sp]) hmem)) ?_
    rintro s' rfl
    refine ⟨by simp, Reg64s.getXReg_setXReg_same _ _ _, fun x hxrd hx16 => ?_, rfl, rfl⟩
    rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hxrd.symm,
      Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]

private theorem armStpAddr_fallsTo (r1 r2 : XReg) (addr : AddrExpr) (a : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData)
    (hbase : addr.base = RegOrSp.SP)
    (hal : (get s .SP).toNat % 16 = 0)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), addr.eval s p = (a, s))
    (hmem : (region a 8 ⋆ (region (a + 8#64) 8 ⋆ R)) s.dmem) :
    armDirFallsTo (ins (.STP (zr r1 .W64) (zr r2 .W64) addr)) s
      (fun s' => s'.regs = s.regs ∧ s'.status = s.status ∧
        (cell64 a (get s (.reg r1)) ⋆ (cell64 (a + 8#64) (get s (.reg r2)) ⋆ R)) s'.dmem) := by
  obtain ⟨bs1, hl1, hbs1⟩ := region_sep_elim hmem
  intro _ p next jmp P hk
  simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.checkSPAlignment,
    hbase, armCheckSP_eq_false s hal, Bool.false_eq_true, ↓reduceIte, haddr p,
    getRegOrZr_zr, RegWidth.bits, Effects.All]
  rw [store_All_of_sep _ _ .W64 _ _ _ bs1 _ hbs1 hl1]
  have hm1 : (region (a + 8#64) 8 ⋆ (cell64 a (get s (.reg r1)) ⋆ R))
      (Mem.storeInt s.dmem a 8 (s.regs.getXReg r1).toBitVec.toInt) := by
    have hs1 := Mem.storeInt_sep a 8 bs1 (region (a + 8#64) 8 ⋆ R) s.dmem ⟨hbs1, hl1⟩
      (s.regs.getXReg r1).toBitVec.toInt
    rw [get_reg]
    exact sep_cast hs1 (by ac_rfl)
  obtain ⟨bs2, hl2, hbs2⟩ := region_sep_elim hm1
  have hbv : RegWidth.W64.bytesv = 8#64 := rfl
  rw [hbv, store_All_of_sep _ _ .W64 _ _ _ bs2 _ hbs2 hl2]
  refine hk _ ⟨rfl, rfl, ?_⟩
  have hs2 := Mem.storeInt_sep (a + 8#64) 8 bs2 (cell64 a (get s (.reg r1)) ⋆ R)
    (Mem.storeInt s.dmem a 8 (s.regs.getXReg r1).toBitVec.toInt) ⟨hbs2, hl2⟩
    (s.regs.getXReg r2).toBitVec.toInt
  exact sep_cast (show (cell64 (a + 8#64) (get s (.reg r2)) ⋆ (cell64 a (get s (.reg r1)) ⋆ R)) _
    from hs2) (by ac_rfl)

private theorem armLdpAddr_fallsTo (rd1 rd2 : XReg) (addr : AddrExpr) (a v1 v2 : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData)
    (hbase : addr.base = RegOrSp.SP)
    (hal : (get s .SP).toNat % 16 = 0)
    (haddr : ∀ [Labels] (p : Std.Rco Int64), addr.eval s p = (a, s))
    (hmem : (cell64 a v1 ⋆ (cell64 (a + 8#64) v2 ⋆ R)) s.dmem) :
    armDirFallsTo (ins (.LDP (zr rd1 .W64) (zr rd2 .W64) addr)) s
      (fun s' => s' = wr (wr s rd1 v1) rd2 v2) := by
  intro _ p next jmp P hk
  simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.checkSPAlignment,
    hbase, armCheckSP_eq_false s hal, Bool.false_eq_true, ↓reduceIte, haddr p, Effects.All]
  rw [load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v1.toInt) (cell64 (a + 8#64) v2 ⋆ R) hmem
    (Int.toBytes_length _ _)]
  have hmem2 : (cell64 (a + 8#64) v2 ⋆ (cell64 a v1 ⋆ R)) s.dmem := sep_cast hmem (by ac_rfl)
  have hbv : RegWidth.W64.bytesv = 8#64 := rfl
  rw [hbv, load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v2.toInt) (cell64 a v1 ⋆ R) hmem2
    (Int.toBytes_length _ _)]
  have hv1 : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v1.toInt)) = v1 :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v1
  have hv2 : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v2.toInt)) = v2 :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v2
  simp only [MachineData.setRegOrZr, setRegOrZr_zr, MemWidth.bits, hv1, hv2, BitVec.setWidth_eq]
  exact hk _ rfl

private theorem armStpSpXReg_wp [Host] (r1 r2 : XReg) (o : Nat) {R : Mem 64 → Prop}
    (s : MachineData) (hr1 : r1 ≠ .X16) (hr2 : r2 ≠ .X16) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 o) 8 ⋆
      (region (get s .SP + BitVec.ofNat 64 (o + 8)) 8 ⋆ R)) s.dmem) :
    _root_.Program.wp (emitClean (armStpSpXRegIns r1 r2 o))
      (fun s' => s'.regs.SP = s.regs.SP ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧
        (cell64 (get s .SP + BitVec.ofNat 64 o) (get s (.reg r1)) ⋆
          (cell64 (get s .SP + BitVec.ofNat 64 (o + 8)) (get s (.reg r2)) ⋆ R)) s'.dmem)
      (fun _ _ => False) s := by
  have ho8 : get s .SP + BitVec.ofNat 64 o + 8#64 = get s .SP + BitVec.ofNat 64 (o + 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  dsimp only [armStpSpXRegIns]
  simp only [emitClean_ite]
  split
  · have hmem' : (region (get s .SP + BitVec.ofNat 64 o) 8 ⋆
        (region (get s .SP + BitVec.ofNat 64 o + 8#64) 8 ⋆ R)) s.dmem := by
      simpa only [ho8] using hmem
    refine armWp_mono
      (armDirFallsTo_wp (armStpAddr_fallsTo r1 r2 (atOff .SP o) (get s .SP + BitVec.ofNat 64 o) s
        rfl hal (fun p => by rw [armAtSp_eval]; rfl) hmem')) ?_
    rintro s' ⟨hregs, hst, hdmem⟩
    refine ⟨congrArg Reg64s.SP hregs, fun _ _ => congrFun (congrArg Reg64s.getXReg hregs) _,
      hst, ?_⟩
    simpa only [ho8] using hdmem
  · rw [emitClean_append]
    refine armWp_append (armStSpXReg_wp r1 o s hr1 hal hmem) ?_
    rintro s₁ ⟨hsp1, hx1, hst1, hdmem1⟩
    have hgetsp1 : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
    have hal1 : (get s₁ .SP).toNat % 16 = 0 := hgetsp1 ▸ hal
    have hmem2 : (region (get s₁ .SP + BitVec.ofNat 64 (o + 8)) 8 ⋆
        (cell64 (get s .SP + BitVec.ofNat 64 o) (get s (.reg r1)) ⋆ R)) s₁.dmem := by
      rw [hgetsp1]
      exact sep_cast hdmem1 (by ac_rfl)
    refine armWp_mono (armStSpXReg_wp r2 (o + 8) s₁ hr2 hal1 hmem2) ?_
    rintro s' ⟨hsp2, hx2, hst2, hdmem2⟩
    have hr2_1 : get s₁ (.reg r2) = get s (.reg r2) := by
      rw [get_reg, hx1 r2 hr2]; exact (get_reg s r2).symm
    rw [hgetsp1, hr2_1] at hdmem2
    refine ⟨hsp2.trans hsp1, fun x hx => (hx2 x hx).trans (hx1 x hx), hst2.trans hst1, ?_⟩
    exact sep_cast hdmem2 (by ac_rfl)

private theorem armLdpSpXReg_wp [Host] (rd1 rd2 : XReg) (o : Nat) (v1 v2 : BitVec 64)
    {R : Mem 64 → Prop} (s : MachineData) (hrd : rd1 ≠ rd2) (hrd1 : rd1 ≠ .X16)
    (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (cell64 (get s .SP + BitVec.ofNat 64 o) v1 ⋆
      (cell64 (get s .SP + BitVec.ofNat 64 (o + 8)) v2 ⋆ R)) s.dmem) :
    _root_.Program.wp (emitClean (armLdpSpXRegIns rd1 rd2 o))
      (fun s' => s'.regs.SP = s.regs.SP ∧
        s'.regs.getXReg rd1 = UInt64.ofBitVec v1 ∧
        s'.regs.getXReg rd2 = UInt64.ofBitVec v2 ∧
        (∀ x, x ≠ rd1 → x ≠ rd2 → x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  have ho8 : get s .SP + BitVec.ofNat 64 o + 8#64 = get s .SP + BitVec.ofNat 64 (o + 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  dsimp only [armLdpSpXRegIns]
  simp only [emitClean_ite]
  split
  · have hmem' : (cell64 (get s .SP + BitVec.ofNat 64 o) v1 ⋆
        (cell64 (get s .SP + BitVec.ofNat 64 o + 8#64) v2 ⋆ R)) s.dmem := by
      simpa only [ho8] using hmem
    refine armWp_mono
      (armDirFallsTo_wp (armLdpAddr_fallsTo rd1 rd2 (atOff .SP o)
        (get s .SP + BitVec.ofNat 64 o) v1 v2 s rfl hal
        (fun p => by rw [armAtSp_eval]; rfl) hmem')) ?_
    rintro s' rfl
    refine ⟨by simp, ?_, Reg64s.getXReg_setXReg_same _ _ _, fun x hx1 hx2 _ => ?_, rfl, rfl⟩
    · rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrd.symm, Reg64s.getXReg_setXReg_same]
    · rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx2.symm,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx1.symm]
  · rw [emitClean_append]
    refine armWp_append (armLdSpXReg_wp rd1 o v1 s hal hmem) ?_
    rintro s₁ ⟨hsp1, hrd1_eq, hx1, hst1, hdmem1⟩
    have hgetsp1 : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
    have hal1 : (get s₁ .SP).toNat % 16 = 0 := hgetsp1 ▸ hal
    have hmem2 : (cell64 (get s₁ .SP + BitVec.ofNat 64 (o + 8)) v2 ⋆
        (cell64 (get s .SP + BitVec.ofNat 64 o) v1 ⋆ R)) s₁.dmem := by
      rw [hgetsp1, hdmem1]
      exact sep_cast hmem (by ac_rfl)
    refine armWp_mono (armLdSpXReg_wp rd2 (o + 8) v2 s₁ hal1 hmem2) ?_
    rintro s' ⟨hsp2, hrd2_eq, hx2, hst2, hdmem2⟩
    refine ⟨hsp2.trans hsp1, ?_, hrd2_eq, fun x hx1' hx2' hx16 => ?_,
      hst2.trans hst1, hdmem2.trans hdmem1⟩
    · rw [hx2 rd1 hrd hrd1, hrd1_eq]
    · rw [hx2 x hx2' hx16, hx1 x hx1' hx16]

private theorem evalUBFM_0_7 (v : BitVec 64) :
    evalUBFM (w := .W64) v 0 7 = (v.setWidth 8).setWidth 64 := by
  simp [evalUBFM, BitVec.take, BitVec.zeroExtend]
  rfl

private theorem evalUBFM_0_15 (v : BitVec 64) :
    evalUBFM (w := .W64) v 0 15 = (v.setWidth 16).setWidth 64 := by
  simp [evalUBFM, BitVec.take, BitVec.zeroExtend]
  rfl

private theorem armCanon8_fallsTo (x : XReg) (s : MachineData) :
    armDirFallsTo (ins (.UBFM (zr x .W64) (zr x .W64) 0 7)) s
      (fun s' => s' = wr s x (((get s (.reg x)).setWidth 8).setWidth 64)) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, evalUBFM_0_7]
  exact hk _ rfl

private theorem armCanon16_fallsTo (x : XReg) (s : MachineData) :
    armDirFallsTo (ins (.UBFM (zr x .W64) (zr x .W64) 0 15)) s
      (fun s' => s' = wr s x (((get s (.reg x)).setWidth 16).setWidth 64)) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, evalUBFM_0_15]
  exact hk _ rfl

private theorem armCanon32_fallsTo (x : XReg) (s : MachineData) :
    armDirFallsTo (ins (.ORR_s (zr x .W32) (xzr .W32) (sh x))) s
      (fun s' => s' = wr s x (((get s (.reg x)).setWidth 32).setWidth 64)) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, sh, Int64.toInt_zero, RegWidth.bits]
  have e : ((0#32 ||| (s.regs.getXReg x).toBitVec.setWidth 32 <<< (0 : Int).toNat) : BitVec 32).setWidth 64 =
      ((get s (.reg x)).setWidth 32).setWidth 64 := by
    simp [get_reg]
  rw [e]
  exact hk _ rfl

private theorem armCanonAbiXReg_wp [Host] {t : Ty} {x : XReg} {v : Val t} (s : MachineData)
    (ht : t = .bool ∨ ∃ n ∈ [8, 16, 32], t = .bits n)
    (hh : GprHolds (get s (.reg x)) t v) :
    _root_.Program.wp (armCanonAbiXReg t x)
      (fun s' => ∃ s'', s' = s'' ∧ s''.regs = (wr s x (get s'' (.reg x))).regs ∧
        s''.status = s.status ∧ s''.dmem = s.dmem ∧
        AbiGprHolds (get s'' (.reg x)) t v)
      (fun _ _ => False) s := by
  have mkSingle : ∀ {d : Directive} {n : Nat},
      armDirFallsTo d s (fun s' => s' = wr s x (((get s (.reg x)).setWidth n).setWidth 64)) →
      AbiGprHolds (((get s (.reg x)).setWidth n).setWidth 64) t v →
      _root_.Program.wp [d]
        (fun s' => ∃ s'', s' = s'' ∧ s''.regs = (wr s x (get s'' (.reg x))).regs ∧
          s''.status = s.status ∧ s''.dmem = s.dmem ∧
          AbiGprHolds (get s'' (.reg x)) t v)
        (fun _ _ => False) s := by
    intro d n hd hAbi
    refine armWp_mono (armDirFallsTo_wp hd) ?_
    rintro s' rfl
    refine ⟨wr s x (((get s (.reg x)).setWidth n).setWidth 64), rfl, ?_, rfl, rfl, ?_⟩
    · simp [wr, get_wr_same]
    · simpa [get_wr_same] using hAbi
  rcases ht with rfl | ⟨n, hn, rfl⟩
  · exact mkSingle (armCanon8_fallsTo x s) (abiGprHolds_bool_of_gprHolds hh)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact mkSingle (armCanon8_fallsTo x s) (abiGprHolds_bits_of_gprHolds hh)
    · exact mkSingle (armCanon16_fallsTo x s) (abiGprHolds_bits_of_gprHolds hh)
    · exact mkSingle (armCanon32_fallsTo x s) (abiGprHolds_bits_of_gprHolds hh)

/-! ## 4. `FrameTarget` snippet specifications -/

private theorem armPrologue_spec {h : Host} {k ns : Nat} {s : MachineData} {ra : Int64}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hra : get s (.reg .X30) = ra.toBitVec)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hF : armFrameSize ns ≤ 2 ^ 64)
    (hmem : s.dmem =⋆ region (get s .SP) 0 ⋆
      region (get s .SP - BitVec.ofNat 64 (armFrameSize ns)) (armFrameSize ns) ⋆ G) :
    armMach.FallsTo armCondReads h k (armPrologue ns).1 (.SP :: [.reg .X30] ++ armScratch) []
      (armPrologue ns).2 s
      (fun s' => get s' .SP = get s .SP - BitVec.ofNat 64 (armFrameSize ns) ∧
        (s'.dmem =⋆
          (cell64 (get s .SP - BitVec.ofNat 64 (armFrameSize ns) + BitVec.ofNat 64 (8 * ns))
              ra.toBitVec ⋆
            region (get s .SP - BitVec.ofNat 64 (armFrameSize ns) + BitVec.ofNat 64 (8 * ns) + 8#64)
              (armFrameSize ns - 8 * ns - 8)) ⋆
          region (get s .SP - BitVec.ofNat 64 (armFrameSize ns)) (8 * ns) ⋆ G))
      post := by
  letI := h
  rw [region_zero, emp_sep, region_frame_split_ra (armFrameSize_ge ns) hF] at hmem
  let sp' := get s .SP - BitVec.ofNat 64 (armFrameSize ns)
  have hsp' : sp'.toNat % 16 = 0 := aligned16_sub hsp (armFrameSize_mod ns)
  have hmem' : s.dmem =⋆ region (sp' + BitVec.ofNat 64 (8 * ns)) 8 ⋆
      (region sp' (8 * ns) ⋆
        region (sp' + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8) ⋆ G) :=
    sep_cast hmem (by dsimp only [sp']; ac_rfl)
  apply armFallsTo_of_wp
  dsimp only [armPrologue, armPrologueIns]
  rw [emitClean_append]
  refine armWp_append (armSubSp_wp (armFrameSize ns) s) ?_
  rintro s₁ ⟨hsp1, hx1, hst1, hdmem1⟩
  have hgetsp1 : get s₁ .SP = sp' := by simp [get_sp, hsp1, sp']
  have hhal1 : (get s₁ .SP).toNat % 16 = 0 := hgetsp1 ▸ hsp'
  have hx30_1 : get s₁ (.reg .X30) = ra.toBitVec := by
    rw [get_reg, hx1 .X30 (by decide)]; exact hra
  have hmem1 : (region (get s₁ .SP + BitVec.ofNat 64 (8 * ns)) 8 ⋆
      (region sp' (8 * ns) ⋆
        region (sp' + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8) ⋆ G))
      s₁.dmem := by
    rw [hgetsp1, hdmem1]; exact hmem'
  refine armWp_mono (armStSpXReg_wp .X30 (8 * ns) s₁ (by decide) hhal1 hmem1) ?_
  rintro s' ⟨hsp2, hx2, hst2, hdmem2⟩
  rw [hgetsp1, hx30_1] at hdmem2
  have hsp_final : get s' .SP = sp' := by simp [get_sp, hsp2, hsp1, sp']
  have hdmem_final : s'.dmem =⋆
      (cell64 (sp' + BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆
        region (sp' + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8)) ⋆
      region sp' (8 * ns) ⋆ G :=
    sep_cast hdmem2 (by ac_rfl)
  refine ⟨⟨hsp_final, hdmem_final⟩, armFrame_upd_regs (armKeep_regs _ (fun hne => ?_) (fun x hx => ?_))
    (Or.inr (hst2.trans hst1))⟩
  · exact absurd List.mem_cons_self hne
  · have hx16 : x ≠ .X16 := fun e => hx (by simp [e, armScratch])
    rw [hx2 x hx16, hx1 x hx16]

private theorem armEpilogue_spec {h : Host} {k ns : Nat} {s : MachineData} {ra : Int64}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hsp : (get s .SP).toNat % 16 = 0)
    (hF : armFrameSize ns ≤ 2 ^ 64)
    (hmem : s.dmem =⋆
      (cell64 (get s .SP + BitVec.ofNat 64 (armFrameSize ns) - BitVec.ofNat 64 (armFrameSize ns) +
          BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆
        region (get s .SP + BitVec.ofNat 64 (armFrameSize ns) - BitVec.ofNat 64 (armFrameSize ns) +
          BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8)) ⋆ G) :
    armMach.FallsTo armCondReads h k (armEpilogue ns).1 (.SP :: [.reg .X30] ++ armScratch) []
      (armEpilogue ns).2 s
      (fun s' => get s' .SP = get s .SP + BitVec.ofNat 64 (armFrameSize ns) ∧
        get s' (.reg .X30) = ra.toBitVec ∧
        (s'.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (armFrameSize ns)) 0 ⋆
          region (get s .SP + BitVec.ofNat 64 (8 * ns)) (armFrameSize ns - 8 * ns) ⋆ G))
      post := by
  letI := h
  rw [BitVec.add_sub_cancel] at hmem
  have hmem_reassoc : (cell64 (get s .SP + BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆
      (region (get s .SP + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8) ⋆ G))
      s.dmem :=
    sep_cast hmem (by ac_rfl)
  apply armFallsTo_of_wp
  dsimp only [armEpilogue, armEpilogueIns]
  rw [emitClean_append]
  refine armWp_append (armLdSpXReg_wp .X30 (8 * ns) ra.toBitVec s hsp hmem_reassoc) ?_
  rintro s₁ ⟨hsp1, hx30_1, hx1, hst1, hdmem1⟩
  refine armWp_mono (armAddSp_wp (armFrameSize ns) s₁) ?_
  rintro s' ⟨hsp2, hx2, hst2, hdmem2⟩
  have hgetsp1 : get s₁ .SP = get s .SP := by simp [get_sp, hsp1]
  have hsp_final : get s' .SP = get s .SP + BitVec.ofNat 64 (armFrameSize ns) := by
    simp [get_sp, hsp2, hgetsp1]
  have hra_final : get s' (.reg .X30) = ra.toBitVec := by
    rw [get_reg, hx2 .X30 (by decide), hx30_1]
  have hdmem_reg : s'.dmem =⋆
      (region (get s .SP + BitVec.ofNat 64 (8 * ns)) 8 ⋆
        region (get s .SP + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8)) ⋆ G := by
    have h1 : (cell64 (get s .SP + BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆
        (region (get s .SP + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8) ⋆ G))
        s'.dmem := by
      rw [hdmem2, hdmem1]; exact hmem_reassoc
    exact sep_cast (sep_mono (fun _ => cell64_region) h1) (by ac_rfl)
  have hge := armFrameSize_ge ns
  have hsplit : region (get s .SP + BitVec.ofNat 64 (8 * ns)) (armFrameSize ns - 8 * ns) =
      (region (get s .SP + BitVec.ofNat 64 (8 * ns)) 8 ⋆
        region (get s .SP + BitVec.ofNat 64 (8 * ns) + 8#64) (armFrameSize ns - 8 * ns - 8)) := by
    have he : armFrameSize ns - 8 * ns = 8 + (armFrameSize ns - 8 * ns - 8) := by omega
    conv => lhs; rw [he]
    exact region_split (by omega)
  have hdmem_final : s'.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (armFrameSize ns)) 0 ⋆
      region (get s .SP + BitVec.ofNat 64 (8 * ns)) (armFrameSize ns - 8 * ns) ⋆ G := by
    rw [region_zero, emp_sep, hsplit]
    exact hdmem_reg
  refine ⟨⟨hsp_final, hra_final, hdmem_final⟩,
    armFrame_upd_regs (armKeep_regs _ (fun hne => absurd List.mem_cons_self hne) (fun x hx => ?_))
      (Or.inr (hst2.trans hst1))⟩
  have hx30 : x ≠ .X30 := fun e => hx (by simp [e])
  have hx16 : x ≠ .X16 := fun e => hx (by simp [e, armScratch])
  rw [hx2 x hx16, hx1 x hx30 hx16]

private theorem armSlotSt_wp [Host] (i : Nat) (r : Reg) {R : Mem 64 → Prop} (s : MachineData)
    (hr : r ∉ armScratch) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ R) s.dmem) :
    _root_.Program.wp (armSlotSt i r)
      (fun s' => s'.regs.SP = s.regs.SP ∧
        (∀ x, x ≠ .X16 → x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧
        (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s r) ⋆ R) s'.dmem)
      (fun _ _ => False) s := by
  cases r with
  | reg x =>
    have hx16 : x ≠ .X16 := fun e => (ne_of_not_mem_armScratch hr).1 (e ▸ rfl)
    refine armWp_mono (armStSpXReg_wp x (8 * i) s hx16 hal hmem) ?_
    rintro s' ⟨hsp', hx', hst', hdmem'⟩
    exact ⟨hsp', fun y hy16 _ => hx' y hy16, hst', hdmem'⟩
  | SP =>
    dsimp only [armSlotSt, armSlotStIns]
    simp only [emitClean_append]
    refine armWp_cons (armMovToX_wp .X17 .SP s) ?_
    rintro s₁ rfl
    have hsp1 : (get (wr s .X17 (get s .SP)) .SP).toNat % 16 = 0 := by
      simpa [get_sp] using hal
    have hmem1 : (region (get (wr s .X17 (get s .SP)) .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ R)
        (wr s .X17 (get s .SP)).dmem := by
      simpa [get_sp] using hmem
    refine armWp_mono
      (armStSpXReg_wp .X17 (8 * i) (wr s .X17 (get s .SP)) (by decide) hsp1 hmem1) ?_
    rintro s' ⟨hsp', hx', hst', hdmem'⟩
    have hx17 : get (wr s .X17 (get s .SP)) (.reg .X17) = get s .SP := get_wr_same _ _ _
    rw [hx17] at hdmem'
    simp only [get_sp, Reg64s.SP_setXReg] at hsp' hdmem'
    refine ⟨hsp', fun y hy16 hy17 => ?_, hst', hdmem'⟩
    rw [hx' y hy16, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy17.symm]

private theorem armSlotSt_spec {h : Host} {k i : Nat} {r : Reg} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hr : r ∉ armScratch)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ G) :
    armMach.FallsTo armCondReads h k (armSlotSt i r) armScratch [] maskNone s
      (fun s' => s'.dmem =⋆
        cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s r) ⋆ G) post := by
  letI := h
  apply armFallsTo_of_wp
  refine armWp_mono (armSlotSt_wp i r s hr hsp hmem) ?_
  rintro s' ⟨hsp', hx', hst', hdmem'⟩
  refine ⟨hdmem', armFrame_upd_regs (armKeep_regs _ (fun _ => hsp') (fun y hy => ?_)) (Or.inr hst')⟩
  have hy16 : y ≠ .X16 := fun e => hy (by simp [e, armScratch])
  have hy17 : y ≠ .X17 := fun e => hy (by simp [e, armScratch])
  exact hx' y hy16 hy17

private theorem armSlotLd_wp [Host] (rd : Reg) (i : Nat) (v : BitVec 64) {R : Mem 64 → Prop}
    (s : MachineData) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) v ⋆ R) s.dmem) :
    _root_.Program.wp (armSlotLd rd i)
      (fun s' => get s' rd = v ∧
        (∀ r, r ≠ rd → r ∉ armScratch → get s' r = get s r) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  cases rd with
  | reg x =>
    refine armWp_mono (armLdSpXReg_wp x (8 * i) v s hal hmem) ?_
    rintro s' ⟨hsp', hrx, hx', hst', hdmem'⟩
    refine ⟨by simp [get_reg, hrx], fun r hr1 hr2 => ?_, hst', hdmem'⟩
    cases r with
    | SP => simp [get_sp, hsp']
    | reg y =>
      have hyx : y ≠ x := fun e => hr1 (e ▸ rfl)
      have hy16 : y ≠ .X16 := fun e => hr2 (by simp [e, armScratch])
      simp [get_reg, hx' y hyx hy16]
  | SP =>
    dsimp only [armSlotLd, armSlotLdIns]
    simp only [emitClean_append]
    refine armWp_append (armLdSpXReg_wp .X17 (8 * i) v s hal hmem) ?_
    rintro s₁ ⟨hsp1, hx17, hx1, hst1, hdmem1⟩
    refine armWp_mono (armMovToSp_wp .X17 s₁) ?_
    rintro s' rfl
    refine ⟨by simp [get_sp, get_reg, hx17], fun r hr1 hr2 => ?_, hst1, hdmem1⟩
    cases r with
    | SP => exact absurd rfl hr1
    | reg y =>
      have hy17 : y ≠ .X17 := fun e => hr2 (by simp [e, armScratch])
      have hy16 : y ≠ .X16 := fun e => hr2 (by simp [e, armScratch])
      simp only [get_reg, Reg64s_getXReg_setSP]
      exact congrArg UInt64.toBitVec (hx1 y hy17 hy16)

private theorem armSlotLd_spec {h : Host} {k i : Nat} {rd : Reg} {v : BitVec 64} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (_hrd : rd ∉ armScratch)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) v ⋆ G) :
    armMach.FallsTo armCondReads h k (armSlotLd rd i) (rd :: armScratch) [] maskNone s
      (fun s' => get s' rd = v ∧ s'.dmem = s.dmem) post := by
  letI := h
  apply armFallsTo_of_wp
  refine armWp_mono (armSlotLd_wp rd i v s hsp hmem) ?_
  rintro s' ⟨hv, hkeep, hst', hdmem'⟩
  refine ⟨⟨hv, hdmem'⟩, armFrame_upd_regs (fun r hr => ?_) (Or.inr hst')⟩
  rw [List.mem_cons, not_or] at hr
  exact hkeep r hr.1 hr.2

private theorem armSaveRegs_wp [Host] (i : Nat) (rs : List Reg) {R : Mem 64 → Prop}
    (s : MachineData) (hlen : 8 * i + 8 * rs.length ≤ 2 ^ 64)
    (hrs : ∀ r ∈ rs, r ∉ armScratch) (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (region (get s .SP + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ R) s.dmem) :
    _root_.Program.wp (armSaveRegs i rs)
      (fun s' => s'.regs.SP = s.regs.SP ∧
        (∀ x, x ≠ .X16 → x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧
        (array64 (get s .SP + BitVec.ofNat 64 (8 * i)) (rs.map (get s)) ⋆ R) s'.dmem)
      (fun _ _ => False) s := by
  match rs with
  | [] =>
    simp only [List.length_nil, Nat.mul_zero, region_zero, emp_sep] at hmem
    refine armWp_mono (armWp_nil ⟨rfl, fun _ _ _ => rfl, rfl, ?_⟩) (fun _ h => h)
    simpa [List.map_nil, array64_nil, emp_sep] using hmem
  | [r] =>
    have hmem1 : (region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ R) s.dmem := by
      simpa using hmem
    refine armWp_mono (armSlotSt_wp i r s (hrs r List.mem_cons_self) hal hmem1) ?_
    rintro s' ⟨hsp', hx', hst', hdmem'⟩
    refine ⟨hsp', hx', hst', ?_⟩
    simpa only [List.map_cons, List.map_nil, array64_cons, array64_nil, sep_emp] using hdmem'
  | r1 :: r2 :: rs' =>
    have stepSingle : ∀ (hi : armSaveRegsIns i (r1 :: r2 :: rs') =
        armSlotStIns i r1 ++ armSaveRegsIns (i + 1) (r2 :: rs')),
        _root_.Program.wp (armSaveRegs i (r1 :: r2 :: rs'))
          (fun s' => s'.regs.SP = s.regs.SP ∧
            (∀ x, x ≠ .X16 → x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x) ∧
            s'.status = s.status ∧
            (array64 (get s .SP + BitVec.ofNat 64 (8 * i))
              ((r1 :: r2 :: rs').map (get s)) ⋆ R) s'.dmem)
          (fun _ _ => False) s := by
      intro hi
      have hmem1 : (region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆
          (region (get s .SP + BitVec.ofNat 64 (8 * (i + 1))) (8 * (r2 :: rs').length) ⋆ R))
          s.dmem := by
        have e1 : 8 * (r1 :: r2 :: rs').length = 8 + 8 * (r2 :: rs').length := by
          simp only [List.length_cons]; omega
        have hlen' : 8 + 8 * (r2 :: rs').length ≤ 2 ^ 64 := by
          simp only [List.length_cons] at hlen ⊢; omega
        rw [e1, region_split hlen'] at hmem
        have ha1 : get s .SP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8 =
            get s .SP + BitVec.ofNat 64 (8 * (i + 1)) := by
          apply BitVec.eq_of_toNat_eq; simp; omega
        rw [ha1] at hmem
        exact sep_cast hmem (by ac_rfl)
      dsimp only [armSaveRegs]; rw [hi, emitClean_append]
      refine armWp_append (armSlotSt_wp i r1 s (hrs r1 List.mem_cons_self) hal hmem1) ?_
      rintro s₁ ⟨hsp_1, hx_1, hst_1, hdmem_1⟩
      have hgetsp1 : get s₁ .SP = get s .SP := by simp [get_sp, hsp_1]
      have hal1 : (get s₁ .SP).toNat % 16 = 0 := hgetsp1 ▸ hal
      have hrs' : ∀ r ∈ r2 :: rs', r ∉ armScratch := fun r hr =>
        hrs r (List.mem_cons_of_mem _ hr)
      have hmem_rest : (region (get s₁ .SP + BitVec.ofNat 64 (8 * (i + 1)))
          (8 * (r2 :: rs').length) ⋆
          (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s r1) ⋆ R)) s₁.dmem := by
        rw [hgetsp1]; exact sep_cast hdmem_1 (by ac_rfl)
      refine armWp_mono (armSaveRegs_wp (i + 1) (r2 :: rs') s₁
          (by simp only [List.length_cons] at hlen ⊢; omega) hrs' hal1 hmem_rest) ?_
      rintro s' ⟨hsp_2, hx_2, hst_2, hdmem_2⟩
      have hmap : (r2 :: rs').map (get s₁) = (r2 :: rs').map (get s) := by
        refine List.map_congr_left fun r hr => ?_
        cases r with
        | SP => exact hgetsp1
        | reg x =>
          have hx := ne_of_not_mem_armScratch (hrs' _ hr)
          simp [get_reg, hx_1 x (fun e => hx.1 (congrArg XRegOrSp.reg e))
            (fun e => hx.2 (congrArg XRegOrSp.reg e))]
      rw [hgetsp1, hmap] at hdmem_2
      refine ⟨hsp_2.trans hsp_1, fun x hx16 hx17 => (hx_2 x hx16 hx17).trans (hx_1 x hx16 hx17),
        hst_2.trans hst_1, ?_⟩
      simp only [List.map_cons, array64_cons] at hdmem_2 ⊢
      have h8a : get s .SP + BitVec.ofNat 64 (8 * i) + 8 =
          get s .SP + BitVec.ofNat 64 (8 * (i + 1)) := by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
      rw [h8a]
      exact sep_cast hdmem_2 (by ac_rfl)
    cases r1 with
    | SP => exact stepSingle (by cases r2 <;> rfl)
    | reg x1 =>
      cases r2 with
      | SP => exact stepSingle rfl
      | reg x2 =>
        have hr1 : x1 ≠ .X16 := fun e =>
          (ne_of_not_mem_armScratch (hrs _ List.mem_cons_self)).1 (e ▸ rfl)
        have hr2 : x2 ≠ .X16 := fun e =>
          (ne_of_not_mem_armScratch (hrs _ (List.mem_cons_of_mem _ List.mem_cons_self))).1
            (e ▸ rfl)
        have hmem' : (region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆
            (region (get s .SP + BitVec.ofNat 64 (8 * i + 8)) 8 ⋆
              (region (get s .SP + BitVec.ofNat 64 (8 * (i + 2))) (8 * rs'.length) ⋆ R)))
            s.dmem := by
          have e1 : 8 * (XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs').length =
              8 + (8 + 8 * rs'.length) := by
            simp only [List.length_cons]; omega
          have hlen' : 8 + (8 + 8 * rs'.length) ≤ 2 ^ 64 := by
            simp only [List.length_cons] at hlen; omega
          rw [e1, region_split hlen', region_split (by omega)] at hmem
          have ha1 : get s .SP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8 =
              get s .SP + BitVec.ofNat 64 (8 * i + 8) := by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          have ha2 : get s .SP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8 +
              BitVec.ofNat 64 8 = get s .SP + BitVec.ofNat 64 (8 * (i + 2)) := by
            apply BitVec.eq_of_toNat_eq; simp; omega
          rw [ha2, ha1] at hmem
          exact sep_cast hmem (by ac_rfl)
        dsimp only [armSaveRegs, armSaveRegsIns]
        rw [emitClean_append]
        refine armWp_append (armStpSpXReg_wp x1 x2 (8 * i) s hr1 hr2 hal hmem') ?_
        rintro s₁ ⟨hsp_1, hx_1, hst_1, hdmem_1⟩
        have hgetsp1 : get s₁ .SP = get s .SP := by simp [get_sp, hsp_1]
        have hal1 : (get s₁ .SP).toNat % 16 = 0 := hgetsp1 ▸ hal
        have hrs' : ∀ r ∈ rs', r ∉ armScratch := fun r hr =>
          hrs r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
        have hmem_rest : (region (get s₁ .SP + BitVec.ofNat 64 (8 * (i + 2))) (8 * rs'.length) ⋆
            (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s (.reg x1)) ⋆
              (cell64 (get s .SP + BitVec.ofNat 64 (8 * i + 8)) (get s (.reg x2)) ⋆ R)))
            s₁.dmem := by
          rw [hgetsp1]
          exact sep_cast hdmem_1 (by ac_rfl)
        refine armWp_mono (armSaveRegs_wp (i + 2) rs' s₁
            (by simp only [List.length_cons] at hlen; omega) hrs' hal1 hmem_rest) ?_
        rintro s' ⟨hsp_2, hx_2, hst_2, hdmem_2⟩
        have hmap : rs'.map (get s₁) = rs'.map (get s) := by
          refine List.map_congr_left fun r hr => ?_
          cases r with
          | SP => exact hgetsp1
          | reg x =>
            have hx := ne_of_not_mem_armScratch (hrs' _ hr)
            simp [get_reg, hx_1 x (fun e => hx.1 (congrArg XRegOrSp.reg e))]
        rw [hgetsp1, hmap] at hdmem_2
        refine ⟨hsp_2.trans hsp_1, fun x hx16 hx17 => (hx_2 x hx16 hx17).trans (hx_1 x hx16),
          hst_2.trans hst_1, ?_⟩
        simp only [List.map_cons, array64_cons]
        have h8a : get s .SP + BitVec.ofNat 64 (8 * i) + 8 =
            get s .SP + BitVec.ofNat 64 (8 * i + 8) := by
          rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
        have h8b : get s .SP + BitVec.ofNat 64 (8 * i) + 8 + 8 =
            get s .SP + BitVec.ofNat 64 (8 * (i + 2)) := by
          rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1
          apply BitVec.eq_of_toNat_eq; simp; omega
        rw [h8b, h8a]
        exact sep_cast hdmem_2 (by ac_rfl)

private theorem armSaveRegs_spec {h : Host} {k i : Nat} {rs : List Reg} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hlen : 8 * i + 8 * rs.length ≤ 2 ^ 64)
    (hrs : ∀ r ∈ rs, r ∉ armScratch)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ G) :
    armMach.FallsTo armCondReads h k (armSaveRegs i rs) armScratch [] maskNone s
      (fun s' => s'.dmem =⋆
        array64 (get s .SP + BitVec.ofNat 64 (8 * i)) (rs.map (get s)) ⋆ G) post := by
  letI := h
  apply armFallsTo_of_wp
  refine armWp_mono (armSaveRegs_wp i rs s hlen hrs hsp hmem) ?_
  rintro s' ⟨hsp', hx', hst', hdmem'⟩
  refine ⟨hdmem', armFrame_upd_regs (armKeep_regs _ (fun _ => hsp') (fun y hy => ?_)) (Or.inr hst')⟩
  have hy16 : y ≠ .X16 := fun e => hy (by simp [e, armScratch])
  have hy17 : y ≠ .X17 := fun e => hy (by simp [e, armScratch])
  exact hx' y hy16 hy17

private theorem armRestoreRegs_wp [Host] (i : Nat) (rs : List Reg) {R : Mem 64 → Prop}
    (s₀ s : MachineData) (hnd : rs.Nodup) (hsub : ∀ r ∈ rs, r ∈ armFrame.calleeSaved)
    (hal : (get s .SP).toNat % 16 = 0)
    (hmem : (array64 (get s .SP + BitVec.ofNat 64 (8 * i)) (rs.map (get s₀)) ⋆ R) s.dmem) :
    _root_.Program.wp (armRestoreRegs i rs)
      (fun s' => get s' .SP = get s .SP ∧
        (∀ r ∈ rs, get s' r = get s₀ r) ∧
        (∀ x, .reg x ∉ rs → x ≠ .X16 → x ≠ .X17 → get s' (.reg x) = get s (.reg x)) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  match rs with
  | [] =>
    exact armWp_mono
      (armWp_nil ⟨rfl, fun _ h => False.elim (List.not_mem_nil h),
        fun _ _ _ _ => rfl, rfl, rfl⟩)
      (fun _ h => h)
  | [r] =>
    have hsp_ne : .SP ≠ r := fun e => by
      have h := hsub r List.mem_cons_self
      rw [← e] at h; simp at h
    have hmem1 : (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s₀ r) ⋆ R) s.dmem := by
      simpa only [List.map_cons, List.map_nil, array64_cons, array64_nil, sep_emp] using hmem
    refine armWp_mono (armSlotLd_wp r i (get s₀ r) s hal hmem1) ?_
    rintro s' ⟨hr, hkeep, hst', hdmem'⟩
    refine ⟨hkeep .SP hsp_ne (by simp [armScratch]), fun q hq => ?_,
      fun x hx1 hx16 hx17 => ?_, hst', hdmem'⟩
    · simp only [List.mem_singleton] at hq; subst hq; exact hr
    · have hne : XRegOrSp.reg x ≠ r := fun e => hx1 (by simp [e])
      have hns : XRegOrSp.reg x ∉ armScratch := fun h => by
        simp only [armScratch, List.mem_cons, List.not_mem_nil, or_false,
          XRegOrSp.reg.injEq] at h
        exact h.elim hx16 hx17
      exact hkeep (.reg x) hne hns
  | r1 :: r2 :: rs' =>
    cases r1 with
    | SP =>
      exfalso
      have h := hsub .SP List.mem_cons_self
      simp at h
    | reg x1 =>
      cases r2 with
      | SP =>
        exfalso
        have h := hsub .SP (List.mem_cons_of_mem _ List.mem_cons_self)
        simp at h
      | reg x2 =>
        have hr12 : x1 ≠ x2 := fun e => by
          have h1 := (List.nodup_cons.mp hnd).1
          exact h1 (by simp [e])
        have hr1_cs := hsub (.reg x1) List.mem_cons_self
        have hr2_cs := hsub (.reg x2) (List.mem_cons_of_mem _ List.mem_cons_self)
        have hr1_16 : x1 ≠ .X16 := fun e => by subst e; simp at hr1_cs
        have hr1_17 : x1 ≠ .X17 := fun e => by subst e; simp at hr1_cs
        have hr2_16 : x2 ≠ .X16 := fun e => by subst e; simp at hr2_cs
        have hr2_17 : x2 ≠ .X17 := fun e => by subst e; simp at hr2_cs
        have hnd' : rs'.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
        have hsub' : ∀ r ∈ rs', r ∈ armFrame.calleeSaved := fun r hr =>
          hsub r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
        have hmem' : (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s₀ (.reg x1)) ⋆
            (cell64 (get s .SP + BitVec.ofNat 64 (8 * i + 8)) (get s₀ (.reg x2)) ⋆
              (array64 (get s .SP + BitVec.ofNat 64 (8 * (i + 2))) (rs'.map (get s₀)) ⋆ R)))
            s.dmem := by
          simp only [List.map_cons, array64_cons] at hmem
          have h8a : get s .SP + BitVec.ofNat 64 (8 * i) + 8 =
              get s .SP + BitVec.ofNat 64 (8 * i + 8) := by
            rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
          have h8b : get s .SP + BitVec.ofNat 64 (8 * i) + 8 + 8 =
              get s .SP + BitVec.ofNat 64 (8 * (i + 2)) := by
            rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1
            apply BitVec.eq_of_toNat_eq; simp; omega
          rw [h8b, h8a] at hmem
          exact sep_cast hmem (by ac_rfl)
        dsimp only [armRestoreRegs, armRestoreRegsIns]
        rw [emitClean_append]
        refine armWp_append
          (armLdpSpXReg_wp x1 x2 (8 * i) (get s₀ (.reg x1)) (get s₀ (.reg x2)) s
            hr12 hr1_16 hal hmem') ?_
        rintro s₁ ⟨hsp_1, hr1_eq, hr2_eq, hx_1, hst_1, hdmem_1⟩
        have hgetsp1 : get s₁ .SP = get s .SP := by simp [get_sp, hsp_1]
        have hal1 : (get s₁ .SP).toNat % 16 = 0 := hgetsp1 ▸ hal
        have hmem_rest : (array64 (get s₁ .SP + BitVec.ofNat 64 (8 * (i + 2))) (rs'.map (get s₀)) ⋆
            (cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s₀ (.reg x1)) ⋆
              (cell64 (get s .SP + BitVec.ofNat 64 (8 * i + 8)) (get s₀ (.reg x2)) ⋆ R)))
            s₁.dmem := by
          rw [hgetsp1, hdmem_1]
          exact sep_cast hmem' (by ac_rfl)
        refine armWp_mono (armRestoreRegs_wp (i + 2) rs' s₀ s₁ hnd' hsub' hal1 hmem_rest) ?_
        rintro s' ⟨hsp_2, hres_2, hx_2, hst_2, hdmem_2⟩
        refine ⟨hsp_2.trans hgetsp1, fun q hq => ?_, fun x hx hx16 hx17 => ?_,
          hst_2.trans hst_1, hdmem_2.trans hdmem_1⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · have hnr1 : XRegOrSp.reg x1 ∉ rs' := fun hm =>
              (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hm)
            rw [hx_2 x1 hnr1 hr1_16 hr1_17, get_reg, hr1_eq]
          · rcases List.mem_cons.mp hq with rfl | hq
            · have hnr2 : XRegOrSp.reg x2 ∉ rs' :=
                (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
              rw [hx_2 x2 hnr2 hr2_16 hr2_17, get_reg, hr2_eq]
            · exact hres_2 q hq
        · simp only [List.mem_cons, XRegOrSp.reg.injEq, not_or] at hx
          rw [hx_2 x hx.2.2 hx16 hx17, get_reg, hx_1 x hx.1 hx.2.1 hx16]; rfl

private theorem armRestoreRegs_spec {h : Host} {k i : Nat} {rs : List Reg} {s₀ s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hnd : rs.Nodup)
    (hsub : ∀ r ∈ rs, r ∈ armFrame.calleeSaved)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ array64 (get s .SP + BitVec.ofNat 64 (8 * i)) (rs.map (get s₀)) ⋆ G) :
    armMach.FallsTo armCondReads h k (armRestoreRegs i rs) (rs ++ armScratch) [] maskNone s
      (fun s' => (∀ r ∈ rs, get s' r = get s₀ r) ∧ s'.dmem = s.dmem) post := by
  letI := h
  apply armFallsTo_of_wp
  refine armWp_mono (armRestoreRegs_wp i rs s₀ s hnd hsub hsp hmem) ?_
  rintro s' ⟨hsp', hres, hx', hst', hdmem'⟩
  refine ⟨⟨hres, hdmem'⟩, armFrame_upd_regs (fun r hr => ?_) (Or.inr hst')⟩
  rw [List.mem_append, not_or] at hr
  cases r with
  | SP => exact hsp'
  | reg x =>
    have hx16 : x ≠ .X16 := fun e => hr.2 (by simp [e, armScratch])
    have hx17 : x ≠ .X17 := fun e => hr.2 (by simp [e, armScratch])
    exact hx' x hr.1 hx16 hx17

private theorem armCanonAbi_spec {h : Host} {k : Nat} {t : Ty} {r : Reg} {v : Val t}
    {s : MachineData} {post : MachineState → Prop}
    (ht : t = .bool ∨ ∃ n ∈ [8, 16, 32, 64], t = .bits n)
    (hr : r ∉ armScratch)
    (hh : GprHolds (get s r) t v) :
    armMach.FallsTo armCondReads h k (armCanonAbi t r).1 (r :: armScratch) []
      (armCanonAbi t r).2 s
      (fun s' => AbiGprHolds (get s' r) t v ∧ s'.dmem = s.dmem) post := by
  letI := h
  have splitSmall : (t = .bool ∨ ∃ n ∈ [8, 16, 32], t = .bits n) ∨ t = .bits 64 := by
    rcases ht with rfl | ⟨n, hn, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inr ⟨8, by decide, rfl⟩)
      · exact Or.inl (Or.inr ⟨16, by decide, rfl⟩)
      · exact Or.inl (Or.inr ⟨32, by decide, rfl⟩)
      · exact Or.inr rfl
  rcases splitSmall with (rfl | ⟨n, hn, rfl⟩) | rfl
  · cases r with
    | reg x =>
      apply armFallsTo_of_wp
      refine armWp_mono (armCanonAbiXReg_wp s (Or.inl rfl) hh) ?_
      rintro s' ⟨s'', rfl, hregs, hst, hdmem, hAbi⟩
      refine ⟨⟨hAbi, hdmem⟩, armFrame_upd_regs (armKeep_regs _ (fun _ => ?_) (fun y hy => ?_)) (Or.inr hst)⟩
      · rw [hregs]; exact Reg64s.SP_setXReg _ _ _
      · have hyx : y ≠ x := fun e => hy (by simp [e])
        rw [hregs]; exact Reg64s.getXReg_setXReg_of_ne _ _ _ _ hyx.symm
    | SP =>
      apply armFallsTo_of_wp
      dsimp only [armCanonAbi, armCanonAbiIns]
      simp only [emitClean_append]
      refine armWp_cons (armMovToX_wp .X16 .SP s) ?_
      rintro s₁ rfl
      have hh1 : GprHolds (get (wr s .X16 (get s .SP)) (.reg .X16)) .bool v := by
        simpa [get_wr_same] using hh
      refine armWp_append (armCanonAbiXReg_wp (wr s .X16 (get s .SP)) (Or.inl rfl) hh1) ?_
      rintro s₂ ⟨s'', rfl, hregs, hst, hdmem, hAbi⟩
      refine armWp_mono (armMovToSp_wp .X16 s₂) ?_
      rintro s' rfl
      refine ⟨⟨by simpa [get_sp] using hAbi, hdmem⟩,
        armFrame_upd_regs (armKeep_regs _ (fun hsp => absurd List.mem_cons_self hsp) (fun y hy => ?_))
          (Or.inr hst)⟩
      have hy16 : y ≠ .X16 := fun e => hy (by simp [e, armScratch])
      change s₂.regs.getXReg y = s.regs.getXReg y
      rw [hregs, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy16.symm,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy16.symm]
  · cases r with
    | reg x =>
      apply armFallsTo_of_wp
      refine armWp_mono (armCanonAbiXReg_wp s (Or.inr ⟨n, hn, rfl⟩) hh) ?_
      rintro s' ⟨s'', rfl, hregs, hst, hdmem, hAbi⟩
      refine ⟨⟨hAbi, hdmem⟩, armFrame_upd_regs (armKeep_regs _ (fun _ => ?_) (fun y hy => ?_)) (Or.inr hst)⟩
      · rw [hregs]; exact Reg64s.SP_setXReg _ _ _
      · have hyx : y ≠ x := fun e => hy (by simp [e])
        rw [hregs]; exact Reg64s.getXReg_setXReg_of_ne _ _ _ _ hyx.symm
    | SP =>
      have hcond : (n == 8 || n == 16 || n == 32) = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl <;> decide
      apply armFallsTo_of_wp
      dsimp only [armCanonAbi, armCanonAbiIns]
      simp only [hcond, ↓reduceIte, emitClean_append]
      refine armWp_cons (armMovToX_wp .X16 .SP s) ?_
      rintro s₁ rfl
      have hh1 : GprHolds (get (wr s .X16 (get s .SP)) (.reg .X16)) (.bits n) v := by
        simpa [get_wr_same] using hh
      refine armWp_append (armCanonAbiXReg_wp (wr s .X16 (get s .SP)) (Or.inr ⟨n, hn, rfl⟩) hh1) ?_
      rintro s₂ ⟨s'', rfl, hregs, hst, hdmem, hAbi⟩
      refine armWp_mono (armMovToSp_wp .X16 s₂) ?_
      rintro s' rfl
      refine ⟨⟨by simpa [get_sp] using hAbi, hdmem⟩,
        armFrame_upd_regs (armKeep_regs _ (fun hsp => absurd List.mem_cons_self hsp) (fun y hy => ?_))
          (Or.inr hst)⟩
      have hy16 : y ≠ .X16 := fun e => hy (by simp [e, armScratch])
      change s₂.regs.getXReg y = s.regs.getXReg y
      rw [hregs, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy16.symm,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy16.symm]
  · cases r <;>
      exact Machine.FallsTo.nil ⟨abiGprHolds_bits64_of_gprHolds hh, rfl⟩

private theorem armCall_spec {h : Host} {k : Nat} {sym : Sym} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hc : [armCallD sym].IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ region (get s .SP - 0#64) 0 ⋆ G)
    (hk : ∀ s' : MachineData,
      get s' .SP = get s .SP - 0#64 →
      armMach.Frame armCondReads s s' (.SP :: [.reg .X30] ++ armScratch) [] maskAll →
      get s' (.reg .X30) = (Host.addrOf (k + 1)).toBitVec →
      (s'.dmem =⋆ region (get s' .SP) 0 ⋆ G) →
      Eventually (step1 Host.exe) post ⟨s', hostLabel h sym⟩) :
    armMach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [armCallD]
  simp only [t_step_simp, Reg64s.setRegOrZr_reg64]
  have hra : BitVec.ofInt 64 (Host.addrOf (k + 1)).toInt = (Host.addrOf (k + 1)).toBitVec := by
    rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  rw [hra]
  refine hk (wr s .X30 (Host.addrOf (k + 1)).toBitVec) (by simp [get_sp]) ?_
    (get_wr_same _ _ _) (by simpa [get_sp] using hmem)
  refine armFrame_upd_regs (armKeep_regs _ (fun _ => rfl) (fun y hy => ?_)) (Or.inl rfl)
  have hy30 : y ≠ .X30 := fun e => hy (by simp [e])
  exact Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy30.symm

private theorem armExitJmp_spec {h : Host} {k : Nat} {sym : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : [armJmpD sym].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      armMach.Frame armCondReads s s' armScratch [] maskNone → s'.dmem = s.dmem →
      Eventually (step1 Host.exe) post ⟨s', hostLabel h sym⟩) :
    armMach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [armJmpD]; simp only [t_step_simp]
  exact hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone) rfl

private theorem armRet_spec {h : Host} {k : Nat} {s : MachineData} {ra : Int64}
    {post : MachineState → Prop}
    (hc : [armRetD].IsInfixAt Host.prog k)
    (hra : get s (.reg .X30) = ra.toBitVec)
    (hk : ∀ s' : MachineData,
      armMach.KeepsGpr s s' (.SP :: armScratch) →
      armMach.KeepsVec s s' [] →
      get s' .SP = get s .SP + 0#64 →
      s'.dmem = s.dmem →
      Eventually (step1 Host.exe) post ⟨s', ra⟩) :
    armMach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [armRetD]
  simp only [t_step_simp, Reg64s.getRegOrZr_reg64]
  have hpc : Int64.ofInt (s.regs.getXReg .X30).toBitVec.signed = ra := by
    rw [show (s.regs.getXReg .X30).toBitVec = ra.toBitVec from hra]
    simp [BitVec.signed, Int64.toInt_toBitVec, Int64.ofInt_toInt]
  rw [hpc]
  exact hk s (fun _ _ => rfl) (fun v => v.elim) (by simp) rfl

/-! ## 5. `armFrameSpec : FrameTarget armMach armFrame armCondReads` -/

theorem armFrameSpec_spec :
    FrameSpec armMach armFrame armCondReads armFramePreds where
  sp_disj := by simp
  scratch_disj := by simp
  cs_disj := by simp
  ra_disj := by simp
  argRegs_nodup := by decide
  retRegs_nodup := by decide
  retAddr_region _ _ _ h := h
  raReg_of_raRegs _ _ _ h hra := by
    dsimp [armFramePreds] at hra ⊢
    rw [← hra]; exact h (.reg .X30) (by simp)
  slots_le_frameSize := armFrameSize_slots
  spOk_frame _ ns h := aligned16_sub h (armFrameSize_mod ns)
  spEntry_call sp ns h := by simpa [BitVec.sub_zero] using aligned16_sub h (armFrameSize_mod ns)
  labelAddr_eq {h} {_} {_} hk hfirst := letI := h; Host.label_eq_addrOf hk hfirst
  label_spec {h} {_} {_} {_} {_} hi hrun := letI := h; Host.eventually_label hi hrun
  prologue_spec {h} {_} {_} {_} {_} {_} {_} hra hsp hF hmem :=
    letI := h; armPrologue_spec hra hsp (by omega) hmem
  epilogue_spec {h} {_} {_} {_} {_} {_} {_} hsp hF hmem :=
    letI := h; armEpilogue_spec hsp (by omega) hmem
  slotSt_spec {h} {_} {_} {_} {_} {_} {_} hr hsp hmem :=
    letI := h; armSlotSt_spec hr hsp hmem
  slotLd_spec {h} {_} {_} {_} {_} {_} {_} {_} hrd hsp hmem :=
    letI := h; armSlotLd_spec hrd hsp hmem
  saveRegs_spec {fn h k i rs s G post} hfn hlen hrs hsp hmem := by
    cases hfn
    letI := h; exact armSaveRegs_spec hlen hrs hsp hmem
  restoreRegs_spec {fn h k i rs s₀ s G post} hfn hnd hsub hsp hmem := by
    cases hfn
    letI := h; exact armRestoreRegs_spec hnd hsub hsp hmem
  canonAbi_spec {h} {_} {_} {_} {_} {_} {_} ht hr hh :=
    letI := h; armCanonAbi_spec ht hr hh
  call_spec {h} {_} {_} {_} {_} {_} hc hmem hk :=
    letI := h; armCall_spec hc hmem hk
  exitJmp_spec {h} {_} {_} {_} {_} hc hk :=
    letI := h; armExitJmp_spec hc hk
  ret_spec {h} {_} {_} {_} {_} {_} hc hra _ hk :=
    letI := h; armRet_spec hc hra hk

@[expose] def armFrameSpec : FrameTarget armMach armFrame armCondReads where
  toFramePreds := armFramePreds
  spec := armFrameSpec_spec

/-! ## 6. `NoLab` lemmas -/

section NoLab

theorem armPrologue_noLab (ns : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ (armFrame.prologue ns).1 :=
  emitClean_noLab _ l

theorem armEpilogue_noLab (ns : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ (armFrame.epilogue ns).1 :=
  emitClean_noLab _ l

theorem armSlotSt_noLab (i : Nat) (r : Reg) (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.slotSt i r :=
  emitClean_noLab _ l

theorem armSlotLd_noLab (rd : Reg) (i : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.slotLd rd i :=
  emitClean_noLab _ l

theorem armSaveRegs_noLab (base : Nat) (rs : List Reg) (l : Sym) :
    Kraken.Directive.label l ∉ armSaveRegs base rs :=
  emitClean_noLab _ l

theorem armRestoreRegs_noLab (base : Nat) (rs : List Reg) (l : Sym) :
    Kraken.Directive.label l ∉ armRestoreRegs base rs :=
  emitClean_noLab _ l

theorem armCanonAbi_noLab (t : Ty) (r : Reg) (l : Sym) :
    Kraken.Directive.label l ∉ (armFrame.canonAbi t r).1 :=
  emitClean_noLab _ l

theorem armCall_noLab (sym : Sym) (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.call sym :=
  emitClean_noLab _ l

theorem armExitJmp_noLab (sym : Sym) (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.exitJmp sym :=
  emitClean_noLab _ l

theorem armRet_noLab (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.ret :=
  emitClean_noLab _ l

end NoLab

/-! ## 7. `ParserChecks` (`Kraken.AArch64.Parser`) -/

section ParserChecks
open Kraken.AArch64.Parser

example : ⸨prog|
  sub sp, sp, #16
  str x30, [sp, #0]
⸩ = (armFrame.prologue 0).1 := rfl

example : ⸨prog|
  ldr x30, [sp, #0]
  add sp, sp, #16
⸩ = (armFrame.epilogue 0).1 := rfl

example : ⸨prog|
  ldr x16, =4096
  sub sp, sp, x16
  str x30, [sp, #4080]
⸩ = (armFrame.prologue 510).1 := rfl

example : ⸨prog|
  ldr x16, =32784
  sub sp, sp, x16
  ldr x16, =32768
  str x30, [sp, x16]
⸩ = (armFrame.prologue 4096).1 := rfl

example : ⸨prog|
  ldr x16, =32768
  ldr x30, [sp, x16]
  ldr x16, =32784
  add sp, sp, x16
⸩ = (armFrame.epilogue 4096).1 := rfl

example : ⸨prog|
  str x0, [sp, #8]
⸩ = armFrame.slotSt 1 (.reg .X0) := rfl

example : ⸨prog|
  ldr x0, [sp, #8]
⸩ = armFrame.slotLd (.reg .X0) 1 := rfl

example : ⸨prog|
  ldr x16, =32768
  str x0, [sp, x16]
⸩ = armFrame.slotSt 4096 (.reg .X0) := rfl

example : ⸨prog|
  ldr x16, =32768
  ldr x0, [sp, x16]
⸩ = armFrame.slotLd (.reg .X0) 4096 := rfl

example : ⸨prog|
  mov x17, sp
  str x17, [sp, #8]
⸩ = armFrame.slotSt 1 .SP := rfl

example : ⸨prog|
  ldr x17, [sp, #8]
  mov sp, x17
⸩ = armFrame.slotLd .SP 1 := rfl

example : ⸨prog|
  stp x19, x20, [sp, #0]
  stp x21, x22, [sp, #16]
⸩ = armSaveRegs 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22] := rfl

example : ⸨prog|
  stp x19, x20, [sp, #8]
  str x21, [sp, #24]
⸩ = armSaveRegs 1 [.reg .X19, .reg .X20, .reg .X21] := rfl

example : ⸨prog|
  stp x19, x20, [sp, #504]
⸩ = armSaveRegs 63 [.reg .X19, .reg .X20] := rfl

example : ⸨prog|
  str x19, [sp, #512]
  str x20, [sp, #520]
⸩ = armSaveRegs 64 [.reg .X19, .reg .X20] := rfl

example : ⸨prog|
  ldp x19, x20, [sp, #0]
  ldp x21, x22, [sp, #16]
⸩ = armRestoreRegs 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22] := rfl

example : ⸨prog|
  ldp x19, x20, [sp, #8]
  ldr x21, [sp, #24]
⸩ = armRestoreRegs 1 [.reg .X19, .reg .X20, .reg .X21] := rfl

example : ⸨prog|
  ldp x19, x20, [sp, #504]
⸩ = armRestoreRegs 63 [.reg .X19, .reg .X20] := rfl

example : ⸨prog|
  ldr x19, [sp, #512]
  ldr x20, [sp, #520]
⸩ = armRestoreRegs 64 [.reg .X19, .reg .X20] := rfl

example : ⸨prog| uxtb x0, w0 ⸩ = (armFrame.canonAbi .bool (.reg .X0)).1 := rfl
example : ⸨prog| uxtb x0, w0 ⸩ = (armFrame.canonAbi i8 (.reg .X0)).1 := rfl
example : ⸨prog| uxth x0, w0 ⸩ = (armFrame.canonAbi i16 (.reg .X0)).1 := rfl
example : ⸨prog| mov w0, w0 ⸩ = (armFrame.canonAbi i32 (.reg .X0)).1 := rfl

example : ⸨prog|
  mov x16, sp
  uxtb x16, w16
  mov sp, x16
⸩ = (armFrame.canonAbi i8 .SP).1 := rfl

example : ⸨prog| bl f ⸩ = armFrame.call "f" := rfl
example : ⸨prog| b f ⸩ = armFrame.exitJmp "f" := rfl
example : ⸨prog| ret ⸩ = armFrame.ret := rfl

end ParserChecks

end LeanQbe.T.Arm64
