module

public import LeanQbe.T.Arm64.Frame
public import LeanQbe.T.AbiLemmas
import Kraken.AArch64.Parser
import all Kraken.Mem
import all Kraken.Separation

/-!
# AAPCS64 Arm64 Frame Verification (`T11b`)

Proves `armFrameSpec : FrameTarget armMach armFrame armCondReads`, `NoLab` invariants for all
frame/slot/ABI/call snippets, and `ParserChecks` against `Kraken.AArch64.Parser`.
All frame and slot proofs hold unconditionally up to `armFrameSize ns ≤ 2 ^ 64` (using `.X16`
literal-pool + register-offset fallback for `4096 ≤ armFrameSize ns` and `32768 ≤ 8 * ns`, and
`.X16`/`.X17` routing when slot/ABI operations target `.SP`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open Std Std.ExtHashMap

/-! ## 1. Frame size arithmetic, alignment, and address helpers -/

theorem armFrameSize_ge (ns : Nat) : 8 * ns + 8 ≤ armFrameSize ns := by
  unfold armFrameSize; omega

theorem armFrameSize_slots (ns : Nat) : 8 * ns ≤ armFrameSize ns := by
  have := armFrameSize_ge ns; omega

theorem armFrameSize_mod (ns : Nat) : armFrameSize ns % 16 = 0 := by
  unfold armFrameSize; omega

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
  simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
    Reg64s.getRegOrSp_sp64, BitVec.signed, Reg64s.getRegOrZr64, RegOrZr.base]
  exact congrArg (·, s) (ofInt_toInt_add_toNat _ _)

/-! ## 2. Frame helpers & shared building-block `Program.wp` lemmas -/

private theorem armFrame_upd_regs {s s' : MachineData} {gClob : List Reg} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r)
    (hflg : fClob = maskAll ∨ s'.status = s.status) :
    armMach.Frame armCondReads s s' gClob [] fClob := by
  refine ⟨hkeep, fun v => v.elim, ?_⟩
  rcases hflg with rfl | hst
  · intro c hdisj
    cases c <;> simp [FlagMask.disjoint, armCondReads, maskAll, maskN, maskZ, maskC, maskV] at hdisj
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
  simp only [t_step_simp, ExtRegExpr.interp, BitVec.apply_extend,
    Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits, Reg64s.getRegOrZr64,
    RegOrZr.base, BitVec.unsigned]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  exact hk _ rfl

private theorem armAddSpX16_fallsTo (s : MachineData) :
    armDirFallsTo (ins (.ADD_e (.low .SP .W64) (.low .SP .W64) (.ext (armUxtx .X16)))) s
      (fun s' => s' = { s with regs := { s.regs with SP := UInt64.ofBitVec (get s .SP + get s (.reg .X16)) } }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, ExtRegExpr.interp, BitVec.apply_extend,
    Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits, Reg64s.getRegOrZr64,
    RegOrZr.base, BitVec.unsigned]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  exact hk _ rfl

private theorem armSubSp_wp [Host] (n : Nat) (s : MachineData) :
    _root_.Program.wp (armSubSp n)
      (fun s' => s'.regs.SP = UInt64.ofBitVec (get s .SP - BitVec.ofNat 64 n) ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem) (fun _ _ => False) s := by
  dsimp only [armSubSp]
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
  dsimp only [armAddSp]
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
  dsimp only [armStSpXReg]
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
  dsimp only [armLdSpXReg]
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

theorem armPrologue_spec {h : Host} {k ns : Nat} {s : MachineData} {ra : Int64}
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
  dsimp only [armPrologue]
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

theorem armEpilogue_spec {h : Host} {k ns : Nat} {s : MachineData} {ra : Int64}
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
  dsimp only [armEpilogue]
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

theorem armSlotSt_spec {h : Host} {k i : Nat} {r : Reg} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hr : r ∉ armScratch)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ region (get s .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ G) :
    armMach.FallsTo armCondReads h k (armSlotSt i r) armScratch [] maskNone s
      (fun s' => s'.dmem =⋆
        cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) (get s r) ⋆ G) post := by
  letI := h
  apply armFallsTo_of_wp
  cases r with
  | reg x =>
    have hx16 : x ≠ .X16 := fun e => (ne_of_not_mem_armScratch hr).1 (e ▸ rfl)
    refine armWp_mono (armStSpXReg_wp x (8 * i) s hx16 hsp hmem) ?_
    rintro s' ⟨hsp', hx', hst', hdmem'⟩
    refine ⟨hdmem', armFrame_upd_regs (armKeep_regs _ (fun _ => hsp') (fun y hy => ?_)) (Or.inr hst')⟩
    exact hx' y (fun e => hy (by simp [e, armScratch]))
  | SP =>
    dsimp only [armSlotSt]
    refine armWp_cons (armMovToX_wp .X17 .SP s) ?_
    rintro s₁ rfl
    have hsp1 : (get (wr s .X17 (get s .SP)) .SP).toNat % 16 = 0 := by
      simpa [get_sp] using hsp
    have hmem1 : (region (get (wr s .X17 (get s .SP)) .SP + BitVec.ofNat 64 (8 * i)) 8 ⋆ G)
        (wr s .X17 (get s .SP)).dmem := by
      simpa [get_sp] using hmem
    refine armWp_mono (armStSpXReg_wp .X17 (8 * i) (wr s .X17 (get s .SP)) (by decide) hsp1 hmem1) ?_
    rintro s' ⟨hsp', hx', hst', hdmem'⟩
    have hx17 : get (wr s .X17 (get s .SP)) (.reg .X17) = get s .SP := get_wr_same _ _ _
    rw [hx17] at hdmem'
    simp only [get_sp, Reg64s.SP_setXReg] at hsp' hdmem'
    refine ⟨hdmem', armFrame_upd_regs (armKeep_regs _ (fun _ => hsp') (fun y hy => ?_)) (Or.inr hst')⟩
    have hy16 : y ≠ .X16 := fun e => hy (by simp [e, armScratch])
    have hy17 : y ≠ .X17 := fun e => hy (by simp [e, armScratch])
    rw [hx' y hy16, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy17.symm]

theorem armSlotLd_spec {h : Host} {k i : Nat} {rd : Reg} {v : BitVec 64} {s : MachineData}
    {G : Mem 64 → Prop} {post : MachineState → Prop}
    (hrd : rd ∉ armScratch)
    (hsp : (get s .SP).toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 (get s .SP + BitVec.ofNat 64 (8 * i)) v ⋆ G) :
    armMach.FallsTo armCondReads h k (armSlotLd rd i) (rd :: armScratch) [] maskNone s
      (fun s' => get s' rd = v ∧ s'.dmem = s.dmem) post := by
  letI := h
  apply armFallsTo_of_wp
  cases rd with
  | reg x =>
    refine armWp_mono (armLdSpXReg_wp x (8 * i) v s hsp hmem) ?_
    rintro s' ⟨hsp', hrx, hx', hst', hdmem'⟩
    refine ⟨⟨by simp [get_reg, hrx], hdmem'⟩,
      armFrame_upd_regs (armKeep_regs _ (fun _ => hsp') (fun y hy => ?_)) (Or.inr hst')⟩
    have hyx : y ≠ x := fun e => hy (by simp [e])
    have hy16 : y ≠ .X16 := fun e => hy (by simp [e, armScratch])
    exact hx' y hyx hy16
  | SP =>
    dsimp only [armSlotLd]
    refine armWp_append (armLdSpXReg_wp .X17 (8 * i) v s hsp hmem) ?_
    rintro s₁ ⟨hsp1, hx17, hx1, hst1, hdmem1⟩
    refine armWp_mono (armMovToSp_wp .X17 s₁) ?_
    rintro s' rfl
    refine ⟨⟨by simp [get_sp, get_reg, hx17], hdmem1⟩,
      armFrame_upd_regs (armKeep_regs _ (fun h => absurd List.mem_cons_self h) (fun y hy => ?_))
        (Or.inr hst1)⟩
    have hy17 : y ≠ .X17 := fun e => hy (by simp [e, armScratch])
    have hy16 : y ≠ .X16 := fun e => hy (by simp [e, armScratch])
    exact hx1 y hy17 hy16

theorem armCanonAbi_spec {h : Host} {k : Nat} {t : Ty} {r : Reg} {v : Val t}
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
      dsimp only [armCanonAbi]
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
      dsimp only [armCanonAbi]
      simp only [hcond, ↓reduceIte]
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

theorem armCall_spec {h : Host} {k : Nat} {sym : Sym} {s : MachineData}
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
  simp only [t_step_simp, armCallD, Reg64s.setRegOrZr_reg64]
  have hra : BitVec.ofInt 64 (Host.addrOf (k + 1)).toInt = (Host.addrOf (k + 1)).toBitVec := by
    rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  rw [hra]
  refine hk (wr s .X30 (Host.addrOf (k + 1)).toBitVec) (by simp [get_sp]) ?_
    (get_wr_same _ _ _) (by simpa [get_sp] using hmem)
  refine armFrame_upd_regs (armKeep_regs _ (fun _ => rfl) (fun y hy => ?_)) (Or.inl rfl)
  have hy30 : y ≠ .X30 := fun e => hy (by simp [e])
  exact Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy30.symm

theorem armExitJmp_spec {h : Host} {k : Nat} {sym : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : [armJmpD sym].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      armMach.Frame armCondReads s s' armScratch [] maskNone → s'.dmem = s.dmem →
      Eventually (step1 Host.exe) post ⟨s', hostLabel h sym⟩) :
    armMach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp, armJmpD]
  exact hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone) rfl

theorem armRet_spec {h : Host} {k : Nat} {s : MachineData} {ra : Int64}
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
  simp only [t_step_simp, armRetD, Reg64s.getRegOrZr_reg64]
  have hpc : Int64.ofInt (s.regs.getXReg .X30).toBitVec.signed = ra := by
    rw [show (s.regs.getXReg .X30).toBitVec = ra.toBitVec from hra]
    simp [BitVec.signed, Int64.toInt_toBitVec, Int64.ofInt_toInt]
  rw [hpc]
  exact hk s (fun _ _ => rfl) (fun v => v.elim) (by simp) rfl

/-! ## 5. `armFrameSpec : FrameTarget armMach armFrame armCondReads` -/

def armFrameSpec : FrameTarget armMach armFrame armCondReads where
  RetAddr sp _ := region sp 0
  raReg s ra := get s (.reg .X30) = ra.toBitVec
  spEntry sp := sp.toNat % 16 = 0
  spOk sp := sp.toNat % 16 = 0
  Saved sp ra ns :=
    cell64 (sp - BitVec.ofNat 64 (armFrameSize ns) + BitVec.ofNat 64 (8 * ns)) ra.toBitVec ⋆
      region (sp - BitVec.ofNat 64 (armFrameSize ns) + BitVec.ofNat 64 (8 * ns) + 8#64)
        (armFrameSize ns - 8 * ns - 8)
  sp_disj := by simp
  scratch_disj := by simp
  cs_disj := by simp
  ra_disj := by simp
  argRegs_nodup := by decide
  retRegs_nodup := by decide
  retAddr_region _ _ _ h := h
  raReg_of_raRegs _ _ _ h hra := by rw [← hra]; exact h (.reg .X30) (by simp)
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
  canonAbi_spec {h} {_} {_} {_} {_} {_} {_} ht hr hh :=
    letI := h; armCanonAbi_spec ht hr hh
  call_spec {h} {_} {_} {_} {_} {_} hc hmem hk :=
    letI := h; armCall_spec hc hmem hk
  exitJmp_spec {h} {_} {_} {_} {_} hc hk :=
    letI := h; armExitJmp_spec hc hk
  ret_spec {h} {_} {_} {_} {_} {_} hc hra _ hk :=
    letI := h; armRet_spec hc hra hk

/-! ## 6. `NoLab` lemmas -/

section NoLab

theorem armPrologue_noLab (ns : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ (armFrame.prologue ns).1 := by
  dsimp only [armFrame, armPrologue, armSubSp, armStSpXReg]
  simp only [List.mem_append, not_or]
  constructor <;> split <;> simp [armLdrPool, ins]

theorem armEpilogue_noLab (ns : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ (armFrame.epilogue ns).1 := by
  dsimp only [armFrame, armEpilogue, armLdSpXReg, armAddSp]
  simp only [List.mem_append, not_or]
  constructor <;> split <;> simp [armLdrPool, ins]

theorem armSlotSt_noLab (i : Nat) (r : Reg) (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.slotSt i r := by
  cases r with
  | reg x =>
    dsimp only [armFrame, armSlotSt, armStSpXReg]
    split <;> simp [armLdrPool, ins]
  | SP =>
    dsimp only [armFrame, armSlotSt, armStSpXReg]
    simp only [List.mem_cons, List.singleton_append, not_or]
    refine ⟨by simp [armMovToX, ins], ?_⟩
    split <;> simp [armLdrPool, ins]

theorem armSlotLd_noLab (rd : Reg) (i : Nat) (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.slotLd rd i := by
  cases rd with
  | reg x =>
    dsimp only [armFrame, armSlotLd, armLdSpXReg]
    split <;> simp [armLdrPool, ins]
  | SP =>
    dsimp only [armFrame, armSlotLd, armLdSpXReg]
    simp only [List.mem_append, List.mem_singleton, not_or]
    refine ⟨?_, by simp [armMovToSp, ins]⟩
    split <;> simp [armLdrPool, ins]

theorem armCanonAbi_noLab (t : Ty) (r : Reg) (l : Sym) :
    Kraken.Directive.label l ∉ (armFrame.canonAbi t r).1 := by
  cases r with
  | reg x =>
    cases t with
    | bool => simp [armCanonAbi, armCanonAbiXReg, ins]
    | bits n =>
      dsimp only [armFrame, armCanonAbi, armCanonAbiXReg]
      repeat (split <;> try simp [ins])
      all_goals simp [ins]
    | float _ | pair _ _ => simp [armCanonAbi, armCanonAbiXReg]
  | SP =>
    cases t with
    | bool => simp [armCanonAbi, armCanonAbiXReg, armMovToX, armMovToSp, ins]
    | bits n =>
      dsimp only [armFrame, armCanonAbi]
      split
      · simp only [List.append_assoc, List.mem_cons, List.mem_append, not_or]
        refine ⟨by simp [armMovToX, ins], ?_, by simp [armMovToSp, ins]⟩
        dsimp only [armCanonAbiXReg]
        repeat (split <;> try simp [ins])
        all_goals simp [ins]
      · simp
    | float _ | pair _ _ => simp [armCanonAbi]

theorem armCall_noLab (sym : Sym) (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.call sym := by
  simp [armCallD, ins]

theorem armExitJmp_noLab (sym : Sym) (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.exitJmp sym := by
  simp [armJmpD, ins]

theorem armRet_noLab (l : Sym) :
    Kraken.Directive.label l ∉ armFrame.ret := by
  simp [armRetD, ins]

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
