module

public import LeanQbe.T.Arm64.IselScrLemmas2
import LeanQbe.T.Arm64.IselFlagHooksLemmas

/-!
# AArch64 Wave 6.2-A `armCmpOpScr` Proofs — Part 3

Verifies `armZeroCmpScr_wp`, `armCmpOpScr_wp` (`armCmpOpScrIns`, preserving `ScrOk`,
`AbiGprHolds`, and `FlagCmpOk`), and `armCmpOpScrIns_nil_fst`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. `ScrOk` + `AbiGprHolds` Helpers and `armZeroCmpScr_wp` -/

theorem abiGprHolds_bool_01' {v : BitVec 64} {b : Bool}
    (h : v = BitVec.ofNat 64 b.toNat) : AbiGprHolds v .bool b := by
  cases b <;> simp [AbiGprHolds, h]

theorem scrOk_nil (s : MachineData) : ScrOk armMach armScratch [] s := by
  intro p hp; cases hp

private theorem armZeroAndsFinishScr_wp [Host] {n : Nat} (hn' : n = 8 ∨ n = 16) (o : CmpOp)
    (neg : Bool) (rx : XReg) (dst : PDst Reg Empty ArmCond .bool)
    {scr : List (Reg × BitVec 64)} {vr : BitVec n} {c : List Instr} {clob : FlagMask}
    {s : MachineData}
    (hrx : (s.regs.getXReg rx).toBitVec.setWidth n = vr)
    (hscr : ScrOk armMach armScratch scr s)
    (hev : o.evalBits vr 0#n = (if neg then CmpOp.ne else CmpOp.eq).evalBits vr 0#n)
    (hfin : (match dst with
      | .flag cf =>
        if cf == (if neg then ArmCond.ne else ArmCond.eq) then
          some ([armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32)
            (.int64 (if n == 8 then 0xFF else 0xFFFF)))], maskNZCV)
        else none
      | .gpr (.reg d) =>
        some ([armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32)
            (.int64 (if n == 8 then 0xFF else 0xFFFF))),
          armCset64I d (if neg then ArmCond.ne else ArmCond.eq)], maskNZCV)
      | .gpr .SP | .vec _ => none) = some (c, clob))
    (hd : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst (o.evalBits vr 0#n) ∧
      (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr s' rd) .bool (o.evalBits vr 0#n)) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch) [] clob ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s := by
  have ands816_wp :
      let c64 : BitVec 64 := BitVec.ofNat 64 (if n == 8 then 0xFF else 0xFFFF)
      _root_.Program.wp
        [ins (.ANDS_i (xzr .W32) (zr rx .W32) (.int64 (if n == 8 then 0xFF else 0xFFFF)))]
        (fun s' => (if neg then ArmCond.ne else ArmCond.eq).interp s'.status =
            (if neg then CmpOp.ne else CmpOp.eq).evalBits vr 0#n ∧
          s'.dmem = s.dmem ∧
          armMach.Frame armCondReads s s' armScratch [] maskNZCV ∧
          ScrOk armMach armScratch scr s')
        (fun _ _ => False) s := by
    intro c64
    have hc64 : (if n == 8 then (0xFF : Int64) else 0xFFFF) = Int64.ofBitVec c64 := by
      rcases hn' with rfl | rfl <;> rfl
    rw [hc64]
    refine armWp_mono (armAndsImm_wp .W32 rx c64 s) ?_
    rintro sx rfl
    refine ⟨?_, rfl, armFrame_nzcv fun _ _ => rfl, scrOk_of_keeps hscr fun _ _ => rfl⟩
    have hmask : c64.setWidth 32 = (~~~0#n).setWidth 32 := by
      rcases hn' with rfl | rfl <;> rfl
    have hrx32 : ((s.regs.getXReg rx).toBitVec.setWidth 32).setWidth n = vr := by
      rwa [BitVec.setWidth_setWidth_of_le _ (by rcases hn' with rfl | rfl <;> decide)]
    have hz : ((s.regs.getXReg rx).toBitVec.setWidth 32 &&& c64.setWidth 32 == 0#32) =
        (vr == 0#n) := by
      rw [hmask, subword_and_eq_zero (by rcases hn' with rfl | rfl <;> decide) hrx32]
      have hand : vr &&& ~~~0#n = vr := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
      rw [hand]
    simpa [RegWidth.bits, MemWidth.bits] using testCond_eq_of_z neg _ vr hz
  cases dst with
  | vec vr' => exact vr'.elim
  | flag cf =>
    dsimp only at hfin
    by_cases heqc : (cf == (if neg then ArmCond.ne else ArmCond.eq)) = true
    · simp only [heqc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hfin
      rcases hfin with ⟨rfl, rfl⟩
      have hcf : cf = (if neg then ArmCond.ne else ArmCond.eq) := by
        cases cf <;> cases neg <;> first | rfl | exact absurd heqc (by decide)
      subst hcf
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono ands816_wp ?_
      rintro sx ⟨hcc, hdm, hfr, hsc⟩
      refine ⟨?_, (fun _ h => by cases h), hdm, hfr, hsc⟩
      simpa [Machine.PDstHolds, hev] using hcc
    · simp only [heqc, Bool.false_eq_true, ↓reduceIte] at hfin; cases hfin
  | gpr r => cases r with | SP => cases hfin | reg d =>
    rcases Option.some.inj hfin with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    have hdScr : XRegOrSp.reg d ∉ armScratch := hd (.reg d) (by simp [tupDstGprs])
    refine armWp_cons ands816_wp ?_
    rintro sx ⟨hcc, hdm, hfr, hsc⟩
    refine armWp_mono (armCset64_wp d (if neg then .ne else .eq) sx) ?_
    rintro sy rfl
    refine ⟨?_, ?_, hdm, armFrame_nzcv fun r hr => ?_, scrOk_wr_nonScr hsc hdScr⟩
    · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hcc, hev]
      cases (if neg then CmpOp.ne else CmpOp.eq).evalBits vr 0#n <;> rfl
    · intro rd hrd; cases hrd
      exact abiGprHolds_bool_01' (by simp [get_wr_same, hcc, hev])
    · have hne : r ≠ .reg d ∧ r ∉ armScratch :=
        ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne sx d _ r hne.1]; exact hfr.1 r hne.2

private theorem armZeroCmpScr_wp [Host] {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    (o : CmpOp) (rx : XReg) (dst : PDst Reg Empty ArmCond .bool)
    {scr : List (Reg × BitVec 64)} {vr : BitVec n} {c : List Instr} {clob : FlagMask}
    {s : MachineData}
    (hc : armZeroCmpIns? o n rx dst = some (c, clob))
    (hrx : (s.regs.getXReg rx).toBitVec.setWidth n = vr)
    (hd : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst (o.evalBits vr 0#n) ∧
      (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr s' rd) .bool (o.evalBits vr 0#n)) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch) [] clob ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s := by
  have hnw := mem_armWidths_le_armWidth hn
  have hn0 : 0 < n := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> decide
  have sltBitEq : ((s.regs.getXReg rx).toBitVec.setWidth (armWidthOf n).bits).getLsbD (n - 1) =
      vr.slt 0#n := by
    have hnltw : n - 1 < (armWidthOf n).bits := by omega
    rw [← hrx, BitVec.getLsbD_setWidth]
    have hbit : vr.slt 0#n = vr.msb := by
      simp only [BitVec.slt, BitVec.toInt_eq_msb_cond, BitVec.msb_zero, BitVec.toNat_zero,
        Bool.false_eq_true, ↓reduceIte]
      have hlt : (vr.toNat : Int) < (2 : Int) ^ n := by exact_mod_cast vr.isLt
      have h0 : (0 : Int) ≤ vr.toNat := Int.natCast_nonneg _
      cases hv : vr.msb <;> simp <;> try omega
    rw [← hrx] at hbit
    rw [hbit, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]
    simp [show n - 1 < n by omega, hnltw]
  cases o with
  | slt =>
    cases dst with
    | vec vr' => exact vr'.elim
    | flag _ => dsimp only [armZeroCmpIns?] at hc; cases hc
    | gpr r => cases r with
      | SP => dsimp only [armZeroCmpIns?] at hc; cases hc
      | reg d =>
        dsimp only [armZeroCmpIns?] at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        have hdScr : XRegOrSp.reg d ∉ armScratch := hd (.reg d) (by simp [tupDstGprs])
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl
        all_goals
          (refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
             simp only [armWidthOf, t_step_simp]
             rw [evalUBFM_bit _ (by decide)]; exact hk _ rfl) ?_
           rintro s' rfl
           refine ⟨?_, ?_, rfl, frame_wr d _ List.mem_cons_self maskNone,
             scrOk_wr_nonScr hscr hdScr⟩
           · simp only [Machine.PDstHolds, GprHolds, get_wr_same, RegWidth.bits, MemWidth.bits]
             have heval : CmpOp.slt.evalBits vr 0#_ = vr.slt 0#_ := rfl
             rw [heval, ← sltBitEq]; simp only [armWidthOf, RegWidth.bits, MemWidth.bits]
             cases ((s.regs.getXReg rx).toBitVec.setWidth _).getLsbD _ <;> decide
           · intro rd hrd; cases hrd
             have heval : CmpOp.slt.evalBits vr 0#_ = vr.slt 0#_ := rfl
             rw [heval, ← sltBitEq]
             refine abiGprHolds_bool_01' ?_
             simp only [get_wr_same, armWidthOf, RegWidth.bits, MemWidth.bits]
             cases ((s.regs.getXReg rx).toBitVec.setWidth _).getLsbD _ <;> decide)
  | sge =>
    cases dst with
    | vec vr' => exact vr'.elim
    | flag _ => dsimp only [armZeroCmpIns?] at hc; cases hc
    | gpr r => cases r with
      | SP => dsimp only [armZeroCmpIns?] at hc; cases hc
      | reg d =>
        dsimp only [armZeroCmpIns?] at hc; split at hc
        · rename_i hn816
          have hn' : n = 8 ∨ n = 16 := by
            rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
          rcases Option.some.inj hc with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          have hdScr : XRegOrSp.reg d ∉ armScratch := hd (.reg d) (by simp [tupDstGprs])
          have hw32 : armWidthOf n = .W32 := by rcases hn' with rfl | rfl <;> rfl
          have hsge : CmpOp.sge.evalBits vr 0#n = !(vr.slt 0#n) := by
            simp only [CmpOp.evalBits, BitVec.sle, BitVec.slt]
            by_cases hlt : vr.toInt < (0#n).toInt
            · simp only [hlt, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
            · simp only [hlt, decide_false, Bool.not_false, decide_eq_true_eq]; omega
          have hbit32 : ((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n - 1) =
              vr.slt 0#n := by
            simpa [hw32] using sltBitEq
          refine armWp_cons (armDirFallsTo_wp (Q := fun s' => s' = wr s d
              ((BitVec.ofNat 32
                (((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n - 1)).toNat).setWidth 64))
            fun {_} p next jmp Q hk => by
              simp only [t_step_simp]
              rw [evalUBFM_bit _ (by rcases hn' with rfl | rfl <;> decide)]
              exact hk _ rfl) ?_
          rintro s₁ rfl
          refine armWp_mono (armDirFallsTo_wp (Q := fun s₂ => s₂ = wr (wr s d
              ((BitVec.ofNat 32 (((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD
                (n - 1)).toNat).setWidth 64)) d
              ((BitVec.ofNat 32 (((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD
                (n - 1)).toNat ^^^ 1#32).setWidth 64))
            fun {_} p next jmp Q hk => by
              simp only [t_step_simp, ConstExpr.interp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
                RegWidth.bits, MemWidth.bits, Reg64s.getXReg_setXReg_same,
                BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
                show BitVec.ofInt 32 (Int64.toInt 1) = 1#32 from rfl]
              exact hk _ rfl) ?_
          rintro s₂ rfl; rw [wr_wr_same]
          refine ⟨?_, ?_, rfl, frame_wr d _ List.mem_cons_self maskNone,
            scrOk_wr_nonScr hscr hdScr⟩
          · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hsge, ← hbit32]
            cases ((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n - 1) <;> decide
          · intro rd hrd; cases hrd; refine abiGprHolds_bool_01' ?_
            simp only [get_wr_same, hsge, ← hbit32]
            cases ((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n - 1) <;> decide
        · cases hc
  | eq =>
    dsimp only [armZeroCmpIns?] at hc; split at hc
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      dsimp only [armCmpCond] at hc
      exact armZeroAndsFinishScr_wp hn' .eq false rx dst hrx hscr rfl hc hd
    · cases hc
  | ne =>
    dsimp only [armZeroCmpIns?] at hc; split at hc
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      dsimp only [armCmpCond] at hc
      exact armZeroAndsFinishScr_wp hn' .ne true rx dst hrx hscr rfl hc hd
    · cases hc
  | ule =>
    cases dst with
    | vec vr' => exact vr'.elim
    | flag _ => dsimp only [armZeroCmpIns?] at hc; cases hc
    | gpr r => cases r with
      | SP => dsimp only [armZeroCmpIns?] at hc; cases hc
      | reg d =>
        dsimp only [armZeroCmpIns?] at hc; split at hc
        · rename_i hn816
          have hn' : n = 8 ∨ n = 16 := by
            rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
          have hev : CmpOp.ule.evalBits vr 0#n = CmpOp.eq.evalBits vr 0#n := by
            simp only [CmpOp.evalBits, BitVec.ule, BitVec.toNat_zero, Nat.le_zero]
            by_cases hv : vr = 0#n
            · simp [hv]
            · have hne0 : vr.toNat ≠ 0 := fun h => hv (BitVec.eq_of_toNat_eq (by simpa using h))
              simp [hv, hne0]
          exact armZeroAndsFinishScr_wp hn' .ule false rx (.gpr (.reg d)) hrx hscr hev hc hd
        · cases hc
  | ugt =>
    cases dst with
    | vec vr' => exact vr'.elim
    | flag _ => dsimp only [armZeroCmpIns?] at hc; cases hc
    | gpr r => cases r with
      | SP => dsimp only [armZeroCmpIns?] at hc; cases hc
      | reg d =>
        dsimp only [armZeroCmpIns?] at hc; split at hc
        · rename_i hn816
          have hn' : n = 8 ∨ n = 16 := by
            rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
          have hev : CmpOp.ugt.evalBits vr 0#n = CmpOp.ne.evalBits vr 0#n := by
            simp only [CmpOp.evalBits, BitVec.ult, BitVec.toNat_zero]
            by_cases hv : vr = 0#n
            · simp [hv]
            · have hpos : 0 < vr.toNat :=
                Nat.pos_of_ne_zero (fun h => hv (BitVec.eq_of_toNat_eq (by simpa using h)))
              simp [hv, hpos]
          exact armZeroAndsFinishScr_wp hn' .ugt true rx (.gpr (.reg d)) hrx hscr hev hc hd
        · cases hc
  | ult | uge | sle | sgt => dsimp only [armZeroCmpIns?] at hc; cases hc

/-! ## 2. Register-Preserving `armCmpImmScr_wp` & `armCmpOpScr_wp` -/

private theorem imm12_toNat_lt {n : Nat} {c : BitVec n} {ei : ExtOrImmReg}
    (h : armImm12? c = some ei) : c.toNat < 16777216 := by
  dsimp only [armImm12?] at h; split at h
  · rename_i hlt; have := Nat.blt_eq.mp hlt; omega
  · split at h
    · rename_i hand; simp only [Bool.and_eq_true, Nat.blt_eq] at hand; exact hand.1
    · cases h

private theorem adds_eq_subs_neg' {w : Nat} (_hw : 32 ≤ w) (x k : BitVec w)
    (hk0 : k ≠ 0#w) (hklt : k.toNat < 16777216) :
    StatusFlags.adds (x + k) x k = StatusFlags.subs (x - (-k)) x (-k) := by
  have hpow : 16777216 < 2 ^ (w - 1) := by
    have : 2 ^ 31 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have : 16777216 < 2 ^ 31 := by decide
    omega
  have hxlt := x.isLt
  have hkpos : 0 < k.toNat := by
    rcases Nat.eq_zero_or_pos k.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hk0
    · exact h
  have hpoww : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have hw1 : (w - 1) + 1 = w := by omega
    calc 2 ^ w = 2 ^ ((w - 1) + 1) := by rw [hw1]
      _ = 2 * 2 ^ (w - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hres : x + k = x - (-k) := by rw [BitVec.sub_neg]
  have hnknat : (-k).toNat = 2 ^ w - k.toNat := by
    rw [BitVec.toNat_neg]; exact Nat.mod_eq_of_lt (by omega)
  have hc : ((x + k).unsigned != x.unsigned + k.unsigned) =
      ((x - (-k)).unsigned == x.unsigned - (-k).unsigned) := by
    rw [← hres]; simp only [BitVec.unsigned, BitVec.toNat_add]
    by_cases hsum : x.toNat + k.toNat < 2 ^ w
    · have hm : (x.toNat + k.toNat) % 2 ^ w = x.toNat + k.toNat := Nat.mod_eq_of_lt hsum
      rw [hm, hnknat]
      have hb1 : (((x.toNat + k.toNat : Nat) : Int) != (x.toNat : Int) + (k.toNat : Int)) =
          false := by simp
      have hb2 : (((x.toNat + k.toNat : Nat) : Int) ==
          (x.toNat : Int) - ((2 ^ w - k.toNat : Nat) : Int)) = false :=
        beq_false_of_ne (by omega)
      exact hb1.trans hb2.symm
    · have hq : 2 ^ w ≤ x.toNat + k.toNat := by omega
      have hm : (x.toNat + k.toNat) % 2 ^ w = x.toNat + k.toNat - 2 ^ w := by
        rw [Nat.mod_eq_sub_mod hq, Nat.mod_eq_of_lt (by omega)]
      rw [hm, hnknat]
      have hb1 : (((x.toNat + k.toNat - 2 ^ w : Nat) : Int) !=
          (x.toNat : Int) + (k.toNat : Int)) = true := bne_iff_ne.mpr (by omega)
      have hb2 : (((x.toNat + k.toNat - 2 ^ w : Nat) : Int) ==
          (x.toNat : Int) - ((2 ^ w - k.toNat : Nat) : Int)) = true := beq_iff_eq.mpr (by omega)
      exact hb1.trans hb2.symm
  have hksgn : k.signed = (k.toNat : Int) := by
    simp only [BitVec.signed, BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hnksgn : (-k).signed = -(k.toNat : Int) := by
    simp only [BitVec.signed, BitVec.toInt_eq_toNat_cond, hnknat]; split <;> omega
  have hv : ((x + k).signed != x.signed + k.signed) =
      ((x - (-k)).signed != x.signed - (-k).signed) := by
    rw [← hres, hksgn, hnksgn,
      show x.signed - -(k.toNat : Int) = x.signed + (k.toNat : Int) by omega]
  simp only [StatusFlags.adds, StatusFlags.subs, StatusFlags.from_result]; rw [hc, hv, hres]

private theorem armCmpImmScr_wp [Host] {n : Nat} (hn : n = 32 ∨ n = 64) (w : RegWidth)
    (hw : w.bits = n) (rx : XReg) (imm : BitVec n) {cmp : List Instr}
    (hc : armCmpImmIns? w rx imm = some cmp) (s : MachineData) :
    _root_.Program.wp (emitClean cmp)
      (fun sx => sx.regs = s.regs ∧
        sx.status = StatusFlags.subs
          ((s.regs.getXReg rx).toBitVec.setWidth n - imm)
          ((s.regs.getXReg rx).toBitVec.setWidth n) imm ∧
        sx.dmem = s.dmem ∧ armMach.Frame armCondReads s sx armScratch [] maskNZCV)
      (fun _ _ => False) s := by
  have hn64 : n ≤ 64 := by rcases hn with rfl | rfl <;> decide
  dsimp only [armCmpImmIns?] at hc
  cases himm : armImm12? imm with
  | some ei =>
    simp only [himm, Option.some.injEq] at hc; subst hc
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armDirFallsTo_wp (Q := fun sx => sx = { s with
        status := StatusFlags.subs
          ((s.regs.getXReg rx).toBitVec.setWidth w.bits - imm.setWidth w.bits)
          ((s.regs.getXReg rx).toBitVec.setWidth w.bits) (imm.setWidth w.bits) })
      fun {_} p next jmp Q hk => by
        have hm := armImm12_some hn64 himm w p s.regs
        dsimp only [ExtOrImmReg.interp] at hm
        cases w <;>
          ( simp only [t_step_simp, Reg64s.setRegOrZr_xzr] at hm ⊢
            rw [hm]
            exact hk _ (by simp [RegWidth.bits, MemWidth.bits]) ) ) ?_
    rintro s₁ rfl
    refine ⟨rfl, ?_, rfl, armFrame_nzcv fun _ _ => rfl⟩
    cases w <;> simp only [RegWidth.bits, MemWidth.bits] at hw <;> subst hw <;>
      simp [BitVec.setWidth_eq]
  | none =>
    simp only [himm] at hc; split at hc; · cases hc
    · rename_i hne0
      have himm0 : imm ≠ 0#n := fun e => hne0 (beq_iff_eq.mpr e)
      have hnimm0 : -imm ≠ 0#n := fun h => himm0 (by simpa using congrArg (- ·) h)
      cases hni : armImm12? (-imm) with
      | none => simp [hni] at hc
      | some ei =>
        simp only [hni, Option.some.injEq] at hc; subst hc
        simp only [emitClean_cons, emitClean_nil]
        refine armWp_mono (armDirFallsTo_wp (Q := fun sx => sx = { s with
            status := StatusFlags.adds
              ((s.regs.getXReg rx).toBitVec.setWidth w.bits + (-imm).setWidth w.bits)
              ((s.regs.getXReg rx).toBitVec.setWidth w.bits) ((-imm).setWidth w.bits) })
          fun {_} p next jmp Q hk => by
            have hm := armImm12_some hn64 hni w p s.regs
            dsimp only [ExtOrImmReg.interp] at hm
            cases w <;>
              ( simp only [t_step_simp, Reg64s.setRegOrZr_xzr] at hm ⊢
                rw [hm]
                exact hk _ (by simp [RegWidth.bits, MemWidth.bits]) ) ) ?_
        rintro s₁ rfl
        refine ⟨rfl, ?_, rfl, armFrame_nzcv fun _ _ => rfl⟩
        have hlt : (-imm).toNat < 16777216 := imm12_toNat_lt hni
        cases w <;> simp only [RegWidth.bits, MemWidth.bits] at hw <;> subst hw <;>
          simp only [BitVec.setWidth_eq] <;>
          rw [adds_eq_subs_neg' (by decide) _ _ hnimm0 hlt, BitVec.neg_neg]

private theorem cmp_sub3264 {sx : MachineData} {m : Nat} (hm : m = 32 ∨ m = 64) {x y : BitVec m}
    (hst : sx.status = StatusFlags.subs (x - y) x y) :
    FlagCmpOk armMach armGpr sx x y false := by
  intro co' cc' _ hco'; cases hco'; dsimp only [Machine.evalCond, armMach]; rw [hst]
  exact armCmpCond_subs hm co' x y

private theorem cmp_signExtEval {m : Nat} (hm : m = 8 ∨ m = 16) (co' : CmpOp) (x y : BitVec m) :
    co'.evalBits (x.signExtend 32) (y.signExtend 32) = co'.evalBits x y := by
  have hle : m ≤ 32 := by rcases hm with rfl | rfl <;> decide
  have hmsb : ∀ z : BitVec m, (z.signExtend 32).msb = z.msb := fun z => by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
    have hz : z.msb = z.getLsbD (m - 1) := by
      rcases hm with rfl | rfl <;> exact BitVec.msb_eq_getLsbD_last z
    rw [hz]; rcases hm with rfl | rfl <;> simp
  have hseNat : ∀ z : BitVec m,
      (z.signExtend 32).toNat = if z.msb then 2 ^ 32 - 2 ^ m + z.toNat else z.toNat := fun z => by
    have hltz := z.isLt; have hlt32 := (z.signExtend 32).isLt
    have hti := BitVec.toInt_signExtend_of_le (x := z) hle
    rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond, hmsb z] at hti
    cases hz : z.msb <;> simp only [hz, ↓reduceIte, Bool.false_eq_true] at hti ⊢ <;>
      rcases hm with rfl | rfl <;> omega
  have hmle : ∀ z : BitVec m, z.msb = true ↔ 2 ^ (m - 1) ≤ z.toNat := fun z => by
    rw [BitVec.msb_eq_decide, decide_eq_true_eq]
  have hult : ∀ a b : BitVec m, (a.signExtend 32).ult (b.signExtend 32) = a.ult b := fun a b => by
    have ha := a.isLt; have hb := b.isLt; simp only [BitVec.ult, hseNat]
    cases ha' : a.msb <;> cases hb' : b.msb
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ha2 : ¬(2 ^ (m - 1) ≤ a.toNat) := fun h => by
        have := (hmle a).mpr h; rw [ha'] at this; cases this
      have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      rcases hm with rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
      have hb2 : ¬(2 ^ (m - 1) ≤ b.toNat) := fun h => by
        have := (hmle b).mpr h; rw [hb'] at this; cases this
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      rcases hm with rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
    · simp only [↓reduceIte]
      have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
      have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      rcases hm with rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
  have heq : (x.signExtend 32 = y.signExtend 32) ↔ x = y := by
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    have h' := congrArg (BitVec.setWidth m) h
    simpa only [setWidth_signExtend_self hle] using h'
  have hule : ∀ a b : BitVec m, (a.signExtend 32).ule (b.signExtend 32) = a.ule b := fun a b => by
    have ha := a.isLt; have hb := b.isLt; simp only [BitVec.ule, hseNat]
    cases ha' : a.msb <;> cases hb' : b.msb
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ha2 : ¬(2 ^ (m - 1) ≤ a.toNat) := fun h => by
        have := (hmle a).mpr h; rw [ha'] at this; cases this
      have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      rcases hm with rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
      have hb2 : ¬(2 ^ (m - 1) ≤ b.toNat) := fun h => by
        have := (hmle b).mpr h; rw [hb'] at this; cases this
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      rcases hm with rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
    · simp only [↓reduceIte]
      have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
      have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      rcases hm with rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
  cases co' with
  | eq => simp only [CmpOp.evalBits, heq]
  | ne => simp only [CmpOp.evalBits, ne_eq, heq]
  | ult => exact hult x y
  | ule => exact hule x y
  | ugt => exact hult y x
  | uge => exact hule y x
  | slt | sle | sgt | sge => exact cmp_subword_signed hm _ rfl x y

private theorem cmp_sub816 {n : Nat} {sx : MachineData} (hn' : n = 8 ∨ n = 16) {x y : BitVec n}
    (hst : sx.status = StatusFlags.subs (x.signExtend 32 - y.signExtend 32)
      (x.signExtend 32) (y.signExtend 32)) :
    FlagCmpOk armMach armGpr sx x y false := by
  intro co' cc' _ hco'; cases hco'; dsimp only [Machine.evalCond, armMach]; rw [hst]
  exact (armCmpCond_subs (Or.inl rfl) co' _ _).trans (cmp_signExtEval hn' co' x y)

private theorem cmpScr_flagsExtract {o : CmpOp} {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool} {lf : Bool}
    (hfl : armCmpFlagsOut o n pa pb dst = some lf) :
    ((n = 32 ∨ n = 64) ∨ armIsSignedCmp o = true) ∧
    (match pa, pb with
      | .gpr (.reg ra), .imm cb =>
        (!(cb == 0#n && (armZeroCmpIns? o n ra dst).isSome)) = true ∧ lf = true
      | .imm ca, .gpr (.reg rb) =>
        if ca == 0#n then (armZeroCmpIns? o.swap n rb dst = none) ∧ lf = false
        else if n == 32 || n == 64 then lf = !(armCmpImmIns? (armWidthOf n) rb ca).isSome
        else lf = false
      | .gpr (.reg _), .gpr (.reg _) => lf = true
      | _, _ => False) := by
  dsimp only [armCmpFlagsOut] at hfl
  split at hfl; · cases hfl
  split at hfl; · cases hfl
  rename_i _ hnotbad
  have hsgnOk : (n = 32 ∨ n = 64) ∨ armIsSignedCmp o = true := by
    rcases mem_armWidths hn with rfl | rfl | rfl | rfl
    · simp at hnotbad; exact Or.inr hnotbad
    · simp at hnotbad; exact Or.inr hnotbad
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
  refine ⟨hsgnOk, ?_⟩
  simp only [Option.bind_eq_some_iff] at hfl
  rcases hfl with ⟨lf', hlf', hfin⟩
  have hlfEq : lf' = lf := by
    cases dst with
    | gpr r => cases r <;> simp at hfin; exact hfin
    | flag cf =>
      dsimp only at hfin
      by_cases hcf : (cf == armCmpCond (if lf' then o else o.swap)) = true
      · simp only [hcf, ↓reduceIte, Option.some.injEq] at hfin; exact hfin
      · simp only [hcf, ↓reduceIte, reduceCtorEq] at hfin
    | vec v => exact v.elim
  subst hlfEq
  cases pa with
  | vec v => exact v.elim
  | imm ca => cases pb with
    | vec v => exact v.elim
    | imm _ => simp at hlf'
    | gpr r2 => cases r2 with
      | SP => simp at hlf'
      | reg rb =>
        dsimp only at hlf'
        cases hca0 : ca == 0#n <;>
          simp only [hca0, Bool.false_eq_true, ↓reduceIte] at hlf' ⊢
        · cases hn3264 : n == 32 || n == 64 <;>
            simp only [hn3264, Bool.false_eq_true, ↓reduceIte] at hlf' ⊢ <;>
            cases hlf' <;> rfl
        · cases hzc : armZeroCmpIns? o.swap n rb dst
          · simp only [hzc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              Option.some.injEq] at hlf'
            exact ⟨rfl, hlf'.symm⟩
          · simp only [hzc, Option.isSome_some, ↓reduceIte] at hlf'; cases hlf'
  | gpr r1 => cases r1 with
    | SP => simp at hlf'
    | reg ra => cases pb with
      | vec v => exact v.elim
      | imm cb =>
        dsimp only at hlf'
        cases hcond : (cb == 0#n && (armZeroCmpIns? o n ra dst).isSome) <;>
          simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hlf'
        · cases hlf'; simp [hcond]
        · cases hlf'
      | gpr r2 => cases r2 with | SP => simp at hlf' | reg rb => cases hlf'; rfl

private theorem cmpScr_sgn816 {o : CmpOp} {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool} {lf : Bool}
    (hn' : n = 8 ∨ n = 16) (hfl : armCmpFlagsOut o n pa pb dst = some lf) :
    armIsSignedCmp o = true := by
  rcases (cmpScr_flagsExtract hn hfl).1 with (rfl | rfl) | hs
  · rcases hn' with h | h <;> cases h
  · rcases hn' with h | h <;> cases h
  · exact hs

private abbrev cmpScrFinish (dst : PDst Reg Empty ArmCond .bool) (cmpCode : List Instr)
    (cond : ArmCond) (scrOut : List (Reg × BitVec 64)) :
    Option (List Instr × FlagMask × List (Reg × BitVec 64)) :=
  match dst with
  | .flag cf => if cf == cond then some (cmpCode, maskNZCV, scrOut) else none
  | .gpr (.reg d) => some (cmpCode ++ [armCset64I d cond], maskNZCV, scrOut)
  | .gpr .SP | .vec _ => none

private theorem cmpScr_finish [Host] {o : CmpOp} {n : Nat}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool}
    {va vb : BitVec n} {c : List Instr} {clob : FlagMask}
    {scrMid scrOut : List (Reg × BitVec 64)} {s s' : MachineData}
    {cmpCode : List Instr} {cond : ArmCond}
    (hcmp : _root_.Program.wp (emitClean cmpCode)
      (fun sx => cond.interp sx.status = o.evalBits va vb ∧
        (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
          FlagCmpOk armMach armGpr sx (if lf then va else vb) (if lf then vb else va) false) ∧
        sx.dmem = s.dmem ∧ armMach.Frame armCondReads s sx armScratch [] maskNZCV ∧
        ScrOk armMach armScratch scrMid sx) (fun _ _ => False) s')
    (hfin : cmpScrFinish dst cmpCode cond scrMid = some (c, clob, scrOut))
    (hd : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch) :
    _root_.Program.wp (emitClean c)
      (fun sy => armMach.PDstHolds sy .bool dst (o.evalBits va vb) ∧
        (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr sy rd) .bool (o.evalBits va vb)) ∧
        (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
          FlagCmpOk armMach armGpr sy (if lf then va else vb) (if lf then vb else va) false) ∧
        armMach.mem sy = armMach.mem s ∧
        armMach.Frame armCondReads s sy (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch)
          [] clob ∧
        ScrOk armMach armScratch scrOut sy) (fun _ _ => False) s' := by
  cases dst with
  | vec vr => exact vr.elim
  | flag cf =>
    dsimp only [cmpScrFinish] at hfin; split at hfin
    · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      rcases Option.some.inj hfin with ⟨rfl, rfl, rfl⟩
      exact armWp_mono hcmp fun _ ⟨hcc, hfc, hdm, hfr, hsc⟩ =>
        ⟨hcc, (fun _ h => by cases h), hfc, hdm, hfr, hsc⟩
    · cases hfin
  | gpr r => cases r with | SP => cases hfin | reg d =>
    rcases Option.some.inj hfin with ⟨rfl, rfl, rfl⟩
    rw [emitClean_append, emitClean_cons, emitClean_nil]
    have hdScr : XRegOrSp.reg d ∉ armScratch := hd (.reg d) (by simp [tupDstGprs])
    refine armWp_append hcmp ?_; rintro sx ⟨hcc, hfc, hdm, hfr, hsc⟩
    refine armWp_mono (armCset64_wp d cond sx) ?_; rintro sy rfl
    refine ⟨?_, ?_, hfc, hdm, armFrame_nzcv fun r hr => ?_, scrOk_wr_nonScr hsc hdScr⟩
    · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hcc]; cases o.evalBits va vb <;> rfl
    · intro rd hrd; cases hrd; refine abiGprHolds_bool_01' ?_
      simp [get_wr_same, hcc]
    · have hne : r ≠ .reg d ∧ r ∉ armScratch :=
        ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne sx d _ r hne.1]; exact hfr.1 r hne.2

private theorem cmpScr_imm816 [Host] (o : CmpOp) {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    (hn' : n = 8 ∨ n = 16) (isSwap : Bool) (rx : XReg)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dst : PDst Reg Empty ArmCond .bool)
    {scr : List (Reg × BitVec 64)} {va vb vr vimm : BitVec n} (o' : CmpOp)
    {c : List Instr} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)} {s : MachineData}
    (hrx : (s.regs.getXReg rx).toBitVec.setWidth n = vr)
    (hd : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hsweq : if isSwap then o' = o.swap ∧ va = vimm ∧ vb = vr
      else o' = o ∧ va = vr ∧ vb = vimm)
    (hfin : (let sgn := armIsSignedCmp o
      let c32 := if sgn then vimm.signExtend 32 else vimm.setWidth 32
      let ext := armExt32I sgn n .X16 rx
      let scr1 := armKillScr [.reg .X16] scr
      match armCmpImmIns? .W32 .X16 c32 with
      | some cmp => cmpScrFinish dst (ext :: cmp) (armCmpCond o') scr1
      | none =>
        let (ci17, scr2) := armMovImmScr scr1 .X17 (c32.setWidth 64)
        cmpScrFinish dst
          (ext :: ci17 ++ [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
          (armCmpCond o') scr2) = some (c, clob, scrOut))
    (hsgnOk : ∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
      (isSwap = false → lf = true) ∧ (isSwap = true → lf = false)) :
    _root_.Program.wp (emitClean c)
      (fun sy => armMach.PDstHolds sy .bool dst (o.evalBits va vb) ∧
        (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr sy rd) .bool (o.evalBits va vb)) ∧
        (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
          FlagCmpOk armMach armGpr sy (if lf then va else vb) (if lf then vb else va) false) ∧
        armMach.mem sy = armMach.mem s ∧
        armMach.Frame armCondReads s sy (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch)
          [] clob ∧
        ScrOk armMach armScratch scrOut sy) (fun _ _ => False) s := by
  dsimp only at hfin
  have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
  have hnw32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
  let sgn := armIsSignedCmp o
  let c32 := if sgn then vimm.signExtend 32 else vimm.setWidth 32
  let scr1 := armKillScr [.reg .X16] scr
  have hevalSub : o'.evalBits (if sgn then vr.signExtend 32 else vr.setWidth 32) c32 =
      o.evalBits va vb := by
    have ho'sgn : armIsSignedCmp o' = sgn := by
      cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hsweq
      · rcases hsweq with ⟨rfl, _⟩; rfl
      · rcases hsweq with ⟨rfl, _⟩; cases o <;> rfl
    cases hsgn : sgn
    · simp only [hsgn, Bool.false_eq_true, ↓reduceIte, c32]
      cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hsweq
      · rcases hsweq with ⟨rfl, rfl, rfl⟩
        exact cmp_subword_unsigned hn' o' (hsgn ▸ ho'sgn) va vb
      · rcases hsweq with ⟨rfl, rfl, rfl⟩
        rw [CmpOp.swap_evalBits]; exact cmp_subword_unsigned hn' o hsgn va vb
    · simp only [hsgn, ↓reduceIte, c32]
      cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hsweq
      · rcases hsweq with ⟨rfl, rfl, rfl⟩
        exact cmp_subword_signed hn' o' (hsgn ▸ ho'sgn) va vb
      · rcases hsweq with ⟨rfl, rfl, rfl⟩
        rw [CmpOp.swap_evalBits]; exact cmp_subword_signed hn' o hsgn va vb
  have mkFlagOk : ∀ sx, (sgn = true → FlagCmpOk armMach armGpr sx vr vimm false) →
      ∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
      FlagCmpOk armMach armGpr sx (if lf then va else vb) (if lf then vb else va) false := by
    intro sx hfc lf hfl
    have hsg := cmpScr_sgn816 hn hn' hfl
    have hsw := hsgnOk hfl
    cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hsweq
    · rcases hsweq with ⟨rfl, rfl, rfl⟩; obtain rfl := hsw.1 rfl; exact hfc hsg
    · rcases hsweq with ⟨rfl, rfl, rfl⟩; obtain rfl := hsw.2 rfl; exact hfc hsg
  cases hci : armCmpImmIns? .W32 .X16 c32 with
  | some cmp =>
    rw [hci] at hfin; dsimp only at hfin
    refine cmpScr_finish (cmpCode := armExt32I sgn n .X16 rx :: cmp) (cond := armCmpCond o')
      (scrMid := scr1) ?_ hfin hd
    rw [emitClean_cons]
    refine armWp_cons (armExt32_wp sgn hn0 hnw32 .X16 rx s vr hrx) ?_
    rintro s₁ rfl
    have hscr₁ : ScrOk armMach armScratch scr1
        (wr s .X16 ((if sgn then vr.signExtend 32 else vr.setWidth 32).setWidth 64)) :=
      scrOk_wr_kill hscr
    refine armWp_mono (armCmpImmScr_wp (Or.inl rfl) .W32 rfl .X16 c32 hci _) ?_
    rintro sx ⟨hreg, hst, hdm, hfr⟩
    have h16 :
        let v32 := if sgn then vr.signExtend 32 else vr.setWidth 32
        ((wr s .X16 (v32.setWidth 64)).regs.getXReg .X16).toBitVec.setWidth 32 = v32 := by
      simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    rw [h16] at hst
    have hcc : (armCmpCond o').interp sx.status = o.evalBits va vb := by
      rw [hst, armCmpCond_subs (Or.inl rfl)]; exact hevalSub
    refine ⟨hcc, mkFlagOk sx fun hs => ?_, hdm, armFrame_nzcv fun r hr => ?_,
      scrOk_of_keeps hscr₁ fun r _ => ?_⟩
    · dsimp only [sgn] at hs; dsimp only [sgn, c32] at hst
      have hv' : (if armIsSignedCmp o then vr.signExtend 32 else vr.setWidth 32) =
          vr.signExtend 32 := by simp [hs]
      have hc' : (if armIsSignedCmp o then vimm.signExtend 32 else vimm.setWidth 32) =
          vimm.signExtend 32 := by simp [hs]
      rw [hv', hc'] at hst; exact cmp_sub816 hn' hst
    · exact (hfr.1 r hr).trans ((frame_wr .X16 _ x16_mem_scratch maskNone).1 r hr)
    · cases r <;> simp [get_reg, get_sp, hreg]
  | none =>
    rw [hci] at hfin; dsimp only at hfin
    generalize hm17 : armMovImmScr scr1 .X17 (c32.setWidth 64) = ms17
    rcases ms17 with ⟨ci17, scr2⟩; rw [hm17] at hfin; dsimp only at hfin
    refine cmpScr_finish (cmpCode := armExt32I sgn n .X16 rx :: ci17 ++
        [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
      (cond := armCmpCond o') (scrMid := scr2) ?_ hfin hd
    rw [List.cons_append, emitClean_cons, emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_cons (armExt32_wp sgn hn0 hnw32 .X16 rx s vr hrx) ?_
    rintro s₁ hs₁
    have hfr₁ : armMach.Frame armCondReads s s₁ armScratch [] maskNone :=
      hs₁ ▸ frame_wr .X16 _ x16_mem_scratch maskNone
    have hscr₁ : ScrOk armMach armScratch scr1 s₁ := hs₁ ▸ scrOk_wr_kill hscr
    have hmov := armMovImmScr_wp x17_mem_scratch (c32.setWidth 64) hscr₁
    rw [hm17] at hmov; dsimp only at hmov
    refine armWp_append hmov ?_
    rintro s₂ ⟨h17₂', hx₂, _, hdm₂, hst₂, hfr₂, hscr₂⟩
    have hfr₂' : armMach.Frame armCondReads s s₂ armScratch [] maskNone :=
      armFrame_scratch_trans hfr₁
        (hfr₂.weaken (fun r hr => by simp_all [armScratch]) (fun v => v.elim) rfl)
    have h16₂ : (s₂.regs.getXReg .X16).toBitVec.setWidth 32 =
        if sgn then vr.signExtend 32 else vr.setWidth 32 := by
      rw [hx₂ .X16 (by decide), hs₁]
      simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    have h17₂ : (s₂.regs.getXReg .X17).toBitVec.setWidth 32 = c32 := by
      rw [h17₂', BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    refine armWp_mono (armStatusScratch_after (s := s) (s₂ := s₂)
      (armDirFallsTo_wp fun {_} p next jmp Q hk => by
        simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
          BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, h16₂, h17₂]
        exact hk _ rfl) (by rw [hdm₂, hs₁]) hfr₂') ?_
    rintro s₃ ⟨hr₃, hst₃, hdm₃, hfr₃⟩
    refine ⟨hst₃ ▸ (armCmpCond_subs (Or.inl rfl) o' _ _).trans hevalSub,
      mkFlagOk s₃ fun hs => ?_, hdm₃, hfr₃, scrOk_of_keeps hscr₂ fun r _ => ?_⟩
    · dsimp only [sgn] at hs; dsimp only [sgn, c32] at hst₃
      have hv' : (if armIsSignedCmp o then vr.signExtend 32 else vr.setWidth 32) =
          vr.signExtend 32 := by simp [hs]
      have hc' : (if armIsSignedCmp o then vimm.signExtend 32 else vimm.setWidth 32) =
          vimm.signExtend 32 := by simp [hs]
      rw [hv', hc'] at hst₃; exact cmp_sub816 hn' hst₃
    · cases r with
      | SP => simp [get_sp, hr₃]
      | reg x => simpa [get_reg] using congrArg (fun rg => (rg.getXReg x).toBitVec) hr₃

private theorem cmpScr_fallback [Host] (o : CmpOp) {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    {scr scr₁ scr₂ scrOut : List (Reg × BitVec 64)}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool}
    {va vb : BitVec n} {ca cb c : List Instr} {ra rb : XReg} {clob : FlagMask}
    {s : MachineData}
    (ha : armArgInScr scr .X16 pa = some (ca, ra, scr₁))
    (hb : armArgInScr scr₁ .X17 pb = some (cb, rb, scr₂))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hd : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hlf : ∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf → lf = true)
    (hfb : (if n == 32 || n == 64 then
        cmpScrFinish dst
          (ca ++ cb ++ [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb))])
          (armCmpCond o) scr₂
      else
        cmpScrFinish dst
          (ca ++ cb ++ [armExt32I (armIsSignedCmp o) n .X16 ra,
            armExt32I (armIsSignedCmp o) n .X17 rb,
            armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
          (armCmpCond o) (armKillScr [.reg .X16, .reg .X17] scr₂)) = some (c, clob, scrOut)) :
    _root_.Program.wp (emitClean c)
      (fun sy => armMach.PDstHolds sy .bool dst (o.evalBits va vb) ∧
        (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr sy rd) .bool (o.evalBits va vb)) ∧
        (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
          FlagCmpOk armMach armGpr sy (if lf then va else vb) (if lf then vb else va) false) ∧
        armMach.mem sy = armMach.mem s ∧
        armMach.Frame armCondReads s sy (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch)
          [] clob ∧
        ScrOk armMach armScratch scrOut sy) (fun _ _ => False) s := by
  have hn64 := mem_armWidths_le_64 hn
  split at hfb
  · rename_i hn3264
    have hn' : n = 32 ∨ n = 64 := by
      simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
    refine cmpScr_finish (cmpCode := ca ++ cb ++
        [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb))])
      (cond := armCmpCond o) (scrMid := scr₂) ?_ hfb hd
    rw [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append (armArgs2Scr_wp hn64 hn64 ha hb hpa hpb hga hgb hscr) ?_
    rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂, hscr₂⟩
    rcases hn' with rfl | rfl
    · rw [show armWidthOf 32 = .W32 from rfl]
      refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp (Q := fun s' =>
          s' = { s₂ with status := StatusFlags.subs (va - vb) va vb })
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
            BitVec.shiftLeft_zero]
          rw [hra, hrb]; exact hk _ rfl) hd₂ hfr₂) ?_
      rintro s₃ ⟨hr₃, hst₃, hdm₃, hfr₃⟩
      refine ⟨hst₃ ▸ armCmpCond_subs (Or.inl rfl) o va vb, ?_, hdm₃, hfr₃,
        scrOk_of_keeps hscr₂ fun r _ => ?_⟩
      · intro lf hfl; obtain rfl := hlf hfl; exact cmp_sub3264 (Or.inl rfl) hst₃
      · cases r with | SP => simp [get_sp, hr₃] | reg x =>
          simpa [get_reg] using congrArg (fun rg => (rg.getXReg x).toBitVec) hr₃
    · rw [show armWidthOf 64 = .W64 from rfl]
      refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp (Q := fun s' =>
          s' = { s₂ with status := StatusFlags.subs (va - vb) va vb })
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
            BitVec.shiftLeft_zero, BitVec.setWidth_eq] at hra hrb ⊢
          rw [hra, hrb]; exact hk _ rfl) hd₂ hfr₂) ?_
      rintro s₃ ⟨hr₃, hst₃, hdm₃, hfr₃⟩
      refine ⟨hst₃ ▸ armCmpCond_subs (Or.inr rfl) o va vb, ?_, hdm₃, hfr₃,
        scrOk_of_keeps hscr₂ fun r _ => ?_⟩
      · intro lf hfl; obtain rfl := hlf hfl; exact cmp_sub3264 (Or.inr rfl) hst₃
      · cases r with | SP => simp [get_sp, hr₃] | reg x =>
          simpa [get_reg] using congrArg (fun rg => (rg.getXReg x).toBitVec) hr₃
  · rename_i hn816
    have hn' : n = 8 ∨ n = 16 := by
      rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
    have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
    have hnw32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
    refine cmpScr_finish (cmpCode := ca ++ cb ++ [armExt32I (armIsSignedCmp o) n .X16 ra,
        armExt32I (armIsSignedCmp o) n .X17 rb,
        armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
      (cond := armCmpCond o) (scrMid := armKillScr [.reg .X16, .reg .X17] scr₂) ?_ hfb hd
    simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
    refine armWp_append (armArgs2Scr_wp hn64 hn64 ha hb hpa hpb hga hgb hscr) ?_
    rintro s₂ ⟨hra, hrb, _, hneB, hd₂, _, hfr₂, hscr₂⟩
    simp only [emitClean_cons, emitClean_nil]
    refine armScratch_cons x16_mem_scratch hd₂ hfr₂
      (armExt32_wp (armIsSignedCmp o) hn0 hnw32 .X16 ra s₂ va hra)
      fun s₂' hs₂' hd₂' hfr₂' => ?_
    have hrb' : (s₂'.regs.getXReg rb).toBitVec.setWidth n = vb := by
      rw [hs₂', Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm]; exact hrb
    refine armScratch_cons x17_mem_scratch hd₂' hfr₂'
      (armExt32_wp (armIsSignedCmp o) hn0 hnw32 .X17 rb s₂' vb hrb')
      fun s₃ hs₃ hd₃ hfr₃ => ?_
    have hscr₃ : ScrOk armMach armScratch (armKillScr [.reg .X16, .reg .X17] scr₂) s₃ := by
      refine scrOk_kill_of_keeps hscr₂ fun r _ hr => ?_
      have h16 : r ≠ .reg .X16 := fun e => hr (e ▸ by simp)
      have h17 : r ≠ .reg .X17 := fun e => hr (e ▸ by simp)
      change get s₃ r = get s₂ r
      rw [hs₃, get_wr_of_ne _ .X17 _ r h17, hs₂', get_wr_of_ne _ .X16 _ r h16]
    have h16₃ : (s₃.regs.getXReg .X16).toBitVec.setWidth 32 =
        if armIsSignedCmp o then va.signExtend 32 else va.setWidth 32 := by
      rw [hs₃, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide), hs₂']
      simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    have h17₃ : (s₃.regs.getXReg .X17).toBitVec.setWidth 32 =
        if armIsSignedCmp o then vb.signExtend 32 else vb.setWidth 32 := by
      rw [hs₃]; simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
        BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, h16₃, h17₃]; exact hk _ rfl) hd₃
        hfr₃) ?_
    rintro s₄ ⟨hr₄, hst₄, hdm₄, hfr₄⟩
    refine ⟨?_, ?_, hdm₄, hfr₄, scrOk_of_keeps hscr₃ fun r _ => ?_⟩
    · rw [hst₄, armCmpCond_subs (Or.inl rfl)]
      cases hsgn : armIsSignedCmp o
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact cmp_subword_unsigned hn' o hsgn va vb
      · simp only [↓reduceIte]; exact cmp_subword_signed hn' o hsgn va vb
    · intro lf hfl; have hsgn := cmpScr_sgn816 hn hn' hfl; obtain rfl := hlf hfl
      have h16 : (if armIsSignedCmp o then va.signExtend 32 else va.setWidth 32) =
          va.signExtend 32 := by simp [hsgn]
      have h17 : (if armIsSignedCmp o then vb.signExtend 32 else vb.setWidth 32) =
          vb.signExtend 32 := by simp [hsgn]
      rw [h16, h17] at hst₄; exact cmp_sub816 hn' hst₄
    · cases r with | SP => simp [get_sp, hr₄] | reg x =>
        simpa [get_reg] using congrArg (fun rg => (rg.getXReg x).toBitVec) hr₄

theorem armCmpOpScr_wp [Host] {scr : List (Reg × BitVec 64)} (o : CmpOp) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dst : PDst Reg Empty ArmCond .bool)
    {va vb : BitVec n} {c : List Instr} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    {s : MachineData}
    (hc : armCmpOpScrIns scr o n pa pb dst = some (c, clob, scrOut))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hd : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst (o.evalBits va vb) ∧
      (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr s' rd) .bool (o.evalBits va vb)) ∧
      (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
        FlagCmpOk armMach armGpr s' (if lf then va else vb) (if lf then vb else va) false) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch)
        [] clob ∧
      ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
  dsimp only [armCmpOpScrIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    cases pa with
    | vec vr => exact vr.elim
    | gpr r => cases r with
      | SP => cases pb with
        | vec vr => exact vr.elim
        | imm _ | gpr _ => dsimp only at hc; simp [armArgInScr] at hc
      | reg ra => cases pb with
        | vec vr => exact vr.elim
        | gpr r2 => cases r2 with
          | SP => dsimp only at hc; simp [armArgInScr] at hc
          | reg rb =>
            dsimp only at hc; simp only [bind, Option.bind_eq_some_iff] at hc
            rcases hc with ⟨⟨ca', ra', scr₁⟩, ha, ⟨cb', rb', scr₂⟩, hb, hfin⟩
            exact cmpScr_fallback o hn ha hb hga hgb hd hscr hpa hpb
              (fun hfl => (cmpScr_flagsExtract hn hfl).2) hfin
        | imm cb =>
          dsimp only at hc
          have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
          have hcb : cb = vb := hpb
          have hlfT : ∀ {lf}, armCmpFlagsOut o n (.gpr (.reg ra)) (.imm cb) dst = some lf →
              lf = true := fun hfl => (cmpScr_flagsExtract hn hfl).2.2
          by_cases hcb0 : cb == 0#n
          · simp only [hcb0, ↓reduceIte] at hc
            have hvb0 : vb = 0#n := hcb.symm.trans (beq_iff_eq.mp hcb0)
            cases hzc : armZeroCmpIns? o n ra dst with
            | some rz =>
              rw [hzc] at hc; rcases Option.some.inj hc with ⟨rfl, rfl, rfl⟩
              refine armWp_mono (armZeroCmpScr_wp hn o ra dst hzc hra hd hscr) ?_
              rintro sy ⟨h1, h1a, h2, h3, h4⟩
              refine ⟨hvb0 ▸ h1, fun rd hrd => hvb0 ▸ h1a rd hrd, fun hfl => ?_, h2, h3, h4⟩
              have hbad := (cmpScr_flagsExtract hn hfl).2.1
              simp [hcb0, hzc] at hbad
            | none =>
              rw [hzc] at hc
              by_cases hn3264 : (n == 32 || n == 64) = true
              · have hn' : n = 32 ∨ n = 64 := by
                  simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
                simp only [hn3264, ↓reduceIte] at hc
                rcases option_none_or_some (armCmpImmIns? (armWidthOf n) ra cb) with
                  hnone | ⟨cmp, hcmp⟩
                · rw [hnone] at hc; cases hc
                · rw [hcmp] at hc
                  have hw : (armWidthOf n).bits = n := by rcases hn' with rfl | rfl <;> rfl
                  refine cmpScr_finish
                    (armWp_mono (armCmpImmScr_wp hn' (armWidthOf n) hw ra cb hcmp s) ?_) hc hd
                  rintro s₁ ⟨hr₁, hst, hdm, hfr⟩; rw [hra, hcb] at hst
                  refine ⟨hst ▸ armCmpCond_subs hn' o va vb, ?_, hdm, hfr,
                    scrOk_of_keeps hscr fun r _ => ?_⟩
                  · intro lf hfl; obtain rfl := hlfT hfl; exact cmp_sub3264 hn' hst
                  · cases r <;> simp [get_reg, get_sp, hr₁]
              · have hn' : n = 8 ∨ n = 16 := by
                  rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                    first | exact Or.inl rfl | exact Or.inr rfl | simp at hn3264
                simp only [hn3264, Bool.false_eq_true, ↓reduceIte] at hc
                rcases option_none_or_some (armCmpImmIns? .W32 .X16 0#32) with
                  hnone | ⟨cmp, hcmp⟩
                · rw [hnone] at hc; cases hc
                · rw [hcmp] at hc
                  have hcb0' : cb = 0#n := beq_iff_eq.mp hcb0
                  have hc32 :
                      (if armIsSignedCmp o then cb.signExtend 32 else cb.setWidth 32) = 0#32 := by
                    rw [hcb0']; rcases hn' with rfl | rfl <;> cases armIsSignedCmp o <;> decide
                  exact cmpScr_imm816 o hn hn' false ra _ _ dst o hra hd hscr
                    ⟨rfl, rfl, hcb.symm⟩
                    (by cases dst with
                      | vec vr => exact vr.elim
                      | flag cf => simpa [cmpScrFinish, hc32, hcmp] using hc
                      | gpr r => cases r with
                        | SP => cases hc
                        | reg d => simpa [cmpScrFinish, hc32, hcmp, List.append_assoc] using hc)
                    (fun hfl => ⟨fun _ => hlfT hfl, fun h => (by cases h)⟩)
          · simp only [hcb0, Bool.false_eq_true, ↓reduceIte] at hc; split at hc
            · rename_i hn3264
              have hn' : n = 32 ∨ n = 64 := by
                simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
              rcases option_none_or_some (armCmpImmIns? (armWidthOf n) ra cb) with
                hnone | ⟨cmp, hcmp⟩
              · simp only [hnone, bind, Option.bind_eq_some_iff] at hc
                rcases hc with ⟨⟨cb', rb', scr₂⟩, hb, hfin⟩
                refine cmpScr_fallback o hn (ca := []) (ra := ra) rfl hb hga hgb hd hscr
                  hpa hpb hlfT ?_
                simp only [hn3264, ↓reduceIte]
                cases dst with
                | vec vr => exact vr.elim
                | flag cf => simpa [cmpScrFinish] using hfin
                | gpr r => cases r with
                  | SP => simp at hfin
                  | reg d => simpa [cmpScrFinish, List.append_assoc] using hfin
              · simp only [hcmp] at hc
                have hw : (armWidthOf n).bits = n := by rcases hn' with rfl | rfl <;> rfl
                refine cmpScr_finish
                  (armWp_mono (armCmpImmScr_wp hn' (armWidthOf n) hw ra cb hcmp s) ?_) hc hd
                rintro s₁ ⟨hr₁, hst, hdm, hfr⟩; rw [hra, hcb] at hst
                refine ⟨hst ▸ armCmpCond_subs hn' o va vb, ?_, hdm, hfr,
                  scrOk_of_keeps hscr fun r _ => ?_⟩
                · intro lf hfl; obtain rfl := hlfT hfl; exact cmp_sub3264 hn' hst
                · cases r <;> simp [get_reg, get_sp, hr₁]
            · rename_i hn816
              have hn' : n = 8 ∨ n = 16 := by
                rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
              exact cmpScr_imm816 o hn hn' false ra _ _ dst o hra hd hscr
                ⟨rfl, rfl, hcb.symm⟩
                (by cases hci' : armCmpImmIns? .W32 .X16
                      (if armIsSignedCmp o then vb.signExtend 32 else vb.setWidth 32) <;>
                    cases dst with
                    | vec vr => exact vr.elim
                    | flag cf => simpa [hcb, hci', cmpScrFinish] using hc
                    | gpr r => cases r with
                      | SP => simp [hcb, hci'] at hc
                      | reg d => simpa [hcb, hci', cmpScrFinish, List.append_assoc] using hc)
                (fun hfl => ⟨fun _ => hlfT hfl, fun h => (by cases h)⟩)
    | imm ca => cases pb with
      | vec vr => exact vr.elim
      | imm _ =>
        dsimp only at hc; simp only [bind, Option.bind_eq_some_iff] at hc
        rcases hc with ⟨⟨ca', ra', scr₁⟩, ha, ⟨cb', rb', scr₂⟩, hb, hfin⟩
        exact cmpScr_fallback o hn ha hb hga hgb hd hscr hpa hpb
          (fun hfl => False.elim (cmpScr_flagsExtract hn hfl).2) hfin
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgInScr] at hc
        | reg rb =>
          dsimp only at hc
          have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
          have hca : ca = va := hpa
          by_cases hca0 : ca == 0#n
          · simp only [hca0, ↓reduceIte] at hc
            have hva0 : va = 0#n := hca.symm.trans (beq_iff_eq.mp hca0)
            have hlfF : ∀ {lf}, armCmpFlagsOut o n (.imm ca) (.gpr (.reg rb)) dst = some lf →
                lf = false := fun hfl => by
              have h := (cmpScr_flagsExtract hn hfl).2; simp only [hca0, ↓reduceIte] at h; exact h.2
            cases hzc : armZeroCmpIns? o.swap n rb dst with
            | some rz =>
              rw [hzc] at hc; rcases Option.some.inj hc with ⟨rfl, rfl, rfl⟩
              refine armWp_mono (armZeroCmpScr_wp hn o.swap rb dst hzc hrb hd hscr) ?_
              rintro sy ⟨h1, h1a, h2, h3, h4⟩
              refine ⟨by rw [CmpOp.swap_evalBits] at h1; exact hva0 ▸ h1, fun rd hrd => by
                rw [CmpOp.swap_evalBits] at h1a; exact hva0 ▸ h1a rd hrd, fun hfl => ?_,
                h2, h3, h4⟩
              have h := (cmpScr_flagsExtract hn hfl).2; simp [hca0, hzc] at h
            | none =>
              rw [hzc] at hc
              by_cases hn3264 : (n == 32 || n == 64) = true
              · have hn' : n = 32 ∨ n = 64 := by
                  simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
                simp only [hn3264, ↓reduceIte] at hc
                rcases option_none_or_some (armCmpImmIns? (armWidthOf n) rb ca) with
                  hnone | ⟨cmp, hcmp⟩
                · rw [hnone] at hc; cases hc
                · rw [hcmp] at hc
                  have hw : (armWidthOf n).bits = n := by rcases hn' with rfl | rfl <;> rfl
                  refine cmpScr_finish
                    (armWp_mono (armCmpImmScr_wp hn' (armWidthOf n) hw rb ca hcmp s) ?_) hc hd
                  rintro s₁ ⟨hr₁, hst, hdm, hfr⟩; rw [hrb, hca] at hst
                  refine ⟨?_, ?_, hdm, hfr, scrOk_of_keeps hscr fun r _ => ?_⟩
                  · rw [hst, armCmpCond_subs hn' o.swap vb va, CmpOp.swap_evalBits]
                  · intro lf hfl; obtain rfl := hlfF hfl; exact cmp_sub3264 hn' hst
                  · cases r <;> simp [get_reg, get_sp, hr₁]
              · have hn' : n = 8 ∨ n = 16 := by
                  rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                    first | exact Or.inl rfl | exact Or.inr rfl | simp at hn3264
                simp only [hn3264, Bool.false_eq_true, ↓reduceIte] at hc
                rcases option_none_or_some (armCmpImmIns? .W32 .X16 0#32) with
                  hnone | ⟨cmp, hcmp⟩
                · rw [hnone] at hc; cases hc
                · rw [hcmp] at hc
                  have hca0' : ca = 0#n := beq_iff_eq.mp hca0
                  have hc32 :
                      (if armIsSignedCmp o then ca.signExtend 32 else ca.setWidth 32) = 0#32 := by
                    rw [hca0']; rcases hn' with rfl | rfl <;> cases armIsSignedCmp o <;> decide
                  exact cmpScr_imm816 o hn hn' true rb _ _ dst o.swap hrb hd hscr
                    ⟨rfl, hca.symm, rfl⟩
                    (by cases dst with
                      | vec vr => exact vr.elim
                      | flag cf => simpa [cmpScrFinish, hc32, hcmp] using hc
                      | gpr r => cases r with
                        | SP => cases hc
                        | reg d => simpa [cmpScrFinish, hc32, hcmp, List.append_assoc] using hc)
                    (fun hfl => ⟨fun h => (by cases h), fun _ => hlfF hfl⟩)
          · simp only [hca0, Bool.false_eq_true, ↓reduceIte] at hc; split at hc
            · rename_i hn3264
              have hn' : n = 32 ∨ n = 64 := by
                simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
              rcases option_none_or_some (armCmpImmIns? (armWidthOf n) rb ca) with
                hnone | ⟨cmp, hcmp⟩
              · simp only [hnone, bind, Option.bind_eq_some_iff] at hc
                rcases hc with ⟨⟨ca', ra', scr₁⟩, ha, hfin⟩
                have hlfT : ∀ {lf}, armCmpFlagsOut o n (.imm ca) (.gpr (.reg rb)) dst = some lf →
                    lf = true := fun hfl => by
                  have h := (cmpScr_flagsExtract hn hfl).2
                  simp [hca0, hn3264, hnone] at h; exact h
                refine cmpScr_fallback o hn (cb := []) (rb := rb) ha rfl hga hgb hd hscr
                  hpa hpb hlfT ?_
                simp only [hn3264, ↓reduceIte, List.append_nil]
                cases dst with
                | vec vr => exact vr.elim
                | flag cf => simpa [cmpScrFinish] using hfin
                | gpr r => cases r with
                  | SP => simp at hfin
                  | reg d => simpa [cmpScrFinish, List.append_assoc] using hfin
              · simp only [hcmp] at hc
                have hw : (armWidthOf n).bits = n := by rcases hn' with rfl | rfl <;> rfl
                have hlfF : ∀ {lf}, armCmpFlagsOut o n (.imm ca) (.gpr (.reg rb)) dst = some lf →
                    lf = false := fun hfl => by
                  have h := (cmpScr_flagsExtract hn hfl).2
                  simp [hca0, hn3264, hcmp] at h; exact h
                refine cmpScr_finish
                  (armWp_mono (armCmpImmScr_wp hn' (armWidthOf n) hw rb ca hcmp s) ?_) hc hd
                rintro s₁ ⟨hr₁, hst, hdm, hfr⟩; rw [hrb, hca] at hst
                refine ⟨?_, ?_, hdm, hfr, scrOk_of_keeps hscr fun r _ => ?_⟩
                · rw [hst, armCmpCond_subs hn' o.swap vb va, CmpOp.swap_evalBits]
                · intro lf hfl; obtain rfl := hlfF hfl; exact cmp_sub3264 hn' hst
                · cases r <;> simp [get_reg, get_sp, hr₁]
            · rename_i hn816
              have hn' : n = 8 ∨ n = 16 := by
                rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
              have hlfF : ∀ {lf}, armCmpFlagsOut o n (.imm ca) (.gpr (.reg rb)) dst = some lf →
                  lf = false := fun hfl => by
                have h := (cmpScr_flagsExtract hn hfl).2; simp [hca0, hn816] at h; exact h
              exact cmpScr_imm816 o hn hn' true rb _ _ dst o.swap hrb hd hscr
                ⟨rfl, hca.symm, rfl⟩
                (by cases hci' : armCmpImmIns? .W32 .X16
                      (if armIsSignedCmp o then va.signExtend 32 else va.setWidth 32) <;>
                    cases dst with
                    | vec vr => exact vr.elim
                    | flag cf => simpa [hca, hci', cmpScrFinish] using hc
                    | gpr r => cases r with
                      | SP => simp [hca, hci'] at hc
                      | reg d => simpa [hca, hci', cmpScrFinish, List.append_assoc] using hc)
                (fun hfl => ⟨fun h => (by cases h), fun _ => hlfF hfl⟩)

private theorem map_cmpFinish (dst : PDst Reg Empty ArmCond .bool) (c1 : List Instr)
    (d2 : XReg → List Instr) (cond : ArmCond) (scr : List (Reg × BitVec 64))
    (hd : ∀ d, d2 d = c1 ++ [armCset64I d cond]) :
    Option.map (fun x => (x.fst, x.2.fst)) (cmpScrFinish dst c1 cond scr) =
      match dst with
      | .flag cf => if cf == cond then some (c1, maskNZCV) else none
      | .gpr (.reg d) => some (d2 d, maskNZCV)
      | .gpr .SP | .vec _ => none := by
  cases dst with
  | vec v => exact v.elim
  | flag cf => dsimp only [cmpScrFinish]; split <;> rfl
  | gpr r => cases r with | SP => rfl | reg d => simp [cmpScrFinish, hd d]

private theorem argInScr_nil_imm (rx : XReg) {n : Nat} (c : BitVec n) :
    armArgInScr [] rx (.imm c) =
      some (armMovImmI rx (c.setWidth 64), rx, armSetScr [] rx (c.setWidth 64)) := by
  simp [armArgInScr, armMovImmScr, armHasScr]

private theorem argInScr_set16_imm {n : Nat} (a : BitVec 64) (c : BitVec n) :
    armArgInScr (armSetScr [] .X16 a) .X17 (.imm c) =
      some (armMovImmI .X17 (c.setWidth 64), .X17,
        armSetScr (armSetScr [] .X16 a) .X17 (c.setWidth 64)) := by
  have hne : armHasScr (armSetScr [] .X16 a) .X17 (c.setWidth 64) = false := by
    dsimp only [armHasScr, armSetScr, armKillScr]
    simp only [List.filter_nil, List.any_cons, List.any_nil, Bool.or_false]
    rw [show (XRegOrSp.reg .X16 == XRegOrSp.reg .X17) = false from rfl]; rfl
  dsimp only [armArgInScr, armMovImmScr]; rw [hne]; rfl

theorem armCmpOpScrIns_nil_fst (o : CmpOp) (n : Nat)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dst : PDst Reg Empty ArmCond .bool) :
    (armCmpOpScrIns [] o n pa pb dst).map (fun (c, cl, _) => (c, cl)) =
      armCmpOpIns o n pa pb dst := by
  have hkillNil : ∀ l, armKillScr l [] = [] := fun _ => rfl
  have hfin : ∀ (c1 : List Instr) (cond : ArmCond) (scr : List (Reg × BitVec 64)),
      Option.map (fun x => (x.fst, x.2.fst)) (cmpScrFinish dst c1 cond scr) =
      match dst with
      | .flag cf => if cf == cond then some (c1, maskNZCV) else none
      | .gpr (.reg d) => some (c1 ++ [armCset64I d cond], maskNZCV)
      | .gpr .SP | .vec _ => none :=
    fun c1 cond scr => map_cmpFinish dst c1 (fun d => c1 ++ [armCset64I d cond]) cond scr
      fun _ => rfl
  dsimp only [armCmpOpScrIns, armCmpOpIns]
  split; · rfl
  · cases pa with
    | vec vr => exact vr.elim
    | imm ca => cases pb with
      | vec vr => exact vr.elim
      | imm cb =>
        dsimp only
        have hbind : ∀ {α β} (x : α) (f : α → Option β),
            (do let y ← some x; f y) = f x := fun _ _ => rfl
        rw [argInScr_nil_imm, hbind, argInScr_set16_imm, hbind]
        simp only [armArgInIns]
        split <;> exact map_cmpFinish dst _ _ _ _ fun _ => by simp
      | gpr r => cases r with
        | SP => simp [armArgInScr, armArgInIns]
        | reg rb =>
          dsimp only
          by_cases h0 : ca == 0#n
          · simp only [h0, ↓reduceIte]
            cases armZeroCmpIns? o.swap n rb dst <;> dsimp only
            · split
              · cases armCmpImmIns? (armWidthOf n) rb ca with
                | none => rfl
                | some _ => exact hfin _ _ _
              · cases armCmpImmIns? .W32 .X16 0#32 with
                | none => rfl
                | some _ => exact map_cmpFinish dst _ _ _ _ fun _ => rfl
            · rfl
          · simp only [h0, Bool.false_eq_true, ↓reduceIte]; split
            · cases armCmpImmIns? (armWidthOf n) rb ca with
              | some _ => exact hfin _ _ _
              | none =>
                rw [argInScr_nil_imm]
                simp only [armArgInIns]; exact hfin _ _ _
            · cases armCmpImmIns? .W32 .X16 _ with
              | some _ => exact map_cmpFinish dst _ _ _ _ fun _ => rfl
              | none =>
                simp only [hkillNil, armMovImmScr, armHasScr, List.any_nil, Bool.false_eq_true,
                  ↓reduceIte]
                exact map_cmpFinish dst _ _ _ _ fun _ => by simp
    | gpr r => cases r with
      | SP => cases pb with
        | vec vr => exact vr.elim | imm _ | gpr _ => simp [armArgInScr, armArgInIns]
      | reg ra => cases pb with
        | vec vr => exact vr.elim
        | gpr r2 => cases r2 with
          | SP => simp [armArgInScr, armArgInIns]
          | reg rb =>
            simp only [armArgInScr, armArgInIns]
            split <;> exact map_cmpFinish dst _ _ _ _ fun _ => by simp
        | imm cb =>
          dsimp only
          by_cases h0 : cb == 0#n
          · simp only [h0, ↓reduceIte]
            cases armZeroCmpIns? o n ra dst <;> dsimp only
            · split
              · cases armCmpImmIns? (armWidthOf n) ra cb with
                | none => rfl
                | some _ => exact hfin _ _ _
              · cases armCmpImmIns? .W32 .X16 0#32 with
                | none => rfl
                | some _ => exact map_cmpFinish dst _ _ _ _ fun _ => rfl
            · rfl
          · simp only [h0, Bool.false_eq_true, ↓reduceIte]; split
            · cases armCmpImmIns? (armWidthOf n) ra cb with
              | some _ => exact hfin _ _ _
              | none =>
                rw [argInScr_nil_imm]
                simp only [armArgInIns]; exact hfin _ _ _
            · cases armCmpImmIns? .W32 .X16 _ with
              | some _ => exact map_cmpFinish dst _ _ _ _ fun _ => rfl
              | none =>
                simp only [hkillNil, armMovImmScr, armHasScr, List.any_nil, Bool.false_eq_true,
                  ↓reduceIte]
                exact map_cmpFinish dst _ _ _ _ fun _ => by simp

end LeanQbe.T.Arm64
