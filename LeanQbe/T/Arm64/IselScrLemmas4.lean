module

public import LeanQbe.T.Arm64.IselScrLemmas3

/-!
# AArch64 Wave 6.2-A Zero-Ext & `armOpScr` Keep Helpers — Part 4

Verifies:
* `armOp_zext_non32_fallsTo` (`OPT-10a` for `.zext`, `.ofBool`, `.cmp`, and no-GPR `.bool`)
* `armOpScr_keep_fallsTo` (`OPT-7b` scratch-preserving scalar ops in `armOpScr`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. `AbiGprHolds` & `ScrOk`-Preserving Single-Destination Helpers -/

private theorem setWidth64_of_zext' {m n : Nat} (hle : m ≤ n) (va : BitVec m) :
    va.setWidth 64 = (va.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · have him : ¬ (i < m) := fun h => hin (Nat.lt_of_lt_of_le h hle)
    simp [hin, BitVec.getLsbD_of_ge va i (Nat.le_of_not_lt him)]

private theorem armWrDst_scr_of_eq [Host] {c : List Directive} {n : Nat} (hn : n ≤ 64)
    (d : XReg) (hdS : XRegOrSp.reg d ∉ armScratch) {scr : List (Reg × BitVec 64)}
    {s : MachineData} {val64 : BitVec 64} {target : BitVec n}
    (hscr : ScrOk armMach armScratch scr s)
    (hwp : _root_.Program.wp c (fun s' => s' = wr s d val64) (fun _ _ => False) s)
    (hval : val64.setWidth n = target)
    (hvalZ : n = 32 → val64 = target.setWidth 64) :
    _root_.Program.wp c (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) target ∧
      (n = 32 → armMach.getGpr s' (.reg d) = target.setWidth 64) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s :=
  armWp_mono hwp fun s' hs' => by
    subst hs'
    refine ⟨⟨hn, by simpa [get_wr_same] using hval⟩, fun hn32 => by
      simpa [get_wr_same] using hvalZ hn32, rfl, frame_wr d _ List.mem_cons_self maskNone,
      scrOk_wr_nonScr hscr hdS⟩

private theorem armZextOp_scr_wp [Host] {m n : Nat} (pa : PArg Reg Empty ArmCond (.bits m))
    (d : XReg) (hdS : XRegOrSp.reg d ∉ armScratch) {scr : List (Reg × BitVec 64)}
    {va : BitVec m} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armZextOpIns m n pa d = some (c, clob))
    (hp : armMach.PArgHolds s (.bits m) pa va) (hle : m ≤ n)
    (hscr : ScrOk armMach armScratch scr s) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.setWidth n) ∧
      AbiGprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.setWidth n) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s := by
  dsimp only [armZextOpIns] at hc; split at hc
  · simp at hc
  · rename_i hok; replace hok := not_not_eq_true hok
    simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, Nat.ble_eq] at hok
    have hn64 := mem_armWidths_le_64 hok.1.2
    have fin0 : ∀ {val64 : BitVec 64} {p : List Directive},
        _root_.Program.wp p (fun s' => s' = wr s d val64) (fun _ _ => False) s →
        val64 = (va.setWidth n).setWidth 64 →
        _root_.Program.wp p (fun s' =>
          GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.setWidth n) ∧
          AbiGprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.setWidth n) ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
          ScrOk armMach armScratch scr s') (fun _ _ => False) s := fun {val64} _ hwp hv =>
      armWp_mono hwp fun s' hs' => by
        subst hs'
        have habi :
            AbiGprHolds (armMach.getGpr (wr s d val64) (.reg d)) (.bits n) (va.setWidth n) :=
          ⟨hn64, by simpa [get_wr_same] using hv⟩
        exact ⟨habi.toGprHolds, habi, rfl, frame_wr d _ List.mem_cons_self maskNone,
          scrOk_wr_nonScr hscr hdS⟩
    cases pa with
    | vec vr => exact vr.elim
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      exact fin0 (armMovImm_wp d ((ca.setWidth n).setWidth 64) s) rfl
    | gpr r => cases r with | SP => simp at hc | reg rx =>
      have hrx : (s.regs.getXReg rx).toBitVec.setWidth m = va := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
      rcases mem_armWidths hok.1.1 with rfl | rfl | rfl | rfl
      · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        exact fin0 (armUbfmLow64_wp (m := 8) (by decide) (by decide) d rx s)
          (by rw [hrx, ← setWidth64_of_zext' hle va])
      · simp only [show (16 == 8) = false from rfl, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        exact fin0 (armUbfmLow64_wp (m := 16) (by decide) (by decide) d rx s)
          (by rw [hrx, ← setWidth64_of_zext' hle va])
      · simp only [show (32 == 8) = false from rfl, show (32 == 16) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Option.some.injEq,
          Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        exact fin0 (armMovRegDir_wp .W32 d rx s)
          (by simp only [RegWidth.bits, MemWidth.bits]; rw [hrx, ← setWidth64_of_zext' hle va])
      · simp only [show (64 == 8) = false from rfl, show (64 == 16) = false from rfl,
          show (64 == 32) = false from rfl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        have hn64' : n = 64 := by rcases mem_armWidths hok.1.2 with rfl | rfl | rfl | rfl <;> omega
        subst hn64'
        exact fin0 (armMovRegDir_wp .W64 d rx s) (by simpa [BitVec.setWidth_eq] using hrx)

private theorem armOfBoolOp_scr_wp [Host] {n : Nat} (pa : PArg Reg Empty ArmCond .bool)
    (d : XReg) (hdS : XRegOrSp.reg d ∉ armScratch) {scr : List (Reg × BitVec 64)}
    {b : Bool} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armOfBoolOpIns n pa d = some (c, clob))
    (hp : armMach.PArgHolds s .bool pa b)
    (hscr : ScrOk armMach armScratch scr s) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (BitVec.ofNat n b.toNat) ∧
      AbiGprHolds (armMach.getGpr s' (.reg d)) (.bits n) (BitVec.ofNat n b.toNat) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s := by
  dsimp only [armOfBoolOpIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hsw : (BitVec.ofNat n b.toNat).setWidth 64 = BitVec.ofNat 64 b.toNat := by
      cases b <;> rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rfl
    have fin0 : ∀ {val64 : BitVec 64} {p : List Directive},
        _root_.Program.wp p (fun s' => s' = wr s d val64) (fun _ _ => False) s →
        val64 = BitVec.ofNat 64 b.toNat →
        _root_.Program.wp p (fun s' =>
          GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (BitVec.ofNat n b.toNat) ∧
          AbiGprHolds (armMach.getGpr s' (.reg d)) (.bits n) (BitVec.ofNat n b.toNat) ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
          ScrOk armMach armScratch scr s') (fun _ _ => False) s := fun {val64} _ hwp hv =>
      armWp_mono hwp fun s' hs' => by
        subst hs'
        have hwr : armMach.getGpr (wr s d val64) (.reg d) = val64 := get_wr_same s d val64
        have habi : AbiGprHolds (armMach.getGpr (wr s d val64) (.reg d)) (.bits n)
            (BitVec.ofNat n b.toNat) :=
          ⟨hn64, by rw [hwr, hv, ← hsw]⟩
        exact ⟨habi.toGprHolds, habi, rfl, frame_wr d _ List.mem_cons_self maskNone,
          scrOk_wr_nonScr hscr hdS⟩
    cases pa with
    | vec vr => exact vr.elim
    | gpr r => cases r with | SP => simp at hc | reg rx =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
      have hrx : (s.regs.getXReg rx).toBitVec.setWidth 8 = BitVec.ofNat 8 b.toNat := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hp
      refine fin0 (armUbfmLow64_wp (m := 8) (by decide) (by decide) d rx s) ?_
      rw [hrx]; cases b <;> rfl
    | imm cb =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      exact fin0 (armMovImm_wp d (BitVec.ofNat 64 cb.toNat) s) rfl
    | flag cond =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
      have hpc : cond.interp s.status = b := hp
      exact fin0 (armCset64_wp d cond s) (by rw [hpc])

private theorem armSextOp_scr_wp [Host] {m n : Nat} (pa : PArg Reg Empty ArmCond (.bits m))
    (d : XReg) (hdS : XRegOrSp.reg d ∉ armScratch) {scr : List (Reg × BitVec 64)}
    {va : BitVec m} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armSextOpIns m n pa d = some (c, clob))
    (hp : armMach.PArgHolds s (.bits m) pa va) (hle : m ≤ n)
    (hscr : ScrOk armMach armScratch scr s) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.signExtend n) ∧
      (n = 32 → armMach.getGpr s' (.reg d) = (va.signExtend n).setWidth 64) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s := by
  dsimp only [armSextOpIns] at hc; split at hc
  · simp at hc
  · rename_i hok; replace hok := not_not_eq_true hok
    simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, Nat.ble_eq] at hok
    rcases hok with ⟨⟨hm, hn⟩, _⟩
    have hn64 := mem_armWidths_le_64 hn
    have hnw := mem_armWidths_le_armWidth hn
    cases pa with
    | vec vr => exact vr.elim
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      exact armWrDst_scr_of_eq hn64 d hdS hscr
        (armMovImm_wp d ((ca.signExtend n).setWidth 64) s)
        (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
        (fun hn32 => by subst hn32; rfl)
    | gpr r => cases r with | SP => simp at hc | reg rx =>
      have hrx : (s.regs.getXReg rx).toBitVec.setWidth m = va := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
      have hse_trunc :
          (va.signExtend (armWidthOf n).bits).setWidth n = va.signExtend n := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
          show (i : Nat) < (armWidthOf n).bits by omega, decide_true, Bool.true_and]
      rcases mem_armWidths hm with rfl | rfl | rfl | rfl
      · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        exact armWrDst_scr_of_eq hn64 d hdS hscr
          (armSbfmLow_wp (armWidthOf n) (m := 8) (by decide) (by omega) d rx s)
          (by rw [BitVec.setWidth_setWidth_of_le _ hn64, hrx, hse_trunc])
          (fun hn32 => by subst hn32; rw [show (armWidthOf 32).bits = 32 from rfl, hrx])
      · simp only [show (16 == 8) = false from rfl, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        exact armWrDst_scr_of_eq hn64 d hdS hscr
          (armSbfmLow_wp (armWidthOf n) (m := 16) (by decide) (by omega) d rx s)
          (by rw [BitVec.setWidth_setWidth_of_le _ hn64, hrx, hse_trunc])
          (fun hn32 => by subst hn32; rw [show (armWidthOf 32).bits = 32 from rfl, hrx])
      · simp only [show (32 == 8) = false from rfl, show (32 == 16) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Option.some.injEq,
          Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        exact armWrDst_scr_of_eq hn64 d hdS hscr
          (armSbfmLow_wp (armWidthOf n) (m := 32) (by decide) (by omega) d rx s)
          (by rw [BitVec.setWidth_setWidth_of_le _ hn64, hrx, hse_trunc])
          (fun hn32 => by
            subst hn32; rw [show (armWidthOf 32).bits = 32 from rfl, hrx, BitVec.signExtend_eq])
      · simp only [show (64 == 8) = false from rfl, show (64 == 16) = false from rfl,
          show (64 == 32) = false from rfl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        have hn64' : n = 64 := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> omega
        subst hn64'
        exact armWrDst_scr_of_eq hn64 d hdS hscr (armMovRegDir_wp .W64 d rx s)
          (by simpa [BitVec.setWidth_eq] using hrx) (fun h => by cases h)

private theorem armTruncOp_scr_wp [Host] {m n : Nat} (pa : PArg Reg Empty ArmCond (.bits m))
    (d : XReg) (hdS : XRegOrSp.reg d ∉ armScratch) {scr : List (Reg × BitVec 64)}
    {va : BitVec m} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armTruncOpIns m n pa d = some (c, clob))
    (hp : armMach.PArgHolds s (.bits m) pa va) (hle : n ≤ m)
    (hscr : ScrOk armMach armScratch scr s) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) (va.setWidth n) ∧
      (n = 32 → armMach.getGpr s' (.reg d) = (va.setWidth n).setWidth 64) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s := by
  dsimp only [armTruncOpIns] at hc; split at hc
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
      exact armWrDst_scr_of_eq hn64 d hdS hscr (armMovImm_wp d ((ca.setWidth n).setWidth 64) s)
        (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
        (fun hn32 => by subst hn32; rfl)
    | gpr r => cases r with | SP => simp at hc | reg rx =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
      have hrx : (s.regs.getXReg rx).toBitVec.setWidth m = va := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hp.2
      exact armWrDst_scr_of_eq hn64 d hdS hscr (armMovRegDir_wp (armWidthOf n) d rx s)
        (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_setWidth_of_le _ hnw,
          ← BitVec.setWidth_setWidth_of_le (s.regs.getXReg rx).toBitVec hle, hrx])
        (fun hn32 => by
          subst hn32
          rw [show (armWidthOf 32).bits = 32 from rfl,
            ← BitVec.setWidth_setWidth_of_le (s.regs.getXReg rx).toBitVec hle, hrx])

/-! ## 2. `armBoolNoGpr_abi_wp` and `armOp_zext_non32_fallsTo` (`OPT-10a`) -/

private theorem armBoolNoGpr_abi_wp [Host] {sig : List Ty} (code : OpCode sig [.bool])
    (pas : Tup (PArg Reg Empty ArmCond) sig) (d : XReg) {c : List Instr} {clob : FlagMask}
    {vs : Tup Val sig} {P : Tup Val [.bool] → Prop} {s : MachineData}
    (hnog : armHasNoGprArg pas = true) (hc : armBoolOpIns code pas d = some (c, clob))
    (hrel : TRel (armMach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    _root_.Program.wp (emitClean c) (fun s' =>
      (∃ rv : Bool, P (rv, ()) ∧ AbiGprHolds (armMach.getGpr s' (.reg d)) .bool rv) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  have hBoolImm : ∀ (res : Bool), P (res, ()) →
      _root_.Program.wp (emitClean (armMovImmI d (BitVec.ofNat 64 res.toNat))) (fun s' =>
        (∃ rv : Bool, P (rv, ()) ∧ AbiGprHolds (armMach.getGpr s' (.reg d)) .bool rv) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone)
        (fun _ _ => False) s := fun res hP =>
    armWp_mono (armMovImm_wp d (BitVec.ofNat 64 res.toNat) s) fun s' hs' => by
      subst hs'; exact ⟨⟨res, hP, abiGprHolds_bool_01' (get_wr_same s d _)⟩, rfl,
        frame_wr d _ List.mem_cons_self maskNone⟩
  have hBoolFlag : ∀ {res : Bool} (cond : ArmCond), cond.interp s.status = res → P (res, ()) →
      _root_.Program.wp (emitClean [armCset64I d cond]) (fun s' =>
        (∃ rv : Bool, P (rv, ()) ∧ AbiGprHolds (armMach.getGpr s' (.reg d)) .bool rv) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone)
        (fun _ _ => False) s := fun {res} cond hcond hP => by
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armCset64_wp d cond s) fun s' hs' => by
      subst hs'; exact ⟨⟨res, hP, abiGprHolds_bool_01' (by simp [get_wr_same, hcond])⟩, rfl,
        frame_wr d _ List.mem_cons_self maskNone⟩
  have argInAbi : ∀ {tmp : XReg} {pa : PArg Reg Empty ArmCond .bool} {v : Bool}
      {ca : List Instr} {ra : XReg} {sx : MachineData},
      armBoolArgInIns tmp pa = some (ca, ra) → armMach.PArgHolds sx .bool pa v →
      pa.gprs = [] →
      _root_.Program.wp (emitClean ca) (fun s' =>
        (s'.regs.getXReg ra).toBitVec = BitVec.ofNat 64 v.toNat ∧
        s'.dmem = sx.dmem ∧ s'.status = sx.status ∧
        armMach.Frame armCondReads sx s' [.reg tmp] [] maskNone) (fun _ _ => False) sx := by
    intro tmp pa v ca ra sx ha hp hnp
    cases pa with
    | vec vr => exact vr.elim
    | gpr _ => simp [PArg.gprs] at hnp
    | imm b =>
      simp only [armBoolArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
      rcases ha with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp; subst hp
      refine armWp_mono (armMovImm_wp tmp (BitVec.ofNat 64 b.toNat) sx) ?_
      rintro s' rfl
      exact ⟨by simp, rfl, rfl, frame_wr tmp _ List.mem_cons_self maskNone⟩
    | flag c =>
      simp only [armBoolArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
      rcases ha with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hp
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armCset64_wp tmp c sx) ?_
      rintro s' rfl
      exact ⟨by simp [hp], rfl, rfl, frame_wr tmp _ List.mem_cons_self maskNone⟩
  have fallback2 : ∀ (op : Nat) (pa pb : PArg Reg Empty ArmCond .bool) {va vb : Bool}
      {ca cb : List Instr} {ra rb : XReg},
      armBoolArgInIns .X16 pa = some (ca, ra) → armBoolArgInIns .X17 pb = some (cb, rb) →
      pa.gprs = [] → pb.gprs = [] →
      armMach.PArgHolds s .bool pa va → armMach.PArgHolds s .bool pb vb →
      (res : Bool) → P (res, ()) →
      res = (match op with | 0 => va && vb | 1 => va || vb | _ => va != vb) →
      _root_.Program.wp (emitClean (ca ++ cb ++ [match op with
        | 0 => armIselInsI (.AND_s (zr d .W32) (zr ra .W32) (sh rb))
        | 1 => armIselInsI (.ORR_s (zr d .W32) (zr ra .W32) (sh rb))
        | _ => armIselInsI (.EOR_s (zr d .W32) (zr ra .W32) (sh rb))])) (fun s' =>
        (∃ rv : Bool, P (rv, ()) ∧ AbiGprHolds (armMach.getGpr s' (.reg d)) .bool rv) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone)
        (fun _ _ => False) s := by
    intro op pa pb va vb ca cb ra rb ha hb hna hnb hpa hpb res hP hres
    rw [emitClean_append, emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
    refine armWp_append (argInAbi ha hpa hna) ?_
    rintro s₁ ⟨hra₁, hd₁, hst₁, hfr₁⟩
    have hpb₁ : armMach.PArgHolds s₁ .bool pb vb := by
      cases pb with
      | vec v => exact v.elim
      | gpr _ => simp [PArg.gprs] at hnb
      | imm _ => exact hpb
      | flag _ => simpa [Machine.PArgHolds, armMach, Machine.evalCond, hst₁] using hpb
    refine armWp_append (argInAbi hb hpb₁ hnb) ?_
    rintro s₂ ⟨hrb₂, hd₂, hst₂, hfr₂⟩
    have hra₂ : (s₂.regs.getXReg ra).toBitVec = BitVec.ofNat 64 va.toNat := by
      have h16 : ra = .X16 := by
        cases pa with
        | vec v => exact v.elim
        | gpr _ => simp at hna
        | imm _ => simp [armBoolArgInIns] at ha; exact ha.2.symm
        | flag _ => simp [armBoolArgInIns] at ha; exact ha.2.symm
      subst h16
      have hx := hfr₂.1 (.reg .X16) (fun h => by simp at h)
      simpa [get_reg, hra₁] using hx
    have hfrS := armFrame_scratch2 hfr₁ hfr₂
    have h32a : (s₂.regs.getXReg ra).toBitVec.setWidth 32 = BitVec.ofNat 32 va.toNat := by
      rw [hra₂]; cases va <;> rfl
    have h32b : (s₂.regs.getXReg rb).toBitVec.setWidth 32 = BitVec.ofNat 32 vb.toNat := by
      rw [hrb₂]; cases vb <;> rfl
    cases op with
    | zero =>
      rw [show (match (0 : Nat) with
        | 0 => armIselInsI (.AND_s (zr d .W32) (zr ra .W32) (sh rb))
        | 1 => armIselInsI (.ORR_s (zr d .W32) (zr ra .W32) (sh rb))
        | _ => armIselInsI (.EOR_s (zr d .W32) (zr ra .W32) (sh rb))) =
        armIselInsI (.AND_s (zr d .W32) (zr ra .W32) (sh rb)) from rfl]
      refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
        simp only [t_step_simp, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
          Reg64s.getRegOrZr, Reg64s.getRegOrZr64, zr, Int64.toInt_zero, Int.toNat_zero,
          BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits]
        exact hk _ rfl) ?_
      rintro s' rfl
      refine ⟨⟨res, hP, abiGprHolds_bool_01' ?_⟩, hd₂.trans hd₁,
        armFrame_scratch_wr hfrS (frame_wr d _ List.mem_cons_self maskNone)⟩
      dsimp only
      simp only [get_reg, Reg64s.getXReg_setXReg_same, hres]
      change BitVec.zeroExtend 64 ((s₂.regs.getXReg ra).toBitVec.setWidth 32 &&&
        (s₂.regs.getXReg rb).toBitVec.setWidth 32) = _
      rw [h32a, h32b]; cases va <;> cases vb <;> rfl
    | succ op => cases op with
      | zero =>
        rw [show (match (1 : Nat) with
          | 0 => armIselInsI (.AND_s (zr d .W32) (zr ra .W32) (sh rb))
          | 1 => armIselInsI (.ORR_s (zr d .W32) (zr ra .W32) (sh rb))
          | _ => armIselInsI (.EOR_s (zr d .W32) (zr ra .W32) (sh rb))) =
          armIselInsI (.ORR_s (zr d .W32) (zr ra .W32) (sh rb)) from rfl]
        refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
            Reg64s.getRegOrZr, Reg64s.getRegOrZr64, zr, Int64.toInt_zero, Int.toNat_zero,
            BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits]
          exact hk _ rfl) ?_
        rintro s' rfl
        refine ⟨⟨res, hP, abiGprHolds_bool_01' ?_⟩, hd₂.trans hd₁,
          armFrame_scratch_wr hfrS (frame_wr d _ List.mem_cons_self maskNone)⟩
        dsimp only
        simp only [get_reg, Reg64s.getXReg_setXReg_same, hres]
        change BitVec.zeroExtend 64 ((s₂.regs.getXReg ra).toBitVec.setWidth 32 |||
          (s₂.regs.getXReg rb).toBitVec.setWidth 32) = _
        rw [h32a, h32b]; cases va <;> cases vb <;> rfl
      | succ op =>
        rw [show (match op.succ.succ with
          | 0 => armIselInsI (.AND_s (zr d .W32) (zr ra .W32) (sh rb))
          | 1 => armIselInsI (.ORR_s (zr d .W32) (zr ra .W32) (sh rb))
          | _ => armIselInsI (.EOR_s (zr d .W32) (zr ra .W32) (sh rb))) =
          armIselInsI (.EOR_s (zr d .W32) (zr ra .W32) (sh rb)) from rfl]
        refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
            Reg64s.getRegOrZr, Reg64s.getRegOrZr64, zr, Int64.toInt_zero, Int.toNat_zero,
            BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits]
          exact hk _ rfl) ?_
        rintro s' rfl
        refine ⟨⟨res, hP, abiGprHolds_bool_01' ?_⟩, hd₂.trans hd₁,
          armFrame_scratch_wr hfrS (frame_wr d _ List.mem_cons_self maskNone)⟩
        dsimp only
        simp only [get_reg, Reg64s.getXReg_setXReg_same, hres]
        change BitVec.zeroExtend 64 ((s₂.regs.getXReg ra).toBitVec.setWidth 32 ^^^
          (s₂.regs.getXReg rb).toBitVec.setWidth 32) = _
        rw [h32a, h32b]; cases va <;> cases vb <;> rfl
  have hAndOr : ∀ (isOr : Bool) (pa pb : PArg Reg Empty ArmCond .bool) {a b : Bool},
      pa.gprs = [] → pb.gprs = [] →
      armBoolAndOrIns isOr pa pb d = some (c, clob) →
      armMach.PArgHolds s .bool pa a → armMach.PArgHolds s .bool pb b →
      P (if isOr then (a || b, ()) else (a && b, ())) →
      _root_.Program.wp (emitClean c) (fun s' =>
        (∃ rv : Bool, P (rv, ()) ∧ AbiGprHolds (armMach.getGpr s' (.reg d)) .bool rv) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
    intro isOr pa pb a b hna hnb hco hpa hpb hP
    cases pa with
    | vec vr => exact vr.elim | gpr _ => simp at hna
    | flag c1 => cases pb with
      | vec vr => exact vr.elim | gpr _ => simp at hnb
      | imm cb =>
        dsimp only [armBoolAndOrIns] at hco; simp only [Machine.PArgHolds] at hpb; subst hpb
        by_cases heq : cb == isOr
        · simp only [heq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hco
          rcases hco with ⟨rfl, rfl⟩
          exact hBoolImm isOr (by cases isOr <;> cases cb <;>
            first | exact absurd heq (by decide) | simpa using hP)
        · simp only [heq, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hco
          rcases hco with ⟨rfl, rfl⟩
          exact hBoolFlag c1 hpa (by cases isOr <;> cases cb <;>
            first | exact absurd (by decide) heq | simpa using hP)
      | flag c2 =>
        dsimp only [armBoolAndOrIns] at hco; rcases Option.some.inj hco with ⟨rfl, rfl⟩
        by_cases h12 : c1 == c2
        · simp only [h12, ↓reduceIte]; have heq : c1 = c2 := beq_iff_eq.mp h12; subst heq
          have hv : a = b := hpa.symm.trans hpb; subst hv
          exact hBoolFlag c1 hpa (by cases isOr <;> cases a <;> simpa using hP)
        · simp only [h12, Bool.false_eq_true, ↓reduceIte]
          by_cases hneg : c1 == armNegCond c2
          · simp only [hneg, ↓reduceIte]
            have heq : c1 = armNegCond c2 := beq_iff_eq.mp hneg; subst heq
            dsimp only [Machine.PArgHolds, Machine.evalCond, armMach] at hpa hpb
            have hv : a = !b := by rw [← hpa, ← hpb, armNegCond_interp]
            subst hv; exact hBoolImm isOr (by cases isOr <;> cases b <;> simpa using hP)
          · simp only [hneg, Bool.false_eq_true, ↓reduceIte, emitClean_cons]
            refine armWp_cons (armCset64_wp .X16 c1 s) ?_; rintro s₁ rfl
            dsimp only [Machine.PArgHolds, Machine.evalCond, armMach] at hpa hpb
            have h16 : ((wr s .X16 (BitVec.ofNat 64 (c1.interp s.status).toNat)).regs.getXReg
                .X16).toBitVec.setWidth 32 = BitVec.ofNat 32 a.toNat := by
              have hw : (wr s .X16 (BitVec.ofNat 64 (c1.interp s.status).toNat)).regs.getXReg
                  .X16 = UInt64.ofBitVec (BitVec.ofNat 64 (c1.interp s.status).toNat) := by
                simp
              rw [hw]; simp only [hpa]; cases a <;> rfl
            cases isOr <;> simp only [Bool.false_eq_true, ↓reduceIte, emitClean_cons, emitClean_nil]
            · cases hb : b
              · have hc2 : c2.toKraken.interp s.status = false := by rw [← hb]; exact hpb
                refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                  simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hc2]; exact hk _ rfl) ?_
                rintro s' rfl
                refine ⟨⟨a && false, hb ▸ hP, abiGprHolds_bool_01' ?_⟩, rfl,
                  armFrame_scratch_wr (frame_wr .X16 _ x16_mem_scratch maskNone)
                    (frame_wr d _ List.mem_cons_self maskNone)⟩
                simp only [get_reg, Reg64s.getXReg_setXReg_same, hpa]; cases a <;> rfl
              · have hc2 : c2.toKraken.interp s.status = true := by rw [← hb]; exact hpb
                refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                  simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hc2]; exact hk _ rfl) ?_
                rintro s' rfl
                refine ⟨⟨a && true, hb ▸ hP, abiGprHolds_bool_01' ?_⟩, rfl,
                  armFrame_scratch_wr (frame_wr .X16 _ x16_mem_scratch maskNone)
                    (frame_wr d _ List.mem_cons_self maskNone)⟩
                simp only [get_reg, Reg64s.getXReg_setXReg_same, hpa]; cases a <;> rfl
            · cases hb : b
              · have hc2 : (armNegCond c2).toKraken.interp s.status = true := by
                  have hcb : c2.interp s.status = false := by rw [← hb]; exact hpb
                  change (armNegCond c2).interp s.status = true
                  rw [armNegCond_interp, hcb]; rfl
                refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                  simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hc2]; exact hk _ rfl) ?_
                rintro s' rfl
                refine ⟨⟨a || false, hb ▸ hP, abiGprHolds_bool_01' ?_⟩, rfl,
                  armFrame_scratch_wr (frame_wr .X16 _ x16_mem_scratch maskNone)
                    (frame_wr d _ List.mem_cons_self maskNone)⟩
                simp only [get_reg, Reg64s.getXReg_setXReg_same, hpa]; cases a <;> rfl
              · have hc2 : (armNegCond c2).toKraken.interp s.status = false := by
                  have hcb : c2.interp s.status = true := by rw [← hb]; exact hpb
                  change (armNegCond c2).interp s.status = false
                  rw [armNegCond_interp, hcb]; rfl
                refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                  simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hc2]; exact hk _ rfl) ?_
                rintro s' rfl
                refine ⟨⟨a || true, hb ▸ hP, abiGprHolds_bool_01' ?_⟩, rfl,
                  armFrame_scratch_wr (frame_wr .X16 _ x16_mem_scratch maskNone)
                    (frame_wr d _ List.mem_cons_self maskNone)⟩
                simp only [get_reg, Reg64s.getXReg_setXReg_same, hpa]; cases a <;> rfl
    | imm ca => cases pb with
      | vec vr => exact vr.elim | gpr _ => simp at hnb
      | flag c2 =>
        dsimp only [armBoolAndOrIns] at hco; simp only [Machine.PArgHolds] at hpa; subst hpa
        by_cases heq : ca == isOr
        · simp only [heq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hco
          rcases hco with ⟨rfl, rfl⟩
          exact hBoolImm isOr (by cases isOr <;> cases ca <;>
            first | exact absurd heq (by decide) | simpa using hP)
        · simp only [heq, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hco
          rcases hco with ⟨rfl, rfl⟩
          exact hBoolFlag c2 hpb (by cases isOr <;> cases ca <;>
            first | exact absurd (by decide) heq | simpa using hP)
      | imm cb =>
        dsimp only [armBoolAndOrIns] at hco
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hco
        rcases hco with ⟨⟨ca', ra⟩, ha, ⟨cb', rb⟩, hb, rfl, rfl⟩
        cases isOr
        · exact fallback2 0 (.imm ca) (.imm cb) ha hb rfl rfl hpa hpb _ hP rfl
        · exact fallback2 1 (.imm ca) (.imm cb) ha hb rfl rfl hpa hpb _ hP rfl
  cases code with
  | copy _ =>
    rcases pas with ⟨pa, _⟩; rcases vs with ⟨b, _⟩
    have hpa := trel1_inv hrel; dsimp only [OpCode.wp] at hwp; dsimp only [armBoolOpIns] at hc
    cases pa with
    | vec vr => exact vr.elim | gpr _ => simp [armHasNoGprArg] at hnog
    | imm cb =>
      rcases Option.some.inj hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hpa; subst hpa
      exact hBoolImm cb hwp
    | flag cond => rcases Option.some.inj hc with ⟨rfl, rfl⟩; exact hBoolFlag cond hpa hwp
  | not _ =>
    rcases pas with ⟨pa, _⟩; rcases vs with ⟨a, _⟩
    have hpa := trel1_inv hrel; dsimp only [OpCode.wp, lift1] at hwp
    dsimp only [armBoolOpIns] at hc
    cases pa with
    | vec vr => exact vr.elim | gpr _ => simp [armHasNoGprArg] at hnog
    | imm cb =>
      rcases Option.some.inj hc with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hpa; subst hpa
      exact hBoolImm (!cb) hwp
    | flag cond =>
      rcases Option.some.inj hc with ⟨rfl, rfl⟩
      have hpc : cond.interp s.status = a := hpa
      exact hBoolFlag (armNegCond cond) (by rw [armNegCond_interp, hpc]) hwp
  | and _ =>
    rcases pas with ⟨pa, pb, _⟩; rcases vs with ⟨a, b, _⟩
    have ⟨hpa, hpb⟩ := trel2_inv hrel; dsimp only [OpCode.wp, lift2] at hwp
    dsimp only [armBoolOpIns] at hc
    have hna : pa.gprs = [] := by
      cases pa with | vec v => exact v.elim | gpr _ => simp [armHasNoGprArg] at hnog | _ => rfl
    have hnb : pb.gprs = [] := by
      cases pa with
      | vec v => exact v.elim
      | gpr _ => simp [armHasNoGprArg] at hnog
      | _ => cases pb with
        | vec v => exact v.elim | gpr _ => simp [armHasNoGprArg] at hnog | _ => rfl
    exact hAndOr false pa pb hna hnb hc hpa hpb hwp
  | or _ =>
    rcases pas with ⟨pa, pb, _⟩; rcases vs with ⟨a, b, _⟩
    have ⟨hpa, hpb⟩ := trel2_inv hrel; dsimp only [OpCode.wp, lift2] at hwp
    dsimp only [armBoolOpIns] at hc
    have hna : pa.gprs = [] := by
      cases pa with | vec v => exact v.elim | gpr _ => simp [armHasNoGprArg] at hnog | _ => rfl
    have hnb : pb.gprs = [] := by
      cases pa with
      | vec v => exact v.elim
      | gpr _ => simp [armHasNoGprArg] at hnog
      | _ => cases pb with
        | vec v => exact v.elim | gpr _ => simp [armHasNoGprArg] at hnog | _ => rfl
    exact hAndOr true pa pb hna hnb hc hpa hpb hwp
  | xor _ =>
    rcases pas with ⟨pa, pb, _⟩; rcases vs with ⟨a, b, _⟩
    have ⟨hpa, hpb⟩ := trel2_inv hrel; dsimp only [OpCode.wp, lift2] at hwp
    dsimp only [armBoolOpIns] at hc
    have hna : pa.gprs = [] := by
      cases pa with | vec v => exact v.elim | gpr _ => simp [armHasNoGprArg] at hnog | _ => rfl
    have hnb : pb.gprs = [] := by
      cases pa with
      | vec v => exact v.elim
      | gpr _ => simp [armHasNoGprArg] at hnog
      | _ => cases pb with
        | vec v => exact v.elim | gpr _ => simp [armHasNoGprArg] at hnog | _ => rfl
    cases pa with
    | vec vr => exact vr.elim | gpr _ => simp at hna
    | flag c1 => cases pb with
      | vec vr => exact vr.elim | gpr _ => simp at hnb
      | imm cb =>
        dsimp only [armBoolXorIns] at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
        simp only [Machine.PArgHolds] at hpb; subst hpb
        have hpc : c1.interp s.status = a := hpa
        cases cb
        · exact hBoolFlag c1 hpc (by simpa using hwp)
        · exact @hBoolFlag (!a) (armNegCond c1) (by rw [armNegCond_interp, hpc])
            (by simpa using hwp)
      | flag c2 =>
        dsimp only [armBoolXorIns] at hc
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl, rfl⟩
        exact fallback2 2 (.flag c1) (.flag c2) ha hb rfl rfl hpa hpb _ hwp rfl
    | imm ca => cases pb with
      | vec vr => exact vr.elim | gpr _ => simp at hnb
      | flag c2 =>
        dsimp only [armBoolXorIns] at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
        simp only [Machine.PArgHolds] at hpa; subst hpa
        have hpc : c2.interp s.status = b := hpb
        cases ca
        · exact hBoolFlag c2 hpc (by simpa using hwp)
        · exact @hBoolFlag (!b) (armNegCond c2) (by rw [armNegCond_interp, hpc])
            (by simpa using hwp)
      | imm cb =>
        dsimp only [armBoolXorIns] at hc
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨⟨ca', ra⟩, ha, ⟨cb', rb⟩, hb, rfl, rfl⟩
        exact fallback2 2 (.imm ca) (.imm cb) ha hb rfl rfl hpa hpb _ hwp rfl
  | _ => delta armBoolOpIns at hc; cases hc

theorem armOp_zext_non32_fallsTo {h : Host} {k : Nat} {sig : List Ty} {t0 : Ty}
    {code : OpCode sig [t0]} {pas : Tup (PArg Reg Empty ArmCond) sig}
    {rd : Reg} {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    {vs : Tup Val sig} {P : Tup Val [t0] → Prop} {s : MachineData} {post : MachineState → Prop}
    (hne32 : t0 ≠ .bits 32)
    (hz : armZeroExtOp code pas (.gpr rd, ()) = true)
    (hc_in : armOp code pas (.gpr rd, ()) vh = some (c, clob))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ armScratch) (hrd : rd ∉ armScratch)
    (hrel : TRel (armMach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => (∃ rv : Val t0, P (rv, ()) ∧ AbiGprHolds (armMach.getGpr s' rd) t0 rv) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  cases rd with
  | SP =>
    rcases t0 with _ | w | _ | _ <;> cases code with
    | cmp o t m h => cases t <;> (dsimp only [armZeroExtOp] at hz; cases hz)
    | _ => dsimp only [armZeroExtOp] at hz; cases hz
  | reg d =>
    obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
    have hd1 : ∀ r ∈ @tupDstGprs Reg Empty ArmCond [.bool] (.gpr (.reg d), ()),
        r ∉ armScratch := by
      simpa [tupDstGprs] using hrd
    cases code with
    | zext m n =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armFallsTo_of_wp
        (armWp_mono (armZextOp_scr_wp pa d hrd hc (trel1_inv hrel) hwp.1 (scrOk_nil s))
          fun _ ⟨_, ha, hm, hfr, _⟩ => ⟨⟨⟨va.setWidth n, hwp.2, ha⟩, hm⟩, hfr⟩)
    | ofBool n =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨b, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armFallsTo_of_wp
        (armWp_mono (armOfBoolOp_scr_wp pa d hrd hc (trel1_inv hrel) (scrOk_nil s))
          fun _ ⟨_, ha, hm, hfr, _⟩ => ⟨⟨⟨BitVec.ofNat n b.toNat, hwp, ha⟩, hm⟩, hfr⟩)
    | cmp o t m hm =>
      subst hm; cases t <;> try (dsimp only [armZeroExtOp] at hz; cases hz)
      rename_i w
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      have hcScr : ∃ scrOut, armCmpOpScrIns [] o w pa pb (.gpr (.reg d)) =
          some (ci, clob, scrOut) := by
        have hmap := armCmpOpScrIns_nil_fst o w pa pb (.gpr (.reg d))
        rw [hc] at hmap
        cases h0 : armCmpOpScrIns [] o w pa pb (.gpr (.reg d))
        · simp [h0] at hmap
        · rename_i t'; rcases t' with ⟨c', cl', scrOut⟩
          simp only [h0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
          exact ⟨scrOut, by simp [hmap.1, hmap.2]⟩
      obtain ⟨scrOut, hscr⟩ := hcScr
      have ⟨hpa, hpb⟩ := trel2_inv hrel
      have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr =>
        hargs r (by cases pa <;> simp [PArg.gprs, tupArgGprs] at hr ⊢; exact Or.inl hr)
      have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr =>
        hargs r (by cases pa <;> cases pb <;> simp [PArg.gprs, tupArgGprs] at hr ⊢ <;>
          first | exact hr | exact Or.inl hr | exact Or.inr hr)
      exact armFallsTo_of_wp (armWp_mono
        (armCmpOpScr_wp o pa pb (.gpr (.reg d)) hscr hga hgb hd1 (scrOk_nil s) hpa hpb)
        fun _ ⟨_, habi, _, hm, hfr, _⟩ =>
          ⟨⟨⟨o.evalBits va vb, hwp, habi (.reg d) rfl⟩, hm⟩, hfr⟩)
    | copy _ | not _ | and _ | or _ | xor _ =>
      cases t0 with
      | bool =>
        dsimp only [armZeroExtOp] at hz; dsimp only [armOpIns] at hc
        exact armFallsTo_of_wp (armWp_mono (armBoolNoGpr_abi_wp _ pas d hz hc hrel hwp)
          fun _ ⟨hp, hm, hfr⟩ => ⟨⟨hp, hm⟩, hfr⟩)
      | bits w =>
        have hne : (w == 32) = false := beq_false_of_ne fun e => hne32 (e ▸ rfl)
        dsimp only [armZeroExtOp] at hz; simp only [hne] at hz; cases hz
      | float _ | pair _ _ => dsimp only [armZeroExtOp] at hz; cases hz
    | add _ | sub _ | mul _ | neg _ | shl _ | lshr _ | ashr _ | rotl _ | rotr _ | bswap _
    | select _ | bitcast _ _ _ =>
      cases t0 with
      | bits w =>
        have hne : (w == 32) = false := beq_false_of_ne fun e => hne32 (e ▸ rfl)
        dsimp only [armZeroExtOp] at hz; simp only [hne] at hz; cases hz
      | _ => dsimp only [armZeroExtOp] at hz; cases hz
    | _ =>
      first
      | (dsimp only [armOpIns] at hc; cases hc)
      | (dsimp only [armZeroExtOp] at hz
         first
         | cases hz
         | exact absurd (beq_iff_eq.mp hz ▸ rfl) hne32)

/-! ## 3. Scratch-Preserving Fallback `armOpScr_keep_fallsTo` (`OPT-7b`) -/

private theorem armKeepFin1 {h : Host} {k : Nat} {t0 : Ty} {rs sig : List Ty} (hrs : rs = [t0])
    {code : OpCode sig rs} {pas : Tup (PArg Reg Empty ArmCond) sig} (d : XReg)
    (dsts : Tup (PDst Reg Empty ArmCond) rs)
    (hdsts : dsts = hrs ▸ ((.gpr (.reg d), ()) : Tup (PDst Reg Empty ArmCond) [t0]))
    {scr : List (Reg × BitVec 64)} {ci : List Instr} {clob : FlagMask} {rv : Val t0}
    {P : Tup Val rs → Prop} {s : MachineData} {post : MachineState → Prop}
    (hwpP : @Program.wp h (emitClean ci) (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) t0 rv ∧
      (armZeroExtOp code pas dsts = true → AbiGprHolds (armMach.getGpr s' (.reg d)) t0 rv) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s)
    (hP : P (hrs ▸ ((rv, ()) : Tup Val [t0]))) :
    armMach.FallsTo armCondReads h k (emitClean ci)
      (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
          (∀ {t'} {ht : rs = [t']} {rd}, dsts = ht ▸ (.gpr rd, ()) →
            armZeroExtOp code pas dsts = true →
            AbiGprHolds (armMach.getGpr s' rd) t' (ht ▸ rvs).1)) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scr s') post := by
  letI := h; subst hrs; subst hdsts
  refine armFallsTo_of_wp (armWp_mono hwpP fun s' ⟨hg, habi, hm, hfr, hsc⟩ => ?_)
  refine ⟨⟨⟨(rv, ()), hP, .cons hg .nil, ?_⟩, hm, hsc⟩, by simpa [tupDstGprs] using hfr⟩
  intro t' ht rd hrd hz
  have hteq : t0 = t' := List.cons.inj ht |>.1; subst hteq
  have hrd' : XRegOrSp.reg d = rd := by cases hrd; rfl
  subst hrd'; exact habi hz

private theorem armKeepFinBits {h : Host} {k n : Nat} {rs sig : List Ty} (hrs : rs = [.bits n])
    {code : OpCode sig rs} {pas : Tup (PArg Reg Empty ArmCond) sig} (d : XReg)
    (dsts : Tup (PDst Reg Empty ArmCond) rs)
    (hdsts : dsts = hrs ▸ ((.gpr (.reg d), ()) : Tup (PDst Reg Empty ArmCond) [.bits n]))
    {scr : List (Reg × BitVec 64)} {ci : List Instr} {clob : FlagMask} {rv : BitVec n}
    {P : Tup Val rs → Prop} {s : MachineData} {post : MachineState → Prop}
    (hwpB : @Program.wp h (emitClean ci) (fun s' =>
      GprHolds (armMach.getGpr s' (.reg d)) (.bits n) rv ∧
      (n = 32 → armMach.getGpr s' (.reg d) = rv.setWidth 64) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
      ScrOk armMach armScratch scr s') (fun _ _ => False) s)
    (h32 : armZeroExtOp code pas dsts = true → n = 32)
    (hP : P (hrs ▸ ((rv, ()) : Tup Val [.bits n]))) :
    armMach.FallsTo armCondReads h k (emitClean ci)
      (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
          (∀ {t'} {ht : rs = [t']} {rd}, dsts = ht ▸ (.gpr rd, ()) →
            armZeroExtOp code pas dsts = true →
            AbiGprHolds (armMach.getGpr s' rd) t' (ht ▸ rvs).1)) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scr s') post := by
  letI := h; subst hrs; subst hdsts
  exact armKeepFin1 rfl d _ rfl (armWp_mono hwpB fun s' ⟨hg, h32v, hm, hfr, hsc⟩ =>
    ⟨hg, (fun hz => by obtain rfl := h32 hz; exact ⟨by decide, h32v rfl⟩), hm, hfr, hsc⟩) hP

@[expose] def armKeepScr {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg Empty ArmCond) sig) : Bool :=
  match sig, code, pas with
  | _, .copy _, _ | _, .zext _ _, _ | _, .sext _ _, _ | _, .trunc _ _, _
  | _, .bitcast _ _ _, _ | _, .ofBool _, _ | _, .neg _, _ | _, .not _, _ => true
  | _, .shl (.bits n), (.gpr (.reg _), .imm _, ())
  | _, .lshr (.bits n), (.gpr (.reg _), .imm _, ())
  | _, .ashr (.bits n), (.gpr (.reg _), .imm _, ()) => n == 32 || n == 64
  | _, _, _ => false

theorem armOpScr_keep_fallsTo {h : Host} {k : Nat} {scr : List (Reg × BitVec 64)}
    {sig rs : List Ty} {code : OpCode sig rs} {pas : Tup (PArg Reg Empty ArmCond) sig}
    {dsts : Tup (PDst Reg Empty ArmCond) rs} {vh : VariantHint}
    {c : List Directive} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val rs → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hkeep : armKeepScr code pas = true)
    (hc_in : armOp code pas dsts vh = some (c, clob))
    (hdsts : ∀ r ∈ tupDstGprs dsts, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hrel : TRel (armMach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    armMach.FallsTo armCondReads h k c (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs ∧
          (∀ {t0} {ht : rs = [t0]} {rd}, dsts = ht ▸ (.gpr rd, ()) →
            armZeroExtOp code pas dsts = true →
            AbiGprHolds (armMach.getGpr s' rd) t0 (ht ▸ rvs).1)) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scr s') post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  dsimp only [armKeepScr] at hkeep
  cases code
  all_goals try (dsimp only at hkeep; cases hkeep)
  case copy.refl t =>
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    all_goals have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    · rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨b, ⟨⟩⟩
      dsimp only [armOpIns, armBoolOpIns] at hc
      cases pa with
      | vec vr => exact vr.elim
      | gpr r => cases r with | SP => simp at hc | reg rx =>
        rcases Option.some.inj hc with ⟨rfl, rfl⟩
        refine armKeepFin1 rfl d _ rfl (armWp_mono (by
          rw [emitClean_cons, emitClean_nil]; exact armMovRegDir_wp .W32 d rx s) ?_) hwp
        rintro s' rfl
        refine ⟨?_, (fun hz => by cases hz), rfl,
          frame_wr d _ List.mem_cons_self maskNone, scrOk_wr_nonScr hscr hdS⟩
        simpa [Machine.PDstHolds, GprHolds, get_wr_same, RegWidth.bits, MemWidth.bits,
          BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
          BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)] using
          (by simpa [Machine.PArgHolds, GprHolds, get_reg] using trel1_inv hrel :
            (s.regs.getXReg rx).toBitVec.setWidth 8 = BitVec.ofNat 8 b.toNat)
      | imm cb =>
        rcases Option.some.inj hc with ⟨rfl, rfl⟩
        have hcb : cb = b := trel1_inv hrel; subst hcb
        refine armKeepFin1 rfl d _ rfl
          (armWp_mono (armMovImm_wp d (BitVec.ofNat 64 cb.toNat) s) ?_) hwp
        rintro s' rfl
        exact ⟨by simp [GprHolds, get_wr_same],
          fun _ => abiGprHolds_bool_01' (get_wr_same s d _), rfl,
          frame_wr d _ List.mem_cons_self maskNone, scrOk_wr_nonScr hscr hdS⟩
      | flag cond =>
        rcases Option.some.inj hc with ⟨rfl, rfl⟩
        have hpc : cond.interp s.status = b := trel1_inv hrel
        refine armKeepFin1 rfl d _ rfl (armWp_mono (by
          rw [emitClean_cons, emitClean_nil]; exact armCset64_wp d cond s) ?_) hwp
        rintro s' rfl
        exact ⟨by simp [GprHolds, get_wr_same, hpc],
          fun _ => abiGprHolds_bool_01' (by simp [get_wr_same, hpc]), rfl,
          frame_wr d _ List.mem_cons_self maskNone, scrOk_wr_nonScr hscr hdS⟩
    · rename_i n
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc; split at hc
      rotate_left
      · cases hc
      · rename_i hn; simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
        have hn64 := mem_armWidths_le_64 hn; have hnw := mem_armWidths_le_armWidth hn
        have h32 : armZeroExtOp (.copy (.bits n)) (pa, ()) (.gpr (.reg d), ()) = true →
            n = 32 := fun hz => by
          rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> first | rfl | cases hz
        cases pa with
        | vec vr => exact vr.elim
        | imm cv =>
          simp only [armCopyBitsIns, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩; have hcv : cv = va := trel1_inv hrel; subst hcv
          exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
            (armMovImm_wp d (cv.setWidth 64) s)
            (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
            (fun hn32 => by subst hn32; rfl)) h32 hwp
        | gpr r => cases r with | SP => simp [armCopyBitsIns] at hc | reg rx =>
          simp only [armCopyBitsIns, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          have hrx : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using (trel1_inv hrel).2
          exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
            (by rw [emitClean_cons, emitClean_nil]; exact armMovRegDir_wp (armWidthOf n) d rx s)
            (by
              rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_setWidth_of_le _ hnw, hrx])
            (fun hn32 => by subst hn32; rw [show (armWidthOf 32).bits = 32 from rfl, hrx])) h32 hwp
  case bitcast.refl t u htu =>
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try cases u
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rename_i m n; have hmn : m = n := htu; subst hmn
    have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    dsimp only [armOpIns] at hc; split at hc
    rotate_left
    · cases hc
    rename_i hok; simp only [Bool.and_self, List.contains_eq_mem, decide_eq_true_eq] at hok
    have hn64 := mem_armWidths_le_64 hok; have hnw := mem_armWidths_le_armWidth hok
    have hwp' : P (va, ()) := by simpa [OpCode.wp, toBits, ofBits] using hwp
    have h32 : armZeroExtOp (.bitcast (.bits m) (.bits m) htu) (pa, ())
        (.gpr (.reg d), ()) = true → m = 32 := fun hz => by
      rcases mem_armWidths hok with rfl | rfl | rfl | rfl <;> first | rfl | cases hz
    cases pa with
    | vec vr => exact vr.elim
    | imm cv =>
      simp only [armCopyBitsIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; have hcv : cv = va := trel1_inv hrel; subst hcv
      exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
        (armMovImm_wp d (cv.setWidth 64) s)
        (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
        (fun hn32 => by subst hn32; rfl)) h32 hwp'
    | gpr r => cases r with | SP => simp [armCopyBitsIns] at hc | reg rx =>
      simp only [armCopyBitsIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩
      have hrx : (s.regs.getXReg rx).toBitVec.setWidth m = va := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using (trel1_inv hrel).2
      exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
        (by rw [emitClean_cons, emitClean_nil]; exact armMovRegDir_wp (armWidthOf m) d rx s)
        (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_setWidth_of_le _ hnw, hrx])
        (fun hn32 => by subst hn32; rw [show (armWidthOf 32).bits = 32 from rfl, hrx])) h32 hwp'
  case zext.refl m n =>
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    dsimp only [armOpIns] at hc
    exact armKeepFin1 rfl d _ rfl
      (armWp_mono (armZextOp_scr_wp pa d hdS hc (trel1_inv hrel) hwp.1 hscr)
        fun _ ⟨hg, habi, hm, hfr, hsc⟩ => ⟨hg, fun _ => habi, hm, hfr, hsc⟩) hwp.2
  case ofBool.refl n =>
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨b, ⟨⟩⟩
    dsimp only [armOpIns] at hc
    exact armKeepFin1 rfl d _ rfl
      (armWp_mono (armOfBoolOp_scr_wp pa d hdS hc (trel1_inv hrel) hscr)
        fun _ ⟨hg, habi, hm, hfr, hsc⟩ => ⟨hg, fun _ => habi, hm, hfr, hsc⟩) hwp
  case sext.refl m n =>
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    dsimp only [armOpIns] at hc
    have hn : n ∈ [8, 16, 32, 64] := by
      dsimp only [armSextOpIns] at hc; split at hc
      · simp at hc
      · rename_i hok; replace hok := not_not_eq_true hok
        simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hok; exact hok.1.2
    exact armKeepFinBits rfl d _ rfl (armSextOp_scr_wp pa d hdS hc (trel1_inv hrel) hwp.1 hscr)
      (fun hz => by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> first | rfl | cases hz)
      hwp.2
  case trunc.refl m n =>
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    dsimp only [armOpIns] at hc
    have hn : n ∈ [8, 16, 32, 64] := by
      dsimp only [armTruncOpIns] at hc; split at hc
      · simp at hc
      · rename_i hok; replace hok := not_not_eq_true hok
        simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hok; exact hok.1.2
    exact armKeepFinBits rfl d _ rfl (armTruncOp_scr_wp pa d hdS hc (trel1_inv hrel) hwp.1 hscr)
      (fun hz => by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> first | rfl | cases hz)
      hwp.2
  case neg.refl t =>
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rename_i n
    have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    dsimp only [armOpIns] at hc; split at hc
    · simp at hc
    rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn; have hnw := mem_armWidths_le_armWidth hn
    have h32 : armZeroExtOp (.neg (.bits n)) (pa, ()) (.gpr (.reg d), ()) = true →
        n = 32 := fun hz => by
      rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> first | rfl | cases hz
    cases pa with
    | vec vr => exact vr.elim
    | imm cv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; have hcv : cv = va := trel1_inv hrel; subst hcv
      exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
        (armMovImm_wp d ((-cv).setWidth 64) s)
        (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
        (fun hn32 => by subst hn32; rfl)) h32 (by simpa [OpCode.wp, lift1] using hwp)
    | gpr r => cases r with | SP => simp at hc | reg rx =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩
      have hrx : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using (trel1_inv hrel).2
      exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
        (by rw [emitClean_cons, emitClean_nil]; exact armSubNegDir_wp (armWidthOf n) d rx s)
        (by rw [BitVec.setWidth_setWidth_of_le _ hn64, setWidth_neg_of_le hnw,
          BitVec.setWidth_setWidth_of_le _ hnw, hrx])
        (fun hn32 => by subst hn32; rw [show (armWidthOf 32).bits = 32 from rfl, hrx]))
        h32 (by simpa [OpCode.wp, lift1] using hwp)
  case «not».refl t =>
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    all_goals have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    · rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨a, ⟨⟩⟩
      dsimp only [armOpIns, armBoolOpIns] at hc
      cases pa with
      | vec vr => exact vr.elim
      | imm cb =>
        rcases Option.some.inj hc with ⟨rfl, rfl⟩
        have hcb : cb = a := trel1_inv hrel; subst hcb
        refine armKeepFin1 rfl d _ rfl (rv := !cb)
          (armWp_mono (armMovImm_wp d (BitVec.ofNat 64 (!cb).toNat) s) ?_)
          (by simpa [OpCode.wp, lift1] using hwp)
        rintro s' rfl
        exact ⟨by simp [GprHolds, get_wr_same],
          fun _ => abiGprHolds_bool_01' (get_wr_same s d _), rfl,
          frame_wr d _ List.mem_cons_self maskNone, scrOk_wr_nonScr hscr hdS⟩
      | flag cond =>
        rcases Option.some.inj hc with ⟨rfl, rfl⟩
        have hpc : cond.interp s.status = a := trel1_inv hrel
        refine armKeepFin1 rfl d _ rfl (rv := !a) (armWp_mono (by
          rw [emitClean_cons, emitClean_nil]; exact armCset64_wp d (armNegCond cond) s) ?_)
          (by simpa [OpCode.wp, lift1] using hwp)
        rintro s' rfl
        refine ⟨by simp [GprHolds, get_wr_same, armNegCond_interp, hpc],
          fun _ => abiGprHolds_bool_01' (by simp [get_wr_same, armNegCond_interp, hpc]), rfl,
          frame_wr d _ List.mem_cons_self maskNone, scrOk_wr_nonScr hscr hdS⟩
      | gpr r => cases r with | SP => simp at hc | reg rx =>
        rcases Option.some.inj hc with ⟨rfl, rfl⟩
        have hrx : (s.regs.getXReg rx).toBitVec.setWidth 8 = BitVec.ofNat 8 a.toNat := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using trel1_inv hrel
        refine armKeepFin1 rfl d _ rfl (rv := !a) (armWp_mono (by
          rw [emitClean_cons, emitClean_nil]
          exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
            simp only [t_step_simp, ConstExpr.interp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
              RegWidth.bits]
            exact hk _ rfl) ?_) (by simpa [OpCode.wp, lift1] using hwp)
        rintro s' rfl
        refine ⟨?_, (fun hz => by cases hz), rfl,
          frame_wr d _ List.mem_cons_self maskNone, scrOk_wr_nonScr hscr hdS⟩
        simp only [GprHolds, get_reg, Reg64s.getXReg_setXReg_same]
        rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), setWidth8_xor,
          BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), hrx]
        cases a <;> decide
    · rename_i n
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc; split at hc
      · simp at hc
      rename_i hn; replace hn := not_not_eq_true hn
      simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
      have hn64 := mem_armWidths_le_64 hn; have hnw := mem_armWidths_le_armWidth hn
      have h32 : armZeroExtOp (.not (.bits n)) (pa, ()) (.gpr (.reg d), ()) = true →
          n = 32 := fun hz => by
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> first | rfl | cases hz
      cases pa with
      | vec vr => exact vr.elim
      | imm cv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; have hcv : cv = va := trel1_inv hrel; subst hcv
        exact armKeepFinBits rfl d _ rfl (rv := ~~~cv) (armWrDst_scr_of_eq hn64 d hdS hscr
          (armMovImm_wp d ((~~~cv).setWidth 64) s)
          (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
          (fun hn32 => by subst hn32; rfl)) h32 (by simpa [OpCode.wp, lift1] using hwp)
      | gpr r => cases r with | SP => simp at hc | reg rx =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩
        have hrx : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using (trel1_inv hrel).2
        exact armKeepFinBits rfl d _ rfl (rv := ~~~va) (armWrDst_scr_of_eq hn64 d hdS hscr
          (by rw [emitClean_cons, emitClean_nil]; exact armOrnNotDir_wp (armWidthOf n) d rx s)
          (by apply BitVec.eq_of_getLsbD_eq; intro i hi
              rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp [hi, armWidthOf, ← hrx])
          (fun hn32 => by subst hn32; rw [show (armWidthOf 32).bits = 32 from rfl, hrx]))
          h32 (by simpa [OpCode.wp, lift1] using hwp)
  all_goals
    rename_i t
    rcases dsts with ⟨⟨d | _⟩ | vr | _, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    all_goals try simp at hkeep
    rename_i n
    have hdS : XRegOrSp.reg d ∉ armScratch := hdsts (.reg d) (by simp [tupDstGprs])
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    cases pa with
    | vec vr => exact vr.elim
    | imm _ => simp at hkeep
    | gpr r => cases r with | SP => simp at hkeep | reg ra =>
      cases pb with
      | vec vr => exact vr.elim
      | gpr _ => simp at hkeep
      | imm cb =>
        have hn' : n = 32 ∨ n = 64 := by
          simp only [Bool.or_eq_true, beq_iff_eq] at hkeep; exact hkeep
        have hcond : (n == 32 || n == 64) = true := hkeep
        have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl <;> decide
        have ⟨hpa, hpb⟩ := trel2_inv hrel
        have hcb : cb = vb := hpb
        have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
        have hmem : (![8, 16, 32, 64].contains n) = false := by
          rcases hn' with rfl | rfl <;> rfl
        dsimp only [armOpIns, armShiftOpIns] at hc
        simp only [hcond, hmem, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩
        rcases hn' with rfl | rfl
        · first
          | exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
              (by rw [emitClean_cons, emitClean_nil]
                  exact armShiftImmDir_wp .shl .W32 d ra (cb.toNat % 32)
                    (Nat.mod_lt _ (by decide)) s)
              (by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb,
                BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]; rfl)
              (fun _ => by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb]; rfl))
              (fun _ => rfl) hwp
          | exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
              (by rw [emitClean_cons, emitClean_nil]
                  exact armShiftImmDir_wp .lshr .W32 d ra (cb.toNat % 32)
                    (Nat.mod_lt _ (by decide)) s)
              (by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb,
                BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]; rfl)
              (fun _ => by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb]; rfl))
              (fun _ => rfl) hwp
          | exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
              (by rw [emitClean_cons, emitClean_nil]
                  exact armShiftImmDir_wp .ashr .W32 d ra (cb.toNat % 32)
                    (Nat.mod_lt _ (by decide)) s)
              (by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb,
                BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]; rfl)
              (fun _ => by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb]; rfl))
              (fun _ => rfl) hwp
        · first
          | exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
              (by rw [emitClean_cons, emitClean_nil]
                  exact armShiftImmDir_wp .shl .W64 d ra (cb.toNat % 64)
                    (Nat.mod_lt _ (by decide)) s)
              (by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb,
                BitVec.setWidth_eq, BitVec.setWidth_eq]; rfl)
              (fun h => by cases h)) (fun hz => by dsimp only [armZeroExtOp] at hz; cases hz) hwp
          | exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
              (by rw [emitClean_cons, emitClean_nil]
                  exact armShiftImmDir_wp .lshr .W64 d ra (cb.toNat % 64)
                    (Nat.mod_lt _ (by decide)) s)
              (by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb,
                BitVec.setWidth_eq, BitVec.setWidth_eq]; rfl)
              (fun h => by cases h)) (fun hz => by dsimp only [armZeroExtOp] at hz; cases hz) hwp
          | exact armKeepFinBits rfl d _ rfl (armWrDst_scr_of_eq hn64 d hdS hscr
              (by rw [emitClean_cons, emitClean_nil]
                  exact armShiftImmDir_wp .ashr .W64 d ra (cb.toNat % 64)
                    (Nat.mod_lt _ (by decide)) s)
              (by simp only [RegWidth.bits, MemWidth.bits]; rw [hra, hcb,
                BitVec.setWidth_eq, BitVec.setWidth_eq]; rfl)
              (fun h => by cases h)) (fun hz => by dsimp only [armZeroExtOp] at hz; cases hz) hwp

/-! ## 4. Scratch-Aware ALU / Compare / Select Helper `armOpScr_alu_spec` (`OPT-7b`) -/

theorem armOpScr_bin_spec {h : Host} {k n : Nat} {scr : List (Reg × BitVec 64)}
    (bk : ArmBinK) {code : OpCode [.bits n, .bits n] [.bits n]}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} (d : XReg)
    {c : List Directive} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    {va vb : BitVec n} {P : Tup Val [.bits n] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc : (armBinOpScrIns scr bk n pa pb d).map (fun (c, cl, s') => (emitClean c, cl, s')) =
      some (c, clob, scrOut))
    (hargs : ∀ r ∈ tupArgGprs (ts := [.bits n, .bits n]) (pa, pb, ()), r ∉ armScratch)
    (hd : XRegOrSp.reg d ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hpa : armMach.PArgHolds s (.bits n) pa va)
    (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hres : P (armBinEval bk va vb, ())) :
    armMach.FallsTo armCondReads h k c
        (@tupDstGprs Reg Empty ArmCond [.bits n] (.gpr (.reg d), ()) ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
          TRel (armMach.PDstHolds s')
            ((.gpr (.reg d), ()) : Tup (PDst Reg Empty ArmCond) [.bits n]) rvs ∧
          (armZeroExtOp code (pa, pb, ()) (.gpr (.reg d), ()) = true →
            AbiGprHolds (armMach.getGpr s' (.reg d)) (.bits n) (armBinEval bk va vb))) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  letI := h
  obtain ⟨⟨ci, cl', scr'⟩, hci, hceq⟩ := Option.map_eq_some_iff.mp hc
  rcases hceq with ⟨rfl, rfl, rfl⟩
  have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr =>
    hargs r (by rw [tupArgGprs_cons, List.mem_append]; exact Or.inl hr)
  have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr =>
    hargs r (by
      rw [tupArgGprs_cons, List.mem_append, tupArgGprs_cons, List.mem_append]
      exact Or.inr (Or.inl hr))
  refine armFallsTo_of_wp
    (armWp_mono (armBinOpScr_wp bk pa pb d hci hd hga hgb hscr hpa hpb) fun s' ⟨hg, hm, hfr, hs⟩ =>
      ⟨⟨⟨(armBinEval bk va vb, ()), hres, .cons hg.1 .nil, ?_⟩, hm, hs⟩, ?_⟩)
  · intro hz
    have hn32 : n = 32 := by
      cases code <;> dsimp only [armZeroExtOp] at hz <;>
        exact beq_iff_eq.mp (by simpa using hz)
    subst hn32
    exact ⟨by decide, hg.2 rfl⟩
  · simpa [tupDstGprs] using hfr

theorem armOpScr_cmp_spec {h : Host} {k n : Nat} {scr : List (Reg × BitVec 64)}
    (o : CmpOp) {pa pb : PArg Reg Empty ArmCond (.bits n)} (dst : PDst Reg Empty ArmCond .bool)
    {c : List Directive} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    {va vb : BitVec n} {P : Tup Val [.bool] → Prop} {s : MachineData} {post : MachineState → Prop}
    (hc : (armCmpOpScrIns scr o n pa pb dst).map (fun (c, cl, s') => (emitClean c, cl, s')) =
      some (c, clob, scrOut))
    (hargs : ∀ r ∈ tupArgGprs (ts := [.bits n, .bits n]) (pa, pb, ()), r ∉ armScratch)
    (hdsts : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hres : P (o.evalBits va vb, ())) :
    armMach.FallsTo armCondReads h k c (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch) []
        clob s
      (fun s' => P (o.evalBits va vb, ()) ∧
          TRel (as := [.bool]) (armMach.PDstHolds s') (dst, ()) (o.evalBits va vb, ()) ∧
          (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr s' rd) .bool (o.evalBits va vb)) ∧
          (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
            FlagCmpOk armMach armGpr s' (if lf then va else vb) (if lf then vb else va) false) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  letI := h
  obtain ⟨⟨ci, cl', scr'⟩, hci, hceq⟩ := Option.map_eq_some_iff.mp hc
  rcases hceq with ⟨rfl, rfl, rfl⟩
  have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr =>
    hargs r (by rw [tupArgGprs_cons, List.mem_append]; exact Or.inl hr)
  have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr =>
    hargs r (by
      rw [tupArgGprs_cons, List.mem_append, tupArgGprs_cons, List.mem_append]
      exact Or.inr (Or.inl hr))
  refine armFallsTo_of_wp
    (armWp_mono (armCmpOpScr_wp o pa pb dst hci hga hgb hdsts hscr hpa hpb)
      fun s' ⟨hpd, habi, hfc, hm, hfr, hs⟩ =>
        ⟨⟨hres, .cons hpd .nil, habi, hfc, hm, hs⟩, hfr⟩)

theorem armOpScr_sel_spec {h : Host} {k n : Nat} {scr : List (Reg × BitVec 64)}
    {pc : PArg Reg Empty ArmCond .bool} {pa pb : PArg Reg Empty ArmCond (.bits n)} (d : XReg)
    {c : List Directive} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    {vc : Bool} {va vb : BitVec n} {P : Tup Val [.bits n] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc : (armSelectOpScrIns scr n pc pa pb d).map (fun (c, cl, s') => (emitClean c, cl, s')) =
      some (c, clob, scrOut))
    (hargs : ∀ r ∈ tupArgGprs (ts := [.bool, .bits n, .bits n]) (pc, pa, pb, ()), r ∉ armScratch)
    (hd : XRegOrSp.reg d ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hpc : armMach.PArgHolds s .bool pc vc)
    (hpa : armMach.PArgHolds s (.bits n) pa va)
    (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hres : P (if vc then va else vb, ())) :
    armMach.FallsTo armCondReads h k c
        (@tupDstGprs Reg Empty ArmCond [.bits n] (.gpr (.reg d), ()) ++ armScratch) [] clob s
      (fun s' => P (if vc then va else vb, ()) ∧
          TRel (as := [.bits n]) (armMach.PDstHolds s') (.gpr (.reg d), ())
            (if vc then va else vb, ()) ∧
          (armZeroExtOp (.select (.bits n)) (pc, pa, pb, ()) (.gpr (.reg d), ()) = true →
            AbiGprHolds (armMach.getGpr s' (.reg d)) (.bits n) (if vc then va else vb)) ∧
        armMach.mem s' = armMach.mem s ∧ ScrOk armMach armScratch scrOut s') post := by
  letI := h
  obtain ⟨⟨ci, cl', scr'⟩, hci, hceq⟩ := Option.map_eq_some_iff.mp hc
  rcases hceq with ⟨rfl, rfl, rfl⟩
  have hgc : ∀ r ∈ pc.gprs, r ∉ armScratch := fun r hr =>
    hargs r (by rw [tupArgGprs_cons, List.mem_append]; exact Or.inl hr)
  have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr =>
    hargs r (by
      rw [tupArgGprs_cons, List.mem_append, tupArgGprs_cons, List.mem_append]
      exact Or.inr (Or.inl hr))
  have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr =>
    hargs r (by
      rw [tupArgGprs_cons, List.mem_append, tupArgGprs_cons, List.mem_append,
        tupArgGprs_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inl hr)))
  refine armFallsTo_of_wp
    (armWp_mono (armSelectOpScr_wp pc pa pb d hci hd hga hgb hgc hscr hpc hpa hpb)
      fun s' ⟨hg, hm, hfr, hs⟩ =>
        ⟨⟨hres, .cons hg.1 .nil, ?_, hm, hs⟩, ?_⟩)
  · intro hz
    dsimp only [armZeroExtOp] at hz
    have hn32 : n = 32 := beq_iff_eq.mp hz
    subst hn32
    exact ⟨by decide, hg.2 rfl⟩
  · simpa [tupDstGprs] using hfr

end LeanQbe.T.Arm64
