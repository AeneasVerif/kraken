module

public import LeanQbe.T.Arm64.IselScrLemmas1
import LeanQbe.T.Arm64.IselFlagHooksLemmas

/-!
# AArch64 Wave 6.2-A Zero-Extension & `armOpScr` Proofs — Part 2

Verifies:
* `armSetcc_zext`, `armTestOp_zext`, `armCmpMem_zext`, `armShiftCmp_zext`, `armOp_zext` (`OPT-10a`)
* `armBinOpScr_wp`, `armSelectOpScr_wp`, `armCmpOpScr_wp` (`OPT-7b` scratch-constant reuse)
* `armOpScr_spec` and `armOpScr_noLab` (`GprTarget.opScr_spec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. `AbiGprHolds` Zero-Extension Specifications (`OPT-10a`) -/

private theorem abiGprHolds_bool_01 {v : BitVec 64} {b : Bool} (h : v = BitVec.ofNat 64 b.toNat) :
    AbiGprHolds v .bool b := by
  cases b <;> simp [AbiGprHolds, h]

private theorem setWidth64_of_zext {m n : Nat} (hle : m ≤ n) (va : BitVec m) :
    va.setWidth 64 = (va.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · have him : ¬ (i < m) := fun h => hin (Nat.lt_of_lt_of_le h hle)
    simp [hin, BitVec.getLsbD_of_ge va i (Nat.le_of_not_lt him)]

theorem armSetcc_zext (_ : armGpr.zeroExtSetcc = true) {h : Host} {k : Nat}
    {rd : Reg} {c : ArmCond} {s : MachineData} {post : MachineState → Prop}
    (_ : rd ∉ armScratch) :
    armMach.FallsTo armCondReads h k (armGpr.setcc rd c) (rd :: armScratch) [] FlagMask.none s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) .bool (armMach.evalCond s c) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  refine armFallsTo_of_wp ?_
  cases rd with
  | reg d =>
    refine armWp_mono (armCset64_wp d c s) ?_
    rintro s' rfl
    refine ⟨⟨abiGprHolds_bool_01 (get_wr_same s d _), rfl⟩,
      frame_wr d _ List.mem_cons_self FlagMask.none⟩
  | SP =>
    refine armWp_cons (armCset64_wp .X16 c s) ?_
    rintro s₁ rfl
    refine armWp_mono (armMovToSp_wp .X16 (wr s .X16 _)) ?_
    rintro s' rfl
    refine ⟨⟨abiGprHolds_bool_01 (by simp [get_sp, get_wr_same]), rfl⟩,
      armFrame_status_eq (fun r hr => ?_) rfl⟩
    simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
    cases r with
    | SP => exact absurd rfl hr.1
    | reg xr =>
      have hx : .X16 ≠ xr := fun e => hr.2.1 (congrArg XRegOrSp.reg e.symm)
      simp only [get_reg]
      exact congrArg UInt64.toBitVec (Reg64s.getXReg_setXReg_of_ne s.regs .X16 xr _ hx)

theorem armTestOp_zext (_ : armGpr.zeroExtBoolCmp = true) {h : Host} {k w : Nat} {neg : Bool}
    {pa pb : PArg Reg Empty ArmCond (.bits w)} {rd : Reg} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec w} {s : MachineData} {post : MachineState → Prop}
    (hc : armGpr.testOp w neg pa pb (.gpr rd) = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ armScratch) (hrd : rd ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits w) pa va) (hpb : armMach.PArgHolds s (.bits w) pb vb) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) .bool
          ((if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  refine armFallsTo_of_wp (armWp_mono (armTestOp_wp neg pa pb (.gpr rd) hc hargs
    (by simpa using hrd) hpa hpb) ?_)
  rintro s' ⟨⟨_, habi, _⟩, hdm, hfr⟩
  exact ⟨⟨habi rd rfl, hdm⟩, by simpa using hfr⟩

theorem armCmpMem_zext (_ : armGpr.zeroExtBoolCmp = true) {h : Host} {k : Nat}
    {co : CmpOp} {w : Nat} {a : AddrArg Reg} {pb : PArg Reg Empty ArmCond (.bits w)}
    {rd : Reg} {c : List Directive} {clob : FlagMask} {va vb : BitVec w}
    {s : MachineData} {post : MachineState → Prop}
    (hc_in : armGpr.cmpMem co w a pb (.gpr rd) = some (c, clob))
    (hargs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ armScratch) (_hrd : rd ∉ armScratch)
    (hload : loadVal (armMach.mem s) (.bits w) (a.eval (armMach.getGpr s)) = some va)
    (hpb : armMach.PArgHolds s (.bits w) pb vb) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) .bool (co.evalBits va vb) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  refine armFallsTo_of_wp (armWp_mono (armCmpMem_core_wp hc hargs hload hpb) ?_)
  rintro s' ⟨_, habi, _, hdm, hfr⟩
  exact ⟨⟨habi rd rfl, hdm⟩, by simpa using hfr⟩

theorem armShiftCmp_zext (_ : armGpr.zeroExtBoolCmp = true) {h : Host} {k : Nat}
    {o : CmpOp} {w : Nat} {ra rb : Reg} {sh : AluShift} {n : Nat} {lhsShift : Bool}
    {rd : Reg} {c : List Directive} {clob : FlagMask} {va vb : BitVec w}
    {s : MachineData} {post : MachineState → Prop}
    (hc : armGpr.shiftCmp o w ra rb sh n lhsShift (.gpr rd) = some (c, clob))
    (_ : ra ∉ armScratch) (_ : rb ∉ armScratch) (_hrd : rd ∉ armScratch)
    (hpa : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hpb : GprHolds (armMach.getGpr s rb) (.bits w) vb) :
    let lhs := if lhsShift then sh.eval va n else va
    let rhs := if lhsShift then vb else sh.eval vb n
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) .bool (o.evalBits lhs rhs) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  refine armFallsTo_of_wp (armWp_mono (armShiftedCmp_wp hc hpa hpb) ?_)
  rintro s' ⟨_, habi, _, hdm, hfr⟩
  have hsh : (armAluShift sh).eval = @sh.eval w := by funext v m; cases sh <;> rfl
  refine ⟨⟨?_, hdm⟩, by simpa using hfr⟩
  cases lhsShift <;> simpa [hsh] using habi rd rfl

private theorem armArgInScr_nil {tmp : XReg} {n : Nat} (pa : PArg Reg Empty ArmCond (.bits n)) :
    (armArgInScr [] tmp pa).map (fun (ca, ra, _) => (ca, ra)) = armArgInIns tmp pa := by
  cases pa with
  | imm c => simp [armArgInScr, armMovImmScr, armHasScr, armArgInIns]
  | gpr r => cases r <;> rfl
  | vec v => exact v.elim

/-! ## 2. Scratch-Aware ALU, Select, Compare & Fallback Proofs (`OPT-7b`) -/

theorem armBinOpScr_wp [Host] {scr : List (Reg × BitVec 64)} (k : ArmBinK) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb : BitVec n} {c : List Instr} {clob : FlagMask} {scrOut : List (Reg × BitVec 64)}
    {s : MachineData}
    (hc : armBinOpScrIns scr k n pa pb d = some (c, clob, scrOut))
    (hd : XRegOrSp.reg d ∉ armScratch)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (armBinEval k va vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
      ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
  dsimp only [armBinOpScrIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hnw := mem_armWidths_le_armWidth hn
    have wrDstScr : ∀ {val64 : BitVec 64} {target : BitVec n} {scrA : List (Reg × BitVec 64)}
        {p : List Directive} {sx : MachineData},
        _root_.Program.wp p (fun s' => s' = wr sx d val64) (fun _ _ => False) sx →
        sx.dmem = s.dmem →
        armMach.Frame armCondReads s sx armScratch [] maskNone →
        ScrOk armMach armScratch scrA sx →
        val64.setWidth n = target → (n = 32 → val64 = target.setWidth 64) →
        _root_.Program.wp p (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n target ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
          ScrOk armMach armScratch scrA s') (fun _ _ => False) sx := by
      intro val64 target scrA p sx hwp hdm hfr hsc hv hv32
      refine armWp_mono hwp ?_; rintro s' rfl
      refine ⟨⟨⟨hn64, by simpa [get_wr_same] using hv⟩, fun hn32 => by
          simpa [get_wr_same] using hv32 hn32⟩,
        hdm, armFrame_scratch_wr hfr (frame_wr d _ List.mem_cons_self maskNone),
        scrOk_wr_nonScr hsc hd⟩
    have hfr0 := Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone
    have hset : ∀ x y : BitVec (armWidthOf n).bits,
        x.setWidth n = va → y.setWidth n = vb →
        ((armBinEval k x y).setWidth 64).setWidth n = armBinEval k va vb := fun x y hx hy => by
      rw [BitVec.setWidth_setWidth_of_le _ hn64]
      rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> cases k <;>
        simp only [armBinEval] at hx hy ⊢
      all_goals first
        | (subst hx hy; exact setWidth_sub_of_le hnw x y)
        | (rw [← hx, ← hy]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul,
            Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)])
        | (subst hx hy; apply BitVec.eq_of_getLsbD_eq; intro i hi;
           simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or,
             BitVec.getLsbD_xor, hi, armWidthOf])
    have hsetZ : ∀ x y : BitVec (armWidthOf n).bits,
        x.setWidth n = va → y.setWidth n = vb →
        n = 32 → (armBinEval k x y).setWidth 64 = (armBinEval k va vb).setWidth 64 := by
      intro x y hx hy hn32; subst hn32
      have hw : (armWidthOf 32).bits = 32 := rfl
      revert x y hx hy; rw [hw]
      intro x y hx hy; simp only [BitVec.setWidth_eq] at hx hy; rw [hx, hy]
    have fallback : ∀ {ca ra scr₁ cb rb scr₂},
        armArgInScr scr .X16 pa = some (ca, ra, scr₁) →
        armArgInScr scr₁ .X17 pb = some (cb, rb, scr₂) →
        c = ca ++ cb ++ [armBinDirI k (armWidthOf n) d ra rb] → clob = maskNone →
        scrOut = scr₂ →
        _root_.Program.wp (emitClean c) (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n (armBinEval k va vb) ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
          ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
      intro ca ra scr₁ cb rb scr₂ ha hb hceq hclob hsce; subst hceq hclob hsce
      rw [emitClean_append, emitClean_cons, emitClean_nil]
      refine armWp_append (armArgs2Scr_wp hn64 hn64 ha hb hpa hpb hga hgb hscr) ?_
      rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂, hscr₂⟩
      exact wrDstScr (armBinDir_wp k (armWidthOf n) d ra rb s₂) hd₂ hfr₂ hscr₂
        (hset _ _ (by rwa [BitVec.setWidth_setWidth_of_le _ hnw])
          (by rwa [BitVec.setWidth_setWidth_of_le _ hnw]))
        (hsetZ _ _ (by rwa [BitVec.setWidth_setWidth_of_le _ hnw])
          (by rwa [BitVec.setWidth_setWidth_of_le _ hnw]))
    have hfbRun : (armArgInScr scr .X16 pa >>= fun a => armArgInScr a.2.2 .X17 pb >>= fun b =>
        some (a.1 ++ b.1 ++ [armBinDirI k (armWidthOf n) d a.2.1 b.2.1], maskNone, b.2.2)) =
          some (c, clob, scrOut) →
        _root_.Program.wp (emitClean c) (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n (armBinEval k va vb) ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
          ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := fun h => by
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨⟨ca, ra, scr₁⟩, ha, ⟨cb, rb, scr₂⟩, hb, rfl, rfl, rfl⟩
      exact fallback ha hb rfl rfl rfl
    have addSubImmStep : ∀ (isSub isSwap : Bool) (_hvalid : isSub = false ∨ isSwap = false)
        (rx : XReg) (imm : BitVec n) {dir : Instr},
        armAddSubImmI? isSub (armWidthOf n) d rx imm = some dir →
        (if isSub then k = .sub else k = .add) →
        (if isSwap then
          (armMach.PArgHolds s (.bits n) (.imm imm) va ∧
            armMach.PArgHolds s (.bits n) (.gpr (.reg rx)) vb)
         else
          (armMach.PArgHolds s (.bits n) (.gpr (.reg rx)) va ∧
            armMach.PArgHolds s (.bits n) (.imm imm) vb)) →
        c = [dir] → clob = maskNone → scrOut = scr →
        _root_.Program.wp (emitClean c) (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n (armBinEval k va vb) ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
          ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
      intro isSub isSwap hvalid rx imm dir hdir hk' hps hc' hclob hsce
      subst hc' hclob hsce
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armAddSubImmI_wp hn64 hnw (fun e => e ▸ rfl) isSub d rx imm hdir s) ?_
      rintro s' ⟨val64, rfl, hval, hvalZ⟩
      refine ⟨⟨⟨hn64, ?_⟩, fun hn32 => ?_⟩, rfl, frame_wr d _ List.mem_cons_self maskNone,
        scrOk_wr_nonScr hscr hd⟩
      · cases isSub <;> simp only [↓reduceIte, Bool.false_eq_true] at hk' hval <;> subst hk'
        · cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hps
          · have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.1.2
            have him : imm = vb := by simpa [Machine.PArgHolds] using hps.2
            simpa [get_wr_same, armBinEval, hra, him] using hval
          · have hrb : (s.regs.getXReg rx).toBitVec.setWidth n = vb := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.2.2
            have him : imm = va := by simpa [Machine.PArgHolds] using hps.1
            simpa [get_wr_same, armBinEval, hrb, him, BitVec.add_comm] using hval
        · cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hps
          · have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.1.2
            have him : imm = vb := by simpa [Machine.PArgHolds] using hps.2
            simpa [get_wr_same, armBinEval, hra, him] using hval
          · rcases hvalid with h | h <;> cases h
      · have hz := hvalZ hn32; subst hn32
        cases isSub <;> simp only [↓reduceIte, Bool.false_eq_true] at hk' hz <;> subst hk'
        · cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hps
          · have hra : (s.regs.getXReg rx).toBitVec.setWidth 32 = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.1.2
            have him : imm = vb := by simpa [Machine.PArgHolds] using hps.2
            simpa [get_wr_same, armBinEval, hra, him, BitVec.setWidth_eq] using hz
          · have hrb : (s.regs.getXReg rx).toBitVec.setWidth 32 = vb := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.2.2
            have him : imm = va := by simpa [Machine.PArgHolds] using hps.1
            simpa [get_wr_same, armBinEval, hrb, him, BitVec.setWidth_eq, BitVec.add_comm] using hz
        · cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hps
          · have hra : (s.regs.getXReg rx).toBitVec.setWidth 32 = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.1.2
            have him : imm = vb := by simpa [Machine.PArgHolds] using hps.2
            simpa [get_wr_same, armBinEval, hra, him, BitVec.setWidth_eq] using hz
          · rcases hvalid with h | h <;> cases h
    have logicImmStep : ∀ (isSwap : Bool) (rx : XReg) (imm : BitVec n) (wlog : RegWidth)
        (c64 : BitVec 64) {dir : Instr},
        (k = .and ∨ k = .or ∨ k = .xor) →
        (wlog = armWidthOf n ∨ (n = 8 ∨ n = 16) ∧ wlog = .W32) →
        c64.setWidth n = imm →
        (n = 32 → c64.setWidth 32 = imm.setWidth 32) →
        armLogicImmDirI k wlog d rx (Int64.ofBitVec c64) = some dir →
        (if isSwap then
          (armMach.PArgHolds s (.bits n) (.imm imm) va ∧
            armMach.PArgHolds s (.bits n) (.gpr (.reg rx)) vb)
         else
          (armMach.PArgHolds s (.bits n) (.gpr (.reg rx)) va ∧
            armMach.PArgHolds s (.bits n) (.imm imm) vb)) →
        c = [dir] → clob = maskNone → scrOut = scr →
        _root_.Program.wp (emitClean c) (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n (armBinEval k va vb) ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
          ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
      intro isSwap rx imm wlog c64 dir hklog hwlog hc64 hc64_32 hdir hps hc' hclob hsce
      subst hc' hclob hsce
      simp only [emitClean_cons, emitClean_nil]
      have hcomm : ∀ {m : Nat} (x y : BitVec m), armBinEval k x y = armBinEval k y x := by
        intro m x y; rcases hklog with rfl | rfl | rfl <;>
          simp only [armBinEval, BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm]
      have hnwl : n ≤ wlog.bits := by
        rcases hwlog with rfl | ⟨hn816, rfl⟩; exact hnw; rcases hn816 with rfl | rfl <;> decide
      have himmw : (c64.setWidth wlog.bits).setWidth n = imm := by
        rw [BitVec.setWidth_setWidth_of_le _ hnwl, hc64]
      have hsetWlog : ∀ x y : BitVec wlog.bits,
          x.setWidth n = va → y.setWidth n = vb →
          ((armBinEval k x y).setWidth 64).setWidth n = armBinEval k va vb := fun x y hx hy => by
        rw [BitVec.setWidth_setWidth_of_le _ hn64]; subst hx hy
        rcases hklog with rfl | rfl | rfl <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
          simp [hi, Nat.lt_of_lt_of_le hi hnwl, armBinEval]
      have hsetZWlog : ∀ x y : BitVec wlog.bits,
          x.setWidth n = va → y.setWidth n = vb →
          n = 32 → (armBinEval k x y).setWidth 64 = (armBinEval k va vb).setWidth 64 := by
        intro x y hx hy hn32; subst hn32
        rcases hwlog with rfl | ⟨hn816, _⟩
        · have hw32 : (armWidthOf 32).bits = 32 := rfl
          revert x y hx hy; rw [hw32]
          intro x y hx hy; simp only [BitVec.setWidth_eq] at hx hy; rw [hx, hy]
        · rcases hn816 with h | h <;> cases h
      refine wrDstScr (armLogicImm_wp k wlog d rx c64 dir hdir s) rfl hfr0 hscr ?_ ?_
      · cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hps
        · have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.1.2
          have him : imm = vb := by simpa [Machine.PArgHolds] using hps.2
          exact hsetWlog _ _ (by rw [BitVec.setWidth_setWidth_of_le _ hnwl, hra])
            (by rw [himmw, him])
        · have hrb : (s.regs.getXReg rx).toBitVec.setWidth n = vb := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.2.2
          have him : imm = va := by simpa [Machine.PArgHolds] using hps.1
          rw [hcomm ((s.regs.getXReg rx).toBitVec.setWidth _) _]
          exact hsetWlog _ _ (by rw [himmw, him])
            (by rw [BitVec.setWidth_setWidth_of_le _ hnwl, hrb])
      · intro hn32; subst hn32
        rcases hwlog with rfl | ⟨h8 | h16, _⟩ <;> try contradiction
        have hcw : c64.setWidth (armWidthOf 32).bits = imm := by
          simpa [RegWidth.bits, MemWidth.bits, armWidthOf, BitVec.setWidth_eq] using hc64_32 rfl
        cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hps
        · have hra : (s.regs.getXReg rx).toBitVec.setWidth 32 = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.1.2
          have him : imm = vb := by simpa [Machine.PArgHolds] using hps.2
          exact hsetZWlog _ _ (by rw [BitVec.setWidth_setWidth_of_le _ hnwl, hra])
            (by rw [hcw, him]; exact BitVec.setWidth_eq _) rfl
        · have hrb : (s.regs.getXReg rx).toBitVec.setWidth 32 = vb := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hps.2.2
          have him : imm = va := by simpa [Machine.PArgHolds] using hps.1
          rw [hcomm ((s.regs.getXReg rx).toBitVec.setWidth _) _]
          exact hsetZWlog _ _ (by rw [hcw, him]; exact BitVec.setWidth_eq _)
            (by rw [BitVec.setWidth_setWidth_of_le _ hnwl, hrb]) rfl
    have find?_some_prop' : ∀ {α : Type} (p : α → Bool) {l : List α} {a : α},
        l.find? p = some a → p a = true := by
      intro α p l a h
      induction l with
      | nil => simp at h
      | cons x xs ih =>
        simp only [List.find?] at h; split at h
        · cases h; assumption
        · exact ih h
    have bv_mul_pow2' : ∀ (x : BitVec n) {kshift : Nat},
        kshift < n → x * (1#n <<< kshift) = x <<< kshift := by
      intro x kshift hklt
      have hpow : 2 ^ kshift < 2 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 2) hklt
      have h1 : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt h1, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hpow]
    have armMulRegImmScr_wp : ∀ (r : XReg) (imm : BitVec n) {vr : BitVec n},
        (s.regs.getXReg r).toBitVec.setWidth n = vr → XRegOrSp.reg r ∉ armScratch →
        let res := armMulRegImmScrIns scr (armWidthOf n) d r imm
        _root_.Program.wp (emitClean res.1) (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n (vr * imm) ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
          ScrOk armMach armScratch res.2 s') (fun _ _ => False) s := by
      intro r imm vr hr hrS
      dsimp only [armMulRegImmScrIns]
      by_cases hz : imm == 0#n
      · simp only [hz, ↓reduceIte]
        refine armWp_mono (armMovImm_wp d 0#64 s) ?_
        rintro s' rfl
        have h0 : vr * imm = 0#n := by rw [beq_iff_eq.mp hz]; simp
        refine ⟨⟨⟨hn64, ?_⟩, ?_⟩, rfl, frame_wr d _ List.mem_cons_self maskNone,
          scrOk_wr_nonScr hscr hd⟩
        · simp [get_wr_same, h0]
        · intro hn32; subst hn32; simp [get_wr_same, h0]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        by_cases hm1 : imm == ~~~0#n
        · simp only [hm1, ↓reduceIte, emitClean_cons, emitClean_nil]
          have himm : imm = ~~~0#n := beq_iff_eq.mp hm1
          have hmul : -vr = vr * ~~~0#n := by
            rw [show (~~~0#n) = (-1#n) from by
              rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> decide]
            simp [BitVec.mul_neg]
          refine wrDstScr (armSubNegDir_wp (armWidthOf n) d r s) rfl hfr0 hscr ?_ ?_
          · rw [BitVec.setWidth_setWidth_of_le _ hn64, setWidth_neg_of_le hnw,
              BitVec.setWidth_setWidth_of_le _ hnw, hr, himm]; exact hmul
          · intro hn32; subst hn32
            rw [show (armWidthOf 32).bits = 32 from rfl, hr, himm, hmul]
        · simp only [hm1, Bool.false_eq_true, ↓reduceIte]
          cases hp2 : armPow2Shift? imm with
          | some kshift =>
            simp only
            have hfind : (List.range n).find? (fun k => imm == 1#n <<< k) = some kshift := hp2
            have hklt : kshift < n := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
            have himm : imm = 1#n <<< kshift :=
              beq_iff_eq.mp (find?_some_prop' (fun k => imm == 1#n <<< k) hfind)
            have hmul : vr <<< kshift = vr * imm := by rw [himm, bv_mul_pow2' vr hklt]
            by_cases hk0 : kshift == 0
            · have hk0' : kshift = 0 := beq_iff_eq.mp hk0
              subst hk0'
              simp only [beq_self_eq_true, ↓reduceIte, emitClean_cons, emitClean_nil]
              have himm1 : imm = 1#n := by simpa using himm
              refine wrDstScr (armMovRegDir_wp (armWidthOf n) d r s) rfl hfr0 hscr ?_ ?_
              · rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_setWidth_of_le _ hnw,
                  hr, himm1]
                simp
              · intro hn32; subst hn32
                rw [show (armWidthOf 32).bits = 32 from rfl, hr, himm1]; simp
            · simp only [hk0, Bool.false_eq_true, ↓reduceIte, emitClean_cons, emitClean_nil]
              have hkltw : kshift < (armWidthOf n).bits := Nat.lt_of_lt_of_le hklt hnw
              have hshw :
                  (((s.regs.getXReg r).toBitVec.setWidth
                    (armWidthOf n).bits <<< kshift).setWidth 64).setWidth n = vr * imm := by
                rw [BitVec.setWidth_setWidth_of_le _ hn64, ← hmul]
                apply BitVec.eq_of_getLsbD_eq; intro i hi
                simp [hi, Nat.lt_of_lt_of_le hi hnw, ← hr]
              refine wrDstScr (armShiftImmDir_wp .shl (armWidthOf n) d r kshift hkltw s)
                rfl hfr0 hscr hshw ?_
              intro hn32; subst hn32
              rw [show (armWidthOf 32).bits = 32 from rfl, hr, hmul]
          | none =>
            simp only
            cases hp21 : armPow2Plus1Shift? imm with
            | some kshift =>
              simp only [emitClean_cons, emitClean_nil]
              have hfind : (List.range n).tail.find?
                  (fun k => imm == (1#n <<< k) + 1#n) = some kshift := hp21
              have hklt : kshift < n :=
                List.mem_range.mp (List.mem_of_mem_tail (List.mem_of_find?_eq_some hfind))
              have himm : imm = (1#n <<< kshift) + 1#n :=
                beq_iff_eq.mp (find?_some_prop' (fun k => imm == (1#n <<< k) + 1#n) hfind)
              have hmul : vr + (vr <<< kshift) = vr * imm := by
                rw [himm, BitVec.mul_add, BitVec.mul_one, bv_mul_pow2' vr hklt, BitVec.add_comm]
              have hkltw : kshift < (armWidthOf n).bits := Nat.lt_of_lt_of_le hklt hnw
              refine wrDstScr (armAddShiftLslDir_wp (armWidthOf n) d r r kshift hkltw s)
                rfl hfr0 hscr ?_ ?_
              · rw [BitVec.setWidth_setWidth_of_le _ hn64, ← hmul]
                have haddw : ∀ (x y : BitVec (armWidthOf n).bits),
                    (x + y).setWidth n = x.setWidth n + y.setWidth n := fun x y => by
                  apply BitVec.eq_of_toNat_eq
                  simp [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)]
                rw [haddw, BitVec.setWidth_setWidth_of_le _ hnw, hr]
                congr 1; apply BitVec.eq_of_getLsbD_eq; intro i hi
                simp [hi, Nat.lt_of_lt_of_le hi hnw, ← hr]
              · intro hn32; subst hn32
                rw [show (armWidthOf 32).bits = 32 from rfl, hr, hmul]
            | none =>
              simp only
              generalize hmov : armMovImmScr scr .X17 (imm.setWidth 64) = ms
              rcases ms with ⟨cim, scr''⟩
              have ha : armArgInScr scr .X16 (.gpr (.reg r) : PArg Reg Empty ArmCond (.bits n)) =
                  some ([], r, scr) := rfl
              have hb : armArgInScr scr .X17 (.imm imm : PArg Reg Empty ArmCond (.bits n)) =
                  some (cim, .X17, scr'') := by simp [armArgInScr, hmov]
              have hpa' : armMach.PArgHolds s (.bits n) (.gpr (.reg r)) vr := ⟨hn64, hr⟩
              have hpb' : armMach.PArgHolds s (.bits n) (.imm imm) imm := rfl
              have hga' : ∀ r' ∈ (PArg.gpr (.reg r) : PArg Reg Empty ArmCond (.bits n)).gprs,
                  r' ∉ armScratch := by simpa [PArg.gprs] using hrS
              rw [emitClean_append, emitClean_cons, emitClean_nil]
              refine armWp_append
                (armArgs2Scr_wp hn64 hn64 ha hb hpa' hpb' hga' (by simp [PArg.gprs]) hscr) ?_
              rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂, hscr₂⟩
              refine wrDstScr (armBinDir_wp .mul (armWidthOf n) d r .X17 s₂) hd₂ hfr₂ hscr₂ ?_ ?_
              · rw [BitVec.setWidth_setWidth_of_le _ hn64]
                have h1 :=
                  BitVec.setWidth_setWidth_of_le (s₂.regs.getXReg r).toBitVec hnw |>.trans hra
                have h2 :=
                  BitVec.setWidth_setWidth_of_le (s₂.regs.getXReg .X17).toBitVec hnw |>.trans hrb
                rw [← h1, ← h2]
                apply BitVec.eq_of_toNat_eq
                simp [armBinEval, BitVec.toNat_mul, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)]
              · intro hn32; subst hn32
                rw [show (armWidthOf 32).bits = 32 from rfl, hra, hrb]; rfl
    cases k with
    | mul =>
      cases pa with
      | vec vr => exact vr.elim
      | imm ca => cases pb with
        | vec vr => exact vr.elim
        | imm _ => dsimp only at hc; exact hfbRun hc
        | gpr r => cases r with
          | SP => dsimp only at hc; simp [armArgInScr] at hc
          | reg rb =>
            dsimp only at hc
            rcases Option.some.inj hc with ⟨rfl, rfl, rfl⟩
            have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
            have hca : ca = va := hpa
            have hgb' : XRegOrSp.reg rb ∉ armScratch := hgb (.reg rb) (by simp [PArg.gprs])
            have hmul := armMulRegImmScr_wp rb ca hrb hgb'
            refine armWp_mono hmul fun s' ⟨hg, hm, hfr, hsc⟩ => ⟨?_, hm, hfr, hsc⟩
            simpa only [armBinEval, hca, BitVec.mul_comm] using hg
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgInScr] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ => dsimp only at hc; exact hfbRun hc
          | imm cb =>
            dsimp only at hc
            rcases Option.some.inj hc with ⟨rfl, rfl, rfl⟩
            have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
            have hcb : cb = vb := hpb
            have hga' : XRegOrSp.reg ra ∉ armScratch := hga (.reg ra) (by simp [PArg.gprs])
            have hmul := armMulRegImmScr_wp ra cb hra hga'
            refine armWp_mono hmul fun s' ⟨hg, hm, hfr, hsc⟩ => ⟨?_, hm, hfr, hsc⟩
            simpa only [armBinEval, hcb] using hg
    | and | or | xor =>
      cases pa with
      | vec vr => exact vr.elim
      | imm ca => cases pb with
        | vec vr => exact vr.elim
        | imm _ => dsimp only at hc; exact hfbRun hc
        | gpr r => cases r with
          | SP => dsimp only at hc; simp [armArgInScr] at hc
          | reg rb =>
            dsimp only at hc; split at hc
            · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
              rcases hc with ⟨dir, hdir, rfl, rfl, rfl⟩
              exact logicImmStep true rb ca (armWidthOf n) (ca.setWidth 64)
                (by
                  first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
                    exact Or.inr (Or.inr rfl))
                (Or.inl rfl) (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
                (fun hn32 => by
                  subst hn32; rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq])
                (congrArg some hdir) ⟨hpa, hpb⟩ rfl rfl rfl
            · split at hc
              · next h816 =>
                have hn816 : n = 8 ∨ n = 16 := by
                  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h816; exact h816.1
                simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
                rcases hc with ⟨dir, hdir, rfl, rfl, rfl⟩
                exact logicImmStep true rb ca .W32 (ca.signExtend 64)
                  (by
                    first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
                      exact Or.inr (Or.inr rfl))
                  (Or.inr ⟨hn816, rfl⟩)
                  (by
                    rcases hn816 with rfl | rfl <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
                      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
                        show i < 64 by omega, decide_true, Bool.true_and, ↓reduceIte])
                  (fun hn32 => by rcases hn816 with h | h <;> cases (h.symm.trans hn32))
                  (congrArg some hdir) ⟨hpa, hpb⟩ rfl rfl rfl
              · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
                rcases hc with ⟨⟨ca', ra, scr'⟩, ha, rfl, rfl, rfl⟩
                exact fallback (cb := []) (rb := rb) (scr₂ := scr') ha rfl (by simp) rfl rfl
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgInScr] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ => dsimp only at hc; exact hfbRun hc
          | imm cb =>
            dsimp only at hc; split at hc
            · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
              rcases hc with ⟨dir, hdir, rfl, rfl, rfl⟩
              exact logicImmStep false ra cb (armWidthOf n) (cb.setWidth 64)
                (by
                  first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
                    exact Or.inr (Or.inr rfl))
                (Or.inl rfl) (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
                (fun hn32 => by
                  subst hn32; rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq])
                (congrArg some hdir) ⟨hpa, hpb⟩ rfl rfl rfl
            · split at hc
              · next h816 =>
                have hn816 : n = 8 ∨ n = 16 := by
                  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h816; exact h816.1
                simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
                rcases hc with ⟨dir, hdir, rfl, rfl, rfl⟩
                exact logicImmStep false ra cb .W32 (cb.signExtend 64)
                  (by
                    first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
                      exact Or.inr (Or.inr rfl))
                  (Or.inr ⟨hn816, rfl⟩)
                  (by
                    rcases hn816 with rfl | rfl <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
                      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
                        show i < 64 by omega, decide_true, Bool.true_and, ↓reduceIte])
                  (fun hn32 => by rcases hn816 with h | h <;> cases (h.symm.trans hn32))
                  (congrArg some hdir) ⟨hpa, hpb⟩ rfl rfl rfl
              · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
                rcases hc with ⟨⟨cb', rb, scr'⟩, hb, rfl, rfl, rfl⟩
                exact fallback (ca := []) (ra := ra) (scr₁ := scr) rfl hb rfl rfl rfl
    | add =>
      cases pa with
      | vec vr => exact vr.elim
      | imm ca => cases pb with
        | vec vr => exact vr.elim
        | imm _ => dsimp only at hc; exact hfbRun hc
        | gpr r => cases r with
          | SP => dsimp only at hc; simp [armArgInScr] at hc
          | reg rb =>
            dsimp only at hc
            rcases option_none_or_some (armAddSubImmI? false (armWidthOf n) d rb ca) with
              hnone | ⟨dir, hdir⟩
            · simp only [hnone, bind, Option.bind_eq_some_iff, Option.some.injEq,
                Prod.mk.injEq] at hc
              rcases hc with ⟨⟨ca', ra, scr'⟩, ha, rfl, rfl, rfl⟩
              exact fallback (cb := []) (rb := rb) (scr₂ := scr') ha rfl (by simp) rfl rfl
            · simp only [hdir, Option.some.injEq, Prod.mk.injEq] at hc
              exact addSubImmStep false true (Or.inl rfl) rb ca hdir rfl ⟨hpa, hpb⟩
                hc.1.symm hc.2.1.symm hc.2.2.symm
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgInScr] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ => dsimp only at hc; exact hfbRun hc
          | imm cb =>
            dsimp only at hc
            rcases option_none_or_some (armAddSubImmI? false (armWidthOf n) d ra cb) with
              hnone | ⟨dir, hdir⟩
            · simp only [hnone, bind, Option.bind_eq_some_iff, Option.some.injEq,
                Prod.mk.injEq] at hc
              rcases hc with ⟨⟨cb', rb, scr'⟩, hb, rfl, rfl, rfl⟩
              exact fallback (ca := []) (ra := ra) (scr₁ := scr) rfl hb rfl rfl rfl
            · simp only [hdir, Option.some.injEq, Prod.mk.injEq] at hc
              exact addSubImmStep false false (Or.inl rfl) ra cb hdir rfl ⟨hpa, hpb⟩
                hc.1.symm hc.2.1.symm hc.2.2.symm
    | sub =>
      cases pa with
      | vec vr => exact vr.elim
      | imm ca => cases pb with
        | vec vr => exact vr.elim
        | imm _ => dsimp only at hc; exact hfbRun hc
        | gpr r => cases r with
          | SP => dsimp only at hc; simp [armArgInScr] at hc
          | reg rb =>
            dsimp only at hc
            by_cases hca0 : ca == 0#n
            · simp only [hca0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
              rcases hc with ⟨rfl, rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
              have hva0 : va = 0#n := hpa.symm.trans (beq_iff_eq.mp hca0)
              have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
                simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
              refine wrDstScr (armSubNegDir_wp (armWidthOf n) d rb s) rfl hfr0 hscr ?_ ?_
              · rw [BitVec.setWidth_setWidth_of_le _ hn64, setWidth_neg_of_le hnw,
                  BitVec.setWidth_setWidth_of_le _ hnw, hrb]
                simp [armBinEval, hva0]
              · intro hn32; subst hn32
                rw [show (armWidthOf 32).bits = 32 from rfl, hrb]; simp [armBinEval, hva0]
            · simp only [hca0, Bool.false_eq_true, ↓reduceIte] at hc
              by_cases hcan1 : ca == ~~~0#n
              · simp only [hcan1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
                rcases hc with ⟨rfl, rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
                have hvan1 : va = ~~~0#n := hpa.symm.trans (beq_iff_eq.mp hcan1)
                have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
                  simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
                have hnot0 : ∀ z : BitVec n, (~~~0#n) - z = ~~~z := fun z => by
                  apply BitVec.eq_of_toNat_eq
                  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
                  have hlt := z.isLt
                  simp [BitVec.toNat_not, BitVec.toNat_sub]
                  rw [show 2 ^ n - z.toNat + (2 ^ n - 1) = (2 ^ n - 1 - z.toNat) + 2 ^ n by omega,
                    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                refine wrDstScr (armOrnNotDir_wp (armWidthOf n) d rb s) rfl hfr0 hscr ?_ ?_
                · rw [BitVec.setWidth_setWidth_of_le _ hn64]; dsimp only [armBinEval]
                  rw [hvan1, hnot0]
                  apply BitVec.eq_of_getLsbD_eq; intro i hi
                  rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                    simp [hi, armWidthOf, ← hrb]
                · intro hn32; subst hn32
                  rw [show (armWidthOf 32).bits = 32 from rfl, hrb]; dsimp only [armBinEval]
                  rw [hvan1, hnot0]
              · simp only [hcan1, Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff,
                  Option.some.injEq, Prod.mk.injEq] at hc
                rcases hc with ⟨⟨ca', ra, scr'⟩, ha, rfl, rfl, rfl⟩
                exact fallback (cb := []) (rb := rb) (scr₂ := scr') ha rfl (by simp) rfl rfl
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgInScr] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ => dsimp only at hc; exact hfbRun hc
          | imm cb =>
            dsimp only at hc
            rcases option_none_or_some (armAddSubImmI? true (armWidthOf n) d ra cb) with
              hnone | ⟨dir, hdir⟩
            · simp only [hnone, bind, Option.bind_eq_some_iff, Option.some.injEq,
                Prod.mk.injEq] at hc
              rcases hc with ⟨⟨cb', rb, scr'⟩, hb, rfl, rfl, rfl⟩
              exact fallback (ca := []) (ra := ra) (scr₁ := scr) rfl hb rfl rfl rfl
            · simp only [hdir, Option.some.injEq, Prod.mk.injEq] at hc
              exact addSubImmStep true false (Or.inr rfl) ra cb hdir rfl ⟨hpa, hpb⟩
                hc.1.symm hc.2.1.symm hc.2.2.symm

theorem armSelectCondScr_wp [Host] {scr : List (Reg × BitVec 64)} {n : Nat}
    (hn : n ∈ [8, 16, 32, 64]) (cond : ArmCond)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {vc : Bool} {va vb : BitVec n} {c : List Instr} {scrOut : List (Reg × BitVec 64)}
    {s : MachineData}
    (hc : armSelectCondScrIns scr n cond pa pb d = some (c, scrOut))
    (hd : XRegOrSp.reg d ∉ armScratch) (hpc : cond.interp s.status = vc)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
      ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
  have hn64 := mem_armWidths_le_64 hn
  have hnw := mem_armWidths_le_armWidth hn
  have hfr0 := Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone
  have wrDstScr : ∀ {val64 : BitVec 64} {target : BitVec n} {scrA : List (Reg × BitVec 64)}
      {p : List Directive} {sx : MachineData},
      _root_.Program.wp p (fun s' => s' = wr sx d val64) (fun _ _ => False) sx →
      sx.dmem = s.dmem → armMach.Frame armCondReads s sx armScratch [] maskNone →
      ScrOk armMach armScratch scrA sx →
      val64.setWidth n = target → (n = 32 → val64 = target.setWidth 64) →
      _root_.Program.wp p (fun s' =>
        GprHoldsZ (armMach.getGpr s' (.reg d)) n target ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
        ScrOk armMach armScratch scrA s') (fun _ _ => False) sx := by
    intro val64 target scrA p sx hwp hdm hfr hsc hv hv32
    refine armWp_mono hwp ?_; rintro s' rfl
    refine ⟨⟨⟨hn64, by simpa [get_wr_same] using hv⟩, fun hn32 => by
        simpa [get_wr_same] using hv32 hn32⟩,
      hdm, armFrame_scratch_wr hfr (frame_wr d _ List.mem_cons_self maskNone),
      scrOk_wr_nonScr hsc hd⟩
  have fallback : (do
        let (ca, ra, scr1) ← armArgInScr scr .X16 pa
        let (cb, rb, scr2) ← armArgInScr scr1 .X17 pb
        some (ca ++ cb ++ [armIselInsI (.CSEL (zr d (armWidthOf n)) (zr ra (armWidthOf n))
          (zr rb (armWidthOf n)) cond.toKraken)], scr2)) = some (c, scrOut) →
      _root_.Program.wp (emitClean c) (fun s' =>
        GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
        ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
    intro hfb
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hfb
    rcases hfb with ⟨⟨ca, ra, scr1⟩, ha, ⟨cb, rb, scr2⟩, hb, rfl, rfl⟩
    rw [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append (armArgs2Scr_wp hn64 hn64 ha hb hpa hpb hga hgb hscr) ?_
    rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂, hscr₂⟩
    refine wrDstScr (armCselDir_wp (armWidthOf n) d ra rb cond.toKraken s₂) hd₂ hfr₂ hscr₂ ?_ ?_
    · rw [show cond.toKraken.interp s₂.status = vc from hst₂ ▸ hpc]
      cases vc <;> simp only [↓reduceIte, Bool.false_eq_true, BitVec.setWidth_setWidth_of_le _ hn64]
      · rw [BitVec.setWidth_setWidth_of_le _ hnw, hrb]
      · rw [BitVec.setWidth_setWidth_of_le _ hnw, hra]
    · intro hn32; subst hn32
      rw [show cond.toKraken.interp s₂.status = vc from hst₂ ▸ hpc,
        show (armWidthOf 32).bits = 32 from rfl]
      cases vc <;> simp only [↓reduceIte, Bool.false_eq_true]
      · rw [hrb]
      · rw [hra]
  have fastRegImm : ∀ (op : Nat) (isSwap : Bool) (rx : XReg) {vr : BitVec n}
      (hrx : (s.regs.getXReg rx).toBitVec.setWidth n = vr)
      (himm : (if isSwap then va else vb) = match op with
        | 0 => 0#n | 1 => 1#n | _ => ~~~0#n)
      (hreg : (if isSwap then vb else va) = vr)
      (hc_eq : c = [match op with
        | 0 => armIselInsI (.CSEL (zr d (armWidthOf n)) (zr rx (armWidthOf n)) (xzr (armWidthOf n))
            (if isSwap then armNegCond cond else cond).toKraken)
        | 1 => armIselInsI (.CSINC (zr d (armWidthOf n)) (zr rx (armWidthOf n)) (xzr (armWidthOf n))
            (if isSwap then armNegCond cond else cond).toKraken)
        | _ => armIselInsI (.CSINV (zr d (armWidthOf n)) (zr rx (armWidthOf n)) (xzr (armWidthOf n))
            (if isSwap then armNegCond cond else cond).toKraken)])
      (hsce : scrOut = scr),
      _root_.Program.wp (emitClean c) (fun s' =>
        GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
        ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
    intro op isSwap rx vr hrx himm hreg hceq hsce; subst hceq hsce
    simp only [emitClean_cons, emitClean_nil]
    have hcnd : (if isSwap then armNegCond cond else cond).interp s.status =
        if isSwap then !vc else vc := by
      cases isSwap <;> simp [armNegCond_interp, hpc]
    have hrxw : (s.regs.getRegOrZr (.low (.reg rx) (armWidthOf n))).setWidth n = vr := by
      have h' : s.regs.getRegOrZr (.low (.reg rx) (armWidthOf n)) =
          (s.regs.getXReg rx).toBitVec.setWidth (armWidthOf n).bits := by
        cases armWidthOf n <;>
          (simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take];
           apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi])
      rw [h', BitVec.setWidth_setWidth_of_le _ hnw, hrx]
    have hrx32 :
        s.regs.getRegOrZr (.low (.reg rx) .W32) = (s.regs.getXReg rx).toBitVec.setWidth 32 := by
      simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
    rcases op with _ | _ | op
    · refine wrDstScr (armSelectDir_wp 0 (armWidthOf n) d (.reg rx) .XZR
          (if isSwap then armNegCond cond else cond) s) rfl hfr0 hscr ?_ ?_
      · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] at himm hreg ⊢
        all_goals first
          | rw [hrxw, hreg]
          | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
             simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
      · intro hn32; subst hn32
        rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
            Bool.not_false] at himm hreg ⊢ <;>
          first | rw [hrx, hreg] | (rw [himm]; try decide)
    · refine wrDstScr (armSelectDir_wp 1 (armWidthOf n) d (.reg rx) .XZR
          (if isSwap then armNegCond cond else cond) s) rfl hfr0 hscr ?_ ?_
      · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] at himm hreg ⊢
        all_goals first
          | rw [hrxw, hreg]
          | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
             simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
      · intro hn32; subst hn32
        rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
            Bool.not_false] at himm hreg ⊢ <;>
          first | rw [hrx, hreg] | (rw [himm]; try decide)
    · refine wrDstScr (armSelectDir_wp (op + 2) (armWidthOf n) d (.reg rx) .XZR
          (if isSwap then armNegCond cond else cond) s) rfl hfr0 hscr ?_ ?_
      · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] at himm hreg ⊢
        all_goals first
          | rw [hrxw, hreg]
          | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
             simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
      · intro hn32; subst hn32
        rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
            Bool.not_false] at himm hreg ⊢ <;>
          first | rw [hrx, hreg] | (rw [himm]; try decide)
  cases pa with
  | vec vr => exact vr.elim
  | imm ca => cases pb with
    | vec vr => exact vr.elim
    | gpr r => cases r with
      | SP => dsimp only [armSelectCondScrIns] at hc; simp [armArgInScr] at hc
      | reg rb =>
        have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
        have hca : ca = va := hpa
        dsimp only [armSelectCondScrIns] at hc
        by_cases hc0 : ca == 0#n
        · simp only [hc0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          exact fastRegImm 0 true rb hrb (hca.symm.trans (beq_iff_eq.mp hc0)) rfl hc.1.symm
            hc.2.symm
        · by_cases hc1 : ca == 1#n
          · simp only [hc0, hc1, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
              Prod.mk.injEq] at hc
            exact fastRegImm 1 true rb hrb (hca.symm.trans (beq_iff_eq.mp hc1)) rfl hc.1.symm
              hc.2.symm
          · by_cases hcn1 : ca == ~~~0#n
            · simp only [hc0, hc1, hcn1, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
                Prod.mk.injEq] at hc
              exact fastRegImm 2 true rb hrb (hca.symm.trans (beq_iff_eq.mp hcn1)) rfl hc.1.symm
                hc.2.symm
            · simp only [hc0, hc1, hcn1, Bool.false_eq_true, ↓reduceIte, bind,
                Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
              rcases hc with ⟨⟨ca', ra', scr'⟩, ha, rfl, rfl⟩
              exact fallback (by rw [ha]; dsimp only [armArgInScr]; simp)
    | imm cb =>
      have hca : ca = va := hpa; have hcb : cb = vb := hpb
      dsimp only [armSelectCondScrIns] at hc
      by_cases heq : ca == cb
      · simp only [heq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩
        have hcae : ca = vb := (beq_iff_eq.mp heq).trans hcb
        have hv : va = vb := hca.symm.trans hcae
        rw [hcae]
        refine wrDstScr (armMovImm_wp d (vb.setWidth 64) s) rfl hfr0 hscr ?_ ?_
        · rw [hv, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]; cases vc <;> rfl
        · intro hn32; subst hn32; rw [hv]; cases vc <;> rfl
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hc
        have fastImmImm : ∀ (isInv flip : Bool),
            (va = if isInv then (if flip then ~~~0#n else 0#n) else (if flip then 1#n else 0#n)) →
            (vb = if isInv then (if flip then 0#n else ~~~0#n) else (if flip then 0#n else 1#n)) →
            c = [if isInv then
                armIselInsI (.CSINV (zr d (armWidthOf n)) (xzr (armWidthOf n)) (xzr (armWidthOf n))
                  (if flip then armNegCond cond else cond).toKraken)
              else
                armIselInsI (.CSINC (zr d (armWidthOf n)) (xzr (armWidthOf n)) (xzr (armWidthOf n))
                  (if flip then armNegCond cond else cond).toKraken)] →
            scrOut = scr →
            _root_.Program.wp (emitClean c) (fun s' =>
              GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
              armMach.mem s' = armMach.mem s ∧
              armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
              ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
          intro isInv flip hva hvb hceq hsce; subst hceq hsce
          simp only [emitClean_cons, emitClean_nil]
          have hcnd : (if flip then armNegCond cond else cond).interp s.status =
              if flip then !vc else vc := by
            cases flip <;> simp [armNegCond_interp, hpc]
          cases isInv
          · refine wrDstScr (armSelectDir_wp 1 (armWidthOf n) d .XZR .XZR
                (if flip then armNegCond cond else cond) s) rfl hfr0 hscr ?_ ?_
            · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
              rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                cases flip <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
                  armWidthOf, RegWidth.bits, MemWidth.bits] <;>
                first | (rw [hva]; decide) | (rw [hvb]; decide)
            · intro hn32; subst hn32
              rw [show armWidthOf 32 = .W32 from rfl, hcnd, getRegOrZr_low_xzr]
              cases flip <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
                  RegWidth.bits, MemWidth.bits] <;>
                first | (rw [hva]; decide) | (rw [hvb]; decide)
          · refine wrDstScr (armSelectDir_wp 2 (armWidthOf n) d .XZR .XZR
                (if flip then armNegCond cond else cond) s) rfl hfr0 hscr ?_ ?_
            · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
              rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                cases flip <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
                  armWidthOf, RegWidth.bits, MemWidth.bits] <;>
                first | (rw [hva]; decide) | (rw [hvb]; decide)
            · intro hn32; subst hn32
              rw [show armWidthOf 32 = .W32 from rfl, hcnd, getRegOrZr_low_xzr]
              cases flip <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
                  RegWidth.bits, MemWidth.bits] <;>
                first | (rw [hva]; decide) | (rw [hvb]; decide)
        by_cases h10 : (ca == 1#n && cb == 0#n) = true
        · simp only [h10, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          simp only [Bool.and_eq_true, beq_iff_eq] at h10
          exact fastImmImm false true (hca.symm.trans h10.1) (hcb.symm.trans h10.2)
            hc.1.symm hc.2.symm
        · simp only [h10, Bool.false_eq_true, ↓reduceIte] at hc
          by_cases h01 : (ca == 0#n && cb == 1#n) = true
          · simp only [h01, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
            simp only [Bool.and_eq_true, beq_iff_eq] at h01
            exact fastImmImm false false (hca.symm.trans h01.1) (hcb.symm.trans h01.2)
              hc.1.symm hc.2.symm
          · simp only [h01, Bool.false_eq_true, ↓reduceIte] at hc
            by_cases hn10 : (ca == ~~~0#n && cb == 0#n) = true
            · simp only [hn10, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
              simp only [Bool.and_eq_true, beq_iff_eq] at hn10
              exact fastImmImm true true (hca.symm.trans hn10.1) (hcb.symm.trans hn10.2)
                hc.1.symm hc.2.symm
            · simp only [hn10, Bool.false_eq_true, ↓reduceIte] at hc
              by_cases h0n1 : (ca == 0#n && cb == ~~~0#n) = true
              · simp only [h0n1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
                simp only [Bool.and_eq_true, beq_iff_eq] at h0n1
                exact fastImmImm true false (hca.symm.trans h0n1.1) (hcb.symm.trans h0n1.2)
                  hc.1.symm hc.2.symm
              · simp only [h0n1, Bool.false_eq_true, ↓reduceIte] at hc
                have fastImmOne : ∀ (op : Nat) (isSwap : Bool) (tmp : XReg)
                    (htmp : XRegOrSp.reg tmp ∈ armScratch)
                    {ca' : List Instr} {ra : XReg} {scr' : List (Reg × BitVec 64)}
                    (himm : (if isSwap then va else vb) = match op with
                      | 0 => 0#n | 1 => 1#n | _ => ~~~0#n)
                    (ha : armArgInScr scr tmp (if isSwap then .imm cb else .imm ca) =
                      some (ca', ra, scr'))
                    (hc_eq : c = ca' ++ [match op with
                      | 0 => armIselInsI (.CSEL (zr d (armWidthOf n)) (zr ra (armWidthOf n))
                          (xzr (armWidthOf n)) (if isSwap then armNegCond cond else cond).toKraken)
                      | 1 => armIselInsI (.CSINC (zr d (armWidthOf n)) (zr ra (armWidthOf n))
                          (xzr (armWidthOf n)) (if isSwap then armNegCond cond else cond).toKraken)
                      | _ => armIselInsI (.CSINV (zr d (armWidthOf n)) (zr ra (armWidthOf n))
                          (xzr (armWidthOf n))
                          (if isSwap then armNegCond cond else cond).toKraken)])
                    (hsce : scrOut = scr'),
                    _root_.Program.wp (emitClean c) (fun s' =>
                      GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
                      armMach.mem s' = armMach.mem s ∧
                      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
                      ScrOk armMach armScratch scrOut s')
                      (fun _ _ => False) s := by
                  intro op isSwap tmp htmp ca' ra scr' himm ha hceq hsce
                  subst hceq hsce
                  rw [emitClean_append]
                  have hpa1 : armMach.PArgHolds s (.bits n) (if isSwap then .imm cb else .imm ca)
                      (if isSwap then vb else va) := by
                    cases isSwap; exact hca; exact hcb
                  refine armWp_append (armArgInScr_wp hn64 htmp ha hpa1 hscr) ?_
                  rintro s₁ ⟨hra₁, _, _, hdmem₁, hst₁, hfr₁, hscr₁⟩
                  have hfrScr : armMach.Frame armCondReads s s₁ armScratch [] maskNone :=
                    hfr₁.weaken (fun r hr => by simp_all) (fun v => v.elim) rfl
                  simp only [emitClean_cons, emitClean_nil]
                  have hcnd : (if isSwap then armNegCond cond else cond).interp s₁.status =
                      if isSwap then !vc else vc := by
                    rw [hst₁]; cases isSwap <;> simp [armNegCond_interp, hpc]
                  have hrxw : (s₁.regs.getRegOrZr (.low (.reg ra) (armWidthOf n))).setWidth n =
                      if isSwap then vb else va := by
                    have h' : s₁.regs.getRegOrZr (.low (.reg ra) (armWidthOf n)) =
                        (s₁.regs.getXReg ra).toBitVec.setWidth (armWidthOf n).bits := by
                      cases armWidthOf n <;>
                        (simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64,
                           RegOrZr.base, BitVec.take];
                         apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi])
                    rw [h', BitVec.setWidth_setWidth_of_le _ hnw, hra₁]
                  have hrx32 : s₁.regs.getRegOrZr (.low (.reg ra) .W32) =
                      (s₁.regs.getXReg ra).toBitVec.setWidth 32 := by
                    simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]
                    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
                  rcases op with _ | _ | op
                  · refine wrDstScr (armSelectDir_wp 0 (armWidthOf n) d (.reg ra) .XZR
                        (if isSwap then armNegCond cond else cond) s₁) hdmem₁ hfrScr hscr₁ ?_ ?_
                    · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
                      cases isSwap <;> cases vc <;>
                        simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
                          Bool.not_false] at himm hrxw ⊢
                      all_goals first
                        | rw [hrxw]
                        | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
                           simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
                    · intro hn32; subst hn32
                      rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
                      cases isSwap <;> cases vc <;>
                        simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
                          Bool.not_false] at himm hra₁ ⊢ <;>
                        first | rw [hra₁] | (rw [himm]; try decide)
                  · refine wrDstScr (armSelectDir_wp 1 (armWidthOf n) d (.reg ra) .XZR
                        (if isSwap then armNegCond cond else cond) s₁) hdmem₁ hfrScr hscr₁ ?_ ?_
                    · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
                      cases isSwap <;> cases vc <;>
                        simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
                          Bool.not_false] at himm hrxw ⊢
                      all_goals first
                        | rw [hrxw]
                        | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
                           simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
                    · intro hn32; subst hn32
                      rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
                      cases isSwap <;> cases vc <;>
                        simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
                          Bool.not_false] at himm hra₁ ⊢ <;>
                        first | rw [hra₁] | (rw [himm]; try decide)
                  · refine wrDstScr (armSelectDir_wp (op + 2) (armWidthOf n) d (.reg ra) .XZR
                        (if isSwap then armNegCond cond else cond) s₁) hdmem₁ hfrScr hscr₁ ?_ ?_
                    · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
                      cases isSwap <;> cases vc <;>
                        simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
                          Bool.not_false] at himm hrxw ⊢
                      all_goals first
                        | rw [hrxw]
                        | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
                           simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
                    · intro hn32; subst hn32
                      rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
                      cases isSwap <;> cases vc <;>
                        simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
                          Bool.not_false] at himm hra₁ ⊢ <;>
                        first | rw [hra₁] | (rw [himm]; try decide)
                by_cases hcb0 : (cb == 0#n) = true
                · simp only [hcb0, ↓reduceIte, bind, Option.bind_eq_some_iff, Option.some.injEq,
                    Prod.mk.injEq] at hc
                  rcases hc with ⟨⟨ca', ra, scr'⟩, ha, rfl, rfl⟩
                  exact fastImmOne 0 false .X16 x16_mem_scratch
                    (hcb.symm.trans (beq_iff_eq.mp hcb0)) ha rfl rfl
                · simp only [hcb0, Bool.false_eq_true, ↓reduceIte] at hc
                  by_cases hcb1 : (cb == 1#n) = true
                  · simp only [hcb1, ↓reduceIte, bind, Option.bind_eq_some_iff, Option.some.injEq,
                      Prod.mk.injEq] at hc
                    rcases hc with ⟨⟨ca', ra, scr'⟩, ha, rfl, rfl⟩
                    exact fastImmOne 1 false .X16 x16_mem_scratch
                      (hcb.symm.trans (beq_iff_eq.mp hcb1)) ha rfl rfl
                  · simp only [hcb1, Bool.false_eq_true, ↓reduceIte] at hc
                    by_cases hcbn1 : (cb == ~~~0#n) = true
                    · simp only [hcbn1, ↓reduceIte, bind, Option.bind_eq_some_iff,
                        Option.some.injEq, Prod.mk.injEq] at hc
                      rcases hc with ⟨⟨ca', ra, scr'⟩, ha, rfl, rfl⟩
                      exact fastImmOne 2 false .X16 x16_mem_scratch
                        (hcb.symm.trans (beq_iff_eq.mp hcbn1)) ha rfl rfl
                    · simp only [hcbn1, Bool.false_eq_true, ↓reduceIte] at hc
                      by_cases hca0 : (ca == 0#n) = true
                      · simp only [hca0, ↓reduceIte, bind, Option.bind_eq_some_iff,
                          Option.some.injEq, Prod.mk.injEq] at hc
                        rcases hc with ⟨⟨cb', rb, scr'⟩, hb, rfl, rfl⟩
                        exact fastImmOne 0 true .X17 x17_mem_scratch
                          (hca.symm.trans (beq_iff_eq.mp hca0)) hb rfl rfl
                      · simp only [hca0, Bool.false_eq_true, ↓reduceIte] at hc
                        by_cases hca1 : (ca == 1#n) = true
                        · simp only [hca1, ↓reduceIte, bind, Option.bind_eq_some_iff,
                            Option.some.injEq, Prod.mk.injEq] at hc
                          rcases hc with ⟨⟨cb', rb, scr'⟩, hb, rfl, rfl⟩
                          exact fastImmOne 1 true .X17 x17_mem_scratch
                            (hca.symm.trans (beq_iff_eq.mp hca1)) hb rfl rfl
                        · simp only [hca1, Bool.false_eq_true, ↓reduceIte] at hc
                          by_cases hcan1 : (ca == ~~~0#n) = true
                          · simp only [hcan1, ↓reduceIte, bind, Option.bind_eq_some_iff,
                              Option.some.injEq, Prod.mk.injEq] at hc
                            rcases hc with ⟨⟨cb', rb, scr'⟩, hb, rfl, rfl⟩
                            exact fastImmOne 2 true .X17 x17_mem_scratch
                              (hca.symm.trans (beq_iff_eq.mp hcan1)) hb rfl rfl
                          · simp only [hcan1, Bool.false_eq_true, ↓reduceIte] at hc
                            exact fallback hc
  | gpr r => cases r with
    | SP =>
      dsimp only [armSelectCondScrIns] at hc
      cases pb <;> simp [armArgInScr] at hc
    | reg ra =>
      have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
      cases pb with
      | vec vr => exact vr.elim
      | gpr _ => dsimp only [armSelectCondScrIns] at hc; exact fallback hc
      | imm cb =>
        have hcb : cb = vb := hpb
        dsimp only [armSelectCondScrIns] at hc
        by_cases hc0 : cb == 0#n
        · simp only [hc0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          exact fastRegImm 0 false ra hra (hcb.symm.trans (beq_iff_eq.mp hc0)) rfl hc.1.symm
            hc.2.symm
        · by_cases hc1 : cb == 1#n
          · simp only [hc0, hc1, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
              Prod.mk.injEq] at hc
            exact fastRegImm 1 false ra hra (hcb.symm.trans (beq_iff_eq.mp hc1)) rfl hc.1.symm
              hc.2.symm
          · by_cases hcn1 : cb == ~~~0#n
            · simp only [hc0, hc1, hcn1, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
                Prod.mk.injEq] at hc
              exact fastRegImm 2 false ra hra (hcb.symm.trans (beq_iff_eq.mp hcn1)) rfl hc.1.symm
                hc.2.symm
            · simp only [hc0, hc1, hcn1, Bool.false_eq_true, ↓reduceIte, bind,
                Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
              rcases hc with ⟨⟨cb', rb', scr'⟩, hb, rfl, rfl⟩
              exact fallback (by
                have ha' :
                    armArgInScr scr .X16 (.gpr (.reg ra) : PArg Reg Empty ArmCond (.bits n)) =
                      some ([], ra, scr) := rfl
                rw [ha']; simp only [bind, Option.bind_some, hb]; rfl)

theorem armSelectOpScr_wp [Host] {scr : List (Reg × BitVec 64)} {n : Nat}
    (pc : PArg Reg Empty ArmCond .bool) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {vc : Bool} {va vb : BitVec n} {c : List Instr} {clob : FlagMask}
    {scrOut : List (Reg × BitVec 64)} {s : MachineData}
    (hc : armSelectOpScrIns scr n pc pa pb d = some (c, clob, scrOut))
    (hd : XRegOrSp.reg d ∉ armScratch)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (_hgc : ∀ r ∈ pc.gprs, r ∉ armScratch)
    (hscr : ScrOk armMach armScratch scr s)
    (hpc : armMach.PArgHolds s .bool pc vc)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob ∧
      ScrOk armMach armScratch scrOut s') (fun _ _ => False) s := by
  dsimp only [armSelectOpScrIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hnw := mem_armWidths_le_armWidth hn
    have copyScr : ∀ {xpa : PArg Reg Empty ArmCond (.bits n)} {xv : BitVec n}
        {ci : List Instr} {cl : FlagMask},
        armCopyBitsIns n xpa d = some (ci, cl) → armMach.PArgHolds s (.bits n) xpa xv →
        _root_.Program.wp (emitClean ci) (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n xv ∧ armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] cl ∧
          ScrOk armMach armScratch scr s') (fun _ _ => False) s := by
      intro xpa xv ci cl hci hxp
      have finWr : ∀ {val64 : BitVec 64} {p : List Directive},
          _root_.Program.wp p (fun s' => s' = wr s d val64) (fun _ _ => False) s →
          val64.setWidth n = xv → (n = 32 → val64 = xv.setWidth 64) →
          _root_.Program.wp p (fun s' =>
            GprHoldsZ (armMach.getGpr s' (.reg d)) n xv ∧ armMach.mem s' = armMach.mem s ∧
            armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone ∧
            ScrOk armMach armScratch scr s') (fun _ _ => False) s := by
        intro val64 p hwp hv hv32
        refine armWp_mono hwp ?_; rintro s' rfl
        refine ⟨⟨⟨hn64, by simpa [get_wr_same] using hv⟩, fun hn32 => by
            simpa [get_wr_same] using hv32 hn32⟩,
          rfl, frame_wr d _ List.mem_cons_self maskNone, scrOk_wr_nonScr hscr hd⟩
      cases xpa with
      | vec vr => exact vr.elim
      | gpr r => cases r with | SP => simp [armCopyBitsIns] at hci | reg rx =>
        simp only [armCopyBitsIns, Option.some.injEq, Prod.mk.injEq] at hci
        rcases hci with ⟨rfl, rfl⟩; simp only [emitClean_cons, emitClean_nil]
        have hrx : (s.regs.getXReg rx).toBitVec.setWidth n = xv := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hxp.2
        exact finWr (armMovRegDir_wp (armWidthOf n) d rx s)
          (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_setWidth_of_le _ hnw,
            hrx])
          (fun hn32 => by subst hn32; rw [show (armWidthOf 32).bits = 32 from rfl, hrx])
      | imm cv =>
        simp only [armCopyBitsIns, Option.some.injEq, Prod.mk.injEq] at hci
        rcases hci with ⟨rfl, rfl⟩; simp only [Machine.PArgHolds] at hxp; subst hxp
        exact finWr (armMovImm_wp d (cv.setWidth 64) s)
          (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
          (fun hn32 => by subst hn32; rfl)
    cases pc with
    | vec vr => exact vr.elim
    | imm bv =>
      simp only [Machine.PArgHolds] at hpc; subst hpc
      cases bv
      · dsimp only at hc; rw [Option.map_eq_some_iff] at hc
        rcases hc with ⟨⟨ci, cl'⟩, hci, hceq⟩; cases hceq
        exact copyScr hci hpb
      · dsimp only at hc; rw [Option.map_eq_some_iff] at hc
        rcases hc with ⟨⟨ci, cl'⟩, hci, hceq⟩; cases hceq
        exact copyScr hci hpa
    | flag cond =>
      dsimp only at hc; simp only [bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hc
      rcases hc with ⟨⟨sel, scr'⟩, hsel, rfl, rfl, rfl⟩
      exact armSelectCondScr_wp hn cond pa pb d hsel hd hpc hga hgb hscr hpa hpb
    | gpr r => cases r with | SP => simp at hc | reg rc =>
      dsimp only at hc; simp only [bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hc
      rcases hc with ⟨⟨sel, scr'⟩, hsel, rfl, rfl, rfl⟩
      have hrc : (s.regs.getXReg rc).toBitVec.setWidth 8 = BitVec.ofNat 8 vc.toNat := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hpc
      let st1 := StatusFlags.from_result
        ((s.regs.getXReg rc).toBitVec.setWidth 32 &&& 1#32) { c := false, v := false }
      rw [emitClean_cons]
      refine armWp_cons (armDirFallsTo_wp (Q := fun s' => s' = { s with status := st1 })
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_one, RegWidth.bits,
            MemWidth.bits]
          exact hk _ rfl) ?_
      rintro s₁ rfl
      have hpa₁ : armMach.PArgHolds { s with status := st1 } (.bits n) pa va := by
        cases pa with | vec vr => exact vr.elim | imm _ => exact hpa | gpr _ => exact hpa
      have hpb₁ : armMach.PArgHolds { s with status := st1 } (.bits n) pb vb := by
        cases pb with | vec vr => exact vr.elim | imm _ => exact hpb | gpr _ => exact hpb
      have hne1 : ArmCond.ne.interp st1 = vc := by
        have hmask : (s.regs.getXReg rc).toBitVec.setWidth 32 &&& 1#32 =
            if vc then 1#32 else 0#32 := by
          have hb0 := congrArg (fun z => z.getLsbD 0) hrc
          apply BitVec.eq_of_getLsbD_eq; intro i hi
          by_cases hi0 : i = 0
          · subst hi0; simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth] at hb0 ⊢
            cases vc <;> simp_all <;> decide
          · have h0 : (1#32 : BitVec 32).getLsbD i = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
                (Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ i)))
            cases vc <;> simp [BitVec.getLsbD_and, h0]
        change CondCode.NE.interp st1 = vc
        dsimp only [st1]; rw [hmask]; cases vc <;> decide
      have hscr₁ : ScrOk armMach armScratch scr { s with status := st1 } :=
        scrOk_of_keeps hscr fun r _ => by cases r <;> rfl
      refine armWp_mono (armSelectCondScr_wp hn .ne pa pb d hsel hd hne1 hga hgb hscr₁ hpa₁ hpb₁)
        ?_
      rintro s' ⟨hg, hdm, hfr, hscr'⟩
      exact ⟨hg, hdm, armFrame_nzcv fun r hr => hfr.1 r hr, hscr'⟩

end LeanQbe.T.Arm64
