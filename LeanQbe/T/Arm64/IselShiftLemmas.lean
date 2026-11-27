module

public import LeanQbe.T.Arm64.IselShift
public import LeanQbe.T.Arm64.IselLemmas30
import Kraken.AArch64.Parser

/-!
# Arm64 Shifted- & Extended-Register ALU/CMP Correctness Proofs (`IselShiftLemmas`)

Proves `FallsTo armMach` simulation, `FlagCmpOk`, `zero32`, and label-freedom for:
* `armShiftedAlu?` (`ADD_s`/`SUB_s`/`AND_s`/`ORR_s`/`EOR_s`)
* `armShiftedCmp?` (`SUBS_s` with `LSL`/`LSR`/`ASR` on LHS or RHS)
* `armExtAlu?` (`ADD_e`/`SUB_e` with `UXTB`/`SXTB`/`UXTH`/`SXTH`/`UXTW`/`SXTW`)
* `armExtCmp?` (`SUBS_e` with `UXTB`..`SXTW` on LHS or RHS)
plus `ParserChecks` verifying every emitted instruction matches `Kraken.AArch64.Parser`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

section

/-! ## 1. Width & `armShiftedAlu?` Correctness -/

/-- Valid `armShiftWidth?` widths are strictly `32` (`W32`) or `64` (`W64`). -/
theorem armShiftWidth?_eq {w : Nat} {rw : RegWidth}
    (h : armShiftWidth? w = some rw) :
    (w = 32 ∧ rw = .W32) ∨ (w = 64 ∧ rw = .W64) := by
  cases w with
  | zero => simp [armShiftWidth?] at h
  | succ n =>
      unfold armShiftWidth? at h
      split at h <;> simp_all

/-- Any `armShiftedAlu?` result carries `maskNone` flags. -/
theorem armShiftedAlu?_clob_none {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]}
    {ra rb : Reg} {sh : ArmShiftOp} {k : Nat} {rd : Reg}
    {dirs : List Directive} {clob : FlagMask}
    (h : armShiftedAlu? w c ra rb sh k rd = some (dirs, clob)) :
    clob = maskNone := by
  unfold armShiftedAlu? at h
  rcases emitCleanPair_eq_some.mp h with ⟨_, _, _⟩
  rename_i raw hraw _
  simp only [Option.map_eq_some_iff] at hraw
  rcases hraw with ⟨_, _, hpair⟩
  cases hpair
  rfl

/-- Every directive emitted by `armShiftedAlu?` is an `.instr` (never a `.label`). -/
theorem armShiftedAlu_noLab {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]}
    {ra rb : Reg} {sh : ArmShiftOp} {k : Nat} {rd : Reg}
    {dirs : List Directive} {clob : FlagMask}
    (h : armShiftedAlu? w c ra rb sh k rd = some (dirs, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ dirs :=
  emitCleanPair_noLab h l

/-- Deconstruct a successful `armShiftedAlu?` call into its validated components. -/
theorem armShiftedAlu?_eq_some {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]}
    {ra rb : Reg} {sh : ArmShiftOp} {k : Nat} {rd : Reg}
    {dirs : List Directive} {clob : FlagMask}
    (h : armShiftedAlu? w c ra rb sh k rd = some (dirs, clob)) :
    ∃ rw op d a b,
      k < w ∧
      armShiftWidth? w = some rw ∧
      armShiftAluOfOpCode? c = some op ∧
      rd = .reg d ∧ ra = .reg a ∧ rb = .reg b ∧
      dirs = [armShiftedAluDirI op rw d a b sh k] ∧
      clob = maskNone := by
  unfold armShiftedAlu? armShiftedAluIns at h
  rcases emitCleanPair_eq_some.mp h with ⟨raw, hraw, rfl⟩
  simp only [Option.map_eq_some_iff] at hraw
  rcases hraw with ⟨insList, hinsList, hpair⟩
  cases hpair
  split at hinsList
  · contradiction
  · rename_i hlt
    have hk : k < w := by simpa [Nat.blt_eq] using hlt
    cases hw : armShiftWidth? w with
    | none => simp [hw] at hinsList
    | some rw =>
      cases hop : armShiftAluOfOpCode? c with
      | none => simp [hw, hop] at hinsList
      | some op =>
        cases rd with
        | SP => simp [hw, hop, armRegX?] at hinsList
        | reg d =>
          cases ra with
          | SP => simp [hw, hop, armRegX?] at hinsList
          | reg a =>
            cases rb with
            | SP => simp [hw, hop, armRegX?] at hinsList
            | reg b =>
              simp [hw, hop, armRegX?] at hinsList
              subst hinsList
              exact ⟨rw, op, d, a, b, hk, rfl, rfl, rfl, rfl, rfl,
                by simp [emitClean_cons, emitClean_nil, armShiftedAluDirI], rfl⟩

/-- Small shift counts `< 2 ^ 63` satisfy `(↑k).bmod Int64.size = ↑k`, so `.toNat = k`. -/
private theorem bmod_int64_toNat {k : Nat} (hk : k < 2 ^ 63) :
    ((k : Int).bmod Int64.size).toNat = k := by
  have hs : Int64.size = 2 ^ 64 := by decide
  unfold Int.bmod
  rw [hs]
  dsimp
  split <;> omega

/-- When `k < w`, `ShiftRegExpr.interp` matches `ArmShiftOp.eval`. -/
theorem armShiftRegExpr_interp (rw : RegWidth) (rb : XReg)
    (sh : ArmShiftOp) (k : Nat) (hk : k < rw.bits)
    (regs : Reg64s) (mem : Std.Rco Int64) :
    (armShiftRegExpr rw rb sh k).interp regs mem =
      sh.eval ((regs.getXReg rb).toBitVec.setWidth rw.bits) k := by
  have hk64 : k < 2 ^ 63 := Nat.lt_trans hk (by cases rw <;> decide)
  have hmod := bmod_int64_toNat hk64
  cases rw <;> cases sh <;>
    simp [armShiftRegExpr, ArmShiftOp.toKraken, ArmShiftOp.eval,
      ShiftRegExpr.interp, getRegOrZr_zr, hmod]

/-- Single-instruction WP for `armShiftedAluDirI` updating `rd` and leaving memory untouched. -/
theorem armShiftedAluDir_wp [Host] (op : ArmShiftAluOp) (rw : RegWidth)
    (rd ra rb : XReg) (sh : ArmShiftOp) (k : Nat) (hk : k < rw.bits)
    (s : MachineData) :
    _root_.Program.wp [armShiftedAluDirI op rw rd ra rb sh k]
      (fun s' =>
        let va := (s.regs.getXReg ra).toBitVec.setWidth rw.bits
        let vb := sh.eval ((s.regs.getXReg rb).toBitVec.setWidth rw.bits) k
        s' = wr s rd ((op.eval va vb).setWidth 64))
      (fun _ _ => False) s := by
  have hk64 : k < 2 ^ 63 := Nat.lt_trans hk (by cases rw <;> decide)
  have hmod := bmod_int64_toNat hk64
  cases rw <;> cases op <;> cases sh <;>
    simp only [armShiftedAluDirI, armShiftedAluInstrI] <;>
    apply armDirFallsTo_wp <;>
    simp [armDirFallsTo, armShiftRegExpr, ArmShiftOp.toKraken,
      ArmShiftOp.eval, ArmShiftAluOp.eval, t_step_simp, hmod, wr]

/-- Relate `ArmShiftAluOp.eval` on `va, vb` from `OpCode.wp`. -/
theorem armShiftAluOfOpCode_wp {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]} {op : ArmShiftAluOp}
    (hc : armShiftAluOfOpCode? c = some op)
    {va vb : BitVec w} {post : BitVec w → Prop} :
    c.wp (va, vb, ()) (fun (res, ()) => post res) →
    post (op.eval va vb) := by
  cases c with
  | add _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simp [OpCode.wp, lift2, ArmShiftAluOp.eval]
  | sub _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simp [OpCode.wp, lift2, ArmShiftAluOp.eval]
  | and _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simp [OpCode.wp, lift2, ArmShiftAluOp.eval]
  | or  _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simp [OpCode.wp, lift2, ArmShiftAluOp.eval]
  | xor _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simp [OpCode.wp, lift2, ArmShiftAluOp.eval]
  | _     => simp [armShiftAluOfOpCode?] at hc

/-- Lift `post (op.eval va vb)` into `OpCode.wp`. -/
theorem armShiftAluOfOpCode_wp_of {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]} {op : ArmShiftAluOp}
    (hc : armShiftAluOfOpCode? c = some op)
    {va vb : BitVec w} {post : BitVec w → Prop}
    (hp : post (op.eval va vb)) :
    c.wp (va, vb, ()) (fun (res, ()) => post res) := by
  cases c with
  | add _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simpa [OpCode.wp, lift2, ArmShiftAluOp.eval] using hp
  | sub _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simpa [OpCode.wp, lift2, ArmShiftAluOp.eval] using hp
  | and _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simpa [OpCode.wp, lift2, ArmShiftAluOp.eval] using hp
  | or  _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simpa [OpCode.wp, lift2, ArmShiftAluOp.eval] using hp
  | xor _ => simp [armShiftAluOfOpCode?] at hc; subst hc
             simpa [OpCode.wp, lift2, ArmShiftAluOp.eval] using hp
  | _     => simp [armShiftAluOfOpCode?] at hc

/-- Width-32 or width-64 truncation of a 64-bit extension is the identity. -/
theorem setWidth_setWidth64_eq {w : Nat} (hw : w ≤ 64) (v : BitVec w) :
    (v.setWidth 64).setWidth w = v := by
  simpa using BitVec.setWidth_setWidth_of_le (x := v) hw

/-- Full WP theorem for `armShiftedAlu?` with `GprHoldsZ` and `rd :: armScratch` framing. -/
theorem armShiftedAlu_wp [Host] {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]} {op : ArmShiftAluOp}
    {ra rb : Reg} {sh : ArmShiftOp} {k : Nat} {rd : Reg}
    {dirs : List Directive} {clob : FlagMask}
    (hins : armShiftedAlu? w c ra rb sh k rd = some (dirs, clob))
    (hop : armShiftAluOfOpCode? c = some op)
    {s : MachineData} {va vb : BitVec w}
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits w) vb) :
    _root_.Program.wp dirs
      (fun s' =>
        GprHoldsZ (armMach.getGpr s' rd) w (op.eval va (sh.eval vb k)) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (rd :: armScratch) [] clob)
      (fun _ _ => False) s := by
  rcases armShiftedAlu?_eq_some hins with
    ⟨rw, op', d, a, b, hk, hw, hop', hrd, hra, hrb, hdirs, hclob⟩
  rw [hop] at hop'
  injection hop' with hopEq
  subst hopEq hrd hra hrb hdirs hclob
  have hbits : w = rw.bits := by
    rcases armShiftWidth?_eq hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  subst hbits
  have hw64 : rw.bits ≤ 64 := by cases rw <;> decide
  have hva : (s.regs.getXReg a).toBitVec.setWidth rw.bits = va := by
    simpa [armMach, get_reg, GprHolds] using ha.2
  have hvb : (s.regs.getXReg b).toBitVec.setWidth rw.bits = vb := by
    simpa [armMach, get_reg, GprHolds] using hb.2
  have hdir := armShiftedAluDir_wp op rw d a b sh k hk s
  simp only [hva, hvb] at hdir
  exact armWrDst_of_eq hw64 d hdir
    (setWidth_setWidth64_eq hw64 (op.eval va (sh.eval vb k)))
    (fun _ => rfl)

/-- Exact-register `FallsTo` theorem with `OpCode.wp` semantics (matching `GprTarget`). -/
theorem armShiftedAlu_spec (h : Host) {steps : Nat} {w : Nat}
    (c : OpCode [.bits w, .bits w] [.bits w])
    (ra rb : Reg) (sh : ArmShiftOp) (k : Nat) (rd : Reg)
    (dirs : List Directive) (clob : FlagMask)
    (hins : armShiftedAlu? w c ra rb sh k rd = some (dirs, clob))
    (s : MachineData) (va vb : BitVec w)
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits w) vb)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h steps dirs (rd :: armScratch) [] clob s
      (fun s' =>
        c.wp (va, sh.eval vb k, ()) (fun (res, ()) =>
          GprHolds (armMach.getGpr s' rd) (.bits w) res) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (rd :: armScratch) [] clob)
      post := by
  rcases armShiftedAlu?_eq_some hins with
    ⟨_, op, _, _, _, _, _, hop, _, _, _, _, _⟩
  have hwp := @armShiftedAlu_wp h w c op ra rb sh k rd dirs clob hins hop s va vb ha hb
  apply armFallsTo_of_wp
  refine armWp_mono hwp ?_
  intro s' ⟨hhold, hmem, hfr⟩
  exact ⟨⟨armShiftAluOfOpCode_wp_of hop
    (post := fun res => GprHolds (armMach.getGpr s' rd) (.bits w) res) hhold.holds,
    hmem, hfr⟩, hfr⟩

/-- Zero-extending `armMach.FallsTo` spec for `w = 32`: guarantees upper 32 bits of `rd` are 0. -/
theorem armShiftedAlu_zero32 (h : Host) {steps : Nat}
    (c : OpCode [.bits 32, .bits 32] [.bits 32])
    (ra rb : Reg) (sh : ArmShiftOp) (k : Nat) (rd : Reg)
    (dirs : List Directive) (clob : FlagMask)
    (hins : armShiftedAlu? 32 c ra rb sh k rd = some (dirs, clob))
    (s : MachineData) (va vb : BitVec 32)
    (ha : GprHolds (armMach.getGpr s ra) (.bits 32) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits 32) vb)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h steps dirs (rd :: armScratch) [] clob s
      (fun s' =>
        c.wp (va, sh.eval vb k, ()) (fun (res, ()) =>
          armMach.getGpr s' rd = res.setWidth 64) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (rd :: armScratch) [] clob)
      post := by
  rcases armShiftedAlu?_eq_some hins with
    ⟨_, op, _, _, _, _, _, hop, _, _, _, _, _⟩
  have hwp := @armShiftedAlu_wp h 32 c op ra rb sh k rd dirs clob hins hop s va vb ha hb
  apply armFallsTo_of_wp
  refine armWp_mono hwp ?_
  intro s' ⟨hhold, hmem, hfr⟩
  exact ⟨⟨armShiftAluOfOpCode_wp_of hop
    (post := fun res => armMach.getGpr s' rd = res.setWidth 64) hhold.zero32,
    hmem, hfr⟩, hfr⟩

/-- Exact-result `FallsTo` theorem exposing `ArmShiftAluOp.eval` and `[rd]` framing directly. -/
theorem armShiftedAlu_fallsTo_eval (h : Host) {steps : Nat} {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]} {op : ArmShiftAluOp}
    (ra rb : Reg) (sh : ArmShiftOp) (k : Nat) (rd : Reg)
    (dirs : List Directive) (clob : FlagMask)
    (hins : armShiftedAlu? w c ra rb sh k rd = some (dirs, clob))
    (hop : armShiftAluOfOpCode? c = some op)
    (s : MachineData) (va vb : BitVec w)
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits w) vb)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h steps dirs (rd :: armScratch) [] clob s
      (fun s' =>
        GprHoldsZ (armMach.getGpr s' rd) w (op.eval va (sh.eval vb k)) ∧
        armMach.mem s' = armMach.mem s)
      post := by
  have hwp := @armShiftedAlu_wp h w c op ra rb sh k rd dirs clob hins hop s va vb ha hb
  apply armFallsTo_of_wp
  exact armWp_mono hwp (fun _ ⟨hhold, hmem, hfr⟩ => ⟨⟨hhold, hmem⟩, hfr⟩)

/-! ## 2. Shared `armCmpFinish` Combinator & Shifted `CMP` (`SUBS_s`) -/

private theorem armCmpFinish_wp [Host] {cmpIns : Instr} {cond : ArmCond}
    {dst : PDst Reg Empty ArmCond .bool} {c : List Instr} {clob : FlagMask}
    {w : Nat} {x y : BitVec w} {res : Bool} {s : MachineData}
    (hw : w = 32 ∨ w = 64)
    (hcmp : _root_.Program.wp (emitClean [cmpIns]) (fun sx =>
      sx.status = StatusFlags.subs (x - y) x y ∧ sx.dmem = s.dmem ∧
      armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s)
    (hres : cond.interp (StatusFlags.subs (x - y) x y) = res)
    (hfin : armCmpFinish cmpIns cond dst = some (c, clob)) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst res ∧
      FlagCmpOk armMach armGpr s' x y false ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (dst.gprs ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  have hfc : ∀ {sx : MachineData}, sx.status = StatusFlags.subs (x - y) x y →
      FlagCmpOk armMach armGpr sx x y false := by
    intro sx hst co cnd _ hco
    cases hco; dsimp only [Machine.evalCond, armMach]; rw [hst]
    exact armCmpCond_subs hw co x y
  cases dst with
  | vec v => exact v.elim
  | flag cf =>
    dsimp only [armCmpFinish] at hfin; split at hfin
    · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      rcases Option.some.inj hfin with ⟨rfl, rfl⟩
      refine armWp_mono hcmp ?_; rintro sx ⟨hst, hdm, hfr⟩
      exact ⟨by simpa [Machine.PDstHolds, Machine.evalCond, hst] using hres, hfc hst, hdm, hfr⟩
    · cases hfin
  | gpr r => cases r with
    | SP => cases hfin
    | reg d =>
      rcases Option.some.inj hfin with ⟨rfl, rfl⟩
      rw [emitClean_cons, emitClean_cons, emitClean_nil]
      refine armWp_cons (by simpa [emitClean_cons, emitClean_nil] using hcmp) ?_
      rintro sx ⟨hst, hdm, hfr⟩
      refine armWp_mono (armCset64_wp d cond sx) ?_; rintro sy rfl
      refine ⟨?_, hfc hst, hdm, armFrame_nzcv fun r hr => ?_⟩
      · have hcc : cond.interp sx.status = res := by rw [hst]; exact hres
        simp only [Machine.PDstHolds, GprHolds, get_wr_same, hcc]; cases res <;> rfl
      · have hne : r ≠ .reg d ∧ r ∉ armScratch :=
          ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
        rw [get_wr_of_ne sx d _ r hne.1]; exact hfr.1 r hne.2

private theorem armShiftedCmpInstr_wp [Host] (rw : RegWidth) (baseR shiftR : XReg)
    (sh : ArmShiftOp) (k : Nat) (hk : k < rw.bits) (s : MachineData) :
    _root_.Program.wp (emitClean [armShiftedCmpInstrI rw baseR shiftR sh k])
      (fun sx =>
        let va := (s.regs.getXReg baseR).toBitVec.setWidth rw.bits
        let vb := sh.eval ((s.regs.getXReg shiftR).toBitVec.setWidth rw.bits) k
        sx.status = StatusFlags.subs (va - vb) va vb ∧ sx.dmem = s.dmem ∧
        armMach.Frame armCondReads s sx armScratch [] maskNZCV)
      (fun _ _ => False) s := by
  have hk64 : k < 2 ^ 63 := Nat.lt_trans hk (by cases rw <;> decide)
  have hamt : (Int64.ofNat k).toInt.toNat = k := by
    rw [Int64.toInt_ofNat_of_lt hk64, Int.toNat_natCast]
  rw [emitClean_cons, emitClean_nil]
  cases rw <;> cases sh
  · exact armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk' => by
      simp only [armShiftedCmpInstrI, armIselInsI, t_step_simp, Reg64s.setRegOrZr_xzr,
        armShiftRegExpr, ArmShiftOp.toKraken, RegWidth.bits, MemWidth.bits, hamt]
      exact hk' _ rfl) rfl
      (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone))
      (fun _ ⟨_, hst, hdm, hfr⟩ => ⟨hst, hdm, hfr⟩)
  · exact armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk' => by
      simp only [armShiftedCmpInstrI, armIselInsI, t_step_simp, Reg64s.setRegOrZr_xzr,
        armShiftRegExpr, ArmShiftOp.toKraken, RegWidth.bits, MemWidth.bits, hamt]
      exact hk' _ rfl) rfl
      (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone))
      (fun _ ⟨_, hst, hdm, hfr⟩ => ⟨hst, hdm, hfr⟩)
  · exact armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk' => by
      simp only [armShiftedCmpInstrI, armIselInsI, t_step_simp, Reg64s.setRegOrZr_xzr,
        armShiftRegExpr, ArmShiftOp.toKraken, RegWidth.bits, MemWidth.bits, hamt]
      exact hk' _ rfl) rfl
      (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone))
      (fun _ ⟨_, hst, hdm, hfr⟩ => ⟨hst, hdm, hfr⟩)
  · exact armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk' => by
      simp only [armShiftedCmpInstrI, armIselInsI, t_step_simp, Reg64s.setRegOrZr_xzr,
        armShiftRegExpr, ArmShiftOp.toKraken, RegWidth.bits, MemWidth.bits,
        BitVec.setWidth_eq, hamt]
      exact hk' _ rfl) rfl
      (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone))
      (fun _ ⟨_, hst, hdm, hfr⟩ => ⟨hst, hdm, hfr⟩)
  · exact armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk' => by
      simp only [armShiftedCmpInstrI, armIselInsI, t_step_simp, Reg64s.setRegOrZr_xzr,
        armShiftRegExpr, ArmShiftOp.toKraken, RegWidth.bits, MemWidth.bits,
        BitVec.setWidth_eq, hamt]
      exact hk' _ rfl) rfl
      (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone))
      (fun _ ⟨_, hst, hdm, hfr⟩ => ⟨hst, hdm, hfr⟩)
  · exact armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk' => by
      simp only [armShiftedCmpInstrI, armIselInsI, t_step_simp, Reg64s.setRegOrZr_xzr,
        armShiftRegExpr, ArmShiftOp.toKraken, RegWidth.bits, MemWidth.bits,
        BitVec.setWidth_eq, hamt]
      exact hk' _ rfl) rfl
      (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone))
      (fun _ ⟨_, hst, hdm, hfr⟩ => ⟨hst, hdm, hfr⟩)

/-- Label-freedom for `armShiftedCmp?`. -/
theorem armShiftedCmp_noLab {o : CmpOp} {w : Nat} {ra rb : Reg} {sh : ArmShiftOp} {k : Nat}
    {lhsShift : Bool} {dst : PDst Reg Empty ArmCond .bool}
    {dirs : List Directive} {clob : FlagMask}
    (h : armShiftedCmp? o w ra rb sh k lhsShift dst = some (dirs, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ dirs :=
  emitCleanPair_noLab h l

/-- Full WP theorem for `armShiftedCmp?`, proving boolean destination semantics + `FlagCmpOk`. -/
theorem armShiftedCmp_wp [Host] {o : CmpOp} {w : Nat} {ra rb : Reg} {sh : ArmShiftOp} {k : Nat}
    {lhsShift : Bool} {dst : PDst Reg Empty ArmCond .bool}
    {dirs : List Directive} {clob : FlagMask}
    (hins : armShiftedCmp? o w ra rb sh k lhsShift dst = some (dirs, clob))
    {s : MachineData} {va vb : BitVec w}
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits w) vb) :
    let lhs := if lhsShift then sh.eval va k else va
    let rhs := if lhsShift then vb else sh.eval vb k
    _root_.Program.wp dirs
      (fun s' =>
        armMach.PDstHolds s' .bool dst (o.evalBits lhs rhs) ∧
        (∀ {lf}, armShiftedCmpFlagsOut o w lhsShift dst = some lf →
          FlagCmpOk armMach armGpr s' (if lf then lhs else rhs) (if lf then rhs else lhs) false) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (dst.gprs ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp hins
  dsimp only [armShiftedCmpIns] at hci
  split at hci
  · cases hci
  · rename_i hklt
    have hk : k < w := by simpa [Nat.blt_eq] using hklt
    cases hw : armShiftWidth? w with
    | none => simp [hw] at hci
    | some rw =>
      rcases armShiftWidth?_eq hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases ra with
        | SP => simp [hw, armRegX?] at hci
        | reg a =>
          cases rb with
          | SP => simp [hw, armRegX?] at hci
          | reg b =>
            simp only [hw, armRegX?] at hci
            have ha' : (s.regs.getXReg a).toBitVec.setWidth 32 = va := by
              simpa [armMach, get_reg, GprHolds] using ha.2
            have hb' : (s.regs.getXReg b).toBitVec.setWidth 32 = vb := by
              simpa [armMach, get_reg, GprHolds] using hb.2
            cases lhsShift
            · dsimp only [Bool.false_eq_true, ↓reduceIte] at hci ⊢
              have hwp := armCmpFinish_wp (Or.inl rfl)
                (armShiftedCmpInstr_wp .W32 a b sh k hk s)
                (armCmpCond_subs (Or.inl rfl) o _ _) hci
              rw [ha', hb'] at hwp
              refine armWp_mono hwp ?_
              rintro s' ⟨hpd, hfc, hdm, hfr⟩
              refine ⟨hpd, fun {lf} hfl => ?_, hdm, hfr⟩
              cases dst with
              | vec v => exact v.elim
              | gpr r => cases r <;> simp [armShiftedCmpFlagsOut] at hfl; subst hfl; exact hfc
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o) = true
                · simp [armShiftedCmpFlagsOut, hcf] at hfl; subst hfl; exact hfc
                · simp [armShiftedCmpFlagsOut, hcf] at hfl
            · simp only [↓reduceIte] at hci ⊢
              have hwp := armCmpFinish_wp (Or.inl rfl)
                (armShiftedCmpInstr_wp .W32 b a sh k hk s)
                (by rw [armCmpCond_subs (Or.inl rfl), CmpOp.swap_evalBits]) hci
              rw [ha', hb'] at hwp
              refine armWp_mono hwp ?_
              rintro s' ⟨hpd, hfc, hdm, hfr⟩
              refine ⟨hpd, fun {lf} hfl => ?_, hdm, hfr⟩
              cases dst with
              | vec v => exact v.elim
              | gpr r => cases r <;> simp [armShiftedCmpFlagsOut] at hfl; subst hfl; exact hfc
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o.swap) = true
                · simp [armShiftedCmpFlagsOut, hcf] at hfl; subst hfl; exact hfc
                · simp [armShiftedCmpFlagsOut, hcf] at hfl
      · cases ra with
        | SP => simp [hw, armRegX?] at hci
        | reg a =>
          cases rb with
          | SP => simp [hw, armRegX?] at hci
          | reg b =>
            simp only [hw, armRegX?] at hci
            have ha' : (s.regs.getXReg a).toBitVec.setWidth 64 = va := by
              simpa [armMach, get_reg, GprHolds] using ha.2
            have hb' : (s.regs.getXReg b).toBitVec.setWidth 64 = vb := by
              simpa [armMach, get_reg, GprHolds] using hb.2
            cases lhsShift
            · dsimp only [Bool.false_eq_true, ↓reduceIte] at hci ⊢
              have hwp := armCmpFinish_wp (Or.inr rfl)
                (armShiftedCmpInstr_wp .W64 a b sh k hk s)
                (armCmpCond_subs (Or.inr rfl) o _ _) hci
              rw [ha', hb'] at hwp
              refine armWp_mono hwp ?_
              rintro s' ⟨hpd, hfc, hdm, hfr⟩
              refine ⟨hpd, fun {lf} hfl => ?_, hdm, hfr⟩
              cases dst with
              | vec v => exact v.elim
              | gpr r => cases r <;> simp [armShiftedCmpFlagsOut] at hfl; subst hfl; exact hfc
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o) = true
                · simp [armShiftedCmpFlagsOut, hcf] at hfl; subst hfl; exact hfc
                · simp [armShiftedCmpFlagsOut, hcf] at hfl
            · simp only [↓reduceIte] at hci ⊢
              have hwp := armCmpFinish_wp (Or.inr rfl)
                (armShiftedCmpInstr_wp .W64 b a sh k hk s)
                (by rw [armCmpCond_subs (Or.inr rfl), CmpOp.swap_evalBits]) hci
              rw [ha', hb'] at hwp
              refine armWp_mono hwp ?_
              rintro s' ⟨hpd, hfc, hdm, hfr⟩
              refine ⟨hpd, fun {lf} hfl => ?_, hdm, hfr⟩
              cases dst with
              | vec v => exact v.elim
              | gpr r => cases r <;> simp [armShiftedCmpFlagsOut] at hfl; subst hfl; exact hfc
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o.swap) = true
                · simp [armShiftedCmpFlagsOut, hcf] at hfl; subst hfl; exact hfc
                · simp [armShiftedCmpFlagsOut, hcf] at hfl

/-- `FallsTo` specification for `armShiftedCmp?`. -/
theorem armShiftedCmp_spec (h : Host) {steps : Nat} {o : CmpOp} {w : Nat}
    (ra rb : Reg) (sh : ArmShiftOp) (k : Nat) (lhsShift : Bool)
    (dst : PDst Reg Empty ArmCond .bool) (dirs : List Directive) (clob : FlagMask)
    (hins : armShiftedCmp? o w ra rb sh k lhsShift dst = some (dirs, clob))
    (s : MachineData) (va vb : BitVec w)
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits w) vb)
    (post : MachineState → Prop) :
    let lhs := if lhsShift then sh.eval va k else va
    let rhs := if lhsShift then vb else sh.eval vb k
    armMach.FallsTo armCondReads h steps dirs (dst.gprs ++ armScratch) [] clob s
      (fun s' =>
        armMach.PDstHolds s' .bool dst (o.evalBits lhs rhs) ∧
        (∀ {lf}, armShiftedCmpFlagsOut o w lhsShift dst = some lf →
          FlagCmpOk armMach armGpr s' (if lf then lhs else rhs) (if lf then rhs else lhs) false) ∧
        armMach.mem s' = armMach.mem s)
      post := by
  letI := h
  refine armFallsTo_of_wp (armWp_mono (armShiftedCmp_wp hins ha hb) ?_)
  rintro s' ⟨hpd, hfc, hdm, hfr⟩
  exact ⟨⟨hpd, hfc, hdm⟩, hfr⟩

/-! ## 3. Extended-Register Semantics & `ADD_e`/`SUB_e`/`SUBS_e` Correctness -/

private theorem armExtShiftAmount?_eq {k : Nat} {amt : ExtendAmount}
    (h : armExtShiftAmount? k = some amt) :
    (k = 0 ∧ amt = .E0) ∨ (k = 1 ∧ amt = .E1) ∨ (k = 2 ∧ amt = .E2) ∨
    (k = 3 ∧ amt = .E3) ∨ (k = 4 ∧ amt = .E4) := by
  rcases k with _ | _ | _ | _ | _ | k <;> simp only [armExtShiftAmount?] at h
  · cases h; exact Or.inl ⟨rfl, rfl⟩
  · cases h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · cases h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · cases h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · cases h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · contradiction

private theorem ofInt_apply_extend (rw : RegWidth) (rb : XReg) (e : ArmExtType)
    (k : Nat) {amt : ExtendAmount} (hamt : armExtShiftAmount? k = some amt)
    (regs : Reg64s) (mem : Std.Rco Int64) :
    BitVec.ofInt rw.bits ((armExtRegExpr rb e amt).interp regs mem) =
      e.eval ((regs.getXReg rb).toBitVec.setWidth e.srcBits) k := by
  have hk_eq := armExtShiftAmount?_eq hamt
  have hshl1 : ∀ (z : Int) (m : Nat),
      BitVec.ofInt rw.bits (z * (2 ^ m : Nat)) = BitVec.ofInt rw.bits z <<< m := by
    intro z m
    rw [BitVec.ofInt_mul, BitVec.ofInt_natCast,
      show (BitVec.ofNat rw.bits (2 ^ m)) = 1#rw.bits <<< m from by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]]
    apply BitVec.eq_of_toNat_eq
    rcases rw with _ | _ <;> simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hshl : ∀ (z : Int) (m : Nat),
      BitVec.ofInt rw.bits (z <<< m) = BitVec.ofInt rw.bits z <<< m := by
    intro z m
    rw [Int.shiftLeft_eq, show (2 : Int) ^ m = ((2 ^ m : Nat) : Int) from by simp, hshl1]
  have hunsigned : ∀ {n : Nat} (hn : n ≤ rw.bits) (x : BitVec n),
      BitVec.ofInt rw.bits x.unsigned = x.zeroExtend rw.bits := by
    intro n hn x
    rw [BitVec.unsigned, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    have hx := x.isLt
    have hpow : 2 ^ n ≤ 2 ^ rw.bits := Nat.pow_le_pow_right (by decide) hn
    simp [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx hpow)]
  have hsigned : ∀ {n : Nat} (hn : n ≤ rw.bits) (x : BitVec n),
      BitVec.ofInt rw.bits x.signed = x.signExtend rw.bits := fun hn x => by
    have hx : x.signed = (x.signExtend rw.bits).signed := by
      rw [BitVec.signed, BitVec.signed, BitVec.toInt_signExtend_of_le hn]
    rw [hx, BitVec.signed, BitVec.ofInt_toInt]
  have hextr : ∀ (n : Nat) (x : BitVec 64), BitVec.extractLsb' 0 n x = x.setWidth n := by
    intro n x; apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']
  have hreg64 : regs.getRegOrZr64 (zr rb .W32).base = regs.getXReg rb := rfl
  cases rw <;> rcases hk_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases e <;>
    (simp only [ExtRegExpr.interp, BitVec.apply_extend, armExtRegExpr, ArmExtType.toKraken,
       ArmExtType.eval, ArmExtType.srcBits, ArmExtType.isSigned, hreg64,
       BitVec.take, hextr, MemWidth.bits, Bool.false_eq_true, ↓reduceIte];
     try rw [hshl]) <;>
    first
      | (rw [hunsigned (by decide)] <;> simp)
      | (rw [hsigned (by decide)] <;> simp)

private theorem armExtAluDir_wp [Host] (op : ArmExtAluOp) (rw : RegWidth)
    (rd ra rb : XReg) (e : ArmExtType) (k : Nat) {amt : ExtendAmount}
    (hamt : armExtShiftAmount? k = some amt) (s : MachineData) :
    _root_.Program.wp [armExtAluDirI op rw rd ra rb e amt]
      (fun s' =>
        let va := (s.regs.getXReg ra).toBitVec.setWidth rw.bits
        let vb : BitVec rw.bits := e.eval ((s.regs.getXReg rb).toBitVec.setWidth e.srcBits) k
        s' = wr s rd ((op.eval va vb).setWidth 64))
      (fun _ _ => False) s := by
  cases rw <;> cases op
  · exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      have he := ofInt_apply_extend .W32 rb e k hamt s.regs p
      simp only [armExtAluDirI, armExtAluInstrI, t_step_simp, RegWidth.bits, MemWidth.bits]
        at he ⊢
      rw [he]; exact hk _ (by simp [ArmExtAluOp.eval, wr])
  · exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      have he := ofInt_apply_extend .W32 rb e k hamt s.regs p
      simp only [armExtAluDirI, armExtAluInstrI, t_step_simp, RegWidth.bits, MemWidth.bits]
        at he ⊢
      rw [he]; exact hk _ (by simp [ArmExtAluOp.eval, wr])
  · exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      have he := ofInt_apply_extend .W64 rb e k hamt s.regs p
      simp only [armExtAluDirI, armExtAluInstrI, t_step_simp, RegWidth.bits, MemWidth.bits,
        BitVec.setWidth_eq] at he ⊢
      rw [he]; exact hk _ (by simp [ArmExtAluOp.eval, wr])
  · exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      have he := ofInt_apply_extend .W64 rb e k hamt s.regs p
      simp only [armExtAluDirI, armExtAluInstrI, t_step_simp, RegWidth.bits, MemWidth.bits,
        BitVec.setWidth_eq] at he ⊢
      rw [he]; exact hk _ (by simp [ArmExtAluOp.eval, wr])

private theorem armExtAluOfOpCode_wp_of {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]} {op : ArmExtAluOp}
    (hc : armExtAluOfOpCode? c = some op)
    {va vb : BitVec w} {post : BitVec w → Prop} (hp : post (op.eval va vb)) :
    c.wp (va, vb, ()) (fun (res, ()) => post res) := by
  cases c with
  | add _ => simp [armExtAluOfOpCode?] at hc; subst hc
             simpa [OpCode.wp, lift2, ArmExtAluOp.eval] using hp
  | sub _ => simp [armExtAluOfOpCode?] at hc; subst hc
             simpa [OpCode.wp, lift2, ArmExtAluOp.eval] using hp
  | _     => simp [armExtAluOfOpCode?] at hc

/-- Label-freedom for `armExtAlu?`. -/
theorem armExtAlu_noLab {w : Nat} {c : OpCode [.bits w, .bits w] [.bits w]}
    {ra rb : Reg} {e : ArmExtType} {k : Nat} {rd : Reg}
    {dirs : List Directive} {clob : FlagMask}
    (h : armExtAlu? w c ra rb e k rd = some (dirs, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ dirs :=
  emitCleanPair_noLab h l

/-- Full WP theorem for `armExtAlu?` with `GprHoldsZ` and `rd :: armScratch` framing. -/
theorem armExtAlu_wp [Host] {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]} {op : ArmExtAluOp}
    {ra rb : Reg} {e : ArmExtType} {k : Nat} {rd : Reg}
    {dirs : List Directive} {clob : FlagMask}
    (hins : armExtAlu? w c ra rb e k rd = some (dirs, clob))
    (hop : armExtAluOfOpCode? c = some op)
    {s : MachineData} {va : BitVec w} {vb : BitVec e.srcBits}
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits e.srcBits) vb) :
    _root_.Program.wp dirs
      (fun s' =>
        GprHoldsZ (armMach.getGpr s' rd) w (op.eval va (e.eval vb k)) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (rd :: armScratch) [] clob)
      (fun _ _ => False) s := by
  unfold armExtAlu? armExtAluIns at hins
  rcases emitCleanPair_eq_some.mp hins with ⟨raw, hraw, rfl⟩
  simp only [Option.map_eq_some_iff] at hraw
  rcases hraw with ⟨insList, hinsList, hpair⟩
  cases hpair
  cases hw : armShiftWidth? w with
  | none => simp [hw] at hinsList
  | some rw =>
    cases hop' : armExtAluOfOpCode? c with
    | none => simp [hw, hop'] at hinsList
    | some op' =>
      rw [hop] at hop'; cases hop'
      cases hamt : armExtShiftAmount? k with
      | none => simp [hw, hop, hamt] at hinsList
      | some amt =>
        cases rd with
        | SP => simp [hw, hop, hamt, armRegX?] at hinsList
        | reg d =>
          cases ra with
          | SP => simp [hw, hop, hamt, armRegX?] at hinsList
          | reg a =>
            cases rb with
            | SP => simp [hw, hop, hamt, armRegX?] at hinsList
            | reg b =>
              simp [hw, hop, hamt, armRegX?] at hinsList
              subst hinsList
              rcases armShiftWidth?_eq hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · have hw64 : RegWidth.bits .W32 ≤ 64 := by decide
                have hva : (s.regs.getXReg a).toBitVec.setWidth 32 = va := by
                  simpa [armMach, get_reg, GprHolds] using ha.2
                have hvb : (s.regs.getXReg b).toBitVec.setWidth e.srcBits = vb := by
                  simpa [armMach, get_reg, GprHolds] using hb.2
                have hdir := armExtAluDir_wp op .W32 d a b e k hamt s
                simp only [hva, hvb, emitClean_cons, emitClean_nil] at hdir ⊢
                exact armWrDst_of_eq hw64 d hdir
                  (setWidth_setWidth64_eq hw64 (op.eval va (e.eval vb k)))
                  (fun _ => rfl)
              · have hw64 : RegWidth.bits .W64 ≤ 64 := by decide
                have hva : (s.regs.getXReg a).toBitVec.setWidth 64 = va := by
                  simpa [armMach, get_reg, GprHolds] using ha.2
                have hvb : (s.regs.getXReg b).toBitVec.setWidth e.srcBits = vb := by
                  simpa [armMach, get_reg, GprHolds] using hb.2
                have hdir := armExtAluDir_wp op .W64 d a b e k hamt s
                simp only [hva, hvb, emitClean_cons, emitClean_nil] at hdir ⊢
                exact armWrDst_of_eq hw64 d hdir
                  (setWidth_setWidth64_eq hw64 (op.eval va (e.eval vb k)))
                  (fun _ => rfl)

private theorem armExtAlu_hasOp {w : Nat}
    {c : OpCode [.bits w, .bits w] [.bits w]}
    {ra rb : Reg} {e : ArmExtType} {k : Nat} {rd : Reg}
    {dirs : List Directive} {clob : FlagMask}
    (hins : armExtAlu? w c ra rb e k rd = some (dirs, clob)) :
    ∃ op, armExtAluOfOpCode? c = some op := by
  unfold armExtAlu? armExtAluIns at hins
  rcases emitCleanPair_eq_some.mp hins with ⟨_, hraw, _⟩
  simp only [Option.map_eq_some_iff] at hraw
  rcases hraw with ⟨_, hinsList, _⟩
  cases hop' : armExtAluOfOpCode? c with
  | some op => exact ⟨op, rfl⟩
  | none => cases armShiftWidth? w <;> simp [hop'] at hinsList

/-- `FallsTo` specification for `armExtAlu?` against `OpCode.wp`. -/
theorem armExtAlu_spec (h : Host) {steps : Nat} {w : Nat}
    (c : OpCode [.bits w, .bits w] [.bits w])
    (ra rb : Reg) (e : ArmExtType) (k : Nat) (rd : Reg)
    (dirs : List Directive) (clob : FlagMask)
    (hins : armExtAlu? w c ra rb e k rd = some (dirs, clob))
    (s : MachineData) (va : BitVec w) (vb : BitVec e.srcBits)
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits e.srcBits) vb)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h steps dirs (rd :: armScratch) [] clob s
      (fun s' =>
        c.wp (va, e.eval vb k, ()) (fun (res, ()) =>
          GprHolds (armMach.getGpr s' rd) (.bits w) res) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (rd :: armScratch) [] clob)
      post := by
  rcases armExtAlu_hasOp hins with ⟨op, hop⟩
  apply armFallsTo_of_wp
  refine armWp_mono (@armExtAlu_wp h w c op ra rb e k rd dirs clob hins hop s va vb ha hb) ?_
  intro s' ⟨hhold, hmem, hfr⟩
  exact ⟨⟨armExtAluOfOpCode_wp_of hop
    (post := fun res => GprHolds (armMach.getGpr s' rd) (.bits w) res) hhold.holds,
    hmem, hfr⟩, hfr⟩

/-- Zero-extending `FallsTo` specification for 32-bit `armExtAlu?`. -/
theorem armExtAlu_zero32 (h : Host) {steps : Nat}
    (c : OpCode [.bits 32, .bits 32] [.bits 32])
    (ra rb : Reg) (e : ArmExtType) (k : Nat) (rd : Reg)
    (dirs : List Directive) (clob : FlagMask)
    (hins : armExtAlu? 32 c ra rb e k rd = some (dirs, clob))
    (s : MachineData) (va : BitVec 32) (vb : BitVec e.srcBits)
    (ha : GprHolds (armMach.getGpr s ra) (.bits 32) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits e.srcBits) vb)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h steps dirs (rd :: armScratch) [] clob s
      (fun s' =>
        c.wp (va, e.eval vb k, ()) (fun (res, ()) =>
          armMach.getGpr s' rd = res.setWidth 64) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (rd :: armScratch) [] clob)
      post := by
  rcases armExtAlu_hasOp hins with ⟨op, hop⟩
  apply armFallsTo_of_wp
  refine armWp_mono (@armExtAlu_wp h 32 c op ra rb e k rd dirs clob hins hop s va vb ha hb) ?_
  intro s' ⟨hhold, hmem, hfr⟩
  exact ⟨⟨armExtAluOfOpCode_wp_of hop
    (post := fun res => armMach.getGpr s' rd = res.setWidth 64) hhold.zero32,
    hmem, hfr⟩, hfr⟩

private theorem armExtCmpInstr_wp [Host] (rw : RegWidth) (baseR extR : XReg)
    (e : ArmExtType) (k : Nat) {amt : ExtendAmount} (hamt : armExtShiftAmount? k = some amt)
    (s : MachineData) :
    _root_.Program.wp (emitClean [armExtCmpInstrI rw baseR extR e amt])
      (fun sx =>
        let va := (s.regs.getXReg baseR).toBitVec.setWidth rw.bits
        let vb : BitVec rw.bits := e.eval ((s.regs.getXReg extR).toBitVec.setWidth e.srcBits) k
        sx.status = StatusFlags.subs (va - vb) va vb ∧ sx.dmem = s.dmem ∧
        armMach.Frame armCondReads s sx armScratch [] maskNZCV)
      (fun _ _ => False) s := by
  rw [emitClean_cons, emitClean_nil]
  cases rw
  · exact armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk' => by
      have hext := ofInt_apply_extend .W32 extR e k hamt s.regs p
      simp only [armExtCmpInstrI, armIselInsI, t_step_simp, Reg64s.setRegOrZr_xzr,
        RegWidth.bits, MemWidth.bits] at hext ⊢
      rw [hext]; exact hk' _ rfl) rfl
      (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone))
      (fun _ ⟨_, hst, hdm, hfr⟩ => ⟨hst, hdm, hfr⟩)
  · exact armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk' => by
      have hext := ofInt_apply_extend .W64 extR e k hamt s.regs p
      simp only [armExtCmpInstrI, armIselInsI, t_step_simp, Reg64s.setRegOrZr_xzr,
        RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq] at hext ⊢
      rw [hext]; exact hk' _ rfl) rfl
      (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone))
      (fun _ ⟨_, hst, hdm, hfr⟩ => ⟨hst, hdm, hfr⟩)

/-- Label-freedom for `armExtCmp?`. -/
theorem armExtCmp_noLab {o : CmpOp} {w : Nat} {ra rb : Reg} {e : ArmExtType} {k : Nat}
    {lhsExt : Bool} {dst : PDst Reg Empty ArmCond .bool}
    {dirs : List Directive} {clob : FlagMask}
    (h : armExtCmp? o w ra rb e k lhsExt dst = some (dirs, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ dirs :=
  emitCleanPair_noLab h l

/-- Full WP theorem for `armExtCmp?`, proving boolean destination semantics + `FlagCmpOk`. -/
theorem armExtCmp_wp [Host] {o : CmpOp} {w : Nat} {ra rb : Reg} {e : ArmExtType} {k : Nat}
    {lhsExt : Bool} {dst : PDst Reg Empty ArmCond .bool}
    {dirs : List Directive} {clob : FlagMask}
    (hins : armExtCmp? o w ra rb e k lhsExt dst = some (dirs, clob))
    {s : MachineData} {vBase : BitVec w} {vExt : BitVec e.srcBits}
    (hBase : GprHolds (armMach.getGpr s (if lhsExt then rb else ra)) (.bits w) vBase)
    (hExt : GprHolds (armMach.getGpr s (if lhsExt then ra else rb)) (.bits e.srcBits) vExt) :
    let lhs : BitVec w := if lhsExt then e.eval vExt k else vBase
    let rhs : BitVec w := if lhsExt then vBase else e.eval vExt k
    _root_.Program.wp dirs
      (fun s' =>
        armMach.PDstHolds s' .bool dst (o.evalBits lhs rhs) ∧
        (∀ {lf}, armExtCmpFlagsOut o w lhsExt dst = some lf →
          FlagCmpOk armMach armGpr s' (if lf then lhs else rhs) (if lf then rhs else lhs) false) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (dst.gprs ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp hins
  dsimp only [armExtCmpIns] at hci
  cases hw : armShiftWidth? w with
  | none => simp [hw] at hci
  | some rw =>
    cases hamt : armExtShiftAmount? k with
    | none => simp [hw, hamt] at hci
    | some amt =>
      cases ra with
      | SP => simp [hw, hamt, armRegX?] at hci
      | reg a =>
        cases rb with
        | SP => simp [hw, hamt, armRegX?] at hci
        | reg b =>
          simp only [hw, hamt, armRegX?] at hci
          rcases armShiftWidth?_eq hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · cases lhsExt
            · dsimp only [Bool.false_eq_true, ↓reduceIte] at hci hBase hExt ⊢
              have ha' : (s.regs.getXReg a).toBitVec.setWidth 32 = vBase := by
                simpa [armMach, get_reg, GprHolds] using hBase.2
              have hb' : (s.regs.getXReg b).toBitVec.setWidth e.srcBits = vExt := by
                simpa [armMach, get_reg, GprHolds] using hExt.2
              have hwp := armCmpFinish_wp (Or.inl rfl)
                (armExtCmpInstr_wp .W32 a b e k hamt s)
                (armCmpCond_subs (Or.inl rfl) o _ _) hci
              rw [ha', hb'] at hwp
              refine armWp_mono hwp ?_
              rintro s' ⟨hpd, hfc, hdm, hfr⟩
              refine ⟨hpd, fun {lf} hfl => ?_, hdm, hfr⟩
              cases dst with
              | vec v => exact v.elim
              | gpr r => cases r <;> simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut] at hfl
                         subst hfl; exact hfc
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o) = true
                · simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut, hcf] at hfl
                  subst hfl; exact hfc
                · simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut, hcf] at hfl
            · simp only [↓reduceIte] at hci hBase hExt ⊢
              have ha' : (s.regs.getXReg a).toBitVec.setWidth e.srcBits = vExt := by
                simpa [armMach, get_reg, GprHolds] using hExt.2
              have hb' : (s.regs.getXReg b).toBitVec.setWidth 32 = vBase := by
                simpa [armMach, get_reg, GprHolds] using hBase.2
              have hwp := armCmpFinish_wp (Or.inl rfl)
                (armExtCmpInstr_wp .W32 b a e k hamt s)
                (by rw [armCmpCond_subs (Or.inl rfl), CmpOp.swap_evalBits]) hci
              rw [ha', hb'] at hwp
              refine armWp_mono hwp ?_
              rintro s' ⟨hpd, hfc, hdm, hfr⟩
              refine ⟨hpd, fun {lf} hfl => ?_, hdm, hfr⟩
              cases dst with
              | vec v => exact v.elim
              | gpr r => cases r <;> simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut] at hfl
                         subst hfl; exact hfc
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o.swap) = true
                · simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut, hcf] at hfl
                  subst hfl; exact hfc
                · simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut, hcf] at hfl
          · cases lhsExt
            · dsimp only [Bool.false_eq_true, ↓reduceIte] at hci hBase hExt ⊢
              have ha' : (s.regs.getXReg a).toBitVec.setWidth 64 = vBase := by
                simpa [armMach, get_reg, GprHolds] using hBase.2
              have hb' : (s.regs.getXReg b).toBitVec.setWidth e.srcBits = vExt := by
                simpa [armMach, get_reg, GprHolds] using hExt.2
              have hwp := armCmpFinish_wp (Or.inr rfl)
                (armExtCmpInstr_wp .W64 a b e k hamt s)
                (armCmpCond_subs (Or.inr rfl) o _ _) hci
              rw [ha', hb'] at hwp
              refine armWp_mono hwp ?_
              rintro s' ⟨hpd, hfc, hdm, hfr⟩
              refine ⟨hpd, fun {lf} hfl => ?_, hdm, hfr⟩
              cases dst with
              | vec v => exact v.elim
              | gpr r => cases r <;> simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut] at hfl
                         subst hfl; exact hfc
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o) = true
                · simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut, hcf] at hfl
                  subst hfl; exact hfc
                · simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut, hcf] at hfl
            · simp only [↓reduceIte] at hci hBase hExt ⊢
              have ha' : (s.regs.getXReg a).toBitVec.setWidth e.srcBits = vExt := by
                simpa [armMach, get_reg, GprHolds] using hExt.2
              have hb' : (s.regs.getXReg b).toBitVec.setWidth 64 = vBase := by
                simpa [armMach, get_reg, GprHolds] using hBase.2
              have hwp := armCmpFinish_wp (Or.inr rfl)
                (armExtCmpInstr_wp .W64 b a e k hamt s)
                (by rw [armCmpCond_subs (Or.inr rfl), CmpOp.swap_evalBits]) hci
              rw [ha', hb'] at hwp
              refine armWp_mono hwp ?_
              rintro s' ⟨hpd, hfc, hdm, hfr⟩
              refine ⟨hpd, fun {lf} hfl => ?_, hdm, hfr⟩
              cases dst with
              | vec v => exact v.elim
              | gpr r => cases r <;> simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut] at hfl
                         subst hfl; exact hfc
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o.swap) = true
                · simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut, hcf] at hfl
                  subst hfl; exact hfc
                · simp [armExtCmpFlagsOut, armShiftedCmpFlagsOut, hcf] at hfl

/-- `FallsTo` specification for `armExtCmp?`. -/
theorem armExtCmp_spec (h : Host) {steps : Nat} {o : CmpOp} {w : Nat}
    (ra rb : Reg) (e : ArmExtType) (k : Nat) (lhsExt : Bool)
    (dst : PDst Reg Empty ArmCond .bool) (dirs : List Directive) (clob : FlagMask)
    (hins : armExtCmp? o w ra rb e k lhsExt dst = some (dirs, clob))
    (s : MachineData) (vBase : BitVec w) (vExt : BitVec e.srcBits)
    (hBase : GprHolds (armMach.getGpr s (if lhsExt then rb else ra)) (.bits w) vBase)
    (hExt : GprHolds (armMach.getGpr s (if lhsExt then ra else rb)) (.bits e.srcBits) vExt)
    (post : MachineState → Prop) :
    let lhs : BitVec w := if lhsExt then e.eval vExt k else vBase
    let rhs : BitVec w := if lhsExt then vBase else e.eval vExt k
    armMach.FallsTo armCondReads h steps dirs (dst.gprs ++ armScratch) [] clob s
      (fun s' =>
        armMach.PDstHolds s' .bool dst (o.evalBits lhs rhs) ∧
        (∀ {lf}, armExtCmpFlagsOut o w lhsExt dst = some lf →
          FlagCmpOk armMach armGpr s' (if lf then lhs else rhs) (if lf then rhs else lhs) false) ∧
        armMach.mem s' = armMach.mem s)
      post := by
  letI := h
  refine armFallsTo_of_wp (armWp_mono (armExtCmp_wp hins hBase hExt) ?_)
  rintro s' ⟨hpd, hfc, hdm, hfr⟩
  exact ⟨⟨hpd, hfc, hdm⟩, hfr⟩

end

section ParserChecks

open Kraken.AArch64.Parser

private example : armShiftedAlu? 32 (.add _) (.reg .X0) (.reg .X1) .lsl 0 (.reg .X0) =
    some (⸨prog| add w0, w0, w1, lsl #0 ⸩, maskNone) := by rfl

private example : armShiftedAlu? 32 (.add _) (.reg .X1) (.reg .X2) .lsl 3 (.reg .X0) =
    some (⸨prog| add w0, w1, w2, lsl #3 ⸩, maskNone) := by rfl

private example : armShiftedAlu? 64 (.add _) (.reg .X1) (.reg .X2) .lsl 63 (.reg .X0) =
    some (⸨prog| add x0, x1, x2, lsl #63 ⸩, maskNone) := by rfl

private example : armShiftedAlu? 32 (.sub _) (.reg .X3) (.reg .X4) .lsr 31 (.reg .X5) =
    some (⸨prog| sub w5, w3, w4, lsr #31 ⸩, maskNone) := by rfl

private example : armShiftedAlu? 64 (.sub _) (.reg .X3) (.reg .X4) .asr 17 (.reg .X5) =
    some (⸨prog| sub x5, x3, x4, asr #17 ⸩, maskNone) := by rfl

private example : armShiftedAlu? 32 (.and _) (.reg .X6) (.reg .X7) .lsr 12 (.reg .X8) =
    some (⸨prog| and w8, w6, w7, lsr #12 ⸩, maskNone) := by rfl

private example : armShiftedAlu? 64 (.or _) (.reg .X9) (.reg .X10) .asr 40 (.reg .X11) =
    some (⸨prog| orr x11, x9, x10, asr #40 ⸩, maskNone) := by rfl

private example : armShiftedAlu? 32 (.xor _) (.reg .X12) (.reg .X13) .asr 15 (.reg .X14) =
    some (⸨prog| eor w14, w12, w13, asr #15 ⸩, maskNone) := by rfl

private example :
    ⸨prog|
      subs xzr, x1, x2, lsl #3
      subs wzr, w3, w4, lsr #5
      subs xzr, x6, x5, asr #9
      csinc x0, xzr, xzr, lt
      add x0, x1, w2, uxtw #2
      sub x3, x4, w5, sxtw #1
      add w6, w7, w8, sxtb #0
      sub w9, w10, w11, uxth #4
      subs xzr, x1, w2, sxtw #3
      subs wzr, w4, w3, uxtb #1
      csinc x0, xzr, xzr, eq
    ⸩ =
      (armShiftedCmp? .eq 64 (.reg .X1) (.reg .X2) .lsl 3 false (.flag .eq)).elim [] Prod.fst ++
      (armShiftedCmp? .ult 32 (.reg .X3) (.reg .X4) .lsr 5 false (.flag .cc)).elim [] Prod.fst ++
      (armShiftedCmp? .sle 64 (.reg .X5) (.reg .X6) .asr 9 true
        (.gpr (.reg .X0))).elim [] Prod.fst ++
      (armExtAlu? 64 (.add _) (.reg .X1) (.reg .X2) .uxtw 2 (.reg .X0)).elim [] Prod.fst ++
      (armExtAlu? 64 (.sub _) (.reg .X4) (.reg .X5) .sxtw 1 (.reg .X3)).elim [] Prod.fst ++
      (armExtAlu? 32 (.add _) (.reg .X7) (.reg .X8) .sxtb 0 (.reg .X6)).elim [] Prod.fst ++
      (armExtAlu? 32 (.sub _) (.reg .X10) (.reg .X11) .uxth 4 (.reg .X9)).elim [] Prod.fst ++
      (armExtCmp? .sgt 64 (.reg .X1) (.reg .X2) .sxtw 3 false (.flag .gt)).elim [] Prod.fst ++
      (armExtCmp? .ne 32 (.reg .X3) (.reg .X4) .uxtb 1 true
        (.gpr (.reg .X0))).elim [] Prod.fst := by rfl

end ParserChecks

end LeanQbe.T.Arm64
