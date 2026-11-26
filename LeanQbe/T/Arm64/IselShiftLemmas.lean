module

public import LeanQbe.T.Arm64.IselShift
public import LeanQbe.T.Arm64.IselLemmas2
import Kraken.AArch64.Parser

/-!
# Arm64 Shifted-Register ALU Correctness Proofs

Proves `FallsTo armMach` simulation and 32-bit upper-half zeroing for `armShiftedAlu?`,
plus `ParserChecks` verifying every emitted Kraken instruction matches Arm64 assembly syntax.
-/

public section

namespace LeanQbe.T.Arm64

section

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
    (h : armShiftedAlu? w c ra rb sh k rd = some (dirs, clob)) :
    ∀ d ∈ dirs, ∃ i, d = .instr i := by
  unfold armShiftedAlu? at h
  rcases emitCleanPair_eq_some.mp h with ⟨ci, _, rfl⟩
  intro d hd
  cases ci with
  | nil => simp [emitClean] at hd
  | cons x xs =>
    simp [emitClean] at hd
    rcases hd with rfl | hd
    · exact ⟨x, rfl⟩
    · rcases hd with ⟨a, _, ha⟩; exact ⟨a, ha.symm⟩

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

end ParserChecks

end LeanQbe.T.Arm64
