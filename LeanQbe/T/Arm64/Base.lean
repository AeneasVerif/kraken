module

public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr
public import Kraken.AArch64.OmniSemantics
public import Kraken.AArch64.WP
public import Kraken.AArch64.Sep
public import Kraken.AArch64.Regs
public import LeanQbe.T.Target
public import LeanQbe.T.TargetLemmas
public import LeanQbe.T.StepSimp

/-!
# Shared Kraken AArch64 Target Base (`T-prep`)

Shared directive/register/memory abbreviations, `get`/`wr` register-file accessors, `ArmCond`
(restricting `CondCode` to the 14 invertible conditions), flag masks, `armCondReads`,
`armNegCond`, `armMach : Machine Reg Empty ArmCond Directive`, `keepsFlags_of_bits`, and
`[t_step_simp]` rules for `LeanQbe.T.Arm64.*` (`T8`, `T9`, `T11b`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

/-! ## 1. Directive, register, and addressing abbreviations -/

/-- Architectural GP or stack-pointer register. -/
abbrev Reg := XRegOrSp

/-- AArch64 directive wrapper. -/
abbrev ins {w : RegWidth} (op : Operation w) : Directive :=
  .instr { operation_size := w, operation := op }

/-- `x_r` or `w_r`. -/
abbrev zr (r : XReg) (w : RegWidth) : RegOrZr w := .low (.reg r) w

/-- `xzr` or `wzr`. -/
abbrev xzr (w : RegWidth) : RegOrZr w := .low .XZR w

/-- Immediate `#0` operand for arithmetic instructions. -/
abbrev imm0 : ExtOrImmReg := .imm { imm := .int64 0, shift := .S0 }

/-- Unshifted register operand. -/
abbrev sh {w : RegWidth} (r : XReg) : ShiftRegExpr w :=
  { reg := zr r w, amount := 0, shift := .LSL }

/-- Memory operand `[r]`. -/
abbrev atReg (r : XReg) : AddrExpr :=
  { base := .low (.reg r) .W64, off := .imm { imm := .int64 0, index := none } }

/-- Memory operand `[b, #o]`. -/
abbrev atOff (b : Reg) (o : Nat) : AddrExpr :=
  { base := .low b .W64, off := .imm { imm := .int64 (Int64.ofNat o), index := none } }

/-! ## 2. 64-bit register accessors and update rules -/

/-- Read 64-bit GP or stack register `r`. -/
def get (s : MachineData) (r : Reg) : BitVec 64 :=
  s.regs.getRegOrSp64 r

/-- Write 64-bit GP register `d` in `s`. -/
abbrev wr (s : MachineData) (d : XReg) (v : BitVec 64) : MachineData :=
  { s with regs := s.regs.setXReg d v }

theorem get_reg (s : MachineData) (r : XReg) : get s (.reg r) = (s.regs.getXReg r).toBitVec := rfl

theorem get_sp (s : MachineData) : get s .SP = s.regs.SP.toBitVec := rfl

@[simp] theorem get_wr_same (s : MachineData) (d : XReg) (v : BitVec 64) :
    get (wr s d v) (.reg d) = v := by
  simp [get_reg]

@[simp] theorem get_wr_of_ne (s : MachineData) (d : XReg) (v : BitVec 64) (r : Reg)
    (h : r ≠ .reg d) : get (wr s d v) r = get s r := by
  cases r with
  | SP => simp [get_sp]
  | reg r =>
    have h' : d ≠ r := fun e => h (e ▸ rfl)
    simp [get_reg, Reg64s.getXReg_setXReg_of_ne _ _ _ _ h']

@[grind =] theorem get_wr (s : MachineData) (d : XReg) (v : BitVec 64) (r : Reg) :
    get (wr s d v) r = if r = .reg d then v else get s r := by
  split
  · subst r; exact get_wr_same s d v
  · exact get_wr_of_ne s d v r ‹_›

@[simp] theorem wr_wr_same (s : MachineData) (d : XReg) (v v' : BitVec 64) :
    wr (wr s d v) d v' = wr s d v' := by
  simp [wr]

@[simp] theorem dmem_wr (s : MachineData) (d : XReg) (v : BitVec 64) :
    (wr s d v).dmem = s.dmem := rfl

/-! ## 3. `ArmCond`, clobber masks (`N=0, Z=1, C=2, V=3`), and `armCondReads` -/

/-- The 14 genuine invertible AArch64 NZCV conditions (excluding `AL` and `NV`). -/
inductive ArmCond
  | eq | ne | cs | cc | mi | pl | vs | vc | hi | ls | ge | lt | gt | le
  deriving DecidableEq, Repr, Inhabited, Hashable, Lean.ToExpr

/-- Lower `ArmCond` to Kraken's architectural `CondCode`. -/
def ArmCond.toKraken : ArmCond → CondCode
  | .eq => .EQ | .ne => .NE | .cs => .CS | .cc => .CC
  | .mi => .MI | .pl => .PL | .vs => .VS | .vc => .VC
  | .hi => .HI | .ls => .LS | .ge => .GE | .lt => .LT
  | .gt => .GT | .le => .LE

/-- Evaluate `ArmCond` against architectural `StatusFlags`. -/
@[reducible] def ArmCond.interp (c : ArmCond) (st : StatusFlags) : Bool :=
  c.toKraken.interp st

/-- Logical negation of an `ArmCond`. -/
def armNegCond : ArmCond → ArmCond
  | .eq => .ne | .ne => .eq | .cs => .cc | .cc => .cs
  | .mi => .pl | .pl => .mi | .vs => .vc | .vc => .vs
  | .hi => .ls | .ls => .hi | .ge => .lt | .lt => .ge
  | .gt => .le | .le => .gt

def maskNone : FlagMask := 0x00#8
def maskN    : FlagMask := 0x01#8
def maskZ    : FlagMask := 0x02#8
def maskC    : FlagMask := 0x04#8
def maskV    : FlagMask := 0x08#8
def maskNZCV : FlagMask := 0x0F#8
def maskAll  : FlagMask := 0xFF#8

/-- Status flags read by each `ArmCond`. -/
def armCondReads : ArmCond → FlagMask
  | .eq | .ne => maskZ
  | .cs | .cc => maskC
  | .mi | .pl => maskN
  | .vs | .vc => maskV
  | .hi | .ls => maskC ||| maskZ
  | .ge | .lt => maskN ||| maskV
  | .gt | .le => maskZ ||| maskN ||| maskV

theorem armNegCond_interp (c : ArmCond) (st : StatusFlags) :
    (armNegCond c).interp st = !c.interp st := by
  rcases st with ⟨n, z, c', v⟩
  cases c <;> cases n <;> cases z <;> cases c' <;> cases v <;> rfl

theorem armNegCond_reads (c : ArmCond) :
    armCondReads (armNegCond c) = armCondReads c := by
  cases c <;> rfl

/-! ## 4. Scratch registers, `armMach`, and flag framing -/

/-- Scratch registers reserved for AArch64 lowering (`x16`, `x17`). -/
@[reducible] def armScratch : List Reg := [.reg .X16, .reg .X17]

/-- Single-step relation of a laid-out Kraken AArch64 host program. -/
def hostStep (h : Host) : MachineState → (MachineState → Prop) → Prop :=
  letI := h; step1 Host.exe

/-- Address resolved for label `l` in Kraken AArch64 host `h`. -/
def hostLabel (h : Host) (l : Label) : Int64 :=
  letI := h; Labels.label l

/-- Kraken AArch64 packaged as a `LeanQbe.T.Machine`. -/
@[reducible] def armMach : Machine Reg Empty ArmCond Directive where
  MData := MachineData
  Addr := Int64
  State := MachineState
  Host := Host
  getGpr := get
  getVec _ v := v.elim
  evalCond s c := c.interp s.status
  mem s := s.dmem
  mkState s a := ⟨s, a⟩
  pc st := st.pc
  data st := st.data
  pc_mk _ _ := rfl
  data_mk _ _ := rfl
  mk_eta _ := rfl
  prog h := @Host.prog h
  addrOf h k := @Host.addrOf h k
  labelAddr := hostLabel
  step := hostStep

private theorem flag_bit_clear {m clob : FlagMask} {b : Nat}
    (hm : m.getLsbD b = true) (hdisj : FlagMask.disjoint m clob = true) :
    clob.getLsbD b = false := by
  have h0 : (m &&& clob).getLsbD b = false := by
    simp only [FlagMask.disjoint, beq_iff_eq] at hdisj
    rw [hdisj]; simp
  simpa [BitVec.getLsbD_and, hm] using h0

/-- Bit-level sufficient condition for `armMach.UpdFlags armCondReads`. -/
theorem keepsFlags_of_bits {s s' : MachineData} {clob : FlagMask}
    (hn : clob.getLsbD 0 = false → s'.status.n = s.status.n)
    (hz : clob.getLsbD 1 = false → s'.status.z = s.status.z)
    (hc : clob.getLsbD 2 = false → s'.status.c = s.status.c)
    (hv : clob.getLsbD 3 = false → s'.status.v = s.status.v) :
    armMach.UpdFlags armCondReads s s' clob := by
  intro c hdisj
  cases c <;> simp only [armCondReads, ArmCond.interp, ArmCond.toKraken,
    CondCode.interp] at hdisj ⊢ <;>
    (try rw [hn (flag_bit_clear (b := 0) (by decide) hdisj)]) <;>
    (try rw [hz (flag_bit_clear (b := 1) (by decide) hdisj)]) <;>
    (try rw [hc (flag_bit_clear (b := 2) (by decide) hdisj)]) <;>
    (try rw [hv (flag_bit_clear (b := 3) (by decide) hdisj)])

/-! ## 5. `[t_step_simp]` rules -/

attribute [t_step_simp] Directive.interp Instr.interp Operation.interp ConstExpr.interp
  ConstExpr.evalBranchTarget ExtOrImmReg.interp ShiftRegExpr.interp AddrOrLit.interpLoad
  AddrExpr.interpLoad AddrExpr.interpStore AddrExpr.checkSPAlignment AddrExpr.eval Effects.All
  MachineData.setRegOrZr MachineData.setRegOrSp

@[t_step_simp]
theorem setRegOrZr_zr (regs : Reg64s) (d : XReg) (w : RegWidth) (v : BitVec w.bits) :
    regs.setRegOrZr (zr d w) v = regs.setXReg d (v.setWidth 64) := by
  cases w <;> simp [zr]

@[t_step_simp]
theorem getRegOrZr_zr (regs : Reg64s) (r : XReg) (w : RegWidth) :
    regs.getRegOrZr (zr r w) = (regs.getXReg r).toBitVec.setWidth w.bits := by
  cases w <;> simp [zr]

@[t_step_simp]
theorem getRegOrZr_xzr (regs : Reg64s) (w : RegWidth) :
    regs.getRegOrZr (xzr w) = 0#w.bits := by
  simp [xzr]

end LeanQbe.T.Arm64
