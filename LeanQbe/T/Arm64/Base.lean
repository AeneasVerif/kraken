module

public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr
public import Kraken.AArch64.OmniSemantics
public import Kraken.AArch64.WP
public import Kraken.AArch64.Sep
public import Kraken.AArch64.Regs
public import LeanQbe.T.Target
public import LeanQbe.T.StepSimp

/-!
# Shared Kraken AArch64 Target Base

Shared directive/register/memory abbreviations, `get`/`wr` register-file accessors, `ArmCond`
(restricting `CondCode` to the 14 invertible conditions), flag masks, `armCondReads`,
`armNegCond`, `armMach : Machine Reg Empty ArmCond Directive`, `keepsFlags_of_bits`, and
`[t_step_simp]` rules for `LeanQbe.T.Arm64.*` (isel and frames).
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

/-- Load 64-bit constant `c` into `x_d` via literal pool (`ldr x_d, =c`). -/
abbrev armLdrPoolBv (d : XReg) (c : BitVec 64) : Directive :=
  ins (w := .W64) (.LDR (zr d .W64) (.lit (.pool { expr := .int64 (Int64.ofBitVec c) })))

/-- Copy 64-bit GP or stack register `s` into `x_d` (`add x_d, s, #0` / `mov x_d, s`). -/
abbrev armMovToX (d : XReg) (s : Reg) : Directive :=
  ins (w := .W64) (.ADD_e (.low (.reg d) .W64) (.low s .W64) imm0)

/-- Copy 64-bit GP register `s` into `sp` (`add sp, x_s, #0` / `mov sp, x_s`). -/
abbrev armMovToSp (s : XReg) : Directive :=
  ins (w := .W64) (.ADD_e (.low .SP .W64) (.low (.reg s) .W64) imm0)

/-- Materialize 64-bit symbol address `sym` into `x_d`
(`adrp x_d, sym; add x_d, x_d, :lo12:sym`). -/
def armSymAddr (d : XReg) (sym : Sym) : List Directive :=
  [.adrp d sym, .addLo12 d d sym]

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

theorem ne_of_not_mem_armScratch {r : Reg} (hr : r ∉ armScratch) :
    r ≠ .reg .X16 ∧ r ≠ .reg .X17 := by
  simp only [armScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact hr

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

/-! ## 5. `Program.wp` / `armMach.FallsTo` combinators and `[t_step_simp]` rules -/

/-- Directive `d`, run from `s`, falls through into a state satisfying `Q`. -/
def armDirFallsTo (d : Directive) (s : MachineData) (Q : MachineData → Prop) : Prop :=
  ∀ [Labels] (p : Std.Rco Int64) (next : MachineData → Effects)
    (jmp : Int64 → MachineData → Effects) (P : MachineState → Prop),
    (∀ s', Q s' → (next s').All P) → (d.interp s p next jmp).All P

theorem armDirFallsTo_wp [Host] {d : Directive} {s : MachineData}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} (h : armDirFallsTo d s Q) :
    _root_.Program.wp [d] Q E s :=
  _root_.Program.wp_singleton fun _ _ => h _ _ _ _ fun _ hq => Or.inl ⟨rfl, hq⟩

theorem armWp_nil [Host] {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} (h : Q s) : _root_.Program.wp [] Q E s :=
  _root_.Program.wp_nil h

theorem armWp_mono [Host] {p : _root_.Program} {Q Q' : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : _root_.Program.wp p Q E s) (hQ : ∀ s', Q s' → Q' s') : _root_.Program.wp p Q' E s :=
  _root_.Program.wp_mono hQ (fun _ _ he => he) h

theorem armWp_cons [Host] {d : Directive} {p : _root_.Program}
    {Qd Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (hd : _root_.Program.wp [d] Qd E s) (hp : ∀ s', Qd s' → _root_.Program.wp p Q E s') :
    _root_.Program.wp (d :: p) Q E s :=
  _root_.Program.wp_cons (_root_.Program.wp_mono hp (fun _ _ he => he) hd)

theorem armWp_append [Host] {p q : _root_.Program}
    {Qp Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (hp : _root_.Program.wp p Qp E s) (hq : ∀ s', Qp s' → _root_.Program.wp q Q E s') :
    _root_.Program.wp (p ++ q) Q E s :=
  _root_.Program.wp_append (_root_.Program.wp_mono hq (fun _ _ he => he) hp)

theorem armFallsTo_of_wp {h : Host} {k : Nat} {c : List Directive}
    {gClob : List Reg} {fClob : FlagMask} {s : MachineData}
    {Q : MachineData → Prop} {post : MachineState → Prop}
    (hwp : @Program.wp h c (fun s' => Q s' ∧ armMach.Frame armCondReads s s' gClob [] fClob)
      (fun _ _ => False) s) :
    armMach.FallsTo armCondReads h k c gClob [] fClob s Q post := by
  letI := h
  intro hc hk
  refine eventually_trans _ _ _ _ (hwp k hc) ?_
  rintro ⟨s', a⟩ (⟨ha, ⟨hq, hfr⟩⟩ | hf)
  · dsimp only at ha; subst ha; exact hk s' hq hfr
  · exact False.elim hf

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

theorem armLdrPoolBv_wp [Host] (d : XReg) (c : BitVec 64) (s : MachineData) :
    _root_.Program.wp [armLdrPoolBv d c]
      (fun s' => s' = wr s d c) (fun _ _ => False) s := by
  refine armDirFallsTo_wp (by
    intro _ p next jmp P hk
    simp only [t_step_simp, Literal.interpLoad, BitVec.setWidth_eq]
    rw [← Int64.toInt_toBitVec, Int64.toBitVec_ofBitVec, BitVec.ofInt_toInt]
    exact hk _ rfl)

theorem armMovToX_wp [Host] (d : XReg) (rs : Reg) (s : MachineData) :
    _root_.Program.wp [armMovToX d rs]
      (fun s' => s' = wr s d (get s rs)) (fun _ _ => False) s := by
  refine armDirFallsTo_wp (by
    intro _ p next jmp P hk
    simp only [t_step_simp, imm0, Int64.toInt_zero, Reg64s.setRegOrSp,
      Reg64s.setRegOrSp64]
    rw [show BitVec.ofInt RegWidth.W64.bits 0 = 0#64 from rfl, BitVec.add_zero]
    cases rs with
    | SP => simp [Reg64s.getRegOrSp_sp64]; exact hk _ rfl
    | reg x => simp [Reg64s.getRegOrSp_reg64]; exact hk _ rfl)

theorem armMovToSp_wp [Host] (xs : XReg) (s : MachineData) :
    _root_.Program.wp [armMovToSp xs]
      (fun s' => s' = { s with regs := { s.regs with SP := UInt64.ofBitVec (get s (.reg xs)) } })
      (fun _ _ => False) s := by
  refine armDirFallsTo_wp (by
    intro _ p next jmp P hk
    simp only [t_step_simp, imm0, Int64.toInt_zero, Reg64s.setRegOrSp_sp64,
      Reg64s.getRegOrSp_reg64]
    rw [show BitVec.ofInt RegWidth.W64.bits 0 = 0#64 from rfl, BitVec.add_zero]
    exact hk _ rfl)

theorem armSymAddr_noLab (d : XReg) (sym l : Sym) :
    Kraken.Directive.label l ∉ armSymAddr d sym := by
  simp [armSymAddr]

theorem armSymAddr_wp [Host] (d : XReg) (sym : Sym) (s : MachineData) :
    _root_.Program.wp (armSymAddr d sym)
      (fun s' => s' = wr s d (Labels.label sym).toBitVec) (fun _ _ => False) s :=
  _root_.Program.wp_adrp_add_label d sym s

theorem armSymAddr_spec {h : Host} {k : Nat} {d : XReg} {sym : Sym} {s : MachineData}
    {post : MachineState → Prop} :
    armMach.FallsTo armCondReads h k (armSymAddr d sym) [.reg d] [] maskNone s
      (fun s' => get s' (.reg d) = (armMach.labelAddr h sym).toBitVec ∧ s'.dmem = s.dmem)
      post := by
  letI := h
  refine armFallsTo_of_wp (armWp_mono (armSymAddr_wp d sym s) ?_)
  rintro s' rfl
  refine ⟨⟨get_reg _ _ ▸ get_wr_same _ _ _, rfl⟩,
    ⟨fun r hr => get_wr_of_ne s d _ r (fun e => hr (e ▸ List.mem_cons_self)),
      fun v => v.elim, fun _ _ => rfl⟩⟩

end LeanQbe.T.Arm64
