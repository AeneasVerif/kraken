module

public import Kraken.X64.OmniSemantics
public import Kraken.X64.WP
public import Kraken.X64.Sep
public import Kraken.X64.Regs
public import LeanQbe.T.Target
public import LeanQbe.T.StepSimp

/-!
# Shared Kraken x64 Target Base

Shared directive/register/memory abbreviations, flag clobber masks, condition-code helpers,
`x64Mach : Machine Reg64 RegMm CondCode Directive`, `[t_step_simp]` rules, and self-contained
`Directive.FallsTo` / `Program.wp` combinators for `LeanQbe.T.Amd64.*` (isel and frames).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

/-! ## 1. Directive, register, and addressing abbreviations -/

/-- 64-bit x64 directive wrapper. -/
abbrev ins (op : Operation .W64) : Directive := .instr (.regular .W64 .W64 op)

/-- 32-bit x64 directive wrapper (64-bit address size). -/
abbrev ins32 (op : Operation .W32) : Directive := .instr (.regular .W64 .W32 op)

/-- 16-bit x64 directive wrapper (64-bit address size). -/
abbrev ins16 (op : Operation .W16) : Directive := .instr (.regular .W64 .W16 op)

/-- 8-bit x64 directive wrapper (64-bit address size). -/
abbrev ins8 (op : Operation .W8) : Directive := .instr (.regular .W64 .W8 op)

/-- 64-bit view of general-purpose register `r`. -/
abbrev q (r : Reg64) : Reg .W64 := .low r .W64

/-- 32-bit view of general-purpose register `r`. -/
abbrev d (r : Reg64) : Reg .W32 := .low r .W32

/-- 16-bit view of general-purpose register `r`. -/
abbrev h16 (r : Reg64) : Reg .W16 := .low r .W16

/-- Low 8-bit view of general-purpose register `r`. -/
abbrev b8 (r : Reg64) : Reg .W8 := .low r .W8

/-- Memory operand `[r]`. -/
abbrev atReg (r : Reg64) : AddrExpr := { base := some (.reg r), idx := none }

/-- Memory operand `[r + off]`. -/
abbrev atDisp (r : Reg64) (off : Int64) : AddrExpr :=
  { base := some (.reg r), idx := none, disp := .int64 off }

/-- Map `AddrScale` to Kraken SIB index `Width` (`1/2/4/8` bytes). -/
def scaleWidth : AddrScale → Width
  | .s1 => .W8
  | .s2 => .W16
  | .s4 => .W32
  | .s8 => .W64

/-- SIB scaled-index memory operand `[rb + ri * scale + off]`. -/
abbrev atSIB (rb ri : Reg64) (sc : AddrScale) (off : Int64) : AddrExpr :=
  { base := some (.reg rb), idx := some ⟨ri, scaleWidth sc⟩, disp := .int64 off }

/-- True iff `a` is encodable in x64 SIB/disp hardware (`%rsp` cannot be a SIB index). -/
def x64AddrValid : AddrArg Reg64 → Bool
  | .baseIdxDisp _ .rsp _ _ => false
  | _ => true

/-! ## 2. Status-flag masks, `x64CondReads`, and `x64NegCond` (`CF=0, PF=1, AF=2, ZF=3, SF=4, OF=5`) -/

def maskNone   : FlagMask := 0x00#8
def maskCF     : FlagMask := 0x01#8
def maskPF     : FlagMask := 0x02#8
def maskAF     : FlagMask := 0x04#8
def maskZF     : FlagMask := 0x08#8
def maskSF     : FlagMask := 0x10#8
def maskOF     : FlagMask := 0x20#8
def maskAll    : FlagMask := 0xFF#8
def maskDecInc : FlagMask := maskPF ||| maskAF ||| maskZF ||| maskSF ||| maskOF

/-- Status flags read by each x64 `CondCode`. -/
def x64CondReads : CondCode → FlagMask
  | .o  | .no => maskOF
  | .c  | .nc => maskCF
  | .z  | .nz => maskZF
  | .be | .a  => maskCF ||| maskZF
  | .s  | .ns => maskSF
  | .p  | .np => maskPF
  | .l  | .ge => maskSF ||| maskOF
  | .le | .g  => maskZF ||| maskSF ||| maskOF

/-- Logical negation of an x64 `CondCode`. -/
def x64NegCond : CondCode → CondCode
  | .o => .no | .no => .o
  | .c => .nc | .nc => .c
  | .z => .nz | .nz => .z
  | .be => .a | .a => .be
  | .s => .ns | .ns => .s
  | .p => .np | .np => .p
  | .l => .ge | .ge => .l
  | .le => .g | .g => .le

theorem x64NegCond_interp (cc : CondCode) (st : StatusFlags) :
    (x64NegCond cc).interp st = !cc.interp st := by
  rcases st with ⟨cf, pf, af, zf, sf, of⟩
  cases cc <;> cases cf <;> cases pf <;> cases zf <;> cases sf <;> cases of <;> rfl

theorem x64NegCond_reads (cc : CondCode) :
    x64CondReads (x64NegCond cc) = x64CondReads cc := by
  cases cc <;> rfl

/-! ## 3. Scratch registers, `x64Mach`, and flag framing -/

/-- Caller-saved scratch GPRs reserved for lowering (`%r10`, `%r11`). -/
@[reducible] def x64Scratch : List Reg64 := [.r10, .r11]

theorem ne_of_not_mem_x64Scratch {r : Reg64} (hr : r ∉ x64Scratch) :
    r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [x64Scratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact hr

/-- Single-step relation of a laid-out Kraken x64 host program. -/
def hostStep (h : Host) : MachineState → (MachineState → Prop) → Prop :=
  letI := h; step1 Host.exe

/-- Address resolved for label `l` in Kraken x64 host `h`. -/
def hostLabel (h : Host) (l : Label) : Int64 :=
  letI := h; Labels.label l

/-- Kraken x64 packaged as a `LeanQbe.T.Machine`. -/
@[reducible] def x64Mach : Machine Reg64 RegMm CondCode Directive where
  MData := MachineData
  Addr := Int64
  State := MachineState
  Host := Host
  getGpr s r := s.regs.get64 r
  getVec s vr := s.zmms.get512 vr
  evalCond s cc := cc.interp s.status
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

/-- Bit-level sufficient condition for `x64Mach.UpdFlags x64CondReads`. -/
theorem keepsFlags_of_bits {s s' : MachineData} {clob : FlagMask}
    (hcf : clob.getLsbD 0 = false → s'.status.cf = s.status.cf)
    (hpf : clob.getLsbD 1 = false → s'.status.pf = s.status.pf)
    (hzf : clob.getLsbD 3 = false → s'.status.zf = s.status.zf)
    (hsf : clob.getLsbD 4 = false → s'.status.sf = s.status.sf)
    (hof : clob.getLsbD 5 = false → s'.status.of = s.status.of) :
    x64Mach.UpdFlags x64CondReads s s' clob := by
  intro cc hdisj
  cases cc <;> simp only [x64CondReads, CondCode.interp] at hdisj ⊢ <;>
    (try rw [hcf (flag_bit_clear (b := 0) (by decide) hdisj)]) <;>
    (try rw [hpf (flag_bit_clear (b := 1) (by decide) hdisj)]) <;>
    (try rw [hzf (flag_bit_clear (b := 3) (by decide) hdisj)]) <;>
    (try rw [hsf (flag_bit_clear (b := 4) (by decide) hdisj)]) <;>
    (try rw [hof (flag_bit_clear (b := 5) (by decide) hdisj)])

/-! ## 4. Self-contained `Directive.FallsTo` and `Program.wp` helpers -/

/-- Directive `d`, run from `s`, falls through into a state satisfying `Q`. -/
def Directive.FallsTo (d : Directive) (s : MachineData) (Q : MachineData → Prop) : Prop :=
  ∀ [Labels] (p : Std.Rco Int64) (next : MachineData → Effects)
    (jmp : Int64 → MachineData → Effects) (P : MachineState → Prop),
    (∀ s', Q s' → (next s').All P) → (d.interp s p next jmp).All P

theorem Directive.FallsTo.wp [Host] {d : Directive} {s : MachineData} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} (h : Directive.FallsTo d s Q) :
    _root_.Program.wp [d] Q E s :=
  _root_.Program.wp_singleton fun _ _ => h _ _ _ _ fun _ hq => Or.inl ⟨rfl, hq⟩

namespace Program

variable [Host] {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}

theorem wp.cons {d : Directive} {p : _root_.Program} {Qd : MachineData → Prop}
    (hd : _root_.Program.wp [d] Qd E s) (hp : ∀ s', Qd s' → _root_.Program.wp p Q E s') :
    _root_.Program.wp (d :: p) Q E s :=
  _root_.Program.wp_cons (_root_.Program.wp_mono hp (fun _ _ h => h) hd)

theorem wp.append {p q : _root_.Program} {Qp : MachineData → Prop}
    (hp : _root_.Program.wp p Qp E s) (hq : ∀ s', Qp s' → _root_.Program.wp q Q E s') :
    _root_.Program.wp (p ++ q) Q E s :=
  _root_.Program.wp_append (_root_.Program.wp_mono hq (fun _ _ h => h) hp)

theorem wp.mono {p : _root_.Program} {Q' : MachineData → Prop} (h : _root_.Program.wp p Q E s)
    (hQ : ∀ s', Q s' → Q' s') : _root_.Program.wp p Q' E s :=
  _root_.Program.wp_mono hQ (fun _ _ h => h) h

theorem wp.eventually {p : _root_.Program} {k : Nat} {post : MachineState → Prop}
    (h : _root_.Program.wp p Q E s) (hk : p.IsInfixAt Host.prog k)
    (hQ : ∀ s', Q s' → Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + p.length)⟩)
    (hE : ∀ a s', E a s' → Eventually (step1 Host.exe) post ⟨s', a⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine eventually_trans _ _ _ _ (h k hk) ?_
  rintro ⟨s', a⟩ (⟨ha, hq⟩ | he)
  · dsimp only at ha hq; subst ha; exact hQ s' hq
  · exact hE a s' he

end Program

/-! ## 5. `[t_step_simp]` and `grind` rules -/

attribute [t_step_simp] Directive.interp Instr.interp Operation.interp Operand.interp
  RegOrMem.interp RelRegOrMem.interp ConstExpr.interp ShiftCountExpr.interp
  ShiftCountExpr.interpMasked Effects.All MachineData.set MachineData.setReg
  Reg64s.get_low32 Reg64s.set_low32

attribute [grind =] Reg64s.get64_set64

@[t_step_simp]
theorem get_q (regs : Reg64s) (r : Reg64) : regs.get (q r) = regs.get64 r :=
  Reg64s.get_low64 ..

@[t_step_simp]
theorem set_q (regs : Reg64s) (r : Reg64) (v : BitVec 64) : regs.set (q r) v = regs.set64 r v :=
  rfl

@[t_step_simp]
theorem get_b8 (regs : Reg64s) (r : Reg64) : regs.get (b8 r) = (regs.get64 r).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset, hi]

@[t_step_simp]
theorem get_h16 (regs : Reg64s) (r : Reg64) : regs.get (h16 r) = (regs.get64 r).setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset, hi]

@[t_step_simp]
theorem atReg_interp [Labels] (regs : Reg64s) (r : Reg64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ (atReg r) regs p).zeroExtend 64 = regs.get64 r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_toInt, BitVec.take, hi]

theorem atSIB_interp [Labels] (regs : Reg64s) (rb ri : Reg64) (sc : AddrScale)
    (off : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ (atSIB rb ri sc off) regs p).zeroExtend 64 =
      regs.get64 rb + (regs.get64 ri <<< sc.shift) + off.toBitVec := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, ConstExpr.interp,
    BitVec.signed, BitVec.extractLsb'_eq_self, BitVec.zeroExtend_eq_setWidth,
    BitVec.setWidth_eq, Width.bits]
  rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul]
  simp only [BitVec.ofInt_toInt, BitVec.ofInt_natCast]
  congr 1
  · congr 1
    cases sc <;> apply BitVec.eq_of_toNat_eq <;>
      simp [scaleWidth, AddrScale.shift, Width.bytes, BitVec.toNat_mul,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]

end LeanQbe.T.Amd64
