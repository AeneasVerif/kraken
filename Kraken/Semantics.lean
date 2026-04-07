-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

import Lean
import Std

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

def BitVec.take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
def BitVec.drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop w) new).setWidth _

inductive Width | W8 | W16 | W32 | W64 deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString Width where
  toString | .W8 => "w8" | .W16 => "w16" | .W32 => "w32" | .W64 => "w64"

namespace Width
def bits : Width → Nat | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
def bytes : Width → Nat | W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8
abbrev bytesv (w : Width) {n} : BitVec n := BitVec.ofNat n w.bytes
abbrev type (w : Width) : Type := BitVec w.bits
instance {w : Width} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end Width

inductive Reg64
  | rax | rbx | rcx | rdx
  | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Reg : Width → Type
  | low (_ : Reg64) (w : Width) : Reg w
  | ah : Reg .W8 | bh : Reg .W8 | ch : Reg .W8| dh : Reg .W8
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

namespace Reg
def base {w} (r : Reg w) : Reg64 := match r with
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

def offset {w} (r : Reg w) : Nat := match r with
  | .low _ _ => 0
  | .ah | .bh | .ch | .dh => 8
end Reg

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def Reg64s.get64 (s : Reg64s) (r : Reg64) : Width.W64.type := UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
  | .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
  | .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
  | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15)

def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : Width.W64.type) : Reg64s :=
  let  v := UInt64.ofBitVec v
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  ((s.get64 r.base).drop r.offset).take w.bits
  -- BitVec because it may be signed or unsigned depending on context

def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (v.zeroExtend _)
  | .low r w => s.set64 r ((s.get64 r).replaceLow v)
  | .ah | .bh | .ch | .dh => let old := s.get64 r.base;
    s.set64 r.base (old.replaceLow (BitVec.append v (s.get (.low r.base .W8))))

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev DataMem := Std.ExtHashMap UInt64 UInt64 -- 8-byte-aligned acceses only now
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  status : StatusFlags := .mk false false false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

class Throw α where
  throw: String → α

def throw {α} [inst: Throw α] :=
  inst.throw

def Reg.interp {α w} (r : Reg w) (s : MachineData) (_ : Std.Rco Int64) (ret : w.type → α) :=
  ret (s.regs.get r) -- the unused argument is present ^ for uniformity with RegOrMem.interp

def MachineData.load {α} [Throw α] (s : MachineData) (addr : BitVec 64) (w : Width) (ret : w.type → α): α :=
  if addr % 8 != 0 then throw (s!"Unimplemented: only 8-byte-aligned memory access is supported")
  else match s.dmem[UInt64.ofBitVec addr]? with
  | .some v => ret (v.toBitVec.truncate _)
  | .none => throw (s!"Memory accessed but not mapped (addr={repr addr})")

def MachineData.store {α} [Throw α] (s : MachineData) (addr : BitVec 64) {w : Width} (v : w.type) (ret: MachineData → α) : α :=
  s.load addr .W64 (fun old =>
  ret { s with dmem := s.dmem.insert (.ofBitVec addr) (.ofBitVec (old.replaceLow v)) })

abbrev Label := String

class Labels where label : Label → Int64
def label [inst: Labels] := inst.label

inductive ConstExpr
  | Label (_ : Label)
  | Int64 (_ : Int64)
  | before_current_instruction | after_current_instruction
  | add (_ _ : ConstExpr) | sub (_ _ : ConstExpr)
  -- Careful adding operations here! Need to match overflow behavior of all
  -- assemblers we want compatibility with. We assume oversized literals error;
  -- clang and gcc seem to always use 64-bit arithmetic (MCValue has an int64).
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance : Coe Label ConstExpr where coe := ConstExpr.Label
instance : Coe Int64 ConstExpr where coe := ConstExpr.Int64
attribute [coe] ConstExpr.Label
attribute [coe] ConstExpr.Int64

def ConstExpr.interp [Labels] : ConstExpr → Std.Rco _root_.Int64 → _root_.Int64
  | .Label l, _ => label l
  | .Int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p

structure RegW where (w : Width) (reg : Reg w)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr, Hashable, Lean.ToExpr

inductive RegOrRip where | ofRegW (_ : RegW) | rip : RegOrRip
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure AddrIndex where
  reg : RegW
  scale: Width
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure AddrExpr where
  base : Option RegOrRip
  idx : Option AddrIndex
  disp : ConstExpr := .Int64 0
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

class AddressSize where address_size : Width
def address_size [inst: AddressSize] := inst.address_size

def AddrExpr.interp [Labels] [address_size : AddressSize] (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) :=
  let base := match a.base with
              | .some (.ofRegW ⟨_, r⟩)  => (s.get r).toInt
              | .some .rip => p.upper.toInt
              | .none => 0
  let idx := match a.idx with
             | .some ⟨⟨_, r⟩, c⟩ => (s.get r).toInt * c.bytes
             | .none => 0
  BitVec.ofInt address_size.address_size.bits (base + idx + (a.disp.interp p).toInt)

inductive RegOrMem w | Reg (r : Reg w) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe AddrExpr (RegOrMem w) where coe := RegOrMem.mem
attribute [coe] RegOrMem.mem
instance {w} : Coe (Reg w) (RegOrMem w) where coe := RegOrMem.Reg
attribute [coe] RegOrMem.Reg
abbrev Dst := RegOrMem

def RegOrMem.interp {α w} [Labels] [AddressSize] [Throw α] (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → α) :=
  match o with
  | .Reg r => ret (s.regs.get r)
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) w ret

def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.set {α w} [Labels] [AddressSize] [Throw α] (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → α) : α :=
  match d with
  | .Reg r => ret (s.setReg r v)
  | .mem a => s.store ((a.interp s.regs p).zeroExtend _) v ret

inductive Operand w | RegOrMem (_ : RegOrMem w) | imm (v : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe (RegOrMem w) (Operand w) where coe := Operand.RegOrMem
attribute [coe] Operand.RegOrMem
instance {w} : Coe ConstExpr (Operand w) where coe := Operand.imm
attribute [coe] Operand.imm
abbrev Operand.reg {w} (r : Reg w) : Operand w := .RegOrMem (.Reg r)
abbrev Operand.mem {w} (m : AddrExpr) : Operand w := .RegOrMem (.mem m)

def Operand.interp {α w} [Labels] [AddressSize] [Throw α] (o : Operand w) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → α) :=
  match o with
  | .RegOrMem rm => rm.interp s p ret
  | .imm v => ret ((v.interp p).toBitVec.truncate _)
  -- we rely on assemblers erroring out on too-large immediates in uniform ops

inductive CondCode | z | nz | c | nc | a | be
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
abbrev CondCode.e := CondCode.z
abbrev CondCode.ne := CondCode.nz
abbrev CondCode.b := CondCode.c
abbrev CondCode.ae := CondCode.nc

def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .z  => s.zf | .nz => !s.zf | .c  => s.cf | .nc => !s.cf
  | .a  => !s.cf && !s.zf | .be => s.cf || s.zf

inductive ShiftCountExpr | cl | imm8 (v : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

def ShiftCountExpr.interp [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) := match c with
  | .cl => s.regs.rcx.toBitVec.take 8
  | .imm8 v => (v.interp p).toBitVec.truncate _
def ShiftCountExpr.interpMasked [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width) : Nat :=
  (c.interp s p).toNat &&& match w with | .W64 => 0x1f | _ => 0x0f -- "masked to 5 bits (or 6 bits with a 64-bit operand)"

inductive RelRegOrMem | Rel (_ : ConstExpr) | Reg (r : Reg .W64) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

def RelRegOrMem.interp {α} [Labels] [AddressSize] [Throw α] (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64) (ret : BitVec 64 → α) :=
  match o with
  | .Rel c => ret (p.upper + c.interp p).toBitVec
  | .Reg r => ret (s.regs.get r)
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) .W64 ret

inductive Operation (w : Width)
  -- Data movement
  | mov (_ : Dst w) (src : Operand w)
  | movsx {w'} (_ : Dst w) (src : RegOrMem w') -- {_ : w'.bits < w.bits ∧ w'.bits < 32}
  | movzx {w'} (_ : Dst w) (src : RegOrMem w') -- {_ : w'.bits < w.bits ∧ w'.bits < 32}
  | push (src : Operand w)
  | pop  (_ : Dst w)
  | setcc (_ : CondCode) (_ : Dst w) -- {_ : w = .W8}
  | cmovcc (_ : CondCode) (_ : Reg w) (src : RegOrMem w)
  -- Arithmetic
  | lea (_ : Reg w) (src : AddrExpr) -- {_ : 16 <= w.bits}
  | add  (_ : Dst w) (src : Operand w)
  | adc  (_ : Dst w) (src : Operand w)
  | adcx (_ : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  | adox (dst : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  | inc  (_ : RegOrMem w)
  | dec  (_ : RegOrMem w)
  | neg  (_ : RegOrMem w)
  | sub  (_ : Dst w) (src : Operand w)
  | sbb  (_ : Dst w) (src : Operand w)
  | cmp  (a : RegOrMem w) (b : Operand w)
  | mul  (src : RegOrMem w)
  | mulx (hi lo : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  -- | imul1 (src : RegOrMem w)
  | imul (_ : Option (Dst w)) (src1 : RegOrMem w) (src2 : Operand w)
  -- Bitwise
  | test (a : RegOrMem w) (b : Operand w)
  | and  (_ : Dst w) (src : Operand w)
  | or   (_ : Dst w) (src : Operand w)
  | xor  (_ : Dst w) (src : Operand w)
  | shl  (_ : Dst w) (_ : ShiftCountExpr)
  | shr  (_ : Dst w) (_ : ShiftCountExpr)
  | sar  (_ : Dst w) (_ : ShiftCountExpr)
  | shld (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr) -- {_ : 16 <= w.bits}
  | shrd (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr) -- {_ : 16 <= w.bits}
  | rol  (_ : Dst w) (_ : ShiftCountExpr)
  | ror  (_ : Dst w) (_ : ShiftCountExpr)
  | rcl  (_ : Dst w) (_ : ShiftCountExpr)
  | rcr  (_ : Dst w) (_ : ShiftCountExpr)
  | bswap  (dst : Reg w) -- (_ : w = .W32 ∨ w = .W64)
  -- Control flow
  | jcc (cc : CondCode) (target : Label)
  | jmp (target : RelRegOrMem)
  | call (target : RelRegOrMem)
  | ret
  | nop (length : Nat)
  -- TODO: optiona third argument, with the caveat that `.align 16,,0` is valid
  -- syntax
  | nopalign (alignment : Nat) (pad : Option Nat)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

structure StatusFlags.from_result.Remaining where
  cf : Bool
  af : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq

-- TEMPORARY: definitions stolen from Lean 4.28's standard library, but with a
-- different name so that this file builds with both 4.27 and 4.28
namespace BitVec
def cpopNatRec_ {w} (x : BitVec w) (pos acc : Nat) : Nat :=
  match pos with
  | 0 => acc
  | n + 1 => x.cpopNatRec_ n (acc + (x.getLsbD n).toNat)

def cpop_ {w} (x : BitVec w) : BitVec w := BitVec.ofNat w (cpopNatRec_ x w 0)
end BitVec

def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { pf := (result.truncate 8).cpop_ % 2 != BitVec.zero _
    zf := result == BitVec.zero _
    sf := result.msb, cf := f.cf, af := f.af, of := f.of }

class Undefined (T R) where undefined : (T → R) → R
def undefined {T R} [inst: Undefined T R] := inst.undefined

set_option maxHeartbeats 1000000
def Operation.interp {α} [∀ w : Width, Undefined w.type α] [Undefined StatusFlags α] [Undefined Bool α] [Throw α]
  [Labels] [address_size : AddressSize] {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → α) (jmp : Int64 → MachineData → α) : α :=
  match (generalizing := false) (motive := Operation w → α) i with
  | .mov dst src => src.interp s p (fun val => s.set dst val p next)
  | .movsx dst src => src.interp s p (fun val => s.set dst (val.signExtend _) p next)
  | .movzx dst src => src.interp s p (fun val => s.set dst (val.zeroExtend _) p next)
  | .push src =>
    src.interp s p (fun v =>
    let rsp := s.regs.get64 .rsp - w.bytesv
    { s with regs := s.regs.set64 .rsp rsp }.store rsp v next)
  | .pop dst =>
    let rsp := s.regs.get64 .rsp
    s.load rsp w (fun val =>
    s.set dst val p (fun s =>
    next { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) }))
  | .setcc cc dst =>
    s.set dst (cc.interp s.status) p next
  | .cmovcc cc dst src =>
    src.interp s p (fun src =>
    let v := if cc.interp s.status then src else s.regs.get dst
    next (s.setReg dst v))
-- Arithmetic
  | .lea dst src => next (s.setReg dst ((src.interp s.regs p).zeroExtend _))
  | .add dst src =>
    src.interp s p (fun a =>
    dst.interp s p (fun b =>
    let v := a + b
    let status := .from_result v {
      cf := v.toNat != a.toNat + b.toNat
      af := (v.truncate 4).toNat != (a.truncate 4).toNat + (b.truncate 4).toNat,
      of := v.toInt != a.toInt + b.toInt }
    { s with status }.set dst v p next))
  | .adc dst src =>
    src.interp s p (fun a =>
    dst.interp s p (fun b =>
    let c := s.status.cf
    let v := a + b + s.status.cf + c
    let status := .from_result v {
      cf := v.toNat != a.toNat + b.toNat + c
      af := (v.truncate 4).toNat != (a.truncate 4).toNat + (b.truncate 4).toNat + c,
      of := v.toInt != a.toInt + b.toInt + c }
    { s with status }.set dst v p next))
  | .adcx dst src =>
    src.interp s p (fun a =>
    dst.interp s p (fun b =>
    let v := a + b + s.status.cf
    let cf := v.toNat != a.toNat + b.toNat + s.status.cf.toNat
    next { s with regs := s.regs.set dst v, status := { s.status with cf := cf }}))
  | .adox dst src =>
    src.interp s p (fun a =>
    dst.interp s p (fun b =>
    let v := a + b + s.status.of
    let of := v.toNat != a.toNat + b.toNat + s.status.of.toNat
    next { s with regs := s.regs.set dst v, status := { s.status with of := of }}))
  | .inc dst =>
    dst.interp s p (fun a =>
    let v := a + 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.truncate 4).toNat != (a.truncate 4).toNat + 1,
      of := v.toInt != a.toInt + 1 }
    { s with status }.set dst v p next)
  | .dec dst =>
    dst.interp s p (fun a =>
    let v := a - 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.truncate 4).toNat != (a.truncate 4).toNat - 1,
      of := v.toInt != a.toInt - 1 }
    { s with status }.set dst v p next)
  | .neg dst =>
    dst.interp s p (fun b =>
    let v := -b
    let status := .from_result v {
      cf := b != 0
      af := (b.truncate 4) != 0,
      of := v.toInt != - b.toInt }
    { s with status }.set dst v p next)
  | .sub dst src =>
    src.interp s p (fun a =>
    dst.interp s p (fun b =>
    let v := a - b
    let status := .from_result v {
      cf := v.toNat != a.toNat - b.toNat
      af := (v.truncate 4).toNat != (a.truncate 4).toNat - (b.truncate 4).toNat,
      of := v.toInt != a.toInt - b.toInt }
    { s with status }.set dst v p next))
  | .sbb dst src =>
    src.interp s p (fun a =>
    dst.interp s p (fun b =>
    let c := s.status.cf
    let v := a - b - c
    let status := .from_result v {
      cf := v.toNat != a.toNat - b.toNat - c.toNat
      af := (v.truncate 4).toNat != (a.truncate 4).toNat - (b.truncate 4).toNat - c.toNat,
      of := v.toInt != a.toInt - b.toInt - c.toInt }
    { s with status }.set dst v p next))
  | .cmp a b =>
    a.interp s p (fun a =>
    b.interp s p (fun b =>
    let v := a - b
    let status := .from_result v {
      cf := v.toNat != a.toNat - b.toNat
      af := (v.truncate 4).toNat != (a.truncate 4).toNat - (b.truncate 4).toNat,
      of := v.toInt != a.toInt - b.toInt }
    next { s with status }))
  | .mul src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b =>
    let v := a * b
    let vn := a.toNat * b.toNat
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (.ofNat _ vn)
      else (s.setReg (.low .rax w) v).setReg (.low .rdx w) (.ofNat _ (vn >>> w.bits))
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := v.toNat != vn, pf, af, zf, sf, of := v.toNat != vn }})))))
  | .mulx r_hi r_lo src1 =>
    src1.interp s p (fun a =>
    let b := s.regs.get (.low .rdx w)
    let v := a.toNat * b.toNat
    let s := s.setReg r_lo (.ofNat _ v) -- if r_hi = r_li, hi is written:
    let s := s.setReg r_hi (.ofNat _ (v >>> w.bits))
    next s)
  | .imul dst src1 src2 =>
    src1.interp s p (fun a =>
    src2.interp s p (fun b =>
    let v := a * b
    s.set (match (generalizing := false) (motive := Option (RegOrMem w) → RegOrMem w)
             dst with | .some dst => dst | _ => src1) v p (fun s =>
    let cf := v.toInt != a.toInt * b.toInt
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))))
-- Bitwise
  | .test a b =>
    a.interp s p (fun a =>
    b.interp s p (fun b =>
    let v := a &&& b
    undefined (fun af =>
    let status := .from_result v { cf := false, af, of := false}
    next { s with status})))
  | .and dst src | .or dst src | .xor dst src =>
    dst.interp s p (fun a =>
    src.interp s p (fun b =>
    let v := match i with | .and _ _ => a &&& b | .or _ _ => a ||| b | _ => a ^^^ b
    undefined (fun af =>
    let status := .from_result v { cf := false, of := false, af }
    { s with status }.set dst v p next)))
  | .shl dst count =>
    dst.interp s p (fun a =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a <<< count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a <<< (count-1)).msb else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shr dst count =>
    dst.interp s p (fun a =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.ushiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof a.msb else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .sar dst count =>
    dst.interp s p (fun a =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.sshiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof false else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shrd dst src count =>
    dst.interp s p (fun a =>
    src.interp s p (fun b =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := (((b.append a) >>> count).take w.bits).setWidth _
    (λ setstatus => if count >= w.bits then undefined setstatus else
      let cf := a.getLsbD (count-1)
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    { s with status }.set dst v p next)))
  | .shld dst src count =>
    dst.interp s p (fun a =>
    src.interp s p (fun b =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := (((a.append b) <<< count).drop w.bits).setWidth _
    (λ setstatus => if count >= w.bits then undefined setstatus else
      let cf := (a <<< (count-1)).msb
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    { s with status }.set dst v p next)))
  | .rol dst count =>
    dst.interp s p (fun a =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.rotateLeft count
    let cf := v.getLsbD 0
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .ror dst count =>
    dst.interp s p (fun a =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.rotateRight count
    let cf := v.msb
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcr dst count =>
    dst.interp s p (fun a =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateRight count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcl dst count =>
    dst.interp s p (fun a =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateLeft count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .bswap dst =>
    let a := s.regs.get dst
    match (generalizing := false) (motive := Width → α) w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      next (s.setReg dst (v.setWidth _))
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      next (s.setReg dst (v.setWidth _))
    | _ => @undefined _ _ _ (fun v => next (s.setReg dst v))
  | .jcc cc l =>
    if cc.interp s.status
    then jmp (label l) s
    else next s
  | .jmp tgt =>
    tgt.interp s p (fun a =>
    jmp (.ofBitVec a) s)
  | .call tgt =>
    tgt.interp s p (fun a =>
    let rsp := s.regs.get64 .rsp - Width.W64.bytesv
    { s with regs := s.regs.set64 .rsp rsp }.store rsp (w:=.W64) p.upper.toBitVec (jmp (.ofBitVec a)))
  | .ret =>
    let rsp := s.regs.get64 .rsp
    s.load rsp .W64 (fun ra =>
    jmp (.ofBitVec ra) { s with regs := s.regs.set64 .rsp (rsp + 8) })
  | nop _ | nopalign _ _ => next s

structure Instr where
  address_size : Width
  operation_size : Width
  operation : Operation operation_size
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

def Instr.interp {α} [∀ w : Width, Undefined w.type α] [Undefined StatusFlags α] [Undefined Bool α] [Throw α] [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → α) (jmp : Int64 → MachineData → α) : α :=
  Operation.interp (w := i.operation_size ) (address_size := .mk i.address_size) i.operation p s next jmp

instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray
inductive Directive
  | Instr (_ : Instr)
  | Label (_ : Label)
  | ByteArray (_ : ByteArray)
  deriving BEq, DecidableEq, Repr, Hashable, Lean.ToExpr

def Directive.interp {α} [Undefined Bool α] [Throw α] [Labels]
  [∀ w : Width, Undefined w.type α] [Undefined StatusFlags α]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → α) (jmp : Int64 → MachineData → α) : α :=
  match d with
  | .Label _ => next s
  | .Instr i => i.interp s p next jmp
  | .ByteArray _ => throw s!"Unimplemented: execution reached data block at {p.1}"

def Directives.interp {α} [Undefined Bool α] [Throw α] [Labels]
  [∀ w : Width, Undefined w.type α] [Undefined StatusFlags α]
  (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
  (ret : Int64 → MachineData → α) : α :=
  match ds with
  | [] => ret pc s
  | (d, sz) :: ds =>
    d.interp s (.mk pc (pc+.ofNat sz)) (jmp:=ret) (next := (fun s =>
    interp ds s (pc+.ofNat sz) ret))

abbrev Program := List Directive
abbrev Executable := Int64 × List (Directive × Nat) -- start and sizes

class Layout where (start : Int64) (size : Nat → Nat)
def Layout.apply (l : Layout) (prog : Program) : Executable :=
  (l.start, prog.mapIdx (fun i d => (d, l.size i)))
instance : CoeFun Layout (fun _ => Program → Executable) where coe := Layout.apply

-- TEMPORARY: replace with `import Init.Data.List.scan.Basic` when dropping support for Lean 4.28
namespace List
@[inline]
private def scanAuxM {α β m} [Monad m] (f : β → α → m β) (init : β) (l : List α) : m (List β) :=
  go l init []
where
  @[specialize] go : List α → β → List β → m (List β)
    | [], last, acc => pure <| last :: acc
    | x :: xs, last, acc => do go xs (← f last x) (last :: acc)
@[inline]
def scanlM {α β m} [Monad m] (f : β → α → m β) (init : β) (l : List α) : m (List β) :=
  List.reverse <$> scanAuxM f init l
@[inline]
def scanl {α β} (f : β → α → β) (init : β) (as : List α) : List β :=
  Id.run <| as.scanlM (pure <| f · ·) init
end List

def Executable.withAddresses (e : Executable)  : List (Int64 × Directive × Nat) :=
  (e.2.scanl (fun (p, _, _) (d, z) => (p+.ofNat z, d, z)) (e.1, .ByteArray (.mk #[]), 0))

def Executable.labels (e : Executable) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun (p, d, _) => if d = .Label l then .some p else .none)).getD (-1) }

def Executable.directivesAtAddress (e : Executable) (a : Int64) : List (Directive × Nat) :=
  (e.withAddresses.filter (·.1 = a)).map (·.2)

def Executable.directivesFromAddress (e : Executable) (a : Int64) : List (Directive × Nat) :=
  e.2.drop (((e.withAddresses).map (·.1)).idxOf a)

def Executable.directivesFromLabel (e : Executable) (l : Label) : List (Directive × Nat) :=
  e.2.dropWhile (·.1 != .Label l)

def Executable.step {α} [∀ w : Width, Undefined w.type α] [Undefined StatusFlags α] [Undefined Bool α]
  [Throw α]
  (e : Executable) (s : MachineData × Int64) (ret : MachineData × Int64 → α) : α :=
  let := e.labels
  Directives.interp (e.directivesAtAddress s.2) s.1 s.2 (fun pc s => ret (s, pc))

def Executable.straightline {α} [∀ w : Width, Undefined w.type α] [Undefined StatusFlags α] [Undefined Bool α]
  [Throw α]
  (e : Executable) (s : MachineData × Int64) (ret : MachineData × Int64 → α) : α :=
  let := e.labels;
  Directives.interp (e.directivesFromAddress s.2) s.1 s.2 (fun pc s => ret (s, pc))

-- -- Concrete evaluators for expedient testing

def Executable.eval (e : Executable) (s : MachineData × Int64) (until_ : MachineData × Int64 → Bool) : Except String (MachineData × Int64) :=
  if until_ s then .ok s else
  let α := Except String (MachineData × Int64)
  let : Throw α := { throw s := .error s }
  let : Undefined Bool α := { undefined ret := ret (hash s.1.regs % 2 != 0) }
  let : Undefined StatusFlags α := { undefined ret := let h := (hash s.1.regs).toBitVec; ret (.mk h[0] h[1] h[2] h[3] h[4] h[5]) }
  let (w : Width) : Undefined w.type α := { undefined ret := ret ((hash s.1.regs).toBitVec.setWidth w.bits) }
  match e.straightline s Except.ok with
  | .ok s => eval e s until_
  | .error s => .error s
partial_fixpoint

def Directive.fakeSize (hashOfProgram : UInt64) (d : Directive) : Nat :=
  match d with
  | .Label _ => 0
  | .Instr (.mk _ _ (.nop sz)) => sz -- may be zero
  | .Instr i => (1 + hash (hashOfProgram, i) % 15).toNat
  | .ByteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.ByteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize h }
  layout prog

abbrev eval [layout : Layout] (prog : Program) := (layout prog).eval

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .Label "main",
    .Instr (.mk .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.Int64 41)))),
    .Instr (.mk .W64 .W64 (.inc (.Reg (.low .rax .W64)))),
    .Instr (.mk .W64 .W64 .ret) ]
  let start := exe.labels.label "main"
  let data := { dmem := .ofList [(0x100, 0x1337)], regs := {rsp := 0x100} }
  (exe.eval (data, start) (fun (_, pc) => pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)

namespace Reg
@[match_pattern] abbrev rax := low .rax .W64
@[match_pattern] abbrev rbx := low .rbx .W64
@[match_pattern] abbrev rcx := low .rcx .W64
@[match_pattern] abbrev rdx := low .rdx .W64
@[match_pattern] abbrev rsi := low .rsi .W64
@[match_pattern] abbrev rdi := low .rdi .W64
@[match_pattern] abbrev rsp := low .rsp .W64
@[match_pattern] abbrev rbp := low .rbp .W64
@[match_pattern] abbrev r8  := low .r8  .W64
@[match_pattern] abbrev r9  := low .r9  .W64
@[match_pattern] abbrev r10 := low .r10 .W64
@[match_pattern] abbrev r11 := low .r11 .W64
@[match_pattern] abbrev r12 := low .r12 .W64
@[match_pattern] abbrev r13 := low .r13 .W64
@[match_pattern] abbrev r14 := low .r14 .W64
@[match_pattern] abbrev r15 := low .r15 .W64

@[match_pattern] abbrev eax  := low .rax .W32
@[match_pattern] abbrev ebx  := low .rbx .W32
@[match_pattern] abbrev ecx  := low .rcx .W32
@[match_pattern] abbrev edx  := low .rdx .W32
@[match_pattern] abbrev esi  := low .rsi .W32
@[match_pattern] abbrev edi  := low .rdi .W32
@[match_pattern] abbrev esp  := low .rsp .W32
@[match_pattern] abbrev ebp  := low .rbp .W32
@[match_pattern] abbrev r8d  := low .r8  .W32
@[match_pattern] abbrev r9d  := low .r9  .W32
@[match_pattern] abbrev r10d := low .r10 .W32
@[match_pattern] abbrev r11d := low .r11 .W32
@[match_pattern] abbrev r12d := low .r12 .W32
@[match_pattern] abbrev r13d := low .r13 .W32
@[match_pattern] abbrev r14d := low .r14 .W32
@[match_pattern] abbrev r15d := low .r15 .W32

@[match_pattern] abbrev ax   := low .rax .W16
@[match_pattern] abbrev bx   := low .rbx .W16
@[match_pattern] abbrev cx   := low .rcx .W16
@[match_pattern] abbrev dx   := low .rdx .W16
@[match_pattern] abbrev si   := low .rsi .W16
@[match_pattern] abbrev di   := low .rdi .W16
@[match_pattern] abbrev sp   := low .rsp .W16
@[match_pattern] abbrev bp   := low .rbp .W16
@[match_pattern] abbrev r8w  := low .r8  .W16
@[match_pattern] abbrev r9w  := low .r9  .W16
@[match_pattern] abbrev r10w := low .r10 .W16
@[match_pattern] abbrev r11w := low .r11 .W16
@[match_pattern] abbrev r12w := low .r12 .W16
@[match_pattern] abbrev r13w := low .r13 .W16
@[match_pattern] abbrev r14w := low .r14 .W16
@[match_pattern] abbrev r15w := low .r15 .W16

@[match_pattern] abbrev al   := low .rax .W8
@[match_pattern] abbrev bl   := low .rbx .W8
@[match_pattern] abbrev cl   := low .rcx .W8
@[match_pattern] abbrev dl   := low .rdx .W8
@[match_pattern] abbrev sil  := low .rsi .W8
@[match_pattern] abbrev dil  := low .rdi .W8
@[match_pattern] abbrev spl  := low .rsp .W8
@[match_pattern] abbrev bpl  := low .rbp .W8
@[match_pattern] abbrev r8b  := low .r8  .W8
@[match_pattern] abbrev r9b  := low .r9  .W8
@[match_pattern] abbrev r10b := low .r10 .W8
@[match_pattern] abbrev r11b := low .r11 .W8
@[match_pattern] abbrev r12b := low .r12 .W8
@[match_pattern] abbrev r13b := low .r13 .W8
@[match_pattern] abbrev r14b := low .r14 .W8
@[match_pattern] abbrev r15b := low .r15 .W8
end Reg
