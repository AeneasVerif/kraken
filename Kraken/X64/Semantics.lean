-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

import Kraken.Attribute
import Kraken.Layout
import Kraken.Mem
import Kraken.X64.Syntax
import Lean
import Std

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

namespace BitVec
def unsigned {w} (x : BitVec w) : Int := x.toNat
def signed {w} (x : BitVec w) : Int := x.toInt
@[kstep] def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
end BitVec
attribute [kstep]
  BitVec.extractLsb'
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.signed
  BitVec.truncate
def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _

namespace Reg
@[kstep] def base {w} (r : Reg w) : Reg64 := match r with
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

@[kstep] def offset {w} (r : Reg w) : Nat := match r with
  | .low _ _ => 0
  | .ah | .bh | .ch | .dh => 8
end Reg

namespace AvxReg
def base {w} (r : AvxReg w) : RegMm := match r with
  | .xmm r => r
  | .ymm r => r
  | .zmm r => r
end AvxReg

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

@[kstep] def Reg64s.get64 (s : Reg64s) (r : Reg64) : Width.W64.type := UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
  | .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
  | .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
  | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15)

@[kstep] def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : Width.W64.type) : Reg64s :=
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

@[kstep] def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  ((s.get64 r.base).drop r.offset).take w.bits
  -- BitVec because it may be signed or unsigned depending on context

@[kstep] def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (v.zeroExtend _)
  | .low r w => s.set64 r ((s.get64 r).replaceLow v)
  | .ah | .bh | .ch | .dh => let old := s.get64 r.base;
    s.set64 r.base (old.replaceLow (BitVec.append v (s.get (.low r.base .W8))))

def ZmmValue : Type := BitVec 512
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def zmmZero : ZmmValue := 0#512

structure RegZmms where
  zmm0  : ZmmValue := zmmZero
  zmm1  : ZmmValue := zmmZero
  zmm2  : ZmmValue := zmmZero
  zmm3  : ZmmValue := zmmZero
  zmm4  : ZmmValue := zmmZero
  zmm5  : ZmmValue := zmmZero
  zmm6  : ZmmValue := zmmZero
  zmm7  : ZmmValue := zmmZero
  zmm8  : ZmmValue := zmmZero
  zmm9  : ZmmValue := zmmZero
  zmm10 : ZmmValue := zmmZero
  zmm11 : ZmmValue := zmmZero
  zmm12 : ZmmValue := zmmZero
  zmm13 : ZmmValue := zmmZero
  zmm14 : ZmmValue := zmmZero
  zmm15 : ZmmValue := zmmZero
  zmm16 : ZmmValue := zmmZero
  zmm17 : ZmmValue := zmmZero
  zmm18 : ZmmValue := zmmZero
  zmm19 : ZmmValue := zmmZero
  zmm20 : ZmmValue := zmmZero
  zmm21 : ZmmValue := zmmZero
  zmm22 : ZmmValue := zmmZero
  zmm23 : ZmmValue := zmmZero
  zmm24 : ZmmValue := zmmZero
  zmm25 : ZmmValue := zmmZero
  zmm26 : ZmmValue := zmmZero
  zmm27 : ZmmValue := zmmZero
  zmm28 : ZmmValue := zmmZero
  zmm29 : ZmmValue := zmmZero
  zmm30 : ZmmValue := zmmZero
  zmm31 : ZmmValue := zmmZero
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def RegZmms.get512 (s : RegZmms) (r : RegMm) : AvxWidth.W512.type := (match r with
  | .mm0  => s.zmm0  | .mm1  => s.zmm1  | .mm2  => s.zmm2  | .mm3  => s.zmm3
  | .mm4  => s.zmm4  | .mm5  => s.zmm5  | .mm6  => s.zmm6  | .mm7  => s.zmm7
  | .mm8  => s.zmm8  | .mm9  => s.zmm9  | .mm10 => s.zmm10 | .mm11 => s.zmm11
  | .mm12 => s.zmm12 | .mm13 => s.zmm13 | .mm14 => s.zmm14 | .mm15 => s.zmm15
  | .mm16 => s.zmm16 | .mm17 => s.zmm17 | .mm18 => s.zmm18 | .mm19 => s.zmm19
  | .mm20 => s.zmm20 | .mm21 => s.zmm21 | .mm22 => s.zmm22 | .mm23 => s.zmm23
  | .mm24 => s.zmm24 | .mm25 => s.zmm25 | .mm26 => s.zmm26 | .mm27 => s.zmm27
  | .mm28 => s.zmm28 | .mm29 => s.zmm29 | .mm30 => s.zmm30 | .mm31 => s.zmm31)

def RegZmms.set512 (regs : RegZmms) (r : RegMm) (v : AvxWidth.W512.type) : RegZmms :=
  match r with
  | .mm0  => { regs with zmm0  := v } | .mm1  => { regs with zmm1  := v }
  | .mm2  => { regs with zmm2  := v } | .mm3  => { regs with zmm3  := v }
  | .mm4  => { regs with zmm4  := v } | .mm5  => { regs with zmm5  := v }
  | .mm6  => { regs with zmm6  := v } | .mm7  => { regs with zmm7  := v }
  | .mm8  => { regs with zmm8  := v } | .mm9  => { regs with zmm9  := v }
  | .mm10 => { regs with zmm10 := v } | .mm11 => { regs with zmm11 := v }
  | .mm12 => { regs with zmm12 := v } | .mm13 => { regs with zmm13 := v }
  | .mm14 => { regs with zmm14 := v } | .mm15 => { regs with zmm15 := v }
  | .mm16 => { regs with zmm16 := v } | .mm17 => { regs with zmm17 := v }
  | .mm18 => { regs with zmm18 := v } | .mm19 => { regs with zmm19 := v }
  | .mm20 => { regs with zmm20 := v } | .mm21 => { regs with zmm21 := v }
  | .mm22 => { regs with zmm22 := v } | .mm23 => { regs with zmm23 := v }
  | .mm24 => { regs with zmm24 := v } | .mm25 => { regs with zmm25 := v }
  | .mm26 => { regs with zmm26 := v } | .mm27 => { regs with zmm27 := v }
  | .mm28 => { regs with zmm28 := v } | .mm29 => { regs with zmm29 := v }
  | .mm30 => { regs with zmm30 := v } | .mm31 => { regs with zmm31 := v }

def RegZmms.get (s : RegZmms) {w} (r : AvxReg w) : w.type :=
  (s.get512 r.base).take w.bits

def RegZmms.set (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v
  | .ymm r => s.set512 r (v.zeroExtend _)
  | .xmm r => s.set512 r (v.zeroExtend _)

def RegZmms.setLegacy (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v  -- impossible
  | .ymm r => s.set512 r ((s.get512 r).replaceLow v)  -- impossible
  | .xmm r => s.set512 r ((s.get512 r).replaceLow v)

@[kstep]
def BitVec.toAddressSize [address_size: AddressSize] (w: BitVec 64): BitVec address_size.address_size.bits :=
  w.take address_size.address_size.bits

-- TODO: consider adding a `split` helper to switch representations between
-- u128, 4xu32, etc.
def BitVec.packedBinOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c) (a b : BitVec w) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a -- Fallback/Base case (w = 0 or invalid chunk size)
  else
    -- Extract the lowest chunk
    let a_low := a.take c
    let b_low := b.take c
    let res_low := op a_low b_low

    -- Recursively process the remaining high bits
    let a_high := a.drop c
    let b_high := b.drop c
    let res_high := BitVec.packedBinOp c op a_high b_high

    -- Recombine: res_high is the high part, res_low is the low part
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

def BitVec.toFloat32 (v : BitVec 32) : Float32 :=
  Float32.ofBits (UInt32.ofBitVec v)

def Float32.toBitVec (f : Float32) : BitVec 32 :=
  UInt32.toBitVec (Float32.toBits f)

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev DataMem := Mem 64
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  zmms : RegZmms := {}
  status : StatusFlags := .mk false false false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

-- We only allow nondeterministic choices for a fixed set of types.
class inductive NondetSupportingType : Type -> Type
  | bitvec (w : Width) : NondetSupportingType w.type
  | avx_bitvec (aw : AvxWidth) : NondetSupportingType aw.type
  | bool : NondetSupportingType Bool
  | statusFlags : NondetSupportingType StatusFlags

def NondetSupportingType.from_hash {α} [t : NondetSupportingType α] (h : UInt64) : α :=
  match t with
  | .bool => h % 2 != 0
  | .statusFlags => let h := h.toBitVec; (.mk h[0] h[1] h[2] h[3] h[4] h[5])
  | .bitvec w => h.toBitVec.setWidth w.bits
  | .avx_bitvec w => h.toBitVec.setWidth w.bits

instance (w : Width) : NondetSupportingType w.type := .bitvec w
instance (w : AvxWidth) : NondetSupportingType w.type := .avx_bitvec w
instance : NondetSupportingType Bool := .bool
instance : NondetSupportingType StatusFlags := .statusFlags

/-- The instruction effect tree: a computation that reads and writes machine
state, requests access checks, draws nondeterministic values, or fails,
producing a result of the given type. -/
inductive Effects (α : Type) : Type 1
  | done (a : α)
  | unimplemented (msg : String)
  | gp_unaligned (addr : BitVec 64) (w : Nat)
  -- loads and stores *outside* the data memory, eg. MMIO, might still affect the data memory:
  -- for instance, MMIO reads/writes at certain device register addresses might change what
  -- data memory the process logically owns vs what memory is owned by devices
  | nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width)
      (ret : w.type → DataMem → Effects α)
  | nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type)
      (ret : DataMem → Effects α)
  | undefined {β : Type} [NondetSupportingType β] (ret : β → Effects α)
  | require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects α)
  | require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects α)
  | require_exec_access (p : Std.Rco Int64) (ok : Unit → Effects α)
export Effects (unimplemented nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access)

def Effects.bind {α β : Type} : Effects α → (α → Effects β) → Effects β
  | .done a, k => k a
  | .unimplemented msg, _ => .unimplemented msg
  | .gp_unaligned addr w, _ => .gp_unaligned addr w
  | .nonmem_load dmem addr w ret, k =>
      .nonmem_load dmem addr w fun v dmem => (ret v dmem).bind k
  | .nonmem_store dmem addr v ret, k =>
      .nonmem_store dmem addr v fun dmem => (ret dmem).bind k
  | @Effects.undefined _ γ inst ret, k =>
      @Effects.undefined _ γ inst fun v => (ret v).bind k
  | .require_read_access addr w ok, k =>
      .require_read_access addr w fun u => (ok u).bind k
  | .require_write_access addr w ok, k =>
      .require_write_access addr w fun u => (ok u).bind k
  | .require_exec_access p ok, k =>
      .require_exec_access p fun u => (ok u).bind k

instance : Monad Effects where
  pure := .done
  bind := .bind

/-- A nondeterministically chosen value for use in `do` notation. -/
@[kstep] def Effects.undef {β : Type} [NondetSupportingType β] : Effects β :=
  .undefined .done

@[simp] theorem Effects.pure_eq {α : Type} (a : α) :
    (pure a : Effects α) = .done a := rfl

@[simp] theorem Effects.bind_eq {α β : Type} (m : Effects α) (k : α → Effects β) :
    m >>= k = m.bind k := rfl

theorem Effects.bind_done {α : Type} (m : Effects α) : m.bind .done = m := by
  induction m <;> simp [Effects.bind, *]

theorem Effects.bind_assoc {α β γ : Type} (m : Effects α)
    (k₁ : α → Effects β) (k₂ : β → Effects γ) :
    (m.bind k₁).bind k₂ = m.bind fun a => (k₁ a).bind k₂ := by
  induction m <;> simp [Effects.bind, *]

instance : LawfulMonad Effects :=
  LawfulMonad.mk'
    (id_map := Effects.bind_done)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := Effects.bind_assoc)

def Effects.exec {α : Type} (entropy : UInt64) : Effects α → Except String α
  | .done a => .ok a
  | .unimplemented msg => .error msg
  | .gp_unaligned addr w =>
      .error s!"#GP: Memory op at {repr addr} did not have mandatory alignment of {w}"
  | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
  | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
  | @Effects.undefined _ _ inst ret => (ret (inst.from_hash entropy)).exec entropy
  | .require_read_access _ _ ok => (ok ()).exec entropy
  | .require_write_access _ _ ok => (ok ()).exec entropy
  | .require_exec_access _ ok => (ok ()).exec entropy

/-- How one instruction transfers control: fall through, or jump to `target`. -/
inductive Ctrl : Type
  | next
  | jmp (target : Int64)
  deriving Repr, BEq, DecidableEq

-- the unused `Std.Rco Int64` argument and the unmodified `MachineData` return
-- value are present for uniformity with RegOrMem.interp
@[kstep] def Reg.interp {w} (r : Reg w) (s : MachineData) (_ : Std.Rco Int64) :
    Effects (w.type × MachineData) :=
  .done (s.regs.get r, s)

-- An MMIO load may return an updated data memory, for example when a device
-- transfers ownership of a buffer back to the CPU.
def MachineData.load
  (s : MachineData) (addr : BitVec 64) (w : Width) : Effects (w.type × MachineData) :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i => .done (.ofInt _ i, s)
    | .none => nonmem_load s.dmem addr w (fun v dmem => .done (v, { s with dmem })))

-- Alternatively, we could define this in terms of BitVecs without %:
-- (addr &&& BitVec.ofNat 64 (bytes - 1)) == 0#64
def isAligned (bytes : Nat) (addr : BitVec 64) : Bool :=
  addr.toNat % bytes == 0

-- Legacy SSE instructions are generally stricter about alignment requirements,
-- while AVX (VEX-encoded) instructions can mostly deal with unaligned
-- addresses (https://discourse.llvm.org/t/memory-alignment-model-on-avx-avx2-and-avx-512-targets/34705).
-- For this reason we default checkAlign to false.
def MachineData.loadAvx
  (s : MachineData) (addr : BitVec 64) (w : AvxWidth)
  (checkAlign : Bool := false) : Effects (w.type × MachineData) :=
  if checkAlign && !(isAligned w.bytes addr) then
    .gp_unaligned addr w.bytes
  else
    require_read_access addr .W64 (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some i => .done (.ofInt _ i, s)
      | .none => unimplemented "AVX nonmem load not supported")

def MachineData.store (s : MachineData) (addr : BitVec 64) {w : Width} (v : w.type) : Effects MachineData :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
        .done { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
    | .none => nonmem_store s.dmem addr v (fun dmem' => .done { s with dmem := dmem' }))

def MachineData.storeAvx (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (checkAlign : Bool := false) : Effects MachineData :=
  if checkAlign && !(isAligned w.bytes addr) then
    .gp_unaligned addr w.bytes
  else
    require_write_access addr .W64 (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some _ =>
          .done { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
      | .none => unimplemented "AVX nonmem store not supported")

class Labels where label : Label → Int64
export Labels (label)

@[kstep] def ConstExpr.interp [Labels] : ConstExpr → Std.Rco _root_.Int64 → _root_.Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p

@[kstep] def AddrExpr.interp [Labels] [address_size : AddressSize] (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) :=
  let base := match a.base with
              | .some (.reg r) => (s.get64 r).toAddressSize.signed
              | .some .rip => p.upper.toInt
              | .none => 0
  let idx := match a.idx with
             | .some ⟨r, c⟩ => (s.get64 r).toAddressSize.signed * c.bytes
             | .none => 0
  BitVec.ofInt address_size.address_size.bits (base + idx + (a.disp.interp p).toInt)

@[kstep] def RegOrMem.interp {w} [Labels] [AddressSize]
  (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64) : Effects (w.type × MachineData) :=
match o with
  | .reg r => .done (s.regs.get r, s)
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) w

def AvxRegOrMem.interp {w} [Labels] [AddressSize]
  (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (checkAlign : Bool := false) : Effects (w.type × MachineData) :=
match o with
  | .avx r => .done (s.zmms.get r, s)
  | .mem a => s.loadAvx ((a.interp s.regs p).zeroExtend _) w checkAlign

@[kstep] def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.setAvxReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.set r v }

def MachineData.setAvxLegacyReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.setLegacy r v }

@[kstep] def MachineData.set {w} [Labels] [AddressSize] (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64) : Effects MachineData :=
  match d with
  | .reg r => .done (s.setReg r v)
  | .mem a => s.store ((a.interp s.regs p).zeroExtend _) v

def MachineData.setAvx {aw} [Labels] [AddressSize] (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64) (checkAlign : Bool := false) : Effects MachineData :=
match d with
  | .avx r => .done (s.setAvxReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v checkAlign

def MachineData.setAvxLegacy {w} [Labels] [AddressSize] (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) (checkAlign : Bool := false) : Effects MachineData :=
match d with
  | .avx r => .done (s.setAvxLegacyReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v checkAlign

@[kstep] def Operand.interp {w} [Labels] [AddressSize]
  (o : Operand w) (s : MachineData) (p : Std.Rco Int64) : Effects (w.type × MachineData) :=
  match o with
  | regOrMem rm => rm.interp s p
  | .imm v => .done ((v.interp p).toBitVec.truncate _, s)
  -- we rely on assemblers erroring out on too-large immediates in uniform ops

def AvxOperand.interp {aw} [Labels] [AddressSize]
  (o : AvxOperand aw) (s : MachineData) (p : Std.Rco Int64)
  (checkAlign : Bool := false) : Effects (aw.type × MachineData) :=
match o with
  | regOrMem rm => rm.interp s p checkAlign

@[kstep] def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .z  => s.zf | .nz => !s.zf | .c  => s.cf | .nc => !s.cf
  | .a  => !s.cf && !s.zf | .be => s.cf || s.zf
  | .l => s.sf != s.of | .le => (s.sf != s.of) || s.zf

@[kstep] def ShiftCountExpr.interp [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) := match c with
  | .cl => s.regs.rcx.toBitVec.take 8
  | .imm8 v => (v.interp p).toBitVec.take _
@[kstep] def ShiftCountExpr.interpMasked [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width) : Nat :=
  (c.interp s p).toNat &&& match w with | .W64 => 0x3f | _ => 0x1f -- "masked to 5 bits (or 6 bits with a 64-bit operand)"

def RelRegOrMem.interp [Labels] [AddressSize]
  (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64) : Effects (BitVec 64 × MachineData) :=
  match o with
  | .rel c => .done ((p.upper + c.interp p).toBitVec, s)
  | .reg r => .done (s.regs.get r, s)
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) .W64

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

@[kstep] def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { pf := (result.take 8).cpop_ % 2 == BitVec.zero _
    zf := result == BitVec.zero _
    sf := result.msb, cf := f.cf, af := f.af, of := f.of }



set_option maxHeartbeats 1000000
@[kstep] def Operation.interp [Labels] [address_size : AddressSize]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData) : Effects (MachineData × Ctrl) :=
  match (generalizing := false) (motive := Operation w → Effects (MachineData × Ctrl)) i with
  | .mov dst src => do
    let (val, s) ← src.interp s p
    let s ← s.set dst val p
    pure (s, .next)
  | .movsx dst src => do
    let (val, s) ← src.interp s p
    let s ← s.set dst (val.signExtend _) p
    pure (s, .next)
  | .movzx dst src => do
    let (val, s) ← src.interp s p
    let s ← s.set dst (val.zeroExtend _) p
    pure (s, .next)
  | .push src => do
    let (v, s) ← src.interp s p
    let rsp := s.regs.get64 .rsp - w.bytesv
    let s ← { s with regs := s.regs.set64 .rsp rsp }.store rsp v
    pure (s, .next)
  | .pop dst => do
    let rsp := s.regs.get64 .rsp
    let (val, s) ← s.load rsp w
    let s := { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) }
    let s ← s.set dst val p
    pure (s, .next)
  | .setcc cc dst => do
    let s ← s.set dst (cc.interp s.status) p
    pure (s, .next)
  | .cmovcc cc dst src => do
    let (src, s) ← src.interp s p
    let v := if cc.interp s.status then src else s.regs.get dst
    pure (s.setReg dst v, .next)
-- Arithmetic
  | .lea dst src => .done (s.setReg dst ((src.interp s.regs p).zeroExtend _), .next)
  | .add dst src => do
    let (a, s) ← src.interp s p
    let (b, s) ← dst.interp s p
    let v := a + b
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .adc dst src => do
    let (a, s) ← src.interp s p
    let (b, s) ← dst.interp s p
    let c := s.status.cf
    let v := a + b + c
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned + c
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
      of := v.signed != a.signed + b.signed + c }
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .adcx dst src => do
    let (a, s) ← src.interp s p
    let (b, s) ← dst.interp s p
    let v := a + b + s.status.cf
    let cf := v.unsigned != a.unsigned + b.unsigned + s.status.cf
    pure ({ s with regs := s.regs.set dst v, status := { s.status with cf := cf }}, .next)
  | .adox dst src => do
    let (a, s) ← src.interp s p
    let (b, s) ← dst.interp s p
    let v := a + b + s.status.of
    let of := v.unsigned != a.unsigned + b.unsigned + s.status.of
    pure ({ s with regs := s.regs.set dst v, status := { s.status with of := of }}, .next)
  | .inc dst => do
    let (a, s) ← dst.interp s p
    let v := a + 1
    let status := StatusFlags.from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
      of := v.signed != a.signed + 1 }
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .dec dst => do
    let (a, s) ← dst.interp s p
    let v := a - 1
    let status := StatusFlags.from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
      of := v.signed != a.signed - 1 }
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .neg dst => do
    let (b, s) ← dst.interp s p
    let v := -b
    let status := StatusFlags.from_result v {
      cf := b != 0
      af := (b.take 4) != 0,
      of := v.signed != - b.signed }
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .sub dst src => do
    let (a, s) ← src.interp s p
    let (b, s) ← dst.interp s p
    let v := b - a
    let status := StatusFlags.from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
      of := v.signed != b.signed - a.signed }
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .sbb dst src => do
    let (a, s) ← src.interp s p
    let (b, s) ← dst.interp s p
    let c := s.status.cf
    let v := b - a - c
    let status := StatusFlags.from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned - c
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - c,
      of := v.signed != b.signed - a.signed - c }
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .cmp a b => do
    let (a, s) ← a.interp s p
    let (b, s) ← b.interp s p
    let v := a - b
    let status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned - b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := v.signed != a.signed - b.signed }
    pure ({ s with status }, .next)
  | .mul src => do
    let a := s.regs.get (Reg.low .rax w)
    let (b, s) ← src.interp s p
    let v := a * b
    let vn := a.unsigned * b.unsigned
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (.ofInt _ vn)
      else (s.setReg (.low .rax w) v).setReg (.low .rdx w) (.ofInt _ (vn >>> w.bits))
    let sf : Bool ← Effects.undef
    let zf : Bool ← Effects.undef
    let af : Bool ← Effects.undef
    let pf : Bool ← Effects.undef
    pure ({ s with status := { cf := v.unsigned != vn, pf, af, zf, sf, of := v.unsigned != vn }}, .next)
  | .mulx r_hi r_lo src1 => do
    let (a, s) ← src1.interp s p
    let b := s.regs.get (.low .rdx w)
    let v := a.unsigned * b.unsigned
    let s := s.setReg r_lo (.ofInt _ v) -- if r_hi = r_li, hi is written:
    let s := s.setReg r_hi (.ofInt _ (v >>> w.bits))
    pure (s, .next)
  -- imul1 and imul collectively describe variants of the same
  -- syntax level `imul` instruction, where imul1 is the 1-operand case
  | .imul1 src => do
    let a := s.regs.get (Reg.low .rax w)
    let (b, s) ← src.interp s p
    let v := a.toInt * b.toInt
    let s := if w == .W8 then
      s.setReg (.low .rax .W16) (BitVec.ofInt 16 v)
    else
      let result := BitVec.ofInt (w.bits * 2) v
      let low := result.take w.bits
      let high := (result.drop w.bits).setWidth _
      (s.setReg (.low .rax w) low).setReg (.low .rdx w) high
    let sf : Bool ← Effects.undef
    let zf : Bool ← Effects.undef
    let af : Bool ← Effects.undef
    let pf : Bool ← Effects.undef
    let low := BitVec.ofInt w.bits v
    let cf := v != low.toInt
    pure ({ s with status := { cf := cf, pf, af, zf, sf, of := cf }}, .next)
  | .imul dst src1 src2 => do
    let (a, s) ← src1.interp s p
    let (b, s) ← src2.interp s p
    let v := a * b
    let s ← s.set (match (generalizing := false) (motive := Option (RegOrMem w) → RegOrMem w)
             dst with | .some dst => dst | _ => src1) v p
    let cf := v.signed != a.signed * b.signed
    let sf : Bool ← Effects.undef
    let zf : Bool ← Effects.undef
    let af : Bool ← Effects.undef
    let pf : Bool ← Effects.undef
    pure ({ s with status := { cf := cf, pf, af, zf, sf, of := cf }}, .next)
-- Bitwise
  | .test a b => do
    let (a, s) ← a.interp s p
    let (b, s) ← b.interp s p
    let v := a &&& b
    let af : Bool ← Effects.undef
    let status := StatusFlags.from_result v { cf := false, af, of := false}
    pure ({ s with status}, .next)
  | .and dst src | .or dst src | .xor dst src => do
    let (a, s) ← dst.interp s p
    let (b, s) ← src.interp s p
    let v := match i with | .and _ _ => a &&& b | .or _ _ => a ||| b | _ => a ^^^ b
    let af : Bool ← Effects.undef
    let status := StatusFlags.from_result v { cf := false, of := false, af }
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .not dst => do
    let (a, s) ← dst.interp s p
    let v := ~~~a
    let s ← s.set dst v p
    pure (s, .next)
  | .shl dst count => do
    let (a, s) ← dst.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let v := a <<< count
    let af : Bool ← Effects.undef
    let cf : Bool ← if count < w.bits then pure (a <<< (count-1)).msb else Effects.undef
    let of : Bool ← if count == 1 then pure (v.msb != a.msb) else Effects.undef
    let s ← { s with status := .from_result v { s.status with cf, af, of } }.set dst v p
    pure (s, .next)
  | .shr dst count => do
    let (a, s) ← dst.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let v := a.ushiftRight count
    let af : Bool ← Effects.undef
    let cf : Bool ← if count < w.bits then pure (a.getLsbD (count-1)) else Effects.undef
    let of : Bool ← if count == 1 then pure a.msb else Effects.undef
    let s ← { s with status := .from_result v { s.status with cf, af, of } }.set dst v p
    pure (s, .next)
  | .sar dst count => do
    let (a, s) ← dst.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let v := a.sshiftRight count
    let af : Bool ← Effects.undef
    let cf : Bool ← if count < w.bits then pure (a.getLsbD (count-1)) else Effects.undef
    let of : Bool ← if count == 1 then pure false else Effects.undef
    let s ← { s with status := .from_result v { s.status with cf, af, of } }.set dst v p
    pure (s, .next)
  | .shrd dst src count => do
    let (a, s) ← dst.interp s p
    let (b, s) ← src.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let v := (((b.append a) >>> count).take w.bits).setWidth _
    let status : StatusFlags ←
      if count >= w.bits then Effects.undef else do
        let cf := a.getLsbD (count-1)
        let af : Bool ← Effects.undef
        let of : Bool ← if count == 1 then pure (v.msb != a.msb) else Effects.undef
        pure (.from_result v { cf, af, of})
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .shld dst src count => do
    let (a, s) ← dst.interp s p
    let (b, s) ← src.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let v := (((a.append b) <<< count).drop w.bits).setWidth _
    let status : StatusFlags ←
      if count >= w.bits then Effects.undef else do
        let cf := (a <<< (count-1)).msb
        let af : Bool ← Effects.undef
        let of : Bool ← if count == 1 then pure (v.msb != a.msb) else Effects.undef
        pure (.from_result v { cf, af, of})
    let s ← { s with status }.set dst v p
    pure (s, .next)
  | .rol dst count => do
    let (a, s) ← dst.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let v := a.rotateLeft count
    let cf := v.getLsbD 0
    let of : Bool ← if count == 1 then pure (v.msb != a.msb) else Effects.undef
    let s ← { s with status := { s.status with cf, of } }.set dst v p
    pure (s, .next)
  | .ror dst count => do
    let (a, s) ← dst.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let v := a.rotateRight count
    let cf := v.msb
    let of : Bool ← if count == 1 then pure (v.msb != a.msb) else Effects.undef
    let s ← { s with status := { s.status with cf, of } }.set dst v p
    pure (s, .next)
  | .rcr dst count => do
    let (a, s) ← dst.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let t := (BitVec.ofBool s.status.cf ++ a).rotateRight count
    let (cf, v) := (t.msb, t.take w.bits)
    let of : Bool ← if count == 1 then pure (v.msb != a.msb) else Effects.undef
    let s ← { s with status := { s.status with cf, of } }.set dst v p
    pure (s, .next)
  | .rcl dst count => do
    let (a, s) ← dst.interp s p
    let count := count.interpMasked s p w
    if count == 0 then pure (s, .next) else do
    let t := (BitVec.ofBool s.status.cf ++ a).rotateLeft count
    let (cf, v) := (t.msb, t.take w.bits)
    let of : Bool ← if count == 1 then pure (v.msb != a.msb) else Effects.undef
    let s ← { s with status := { s.status with cf, of } }.set dst v p
    pure (s, .next)
  | .bswap dst =>
    let a := s.regs.get dst
    match (generalizing := false) (motive := Width → Effects (MachineData × Ctrl)) w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      .done (s.setReg dst (v.setWidth _), .next)
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      .done (s.setReg dst (v.setWidth _), .next)
    | _ => do
      let v ← Effects.undef
      pure (s.setReg dst v, .next)
  | .jcc cc l =>
    if cc.interp s.status
    then .done (s, .jmp (label l))
    else .done (s, .next)
  | .jmp tgt => do
    let (a, s) ← tgt.interp s p
    pure (s, .jmp (.ofBitVec a))
  | .call tgt => do
    let (a, s) ← tgt.interp s p
    let rsp := s.regs.get64 .rsp - Width.W64.bytesv
    let s ← { s with regs := s.regs.set64 .rsp rsp }.store rsp (w:=.W64) p.upper.toBitVec
    pure (s, .jmp (.ofBitVec a))
  | .ret => do
    let rsp := s.regs.get64 .rsp
    let (ra, s) ← s.load rsp .W64
    pure ({ s with regs := s.regs.set64 .rsp (rsp + 8) }, .jmp (.ofBitVec ra))
  | nop _ | nopalign _ _ => .done (s, .next)

-- AVX Operations Interpreter
def AvxOperation.interp [Labels] [address_size : AddressSize]
  {w} (i : AvxOperation w) (p : Std.Rco Int64) (s : MachineData) : Effects (MachineData × Ctrl) :=
match i with
  | .movups dst src => do
    let (val, s) ← src.interp s p
    let s ← s.setAvxLegacy dst val p
    pure (s, .next)
  | .vmovups dst src => do
    let (val, s) ← src.interp s p
    let s ← s.setAvx dst val p
    pure (s, .next)
  | .movaps dst src => do
    let (val, s) ← src.interp s p (checkAlign := true)
    let s ← s.setAvxLegacy dst val p (checkAlign := true)
    pure (s, .next)
  -- TODO: MXCSR
  | .subps dst src => do
    let (a, s) ← src.interp s p (checkAlign := true)
    let (b, s) ← dst.interp s p
    let v := BitVec.packedBinOp 32 (fun dst_chunk src_chunk =>
      let f_dst := BitVec.toFloat32 dst_chunk
      let f_src := BitVec.toFloat32 src_chunk
      Float32.toBitVec (f_dst - f_src)
    ) b a
    let s ← s.setAvxLegacy dst v p
    pure (s, .next)
  | .addps dst src => do
    let (a, s) ← src.interp s p (checkAlign := true)
    let (b, s) ← dst.interp s p
    let v := BitVec.packedBinOp 32 (fun dst_chunk src_chunk =>
      let f_dst := BitVec.toFloat32 dst_chunk
      let f_src := BitVec.toFloat32 src_chunk
      Float32.toBitVec (f_dst + f_src)
    ) b a
    let s ← s.setAvxLegacy dst v p
    pure (s, .next)

@[kstep] def Instr.interp [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64) : Effects (MachineData × Ctrl) :=
  require_exec_access p (fun _unit =>
    match i with
      | .regular addr_sz op_sz op =>
          Operation.interp (w := op_sz) (address_size := .mk addr_sz) op p s
      | .avx addr_sz op_sz op =>
          AvxOperation.interp (w := op_sz) (address_size := .mk addr_sz) op p s
  )

@[kstep] def Directive.interp [Labels]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64) : Effects (MachineData × Ctrl) :=
  match d with
  | .label _ => .done (s, .next)
  | .instr i => i.interp s p
  | .byteArray _ => .unimplemented s!"Unimplemented: execution reached data block at {p.1}"

/-- How control leaves a list of directives. -/
inductive BlockExit : Type
  | fallthrough (next : Int64)
  | jump (target : Int64)
  deriving Repr, BEq, DecidableEq

/-- The program counter after the exit, forgetting how control got there. -/
@[kstep] def BlockExit.pc : BlockExit → Int64
  | .fallthrough next => next
  | .jump target => target

/-- Run directives in order until the list ends or an instruction jumps. -/
def Directives.interp [Labels]
  (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64) : Effects (MachineData × BlockExit) :=
  match ds with
  | [] => .done (s, .fallthrough pc)
  | (d, sz) :: ds => do
    let (s, c) ← d.interp s (.mk pc (pc+.ofNat sz))
    match c with
    | .next => interp ds s (pc+.ofNat sz)
    | .jmp target => pure (s, .jump target)

abbrev Layout := Kraken.Layout Directive

@[reducible]
def Executable.labels (e : Executable) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun (p, d, _) => if d = .label l then .some p else .none)).getD (-1) }

def Executable.directivesFromLabel (e : Executable) (l : Label) : List (Directive × Nat) :=
  e.2.dropWhile (·.1 != .label l)

abbrev MachineState := MachineData × Int64

/-- Execute one positive-sized instruction, together with any leading
zero-sized directives, passing the state and block exit to the continuation.
The block is delimited by the size table (`takeBlock`); on a layout whose
sizes wrap modulo 2^64 this can be a proper prefix of the directives whose
assigned address equals the pc. -/
def Executable.stepWithExit {α : Type} (e : Executable) (s : MachineState)
    (ret : MachineData → BlockExit → Effects α) : Effects α :=
  let := e.labels
  (Directives.interp (Kraken.Directives.takeBlock (e.directivesFromAddress s.2)) s.1 s.2).bind
    fun (s', ex) => ret s' ex

def Executable.step {α : Type} (e : Executable) (s : MachineState)
    (ret : MachineState → Effects α) : Effects α :=
  e.stepWithExit s (fun s' ex => ret (s', ex.pc))

/-- Run from the current address to the first taken jump or the end of the
listing. Derived from the same monadic core as `step`, with the exit's
program counter forgotten — behaviorally the semantics `Executable.eval`
and the specs have always had. -/
def Executable.straightline {α : Type} (e : Executable) (s : MachineState)
    (ret : MachineState → Effects α) : Effects α :=
  let := e.labels
  (Directives.interp (e.directivesFromAddress s.2) s.1 s.2).bind
    fun (s', ex) => ret (s', ex.pc)

-- -- Concrete evaluators for expedient testing

partial def Executable.eval (e : Executable) (s : MachineState) (until_ : MachineState → Bool) : Except String (MachineState) :=
  if until_ s then .ok s else handleEffects (Executable.straightline e s .done)
where
  handleEffects es :=
    match es with
    | .done s => eval e s until_
    | .unimplemented msg => .error msg
    | .gp_unaligned addr w => .error s!"#GP: Memory op at {repr addr} did not have mandatory alignment of {w}"
    | .require_read_access _ _ ok => handleEffects (ok ())
    | .require_write_access _ _ ok => handleEffects (ok ())
    | .require_exec_access _ ok => handleEffects (ok ())
    | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | @Effects.undefined _ _ t cont => handleEffects (cont (t.from_hash (hash s.1.regs)))

def Directive.fakeSize (hashOfProgram : UInt64) (d : Directive) : Nat :=
  match d with
  | .label _ => 0
  | .instr (.regular _ _ (.nop sz)) => sz -- may be zero
  | .instr i => (1 + hash (hashOfProgram, i) % 15).toNat
  | .byteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize h }
  layout prog

abbrev eval [layout : Layout] (prog : Program) := Executable.eval (layout prog)

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := {rsp := 0x100} }
  (Executable.eval exe (data, start) (fun (_, pc) => pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)
