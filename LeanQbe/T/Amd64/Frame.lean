module

public import LeanQbe.T.Amd64.Base
public import LeanQbe.T.IselStepAttr

/-!
# SysV x64 Frame ISA (`T11b`)

Target-level `FrameIsa` instantiation for System V AMD64 (`x64Frame`):
* Stack pointer `rsp`, scratch `[r10, r11]`, caller-saved allocatable `[rax, rcx, rdx, rsi, rdi,
  r8, r9]`, callee-saved `[rbx, rbp, r12, r13, r14, r15]`, arg regs `[rdi, rsi, rdx, rcx, r8, r9]`,
  return regs `[rax, rdx, rcx, rsi, rdi, r8, r9]`, `raBytes := 8`, `bitWidths := [8, 16, 32, 64]`.
* `frameSize ns := 8 * ns + (if ns % 2 == 0 then 8 else 0)` (kernel-`rfl` via `==`, ensuring
  `frameSize ns % 16 = 8` so `(rsp - frameSize ns)` is 16-byte aligned at calls).
* `prologue`/`epilogue` and `slotSt`/`slotLd` use immediate operands when `< 2^31` and fall back
  to 64-bit `movabs $c, %r10` + register/indexed addressing for large frames/offsets (`≤ 2^64`).
* Unified `canonAbi`: `movzbl`/`movzwl`/`movl`/`[]` zero-extending low bits to 64 bits with
  `FlagMask.none`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

/-- Frame byte size for `ns` 8-byte slots, keeping `frameSize ns ≡ 8 (mod 16)` so `rsp` is
16-byte aligned at calls after the 8-byte return address is pushed. -/
def x64FrameSize (ns : Nat) : Nat :=
  8 * ns + (if ns % 2 == 0 then 8 else 0)

/-- Signed 32-bit nonnegative immediate fit (`< 2^31`), kernel-`rfl` via `Nat.blt`. -/
def x64FitsImm31 (n : Nat) : Bool :=
  Nat.blt n 0x80000000

/-- 64-bit x64 instruction constructor. -/
abbrev insI (op : Operation .W64) : Instr := .regular .W64 .W64 op

/-- 32-bit x64 instruction constructor (64-bit address size). -/
abbrev ins32I (op : Operation .W32) : Instr := .regular .W64 .W32 op

/-- `subq $c, %rsp`. -/
abbrev x64SubSpI (c : Int64) : Instr :=
  insI (.sub (.reg (q .rsp)) (.imm (.int64 c)))

/-- `subq $c, %rsp`. -/
def x64SubSpD (c : Int64) : Directive := .instr (x64SubSpI c)

/-- `addq $c, %rsp`. -/
abbrev x64AddSpI (c : Int64) : Instr :=
  insI (.add (.reg (q .rsp)) (.imm (.int64 c)))

/-- `addq $c, %rsp`. -/
def x64AddSpD (c : Int64) : Directive := .instr (x64AddSpI c)

/-- `movabs $c, %rd` (64-bit immediate move, preserving flags). -/
abbrev x64MoviI (rd : Reg64) (c : BitVec 64) : Instr :=
  insI (.mov (.reg (q rd)) (.imm (.int64 (Int64.ofBitVec c))))

/-- `movabs $c, %rd` (64-bit immediate move, preserving flags). -/
def x64MoviD (rd : Reg64) (c : BitVec 64) : Directive := .instr (x64MoviI rd c)

/-- `[rsp + off]`. -/
abbrev x64AtSp (off : Int64) : AddrExpr :=
  { base := some (.reg .rsp), idx := none, disp := .int64 off }

/-- `[rsp + r10]`. -/
abbrev x64AtSpR10 : AddrExpr :=
  { base := some (.reg .rsp), idx := some ⟨.r10, .W8⟩ }

/-- `movq %rv, off(%rsp)`. -/
abbrev x64StSpI (rv : Reg64) (off : Int64) : Instr :=
  insI (.mov (.mem (x64AtSp off)) (.reg (q rv)))

/-- `movq %rv, off(%rsp)`. -/
def x64StSpD (rv : Reg64) (off : Int64) : Directive := .instr (x64StSpI rv off)

/-- `movq off(%rsp), %rd`. -/
abbrev x64LdSpI (rd : Reg64) (off : Int64) : Instr :=
  insI (.mov (.reg (q rd)) (.mem (x64AtSp off)))

/-- `movq off(%rsp), %rd`. -/
def x64LdSpD (rd : Reg64) (off : Int64) : Directive := .instr (x64LdSpI rd off)

/-- Internal instruction stream for `x64Prologue`. -/
def x64PrologueIns (ns : Nat) : List Instr :=
  let sz := x64FrameSize ns
  if x64FitsImm31 sz then [x64SubSpI (Int64.ofNat sz)]
  else [x64MoviI .r10 (BitVec.ofNat 64 sz), insI (.sub (.reg (q .rsp)) (.reg (q .r10)))]

/-- Allocate `x64FrameSize ns` bytes on `%rsp`. -/
def x64Prologue (ns : Nat) : List Directive × FlagMask :=
  (emitClean (x64PrologueIns ns), maskAll)

/-- Internal instruction stream for `x64Epilogue`. -/
def x64EpilogueIns (ns : Nat) : List Instr :=
  let sz := x64FrameSize ns
  if x64FitsImm31 sz then [x64AddSpI (Int64.ofNat sz)]
  else [x64MoviI .r10 (BitVec.ofNat 64 sz), insI (.add (.reg (q .rsp)) (.reg (q .r10)))]

/-- Deallocate `x64FrameSize ns` bytes on `%rsp`. -/
def x64Epilogue (ns : Nat) : List Directive × FlagMask :=
  (emitClean (x64EpilogueIns ns), maskAll)

/-- Internal instruction stream for `x64SlotSt`. -/
def x64SlotStIns (i : Nat) (r : Reg64) : List Instr :=
  let off := 8 * i
  if x64FitsImm31 off then [x64StSpI r (Int64.ofNat off)]
  else [x64MoviI .r10 (BitVec.ofNat 64 off), insI (.mov (.mem x64AtSpR10) (.reg (q r)))]

/-- Store 64-bit register `r` into stack slot `i` (`[rsp + 8*i]`), preserving all flags. -/
def x64SlotSt (i : Nat) (r : Reg64) : List Directive :=
  emitClean (x64SlotStIns i r)

/-- Internal instruction stream for `x64SlotLd`. -/
def x64SlotLdIns (rd : Reg64) (i : Nat) : List Instr :=
  let off := 8 * i
  if x64FitsImm31 off then [x64LdSpI rd (Int64.ofNat off)]
  else [x64MoviI .r10 (BitVec.ofNat 64 off), insI (.mov (.reg (q rd)) (.mem x64AtSpR10))]

/-- Load stack slot `i` (`[rsp + 8*i]`) into 64-bit register `rd`, preserving all flags. -/
def x64SlotLd (rd : Reg64) (i : Nat) : List Directive :=
  emitClean (x64SlotLdIns rd i)

/-- Internal instruction stream for `x64CanonAbi`. -/
def x64CanonAbiIns (t : Ty) (r : Reg64) : List Instr :=
  match t with
  | .bool | .bits 8  => [ins32I (.movzx (.reg (d r)) (.reg (b8 r)))]
  | .bits 16         => [ins32I (.movzx (.reg (d r)) (.reg (h16 r)))]
  | .bits 32         => [ins32I (.mov (.reg (d r)) (.reg (d r)))]
  | _                => []

/-- Zero-extend low bits of `r` to 64 bits (`AbiGprHolds`), preserving all flags. -/
def x64CanonAbi (t : Ty) (r : Reg64) : List Directive × FlagMask :=
  (emitClean (x64CanonAbiIns t r), maskNone)

/-- `call sym`. -/
abbrev x64CallI (sym : Sym) : Instr :=
  insI (.call (.rel (.sub (.label sym) .after_current_instruction)))

/-- `call sym`. -/
def x64CallD (sym : Sym) : Directive := .instr (x64CallI sym)

/-- `jmp sym`. -/
abbrev x64JmpI (sym : Sym) : Instr :=
  insI (.jmp (.rel (.sub (.label sym) .after_current_instruction)))

/-- `jmp sym`. -/
def x64JmpD (sym : Sym) : Directive := .instr (x64JmpI sym)

/-- `ret`. -/
abbrev x64RetI : Instr := insI .ret

/-- `ret`. -/
def x64RetD : Directive := .instr x64RetI

/-- SysV x64 `FrameIsa` instance. -/
@[reducible] def x64Frame : FrameIsa Reg64 Directive where
  label := .label
  sp := .rsp
  scratch := x64Scratch
  allocatable := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]
  calleeSaved := [.rbx, .rbp, .r12, .r13, .r14, .r15]
  raRegs := []
  argRegs := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
  retRegs := [.rax, .rdx, .rcx, .rsi, .rdi, .r8, .r9]
  bitWidths := [8, 16, 32, 64]
  raBytes := 8
  frameSize := x64FrameSize
  prologue := x64Prologue
  epilogue := x64Epilogue
  slotSt := x64SlotSt
  slotLd := x64SlotLd
  canonAbi := x64CanonAbi
  call sym := emitClean [x64CallI sym]
  exitJmp sym := emitClean [x64JmpI sym]
  ret := emitClean [x64RetI]
  leafZeroFrame := true

/-- SysV x64 frame predicates (`Prop`-valued state/stack invariants, zero `*Lemmas*` imports). -/
@[reducible] def x64FramePreds : FramePreds x64Mach where
  RetAddr sp ra := cell64 sp ra.toBitVec
  raReg _ _ := True
  spEntry sp := (sp + 8#64).toNat % 16 = 0
  spOk _ := True
  Saved sp ra ns :=
    region (sp - BitVec.ofNat 64 (x64FrameSize ns) + BitVec.ofNat 64 (8 * ns))
      (x64FrameSize ns - 8 * ns) ⋆ cell64 sp ra.toBitVec

end LeanQbe.T.Amd64
