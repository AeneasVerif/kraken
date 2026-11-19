module

public import LeanQbe.T.Amd64.Base
public import LeanQbe.T.AbiLemmas

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

/-- `subq $c, %rsp`. -/
def x64SubSpD (c : Int64) : Directive :=
  ins (.sub (.reg (q .rsp)) (.imm (.int64 c)))

/-- `addq $c, %rsp`. -/
def x64AddSpD (c : Int64) : Directive :=
  ins (.add (.reg (q .rsp)) (.imm (.int64 c)))

/-- `movabs $c, %rd` (64-bit immediate move, preserving flags). -/
def x64MoviD (rd : Reg64) (c : BitVec 64) : Directive :=
  ins (.mov (.reg (q rd)) (.imm (.int64 (Int64.ofBitVec c))))

/-- `[rsp + off]`. -/
abbrev x64AtSp (off : Int64) : AddrExpr :=
  { base := some (.reg .rsp), idx := none, disp := .int64 off }

/-- `[rsp + r10]`. -/
abbrev x64AtSpR10 : AddrExpr :=
  { base := some (.reg .rsp), idx := some ⟨.r10, .W8⟩ }

/-- `movq %rv, off(%rsp)`. -/
def x64StSpD (rv : Reg64) (off : Int64) : Directive :=
  ins (.mov (.mem (x64AtSp off)) (.reg (q rv)))

/-- `movq off(%rsp), %rd`. -/
def x64LdSpD (rd : Reg64) (off : Int64) : Directive :=
  ins (.mov (.reg (q rd)) (.mem (x64AtSp off)))

/-- Allocate `x64FrameSize ns` bytes on `%rsp` (`subq $F, %rsp` or `movabs $F, %r10; subq %r10, %rsp`). -/
def x64Prologue (ns : Nat) : List Directive × FlagMask :=
  let sz := x64FrameSize ns
  if x64FitsImm31 sz then
    ([x64SubSpD (Int64.ofNat sz)], maskAll)
  else
    ([x64MoviD .r10 (BitVec.ofNat 64 sz), ins (.sub (.reg (q .rsp)) (.reg (q .r10)))], maskAll)

/-- Deallocate `x64FrameSize ns` bytes on `%rsp` (`addq $F, %rsp` or `movabs $F, %r10; addq %r10, %rsp`). -/
def x64Epilogue (ns : Nat) : List Directive × FlagMask :=
  let sz := x64FrameSize ns
  if x64FitsImm31 sz then
    ([x64AddSpD (Int64.ofNat sz)], maskAll)
  else
    ([x64MoviD .r10 (BitVec.ofNat 64 sz), ins (.add (.reg (q .rsp)) (.reg (q .r10)))], maskAll)

/-- Store 64-bit register `r` into stack slot `i` (`[rsp + 8*i]`), preserving all flags. -/
def x64SlotSt (i : Nat) (r : Reg64) : List Directive :=
  let off := 8 * i
  if x64FitsImm31 off then
    [x64StSpD r (Int64.ofNat off)]
  else
    [x64MoviD .r10 (BitVec.ofNat 64 off), ins (.mov (.mem x64AtSpR10) (.reg (q r)))]

/-- Load stack slot `i` (`[rsp + 8*i]`) into 64-bit register `rd`, preserving all flags. -/
def x64SlotLd (rd : Reg64) (i : Nat) : List Directive :=
  let off := 8 * i
  if x64FitsImm31 off then
    [x64LdSpD rd (Int64.ofNat off)]
  else
    [x64MoviD .r10 (BitVec.ofNat 64 off), ins (.mov (.reg (q rd)) (.mem x64AtSpR10))]

/-- Zero-extend low bits of `r` to 64 bits (`AbiGprHolds`), preserving all flags. -/
def x64CanonAbi (t : Ty) (r : Reg64) : List Directive × FlagMask :=
  match t with
  | .bool | .bits 8  => ([ins32 (.movzx (.reg (d r)) (.reg (b8 r)))], maskNone)
  | .bits 16         => ([ins32 (.movzx (.reg (d r)) (.reg (h16 r)))], maskNone)
  | .bits 32         => ([ins32 (.mov (.reg (d r)) (.reg (d r)))], maskNone)
  | _                => ([], maskNone)

/-- `call sym`. -/
def x64CallD (sym : Sym) : Directive :=
  ins (.call (.rel (.sub (.label sym) .after_current_instruction)))

/-- `jmp sym`. -/
def x64JmpD (sym : Sym) : Directive :=
  ins (.jmp (.rel (.sub (.label sym) .after_current_instruction)))

/-- `ret`. -/
def x64RetD : Directive :=
  ins .ret

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
  call sym := [x64CallD sym]
  exitJmp sym := [x64JmpD sym]
  ret := [x64RetD]

end LeanQbe.T.Amd64
