module

public import Kraken.X64.Semantics
public import LeanQbe.Abi

/-!
# x64 snippets (QBE `amd64/targ.c`, `amd64/emit.c` in spirit)

The executable part of the x64 target: register sets of the System V ABI and one snippet per
thing the lowering emits, as Kraken x64 directives. The step lemmas and the `Target` instance are
in `TargLemmas.lean`.

Register roles:

* scratch: `r10`, `r11` (caller-saved, not used for arguments or results);
* allocatable: the remaining caller-saved registers `rax rcx rdx rsi rdi r8 r9` (leaf functions do
  not save callee-saved registers yet);
* arguments `rdi rsi rdx rcx r8 r9`, results `rax rdx`;
* callee-saved `rbx rbp r12 r13 r14 r15`; stack pointer `rsp`.

Supported in version 0.1 (everything else makes the snippet `none`, so the lowering fails):

* `op`: `copy` at both classes; `add sub and or xor` at both classes, operands registers or
  immediates (both operands go through the scratch registers, so any destination is allowed);
* `load`: `loadl` at class `l` from a register address;
* `store`: `storel` of a register or immediate to a register address.
-/

@[expose] public section

namespace LeanQbe.Amd64

/-- A 64-bit instruction with 64-bit addressing. -/
abbrev ins (op : Operation .W64) : Directive := .instr (.regular .W64 .W64 op)

/-- A 32-bit instruction with 64-bit addressing. -/
abbrev ins32 (op : Operation .W32) : Directive := .instr (.regular .W64 .W32 op)

/-- The 64-bit view of a register. -/
abbrev q (r : Reg64) : Reg .W64 := .low r .W64

/-- The 32-bit view of a register. -/
abbrev d (r : Reg64) : Reg .W32 := .low r .W32

/-- `[r]`: memory operand with base `r`, no index, displacement 0. -/
abbrev atReg (r : Reg64) : AddrExpr := { base := some (.reg r), idx := none }

/-- `mov %rs, %rd` -/
def movD (rd rs : Reg64) : Directive := ins (.mov (.reg (q rd)) (.reg (q rs)))

/-- `mov %rs, %rd` -/
def mov (rd rs : Reg64) : List Directive := [movD rd rs]

/-- `mov $c, %rd` (any 64-bit immediate; the assembler picks `movabs` when needed). -/
def moviD (rd : Reg64) (c : BitVec 64) : Directive :=
  ins (.mov (.reg (q rd)) (.imm (.int64 (Int64.ofBitVec c))))

/-- `mov $c, %rd` -/
def movi (rd : Reg64) (c : BitVec 64) : List Directive := [moviD rd c]

/-- Put an operand into register `t`. -/
def argTo (t : Reg64) : Arg Reg64 → Directive
  | .var r => movD t r
  | .imm c => moviD t c

/-- `op{k} %r10, %r11`: `r11 := r11 op r10` at class `k` (class `w` zero-extends). -/
def binIns : Cls → BinOp → Option Directive
  | .l, .add => some (ins (.add (.reg (q .r11)) (.reg (q .r10))))
  | .l, .sub => some (ins (.sub (.reg (q .r11)) (.reg (q .r10))))
  | .l, .and => some (ins (.and (.reg (q .r11)) (.reg (q .r10))))
  | .l, .or => some (ins (.or (.reg (q .r11)) (.reg (q .r10))))
  | .l, .xor => some (ins (.xor (.reg (q .r11)) (.reg (q .r10))))
  | .w, .add => some (ins32 (.add (.reg (d .r11)) (.reg (d .r10))))
  | .w, .sub => some (ins32 (.sub (.reg (d .r11)) (.reg (d .r10))))
  | .w, .and => some (ins32 (.and (.reg (d .r11)) (.reg (d .r10))))
  | .w, .or => some (ins32 (.or (.reg (d .r11)) (.reg (d .r10))))
  | .w, .xor => some (ins32 (.xor (.reg (d .r11)) (.reg (d .r10))))
  | _, _ => none

/-- `movl %rs32, %rd32` (zero-extends). -/
def movlD (rd rs : Reg64) : Directive := ins32 (.mov (.reg (d rd)) (.reg (d rs)))

/-- `rd := o`. -/
def op : Op Reg64 → Reg64 → Option (List Directive)
  | .bin k o a b, rd => (binIns k o).map fun i => [argTo .r11 a, argTo .r10 b, i, movD rd .r11]
  | .copy .l a, rd => some [argTo rd a]
  | .copy .w (.var r), rd => some [movlD rd r]
  | .copy .w (.imm c), rd => some [moviD rd (Cls.w.trunc c)]
  | _, _ => none

/-- `rd := loadl a`. -/
def load : Cls → Sz → Bool → Reg64 → Arg Reg64 → Option (List Directive)
  | .l, .l, _, rd, .var ra => some [ins (.mov (.reg (q rd)) (.mem (atReg ra)))]
  | _, _, _, _, _ => none

/-- `movq %rv, (%ra)` -/
def storelD (rv ra : Reg64) : Directive := ins (.mov (.mem (atReg ra)) (.reg (q rv)))

/-- `storel x, a`: through `r11`. -/
def store : Sz → Arg Reg64 → Arg Reg64 → Option (List Directive)
  | .l, x, .var ra => some [argTo .r11 x, storelD .r11 ra]
  | _, _, _ => none

/-- `jmp l` (the encoding the parser produces). -/
def jmp (l : String) : List Directive :=
  [ins (.jmp (.rel (.sub (.label l) .after_current_instruction)))]

/-- `test %r32, %r32; jnz l` (the IL's `jnz` tests the low 32 bits). -/
def jnz (r : Reg64) (l : String) : List Directive :=
  [ins32 (.test (.reg (d r)) (.reg (d r))), ins (.jcc .nz l)]

/-- `ret` -/
def ret : List Directive := [ins .ret]

/-! ## Frame instructions (plan step 2b) -/

/-- `push %r` -/
def pushD (r : Reg64) : Directive := ins (.push (.reg (q r)))

/-- `pop %r` -/
def popD (r : Reg64) : Directive := ins (.pop (.reg (q r)))

/-- `sub $c, %rsp` -/
def subSpD (c : Int64) : Directive := ins (.sub (.reg (q .rsp)) (.imm (.int64 c)))

/-- `add $c, %rsp` -/
def addSpD (c : Int64) : Directive := ins (.add (.reg (q .rsp)) (.imm (.int64 c)))

/-- `[rsp + off]` -/
abbrev atSp (off : Int64) : AddrExpr := { base := some (.reg .rsp), idx := none, disp := .int64 off }

/-- `movq %rv, off(%rsp)` -/
def stSpD (rv : Reg64) (off : Int64) : Directive := ins (.mov (.mem (atSp off)) (.reg (q rv)))

/-- `movq off(%rsp), %rd` -/
def ldSpD (rd : Reg64) (off : Int64) : Directive := ins (.mov (.reg (q rd)) (.mem (atSp off)))

/-- `call l` (the encoding the parser produces). -/
def callD (l : String) : Directive :=
  ins (.call (.rel (.sub (.label l) .after_current_instruction)))

/-- `jmp l` -/
def jmpD (l : String) : Directive :=
  ins (.jmp (.rel (.sub (.label l) .after_current_instruction)))

/-- Frame size for `ns` slots: `8 ns` rounded to `≡ 8 mod 16`, so that `rsp ≡ 0 mod 16` at calls
(the return address makes up the other 8). -/
def frameSize (ns : Nat) : Nat := 8 * ns + (if ns % 2 = 0 then 8 else 0)

/-- The x64 instruction set as seen by the lowering. -/
@[reducible] def isa : Isa where
  Reg := Reg64
  Directive := Directive
  label := .label
  sp := .rsp
  scratch := [.r10, .r11]
  allocatable := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]
  argRegs := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
  retRegs := [.rax, .rdx]
  calleeSaved := [.rbx, .rbp, .r12, .r13, .r14, .r15]
  mov := mov
  movi := movi
  op := op
  load := load
  store := store
  jmp := jmp
  jnz := jnz
  ret := ret
  raRegs := []
  frameSize := frameSize
  prologue ns := [subSpD (Int64.ofNat (frameSize ns))]
  epilogue ns := [addSpD (Int64.ofNat (frameSize ns))]
  slotSt i r := [stSpD r (Int64.ofNat (8 * i))]
  slotLd rd i := [ldSpD rd (Int64.ofNat (8 * i))]
  call sym := [callD sym]
  tailJmp sym := [jmpD sym]

end LeanQbe.Amd64
