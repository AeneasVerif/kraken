module

public import Kraken.X64.Semantics
public import LeanQbe.Abi

/-!
# x64 instruction selection (QBE `amd64/isel.c` in spirit)

Snippets for the operations of the IL: `op`, `load`, `store` (each `none` when unsupported, so the
lowering fails), and the directive helpers they are built from. Step lemmas in `IselLemmas.lean`.

Supported (operands go through the scratch registers r11, r10, so any destination is allowed;
operands may be any non-scratch register or an immediate):

* `op`: `copy`, `ext{s,u}{b,h,w}`, `add sub mul and or xor`, `shl shr sar`, and every comparison
  `c{eq,ne,sle,slt,sge,sgt,ule,ult,uge,ugt}`, at both classes. Shift counts go through `%cl`
  (`rcx` is saved in `r10` around the shift); comparisons are `cmp` + `setcc` + `movzbl`, with
  `sge`/`sgt` as `setle`/`setl` on swapped operands (Kraken's parser has no `setge`/`setg`).
* `load`: every width, signedness and class, from a register or an immediate address (through
  `r10`); one `movs*`/`movz*`/`mov` instruction, plus `movl` for a class-`w` load of a long.
* `store`: every width (`movb`/`movw`/`movl`/`movq` of `r11`'s low bytes) of a register or immediate,
  to a register or immediate address (through `r10`).

Unsupported (`none`): `div rem udiv urem` (Kraken's x64 semantics has no `div`/`idiv`).
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

/-- The 8-bit view of a register. -/
abbrev b8 (r : Reg64) : Reg .W8 := .low r .W8

/-- The 16-bit view of a register. -/
abbrev h16 (r : Reg64) : Reg .W16 := .low r .W16

/-- An 8-bit instruction with 64-bit addressing. -/
abbrev ins8 (op : Operation .W8) : Directive := .instr (.regular .W64 .W8 op)

/-- A 16-bit instruction with 64-bit addressing. -/
abbrev ins16 (op : Operation .W16) : Directive := .instr (.regular .W64 .W16 op)

/-- `op{k} %r10, %r11`: `r11 := r11 op r10` at class `k` (class `w` zero-extends). -/
def binIns : Cls → BinOp → Option Directive
  | .l, .add => some (ins (.add (.reg (q .r11)) (.reg (q .r10))))
  | .l, .sub => some (ins (.sub (.reg (q .r11)) (.reg (q .r10))))
  | .l, .and => some (ins (.and (.reg (q .r11)) (.reg (q .r10))))
  | .l, .or => some (ins (.or (.reg (q .r11)) (.reg (q .r10))))
  | .l, .xor => some (ins (.xor (.reg (q .r11)) (.reg (q .r10))))
  | .l, .mul => some (ins (.imul none (.reg (q .r11)) (.reg (q .r10))))
  | .w, .add => some (ins32 (.add (.reg (d .r11)) (.reg (d .r10))))
  | .w, .sub => some (ins32 (.sub (.reg (d .r11)) (.reg (d .r10))))
  | .w, .and => some (ins32 (.and (.reg (d .r11)) (.reg (d .r10))))
  | .w, .or => some (ins32 (.or (.reg (d .r11)) (.reg (d .r10))))
  | .w, .xor => some (ins32 (.xor (.reg (d .r11)) (.reg (d .r10))))
  | .w, .mul => some (ins32 (.imul none (.reg (d .r11)) (.reg (d .r10))))
  | _, _ => none

/-- `sh{l,r}/sar{k} %cl, %r11`: `r11 := r11 shift (cl mod width)` at class `k`. -/
def shiftIns : Cls → BinOp → Option Directive
  | .l, .shl => some (ins (.shl (.reg (q .r11)) .cl))
  | .l, .shr => some (ins (.shr (.reg (q .r11)) .cl))
  | .l, .sar => some (ins (.sar (.reg (q .r11)) .cl))
  | .w, .shl => some (ins32 (.shl (.reg (d .r11)) .cl))
  | .w, .shr => some (ins32 (.shr (.reg (d .r11)) .cl))
  | .w, .sar => some (ins32 (.sar (.reg (d .r11)) .cl))
  | _, _ => none

/-- `movl %rs32, %rd32` (zero-extends). -/
def movlD (rd rs : Reg64) : Directive := ins32 (.mov (.reg (d rd)) (.reg (d rs)))

/-- For each comparison: whether the operands are swapped, and the condition code that holds after
`cmp` iff the comparison holds. `sge`/`sgt` swap the operands because Kraken's parser has no
`setge`/`setg`. -/
def condOf : CmpOp → Bool × CondCode
  | .eq => (false, .z)
  | .ne => (false, .nz)
  | .sle => (false, .le)
  | .slt => (false, .l)
  | .sge => (true, .le)
  | .sgt => (true, .l)
  | .ule => (false, .be)
  | .ult => (false, .c)
  | .uge => (false, .nc)
  | .ugt => (false, .a)

/-- `cmp{k} %r10, %r11`: flags of `r11 - r10` at class `k`. -/
def cmpIns : Cls → Directive
  | .l => ins (.cmp (.reg (q .r11)) (.reg (q .r10)))
  | .w => ins32 (.cmp (.reg (d .r11)) (.reg (d .r10)))

/-- `set{cc} %r11b` -/
def setccD (cc : CondCode) : Directive := ins8 (.setcc cc (.reg (b8 .r11)))

/-- `movzbl %r11b, %rd32` -/
def movzbD (rd : Reg64) : Directive := ins32 (.movzx (.reg (d rd)) (.reg (b8 .r11)))

/-- `rd := ext{s}{sg} r` at class `k`: one `movs*`/`movz*`/`mov` instruction. -/
def extD : Cls → Sz → Bool → Reg64 → Reg64 → Directive
  | .l, .b, true, rd, r => ins (.movsx (.reg (q rd)) (.reg (b8 r)))
  | .w, .b, true, rd, r => ins32 (.movsx (.reg (d rd)) (.reg (b8 r)))
  | _, .b, false, rd, r => ins32 (.movzx (.reg (d rd)) (.reg (b8 r)))
  | .l, .h, true, rd, r => ins (.movsx (.reg (q rd)) (.reg (h16 r)))
  | .w, .h, true, rd, r => ins32 (.movsx (.reg (d rd)) (.reg (h16 r)))
  | _, .h, false, rd, r => ins32 (.movzx (.reg (d rd)) (.reg (h16 r)))
  | .l, .w, true, rd, r => ins (.movsx (.reg (q rd)) (.reg (d r)))
  | .l, .l, _, rd, r => movD rd r
  | _, _, _, rd, r => movlD rd r

/-- `rd := o`. -/
def op : Op Reg64 → Reg64 → Option (List Directive)
  | .bin k o a b, rd =>
    match shiftIns k o with
    | some i => some [argTo .r11 a, movD .r10 .rcx, argTo .rcx b, i, movD .rcx .r10, movD rd .r11]
    | none => (binIns k o).map fun i => [argTo .r11 a, argTo .r10 b, i, movD rd .r11]
  | .cmp k o a b, rd =>
    let (x, y) := if (condOf o).1 then (b, a) else (a, b)
    some [argTo .r11 x, argTo .r10 y, cmpIns k, setccD (condOf o).2, movzbD rd]
  | .ext k s sg (.var r), rd => some [extD k s sg rd r]
  | .ext k s sg (.imm c), rd => some [moviD rd (k.trunc (s.extend sg c))]
  | .copy .l a, rd => some [argTo rd a]
  | .copy .w (.var r), rd => some [movlD rd r]
  | .copy .w (.imm c), rd => some [moviD rd (Cls.w.trunc c)]

/-- An address operand: a register as is, an immediate materialised in `r10`. -/
def addrIn : Arg Reg64 → List Directive × Reg64
  | .var r => ([], r)
  | .imm c => ([moviD .r10 c], .r10)

/-- `rd := load{sz}{sg} (ra)` at class `cl`. -/
def loadIns : Cls → Sz → Bool → Reg64 → Reg64 → List Directive
  | .l, .b, true, rd, ra => [ins (.movsx (.reg (q rd)) (.mem (atReg ra) : RegOrMem .W8))]
  | .w, .b, true, rd, ra => [ins32 (.movsx (.reg (d rd)) (.mem (atReg ra) : RegOrMem .W8))]
  | _, .b, false, rd, ra => [ins32 (.movzx (.reg (d rd)) (.mem (atReg ra) : RegOrMem .W8))]
  | .l, .h, true, rd, ra => [ins (.movsx (.reg (q rd)) (.mem (atReg ra) : RegOrMem .W16))]
  | .w, .h, true, rd, ra => [ins32 (.movsx (.reg (d rd)) (.mem (atReg ra) : RegOrMem .W16))]
  | _, .h, false, rd, ra => [ins32 (.movzx (.reg (d rd)) (.mem (atReg ra) : RegOrMem .W16))]
  | .l, .w, true, rd, ra => [ins (.movsx (.reg (q rd)) (.mem (atReg ra) : RegOrMem .W32))]
  | _, .w, _, rd, ra => [ins32 (.mov (.reg (d rd)) (.mem (atReg ra)))]
  | .l, .l, _, rd, ra => [ins (.mov (.reg (q rd)) (.mem (atReg ra)))]
  | .w, .l, _, rd, ra => [ins (.mov (.reg (q rd)) (.mem (atReg ra))), movlD rd rd]

/-- `rd := load{sz}{sg} a` at class `cl`. -/
def load (cl : Cls) (sz : Sz) (sg : Bool) (rd : Reg64) (a : Arg Reg64) : Option (List Directive) :=
  some ((addrIn a).1 ++ loadIns cl sz sg rd (addrIn a).2)

/-- `movq %rv, (%ra)` -/
def storelD (rv ra : Reg64) : Directive := ins (.mov (.mem (atReg ra)) (.reg (q rv)))

/-- `mov{b,w,l,q} %r11{b,w,d,}, (%ra)` -/
def storeIns : Sz → Reg64 → Directive
  | .b, ra => ins8 (.mov (.mem (atReg ra)) (.reg (b8 .r11)))
  | .h, ra => ins16 (.mov (.mem (atReg ra)) (.reg (h16 .r11)))
  | .w, ra => ins32 (.mov (.mem (atReg ra)) (.reg (d .r11)))
  | .l, ra => storelD .r11 ra

/-- `store{sz} x, a`: the value through `r11`, an immediate address through `r10`. -/
def store (sz : Sz) (x a : Arg Reg64) : Option (List Directive) :=
  some (argTo .r11 x :: (addrIn a).1 ++ [storeIns sz (addrIn a).2])

end LeanQbe.Amd64
