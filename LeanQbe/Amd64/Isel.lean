module

public import Kraken.X64.Semantics
public import LeanQbe.Abi

/-!
# x64 instruction selection (QBE `amd64/isel.c` in spirit)

Snippets for the operations of the IL: `op`, `load`, `store` (each `none` when unsupported, so the
lowering fails), and the directive helpers they are built from. Step lemmas in `IselLemmas.lean`.

Supported (operands go through the scratch registers r11, r10, so any destination is allowed;
operands may be any non-scratch register or an immediate):

* `op`: every operation of `LeanQbe.Ops` (`copy`, `ext{s,u}{b,h,w,l}`, `add sub mul div rem udiv
  urem and or xor shl shr sar`, and every comparison `c{eq,ne,sle,slt,sge,sgt,ule,ult,uge,ugt}`),
  at both classes, for any non-scratch destination register (and any destination except for
  `div rem udiv urem`, which use `rd` alongside `r10` to save and restore `rax`/`rdx` around the
  hardware `div`/`idiv` instruction). Shift counts go through `%cl` (`rcx` is saved in `r10`
  around the shift); comparisons are `cmp` + `setcc` + `movzbl`, with `sge`/`sgt` as `setle`/`setl`
  on swapped operands.
* `load`: every width, signedness and class, from a register or an immediate address (through
  `r10`); one `movs*`/`movz*`/`mov` instruction, plus `movl` for a class-`w` load of a long.
* `store`: every width (`movb`/`movw`/`movl`/`movq` of `r11`'s low bytes) of a register or immediate,
  to a register or immediate address (through `r10`).
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

/-- Prepare `rdx:rax` (`edx:eax`) and divide by `r11` (`r11d`), leaving the result in `rax` (`div`,
`udiv`) or `rdx` (`rem`, `urem`). -/
def divCore : Cls → BinOp → Option (List Directive × Reg64)
  | .l, .udiv => some ([moviD .rdx 0, ins (.div (.reg (q .r11)))], .rax)
  | .l, .urem => some ([moviD .rdx 0, ins (.div (.reg (q .r11)))], .rdx)
  | .w, .udiv => some ([moviD .rdx 0, ins32 (.div (.reg (d .r11)))], .rax)
  | .w, .urem => some ([moviD .rdx 0, ins32 (.div (.reg (d .r11)))], .rdx)
  | .l, .div =>
    some ([movD .rdx .rax, ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63))),
      ins (.idiv (.reg (q .r11)))], .rax)
  | .l, .rem =>
    some ([movD .rdx .rax, ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63))),
      ins (.idiv (.reg (q .r11)))], .rdx)
  | .w, .div =>
    some ([movlD .rdx .rax, ins32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31))),
      ins32 (.idiv (.reg (d .r11)))], .rax)
  | .w, .rem =>
    some ([movlD .rdx .rax, ins32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31))),
      ins32 (.idiv (.reg (d .r11)))], .rdx)
  | _, _ => none

/-- Save `rax`/`rdx` using `rd` and `r10`, run `divCore`, and restore `rax`/`rdx` (except `rd`).
Returns `none` if `rd` is a scratch register (the lowering only picks allocatable destinations). -/
def divSeq (rd : Reg64) (core : List Directive) (res : Reg64) (a b : Arg Reg64) :
    Option (List Directive) :=
  if rd = .r10 ∨ rd = .r11 then none
  else if rd = .rax then
    some (argTo .r10 a :: argTo .r11 b :: movD .rax .r10 :: movD .r10 .rdx ::
      (core ++ [movD .rax res, movD .rdx .r10]))
  else if rd = .rdx then
    some (argTo .r10 a :: argTo .r11 b :: movD .rdx .rax :: movD .rax .r10 :: movD .r10 .rdx ::
      (core ++ [movD .rdx res, movD .rax .r10]))
  else
    some (argTo .r10 a :: argTo .r11 b :: movD rd .rax :: movD .rax .r10 :: movD .r10 .rdx ::
      (core ++ [movD .r11 res, movD .rdx .r10, movD .rax rd, movD rd .r11]))

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

/-- `sh{l,r}/sar{k} $c, %rd`: shift `rd` by immediate `c` (masked to 5 or 6 bits). -/
def shiftImmIns : Cls → BinOp → Reg64 → Val → Option Directive
  | .l, .shl, r, c => some (ins (.shl (.reg (q r)) (.imm8 (.int64 (Int64.ofBitVec c)))))
  | .l, .shr, r, c => some (ins (.shr (.reg (q r)) (.imm8 (.int64 (Int64.ofBitVec c)))))
  | .l, .sar, r, c => some (ins (.sar (.reg (q r)) (.imm8 (.int64 (Int64.ofBitVec c)))))
  | .w, .shl, r, c => some (ins32 (.shl (.reg (d r)) (.imm8 (.int64 (Int64.ofBitVec c)))))
  | .w, .shr, r, c => some (ins32 (.shr (.reg (d r)) (.imm8 (.int64 (Int64.ofBitVec c)))))
  | .w, .sar, r, c => some (ins32 (.sar (.reg (d r)) (.imm8 (.int64 (Int64.ofBitVec c)))))
  | _, _, _, _ => none

/-- `op{k} %rs, %rd`: `rd := rd op rs` at class `k` (class `w` zero-extends). -/
def binRegIns : Cls → BinOp → Reg64 → Reg64 → Option Directive
  | .l, .add, rd, rs => some (ins (.add (.reg (q rd)) (.reg (q rs))))
  | .l, .sub, rd, rs => some (ins (.sub (.reg (q rd)) (.reg (q rs))))
  | .l, .and, rd, rs => some (ins (.and (.reg (q rd)) (.reg (q rs))))
  | .l, .or,  rd, rs => some (ins (.or  (.reg (q rd)) (.reg (q rs))))
  | .l, .xor, rd, rs => some (ins (.xor (.reg (q rd)) (.reg (q rs))))
  | .l, .mul, rd, rs => some (ins (.imul none (.reg (q rd)) (.reg (q rs))))
  | .w, .add, rd, rs => some (ins32 (.add (.reg (d rd)) (.reg (d rs))))
  | .w, .sub, rd, rs => some (ins32 (.sub (.reg (d rd)) (.reg (d rs))))
  | .w, .and, rd, rs => some (ins32 (.and (.reg (d rd)) (.reg (d rs))))
  | .w, .or,  rd, rs => some (ins32 (.or  (.reg (d rd)) (.reg (d rs))))
  | .w, .xor, rd, rs => some (ins32 (.xor (.reg (d rd)) (.reg (d rs))))
  | .w, .mul, rd, rs => some (ins32 (.imul none (.reg (d rd)) (.reg (d rs))))
  | _, _, _, _ => none

/-- Whether a binary op in `binRegIns` is commutative (`add`, `and`, `or`, `xor`, `mul`). -/
def isComm : BinOp → Bool
  | .add | .and | .or | .xor | .mul => true
  | _ => false

/-- `cmp{k} %ry, %rx`: flags of `rx - ry` at class `k`. -/
def cmpRegIns : Cls → Reg64 → Reg64 → Directive
  | .l, rx, ry => ins (.cmp (.reg (q rx)) (.reg (q ry)))
  | .w, rx, ry => ins32 (.cmp (.reg (d rx)) (.reg (d ry)))

/-- `mov{b,w,l,q} %rv{b,w,d,}, (%ra)` -/
def storeRegIns : Sz → Reg64 → Reg64 → Directive
  | .b, rv, ra => ins8 (.mov (.mem (atReg ra)) (.reg (b8 rv)))
  | .h, rv, ra => ins16 (.mov (.mem (atReg ra)) (.reg (h16 rv)))
  | .w, rv, ra => ins32 (.mov (.mem (atReg ra)) (.reg (d rv)))
  | .l, rv, ra => storelD rv ra

/-- Whether `c` fits in a signed 32-bit immediate (sign-extended to 64 bits). -/
def fitsImm32 (c : Val) : Bool := (c.truncate 32).signExtend 64 == c

/-- Signed 32-bit `Int64` value matching `c`'s low 32 bits. -/
def imm32Val (c : Val) : Int64 := Int64.ofBitVec ((c.truncate 32).signExtend 64)

/-- Immediate operand encoding `imm32Val c` at width `w`. -/
def imm32Op (w : Width) (c : Val) : Operand w := .imm (.int64 (imm32Val c))

/-- Immediate value truncated to `sz` and sign-extended to 64 bits (always fits without assembler warning). -/
def storeImmVal (sz : Sz) (c : Val) : Int64 :=
  match sz with
  | .b => Int64.ofBitVec ((c.truncate 8).signExtend 64)
  | .h => Int64.ofBitVec ((c.truncate 16).signExtend 64)
  | .w => imm32Val c
  | .l => imm32Val c

/-- `mov{b,w,l,q} $c, (%ra)` -/
def storeImmIns (sz : Sz) (c : Val) (ra : Reg64) : Directive :=
  match sz with
  | .b => ins8  (.mov (.mem (atReg ra)) (.imm (.int64 (storeImmVal .b c))))
  | .h => ins16 (.mov (.mem (atReg ra)) (.imm (.int64 (storeImmVal .h c))))
  | .w => ins32 (.mov (.mem (atReg ra)) (.imm (.int64 (storeImmVal .w c))))
  | .l => ins   (.mov (.mem (atReg ra)) (.imm (.int64 (storeImmVal .l c))))

/-- `op{k} $c, %rd`: `rd := rd op imm32(c)` at class `k`. -/
def binImmIns : Cls → BinOp → Reg64 → Val → Option Directive
  | .l, .add, rd, c => some (ins   (.add (.reg (q rd)) (imm32Op .W64 c)))
  | .l, .sub, rd, c => some (ins   (.sub (.reg (q rd)) (imm32Op .W64 c)))
  | .l, .and, rd, c => some (ins   (.and (.reg (q rd)) (imm32Op .W64 c)))
  | .l, .or,  rd, c => some (ins   (.or  (.reg (q rd)) (imm32Op .W64 c)))
  | .l, .xor, rd, c => some (ins   (.xor (.reg (q rd)) (imm32Op .W64 c)))
  | .l, .mul, rd, c => some (ins   (.imul none (.reg (q rd)) (imm32Op .W64 c)))
  | .w, .add, rd, c => some (ins32 (.add (.reg (d rd)) (imm32Op .W32 c)))
  | .w, .sub, rd, c => some (ins32 (.sub (.reg (d rd)) (imm32Op .W32 c)))
  | .w, .and, rd, c => some (ins32 (.and (.reg (d rd)) (imm32Op .W32 c)))
  | .w, .or,  rd, c => some (ins32 (.or  (.reg (d rd)) (imm32Op .W32 c)))
  | .w, .xor, rd, c => some (ins32 (.xor (.reg (d rd)) (imm32Op .W32 c)))
  | .w, .mul, rd, c => some (ins32 (.imul none (.reg (d rd)) (imm32Op .W32 c)))
  | _, _, _, _ => none

/-- `cmp{k} $c, %rx`: flags of `rx - imm32(c)` at class `k`. -/
def cmpImmIns : Cls → Reg64 → Val → Directive
  | .l, rx, c => ins   (.cmp (.reg (q rx)) (imm32Op .W64 c))
  | .w, rx, c => ins32 (.cmp (.reg (d rx)) (imm32Op .W32 c))

/-- Move register at class `k`. -/
def movK : Cls → Reg64 → Reg64 → Directive
  | .l => movD
  | .w => movlD

/-- `rd := o` with fast paths for immediate shifts, immediate ALU/cmp, 3-op `lea`, and 2-address `bin`. -/
def op : Op Reg64 → Reg64 → Option (List Directive)
  | .bin k o a b, rd =>
    match shiftIns k o with
    | some i =>
      match b with
      | .imm c =>
        match shiftImmIns k o rd c with
        | some si =>
          match a with
          | .var ra => if ra = rd then some [si] else some [argTo rd (.var ra), si]
          | .imm _ => some [argTo rd a, si]
        | none => some [argTo .r11 a, movD .r10 .rcx, argTo .rcx b, i, movD .rcx .r10, movD rd .r11]
      | .var _ => some [argTo .r11 a, movD .r10 .rcx, argTo .rcx b, i, movD .rcx .r10, movD rd .r11]
    | none =>
      match divCore k o with
      | some (core, res) => divSeq rd core res a b
      | none =>
        match k, a, b with
        | _, .var ra, .var rb =>
          if ra = rd then (binRegIns k o rd rb).map (· :: [])
          else if isComm o ∧ rb = rd then (binRegIns k o rd ra).map (· :: [])
          else if k == .l && o == .add && rb ≠ rd then
            some [ins (.lea (q rd) { base := some (.reg ra), idx := some ⟨rb, .W8⟩ })]
          else if rb ≠ rd then (binRegIns k o rd rb).map fun i => [movK k rd ra, i]
          else (binIns k o).map fun i => [argTo .r11 a, argTo .r10 b, i, movD rd .r11]
        | _, .var ra, .imm cb =>
          if k == .w || fitsImm32 cb then
            if ra = rd then (binImmIns k o rd cb).map (· :: [])
            else if k == .l && o == .add then
              some [ins (.lea (q rd) { base := some (.reg ra), idx := none, disp := .int64 (imm32Val cb) })]
            else (binImmIns k o rd cb).map fun i => [movK k rd ra, i]
          else (binIns k o).map fun i => [argTo .r11 a, argTo .r10 b, i, movD rd .r11]
        | _, .imm ca, .var rb =>
          if isComm o && (k == .w || fitsImm32 ca) then
            if rb = rd then (binImmIns k o rd ca).map (· :: [])
            else if k == .l && o == .add then
              some [ins (.lea (q rd) { base := some (.reg rb), idx := none, disp := .int64 (imm32Val ca) })]
            else (binImmIns k o rd ca).map fun i => [movK k rd rb, i]
          else (binIns k o).map fun i => [argTo .r11 a, argTo .r10 b, i, movD rd .r11]
        | _, _, _ => (binIns k o).map fun i => [argTo .r11 a, argTo .r10 b, i, movD rd .r11]
  | .cmp k o a b, rd =>
    let (x, y) := if (condOf o).1 then (b, a) else (a, b)
    match x, y with
    | .var rx, .var ry => some [cmpRegIns k rx ry, setccD (condOf o).2, movzbD rd]
    | .var rx, .imm cy =>
      if k == .w || fitsImm32 cy then some [cmpImmIns k rx cy, setccD (condOf o).2, movzbD rd]
      else some [moviD .r10 cy, cmpRegIns k rx .r10, setccD (condOf o).2, movzbD rd]
    | .imm cx, .var ry => some [moviD .r10 cx, cmpRegIns k .r10 ry, setccD (condOf o).2, movzbD rd]
    | _, _ => some [argTo .r11 x, argTo .r10 y, cmpIns k, setccD (condOf o).2, movzbD rd]
  | .ext k s sg (.var r), rd => some [extD k s sg rd r]
  | .ext k s sg (.imm c), rd => some [moviD rd (k.trunc (s.extend sg c))]
  | .copy .l a, rd => some [argTo rd a]
  | .copy .w (.var r), rd => some [movlD rd r]
  | .copy .w (.imm c), rd => some [moviD rd (Cls.w.trunc c)]

/-- `store{sz} x, a` with direct register/imm store. -/
def store (sz : Sz) (x a : Arg Reg64) : Option (List Directive) :=
  match x with
  | .var rv => some ((addrIn a).1 ++ [storeRegIns sz rv (addrIn a).2])
  | .imm cx =>
    if sz != .l || fitsImm32 cx then some ((addrIn a).1 ++ [storeImmIns sz cx (addrIn a).2])
    else some (argTo .r11 x :: (addrIn a).1 ++ [storeIns sz (addrIn a).2])

/-- Fused comparison + conditional branch directly to `l`. -/
def jnzCmp (k : Cls) (o : CmpOp) (a b : Arg Reg64) (l : String) : Option (List Directive) :=
  let (x, y) := if (condOf o).1 then (b, a) else (a, b)
  let j := ins (.jcc (condOf o).2 l)
  match x, y with
  | .var rx, .var ry => some [cmpRegIns k rx ry, j]
  | .var rx, .imm cy =>
    if k == .w || fitsImm32 cy then some [cmpImmIns k rx cy, j]
    else some [moviD .r10 cy, cmpRegIns k rx .r10, j]
  | .imm cx, .var ry => some [moviD .r10 cx, cmpRegIns k .r10 ry, j]
  | _, _ => some [argTo .r11 x, argTo .r10 y, cmpIns k, j]

end LeanQbe.Amd64
