module

public import LeanQbe.Arm64.Targ

/-!
# AArch64 instruction selection (QBE `arm64/isel.c` in spirit)

One snippet per IL operation, load and store. Class `w` operations use the 32-bit (`w`) form of each
instruction, which reads the low 32 bits of its operands and zero-extends its result, exactly QBE's
`w` semantics in `LeanQbe.Ops`. Immediate operands are materialised into the scratch registers
(`x16` for the first operand or the address, `x17` for the second operand or the stored value).

Unsupported, returning `none`: a destination or operand in `sp` (the allocator never assigns it),
and `rem`/`urem` with two immediate operands (no scratch register left for the quotient; constant
folding removes these).
-/

@[expose] public section

namespace LeanQbe.Arm64

/-- The register width of a class. -/
def widthOf : Cls → RegWidth
  | .w => .W32
  | .l => .W64

/-- An operand in a register: a register other than `sp` as is, an immediate materialised in `tmp`. -/
def argIn (a : Arg Reg) (tmp : XReg) : Option (List Directive × XReg) :=
  match a with
  | .var (.reg r) => some ([], r)
  | .var .SP => none
  | .imm c => some (movImm tmp c, tmp)

/-- A scratch register for the quotient of `rem`/`urem`, distinct from both operand registers. -/
def remTmp (a b : Arg Reg) : Option XReg :=
  match a, b with
  | _, .var _ => some .X17
  | .var _, .imm _ => some .X16
  | .imm _, .imm _ => none

/-- `d := a o b` at width `w`, quotient register `t` for `rem`/`urem`. -/
def binIns (w : RegWidth) (o : BinOp) (d a b t : XReg) : List Directive :=
  match o with
  | .add => [ins (.ADD_s (zr d w) (zr a w) (sh b))]
  | .sub => [ins (.SUB_s (zr d w) (zr a w) (sh b))]
  | .mul => [ins (.MADD (zr d w) (zr a w) (zr b w) (xzr w))]
  | .div => [ins (.SDIV (zr d w) (zr a w) (zr b w))]
  | .udiv => [ins (.UDIV (zr d w) (zr a w) (zr b w))]
  | .rem => [ins (.SDIV (zr t w) (zr a w) (zr b w)), ins (.MSUB (zr d w) (zr t w) (zr b w) (zr a w))]
  | .urem => [ins (.UDIV (zr t w) (zr a w) (zr b w)), ins (.MSUB (zr d w) (zr t w) (zr b w) (zr a w))]
  | .and => [ins (.AND_s (zr d w) (zr a w) (sh b))]
  | .or => [ins (.ORR_s (zr d w) (zr a w) (sh b))]
  | .xor => [ins (.EOR_s (zr d w) (zr a w) (sh b))]
  | .sar => [ins (.ASRV (zr d w) (zr a w) (zr b w))]
  | .shr => [ins (.LSRV (zr d w) (zr a w) (zr b w))]
  | .shl => [ins (.LSLV (zr d w) (zr a w) (zr b w))]

/-- The condition code that holds after `cmp a, b` iff `a o b`. -/
def condOf : CmpOp → CondCode
  | .eq => .EQ
  | .ne => .NE
  | .sle => .LE
  | .slt => .LT
  | .sge => .GE
  | .sgt => .GT
  | .ule => .LS
  | .ult => .CC
  | .uge => .CS
  | .ugt => .HI

/-- The negated condition code: `cset d, cc` is `csinc d, wzr, wzr, notCondOf o`. -/
def notCondOf : CmpOp → CondCode
  | .eq => .NE
  | .ne => .EQ
  | .sle => .GT
  | .slt => .GE
  | .sge => .LT
  | .sgt => .LE
  | .ule => .HI
  | .ult => .CS
  | .uge => .CC
  | .ugt => .LS

/-- `cmp a, b; cset w_d, o` at width `w`. -/
def cmpIns (w : RegWidth) (o : CmpOp) (d a b : XReg) : List Directive :=
  [ins (.SUBS_s (xzr w) (zr a w) (sh b)),
   ins (w := .W32) (.CSINC (zr d .W32) (xzr .W32) (xzr .W32) (notCondOf o))]

/-- The index of the top bit of an `s`-sized value, for `sbfm`/`ubfm`. -/
def topBit : Sz → Nat
  | .b => 7
  | .h => 15
  | .w => 31
  | .l => 63

/-- `d := k.trunc (s.extend sg a)` for a register `a`. -/
def extIns (k : Cls) (s : Sz) (sg : Bool) (d a : XReg) : List Directive :=
  match s with
  | .l => [ins (.ORR_s (zr d (widthOf k)) (xzr (widthOf k)) (sh a))]
  | _ =>
    if sg then [ins (.SBFM (zr d (widthOf k)) (zr a (widthOf k)) 0 (topBit s))]
    else [ins (.UBFM (zr d (widthOf k)) (zr a (widthOf k)) 0 (topBit s))]

/-- `rd := o`. -/
def op (o : Op Reg) (rd : Reg) : Option (List Directive) :=
  match rd with
  | .SP => none
  | .reg d =>
    match o with
    | .bin k bo a b => do
      let (ca, ra) ← argIn a .X16
      let (cb, rb) ← argIn b .X17
      let t ← match bo with
        | .rem | .urem => remTmp a b
        | _ => some .X16
      some (ca ++ cb ++ binIns (widthOf k) bo d ra rb t)
    | .cmp k co a b => do
      let (ca, ra) ← argIn a .X16
      let (cb, rb) ← argIn b .X17
      some (ca ++ cb ++ cmpIns (widthOf k) co d ra rb)
    | .ext k s sg a =>
      match a with
      | .imm c => some (movImm d (k.trunc (s.extend sg c)))
      | .var (.reg r) => some (extIns k s sg d r)
      | .var .SP => none
    | .copy k a =>
      match a with
      | .imm c => some (movImm d (k.trunc c))
      | .var (.reg r) => some (extIns k .l false d r)
      | .var .SP => none

/-- The load instructions for `d := load{s}{sg} [a]` at class `k`. -/
def loadIns (k : Cls) (s : Sz) (sg : Bool) (d a : XReg) : List Directive :=
  match s, sg, k with
  | .l, _, .l => [ins (w := .W64) (.LDR (zr d .W64) (.addr (atReg a)))]
  | .l, _, .w => [ins (w := .W64) (.LDR (zr d .W64) (.addr (atReg a))),
                  ins (.ORR_s (zr d .W32) (xzr .W32) (sh d))]
  | .w, true, .l => [ins (w := .W64) (.LDRSW (zr d .W64) (.addr (atReg a)))]
  | .w, _, _ => [ins (w := .W32) (.LDR (zr d .W32) (.addr (atReg a)))]
  | .h, false, _ => [ins (w := .W32) (.LDRH (zr d .W32) (atReg a))]
  | .h, true, k => [ins (.LDRSH (zr d (widthOf k)) (atReg a))]
  | .b, false, _ => [ins (w := .W32) (.LDRB (zr d .W32) (atReg a))]
  | .b, true, k => [ins (.LDRSB (zr d (widthOf k)) (atReg a))]

/-- `rd := load{s}{sg} a` at class `k`. -/
def load (k : Cls) (s : Sz) (sg : Bool) (rd : Reg) (a : Arg Reg) : Option (List Directive) :=
  match rd with
  | .SP => none
  | .reg d => do
    let (ca, ra) ← argIn a .X16
    some (ca ++ loadIns k s sg d ra)

/-- The store instruction for `store{s} v, [a]`. -/
def storeIns (s : Sz) (v a : XReg) : List Directive :=
  match s with
  | .l => [ins (w := .W64) (.STR (zr v .W64) (atReg a))]
  | .w => [ins (w := .W32) (.STR (zr v .W32) (atReg a))]
  | .h => [ins (w := .W32) (.STRH (zr v .W32) (atReg a))]
  | .b => [ins (w := .W32) (.STRB (zr v .W32) (atReg a))]

/-- `store{s} x, a`. -/
def store (s : Sz) (x a : Arg Reg) : Option (List Directive) := do
  let (cx, rx) ← argIn x .X17
  let (ca, ra) ← argIn a .X16
  some (cx ++ ca ++ storeIns s rx ra)

/-- The AArch64 instruction set as seen by the lowering. -/
@[reducible] def isa : Isa where
  Reg := Reg
  Directive := Directive
  label := .label
  sp := .SP
  scratch := scratch
  allocatable := allocatable
  argRegs := argRegs
  retRegs := retRegs
  calleeSaved := calleeSaved
  mov := mov
  movi := movi
  op := op
  load := load
  store := store
  jmp := jmp
  jnz := jnz
  ret := ret
  raRegs := [.reg .X30]
  frameSize := frameSize
  prologue := prologue
  epilogue := epilogue
  slotSt := slotSt
  slotLd := slotLd
  call := call
  tailJmp := tailJmp

end LeanQbe.Arm64
