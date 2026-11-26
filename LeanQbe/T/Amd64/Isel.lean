module

public import LeanQbe.T.Amd64.Base
public import LeanQbe.T.Amd64.IselZero
public import LeanQbe.T.IselStepAttr

/-!
# Typed x64 Scalar Instruction Selection

Implements `x64Gpr : GprIsa Reg64 RegMm CondCode Directive` over `LeanQbe.T.Amd64.Base` (`x64Mach`,
`x64Scratch := [.r10, .r11]`, `x64CondReads`, `x64NegCond`):

* `x64SupportsScalarOp`: kernel-`rfl`-safe 1-for-1 `Bool` gate covering:
  - `[8, 16, 32, 64]`: `copy/add/sub/mul/neg/and/or/xor/not`, `shl/lshr/ashr/rotl/rotr` (with
    BMI2 flag-free `shlx`/`shrx`/`sarx` and immediate `rorx` at `32`/`64`),
    `clz/cls/ctz/popcnt` (`lzcnt`/`tzcnt`/`popcnt` with `8`/`16`-to-`32` widening),
    `ofBool`, `udiv/sdiv/urem/srem`, `cmp` (both `.flag` and `.gpr`), `select` (`.flag`, `.gpr`,
    and `.imm`, branchless via `cmovcc`), `zext/sext/trunc/bitcast`, and `.bool`
    `copy/and/or/xor/not`.
  - `[16, 32, 64]`: `bswap` (`rolw $8`, `bswapl`, `bswapq`).
  - `[32, 64]`: `addc` (`.default` `adc`, `.adcx` `adcx`, `.adox` `adox`), `subb` (`sbb`),
    `umulw` (`.default` `mul`, `.mulxFast` `mulx`), `smulw` (`imul1`),
    `fshl`/`fshr` (`shld`/`shrd`).
* Supports `VariantHint.disp` (`lea disp(%rb), %rd`), `VariantHint.decInc` (`dec`/`inc` preserving
  `CF`), 2-address ALU fast paths, immediate shifts/ALU/cmp, and `[base]`/`[base+disp]`/`imm`
  `load`/`store`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

/-! ## 1. Width, register, immediate, and addressing helpers -/

/-- Supported scalar bit widths (`[8, 16, 32, 64]`). -/
def x64BitWidths : List Nat := [8, 16, 32, 64]

/-- Supported multi-word/carry bit widths (`[32, 64]`). -/
def x64WideWidths : List Nat := [32, 64]

/-- Dispatch a dependent family `F n` across supported Kraken widths `{8, 16, 32, 64}`. -/
def withWidth {F : Nat → Type} {α : Type} (n : Nat) (x : F n)
    (k : (w : Width) → F w.bits → Option α) : Option α :=
  match n, x with
  | 8,  x => k .W8  x
  | 16, x => k .W16 x
  | 32, x => k .W32 x
  | 64, x => k .W64 x
  | _,  _ => none

/-- Dispatch a dependent family `F n` across wide widths `{32, 64}`. -/
def withWideWidth {F : Nat → Type} {α : Type} (n : Nat) (x : F n)
    (k : (w : Width) → F w.bits → Option α) : Option α :=
  match n, x with
  | 32, x => k .W32 x
  | 64, x => k .W64 x
  | _,  _ => none

/-- Width-indexed register view of `r`. -/
def regW : (w : Width) → Reg64 → Reg w
  | .W8,  r => b8 r
  | .W16, r => h16 r
  | .W32, r => d r
  | .W64, r => q r

/-- `mov %rs, %rd` (64-bit) instruction. -/
abbrev movI (rd rs : Reg64) : Instr :=
  x64InsI .W64 (.mov (.reg (q rd)) (.reg (q rs)))

/-- `movl %rs32, %rd32` instruction (zero-extends to 64 bits). -/
abbrev movlI (rd rs : Reg64) : Instr :=
  x64InsI .W32 (.mov (.reg (d rd)) (.reg (d rs)))

/-- Width-preserving register-to-register move (`movzbl`/`movzwl`/`movl`/`movq`) instruction. -/
abbrev movWI (w : Width) (rd rs : Reg64) : Instr :=
  match w with
  | .W8  => x64InsI .W32 (.movzx (.reg (d rd)) (.reg (b8 rs)))
  | .W16 => x64InsI .W32 (.movzx (.reg (d rd)) (.reg (h16 rs)))
  | .W32 => movlI rd rs
  | .W64 => movI rd rs

/-- Width-indexed 64-bit-addressed directive wrapper. -/
def insW (w : Width) (op : Operation w) : Directive := .instr (x64InsI w op)

/-- `mov %rs, %rd` (64-bit). -/
def movD (rd rs : Reg64) : Directive := .instr (movI rd rs)

/-- `movl %rs32, %rd32` (zero-extends to 64 bits). -/
def movlD (rd rs : Reg64) : Directive := .instr (movlI rd rs)

/-- `mov $c, %rd` (full 64-bit immediate, preserves all status flags). -/
def moviD (rd : Reg64) (c : BitVec 64) : Directive := .instr (moviI rd c)

/-- Width-preserving register-to-register move (`movzbl`/`movzwl`/`movl`/`movq`). -/
def movW (w : Width) (rd rs : Reg64) : Directive := .instr (movWI w rd rs)

/-- Whether `c` fits in a sign-extended 32-bit immediate. -/
def fitsImm32 (c : BitVec 64) : Bool :=
  (c.truncate 32).signExtend 64 == c

/-- `Operand` encoding `c : BitVec w.bits` at width `w` (`w ≠ .W64` or `fitsImm32 c`). -/
def immBitsOp (w : Width) (c : BitVec w.bits) : Operand w :=
  .imm (.int64 (Int64.ofBitVec (c.signExtend 64)))

/-- Load a scalar `.bits w.bits` `PArg` into `rd` at width `w`, preserving status flags. -/
def argToBitsI (w : Width) (rd : Reg64) :
    PArg Reg64 RegMm CondCode (.bits w.bits) → Option Instr
  | .gpr rs => some (movWI w rd rs)
  | .imm c  => some (moviI rd (c.setWidth 64))
  | .vec _  => none

/-- `setcc cc %rd_b` instruction sequence (preserves all status flags; leaves bits `8..63` intact). -/
def setccOnlyIns (rd : Reg64) (cc : CondCode) : List Instr :=
  [x64InsI .W8 (.setcc cc (.reg (b8 rd)))]

/-- `setcc cc %rd_b` (preserves all status flags). -/
def setccOnly (rd : Reg64) (cc : CondCode) : List Directive :=
  emitClean (setccOnlyIns rd cc)

/-- `setcc cc %rd_b; movzbl %rd_b, %rd_d` instruction sequence (preserves all status flags). -/
def setccMoveIns (rd : Reg64) (cc : CondCode) : List Instr :=
  [x64InsI .W8 (.setcc cc (.reg (b8 rd))), x64InsI .W32 (.movzx (.reg (d rd)) (.reg (b8 rd)))]

/-- `setcc cc %rd_b; movzbl %rd_b, %rd_d` (preserves all status flags). -/
def setccMove (rd : Reg64) (cc : CondCode) : List Directive :=
  emitClean (setccMoveIns rd cc)

/-- Materialize `.bool` `PArg` into low 8 bits of `rd` (`0#8` or `1#8`), preserving flags. -/
def boolArgTo8I (rd : Reg64) : PArg Reg64 RegMm CondCode .bool → Option Instr
  | .gpr rs  => some (x64InsI .W8 (.mov (.reg (b8 rd)) (.reg (b8 rs))))
  | .imm b   => some (moviI rd (BitVec.ofNat 64 b.toNat))
  | .flag cc => some (x64InsI .W8 (.setcc cc (.reg (b8 rd))))
  | .vec _   => none

/-- SIB scaled-index memory operand without base `[ri * scale + off]`. -/
abbrev atIdx (ri : Reg64) (sc : AddrScale) (off : Int64) : AddrExpr :=
  { base := none, idx := some ⟨ri, scaleWidth sc⟩, disp := .int64 off }

/-- Lower `AddrArg Reg64` to prefix setup instructions, a Kraken `AddrExpr`, and a flag mask.
Uses `.r10` if needed (leaving `.r11` free for store values). -/
def addrToExprIns : AddrArg Reg64 → List Instr × AddrExpr × FlagMask
  | .baseDisp r off =>
    if off == 0 then ([], atReg r, maskNone)
    else if fitsImm32 off.toBitVec then ([], atDisp r off, maskNone)
    else ([moviI .r10 off.toBitVec, x64InsI .W64 (.lea (q .r10) (atSIB r .r10 .s1 0))],
          atReg .r10, maskNone)
  | .baseIdxDisp rb ri sc off =>
    if fitsImm32 off.toBitVec then ([], atSIB rb ri sc off, maskNone)
    else ([moviI .r10 off.toBitVec, x64InsI .W64 (.lea (q .r10) (atSIB rb .r10 .s1 0))],
          atSIB .r10 ri sc 0, maskNone)
  | .imm addr => ([moviI .r10 addr], atReg .r10, maskNone)

/-- Lower `AddrArg Reg64` to prefix setup directives, a Kraken `AddrExpr`, and a flag mask. -/
def addrToExpr (a : AddrArg Reg64) : List Directive × AddrExpr × FlagMask :=
  (emitClean (addrToExprIns a).1, (addrToExprIns a).2)

/-! ## 2. Condition codes and primitive operation builders -/

/-- Map `LeanQbe.T.CmpOp` to Kraken `CondCode`. -/
def condOf : CmpOp → CondCode
  | .eq  => .z
  | .ne  => .nz
  | .ult => .c
  | .ule => .be
  | .ugt => .a
  | .uge => .nc
  | .slt => .l
  | .sle => .le
  | .sgt => .g
  | .sge => .ge

/-- Binary ALU operation kind supported by `opBin`. -/
inductive AluBinKind | add | sub | and | or | xor | mul
  deriving DecidableEq

def AluBinKind.isComm : AluBinKind → Bool
  | .add | .and | .or | .xor | .mul => true
  | .sub => false

def AluBinKind.eval {n : Nat} : AluBinKind → BitVec n → BitVec n → BitVec n
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or,  a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .mul, a, b => a * b

/-- Width-polymorphic two-address instruction `dst := dst op src`.
For `.mul` at `.W8`, emits `.W32` `imull` since x86-64 has no 2-operand `imulb`. -/
abbrev aluBinI (w : Width) (k : AluBinKind) (dst : Reg64) (src : Operand w) : Instr :=
  match k with
  | .add => x64InsI w (.add (.reg (regW w dst)) src)
  | .sub => x64InsI w (.sub (.reg (regW w dst)) src)
  | .and => x64InsI w (.and (.reg (regW w dst)) src)
  | .or  => x64InsI w (.or  (.reg (regW w dst)) src)
  | .xor => x64InsI w (.xor (.reg (regW w dst)) src)
  | .mul =>
    match w, src with
    | .W8, .regOrMem (.reg r) => x64InsI .W32 (.imul none (.reg (d dst)) (.reg (d r.base)))
    | .W8, .imm v => x64InsI .W32 (.imul none (.reg (d dst)) (.imm v))
    | _, _ => x64InsI w (.imul none (.reg (regW w dst)) src)

/-- Width-polymorphic two-address directive `dst := dst op src`. -/
def aluBinIns (w : Width) (k : AluBinKind) (dst : Reg64) (src : Operand w) : Directive :=
  .instr (aluBinI w k dst src)

/-- Shift/rotate operation kind supported by `opShift`. -/
inductive ShiftKind | shl | lshr | ashr | rotl | rotr
  deriving DecidableEq

def ShiftKind.toOp {w : Width} : ShiftKind → Dst w → ShiftCountExpr → Operation w
  | .shl  => .shl
  | .lshr => .shr
  | .ashr => .sar
  | .rotl => .rol
  | .rotr => .ror

def ShiftKind.isRot : ShiftKind → Bool
  | .rotl | .rotr => true
  | _ => false

/-- BMI2 flag-free 3-operand variable shift constructor for `shl`/`lshr`/`ashr`. -/
def ShiftKind.toBmi2Op? {w : Width} :
    ShiftKind → Option (Reg w → RegOrMem w → Reg w → Operation w)
  | .shl  => some .shlx
  | .lshr => some .shrx
  | .ashr => some .sarx
  | _     => none

/-- Pure `BitVec` shift/rotate semantics parameterized by shift count `k`. -/
def ShiftKind.eval {n : Nat} : ShiftKind → BitVec n → Nat → BitVec n
  | .shl,  x, k => x <<< k
  | .lshr, x, k => x >>> k
  | .ashr, x, k => x.sshiftRight k
  | .rotl, x, k => x.rotateLeft k
  | .rotr, x, k => x.rotateRight k

/-- Bit-counting operation kind supported by `opBitcnt`. -/
inductive BitcntKind | clz | cls | ctz | popcnt
  deriving DecidableEq

/-- Pure `BitVec` semantics of bit-counting operations. -/
def BitcntKind.eval (w : Width) : BitcntKind → BitVec w.bits → BitVec w.bits
  | .clz,    x => x.clz
  | .cls,    x => (if x.msb then (~~~x).clz else x.clz) - BitVec.ofNat w.bits 1
  | .ctz,    x => x.reverse.clz
  | .popcnt, x => x.cpop

/-- Mask `ecx` to `0..7` or `0..15` for variable `8`/`16`-bit shifts (Kraken masks by `0x1f`). -/
def shiftMaskRcxIns : Width → List Instr
  | .W8  => [x64InsI .W32 (.and (.reg (d .rcx)) (.imm (.int64 7)))]
  | .W16 => [x64InsI .W32 (.and (.reg (d .rcx)) (.imm (.int64 15)))]
  | _    => []

/-- Mask `ecx` to `0..7` or `0..15` for variable `8`/`16`-bit shifts. -/
def shiftMaskRcx (w : Width) : List Directive :=
  emitClean (shiftMaskRcxIns w)

/-! ## 3. Individual scalar operation lowering (`op*`) -/

/-- Lower `.copy (.bits w.bits)` into `rd`. -/
def opCopyBitsIns (w : Width) (pa : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  match pa with
  | .gpr rs => if rs == rd then some ([], maskNone) else some ([movWI w rd rs], maskNone)
  | .imm c  => some ([moviI rd (c.setWidth 64)], maskNone)
  | .vec _  => none

/-- Lower `.copy .bool` into `pd`. -/
def opCopyBoolIns (pa : PArg Reg64 RegMm CondCode .bool)
    (pd : PDst Reg64 RegMm CondCode .bool) : Option (List Instr × FlagMask) :=
  match pd with
  | .gpr rd =>
    match pa with
    | .gpr rs =>
      if rs == rd then some ([], maskNone)
      else some ([x64InsI .W32 (.movzx (.reg (d rd)) (.reg (b8 rs)))], maskNone)
    | .imm b   => some ([moviI rd (BitVec.ofNat 64 b.toNat)], maskNone)
    | .flag cc => some (setccOnlyIns rd cc, maskNone)
    | .vec _   => none
  | _ => none

/-- In-place 8-bit boolean binary step `rd := rd op other`. -/
def boolBinSelfIns (insFn : Dst .W8 → Operand .W8 → Operation .W8) (rd : Reg64)
    (other : PArg Reg64 RegMm CondCode .bool) : Option (List Instr × FlagMask) :=
  match other with
  | .gpr rs => some ([x64InsI .W8 (insFn (.reg (b8 rd)) (.reg (b8 rs)))], maskAll)
  | _ => do
    let d2 ← boolArgTo8I .r10 other
    some ([d2, x64InsI .W8 (insFn (.reg (b8 rd)) (.reg (b8 .r10)))], maskAll)

/-- Direct 8-bit boolean binary lowering `rd := first op second` (`rd ∉ args`). -/
def boolBinDstIns (insFn : Dst .W8 → Operand .W8 → Operation .W8) (rd : Reg64)
    (first second : PArg Reg64 RegMm CondCode .bool) : Option (List Instr × FlagMask) := do
  let d1 ← boolArgTo8I rd first
  match second with
  | .gpr rs => some ([d1, x64InsI .W8 (insFn (.reg (b8 rd)) (.reg (b8 rs)))], maskAll)
  | _ => do
    let d2 ← boolArgTo8I .r10 second
    some ([d1, d2, x64InsI .W8 (insFn (.reg (b8 rd)) (.reg (b8 .r10)))], maskAll)

/-- Lower `.and`/`.or`/`.xor` on `.bool` into `pd` without redundant `.r11`/`movzx` roundtrips. -/
def opBoolBinIns (op : Bool → Bool → Bool) (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (pa pb : PArg Reg64 RegMm CondCode .bool) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Instr × FlagMask) :=
  match pd with
  | .gpr rd =>
    match pa, pb with
    | .imm a, .imm b => some ([moviI rd (BitVec.ofNat 64 (op a b).toNat)], maskNone)
    | .gpr ra, _ =>
      if ra == rd then boolBinSelfIns insFn rd pb
      else match pb with
      | .gpr rb =>
        if rb == rd then boolBinSelfIns insFn rd pa
        else boolBinDstIns insFn rd pa pb
      | _ => boolBinDstIns insFn rd pb pa
    | _, .gpr rb =>
      if rb == rd then boolBinSelfIns insFn rd pa
      else boolBinDstIns insFn rd pa pb
    | _, _ => boolBinDstIns insFn rd pa pb
  | _ => none

/-- Lower `.not .bool` into `pd` (zero-insn flag invert or direct byte xor without `movzx`). -/
def opBoolNotIns (pa : PArg Reg64 RegMm CondCode .bool)
    (pd : PDst Reg64 RegMm CondCode .bool) : Option (List Instr × FlagMask) :=
  match pd with
  | .flag ccDst =>
    match pa with
    | .flag ccSrc => if ccDst == x64NegCond ccSrc then some ([], maskNone) else none
    | _ => none
  | .gpr rd =>
    match pa with
    | .imm b   => some ([moviI rd (BitVec.ofNat 64 (!b).toNat)], maskNone)
    | .flag cc => some (setccOnlyIns rd (x64NegCond cc), maskNone)
    | .gpr rs  =>
      let xor1 := x64InsI .W8 (.xor (.reg (b8 rd)) (.imm (.int64 1)))
      if rs == rd then some ([xor1], maskAll)
      else some ([x64InsI .W32 (.movzx (.reg (d rd)) (.reg (b8 rs))), xor1], maskAll)
    | .vec _ => none
  | _ => none

/-- Lower `.neg (.bits w.bits)` into `rd`. -/
def opNegIns (w : Width) (pa : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  match pa with
  | .imm c  => some ([moviI rd ((-c).setWidth 64)], maskNone)
  | .gpr rs =>
    let pre := if rs == rd then [] else [movWI w rd rs]
    some (pre ++ [x64InsI w (.neg (.reg (regW w rd)))], maskAll)
  | .vec _  => none

/-- Lower `.not (.bits w.bits)` into `rd` (`not` leaves all status flags intact). -/
def opNotIns (w : Width) (pa : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  match pa with
  | .imm c  => some ([moviI rd ((~~~c).setWidth 64)], maskNone)
  | .gpr rs =>
    let pre := if rs == rd then [] else [movWI w rd rs]
    some (pre ++ [x64InsI w (.not (.reg (regW w rd)))], maskNone)
  | .vec _  => none

/-- Non-destructive 3-address `lea` for `add`/`sub` reg+imm (`ra != rd`) at `W32`/`W64`. -/
def opBinLeaImm? (w : Width) (k : AluBinKind) (ra : Reg64) (cb : BitVec w.bits) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  if (w == .W32 || w == .W64) && ra != rd && (k == .add || k == .sub) then
    let off64 : BitVec 64 := (if k == .add then cb else -cb).signExtend 64
    if fitsImm32 off64 then
      some ([x64InsI w (.lea (regW w rd) (atDisp ra (Int64.ofBitVec off64)))], maskNone)
    else none
  else none

/-- Non-destructive 3-address `lea rd, [ra + rb*1]` for `add` (`ra != rd`, `rb != rd`)
at `W32`/`W64`, swapping index if `rb = .rsp`. -/
def opBinLeaReg? (w : Width) (k : AluBinKind) (ra rb rd : Reg64) :
    Option (List Instr × FlagMask) :=
  if k == .add && (w == .W32 || w == .W64) && ra != rd && rb != rd then
    if rb != .rsp then some ([x64InsI w (.lea (regW w rd) (atSIB ra rb .s1 0))], maskNone)
    else if ra != .rsp then some ([x64InsI w (.lea (regW w rd) (atSIB rb ra .s1 0))], maskNone)
    else none
  else none

/-- Lower constant multiplication by `{3, 5, 6, 9, 10, 12}` into 1-cycle `lea` (`+ add`/`shl`) at
`W32`/`W64` when `ra != .rsp` (`%rsp` is illegal as SIB index). -/
def opBinLeaMul? (w : Width) (k : AluBinKind) (ra : Reg64) (cb : BitVec w.bits) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  if k == .mul && (w == .W32 || w == .W64) && ra != .rsp then
    if cb == 3#w.bits then
      some ([x64InsI w (.lea (regW w rd) (atSIB ra ra .s2 0))], maskNone)
    else if cb == 5#w.bits then
      some ([x64InsI w (.lea (regW w rd) (atSIB ra ra .s4 0))], maskNone)
    else if cb == 9#w.bits then
      some ([x64InsI w (.lea (regW w rd) (atSIB ra ra .s8 0))], maskNone)
    else if cb == 6#w.bits then
      some ([x64InsI w (.lea (regW w rd) (atSIB ra ra .s2 0)),
             aluBinI w .add rd (.reg (regW w rd))], maskAll)
    else if cb == 10#w.bits then
      some ([x64InsI w (.lea (regW w rd) (atSIB ra ra .s4 0)),
             aluBinI w .add rd (.reg (regW w rd))], maskAll)
    else if cb == 12#w.bits then
      some ([x64InsI w (.lea (regW w rd) (atSIB ra ra .s2 0)),
             x64InsI w (.shl (.reg (regW w rd)) (.imm8 (.int64 2)))], maskAll)
    else none
  else none

/-- Lower binary ALU ops (`add`, `sub`, `and`, `or`, `xor`, `mul`) at `w`,
including `VariantHint.disp` (`lea`), `VariantHint.decInc` (`inc`/`dec` preserving `CF`),
and flag-free non-destructive 3-address `lea` for `add`/`sub` imm when `ra != rd`. -/
def opBinIns (w : Width) (k : AluBinKind)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) (vh : VariantHint) :
    Option (List Instr × FlagMask) :=
  let tryDisp : Option (List Instr × FlagMask) :=
    match vh with
    | .disp off =>
      if (w == .W32 || w == .W64) && fitsImm32 off.toBitVec then
        match k, pa, pb with
        | .add, .gpr rb, .imm cb =>
          if off.toBitVec.setWidth w.bits == cb then
            some ([x64InsI w (.lea (regW w rd) (atDisp rb off))], maskNone)
          else none
        | .add, .imm ca, .gpr rb =>
          if off.toBitVec.setWidth w.bits == ca then
            some ([x64InsI w (.lea (regW w rd) (atDisp rb off))], maskNone)
          else none
        | .sub, .gpr rb, .imm cb =>
          if (-off.toBitVec).setWidth w.bits == cb then
            some ([x64InsI w (.lea (regW w rd) (atDisp rb off))], maskNone)
          else none
        | _, _, _ => none
      else none
    | _ => none
  let tryDecInc : Option (List Instr × FlagMask) :=
    match vh with
    | .decInc =>
      match k, pa, pb with
      | .sub, .gpr ra, .imm cb =>
        if cb == 1#w.bits then
          let pre := if ra == rd then [] else [movWI w rd ra]
          some (pre ++ [x64InsI w (.dec (.reg (regW w rd)))], maskDecInc)
        else if cb == -1#w.bits then
          let pre := if ra == rd then [] else [movWI w rd ra]
          some (pre ++ [x64InsI w (.inc (.reg (regW w rd)))], maskDecInc)
        else none
      | .add, .gpr ra, .imm cb =>
        if cb == 1#w.bits then
          let pre := if ra == rd then [] else [movWI w rd ra]
          some (pre ++ [x64InsI w (.inc (.reg (regW w rd)))], maskDecInc)
        else if cb == -1#w.bits then
          let pre := if ra == rd then [] else [movWI w rd ra]
          some (pre ++ [x64InsI w (.dec (.reg (regW w rd)))], maskDecInc)
        else none
      | .add, .imm ca, .gpr rb =>
        if ca == 1#w.bits then
          let pre := if rb == rd then [] else [movWI w rd rb]
          some (pre ++ [x64InsI w (.inc (.reg (regW w rd)))], maskDecInc)
        else none
      | _, _, _ => none
    | _ => none
  match tryDisp with
  | some res => some res
  | none =>
    match tryDecInc with
    | some res => some res
    | none =>
      let regImm (ra : Reg64) (cb : BitVec w.bits) : List Instr × FlagMask :=
        let pre := if ra == rd then [] else [movWI w rd ra]
        if w != .W64 || fitsImm32 (cb.setWidth 64) then
          (pre ++ [aluBinI w k rd (immBitsOp w cb)], maskAll)
        else
          ([moviI .r10 (cb.setWidth 64)] ++ pre ++ [aluBinI w k rd (.reg (regW w .r10))],
           maskAll)
      match pa, pb with
      | .imm ca, .imm cb =>
        some ([moviI rd ((k.eval ca cb).setWidth 64)], maskNone)
      | .gpr ra, .gpr rb =>
        if ra == rd then some ([aluBinI w k rd (.reg (regW w rb))], maskAll)
        else if k.isComm && rb == rd then some ([aluBinI w k rd (.reg (regW w ra))], maskAll)
        else if k == .sub && rb == rd then
          some ([x64InsI w (.neg (.reg (regW w rd))),
                 aluBinI w .add rd (.reg (regW w ra))], maskAll)
        else match opBinLeaReg? w k ra rb rd with
          | some res => some res
          | none =>
            if rb != rd then
              some ([movWI w rd ra, aluBinI w k rd (.reg (regW w rb))], maskAll)
            else
              some ([movWI w .r11 ra, aluBinI w k .r11 (.reg (regW w rb)),
                     movWI w rd .r11], maskAll)
      | .gpr ra, .imm cb =>
        some ((opBinLeaImm? w k ra cb rd <|> opBinLeaMul? w k ra cb rd).getD (regImm ra cb))
      | .imm ca, .gpr rb =>
        if k == .sub && ca == 0 then
          let pre := if rb == rd then [] else [movWI w rd rb]
          some (pre ++ [x64InsI w (.neg (.reg (regW w rd)))], maskAll)
        else if k.isComm then
          some ((opBinLeaImm? w k rb ca rd <|> opBinLeaMul? w k rb ca rd).getD (regImm rb ca))
        else
          some ([moviI .r11 (ca.setWidth 64), aluBinI w .sub .r11 (.reg (regW w rb)),
                 movWI w rd .r11], maskAll)
      | _, _ => none

/-- Lower `.shl`/`.lshr`/`.ashr`/`.rotl`/`.rotr` on `.bits w.bits` into `rd`.
For 32/64-bit, uses BMI2 flag-free `shlx`/`shrx`/`sarx` on variable shifts and `rorx` on
non-zero immediate rotates (`maskNone`); 8/16-bit and variable rotates use `%cl` / legacy ops. -/
def opShiftIns (w : Width) (sk : ShiftKind)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  let isWide := w == .W32 || w == .W64
  match pb with
  | .imm cb =>
    let cnt := cb.toNat % w.bits
    if cnt == 0 then opCopyBitsIns w pa rd
    else if isWide && sk.isRot then
      let rotCnt := if sk == .rotl then w.bits - cnt else cnt
      match pa with
      | .gpr ra =>
        some ([x64InsI w (.rorx (regW w rd) (.reg (regW w ra)) (.int64 (Int64.ofNat rotCnt)))],
              maskNone)
      | .imm ca => some ([moviI rd ((sk.eval ca cnt).setWidth 64)], maskNone)
      | .vec _  => none
    else
      let fallback : Option (List Instr × FlagMask) := do
        let setup ←
          match pa with
          | .gpr ra => some (if ra == rd then [] else [movWI w rd ra])
          | .imm ca => some [moviI rd (ca.setWidth 64)]
          | .vec _  => none
        let clob := if sk.isRot then maskCF ||| maskOF else maskAll
        some (setup ++
                [x64InsI w (sk.toOp (.reg (regW w rd)) (.imm8 (.int64 (Int64.ofNat cnt))))],
              clob)
      if isWide && sk == .shl then
        match pa, AddrScale.ofShift? cnt with
        | .gpr ra, some sc =>
          if ra != rd && ra != .rsp then
            some ([x64InsI w (.lea (regW w rd) (atIdx ra sc 0))], maskNone)
          else fallback
        | _, _ => fallback
      else fallback
  | .gpr rb =>
    if isWide && !sk.isRot then
      match sk.toBmi2Op?, pa with
      | some bmiOp, .gpr ra =>
        some ([x64InsI w (bmiOp (regW w rd) (.reg (regW w ra)) (regW w rb))], maskNone)
      | some bmiOp, .imm ca =>
        some ([moviI .r11 (ca.setWidth 64),
               x64InsI w (bmiOp (regW w rd) (.reg (regW w .r11)) (regW w rb))], maskNone)
      | _, _ => none
    else do
      let d1 ← argToBitsI w .r11 pa
      let mvRcx := if rb == .rcx then [] else [movWI w .rcx rb]
      let mask := shiftMaskRcxIns w
      let sh := x64InsI w (sk.toOp (.reg (regW w .r11)) .cl)
      let clob :=
        if w == .W8 || w == .W16 then maskAll else if sk.isRot then maskCF ||| maskOF else maskAll
      some ([d1, movI .r10 .rcx] ++ mvRcx ++ mask ++ [sh, movI .rcx .r10, movWI w rd .r11],
            clob)
  | .vec _ => none

/-- Lower `.clz`/`.cls`/`.ctz`/`.popcnt` on `.bits w.bits` into `rd` across `{8, 16, 32, 64}`.
Constant-folds `.imm` inputs with `maskNone`; lowers `.gpr` inputs via `lzcnt`/`tzcnt`/`popcnt`
(zero/sign-extending `8`/`16`-bit operands to `32` bits and adjusting counts) with `maskAll`. -/
def opBitcntIns (w : Width) (bk : BitcntKind)
    (pa : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  match pa with
  | .imm c => some ([moviI rd ((bk.eval w c).setWidth 64)], maskNone)
  | .vec _ => none
  | .gpr ra =>
    let insn := match w, bk with
      | .W32, .popcnt | .W64, .popcnt =>
        [x64InsI w (.popcnt (regW w rd) (.reg (regW w ra)))]
      | .W8, .popcnt | .W16, .popcnt =>
        [movWI w rd ra, x64InsI .W32 (.popcnt (d rd) (.reg (d rd)))]
      | .W32, .clz | .W64, .clz =>
        [x64InsI w (.lzcnt (regW w rd) (.reg (regW w ra)))]
      | .W8, .clz | .W16, .clz =>
        [movWI w rd ra,
         x64InsI .W32 (.lzcnt (d rd) (.reg (d rd))),
         aluBinI .W32 .sub rd (immBitsOp .W32 (BitVec.ofNat 32 (32 - w.bits)))]
      | .W32, .ctz | .W64, .ctz =>
        [x64InsI w (.tzcnt (regW w rd) (.reg (regW w ra)))]
      | .W8, .ctz | .W16, .ctz =>
        [movWI w rd ra,
         aluBinI .W32 .or rd (immBitsOp .W32 (BitVec.ofNat 32 (1 <<< w.bits))),
         x64InsI .W32 (.tzcnt (d rd) (.reg (d rd)))]
      | .W32, .cls | .W64, .cls =>
        [movWI w .r11 ra,
         x64InsI w (.sar (.reg (regW w .r11)) (.imm8 (.int64 (Int64.ofNat (w.bits - 1))))),
         aluBinI w .xor .r11 (.reg (regW w ra)),
         x64InsI w (.lzcnt (regW w rd) (.reg (regW w .r11))),
         x64InsI w (.dec (.reg (regW w rd)))]
      | .W8, .cls | .W16, .cls =>
        let movsx := match w with
          | .W8 => x64InsI .W32 (.movsx (.reg (d rd)) (.reg (b8 ra)))
          | _   => x64InsI .W32 (.movsx (.reg (d rd)) (.reg (h16 ra)))
        [movsx,
         movlI .r11 rd,
         x64InsI .W32 (.sar (.reg (d .r11)) (.imm8 (.int64 31))),
         aluBinI .W32 .xor rd (.reg (d .r11)),
         x64InsI .W32 (.lzcnt (d rd) (.reg (d rd))),
         aluBinI .W32 .sub rd (immBitsOp .W32 (BitVec.ofNat 32 (33 - w.bits)))]
    some (insn, maskAll)

/-- Lower `.udiv`/`.sdiv`/`.urem`/`.srem` on `.bits w.bits` into `rd`.
Widths `8`/`16` are zero/sign-extended to `32` bits and run through 32-bit `divl`/`idivl`. -/
def opDivIns (w : Width) (isSigned isRem : Bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  if rd == .r10 || rd == .r11 then none
  else do
    let extTo (t : Reg64) : PArg Reg64 RegMm CondCode (.bits w.bits) → Option Instr
      | .gpr r =>
        match w with
        | .W8  => some (x64InsI .W32 (if isSigned then .movsx (.reg (d t)) (.reg (b8 r))
                                      else .movzx (.reg (d t)) (.reg (b8 r))))
        | .W16 => some (x64InsI .W32 (if isSigned then .movsx (.reg (d t)) (.reg (h16 r))
                                      else .movzx (.reg (d t)) (.reg (h16 r))))
        | .W32 => some (movlI t r)
        | .W64 => some (movI t r)
      | .imm c =>
        let c64 := if isSigned then c.signExtend 64 else c.setWidth 64
        some (moviI t c64)
      | .vec _ => none
    let da ← extTo .r10 pa
    let db ← extTo .r11 pb
    let core : List Instr :=
      match w with
      | .W64 =>
        if isSigned then
          [movI .rdx .rax, x64InsI .W64 (.sar (.reg (q .rdx)) (.imm8 (.int64 63))),
           x64InsI .W64 (.idiv (.reg (q .r11)))]
        else
          [x64InsI .W32 (.xor (.reg (d .rdx)) (.reg (d .rdx))),
           x64InsI .W64 (.div (.reg (q .r11)))]
      | _ =>
        if isSigned then
          [movlI .rdx .rax, x64InsI .W32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31))),
           x64InsI .W32 (.idiv (.reg (d .r11)))]
        else
          [x64InsI .W32 (.xor (.reg (d .rdx)) (.reg (d .rdx))),
           x64InsI .W32 (.div (.reg (d .r11)))]
    let res : Reg64 := if isRem then .rdx else .rax
    let mvRes (dst src : Reg64) : List Instr :=
      if dst == src then []
      else [if w == .W64 then movI dst src else movlI dst src]
    let seq :=
      if rd == .rax then
        [da, db, movI .rax .r10, movI .r10 .rdx] ++ core ++ mvRes .rax res ++ [movI .rdx .r10]
      else if rd == .rdx then
        [da, db, movI .rdx .rax, movI .rax .r10, movI .r10 .rdx] ++ core ++
          mvRes .rdx res ++ [movI .rax .r10]
      else
        [da, db, movI rd .rax, movI .rax .r10, movI .r10 .rdx] ++ core ++
          [movI .r11 res, movI .rdx .r10, movI .rax rd,
           if w == .W64 then movI rd .r11 else movlI rd .r11]
    some (seq, maskAll)

/-- Emit `test %rx, %rx` when `cy == 0`, else `cmp $cy, %rx` (using `%r10` for 64-bit non-imm32). -/
def cmpRegImmIns (w : Width) (rx : Reg64) (cy : BitVec w.bits) : List Instr :=
  if cy == 0#w.bits then
    [x64InsI w (.test (.reg (regW w rx)) (.reg (regW w rx)))]
  else if w != .W64 || fitsImm32 (cy.setWidth 64) then
    [x64InsI w (.cmp (.reg (regW w rx)) (immBitsOp w cy))]
  else
    [moviI .r10 (cy.setWidth 64), x64InsI w (.cmp (.reg (regW w rx)) (.reg (regW w .r10)))]

/-- Emit `cmp`/`test` setting flags for `a - b` at width `w`. -/
def cmpDirectIns (w : Width) (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) :
    Option (List Instr) :=
  match pa, pb with
  | .gpr rx, .gpr ry => some [x64InsI w (.cmp (.reg (regW w rx)) (.reg (regW w ry)))]
  | .gpr rx, .imm cy => some (cmpRegImmIns w rx cy)
  | .imm cx, .gpr ry =>
    some [moviI .r10 (cx.setWidth 64), x64InsI w (.cmp (.reg (regW w .r10)) (.reg (regW w ry)))]
  | .imm cx, .imm cy =>
    some [moviI .r11 (cx.setWidth 64), moviI .r10 (cy.setWidth 64),
          x64InsI w (.cmp (.reg (regW w .r11)) (.reg (regW w .r10)))]
  | _, _ => none

/-- Lower `.cmp co (.bits w.bits)` into either `.gpr rd` or `.flag cc`. -/
def opCmpIns (w : Width) (co : CmpOp)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Instr × FlagMask) :=
  match pd with
  | .gpr rd =>
    match pa, pb with
    | .imm cx, .imm cy =>
      some ([moviI rd (BitVec.ofNat 64 (co.evalBits cx cy).toNat)], maskNone)
    | .imm cx, .gpr ry =>
      if w != .W64 || fitsImm32 (cx.setWidth 64) then
        some (cmpRegImmIns w ry cx ++ setccOnlyIns rd (condOf co.swap), maskAll)
      else
        some ([moviI .r10 (cx.setWidth 64),
               x64InsI w (.cmp (.reg (regW w .r10)) (.reg (regW w ry)))] ++
              setccOnlyIns rd (condOf co), maskAll)
    | _, _ => do
      let c ← cmpDirectIns w pa pb
      some (c ++ setccOnlyIns rd (condOf co), maskAll)
  | .flag cc =>
    match pa, pb with
    | .imm cx, .gpr ry =>
      if cc == condOf co.swap && (w != .W64 || fitsImm32 (cx.setWidth 64)) then
        some (cmpRegImmIns w ry cx, maskAll)
      else if cc == condOf co then
        some ([moviI .r10 (cx.setWidth 64),
               x64InsI w (.cmp (.reg (regW w .r10)) (.reg (regW w ry)))], maskAll)
      else if cc == condOf co.swap then
        some ([moviI .r10 (cx.setWidth 64),
               x64InsI w (.cmp (.reg (regW w ry)) (.reg (regW w .r10)))], maskAll)
      else none
    | _, _ =>
      if cc == condOf co then do
        let c ← cmpDirectIns w pa pb
        some (c, maskAll)
      else if cc == condOf co.swap then do
        let c ← cmpDirectIns w pb pa
        some (c, maskAll)
      else none
  | .vec _ => none

/-- Flag-driven conditional select (`rd := if cc then pa else pb`) preserving all status flags.
Emits `.W32` `cmovcc` for widths `8, 16, 32` and `.W64` `cmovcc` for `64`. -/
def selectFlagSeqIns (w : Width) (cc : CondCode)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) : Option (List Instr) :=
  let cw : Width := if w == .W64 then .W64 else .W32
  let cmov (cond : CondCode) (src : Reg64) : Instr :=
    x64InsI cw (.cmovcc cond (regW cw rd) (.reg (regW cw src)))
  match pa, pb with
  | .gpr ra, .gpr rb =>
    if ra == rb then some (if ra == rd then [] else [movWI cw rd ra])
    else if rd == rb then some [cmov cc ra]
    else if rd == ra then some [cmov (x64NegCond cc) rb]
    else some [movWI cw rd rb, cmov cc ra]
  | .gpr ra, .imm cb =>
    if rd == ra then some [moviI .r10 (cb.setWidth 64), cmov (x64NegCond cc) .r10]
    else some [moviI rd (cb.setWidth 64), cmov cc ra]
  | .imm ca, .gpr rb =>
    if rd == rb then some [moviI .r10 (ca.setWidth 64), cmov cc .r10]
    else some [moviI rd (ca.setWidth 64), cmov (x64NegCond cc) rb]
  | .imm ca, .imm cb =>
    some [moviI rd (cb.setWidth 64), moviI .r10 (ca.setWidth 64), cmov cc .r10]
  | _, _ => none

/-- Lower `.select (.bits w.bits)` (`cmovcc`, never branching). -/
def opSelectIns (w : Width) (pc : PArg Reg64 RegMm CondCode .bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  match pc with
  | .imm b   => opCopyBitsIns w (if b then pa else pb) rd
  | .flag cc => (selectFlagSeqIns w cc pa pb rd).map (·, maskNone)
  | .gpr rc  =>
    (selectFlagSeqIns w .nz pa pb rd).map fun seq =>
      (x64InsI .W8 (.test (.reg (b8 rc)) (.reg (b8 rc))) :: seq, maskAll)
  | .vec _   => none

/-- Lower `.ofBool` (`n ∈ {8, 16, 32, 64}`) into `rd` (zero-extending from low 8 bits). -/
def opOfBoolIns (pa : PArg Reg64 RegMm CondCode .bool) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  match pa with
  | .gpr rs  => some ([x64InsI .W32 (.movzx (.reg (d rd)) (.reg (b8 rs)))], maskNone)
  | .imm b   => some ([moviI rd (BitVec.ofNat 64 b.toNat)], maskNone)
  | .flag cc => some (setccMoveIns rd cc, maskNone)
  | .vec _   => none

/-- Lower `.zext m n` (`m < n`, `m, n ∈ {8, 16, 32, 64}`) into `rd`. -/
def opZextIns (m n : Nat) (pa : PArg Reg64 RegMm CondCode (.bits m)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  if !(x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n) then none
  else
    match pa with
    | .imm c => some ([moviI rd (c.setWidth 64)], maskNone)
    | .gpr r =>
      match m with
      | 8  => some ([x64InsI .W32 (.movzx (.reg (d rd)) (.reg (b8 r)))], maskNone)
      | 16 => some ([x64InsI .W32 (.movzx (.reg (d rd)) (.reg (h16 r)))], maskNone)
      | 32 => some ([movlI rd r], maskNone)
      | _  => none
    | .vec _ => none

/-- Lower `.sext m n` (`m < n`, `m, n ∈ {8, 16, 32, 64}`) into `rd`. -/
def opSextIns (m n : Nat) (pa : PArg Reg64 RegMm CondCode (.bits m)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  if !(x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n) then none
  else
    match pa with
    | .imm c => some ([moviI rd ((c.signExtend n).setWidth 64)], maskNone)
    | .gpr r =>
      match m, n with
      | 8,  64 => some ([x64InsI .W64 (.movsx (.reg (q rd)) (.reg (b8 r)))], maskNone)
      | 8,  _  => some ([x64InsI .W32 (.movsx (.reg (d rd)) (.reg (b8 r)))], maskNone)
      | 16, 64 => some ([x64InsI .W64 (.movsx (.reg (q rd)) (.reg (h16 r)))], maskNone)
      | 16, _  => some ([x64InsI .W32 (.movsx (.reg (d rd)) (.reg (h16 r)))], maskNone)
      | 32, 64 => some ([x64InsI .W64 (.movsx (.reg (q rd)) (.reg (d r)))], maskNone)
      | _,  _  => none
    | .vec _ => none

/-- Lower `.trunc m n` (`n < m`, `m, n ∈ {8, 16, 32, 64}`) into `rd`. -/
def opTruncIns (m n : Nat) (pa : PArg Reg64 RegMm CondCode (.bits m)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  if !(x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (n + 1) m) then none
  else
    let res := fun (w : Width) =>
      match pa with
      | .imm c => some ([moviI rd ((c.setWidth n).setWidth 64)], maskNone)
      | .gpr r => if r == rd then some ([], maskNone) else some ([movWI w rd r], maskNone)
      | .vec _ => none
    match n with
    | 8  => res .W8
    | 16 => res .W16
    | 32 => res .W32
    | _  => none

/-- Lower `.bswap (.bits n)` (`n ∈ {16, 32, 64}`) into `rd`. -/
def opBswapIns (n : Nat) (pa : PArg Reg64 RegMm CondCode (.bits n)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  match n, pa with
  | 16, .imm c => some ([moviI rd ((bswapBits c).setWidth 64)], maskNone)
  | 16, .gpr r =>
    let pre := if r == rd then [] else [movWI .W16 rd r]
    some (pre ++ [x64InsI .W16 (.rol (.reg (h16 rd)) (.imm8 (.int64 8)))], maskCF ||| maskOF)
  | 32, .imm c => some ([moviI rd ((bswapBits c).setWidth 64)], maskNone)
  | 32, .gpr r =>
    let pre := if r == rd then [] else [movlI rd r]
    some (pre ++ [x64InsI .W32 (.bswap (d rd))], maskNone)
  | 64, .imm c => some ([moviI rd (bswapBits c)], maskNone)
  | 64, .gpr r =>
    let pre := if r == rd then [] else [movI rd r]
    some (pre ++ [x64InsI .W64 (.bswap (q rd))], maskNone)
  | _, _ => none

/-- Two-address carry/borrow core preserving `CF` (or `OF`) before the operation runs. -/
def carryCoreIns (w : Width) (isComm : Bool)
    (mkReg : Reg64 → Reg64 → Instr) (mkImm : Reg64 → BitVec w.bits → Instr)
    (supportsImm : Bool) (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr) :=
  let regImm (ra : Reg64) (cb : BitVec w.bits) : List Instr :=
    let pre := if ra == rd then [] else [movWI w rd ra]
    if supportsImm && (w != .W64 || fitsImm32 (cb.setWidth 64)) then
      pre ++ [mkImm rd cb]
    else
      [moviI .r10 (cb.setWidth 64)] ++ pre ++ [mkReg rd .r10]
  match pa, pb with
  | .gpr ra, .gpr rb =>
    if ra == rd then some [mkReg rd rb]
    else if isComm && rb == rd then some [mkReg rd ra]
    else if rb != rd then some [movWI w rd ra, mkReg rd rb]
    else some [movWI w .r11 ra, mkReg .r11 rb, movWI w rd .r11]
  | .gpr ra, .imm cb => some (regImm ra cb)
  | .imm ca, .gpr rb =>
    if isComm then some (regImm rb ca)
    else some [moviI .r11 (ca.setWidth 64), mkReg .r11 rb, movWI w rd .r11]
  | .imm ca, .imm cb =>
    some (moviI rd (ca.setWidth 64) :: regImm rd cb)
  | _, _ => none

/-- Lower `.addc w.bits` (`w ∈ {.W32, .W64}`), supporting `.default` (`adc`), `.adcx`, `.adox`. -/
def opAddcIns (w : Width)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pc : PArg Reg64 RegMm CondCode .bool)
    (dsum : PDst Reg64 RegMm CondCode (.bits w.bits)) (dc : PDst Reg64 RegMm CondCode .bool)
    (vh : VariantHint) : Option (List Instr × FlagMask) :=
  match dsum with
  | .gpr rd =>
    let distinctDst : Bool := match dc with | .gpr rc => rc != rd | _ => true
    if !distinctDst then none
    else
      let coutSeq (flagCc : CondCode) : Option (List Instr) :=
        match dc with
        | .flag cc => if cc == flagCc then some [] else none
        | .gpr rc  => some (setccMoveIns rc flagCc)
        | .vec _   => none
      let adcFallback : Option (List Instr × FlagMask) := do
        let setupCf ←
          match pc with
          | .flag .c   => some []
          | .flag cc   =>
            some [x64InsI .W8 (.setcc cc (.reg (b8 .r10))), x64InsI .W8 (.neg (.reg (b8 .r10)))]
          | .gpr rc    =>
            some [x64InsI .W8 (.mov (.reg (b8 .r10)) (.reg (b8 rc))),
                  x64InsI .W8 (.neg (.reg (b8 .r10)))]
          | .imm false => some [x64InsI .W32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
          | .imm true  => some [moviI .r10 1, x64InsI .W8 (.neg (.reg (b8 .r10)))]
          | .vec _     => none
        let core ← carryCoreIns w true
          (fun dst src => x64InsI w (.adc (.reg (regW w dst)) (.reg (regW w src))))
          (fun dst imm => x64InsI w (.adc (.reg (regW w dst)) (immBitsOp w imm)))
          true pa pb rd
        let tail ← coutSeq .c
        some (setupCf ++ core ++ tail, maskAll)
      match vh with
      | .adcx =>
        match pc with
        | .flag .c => do
          let core ← carryCoreIns w true
            (fun dst src => x64InsI w (.adcx (regW w dst) (.reg (regW w src))))
            (fun dst _ => x64InsI w (.adcx (regW w dst) (.reg (regW w dst))))
            false pa pb rd
          let tail ← coutSeq .c
          some (core ++ tail, maskCF)
        | _ => adcFallback
      | .adox =>
        match pc with
        | .flag .o => do
          let core ← carryCoreIns w true
            (fun dst src => x64InsI w (.adox (regW w dst) (.reg (regW w src))))
            (fun dst _ => x64InsI w (.adox (regW w dst) (.reg (regW w dst))))
            false pa pb rd
          let tail ← coutSeq .o
          some (core ++ tail, maskOF)
        | _ => adcFallback
      | _ => adcFallback
  | .vec _ => none

/-- Lower `.subb w.bits` (`w ∈ {.W32, .W64}`) via `sbb`. -/
def opSubbIns (w : Width)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pc : PArg Reg64 RegMm CondCode .bool)
    (ddiff : PDst Reg64 RegMm CondCode (.bits w.bits)) (db : PDst Reg64 RegMm CondCode .bool) :
    Option (List Instr × FlagMask) :=
  match ddiff with
  | .gpr rd =>
    let distinctDst : Bool := match db with | .gpr rb => rb != rd | _ => true
    if !distinctDst then none
    else do
      let setupCf ←
        match pc with
        | .flag .c   => some []
        | .flag cc   =>
          some [x64InsI .W8 (.setcc cc (.reg (b8 .r10))), x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .gpr rc    =>
          some [x64InsI .W8 (.mov (.reg (b8 .r10)) (.reg (b8 rc))),
                x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .imm false => some [x64InsI .W32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
        | .imm true  => some [moviI .r10 1, x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .vec _     => none
      let core ← carryCoreIns w false
        (fun dst src => x64InsI w (.sbb (.reg (regW w dst)) (.reg (regW w src))))
        (fun dst imm => x64InsI w (.sbb (.reg (regW w dst)) (immBitsOp w imm)))
        true pa pb rd
      let tail ←
        match db with
        | .flag .c => some []
        | .flag _  => none
        | .gpr rb  => some (setccMoveIns rb .c)
        | .vec _   => none
      some (setupCf ++ core ++ tail, maskAll)
  | .vec _ => none

/-- Lower `.umulw w.bits` / `.smulw w.bits` (`w ∈ {.W32, .W64}`), supporting `.mulxFast`. -/
def opMulwIns (w : Width) (isSigned : Bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits))
    (dlo dhi : PDst Reg64 RegMm CondCode (.bits w.bits)) (vh : VariantHint) :
    Option (List Instr × FlagMask) :=
  match dlo, dhi with
  | .gpr rlo, .gpr rhi =>
    if rlo == rhi then none
    else if !isSigned && vh == .mulxFast then do
      let da ← argToBitsI w .r11 pa
      let saveRdx := if rlo == .rdx || rhi == .rdx then [] else [movI .r10 .rdx]
      let loadB ←
        match pb with
        | .gpr .rdx => some []
        | _ => do let db ← argToBitsI w .rdx pb; some [db]
      let mulxDir := x64InsI w (.mulx (regW w rhi) (regW w rlo) (.reg (regW w .r11)))
      let restRdx := if rlo == .rdx || rhi == .rdx then [] else [movI .rdx .r10]
      some ([da] ++ saveRdx ++ loadB ++ [mulxDir] ++ restRdx, maskNone)
    else do
      let da ← argToBitsI w .r10 pa
      let db ← argToBitsI w .r11 pb
      let mulDir := x64InsI w (if isSigned then .imul1 (.reg (regW w .r11))
                                           else .mul (.reg (regW w .r11)))
      let seq :=
        if rlo == .rax && rhi == .rdx then
          [da, db, movI .rax .r10, mulDir]
        else if rlo == .rdx && rhi == .rax then
          [da, db, movI .rax .r10, mulDir, movI .r10 .rax, movI .rax .rdx, movI .rdx .r10]
        else if rlo == .rax then
          [da, db, movI .rax .r10, movI .r10 .rdx, mulDir, movI rhi .rdx, movI .rdx .r10]
        else if rhi == .rdx then
          [da, db, movI rlo .rax, movI .rax .r10, mulDir,
           movI .r10 rlo, movI rlo .rax, movI .rax .r10]
        else if rlo == .rdx then
          [da, db, movI rhi .rax, movI .rax .r10, mulDir,
           movI .r10 rhi, movI rhi .rdx, movI .rdx .rax, movI .rax .r10]
        else if rhi == .rax then
          [da, db, movI rlo .rdx, movI .rax .r10, mulDir,
           movI .r10 rlo, movI rlo .rax, movI .rax .rdx, movI .rdx .r10]
        else
          [da, db, movI rlo .rax, movI rhi .rdx, movI .rax .r10, mulDir,
           movI .r10 rlo, movI rlo .rax, movI .rax .r10,
           movI .r10 rhi, movI rhi .rdx, movI .rdx .r10]
      some (seq, maskAll)
  | _, _ => none

/-- Lower `.fshl w.bits` / `.fshr w.bits` (`w ∈ {.W32, .W64}`) via `shld`/`shrd`.
Note `shld dst src` computes high bits of `(dst ++ src) <<< c`; `shrd dst src` computes low
bits of `(src ++ dst) >>> c`, so `fshr` passes `dst := lo`, `src := hi`. -/
def opFunnelIns (w : Width) (isRight : Bool)
    (pa pb pc : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  let dstArg := if isRight then pb else pa
  let srcArg := if isRight then pa else pb
  let mkShift (cnt : ShiftCountExpr) : Instr :=
    x64InsI w (if isRight then .shrd (.reg (regW w .r11)) (regW w .r10) cnt
                          else .shld (.reg (regW w .r11)) (regW w .r10) cnt)
  match pc with
  | .imm c =>
    let cnt := c.toNat % w.bits
    if cnt == 0 then opCopyBitsIns w dstArg rd
    else do
      let dDst ← argToBitsI w .r11 dstArg
      let dSrc ← argToBitsI w .r10 srcArg
      some ([dDst, dSrc, mkShift (.imm8 (.int64 (Int64.ofNat cnt))), movWI w rd .r11], maskAll)
  | .gpr rc => do
    let dDst ← argToBitsI w .r11 dstArg
    let dSrc ← argToBitsI w .r10 srcArg
    let sh := mkShift .cl
    if rd == .rcx then
      let mvRcx := if rc == .rcx then [] else [movI .rcx rc]
      some ([dDst, dSrc] ++ mvRcx ++ [sh, movWI w .rcx .r11], maskAll)
    else if rc == rd then
      some ([dDst, dSrc,
             x64InsI .W64 (.xor (.reg (q .rcx)) (.reg (q rd))),
             x64InsI .W64 (.xor (.reg (q rd)) (.reg (q .rcx))),
             x64InsI .W64 (.xor (.reg (q .rcx)) (.reg (q rd))),
             sh, movI .rcx rd, movWI w rd .r11], maskAll)
    else
      let mvRcx := if rc == .rcx then [] else [movI .rcx rc]
      some ([dDst, dSrc, movI rd .rcx] ++ mvRcx ++ [sh, movI .rcx rd, movWI w rd .r11], maskAll)
  | .vec _ => none

/-! ## 4. Top-level `supportsScalarOp`, `op`, `load`, `store`, and `x64Gpr` -/

/-- Pure `Bool` kernel-`rfl`-safe 1-for-1 scalar opcode predicate for `x64Gpr`. -/
def x64SupportsScalarOp {sig rs : List Ty} (code : OpCode sig rs)
    (_args : Tup (Arg (fun _ => Unit)) sig) : Bool :=
  match sig, rs, code with
  | _, _, .copy (.bits n) | _, _, .add (.bits n) | _, _, .sub (.bits n) | _, _, .mul (.bits n)
  | _, _, .neg (.bits n) | _, _, .and (.bits n) | _, _, .or (.bits n) | _, _, .xor (.bits n)
  | _, _, .not (.bits n) | _, _, .shl (.bits n) | _, _, .lshr (.bits n) | _, _, .ashr (.bits n)
  | _, _, .rotl (.bits n) | _, _, .rotr (.bits n) | _, _, .ofBool n
  | _, _, .udiv n | _, _, .sdiv n | _, _, .urem n | _, _, .srem n
  | _, _, .clz n | _, _, .cls n | _, _, .ctz n | _, _, .popcnt n
  | _, _, .cmp _ (.bits n) _ _ | _, _, .select (.bits n) => x64BitWidths.contains n
  | _, _, .copy .bool | _, _, .and .bool | _, _, .or .bool
  | _, _, .xor .bool | _, _, .not .bool => true
  | _, _, .bswap (.bits n) => [16, 32, 64].contains n
  | _, _, .addc n | _, _, .subb n | _, _, .umulw n | _, _, .smulw n
  | _, _, .fshl n | _, _, .fshr n => x64WideWidths.contains n
  | _, _, .zext m n | _, _, .sext m n =>
    x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n
  | _, _, .trunc m n =>
    x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (n + 1) m
  | _, _, .bitcast (.bits m) (.bits n) _ =>
    x64BitWidths.contains m && x64BitWidths.contains n
  | _, _, _ => false

/-- Lower a scalar `OpCode` into an instruction list and its flag clobber mask. -/
def x64OpIns : {sig rs : List Ty} → OpCode sig rs → Tup (PArg Reg64 RegMm CondCode) sig →
    Tup (PDst Reg64 RegMm CondCode) rs → VariantHint → Option (List Instr × FlagMask)
  | _, _, .copy (.bits n), (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opCopyBitsIns w pa' rd
  | _, _, .copy .bool, (pa, ()), (pd, ()), _ => opCopyBoolIns pa pd
  | _, _, .add (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBinIns w .add pa' pb' rd vh
  | _, _, .sub (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBinIns w .sub pa' pb' rd vh
  | _, _, .mul (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBinIns w .mul pa' pb' rd vh
  | _, _, .and (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBinIns w .and pa' pb' rd vh
  | _, _, .or (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBinIns w .or pa' pb' rd vh
  | _, _, .xor (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBinIns w .xor pa' pb' rd vh
  | _, _, .neg (.bits n), (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opNegIns w pa' rd
  | _, _, .not (.bits n), (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opNotIns w pa' rd
  | _, _, .and .bool, (pa, pb, ()), (pd, ()), _ => opBoolBinIns (· && ·) .and pa pb pd
  | _, _, .or  .bool, (pa, pb, ()), (pd, ()), _ => opBoolBinIns (· || ·) .or  pa pb pd
  | _, _, .xor .bool, (pa, pb, ()), (pd, ()), _ => opBoolBinIns (· ^^ ·) .xor pa pb pd
  | _, _, .not .bool, (pa, ()), (pd, ()), _ => opBoolNotIns pa pd
  | _, _, .shl  (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShiftIns w .shl pa' pb' rd
  | _, _, .lshr (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShiftIns w .lshr pa' pb' rd
  | _, _, .ashr (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShiftIns w .ashr pa' pb' rd
  | _, _, .rotl (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShiftIns w .rotl pa' pb' rd
  | _, _, .rotr (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShiftIns w .rotr pa' pb' rd
  | _, _, .fshl n, (pa, pb, pc, ()), (.gpr rd, ()), _ =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb, pc)
      fun w (pa', pb', pc') => opFunnelIns w false pa' pb' pc' rd
  | _, _, .fshr n, (pa, pb, pc, ()), (.gpr rd, ()), _ =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb, pc)
      fun w (pa', pb', pc') => opFunnelIns w true pa' pb' pc' rd
  | _, _, .bswap (.bits n), (pa, ()), (.gpr rd, ()), _ => opBswapIns n pa rd
  | _, _, .clz n, (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opBitcntIns w .clz pa' rd
  | _, _, .cls n, (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opBitcntIns w .cls pa' rd
  | _, _, .ctz n, (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opBitcntIns w .ctz pa' rd
  | _, _, .popcnt n, (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opBitcntIns w .popcnt pa' rd
  | _, _, .cmp co (.bits n) _ h, (pa, pb, ()), (pd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') =>
        opCmpIns w co pa' pb' (cast (congrArg (PDst Reg64 RegMm CondCode) h) pd)
  | _, _, .select (.bits n), (pc, pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opSelectIns w pc pa' pb' rd
  | _, _, .zext m n, (pa, ()), (.gpr rd, ()), _ => opZextIns m n pa rd
  | _, _, .sext m n, (pa, ()), (.gpr rd, ()), _ => opSextIns m n pa rd
  | _, _, .trunc m n, (pa, ()), (.gpr rd, ()), _ => opTruncIns m n pa rd
  | _, _, .ofBool n, (pa, ()), (.gpr rd, ()), _ =>
    if x64BitWidths.contains n then opOfBoolIns pa rd else none
  | _, _, .addc n, (pa, pb, pc, ()), (dsum, dc, ()), vh =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k)) n (pa, pb, dsum)
      fun w (pa', pb', dsum') => opAddcIns w pa' pb' pc dsum' dc vh
  | _, _, .subb n, (pa, pb, pc, ()), (ddiff, db, ()), _ =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k)) n (pa, pb, ddiff)
      fun w (pa', pb', ddiff') => opSubbIns w pa' pb' pc ddiff' db
  | _, _, .umulw n, (pa, pb, ()), (dlo, dhi, ()), vh =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k)) n (pa, pb, dlo, dhi)
      fun w (pa', pb', dlo', dhi') => opMulwIns w false pa' pb' dlo' dhi' vh
  | _, _, .smulw n, (pa, pb, ()), (dlo, dhi, ()), vh =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k)) n (pa, pb, dlo, dhi)
      fun w (pa', pb', dlo', dhi') => opMulwIns w true pa' pb' dlo' dhi' vh
  | _, _, .udiv n, (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opDivIns w false false pa' pb' rd
  | _, _, .sdiv n, (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opDivIns w true false pa' pb' rd
  | _, _, .urem n, (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opDivIns w false true pa' pb' rd
  | _, _, .srem n, (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opDivIns w true true pa' pb' rd
  | _, _, .bitcast (.bits m) (.bits n) _, (pa, ()), (.gpr rd, ()), _ =>
    if x64BitWidths.contains n then
      withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) m pa fun w pa' =>
        opCopyBitsIns w pa' rd
    else none
  | _, _, _, _, _, _ => none

/-- Lower a scalar `OpCode` into x64 directives and its flag clobber mask. -/
def x64Op {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) rs) (vh : VariantHint) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64OpIns code pas dsts vh)

/-- Lower a scalar memory load of type `t` into `rd` (instruction list). -/
def x64LoadIns (t : Ty) (rd : Reg64) (a : AddrArg Reg64) : Option (List Instr × FlagMask) :=
  if !x64AddrValid a then none else
  let pre := (addrToExprIns a).1
  let addr := (addrToExprIns a).2.1
  let clob := (addrToExprIns a).2.2
  match t with
  | .bool | .bits 8 =>
    some (pre ++ [x64InsI .W32 (.movzx (.reg (d rd)) (.mem addr : RegOrMem .W8))], clob)
  | .bits 16 =>
    some (pre ++ [x64InsI .W32 (.movzx (.reg (d rd)) (.mem addr : RegOrMem .W16))], clob)
  | .bits 32 =>
    some (pre ++ [x64InsI .W32 (.mov (.reg (d rd)) (.mem addr))], clob)
  | .bits 64 =>
    some (pre ++ [x64InsI .W64 (.mov (.reg (q rd)) (.mem addr))], clob)
  | _ => none

/-- Lower a scalar memory load of type `t` into `rd`. -/
def x64Load (t : Ty) (rd : Reg64) (a : AddrArg Reg64) : Option (List Directive × FlagMask) :=
  emitCleanPair (x64LoadIns t rd a)

/-- Lower a fused sign-extending load `rd := (load (.bits m) a).signExtend 64` (`movs{b,w,l}q`). -/
def x64LoadSextIns (m n : Nat) (rd : Reg64) (a : AddrArg Reg64) :
    Option (List Instr × FlagMask) :=
  if !(x64AddrValid a && Nat.blt m n && Nat.ble n 64) then none else
  let pre := (addrToExprIns a).1
  let addr := (addrToExprIns a).2.1
  let clob := (addrToExprIns a).2.2
  match m with
  | 8 => some (pre ++ [x64InsI .W64 (.movsx (.reg (q rd)) (.mem addr : RegOrMem .W8))], clob)
  | 16 => some (pre ++ [x64InsI .W64 (.movsx (.reg (q rd)) (.mem addr : RegOrMem .W16))], clob)
  | 32 => some (pre ++ [x64InsI .W64 (.movsx (.reg (q rd)) (.mem addr : RegOrMem .W32))], clob)
  | _ => none

/-- Lower a fused sign-extending load (see `x64LoadSextIns`). -/
def x64LoadSext (m n : Nat) (rd : Reg64) (a : AddrArg Reg64) : Option (List Directive × FlagMask) :=
  emitCleanPair (x64LoadSextIns m n rd a)

/-- Lower a scalar memory store of type `t` (instruction list). -/
def x64StoreIns : (t : Ty) → PArg Reg64 RegMm CondCode t → AddrArg Reg64 →
    Option (List Instr × FlagMask)
  | .bool, pa, a =>
    if !x64AddrValid a then none else
    let pre := (addrToExprIns a).1
    let addr := (addrToExprIns a).2.1
    let clob := (addrToExprIns a).2.2
    match pa with
    | .gpr r => some (pre ++ [x64InsI .W8 (.mov (.mem addr) (.reg (b8 r)))], clob)
    | .imm b =>
      some (pre ++ [x64InsI .W8 (.mov (.mem addr) (.imm (.int64 (Int64.ofNat b.toNat))))], clob)
    | .flag cc =>
      some (x64InsI .W8 (.setcc cc (.reg (b8 .r11))) ::
            pre ++ [x64InsI .W8 (.mov (.mem addr) (.reg (b8 .r11)))], clob)
    | .vec _ => none
  | .bits n, pa, a =>
    if !x64AddrValid a then none else
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      let pre := (addrToExprIns a).1
      let addr := (addrToExprIns a).2.1
      let clob := (addrToExprIns a).2.2
      match pa' with
      | .gpr r => some (pre ++ [x64InsI w (.mov (.mem addr) (.reg (regW w r)))], clob)
      | .imm c =>
        if w != .W64 || fitsImm32 (c.setWidth 64) then
          some (pre ++ [x64InsI w (.mov (.mem addr) (immBitsOp w c))], clob)
        else
          some (pre ++ [moviI .r11 (c.setWidth 64),
                        x64InsI .W64 (.mov (.mem addr) (.reg (q .r11)))], clob)
      | .vec _ => none
  | _, _, _ => none

/-- Lower a scalar memory store of type `t`. -/
def x64Store (t : Ty) (pa : PArg Reg64 RegMm CondCode t) (a : AddrArg Reg64) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64StoreIns t pa a)

/-- Emit `test` setting flags for `a &&& b` at width `w`. -/
def testDirectIns (w : Width) (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) :
    Option (List Instr) :=
  let regImm (rx : Reg64) (cy : BitVec w.bits) : List Instr :=
    if w != .W64 || fitsImm32 (cy.setWidth 64) then
      [x64InsI w (.test (.reg (regW w rx)) (immBitsOp w cy))]
    else
      [moviI .r10 (cy.setWidth 64), x64InsI w (.test (.reg (regW w rx)) (.reg (regW w .r10)))]
  match pa, pb with
  | .gpr rx, .gpr ry => some [x64InsI w (.test (.reg (regW w rx)) (.reg (regW w ry)))]
  | .gpr rx, .imm cy => some (regImm rx cy)
  | .imm cx, .gpr ry => some (regImm ry cx)
  | .imm cx, .imm cy =>
    some [moviI .r11 (cx.setWidth 64), moviI .r10 (cy.setWidth 64),
          x64InsI w (.test (.reg (regW w .r11)) (.reg (regW w .r10)))]
  | _, _ => none

/-- Lower fused `(pa &&& pb) ==/!= 0` bit-test (`neg = false` -> `== 0`, `true` -> `!= 0`). -/
def x64TestOpIns (n : Nat) (neg : Bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Instr × FlagMask) :=
  withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                          PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb) fun w (pa', pb') =>
    let wantCc : CondCode := if neg then .nz else .z
    match pd with
    | .gpr rd =>
      match pa', pb' with
      | .imm cx, .imm cy =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (cx &&& cy) 0#w.bits
        some ([moviI rd (BitVec.ofNat 64 res.toNat)], maskNone)
      | _, _ => do
        let t ← testDirectIns w pa' pb'
        some (t ++ setccOnlyIns rd wantCc, maskAll)
    | .flag cc =>
      if cc == wantCc then do
        let t ← testDirectIns w pa' pb'
        some (t, maskAll)
      else none
    | .vec _ => none

/-- Lower fused `(pa &&& pb) ==/!= 0` bit-test into x64 directives. -/
def x64TestOp (n : Nat) (neg : Bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64TestOpIns n neg pa pb pd)

/-- Emit `cmp` between memory operand `addr` and `pb` (`swapped = false` -> `[addr] - pb`,
`swapped = true` -> `pb - [addr]`). Uses `.r11` for immediates (leaving `.r10` for `addr`). -/
def cmpMemCoreIns (w : Width) (addr : AddrExpr) (swapped : Bool)
    (pb : PArg Reg64 RegMm CondCode (.bits w.bits)) : Option (List Instr) :=
  match pb with
  | .gpr ry =>
    if swapped then
      some [x64InsI w (.cmp (.reg (regW w ry)) (.regOrMem (.mem addr)))]
    else
      some [x64InsI w (.cmp (.mem addr) (.reg (regW w ry)))]
  | .imm cy =>
    if swapped then
      some [moviI .r11 (cy.setWidth 64),
            x64InsI w (.cmp (.reg (regW w .r11)) (.regOrMem (.mem addr)))]
    else if w != .W64 || fitsImm32 (cy.setWidth 64) then
      some [x64InsI w (.cmp (.mem addr) (immBitsOp w cy))]
    else
      some [moviI .r11 (cy.setWidth 64), x64InsI w (.cmp (.mem addr) (.reg (regW w .r11)))]
  | .vec _ => none

/-- Lower fused `co.evalBits (load (.bits n) a) pb` via memory-operand `cmp{b,w,l,q}`. -/
def x64CmpMemIns (co : CmpOp) (n : Nat) (a : AddrArg Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Instr × FlagMask) :=
  if !x64AddrValid a then none else
  withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pb fun w pb' =>
    let pre := (addrToExprIns a).1
    let addr := (addrToExprIns a).2.1
    match pd with
    | .gpr rd => do
      let core ← cmpMemCoreIns w addr false pb'
      some (pre ++ core ++ setccOnlyIns rd (condOf co), maskAll)
    | .flag cc =>
      if cc == condOf co then do
        let core ← cmpMemCoreIns w addr false pb'
        some (pre ++ core, maskAll)
      else if cc == condOf co.swap then do
        let core ← cmpMemCoreIns w addr true pb'
        some (pre ++ core, maskAll)
      else none
    | .vec _ => none

/-- Lower fused `co.evalBits (load (.bits n) a) pb` into x64 directives. -/
def x64CmpMem (co : CmpOp) (n : Nat) (a : AddrArg Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64CmpMemIns co n a pb pd)

/-- Lower fused `(load (.bits n) a &&& pb) ==/!= 0` via memory-operand `test{b,w,l,q}`. -/
def x64TestMemIns (n : Nat) (neg : Bool) (a : AddrArg Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Instr × FlagMask) :=
  if !x64AddrValid a then none else
  withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pb fun w pb' =>
    let pre := (addrToExprIns a).1
    let addr := (addrToExprIns a).2.1
    let core? : Option (List Instr) :=
      match pb' with
      | .gpr ry => some [x64InsI w (.test (.mem addr) (.reg (regW w ry)))]
      | .imm cy =>
        if w != .W64 || fitsImm32 (cy.setWidth 64) then
          some [x64InsI w (.test (.mem addr) (immBitsOp w cy))]
        else
          some [moviI .r11 (cy.setWidth 64), x64InsI w (.test (.mem addr) (.reg (regW w .r11)))]
      | .vec _ => none
    let wantCc : CondCode := if neg then .nz else .z
    match pd with
    | .gpr rd => do
      let core ← core?
      some (pre ++ core ++ setccOnlyIns rd wantCc, maskAll)
    | .flag cc =>
      if cc == wantCc then do
        let core ← core?
        some (pre ++ core, maskAll)
      else none
    | .vec _ => none

/-- Lower fused `(load (.bits n) a &&& pb) ==/!= 0` into x64 directives. -/
def x64TestMem (n : Nat) (neg : Bool) (a : AddrArg Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64TestMemIns n neg a pb pd)

/-- Map scalar binary arithmetic/logic `OpCode` to `AluBinKind`. -/
def x64AluMemKind? : {n : Nat} → OpCode [.bits n, .bits n] [.bits n] → Option AluBinKind
  | _, .add (.bits _) => some .add
  | _, .sub (.bits _) => some .sub
  | _, .and (.bits _) => some .and
  | _, .or  (.bits _) => some .or
  | _, .xor (.bits _) => some .xor
  | _, .mul (.bits _) => some .mul
  | _, _ => none

/-- Lower binary op with one memory operand into `rd` (`memRhs = false` => `op mem pb`). -/
def x64AluMemIns (n : Nat) (code : OpCode [.bits n, .bits n] [.bits n]) (memRhs : Bool)
    (a : AddrArg Reg64) (pb : PArg Reg64 RegMm CondCode (.bits n)) (rd : Reg64) :
    Option (List Instr × FlagMask) :=
  if !x64AddrValid a then none else
  match x64AluMemKind? code with
  | none => none
  | some k =>
    if !(memRhs || k.isComm) || (k == .mul && n == 8) then none else
    withWidth (F := fun m => PArg Reg64 RegMm CondCode (.bits m)) n pb fun w pb' =>
      let pre := (addrToExprIns a).1
      let addr := (addrToExprIns a).2.1
      let alu := aluBinI w k rd (.regOrMem (.mem addr))
      match pb' with
      | .gpr rs =>
        if rs == rd then some (pre ++ [alu], maskAll)
        else if a.regs.contains rd then none
        else some ([movWI w rd rs] ++ pre ++ [alu], maskAll)
      | .imm cb =>
        if a.regs.contains rd then none
        else some ([moviI rd (cb.setWidth 64)] ++ pre ++ [alu], maskAll)
      | .vec _ => none

/-- Lower memory-operand binary ALU op into x64 directives. -/
def x64AluMem (n : Nat) (code : OpCode [.bits n, .bits n] [.bits n]) (memRhs : Bool)
    (a : AddrArg Reg64) (pb : PArg Reg64 RegMm CondCode (.bits n)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64AluMemIns n code memRhs a pb rd)

/-- Lower `jnz` on low byte at `[a]` (`cmpb $0, [a]; jcc cc l`). -/
def x64JnzMemIns (a : AddrArg Reg64) (inv : Bool) (l : Sym) :
    Option (List Instr × FlagMask) :=
  if !x64AddrValid a then none else
  let pre := (addrToExprIns a).1
  let addr := (addrToExprIns a).2.1
  let cc : CondCode := if inv then .z else .nz
  some (pre ++ [x64InsI .W8 (.cmp (.mem addr) (immBitsOp .W8 0#8)),
                x64InsI .W64 (.jcc cc l)], maskAll)

/-- Lower memory-operand `jnz` into x64 directives. -/
def x64JnzMem (a : AddrArg Reg64) (inv : Bool) (l : Sym) : Option (List Directive × FlagMask) :=
  emitCleanPair (x64JnzMemIns a inv l)

/-- Supported memory read-modify-write ALU kinds (`add`, `sub`, `and`, `or`, `xor`). -/
inductive RmwKind | add | sub | and | or | xor
  deriving DecidableEq

/-- Map `OpCode` to `RmwKind` for memory read-modify-write. -/
def x64RmwKind? : {n : Nat} → OpCode [.bits n, .bits n] [.bits n] → Option RmwKind
  | _, .add (.bits _) => some .add
  | _, .sub (.bits _) => some .sub
  | _, .and (.bits _) => some .and
  | _, .or  (.bits _) => some .or
  | _, .xor (.bits _) => some .xor
  | _, _ => none

/-- Memory-destination ALU instruction `[addr] := [addr] op src`. -/
def rmwMemI (w : Width) (k : RmwKind) (addr : AddrExpr) (src : Operand w) : Instr :=
  match k with
  | .add => x64InsI w (.add (.mem addr) src)
  | .sub => x64InsI w (.sub (.mem addr) src)
  | .and => x64InsI w (.and (.mem addr) src)
  | .or  => x64InsI w (.or  (.mem addr) src)
  | .xor => x64InsI w (.xor (.mem addr) src)

/-- Lower `[a] := code [a] pb` using `inc`/`dec` (for `±1`) or `add`/`sub`/`and`/`or`/`xor`. -/
def x64RmwMemIns (n : Nat) (code : OpCode [.bits n, .bits n] [.bits n])
    (a : AddrArg Reg64) (pb : PArg Reg64 RegMm CondCode (.bits n)) :
    Option (List Instr × FlagMask) :=
  if !x64AddrValid a then none else
  match x64RmwKind? code with
  | none => none
  | some k =>
    withWidth (F := fun m => PArg Reg64 RegMm CondCode (.bits m)) n pb fun w pb' =>
      let pre := (addrToExprIns a).1
      let addr := (addrToExprIns a).2.1
      match pb' with
      | .gpr ry => some (pre ++ [rmwMemI w k addr (.reg (regW w ry))], maskAll)
      | .imm cy =>
        if (k == .add && cy == 1#w.bits) || (k == .sub && cy == -1#w.bits) then
          some (pre ++ [x64InsI w (.inc (.mem addr))], maskDecInc)
        else if (k == .sub && cy == 1#w.bits) || (k == .add && cy == -1#w.bits) then
          some (pre ++ [x64InsI w (.dec (.mem addr))], maskDecInc)
        else if w != .W64 || fitsImm32 (cy.setWidth 64) then
          some (pre ++ [rmwMemI w k addr (immBitsOp w cy)], maskAll)
        else
          some (pre ++ [moviI .r11 (cy.setWidth 64),
                        rmwMemI w k addr (.reg (regW w .r11))], maskAll)
      | .vec _ => none

/-- Lower fused memory RMW into x64 directives. -/
def x64RmwMem (n : Nat) (code : OpCode [.bits n, .bits n] [.bits n])
    (a : AddrArg Reg64) (pb : PArg Reg64 RegMm CondCode (.bits n)) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64RmwMemIns n code a pb)

/-- Lower `rd := (base? + (idx <<< sc.shift) + disp)` via 3-op `leaq`/`leal` (`maskNone`),
guarding against `%rsp` as SIB index and `disp` outside signed 32-bit range. -/
def x64LeaArithIns (w : Nat) (base? : Option Reg64) (idx : Reg64) (sc : AddrScale)
    (disp : Int64) (rd : Reg64) : Option (List Instr × FlagMask) :=
  if !fitsImm32 disp.toBitVec then none
  else
    let mk (wd : Width) : Option (List Instr × FlagMask) :=
      match base? with
      | some rb =>
        if idx != .rsp then
          some ([x64InsI wd (.lea (regW wd rd) (atSIB rb idx sc disp))], maskNone)
        else if sc == .s1 && rb != .rsp then
          some ([x64InsI wd (.lea (regW wd rd) (atSIB idx rb .s1 disp))], maskNone)
        else none
      | none =>
        if idx != .rsp then
          some ([x64InsI wd (.lea (regW wd rd) (atIdx idx sc disp))], maskNone)
        else none
    match w with
    | 32 => mk .W32
    | 64 => mk .W64
    | _  => none

/-- Lower `rd := (base? + (idx <<< sc.shift) + disp)` into x64 directives. -/
def x64LeaArith (w : Nat) (base? : Option Reg64) (idx : Reg64) (sc : AddrScale)
    (disp : Int64) (rd : Reg64) : Option (List Directive × FlagMask) :=
  emitCleanPair (x64LeaArithIns w base? idx sc disp rd)

/-- `true` when `x64Op` writes `[.bits 32]` to `.gpr rd` with bits `32..63` guaranteed zero. -/
def x64ZeroUpper32Op : {sig rs : List Ty} → OpCode sig rs →
    Tup (PArg Reg64 RegMm CondCode) sig → Tup (PDst Reg64 RegMm CondCode) rs → Bool
  | _, _, .add (.bits 32), _, (.gpr _, ())
  | _, _, .sub (.bits 32), _, (.gpr _, ())
  | _, _, .mul (.bits 32), _, (.gpr _, ())
  | _, _, .and (.bits 32), _, (.gpr _, ())
  | _, _, .or (.bits 32), _, (.gpr _, ())
  | _, _, .xor (.bits 32), _, (.gpr _, ())
  | _, _, .neg (.bits 32), _, (.gpr _, ())
  | _, _, .not (.bits 32), _, (.gpr _, ())
  | _, _, .ofBool 32, _, (.gpr _, ())
  | _, _, .bswap (.bits 32), _, (.gpr _, ())
  | _, _, .clz 32, _, (.gpr _, ())
  | _, _, .cls 32, _, (.gpr _, ())
  | _, _, .ctz 32, _, (.gpr _, ())
  | _, _, .popcnt 32, _, (.gpr _, ())
  | _, _, .udiv 32, _, (.gpr _, ())
  | _, _, .sdiv 32, _, (.gpr _, ())
  | _, _, .urem 32, _, (.gpr _, ())
  | _, _, .srem 32, _, (.gpr _, ()) => true
  | _, _, .zext m 32, _, (.gpr _, ())
  | _, _, .sext m 32, _, (.gpr _, ()) => m == 8 || m == 16
  | _, _, .trunc m 32, (pa, ()), (.gpr rd, ()) =>
    m == 64 && match pa with
    | .imm _ => true
    | .gpr rs => rs != rd
    | _ => false
  | _, _, .shl (.bits 32), (_, pb, ()), (.gpr _, ())
  | _, _, .lshr (.bits 32), (_, pb, ()), (.gpr _, ())
  | _, _, .ashr (.bits 32), (_, pb, ()), (.gpr _, ())
  | _, _, .rotl (.bits 32), (_, pb, ()), (.gpr _, ())
  | _, _, .rotr (.bits 32), (_, pb, ()), (.gpr _, ()) =>
    match pb with
    | .imm cb => cb.toNat % 32 != 0
    | .gpr _ => true
    | _ => false
  | _, _, .fshl 32, (pa, _, pc, ()), (.gpr rd, ()) =>
    match pc with
    | .gpr _ => true
    | .imm cb =>
      cb.toNat % 32 != 0 ||
        match pa with | .imm _ => true | .gpr rs => rs != rd | _ => false
    | _ => false
  | _, _, .fshr 32, (_, pb, pc, ()), (.gpr rd, ()) =>
    match pc with
    | .gpr _ => true
    | .imm cb =>
      cb.toNat % 32 != 0 ||
        match pb with | .imm _ => true | .gpr rs => rs != rd | _ => false
    | _ => false
  | _, _, .select (.bits 32), (pc, pa, pb, ()), (.gpr rd, ()) =>
    match pc with
    | .imm b =>
      match if b then pa else pb with | .imm _ => true | .gpr rs => rs != rd | _ => false
    | .flag _ | .gpr _ =>
      match pa, pb with
      | .gpr ra, .gpr rb => !(ra == rb && ra == rd)
      | _, _ => true
    | _ => false
  | _, _, .copy (.bits 32), (pa, ()), (.gpr rd, ())
  | _, _, .bitcast (.bits 32) (.bits 32) _, (pa, ()), (.gpr rd, ()) =>
    match pa with
    | .imm _ => true
    | .gpr rs => rs != rd
    | _ => false
  | _, _, _, _, _ => false

/-- Polarity-aware GPR `jnz`: `testb %r, %r; jnz/jz sym`. -/
def x64JnzGpr (r : Reg64) (inv : Bool) (l : Sym) : List Directive × FlagMask :=
  (emitClean [x64InsI .W8 (.test (.reg (b8 r)) (.reg (b8 r))),
              x64InsI .W64 (.jcc (if inv then .z else .nz) l)], maskAll)

/-- Width at which `(r &&& mask) ==/!= 0` is equivalent to testing `SF` via `test %r, %r`:
matches width sign bits (`8`/`16`/`32`/`64`) and bit 31 (`0x80000000`) within `64`-bit GPRs. -/
def signTestWidth? (n : Nat) (mask : BitVec n) : Option Width :=
  withWidth (F := fun k => BitVec k) n mask fun w mask' =>
    if mask' == (1#w.bits <<< (w.bits - 1)) then some w
    else match w, mask' with
      | .W64, m => if m == 0x80000000#64 then some .W32 else none
      | _, _ => none

/-- Lower fused `(r &&& mask) ==/!= 0` sign-bit branch (`neg = true` -> `!= 0` -> `js`, `false` ->
`== 0` -> `jns`) via macro-fusable `test %r, %r; js/jns`. -/
def x64TestJccIns (neg : Bool) (n : Nat) (r : Reg64) (mask : BitVec n) (l : Sym) :
    Option (List Instr × FlagMask) :=
  (signTestWidth? n mask).map fun tw =>
    let cc : CondCode := if neg then .s else .ns
    ([x64InsI tw (.test (.reg (regW tw r)) (.reg (regW tw r))),
      x64InsI .W64 (.jcc cc l)], maskAll)

/-- Lower fused sign-bit branch `(r &&& mask) ==/!= 0` into x64 directives. -/
def x64TestJcc (neg : Bool) (n : Nat) (r : Reg64) (mask : BitVec n) (l : Sym) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64TestJccIns neg n r mask l)

/-- Condition code holding the `.bool` GPR result simultaneously in flags after `x64Op`. -/
def x64BoolFlagOut {sig : List Ty} (code : OpCode sig [.bool])
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option CondCode :=
  match pd with
  | .gpr _ =>
    match code with
    | .copy .bool => match pas with | (.flag cc, ()) => some cc | _ => none
    | .not  .bool => match pas with
      | (.flag cc, ()) => some (x64NegCond cc) | (.gpr _, ()) => some .nz | _ => none
    | .and .bool | .or .bool | .xor .bool =>
      match pas with
      | (pa, pb, ()) =>
        match pa, pb with
        | .imm _, .imm _ | .vec _, _ | _, .vec _ => none
        | _, _ => some .nz
    | _ => none
  | _ => none

/-- Operand order (`true` -> `lhs - rhs`, `false` -> `rhs - lhs`) whose compare flags survive
`opCmpIns`. -/
def x64CmpFlagsOut (co : CmpOp) (w : Nat)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w))
    (pd : PDst Reg64 RegMm CondCode .bool) : Option Bool :=
  if !x64BitWidths.contains w then none
  else match pd with
    | .gpr _ =>
      match pa, pb with
      | .imm _, .imm _ => none
      | .imm cx, .gpr _ =>
        some (!( !(w == 64) || fitsImm32 (cx.setWidth 64) ))
      | .gpr _, .gpr _ | .gpr _, .imm _ => some true
      | _, _ => none
    | .flag cc =>
      match pa, pb with
      | .imm cx, .gpr _ =>
        if cc == condOf co.swap && (!(w == 64) || fitsImm32 (cx.setWidth 64)) then some false
        else if cc == condOf co then some true
        else if cc == condOf co.swap then some false
        else none
      | .gpr _, .gpr _ | .gpr _, .imm _ | .imm _, .imm _ =>
        if cc == condOf co then some true
        else if cc == condOf co.swap then some false
        else none
      | _, _ => none
    | .vec _ => none

/-- ALU ops into `.gpr` that leave zero-comparison flags when `clob ≠ maskNone`
(`some true` = `==`/`!=` only, `some false` = full signed/unsigned vs `0`). -/
def x64AluZeroOut {sig : List Ty} (w : Nat) (code : OpCode sig [.bits w])
    (pd : PDst Reg64 RegMm CondCode (.bits w)) : Option Bool :=
  match pd with
  | .gpr _ =>
    match code with
    | .add (.bits _) | .sub (.bits _) | .neg (.bits _) => some true
    | .and (.bits _) | .or  (.bits _) | .xor (.bits _) => some false
    | _ => none
  | _ => none

/-- Operand order (`true` -> `[a] - pb`, `false` -> `pb - [a]`) of `x64CmpMem`. -/
def x64CmpMemFlagsOut (co : CmpOp) : PDst Reg64 RegMm CondCode .bool → Option Bool
  | .gpr _ => some true
  | .flag cc =>
    if cc == condOf co then some true
    else if cc == condOf co.swap then some false
    else none
  | .vec _ => none

/-- Typed x64 scalar `GprIsa` instance. -/
def x64Gpr : GprIsa Reg64 RegMm CondCode Directive where
  condReads := x64CondReads
  negCond := x64NegCond
  zeroFlags := [.c, .o]
  clearFlags := emitClean [x64InsI .W32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
  mov rd rs := emitClean [movI rd rs]
  movi rd c := emitClean [moviI rd c]
  setcc := setccOnly
  jmp l := emitClean [x64InsI .W64 (.jmp (.rel (.sub (.label l) .after_current_instruction)))]
  jcc cc l := emitClean [x64InsI .W64 (.jcc cc l)]
  jnzGpr r l := x64JnzGpr r false l
  op := x64Op
  load := x64Load
  store := x64Store
  supportsScalarOp := x64SupportsScalarOp
  cmpFlags := [.z, .nz, .l, .ge, .le, .g, .be, .a]
  zeroUpper32Load := true
  zeroExtLoad := true
  zeroUpper32Op := x64ZeroUpper32Op
  elideZext32 := true
  testOp := x64TestOp
  cmpMem := x64CmpMem
  testMem := x64TestMem
  loadSext := x64LoadSext
  testJcc := x64TestJcc
  aluMem := x64AluMem
  zeroUpper32AluMem := true
  jnzMem := x64JnzMem
  rmwMem := x64RmwMem
  leaArith := x64LeaArith
  zeroUpper32LeaArith := true
  jnzGprInv? := some x64JnzGpr
  condOfCmp? := some ∘ condOf
  boolFlagOut? := x64BoolFlagOut
  cmpFlagsOut? := x64CmpFlagsOut
  aluZeroOut? := x64AluZeroOut
  hasTestFlags := true
  cmpMemFlagsOut? := x64CmpMemFlagsOut
  moviDeadFlags? := some x64MoviDeadFlags

end LeanQbe.T.Amd64
