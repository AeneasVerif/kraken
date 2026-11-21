module

public import LeanQbe.T.Amd64.Base
public import LeanQbe.T.OpsLemmas

/-!
# Typed x64 Scalar Instruction Selection (`T8`)

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
    `umulw` (`.default` `mul`, `.mulxFast` `mulx`), `smulw` (`imul1`), `fshl`/`fshr` (`shld`/`shrd`).
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

/-- Width-indexed 64-bit-addressed directive wrapper. -/
def insW : (w : Width) → Operation w → Directive
  | .W8,  op => ins8 op
  | .W16, op => ins16 op
  | .W32, op => ins32 op
  | .W64, op => ins op

/-- `mov %rs, %rd` (64-bit). -/
def movD (rd rs : Reg64) : Directive :=
  ins (.mov (.reg (q rd)) (.reg (q rs)))

/-- `movl %rs32, %rd32` (zero-extends to 64 bits). -/
def movlD (rd rs : Reg64) : Directive :=
  ins32 (.mov (.reg (d rd)) (.reg (d rs)))

/-- `mov $c, %rd` (full 64-bit immediate, preserves all status flags). -/
def moviD (rd : Reg64) (c : BitVec 64) : Directive :=
  ins (.mov (.reg (q rd)) (.imm (.int64 (Int64.ofBitVec c))))

/-- Width-preserving register-to-register move (`movzbl`/`movzwl`/`movl`/`movq`). -/
def movW (w : Width) (rd rs : Reg64) : Directive :=
  match w with
  | .W8  => ins32 (.movzx (.reg (d rd)) (.reg (b8 rs)))
  | .W16 => ins32 (.movzx (.reg (d rd)) (.reg (h16 rs)))
  | .W32 => movlD rd rs
  | .W64 => movD rd rs

/-- Whether `c` fits in a sign-extended 32-bit immediate. -/
def fitsImm32 (c : BitVec 64) : Bool :=
  (c.truncate 32).signExtend 64 == c

/-- `Operand` encoding `c : BitVec w.bits` at width `w` (`w ≠ .W64` or `fitsImm32 c`). -/
def immBitsOp (w : Width) (c : BitVec w.bits) : Operand w :=
  .imm (.int64 (Int64.ofBitVec (c.signExtend 64)))

/-- Load a scalar `.bits w.bits` `PArg` into `rd` at width `w`, preserving status flags. -/
def argToBits (w : Width) (rd : Reg64) :
    PArg Reg64 RegMm CondCode (.bits w.bits) → Option Directive
  | .gpr rs => some (movW w rd rs)
  | .imm c  => some (moviD rd (c.setWidth 64))
  | .vec _  => none

/-- `setcc cc %rd_b; movzbl %rd_b, %rd_d` (preserves all status flags). -/
def setccMove (rd : Reg64) (cc : CondCode) : List Directive :=
  [ins8 (.setcc cc (.reg (b8 rd))), ins32 (.movzx (.reg (d rd)) (.reg (b8 rd)))]

/-- Materialize a `.bool` `PArg` into the low 8 bits of `rd` (`0#8` or `1#8`), preserving flags. -/
def boolArgTo8 (rd : Reg64) : PArg Reg64 RegMm CondCode .bool → Option Directive
  | .gpr rs  => some (ins8 (.mov (.reg (b8 rd)) (.reg (b8 rs))))
  | .imm b   => some (moviD rd (BitVec.ofNat 64 b.toNat))
  | .flag cc => some (ins8 (.setcc cc (.reg (b8 rd))))
  | .vec _   => none

/-- Lower `AddrArg Reg64` to prefix setup directives, a Kraken `AddrExpr`, and a flag mask.
Uses `.r10` if needed (leaving `.r11` free for store values). -/
def addrToExpr : AddrArg Reg64 → List Directive × AddrExpr × FlagMask
  | .baseDisp r off =>
    if off == 0 then ([], atReg r, maskNone)
    else if fitsImm32 off.toBitVec then ([], atDisp r off, maskNone)
    else ([moviD .r10 off.toBitVec, ins (.add (.reg (q .r10)) (.reg (q r)))],
          atReg .r10, maskAll)
  | .imm addr => ([moviD .r10 addr], atReg .r10, maskNone)

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
def aluBinIns (w : Width) (k : AluBinKind) (dst : Reg64) (src : Operand w) : Directive :=
  match k with
  | .add => insW w (.add (.reg (regW w dst)) src)
  | .sub => insW w (.sub (.reg (regW w dst)) src)
  | .and => insW w (.and (.reg (regW w dst)) src)
  | .or  => insW w (.or  (.reg (regW w dst)) src)
  | .xor => insW w (.xor (.reg (regW w dst)) src)
  | .mul =>
    match w, src with
    | .W8, .regOrMem (.reg r) => ins32 (.imul none (.reg (d dst)) (.reg (d r.base)))
    | .W8, .imm v => ins32 (.imul none (.reg (d dst)) (.imm v))
    | _, _ => insW w (.imul none (.reg (regW w dst)) src)

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

/-- Mask `ecx` to `0..7` or `0..15` for variable `8`/`16`-bit shifts (Kraken shifts mask by `0x1f`). -/
def shiftMaskRcx : Width → List Directive
  | .W8  => [ins32 (.and (.reg (d .rcx)) (.imm (.int64 7)))]
  | .W16 => [ins32 (.and (.reg (d .rcx)) (.imm (.int64 15)))]
  | _    => []

/-! ## 3. Individual scalar operation lowering (`op*`) -/

/-- Lower `.copy (.bits w.bits)` into `rd`. -/
def opCopyBits (w : Width) (pa : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  match pa with
  | .gpr rs => if rs == rd then some ([], maskNone) else some ([movW w rd rs], maskNone)
  | .imm c  => some ([moviD rd (c.setWidth 64)], maskNone)
  | .vec _  => none

/-- Lower `.copy .bool` into `pd`. -/
def opCopyBool (pa : PArg Reg64 RegMm CondCode .bool) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Directive × FlagMask) :=
  match pd with
  | .gpr rd =>
    match pa with
    | .gpr rs =>
      if rs == rd then some ([], maskNone)
      else some ([ins32 (.movzx (.reg (d rd)) (.reg (b8 rs)))], maskNone)
    | .imm b   => some ([moviD rd (BitVec.ofNat 64 b.toNat)], maskNone)
    | .flag cc => some (setccMove rd cc, maskNone)
    | .vec _   => none
  | _ => none

/-- Lower `.and`/`.or`/`.xor` on `.bool` into `pd`. -/
def opBoolBin (op : Bool → Bool → Bool) (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (pa pb : PArg Reg64 RegMm CondCode .bool) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Directive × FlagMask) :=
  match pd with
  | .gpr rd =>
    match pa, pb with
    | .imm a, .imm b => some ([moviD rd (BitVec.ofNat 64 (op a b).toNat)], maskNone)
    | _, _ => do
      let d1 ← boolArgTo8 .r11 pa
      let d2 ← boolArgTo8 .r10 pb
      some ([d1, d2, ins8 (insFn (.reg (b8 .r11)) (.reg (b8 .r10))),
             ins32 (.movzx (.reg (d rd)) (.reg (b8 .r11)))], maskAll)
  | _ => none

/-- Lower `.not .bool` into `pd`. -/
def opBoolNot (pa : PArg Reg64 RegMm CondCode .bool) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Directive × FlagMask) :=
  match pd with
  | .gpr rd =>
    match pa with
    | .imm b => some ([moviD rd (BitVec.ofNat 64 (!b).toNat)], maskNone)
    | _ => do
      let d1 ← boolArgTo8 .r11 pa
      some ([d1, ins8 (.xor (.reg (b8 .r11)) (.imm (.int64 1))),
             ins32 (.movzx (.reg (d rd)) (.reg (b8 .r11)))], maskAll)
  | _ => none

/-- Lower `.neg (.bits w.bits)` into `rd`. -/
def opNeg (w : Width) (pa : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  match pa with
  | .imm c  => some ([moviD rd ((-c).setWidth 64)], maskNone)
  | .gpr rs =>
    let pre := if rs == rd then [] else [movW w rd rs]
    some (pre ++ [insW w (.neg (.reg (regW w rd)))], maskAll)
  | .vec _  => none

/-- Lower `.not (.bits w.bits)` into `rd` (`not` leaves all status flags intact!). -/
def opNot (w : Width) (pa : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  match pa with
  | .imm c  => some ([moviD rd ((~~~c).setWidth 64)], maskNone)
  | .gpr rs =>
    let pre := if rs == rd then [] else [movW w rd rs]
    some (pre ++ [insW w (.not (.reg (regW w rd)))], maskNone)
  | .vec _  => none

/-- Lower binary ALU ops (`add`, `sub`, `and`, `or`, `xor`, `mul`) at `w`,
including `VariantHint.disp` (`lea`) and `VariantHint.decInc` (`inc`/`dec` preserving `CF`). -/
def opBin (w : Width) (k : AluBinKind)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) (vh : VariantHint) :
    Option (List Directive × FlagMask) :=
  let tryDisp : Option (List Directive × FlagMask) :=
    match vh with
    | .disp off =>
      if (w == .W32 || w == .W64) && fitsImm32 off.toBitVec then
        match k, pa, pb with
        | .add, .gpr rb, .imm cb =>
          if off.toBitVec.setWidth w.bits == cb then
            some ([insW w (.lea (regW w rd) (atDisp rb off))], maskNone)
          else none
        | .add, .imm ca, .gpr rb =>
          if off.toBitVec.setWidth w.bits == ca then
            some ([insW w (.lea (regW w rd) (atDisp rb off))], maskNone)
          else none
        | .sub, .gpr rb, .imm cb =>
          if (-off.toBitVec).setWidth w.bits == cb then
            some ([insW w (.lea (regW w rd) (atDisp rb off))], maskNone)
          else none
        | _, _, _ => none
      else none
    | _ => none
  let tryDecInc : Option (List Directive × FlagMask) :=
    match vh with
    | .decInc =>
      match k, pa, pb with
      | .sub, .gpr ra, .imm cb =>
        if cb == 1#w.bits then
          let pre := if ra == rd then [] else [movW w rd ra]
          some (pre ++ [insW w (.dec (.reg (regW w rd)))], maskDecInc)
        else if cb == -1#w.bits then
          let pre := if ra == rd then [] else [movW w rd ra]
          some (pre ++ [insW w (.inc (.reg (regW w rd)))], maskDecInc)
        else none
      | .add, .gpr ra, .imm cb =>
        if cb == 1#w.bits then
          let pre := if ra == rd then [] else [movW w rd ra]
          some (pre ++ [insW w (.inc (.reg (regW w rd)))], maskDecInc)
        else if cb == -1#w.bits then
          let pre := if ra == rd then [] else [movW w rd ra]
          some (pre ++ [insW w (.dec (.reg (regW w rd)))], maskDecInc)
        else none
      | .add, .imm ca, .gpr rb =>
        if ca == 1#w.bits then
          let pre := if rb == rd then [] else [movW w rd rb]
          some (pre ++ [insW w (.inc (.reg (regW w rd)))], maskDecInc)
        else none
      | _, _, _ => none
    | _ => none
  match tryDisp with
  | some res => some res
  | none =>
    match tryDecInc with
    | some res => some res
    | none =>
      let regImm (ra : Reg64) (cb : BitVec w.bits) : List Directive × FlagMask :=
        let pre := if ra == rd then [] else [movW w rd ra]
        if w != .W64 || fitsImm32 (cb.setWidth 64) then
          (pre ++ [aluBinIns w k rd (immBitsOp w cb)], maskAll)
        else
          ([moviD .r10 (cb.setWidth 64)] ++ pre ++ [aluBinIns w k rd (.reg (regW w .r10))], maskAll)
      match pa, pb with
      | .imm ca, .imm cb =>
        some ([moviD rd ((k.eval ca cb).setWidth 64)], maskNone)
      | .gpr ra, .gpr rb =>
        if ra == rd then some ([aluBinIns w k rd (.reg (regW w rb))], maskAll)
        else if k.isComm && rb == rd then some ([aluBinIns w k rd (.reg (regW w ra))], maskAll)
        else if k == .sub && rb == rd then
          some ([insW w (.neg (.reg (regW w rd))), aluBinIns w .add rd (.reg (regW w ra))], maskAll)
        else if rb != rd then
          some ([movW w rd ra, aluBinIns w k rd (.reg (regW w rb))], maskAll)
        else
          some ([movW w .r11 ra, aluBinIns w k .r11 (.reg (regW w rb)), movW w rd .r11], maskAll)
      | .gpr ra, .imm cb => some (regImm ra cb)
      | .imm ca, .gpr rb =>
        if k == .sub && ca == 0 then
          let pre := if rb == rd then [] else [movW w rd rb]
          some (pre ++ [insW w (.neg (.reg (regW w rd)))], maskAll)
        else if k.isComm then some (regImm rb ca)
        else
          some ([moviD .r11 (ca.setWidth 64), aluBinIns w .sub .r11 (.reg (regW w rb)),
                 movW w rd .r11], maskAll)
      | _, _ => none

/-- Lower `.shl`/`.lshr`/`.ashr`/`.rotl`/`.rotr` on `.bits w.bits` into `rd`.
For 32/64-bit, uses BMI2 flag-free `shlx`/`shrx`/`sarx` on variable shifts and `rorx` on
non-zero immediate rotates (`maskNone`); 8/16-bit and variable rotates use `%cl` / legacy ops. -/
def opShift (w : Width) (sk : ShiftKind)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  let isWide := w == .W32 || w == .W64
  match pb with
  | .imm cb =>
    let cnt := cb.toNat % w.bits
    if cnt == 0 then opCopyBits w pa rd
    else if isWide && sk.isRot then
      let rotCnt := if sk == .rotl then w.bits - cnt else cnt
      match pa with
      | .gpr ra =>
        some ([insW w (.rorx (regW w rd) (.reg (regW w ra)) (.int64 (Int64.ofNat rotCnt)))],
              maskNone)
      | .imm ca => some ([moviD rd ((sk.eval ca cnt).setWidth 64)], maskNone)
      | .vec _  => none
    else do
      let setup ←
        match pa with
        | .gpr ra => some (if ra == rd then [] else [movW w rd ra])
        | .imm ca => some [moviD rd (ca.setWidth 64)]
        | .vec _  => none
      let clob := if sk.isRot then maskCF ||| maskOF else maskAll
      some (setup ++ [insW w (sk.toOp (.reg (regW w rd)) (.imm8 (.int64 (Int64.ofNat cnt))))],
            clob)
  | .gpr rb =>
    if isWide && !sk.isRot then
      match sk.toBmi2Op?, pa with
      | some bmiOp, .gpr ra =>
        some ([insW w (bmiOp (regW w rd) (.reg (regW w ra)) (regW w rb))], maskNone)
      | some bmiOp, .imm ca =>
        some ([moviD .r11 (ca.setWidth 64),
               insW w (bmiOp (regW w rd) (.reg (regW w .r11)) (regW w rb))], maskNone)
      | _, _ => none
    else do
      let d1 ← argToBits w .r11 pa
      let mvRcx := if rb == .rcx then [] else [movW w .rcx rb]
      let mask := shiftMaskRcx w
      let sh := insW w (sk.toOp (.reg (regW w .r11)) .cl)
      let clob :=
        if w == .W8 || w == .W16 then maskAll else if sk.isRot then maskCF ||| maskOF else maskAll
      some ([d1, movD .r10 .rcx] ++ mvRcx ++ mask ++ [sh, movD .rcx .r10, movW w rd .r11], clob)
  | .vec _ => none

/-- Lower `.clz`/`.cls`/`.ctz`/`.popcnt` on `.bits w.bits` into `rd` across `{8, 16, 32, 64}`.
Constant-folds `.imm` inputs with `maskNone`; lowers `.gpr` inputs via `lzcnt`/`tzcnt`/`popcnt`
(zero/sign-extending `8`/`16`-bit operands to `32` bits and adjusting counts) with `maskAll`. -/
def opBitcnt (w : Width) (bk : BitcntKind)
    (pa : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  match pa with
  | .imm c => some ([moviD rd ((bk.eval w c).setWidth 64)], maskNone)
  | .vec _ => none
  | .gpr ra =>
    let insn := match w, bk with
      | .W32, .popcnt | .W64, .popcnt =>
        [insW w (.popcnt (regW w rd) (.reg (regW w ra)))]
      | .W8, .popcnt | .W16, .popcnt =>
        [movW w rd ra, ins32 (.popcnt (d rd) (.reg (d rd)))]
      | .W32, .clz | .W64, .clz =>
        [insW w (.lzcnt (regW w rd) (.reg (regW w ra)))]
      | .W8, .clz | .W16, .clz =>
        [movW w rd ra,
         ins32 (.lzcnt (d rd) (.reg (d rd))),
         aluBinIns .W32 .sub rd (immBitsOp .W32 (BitVec.ofNat 32 (32 - w.bits)))]
      | .W32, .ctz | .W64, .ctz =>
        [insW w (.tzcnt (regW w rd) (.reg (regW w ra)))]
      | .W8, .ctz | .W16, .ctz =>
        [movW w rd ra,
         aluBinIns .W32 .or rd (immBitsOp .W32 (BitVec.ofNat 32 (1 <<< w.bits))),
         ins32 (.tzcnt (d rd) (.reg (d rd)))]
      | .W32, .cls | .W64, .cls =>
        [movW w .r11 ra,
         insW w (.sar (.reg (regW w .r11)) (.imm8 (.int64 (Int64.ofNat (w.bits - 1))))),
         aluBinIns w .xor .r11 (.reg (regW w ra)),
         insW w (.lzcnt (regW w rd) (.reg (regW w .r11))),
         insW w (.dec (.reg (regW w rd)))]
      | .W8, .cls | .W16, .cls =>
        let movsx := match w with
          | .W8 => ins32 (.movsx (.reg (d rd)) (.reg (b8 ra)))
          | _   => ins32 (.movsx (.reg (d rd)) (.reg (h16 ra)))
        [movsx,
         movlD .r11 rd,
         ins32 (.sar (.reg (d .r11)) (.imm8 (.int64 31))),
         aluBinIns .W32 .xor rd (.reg (d .r11)),
         ins32 (.lzcnt (d rd) (.reg (d rd))),
         aluBinIns .W32 .sub rd (immBitsOp .W32 (BitVec.ofNat 32 (33 - w.bits)))]
    some (insn, maskAll)

/-- Lower `.udiv`/`.sdiv`/`.urem`/`.srem` on `.bits w.bits` into `rd`.
Widths `8`/`16` are zero/sign-extended to `32` bits and run through 32-bit `divl`/`idivl`. -/
def opDiv (w : Width) (isSigned isRem : Bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  if rd == .r10 || rd == .r11 then none
  else do
    let extTo (t : Reg64) : PArg Reg64 RegMm CondCode (.bits w.bits) → Option Directive
      | .gpr r =>
        match w with
        | .W8  => some (ins32 (if isSigned then .movsx (.reg (d t)) (.reg (b8 r))
                              else .movzx (.reg (d t)) (.reg (b8 r))))
        | .W16 => some (ins32 (if isSigned then .movsx (.reg (d t)) (.reg (h16 r))
                              else .movzx (.reg (d t)) (.reg (h16 r))))
        | .W32 => some (movlD t r)
        | .W64 => some (movD t r)
      | .imm c =>
        let c64 := if isSigned then c.signExtend 64 else c.setWidth 64
        some (moviD t c64)
      | .vec _ => none
    let da ← extTo .r10 pa
    let db ← extTo .r11 pb
    let core : List Directive :=
      match w with
      | .W64 =>
        if isSigned then
          [movD .rdx .rax, ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63))),
           ins (.idiv (.reg (q .r11)))]
        else
          [moviD .rdx 0, ins (.div (.reg (q .r11)))]
      | _ =>
        if isSigned then
          [movlD .rdx .rax, ins32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31))),
           ins32 (.idiv (.reg (d .r11)))]
        else
          [moviD .rdx 0, ins32 (.div (.reg (d .r11)))]
    let res : Reg64 := if isRem then .rdx else .rax
    let seq :=
      if rd == .rax then
        [da, db, movD .rax .r10, movD .r10 .rdx] ++ core ++ [movD .rax res, movD .rdx .r10]
      else if rd == .rdx then
        [da, db, movD .rdx .rax, movD .rax .r10, movD .r10 .rdx] ++ core ++
          [movD .rdx res, movD .rax .r10]
      else
        [da, db, movD rd .rax, movD .rax .r10, movD .r10 .rdx] ++ core ++
          [movD .r11 res, movD .rdx .r10, movD .rax rd, movD rd .r11]
    some (seq, maskAll)

/-- Emit `cmp` setting flags for `a - b` at width `w`. -/
def cmpDirect (w : Width) (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) :
    Option (List Directive) :=
  match pa, pb with
  | .gpr rx, .gpr ry => some [insW w (.cmp (.reg (regW w rx)) (.reg (regW w ry)))]
  | .gpr rx, .imm cy =>
    if w != .W64 || fitsImm32 (cy.setWidth 64) then
      some [insW w (.cmp (.reg (regW w rx)) (immBitsOp w cy))]
    else
      some [moviD .r10 (cy.setWidth 64), insW w (.cmp (.reg (regW w rx)) (.reg (regW w .r10)))]
  | .imm cx, .gpr ry =>
    some [moviD .r10 (cx.setWidth 64), insW w (.cmp (.reg (regW w .r10)) (.reg (regW w ry)))]
  | .imm cx, .imm cy =>
    some [moviD .r11 (cx.setWidth 64), moviD .r10 (cy.setWidth 64),
          insW w (.cmp (.reg (regW w .r11)) (.reg (regW w .r10)))]
  | _, _ => none

/-- Lower `.cmp co (.bits w.bits)` into either `.gpr rd` or `.flag cc`. -/
def opCmp (w : Width) (co : CmpOp)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pd : PDst Reg64 RegMm CondCode .bool) :
    Option (List Directive × FlagMask) :=
  match pd with
  | .gpr rd =>
    match pa, pb with
    | .imm cx, .imm cy =>
      some ([moviD rd (BitVec.ofNat 64 (co.evalBits cx cy).toNat)], maskNone)
    | .imm cx, .gpr ry =>
      if w != .W64 || fitsImm32 (cx.setWidth 64) then
        some ([insW w (.cmp (.reg (regW w ry)) (immBitsOp w cx))] ++
              setccMove rd (condOf co.swap), maskAll)
      else
        some ([moviD .r10 (cx.setWidth 64),
               insW w (.cmp (.reg (regW w .r10)) (.reg (regW w ry)))] ++
              setccMove rd (condOf co), maskAll)
    | _, _ => do
      let c ← cmpDirect w pa pb
      some (c ++ setccMove rd (condOf co), maskAll)
  | .flag cc =>
    match pa, pb with
    | .imm cx, .gpr ry =>
      if cc == condOf co.swap && (w != .W64 || fitsImm32 (cx.setWidth 64)) then
        some ([insW w (.cmp (.reg (regW w ry)) (immBitsOp w cx))], maskAll)
      else if cc == condOf co then
        some ([moviD .r10 (cx.setWidth 64),
               insW w (.cmp (.reg (regW w .r10)) (.reg (regW w ry)))], maskAll)
      else if cc == condOf co.swap then
        some ([moviD .r10 (cx.setWidth 64),
               insW w (.cmp (.reg (regW w ry)) (.reg (regW w .r10)))], maskAll)
      else none
    | _, _ =>
      if cc == condOf co then do
        let c ← cmpDirect w pa pb
        some (c, maskAll)
      else if cc == condOf co.swap then do
        let c ← cmpDirect w pb pa
        some (c, maskAll)
      else none
  | .vec _ => none

/-- Flag-driven conditional select (`rd := if cc then pa else pb`) preserving all status flags.
Emits `.W32` `cmovcc` for widths `8, 16, 32` and `.W64` `cmovcc` for `64`. -/
def selectFlagSeq (w : Width) (cc : CondCode)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) : Option (List Directive) :=
  let cw : Width := if w == .W64 then .W64 else .W32
  let cmov (cond : CondCode) (src : Reg64) : Directive :=
    insW cw (.cmovcc cond (regW cw rd) (.reg (regW cw src)))
  match pa, pb with
  | .gpr ra, .gpr rb =>
    if ra == rb then some (if ra == rd then [] else [movW cw rd ra])
    else if rd == rb then some [cmov cc ra]
    else if rd == ra then some [cmov (x64NegCond cc) rb]
    else some [movW cw rd rb, cmov cc ra]
  | .gpr ra, .imm cb =>
    if rd == ra then some [moviD .r10 (cb.setWidth 64), cmov (x64NegCond cc) .r10]
    else some [moviD rd (cb.setWidth 64), cmov cc ra]
  | .imm ca, .gpr rb =>
    if rd == rb then some [moviD .r10 (ca.setWidth 64), cmov cc .r10]
    else some [moviD rd (ca.setWidth 64), cmov (x64NegCond cc) rb]
  | .imm ca, .imm cb =>
    some [moviD rd (cb.setWidth 64), moviD .r10 (ca.setWidth 64), cmov cc .r10]
  | _, _ => none

/-- Lower `.select (.bits w.bits)` (`cmovcc`, never branching). -/
def opSelect (w : Width) (pc : PArg Reg64 RegMm CondCode .bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  match pc with
  | .imm b   => opCopyBits w (if b then pa else pb) rd
  | .flag cc => (selectFlagSeq w cc pa pb rd).map (·, maskNone)
  | .gpr rc  =>
    (selectFlagSeq w .nz pa pb rd).map fun seq =>
      (ins8 (.test (.reg (b8 rc)) (.reg (b8 rc))) :: seq, maskAll)
  | .vec _   => none

/-- Lower `.ofBool` (`n ∈ {8, 16, 32, 64}`) into `rd` (zero-extending from low 8 bits). -/
def opOfBool (pa : PArg Reg64 RegMm CondCode .bool) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  match pa with
  | .gpr rs  => some ([ins32 (.movzx (.reg (d rd)) (.reg (b8 rs)))], maskNone)
  | .imm b   => some ([moviD rd (BitVec.ofNat 64 b.toNat)], maskNone)
  | .flag cc => some (setccMove rd cc, maskNone)
  | .vec _   => none

/-- Lower `.zext m n` (`m < n`, `m, n ∈ {8, 16, 32, 64}`) into `rd`. -/
def opZext (m n : Nat) (pa : PArg Reg64 RegMm CondCode (.bits m)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  if !(x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n) then none
  else
    match pa with
    | .imm c => some ([moviD rd (c.setWidth 64)], maskNone)
    | .gpr r =>
      match m with
      | 8  => some ([ins32 (.movzx (.reg (d rd)) (.reg (b8 r)))], maskNone)
      | 16 => some ([ins32 (.movzx (.reg (d rd)) (.reg (h16 r)))], maskNone)
      | 32 => some ([movlD rd r], maskNone)
      | _  => none
    | .vec _ => none

/-- Lower `.sext m n` (`m < n`, `m, n ∈ {8, 16, 32, 64}`) into `rd`. -/
def opSext (m n : Nat) (pa : PArg Reg64 RegMm CondCode (.bits m)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  if !(x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n) then none
  else
    match pa with
    | .imm c => some ([moviD rd ((c.signExtend n).setWidth 64)], maskNone)
    | .gpr r =>
      match m, n with
      | 8,  64 => some ([ins (.movsx (.reg (q rd)) (.reg (b8 r)))], maskNone)
      | 8,  _  => some ([ins32 (.movsx (.reg (d rd)) (.reg (b8 r)))], maskNone)
      | 16, 64 => some ([ins (.movsx (.reg (q rd)) (.reg (h16 r)))], maskNone)
      | 16, _  => some ([ins32 (.movsx (.reg (d rd)) (.reg (h16 r)))], maskNone)
      | 32, 64 => some ([ins (.movsx (.reg (q rd)) (.reg (d r)))], maskNone)
      | _,  _  => none
    | .vec _ => none

/-- Lower `.trunc m n` (`n < m`, `m, n ∈ {8, 16, 32, 64}`) into `rd`. -/
def opTrunc (m n : Nat) (pa : PArg Reg64 RegMm CondCode (.bits m)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  if !(x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (n + 1) m) then none
  else
    let res := fun (w : Width) =>
      match pa with
      | .imm c => some ([moviD rd ((c.setWidth n).setWidth 64)], maskNone)
      | .gpr r => if r == rd then some ([], maskNone) else some ([movW w rd r], maskNone)
      | .vec _ => none
    match n with
    | 8  => res .W8
    | 16 => res .W16
    | 32 => res .W32
    | _  => none

/-- Lower `.bswap (.bits n)` (`n ∈ {16, 32, 64}`) into `rd`. -/
def opBswap (n : Nat) (pa : PArg Reg64 RegMm CondCode (.bits n)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  match n, pa with
  | 16, .imm c => some ([moviD rd ((bswapBits c).setWidth 64)], maskNone)
  | 16, .gpr r =>
    let pre := if r == rd then [] else [movW .W16 rd r]
    some (pre ++ [ins16 (.rol (.reg (h16 rd)) (.imm8 (.int64 8)))], maskCF ||| maskOF)
  | 32, .imm c => some ([moviD rd ((bswapBits c).setWidth 64)], maskNone)
  | 32, .gpr r =>
    let pre := if r == rd then [] else [movlD rd r]
    some (pre ++ [ins32 (.bswap (d rd))], maskNone)
  | 64, .imm c => some ([moviD rd (bswapBits c)], maskNone)
  | 64, .gpr r =>
    let pre := if r == rd then [] else [movD rd r]
    some (pre ++ [ins (.bswap (q rd))], maskNone)
  | _, _ => none

/-- Two-address carry/borrow core preserving `CF` (or `OF`) before the operation runs. -/
def carryCore (w : Width) (isComm : Bool)
    (mkReg : Reg64 → Reg64 → Directive) (mkImm : Reg64 → BitVec w.bits → Directive)
    (supportsImm : Bool) (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive) :=
  let regImm (ra : Reg64) (cb : BitVec w.bits) : List Directive :=
    let pre := if ra == rd then [] else [movW w rd ra]
    if supportsImm && (w != .W64 || fitsImm32 (cb.setWidth 64)) then
      pre ++ [mkImm rd cb]
    else
      [moviD .r10 (cb.setWidth 64)] ++ pre ++ [mkReg rd .r10]
  match pa, pb with
  | .gpr ra, .gpr rb =>
    if ra == rd then some [mkReg rd rb]
    else if isComm && rb == rd then some [mkReg rd ra]
    else if rb != rd then some [movW w rd ra, mkReg rd rb]
    else some [movW w .r11 ra, mkReg .r11 rb, movW w rd .r11]
  | .gpr ra, .imm cb => some (regImm ra cb)
  | .imm ca, .gpr rb =>
    if isComm then some (regImm rb ca)
    else some [moviD .r11 (ca.setWidth 64), mkReg .r11 rb, movW w rd .r11]
  | .imm ca, .imm cb =>
    some (moviD rd (ca.setWidth 64) :: regImm rd cb)
  | _, _ => none

/-- Lower `.addc w.bits` (`w ∈ {.W32, .W64}`), supporting `.default` (`adc`), `.adcx`, `.adox`. -/
def opAddc (w : Width)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pc : PArg Reg64 RegMm CondCode .bool)
    (dsum : PDst Reg64 RegMm CondCode (.bits w.bits)) (dc : PDst Reg64 RegMm CondCode .bool)
    (vh : VariantHint) : Option (List Directive × FlagMask) :=
  match dsum with
  | .gpr rd =>
    let distinctDst : Bool := match dc with | .gpr rc => rc != rd | _ => true
    if !distinctDst then none
    else
      let coutSeq (flagCc : CondCode) : Option (List Directive) :=
        match dc with
        | .flag cc => if cc == flagCc then some [] else none
        | .gpr rc  => some (setccMove rc flagCc)
        | .vec _   => none
      let adcFallback : Option (List Directive × FlagMask) := do
        let setupCf ←
          match pc with
          | .flag .c   => some []
          | .flag cc   => some [ins8 (.setcc cc (.reg (b8 .r10))), ins8 (.neg (.reg (b8 .r10)))]
          | .gpr rc    => some [ins8 (.mov (.reg (b8 .r10)) (.reg (b8 rc))),
                                ins8 (.neg (.reg (b8 .r10)))]
          | .imm false => some [ins32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
          | .imm true  => some [moviD .r10 1, ins8 (.neg (.reg (b8 .r10)))]
          | .vec _     => none
        let core ← carryCore w true
          (fun dst src => insW w (.adc (.reg (regW w dst)) (.reg (regW w src))))
          (fun dst imm => insW w (.adc (.reg (regW w dst)) (immBitsOp w imm)))
          true pa pb rd
        let tail ← coutSeq .c
        some (setupCf ++ core ++ tail, maskAll)
      match vh with
      | .adcx =>
        match pc with
        | .flag .c => do
          let core ← carryCore w true
            (fun dst src => insW w (.adcx (regW w dst) (.reg (regW w src))))
            (fun dst _ => insW w (.adcx (regW w dst) (.reg (regW w dst))))
            false pa pb rd
          let tail ← coutSeq .c
          some (core ++ tail, maskCF)
        | _ => adcFallback
      | .adox =>
        match pc with
        | .flag .o => do
          let core ← carryCore w true
            (fun dst src => insW w (.adox (regW w dst) (.reg (regW w src))))
            (fun dst _ => insW w (.adox (regW w dst) (.reg (regW w dst))))
            false pa pb rd
          let tail ← coutSeq .o
          some (core ++ tail, maskOF)
        | _ => adcFallback
      | _ => adcFallback
  | .vec _ => none

/-- Lower `.subb w.bits` (`w ∈ {.W32, .W64}`) via `sbb`. -/
def opSubb (w : Width)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pc : PArg Reg64 RegMm CondCode .bool)
    (ddiff : PDst Reg64 RegMm CondCode (.bits w.bits)) (db : PDst Reg64 RegMm CondCode .bool) :
    Option (List Directive × FlagMask) :=
  match ddiff with
  | .gpr rd =>
    let distinctDst : Bool := match db with | .gpr rb => rb != rd | _ => true
    if !distinctDst then none
    else do
      let setupCf ←
        match pc with
        | .flag .c   => some []
        | .flag cc   => some [ins8 (.setcc cc (.reg (b8 .r10))), ins8 (.neg (.reg (b8 .r10)))]
        | .gpr rc    => some [ins8 (.mov (.reg (b8 .r10)) (.reg (b8 rc))),
                              ins8 (.neg (.reg (b8 .r10)))]
        | .imm false => some [ins32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
        | .imm true  => some [moviD .r10 1, ins8 (.neg (.reg (b8 .r10)))]
        | .vec _     => none
      let core ← carryCore w false
        (fun dst src => insW w (.sbb (.reg (regW w dst)) (.reg (regW w src))))
        (fun dst imm => insW w (.sbb (.reg (regW w dst)) (immBitsOp w imm)))
        true pa pb rd
      let tail ←
        match db with
        | .flag .c => some []
        | .flag _  => none
        | .gpr rb  => some (setccMove rb .c)
        | .vec _   => none
      some (setupCf ++ core ++ tail, maskAll)
  | .vec _ => none

/-- Lower `.umulw w.bits` / `.smulw w.bits` (`w ∈ {.W32, .W64}`), supporting `.mulxFast`. -/
def opMulw (w : Width) (isSigned : Bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits))
    (dlo dhi : PDst Reg64 RegMm CondCode (.bits w.bits)) (vh : VariantHint) :
    Option (List Directive × FlagMask) :=
  match dlo, dhi with
  | .gpr rlo, .gpr rhi =>
    if rlo == rhi then none
    else if !isSigned && vh == .mulxFast then do
      let da ← argToBits w .r11 pa
      let saveRdx := if rlo == .rdx || rhi == .rdx then [] else [movD .r10 .rdx]
      let loadB ←
        match pb with
        | .gpr .rdx => some []
        | _ => do let db ← argToBits w .rdx pb; some [db]
      let mulxDir := insW w (.mulx (regW w rhi) (regW w rlo) (.reg (regW w .r11)))
      let restRdx := if rlo == .rdx || rhi == .rdx then [] else [movD .rdx .r10]
      some ([da] ++ saveRdx ++ loadB ++ [mulxDir] ++ restRdx, maskNone)
    else do
      let da ← argToBits w .r10 pa
      let db ← argToBits w .r11 pb
      let mulDir := insW w (if isSigned then .imul1 (.reg (regW w .r11))
                                        else .mul (.reg (regW w .r11)))
      let seq :=
        if rlo == .rax && rhi == .rdx then
          [da, db, movD .rax .r10, mulDir]
        else if rlo == .rdx && rhi == .rax then
          [da, db, movD .rax .r10, mulDir, movD .r10 .rax, movD .rax .rdx, movD .rdx .r10]
        else if rlo == .rax then
          [da, db, movD .rax .r10, movD .r10 .rdx, mulDir, movD rhi .rdx, movD .rdx .r10]
        else if rhi == .rdx then
          [da, db, movD rlo .rax, movD .rax .r10, mulDir,
           movD .r10 rlo, movD rlo .rax, movD .rax .r10]
        else if rlo == .rdx then
          [da, db, movD rhi .rax, movD .rax .r10, mulDir,
           movD .r10 rhi, movD rhi .rdx, movD .rdx .rax, movD .rax .r10]
        else if rhi == .rax then
          [da, db, movD rlo .rdx, movD .rax .r10, mulDir,
           movD .r10 rlo, movD rlo .rax, movD .rax .rdx, movD .rdx .r10]
        else
          [da, db, movD rlo .rax, movD rhi .rdx, movD .rax .r10, mulDir,
           movD .r10 rlo, movD rlo .rax, movD .rax .r10,
           movD .r10 rhi, movD rhi .rdx, movD .rdx .r10]
      some (seq, maskAll)
  | _, _ => none

/-- Lower `.fshl w.bits` / `.fshr w.bits` (`w ∈ {.W32, .W64}`) via `shld`/`shrd`.
Note `shld dst src` computes high bits of `(dst ++ src) <<< c`; `shrd dst src` computes low
bits of `(src ++ dst) >>> c`, so `fshr` passes `dst := lo`, `src := hi`. -/
def opFunnel (w : Width) (isRight : Bool)
    (pa pb pc : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    Option (List Directive × FlagMask) :=
  let dstArg := if isRight then pb else pa
  let srcArg := if isRight then pa else pb
  let mkShift (cnt : ShiftCountExpr) : Directive :=
    insW w (if isRight then .shrd (.reg (regW w .r11)) (regW w .r10) cnt
                       else .shld (.reg (regW w .r11)) (regW w .r10) cnt)
  match pc with
  | .imm c =>
    let cnt := c.toNat % w.bits
    if cnt == 0 then opCopyBits w dstArg rd
    else do
      let dDst ← argToBits w .r11 dstArg
      let dSrc ← argToBits w .r10 srcArg
      some ([dDst, dSrc, mkShift (.imm8 (.int64 (Int64.ofNat cnt))), movW w rd .r11], maskAll)
  | .gpr rc => do
    let dDst ← argToBits w .r11 dstArg
    let dSrc ← argToBits w .r10 srcArg
    let sh := mkShift .cl
    if rd == .rcx then
      let mvRcx := if rc == .rcx then [] else [movD .rcx rc]
      some ([dDst, dSrc] ++ mvRcx ++ [sh, movW w .rcx .r11], maskAll)
    else if rc == rd then
      some ([dDst, dSrc,
             ins (.xor (.reg (q .rcx)) (.reg (q rd))),
             ins (.xor (.reg (q rd)) (.reg (q .rcx))),
             ins (.xor (.reg (q .rcx)) (.reg (q rd))),
             sh, movD .rcx rd, movW w rd .r11], maskAll)
    else
      let mvRcx := if rc == .rcx then [] else [movD .rcx rc]
      some ([dDst, dSrc, movD rd .rcx] ++ mvRcx ++ [sh, movD .rcx rd, movW w rd .r11], maskAll)
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

/-- Lower a scalar `OpCode` into x64 directives and its flag clobber mask. -/
def x64Op : {sig rs : List Ty} → OpCode sig rs → Tup (PArg Reg64 RegMm CondCode) sig →
    Tup (PDst Reg64 RegMm CondCode) rs → VariantHint → Option (List Directive × FlagMask)
  | _, _, .copy (.bits n), (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opCopyBits w pa' rd
  | _, _, .copy .bool, (pa, ()), (pd, ()), _ => opCopyBool pa pd
  | _, _, .add (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBin w .add pa' pb' rd vh
  | _, _, .sub (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBin w .sub pa' pb' rd vh
  | _, _, .mul (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBin w .mul pa' pb' rd vh
  | _, _, .and (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBin w .and pa' pb' rd vh
  | _, _, .or (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBin w .or pa' pb' rd vh
  | _, _, .xor (.bits n), (pa, pb, ()), (.gpr rd, ()), vh =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opBin w .xor pa' pb' rd vh
  | _, _, .neg (.bits n), (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opNeg w pa' rd
  | _, _, .not (.bits n), (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opNot w pa' rd
  | _, _, .and .bool, (pa, pb, ()), (pd, ()), _ => opBoolBin (· && ·) .and pa pb pd
  | _, _, .or  .bool, (pa, pb, ()), (pd, ()), _ => opBoolBin (· || ·) .or  pa pb pd
  | _, _, .xor .bool, (pa, pb, ()), (pd, ()), _ => opBoolBin (· ^^ ·) .xor pa pb pd
  | _, _, .not .bool, (pa, ()), (pd, ()), _ => opBoolNot pa pd
  | _, _, .shl  (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShift w .shl pa' pb' rd
  | _, _, .lshr (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShift w .lshr pa' pb' rd
  | _, _, .ashr (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShift w .ashr pa' pb' rd
  | _, _, .rotl (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShift w .rotl pa' pb' rd
  | _, _, .rotr (.bits n), (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opShift w .rotr pa' pb' rd
  | _, _, .fshl n, (pa, pb, pc, ()), (.gpr rd, ()), _ =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb, pc)
      fun w (pa', pb', pc') => opFunnel w false pa' pb' pc' rd
  | _, _, .fshr n, (pa, pb, pc, ()), (.gpr rd, ()), _ =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb, pc)
      fun w (pa', pb', pc') => opFunnel w true pa' pb' pc' rd
  | _, _, .bswap (.bits n), (pa, ()), (.gpr rd, ()), _ => opBswap n pa rd
  | _, _, .clz n, (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opBitcnt w .clz pa' rd
  | _, _, .cls n, (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opBitcnt w .cls pa' rd
  | _, _, .ctz n, (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opBitcnt w .ctz pa' rd
  | _, _, .popcnt n, (pa, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      opBitcnt w .popcnt pa' rd
  | _, _, .cmp co (.bits n) _ h, (pa, pb, ()), (pd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') =>
        opCmp w co pa' pb' (cast (congrArg (PDst Reg64 RegMm CondCode) h) pd)
  | _, _, .select (.bits n), (pc, pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opSelect w pc pa' pb' rd
  | _, _, .zext m n, (pa, ()), (.gpr rd, ()), _ => opZext m n pa rd
  | _, _, .sext m n, (pa, ()), (.gpr rd, ()), _ => opSext m n pa rd
  | _, _, .trunc m n, (pa, ()), (.gpr rd, ()), _ => opTrunc m n pa rd
  | _, _, .ofBool n, (pa, ()), (.gpr rd, ()), _ =>
    if x64BitWidths.contains n then opOfBool pa rd else none
  | _, _, .addc n, (pa, pb, pc, ()), (dsum, dc, ()), vh =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k)) n (pa, pb, dsum)
      fun w (pa', pb', dsum') => opAddc w pa' pb' pc dsum' dc vh
  | _, _, .subb n, (pa, pb, pc, ()), (ddiff, db, ()), _ =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k)) n (pa, pb, ddiff)
      fun w (pa', pb', ddiff') => opSubb w pa' pb' pc ddiff' db
  | _, _, .umulw n, (pa, pb, ()), (dlo, dhi, ()), vh =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k)) n (pa, pb, dlo, dhi)
      fun w (pa', pb', dlo', dhi') => opMulw w false pa' pb' dlo' dhi' vh
  | _, _, .smulw n, (pa, pb, ()), (dlo, dhi, ()), vh =>
    withWideWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                                PArg Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k) ×
                                PDst Reg64 RegMm CondCode (.bits k)) n (pa, pb, dlo, dhi)
      fun w (pa', pb', dlo', dhi') => opMulw w true pa' pb' dlo' dhi' vh
  | _, _, .udiv n, (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opDiv w false false pa' pb' rd
  | _, _, .sdiv n, (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opDiv w true false pa' pb' rd
  | _, _, .urem n, (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opDiv w false true pa' pb' rd
  | _, _, .srem n, (pa, pb, ()), (.gpr rd, ()), _ =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k) ×
                            PArg Reg64 RegMm CondCode (.bits k)) n (pa, pb)
      fun w (pa', pb') => opDiv w true true pa' pb' rd
  | _, _, .bitcast (.bits m) (.bits n) _, (pa, ()), (.gpr rd, ()), _ =>
    if x64BitWidths.contains n then
      withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) m pa fun w pa' =>
        opCopyBits w pa' rd
    else none
  | _, _, _, _, _, _ => none

/-- Lower a scalar memory load of type `t` into `rd`. -/
def x64Load (t : Ty) (rd : Reg64) (a : AddrArg Reg64) : Option (List Directive × FlagMask) :=
  let (pre, addr, clob) := addrToExpr a
  match t with
  | .bool | .bits 8 =>
    some (pre ++ [ins32 (.movzx (.reg (d rd)) (.mem addr : RegOrMem .W8))], clob)
  | .bits 16 =>
    some (pre ++ [ins32 (.movzx (.reg (d rd)) (.mem addr : RegOrMem .W16))], clob)
  | .bits 32 =>
    some (pre ++ [ins32 (.mov (.reg (d rd)) (.mem addr))], clob)
  | .bits 64 =>
    some (pre ++ [ins (.mov (.reg (q rd)) (.mem addr))], clob)
  | _ => none

/-- Lower a scalar memory store of type `t`. -/
def x64Store : (t : Ty) → PArg Reg64 RegMm CondCode t → AddrArg Reg64 →
    Option (List Directive × FlagMask)
  | .bool, pa, a =>
    let (pre, addr, clob) := addrToExpr a
    match pa with
    | .gpr r => some (pre ++ [ins8 (.mov (.mem addr) (.reg (b8 r)))], clob)
    | .imm b => some (pre ++ [ins8 (.mov (.mem addr) (.imm (.int64 (Int64.ofNat b.toNat))))], clob)
    | .flag cc =>
      some (ins8 (.setcc cc (.reg (b8 .r11))) ::
            pre ++ [ins8 (.mov (.mem addr) (.reg (b8 .r11)))], clob)
    | .vec _ => none
  | .bits n, pa, a =>
    withWidth (F := fun k => PArg Reg64 RegMm CondCode (.bits k)) n pa fun w pa' =>
      let (pre, addr, clob) := addrToExpr a
      match pa' with
      | .gpr r => some (pre ++ [insW w (.mov (.mem addr) (.reg (regW w r)))], clob)
      | .imm c =>
        if w != .W64 || fitsImm32 (c.setWidth 64) then
          some (pre ++ [insW w (.mov (.mem addr) (immBitsOp w c))], clob)
        else
          some (pre ++ [moviD .r11 (c.setWidth 64),
                        ins (.mov (.mem addr) (.reg (q .r11)))], clob)
      | .vec _ => none
  | _, _, _ => none

/-- Typed x64 scalar `GprIsa` instance (`T8`). -/
def x64Gpr : GprIsa Reg64 RegMm CondCode Directive where
  condReads := x64CondReads
  negCond := x64NegCond
  zeroFlags := [.c, .o]
  clearFlags := [ins32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
  mov rd rs := [movD rd rs]
  movi rd c := [moviD rd c]
  setcc := setccMove
  jmp l := [ins (.jmp (.rel (.sub (.label l) .after_current_instruction)))]
  jcc cc l := [ins (.jcc cc l)]
  jnzGpr r l := ([ins8 (.test (.reg (b8 r)) (.reg (b8 r))), ins (.jcc .nz l)], maskAll)
  op := x64Op
  load := x64Load
  store := x64Store
  supportsScalarOp := x64SupportsScalarOp
  cmpFlags := [.z, .nz, .l, .ge, .le, .g, .be, .a]

end LeanQbe.T.Amd64
