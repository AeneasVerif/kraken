module

public import LeanQbe.T.Arm64.IselCore
public import LeanQbe.T.Arm64.IselScr

/-!
# AArch64 Scalar Instruction Selection (`GprIsa`)

Wires `LeanQbe.T.Arm64.armGpr : GprIsa Reg Empty ArmCond Directive` over helpers in
`LeanQbe.T.Arm64.IselCore` and `LeanQbe.T.Arm64.IselScr`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-- Scalar `OpCode` lowering for AArch64 (`Instr` builder). -/
def armOpIns {sig rs : List Ty} (code : OpCode sig rs) (pas : Tup (PArg Reg Empty ArmCond) sig)
    (dsts : Tup (PDst Reg Empty ArmCond) rs) (vh : VariantHint) : Option (List Instr × FlagMask) :=
  match sig, rs, code, pas, dsts with
  | _, _, .copy .bool, (pa, ()), (.gpr (.reg d), ()) => armBoolOpIns (.copy .bool) (pa, ()) d
  | _, _, .and .bool, (pa, pb, ()), (.gpr (.reg d), ()) =>
    armBoolOpIns (.and .bool) (pa, pb, ()) d
  | _, _, .or .bool, (pa, pb, ()), (.gpr (.reg d), ()) =>
    armBoolOpIns (.or .bool) (pa, pb, ()) d
  | _, _, .xor .bool, (pa, pb, ()), (.gpr (.reg d), ()) =>
    armBoolOpIns (.xor .bool) (pa, pb, ()) d
  | _, _, .not .bool, (pa, ()), (.gpr (.reg d), ()) => armBoolOpIns (.not .bool) (pa, ()) d
  | _, _, .copy (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if [8, 16, 32, 64].contains n then armCopyBitsIns n pa d else none
  | _, _, .bitcast (.bits m) (.bits n) _, (pa, ()), (.gpr (.reg d), ()) =>
    if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n then
      armCopyBitsIns m pa d
    else none
  | _, _, .zext m n, (pa, ()), (.gpr (.reg d), ()) => armZextOpIns m n pa d
  | _, _, .sext m n, (pa, ()), (.gpr (.reg d), ()) => armSextOpIns m n pa d
  | _, _, .trunc m n, (pa, ()), (.gpr (.reg d), ()) => armTruncOpIns m n pa d
  | _, _, .ofBool n, (pa, ()), (.gpr (.reg d), ()) => armOfBoolOpIns n pa d
  | _, _, .add (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .add n pa pb d
  | _, _, .sub (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .sub n pa pb d
  | _, _, .mul (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .mul n pa pb d
  | _, _, .and (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .and n pa pb d
  | _, _, .or (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .or n pa pb d
  | _, _, .xor (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .xor n pa pb d
  | _, _, .neg (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if ![8, 16, 32, 64].contains n then none
    else match pa with
      | .imm c => some (armMovImmI d ((-c).setWidth 64), maskNone)
      | .gpr (.reg r) =>
        let w := armWidthOf n
        some ([armIselInsI (.SUB_s (zr d w) (xzr w) (sh r))], maskNone)
      | .gpr .SP => none
  | _, _, .not (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if ![8, 16, 32, 64].contains n then none
    else match pa with
      | .imm c => some (armMovImmI d ((~~~c).setWidth 64), maskNone)
      | .gpr (.reg r) =>
        let w := armWidthOf n
        some ([armIselInsI (.ORN_s (zr d w) (xzr w) (sh r))], maskNone)
      | .gpr .SP => none
  | _, _, .shl (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOpIns .shl n pa pb d
  | _, _, .lshr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOpIns .lshr n pa pb d
  | _, _, .ashr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOpIns .ashr n pa pb d
  | _, _, .rotl (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armRotOpIns true n pa pb d
  | _, _, .rotr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armRotOpIns false n pa pb d
  | _, _, .udiv n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .udiv n pa pb d
  | _, _, .udiv0 n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .udiv n pa pb d
  | _, _, .sdiv n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .sdiv n pa pb d
  | _, _, .sdiv0 n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .sdiv n pa pb d
  | _, _, .urem n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .urem n pa pb d
  | _, _, .srem n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .srem n pa pb d
  | _, _, .bswap (.bits n), (pa, ()), (.gpr (.reg d), ()) => do
    if ![16, 32, 64].contains n then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let dir := if n == 16 then armIselInsI (.REV16 (zr d .W32) (zr ra .W32))
                 else if n == 32 then armIselInsI (.REV (zr d .W32) (zr ra .W32))
                 else armIselInsI (.REV (zr d .W64) (zr ra .W64))
      some (ca ++ [dir], maskNone)
  | _, _, .clz n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let w := armWidthOf n
      some (ca ++ [armIselInsI (.CLZ (zr d w) (zr ra w))], maskNone)
  | _, _, .cls n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let w := armWidthOf n
      some (ca ++ [armIselInsI (.CLS (zr d w) (zr ra w))], maskNone)
  | _, _, .rbit n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let w := armWidthOf n
      some (ca ++ [armIselInsI (.RBIT (zr d w) (zr ra w))], maskNone)
  | _, _, .ctz n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let w := armWidthOf n
      some (ca ++ [armIselInsI (.RBIT (zr d w) (zr ra w)),
        armIselInsI (.CLZ (zr d w) (zr d w))], maskNone)
  | _, _, .cmp o (.bits n) _ rfl, (pa, pb, ()), (dst, ()) => armCmpOpIns o n pa pb dst
  | _, _, .select (.bits n), (pc, pa, pb, ()), (.gpr (.reg d), ()) =>
    armSelectOpIns n pc pa pb d
  | _, _, .addc n, (pa, pb, cin, ()), (.gpr (.reg d), cout, ()) =>
    armAddcOpIns n pa pb cin d cout vh
  | _, _, .subb n, (pa, pb, bin, ()), (.gpr (.reg d), bout, ()) =>
    armSubbOpIns n pa pb bin d bout vh
  | _, _, .umulw n, (pa, pb, ()), (.gpr (.reg dlo), .gpr (.reg dhi), ()) =>
    armMulwOpIns false n pa pb dlo dhi
  | _, _, .smulw n, (pa, pb, ()), (.gpr (.reg dlo), .gpr (.reg dhi), ()) =>
    armMulwOpIns true n pa pb dlo dhi
  | _, _, .fshl n, (pa, pb, pc, ()), (.gpr (.reg d), ()) => armFunnelOpIns true n pa pb pc d
  | _, _, .fshr n, (pa, pb, pc, ()), (.gpr (.reg d), ()) => armFunnelOpIns false n pa pb pc d
  | _, _, _, _, _ => none

/-- Scalar `OpCode` lowering for AArch64. -/
def armOp {sig rs : List Ty} (code : OpCode sig rs) (pas : Tup (PArg Reg Empty ArmCond) sig)
    (dsts : Tup (PDst Reg Empty ArmCond) rs) (vh : VariantHint) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armOpIns code pas dsts vh)

/-- Computable `rfl`-safe scalar opcode support gate for AArch64 (`GprIsa.supportsScalarOp`). -/
def armSupportsScalarOp {sig rs : List Ty} (code : OpCode sig rs)
    (_args : Tup (Arg (fun _ => Unit)) sig) : Bool :=
  match sig, rs, code with
  | _, _, .copy (.bits n) | _, _, .add (.bits n) | _, _, .sub (.bits n) | _, _, .mul (.bits n)
  | _, _, .neg (.bits n) | _, _, .and (.bits n) | _, _, .or (.bits n) | _, _, .xor (.bits n)
  | _, _, .not (.bits n) | _, _, .shl (.bits n) | _, _, .lshr (.bits n) | _, _, .ashr (.bits n)
  | _, _, .rotl (.bits n) | _, _, .rotr (.bits n) | _, _, .ofBool n
  | _, _, .udiv n | _, _, .sdiv n | _, _, .urem n | _, _, .srem n
  | _, _, .udiv0 n | _, _, .sdiv0 n | _, _, .cmp _ (.bits n) _ _
  | _, _, .select (.bits n) => [8, 16, 32, 64].contains n
  | _, _, .copy .bool | _, _, .and .bool | _, _, .or .bool
  | _, _, .xor .bool | _, _, .not .bool => true
  | _, _, .bswap (.bits n) => [16, 32, 64].contains n
  | _, _, .clz n | _, _, .cls n | _, _, .rbit n | _, _, .ctz n
  | _, _, .fshl n | _, _, .fshr n
  | _, _, .addc n | _, _, .subb n | _, _, .umulw n | _, _, .smulw n => [32, 64].contains n
  | _, _, .zext m n | _, _, .sext m n =>
    [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble (m + 1) n
  | _, _, .trunc m n =>
    [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble (n + 1) m
  | _, _, .bitcast (.bits m) (.bits n) _ =>
    [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n
  | _, _, _ => false

/-- `true` when `armOp` writes `[.bits 32]` to `.gpr (.reg _)` with bits `32..63` zeroed. -/
def armZeroUpper32Op : {sig rs : List Ty} → OpCode sig rs →
    Tup (PArg Reg Empty ArmCond) sig → Tup (PDst Reg Empty ArmCond) rs → Bool
  | _, [.bits 32], _, _, (.gpr (.reg _), ()) => true
  | _, _, _, _, _ => false

/-- Lower `rd := base? + (idx <<< sc.shift) + disp` at `w ∈ {32, 64}` via `ADD_s` / `UBFM`
(+ optional 12-bit immediate `ADD_e`/`SUB_e`), zeroing bits `32..63` when `w = 32`. -/
def armLeaArithIns (w : Nat) (base? : Option Reg) (idx : Reg) (sc : AddrScale)
    (disp : Int64) (rd : Reg) : Option (List Instr × FlagMask) := do
  if !(w == 32 || w == 64) then none
  else
    let rw := armWidthOf w
    let dw := disp.toBitVec.setWidth w
    let d ← match rd with | .reg d => some d | .SP => none
    let ri ← match idx with | .reg ri => some ri | .SP => none
    match base? with
    | some (.reg rb) =>
      let mkSft (dst : XReg) : Instr := armIselInsI (.ADD_s (zr dst rw) (zr rb rw)
        { reg := zr ri rw, amount := Int64.ofNat sc.shift, shift := .LSL })
      if dw == 0#w then some ([mkSft d], maskNone)
      else
        let addDisp ← armAddSubImmI? false rw d .X16 dw
        some ([mkSft .X16, addDisp], maskNone)
    | some .SP => none
    | none =>
      if sc.shift == 0 then
        if dw == 0#w then some ([armIselInsI (.ORR_s (zr d rw) (xzr rw) (sh ri))], maskNone)
        else
          let addDisp ← armAddSubImmI? false rw d ri dw
          some ([addDisp], maskNone)
      else
        let shDir (dst : XReg) : Instr := armIselInsI
          (.UBFM (zr dst rw) (zr ri rw) ((rw.bits - sc.shift) % rw.bits) (rw.bits - 1 - sc.shift))
        if dw == 0#w then some ([shDir d], maskNone)
        else
          let addDisp ← armAddSubImmI? false rw d .X16 dw
          some ([shDir .X16, addDisp], maskNone)

/-- Lower `rd := (base? + (idx <<< sc.shift) + disp)` into AArch64 directives. -/
def armLeaArith (w : Nat) (base? : Option Reg) (idx : Reg) (sc : AddrScale)
    (disp : Int64) (rd : Reg) : Option (List Directive × FlagMask) :=
  emitCleanPair (armLeaArithIns w base? idx sc disp rd)

/-- Lower 64-bit `rd := (base? + ((zext 32 64 idx) <<< shift) + disp)` (`0 ≤ shift ≤ 4` with base,
or `0 ≤ shift ≤ 32` without base) using `ADD_e ... UXTW` or `UBFM` (`Instr` builder). -/
def armLeaArithZextIns (base? : Option Reg) (idx : Reg) (shift : Nat) (disp : Int64)
    (rd : Reg) : Option (List Instr × FlagMask) := do
  let d ← match rd with | .reg d => some d | .SP => none
  let ri ← match idx with | .reg ri => some ri | .SP => none
  match base? with
  | some (.reg rb) =>
    let amt ← armExtendAmount? shift
    if disp == 0 then some ([armAddUxtwI (.reg d) (.reg rb) ri amt], maskNone)
    else
      let addDisp ← armAddSubImmI? false .W64 d .X16 disp.toBitVec
      some ([armAddUxtwI (.reg .X16) (.reg rb) ri amt, addDisp], maskNone)
  | some .SP => none
  | none =>
    if !Nat.ble shift 32 then none
    else
      let mkSh (dst : XReg) : Instr :=
        if shift == 0 then armIselInsI (.ORR_s (zr dst .W32) (xzr .W32) (sh ri))
        else armIselInsI (.UBFM (zr dst .W64) (zr ri .W64) (64 - shift) 31)
      if disp == 0 then some ([mkSh d], maskNone)
      else
        let addDisp ← armAddSubImmI? false .W64 d .X16 disp.toBitVec
        some ([mkSh .X16, addDisp], maskNone)

/-- Lower 64-bit `rd := (base? + ((zext 32 64 idx) <<< shift) + disp)` into AArch64 directives. -/
def armLeaArithZext (base? : Option Reg) (idx : Reg) (shift : Nat) (disp : Int64)
    (rd : Reg) : Option (List Directive × FlagMask) :=
  emitCleanPair (armLeaArithZextIns base? idx shift disp rd)

/-- Finish a list of flag-setting compare instructions for `.flag c` or `.gpr (.reg d)`. -/
def armCmpSeqFinish (cmpCode : List Instr) (cond : ArmCond)
    (dst : PDst Reg Empty ArmCond .bool) : Option (List Instr × FlagMask) :=
  match dst with
  | .flag c => if c == cond then some (cmpCode, maskNZCV) else none
  | .gpr (.reg d) => some (cmpCode ++ [armCset64I d cond], maskNZCV)
  | .gpr .SP | .vec _ => none

/-! ## 2. Fused Memory-Operand Compare (`armCmpMem`, `LDRSB`/`LDRSH` + `CMP`) -/

/-- `armCmpMem` targets `.flag cc` with `cc = armCmpCond o.swap ≠ armCmpCond o` (Rega's
`tryFuseCmp` swapped hint): emit the reversed compare `pb - mem`. -/
def armCmpMemSwapped (o : CmpOp) : PDst Reg Empty ArmCond .bool → Bool
  | .flag cf => cf != armCmpCond o && cf == armCmpCond o.swap
  | _ => false

/-- Reversed compare `SUBS zr, pb, x17` (`pb` in `rb`/`x16`; `8`/`16`-bit sign/zero-extended to
32 bits per `sgn`) for the swapped-condition form of `armCmpMem`. -/
def armCmpMemSwapSeq (sgn : Bool) (n : Nat) (pb : PArg Reg Empty ArmCond (.bits n)) :
    Option (List Instr) :=
  let rw := armWidthOf n
  match pb with
  | .gpr (.reg rb) =>
    if n == 8 || n == 16 then
      some [armExt32I sgn n .X16 rb, armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]
    else some [armIselInsI (.SUBS_s (xzr rw) (zr rb rw) (sh .X17))]
  | .imm cb =>
    if n == 8 || n == 16 then
      let c32 := if sgn then cb.signExtend 32 else cb.setWidth 32
      some (armMovImmI .X16 (c32.setWidth 64) ++
        [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
    else
      some (armMovImmI .X16 (cb.setWidth 64) ++
        [armIselInsI (.SUBS_s (xzr rw) (zr .X16 rw) (sh .X17))])
  | .gpr .SP | .vec _ => none

/-- Fused memory-operand compare `co.evalBits (load (.bits n) a) pb` (`Instr` builder).
Uses `LDRSB`/`LDRSH` for signed `8`/`16`-bit compares (`ldrb + sxtb + cmp -> ldrsb + cmp`),
`LDRB`/`LDRH` (no `UBFM`) for unsigned `8`/`16`-bit compares, and `LDR` for `32`/`64`-bit.
For `armCmpMemSwapped o dst` emits the reversed `pb - mem` compare (`armCmpMemSwapSeq`). -/
def armCmpMemIns (o : CmpOp) (n : Nat) (a : AddrArg Reg) (pb : PArg Reg Empty ArmCond (.bits n))
    (dst : PDst Reg Empty ArmCond .bool) : Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let scale ← armMemScale (.bits n)
    if !armAddrValid scale a then none
    else
      let (setup, addr) := armSetupAddrIns scale a
      let sgn := armIsSignedCmp o
      let ldDir ← if (n == 8 || n == 16) && sgn then armLoadSextDirI n .X17 addr
                  else armLoadDirI (.bits n) .X17 addr
      let rw := armWidthOf n
      if armCmpMemSwapped o dst then
        let sq ← armCmpMemSwapSeq sgn n pb
        armCmpSeqFinish (setup ++ [ldDir] ++ sq) (armCmpCond o.swap) dst
      else
        let cmpSeq ← match pb with
          | .gpr (.reg rb) =>
            if n == 8 || n == 16 then
              some [armExt32I sgn n .X16 rb,
                armIselInsI (.SUBS_s (xzr .W32) (zr .X17 .W32) (sh .X16))]
            else
              some [armIselInsI (.SUBS_s (xzr rw) (zr .X17 rw) (sh rb))]
          | .imm cb =>
            if n == 8 || n == 16 then
              let c32 := if sgn then cb.signExtend 32 else cb.setWidth 32
              match armCmpImmIns? .W32 .X17 c32 with
              | some cmp => some cmp
              | none => some (armMovImmI .X16 (c32.setWidth 64) ++
                  [armIselInsI (.SUBS_s (xzr .W32) (zr .X17 .W32) (sh .X16))])
            else
              match armCmpImmIns? rw .X17 cb with
              | some cmp => some cmp
              | none => some (armMovImmI .X16 (cb.setWidth 64) ++
                  [armIselInsI (.SUBS_s (xzr rw) (zr .X17 rw) (sh .X16))])
          | .gpr .SP | .vec _ => none
        armCmpSeqFinish (setup ++ [ldDir] ++ cmpSeq) (armCmpCond o) dst

/-- Fused memory-operand compare `co.evalBits (load (.bits n) a) pb` returning clean directives
and `maskNZCV`. -/
def armCmpMem (o : CmpOp) (n : Nat) (a : AddrArg Reg) (pb : PArg Reg Empty ArmCond (.bits n))
    (dst : PDst Reg Empty ArmCond .bool) : Option (List Directive × FlagMask) :=
  emitCleanPair (armCmpMemIns o n a pb dst)

/-- Operand-order flag-reuse oracle (`some true` = `va - vb`) matching `armCmpMem`.
Guarantees full `FlagCmpOk ... false` on `32`/`64`-bit compares and signed `8`/`16`-bit
compares (`LDRSB`/`LDRSH` sign-extended to 32 bits). -/
def armCmpMemFlagsOut (o : CmpOp) (n : Nat) (pb : PArg Reg Empty ArmCond (.bits n))
    (dst : PDst Reg Empty ArmCond .bool) : Option Bool :=
  if ![8, 16, 32, 64].contains n then none
  else if (n == 8 || n == 16) && !armIsSignedCmp o then none
  else
    let pbOk := match pb with | .gpr (.reg _) | .imm _ => true | _ => false
    let dstOk := match dst with
      | .gpr (.reg _) => true
      | .flag cf => cf == armCmpCond o
      | _ => false
    if pbOk && dstOk then some true else none

/-- Scratch-aware `armOp` preserving `(X16, X17)` constants across ALU/cmp/select and simple
non-scratch scalar ops (`OPT-7b`). -/
def armOpScr (scr : List (Reg × BitVec 64)) {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg Empty ArmCond) sig) (dsts : Tup (PDst Reg Empty ArmCond) rs)
    (vh : VariantHint) : Option (List Directive × FlagMask × List (Reg × BitVec 64)) :=
  match sig, rs, code, pas, dsts with
  | _, _, .add (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) =>
    (armBinOpScrIns scr .add n pa pb d).map fun (c, cl, s') => (emitClean c, cl, s')
  | _, _, .sub (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) =>
    (armBinOpScrIns scr .sub n pa pb d).map fun (c, cl, s') => (emitClean c, cl, s')
  | _, _, .mul (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) =>
    (armBinOpScrIns scr .mul n pa pb d).map fun (c, cl, s') => (emitClean c, cl, s')
  | _, _, .and (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) =>
    (armBinOpScrIns scr .and n pa pb d).map fun (c, cl, s') => (emitClean c, cl, s')
  | _, _, .or  (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) =>
    (armBinOpScrIns scr .or  n pa pb d).map fun (c, cl, s') => (emitClean c, cl, s')
  | _, _, .xor (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) =>
    (armBinOpScrIns scr .xor n pa pb d).map fun (c, cl, s') => (emitClean c, cl, s')
  | _, _, .cmp o (.bits n) _ rfl, (pa, pb, ()), (dst, ()) =>
    (armCmpOpScrIns scr o n pa pb dst).map fun (c, cl, s') => (emitClean c, cl, s')
  | _, _, .select (.bits n), (pc, pa, pb, ()), (.gpr (.reg d), ()) =>
    (armSelectOpScrIns scr n pc pa pb d).map fun (c, cl, s') => (emitClean c, cl, s')
  | _, _, _, _, _ =>
    (armOp code pas dsts vh).map fun (c, cl) =>
      let scr' := match sig, code, pas with
        | _, .copy _, _ | _, .zext _ _, _ | _, .sext _ _, _ | _, .trunc _ _, _
        | _, .bitcast _ _ _, _ | _, .ofBool _, _ | _, .neg _, _ | _, .not _, _ => scr
        | _, .shl (.bits n), (.gpr (.reg _), .imm _, ())
        | _, .lshr (.bits n), (.gpr (.reg _), .imm _, ())
        | _, .ashr (.bits n), (.gpr (.reg _), .imm _, ()) =>
          if n == 32 || n == 64 then scr else []
        | _, _, _ => []
      (c, cl, scr')

/-- AArch64 `GprIsa` instance over `LeanQbe.T.Arm64.Base`. -/
@[reducible] def armGpr : GprIsa Reg Empty ArmCond Directive where
  condReads := armCondReads
  negCond := armNegCond
  zeroFlags := armZeroFlags
  clearFlags := armClearFlags
  mov := armMov
  movi := armMovi
  setcc := armSetcc
  jmp := armJmp
  jcc := armJcc
  jnzGpr := armJnzGpr
  op := armOp
  load := armLoad
  store := armStore
  supportsScalarOp := armSupportsScalarOp
  cmpFlags := [.eq, .ne, .lt, .ge, .le, .gt, .ls, .hi]
  zeroUpper32Load := true
  zeroExtLoad := true
  zeroUpper32Op := armZeroUpper32Op
  elideZext32 := true
  testOp := armTestOp
  loadSext := armLoadSext
  cmpZeroJcc := armCmpZeroJcc
  testJcc := armTestJcc
  leaArith := armLeaArith
  zeroUpper32LeaArith := true
  loadZextIdx := armLoadZextIdx
  loadSextZextIdx := armLoadSextZextIdx
  storeZextIdx := armStoreZextIdx
  leaArithZext := armLeaArithZext
  cmpMem := armCmpMem
  jnzGprInv? := some armJnzGprInv
  condOfCmp? := some ∘ armCmpCond
  boolFlagOut? := armBoolFlagOut
  cmpFlagsOut? := armCmpFlagsOut
  hasTestFlags := true
  addrCse := true
  widenZextCmp := true
  shiftAlu := armShiftAlu
  zeroUpper32ShiftAlu := true
  deferShiftAlu := true
  shiftCmp := armShiftCmp
  shiftCmpFlagsOut? := armShiftedCmpFlagsOut
  zeroExtOp := armZeroExtOp
  zeroExtBoolCmp := true
  zeroExtSetcc := true
  preferRegImm? := some armPreferRegImm
  preferStoreRegImm := armPreferStoreRegImm
  mulHi? := some armMulHi
  storeScr? := some armStoreScr
  storeZextIdxScr? := some armStoreZextIdxScr
  loadScr? := some armLoadScr
  loadZextIdxScr? := some armLoadZextIdxScr
  opScr? := some armOpScr

end LeanQbe.T.Arm64
