module

public import LeanQbe.T.Arm64.Base
public import LeanQbe.T.IselStepAttr
public import LeanQbe.T.Arm64.IselFlagHooks
public import LeanQbe.T.Arm64.Isel
public import LeanQbe.T.Arm64.IselShift

/-!
# Arm64 Rank-9 Narrow Compare & Fused Load-Compare Helpers (`IselNarrow`)

Provides self-contained, Part-2-ready ISel helpers (free of `*Lemmas*` imports) for:
* `armCmpZextOp`: elides dead `UBFM #0, #7`/`#15` in `8`/`16`-bit unsigned/equality compares when
  the caller establishes `AbiGprHolds` (`az`/`bz = true`, e.g. from `ldrb`/`ldrh` / `hasVarGprZ`).
* `armCmpZeroZextJcc`: emits 1-instruction `CBZ`/`CBNZ` (instead of `UBFM` + `CBZ`/`CBNZ`) for
  `8`/`16`-bit zero-provenance operands.
* `armCmpMem`: fused `LDRSB`/`LDRSH`/`LDRB`/`LDRH`/`LDR` + `CMP` targeting `.flag c` or `.gpr d`
  (turning `ldrb + sxtb + cmp` into `ldrsb + cmp`), plus `armCmpMemFlagsOut`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Zero-Provenance Narrow Compare (`armCmpZextOp`, `armCmpZeroZextJcc`) -/

/-- Compare `rx : XReg` against immediate `cb : BitVec n` at `.W32` (`SUBS_e`/`ADDS_e` or `MOV` +
`SUBS_s`) assuming upper bits `n..31` of `rx` match `cb.setWidth 32` (zero-extended). -/
@[expose]
def armCmpZextRegImm32 (rx : XReg) (cb32 : BitVec 32) : List Instr :=
  match armCmpImmIns? .W32 rx cb32 with
  | some cmp => cmp
  | none => armMovImmI .X17 (cb32.setWidth 64) ++
      [armIselInsI (.SUBS_s (xzr .W32) (zr rx .W32) (sh .X17))]

/-- Finish a list of flag-setting compare instructions for `.flag c` or `.gpr (.reg d)`. -/
@[expose]
def armCmpSeqFinish (cmpCode : List Instr) (cond : ArmCond)
    (dst : PDst Reg Empty ArmCond .bool) : Option (List Instr × FlagMask) :=
  match dst with
  | .flag c => if c == cond then some (cmpCode, maskNZCV) else none
  | .gpr (.reg d) => some (cmpCode ++ [armCset64I d cond], maskNZCV)
  | .gpr .SP | .vec _ => none

/-- Narrow-compare lowering taking `AbiGprHolds` provenance booleans `az`/`bz` for `pa`/`pb`.
When `n ∈ {8, 16}` and `!armIsSignedCmp o`, zero-known GPR operands omit `UBFM #0, #7`/`#15`.
Falls back to `armCmpOpIns` otherwise. -/
@[expose]
def armCmpZextOpIns (o : CmpOp) (n : Nat) (az bz : Bool)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dst : PDst Reg Empty ArmCond .bool) :
    Option (List Instr × FlagMask) :=
  if (n == 8 || n == 16) && !armIsSignedCmp o then
    match pa, pb with
    | .gpr (.reg ra), .imm cb =>
      if az then armCmpSeqFinish (armCmpZextRegImm32 ra (cb.setWidth 32)) (armCmpCond o) dst
      else armCmpOpIns o n pa pb dst
    | .imm ca, .gpr (.reg rb) =>
      if bz then
        match armCmpImmIns? .W32 rb (ca.setWidth 32) with
        | some cmp => armCmpSeqFinish cmp (armCmpCond o.swap) dst
        | none =>
          armCmpSeqFinish
            (armMovImmI .X16 ((ca.setWidth 32).setWidth 64) ++
              [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh rb))])
            (armCmpCond o) dst
      else armCmpOpIns o n pa pb dst
    | .gpr (.reg ra), .gpr (.reg rb) =>
      if az && bz then
        armCmpSeqFinish [armIselInsI (.SUBS_s (xzr .W32) (zr ra .W32) (sh rb))]
          (armCmpCond o) dst
      else armCmpOpIns o n pa pb dst
    | _, _ => armCmpOpIns o n pa pb dst
  else armCmpOpIns o n pa pb dst

/-- Clean directive lowering for `armCmpZextOpIns`. -/
@[expose]
def armCmpZextOp (o : CmpOp) (n : Nat) (az bz : Bool)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dst : PDst Reg Empty ArmCond .bool) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armCmpZextOpIns o n az bz pa pb dst)

/-- Compare-against-zero branch lowering with `isZext : Bool` provenance. When `isZext = true`
at `n ∈ {8, 16}` for `.eq`/`.ne`/`.ule`/`.ugt`, emits 1-instruction `CBZ`/`CBNZ w_x, l` instead
of `UBFM` + `CBZ`/`CBNZ`. Falls back to `armCmpZeroJccIns` otherwise. -/
@[expose]
def armCmpZeroZextJccIns (isZext : Bool) (co : CmpOp) (n : Nat) (r : Reg) (l : Sym) :
    Option (List Instr × FlagMask) :=
  if isZext && (n == 8 || n == 16) then
    match r, co with
    | .reg x, .eq | .reg x, .ule =>
      some ([armIselInsI (w := .W32) (.CBZ (zr x .W32) (.label l))], maskNone)
    | .reg x, .ne | .reg x, .ugt =>
      some ([armIselInsI (w := .W32) (.CBNZ (zr x .W32) (.label l))], maskNone)
    | _, _ => armCmpZeroJccIns co n r l
  else armCmpZeroJccIns co n r l

/-- Clean directive lowering for `armCmpZeroZextJccIns`. -/
@[expose]
def armCmpZeroZextJcc (isZext : Bool) (co : CmpOp) (n : Nat) (r : Reg) (l : Sym) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armCmpZeroZextJccIns isZext co n r l)

/-! ## 2. Fused Memory-Operand Compare (`armCmpMem`, `LDRSB`/`LDRSH` + `CMP`) -/

/-- Fused memory-operand compare `co.evalBits (load (.bits n) a) pb` (`Instr` builder).
Uses `LDRSB`/`LDRSH` for signed `8`/`16`-bit compares (`ldrb + sxtb + cmp -> ldrsb + cmp`),
`LDRB`/`LDRH` (no `UBFM`) for unsigned `8`/`16`-bit compares, and `LDR` for `32`/`64`-bit. -/
@[expose]
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
@[expose]
def armCmpMem (o : CmpOp) (n : Nat) (a : AddrArg Reg) (pb : PArg Reg Empty ArmCond (.bits n))
    (dst : PDst Reg Empty ArmCond .bool) : Option (List Directive × FlagMask) :=
  emitCleanPair (armCmpMemIns o n a pb dst)

/-- Operand-order flag-reuse oracle (`some true` = `va - vb`) matching `armCmpMem`.
Guarantees full `FlagCmpOk ... false` on `32`/`64`-bit compares and signed `8`/`16`-bit
compares (`LDRSB`/`LDRSH` sign-extended to 32 bits). -/
@[expose]
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

end LeanQbe.T.Arm64
