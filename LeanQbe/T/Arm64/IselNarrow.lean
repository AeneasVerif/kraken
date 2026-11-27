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

end LeanQbe.T.Arm64
