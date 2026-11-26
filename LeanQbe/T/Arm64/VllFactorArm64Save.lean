module

public import LeanQbe.T.Vll.RegaInst
public import LeanQbe.T.Arm64.VllArm64
public import LeanQbe.T.Arm64.VllAsmArm64
public import LeanQbe.T.Arm64.Targ

/-!
# AArch64 `VllNativeHooks` Save/Restore & Shared Wrapper Primitives (`Arm64.VllFactorArm64Save`)

Factored out of `Arm64.VllFactorArm641` to keep every module well under `2,500` LOC with zero
public `*Lemmas*` imports and zero `Amd64`/`Kraken.X64` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T
open LeanQbe.T.Vll

/-- Save callee-saved registers using core `.slotSt`, pairing adjacent GP registers into a single
`.native` `STP` only when `armFitsPairOff (8 * i)` holds. -/
@[expose] def vllArmSaveRegs : Nat → List Arm64.Reg → List (Instr arm64Arch)
  | _, [] => []
  | i, [r] => [.slotSt i r]
  | i, .SP :: r2 :: rs => .slotSt i .SP :: vllArmSaveRegs (i + 1) (r2 :: rs)
  | i, .reg r1 :: .SP :: rs => .slotSt i (.reg r1) :: vllArmSaveRegs (i + 1) (.SP :: rs)
  | i, .reg r1 :: .reg r2 :: rs =>
    (if armFitsPairOff (8 * i) then
       [.native (.instr (armInsI (.STP (zr r1 .W64) (zr r2 .W64) (atOff .SP (8 * i)))))]
     else [.slotSt i (.reg r1), .slotSt (i + 1) (.reg r2)]) ++
      vllArmSaveRegs (i + 2) rs

/-- Restore callee-saved registers using core `.slotLd`, pairing adjacent GP registers into a
single `.native` `LDP` only when `armFitsPairOff (8 * i)` holds. -/
@[expose] def vllArmRestoreRegs : Nat → List Arm64.Reg → List (Instr arm64Arch)
  | _, [] => []
  | i, [r] => [.slotLd r i]
  | i, .SP :: r2 :: rs => .slotLd .SP i :: vllArmRestoreRegs (i + 1) (r2 :: rs)
  | i, .reg r1 :: .SP :: rs => .slotLd (.reg r1) i :: vllArmRestoreRegs (i + 1) (.SP :: rs)
  | i, .reg r1 :: .reg r2 :: rs =>
    (if armFitsPairOff (8 * i) then
       [.native (.instr (armInsI (.LDP (zr r1 .W64) (zr r2 .W64) (atOff .SP (8 * i)))))]
     else [.slotLd (.reg r1) i, .slotLd (.reg r2) (i + 1)]) ++
      vllArmRestoreRegs (i + 2) rs

/-- Pure core `.load (.w8/.w16) .sx` lowering for `loadSext`, matching `armLoadSext` 1:1. -/
@[expose] def vllArmLoadSext (m n : Nat) (rd : Arm64.Reg) (a : AddrArg Arm64.Reg) :
    Option (List (Instr arm64Arch) × FlagMask) :=
  if !(m == 8 || m == 16) || !Nat.blt m n || !Nat.ble n 64 then none
  else match m with
    | 8  => if armAddrValid 1 a then some ([.load .w8 .sx rd a], maskNone) else none
    | 16 => if armAddrValid 2 a then some ([.load .w16 .sx rd a], maskNone) else none
    | _  => none

/-- Wrap a Kraken AArch64 `(List Directive × FlagMask)` result into `.native` VLL instructions. -/
@[expose] def wrapArmNative (res : Option (List _root_.Directive × FlagMask)) :
    Option (List (Instr arm64Arch) × FlagMask) :=
  res.map fun (ds, cl) => (ds.map .native, cl)

/-- Pure core `.cmp` / `.cmp + .setcc` helper for 32/64-bit comparisons. -/
@[expose] def vllArmCmpCore (o : CmpOp) (w : Width) (ra : XReg) (rhs : Src arm64Arch)
    (dst : PDst Arm64.Reg Empty ArmCond .bool) : Option (List (Instr arm64Arch) × FlagMask) :=
  match dst with
  | .flag cf => if cf == armCmpCond o then some ([.cmp w (.reg ra) rhs], maskNZCV) else none
  | .gpr (.reg d) => some ([.cmp w (.reg ra) rhs, .setcc (.reg d) (armCmpCond o)], maskNZCV)
  | .gpr .SP | .vec _ => none

end LeanQbe.T.Arm64
