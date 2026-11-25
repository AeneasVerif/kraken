module

public import LeanQbe.T.Arm64.Isel
public import LeanQbe.T.Arm64.Frame
public import LeanQbe.T.Legal

/-!
# AAPCS64 Arm64 Pure `Isa` & `LegalTarget`

Provides `armIsa : Isa` and `armLegalTarget : LegalTarget` with zero `*Lemmas*` imports so
executables (`leanqbe-arm64`) and pure compilation consumers do not link verification proof objects.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-- True iff `armLoad`/`armStore` encodes `[base + disp]` as one scaled unsigned offset without
literal-pool `.X16` fallback. -/
def armSupportsAddrDisp (t : Ty) (d : BitVec 64) : Bool :=
  match armMemScale t with
  | some sc => armFitsScaledOff sc (Int64.ofBitVec d)
  | none => false

/-- True iff `armLoad`/`armStore` encodes `[base + idx*scale + disp]` using `armSetupAddrIns`
and scratch `.X16` only. -/
def armSupportsAddrIdx (t : Ty) (sc : AddrScale) (d : BitVec 64) : Bool :=
  match armMemScale t with
  | some scale => armAddrIdxValid scale sc (Int64.ofBitVec d)
  | none => false

/-- Pure AAPCS64 Arm64 scalar `Isa` (`VecIsa.empty`, zero `*Lemmas*` imports). -/
@[reducible] def armIsa : Isa where
  Reg := Reg
  VReg := Empty
  Cond := ArmCond
  Directive := Directive
  gpr := armGpr
  vec := VecIsa.empty Reg ArmCond Directive
  frame := armFrame
  supportsAddrDisp := armSupportsAddrDisp
  supportsAddrIdx := armSupportsAddrIdx
  supportsTestFuse := true
  supportsAddrZextIdx := armSupportsAddrIdx

/-- AArch64 scalar legalization capability record (`LegalTarget.aarch64`, no vectors/floats). -/
def armLegalTarget : LegalTarget := LegalTarget.aarch64

theorem armLegalTarget_valid : armLegalTarget.valid = true := by
  decide

end LeanQbe.T.Arm64
