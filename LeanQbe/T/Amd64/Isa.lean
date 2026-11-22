module

public import LeanQbe.T.Amd64.Isel
public import LeanQbe.T.Amd64.IselVec
public import LeanQbe.T.Amd64.Frame
public import LeanQbe.T.Legal

/-!
# SysV x64 Pure `Isa` & `LegalTarget` (`P2-B`)

Provides `x64Isa : Isa` and `x64LegalTarget : LegalTarget` with zero `*Lemmas*` imports so
executables (`leanqbe`) and pure compilation consumers do not link verification proof objects.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

open LeanQbe.T

/-- True iff `x64Load`/`x64Store`/`x64Vload`/`x64Vstore` encodes `[base + disp]` in one
displacement operand without scratch materialization. -/
def x64SupportsAddrDisp (t : Ty) (d : BitVec 64) : Bool :=
  let okTy := match t with
    | .bool => true
    | .bits n => x64BitWidths.contains n
    | .pair _ _ => (x64VecSlotWidth t).isSome
    | .float _ => false
  okTy && fitsImm32 d

/-- True iff `x64Load`/`x64Store`/`x64Vload`/`x64Vstore` encodes `[base + idx*scale + disp]`
in one SIB+disp operand without scratch materialization. -/
def x64SupportsAddrIdx (t : Ty) (_sc : AddrScale) (d : BitVec 64) : Bool :=
  x64SupportsAddrDisp t d

/-- True iff `x64CmpMem` / `x64TestMem` supports a scalar memory operand of type `t`. -/
def x64SupportsCmpMem : Ty → Bool
  | .bits n => x64BitWidths.contains n
  | _ => false

/-- Pure SysV x64 `Isa` (zero `*Lemmas*` imports). -/
@[reducible] def x64Isa : Isa where
  Reg := Reg64
  VReg := RegMm
  Cond := CondCode
  Directive := Directive
  gpr := x64Gpr
  vec := x64Vec
  frame := x64Frame
  supportsAddrDisp := x64SupportsAddrDisp
  supportsAddrIdx := x64SupportsAddrIdx
  supportsTestFuse := true
  supportsCmpMem := x64SupportsCmpMem
  supportsTestMem := x64SupportsCmpMem

/-- SysV x64 legalization capability record aligned with `x64Isa` (`[8, 16, 32, 64]` scalar,
`[128, 256, 512]` packed `[i32, f32]` SIMD, 128-bit SSE shuffle/float ops, no SHA-NI). -/
def x64LegalTarget : LegalTarget :=
  { LegalTarget.x64 [128, 256, 512] with
    floatFmts := [.s]
    vecIntOpSupported := fun {_ _} code t uniformImm =>
      match code with
      | .copy _ => true
      | .add _ => isI32Vec t
      | .and _ | .or _ | .xor _ | .not _ | .ternlog _ _ => true
      | .rotr _ | .lshr _ => isI32Vec t && uniformImm
      | .shufd _ _ | .shufb _ | .alignr _ _ | .blendw _ _ => t.size == 128
      | _ => false
    vecFloatOpSupported := fun {_ _} code t =>
      match code with
      | .fadd _ | .fsub _ => isF32Vec t && t.size == 128
      | _ => false }

theorem x64LegalTarget_valid : x64LegalTarget.valid = true := by
  decide

end LeanQbe.T.Amd64
