module

public import LeanQbe.T.RegaDefs

/-!
# `.zext 32 64` Index-Extension & Addressing Helpers (`RegaZext`)

Detects `.zext 32 64` index variables inside `DefFact` address trees (`addrSum`, `scaleOff`,
`addImm64`, `zextVar 32 64`) for `Live.elideAddrTreeDeps` and `Rega` (`tryAddrZext`,
`extractLeaZext64`, `tryLeaArithZext`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-- Match `v` as `.zextVar 32 64 idx`, returning `some idx`. -/
def asZext32? (defs : Trie DefFact) (v : Nat) : Option Nat :=
  match defs.find? v with
  | some (.zextVar m n idx) => if Nat.beq m 32 && Nat.beq n 64 then some idx else none
  | _ => none

/-- If `b + (i <<< sh)` uses a `.zextVar 32 64 idx` operand (checking both operand orders when
`sh = 0`), return `(baseVar, idxVar, zextVar)`. -/
def zextAddrSumVar? (defs : Trie DefFact) (b i sh : Nat) : Option (Nat × Nat × Nat) :=
  match asZext32? defs i with
  | some idx => some (b, idx, i)
  | none =>
    if Nat.beq sh 0 then
      (asZext32? defs b).map fun idx => (i, idx, b)
    else none

/-- Resolve `a : Arg VNat i64` to `(baseReg, idxReg, scale, disp)` when `a` is an `addrSum`
whose index operand is a `.zextVar 32 64` variable. -/
def tryAddrZext (I : Isa) (st : SymState I) {α : Type} (a : Arg VNat i64)
    (k : I.Reg → I.Reg → AddrScale → Int64 → Option α) : Option α :=
  match a with
  | .imm _ => none
  | .var x =>
    match st.defs.find? x with
    | some (.addrSum base idx sh d) =>
      match zextAddrSumVar? st.defs base idx sh with
      | some (rbVar, ridxVar, _) =>
        (AddrScale.ofShift? sh).bind fun sc =>
          (findGprFor I true st.regs (.var rbVar)).bind fun rb =>
            (findGprFor I true st.regs (.var ridxVar)).bind fun ri =>
              k rb ri sc (Int64.ofBitVec d)
      | none => none
    | _ => none

/-- Match `v` as `((zext 32 64 idx) <<< sh) + d`, returning `(idx, sh, d)`. -/
def zextScalePart? (defs : Trie DefFact) (v : Nat) : Option (Nat × Nat × BitVec 64) :=
  match defs.find? v with
  | some (.zextVar m n idx) => if Nat.beq m 32 && Nat.beq n 64 then some (idx, 0, 0#64) else none
  | some (.addImm64 z d) => (asZext32? defs z).map fun idx => (idx, 0, d)
  | some (.scaleOff z sh d) => (asZext32? defs z).map fun idx => (idx, sh, d)
  | _ => none

/-- Extract `(base, disp)` from `v`, unwrapping `.addImm64`. -/
def baseDispPart (defs : Trie DefFact) (v : Nat) : Nat × BitVec 64 :=
  match defs.find? v with
  | some (.addImm64 b d) => (b, d)
  | _ => (v, 0#64)

/-- Helper for `x + cc` (`cc` signed 64-bit disp) when `x` is a `.zextVar 32 64` address tree. -/
def extractLeaZextImm (defs : Trie DefFact) (x : Nat) (cc : BitVec 64) :
    Option (Option Nat × Nat × Nat × Int64) :=
  match defs.find? x with
  | some (.addrSum b i sh d) =>
    (zextAddrSumVar? defs b i sh).map fun (rb, ridx, _) =>
      (some rb, ridx, sh, Int64.ofBitVec (d + cc))
  | _ =>
    match zextScalePart? defs x with
    | some (idx, sh, d) =>
      if Nat.blt 0 sh then some (none, idx, sh, Int64.ofBitVec (d + cc)) else none
    | none => none

/-- Extract `(base?, idx, shift, disp)` for 64-bit
`rd := base? + ((zext 32 64 idx) <<< shift) + disp`
from a single `Op` whose operands have `.zextVar 32 64` provenance. -/
def extractLeaZext64 (defs : Trie DefFact) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig →
    Option (Option Nat × Nat × Nat × Int64)
  | _, _, .shl (.bits 64), (.var x, .imm k, ()) =>
    let kn := k.toNat
    if !Nat.blt kn 64 then none
    else match zextScalePart? defs x with
      | some (idx, sh, d) =>
        if Nat.blt 0 (sh + kn) && Nat.blt (sh + kn) 64 then
          some (none, idx, sh + kn, Int64.ofBitVec (d <<< kn))
        else none
      | none => none
  | _, _, .add (.bits 64), (.var x, .var y, ()) =>
    (match zextScalePart? defs x with
     | some (idx, sh, d1) =>
       let (rb, d2) := baseDispPart defs y
       some (some rb, idx, sh, Int64.ofBitVec (d1 + d2))
     | none => none) <|>
    (match zextScalePart? defs y with
     | some (idx, sh, d1) =>
       let (rb, d2) := baseDispPart defs x
       some (some rb, idx, sh, Int64.ofBitVec (d1 + d2))
     | none => none)
  | _, _, .add (.bits 64), (.var x, .imm c, ())
  | _, _, .add (.bits 64), (.imm c, .var x, ()) =>
    extractLeaZextImm defs x (c.setWidth 64)
  | _, _, .sub (.bits 64), (.var x, .imm c, ()) =>
    extractLeaZextImm defs x (-(c.setWidth 64))
  | _, _, _, _ => none

/-- Lower 64-bit `rd := base? + ((zext 32 64 idx) <<< shift) + disp` via `I.gpr.leaArithZext`. -/
def tryLeaArithZext (I : Isa) (st : SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) : Option (List I.Directive × FlagMask × Bool) :=
  match ts, dsts with
  | [.bits 64], (.gpr rd, ()) =>
    (extractLeaZext64 st.defs code args).bind fun (base?, idx, sh, disp) =>
      let rbOpt? : Option (Option I.Reg) := match base? with
        | some b => (findGprFor I true st.regs (.var b)).map some
        | none => some none
      rbOpt?.bind fun rb? =>
        (findGprFor I true st.regs (.var idx)).bind fun ri =>
          (I.gpr.leaArithZext rb? ri sh disp rd).map fun (c, cl) => (c, cl, false)
  | _, _ => none

end Rega
end LeanQbe.T
