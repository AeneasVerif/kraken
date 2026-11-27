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

/-- Address fact of `x`: its `DefFact`, except that under `cse` an `addImm64 p c` link over an
`addrSum p` (`GprIsa.addrCse`) is unfolded back to `addrSum b i sh (d + c)`. -/
def addrDefOf (cse : Bool) (defs : Trie DefFact) (x : Nat) : Option DefFact :=
  match defs.find? x with
  | some (.addImm64 p c) =>
    if cse then
      match defs.find? p with
      | some (.addrSum b i sh d) => some (.addrSum b i sh (d + c))
      | _ => some (.addImm64 p c)
    else some (.addImm64 p c)
  | df => df

/-- Resolve `a : Arg VNat i64` to `(baseReg, idxReg, scale, disp)` when `a` is an `addrSum`
whose index operand is a `.zextVar 32 64` variable. -/
def tryAddrZext (I : Isa) (st : SymState I) {α : Type} (a : Arg VNat i64)
    (k : I.Reg → I.Reg → AddrScale → Int64 → Option α) : Option α :=
  match a with
  | .imm _ => none
  | .var x =>
    match addrDefOf I.gpr.addrCse st.defs x with
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

/-! ## Shifted-Register ALU Fusion (`GprIsa.shiftAlu`) -/

/-- Match `add`/`sub`/`and`/`or`/`xor (.bits _)` over two variables as `(op, x, y)`. -/
def rmwVarVar? : {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig →
    Option (RmwOp × Nat × Nat)
  | _, _, .add (.bits _), (.var x, .var y, ()) => some (.add, x, y)
  | _, _, .sub (.bits _), (.var x, .var y, ()) => some (.sub, x, y)
  | _, _, .and (.bits _), (.var x, .var y, ()) => some (.and, x, y)
  | _, _, .or (.bits _), (.var x, .var y, ()) => some (.or, x, y)
  | _, _, .xor (.bits _), (.var x, .var y, ()) => some (.xor, x, y)
  | _, _, _, _ => none

/-- `t` as `(src, sh, k)` with `t = sh.eval src k` at width `w`. -/
def asShiftOf? (defs : Trie DefFact) (w t : Nat) : Option (Nat × AluShift × Nat) :=
  match defs.find? t with
  | some (.scaleOff x k d) => if Nat.beq w 64 && d == 0#64 then some (x, .lsl, k) else none
  | some (.shlVarImm w' x k) => if Nat.beq w' w then some (x, .lsl, k) else none
  | some (.shiftVarImm w' sh x k) => if Nat.beq w' w then some (x, sh, k) else none
  | _ => none

/-- Lower `rd := a op t` where `t` is an immediate shift of a GPR-resident `src` via
`I.gpr.shiftAlu` (`rd := a op (src sh k)`). -/
def shiftAluGo (I : Isa) (st : SymState I) (w : Nat) (op : RmwOp) (rd : I.Reg) (a t : Nat) :
    Option (List I.Directive × FlagMask × Bool) :=
  (asShiftOf? st.defs w t).bind fun (src, sh, k) =>
    (findGprFor I true st.regs (.var a)).bind fun ra =>
      (findGprFor I true st.regs (.var src)).bind fun rs =>
        (I.gpr.shiftAlu w (op.toOpCode w) ra rs sh k rd).map fun (c, cl) =>
          (c, cl, Nat.beq w 32 && I.gpr.zeroUpper32ShiftAlu)

/-- `shiftAluGo` on `a op t`, or on `t op a` for commutative `op`. -/
def tryShiftAlu (I : Isa) (st : SymState I) {sig ts : List Ty} (w : Nat) (code : OpCode sig ts)
    (args : Tup (Arg VNat) sig) (rd : I.Reg) : Option (List I.Directive × FlagMask × Bool) :=
  (rmwVarVar? code args).bind fun (op, x, y) =>
    shiftAluGo I st w op rd x y <|> if op.isComm then shiftAluGo I st w op rd y x else none

/-! ## Shifted-Register Compare Fusion (`GprIsa.shiftCmp`) -/

/-- Lower `x <co> y` via `I.gpr.shiftCmp` when `y` is a shift of `src` (`lhsShift = false`)
or `x` is a shift of `src` (`lhsShift = true`), returning `(code, clob, lhsShift)`. -/
def shiftCmpGo (I : Isa) (st : SymState I) (co : CmpOp) (w x y : Nat)
    (pd : PDst I.Reg I.VReg I.Cond .bool) :
    Option (List I.Directive × FlagMask × Bool) :=
  let run (lhsShift : Bool) (a t : Nat) : Option (List I.Directive × FlagMask × Bool) :=
    (asShiftOf? st.defs w t).bind fun (src, sh, k) =>
      (findGprFor I true st.regs (.var a)).bind fun ra =>
        (findGprFor I true st.regs (.var src)).bind fun rs =>
          let (r0, r1) := if lhsShift then (rs, ra) else (ra, rs)
          (I.gpr.shiftCmp co w r0 r1 sh k lhsShift pd).map fun (d, cl) => (d, cl, lhsShift)
  run false x y <|> run true y x

/-- Match `.cmp co (.bits w) .bool _` over two variables and lower via `shiftCmpGo`. -/
def tryShiftCmpFuse (I : Isa) (st : SymState I) {sig ts : List Ty} (code : OpCode sig ts)
    (args : Tup (Arg VNat) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask × Bool) :=
  match sig, ts, code, args, dsts with
  | _, _, .cmp co (.bits w) .bool _, (.var x, .var y, ()), (pd, ()) =>
    if !Nat.ble w 64 then none else shiftCmpGo I st co w x y pd
  | _, _, _, _, _ => none

/-- `true` when `x` is a scaled (`sh ≠ 0`) `addrSum`. -/
def isScaledAddrSum (defs : Trie DefFact) (x : Nat) : Bool :=
  match defs.find? x with
  | some (.addrSum _ _ sh _) => !Nat.beq sh 0
  | _ => false

/-- `x ± c` over a scaled `addrSum` `x` (see `GprIsa.addrCse`). -/
def addrCseHit (defs : Trie DefFact) :
    {sig rs : List Ty} → OpCode sig rs → Tup (Arg VNat) sig → Bool
  | _, _, .add (.bits _), (.var x, .imm _, ()) => isScaledAddrSum defs x
  | _, _, .add (.bits _), (.imm _, .var x, ()) => isScaledAddrSum defs x
  | _, _, .sub (.bits _), (.var x, .imm _, ()) => isScaledAddrSum defs x
  | _, _, _, _ => false

/-- Lookup a non-scratch canonical `.gprZ` register holding `.var x`. -/
def tryGprZ (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) {α : Type}
    (x : Nat) (k : I.Reg → Option α) : Option α :=
  R.findSome? fun (sa', rl) =>
    match rl with
    | .gprZ r => if !(I.frame.scratch.contains r) && symArgEq sa' (.var x) then k r else none
    | _ => none

/-- Widen an `n`-bit variable (in `.gprZ`) or immediate operand to a 32-bit `PArg`. -/
def widenZextArg32 (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) {n : Nat} :
    Arg VNat (.bits n) → Option (PArg I.Reg I.VReg I.Cond (.bits 32))
  | .var x => tryGprZ I R x (fun r => some (.gpr r))
  | .imm c => some (.imm (c.setWidth 32))

end Rega
end LeanQbe.T
