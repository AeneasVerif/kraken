module

public import LeanQbe.T.RegaDefs

/-!
# Verified `Base + ConstDisp` Rematerialization Helpers (`T.RegaRemat`)

Shared by `LeanQbe.T.Rega`, `LeanQbe.T.RegaLemmas1`, `LeanQbe.T.RegaLemmas3b`, and
`LeanQbe.T.RegaLemmasRemat`:
* `rematAddImm64`: single-instruction, flag-preserving `rd := rb + disp` via existing
  `I.gpr.op (.add i64)` with `VariantHint.disp` (`leaq disp(%rb), %rd` on x86-64;
  `add/sub xd, xrb, #imm` on AArch64).
* `ShufMove`: internal move language for `Rega.shuffle` adding `rematAdd` alongside
  `Target.Move` (zero edits to `Target.lean`).
* `tryRematDirect`, `tryRematAdd64SameDst`, `tryRematCmpEqImm`, `rematPreStep`:
  on-demand `Base + ConstDisp` rematerialization in `Rega.lowerOp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-- Flag-preserving 64-bit `rd := rb + disp` rematerialization via existing `I.gpr.op`. -/
def rematAddImm64 (I : Isa) (rb rd : I.Reg) (disp : BitVec 64) : Option (List I.Directive) :=
  match I.gpr.op (.add (.bits 64)) (.gpr rb, .imm disp, ()) (.gpr rd, ())
      (.disp (Int64.ofBitVec disp)) with
  | some (c, clob) => if clob == FlagMask.none then some c else none
  | none => none

/-- Internal move language for `Rega.shuffle`: extends `I.Move` with `Base + ConstDisp`
rematerialization without altering `Target.Move`. -/
inductive ShufMove (Reg VReg Cond : Type) where
  | base (mv : Move Reg VReg Cond)
  | rematAdd (x base : Nat) (disp : BitVec 64) (d : Reg)
  deriving DecidableEq, Repr

/-- Lookup a rematerializable `.addImm64 base disp` definition for `x` whose `base` currently
resides in a non-scratch GPR `rb` and whose `I.gpr.op` rematerialization is flag-preserving. -/
def rematBaseOf? (I : Isa) (st : SymState I) (x : Nat) : Option (Nat × BitVec 64 × I.Reg) :=
  match st.defs.find? x with
  | some (.addImm64 base disp) =>
    (findGprFor I true st.regs (.var base)).map fun rb => (base, disp, rb)
  | _ => none

/-- Find the first `i64` variable argument in `args` that is missing from non-scratch GPRs
in `st.regs` and has a live `.addImm64 base disp` base in a non-scratch GPR. -/
def findMissingRematArg (I : Isa) (st : SymState I) :
    {sig : List Ty} → Tup (Arg VNat) sig → Option (Nat × Nat × BitVec 64 × I.Reg)
  | [], () => none
  | t :: _, (a, as) =>
    match t, a with
    | .bits 64, .var x =>
      if (findGprFor I true st.regs (.var x)).isNone then
        match rematBaseOf? I st x with
        | some (base, disp, rb) => some (x, base, disp, rb)
        | none => findMissingRematArg I st as
      else findMissingRematArg I st as
    | _, _ => findMissingRematArg I st as

/-- Direct 1-instruction `Base + ConstDisp` lowering when an `i64` op (`copy`, `add imm`,
`sub imm`) yields `recordDef = some (.addImm64 base disp)` into `.gpr rd`. -/
def tryRematDirect (I : Isa) (st : SymState I) (df? : Option DefFact) {ts : List Ty}
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) : Option (List I.Directive × FlagMask) :=
  match ts, dsts, df? with
  | [.bits 64], (.gpr rd, ()), some (.addImm64 base disp) =>
    (findGprFor I true st.regs (.var base)).bind fun rb =>
      (rematAddImm64 I rb rd disp).map (·, FlagMask.none)
  | _, _, _ => none

/-- Two-instruction 64-bit `(base + disp) + y` / `y + (base + disp)` lowering into `.gpr rd`
with zero extra registers (even when `rd == ry`), using `rd := rb + ry; rd := rd + disp`. -/
def tryRematAdd64SameDst (I : Isa) (st : SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) : Option (List I.Directive × FlagMask) :=
  match sig, ts, code, args, dsts with
  | _, _, .add (.bits 64), (.var x, .var y, ()), (.gpr rd, ()) =>
    let run (remVar otherVar : Nat) : Option (List I.Directive × FlagMask) :=
      if (findGprFor I true st.regs (.var remVar)).isSome then none
      else (rematBaseOf? I st remVar).bind fun (_, disp, rb) =>
        (findGprFor I true st.regs (.var otherVar)).bind fun ry =>
          (I.gpr.op (.add (.bits 64)) (.gpr rb, .gpr ry, ()) (.gpr rd, ()) .default).bind
            fun (c1, cl1) =>
              (rematAddImm64 I rd rd disp).map fun c2 => (c1 ++ c2, cl1)
    run x y <|> run y x
  | _, _, _, _, _ => none

/-- Fold 64-bit equality/inequality `(base + disp) ==/!= imm` into `base ==/!= (imm - disp)`
without allocating any temporary register. -/
def tryRematCmpEqImm (I : Isa) (st : SymState I) (vh : VariantHint) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) : Option (List I.Directive × FlagMask) :=
  match sig, ts, code, args, dsts with
  | _, _, .cmp co (.bits 64) .bool _, (a, b, ()), (pd, ()) =>
    if !(co == .eq || co == .ne) then none
    else
      let run (x : Nat) (c : BitVec 64) : Option (List I.Directive × FlagMask) :=
        if (findGprFor I true st.regs (.var x)).isSome then none
        else (rematBaseOf? I st x).bind fun (_, disp, rb) =>
          I.gpr.op (.cmp co (.bits 64)) (.gpr rb, .imm (c - disp), ()) (pd, ()) vh
      match a, b with
      | .var x, .imm c | .imm c, .var x => run x c
      | _, _ => none
  | _, _, _, _, _ => none

/-- Check whether `r` has no binding at all in `st.regs`. -/
def regUnusedIn (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (r : I.Reg) : Bool :=
  R.all fun (_, rl) => !regLocMatchesGpr rl r

/-- Pick a non-scratch allocatable register to materialize a missing `addImm64` operand of `op`:
either its sole `.gpr rd` destination or a register completely unused in `st.regs`. -/
def rematTempCands (I : Isa) (saved : List I.Reg) (st : SymState I) {ts : List Ty}
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) : List I.Reg :=
  let dstCands : List I.Reg := match ts, dsts with
    | [_], (.gpr rd, ()) => [rd]
    | _, _ => []
  let freeCands : List I.Reg :=
    (I.frame.allocatable ++ saved).filter fun r =>
      !(I.frame.scratch.contains r) && regUnusedIn I st.regs r
  dstCands ++ freeCands

end Rega
end LeanQbe.T
