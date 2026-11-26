module

public import LeanQbe.T.RegaDefs

/-!
# Flag-Liveness Gate and Zero-Idiom Lowering Helpers (`T.RegaZero`)

Shared by `LeanQbe.T.Rega`, `LeanQbe.T.RegaLemmas0`, and `LeanQbe.T.RegaLemmasZero`:
* `stHasFlagReg` and `flagsDeadAt`: combine sound in-state flag deadness with the untrusted
  `Hints.deadFlags` oracle.
* `execMovi`: flag-liveness-gated `movi` lowering hook (`I.gpr.moviDeadFlags?`), preserving
  exact `I.gpr.movi` fallback when `moviDeadFlags? = none` or flags may be live.
* `tryMoviZero`: `OpCode` zero-constant lowering via `I.gpr.moviDeadFlags?` when flags are
  dead, applying `clob` (`maskAll` on x64 `xorl %ed, %ed`) so invalid hints fail closed.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-- `true` iff symbolic register map `R` currently holds any live `.flag` binding. -/
def stHasFlagReg {I : Isa} (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : Bool :=
  R.any fun (_, rl) => match rl with | .flag _ => true | _ => false

/-- `true` when flags are dead in `st` (either neither `st.flags` nor `.flag` regs hold a
flag, or the untrusted `Hints.deadFlags` oracle marks `ip?` dead). Always paired with the hook's
returned `FlagMask` so an invalid hint drops any live flag fact and fails closed. -/
def flagsDeadAt (I : Isa) (h : I.Hints) (ip? : Option Nat) (st : SymState I) : Bool :=
  (st.flags.isNone && !stHasFlagReg st.regs) || (ip?.map (h.deadFlags.getD · false)).getD false

/-- Select `I.gpr.moviDeadFlags?` when flags are dead in `st` or `deadHint = true`, falling
back to `I.gpr.movi` (`FlagMask.none`) otherwise. -/
def execMovi (I : Isa) (st : SymState I) (deadHint : Bool) (d : I.Reg) (c : BitVec 64) :
    List I.Directive × FlagMask :=
  match I.gpr.moviDeadFlags? with
  | some fn =>
    if (st.flags.isNone && !stHasFlagReg st.regs) || deadHint then fn d c
    else (I.gpr.movi d c, FlagMask.none)
  | none => (I.gpr.movi d c, FlagMask.none)

/-- Lower a zero-constant scalar op via `I.gpr.moviDeadFlags?` when `flagsDeadAt` holds. -/
def tryMoviZero (I : Isa) (h : I.Hints) (ip : Nat) (st : SymState I)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask × Bool) :=
  if !flagsDeadAt I h (some ip) st then none
  else
    match I.gpr.moviDeadFlags? with
    | none => none
    | some fn =>
      let emit (n : Nat) (rd : I.Reg) :=
        let p := fn rd 0#64
        some (p.1, p.2, Nat.beq n 32 && I.frame.bitWidths.contains 32)
      match code with
      | .copy (.bits n) => match args, dsts with
        | (.imm c, ()), (.gpr rd, ()) =>
          if Nat.ble n 64 && I.frame.bitWidths.contains n && c == 0#n then emit n rd else none
        | _, _ => none
      | .copy .bool => match args, dsts with
        | (.imm false, ()), (.gpr rd, ()) => emit 0 rd
        | _, _ => none
      | .ofBool n => match args, dsts with
        | (.imm false, ()), (.gpr rd, ()) =>
          if Nat.ble n 64 && I.frame.bitWidths.contains n then emit n rd else none
        | _, _ => none
      | .bitcast (.bits m) (.bits n) _ => match args, dsts with
        | (.imm c, ()), (.gpr rd, ()) =>
          if Nat.ble m 64 && Nat.ble n 64 && I.frame.bitWidths.contains m &&
              I.frame.bitWidths.contains n && c == 0#m then emit n rd
          else none
        | _, _ => none
      | _ => none

end Rega
end LeanQbe.T
