module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.IselLemmas4
public import Kraken.AArch64.Print

/-!
# AArch64 Directive Inspection Predicates (`Arm64DirPreds`)

Directive-matching predicates for testing instruction selection, branch fusion,
and constant materialization on `armTarget`. This module imports ONLY AArch64 / AAPCS64
constructs and never imports `Kraken.X64`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Arm64DirPreds

open LeanQbe.T LeanQbe.T.Arm64

/-- `cset` is `CSINC xd, xzr, xzr, ¬c`. -/
def isCsetDir (d : armTarget.toIsa.Directive) : Bool :=
  (Kraken.AArch64.Print.directive d).startsWith "csinc"

def isCbzDir : Directive → Bool
  | .instr { operation := .CBZ .., .. } => true
  | _ => false

def isCbnzDir : Directive → Bool
  | .instr { operation := .CBNZ .., .. } => true
  | _ => false

def isTbzDir : Directive → Bool
  | .instr { operation := .TBZ .., .. } => true
  | _ => false

def isTbnzDir : Directive → Bool
  | .instr { operation := .TBNZ .., .. } => true
  | _ => false

def isTbzOrTbnzDir : Directive → Bool
  | .instr { operation := .TBZ .., .. }
  | .instr { operation := .TBNZ .., .. } => true
  | _ => false

def isSubsDir : Directive → Bool
  | .instr { operation := .SUBS_e .., .. }
  | .instr { operation := .SUBS_s .., .. } => true
  | _ => false

def isAndsImmDir : Directive → Bool
  | .instr { operation := .ANDS_i .., .. } => true
  | _ => false

def isAndsRegDir : Directive → Bool
  | .instr { operation := .ANDS_s .., .. } => true
  | _ => false

def isAndsDir (d : Directive) : Bool :=
  isAndsImmDir d || isAndsRegDir d

def isAndDir : Directive → Bool
  | .instr { operation := .AND_i .., .. }
  | .instr { operation := .AND_s .., .. } => true
  | _ => false

def isBcondDir : Directive → Bool
  | .instr { operation := .B_cond .., .. } => true
  | _ => false

def isAddScaledDir : Directive → Bool
  | .instr { operation := .ADD_s (.low (.reg .X16) .W64) _ _, .. } => true
  | _ => false

def isSubImmX16Dir : Directive → Bool
  | .instr { operation := .SUB_e (.low (.reg .X16) .W64) _ _, .. } => true
  | _ => false

def isLslDir : Directive → Bool
  | .instr { operation := .UBFM _ _ 62 61, .. }
  | .instr { operation := .UBFM _ _ 61 60, .. }
  | .instr { operation := .LSLV .., .. } => true
  | _ => false

def isExtDir : Directive → Bool
  | .instr { operation := .UBFM _ _ 0 7, .. }
  | .instr { operation := .SBFM _ _ 0 7, .. }
  | .instr { operation := .UBFM _ _ 0 15, .. }
  | .instr { operation := .SBFM _ _ 0 15, .. } => true
  | _ => false

def isMovnDir : Directive → Bool
  | .instr { operation := .MOVN .., .. } => true
  | _ => false

def isMovz0Dir : Directive → Bool
  | .instr { operation := .MOVZ _ (.int64 0) _, .. } => true
  | _ => false

def isMovzDir : Directive → Bool
  | .instr { operation := .MOVZ .., .. } => true
  | _ => false

def isMovkDir : Directive → Bool
  | .instr { operation := .MOVK .., .. } => true
  | _ => false

def isLdrPoolDir : Directive → Bool
  | .instr { operation := .LDR _ (.lit (.pool _)), .. } => true
  | _ => false

def isOrrImmDir : Directive → Bool
  | .instr { operation := .ORR_i .., .. } => true
  | _ => false

def isSubZrDir : Directive → Bool
  | .instr { operation := .SUB_s _ (.low .XZR _) _, .. } => true
  | _ => false

def isAddImmDir : Directive → Bool
  | .instr { operation := .ADD_e .., .. } => true
  | _ => false

def isSubImmDir : Directive → Bool
  | .instr { operation := .SUB_e .., .. } => true
  | _ => false

def isAddsImmDir : Directive → Bool
  | .instr { operation := .ADDS_e .., .. } => true
  | _ => false

def isSubsImmDir : Directive → Bool
  | .instr { operation := .SUBS_e .., .. } => true
  | _ => false

def isUbfmZext8Dir : Directive → Bool
  | .instr { operation := .UBFM _ _ 0 7, .. } => true
  | _ => false

def isUbfmZext16Dir : Directive → Bool
  | .instr { operation := .UBFM _ _ 0 15, .. } => true
  | _ => false

def isExt32Dir : Directive → Bool
  | .instr { operation := .UBFM _ _ 0 7, .. }
  | .instr { operation := .SBFM _ _ 0 7, .. }
  | .instr { operation := .UBFM _ _ 0 15, .. }
  | .instr { operation := .SBFM _ _ 0 15, .. } => true
  | _ => false

def isArmAddSubOrPoolDir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  !(s.startsWith "add sp," || s.startsWith "sub sp,") &&
    (s.startsWith "add " || s.startsWith "sub " || s.contains '=')

def isArmAddSubShlOrPoolDir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  !(s.startsWith "add sp," || s.startsWith "sub sp," || s.endsWith ", #0") &&
    (s.startsWith "add " || s.startsWith "sub " || s.startsWith "lsl " || s.contains '=')

def isArmSibDir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  (s.startsWith "ldr" || s.startsWith "str") &&
    (s.contains ", lsl #1" || s.contains ", lsl #2" || s.contains ", lsl #3")

def isArmOrrWOrUbfmDir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  s.startsWith "orr w" || s.startsWith "ubfm"

def isArmSext32Dir (d : armTarget.toIsa.Directive) : Bool :=
  let s := Kraken.AArch64.Print.directive d
  s.startsWith "sbfm x" && s.contains ", #0, #31"

end LeanQbeTest.T.Arm64DirPreds
