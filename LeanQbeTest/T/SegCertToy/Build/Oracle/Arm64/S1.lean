module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S1

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def hint_toy_inc : armIsa.Hints :=
  {
    dest := (.node none (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty) .empty),
    deadFlags := (.node (some true) (.node (some true) .empty .empty) .empty) }
@[expose] def ext_toy_inc : List (SigEntry × Nat) :=
  []

@[expose] def hint_toy_helper1 : armIsa.Hints :=
  {
    dest := (.node
      none
      (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty)
      (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty)),
    deferLea := (.node (some true) .empty .empty),
    deadFlags := (.node
      (some true)
      (.node (some true) .empty .empty)
      (.node (some true) .empty .empty)) }
@[expose] def ext_toy_helper1 : List (SigEntry × Nat) :=
  []

@[expose] def hints : List armIsa.Hints :=
  [hint_toy_inc, hint_toy_helper1]

@[expose] def ext : List (SigEntry × Nat) :=
  []

end LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S1
