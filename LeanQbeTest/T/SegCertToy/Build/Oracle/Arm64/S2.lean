module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def hint_toy_add_inc : armIsa.Hints :=
  {
    dest := (.node
      none
      (.node none (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty) .empty)
      (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty)),
    deferLea := (.node (some true) .empty .empty),
    deadFlags := (.node
      (some true)
      (.node (some true) .empty .empty)
      (.node (some true) .empty .empty)) }
@[expose] def ext_toy_add_inc : List (SigEntry × Nat) :=
  []

@[expose] def hint_toy_mix2 : armIsa.Hints :=
  {
    dest := (.node
      none
      (.node
        none
        (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty)
        (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty))
      (.node none (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty) .empty)),
    pre := (.node
      (some { clearFlags := false, moves := [(.st 0 (XRegOrSp.reg (XReg.X1)))] })
      .empty
      (.node
        (some { clearFlags := false, moves := [(.ld (XRegOrSp.reg (XReg.X1)) 0)] })
        .empty
        .empty)),
    deferLea := (.node
      none
      (.node (some true) .empty .empty)
      (.node (some true) .empty .empty)),
    deadFlags := (.node
      (some true)
      (.node (some true) (.node (some true) .empty .empty) .empty)
      (.node (some true) (.node (some true) .empty .empty) .empty)),
    nslots := 1 }
@[expose] def ext_toy_mix2 : List (SigEntry × Nat) :=
  [(("toy_helper1", [i64], [i64]), 0)]

@[expose] def hints : List armIsa.Hints :=
  [hint_toy_add_inc, hint_toy_mix2]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("toy_helper1", [i64], [i64]), 0)]

end LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S2
