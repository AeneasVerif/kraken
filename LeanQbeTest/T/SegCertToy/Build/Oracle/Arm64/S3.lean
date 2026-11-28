module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S3

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def hint_toy_step3 : armIsa.Hints :=
  {
    dest := (.node none (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty) .empty),
    deadFlags := (.node (some true) (.node (some true) .empty .empty) .empty) }
@[expose] def ext_toy_step3 : List (SigEntry × Nat) :=
  []

@[expose] def hint_toy_main : armIsa.Hints :=
  {
    dest := (.node
      none
      .empty
      (.node none (.node (some (.gpr (XRegOrSp.reg (XReg.X0)))) .empty .empty) .empty)),
    pre := (.node
      (some { clearFlags := false, moves := [(.st 0 (XRegOrSp.reg (XReg.X0)))] })
      (.node
        (some { clearFlags := false, moves := [(.st 1 (XRegOrSp.reg (XReg.X0)))] })
        .empty
        .empty)
      (.node
        (some { clearFlags := false, moves := [(.ld (XRegOrSp.reg (XReg.X1)) 1)] })
        .empty
        .empty)),
    deadFlags := (.node
      (some true)
      (.node (some true) (.node (some true) .empty .empty) .empty)
      (.node (some true) .empty .empty)),
    nslots := 2 }
@[expose] def ext_toy_main : List (SigEntry × Nat) :=
  [(("toy_mix2", [i64, i64], [i64]), 16), (("toy_step3", [i64], [i64]), 0)]

@[expose] def hints : List armIsa.Hints :=
  [hint_toy_step3, hint_toy_main]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("toy_mix2", [i64, i64], [i64]), 16)]

end LeanQbeTest.T.SegCertToy.Build.Oracle.Arm64.S3
