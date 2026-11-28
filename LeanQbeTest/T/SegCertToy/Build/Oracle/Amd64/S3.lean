module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S3

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def hint_toy_step3 : x64Isa.Hints :=
  {
    dest := (.node none (.node (some (.gpr Reg64.rax)) .empty .empty) .empty),
    pre := (.node
      (some { clearFlags := false, moves := [(.mov Reg64.rax Reg64.rdi)] })
      .empty
      .empty),
    deadFlags := (.node (some true) (.node (some true) .empty .empty) .empty) }
@[expose] def ext_toy_step3 : List (SigEntry × Nat) :=
  []

@[expose] def hint_toy_main : x64Isa.Hints :=
  {
    dest := (.node
      none
      .empty
      (.node none (.node (some (.gpr Reg64.rax)) .empty .empty) .empty)),
    pre := (.node
      (some { clearFlags := false, moves := [(.st 0 Reg64.rdi)] })
      (.node
        (some { clearFlags := false, moves := [(.mov Reg64.rbx Reg64.rax)] })
        .empty
        .empty)
      .empty),
    deadFlags := (.node
      (some true)
      (.node (some true) (.node (some true) .empty .empty) .empty)
      (.node (some true) .empty .empty)),
    nslots := 1,
    saved := [Reg64.rbx] }
@[expose] def ext_toy_main : List (SigEntry × Nat) :=
  [(("toy_mix2", [i64, i64], [i64]), 16), (("toy_step3", [i64], [i64]), 0)]

@[expose] def hints : List x64Isa.Hints :=
  [hint_toy_step3, hint_toy_main]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("toy_mix2", [i64, i64], [i64]), 16)]

end LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S3
