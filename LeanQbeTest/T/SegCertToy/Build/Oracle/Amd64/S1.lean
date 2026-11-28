module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S1

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def hint_toy_inc : x64Isa.Hints :=
  {
    dest := (.node none (.node (some (.gpr Reg64.rax)) .empty .empty) .empty),
    pre := (.node
      (some { clearFlags := false, moves := [(.mov Reg64.rax Reg64.rdi)] })
      .empty
      .empty),
    deadFlags := (.node (some true) (.node (some true) .empty .empty) .empty) }
@[expose] def ext_toy_inc : List (SigEntry × Nat) :=
  []

@[expose] def hint_toy_helper1 : x64Isa.Hints :=
  {
    dest := (.node
      none
      (.node (some (.gpr Reg64.rax)) .empty .empty)
      (.node (some (.gpr Reg64.rax)) .empty .empty)),
    pre := (.node
      (some { clearFlags := false, moves := [(.mov Reg64.rax Reg64.rdi)] })
      .empty
      .empty),
    deferLea := (.node (some true) .empty .empty),
    deadFlags := (.node
      (some true)
      (.node (some true) .empty .empty)
      (.node (some true) .empty .empty)) }
@[expose] def ext_toy_helper1 : List (SigEntry × Nat) :=
  []

@[expose] def hints : List x64Isa.Hints :=
  [hint_toy_inc, hint_toy_helper1]

@[expose] def ext : List (SigEntry × Nat) :=
  []

end LeanQbeTest.T.SegCertToy.Build.Oracle.Amd64.S1
