module

public import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7

/-!
# Source Verification and Axiom Audit (`FullM7`, `410/410`)

1. Executable `#guard` checks on `m7Fns` (`410` functions, unique names) and `m7Module`
   (`checkAcyclic = true`, empty externs/exits, `410` signatures).
2. Root-namespace audit theorems for `FullM7.m7Fns_wf` and `FullM7.m7_acyclic` with
   single-line `#print axioms` checks (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7SourceTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM7

#guard m7Fns.length == 410
#guard (m7Fns.map Fn.name).eraseDups.length == 410
#guard m7Module.checkAcyclic == true
#guard m7Module.externs.isEmpty && m7Module.exits.isEmpty
#guard m7Module.sigs.length == 410

theorem m7_wf : ∀ f ∈ m7Fns, f.Wf := m7Fns_wf

theorem m7_acyc : m7Module.checkAcyclic = true := m7_acyclic

end LeanQbeTest.T.KissatM7SourceTest

abbrev m7src_wf := @LeanQbeTest.T.KissatM7SourceTest.m7_wf
abbrev m7src_acyc := @LeanQbeTest.T.KissatM7SourceTest.m7_acyc

#print axioms m7src_wf
#print axioms m7src_acyc
