module

public import LeanQbe.T.RegaLemmas4

/-!
# `T7b` facade: correctness of the PHOAS-first checked lowering

Re-exports `RegaLemmas1`–`RegaLemmas4`. Headline theorems (namespace `LeanQbe.T.Rega`):
* `lowerFn_correct : f.Wf → lowerFn T.toIsa hints E f = .ok code → code.IsInfixAt .. k₀ →
  T.LabelsUnique host → … → T.FnSpec host f.name (Func.spec Γ f.body) n nX`;
* `lowerFn_labelsUnique : LabelClean I → lowerFn I hints E f = .ok code →` labels of `code`
  occur at pairwise-distinct positions (structural, Guardrail 5);
* `lowerFn_label_mem`: every label of `code` is `f.name` or `lname f.name j`.
-/

set_option autoImplicit false
