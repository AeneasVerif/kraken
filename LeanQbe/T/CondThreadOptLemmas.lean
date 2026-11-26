module

public import LeanQbe.T.CondThreadOptLemmas0
public import LeanQbe.T.CondThreadOptLemmas1
public import LeanQbe.T.CondThreadOptLemmas2

/-!
# Soundness Proofs for `CondThreadOpt`

Proves relational well-formedness (`*_wf`), weakest-precondition semantics preservation (`*_spec`
and `condThread_ok`), and call/exit well-scopedness (`*_callsOk`) for:

* `Func.pathCondOpt` (lexical identity tracking, symbolic `zext`/`sext` keys, comparison
  implication tables `cmpImplies` / `cmpConstImplies` / `factImpliesCmpBits`, and dominating edge
  fact refutation),
* `Func.condThreadWithPlan` / `Func.condThreadPass` (verified `validateCTPlan` + bool-parameter
  splitting and depth-1 bounded constant-arg head threading),
* Combined entrypoints `Func.condThreadOpt`, `condThread_ok`, `Fn.condThreadOpt`, and
  `Func.condThreadLateOpt`.
-/

set_option autoImplicit false
