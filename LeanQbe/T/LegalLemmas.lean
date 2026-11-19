module

public import LeanQbe.T.LegalWfBaseLemmas
public import LeanQbe.T.LegalWfOpsLemmas
public import LeanQbe.T.LegalWpBaseLemmas
public import LeanQbe.T.LegalWpSimdLemmas
public import LeanQbe.T.LegalOpWpLemmas1
public import LeanQbe.T.LegalOpWpLemmas2
public import LeanQbe.T.LegalMemLemmas

/-!
# Correctness proofs facade for `LeanQbe.T.Legal` (`T5`, `G13`)

Re-exports `LegalWfBaseLemmas`, `LegalWfOpsLemmas`, `LegalWpBaseLemmas`, `LegalWpSimdLemmas`,
`LegalOpWpLemmas1`, `LegalOpWpLemmas2`, and `LegalMemLemmas`:
* `Func.legal_wf` / `Fn.legal_wf`: well-formedness preservation;
* `Func.legal_wp` / `Func.legal_spec` / `Fn.legal_spec`: semantic preservation.
-/
