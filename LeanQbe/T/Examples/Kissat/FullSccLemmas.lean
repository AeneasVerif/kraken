module

public import LeanQbe.T.Examples.Kissat.FullSccLemmas1
public import LeanQbe.T.Examples.Kissat.FullSccLemmas2

/-!
# Kissat `D-Full` Tarjan SCC `Func.wp` Proofs (`Stage 4`, Hub)

Public import hub re-exporting the `2` Tarjan SCC `Func.wp` theorems (`Full3.lean` #24–25;
substitution fns #26–29 split to `FullSubstLemmas`):
- `FullSccLemmas1`: `FullSccSpecs` (`fullTarjanSccSpec` matches `FullSpec3.fullTarjanSccSpec`
  by `rfl`), scoped `FullSccTactics`, BIG implication-graph & `TarjanDfsInv` helpers, and
  `full_tarjan_pop_scc_wp` (`Full3.lean` #24).
- `FullSccLemmas2`: Tarjan DFS pure transition lemmas and `full_tarjan_scc_wp` (`Full3.lean` #25).
-/
