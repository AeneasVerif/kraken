module

public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas2
public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas3

/-!
# Kissat `D-Full` Parse/Init `Func.wp` Proofs Hub (`Stage 4`, `10` fns)

Re-exports parametric `(Γ : Env)` `Func.wp` theorems for all `10` owned `Full1.lean` init,
sizing, and zeroing functions (UNSAT-only, strictly scoped tactics):
- Sizing & header setup (`FullParseInitLemmas2`): `full_fixed_bytes_wp`,
  `full_calc_ext_cap_wp`, `full_calc_scr_cap_wp`, `full_calc_max_v_wp`,
  `full_init_ptrs_wp`, `full_init_hdr_wp`, `full_init_arenas_wp`
- Array zeroing & state construction (`FullParseInitLemmas3`): `full_zero_tables1_wp`,
  `full_zero_tables2_wp`, `full_init_state_wp`.
-/
