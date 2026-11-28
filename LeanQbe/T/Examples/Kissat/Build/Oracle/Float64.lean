module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Float64

open LeanQbe.T

@[expose] def plan : InlPlan := [
  ("f64u_round_pack", ["f64u_msb64"]),
  ("f64u_add", ["f64u_round_pack"]),
  ("f64u_sub", ["f64u_round_pack"]),
  ("f64u_mul", ["f64u_msb64", "f64u_round_pack"]),
  ("f64u_div", ["f64u_msb64", "f64u_round_pack"]),
  ("f64u_inv_u64", ["f64u_msb64", "f64u_round_pack"]),
  ("f64u_from_u64", ["f64u_msb64"]),
  ("f64u_log10_u64", ["u64_mul128", "f64u_msb64", "f64u_round_pack"]),
  ("f64u_nlogpown", ["f64u_from_u64"])
]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Float64
