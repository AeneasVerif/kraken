module

public import LeanQbe.T.InlinePlan

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Oracle.S2

open LeanQbe.T

@[expose] def plan : InlPlan := [("toy_add_inc", ["toy_inc"]), ("toy_mix2", ["toy_add_inc"])]

end LeanQbeTest.T.SegCertToy.Build.Oracle.S2
