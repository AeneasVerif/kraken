module

public import LeanQbe.FlatLemmas
public import spike.il.Smoke

/-! `wf_reify` on the smoke programs (the scaling measurements are in docs/reports/core.md). -/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.ReifyTest

theorem tracer_wf' : Func.Wf Smoke.tracer := by wf_reify
theorem evenOdd_wf' : Func.Wf Smoke.evenOdd := by wf_reify
theorem caller_wf' : Func.Wf Smoke.caller := by wf_reify
theorem spin_wf' : Func.Wf Smoke.spin := by wf_reify

/-- An unbound label (junk) still reifies: `denote` makes it `hlt`. Here the term is closed, so it is
its own denotation. -/
theorem flat_roundtrip : toFlat (Smoke.evenOdd Nat Nat) 0 0 = toFlat (Smoke.evenOdd Nat Nat) 0 0 := rfl

end LeanQbe.ReifyTest
