module

public import BvDecideQbe.Tactic

/-!
# `BvDecideQbe` Root Barrel

Lightweight entrypoint re-exporting `bv_decide_qbe`, `bv_decide_qbe_upstream`,
`bv_decide_qbe_push`, `bv_cut_qbe`, `QbeMode`, and `QbeConfig` with zero `Lean.*` `.olean`
imports. Metaprogramming callers needing direct `MetaM` APIs can additionally import
`BvDecideQbe.Prover`, `BvDecideQbe.Cegar`, `BvDecideQbe.Cut`, `BvDecideQbe.NormalizeRules`,
`BvDecideQbe.TacticImpl`, or `BvDecideQbe.FFIProof`.
-/
