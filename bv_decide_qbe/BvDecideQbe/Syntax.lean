module

public import Std.Tactic.BVDecide
public import BvDecideQbe.Config
public import BvDecideQbe.NormalizeTheorems

/-!
# Lightweight Syntax & Macros for `bv_decide_qbe` and `bv_cut_qbe`

Pure `Init` + `Std.Tactic.BVDecide` syntax declarations kept free of `Lean.*` imports so both
`BvDecideQbe.Tactic` (lean user entrypoint) and `BvDecideQbe.TacticImpl` (precompiled plugin
elaborators) can share the exact syntax node kinds without circularity or `.olean` bloat.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Parser.Tactic

/-- Trust-pure `BitVec` decision tactic backed by `BVP1` + verified `KissatFidelity`
+ kernel `rfl`. -/
syntax (name := bvDecideQbeStx) "bv_decide_qbe" optConfig (bvTypes)? : tactic

/-- Upstream-fidelity `bv_decide_qbe` alias (disables `D1–D8`, keeping only `D0`). -/
macro (name := bvDecideQbeUpstreamStx) "bv_decide_qbe_upstream"
    cfg:optConfig types:(bvTypes)? : tactic => do
  let `(Lean.Parser.Tactic.optConfig| $items:configItem*) := cfg | Macro.throwUnsupported
  `(tactic| bv_decide_qbe $items* (mode := .upstream) $[$types]?)

/-- Trust-pure `BitVec` decision tactic in `sym =>` and `grind =>` mode. -/
syntax (name := bvDecideQbeGrindStx) "bv_decide_qbe" optConfig (bvTypes)? : grind

/-- Upstream-fidelity `bv_decide_qbe` alias in `sym =>` and `grind =>` mode. -/
macro (name := bvDecideQbeUpstreamGrindStx) "bv_decide_qbe_upstream"
    cfg:optConfig types:(bvTypes)? : grind => do
  let `(Lean.Parser.Tactic.optConfig| $items:configItem*) := cfg | Macro.throwUnsupported
  `(grind| bv_decide_qbe $items* (mode := .upstream) $[$types]?)

/-- Incremental pre-processor for `bv_decide_qbe` in `sym =>` and `grind =>` mode. -/
syntax (name := bvDecideQbePushStx) "bv_decide_qbe_push" optConfig : grind

/-- Zero-new-trust cutpoint-equivalence & ring-dispatch tactic (`E0 / H5a + H6a + H7`).
Supports automatic pre-inlining cut discovery (`bv_cut_qbe`) and explicit cutpoint lists
(`bv_cut_qbe [e1 = e2, ...]`). -/
syntax (name := bvCutQbeStx) "bv_cut_qbe" optConfig ("[" term,* "]")? (bvTypes)? : tactic

end BvDecideQbe
