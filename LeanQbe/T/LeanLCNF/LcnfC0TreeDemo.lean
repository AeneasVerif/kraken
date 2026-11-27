module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.LeanLCNF.LcnfC0Full
public import LeanQbe.T.LinkBudgetLfp
meta import Lean
meta import LeanQbe.T.LeanLCNF.Basic
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.Frontend.C0.Elab

/-!
# Verified Non-Linear Binary-Tree Structural Recursion `LCNF` Demo (`LcnfC0TreeDemo`)

Pure data/IR module (`0` proof imports, `0` target-arch imports) extracting two-branch structurally
recursive Lean 4 `Tree` functions via `lcnf_of_lean!` and `splice_lcnf_tflat_scc!` for linking
onto `rtC0CoreMod` via `compile_linked_budget_scc!`:

* `TreeDemo.treeSum`: `match t with | .leaf => 0 | .node v l r => v + treeSum l + treeSum r`,
  lowering to a genuine two-branch non-tail self-recursive `.call` SCC with live-across-call
  tagged-scalar (`v`, `vl`) and heap-pointer (`r`) registers, calling runtime `lcnf_nat_slow` and
  `lcnf_dec_ref_cold`.
* `TreeDemo.treeSize`: `match t with | .leaf => 0 | .node _ l r => 1 + treeSize l + treeSize r`,
  lowering to a second independent two-branch self-recursive `.call` SCC.
* Shared exact dual-arch stack budget parameters (`maxFrame = 48`, `minEntry = 272`, depth
  `D = 16`, `exportBound = 272 + 16 * 48 = 1040 ≤ 2048`), exact on both `x64Target` and
  `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

namespace TreeDemo

/-- Binary tree of natural numbers (`leaf = 1#64`, `node` = 32-byte tag-1 constructor). -/
inductive Tree where
  | leaf : Tree
  | node (v : Nat) (l r : Tree) : Tree
  deriving Repr, DecidableEq

/-- Height (maximum root-to-leaf path length) of a `Tree`. -/
@[expose] def Tree.depth : Tree → Nat
  | .leaf => 0
  | .node _ l r => 1 + max l.depth r.depth

/-- Two-branch structural sum of all node values in a `Tree`. -/
@[expose] def treeSum : Tree → Nat
  | .leaf => 0
  | .node v l r => v + treeSum l + treeSum r

/-- Two-branch structural node count of a `Tree`. -/
@[expose] def treeSize : Tree → Nat
  | .leaf => 0
  | .node _ l r => 1 + treeSize l + treeSize r

end TreeDemo

/-- Extract impure LCNF via `readLcModule`, lower via `lowerModule`, and splice cyclic/SCC
`TFlatFn`s into exposed kernel definitions (without topological acyclicity rejection). -/
local elab "splice_lcnf_tflat_scc! " modId:ident "[" roots:ident,* "]" : command => do
  let ns ← Lean.getCurrNamespace
  let outNm := ns ++ modId.getId
  let rs ← Lean.Elab.Command.liftTermElabM <| roots.getElems.toList.mapM fun r =>
    Lean.resolveGlobalConstNoOverload r.raw
  let lcMod ← Lean.Elab.Command.liftCoreM <| readLcModule modId.getId.toString rs
  let tfs ← match lowerModule lcMod with
    | .ok tfs => pure tfs
    | .error e => throwError "splice_lcnf_tflat_scc!: {e}"
  for tf in tfs do
    if !tf.flat.wfCheck (pushTypes tf.as []) [] then
      throwError "splice_lcnf_tflat_scc!: wfCheck failed for {tf.name}"
  let mut fnNames : List Lean.Name := []
  let c0TfConst := Lean.mkConst ``LeanQbe.T.Frontend.C0.TFlatFn
  for (tf, i) in tfs.zip (List.range tfs.length) do
    let e ← match LeanQbe.T.Bootstrap0.spliceTFlatFn tf with
      | .ok e => pure e
      | .error err => throwError "splice_lcnf_tflat_scc!: {err}"
    let nm := outNm ++ Lean.Name.mkSimple s!"tf_{i}"
    Lean.Elab.Command.liftCoreM <|
      LeanQbe.T.Frontend.C0.addExposedDecl nm c0TfConst e (forceExpose := true)
    fnNames := fnNames ++ [nm]
  let tfsTy := Lean.mkApp (Lean.mkConst ``List [.zero]) c0TfConst
  let tfsVal := (fnNames.map Lean.mkConst).foldr
    (fun e acc => Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) c0TfConst e acc)
    (Lean.mkApp (Lean.mkConst ``List.nil [.zero]) c0TfConst)
  Lean.Elab.Command.liftCoreM <|
    LeanQbe.T.Frontend.C0.addExposedDecl outNm tfsTy tfsVal (forceExpose := true)

lcnf_of_lean! treeDemoLcMod [TreeDemo.treeSum, TreeDemo.treeSize]

splice_lcnf_tflat_scc! treeDemoTfs [TreeDemo.treeSum, TreeDemo.treeSize]

lcnf_lower_thm! treeDemoTfs treeDemoLcMod

/-- Mangled symbol name of `TreeDemo.treeSum`. -/
@[expose] def treeDemoSumName : Sym :=
  "l_LeanQbe_T_LeanLCNF_TreeDemo_treeSum"

/-- Mangled symbol name of `TreeDemo.treeSize`. -/
@[expose] def treeDemoSizeName : Sym :=
  "l_LeanQbe_T_LeanLCNF_TreeDemo_treeSize"

/-- Lowered `LeanQbe.T.Fn` of `TreeDemo.treeSum`. -/
@[expose] def treeDemoSumFn : Fn :=
  treeDemoTfs.tf_0.toFn

/-- Lowered `LeanQbe.T.Fn` of `TreeDemo.treeSize`. -/
@[expose] def treeDemoSizeFn : Fn :=
  treeDemoTfs.tf_1.toFn

/-- Exact compiled single-frame cost (`effFrame + raBytes = 48`) for both `treeSum` and
`treeSize` on both x86-64 and AArch64. -/
@[expose] def treeDemoMaxFrame : Nat := 48

/-- Exact entry headroom (`48 + max(224, 112) = 272`) covering `lcnf_nat_slow` and
`lcnf_dec_ref_cold` on both x86-64 and AArch64. -/
@[expose] def treeDemoMinEntry : Nat := 272

/-- Certified maximum binary-tree recursion depth (`D = 16`, up to `2^16 - 1` nodes). -/
@[expose] def treeDemoDepthBudget : Nat := 16

/-- Exported stack bound at depth `D = 16`: `272 + 16 * 48 = 1040 ≤ 2048`. -/
@[expose] def treeDemoExportBound : Nat :=
  treeDemoMinEntry + treeDemoDepthBudget * treeDemoMaxFrame

/-- Exported per-symbol stack bounds for `compile_linked_budget_scc!`. -/
@[expose] def treeDemoExportBounds : List (Sym × Nat) :=
  [(treeDemoSumName, treeDemoExportBound), (treeDemoSizeName, treeDemoExportBound)]

/-- `BudgetFn` descriptor for `TreeDemo.treeSum`. -/
@[expose] def treeDemoSumBudgetFn : BudgetFn :=
  { toFn := treeDemoSumFn, maxFrame := treeDemoMaxFrame, minEntry := treeDemoMinEntry }

/-- `BudgetFn` descriptor for `TreeDemo.treeSize`. -/
@[expose] def treeDemoSizeBudgetFn : BudgetFn :=
  { toFn := treeDemoSizeFn, maxFrame := treeDemoMaxFrame, minEntry := treeDemoMinEntry }

/-- Standalone user `BudgetModule` (`2` independent `.recBudgetSCC` chunks) for
`compile_linked_budget_scc!`. -/
@[expose] def treeDemoBudgetMod : BudgetModule :=
  { fns := [treeDemoSumBudgetFn, treeDemoSizeBudgetFn], externs := [], exits := rtExitSyms }

/-- Standalone user `Module` containing the lowered two-branch recursive `treeSum` & `treeSize`. -/
@[expose] def treeDemoProgMod : Module :=
  { fns := Frontend.C0.tflatFnsToFns treeDemoTfs, externs := [], exits := rtExitSyms }

/-- Full `88`-function linked `Module`: `rtC0CoreMod` (`86` fns) ++ `treeDemoProgMod` (`2` fns). -/
@[expose] def treeDemoLinkedMod : Module :=
  linkLcnfWithRtC0 treeDemoTfs false

end LeanQbe.T.LeanLCNF
