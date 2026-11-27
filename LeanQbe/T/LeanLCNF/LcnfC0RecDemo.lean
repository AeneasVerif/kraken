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
# Verified Structurally Recursive Lean `LCNF` Demo Program (`LcnfC0RecDemo`)

Pure data/IR module (`0` proof imports, `0` target-arch imports) extracting a structurally
recursive Lean 4 `List Nat` function via `lcnf_of_lean!` and `splice_lcnf_tflat_scc!` for
linking onto `rtC0CoreMod` via `compile_linked_budget_scc!`:

* `RecDemo.listSum`: `match xs with | [] => 0 | x :: rest => x + listSum rest`, lowering to a
  genuine non-tail self-recursive `.call` SCC calling runtime `lcnf_nat_slow` and
  `lcnf_dec_ref_cold`.
* Shared dual-arch stack budget parameters (`maxFrame = 32`, `minEntry = 256`, depth `D = 16`,
  `exportBound = 256 + 16 * 32 = 768 ≤ 2048`), exact on both `x64Target` and `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

namespace RecDemo

@[expose] def listSum : List Nat → Nat
  | [] => 0
  | x :: rest => x + listSum rest

end RecDemo

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

lcnf_of_lean! recDemoLcMod [RecDemo.listSum]

splice_lcnf_tflat_scc! recDemoTfs [RecDemo.listSum]

lcnf_lower_thm! recDemoTfs recDemoLcMod

/-- Mangled symbol name of `RecDemo.listSum`. -/
@[expose] def recDemoListSumName : Sym :=
  "l_LeanQbe_T_LeanLCNF_RecDemo_listSum"

/-- Lowered `LeanQbe.T.Fn` of `RecDemo.listSum`. -/
@[expose] def recDemoListSumFn : Fn :=
  recDemoTfs.tf_0.toFn

/-- Exact compiled single-frame cost (`effFrame + raBytes = 32`) on both x86-64 and AArch64. -/
@[expose] def recDemoMaxFrame : Nat := 32

/-- Exact entry headroom (`32 + max(224, 112) = 256`) covering `lcnf_nat_slow` and
`lcnf_dec_ref_cold` on both x86-64 and AArch64. -/
@[expose] def recDemoMinEntry : Nat := 256

/-- Certified maximum `List Nat` recursion depth (`D = 16`). -/
@[expose] def recDemoDepthBudget : Nat := 16

/-- Exported stack bound for `listSum` at depth `D = 16`: `256 + 16 * 32 = 768 ≤ 2048`. -/
@[expose] def recDemoExportBound : Nat :=
  recDemoMinEntry + recDemoDepthBudget * recDemoMaxFrame

/-- `BudgetFn` descriptor for `RecDemo.listSum`. -/
@[expose] def recDemoListSumBudgetFn : BudgetFn :=
  { toFn := recDemoListSumFn, maxFrame := recDemoMaxFrame, minEntry := recDemoMinEntry }

/-- Standalone user `BudgetModule` for `compile_linked_budget_scc!`. -/
@[expose] def recDemoBudgetMod : BudgetModule :=
  { fns := [recDemoListSumBudgetFn], externs := [], exits := rtExitSyms }

/-- Standalone user `Module` containing the lowered structurally recursive `listSum` function. -/
@[expose] def recDemoProgMod : Module :=
  { fns := Frontend.C0.tflatFnsToFns recDemoTfs, externs := [], exits := rtExitSyms }

/-- Full `81`-function linked `Module`: `rtC0CoreMod` (`80` fns) ++ `recDemoProgMod` (`1` fn). -/
@[expose] def recDemoLinkedMod : Module :=
  linkLcnfWithRtC0 recDemoTfs false

end LeanQbe.T.LeanLCNF
