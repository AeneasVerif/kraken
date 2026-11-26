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
# Verified Mutually-Recursive 2-Function SCC `LCNF` Demo (`LcnfC0MutRecDemo`)

Pure data/IR module (`0` proof imports, `0` target-arch imports) extracting a genuine 2-function
mutually-recursive Lean 4 `Rose`/`Forest` program via `lcnf_of_lean!` and `splice_lcnf_tflat_scc!`
for compilation into a **single 2-function `.recBudgetSCC` chunk** via `compile_linked_budget_scc!`
and linking onto `rtC0CoreMod`:

* `MutRecDemo.roseSum`: sums a `Rose` node (`node v cs ↦ v + forestSum cs`), calling `forestSum`
  with live-across-call tagged scalar `v` and runtime `lcnf_nat_slow` / `lcnf_dec_ref_cold`.
* `MutRecDemo.forestSum`: sums a `Forest` (`nil ↦ 0`, `cons hd tl ↦ roseSum hd + forestSum tl`),
  calling both `roseSum` and `forestSum` with live-across-call `tl` and `roseSum hd`.
* Exact dual-arch stack budget parameters (`maxFrame = 48`, `minEntry = 272`, depth `D = 16`,
  `exportBound = 272 + 16 * 48 = 1040 ≤ 2048`), exact on both `x64Target` and `armTarget`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

namespace MutRecDemo

mutual
  /-- Multi-way rose tree of natural numbers (`node` = 24-byte tag-0 constructor). -/
  inductive Rose where
    | node (v : Nat) (cs : Forest) : Rose
    deriving Repr, DecidableEq

  /-- Child forest of rose trees (`nil = 1#64`, `cons` = 24-byte tag-1 constructor). -/
  inductive Forest where
    | nil : Forest
    | cons (hd : Rose) (tl : Forest) : Forest
    deriving Repr, DecidableEq
end

mutual
  /-- Mutual call-stack depth measure for `Rose`. -/
  @[expose] def roseDepth : Rose → Nat
    | .node _ cs => 1 + forestDepth cs

  /-- Mutual call-stack depth measure for `Forest`. -/
  @[expose] def forestDepth : Forest → Nat
    | .nil => 0
    | .cons hd tl => 1 + max (roseDepth hd) (forestDepth tl)
end

mutual
  /-- Mutually recursive sum of all node values in a `Rose` tree. -/
  @[expose] def roseSum : Rose → Nat
    | .node v cs => v + forestSum cs

  /-- Mutually recursive sum of all node values across a `Forest`. -/
  @[expose] def forestSum : Forest → Nat
    | .nil => 0
    | .cons hd tl => roseSum hd + forestSum tl
end

end MutRecDemo

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

lcnf_of_lean! mutRecDemoLcMod [MutRecDemo.roseSum, MutRecDemo.forestSum]

splice_lcnf_tflat_scc! mutRecDemoTfs [MutRecDemo.roseSum, MutRecDemo.forestSum]

/-- Mangled symbol name of `MutRecDemo.roseSum`. -/
@[expose] def mutRecDemoRoseName : Sym :=
  "l_LeanQbe_T_LeanLCNF_MutRecDemo_roseSum"

/-- Mangled symbol name of `MutRecDemo.forestSum`. -/
@[expose] def mutRecDemoForestName : Sym :=
  "l_LeanQbe_T_LeanLCNF_MutRecDemo_forestSum"

/-- Lowered `LeanQbe.T.Fn` of `MutRecDemo.roseSum`. -/
@[expose] def mutRecDemoRoseFn : Fn :=
  mutRecDemoTfs.tf_0.toFn

/-- Lowered `LeanQbe.T.Fn` of `MutRecDemo.forestSum`. -/
@[expose] def mutRecDemoForestFn : Fn :=
  mutRecDemoTfs.tf_1.toFn

/-- Exact compiled single-frame bound (`effFrame + raBytes ≤ 48`) for the 2-fn mutual SCC on both
x86-64 and AArch64 (`forestSum` is tight at `48`). -/
@[expose] def mutRecDemoMaxFrame : Nat := 48

/-- Exact entry headroom (`48 + max(224, 112) = 272`) covering `lcnf_nat_slow` and
`lcnf_dec_ref_cold` on both x86-64 and AArch64. -/
@[expose] def mutRecDemoMinEntry : Nat := 272

/-- Certified maximum mutual call-depth (`D = 16`). -/
@[expose] def mutRecDemoDepthBudget : Nat := 16

/-- Exported stack bound at depth `D = 16`: `272 + 16 * 48 = 1040 ≤ 2048`. -/
@[expose] def mutRecDemoExportBound : Nat :=
  mutRecDemoMinEntry + mutRecDemoDepthBudget * mutRecDemoMaxFrame

/-- Exported per-symbol stack bounds for `compile_linked_budget_scc!`. -/
@[expose] def mutRecDemoExportBounds : List (Sym × Nat) :=
  [(mutRecDemoRoseName, mutRecDemoExportBound), (mutRecDemoForestName, mutRecDemoExportBound)]

/-- `BudgetFn` descriptor for `MutRecDemo.roseSum`. -/
@[expose] def mutRecDemoRoseBudgetFn : BudgetFn :=
  { toFn := mutRecDemoRoseFn, maxFrame := mutRecDemoMaxFrame, minEntry := mutRecDemoMinEntry }

/-- `BudgetFn` descriptor for `MutRecDemo.forestSum`. -/
@[expose] def mutRecDemoForestBudgetFn : BudgetFn :=
  { toFn := mutRecDemoForestFn, maxFrame := mutRecDemoMaxFrame, minEntry := mutRecDemoMinEntry }

/-- Standalone user `BudgetModule` forming a single 2-function mutually-recursive `.recBudgetSCC`
chunk for `compile_linked_budget_scc!`. -/
@[expose] def mutRecDemoBudgetMod : BudgetModule :=
  { fns := [mutRecDemoRoseBudgetFn, mutRecDemoForestBudgetFn], externs := [], exits := rtExitSyms }

/-- Standalone user `Module` containing lowered `roseSum` & `forestSum`. -/
@[expose] def mutRecDemoProgMod : Module :=
  { fns := LeanLRC.tflatFnsToFns mutRecDemoTfs, externs := [], exits := rtExitSyms }

/-- Full `88`-function linked `Module`: `rtC0CoreMod` (`86` fns) ++ `mutRecDemoProgMod` (`2` fns).
-/
@[expose] def mutRecDemoLinkedMod : Module :=
  linkLcnfWithRtC0 mutRecDemoTfs false

end LeanQbe.T.LeanLCNF
