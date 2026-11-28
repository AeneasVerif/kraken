/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Inline
public import LeanQbe.T.Opt

/-!
# Plan-Driven Acyclic Inlining (`InlinePlan`)

Additive leaf replacing the global sequential inline policy fold (`Module.optInlinePolicy`) with
an untrusted per-caller `InlPlan := List (Sym × List Sym)`.

* `planFor`: look up the ordered callee-name list for a caller symbol.
* `lookupFnByName`: look up a prior inlined callee by symbol name.
* `selectPlanCands`: resolve `planFor` names against accumulated candidates.
* `inlineFnsPlan` / `inlineFnsPlanCands`: single-pass callee-first inlining with per-function
  `Fn.renorm` so every candidate pushed onto `cands` is already a flat `denoteFunc`-backed `Fn`.
* `Module.inlinePlan`: whole-module plan-driven inlining + renormalization.
* `policyToInlPlan`: pure oracle extracting the exact `InlPlan` reproducing `Module.inlinePolicy`
  / `selectCandsForCaller` decisions for asm-SHA parity.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Untrusted per-caller inline plan mapping each caller symbol to ordered callee symbols. -/
abbrev InlPlan := List (Sym × List Sym)

/-- Look up the ordered list of callee symbols to inline into `caller` (`[]` if absent). -/
@[expose] def planFor : InlPlan → Sym → List Sym
  | [], _ => []
  | (k, cs) :: rest, caller => if k == caller then cs else planFor rest caller

/-- Look up a candidate function by symbol name (returns the most recent matching entry). -/
@[expose] def lookupFnByName : List Fn → Sym → Option Fn
  | [], _ => none
  | fn :: rest, nm => if fn.name == nm then some fn else lookupFnByName rest nm

/-- Resolve `plan`'s callee names for `caller` against accumulated `cands`. -/
@[expose] def selectPlanCands (plan : InlPlan) (cands : List Fn) (caller : Sym) : List Fn :=
  (planFor plan caller).filterMap (lookupFnByName cands)

/-- Callee-first plan-driven inliner with per-function `Fn.renorm`, keeping every pushed candidate
materialized as a flat `denoteFunc`-backed `Fn`. -/
@[expose] def inlineFnsPlan (plan : InlPlan) : List Fn → List Fn → List Fn
  | _, [] => []
  | cands, fn :: rest =>
      let cs := selectPlanCands plan cands fn.name
      let fn' := (fn.inline cs).renorm
      fn' :: inlineFnsPlan plan (fn' :: cands) rest

/-- Candidate list accumulated by `inlineFnsPlan` after processing a function list. -/
@[expose] def inlineFnsPlanCands (plan : InlPlan) : List Fn → List Fn → List Fn
  | cands, [] => cands
  | cands, fn :: rest =>
      let cs := selectPlanCands plan cands fn.name
      let fn' := (fn.inline cs).renorm
      inlineFnsPlanCands plan (fn' :: cands) rest

/-- Run plan-driven acyclic inlining + renormalization on `M`, preserving function order,
signatures, `externs`, `exits`, `sigs`, and `namesNodup`. -/
@[expose] def Module.inlinePlan (M : Module) (plan : InlPlan) : Module :=
  { M with fns := inlineFnsPlan plan [] M.fns }

/-- All callee symbols referenced by `plan` for callers in `fns`. -/
@[expose] def planTargetsFor (plan : InlPlan) (fns : List Fn) : List Sym :=
  fns.flatMap fun fn => planFor plan fn.name

/-- Deduplicated callee symbols defined in `segNames` that are targeted by callers outside
`segNames` under `plan`. -/
@[expose] def planExportsFor (plan : InlPlan) (segNames : List Sym) : List Sym :=
  let extTargets := plan.flatMap fun (caller, callees) =>
    if segNames.contains caller then [] else callees
  segNames.filter fun nm => extTargets.contains nm

/-- Tail-like helper extracting the exact `InlPlan` corresponding to `inlineFnsPolicy`'s
`selectCandsForCaller` choices (pruned to callees actually called by each caller). -/
@[expose] def policyToInlPlanAux (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat)) (extSigs : List SigEntry) (exits : List Sym) :
    List SigEntry → List Fn → List Fn → InlPlan
  | _, _, [] => []
  | seenSigs, cands, fn :: rest =>
      let candsFn := selectCandsForCaller policy cands fn
      let callerCalls :=
        exprCallSites [] (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))
      let chosen := (candsFn.filter fun c => lookupCallSite callerCalls c.name > 0).map Fn.name
      let fn' := fn.inline candsFn
      let allowed := seenSigs ++ extSigs
      let sites := lookupCallSite siteCounts fn'.name
      let loopSites := lookupCallSite loopCounts fn'.name
      let cands' :=
        if inlineCandidateOkPolicy policy sites loopSites allowed exits fn' then
          fn' :: cands
        else
          cands
      let restPlan := policyToInlPlanAux policy siteCounts loopCounts extSigs exits
        (seenSigs ++ [fn.sig]) cands' rest
      if chosen.isEmpty then restPlan else (fn.name, chosen) :: restPlan

/-- Compute the exact `InlPlan` reproducing `Module.inlinePolicy` / `Module.optInlinePolicy`
decisions on `M` (used by the untrusted oracle to preserve asm-SHA parity). -/
@[expose] def policyToInlPlan (policy : InlinePolicy) (M : Module) : InlPlan :=
  let needSites := policy.singleSiteMax > 0 || policy.maxTotalDup > 0
  let siteCounts := if needSites then fnsCallSites M.fns else []
  let loopCounts := if policy.requireLoopSite then fnsLoopCallSites M.fns else []
  policyToInlPlanAux policy siteCounts loopCounts
    (M.externs.map Extern.sig) M.exits [] [] M.fns

end LeanQbe.T
