module

public import BvDecideQbe.Cegar
public import BvDecideQbe.CutCore
public import BvDecideQbe.NormalizeRules
public import Lean.Elab.Tactic.BVDecide
public import Lean.Meta.Tactic.Grind.Main
public import Lean.Meta.Tactic.Simp.Main
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Cutpoint-Equivalence Tactic `bv_cut_qbe` & Ring-Dispatch Helper (`E0 / H5a` + `H6a`)

Zero-new-trust Lean front end for cutpoint slicing and word-level ring dispatch on `BitVec`
equivalence goals (building on `BvDecideQbe.CutCore` for pre-inlining DAG extraction and
64-pattern simulation discovery):
1. **`H7` normalizer & `H6a` ring dispatch:** Applies `shiftmul`/`opt_share` without inlining
   `let`s, and discharges pure `BitVec` ring + constant-shift obligations via two-pass
   `shl → mul` + `grind` (zero solver axioms).
2. **Sound topological discharge (`H5a`):** For each candidate cut `(g, t)` in topological
   order, slices the cone back to the already-proved cut frontier, abstracts both endpoints
   `(g', t')` of earlier cuts to a shared fresh variable `v`, retains transitive cone-relevant
   side conditions, caches closed identical stage obligations, and composes kernel-checked
   proof terms (`Eq.trans` / `congrArg` / `∀`-instantiation).
3. **Fallback hygiene:** Failed automatic cuts are dropped cleanly (`nomatch`), and direct
   fallback converts deep `BitVec` `let`-DAGs to explicit equality hypotheses to avoid
   exponential `zetaDeltaAll` expansion.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Lean.Elab.Tactic.BVDecide
open Lean.Meta.Tactic.BVDecide
open Std.Tactic.BVDecide

/-! ## 1. `H7` Simp Normalizer & `H6a` Ring-Dispatch Helper -/

private def mkOnlySimpContext (ruleNames : Array Name) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in ruleNames do
    thms ← thms.addConst n
  let cfg : Simp.Config := {
    zeta := false
    zetaDelta := false
    failIfUnchanged := false
    decide := false
  }
  Simp.mkContext cfg #[thms]

/-- Apply `H7` normalizer rules (`shiftmul` + `opt_share`) to `mvarId`'s target without
inlining `let`-bindings. Returns `none` if the goal is closed (zero solver axioms). -/
def trySimpNormalizeRules (mvarId : MVarId) : MetaM (Option MVarId) := do
  let ctx ← mkOnlySimpContext NormalizeRules.normalizeRuleNames
  let (res?, _) ← Meta.simpTarget mvarId ctx (mayCloseGoal := true)
  return res?

private def isConstShiftArg (e : Expr) : Bool :=
  (getNatLit? e).isSome || (getBitVecLit? e).isSome

private partial def isRingExprAux (w : Nat) (e : Expr)
    (budget : IO.Ref Nat) (seen : IO.Ref (Std.HashSet Sym.ExprPtr))
    (hasOp : IO.Ref Bool) : MetaM Bool := do
  let rem ← budget.get
  if rem == 0 then return false
  let e := e.consumeMData
  if (← seen.get).contains ⟨e⟩ then return true
  budget.set (rem - 1)
  seen.modify (·.insert ⟨e⟩)
  if let some ⟨w', _⟩ := getBitVecLit? e then
    return w' == w
  match e with
  | .fvar fv =>
    let ldecl ← fv.getDecl
    let some w' ← getBitVecWidth? ldecl.type | return false
    if w' != w then return false
    match ldecl.value? with
    | none => return true
    | some val => isRingExprAux w val budget seen hasOp
  | .bvar _ => return true
  | _ =>
    match_expr e with
    | BitVec.twoPow wExpr kExpr =>
      return getNatLit? wExpr == some w && (getNatLit? kExpr).isSome
    | HAdd.hAdd _ _ _ _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | Add.add _ _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | BitVec.add _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | HSub.hSub _ _ _ _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | Sub.sub _ _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | BitVec.sub _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | HMul.hMul _ _ _ _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | Mul.mul _ _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | BitVec.mul _ a b =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp <&&> isRingExprAux w b budget seen hasOp
    | Neg.neg _ _ a =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp
    | BitVec.neg _ a =>
      hasOp.set true
      isRingExprAux w a budget seen hasOp
    | HShiftLeft.hShiftLeft _ _ _ _ a s =>
      if isConstShiftArg s then
        hasOp.set true
        isRingExprAux w a budget seen hasOp
      else
        return false
    | BitVec.shiftLeft _ a s =>
      if isConstShiftArg s then
        hasOp.set true
        isRingExprAux w a budget seen hasOp
      else
        return false
    | _ => return false

/-- Syntactic check: `mvarId`'s target is a concrete-width `BitVec` equality built solely from
ring operations (`+`, `-`, `*`, `neg`, constants) and constant-amount left shifts (`<<< k`). -/
def isRingCandidateGoal (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let ty := (← instantiateMVars (← mvarId.getType)).consumeMData
    let some (eqTy, lhs, rhs) := ty.eq? | return false
    let some w ← getBitVecWidth? eqTy | return false
    if w == 0 then return false
    let budget ← IO.mkRef (16384 : Nat)
    let seen ← IO.mkRef ({} : Std.HashSet Sym.ExprPtr)
    let hasOp ← IO.mkRef false
    let okL ← isRingExprAux w lhs budget seen hasOp
    if !okL then return false
    let okR ← isRingExprAux w rhs budget seen hasOp
    if !okR then return false
    return ← hasOp.get

private def hasShiftLeft (e : Expr) (maxVisits : Nat := 16384) : Bool := Id.run do
  let mut stack : Array Expr := #[e]
  let mut visited : Std.HashSet Sym.ExprPtr := {}
  let mut rem := maxVisits
  while rem > 0 && !stack.isEmpty do
    let cur := stack.back!
    stack := stack.pop
    if visited.contains ⟨cur⟩ then continue
    visited := visited.insert ⟨cur⟩
    rem := rem - 1
    match cur with
    | .const n _ =>
      if n == ``HShiftLeft.hShiftLeft || n == ``BitVec.shiftLeft then
        return true
    | .app f a => stack := stack.push a; stack := stack.push f
    | .mdata _ b | .proj _ _ b => stack := stack.push b
    | .lam _ d b _ | .forallE _ d b _ => stack := stack.push d; stack := stack.push b
    | .letE _ t v b _ => stack := stack.push t; stack := stack.push v; stack := stack.push b
    | _ => pure ()
  return false

/-- Rewrite constant left shifts `x <<< k` into `x * c#w` in two non-looping `simp` passes. -/
def rewriteConstShiftsToMul (mvarId : MVarId) : MetaM (Option MVarId) := do
  let ty ← instantiateMVars (← mvarId.getType)
  if !hasShiftLeft ty then
    return some mvarId
  let ctx1 ← mkOnlySimpContext NormalizeRules.shiftLeftToMulRuleNames
  let (some mvar1, _) ← Meta.simpTarget mvarId ctx1 (mayCloseGoal := true)
    | return none
  let ctx2 ← mkOnlySimpContext NormalizeRules.twoPowReduceRuleNames
  let simprocs ← Simp.getSimprocs
  let (res?, _) ← Meta.simpTarget mvar1 ctx2 #[simprocs] (mayCloseGoal := true)
  return res?

/-- Attempt `H6a` word-level ring dispatch (`shl → mul` + `grind` ring solver, zero solver
axioms). Leaves state untouched and returns `false` if not in the ring fragment or if `grind`
does not close the goal. -/
def tryRingDispatch (mvarId : MVarId) : MetaM Bool := do
  let saved ← saveState
  try
    let (_, mvar1) ← mvarId.intros
    unless ← isRingCandidateGoal mvar1 do
      restoreState saved
      return false
    let some mvar2 ← rewriteConstShiftsToMul mvar1 | do
      let proof ← instantiateMVars (mkMVar mvarId)
      if proof.hasMVar || proof.hasSorry then
        restoreState saved
        return false
      return true
    let ok ← mvar2.withContext do
      let goalType ← instantiateMVars (← mvar2.getType)
      let params ← Grind.mkOnlyParams { verbose := false, revert := true }
      let tmp ← mkFreshExprSyntheticOpaqueMVar goalType
      let solved ← try
        Grind.withProtectedMCtx params.config tmp.mvarId! fun mvarId' => do
          let res ← Grind.main mvarId' params
          if res.hasFailed then
            throwError "ring dispatch failed"
        pure true
      catch _ =>
        pure false
      if !solved then return false
      let val ← instantiateMVars tmp
      if val.hasMVar || val.hasSorry then
        return false
      mvar2.assign val
      return true
    if !ok then
      restoreState saved
      return false
    let fullProof ← instantiateMVars (mkMVar mvarId)
    if fullProof.hasMVar || fullProof.hasSorry then
      restoreState saved
      return false
    return true
  catch _ =>
    restoreState saved
    return false

/-! ## 2. Sound Cone Slicing, Dual-Endpoint Abstraction, and Composition -/

private structure ProvedCut where
  lhs : Expr
  rhs : Expr
  lhsTy : Expr
  proof : Expr -- `lhs = rhs` in the original goal's `LCtx`
  deriving Inhabited

private def abstractPattern (e pat : Expr) : MetaM Expr := do
  if pat.isFVar then
    return e.abstract #[pat]
  else
    withConfig (fun c => { c with zeta := false, zetaDelta := false }) do
      kabstract e pat

/-- Rewrite occurrences of `pat` to `repl` inside `e` given `h : pat = repl`, returning
`(e', proof : e = e')`. When `isDefEqStep := true` (`let`-unfolding), skips `congrArg`. -/
private def rewriteSubexpr (e pat repl patTy h : Expr) (isDefEqStep : Bool := false) :
    MetaM (Expr × Option Expr) := do
  let abst ← abstractPattern e pat
  if !abst.hasLooseBVars then
    return (e, none)
  let newE := abst.instantiate1 repl
  if isDefEqStep then
    return (newE, none)
  try
    let fn := mkLambda `cut_z .default patTy abst
    let stepPrf ← mkCongrArg fn h
    return (newE, some stepPrf)
  catch _ =>
    return (e, none)

private def chainEqProof (curPrf? stepPrf? : Option Expr) : MetaM (Option Expr) :=
  match curPrf?, stepPrf? with
  | none, none => return none
  | some p, none => return some p
  | none, some q => return some q
  | some p, some q => return some (← mkEqTrans p q)

/-- Unfold `defMap` variables backward from `e`, stopping at any `FVarId` in `frontier`
(except the root itself when `unfoldRoot := true`). Returns `(e', proof? : e = e')`. -/
private def unfoldToFrontier (g : DefGraph) (e : Expr) (frontier : Std.HashSet FVarId)
    (unfoldRoot : Bool := true) : MetaM (Expr × Option Expr) := do
  let mut cur := e
  let mut prf? : Option Expr := none
  -- Unfold in reverse topological order so dependencies are always unfolded after dependents.
  let rootFVar? : Option FVarId := match e.consumeMData with | .fvar fv => some fv | _ => none
  for idx in [0:g.topoOrder.size] do
    let fv := g.topoOrder[g.topoOrder.size - 1 - idx]!
    let isRoot := unfoldRoot && rootFVar? == some fv
    if !isRoot && frontier.contains fv then
      continue
    if !exprContainsFVar cur fv then
      continue
    let some info := g.defs.get? fv | continue
    let (nextE, stepPrf?) ←
      rewriteSubexpr cur (mkFVar fv) info.rhs (mkBitVecTy info.width) info.eqProof info.isLet
    cur := nextE
    prf? ← chainEqProof prf? stepPrf?
  return (cur, prf?)

/-- Rewrite all `cut.rhs` occurrences to `cut.lhs` in `e` using `cut.proof.symm`. -/
private def applyProvedCuts (e : Expr) (cuts : Array ProvedCut) : MetaM (Expr × Option Expr) := do
  let mut cur := e
  let mut prf? : Option Expr := none
  -- Apply newest cuts first (reverse topological order) so outer expressions rewrite cleanly.
  for idx in [0:cuts.size] do
    let cut := cuts[cuts.size - 1 - idx]!
    let symmPrf ← mkEqSymm cut.proof
    let (nextE, stepPrf?) ← rewriteSubexpr cur cut.rhs cut.lhs cut.lhsTy symmPrf false
    if nextE != cur then
      cur := nextE
      prf? ← chainEqProof prf? stepPrf?
  return (cur, prf?)

/-- Collect transitive cone-relevant side-condition hypotheses and all free variables needed to
build a self-contained closed sliced obligation. -/
private def collectSliceClosure (g : DefGraph) (lhs rhs : Expr) :
    MetaM (Array FVarId × Array FVarId) := do
  let lctx ← getLCtx
  let mut varSet : Std.HashSet FVarId := {}
  for fv in collectExprFVars lhs do varSet := varSet.insert fv
  for fv in collectExprFVars rhs do varSet := varSet.insert fv
  -- Transitive closure over non-defining side-condition hypotheses touching `varSet`.
  let mut keptSides : Std.HashSet FVarId := {}
  let mut changed := true
  while changed do
    changed := false
    for sh in g.sideHyps do
      if keptSides.contains sh then continue
      let shTy ← instantiateMVars (← sh.getDecl).type
      let shVars := collectExprFVars shTy
      if shVars.any (fun v => varSet.contains v) then
        keptSides := keptSides.insert sh
        for v in shVars do
          if !varSet.contains v then
            varSet := varSet.insert v
            changed := true
  -- Also pull in any FVars occurring in the types of `varSet` (e.g. parametric widths).
  let mut typeChanged := true
  while typeChanged do
    typeChanged := false
    let snapshot := varSet.toList
    for fv in snapshot do
      let ty ← instantiateMVars (← fv.getDecl).type
      for tv in collectExprFVars ty do
        if !varSet.contains tv then
          varSet := varSet.insert tv
          typeChanged := true
  -- Order in `LCtx` order so dependent types remain well-scoped.
  let mut orderedVars : Array FVarId := #[]
  let mut orderedSides : Array FVarId := #[]
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    if varSet.contains ldecl.fvarId && !keptSides.contains ldecl.fvarId then
      orderedVars := orderedVars.push ldecl.fvarId
    else if keptSides.contains ldecl.fvarId then
      orderedSides := orderedSides.push ldecl.fvarId
  return (orderedVars, orderedSides)

private structure SliceObligation where
  sliceProp : Expr
  args : Array Expr
  isClosed : Bool

/-- Build a closed (or LCtx-local) sliced obligation `∀ v_0 ... v_k, H_0 → ... → lhs' = rhs'`,
abstracting every `sliceVar` as a regular non-`let` binder AND abstracting any compound
`cut.lhs` expressions appearing in `lhs`/`rhs` (when `abstractCompoundCuts := true`). -/
private def buildSliceObligation (g : DefGraph) (lhs rhs : Expr) (cuts : Array ProvedCut)
    (abstractCompoundCuts : Bool := true) : MetaM SliceObligation := do
  -- First optionally abstract compound `cut.lhs` terms into synthetic variables.
  let mut curLhs := lhs
  let mut curRhs := rhs
  let mut compoundArgs : Array (Expr × Expr) := #[]
  if abstractCompoundCuts then
    for idx in [0:cuts.size] do
      let cut := cuts[cuts.size - 1 - idx]!
      if cut.lhs.isFVar then continue
      let abstL ← abstractPattern curLhs cut.lhs
      let abstR ← abstractPattern curRhs cut.lhs
      if abstL.hasLooseBVars || abstR.hasLooseBVars then
        compoundArgs := compoundArgs.push (cut.lhs, cut.lhsTy)
  let (sliceVars, sideHyps) ← collectSliceClosure g lhs rhs
  let mut declInfos : Array (Name × (Array Expr → MetaM Expr)) := #[]
  for i in [0:sliceVars.size] do
    let fv := sliceVars[i]!
    let origTy ← instantiateMVars (← fv.getDecl).type
    let nm := Name.mkSimple s!"v{i}"
    let idx := i
    declInfos := declInfos.push (nm, fun prev => do
      let mut ty := origTy
      for j in [0:idx] do
        ty := ty.replaceFVarId sliceVars[j]! prev[j]!
      return ty)
  let baseCount := sliceVars.size
  for i in [0:compoundArgs.size] do
    let (_, cTy) := compoundArgs[i]!
    let nm := Name.mkSimple s!"c{i}"
    declInfos := declInfos.push (nm, fun prev => do
      let mut ty := cTy
      for j in [0:baseCount] do
        ty := ty.replaceFVarId sliceVars[j]! prev[j]!
      return ty)
  for i in [0:sideHyps.size] do
    let sh := sideHyps[i]!
    let origTy ← instantiateMVars (← sh.getDecl).type
    let nm := Name.mkSimple s!"h{i}"
    declInfos := declInfos.push (nm, fun prev => do
      let mut ty := origTy
      for j in [0:baseCount] do
        ty := ty.replaceFVarId sliceVars[j]! prev[j]!
      return ty)
  let sliceProp ← withLocalDeclsD declInfos fun fvars => do
    let mut l := curLhs
    let mut r := curRhs
    for j in [0:baseCount] do
      l := l.replaceFVarId sliceVars[j]! fvars[j]!
      r := r.replaceFVarId sliceVars[j]! fvars[j]!
    for i in [0:compoundArgs.size] do
      let (cExpr, _) := compoundArgs[i]!
      let mut cSubst := cExpr
      for j in [0:baseCount] do
        cSubst := cSubst.replaceFVarId sliceVars[j]! fvars[j]!
      let fv := fvars[baseCount + i]!
      let abstL ← abstractPattern l cSubst
      let abstR ← abstractPattern r cSubst
      if abstL.hasLooseBVars then l := abstL.instantiate1 fv
      if abstR.hasLooseBVars then r := abstR.instantiate1 fv
    let eqExpr ← mkEq l r
    mkForallFVars fvars eqExpr
  let args : Array Expr :=
    (sliceVars.map mkFVar) ++ (compoundArgs.map (·.1)) ++ (sideHyps.map mkFVar)
  let sliceProp ← instantiateMVars sliceProp
  return { sliceProp := sliceProp, args := args, isClosed := !sliceProp.hasFVar }

/-- Discharge a single goal `mvarId` using `rfl` → `H7` normalizer → `H6a` ring dispatch →
`bv_decide_qbe`. Emits zero axioms on SAT or failure. -/
private def solveSingleObligation (mvarId : MVarId) (cfg : BVDecideConfig)
    (types : Option (Array Name)) (qbeCtx : QbeContext) (tryNorm : Bool := true) :
    MetaM (Except (Option CounterExample) Unit) := do
  -- Fast path 0: definitional equality
  let closedDefEq ← mvarId.withContext do
    let ty := (← instantiateMVars (← mvarId.getType)).consumeMData
    if let some (_, l, r) := ty.eq? then
      if ← withReducible (isDefEq l r) then
        mvarId.assign (← mkEqRefl l)
        return true
    return false
  if closedDefEq then return .ok ()
  -- Fast path 1: `H7` normalizer rules (`shiftmul` + `opt_share`)
  let mut cur := mvarId
  if tryNorm then
    match ← trySimpNormalizeRules cur with
    | none => return .ok ()
    | some next => cur := next
  -- Fast path 2: `H6a` ring dispatch (`shl → mul` + `grind`, zero solver axioms)
  if ← tryRingDispatch cur then
    return .ok ()
  -- General path 3: trust-pure `bv_decide_qbe` (with `*`-gated auto `acNf`)
  let effectiveCfg ←
    if cfg.acNf then pure cfg
    else if ← hasBvMulInGoal cfg.fixedInt cur then pure { cfg with acNf := true }
    else pure cfg
  let tacticCtx := mkQbeTacticContext effectiveCfg types
  let qbeCtx' := { qbeCtx with acNf := effectiveCfg.acNf }
  let params ← Grind.mkDefaultParams {}
  try
    match ← Grind.GrindM.run (params := params) <|
        bvDecideQbe' (.mvarIdTarget cur) tacticCtx qbeCtx' with
    | .ok _ => return .ok ()
    | .error cex => return .error (some cex)
  catch _ =>
    return .error none

/-- Solve a closed (or LCtx-local) `SliceObligation`, consulting `sliceCache` first to reuse
previously proved identical stage obligations with zero extra solver calls or axioms. -/
private def solveSliceObligation (ob : SliceObligation)
    (sliceCache : IO.Ref (Std.HashMap Expr Expr))
    (cfg : BVDecideConfig) (types : Option (Array Name)) (qbeCtx : QbeContext) :
    MetaM (Except (Option CounterExample) Expr) := do
  if ob.isClosed then
    if let some cachedPrf := (← sliceCache.get).get? ob.sliceProp then
      return .ok (mkAppN cachedPrf ob.args)
  let mkAndSolve : MetaM (Except (Option CounterExample) Expr) := do
    let mvar ← mkFreshExprSyntheticOpaqueMVar ob.sliceProp
    match ← solveSingleObligation mvar.mvarId! cfg types qbeCtx (tryNorm := true) with
    | .ok () =>
      let prf ← instantiateMVars mvar
      if prf.hasMVar || prf.hasSorry then
        return .error none
      if ob.isClosed then
        sliceCache.modify (·.insert ob.sliceProp prf)
      return .ok (mkAppN prf ob.args)
    | .error cex? =>
      return .error cex?
  if ob.isClosed then
    withLCtx {} {} mkAndSolve
  else
    mkAndSolve

/-- Attempt to prove `lhs = rhs` in the original `LCtx` by unfolding to `frontier`, rewriting
by `cuts`, building the sliced obligation, and composing the kernel proof. -/
private def proveCutWithFrontier (g : DefGraph) (lhs rhs : Expr)
    (frontier : Std.HashSet FVarId) (cuts : Array ProvedCut)
    (sliceCache : IO.Ref (Std.HashMap Expr Expr))
    (cfg : BVDecideConfig) (types : Option (Array Name)) (qbeCtx : QbeContext)
    (abstractCompoundCuts : Bool := true) :
    MetaM (Except (Option CounterExample) Expr) := do
  let (gUnf, hg1?) ← unfoldToFrontier g lhs frontier (unfoldRoot := true)
  let (tUnf, ht1?) ← unfoldToFrontier g rhs frontier (unfoldRoot := true)
  let (gRw, hg2?) ← applyProvedCuts gUnf cuts
  let (tRw, ht2?) ← applyProvedCuts tUnf cuts
  let hg? ← chainEqProof hg1? hg2?
  let ht? ← chainEqProof ht1? ht2?
  -- Fast path: identical after unfolding and rewriting previous cuts!
  let midPrf? : Except (Option CounterExample) Expr ← do
    if gRw == tRw || (← withReducible (isDefEq gRw tRw)) then
      pure (.ok (← mkEqRefl gRw))
    else
      let ob ← buildSliceObligation g gRw tRw cuts abstractCompoundCuts
      solveSliceObligation ob sliceCache cfg types qbeCtx
  match midPrf? with
  | .error cex? => return .error cex?
  | .ok midPrf =>
    let step1 ← match hg? with
      | none => pure midPrf
      | some hg => mkEqTrans hg midPrf
    let full ← match ht? with
      | none => pure step1
      | some ht => mkEqTrans step1 (← mkEqSymm ht)
    return .ok full

/-! ## 3. Main Entrypoint `bvCutQbe` -/

private def addCutToFrontier (frontier : Std.HashSet FVarId) (cut : ProvedCut) :
    Std.HashSet FVarId :=
  let f1 := match cut.lhs.consumeMData with | .fvar fv => frontier.insert fv | _ => frontier
  match cut.rhs.consumeMData with | .fvar fv => f1.insert fv | _ => f1

/-- Convert `BitVec` `let`-bindings into non-`let` binders plus explicit equality hypotheses
`h : x = rhs` in a fresh closed goal so `bv_normalize`'s `zetaDeltaAll` never exponentially
tree-expands deep `let`-DAGs (e.g. buggy 16-round ARX `let` chains). -/
private def solveViaLetsAsHyps (mvarId : MVarId) (cfg : BVDecideConfig)
    (types : Option (Array Name)) (qbeCtx : QbeContext) : MetaM Bool :=
  mvarId.withContext do
    let lctx ← getLCtx
    let target ← instantiateMVars (← mvarId.getType)
    let mut letFVars : Array FVarId := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      if ldecl.value?.isSome then
        if (← getBitVecWidth? ldecl.type).isSome then
          letFVars := letFVars.push ldecl.fvarId
    if letFVars.size < 2 then
      return false
    let letSet : Std.HashSet FVarId := letFVars.foldl (·.insert ·) {}
    let mut allVars : Array FVarId := #[]
    let mut propHyps : Array FVarId := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      if ldecl.value?.isSome then
        if letSet.contains ldecl.fvarId then
          allVars := allVars.push ldecl.fvarId
        else
          -- Non-BitVec `let` present: decline conversion and let direct solver handle it.
          return false
      else if ← isProp ldecl.type then
        propHyps := propHyps.push ldecl.fvarId
      else
        allVars := allVars.push ldecl.fvarId
    let mut varIdxMap : Std.HashMap FVarId Nat := {}
    for i in [0:allVars.size] do
      varIdxMap := varIdxMap.insert allVars[i]! i
    let replaceVars (e : Expr) (fvars : Array Expr) (limit : Nat) : Expr := Id.run do
      let mut out := e
      for j in [0:limit] do
        out := out.replaceFVarId allVars[j]! fvars[j]!
      return out
    let mut declInfos : Array (Name × (Array Expr → MetaM Expr)) := #[]
    for i in [0:allVars.size] do
      let fv := allVars[i]!
      let ldecl ← fv.getDecl
      let origTy ← instantiateMVars ldecl.type
      let idx := i
      declInfos := declInfos.push (ldecl.userName, fun prev =>
        pure (replaceVars origTy prev idx))
    let nVars := allVars.size
    let mut reflArgs : Array Expr := #[]
    for i in [0:letFVars.size] do
      let fv := letFVars[i]!
      let ldecl ← fv.getDecl
      let some rawVal := ldecl.value? | return false
      let val ← instantiateMVars rawVal
      let some vIdx := varIdxMap.get? fv | return false
      let nm := Name.mkSimple s!"hlet_{i}"
      declInfos := declInfos.push (nm, fun prev => do
        let rhsSubst := replaceVars val prev nVars
        mkEq prev[vIdx]! rhsSubst)
      reflArgs := reflArgs.push (← mkEqRefl (mkFVar fv))
    for i in [0:propHyps.size] do
      let hfv := propHyps[i]!
      let ldecl ← hfv.getDecl
      let origTy ← instantiateMVars ldecl.type
      declInfos := declInfos.push (ldecl.userName, fun prev =>
        pure (replaceVars origTy prev nVars))
    let closedProp ← withLocalDeclsD declInfos fun fvars => do
      let body := replaceVars target fvars nVars
      mkForallFVars fvars body
    let closedProp ← instantiateMVars closedProp
    if closedProp.hasFVar then
      return false
    let prf ← withLCtx {} {} do
      let tmp ← mkFreshExprSyntheticOpaqueMVar closedProp
      let effectiveCfg ←
        if cfg.acNf then pure cfg
        else if ← hasBvMulInGoal cfg.fixedInt tmp.mvarId! then pure { cfg with acNf := true }
        else pure cfg
      let tacticCtx := mkQbeTacticContext effectiveCfg types
      let qbeCtx' := { qbeCtx with acNf := effectiveCfg.acNf }
      let params ← Grind.mkDefaultParams {}
      discard <| Grind.GrindM.run (params := params) <|
        bvDecideQbe (.mvarIdTarget tmp.mvarId!) tacticCtx qbeCtx'
      instantiateMVars tmp
    let args : Array Expr :=
      (allVars.map mkFVar) ++ reflArgs ++ (propHyps.map mkFVar)
    mvarId.assign (mkAppN prf args)
    return true

private def fallbackDirectSolve (mvarId : MVarId) (cfg : BVDecideConfig)
    (types : Option (Array Name)) (qbeCtx : QbeContext) (tryNorm : Bool := true) :
    MetaM Unit := do
  let mut cur := mvarId
  if tryNorm then
    match ← trySimpNormalizeRules cur with
    | none => return
    | some next => cur := next
  if ← tryRingDispatch cur then
    return
  if ← solveViaLetsAsHyps cur cfg types qbeCtx then
    return
  let effectiveCfg ←
    if cfg.acNf then pure cfg
    else if ← hasBvMulInGoal cfg.fixedInt cur then pure { cfg with acNf := true }
    else pure cfg
  let tacticCtx := mkQbeTacticContext effectiveCfg types
  let qbeCtx' := { qbeCtx with acNf := effectiveCfg.acNf }
  let params ← Grind.mkDefaultParams {}
  discard <| Grind.GrindM.run (params := params) <|
    bvDecideQbe (.mvarIdTarget cur) tacticCtx qbeCtx'

/-- Main MetaM entrypoint for `bv_cut_qbe`.
- If `explicitCuts` is non-empty, proves each explicit cut `g = t` in order (failing cleanly
  if any explicit cut is unprovable), abstracts both endpoints in subsequent obligations, and
  discharges the residual root goal.
- If `explicitCuts` is empty, extracts the pre-inlining `let`/hypothesis DAG, runs fast
  corner + random simulation (bailing out cleanly on `+uf`/opaque atoms or tiny goals, and
  skipping cuts on probable CEX), discharges discovered cuts in topological order (dropping
  any false/unprovable automatic cut), and finishes the residual root goal with guaranteed
  completeness fallback to direct `bv_decide_qbe`. -/
def bvCutQbe (mvarId : MVarId) (cfg : BVDecideConfig)
    (types : Option (Array Name) := none) (qbeCtx : QbeContext := {})
    (explicitCuts : Array Expr := #[]) : MetaM Unit := do
  -- Lift leading `∀`/`→`/`let` binders (including leading `let`s on `lhs`/`rhs`).
  let mvarId ← liftTargetLets mvarId
  mvarId.withContext do
    if !explicitCuts.isEmpty then
      bvCutQbeExplicit mvarId cfg types qbeCtx explicitCuts
      return
    -- Fast path 0 (automatic mode): definitional equality
    let targetTy := (← instantiateMVars (← mvarId.getType)).consumeMData
    if let some (_, l, r) := targetTy.eq? then
      if ← withReducible (isDefEq l r) then
        mvarId.assign (← mkEqRefl l)
        return
    -- Fast path 1 (automatic mode): try `H7` normalizer and whole-goal `H6a` ring dispatch
    -- before doing any DAG/simulation work.
    let mvarNorm? ← trySimpNormalizeRules mvarId
    let some mvarAfterNorm := mvarNorm? | return
    if ← tryRingDispatch mvarAfterNorm then
      return
    -- Continue on `mvarAfterNorm` (which kept all `let`s intact!).
    bvCutQbeAuto mvarAfterNorm cfg types qbeCtx
where
  bvCutQbeExplicit (mvarId : MVarId) (cfg : BVDecideConfig) (types : Option (Array Name))
      (qbeCtx : QbeContext) (explicitCuts : Array Expr) : MetaM Unit :=
    mvarId.withContext do
      let g ← extractDefGraph mvarId
      let sliceCache ← IO.mkRef ({} : Std.HashMap Expr Expr)
      let mut provedCuts : Array ProvedCut := #[]
      let mut frontier : Std.HashSet FVarId := {}
      for cutExpr in explicitCuts do
        let cutTy := (← instantiateMVars cutExpr).consumeMData
        let some (eqTy, lhs, rhs) := cutTy.eq?
          | throwError "Tactic `bv_cut_qbe`: explicit cutpoint must be an equality `e1 = e2`, \
              got:{indentExpr cutTy}"
        let prfRes ← proveCutWithFrontier g lhs rhs frontier provedCuts sliceCache cfg types
          qbeCtx (abstractCompoundCuts := true)
        let prf ← match prfRes with
          | .ok p => pure p
          | .error (some cex) => throwCounterExample cex
          | .error none =>
            -- Retry without abstracting earlier cuts in case a cut depended on an earlier cone.
            let mvarTmp ← mkFreshExprSyntheticOpaqueMVar cutTy
            match ← solveSingleObligation mvarTmp.mvarId! cfg types qbeCtx (tryNorm := true) with
            | .ok () => instantiateMVars mvarTmp
            | .error (some cex) => throwCounterExample cex
            | .error none =>
              throwError "Tactic `bv_cut_qbe`: failed to prove explicit cutpoint:{indentExpr cutTy}"
        let cut : ProvedCut := { lhs := lhs, rhs := rhs, lhsTy := eqTy, proof := prf }
        provedCuts := provedCuts.push cut
        frontier := addCutToFrontier frontier cut
      -- Discharge root goal using the proved explicit cuts.
      let targetTy := (← instantiateMVars (← mvarId.getType)).consumeMData
      if let some (_, rootLhs, rootRhs) := targetTy.eq? then
        match ← proveCutWithFrontier g rootLhs rootRhs frontier provedCuts sliceCache cfg types
            qbeCtx (abstractCompoundCuts := true) with
        | .ok rootPrf =>
          mvarId.assign rootPrf
          return
        | .error _ =>
          -- Retry rewriting `t → g` without generalizing compound `g`s.
          match ← proveCutWithFrontier g rootLhs rootRhs frontier provedCuts sliceCache cfg types
              qbeCtx (abstractCompoundCuts := false) with
          | .ok rootPrf =>
            mvarId.assign rootPrf
            return
          | .error _ =>
            fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := true)
      else
        fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := true)

  bvCutQbeAuto (mvarId : MVarId) (cfg : BVDecideConfig) (types : Option (Array Name))
      (qbeCtx : QbeContext) : MetaM Unit :=
    mvarId.withContext do
      -- Bail out cleanly if `+uf` is enabled (opaque function atoms cannot be simulated).
      if cfg.uf then
        fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := false)
        return
      let targetTy := (← instantiateMVars (← mvarId.getType)).consumeMData
      let some (eqTy, rootLhs, rootRhs) := targetTy.eq? | do
        fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := false)
        return
      let some _ ← getBitVecWidth? eqTy | do
        fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := false)
        return
      let g ← extractDefGraph mvarId
      -- Tiny-goal bailout: skip simulation when there are fewer than 2 defining bindings
      -- or when total expression size is tiny.
      if g.defs.size < 2 then
        fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := false)
        return
      let discovery ← discoverCandidateCuts g rootLhs rootRhs
      if discovery.probableCex || discovery.candidates.isEmpty then
        fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := false)
        return
      let sliceCache ← IO.mkRef ({} : Std.HashMap Expr Expr)
      let mut provedCuts : Array ProvedCut := #[]
      let mut frontier : Std.HashSet FVarId := {}
      -- Per-cut bounded budget so a single hard/false automatic cut cannot exhaust the budget.
      let cutTimeout := min cfg.timeout (max 2 (cfg.timeout / 2))
      let cutCfg : BVDecideConfig := { cfg with timeout := cutTimeout }
      let cutQbeCtx : QbeContext := { qbeCtx with fuel := fuelOfTimeout cutTimeout }
      for cand in discovery.candidates do
        match ← proveCutWithFrontier g cand.lhs cand.rhs frontier provedCuts sliceCache cutCfg
            types cutQbeCtx (abstractCompoundCuts := false) with
        | .ok prf =>
          let cut : ProvedCut := {
            lhs := cand.lhs
            rhs := cand.rhs
            lhsTy := mkBitVecTy cand.width
            proof := prf
          }
          provedCuts := provedCuts.push cut
          frontier := addCutToFrontier frontier cut
        | .error _ =>
          -- Automatic `nomatch` fallback: drop false or unprovable candidate cut cleanly.
          pure ()
      if provedCuts.isEmpty then
        fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := false)
        return
      -- Discharge the simplified residual root goal.
      match ← proveCutWithFrontier g rootLhs rootRhs frontier provedCuts sliceCache cfg types
          qbeCtx (abstractCompoundCuts := false) with
      | .ok rootPrf =>
        mvarId.assign rootPrf
        return
      | .error _ =>
        -- Completeness fallback: if over-abstraction hid a side condition needed at root,
        -- solve the original un-abstracted goal directly.
        fallbackDirectSolve mvarId cfg types qbeCtx (tryNorm := false)

end BvDecideQbe
