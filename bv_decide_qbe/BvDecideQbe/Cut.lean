module

public import BvDecideQbe.Cegar
public import BvDecideQbe.NormalizeRules
public import Lean.Elab.Tactic.BVDecide
public import Lean.Meta.Tactic.Grind.Main
public import Lean.Meta.Tactic.Simp.Main
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Cutpoint-Equivalence Tactic `bv_cut_qbe` & Ring-Dispatch Helper (`E0 / H5a` + `H6a`)

Zero-new-trust Lean front end for cutpoint slicing and word-level ring dispatch on `BitVec`
equivalence goals:
1. **Pre-inlining DAG extraction (`P1-3`):** Inspects `let`-bindings and `h : x = e` local
   hypotheses BEFORE `bv_normalize` inlines them, topologically breaking any cycles and
   retaining all non-defining side-condition hypotheses (`a < 100#32`, `x ≠ 0`, etc.).
2. **Word-level simulation discovery:** Evaluates reflected `BitVec`/`Bool` subexpressions
   across deterministic corner + random patterns (filtered by reflected side conditions),
   bailing out cleanly when `+uf` opaque atoms are present or the goal is tiny.
   Detects probable counterexamples early (zero intermediate axioms emitted!).
3. **Sound topological discharge (`H5a` + `H6a`):** For each candidate cut `(g, t)` in
   topological order, slices the cone back to the already-proved cut frontier, abstracts both
   endpoints `(g', t')` of earlier cuts to a shared fresh variable `v`, retains transitive
   cone-relevant side conditions, and proves the obligation via:
   - `rfl` / `H7` normalizer rules (`shiftmul` + `opt_share`, zero axioms);
   - `H6a` ring dispatch (constant `shl → mul` + `grind`, zero solver axioms);
   - `bv_decide_qbe` (verified in-process `KissatFidelity` + kernel `rfl`).
   Every step produces a kernel-checked proof term (`Eq.trans` / `congrArg` / `∀`-instantiation).
   Failed automatic cuts are dropped cleanly (`nomatch` fallback).
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Lean.Elab.Tactic.BVDecide
open Lean.Meta.Tactic.BVDecide
open Std.Tactic.BVDecide

/-! ## 1. Low-Level Expression Inspection & Literal Helpers -/

private partial def getNatLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | .const ``Nat.zero _ => some 0
  | .app (.const ``Nat.succ _) inner => (getNatLit? inner).map (· + 1)
  | .app (.app (.app (.const ``OfNat.ofNat _) ty) val) _ =>
    if ty.consumeMData.isConstOf ``Nat then getNatLit? val else none
  | _ => none

private def getBitVecWidth? (ty : Expr) : MetaM (Option Nat) := do
  let ty := (← instantiateMVars ty).consumeMData
  match_expr ty with
  | BitVec wExpr =>
    if let some w := getNatLit? wExpr then
      return some w
    let wWhnf ← whnf wExpr
    return getNatLit? wWhnf
  | _ => return none

private def getBitVecLit? (e : Expr) : Option (Σ w, BitVec w) :=
  match e.consumeMData with
  | .app (.app (.const ``BitVec.ofNat _) wExpr) nExpr => do
    let w ← getNatLit? wExpr
    let n ← getNatLit? nExpr
    return ⟨w, BitVec.ofNat w n⟩
  | .app (.app (.app (.const ``OfNat.ofNat _) ty) nExpr) _ =>
    match ty.consumeMData with
    | .app (.const ``BitVec _) wExpr => do
      let w ← getNatLit? wExpr
      let n ← getNatLit? nExpr
      return ⟨w, BitVec.ofNat w n⟩
    | _ => none
  | _ => none

private def getBoolLit? (e : Expr) : Option Bool :=
  match e.consumeMData with
  | .const ``Bool.true _ => some true
  | .const ``Bool.false _ => some false
  | _ => none

private def mkBitVecTy (w : Nat) : Expr :=
  mkApp (mkConst ``BitVec) (mkNatLit w)

/-! ## 2. `H7` Simp Normalizer & `H6a` Ring-Dispatch Helper -/

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

/-! ## 3. Pre-Inlining DAG Extraction (`P1-3`) -/

private structure DefInfo where
  fvarId : FVarId
  width : Nat
  rhs : Expr
  eqProof : Expr
  isLet : Bool
  hypFVarId? : Option FVarId
  deriving Inhabited

private structure DefGraph where
  defs : Std.HashMap FVarId DefInfo
  topoOrder : Array FVarId
  depth : Std.HashMap FVarId Nat
  sideHyps : Array FVarId
  deriving Inhabited

private def collectExprFVars (e : Expr) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds

private def exprContainsFVar (e : Expr) (target : FVarId) : Bool :=
  (collectExprFVars e).contains target

private def liftTargetLets (mvarId : MVarId) : MetaM MVarId := do
  let mut cur := mvarId
  let mut steps := 0
  while steps < 256 do
    steps := steps + 1
    let progress ← cur.withContext do
      let ty := (← instantiateMVars (← cur.getType)).consumeMData
      if ty.isForall || ty.isLet then
        let (_, next) ← cur.intro1P
        return some next
      let some (eqTy, lhs, rhs) := ty.eq? | return none
      if let .letE n t v b nondep := lhs.consumeMData then
        let u ← getLevel eqTy
        let eqBody := mkApp3 (mkConst ``Eq [u]) eqTy b rhs
        let lifted := Expr.letE n t v eqBody nondep
        let changed ← cur.change lifted (checkDefEq := true)
        let (_, next) ← changed.intro1P
        return some next
      if let .letE n t v b nondep := rhs.consumeMData then
        let u ← getLevel eqTy
        let eqBody := mkApp3 (mkConst ``Eq [u]) eqTy lhs b
        let lifted := Expr.letE n t v eqBody nondep
        let changed ← cur.change lifted (checkDefEq := true)
        let (_, next) ← changed.intro1P
        return some next
      return none
    match progress with
    | some next => cur := next
    | none => break
  return cur

/-- Extract a cycle-free pre-inlining definition DAG from `LCtx` (`let`-bindings and
`h : x = e` / `h : e = x` `BitVec` equalities), keeping all remaining `Prop` hypotheses in
`sideHyps` so cone-relevant side conditions are never dropped. -/
private def extractDefGraph (mvarId : MVarId) : MetaM DefGraph :=
  mvarId.withContext do
    let lctx ← getLCtx
    let mut rawDefs : Std.HashMap FVarId DefInfo := {}
    let mut defHypSet : Std.HashSet FVarId := {}
    let mut orderedVars : Array FVarId := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      if let some val := ldecl.value? then
        if let some w ← getBitVecWidth? ldecl.type then
          let val ← instantiateMVars val
          if !exprContainsFVar val ldecl.fvarId then
            rawDefs := rawDefs.insert ldecl.fvarId {
              fvarId := ldecl.fvarId
              width := w
              rhs := val
              eqProof := ← mkEqRefl (mkFVar ldecl.fvarId)
              isLet := true
              hypFVarId? := none
            }
            orderedVars := orderedVars.push ldecl.fvarId
    for ldecl in lctx do
      if ldecl.isImplementationDetail || ldecl.value?.isSome then continue
      let ty := (← instantiateMVars ldecl.type).consumeMData
      let some (eqTy, a, b) := ty.eq? | continue
      let some w ← getBitVecWidth? eqTy | continue
      let a := a.consumeMData
      let b := b.consumeMData
      if let .fvar fv := a then
        if !rawDefs.contains fv && !exprContainsFVar b fv then
          rawDefs := rawDefs.insert fv {
            fvarId := fv
            width := w
            rhs := b
            eqProof := mkFVar ldecl.fvarId
            isLet := false
            hypFVarId? := some ldecl.fvarId
          }
          defHypSet := defHypSet.insert ldecl.fvarId
          orderedVars := orderedVars.push fv
          continue
      if let .fvar fv := b then
        if !rawDefs.contains fv && !exprContainsFVar a fv then
          let symmPrf ← mkEqSymm (mkFVar ldecl.fvarId)
          rawDefs := rawDefs.insert fv {
            fvarId := fv
            width := w
            rhs := a
            eqProof := symmPrf
            isLet := false
            hypFVarId? := some ldecl.fvarId
          }
          defHypSet := defHypSet.insert ldecl.fvarId
          orderedVars := orderedVars.push fv
    -- Topologically sort `rawDefs`, dropping any back-edge that would form a cycle.
    let stateRef ← IO.mkRef ({} : Std.HashMap FVarId Nat) -- 1 = visiting, 2 = done
    let droppedRef ← IO.mkRef ({} : Std.HashSet FVarId)
    let topoRef ← IO.mkRef (#[] : Array FVarId)
    let depthRef ← IO.mkRef ({} : Std.HashMap FVarId Nat)
    let defHypRef ← IO.mkRef defHypSet
    let rec dfs (fuel : Nat) (fv : FVarId) : MetaM Unit := do
      let .succ fuel' := fuel | do
        droppedRef.modify (·.insert fv)
        return
      match (← stateRef.get).get? fv with
      | some 2 => return
      | some 1 =>
        droppedRef.modify (·.insert fv)
        return
      | _ => pure ()
      let some info := rawDefs.get? fv | return
      stateRef.modify (·.insert fv 1)
      let deps := collectExprFVars info.rhs
      let mut maxDep := 0
      let mut hasCycle := false
      for d in deps do
        if rawDefs.contains d then
          if (← stateRef.get).get? d == some 1 then
            hasCycle := true
          else
            dfs fuel' d
            if !(← droppedRef.get).contains d then
              maxDep := max maxDep ((← depthRef.get).getD d 0)
      if hasCycle || (← droppedRef.get).contains fv then
        droppedRef.modify (·.insert fv)
        stateRef.modify (·.insert fv 2)
        if let some hfv := info.hypFVarId? then
          defHypRef.modify (·.erase hfv)
      else
        stateRef.modify (·.insert fv 2)
        depthRef.modify (·.insert fv (maxDep + 1))
        topoRef.modify (·.push fv)
    for fv in orderedVars do
      dfs (orderedVars.size + 1) fv
    let topo ← topoRef.get
    let depthMap ← depthRef.get
    let finalDefHypSet ← defHypRef.get
    let mut cleanDefs : Std.HashMap FVarId DefInfo := {}
    for fv in topo do
      if let some info := rawDefs.get? fv then
        cleanDefs := cleanDefs.insert fv info
    let mut sideHyps : Array FVarId := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail || ldecl.value?.isSome then continue
      if finalDefHypSet.contains ldecl.fvarId then continue
      if ← isProp ldecl.type then
        sideHyps := sideHyps.push ldecl.fvarId
    return { defs := cleanDefs, topoOrder := topo, depth := depthMap, sideHyps := sideHyps }

private def collectConeVars (g : DefGraph) (root : Expr) : Std.HashSet FVarId := Id.run do
  let mut stack := collectExprFVars root
  let mut visited : Std.HashSet FVarId := {}
  while !stack.isEmpty do
    let fv := stack.back!
    stack := stack.pop
    if visited.contains fv then continue
    visited := visited.insert fv
    if let some info := g.defs.get? fv then
      for d in collectExprFVars info.rhs do
        if !visited.contains d then
          stack := stack.push d
  return visited

/-! ## 4. Fast 64-Bit Corner + Random Simulation Engine -/

private inductive SimBvOp where
  | var (slot : Nat)
  | const (w : Nat) (val : BitVec w)
  | bin (op : BVBinOp) (lhs rhs : Nat)
  | sub (lhs rhs : Nat)
  | neg (inner : Nat)
  | un (op : BVUnOp) (inner : Nat)
  | shlConst (inner k : Nat)
  | shrConst (inner k : Nat)
  | shlBv (lhs rhs : Nat)
  | shrBv (lhs rhs : Nat)
  | ashrBv (lhs rhs : Nat)
  | append (lhs rhs : Nat)
  | extract (start len inner : Nat)
  | zeroExtend (inner : Nat)
  | signExtend (inner : Nat)
  | replicate (n inner : Nat)
  | ite (condNode thenNode elseNode : Nat)

private inductive SimBoolOp where
  | bvar (slot : Nat)
  | bconst (val : Bool)
  | not (inner : Nat)
  | and (lhs rhs : Nat)
  | or (lhs rhs : Nat)
  | xor (lhs rhs : Nat)
  | beq (lhs rhs : Nat)
  | bvEq (lhs rhs : Nat)
  | bvNe (lhs rhs : Nat)
  | bvUlt (lhs rhs : Nat)
  | bvUle (lhs rhs : Nat)
  | bvSlt (lhs rhs : Nat)
  | bvSle (lhs rhs : Nat)
  | getLsbD (inner idx : Nat)
  | msb (inner : Nat)

private inductive SimNode where
  | bv (width : Nat) (op : SimBvOp)
  | bool (op : SimBoolOp)

private structure SimBuildState where
  nodes : Array SimNode := #[]
  bvVars : Array Nat := #[]
  numBoolVars : Nat := 0
  bvFVarSlot : Std.HashMap FVarId Nat := {}
  boolFVarSlot : Std.HashMap FVarId Nat := {}
  fvarNode : Std.HashMap FVarId Nat := {}
  exprNode : Std.HashMap Sym.ExprPtr Nat := {}
  boolExprNode : Std.HashMap Sym.ExprPtr Nat := {}
  maxNodes : Nat := 32768

private abbrev SimBuildM := StateRefT SimBuildState MetaM

private def addSimNode (n : SimNode) : SimBuildM (Option Nat) := do
  let st ← get
  if st.nodes.size ≥ st.maxNodes then return none
  let idx := st.nodes.size
  set { st with nodes := st.nodes.push n }
  return some idx

private def getOrAddBvVar (fv : FVarId) (w : Nat) : SimBuildM (Option Nat) := do
  let st ← get
  if let some idx := st.fvarNode.get? fv then
    return some idx
  let slot := st.bvVars.size
  let some idx ← addSimNode (.bv w (.var slot)) | return none
  modify fun s => { s with
    bvVars := s.bvVars.push w
    bvFVarSlot := s.bvFVarSlot.insert fv slot
    fvarNode := s.fvarNode.insert fv idx }
  return some idx

private def getOrAddBoolVar (fv : FVarId) : SimBuildM (Option Nat) := do
  let st ← get
  if let some idx := st.boolFVarSlot.get? fv then
    return some idx
  let slot := st.numBoolVars
  let some idx ← addSimNode (.bool (.bvar slot)) | return none
  modify fun s => { s with
    numBoolVars := s.numBoolVars + 1
    boolFVarSlot := s.boolFVarSlot.insert fv idx }
  return some idx

private def simNodeWidth? (idx : Nat) : SimBuildM (Option Nat) := do
  let st ← get
  match st.nodes[idx]? with
  | some (.bv w _) => return some w
  | _ => return none

mutual

private partial def reflectSimBv (g : DefGraph) (e : Expr) : SimBuildM (Option Nat) := do
  let e := e.consumeMData
  if let some idx := (← get).exprNode.get? ⟨e⟩ then
    return some idx
  let res ← reflectSimBvCore g e
  if let some idx := res then
    modify fun s => { s with exprNode := s.exprNode.insert ⟨e⟩ idx }
  return res

private partial def reflectSimBvCore (g : DefGraph) (e : Expr) : SimBuildM (Option Nat) := do
  if let some ⟨w, val⟩ := getBitVecLit? e then
    return ← addSimNode (.bv w (.const w val))
  if let .fvar fv := e then
    if let some idx := (← get).fvarNode.get? fv then
      return some idx
    if let some info := g.defs.get? fv then
      let some idx ← reflectSimBv g info.rhs | return none
      modify fun s => { s with fvarNode := s.fvarNode.insert fv idx }
      return some idx
    let some w ← getBitVecWidth? (← fv.getDecl).type | return none
    return ← getOrAddBvVar fv w
  match_expr e with
  | BitVec.twoPow wExpr kExpr =>
    let some w := getNatLit? wExpr | return none
    let some k := getNatLit? kExpr | return none
    addSimNode (.bv w (.const w (BitVec.twoPow w k)))
  | HAdd.hAdd _ _ _ _ a b => reflectSimBin g .add a b
  | Add.add _ _ a b => reflectSimBin g .add a b
  | BitVec.add _ a b => reflectSimBin g .add a b
  | HSub.hSub _ _ _ _ a b => reflectSimSub g a b
  | Sub.sub _ _ a b => reflectSimSub g a b
  | BitVec.sub _ a b => reflectSimSub g a b
  | HMul.hMul _ _ _ _ a b => reflectSimBin g .mul a b
  | Mul.mul _ _ a b => reflectSimBin g .mul a b
  | BitVec.mul _ a b => reflectSimBin g .mul a b
  | HAnd.hAnd _ _ _ _ a b => reflectSimBin g .and a b
  | AndOp.and _ _ a b => reflectSimBin g .and a b
  | BitVec.and _ a b => reflectSimBin g .and a b
  | HOr.hOr _ _ _ _ a b => reflectSimBin g .or a b
  | OrOp.or _ _ a b => reflectSimBin g .or a b
  | BitVec.or _ a b => reflectSimBin g .or a b
  | HXor.hXor _ _ _ _ a b => reflectSimBin g .xor a b
  | XorOp.xor _ _ a b => reflectSimBin g .xor a b
  | BitVec.xor _ a b => reflectSimBin g .xor a b
  | HDiv.hDiv _ _ _ _ a b => reflectSimBin g .udiv a b
  | HMod.hMod _ _ _ _ a b => reflectSimBin g .umod a b
  | Neg.neg _ _ a =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    addSimNode (.bv w (.neg ai))
  | BitVec.neg _ a =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    addSimNode (.bv w (.neg ai))
  | Complement.complement _ _ a => reflectSimUn g .not a
  | BitVec.not _ a => reflectSimUn g .not a
  | BitVec.reverse _ a => reflectSimUn g .reverse a
  | BitVec.clz _ a => reflectSimUn g .clz a
  | BitVec.cpop _ a => reflectSimUn g .cpop a
  | BitVec.rotateLeft _ a kExpr =>
    let some k := getNatLit? kExpr | return none
    reflectSimUn g (.rotateLeft k) a
  | BitVec.rotateRight _ a kExpr =>
    let some k := getNatLit? kExpr | return none
    reflectSimUn g (.rotateRight k) a
  | BitVec.sshiftRight _ a kExpr =>
    let some k := getNatLit? kExpr | return none
    reflectSimUn g (.arithShiftRightConst k) a
  | BitVec.sshiftRight' _ _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some si ← reflectSimBv g s | return none
    let some w ← simNodeWidth? ai | return none
    addSimNode (.bv w (.ashrBv ai si))
  | HShiftLeft.hShiftLeft _ _ _ _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    if let some k := getNatLit? s then
      addSimNode (.bv w (.shlConst ai k))
    else
      let some si ← reflectSimBv g s | return none
      addSimNode (.bv w (.shlBv ai si))
  | BitVec.shiftLeft _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    let some k := getNatLit? s | return none
    addSimNode (.bv w (.shlConst ai k))
  | HShiftRight.hShiftRight _ _ _ _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    if let some k := getNatLit? s then
      addSimNode (.bv w (.shrConst ai k))
    else
      let some si ← reflectSimBv g s | return none
      addSimNode (.bv w (.shrBv ai si))
  | BitVec.ushiftRight _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    let some k := getNatLit? s | return none
    addSimNode (.bv w (.shrConst ai k))
  | HAppend.hAppend _ _ _ _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    let some wa ← simNodeWidth? ai | return none
    let some wb ← simNodeWidth? bi | return none
    addSimNode (.bv (wa + wb) (.append ai bi))
  | BitVec.append _ _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    let some wa ← simNodeWidth? ai | return none
    let some wb ← simNodeWidth? bi | return none
    addSimNode (.bv (wa + wb) (.append ai bi))
  | BitVec.extractLsb' _ sExpr lExpr a =>
    let some start := getNatLit? sExpr | return none
    let some len := getNatLit? lExpr | return none
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bv len (.extract start len ai))
  | BitVec.extractLsb _ hiExpr loExpr a =>
    let some hi := getNatLit? hiExpr | return none
    let some lo := getNatLit? loExpr | return none
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bv (hi - lo + 1) (.extract lo (hi - lo + 1) ai))
  | BitVec.zeroExtend _ vExpr a => reflectSimZeroExt g vExpr a
  | BitVec.truncate _ vExpr a => reflectSimZeroExt g vExpr a
  | BitVec.setWidth _ vExpr a => reflectSimZeroExt g vExpr a
  | BitVec.setWidth' _ vExpr _ a => reflectSimZeroExt g vExpr a
  | BitVec.signExtend _ vExpr a =>
    let some v := getNatLit? vExpr | return none
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bv v (.signExtend ai))
  | BitVec.replicate _ nExpr a =>
    let some n := getNatLit? nExpr | return none
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    addSimNode (.bv (w * n) (.replicate n ai))
  | ite _ c _ t f =>
    let some ci ← reflectSimBool g c | return none
    let some ti ← reflectSimBv g t | return none
    let some fi ← reflectSimBv g f | return none
    let some wt ← simNodeWidth? ti | return none
    let some wf ← simNodeWidth? fi | return none
    if wt != wf then return none
    addSimNode (.bv wt (.ite ci ti fi))
  | cond _ c t f =>
    let some ci ← reflectSimBool g c | return none
    let some ti ← reflectSimBv g t | return none
    let some fi ← reflectSimBv g f | return none
    let some wt ← simNodeWidth? ti | return none
    let some wf ← simNodeWidth? fi | return none
    if wt != wf then return none
    addSimNode (.bv wt (.ite ci ti fi))
  | _ => return none

private partial def reflectSimBin (g : DefGraph) (op : BVBinOp) (a b : Expr) :
    SimBuildM (Option Nat) := do
  let some ai ← reflectSimBv g a | return none
  let some bi ← reflectSimBv g b | return none
  let some wa ← simNodeWidth? ai | return none
  let some wb ← simNodeWidth? bi | return none
  if wa != wb then return none
  addSimNode (.bv wa (.bin op ai bi))

private partial def reflectSimSub (g : DefGraph) (a b : Expr) : SimBuildM (Option Nat) := do
  let some ai ← reflectSimBv g a | return none
  let some bi ← reflectSimBv g b | return none
  let some wa ← simNodeWidth? ai | return none
  let some wb ← simNodeWidth? bi | return none
  if wa != wb then return none
  addSimNode (.bv wa (.sub ai bi))

private partial def reflectSimUn (g : DefGraph) (op : BVUnOp) (a : Expr) :
    SimBuildM (Option Nat) := do
  let some ai ← reflectSimBv g a | return none
  let some wa ← simNodeWidth? ai | return none
  addSimNode (.bv wa (.un op ai))

private partial def reflectSimZeroExt (g : DefGraph) (vExpr a : Expr) :
    SimBuildM (Option Nat) := do
  let some v := getNatLit? vExpr | return none
  let some ai ← reflectSimBv g a | return none
  addSimNode (.bv v (.zeroExtend ai))

private partial def reflectSimBool (g : DefGraph) (e : Expr) : SimBuildM (Option Nat) := do
  let e := e.consumeMData
  if let some idx := (← get).boolExprNode.get? ⟨e⟩ then
    return some idx
  let res ← reflectSimBoolCore g e
  if let some idx := res then
    modify fun s => { s with boolExprNode := s.boolExprNode.insert ⟨e⟩ idx }
  return res

private partial def reflectSimBoolCore (g : DefGraph) (e : Expr) : SimBuildM (Option Nat) := do
  if let some b := getBoolLit? e then
    return ← addSimNode (.bool (.bconst b))
  if let .fvar fv := e then
    let ty := (← instantiateMVars (← fv.getDecl).type).consumeMData
    if ty.isConstOf ``Bool then
      return ← getOrAddBoolVar fv
    return none
  match_expr e with
  | True => addSimNode (.bool (.bconst true))
  | False => addSimNode (.bool (.bconst false))
  | Not inner =>
    let some i ← reflectSimBool g inner | return none
    addSimNode (.bool (.not i))
  | Bool.not inner =>
    let some i ← reflectSimBool g inner | return none
    addSimNode (.bool (.not i))
  | And a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.and ai bi))
  | Bool.and a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.and ai bi))
  | Or a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.or ai bi))
  | Bool.or a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.or ai bi))
  | Bool.xor a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.xor ai bi))
  | Eq ty a b =>
    if ty.consumeMData.isConstOf ``Bool then
      if getBoolLit? b == some true then
        reflectSimBool g a
      else if getBoolLit? a == some true then
        reflectSimBool g b
      else if getBoolLit? b == some false then
        let some ai ← reflectSimBool g a | return none
        addSimNode (.bool (.not ai))
      else if getBoolLit? a == some false then
        let some bi ← reflectSimBool g b | return none
        addSimNode (.bool (.not bi))
      else
        let some ai ← reflectSimBool g a | return none
        let some bi ← reflectSimBool g b | return none
        addSimNode (.bool (.beq ai bi))
    else if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvEq ai bi))
    else
      return none
  | Ne ty a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvNe ai bi))
    else if ty.consumeMData.isConstOf ``Bool then
      let some ai ← reflectSimBool g a | return none
      let some bi ← reflectSimBool g b | return none
      addSimNode (.bool (.xor ai bi))
    else
      return none
  | BEq.beq ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvEq ai bi))
    else if ty.consumeMData.isConstOf ``Bool then
      let some ai ← reflectSimBool g a | return none
      let some bi ← reflectSimBool g b | return none
      addSimNode (.bool (.beq ai bi))
    else
      return none
  | LT.lt ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvUlt ai bi))
    else
      return none
  | LE.le ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvUle ai bi))
    else
      return none
  | GT.gt ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvUlt bi ai))
    else
      return none
  | GE.ge ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvUle bi ai))
    else
      return none
  | BitVec.ult _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    addSimNode (.bool (.bvUlt ai bi))
  | BitVec.ule _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    addSimNode (.bool (.bvUle ai bi))
  | BitVec.slt _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    addSimNode (.bool (.bvSlt ai bi))
  | BitVec.sle _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    addSimNode (.bool (.bvSle ai bi))
  | BitVec.getLsbD _ a idxExpr =>
    let some idx := getNatLit? idxExpr | return none
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bool (.getLsbD ai idx))
  | BitVec.msb _ a =>
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bool (.msb ai))
  | decide p _ => reflectSimBool g p
  | _ => return none

end

private inductive SimVal where
  | bv (w : Nat) (val : BitVec w)
  | bool (val : Bool)
  deriving Inhabited

private def SimVal.asBv (w : Nat) : SimVal → BitVec w
  | .bv w' v => if h : w' = w then h ▸ v else v.setWidth w
  | .bool b => BitVec.ofNat w (if b then 1 else 0)

private def SimVal.asBool : SimVal → Bool
  | .bool b => b
  | .bv _ v => v.toNat != 0

private def evalSimDag (nodes : Array SimNode) (bvInputs : Array BVExpr.PackedBitVec)
    (boolInputs : Array Bool) : Array SimVal := Id.run do
  let mut vals : Array SimVal := Array.emptyWithCapacity nodes.size
  for node in nodes do
    let v : SimVal := match node with
      | .bv w op =>
        let res : BitVec w := match op with
          | .var slot =>
            let p := bvInputs[slot]!
            if h : p.w = w then h ▸ p.bv else p.bv.setWidth w
          | .const w' c =>
            if h : w' = w then h ▸ c else c.setWidth w
          | .bin bop l r => bop.eval (vals[l]!.asBv w) (vals[r]!.asBv w)
          | .sub l r => (vals[l]!.asBv w) - (vals[r]!.asBv w)
          | .neg a => -(vals[a]!.asBv w)
          | .un uop a => uop.eval (vals[a]!.asBv w)
          | .shlConst a k => (vals[a]!.asBv w) <<< k
          | .shrConst a k => (vals[a]!.asBv w) >>> k
          | .shlBv a s =>
            match vals[s]! with
            | .bv _ sv => (vals[a]!.asBv w) <<< sv
            | _ => 0#w
          | .shrBv a s =>
            match vals[s]! with
            | .bv _ sv => (vals[a]!.asBv w) >>> sv
            | _ => 0#w
          | .ashrBv a s =>
            match vals[s]! with
            | .bv _ sv => BitVec.sshiftRight' (vals[a]!.asBv w) sv
            | _ => 0#w
          | .append l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr =>
              let cat := vl ++ vr
              if h : wl + wr = w then h ▸ cat else cat.setWidth w
            | _, _ => 0#w
          | .extract start len a =>
            match vals[a]! with
            | .bv _ va =>
              let ex := BitVec.extractLsb' start len va
              if h : len = w then h ▸ ex else ex.setWidth w
            | _ => 0#w
          | .zeroExtend a =>
            match vals[a]! with
            | .bv _ va => va.setWidth w
            | _ => 0#w
          | .signExtend a =>
            match vals[a]! with
            | .bv _ va => va.signExtend w
            | _ => 0#w
          | .replicate n a =>
            match vals[a]! with
            | .bv wa va =>
              let rep := BitVec.replicate n va
              if h : wa * n = w then h ▸ rep else rep.setWidth w
            | _ => 0#w
          | .ite c t f =>
            if vals[c]!.asBool then vals[t]!.asBv w else vals[f]!.asBv w
        .bv w res
      | .bool op =>
        let res : Bool := match op with
          | .bvar slot => boolInputs[slot]!
          | .bconst b => b
          | .not a => !vals[a]!.asBool
          | .and l r => vals[l]!.asBool && vals[r]!.asBool
          | .or l r => vals[l]!.asBool || vals[r]!.asBool
          | .xor l r => vals[l]!.asBool ^^ vals[r]!.asBool
          | .beq l r => vals[l]!.asBool == vals[r]!.asBool
          | .bvEq l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr => wl == wr && vl.toNat == vr.toNat
            | _, _ => false
          | .bvNe l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr => !(wl == wr && vl.toNat == vr.toNat)
            | _, _ => false
          | .bvUlt l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr => wl == wr && vl.toNat < vr.toNat
            | _, _ => false
          | .bvUle l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr => wl == wr && vl.toNat ≤ vr.toNat
            | _, _ => false
          | .bvSlt l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr =>
              if h : wr = wl then vl.slt (h ▸ vr) else false
            | _, _ => false
          | .bvSle l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr =>
              if h : wr = wl then vl.sle (h ▸ vr) else false
            | _, _ => false
          | .getLsbD a idx =>
            match vals[a]! with
            | .bv _ va => va.getLsbD idx
            | _ => false
          | .msb a =>
            match vals[a]! with
            | .bv _ va => va.msb
            | _ => false
        .bool res
    vals := vals.push v
  return vals

private def splitmix64 (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9e3779b97f4a7c15
  let z := (s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (s', z ^^^ (z >>> 31))

private def randNatWidth (seed : UInt64) (w : Nat) (smallMask? : Option Nat := none) :
    UInt64 × Nat := Id.run do
  if let some mask := smallMask? then
    let (s', r) := splitmix64 seed
    return (s', r.toNat &&& mask)
  let words := max 1 ((w + 63) / 64)
  let mut s := seed
  let mut acc : Nat := 0
  for i in [0:words] do
    let (s', r) := splitmix64 s
    s := s'
    acc := acc ||| (r.toNat <<< (64 * i))
  return (s, acc)

private def cornerNatFor (patIdx varIdx w : Nat) : Nat :=
  let allOnes := (1 <<< w) - 1
  let msb := if w == 0 then 0 else 1 <<< (w - 1)
  match patIdx with
  | 0 => 0
  | 1 => allOnes
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 7
  | 6 => msb
  | 7 => msb - 1
  | 8 => 0x5555555555555555 &&& allOnes
  | 9 => 0xaaaaaaaaaaaaaaaa &&& allOnes
  | 10 => varIdx + 1
  | 11 => (allOnes ^^^ (1 <<< (varIdx % max 1 w)))
  | 12 => if varIdx % 2 == 0 then 0 else allOnes
  | 13 => if varIdx % 2 == 0 then 1 else 0
  | 14 => (varIdx * 17 + 5) &&& 0x3f
  | _ => (varIdx * 31 + 11) &&& 0xff

private structure SimPattern where
  bvInputs : Array BVExpr.PackedBitVec
  boolInputs : Array Bool

private def mkCornerPattern (bvVars : Array Nat) (numBoolVars patIdx : Nat) :
    SimPattern := Id.run do
  let mut bvs : Array BVExpr.PackedBitVec := Array.emptyWithCapacity bvVars.size
  for h : i in [0:bvVars.size] do
    let w := bvVars[i]
    bvs := bvs.push ⟨BitVec.ofNat w (cornerNatFor patIdx i w)⟩
  let mut bs : Array Bool := Array.emptyWithCapacity numBoolVars
  for i in [0:numBoolVars] do
    bs := bs.push (((patIdx >>> (i % 4)) &&& 1) == 1)
  return { bvInputs := bvs, boolInputs := bs }

private def mkRandPattern (bvVars : Array Nat) (numBoolVars : Nat) (seed : UInt64)
    (smallMask? : Option Nat := none) : UInt64 × SimPattern := Id.run do
  let mut s := seed
  let mut bvs : Array BVExpr.PackedBitVec := Array.emptyWithCapacity bvVars.size
  for w in bvVars do
    let (s', v) := randNatWidth s w smallMask?
    s := s'
    bvs := bvs.push ⟨BitVec.ofNat w v⟩
  let mut bs : Array Bool := Array.emptyWithCapacity numBoolVars
  for _ in [0:numBoolVars] do
    let (s', r) := splitmix64 s
    s := s'
    bs := bs.push ((r &&& 1) == 1)
  return (s, { bvInputs := bvs, boolInputs := bs })

private structure CandidateCut where
  lhs : Expr
  rhs : Expr
  width : Nat
  maxDepth : Nat
  sumDepth : Nat
  orderIdx : Nat

private structure DiscoveryResult where
  candidates : Array CandidateCut
  probableCex : Bool

private def hashSignature (vals : Array Nat) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for v in vals do
    h := (h ^^^ v.toUInt64) * 0x100000001b3
  return h

/-- Discover same-width candidate cut pairs `(g, t)` via 64-bit corner + random simulation.
Bails out cleanly (returning empty candidates) if opaque atoms are encountered or the goal
has too few nodes to benefit from slicing. -/
private def discoverCandidateCuts (g : DefGraph) (lhs rhs : Expr) :
    MetaM DiscoveryResult := do
  if g.defs.size < 2 then
    return { candidates := #[], probableCex := false }
  let leftCone := collectConeVars g lhs
  let rightCone := collectConeVars g rhs
  let mut leftVars : Array FVarId := #[]
  let mut rightVars : Array FVarId := #[]
  for fv in g.topoOrder do
    if leftCone.contains fv then leftVars := leftVars.push fv
    if rightCone.contains fv then rightVars := rightVars.push fv
  -- Also include primary inputs appearing in `leftCone`/`rightCone` for alias cuts like `u0 = x0`.
  for fv in leftCone do
    if !g.defs.contains fv then
      leftVars := leftVars.push fv
  for fv in rightCone do
    if !g.defs.contains fv then
      rightVars := rightVars.push fv
  if leftVars.isEmpty || rightVars.isEmpty then
    return { candidates := #[], probableCex := false }

  let ((rootPair?, sideNodes, allSideReflected, leftNodes, rightNodes), simSt) ←
    (do
      let some lhsNode ← reflectSimBv g lhs | return (none, #[], false, #[], #[])
      let some rhsNode ← reflectSimBv g rhs | return (none, #[], false, #[], #[])
      let mut sNodes : Array Nat := #[]
      let mut allOk := true
      for sh in g.sideHyps do
        let shTy ← instantiateMVars (← sh.getDecl).type
        if let some si ← reflectSimBool g shTy then
          sNodes := sNodes.push si
        else
          allOk := false
      let mut lNodes : Array (FVarId × Nat × Nat) := #[]
      for fv in leftVars do
        if let some ni ← reflectSimBv g (mkFVar fv) then
          if let some w ← simNodeWidth? ni then
            lNodes := lNodes.push (fv, w, ni)
      let mut rNodes : Array (FVarId × Nat × Nat) := #[]
      for fv in rightVars do
        if let some ni ← reflectSimBv g (mkFVar fv) then
          if let some w ← simNodeWidth? ni then
            rNodes := rNodes.push (fv, w, ni)
      return (some (lhsNode, rhsNode), sNodes, allOk, lNodes, rNodes)
    ).run {}

  let some (lhsNode, rhsNode) := rootPair?
    | return { candidates := #[], probableCex := false }

  -- Generate corner + small-range + full-width deterministic random patterns.
  let mut rawPats : Array SimPattern := #[]
  for i in [0:16] do
    rawPats := rawPats.push (mkCornerPattern simSt.bvVars simSt.numBoolVars i)
  let mut seed : UInt64 := 0x243f6a8885a308d3
  for i in [0:16] do
    let mask := if i < 8 then 0x3f else 0x3ff
    let (s', pat) := mkRandPattern simSt.bvVars simSt.numBoolVars seed (some mask)
    seed := s'
    rawPats := rawPats.push pat
  for _ in [0:32] do
    let (s', pat) := mkRandPattern simSt.bvVars simSt.numBoolVars seed none
    seed := s'
    rawPats := rawPats.push pat

  -- Evaluate patterns, filtering by reflected side conditions when present.
  let mut validEvals : Array (Array SimVal) := #[]
  let mut probableCex := false
  let evalAndKeep (pat : SimPattern) : Array SimVal × Bool × Bool :=
    let vals := evalSimDag simSt.nodes pat.bvInputs pat.boolInputs
    let okSide := sideNodes.all fun si => vals[si]!.asBool
    let rootDiff := match vals[lhsNode]!, vals[rhsNode]! with
      | .bv wl vl, .bv wr vr => wl != wr || vl.toNat != vr.toNat
      | _, _ => false
    (vals, okSide, rootDiff)

  for pat in rawPats do
    let (vals, okSide, rootDiff) := evalAndKeep pat
    if okSide then
      if rootDiff && allSideReflected then
        probableCex := true
      validEvals := validEvals.push vals

  if validEvals.size < 8 && !sideNodes.isEmpty then
    for i in [0:256] do
      let mask? :=
        if i % 3 == 0 then some 0x1f
        else if i % 3 == 1 then some 0xff
        else none
      let (s', pat) := mkRandPattern simSt.bvVars simSt.numBoolVars seed mask?
      seed := s'
      let (vals, okSide, rootDiff) := evalAndKeep pat
      if okSide then
        if rootDiff && allSideReflected then
          probableCex := true
        validEvals := validEvals.push vals
        if validEvals.size ≥ 32 then break

  if probableCex then
    return { candidates := #[], probableCex := true }
  if validEvals.isEmpty then
    return { candidates := #[], probableCex := false }

  -- Bucket left nodes by `(width, signatureHash)` and verify exact signature equality.
  let mkSig (nodeIdx : Nat) : Array Nat :=
    validEvals.map fun vals =>
      match (vals[nodeIdx]! : SimVal) with
      | .bv _ v => v.toNat
      | .bool b => if b then 1 else 0

  let mut leftBuckets : Std.HashMap (Nat × UInt64) (Array (FVarId × Array Nat)) := {}
  for (fv, w, ni) in leftNodes do
    let sig := mkSig ni
    let key := (w, hashSignature sig)
    let cur := leftBuckets.getD key #[]
    leftBuckets := leftBuckets.insert key (cur.push (fv, sig))

  let lhsFVar? : Option FVarId := match lhs.consumeMData with | .fvar fv => some fv | _ => none
  let rhsFVar? : Option FVarId := match rhs.consumeMData with | .fvar fv => some fv | _ => none

  let mut seenPairs : Std.HashSet (FVarId × FVarId) := {}
  let mut matchedRight : Std.HashSet FVarId := {}
  let mut candidates : Array CandidateCut := #[]
  let mut orderIdx := 0

  for (rfv, w, rni) in rightNodes do
    if matchedRight.contains rfv then continue
    let rsig := mkSig rni
    let key := (w, hashSignature rsig)
    let some lEntries := leftBuckets.get? key | continue
    -- Pick lowest-depth matching left node distinct from `rfv`.
    let mut bestL? : Option (FVarId × Nat) := none
    for (lfv, lsig) in lEntries do
      if lfv == rfv then continue
      if lsig != rsig then continue
      if lhsFVar? == some lfv && rhsFVar? == some rfv then continue
      let ld := g.depth.getD lfv 0
      let rd := g.depth.getD rfv 0
      if ld == 0 && rd == 0 then continue
      match bestL? with
      | none => bestL? := some (lfv, ld)
      | some (_, bestD) => if ld < bestD then bestL? := some (lfv, ld)
    if let some (lfv, ld) := bestL? then
      if !seenPairs.contains (lfv, rfv) && !seenPairs.contains (rfv, lfv) then
        seenPairs := seenPairs.insert (lfv, rfv)
        matchedRight := matchedRight.insert rfv
        let rd := g.depth.getD rfv 0
        candidates := candidates.push {
          lhs := mkFVar lfv
          rhs := mkFVar rfv
          width := w
          maxDepth := max ld rd
          sumDepth := ld + rd
          orderIdx := orderIdx
        }
        orderIdx := orderIdx + 1

  let sorted := candidates.qsort fun a b =>
    if a.maxDepth != b.maxDepth then a.maxDepth < b.maxDepth
    else if a.sumDepth != b.sumDepth then a.sumDepth < b.sumDepth
    else a.orderIdx < b.orderIdx
  return { candidates := sorted, probableCex := false }

/-! ## 5. Sound Cone Slicing, Dual-Endpoint Abstraction, and Composition -/

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
  let withCompCount := baseCount + compoundArgs.size
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
  let _ := withCompCount
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

/-! ## 6. Main Entrypoint `bvCutQbe` -/

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
