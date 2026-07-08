prelude
import Lean
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Sym.Simp.Attr
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.AppBuilder
import KrakenStdlibCandidates.Init.RemoveToInt
import KrakenStdlibCandidates.Init.Data.BitVec.Basic


/-!
# Grind internalization hooks for homomorphisms and predicates.
-/

namespace Homomorphism

open Lean Meta Grind Sym Simp

initialize registerTraceClass `homo
initialize registerTraceClass `homo.pred
initialize registerTraceClass `homo.visit

initialize homoPredExt : SimplePersistentEnvExtension (Name × Name × Nat) (NameMap (List (Name × Nat))) ←
  let add := fun s (f, thm, k) =>
    let list := (s.find? f).getD []
    s.insert f ((thm, k) :: list)
  registerSimplePersistentEnvExtension {
    addEntryFn    := add
    addImportedFn := fun es => mkStateFromImportedEntries add {} es
  }

def getPredMap : CoreM (NameMap (List (Name × Nat))) :=
  return homoPredExt.getState (← getEnv)

def getExplicitArity (type : Expr) : Nat :=
  match type with
  | Expr.forallE _ _ body bi =>
    let rest := getExplicitArity body
    if bi.isExplicit then rest + 1 else rest
  | _ => 0

def addPredicate (thmName : Name) : MetaM Unit := do
  let info ← getConstInfo thmName
  unless (← isProp info.type) do
    throwError "invalid homomorphism predicate, `{thmName}` is not a proposition"
  let _vs := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs type => do
    let xs_explicit ← xs.filterM fun x => do
      return (← getFVarLocalDecl x).binderInfo.isExplicit
    let found? := type.find? fun e => Id.run do
      if e.isApp then
        let fn := e.getAppFn
        let args := e.getAppArgs
        if let .const _ _us := fn then
          if args.size < xs_explicit.size then return false
          let trailingArgs := args.extract (args.size - xs_explicit.size) args.size
          return trailingArgs == xs_explicit
      return false
    let some found := found? |
      throwError "invalid homomorphism predicate, `{thmName}` does not contain application that covers all parameters"
    let .const declName _ := found.getAppFn | unreachable!
    let k := getExplicitArity info.type
    modifyEnv fun env => homoPredExt.addEntry env (declName, thmName, k)

initialize registerBuiltinAttribute {
    name := `grind_homo_pred
    descr := "add a theorem to be applied to atoms"
    add := fun declName _ _ => discard <| addPredicate declName |>.run {} {}
  }

/--
Declares attribute `[grind_mono]` for marking theorems implementing the homomorphism.
-/
initialize homoSimpExtension : SymSimpExtension ←
  registerSymSimpAttr `grind_homo "`grind` homomorphism attribute"

/--
Returns theorems marked with `[grind_mono]`
-/
def getTheorems : CoreM Theorems :=
  homoSimpExtension.getTheorems

/--
Creates a simproc that applies the theorems marked with `[grind_mono]`.
This simproc is meant to be applied as a `pre` method.

Recall that `grind` internalizes terms bottom-up. By the time a
simplification set runs on a term `e`, all subterms of `e` are already
in the E-graph and have been processed by the pipeline.

**Stop condition.** When simp encounters a term `t` during traversal:

- If a rule matches `t`: apply it, continue (result is a new term).
- If no rule matches `t` AND `t` is already in the E-graph:
  stop, don't descend. Otherwise: descend normally.
-/
partial def extractLiteral? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n ← getNatValue? e then return some n
  if let some i ← getIntValue? e then if i ≥ 0 then return some i.toNat
  if e.isAppOfArity ``NatCast.natCast 3 then
    if let some n ← getNatValue? e.appArg! then return some n
  if e.isAppOfArity ``HMod.hMod 6 then
    return ← extractLiteral? e.appFn!.appArg!
  return none

partial def getTrailingZeros (n : Nat) : Nat :=
  if n == 0 then 0
  else if n % 2 == 1 then 0
  else 1 + getTrailingZeros (n / 2)

partial def isPowerOfTwo (n : Nat) : Option Nat :=
  if n == 0 then none
  else if n.land (n - 1) == 0 then some (getTrailingZeros n)
  else none

def landMaskToMod (e : Expr) : MetaM (Option Sym.Simp.Result) := do
  let_expr HAnd.hAnd _ _ _ _ a mExpr := e | return none
  let optM ← extractLiteral? mExpr
  let some m := optM | return none

  let aType ← Lean.Meta.inferType a
  if aType.isConstOf ``Int then
    let mkLit := fun (val : Nat) => mkIntLit val

    -- 1. Standard masks: 2^k - 1
    if m > 0 && m.land (m + 1) == 0 then
      let newM := m + 1
      let newExpr ← mkAppM ``HMod.hMod #[a, mkLit newM]
      let hType1 ← mkAppM ``LE.le #[mkLit 0, mExpr]
      let hProof1 ← mkDecideProof hType1
      let hType2 ← mkEq (← mkAppM ``HAnd.hAnd #[mExpr, mkLit newM]) (mkLit 0)
      let hProof2 ← mkDecideProof hType2
      let prf ← mkAppM `Int.land_mask_eq_mod #[a, mExpr, hProof1, hProof2]
      return some (.step newExpr prf)

    -- 2. Upper masks: 2^k - 2^n
    else if m > 0 then
      let n := getTrailingZeros m
      let low := 2^n
      if let some k := isPowerOfTwo (m + low) then
        if k >= n then
          let d := k - n
          let nExpr := mkNatLit n
          let kExpr := mkNatLit k
          let twoD := mkLit (2^d)
          let twoN ← mkAppM ``HPow.hPow #[mkLit 2, nExpr]
          let a_div_n ← mkAppM ``HDiv.hDiv #[a, twoN]
          let a_div_mod ← mkAppM ``HMod.hMod #[a_div_n, twoD]
          let newExpr ← mkAppM ``HMul.hMul #[a_div_mod, twoN]

          let hLeType ← mkAppM ``LE.le #[nExpr, kExpr]
          let hLeProof ← mkDecideProof hLeType
          let hType ← mkEq (← mkAppM ``HAdd.hAdd #[mExpr, twoN]) (← mkAppM ``HPow.hPow #[mkLit 2, kExpr])
          let hProof ← mkDecideProof hType
          let prf ← mkAppM `Int.land_upper_mask_eq_div #[a, mExpr, kExpr, nExpr, hLeProof, hProof]
          return some (.step newExpr prf)
  else if aType.isConstOf ``Nat then
    let mkLit := fun (val : Nat) => mkNatLit val
    if m > 0 && m.land (m + 1) == 0 then
      let newM := m + 1
      let newExpr ← mkAppM ``HMod.hMod #[a, mkLit newM]
      let hType ← mkEq (← mkAppM ``HAnd.hAnd #[mExpr, mkLit newM]) (mkLit 0)
      let hProof ← mkDecideProof hType
      let prf ← mkAppM `Nat.land_mask_eq_mod #[a, mExpr, hProof]
      return some (.step newExpr prf)

  return none

def mkRewriter : GoalM Sym.Simp.Simproc := do
  let s ← get
  -- Remark: We are not using any discharger. So, our rewriting rules are all context
  -- independent.
  let rw := (← getTheorems).rewrite
  return fun e => do
    trace[homo.visit] "{e}"
    let r ← rw e
    if !r.isRfl then return r
    -- If `e` is already in the E-graph, we don't revisit its children
    let done := s.enodeMap.contains { expr := e }
    return .rfl (done := done)

def appendToMul (e : Expr) : MetaM (Option Sym.Simp.Result) := do
  let isUnsigned := e.isAppOf `BitVec.unsigned
  let isToNat := e.isAppOf ``BitVec.toNat
  if isUnsigned || isToNat then
    let app ← instantiateMVars e.appArg!
    if app.isAppOf `HAppend.hAppend || app.isAppOf ``BitVec.append then
      if let b :: a :: _ := app.getAppArgs.toList.reverse then
        try
          let prf ← if isUnsigned then mkAppM ``BitVec.unsigned_append #[a, b] else mkAppM ``BitVec.toNat_append #[a, b]
          let rhs := (← inferType prf).appArg!
          return some (.step rhs prf)
        catch _ => return none
  return none

structure State where
  cache : Sym.Simp.Cache := {}
  processed : PHashSet ExprPtr := {}

initialize homoExt : SolverExtension State ←
  registerSolverExtension (return {})

def applyHomo (e : Expr) : GoalM Sym.Simp.Result := do
  let rewriter ← mkRewriter
  let methods := {
    pre := fun e => do
      if let some r ← landMaskToMod e then return r
      rewriter e
    post := fun e => do
      if let some r ← landMaskToMod e then return r
      return .rfl (done := false)
  }
  -- Reuse cache.
  let persistentCache := (← homoExt.getState).cache
  homoExt.modifyState fun s => { s with cache := {} } -- Improve uniqueness. This is a minor optimization
  let (r, simpState) ← Sym.Simp.SimpM.run (Sym.Simp.simp e) (methods := methods) (s := { persistentCache })
  homoExt.modifyState fun s => { s with cache := simpState.persistentCache }
  trace[homo] "applyHomo on {e} completed"
  return r

/--
Returns `true` if some theorem marked with `[grind_homo]` is applicable to `e`.

Motivation: we don't want to start the simplifier and fail immediately.
-/
def isTarget (e : Expr) : CoreM Bool := do
  if e.isConstOf ``System.Platform.numBits || e.isAppOf `BitVec.unsigned || e.isAppOf ``BitVec.toNat || e.isAppOf `HAppend.hAppend || e.isAppOf ``BitVec.append || e.isAppOf ``HAnd.hAnd || e.isAppOf ``HShiftRight.hShiftRight then return true
  if let .const declName _ := e.getAppFn then
    if (← getPredMap).contains declName then return true
  let thms ← getTheorems
  return !(thms.getMatch e).isEmpty

/--
Internalization procedure for this module. See `homoExt.setMethods`
-/
def internalize (e : Expr) (_ : Option Expr) : GoalM Unit := do
  trace[homo] "internalize checking: {e}, isTarget={← isTarget e}"
  unless (← isTarget e) do return ()

  if e.isConstOf ``System.Platform.numBits then
    let thm := mkConst ``System.Platform.numBits_eq
    let pred ← Meta.inferType thm
    addNewRawFact thm pred (← getGeneration e) .input .other
    return ()

  let isUnsigned := e.isAppOf `BitVec.unsigned
  let isToNat := e.isAppOf ``BitVec.toNat
  if isUnsigned || isToNat then
    if let some (.step e₁ h₁ _) ← appendToMul e then
      let r ← preprocess e₁
      let h ← mkEqTrans h₁ (← r.getProof)
      let gen ← getGeneration e
      Grind.internalize r.expr gen
      pushEq e r.expr h
      return ()

  let f := e.getAppFn
  if let .const declName _ := f then
    unless (← homoExt.getState).processed.contains { expr := e } do
      homoExt.modifyState fun s => { s with processed := s.processed.insert { expr := e } }
      if let some thms := (← getPredMap).find? declName then
        let args := e.getAppArgs
        for (thmName, k) in thms do
          try
            if args.size < k then throwError "insufficient arguments"
            let thm ← Meta.mkAppM thmName (args.extract (args.size - k) args.size)
            let pred ← Meta.inferType thm
            trace[homo.pred] "Found matching predicate homomorphism: {thmName} with type {pred}"
            addNewRawFact thm pred (← getGeneration e) .input .other
          catch err =>
            trace[homo.pred] "Failed to apply {thmName}: {err.toMessageData}"
            continue -- try next theorem in the list
        return ()

  if e.isAppOf ``Eq && !(← alreadyInternalized e) then
    let_expr Eq _ lhs rhs := e | return ()
    let gen := max (← getGeneration lhs) (← getGeneration rhs)
    Grind.internalize e gen
    return ()

  let res ← applyHomo e
  let .step e₁ h₁ _ := res | return ()
  let r ← preprocess e₁
  let h ← mkEqTrans h₁ (← r.getProof)
  let gen ← getGeneration e
  Grind.internalize r.expr gen
  trace[homo] "{e}\n====>\n{r.expr}"
  pushEq e r.expr h

initialize
  homoExt.setMethods
    (internalize := internalize)

end Homomorphism


