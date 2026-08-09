import Kraken.X64.Syntax
import Kraken.X64.Semantics
import Kraken.X64.OmniSemantics
import Kraken.X64.PrintIntel
import Lean
import Lean.PrettyPrinter.Delaborator
import Lean.Elab.Term

open Lean
open Lean.Meta
open Lean.PrettyPrinter
open Lean.PrettyPrinter.Delaborator
open Lean.PrettyPrinter.Delaborator.SubExpr

--------------------------------------------------------------------------------
-- 1. Define custom syntax representations for the Goal View (with Explicit Names)
--------------------------------------------------------------------------------

-- Explicitly named so we can construct them manually and safely
syntax (name := asmSym) "[asm|" ppIndent((ppLine str)*) "]" : term
syntax (name := asmLayoutSym) "[asm_layout|" ppIndent((ppLine term)*) "]" : term

-- Standard fallback syntax for general open lists
syntax "[asm| " term,* " ]" : term

--------------------------------------------------------------------------------
-- 2. Define safe helpers to identify types & navigate arrays
--------------------------------------------------------------------------------

-- Fully compiler-independent indexing helper using core GetElem
def getArg (args : Array Expr) (i : Nat) : DelabM Expr := do
  if h : i < args.size then
    return args[i]
  else
    failure

def isDirectiveType (e : Expr) : MetaM Bool :=
  return Expr.isConstOf e ``Directive

def isNatType (e : Expr) : MetaM Bool :=
  return Expr.isConstOf e ``Nat

def isDirectiveNatType (e : Expr) : MetaM Bool := do
  match_expr e with
  | Prod a b => return Expr.isConstOf a ``Directive && Expr.isConstOf b ``Nat
  | _ => return false

-- Version-independent helper with fully-qualified constructors
def getNatVal? (e : Expr) : Option Nat :=
  match_expr e with
  | OfNat.ofNat _ n _ =>
    if let Expr.lit (Literal.natVal val) := n then some val else none
  | _ =>
    if let Expr.lit (Literal.natVal val) := e then some val else none

--------------------------------------------------------------------------------
-- 3. Define the consolidated Delaborator (Unsafe, getArg & Explicit Namespaces)
--------------------------------------------------------------------------------

-- Delaborates individual (Directive × Nat) pairs beautifully as "@N: instruction"
@[app_delab Prod.mk]
unsafe def delabDirectiveNatPair : Delab := do
  let e ← getExpr
  match_expr e with
  | Prod.mk alpha beta dExpr nExpr =>
    if (← isDirectiveType alpha) && (← isNatType beta) then

      -- 1. Evaluates closed Directive parts to their authentic ToString assembly format
      let dStr ← if !dExpr.hasFVar && !dExpr.hasMVar then
        let typeExpr ← Meta.inferType dExpr
        let d ← Meta.evalExpr Directive typeExpr dExpr
        pure s!"{d}"
      else
        pure "<symbolic_directive>"

      -- 2. Extract the Nat index/offset from nExpr using fully-qualified matches
      let idxStr ← match nExpr with
        | Expr.app _ arg =>
          if let some n := getNatVal? arg then
            pure s!"{n}"
          else
            -- If it's a symbolic index (e.g. `layout.size 0`), navigate inside to get the index term
            let idxStx ← withAppArg (withAppArg delab)
            let fmt ← PrettyPrinter.ppTerm idxStx
            pure s!"{fmt}"
        | _ =>
          if let some n := getNatVal? nExpr then
            pure s!"{n}"
          else
            let idxStx ← withAppArg delab
            let fmt ← PrettyPrinter.ppTerm idxStx
            pure s!"{fmt}"

      let combinedStr := s!"@{idxStr}: {dStr}"
      return Syntax.mkStrLit combinedStr
    else
      failure
  | _ => failure

-- Recursive helper to process Lists of symbolic pairs
unsafe def delabDirectiveNatListGo : DelabM (List Term) := do
  let curr ← getExpr
  if curr.isAppOfArity ``List.cons 3 then
    let head ← withAppFn (withAppArg delab)
    let tail ← withAppArg delabDirectiveNatListGo
    return head :: tail
  else if curr.isAppOfArity ``List.nil 1 then
    return []
  else
    let tail ← delab
    return [tail]

-- Standalone helper for List Directive (Program)
unsafe def delabProgramListGo : DelabM (List Term) := do
  let curr ← getExpr
  match_expr curr with
  | List.cons _ _ _ =>
    let head ← withAppFn (withAppArg delab)
    let tail ← withAppArg delabProgramListGo
    return head :: tail
  | List.nil _ =>
    return []
  | _ =>
    let tail ← delab
    return [tail]

@[app_delab List.cons]
unsafe def delabProgramList : Delab := do
  let e ← getExpr
  let args := e.getAppArgs
  if args.size >= 3 then
    let alpha ← getArg args 0

    -- ==========================================
    -- Case A: List Directive (Program)
    -- ==========================================
    if ← isDirectiveType alpha then
      if !e.hasFVar && !e.hasMVar then
        let typeExpr ← Meta.inferType e
        let prog ← Meta.evalExpr (List Directive) typeExpr e
        let lines := prog.map (fun d => s!"{d}")
        let linesStx : Array Syntax := lines.map (fun line => Syntax.mkStrLit line) |>.toArray

        -- Manually build raw Syntax node and coerce to Term with anonymous constructor ⟨...⟩
        let node := Syntax.node SourceInfo.none ``asmSym #[
          Syntax.atom SourceInfo.none "[asm|",
          Syntax.node SourceInfo.none nullKind linesStx,
          Syntax.atom SourceInfo.none "]"
        ]
        return ⟨node⟩
      else
        let elems ← delabProgramListGo
        let elemsArr := elems.toArray
        return ← `([asm| $elemsArr,* ])

    -- ==========================================
    -- Case B: List (Directive × Nat) (Layout)
    -- ==========================================
    else if ← isDirectiveNatType alpha then
      if !e.hasFVar && !e.hasMVar then
        let typeExpr ← Meta.inferType e
        let prog ← Meta.evalExpr (List (Directive × Nat)) typeExpr e
        let lines := prog.map (fun (d, sz) => s!"{d}  [size: {sz}]")
        let linesStx : Array Syntax := lines.map (fun line => Syntax.mkStrLit line) |>.toArray

        -- Manually build raw Syntax node and coerce to Term with anonymous constructor ⟨...⟩
        let node := Syntax.node SourceInfo.none ``asmSym #[
          Syntax.atom SourceInfo.none "[asm|",
          Syntax.node SourceInfo.none nullKind linesStx,
          Syntax.atom SourceInfo.none "]"
        ]
        return ⟨node⟩
      else
        -- Fallback: Manually build raw Syntax node and coerce to Term with anonymous constructor ⟨...⟩
        let elems ← delabDirectiveNatListGo
        let elemsArr : Array Syntax := elems.map (·.raw) |>.toArray
        let node := Syntax.node SourceInfo.none ``asmLayoutSym #[
          Syntax.atom SourceInfo.none "[asm_layout|",
          Syntax.node SourceInfo.none nullKind elemsArr,
          Syntax.atom SourceInfo.none "]"
        ]
        return ⟨node⟩

  failure
