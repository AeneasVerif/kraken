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

-- Explicitly named so we can construct them manually and safely
syntax (name := asmSym) "[asm|" ppIndent((ppLine str)*) "]" : term
syntax (name := asmLayoutSym) "[asm_layout|" ppIndent((ppLine term)*) "]" : term

-- Standard fallback syntax for general open lists
syntax "[asm| " term,* " ]" : term

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

-- Delaborates individual (Directive × Nat) pairs as "@N: instruction".
-- This function is `unsafe` because it uses `Meta.evalExpr` to compute dExpr
-- (and to cast the result to the Directive type); we can't guarantee the safety
-- of doing this (if we want to reuse our existing formatter).
@[app_delab Prod.mk]
unsafe def delabDirectiveNatPair : Delab := do
  let e ← getExpr

  match_expr e with
  | Prod.mk alpha beta dExpr nExpr =>
    if !(alpha.isConstOf ``Directive && beta.isConstOf ``Nat) then
      failure

    -- Evaluates closed Directive parts and uses the normal formatter
    let dStr ← if !dExpr.hasFVar && !dExpr.hasMVar then
      let typeExpr ← Meta.inferType dExpr
      let d ← Meta.evalExpr Directive typeExpr dExpr
      pure s!"{d}"
    else
      -- Unfold let-bound variables (zeta reduction) and instantiate metavariables
      let dExprUnfolded ← Meta.zetaReduce (← instantiateMVars dExpr)
      let fmt ← PrettyPrinter.ppExpr dExprUnfolded
      pure s!"{fmt}"

    -- Extract the Nat index/offset from nExpr
    let idxStr ← if let some n := getNatVal? nExpr then
      pure s!"#{n}"
    else match nExpr with
      | Expr.app _ arg =>
        if let some n := getNatVal? arg then
          pure s!"#{n}"
        else
          -- We want to delaborate `arg`.
          -- Step into nExpr (1st withAppArg), then step into arg (2nd withAppArg)
          let idxStx ← withAppArg (withAppArg delab)
          let fmt ← PrettyPrinter.ppTerm idxStx
          pure s!"{fmt}"
      | _ =>
        -- We want to delaborate `nExpr`.
        -- Step into nExpr (withAppArg)
        let idxStx ← withAppArg delab
        let fmt ← PrettyPrinter.ppTerm idxStx
        pure s!"{fmt}"

    return Syntax.mkStrLit s!"@{idxStr}: {dStr}"

  | _ => failure

-- Helper to delaborate program listing-style lists.
partial def delabProgramListGo : DelabM (List Term) := do
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

/-
   Delaborates lists of Directives or (Directive × Nat)s as program listings.

   This formats programs in the context like:
          [asm|
              "mov QWORD PTR [rdi+0], rax"
              "mov QWORD PTR [rdi+8], rcx"
              "mov r12, QWORD PTR [rdi+0]"
              "mov r13, QWORD PTR [rdi+8]"]

   and with delabDirectiveNatPair, it formats (Directive × Nat)s as:

    [asm_layout|
        "@#0: mov QWORD PTR [rdi+0], rax"
        "@#1: mov QWORD PTR [rdi+8], rcx"
        "@#2: mov r12, QWORD PTR [rdi+0]"
        "@#3: mov r13, QWORD PTR [rdi+8]"]

   It's `unsafe` because of `Meta.evalExpr` as above.
-/
@[app_delab List.cons]
unsafe def delabProgramList : Delab := do
  let e ← getExpr

  match_expr e with
  | List.cons alpha _head _tail =>
    -- List Directive (Program)
    if alpha.isConstOf ``Directive then
      if !e.hasFVar && !e.hasMVar then
        let typeExpr ← Meta.inferType e
        let prog ← Meta.evalExpr (List Directive) typeExpr e
        let lines := prog.map (fun d => s!"{d}")
        let linesStx : Array Syntax := lines.map (fun line => Syntax.mkStrLit line) |>.toArray
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

    -- List (Directive × Nat) (Layout)
    else if ← isDirectiveNatType alpha then
      if !e.hasFVar && !e.hasMVar then
        let typeExpr ← Meta.inferType e
        let prog ← Meta.evalExpr (List (Directive × Nat)) typeExpr e
        let lines := prog.map (fun (d, sz) => s!"{d}  [size: {sz}]")
        let linesStx : Array Syntax := lines.map (fun line => Syntax.mkStrLit line) |>.toArray
        let node := Syntax.node SourceInfo.none ``asmSym #[
          Syntax.atom SourceInfo.none "[asm|",
          Syntax.node SourceInfo.none nullKind linesStx,
          Syntax.atom SourceInfo.none "]"
        ]
        return ⟨node⟩
      else
        let elems ← delabProgramListGo
        let elemsArr : Array Syntax := elems.map (·.raw) |>.toArray
        let node := Syntax.node SourceInfo.none ``asmLayoutSym #[
          Syntax.atom SourceInfo.none "[asm_layout|",
          Syntax.node SourceInfo.none nullKind elemsArr,
          Syntax.atom SourceInfo.none "]"
        ]
        return ⟨node⟩

    else
      failure

  | _ => failure
