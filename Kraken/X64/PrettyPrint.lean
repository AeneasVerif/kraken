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

/-- Enables the `[asm| ...]` / `[asm_layout| ...]` listing pretty printer. Turn this
off (or use `pp.explicit`/`pp.all`) to see the underlying terms. -/
register_option pp.kraken.asm : Bool := {
  defValue := true
  descr := "(pretty printer) display lists of `Directive`s as assembly listings"
}

-- Output-only syntax: these are never written by hand; they exist so that the
-- delaborators below can emit nicely formatted listings.
syntax (name := asmSym) "[asm|" ppIndent((ppLine term)*) "]" : term
syntax (name := asmLayoutSym) "[asm_layout|" ppIndent((ppLine term)*) "]" : term

/-- `true` when the listing pretty printer should be used. -/
private def asmPPEnabled : DelabM Bool := do
  if (← getPPOption getPPExplicit) then return false
  return (← getOptions).getBool `pp.kraken.asm true

private def asmListing (kind : SyntaxNodeKind) (opener : String) (elems : Array Term) : Term :=
  ⟨Syntax.node SourceInfo.none kind #[
      Syntax.atom SourceInfo.none opener,
      Syntax.node SourceInfo.none nullKind (elems.map (·.raw)),
      Syntax.atom SourceInfo.none "]"]⟩

private def isDirectiveNatType (e : Expr) : Bool :=
  match_expr e with
  | Prod a b => a.isConstOf ``Directive && b.isConstOf ``Nat
  | _ => false

private def natLit? (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?

/-- Extracts `i` from `layout.size i`: `Layout.apply` tags the `i`-th directive of a
program with `layout.size i`, so this recovers the directive's index. -/
private def layoutIndex? (e : Expr) : Option Nat :=
  match_expr e with
  | Kraken.Layout.size _ _ i => natLit? i
  | _ => none

/-- Evaluates a *closed* expression of type `α` and renders it with `ToString`.
Returns `none` if the term is open or cannot be evaluated (it mentions `sorry`, an
axiom, a constant without executable code, ...) so that callers can fall back to
ordinary delaboration instead of failing to pretty print the whole goal. This
is unsafe because of Meta.evalExpr. -/
private unsafe def evalToStringImpl (α : Type) [ToString α] (typeName : Name) (e : Expr) :
    MetaM (Option String) := do
  if e.hasFVar || e.hasMVar then return none
  try
    return some (toString (← Meta.evalExpr' α typeName e))
  catch _ =>
    return none

@[implemented_by evalToStringImpl]
private def evalToString? (α : Type) [ToString α] (_typeName : Name) (_e : Expr) :
    MetaM (Option String) := return none

private def directiveStr? (e : Expr) : MetaM (Option String) :=
  evalToString? Directive ``Directive e

/-- Renders `e` on a single line using the ordinary pretty printer. -/
private def ppOneLine (e : Expr) : MetaM String := do
  let e ← Meta.zetaReduce (← instantiateMVars e)
  return (← PrettyPrinter.ppExpr e).pretty (width := 1000000)

/-- Renders a `(Directive × Nat)` layout entry. The current subterm must be the pair. -/
private def layoutEntryStr (dExpr nExpr : Expr) : DelabM String := do
  let dStr ← match ← directiveStr? dExpr with
    | some s => pure s
    | none => ppOneLine dExpr
  if let some i := layoutIndex? nExpr then
    return s!"@#{i}: {dStr}"
  else if let some n := natLit? nExpr then
    return s!"{dStr}  [size: {n}]"
  else
    -- Delaborate the size term itself rather than guessing at an index.
    let nStx ← withAppArg delab
    return s!"{dStr}  [size: {(← PrettyPrinter.ppTerm nStx).pretty (width := 1000000)}]"

/-- Delaborates individual `(Directive × Nat)` pairs as `"@#i: instruction"` (when the
size is `layout.size i`) or `"instruction  [size: n]"`. -/
@[app_delab Prod.mk]
def delabDirectiveNatPair : Delab := do
  unless ← asmPPEnabled do failure
  match_expr ← getExpr with
  | Prod.mk α β dExpr nExpr =>
    unless α.isConstOf ``Directive && β.isConstOf ``Nat do failure
    annotateTermInfo (Syntax.mkStrLit (← layoutEntryStr dExpr nExpr))
  | _ => failure

/-- Delaborates the spine of a list, returning its elements and, if the list does not
end in `[]`, its tail. -/
private partial def delabListSpine (elem : Delab) : DelabM (Array Term × Option Term) := do
  match_expr ← getExpr with
  | List.cons _ _ _ =>
    let hd ← withAppFn (withAppArg elem)
    let (tl, tail?) ← withAppArg (delabListSpine elem)
    return (#[hd] ++ tl, tail?)
  | List.nil _ => return (#[], none)
  | _ => return (#[], some (← delab))

/-- Renders a closed `Directive` as assembly text, and anything else structurally. -/
private def delabDirectiveElem : Delab := do
  match ← directiveStr? (← getExpr) with
  | some s => annotateTermInfo (Syntax.mkStrLit s)
  | none => delab

/-
   Delaborates lists of `Directive`s or `(Directive × Nat)`s as program listings:

          [asm|
              "mov QWORD PTR [rdi+0], rax"
              "mov QWORD PTR [rdi+8], rcx"]

   and, for layouts,

          [asm_layout|
              "@#0: mov QWORD PTR [rdi+0], rax"
              "@#1: mov QWORD PTR [rdi+8], rcx"]

   Elements are formatted individually, so a list with an unknown tail still shows
   the directives it does know:

          [asm| "mov r12, QWORD PTR [rdi+0]"] ++ rest
-/
@[app_delab List.cons]
def delabProgramList : Delab := do
  unless ← asmPPEnabled do failure
  match_expr ← getExpr with
  | List.cons α _ _ =>
    let (kind, opener, elem) ←
      if α.isConstOf ``Directive then
        pure (``asmSym, "[asm|", delabDirectiveElem)
      else if isDirectiveNatType α then
        pure (``asmLayoutSym, "[asm_layout|", (delab : Delab))
      else
        failure
    let (elems, tail?) ← delabListSpine elem
    let listing := asmListing kind opener elems
    match tail? with
    | none => return listing
    | some tail => `($listing ++ $tail)
  | _ => failure
