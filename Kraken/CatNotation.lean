module

public import Lean
public meta import Lean

/-!
The generic, language-independent `notation ... in c` command, prototyped in LeanScratchpad
(`CatNotation.lean`). Nothing in this file may be specific to a language: it is meant to be upstreamed to Lean
eventually. Changes since the copy: `(priority := p)` and `(print := false)`; the items `&"s"`, `noWs`, `lineEq` and fixed
numerals; and printing with a delaborator, so that a right-hand side may fix implicit arguments.

`notation ... in c`, a variant of Lean's `notation` for custom syntax
categories. `notation items in c => rhs` adds one rule to category `c`, and like `notation` it
derives parsing (a `syntax` rule plus `macro_rules`) and printing from the single declaration. An
item `x:d` is a variable of category `d`; the other items are listed at `item` below.

Every variable must occur on the right-hand side. Two kinds of rules switch between Lean and a
custom category `c`: `entry_notation items => x` with `x:c` is a term that contains a `c` (named
`c.entry`), and `escape_notation items in c => e` with `e:term` is a `c` that contains a Lean term
(named `c.escape`). A rule `n:num in c => ...` or `x:ident in c => ...` shows numerals or strings
in `c`. For these rules, the printer uses builders `c.entry.mk`, `c.escape.mk`, `c.ofNum` and
`c.ofIdent`, which apply the rule to a syntax tree; all other rules are named by `syntax`.

Printing works like `notation`'s unexpanders (`mkUnexpander`), with one difference: the pattern
is matched against all arguments of the application, implicit ones included, instead of against
the application as printed (which leaves them out). So a right-hand side `@f a₁ … aₙ` gives the
arguments for all of `f`'s parameters, and `f a₁ … aₙ` for its explicit ones, with any argument
for an implicit parameter accepted, as with `notation`. This tells apart rules that differ only
in an implicit argument, such as the index of an indexed family:
`@RegOrMem.mem Width.W8 m` only prints terms of type `RegOrMem Width.W8`.

The printer of a rule uses the switches and literal rules declared before it. The entry of a
rule's category is required; values that need a missing escape or literal rule are printed as
ordinary Lean terms.
-/

/-! ## `notation ... in c` (generic) -/
namespace CatNotation
open Lean Elab Command PrettyPrinter

public meta section

/-- `ident_str% x` is the identifier `x` as a string literal. -/
macro "ident_str% " x:ident : term =>
  pure (Syntax.mkStrLit (x.getId.eraseMacroScopes.toString false))

/-! ### Printing helpers, used by the generated unexpanders -/

/-- Shows an argument, already printed as a term, in category `cat`: an entry `[cat| s]` is
unwrapped, numerals, strings (as identifiers) and other terms are switched into `cat` with the
given builders. Fails if the needed builder is missing. -/
def toCat (cat : Name) (num? str? esc? : Option (Syntax → Syntax)) (e : Syntax) : Option Syntax :=
  if e.isOfKind (cat ++ `entry) then e.getArgs.find? (!·.isAtom)
  else if let (some f, true) := (num?, e.isOfKind numLitKind) then some (f e)
  else if let (some f, some s) := (str?, e.isStrLit?) then some (f (mkIdent (.mkSimple s)))
  else esc?.map (· e)

def numeral (e : Syntax) : Option Syntax := if e.isOfKind numLitKind then some e else none

def get? : Option Syntax → UnexpandM Syntax
  | some s => pure s
  | none => throw ()

open Delaborator SubExpr in
/-- The printer of a rule for the function `f`: prints all arguments of the application, implicit
ones included, and applies `unexpand` to `f a₁ … aₙ`. Fails if `unexpand` does, so that the
next delaborator for `f` is tried. -/
def delabAllArgs (unexpand : Unexpander) : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  -- Full names, so that constants match the pattern whatever namespaces are open.
  let args ← withTheReader Core.Context (fun c => { c with options := pp.fullNames.set c.options true }) do
    (Array.range e.getAppNumArgs).mapM fun i => withNaryArg i delab
  let some f := e.getAppFn.constName? | failure
  match unexpand (Syntax.mkApp (mkIdent f) args) |>.run .missing |>.run () with
  | .ok stx _ => pure ⟨stx⟩
  | _ => failure

/-- The binder infos of the parameters of a function of type `t`. -/
def binderInfos : Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: binderInfos b
  | _ => []

/-! ### The commands -/

/-- Items: a token `"s"`, a non-reserved token `&"s"` (matched as an identifier, so `s` stays
usable as one), `noWs` (no whitespace before the next item), `lineEq` (the next item is on the
line of the rule's first item), a fixed numeral such as `0x67`
(read as a `num`, but only this spelling is accepted), or a variable `x:cat`. -/
syntax item := str <|> ("&" str) <|> &"noWs" <|> &"lineEq" <|> num <|> (ident ":" ident)
/-- `(print := false)` makes the rule parse-only: it gets no printer, so the printer uses other
rules for the same terms, whatever the order of declaration. -/
syntax printOpt := atomic("(" &"print") " := " &"false" ")"
/-- `(priority := p)` is passed on to `syntax`: of two rules that read the same input, the parser
takes the one with the higher priority. -/
syntax "notation " (Lean.Parser.Command.namedPrio)? (printOpt)? item* " in " ident " => " term :
  command
syntax "entry_notation " item* " => " term : command
syntax "escape_notation " item* " in " ident " => " term : command

inductive Item where
  | tok (s : StrLit)
  | nonReserved (s : StrLit)
  | noWs
  | lineEq
  | numeral (n : NumLit)
  | var (x : Ident) (cat : Name)

/-- An `item` node holds one alternative: `str`, `group` (of `&` and `str`, or of `x`, `:`, `d`),
`token.noWs`, `token.lineEq`, or `num`. -/
def Item.ofSyntax (stx : TSyntax ``item) : Item :=
  let a := stx.raw[0]
  if a.isOfKind strLitKind then .tok ⟨a⟩
  else if a.isOfKind numLitKind then .numeral ⟨a⟩
  else if a.isOfKind `token.noWs then .noWs
  else if a.isOfKind `token.lineEq then .lineEq
  else if a[0].isToken "&" then .nonReserved ⟨a[1]⟩
  else .var ⟨a[0]⟩ a[2].getId.eraseMacroScopes

/-- For the printer: the syntax of a token or numeral item, `none` for `noWs` and `lineEq` (which leave no
node) and variables. A non-reserved token is read as an identifier but stored as an atom
(`nonReservedSymbolFnAux`), so it prints like a token. -/
def Item.printFixed? : Item → CommandElabM (Option Term)
  | .tok s | .nonReserved s => some <$> `(Lean.mkAtom $(quote s.getString.trimAscii.toString))
  | .numeral n => some <$> `(Lean.Syntax.mkNumLit $(quote n.raw[0].getAtomVal))
  | _ => pure none

/-- What the printer may use a rule for. -/
inductive Role where
  | plain
  /-- `entry_notation`: a term that contains category `c` -/
  | entry (c : Name)
  /-- `escape_notation`: the rule's category contains a term -/
  | escape
  /-- `n:num in c` or `x:ident in c`: shows numerals or strings in the rule's category -/
  | literal (lit : Name)

/-- A rule `items in cat => rhs`. -/
structure Rule where
  cat : Name
  items : Array Item
  rhs : Term
  role : Role
  prio? : Option (TSyntax `prio) := none

/-- Entries and escapes have fixed names; other rules are named by `syntax`. -/
def Rule.kind? (r : Rule) : Option Name := match r.role with
  | .entry c => some (c ++ `entry)
  | .escape => some (r.cat ++ `escape)
  | _ => none

/-- The function that applies the rule to a syntax tree, for rules the printer uses. -/
def Rule.builder? (r : Rule) : Option Name := match r.role with
  | .entry c => some (c ++ `entry ++ `mk)
  | .escape => some (r.cat ++ `escape ++ `mk)
  | .literal `num => some (r.cat ++ `ofNum)
  | .literal _ => some (r.cat ++ `ofIdent)
  | .plain => none

def Rule.varCat? (r : Rule) (x : Syntax) : Option Name := r.items.findSome? fun
  | .var y d => if y.getId == x.getId then some d else none
  | _ => none

/-- Checks the rule and determines its role. `switch` is `entry`, `escape`, or `anonymous`. -/
def Rule.mk? (switch cat : Name) (items : Array Item) (rhs : Term) : CommandElabM Rule := do
  for item in items do
    if let .var x _ := item then
      unless (rhs.raw.find? (·.getId == x.getId)).isSome do
        throwErrorAt x "variable `{x}` does not occur on the right-hand side"
  let r : Rule := { cat, items, rhs, role := .plain }
  let d? := r.varCat? rhs
  let role : Role ←
    if switch == `entry then
      match d? with
      | some d =>
        if [`term, `num, `ident, `str].contains d then
          throwErrorAt rhs "an `entry_notation` must switch into a custom category"
        pure (.entry d)
      | none => throwErrorAt rhs "the right-hand side of an `entry_notation` must be a variable"
    else if switch == `escape then
      match d? with
      | some `term => pure .escape
      | some _ => throwErrorAt rhs "an `escape_notation` must switch to `term`"
      | none => throwErrorAt rhs "the right-hand side of an `escape_notation` must be a variable"
    else if let #[.var _ l] := items then
      pure (if [`num, `ident].contains l then .literal l else .plain)
    else pure .plain
  if role matches .plain && d?.isSome then
    throwErrorAt rhs "a notation that switches categories must be an `entry_notation` or an \
      `escape_notation`"
  let r := { r with role }
  if let some b := r.builder? then
    if (← getEnv).contains b then
      throwError match role with
        | .entry c => m!"there already is an `entry_notation` for `{c}`"
        | .escape => m!"there already is an `escape_notation` for `{cat}`"
        | _ => m!"there already is a notation for these literals in `{cat}`"
  return r

def antiquot (x : Syntax) : Syntax := Syntax.mkAntiquotNode `term x (isPseudoKind := true)

/-- Parsing: the `syntax` rule; returns its syntax node kind. -/
def Rule.addSyntax (r : Rule) : CommandElabM Name := do
  let items : Array (TSyntax `stx) ← r.items.mapM fun
    | .tok s => `(stx| $s:str)
    | .nonReserved s => `(stx| & $s:str)
    | .noWs => `(stx| noWs)
    | .lineEq => `(stx| lineEq)
    | .numeral _ => `(stx| num)
    | .var _ d => `(stx| $(mkIdent d):ident)
  -- A rule with `lineEq` saves its own position, so `lineEq` refers to the rule's first item.
  let items ← if r.items.any (· matches .lineEq) then pure #[← `(stx| withPosition($[$items]*))]
    else pure items
  let name? := r.kind?.map mkIdent
  Command.elabSyntax
    (← `(syntax $[(name := $name?)]? $[(priority := $r.prio?)]? $[$items]* : $(mkIdent r.cat)))

/-- Translation: a macro that substitutes the variables into `rhs`. A fixed numeral is part of
the pattern, so other spellings of a numeral don't match. -/
def Rule.addMacro (r : Rule) (kind : Name) : CommandElabM Unit := do
  let pat : Term := ⟨mkNode kind (r.items.filterMap fun
    | .tok s | .nonReserved s => some (mkAtom s.getString.trimAscii.toString)
    | .noWs | .lineEq => none
    | .numeral n => some n.raw
    | .var x _ => some (antiquot x))⟩
  let rhs : Term := ⟨Id.run <| r.rhs.raw.replaceM fun s =>
    pure (if (r.varCat? s).isSome then some (antiquot s) else none)⟩
  elabCommand (← `(macro_rules | `($pat) => ``($rhs)))

/-- For rules the printer uses: the builder, which applies the rule to a syntax tree. -/
def Rule.addBuilder (r : Rule) (kind : Name) : CommandElabM Unit := do
  let some b := r.builder? | return
  let x := mkIdent `x
  let args : Array Term ← r.items.filterMapM fun
    | .var .. => pure (some x)
    | item => item.printFixed?
  elabCommand (← `(def $(mkIdent (`_root_ ++ b)) ($x : Lean.Syntax) : Lean.Syntax :=
    Lean.mkNode $(quote kind) #[$args,*]))

/-- Printing: an unexpander, derived from `rhs` like `notation` does (`mkUnexpander`), that also
switches each variable into its category and the result into `term`. It is applied by a
delaborator to all arguments, implicit ones included (`delabAllArgs`). -/
def Rule.addUnexpander (r : Rule) (kind : Name) : CommandElabM Unit := do
  if r.role matches .entry _ | .escape then return
  let env ← getEnv
  let builder? (n : Name) : CommandElabM Term :=
    if env.contains n then `(some $(mkIdent n)) else `(none)
  unless env.contains (r.cat ++ `entry ++ `mk) do return
  let qrhs : Term := ⟨Id.run <| r.rhs.raw.replaceM fun s =>
    pure (if (r.varCat? s).isSome then some (antiquot s) else none)⟩
  let (c, args, explicit) ← match qrhs with
    | `(@$c:ident $args*) => pure (c, args, true)
    | `($c:ident $args*) => pure (c, args, false)
    | `($c:ident) => pure (c, #[], false)
    | _ => return
  let [(c, [])] ← liftMacroM <| Macro.resolveGlobalName c.getId | return
  -- Named arguments (`(x := e)`) are not supported by the printer; use `@f` instead.
  if args.any (·.raw.isOfKind ``Lean.Parser.Term.namedArgument) then return
  let args ← liftMacroM <| args.mapM removeParentheses
  if hasDuplicateAntiquot args then return
  -- Constants in the pattern by their full names, as `delabAllArgs` prints them.
  let args ← args.mapM fun a => liftMacroM <| a.replaceM fun
    | s@(.node ..) => pure (if s.isAntiquot then some s else none)
    | .ident _ _ n _ => do
      match ← Macro.resolveGlobalName n with
      | [(c, [])] => pure (some (mkIdent c))
      | _ => pure none
    | _ => pure none
  -- One pattern per argument of the application: `@f a₁ … aₙ` gives all of them; `f a₁ … aₙ`
  -- the explicit ones, and any argument is accepted for an implicit parameter before them.
  let args : Array Syntax ← if explicit then pure args else do
    let mut out := #[]
    let mut rest := args.toList
    for bi in binderInfos (← getConstInfo c).type do
      let some a := rest.head? | break
      if bi.isExplicit then
        out := out.push a
        rest := rest.tail
      else
        out := out.push (antiquot (mkIdent (.mkSimple s!"_implicit{out.size}")))
    pure out
  let outs : Array Term ← r.items.filterMapM fun
    | .var x `num => some <$> `((← CatNotation.get? (CatNotation.numeral ($x).raw)))
    | .var x d => some <$> do
      if [`ident, `str, `term].contains d then `(($x).raw) else
      `((← CatNotation.get? (CatNotation.toCat $(quote d) $(← builder? (d ++ `ofNum))
        $(← builder? (d ++ `ofIdent)) $(← builder? (d ++ `escape ++ `mk)) ($x).raw)))
    | item => item.printFixed?
  let lhs := Syntax.mkApp (← `($$f:ident)) (args.map (⟨·⟩))
  let enter := mkIdent (r.cat ++ `entry ++ `mk)
  let un := mkIdent (kind ++ `unexpand)
  elabCommand (← `(def $un : Lean.PrettyPrinter.Unexpander
    | `($lhs) => do pure (⟨$enter (Lean.mkNode $(quote kind) #[$outs,*])⟩ : Lean.Term)
    | _ => throw ()))
  elabCommand (← `(@[delab $(mkIdent (`app ++ c)):ident]
    def $(mkIdent (kind ++ `delab)) : Lean.PrettyPrinter.Delaborator.Delab :=
      CatNotation.delabAllArgs $un))

def elabRule (switch : Name) (items : TSyntaxArray ``item) (cat : Ident) (rhs : Term)
    (prio? : Option (TSyntax `prio) := none) (print := true) : CommandElabM Unit := do
  let r ← Rule.mk? switch cat.getId.eraseMacroScopes (items.map Item.ofSyntax) rhs
  let r := { r with prio? }
  let kind ← r.addSyntax
  r.addMacro kind
  r.addBuilder kind
  if print then r.addUnexpander kind

elab_rules : command
  | `(notation $[(priority := $p?)]? $[$po?:printOpt]? $items* in $cat => $rhs) =>
    elabRule .anonymous items cat rhs p? (print := po?.isNone)
  | `(entry_notation $items* => $rhs) => elabRule `entry items (mkIdent `term) rhs
  | `(escape_notation $items* in $cat => $rhs) => elabRule `escape items cat rhs

end

end CatNotation
