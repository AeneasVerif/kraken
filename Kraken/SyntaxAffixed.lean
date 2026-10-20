module

/-
Kraken SyntaxAffixed - Keyword Families

The `declare_affixes` and `syntax_affixed` commands declare families of non-reserved keywords
(`x0`..`x30`, `add`/`adds`, `b.eq`..`b.le`, ...) from a stem and sets of prefixes and suffixes, and
`splitAffixed` recovers the parts in the elaborator.
-/

public import Lean
public meta import Lean

open Lean

namespace Kraken

/-- An affix set: an array of `(affix, optional docstring)` pairs, used as the prefixes or the suffixes
    of a family of keywords. -/
public meta abbrev AffixSet := Array (String × Option String)

/-- A `|`-prefixed string literal with an optional docstring (`| /-- ... -/ "s"`). -/
declare_syntax_cat doc_str_item
syntax "|" (Parser.Command.docComment)? str : doc_str_item

/-- Elaborate a `doc_str_item` syntax node into a `(String × Option String)` term. -/
private meta def elabDocStrItem (item : TSyntax `doc_str_item) :
    Elab.Command.CommandElabM (TSyntax `term) :=
  match item with
  | `(doc_str_item| | $[$d?:docComment]? $s:str) => do
    let doc? ← d?.mapM getDocStringText
    `(term| ($s, $(quote doc?)))
  | _ => Elab.throwUnsupportedSyntax

/-- Declare a reusable named affix set with per-affix docstrings, optionally extending other sets. -/
syntax (name := declareAffixes) (Parser.Command.docComment)? "declare_affixes " ident (" extends " ident,+)? doc_str_item+ : command
elab_rules (kind := declareAffixes) : command
  | `(declareAffixes| $[$doc?]? declare_affixes $name $[extends $parents?,*]? $items*) => do
    let parents := parents?.getD ∅ |>.getElems
    let pairs ← items.mapM elabDocStrItem
    Elab.Command.elabCommand (← `(command|
      $[$doc?:docComment]?
      private meta def $name : AffixSet := #[ $[$parents],* ].flatten ++ #[ $[$pairs],* ]
    ))

/-- Evaluate the name of an affix set; an omitted set stands for the empty affix alone. -/
private meta def evalAffixSet (set? : Option Ident) : Elab.Command.CommandElabM AffixSet :=
  match set? with
  | none => pure #[("", none)]
  | some set => Elab.Command.liftTermElabM <|
    -- safety: Safe since `mkConst ``AffixSet` reflects `AffixSet`.
    unsafe Elab.Term.evalTerm AffixSet (mkConst ``AffixSet) set

/-- Declare a non-reserved keyword syntax `pre ++ stem ++ sfx : cat` for every prefix `pre` and suffix
    `sfx` of the given affix sets (an omitted set or stem is empty), concatenating the docstrings of the
    command, the prefix and the suffix. Each syntax kind is named ``cat.affixed.«pre|stem|sfx»``, so that
    `splitAffixed` can recover the parts in the elaborator. -/
syntax (name := syntaxAffixed) (Parser.Command.docComment)? "syntax_affixed "
  (atomic(" (" &"prefixes" " := ") ident ") ")? (atomic(" (" &"suffixes" " := ") ident ") ")?
  (str)? " : " ident : command
elab_rules (kind := syntaxAffixed) : command
  | `(syntaxAffixed| $[$doc?]? syntax_affixed $[(prefixes := $pres?)]? $[(suffixes := $sfxs?)]? $[$stem?]? : $cat) => do
    let headDoc? ← doc?.mapM getDocStringText
    let stem := (stem?.map (·.getString)).getD ""
    let catParser := mkIdent (cat.getId.appendAfter "_parser")
    for (pre, preDoc?) in ← evalAffixSet pres? do
      for (sfx, sfxDoc?) in ← evalAffixSet sfxs? do
        let keyword := pre ++ stem ++ sfx
        let kind := (cat.getId.str "affixed").str s!"{pre}|{stem}|{sfx}"
        let docs := [headDoc?, preDoc?, sfxDoc?].filterMap id
        let doc? := if docs.isEmpty then none else some (mkMarkdownDocComment ("\n\n".intercalate docs))
        -- The expansion of `syntax (name := kind) &keyword : cat`, except that keywords containing a `.`
        -- (such as `b.eq`) tokenize as hierarchical identifiers, which the keyword index of the category
        -- cannot look up, so they are also dispatched on identifiers (`nonReservedSymbol`'s `includeIdent`,
        -- which the `syntax` command cannot express).
        Elab.Command.elabCommand (← `(command|
          $[$doc?:docComment]? @[$catParser:ident] public meta def $(mkIdent kind) : Lean.ParserDescr :=
            ParserDescr.node $(quote ((← getCurrNamespace) ++ kind)) Lean.Parser.leadPrec
              (ParserDescr.nonReservedSymbol $(quote keyword) $(quote (keyword.contains '.')))))

public meta section

open Elab Term

/-- Extract the `(prefix, stem, suffix)` triple from a syntax node declared via `syntax_affixed`. -/
def splitAffixed (stx : Syntax) : TermElabM (String × String × String) := withRef stx do
  let .str (.str _ "affixed") parts := stx.getKind | throwError "expected affixed keyword"
  let [pre, stem, sfx] := parts.splitOn "|" | throwError "expected affixed keyword"
  pure (pre, stem, sfx)

def splitSuffixed (stx : Syntax) : TermElabM (String × String) := do
  let (pre, stem, sfx) ← splitAffixed stx
  pure (pre ++ stem, sfx)

def getAffixedPrefix (stx : Syntax) : TermElabM String := do
  let (pre, _, _) ← splitAffixed stx
  return pre

def getAffixedStem (stx : Syntax) : TermElabM String := do
  let (_, stem, _) ← splitAffixed stx
  return stem

def getAffixedSuffix (stx : Syntax) : TermElabM String := do
  let (_, _, sfx) ← splitAffixed stx
  return sfx

end

end Kraken
