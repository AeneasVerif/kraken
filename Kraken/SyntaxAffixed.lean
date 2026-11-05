module

/-
Kraken SyntaxAffixed - Keyword Families

The `declare_affixes` and `syntax_affixed` commands declare families of non-reserved keywords
(`x0`..`x30`, `add`/`adds`, `b.eq`..`b.le`, ...) from a stem and sets of prefixes and suffixes, and
`splitAffixed` recovers the parts in the elaborator.
-/

public import Lean
public meta import Lean

open Lean Elab Command

namespace Kraken

/-- An affix set: an array of `(affix, optional docstring)` pairs, used as the prefixes or the suffixes
    of a family of keywords. -/
public meta abbrev AffixSet := Array (String × Option String)

meta section

/-- The affix sets declared with `declare_affixes`, keyed by the name of the constant that
    `declare_affixes` declares for navigation and documentation purposes. -/
initialize affixSetsExt : SimplePersistentEnvExtension (Name × AffixSet) (NameMap AffixSet) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun sets (name, set) => sets.insert name set
    addImportedFn := mkStateFromImportedEntries (fun sets (name, set) => sets.insert name set) {}
  }

/-- The affix set named `id`, resolved like any identifier (which also makes hover and go-to-definition
    work on it). -/
private def getAffixSet (id : Ident) : CommandElabM AffixSet := do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some set := (affixSetsExt.getState (← getEnv)).find? name
    | throwErrorAt id "`{id.getId}` is not an affix set"
  pure set

/-- A `|`-prefixed string literal with an optional docstring (`| /-- ... -/ "s"`). -/
declare_syntax_cat doc_str_item
syntax "|" (Parser.Command.docComment)? str : doc_str_item

/-- Evaluate a `doc_str_item` syntax node into its `(affix, optional docstring)` pair. -/
private def evalDocStrItem (item : TSyntax `doc_str_item) : CommandElabM (String × Option String) :=
  match item with
  | `(doc_str_item| | $[$d?:docComment]? $s:str) => return (s.getString, ← d?.mapM getDocStringText)
  | _ => throwUnsupportedSyntax

/-- Declare a reusable named affix set with per-affix docstrings, optionally extending other sets. The
    set is stored in `affixSetsExt`; a constant of the same name is declared alongside so that the set
    can be hovered, documented, navigated to and referred to from other modules like any definition. -/
syntax (name := declareAffixes) (Parser.Command.docComment)? "declare_affixes " ident (" extends " ident,+)? doc_str_item+ : command
elab_rules (kind := declareAffixes) : command
  | `(declareAffixes| $[$doc?]? declare_affixes $name $[extends $parents?,*]? $items*) => do
    let parents ← (parents?.getD ∅).getElems.mapM getAffixSet
    let set : AffixSet := parents.flatten ++ (← items.mapM evalDocStrItem)
    elabCommand (← `(command| $[$doc?:docComment]? public meta def $name : AffixSet := $(quote set)))
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
    modifyEnv (affixSetsExt.addEntry · (declName, set))

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
    -- An omitted affix set stands for the empty affix alone.
    let affixes (set? : Option Ident) : CommandElabM AffixSet := set?.mapM getAffixSet <&> (·.getD #[("", none)])
    for (pre, preDoc?) in ← affixes pres? do
      for (sfx, sfxDoc?) in ← affixes sfxs? do
        let keyword := pre ++ stem ++ sfx
        -- `syntax` would reject such atoms; we bypass it (see below), so check here.
        if keyword.isEmpty then
          throwError "`syntax_affixed` cannot declare an empty keyword: give a stem, prefixes or suffixes"
        if keyword.any Char.isWhitespace then
          throwError "`syntax_affixed` cannot declare the keyword {keyword.quote}: keywords cannot contain whitespace"
        let kind := (cat.getId.str "affixed").str s!"{pre}|{stem}|{sfx}"
        let docs := [headDoc?, preDoc?, sfxDoc?].filterMap id
        let doc? := if docs.isEmpty then none else some (mkMarkdownDocComment ("\n\n".intercalate docs))
        -- The expansion of `syntax (name := kind) &keyword : cat`, except that keywords containing a `.`
        -- (such as `b.eq`) tokenize as hierarchical identifiers, which the keyword index of the category
        -- cannot look up, so they are also dispatched on identifiers (`nonReservedSymbol`'s `includeIdent`,
        -- which the `syntax` command cannot express).
        elabCommand (← `(command|
          $[$doc?:docComment]? @[$catParser:ident] public meta def $(mkIdent kind) : Lean.ParserDescr :=
            ParserDescr.node $(quote ((← getCurrNamespace) ++ kind)) Lean.Parser.leadPrec
              (ParserDescr.nonReservedSymbol $(quote keyword) $(quote (keyword.contains '.')))))

end

public meta section

open Term

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
