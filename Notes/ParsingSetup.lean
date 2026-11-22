module

import Std.Internal.Parsec
public import Kraken.X64.Parser
public import Kraken.X64.Parser.Elab


/-!

## Parsing with the Lean frontend

Previously, our parsers were implemented as functions `parse : String → m Program`, using the
`Std.Internal.Parsec` framework. This function worked at the object level, but we used it at
the meta level, in combination with `Syntax.getString : Syntax → String` and `Lean.ToExpr : α → Expr`.
This setup allowed us to parse external files as well as enjoy a convenient syntax to build
`Program` terms. However, this setup prevented us from having antiqutations.

We would like to be able to state theorems like the following

```lean
theorem inc_inc {w : Width} (r : Reg w) :
    ⸨prog| add $2, %❰r❱⸩ = ⸨prog| inc %❰r❱; inc %❰r❱⸩ := by ...
```

However, with our old setup, we had no way to represent `r` in our model. In particular, our
`parse : String → m Program` function is constrainted to representing concrete programs for every
concrete string.

In order to support antiquotations (and a nicer syntax to embed various parts of the model),
we decided to implement the parser as a `parse : Syntax → m Expr` function. Now we are building
`Expr`s of type `Program` instead of `Program` objects directly, which allows us to embed expressions
of antiquotations directly, since we recieve them as abstract `Expr` types as well.

-/

section ShowcasingAntiquotations

open Lean Expr

/--
info: AddrExpr.mk (Option.some.{0} RegOrRip (RegOrRip.reg Reg64.rax)) (Option.none.{0} AddrIndex) (ConstExpr.int64 (OfNat.ofNat.{0} Int64 0 (Int64.instOfNat 0)))
-/
#guard_msgs in run_elab do
  let stx ← `(x64_mem| 0(%rax))
  let e ← (Kraken.X64.Parser.elabMem stx).run' (width? := some Width.W64)
  Lean.logInfo s!"{e}"

/--
info: AddrExpr.mk (Option.some.{0} RegOrRip (RegOrRip.reg Reg64.rax)) (Option.none.{0} AddrIndex) _uniq.2238
-/
#guard_msgs in run_elab Meta.withLocalDeclD `c (toTypeExpr ConstExpr) fun _ => do
    let stx ← `(x64_mem| ❰$(mkIdent `c)❱(%rax))
    let e ← (Kraken.X64.Parser.elabMem stx).run' (width? := some Width.W64)
    Lean.logInfo s!"{e}"

end ShowcasingAntiquotations


/-!

For the most part, we can use this new `Syntax → m Expr` function directly to cover all of the
usecases we had for the parser before, since most of our uses for it expected `Expr` at the end
of their pipeline anyways. However, for some usecases we still want to have a `String → m Program`
function. In these cases, we can build such a computation from `Syntax → m Expr` by using
`Lean.Parser.runParserCategory` to do `String → Syntax` and `evalExpr` to do `Expr → m Program`.

Notably, notice how the `evalExpr` step, we are going from the meta level `Expr` to the object
level `Program` type. This transformation is not generaly safe, since it requires that the user
provides a type `α` (in our case `Program`), and expects the invariant that the passed `Expr` is of
such type `α` to ensure the correctness of `evalExpr`. Therefore, for this step of the pipeline we
must use `unsafe ...` to wrap the `evalExpr` call.

-/

/--
info: Lean.Parser.runParserCategory (env : Lean.Environment) (catName : Lean.Name) (input : String)
  (fileName : String := "<input>") : Except String Lean.Syntax
-/
#guard_msgs in #check Lean.Parser.runParserCategory

/-- info: Kraken.X64.Parser.parse (input : String) : Except String Program -/
#guard_msgs in #check Kraken.X64.Parser.parse

/-!

Furthermore, the prior description only allows us to build `String → TermElabM Program`. To lower the
`TermElabM` monad to `IO`, we must build an environment to provide the `CoreM` monad. Building the
correct such `Environment` can be done by running

```lean
-- Ensure initializers are run whem importing `.olean` files.
enableInitializersExecution
-- Initialize the search path to ensure imports work properly
initSearchPath (← findSysroot) [← getLibDir (← getBuildDir)]
-- Create an `Environment` object  which imports the elaborator
let env ← importModules #[{ module := `Kraken.X64.Parser.Elab }] {} (loadExts := true)
```

-/

/-- info: Lean.enableInitializersExecution : BaseIO Unit -/
#guard_msgs in #check Lean.enableInitializersExecution
/--
info: Lean.initSearchPath (leanSysroot : System.FilePath) (sp : Lean.SearchPath := ∅) : IO Unit
-/
#guard_msgs in #check Lean.initSearchPath
/--
info: Lean.importModules (imports : Array Lean.Import) (opts : Lean.Options) (trustLevel : UInt32 := 0)
  (plugins : Array Lean.Plugin := #[]) (leakEnv loadExts : Bool := false)
  (level : Lean.OLeanLevel := Lean.OLeanLevel.private) (arts : Lean.NameMap Lean.ImportArtifacts := ∅) :
  IO Lean.Environment
-/
#guard_msgs in #check Lean.importModules


/-!

## Using Expr over Syntax for indirection

It is still not clear if writing an elaborator is best over a macro. The reason why
we need an elaborator to implement antiquotations is that representing our outputs as
`Expr` over `Program` allows us to encode `Program` objects, but also embed results
produced by other syntax. However, this same "indirection" could have been achieved
equivalently by using `Syntax` instead.

The main benefit of using `TermElabM` is that it is faster than `Syntax` to produce the
final output. Experimental benchmarks show a 30× performance improvement when using
elaborators. However, other benefits of using `TermElabM`, such as having access to the
`Environment`, are not taken advantage of at the time of writing.

The benefits of using `MacroM` over `TermElabM` are not easy to dimiss though. Using
`MacroM` ensures that our syntax can also be used in patterns, and syntax antiquotations
provide for a cleaner way of building `Syntax` objects over the explicit constructors or
buider functions needed for building `Expr` objects.

It remains to be explored whether it would make sense to target `Syntax` over `Expr`
for our elaboration.

-/
