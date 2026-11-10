module

public import LeanQbe.Rega

/-!
# The pipeline (QBE `main.c`)

Version 0: every function goes straight to `Rega.lowerFn` with its hints. Mid-end passes, the
allocation oracle (`Live`, `Spill`) and the module-level theorem (`MainLemmas`) come in step 3.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- A function together with its (untrusted) allocation hints. -/
structure FnHints (I : Isa) where
  fn : Fn
  hints : Rega.Hints I

/-- Compile a list of functions to one list of directives. -/
def compile {I : Isa} : List (FnHints I) → Except String (List I.Directive)
  | [] => .ok []
  | u :: us =>
    match Rega.lowerFn u.hints u.fn, compile us with
    | .ok c, .ok cs => .ok (c ++ cs)
    | .error e, _ => .error s!"{u.fn.name}: {e}"
    | _, .error e => .error e

end LeanQbe
