module

public import LeanQbe.Rega
public import LeanQbe.Spill
public import LeanQbe.Opt

/-!
# The pipeline (QBE `main.c`)

`compileFn I f`: the verified mid-end `Func.opt` (fold, CSE, fold), then the untrusted allocation
oracle `Spill.hints`, then the verified lowering `Rega.lowerFn`. The theorem is in `MainLemmas.lean`.
Calls, exits and spills come in step 3.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- The function after the mid-end. -/
def Fn.opt (f : Fn) : Fn := ⟨f.name, Func.opt f.body⟩

/-- Compile one function. -/
def compileFn (I : Isa) (f : Fn) : Except String (List I.Directive) :=
  Rega.lowerFn (Spill.hints I f.opt) f.opt

/-- Compile a list of functions to one list of directives. -/
def compile (I : Isa) : List Fn → Except String (List I.Directive)
  | [] => .ok []
  | f :: fs =>
    match compileFn I f, compile I fs with
    | .ok c, .ok cs => .ok (c ++ cs)
    | .error e, _ => .error s!"{f.name}: {e}"
    | _, .error e => .error e

end LeanQbe
