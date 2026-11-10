module

public import LeanQbe.Rega
public import LeanQbe.Spill
public import LeanQbe.Opt

/-!
# The pipeline (QBE `main.c`)

`compileFn I f`: the verified mid-end `Func.opt` (fold, CSE, fold), then the untrusted allocation
oracle `Spill.hints`, then the verified lowering `Rega.lowerFn`. The theorem is in `MainLemmas.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- Symbols called by an expression. -/
def Expr.callees : Expr Unit Unit → List String
  | .param f | .let_ _ f | .load _ _ _ _ f | .label f => Expr.callees (f ())
  | .store _ _ _ k => Expr.callees k
  | .call g _ k => g :: Expr.callees k
  | .jnz _ t e => Expr.callees t ++ Expr.callees e
  | .block b rest => Expr.callees b ++ Expr.callees rest
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => []

/-- Exit targets of an expression. -/
def Expr.exits : Expr Unit Unit → List String
  | .param f | .let_ _ f | .load _ _ _ _ f | .label f => Expr.exits (f ())
  | .store _ _ _ k | .call _ _ k => Expr.exits k
  | .jnz _ t e => Expr.exits t ++ Expr.exits e
  | .block b rest => Expr.exits b ++ Expr.exits rest
  | .exit g _ => [g]
  | .jump _ _ | .ret _ | .hlt => []

/-- The function after the mid-end. -/
def Fn.opt (f : Fn) : Fn := ⟨f.name, Func.opt f.body⟩

/-- What a function may call and exit to. -/
def Fn.ext (f : Fn) : Rega.Ext :=
  ⟨Expr.callees (f.body Unit Unit), Expr.exits (f.body Unit Unit)⟩

/-- Hints used by `compileFn`. -/
def Fn.hints (I : Isa) (f : Fn) : Rega.Hints I := Spill.hints I f.opt

/-- Spill-slot count of the compiled function. -/
def Fn.nslots (I : Isa) (f : Fn) : Nat := (f.hints I).nslots

/-- Compile one function. -/
def compileFn (I : Isa) (f : Fn) : Except String (List I.Directive) :=
  Rega.lowerFn (f.hints I) f.opt.ext f.opt

/-- Compile a list of functions to one list of directives. -/
def compile (I : Isa) : List Fn → Except String (List I.Directive)
  | [] => .ok []
  | f :: fs =>
    match compileFn I f, compile I fs with
    | .ok c, .ok cs => .ok (c ++ cs)
    | .error e, _ => .error s!"{f.name}: {e}"
    | _, .error e => .error e

end LeanQbe
