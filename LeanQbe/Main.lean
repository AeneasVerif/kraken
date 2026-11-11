module

public import LeanQbe.Rega
public import LeanQbe.Spill
public import LeanQbe.Opt

/-!
# The pipeline (QBE `main.c`)

`compileFn I f`: the verified mid-end `Func.opt` (fold, CSE, fold), then the untrusted allocation
oracle `Spill.hints`, then the verified lowering `Rega.lowerFn`. `compileModule` compiles an acyclic
list of functions and computes and checks their stack bounds automatically. The theorems are in
`MainLemmas.lean`.
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

/-- Total 8-byte frame slots of the compiled function (spill slots + saved callee-saved regs). -/
def Fn.nslots (I : Isa) (f : Fn) : Nat := (f.hints I).totalSlots

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

/-- Look up a stack bound in an association list. -/
def lookupBound (bounds : List (String × Nat)) (g : String) : Option Nat :=
  (bounds.find? (fun p => p.1 == g)).map Prod.snd

/-- Compute the required stack bound for `f` given `bounds` of already-available callees,
or fail if a callee is missing. -/
def calleesBound (F raBytes : Nat) (bounds : List (String × Nat)) :
    List String → Option Nat
  | [] => some F
  | g :: gs =>
    match lookupBound bounds g, calleesBound F raBytes bounds gs with
    | some bg, some rest => some (Nat.max (F + raBytes + bg) rest)
    | _, _ => none

/-- Compute and check the stack bound of `f` given `bounds` (external callees + earlier functions
in the module) and allowed `exits`. -/
def checkAndBound (I : Isa) (raBytes : Nat) (exits : List String) (nX : Nat)
    (bounds : List (String × Nat)) (f : Fn) : Option Nat :=
  match calleesBound (I.frameSize (f.nslots I)) raBytes bounds f.opt.ext.callees with
  | none => none
  | some n₁ =>
    if f.opt.ext.exits.all (fun g => decide (g ∈ exits)) then
      let n := if f.opt.ext.exits.isEmpty then n₁ else Nat.max n₁ nX
      if n + raBytes ≤ 2 ^ 64 then some n else none
    else none

/-- Compile an acyclic list of functions (callees first), computing and checking each function's
stack bound automatically. Returns the concatenated assembly directives and the `(name, stackBound)`
list for the compiled functions. -/
def compileModule (I : Isa) (raBytes : Nat) (extCallees : List (String × Nat))
    (exits : List String) (nX : Nat) :
    List Fn → Except String (List I.Directive × List (String × Nat))
  | [] => .ok ([], [])
  | f :: fs =>
    match compileFn I f, checkAndBound I raBytes exits nX extCallees f with
    | .ok c, some b =>
      match compileModule I raBytes ((f.name, b) :: extCallees) exits nX fs with
      | .ok (cs, bs) => .ok (c ++ cs, (f.name, b) :: bs)
      | .error e => .error e
    | .error e, _ => .error s!"{f.name}: {e}"
    | _, none => .error s!"{f.name}: unknown callee, undeclared exit, or stack overflow"

end LeanQbe
