module

public import LeanQbe.Ops

/-!
# The IL term (QBE `all.h`: `Ins`, `Blk`, `Fn`)

A function is `∀ V L, Expr V L` (decision D1), a parametric higher-order abstract syntax (PHOAS) term in
the uniform encoding E1: one plain inductive type, every bound name one λ.

* `let_` and `load` bind one value; `param` binds one block, function or call-result parameter;
  `label` declares one join point.
* A group of mutually recursive join points is `label* block*`:
  `label fun even => label fun odd => block bEven (block bOdd entry)`; the i-th `block` defines the
  i-th pending label, and must follow the `label`s directly.
* A block, a function body and the continuation of a `call` start with their `param`s.
* `call f args k` calls the global symbol `f`; its results are the arguments of `k`, consumed by the
  `param`s at the start of `k`.
* Terminators: `jnz`, `jump`, `ret` (any number of results, decision D6), `exit f args` (abnormal exit
  by a tail call to `f`, decision D5), `hlt` (unreachable).

Arity is not typed: a mismatch between arguments and `param`s makes `wp` false and is rejected by the
compiler. So are the other junk shapes (`param` in the middle of a body, `block` with no pending label).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- Global symbols (functions; later data). -/
abbrev Sym := String

inductive Expr (V L : Type) : Type
  /-- `%x =k op` -/
  | let_ (op : Op V) (k : V → Expr V L)
  /-- `%x =k load{s}{sg} a` -/
  | load (c : Cls) (s : Sz) (signed : Bool) (a : Arg V) (k : V → Expr V L)
  /-- `store{s} v, a` -/
  | store (s : Sz) (v a : Arg V) (k : Expr V L)
  /-- `call $f(args)`; the results are passed to the leading `param`s of `k`. -/
  | call (f : Sym) (args : List (Arg V)) (k : Expr V L)
  /-- `jnz c, @t, @e`: tests the low 32 bits of `c`, as QBE does. -/
  | jnz (c : Arg V) (t e : Expr V L)
  | jump (j : L) (args : List (Arg V))
  | ret (vs : List (Arg V))
  /-- Abnormal exit: tail call to `f`, which does not return (decision D5). -/
  | exit (f : Sym) (args : List (Arg V))
  | hlt
  | param (f : V → Expr V L)
  | label (f : L → Expr V L)
  | block (b rest : Expr V L)

/-- A closed function body. -/
abbrev Func : Type 1 := ∀ V L : Type, Expr V L

/-- A named function, the counterpart of QBE's `Fn`. -/
structure Fn where
  name : Sym
  body : Func

end LeanQbe
