module

public import LeanQbe.T.Ops

/-!
# The typed IL term

Spike-2 shape (`Expr`/`Blocks` mutual inductives with head-bound `Tup` binders and `group`
join-point groups) extended with multi-result `let_`, typed `load`/`store`, signature-indexed
`call`, `exit` (decision D5), and `hlt`:

* A function is `Func as rs := ∀ V L, Tup V as → Expr V L rs`.
* Block parameters, call results, and multi-result operations bind all values at once via `Tup`.
* `group` binds a tuple of join-point labels `Tup L sig` simultaneously over `Bodies` and entry `k`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Global symbol name (function; later data). -/
abbrev Sym := String

mutual
inductive Expr (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) : Type
  /-- `(%r₁, …, %rₖ) = op(args)`: bind all operation results at once. -/
  | let_ {ts : List Ty} (op : Op V ts) (k : Tup V ts → Expr V L rs)
  /-- `%x = load t, a` -/
  | load (t : Ty) (a : Arg V i64) (k : V t → Expr V L rs)
  /-- `store t v, a` -/
  | store {t : Ty} (v : Arg V t) (a : Arg V i64) (k : Expr V L rs)
  /-- `(%r₁, …, %rₖ) = call $f(args)` -/
  | call (f : Sym) {as bs : List Ty} (args : Tup (Arg V) as) (k : Tup V bs → Expr V L rs)
  /-- `jnz c, t, e` -/
  | jnz (c : Arg V .bool) (t e : Expr V L rs)
  /-- `jump j(args)` -/
  | jump {ts : List Ty} (j : L ts) (args : Tup (Arg V) ts)
  /-- `ret vs` -/
  | ret (vs : Tup (Arg V) rs)
  /-- Abnormal exit: tail call to `f` with `args`, which does not return (decision D5). -/
  | exit (f : Sym) {as : List Ty} (args : Tup (Arg V) as)
  /-- Unreachable / undefined behaviour. -/
  | hlt
  /-- Join-point group: the labels are bound over `bodies` and over the entry `k`. -/
  | group {sig : List (List Ty)} (bodies : Tup L sig → Blocks V L rs sig)
      (k : Tup L sig → Expr V L rs)

inductive Blocks (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) : List (List Ty) → Type
  | nil : Blocks V L rs []
  /-- A block binds its parameter tuple at its head. -/
  | cons {ts : List Ty} {sig : List (List Ty)} (b : Tup V ts → Expr V L rs)
      (bs : Blocks V L rs sig) : Blocks V L rs (ts :: sig)
end

/-- A closed function body taking `as` and returning `rs`. -/
abbrev Func (as rs : List Ty) : Type 1 :=
  ∀ (V : Ty → Type) (L : List Ty → Type), Tup V as → Expr V L rs

/-- A named typed function. -/
structure Fn where
  name : Sym
  as : List Ty
  rs : List Ty
  body : Func as rs

/-- Positional lookup of block `i` inside a group's `Blocks`. -/
def Blocks.get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → {ts : List Ty} → Blocks V L rs sig → Member ts sig →
    Tup V ts → Expr V L rs
  | _, _, .cons b _, .here => b
  | _, _, .cons _ bs, .there i => bs.get i

/-- Structured one-block loop: a single-block group whose block may jump back to itself. -/
def loop1 {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty}
    (body : L ts → Tup V ts → Expr V L rs) (entry : L ts → Expr V L rs) : Expr V L rs :=
  .group (sig := [ts]) (fun Js => .cons (body Js.1) .nil) (fun Js => entry Js.1)

end LeanQbe.T
