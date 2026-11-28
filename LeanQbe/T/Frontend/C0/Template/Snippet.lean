module

public import LeanQbe.T.IL

/-!
# Continuation-Passing C0 Template Snippets & Unrolling Combinators

Defines `C0ExprSnippet`, `C0StmtSnippet`, `materializeArg`, `materializeArgs`, `c0UnrollK`,
`c0Unroll`, `exprBind`, `blocksBind`, and `funcToExprSnippet` for static PHOAS C0 templates.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

open LeanQbe.T

/-- Continuation-passing C0 expression snippet taking arguments `as` and yielding `V r`. -/
abbrev C0ExprSnippet (as : List Ty) (r : Ty) : Type 1 :=
  ∀ (V : Ty → Type) (L : List Ty → Type) (rs : List Ty),
    Tup (Arg V) as → (V r → LeanQbe.T.Expr V L rs) → LeanQbe.T.Expr V L rs

/-- Continuation-passing C0 statement snippet transforming state variables `ts`. -/
abbrev C0StmtSnippet (ts : List Ty) : Type 1 :=
  ∀ (V : Ty → Type) (L : List Ty → Type) (rs : List Ty),
    Tup V ts → (Tup V ts → LeanQbe.T.Expr V L rs) → LeanQbe.T.Expr V L rs

/-- Materialize an `Arg V t` into a `V t`, emitting `.copy` only for immediates. -/
@[expose] def materializeArg {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {t : Ty}
    (a : Arg V t) (k : V t → LeanQbe.T.Expr V L rs) : LeanQbe.T.Expr V L rs :=
  match a with
  | .var v => k v
  | .imm c => .let_ (Op.mk (.copy t) (.imm c, ())) fun (v, ()) => k v

/-- Materialize a tuple of `Arg V` operands into `Tup V ts`. -/
@[expose] def materializeArgs {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {ts : List Ty} → Tup (Arg V) ts →
    (Tup V ts → LeanQbe.T.Expr V L rs) → LeanQbe.T.Expr V L rs
  | [], (), k => k ()
  | _ :: _, (a, as), k =>
    materializeArg a fun v => materializeArgs as fun vs => k (v, vs)

/-- Unroll a specialization-fixed step continuation statically over a Lean `List α`. -/
@[expose] def c0UnrollK {α : Type} {ts : List Ty}
    {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (xs : List α)
    (step : α → Tup V ts → (Tup V ts → LeanQbe.T.Expr V L rs) → LeanQbe.T.Expr V L rs)
    (init : Tup V ts) (k : Tup V ts → LeanQbe.T.Expr V L rs) : LeanQbe.T.Expr V L rs :=
  match xs with
  | [] => k init
  | x :: rest => step x init fun mid => c0UnrollK rest step mid k

/-- Unroll a `C0StmtSnippet` statically over a Lean `List α`. -/
@[expose] def c0Unroll {α : Type} {ts : List Ty} (xs : List α) (step : α → C0StmtSnippet ts)
    {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (init : Tup V ts) (k : Tup V ts → LeanQbe.T.Expr V L rs) : LeanQbe.T.Expr V L rs :=
  c0UnrollK xs (fun x => step x V L rs) init k

mutual
  /-- Sequentially compose a `LeanQbe.T.Expr V L as` with a continuation receiving `.ret` values. -/
  @[expose] def exprBind {V : Ty → Type} {L : List Ty → Type} {as bs : List Ty}
      (e : LeanQbe.T.Expr V L as) (k : Tup (Arg V) as → LeanQbe.T.Expr V L bs) :
      LeanQbe.T.Expr V L bs :=
    match e with
    | .let_ op cont => .let_ op fun r => exprBind (cont r) k
    | .load t a cont => .load t a fun v => exprBind (cont v) k
    | .store v a cont => .store v a (exprBind cont k)
    | .call f args cont => .call f args fun r => exprBind (cont r) k
    | .jnz c t f => .jnz c (exprBind t k) (exprBind f k)
    | .jump j args => .jump j args
    | .ret vs => k vs
    | .exit f args => .exit f args
    | .hlt => .hlt
    | .group bodies entry =>
      .group (fun js => blocksBind (bodies js) k) (fun js => exprBind (entry js) k)

  /-- Mutual helper for `exprBind` over `LeanQbe.T.Blocks`. -/
  @[expose] def blocksBind {V : Ty → Type} {L : List Ty → Type} {as bs : List Ty} :
      {sig : List (List Ty)} → LeanQbe.T.Blocks V L as sig →
      (Tup (Arg V) as → LeanQbe.T.Expr V L bs) → LeanQbe.T.Blocks V L bs sig
    | _, .nil, _ => .nil
    | _, .cons b more, k => .cons (fun ps => exprBind (b ps) k) (blocksBind more k)
end

/-- Convert a single-return `Func as [r]` into an inlineable `C0ExprSnippet as r`. -/
@[expose] def funcToExprSnippet {as : List Ty} {r : Ty} (f : Func as [r]) : C0ExprSnippet as r :=
  fun V L _ args k =>
    materializeArgs args fun xs =>
      exprBind (f V L xs) fun (res, ()) => materializeArg res k


end LeanQbe.T.Frontend.C0

end
