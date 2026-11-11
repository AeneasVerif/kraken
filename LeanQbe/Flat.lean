module

public import LeanQbe.IL

/-!
# First-order mirror of the IL, and reification

`Flat` is the IL with names as de Bruijn *levels* (`Nat`): the `i`-th value binder and the `j`-th label
binder, counted from the root. `toFlat` reads a term at `V := Nat`, `L := Nat`; `denote` turns a `Flat`
back into a PHOAS term at any `V L`. For a concrete function `f`,

    f = fun V L => denote V L (toFlat (f Nat Nat) 0 0) [] 0 [] 0

holds by `rfl` (checked by the kernel), and `FlatLemmas.denote_wf` proves every denotation well-formed
once and for all. Together they prove `Func.Wf f` in time linear in the kernel's evaluation of `toFlat`
(`wf_reify`), instead of `wf_tac`'s search, which is quadratic in the number of binders.

Contexts are lists with the newest binder first, plus their length kept as a separate argument, so that
the index arithmetic is on closed numerals (the elaborator does not fold `Nat` arithmetic on open
terms; the kernel does not care).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

inductive Flat : Type
  | let_ (op : Op Nat) (k : Flat)
  | load (c : Cls) (s : Sz) (signed : Bool) (a : Arg Nat) (k : Flat)
  | store (s : Sz) (v a : Arg Nat) (k : Flat)
  | call (f : Sym) (args : List (Arg Nat)) (k : Flat)
  | jnz (c : Arg Nat) (t e : Flat)
  | jump (j : Nat) (args : List (Arg Nat))
  | ret (vs : List (Arg Nat))
  | exit (f : Sym) (args : List (Arg Nat))
  | hlt
  | param (k : Flat)
  | label (k : Flat)
  | block (b rest : Flat)
  deriving Inhabited, Repr

/-- Names are levels: `nv` / `nl` = number of value / label binders in scope. -/
def toFlat : Expr Nat Nat → Nat → Nat → Flat
  | .let_ op k, nv, nl => .let_ op (toFlat (k nv) (nv + 1) nl)
  | .load c s sg a k, nv, nl => .load c s sg a (toFlat (k nv) (nv + 1) nl)
  | .store s v a k, nv, nl => .store s v a (toFlat k nv nl)
  | .call f as k, nv, nl => .call f as (toFlat k nv nl)
  | .jnz c t e, nv, nl => .jnz c (toFlat t nv nl) (toFlat e nv nl)
  | .jump j as, _, _ => .jump j as
  | .ret vs, _, _ => .ret vs
  | .exit f as, _, _ => .exit f as
  | .hlt, _, _ => .hlt
  | .param f, nv, nl => .param (toFlat (f nv) (nv + 1) nl)
  | .label f, nv, nl => .label (toFlat (f nl) nv (nl + 1))
  | .block b r, nv, nl => .block (toFlat b nv nl) (toFlat r nv nl)

/-- Level `i` in a context of length `n`, newest first. -/
def lookup {α : Type} (ctx : List α) (n i : Nat) : Option α :=
  if i < n then ctx[n - 1 - i]? else none

def denoteArg {V : Type} (ctx : List V) (n : Nat) : Arg Nat → Option (Arg V)
  | .var i =>
    match lookup ctx n i with
    | some v => some (.var v)
    | none => none
  | .imm c => some (.imm c)

def denoteArgs {V : Type} (ctx : List V) (n : Nat) : List (Arg Nat) → Option (List (Arg V))
  | [] => some []
  | a :: as =>
    match denoteArg ctx n a, denoteArgs ctx n as with
    | some a, some as => some (a :: as)
    | _, _ => none

def denoteOp {V : Type} (ctx : List V) (n : Nat) : Op Nat → Option (Op V)
  | .bin k o a b =>
    match denoteArg ctx n a, denoteArg ctx n b with
    | some a, some b => some (.bin k o a b)
    | _, _ => none
  | .cmp k o a b =>
    match denoteArg ctx n a, denoteArg ctx n b with
    | some a, some b => some (.cmp k o a b)
    | _, _ => none
  | .ext k s sg a =>
    match denoteArg ctx n a with
    | some a => some (.ext k s sg a)
    | none => none
  | .copy k a =>
    match denoteArg ctx n a with
    | some a => some (.copy k a)
    | none => none

/-- Unbound names denote `hlt` (which is well-formed and has `wp = False`). -/
def denote (V L : Type) : Flat → List V → Nat → List L → Nat → Expr V L
  | .let_ op k, vs, nv, ls, nl =>
    match denoteOp vs nv op with
    | some op => .let_ op fun v => denote V L k (v :: vs) (nv + 1) ls nl
    | none => .hlt
  | .load c s sg a k, vs, nv, ls, nl =>
    match denoteArg vs nv a with
    | some a => .load c s sg a fun v => denote V L k (v :: vs) (nv + 1) ls nl
    | none => .hlt
  | .store s v a k, vs, nv, ls, nl =>
    match denoteArg vs nv v, denoteArg vs nv a with
    | some v, some a => .store s v a (denote V L k vs nv ls nl)
    | _, _ => .hlt
  | .call f as k, vs, nv, ls, nl =>
    match denoteArgs vs nv as with
    | some as => .call f as (denote V L k vs nv ls nl)
    | none => .hlt
  | .jnz c t e, vs, nv, ls, nl =>
    match denoteArg vs nv c with
    | some c => .jnz c (denote V L t vs nv ls nl) (denote V L e vs nv ls nl)
    | none => .hlt
  | .jump j as, vs, nv, ls, nl =>
    match lookup ls nl j, denoteArgs vs nv as with
    | some j, some as => .jump j as
    | _, _ => .hlt
  | .ret rs, vs, nv, _, _ =>
    match denoteArgs vs nv rs with
    | some rs => .ret rs
    | none => .hlt
  | .exit f as, vs, nv, _, _ =>
    match denoteArgs vs nv as with
    | some as => .exit f as
    | none => .hlt
  | .hlt, _, _, _, _ => .hlt
  | .param k, vs, nv, ls, nl => .param fun v => denote V L k (v :: vs) (nv + 1) ls nl
  | .label k, vs, nv, ls, nl => .label fun j => denote V L k vs nv (j :: ls) (nl + 1)
  | .block b r, vs, nv, ls, nl => .block (denote V L b vs nv ls nl) (denote V L r vs nv ls nl)

end LeanQbe
