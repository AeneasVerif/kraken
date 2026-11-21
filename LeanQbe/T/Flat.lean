module

public import LeanQbe.T.IL

/-!
# Typed first-order de Bruijn mirror and reification

`TFlat rs` (mutually with `TBlocks rs sig`) is a first-order mirror of `Expr` / `Blocks` with
typed operations and de Bruijn *indices* (`Nat`, `0` = most recently bound variable/label).

* `toTFlat` extracts a `TFlat rs` from `Expr K KL rs` (`K := fun _ => Nat`, `KL := fun _ => Nat`),
  converting de Bruijn levels `(nv, nl)` into de Bruijn indices (`nv - 1 - lvl`), with out-of-scope
  levels mapped safely out of bounds (`nv`).
* `denote` turns a `TFlat rs` back into `Expr V L rs` for any `V L`, checking bounds and `Ty`
  equality via `castTy` / `castListTy` (mapping any mismatch to `.hlt`).
* `TFlat.wfCheck` checks that every variable and label index in a `TFlat` is in scope at its
  expected type (`Bool`).
* `FlatLemmas.denote_wf` proves every denotation `Wf`-related across any two instantiations, and
  `Func.wf_of_reify` proves `Func.Wf f` from a single kernel-checked `rfl` equation.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Type-erased variable level representation used during reification. -/
abbrev K : Ty → Type := fun _ => Nat

/-- Type-erased label level representation used during reification. -/
abbrev KL : List Ty → Type := fun _ => Nat

mutual
/-- Typed first-order mirror of `Expr` with de Bruijn indices (`0` = newest binder). -/
inductive TFlat (rs : List Ty) : Type
  | let_ {ts : List Ty} (op : Op K ts) (k : TFlat rs) : TFlat rs
  | load (t : Ty) (a : Arg K i64) (k : TFlat rs) : TFlat rs
  | store {t : Ty} (v : Arg K t) (a : Arg K i64) (k : TFlat rs) : TFlat rs
  | call (f : Sym) {as : List Ty} (bs : List Ty) (args : Tup (Arg K) as) (k : TFlat rs) : TFlat rs
  | jnz (c : Arg K .bool) (t e : TFlat rs) : TFlat rs
  | jump {ts : List Ty} (j : Nat) (args : Tup (Arg K) ts) : TFlat rs
  | ret (vs : Tup (Arg K) rs) : TFlat rs
  | exit (f : Sym) {as : List Ty} (args : Tup (Arg K) as) : TFlat rs
  | hlt : TFlat rs
  | group {sig : List (List Ty)} (bodies : TBlocks rs sig) (k : TFlat rs) : TFlat rs

/-- Typed first-order mirror of `Blocks`. -/
inductive TBlocks (rs : List Ty) : List (List Ty) → Type
  | nil : TBlocks rs []
  | cons {ts : List Ty} {sig : List (List Ty)} (b : TFlat rs) (bs : TBlocks rs sig) :
      TBlocks rs (ts :: sig)
end

/-- Push a tuple onto a sigma-tagged context list (`0`-indexed newest first, matching
`Tup.levels as n`: the last element of `as` ends up at head index `0`). -/
def pushTup {α : Type} {f : α → Type} : {as : List α} → Tup f as →
    List ((a : α) × f a) → List ((a : α) × f a)
  | [], (), acc => acc
  | a :: _, (x, xs), acc => pushTup xs (⟨a, x⟩ :: acc)

/-- Push a list of types onto a context in the same order as `pushTup`. -/
def pushTypes {α : Type} : List α → List α → List α
  | [], acc => acc
  | a :: as, acc => pushTypes as (a :: acc)

/-- Convert a de Bruijn level in `Expr K KL` (`0` = oldest) into a de Bruijn index (`0` = newest),
mapping out-of-scope levels `≥ nv` to `nv`. -/
def idxArg (nv : Nat) {t : Ty} : Arg K t → Arg K t
  | .var lvl => .var (if lvl < nv then nv - 1 - lvl else nv)
  | .imm c => .imm c

/-- Convert a tuple of operand levels to de Bruijn indices. -/
def idxArgs (nv : Nat) : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => ()
  | _ :: _, (a, as) => (idxArg nv a, idxArgs nv as)

mutual
/-- Total reification of `Expr K KL rs` into `TFlat rs`, tracking current value/label depths
`nv`, `nl`. -/
def toTFlat {rs : List Ty} : Expr K KL rs → Nat → Nat → TFlat rs
  | .let_ (ts := ts) op k, nv, nl =>
    .let_ ⟨op.code, idxArgs nv op.args⟩ (toTFlat (k (Tup.levels ts nv)) (nv + ts.length) nl)
  | .load t a k, nv, nl => .load t (idxArg nv a) (toTFlat (k nv) (nv + 1) nl)
  | .store v a k, nv, nl => .store (idxArg nv v) (idxArg nv a) (toTFlat k nv nl)
  | .call f (bs := bs) args k, nv, nl =>
    .call f bs (idxArgs nv args) (toTFlat (k (Tup.levels bs nv)) (nv + bs.length) nl)
  | .jnz c t e, nv, nl => .jnz (idxArg nv c) (toTFlat t nv nl) (toTFlat e nv nl)
  | .jump j args, nv, nl => .jump (if j < nl then nl - 1 - j else nl) (idxArgs nv args)
  | .ret vs, nv, _ => .ret (idxArgs nv vs)
  | .exit f args, nv, _ => .exit f (idxArgs nv args)
  | .hlt, _, _ => .hlt
  | .group (sig := sig) bodies k, nv, nl =>
    let ls' := Tup.levels sig nl
    let nl' := nl + sig.length
    .group (toTBlocks (bodies ls') nv nl') (toTFlat (k ls') nv nl')

/-- Reify `Blocks K KL rs sig` into `TBlocks rs sig`. -/
def toTBlocks {rs : List Ty} :
    {sig : List (List Ty)} → Blocks K KL rs sig → Nat → Nat → TBlocks rs sig
  | _, .nil, _, _ => .nil
  | _, .cons (ts := ts) b bs, nv, nl =>
    .cons (toTFlat (b (Tup.levels ts nv)) (nv + ts.length) nl) (toTBlocks bs nv nl)
end

/-- Direct `List` indexing without `GetElem?` dispatch. -/
def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => listGet? as n

/-- Fast structural decidable equality on `Ty` (avoids derived `DecidableEq` matcher overhead). -/
def tyDecEq : (a b : Ty) → Decidable (a = b)
  | .bool, .bool => isTrue rfl
  | .bits m, .bits n =>
    if h : m = n then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .float f, .float g =>
    if h : f = g then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .pair a1 b1, .pair a2 b2 =>
    match tyDecEq a1 a2, tyDecEq b1 b2 with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .bool, .bits _ | .bool, .float _ | .bool, .pair _ _
  | .bits _, .bool | .bits _, .float _ | .bits _, .pair _ _
  | .float _, .bool | .float _, .bits _ | .float _, .pair _ _
  | .pair _ _, .bool | .pair _ _, .bits _ | .pair _ _, .float _ =>
    isFalse (fun e => by cases e)

/-- Structural decidable equality on `List Ty`. -/
def listTyDecEq : (a b : List Ty) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match tyDecEq a b, listTyDecEq as bs with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (fun e => by cases e)

/-- Cast a value `f a` to `f b` if `a = b`. -/
def castTy {f : Ty → Type} : (a b : Ty) → f a → Option (f b)
  | .bool, .bool, v => some v
  | .bits m, .bits n, v => if h : m = n then some (h ▸ v) else none
  | .float f, .float g, v => if h : f = g then some (h ▸ v) else none
  | .pair a1 b1, .pair a2 b2, v =>
    match tyDecEq a1 a2, tyDecEq b1 b2 with
    | isTrue h1, isTrue h2 => some (h1 ▸ h2 ▸ v)
    | _, _ => none
  | _, _, _ => none

/-- Cast a label `f a` to `f b` if `a = b`. -/
def castListTy {f : List Ty → Type} (a b : List Ty) (v : f a) : Option (f b) :=
  match listTyDecEq a b with
  | isTrue h => some (h ▸ v)
  | isFalse _ => none

/-- Typed de Bruijn variable lookup in `vs`. -/
def lookupV {V : Ty → Type} (vs : List ((t : Ty) × V t)) (t : Ty) (idx : Nat) : Option (V t) :=
  match listGet? vs idx with
  | some ⟨t', v⟩ => castTy t' t v
  | none => none

/-- Typed de Bruijn label lookup in `ls`. -/
def lookupL {L : List Ty → Type} (ls : List ((ts : List Ty) × L ts)) (ts : List Ty) (idx : Nat) :
    Option (L ts) :=
  match listGet? ls idx with
  | some ⟨ts', l⟩ => castListTy ts' ts l
  | none => none

def denoteArg {V : Ty → Type} (vs : List ((t : Ty) × V t)) {t : Ty} : Arg K t → Option (Arg V t)
  | .var i => match lookupV vs t i with | some v => some (.var v) | none => none
  | .imm c => some (.imm c)

def denoteArgs {V : Ty → Type} (vs : List ((t : Ty) × V t)) :
    {ts : List Ty} → Tup (Arg K) ts → Option (Tup (Arg V) ts)
  | [], () => some ()
  | _ :: _, (a, as) =>
    match denoteArg vs a, denoteArgs vs as with
    | some a', some as' => some (a', as')
    | _, _ => none

mutual
/-- Denote `TFlat rs` into `Expr V L rs`; out-of-bounds or type-mismatched indices become `.hlt`. -/
def denote (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    TFlat rs → List ((t : Ty) × V t) → List ((ts : List Ty) × L ts) → Expr V L rs
  | .let_ op k, vs, ls =>
    match denoteArgs vs op.args with
    | some args' => .let_ ⟨op.code, args'⟩ fun xs => denote V L k (pushTup xs vs) ls
    | none => .hlt
  | .load t a k, vs, ls =>
    match denoteArg vs a with
    | some a' => .load t a' fun v => denote V L k (⟨t, v⟩ :: vs) ls
    | none => .hlt
  | .store v a k, vs, ls =>
    match denoteArg vs v, denoteArg vs a with
    | some v', some a' => .store v' a' (denote V L k vs ls)
    | _, _ => .hlt
  | .call f bs args k, vs, ls =>
    match denoteArgs vs args with
    | some args' => .call f (bs := bs) args' fun xs => denote V L k (pushTup xs vs) ls
    | none => .hlt
  | .jnz c t e, vs, ls =>
    match denoteArg vs c with
    | some c' => .jnz c' (denote V L t vs ls) (denote V L e vs ls)
    | none => .hlt
  | .jump (ts := ts) j args, vs, ls =>
    match lookupL ls ts j, denoteArgs vs args with
    | some j', some args' => .jump j' args'
    | _, _ => .hlt
  | .ret vs', vs, _ =>
    match denoteArgs vs vs' with
    | some vs'' => .ret vs''
    | none => .hlt
  | .exit f args, vs, _ =>
    match denoteArgs vs args with
    | some args' => .exit f args'
    | none => .hlt
  | .hlt, _, _ => .hlt
  | .group (sig := sig) bodies k, vs, ls =>
    .group (sig := sig)
      (fun Js => denoteB V L bodies vs (pushTup Js ls))
      (fun Js => denote V L k vs (pushTup Js ls))

/-- Denote `TBlocks rs sig` into `Blocks V L rs sig`. -/
def denoteB (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → List ((t : Ty) × V t) →
    List ((ts : List Ty) × L ts) → Blocks V L rs sig
  | _, .nil, _, _ => .nil
  | _, .cons b bs, vs, ls =>
    .cons (fun xs => denote V L b (pushTup xs vs) ls) (denoteB V L bs vs ls)
end

/-- Computable check that an operand's de Bruijn index is in bounds at type `t`. -/
def checkArg (Γ : List Ty) (t : Ty) : Arg K t → Bool
  | .var i =>
    match listGet? Γ i with
    | some t' => match tyDecEq t' t with | isTrue _ => true | isFalse _ => false
    | none => false
  | .imm _ => true

/-- Computable check for a tuple of operands. -/
def checkArgs (Γ : List Ty) : {ts : List Ty} → Tup (Arg K) ts → Bool
  | [], () => true
  | t :: _, (a, as) => checkArg Γ t a && checkArgs Γ as

mutual
/-- Total computable scope/type checker for `TFlat rs` under value context `Γ` and label
context `Δ`. -/
def TFlat.wfCheck {rs : List Ty} (Γ : List Ty) (Δ : List (List Ty)) : TFlat rs → Bool
  | .let_ (ts := ts) op k => checkArgs Γ op.args && k.wfCheck (pushTypes ts Γ) Δ
  | .load t a k => checkArg Γ i64 a && k.wfCheck (t :: Γ) Δ
  | .store (t := t) v a k => checkArg Γ t v && checkArg Γ i64 a && k.wfCheck Γ Δ
  | .call _ bs args k => checkArgs Γ args && k.wfCheck (pushTypes bs Γ) Δ
  | .jnz c t e => checkArg Γ .bool c && t.wfCheck Γ Δ && e.wfCheck Γ Δ
  | .jump (ts := ts) j args =>
    (match listGet? Δ j with
     | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
     | none => false) && checkArgs Γ args
  | .ret vs => checkArgs Γ vs
  | .exit _ args => checkArgs Γ args
  | .hlt => true
  | .group (sig := sig) bodies k =>
    let Δ' := pushTypes sig Δ
    bodies.wfCheck Γ Δ' && k.wfCheck Γ Δ'

/-- Total computable scope/type checker for `TBlocks rs sig`. -/
def TBlocks.wfCheck {rs : List Ty} (Γ : List Ty) (Δ : List (List Ty)) :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons (ts := ts) b bs => b.wfCheck (pushTypes ts Γ) Δ && bs.wfCheck Γ Δ
end

mutual
/-- True iff `TFlat rs` contains no explicit `.hlt` node. -/
def TFlat.noHlt {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k => k.noHlt
  | .load _ _ k => k.noHlt
  | .store _ _ k => k.noHlt
  | .call _ _ _ k => k.noHlt
  | .jnz _ t e => t.noHlt && e.noHlt
  | .jump _ _ => true
  | .ret _ => true
  | .exit _ _ => true
  | .hlt => false
  | .group bodies k => bodies.noHlt && k.noHlt

/-- True iff `TBlocks rs sig` contains no explicit `.hlt` node. -/
def TBlocks.noHlt {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => b.noHlt && bs.noHlt
end

/-- Reify a closed function `f` into its first-order de Bruijn `TFlat` representation. -/
def reifyFunc {as rs : List Ty} (f : Func as rs) : TFlat rs :=
  toTFlat (f K KL (Tup.levels as 0)) as.length 0

/-- Denote a first-order `TFlat` term back into a closed PHOAS `Func`. -/
def denoteFunc {as rs : List Ty} (tf : TFlat rs) : Func as rs :=
  fun V L xs => denote V L tf (pushTup xs []) []

/-- Reification-denotation round-trip flattening nested PHOAS closures into canonical AST form. -/
def Func.renorm {as rs : List Ty} (f : Func as rs) : Func as rs :=
  denoteFunc (reifyFunc f)

/-- Total computable reification + scope/type check for a closed `Func as rs`.
This cross-checks `toTFlat`'s de Bruijn index arithmetic against `TFlat.wfCheck` (ensuring
no out-of-scope or type-mismatched variable/label index collapses to `.hlt` under `denote`,
as proved by `Func.denote_noHlt_of_check`); it is NOT a theorem bridge to `Func.Wf`, which
holds unconditionally by parametricity for any reified term (`Func.wf_of_reify`). -/
def Func.checkTFlat {as rs : List Ty} (f : Func as rs) : Bool :=
  (reifyFunc f).wfCheck (pushTypes as []) []

end LeanQbe.T
