module

public import LeanQbe.T.OptUtil

/-!
# Commutative canonicalization and constant-chain reassociation (`O-M1`)

PHOAS-to-PHOAS pass `canon : Nat → Expr (CanonVal V) L rs → Expr V L rs` where `CanonVal V t`
tracks:
* the emitted operand `out : Arg V t`,
* a symbolic lexical key `key : FKey t` (used to order commutative variable operands), and
* optional `constDef : Option (CanonDef V t)` recording `(op base imm)` provenance for associative
  constant-chain reassociation.

Transformations (across `.bool`, `.bits n`, and nested `.pair`/vector trees):
1. **Commutative canonicalization**: for `.add`, `.mul`, `.and`, `.or`, `.xor`, and `.cmp co`
   (using `CmpOp.swap`, guarding `.add`/`.mul`/`.cmp` by `!t.hasFloat`), places any immediate on
   the right (`c + x → x + c`, `5 < x → x > 5`) and orders two variable operands deterministically
   by lexical key (`k1 ≤ k2`).
2. **Constant-chain reassociation (`MB4`)**: for associative ops `.add`, `.mul`, `.and`, `.or`,
   `.xor`, rewrites `(x op c₁) op c₂ → x op (AssocOp.eval op t c₁ c₂)`. Shifts
   (`shl`/`lshr`/`ashr`) are intentionally excluded because mod-`n` shift wrapping is not
   associative when shift counts sum to `≥ n`.

Correctness (`LeanQbe/T/CanonLemmas.lean`): `canon_wp`, `canon_wf`, `Func.canon_spec`,
`Func.canon_wf`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Associative and commutative binary opcodes eligible for constant-chain reassociation.
Shifts are excluded because mod-`n` shift-count wrapping is not associative. -/
inductive AssocOp
  | add
  | mul
  | and
  | or
  | xor
  deriving DecidableEq, Repr, Inhabited

/-- Reconstruct the typed `OpCode` for an `AssocOp` at type `t`. -/
def AssocOp.toOpCode : AssocOp → (t : Ty) → OpCode [t, t] [t]
  | .add, t => .add t
  | .mul, t => .mul t
  | .and, t => .and t
  | .or, t => .or t
  | .xor, t => .xor t

/-- Whether `AssocOp` requires `!t.hasFloat` (true for `.add` and `.mul`). -/
def AssocOp.needsNoFloat : AssocOp → Bool
  | .add | .mul => true
  | .and | .or | .xor => false

/-- Evaluate an `AssocOp` leaf-wise on concrete values of type `t`. -/
def AssocOp.eval : AssocOp → (t : Ty) → Val t → Val t → Val t
  | .add, t, a, b => lift2 (· + ·) (· ^^ ·) t a b
  | .mul, t, a, b => lift2 (· * ·) (· && ·) t a b
  | .and, t, a, b => lift2 (· &&& ·) (· && ·) t a b
  | .or, t, a, b => lift2 (· ||| ·) (· || ·) t a b
  | .xor, t, a, b => lift2 (· ^^^ ·) (· ^^ ·) t a b

/-- Optional provenance recording that a variable was bound by `op base imm`. -/
structure CanonDef (V : Ty → Type) (t : Ty) : Type where
  op : AssocOp
  base : Arg V t
  imm : Val t

/-- Input value representation in `canon`: output operand, lexical key, and optional constant-chain
provenance. -/
structure CanonVal (V : Ty → Type) (t : Ty) : Type where
  out : Arg V t
  key : FKey t
  constDef : Option (CanonDef V t) := none

/-- Wrap a fresh bound output variable `v` with lexical key `next`. -/
def CanonVal.fresh {V : Ty → Type} {t : Ty} (v : V t) (next : Nat) : CanonVal V t :=
  ⟨.var v, .var next, none⟩

/-- Total deterministic ordering on symbolic keys `FKey t`. -/
def FKey.le {t : Ty} : FKey t → FKey t → Bool
  | .var i, .var j => i ≤ j
  | .var _, .imm _ => true
  | .imm _, .var _ => false
  | .imm _, .imm _ => true

/-- Output operand of an `Arg (CanonVal V) t`. -/
def Arg.cnout {V : Ty → Type} {t : Ty} : Arg (CanonVal V) t → Arg V t
  | .var c => c.out
  | .imm c => .imm c

/-- Symbolic lexical key of an `Arg (CanonVal V) t`. -/
def Arg.cnkey {V : Ty → Type} {t : Ty} : Arg (CanonVal V) t → FKey t
  | .var c => c.key
  | .imm c => .imm c

/-- Optional `(op base imm)` provenance of an `Arg (CanonVal V) t`. -/
def Arg.cndef? {V : Ty → Type} {t : Ty} : Arg (CanonVal V) t → Option (CanonDef V t)
  | .var c => c.constDef
  | .imm _ => none

/-- Map `Arg.cnout` across an operand tuple. -/
abbrev tupCnOut {V : Ty → Type} :
    {ts : List Ty} → Tup (Arg (CanonVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => Arg.cnout

/-- Wrap bound output variables `xs : Tup V ts` into fresh `CanonVal V`s starting at `next`. -/
abbrev freshCanonVals {V : Ty → Type} :
    (ts : List Ty) → Tup V ts → Nat → Tup (CanonVal V) ts :=
  tupFreshWith fun x next => CanonVal.fresh x next

/-- Outcome of lowering one `let_` binding in `canon`. -/
structure CanonLetStep (V : Ty → Type) (ts : List Ty) : Type where
  op : Op V ts
  wrap : Tup V ts → Tup (CanonVal V) ts

/-- Whether commutative operands `(a, b)` should swap: moves `.imm` to the right and orders two
variables by `FKey.le`. -/
def shouldSwap {V : Ty → Type} {t : Ty} (a b : Arg (CanonVal V) t) : Bool :=
  match a.cnout.imm?, b.cnout.imm? with
  | some _, none => true
  | none, none => !(FKey.le a.cnkey b.cnkey)
  | _, _ => false

/-- Core associative constant-chain reassociation on ordered operands `(a', b')`. -/
def canonAssocCore {V : Ty → Type} (next : Nat) (aop : AssocOp) (t : Ty)
    (a' b' : Arg (CanonVal V) t) : CanonLetStep V [t] :=
  match b'.cnout.imm? with
  | some c₂ =>
    let (base, c) :=
      match a'.cndef? with
      | some d =>
        if d.op == aop then (d.base, aop.eval t d.imm c₂) else (a'.cnout, c₂)
      | none => (a'.cnout, c₂)
    ⟨op2 (aop.toOpCode t) base (.imm c),
      fun (r, ()) => (⟨.var r, .var next, some ⟨aop, base, c⟩⟩, ())⟩
  | none =>
    ⟨op2 (aop.toOpCode t) a'.cnout b'.cnout,
      fun (r, ()) => (CanonVal.fresh r next, ())⟩

/-- Canonicalize an associative/commutative operation `aop` on `(a, b)` at type `t`, putting
immediates on the right, ordering variables by lexical key, and collapsing `(x op c₁) op c₂`. -/
def canonAssocStep {V : Ty → Type} (next : Nat) (aop : AssocOp) (t : Ty)
    (a b : Arg (CanonVal V) t) : CanonLetStep V [t] :=
  if shouldSwap a b then canonAssocCore next aop t b a else canonAssocCore next aop t a b

/-- Lower one `OpCode` with canonicalized operands in `canon`. -/
def OpCode.canonLet {V : Ty → Type} :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg (CanonVal V)) sig → Nat → CanonLetStep V ts
  | _, _, .add t, (a, b, ()), next =>
    if t.hasFloat then
      ⟨op2 (.add t) a.cnout b.cnout, fun xs => freshCanonVals [t] xs next⟩
    else canonAssocStep next .add t a b
  | _, _, .mul t, (a, b, ()), next =>
    if t.hasFloat then
      ⟨op2 (.mul t) a.cnout b.cnout, fun xs => freshCanonVals [t] xs next⟩
    else canonAssocStep next .mul t a b
  | _, _, .and t, (a, b, ()), next => canonAssocStep next .and t a b
  | _, _, .or t, (a, b, ()), next => canonAssocStep next .or t a b
  | _, _, .xor t, (a, b, ()), next => canonAssocStep next .xor t a b
  | _, _, .cmp o t m h, (a, b, ()), next =>
    if t.hasFloat then
      ⟨op2 (.cmp o t m h) a.cnout b.cnout, fun xs => freshCanonVals [m] xs next⟩
    else if shouldSwap a b then
      ⟨op2 (.cmp o.swap t m h) b.cnout a.cnout, fun xs => freshCanonVals [m] xs next⟩
    else
      ⟨op2 (.cmp o t m h) a.cnout b.cnout, fun xs => freshCanonVals [m] xs next⟩
  | _, ts, code, args, next =>
    ⟨⟨code, tupCnOut args⟩, fun xs => freshCanonVals ts xs next⟩

/-- Lower one `let_` operation in `canon`. -/
def Op.canonLet {V : Ty → Type} {ts : List Ty} (op : Op (CanonVal V) ts) (next : Nat) :
    CanonLetStep V ts :=
  op.code.canonLet op.args next

mutual
def canon {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (next : Nat) :
    Expr (CanonVal V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    let step := op.canonLet next
    .let_ step.op fun xs => canon (next + ts.length) (k (step.wrap xs))
  | .load t a k =>
    .load t a.cnout fun v => canon (next + 1) (k (CanonVal.fresh v next))
  | .store v a k =>
    .store v.cnout a.cnout (canon next k)
  | .call f (bs := bs) args k =>
    .call f (tupCnOut args) fun xs =>
      canon (next + bs.length) (k (freshCanonVals bs xs next))
  | .jnz c t e =>
    .jnz c.cnout (canon next t) (canon next e)
  | .jump j args => .jump j (tupCnOut args)
  | .ret vs => .ret (tupCnOut vs)
  | .exit f args => .exit f (tupCnOut args)
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => canonB next (bodies Js)) (fun Js => canon next (k Js))

def canonB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (next : Nat) :
    {sig : List (List Ty)} → Blocks (CanonVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => canon (next + ts.length) (b (freshCanonVals ts xs next))) (canonB next bs)
end

/-- Canonicalize commutative operations and associative constant chains on a closed `Func`. -/
def Func.canon {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => LeanQbe.T.canon as.length (f (CanonVal V) L (freshCanonVals as xs 0))

end LeanQbe.T
