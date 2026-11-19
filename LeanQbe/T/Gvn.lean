module

public import LeanQbe.T.OptUtil

/-!
# Lexical-scope Common Subexpression Elimination / Global Value Numbering (`T6`)

PHOAS-to-PHOAS pass `gvn : Nat → GvnTbl V → Expr (GVal V) L rs → Expr V L rs` where
`GVal V t = V t × Nat` pairs each output binder with a lexical value number (`K t = Nat`).

Each pure `let_` instruction is keyed by
`GvnKey := (sig : List Ty) × (rs : List Ty) × OpCode sig rs × Tup (Arg K) sig` with fast
structural `DecidableEq` (`listTyDecEq`, derived `DecidableEq` on `OpCode`, `tupDecEq argKDecEq`).
On a table hit, the `let_` is eliminated and its continuation receives the cached `Tup (GVal V) rs`;
on a miss, the `let_` is emitted and `(key, freshGVals)` is pushed onto the lexical table.
Effectful or control constructs (`load`, `store`, `call`, `exit`) are never deduplicated; lexical
`tbl` enters `jnz` branches and `group` block bodies/continuations safely because `OpCode.wp` is
memory-independent.

Correctness (`LeanQbe/T/GvnLemmas.lean`): `OpCode.wp_self`, `gvn_wp`, `gvn_wf`,
`Func.gvn_spec`, `Func.gvn_wf`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

attribute [local instance] Val.decEq

/-- Fast structural decidable equality on `Arg K t`. -/
def argKDecEq (t : Ty) : DecidableEq (Arg K t)
  | .var i, .var j =>
    if h : i = j then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .imm a, .imm b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .var _, .imm _ => isFalse (fun e => by cases e)
  | .imm _, .var _ => isFalse (fun e => by cases e)

/-- Structural decidable equality on `Tup f as` given pointwise `DecidableEq`. -/
def tupDecEq {α : Type} {f : α → Type} (df : ∀ a, DecidableEq (f a)) :
    {as : List α} → DecidableEq (Tup f as)
  | [] => fun () () => isTrue rfl
  | _ :: _ => fun (a, as) (b, bs) =>
    match df _ a b, tupDecEq df as bs with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)

/-- Input variable representation in `gvn`: output binder paired with lexical value number. -/
abbrev GVal (V : Ty → Type) (t : Ty) := V t × Nat

/-- Expression key in GVN: `(sig, rs, code, operandKeys)`. -/
abbrev GvnKey := (sig : List Ty) × (rs : List Ty) × OpCode sig rs × Tup (Arg K) sig

/-- Decidable equality on `GvnKey` using fast `listTyDecEq`, `tupDecEq argKDecEq` on operands, and
derived `OpCode` `DecidableEq`. Operands are checked before `OpCode.decEq` so bucket collisions
with differing operands short-circuit cleanly. -/
def gvnKeyDecEq (k₁ k₂ : GvnKey) : Decidable (k₁ = k₂) :=
  match listTyDecEq k₁.1 k₂.1 with
  | isFalse hs => isFalse (fun h => hs (congrArg Sigma.fst h))
  | isTrue hs =>
    match listTyDecEq k₁.2.1 k₂.2.1 with
    | isFalse hr => isFalse (fun h => by cases h; exact hr rfl)
    | isTrue hr => by
      rcases k₁ with ⟨s₁, r₁, c₁, a₁⟩
      rcases k₂ with ⟨s₂, r₂, c₂, a₂⟩
      dsimp only at hs hr
      subst hs hr
      exact match tupDecEq argKDecEq a₁ a₂ with
        | isFalse ha => isFalse (fun h => by cases h; exact ha rfl)
        | isTrue ha =>
          match decEq c₁ c₂ with
          | isTrue hc => isTrue (hc ▸ ha ▸ rfl)
          | isFalse hc => isFalse (fun h => by cases h; exact hc rfl)

instance : DecidableEq GvnKey := gvnKeyDecEq

/-- Fast GMP-`Nat` value hash for GVN trie bucketing. -/
def valHash : (t : Ty) → Val t → Nat
  | .bool, b => if b then 1 else 0
  | .bits _, v => v.toNat
  | .float _, v => v.toNat
  | .pair a b, (x, y) => valHash a x + 131 * valHash b y

/-- Fast `Nat` hash of a symbolic `Arg K t`. -/
def argHash {t : Ty} : Arg K t → Nat
  | .var i => i * 2 + 1
  | .imm c => (valHash t c) * 2

/-- Fast `Nat` hash of an operand tuple. -/
def tupArgHash : {ts : List Ty} → Tup (Arg K) ts → Nat
  | [], () => 1
  | _ :: _, (a, as) => argHash a + 131 * tupArgHash as

def cmpOpTag : CmpOp → Nat
  | .eq => 0 | .ne => 1 | .ult => 2 | .ule => 3 | .ugt => 4
  | .uge => 5 | .slt => 6 | .sle => 7 | .sgt => 8 | .sge => 9

def fcmpOpTag : FCmpOp → Nat
  | .eq => 0 | .ne => 1 | .lt => 2 | .le => 3
  | .gt => 4 | .ge => 5 | .ord => 6 | .uno => 7

/-- Fast `Nat` opcode tag for GVN trie bucketing. -/
def opCodeTag {sig rs : List Ty} : OpCode sig rs → Nat
  | .copy _ => 1
  | .add _ => 2
  | .sub _ => 3
  | .mul _ => 4
  | .neg _ => 5
  | .and _ => 6
  | .or _ => 7
  | .xor _ => 8
  | .not _ => 9
  | .ternlog _ imm => 10 + 64 * imm.toNat
  | .shl _ => 11
  | .lshr _ => 12
  | .ashr _ => 13
  | .rotl _ => 14
  | .rotr _ => 15
  | .fshl _ => 16
  | .fshr _ => 17
  | .bswap _ => 18
  | .clz _ => 19
  | .cls _ => 20
  | .rbit _ => 21
  | .ctz _ => 22
  | .popcnt _ => 23
  | .cmp o _ _ _ => 24 + 64 * cmpOpTag o
  | .select _ => 25
  | .blend _ _ _ => 26
  | .zext _ n => 27 + 64 * n
  | .sext _ n => 28 + 64 * n
  | .trunc _ n => 29 + 64 * n
  | .ofBool n => 30 + 64 * n
  | .addc _ => 31
  | .subb _ => 32
  | .umulw _ => 33
  | .smulw _ => 34
  | .udiv _ => 35
  | .sdiv _ => 36
  | .urem _ => 37
  | .srem _ => 38
  | .udiv0 _ => 39
  | .sdiv0 _ => 40
  | .mkpair _ _ => 41
  | .unpair _ _ => 42
  | .bitcast _ u _ => 43 + 64 * u.size
  | .shufd _ imm => 44 + 64 * imm.toNat
  | .shufb _ => 45
  | .alignr _ imm => 46 + 64 * imm.toNat
  | .blendw _ imm => 47 + 64 * imm.toNat
  | .sha256rnds2 => 48
  | .sha256msg1 => 49
  | .sha256msg2 => 50
  | .fadd _ => 51
  | .fsub _ => 52
  | .fmul _ => 53
  | .fdiv _ => 54
  | .ffma _ => 55
  | .fsqrt _ => 56
  | .fneg _ => 57
  | .fabs _ => 58
  | .fcmp o _ _ _ => 59 + 64 * fcmpOpTag o
  | .fptoui _ n => 60 + 64 * n
  | .fptosi _ n => 61 + 64 * n
  | .uitofp _ _ => 62
  | .sitofp _ _ => 63
  | .fcvt _ _ => 64

/-- 16-bit prime-modulus hash of `(code, args)` for `GvnTrie` indexing (`< 2^16`). -/
def gvnHash {sig rs : List Ty} (code : OpCode sig rs) (args : Tup (Arg K) sig) : Nat :=
  (tupArgHash args * 131 + opCodeTag code) % 65521

/-- A single entry in a `GvnTrie` bucket. -/
abbrev GvnEntry (V : Ty → Type) := (k : GvnKey) × Tup (GVal V) k.2.1

/-- Hash bucket of `GvnKey` entries sharing the same `gvnHash`. -/
abbrev GvnBucket (V : Ty → Type) := List (GvnEntry V)

/-- Binary trie over hash bits (`O(log B)` depth `≤ 16` without `WellFounded.fix`). -/
inductive GvnTrie (V : Ty → Type) : Type where
  | empty
  | node (bucket : GvnBucket V) (even odd : GvnTrie V)

def GvnTrie.get {V : Ty → Type} : GvnTrie V → Nat → Nat → GvnBucket V
  | .empty, _, _ => []
  | .node b _ _, 0, _ => b
  | .node b _ _, _ + 1, 0 => b
  | .node _ e o, fuel + 1, n + 1 =>
    if n % 2 == 0 then GvnTrie.get e fuel (n / 2) else GvnTrie.get o fuel (n / 2)

def GvnTrie.insert {V : Ty → Type} : GvnTrie V → Nat → Nat → GvnEntry V → GvnTrie V
  | .empty, 0, _, entry => .node [entry] .empty .empty
  | .node b e o, 0, _, entry => .node (entry :: b) e o
  | .empty, _ + 1, 0, entry => .node [entry] .empty .empty
  | .node b e o, _ + 1, 0, entry => .node (entry :: b) e o
  | .empty, fuel + 1, n + 1, entry =>
    if n % 2 == 0 then .node [] (GvnTrie.insert .empty fuel (n / 2) entry) .empty
    else .node [] .empty (GvnTrie.insert .empty fuel (n / 2) entry)
  | .node b e o, fuel + 1, n + 1, entry =>
    if n % 2 == 0 then .node b (GvnTrie.insert e fuel (n / 2) entry) o
    else .node b e (GvnTrie.insert o fuel (n / 2) entry)

/-- Lexical CSE table mapping `GvnKey`s to cached `GVal V` result tuples (hash-bucketed trie). -/
abbrev GvnTbl (V : Ty → Type) := GvnTrie V

def GvnBucket.find {V : Ty → Type} :
    GvnBucket V → (sig rs : List Ty) → OpCode sig rs → Tup (Arg K) sig → Option (Tup (GVal V) rs)
  | [], _, _, _, _ => none
  | ⟨k', v⟩ :: rest, sig, rs, code, args =>
    match gvnKeyDecEq k' ⟨sig, rs, code, args⟩ with
    | isTrue h => some (cast (congrArg (fun k => Tup (GVal V) k.2.1) h) v)
    | isFalse _ => GvnBucket.find rest sig rs code args

/-- Look up a key `(sig, rs, code, args)` in `tbl`, casting the cached tuple along `rs`. -/
@[irreducible] def GvnTbl.find {V : Ty → Type} (tbl : GvnTbl V)
    (sig rs : List Ty) (code : OpCode sig rs) (args : Tup (Arg K) sig) : Option (Tup (GVal V) rs) :=
  GvnBucket.find (GvnTrie.get tbl 16 (gvnHash code args)) sig rs code args

/-- Insert `(key, v)` into `tbl` at `gvnHash code args`. -/
@[irreducible] def GvnTbl.insert {V : Ty → Type} (tbl : GvnTbl V)
    (sig rs : List Ty) (code : OpCode sig rs) (args : Tup (Arg K) sig) (v : Tup (GVal V) rs) :
    GvnTbl V :=
  GvnTrie.insert tbl 16 (gvnHash code args) ⟨⟨sig, rs, code, args⟩, v⟩

def Arg.gout {V : Ty → Type} {t : Ty} : Arg (GVal V) t → Arg V t
  | .var p => .var p.1
  | .imm c => .imm c

def Arg.gkey {V : Ty → Type} {t : Ty} : Arg (GVal V) t → Arg K t
  | .var p => .var p.2
  | .imm c => .imm c

abbrev tupGOut {V : Ty → Type} : {ts : List Ty} → Tup (Arg (GVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => Arg.gout

abbrev tupGKey {V : Ty → Type} : {ts : List Ty} → Tup (Arg (GVal V)) ts → Tup (Arg K) ts :=
  tupMapArg fun _ => Arg.gkey

abbrev freshGVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (GVal V) ts :=
  tupFreshWith fun x next => (x, next)

mutual
def gvn {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (tbl : GvnTbl V) : Expr (GVal V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    let kArgs := tupGKey op.args
    match tbl.find op.sig ts op.code kArgs with
    | some cached => gvn next tbl (k cached)
    | none =>
      let op' : Op V ts := ⟨op.code, tupGOut op.args⟩
      .let_ op' fun xs =>
        let gs := freshGVals ts xs next
        gvn (next + ts.length) (tbl.insert op.sig ts op.code kArgs gs) (k gs)
  | .load t a k =>
    .load t a.gout fun v => gvn (next + 1) tbl (k (v, next))
  | .store v a k =>
    .store v.gout a.gout (gvn next tbl k)
  | .call f (bs := bs) args k =>
    .call f (tupGOut args) fun xs =>
      gvn (next + bs.length) tbl (k (freshGVals bs xs next))
  | .jnz c t e =>
    .jnz c.gout (gvn next tbl t) (gvn next tbl e)
  | .jump j args => .jump j (tupGOut args)
  | .ret vs => .ret (tupGOut vs)
  | .exit f args => .exit f (tupGOut args)
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => gvnB next tbl (bodies Js)) (fun Js => gvn next tbl (k Js))

def gvnB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (tbl : GvnTbl V) :
    {sig : List (List Ty)} → Blocks (GVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => gvn (next + ts.length) tbl (b (freshGVals ts xs next))) (gvnB next tbl bs)
end

/-- Run lexical GVN/CSE on a closed function `Func`. -/
def Func.gvn {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => LeanQbe.T.gvn as.length .empty (f (GVal V) L (freshGVals as xs 0))

end LeanQbe.T
