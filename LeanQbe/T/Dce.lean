module

public import LeanQbe.T.WP
public import LeanQbe.T.Flat

/-!
# Dead-Code Elimination (`T6`)

Two-phase PHOAS dead-code elimination pass:
1. Bottom-up pure liveness analysis (`liveVars` / `liveVarsB`) over `Expr K KL0 rs` using an
   `O(log N)` structural binary trie `NatSet` (`NatTrie` with `List Nat` overflow for `≥ 2^32`).
   A `let_` binding `[b, b + ts.length)` is kept iff any of its results is live in its
   continuation (`anyLive`), causing chains of dead pure bindings to cascade in a single sweep.
   Side-effectful or control nodes (`load`, `store`, `call`, `exit`, `store`, `jnz`, `jump`,
   `ret`, `hlt`, `group`) are never dropped, and `group` block liveness is conservatively
   unioned with the continuation's liveness.
2. Top-down reconstruction (`dceSweep` / `dceSweepB`) over `Expr (OptV V) L rs` guided by the
   computed `KeepTree` / `KeepBlocks`.

Correctness (`LeanQbe/T/DceLemmas.lean`): `OpCode.wp_exists`, `dce_wp`, `dce_wf`,
`Func.dce_wf`, `Func.dce_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

attribute [local instance] Val.inhabited

/-! ## Fast structural `NatSet` (binary trie + large-index fallback) -/

/-- Structural binary trie for variable levels `< 2^32`, avoiding `WellFounded.fix` so
kernel `rfl` / `t_kernel_rfl` stays fast. -/
inductive NatTrie : Type where
  | empty
  | node (here : Bool) (even odd : NatTrie)
  deriving Repr, DecidableEq, Inhabited

def NatTrie.mem : NatTrie → Nat → Bool
  | .empty, _ => false
  | .node h _ _, 0 => h
  | .node _ e o, n + 1 =>
    if n % 2 == 0 then NatTrie.mem e (n / 2) else NatTrie.mem o (n / 2)

def NatTrie.insert : Nat → NatTrie → Nat → NatTrie
  | _, .empty, 0 => .node true .empty .empty
  | _, .node _ e o, 0 => .node true e o
  | 0, t, _ + 1 => t
  | fuel + 1, .empty, n + 1 =>
    if n % 2 == 0 then .node false (NatTrie.insert fuel .empty (n / 2)) .empty
    else .node false .empty (NatTrie.insert fuel .empty (n / 2))
  | fuel + 1, .node h e o, n + 1 =>
    if n % 2 == 0 then .node h (NatTrie.insert fuel e (n / 2)) o
    else .node h e (NatTrie.insert fuel o (n / 2))

def NatTrie.union : NatTrie → NatTrie → NatTrie
  | .empty, t => t
  | t, .empty => t
  | .node h₁ e₁ o₁, .node h₂ e₂ o₂ =>
    .node (h₁ || h₂) (NatTrie.union e₁ e₂) (NatTrie.union o₁ o₂)

def listMemNat : List Nat → Nat → Bool
  | [], _ => false
  | x :: xs, y => (x == y) || listMemNat xs y

/-- Variable-level set: `O(log N)` trie for indices `< 2^32`, exact list fallback above `2^32`. -/
structure NatSet : Type where
  trie : NatTrie
  big : List Nat
  deriving Repr, DecidableEq, Inhabited

def NatSet.empty : NatSet := ⟨.empty, []⟩

def NatSet.mem (s : NatSet) (n : Nat) : Bool :=
  s.trie.mem n || listMemNat s.big n

def NatSet.insert (s : NatSet) (n : Nat) : NatSet :=
  if n < 4294967296 then ⟨NatTrie.insert 32 s.trie n, s.big⟩
  else ⟨s.trie, n :: s.big⟩

def NatSet.union (s₁ s₂ : NatSet) : NatSet :=
  ⟨NatTrie.union s₁.trie s₂.trie, s₁.big ++ s₂.big⟩

/-! ## Keep-tree representation and variable helpers -/

/-- Variable representation in `dceSweep`: `some v` for live binders, `none` for dropped ones. -/
abbrev OptV (V : Ty → Type) (t : Ty) : Type := Option (V t)

/-- Type-erased label representation used during bottom-up liveness analysis. -/
abbrev KL0 : List Ty → Type := fun _ => Unit

def someTup {V : Ty → Type} : (ts : List Ty) → Tup V ts → Tup (OptV V) ts
  | [], () => ()
  | _ :: ts, (x, xs) => (some x, someTup ts xs)

def noneTup {V : Ty → Type} : (ts : List Ty) → Tup (OptV V) ts
  | [] => ()
  | _ :: ts => (none, noneTup ts)

def addArgKey {t : Ty} : Arg K t → NatSet → NatSet
  | .var i, s => s.insert i
  | .imm _, s => s

def addArgKeys : {ts : List Ty} → Tup (Arg K) ts → NatSet → NatSet
  | [], (), s => s
  | _ :: _, (a, as), s => addArgKey a (addArgKeys as s)

def anyLive (b : Nat) : Nat → NatSet → Bool
  | 0, _ => false
  | k + 1, s => s.mem b || anyLive (b + 1) k s

def argSweep {V : Ty → Type} {t : Ty} : Arg (OptV V) t → Arg V t
  | .var (some v) => .var v
  | .var none => .imm default
  | .imm c => .imm c

def argsSweep {V : Ty → Type} : {ts : List Ty} → Tup (Arg (OptV V)) ts → Tup (Arg V) ts
  | [], () => ()
  | _ :: _, (a, as) => (argSweep a, argsSweep as)

mutual
inductive KeepTree : Type
  | leaf : KeepTree
  | node1 (k : KeepTree) : KeepTree
  | letNode (keep : Bool) (k : KeepTree) : KeepTree
  | node2 (t e : KeepTree) : KeepTree
  | groupNode (bs : KeepBlocks) (k : KeepTree) : KeepTree

inductive KeepBlocks : Type
  | nil : KeepBlocks
  | cons (hd : KeepTree) (tl : KeepBlocks) : KeepBlocks
end

/-! ## Bottom-up liveness and top-down sweep -/

mutual
def liveVars {rs : List Ty} (b : Nat) : Expr K KL0 rs → NatSet × KeepTree
  | .let_ (ts := ts) op k =>
    let (s, kt) := liveVars (b + ts.length) (k (Tup.levels ts b))
    if anyLive b ts.length s then
      (addArgKeys op.args s, .letNode true kt)
    else
      (s, .letNode false kt)
  | .load _ a k =>
    let (s, kt) := liveVars (b + 1) (k b)
    (addArgKey a s, .node1 kt)
  | .store v a k =>
    let (s, kt) := liveVars b k
    (addArgKey v (addArgKey a s), .node1 kt)
  | .call _ (bs := bs) args k =>
    let (s, kt) := liveVars (b + bs.length) (k (Tup.levels bs b))
    (addArgKeys args s, .node1 kt)
  | .jnz c t e =>
    let (st, ktt) := liveVars b t
    let (se, kte) := liveVars b e
    (addArgKey c (st.union se), .node2 ktt kte)
  | .jump _ args => (addArgKeys args .empty, .leaf)
  | .ret vs => (addArgKeys vs .empty, .leaf)
  | .exit _ args => (addArgKeys args .empty, .leaf)
  | .hlt => (.empty, .leaf)
  | .group (sig := sig) bodies k =>
    let ls := Tup.units sig
    let (sb, kbs) := liveVarsB b (bodies ls)
    let (sk, ktk) := liveVars b (k ls)
    (sb.union sk, .groupNode kbs ktk)

def liveVarsB {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → Blocks K KL0 rs sig → NatSet × KeepBlocks
  | _, .nil => (.empty, .nil)
  | _, .cons (ts := ts) hd tl =>
    let (sh, kh) := liveVars (b + ts.length) (hd (Tup.levels ts b))
    let (st, kt) := liveVarsB b tl
    (sh.union st, .cons kh kt)
end

mutual
def dceSweep {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (kt : KeepTree) : Expr (OptV V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    match kt with
    | .letNode true kt' =>
      .let_ ⟨op.code, argsSweep op.args⟩ (fun xs => dceSweep kt' (k (someTup ts xs)))
    | .letNode false kt' =>
      dceSweep kt' (k (noneTup ts))
    | _ => .hlt
  | .load t a k =>
    match kt with
    | .node1 kt' => .load t (argSweep a) (fun v => dceSweep kt' (k (some v)))
    | _ => .hlt
  | .store v a k =>
    match kt with
    | .node1 kt' => .store (argSweep v) (argSweep a) (dceSweep kt' k)
    | _ => .hlt
  | .call f (bs := bs) args k =>
    match kt with
    | .node1 kt' =>
      .call f (argsSweep args) (fun xs => dceSweep kt' (k (someTup bs xs)))
    | _ => .hlt
  | .jnz c t e =>
    match kt with
    | .node2 ktt kte => .jnz (argSweep c) (dceSweep ktt t) (dceSweep kte e)
    | _ => .hlt
  | .jump j args => .jump j (argsSweep args)
  | .ret vs => .ret (argsSweep vs)
  | .exit f args => .exit f (argsSweep args)
  | .hlt => .hlt
  | .group bodies k =>
    match kt with
    | .groupNode kbs ktk =>
      .group (fun Js => dceSweepB kbs (bodies Js)) (fun Js => dceSweep ktk (k Js))
    | _ => .hlt

def dceSweepB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (kbs : KeepBlocks) : {sig : List (List Ty)} → Blocks (OptV V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    match kbs with
    | .cons kh kt => .cons (fun xs => dceSweep kh (b (someTup ts xs))) (dceSweepB kt bs)
    | _ => .cons (fun _ => .hlt) (dceSweepB .nil bs)
end

/-- Run dead-code elimination on a closed function `Func`. -/
def Func.dce {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let kt := (liveVars as.length (f K KL0 (Tup.levels as 0))).2
  fun V L xs => dceSweep kt (f (OptV V) L (someTup as xs))

end LeanQbe.T
