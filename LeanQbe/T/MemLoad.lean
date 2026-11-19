module

public import LeanQbe.T.OptUtil
public import LeanQbe.T.Fold
public import LeanQbe.T.Dce

/-!
# Lexical Memory Load/Store Optimization (`MemLoad`, `DeadLoadElim`) and `AssumeElim` (`O-M2`)

1. **`Func.memLoad`**: two-phase PHOAS lexical load CSE and store-to-load forwarding:
   - Phase 1 (`analyzeMem` / `analyzeMemB` at `K`, `KL0`): builds a `MemSumTree` computing
     conservative may-store / may-call `MemSummary` summaries for every `.group` (covering both
     `bodies` and the group entry `k`), tracking symbolic `(baseKey, off)` through `add i64`,
     `sub i64`, and `copy i64` chains via `Trie (FKey i64 × BitVec 64)`.
   - Phase 2 (`memLoadSweep` / `memLoadSweepB` over `MVal V`): threads `baseOff` and a dominating
     cache of `(baseKey, off, ty, val, valKey)` entries:
     * `.load t a k`: forwards matching `(baseKey, off, t)` cache hit `val` directly to `k`; on
       miss emits `.load` and records `(baseKey, off, t, .var v, .var next)`.
     * `.store v a k`: filters cache keeping only entries sharing `baseKey` with provably disjoint
       `BitVec 64` offset spans (cancelling `base` even across `base + off` wraparound), and when
       `t.bytes ≤ 2 ^ 64` inserts `(baseKey, off, t, v.mout, v.mkey)` for `k`.
     * `.call`: flushes cache (`[]`).
     * `.jnz`: both arms inherit the current cache.
     * `.group bodies k`: entry `k` inherits the current cache, while `bodies` receives the subset
       of `cache` disjoint from the group's `MemSummary` (preserving the full cache when
       read-only, disjoint fields when stores are to tracked bases, and flushing on calls or
       untracked stores).
2. **`Func.deadLoadElim`**: optional dead-load elimination via bottom-up `K` liveness
   (`liveLoadVars`) + `deadLoadSweep`, dropping unused `.load`s while keeping used loads and all
   `let_`/`store`/`call`/`exit` nodes.
3. **`Func.assumeElim`**: rewrites `.jnz c t .hlt → t` and `.jnz c .hlt e → e` bottom-up across
   `Expr` and `Blocks`.

Correctness (`LeanQbe/T/MemLoadLemmas.lean`): `Func.memLoad_wf`, `Func.memLoad_spec`,
`Func.deadLoadElim_wf`, `Func.deadLoadElim_spec`, `Func.assumeElim_wf`, `Func.assumeElim_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## `MVal`, symbolic `(baseKey, off)` map, and memory cache -/

/-- Input value representation in `memLoad`: replacement operand paired with symbolic `FKey`. -/
structure MVal (V : Ty → Type) (t : Ty) : Type where
  out : Arg V t
  key : FKey t

/-- Wrap a bound output variable `v` with fresh lexical key `next`. -/
def MVal.fresh {V : Ty → Type} {t : Ty} (v : V t) (next : Nat) : MVal V t :=
  ⟨.var v, .var next⟩

/-- Output operand of an `Arg (MVal V) t`. -/
def Arg.mout {V : Ty → Type} {t : Ty} : Arg (MVal V) t → Arg V t
  | .var m => m.out
  | .imm c => .imm c

/-- Symbolic key of an `Arg (MVal V) t`. -/
def Arg.mkey {V : Ty → Type} {t : Ty} : Arg (MVal V) t → FKey t
  | .var m => m.key
  | .imm c => .imm c

/-- Map `Arg.mout` across an operand tuple. -/
abbrev tupMOut {V : Ty → Type} : {ts : List Ty} → Tup (Arg (MVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => Arg.mout

/-- Extract symbolic keys across an operand tuple. -/
def tupMKey {V : Ty → Type} : {ts : List Ty} → Tup (Arg (MVal V)) ts → Tup FKey ts
  | [], () => ()
  | _ :: _, (a, as) => (a.mkey, tupMKey as)

/-- Wrap bound output variables `xs : Tup V ts` into fresh `MVal V`s starting at `next`. -/
abbrev freshMVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (MVal V) ts :=
  tupFreshWith fun x next => MVal.fresh x next

/-- Fast kernel-reducible boolean equality on `FKey i64`. -/
def fkey64Beq : FKey i64 → FKey i64 → Bool
  | .var i, .var j => i == j
  | .imm a, .imm b => a == b
  | _, _ => false

/-- Symbolic `(baseKey, off)` map keyed by de Bruijn variable level (`O(log N)` binary trie). -/
abbrev BaseOffMap := Trie (FKey i64 × BitVec 64)

/-- Resolve an `i64` symbolic key against `baseOff`, mapping `.imm c` to `(.imm 0#64, c)`. -/
def resolveKey (baseOff : BaseOffMap) : FKey i64 → FKey i64 × BitVec 64
  | .var i => baseOff.getD i (.var i, 0#64)
  | .imm c => (.imm 0#64, c)

/-- Update `baseOff` across one `let_` binding using symbolic operand keys `kargs`. -/
def stepBaseOff (next : Nat) (baseOff : BaseOffMap) :
    {sig ts : List Ty} → OpCode sig ts → Tup FKey sig → BaseOffMap
  | _, _, .add (.bits n), (x, y, ()) =>
    if h : n = 64 then
      let x' : FKey (.bits 64) := h ▸ x
      let y' : FKey (.bits 64) := h ▸ y
      match y' with
      | .imm d =>
        let (b, off) := resolveKey baseOff x'
        baseOff.insert next (b, off + d)
      | .var _ =>
        match x' with
        | .imm d =>
          let (b, off) := resolveKey baseOff y'
          baseOff.insert next (b, off + d)
        | .var _ => baseOff
    else baseOff
  | _, _, .sub (.bits n), (x, y, ()) =>
    if h : n = 64 then
      let x' : FKey (.bits 64) := h ▸ x
      let y' : FKey (.bits 64) := h ▸ y
      match y' with
      | .imm d =>
        let (b, off) := resolveKey baseOff x'
        baseOff.insert next (b, off - d)
      | .var _ => baseOff
    else baseOff
  | _, _, .copy (.bits n), (x, ()) =>
    if h : n = 64 then
      let x' : FKey (.bits 64) := h ▸ x
      baseOff.insert next (resolveKey baseOff x')
    else baseOff
  | _, _, _, _ => baseOff

/-- A dominating memory cache entry `(baseKey, off, ty, val, valKey)`. -/
structure CacheEntry (V : Ty → Type) : Type where
  baseKey : FKey i64
  off : BitVec 64
  ty : Ty
  val : Arg V ty
  valKey : FKey ty

/-- `BitVec 64` offset-interval disjointness predicate (cancelling a shared `base` even when
`base + off` wraps around `2 ^ 64`). -/
def spanDisjoint (off₁ : BitVec 64) (bytes₁ : Nat) (off₂ : BitVec 64) (bytes₂ : Nat) : Bool :=
  (off₁.toNat + bytes₁ ≤ off₂.toNat && off₂.toNat + bytes₂ ≤ 2 ^ 64) ||
  (off₂.toNat + bytes₂ ≤ off₁.toNat && off₁.toNat + bytes₁ ≤ 2 ^ 64)

/-- True iff `e` shares `baseKey` `b` and occupies a provably disjoint offset span from
`(b, off, bytes)`. -/
def entryDisjointWrite (b : FKey i64) (off : BitVec 64) (bytes : Nat)
    {V : Ty → Type} (e : CacheEntry V) : Bool :=
  fkey64Beq e.baseKey b && spanDisjoint off bytes e.off e.ty.bytes

/-- Filter `cache` keeping only entries provably disjoint from `(b, off, bytes)`. -/
def filterCacheWrite {V : Ty → Type} (b : FKey i64) (off : BitVec 64) (bytes : Nat)
    (cache : List (CacheEntry V)) : List (CacheEntry V) :=
  cache.filter (entryDisjointWrite b off bytes)

/-- Look up a dominating cache entry matching `(b, off, t)`. -/
def lookupCache {V : Ty → Type} (b : FKey i64) (off : BitVec 64) (t : Ty) :
    List (CacheEntry V) → Option (MVal V t)
  | [] => none
  | e :: rest =>
    if fkey64Beq e.baseKey b && e.off == off then
      match tyDecEq e.ty t with
      | isTrue h => some ⟨h ▸ e.val, h ▸ e.valKey⟩
      | isFalse _ => lookupCache b off t rest
    else lookupCache b off t rest

/-! ## Phase 1: conservative may-store / may-call group summaries at `K` -/

/-- A tracked byte span written by a `.store` instruction. -/
structure WriteSpan : Type where
  baseKey : FKey i64
  off : BitVec 64
  bytes : Nat

/-- Conservative may-store / may-call summary of a subexpression or block list. -/
inductive MemSummary : Type
  | exact (writes : List WriteSpan)
  | unknown

/-- Empty (read-only, call-free) summary. -/
def MemSummary.empty : MemSummary := .exact []

/-- Record a `.store` write span into a `MemSummary`. -/
def MemSummary.addWrite (w : WriteSpan) : MemSummary → MemSummary
  | .unknown => .unknown
  | .exact ws => .exact (w :: ws)

/-- Join two `MemSummary` values conservatively. -/
def MemSummary.join : MemSummary → MemSummary → MemSummary
  | .unknown, _ | _, .unknown => .unknown
  | .exact ws₁, .exact ws₂ => .exact (ws₁ ++ ws₂)

/-- True iff entry `e` is provably disjoint from every write in `s` (and `s` has no `.call`). -/
def summaryDisjointEntry (s : MemSummary) {V : Ty → Type} (e : CacheEntry V) : Bool :=
  match s with
  | .unknown => false
  | .exact ws => ws.all fun w => entryDisjointWrite w.baseKey w.off w.bytes e

/-- Filter `cache` keeping only entries preserved across summary `s`. -/
def filterCacheSummary {V : Ty → Type} (s : MemSummary) (cache : List (CacheEntry V)) :
    List (CacheEntry V) :=
  cache.filter (summaryDisjointEntry s)

mutual
/-- Structural summary tree mirroring `Expr` to guide `memLoadSweep` across `.group`s. -/
inductive MemSumTree : Type
  | leaf : MemSumTree
  | node1 (k : MemSumTree) : MemSumTree
  | node2 (t e : MemSumTree) : MemSumTree
  | groupNode (sum : MemSummary) (bs : MemSumBlocks) (k : MemSumTree) : MemSumTree

/-- Structural summary tree mirroring `Blocks`. -/
inductive MemSumBlocks : Type
  | nil : MemSumBlocks
  | cons (hd : MemSumTree) (tl : MemSumBlocks) : MemSumBlocks
end

mutual
/-- Compute conservative may-store / may-call summary tree over `Expr K KL0 rs`. -/
def analyzeMem {rs : List Ty} (next : Nat) (baseOff : BaseOffMap) :
    Expr K KL0 rs → MemSummary × MemSumTree
  | .let_ (ts := ts) op k =>
    let baseOff' := stepBaseOff next baseOff op.code op.args
    let (s, kt) := analyzeMem (next + ts.length) baseOff' (k (Tup.levels ts next))
    (s, .node1 kt)
  | .load _ _ k =>
    let (s, kt) := analyzeMem (next + 1) baseOff (k next)
    (s, .node1 kt)
  | .store (t := t) _ a k =>
    let (b, off) := resolveKey baseOff a
    let (s, kt) := analyzeMem next baseOff k
    (MemSummary.addWrite ⟨b, off, t.bytes⟩ s, .node1 kt)
  | .call _ (bs := bs) _ k =>
    let (_, kt) := analyzeMem (next + bs.length) baseOff (k (Tup.levels bs next))
    (.unknown, .node1 kt)
  | .jnz _ t e =>
    let (st, ktt) := analyzeMem next baseOff t
    let (se, kte) := analyzeMem next baseOff e
    (st.join se, .node2 ktt kte)
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => (.empty, .leaf)
  | .group (sig := sig) bodies k =>
    let ls := Tup.units sig
    let (sb, bs) := analyzeMemB next baseOff (bodies ls)
    let (sk, kt) := analyzeMem next baseOff (k ls)
    let sum := sb.join sk
    (sum, .groupNode sum bs kt)

/-- Block-list companion of `analyzeMem`. -/
def analyzeMemB {rs : List Ty} (next : Nat) (baseOff : BaseOffMap) :
    {sig : List (List Ty)} → Blocks K KL0 rs sig → MemSummary × MemSumBlocks
  | _, .nil => (.empty, .nil)
  | _, .cons (ts := ts) hd tl =>
    let (sh, kh) := analyzeMem (next + ts.length) baseOff (hd (Tup.levels ts next))
    let (st, kt) := analyzeMemB next baseOff tl
    (sh.join st, .cons kh kt)
end

/-! ## Phase 2: `memLoadSweep` and `Func.memLoad` -/

mutual
/-- Lexical load-CSE and store-to-load forwarding sweep guided by `MemSumTree`. -/
def memLoadSweep {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (baseOff : BaseOffMap) (cache : List (CacheEntry V))
    (mst : MemSumTree) : Expr (MVal V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    let baseOff' := stepBaseOff next baseOff op.code (tupMKey op.args)
    .let_ ⟨op.code, tupMOut op.args⟩ fun xs =>
      memLoadSweep (next + ts.length) baseOff' cache kt (k (freshMVals ts xs next))
  | .load t a k =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    let (b, off) := resolveKey baseOff a.mkey
    match lookupCache b off t cache with
    | some cached =>
      memLoadSweep (next + 1) baseOff cache kt (k cached)
    | none =>
      .load t a.mout fun v =>
        let cache' := ⟨b, off, t, .var v, .var next⟩ :: cache
        memLoadSweep (next + 1) baseOff cache' kt (k (MVal.fresh v next))
  | .store (t := t) v a k =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    let (b, off) := resolveKey baseOff a.mkey
    let cache' := filterCacheWrite b off t.bytes cache
    let cache'' :=
      if t.bytes ≤ 2 ^ 64 then ⟨b, off, t, v.mout, v.mkey⟩ :: cache'
      else cache'
    .store v.mout a.mout (memLoadSweep next baseOff cache'' kt k)
  | .call f (bs := bs) args k =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    .call f (tupMOut args) fun xs =>
      memLoadSweep (next + bs.length) baseOff [] kt (k (freshMVals bs xs next))
  | .jnz c t e =>
    let (ktt, kte) := match mst with | .node2 ktt kte => (ktt, kte) | _ => (.leaf, .leaf)
    .jnz c.mout (memLoadSweep next baseOff cache ktt t) (memLoadSweep next baseOff cache kte e)
  | .jump j args => .jump j (tupMOut args)
  | .ret vs => .ret (tupMOut vs)
  | .exit f args => .exit f (tupMOut args)
  | .hlt => .hlt
  | .group bodies k =>
    let (sum, bsMST, kMST) := match mst with
      | .groupNode sum bsMST kMST => (sum, bsMST, kMST)
      | _ => (.unknown, .nil, .leaf)
    let cacheB := filterCacheSummary sum cache
    .group
      (fun Js => memLoadSweepB next baseOff cacheB bsMST (bodies Js))
      (fun Js => memLoadSweep next baseOff cache kMST (k Js))

/-- Block-list companion of `memLoadSweep`. -/
def memLoadSweepB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (baseOff : BaseOffMap) (cache : List (CacheEntry V))
    (bsMST : MemSumBlocks) : {sig : List (List Ty)} → Blocks (MVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    let (kh, kt) := match bsMST with | .cons kh kt => (kh, kt) | _ => (.leaf, .nil)
    .cons (fun xs => memLoadSweep (next + ts.length) baseOff cache kh (b (freshMVals ts xs next)))
      (memLoadSweepB next baseOff cache kt bs)
end

/-- Run lexical memory load CSE and store-to-load forwarding on a closed `Func`. -/
def Func.memLoad {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let mst := (analyzeMem as.length .empty (f K KL0 (Tup.levels as 0))).2
  fun V L xs => memLoadSweep as.length .empty [] mst (f (MVal V) L (freshMVals as xs 0))

/-! ## Optional dead-load elimination (`Func.deadLoadElim`) -/

mutual
/-- Bottom-up liveness analysis over `Expr K KL0 rs` tracking which `.load` results are used. -/
def liveLoadVars {rs : List Ty} (b : Nat) : Expr K KL0 rs → Trie Unit × KeepTree
  | .let_ (ts := ts) op k =>
    let (s, kt) := liveLoadVars (b + ts.length) (k (Tup.levels ts b))
    (addArgKeys op.args s, .node1 kt)
  | .load _ a k =>
    let (s, kt) := liveLoadVars (b + 1) (k b)
    if (s.find? b).isSome then
      (addArgKey a s, .letNode true kt)
    else
      (s, .letNode false kt)
  | .store v a k =>
    let (s, kt) := liveLoadVars b k
    (addArgKey v (addArgKey a s), .node1 kt)
  | .call _ (bs := bs) args k =>
    let (s, kt) := liveLoadVars (b + bs.length) (k (Tup.levels bs b))
    (addArgKeys args s, .node1 kt)
  | .jnz c t e =>
    let (st, ktt) := liveLoadVars b t
    let (se, kte) := liveLoadVars b e
    (addArgKey c (trieUnion st se), .node2 ktt kte)
  | .jump _ args => (addArgKeys args .empty, .leaf)
  | .ret vs => (addArgKeys vs .empty, .leaf)
  | .exit _ args => (addArgKeys args .empty, .leaf)
  | .hlt => (.empty, .leaf)
  | .group (sig := sig) bodies k =>
    let ls := Tup.units sig
    let (sb, kbs) := liveLoadVarsB b (bodies ls)
    let (sk, ktk) := liveLoadVars b (k ls)
    (trieUnion sb sk, .groupNode kbs ktk)

/-- Block-list companion of `liveLoadVars`. -/
def liveLoadVarsB {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → Blocks K KL0 rs sig → Trie Unit × KeepBlocks
  | _, .nil => (.empty, .nil)
  | _, .cons (ts := ts) hd tl =>
    let (sh, kh) := liveLoadVars (b + ts.length) (hd (Tup.levels ts b))
    let (st, kt) := liveLoadVarsB b tl
    (trieUnion sh st, .cons kh kt)
end

mutual
/-- Top-down sweep dropping unused `.load` bindings guided by `liveLoadVars`'s `KeepTree`. -/
def deadLoadSweep {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (kt : KeepTree) : Expr (OptV V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    match kt with
    | .node1 kt' =>
      .let_ ⟨op.code, argsSweep op.args⟩ fun xs => deadLoadSweep kt' (k (someTup ts xs))
    | _ => .hlt
  | .load t a k =>
    match kt with
    | .letNode true kt' => .load t (argSweep a) fun v => deadLoadSweep kt' (k (some v))
    | .letNode false kt' => deadLoadSweep kt' (k none)
    | _ => .hlt
  | .store v a k =>
    match kt with
    | .node1 kt' => .store (argSweep v) (argSweep a) (deadLoadSweep kt' k)
    | _ => .hlt
  | .call f (bs := bs) args k =>
    match kt with
    | .node1 kt' =>
      .call f (argsSweep args) fun xs => deadLoadSweep kt' (k (someTup bs xs))
    | _ => .hlt
  | .jnz c t e =>
    match kt with
    | .node2 ktt kte => .jnz (argSweep c) (deadLoadSweep ktt t) (deadLoadSweep kte e)
    | _ => .hlt
  | .jump j args => .jump j (argsSweep args)
  | .ret vs => .ret (argsSweep vs)
  | .exit f args => .exit f (argsSweep args)
  | .hlt => .hlt
  | .group bodies k =>
    match kt with
    | .groupNode kbs ktk =>
      .group (fun Js => deadLoadSweepB kbs (bodies Js)) (fun Js => deadLoadSweep ktk (k Js))
    | _ => .hlt

/-- Block-list companion of `deadLoadSweep`. -/
def deadLoadSweepB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (kbs : KeepBlocks) : {sig : List (List Ty)} → Blocks (OptV V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    match kbs with
    | .cons kh kt => .cons (fun xs => deadLoadSweep kh (b (someTup ts xs))) (deadLoadSweepB kt bs)
    | _ => .cons (fun _ => .hlt) (deadLoadSweepB .nil bs)
end

/-- Drop pure unused `.load` instructions from a closed `Func`. -/
def Func.deadLoadElim {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let kt := (liveLoadVars as.length (f K KL0 (Tup.levels as 0))).2
  fun V L xs => deadLoadSweep kt (f (OptV V) L (someTup as xs))

/-! ## `AssumeElim`: `.jnz c t .hlt → t` and `.jnz c .hlt e → e` -/

/-- True iff `e` is `.hlt`. -/
def Expr.isHlt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} : Expr V L rs → Bool
  | .hlt => true
  | _ => false

/-- Simplify `.jnz c t .hlt → t` and `.jnz c .hlt e → e`. -/
def mkJnzAssume {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) (t e : Expr V L rs) : Expr V L rs :=
  if e.isHlt then t
  else if t.isHlt then e
  else .jnz c t e

mutual
/-- Eliminate impossible branches leading to `.hlt` anywhere in `Expr`. -/
def assumeElim {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} : Expr V L rs → Expr V L rs
  | .let_ op k => .let_ op fun xs => assumeElim (k xs)
  | .load t a k => .load t a fun v => assumeElim (k v)
  | .store v a k => .store v a (assumeElim k)
  | .call f args k => .call f args fun xs => assumeElim (k xs)
  | .jnz c t e => mkJnzAssume c (assumeElim t) (assumeElim e)
  | .jump j args => .jump j args
  | .ret vs => .ret vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group bodies k => .group (fun Js => assumeElimB (bodies Js)) (fun Js => assumeElim (k Js))

/-- Block-list companion of `assumeElim`. -/
def assumeElimB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks V L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons (fun xs => assumeElim (b xs)) (assumeElimB bs)
end

/-- Run `assumeElim` on a closed `Func`. -/
def Func.assumeElim {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => LeanQbe.T.assumeElim (f V L xs)

end LeanQbe.T
