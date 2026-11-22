module

public import LeanQbe.T.OptUtil
public import LeanQbe.T.Flat

/-!
# Lexical Memory Load/Store Optimization (`MemLoad`) and `AssumeElim` (`O-M2`)

1. **`Func.memLoad`**: two-phase PHOAS lexical load CSE and store-to-load forwarding:
   - Phase 1 (`analyzeMem` / `analyzeMemB` at `K`, `KL`): builds a `MemSumTree` computing
     conservative may-store / may-call `MemSummary` summaries for every `.group` (using
     `anyLive` to avoid self-kill on acyclic join blocks), tracking symbolic indexed addresses
     `(base, idx, scale, off)` through `add`, `sub`, `mul`, `shl`, `copy`, `zext 32 64`, and
     `sext 32 64` chains via `Trie BaseOffEntry`.
   - Phase 2 (`memLoadSweep` / `memLoadSweepB` over `MVal V`): threads `baseOff` and a dominating
     cache of `(ak, ty, val, valKey)` entries:
     * `.load t a k`: forwards matching `(ak, t)` cache hit `val` directly to `k`; on miss emits
       `.load` and records `(ak, t, .var v, .var next)`.
     * `.store v a k`: filters cache keeping only entries sharing `(base, idx, scale)` with
       provably disjoint `BitVec 64` offset spans (cancelling `base + idx * scale` even across
       wraparound), and when `t.bytes ≤ 2 ^ 64` inserts `(ak, t, v.mout, v.mkey)` for `k`.
     * `.call`: flushes cache (`[]`).
     * `.jnz`: both arms inherit the current cache.
     * `.group bodies k`: entry `k` inherits the current cache, while `bodies` receives the subset
       of `cache` disjoint from the group's entry summary (`sk` when `bodies` is acyclic,
       `sb.join sk` otherwise).
2. **`Func.assumeElim`**: rewrites `.jnz c t .hlt → t` and `.jnz c .hlt e → e` bottom-up across
   `Expr` and `Blocks`.

Correctness (`LeanQbe/T/MemLoadLemmas.lean`): `Func.memLoad_wf`, `Func.memLoad_spec`,
`Func.deadLoadElim_wf`, `Func.deadLoadElim_spec`, `Func.assumeElim_wf`, `Func.assumeElim_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## `MVal`, symbolic `(base, idx, scale, off)` map, and memory cache -/

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

/-- Fast kernel-reducible boolean equality on `FKey (.bits 32)`. -/
def fkey32Beq : FKey (.bits 32) → FKey (.bits 32) → Bool
  | .var i, .var j => i == j
  | .imm a, .imm b => a == b
  | _, _ => false

/-- Symbolic index expression tracked for `(base, idx, scale, off)` addressing. -/
inductive IdxKey : Type
  | none : IdxKey
  | k64 (k : FKey i64) : IdxKey
  | zext32 (k : FKey (.bits 32)) : IdxKey
  | sext32 (k : FKey (.bits 32)) : IdxKey

/-- Fast kernel-reducible boolean equality on `IdxKey`. -/
def idxKeyBeq : IdxKey → IdxKey → Bool
  | .none, .none => true
  | .k64 a, .k64 b => fkey64Beq a b
  | .zext32 a, .zext32 b => fkey32Beq a b
  | .sext32 a, .sext32 b => fkey32Beq a b
  | _, _ => false

/-- Symbolic indexed address key representing `base + idx * scale + off`. -/
structure MemAddrKey : Type where
  base : FKey i64
  idx : IdxKey
  scale : BitVec 64
  off : BitVec 64

/-- Constant `MemAddrKey` representing `0 + 0 * 0 + c`. -/
def MemAddrKey.const (c : BitVec 64) : MemAddrKey :=
  ⟨.imm 0#64, .none, 0#64, c⟩

/-- Variable `MemAddrKey` representing `v + 0 * 0 + 0`. -/
def MemAddrKey.var (i : Nat) : MemAddrKey :=
  ⟨.var i, .none, 0#64, 0#64⟩

/-- True iff two `MemAddrKey`s share identical `(base, idx, scale)`. -/
def MemAddrKey.sameBase (a b : MemAddrKey) : Bool :=
  fkey64Beq a.base b.base && idxKeyBeq a.idx b.idx && a.scale == b.scale

/-- True iff two `MemAddrKey`s share identical `(base, idx, scale, off)`. -/
def MemAddrKey.beq (a b : MemAddrKey) : Bool :=
  a.sameBase b && a.off == b.off

/-- Per-variable symbolic address entry pairing `MemAddrKey` with `zext32`/`sext32` index. -/
structure BaseOffEntry : Type where
  ak : MemAddrKey
  idxSelf : IdxKey

/-- Symbolic address map keyed by de Bruijn variable level (`O(log N)` binary trie). -/
abbrev BaseOffMap := Trie BaseOffEntry

/-- Resolve an `i64` symbolic key against `baseOff` to its `BaseOffEntry`. -/
def resolveEntry (baseOff : BaseOffMap) : FKey i64 → BaseOffEntry
  | .var i => baseOff.getD i ⟨.var i, .k64 (.var i)⟩
  | .imm c => ⟨.const c, if c == 0#64 then .none else .k64 (.imm c)⟩

/-- Resolve an `i64` symbolic key against `baseOff` to its `MemAddrKey`. -/
def resolveKey (baseOff : BaseOffMap) (k : FKey i64) : MemAddrKey :=
  (resolveEntry baseOff k).ak

/-- Resolve an `i64` symbolic key against `baseOff` to its `IdxKey`. -/
def resolveIdx (baseOff : BaseOffMap) (k : FKey i64) : IdxKey :=
  (resolveEntry baseOff k).idxSelf

/-- Combine two `i64` keys under addition into a canonical `MemAddrKey` when expressible. -/
def addAddr (baseOff : BaseOffMap) (x y : FKey i64) : Option MemAddrKey :=
  let a₁ := resolveKey baseOff x
  let a₂ := resolveKey baseOff y
  if fkey64Beq a₁.base (.imm 0#64) && a₁.scale == 0#64 then
    some { a₂ with off := a₂.off + a₁.off }
  else if fkey64Beq a₂.base (.imm 0#64) && a₂.scale == 0#64 then
    some { a₁ with off := a₁.off + a₂.off }
  else if a₁.scale == 0#64 && fkey64Beq a₂.base (.imm 0#64) then
    some ⟨a₁.base, a₂.idx, a₂.scale, a₁.off + a₂.off⟩
  else if a₂.scale == 0#64 && fkey64Beq a₁.base (.imm 0#64) then
    some ⟨a₂.base, a₁.idx, a₁.scale, a₁.off + a₂.off⟩
  else if a₁.scale == 0#64 && a₂.scale == 0#64 then
    match a₁.base, a₂.base with
    | .var v₁, .var v₂ =>
      if v₁ < v₂ then some ⟨.var v₁, resolveIdx baseOff (.var v₂), 1#64, a₁.off + a₂.off⟩
      else if v₂ < v₁ then some ⟨.var v₂, resolveIdx baseOff (.var v₁), 1#64, a₁.off + a₂.off⟩
      else some ⟨.imm 0#64, resolveIdx baseOff (.var v₁), 2#64, a₁.off + a₂.off⟩
    | _, _ => none
  else none

/-- Combine two `i64` keys under subtraction into an `MemAddrKey` when RHS is constant. -/
def subAddr (baseOff : BaseOffMap) (x y : FKey i64) : Option MemAddrKey :=
  let a₁ := resolveKey baseOff x
  let a₂ := resolveKey baseOff y
  if fkey64Beq a₂.base (.imm 0#64) && a₂.scale == 0#64 then
    some { a₁ with off := a₁.off - a₂.off }
  else none

/-- Scale an `i64` key by constant `d` into an `MemAddrKey` when expressible. -/
def scaleAddr (baseOff : BaseOffMap) (arg : FKey i64) (d : BitVec 64) : Option MemAddrKey :=
  if d == 0#64 then some (.const 0#64)
  else
    let a := resolveKey baseOff arg
    if d == 1#64 then some a
    else if fkey64Beq a.base (.imm 0#64) && a.scale == 0#64 then
      some (.const (a.off * d))
    else if fkey64Beq a.base (.imm 0#64) then
      some ⟨.imm 0#64, a.idx, a.scale * d, a.off * d⟩
    else if a.scale == 0#64 then
      some ⟨.imm 0#64, resolveIdx baseOff a.base, d, a.off * d⟩
    else none

/-- Insert `ak` with fresh self-index `.k64 (.var next)` into `baseOff` when `some`. -/
def insertAddrOpt (next : Nat) (baseOff : BaseOffMap) : Option MemAddrKey → BaseOffMap
  | some ak => baseOff.insert next ⟨ak, .k64 (.var next)⟩
  | none => baseOff

/-- Update `baseOff` for `sig = [i64, i64]`, `ts = [i64]` using `DecidableEq` dispatch. -/
def stepBaseOff2 (next : Nat) (baseOff : BaseOffMap)
    (code : OpCode [i64, i64] [i64]) (x y : FKey i64) : BaseOffMap :=
  if code = .add i64 then insertAddrOpt next baseOff (addAddr baseOff x y)
  else if code = .sub i64 then insertAddrOpt next baseOff (subAddr baseOff x y)
  else if code = .mul i64 then
    let ak? := match y with
      | .imm d => scaleAddr baseOff x d
      | .var _ => match x with | .imm d => scaleAddr baseOff y d | .var _ => none
    insertAddrOpt next baseOff ak?
  else if code = .shl i64 then
    match y with
    | .imm k =>
      insertAddrOpt next baseOff (scaleAddr baseOff x (BitVec.twoPow 64 (k.toNat % 64)))
    | .var _ => baseOff
  else baseOff

/-- Update `baseOff` across one `let_` binding using symbolic operand keys `kargs`. -/
def stepBaseOff (next : Nat) (baseOff : BaseOffMap)
    {sig ts : List Ty} (code : OpCode sig ts) (kargs : Tup FKey sig) : BaseOffMap :=
  if hs : sig = [i64, i64] then
    if ht : ts = [i64] then
      let (x, y, ()) := hs ▸ kargs
      stepBaseOff2 next baseOff (hs ▸ ht ▸ code) x y
    else baseOff
  else if hs : sig = [i64] then
    if ht : ts = [i64] then
      if (hs ▸ ht ▸ code) = .copy i64 then
        let (x, ()) := hs ▸ kargs
        baseOff.insert next (resolveEntry baseOff x)
      else baseOff
    else baseOff
  else if hs : sig = [.bits 32] then
    if ht : ts = [i64] then
      let code' : OpCode [.bits 32] [i64] := hs ▸ ht ▸ code
      let (x, ()) := hs ▸ kargs
      if code' = .zext 32 64 then baseOff.insert next ⟨.var next, .zext32 x⟩
      else if code' = .sext 32 64 then baseOff.insert next ⟨.var next, .sext32 x⟩
      else baseOff
    else baseOff
  else baseOff

/-- A dominating memory cache entry `(ak, ty, val, valKey)`. -/
structure CacheEntry (V : Ty → Type) : Type where
  ak : MemAddrKey
  ty : Ty
  val : Arg V ty
  valKey : FKey ty

/-- `BitVec 64` offset-interval disjointness predicate (cancelling shared `base + idx * scale`
even across `2 ^ 64` wraparound). -/
def spanDisjoint (off₁ : BitVec 64) (bytes₁ : Nat) (off₂ : BitVec 64) (bytes₂ : Nat) : Bool :=
  (off₁.toNat + bytes₁ ≤ off₂.toNat && off₂.toNat + bytes₂ ≤ 2 ^ 64) ||
  (off₂.toNat + bytes₂ ≤ off₁.toNat && off₁.toNat + bytes₁ ≤ 2 ^ 64)

/-- True iff `e` shares `(base, idx, scale)` with `akW` and occupies a provably disjoint offset
span from `(akW, bytesW)`. -/
def entryDisjointWrite (akW : MemAddrKey) (bytesW : Nat)
    {V : Ty → Type} (e : CacheEntry V) : Bool :=
  e.ak.sameBase akW && spanDisjoint akW.off bytesW e.ak.off e.ty.bytes

/-- Filter `cache` keeping only entries provably disjoint from `(ak, bytes)`. -/
def filterCacheWrite {V : Ty → Type} (ak : MemAddrKey) (bytes : Nat)
    (cache : List (CacheEntry V)) : List (CacheEntry V) :=
  cache.filter (entryDisjointWrite ak bytes)

/-- Look up a dominating cache entry matching `(ak, t)`. -/
def lookupCache {V : Ty → Type} (ak : MemAddrKey) (t : Ty) :
    List (CacheEntry V) → Option (MVal V t)
  | [] => none
  | e :: rest =>
    if e.ak.beq ak then
      match tyDecEq e.ty t with
      | isTrue h => some ⟨h ▸ e.val, h ▸ e.valKey⟩
      | isFalse _ => lookupCache ak t rest
    else lookupCache ak t rest

/-! ## Phase 1: conservative may-store / may-call group summaries at `(K, KL)` -/

/-- A tracked byte span written by a `.store` instruction. -/
structure WriteSpan : Type where
  ak : MemAddrKey
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
  | .exact ws => ws.all fun w => entryDisjointWrite w.ak w.bytes e

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
/-- Compute conservative may-store / may-call summary tree and jump-target set over `Expr K KL`. -/
def analyzeMem {rs : List Ty} (next nl : Nat) (baseOff : BaseOffMap) :
    Expr K KL rs → MemSummary × Trie Unit × MemSumTree
  | .let_ (ts := ts) op k =>
    let baseOff' := stepBaseOff next baseOff op.code op.args
    let (s, l, kt) := analyzeMem (next + ts.length) nl baseOff' (k (Tup.levels ts next))
    (s, l, .node1 kt)
  | .load _ _ k =>
    let (s, l, kt) := analyzeMem (next + 1) nl baseOff (k next)
    (s, l, .node1 kt)
  | .store (t := t) _ a k =>
    let ak := resolveKey baseOff a
    let (s, l, kt) := analyzeMem next nl baseOff k
    (MemSummary.addWrite ⟨ak, t.bytes⟩ s, l, .node1 kt)
  | .call _ (bs := bs) _ k =>
    let (_, l, kt) := analyzeMem (next + bs.length) nl baseOff (k (Tup.levels bs next))
    (.unknown, l, .node1 kt)
  | .jnz _ t e =>
    let (st, lt, ktt) := analyzeMem next nl baseOff t
    let (se, le, kte) := analyzeMem next nl baseOff e
    (st.join se, trieUnion lt le, .node2 ktt kte)
  | .jump j _ => (.empty, (Trie.empty).insert j (), .leaf)
  | .ret _ | .exit _ _ | .hlt => (.empty, .empty, .leaf)
  | .group (sig := sig) bodies k =>
    let ls := Tup.levels sig nl
    let nl' := nl + sig.length
    let (sb, lb, bs) := analyzeMemB next nl' baseOff (bodies ls)
    let (sk, lk, kt) := analyzeMem next nl' baseOff (k ls)
    let sum := sb.join sk
    let sumB := if anyLive nl sig.length lb then sum else sk
    (sum, trieUnion lb lk, .groupNode sumB bs kt)

/-- Block-list companion of `analyzeMem`. -/
def analyzeMemB {rs : List Ty} (next nl : Nat) (baseOff : BaseOffMap) :
    {sig : List (List Ty)} → Blocks K KL rs sig → MemSummary × Trie Unit × MemSumBlocks
  | _, .nil => (.empty, .empty, .nil)
  | _, .cons (ts := ts) hd tl =>
    let (sh, lh, kh) := analyzeMem (next + ts.length) nl baseOff (hd (Tup.levels ts next))
    let (st, lt, kt) := analyzeMemB next nl baseOff tl
    (sh.join st, trieUnion lh lt, .cons kh kt)
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
    let ak := resolveKey baseOff a.mkey
    match lookupCache ak t cache with
    | some cached =>
      memLoadSweep (next + 1) baseOff cache kt (k cached)
    | none =>
      .load t a.mout fun v =>
        let cache' := ⟨ak, t, .var v, .var next⟩ :: cache
        memLoadSweep (next + 1) baseOff cache' kt (k (MVal.fresh v next))
  | .store (t := t) v a k =>
    let kt := match mst with | .node1 kt' => kt' | _ => .leaf
    let ak := resolveKey baseOff a.mkey
    let cache' := filterCacheWrite ak t.bytes cache
    let cache'' :=
      if t.bytes ≤ 2 ^ 64 then ⟨ak, t, v.mout, v.mkey⟩ :: cache'
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
  let mst := (analyzeMem as.length 0 .empty (f K KL (Tup.levels as 0))).2.2
  fun V L xs => memLoadSweep as.length .empty [] mst (f (MVal V) L (freshMVals as xs 0))

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
