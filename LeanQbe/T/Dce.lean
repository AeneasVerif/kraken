module

public import LeanQbe.T.OptUtil

/-!
# Dead-Code Elimination (`Func.dce`, `Func.deadLoadElim`)

Two-phase PHOAS dead-binding elimination pass (`liveVarsWith` / `dceSweep` / `Func.dceWith`):
1. Bottom-up pure liveness analysis (`liveVarsWith` / `liveVarsBWith`) over `Expr K KL0 rs` using
   the shared `O(log N)` structural binary trie `Trie Unit` (`OptUtil`), parameterized by
   `dropLets dropLoads : Bool`:
   - When `dropLets` is true, a `let_` binding `[b, b + ts.length)` is kept iff any of its results
     is live in its continuation (`anyLive`), causing chains of dead pure bindings to cascade in a
     single sweep.
   - When `dropLoads` is true, a `.load` binding `b` is kept iff `(s.find? b).isSome`.
   - Side-effectful or control nodes (`store`, `call`, `exit`, `jnz`, `jump`, `ret`, `hlt`,
     `group`) are never dropped, and `group` block liveness is conservatively unioned with the
     continuation's liveness.
2. Top-down reconstruction (`dceSweep` / `dceSweepB`) over `Expr (OptV V) L rs` guided by the
   computed `KeepTree` / `KeepBlocks`.
3. `Func.dce := Func.dceWith true false` (dead `let_` elimination) and
   `Func.deadLoadElim := Func.dceWith false true` (dead `.load` elimination).

Correctness (`LeanQbe/T/DceLemmas.lean`): `OpCode.wp_exists`, `dceWith_wp`, `dceWith_wf`,
`dce_wp`, `dce_wf`, `Func.dce_wf`, `Func.dce_spec`, `Func.deadLoadElim_wf`,
`Func.deadLoadElim_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Keep-tree representation -/

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
def liveVarsWith (dropLets dropLoads : Bool) {rs : List Ty} (b : Nat) :
    Expr K KL0 rs → Trie Unit × KeepTree
  | .let_ (ts := ts) op k =>
    let (s, kt) := liveVarsWith dropLets dropLoads (b + ts.length) (k (Tup.levels ts b))
    if !dropLets || anyLive b ts.length s then
      (addArgKeys op.args s, .letNode true kt)
    else
      (s, .letNode false kt)
  | .load _ a k =>
    let (s, kt) := liveVarsWith dropLets dropLoads (b + 1) (k b)
    if !dropLoads || (s.find? b).isSome then
      (addArgKey a s, .letNode true kt)
    else
      (s, .letNode false kt)
  | .store v a k =>
    let (s, kt) := liveVarsWith dropLets dropLoads b k
    (addArgKey v (addArgKey a s), .node1 kt)
  | .call _ (bs := bs) args k =>
    let (s, kt) := liveVarsWith dropLets dropLoads (b + bs.length) (k (Tup.levels bs b))
    (addArgKeys args s, .node1 kt)
  | .jnz c t e =>
    let (st, ktt) := liveVarsWith dropLets dropLoads b t
    let (se, kte) := liveVarsWith dropLets dropLoads b e
    (addArgKey c (trieUnion st se), .node2 ktt kte)
  | .jump _ args => (addArgKeys args .empty, .leaf)
  | .ret vs => (addArgKeys vs .empty, .leaf)
  | .exit _ args => (addArgKeys args .empty, .leaf)
  | .hlt => (.empty, .leaf)
  | .group (sig := sig) bodies k =>
    let ls := Tup.units sig
    let (sb, kbs) := liveVarsBWith dropLets dropLoads b (bodies ls)
    let (sk, ktk) := liveVarsWith dropLets dropLoads b (k ls)
    (trieUnion sb sk, .groupNode kbs ktk)

def liveVarsBWith (dropLets dropLoads : Bool) {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → Blocks K KL0 rs sig → Trie Unit × KeepBlocks
  | _, .nil => (.empty, .nil)
  | _, .cons (ts := ts) hd tl =>
    let (sh, kh) := liveVarsWith dropLets dropLoads (b + ts.length) (hd (Tup.levels ts b))
    let (st, kt) := liveVarsBWith dropLets dropLoads b tl
    (trieUnion sh st, .cons kh kt)
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
    | .letNode true kt' => .load t (argSweep a) (fun v => dceSweep kt' (k (some v)))
    | .letNode false kt' => dceSweep kt' (k none)
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

/-- Run configurable dead-binding elimination (`dropLets`, `dropLoads`) on a closed `Func`. -/
def Func.dceWith (dropLets dropLoads : Bool) {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let kt := (liveVarsWith dropLets dropLoads as.length (f K KL0 (Tup.levels as 0))).2
  fun V L xs => dceSweep kt (f (OptV V) L (someTup as xs))

/-- Run dead-code elimination (dropping dead `let_` bindings) on a closed `Func`. -/
def Func.dce {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.dceWith true false f

/-- Drop pure unused `.load` instructions from a closed `Func`. -/
def Func.deadLoadElim {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.dceWith false true f

end LeanQbe.T
