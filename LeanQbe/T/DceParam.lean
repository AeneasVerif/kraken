module

public import LeanQbe.T.Dce

/-!
# Dead-Code & Dead Block-Parameter Elimination (`Func.dceP`)

Generalizes `LeanQbe.T.Dce` (`Func.dceWith`) to eliminate dead `.group` block parameters along
with dead pure `let_` bindings (and optionally dead `.load` bindings):

1. Each block parameter list `ts` is paired with a typed keep-mask `Mask ts` (`Bool` per param),
   carried in the `Nat` pre-scan via label instantiation `KLM` and in the PHOAS sweep via
   `NLabel L`.
2. `liveVarsP` / `liveVarsBP` compute per-block liveness masks under a guessed `PTree` plan and
   validate `maskLe newMask guessedMask` (`ok = true`). Starting from `.leaf` ("keep all",
   `rounds = 0`) always succeeds (`liveVarsP_leaf_ok`); extra rounds iterate the computed plan
   to peel join-to-join dead-parameter chains.
3. `dceSweepP` / `dceSweepBP` narrow `.group` signatures (`narrowSig`) and `.jump` operands
   (`tupNarrow`), binding dropped parameters to `none : OptV V t` (`tupWiden`). If a multi-round
   check ever fails, `Func.dcePWith` falls back to `Func.dceWith`.

Correctness (`LeanQbe/T/DceParamLemmas.lean`): `dceP_wp`, `dceP_wf`, `Func.dcePWith_wf`,
`Func.dcePWith_spec`, `Func.dceP_wf`, `Func.dceP_spec`, `liveVarsP_leaf_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace DceParam

/-! ## Mask and narrowed-signature plumbing -/

/-- Typed keep-mask: one `Bool` per parameter of `ts`. -/
abbrev Mask (ts : List Ty) : Type := Tup (fun _ : Ty => Bool) ts

/-- Read a typed mask from an untyped `List Bool` plan (missing entries default to `true`). -/
def maskOf : (ts : List Ty) → List Bool → Mask ts
  | [], _ => ()
  | _ :: ts, m => (m.headD true, maskOf ts m.tail)

/-- Keep the `true`-masked parameter types of `ts`. -/
@[reducible] def narrow : (ts : List Ty) → Mask ts → List Ty
  | [], _ => []
  | t :: ts, (true, m) => t :: narrow ts m
  | _ :: ts, (false, m) => narrow ts m

/-- Keep the `true`-masked parameter types of every block signature in `sig`. -/
@[reducible] def narrowSig : (sig : List (List Ty)) → Tup Mask sig → List (List Ty)
  | [], _ => []
  | ts :: sig, (m, ms) => narrow ts m :: narrowSig sig ms

/-- Project a tuple `Tup f ts` down to the `true`-masked positions of `m`. -/
def tupNarrow {f : Ty → Type} : (ts : List Ty) → (m : Mask ts) → Tup f ts → Tup f (narrow ts m)
  | [], _, _ => ()
  | _ :: ts, (true, m), (x, xs) => (x, tupNarrow ts m xs)
  | _ :: ts, (false, m), (_, xs) => tupNarrow ts m xs

/-- Rebuild a full `OptV` tuple from a narrowed tuple, filling dropped slots with `none`. -/
def tupWiden {V : Ty → Type} :
    (ts : List Ty) → (m : Mask ts) → Tup V (narrow ts m) → Tup (OptV V) ts
  | [], _, _ => ()
  | _ :: ts, (true, m), (x, xs) => (some x, tupWiden ts m xs)
  | _ :: ts, (false, m), xs => (none, tupWiden ts m xs)

/-- Sweep-side label carrying the keep-mask of its own parameter list. -/
inductive NLabel (L : List Ty → Type) : List Ty → Type
  | mk {ts : List Ty} (m : Mask ts) (l : L (narrow ts m)) : NLabel L ts

/-- Wrap narrowed target labels `Tup L (narrowSig sig ms)` into `Tup (NLabel L) sig`. -/
def wrapLabels {L : List Ty → Type} :
    (sig : List (List Ty)) → (ms : Tup Mask sig) → Tup L (narrowSig sig ms) → Tup (NLabel L) sig
  | [], _, _ => ()
  | _ :: sig, (m, ms), (j, js) => (.mk m j, wrapLabels sig ms js)

/-- Pre-scan label representation: guessed keep-mask for the block's parameters. -/
abbrev KLM : List Ty → Type := Mask

/-! ## Plan tree -/

mutual
/-- Structural liveness-and-mask plan tree mirroring `Expr`. -/
inductive PTree : Type
  | leaf : PTree
  | node1 (k : PTree) : PTree
  | letNode (keep : Bool) (k : PTree) : PTree
  | node2 (t e : PTree) : PTree
  | groupNode (bs : PBlocks) (k : PTree) : PTree

/-- Block-list companion of `PTree`, carrying an untyped `List Bool` keep-mask per block. -/
inductive PBlocks : Type
  | nil : PBlocks
  | cons (mask : List Bool) (hd : PTree) (tl : PBlocks) : PBlocks
end

/-- Child plan for single-continuation nodes (`let_`, `load`, `store`, `call`). -/
def PTree.sub1 : PTree → PTree
  | .node1 k | .letNode _ k => k
  | _ => .leaf

/-- Then-branch child plan for `.jnz`. -/
def PTree.subT : PTree → PTree
  | .node2 t _ => t
  | _ => .leaf

/-- Else-branch child plan for `.jnz`. -/
def PTree.subE : PTree → PTree
  | .node2 _ e => e
  | _ => .leaf

/-- Block-list child plan for `.group`. -/
def PTree.subB : PTree → PBlocks
  | .groupNode bs _ => bs
  | _ => .nil

/-- Continuation child plan for `.group`. -/
def PTree.subK : PTree → PTree
  | .groupNode _ k => k
  | _ => .leaf

/-- Head block mask of a `PBlocks` plan. -/
def PBlocks.mask : PBlocks → List Bool
  | .cons m _ _ => m
  | .nil => []

/-- Head block body plan of a `PBlocks` plan. -/
def PBlocks.hd : PBlocks → PTree
  | .cons _ h _ => h
  | .nil => .leaf

/-- Tail block-list plan of a `PBlocks` plan. -/
def PBlocks.tl : PBlocks → PBlocks
  | .cons _ _ t => t
  | .nil => .nil

/-- Extract typed keep-masks for every block in `sig` from a `PBlocks` plan. -/
def PBlocks.masksOf : (sig : List (List Ty)) → PBlocks → Tup Mask sig
  | [], _ => ()
  | ts :: sig, kbs => (maskOf ts kbs.mask, PBlocks.masksOf sig kbs.tl)

/-! ## Pre-scan: liveness under guessed masks -/

/-- Record only the `true`-masked jump operand keys into `s`. -/
def addMasked : {ts : List Ty} → Mask ts → Tup (Arg K) ts → Trie Unit → Trie Unit
  | [], _, _, s => s
  | _ :: _, (true, m), (a, as), s => addArgKey a (addMasked m as s)
  | _ :: _, (false, m), (_, as), s => addMasked m as s

/-- Compute the `List Bool` liveness mask for consecutive parameter levels `[b, b + n)`. -/
def liveMask (b : Nat) : Nat → Trie Unit → List Bool
  | 0, _ => []
  | n + 1, s => (s.find? b).isSome :: liveMask (b + 1) n s

/-- Pointwise mask order `new ⊑ guess`: every kept parameter was assumed live at jumps. -/
def maskLe : {ts : List Ty} → Mask ts → Mask ts → Bool
  | [], _, _ => true
  | _ :: _, (x, n), (y, g) => (!x || y) && maskLe n g

mutual
/-- Bottom-up liveness analysis over `Expr K KLM rs` parameterized by a guessed plan `g`,
returning `(liveSet, newPlan, valid)`. -/
def liveVarsP (dropLets dropLoads : Bool) {rs : List Ty} (g : PTree) (b : Nat) :
    Expr K KLM rs → Trie Unit × PTree × Bool
  | .let_ (ts := ts) op k =>
    let (s, kt, ok) :=
      liveVarsP dropLets dropLoads g.sub1 (b + ts.length) (k (Tup.levels ts b))
    if !dropLets || anyLive b ts.length s then (addArgKeys op.args s, .letNode true kt, ok)
    else (s, .letNode false kt, ok)
  | .load _ a k =>
    let (s, kt, ok) := liveVarsP dropLets dropLoads g.sub1 (b + 1) (k b)
    if !dropLoads || (s.find? b).isSome then (addArgKey a s, .letNode true kt, ok)
    else (s, .letNode false kt, ok)
  | .store v a k =>
    let (s, kt, ok) := liveVarsP dropLets dropLoads g.sub1 b k
    (addArgKey v (addArgKey a s), .node1 kt, ok)
  | .call _ (bs := bs) args k =>
    let (s, kt, ok) :=
      liveVarsP dropLets dropLoads g.sub1 (b + bs.length) (k (Tup.levels bs b))
    (addArgKeys args s, .node1 kt, ok)
  | .jnz c t e =>
    let (st, ktt, okt) := liveVarsP dropLets dropLoads g.subT b t
    let (se, kte, oke) := liveVarsP dropLets dropLoads g.subE b e
    (addArgKey c (trieUnion st se), .node2 ktt kte, okt && oke)
  | .jump m args => (addMasked m args .empty, .leaf, true)
  | .ret vs => (addArgKeys vs .empty, .leaf, true)
  | .exit _ args => (addArgKeys args .empty, .leaf, true)
  | .hlt => (.empty, .leaf, true)
  | .group (sig := sig) bodies k =>
    let ls := g.subB.masksOf sig
    let (sb, kbs, okb) := liveVarsBP dropLets dropLoads g.subB b (bodies ls)
    let (sk, ktk, okk) := liveVarsP dropLets dropLoads g.subK b (k ls)
    (trieUnion sb sk, .groupNode kbs ktk, okb && okk)

/-- Block-list companion of `liveVarsP`. -/
def liveVarsBP (dropLets dropLoads : Bool) {rs : List Ty} (g : PBlocks) (b : Nat) :
    {sig : List (List Ty)} → Blocks K KLM rs sig → Trie Unit × PBlocks × Bool
  | _, .nil => (.empty, .nil, true)
  | _, .cons (ts := ts) hd tl =>
    let (sh, kh, okh) :=
      liveVarsP dropLets dropLoads g.hd (b + ts.length) (hd (Tup.levels ts b))
    let (st, kt, okt) := liveVarsBP dropLets dropLoads g.tl b tl
    let m := liveMask b ts.length sh
    (trieUnion sh st, .cons m kh kt, maskLe (maskOf ts m) (maskOf ts g.mask) && okh && okt)
end

/-! ## Top-down PHOAS sweep -/

mutual
/-- Reconstruct a narrowed `Expr V L rs` from `Expr (OptV V) (NLabel L) rs` using `kt`. -/
def dceSweepP {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (kt : PTree) : Expr (OptV V) (NLabel L) rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    match kt with
    | .letNode true kt' =>
      .let_ ⟨op.code, argsSweep op.args⟩ (fun xs => dceSweepP kt' (k (someTup ts xs)))
    | .letNode false kt' => dceSweepP kt' (k (noneTup ts))
    | _ => .hlt
  | .load t a k =>
    match kt with
    | .letNode true kt' => .load t (argSweep a) (fun v => dceSweepP kt' (k (some v)))
    | .letNode false kt' => dceSweepP kt' (k none)
    | _ => .hlt
  | .store v a k =>
    match kt with
    | .node1 kt' => .store (argSweep v) (argSweep a) (dceSweepP kt' k)
    | _ => .hlt
  | .call f (bs := bs) args k =>
    match kt with
    | .node1 kt' => .call f (argsSweep args) (fun xs => dceSweepP kt' (k (someTup bs xs)))
    | _ => .hlt
  | .jnz c t e =>
    match kt with
    | .node2 ktt kte => .jnz (argSweep c) (dceSweepP ktt t) (dceSweepP kte e)
    | _ => .hlt
  | .jump (ts := ts) (.mk m l) args => .jump l (tupNarrow ts m (argsSweep args))
  | .ret vs => .ret (argsSweep vs)
  | .exit f args => .exit f (argsSweep args)
  | .hlt => .hlt
  | .group (sig := sig) bodies k =>
    match kt with
    | .groupNode kbs ktk =>
      .group (sig := narrowSig sig (kbs.masksOf sig))
        (fun Js => dceSweepBP kbs (bodies (wrapLabels sig (kbs.masksOf sig) Js)))
        (fun Js => dceSweepP ktk (k (wrapLabels sig (kbs.masksOf sig) Js)))
    | _ => .hlt

/-- Block-list companion of `dceSweepP`, narrowing each block's signature via `kbs.masksOf`. -/
def dceSweepBP {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (kbs : PBlocks) :
    {sig : List (List Ty)} → Blocks (OptV V) (NLabel L) rs sig →
    Blocks V L rs (narrowSig sig (kbs.masksOf sig))
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => dceSweepP kbs.hd (b (tupWiden ts (maskOf ts kbs.mask) xs)))
      (dceSweepBP kbs.tl bs)
end

/-- Apply `f` `n` times starting from `a`. -/
def iterN {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => iterN f n (f a)

end DceParam

open DceParam in
/-- Configurable dead-binding and dead-`.group`-parameter elimination on a closed `Func`.
`rounds` extra refinement rounds iterate the computed mask plan (`0` = single syntactic round);
falls back to `Func.dceWith` if the plan validity check fails. -/
def Func.dcePWith (dropLets dropLoads : Bool) (rounds : Nat := 0) {as rs : List Ty}
    (f : Func as rs) : Func as rs :=
  let ek := f K KLM (Tup.levels as 0)
  let g := iterN (fun g => (liveVarsP dropLets dropLoads g as.length ek).2.1) rounds .leaf
  let r := liveVarsP dropLets dropLoads g as.length ek
  if r.2.2 then fun V L xs => dceSweepP r.2.1 (f (OptV V) (NLabel L) (someTup as xs))
  else Func.dceWith dropLets dropLoads f

/-- Dead-`let_` and dead-`.group`-parameter elimination on a closed `Func`. -/
def Func.dceP {as rs : List Ty} (f : Func as rs) (rounds : Nat := 0) : Func as rs :=
  Func.dcePWith true false rounds f

end LeanQbe.T
