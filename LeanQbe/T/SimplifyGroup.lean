module

public import LeanQbe.T.OptUtil

/-!
# PHOAS Join-Group Simplification & Elimination (`O-M2`)

Pure 100%-PHOAS bottom-up `.group` simplification pass (`simplifyGroup` / `Func.simplifyGroup`)
using local label tagging `JLabel L ts` (no `reify`/`TFlat`):

* Instantiates `L` as `JLabel L` (`outer` / `loc id` / `probe`) and threads `depth : Nat` down
  through `.group` binders so label identity checks are exact and decidable.
* Simplifies block bodies and group continuations bottom-up, then computes local block
  reachability (`reachLoop`) starting from local jumps in the simplified continuation `k'`:
  - **Dead-group unwrap**: when zero local blocks are reachable (`sig' = []`, including
    `countJumps id k' == 0` for single-block groups), drops the `.group` and returns `k'`.
  - **Dead-block elimination**: drops unreachable blocks from multi-block `.group`s, narrowing
    `sig` to reachable blocks `sig'`.
  - **Single-use non-recursive join-block splicing**: when one reachable block `b` remains
    (`sig' = [ts]`), `!hasJumpTo jId b`, and either `k'` is a tail jump `.jump J args` or
    `exprSizeJ b ≤ 16 && countJumps jId k' == 1`, replaces `.jump J args` inside `k'` with `b args`.
  - **Otherwise**: rebinds kept labels via `substLabels`.

Correctness (`LeanQbe/T/SimplifyGroupLemmas.lean`): `simplifyGroup_wp`, `simplifyGroup_wf`,
`Func.simplifyGroup_wf`, `Func.simplifyGroup_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace SgImpl

/-! ## Local PHOAS label tagging and operand flattening helpers -/

/-- Label representation for `SimplifyGroup`: `outer` preserves enclosing labels, `loc id` tags
local `.group` binders, and `probe` is used only when inspecting nested `.group`s. -/
inductive JLabel (L : List Ty → Type) : List Ty → Type
  | outer {ts : List Ty} : L ts → JLabel L ts
  | loc {ts : List Ty} (id : Nat) : JLabel L ts
  | probe {ts : List Ty} : JLabel L ts

def locLabels {L : List Ty → Type} : (sig : List (List Ty)) → Nat → Tup (JLabel L) sig
  | [], _ => ()
  | _ :: sig, d => (.loc d, locLabels sig (d + 1))

def probeLabels {L : List Ty → Type} : (sig : List (List Ty)) → Tup (JLabel L) sig
  | [] => ()
  | _ :: sig => (.probe, probeLabels sig)

/-- Block list parameterized over `Tup (Arg V) ts` so spliced blocks accept jump operands
directly (both variables and immediates) without extra `copy` bindings. -/
inductive SBlocks (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) : List (List Ty) → Type
  | nil : SBlocks V L rs []
  | cons {ts : List Ty} {sig : List (List Ty)}
      (b : Tup (Arg V) ts → Expr V L rs) (bs : SBlocks V L rs sig) : SBlocks V L rs (ts :: sig)

def sblocksToBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → SBlocks V L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons (fun xs => b (toArgTup xs)) (sblocksToBlocks bs)

/-! ## Jump counting, IR size measurement, and reachability analysis -/

/-- True iff `e` is directly `.jump (.loc targetId) args` with matching signature `targetTs`. -/
def isJumpTo (targetId : Nat) (targetTs : List Ty)
    {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (OptV V) (JLabel L) rs → Bool
  | .jump (ts := ts) (.loc id) _ => id == targetId && Ty.listBeq ts targetTs
  | _ => false

mutual
/-- Count static occurrences of `.jump (.loc targetId) _` inside `e`. -/
def countJumps (targetId : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (OptV V) (JLabel L) rs → Nat
  | .let_ (ts := ts) _ k => countJumps targetId (k (noneTup ts))
  | .load _ _ k => countJumps targetId (k none)
  | .store _ _ k => countJumps targetId k
  | .call _ (bs := bs) _ k => countJumps targetId (k (noneTup bs))
  | .jnz _ t e => countJumps targetId t + countJumps targetId e
  | .jump (.loc id) _ => if id == targetId then 1 else 0
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := sig) bodies k =>
    countJumpsB targetId (bodies (probeLabels sig)) + countJumps targetId (k (probeLabels sig))

def countJumpsB (targetId : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (OptV V) (JLabel L) rs sig → Nat
  | _, .nil => 0
  | _, .cons (ts := ts) b bs => countJumps targetId (b (noneTup ts)) + countJumpsB targetId bs
end

/-- True iff `e` contains at least one jump to `.loc targetId`. -/
def hasJumpTo (targetId : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (e : Expr (OptV V) (JLabel L) rs) : Bool :=
  countJumps targetId e != 0

mutual
/-- Node-count size metric on `Expr (OptV V) (JLabel L) rs`, matching `Inline.exprSize`. -/
def exprSizeJ {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (OptV V) (JLabel L) rs → Nat
  | .let_ (ts := ts) _ k => 1 + exprSizeJ (k (noneTup ts))
  | .load _ _ k => 1 + exprSizeJ (k none)
  | .store _ _ k => 1 + exprSizeJ k
  | .call _ (bs := bs) _ k => 1 + exprSizeJ (k (noneTup bs))
  | .jnz _ t e => 1 + exprSizeJ t + exprSizeJ e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 1
  | .group (sig := sig) bodies k =>
    1 + blocksSizeJ (bodies (probeLabels sig)) + exprSizeJ (k (probeLabels sig))

def blocksSizeJ {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (OptV V) (JLabel L) rs sig → Nat
  | _, .nil => 0
  | _, .cons (ts := ts) b bs => exprSizeJ (b (noneTup ts)) + blocksSizeJ bs
end

def insertUnique (x : Nat) (xs : List Nat) : List Nat :=
  if xs.contains x then xs else x :: xs

mutual
/-- Collect deduplicated local label IDs in `[lo, hi)` jumped to anywhere in `e`. -/
def collectJumps (lo hi : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (OptV V) (JLabel L) rs → List Nat → List Nat
  | .let_ (ts := ts) _ k, acc => collectJumps lo hi (k (noneTup ts)) acc
  | .load _ _ k, acc => collectJumps lo hi (k none) acc
  | .store _ _ k, acc => collectJumps lo hi k acc
  | .call _ (bs := bs) _ k, acc => collectJumps lo hi (k (noneTup bs)) acc
  | .jnz _ t e, acc => collectJumps lo hi e (collectJumps lo hi t acc)
  | .jump (.loc id) _, acc => if lo ≤ id && id < hi then insertUnique id acc else acc
  | .jump _ _, acc | .ret _, acc | .exit _ _, acc | .hlt, acc => acc
  | .group (sig := sig) bodies k, acc =>
    collectJumps lo hi (k (probeLabels sig)) (collectJumpsB lo hi (bodies (probeLabels sig)) acc)

def collectJumpsB (lo hi : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (OptV V) (JLabel L) rs sig → List Nat → List Nat
  | _, .nil, acc => acc
  | _, .cons (ts := ts) b bs, acc =>
    collectJumpsB lo hi bs (collectJumps lo hi (b (noneTup ts)) acc)
end

/-- Build adjacency list `(blockId, jumpTargets)` for blocks in `[lo, hi)`. -/
def blockAdj (lo hi : Nat) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Nat → {sig : List (List Ty)} → SBlocks (OptV V) (JLabel L) rs sig →
    List (Nat × List Nat)
  | _, _, .nil => []
  | id, ts :: _, .cons b bs =>
    (id, collectJumps lo hi (b (dummyArgOptTup ts)) []) :: blockAdj lo hi (id + 1) bs

def unionChanged : List Nat → List Nat → List Nat × Bool
  | acc, [] => (acc, false)
  | acc, x :: xs =>
    if acc.contains x then unionChanged acc xs
    else
      let (acc', _) := unionChanged (x :: acc) xs
      (acc', true)

def reachStep (adj : List (Nat × List Nat)) (reach : List Nat) : List Nat × Bool :=
  adj.foldl (fun (acc, ch) (id, succs) =>
    if reach.contains id then
      let (acc', ch') := unionChanged acc succs
      (acc', ch || ch')
    else (acc, ch)) (reach, false)

/-- Fixed-point reachability loop over `[lo, hi)` (`fuel = sig.length + 1` always reaches
fixpoint because every non-terminating step strictly increases `reach.length ≤ sig.length`). -/
def reachLoop (adj : List (Nat × List Nat)) : Nat → List Nat → List Nat
  | 0, reach => reach
  | fuel + 1, reach =>
    let (reach', changed) := reachStep adj reach
    if changed then reachLoop adj fuel reach' else reach

/-! ## Dead-block filtering, label rebinding, splicing, and final untagging -/

structure FilterRes (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) where
  sig : List (List Ty)
  ids : List Nat
  blocks : SBlocks V (JLabel L) rs sig
  mkEnv : Tup (JLabel L) sig → List (Nat × ((ts : List Ty) × JLabel L ts))

def filterSBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (keep : Nat → Bool) :
    (sig : List (List Ty)) → SBlocks V (JLabel L) rs sig → Nat → FilterRes V L rs
  | [], .nil, _ => ⟨[], [], .nil, fun _ => []⟩
  | ts :: sig, .cons b bs, id =>
    match filterSBlocks keep sig bs (id + 1) with
    | ⟨sig', ids', bs', mkEnv⟩ =>
      if keep id then
        ⟨ts :: sig', id :: ids', .cons b bs', fun (j, js) => (id, ⟨ts, j⟩) :: mkEnv js⟩
      else ⟨sig', ids', bs', mkEnv⟩

def lookupLblEnv {L : List Ty → Type} :
    List (Nat × ((ts : List Ty) × JLabel L ts)) → (id : Nat) → (ts : List Ty) →
    Option (JLabel L ts)
  | [], _, _ => none
  | (id', ⟨ts', j⟩) :: rest, id, ts =>
    if id == id' then
      match listTyDecEq ts' ts with
      | isTrue h => some (h ▸ j)
      | isFalse _ => lookupLblEnv rest id ts
    else lookupLblEnv rest id ts

mutual
/-- Replace local label IDs in `env` with their rebound `JLabel L` binders. -/
def substLabels {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (env : List (Nat × ((ts : List Ty) × JLabel L ts))) :
    Expr V (JLabel L) rs → Expr V (JLabel L) rs
  | .let_ op k => .let_ op fun xs => substLabels env (k xs)
  | .load t a k => .load t a fun v => substLabels env (k v)
  | .store v a k => .store v a (substLabels env k)
  | .call f args k => .call f args fun xs => substLabels env (k xs)
  | .jnz c t e => .jnz c (substLabels env t) (substLabels env e)
  | .jump (ts := ts) (.loc id) args =>
    match lookupLblEnv env id ts with
    | some j' => .jump j' args
    | none => .jump (.loc id) args
  | .jump j args => .jump j args
  | .ret vs => .ret vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => substLabelsB env (bodies Js)) (fun Js => substLabels env (k Js))

def substLabelsB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (env : List (Nat × ((ts : List Ty) × JLabel L ts))) :
    {sig : List (List Ty)} → Blocks V (JLabel L) rs sig → Blocks V (JLabel L) rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons (fun xs => substLabels env (b xs)) (substLabelsB env bs)
end

mutual
/-- Splice non-recursive join block `b` at every `.jump (.loc targetId) args` in `e`. -/
def spliceBlock {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (targetId : Nat) (targetTs : List Ty) (b : Tup (Arg V) targetTs → Expr V (JLabel L) rs) :
    Expr V (JLabel L) rs → Expr V (JLabel L) rs
  | .let_ op k => .let_ op fun xs => spliceBlock targetId targetTs b (k xs)
  | .load t a k => .load t a fun v => spliceBlock targetId targetTs b (k v)
  | .store v a k => .store v a (spliceBlock targetId targetTs b k)
  | .call f args k => .call f args fun xs => spliceBlock targetId targetTs b (k xs)
  | .jnz c t e =>
    .jnz c (spliceBlock targetId targetTs b t) (spliceBlock targetId targetTs b e)
  | .jump (ts := ts) (.loc id) args =>
    if id == targetId then
      match listTyDecEq ts targetTs with
      | isTrue h => b (h ▸ args)
      | isFalse _ => .jump (.loc id) args
    else .jump (.loc id) args
  | .jump j args => .jump j args
  | .ret vs => .ret vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => spliceBlockB targetId targetTs b (bodies Js))
      (fun Js => spliceBlock targetId targetTs b (k Js))

def spliceBlockB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (targetId : Nat) (targetTs : List Ty) (b : Tup (Arg V) targetTs → Expr V (JLabel L) rs) :
    {sig : List (List Ty)} → Blocks V (JLabel L) rs sig → Blocks V (JLabel L) rs sig
  | _, .nil => .nil
  | _, .cons b' bs =>
    .cons (fun xs => spliceBlock targetId targetTs b (b' xs))
      (spliceBlockB targetId targetTs b bs)
end

/-- Simplify a `.group` node from its already-simplified blocks `bs'` and continuation `k'`. -/
def handleGroup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (depth : Nat) {sig : List (List Ty)}
    (bs' : SBlocks (OptV V) (JLabel L) rs sig)
    (k' : Expr (OptV V) (JLabel L) rs) : Expr (OptV V) (JLabel L) rs :=
  let hi := depth + sig.length
  let init := collectJumps depth hi k' []
  let adj := blockAdj depth hi depth bs'
  let reach := reachLoop adj (sig.length + 1) init
  let f := filterSBlocks (fun id => reach.contains id) sig bs' depth
  match f with
  | ⟨[], _, .nil, _⟩ => k'
  | ⟨[ts], [jId], .cons b .nil, mkEnv⟩ =>
    let bDummy := b (dummyArgOptTup ts)
    if !hasJumpTo jId bDummy &&
       (isJumpTo jId ts k' || (exprSizeJ bDummy <= 16 && countJumps jId k' == 1)) then
      spliceBlock jId ts b k'
    else
      .group (sig := [ts])
        (fun Js => substLabelsB (mkEnv Js) (sblocksToBlocks (.cons b .nil)))
        (fun Js => substLabels (mkEnv Js) k')
  | ⟨sig', _, bs'', mkEnv⟩ =>
    .group (sig := sig')
      (fun Js => substLabelsB (mkEnv Js) (sblocksToBlocks bs''))
      (fun Js => substLabels (mkEnv Js) k')

mutual
/-- Final linear pass unwrapping `OptV V` and `JLabel L` back to `V` and `L`. -/
def untagExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (OptV V) (JLabel L) rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    .let_ ⟨op.code, argsSweep op.args⟩ fun xs => untagExpr (k (someTup ts xs))
  | .load t a k =>
    .load t (argSweep a) fun v => untagExpr (k (some v))
  | .store v a k =>
    .store (argSweep v) (argSweep a) (untagExpr k)
  | .call f (bs := bs) args k =>
    .call f (argsSweep args) fun xs => untagExpr (k (someTup bs xs))
  | .jnz c t e =>
    .jnz (argSweep c) (untagExpr t) (untagExpr e)
  | .jump (.outer l) args => .jump l (argsSweep args)
  | .jump _ _ => .hlt
  | .ret vs => .ret (argsSweep vs)
  | .exit f args => .exit f (argsSweep args)
  | .hlt => .hlt
  | .group bodies k =>
    .group
      (fun Js => untagBlocks (bodies (Js.map fun _ l => .outer l)))
      (fun Js => untagExpr (k (Js.map fun _ l => .outer l)))

def untagBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (OptV V) (JLabel L) rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => untagExpr (b (someTup ts xs))) (untagBlocks bs)
end

end SgImpl

open SgImpl

mutual
/-- Bottom-up structural join-group simplification over `Expr (Arg (OptV V)) (JLabel L) rs`. -/
def simplifyGroup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (depth : Nat) : Expr (Arg (OptV V)) (JLabel L) rs → Expr (OptV V) (JLabel L) rs
  | .let_ op k =>
    .let_ (flattenOp op) fun xs => simplifyGroup depth (k (toArgTup xs))
  | .load t a k =>
    .load t (flattenArg a) fun v => simplifyGroup depth (k (.var v))
  | .store v a k =>
    .store (flattenArg v) (flattenArg a) (simplifyGroup depth k)
  | .call f args k =>
    .call f (flattenArgs args) fun xs => simplifyGroup depth (k (toArgTup xs))
  | .jnz c t e =>
    .jnz (flattenArg c) (simplifyGroup depth t) (simplifyGroup depth e)
  | .jump j args => .jump j (flattenArgs args)
  | .ret vs => .ret (flattenArgs vs)
  | .exit f args => .exit f (flattenArgs args)
  | .hlt => .hlt
  | .group (sig := sig) bodies k =>
    let locLs := locLabels sig depth
    let depth' := depth + sig.length
    handleGroup depth (simplifyGroupB depth' (bodies locLs)) (simplifyGroup depth' (k locLs))

/-- Block-list companion of `simplifyGroup`. -/
def simplifyGroupB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (depth : Nat) : {sig : List (List Ty)} →
    Blocks (Arg (OptV V)) (JLabel L) rs sig → SBlocks (OptV V) (JLabel L) rs sig
  | _, .nil => .nil
  | _, .cons b bs =>
    .cons (fun xs => simplifyGroup depth (b xs)) (simplifyGroupB depth bs)
end

/-- Simplify and eliminate dead or non-recursive single-use join `.group`s on a closed `Func`. -/
def Func.simplifyGroup {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs =>
    untagExpr
      (_root_.LeanQbe.T.simplifyGroup 0
        (f (Arg (OptV V)) (JLabel L) (toArgTup (someTup as xs))))

end LeanQbe.T
