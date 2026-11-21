module

public import LeanQbe.T.OptUtil

/-!
# Linear Plan-Guided PHOAS Join-Group Simplification (`Func.simplifyGroupPlan`)

Replaces `SimplifyGroup`'s bottom-up `O(3^d)` PHOAS re-traversal with a two-phase `O(N)` pass:

1. **Phase 1 (untrusted `TFlat` bottom-up oracle, `SgpImpl.buildPlan`)**: reifies `f` once via
   `reifyFunc`, computes exact post-simplification jump counts (`JumpMap`, small-to-large `Trie Nat`
   merge), AST node counts (`exprSizeJ`-identical), and tail-jump targets bottom-up in a single
   linear pass, emitting a structural `SimpPlan` tree with per-`.group` actions:
   - `GroupAct.unwrap`: dead-group elimination (`0` reachable blocks);
   - `GroupAct.splice idx`: non-recursive single-block tail-jump or bounded single-use (`≤ 16`
     nodes, `count == 1`) block splicing;
   - `GroupAct.filter keep`: dead-block elimination / label rebinding.
2. **Phase 2 (verified single-pass PHOAS validator + rewriter)**:
   - `validatePlan`: single `O(N)` pass at `(UnitV, BoolL)` verifying plan structure and proving no
     reachable `.jump` targets a dropped (`.dead`) label;
   - `rewriteExpr`: single-pass PHOAS rewriter using `PlanL V L rs` (`.keep` / `.dead` / `.splice`),
     with zero `substLabels`, `spliceBlock`, `OptV`, or `OuterWf` re-traversals.

Correctness (`LeanQbe/T/SimplifyGroupPlanLemmas.lean`): `Func.simplifyGroupWithPlan_wf`,
`Func.simplifyGroupWithPlan_spec`, `Func.simplifyGroupPlan_wf`, `Func.simplifyGroupPlan_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace SgpImpl

/-! ## Structured simplification plan tree (`SimpPlan`) -/

/-- Planned transformation for a single `.group` node. -/
inductive GroupAct : Type
  | unwrap
  | splice (idx : Nat)
  | filter (keep : List Bool)
  deriving DecidableEq, Repr

mutual
/-- Structural simplification plan tree mirroring an `Expr`. -/
inductive SimpPlan : Type
  | leaf
  | node1 (k : SimpPlan)
  | node2 (t e : SimpPlan)
  | group (act : GroupAct) (bs : SimpPlanB) (k : SimpPlan)
  deriving DecidableEq, Repr

/-- Structural simplification plan list mirroring `Blocks`. -/
inductive SimpPlanB : Type
  | nil
  | cons (b : SimpPlan) (bs : SimpPlanB)
  deriving DecidableEq, Repr
end

/-! ## Phase 1: Untrusted `O(N)` bottom-up `TFlat` planner -/

/-- Label-level jump-count map with small-to-large merge via `Trie Nat`. -/
structure JumpMap where
  trie : Trie Nat
  keys : List Nat
  card : Nat

def JumpMap.empty : JumpMap := ⟨.empty, [], 0⟩

def JumpMap.singleton (lvl : Nat) : JumpMap :=
  ⟨Trie.empty.insert lvl 1, [lvl], 1⟩

def JumpMap.get (m : JumpMap) (lvl : Nat) : Nat :=
  m.trie.getD lvl 0

def JumpMap.add (m : JumpMap) (lvl cnt : Nat) : JumpMap :=
  if cnt == 0 then m
  else match m.trie.find? lvl with
  | none => ⟨m.trie.insert lvl cnt, lvl :: m.keys, m.card + 1⟩
  | some cur => ⟨m.trie.insert lvl (cur + cnt), m.keys, m.card⟩

/-- Erase all label levels in `[lo, lo + len)` from `m`. -/
def JumpMap.eraseRange (m : JumpMap) (lo len : Nat) : JumpMap :=
  if m.card == 0 || len == 0 then m
  else match m.keys with
  | [k] => if lo ≤ k && k < lo + len then .empty else m
  | _ =>
    let rec go (t : Trie Nat) (cur : Nat) : Nat → Trie Nat
      | 0 => t
      | rem + 1 =>
        let t' := if (t.find? cur).isSome then t.erase cur else t
        go t' (cur + 1) rem
    ⟨go m.trie lo len, m.keys, m.card⟩

/-- Small-to-large additive merge of two `JumpMap`s. -/
def JumpMap.merge (a b : JumpMap) : JumpMap :=
  if a.card == 0 then b
  else if b.card == 0 then a
  else
    let (small, big) := if a.card ≤ b.card then (a, b) else (b, a)
    small.keys.foldl (fun acc k =>
      match small.trie.find? k with
      | some c => acc.add k c
      | none => acc) big

/-- Collect local label levels in `[lo, lo + len)` with nonzero jump count in `m`. -/
def collectLocal (lo len : Nat) (m : JumpMap) : List Nat :=
  let rec go (cur : Nat) : Nat → List Nat → List Nat
    | 0, acc => acc
    | rem + 1, acc =>
      let acc' := if m.get cur > 0 then cur :: acc else acc
      go (cur + 1) rem acc'
  go lo len []

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

/-- Fixpoint reachability loop over local block IDs in `[nl, nl + sig.length)`. -/
def reachLoop (adj : List (Nat × List Nat)) : Nat → List Nat → List Nat
  | 0, reach => reach
  | fuel + 1, reach =>
    let (reach', changed) := reachStep adj reach
    if changed then reachLoop adj fuel reach' else reach

/-- Exact post-simplification bottom-up summary of a `TFlat` subtree. -/
structure PlanInfo where
  jumps : JumpMap
  size : Nat
  tailJump : Option (Nat × List Ty)
  changed : Bool

/-- Build `(blockId, localSuccs)` adjacency list from precomputed block summaries. -/
def buildAdj (lo len : Nat) : Nat → List (List Ty × PlanInfo) → List (Nat × List Nat)
  | _, [] => []
  | id, (_, bi) :: rest => (id, collectLocal lo len bi.jumps) :: buildAdj lo len (id + 1) rest

/-- Build the boolean keep mask and kept block indices in positional order `0 .. len - 1`. -/
def buildKeepInfo (nl : Nat) (reach : List Nat) :
    Nat → List (List Ty × PlanInfo) → List Bool × List Nat
  | _, [] => ([], [])
  | idx, _ :: rest =>
    let (mask, idxs) := buildKeepInfo nl reach (idx + 1) rest
    if reach.contains (nl + idx) then (true :: mask, idx :: idxs)
    else (false :: mask, idxs)

/-- Merge `jumps`, sum `size`, and OR `changed` across all kept blocks. -/
def mergeKeptBlocks (nl len : Nat) :
    List Bool → List (List Ty × PlanInfo) → JumpMap → Nat → Bool → JumpMap × Nat × Bool
  | true :: ks, (_, bi) :: rest, jAcc, sAcc, cAcc =>
    mergeKeptBlocks nl len ks rest
      (jAcc.merge (bi.jumps.eraseRange nl len)) (sAcc + bi.size) (cAcc || bi.changed)
  | false :: ks, _ :: rest, jAcc, sAcc, _ =>
    mergeKeptBlocks nl len ks rest jAcc sAcc true
  | _, _, jAcc, sAcc, cAcc => (jAcc, sAcc, cAcc)

/-- Look up the `idx`-th `(ts, PlanInfo)` entry from a block summary list. -/
def getBlockInfo? : Nat → List (List Ty × PlanInfo) → Option (List Ty × PlanInfo)
  | _, [] => none
  | 0, x :: _ => some x
  | n + 1, _ :: rest => getBlockInfo? n rest

/-- Decide the `GroupAct` and post-simplification `PlanInfo` for a `.group` node. -/
def decideGroup (nl : Nat) (sig : List (List Ty))
    (pbs : SimpPlanB) (bis : List (List Ty × PlanInfo))
    (pk : SimpPlan) (ik : PlanInfo) : SimpPlan × PlanInfo :=
  match sig, bis with
  | [], [] =>
    (.group .unwrap pbs pk, ⟨ik.jumps, ik.size, ik.tailJump, true⟩)
  | [ts], [(_, ib)] =>
    let kc := ik.jumps.get nl
    if kc == 0 then
      (.group .unwrap pbs pk, ⟨ik.jumps.eraseRange nl 1, ik.size, ik.tailJump, true⟩)
    else
      let selfRec := ib.jumps.get nl != 0
      let isTail := match ik.tailJump with
        | some (id, ts') => id == nl && Ty.listBeq ts' ts
        | none => false
      let jumps := (ik.jumps.eraseRange nl 1).merge (ib.jumps.eraseRange nl 1)
      if !selfRec && (isTail || (ib.size ≤ 16 && kc == 1)) then
        let tj := if isTail then ib.tailJump else none
        (.group (.splice 0) pbs pk, ⟨jumps, ik.size - 1 + ib.size, tj, true⟩)
      else
        (.group (.filter [true]) pbs pk,
          ⟨jumps, 1 + ib.size + ik.size, none, ib.changed || ik.changed⟩)
  | _, _ =>
    let len := sig.length
    let init := collectLocal nl len ik.jumps
    let adj := buildAdj nl len nl bis
    let reach := reachLoop adj (len + 1) init
    let (keep, keptIdxs) := buildKeepInfo nl reach 0 bis
    match keptIdxs with
    | [] =>
      (.group .unwrap pbs pk, ⟨ik.jumps.eraseRange nl len, ik.size, ik.tailJump, true⟩)
    | [idx] =>
      match getBlockInfo? idx bis with
      | some (ts, ib) =>
        let jId := nl + idx
        let kc := ik.jumps.get jId
        let selfRec := ib.jumps.get jId != 0
        let isTail := match ik.tailJump with
          | some (id, ts') => id == jId && Ty.listBeq ts' ts
          | none => false
        let jumps := (ik.jumps.eraseRange nl len).merge (ib.jumps.eraseRange nl len)
        if !selfRec && (isTail || (ib.size ≤ 16 && kc == 1)) then
          let tj := if isTail then ib.tailJump else none
          (.group (.splice idx) pbs pk, ⟨jumps, ik.size - 1 + ib.size, tj, true⟩)
        else
          let anyDrop := keep.any (!·)
          (.group (.filter keep) pbs pk,
            ⟨jumps, 1 + ib.size + ik.size, none, anyDrop || ib.changed || ik.changed⟩)
      | none =>
        let (jumps, sumSz, ch) :=
          mergeKeptBlocks nl len keep bis (ik.jumps.eraseRange nl len) 0 ik.changed
        (.group (.filter keep) pbs pk, ⟨jumps, 1 + sumSz + ik.size, none, ch⟩)
    | _ =>
      let (jumps, sumSz, ch) :=
        mergeKeptBlocks nl len keep bis (ik.jumps.eraseRange nl len) 0 ik.changed
      (.group (.filter keep) pbs pk, ⟨jumps, 1 + sumSz + ik.size, none, ch⟩)

mutual
/-- Single-pass bottom-up planner over `TFlat rs` tracking enclosing label depth `nl`. -/
def buildPlan {rs : List Ty} (nl : Nat) : TFlat rs → SimpPlan × PlanInfo
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    let (pk, ik) := buildPlan nl k
    (.node1 pk, ⟨ik.jumps, 1 + ik.size, none, ik.changed⟩)
  | .jnz _ t e =>
    let (pt, it) := buildPlan nl t
    let (pe, ie) := buildPlan nl e
    (.node2 pt pe,
      ⟨it.jumps.merge ie.jumps, 1 + it.size + ie.size, none, it.changed || ie.changed⟩)
  | .jump (ts := ts) j _ =>
    if j < nl then
      let lvl := nl - 1 - j
      (.leaf, ⟨JumpMap.singleton lvl, 1, some (lvl, ts), false⟩)
    else
      (.leaf, ⟨.empty, 1, none, false⟩)
  | .ret _ | .exit _ _ | .hlt =>
    (.leaf, ⟨.empty, 1, none, false⟩)
  | .group (sig := sig) bodies k =>
    let nl' := nl + sig.length
    let (pbs, bis) := buildPlanB nl' bodies
    let (pk, ik) := buildPlan nl' k
    decideGroup nl sig pbs bis pk ik

/-- Block-list companion of `buildPlan`. -/
def buildPlanB {rs : List Ty} (nl : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → SimpPlanB × List (List Ty × PlanInfo)
  | _, .nil => (.nil, [])
  | _, .cons (ts := ts) b bs =>
    let (pb, ib) := buildPlan nl b
    let (pbs, bis) := buildPlanB nl bs
    (.cons pb pbs, (ts, ib) :: bis)
end

/-! ## Phase 2: Verified `O(N)` plan validator & single-pass PHOAS rewriter -/

/-- Unit variable representation used by `validatePlan`. -/
abbrev UnitV : Ty → Type := fun _ => Unit

/-- Boolean label-liveness representation used by `validatePlan` (`true` = live, `false` = dead). -/
abbrev BoolL : List Ty → Type := fun _ => Bool

/-- Single-pass PHOAS label representation for `rewriteExpr`. -/
inductive PlanL (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) : List Ty → Type
  | keep {ts : List Ty} (l : L ts) : PlanL V L rs ts
  | dead {ts : List Ty} : PlanL V L rs ts
  | splice {ts : List Ty} (body : Tup (Arg V) ts → Expr V L rs) : PlanL V L rs ts

/-- Tuple of `false` (dead) boolean labels matching `sig`. -/
def allFalse : (sig : List (List Ty)) → Tup BoolL sig
  | [] => ()
  | _ :: sig => (false, allFalse sig)

/-- Tuple with `true` at position `idx` and `false` elsewhere. -/
def oneTrue : Nat → (sig : List (List Ty)) → Tup BoolL sig
  | _, [] => ()
  | 0, _ :: sig => (true, allFalse sig)
  | idx + 1, _ :: sig => (false, oneTrue idx sig)

/-- Convert a boolean mask into a `Tup BoolL sig` (padding short masks with `false`). -/
def boolTup : List Bool → (sig : List (List Ty)) → Tup BoolL sig
  | _, [] => ()
  | [], _ :: sig => (false, allFalse sig)
  | k :: ks, _ :: sig => (k, boolTup ks sig)

/-- Tuple of `.dead` labels matching `sig`. -/
def deadTup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (sig : List (List Ty)) → Tup (PlanL V L rs) sig
  | [] => ()
  | _ :: sig => (.dead, deadTup sig)

/-- Filter a group signature `sig` by boolean mask `ks`. -/
def filterSig (ks : List Bool) (sig : List (List Ty)) : List (List Ty) :=
  match sig with
  | [] => []
  | ts :: sig' =>
    match ks with
    | true :: ks' => ts :: filterSig ks' sig'
    | false :: ks' => filterSig ks' sig'
    | [] => []
termination_by structural sig

/-- Expand kept output labels `Tup L (filterSig ks sig)` to `Tup (PlanL V L rs) sig`. -/
def expandKeepLabels {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (ks : List Bool) → (sig : List (List Ty)) → Tup L (filterSig ks sig) →
    Tup (PlanL V L rs) sig
  | _, [], () => ()
  | [], _ :: sig, () => (.dead, deadTup sig)
  | true :: ks, _ :: sig, (j, js) => (.keep j, expandKeepLabels ks sig js)
  | false :: ks, _ :: sig, js => (.dead, expandKeepLabels ks sig js)

mutual
/-- Single-pass `O(N)` validator checking plan structure and verifying no reachable `.jump`
targets a dropped (`.dead`) label. -/
def validatePlan {rs : List Ty} (plan : SimpPlan) : Expr UnitV BoolL rs → Bool
  | .let_ (ts := ts) _ k =>
    match plan with | .node1 pk => validatePlan pk (k (Tup.units ts)) | _ => false
  | .load _ _ k =>
    match plan with | .node1 pk => validatePlan pk (k ()) | _ => false
  | .store _ _ k =>
    match plan with | .node1 pk => validatePlan pk k | _ => false
  | .call _ (bs := bs) _ k =>
    match plan with | .node1 pk => validatePlan pk (k (Tup.units bs)) | _ => false
  | .jnz _ t e =>
    match plan with | .node2 pt pe => validatePlan pt t && validatePlan pe e | _ => false
  | .jump ok _ =>
    match plan with | .leaf => ok | _ => false
  | .ret _ | .exit _ _ | .hlt =>
    match plan with | .leaf => true | _ => false
  | .group (sig := sig) bodies k =>
    match plan with
    | .group .unwrap _ pk => validatePlan pk (k (allFalse sig))
    | .group (.splice idx) pbs pk =>
      validateSpliceBlock idx pbs (bodies (allFalse sig)) &&
      validatePlan pk (k (oneTrue idx sig))
    | .group (.filter keep) pbs pk =>
      let ls := boolTup keep sig
      validateFilteredBlocks keep pbs (bodies ls) &&
      validatePlan pk (k ls)
    | _ => false

/-- Validate the single spliced block at index `idx` (under all-dead local labels). -/
def validateSpliceBlock {rs : List Ty} (idx : Nat) (pbs : SimpPlanB) :
    {sig : List (List Ty)} → Blocks UnitV BoolL rs sig → Bool
  | [], .nil => false
  | ts :: _, .cons b bs =>
    match idx, pbs with
    | 0, .cons pb _ => validatePlan pb (b (Tup.units ts))
    | idx' + 1, .cons _ pbs' => validateSpliceBlock idx' pbs' bs
    | _, .nil => false

/-- Validate every kept block in a `.filter keep` group and check mask/plan/signature lengths. -/
def validateFilteredBlocks {rs : List Ty} (ks : List Bool) (pbs : SimpPlanB) :
    {sig : List (List Ty)} → Blocks UnitV BoolL rs sig → Bool
  | [], .nil =>
    match ks, pbs with | [], .nil => true | _, _ => false
  | ts :: _, .cons b bs =>
    match ks, pbs with
    | true :: ks', .cons pb pbs' =>
      validatePlan pb (b (Tup.units ts)) && validateFilteredBlocks ks' pbs' bs
    | false :: ks', .cons _ pbs' =>
      validateFilteredBlocks ks' pbs' bs
    | _, _ => false
end

mutual
/-- Single-pass verified PHOAS rewriter guided by `SimpPlan`. -/
def rewriteExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (plan : SimpPlan) :
    Expr (Arg V) (PlanL V L rs) rs → Expr V L rs
  | .let_ op k =>
    match plan with
    | .node1 pk => .let_ (flattenOp op) fun xs => rewriteExpr pk (k (toArgTup xs))
    | _ => .hlt
  | .load t a k =>
    match plan with
    | .node1 pk => .load t (flattenArg a) fun v => rewriteExpr pk (k (.var v))
    | _ => .hlt
  | .store v a k =>
    match plan with
    | .node1 pk => .store (flattenArg v) (flattenArg a) (rewriteExpr pk k)
    | _ => .hlt
  | .call f args k =>
    match plan with
    | .node1 pk => .call f (flattenArgs args) fun xs => rewriteExpr pk (k (toArgTup xs))
    | _ => .hlt
  | .jnz c t e =>
    match plan with
    | .node2 pt pe => .jnz (flattenArg c) (rewriteExpr pt t) (rewriteExpr pe e)
    | _ => .hlt
  | .jump j args =>
    match plan with
    | .leaf =>
      match j with
      | .keep l => .jump l (flattenArgs args)
      | .dead => .hlt
      | .splice body => body (flattenArgs args)
    | _ => .hlt
  | .ret vs =>
    match plan with | .leaf => .ret (flattenArgs vs) | _ => .hlt
  | .exit f args =>
    match plan with | .leaf => .exit f (flattenArgs args) | _ => .hlt
  | .hlt =>
    match plan with | .leaf => .hlt | _ => .hlt
  | .group (sig := sig) bodies k =>
    match plan with
    | .group .unwrap _ pk => rewriteExpr pk (k (deadTup sig))
    | .group (.splice idx) pbs pk =>
      let ls := rewriteSpliceLabels idx pbs (bodies (deadTup sig))
      rewriteExpr pk (k ls)
    | .group (.filter keep) pbs pk =>
      .group (sig := filterSig keep sig)
        (fun Js => rewriteFilteredBlocks keep pbs (bodies (expandKeepLabels keep sig Js)))
        (fun Js => rewriteExpr pk (k (expandKeepLabels keep sig Js)))
    | _ => .hlt

/-- Build the `Tup (PlanL V L rs) sig` assigning `.splice` to block `idx` and `.dead` elsewhere. -/
def rewriteSpliceLabels {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (idx : Nat) (pbs : SimpPlanB) :
    {sig : List (List Ty)} → Blocks (Arg V) (PlanL V L rs) rs sig → Tup (PlanL V L rs) sig
  | [], .nil => ()
  | _ :: sig, .cons b bs =>
    match idx, pbs with
    | 0, .cons pb _ => (.splice fun args => rewriteExpr pb (b args), deadTup sig)
    | idx' + 1, .cons _ pbs' => (.dead, rewriteSpliceLabels idx' pbs' bs)
    | _, .nil => (.dead, deadTup sig)

/-- Rewrite only blocks marked `true` in `ks`, building `Blocks V L rs (filterSig ks sig)`. -/
def rewriteFilteredBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (ks : List Bool) (pbs : SimpPlanB) :
    {sig : List (List Ty)} → Blocks (Arg V) (PlanL V L rs) rs sig →
    Blocks V L rs (filterSig ks sig)
  | [], .nil => .nil
  | _ :: _, .cons b bs =>
    match ks, pbs with
    | true :: ks', .cons pb pbs' =>
      .cons (fun xs => rewriteExpr pb (b (toArgTup xs))) (rewriteFilteredBlocks ks' pbs' bs)
    | false :: ks', .cons _ pbs' =>
      rewriteFilteredBlocks ks' pbs' bs
    | true :: ks', .nil =>
      .cons (fun _ => .hlt) (rewriteFilteredBlocks ks' .nil bs)
    | false :: ks', .nil =>
      rewriteFilteredBlocks ks' .nil bs
    | [], _ => .nil
end

end SgpImpl

open SgpImpl

/-- Apply a precomputed `SimpPlan` to a closed `Func` if it passes linear `validatePlan`. -/
def Func.simplifyGroupWithPlan {as rs : List Ty} (plan : SimpPlan) (f : Func as rs) : Func as rs :=
  if validatePlan plan (f UnitV BoolL (Tup.units as)) then
    fun V L xs => rewriteExpr plan (f (Arg V) (PlanL V L rs) (toArgTup xs))
  else
    f

/-- Linear `O(N)` plan-guided join-group simplification on a closed `Func`. -/
def Func.simplifyGroupPlan {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let tf := reifyFunc f
  let (plan, info) := buildPlan 0 tf
  if info.changed then
    Func.simplifyGroupWithPlan plan (denoteFunc tf)
  else
    denoteFunc tf

/-- Named-function wrapper for `Func.simplifyGroupPlan`, preserving metadata. -/
def Fn.simplifyGroupPlan (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.simplifyGroupPlan fn.body⟩

end LeanQbe.T
