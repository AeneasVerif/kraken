module

public import LeanQbe.T.OptUtil

/-!
# Tail Duplication of Small Join/Trampoline Blocks (`LeanQbe.T.TailDup`)

Two-phase `O(N)` verified typed-IR tail-duplication pass (`Func.tailDup`, `G2-P3.1c`):

1. **Phase 1 (`TailDup.buildPlan`, untrusted `O(N)` `TFlat` planner)**:
   Scans `reifyFunc f` bottom-up tracking exact incoming jump counts (`JumpMap`) and straight-line
   instruction lengths (`tailInstrs?`), identifying unreachable blocks (`.drop`) and tiny join/tail
   blocks (`.dup`: `≤ maxInstrs` instructions terminating in `.jump` / `.ret` / `.exit` / `.hlt`
   with `1 .. maxPreds` predecessors, non-self-recursive, and acyclic with respect to other `.dup`
   blocks in the same `.group`).
2. **Phase 2 (`TailDup.validatePlan` + `TailDup.rewriteExpr`, verified PHOAS pass)**:
   Single `O(N)` validator at `(UnitV, BoolL)` checking structural alignment, ensuring `.dup`
   blocks never target `.dup`/`.drop` blocks and reachable `.keep`/`k` code never targets `.drop`
   blocks, followed by a single-pass PHOAS rewriter (`DupL V L rs`) that duplicates `.dup` blocks
   directly into their callers and unwraps `.group`s whose blocks are all duplicated/dropped.
3. **`Func.tailDup` / `Fn.tailDup`**:
   Runs bounded fixpoint iterations (`cfg.maxIters`, stopping early when `!plan.hasChanges`),
   handling chains of tiny trampolines and nested `.group` unwrapping cleanly.

Correctness (`LeanQbe/T/TailDupLemmas.lean`): `Func.tailDup_wf`, `Func.tailDup_spec`,
`tailDup_wp`, `Func.tailDup_callsOk`, `Fn.tailDup_wf`, `Fn.tailDup_spec`, `Fn.tailDup_callsOk`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace TailDup

/-! ## Configuration and Structural Plan (`TailDupConfig`, `DupAct`, `DupPlan`) -/

/-- Configuration knobs for tiny join-block tail duplication (`Func.tailDup`). -/
structure TailDupConfig where
  /-- Maximum non-terminator instructions in a duplicated block. -/
  maxInstrs : Nat := 2
  /-- Maximum incoming jump count (`1 .. maxPreds`) for a duplicated block. -/
  maxPreds : Nat := 2
  /-- Allow duplicating tiny blocks terminating in `.ret`. -/
  allowRet : Bool := true
  /-- Allow duplicating tiny blocks terminating in `.exit` or `.hlt`. -/
  allowExit : Bool := true
  /-- Allow `.load` / `.store` among the instructions of a duplicated block. -/
  allowMem : Bool := true
  /-- Allow `.call` among the instructions of a duplicated block. -/
  allowCall : Bool := false
  /-- Drop unreachable blocks (`0` incoming jumps). -/
  dropDead : Bool := true
  /-- Maximum tail-duplication iterations (`tailDupOnce`). -/
  maxIters : Nat := 3
  deriving Repr, DecidableEq

/-- Default tail-duplication configuration (`≤ 2` instrs, `≤ 2` preds, `.jmp`/`.ret`). -/
def defaultConfig : TailDupConfig := {}

/-- Per-block action inside a `.group` node. -/
inductive DupAct : Type
  | keep
  | dup
  | drop
  deriving DecidableEq, Repr

mutual
/-- Structural tail-duplication plan tree mirroring an `Expr` / `TFlat`. -/
inductive DupPlan : Type
  | leaf
  | node1 (k : DupPlan)
  | node2 (t e : DupPlan)
  | group (acts : List DupAct) (bs : DupPlanB) (k : DupPlan)
  deriving DecidableEq, Repr

/-- Block-list companion of `DupPlan`. -/
inductive DupPlanB : Type
  | nil
  | cons (b : DupPlan) (bs : DupPlanB)
  deriving DecidableEq, Repr
end

mutual
/-- True iff `plan` drops or duplicates at least one block. -/
def DupPlan.hasChanges : DupPlan → Bool
  | .leaf => false
  | .node1 k => k.hasChanges
  | .node2 t e => t.hasChanges || e.hasChanges
  | .group acts bs k =>
    acts.any (fun | .keep => false | _ => true) || bs.hasChanges || k.hasChanges

/-- Block-list companion of `DupPlan.hasChanges`. -/
def DupPlanB.hasChanges : DupPlanB → Bool
  | .nil => false
  | .cons b bs => b.hasChanges || bs.hasChanges
end

/-! ## Phase 1: Untrusted `O(N)` Bottom-Up `TFlat` Planner -/

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
  else
    let rec go (t : Trie Nat) (cur : Nat) : Nat → Trie Nat
      | 0 => t
      | rem + 1 =>
        let t' := if (t.find? cur).isSome then t.erase cur else t
        go t' (cur + 1) rem
    let keys' := m.keys.filter fun k => !(lo ≤ k && k < lo + len)
    if keys'.isEmpty then .empty
    else ⟨go m.trie lo len, keys', keys'.length⟩

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

/-- Add `factor` copies of `src` into `dst`. -/
def JumpMap.addScaled (dst src : JumpMap) (factor : Nat) : JumpMap :=
  if factor == 0 || src.card == 0 then dst
  else if factor == 1 && dst.card == 0 then src
  else src.keys.foldl (fun acc k =>
    match src.trie.find? k with
    | some c => acc.add k (c * factor)
    | none => acc) dst

/-- Collect local label levels in `[lo, lo + len)` with nonzero jump count in `m`. -/
def collectLocal (lo len : Nat) (m : JumpMap) : List Nat :=
  let rec go (cur : Nat) : Nat → List Nat → List Nat
    | 0, acc => acc
    | rem + 1, acc =>
      let acc' := if m.get cur > 0 then cur :: acc else acc
      go (cur + 1) rem acc'
  go lo len []

/-- Post-simplification bottom-up summary of a `TFlat` subtree. -/
structure PlanInfo where
  jumps : JumpMap
  tailInstrs? : Option Nat
  changed : Bool

/-- Build `(blockId, localSuccs)` adjacency list from precomputed block summaries. -/
def buildAdj (lo len : Nat) : Nat → List PlanInfo → List (Nat × List Nat)
  | _, [] => []
  | id, bi :: rest => (id, collectLocal lo len bi.jumps) :: buildAdj lo len (id + 1) rest

/-- Accumulate jump counts from all reachable blocks plus entry `ik`. -/
def mergeReachJumps (nl : Nat) (dropDead : Bool) (reach : List Nat) :
    Nat → List PlanInfo → JumpMap → JumpMap
  | _, [], acc => acc
  | idx, bi :: rest, acc =>
    let isReach := !dropDead || reach.contains (nl + idx)
    let acc' := if isReach then acc.merge bi.jumps else acc
    mergeReachJumps nl dropDead reach (idx + 1) rest acc'

/-- Check if block `bi` at `lvl` is an eligible tiny non-self-recursive tail-dup candidate. -/
def isDupCandidate (cfg : TailDupConfig) (lvl : Nat) (totalJumps : JumpMap)
    (bi : PlanInfo) : Bool :=
  let preds := totalJumps.get lvl
  1 ≤ preds && preds ≤ cfg.maxPreds &&
    bi.jumps.get lvl == 0 &&
    match bi.tailInstrs? with
    | some n => n ≤ cfg.maxInstrs
    | none => false

/-- Variant of `chooseActs` allowing cycle breaking when `defer` would stall a
2-block mutual cycle: only defer to `t > lvl` when `t` does not jump back to `lvl`. -/
def hasAcyclicHigherEligible (cfg : TailDupConfig) (nl lvl : Nat) (totalJumps : JumpMap)
    (reach : List Nat) (bis : List PlanInfo) (localSuccs : List Nat) : Bool :=
  let rec checkIdx (idx : Nat) : List PlanInfo → Bool
    | [] => false
    | b :: bs =>
      let t := nl + idx
      if t > lvl && localSuccs.contains t && (!cfg.dropDead || reach.contains t) &&
          isDupCandidate cfg t totalJumps b && b.jumps.get lvl == 0 then true
      else checkIdx (idx + 1) bs
  checkIdx 0 bis

/-- Select `DupAct` for each block in a `.group`, guaranteeing no `.dup` block targets `.dup` or
`.drop` in the same `.group`. -/
def chooseActs (cfg : TailDupConfig) (nl len : Nat) (reach : List Nat)
    (totalJumps : JumpMap) (allBis : List PlanInfo) :
    Nat → List PlanInfo → List Nat → List Nat → List DupAct
  | _, [], _, _ => []
  | idx, bi :: rest, dupSet, dupTargets =>
    let lvl := nl + idx
    if cfg.dropDead && !reach.contains lvl then
      .drop :: chooseActs cfg nl len reach totalJumps allBis (idx + 1) rest dupSet dupTargets
    else
      let localSuccs := collectLocal nl len bi.jumps
      let cand := isDupCandidate cfg lvl totalJumps bi
      let conflict := dupTargets.contains lvl || localSuccs.any (fun t => dupSet.contains t)
      let defer := hasAcyclicHigherEligible cfg nl lvl totalJumps reach allBis localSuccs
      if cand && !conflict && !defer then
        .dup :: chooseActs cfg nl len reach totalJumps allBis (idx + 1) rest
          (lvl :: dupSet) (localSuccs ++ dupTargets)
      else
        .keep :: chooseActs cfg nl len reach totalJumps allBis (idx + 1) rest dupSet dupTargets

/-- Merge outer jumps and `changed` flag across `acts` and `bis`, scaling `.dup` blocks' outer
jumps by their incoming predecessor count `totalJumps.get (nl + idx)`. -/
def mergeGroupInfo (nl len : Nat) (totalJumps : JumpMap) :
    Nat → List DupAct → List PlanInfo → JumpMap → Bool → JumpMap × Bool
  | _, [], _, jAcc, cAcc => (jAcc, cAcc)
  | _, _, [], jAcc, cAcc => (jAcc, cAcc)
  | idx, .keep :: acts, bi :: bis, jAcc, cAcc =>
    mergeGroupInfo nl len totalJumps (idx + 1) acts bis
      (jAcc.merge (bi.jumps.eraseRange nl len)) (cAcc || bi.changed)
  | idx, .dup :: acts, bi :: bis, jAcc, _ =>
    let preds := totalJumps.get (nl + idx)
    mergeGroupInfo nl len totalJumps (idx + 1) acts bis
      (jAcc.addScaled (bi.jumps.eraseRange nl len) preds) true
  | idx, .drop :: acts, _ :: bis, jAcc, _ =>
    mergeGroupInfo nl len totalJumps (idx + 1) acts bis jAcc true

/-- Decide the `.group` plan and post-duplication `PlanInfo`. -/
def decideGroup (cfg : TailDupConfig) (nl : Nat) (sig : List (List Ty))
    (pbs : DupPlanB) (bis : List PlanInfo) (pk : DupPlan) (ik : PlanInfo) :
    DupPlan × PlanInfo :=
  let len := sig.length
  if len == 0 then
    (.group [] pbs pk, ⟨ik.jumps, ik.tailInstrs?, true⟩)
  else
    let init := collectLocal nl len ik.jumps
    let adj := buildAdj nl len nl bis
    let reach :=
      if cfg.dropDead then reachFixpoint forwardReachStep adj (len + 1) init else []
    let totalJumps := mergeReachJumps nl cfg.dropDead reach 0 bis ik.jumps
    let acts := chooseActs cfg nl len reach totalJumps bis 0 bis [] []
    let (jumps, changed) :=
      mergeGroupInfo nl len totalJumps 0 acts bis (ik.jumps.eraseRange nl len) ik.changed
    (.group acts pbs pk, ⟨jumps, none, changed⟩)

mutual
/-- Single-pass bottom-up planner over `TFlat rs` tracking enclosing label depth `nl`. -/
def buildPlan (cfg : TailDupConfig) {rs : List Ty} (nl : Nat) : TFlat rs → DupPlan × PlanInfo
  | .let_ _ k =>
    let (pk, ik) := buildPlan cfg nl k
    (.node1 pk, ⟨ik.jumps, ik.tailInstrs?.map (· + 1), ik.changed⟩)
  | .load _ _ k | .store _ _ k =>
    let (pk, ik) := buildPlan cfg nl k
    let ti := if cfg.allowMem then ik.tailInstrs?.map (· + 1) else none
    (.node1 pk, ⟨ik.jumps, ti, ik.changed⟩)
  | .call _ _ _ k =>
    let (pk, ik) := buildPlan cfg nl k
    let ti := if cfg.allowCall then ik.tailInstrs?.map (· + 1) else none
    (.node1 pk, ⟨ik.jumps, ti, ik.changed⟩)
  | .jnz _ t e =>
    let (pt, it) := buildPlan cfg nl t
    let (pe, ie) := buildPlan cfg nl e
    (.node2 pt pe, ⟨it.jumps.merge ie.jumps, none, it.changed || ie.changed⟩)
  | .jump j _ =>
    if j < nl then
      (.leaf, ⟨JumpMap.singleton (nl - 1 - j), some 0, false⟩)
    else
      (.leaf, ⟨.empty, some 0, false⟩)
  | .ret _ =>
    (.leaf, ⟨.empty, if cfg.allowRet then some 0 else none, false⟩)
  | .exit _ _ | .hlt =>
    (.leaf, ⟨.empty, if cfg.allowExit then some 0 else none, false⟩)
  | .group (sig := sig) bodies k =>
    let nl' := nl + sig.length
    let (pbs, bis) := buildPlanB cfg nl' bodies
    let (pk, ik) := buildPlan cfg nl' k
    decideGroup cfg nl sig pbs bis pk ik

/-- Block-list companion of `buildPlan`. -/
def buildPlanB (cfg : TailDupConfig) {rs : List Ty} (nl : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → DupPlanB × List PlanInfo
  | _, .nil => (.nil, [])
  | _, .cons b bs =>
    let (pb, ib) := buildPlan cfg nl b
    let (pbs, bis) := buildPlanB cfg nl bs
    (.cons pb pbs, ib :: bis)
end

/-! ## Phase 2: Verified `O(N)` Plan Validator & Single-Pass PHOAS Rewriter -/

/-- Unit variable representation used by `validatePlan`. -/
abbrev UnitV : Ty → Type := fun _ => Unit

/-- Boolean label-liveness representation used by `validatePlan` (`true` = live, `false` = dead). -/
abbrev BoolL : List Ty → Type := fun _ => Bool

/-- Single-pass PHOAS label representation for `rewriteExpr`. -/
inductive DupL (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) : List Ty → Type
  | keep {ts : List Ty} (l : L ts) : DupL V L rs ts
  | dead {ts : List Ty} : DupL V L rs ts
  | dup {ts : List Ty} (body : Tup (Arg V) ts → Expr V L rs) : DupL V L rs ts

/-- Filter a group signature `sig` keeping only blocks with `DupAct.keep`. -/
def filterActsSig (acts : List DupAct) (sig : List (List Ty)) : List (List Ty) :=
  match sig with
  | [] => []
  | ts :: sig' =>
    match acts with
    | .keep :: acts' => ts :: filterActsSig acts' sig'
    | .dup :: acts' | .drop :: acts' => filterActsSig acts' sig'
    | [] => []
termination_by structural sig

/-- Tuple of `false` (dead) boolean labels matching `sig`. -/
def allFalse : (sig : List (List Ty)) → Tup BoolL sig
  | [] => ()
  | _ :: sig => (false, allFalse sig)

/-- Label-liveness tuple for validating `.dup` blocks (`true` iff `.keep`). -/
def noDupBoolTup : List DupAct → (sig : List (List Ty)) → Tup BoolL sig
  | _, [] => ()
  | [], _ :: sig => (false, allFalse sig)
  | .keep :: acts, _ :: sig => (true, noDupBoolTup acts sig)
  | .dup :: acts, _ :: sig | .drop :: acts, _ :: sig => (false, noDupBoolTup acts sig)

/-- Label-liveness tuple for validating `.keep` blocks and entry `k` (`true` iff `.keep` or
`.dup`). -/
def dupBoolTup : List DupAct → (sig : List (List Ty)) → Tup BoolL sig
  | _, [] => ()
  | [], _ :: sig => (false, allFalse sig)
  | .keep :: acts, _ :: sig | .dup :: acts, _ :: sig => (true, dupBoolTup acts sig)
  | .drop :: acts, _ :: sig => (false, dupBoolTup acts sig)

/-- Tuple of `.dead` labels matching `sig`. -/
def deadTup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (sig : List (List Ty)) → Tup (DupL V L rs) sig
  | [] => ()
  | _ :: sig => (.dead, deadTup sig)

/-- Expand kept output labels `Tup L (filterActsSig acts sig)` into `Tup (DupL V L rs) sig`
(marking `.dup` and `.drop` slots as `.dead`). -/
def expandKeepLabels {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List DupAct) → (sig : List (List Ty)) → Tup L (filterActsSig acts sig) →
    Tup (DupL V L rs) sig
  | _, [], () => ()
  | [], _ :: sig, () => (.dead, deadTup sig)
  | .keep :: acts, _ :: sig, (j, js) => (.keep j, expandKeepLabels acts sig js)
  | .dup :: acts, _ :: sig, js | .drop :: acts, _ :: sig, js =>
    (.dead, expandKeepLabels acts sig js)

mutual
/-- Single-pass `O(N)` validator checking plan structure and verifying no reachable `.jump`
targets a dropped (`.dead`) label. -/
def validatePlan {rs : List Ty} (plan : DupPlan) : Expr UnitV BoolL rs → Bool
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
    | .group acts pbs pk =>
      let lsNo := noDupBoolTup acts sig
      let lsYes := dupBoolTup acts sig
      validateDupBlocks acts pbs (bodies lsNo) &&
      validateKeptBlocks acts pbs (bodies lsYes) &&
      validatePlan pk (k lsYes)
    | _ => false

/-- Validate every `.dup` block under `lsNo` (verifying exact `acts`/`pbs`/`sig` lengths). -/
def validateDupBlocks {rs : List Ty} (acts : List DupAct) (pbs : DupPlanB) :
    {sig : List (List Ty)} → Blocks UnitV BoolL rs sig → Bool
  | [], .nil =>
    match acts, pbs with | [], .nil => true | _, _ => false
  | ts :: _, .cons b bs =>
    match acts, pbs with
    | .dup :: acts', .cons pb pbs' =>
      validatePlan pb (b (Tup.units ts)) && validateDupBlocks acts' pbs' bs
    | .keep :: acts', .cons _ pbs' | .drop :: acts', .cons _ pbs' =>
      validateDupBlocks acts' pbs' bs
    | _, _ => false

/-- Validate every `.keep` block under `lsYes`. -/
def validateKeptBlocks {rs : List Ty} (acts : List DupAct) (pbs : DupPlanB) :
    {sig : List (List Ty)} → Blocks UnitV BoolL rs sig → Bool
  | [], .nil =>
    match acts, pbs with | [], .nil => true | _, _ => false
  | ts :: _, .cons b bs =>
    match acts, pbs with
    | .keep :: acts', .cons pb pbs' =>
      validatePlan pb (b (Tup.units ts)) && validateKeptBlocks acts' pbs' bs
    | .dup :: acts', .cons _ pbs' | .drop :: acts', .cons _ pbs' =>
      validateKeptBlocks acts' pbs' bs
    | _, _ => false
end

mutual
/-- Single-pass verified PHOAS rewriter guided by `DupPlan`. -/
def rewriteExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (plan : DupPlan) :
    Expr (Arg V) (DupL V L rs) rs → Expr V L rs
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
      | .dup body => body (flattenArgs args)
    | _ => .hlt
  | .ret vs =>
    match plan with | .leaf => .ret (flattenArgs vs) | _ => .hlt
  | .exit f args =>
    match plan with | .leaf => .exit f (flattenArgs args) | _ => .hlt
  | .hlt =>
    match plan with | .leaf => .hlt | _ => .hlt
  | .group (sig := sig) bodies k =>
    match plan with
    | .group acts pbs pk =>
      if acts.any (· == .keep) then
        .group (sig := filterActsSig acts sig)
          (fun Js =>
            let lsNo := expandKeepLabels acts sig Js
            let lsDup := buildDupLabels acts pbs (bodies lsNo) lsNo
            rewriteKeptBlocks acts pbs (bodies lsDup))
          (fun Js =>
            let lsNo := expandKeepLabels acts sig Js
            let lsDup := buildDupLabels acts pbs (bodies lsNo) lsNo
            rewriteExpr pk (k lsDup))
      else
        let lsNo := deadTup sig
        let lsDup := buildDupLabels acts pbs (bodies lsNo) lsNo
        rewriteExpr pk (k lsDup)
    | _ => .hlt

/-- Build `Tup (DupL V L rs) sig` replacing `.dup` positions with `.dup` closures over `lsNo`. -/
def buildDupLabels {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (acts : List DupAct) (pbs : DupPlanB) :
    {sig : List (List Ty)} → Blocks (Arg V) (DupL V L rs) rs sig →
    Tup (DupL V L rs) sig → Tup (DupL V L rs) sig
  | [], .nil, () => ()
  | _ :: sig, .cons b bs, (l, ls) =>
    match acts, pbs with
    | .dup :: acts', .cons pb pbs' =>
      (.dup (fun args => rewriteExpr pb (b args)), buildDupLabels acts' pbs' bs ls)
    | .keep :: acts', .cons _ pbs' =>
      (l, buildDupLabels acts' pbs' bs ls)
    | .drop :: acts', .cons _ pbs' =>
      (.dead, buildDupLabels acts' pbs' bs ls)
    | _, _ => (.dead, deadTup sig)

/-- Emit only blocks marked `.keep` in `acts`, building `Blocks V L rs (filterActsSig acts sig)`. -/
def rewriteKeptBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (acts : List DupAct) (pbs : DupPlanB) :
    {sig : List (List Ty)} → Blocks (Arg V) (DupL V L rs) rs sig →
    Blocks V L rs (filterActsSig acts sig)
  | [], .nil => .nil
  | _ :: _, .cons b bs =>
    match acts, pbs with
    | .keep :: acts', .cons pb pbs' =>
      .cons (fun xs => rewriteExpr pb (b (toArgTup xs))) (rewriteKeptBlocks acts' pbs' bs)
    | .dup :: acts', .cons _ pbs' | .drop :: acts', .cons _ pbs' =>
      rewriteKeptBlocks acts' pbs' bs
    | .keep :: acts', .nil =>
      .cons (fun _ => .hlt) (rewriteKeptBlocks acts' .nil bs)
    | .dup :: acts', .nil | .drop :: acts', .nil =>
      rewriteKeptBlocks acts' .nil bs
    | [], _ => .nil
end

end TailDup

open TailDup

/-- Apply a precomputed `DupPlan` to a closed `Func` if it passes linear `validatePlan`. -/
def Func.tailDupWithPlan {as rs : List Ty} (plan : DupPlan) (f : Func as rs) : Func as rs :=
  if validatePlan plan (f UnitV BoolL (Tup.units as)) then
    fun V L xs => rewriteExpr plan (f (Arg V) (DupL V L rs) (toArgTup xs))
  else
    f

/-- Single `O(N)` pass of tiny join/tail block duplication on a closed `Func`. -/
def Func.tailDupOnce {as rs : List Ty} (f : Func as rs) (cfg : TailDupConfig := {}) :
    Func as rs × Bool :=
  let tf := reifyFunc f
  let (plan, info) := buildPlan cfg 0 tf
  if info.changed then
    (Func.tailDupWithPlan plan (denoteFunc tf), true)
  else
    (denoteFunc tf, false)

/-- Bounded-iteration tail-duplication loop on a closed `Func`, exiting early at fixpoint. -/
def Func.tailDupLoop {as rs : List Ty} (cfg : TailDupConfig) : Nat → Func as rs → Func as rs
  | 0, f => f
  | fuel + 1, f =>
    let (f', ch) := Func.tailDupOnce f cfg
    if ch then Func.tailDupLoop cfg fuel f' else f'

/-- Verified tiny join/tail block duplication (`Func.tailDup`): duplicates tiny `≤ 2`-instruction
blocks terminating in `.jump`/`.ret` with `≤ 2` predecessors directly into their callers. -/
def Func.tailDup {as rs : List Ty} (f : Func as rs) (cfg : TailDupConfig := {}) : Func as rs :=
  Func.tailDupLoop cfg cfg.maxIters f

/-- Named-function wrapper for `Func.tailDup`, preserving metadata. -/
def Fn.tailDup (fn : Fn) (cfg : TailDupConfig := {}) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.tailDup fn.body cfg⟩

end LeanQbe.T
