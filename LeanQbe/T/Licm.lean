module

public import LeanQbe.T.OptUtil
public import LeanQbe.T.Gvn

/-!
# Loop-Invariant Code Motion (`Func.licm`)

Two-phase PHOAS loop-invariant code motion pass following the `TFlat` guess-and-check pattern:

1. **Untrusted `TFlat` analyzer (`buildHoistPlan`):**
   - Reifies `f` once via `reifyFunc f : TFlat rs` (`O(N)`, avoiding PHOAS closure re-traversal).
   - Identifies single-block and multi-block `.group` loops via local label cycle detection
     (`computeLoopMask`) and computes backedge-reachability (`buildReach` / `extReachMask`) so
     loop-exit-only cold branches (e.g. error/conflict exits) are not speculatively hoisted into
     loop-live registers.
   - Scans looping blocks top-down (`scanTFlat` / `scanLoopBlocks`) to extract transitively
     loop-invariant pure total `.let_` bindings (`OpCode.isLicmPure`) at the outermost loop
     `.group` to which they are invariant, deduplicating identical hoisted expressions via
     `PlanTbl` (`GvnTbl (fun _ => Unit)`).
2. **Verified PHOAS rewriter (`emitHoists`, `licmSweep`, `licmSweepB`):**
   - Locally validates `h.code.isLicmPure`, table non-duplication, and lexical availability of
     all operands in `env : VEnv V` (`Trie ((t : Ty) × V t)`) before emitting each hoisted
     `.let_` directly before `.group` (binding hoisted values lexically across `bodies` and `k`
     with zero block-parameter plumbing).
   - Replaces matching in-loop `.let_` nodes via `GvnTbl V` lookups.
   - Zero-overhead fast path: returns `f` unchanged when `plan.hasHoists = false`.

Correctness (`LeanQbe/T/LicmLemmas.lean`): `OpCode.isLicmPure_spec`, `licmSweep_wf`,
`licmSweep_wp`, `Func.licm_wf`, `Func.licm_spec`, `Func.licm_supportsSource`, `Fn.licm_wf`,
`Fn.licm_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Pure total deterministic opcode predicate -/

/-- True iff `code` is pure, total (never UB), and deterministic (no floating-point NaN
nondeterminism, no partial division/remainder UB, and no `mkpair`/`unpair` legality bridges), so
hoisting it before a `.group` is unconditionally sound in `wp` and preserves `supportsSource`. -/
def OpCode.isLicmPure : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .copy t => !t.hasFloat
  | _, _, .add t | _, _, .sub t | _, _, .mul t | _, _, .neg t => !t.hasFloat
  | _, _, .and t | _, _, .or t | _, _, .xor t | _, _, .not t | _, _, .ternlog t _ => !t.hasFloat
  | _, _, .shl t | _, _, .lshr t | _, _, .ashr t | _, _, .rotl t | _, _, .rotr t => !t.hasFloat
  | _, _, .fshl _ | _, _, .fshr _ => true
  | _, _, .bswap t => t.bswapOk
  | _, _, .clz _ | _, _, .cls _ | _, _, .rbit _ | _, _, .ctz _ | _, _, .popcnt _ => true
  | _, _, .cmp _ t _ _ => !t.hasFloat
  | _, _, .select t => !t.hasFloat
  | _, _, .blend t _ _ => !t.hasFloat
  | _, _, .zext m n => Nat.ble m n
  | _, _, .sext m n => Nat.ble m n
  | _, _, .trunc m n => Nat.ble n m
  | _, _, .ofBool _ => true
  | _, _, .addc _ | _, _, .subb _ | _, _, .umulw _ | _, _, .smulw _ => true
  | _, _, .bitcast t u _ => !t.hasFloat && !u.hasFloat
  | _, _, .shufd t _ | _, _, .shufb t | _, _, .alignr t _ | _, _, .blendw t _ =>
    !t.hasFloat && t.size != 0 && t.size % 128 == 0
  | _, _, .sha256rnds2 | _, _, .sha256msg1 | _, _, .sha256msg2 => true
  | _, _, _ => false

/-! ## Hoist plan structures -/

/-- A single pure-total operation descriptor to hoist before a loop `.group`. Operands reference
lexical value-number levels (`Arg K`) already bound before `.group` or by earlier hoisted ops. -/
structure HoistOp : Type where
  sig : List Ty
  ts : List Ty
  code : OpCode sig ts
  args : Tup (Arg K) sig

mutual
/-- Structural hoist plan mirroring `Expr`, attaching `List HoistOp` to each `.group`. -/
inductive HoistPlan : Type
  | leaf : HoistPlan
  | node1 (k : HoistPlan) : HoistPlan
  | node2 (t e : HoistPlan) : HoistPlan
  | groupNode (hoists : List HoistOp) (bs : HoistBlocks) (k : HoistPlan) : HoistPlan

/-- Block-list companion of `HoistPlan`. -/
inductive HoistBlocks : Type
  | nil : HoistBlocks
  | cons (hd : HoistPlan) (tl : HoistBlocks) : HoistBlocks
end

mutual
/-- True iff any `.group` in the plan schedules at least one hoisted operation. -/
def HoistPlan.hasHoists : HoistPlan → Bool
  | .leaf => false
  | .node1 k => k.hasHoists
  | .node2 t e => t.hasHoists || e.hasHoists
  | .groupNode hs bs k => !hs.isEmpty || bs.hasHoists || k.hasHoists

/-- Block-list companion of `HoistPlan.hasHoists`. -/
def HoistBlocks.hasHoists : HoistBlocks → Bool
  | .nil => false
  | .cons h t => h.hasHoists || t.hasHoists
end

/-! ## Phase 1 (untrusted): `TFlat` loop detection, reachability, and hoist planning -/

namespace Licm

/-- Insert `x` into `xs` if not already present. -/
def addUnique (x : Nat) (xs : List Nat) : List Nat :=
  if xs.contains x then xs else x :: xs

mutual
/-- Collect deduplicated local jump targets in `[shift, shift + m)`, shifted back to `[0, m)`. -/
def collectLocalJumps (shift m : Nat) {rs : List Ty} : TFlat rs → List Nat → List Nat
  | .let_ _ k, acc | .load _ _ k, acc | .store _ _ k, acc | .call _ _ _ k, acc =>
    collectLocalJumps shift m k acc
  | .jnz _ t e, acc => collectLocalJumps shift m e (collectLocalJumps shift m t acc)
  | .jump j _, acc =>
    if shift ≤ j && j < shift + m then addUnique (j - shift) acc else acc
  | .ret _, acc | .exit _ _, acc | .hlt, acc => acc
  | .group (sig := sig) bodies k, acc =>
    let shift' := shift + sig.length
    collectLocalJumps shift' m k (collectLocalJumpsB shift' m bodies acc)

/-- Block-list companion of `collectLocalJumps`. -/
def collectLocalJumpsB (shift m : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → List Nat → List Nat
  | _, .nil, acc => acc
  | _, .cons b bs, acc => collectLocalJumpsB shift m bs (collectLocalJumps shift m b acc)
end

/-- Build local jump adjacency `(blockLabelIdx, succLabelIdxs)` for `TBlocks` of length `m`. -/
def buildBlockAdj (m : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → List (Nat × List Nat)
  | _, .nil => []
  | _ :: sig, .cons b bs => (sig.length, collectLocalJumps 0 m b []) :: buildBlockAdj m bs

/-- Return all local block label indices in `bodies` that lie on a cycle (self-loop or
multi-block cycle). Empty iff the `.group` is acyclic (not a loop). -/
def computeLoopMask {rs : List Ty} {sig : List (List Ty)} (bodies : TBlocks rs sig) : List Nat :=
  let m := sig.length
  let adj := buildBlockAdj m bodies
  adj.foldl (fun acc (lbl, succs) =>
    let reach := reachFixpoint forwardReachStep adj m succs
    if reach.contains lbl then lbl :: acc else acc) []

mutual
/-- True iff `tf` contains any `.jump` targeting a label in `mask` (shifted by `shift`). -/
def hasJumpInMask (mask : List Nat) (shift : Nat) {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => hasJumpInMask mask shift k
  | .jnz _ t e => hasJumpInMask mask shift t || hasJumpInMask mask shift e
  | .jump j _ => shift ≤ j && mask.contains (j - shift)
  | .ret _ | .exit _ _ | .hlt => false
  | .group (sig := sig) bodies k =>
    let shift' := shift + sig.length
    hasJumpInMaskB mask shift' bodies || hasJumpInMask mask shift' k

/-- Block-list companion of `hasJumpInMask`. -/
def hasJumpInMaskB (mask : List Nat) (shift : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => hasJumpInMask mask shift b || hasJumpInMaskB mask shift bs
end

/-- Collect local block label indices in `bodies` that directly jump to `outerMask`. -/
def directOuterReach (outerMask : List Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → List Nat
  | _, .nil => []
  | _ :: sig, .cons b bs =>
    let rest := directOuterReach outerMask bs
    if hasJumpInMask outerMask 0 b then sig.length :: rest else rest

/-- Compute local block label indices in `bodies` that can reach `outerMask` in `≥ 1` steps. -/
def extReachMask (outerMask : List Nat) {rs : List Ty} {sig : List (List Ty)}
    (bodies : TBlocks rs sig) : List Nat :=
  if outerMask.isEmpty then []
  else
    let init := directOuterReach outerMask bodies
    if init.isEmpty then []
    else reachFixpoint backReachStep (buildBlockAdj sig.length bodies) sig.length init

mutual
/-- Mirror tree annotating each subexpression with whether it can reach a loop backedge. -/
inductive ReachTree : Type
  | leaf (reaches : Bool)
  | node1 (reaches : Bool) (k : ReachTree)
  | node2 (reaches : Bool) (t e : ReachTree)
  | groupNode (reaches : Bool) (bs : ReachBlocks) (k : ReachTree)

/-- Block-list companion of `ReachTree`. -/
inductive ReachBlocks : Type
  | nil
  | cons (hd : ReachTree) (tl : ReachBlocks)
end

/-- Record outer variable indices (`idx ≥ depth`, normalized by `idx - depth`) in `s`. -/
def addOuterArg (depth : Nat) {t : Ty} : Arg K t → Trie Unit → Trie Unit
  | .var idx, s => if depth ≤ idx then s.insert (idx - depth) () else s
  | .imm _, s => s

/-- Tuple companion of `addOuterArg`. -/
def addOuterArgs (depth : Nat) : {ts : List Ty} → Tup (Arg K) ts → Trie Unit → Trie Unit
  | [], (), s => s
  | _ :: _, (a, as), s => addOuterArgs depth as (addOuterArg depth a s)

mutual
/-- Collect distinct outer variable indices referenced inside `tf` relative to binder `depth`. -/
def collectOuter (depth : Nat) {rs : List Ty} : TFlat rs → Trie Unit → Trie Unit
  | .let_ (ts := ts) op k, s => collectOuter (depth + ts.length) k (addOuterArgs depth op.args s)
  | .load _ a k, s => collectOuter (depth + 1) k (addOuterArg depth a s)
  | .store v a k, s => collectOuter depth k (addOuterArg depth v (addOuterArg depth a s))
  | .call _ (bs := bs) args k, s => collectOuter (depth + bs.length) k (addOuterArgs depth args s)
  | .jnz c t e, s => collectOuter depth e (collectOuter depth t (addOuterArg depth c s))
  | .jump _ args, s => addOuterArgs depth args s
  | .ret vs, s => addOuterArgs depth vs s
  | .exit _ args, s => addOuterArgs depth args s
  | .hlt, s => s
  | .group bodies k, s => collectOuter depth k (collectOuterB depth bodies s)

/-- Block-list companion of `collectOuter`. -/
def collectOuterB (depth : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Trie Unit → Trie Unit
  | _, .nil, s => s
  | ts :: _, .cons b bs, s => collectOuterB depth bs (collectOuter (depth + ts.length) b s)
end

/-- Count occupied entries in a `Trie Unit`. -/
def trieCard : Trie Unit → Nat
  | .empty => 0
  | .node v l r => trieCard l + (if v.isSome then 1 else 0) + trieCard r

/-- True for cheap ops (comparisons) that should not be hoisted out of cold branches (`jnzD ≥ 2`)
inside high-pressure loops (`> 8` outer live-in variables), since hoisting destroys flag fusion and
adds a live boolean spill slot. -/
def isColdSkipOp {as rs : List Ty} : OpCode as rs → Bool
  | .cmp _ _ _ _ => true
  | _ => false

mutual
/-- Compute bottom-up backedge-reachability tree for `tf` against target label mask `mask`,
suppressing `.let_` hoist flags on cold-branch comparisons (`jnzD ≥ 2`) when `highPress` holds. -/
def buildReachWith (highPress : Bool) (jnzD : Nat) (mask : List Nat) {rs : List Ty} :
    TFlat rs → Bool × ReachTree
  | .let_ op k =>
    let (rkReach, rk) := buildReachWith highPress jnzD mask k
    let skip := highPress && Nat.ble 2 jnzD && isColdSkipOp op.code
    (rkReach, .node1 (rkReach && !skip) rk)
  | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    let (rkReach, rk) := buildReachWith highPress jnzD mask k
    (rkReach, .node1 rkReach rk)
  | .jnz _ t e =>
    let (rtReach, rt) := buildReachWith highPress (jnzD + 1) mask t
    let (reReach, re) := buildReachWith highPress (jnzD + 1) mask e
    let r := rtReach || reReach
    (r, .node2 r rt re)
  | .jump j _ =>
    let r := mask.contains j
    (r, .leaf r)
  | .ret _ | .exit _ _ | .hlt => (false, .leaf false)
  | .group (sig := sig) bodies k =>
    let outerMask := mask.map (· + sig.length)
    let ext := extReachMask outerMask bodies
    let mask' := ext ++ outerMask
    let (rb, rbs) := buildReachWithB highPress jnzD mask' bodies
    let (rkReach, rk) := buildReachWith highPress jnzD mask' k
    let r := rb || rkReach
    (r, .groupNode r rbs rk)

/-- Block-list companion of `buildReachWith`. -/
def buildReachWithB (highPress : Bool) (jnzD : Nat) (mask : List Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool × ReachBlocks
  | _, .nil => (false, .nil)
  | _, .cons b bs =>
    let (rbReach, rb) := buildReachWith highPress jnzD mask b
    let (rbsReach, rt) := buildReachWithB highPress jnzD mask bs
    (rbReach || rbsReach, .cons rb rt)
end

/-- Enable the cold-branch pressure gate when `bodies` references `> 8` outer live-in vars. -/
def buildReachB (mask : List Nat) {rs : List Ty} {sig : List (List Ty)}
    (bodies : TBlocks rs sig) : Bool × ReachBlocks :=
  let highPress := Nat.blt 8 (trieCard (collectOuterB 0 bodies .empty))
  buildReachWithB highPress 0 mask bodies

/-- Erased `GvnTbl` used by the analyzer to track already-hoisted keys and their assigned levels. -/
abbrev PlanTbl := GvnTbl (fun _ => Unit)

/-- Extract the tuple of assigned `Nat` levels from a `PlanTbl` entry. -/
def planLevels : {ts : List Ty} → Tup (GVal (fun _ => Unit)) ts → Tup K ts
  | [], () => ()
  | _ :: _, (((), lvl), rest) => (lvl, planLevels rest)

/-- Allocate fresh `PlanTbl` value-number entries starting at `next`. -/
def freshPlanVals (ts : List Ty) (next : Nat) : Tup (GVal (fun _ => Unit)) ts :=
  freshGVals ts (Tup.units ts) next

/-- Push consecutive levels `next, ..., next + k - 1` onto `env` (newest first). -/
def pushLevels : Nat → Nat → List Nat → List Nat
  | 0, _, env => env
  | k + 1, next, env => pushLevels k (next + 1) (next :: env)

/-- Push a tuple of levels `Tup K ts` onto `env` (matching `pushTup`). -/
def pushTupK : {ts : List Ty} → Tup K ts → List Nat → List Nat
  | [], (), env => env
  | _ :: _, (l, ls), env => pushTupK ls (l :: env)

/-- Push `k` loop-variant `none` binders onto `senv`. -/
def pushNones : Nat → List (Option Nat) → List (Option Nat)
  | 0, senv => senv
  | k + 1, senv => pushNones k (none :: senv)

/-- Push a tuple of invariant `some` levels onto `senv` (matching `pushTup`). -/
def pushTupSome : {ts : List Ty} → Tup K ts → List (Option Nat) → List (Option Nat)
  | [], (), senv => senv
  | _ :: _, (l, ls), senv => pushTupSome ls (some l :: senv)

/-- Map a de Bruijn index operand in `TFlat` to its lexical `licmSweep` value number. -/
def mapIdxArg (env : List Nat) {t : Ty} : Arg K t → Arg K t
  | .var idx => .var ((listGet? env idx).getD 0)
  | .imm c => .imm c

/-- Tuple companion of `mapIdxArg`. -/
def mapIdxArgs (env : List Nat) : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => ()
  | _ :: _, (a, as) => (mapIdxArg env a, mapIdxArgs env as)

/-- Resolve a de Bruijn index operand to an invariant level (`some`) or fail on loop-variant
variables. -/
def scanIdxArg (senv : List (Option Nat)) {t : Ty} : Arg K t → Option (Arg K t)
  | .var idx =>
    match listGet? senv idx with
    | some (some lvl) => some (.var lvl)
    | _ => none
  | .imm c => some (.imm c)

/-- Tuple companion of `scanIdxArg`. -/
def scanIdxArgs (senv : List (Option Nat)) :
    {ts : List Ty} → Tup (Arg K) ts → Option (Tup (Arg K) ts)
  | [], () => some ()
  | _ :: _, (a, as) =>
    match scanIdxArg senv a, scanIdxArgs senv as with
    | some a', some as' => some (a', as')
    | _, _ => none

/-- State threaded while scanning a loop `.group` for hoistable invariant pure ops. -/
structure ScanState : Type where
  next : Nat
  tbl : PlanTbl
  hoistsRev : List HoistOp

mutual
/-- Scan a `TFlat` inside a loop body, collecting transitively loop-invariant pure total ops on
backedge-reaching paths into `st.hoistsRev` (in reverse topological order). -/
def scanTFlat {rs : List Ty} (senv : List (Option Nat)) (rt : ReachTree) :
    TFlat rs → ScanState → ScanState
  | .let_ (ts := ts) op k, st =>
    let (reaches, rk) := match rt with | .node1 r rk => (r, rk) | _ => (false, .leaf false)
    if op.code.isLicmPure then
      match scanIdxArgs senv op.args with
      | some kArgs =>
        match st.tbl.find op.sig ts op.code kArgs with
        | some cached =>
          scanTFlat (pushTupSome (planLevels cached) senv) rk k st
        | none =>
          if reaches then
            let h : HoistOp := ⟨op.sig, ts, op.code, kArgs⟩
            let pvs := freshPlanVals ts st.next
            let st' : ScanState :=
              ⟨st.next + ts.length, st.tbl.insert op.sig ts op.code kArgs pvs, h :: st.hoistsRev⟩
            scanTFlat (pushTupSome (Tup.levels ts st.next) senv) rk k st'
          else
            scanTFlat (pushNones ts.length senv) rk k st
      | none => scanTFlat (pushNones ts.length senv) rk k st
    else
      scanTFlat (pushNones ts.length senv) rk k st
  | .load _ _ k, st =>
    let rk := match rt with | .node1 _ rk => rk | _ => .leaf false
    scanTFlat (none :: senv) rk k st
  | .store _ _ k, st =>
    let rk := match rt with | .node1 _ rk => rk | _ => .leaf false
    scanTFlat senv rk k st
  | .call _ bs _ k, st =>
    let rk := match rt with | .node1 _ rk => rk | _ => .leaf false
    scanTFlat (pushNones bs.length senv) rk k st
  | .jnz _ t e, st =>
    let (rt1, rt2) := match rt with
      | .node2 _ rt1 rt2 => (rt1, rt2)
      | _ => (.leaf false, .leaf false)
    let st1 := scanTFlat senv rt1 t st
    scanTFlat senv rt2 e st1
  | .jump _ _, st | .ret _, st | .exit _ _, st | .hlt, st => st
  | .group bodies k, st =>
    let (rbs, rk) := match rt with
      | .groupNode _ rbs rk => (rbs, rk)
      | _ => (.nil, .leaf false)
    let st1 := scanTBlocksAll senv rbs bodies st
    scanTFlat senv rk k st1

/-- Scan every block of a nested `.group` inside an enclosing loop body. -/
def scanTBlocksAll {rs : List Ty} (senv : List (Option Nat)) :
    {sig : List (List Ty)} → ReachBlocks → TBlocks rs sig → ScanState → ScanState
  | _, _, .nil, st => st
  | ts :: _, rbs, .cons b bs, st =>
    let (rh, rt) := match rbs with | .cons rh rt => (rh, rt) | _ => (.leaf false, .nil)
    let st1 := scanTFlat (pushNones ts.length senv) rh b st
    scanTBlocksAll senv rt bs st1
end

/-- Scan only the looping blocks (`loopMask`) of the current loop `.group`. -/
def scanLoopBlocks (loopMask : List Nat) {rs : List Ty} (senv : List (Option Nat)) :
    {sig : List (List Ty)} → ReachBlocks → TBlocks rs sig → ScanState → ScanState
  | [], _, .nil, st => st
  | ts :: sig, rbs, .cons b bs, st =>
    let (rh, rt) := match rbs with | .cons rh rt => (rh, rt) | _ => (.leaf false, .nil)
    let st1 :=
      if loopMask.contains sig.length then
        scanTFlat (pushNones ts.length senv) rh b st
      else st
    scanLoopBlocks loopMask senv rt bs st1

mutual
/-- Top-down hoist planner over `TFlat rs`, mirroring `licmSweep`'s exact value numbering so
outer-loop hoists propagate cleanly into nested loops. -/
def analyzeTFlat {rs : List Ty} (next : Nat) (env : List Nat) (tbl : PlanTbl) :
    TFlat rs → HoistPlan
  | .let_ (ts := ts) op k =>
    let kArgs := mapIdxArgs env op.args
    match tbl.find op.sig ts op.code kArgs with
    | some cached =>
      .node1 (analyzeTFlat next (pushTupK (planLevels cached) env) tbl k)
    | none =>
      .node1 (analyzeTFlat (next + ts.length) (pushLevels ts.length next env) tbl k)
  | .load _ _ k => .node1 (analyzeTFlat (next + 1) (next :: env) tbl k)
  | .store _ _ k => .node1 (analyzeTFlat next env tbl k)
  | .call _ bs _ k =>
    .node1 (analyzeTFlat (next + bs.length) (pushLevels bs.length next env) tbl k)
  | .jnz _ t e => .node2 (analyzeTFlat next env tbl t) (analyzeTFlat next env tbl e)
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => .leaf
  | .group bodies k =>
    let loopMask := computeLoopMask bodies
    if loopMask.isEmpty then
      .groupNode [] (analyzeTBlocks next env tbl bodies) (analyzeTFlat next env tbl k)
    else
      let rbs := (buildReachB loopMask bodies).2
      let st := scanLoopBlocks loopMask (env.map some) rbs bodies ⟨next, tbl, []⟩
      let hoists := st.hoistsRev.reverse
      .groupNode hoists (analyzeTBlocks st.next env st.tbl bodies)
        (analyzeTFlat st.next env st.tbl k)

/-- Block-list companion of `analyzeTFlat`. -/
def analyzeTBlocks {rs : List Ty} (next : Nat) (env : List Nat) (tbl : PlanTbl) :
    {sig : List (List Ty)} → TBlocks rs sig → HoistBlocks
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (analyzeTFlat (next + ts.length) (pushLevels ts.length next env) tbl b)
      (analyzeTBlocks next env tbl bs)
end

/-- Compute the top-level `HoistPlan` for a reified function body with `nParams` parameters. -/
def buildHoistPlan {rs : List Ty} (nParams : Nat) (tf : TFlat rs) : HoistPlan :=
  analyzeTFlat nParams (pushLevels nParams 0 []) .empty tf

end Licm

/-! ## Phase 2 (verified): PHOAS lexical binder environment and checked rewriter -/

/-- Lexical environment mapping value-number levels `Nat` to bound PHOAS variables. -/
abbrev VEnv (V : Ty → Type) := Trie ((t : Ty) × V t)

/-- Insert a tuple of bound variables into `env` at consecutive levels starting at `next`. -/
def envInsertTup {V : Ty → Type} : {ts : List Ty} → VEnv V → Nat → Tup V ts → VEnv V
  | [], env, _, () => env
  | t :: _, env, next, (x, xs) => envInsertTup (env.insert next ⟨t, x⟩) (next + 1) xs

/-- Resolve a symbolic operand `Arg K t` against the lexical variable environment `env`. -/
def resolveArg {V : Ty → Type} (env : VEnv V) {t : Ty} : Arg K t → Option (Arg V t)
  | .var lvl =>
    match env.find? lvl with
    | some ⟨t', v⟩ =>
      match castTy t' t v with
      | some v' => some (.var v')
      | none => none
    | none => none
  | .imm c => some (.imm c)

/-- Tuple companion of `resolveArg`. -/
def resolveArgs {V : Ty → Type} (env : VEnv V) :
    {ts : List Ty} → Tup (Arg K) ts → Option (Tup (Arg V) ts)
  | [], () => some ()
  | _ :: _, (a, as) =>
    match resolveArg env a, resolveArgs env as with
    | some a', some as' => some (a', as')
    | _, _ => none

/-- Emit a validated prefix of hoisted pure-total `.let_` bindings before a `.group`, extending
`next`, `env`, and `tbl` lexically for `cont`. Any invalid, duplicate, or out-of-scope entry in
`hoists` is safely skipped. -/
def emitHoists {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hoists : List HoistOp) (next : Nat) (env : VEnv V) (tbl : GvnTbl V)
    (cont : Nat → VEnv V → GvnTbl V → Expr V L rs) : Expr V L rs :=
  match hoists with
  | [] => cont next env tbl
  | h :: rest =>
    if h.code.isLicmPure then
      match tbl.find h.sig h.ts h.code h.args with
      | some _ => emitHoists rest next env tbl cont
      | none =>
        match resolveArgs env h.args with
        | some vArgs =>
          .let_ ⟨h.code, vArgs⟩ fun xs =>
            let gs := freshGVals h.ts xs next
            let env' := envInsertTup env next xs
            let tbl' := tbl.insert h.sig h.ts h.code h.args gs
            emitHoists rest (next + h.ts.length) env' tbl' cont
        | none => emitHoists rest next env tbl cont
    else
      emitHoists rest next env tbl cont

mutual
/-- Verified PHOAS LICM sweep: emits validated `HoistOp` prefixes before `.group` nodes and
replaces matching pure-total `.let_` bindings inside loops via `tbl`. -/
def licmSweep {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (env : VEnv V) (tbl : GvnTbl V) (plan : HoistPlan) :
    Expr (GVal V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    let kArgs := tupGKey op.args
    match tbl.find op.sig ts op.code kArgs with
    | some cached => licmSweep next env tbl kPlan (k cached)
    | none =>
      .let_ ⟨op.code, tupGOut op.args⟩ fun xs =>
        licmSweep (next + ts.length) (envInsertTup env next xs) tbl kPlan
          (k (freshGVals ts xs next))
  | .load t a k =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    .load t a.gout fun v =>
      licmSweep (next + 1) (env.insert next ⟨t, v⟩) tbl kPlan (k (v, next))
  | .store v a k =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    .store v.gout a.gout (licmSweep next env tbl kPlan k)
  | .call f (bs := bs) args k =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    .call f (tupGOut args) fun xs =>
      licmSweep (next + bs.length) (envInsertTup env next xs) tbl kPlan
        (k (freshGVals bs xs next))
  | .jnz c t e =>
    let (pt, pe) := match plan with | .node2 pt pe => (pt, pe) | _ => (.leaf, .leaf)
    .jnz c.gout (licmSweep next env tbl pt t) (licmSweep next env tbl pe e)
  | .jump j args => .jump j (tupGOut args)
  | .ret vs => .ret (tupGOut vs)
  | .exit f args => .exit f (tupGOut args)
  | .hlt => .hlt
  | .group bodies k =>
    let (hoists, bsPlan, kPlan) := match plan with
      | .groupNode hs bsP kP => (hs, bsP, kP)
      | _ => ([], .nil, .leaf)
    emitHoists hoists next env tbl fun next' env' tbl' =>
      .group
        (fun Js => licmSweepB next' env' tbl' bsPlan (bodies Js))
        (fun Js => licmSweep next' env' tbl' kPlan (k Js))

/-- Block-list companion of `licmSweep`. -/
def licmSweepB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (env : VEnv V) (tbl : GvnTbl V) (bsPlan : HoistBlocks) :
    {sig : List (List Ty)} → Blocks (GVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    let (ph, pt) := match bsPlan with | .cons ph pt => (ph, pt) | _ => (.leaf, .nil)
    .cons
      (fun xs => licmSweep (next + ts.length) (envInsertTup env next xs) tbl ph
        (b (freshGVals ts xs next)))
      (licmSweepB next env tbl pt bs)
end

/-! ## Read-only loop load hoisting and dominating load forwarding -/

/-- A hoisted read-only load descriptor (`load ty addr`) with outer level address `addr`. -/
structure HoistLoad : Type where
  ty : Ty
  addr : Arg K (.bits 64)

mutual
/-- Structural plan for read-only loop load hoisting and dominating load forwarding. -/
inductive RoPlan : Type
  | leaf : RoPlan
  | node1 (k : RoPlan) : RoPlan
  | fwdLoad (lvl : Nat) (k : RoPlan) : RoPlan
  | node2 (t e : RoPlan) : RoPlan
  | groupNode (hoists : List HoistLoad) (bs : RoBlocks) (k : RoPlan) : RoPlan

/-- Block-list companion of `RoPlan`. -/
inductive RoBlocks : Type
  | nil : RoBlocks
  | cons (hd : RoPlan) (tl : RoBlocks) : RoBlocks
end

mutual
/-- True iff `p` performs at least one load hoist or forwarded load. -/
def RoPlan.hasChanges : RoPlan → Bool
  | .leaf => false
  | .node1 k => k.hasChanges
  | .fwdLoad _ _ => true
  | .node2 t e => t.hasChanges || e.hasChanges
  | .groupNode hs bs k => !hs.isEmpty || bs.hasChanges || k.hasChanges

/-- Block-list companion of `RoPlan.hasChanges`. -/
def RoBlocks.hasChanges : RoBlocks → Bool
  | .nil => false
  | .cons hd tl => hd.hasChanges || tl.hasChanges
end

namespace Licm

/-- Maximum outer live-in variables for hoisting guaranteed header loads into preheader. -/
def roLoadPressCap : Nat := 12

mutual
/-- True iff `tf` contains no `.jump j` with `lo ≤ j ∧ j < hi`. -/
def noJumpInRange (lo hi : Nat) {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => noJumpInRange lo hi k
  | .jnz _ t e => noJumpInRange lo hi t && noJumpInRange lo hi e
  | .jump j _ => !(Nat.ble lo j && Nat.blt j hi)
  | .ret _ | .exit _ _ | .hlt => true
  | .group (sig := sig) bodies k =>
    noJumpInRangeB (lo + sig.length) (hi + sig.length) bodies &&
    noJumpInRange (lo + sig.length) (hi + sig.length) k

/-- Block-list companion of `noJumpInRange`. -/
def noJumpInRangeB (lo hi : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => noJumpInRange lo hi b && noJumpInRangeB lo hi bs
end

mutual
/-- True iff no `.store` or `.call` in `tf` can reach a `.jump j` with `lo ≤ j ∧ j < hi`. -/
def memCleanReaches (lo hi : Nat) {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k | .load _ _ k => memCleanReaches lo hi k
  | .store _ _ k | .call _ _ _ k => noJumpInRange lo hi k
  | .jnz _ t e => memCleanReaches lo hi t && memCleanReaches lo hi e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => true
  | .group (sig := sig) bodies k =>
    let lo' := lo + sig.length
    let hi' := hi + sig.length
    if noJumpInRangeB lo' hi' bodies && noJumpInRange lo' hi' k then true
    else memCleanReachesB 0 hi' bodies && memCleanReaches 0 hi' k

/-- Block-list companion of `memCleanReaches`. -/
def memCleanReachesB (lo hi : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => memCleanReaches lo hi b && memCleanReachesB lo hi bs
end

/-- Lookup `(t, addrLvl)` in `ldTbl : List (Ty × Nat × Nat)` (`(t, addrLvl, valLvl)`). -/
def lookupLd (t : Ty) (alvl : Nat) : List (Ty × Nat × Nat) → Option Nat
  | [] => none
  | (t', a', v') :: rest => if t' == t && a' == alvl then some v' else lookupLd t alvl rest

/-- Map a `.bits 64` address arg through `senv` (outer levels or `none` for local/variant). -/
def mapRoAddr (senv : List (Option Nat)) : Arg K (.bits 64) → Option (Arg K (.bits 64))
  | .imm c => some (.imm c)
  | .var idx =>
    match listGet? senv idx with
    | some (some lvl) => some (.var lvl)
    | _ => none

/-- Collect safe invariant loads along a straight-line prefix (`isLicmPure` `.let_` + invariant
`.load`s), stopping at any branch/mem-op/variant-load or non-pure op, returning
`(hoists, newLdTbl, endJump?)`. -/
def scanPrefixLoads (cap : Nat) (next : Nat) (senv : List (Option Nat))
    (ldTbl : List (Ty × Nat × Nat)) {rs : List Ty} :
    TFlat rs → List HoistLoad × List (Ty × Nat × Nat) × Option Nat
  | .let_ (ts := ts) op k =>
    if op.code.isLicmPure then
      scanPrefixLoads cap next (pushNones ts.length senv) ldTbl k
    else ([], ldTbl, none)
  | .load t a k =>
    match mapRoAddr senv a with
    | some ka =>
      let already? := match ka with | .var alvl => lookupLd t alvl ldTbl | .imm _ => none
      match already? with
      | some vlvl =>
        scanPrefixLoads cap next (some vlvl :: senv) ldTbl k
      | none =>
        if Nat.ble cap 0 then
          ([], ldTbl, none)
        else
          let ldTbl' := match ka with | .var alvl => (t, alvl, next) :: ldTbl | .imm _ => ldTbl
          let (hs, lds, jmp?) :=
            scanPrefixLoads (cap - 1) (next + 1) (some next :: senv) ldTbl' k
          (⟨t, ka⟩ :: hs, lds, jmp?)
    | none => ([], ldTbl, none)
  | .jump i _ => ([], ldTbl, some i)
  | _ => ([], ldTbl, none)

/-- Extract `block[idx]` from `TBlocks` with its outer parameter binder count. -/
def getBlock? {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Option (Nat × TFlat rs)
  | _, .nil, _ => none
  | ts :: _, .cons b _, 0 => some (ts.length, b)
  | _ :: _, .cons _ bs, n + 1 => getBlock? bs n

/-- Decompose a `ReachTree` node for straight-line constructors. -/
def roRtStep1 : ReachTree → Bool × ReachTree
  | .node1 r rk => (r, rk)
  | _ => (false, .leaf false)

mutual
/-- Top-down read-only loop load hoist and dominating load forwarding planner.
When `inLoop` is `some rt`, forwards `ldTbl` hits only when `rt` can reach a backedge
so cold exit paths never extend live ranges across the loop. -/
def analyzeRoTFlat {rs : List Ty} (next : Nat) (env : List Nat)
    (ldTbl : List (Ty × Nat × Nat)) (inLoop : Option ReachTree) : TFlat rs → RoPlan
  | .let_ (ts := ts) _ k =>
    let inL' := inLoop.map (fun rt => (roRtStep1 rt).2)
    .node1 (analyzeRoTFlat (next + ts.length) (pushLevels ts.length next env) ldTbl inL' k)
  | .load t a k =>
    let (allowFwd, inL') := match inLoop with
      | none => (true, none)
      | some rt => let (r, rk) := roRtStep1 rt; (r, some rk)
    let alvl? := match a with | .var idx => listGet? env idx | .imm _ => none
    match if allowFwd then alvl?.bind (fun alvl => lookupLd t alvl ldTbl) else none with
    | some vlvl => .fwdLoad vlvl (analyzeRoTFlat next (vlvl :: env) ldTbl inL' k)
    | none =>
      let ldTbl' := match alvl? with | some alvl => (t, alvl, next) :: ldTbl | none => ldTbl
      .node1 (analyzeRoTFlat (next + 1) (next :: env) ldTbl' inL' k)
  | .store _ _ k =>
    let inL' := inLoop.map (fun rt => (roRtStep1 rt).2)
    .node1 (analyzeRoTFlat next env [] inL' k)
  | .call _ (bs := bs) _ k =>
    let inL' := inLoop.map (fun rt => (roRtStep1 rt).2)
    .node1 (analyzeRoTFlat (next + bs.length) (pushLevels bs.length next env) [] inL' k)
  | .jnz _ t e =>
    let (inT, inE) := match inLoop with
      | some (.node2 _ rt re) => (some rt, some re)
      | some _ => (some (.leaf false), some (.leaf false))
      | none => (none, none)
    .node2 (analyzeRoTFlat next env ldTbl inT t) (analyzeRoTFlat next env ldTbl inE e)
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => .leaf
  | .group (sig := sig) bodies k =>
    let loopMask := computeLoopMask bodies
    let inK := inLoop.map (fun rt => match rt with | .groupNode _ _ rk => rk | _ => .leaf false)
    let cleanGroup :=
      Nat.blt 0 sig.length &&
      memCleanReachesB 0 sig.length bodies &&
      memCleanReaches 0 sig.length k
    if !cleanGroup then
      .groupNode [] (analyzeRoTBlocks next env [] .nil false bodies)
        (analyzeRoTFlat next env ldTbl inK k)
    else if loopMask.isEmpty then
      let rbsSub := match inLoop with
        | some (.groupNode _ rbs _) => rbs
        | _ => .nil
      .groupNode [] (analyzeRoTBlocks next env ldTbl rbsSub inLoop.isSome bodies)
        (analyzeRoTFlat next env ldTbl inK k)
    else
      let outerCard := trieCard (collectOuterB 0 bodies .empty)
      let lowPress := Nat.blt outerCard roLoadPressCap
      let budget := if lowPress then roLoadPressCap - outerCard else 0
      let senv := env.map some
      let (hsE, ldE, jmp?) :=
        if lowPress then scanPrefixLoads budget next senv ldTbl k else ([], ldTbl, none)
      let nextE := next + hsE.length
      let rem := budget - hsE.length
      let (hsB, ldB) :=
        if Nat.blt 0 rem then
          let getBlk := fun j =>
            if Nat.blt j sig.length then getBlock? bodies (sig.length - 1 - j) else none
          match jmp?.bind getBlk with
          | some (nPars, b) =>
            let (hs2, ld2, _) := scanPrefixLoads rem nextE (pushNones nPars senv) ldE b
            (hs2, ld2)
          | none => ([], ldE)
        else ([], ldE)
      let hoists := hsE ++ hsB
      let next' := next + hoists.length
      let rbsLoop := (buildReachWithB false 0 loopMask bodies).2
      let bsLd := if lowPress then ldB else []
      .groupNode hoists (analyzeRoTBlocks next' env bsLd rbsLoop true bodies)
        (analyzeRoTFlat next' env ldB inK k)

/-- Block-list companion of `analyzeRoTFlat`. -/
def analyzeRoTBlocks {rs : List Ty} (next : Nat) (env : List Nat)
    (ldTbl : List (Ty × Nat × Nat)) (rbs : ReachBlocks) (gateReach : Bool) :
    {sig : List (List Ty)} → TBlocks rs sig → RoBlocks
  | _, .nil => .nil
  | ts :: _, .cons b bs =>
    let (rh, rtl) := match rbs with | .cons rh rtl => (rh, rtl) | _ => (.leaf false, .nil)
    let inB := if gateReach then some rh else none
    .cons (analyzeRoTFlat (next + ts.length) (pushLevels ts.length next env) ldTbl inB b)
      (analyzeRoTBlocks next env ldTbl rtl gateReach bs)
end

/-- Compute the `RoPlan` for a reified function body with `nParams` parameters. -/
def buildRoPlan {rs : List Ty} (nParams : Nat) (tf : TFlat rs) : RoPlan :=
  analyzeRoTFlat nParams (pushLevels nParams 0 []) [] none tf

end Licm

/-- Emit hoisted `.load`s before a clean `.group`. -/
def emitRoHoists {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hoists : List HoistLoad) (next : Nat) (env : VEnv V)
    (cont : Nat → VEnv V → Expr V L rs) : Expr V L rs :=
  match hoists with
  | [] => cont next env
  | h :: rest =>
    match resolveArg env h.addr with
    | some va =>
      .load h.ty va fun v => emitRoHoists rest (next + 1) (env.insert next ⟨h.ty, v⟩) cont
    | none => emitRoHoists rest next env cont

mutual
/-- Apply a `RoPlan` over `Expr V L rs`, hoisting safe loads and forwarding dominated loads. -/
def roSweep {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (env : VEnv V) (plan : RoPlan) : Expr V L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    .let_ op fun xs => roSweep (next + ts.length) (envInsertTup env next xs) kPlan (k xs)
  | .load t a k =>
    match plan with
    | .fwdLoad lvl kPlan =>
      match env.find? lvl with
      | some ⟨t', v⟩ =>
        if h : t' = t then roSweep next env kPlan (k (h ▸ v))
        else .load t a fun v => roSweep (next + 1) (env.insert next ⟨t, v⟩) kPlan (k v)
      | none => .load t a fun v => roSweep (next + 1) (env.insert next ⟨t, v⟩) kPlan (k v)
    | _ =>
      let kPlan := match plan with | .node1 p => p | _ => .leaf
      .load t a fun v => roSweep (next + 1) (env.insert next ⟨t, v⟩) kPlan (k v)
  | .store v a k =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    .store v a (roSweep next env kPlan k)
  | .call f (bs := bs) args k =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    .call f args fun xs => roSweep (next + bs.length) (envInsertTup env next xs) kPlan (k xs)
  | .jnz c t e =>
    let (tPlan, ePlan) := match plan with | .node2 tp ep => (tp, ep) | _ => (.leaf, .leaf)
    .jnz c (roSweep next env tPlan t) (roSweep next env ePlan e)
  | .jump lbl args => .jump lbl args
  | .ret vs => .ret vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group bodies k =>
    let (hoists, bsPlan, kPlan) := match plan with
      | .groupNode hs bsP kP => (hs, bsP, kP)
      | _ => ([], .nil, .leaf)
    emitRoHoists hoists next env fun next' env' =>
      .group
        (fun Js => roSweepB next' env' bsPlan (bodies Js))
        (fun Js => roSweep next' env' kPlan (k Js))

/-- Block-list companion of `roSweep`. -/
def roSweepB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (env : VEnv V) (plan : RoBlocks) :
    {sig : List (List Ty)} → Blocks V L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | ts :: _, .cons b bs =>
    let (hdP, tlP) := match plan with | .cons hd tl => (hd, tl) | _ => (.leaf, .nil)
    .cons (fun xs => roSweep (next + ts.length) (envInsertTup env next xs) hdP (b xs))
      (roSweepB next env tlP bs)
end

/-- Run pure Loop-Invariant Code Motion (`LICM`) on a closed function `Func`. -/
def Func.licmPure {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let plan := Licm.buildHoistPlan as.length (reifyFunc f)
  if plan.hasHoists then
    fun V L xs =>
      licmSweep as.length (envInsertTup .empty 0 xs) .empty plan
        (f (GVal V) L (freshGVals as xs 0))
  else
    f

/-- Read-only loop load hoisting and dominating load forwarding on a closed function `Func`. -/
def Func.licmRoLoad {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let plan := Licm.buildRoPlan as.length (reifyFunc f)
  if plan.hasChanges then
    fun V L xs => roSweep as.length (envInsertTup .empty 0 xs) plan (f V L xs)
  else
    f

/-- Run Loop-Invariant Code Motion (`LICM`) on a closed function `Func`: pure invariant hoisting,
read-only loop load hoisting/forwarding, and a follow-up pure pass when loads move. -/
def Func.licm {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let f1 := f.licmPure
  let plan := Licm.buildRoPlan as.length (reifyFunc f1)
  if plan.hasChanges then
    let f2 : Func as rs :=
      fun V L xs => roSweep as.length (envInsertTup .empty 0 xs) plan (f1 V L xs)
    f2.licmPure
  else
    f1

/-- Run Loop-Invariant Code Motion (`LICM`) on a named function `Fn`. -/
def Fn.licm (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.licm fn.body⟩

end LeanQbe.T
