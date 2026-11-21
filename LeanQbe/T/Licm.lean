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

/-- Extract the root reachability flag of a `ReachTree`. -/
def ReachTree.reaches : ReachTree → Bool
  | .leaf r | .node1 r _ | .node2 r _ _ | .groupNode r _ _ => r

mutual
/-- Compute bottom-up backedge-reachability tree for `tf` against target label mask `mask`. -/
def buildReach (mask : List Nat) {rs : List Ty} : TFlat rs → ReachTree
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    let rk := buildReach mask k
    .node1 rk.reaches rk
  | .jnz _ t e =>
    let rt := buildReach mask t
    let re := buildReach mask e
    .node2 (rt.reaches || re.reaches) rt re
  | .jump j _ => .leaf (mask.contains j)
  | .ret _ | .exit _ _ | .hlt => .leaf false
  | .group (sig := sig) bodies k =>
    let outerMask := mask.map (· + sig.length)
    let ext := extReachMask outerMask bodies
    let mask' := ext ++ outerMask
    let (rb, rbs) := buildReachB mask' bodies
    let rk := buildReach mask' k
    .groupNode (rb || rk.reaches) rbs rk

/-- Block-list companion of `buildReach`. -/
def buildReachB (mask : List Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool × ReachBlocks
  | _, .nil => (false, .nil)
  | _, .cons b bs =>
    let rb := buildReach mask b
    let (rbs, rt) := buildReachB mask bs
    (rb.reaches || rbs, .cons rb rt)
end

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

/-- Run Loop-Invariant Code Motion (`LICM`) on a closed function `Func`. Returns `f` unchanged
when no loop-invariant pure total operations are found. -/
def Func.licm {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let plan := Licm.buildHoistPlan as.length (reifyFunc f)
  if plan.hasHoists then
    fun V L xs =>
      licmSweep as.length (envInsertTup .empty 0 xs) .empty plan
        (f (GVal V) L (freshGVals as xs 0))
  else
    f

/-- Run Loop-Invariant Code Motion (`LICM`) on a named function `Fn`. -/
def Fn.licm (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.licm fn.body⟩

end LeanQbe.T
