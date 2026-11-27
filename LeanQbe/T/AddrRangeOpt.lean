module

public import LeanQbe.T.OptUtil
public import LeanQbe.T.Licm

/-!
# Loop-Aware Address Reassociation & Range-Check Collapse (`Func.addrRangeOpt`)

Single-traversal linear PHOAS pass scheduled in `Func.lateCfgPre` (after `Legal` and `Fold`,
before `Gvn` and `Licm`), combining two semantics-preserving algebraic optimizations:

1. **Loop-aware address reassociation (`#3`):**
   - An untrusted `O(N)` `TFlat` pre-scan (`buildLoopTree`, reusing `Licm.computeLoopMask`)
     identifies looping blocks so each bound value tracks its effective loop nesting depth
     (`0` for function parameters, immediates, and transitively invariant pure operations).
   - Inside loops (`curD > 0`), rewrites 64-bit linear address patterns whose `base` and
     invariant summand `inv` both lie strictly outside the loop of `iv`
     (`max base.depth inv.depth < iv.depth`):
     * `base + (((inv + iv) <<< sh) + disp)` → `((base + (inv <<< sh)) + (iv <<< sh)) + disp`
     * `base + (((iv - inv) <<< sh) + disp)` → `((base - (inv <<< sh)) + (iv <<< sh)) + disp`
     * `base + ((inv + iv) + disp)` → `((base + inv) + iv) + disp`
     * `base + ((iv - inv) + disp)` → `((base - inv) + iv) + disp`
     All four identities hold unconditionally mod `2^64` (no `inbounds` or no-wrap assumptions).
     Subsequent `Gvn` + `Licm` hoist `base ± (inv <<< sh)` out of the loop, leaving a single
     scaled-index load/store (`(%base, %iv, 4)` on x86-64; `[xB, xI, lsl #2]` on AArch64), and
     `DceParam` removes the dead unsplit address ops.

2. **Signed & unsigned range-check collapse (`#1c`):**
   - Tracks scalar `.bits w` immediate comparison provenance `lhs op imm` (including `.not .bool`
     negation and swapped immediate-on-left forms).
   - Collapses same-operand range checks into a single unsigned compare (or constant bool when
     empty/tautological):
     * `(lo ≤s x && x <s hi)` / `(lo ≤u x && x <u hi)` → `(x - lo) <u (hi - lo)` (or `x <u hi`
       when `lo = 0`, or `false` when `hi ≤ lo`).
     * `(x <s lo || hi ≤s x)` / `(x <u lo || hi ≤u x)` → `(x - lo) ≥u (hi - lo)` (or `x ≥u hi`
       when `lo = 0`, or `true` when `hi ≤ lo`).
     Non-strict bounds (`≤`, `>`) are normalized to strict bounds when non-extreme.

3. **Fast-path gating:** functions with neither an in-loop 64-bit `add` nor any `.and .bool`/
   `.or .bool` return `f` unchanged without traversing PHOAS closures.

Correctness (`LeanQbe/T/AddrRangeOptLemmas.lean`): `addrRangeSweep_wp`, `addrRangeSweep_wf`,
`Func.addrRangeOpt_wf`, `Func.addrRangeOpt_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Phase 1 (untrusted): `TFlat` loop-block tree and candidate pre-scan -/

mutual
/-- Structural mirror of `Expr` marking looping blocks inside each `.group` and per-site
displacement-folding decisions (`foldDisp` on `.let_` nodes). -/
inductive LoopTree : Type
  | leaf : LoopTree
  | node1 (foldDisp : Bool) (k : LoopTree) : LoopTree
  | node2 (t e : LoopTree) : LoopTree
  | groupNode (bs : LoopBlocks) (k : LoopTree) : LoopTree

/-- Block-list companion of `LoopTree`. -/
inductive LoopBlocks : Type
  | nil : LoopBlocks
  | cons (isLoop : Bool) (hd : LoopTree) (tl : LoopBlocks) : LoopBlocks
end

namespace AddrRangeOpt

/-- True iff `code` is a candidate for `addrRangeOpt` at `inLoop`. -/
def isCandOp (inLoop : Bool) : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .add (.bits 64) => inLoop
  | _, _, .and .bool => true
  | _, _, .or .bool => true
  | _, _, _ => false

/-- True iff `code` is an in-loop 64-bit `add` candidate. -/
def isInLoopAdd64 (inLoop : Bool) : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .add (.bits 64) => inLoop
  | _, _, _ => false

mutual
/-- Build a `LoopTree`, candidate flag (`hasWork`), and in-loop 64-bit `add` flag (`hasAdd64`). -/
def buildLoopTreeAux (inLoop : Bool) {rs : List Ty} : TFlat rs → LoopTree × Bool × Bool
  | .let_ op k =>
    let (tk, wk, ak) := buildLoopTreeAux inLoop k
    (.node1 false tk, isCandOp inLoop op.code || wk, isInLoopAdd64 inLoop op.code || ak)
  | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    let (tk, wk, ak) := buildLoopTreeAux inLoop k
    (.node1 false tk, wk, ak)
  | .jnz _ t e =>
    let (tt, wt, at_) := buildLoopTreeAux inLoop t
    let (te, we, ae) := buildLoopTreeAux inLoop e
    (.node2 tt te, wt || we, at_ || ae)
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => (.leaf, false, false)
  | .group bodies k =>
    let loopMask := Licm.computeLoopMask bodies
    let (tbs, wbs, abs) := buildLoopBlocksAux inLoop loopMask bodies
    let (tk, wk, ak) := buildLoopTreeAux inLoop k
    (.groupNode tbs tk, wbs || wk, abs || ak)

/-- Block-list companion of `buildLoopTreeAux`. -/
def buildLoopBlocksAux (inLoop : Bool) (loopMask : List Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → LoopBlocks × Bool × Bool
  | [], .nil => (.nil, false, false)
  | _ :: sig, .cons b bs =>
    let isL := loopMask.contains sig.length
    let (tb, wb, ab) := buildLoopTreeAux (inLoop || isL) b
    let (tbs, wbs, abs) := buildLoopBlocksAux inLoop loopMask bs
    (.cons isL tb tbs, wb || wbs, ab || abs)
end

/-- Build a `LoopTree` and a candidate flag (`true` iff the function contains an in-loop
64-bit `add` or any `.and .bool` / `.or .bool`). -/
def buildLoopTree (inLoop : Bool) {rs : List Ty} (tf : TFlat rs) : LoopTree × Bool :=
  let (t, w, _) := buildLoopTreeAux inLoop tf
  (t, w)

/-- Untrusted key identifying a hoisted invariant base `(isSub, baseUid, invUid, sh)`
(`sh = 0` for `addrPlain`; `0 < sh < 64` for `addrShl`). -/
structure DispKey where
  isSub : Bool
  baseUid : Nat
  invUid : Nat
  sh : Nat
  deriving BEq

/-- Displacement uniqueness state for a `DispKey` across all reassociated sites in a function. -/
inductive DispState where
  | unique (d : BitVec 64)
  | conflict

/-- Record `(key, disp)` in a displacement uniqueness table. -/
def DispTable.record (tbl : List (DispKey × DispState)) (key : DispKey)
    (disp : BitVec 64) : List (DispKey × DispState) :=
  match tbl with
  | [] => [(key, .unique disp)]
  | (k, st) :: rest =>
    if k == key then
      let st' := match st with
        | .unique d => if d == disp then .unique d else .conflict
        | .conflict => .conflict
      (k, st') :: rest
    else (k, st) :: DispTable.record rest key disp

/-- True iff `key` has a single unique non-zero displacement across the function. -/
def DispTable.isUniqueNonZero (tbl : List (DispKey × DispState)) (key : DispKey) : Bool :=
  match tbl.find? (fun p => p.1 == key) with
  | some (_, .unique d) => d != 0#64
  | _ => false

/-- Untrusted 64-bit linear-address summary for Phase-1 displacement uniqueness analysis. -/
inductive PlanAddr where
  | addVC (x dx : Nat) (disp : BitVec 64)
  | shlVC (x dx sh : Nat) (disp : BitVec 64)
  | addVV (x dx y dy : Nat) (disp : BitVec 64)
  | subVV (x dx y dy : Nat) (disp : BitVec 64)
  | shlAddVV (x dx y dy sh : Nat) (disp : BitVec 64)
  | shlSubVV (x dx y dy sh : Nat) (disp : BitVec 64)

/-- Shift displacement of a `PlanAddr` by `c`. -/
def PlanAddr.shiftDisp (c : BitVec 64) : PlanAddr → PlanAddr
  | .addVC x dx d => .addVC x dx (d + c)
  | .shlVC x dx sh d => .shlVC x dx sh (d + c)
  | .addVV x dx y dy d => .addVV x dx y dy (d + c)
  | .subVV x dx y dy d => .subVV x dx y dy (d + c)
  | .shlAddVV x dx y dy sh d => .shlAddVV x dx y dy sh (d + c)
  | .shlSubVV x dx y dy sh d => .shlSubVV x dx y dy sh (d + c)

/-- Per-variable untrusted Phase-1 summary `(uid, depth, addr?)`. -/
structure PlanVal where
  uid : Nat
  depth : Nat
  addr? : Option PlanAddr := none

/-- Look up a de Bruijn index `i` at `inDepth` in `env`. -/
def planLookup (inDepth : Nat) (env : Trie PlanVal) (i : Nat) : PlanVal :=
  let lvl := inDepth - 1 - i
  env.getD lvl ⟨lvl, 0, none⟩

/-- Maximum loop depth across `TFlat` arguments. -/
def planTupMaxDepth (inDepth : Nat) (env : Trie PlanVal) :
    {ts : List Ty} → Tup (Arg (fun _ => Nat)) ts → Nat
  | [], () => 0
  | _ :: _, (.imm _, as) => planTupMaxDepth inDepth env as
  | _ :: _, (.var i, as) =>
    Nat.max (planLookup inDepth env i).depth (planTupMaxDepth inDepth env as)

/-- Insert `n` fresh `PlanVal` entries at depth `d` starting from `inDepth` and `uid`. -/
def planInsertFresh (d : Nat) : Nat → Nat → Nat → Trie PlanVal → Nat × Trie PlanVal
  | 0, _, uid, env => (uid, env)
  | k + 1, inD, uid, env =>
    planInsertFresh d k (inD + 1) (uid + 1) (env.insert inD ⟨uid, d, none⟩)

/-- Mirror `tryAddrReassocOne` in Phase-1 `uid` space, returning
`(key, disp, ivD, plainT1InvD?)`. -/
def planTryReassocOne (inDepth : Nat) (env : Trie PlanVal)
    (baseArg offArg : Arg (fun _ => Nat) (.bits 64)) :
    Option (DispKey × BitVec 64 × Nat × Option (Nat × Nat)) :=
  match baseArg, offArg with
  | .var bi, .var oi =>
    let bv := planLookup inDepth env bi
    let ov := planLookup inDepth env oi
    match ov.addr? with
    | some (.shlAddVV x dx y dy sh disp) =>
      if Nat.blt (Nat.max bv.depth dx) dy then
        some (⟨false, bv.uid, x, sh⟩, disp, dy, none)
      else if Nat.blt (Nat.max bv.depth dy) dx then
        some (⟨false, bv.uid, y, sh⟩, disp, dx, none)
      else none
    | some (.shlSubVV _ dx y dy sh disp) =>
      if Nat.blt (Nat.max bv.depth dy) dx then
        some (⟨true, bv.uid, y, sh⟩, disp, dx, none)
      else none
    | some (.addVV x dx y dy disp) =>
      if Nat.blt (Nat.max bv.depth dx) dy then
        some (⟨false, bv.uid, x, 0⟩, disp, dy, some (Nat.max bv.depth dx, y))
      else if Nat.blt (Nat.max bv.depth dy) dx then
        some (⟨false, bv.uid, y, 0⟩, disp, dx, some (Nat.max bv.depth dy, x))
      else none
    | some (.subVV x dx y dy disp) =>
      if Nat.blt (Nat.max bv.depth dy) dx then
        some (⟨true, bv.uid, y, 0⟩, disp, dx, some (Nat.max bv.depth dy, x))
      else none
    | _ => none
  | _, _ => none

/-- Mirror `recordAddProv` for 64-bit `add` in Phase-1 `uid` space. -/
def planRecordAdd (inDepth : Nat) (env : Trie PlanVal)
    (a b : Arg (fun _ => Nat) (.bits 64)) : Option PlanAddr :=
  match a, b with
  | .var ai, .var bi =>
    let av := planLookup inDepth env ai
    let bv := planLookup inDepth env bi
    match av.addr?, bv.addr? with
    | some (.addVC x dx d1), some (.addVC y dy d2) => some (.addVV x dx y dy (d1 + d2))
    | some (.addVC x dx d1), _ => some (.addVV x dx bv.uid bv.depth d1)
    | _, some (.addVC y dy d2) => some (.addVV av.uid av.depth y dy d2)
    | some (.shlVC x dx sh1 d1), some (.shlVC y dy sh2 d2) =>
      if sh1 == sh2 then some (.shlAddVV x dx y dy sh1 (d1 + d2))
      else some (.addVV av.uid av.depth bv.uid bv.depth 0#64)
    | _, _ => some (.addVV av.uid av.depth bv.uid bv.depth 0#64)
  | .var ai, .imm c =>
    let av := planLookup inDepth env ai
    match av.addr? with
    | some ad => some (ad.shiftDisp c)
    | none => some (.addVC av.uid av.depth c)
  | .imm c, .var bi =>
    let bv := planLookup inDepth env bi
    match bv.addr? with
    | some ad => some (ad.shiftDisp c)
    | none => some (.addVC bv.uid bv.depth c)
  | .imm _, .imm _ => none

/-- Mirror `recordSubProv` for 64-bit `sub` in Phase-1 `uid` space. -/
def planRecordSub (inDepth : Nat) (env : Trie PlanVal)
    (a b : Arg (fun _ => Nat) (.bits 64)) : Option PlanAddr :=
  match a, b with
  | .var ai, .var bi =>
    let av := planLookup inDepth env ai
    let bv := planLookup inDepth env bi
    match av.addr?, bv.addr? with
    | some (.addVC x dx d1), some (.addVC y dy d2) => some (.subVV x dx y dy (d1 - d2))
    | some (.addVC x dx d1), _ => some (.subVV x dx bv.uid bv.depth d1)
    | _, some (.addVC y dy d2) => some (.subVV av.uid av.depth y dy (-d2))
    | some (.shlVC x dx sh1 d1), some (.shlVC y dy sh2 d2) =>
      if sh1 == sh2 then some (.shlSubVV x dx y dy sh1 (d1 - d2))
      else some (.subVV av.uid av.depth bv.uid bv.depth 0#64)
    | _, _ => some (.subVV av.uid av.depth bv.uid bv.depth 0#64)
  | .var ai, .imm c =>
    let av := planLookup inDepth env ai
    match av.addr? with
    | some ad => some (ad.shiftDisp (-c))
    | none => some (.addVC av.uid av.depth (-c))
  | _, _ => none

/-- Mirror `recordShlProv` for 64-bit `shl` in Phase-1 `uid` space. -/
def planRecordShl (inDepth : Nat) (env : Trie PlanVal)
    (a b : Arg (fun _ => Nat) (.bits 64)) : Option PlanAddr :=
  match a, b with
  | .var ai, .imm k =>
    let kn := k.toNat
    if 0 < kn && kn < 64 then
      let av := planLookup inDepth env ai
      match av.addr? with
      | some (.addVC x dx d) => some (.shlVC x dx kn (d <<< kn))
      | some (.shlVC x dx sh d) =>
        if sh + kn < 64 then some (.shlVC x dx (sh + kn) (d <<< kn)) else none
      | some (.addVV x dx y dy d) => some (.shlAddVV x dx y dy kn (d <<< kn))
      | some (.subVV x dx y dy d) => some (.shlSubVV x dx y dy kn (d <<< kn))
      | some (.shlAddVV x dx y dy sh d) =>
        if sh + kn < 64 then some (.shlAddVV x dx y dy (sh + kn) (d <<< kn)) else none
      | some (.shlSubVV x dx y dy sh d) =>
        if sh + kn < 64 then some (.shlSubVV x dx y dy (sh + kn) (d <<< kn)) else none
      | none => some (.shlVC av.uid av.depth kn 0#64)
    else none
  | _, _ => none

mutual
/-- Intermediate tree tagging `.let_` nodes with optional `DispKey` before resolving uniqueness. -/
inductive SiteTree : Type
  | leaf : SiteTree
  | node1 (key? : Option DispKey) (k : SiteTree) : SiteTree
  | node2 (t e : SiteTree) : SiteTree
  | groupNode (bs : SiteBlocks) (k : SiteTree) : SiteTree

/-- Block-list companion of `SiteTree`. -/
inductive SiteBlocks : Type
  | nil : SiteBlocks
  | cons (isLoop : Bool) (hd : SiteTree) (tl : SiteBlocks) : SiteBlocks
end

mutual
/-- Resolve `SiteTree` into `LoopTree` using the completed function-wide `DispTable`. -/
def finalizeSiteTree (tbl : List (DispKey × DispState)) : SiteTree → LoopTree
  | .leaf => .leaf
  | .node1 key? k =>
    let f := match key? with
      | some key => DispTable.isUniqueNonZero tbl key
      | none => false
    .node1 f (finalizeSiteTree tbl k)
  | .node2 t e => .node2 (finalizeSiteTree tbl t) (finalizeSiteTree tbl e)
  | .groupNode bs k => .groupNode (finalizeSiteBlocks tbl bs) (finalizeSiteTree tbl k)

/-- Block-list companion of `finalizeSiteTree`. -/
def finalizeSiteBlocks (tbl : List (DispKey × DispState)) : SiteBlocks → LoopBlocks
  | .nil => .nil
  | .cons isL hd tl => .cons isL (finalizeSiteTree tbl hd) (finalizeSiteBlocks tbl tl)
end

/-- Step one `.let_` operation during Phase-1 displacement collection. -/
def planLetStep (curD inDepth uid : Nat) (env : Trie PlanVal)
    (tbl : List (DispKey × DispState)) {ts : List Ty} (op : Op (fun _ => Nat) ts) :
    Option DispKey × Nat × Trie PlanVal × List (DispKey × DispState) :=
  let outD := if op.code.isLicmPure then planTupMaxDepth inDepth env op.args else curD
  let ⟨code, args⟩ := op
  match code, args with
  | .add (.bits 64), (a, b, ()) =>
    let hit := if 0 < curD then
        match planTryReassocOne inDepth env a b with
        | some r => some r
        | none => planTryReassocOne inDepth env b a
      else none
    match hit with
    | some (key, disp, ivD, plainInfo) =>
      let tbl' := DispTable.record tbl key disp
      match plainInfo with
      | none => (some key, uid + 1, env.insert inDepth ⟨uid, ivD, none⟩, tbl')
      | some (invD, ivUid) =>
        let t1Uid := uid
        let resUid := uid + 1
        (some key, uid + 2,
          env.insert inDepth ⟨resUid, ivD, some (.addVV t1Uid invD ivUid ivD disp)⟩, tbl')
    | none =>
      (none, uid + 1, env.insert inDepth ⟨uid, outD, planRecordAdd inDepth env a b⟩, tbl)
  | .sub (.bits 64), (a, b, ()) =>
    (none, uid + 1, env.insert inDepth ⟨uid, outD, planRecordSub inDepth env a b⟩, tbl)
  | .shl (.bits 64), (a, b, ()) =>
    (none, uid + 1, env.insert inDepth ⟨uid, outD, planRecordShl inDepth env a b⟩, tbl)
  | .copy (.bits 64), (.var ai, ()) =>
    let av := planLookup inDepth env ai
    (none, uid + 1, env.insert inDepth ⟨uid, outD, av.addr?⟩, tbl)
  | _, _ =>
    let (uid', env') := planInsertFresh outD ts.length inDepth uid env
    (none, uid', env', tbl)

mutual
/-- Walk `TFlat` alongside `LoopTree` to collect all reassociated `(DispKey, disp)` sites. -/
def collectDispSites (curD : Nat) {rs : List Ty} :
    LoopTree → TFlat rs → Nat → Nat → Trie PlanVal → List (DispKey × DispState) →
    SiteTree × Nat × List (DispKey × DispState)
  | plan, .let_ (ts := ts) op k, inD, uid, env, tbl =>
    let kPlan := match plan with | .node1 _ pk => pk | _ => .leaf
    let (key?, uid', env', tbl') := planLetStep curD inD uid env tbl op
    let (tk, uid'', tbl'') := collectDispSites curD kPlan k (inD + ts.length) uid' env' tbl'
    (.node1 key? tk, uid'', tbl'')
  | plan, .load _ _ k, inD, uid, env, tbl =>
    let kPlan := match plan with | .node1 _ pk => pk | _ => .leaf
    let (tk, uid', tbl') :=
      collectDispSites curD kPlan k (inD + 1) (uid + 1) (env.insert inD ⟨uid, curD, none⟩) tbl
    (.node1 none tk, uid', tbl')
  | plan, .store _ _ k, inD, uid, env, tbl =>
    let kPlan := match plan with | .node1 _ pk => pk | _ => .leaf
    let (tk, uid', tbl') := collectDispSites curD kPlan k inD uid env tbl
    (.node1 none tk, uid', tbl')
  | plan, .call _ bs _ k, inD, uid, env, tbl =>
    let kPlan := match plan with | .node1 _ pk => pk | _ => .leaf
    let (uid', env') := planInsertFresh curD bs.length inD uid env
    let (tk, uid'', tbl') := collectDispSites curD kPlan k (inD + bs.length) uid' env' tbl
    (.node1 none tk, uid'', tbl')
  | plan, .jnz _ t e, inD, uid, env, tbl =>
    let (pt, pe) := match plan with | .node2 pt pe => (pt, pe) | _ => (.leaf, .leaf)
    let (st, uid1, tbl1) := collectDispSites curD pt t inD uid env tbl
    let (se, uid2, tbl2) := collectDispSites curD pe e inD uid1 env tbl1
    (.node2 st se, uid2, tbl2)
  | _, .jump _ _, _, uid, _, tbl | _, .ret _, _, uid, _, tbl
  | _, .exit _ _, _, uid, _, tbl | _, .hlt, _, uid, _, tbl => (.leaf, uid, tbl)
  | plan, .group bodies k, inD, uid, env, tbl =>
    let (bsPlan, kPlan) := match plan with
      | .groupNode bs pk => (bs, pk)
      | _ => (.nil, .leaf)
    let (sbs, uid1, tbl1) := collectDispSitesB curD bsPlan bodies inD uid env tbl
    let (sk, uid2, tbl2) := collectDispSites curD kPlan k inD uid1 env tbl1
    (.groupNode sbs sk, uid2, tbl2)

/-- Block-list companion of `collectDispSites`. -/
def collectDispSitesB (curD : Nat) {rs : List Ty} :
    LoopBlocks → {sig : List (List Ty)} → TBlocks rs sig → Nat → Nat → Trie PlanVal →
    List (DispKey × DispState) → SiteBlocks × Nat × List (DispKey × DispState)
  | _, [], .nil, _, uid, _, tbl => (.nil, uid, tbl)
  | bsPlan, ts :: _, .cons b bs, inD, uid, env, tbl =>
    let (isL, ph, pt) := match bsPlan with
      | .cons isL ph pt => (isL, ph, pt)
      | .nil => (false, .leaf, .nil)
    let bd := if isL then curD + 1 else curD
    let (uid1, env1) := planInsertFresh bd ts.length inD uid env
    let (sh, uid2, tbl1) := collectDispSites bd ph b (inD + ts.length) uid1 env1 tbl
    let (st, uid3, tbl2) := collectDispSitesB curD pt bs inD uid2 env tbl1
    (.cons isL sh st, uid3, tbl2)
end

/-- Build a `LoopTree` with per-site unique-displacement folding flags (when `foldDisp = true`)
and candidate flag. -/
def buildAddrPlan (foldDisp : Bool) (nArgs : Nat) {rs : List Ty} (tf : TFlat rs) :
    LoopTree × Bool :=
  let (plan, hasWork, hasAdd64) := buildLoopTreeAux false tf
  if !hasWork then (plan, false)
  else if !foldDisp || !hasAdd64 then (plan, true)
  else
    let (uid0, env0) := planInsertFresh 0 nArgs 0 0 .empty
    let (stree, _, tbl) := collectDispSites 0 plan tf nArgs uid0 env0 []
    (finalizeSiteTree tbl stree, true)

end AddrRangeOpt

/-- Extract child plan for single-continuation nodes. -/
def LoopTree.step1 : LoopTree → LoopTree
  | .node1 _ k => k
  | _ => .leaf

/-- Extract per-site displacement-folding flag for `.let_` nodes. -/
def LoopTree.foldDisp : LoopTree → Bool
  | .node1 f _ => f
  | _ => false

/-- Extract branch plans for `.jnz` nodes. -/
def LoopTree.step2 : LoopTree → LoopTree × LoopTree
  | .node2 t e => (t, e)
  | _ => (.leaf, .leaf)

/-- Extract block and continuation plans for `.group` nodes. -/
def LoopTree.stepGroup : LoopTree → LoopBlocks × LoopTree
  | .groupNode bs k => (bs, k)
  | _ => (.nil, .leaf)

/-- Extract head `(isLoop, hdPlan)` and tail `tlPlan` from `LoopBlocks`. -/
def LoopBlocks.stepCons : LoopBlocks → Bool × LoopTree × LoopBlocks
  | .cons isL hd tl => (isL, hd, tl)
  | .nil => (false, .leaf, .nil)

/-! ## Phase 2 (verified): Value provenance (`ARVal`) and local rewrites (`ARStep`) -/

/-- Provenance of a scalar `.bits w` comparison against an immediate: `lhs op imm`. -/
structure CmpImmDef (V : Ty → Type) : Type where
  w : Nat
  op : CmpOp
  lhs : Arg V (.bits w)
  lhsKey : FKey (.bits w)
  imm : BitVec w

/-- Provenance of a zero-extended `.bits m → .bits n` value (`0 < m < n`). -/
structure ZextDef (V : Ty → Type) (n : Nat) : Type where
  m : Nat
  hm0 : 0 < m
  hmn : m < n
  src : Arg V (.bits m)
  srcKey : FKey (.bits m)

/-- Provenance of a `.bits n` linear address term, tracking operand loop depths. -/
inductive AddrDef (V : Ty → Type) (n : Nat) : Type
  /-- `x + disp` where `x` is a variable at loop depth `dx`. -/
  | addVC (x : Arg V (.bits n)) (dx : Nat) (disp : BitVec n)
  /-- `(x <<< sh) + disp` where `sh < n` and `x` has loop depth `dx`. -/
  | shlVC (x : Arg V (.bits n)) (dx : Nat) (sh : Nat) (hsh : sh < n) (disp : BitVec n)
  /-- `x + y + disp` where `x, y` are variables at loop depths `dx, dy`. -/
  | addVV (x : Arg V (.bits n)) (dx : Nat) (y : Arg V (.bits n)) (dy : Nat) (disp : BitVec n)
  /-- `x - y + disp` where `x, y` are variables at loop depths `dx, dy`. -/
  | subVV (x : Arg V (.bits n)) (dx : Nat) (y : Arg V (.bits n)) (dy : Nat) (disp : BitVec n)
  /-- `((x + y) <<< sh) + disp` where `sh < n` and `x, y` have depths `dx, dy`. -/
  | shlAddVV (x : Arg V (.bits n)) (dx : Nat) (y : Arg V (.bits n)) (dy : Nat)
      (sh : Nat) (hsh : sh < n) (disp : BitVec n)
  /-- `((x - y) <<< sh) + disp` where `sh < n` and `x, y` have depths `dx, dy`. -/
  | shlSubVV (x : Arg V (.bits n)) (dx : Nat) (y : Arg V (.bits n)) (dy : Nat)
      (sh : Nat) (hsh : sh < n) (disp : BitVec n)

/-- Combined `.bits n` provenance: optional linear address and optional zero-extension source. -/
structure BitsProv (V : Ty → Type) (n : Nat) : Type where
  addr? : Option (AddrDef V n) := none
  zext? : Option (ZextDef V n) := none

/-- Type-indexed provenance carried by `ARVal`:
* `.bool`: optional immediate comparison `CmpImmDef V`;
* `.bits n`: `BitsProv V n` (`addr?` for `n = 64` linear addresses, `zext?` for `.zext m n`);
* all other types: `Unit`. -/
abbrev ARProv (V : Ty → Type) : Ty → Type
  | .bool => Option (CmpImmDef V)
  | .bits n => BitsProv V n
  | .float _ | .pair _ _ => Unit

/-- Absence of provenance at any type `t`. -/
def ARProv.none {V : Ty → Type} : {t : Ty} → ARProv V t
  | .bool => Option.none
  | .bits _ => {}
  | .float _ | .pair _ _ => ()

/-- Value representation threaded through `addrRangeSweep`. -/
structure ARVal (V : Ty → Type) (t : Ty) : Type where
  out : Arg V t
  key : FKey t
  depth : Nat
  prov : ARProv V t := .none

/-- Fresh bound variable `ARVal` at loop depth `d` with symbolic key `next`. -/
def ARVal.fresh {V : Ty → Type} {t : Ty} (v : V t) (next d : Nat) : ARVal V t :=
  ⟨.var v, .var next, d, .none⟩

/-- Constant `ARVal` carrying immediate `c` (loop depth `0`). -/
def ARVal.ofImm {V : Ty → Type} {t : Ty} (c : Val t) : ARVal V t :=
  ⟨.imm c, .imm c, 0, .none⟩

/-- Wrap bound output variables `xs : Tup V ts` into fresh `ARVal V`s at loop depth `d`. -/
abbrev freshARVals {V : Ty → Type} (d : Nat) :
    (ts : List Ty) → Tup V ts → Nat → Tup (ARVal V) ts :=
  tupFreshWith fun x next => ARVal.fresh x next d

/-- Output operand of an `Arg (ARVal V) t`. -/
def Arg.arOut {V : Ty → Type} {t : Ty} : Arg (ARVal V) t → Arg V t
  | .var a => a.out
  | .imm c => .imm c

/-- Symbolic key of an `Arg (ARVal V) t`. -/
def Arg.arKey {V : Ty → Type} {t : Ty} : Arg (ARVal V) t → FKey t
  | .var a => a.key
  | .imm c => .imm c

/-- Loop depth of an `Arg (ARVal V) t` (`0` for immediates). -/
def Arg.arDepth {V : Ty → Type} {t : Ty} : Arg (ARVal V) t → Nat
  | .var a => a.depth
  | .imm _ => 0

/-- Provenance of an `Arg (ARVal V) t`. -/
def Arg.arProv {V : Ty → Type} {t : Ty} : Arg (ARVal V) t → ARProv V t
  | .var a => a.prov
  | .imm _ => .none

/-- Promote an `Arg (ARVal V) t` to `ARVal V t`, preserving provenance and depth on variables. -/
def Arg.toARVal {V : Ty → Type} {t : Ty} : Arg (ARVal V) t → ARVal V t
  | .var a => a
  | .imm c => ARVal.ofImm c

/-- Map `Arg.arOut` across an operand tuple. -/
abbrev tupArOut {V : Ty → Type} : {ts : List Ty} → Tup (Arg (ARVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => Arg.arOut

/-- Maximum loop depth across all operands in a tuple (`0` if empty or all immediates). -/
def tupMaxDepth {V : Ty → Type} : {ts : List Ty} → Tup (Arg (ARVal V)) ts → Nat
  | [], () => 0
  | _ :: _, (a, as) => Nat.max a.arDepth (tupMaxDepth as)

/-! ## Range-check bound normalization (`RangeBound`) -/

/-- Maximum signed `w`-bit two's-complement value (`2^(w-1) - 1` for `w > 0`, `0#0` for `w = 0`). -/
def arIntMax (w : Nat) : BitVec w := ~~~(BitVec.intMin w)

/-- Normalized single-sided bound on a `w`-bit value `x`: `lo ≤ x` or `x < hi` (signed/unsigned). -/
inductive RangeBound (w : Nat) : Type
  | ge (signed : Bool) (lo : BitVec w)
  | lt (signed : Bool) (hi : BitVec w)

/-- Normalize a comparison `x o c` into a half-open bound `lo ≤ x` or `x < hi`. -/
def toRangeBound {w : Nat} : CmpOp → BitVec w → Option (RangeBound w)
  | .uge, c => some (.ge false c)
  | .ugt, c => if c != BitVec.allOnes w then some (.ge false (c + 1#w)) else none
  | .ult, c => some (.lt false c)
  | .ule, c => if c != BitVec.allOnes w then some (.lt false (c + 1#w)) else none
  | .sge, c => some (.ge true c)
  | .sgt, c => if c != arIntMax w then some (.ge true (c + 1#w)) else none
  | .slt, c => some (.lt true c)
  | .sle, c => if c != arIntMax w then some (.lt true (c + 1#w)) else none
  | _, _ => none

/-- Extract `(signed, lo, hi)` for an `and` range check `(lo ≤ x) && (x < hi)` in either order. -/
def matchAndBounds {w : Nat} (b1 b2 : RangeBound w) : Option (Bool × BitVec w × BitVec w) :=
  match b1, b2 with
  | .ge s1 lo, .lt s2 hi => if s1 == s2 then some (s1, lo, hi) else none
  | .lt s2 hi, .ge s1 lo => if s1 == s2 then some (s1, lo, hi) else none
  | _, _ => none

/-- Extract `(signed, lo, hi)` for an `or` range check `(x < lo) || (hi ≤ x)` in either order. -/
def matchOrBounds {w : Nat} (b1 b2 : RangeBound w) : Option (Bool × BitVec w × BitVec w) :=
  match b1, b2 with
  | .lt s1 lo, .ge s2 hi => if s1 == s2 then some (s1, lo, hi) else none
  | .ge s2 hi, .lt s1 lo => if s1 == s2 then some (s1, lo, hi) else none
  | _, _ => none

/-! ## Local step descriptor (`ARStep`) and decision logic -/

/-- Outcome of lowering one `.let_` operation in `addrRangeSweep`. -/
inductive ARStep (V : Ty → Type) : List Ty → Type
  | elim {ts : List Ty} (res : Tup (ARVal V) ts) : ARStep V ts
  | emit1 {ts : List Ty} (op : Op V ts) (wrap : Tup V ts → Tup (ARVal V) ts) : ARStep V ts
  | rangeSubCmp (w : Nat) (o : CmpOp) (x : Arg V (.bits w)) (lo width : BitVec w)
      (outD : Nat) : ARStep V [.bool]
  | addrShl (n : Nat) (isSub : Bool) (base inv iv : Arg V (.bits n))
      (ivD sh : Nat) (hsh : sh < n) (disp : BitVec n) : ARStep V [.bits n]
  | addrPlain (n : Nat) (isSub : Bool) (base inv iv : Arg V (.bits n))
      (invD ivD : Nat) (disp : BitVec n) : ARStep V [.bits n]

/-- Try reassociating `base + off` where `base` is a variable and `off` has `AddrDef` provenance
whose invariant term and `base` both have strictly smaller loop depth than the variant term. -/
def tryAddrReassocOne {V : Ty → Type} {n : Nat}
    (base off : Arg (ARVal V) (.bits n)) : Option (ARStep V [.bits n]) :=
  if base.arOut.imm?.isSome then none
  else
    let bd := base.arDepth
    match off.arProv.addr? with
    | some (.shlAddVV x dx y dy sh hsh disp) =>
      if Nat.blt (Nat.max bd dx) dy then
        some (.addrShl n false base.arOut x y dy sh hsh disp)
      else if Nat.blt (Nat.max bd dy) dx then
        some (.addrShl n false base.arOut y x dx sh hsh disp)
      else none
    | some (.shlSubVV x dx y dy sh hsh disp) =>
      if Nat.blt (Nat.max bd dy) dx then
        some (.addrShl n true base.arOut y x dx sh hsh disp)
      else none
    | some (.addVV x dx y dy disp) =>
      if Nat.blt (Nat.max bd dx) dy then
        some (.addrPlain n false base.arOut x y (Nat.max bd dx) dy disp)
      else if Nat.blt (Nat.max bd dy) dx then
        some (.addrPlain n false base.arOut y x (Nat.max bd dy) dx disp)
      else none
    | some (.subVV x dx y dy disp) =>
      if Nat.blt (Nat.max bd dy) dx then
        some (.addrPlain n true base.arOut y x (Nat.max bd dy) dx disp)
      else none
    | some (.addVC _ _ _) | some (.shlVC _ _ _ _ _) | none => none

/-- Try collapsing `.and .bool` or `.or .bool` on two same-operand immediate comparisons into a
single unsigned range check (or constant bool). -/
def tryRangeStep {V : Ty → Type} (isOr : Bool) (outD next : Nat)
    (a b : Arg (ARVal V) .bool) : Option (ARStep V [.bool]) :=
  match a.arProv, b.arProv with
  | some c1, some c2 =>
    if hw : c1.w = c2.w then
      let lhs2Key : FKey (.bits c1.w) := hw ▸ c2.lhsKey
      let imm2 : BitVec c1.w := hw ▸ c2.imm
      if fKeyBeq c1.lhsKey lhs2Key then
        match toRangeBound c1.op c1.imm, toRangeBound c2.op imm2 with
        | some b1, some b2 =>
          match if isOr then matchOrBounds b1 b2 else matchAndBounds b1 b2 with
          | some (signed, lo, hi) =>
            let isLt := if signed then lo.slt hi else lo.ult hi
            if !isLt then
              some (.elim (ARVal.ofImm isOr, ()))
            else
              let cmpOp : CmpOp := if isOr then .uge else .ult
              if lo == 0#c1.w then
                some (.emit1 (op2 (.cmp cmpOp (.bits c1.w)) c1.lhs (.imm hi))
                  fun (r, ()) => (ARVal.fresh r next outD, ()))
              else
                some (.rangeSubCmp c1.w cmpOp c1.lhs lo (hi - lo) outD)
          | none => none
        | _, _ => none
      else none
    else none
  | _, _ => none

/-- Shift the constant displacement of an `AddrDef` by `c`. -/
def AddrDef.shiftDisp {V : Ty → Type} {n : Nat} (c : BitVec n) : AddrDef V n → AddrDef V n
  | .addVC x dx d => .addVC x dx (d + c)
  | .shlVC x dx sh hsh d => .shlVC x dx sh hsh (d + c)
  | .addVV x dx y dy d => .addVV x dx y dy (d + c)
  | .subVV x dx y dy d => .subVV x dx y dy (d + c)
  | .shlAddVV x dx y dy sh hsh d => .shlAddVV x dx y dy sh hsh (d + c)
  | .shlSubVV x dx y dy sh hsh d => .shlSubVV x dx y dy sh hsh (d + c)

/-- Record `AddrDef` provenance on a kept `.add (.bits n)` operation (populated for `n = 64`). -/
def recordAddProv {V : Ty → Type} {n : Nat}
    (a b : Arg (ARVal V) (.bits n)) : Option (AddrDef V n) :=
  if n != 64 then none
  else match a.arOut.imm?, b.arOut.imm? with
  | none, none =>
    match a.arProv.addr?, b.arProv.addr? with
    | some (.addVC x dx d1), some (.addVC y dy d2) => some (.addVV x dx y dy (d1 + d2))
    | some (.addVC x dx d1), _ => some (.addVV x dx b.arOut b.arDepth d1)
    | _, some (.addVC y dy d2) => some (.addVV a.arOut a.arDepth y dy d2)
    | some (.shlVC x dx sh1 hsh1 d1), some (.shlVC y dy sh2 _ d2) =>
      if sh1 == sh2 then some (.shlAddVV x dx y dy sh1 hsh1 (d1 + d2))
      else some (.addVV a.arOut a.arDepth b.arOut b.arDepth 0#n)
    | _, _ => some (.addVV a.arOut a.arDepth b.arOut b.arDepth 0#n)
  | none, some c =>
    match a.arProv.addr? with
    | some ad => some (ad.shiftDisp c)
    | none => some (.addVC a.arOut a.arDepth c)
  | some c, none =>
    match b.arProv.addr? with
    | some ad => some (ad.shiftDisp c)
    | none => some (.addVC b.arOut b.arDepth c)
  | some _, some _ => none

/-- Record `AddrDef` provenance on a kept `.sub (.bits n)` operation (populated for `n = 64`). -/
def recordSubProv {V : Ty → Type} {n : Nat}
    (a b : Arg (ARVal V) (.bits n)) : Option (AddrDef V n) :=
  if n != 64 then none
  else match a.arOut.imm?, b.arOut.imm? with
  | none, none =>
    match a.arProv.addr?, b.arProv.addr? with
    | some (.addVC x dx d1), some (.addVC y dy d2) => some (.subVV x dx y dy (d1 - d2))
    | some (.addVC x dx d1), _ => some (.subVV x dx b.arOut b.arDepth d1)
    | _, some (.addVC y dy d2) => some (.subVV a.arOut a.arDepth y dy (-d2))
    | some (.shlVC x dx sh1 hsh1 d1), some (.shlVC y dy sh2 _ d2) =>
      if sh1 == sh2 then some (.shlSubVV x dx y dy sh1 hsh1 (d1 - d2))
      else some (.subVV a.arOut a.arDepth b.arOut b.arDepth 0#n)
    | _, _ => some (.subVV a.arOut a.arDepth b.arOut b.arDepth 0#n)
  | none, some c =>
    match a.arProv.addr? with
    | some ad => some (ad.shiftDisp (-c))
    | none => some (.addVC a.arOut a.arDepth (-c))
  | _, _ => none

/-- Record `AddrDef` provenance on a kept `.shl (.bits n)` operation (populated for `n = 64`). -/
def recordShlProv {V : Ty → Type} {n : Nat}
    (a b : Arg (ARVal V) (.bits n)) : Option (AddrDef V n) :=
  if n != 64 then none
  else match b.arOut.imm? with
  | some k =>
    let kn := k.toNat
    if hkn : 0 < kn ∧ kn < n then
      match a.arProv.addr? with
      | some (.addVC x dx d) => some (.shlVC x dx kn hkn.2 (d <<< kn))
      | some (.shlVC x dx sh _ d) =>
        if hsum : sh + kn < n then some (.shlVC x dx (sh + kn) hsum (d <<< kn))
        else none
      | some (.addVV x dx y dy d) => some (.shlAddVV x dx y dy kn hkn.2 (d <<< kn))
      | some (.subVV x dx y dy d) => some (.shlSubVV x dx y dy kn hkn.2 (d <<< kn))
      | some (.shlAddVV x dx y dy sh _ d) =>
        if hsum : sh + kn < n then some (.shlAddVV x dx y dy (sh + kn) hsum (d <<< kn))
        else none
      | some (.shlSubVV x dx y dy sh _ d) =>
        if hsum : sh + kn < n then some (.shlSubVV x dx y dy (sh + kn) hsum (d <<< kn))
        else none
      | none => some (.shlVC a.arOut a.arDepth kn hkn.2 0#n)
    else none
  | none => none

/-- True iff `o` is a signed comparison (`slt`, `sle`, `sgt`, `sge`). -/
def arCmpIsSigned : CmpOp → Bool
  | .slt | .sle | .sgt | .sge => true
  | _ => false

/-- Convert signed comparison opcodes to unsigned counterparts, leaving `eq`/`ne`/unsigned as-is. -/
def arCmpToUnsigned : CmpOp → CmpOp
  | .slt => .ult | .sle => .ule | .sgt => .ugt | .sge => .uge | o => o

/-- Record `ZextDef` provenance on a kept `.zext m n` operation when `0 < m < n`. -/
def recordZextProv {V : Ty → Type} (m n : Nat) (a : Arg (ARVal V) (.bits m)) : BitsProv V n :=
  if h : 0 < m ∧ m < n then
    match a.arProv.zext? with
    | some zd =>
      { zext? := some ⟨zd.m, zd.hm0, Nat.lt_trans zd.hmn h.2, zd.src, zd.srcKey⟩ }
    | none =>
      { zext? := some ⟨m, h.1, h.2, a.arOut, a.arKey⟩ }
  else {}

/-- Build `CmpImmDef` for `a o c`, narrowing through `ZextDef` when `c` fits in `zd.m` bits. -/
def mkCmpImmFromArg {V : Ty → Type} {n : Nat} (o : CmpOp)
    (a : Arg (ARVal V) (.bits n)) (c : BitVec n) : CmpImmDef V :=
  match a.arProv.zext? with
  | some zd =>
    let c' := c.setWidth zd.m
    if c'.setWidth n == c then
      let o' := if arCmpIsSigned o then arCmpToUnsigned o else o
      ⟨zd.m, o', zd.src, zd.srcKey, c'⟩
    else ⟨n, o, a.arOut, a.arKey, c⟩
  | none => ⟨n, o, a.arOut, a.arKey, c⟩

/-- Record `CmpImmDef` provenance on a kept `.cmp o (.bits w)` operation. -/
def recordCmpImmProv {V : Ty → Type} {w : Nat} (o : CmpOp)
    (a b : Arg (ARVal V) (.bits w)) : Option (CmpImmDef V) :=
  match a.arOut.imm?, b.arOut.imm? with
  | _, some c => some (mkCmpImmFromArg o a c)
  | some c, none => some (mkCmpImmFromArg o.swap b c)
  | none, none => none

/-- Wrap the result(s) of a kept `.let_` operation into `ARVal V`s, recording provenance. -/
def wrapKept {V : Ty → Type} (outD next : Nat) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg (ARVal V)) sig) (xs : Tup V ts) : Tup (ARVal V) ts :=
  match code, args, xs with
  | .add (.bits _), (a, b, ()), (r, ()) =>
    (⟨.var r, .var next, outD, { addr? := recordAddProv a b }⟩, ())
  | .sub (.bits _), (a, b, ()), (r, ()) =>
    (⟨.var r, .var next, outD, { addr? := recordSubProv a b }⟩, ())
  | .shl (.bits _), (a, b, ()), (r, ()) =>
    (⟨.var r, .var next, outD, { addr? := recordShlProv a b }⟩, ())
  | .zext m _, (a, ()), (r, ()) =>
    (⟨.var r, .var next, outD, recordZextProv m _ a⟩, ())
  | .copy (.bits _), (a, ()), (r, ()) =>
    (⟨.var r, .var next, outD, a.arProv⟩, ())
  | .cmp o (.bits _) .bool _, (a, b, ()), (r, ()) =>
    (⟨.var r, .var next, outD, recordCmpImmProv o a b⟩, ())
  | .not .bool, (a, ()), (r, ()) =>
    (⟨.var r, .var next, outD,
      a.arProv.map fun cm => ⟨cm.w, cm.op.neg, cm.lhs, cm.lhsKey, cm.imm⟩⟩, ())
  | .copy .bool, (a, ()), (r, ()) =>
    (⟨.var r, .var next, outD, a.arProv⟩, ())
  | _, _, xs => freshARVals outD ts xs next

/-- Decide the lowering step for one `.let_` operation at loop depth `curD`. -/
def Op.arStep {V : Ty → Type} {ts : List Ty} (curD next : Nat) (op : Op (ARVal V) ts) :
    ARStep V ts :=
  let outD := if op.code.isLicmPure then tupMaxDepth op.args else curD
  let ⟨code, args⟩ := op
  match code, args with
  | .add (.bits n), (a, b, ()) =>
    if n == 64 && 0 < curD then
      match tryAddrReassocOne a b with
      | some st => st
      | none =>
        match tryAddrReassocOne b a with
        | some st => st
        | none => .emit1 ⟨.add (.bits n), tupArOut (a, b, ())⟩
            (wrapKept outD next (.add (.bits n)) (a, b, ()))
    else
      .emit1 ⟨.add (.bits n), tupArOut (a, b, ())⟩
        (wrapKept outD next (.add (.bits n)) (a, b, ()))
  | .and .bool, (a, b, ()) =>
    if a.arOut.imm? == some false || b.arOut.imm? == some false then
      .elim (ARVal.ofImm false, ())
    else if a.arOut.imm? == some true then
      .elim (b.toARVal, ())
    else if b.arOut.imm? == some true then
      .elim (a.toARVal, ())
    else
      match tryRangeStep false outD next a b with
      | some st => st
      | none =>
        .emit1 (op2 (.and .bool) a.arOut b.arOut) (fun xs => freshARVals outD [.bool] xs next)
  | .or .bool, (a, b, ()) =>
    if a.arOut.imm? == some true || b.arOut.imm? == some true then
      .elim (ARVal.ofImm true, ())
    else if a.arOut.imm? == some false then
      .elim (b.toARVal, ())
    else if b.arOut.imm? == some false then
      .elim (a.toARVal, ())
    else
      match tryRangeStep true outD next a b with
      | some st => st
      | none =>
        .emit1 (op2 (.or .bool) a.arOut b.arOut) (fun xs => freshARVals outD [.bool] xs next)
  | code, args =>
    .emit1 ⟨code, tupArOut args⟩ (wrapKept outD next code args)

/-! ## Verified PHOAS sweep (`addrRangeSweep`) -/

mutual
/-- Verified linear PHOAS sweep performing loop-aware address reassociation and range-check
collapse under an untrusted `LoopTree`. -/
def addrRangeSweep {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (curD next : Nat) (plan : LoopTree) : Expr (ARVal V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    let kPlan := plan.step1
    let foldD := plan.foldDisp
    match op.arStep curD next with
    | .elim res => addrRangeSweep curD next kPlan (k res)
    | .emit1 op' wrap =>
      .let_ op' fun xs => addrRangeSweep curD (next + ts.length) kPlan (k (wrap xs))
    | .rangeSubCmp w o x lo width outD =>
      .let_ (op2 (.sub (.bits w)) x (.imm lo)) fun (t, ()) =>
      .let_ (op2 (.cmp o (.bits w)) (.var t) (.imm width)) fun (r, ()) =>
      addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh r next outD, ()))
    | .addrShl n isSub base inv iv ivD sh _ disp =>
      .let_ (op2 (.shl (.bits n)) inv (.imm (BitVec.ofNat n sh))) fun (t1, ()) =>
      .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base (.var t1)) fun (t2, ()) =>
      if disp == 0#n then
        .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
        addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t4 next ivD, ()))
      else if foldD then
        .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t2d, ()) =>
        .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t2d) (.var t3)) fun (t4, ()) =>
        addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t4 next ivD, ()))
      else
        .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t4) (.imm disp)) fun (t5, ()) =>
        addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t5 next ivD, ()))
    | .addrPlain n isSub base inv iv invD ivD disp =>
      .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base inv) fun (t1, ()) =>
      if disp == 0#n then
        .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
        addrRangeSweep curD (next + 1) kPlan
          (k (⟨.var t2, .var next, ivD, { addr? := some (.addVV (.var t1) invD iv ivD 0#n) }⟩, ()))
      else if foldD then
        .let_ (op2 (.add (.bits n)) (.var t1) (.imm disp)) fun (t1d, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t1d) iv) fun (t2, ()) =>
        addrRangeSweep curD (next + 1) kPlan
          (k (⟨.var t2, .var next, ivD, { addr? := some (.addVV (.var t1d) invD iv ivD 0#n) }⟩, ()))
      else
        .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t3, ()) =>
        addrRangeSweep curD (next + 1) kPlan
          (k (⟨.var t3, .var next, ivD, { addr? := some (.addVV (.var t1) invD iv ivD disp) }⟩, ()))
  | .load t a k =>
    .load t a.arOut fun v => addrRangeSweep curD (next + 1) plan.step1 (k (ARVal.fresh v next curD))
  | .store v a k =>
    .store v.arOut a.arOut (addrRangeSweep curD next plan.step1 k)
  | .call f (bs := bs) args k =>
    .call f (tupArOut args) fun xs =>
      addrRangeSweep curD (next + bs.length) plan.step1 (k (freshARVals curD bs xs next))
  | .jnz c t e =>
    let (pt, pe) := plan.step2
    match c.arOut with
    | .imm true => addrRangeSweep curD next pt t
    | .imm false => addrRangeSweep curD next pe e
    | .var v => .jnz (.var v) (addrRangeSweep curD next pt t) (addrRangeSweep curD next pe e)
  | .jump j args => .jump j (tupArOut args)
  | .ret vs => .ret (tupArOut vs)
  | .exit f args => .exit f (tupArOut args)
  | .hlt => .hlt
  | .group bodies k =>
    let (bsPlan, kPlan) := plan.stepGroup
    .group
      (fun Js => addrRangeSweepB curD next bsPlan (bodies Js))
      (fun Js => addrRangeSweep curD next kPlan (k Js))

/-- Block-list companion of `addrRangeSweep`. -/
def addrRangeSweepB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (curD next : Nat) (bsPlan : LoopBlocks) :
    {sig : List (List Ty)} → Blocks (ARVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    let (isL, ph, pt) := bsPlan.stepCons
    let bd := if isL then curD + 1 else curD
    .cons (fun xs => addrRangeSweep bd (next + ts.length) ph (b (freshARVals bd ts xs next)))
      (addrRangeSweepB curD next pt bs)
end

/-- Run loop-aware address reassociation and range-check collapse on a closed function `Func`,
folding unique non-zero constant displacements into hoisted base pointers when `foldDisp` is
`true` and bypassing the PHOAS sweep when no candidate sites exist. -/
def Func.addrRangeOptWith (foldDisp : Bool) {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let (plan, hasWork) := AddrRangeOpt.buildAddrPlan foldDisp as.length (reifyFunc f)
  if hasWork then
    fun V L xs => addrRangeSweep 0 as.length plan (f (ARVal V) L (freshARVals 0 as xs 0))
  else
    f

/-- Run `Func.addrRangeOptWith false` (target-neutral default preserving x86-64 SIB
displacements). -/
def Func.addrRangeOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.addrRangeOptWith false f

end LeanQbe.T
