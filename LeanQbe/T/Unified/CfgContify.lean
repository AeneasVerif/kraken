module

public import LeanQbe.T.Unified.CfgRecovery

/-!
# Stage-1 Witness-Checked CFG Recovery, Contification & Private Frame Promotion
(`Unified.CfgContify`)

Extends Stage-0 `Unified.CfgRecovery` additively (`0` edits to `CfgRecovery*`) with:
* Nested Bourdoncle WTO `GroupTree` loops (`buildNestedLoopTree`) and verification.
* Private stack-slot promotion (`PrivFrameCfg`: `[sp₀ - 8*nSlots, sp₀)` -> SSA virtuals) in both
  static `FrameDisj` (`dynAliasGuard = false`, rejecting unguarded potential aliases) and
  zero-assumption dynamic alias-guard mode (`dynAliasGuard = true`, emitting runtime range
  checks + `flushFrame` + unpromoted tail fallback).
* Single-return (`rp`) and dual-return (`rp + 8`, `Ex 2b`) contification with `callM`-style
  stack-slot promotion (`blockNoMem` callees leave promoted slots live across `.call`).
* Untrusted heuristic `analyzeContify : CodeMap → Option ContifyWitness`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.BedrockWord

/-! ## §1. Stage-1 Witness Types & Frame Geometry -/

@[expose] section
/-- Private stack-frame promotion settings for `[sp₀ - 8*numSlots, sp₀)`. -/
structure PrivFrameCfg : Type where
  numSlots      : Nat := 0
  dynAliasGuard : Bool := false
  deriving DecidableEq, Repr
end

/-- Stage-1 region witness adding `PrivFrameCfg` on top of Stage-0 `RegionWitness`. -/
structure ContifyRegion : Type where
  name            : Sym
  entryPc         : BitVec 64
  abi             : RegionAbi
  privFrame       : PrivFrameCfg := {}
  tree            : List GroupTree
  edges           : List EdgeWitness
  retainFallbacks : Bool := true

/-- All block addresses owned by a `ContifyRegion`. -/
@[expose] def ContifyRegion.allPcs (cr : ContifyRegion) : List (BitVec 64) :=
  cr.tree.flatMap GroupTree.allPcs

/-- Forget `privFrame` to view `cr` as a Stage-0 `RegionWitness`. -/
@[expose] def ContifyRegion.toRegionWitness (cr : ContifyRegion) : RegionWitness where
  name            := cr.name
  entryPc         := cr.entryPc
  abi             := cr.abi
  tree            := cr.tree
  edges           := cr.edges
  retainFallbacks := cr.retainFallbacks

/-- Whole-program Stage-1 recovery witness ordered callees-first. -/
structure ContifyWitness : Type where
  regions : List ContifyRegion

/-- Virtualized 64-bit byte address of promoted private stack slot `k` (`sp₀ - 8*(k+1)`). -/
@[expose] def slotAddr (sp₀ : BitVec 64) (k : Nat) : BitVec 64 :=
  sp₀ - BitVec.ofNat 64 (8 * (k + 1))

/-- Region-internal boundary signature: `6` regs, plus `(sp₀, slot₀..slot_{nSlots-1})`. -/
@[expose] def contSig (nSlots : Nat) : List Ty :=
  if nSlots = 0 then regSig else regSig ++ List.replicate (nSlots + 1) i64

/-- Initial de Bruijn type context at every internal label of an `nSlots`-slot region. -/
@[expose] def contCtx (nSlots : Nat) : List Ty :=
  pushTypes (contSig nSlots) []

@[expose] def blockNoMem : BlockFlat → Bool
  | .let_ _ k => blockNoMem k
  | .load _ _ _ => false
  | .store _ _ _ => false
  | .codeAddr _ k => blockNoMem k
  | .jnz _ t e => blockNoMem t && blockNoMem e
  | .ijmp _ _ => true
  | .halt _ => false
  | .hlt => true

@[expose] section
/-- Stage-1 callee metadata extending Stage-0 `CalleeMeta` with `memFree` tracking. -/
structure ContCalleeMeta : Type where
  name    : Sym
  entryPc : BitVec 64
  dualRet : Bool
  memFree : Bool
  deriving DecidableEq, Repr
end

/-! ## §2. Extended Symbolic Evaluator (`ContSymVal`: `spOffset` + `PrivFrame`) -/

@[expose] section
/-- Symbolic abstraction tracking `sp₀ + off`, `rp₀ + off`, aligned tags, `select`, and
strides. -/
inductive ContSymVal : Type
  | spOffset (off : BitVec 64)
  | rpOffset (off : BitVec 64)
  | const (w : BitVec 64)
  | alignedConst (w : BitVec 64)
  | taggedAligned (w tag : BitVec 64)
  | shl3 (idxLvl : Nat)
  | stride (base : BitVec 64) (idxLvl : Nat)
  | ite (condLvl : Nat) (tVal eVal : ContSymVal)
  | boolConst (b : Bool)
  | cmpUlt (lhsLvl : Nat) (bound : BitVec 64)
  | top
  deriving DecidableEq, Repr
end

/-- Forward symbolic state for Stage-1 `BlockFlat` checking and slot promotion. -/
structure ContSymState : Type where
  env   : List ContSymVal
  ctx   : List Ty
  facts : List SymFact
  deriving DecidableEq, Repr

/-- Convert Stage-1 `ContSymVal` to Stage-0 `SymVal` (mapping `.spOffset` to `.top`). -/
@[expose] def ContSymVal.toSymVal : ContSymVal → SymVal
  | .spOffset _ => .top
  | .rpOffset o => .rpOffset o
  | .const w => .const w
  | .alignedConst w => .alignedConst w
  | .taggedAligned w t => .taggedAligned w t
  | .shl3 l => .shl3 l
  | .stride b l => .stride b l
  | .ite c t e => .ite c t.toSymVal e.toSymVal
  | .boolConst b => .boolConst b
  | .cmpUlt l b => .cmpUlt l b
  | .top => .top

/-- Convert `ContSymState` into Stage-0 `SymState` for Stage-0 edge reuse. -/
@[expose] def ContSymState.toSymState (st : ContSymState) : SymState where
  env := st.env.map ContSymVal.toSymVal
  ctx := st.ctx
  facts := st.facts

/-- Initial symbolic state: `sp` at level `0` has `.spOffset 0#64`, `rp` at level `1` has
`.rpOffset 0#64`, remaining regs are `.top` (`ctx = regCtx`). -/
@[expose] def ContSymState.init : ContSymState where
  env := [.top, .top, .top, .top, .rpOffset 0#64, .spOffset 0#64]
  ctx := regCtx
  facts := []

/-- Look up a symbolic value by `BlockFlat` de Bruijn index (`0` = head). -/
@[expose] def ContSymState.getSym (st : ContSymState) (idx : Nat) : ContSymVal :=
  match listGet? st.env idx with
  | some v => v
  | none => .top

/-- Evaluate a typed `Arg K t` in `st`. -/
@[expose] def ContSymState.evalArg (st : ContSymState) {t : Ty} : Arg K t → ContSymVal
  | .var idx => st.getSym idx
  | .imm c =>
      match t with
      | .bool => .boolConst c
      | .bits 64 => .const c
      | _ => .top

/-- Extract constant 64-bit value from `ContSymVal`. -/
@[expose] def ContSymVal.asConst? : ContSymVal → Option (BitVec 64)
  | .const w => some w
  | .alignedConst w => some w
  | _ => none

/-- Extract known constant from `Arg K i64`. -/
@[expose] def ContSymState.resolveConst (st : ContSymState) (a : Arg K i64) : Option (BitVec 64) :=
  (st.evalArg a).asConst?

/-- Convert `idx < st.env.length` to immutable level. -/
@[expose] def ContSymState.toLevel? (st : ContSymState) (idx : Nat) : Option Nat :=
  if idx < st.env.length then some (st.env.length - 1 - idx) else none

/-- Check `lvl` has exact type `t`. -/
@[expose] def ContSymState.levelHasTy (st : ContSymState) (lvl : Nat) (t : Ty) : Bool :=
  if lvl < st.ctx.length then
    match listGet? st.ctx (st.ctx.length - 1 - lvl) with
    | some t' => match tyDecEq t' t with | isTrue _ => true | isFalse _ => false
    | none => false
  else false

/-- Push operation outputs onto `ContSymState`. -/
@[expose] def ContSymState.pushRes (st : ContSymState) (ts : List Ty) (svs : List ContSymVal) :
    ContSymState :=
  { env := svs ++ st.env
    ctx := pushTypes ts st.ctx
    facts := st.facts }

@[expose] def contMkAdd (x y : ContSymVal) : ContSymVal :=
  match x, y with
  | .spOffset o, .const c => .spOffset (o + c)
  | .const c, .spOffset o => .spOffset (o + c)
  | .rpOffset o, .const c => .rpOffset (o + c)
  | .const c, .rpOffset o => .rpOffset (o + c)
  | .alignedConst base, .shl3 lvl => .stride base lvl
  | .const base, .shl3 lvl => .stride base lvl
  | .shl3 lvl, .alignedConst base => .stride base lvl
  | .shl3 lvl, .const base => .stride base lvl
  | _, _ =>
      match x.asConst?, y.asConst? with
      | some a, some b => .const (a + b)
      | _, _ => .top

@[expose] def contMkSub (x y : ContSymVal) : ContSymVal :=
  match x, y with
  | .spOffset o, .const c => .spOffset (o - c)
  | _, _ =>
      match x.asConst?, y.asConst? with
      | some a, some b => .const (a - b)
      | _, _ => .top

@[expose] def contMkOrTag (x y : ContSymVal) : ContSymVal :=
  match x, y with
  | .alignedConst w, .const tag =>
      if BitVec.ult tag 8#64 then .taggedAligned w tag else .const (w ||| tag)
  | .const tag, .alignedConst w =>
      if BitVec.ult tag 8#64 then .taggedAligned w tag else .const (tag ||| w)
  | .const a, .const b => .const (a ||| b)
  | _, _ => .top

@[expose] def contMkUntag (x y : ContSymVal) : ContSymVal :=
  match x, y with
  | .taggedAligned w _, .const m => if m == ~~~7#64 then .alignedConst w else .top
  | .const m, .taggedAligned w _ => if m == ~~~7#64 then .alignedConst w else .top
  | .const a, .const b => .const (a &&& b)
  | .alignedConst a, .const b => .const (a &&& b)
  | .const a, .alignedConst b => .const (a &&& b)
  | _, _ => .top

/-- Abstractly evaluate `OpCode` in `ContSymState`. -/
@[expose] def evalContOpCode (st : ContSymState) :
    {as ts : List Ty} → OpCode as ts → Tup (Arg K) as → List ContSymVal
  | _, _, .copy (.bits n), (a, ()) =>
      if n == 64 then [st.evalArg a] else [.top]
  | _, _, .copy .bool, (a, ()) => [st.evalArg a]
  | _, _, .not (.bits n), (a, ()) =>
      if n == 64 then
        match (st.evalArg a).asConst? with
        | some w => [.const (~~~w)]
        | none => [.top]
      else [.top]
  | _, _, .add (.bits n), (a, b, ()) =>
      if n == 64 then [contMkAdd (st.evalArg a) (st.evalArg b)] else [.top]
  | _, _, .sub (.bits n), (a, b, ()) =>
      if n == 64 then [contMkSub (st.evalArg a) (st.evalArg b)] else [.top]
  | _, _, .or (.bits n), (a, b, ()) =>
      if n == 64 then [contMkOrTag (st.evalArg a) (st.evalArg b)] else [.top]
  | _, _, .and (.bits n), (a, b, ()) =>
      if n == 64 then [contMkUntag (st.evalArg a) (st.evalArg b)] else [.top]
  | _, _, .shl (.bits n), (a, b, ()) =>
      if n == 64 then
        match a, (st.evalArg b).asConst? with
        | .var idx, some 3#64 =>
            match st.toLevel? idx with
            | some lvl => if st.levelHasTy lvl i64 then [.shl3 lvl] else [.top]
            | none => [.top]
        | _, _ => [.top]
      else [.top]
  | _, _, .mul (.bits n), (a, b, ()) =>
      if n == 64 then
        match a, (st.evalArg b).asConst?, (st.evalArg a).asConst?, b with
        | .var idx, some 8#64, _, _ =>
            match st.toLevel? idx with
            | some lvl => if st.levelHasTy lvl i64 then [.shl3 lvl] else [.top]
            | none => [.top]
        | _, _, some 8#64, .var idx =>
            match st.toLevel? idx with
            | some lvl => if st.levelHasTy lvl i64 then [.shl3 lvl] else [.top]
            | none => [.top]
        | _, some x, some y, _ => [.const (y * x)]
        | _, _, _, _ => [.top]
      else [.top]
  | _, _, .select (.bits n), (c, t, e, ()) =>
      if n == 64 then
        match c with
        | .imm true => [st.evalArg t]
        | .imm false => [st.evalArg e]
        | .var idx =>
            match st.toLevel? idx with
            | some lvl =>
                if st.levelHasTy lvl .bool then
                  [.ite lvl (st.evalArg t) (st.evalArg e)]
                else [.top]
            | none => [.top]
      else [.top]
  | _, _, .cmp .ult (.bits n), (a, b, ()) =>
      if n == 64 then
        match a, (st.evalArg b).asConst? with
        | .var idx, some bound =>
            match st.toLevel? idx with
            | some lvl => if st.levelHasTy lvl i64 then [.cmpUlt lvl bound] else [.top]
            | none => [.top]
        | _, _ => [.top]
      else [.top]
  | _, ts, _, _ => List.replicate ts.length .top

/-- Evaluate `Op K ts` symbolically in `ContSymState`. -/
@[expose] def evalContOp (st : ContSymState) {ts : List Ty} (op : Op K ts) : List ContSymVal :=
  evalContOpCode st op.code op.args

/-- Record branch condition fact down `.jnz`. -/
@[expose] def ContSymState.pushCondFact (st : ContSymState) (c : Arg K .bool) (taken : Bool) :
    ContSymState :=
  if taken then
    match c with
    | .var idx =>
        match st.getSym idx with
        | .cmpUlt lvl bound => { st with facts := .ultBound lvl bound :: st.facts }
        | _ => st
    | .imm _ => st
  else st

/-- Recognize promoted private stack slot `k < nSlots` (`sp₀ - 8*(k+1)`). -/
@[expose] def spSlotOf? (nSlots : Nat) (sv : ContSymVal) : Option Nat :=
  (List.range nSlots).find? fun k => sv == .spOffset (0#64 - BitVec.ofNat 64 (8 * (k + 1)))

/-- Statically recognize non-negative small stack-frame offsets (`sp₀ + [0..4096]`) with
`bytes ≤ 4096` proven disjoint from `[sp₀ - 8*nSlots, sp₀)` for `nSlots ≤ 64`. -/
@[expose] def isStaticOutsideFrame (nSlots bytes : Nat) (sv : ContSymVal) : Bool :=
  match sv with
  | .spOffset o => (nSlots ≤ 64) && (bytes ≤ 4096) && (o.toNat ≤ 4096)
  | _ => false

/-- Symbolic leaf collected by `symEvalContBlock`. -/
structure ContSymLeaf : Type where
  path     : BranchPath
  st       : ContSymState
  target   : Arg K i64
  nextRegs : RegsExpr K

/-- Walk `BlockFlat` symbolically while checking `PrivFrame` memory-access safety. -/
@[expose] def symEvalContBlock (cm : CodeMap) (pf : PrivFrameCfg) :
    BlockFlat → BranchPath → ContSymState → Option (List ContSymLeaf)
  | .let_ (ts := ts) op k, path, st =>
      symEvalContBlock cm pf k path (st.pushRes ts (evalContOp st op))
  | .load t a k, path, st =>
      let okMem :=
        if pf.numSlots == 0 then true
        else if t == i64 && (spSlotOf? pf.numSlots (st.evalArg a)).isSome then true
        else if isStaticOutsideFrame pf.numSlots t.bytes (st.evalArg a) then true
        else pf.dynAliasGuard && (t.bytes ≤ 16)
      if okMem then
        symEvalContBlock cm pf k path { st with env := .top :: st.env, ctx := t :: st.ctx }
      else none
  | .store (t := t) _ a k, path, st =>
      let okMem :=
        if pf.numSlots == 0 then true
        else if t == i64 && (spSlotOf? pf.numSlots (st.evalArg a)).isSome then true
        else if isStaticOutsideFrame pf.numSlots t.bytes (st.evalArg a) then true
        else pf.dynAliasGuard && (t.bytes ≤ 16)
      if okMem then symEvalContBlock cm pf k path st else none
  | .codeAddr sym k, path, st =>
      match cm.addrOf? sym with
      | some a =>
          let sv := if (a &&& 7#64) == 0#64 then .alignedConst a else .const a
          symEvalContBlock cm pf k path { st with env := sv :: st.env, ctx := i64 :: st.ctx }
      | none => none
  | .jnz c t e, path, st => do
      let lt ← symEvalContBlock cm pf t (path ++ [true]) (st.pushCondFact c true)
      let le ← symEvalContBlock cm pf e (path ++ [false]) (st.pushCondFact c false)
      some (lt ++ le)
  | .ijmp tgt nxt, path, st => some [⟨path, st, tgt, nxt⟩]
  | .halt _, _, _ => some []
  | .hlt, _, _ => none

/-! ## §3. Checked `ContifyRegion` & `ContifyWitness` -/

/-- Check edge witness `(leaf, kind)` under Stage-1 `abi`, `pf`, `pcs`, and `ContCalleeMeta`. -/
@[expose] def checkContEdgeLeaf (cm : CodeMap) (abi : RegionAbi) (pf : PrivFrameCfg)
    (callees : List ContCalleeMeta) (pcs : List (BitVec 64)) (leaf : ContSymLeaf)
    (kind : EdgeKind) : Bool :=
  match kind with
  | .memTableGuarded _ _ | .memTableRo _ _ _ => false
  | _ =>
  let st := leaf.st
  let stage0Ok :=
    checkEdgeLeaf cm abi (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩)
      pcs ⟨leaf.path, st.toSymState, leaf.target, leaf.nextRegs⟩ kind
  if !stage0Ok then false
  else
    let spOk :=
      if pf.numSlots == 0 then true
      else match kind with
        | .direct _ | .select _ _ | .strideTable _ _ _ | .guarded _ | .contCall _ _ _ _ _ =>
            st.evalArg leaf.nextRegs.sp == .spOffset 0#64
        | _ => true
    if !spOk then false
    else match kind with
    | .contCall callee calleePc _ _ _ =>
        if pf.numSlots == 0 then true
        else callees.any fun c =>
          (c.name == callee) && (c.entryPc == calleePc) && c.memFree
    | _ => true

/-- True iff every block inside `cr` has zero `Mem 64` ops or `.halt`, preserves `sp`, and
any `.contCall` targets a `memFree` callee in `callees`. -/
@[expose] def regionMemFree (cm : CodeMap) (callees : List ContCalleeMeta)
    (cr : ContifyRegion) : Bool :=
  cr.allPcs.all fun pc =>
    match cm.lookupAddr pc with
    | some b =>
        blockNoMem b &&
        match symEvalContBlock cm cr.privFrame b [] ContSymState.init with
        | some leaves =>
            leaves.all fun lf =>
              (lf.st.evalArg lf.nextRegs.sp == .spOffset 0#64) &&
              match cr.toRegionWitness.findEdge pc lf.path with
              | some ew =>
                  match ew.kind with
                  | .contCall callee calleePc _ _ _ =>
                      callees.any fun c =>
                        (c.name == callee) && (c.entryPc == calleePc) && c.memFree
                  | _ => true
              | none => false
        | none => false
    | none => false

/-- Convert a `ContifyRegion` into `ContCalleeMeta` if `cr.abi = .contified dualRet`. -/
@[expose] def ContifyRegion.toCalleeMeta? (cm : CodeMap) (callees : List ContCalleeMeta)
    (cr : ContifyRegion) : Option ContCalleeMeta :=
  match cr.abi with
  | .contified dualRet => some ⟨cr.name, cr.entryPc, dualRet, regionMemFree cm callees cr⟩
  | .retEnvelope => none

/-- Check all leaves of block `pc` inside `cr` with Stage-1 `symEvalContBlock`. -/
@[expose] def checkContBlockLeaves (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) (pcs : List (BitVec 64)) (pc : BitVec 64) : Bool :=
  match cm.lookupAddr pc with
  | none => false
  | some b =>
      b.wfCheck regCtx && b.noHlt &&
      match symEvalContBlock cm cr.privFrame b [] ContSymState.init with
      | none => false
      | some leaves =>
          leaves.all fun leaf =>
            match cr.toRegionWitness.findEdge pc leaf.path with
            | none => false
            | some ew => checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs leaf ew.kind

mutual
/-- Verify nested WTO scoping and Stage-1 edge soundness across `GroupTree` list. -/
@[expose] def checkContGroupNodes (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) (pcs : List (BitVec 64)) : List GroupTree → Bool
  | [] => true
  | g :: gs =>
      checkContGroupNode cm cr callees pcs g && checkContGroupNodes cm cr callees pcs gs

/-- Verify one `GroupTree` node inside `pcs`. -/
@[expose] def checkContGroupNode (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) (pcs : List (BitVec 64)) : GroupTree → Bool
  | .leaf pc => checkContBlockLeaves cm cr callees pcs pc
  | .loop header nodes =>
      let entries := nodes.map GroupTree.entryPc
      let pcsInner := pushLabelPcs entries pcs
      (!nodes.isEmpty) && entries.contains header &&
      checkContGroupNodes cm cr callees pcsInner nodes
end

/-! ## §4. Deterministic Stage-1 Lowering (`remapArg`, `PrivFrame` Scalarization & Bailout) -/

/-- Map a `BlockFlat` de Bruijn index to its `TFlat` index via `envMap` (list of `TFlat`
levels). -/
@[expose] def remapArg (depth : Nat) (envMap : List Nat) {t : Ty} : Arg K t → Arg K t
  | .var idx =>
      match listGet? envMap idx with
      | some lvl => .var (depth - 1 - lvl)
      | none => .var idx
  | .imm c => .imm c

/-- Remap a `Tup (Arg K) ts`. -/
@[expose] def remapArgs (depth : Nat) (envMap : List Nat) :
    {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => ()
  | _ :: _, (a, as) => (remapArg depth envMap a, remapArgs depth envMap as)

/-- Remap all 6 register expressions. -/
@[expose] def remapRegsExpr (depth : Nat) (envMap : List Nat) (e : RegsExpr K) : RegsExpr K :=
  ⟨remapArg depth envMap e.sp, remapArg depth envMap e.rp, remapArg depth envMap e.rv,
   remapArg depth envMap e.r1, remapArg depth envMap e.r2, remapArg depth envMap e.r3⟩

/-- Initial `envMap` for `BlockFlat` registers `r3..sp` (indices `0..5`) mapped to `TFlat` levels
`5..0`. Note `sp₀` and promoted slots live at `TFlat` levels `6 .. 6 + nSlots` above `5..0`. -/
@[expose] def initEnvMap : List Nat := [5, 4, 3, 2, 1, 0]

/-- Initial `TFlat` variable levels for promoted slots `0..nSlots-1` (`7 .. 6 + nSlots`). -/
@[expose] def initSlotsLvls (nSlots : Nat) : List Nat :=
  (List.range nSlots).map (· + 7)

/-- Prepend new `BlockFlat` binder levels `[d, ..., d + ts.length - 1]` to `envMap`. -/
@[expose] def pushEnvMap : List Ty → Nat → List Nat → List Nat
  | [], _, em => em
  | _ :: ts, d, em => pushEnvMap ts (d + 1) (d :: em)

/-- Build `Tup (Arg K)` for promoted slots from `sLvls`. -/
@[expose] def mkSlotArgs (depth : Nat) : (n : Nat) → List Nat → Tup (Arg K) (List.replicate n i64)
  | 0, _ => ()
  | n + 1, [] => (.imm 0#64, mkSlotArgs depth n [])
  | n + 1, l :: ls => (.var (depth - 1 - l), mkSlotArgs depth n ls)

/-- Build register + optional `(sp₀, slot₀..slot_{nSlots-1})` tuple args for internal `.jump`. -/
@[expose] def mkJumpTuple (depth sp0Lvl : Nat) (nxt : RegsExpr K) :
    (nSlots : Nat) → (sLvls : List Nat) → Tup (Arg K) (contSig nSlots)
  | 0, _ => nxt.toTup
  | n + 1, sLvls =>
      tupAppend nxt.toTup (.var (depth - 1 - sp0Lvl), mkSlotArgs depth (n + 1) sLvls)

/-- Base entry tuple for a `GroupTree` node (`depth = contSig.length`, `sp0Lvl = 6`). -/
@[expose] def baseContArgs (nSlots : Nat) : Tup (Arg K) (contSig nSlots) :=
  let depth := if nSlots = 0 then 6 else 7 + nSlots
  let rBase : RegsExpr K := ⟨.var (depth - 1 - 0), .var (depth - 1 - 1), .var (depth - 1 - 2),
    .var (depth - 1 - 3), .var (depth - 1 - 4), .var (depth - 1 - 5)⟩
  mkJumpTuple depth 6 rBase nSlots (initSlotsLvls nSlots)

/-- Lower an internal jump with `nSlots`-slot arguments to `targetPc` in `pcs`. -/
@[expose] def lowerContJumpTo {rs : List Ty} (nSlots : Nat) (pcs : List (BitVec 64))
    (targetPc : BitVec 64) (args : Tup (Arg K) (contSig nSlots)) : TFlat rs :=
  match findLabelIdx pcs targetPc with
  | some j => .jump (ts := contSig nSlots) j args
  | none => .hlt

/-- Shift all variable indices in `Tup (Arg K) ts` outward by `k`. -/
@[expose] def shiftArgTup (k : Nat) : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => ()
  | _ :: _, (a, as) => (shiftArg k a, shiftArgTup k as)

/-- Lower stride cascade passing full `(nxt, sp₀, slots)` jump arguments. -/
@[expose] def lowerContStride {rs : List Ty} (nSlots : Nat) (pcs : List (BitVec 64))
    (idxVar : Nat) (args : Tup (Arg K) (contSig nSlots)) :
    Nat → Nat → List (BitVec 64) → TFlat rs
  | _, _, [] => .hlt
  | _, curShift, [lastPc] => lowerContJumpTo nSlots pcs lastPc (shiftArgTup curShift args)
  | k, curShift, tPc :: rest =>
      let eqOp : Op K [.bool] := op2 (.cmp .eq i64) (.var (idxVar + curShift))
        (.imm (BitVec.ofNat 64 k))
      .let_ eqOp
        (.jnz (.var 0)
          (lowerContJumpTo nSlots pcs tPc (shiftArgTup (curShift + 1) args))
          (lowerContStride nSlots pcs idxVar args (k + 1) (curShift + 1) rest))

/-- Flush promoted private slots `sLvls` back into `[sp₀ - 8*(k+1)]` before `kCont`. -/
@[expose] def flushFrameAux {rs : List Ty} (sp0Lvl : Nat) (k : Nat) :
    List Nat → Nat → TFlat rs → TFlat rs
  | [], _, kCont => kCont
  | sLvl :: rest, depth, kCont =>
      let addrOp : Op K [i64] :=
        op2 (.sub i64) (.var (depth - 1 - sp0Lvl)) (.imm (BitVec.ofNat 64 (8 * (k + 1))))
      .let_ addrOp
        (.store (t := i64) (.var (depth + 1 - 1 - sLvl)) (.var 0)
          (flushFrameAux sp0Lvl (k + 1) rest (depth + 1) kCont))

/-- Flush `nSlots` slots (`0..nSlots-1`), invoking `kCont (depth + sLvls.length)`. -/
@[expose] def flushFrame {rs : List Ty} (sp0Lvl : Nat) (sLvls : List Nat) (depth : Nat)
    (kCont : Nat → TFlat rs) : TFlat rs :=
  flushFrameAux sp0Lvl 0 sLvls depth (kCont (depth + sLvls.length))

/-- Lower speculative `guarded` cascade, flushing `sLvls` before cold `.ret` bailout. -/
@[expose] def lowerContGuarded (nSlots sp0Lvl : Nat) (sLvls : List Nat)
    (pcs : List (BitVec 64)) (tgt : Arg K i64) (nxt : RegsExpr K) (depth : Nat) :
    Nat → List (BitVec 64) → TFlat RegionAbi.retEnvelope.retSig
  | curShift, [] =>
      flushFrame sp0Lvl sLvls (depth + curShift) fun _ =>
        mkRetEnvelope (shiftArg (curShift + sLvls.length) tgt)
          (shiftRegsExpr (curShift + sLvls.length) nxt)
  | curShift, hPc :: rest =>
      let eqOp : Op K [.bool] := op2 (.cmp .eq i64) (shiftArg curShift tgt) (.imm hPc)
      let jArgs := mkJumpTuple (depth + curShift + 1) sp0Lvl
        (shiftRegsExpr (curShift + 1) nxt) nSlots sLvls
      .let_ eqOp
        (.jnz (.var 0)
          (lowerContJumpTo nSlots pcs hPc jArgs)
          (lowerContGuarded nSlots sp0Lvl sLvls pcs tgt nxt depth (curShift + 1) rest))

/-- Unpromoted tail lowering after `flushFrame` (resolving `codeAddr sym` through `cm`). -/
@[expose] def lowerUnpromotedTail (cm : CodeMap) :
    BlockFlat → Nat → List Nat → TFlat RegionAbi.retEnvelope.retSig
  | .let_ (ts := ts) op k, d, em =>
      .let_ ⟨op.code, remapArgs d em op.args⟩
        (lowerUnpromotedTail cm k (d + ts.length) (pushEnvMap ts d em))
  | .load t a k, d, em =>
      .load t (remapArg d em a) (lowerUnpromotedTail cm k (d + 1) (d :: em))
  | .store v a k, d, em =>
      .store (remapArg d em v) (remapArg d em a) (lowerUnpromotedTail cm k d em)
  | .codeAddr sym k, d, em =>
      match cm.addrOf? sym with
      | some a =>
          .let_ (op1 (.copy i64) (.imm a))
            (lowerUnpromotedTail cm k (d + 1) (d :: em))
      | none => .hlt
  | .jnz c t e, d, em =>
      .jnz (remapArg d em c) (lowerUnpromotedTail cm t d em) (lowerUnpromotedTail cm e d em)
  | .ijmp tgt nxt, d, em => mkRetEnvelope (remapArg d em tgt) (remapRegsExpr d em nxt)
  | .halt c, d, em => .exit haltSym (as := [i64]) (remapArg d em c, ())
  | .hlt, _, _ => .hlt

/-- Emit 5-let runtime disjointness check `8*nSlots ≤ a - lo ∧ a - lo ≤ 2^64 - bytes`. -/
@[expose] def emitAliasGuard {rs : List Ty} (sp0Lvl nSlots d : Nat) (aTflat : Arg K i64)
    (bytes : Nat) (tBranch fBranch : TFlat rs) : TFlat rs :=
  let loOp : Op K [i64] :=
    op2 (.sub i64) (.var (d - 1 - sp0Lvl)) (.imm (BitVec.ofNat 64 (8 * nSlots)))
  let distOp : Op K [i64] := op2 (.sub i64) (shiftArg 1 aTflat) (.var 0)
  let c1Op : Op K [.bool] :=
    op2 (.cmp .ule i64) (.imm (BitVec.ofNat 64 (8 * nSlots))) (.var 0)
  let c2Op : Op K [.bool] :=
    op2 (.cmp .ule i64) (.var 1) (.imm (BitVec.ofNat 64 (2 ^ 64 - bytes)))
  let okOp : Op K [.bool] := op2 (.and .bool) (.var 1) (.var 0)
  .let_ loOp <| .let_ distOp <| .let_ c1Op <| .let_ c2Op <| .let_ okOp <|
    .jnz (.var 0) tBranch fBranch

/-- Lower a Stage-1 edge leaf carrying explicit `envMap` so `select`/`strideTable` look up exact
`TFlat` levels from `ContSymState` levels cleanly. -/
@[expose] def liftContEdgeMapped (abi : RegionAbi) (nSlots sp0Lvl : Nat) (sLvls : List Nat)
    (pcs : List (BitVec 64)) (st : ContSymState) (d : Nat) (em : List Nat)
    (tgtRaw : Arg K i64) (nxtRaw : RegsExpr K) (kind : EdgeKind) : TFlat abi.retSig :=
  let tgt := remapArg d em tgtRaw
  let nxt := remapRegsExpr d em nxtRaw
  let jArgs := mkJumpTuple d sp0Lvl nxt nSlots sLvls
  let idxOfLvl (lvl : Nat) : Nat :=
    let bIdx := st.env.length - 1 - lvl
    match listGet? em bIdx with
    | some tl => d - 1 - tl
    | none => 0
  match abi, kind with
  | _, .direct targetPc => lowerContJumpTo nSlots pcs targetPc jArgs
  | _, .select tPc ePc =>
      match st.evalArg tgtRaw with
      | .ite cLvl _ _ =>
          .jnz (.var (idxOfLvl cLvl))
            (lowerContJumpTo nSlots pcs tPc jArgs)
            (lowerContJumpTo nSlots pcs ePc jArgs)
      | _ => .hlt
  | _, .strideTable _ targets false =>
      match st.evalArg tgtRaw with
      | .stride _ lvl => lowerContStride nSlots pcs (idxOfLvl lvl) jArgs 0 0 targets
      | _ => .hlt
  | .retEnvelope, .strideTable _ targets true =>
      match st.evalArg tgtRaw with
      | .stride _ lvl =>
          let iv := idxOfLvl lvl
          let boundOp : Op K [.bool] :=
            op2 (.cmp .ult i64) (.var iv) (.imm (BitVec.ofNat 64 targets.length))
          let jArgs1 := mkJumpTuple (d + 1) sp0Lvl (remapRegsExpr (d + 1) em nxtRaw) nSlots sLvls
          .let_ boundOp
            (.jnz (.var 0)
              (lowerContStride nSlots pcs (iv + 1) jArgs1 0 0 targets)
              (flushFrame sp0Lvl sLvls (d + 1) fun _ =>
                mkRetEnvelope (shiftArg (1 + sLvls.length) tgt)
                  (shiftRegsExpr (1 + sLvls.length) nxt)))
      | _ => .hlt
  | .retEnvelope, .contCall callee _ dualRet retPc altRetPc? =>
      let retSigC := (RegionAbi.contified dualRet).retSig
      let retDepth := d + retSigC.length
      let retNxt : RegsExpr K :=
        if dualRet then
          ⟨.var (retDepth - 1 - (d + 1)), .var (retDepth - 1 - (d + 2)),
           .var (retDepth - 1 - (d + 3)), .var (retDepth - 1 - (d + 4)),
           .var (retDepth - 1 - (d + 5)), .var (retDepth - 1 - (d + 6))⟩
        else
          ⟨.var (retDepth - 1 - d), .var (retDepth - 1 - (d + 1)),
           .var (retDepth - 1 - (d + 2)), .var (retDepth - 1 - (d + 3)),
           .var (retDepth - 1 - (d + 4)), .var (retDepth - 1 - (d + 5))⟩
      let jCall := mkJumpTuple retDepth sp0Lvl retNxt nSlots sLvls
      if dualRet then
        match altRetPc? with
        | some altPc =>
            .call callee retSigC nxt.toTup
              (.jnz (.var 6)
                (lowerContJumpTo nSlots pcs altPc jCall)
                (lowerContJumpTo nSlots pcs retPc jCall))
        | none => .hlt
      else
        .call callee retSigC nxt.toTup (lowerContJumpTo nSlots pcs retPc jCall)
  | .contified false, .contRet false => .ret nxt.toTup
  | .contified true, .contRet isAlt => .ret (.imm isAlt, nxt.toTup)
  | .retEnvelope, .guarded hotTargets =>
      lowerContGuarded nSlots sp0Lvl sLvls pcs tgt nxt d 0 hotTargets
  | .retEnvelope, .bailout =>
      flushFrame sp0Lvl sLvls d fun _ =>
        mkRetEnvelope (shiftArg sLvls.length tgt) (shiftRegsExpr sLvls.length nxt)
  | _, _ => .hlt

/-- Lower non-private `load` / `store` with static or dynamic-guarded frame safety. -/
@[expose] def lowerNonSlotLoad (cm : CodeMap) (abi : RegionAbi) (pf : PrivFrameCfg)
    (t : Ty) (a : Arg K i64) (st : ContSymState) (d : Nat) (em sLvls : List Nat)
    (kRaw : BlockFlat) (kCont : Nat → List Nat → TFlat abi.retSig) : TFlat abi.retSig :=
  let nSlots := pf.numSlots
  if isStaticOutsideFrame nSlots t.bytes (st.evalArg a) then
    .load t (remapArg d em a) (kCont (d + 1) (d :: em))
  else
    match abi with
    | .retEnvelope =>
        if pf.dynAliasGuard && (t.bytes ≤ 16) then
          let aT := remapArg d em a
          let tArm := .load t (shiftArg 5 aT) (kCont (d + 6) ((d + 5) :: em))
          let fArm := flushFrame 6 sLvls (d + 5) fun d' =>
            lowerUnpromotedTail cm (.load t a kRaw) d' em
          emitAliasGuard 6 nSlots d aT t.bytes tArm fArm
        else .hlt
    | .contified _ => .hlt

/-- Lower non-private `store` with static or dynamic-guarded frame safety. -/
@[expose] def lowerNonSlotStore (cm : CodeMap) (abi : RegionAbi) (pf : PrivFrameCfg)
    {t : Ty} (v : Arg K t) (a : Arg K i64) (st : ContSymState) (d : Nat) (em sLvls : List Nat)
    (kRaw : BlockFlat) (kCont : Nat → TFlat abi.retSig) : TFlat abi.retSig :=
  let nSlots := pf.numSlots
  if isStaticOutsideFrame nSlots t.bytes (st.evalArg a) then
    .store (remapArg d em v) (remapArg d em a) (kCont d)
  else
    match abi with
    | .retEnvelope =>
        if pf.dynAliasGuard && (t.bytes ≤ 16) then
          let aT := remapArg d em a
          let vT := remapArg d em v
          let tArm := .store (shiftArg 5 vT) (shiftArg 5 aT) (kCont (d + 5))
          let fArm := flushFrame 6 sLvls (d + 5) fun d' =>
            lowerUnpromotedTail cm (.store v a kRaw) d' em
          emitAliasGuard 6 nSlots d aT t.bytes tArm fArm
        else .hlt
    | .contified _ => .hlt

/-- Lower a `BlockFlat` with promoted slots `sLvls` (`em` maps `BlockFlat` -> `TFlat` levels). -/
@[expose] def liftContifyBlock (cm : CodeMap) (abi : RegionAbi) (pf : PrivFrameCfg)
    (rw : RegionWitness) (pcs : List (BitVec 64)) (pc : BitVec 64) :
    BlockFlat → BranchPath → ContSymState → Nat → List Nat → List Nat → TFlat abi.retSig
  | .let_ (ts := ts) op k, path, st, d, em, sLvls =>
      .let_ ⟨op.code, remapArgs d em op.args⟩
        (liftContifyBlock cm abi pf rw pcs pc k path (st.pushRes ts (evalContOp st op))
          (d + ts.length) (pushEnvMap ts d em) sLvls)
  | .load t a k, path, st, d, em, sLvls =>
      let nSlots := pf.numSlots
      let kNext d' em' := liftContifyBlock cm abi pf rw pcs pc k path
        { st with env := .top :: st.env, ctx := t :: st.ctx } d' em' sLvls
      if nSlots == 0 then
        .load t (remapArg d em a) (kNext (d + 1) (d :: em))
      else
        match t with
        | .bits 64 =>
            match spSlotOf? nSlots (st.evalArg a) with
            | some slotIdx =>
                match listGet? sLvls slotIdx with
                | some sLvl =>
                    .let_ (op1 (.copy i64) (.var (d - 1 - sLvl)))
                      (liftContifyBlock cm abi pf rw pcs pc k path
                        { st with env := .top :: st.env, ctx := i64 :: st.ctx }
                        (d + 1) (d :: em) sLvls)
                | none => .hlt
            | none => lowerNonSlotLoad cm abi pf i64 a st d em sLvls k kNext
        | _ => lowerNonSlotLoad cm abi pf t a st d em sLvls k kNext
  | .store (t := t) v a k, path, st, d, em, sLvls =>
      let nSlots := pf.numSlots
      let kStore d' := liftContifyBlock cm abi pf rw pcs pc k path st d' em sLvls
      if nSlots == 0 then
        .store (remapArg d em v) (remapArg d em a) (kStore d)
      else if t == i64 then
        match spSlotOf? nSlots (st.evalArg a) with
        | some slotIdx =>
            match remapArg d em v with
            | .var vi =>
                let vLvl := d - 1 - vi
                liftContifyBlock cm abi pf rw pcs pc k path st d em (sLvls.set slotIdx vLvl)
            | .imm c =>
                match t with
                | .bits 64 =>
                    .let_ (op1 (.copy i64) (.imm c))
                      (liftContifyBlock cm abi pf rw pcs pc k path st
                        (d + 1) em (sLvls.set slotIdx d))
                | _ => .hlt
        | none => lowerNonSlotStore cm abi pf v a st d em sLvls k kStore
      else
        lowerNonSlotStore cm abi pf v a st d em sLvls k kStore
  | .codeAddr sym k, path, st, d, em, sLvls =>
      match cm.addrOf? sym with
      | some a =>
          let sv := if (a &&& 7#64) == 0#64 then .alignedConst a else .const a
          .let_ (op1 (.copy i64) (.imm a))
            (liftContifyBlock cm abi pf rw pcs pc k path
              { st with env := sv :: st.env, ctx := i64 :: st.ctx } (d + 1) (d :: em) sLvls)
      | none => .hlt
  | .jnz c t e, path, st, d, em, sLvls =>
      .jnz (remapArg d em c)
        (liftContifyBlock cm abi pf rw pcs pc t (path ++ [true]) (st.pushCondFact c true) d em
          sLvls)
        (liftContifyBlock cm abi pf rw pcs pc e (path ++ [false]) (st.pushCondFact c false) d em
          sLvls)
  | .ijmp tgt nxt, path, st, d, em, sLvls =>
      match rw.findEdge pc path with
      | some ew =>
          liftContEdgeMapped abi pf.numSlots 6 sLvls pcs st d em tgt nxt ew.kind
      | none => .hlt
  | .halt c, _, _, d, em, sLvls =>
      flushFrame 6 sLvls d fun d' =>
        .exit haltSym (as := [i64]) (remapArg d' em c, ())
  | .hlt, _, _, _, _, _ => .hlt

mutual
/-- Lower a nested `GroupTree` node into `TFlat cr.abi.retSig`. -/
@[expose] def liftContifyGroupNode (cm : CodeMap) (cr : ContifyRegion)
    (pcs : List (BitVec 64)) : GroupTree → TFlat cr.abi.retSig
  | .leaf pc =>
      let nSlots := cr.privFrame.numSlots
      let d0 := if nSlots = 0 then 6 else 7 + nSlots
      match cm.lookupAddr pc with
      | some b =>
          liftContifyBlock cm cr.abi cr.privFrame cr.toRegionWitness pcs pc b []
            ContSymState.init d0 initEnvMap (initSlotsLvls nSlots)
      | none => .hlt
  | .loop header nodes =>
      let nSlots := cr.privFrame.numSlots
      let entries := nodes.map GroupTree.entryPc
      let pcsInner := pushLabelPcs entries pcs
      let bodies := liftContifyGroupNodes cm cr pcsInner nodes
      .group bodies (lowerContJumpTo nSlots pcsInner header (baseContArgs nSlots))

/-- Lower a list of nested `GroupTree` nodes into `TBlocks cr.abi.retSig`. -/
@[expose] def liftContifyGroupNodes (cm : CodeMap) (cr : ContifyRegion)
    (pcs : List (BitVec 64)) :
    (gs : List GroupTree) →
      TBlocks cr.abi.retSig (gs.map fun _ => contSig cr.privFrame.numSlots)
  | [] => .nil
  | g :: gs =>
      .cons (liftContifyGroupNode cm cr pcs g) (liftContifyGroupNodes cm cr pcs gs)
end

/-- Emit `nSlots` initial `.load i64 (sp₀ - 8*(k+1))` loads at region entry (`sp₀` at level `0`,
depth initially `6`). Note each slot step pushes `2` binders (`addr`, `val`). -/
@[expose] def loadEntryFrameAux {rs : List Ty} (sp0Lvl totalK : Nat) :
    Nat → TFlat rs → TFlat rs
  | 0, kCont => kCont
  | rem + 1, kCont =>
      let k := totalK - (rem + 1)
      let d := 6 + 2 * k
      let addrOp : Op K [i64] :=
        op2 (.sub i64) (.var (d - 1 - sp0Lvl)) (.imm (BitVec.ofNat 64 (8 * (k + 1))))
      .let_ addrOp
        (.load i64 (.var 0)
          (loadEntryFrameAux sp0Lvl totalK rem kCont))

/-- Build slot entry arg list from `loadEntryFrameAux` (`2*idx + 1` offsets from `6`). -/
@[expose] def mkEntrySlotArgs (d : Nat) :
    (n idx : Nat) → Tup (Arg K) (List.replicate n i64)
  | 0, _ => ()
  | n + 1, idx => (.var (d - 1 - (6 + 2 * idx + 1)), mkEntrySlotArgs d n (idx + 1))

/-- Construct `(sp..r3, sp₀, slot₀..slot_{nSlots-1})` entry args from `loadEntryFrameAux`. -/
@[expose] def mkEntryFrameArgs : (nSlots : Nat) → Tup (Arg K) (contSig nSlots)
  | 0 => (.var 5, .var 4, .var 3, .var 2, .var 1, .var 0, ())
  | k + 1 =>
      let d := 6 + 2 * (k + 1)
      let rEnt : RegsExpr K :=
        ⟨.var (d - 1 - 0), .var (d - 1 - 1), .var (d - 1 - 2),
         .var (d - 1 - 3), .var (d - 1 - 4), .var (d - 1 - 5)⟩
      tupAppend rEnt.toTup (.var (d - 1 - 0), mkEntrySlotArgs d (k + 1) 0)

/-- Lower an entire `ContifyRegion` (with `loadEntryFrameAux` prelude when `nSlots > 0`). -/
@[expose] def liftContifyTFlat (cm : CodeMap) (cr : ContifyRegion) : TFlat cr.abi.retSig :=
  let nSlots := cr.privFrame.numSlots
  let entries := cr.tree.map GroupTree.entryPc
  let pcs := pushLabelPcs entries []
  let bodies := liftContifyGroupNodes cm cr pcs cr.tree
  let grp := .group bodies (lowerContJumpTo nSlots pcs cr.entryPc (mkEntryFrameArgs nSlots))
  loadEntryFrameAux 0 nSlots nSlots grp

/-- Computable verifier checking ALL Stage-1 safety/WTO/typing/`PrivFrame` conditions for one
`ContifyRegion`. -/
@[expose] def ContifyRegion.check (cm : CodeMap) (callees : List ContCalleeMeta)
    (cr : ContifyRegion) : Bool :=
  let nSlots := cr.privFrame.numSlots
  let entries := cr.tree.map GroupTree.entryPc
  let pcs := pushLabelPcs entries []
  let tf := liftContifyTFlat cm cr
  fnNameOk cr.name &&
  (nSlots ≤ 64) &&
  (nSlots == 0 || cr.abi == .retEnvelope) &&
  (!cr.tree.isEmpty) &&
  (cm.lookupAddr cr.entryPc).isSome &&
  entries.contains cr.entryPc &&
  listNodup cr.allPcs &&
  checkContGroupNodes cm cr callees pcs cr.tree &&
  tf.wfCheck regCtx [] &&
  tf.noHlt

/-- Deterministic lifting from `ContifyRegion` to typed `LeanQbe.T.Fn`. -/
@[expose] def liftContifyRegion (cm : CodeMap) (cr : ContifyRegion) : Fn where
  name := cr.name
  as := regSig
  rs := cr.abi.retSig
  body := denoteFunc (liftContifyTFlat cm cr)

/-- Whole-witness verifier checking region disjointness, naming, and DAG contification. -/
@[expose] def ContifyWitness.checkAux (cm : CodeMap) (callees : List ContCalleeMeta) :
    List ContifyRegion → Bool
  | [] => true
  | cr :: crs =>
      cr.check cm callees &&
      let callees' := match cr.toCalleeMeta? cm callees with
        | some c => c :: callees
        | none => callees
      ContifyWitness.checkAux cm callees' crs

/-- Verify all regions in `wit` are well-formed, disjoint, distinctly named, and acyclic. -/
@[expose] def ContifyWitness.check (cm : CodeMap) (wit : ContifyWitness) : Bool :=
  listNodup (wit.regions.map (·.name)) &&
  listNodup (wit.regions.flatMap ContifyRegion.allPcs) &&
  ContifyWitness.checkAux cm [] wit.regions

/-- Compute residual `CodeMap` `W_res` matching Stage-0 `residualCodeMap`. -/
@[expose] def residualContifyCodeMap (cm : CodeMap) (wit : ContifyWitness) : CodeMap :=
  let entries := wit.regions.map (·.entryPc)
  let dropAll :=
    (wit.regions.filter (fun r => !r.retainFallbacks)).flatMap ContifyRegion.allPcs
  cm.filter fun e => (!entries.contains e.addr) && (!dropAll.contains e.addr)

/-- Verified Stage-1 lifting returning `(liftedFns, W_res)` in region order. -/
@[expose] def checkAndLiftContify (cm : CodeMap) (wit : ContifyWitness) :
    Except String (List Fn × CodeMap) :=
  if wit.check cm then
    .ok (wit.regions.map (liftContifyRegion cm), residualContifyCodeMap cm wit)
  else
    .error "CfgContify: witness check failed"

/-! ## §5. Untrusted Heuristic Stage-1 Recovery (`analyzeContify`) -/

private def countContiguousPadsC (cm : CodeMap) (base : BitVec 64) :
    Nat → Nat → List (BitVec 64)
  | 0, _ => []
  | fuel + 1, idx =>
      let addr := base + BitVec.ofNat 64 (8 * idx)
      match cm.lookupAddr addr with
      | some _ => addr :: countContiguousPadsC cm base fuel (idx + 1)
      | none => []

private def detectStrideTargetsC (cm : CodeMap) (st : ContSymState) (base : BitVec 64)
    (lvl : Nat) : Option (List (BitVec 64) × Bool) :=
  let maxPads := 16
  let pads := countContiguousPadsC cm base maxPads 0
  if pads.isEmpty then none
  else
    let bounded := (List.range maxPads).find? fun k =>
      k > 0 && st.toSymState.hasUltBound lvl k
    match bounded with
    | some k => if k ≤ pads.length then some (pads.take k, false) else some (pads, true)
    | none => some (pads, true)

private def isDualReturnC (cm : CodeMap) (entries : List CodeEntry) : Option (Sym × Bool) :=
  match entries with
  | [] => none
  | e :: _ =>
      match symEvalContBlock cm {} e.block [] ContSymState.init with
      | some leaves =>
          let hasRp0 := leaves.any fun l => l.st.evalArg l.target == .rpOffset 0#64
          let hasRp8 := leaves.any fun l => l.st.evalArg l.target == .rpOffset 8#64
          if (hasRp0 || hasRp8) && leaves.all (fun l =>
              match l.st.evalArg l.target with
              | .rpOffset 0#64 | .rpOffset 8#64 => true
              | _ => false) then
            some (e.name, hasRp8)
          else none
      | none => none

private def classifyCalleesC (cm : CodeMap) : List (CodeEntry × Bool) :=
  cm.filterMap fun e =>
    match isDualReturnC cm [e] with
    | some (_, dual) => some (e, dual)
    | none => none

private def classifyLeafC (cm : CodeMap) (calleeMap : List (CodeEntry × Bool))
    (srcPc : BitVec 64) (leaf : ContSymLeaf) : EdgeWitness × List (BitVec 64) :=
  let st := leaf.st
  match st.evalArg leaf.target with
  | .const p | .alignedConst p =>
      match st.resolveConst leaf.nextRegs.rp with
      | some retPc =>
          match calleeMap.find? (fun (ce, _) => ce.addr == p) with
          | some (ce, dual) =>
              if (cm.lookupAddr retPc).isSome &&
                 ((!dual) || (cm.lookupAddr (retPc + 8#64)).isSome) then
                let alt? := if dual then some (retPc + 8#64) else none
                (⟨srcPc, leaf.path, .contCall ce.name ce.addr dual retPc alt?⟩,
                 if dual then [retPc, retPc + 8#64] else [retPc])
              else if (cm.lookupAddr p).isSome then
                (⟨srcPc, leaf.path, .direct p⟩, [p])
              else (⟨srcPc, leaf.path, .bailout⟩, [])
          | none =>
              if (cm.lookupAddr p).isSome then (⟨srcPc, leaf.path, .direct p⟩, [p])
              else (⟨srcPc, leaf.path, .bailout⟩, [])
      | none =>
          if (cm.lookupAddr p).isSome then (⟨srcPc, leaf.path, .direct p⟩, [p])
          else (⟨srcPc, leaf.path, .bailout⟩, [])
  | .ite _ tSym eSym =>
      match tSym.asConst?, eSym.asConst? with
      | some tPc, some ePc =>
          if (cm.lookupAddr tPc).isSome && (cm.lookupAddr ePc).isSome then
            (⟨srcPc, leaf.path, .select tPc ePc⟩, [tPc, ePc])
          else (⟨srcPc, leaf.path, .bailout⟩, [])
      | _, _ => (⟨srcPc, leaf.path, .bailout⟩, [])
  | .stride base lvl =>
      match detectStrideTargetsC cm st base lvl with
      | some (pads, needG) =>
          (⟨srcPc, leaf.path, .strideTable base pads needG⟩, pads)
      | none => (⟨srcPc, leaf.path, .bailout⟩, [])
  | _ => (⟨srcPc, leaf.path, .bailout⟩, [])

private partial def collectReachableC (cm : CodeMap) (calleeMap : List (CodeEntry × Bool))
    (claimed : List (BitVec 64)) (work : List (BitVec 64)) (visited : List (BitVec 64))
    (edges : List EdgeWitness) : List (BitVec 64) × List EdgeWitness :=
  match work with
  | [] => (visited, edges)
  | pc :: rest =>
      if visited.contains pc || claimed.contains pc then
        collectReachableC cm calleeMap claimed rest visited edges
      else
        match cm.lookupAddr pc with
        | none => collectReachableC cm calleeMap claimed rest visited edges
        | some b =>
            match symEvalContBlock cm {} b [] ContSymState.init with
            | none => collectReachableC cm calleeMap claimed rest visited edges
            | some leaves =>
                let pairs := leaves.map (classifyLeafC cm calleeMap pc)
                let newEdges := pairs.map Prod.fst
                let nextPcs := (pairs.flatMap Prod.snd).filter
                  fun p => !visited.contains p && !claimed.contains p && (cm.lookupAddr p).isSome
                collectReachableC cm calleeMap claimed (nextPcs ++ rest)
                  (pc :: visited) (edges ++ newEdges)

private def directSuccsOfC (edges : List EdgeWitness) (pc : BitVec 64) : List (BitVec 64) :=
  edges.flatMap fun ew =>
    if ew.srcPc != pc then []
    else match ew.kind with
      | .direct p => [p]
      | .select t e => [t, e]
      | .strideTable _ ts _ => ts
      | .contCall _ _ true r (some a) => [r, a]
      | .contCall _ _ _ r _ => [r]
      | .guarded hs => hs
      | _ => []

private partial def reachFromC (edges : List EdgeWitness) (allowed : List (BitVec 64)) :
    List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], vis => vis
  | p :: ps, vis =>
      if vis.contains p || !allowed.contains p then reachFromC edges allowed ps vis
      else
        let succs := (directSuccsOfC edges p).filter allowed.contains
        reachFromC edges allowed (succs ++ ps) (p :: vis)

/-- Recursive Bourdoncle WTO loop builder supporting arbitrarily nested `GroupTree.loop`s. -/
private def buildNestedLoopTree (edges : List EdgeWitness) :
    Nat → List (BitVec 64) → List GroupTree
  | _, [] => []
  | 0, pcs => pcs.map .leaf
  | fuel + 1, pcs =>
      let headers := pcs.filter fun h =>
        (reachFromC edges pcs (directSuccsOfC edges h) []).contains h
      match headers with
      | [] => pcs.map .leaf
      | h :: _ =>
          let rFromH := reachFromC edges pcs [h] []
          let loopBody := rFromH.filter fun u =>
            u == h || (reachFromC edges pcs (directSuccsOfC edges u) []).contains h
          let outerEntrants := pcs.filter fun p =>
            !loopBody.contains p &&
            (directSuccsOfC edges p).any (fun s => s != h && loopBody.contains s)
          if loopBody.length ≥ 1 && outerEntrants.isEmpty then
            let innerTail := loopBody.filter (· != h)
            let innerTree := .leaf h :: buildNestedLoopTree edges fuel innerTail
            let rest := pcs.filter (fun p => !loopBody.contains p)
            (.loop h innerTree) :: buildNestedLoopTree edges fuel rest
          else pcs.map .leaf

/-- Inspect symbolic address `sv` for negative stack slot `(k + 1)` (`0..15`), or whether an
unknown non-static address appears (`needGuard`). -/
private def scanMemSlotsBlock (cm : CodeMap) :
    BlockFlat → ContSymState → Nat × Bool
  | .let_ (ts := ts) op k, st => scanMemSlotsBlock cm k (st.pushRes ts (evalContOp st op))
  | .load t a k, st =>
      let sv := st.evalArg a
      let kHit := if t == i64 then spSlotOf? 16 sv else none
      let (m1, ng1) := match kHit with
        | some idx => (idx + 1, false)
        | none => (0, !isStaticOutsideFrame 16 t.bytes sv)
      let (m2, ng2) := scanMemSlotsBlock cm k { st with env := .top :: st.env, ctx := t :: st.ctx }
      (Nat.max m1 m2, ng1 || ng2)
  | .store (t := t) _ a k, st =>
      let sv := st.evalArg a
      let kHit := if t == i64 then spSlotOf? 16 sv else none
      let (m1, ng1) := match kHit with
        | some idx => (idx + 1, false)
        | none => (0, !isStaticOutsideFrame 16 t.bytes sv)
      let (m2, ng2) := scanMemSlotsBlock cm k st
      (Nat.max m1 m2, ng1 || ng2)
  | .codeAddr sym k, st =>
      let sv := match cm.addrOf? sym with
        | some a => if (a &&& 7#64) == 0#64 then .alignedConst a else .const a
        | none => .top
      scanMemSlotsBlock cm k { st with env := sv :: st.env, ctx := i64 :: st.ctx }
  | .jnz c t e, st =>
      let (m1, ng1) := scanMemSlotsBlock cm t (st.pushCondFact c true)
      let (m2, ng2) := scanMemSlotsBlock cm e (st.pushCondFact c false)
      (Nat.max m1 m2, ng1 || ng2)
  | _, _ => (0, false)

private def detectPrivFrame (cm : CodeMap) (pcs : List (BitVec 64)) : PrivFrameCfg :=
  let (slots, needDyn) := pcs.foldl (fun (acc : Nat × Bool) pc =>
    match cm.lookupAddr pc with
    | some b =>
        let (m, ng) := scanMemSlotsBlock cm b ContSymState.init
        (Nat.max acc.1 m, acc.2 || ng)
    | none => acc) (0, false)
  if slots == 0 then {} else ⟨slots, needDyn⟩

/-- Untrusted heuristic Stage-1 analyzer recovering contified callees, nested Bourdoncle
`GroupTree` loops, and private stack-slot promotion (`PrivFrameCfg` + dynamic alias guard). -/
def analyzeContify (cm : CodeMap) : Option ContifyWitness :=
  let calleeEntries := classifyCalleesC cm
  let calleeRegs : List ContifyRegion := (calleeEntries.map fun (ce, dual) =>
    let leaves := (symEvalContBlock cm {} ce.block [] ContSymState.init).getD []
    let es := leaves.map fun l =>
      let isAlt := l.st.evalArg l.target == .rpOffset 8#64
      ⟨ce.addr, l.path, .contRet isAlt⟩
    ⟨ce.name, ce.addr, .contified dual, {}, [.leaf ce.addr], es, true⟩).filter
      (·.check cm [])
  let calleeMeta := calleeRegs.filterMap (·.toCalleeMeta? cm [])
  let validCalleeEntries := calleeEntries.filter fun (ce, _) =>
    calleeRegs.any (fun cr => cr.entryPc == ce.addr)
  let claimedInit := calleeRegs.map (·.entryPc)
  let callerStep := cm.foldl (fun (acc : List (BitVec 64) × List ContifyRegion) e =>
    let (claimed, regs) := acc
    if claimed.contains e.addr then acc
    else
      let (pcsRev, rawEdges) := collectReachableC cm validCalleeEntries claimed [e.addr] [] []
      let pcs := pcsRev.reverse
      if pcs.isEmpty then acc
      else
        let tree := buildNestedLoopTree rawEdges pcs.length pcs
        let pf := detectPrivFrame cm pcs
        let cr : ContifyRegion :=
          ⟨e.name ++ "_reg", e.addr, .retEnvelope, pf, tree, rawEdges, true⟩
        if cr.check cm calleeMeta then
          (pcs ++ claimed, regs ++ [cr])
        else
          let cr0 : ContifyRegion :=
            ⟨e.name ++ "_reg", e.addr, .retEnvelope, {}, tree, rawEdges, true⟩
          if cr0.check cm calleeMeta then (pcs ++ claimed, regs ++ [cr0])
          else acc) (claimedInit, [])
  let wit : ContifyWitness := ⟨calleeRegs ++ callerStep.2⟩
  if wit.regions.isEmpty || !wit.check cm then none else some wit

end LeanQbe.T.Unified
