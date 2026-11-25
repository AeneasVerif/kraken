module

public import LeanQbe.T.BedrockWord.Core
public import LeanQbe.T.Unified.Ssa
public import LeanQbe.T.Main

/-!
# Verified Witness-Checked CFG Recovery (`Unified.CfgRecovery`)

Implements Stage 0 of the CFG recovery pipeline over `LeanQbe.T.BedrockWord`:

* Witness schema (`RegionAbi`, `EdgeKind`, `EdgeWitness`, `GroupTree`, `RegionWitness`,
  `CfgWitness`) covering direct/untagged targets, flagless `OpCode.select`, bounded stride
  jump tables (`base + (idx <<< 3)` / `base + idx * 8`), single/dual-return `callM`/`retM`
  contification (`rp` / `rp + 8`), Bourdoncle loop `GroupTree`, and speculative `guarded`
  edges with `bailout`.
* Forward linear symbolic evaluator (`SymVal`, `SymFact`, `SymState`, `symEvalBlock`).
* Linear computable witness checker (`RegionWitness.check`, `CfgWitness.check`) enforcing
  `BlockFlat.Wf`, WTO lexical scoping, DAG contification, `TFlat.wfCheck`, and `TFlat.noHlt`.
* Sound deterministic `TFlat` region lowerer (`liftRegion`, `checkAndLiftRegion`,
  `checkAndLiftWitness`) yielding typed `LeanQbe.T.Fn` + residual `CodeMap` `W_res`.
* Untrusted heuristic analyzer (`analyzeCfg : CodeMap → Option CfgWitness`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.BedrockWord

/-! ## §1. Witness Types and Region ABIs -/

/-- Synthetic `.exit` target symbol representing `BlockFlat.halt code`. -/
@[expose] def haltSym : Sym := "bw_halt"

@[expose] section
/-- Calling convention and exit envelope selected for one recovered region. -/
inductive RegionAbi : Type
  | retEnvelope
  | contified (dualRet : Bool)
  deriving DecidableEq, Repr
end

/-- Typed return signature associated with a `RegionAbi`. -/
@[expose] def RegionAbi.retSig : RegionAbi → List Ty
  | .retEnvelope => i64 :: regSig
  | .contified false => regSig
  | .contified true => .bool :: regSig

/-- True iff the region uses a contified callee calling convention. -/
@[expose] def RegionAbi.isContified : RegionAbi → Bool
  | .retEnvelope => false
  | .contified _ => true

/-- True iff a contified region returns via dual `(rp, rp + 8)` convention. -/
@[expose] def RegionAbi.isDualRet : RegionAbi → Bool
  | .contified true => true
  | _ => false

@[expose] section
/-- Verified lifting strategy for one `BlockFlat.ijmp` terminator leaf. -/
inductive EdgeKind : Type
  | direct (targetPc : BitVec 64)
  | select (tPc ePc : BitVec 64)
  | strideTable (basePc : BitVec 64) (targets : List (BitVec 64)) (needGuard : Bool)
  | contCall (callee : Sym) (calleePc : BitVec 64) (dualRet : Bool) (retPc : BitVec 64)
      (altRetPc? : Option (BitVec 64))
  | contRet (isAlt : Bool)
  | guarded (hotTargets : List (BitVec 64))
  | bailout
  deriving DecidableEq, Repr

/-- Path of `.jnz` branch choices (`true` = then, `false` = else) reaching a block leaf. -/
abbrev BranchPath : Type := List Bool

/-- Edge witness annotating one `(srcPc, path)` `ijmp` leaf inside a region. -/
structure EdgeWitness : Type where
  srcPc : BitVec 64
  path  : BranchPath
  kind  : EdgeKind
  deriving DecidableEq, Repr
end

/-- Bourdoncle Weak Topological Ordering group tree defining nested `TFlat.group` scopes. -/
inductive GroupTree : Type
  | leaf (pc : BitVec 64)
  | loop (header : BitVec 64) (nodes : List GroupTree)

/-- Entry address of a `GroupTree` node. -/
@[expose] def GroupTree.entryPc : GroupTree → BitVec 64
  | .leaf pc => pc
  | .loop header _ => header

/-- All block addresses contained in a `GroupTree` node (preorder). -/
@[expose] def GroupTree.allPcs : GroupTree → List (BitVec 64)
  | .leaf pc => [pc]
  | .loop _ nodes => nodes.flatMap GroupTree.allPcs

/-- Self-contained witness for lifting one CFG region into a `LeanQbe.T.Fn`. -/
structure RegionWitness : Type where
  name            : Sym
  entryPc         : BitVec 64
  abi             : RegionAbi
  tree            : List GroupTree
  edges           : List EdgeWitness
  retainFallbacks : Bool := true

/-- All block addresses owned by a region. -/
@[expose] def RegionWitness.allPcs (rw : RegionWitness) : List (BitVec 64) :=
  rw.tree.flatMap GroupTree.allPcs

/-- Whole-program recovery witness ordered callees-first (`R₀, ..., Rₙ₋₁`). -/
structure CfgWitness : Type where
  regions : List RegionWitness

/-! ## §2. Forward Linear Symbolic Evaluator -/

@[expose] section
/-- Symbolic abstraction over block-local values (references variables by de Bruijn level). -/
inductive SymVal : Type
  | rpOffset (off : BitVec 64)
  | const (w : BitVec 64)
  | alignedConst (w : BitVec 64)
  | taggedAligned (w tag : BitVec 64)
  | shl3 (idxLvl : Nat)
  | stride (base : BitVec 64) (idxLvl : Nat)
  | ite (condLvl : Nat) (tVal eVal : SymVal)
  | boolConst (b : Bool)
  | cmpUlt (lhsLvl : Nat) (bound : BitVec 64)
  | top
  deriving DecidableEq, Repr

/-- Dominating branch fact recorded while walking `.jnz` conditions. -/
inductive SymFact : Type
  | ultBound (lvl : Nat) (bound : BitVec 64)
  deriving DecidableEq, Repr

/-- Forward symbolic state synchronized with de Bruijn stack `vs` (head = index `0`). -/
structure SymState : Type where
  env   : List SymVal
  ctx   : List Ty
  facts : List SymFact
  deriving DecidableEq, Repr
end

/-- Initial symbolic state matching `regCtx` (`[r3, r2, r1, rv, rp, sp]`, levels `5..0`). -/
@[expose] def SymState.init : SymState where
  env   := [.top, .top, .top, .top, .rpOffset 0#64, .top]
  ctx   := regCtx
  facts := []

/-- Look up a symbolic value by de Bruijn index (`0` = head). -/
@[expose] def SymState.getSym (st : SymState) (idx : Nat) : SymVal :=
  match listGet? st.env idx with
  | some v => v
  | none => .top

/-- Evaluate a typed `Arg K t` symbolically in `st`. -/
@[expose] def SymState.evalArg (st : SymState) {t : Ty} : Arg K t → SymVal
  | .var idx => st.getSym idx
  | .imm c =>
      match t with
      | .bool => .boolConst c
      | .bits 64 => .const c
      | _ => .top

/-- Convert a de Bruijn index `< st.env.length` to its immutable de Bruijn level. -/
@[expose] def SymState.toLevel? (st : SymState) (idx : Nat) : Option Nat :=
  if idx < st.env.length then some (st.env.length - 1 - idx) else none

/-- Check that `lvl` is in scope in `st.ctx` with exact type `t`. -/
@[expose] def SymState.levelHasTy (st : SymState) (lvl : Nat) (t : Ty) : Bool :=
  if lvl < st.ctx.length then
    match listGet? st.ctx (st.ctx.length - 1 - lvl) with
    | some t' => match tyDecEq t' t with | isTrue _ => true | isFalse _ => false
    | none => false
  else false

/-- Extract a known constant 64-bit value if `sv` represents a constant or aligned constant. -/
@[expose] def SymVal.asConst? : SymVal → Option (BitVec 64)
  | .const w => some w
  | .alignedConst w => some w
  | _ => none

/-- Extract the constant from an `Arg K i64`. -/
@[expose] def SymState.resolveConst (st : SymState) (a : Arg K i64) : Option (BitVec 64) :=
  (st.evalArg a).asConst?

/-- Check whether `a : Arg K i64` represents `rp₀ + 0#64`. -/
@[expose] def SymState.isRpZero (st : SymState) (a : Arg K i64) : Bool :=
  match st.evalArg a with
  | .rpOffset 0#64 => true
  | _ => false

/-- Check whether dominating branch facts guarantee `lvl < n` (unsigned 64-bit). -/
@[expose] def SymState.hasUltBound (st : SymState) (lvl : Nat) (n : Nat) : Bool :=
  st.facts.any fun f => match f with
    | .ultBound l b => (l == lvl) && (b.toNat ≤ n)

/-- Push new result types + symbolic values preserving de Bruijn head-first alignment. -/
@[expose] def SymState.pushRes (st : SymState) (ts : List Ty) (svs : List SymVal) : SymState :=
  { env := svs ++ st.env
    ctx := pushTypes ts st.ctx
    facts := st.facts }

@[expose] def mkUntag (x y : SymVal) : SymVal :=
  match x, y with
  | .taggedAligned w _, .const m => if m == ~~~7#64 then .alignedConst w else .top
  | .const m, .taggedAligned w _ => if m == ~~~7#64 then .alignedConst w else .top
  | .const a, .const b => .const (a &&& b)
  | .alignedConst a, .const b => .const (a &&& b)
  | .const a, .alignedConst b => .const (a &&& b)
  | _, _ => .top

@[expose] def mkOrTag (x y : SymVal) : SymVal :=
  match x, y with
  | .alignedConst w, .const tag =>
      if BitVec.ult tag 8#64 then .taggedAligned w tag else .const (w ||| tag)
  | .const tag, .alignedConst w =>
      if BitVec.ult tag 8#64 then .taggedAligned w tag else .const (tag ||| w)
  | .const a, .const b => .const (a ||| b)
  | _, _ => .top

@[expose] def mkAdd (x y : SymVal) : SymVal :=
  match x, y with
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

/-- Abstractly interpret one `OpCode` producing symbolic values in push-order (last = head). -/
@[expose] def symEvalOpCode (st : SymState) :
    {as ts : List Ty} → OpCode as ts → Tup (Arg K) as → List SymVal
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
      if n == 64 then [mkAdd (st.evalArg a) (st.evalArg b)] else [.top]
  | _, _, .sub (.bits n), (a, b, ()) =>
      if n == 64 then
        match (st.evalArg a).asConst?, (st.evalArg b).asConst? with
        | some x, some y => [.const (x - y)]
        | _, _ => [.top]
      else [.top]
  | _, _, .or (.bits n), (a, b, ()) =>
      if n == 64 then [mkOrTag (st.evalArg a) (st.evalArg b)] else [.top]
  | _, _, .and (.bits n), (a, b, ()) =>
      if n == 64 then [mkUntag (st.evalArg a) (st.evalArg b)] else [.top]
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

/-- Abstractly interpret one `Op K ts` producing symbolic values in push-order (last = head). -/
@[expose] def symEvalOp (st : SymState) {ts : List Ty} (op : Op K ts) : List SymVal :=
  symEvalOpCode st op.code op.args

/-- Record branch condition facts when descending down `.jnz c t e`. -/
@[expose] def SymState.pushCondFact (st : SymState) (c : Arg K .bool) (taken : Bool) : SymState :=
  if taken then
    match c with
    | .var idx =>
        match st.getSym idx with
        | .cmpUlt lvl bound => { st with facts := .ultBound lvl bound :: st.facts }
        | _ => st
    | .imm _ => st
  else st

/-- Symbolic leaf summary collected from walking a `BlockFlat`. -/
structure SymLeaf : Type where
  path     : BranchPath
  st       : SymState
  target   : Arg K i64
  nextRegs : RegsExpr K

/-- Walk a `BlockFlat` symbolically collecting every `.ijmp` leaf `(path, st, tgt, nxt)`.
Returns `none` if `.hlt` is encountered or `codeAddr sym` fails to resolve in `cm`. -/
@[expose] def symEvalBlock (cm : CodeMap) :
    BlockFlat → BranchPath → SymState → Option (List SymLeaf)
  | .let_ (ts := ts) op k, path, st =>
      symEvalBlock cm k path (st.pushRes ts (symEvalOp st op))
  | .load t _ k, path, st =>
      symEvalBlock cm k path { st with env := .top :: st.env, ctx := t :: st.ctx }
  | .store _ _ k, path, st =>
      symEvalBlock cm k path st
  | .codeAddr sym k, path, st =>
      match cm.addrOf? sym with
      | some a =>
          let sv := if (a &&& 7#64) == 0#64 then .alignedConst a else .const a
          symEvalBlock cm k path { st with env := sv :: st.env, ctx := i64 :: st.ctx }
      | none => none
  | .jnz c t e, path, st => do
      let lt ← symEvalBlock cm t (path ++ [true]) (st.pushCondFact c true)
      let le ← symEvalBlock cm e (path ++ [false]) (st.pushCondFact c false)
      some (lt ++ le)
  | .ijmp tgt nxt, path, st => some [⟨path, st, tgt, nxt⟩]
  | .halt _, _, _ => some []
  | .hlt, _, _ => none

/-! ## §3. Checked `GroupTree`, `RegionWitness`, and `CfgWitness` -/

/-- Push a list of target PCs onto label stack `pcs` matching `pushTup` ordering
(last element ends up at index `0`). -/
@[expose] def pushLabelPcs : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], acc => acc
  | p :: ps, acc => pushLabelPcs ps (p :: acc)

/-- Find the de Bruijn label index for `targetPc` in `pcs`. -/
@[expose] def findLabelIdx (pcs : List (BitVec 64)) (targetPc : BitVec 64) : Option Nat :=
  match pcs with
  | [] => none
  | p :: ps => if p == targetPc then some 0 else (findLabelIdx ps targetPc).map (· + 1)

/-- Look up an edge witness for `(srcPc, path)`. -/
@[expose] def RegionWitness.findEdge (rw : RegionWitness) (srcPc : BitVec 64)
    (path : BranchPath) : Option EdgeWitness :=
  rw.edges.find? fun e => (e.srcPc == srcPc) && (e.path == path)

/-- Validate that `targets` match contiguous 8-byte slots `[base + 0, base + 8, ...]`
and every slot target is in scope in `pcs`. -/
@[expose] def checkStrideTargets (pcs : List (BitVec 64)) (base : BitVec 64) :
    Nat → List (BitVec 64) → Bool
  | _, [] => true
  | idx, t :: ts =>
      (t == base + BitVec.ofNat 64 (8 * idx)) &&
      (findLabelIdx pcs t).isSome &&
      checkStrideTargets pcs base (idx + 1) ts

@[expose] section
/-- Metadata record of an already-checked contified callee region available to callers. -/
structure CalleeMeta : Type where
  name    : Sym
  entryPc : BitVec 64
  dualRet : Bool
  deriving DecidableEq, Repr
end

/-- Verify one `(leaf, edge)` pair against symbolic state `st`, lexical `pcs`, `abi`, and
available contified `callees`. -/
@[expose] def checkEdgeLeaf (cm : CodeMap) (abi : RegionAbi) (callees : List CalleeMeta)
    (pcs : List (BitVec 64)) (leaf : SymLeaf) (kind : EdgeKind) : Bool :=
  let st := leaf.st
  let rpOk := !abi.isContified || st.isRpZero leaf.nextRegs.rp
  match kind with
  | .direct targetPc =>
      rpOk && (st.resolveConst leaf.target == some targetPc) &&
      (findLabelIdx pcs targetPc).isSome
  | .select tPc ePc =>
      rpOk &&
      (findLabelIdx pcs tPc).isSome &&
      (findLabelIdx pcs ePc).isSome &&
      match st.evalArg leaf.target with
      | .ite cLvl tSym eSym =>
          st.levelHasTy cLvl .bool &&
          (tSym.asConst? == some tPc) &&
          (eSym.asConst? == some ePc)
      | _ => false
  | .strideTable basePc targets needGuard =>
      rpOk && (!targets.isEmpty) &&
      checkStrideTargets pcs basePc 0 targets &&
      match st.evalArg leaf.target with
      | .stride b lvl =>
          (b == basePc) && st.levelHasTy lvl i64 &&
          if needGuard then !abi.isContified
          else st.hasUltBound lvl targets.length
      | _ => false
  | .contCall callee calleePc dualRet retPc altRetPc? =>
      (!abi.isContified) &&
      (cm.addrOf? callee == some calleePc) &&
      (st.resolveConst leaf.target == some calleePc) &&
      (st.resolveConst leaf.nextRegs.rp == some retPc) &&
      (findLabelIdx pcs retPc).isSome &&
      callees.any (fun c =>
        (c.name == callee) && (c.entryPc == calleePc) && (c.dualRet == dualRet)) &&
      if dualRet then
        (altRetPc? == some (retPc + 8#64)) &&
        (findLabelIdx pcs (retPc + 8#64)).isSome
      else
        altRetPc?.isNone
  | .contRet isAlt =>
      match abi with
      | .contified dualRet =>
          ((!isAlt) || dualRet) &&
          (st.evalArg leaf.target == .rpOffset (if isAlt then 8#64 else 0#64))
      | .retEnvelope => false
  | .guarded hotTargets =>
      (!abi.isContified) &&
      hotTargets.all (fun p => (findLabelIdx pcs p).isSome)
  | .bailout => !abi.isContified

/-- Verify all leaves of a block at `pc` inside lexical scope `pcs`. -/
@[expose] def checkBlockLeaves (cm : CodeMap) (rw : RegionWitness) (callees : List CalleeMeta)
    (pcs : List (BitVec 64)) (pc : BitVec 64) : Bool :=
  match cm.lookupAddr pc with
  | none => false
  | some b =>
      b.wfCheck regCtx && b.noHlt &&
      match symEvalBlock cm b [] SymState.init with
      | none => false
      | some leaves =>
          leaves.all fun leaf =>
            match rw.findEdge pc leaf.path with
            | none => false
            | some ew => checkEdgeLeaf cm rw.abi callees pcs leaf ew.kind

mutual
/-- Verify WTO scoping and leaf edge soundness across a `GroupTree` list. -/
@[expose] def checkGroupNodes (cm : CodeMap) (rw : RegionWitness) (callees : List CalleeMeta)
    (pcs : List (BitVec 64)) : List GroupTree → Bool
  | [] => true
  | g :: gs => checkGroupNode cm rw callees pcs g && checkGroupNodes cm rw callees pcs gs

/-- Verify one `GroupTree` node inside `pcs`. -/
@[expose] def checkGroupNode (cm : CodeMap) (rw : RegionWitness) (callees : List CalleeMeta)
    (pcs : List (BitVec 64)) : GroupTree → Bool
  | .leaf pc => checkBlockLeaves cm rw callees pcs pc
  | .loop header nodes =>
      let entries := nodes.map GroupTree.entryPc
      let pcsInner := pushLabelPcs entries pcs
      (!nodes.isEmpty) &&
      entries.contains header &&
      checkGroupNodes cm rw callees pcsInner nodes
end

/-! ## §4. Deterministic `TFlat` Region Lowerer -/

/-- Shift all de Bruijn variable indices in `Arg K t` outward by `k`. -/
@[expose] def shiftArg (k : Nat) {t : Ty} : Arg K t → Arg K t
  | .var i => .var (i + k)
  | .imm c => .imm c

/-- Shift all de Bruijn variable indices in `RegsExpr K` outward by `k`. -/
@[expose] def shiftRegsExpr (k : Nat) (e : RegsExpr K) : RegsExpr K :=
  ⟨shiftArg k e.sp, shiftArg k e.rp, shiftArg k e.rv,
   shiftArg k e.r1, shiftArg k e.r2, shiftArg k e.r3⟩

/-- Canonical 6-register tuple arguments `(sp, rp, rv, r1, r2, r3)` at base depth (`5..0`). -/
@[expose] def baseRegArgs : Tup (Arg K) regSig :=
  (.var 5, .var 4, .var 3, .var 2, .var 1, .var 0, ())

/-- Build a 7-register envelope `.ret` terminator from shifted `tgt` and `nxt`. -/
@[expose] def mkRetEnvelope (tgt : Arg K i64) (nxt : RegsExpr K) :
    TFlat (RegionAbi.retEnvelope.retSig) :=
  .ret (tgt, nxt.sp, nxt.rp, nxt.rv, nxt.r1, nxt.r2, nxt.r3, ())

/-- Lower a jump to known `targetPc` in `pcs`. -/
@[expose] def lowerJumpTo {rs : List Ty} (pcs : List (BitVec 64)) (targetPc : BitVec 64)
    (nxt : RegsExpr K) : TFlat rs :=
  match findLabelIdx pcs targetPc with
  | some j => .jump (ts := regSig) j nxt.toTup
  | none => .hlt

/-- Lower contiguous bounded jump-table dispatch `base + 8 * k ↦ targets[k]` (0 `.hlt`s). -/
@[expose] def lowerStrideCascade {rs : List Ty} (pcs : List (BitVec 64)) (idxVar : Nat)
    (nxt : RegsExpr K) : Nat → Nat → List (BitVec 64) → TFlat rs
  | _, _, [] => .hlt
  | _, curShift, [lastPc] => lowerJumpTo pcs lastPc (shiftRegsExpr curShift nxt)
  | k, curShift, tPc :: rest =>
      let eqOp : Op K [.bool] := op2 (.cmp .eq i64) (.var (idxVar + curShift))
        (.imm (BitVec.ofNat 64 k))
      .let_ eqOp
        (.jnz (.var 0)
          (lowerJumpTo pcs tPc (shiftRegsExpr (curShift + 1) nxt))
          (lowerStrideCascade pcs idxVar nxt (k + 1) (curShift + 1) rest))

/-- Lower speculative `guarded` hot-target cascade with cold `.ret` bailout fallback. -/
@[expose] def lowerGuardedCascade (pcs : List (BitVec 64)) (tgt : Arg K i64)
    (nxt : RegsExpr K) : Nat → List (BitVec 64) → TFlat RegionAbi.retEnvelope.retSig
  | curShift, [] => mkRetEnvelope (shiftArg curShift tgt) (shiftRegsExpr curShift nxt)
  | curShift, hPc :: rest =>
      let eqOp : Op K [.bool] := op2 (.cmp .eq i64) (shiftArg curShift tgt) (.imm hPc)
      .let_ eqOp
        (.jnz (.var 0)
          (lowerJumpTo pcs hPc (shiftRegsExpr (curShift + 1) nxt))
          (lowerGuardedCascade pcs tgt nxt (curShift + 1) rest))

/-- Lower one checked `(ijmp tgt nxt, edgeKind)` leaf at `st` into `TFlat abi.retSig`. -/
@[expose] def liftEdge (abi : RegionAbi) (pcs : List (BitVec 64)) (st : SymState)
    (tgt : Arg K i64) (nxt : RegsExpr K) (kind : EdgeKind) : TFlat abi.retSig :=
  match abi, kind with
  | _, .direct targetPc => lowerJumpTo pcs targetPc nxt
  | _, .select tPc ePc =>
      match st.evalArg tgt with
      | .ite cLvl _ _ =>
          let cIdx := st.env.length - 1 - cLvl
          .jnz (.var cIdx) (lowerJumpTo pcs tPc nxt) (lowerJumpTo pcs ePc nxt)
      | _ => .hlt
  | _, .strideTable _ targets false =>
      match st.evalArg tgt with
      | .stride _ lvl =>
          let idxVar := st.env.length - 1 - lvl
          lowerStrideCascade pcs idxVar nxt 0 0 targets
      | _ => .hlt
  | .retEnvelope, .strideTable _ targets true =>
      match st.evalArg tgt with
      | .stride _ lvl =>
          let idxVar := st.env.length - 1 - lvl
          let boundOp : Op K [.bool] :=
            op2 (.cmp .ult i64) (.var idxVar) (.imm (BitVec.ofNat 64 targets.length))
          .let_ boundOp
            (.jnz (.var 0)
              (lowerStrideCascade pcs idxVar nxt 0 1 targets)
              (mkRetEnvelope (shiftArg 1 tgt) (shiftRegsExpr 1 nxt)))
      | _ => .hlt
  | .retEnvelope, .contCall callee _ dualRet retPc altRetPc? =>
      let retSigC := (RegionAbi.contified dualRet).retSig
      if dualRet then
        match altRetPc? with
        | some altPc =>
            .call callee retSigC nxt.toTup
              (.jnz (.var 6)
                (lowerJumpTo pcs altPc ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)
                (lowerJumpTo pcs retPc ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩))
        | none => .hlt
      else
        .call callee retSigC nxt.toTup
          (lowerJumpTo pcs retPc ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)
  | .contified false, .contRet false => .ret nxt.toTup
  | .contified true, .contRet isAlt => .ret (.imm isAlt, nxt.toTup)
  | .retEnvelope, .guarded hotTargets => lowerGuardedCascade pcs tgt nxt 0 hotTargets
  | .retEnvelope, .bailout => mkRetEnvelope tgt nxt
  | _, _ => .hlt

/-- Lower a `BlockFlat` inside `rw` and lexical `pcs` into `TFlat rw.abi.retSig`. -/
@[expose] def liftBlock (cm : CodeMap) (rw : RegionWitness) (pcs : List (BitVec 64))
    (pc : BitVec 64) : BlockFlat → BranchPath → SymState → TFlat rw.abi.retSig
  | .let_ (ts := ts) op k, path, st =>
      .let_ op (liftBlock cm rw pcs pc k path (st.pushRes ts (symEvalOp st op)))
  | .load t a k, path, st =>
      .load t a (liftBlock cm rw pcs pc k path
        { st with env := .top :: st.env, ctx := t :: st.ctx })
  | .store v a k, path, st =>
      .store v a (liftBlock cm rw pcs pc k path st)
  | .codeAddr sym k, path, st =>
      match cm.addrOf? sym with
      | some a =>
          let sv := if (a &&& 7#64) == 0#64 then .alignedConst a else .const a
          .let_ (op1 (.copy i64) (.imm a))
            (liftBlock cm rw pcs pc k path
              { st with env := sv :: st.env, ctx := i64 :: st.ctx })
      | none => .hlt
  | .jnz c t e, path, st =>
      .jnz c
        (liftBlock cm rw pcs pc t (path ++ [true]) (st.pushCondFact c true))
        (liftBlock cm rw pcs pc e (path ++ [false]) (st.pushCondFact c false))
  | .ijmp tgt nxt, path, st =>
      match rw.findEdge pc path with
      | some ew => liftEdge rw.abi pcs st tgt nxt ew.kind
      | none => .hlt
  | .halt c, _, _ => .exit haltSym (as := [i64]) (c, ())
  | .hlt, _, _ => .hlt

mutual
/-- Lower a `GroupTree` node into its entry-parameterized `TFlat rw.abi.retSig` body. -/
@[expose] def liftGroupNode (cm : CodeMap) (rw : RegionWitness) (pcs : List (BitVec 64)) :
    GroupTree → TFlat rw.abi.retSig
  | .leaf pc =>
      match cm.lookupAddr pc with
      | some b => liftBlock cm rw pcs pc b [] SymState.init
      | none => .hlt
  | .loop header nodes =>
      let entries := nodes.map GroupTree.entryPc
      let pcsInner := pushLabelPcs entries pcs
      let bodies := liftGroupNodes cm rw pcsInner nodes
      .group bodies (lowerJumpTo pcsInner header ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)

/-- Lower a list of `GroupTree` nodes into `TBlocks rw.abi.retSig`. -/
@[expose] def liftGroupNodes (cm : CodeMap) (rw : RegionWitness) (pcs : List (BitVec 64)) :
    (gs : List GroupTree) → TBlocks rw.abi.retSig (gs.map fun _ => regSig)
  | [] => .nil
  | g :: gs => .cons (liftGroupNode cm rw pcs g) (liftGroupNodes cm rw pcs gs)
end

/-- Lower an entire `RegionWitness` into its root `TFlat rw.abi.retSig`. -/
@[expose] def liftRegionTFlat (cm : CodeMap) (rw : RegionWitness) : TFlat rw.abi.retSig :=
  let entries := rw.tree.map GroupTree.entryPc
  let pcs := pushLabelPcs entries []
  let bodies := liftGroupNodes cm rw pcs rw.tree
  .group bodies (lowerJumpTo pcs rw.entryPc ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)

/-- Computable verifier checking ALL safety/WTO/typing conditions for one `RegionWitness`. -/
@[expose] def RegionWitness.check (cm : CodeMap) (callees : List CalleeMeta)
    (rw : RegionWitness) : Bool :=
  let entries := rw.tree.map GroupTree.entryPc
  let pcs := pushLabelPcs entries []
  let tf := liftRegionTFlat cm rw
  fnNameOk rw.name &&
  (!rw.tree.isEmpty) &&
  (cm.lookupAddr rw.entryPc).isSome &&
  entries.contains rw.entryPc &&
  listNodup rw.allPcs &&
  checkGroupNodes cm rw callees pcs rw.tree &&
  tf.wfCheck regCtx [] &&
  tf.noHlt

/-- Deterministic lifting from `RegionWitness` to typed `LeanQbe.T.Fn`. -/
@[expose] def liftRegion (cm : CodeMap) (rw : RegionWitness) : Fn where
  name := rw.name
  as := regSig
  rs := rw.abi.retSig
  body := denoteFunc (liftRegionTFlat cm rw)

/-- Verify `rw` and lift it to a `LeanQbe.T.Fn`. -/
@[expose] def checkAndLiftRegion (cm : CodeMap) (callees : List CalleeMeta)
    (rw : RegionWitness) : Except String Fn :=
  if rw.check cm callees then .ok (liftRegion cm rw)
  else .error s!"CfgRecovery: region check failed for {rw.name}"

/-- Convert a `RegionWitness` into `CalleeMeta` if `rw.abi = .contified dualRet`. -/
@[expose] def RegionWitness.toCalleeMeta? (rw : RegionWitness) : Option CalleeMeta :=
  match rw.abi with
  | .contified dualRet => some ⟨rw.name, rw.entryPc, dualRet⟩
  | .retEnvelope => none

/-- Computable verifier checking region disjointness, naming, and callee-first DAG order. -/
@[expose] def CfgWitness.checkAux (cm : CodeMap) (callees : List CalleeMeta) :
    List RegionWitness → Bool
  | [] => true
  | rw :: rws =>
      rw.check cm callees &&
      let callees' := match rw.toCalleeMeta? with
        | some c => c :: callees
        | none => callees
      CfgWitness.checkAux cm callees' rws

/-- Verify all regions in `wit` are well-formed, disjoint, distinctly named, and acyclic. -/
@[expose] def CfgWitness.check (cm : CodeMap) (wit : CfgWitness) : Bool :=
  listNodup (wit.regions.map (·.name)) &&
  listNodup (wit.regions.flatMap RegionWitness.allPcs) &&
  CfgWitness.checkAux cm [] wit.regions

/-- Compute residual `CodeMap` `W_res`: if `retainFallbacks = true`, retains all blocks NOT
replaced at a region entry (`rw.entryPc`); otherwise excludes all `wit` blocks. -/
@[expose] def residualCodeMap (cm : CodeMap) (wit : CfgWitness) : CodeMap :=
  let entries := wit.regions.map (·.entryPc)
  let dropAll := (wit.regions.filter (fun r => !r.retainFallbacks)).flatMap RegionWitness.allPcs
  cm.filter fun e => (!entries.contains e.addr) && (!dropAll.contains e.addr)

/-- Verified whole-witness lifting returning `(liftedFns, W_res)` in region order. -/
@[expose] def checkAndLiftWitness (cm : CodeMap) (wit : CfgWitness) :
    Except String (List Fn × CodeMap) :=
  if wit.check cm then
    .ok (wit.regions.map (liftRegion cm), residualCodeMap cm wit)
  else
    .error "CfgRecovery: witness check failed"

/-! ## §5. Untrusted Heuristic CFG Recovery (`analyzeCfg`) -/

private def countContiguousPads (cm : CodeMap) (base : BitVec 64) : Nat → Nat → List (BitVec 64)
  | 0, _ => []
  | fuel + 1, idx =>
      let addr := base + BitVec.ofNat 64 (8 * idx)
      match cm.lookupAddr addr with
      | some _ => addr :: countContiguousPads cm base fuel (idx + 1)
      | none => []

private def detectStrideTargets (cm : CodeMap) (st : SymState) (base : BitVec 64)
    (lvl : Nat) : Option (List (BitVec 64) × Bool) :=
  let maxPads := 16
  let pads := countContiguousPads cm base maxPads 0
  if pads.isEmpty then none
  else
    let bounded := (List.range maxPads).find? fun k => k > 0 && st.hasUltBound lvl k
    match bounded with
    | some k => if k ≤ pads.length then some (pads.take k, false) else some (pads, true)
    | none => some (pads, true)

private def isDualReturn (cm : CodeMap) (entries : List CodeEntry) : Option (Sym × Bool) :=
  match entries with
  | [] => none
  | e :: _ =>
      match symEvalBlock cm e.block [] SymState.init with
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

private def classifyCallees (cm : CodeMap) : List (CodeEntry × Bool) :=
  cm.filterMap fun e =>
    match isDualReturn cm [e] with
    | some (_, dual) => some (e, dual)
    | none => none

private def classifyLeaf (cm : CodeMap) (calleeMap : List (CodeEntry × Bool))
    (srcPc : BitVec 64) (leaf : SymLeaf) : EdgeWitness × List (BitVec 64) :=
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
      match detectStrideTargets cm st base lvl with
      | some (pads, needG) =>
          (⟨srcPc, leaf.path, .strideTable base pads needG⟩, pads)
      | none => (⟨srcPc, leaf.path, .bailout⟩, [])
  | _ => (⟨srcPc, leaf.path, .bailout⟩, [])

private partial def collectReachable (cm : CodeMap) (calleeMap : List (CodeEntry × Bool))
    (claimed : List (BitVec 64)) (work : List (BitVec 64)) (visited : List (BitVec 64))
    (edges : List EdgeWitness) : List (BitVec 64) × List EdgeWitness :=
  match work with
  | [] => (visited, edges)
  | pc :: rest =>
      if visited.contains pc || claimed.contains pc then
        collectReachable cm calleeMap claimed rest visited edges
      else
        match cm.lookupAddr pc with
        | none => collectReachable cm calleeMap claimed rest visited edges
        | some b =>
            match symEvalBlock cm b [] SymState.init with
            | none => collectReachable cm calleeMap claimed rest visited edges
            | some leaves =>
                let pairs := leaves.map (classifyLeaf cm calleeMap pc)
                let newEdges := pairs.map Prod.fst
                let nextPcs := (pairs.flatMap Prod.snd).filter
                  fun p => !visited.contains p && !claimed.contains p && (cm.lookupAddr p).isSome
                collectReachable cm calleeMap claimed (nextPcs ++ rest)
                  (pc :: visited) (edges ++ newEdges)

private def isBailoutEdge (ew : EdgeWitness) : Bool :=
  match ew.kind with
  | .bailout => true
  | _ => false

private def directSuccsOf (edges : List EdgeWitness) (pc : BitVec 64) : List (BitVec 64) :=
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

private partial def reachFrom (edges : List EdgeWitness) (allowed : List (BitVec 64)) :
    List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], vis => vis
  | p :: ps, vis =>
      if vis.contains p || !allowed.contains p then reachFrom edges allowed ps vis
      else
        let succs := (directSuccsOf edges p).filter allowed.contains
        reachFrom edges allowed (succs ++ ps) (p :: vis)

private def buildLoopTree (edges : List EdgeWitness) (pcs : List (BitVec 64)) : List GroupTree :=
  -- Identify backedge headers: nodes reachable from one of their own successors.
  let headers := pcs.filter fun h =>
    let r := reachFrom edges pcs (directSuccsOf edges h) []
    r.contains h
  match headers with
  | h :: _ =>
      -- Partition blocks that can reach `h` inside the loop body (entered solely via `h`).
      let rFromH := reachFrom edges pcs [h] []
      let loopBody := rFromH.filter fun u =>
        u == h || (reachFrom edges pcs (directSuccsOf edges u) []).contains h
      let outerEntrants := pcs.filter fun p =>
        !loopBody.contains p &&
        (directSuccsOf edges p).any (fun s => s != h && loopBody.contains s)
      if loopBody.length ≥ 1 && outerEntrants.isEmpty then
        let rest := pcs.filter (fun p => !loopBody.contains p)
        let loopNodes := .leaf h :: (loopBody.filter (· != h)).map .leaf
        (.loop h loopNodes) :: rest.map .leaf
      else pcs.map .leaf
  | [] => pcs.map .leaf

/-- Untrusted heuristic CFG analyzer recovering contified callees, direct/select/stride edges,
Bourdoncle-style single-entry `GroupTree` loops, and speculative guarded bailouts.
Every emitted witness is verified with `CfgWitness.check cm`. -/
def analyzeCfg (cm : CodeMap) : Option CfgWitness :=
  let calleeEntries := classifyCallees cm
  let calleeRegs : List RegionWitness := (calleeEntries.map fun (ce, dual) =>
    let leaves := (symEvalBlock cm ce.block [] SymState.init).getD []
    let es := leaves.map fun l =>
      let isAlt := l.st.evalArg l.target == .rpOffset 8#64
      ⟨ce.addr, l.path, .contRet isAlt⟩
    ⟨ce.name, ce.addr, .contified dual, [.leaf ce.addr], es, true⟩).filter (·.check cm [])
  let calleeMeta := calleeRegs.filterMap RegionWitness.toCalleeMeta?
  let validCalleeEntries := calleeEntries.filter fun (ce, _) =>
    calleeRegs.any (fun rw => rw.entryPc == ce.addr)
  let claimedInit := calleeRegs.map (·.entryPc)
  let callerStep := cm.foldl (fun (acc : List (BitVec 64) × List RegionWitness) e =>
    let (claimed, regs) := acc
    if claimed.contains e.addr then acc
    else
      let (pcsRev, rawEdges) := collectReachable cm validCalleeEntries claimed [e.addr] [] []
      let pcs := pcsRev.reverse
      if pcs.isEmpty then acc
      else
        let tree := buildLoopTree rawEdges pcs
        let rw : RegionWitness :=
          ⟨e.name ++ "_reg", e.addr, .retEnvelope, tree, rawEdges, true⟩
        if rw.check cm calleeMeta then
          (pcs ++ claimed, regs ++ [rw])
        else acc) (claimedInit, [])
  let wit : CfgWitness := ⟨calleeRegs ++ callerStep.2⟩
  if wit.regions.isEmpty || !wit.check cm then none else some wit

end LeanQbe.T.Unified
