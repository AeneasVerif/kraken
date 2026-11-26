module

public import LeanQbe.T.FlatDirect
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.Licm
public import LeanQbe.T.LoopRotate

/-!
# Native `TFlat` Loop Optimizations (`OptFlatLoop`)

Direct `TFlat rs → TFlat rs` implementations of `Func.licm` (`OptFlatLoop.licmFlat`) and
`Func.loopRotate` (`OptFlatLoop.loopRotateFlat`) using structural recursion (`0` `WellFounded.fix`,
`0` `Classical.choice`, `0` PHOAS closure roundtrips):

* `OptFlatLoop.licmFlat`: two-stage pure-total LICM (`licmPureFlat`), read-only loop load hoisting
  and forwarding (`roSweepFlat`), and follow-up `licmPureFlat` when loads move.
* `OptFlatLoop.loopRotateFlat`: `buildRotPlan` gate, structural `BoolL` + header/mask validator
  (`validateRotPlanFlat`), and zero-shift `RotLFlat` rewriter (`rewriteRotFlat`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatLoop

open OptFlatPlanKit

/-! ## 1. Native `TFlat` Loop-Invariant Code Motion (`licmFlat`) -/

/-- Result of emitting a validated prefix of hoisted pure-total `.let_` bindings on `TFlat`. -/
structure HoistEmitRes (rs : List Ty) where
  wrap : TFlat rs → TFlat rs
  next : Nat
  env : VEnv K
  tbl : GvnTbl K
  outDepth : Nat

/-- Emit a validated prefix of hoisted pure-total `.let_` bindings before a `.group`, extending
`next`, `env`, `tbl`, and `outDepth`. Matches `emitHoists` on `(K, KL)`. -/
def emitHoistsFlat {rs : List Ty} :
    List HoistOp → Nat → VEnv K → GvnTbl K → Nat → HoistEmitRes rs
  | [], next, env, tbl, outD => ⟨id, next, env, tbl, outD⟩
  | h :: rest, next, env, tbl, outD =>
    if h.code.isLicmPure then
      match tbl.find h.sig h.ts h.code h.args with
      | some _ => emitHoistsFlat rest next env tbl outD
      | none =>
        match resolveArgs env h.args with
        | some vArgs =>
          let xs := Tup.levels h.ts outD
          let gs := freshGVals h.ts xs next
          let env' := envInsertTup env next xs
          let tbl' := tbl.insert h.sig h.ts h.code h.args gs
          let r := emitHoistsFlat rest (next + h.ts.length) env' tbl' (outD + h.ts.length)
          ⟨fun tail => .let_ ⟨h.code, idxArgs outD vArgs⟩ (r.wrap tail),
            r.next, r.env, r.tbl, r.outDepth⟩
        | none => emitHoistsFlat rest next env tbl outD
    else
      emitHoistsFlat rest next env tbl outD

mutual
/-- Native `TFlat` LICM sweep matching `licmSweep` on `(GVal K, KL)`. -/
def licmSweepFlat {rs : List Ty} (next : Nat) (env : VEnv K) (tbl : GvnTbl K)
    (plan : HoistPlan) :
    TFlat rs → Nat → Trie ((t : Ty) × GVal K t) → Nat → TFlat rs
  | .let_ (ts := ts) op k, inD, inE, outD =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    let gArgs := resolveEnvArgs inD inE op.args
    let kArgs := tupGKey gArgs
    match tbl.find op.sig ts op.code kArgs with
    | some cached =>
      licmSweepFlat next env tbl kPlan k (inD + ts.length) (insertTupEnv inD inE cached) outD
    | none =>
      let xs := Tup.levels ts outD
      let gs := freshGVals ts xs next
      .let_ ⟨op.code, idxArgs outD (tupGOut gArgs)⟩
        (licmSweepFlat (next + ts.length) (envInsertTup env next xs) tbl kPlan k
          (inD + ts.length) (insertTupEnv inD inE gs) (outD + ts.length))
  | .load t a k, inD, inE, outD =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    let a' := (resolveEnvArg inD inE a).gout
    .load t (idxArg outD a')
      (licmSweepFlat (next + 1) (env.insert next ⟨t, outD⟩) tbl kPlan k
        (inD + 1) (inE.insert inD ⟨t, (outD, next)⟩) (outD + 1))
  | .store v a k, inD, inE, outD =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    let v' := (resolveEnvArg inD inE v).gout
    let a' := (resolveEnvArg inD inE a).gout
    .store (idxArg outD v') (idxArg outD a') (licmSweepFlat next env tbl kPlan k inD inE outD)
  | .call f bs args k, inD, inE, outD =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    let args' := tupGOut (resolveEnvArgs inD inE args)
    let xs := Tup.levels bs outD
    let gs := freshGVals bs xs next
    .call f bs (idxArgs outD args')
      (licmSweepFlat (next + bs.length) (envInsertTup env next xs) tbl kPlan k
        (inD + bs.length) (insertTupEnv inD inE gs) (outD + bs.length))
  | .jnz c t e, inD, inE, outD =>
    let (pt, pe) := match plan with | .node2 pt pe => (pt, pe) | _ => (.leaf, .leaf)
    let c' := (resolveEnvArg inD inE c).gout
    .jnz (idxArg outD c')
      (licmSweepFlat next env tbl pt t inD inE outD)
      (licmSweepFlat next env tbl pe e inD inE outD)
  | .jump j args, inD, inE, outD =>
    .jump j (idxArgs outD (tupGOut (resolveEnvArgs inD inE args)))
  | .ret vs, inD, inE, outD =>
    .ret (idxArgs outD (tupGOut (resolveEnvArgs inD inE vs)))
  | .exit f args, inD, inE, outD =>
    .exit f (idxArgs outD (tupGOut (resolveEnvArgs inD inE args)))
  | .hlt, _, _, _ => .hlt
  | .group bodies k, inD, inE, outD =>
    let (hoists, bsPlan, kPlan) := match plan with
      | .groupNode hs bsP kP => (hs, bsP, kP)
      | _ => ([], .nil, .leaf)
    let r := emitHoistsFlat hoists next env tbl outD
    r.wrap (.group
      (licmSweepBFlat r.next r.env r.tbl bsPlan bodies inD inE r.outDepth)
      (licmSweepFlat r.next r.env r.tbl kPlan k inD inE r.outDepth))

/-- Block-list companion of `licmSweepFlat`. -/
def licmSweepBFlat {rs : List Ty} (next : Nat) (env : VEnv K) (tbl : GvnTbl K)
    (bsPlan : HoistBlocks) :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × GVal K t) → Nat →
    TBlocks rs sig
  | _, .nil, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inD, inE, outD =>
    let (ph, pt) := match bsPlan with | .cons ph pt => (ph, pt) | _ => (.leaf, .nil)
    let xs := Tup.levels ts outD
    let gs := freshGVals ts xs next
    .cons
      (licmSweepFlat (next + ts.length) (envInsertTup env next xs) tbl ph b
        (inD + ts.length) (insertTupEnv inD inE gs) (outD + ts.length))
      (licmSweepBFlat next env tbl pt bs inD inE outD)
end

/-- Native `TFlat` pure Loop-Invariant Code Motion matching `reifyFunc (Func.licmPure ...)`. -/
def licmPureFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  let plan := Licm.buildHoistPlan as.length tf
  if plan.hasHoists then
    let xs := Tup.levels as 0
    licmSweepFlat as.length (insertTupEnv 0 .empty xs) .empty plan tf
      as.length (initEnv (fun x next => (x, next)) as) as.length
  else tf

/-- Result of emitting hoisted `.load`s before a clean `.group` on `TFlat`. -/
structure RoEmitRes (rs : List Ty) where
  wrap : TFlat rs → TFlat rs
  next : Nat
  env : VEnv K
  outDepth : Nat

/-- Emit hoisted `.load`s before a clean `.group` on `TFlat`, matching `emitRoHoists`. -/
def emitRoHoistsFlat {rs : List Ty} :
    List HoistLoad → Nat → VEnv K → Nat → RoEmitRes rs
  | [], next, env, outD => ⟨id, next, env, outD⟩
  | h :: rest, next, env, outD =>
    match resolveArg env h.addr with
    | some va =>
      let r := emitRoHoistsFlat rest (next + 1) (env.insert next ⟨h.ty, outD⟩) (outD + 1)
      ⟨fun tail => .load h.ty (idxArg outD va) (r.wrap tail), r.next, r.env, r.outDepth⟩
    | none => emitRoHoistsFlat rest next env outD

mutual
/-- Native `TFlat` read-only loop load hoisting and dominating load forwarding sweep matching
`roSweep` on `(K, KL)`. -/
def roSweepFlat {rs : List Ty} (next : Nat) (env : VEnv K) (plan : RoPlan) :
    TFlat rs → Nat → Trie ((t : Ty) × K t) → Nat → TFlat rs
  | .let_ (ts := ts) op k, inD, inE, outD =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    let args' := resolveEnvArgs inD inE op.args
    let xs := Tup.levels ts outD
    .let_ ⟨op.code, idxArgs outD args'⟩
      (roSweepFlat (next + ts.length) (envInsertTup env next xs) kPlan k
        (inD + ts.length) (insertTupEnv inD inE xs) (outD + ts.length))
  | .load t a k, inD, inE, outD =>
    let a' := resolveEnvArg inD inE a
    match plan with
    | .fwdLoad lvl kPlan =>
      match env.find? lvl with
      | some ⟨t', v⟩ =>
        if h : t' = t then
          roSweepFlat next env kPlan k (inD + 1) (inE.insert inD ⟨t, h ▸ v⟩) outD
        else
          .load t (idxArg outD a')
            (roSweepFlat (next + 1) (env.insert next ⟨t, outD⟩) kPlan k
              (inD + 1) (inE.insert inD ⟨t, outD⟩) (outD + 1))
      | none =>
        .load t (idxArg outD a')
          (roSweepFlat (next + 1) (env.insert next ⟨t, outD⟩) kPlan k
            (inD + 1) (inE.insert inD ⟨t, outD⟩) (outD + 1))
    | _ =>
      let kPlan := match plan with | .node1 p => p | _ => .leaf
      .load t (idxArg outD a')
        (roSweepFlat (next + 1) (env.insert next ⟨t, outD⟩) kPlan k
          (inD + 1) (inE.insert inD ⟨t, outD⟩) (outD + 1))
  | .store v a k, inD, inE, outD =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    let v' := resolveEnvArg inD inE v
    let a' := resolveEnvArg inD inE a
    .store (idxArg outD v') (idxArg outD a') (roSweepFlat next env kPlan k inD inE outD)
  | .call f bs args k, inD, inE, outD =>
    let kPlan := match plan with | .node1 p => p | _ => .leaf
    let args' := resolveEnvArgs inD inE args
    let xs := Tup.levels bs outD
    .call f bs (idxArgs outD args')
      (roSweepFlat (next + bs.length) (envInsertTup env next xs) kPlan k
        (inD + bs.length) (insertTupEnv inD inE xs) (outD + bs.length))
  | .jnz c t e, inD, inE, outD =>
    let (tPlan, ePlan) := match plan with | .node2 tp ep => (tp, ep) | _ => (.leaf, .leaf)
    let c' := resolveEnvArg inD inE c
    .jnz (idxArg outD c')
      (roSweepFlat next env tPlan t inD inE outD)
      (roSweepFlat next env ePlan e inD inE outD)
  | .jump j args, inD, inE, outD =>
    .jump j (idxArgs outD (resolveEnvArgs inD inE args))
  | .ret vs, inD, inE, outD =>
    .ret (idxArgs outD (resolveEnvArgs inD inE vs))
  | .exit f args, inD, inE, outD =>
    .exit f (idxArgs outD (resolveEnvArgs inD inE args))
  | .hlt, _, _, _ => .hlt
  | .group bodies k, inD, inE, outD =>
    let (hoists, bsPlan, kPlan) := match plan with
      | .groupNode hs bsP kP => (hs, bsP, kP)
      | _ => ([], .nil, .leaf)
    let r := emitRoHoistsFlat hoists next env outD
    r.wrap (.group
      (roSweepBFlat r.next r.env bsPlan bodies inD inE r.outDepth)
      (roSweepFlat r.next r.env kPlan k inD inE r.outDepth))

/-- Block-list companion of `roSweepFlat`. -/
def roSweepBFlat {rs : List Ty} (next : Nat) (env : VEnv K) (plan : RoBlocks) :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × K t) → Nat → TBlocks rs sig
  | _, .nil, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inD, inE, outD =>
    let (hdP, tlP) := match plan with | .cons hd tl => (hd, tl) | _ => (.leaf, .nil)
    let xs := Tup.levels ts outD
    .cons
      (roSweepFlat (next + ts.length) (envInsertTup env next xs) hdP b
        (inD + ts.length) (insertTupEnv inD inE xs) (outD + ts.length))
      (roSweepBFlat next env tlP bs inD inE outD)
end

/-- Direct `TFlat` Loop-Invariant Code Motion matching `reifyFunc (Func.licm (denoteFunc tf))`. -/
def licmFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  let tf1 := licmPureFlat as tf
  let plan := Licm.buildRoPlan as.length tf1
  if plan.hasChanges then
    let initE := insertTupEnv 0 .empty (Tup.levels as 0)
    let tf2 := roSweepFlat as.length initE plan tf1 as.length initE as.length
    licmPureFlat as tf2
  else tf1

/-- `TFlatFn` wrapper for `licmFlat`. -/
def licmFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, licmFlat f.as f.body⟩

/-! ## 2. Native `TFlat` CFG Loop Rotation (`loopRotateFlat`) -/

section LoopRotateFlat
open LoopRotate

/-- Output-level-based `TFlat` label payload for zero-shift loop rotation (`RotL K KL rs`). -/
inductive RotLFlat (rs : List Ty) : List Ty → Type
  | keep {ts : List Ty} (outLbl : Nat) : RotLFlat rs ts
  | expand {ts : List Ty} (f : Nat → Nat → Tup (Arg K) ts → TFlat rs) : RotLFlat rs ts
  | expandOrKeep {ts : List Ty} (f : Nat → Nat → Tup (Arg K) ts → TFlat rs) (lHdr : Nat) :
      RotLFlat rs ts
  | dead {ts : List Ty} : RotLFlat rs ts

/-- Wrap outer output label levels into `RotLFlat.keep`. -/
def wrapKeepLabelsFlat {rs : List Ty} :
    {sig : List (List Ty)} → Tup KL sig → Tup (RotLFlat rs) sig
  | [], () => ()
  | _ :: _, (l, ls) => (.keep l, wrapKeepLabelsFlat ls)

mutual
/-- Native `TFlat` mirror of `LoopRotate.validateLeaf`. -/
def validateLeafFlat {rs : List Ty} :
    TFlat rs → Nat → Nat → Trie ((ts : List Ty) × BoolL ts) → Option (Trie Unit)
  | .let_ (ts := ts) op k, nv, inLD, inLE => do
    let s ← validateLeafFlat k (nv + ts.length) inLD inLE
    pure (addArgKeys (levelArgs nv op.args) s)
  | .load _ a k, nv, inLD, inLE => do
    let s ← validateLeafFlat k (nv + 1) inLD inLE
    pure (addArgKey (levelArg nv a) s)
  | .store v a k, nv, inLD, inLE => do
    let s ← validateLeafFlat k nv inLD inLE
    pure (addArgKey (levelArg nv v) (addArgKey (levelArg nv a) s))
  | .call _ bs args k, nv, inLD, inLE => do
    let s ← validateLeafFlat k (nv + bs.length) inLD inLE
    pure (addArgKeys (levelArgs nv args) s)
  | .jnz c t e, nv, inLD, inLE => do
    let st ← validateLeafFlat t nv inLD inLE
    let se ← validateLeafFlat e nv inLD inLE
    pure (addArgKey (levelArg nv c) (trieUnion st se))
  | .jump (ts := ts) j args, nv, inLD, inLE =>
    match resolveLabel inLD inLE ts j with
    | some true => pure (addArgKeys (levelArgs nv args) .empty)
    | _ => none
  | .ret vs, nv, _, _ => pure (addArgKeys (levelArgs nv vs) .empty)
  | .exit _ args, nv, _, _ => pure (addArgKeys (levelArgs nv args) .empty)
  | .hlt, _, _, _ => pure .empty
  | .group (sig := sig) bs k, nv, inLD, inLE => do
    let inLD' := inLD + sig.length
    let inLE' := insertTupEnv inLD inLE (trueLabels sig)
    let sb ← validateLeafBFlat bs nv inLD' inLE'
    let sk ← validateLeafFlat k nv inLD' inLE'
    pure (trieUnion sb sk)

/-- Block-list companion of `validateLeafFlat`. -/
def validateLeafBFlat {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig →
    Nat → Nat → Trie ((ts : List Ty) × BoolL ts) → Option (Trie Unit)
  | _, .nil, _, _, _ => pure .empty
  | _, .cons (ts := ts) b bs, nv, inLD, inLE => do
    let s ← validateLeafFlat b (nv + ts.length) inLD inLE
    let ss ← validateLeafBFlat bs nv inLD inLE
    pure (trieUnion s ss)
end

/-- Native `TFlat` mirror of `LoopRotate.validateHdr`. -/
def validateHdrFlat {rs : List Ty} :
    HdrPlan → TFlat rs → Nat → Option (Trie Unit × TFlat rs × TFlat rs × Nat)
  | [], .jnz c t e, nv => pure (addArgKey (levelArg nv c) .empty, t, e, nv)
  | .let_ dts :: ss, .let_ (ts := dts') op k, nv =>
    match tysDecEq dts dts' with
    | isTrue _ =>
      if isSafeHdrOp op.code then do
        let (s, t, e, nv') ← validateHdrFlat ss k (nv + dts.length)
        pure (addArgKeys (levelArgs nv op.args) s, t, e, nv')
      else none
    | isFalse _ => none
  | .load t :: ss, .load t' a k, nv =>
    match tyDecEq t t' with
    | isTrue _ => do
      let (s, te, ee, nv') ← validateHdrFlat ss k (nv + 1)
      pure (addArgKey (levelArg nv a) s, te, ee, nv')
    | isFalse _ => none
  | _, _, _ => none

/-- Native `TFlat` mirror of `LoopRotate.validateRotPlanWith`
(structurally recursive on `RotPlan`). -/
def validateRotPlanWithFlat {rs : List Ty} (allowHdr : Bool) :
    RotPlan → TFlat rs → Nat → Nat → Trie ((ts : List Ty) × BoolL ts) → Option (Trie Unit)
  | .leaf, tf, nv, inLD, inLE => validateLeafFlat tf nv inLD inLE
  | .letP p, .let_ (ts := ts) op k, nv, inLD, inLE => do
    let s ← validateRotPlanWithFlat allowHdr p k (nv + ts.length) inLD inLE
    pure (addArgKeys (levelArgs nv op.args) s)
  | .loadP p, .load _ a k, nv, inLD, inLE => do
    let s ← validateRotPlanWithFlat allowHdr p k (nv + 1) inLD inLE
    pure (addArgKey (levelArg nv a) s)
  | .storeP p, .store v a k, nv, inLD, inLE => do
    let s ← validateRotPlanWithFlat allowHdr p k nv inLD inLE
    pure (addArgKey (levelArg nv v) (addArgKey (levelArg nv a) s))
  | .callP p, .call _ bs args k, nv, inLD, inLE => do
    let s ← validateRotPlanWithFlat allowHdr p k (nv + bs.length) inLD inLE
    pure (addArgKeys (levelArgs nv args) s)
  | .jnzP tp ep, .jnz c t e, nv, inLD, inLE => do
    let st ← validateRotPlanWithFlat allowHdr tp t nv inLD inLE
    let se ← validateRotPlanWithFlat allowHdr ep e nv inLD inLE
    pure (addArgKey (levelArg nv c) (trieUnion st se))
  | .jnzP .leaf .leaf, .jump (ts := ts) j args, nv, inLD, inLE =>
    if allowHdr then
      match resolveLabel inLD inLE ts j with
      | some true => pure (addArgKeys (levelArgs nv args) .empty)
      | _ => none
    else none
  | .groupKeep bsP kP, .group (sig := sig) bs k, nv, inLD, inLE => do
    let inLD' := inLD + sig.length
    let inLE' := insertTupEnv inLD inLE (trueLabels sig)
    let sb ← validateKeepBFlat allowHdr bsP bs nv inLD' inLE'
    let sk ← validateRotPlanWithFlat allowHdr kP k nv inLD' inLE'
    pure (trieUnion sb sk)
  | .groupRot dir hdr contMasks exitMode contP exitP entryP,
    .group bs k, nv, inLD, inLE =>
    match bs with
    | .cons (ts := ts) b bs' =>
      match bs' with
      | .nil => do
        let nv0 := nv + ts.length
        let (sh, armT, armE, _) ← validateHdrFlat hdr b nv0
        let armCont := if dir then armT else armE
        let armExit := if dir then armE else armT
        let isPart := isPartialMasks hdr contMasks
        let inLD' := inLD + 1
        let inLE_T := inLE.insert inLD ⟨ts, true⟩
        let inLE_F := inLE.insert inLD ⟨ts, false⟩
        let sc ← validateRotPlanWithFlat (allowHdr || isPart) contP armCont
          (nv0 + hdrStepCount hdr) inLD' inLE_T
        let sx ← validateRotPlanWithFlat allowHdr exitP armExit
          (nv0 + hdrStepCount hdr) inLD' inLE_F
        let se ← validateRotPlanWithFlat allowHdr entryP k nv inLD' inLE_T
        if !checkDeadStepMasks nv0 sc hdr contMasks then none
        else match exitMode with
        | .inline => pure (trieUnion sh (trieUnion sc (trieUnion sx se)))
        | .wrap xsMask hMasks =>
          if checkDeadMask nv sx ts xsMask && checkDeadStepMasks nv0 sx hdr hMasks then
            pure (trieUnion sh (trieUnion sc (trieUnion sx se)))
          else none
      | .cons _ _ => none
    | .nil => none
  | _, _, _, _, _ => none
where
  /-- Block-list companion of `validateRotPlanWithFlat`. -/
  validateKeepBFlat {rs : List Ty} (allowHdr : Bool) :
      List RotPlan → {sig : List (List Ty)} → TBlocks rs sig →
      Nat → Nat → Trie ((ts : List Ty) × BoolL ts) → Option (Trie Unit)
    | [], _, .nil, _, _, _ => pure .empty
    | p :: ps, _, .cons (ts := ts) b bs, nv, inLD, inLE => do
      let s ← validateRotPlanWithFlat allowHdr p b (nv + ts.length) inLD inLE
      let ss ← validateKeepBFlat allowHdr ps bs nv inLD inLE
      pure (trieUnion s ss)
    | _, _, _, _, _, _ => none

/-- Native `TFlat` mirror of `LoopRotate.validateRotPlan`. -/
def validateRotPlanFlat {rs : List Ty} (plan : RotPlan) (tf : TFlat rs) (nv : Nat) :
    Option (Trie Unit) :=
  validateRotPlanWithFlat false plan tf nv 0 .empty

mutual
/-- Native `TFlat` identity flattening rewriter matching `LoopRotate.flatExpr`. -/
def flatExprFlat {rs : List Ty} :
    TFlat rs → Nat → Trie ((t : Ty) × OptArg K t) →
    Nat → Trie ((ts : List Ty) × RotLFlat rs ts) → Nat → Nat → TFlat rs
  | .let_ (ts := ts) op k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let op' : Op K ts := ⟨op.code, idxArgs outVD (flatOptArgs (resolveEnvArgs inVD inVE op.args))⟩
    let xs := Tup.levels ts outVD
    .let_ op'
      (flatExprFlat k (inVD + ts.length) (insertTupEnv inVD inVE (someVarsToOpt xs))
        inLD inLE (outVD + ts.length) outLD)
  | .load t a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let a' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE a))
    .load t a'
      (flatExprFlat k (inVD + 1) (inVE.insert inVD ⟨t, some (.var outVD)⟩)
        inLD inLE (outVD + 1) outLD)
  | .store v a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let v' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE v))
    let a' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE a))
    .store v' a' (flatExprFlat k inVD inVE inLD inLE outVD outLD)
  | .call f bs args k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let args' := idxArgs outVD (flatOptArgs (resolveEnvArgs inVD inVE args))
    let xs := Tup.levels bs outVD
    .call f bs args'
      (flatExprFlat k (inVD + bs.length) (insertTupEnv inVD inVE (someVarsToOpt xs))
        inLD inLE (outVD + bs.length) outLD)
  | .jnz c t e, inVD, inVE, inLD, inLE, outVD, outLD =>
    let c' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE c))
    .jnz c'
      (flatExprFlat t inVD inVE inLD inLE outVD outLD)
      (flatExprFlat e inVD inVE inLD inLE outVD outLD)
  | .jump (ts := ts) j args, inVD, inVE, inLD, inLE, outVD, outLD =>
    let args' := flatOptArgs (resolveEnvArgs inVD inVE args)
    match resolveLabel inLD inLE ts j with
    | some (.keep l) => .jump (idxLabel outLD l) (idxArgs outVD args')
    | some (.expand f) | some (.expandOrKeep f _) => f outVD outLD args'
    | some .dead | none => .hlt
  | .ret vs, inVD, inVE, _, _, outVD, _ =>
    .ret (idxArgs outVD (flatOptArgs (resolveEnvArgs inVD inVE vs)))
  | .exit f args, inVD, inVE, _, _, outVD, _ =>
    .exit f (idxArgs outVD (flatOptArgs (resolveEnvArgs inVD inVE args)))
  | .hlt, _, _, _, _, _, _ => .hlt
  | .group (sig := sig) bs k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let wrapped := wrapKeepLabelsFlat (rs := rs) (Tup.levels sig outLD)
    let inLD' := inLD + sig.length
    let inLE' := insertTupEnv inLD inLE wrapped
    let outLD' := outLD + sig.length
    .group
      (flatBlocksFlat bs inVD inVE inLD' inLE' outVD outLD')
      (flatExprFlat k inVD inVE inLD' inLE' outVD outLD')

/-- Block-list companion of `flatExprFlat`. -/
def flatBlocksFlat {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × OptArg K t) →
    Nat → Trie ((ts : List Ty) × RotLFlat rs ts) → Nat → Nat → TBlocks rs sig
  | _, .nil, _, _, _, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inVD, inVE, inLD, inLE, outVD, outLD =>
    let xs := Tup.levels ts outVD
    .cons
      (flatExprFlat b (inVD + ts.length) (insertTupEnv inVD inVE (someVarsToOpt xs))
        inLD inLE (outVD + ts.length) outLD)
      (flatBlocksFlat bs inVD inVE inLD inLE outVD outLD)
end

/-- Native `TFlat` mirror of `LoopRotate.hdrPeel`. -/
def hdrPeelFlat {rs tail : List Ty} (dir wantCont : Bool) :
    (hdr : HdrPlan) → (ms : List (List Bool)) →
    Tup K (stepMasksSig hdr ms tail) →
    TFlat rs → Nat → Trie ((t : Ty) × OptArg K t) →
    Option (TFlat rs × Nat × Trie ((t : Ty) × OptArg K t))
  | [], _, _, .jnz _ armT armE, inVD, inVE =>
    some (if wantCont == dir then armT else armE, inVD, inVE)
  | .let_ dts :: ss, ms, params, .let_ (ts := dts') _ k, inVD, inVE =>
    match tysDecEq dts dts' with
    | isTrue rfl =>
      let (stepLive, rest) := LoopRotate.tupSplit (filterTys dts (ms.headD [])) params
      let ys : Tup (OptArg K) dts := tupWiden dts (ms.headD []) stepLive
      hdrPeelFlat dir wantCont ss ms.tail rest k (inVD + dts.length) (insertTupEnv inVD inVE ys)
    | isFalse _ => none
  | .load t :: ss, ms, params, .load t' _ k, inVD, inVE =>
    match tyDecEq t t' with
    | isTrue rfl =>
      let (stepLive, rest) := LoopRotate.tupSplit (filterTys [t] (ms.headD [])) params
      let y1 : OptArg K t := (tupWiden [t] (ms.headD []) stepLive).1
      hdrPeelFlat dir wantCont ss ms.tail rest k (inVD + 1) (inVE.insert inVD ⟨t, y1⟩)
    | isFalse _ => none
  | _, _, _, _, _, _ => none

/-- Native `TFlat` mirror of `LoopRotate.hdrEmit`. -/
def hdrEmitFlat {rs tailC tailX : List Ty}
    (dir : Bool) (tailCArgs : Tup (Arg K) tailC) (tailXArgs : Tup (Arg K) tailX) :
    (hdr : HdrPlan) → (cMs xMs : List (List Bool)) →
    TFlat rs → Nat → Trie ((t : Ty) × OptArg K t) → Nat → Nat →
    (Nat → Tup (Arg K) (stepMasksSig hdr cMs tailC) → TFlat rs) →
    (TFlat rs → Nat → Trie ((t : Ty) × OptArg K t) → Nat →
      Tup (Arg K) (stepMasksSig hdr xMs tailX) → TFlat rs) →
    TFlat rs
  | [], _, _, .jnz c armT armE, inVD, inVE, outVD, _, kC, kX =>
    let c' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE c))
    if dir then .jnz c' (kC outVD tailCArgs) (kX armE inVD inVE outVD tailXArgs)
    else .jnz c' (kX armT inVD inVE outVD tailXArgs) (kC outVD tailCArgs)
  | .let_ dts :: ss, cMs, xMs, .let_ (ts := dts') op k, inVD, inVE, outVD, outLD, kC, kX =>
    match tysDecEq dts dts' with
    | isTrue rfl =>
      let op' : Op K dts :=
        ⟨op.code, idxArgs outVD (flatOptArgs (resolveEnvArgs inVD inVE op.args))⟩
      let ys := Tup.levels dts outVD
      .let_ op'
        (hdrEmitFlat dir tailCArgs tailXArgs ss cMs.tail xMs.tail k
          (inVD + dts.length) (insertTupEnv inVD inVE (someVarsToOpt ys))
          (outVD + dts.length) outLD
          (fun od rest =>
            kC od (LoopRotate.tupAppend (tupSelectArgs dts (cMs.headD []) (toArgTup ys)) rest))
          (fun ex iv ie od rest =>
            kX ex iv ie od
              (LoopRotate.tupAppend (tupSelectArgs dts (xMs.headD []) (toArgTup ys)) rest)))
    | isFalse _ => .hlt
  | .load t :: ss, cMs, xMs, .load t' a k, inVD, inVE, outVD, outLD, kC, kX =>
    match tyDecEq t t' with
    | isTrue rfl =>
      let a' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE a))
      let as1 : Tup (Arg K) [t] := (.var outVD, ())
      .load t a'
        (hdrEmitFlat dir tailCArgs tailXArgs ss cMs.tail xMs.tail k
          (inVD + 1) (inVE.insert inVD ⟨t, some (.var outVD)⟩)
          (outVD + 1) outLD
          (fun od rest =>
            kC od (LoopRotate.tupAppend (tupSelectArgs [t] (cMs.headD []) as1) rest))
          (fun ex iv ie od rest =>
            kX ex iv ie od
              (LoopRotate.tupAppend (tupSelectArgs [t] (xMs.headD []) as1) rest)))
    | isFalse _ => .hlt
  | _, _, _, _, _, _, _, _, _, _ => .hlt

/-- Native `TFlat` mirror of `LoopRotate.rewriteRotWith` (structurally recursive on `RotPlan`). -/
def rewriteRotWithFlat {rs : List Ty} (allowHdr : Bool) :
    RotPlan → TFlat rs → Nat → Trie ((t : Ty) × OptArg K t) →
    Nat → Trie ((ts : List Ty) × RotLFlat rs ts) → Nat → Nat → TFlat rs
  | .leaf, tf, inVD, inVE, inLD, inLE, outVD, outLD =>
    flatExprFlat tf inVD inVE inLD inLE outVD outLD
  | .letP p, .let_ (ts := ts) op k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let op' : Op K ts := ⟨op.code, idxArgs outVD (flatOptArgs (resolveEnvArgs inVD inVE op.args))⟩
    let xs := Tup.levels ts outVD
    .let_ op'
      (rewriteRotWithFlat allowHdr p k
        (inVD + ts.length) (insertTupEnv inVD inVE (someVarsToOpt xs))
        inLD inLE (outVD + ts.length) outLD)
  | .loadP p, .load t a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let a' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE a))
    .load t a'
      (rewriteRotWithFlat allowHdr p k (inVD + 1) (inVE.insert inVD ⟨t, some (.var outVD)⟩)
        inLD inLE (outVD + 1) outLD)
  | .storeP p, .store v a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let v' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE v))
    let a' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE a))
    .store v' a' (rewriteRotWithFlat allowHdr p k inVD inVE inLD inLE outVD outLD)
  | .callP p, .call f bs args k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let args' := idxArgs outVD (flatOptArgs (resolveEnvArgs inVD inVE args))
    let xs := Tup.levels bs outVD
    .call f bs args'
      (rewriteRotWithFlat allowHdr p k
        (inVD + bs.length) (insertTupEnv inVD inVE (someVarsToOpt xs))
        inLD inLE (outVD + bs.length) outLD)
  | .jnzP tp ep, .jnz c t e, inVD, inVE, inLD, inLE, outVD, outLD =>
    let c' := idxArg outVD (flatOptArg (resolveEnvArg inVD inVE c))
    .jnz c'
      (rewriteRotWithFlat allowHdr tp t inVD inVE inLD inLE outVD outLD)
      (rewriteRotWithFlat allowHdr ep e inVD inVE inLD inLE outVD outLD)
  | .jnzP .leaf .leaf, .jump (ts := ts) j args, inVD, inVE, inLD, inLE, outVD, outLD =>
    if allowHdr then
      let args' := idxArgs outVD (flatOptArgs (resolveEnvArgs inVD inVE args))
      match resolveLabel inLD inLE ts j with
      | some (.expandOrKeep _ lHdr) => .jump (idxLabel outLD lHdr) args'
      | some (.expand f) => f outVD outLD (flatOptArgs (resolveEnvArgs inVD inVE args))
      | some (.keep l) => .jump (idxLabel outLD l) args'
      | some .dead | none => .hlt
    else .hlt
  | .groupKeep bsP kP, .group (sig := sig) bs k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let wrapped := wrapKeepLabelsFlat (rs := rs) (Tup.levels sig outLD)
    let inLD' := inLD + sig.length
    let inLE' := insertTupEnv inLD inLE wrapped
    let outLD' := outLD + sig.length
    .group
      (rewriteKeepBFlat allowHdr bsP bs inVD inVE inLD' inLE' outVD outLD')
      (rewriteRotWithFlat allowHdr kP k inVD inVE inLD' inLE' outVD outLD')
  | .groupRot dir hdr contMasks exitMode contP exitP entryP,
    .group bs k, inVD, inVE, inLD, inLE, outVD, outLD =>
    match bs with
    | .cons (ts := ts) b bs' =>
      match bs' with
      | .nil =>
        let inLD_b := inLD + 1
        let inLE_dead := inLE.insert inLD ⟨ts, .dead⟩
        let emitLoop (outLD_l : Nat)
            (mkHdrCont : Nat → Nat → Nat → Tup (Arg K) ts → TFlat rs) : TFlat rs :=
          if isPartialMasks hdr contMasks then
            let J_rot := outLD_l
            let J_hdr := outLD_l + 1
            let outLD' := outLD_l + 2
            let rotParams := Tup.levels (rotSig hdr contMasks ts) outVD
            let outVD_b0 := outVD + (rotSig hdr contMasks ts).length
            let xs := splitTail hdr contMasks rotParams
            let b0 := match hdrPeelFlat dir true hdr contMasks rotParams b
                (inVD + ts.length) (insertTupEnv inVD inVE (someVarsToOpt xs)) with
              | some (arm, iv', ie') =>
                rewriteRotWithFlat true contP arm iv' ie'
                  inLD_b (inLE.insert inLD ⟨ts, .expandOrKeep (mkHdrCont J_rot) J_hdr⟩)
                  outVD_b0 outLD'
              | none => .hlt
            let hdrParams := Tup.levels ts outVD
            let b1 := mkHdrCont J_rot (outVD + ts.length) outLD' (toArgTup hdrParams)
            .group (sig := [rotSig hdr contMasks ts, ts])
              (.cons b0 (.cons b1 .nil))
              (rewriteRotWithFlat allowHdr entryP k inVD inVE
                inLD_b (inLE.insert inLD ⟨ts, .expand (mkHdrCont J_rot)⟩) outVD outLD')
          else
            let J_rot := outLD_l
            let outLD' := outLD_l + 1
            let rotParams := Tup.levels (rotSig hdr contMasks ts) outVD
            let outVD_b0 := outVD + (rotSig hdr contMasks ts).length
            let xs := splitTail hdr contMasks rotParams
            let b0 := match hdrPeelFlat dir true hdr contMasks rotParams b
                (inVD + ts.length) (insertTupEnv inVD inVE (someVarsToOpt xs)) with
              | some (arm, iv', ie') =>
                rewriteRotWithFlat allowHdr contP arm iv' ie'
                  inLD_b (inLE.insert inLD ⟨ts, .expand (mkHdrCont J_rot)⟩)
                  outVD_b0 outLD'
              | none => .hlt
            .group (sig := [rotSig hdr contMasks ts])
              (.cons b0 .nil)
              (rewriteRotWithFlat allowHdr entryP k inVD inVE
                inLD_b (inLE.insert inLD ⟨ts, .expand (mkHdrCont J_rot)⟩) outVD outLD')
        match exitMode with
        | .inline =>
          emitLoop outLD fun J_rot curVD curLD args =>
            hdrEmitFlat (tailC := ts) (tailX := ts) dir args args hdr contMasks [] b
              (inVD + ts.length) (insertTupEnv inVD inVE (someArgsToOpt args)) curVD curLD
              (fun od rotArgs => .jump (idxLabel curLD J_rot) (idxArgs od rotArgs))
              (fun ex iv ie od _ =>
                rewriteRotWithFlat allowHdr exitP ex iv ie inLD_b inLE_dead od curLD)
        | .wrap xsMask hMasks =>
          let J_exit := outLD
          let outLD_w := outLD + 1
          let exitParams := Tup.levels (exitSig hdr hMasks xsMask ts) outVD
          let outVD_ex := outVD + (exitSig hdr hMasks xsMask ts).length
          let xsTail := splitTail hdr hMasks exitParams
          let xsOpt := tupWiden ts xsMask xsTail
          let exitBlk := match hdrPeelFlat dir false hdr hMasks exitParams b
              (inVD + ts.length) (insertTupEnv inVD inVE xsOpt) with
            | some (arm, iv', ie') =>
              rewriteRotWithFlat allowHdr exitP arm iv' ie' inLD_b inLE_dead outVD_ex outLD_w
            | none => .hlt
          .group (sig := [exitSig hdr hMasks xsMask ts])
            (.cons exitBlk .nil)
            (emitLoop outLD_w fun J_rot curVD curLD args =>
              hdrEmitFlat (tailC := ts) (tailX := filterTys ts xsMask)
                dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks b
                (inVD + ts.length) (insertTupEnv inVD inVE (someArgsToOpt args)) curVD curLD
                (fun od rotArgs => .jump (idxLabel curLD J_rot) (idxArgs od rotArgs))
                (fun _ _ _ od exArgs => .jump (idxLabel curLD J_exit) (idxArgs od exArgs)))
      | .cons _ _ => .hlt
    | .nil => .hlt
  | _, _, _, _, _, _, _, _ => .hlt
where
  /-- Block-list companion of `rewriteRotWithFlat`. -/
  rewriteKeepBFlat {rs : List Ty} (allowHdr : Bool) :
      List RotPlan → {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × OptArg K t) →
      Nat → Trie ((ts : List Ty) × RotLFlat rs ts) → Nat → Nat → TBlocks rs sig
    | [], _, bs, inVD, inVE, inLD, inLE, outVD, outLD =>
      flatBlocksFlat bs inVD inVE inLD inLE outVD outLD
    | p :: ps, _, .cons (ts := ts) b bs, inVD, inVE, inLD, inLE, outVD, outLD =>
      let xs := Tup.levels ts outVD
      .cons
        (rewriteRotWithFlat allowHdr p b
          (inVD + ts.length) (insertTupEnv inVD inVE (someVarsToOpt xs))
          inLD inLE (outVD + ts.length) outLD)
        (rewriteKeepBFlat allowHdr ps bs inVD inVE inLD inLE outVD outLD)
    | _ :: _, _, .nil, _, _, _, _, _, _ => .nil

/-- Native `TFlat` loop rotation matching `reifyFunc (Func.loopRotate (denoteFunc tf) cfg)`. -/
def loopRotateFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig) : TFlat rs :=
  let plan := LoopRotate.buildRotPlan (as := as) cfg tf
  if plan.hasRot then
    match validateRotPlanFlat plan tf as.length with
    | some _ =>
      let initE := insertTupEnv 0 .empty (someVarsToOpt (Tup.levels as 0))
      rewriteRotWithFlat false plan tf as.length initE 0 .empty as.length 0
    | none => tf
  else tf

/-- `TFlatFn` wrapper for `loopRotateFlat`. -/
def loopRotateFlatFn (f : TFlatFn)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig) : TFlatFn :=
  ⟨f.name, f.as, f.rs, loopRotateFlat f.as f.body cfg⟩

end LoopRotateFlat

end OptFlatLoop
end LeanQbe.T
