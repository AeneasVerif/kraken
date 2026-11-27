module

public import LeanQbe.T.FlatDirect
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.DceParam
public import LeanQbe.T.IfOpt

/-!
# Native `Trie`-Env First-Order Mid-End CFG Passes (`OptFlatCfg`)

Direct `TFlat rs → TFlat rs` implementations of the CFG/cleanup mid-end passes (`Func.dceWith`,
`Func.dce`, `Func.deadLoadElim`, `Func.dcePWith`, `Func.dceP`, `Func.ifOptWith`, `Func.ifOpt`,
`Func.ifOptBits`) using de Bruijn level `Trie` environments and output level counters:

* `OptFlatCfg.dceWithFlat` / `OptFlatCfg.dceFlat` / `OptFlatCfg.deadLoadElimFlat`: dead-`let_`
  and dead-`.load` elimination (`Dce.lean`).
* `OptFlatCfg.dcePWithFlat` / `OptFlatCfg.dcePFlat`: dead-`let_` and dead-`.group`-parameter
  elimination (`DceParam.lean`).
* `OptFlatCfg.ifOptFlat`: diamond `.jnz` → `.select` if-conversion (`IfOpt.lean`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatCfg

open OptFlatPlanKit

/-! ## 1. Native `TFlat` Dead-Binding & Dead-Load Elimination (`dceWithFlat`, `deadLoadElimFlat`) -/

mutual
/-- Bottom-up liveness scan directly over `TFlat rs` mirroring `LeanQbe.T.liveVarsWith`. -/
def liveVarsFlat (dropLets dropLoads : Bool) {rs : List Ty} (b : Nat) :
    TFlat rs → Trie Unit × KeepTree
  | .let_ (ts := ts) op k =>
    let (s, kt) := liveVarsFlat dropLets dropLoads (b + ts.length) k
    if !dropLets || anyLive b ts.length s then
      (addArgKeys (levelArgs b op.args) s, .letNode true kt)
    else
      (s, .letNode false kt)
  | .load _ a k =>
    let (s, kt) := liveVarsFlat dropLets dropLoads (b + 1) k
    if !dropLoads || (s.find? b).isSome then
      (addArgKey (levelArg b a) s, .letNode true kt)
    else
      (s, .letNode false kt)
  | .store v a k =>
    let (s, kt) := liveVarsFlat dropLets dropLoads b k
    (addArgKey (levelArg b v) (addArgKey (levelArg b a) s), .node1 kt)
  | .call _ bs args k =>
    let (s, kt) := liveVarsFlat dropLets dropLoads (b + bs.length) k
    (addArgKeys (levelArgs b args) s, .node1 kt)
  | .jnz c t e =>
    let (st, ktt) := liveVarsFlat dropLets dropLoads b t
    let (se, kte) := liveVarsFlat dropLets dropLoads b e
    (addArgKey (levelArg b c) (trieUnion st se), .node2 ktt kte)
  | .jump _ args => (addArgKeys (levelArgs b args) .empty, .leaf)
  | .ret vs => (addArgKeys (levelArgs b vs) .empty, .leaf)
  | .exit _ args => (addArgKeys (levelArgs b args) .empty, .leaf)
  | .hlt => (.empty, .leaf)
  | .group bodies k =>
    let (sb, kbs) := liveVarsBFlat dropLets dropLoads b bodies
    let (sk, ktk) := liveVarsFlat dropLets dropLoads b k
    (trieUnion sb sk, .groupNode kbs ktk)

/-- Block-list companion of `liveVarsFlat`. -/
def liveVarsBFlat (dropLets dropLoads : Bool) {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → Trie Unit × KeepBlocks
  | _, .nil => (.empty, .nil)
  | _, .cons (ts := ts) hd tl =>
    let (sh, kh) := liveVarsFlat dropLets dropLoads (b + ts.length) hd
    let (st, kt) := liveVarsBFlat dropLets dropLoads b tl
    (trieUnion sh st, .cons kh kt)
end

mutual
/-- Top-down `TFlat` DCE sweep guided by `kt : KeepTree` mirroring `LeanQbe.T.dceSweep`. -/
def dceSweepFlat {rs : List Ty} (kt : KeepTree) :
    TFlat rs → Nat → Trie ((t : Ty) × OptV K t) → Nat → TFlat rs
  | .let_ (ts := ts) op k, inD, inE, outD =>
    match kt with
    | .letNode true kt' =>
      let args' := idxArgs outD (argsSweep (resolveEnvArgs inD inE op.args))
      let wrapped := someTup ts (Tup.levels ts outD)
      .let_ ⟨op.code, args'⟩
        (dceSweepFlat kt' k (inD + ts.length) (insertTupEnv inD inE wrapped) (outD + ts.length))
    | .letNode false kt' =>
      dceSweepFlat kt' k (inD + ts.length) (insertTupEnv inD inE (noneTup ts)) outD
    | _ => .hlt
  | .load t a k, inD, inE, outD =>
    match kt with
    | .letNode true kt' =>
      let a' := idxArg outD (argSweep (resolveEnvArg inD inE a))
      .load t a' (dceSweepFlat kt' k (inD + 1) (inE.insert inD ⟨t, some outD⟩) (outD + 1))
    | .letNode false kt' =>
      dceSweepFlat kt' k (inD + 1) (inE.insert inD ⟨t, none⟩) outD
    | _ => .hlt
  | .store v a k, inD, inE, outD =>
    match kt with
    | .node1 kt' =>
      let v' := idxArg outD (argSweep (resolveEnvArg inD inE v))
      let a' := idxArg outD (argSweep (resolveEnvArg inD inE a))
      .store v' a' (dceSweepFlat kt' k inD inE outD)
    | _ => .hlt
  | .call f bs args k, inD, inE, outD =>
    match kt with
    | .node1 kt' =>
      let args' := idxArgs outD (argsSweep (resolveEnvArgs inD inE args))
      let wrapped := someTup bs (Tup.levels bs outD)
      .call f bs args'
        (dceSweepFlat kt' k (inD + bs.length) (insertTupEnv inD inE wrapped) (outD + bs.length))
    | _ => .hlt
  | .jnz c t e, inD, inE, outD =>
    match kt with
    | .node2 ktt kte =>
      let c' := idxArg outD (argSweep (resolveEnvArg inD inE c))
      .jnz c' (dceSweepFlat ktt t inD inE outD) (dceSweepFlat kte e inD inE outD)
    | _ => .hlt
  | .jump j args, inD, inE, outD =>
    .jump j (idxArgs outD (argsSweep (resolveEnvArgs inD inE args)))
  | .ret vs, inD, inE, outD =>
    .ret (idxArgs outD (argsSweep (resolveEnvArgs inD inE vs)))
  | .exit f args, inD, inE, outD =>
    .exit f (idxArgs outD (argsSweep (resolveEnvArgs inD inE args)))
  | .hlt, _, _, _ => .hlt
  | .group bodies k, inD, inE, outD =>
    match kt with
    | .groupNode kbs ktk =>
      .group (dceSweepBFlat kbs bodies inD inE outD) (dceSweepFlat ktk k inD inE outD)
    | _ => .hlt

/-- Block-list companion of `dceSweepFlat`. -/
def dceSweepBFlat {rs : List Ty} (kbs : KeepBlocks) :
    {sig : List (List Ty)} → TBlocks rs sig →
    Nat → Trie ((t : Ty) × OptV K t) → Nat → TBlocks rs sig
  | _, .nil, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inD, inE, outD =>
    match kbs with
    | .cons kh kt =>
      let wrapped := someTup ts (Tup.levels ts outD)
      .cons
        (dceSweepFlat kh b (inD + ts.length) (insertTupEnv inD inE wrapped) (outD + ts.length))
        (dceSweepBFlat kt bs inD inE outD)
    | _ => .cons .hlt (dceSweepBFlat .nil bs inD inE outD)
end

/-- Direct `TFlat` configurable dead-binding elimination matching
`reifyFunc (Func.dceWith dropLets dropLoads (denoteFunc tf))`. -/
def dceWithFlat (dropLets dropLoads : Bool) (as : List Ty) {rs : List Ty}
    (tf : TFlat rs) : TFlat rs :=
  let kt := (liveVarsFlat dropLets dropLoads as.length tf).2
  dceSweepFlat kt tf as.length (initEnv (fun x _ => some x) as) as.length

/-- Direct `TFlat` dead-`let_` elimination matching `reifyFunc (Func.dce (denoteFunc tf))`. -/
def dceFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  dceWithFlat true false as tf

/-- Direct `TFlat` dead-`.load` elimination matching
`reifyFunc (Func.deadLoadElim (denoteFunc tf))`. -/
def deadLoadElimFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  dceWithFlat false true as tf

/-- `TFlatFn` wrapper for `dceFlat`. -/
def dceFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, dceFlat f.as f.body⟩

/-- `TFlatFn` wrapper for `deadLoadElimFlat`. -/
def deadLoadElimFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, deadLoadElimFlat f.as f.body⟩

/-! ## 2. Native `TFlat` Dead-`.group`-Parameter & Dead-`let_` Elimination (`dcePFlat`) -/

section DceParamFlat
open DceParam

mutual
/-- Bottom-up liveness and mask-plan analysis directly over `TFlat rs` with a guessed `PTree`
plan, mirroring `DceParam.liveVarsP`. -/
def liveVarsPFlat (dropLets dropLoads : Bool) {rs : List Ty} (g : PTree)
    (b inLD : Nat) (inLE : Trie ((ts : List Ty) × Mask ts)) :
    TFlat rs → Trie Unit × PTree × Bool
  | .let_ (ts := ts) op k =>
    let (s, kt, ok) := liveVarsPFlat dropLets dropLoads g.sub1 (b + ts.length) inLD inLE k
    if !dropLets || anyLive b ts.length s then
      (addArgKeys (levelArgs b op.args) s, .letNode true kt, ok)
    else
      (s, .letNode false kt, ok)
  | .load _ a k =>
    let (s, kt, ok) := liveVarsPFlat dropLets dropLoads g.sub1 (b + 1) inLD inLE k
    if !dropLoads || (s.find? b).isSome then
      (addArgKey (levelArg b a) s, .letNode true kt, ok)
    else
      (s, .letNode false kt, ok)
  | .store v a k =>
    let (s, kt, ok) := liveVarsPFlat dropLets dropLoads g.sub1 b inLD inLE k
    (addArgKey (levelArg b v) (addArgKey (levelArg b a) s), .node1 kt, ok)
  | .call _ bs args k =>
    let (s, kt, ok) := liveVarsPFlat dropLets dropLoads g.sub1 (b + bs.length) inLD inLE k
    (addArgKeys (levelArgs b args) s, .node1 kt, ok)
  | .jnz c t e =>
    let (st, ktt, okt) := liveVarsPFlat dropLets dropLoads g.subT b inLD inLE t
    let (se, kte, oke) := liveVarsPFlat dropLets dropLoads g.subE b inLD inLE e
    (addArgKey (levelArg b c) (trieUnion st se), .node2 ktt kte, okt && oke)
  | .jump (ts := ts) j args =>
    match resolveLabel inLD inLE ts j with
    | some m => (addMasked m (levelArgs b args) .empty, .leaf, true)
    | none => (.empty, .leaf, true)
  | .ret vs => (addArgKeys (levelArgs b vs) .empty, .leaf, true)
  | .exit _ args => (addArgKeys (levelArgs b args) .empty, .leaf, true)
  | .hlt => (.empty, .leaf, true)
  | .group (sig := sig) bodies k =>
    let ls := g.subB.masksOf sig
    let inLD' := inLD + sig.length
    let inLE' := insertTupEnv inLD inLE ls
    let (sb, kbs, okb) := liveVarsBPFlat dropLets dropLoads g.subB b inLD' inLE' bodies
    let (sk, ktk, okk) := liveVarsPFlat dropLets dropLoads g.subK b inLD' inLE' k
    (trieUnion sb sk, .groupNode kbs ktk, okb && okk)

/-- Block-list companion of `liveVarsPFlat`. -/
def liveVarsBPFlat (dropLets dropLoads : Bool) {rs : List Ty} (g : PBlocks)
    (b inLD : Nat) (inLE : Trie ((ts : List Ty) × Mask ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Trie Unit × PBlocks × Bool
  | _, .nil => (.empty, .nil, true)
  | _, .cons (ts := ts) hd tl =>
    let (sh, kh, okh) := liveVarsPFlat dropLets dropLoads g.hd (b + ts.length) inLD inLE hd
    let (st, kt, okt) := liveVarsBPFlat dropLets dropLoads g.tl b inLD inLE tl
    let m := liveMask b ts.length sh
    (trieUnion sh st, .cons m kh kt, maskLe (maskOf ts m) (maskOf ts g.mask) && okh && okt)
end

mutual
/-- Top-down `TFlat` sweep narrowing `.group` signatures and `.jump` operands according to
`kt : PTree`, mirroring `DceParam.dceSweepP`. -/
def dceSweepPFlat {rs : List Ty} (kt : PTree) :
    TFlat rs → Nat → Trie ((t : Ty) × OptV K t) →
    Nat → Trie ((ts : List Ty) × NLabel KL ts) → Nat → Nat → TFlat rs
  | .let_ (ts := ts) op k, inVD, inVE, inLD, inLE, outVD, outLD =>
    match kt with
    | .letNode true kt' =>
      let args' := idxArgs outVD (argsSweep (resolveEnvArgs inVD inVE op.args))
      let wrapped := someTup ts (Tup.levels ts outVD)
      .let_ ⟨op.code, args'⟩
        (dceSweepPFlat kt' k (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
          inLD inLE (outVD + ts.length) outLD)
    | .letNode false kt' =>
      dceSweepPFlat kt' k (inVD + ts.length) (insertTupEnv inVD inVE (noneTup ts))
        inLD inLE outVD outLD
    | _ => .hlt
  | .load t a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    match kt with
    | .letNode true kt' =>
      let a' := idxArg outVD (argSweep (resolveEnvArg inVD inVE a))
      .load t a'
        (dceSweepPFlat kt' k (inVD + 1) (inVE.insert inVD ⟨t, some outVD⟩)
          inLD inLE (outVD + 1) outLD)
    | .letNode false kt' =>
      dceSweepPFlat kt' k (inVD + 1) (inVE.insert inVD ⟨t, none⟩) inLD inLE outVD outLD
    | _ => .hlt
  | .store v a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    match kt with
    | .node1 kt' =>
      let v' := idxArg outVD (argSweep (resolveEnvArg inVD inVE v))
      let a' := idxArg outVD (argSweep (resolveEnvArg inVD inVE a))
      .store v' a' (dceSweepPFlat kt' k inVD inVE inLD inLE outVD outLD)
    | _ => .hlt
  | .call f bs args k, inVD, inVE, inLD, inLE, outVD, outLD =>
    match kt with
    | .node1 kt' =>
      let args' := idxArgs outVD (argsSweep (resolveEnvArgs inVD inVE args))
      let wrapped := someTup bs (Tup.levels bs outVD)
      .call f bs args'
        (dceSweepPFlat kt' k (inVD + bs.length) (insertTupEnv inVD inVE wrapped)
          inLD inLE (outVD + bs.length) outLD)
    | _ => .hlt
  | .jnz c t e, inVD, inVE, inLD, inLE, outVD, outLD =>
    match kt with
    | .node2 ktt kte =>
      let c' := idxArg outVD (argSweep (resolveEnvArg inVD inVE c))
      .jnz c'
        (dceSweepPFlat ktt t inVD inVE inLD inLE outVD outLD)
        (dceSweepPFlat kte e inVD inVE inLD inLE outVD outLD)
    | _ => .hlt
  | .jump (ts := ts) j args, inVD, inVE, inLD, inLE, outVD, outLD =>
    match resolveLabel inLD inLE ts j with
    | some (.mk m l) =>
      .jump (idxLabel outLD l)
        (idxArgs outVD (tupNarrow ts m (argsSweep (resolveEnvArgs inVD inVE args))))
    | none => .hlt
  | .ret vs, inVD, inVE, _, _, outVD, _ =>
    .ret (idxArgs outVD (argsSweep (resolveEnvArgs inVD inVE vs)))
  | .exit f args, inVD, inVE, _, _, outVD, _ =>
    .exit f (idxArgs outVD (argsSweep (resolveEnvArgs inVD inVE args)))
  | .hlt, _, _, _, _, _, _ => .hlt
  | .group (sig := sig) bodies k, inVD, inVE, inLD, inLE, outVD, outLD =>
    match kt with
    | .groupNode kbs ktk =>
      let ms := kbs.masksOf sig
      let sig' := narrowSig sig ms
      let wrappedL := wrapLabels sig ms (Tup.levels sig' outLD)
      let inLD' := inLD + sig.length
      let inLE' := insertTupEnv inLD inLE wrappedL
      let outLD' := outLD + sig'.length
      .group (sig := sig')
        (dceSweepBPFlat kbs bodies inVD inVE inLD' inLE' outVD outLD')
        (dceSweepPFlat ktk k inVD inVE inLD' inLE' outVD outLD')
    | _ => .hlt

/-- Block-list companion of `dceSweepPFlat`. -/
def dceSweepBPFlat {rs : List Ty} (kbs : PBlocks) :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × OptV K t) →
    Nat → Trie ((ts : List Ty) × NLabel KL ts) → Nat → Nat →
    TBlocks rs (narrowSig sig (kbs.masksOf sig))
  | [], .nil, _, _, _, _, _, _ => .nil
  | ts :: _, .cons b bs, inVD, inVE, inLD, inLE, outVD, outLD =>
    let m := maskOf ts kbs.mask
    let widened := tupWiden ts m (Tup.levels (narrow ts m) outVD)
    .cons
      (dceSweepPFlat kbs.hd b (inVD + ts.length) (insertTupEnv inVD inVE widened)
        inLD inLE (outVD + (narrow ts m).length) outLD)
      (dceSweepBPFlat kbs.tl bs inVD inVE inLD inLE outVD outLD)
end

/-- Direct `TFlat` configurable dead-binding and dead-`.group`-parameter elimination matching
`reifyFunc (Func.dcePWith dropLets dropLoads rounds (denoteFunc tf))`. -/
def dcePWithFlat (dropLets dropLoads : Bool) (rounds : Nat := 0)
    (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  let g := iterN (fun g => (liveVarsPFlat dropLets dropLoads g as.length 0 .empty tf).2.1)
    rounds .leaf
  let r := liveVarsPFlat dropLets dropLoads g as.length 0 .empty tf
  if r.2.2 then
    dceSweepPFlat r.2.1 tf as.length (initEnv (fun x _ => some x) as) 0 .empty as.length 0
  else
    dceWithFlat dropLets dropLoads as tf

/-- Direct `TFlat` dead-`let_` and dead-`.group`-parameter elimination matching
`reifyFunc (Func.dceP (denoteFunc tf))`. -/
def dcePFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  dcePWithFlat true false 0 as tf

/-- `TFlatFn` wrapper for `dcePFlat`. -/
def dcePFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, dcePFlat f.as f.body⟩

end DceParamFlat

/-! ## 3. Native `TFlat` Diamond `jnz` → `select` If-Conversion (`ifOptFlat`) -/

section IfOptFlat
open IfOptImpl

/-- Direct `TFlat` mirror of `IfOptImpl.findFirstJump`. -/
def findFirstJumpFlat {rs : List Ty} :
    Nat → Nat → Trie ((ts : List Ty) × JLabel KL ts) → TFlat rs → Option (TaggedTarget KL)
  | 0, _, _, _ => none
  | _ + 1, inLD, inLE, .jump (ts := ts) j _ =>
    match resolveLabel inLD inLE ts j with
    | some (.tag id lbl) => some ⟨ts, id, lbl⟩
    | _ => none
  | fuel + 1, inLD, inLE, .let_ _ k => findFirstJumpFlat fuel inLD inLE k
  | fuel + 1, inLD, inLE, .jnz _ t _ => findFirstJumpFlat fuel inLD inLE t
  | _ + 1, _, _, _ => none

/-- Direct `TFlat` mirror of `IfOptImpl.findFirstJumpStore`. -/
def findFirstJumpStoreFlat {rs : List Ty} :
    Nat → Nat → Trie ((ts : List Ty) × JLabel KL ts) → TFlat rs → Option (TaggedTarget KL)
  | 0, _, _, _ => none
  | _ + 1, inLD, inLE, .jump (ts := ts) j _ =>
    match resolveLabel inLD inLE ts j with
    | some (.tag id lbl) => some ⟨ts, id, lbl⟩
    | _ => none
  | fuel + 1, inLD, inLE, .let_ _ k => findFirstJumpStoreFlat fuel inLD inLE k
  | fuel + 1, inLD, inLE, .load _ _ k => findFirstJumpStoreFlat fuel inLD inLE k
  | fuel + 1, inLD, inLE, .store _ _ k => findFirstJumpStoreFlat fuel inLD inLE k
  | _ + 1, _, _, _ => none

/-- Direct `TFlat` mirror of `IfOptImpl.checkArm` (structurally recursive on `tf` for kernel
reduction without `WellFounded.fix`). -/
def checkArmFlat (tgt : ArmTarget)
    (jnzFuel letFuel inLD : Nat) (inLE : Trie ((ts : List Ty) × JLabel KL ts))
    {rs : List Ty} (tf : TFlat rs) : Option (ArmPlan × Nat) :=
  match tf with
  | .let_ op k =>
    if isSafeOp op.code then
      match letFuel with
      | 0 => none
      | letFuel' + 1 =>
        (checkArmFlat tgt jnzFuel letFuel' inLD inLE k).map fun (p, rem) => (.let_ p, rem)
    else none
  | .jump (ts := ts) j _ =>
    match resolveLabel inLD inLE ts j with
    | some jl =>
      match tgt, jl with
      | .loc jId jTs, .loc id
      | .tag jId jTs, .tag id _ =>
        if id == jId && Ty.listBeq ts jTs then some (.jump, letFuel) else none
      | _, _ => none
    | none => none
  | .ret _ =>
    match tgt with
    | .ret => some (.ret, letFuel)
    | _ => none
  | .jnz _ t e =>
    match jnzFuel with
    | 0 => none
    | jnzFuel' + 1 => do
      let (pT, rem1) ← checkArmFlat tgt jnzFuel' letFuel inLD inLE t
      let (pE, rem2) ← checkArmFlat tgt jnzFuel' rem1 inLD inLE e
      pure (.jnz pT pE, rem2)
  | _ => none
termination_by structural tf

/-- Direct `TFlat` mirror of `IfOptImpl.checkStoreTail` (structurally recursive on `tf` for kernel
reduction without `WellFounded.fix`). -/
def checkStoreTailFlat (tgt : ArmTarget)
    (letFuel inLD : Nat) (inLE : Trie ((ts : List Ty) × JLabel KL ts))
    {rs : List Ty} (tf : TFlat rs) : Option StoreTail :=
  match tf with
  | .let_ op k =>
    if isSafeOp op.code then
      match letFuel with
      | 0 => none
      | letFuel' + 1 => (checkStoreTailFlat tgt letFuel' inLD inLE k).map .let_
    else none
  | .jump (ts := ts) j _ =>
    match resolveLabel inLD inLE ts j with
    | some jl =>
      match tgt, jl with
      | .loc jId jTs, .loc id
      | .tag jId jTs, .tag id _ =>
        if id == jId && Ty.listBeq ts jTs then some .jump else none
      | _, _ => none
    | none => none
  | .ret _ =>
    match tgt with
    | .ret => some .ret
    | _ => none
  | _ => none
termination_by structural tf

/-- Direct `TFlat` mirror of `IfOptImpl.checkStoreArm` (structurally recursive on `tf` for kernel
reduction without `WellFounded.fix`). -/
def checkStoreArmFlat (tgt : ArmTarget) (allowNewLoads : Bool)
    (letFuel loadFuel : Nat) (tbl : SymTbl) (hits : List Nat)
    (inVD : Nat) (inVE : Trie ((t : Ty) × IVal K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × JLabel KL ts))
    {rs : List Ty} (tf : TFlat rs) : Option (StoreArmPlan × SymTbl) :=
  match tf with
  | .let_ (ts := ts) op k =>
    if isSafeOp op.code then
      match letFuel with
      | 0 => none
      | letFuel' + 1 =>
        let args' := resolveEnvArgs inVD inVE op.args
        let (resKeys, tbl') := tbl.internOp op.code (tupIKeys args')
        let wrapped := dummyKeyIVals (V := K) ts resKeys
        (checkStoreArmFlat tgt allowNewLoads letFuel' loadFuel tbl' hits
          (inVD + ts.length) (insertTupEnv inVD inVE wrapped) inLD inLE k).map
          fun (ap, tbl'') => ({ ap with step := .let_ ap.step }, tbl'')
    else none
  | .load t a k =>
    let aKey := ikey (resolveEnvArg inVD inVE a)
    match findSymLoad tbl.loads t aKey with
    | some entry =>
      let hits' := if hits.contains entry.slot then hits else entry.slot :: hits
      let lv : IVal K t := (.imm default, .var entry.vn)
      (checkStoreArmFlat tgt allowNewLoads letFuel loadFuel tbl hits'
        (inVD + 1) (inVE.insert inVD ⟨t, lv⟩) inLD inLE k).map
        fun (ap, tbl') => ({ ap with step := .loadReuse entry.slot ap.step }, tbl')
    | none =>
      if allowNewLoads then
        match loadFuel with
        | 0 => none
        | loadFuel' + 1 =>
          let slot := tbl.loads.length
          let vn := tbl.vnNext
          let entry : SymLoadEntry := ⟨slot, t, aKey, vn⟩
          let tbl' : SymTbl := { tbl with vnNext := vn + 1, loads := tbl.loads ++ [entry] }
          let hits' := slot :: hits
          let lv : IVal K t := (.imm default, .var vn)
          (checkStoreArmFlat tgt allowNewLoads letFuel loadFuel' tbl' hits'
            (inVD + 1) (inVE.insert inVD ⟨t, lv⟩) inLD inLE k).map
            fun (ap, tbl'') => ({ ap with step := .loadEmit ap.step }, tbl'')
      else none
  | .store (t := st) _ a tail =>
    let aKey := ikey (resolveEnvArg inVD inVE a)
    (checkStoreTailFlat tgt letFuel inLD inLE tail).map fun tailPlan =>
      ({ step := .store tailPlan, storeTy := st, storeAddr := aKey, hitSlots := hits }, tbl)
  | _ => none
termination_by structural tf

/-- Direct `TFlat` mirror of `IfOptImpl.checkStoreArms`. -/
def checkStoreArmsFlat (bitsOnly : Bool) (tgt : ArmTarget)
    (inVD : Nat) (inVE : Trie ((t : Ty) × IVal K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × JLabel KL ts))
    (outVD : Nat) {rs : List Ty} (t e : TFlat rs) : Option StoreDiamondPlan := do
  let tbl0 : SymTbl := ⟨outVD, [], []⟩
  let (apT, tbl1) ← checkStoreArmFlat tgt true 12 2 tbl0 [] inVD inVE inLD inLE t
  guard (isSelectTyWith bitsOnly apT.storeTy)
  let (apE, _) ← checkStoreArmFlat tgt false 12 0 tbl1 [] inVD inVE inLD inLE e
  match tyDecEq apT.storeTy apE.storeTy with
  | isFalse _ => none
  | isTrue _ =>
    guard (fKeyBeq apT.storeAddr apE.storeAddr)
    let numLoads := tbl1.loads.length
    guard ((List.range numLoads).all fun s => apE.hitSlots.contains s)
    pure ⟨apT.step, apE.step, apT.storeTy, numLoads⟩

/-- Direct `TFlat` mirror of `IfOptImpl.checkDiamondWith`. -/
def checkDiamondFlat (bitsOnly : Bool) (jId : Nat) (jTs : List Ty)
    (inVD : Nat) (inVE : Trie ((t : Ty) × IVal K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × JLabel KL ts))
    (outVD : Nat) {rs : List Ty} :
    TFlat rs → Option DiamondPlan
  | .let_ (ts := ts) _ k =>
    let wrapped := dummyIVals (V := K) ts outVD
    (checkDiamondFlat bitsOnly jId jTs (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
      inLD inLE (outVD + ts.length) k).map .let_
  | .load t _ k =>
    let inVE' := inVE.insert inVD ⟨t, (.imm default, .var outVD)⟩
    (checkDiamondFlat bitsOnly jId jTs (inVD + 1) inVE' inLD inLE (outVD + 1) k).map .load
  | .store _ _ k =>
    (checkDiamondFlat bitsOnly jId jTs inVD inVE inLD inLE outVD k).map .store
  | .call _ bs _ k =>
    let wrapped := dummyIVals (V := K) bs outVD
    (checkDiamondFlat bitsOnly jId jTs (inVD + bs.length) (insertTupEnv inVD inVE wrapped)
      inLD inLE (outVD + bs.length) k).map .call
  | .jnz _ t e =>
    if isSelectSigWith bitsOnly jTs then
      match checkArmFlat (.loc jId jTs) 2 4 inLD inLE t,
            checkArmFlat (.loc jId jTs) 2 4 inLD inLE e with
      | some (pT, _), some (pE, _) =>
        some (.jnz pT pE)
      | _, _ =>
        (checkStoreArmsFlat bitsOnly (.loc jId jTs) inVD inVE inLD inLE outVD t e).map .jnzStore
    else none
  | _ => none

/-- Direct `TFlat` mirror of `IfOptImpl.mkPairIValArg`. -/
def mkPairIValArgFlat {rs : List Ty} {a b : Ty}
    (outVD : Nat) (x : Arg (IVal K) a) (y : Arg (IVal K) b)
    (cont : Nat → Arg (IVal K) (.pair a b) → TFlat rs) : TFlat rs :=
  match iout x, iout y with
  | .imm cx, .imm cy => cont outVD (.imm (cx, cy))
  | vx, vy =>
    .let_ ⟨.mkpair a b, (idxArg outVD vx, idxArg outVD vy, ())⟩
      (cont (outVD + 1) (.var (.var outVD, .var outVD)))

/-- Direct `TFlat` mirror of `IfOptImpl.splitPairIVal`. -/
def splitPairIValFlat {rs : List Ty} {a b : Ty}
    (outVD : Nat) (p : Arg (IVal K) (.pair a b))
    (cont : Nat → Arg (IVal K) a → Arg (IVal K) b → TFlat rs) : TFlat rs :=
  match iout p with
  | .imm (c₁, c₂) => cont outVD (.imm c₁) (.imm c₂)
  | .var v =>
    .let_ ⟨.unpair a b, (idxArg outVD (.var v), ())⟩
      (cont (outVD + 2)
        (.var (.var outVD, .var outVD))
        (.var (.var (outVD + 1), .var (outVD + 1))))

/-- Direct `TFlat` mirror of `IfOptImpl.emitSelectTyIVal`. -/
def emitSelectTyIValFlat {rs : List Ty} (c : Arg K .bool) :
    (t : Ty) → Nat → Arg (IVal K) t → Arg (IVal K) t →
    (Nat → Arg (IVal K) t → TFlat rs) → TFlat rs
  | .bool, outVD, aT, aE, cont
  | .bits _, outVD, aT, aE, cont =>
    if fKeyBeq (ikey aT) (ikey aE) then cont outVD aT
    else
      .let_ ⟨.select _, (idxArg outVD c, idxArg outVD (iout aT), idxArg outVD (iout aE), ())⟩
        (cont (outVD + 1) (.var (.var outVD, .var outVD)))
  | .float _, outVD, aT, _, cont => cont outVD aT
  | .pair a b, outVD, aT, aE, cont =>
    if fKeyBeq (ikey aT) (ikey aE) then cont outVD aT
    else
      splitPairIValFlat outVD aT fun od₁ aT₁ aT₂ =>
      splitPairIValFlat od₁ aE fun od₂ aE₁ aE₂ =>
      emitSelectTyIValFlat c a od₂ aT₁ aE₁ fun od₃ r₁ =>
      emitSelectTyIValFlat c b od₃ aT₂ aE₂ fun od₄ r₂ =>
      mkPairIValArgFlat od₄ r₁ r₂ cont

/-- Direct `TFlat` mirror of `IfOptImpl.emitSelectTupIVal`. -/
def emitSelectTupIValFlat {rs : List Ty} (c : Arg K .bool) :
    (ts : List Ty) → Nat → Tup (Arg (IVal K)) ts → Tup (Arg (IVal K)) ts →
    (Nat → Tup (Arg (IVal K)) ts → TFlat rs) → TFlat rs
  | [], outVD, (), (), cont => cont outVD ()
  | t :: ts, outVD, (aT, asT), (aE, asE), cont =>
    emitSelectTyIValFlat c t outVD aT aE fun od' r =>
    emitSelectTupIValFlat c ts od' asT asE fun od'' rs' =>
    cont od'' (r, rs')

/-- Direct `TFlat` mirror of `IfOptImpl.emitSelectTy`. -/
def emitSelectTyFlat {rs : List Ty} (c : Arg K .bool) (t : Ty) (outVD : Nat)
    (aT aE : Arg (IVal K) t) (cont : Nat → Arg K t → TFlat rs) : TFlat rs :=
  emitSelectTyIValFlat c t outVD aT aE fun od' r => cont od' (iout r)

/-- Direct `TFlat` mirror of `IfOptImpl.emitSelectTup`. -/
def emitSelectTupFlat {rs : List Ty} (c : Arg K .bool) (ts : List Ty) (outVD : Nat)
    (asT asE : Tup (Arg (IVal K)) ts)
    (cont : Nat → Tup (Arg K) ts → TFlat rs) : TFlat rs :=
  emitSelectTupIValFlat c ts outVD asT asE fun od' sel => cont od' (tupIOut sel)

/-- Direct `TFlat` mirror of `IfOptImpl.hoistArm`. -/
def hoistArmFlat {rs : List Ty} (jTs : List Ty) :
    ArmPlan → TFlat rs → Nat → Trie ((t : Ty) × IVal K t) → Nat →
    (Nat → Tup (Arg (IVal K)) jTs → TFlat rs) → TFlat rs
  | .jump, .jump (ts := ts) _ args, inVD, inVE, outVD, cont =>
    let args' := resolveEnvArgs inVD inVE args
    match listTyDecEq ts jTs with
    | isTrue h => cont outVD (h ▸ args')
    | isFalse _ => .hlt
  | .ret, .ret vs, inVD, inVE, outVD, cont =>
    let vs' := resolveEnvArgs inVD inVE vs
    match listTyDecEq rs jTs with
    | isTrue h => cont outVD (h ▸ vs')
    | isFalse _ => .hlt
  | .let_ rest, .let_ (ts := ts) op k, inVD, inVE, outVD, cont =>
    let args' := resolveEnvArgs inVD inVE op.args
    let wrapped := freshIVals ts (Tup.levels ts outVD) outVD
    .let_ ⟨op.code, idxArgs outVD (tupIOut args')⟩
      (hoistArmFlat jTs rest k (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
        (outVD + ts.length) cont)
  | .jnz pT pE, .jnz c t e, inVD, inVE, outVD, cont =>
    let c' := iout (resolveEnvArg inVD inVE c)
    hoistArmFlat jTs pT t inVD inVE outVD fun od₁ argsT =>
    hoistArmFlat jTs pE e inVD inVE od₁ fun od₂ argsE =>
    emitSelectTupIValFlat c' jTs od₂ argsT argsE cont
  | _, _, _, _, _, _ => .hlt

/-- Direct `TFlat` mirror of `IfOptImpl.hoistJnzArms`. -/
def hoistJnzArmsFlat {rs : List Ty} (jTs : List Ty)
    (pT pE : ArmPlan) (c : Arg K .bool) (t e : TFlat rs)
    (inVD : Nat) (inVE : Trie ((t : Ty) × IVal K t)) (outVD : Nat)
    (fin : Nat → Tup (Arg K) jTs → TFlat rs) : TFlat rs :=
  hoistArmFlat jTs pT t inVD inVE outVD fun od₁ argsT =>
  hoistArmFlat jTs pE e inVD inVE od₁ fun od₂ argsE =>
  emitSelectTupFlat c jTs od₂ argsT argsE fin

/-- Direct `TFlat` mirror of `IfOptImpl.hoistStoreTail`. -/
def hoistStoreTailFlat {rs : List Ty} (jTs : List Ty) :
    StoreTail → TFlat rs → Nat → Trie ((t : Ty) × IVal K t) → Nat →
    (Nat → Tup (Arg (IVal K)) jTs → TFlat rs) → TFlat rs
  | .jump, .jump (ts := ts) _ args, inVD, inVE, outVD, cont =>
    let args' := resolveEnvArgs inVD inVE args
    match listTyDecEq ts jTs with
    | isTrue h => cont outVD (h ▸ args')
    | isFalse _ => .hlt
  | .ret, .ret vs, inVD, inVE, outVD, cont =>
    let vs' := resolveEnvArgs inVD inVE vs
    match listTyDecEq rs jTs with
    | isTrue h => cont outVD (h ▸ vs')
    | isFalse _ => .hlt
  | .let_ rest, .let_ (ts := ts) op k, inVD, inVE, outVD, cont =>
    let args' := resolveEnvArgs inVD inVE op.args
    let wrapped := freshIVals ts (Tup.levels ts outVD) outVD
    .let_ ⟨op.code, idxArgs outVD (tupIOut args')⟩
      (hoistStoreTailFlat jTs rest k (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
        (outVD + ts.length) cont)
  | _, _, _, _, _, _ => .hlt

/-- Direct `TFlat` mirror of `IfOptImpl.hoistStoreStep`. -/
def hoistStoreStepFlat {rs : List Ty} (jTs : List Ty) (st : Ty) :
    StoreStep → TFlat rs → Nat → Trie ((t : Ty) × IVal K t) → Nat →
    List ((t : Ty) × IVal K t) →
    (Nat → List ((t : Ty) × IVal K t) → Arg (IVal K) st → Arg (IVal K) i64 →
      Tup (Arg (IVal K)) jTs → TFlat rs) →
    TFlat rs
  | .let_ rest, .let_ (ts := ts) op k, inVD, inVE, outVD, loads, cont =>
    let args' := resolveEnvArgs inVD inVE op.args
    let wrapped := freshIVals ts (Tup.levels ts outVD) outVD
    .let_ ⟨op.code, idxArgs outVD (tupIOut args')⟩
      (hoistStoreStepFlat jTs st rest k (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
        (outVD + ts.length) loads cont)
  | .loadEmit rest, .load t a k, inVD, inVE, outVD, loads, cont =>
    let a' := iout (resolveEnvArg inVD inVE a)
    let iv : IVal K t := (.var outVD, .var outVD)
    let inVE' := inVE.insert inVD ⟨t, iv⟩
    .load t (idxArg outVD a')
      (hoistStoreStepFlat jTs st rest k (inVD + 1) inVE' (outVD + 1) (loads ++ [⟨t, iv⟩]) cont)
  | .loadReuse slot rest, .load t _ k, inVD, inVE, outVD, loads, cont =>
    match loads[slot]? with
    | some ⟨t', iv⟩ =>
      match tyDecEq t' t with
      | isTrue h =>
        let inVE' := inVE.insert inVD ⟨t, h ▸ iv⟩
        hoistStoreStepFlat jTs st rest k (inVD + 1) inVE' outVD loads cont
      | isFalse _ => .hlt
    | none => .hlt
  | .store tail, .store (t := st') v a k, inVD, inVE, outVD, loads, cont =>
    let v' := resolveEnvArg inVD inVE v
    let a' := resolveEnvArg inVD inVE a
    match tyDecEq st' st with
    | isTrue h =>
      hoistStoreTailFlat jTs tail k inVD inVE outVD fun od' exitArgs =>
        cont od' loads (h ▸ v') a' exitArgs
    | isFalse _ => .hlt
  | _, _, _, _, _, _, _ => .hlt

/-- Direct `TFlat` mirror of `IfOptImpl.hoistStoreArms`. -/
def hoistStoreArmsFlat {rs : List Ty} (jTs : List Ty)
    (sp : StoreDiamondPlan) (c : Arg K .bool) (t e : TFlat rs)
    (inVD : Nat) (inVE : Trie ((t : Ty) × IVal K t)) (outVD : Nat)
    (fin : Nat → Tup (Arg K) jTs → TFlat rs) : TFlat rs :=
  hoistStoreStepFlat jTs sp.storeTy sp.armT t inVD inVE outVD [] fun od₁ loads₁ vT aT argsT =>
  hoistStoreStepFlat jTs sp.storeTy sp.armE e inVD inVE od₁ loads₁ fun od₂ _ vE _ argsE =>
  emitSelectTyFlat c sp.storeTy od₂ vT vE fun od₃ selVal =>
  .store (idxArg od₃ selVal) (idxArg od₃ (iout aT))
    (emitSelectTupFlat c jTs od₃ argsT argsE fin)

/-- Direct `TFlat` mirror of `IfOptImpl.hoistDiamond`. -/
def hoistDiamondFlat {rs : List Ty} {jTs : List Ty} (jLbl : KL jTs) :
    DiamondPlan → TFlat rs → Nat → Trie ((t : Ty) × IVal K t) → Nat → Nat → TFlat rs
  | .jnz pT pE, .jnz c t e, inVD, inVE, outVD, outLD =>
    let c' := iout (resolveEnvArg inVD inVE c)
    hoistJnzArmsFlat jTs pT pE c' t e inVD inVE outVD fun od' selArgs =>
      .jump (idxLabel outLD jLbl) (idxArgs od' selArgs)
  | .jnzStore sp, .jnz c t e, inVD, inVE, outVD, outLD =>
    let c' := iout (resolveEnvArg inVD inVE c)
    hoistStoreArmsFlat jTs sp c' t e inVD inVE outVD fun od' selArgs =>
      .jump (idxLabel outLD jLbl) (idxArgs od' selArgs)
  | .let_ rest, .let_ (ts := ts) op k, inVD, inVE, outVD, outLD =>
    let args' := resolveEnvArgs inVD inVE op.args
    let wrapped := freshIVals ts (Tup.levels ts outVD) outVD
    .let_ ⟨op.code, idxArgs outVD (tupIOut args')⟩
      (hoistDiamondFlat jLbl rest k (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
        (outVD + ts.length) outLD)
  | .load rest, .load t a k, inVD, inVE, outVD, outLD =>
    let a' := iout (resolveEnvArg inVD inVE a)
    let inVE' := inVE.insert inVD ⟨t, (.var outVD, .var outVD)⟩
    .load t (idxArg outVD a')
      (hoistDiamondFlat jLbl rest k (inVD + 1) inVE' (outVD + 1) outLD)
  | .store rest, .store v a k, inVD, inVE, outVD, outLD =>
    let v' := iout (resolveEnvArg inVD inVE v)
    let a' := iout (resolveEnvArg inVD inVE a)
    .store (idxArg outVD v') (idxArg outVD a')
      (hoistDiamondFlat jLbl rest k inVD inVE outVD outLD)
  | .call rest, .call f bs args k, inVD, inVE, outVD, outLD =>
    let args' := resolveEnvArgs inVD inVE args
    let wrapped := freshIVals bs (Tup.levels bs outVD) outVD
    .call f bs (idxArgs outVD (tupIOut args'))
      (hoistDiamondFlat jLbl rest k (inVD + bs.length) (insertTupEnv inVD inVE wrapped)
        (outVD + bs.length) outLD)
  | _, _, _, _, _, _ => .hlt

/-- Direct `TFlat` mirror of `IfOptImpl.tryPureJnzDiamond`. -/
def tryPureJnzDiamondFlat {rs : List Ty} (bitsOnly : Bool)
    (c : Arg K .bool) (t e : TFlat rs)
    (inVD : Nat) (inVE : Trie ((t : Ty) × IVal K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × JLabel KL ts))
    (outVD outLD : Nat) : Option (TFlat rs) :=
  match findFirstJumpFlat 8 inLD inLE t with
  | some ⟨jTs, jId, jLbl⟩ =>
    if isSelectSigWith bitsOnly jTs then
      match checkArmFlat (.tag jId jTs) 2 4 inLD inLE t,
            checkArmFlat (.tag jId jTs) 2 4 inLD inLE e with
      | some (pT, _), some (pE, _) =>
        some (hoistJnzArmsFlat jTs pT pE c t e inVD inVE outVD fun od' selArgs =>
          .jump (idxLabel outLD jLbl) (idxArgs od' selArgs))
      | _, _ => none
    else none
  | none =>
    if isSelectSigWith bitsOnly rs then
      match checkArmFlat .ret 2 4 inLD inLE t,
            checkArmFlat .ret 2 4 inLD inLE e with
      | some (pT, _), some (pE, _) =>
        some (hoistJnzArmsFlat rs pT pE c t e inVD inVE outVD fun od' selArgs =>
          .ret (idxArgs od' selArgs))
      | _, _ => none
    else none

/-- Direct `TFlat` mirror of `IfOptImpl.tryStoreJnzDiamond`. -/
def tryStoreJnzDiamondFlat {rs : List Ty} (bitsOnly : Bool)
    (c : Arg K .bool) (t e : TFlat rs)
    (inVD : Nat) (inVE : Trie ((t : Ty) × IVal K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × JLabel KL ts))
    (outVD outLD : Nat) : Option (TFlat rs) :=
  match findFirstJumpStoreFlat 16 inLD inLE t with
  | some ⟨jTs, jId, jLbl⟩ =>
    if isSelectSigWith bitsOnly jTs then
      (checkStoreArmsFlat bitsOnly (.tag jId jTs) inVD inVE inLD inLE outVD t e).map fun sp =>
        hoistStoreArmsFlat jTs sp c t e inVD inVE outVD fun od' selArgs =>
          .jump (idxLabel outLD jLbl) (idxArgs od' selArgs)
    else none
  | none =>
    if isSelectSigWith bitsOnly rs then
      (checkStoreArmsFlat bitsOnly .ret inVD inVE inLD inLE outVD t e).map fun sp =>
        hoistStoreArmsFlat rs sp c t e inVD inVE outVD fun od' selArgs =>
          .ret (idxArgs od' selArgs)
    else none

/-- Direct `TFlat` mirror of `IfOptImpl.tryJnzDiamond`. -/
def tryJnzDiamondFlat {rs : List Ty} (bitsOnly : Bool)
    (c : Arg K .bool) (t e : TFlat rs)
    (inVD : Nat) (inVE : Trie ((t : Ty) × IVal K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × JLabel KL ts))
    (outVD outLD : Nat) : Option (TFlat rs) :=
  match tryPureJnzDiamondFlat bitsOnly c t e inVD inVE inLD inLE outVD outLD with
  | some r => some r
  | none => tryStoreJnzDiamondFlat bitsOnly c t e inVD inVE inLD inLE outVD outLD

mutual
/-- Recursive `TFlat` mirror of `LeanQbe.T.ifOptWith`. -/
def ifOptWithFlat {rs : List Ty} (bitsOnly : Bool) (depth : Nat) :
    TFlat rs → Nat → Trie ((t : Ty) × IVal K t) →
    Nat → Trie ((ts : List Ty) × JLabel KL ts) → Nat → Nat → TFlat rs
  | .let_ (ts := ts) op k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let args' := resolveEnvArgs inVD inVE op.args
    let wrapped := freshIVals ts (Tup.levels ts outVD) outVD
    .let_ ⟨op.code, idxArgs outVD (tupIOut args')⟩
      (ifOptWithFlat bitsOnly depth k (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
        inLD inLE (outVD + ts.length) outLD)
  | .load t a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let a' := iout (resolveEnvArg inVD inVE a)
    let inVE' := inVE.insert inVD ⟨t, (.var outVD, .var outVD)⟩
    .load t (idxArg outVD a')
      (ifOptWithFlat bitsOnly depth k (inVD + 1) inVE' inLD inLE (outVD + 1) outLD)
  | .store v a k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let v' := iout (resolveEnvArg inVD inVE v)
    let a' := iout (resolveEnvArg inVD inVE a)
    .store (idxArg outVD v') (idxArg outVD a')
      (ifOptWithFlat bitsOnly depth k inVD inVE inLD inLE outVD outLD)
  | .call f bs args k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let args' := resolveEnvArgs inVD inVE args
    let wrapped := freshIVals bs (Tup.levels bs outVD) outVD
    .call f bs (idxArgs outVD (tupIOut args'))
      (ifOptWithFlat bitsOnly depth k (inVD + bs.length) (insertTupEnv inVD inVE wrapped)
        inLD inLE (outVD + bs.length) outLD)
  | .jnz c t e, inVD, inVE, inLD, inLE, outVD, outLD =>
    let c' := iout (resolveEnvArg inVD inVE c)
    let fallback :=
      .jnz (idxArg outVD c')
        (ifOptWithFlat bitsOnly depth t inVD inVE inLD inLE outVD outLD)
        (ifOptWithFlat bitsOnly depth e inVD inVE inLD inLE outVD outLD)
    if bitsOnly then
      (tryJnzDiamondFlat bitsOnly c' t e inVD inVE inLD inLE outVD outLD).getD fallback
    else fallback
  | .jump (ts := ts) j args, inVD, inVE, inLD, inLE, outVD, outLD =>
    match resolveLabel inLD inLE ts j with
    | some jl =>
      match unwrapJLabel jl with
      | some l =>
        .jump (idxLabel outLD l) (idxArgs outVD (tupIOut (resolveEnvArgs inVD inVE args)))
      | none => .hlt
    | none => .hlt
  | .ret vs, inVD, inVE, _, _, outVD, _ =>
    .ret (idxArgs outVD (tupIOut (resolveEnvArgs inVD inVE vs)))
  | .exit f args, inVD, inVE, _, _, outVD, _ =>
    .exit f (idxArgs outVD (tupIOut (resolveEnvArgs inVD inVE args)))
  | .hlt, _, _, _, _, _, _ => .hlt
  | .group (sig := sig) bodies k, inVD, inVE, inLD, inLE, outVD, outLD =>
    let outJs := Tup.levels sig outLD
    let inLD' := inLD + sig.length
    let outLD' := outLD + sig.length
    if bitsOnly then
      let tagged := tagLabels depth outJs
      let inLE' := insertTupEnv inLD inLE tagged
      .group (sig := sig)
        (ifOptBWithFlat true (depth + sig.length) bodies inVD inVE inLD' inLE' outVD outLD')
        (ifOptWithFlat true (depth + sig.length) k inVD inVE inLD' inLE' outVD outLD')
    else
      match sig, bodies with
      | [], bodies =>
        .group (sig := [])
          (ifOptBWithFlat false depth bodies inVD inVE inLD inLE outVD outLD)
          (ifOptWithFlat false depth k inVD inVE inLD inLE outVD outLD)
      | [ts], bodies =>
        let plan? := checkDiamondFlat false depth ts inVD inVE (inLD + 1)
          (inLE.insert inLD ⟨ts, .loc depth⟩) outVD k
        let inLE' := inLE.insert inLD ⟨ts, .outer outLD⟩
        .group (sig := [ts])
          (ifOptBWithFlat false (depth + 1) bodies inVD inVE inLD' inLE' outVD outLD')
          (match plan? with
           | some plan => hoistDiamondFlat (jTs := ts) outLD plan k inVD inVE outVD outLD'
           | none => ifOptWithFlat false (depth + 1) k inVD inVE inLD' inLE' outVD outLD')
      | ts₁ :: ts₂ :: rest, bodies =>
        let sig' := ts₁ :: ts₂ :: rest
        let outJs' := Tup.levels sig' outLD
        let outer := outJs'.map fun _ l => JLabel.outer l
        let inLE' := insertTupEnv inLD inLE outer
        let inLD'' := inLD + sig'.length
        let outLD'' := outLD + sig'.length
        .group (sig := sig')
          (ifOptBWithFlat false (depth + rest.length + 2) bodies
            inVD inVE inLD'' inLE' outVD outLD'')
          (ifOptWithFlat false (depth + rest.length + 2) k
            inVD inVE inLD'' inLE' outVD outLD'')

/-- Block-list companion of `ifOptWithFlat`. -/
def ifOptBWithFlat {rs : List Ty} (bitsOnly : Bool) (depth : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × IVal K t) →
    Nat → Trie ((ts : List Ty) × JLabel KL ts) → Nat → Nat → TBlocks rs sig
  | _, .nil, _, _, _, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inVD, inVE, inLD, inLE, outVD, outLD =>
    let wrapped := freshIVals ts (Tup.levels ts outVD) outVD
    .cons
      (ifOptWithFlat bitsOnly depth b (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
        inLD inLE (outVD + ts.length) outLD)
      (ifOptBWithFlat bitsOnly depth bs inVD inVE inLD inLE outVD outLD)
end

/-- True iff `a : Arg K t` at de Bruijn depth `curD` refers to binder level `cid`. -/
def flatArgIsLevel (cid curD : Nat) {t : Ty} : Arg K t → Bool
  | .var idx =>
    match levelArg curD (.var idx : Arg K t) with
    | .var lvl => lvl == cid
    | .imm _ => false
  | .imm _ => false

/-- True iff any argument in `args` at depth `curD` refers to binder level `cid`. -/
def flatArgsHasLevel (cid curD : Nat) : {ts : List Ty} → Tup (Arg K) ts → Bool
  | [], () => false
  | _ :: _, (a, as) => flatArgIsLevel cid curD a || flatArgsHasLevel cid curD as

/-- Non-recursive `.let_` step for `shouldDeferCmpFlat`. -/
def shouldDeferCmpFlatStep (cid : Nat) (sawClobber : Bool) (curD : Nat) {rs : List Ty}
    (rec : Bool → Nat → TFlat rs → Bool) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg K) sig → TFlat rs → Bool
  | _, _, .select _, (cond, aT, aE, ()), k =>
    if flatArgIsLevel cid curD cond && !flatArgIsLevel cid curD aT &&
        !flatArgIsLevel cid curD aE then
      sawClobber
    else if flatArgIsLevel cid curD cond || flatArgIsLevel cid curD aT ||
        flatArgIsLevel cid curD aE then
      false
    else
      rec true (curD + 1) k
  | _, ts, code, args, k =>
    if flatArgsHasLevel cid curD args then false
    else
      rec (sawClobber || isCmpClobberOp code) (curD + ts.length) k

/-- Direct `TFlat` mirror of `IfOptImpl.shouldDeferCmp`. -/
def shouldDeferCmpFlat (cid : Nat) : Nat → Bool → Nat → {rs : List Ty} → TFlat rs → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, sawClobber, curD, _, .let_ ⟨code, args⟩ k =>
    shouldDeferCmpFlatStep cid sawClobber curD
      (fun s c k' => shouldDeferCmpFlat cid fuel s c k') code args k
  | _ + 1, _, _, _, _ => false

/-- Direct `TFlat` mirror of `IfOptImpl.matArg`. -/
def matArgFlat {rs : List Ty} (outVD : Nat) (mat : List (Nat × Nat)) :
    {t : Ty} → Arg (SVal K) t →
    (Nat → List (Nat × Nat) → Arg K t → TFlat rs) → TFlat rs
  | _, .imm c, cont => cont outVD mat (.imm c)
  | _, .var (.val a _), cont => cont outVD mat a
  | .bool, .var (.defer d), cont =>
    match lookupMat (V := K) d.id mat with
    | some lvl => cont outVD mat (.var lvl)
    | none =>
      .let_ ⟨.cmp d.co (.bits d.n) .bool rfl,
          (idxArg outVD d.lhs, idxArg outVD d.rhs, ())⟩
        (cont (outVD + 1) ((d.id, outVD) :: mat) (.var outVD))

/-- Direct `TFlat` mirror of `IfOptImpl.matArgs`. -/
def matArgsFlat {rs : List Ty} (outVD : Nat) (mat : List (Nat × Nat)) :
    {ts : List Ty} → Tup (Arg (SVal K)) ts →
    (Nat → List (Nat × Nat) → Tup (Arg K) ts → TFlat rs) → TFlat rs
  | [], (), cont => cont outVD mat ()
  | _ :: _, (a, as), cont =>
    matArgFlat outVD mat a fun od' mat' a' =>
    matArgsFlat od' mat' as fun od'' mat'' as' =>
    cont od'' mat'' (a', as')

mutual
/-- Recursive `TFlat` mirror of `LeanQbe.T.cmpSink`. -/
def cmpSinkWithFlat {rs : List Ty} :
    TFlat rs → Nat → Trie ((t : Ty) × SVal K t) → Nat → List (Nat × Nat) → TFlat rs
  | .let_ (ts := ts) ⟨code, args⟩ k, inVD, inVE, outVD, mat =>
    match code, args, k with
    | .cmp co t m h, args, k =>
      match t, m, h, args, k with
      | .bits n, .bool, _, (a, b, ()), k =>
        let a' := soutBits (resolveEnvArg inVD inVE a)
        let b' := soutBits (resolveEnvArg inVD inVE b)
        if shouldDeferCmpFlat inVD 16 false (inVD + 1) k then
          let d : DeferCmp K := ⟨inVD, n, co, a', b'⟩
          cmpSinkWithFlat k (inVD + 1) (inVE.insert inVD ⟨.bool, .defer d⟩) outVD mat
        else
          let inVE' := inVE.insert inVD ⟨.bool, .val (.var outVD) inVD⟩
          .let_ ⟨.cmp co (.bits n) .bool rfl, (idxArg outVD a', idxArg outVD b', ())⟩
            (cmpSinkWithFlat k (inVD + 1) inVE' (outVD + 1) mat)
      | .bool, m, h, args, k =>
        let args' := resolveEnvArgs inVD inVE args
        matArgsFlat outVD mat args' fun od' mat' margs =>
          let wrapped := freshSVals [m] (Tup.levels [m] od') inVD
          .let_ ⟨.cmp co .bool m h, idxArgs od' margs⟩
            (cmpSinkWithFlat k (inVD + 1) (insertTupEnv inVD inVE wrapped) (od' + 1) mat')
      | .float f, m, h, args, k =>
        let args' := resolveEnvArgs inVD inVE args
        matArgsFlat outVD mat args' fun od' mat' margs =>
          let wrapped := freshSVals [m] (Tup.levels [m] od') inVD
          .let_ ⟨.cmp co (.float f) m h, idxArgs od' margs⟩
            (cmpSinkWithFlat k (inVD + 1) (insertTupEnv inVD inVE wrapped) (od' + 1) mat')
      | .pair x y, m, h, args, k =>
        let args' := resolveEnvArgs inVD inVE args
        matArgsFlat outVD mat args' fun od' mat' margs =>
          let wrapped := freshSVals [m] (Tup.levels [m] od') inVD
          .let_ ⟨.cmp co (.pair x y) m h, idxArgs od' margs⟩
            (cmpSinkWithFlat k (inVD + 1) (insertTupEnv inVD inVE wrapped) (od' + 1) mat')
    | code, args, k =>
      let args' := resolveEnvArgs inVD inVE args
      matArgsFlat outVD mat args' fun od' mat' margs =>
        let wrapped := freshSVals ts (Tup.levels ts od') inVD
        .let_ ⟨code, idxArgs od' margs⟩
          (cmpSinkWithFlat k (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
            (od' + ts.length) mat')
  | .load t a k, inVD, inVE, outVD, mat =>
    matArgFlat outVD mat (resolveEnvArg inVD inVE a) fun od' mat' a' =>
      let inVE' := inVE.insert inVD ⟨t, .val (.var od') inVD⟩
      .load t (idxArg od' a') (cmpSinkWithFlat k (inVD + 1) inVE' (od' + 1) mat')
  | .store v a k, inVD, inVE, outVD, mat =>
    matArgFlat outVD mat (resolveEnvArg inVD inVE v) fun od₁ mat₁ v' =>
    matArgFlat od₁ mat₁ (resolveEnvArg inVD inVE a) fun od₂ mat₂ a' =>
      .store (idxArg od₂ v') (idxArg od₂ a') (cmpSinkWithFlat k inVD inVE od₂ mat₂)
  | .call f bs args k, inVD, inVE, outVD, mat =>
    matArgsFlat outVD mat (resolveEnvArgs inVD inVE args) fun od' mat' args' =>
      let wrapped := freshSVals bs (Tup.levels bs od') inVD
      .call f bs (idxArgs od' args')
        (cmpSinkWithFlat k (inVD + bs.length) (insertTupEnv inVD inVE wrapped)
          (od' + bs.length) mat')
  | .jnz c t e, inVD, inVE, outVD, mat =>
    matArgFlat outVD mat (resolveEnvArg inVD inVE c) fun od' mat' c' =>
      .jnz (idxArg od' c')
        (cmpSinkWithFlat t inVD inVE od' mat')
        (cmpSinkWithFlat e inVD inVE od' mat')
  | .jump j args, inVD, inVE, outVD, mat =>
    matArgsFlat outVD mat (resolveEnvArgs inVD inVE args) fun od' _ args' =>
      .jump j (idxArgs od' args')
  | .ret vs, inVD, inVE, outVD, mat =>
    matArgsFlat outVD mat (resolveEnvArgs inVD inVE vs) fun od' _ vs' =>
      .ret (idxArgs od' vs')
  | .exit f args, inVD, inVE, outVD, mat =>
    matArgsFlat outVD mat (resolveEnvArgs inVD inVE args) fun od' _ args' =>
      .exit f (idxArgs od' args')
  | .hlt, _, _, _, _ => .hlt
  | .group bodies k, inVD, inVE, outVD, mat =>
    .group (cmpSinkBWithFlat bodies inVD inVE outVD mat)
      (cmpSinkWithFlat k inVD inVE outVD mat)

/-- Block-list companion of `cmpSinkWithFlat`. -/
def cmpSinkBWithFlat {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × SVal K t) →
    Nat → List (Nat × Nat) → TBlocks rs sig
  | _, .nil, _, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inVD, inVE, outVD, mat =>
    let wrapped := freshSVals ts (Tup.levels ts outVD) inVD
    .cons
      (cmpSinkWithFlat b (inVD + ts.length) (insertTupEnv inVD inVE wrapped)
        (outVD + ts.length) mat)
      (cmpSinkBWithFlat bs inVD inVE outVD mat)
end

/-- Direct `TFlat` pure `.bits` compare sinking matching
`reifyFunc (Func.cmpSink (denoteFunc tf))`. -/
def cmpSinkFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  cmpSinkWithFlat tf as.length (initEnv (fun x next => .val (.var x) next) as) as.length []

/-- Direct `TFlat` core if-conversion matching
`reifyFunc (Func.ifOptCore bitsOnly (denoteFunc tf))`. -/
def ifOptCoreFlat (bitsOnly : Bool) (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  ifOptWithFlat bitsOnly 0 tf as.length (initEnv (fun x next => (.var x, .var next)) as)
    0 .empty as.length 0

/-- Direct `TFlat` diamond `jnz` → `select` if-conversion matching
`if bitsOnly then reifyFunc (Func.ifOptBits (denoteFunc tf))`
`else reifyFunc (Func.ifOpt (denoteFunc tf))`. -/
def ifOptFlat (bitsOnly : Bool) (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  if bitsOnly then cmpSinkFlat as (ifOptCoreFlat true as tf)
  else ifOptCoreFlat false as tf

/-- `TFlatFn` wrapper for `ifOptFlat`. -/
def ifOptFlatFn (bitsOnly : Bool) (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, ifOptFlat bitsOnly f.as f.body⟩

end IfOptFlat

end OptFlatCfg
end LeanQbe.T
