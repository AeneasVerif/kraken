module

public import LeanQbe.T.FlatDirect
public import LeanQbe.T.LegalFlat
public import LeanQbe.T.RegaFlat
public import LeanQbe.T.Opt
public import LeanQbe.T.OptFlatValue
public import LeanQbe.T.OptFlatMem
public import LeanQbe.T.OptFlatCfg
public import LeanQbe.T.OptFlatAddrRange
public import LeanQbe.T.OptFlatPathCond
public import LeanQbe.T.OptFlatBranch
public import LeanQbe.T.OptFlatLoop

/-!
# Staged `TFlat`-Direct Compilation Driver (`MainFlat`)

Implements first-order `TFlat` equivalents of the mid-end and end-to-end compilation pipeline:

* Native `TFlat` structural/gate/value/mem/CFG/address/path passes: `TFlat.assumeElim`,
  `TFlat.mergeRets`, `OptFlatValue.{foldFlat,copyFlat,canonFlat,gvnFlat}`,
  `OptFlatMem.{memLoadFlat,assumeBitsFlat,divConstFlat}`,
  `OptFlatCfg.{dcePFlat,deadLoadElimFlat,ifOptFlat}`,
  `OptFlatAddrRange.addrRangeOptFlat`, `OptFlatPathCond.pathCondOptFlat`,
  `TFlat.zeroPeelWith`, `simplifyGroupFastFlat`, `peelFastFlat`, `licmFlat`, `loopRotateFlat`.
* Remaining `TFlat`-gated `reifyFunc`-backed bridges (`condThreadPassFlat`, `tailDupFlat`).
* End-to-end entry points matching `Fn.earlyOpt`, `Fn.midFromEarly`, `compileFn`, and
  `compileModule`: `earlyOptFlat`, `midStageFlat`, `compileFlatFn`, `compileModuleFlat`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## 1. Direct `TFlat` Passes (`assumeElim`, `mergeRets`, `divConst`, CFG/Loop Gates) -/

/-- True iff `tf` is `.hlt`. -/
def TFlat.isHlt {rs : List Ty} : TFlat rs → Bool
  | .hlt => true
  | _ => false

/-- Simplify `.jnz c t .hlt → t` and `.jnz c .hlt e → e` on `TFlat`. -/
def TFlat.mkJnzAssume {rs : List Ty} (c : Arg K .bool) (t e : TFlat rs) : TFlat rs :=
  if e.isHlt then t
  else if t.isHlt then e
  else .jnz c t e

mutual
/-- Eliminate impossible branches leading to `.hlt` directly on `TFlat rs`. -/
def TFlat.assumeElim {rs : List Ty} : TFlat rs → TFlat rs
  | .let_ op k => .let_ op k.assumeElim
  | .load t a k => .load t a k.assumeElim
  | .store v a k => .store v a k.assumeElim
  | .call f bs args k => .call f bs args k.assumeElim
  | .jnz c t e => TFlat.mkJnzAssume c t.assumeElim e.assumeElim
  | .jump j args => .jump j args
  | .ret vs => .ret vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group bodies k => .group bodies.assumeElim k.assumeElim

/-- Block-list companion of `TFlat.assumeElim`. -/
def TBlocks.assumeElim {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → TBlocks rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons b.assumeElim bs.assumeElim
end

/-- Direct `TFlat` `assumeElim` entry point. -/
def assumeElimFlat {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  tf.assumeElim

/-- Fresh block-parameter de Bruijn variable indices for `ret (toArgTup r_params)`. -/
def retIdxs : (ts : List Ty) → Tup (Arg K) ts
  | [] => ()
  | _ :: ts => (.var ts.length, retIdxs ts)

mutual
/-- Rewrite every `.ret vs` inside `tf` into `.jump exitIdx vs`, shifting `exitIdx` across inner
`group` binders. -/
def TFlat.mergeRetsAux (exitIdx : Nat) {rs : List Ty} : TFlat rs → TFlat rs
  | .let_ op k => .let_ op (k.mergeRetsAux exitIdx)
  | .load t a k => .load t a (k.mergeRetsAux exitIdx)
  | .store v a k => .store v a (k.mergeRetsAux exitIdx)
  | .call f bs args k => .call f bs args (k.mergeRetsAux exitIdx)
  | .jnz c t e => .jnz c (t.mergeRetsAux exitIdx) (e.mergeRetsAux exitIdx)
  | .jump j args => .jump j args
  | .ret vs => .jump exitIdx vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group (sig := sig) bodies k =>
    .group (bodies.mergeRetsAux (exitIdx + sig.length)) (k.mergeRetsAux (exitIdx + sig.length))

/-- Block-list companion of `TFlat.mergeRetsAux`. -/
def TBlocks.mergeRetsAux (exitIdx : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → TBlocks rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons (b.mergeRetsAux exitIdx) (bs.mergeRetsAux exitIdx)
end

/-- Direct `TFlat` unified epilogue merging matching `Func.mergeRets`. -/
def TFlat.mergeRets {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  if tflatRets tf ≥ 2 then
    .group (sig := [rs]) (.cons (.ret (retIdxs rs)) .nil) (tf.mergeRetsAux 0)
  else
    tf

/-- Direct `TFlat` `mergeRets` entry point. -/
def mergeRetsFlat {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  tf.mergeRets

/-- `TFlat`-gated `simplifyGroupFast` bypassing PHOAS whenever no join candidate or no plan
change occurs. -/
def simplifyGroupFastFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  if hasSimpGroup (tflatLoops tf ≤ 1) tf then
    let (plan, info) := SgpImpl.buildPlan 0 tf
    if info.changed then reifyFunc (Func.simplifyGroupWithPlan plan (denoteFunc (as := as) tf))
    else tf
  else tf

/-- `TFlat`-gated `peelFast` bypassing PHOAS when loop count or node count exceeds budget. -/
def peelFastFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) (budget : Nat := 24) :
    TFlat rs :=
  if tflatLoops tf ≤ 1 && tflatSize tf ≤ 40 then
    reifyFunc (Func.peel (denoteFunc (as := as) tf) budget)
  else tf

/-- Native `TFlat` `licm` (pure + read-only hoisting) via `OptFlatLoop.licmFlat`. -/
def licmFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  OptFlatLoop.licmFlat as tf

/-- Native `TFlat` loop rotation via `OptFlatLoop.loopRotateFlat`. -/
def loopRotateFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig) : TFlat rs :=
  OptFlatLoop.loopRotateFlat as tf cfg

/-! ## 2. Native `OptFlat{AddrRange,PathCond}` & Gated Bridges (`condThreadPass`, `tailDup`) -/

/-- Native `TFlat` loop-aware address reassociation and range-check collapse (`addrRangeOptWith`). -/
def addrRangeOptFlatWith (foldDisp : Bool) (as : List Ty) {rs : List Ty} (tf : TFlat rs) :
    TFlat rs :=
  OptFlatAddrRange.addrRangeOptFlatWith foldDisp as tf

/-- Native `TFlat` loop-aware address reassociation and range-check collapse (`addrRangeOpt`). -/
def addrRangeOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  addrRangeOptFlatWith false as tf

/-- Native `TFlat` dominating path-fact and known-condition pass (`pathCondOpt`). -/
def pathCondOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  OptFlatPathCond.pathCondOptFlat as tf

/-- Native `TFlat` `condThreadPass` matching `reifyFunc (Func.condThreadPass (denoteFunc tf))`. -/
def condThreadPassFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  OptFlatBranch.condThreadPassFlat as tf

/-- `condThreadLateOpt` (`OptFlatPathCond.pathCondOptFlat` + `TFlat`-gated `condThreadPassFlat`). -/
def condThreadLateOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  condThreadPassFlat as (pathCondOptFlat as tf)

/-- Native `TFlat` `tailDup` matching `reifyFunc (Func.tailDup (denoteFunc tf) cfg)`. -/
def tailDupFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (cfg : TailDup.TailDupConfig := {}) : TFlat rs :=
  OptFlatBranch.tailDupFlat as tf cfg

/-! ## 3. End-to-End `earlyOptFlat`, `midStageFlat`, `compileFlatFn`, `compileModuleFlat` -/

/-- First-order mirror of `Fn.earlyOpt`. -/
def earlyOptFlat (f : TFlatFn) : TFlatFn :=
  let tf0 := OptFlatValue.foldFlat f.as (OptFlatValue.copyFlat f.as
    (OptFlatValue.gvnFlat f.as (OptFlatValue.copyFlat f.as
      (OptFlatValue.canonFlat f.as (OptFlatValue.foldFlat f.as f.body)))))
  let tf1 := OptFlatCfg.ifOptFlat false f.as tf0
  let tf2 := simplifyGroupFastFlat f.as tf1
  let tf3 := peelFastFlat f.as tf2 24
  let tf4 := TFlat.zeroPeelWith { peelBudget := 24 } tf3
  let tf5 := OptFlatCfg.dcePFlat f.as
    (OptFlatValue.foldFlat f.as (OptFlatValue.copyFlat f.as tf4))
  ⟨f.name, f.as, f.rs, tf5⟩

/-- First-order mirror of `Fn.midFromEarly` (matching `Fn.midStage` stages verbatim). -/
def midStageFlat (lt : LegalTarget) (ef : TFlatFn) : TFlatFn :=
  let as' := lt.legalSig ef.as
  let rs' := lt.legalSig ef.rs
  let tf0 := legalFlat lt (as := ef.as) ef.body
  let tf1 := OptFlatValue.copyFlat as' (OptFlatMem.divConstFlat as'
    (OptFlatValue.canonFlat as' (OptFlatValue.foldFlat as' tf0)))
  let tf2 := OptFlatValue.foldFlat as' (OptFlatMem.assumeBitsFlat as'
    (OptFlatValue.gvnFlat as' (OptFlatMem.memLoadFlat as' tf1)))
  let tf3 := OptFlatValue.gvnFlat as' (addrRangeOptFlatWith lt.foldAddrDisp as'
    (OptFlatValue.foldFlat as' (assumeElimFlat (OptFlatCfg.deadLoadElimFlat as'
      (simplifyGroupFastFlat as' (OptFlatCfg.ifOptFlat true as' tf2))))))
  let tf4 := loopRotateFlat as' (OptFlatCfg.dcePFlat as' (licmFlat as' tf3))
  let tf5 := mergeRetsFlat (tailDupFlat as' (OptFlatCfg.dcePFlat as'
    (OptFlatValue.foldFlat as' (condThreadLateOptFlat as' tf4))))
  ⟨ef.name, as', rs', tf5⟩

/-- Compile a single `TFlatFn` through `earlyOptFlat → midStageFlat → TFlat.ext →
`Rega.lowerFlatFn`. -/
def compileFlatFn (I : Isa) (lt : LegalTarget) (h : I.Hints) (f : TFlatFn) :
    Except String (List I.Directive) :=
  if !f.wfCheck then .error s!"{f.name}: flat wfCheck failed"
  else
    let mf := midStageFlat lt (earlyOptFlat f)
    Rega.lowerFlatFn I h (TFlat.ext mf.body) mf

/-- First-order mirror of `compileModule` over `List TFlatFn`. -/
def compileModuleFlat (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    List TFlatFn → List I.Hints → Except String (List I.Directive × List (Sym × Nat))
  | [], [] => .ok ([], [])
  | f :: fs, h :: hs =>
    if !f.wfCheck then .error s!"{f.name}: flat wfCheck failed"
    else
      let ef := earlyOptFlat f
      if ef.supportsSource lt then
        let mf := midStageFlat lt ef
        let ext := TFlat.ext mf.body
        match Rega.lowerFlatFn I h ext mf,
              checkAndBoundExt I raBytes exits nX extCallees h ext with
        | .ok c, some b =>
          match compileModuleFlat I lt raBytes (((mf.name, mf.as, mf.rs), b) :: extCallees)
              exits nX fs hs with
          | .ok (cs, bs) => .ok (c ++ cs, (f.name, b) :: bs)
          | .error e => .error e
        | .error e, _ => .error s!"{f.name}: {e}"
        | _, none => .error s!"{f.name}: unknown callee, undeclared exit, or stack overflow"
      else
        .error s!"{f.name}: unsupported source op for target"
  | _, _ => .error "compileModuleFlat: fn/hints length mismatch"

end LeanQbe.T
