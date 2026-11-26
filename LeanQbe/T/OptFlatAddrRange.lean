module

public import LeanQbe.T.FlatDirect
public import LeanQbe.T.OptFlatPlanKit
public import LeanQbe.T.AddrRangeOpt

/-!
# Native `Trie`-Env Loop-Aware Address Reassociation & Range-Check Collapse (`OptFlatAddrRange`)

Direct `TFlat rs → TFlat rs` implementation of `Func.addrRangeOpt` using a de Bruijn level
`Trie ((t : Ty) × ARVal K t)` environment, symbolic key counter `next`, and separate output level
counter `outDepth` (`rangeSubCmp`, `addrShl`, and `addrPlain` emit multiple `.let_` bindings per
unit `next` increment), preserving zero PHOAS closure allocation and fast-path bypass when
`AddrRangeOpt.buildLoopTree false tf` reports `hasWork = false`:

* `OptFlatAddrRange.addrRangeOptFlat`: `TFlat` pass matching `reifyFunc (Func.addrRangeOpt ...)`.
* `OptFlatAddrRange.addrRangeOptFlatFn`: `TFlatFn` wrapper.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace OptFlatAddrRange

open OptFlatPlanKit

/-- Result of lowering one `ARStep K ts`: emitted `TFlat` prefix builder plus updated state
`(next', inDepth', inEnv', outDepth')`. -/
def applyARStep {rs : List Ty} (next : Nat) {ts : List Ty} (step : ARStep K ts)
    (inDepth : Nat) (inEnv : Trie ((t : Ty) × ARVal K t)) (outDepth : Nat) :
    (TFlat rs → TFlat rs) × Nat × Nat × Trie ((t : Ty) × ARVal K t) × Nat :=
  match ts, step with
  | ts, .elim res =>
    (id, next, inDepth + ts.length, insertTupEnv inDepth inEnv res, outDepth)
  | ts, .emit1 op' wrap =>
    let wrapped := wrap (Tup.levels ts outDepth)
    (TFlat.let_ ⟨op'.code, idxArgs outDepth op'.args⟩,
      next + ts.length, inDepth + ts.length, insertTupEnv inDepth inEnv wrapped,
      outDepth + ts.length)
  | _, .rangeSubCmp w o x lo width outD =>
    let mk := fun k =>
      TFlat.let_ (op2 (.sub (.bits w)) (idxArg outDepth x) (.imm lo))
        (.let_ (op2 (.cmp o (.bits w)) (.var 0) (.imm width)) k)
    (mk, next + 1, inDepth + 1,
      insertTupEnv (ts := [.bool]) inDepth inEnv (ARVal.fresh (outDepth + 1) next outD, ()),
      outDepth + 2)
  | _, .addrShl n isSub base inv iv ivD sh _ disp =>
    let op2Code := if isSub then OpCode.sub (.bits n) else .add (.bits n)
    if disp == 0#n then
      let mk := fun k =>
        TFlat.let_ (op2 (.shl (.bits n)) (idxArg outDepth inv) (.imm (BitVec.ofNat n sh)))
          (.let_ (op2 op2Code (idxArg (outDepth + 1) base) (.var 0))
            (.let_ (op2 (.shl (.bits n)) (idxArg (outDepth + 2) iv) (.imm (BitVec.ofNat n sh)))
              (.let_ (op2 (.add (.bits n)) (.var 1) (.var 0)) k)))
      (mk, next + 1, inDepth + 1,
        insertTupEnv (ts := [.bits n]) inDepth inEnv (ARVal.fresh (outDepth + 3) next ivD, ()),
        outDepth + 4)
    else
      let mk := fun k =>
        TFlat.let_ (op2 (.shl (.bits n)) (idxArg outDepth inv) (.imm (BitVec.ofNat n sh)))
          (.let_ (op2 op2Code (idxArg (outDepth + 1) base) (.var 0))
            (.let_ (op2 (.shl (.bits n)) (idxArg (outDepth + 2) iv) (.imm (BitVec.ofNat n sh)))
              (.let_ (op2 (.add (.bits n)) (.var 1) (.var 0))
                (.let_ (op2 (.add (.bits n)) (.var 0) (.imm disp)) k))))
      (mk, next + 1, inDepth + 1,
        insertTupEnv (ts := [.bits n]) inDepth inEnv (ARVal.fresh (outDepth + 4) next ivD, ()),
        outDepth + 5)
  | _, .addrPlain n isSub base inv iv invD ivD disp =>
    let op1Code := if isSub then OpCode.sub (.bits n) else .add (.bits n)
    if disp == 0#n then
      let v : ARVal K (.bits n) :=
        ⟨.var (outDepth + 1), .var next, ivD,
          { addr? := some (.addVV (.var outDepth) invD iv ivD 0#n) }⟩
      let mk := fun k =>
        TFlat.let_ (op2 op1Code (idxArg outDepth base) (idxArg outDepth inv))
          (.let_ (op2 (.add (.bits n)) (.var 0) (idxArg (outDepth + 1) iv)) k)
      (mk, next + 1, inDepth + 1,
        insertTupEnv (ts := [.bits n]) inDepth inEnv (v, ()), outDepth + 2)
    else
      let v : ARVal K (.bits n) :=
        ⟨.var (outDepth + 2), .var next, ivD,
          { addr? := some (.addVV (.var outDepth) invD iv ivD disp) }⟩
      let mk := fun k =>
        TFlat.let_ (op2 op1Code (idxArg outDepth base) (idxArg outDepth inv))
          (.let_ (op2 (.add (.bits n)) (.var 0) (idxArg (outDepth + 1) iv))
            (.let_ (op2 (.add (.bits n)) (.var 0) (.imm disp)) k))
      (mk, next + 1, inDepth + 1,
        insertTupEnv (ts := [.bits n]) inDepth inEnv (v, ()), outDepth + 3)

mutual
/-- Native `TFlat` linear sweep matching `addrRangeSweep`. -/
def addrRangeSweepFlat {rs : List Ty} (curD next : Nat) (plan : LoopTree) :
    TFlat rs → Nat → Trie ((t : Ty) × ARVal K t) → Nat → TFlat rs
  | .let_ (ts := ts) op k, inDepth, inEnv, outDepth =>
    let arOp : Op (ARVal K) ts := ⟨op.code, resolveEnvArgs inDepth inEnv op.args⟩
    let (mk, next', inDepth', inEnv', outDepth') :=
      applyARStep next (arOp.arStep curD next) inDepth inEnv outDepth
    mk (addrRangeSweepFlat curD next' plan.step1 k inDepth' inEnv' outDepth')
  | .load t a k, inDepth, inEnv, outDepth =>
    let a' := (resolveEnvArg inDepth inEnv a).arOut
    let inEnv' := inEnv.insert inDepth ⟨t, ARVal.fresh outDepth next curD⟩
    .load t (idxArg outDepth a')
      (addrRangeSweepFlat curD (next + 1) plan.step1 k (inDepth + 1) inEnv' (outDepth + 1))
  | .store v a k, inDepth, inEnv, outDepth =>
    let v' := (resolveEnvArg inDepth inEnv v).arOut
    let a' := (resolveEnvArg inDepth inEnv a).arOut
    .store (idxArg outDepth v') (idxArg outDepth a')
      (addrRangeSweepFlat curD next plan.step1 k inDepth inEnv outDepth)
  | .call f bs args k, inDepth, inEnv, outDepth =>
    let args' := tupArOut (resolveEnvArgs inDepth inEnv args)
    let wrapped := freshARVals curD bs (Tup.levels bs outDepth) next
    .call f bs (idxArgs outDepth args')
      (addrRangeSweepFlat curD (next + bs.length) plan.step1 k
        (inDepth + bs.length) (insertTupEnv inDepth inEnv wrapped) (outDepth + bs.length))
  | .jnz c t e, inDepth, inEnv, outDepth =>
    let (pt, pe) := plan.step2
    match (resolveEnvArg inDepth inEnv c).arOut with
    | .imm true => addrRangeSweepFlat curD next pt t inDepth inEnv outDepth
    | .imm false => addrRangeSweepFlat curD next pe e inDepth inEnv outDepth
    | .var v =>
      .jnz (idxArg outDepth (.var v))
        (addrRangeSweepFlat curD next pt t inDepth inEnv outDepth)
        (addrRangeSweepFlat curD next pe e inDepth inEnv outDepth)
  | .jump j args, inDepth, inEnv, outDepth =>
    .jump j (idxArgs outDepth (tupArOut (resolveEnvArgs inDepth inEnv args)))
  | .ret vs, inDepth, inEnv, outDepth =>
    .ret (idxArgs outDepth (tupArOut (resolveEnvArgs inDepth inEnv vs)))
  | .exit f args, inDepth, inEnv, outDepth =>
    .exit f (idxArgs outDepth (tupArOut (resolveEnvArgs inDepth inEnv args)))
  | .hlt, _, _, _ => .hlt
  | .group bodies k, inDepth, inEnv, outDepth =>
    let (bsPlan, kPlan) := plan.stepGroup
    .group
      (addrRangeSweepBFlat curD next bsPlan bodies inDepth inEnv outDepth)
      (addrRangeSweepFlat curD next kPlan k inDepth inEnv outDepth)

/-- Block-list companion of `addrRangeSweepFlat`. -/
def addrRangeSweepBFlat {rs : List Ty} (curD next : Nat) (bsPlan : LoopBlocks) :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Trie ((t : Ty) × ARVal K t) → Nat →
    TBlocks rs sig
  | _, .nil, _, _, _ => .nil
  | _, .cons (ts := ts) b bs, inDepth, inEnv, outDepth =>
    let (isL, ph, pt) := bsPlan.stepCons
    let bd := if isL then curD + 1 else curD
    let wrapped := freshARVals bd ts (Tup.levels ts outDepth) next
    .cons
      (addrRangeSweepFlat bd (next + ts.length) ph b
        (inDepth + ts.length) (insertTupEnv inDepth inEnv wrapped) (outDepth + ts.length))
      (addrRangeSweepBFlat curD next pt bs inDepth inEnv outDepth)
end

/-- Direct `TFlat` loop-aware address reassociation and range-check collapse matching
`reifyFunc (Func.addrRangeOpt (denoteFunc tf))`. -/
def addrRangeOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  let (plan, hasWork) := AddrRangeOpt.buildLoopTree false tf
  if hasWork then
    addrRangeSweepFlat 0 as.length plan tf as.length
      (initEnv (fun x next => ARVal.fresh x next 0) as) as.length
  else tf

/-- `TFlatFn` wrapper for `addrRangeOptFlat`. -/
def addrRangeOptFlatFn (f : TFlatFn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, addrRangeOptFlat f.as f.body⟩

end OptFlatAddrRange
end LeanQbe.T
