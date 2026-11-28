module

public import BvDecideQbe.Prover
public import BvDecideQbe.NormalizeTheorems
public import BvDecideQbe.Normalize.AC
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar
public import Lean.Meta.Tactic.BVDecide.Normalize
public import Lean.Meta.Tactic.BVDecide.TacticContext
public import Lean.Meta.Sym.LitValues
import Lean.Meta.Sym.InferType

/-!
# Single-Solve Phase-1 CEGAR Wrapper for `bv_decide_qbe` (`BB-07`)

Reuses upstream `Cegar.checkUf` + `Cegar.processNewHyps` solely for untrusted congruence-lemma
discovery (every UF congruence lemma is kernel-checked and conjoined into `satExpr`), and checks
every BitVec abstraction directly via `probeBVExpr` (`bv_solve_bytes` in-process):
- Intermediate SAT rounds emit zero axioms (`witness.addAxiom` is never called) and feed the
  `evalEfficient`-validated counterexample directly into `Cegar.checkUf`.
- On final UNSAT, `commitUnsatWitness` emits a single `_leanqbe.bv_solve.ax` axiom and closes the
  goal immediately with zero CaDiCaL invocations and zero double-solve.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Lean.Meta.Tactic.BVDecide
open Std.Tactic.BVDecide

/-- Result returned by `BvDecideQbe.cegarBlaster` (`lemmas` from CEGAR + optional `ProveResult`). -/
structure CegarResult where
  lemmas : Array CegarHyp := #[]
  proveResult? : Option ProveResult := none
  deriving Inhabited

/-! ## Lightweight Batched UF Congruence & McCarthy Array Refinement (`Gap #15`) -/

private def mkPairKey (a b : Expr) : Sym.ExprPtr × Sym.ExprPtr :=
  if Expr.lt a b then (⟨a⟩, ⟨b⟩) else (⟨b⟩, ⟨a⟩)

private def pushKernelCegarHyp (name : Name) (prf : Expr) : CegarM Unit := do
  let prf ← Sym.share prf
  let stmt ← Sym.inferType prf
  CegarM.pushNewHyp {
    hyp := {
      name := name
      type := stmt
      value := prf
      source := .cegar
    }
    tacticProof := do
      `(tacticSeq| simp +$(mkIdent `contextual):ident only [$(mkIdent ``implies_true):ident])
    grindProof := pure none
  }

private def addCongrLemmaLocal (lhs rhs : Expr) (mask : Array Bool) (pattern : Expr) :
    CegarM Unit := do
  let lhsArgs := lhs.getAppArgs
  let rhsArgs := rhs.getAppArgs
  let mut congrLemma ← getCongrLemma pattern
  for lhsArg in lhsArgs, rhsArg in rhsArgs, m in mask do
    unless m do continue
    congrLemma := mkApp2 congrLemma lhsArg rhsArg
  pushKernelCegarHyp `congr congrLemma
where
  getCongrLemma (pattern : Expr) : CegarM Expr := do
    let key : Sym.ExprPtr := { expr := pattern }
    if let some lem := (← CegarM.getTheoryState).funState.congrCache[key]? then
      return lem
    let lem ← mkCongrLemma pattern
    CegarM.modifyTheoryState fun ts =>
      { ts with funState.congrCache := ts.funState.congrCache.insert key lem }
    return lem

  mkCongrLemma (pattern : Expr) : CegarM Expr :=
    lambdaTelescope pattern fun lhsArgs _ =>
    lambdaTelescope pattern fun rhsArgs _ => do
      let mut eqDecls := #[]
      for lhsArg in lhsArgs, rhsArg in rhsArgs do
        eqDecls := eqDecls.push (.anonymous, ← mkEq lhsArg rhsArg)
      withLocalDeclsDND eqDecls fun eqs => do
        let mut lem ← mkAppM ``congrArg #[pattern, eqs[0]!]
        for eq in eqs[1...*] do
          lem ← mkAppM ``congr #[lem, eq]
        let mut fvars := #[]
        for lhsArg in lhsArgs, rhsArg in rhsArgs do
          fvars := fvars.push lhsArg |>.push rhsArg
        fvars := fvars ++ eqs
        mkLambdaFVars fvars lem

private inductive ReifiedArg where
  | bv {w : Nat} (e : BVExpr w)
  | bool (e : BVLogicalExpr)

private structure PreparedUfAtom where
  funExpr : Expr
  atomKey : Expr
  atomNum : Nat
  mask : Array Bool
  pattern : Expr
  args : Array ReifiedArg
  deriving Inhabited

private def prepareUfAtoms : CegarM (Array PreparedUfAtom) := do
  let funState := (← getThe Lean.Meta.Tactic.BVDecide.State).theoryState.funState
  let mut out : Array PreparedUfAtom := Array.emptyWithCapacity funState.atoms.size
  for funAtom in funState.atoms, mask in funState.masks, funPattern in funState.patterns do
    let atomKey ← funAtom.atomExpr
    let some atomNum ← ReifyM.getAtomNumber atomKey | continue
    let rawArgs := funAtom.funExpr.getAppArgs
    let mut rargs : Array ReifiedArg := #[]
    for h : idx in 0...rawArgs.size do
      if !mask[idx]! then continue
      let arg := rawArgs[idx]
      if (← isValidBitVecAtom arg).isSome then
        let some reified ← ReifiedBVExpr.of arg | unreachable!
        rargs := rargs.push (.bv reified.bvExpr)
      else if ← isValidBoolAtom arg then
        let some reified ← ReifiedBVLogical.of arg | unreachable!
        rargs := rargs.push (.bool reified.bvExpr)
      else
        unreachable!
    out := out.push {
      funExpr := funAtom.funExpr
      atomKey := atomKey
      atomNum := atomNum
      mask := mask
      pattern := funPattern
      args := rargs
    }
  return out

open Std.Tactic.BVDecide.EfficientEval in
private def evalPreparedArgs (atomCex : Std.HashMap Nat BVExpr.PackedBitVec)
    (args : Array ReifiedArg) : Array BVExpr.PackedBitVec :=
  args.map fun
    | .bv e => ⟨BVExpr.evalEfficient (atomCex.getD · ⟨0#1⟩) e⟩
    | .bool e => ⟨BitVec.ofBool (BVLogicalExpr.evalEfficient (atomCex.getD · ⟨0#1⟩) e)⟩

private def checkUfBatched (cex : CegarM.CounterExample)
    (seenCongr : IO.Ref (Std.HashSet (Sym.ExprPtr × Sym.ExprPtr)))
    (cascade : Bool) : CegarM Bool :=
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Batched UF conflict detection") do
    unless (← CegarM.getTacticContext).config.uf do return false
    let funState := (← getThe Lean.Meta.Tactic.BVDecide.State).theoryState.funState
    if funState.atoms.size ≤ 1 then return false
    let atoms ← prepareUfAtoms
    let mut atomByExpr : Std.HashMap Sym.ExprPtr Nat := {}
    let mut argValsArr : Array (Array BVExpr.PackedBitVec) := Array.emptyWithCapacity atoms.size
    let mut valsArr : Array (Option BVExpr.PackedBitVec) := Array.emptyWithCapacity atoms.size
    let mut buckets :
        Std.HashMap (Sym.ExprPtr × Array BVExpr.PackedBitVec)
          (Array (Nat × BVExpr.PackedBitVec)) := {}
    let mut funModel : Cegar.FunModel := {}
    for h : idx in 0...atoms.size do
      let a := atoms[idx]
      atomByExpr := atomByExpr.insert ⟨a.funExpr⟩ idx
      let argVals := evalPreparedArgs cex.atomCex a.args
      argValsArr := argValsArr.push argVals
      let val? := cex.exprCex[a.atomKey]?
      valsArr := valsArr.push val?
      if let some val := val? then
        funModel := {
          model := funModel.model.alter ⟨a.pattern⟩ fun
            | some entry => some { map := entry.map.insert argVals (val, a.funExpr) }
            | none => some { map := {(argVals, (val, a.funExpr))} }
        }
        let bkey : Sym.ExprPtr × Array BVExpr.PackedBitVec := (⟨a.pattern⟩, argVals)
        buckets := buckets.alter bkey fun
          | some arr => some (arr.push (idx, val))
          | none => some #[(idx, val)]
    CegarM.modifyTheoryState fun s => { s with funState.currentModel := funModel }
    let mut addedAny := false
    let mut emitted := 0
    let maxLemmasPerRound := 64
    let mut cascadeQueue : Array (Nat × Nat) := #[]
    let emitPair (iIdx jIdx : Nat) (emitted : Nat) : CegarM (Bool × Nat) := do
      if emitted ≥ maxLemmasPerRound then return (false, emitted)
      let ai := atoms[iIdx]!
      let aj := atoms[jIdx]!
      if ai.funExpr == aj.funExpr || ai.pattern != aj.pattern then
        return (false, emitted)
      let pkey := mkPairKey ai.funExpr aj.funExpr
      if (← seenCongr.get).contains pkey then
        return (false, emitted)
      seenCongr.modify (·.insert pkey)
      addCongrLemmaLocal ai.funExpr aj.funExpr ai.mask ai.pattern
      return (true, emitted + 1)
    -- 1. Emit ALL violated congruence pairs in every (pattern, args) bucket
    for (_, items) in buckets do
      if items.size < 2 then continue
      for i in [0:items.size] do
        if emitted ≥ maxLemmasPerRound then break
        let (iIdx, vi) := items[i]!
        for j in [i + 1:items.size] do
          if emitted ≥ maxLemmasPerRound then break
          let (jIdx, vj) := items[j]!
          if vi != vj then
            let (didEmit, emitted') ← emitPair iIdx jIdx emitted
            emitted := emitted'
            if didEmit then
              addedAny := true
              if cascade then
                cascadeQueue := cascadeQueue.push (iIdx, jIdx)
    -- 2. Top-down argument cascade: recursively instantiate sub-call congruences whose args
    --    already agree in `cex` and will be forced apart in the next CEGAR round
    if cascade then
      let mut qHead := 0
      while qHead < cascadeQueue.size && emitted < maxLemmasPerRound do
        let (pIdx, qIdx) := cascadeQueue[qHead]!
        qHead := qHead + 1
        let ap := atoms[pIdx]!
        let aq := atoms[qIdx]!
        let pArgs := ap.funExpr.getAppArgs
        let qArgs := aq.funExpr.getAppArgs
        for argP in pArgs, argQ in qArgs, m in ap.mask do
          if !m || argP == argQ || emitted ≥ maxLemmasPerRound then continue
          match atomByExpr.get? ⟨argP⟩, atomByExpr.get? ⟨argQ⟩ with
          | some i1, some i2 =>
            if atoms[i1]!.pattern == atoms[i2]!.pattern && argValsArr[i1]! == argValsArr[i2]! then
              let (didEmit, emitted') ← emitPair i1 i2 emitted
              emitted := emitted'
              if didEmit then
                addedAny := true
                cascadeQueue := cascadeQueue.push (i1, i2)
          | some i1, none =>
            if let some v1 := valsArr[i1]! then
              let bkey : Sym.ExprPtr × Array BVExpr.PackedBitVec :=
                (⟨atoms[i1]!.pattern⟩, argValsArr[i1]!)
              if let some sibs := buckets.get? bkey then
                for (sIdx, sVal) in sibs do
                  if sIdx != i1 && sVal == v1 then
                    let (didEmit, emitted') ← emitPair i1 sIdx emitted
                    emitted := emitted'
                    if didEmit then
                      addedAny := true
                      cascadeQueue := cascadeQueue.push (i1, sIdx)
          | none, some i2 =>
            if let some v2 := valsArr[i2]! then
              let bkey : Sym.ExprPtr × Array BVExpr.PackedBitVec :=
                (⟨atoms[i2]!.pattern⟩, argValsArr[i2]!)
              if let some sibs := buckets.get? bkey then
                for (sIdx, sVal) in sibs do
                  if sIdx != i2 && sVal == v2 then
                    let (didEmit, emitted') ← emitPair i2 sIdx emitted
                    emitted := emitted'
                    if didEmit then
                      addedAny := true
                      cascadeQueue := cascadeQueue.push (i2, sIdx)
          | none, none => pure ()
    return addedAny

private def unwrapBoolAtomExpr (e : Expr) : Expr :=
  match_expr e with
  | BitVec.ofBool inner => inner
  | _ => e

private def evalKnownBvExpr? (exprCex : Std.HashMap Expr BVExpr.PackedBitVec) (e : Expr) :
    Option BVExpr.PackedBitVec :=
  if let some v := exprCex[e]? then
    some v
  else
    (Sym.getBitVecValue? e).run.map fun ⟨_, bv⟩ => ⟨bv⟩

private def matchBvToNat? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | BitVec.toNat w x => some (w, x)
  | _ => none

private structure RowStep where
  lemmaPrf : Expr
  iBv : Expr
  vExpr : Expr
  nextRead : Expr

private def mkLtOfSizeEq (idxExpr sizeEq hj : Expr) : MetaM Expr := do
  let ltFn ← mkAppM ``LT.lt #[idxExpr]
  let propEq ← mkCongrArg ltFn sizeEq
  mkEqMP propEq hj

/-- Build a kernel proof of `curRead = cond (iBv == jBv) vExpr nextRead` from
`rowEq : lhs = if iBv.toNat = jBv.toNat then vExpr else r0` using only `Init` constants. -/
private def mkToNatIteEqCond (elemTy wExpr iBv jBv vExpr nextRead curRead rowEq : Expr) :
    MetaM Expr := do
  let bvTy := mkApp (mkConst ``BitVec) wExpr
  let iNat ← mkAppM ``BitVec.toNat #[iBv]
  let jNat ← mkAppM ``BitVec.toNat #[jBv]
  let bProp ← mkEq iNat jNat
  let decB ← synthInstance (mkApp (mkConst ``Decidable) bProp)
  let hToNat ← mkAppOptM ``BitVec.toNat_eq #[some wExpr, some iBv, some jBv]
  let h1 ← mkAppM ``Iff.symm #[hToNat]
  let hBeq ← mkAppOptM ``beq_iff_eq #[some bvTy, none, none, some iBv, some jBv]
  let h2 ← mkAppM ``Iff.symm #[hBeq]
  let hPropEq ← mkAppM ``propext #[← mkAppM ``Iff.trans #[h1, h2]]
  let beqExpr ← mkAppM ``BEq.beq #[iBv, jBv]
  let beqTrue ← mkEq beqExpr (mkConst ``Bool.true)
  let hcLam ← withLocalDeclD `hc beqTrue fun hc => do
    mkLambdaFVars #[hc] (← mkEqRefl vExpr)
  let hncLam ← withLocalDeclD `hnc (mkApp (mkConst ``Not) beqTrue) fun hnc => do
    mkLambdaFVars #[hnc] (← mkEqRefl nextRead)
  let hIte ← mkAppOptM ``ite_congr
    #[some elemTy, some bProp, some beqTrue, some vExpr, some nextRead, some vExpr, some nextRead,
      some decB, none, some hPropEq, some hcLam, some hncLam]
  let hCond ← mkEqSymm (← mkAppM ``cond_eq_ite #[beqExpr, vExpr, nextRead])
  let inner ← mkEqTrans rowEq (← mkEqTrans hIte hCond)
  let condExpr ← mkAppM ``cond #[beqExpr, vExpr, nextRead]
  let u ← getLevel elemTy
  let reflCur := mkApp2 (mkConst ``Eq.refl [u]) elemTy curRead
  return mkApp6 (mkConst ``Eq.trans [u]) elemTy curRead curRead condExpr reflCur inner

/-- Build a kernel proof of `iBv = jBv → read1 = read2` for `GetElem` reads indexed by
`BitVec.toNat`, using only `Init` constants (`Eq.ndrec`, `Eq.refl`). -/
private def mkGetElemToNatCongr (getElemFn collTy idxTy elemTy valid inst wExpr arrExpr
    iBv jBv hj read1 : Expr) : MetaM Expr := do
  let bvTy := mkApp (mkConst ``BitVec) wExpr
  let iNat ← mkAppM ``BitVec.toNat #[iBv]
  withLocalDeclD `heq (← mkEq iBv jBv) fun heq => do
    let motive ← withLocalDeclD `k bvTy fun k => do
      let kNat ← mkAppM ``BitVec.toNat #[k]
      let body ← withLocalDeclD `hk (mkApp2 valid arrExpr kNat) fun hk => do
        let readK := mkApp8 getElemFn collTy idxTy elemTy valid inst arrExpr kNat hk
        mkForallFVars #[hk] (← mkEq read1 readK)
      mkLambdaFVars #[k] body
    let base ← withLocalDeclD `hk (mkApp2 valid arrExpr iNat) fun hk => do
      mkLambdaFVars #[hk] (← mkEqRefl read1)
    let step ← mkAppOptM ``Eq.ndrec
      #[some bvTy, some iBv, some motive, some base, some jBv, some heq]
    mkLambdaFVars #[heq] (mkApp step hj)

private def mkGetElemRowStep?
    (existingReads : Std.HashMap (Sym.ExprPtr × Sym.ExprPtr) Expr)
    (curRead getElemFn collTy idxTy elemTy valid inst arrExpr idxExpr jBv wExpr hj : Expr) :
    Sym.SymM (Option RowStep) := do
  let mkNext (xs hj0 : Expr) : Sym.SymM Expr :=
    Sym.share (mkApp8 getElemFn collTy idxTy elemTy valid inst xs idxExpr hj0)
  match_expr arrExpr with
  | Array.set α xs iNat v hi =>
    let some (wi, iBv) := matchBvToNat? iNat | return none
    if wi != wExpr then return none
    let hj0 ← match existingReads.get? (⟨xs⟩, ⟨jBv⟩) with
      | some p => pure p
      | none =>
        let sizeEq ← mkAppOptM ``Array.size_set #[some α, some xs, some iNat, some v, some hi]
        Sym.share (← mkLtOfSizeEq idxExpr sizeEq hj)
    let nextRead ← mkNext xs hj0
    let rowEq ← mkAppOptM ``Array.getElem_set
      #[some α, some xs, some iNat, some hi, some v, some idxExpr, some hj]
    let prf ← mkToNatIteEqCond elemTy wExpr iBv jBv v nextRead curRead rowEq
    return some { lemmaPrf := prf, iBv, vExpr := v, nextRead }
  | Array.setIfInBounds α xs iNat v =>
    let some (wi, iBv) := matchBvToNat? iNat | return none
    if wi != wExpr then return none
    let hj0 ← match existingReads.get? (⟨xs⟩, ⟨jBv⟩) with
      | some p => pure p
      | none =>
        let sizeEq ← mkAppOptM ``Array.size_setIfInBounds #[some α, some xs, some iNat, some v]
        Sym.share (← mkLtOfSizeEq idxExpr sizeEq hj)
    let nextRead ← mkNext xs hj0
    let rowEq ← mkAppOptM ``Array.getElem_setIfInBounds
      #[some α, some xs, some iNat, some v, some idxExpr, some hj0]
    let prf ← mkToNatIteEqCond elemTy wExpr iBv jBv v nextRead curRead rowEq
    return some { lemmaPrf := prf, iBv, vExpr := v, nextRead }
  | Array.set! α xs iNat v =>
    let some (wi, iBv) := matchBvToNat? iNat | return none
    if wi != wExpr then return none
    let hj0 ← match existingReads.get? (⟨xs⟩, ⟨jBv⟩) with
      | some p => pure p
      | none =>
        let sizeEq ← mkAppOptM ``Array.size_set! #[some α, some xs, some iNat, some v]
        Sym.share (← mkLtOfSizeEq idxExpr sizeEq hj)
    let nextRead ← mkNext xs hj0
    let rowEq ← mkAppOptM ``Array.getElem_setIfInBounds
      #[some α, some xs, some iNat, some v, some idxExpr, some hj0]
    let prf ← mkToNatIteEqCond elemTy wExpr iBv jBv v nextRead curRead rowEq
    return some { lemmaPrf := prf, iBv, vExpr := v, nextRead }
  | Vector.set α n xs iNat v hi =>
    let some (wi, iBv) := matchBvToNat? iNat | return none
    if wi != wExpr then return none
    let hj0 := (existingReads.get? (⟨xs⟩, ⟨jBv⟩)).getD hj
    let nextRead ← mkNext xs hj0
    let rowEq ← mkAppOptM ``Vector.getElem_set
      #[some α, some n, some xs, some iNat, some v, some hi, some idxExpr, some hj0]
    let prf ← mkToNatIteEqCond elemTy wExpr iBv jBv v nextRead curRead rowEq
    return some { lemmaPrf := prf, iBv, vExpr := v, nextRead }
  | Vector.setIfInBounds α n xs iNat v =>
    let some (wi, iBv) := matchBvToNat? iNat | return none
    if wi != wExpr then return none
    let hj0 := (existingReads.get? (⟨xs⟩, ⟨jBv⟩)).getD hj
    let nextRead ← mkNext xs hj0
    let rowEq ← mkAppOptM ``Vector.getElem_setIfInBounds
      #[some α, some n, some idxExpr, some iNat, some xs, some v, some hj0]
    let prf ← mkToNatIteEqCond elemTy wExpr iBv jBv v nextRead curRead rowEq
    return some { lemmaPrf := prf, iBv, vExpr := v, nextRead }
  | Vector.set! α n xs iNat v =>
    let some (wi, iBv) := matchBvToNat? iNat | return none
    if wi != wExpr then return none
    let hj0 := (existingReads.get? (⟨xs⟩, ⟨jBv⟩)).getD hj
    let nextRead ← mkNext xs hj0
    let rowEq ← mkAppOptM ``Vector.getElem_set!
      #[some α, some n, some idxExpr, some iNat, some xs, some v, some hj0]
    let prf ← mkToNatIteEqCond elemTy wExpr iBv jBv v nextRead curRead rowEq
    return some { lemmaPrf := prf, iBv, vExpr := v, nextRead }
  | List.set α xs iNat v =>
    let some (wi, iBv) := matchBvToNat? iNat | return none
    if wi != wExpr then return none
    let hj0 ← match existingReads.get? (⟨xs⟩, ⟨jBv⟩) with
      | some p => pure p
      | none =>
        let sizeEq ← mkAppOptM ``List.length_set #[some α, some xs, some iNat, some v]
        Sym.share (← mkLtOfSizeEq idxExpr sizeEq hj)
    let nextRead ← mkNext xs hj0
    let rowEq ← mkAppOptM ``List.getElem_set
      #[some α, some xs, some iNat, some idxExpr, some v, some hj]
    let prf ← mkToNatIteEqCond elemTy wExpr iBv jBv v nextRead curRead rowEq
    return some { lemmaPrf := prf, iBv, vExpr := v, nextRead }
  | _ => return none

private def mkHashMapRowStep? (e : Expr) : Sym.SymM (Option (Expr × RowStep)) := do
  if !(← getEnv).contains ``Std.HashMap.getD_insert then return none
  match_expr e with
  | Std.HashMap.getD keyTy valTy beqInst hashInst mExpr jBv dExpr =>
    let_expr BitVec wExpr := keyTy | return none
    match_expr mExpr with
    | Std.HashMap.insert keyTy' valTy' beqInst' hashInst' baseMap iBv vExpr =>
      if keyTy' != keyTy || valTy' != valTy || beqInst' != beqInst || hashInst' != hashInst then
        return none
      let hashOk := match_expr hashInst with
        | BitVec.instHashable w' => w' == wExpr
        | _ => false
      if !hashOk then return none
      let beqOk ← withTransparency .default do
        let some canonBeq ← synthInstance? (mkApp (mkConst ``BEq [0]) keyTy) | return false
        isDefEq canonBeq beqInst
      if !beqOk then return none
      let nextRead ← Sym.share (mkApp7 e.getAppFn keyTy valTy beqInst hashInst baseMap jBv dExpr)
      let rowEq ← mkAppOptM ``Std.HashMap.getD_insert
        #[some keyTy, some valTy, some beqInst, some hashInst, some baseMap,
          none, none, some iBv, some jBv, some dExpr, some vExpr]
      let beqExpr ← mkAppOptM ``BEq.beq #[some keyTy, some beqInst, some iBv, some jBv]
      let hCond ← mkEqSymm (← mkAppM ``cond_eq_ite #[beqExpr, vExpr, nextRead])
      let prf ← mkEqTrans (← mkEqRefl e) (← mkEqTrans rowEq hCond)
      return some (jBv, { lemmaPrf := prf, iBv, vExpr, nextRead })
    | _ => return none
  | _ => return none

private def isArrayReadHead (e : Expr) : Bool :=
  match (unwrapBoolAtomExpr e).getAppFn.constName? with
  | some ``GetElem.getElem | some ``Std.HashMap.getD => true
  | _ => false

private def checkArrayRow (cex : CegarM.CounterExample)
    (seenRow : IO.Ref (Std.HashSet Sym.ExprPtr))
    (seenCongr : IO.Ref (Std.HashSet (Sym.ExprPtr × Sym.ExprPtr))) : CegarM Bool :=
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"McCarthy array ROW refinement") do
    let atomsMap := (← getThe Lean.Meta.Tactic.BVDecide.State).atoms
    let mut candAtoms : Array Expr := #[]
    for (ptr, atom) in atomsMap do
      if !atom.synthetic && isArrayReadHead ptr.expr then
        candAtoms := candAtoms.push ptr.expr
    if candAtoms.isEmpty then return false
    -- Index existing `GetElem.getElem` reads so McCarthy ROW reuses proof terms & atom ExprPtrs
    let mut existingReads : Std.HashMap (Sym.ExprPtr × Sym.ExprPtr) Expr := {}
    let mut readGroups :
        Std.HashMap (Sym.ExprPtr × Sym.ExprPtr × Sym.ExprPtr × BVExpr.PackedBitVec)
          (Array (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr ×
            BVExpr.PackedBitVec)) := {}
    for rawAtom in candAtoms do
      let e := unwrapBoolAtomExpr rawAtom
      match_expr e with
      | GetElem.getElem collTy idxTy elemTy valid inst arrExpr idxExpr proofExpr =>
        if idxTy.isConstOf ``Nat then
          if let some (wExpr, jBv) := matchBvToNat? idxExpr then
            existingReads := existingReads.insert (⟨arrExpr⟩, ⟨jBv⟩) proofExpr
            if let (some jVal, some rVal) :=
                (evalKnownBvExpr? cex.exprCex jBv, cex.exprCex[rawAtom]?) then
              let gkey : Sym.ExprPtr × Sym.ExprPtr × Sym.ExprPtr × BVExpr.PackedBitVec :=
                (⟨collTy⟩, ⟨arrExpr⟩, ⟨wExpr⟩, jVal)
              let recItem :=
                (rawAtom, e, e.getAppFn, idxTy, elemTy, valid, inst, jBv, proofExpr, rVal)
              readGroups := readGroups.alter gkey fun
                | some arr => some (arr.push recItem)
                | none => some #[recItem]
      | _ => pure ()
    let mut added := false
    -- 1. Targeted McCarthy read-over-write lemmas (chaining along `else` branch in one round)
    for rawAtom in candAtoms do
      let mut curExpr := unwrapBoolAtomExpr rawAtom
      for _ in [0:8] do
        if (← seenRow.get).contains ⟨curExpr⟩ then break
        let stepOpt ← match_expr curExpr with
          | GetElem.getElem collTy idxTy elemTy valid inst arrExpr idxExpr proofExpr =>
            if idxTy.isConstOf ``Nat then
              match matchBvToNat? idxExpr with
              | some (wExpr, jBv) =>
                match ← mkGetElemRowStep? existingReads curExpr curExpr.getAppFn collTy idxTy
                    elemTy valid inst arrExpr idxExpr jBv wExpr proofExpr with
                | some st => pure (some (jBv, st))
                | none => pure none
              | none => pure none
            else pure none
          | _ => mkHashMapRowStep? curExpr
        let some (jBv, st) := stepOpt | break
        let vi? := evalKnownBvExpr? cex.exprCex st.iBv
        let vj? := evalKnownBvExpr? cex.exprCex jBv
        let sameIdx := match vi?, vj? with
          | some vi, some vj => vi == vj
          | _, _ => false
        seenRow.modify (·.insert ⟨curExpr⟩)
        pushKernelCegarHyp `array_row st.lemmaPrf
        added := true
        if sameIdx then
          break
        curExpr := st.nextRead
    -- 2. `BitVec.toNat` read congruence (`i = j → arr[i.toNat] = arr[j.toNat]`)
    for ((collPtr, arrPtr, wPtr, _), items) in readGroups do
      if items.size < 2 then continue
      for i in [0:items.size] do
        let (raw1, read1, getElemFn, idxTy, elemTy, valid, inst, iBv, _, v1) := items[i]!
        for j in [i + 1:items.size] do
          let (raw2, _, _, _, _, _, _, jBv, hj, v2) := items[j]!
          if v1 != v2 && raw1 != raw2 then
            let pkey := mkPairKey raw1 raw2
            if !(← seenCongr.get).contains pkey then
              seenCongr.modify (·.insert pkey)
              let prf ← mkGetElemToNatCongr getElemFn collPtr.expr idxTy elemTy valid inst
                wPtr.expr arrPtr.expr iBv jBv hj read1
              pushKernelCegarHyp `array_congr prf
              added := true
    return added

private def checkBitVecQbe (qbeCtx : QbeContext) :
    CegarM (Except (Array (Expr × Bool × BVExpr.PackedBitVec)) ProveResult) := do
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Checking BitVec abstraction") do
    let bvExpr := (← get).satExpr.bvExpr
    match ← probeBVExpr bvExpr qbeCtx with
    | .ok (witness, workUsed, attempts) =>
      CegarM.clearCaches
      let reflRes ← CegarM.getReflectionResult
      let proveRes ← commitUnsatWitness (← read).goal reflRes witness workUsed attempts
        qbeCtx.axiomDeclRange?
      return .ok proveRes
    | .error eqs =>
      return .error eqs

/-- Trust-pure single-solve Phase-1 CEGAR wrapper: uses `unsatProver` directly unless
`ctx.config.needsIncremental` is enabled, in which case incremental CEGAR discovers kernel-proved
congruence and (in `.enhanced` mode) batched/cascading UF + McCarthy array read-over-write lemmas
via zero-axiom `bv_solve_bytes` probes and commits once on UNSAT. -/
def cegarBlaster (ctx : TacticContext) (qbeCtx : QbeContext := {}) : UnsatProver CegarResult :=
  if ctx.config.needsIncremental then
    cegarLoop
  else
    (unsatProver qbeCtx).map fun proveRes => { lemmas := #[], proveResult? := some proveRes }
where
  checkTermination : CegarM Unit := do
    checkSystem "bv_decide_qbe"
    if (← CegarM.getRounds) == 0 then
      throwError
        m!"bv_decide_qbe reached its round limit, consider increasing it via the \
        `cegarRounds` config option"
    CegarM.consumeRound

  cegarLoop : UnsatProver CegarResult := CegarM.run ctx do
    let useEnh := qbeCtx.features.mode == .enhanced
    let seenCongr ← IO.mkRef ({} : Std.HashSet (Sym.ExprPtr × Sym.ExprPtr))
    let seenRow ← IO.mkRef ({} : Std.HashSet Sym.ExprPtr)
    let mut lastCex := #[]
    CegarM.setDidChange true
    while ← CegarM.getDidChange do
      checkTermination
      match ← checkBitVecQbe qbeCtx with
      | .ok proveRes =>
        return .ok { lemmas := ← CegarM.getUsedHyps, proveResult? := some proveRes }
      | .error cex =>
        lastCex := cex
        let cex ← CegarM.CounterExample.ofArray cex
        if useEnh then
          discard <| checkUfBatched cex seenCongr true
          discard <| checkArrayRow cex seenRow seenCongr
        else
          discard <| Cegar.checkUf cex

      match ← Cegar.processNewHyps with
      | .solved =>
        return .ok { lemmas := ← CegarM.getUsedHyps, proveResult? := none }
      | .newHyps => CegarM.setDidChange true
      | .none => CegarM.setDidChange false

    let equations := lastCex.filterMap fun (lhs, synth, rhs) =>
      if synth then none else some (lhs, rhs)
    let funState := (← getThe Lean.Meta.Tactic.BVDecide.State).theoryState.funState
    return .error {
      goal := (← read).goal
      unusedHypotheses := (← read).unusedHypotheses
      equations := equations
      functionAtoms := funState.atoms.map (·.funExpr)
    }

/-- Reflect and solve a preprocessed `BitVec` goal `g` with hypotheses `hypotheses`. -/
def bvUnsatQbe (g : MVarId) (hypotheses : Array Normalize.Hyp) (ctx : TacticContext)
    (qbeCtx : QbeContext := {}) : Grind.GrindM (Except CounterExample CegarResult) :=
  ReifyM.run (hypotheses := hypotheses) (cfg := ctx.config) do
    closeWithBVReflection g (cegarBlaster ctx qbeCtx)

/-- Default node visit cap for bounded `BitVec` multiplication detection. -/
def defaultBvMulMaxVisits : Nat := 16384

private partial def stripTermParens (stx : Syntax) : Syntax :=
  match stx with
  | `(($t:term)) => stripTermParens t
  | _ => stx

private def structInstHasExplicitAcNf (val : Syntax) : Bool :=
  let val := stripTermParens val
  if val.isOfKind ``Lean.Parser.Term.structInst then
    -- `{ src with ... }` explicitly supplies `acNf` via `src`.
    if !val[1].isNone then
      true
    else
      val[2][0].getSepArgs.any fun field =>
        match field[0] with
        | `(Lean.Parser.Term.structInstLVal| $id:ident) =>
          id.getId.eraseMacroScopes == `acNf
        | _ => false
  else
    -- Opaque `BVDecideConfig` expression: preserve its `acNf`.
    true

/-- Return `true` iff `cfgStx` explicitly specifies `acNf` (via `+acNf`, `-acNf`, `(acNf := ...)`,
or `(config := ...)` setting `acNf` or passing an opaque `BVDecideConfig`). -/
partial def hasExplicitAcNf (cfgStx : Syntax) : Bool :=
  if cfgStx.isOfKind nullKind then
    cfgStx.getArgs.any hasExplicitAcNf
  else if cfgStx.getNumArgs == 1 then
    hasExplicitAcNf (cfgStx.getArg 0)
  else if cfgStx.getNumArgs ≥ 1 then
    match cfgStx.getArg 0 with
    | .atom _ val =>
      if (val == "+" || val == "-") && cfgStx.getNumArgs == 2 then
        identName? (cfgStx.getArg 1) == some `acNf
      else if val == "(" && cfgStx.getNumArgs ≤ 5 then
        match identName? (cfgStx.getArg 1) with
        | some `acNf => true
        | some `config => structInstHasExplicitAcNf (cfgStx.getArg 3)
        | _ => false
      else
        false
    | _ => false
  else if let .atom _ val := cfgStx then
    val == "acNf"
  else
    false
where
  identName? : Syntax → Option Name
    | .ident _ _ n _ => some n.eraseMacroScopes
    | .atom _ val =>
      some (if val.contains '.' then String.toName val else Name.mkSimple val)
    | _ => none

private def isBvMulType (fixedInt : Bool) (ty : Expr) : Bool :=
  match ty.consumeMData.getAppFn.consumeMData with
  | .const n _ =>
    if n == ``BitVec then
      true
    else if fixedInt then
      n == ``UInt8 || n == ``UInt16 || n == ``UInt32 || n == ``UInt64 || n == ``USize ||
      n == ``Int8 || n == ``Int16 || n == ``Int32 || n == ``Int64 || n == ``ISize
    else
      false
  | _ => false

private def isBvMulConst (fixedInt : Bool) (n : Name) : Bool :=
  if n == ``BitVec.mul || n == ``BitVec.instMul then
    true
  else if fixedInt then
    n == ``UInt8.mul || n == ``instMulUInt8 ||
    n == ``UInt16.mul || n == ``instMulUInt16 ||
    n == ``UInt32.mul || n == ``instMulUInt32 ||
    n == ``UInt64.mul || n == ``instMulUInt64 ||
    n == ``USize.mul || n == ``instMulUSize ||
    n == ``Int8.mul || n == ``instMulInt8 ||
    n == ``Int16.mul || n == ``instMulInt16 ||
    n == ``Int32.mul || n == ``instMulInt32 ||
    n == ``Int64.mul || n == ``instMulInt64 ||
    n == ``ISize.mul || n == ``instMulISize
  else
    false

private def bvMulConstNames (fixedInt : Bool) : Array Name :=
  if fixedInt then
    #[``BitVec.mul, ``BitVec.instMul,
      ``UInt8.mul, ``instMulUInt8, ``UInt16.mul, ``instMulUInt16,
      ``UInt32.mul, ``instMulUInt32, ``UInt64.mul, ``instMulUInt64,
      ``USize.mul, ``instMulUSize,
      ``Int8.mul, ``instMulInt8, ``Int16.mul, ``instMulInt16,
      ``Int32.mul, ``instMulInt32, ``Int64.mul, ``instMulInt64,
      ``ISize.mul, ``instMulISize]
  else
    #[``BitVec.mul, ``BitVec.instMul]

private def isBvMulApp (fixedInt : Bool) (e : Expr) : Bool :=
  match e with
  | .app (.app (.app (.app f α) _) γ) _ =>
    f.consumeMData.isConstOf ``HMul.hMul &&
      (isBvMulType fixedInt α || isBvMulType fixedInt γ)
  | .app (.app f α) _ =>
    f.consumeMData.isConstOf ``Mul.mul && isBvMulType fixedInt α
  | _ => false

/-- Fast, bounded DAG scan detecting any `BitVec` (or fixed-width int when `fixedInt := true`)
multiplication (`HMul.hMul`, `Mul.mul`, `BitVec.mul`, `BitVec.instMul`, etc.) in `roots`. -/
def hasBvMulExprs (fixedInt : Bool) (roots : Array Expr)
    (maxVisits : Nat := defaultBvMulMaxVisits) : Bool := Id.run do
  let mut stack := roots
  let mut visited : Std.HashSet Sym.ExprPtr := {}
  let mut remaining := maxVisits
  while remaining > 0 && !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    match e with
    | .const n _ =>
      remaining := remaining - 1
      if isBvMulConst fixedInt n then
        return true
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ =>
      pure ()
    | .mdata _ b =>
      remaining := remaining - 1
      stack := stack.push b
    | .proj _ _ b =>
      if !visited.contains ⟨e⟩ then
        remaining := remaining - 1
        visited := visited.insert ⟨e⟩
        stack := stack.push b
    | .app f a =>
      if !visited.contains ⟨e⟩ then
        remaining := remaining - 1
        visited := visited.insert ⟨e⟩
        if isBvMulApp fixedInt e then
          return true
        stack := stack.push a
        stack := stack.push f
    | .forallE _ d b _ | .lam _ d b _ =>
      if !visited.contains ⟨e⟩ then
        remaining := remaining - 1
        visited := visited.insert ⟨e⟩
        stack := stack.push d
        stack := stack.push b
    | .letE _ t v b _ =>
      if !visited.contains ⟨e⟩ then
        remaining := remaining - 1
        visited := visited.insert ⟨e⟩
        stack := stack.push t
        stack := stack.push v
        stack := stack.push b
  return false

/-- Bounded check for `BitVec` (or fixed-width int) multiplication in goal `g` and its local
context (scanning `g`'s target first). -/
def hasBvMulInGoal (fixedInt : Bool) (g : MVarId)
    (maxVisits : Nat := defaultBvMulMaxVisits) : MetaM Bool :=
  g.withContext do
    let mut roots : Array Expr := #[]
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        if let some val := ldecl.value? then
          let val ← if val.hasMVar then instantiateMVars val else pure val
          roots := roots.push val
        let ty ← if ldecl.type.hasMVar then instantiateMVars ldecl.type else pure ldecl.type
        roots := roots.push ty
    let gty ← g.getType
    let gty ← if gty.hasMVar then instantiateMVars gty else pure gty
    roots := roots.push gty
    return hasBvMulExprs fixedInt roots maxVisits

/-- Bounded check for `BitVec` (or fixed-width int) multiplication in a `grind` goal's e-graph
and underlying `MVarId`. -/
def hasBvMulInGrindGoal (fixedInt : Bool) (g : Grind.Goal)
    (maxVisits : Nat := defaultBvMulMaxVisits) : MetaM Bool := do
  if (bvMulConstNames fixedInt).any fun n => g.indicesFound.contains (.const n) then
    return true
  let mut appRoots : Array Expr := #[]
  if let some apps := g.appMap.find? (.const ``HMul.hMul) then
    for app in apps do
      appRoots := appRoots.push app
      if appRoots.size ≥ 256 then break
  if let some apps := g.appMap.find? (.const ``Mul.mul) then
    for app in apps do
      appRoots := appRoots.push app
      if appRoots.size ≥ 512 then break
  if !appRoots.isEmpty && hasBvMulExprs fixedInt appRoots maxVisits then
    return true
  hasBvMulInGoal fixedInt g.mvarId maxVisits

/-- Resolve the effective `BVDecideConfig` for `g`: honor any explicit `acNf` setting in `cfgStx`,
otherwise enable `acNf` iff `g` contains a `BitVec` (or fixed-width int) multiplication. -/
def resolveAutoAcNf (cfgStx : Syntax) (cfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig)
    (g : MVarId) (maxVisits : Nat := defaultBvMulMaxVisits) :
    MetaM Lean.Elab.Tactic.BVDecide.BVDecideConfig := do
  if cfg.acNf || hasExplicitAcNf cfgStx then
    return cfg
  if ← hasBvMulInGoal cfg.fixedInt g maxVisits then
    return { cfg with acNf := true }
  return cfg

/-- Resolve the effective `BVDecideConfig` for a `grind`/`sym` goal `g` (respecting explicit
`acNf` in `cfgStx` and gating automatic `acNf` strictly on `BitVec` multiplication presence). -/
def resolveAutoAcNfGrind (cfgStx : Syntax) (cfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig)
    (g : Grind.Goal) (fixedInt : Bool := cfg.fixedInt)
    (maxVisits : Nat := defaultBvMulMaxVisits) :
    MetaM Lean.Elab.Tactic.BVDecide.BVDecideConfig := do
  if cfg.acNf || hasExplicitAcNf cfgStx then
    return cfg
  if ← hasBvMulInGrindGoal fixedInt g maxVisits then
    return { cfg with acNf := true }
  return cfg

/-- Build a `TacticContext` without invoking external `cadical` discovery or temp files. -/
def mkQbeTacticContext (config : Lean.Elab.Tactic.BVDecide.BVDecideConfig)
    (restrictedTypes : Option (Array Name) := none) : TacticContext :=
  {
    exprDef := .anonymous
    certDef := .anonymous
    reflectionDef := .anonymous
    solver := ""
    lratPath := ""
    config := config
    restrictedTypes := restrictedTypes
  }

/-- Fast O(|DAG|) scan checking whether `e` contains any `cond` constant. -/
private def exprHasCondConst (e : Expr) : Bool := Id.run do
  let mut stack : Array Expr := #[e]
  let mut visited : Std.HashSet Sym.ExprPtr := {}
  while !stack.isEmpty do
    let cur := stack.back!
    stack := stack.pop
    match cur with
    | .const n _ =>
      if n == ``cond then return true
    | .app f a =>
      if !visited.contains ⟨cur⟩ then
        visited := visited.insert ⟨cur⟩
        stack := stack.push a
        stack := stack.push f
    | .mdata _ b | .proj _ _ b =>
      if !visited.contains ⟨cur⟩ then
        visited := visited.insert ⟨cur⟩
        stack := stack.push b
    | _ => pure ()
  return false

private def tryRewriteSignExtendCond (e : Expr) : Sym.SymM (Option (Expr × Expr)) := do
  match_expr e with
  | cond α discrExpr thenExpr elseExpr =>
    let_expr BitVec mExpr := α | return none
    let some m := Sym.getNatValue? mExpr | return none
    if m == 0 then return none
    let some ⟨wT, bvT⟩ := Sym.getBitVecValue? thenExpr | return none
    let some ⟨wE, bvE⟩ := Sym.getBitVecValue? elseExpr | return none
    if wT != m || wE != m then return none
    let allOnes := (1 <<< m) - 1
    let normal := bvT.toNat == allOnes && bvE.toNat == 0
    let flipped := bvT.toNat == 0 && bvE.toNat == allOnes
    if !normal && !flipped then return none
    let oneLit ← Sym.share (mkNatLit 1)
    let mLit ← Sym.share (mkNatLit m)
    let mkRepl (inner : Expr) (negate : Bool) : Sym.SymM Expr := do
      let arg ←
        if negate then
          Sym.share (← mkAppM ``Complement.complement #[inner])
        else
          pure inner
      Sym.share (mkApp3 (mkConst ``BitVec.replicate) oneLit mLit arg)
    match_expr discrExpr with
    | BEq.beq discrTy _ lhs rhs =>
      let_expr BitVec dW := discrTy | return none
      let some 1 := Sym.getNatValue? dW | return none
      match (Sym.getBitVecValue? lhs).run, (Sym.getBitVecValue? rhs).run with
      | none, some ⟨1, rv⟩ =>
        if rv.toNat == 1 then
          let newE ← mkRepl lhs flipped
          let thm := if normal then ``NormalizeRules.cond_beq_one_allOnes_zero_raw
            else ``NormalizeRules.cond_beq_one_zero_allOnes_raw
          return some (newE, mkApp2 (mkConst thm) mLit lhs)
        else if rv.toNat == 0 then
          let newE ← mkRepl lhs normal
          let thm := if normal then ``NormalizeRules.cond_beq_zero_allOnes_zero_raw
            else ``NormalizeRules.cond_beq_zero_zero_allOnes_raw
          return some (newE, mkApp2 (mkConst thm) mLit lhs)
        else return none
      | some ⟨1, lv⟩, none =>
        if lv.toNat == 1 then
          let newE ← mkRepl rhs flipped
          let thm := if normal then ``NormalizeRules.cond_one_beq_allOnes_zero_raw
            else ``NormalizeRules.cond_one_beq_zero_allOnes_raw
          return some (newE, mkApp2 (mkConst thm) mLit rhs)
        else if lv.toNat == 0 then
          let newE ← mkRepl rhs normal
          let thm := if normal then ``NormalizeRules.cond_zero_beq_allOnes_zero_raw
            else ``NormalizeRules.cond_zero_beq_zero_allOnes_raw
          return some (newE, mkApp2 (mkConst thm) mLit rhs)
        else return none
      | _, _ => return none
    | BitVec.getLsbD vExpr xExpr iExpr =>
      let ext ← Sym.share (mkApp4 (mkConst ``BitVec.extractLsb') vExpr iExpr oneLit xExpr)
      let newE ← mkRepl ext flipped
      let thm := if normal then ``NormalizeRules.cond_getLsbD_allOnes_zero_raw
        else ``NormalizeRules.cond_getLsbD_zero_allOnes_raw
      return some (newE, mkApp4 (mkConst thm) vExpr mLit xExpr iExpr)
    | _ => return none
  | _ => return none

private partial def rewriteSignExtendCondsExpr (e : Expr)
    (cache : IO.Ref (Std.HashMap Sym.ExprPtr (Expr × Option Expr))) :
    Sym.SymM (Expr × Option Expr) := do
  if let some hit := (← cache.get).get? ⟨e⟩ then
    return hit
  let res : Expr × Option Expr ← match e with
    | .app f a =>
      let (f', hf?) ← rewriteSignExtendCondsExpr f cache
      let (a', ha?) ← rewriteSignExtendCondsExpr a cache
      let (cur, hChild?) ← match hf?, ha? with
        | none, none => pure (e, none)
        | some hf, some ha =>
          try
            let e' ← Sym.share (.app f' a')
            let h ← mkCongr hf ha
            pure (e', some h)
          catch _ => pure (e, none)
        | some hf, none =>
          try
            let e' ← Sym.share (.app f' a)
            let h ← mkCongrFun hf a
            pure (e', some h)
          catch _ => pure (e, none)
        | none, some ha =>
          try
            let e' ← Sym.share (.app f a')
            let h ← mkCongrArg f ha
            pure (e', some h)
          catch _ => pure (e, none)
      match ← tryRewriteSignExtendCond cur with
      | none => pure (cur, hChild?)
      | some (rwE, hRw) =>
        let hFull ← match hChild? with
          | none => pure hRw
          | some hc => mkEqTrans hc hRw
        pure (rwE, some hFull)
    | _ => pure (e, none)
  cache.modify (·.insert ⟨e⟩ res)
  return res

/-- Kernel-proved (`<= std3`), `O(|DAG|)` post-`bvNormalize` pass replacing `signExtend`-lowered
`cond (b == 1#1) allOnes 0` masks with cast-free `BitVec.replicate m b`. Eliminates the spurious
synthetic `Reflect` atoms and 4 auxiliary propositional clauses that previously blocked ARiSCA
`miterEqWidth?` dispatch on `08_baugh_wooley_{16,32,64}`. No-op when `hyps` contains no `cond`. -/
def elimSignExtendConds (hyps : Array Normalize.Hyp) : Grind.GrindM (Array Normalize.Hyp) := do
  if !hyps.any (fun h => exprHasCondConst h.type) then
    return hyps
  let cache ← IO.mkRef ({} : Std.HashMap Sym.ExprPtr (Expr × Option Expr))
  hyps.mapM fun hyp => do
    if !exprHasCondConst hyp.type then
      return hyp
    match_expr hyp.type with
    | Eq α lhsExpr rhsExpr =>
      let_expr Bool := α | return hyp
      let_expr Bool.true := rhsExpr | return hyp
      let (lhs', hEq?) ← rewriteSignExtendCondsExpr lhsExpr cache
      match hEq? with
      | none => return hyp
      | some hEq =>
        let boolTy := mkConst ``Bool
        let trueC := mkConst ``Bool.true
        let newTy ← Sym.share (mkApp3 (mkConst ``Eq [1]) boolTy lhs' trueC)
        let hSymm := mkApp4 (mkConst ``Eq.symm [1]) boolTy lhsExpr lhs' hEq
        let newVal := mkApp6 (mkConst ``Eq.trans [1]) boolTy lhs' lhsExpr trueC hSymm hyp.value
        return { hyp with type := newTy, value := newVal }
    | _ => return hyp

/-- Run `bv_decide_qbe` on `target`, returning either a `CounterExample` or `CegarResult`. -/
def bvDecideQbe' (target : Normalize.Target) (ctx : TacticContext)
    (qbeCtx : QbeContext := {}) : Grind.GrindM (Except CounterExample CegarResult) := do
  Normalize.PreProcessM.run' ctx.preProcessContext target do
    let solved ← Normalize.bvNormalize
    if solved then return .ok { lemmas := #[], proveResult? := none }
    if qbeCtx.features.mode == .enhanced && ctx.config.acNf then
      let solvedAc ← Normalize.AC.bvMulSubtermNormalize
      if solvedAc then return .ok { lemmas := #[], proveResult? := none }
    let g ← Normalize.PreProcessM.getTargetMVarId
    let rawHyps ← Normalize.PreProcessM.getHyps
    let hyps ←
      if qbeCtx.features.mode == .enhanced then
        g.withContext <| elimSignExtendConds rawHyps
      else
        pure rawHyps
    bvUnsatQbe g hyps ctx qbeCtx

private def plainGrindMethodsRef : Grind.MethodsRef :=
  ({} : Grind.Methods).toMethodsRef

private def plainGrindContext : Grind.Context := {
  simp := default
  simpMethods := {}
  config := {}
  identity := `bv_decide_qbe
  activeSolvers := #[]
  anchorRefs? := none
  symPrios := {}
  debug := false
  ematchDiag := false
}

/-- Execute a plain `.mvarIdTarget` `Grind.GrindM` action directly in `Sym.SymM` without paying
`Grind.mkDefaultParams {}` (simprocs, norm theorems, or `grind` E-matching extensions). -/
def runPlainGrindM {α : Type} (x : Grind.GrindM α) : MetaM α :=
  Sym.SymM.run <| (x plainGrindMethodsRef plainGrindContext).run' {}

/-- Run `bv_decide_qbe'` and throw a formatted counterexample error on SAT. -/
def bvDecideQbe (target : Normalize.Target) (ctx : TacticContext)
    (qbeCtx : QbeContext := {}) : Grind.GrindM CegarResult := do
  match ← bvDecideQbe' target ctx qbeCtx with
  | .ok res => return res
  | .error counterExample => throwCounterExample counterExample

end BvDecideQbe
