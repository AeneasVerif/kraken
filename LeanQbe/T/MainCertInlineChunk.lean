module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.InlineChunk
public meta import Lean
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.InlineChunk

/-!
# Chunked `inline_mod!` Materializers (`MainCertInlineChunk`)

Splits `Module.optInlinePolicy` materialization and kernel equality checking across small
independent modules (`<= 80` fns per chunk) so peak RAM stays well below `8 GB`:

* `inline_chunk_base! baseId srcMod policy`: materializes `siteCounts` / `loopCounts` and
  proves `(srcMod.optInlinePolicy policy).fns = inlRest ... 0 [] []`.
* `inline_mod_chunk! chunkId baseId srcMod policy startIdx count [(prev := ...)] [(isLast := ...)]`:
  materializes ONLY the `count` functions in `[startIdx, startIdx + count)` as `denoteFunc`-backed
  `Fn` defs, normalizes ONLY the new `cands` added in this slice via `normPhoasFn` (preserving
  definitional equality `rfl` without `denoteFunc`), and proves `step_eq` / `last_eq` over ONLY
  that slice.
* `inline_mod_join! modId fnsId srcMod policy baseId [c0, c1, ...]`: joins chunk function lists in
  `O(#chunks)` (`Eq.trans` / `inlRest_prepend_eq`) with zero kernel AST reduction, exporting
  `modId`, `fnsId`, `modId.fns_eq`, and `modId.eq`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section

open Lean Elab Command Meta
open InlineMeta

private def normListElems (normElem : Lean.Expr → MetaM Lean.Expr) (e : Lean.Expr) :
    MetaM (List Lean.Expr) := do
  let mut cur := e
  let mut out : Array Lean.Expr := #[]
  while true do
    let w ← whnf cur
    if w.isAppOfArity ``List.nil 1 then
      return out.toList
    else if w.isAppOfArity ``List.cons 3 then
      let args := w.getAppArgs
      out := out.push (← normElem args[1]!)
      cur := args[2]!
    else
      throwError "normListElems: unexpected {w}"
  return out.toList

private def normArg (vE tE e : Lean.Expr) : MetaM Lean.Expr := do
  let a ← whnf e
  if a.isAppOfArity ``LeanQbe.T.Arg.var 3 then
    let aArgs := a.getAppArgs
    return mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) vE tE (← whnf aArgs[2]!)
  if a.isAppOfArity ``LeanQbe.T.Arg.imm 3 then
    let aArgs := a.getAppArgs
    return mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) vE tE (← reduce (← whnf aArgs[2]!))
  return a

private partial def normTupArg (vE : Lean.Expr) (ts : List Lean.Expr) (e : Lean.Expr) :
    MetaM Lean.Expr := do
  match ts with
  | [] => return Lean.mkConst ``Unit.unit
  | t :: rest =>
    let e ← whnf e
    if e.isAppOfArity ``Prod.mk 4 then
      let args := e.getAppArgs
      return mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) args[0]! args[1]!
        (← normArg vE t args[2]!) (← normTupArg vE rest args[3]!)
    throwError "normTupArg: unexpected {e}"

private def normOp (vE opE : Lean.Expr) : MetaM Lean.Expr := do
  let opW ← whnf opE
  if opW.isAppOfArity ``LeanQbe.T.Op.mk 5 then
    let args := opW.getAppArgs
    let sig ← normListElems whnf args[2]!
    let code ← reduce (← whnf args[3]!)
    return mkApp5 (Lean.mkConst ``LeanQbe.T.Op.mk) vE args[1]! args[2]! code
      (← normTupArg vE sig args[4]!)
  return opW

private def mkTupTy (elemTy fE : Lean.Expr) (elems : List Lean.Expr) : Lean.Expr :=
  mkApp3 (Lean.mkConst ``LeanQbe.T.Tup) elemTy fE (mkListLit .zero elemTy elems)

private def tyExpr : Lean.Expr := Lean.mkConst ``LeanQbe.T.Ty
private def listTyExpr : Lean.Expr := mkApp (Lean.mkConst ``List [.zero]) tyExpr

private def mkEtaTup (fE : Lean.Expr) (elemTys : List Lean.Expr) (tupVar : Lean.Expr)
    (mkTy : List Lean.Expr → Lean.Expr) : Lean.Expr :=
  let rec go (curVar : Lean.Expr) : List Lean.Expr → Lean.Expr
    | [] => Lean.mkConst ``Unit.unit
    | t :: ts =>
      let ta := mkApp fE t
      let tb := mkTy ts
      let fst := mkApp3 (Lean.mkConst ``Prod.fst [.zero, .zero]) ta tb curVar
      let snd := mkApp3 (Lean.mkConst ``Prod.snd [.zero, .zero]) ta tb curVar
      mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb fst (go snd ts)
  go tupVar elemTys

private inductive LinStep where
  | let_ (tsE opNorm tupTy fvar : Lean.Expr)
  | load (tE aNorm vtTy fvar : Lean.Expr)
  | store (tE vNorm aNorm : Lean.Expr)
  | call (fNorm asE bsE argsNorm tupTy fvar : Lean.Expr)

mutual
private partial def normPhoasExpr (vE lE rsE e : Lean.Expr) : MetaM Lean.Expr := do
  let mut lctx ← getLCtx
  let insts ← getLocalInstances
  let mut cur := e
  let mut steps : Array LinStep := #[]
  let mut termNorm : Option Lean.Expr := none
  while termNorm.isNone do
    let eW ← withLCtx lctx insts (whnf cur)
    if eW.isAppOfArity ``LeanQbe.T.Expr.let_ 6 then
      let args := eW.getAppArgs
      let tsE ← withLCtx lctx insts (reduce args[3]!)
      let ts ← withLCtx lctx insts (normListElems whnf tsE)
      let opNorm ← withLCtx lctx insts (normOp vE args[4]!)
      let tupTy := mkTupTy tyExpr vE ts
      let fvarId ← mkFreshFVarId
      let fvar := Lean.mkFVar fvarId
      lctx := lctx.mkLocalDecl fvarId `x tupTy
      steps := steps.push (.let_ tsE opNorm tupTy fvar)
      cur := mkApp args[5]! (mkEtaTup vE ts fvar (mkTupTy tyExpr vE))
    else if eW.isAppOfArity ``LeanQbe.T.Expr.load 6 then
      let args := eW.getAppArgs
      let tE ← withLCtx lctx insts (reduce args[3]!)
      let aNorm ← withLCtx lctx insts (normArg vE (Lean.mkConst ``LeanQbe.T.i64) args[4]!)
      let vtTy := mkApp vE tE
      let fvarId ← mkFreshFVarId
      let fvar := Lean.mkFVar fvarId
      lctx := lctx.mkLocalDecl fvarId `v vtTy
      steps := steps.push (.load tE aNorm vtTy fvar)
      cur := mkApp args[5]! fvar
    else if eW.isAppOfArity ``LeanQbe.T.Expr.store 7 then
      let args := eW.getAppArgs
      let tE ← withLCtx lctx insts (reduce args[3]!)
      let vNorm ← withLCtx lctx insts (normArg vE tE args[4]!)
      let aNorm ← withLCtx lctx insts (normArg vE (Lean.mkConst ``LeanQbe.T.i64) args[5]!)
      steps := steps.push (.store tE vNorm aNorm)
      cur := args[6]!
    else if eW.isAppOfArity ``LeanQbe.T.Expr.call 8 then
      let args := eW.getAppArgs
      let fNorm ← withLCtx lctx insts (reduce args[3]!)
      let asE ← withLCtx lctx insts (reduce args[4]!)
      let bsE ← withLCtx lctx insts (reduce args[5]!)
      let asL ← withLCtx lctx insts (normListElems whnf asE)
      let bsL ← withLCtx lctx insts (normListElems whnf bsE)
      let argsNorm ← withLCtx lctx insts (normTupArg vE asL args[6]!)
      let tupTy := mkTupTy tyExpr vE bsL
      let fvarId ← mkFreshFVarId
      let fvar := Lean.mkFVar fvarId
      lctx := lctx.mkLocalDecl fvarId `xs tupTy
      steps := steps.push (.call fNorm asE bsE argsNorm tupTy fvar)
      cur := mkApp args[7]! (mkEtaTup vE bsL fvar (mkTupTy tyExpr vE))
    else
      let tail ← withLCtx lctx insts do
        if eW.isAppOfArity ``LeanQbe.T.Expr.jnz 6 then
          let args := eW.getAppArgs
          let cNorm ← normArg vE (Lean.mkConst ``LeanQbe.T.Ty.bool) args[3]!
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jnz)
            #[vE, lE, rsE, cNorm, ← normPhoasExpr vE lE rsE args[4]!,
              ← normPhoasExpr vE lE rsE args[5]!]
        if eW.isAppOfArity ``LeanQbe.T.Expr.jump 6 then
          let args := eW.getAppArgs
          let tsE ← reduce args[3]!
          let ts ← normListElems whnf tsE
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
            #[vE, lE, rsE, tsE, ← whnf args[4]!, ← normTupArg vE ts args[5]!]
        if eW.isAppOfArity ``LeanQbe.T.Expr.ret 4 then
          let args := eW.getAppArgs
          let rsL ← normListElems whnf rsE
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.ret)
            #[vE, lE, rsE, ← normTupArg vE rsL args[3]!]
        if eW.isAppOfArity ``LeanQbe.T.Expr.exit 6 then
          let args := eW.getAppArgs
          let fNorm ← reduce args[3]!
          let asE ← reduce args[4]!
          let asL ← normListElems whnf asE
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.exit)
            #[vE, lE, rsE, fNorm, asE, ← normTupArg vE asL args[5]!]
        if eW.isAppOfArity ``LeanQbe.T.Expr.hlt 3 then
          return eW
        if eW.isAppOfArity ``LeanQbe.T.Expr.group 6 then
          let args := eW.getAppArgs
          let sigE ← reduce args[3]!
          let sigL ← normListElems reduce sigE
          let tupLTy := mkTupTy listTyExpr lE sigL
          let etaL js := mkEtaTup lE sigL js (mkTupTy listTyExpr lE)
          let bodiesNorm ← withLocalDeclD `Js tupLTy fun js => do
            mkLambdaFVars #[js] (← normPhoasBlocks vE lE rsE (mkApp args[4]! (etaL js)))
          let kNorm ← withLocalDeclD `Js tupLTy fun js => do
            mkLambdaFVars #[js] (← normPhoasExpr vE lE rsE (mkApp args[5]! (etaL js)))
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.group)
            #[vE, lE, rsE, sigE, bodiesNorm, kNorm]
        throwError "normPhoasExpr: unexpected {eW}"
      termNorm := some tail
  let mut acc := termNorm.get!
  for step in steps.reverse do
    match step with
    | .let_ tsE opNorm tupTy fvar =>
      let kLam := Lean.mkLambda `x .default tupTy (acc.abstract #[fvar])
      acc := mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_) #[vE, lE, rsE, tsE, opNorm, kLam]
    | .load tE aNorm vtTy fvar =>
      let kLam := Lean.mkLambda `v .default vtTy (acc.abstract #[fvar])
      acc := mkAppN (Lean.mkConst ``LeanQbe.T.Expr.load) #[vE, lE, rsE, tE, aNorm, kLam]
    | .store tE vNorm aNorm =>
      acc := mkAppN (Lean.mkConst ``LeanQbe.T.Expr.store) #[vE, lE, rsE, tE, vNorm, aNorm, acc]
    | .call fNorm asE bsE argsNorm tupTy fvar =>
      let kLam := Lean.mkLambda `xs .default tupTy (acc.abstract #[fvar])
      acc := mkAppN (Lean.mkConst ``LeanQbe.T.Expr.call)
        #[vE, lE, rsE, fNorm, asE, bsE, argsNorm, kLam]
  return acc

private partial def normPhoasBlocks (vE lE rsE e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnf e
  if e.isAppOfArity ``LeanQbe.T.Blocks.nil 3 then
    return e
  if e.isAppOfArity ``LeanQbe.T.Blocks.cons 7 then
    let args := e.getAppArgs
    let tsE ← reduce args[3]!
    let sigE ← reduce args[4]!
    let ts ← normListElems whnf tsE
    let bNorm ← withLocalDeclD `xs (mkTupTy tyExpr vE ts) fun xs => do
      let appB := mkApp args[5]! (mkEtaTup vE ts xs (mkTupTy tyExpr vE))
      mkLambdaFVars #[xs] (← normPhoasExpr vE lE rsE appB)
    return mkAppN (Lean.mkConst ``LeanQbe.T.Blocks.cons)
      #[vE, lE, rsE, tsE, sigE, bNorm, ← normPhoasBlocks vE lE rsE args[6]!]
  throwError "normPhoasBlocks: unexpected {e}"
end

/-- Normalize a closed PHOAS `Fn` term into a flat literal `Fn.mk` without `denoteFunc`. -/
def normPhoasFn (fnE : Lean.Expr) : MetaM Lean.Expr := do
  let fnW ← whnf fnE
  if !fnW.isAppOfArity ``LeanQbe.T.Fn.mk 4 then
    throwError "normPhoasFn: unexpected {fnW}"
  let args := fnW.getAppArgs
  let nmE ← reduce args[0]!
  let asE ← reduce args[1]!
  let rsE ← reduce args[2]!
  let asL ← normListElems whnf asE
  let vTy := Lean.mkForall `t .default tyExpr (mkSort Level.one)
  let lTy := Lean.mkForall `ts .default listTyExpr (mkSort Level.one)
  let bodyNorm ← withLocalDeclD `V vTy fun vE =>
    withLocalDeclD `L lTy fun lE =>
      withLocalDeclD `xs (mkTupTy tyExpr vE asL) fun xs => do
        let appBody := mkApp3 args[3]! vE lE (mkEtaTup vE asL xs (mkTupTy tyExpr vE))
        mkLambdaFVars #[vE, lE, xs] (← normPhoasExpr vE lE rsE appBody)
  return mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk) nmE asE rsE bodyNorm

/-- Compiled MetaM output for a single inlining chunk `[a, a + n)`. -/
structure EvalChunkInlData where
  matFns : List MatFnData
  candFlags : List Bool
  seenOut : List SigEntry

/-- Extended chunk output also recording per-accepted-candidate chronological push indices. -/
structure EvalChunkInlDataEx where
  base : EvalChunkInlData
  candSelIdxs : List (List Nat)

/-- Evaluated base metadata for chunked `Module.optInlinePolicy` materialization. -/
structure EvalChunkBaseData where
  siteCounts : List (Sym × Nat)
  loopCounts : List (Sym × Nat)
  externs : List Extern
  exits : List Sym

/-- Evaluate `inlSiteCounts`, `inlLoopCounts`, `externs`, and `exits` once in MetaM. -/
def evalChunkBaseData (M : Module) (policy : InlinePolicy) : EvalChunkBaseData :=
  { siteCounts := inlSiteCounts policy M.fns
    loopCounts := inlLoopCounts policy M.fns
    externs := M.externs
    exits := M.exits }

private def evalChunkLoop (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (exits : List Sym) : List SigEntry → List SigEntry → List Fn → List Fn →
    List MatFnData → List Bool → List (List Nat) → EvalChunkInlDataEx
  | seenRev, _, _, [], msRev, fsRev, idxsRev =>
    { base := { matFns := msRev.reverse, candFlags := fsRev.reverse, seenOut := seenRev.reverse }
      candSelIdxs := idxsRev.reverse }
  | seenRev, allowed, cands, fn :: rest, msRev, fsRev, idxsRev =>
    let candsFn := selectCandsForCaller policy cands fn
    let fn' := fn.inline candsFn
    let sites := lookupCallSite siteCounts fn'.name
    let loopSites := lookupCallSite loopCounts fn'.name
    let ok := inlineCandidateOkPolicy policy sites loopSites allowed exits fn'
    let cands' := if ok then fn' :: cands else cands
    let idxs' :=
      if ok then
        let calls := exprCallSites []
          (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))
        let used := candsFn.filter fun c => calls.any fun p => p.1 == c.name
        let pushIdxs := used.filterMap fun c =>
          (cands.zipIdx.find? fun (g, _) =>
            g.name == c.name && g.as == c.as && g.rs == c.rs).map fun (_, k) =>
            cands.length - 1 - k
        pushIdxs :: idxsRev
      else idxsRev
    evalChunkLoop policy siteCounts loopCounts exits
      (fn.sig :: seenRev) (fn.sig :: allowed) cands' rest
      (⟨fn.name, fn.as, fn.rs, reifyFunc fn'.body⟩ :: msRev)
      (ok :: fsRev) idxs'

/-- Evaluate `[a, a + n)` via tail-recursive `evalChunkLoop`, returning reified `MatFnData`,
candidate flags, `seenOut`, and chronological candidate push indices for `normPhoasFn`. -/
def evalChunkInlDataEx (M : Module) (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat)) (a n : Nat) : EvalChunkInlDataEx :=
  let pre := M.fns.take a
  let slice := (M.fns.drop a).take n
  let extSigs := M.externs.map Extern.sig
  let seenPreRev := (pre.map Fn.sig).reverse
  let candsPre := inlineFnsPolicyCands policy siteCounts loopCounts extSigs M.exits [] [] pre
  evalChunkLoop policy siteCounts loopCounts M.exits
    seenPreRev (seenPreRev ++ extSigs) candsPre slice [] [] []

/-- Evaluate `[a, a + n)` returning `EvalChunkInlData`. -/
def evalChunkInlData (M : Module) (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat)) (a n : Nat) : EvalChunkInlData :=
  (evalChunkInlDataEx M policy siteCounts loopCounts a n).base

private def peelListRange (listE : Lean.Expr) (start count : Nat)
    (bounded : Bool := true) : MetaM (Array Lean.Expr) := do
  let mut cur := listE
  let mut idx : Nat := 0
  let stop := start + count
  let mut out : Array Lean.Expr := #[]
  while !bounded || idx < stop do
    let w ← whnf cur
    if w.isAppOfArity ``List.nil 1 then
      return out
    else if w.isAppOfArity ``List.cons 3 then
      let args := w.getAppArgs
      if idx >= start then
        out := out.push args[1]!
      cur := args[2]!
      idx := idx + 1
    else
      throwError "inline_mod_chunk!: expected list cons/nil at index {idx}, got {w}"
  return out

private def resolveConstLitElemsRev (constNm : Name) : MetaM (Array Lean.Expr) := do
  let env ← getEnv
  let mut curNm? : Option Name := some constNm
  let mut revOut : Array Lean.Expr := #[]
  while let some nm := curNm? do
    curNm? := none
    let some cinfo := env.find? nm
      | throwError "inline_mod_chunk!: unknown constant '{nm}'"
    let some val := cinfo.value?
      | throwError "inline_mod_chunk!: constant '{nm}' has no value"
    let mut cur := val
    while true do
      if cur.isAppOfArity ``List.nil 1 then
        break
      else if cur.isAppOfArity ``List.cons 3 then
        let args := cur.getAppArgs
        revOut := revOut.push args[1]!
        cur := args[2]!
      else if cur.isConst then
        curNm? := some cur.constName!
        break
      else
        throwError "inline_mod_chunk!: expected literal list/tail in '{nm}', got {cur}"
  return revOut.reverse

private def evalChunkBaseElab (srcModT policyT : Syntax) :
    TermElabM (Lean.Expr × Lean.Expr × EvalChunkBaseData) := do
  let (srcModE, policyE) ← elabModAndPolicy srcModT policyT
  let callE := mkApp2 (Lean.mkConst ``LeanQbe.T.evalChunkBaseData) srcModE policyE
  let bd ← unsafe evalExpr EvalChunkBaseData (Lean.mkConst ``LeanQbe.T.EvalChunkBaseData) callE
  return (srcModE, policyE, bd)

/-- `inline_chunk_base! baseId srcMod policy` emits materialized `siteCounts` / `loopCounts`
tables and `rest0_eq : (srcMod.optInlinePolicy policy).fns = inlRest ... 0 [] []`. -/
scoped syntax "inline_chunk_base! " ident term:arg term:arg : command

scoped elab_rules : command
  | `(inline_chunk_base! $baseId $srcModT $policyT) => do
    let ns ← getCurrNamespace
    let baseNm := ns ++ baseId.getId
    let (srcModE, policyE, baseData) ← liftTermElabM (evalChunkBaseElab srcModT policyT)
    let symNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.Sym) (Lean.mkConst ``Nat)
    let listSymNatTy := mkApp (Lean.mkConst ``List [.zero]) symNatTy
    let listSymTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym)
    let scNm := baseNm ++ `siteCounts
    let lcNm := baseNm ++ `loopCounts
    let scEqNm := baseNm ++ `siteCounts_eq
    let lcEqNm := baseNm ++ `loopCounts_eq
    let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) srcModE
    liftCoreM do
      addCertDef scNm listSymNatTy (listSymNatToExpr baseData.siteCounts) true
      addCertDef lcNm listSymNatTy (listSymNatToExpr baseData.loopCounts) true
      addCertDef (baseNm ++ `extSigs)
        (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.SigEntry))
        (listSigToExpr (baseData.externs.map Extern.sig)) false
      addCertDef (baseNm ++ `exits) listSymTy (listSymToExpr baseData.exits) false
      addKernelEqThm scEqNm listSymNatTy
        (mkApp2 (Lean.mkConst ``LeanQbe.T.inlSiteCounts) policyE fnsE) (Lean.mkConst scNm) .zero
      addKernelEqThm lcEqNm listSymNatTy
        (mkApp2 (Lean.mkConst ``LeanQbe.T.inlLoopCounts) policyE fnsE) (Lean.mkConst lcNm) .zero
    let (rest0Ty, rest0Val) ← liftTermElabM do
      let pf := mkAppN (Lean.mkConst ``LeanQbe.T.Module.optInlinePolicy_fns_eq_inlRest)
        #[srcModE, policyE, Lean.mkConst scNm, Lean.mkConst lcNm,
          Lean.mkConst scEqNm, Lean.mkConst lcEqNm]
      return (← instantiateMVars (← inferType pf), ← instantiateMVars pf)
    liftCoreM <| addCertThm (baseNm ++ `rest0_eq) rest0Ty rest0Val

/-- `inline_mod_chunk! chunkId baseId srcMod policy startIdx count [(prev := ...)]
[(isLast := ...)]` materializes and kernel-checks ONLY `[startIdx, startIdx + count)`. -/
scoped syntax "inline_mod_chunk! " ident ident term:arg term:arg num num
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(inline_mod_chunk! $chunkId $baseId $srcModT $policyT $startLit $countLit
      $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let chunkNm := ns ++ chunkId.getId
    let baseNm := ns ++ baseId.getId
    let (aN, nN) := (startLit.getNat, countLit.getNat)
    let mut prevNm? : Option Name := none
    let mut isLast := false
    for i in [:optKeys.size] do
      let v := optVals[i]!
      match optKeys[i]!.getId with
      | `prev =>
        if let `($pid:ident) := v then prevNm? := some (ns ++ pid.getId)
        else throwErrorAt v "inline_mod_chunk!: prev must be an identifier"
      | `isLast =>
        isLast ← liftTermElabM do
          let e ← Term.elabTerm v (some (Lean.mkConst ``Bool))
          Term.synthesizeSyntheticMVarsNoPostponing
          unsafe evalExpr Bool (Lean.mkConst ``Bool) (← instantiateMVars e)
      | k => throwErrorAt optKeys[i]! "inline_mod_chunk!: unknown option '{k}'"
    let (scNm, lcNm) := (baseNm ++ `siteCounts, baseNm ++ `loopCounts)
    let (srcModE, policyE, chunkEx) ← liftTermElabM do
      let (srcModE, policyE) ← elabModAndPolicy srcModT policyT
      let callE := mkAppN (Lean.mkConst ``LeanQbe.T.evalChunkInlDataEx)
        #[srcModE, policyE, Lean.mkConst scNm, Lean.mkConst lcNm, mkNatLit aN, mkNatLit nN]
      let cd ← unsafe evalExpr EvalChunkInlDataEx
        (Lean.mkConst ``LeanQbe.T.EvalChunkInlDataEx) callE
      return (srcModE, policyE, cd)
    let chunkData := chunkEx.base
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let listFnTy := mkApp (Lean.mkConst ``List [1]) fnTy
    let listSigTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.SigEntry)
    let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) srcModE
    let extSigsE := mkApp4 (Lean.mkConst ``List.map [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.Extern) (Lean.mkConst ``LeanQbe.T.SigEntry)
      (Lean.mkConst ``LeanQbe.T.Extern.sig)
      (mkApp (Lean.mkConst ``LeanQbe.T.Module.externs) srcModE)
    let exitsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.exits) srcModE
    let seenInE := match prevNm? with
      | none => mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.SigEntry)
      | some p => Lean.mkConst (p ++ `seenOut)
    let candsInE := match prevNm? with
      | none => mkApp (Lean.mkConst ``List.nil [1]) fnTy
      | some p => Lean.mkConst (p ++ `candsOut)
    let fnConsts ← liftCoreM <| emitMatFnDefs chunkNm chunkData.matFns
    let litFnsNm := chunkNm ++ `fns
    liftCoreM <| addCertDef litFnsNm listFnTy (mkListLit .one fnTy fnConsts) true
    let sliceE := mkApp3 (Lean.mkConst ``List.take [1]) fnTy (mkNatLit nN)
      (mkApp3 (Lean.mkConst ``List.drop [1]) fnTy (mkNatLit aN) fnsE)
    let rhsRaw := mkAppN (Lean.mkConst ``LeanQbe.T.inlineFnsPolicy)
      #[policyE, Lean.mkConst scNm, Lean.mkConst lcNm, extSigsE, exitsE, seenInE, candsInE, sliceE]
    let rhsLit := mkApp4 (Lean.mkConst ``List.map [1, 1]) fnTy fnTy
      (Lean.mkConst ``LeanQbe.T.Fn.renorm) rhsRaw
    let litEqNm := chunkNm ++ `fns_eq
    liftCoreM <| addKernelEqThm litEqNm listFnTy (Lean.mkConst litFnsNm) rhsLit .one
    if isLast then
      let lenLeNm := chunkNm ++ `len_le
      let bleLhs := mkApp2 (Lean.mkConst ``Nat.ble)
        (mkApp (Lean.mkConst ``List.length [1]) fnTy |>.app fnsE) (mkNatLit (aN + nN))
      liftCoreM <| addKernelEqThm lenLeNm (Lean.mkConst ``Bool)
        bleLhs (Lean.mkConst ``Bool.true) .zero
      let (lastTy, lastVal) ← liftTermElabM do
        let pf := mkAppN (Lean.mkConst ``LeanQbe.T.inlRest_last)
          #[policyE, Lean.mkConst scNm, Lean.mkConst lcNm, extSigsE, exitsE, fnsE,
            mkNatLit aN, mkNatLit nN, seenInE, candsInE, Lean.mkConst litFnsNm,
            Lean.mkConst lenLeNm, Lean.mkConst litEqNm]
        return (← instantiateMVars (← inferType pf), ← instantiateMVars pf)
      liftCoreM <| addCertThm (chunkNm ++ `last_eq) lastTy lastVal
    else
      let seenOutNm := chunkNm ++ `seenOut
      let candsOutNm := chunkNm ++ `candsOut
      let sliceSigs := chunkData.matFns.map fun f => (f.name, f.as, f.rs)
      let seenOutVal := mkApp3 (Lean.mkConst ``List.append [.zero])
        (Lean.mkConst ``LeanQbe.T.SigEntry) seenInE (listSigToExpr sliceSigs)
      liftCoreM <| addCertDef seenOutNm listSigTy seenOutVal false
      let mut curCandArr ← liftTermElabM do
        match prevNm? with
        | none => pure #[]
        | some p => resolveConstLitElemsRev (p ++ `candsOut)
      let sliceFnExprs ← liftTermElabM do
        if chunkData.candFlags.any id then peelListRange fnsE aN nN else pure #[]
      let mut newCands : Array Lean.Expr := #[]
      let mut selQueue := chunkEx.candSelIdxs
      let mut j : Nat := 0
      for ok in chunkData.candFlags do
        if ok then
          let pushIdxs := selQueue.head!
          selQueue := selQueue.tail!
          let normE ← liftTermElabM do
            let selListE := mkListLit .one fnTy (pushIdxs.map fun idx => curCandArr[idx]!)
            normPhoasFn (mkApp2 (Lean.mkConst ``LeanQbe.T.Fn.inline) selListE sliceFnExprs[j]!)
          let cNm := chunkNm ++ `cand ++ Name.mkSimple s!"c{j}"
          liftCoreM <| addCertDef cNm fnTy normE false
          let cConst := Lean.mkConst cNm
          curCandArr := curCandArr.push cConst
          newCands := newCands.push cConst
        j := j + 1
      let candsOutVal := newCands.foldl
        (fun acc x => mkApp3 (Lean.mkConst ``List.cons [.one]) fnTy x acc) candsInE
      liftCoreM <| addCertDef candsOutNm listFnTy candsOutVal false
      let seenRhs := mkApp3 (Lean.mkConst ``List.append [.zero])
        (Lean.mkConst ``LeanQbe.T.SigEntry) seenInE
        (mkApp4 (Lean.mkConst ``List.map [1, .zero]) fnTy (Lean.mkConst ``LeanQbe.T.SigEntry)
          (Lean.mkConst ``LeanQbe.T.Fn.sig) sliceE)
      let candsRhs := mkAppN (Lean.mkConst ``LeanQbe.T.inlineFnsPolicyCands)
        #[policyE, Lean.mkConst scNm, Lean.mkConst lcNm, extSigsE, exitsE,
          seenInE, candsInE, sliceE]
      let seenEqNm := chunkNm ++ `seen_eq
      let candsEqNm := chunkNm ++ `cands_eq
      liftCoreM do
        addKernelEqThm seenEqNm listSigTy (Lean.mkConst seenOutNm) seenRhs .zero
        addKernelEqThm candsEqNm listFnTy (Lean.mkConst candsOutNm) candsRhs .one
      let (stepTy, stepVal) ← liftTermElabM do
        let bLit := mkNatLit (aN + nN)
        let hab := mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``Nat) bLit
        let pf := mkAppN (Lean.mkConst ``LeanQbe.T.inlRest_step)
          #[policyE, Lean.mkConst scNm, Lean.mkConst lcNm, extSigsE, exitsE, fnsE,
            mkNatLit aN, mkNatLit nN, bLit, seenInE, Lean.mkConst seenOutNm,
            candsInE, Lean.mkConst candsOutNm, Lean.mkConst litFnsNm, hab,
            Lean.mkConst litEqNm, Lean.mkConst seenEqNm, Lean.mkConst candsEqNm]
        return (← instantiateMVars (← inferType pf), ← instantiateMVars pf)
      liftCoreM <| addCertThm (chunkNm ++ `step_eq) stepTy stepVal

/-- `inline_mod_join! modId fnsId srcMod policy baseId [c0, c1, ...]` concatenates chunk
function lists right-associatively into `fnsId` and `modId`, proving `modId.fns_eq` and
`modId.eq` in `O(#chunks)` with zero kernel AST reduction. -/
scoped syntax "inline_mod_join! " ident ident term:arg term:arg ident
    "[" ident,* "]" : command

scoped elab_rules : command
  | `(inline_mod_join! $modId $fnsId $srcModT $policyT $baseId [$chunkIds,*]) => do
    let ns ← getCurrNamespace
    let (modNm, fnsNm, baseNm) := (ns ++ modId.getId, ns ++ fnsId.getId, ns ++ baseId.getId)
    let chunkNms := chunkIds.getElems.toList.map fun id => ns ++ id.getId
    if chunkNms.isEmpty then throwError "inline_mod_join!: chunk list cannot be empty"
    let (srcModE, policyE, baseData) ← liftTermElabM (evalChunkBaseElab srcModT policyT)
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let listFnTy := mkApp (Lean.mkConst ``List [1]) fnTy
    let modTy := Lean.mkConst ``LeanQbe.T.Module
    let fnsVal := match (chunkNms.map fun c => Lean.mkConst (c ++ `fns)).reverse with
      | [] => mkApp (Lean.mkConst ``List.nil [1]) fnTy
      | last :: restRev =>
        restRev.foldl (fun acc pre => mkApp3 (Lean.mkConst ``List.append [1]) fnTy pre acc) last
    liftCoreM do
      addCertDef fnsNm listFnTy fnsVal true
      addCertDef modNm modTy (mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk) (Lean.mkConst fnsNm)
        (listExternToExpr baseData.externs) (listSymToExpr baseData.exits)) true
    let (fnsEqTy, fnsEqProof, modEqTy, modEqProof) ← liftTermElabM do
      let revChunks := chunkNms.reverse
      let mut eqPf : Lean.Expr := Lean.mkConst (revChunks.head! ++ `last_eq)
      for cNm in revChunks.tail! do
        eqPf ← mkAppM ``LeanQbe.T.inlRest_prepend_eq #[Lean.mkConst (cNm ++ `step_eq), eqPf]
      let fnsEqPf ← mkEqSymm (← mkEqTrans (Lean.mkConst (baseNm ++ `rest0_eq)) eqPf)
      let optModE := mkApp2 (Lean.mkConst ``LeanQbe.T.Module.optInlinePolicy) srcModE policyE
      let modFnsEqTy := mkApp3 (Lean.mkConst ``Eq [2]) listFnTy
        (mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) (Lean.mkConst modNm))
        (mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) optModE)
      let extsEq := mkApp2 (Lean.mkConst ``Eq.refl [.one])
        (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Extern))
        (listExternToExpr baseData.externs)
      let exitsEq := mkApp2 (Lean.mkConst ``Eq.refl [.one])
        (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym))
        (listSymToExpr baseData.exits)
      let modEqPf := mkApp5 (Lean.mkConst ``LeanQbe.T.Module.eq_of_fields)
        (Lean.mkConst modNm) optModE fnsEqPf extsEq exitsEq
      let modEqTy := mkApp3 (Lean.mkConst ``Eq [2]) modTy (Lean.mkConst modNm) optModE
      return (← instantiateMVars modFnsEqTy, ← instantiateMVars fnsEqPf,
        ← instantiateMVars modEqTy, ← instantiateMVars modEqPf)
    liftCoreM do
      addCertThm (modNm ++ `fns_eq) fnsEqTy fnsEqProof
      addCertThm (modNm ++ `eq) modEqTy modEqProof

end

end LeanQbe.T
