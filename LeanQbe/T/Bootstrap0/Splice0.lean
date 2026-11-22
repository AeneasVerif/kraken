module

public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Frontend.C0.Elab
public import LeanQbe.T.MainCert
meta import Lean
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.Frontend.C0.Elab
meta import LeanQbe.T.MainCert

/-!
# Topological Splicer for Lowered `LeanLCNF` Modules (`Bootstrap0`)

Provides the `splice_lcnf_tflat!` command elaborator used to materialize `lowerModule lcMod` into
exposed kernel `TFlatFn` definitions ordered strictly callees-first via post-order DFS topological
sort, feeding `LeanLRC.tflatFnsToFns` + `LeanLRC.tflatFnsToFns_wf` and `compile_linked_chunks!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bootstrap0

meta section

open Lean Elab Command Term Meta
open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Notation (tyConst boolTyExpr i64TyExpr listTyConst mkTupTy listLit)
open LeanQbe.T.Frontend.C0 (TFlatFn valToExpr opCodeToExpr addExposedDecl)

def tyExpr0 (t : Ty) : Lean.Expr :=
  LeanQbe.T.Frontend.C0.tyToExpr t

/-- Reify `Arg K t` to a kernel `Lean.Expr`. -/
def spliceArgK (tE : Lean.Expr) : {t : Ty} → Arg K t → Lean.Expr
  | _, .var i =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) (Lean.mkConst ``LeanQbe.T.K) tE (mkNatLit i)
  | t, .imm c =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) (Lean.mkConst ``LeanQbe.T.K) tE (valToExpr t c)

/-- Reify `Tup (Arg K) ts` to a kernel `Lean.Expr`. -/
def spliceTupArgK : (ts : List Ty) → Tup (Arg K) ts → Lean.Expr
  | [], () => Lean.mkConst ``Unit.unit
  | t :: ts, (a, rest) =>
    let tE := tyExpr0 t
    let fE := mkApp (Lean.mkConst ``LeanQbe.T.Arg) (Lean.mkConst ``LeanQbe.T.K)
    let hdTy := mkApp fE tE
    let eHd := spliceArgK tE a
    let eTl := spliceTupArgK ts rest
    let restTy := mkTupTy tyConst fE (ts.map tyExpr0)
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) hdTy restTy eHd eTl

/-- Reify `Op K ts` to a kernel `Lean.Expr`. -/
def spliceOpK {ts : List Ty} (op : Op K ts) : Except String Lean.Expr := do
  let { sig, code, args } := op
  let tsE := listLit tyConst (ts.map tyExpr0)
  let sigE := listLit tyConst (sig.map tyExpr0)
  let codeE ← opCodeToExpr code
  let argsE := spliceTupArgK sig args
  let kC := Lean.mkConst ``LeanQbe.T.K
  pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[kC, tsE, sigE, codeE, argsE]

mutual
/-- Reify `TFlat rs` to a kernel `Lean.Expr`. -/
partial def spliceTFlat (rsE : Lean.Expr) {rs : List Ty} : TFlat rs → Except String Lean.Expr
  | .let_ (ts := ts) op k => do
    let tsE := listLit tyConst (ts.map tyExpr0)
    let opE ← spliceOpK op
    let kE ← spliceTFlat rsE k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.let_) #[rsE, tsE, opE, kE]
  | .load t a k => do
    let tE := tyExpr0 t
    let aE := spliceArgK i64TyExpr a
    let kE ← spliceTFlat rsE k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.load) #[rsE, tE, aE, kE]
  | .store (t := t) v a k => do
    let tE := tyExpr0 t
    let vE := spliceArgK tE v
    let aE := spliceArgK i64TyExpr a
    let kE ← spliceTFlat rsE k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.store) #[rsE, tE, vE, aE, kE]
  | .call f (as := as) bs args k => do
    let asE := listLit tyConst (as.map tyExpr0)
    let bsE := listLit tyConst (bs.map tyExpr0)
    let argsE := spliceTupArgK as args
    let kE ← spliceTFlat rsE k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.call)
      #[rsE, mkStrLit f, asE, bsE, argsE, kE]
  | .jnz c t e => do
    let cE := spliceArgK boolTyExpr c
    let tE ← spliceTFlat rsE t
    let eE ← spliceTFlat rsE e
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.jnz) #[rsE, cE, tE, eE]
  | .jump (ts := ts) j args => do
    let tsE := listLit tyConst (ts.map tyExpr0)
    let argsE := spliceTupArgK ts args
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.jump) #[rsE, tsE, mkNatLit j, argsE]
  | .ret vs => do
    let vsE := spliceTupArgK rs vs
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.ret) #[rsE, vsE]
  | .exit f (as := as) args => do
    let asE := listLit tyConst (as.map tyExpr0)
    let argsE := spliceTupArgK as args
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.exit) #[rsE, mkStrLit f, asE, argsE]
  | .hlt => pure <| mkApp (Lean.mkConst ``LeanQbe.T.TFlat.hlt) rsE
  | .group (sig := sig) bodies k => do
    let sigE := listLit listTyConst (sig.map fun ts => listLit tyConst (ts.map tyExpr0))
    let bE ← spliceTBlocks rsE bodies
    let kE ← spliceTFlat rsE k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TFlat.group) #[rsE, sigE, bE, kE]

/-- Reify `TBlocks rs sig` to a kernel `Lean.Expr`. -/
partial def spliceTBlocks (rsE : Lean.Expr) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Except String Lean.Expr
  | _, .nil => pure <| mkApp (Lean.mkConst ``LeanQbe.T.TBlocks.nil) rsE
  | _, .cons (ts := ts) (sig := restSig) b bs => do
    let tsE := listLit tyConst (ts.map tyExpr0)
    let sigE :=
      listLit listTyConst (restSig.map fun ts' => listLit tyConst (ts'.map tyExpr0))
    let bE ← spliceTFlat rsE b
    let bsE ← spliceTBlocks rsE bs
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.TBlocks.cons) #[rsE, tsE, sigE, bE, bsE]
end

/-- Reify `TFlatFn` to a kernel `Lean.Expr`. -/
def spliceTFlatFn (tf : TFlatFn) : Except String Lean.Expr := do
  let asE := listLit tyConst (tf.as.map tyExpr0)
  let rsE := listLit tyConst (tf.rs.map tyExpr0)
  let flatE ← spliceTFlat rsE tf.flat
  pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Frontend.C0.TFlatFn.mk)
    #[mkStrLit tf.name, asE, rsE, flatE]

mutual
/-- Collect direct call targets from `TFlat`. -/
partial def collectCallsTFlat {rs : List Ty} : TFlat rs → List String
  | .let_ _ k | .load _ _ k | .store _ _ k => collectCallsTFlat k
  | .call f _ _ k => f :: collectCallsTFlat k
  | .jnz _ t e => collectCallsTFlat t ++ collectCallsTFlat e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => []
  | .group bodies k => collectCallsTBlocks bodies ++ collectCallsTFlat k

/-- Collect direct call targets from `TBlocks`. -/
partial def collectCallsTBlocks {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → List String
  | _, .nil => []
  | _, .cons b bs => collectCallsTFlat b ++ collectCallsTBlocks bs
end

/-- Topologically sort `TFlatFn`s strictly callees-first via post-order DFS; fail on cycles. -/
partial def topoSortTFlat (tfs : List TFlatFn) : Except String (List TFlatFn) := do
  let byName : Std.HashMap String TFlatFn :=
    tfs.foldl (fun m tf => m.insert tf.name tf) {}
  let rec visit (nm : String) (visiting done : Std.HashSet String)
      (out : List TFlatFn) : Except String (Std.HashSet String × List TFlatFn) := do
    if done.contains nm then
      return (done, out)
    if visiting.contains nm then
      throw s!"cycle in lowered LCNF module involving '{nm}'"
    match byName[nm]? with
    | none => return (done, out)
    | some tf =>
      let visiting' := visiting.insert nm
      let mut d := done
      let mut acc := out
      for c in collectCallsTFlat tf.flat do
        if byName.contains c then
          if visiting'.contains c then
            throw s!"cycle in lowered LCNF: '{nm}' calls '{c}'"
          (d, acc) ← visit c visiting' d acc
      return (d.insert nm, acc ++ [tf])
  let mut done : Std.HashSet String := {}
  let mut out : List TFlatFn := []
  for tf in tfs do
    (done, out) ← visit tf.name {} done out
  return out

/-- Splices `lowerModule lcMod` (topologically sorted callees-first) as kernel `TFlatFn` defs. -/
elab "splice_lcnf_tflat! " modId:ident lcModT:term : command => do
  let ns ← getCurrNamespace
  let outNm := ns ++ modId.getId
  let lcE ← liftTermElabM <| Term.elabTerm lcModT
    (some (Lean.mkConst ``LeanQbe.T.LeanLCNF.LcModule))
  let lcMod ← liftTermElabM <|
    unsafe Meta.evalExpr LcModule (Lean.mkConst ``LeanQbe.T.LeanLCNF.LcModule) lcE
  let tfsRaw ← match lowerModule lcMod with
    | .ok tfs => pure tfs
    | .error e => throwError "splice_lcnf_tflat!: {e}"
  let tfs ← match topoSortTFlat tfsRaw with
    | .ok sorted => pure sorted
    | .error e => throwError "splice_lcnf_tflat!: {e}"
  for tf in tfs do
    if !tf.flat.wfCheck (pushTypes tf.as []) [] then
      throwError "splice_lcnf_tflat!: wfCheck failed for {tf.name}"
  let mut fnNames : List Name := []
  for (tf, i) in tfs.zip (List.range tfs.length) do
    let e ← match spliceTFlatFn tf with
      | .ok e => pure e
      | .error err => throwError "splice_lcnf_tflat!: {err}"
    let nm := outNm ++ Name.mkSimple s!"tf_{i}"
    liftCoreM <| addExposedDecl nm (Lean.mkConst ``TFlatFn) e (forceExpose := true)
    fnNames := fnNames ++ [nm]
  let tfsTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``TFlatFn)
  let tfsVal := (fnNames.map Lean.mkConst).foldr
    (fun e acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) (Lean.mkConst ``TFlatFn) e acc)
    (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``TFlatFn))
  liftCoreM <| addExposedDecl outNm tfsTy tfsVal (forceExpose := true)

/-- Compiled `meta` helper evaluating per-function compiled directive counts `(name, dirs)`. -/
def evalModuleDirCounts (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (fs : List Fn) : Except String (List (Sym × Nat)) := do
  let rec go (acc : List (SigEntry × Nat)) :
      List Fn → Except String (List (Sym × Nat))
    | [] => .ok []
    | f :: rest => do
      let (_, code, b, sig) ← evalOneFn I lt raBytes exits nX maxBound acc f
      let tl ← go ((sig, b) :: acc) rest
      .ok ((f.name, code.length) :: tl)
  go ext0 fs

/-- Materialize `def statsId : List (Sym × Nat) := [...]` in compiled native C `meta` code. -/
elab "eval_dir_stats! " statsId:ident targT:term:arg ltT:term:arg modT:term:arg
    extT:term:arg exitsT:term:arg : command => do
  let ns ← getCurrNamespace
  let outNm := ns ++ statsId.getId
  let counts ← liftTermElabM do
    let targE ← Term.elabTerm targT (some (Lean.mkConst ``LeanQbe.T.Target))
    let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
    let modE ← Term.elabTerm modT (some (Lean.mkConst ``LeanQbe.T.Module))
    let sigEntryNatTy :=
      mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
        (Lean.mkConst ``LeanQbe.T.SigEntry) (Lean.mkConst ``Nat)
    let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
    let listSymTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym)
    let ext0E ← Term.elabTerm extT (some listExtTy)
    let exitsE ← Term.elabTerm exitsT (some listSymTy)
    Term.synthesizeSyntheticMVarsNoPostponing
    let isaE := mkApp (Lean.mkConst ``LeanQbe.T.Target.toIsa) (← instantiateMVars targE)
    let frameE ← mkAppM ``LeanQbe.T.Isa.frame #[isaE]
    let raE ← mkAppM ``LeanQbe.T.FrameIsa.raBytes #[frameE]
    let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) (← instantiateMVars modE)
    let callE ← instantiateMVars <| mkAppN (Lean.mkConst ``evalModuleDirCounts)
      #[isaE, ← instantiateMVars ltE, raE, ← instantiateMVars ext0E,
        ← instantiateMVars exitsE, mkNatLit 64, mkNatLit 2048, fnsE]
    let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.Sym) (Lean.mkConst ``Nat)
    let listPairTy := mkApp (Lean.mkConst ``List [.zero]) pairTy
    let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero])
      (Lean.mkConst ``String) listPairTy
    let res ← unsafe Meta.evalExpr (Except String (List (Sym × Nat))) outTy callE
    match res with
    | .ok cs => pure cs
    | .error e => throwError "eval_dir_stats!: {e}"
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
    (Lean.mkConst ``LeanQbe.T.Sym) (Lean.mkConst ``Nat)
  let listPairTy := mkApp (Lean.mkConst ``List [.zero]) pairTy
  let litE := Lean.toExpr counts
  liftCoreM <| addExposedDecl outNm listPairTy litE (forceExpose := true)

end

end LeanQbe.T.Bootstrap0
