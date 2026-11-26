module

public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Frontend.C0.Elab
public import LeanQbe.T.Main
public meta import Lean
public meta import LeanQbe.T.LeanLCNF.Lower1
public meta import LeanQbe.T.Frontend.C0.Elab
public meta import LeanQbe.T.MainCertElab

/-!
# Topological Splicer for Lowered `LeanLCNF` Modules (`Bootstrap0`)

Provides the `splice_lcnf_tflat!` command elaborator used to materialize `lowerModule lcMod` into
exposed kernel `TFlatFn` definitions ordered strictly callees-first via post-order DFS topological
sort, feeding `LeanLRC.tflatFnsToFns` + `LeanLRC.tflatFnsToFns_wf` and `compile_linked_chunks!`.

The splice is *not trusted*: besides `<tfs>` (callees-first) the command emits
* `<tfs>_raw : List TFlatFn`, the same `tf_i` constants in `lowerModule`'s own order,
* `<tfs>_lower : lowerModule lcMod = .ok <tfs>_raw`, checked by the kernel by reduction
  (`Eq.refl`; `lowerModule` is total and free of `Std.HashMap`/`String.hash`), and
* `<tfs>_perm : <tfs>.Perm <tfs>_raw` (`reorderBy_perm`, the topological order as an index list).

`lcnf_lower_thm! <tfs> lcMod` emits `<tfs>_lower : lowerModule lcMod = .ok <tfs>` alone, for
splicers that keep `lowerModule`'s order (the cyclic/SCC demos).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bootstrap0

/-- `xs` reordered by the index list `idx` (out-of-range indices are dropped). -/
def reorderBy {α : Type} (idx : List Nat) (xs : List α) : List α :=
  idx.filterMap (xs[·]?)

theorem filterMap_getElem?_range {α : Type} :
    ∀ xs : List α, (List.range xs.length).filterMap (xs[·]?) = xs
  | [] => rfl
  | x :: xs => by
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    simpa [Function.comp_def] using filterMap_getElem?_range xs

/-- Reordering by a permutation of the positions is a permutation. -/
theorem reorderBy_perm {α : Type} {idx : List Nat} {xs ys : List α}
    (hidx : idx.Perm (List.range xs.length)) (h : reorderBy idx xs = ys) : ys.Perm xs := by
  subst h
  have := hidx.filterMap (xs[·]?)
  rwa [filterMap_getElem?_range] at this

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

/-- Reify `Frontend.C0.TFlatFn` to a kernel `Lean.Expr`. -/
def spliceTFlatFn (tf : Frontend.C0.TFlatFn) : Except String Lean.Expr := do
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

/-- Topologically sort `Frontend.C0.TFlatFn`s strictly callees-first via DFS; fail on cycles. -/
partial def topoSortTFlat (tfs : List Frontend.C0.TFlatFn) :
    Except String (List Frontend.C0.TFlatFn) := do
  let byName : Std.HashMap String Frontend.C0.TFlatFn :=
    tfs.foldl (fun m tf => m.insert tf.name tf) {}
  let rec visit (nm : String) (visiting done : Std.HashSet String)
      (out : List Frontend.C0.TFlatFn) :
      Except String (Std.HashSet String × List Frontend.C0.TFlatFn) := do
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
  let mut out : List Frontend.C0.TFlatFn := []
  for tf in tfs do
    (done, out) ← visit tf.name {} done out
  return out

/-- `List TFlatFn` type, and the list literal of the given `TFlatFn` constants. -/
def tflatFnListTy : Lean.Expr :=
  mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Frontend.C0.TFlatFn)

/-- The list literal of the given `TFlatFn` constants. -/
def tflatFnListLit (names : List Name) : Lean.Expr :=
  let c0TfConst := Lean.mkConst ``LeanQbe.T.Frontend.C0.TFlatFn
  (names.map Lean.mkConst).foldr
    (fun e acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) c0TfConst e acc)
    (mkApp (Lean.mkConst ``List.nil [.zero]) c0TfConst)

/-- Add `thmNm : lowerModule lcE = .ok rawE`, proved by `Eq.refl` and so checked by kernel
reduction of `lowerModule` alone (no elaborator, no compiled code in the trust base). -/
def addLowerThm (thmNm : Name) (lcE rawE : Lean.Expr) : CoreM Unit := do
  let exTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) tflatFnListTy
  let lhs := mkApp (Lean.mkConst ``LeanQbe.T.LeanLCNF.lowerModule) lcE
  let rhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero]) (Lean.mkConst ``String)
    tflatFnListTy rawE
  addDecl <| .thmDecl {
    name := thmNm, levelParams := []
    type := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) exTy lhs rhs
    value := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) exTy rhs }

/-- Add `thmNm : sortedE.Perm rawE` from `reorderBy idx rawE = sortedE` (`Eq.refl`) and
`idx.Perm (List.range rawE.length)` (`decide`), both checked by the kernel. -/
def addPermThm (thmNm : Name) (idx : List Nat) (sortedE rawE : Lean.Expr) : MetaM Unit := do
  let tfC := Lean.mkConst ``LeanQbe.T.Frontend.C0.TFlatFn
  let idxE := Lean.toExpr idx
  let rangeE := mkApp (Lean.mkConst ``List.range)
    (mkApp2 (Lean.mkConst ``List.length [.zero]) tfC rawE)
  let hidx ← mkDecideProof
    (mkApp3 (Lean.mkConst ``List.Perm [.zero]) (Lean.mkConst ``Nat) idxE rangeE)
  let hre := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) tflatFnListTy sortedE
  addDecl <| .thmDecl {
    name := thmNm, levelParams := []
    type := mkApp3 (Lean.mkConst ``List.Perm [.zero]) tfC sortedE rawE
    value := mkAppN (Lean.mkConst ``LeanQbe.T.Bootstrap0.reorderBy_perm)
      #[tfC, idxE, rawE, sortedE, hidx, hre] }

/-- Emits the kernel-checked `<tfs>_lower : lowerModule lcMod = .ok <tfs>` for an already spliced
`<tfs> : List TFlatFn` kept in `lowerModule`'s order. -/
elab "lcnf_lower_thm! " tfsId:ident lcModT:term : command => do
  let tfsNm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo tfsId
  let lcE ← liftTermElabM do
    let e ← Term.elabTerm lcModT (some (Lean.mkConst ``LeanQbe.T.LeanLCNF.LcModule))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  liftCoreM <| addLowerThm (tfsNm.appendAfter "_lower") lcE (Lean.mkConst tfsNm)

/-- Splices `lowerModule lcMod` (topologically sorted callees-first) as kernel `TFlatFn` defs,
with the kernel-checked `<tfs>_lower : lowerModule lcMod = .ok <tfs>_raw` and
`<tfs>_perm : <tfs>.Perm <tfs>_raw`. -/
elab "splice_lcnf_tflat! " modId:ident lcModT:term : command => do
  let ns ← getCurrNamespace
  let outNm := ns ++ modId.getId
  let lcE ← liftTermElabM do
    let e ← Term.elabTerm lcModT (some (Lean.mkConst ``LeanQbe.T.LeanLCNF.LcModule))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
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
  let c0TfConst := Lean.mkConst ``LeanQbe.T.Frontend.C0.TFlatFn
  for (tf, i) in tfs.zip (List.range tfs.length) do
    let e ← match spliceTFlatFn tf with
      | .ok e => pure e
      | .error err => throwError "splice_lcnf_tflat!: {err}"
    let nm := outNm ++ Name.mkSimple s!"tf_{i}"
    liftCoreM <| addExposedDecl nm c0TfConst e (forceExpose := true)
    fnNames := fnNames ++ [nm]
  liftCoreM <| addExposedDecl outNm tflatFnListTy (tflatFnListLit fnNames) (forceExpose := true)
  -- Kernel-checked lowering relation: `<tfs>_raw` lists the same constants in `lowerModule`'s
  -- order (mangled symbols are unique: `lowerModule` checks `symsNodup`).
  let posIn (xs : List Frontend.C0.TFlatFn) (nm : String) : Nat :=
    (xs.findIdx? (·.name == nm)).getD 0
  let rawNames := tfsRaw.map fun tf => fnNames.getD (posIn tfs tf.name) outNm
  let rawNm := outNm.appendAfter "_raw"
  liftCoreM <| addExposedDecl rawNm tflatFnListTy (tflatFnListLit rawNames) (forceExpose := true)
  liftCoreM <| addLowerThm (outNm.appendAfter "_lower") lcE (Lean.mkConst rawNm)
  liftTermElabM <| addPermThm (outNm.appendAfter "_perm") (tfs.map fun tf => posIn tfsRaw tf.name)
    (Lean.mkConst outNm) (Lean.mkConst rawNm)

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
