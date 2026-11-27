module

public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.SepTree
public import LeanQbe.T.Logic.SlabChain
public meta import Lean.Elab.Command
public meta import LeanQbe.T.Logic.C0Step
public meta import LeanQbe.T.Logic.SepTree
public meta import LeanQbe.T.Logic.SlabChain

/-!
# Typed `CommandElabM` Slab Layout & Lens Macros (`c0_slab_layout!`, `c0_lens!`)

Zero-string-templating, `withReducible`-safe replacement for manual C0 arena boilerplate:

1. **`C0Lens` & `c0_lens!`:** Lawful per-field lenses (`C0Lens.comp`, `C0Lens.set_list`,
   `AgreesExcept` integration) plus `c0_lens!` generating per-field `C0Lens` definitions and
   `LengthsOk.upd_*` / `LengthsOk.set_*` preservation one-liners for flat or nested sliced
   states (e.g. `core`/`scratch`).
2. **`c0_slab_layout!` (Mode A — existing sliced `Cfg` / `State`):** Generates `*HdrWords`,
   balanced `SepTree`-backed `*Tree` / `*Mem`, `O(log K)` `Rest` / `focus_*` / `unfocus_*`
   (zero `ecancel`), `@[scoped c0_load]` / `@[scoped c0_store]` header & array lemmas with
   concrete `BitVec.ofNat 64 $strideLit` (plus `i8` direct-byte forms and `_off` sub-buffer
   accessors), and optional `SlabChain.to_region`-backed `*_to_region`.
3. **`c0_slab_layout! def` (Mode B — full sliced slab synthesis):** Generates sliced `<Pfx>Cfg`
   (with contiguous chained `p*` pointers, `usedBytes`, `SizeOk`, `slack`), `<Pfx>State` (with
   `Nat`-backed and `BitVec 64` scalars + typed arrays), `<Pfx>State.LengthsOk` + `C0Lens` +
   `LengthsOk.{upd,set}_*`, balanced `SepTree`-backed `<Pfx>Mem` with integrated `align8` padding,
   `focus_*` / `unfocus_*`, `@[scoped c0_load]` / `@[scoped c0_store]`, and **zero-`ecancel`**
   `<Pfx>_to_region` via `SlabChain.balancedTree_to_region_eq`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std Std.ExtHashMap

/-! ## 1. Lawful Lenses (`C0Lens`) & `LengthsOk` Preservation Tactic -/

/-- Lawful lens into a C0 state record `σ` focusing field `α`. -/
structure C0Lens (σ α : Type) where
  get : σ → α
  set : σ → α → σ
  get_set : ∀ s v, get (set s v) = v
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s v w, set (set s v) w = set s w

namespace C0Lens

/-- Apply a pure function to the focused field. -/
def modify {σ α : Type} (l : C0Lens σ α) (f : α → α) (s : σ) : σ :=
  l.set s (f (l.get s))

/-- Compose two lenses (`outer` into a sub-record such as `s.core`, `inner` into its field). -/
def comp {σ τ α : Type} (outer : C0Lens σ τ) (inner : C0Lens τ α) : C0Lens σ α where
  get s := inner.get (outer.get s)
  set s v := outer.set s (inner.set (outer.get s) v)
  get_set s v := by rw [outer.get_set, inner.get_set]
  set_get s := by rw [inner.set_get, outer.set_get]
  set_set s v w := by rw [outer.get_set, inner.set_set, outer.set_set]

/-- Update element `i` of a list-valued field. -/
def set_list {σ α : Type} (l : C0Lens σ (List α)) (s : σ) (i : Nat) (v : α) : σ :=
  l.set s ((l.get s).set i v)

theorem length_set_list {σ α : Type} (l : C0Lens σ (List α)) (s : σ) (i : Nat) (v : α) :
    (l.get (l.set_list s i v)).length = (l.get s).length := by
  simp only [set_list, l.get_set, List.length_set]

theorem getElem?_set_list_self {σ α : Type} (l : C0Lens σ (List α)) (s : σ) {i : Nat} (v : α)
    (hi : i < (l.get s).length) :
    (l.get (l.set_list s i v))[i]? = some v := by
  simp only [set_list, l.get_set, List.getElem?_set_self hi]

theorem getElem?_set_list_ne {σ α : Type} (l : C0Lens σ (List α)) (s : σ) {i j : Nat} (v : α)
    (hne : i ≠ j) :
    (l.get (l.set_list s i v))[j]? = (l.get s)[j]? := by
  simp only [set_list, l.get_set, List.getElem?_set_ne hne]

/-- Updating a field covered by `mask` satisfies `AgreesExcept mask`. -/
theorem agreesExcept_set {σ α : Type} (l : C0Lens σ α) (mask : σ → σ) (s : σ) (v : α)
    (hm : ∀ t x, mask (l.set t x) = mask t := by intro _ _; rfl) :
    AgreesExcept mask s (l.set s v) :=
  hm s v

/-- Project an unmasked field across `AgreesExcept mask`. -/
theorem get_of_agreesExcept {σ α : Type} (l : C0Lens σ α) {mask : σ → σ} {s s' : σ}
    (h : AgreesExcept mask s s')
    (hm : ∀ t, l.get (mask t) = l.get t := by intro _; rfl) :
    l.get s' = l.get s :=
  h.get l.get hm

end C0Lens

/-! ## 2. Recursive `LengthsOk` Preservation Tactic (`c0_lengths_ok`) -/

section LengthsTactic
open Lean Meta Elab Tactic

private meta def tryCloseWithEq (g : MVarId) (hEq : FVarId) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    let hId := mkIdent (← hEq.getUserName)
    evalTactic (← `(tactic| (dsimp only; rw [$hId:ident]; assumption)))
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

private meta def tryCloseWithSet (g : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| (dsimp only; simp only [List.length_set]; assumption)))
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

private meta partial def solveLengthsOkAux (fuel : Nat) (hEq? : Option FVarId) : TacticM Unit := do
  if fuel == 0 then throwError "c0_lengths_ok: recursion limit reached"
  let g ← getMainGoal
  if ← g.isAssigned then return
  g.withContext do
    let closedByAssump ← try g.assumption; pure true catch _ => pure false
    if closedByAssump then return
    if let some hEq := hEq? then
      if ← tryCloseWithEq g hEq then return
    if ← tryCloseWithSet g then return
    let ty ← instantiateMVars (← g.getType)
    let some headNm := ty.getAppFn.constName?
      | throwError "c0_lengths_ok: cannot discharge goal{indentExpr ty}"
    let mut matchHyp? : Option FVarId := none
    for d in (← getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      if dty.getAppFn.constName? == some headNm then
        matchHyp? := some d.fvarId
        break
    let some hFVar := matchHyp?
      | throwError "c0_lengths_ok: no matching `{headNm}` hypothesis for{indentExpr ty}"
    let hId := mkIdent (← hFVar.getUserName)
    evalTactic (← `(tactic| (cases $hId:ident; constructor)))
    let subGoals ← getUnsolvedGoals
    let mut rem : List MVarId := []
    for sg in subGoals do
      if ← sg.isAssigned then continue
      setGoals [sg]
      solveLengthsOkAux (fuel - 1) hEq?
      rem := rem ++ (← getUnsolvedGoals)
    setGoals rem

/-- Close a flat or arbitrarily nested `LengthsOk` preservation goal after an array/scalar update
without invoking `grind` or `simp_all`. -/
elab "c0_lengths_ok" hEq?:(ident)? : tactic => do
  let hEqFVar? ← match hEq? with
    | some id =>
      withMainContext do
        match (← getLCtx).findFromUserName? id.getId with
        | some d => pure (some d.fvarId)
        | none => throwError "c0_lengths_ok: unknown hypothesis `{id.getId}`"
    | none => pure none
  solveLengthsOkAux 16 hEqFVar?

end LengthsTactic

/-! ## 3. Shared Typed Syntax Helpers (`CommandElabM`) -/

section SlabElabHelpers
open Lean Elab Command Meta

private meta def elemStrideNat (elTy : Term) : CommandElabM Nat := do
  let nm := elTy.raw.getId.eraseMacroScopes
  match nm.componentsRev with
  | .str .anonymous "i8" :: _  => return 1
  | .str .anonymous "i16" :: _ => return 2
  | .str .anonymous "i32" :: _ => return 4
  | .str .anonymous "i64" :: _ => return 8
  | _ => throwErrorAt elTy
    "c0_slab_layout!: expected scalar element type i8, i16, i32, or i64"

private meta def elemValTyStx (elTy : Term) : CommandElabM Term := do
  match ← elemStrideNat elTy with
  | 1 => `(BitVec 8)
  | 2 => `(BitVec 16)
  | 4 => `(BitVec 32)
  | _ => `(BitVec 64)

private meta def capFirst (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: cs => String.ofList (c.toUpper :: cs)

private meta def mkPtrFieldName (arrNm : Name) : Name :=
  Name.mkSimple ("p" ++ capFirst arrNm.toString)

/-- Compute binary path of leaf `idx` in a balanced `SepTree` of `n` leaves (`O(log n)` depth). -/
meta partial def balancedPath (idx n : Nat) : List Bool :=
  if n ≤ 1 then []
  else
    let mid := n / 2
    if idx < mid then false :: balancedPath idx mid
    else true :: balancedPath (idx - mid) (n - mid)

/-- Build a balanced `SepTree` syntax expression from leaf terms. -/
private meta partial def mkBalancedTreeStx (leaves : Array Term) : CommandElabM Term := do
  if leaves.size == 0 then
    throwError "c0_slab_layout!: empty leaf list"
  else if leaves.size == 1 then
    `(SepTree.leaf $(leaves[0]!))
  else
    let mid := leaves.size / 2
    let l ← mkBalancedTreeStx (leaves.extract 0 mid)
    let r ← mkBalancedTreeStx (leaves.extract mid leaves.size)
    `(SepTree.node $l $r)

/-- Render a `List Bool` path as syntax `false :: true :: []`. -/
private meta def mkPathStx (path : List Bool) : CommandElabM Term := do
  let mut acc : Term ← `(term| [])
  for b in path.reverse do
    let bt : Term ← if b then `(term| true) else `(term| false)
    acc ← `(term| $bt :: $acc)
  return acc

/-- Render an `Array Term` as a `List` term via `::`. -/
private meta def mkListStx (xs : Array Term) : CommandElabM Term := do
  let mut acc : Term ← `(term| [])
  for x in xs.reverse do
    acc ← `(term| $x :: $acc)
  return acc

/-- Render a `Nat` sum `t₀ + t₁ + ...` left-associated (returns `0` on empty). -/
private meta def mkSumStx (ts : Array Term) : CommandElabM Term := do
  if ts.isEmpty then `(term| 0)
  else
    let mut acc := ts[0]!
    for i in [1:ts.size] do
      acc ← `(term| $acc + $(ts[i]!))
    return acc

/-- Resolve a `LengthsOk` head constant so generated dot-notation lemmas land in its namespace. -/
private meta def resolveLengthsPrefix (lenPred : Term) : CommandElabM (Option Name) := do
  try
    let nm ← liftCoreM <| resolveGlobalConstNoOverload lenPred
    return some nm
  catch _ =>
    return none

private meta def mkScopedDeclIdent (nsOpt : Option Name) (fallbackPfx leaf : String) :
    Ident :=
  match nsOpt with
  | some ns => mkIdent (`_root_ ++ ns ++ Name.mkSimple leaf)
  | none => mkIdent (Name.mkSimple (fallbackPfx ++ "_" ++ leaf))

private meta structure LensFieldSpec where
  nm : Name
  isArr : Bool
  preservesLen : Bool
  ty : Term
  getExpr : Term
  setFn : Term

private meta def emitLensDecls (pfxStr : String) (sId : Ident) (sTy : Term)
    (lenOpt : Option (Ident × Term × Term)) (fields : Array LensFieldSpec) :
    CommandElabM Unit := do
  let lenNsOpt ← match lenOpt with
    | some (_, _, lenPred) => resolveLengthsPrefix lenPred
    | none => pure none
  for f in fields do
    let lensNm := mkIdent (Name.mkSimple (pfxStr ++ "Lens_" ++ f.nm.toString))
    let lensValTy ← if f.isArr then `(List $(f.ty)) else pure f.ty
    elabCommand (← `(command|
      def $lensNm:ident : C0Lens $sTy $lensValTy where
        get := fun $sId => $(f.getExpr)
        set := fun $sId v => $(f.setFn) v
        get_set _ _ := rfl
        set_get _ := rfl
        set_set _ _ _ := rfl))
    if let some (cId, cTy, lenPred) := lenOpt then
      if f.isArr then
        let updNm := mkScopedDeclIdent lenNsOpt (pfxStr ++ "LengthsOk") ("upd_" ++ f.nm.toString)
        let setNm := mkScopedDeclIdent lenNsOpt (pfxStr ++ "LengthsOk") ("set_" ++ f.nm.toString)
        elabCommand (← `(command|
          theorem $updNm:ident {$cId : $cTy} {$sId : $sTy}
              (hlen : $lenPred $cId $sId) {xs' : List $(f.ty)}
              (hxs : xs'.length = ($(f.getExpr)).length) :
              $lenPred $cId ($(f.setFn) xs') := by
            c0_lengths_ok hxs))
        elabCommand (← `(command|
          theorem $setNm:ident {$cId : $cTy} {$sId : $sTy}
              (hlen : $lenPred $cId $sId) (i : Nat) (v : $(f.ty)) :
              $lenPred $cId ($(f.setFn) (($(f.getExpr)).set i v)) :=
            $updNm hlen (List.length_set ..)))
      else if f.preservesLen then
        let setNm := mkScopedDeclIdent lenNsOpt (pfxStr ++ "LengthsOk") ("set_" ++ f.nm.toString)
        elabCommand (← `(command|
          theorem $setNm:ident {$cId : $cTy} {$sId : $sTy}
              (hlen : $lenPred $cId $sId) (v : $(f.ty)) :
              $lenPred $cId ($(f.setFn) v) := by
            c0_lengths_ok))

private meta structure HdrFieldSpec where
  nm : Name
  valTerm : Term
  updOpt : Option Term
  deriving Inhabited

private meta inductive ArrPadKind where
  | exact
  | align8
  | custom (stride : Term)
  deriving Inhabited

private meta structure ArrEntrySpec where
  nm : Name
  elTy : Term
  ptrField : Ident
  listExpr : Term
  updFn : Term
  lenOpt : Option (Term × ArrPadKind)
  inlinePad : Bool := false
  deriving Inhabited

/-- Core emitter for header/array `SepTree`, `focus_*`/`unfocus_*`, and `withReducible`-safe
`@[scoped c0_load]` / `@[scoped c0_store]` lemmas. -/
private meta def emitSlabCore (pfxStr : String) (cId : Ident) (cTy : Term)
    (sId : Ident) (sTy : Term) (hdrBase : Term) (extraLeafOpt : Option Term)
    (hdrInfos : Array HdrFieldSpec) (arrInfos : Array ArrEntrySpec) :
    CommandElabM (Ident × Ident × Ident × Ident) := do
  -- 1. Emit `<pfx>HdrWords` and `<pfx>HdrWords_length`
  let hdrWords := hdrInfos.map (·.valTerm)
  let hdrWordsId := mkIdent (Name.mkSimple (pfxStr ++ "HdrWords"))
  let hdrLenId := mkIdent (Name.mkSimple (pfxStr ++ "HdrWords_length"))
  let nHdr := Syntax.mkNumLit (toString hdrWords.size)
  let hdrListStx ← mkListStx hdrWords
  elabCommand (← `(command|
    def $hdrWordsId:ident ($cId : $cTy) ($sId : $sTy) : List (BitVec 64) :=
      $hdrListStx))
  elabCommand (← `(command|
    theorem $hdrLenId:ident ($cId : $cTy) ($sId : $sTy) :
        ($hdrWordsId $cId $sId).length = $nHdr := rfl))
  -- 2. Build balanced `SepTree`
  let mut leaves : Array Term := #[]
  leaves := leaves.push (← `(array64 $hdrBase ($hdrWordsId $cId $sId)))
  for ae in arrInfos do
    let pAcc := mkIdent (cId.getId ++ ae.ptrField.getId)
    let strideNat ← elemStrideNat ae.elTy
    let strideLit := Syntax.mkNumLit (toString strideNat)
    if ae.inlinePad then
      match ae.lenOpt with
      | some (cnt, .align8) =>
        let actStx ← `(term| $strideLit * $cnt)
        leaves := leaves.push (← `(
          array (t := $(ae.elTy)) $pAcc $(ae.listExpr) ⋆
            region ($pAcc + BitVec.ofNat 64 $actStx) (align8 $actStx - $actStx)))
      | some (cnt, .custom st) =>
        let actStx ← `(term| $strideLit * $cnt)
        leaves := leaves.push (← `(
          array (t := $(ae.elTy)) $pAcc $(ae.listExpr) ⋆
            region ($pAcc + BitVec.ofNat 64 $actStx) ($st - $actStx)))
      | _ =>
        leaves := leaves.push (← `(array (t := $(ae.elTy)) $pAcc $(ae.listExpr)))
    else
      leaves := leaves.push (← `(array (t := $(ae.elTy)) $pAcc $(ae.listExpr)))
  if let some padLeaf := extraLeafOpt then
    leaves := leaves.push padLeaf
  let totalLeaves := leaves.size
  let treeStx ← mkBalancedTreeStx leaves
  let treeId := mkIdent (Name.mkSimple (pfxStr ++ "Tree"))
  let memId := mkIdent (Name.mkSimple (pfxStr ++ "Mem"))
  elabCommand (← `(command|
    def $treeId:ident ($cId : $cTy) ($sId : $sTy) : SepTree := $treeStx))
  elabCommand (← `(command|
    def $memId:ident ($cId : $cTy) ($sId : $sTy) : Mem 64 → Prop :=
      ($treeId $cId $sId).eval))
  -- 3. Emit `O(1)` header `@[scoped c0_load]` / `@[scoped c0_store]` theorems
  let hdrPath ← mkPathStx (balancedPath 0 totalLeaves)
  for idx in [:hdrInfos.size] do
    let hf := hdrInfos[idx]!
    let offBytes := 8 * idx
    let offLit := Syntax.mkNumLit (toString offBytes)
    let idxLit := Syntax.mkNumLit (toString idx)
    let loadNm := mkIdent (Name.mkSimple ("load_" ++ pfxStr ++ "_" ++ hf.nm.toString))
    let addrStx ← if offBytes == 0 then `($hdrBase) else `($hdrBase + $offLit)
    if offBytes == 0 then
      elabCommand (← `(command|
        @[scoped c0_load] theorem $loadNm:ident {$cId : $cTy} {$sId : $sTy}
            {R : Mem 64 → Prop} {m : Mem 64} (hm : ($memId $cId $sId ⋆ R) m) :
            loadVal m i64 $addrStx = some $(hf.valTerm) :=
          sepTree_hdr_get_zero (t := $treeId $cId $sId) (p := $hdrPath) rfl
            (($hdrLenId $cId $sId).symm ▸ (by decide : 0 < $nHdr)) hm))
    else
      elabCommand (← `(command|
        @[scoped c0_load] theorem $loadNm:ident {$cId : $cTy} {$sId : $sTy}
            {R : Mem 64 → Prop} {m : Mem 64} (hm : ($memId $cId $sId ⋆ R) m) :
            loadVal m i64 $addrStx = some $(hf.valTerm) :=
          sepTree_hdr_get (t := $treeId $cId $sId) (p := $hdrPath) rfl $idxLit
            (($hdrLenId $cId $sId).symm ▸ (by decide : $idxLit < $nHdr)) hm))
    if let some updFn := hf.updOpt then
      let storeNm := mkIdent (Name.mkSimple ("store_" ++ pfxStr ++ "_" ++ hf.nm.toString))
      let hdrWordsTerm : Term := hdrWordsId
      if offBytes == 0 then
        elabCommand (← `(command|
          @[scoped c0_store] theorem $storeNm:ident {$cId : $cTy} {$sId : $sTy}
              {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
              (hm : ($memId $cId $sId ⋆ R) m) :
              storeOk m i64 $addrStx ∧
                ($memId $cId ($updFn v) ⋆ R) (storeMem m i64 $addrStx v) := by
            have hv : $hdrWordsId $cId ($updFn v) = ($hdrWordsId $cId $sId).set 0 v := by
              simp only [$hdrWordsTerm:term, List.set, bv64_ofNat_toNat]
            exact sepTree_hdr_put_zero (t := $treeId $cId $sId) (p := $hdrPath) rfl
              (($hdrLenId $cId $sId).symm ▸ (by decide : 0 < $nHdr)) v hv rfl hm))
      else
        elabCommand (← `(command|
          @[scoped c0_store] theorem $storeNm:ident {$cId : $cTy} {$sId : $sTy}
              {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
              (hm : ($memId $cId $sId ⋆ R) m) :
              storeOk m i64 $addrStx ∧
                ($memId $cId ($updFn v) ⋆ R) (storeMem m i64 $addrStx v) := by
            have hv : $hdrWordsId $cId ($updFn v) = ($hdrWordsId $cId $sId).set $idxLit v := by
              simp only [$hdrWordsTerm:term, List.set, bv64_ofNat_toNat]
            exact sepTree_hdr_put (t := $treeId $cId $sId) (p := $hdrPath) rfl $idxLit
              (($hdrLenId $cId $sId).symm ▸ (by decide : $idxLit < $nHdr)) v hv rfl hm))
  -- 4. Emit `O(log K)` `Rest`, `focus_*`, `unfocus_*`, and `withReducible`-safe array accessors
  for idx in [:arrInfos.size] do
    let ae := arrInfos[idx]!
    let path ← mkPathStx (balancedPath (idx + 1) totalLeaves)
    let pAcc := mkIdent (cId.getId ++ ae.ptrField.getId)
    let strideNat ← elemStrideNat ae.elTy
    let strideLit := Syntax.mkNumLit (toString strideNat)
    let nmStr := ae.nm.toString
    let restNm := mkIdent (Name.mkSimple (pfxStr ++ "Rest_" ++ nmStr))
    let focusNm := mkIdent (Name.mkSimple ("focus_" ++ pfxStr ++ "_" ++ nmStr))
    let unfocusNm := mkIdent (Name.mkSimple ("unfocus_" ++ pfxStr ++ "_" ++ nmStr))
    let loadNatNm := mkIdent (Name.mkSimple ("load_" ++ pfxStr ++ "_" ++ nmStr ++ "_nat"))
    let storeNatNm := mkIdent (Name.mkSimple ("store_" ++ pfxStr ++ "_" ++ nmStr ++ "_nat"))
    let loadBvNm := mkIdent (Name.mkSimple ("load_" ++ pfxStr ++ "_" ++ nmStr))
    let loadU32Nm := mkIdent (Name.mkSimple ("load_" ++ pfxStr ++ "_" ++ nmStr ++ "_u32"))
    let loadOffNm := mkIdent (Name.mkSimple ("load_" ++ pfxStr ++ "_" ++ nmStr ++ "_off"))
    let storeOffNm := mkIdent (Name.mkSimple ("store_" ++ pfxStr ++ "_" ++ nmStr ++ "_off"))
    let storeBvNm := mkIdent (Name.mkSimple ("store_" ++ pfxStr ++ "_" ++ nmStr))
    let storeU32Nm := mkIdent (Name.mkSimple ("store_" ++ pfxStr ++ "_" ++ nmStr ++ "_u32"))
    let isPaddedLeaf := ae.inlinePad && match ae.lenOpt with
      | some (_, .align8) | some (_, .custom _) => true
      | _ => false
    if isPaddedLeaf then
      let padExpr ← match ae.lenOpt with
        | some (cnt, .align8) =>
          let actStx ← `(term| $strideLit * $cnt)
          `(region ($pAcc + BitVec.ofNat 64 $actStx) (align8 $actStx - $actStx))
        | some (cnt, .custom st) =>
          let actStx ← `(term| $strideLit * $cnt)
          `(region ($pAcc + BitVec.ofNat 64 $actStx) ($st - $actStx))
        | _ => `(emp)
      elabCommand (← `(command|
        def $restNm:ident ($cId : $cTy) ($sId : $sTy) : Mem 64 → Prop :=
          $padExpr ⋆ ($treeId $cId $sId).rest $path))
      elabCommand (← `(command|
        theorem $focusNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            (hm : ($memId $cId $sId ⋆ R) m) :
            (array (t := $(ae.elTy)) $pAcc $(ae.listExpr) ⋆ ($restNm $cId $sId ⋆ R)) m :=
          sepTree_arr_pad_focus_rest (t := $treeId $cId $sId) (p := $path) rfl hm))
      elabCommand (← `(command|
        theorem $unfocusNm:ident {$cId : $cTy} {$sId : $sTy} {xs' : List (Val $(ae.elTy))}
            {R : Mem 64 → Prop} {m : Mem 64}
            (hm : (array (t := $(ae.elTy)) $pAcc xs' ⋆ ($restNm $cId $sId ⋆ R)) m) :
            ($memId $cId ($(ae.updFn) xs') ⋆ R) m :=
          sepTree_arr_pad_unfocus_rest_eq (t := $treeId $cId $sId) (p := $path) rfl hm))
      elabCommand (← `(command|
        theorem $loadNatNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            {i : Nat} (hi : i < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
            loadVal m $(ae.elTy) ($pAcc + BitVec.ofNat 64 (($(ae.elTy)).bytes * i)) =
              some (($(ae.listExpr))[i]'hi) :=
          sepTree_arr_pad_get (t := $treeId $cId $sId) (p := $path) rfl (by decide) hi hm))
      elabCommand (← `(command|
        theorem $storeNatNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            (v : Val $(ae.elTy)) {i : Nat} (hi : i < ($(ae.listExpr)).length)
            (hm : ($memId $cId $sId ⋆ R) m) :
            storeOk m $(ae.elTy) ($pAcc + BitVec.ofNat 64 (($(ae.elTy)).bytes * i)) ∧
              ($memId $cId ($(ae.updFn) (($(ae.listExpr)).set i v)) ⋆ R)
                (storeMem m $(ae.elTy) ($pAcc + BitVec.ofNat 64 (($(ae.elTy)).bytes * i)) v) :=
          sepTree_arr_pad_put (t := $treeId $cId $sId) (p := $path) rfl (by decide) v hi rfl hm))
      elabCommand (← `(command|
        theorem $loadOffNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            (k : Nat) {off : BitVec 64}
            (hoff : off = BitVec.ofNat 64 (($(ae.elTy)).bytes * k))
            {i : BitVec 64} (hi : k + i.toNat < ($(ae.listExpr)).length)
            (hm : ($memId $cId $sId ⋆ R) m) :
            loadVal m $(ae.elTy) ($pAcc + off + i * BitVec.ofNat 64 $strideLit) =
              some (($(ae.listExpr))[k + i.toNat]'hi) := by
          rw [show BitVec.ofNat 64 $strideLit = BitVec.ofNat 64 ($(ae.elTy)).bytes from rfl]
          exact sepTree_arr_pad_get_off (t := $treeId $cId $sId) (p := $path) rfl (by decide)
            k hoff hi hm))
      elabCommand (← `(command|
        theorem $storeOffNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            (k : Nat) {off : BitVec 64}
            (hoff : off = BitVec.ofNat 64 (($(ae.elTy)).bytes * k))
            (v : Val $(ae.elTy)) {i : BitVec 64} (hi : k + i.toNat < ($(ae.listExpr)).length)
            (hm : ($memId $cId $sId ⋆ R) m) :
            storeOk m $(ae.elTy) ($pAcc + off + i * BitVec.ofNat 64 $strideLit) ∧
              ($memId $cId ($(ae.updFn) (($(ae.listExpr)).set (k + i.toNat) v)) ⋆ R)
                (storeMem m $(ae.elTy) ($pAcc + off + i * BitVec.ofNat 64 $strideLit) v) := by
          rw [show BitVec.ofNat 64 $strideLit = BitVec.ofNat 64 ($(ae.elTy)).bytes from rfl]
          exact sepTree_arr_pad_put_off (t := $treeId $cId $sId) (p := $path) rfl (by decide)
            k hoff v hi rfl hm))
    else
      elabCommand (← `(command|
        def $restNm:ident ($cId : $cTy) ($sId : $sTy) : Mem 64 → Prop :=
          ($treeId $cId $sId).rest $path))
      elabCommand (← `(command|
        theorem $focusNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            (hm : ($memId $cId $sId ⋆ R) m) :
            (array (t := $(ae.elTy)) $pAcc $(ae.listExpr) ⋆ ($restNm $cId $sId ⋆ R)) m :=
          SepTree.focus (t := $treeId $cId $sId) $path hm))
      elabCommand (← `(command|
        theorem $unfocusNm:ident {$cId : $cTy} {$sId : $sTy} {xs' : List (Val $(ae.elTy))}
            {R : Mem 64 → Prop} {m : Mem 64}
            (hm : (array (t := $(ae.elTy)) $pAcc xs' ⋆ ($restNm $cId $sId ⋆ R)) m) :
            ($memId $cId ($(ae.updFn) xs') ⋆ R) m :=
          SepTree.unfocus_eq (t := $treeId $cId $sId) $path rfl hm))
      elabCommand (← `(command|
        theorem $loadNatNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            {i : Nat} (hi : i < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
            loadVal m $(ae.elTy) ($pAcc + BitVec.ofNat 64 (($(ae.elTy)).bytes * i)) =
              some (($(ae.listExpr))[i]'hi) :=
          sepTree_arr_get (t := $treeId $cId $sId) (p := $path) rfl (by decide) hi hm))
      elabCommand (← `(command|
        theorem $storeNatNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            (v : Val $(ae.elTy)) {i : Nat} (hi : i < ($(ae.listExpr)).length)
            (hm : ($memId $cId $sId ⋆ R) m) :
            storeOk m $(ae.elTy) ($pAcc + BitVec.ofNat 64 (($(ae.elTy)).bytes * i)) ∧
              ($memId $cId ($(ae.updFn) (($(ae.listExpr)).set i v)) ⋆ R)
                (storeMem m $(ae.elTy) ($pAcc + BitVec.ofNat 64 (($(ae.elTy)).bytes * i)) v) :=
          sepTree_arr_put (t := $treeId $cId $sId) (p := $path) rfl (by decide) v hi rfl hm))
      elabCommand (← `(command|
        theorem $loadOffNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            (k : Nat) {off : BitVec 64}
            (hoff : off = BitVec.ofNat 64 (($(ae.elTy)).bytes * k))
            {i : BitVec 64} (hi : k + i.toNat < ($(ae.listExpr)).length)
            (hm : ($memId $cId $sId ⋆ R) m) :
            loadVal m $(ae.elTy) ($pAcc + off + i * BitVec.ofNat 64 $strideLit) =
              some (($(ae.listExpr))[k + i.toNat]'hi) := by
          rw [show BitVec.ofNat 64 $strideLit = BitVec.ofNat 64 ($(ae.elTy)).bytes from rfl]
          exact sepTree_arr_get_off (t := $treeId $cId $sId) (p := $path) rfl (by decide)
            k hoff hi hm))
      elabCommand (← `(command|
        theorem $storeOffNm:ident {$cId : $cTy} {$sId : $sTy} {R : Mem 64 → Prop} {m : Mem 64}
            (k : Nat) {off : BitVec 64}
            (hoff : off = BitVec.ofNat 64 (($(ae.elTy)).bytes * k))
            (v : Val $(ae.elTy)) {i : BitVec 64} (hi : k + i.toNat < ($(ae.listExpr)).length)
            (hm : ($memId $cId $sId ⋆ R) m) :
            storeOk m $(ae.elTy) ($pAcc + off + i * BitVec.ofNat 64 $strideLit) ∧
              ($memId $cId ($(ae.updFn) (($(ae.listExpr)).set (k + i.toNat) v)) ⋆ R)
                (storeMem m $(ae.elTy) ($pAcc + off + i * BitVec.ofNat 64 $strideLit) v) := by
          rw [show BitVec.ofNat 64 $strideLit = BitVec.ofNat 64 ($(ae.elTy)).bytes from rfl]
          exact sepTree_arr_put_off (t := $treeId $cId $sId) (p := $path) rfl (by decide)
            k hoff v hi rfl hm))
    -- Concrete `BitVec.ofNat 64 $strideLit` (`withReducible`-safe for `C0Step.c0_steps`)
    elabCommand (← `(command|
      @[scoped c0_load] theorem $loadBvNm:ident {$cId : $cTy} {$sId : $sTy}
          {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
          (hi : i.toNat < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
          loadVal m $(ae.elTy) ($pAcc + i * BitVec.ofNat 64 $strideLit) =
            some (($(ae.listExpr))[i.toNat]'hi) := by
        rw [show BitVec.ofNat 64 $strideLit = BitVec.ofNat 64 ($(ae.elTy)).bytes from rfl,
          c0_mul_ofNat]
        exact $loadNatNm hi hm))
    elabCommand (← `(command|
      @[scoped c0_load] theorem $loadU32Nm:ident {$cId : $cTy} {$sId : $sTy}
          {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 32}
          (hi : i.toNat < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
          loadVal m $(ae.elTy) ($pAcc + i.setWidth 64 * BitVec.ofNat 64 $strideLit) =
            some (($(ae.listExpr))[i.toNat]'hi) := by
        rw [show BitVec.ofNat 64 $strideLit = BitVec.ofNat 64 ($(ae.elTy)).bytes from rfl,
          c0_u32_mul_ofNat]
        exact $loadNatNm hi hm))
    elabCommand (← `(command|
      @[scoped c0_store] theorem $storeBvNm:ident {$cId : $cTy} {$sId : $sTy}
          {R : Mem 64 → Prop} {m : Mem 64} (v : Val $(ae.elTy)) {i : BitVec 64}
          (hi : i.toNat < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
          storeOk m $(ae.elTy) ($pAcc + i * BitVec.ofNat 64 $strideLit) ∧
            ($memId $cId ($(ae.updFn) (($(ae.listExpr)).set i.toNat v)) ⋆ R)
              (storeMem m $(ae.elTy) ($pAcc + i * BitVec.ofNat 64 $strideLit) v) := by
        rw [show BitVec.ofNat 64 $strideLit = BitVec.ofNat 64 ($(ae.elTy)).bytes from rfl,
          c0_mul_ofNat]
        exact $storeNatNm v hi hm))
    elabCommand (← `(command|
      @[scoped c0_store] theorem $storeU32Nm:ident {$cId : $cTy} {$sId : $sTy}
          {R : Mem 64 → Prop} {m : Mem 64} (v : Val $(ae.elTy)) {i : BitVec 32}
          (hi : i.toNat < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
          storeOk m $(ae.elTy) ($pAcc + i.setWidth 64 * BitVec.ofNat 64 $strideLit) ∧
            ($memId $cId ($(ae.updFn) (($(ae.listExpr)).set i.toNat v)) ⋆ R)
              (storeMem m $(ae.elTy) ($pAcc + i.setWidth 64 * BitVec.ofNat 64 $strideLit) v) := by
        rw [show BitVec.ofNat 64 $strideLit = BitVec.ofNat 64 ($(ae.elTy)).bytes from rfl,
          c0_u32_mul_ofNat]
        exact $storeNatNm v hi hm))
    -- Direct byte-indexing forms (`p + i`, `p + i.setWidth 64`) for `i8` arrays
    if strideNat == 1 then
      let loadByteNm := mkIdent (Name.mkSimple ("load_" ++ pfxStr ++ "_" ++ nmStr ++ "_byte"))
      let loadByteU32Nm :=
        mkIdent (Name.mkSimple ("load_" ++ pfxStr ++ "_" ++ nmStr ++ "_byte_u32"))
      let storeByteNm := mkIdent (Name.mkSimple ("store_" ++ pfxStr ++ "_" ++ nmStr ++ "_byte"))
      let storeByteU32Nm :=
        mkIdent (Name.mkSimple ("store_" ++ pfxStr ++ "_" ++ nmStr ++ "_byte_u32"))
      elabCommand (← `(command|
        @[scoped c0_load] theorem $loadByteNm:ident {$cId : $cTy} {$sId : $sTy}
            {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
            (hi : i.toNat < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
            loadVal m i8 ($pAcc + i) = some (($(ae.listExpr))[i.toNat]'hi) := by
          have h := $loadNatNm hi hm
          simpa only [show i8.bytes = 1 from rfl, Nat.one_mul, bv64_ofNat_toNat] using h))
      elabCommand (← `(command|
        @[scoped c0_load] theorem $loadByteU32Nm:ident {$cId : $cTy} {$sId : $sTy}
            {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 32}
            (hi : i.toNat < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
            loadVal m i8 ($pAcc + i.setWidth 64) = some (($(ae.listExpr))[i.toNat]'hi) := by
          have h := $loadNatNm hi hm
          simpa only [show i8.bytes = 1 from rfl, Nat.one_mul,
            ← sepTree_u32_setWidth_eq] using h))
      elabCommand (← `(command|
        @[scoped c0_store] theorem $storeByteNm:ident {$cId : $cTy} {$sId : $sTy}
            {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 8) {i : BitVec 64}
            (hi : i.toNat < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
            storeOk m i8 ($pAcc + i) ∧
              ($memId $cId ($(ae.updFn) (($(ae.listExpr)).set i.toNat v)) ⋆ R)
                (storeMem m i8 ($pAcc + i) v) := by
          have h := $storeNatNm v hi hm
          simpa only [show i8.bytes = 1 from rfl, Nat.one_mul, bv64_ofNat_toNat] using h))
      elabCommand (← `(command|
        @[scoped c0_store] theorem $storeByteU32Nm:ident {$cId : $cTy} {$sId : $sTy}
            {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 8) {i : BitVec 32}
            (hi : i.toNat < ($(ae.listExpr)).length) (hm : ($memId $cId $sId ⋆ R) m) :
            storeOk m i8 ($pAcc + i.setWidth 64) ∧
              ($memId $cId ($(ae.updFn) (($(ae.listExpr)).set i.toNat v)) ⋆ R)
                (storeMem m i8 ($pAcc + i.setWidth 64) v) := by
          have h := $storeNatNm v hi hm
          simpa only [show i8.bytes = 1 from rfl, Nat.one_mul,
            ← sepTree_u32_setWidth_eq] using h))
  return (hdrWordsId, hdrLenId, treeId, memId)

end SlabElabHelpers

/-! ## 4. `c0_lens!` Command Macro (Typed `CommandElabM`, Zero String Parsing) -/

declare_syntax_cat c0_lens_field

syntax ident ident ":" term ":=" term "|" term : c0_lens_field

/-- Generate per-field `C0Lens` definitions and `LengthsOk.{upd,set}_*` preservation theorems
for any flat or nested sliced state record. -/
syntax "c0_lens!" ident "(" ident ":" term ")"
    (&"lengths" "(" ident ":" term ")" ident)?
    "{" c0_lens_field,* "}" : command

section LensElab
open Lean Elab Command

elab_rules : command
  | `(c0_lens! $pfx:ident ($sId:ident : $sTy:term)
        $[lengths ($cId:ident : $cTy:term) $lenPred:ident]?
        { $fields:c0_lens_field,* }) => do
    let pfxStr := pfx.getId.toString
    let lenOpt := match cId, cTy, lenPred with
      | some cId, some cTy, some lenPred => some (cId, cTy, (lenPred : Term))
      | _, _, _ => none
    let mut parsed : Array LensFieldSpec := #[]
    for f in fields.getElems do
      match f with
      | `(c0_lens_field| $kw:ident $nm:ident : $ty:term := $g:term | $u:term) =>
        match kw.getId with
        | `scalar =>
          parsed := parsed.push {
            nm := nm.getId, isArr := false, preservesLen := true,
            ty := ty, getExpr := g, setFn := u }
        | `bscalar =>
          parsed := parsed.push {
            nm := nm.getId, isArr := false, preservesLen := false,
            ty := ty, getExpr := g, setFn := u }
        | `arr =>
          parsed := parsed.push {
            nm := nm.getId, isArr := true, preservesLen := true,
            ty := ty, getExpr := g, setFn := u }
        | other =>
          throwErrorAt kw "c0_lens!: expected `scalar`, `bscalar`, or `arr`, got `{other}`"
      | _ => throwError "c0_lens!: invalid lens field"
    emitLensDecls pfxStr sId sTy lenOpt parsed

end LensElab

/-! ## 5. `c0_slab_layout!` Command Macro (Mode A & Mode B) -/

declare_syntax_cat slab_hdr_field
declare_syntax_cat slab_arr_entry
declare_syntax_cat slab_def_param
declare_syntax_cat slab_def_scalar
declare_syntax_cat slab_def_arr

syntax ident ident ":=" term : slab_hdr_field
syntax ident ident ":=" term "|" term : slab_hdr_field

syntax ident ":" term "|" ident ":=" term "|" term
  (";" &"len" term ("|" &"align8")?)? : slab_arr_entry
syntax ident ":" term "|" ident ":=" term "|" term
  ";" &"len" term "|" &"stride" term : slab_arr_entry

syntax ident ":" term : slab_def_param
syntax ident ident : slab_def_scalar
syntax ident ":" term "|" &"len" term ("|" &"align8")? : slab_def_arr

/-- Mode A: generate `SepTree`-backed `*Mem`, `focus_*`/`unfocus_*`, `withReducible`-safe
`@[scoped c0_load]`/`@[scoped c0_store]` accessors, and optional `*_to_region` for existing
sliced `(c : Cfg)` and `(s : State)` records. -/
syntax "c0_slab_layout!" ident
    "(" ident ":" term ")" "(" ident ":" term ")"
    "(" &"hdrBase" ":=" term ")"
    ("(" &"withPad" ":=" term ")")?
    &"header" "{" slab_hdr_field,* "}"
    &"arrays" "{" slab_arr_entry,* "}"
    (&"to_region" "(" ident ":" term ")"
      "{" &"total" ":=" term
          ("," &"slack" ":=" term)?
          "," &"fit" ":=" term
          ("," &"bounds" ":=" "[" term,* "]")?
          ("," &"unfold" ":=" "[" ident,* "]")? "}")? : command

/-- Mode B: synthesize sliced `<Pfx>Cfg`, `<Pfx>State`, `<Pfx>State.LengthsOk`, `C0Lens` +
`LengthsOk.{upd,set}_*`, balanced `SepTree`-backed `<Pfx>Mem`, `focus_*`/`unfocus_*`,
`withReducible`-safe `@[scoped c0_load]`/`@[scoped c0_store]`, and **zero-`ecancel`**
`<Pfx>_to_region` via `SlabChain.balancedTree_to_region_eq`. -/
syntax "c0_slab_layout!" "def" ident "(" ident ")"
    &"params" "{" slab_def_param,* "}"
    &"scalars" "{" slab_def_scalar,* "}"
    &"arrays" "{" slab_def_arr,* "}" : command

section SlabElab
open Lean Elab Command

elab_rules : command
  | `(c0_slab_layout! $pfx:ident
        ($cId:ident : $cTy:term) ($sId:ident : $sTy:term)
        (hdrBase := $hdrBase:term)
        $[(withPad := $padOpt:term)]?
        header { $hfields:slab_hdr_field,* }
        arrays { $aentries:slab_arr_entry,* }
        $[to_region ($hlenId?:ident : $hlenTy?:term)
          { total := $tot?:term $[, slack := $sl?:term]? , fit := $ft?:term
            $[, bounds := [$bs?:term,*]]? $[, unfold := [$us?:ident,*]]? }]?) => do
    let pfxStr := pfx.getId.toString
    let mut hdrInfos : Array HdrFieldSpec := #[]
    for hf in hfields.getElems do
      match hf with
      | `(slab_hdr_field| $kw:ident $nm:ident := $val:term) =>
        match kw.getId with
        | `hconst =>
          hdrInfos := hdrInfos.push { nm := nm.getId, valTerm := val, updOpt := none }
        | `hconst_nat =>
          let bvVal ← `(BitVec.ofNat 64 $val)
          hdrInfos := hdrInfos.push { nm := nm.getId, valTerm := bvVal, updOpt := none }
        | other =>
          throwErrorAt kw "c0_slab_layout!: expected `hconst` or `hconst_nat`, got `{other}`"
      | `(slab_hdr_field| $kw:ident $nm:ident := $val:term | $upd:term) =>
        match kw.getId with
        | `hmut =>
          hdrInfos := hdrInfos.push { nm := nm.getId, valTerm := val, updOpt := some upd }
        | `hmut_nat =>
          let bvVal ← `(BitVec.ofNat 64 $val)
          let bvUpd ← `(fun v : BitVec 64 => ($upd) v.toNat)
          hdrInfos := hdrInfos.push { nm := nm.getId, valTerm := bvVal, updOpt := some bvUpd }
        | other =>
          throwErrorAt kw "c0_slab_layout!: expected `hmut` or `hmut_nat`, got `{other}`"
      | _ => throwError "c0_slab_layout!: invalid header field"
    let mut arrInfos : Array ArrEntrySpec := #[]
    for ae in aentries.getElems do
      match ae with
      | `(slab_arr_entry| $nm:ident : $elTy:term | $ptrField:ident := $listExpr:term | $updFn:term
          ; len $cnt:term | align8) =>
        arrInfos := arrInfos.push {
          nm := nm.getId, elTy, ptrField, listExpr, updFn,
          lenOpt := some (cnt, .align8) }
      | `(slab_arr_entry| $nm:ident : $elTy:term | $ptrField:ident := $listExpr:term | $updFn:term
          ; len $cnt:term | stride $st:term) =>
        arrInfos := arrInfos.push {
          nm := nm.getId, elTy, ptrField, listExpr, updFn,
          lenOpt := some (cnt, .custom st) }
      | `(slab_arr_entry| $nm:ident : $elTy:term | $ptrField:ident := $listExpr:term | $updFn:term
          ; len $cnt:term) =>
        arrInfos := arrInfos.push {
          nm := nm.getId, elTy, ptrField, listExpr, updFn,
          lenOpt := some (cnt, .exact) }
      | `(slab_arr_entry| $nm:ident : $elTy:term | $ptrField:ident := $listExpr:term |
          $updFn:term) =>
        arrInfos := arrInfos.push {
          nm := nm.getId, elTy, ptrField, listExpr, updFn, lenOpt := none }
      | _ => throwError "c0_slab_layout!: invalid array entry"
    let (hdrWordsId, _, treeId, memId) ←
      emitSlabCore pfxStr cId cTy sId sTy hdrBase padOpt hdrInfos arrInfos
    -- Optional `to_region` emission via `SlabChain.to_region_eq`
    if let (some hlenId, some hlenTy, some totalTerm, some fitTerm) :=
        (hlenId?, hlenTy?, tot?, ft?) then
      let slackOpt : Option Term := sl?.join
      let boundTerms : Array Term := match bs? with
        | some (some arr) => arr.getElems
        | _ => #[]
      let unfoldIds : Array Ident := match us? with
        | some (some arr) => arr.getElems
        | _ => #[]
      let nHdr := Syntax.mkNumLit (toString hdrInfos.size)
      let mut segStxs : Array Term := #[]
      segStxs := segStxs.push (← `(SlabSeg.ofArray64 ($hdrWordsId $cId $sId) $nHdr rfl))
      for ae in arrInfos do
        let some (cnt, padKind) := ae.lenOpt
          | throwError "c0_slab_layout!: `to_region` requires `; len ...` on array `{ae.nm}`"
        let strideNat ← elemStrideNat ae.elTy
        let strideLit := Syntax.mkNumLit (toString strideNat)
        let actStx ← `(term| $strideLit * $cnt)
        let hactProof ← `(term| by
          rw [show ($(ae.elTy)).bytes = $strideLit from rfl]
          cases $hlenId:ident
          omega)
        match padKind with
        | .exact =>
          let sExact ← `(SlabSeg.ofArrayExact $(ae.elTy) $(ae.listExpr) $actStx $hactProof)
          segStxs := segStxs.push sExact
        | .align8 =>
          let sAlign ← `(SlabSeg.ofArrayAlign8 $(ae.elTy) $(ae.listExpr) $actStx $hactProof)
          segStxs := segStxs.push sAlign
        | .custom st =>
          let hleProof ← `(term| by omega)
          segStxs := segStxs.push
            (← `(SlabSeg.ofArray $(ae.elTy) $(ae.listExpr) $actStx $st $hactProof $hleProof))
      if let some sl := slackOpt then
        segStxs := segStxs.push (← `(SlabSeg.ofRegion $sl))
      let segsList ← mkListStx segStxs
      let cTyName := cTy.raw.getId.eraseMacroScopes
      let mut ptrUnfolds : Array Term := #[]
      for ae in arrInfos do
        ptrUnfolds := ptrUnfolds.push (mkIdent (cTyName ++ ae.ptrField.getId))
      let extraUnfolds : Array Term := unfoldIds.map fun id => (id : Term)
      let allUnfolds := ptrUnfolds ++ extraUnfolds
      let memTerm : Term := memId
      let treeTerm : Term := treeId
      let mut boundTacs : Array (TSyntax `tactic) := #[]
      for bt in boundTerms do
        boundTacs := boundTacs.push (← `(tactic| have := $bt))
      let toRegNm := mkIdent (Name.mkSimple (pfxStr ++ "_to_region"))
      elabCommand (← `(command|
        theorem $toRegNm:ident ($cId : $cTy) ($sId : $sTy) ($hlenId : $hlenTy)
            {m : Mem 64} (hm : $memId $cId $sId m) : region $hdrBase $totalTerm m := by
          $[$boundTacs]*
          let segs : List SlabSeg := $segsList
          have htot : SlabChain.totalBytes segs = $totalTerm := by
            simp only [segs, SlabChain.totalBytes, SlabSeg.ofArray64, SlabSeg.ofArray,
              SlabSeg.ofArrayExact, SlabSeg.ofArrayAlign8, SlabSeg.ofRegion,
              Nat.one_mul, $[$allUnfolds:term],*]
            omega
          have hchain : SlabChain.eval $hdrBase segs m := by
            simp only [segs, SlabChain.eval, SlabSeg.ofArray64, SlabSeg.ofArray,
              SlabSeg.ofArrayExact, SlabSeg.ofArrayAlign8, SlabSeg.ofRegion,
              Nat.sub_self, region_zero, sep_emp, Nat.reduceMul, Nat.one_mul]
            simp only [$memTerm:term, $treeTerm:term, SepTree.eval, $[$allUnfolds:term],*] at hm
            ecancel
          exact SlabChain.to_region_eq htot $fitTerm hchain))

  | `(c0_slab_layout! def $pfx:ident ($cId:ident)
        params { $pfields:slab_def_param,* }
        scalars { $sfields:slab_def_scalar,* }
        arrays { $aentries:slab_def_arr,* }) => do
    let pfxStr := pfx.getId.toString
    let cfgId := mkIdent (Name.mkSimple (pfxStr ++ "Cfg"))
    let stateId := mkIdent (Name.mkSimple (pfxStr ++ "State"))
    let sId := mkIdent `s
    -- 1. Parse params, scalars, arrays
    let mut paramSpecs : Array (Ident × Term) := #[]
    for pf in pfields.getElems do
      match pf with
      | `(slab_def_param| $nm:ident : $ty:term) => paramSpecs := paramSpecs.push (nm, ty)
      | _ => throwError "c0_slab_layout! def: invalid param field"
    let mut scalarSpecs : Array (Ident × Bool) := #[]
    for sf in sfields.getElems do
      match sf with
      | `(slab_def_scalar| $kw:ident $nm:ident) =>
        match kw.getId with
        | `nat => scalarSpecs := scalarSpecs.push (nm, true)
        | `bv64 => scalarSpecs := scalarSpecs.push (nm, false)
        | other => throwErrorAt kw "c0_slab_layout! def: expected `nat` or `bv64`, got `{other}`"
      | _ => throwError "c0_slab_layout! def: invalid scalar field"
    let mut arrSpecs : Array (Ident × Term × Term × Bool) := #[]
    for ae in aentries.getElems do
      match ae with
      | `(slab_def_arr| $nm:ident : $elTy:term | len $cnt:term | align8) =>
        arrSpecs := arrSpecs.push (nm, elTy, cnt, true)
      | `(slab_def_arr| $nm:ident : $elTy:term | len $cnt:term) =>
        arrSpecs := arrSpecs.push (nm, elTy, cnt, false)
      | _ => throwError "c0_slab_layout! def: invalid array entry"
    -- 2. Emit `structure <Pfx>Cfg`
    let mut cfgFields : Array (TSyntax ``Lean.Parser.Command.structSimpleBinder) := #[]
    cfgFields := cfgFields.push (← `(Lean.Parser.Command.structSimpleBinder| hdr : BitVec 64))
    cfgFields := cfgFields.push (← `(Lean.Parser.Command.structSimpleBinder| avail : Nat))
    for (nm, ty) in paramSpecs do
      cfgFields := cfgFields.push (← `(Lean.Parser.Command.structSimpleBinder| $nm:ident : $ty))
    cfgFields := cfgFields.push (← `(Lean.Parser.Command.structSimpleBinder| hfit : avail ≤ 2 ^ 64))
    elabCommand (← `(command|
      structure $cfgId:ident where
        $[$cfgFields:structSimpleBinder]*))
    -- 3. Emit contiguous pointer chain, `usedBytes`, `SizeOk`, `pSlack`, `slack` on `<Pfx>Cfg`
    let nHdrCount := paramSpecs.size + scalarSpecs.size + arrSpecs.size
    let nHdrLit := Syntax.mkNumLit (toString nHdrCount)
    let hdrBytesTerm ← `(term| 8 * $nHdrLit)
    let mut prevPtr ← `(term| $(mkIdent (cId.getId ++ `hdr)))
    let mut prevStride := hdrBytesTerm
    let mut strideTerms : Array Term := #[hdrBytesTerm]
    let mut ptrNames : Array Ident := #[]
    for (nm, elTy, cnt, isAlign8) in arrSpecs do
      let pNm := mkPtrFieldName nm.getId
      let pDefId := mkIdent (cfgId.getId ++ pNm)
      elabCommand (← `(command|
        def $pDefId:ident ($cId : $cfgId) : BitVec 64 :=
          $prevPtr + BitVec.ofNat 64 $prevStride))
      ptrNames := ptrNames.push (mkIdent pNm)
      let strideNat ← elemStrideNat elTy
      let strideLit := Syntax.mkNumLit (toString strideNat)
      let actStx ← `(term| $strideLit * $cnt)
      let segStride ← if isAlign8 then `(term| align8 $actStx) else pure actStx
      strideTerms := strideTerms.push segStride
      prevPtr ← `(term| $(mkIdent (cId.getId ++ pNm)))
      prevStride := segStride
    let pSlackDef := mkIdent (cfgId.getId ++ `pSlack)
    elabCommand (← `(command|
      def $pSlackDef:ident ($cId : $cfgId) : BitVec 64 :=
        $prevPtr + BitVec.ofNat 64 $prevStride))
    let usedBytesDef := mkIdent (cfgId.getId ++ `usedBytes)
    let sizeOkDef := mkIdent (cfgId.getId ++ `SizeOk)
    let slackDef := mkIdent (cfgId.getId ++ `slack)
    let usedSum ← mkSumStx strideTerms
    elabCommand (← `(command|
      def $usedBytesDef:ident ($cId : $cfgId) : Nat := $usedSum))
    elabCommand (← `(command|
      def $sizeOkDef:ident ($cId : $cfgId) : Prop :=
        $(mkIdent (cId.getId ++ `usedBytes)) ≤ $(mkIdent (cId.getId ++ `avail))))
    elabCommand (← `(command|
      def $slackDef:ident ($cId : $cfgId) : Nat :=
        $(mkIdent (cId.getId ++ `avail)) - $(mkIdent (cId.getId ++ `usedBytes))))
    -- 4. Emit `structure <Pfx>State` & `structure <Pfx>State.LengthsOk`
    let mut stateFields : Array (TSyntax ``Lean.Parser.Command.structSimpleBinder) := #[]
    for (nm, isNat) in scalarSpecs do
      let ty ← if isNat then `(Nat) else `(BitVec 64)
      stateFields := stateFields.push (← `(Lean.Parser.Command.structSimpleBinder| $nm:ident : $ty))
    for (nm, elTy, _, _) in arrSpecs do
      let vTy ← elemValTyStx elTy
      stateFields := stateFields.push
        (← `(Lean.Parser.Command.structSimpleBinder| $nm:ident : List $vTy))
    elabCommand (← `(command|
      structure $stateId:ident where
        $[$stateFields:structSimpleBinder]*))
    let lenOkId := mkIdent (stateId.getId ++ `LengthsOk)
    let mut lenFields : Array (TSyntax ``Lean.Parser.Command.structSimpleBinder) := #[]
    for (nm, _, cnt, _) in arrSpecs do
      let lfNm := mkIdent (Name.mkSimple (nm.getId.toString ++ "_len"))
      let sAcc := mkIdent (sId.getId ++ nm.getId)
      lenFields := lenFields.push
        (← `(Lean.Parser.Command.structSimpleBinder| $lfNm:ident : ($sAcc).length = $cnt))
    elabCommand (← `(command|
      structure $lenOkId:ident ($cId : $cfgId) ($sId : $stateId) : Prop where
        $[$lenFields:structSimpleBinder]*))
    -- 5. Emit `C0Lens` + `LengthsOk.{upd,set}_*`
    let mut lensFields : Array LensFieldSpec := #[]
    for (nm, isNat) in scalarSpecs do
      let ty ← if isNat then `(Nat) else `(BitVec 64)
      let gExpr ← `(term| $(mkIdent (sId.getId ++ nm.getId)))
      let uFn ← `(term| fun v => { $sId:ident with $nm:ident := v })
      lensFields := lensFields.push
        { nm := nm.getId, isArr := false, preservesLen := true, ty, getExpr := gExpr, setFn := uFn }
    for (nm, elTy, _, _) in arrSpecs do
      let vTy ← elemValTyStx elTy
      let gExpr ← `(term| $(mkIdent (sId.getId ++ nm.getId)))
      let uFn ← `(term| fun xs => { $sId:ident with $nm:ident := xs })
      lensFields := lensFields.push
        { nm := nm.getId, isArr := true, preservesLen := true, ty := vTy,
          getExpr := gExpr, setFn := uFn }
    emitLensDecls pfxStr sId (← `($stateId)) (some (cId, ← `($cfgId), ← `($lenOkId))) lensFields
    -- 6. Emit `SepTree`-backed `*Mem`, `focus_*`/`unfocus_*`, `@[scoped c0_load/store]`
    let mut hdrInfos : Array HdrFieldSpec := #[]
    for (nm, _) in paramSpecs do
      let cAcc := mkIdent (cId.getId ++ nm.getId)
      hdrInfos := hdrInfos.push
        { nm := nm.getId, valTerm := ← `(BitVec.ofNat 64 $cAcc), updOpt := none }
    for (nm, isNat) in scalarSpecs do
      let sAcc := mkIdent (sId.getId ++ nm.getId)
      if isNat then
        hdrInfos := hdrInfos.push {
          nm := nm.getId,
          valTerm := ← `(BitVec.ofNat 64 $sAcc),
          updOpt := some (← `(fun v : BitVec 64 => { $sId:ident with $nm:ident := v.toNat })) }
      else
        hdrInfos := hdrInfos.push {
          nm := nm.getId,
          valTerm := ← `($sAcc),
          updOpt := some (← `(fun v : BitVec 64 => { $sId:ident with $nm:ident := v })) }
    for idx in [:arrSpecs.size] do
      let pNm := ptrNames[idx]!
      let cAcc := mkIdent (cId.getId ++ pNm.getId)
      hdrInfos := hdrInfos.push { nm := pNm.getId, valTerm := ← `($cAcc), updOpt := none }
    let mut arrInfos : Array ArrEntrySpec := #[]
    for idx in [:arrSpecs.size] do
      let (nm, elTy, cnt, isAlign8) := arrSpecs[idx]!
      let pNm := ptrNames[idx]!
      let sAcc := mkIdent (sId.getId ++ nm.getId)
      let updFn ← `(fun xs => { $sId:ident with $nm:ident := xs })
      arrInfos := arrInfos.push {
        nm := nm.getId, elTy, ptrField := pNm, listExpr := ← `($sAcc), updFn,
        lenOpt := some (cnt, if isAlign8 then .align8 else .exact),
        inlinePad := true }
    let hdrBase ← `(term| $(mkIdent (cId.getId ++ `hdr)))
    let slackLeaf ← `(region $(mkIdent (cId.getId ++ `pSlack)) $(mkIdent (cId.getId ++ `slack)))
    let (hdrWordsId, _, treeId, memId) ←
      emitSlabCore pfxStr cId (← `($cfgId)) sId (← `($stateId)) hdrBase (some slackLeaf)
        hdrInfos arrInfos
    -- 7. Emit ZERO-`ecancel` `<Pfx>_to_region` via `SlabChain.balancedTree_to_region_eq`
    let hlenId := mkIdent `hlen
    let mut segStxs : Array Term := #[]
    segStxs := segStxs.push (← `(SlabSeg.ofArray64 ($hdrWordsId $cId $sId) $nHdrLit rfl))
    for (nm, elTy, cnt, isAlign8) in arrSpecs do
      let strideNat ← elemStrideNat elTy
      let strideLit := Syntax.mkNumLit (toString strideNat)
      let actStx ← `(term| $strideLit * $cnt)
      let sAcc := mkIdent (sId.getId ++ nm.getId)
      let lfAcc : Term := mkIdent (hlenId.getId ++ Name.mkSimple (nm.getId.toString ++ "_len"))
      let hact ← `(term| by rw [show ($elTy).bytes = $strideLit from rfl, $lfAcc:term])
      if isAlign8 then
        segStxs := segStxs.push (← `(SlabSeg.ofArrayAlign8 $elTy $sAcc $actStx $hact))
      else
        segStxs := segStxs.push (← `(SlabSeg.ofArrayExact $elTy $sAcc $actStx $hact))
    segStxs := segStxs.push (← `(SlabSeg.ofRegion $(mkIdent (cId.getId ++ `slack))))
    let segsList ← mkListStx segStxs
    let toRegNm := mkIdent (Name.mkSimple (pfxStr ++ "_to_region"))
    let sizeOkAcc := mkIdent (cId.getId ++ `SizeOk)
    let hfitAcc := mkIdent (cId.getId ++ `hfit)
    let availAcc := mkIdent (cId.getId ++ `avail)
    let slackTerm : Term := slackDef
    let usedBytesTerm : Term := usedBytesDef
    let treeTerm : Term := treeId
    let mut ptrTerms : Array Term := #[]
    for pNm in ptrNames do
      ptrTerms := ptrTerms.push (mkIdent (cfgId.getId ++ pNm.getId))
    ptrTerms := ptrTerms.push (pSlackDef : Term)
    elabCommand (← `(command|
      theorem $toRegNm:ident ($cId : $cfgId) ($sId : $stateId)
          (hsize : $sizeOkAcc) ($hlenId : $lenOkId $cId $sId) {m : Mem 64}
          (hm : $memId $cId $sId m) : region $hdrBase $availAcc m := by
        let segs : List SlabSeg := $segsList
        have htot : SlabChain.totalBytes segs = $availAcc := by
          unfold $sizeOkDef:ident $usedBytesDef:ident at hsize
          simp only [segs, SlabChain.totalBytes, SlabSeg.ofArray64, SlabSeg.ofArray,
            SlabSeg.ofArrayExact, SlabSeg.ofArrayAlign8, SlabSeg.ofRegion,
            $slackTerm:term, $usedBytesTerm:term]
          omega
        have htree : SlabChain.balancedTree (SlabChain.addrList $hdrBase segs) =
            $treeId $cId $sId := by
          simp only [segs, $treeTerm:term, SlabChain.balancedTree, SlabChain.balancedTreeAux,
            SlabChain.addrList, List.length_cons, List.length_nil, List.take_succ_cons,
            List.take_zero, List.drop_succ_cons, List.drop_zero, Nat.reduceAdd, Nat.reduceDiv,
            SlabSeg.ofArray64, SlabSeg.ofArray, SlabSeg.ofArrayExact, SlabSeg.ofArrayAlign8,
            SlabSeg.ofRegion, $[$ptrTerms:term],*]
        unfold $memId:ident at hm
        rw [← htree] at hm
        exact SlabChain.balancedTree_to_region_eq htot $hfitAcc hm))

end SlabElab

end LeanQbe.T
