module

public import BvDecideQbe.Cegar
public import Lean.Elab.Tactic.BVDecide
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Pre-Inlining DAG Extraction & 64-Pattern Simulation Discovery (`E0 / H5a` Core)

Core untrusted discovery front end for `bv_cut_qbe`:
1. Low-level `BitVec`/`Nat`/`Bool` expression and literal inspection helpers.
2. **Pre-inlining DAG extraction (`P1-3`):** Inspects `let`-bindings and `h : x = e` local
   hypotheses BEFORE `bv_normalize` inlines them, topologically breaking any cycles and
   retaining all non-defining side-condition hypotheses (`a < 100#32`, `x ≠ 0`, etc.).
3. **Word-level simulation discovery:** Evaluates reflected `BitVec`/`Bool` subexpressions
   across deterministic 64-bit corner + random patterns (filtered by reflected side conditions),
   bailing out cleanly on opaque atoms or tiny goals and detecting probable CEXs early.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Std.Tactic.BVDecide

/-! ## 1. Low-Level Expression Inspection & Literal Helpers -/

partial def getNatLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | .const ``Nat.zero _ => some 0
  | .app (.const ``Nat.succ _) inner => (getNatLit? inner).map (· + 1)
  | .app (.app (.app (.const ``OfNat.ofNat _) ty) val) _ =>
    if ty.consumeMData.isConstOf ``Nat then getNatLit? val else none
  | _ => none

def getBitVecWidth? (ty : Expr) : MetaM (Option Nat) := do
  let ty := (← instantiateMVars ty).consumeMData
  match_expr ty with
  | BitVec wExpr =>
    if let some w := getNatLit? wExpr then
      return some w
    let wWhnf ← whnf wExpr
    return getNatLit? wWhnf
  | _ => return none

def getBitVecLit? (e : Expr) : Option (Σ w, BitVec w) :=
  match e.consumeMData with
  | .app (.app (.const ``BitVec.ofNat _) wExpr) nExpr => do
    let w ← getNatLit? wExpr
    let n ← getNatLit? nExpr
    return ⟨w, BitVec.ofNat w n⟩
  | .app (.app (.app (.const ``OfNat.ofNat _) ty) nExpr) _ =>
    match ty.consumeMData with
    | .app (.const ``BitVec _) wExpr => do
      let w ← getNatLit? wExpr
      let n ← getNatLit? nExpr
      return ⟨w, BitVec.ofNat w n⟩
    | _ => none
  | _ => none

def getBoolLit? (e : Expr) : Option Bool :=
  match e.consumeMData with
  | .const ``Bool.true _ => some true
  | .const ``Bool.false _ => some false
  | _ => none

def mkBitVecTy (w : Nat) : Expr :=
  mkApp (mkConst ``BitVec) (mkNatLit w)

/-! ## 2. Pre-Inlining DAG Extraction (`P1-3`) -/

structure DefInfo where
  fvarId : FVarId
  width : Nat
  rhs : Expr
  eqProof : Expr
  isLet : Bool
  hypFVarId? : Option FVarId
  deriving Inhabited

structure DefGraph where
  defs : Std.HashMap FVarId DefInfo
  topoOrder : Array FVarId
  depth : Std.HashMap FVarId Nat
  sideHyps : Array FVarId
  deriving Inhabited

def collectExprFVars (e : Expr) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds

def exprContainsFVar (e : Expr) (target : FVarId) : Bool :=
  (collectExprFVars e).contains target

def liftTargetLets (mvarId : MVarId) : MetaM MVarId := do
  let mut cur := mvarId
  let mut steps := 0
  while steps < 256 do
    steps := steps + 1
    let progress ← cur.withContext do
      let ty := (← instantiateMVars (← cur.getType)).consumeMData
      if ty.isForall || ty.isLet then
        let (_, next) ← cur.intro1P
        return some next
      let some (eqTy, lhs, rhs) := ty.eq? | return none
      if let .letE n t v b nondep := lhs.consumeMData then
        let u ← getLevel eqTy
        let eqBody := mkApp3 (mkConst ``Eq [u]) eqTy b rhs
        let lifted := Expr.letE n t v eqBody nondep
        let changed ← cur.change lifted (checkDefEq := true)
        let (_, next) ← changed.intro1P
        return some next
      if let .letE n t v b nondep := rhs.consumeMData then
        let u ← getLevel eqTy
        let eqBody := mkApp3 (mkConst ``Eq [u]) eqTy lhs b
        let lifted := Expr.letE n t v eqBody nondep
        let changed ← cur.change lifted (checkDefEq := true)
        let (_, next) ← changed.intro1P
        return some next
      return none
    match progress with
    | some next => cur := next
    | none => break
  return cur

/-- Extract a cycle-free pre-inlining definition DAG from `LCtx` (`let`-bindings and
`h : x = e` / `h : e = x` `BitVec` equalities), keeping all remaining `Prop` hypotheses in
`sideHyps` so cone-relevant side conditions are never dropped. -/
def extractDefGraph (mvarId : MVarId) : MetaM DefGraph :=
  mvarId.withContext do
    let lctx ← getLCtx
    let mut rawDefs : Std.HashMap FVarId DefInfo := {}
    let mut defHypSet : Std.HashSet FVarId := {}
    let mut orderedVars : Array FVarId := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      if let some val := ldecl.value? then
        if let some w ← getBitVecWidth? ldecl.type then
          let val ← instantiateMVars val
          if !exprContainsFVar val ldecl.fvarId then
            rawDefs := rawDefs.insert ldecl.fvarId {
              fvarId := ldecl.fvarId
              width := w
              rhs := val
              eqProof := ← mkEqRefl (mkFVar ldecl.fvarId)
              isLet := true
              hypFVarId? := none
            }
            orderedVars := orderedVars.push ldecl.fvarId
    for ldecl in lctx do
      if ldecl.isImplementationDetail || ldecl.value?.isSome then continue
      let ty := (← instantiateMVars ldecl.type).consumeMData
      let some (eqTy, a, b) := ty.eq? | continue
      let some w ← getBitVecWidth? eqTy | continue
      let a := a.consumeMData
      let b := b.consumeMData
      if let .fvar fv := a then
        if !rawDefs.contains fv && !exprContainsFVar b fv then
          rawDefs := rawDefs.insert fv {
            fvarId := fv
            width := w
            rhs := b
            eqProof := mkFVar ldecl.fvarId
            isLet := false
            hypFVarId? := some ldecl.fvarId
          }
          defHypSet := defHypSet.insert ldecl.fvarId
          orderedVars := orderedVars.push fv
          continue
      if let .fvar fv := b then
        if !rawDefs.contains fv && !exprContainsFVar a fv then
          let symmPrf ← mkEqSymm (mkFVar ldecl.fvarId)
          rawDefs := rawDefs.insert fv {
            fvarId := fv
            width := w
            rhs := a
            eqProof := symmPrf
            isLet := false
            hypFVarId? := some ldecl.fvarId
          }
          defHypSet := defHypSet.insert ldecl.fvarId
          orderedVars := orderedVars.push fv
    -- Topologically sort `rawDefs`, dropping any back-edge that would form a cycle.
    let stateRef ← IO.mkRef ({} : Std.HashMap FVarId Nat) -- 1 = visiting, 2 = done
    let droppedRef ← IO.mkRef ({} : Std.HashSet FVarId)
    let topoRef ← IO.mkRef (#[] : Array FVarId)
    let depthRef ← IO.mkRef ({} : Std.HashMap FVarId Nat)
    let defHypRef ← IO.mkRef defHypSet
    let rec dfs (fuel : Nat) (fv : FVarId) : MetaM Unit := do
      let .succ fuel' := fuel | do
        droppedRef.modify (·.insert fv)
        return
      match (← stateRef.get).get? fv with
      | some 2 => return
      | some 1 =>
        droppedRef.modify (·.insert fv)
        return
      | _ => pure ()
      let some info := rawDefs.get? fv | return
      stateRef.modify (·.insert fv 1)
      let deps := collectExprFVars info.rhs
      let mut maxDep := 0
      let mut hasCycle := false
      for d in deps do
        if rawDefs.contains d then
          if (← stateRef.get).get? d == some 1 then
            hasCycle := true
          else
            dfs fuel' d
            if !(← droppedRef.get).contains d then
              maxDep := max maxDep ((← depthRef.get).getD d 0)
      if hasCycle || (← droppedRef.get).contains fv then
        droppedRef.modify (·.insert fv)
        stateRef.modify (·.insert fv 2)
        if let some hfv := info.hypFVarId? then
          defHypRef.modify (·.erase hfv)
      else
        stateRef.modify (·.insert fv 2)
        depthRef.modify (·.insert fv (maxDep + 1))
        topoRef.modify (·.push fv)
    for fv in orderedVars do
      dfs (orderedVars.size + 1) fv
    let topo ← topoRef.get
    let depthMap ← depthRef.get
    let finalDefHypSet ← defHypRef.get
    let mut cleanDefs : Std.HashMap FVarId DefInfo := {}
    for fv in topo do
      if let some info := rawDefs.get? fv then
        cleanDefs := cleanDefs.insert fv info
    let mut sideHyps : Array FVarId := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail || ldecl.value?.isSome then continue
      if finalDefHypSet.contains ldecl.fvarId then continue
      if ← isProp ldecl.type then
        sideHyps := sideHyps.push ldecl.fvarId
    return { defs := cleanDefs, topoOrder := topo, depth := depthMap, sideHyps := sideHyps }

def collectConeVars (g : DefGraph) (root : Expr) : Std.HashSet FVarId := Id.run do
  let mut stack := collectExprFVars root
  let mut visited : Std.HashSet FVarId := {}
  while !stack.isEmpty do
    let fv := stack.back!
    stack := stack.pop
    if visited.contains fv then continue
    visited := visited.insert fv
    if let some info := g.defs.get? fv then
      for d in collectExprFVars info.rhs do
        if !visited.contains d then
          stack := stack.push d
  return visited

/-! ## 3. Fast 64-Bit Corner + Random Simulation Engine -/

private inductive SimBvOp where
  | var (slot : Nat)
  | const (w : Nat) (val : BitVec w)
  | bin (op : BVBinOp) (lhs rhs : Nat)
  | sub (lhs rhs : Nat)
  | neg (inner : Nat)
  | un (op : BVUnOp) (inner : Nat)
  | shlConst (inner k : Nat)
  | shrConst (inner k : Nat)
  | shlBv (lhs rhs : Nat)
  | shrBv (lhs rhs : Nat)
  | ashrBv (lhs rhs : Nat)
  | append (lhs rhs : Nat)
  | extract (start len inner : Nat)
  | zeroExtend (inner : Nat)
  | signExtend (inner : Nat)
  | replicate (n inner : Nat)
  | ite (condNode thenNode elseNode : Nat)

private inductive SimBoolOp where
  | bvar (slot : Nat)
  | bconst (val : Bool)
  | not (inner : Nat)
  | and (lhs rhs : Nat)
  | or (lhs rhs : Nat)
  | xor (lhs rhs : Nat)
  | beq (lhs rhs : Nat)
  | bvEq (lhs rhs : Nat)
  | bvNe (lhs rhs : Nat)
  | bvUlt (lhs rhs : Nat)
  | bvUle (lhs rhs : Nat)
  | bvSlt (lhs rhs : Nat)
  | bvSle (lhs rhs : Nat)
  | getLsbD (inner idx : Nat)
  | msb (inner : Nat)

private inductive SimNode where
  | bv (width : Nat) (op : SimBvOp)
  | bool (op : SimBoolOp)

private structure SimBuildState where
  nodes : Array SimNode := #[]
  bvVars : Array Nat := #[]
  numBoolVars : Nat := 0
  bvFVarSlot : Std.HashMap FVarId Nat := {}
  boolFVarSlot : Std.HashMap FVarId Nat := {}
  fvarNode : Std.HashMap FVarId Nat := {}
  exprNode : Std.HashMap Sym.ExprPtr Nat := {}
  boolExprNode : Std.HashMap Sym.ExprPtr Nat := {}
  maxNodes : Nat := 32768

private abbrev SimBuildM := StateRefT SimBuildState MetaM

private def addSimNode (n : SimNode) : SimBuildM (Option Nat) := do
  let st ← get
  if st.nodes.size ≥ st.maxNodes then return none
  let idx := st.nodes.size
  set { st with nodes := st.nodes.push n }
  return some idx

private def getOrAddBvVar (fv : FVarId) (w : Nat) : SimBuildM (Option Nat) := do
  let st ← get
  if let some idx := st.fvarNode.get? fv then
    return some idx
  let slot := st.bvVars.size
  let some idx ← addSimNode (.bv w (.var slot)) | return none
  modify fun s => { s with
    bvVars := s.bvVars.push w
    bvFVarSlot := s.bvFVarSlot.insert fv slot
    fvarNode := s.fvarNode.insert fv idx }
  return some idx

private def getOrAddBoolVar (fv : FVarId) : SimBuildM (Option Nat) := do
  let st ← get
  if let some idx := st.boolFVarSlot.get? fv then
    return some idx
  let slot := st.numBoolVars
  let some idx ← addSimNode (.bool (.bvar slot)) | return none
  modify fun s => { s with
    numBoolVars := s.numBoolVars + 1
    boolFVarSlot := s.boolFVarSlot.insert fv idx }
  return some idx

private def simNodeWidth? (idx : Nat) : SimBuildM (Option Nat) := do
  let st ← get
  match st.nodes[idx]? with
  | some (.bv w _) => return some w
  | _ => return none

mutual

private partial def reflectSimBv (g : DefGraph) (e : Expr) : SimBuildM (Option Nat) := do
  let e := e.consumeMData
  if let some idx := (← get).exprNode.get? ⟨e⟩ then
    return some idx
  let res ← reflectSimBvCore g e
  if let some idx := res then
    modify fun s => { s with exprNode := s.exprNode.insert ⟨e⟩ idx }
  return res

private partial def reflectSimBvCore (g : DefGraph) (e : Expr) : SimBuildM (Option Nat) := do
  if let some ⟨w, val⟩ := getBitVecLit? e then
    return ← addSimNode (.bv w (.const w val))
  if let .fvar fv := e then
    if let some idx := (← get).fvarNode.get? fv then
      return some idx
    if let some info := g.defs.get? fv then
      let some idx ← reflectSimBv g info.rhs | return none
      modify fun s => { s with fvarNode := s.fvarNode.insert fv idx }
      return some idx
    let some w ← getBitVecWidth? (← fv.getDecl).type | return none
    return ← getOrAddBvVar fv w
  match_expr e with
  | BitVec.twoPow wExpr kExpr =>
    let some w := getNatLit? wExpr | return none
    let some k := getNatLit? kExpr | return none
    addSimNode (.bv w (.const w (BitVec.twoPow w k)))
  | HAdd.hAdd _ _ _ _ a b => reflectSimBin g .add a b
  | Add.add _ _ a b => reflectSimBin g .add a b
  | BitVec.add _ a b => reflectSimBin g .add a b
  | HSub.hSub _ _ _ _ a b => reflectSimSub g a b
  | Sub.sub _ _ a b => reflectSimSub g a b
  | BitVec.sub _ a b => reflectSimSub g a b
  | HMul.hMul _ _ _ _ a b => reflectSimBin g .mul a b
  | Mul.mul _ _ a b => reflectSimBin g .mul a b
  | BitVec.mul _ a b => reflectSimBin g .mul a b
  | HAnd.hAnd _ _ _ _ a b => reflectSimBin g .and a b
  | AndOp.and _ _ a b => reflectSimBin g .and a b
  | BitVec.and _ a b => reflectSimBin g .and a b
  | HOr.hOr _ _ _ _ a b => reflectSimBin g .or a b
  | OrOp.or _ _ a b => reflectSimBin g .or a b
  | BitVec.or _ a b => reflectSimBin g .or a b
  | HXor.hXor _ _ _ _ a b => reflectSimBin g .xor a b
  | XorOp.xor _ _ a b => reflectSimBin g .xor a b
  | BitVec.xor _ a b => reflectSimBin g .xor a b
  | HDiv.hDiv _ _ _ _ a b => reflectSimBin g .udiv a b
  | HMod.hMod _ _ _ _ a b => reflectSimBin g .umod a b
  | Neg.neg _ _ a =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    addSimNode (.bv w (.neg ai))
  | BitVec.neg _ a =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    addSimNode (.bv w (.neg ai))
  | Complement.complement _ _ a => reflectSimUn g .not a
  | BitVec.not _ a => reflectSimUn g .not a
  | BitVec.reverse _ a => reflectSimUn g .reverse a
  | BitVec.clz _ a => reflectSimUn g .clz a
  | BitVec.cpop _ a => reflectSimUn g .cpop a
  | BitVec.rotateLeft _ a kExpr =>
    let some k := getNatLit? kExpr | return none
    reflectSimUn g (.rotateLeft k) a
  | BitVec.rotateRight _ a kExpr =>
    let some k := getNatLit? kExpr | return none
    reflectSimUn g (.rotateRight k) a
  | BitVec.sshiftRight _ a kExpr =>
    let some k := getNatLit? kExpr | return none
    reflectSimUn g (.arithShiftRightConst k) a
  | BitVec.sshiftRight' _ _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some si ← reflectSimBv g s | return none
    let some w ← simNodeWidth? ai | return none
    addSimNode (.bv w (.ashrBv ai si))
  | HShiftLeft.hShiftLeft _ _ _ _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    if let some k := getNatLit? s then
      addSimNode (.bv w (.shlConst ai k))
    else
      let some si ← reflectSimBv g s | return none
      addSimNode (.bv w (.shlBv ai si))
  | BitVec.shiftLeft _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    let some k := getNatLit? s | return none
    addSimNode (.bv w (.shlConst ai k))
  | HShiftRight.hShiftRight _ _ _ _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    if let some k := getNatLit? s then
      addSimNode (.bv w (.shrConst ai k))
    else
      let some si ← reflectSimBv g s | return none
      addSimNode (.bv w (.shrBv ai si))
  | BitVec.ushiftRight _ a s =>
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    let some k := getNatLit? s | return none
    addSimNode (.bv w (.shrConst ai k))
  | HAppend.hAppend _ _ _ _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    let some wa ← simNodeWidth? ai | return none
    let some wb ← simNodeWidth? bi | return none
    addSimNode (.bv (wa + wb) (.append ai bi))
  | BitVec.append _ _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    let some wa ← simNodeWidth? ai | return none
    let some wb ← simNodeWidth? bi | return none
    addSimNode (.bv (wa + wb) (.append ai bi))
  | BitVec.extractLsb' _ sExpr lExpr a =>
    let some start := getNatLit? sExpr | return none
    let some len := getNatLit? lExpr | return none
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bv len (.extract start len ai))
  | BitVec.extractLsb _ hiExpr loExpr a =>
    let some hi := getNatLit? hiExpr | return none
    let some lo := getNatLit? loExpr | return none
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bv (hi - lo + 1) (.extract lo (hi - lo + 1) ai))
  | BitVec.zeroExtend _ vExpr a => reflectSimZeroExt g vExpr a
  | BitVec.truncate _ vExpr a => reflectSimZeroExt g vExpr a
  | BitVec.setWidth _ vExpr a => reflectSimZeroExt g vExpr a
  | BitVec.setWidth' _ vExpr _ a => reflectSimZeroExt g vExpr a
  | BitVec.signExtend _ vExpr a =>
    let some v := getNatLit? vExpr | return none
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bv v (.signExtend ai))
  | BitVec.replicate _ nExpr a =>
    let some n := getNatLit? nExpr | return none
    let some ai ← reflectSimBv g a | return none
    let some w ← simNodeWidth? ai | return none
    addSimNode (.bv (w * n) (.replicate n ai))
  | ite _ c _ t f =>
    let some ci ← reflectSimBool g c | return none
    let some ti ← reflectSimBv g t | return none
    let some fi ← reflectSimBv g f | return none
    let some wt ← simNodeWidth? ti | return none
    let some wf ← simNodeWidth? fi | return none
    if wt != wf then return none
    addSimNode (.bv wt (.ite ci ti fi))
  | cond _ c t f =>
    let some ci ← reflectSimBool g c | return none
    let some ti ← reflectSimBv g t | return none
    let some fi ← reflectSimBv g f | return none
    let some wt ← simNodeWidth? ti | return none
    let some wf ← simNodeWidth? fi | return none
    if wt != wf then return none
    addSimNode (.bv wt (.ite ci ti fi))
  | _ => return none

private partial def reflectSimBin (g : DefGraph) (op : BVBinOp) (a b : Expr) :
    SimBuildM (Option Nat) := do
  let some ai ← reflectSimBv g a | return none
  let some bi ← reflectSimBv g b | return none
  let some wa ← simNodeWidth? ai | return none
  let some wb ← simNodeWidth? bi | return none
  if wa != wb then return none
  addSimNode (.bv wa (.bin op ai bi))

private partial def reflectSimSub (g : DefGraph) (a b : Expr) : SimBuildM (Option Nat) := do
  let some ai ← reflectSimBv g a | return none
  let some bi ← reflectSimBv g b | return none
  let some wa ← simNodeWidth? ai | return none
  let some wb ← simNodeWidth? bi | return none
  if wa != wb then return none
  addSimNode (.bv wa (.sub ai bi))

private partial def reflectSimUn (g : DefGraph) (op : BVUnOp) (a : Expr) :
    SimBuildM (Option Nat) := do
  let some ai ← reflectSimBv g a | return none
  let some wa ← simNodeWidth? ai | return none
  addSimNode (.bv wa (.un op ai))

private partial def reflectSimZeroExt (g : DefGraph) (vExpr a : Expr) :
    SimBuildM (Option Nat) := do
  let some v := getNatLit? vExpr | return none
  let some ai ← reflectSimBv g a | return none
  addSimNode (.bv v (.zeroExtend ai))

private partial def reflectSimBool (g : DefGraph) (e : Expr) : SimBuildM (Option Nat) := do
  let e := e.consumeMData
  if let some idx := (← get).boolExprNode.get? ⟨e⟩ then
    return some idx
  let res ← reflectSimBoolCore g e
  if let some idx := res then
    modify fun s => { s with boolExprNode := s.boolExprNode.insert ⟨e⟩ idx }
  return res

private partial def reflectSimBoolCore (g : DefGraph) (e : Expr) : SimBuildM (Option Nat) := do
  if let some b := getBoolLit? e then
    return ← addSimNode (.bool (.bconst b))
  if let .fvar fv := e then
    let ty := (← instantiateMVars (← fv.getDecl).type).consumeMData
    if ty.isConstOf ``Bool then
      return ← getOrAddBoolVar fv
    return none
  match_expr e with
  | True => addSimNode (.bool (.bconst true))
  | False => addSimNode (.bool (.bconst false))
  | Not inner =>
    let some i ← reflectSimBool g inner | return none
    addSimNode (.bool (.not i))
  | Bool.not inner =>
    let some i ← reflectSimBool g inner | return none
    addSimNode (.bool (.not i))
  | And a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.and ai bi))
  | Bool.and a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.and ai bi))
  | Or a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.or ai bi))
  | Bool.or a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.or ai bi))
  | Bool.xor a b =>
    let some ai ← reflectSimBool g a | return none
    let some bi ← reflectSimBool g b | return none
    addSimNode (.bool (.xor ai bi))
  | Eq ty a b =>
    if ty.consumeMData.isConstOf ``Bool then
      if getBoolLit? b == some true then
        reflectSimBool g a
      else if getBoolLit? a == some true then
        reflectSimBool g b
      else if getBoolLit? b == some false then
        let some ai ← reflectSimBool g a | return none
        addSimNode (.bool (.not ai))
      else if getBoolLit? a == some false then
        let some bi ← reflectSimBool g b | return none
        addSimNode (.bool (.not bi))
      else
        let some ai ← reflectSimBool g a | return none
        let some bi ← reflectSimBool g b | return none
        addSimNode (.bool (.beq ai bi))
    else if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvEq ai bi))
    else
      return none
  | Ne ty a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvNe ai bi))
    else if ty.consumeMData.isConstOf ``Bool then
      let some ai ← reflectSimBool g a | return none
      let some bi ← reflectSimBool g b | return none
      addSimNode (.bool (.xor ai bi))
    else
      return none
  | BEq.beq ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvEq ai bi))
    else if ty.consumeMData.isConstOf ``Bool then
      let some ai ← reflectSimBool g a | return none
      let some bi ← reflectSimBool g b | return none
      addSimNode (.bool (.beq ai bi))
    else
      return none
  | LT.lt ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvUlt ai bi))
    else
      return none
  | LE.le ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvUle ai bi))
    else
      return none
  | GT.gt ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvUlt bi ai))
    else
      return none
  | GE.ge ty _ a b =>
    if (← getBitVecWidth? ty).isSome then
      let some ai ← reflectSimBv g a | return none
      let some bi ← reflectSimBv g b | return none
      addSimNode (.bool (.bvUle bi ai))
    else
      return none
  | BitVec.ult _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    addSimNode (.bool (.bvUlt ai bi))
  | BitVec.ule _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    addSimNode (.bool (.bvUle ai bi))
  | BitVec.slt _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    addSimNode (.bool (.bvSlt ai bi))
  | BitVec.sle _ a b =>
    let some ai ← reflectSimBv g a | return none
    let some bi ← reflectSimBv g b | return none
    addSimNode (.bool (.bvSle ai bi))
  | BitVec.getLsbD _ a idxExpr =>
    let some idx := getNatLit? idxExpr | return none
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bool (.getLsbD ai idx))
  | BitVec.msb _ a =>
    let some ai ← reflectSimBv g a | return none
    addSimNode (.bool (.msb ai))
  | decide p _ => reflectSimBool g p
  | _ => return none

end

private inductive SimVal where
  | bv (w : Nat) (val : BitVec w)
  | bool (val : Bool)
  deriving Inhabited

private def SimVal.asBv (w : Nat) : SimVal → BitVec w
  | .bv w' v => if h : w' = w then h ▸ v else v.setWidth w
  | .bool b => BitVec.ofNat w (if b then 1 else 0)

private def SimVal.asBool : SimVal → Bool
  | .bool b => b
  | .bv _ v => v.toNat != 0

private def evalSimDag (nodes : Array SimNode) (bvInputs : Array BVExpr.PackedBitVec)
    (boolInputs : Array Bool) : Array SimVal := Id.run do
  let mut vals : Array SimVal := Array.emptyWithCapacity nodes.size
  for node in nodes do
    let v : SimVal := match node with
      | .bv w op =>
        let res : BitVec w := match op with
          | .var slot =>
            let p := bvInputs[slot]!
            if h : p.w = w then h ▸ p.bv else p.bv.setWidth w
          | .const w' c =>
            if h : w' = w then h ▸ c else c.setWidth w
          | .bin bop l r => bop.eval (vals[l]!.asBv w) (vals[r]!.asBv w)
          | .sub l r => (vals[l]!.asBv w) - (vals[r]!.asBv w)
          | .neg a => -(vals[a]!.asBv w)
          | .un uop a => uop.eval (vals[a]!.asBv w)
          | .shlConst a k => (vals[a]!.asBv w) <<< k
          | .shrConst a k => (vals[a]!.asBv w) >>> k
          | .shlBv a s =>
            match vals[s]! with
            | .bv _ sv => (vals[a]!.asBv w) <<< sv
            | _ => 0#w
          | .shrBv a s =>
            match vals[s]! with
            | .bv _ sv => (vals[a]!.asBv w) >>> sv
            | _ => 0#w
          | .ashrBv a s =>
            match vals[s]! with
            | .bv _ sv => BitVec.sshiftRight' (vals[a]!.asBv w) sv
            | _ => 0#w
          | .append l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr =>
              let cat := vl ++ vr
              if h : wl + wr = w then h ▸ cat else cat.setWidth w
            | _, _ => 0#w
          | .extract start len a =>
            match vals[a]! with
            | .bv _ va =>
              let ex := BitVec.extractLsb' start len va
              if h : len = w then h ▸ ex else ex.setWidth w
            | _ => 0#w
          | .zeroExtend a =>
            match vals[a]! with
            | .bv _ va => va.setWidth w
            | _ => 0#w
          | .signExtend a =>
            match vals[a]! with
            | .bv _ va => va.signExtend w
            | _ => 0#w
          | .replicate n a =>
            match vals[a]! with
            | .bv wa va =>
              let rep := BitVec.replicate n va
              if h : wa * n = w then h ▸ rep else rep.setWidth w
            | _ => 0#w
          | .ite c t f =>
            if vals[c]!.asBool then vals[t]!.asBv w else vals[f]!.asBv w
        .bv w res
      | .bool op =>
        let res : Bool := match op with
          | .bvar slot => boolInputs[slot]!
          | .bconst b => b
          | .not a => !vals[a]!.asBool
          | .and l r => vals[l]!.asBool && vals[r]!.asBool
          | .or l r => vals[l]!.asBool || vals[r]!.asBool
          | .xor l r => vals[l]!.asBool ^^ vals[r]!.asBool
          | .beq l r => vals[l]!.asBool == vals[r]!.asBool
          | .bvEq l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr => wl == wr && vl.toNat == vr.toNat
            | _, _ => false
          | .bvNe l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr => !(wl == wr && vl.toNat == vr.toNat)
            | _, _ => false
          | .bvUlt l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr => wl == wr && vl.toNat < vr.toNat
            | _, _ => false
          | .bvUle l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr => wl == wr && vl.toNat ≤ vr.toNat
            | _, _ => false
          | .bvSlt l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr =>
              if h : wr = wl then vl.slt (h ▸ vr) else false
            | _, _ => false
          | .bvSle l r =>
            match vals[l]!, vals[r]! with
            | .bv wl vl, .bv wr vr =>
              if h : wr = wl then vl.sle (h ▸ vr) else false
            | _, _ => false
          | .getLsbD a idx =>
            match vals[a]! with
            | .bv _ va => va.getLsbD idx
            | _ => false
          | .msb a =>
            match vals[a]! with
            | .bv _ va => va.msb
            | _ => false
        .bool res
    vals := vals.push v
  return vals

private def splitmix64 (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9e3779b97f4a7c15
  let z := (s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (s', z ^^^ (z >>> 31))

private def randNatWidth (seed : UInt64) (w : Nat) (smallMask? : Option Nat := none) :
    UInt64 × Nat := Id.run do
  if let some mask := smallMask? then
    let (s', r) := splitmix64 seed
    return (s', r.toNat &&& mask)
  let words := max 1 ((w + 63) / 64)
  let mut s := seed
  let mut acc : Nat := 0
  for i in [0:words] do
    let (s', r) := splitmix64 s
    s := s'
    acc := acc ||| (r.toNat <<< (64 * i))
  return (s, acc)

private def cornerNatFor (patIdx varIdx w : Nat) : Nat :=
  let allOnes := (1 <<< w) - 1
  let msb := if w == 0 then 0 else 1 <<< (w - 1)
  match patIdx with
  | 0 => 0
  | 1 => allOnes
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 7
  | 6 => msb
  | 7 => msb - 1
  | 8 => 0x5555555555555555 &&& allOnes
  | 9 => 0xaaaaaaaaaaaaaaaa &&& allOnes
  | 10 => varIdx + 1
  | 11 => (allOnes ^^^ (1 <<< (varIdx % max 1 w)))
  | 12 => if varIdx % 2 == 0 then 0 else allOnes
  | 13 => if varIdx % 2 == 0 then 1 else 0
  | 14 => (varIdx * 17 + 5) &&& 0x3f
  | _ => (varIdx * 31 + 11) &&& 0xff

private structure SimPattern where
  bvInputs : Array BVExpr.PackedBitVec
  boolInputs : Array Bool

private def mkCornerPattern (bvVars : Array Nat) (numBoolVars patIdx : Nat) :
    SimPattern := Id.run do
  let mut bvs : Array BVExpr.PackedBitVec := Array.emptyWithCapacity bvVars.size
  for h : i in [0:bvVars.size] do
    let w := bvVars[i]
    bvs := bvs.push ⟨BitVec.ofNat w (cornerNatFor patIdx i w)⟩
  let mut bs : Array Bool := Array.emptyWithCapacity numBoolVars
  for i in [0:numBoolVars] do
    bs := bs.push (((patIdx >>> (i % 4)) &&& 1) == 1)
  return { bvInputs := bvs, boolInputs := bs }

private def mkRandPattern (bvVars : Array Nat) (numBoolVars : Nat) (seed : UInt64)
    (smallMask? : Option Nat := none) : UInt64 × SimPattern := Id.run do
  let mut s := seed
  let mut bvs : Array BVExpr.PackedBitVec := Array.emptyWithCapacity bvVars.size
  for w in bvVars do
    let (s', v) := randNatWidth s w smallMask?
    s := s'
    bvs := bvs.push ⟨BitVec.ofNat w v⟩
  let mut bs : Array Bool := Array.emptyWithCapacity numBoolVars
  for _ in [0:numBoolVars] do
    let (s', r) := splitmix64 s
    s := s'
    bs := bs.push ((r &&& 1) == 1)
  return (s, { bvInputs := bvs, boolInputs := bs })

structure CandidateCut where
  lhs : Expr
  rhs : Expr
  width : Nat
  maxDepth : Nat
  sumDepth : Nat
  orderIdx : Nat

structure DiscoveryResult where
  candidates : Array CandidateCut
  probableCex : Bool

private def hashSignature (vals : Array Nat) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for v in vals do
    h := (h ^^^ v.toUInt64) * 0x100000001b3
  return h

/-- Discover same-width candidate cut pairs `(g, t)` via 64-bit corner + random simulation.
Bails out cleanly (returning empty candidates) if opaque atoms are encountered or the goal
has too few nodes to benefit from slicing. -/
def discoverCandidateCuts (g : DefGraph) (lhs rhs : Expr) :
    MetaM DiscoveryResult := do
  if g.defs.size < 2 then
    return { candidates := #[], probableCex := false }
  let leftCone := collectConeVars g lhs
  let rightCone := collectConeVars g rhs
  let mut leftVars : Array FVarId := #[]
  let mut rightVars : Array FVarId := #[]
  for fv in g.topoOrder do
    if leftCone.contains fv then leftVars := leftVars.push fv
    if rightCone.contains fv then rightVars := rightVars.push fv
  -- Also include primary inputs appearing in `leftCone`/`rightCone` for alias cuts like `u0 = x0`.
  for fv in leftCone do
    if !g.defs.contains fv then
      leftVars := leftVars.push fv
  for fv in rightCone do
    if !g.defs.contains fv then
      rightVars := rightVars.push fv
  if leftVars.isEmpty || rightVars.isEmpty then
    return { candidates := #[], probableCex := false }

  let ((rootPair?, sideNodes, allSideReflected, leftNodes, rightNodes), simSt) ←
    (do
      let some lhsNode ← reflectSimBv g lhs | return (none, #[], false, #[], #[])
      let some rhsNode ← reflectSimBv g rhs | return (none, #[], false, #[], #[])
      let mut sNodes : Array Nat := #[]
      let mut allOk := true
      for sh in g.sideHyps do
        let shTy ← instantiateMVars (← sh.getDecl).type
        if let some si ← reflectSimBool g shTy then
          sNodes := sNodes.push si
        else
          allOk := false
      let mut lNodes : Array (FVarId × Nat × Nat) := #[]
      for fv in leftVars do
        if let some ni ← reflectSimBv g (mkFVar fv) then
          if let some w ← simNodeWidth? ni then
            lNodes := lNodes.push (fv, w, ni)
      let mut rNodes : Array (FVarId × Nat × Nat) := #[]
      for fv in rightVars do
        if let some ni ← reflectSimBv g (mkFVar fv) then
          if let some w ← simNodeWidth? ni then
            rNodes := rNodes.push (fv, w, ni)
      return (some (lhsNode, rhsNode), sNodes, allOk, lNodes, rNodes)
    ).run {}

  let some (lhsNode, rhsNode) := rootPair?
    | return { candidates := #[], probableCex := false }

  -- Generate corner + small-range + full-width deterministic random patterns.
  let mut rawPats : Array SimPattern := #[]
  for i in [0:16] do
    rawPats := rawPats.push (mkCornerPattern simSt.bvVars simSt.numBoolVars i)
  let mut seed : UInt64 := 0x243f6a8885a308d3
  for i in [0:16] do
    let mask := if i < 8 then 0x3f else 0x3ff
    let (s', pat) := mkRandPattern simSt.bvVars simSt.numBoolVars seed (some mask)
    seed := s'
    rawPats := rawPats.push pat
  for _ in [0:32] do
    let (s', pat) := mkRandPattern simSt.bvVars simSt.numBoolVars seed none
    seed := s'
    rawPats := rawPats.push pat

  -- Evaluate patterns, filtering by reflected side conditions when present.
  let mut validEvals : Array (Array SimVal) := #[]
  let mut probableCex := false
  let evalAndKeep (pat : SimPattern) : Array SimVal × Bool × Bool :=
    let vals := evalSimDag simSt.nodes pat.bvInputs pat.boolInputs
    let okSide := sideNodes.all fun si => vals[si]!.asBool
    let rootDiff := match vals[lhsNode]!, vals[rhsNode]! with
      | .bv wl vl, .bv wr vr => wl != wr || vl.toNat != vr.toNat
      | _, _ => false
    (vals, okSide, rootDiff)

  for pat in rawPats do
    let (vals, okSide, rootDiff) := evalAndKeep pat
    if okSide then
      if rootDiff && allSideReflected then
        probableCex := true
      validEvals := validEvals.push vals

  if validEvals.size < 8 && !sideNodes.isEmpty then
    for i in [0:256] do
      let mask? :=
        if i % 3 == 0 then some 0x1f
        else if i % 3 == 1 then some 0xff
        else none
      let (s', pat) := mkRandPattern simSt.bvVars simSt.numBoolVars seed mask?
      seed := s'
      let (vals, okSide, rootDiff) := evalAndKeep pat
      if okSide then
        if rootDiff && allSideReflected then
          probableCex := true
        validEvals := validEvals.push vals
        if validEvals.size ≥ 32 then break

  if probableCex then
    return { candidates := #[], probableCex := true }
  if validEvals.isEmpty then
    return { candidates := #[], probableCex := false }

  -- Bucket left nodes by `(width, signatureHash)` and verify exact signature equality.
  let mkSig (nodeIdx : Nat) : Array Nat :=
    validEvals.map fun vals =>
      match (vals[nodeIdx]! : SimVal) with
      | .bv _ v => v.toNat
      | .bool b => if b then 1 else 0

  let mut leftBuckets : Std.HashMap (Nat × UInt64) (Array (FVarId × Array Nat)) := {}
  for (fv, w, ni) in leftNodes do
    let sig := mkSig ni
    let key := (w, hashSignature sig)
    let cur := leftBuckets.getD key #[]
    leftBuckets := leftBuckets.insert key (cur.push (fv, sig))

  let lhsFVar? : Option FVarId := match lhs.consumeMData with | .fvar fv => some fv | _ => none
  let rhsFVar? : Option FVarId := match rhs.consumeMData with | .fvar fv => some fv | _ => none

  let mut seenPairs : Std.HashSet (FVarId × FVarId) := {}
  let mut matchedRight : Std.HashSet FVarId := {}
  let mut candidates : Array CandidateCut := #[]
  let mut orderIdx := 0

  for (rfv, w, rni) in rightNodes do
    if matchedRight.contains rfv then continue
    let rsig := mkSig rni
    let key := (w, hashSignature rsig)
    let some lEntries := leftBuckets.get? key | continue
    -- Pick lowest-depth matching left node distinct from `rfv`.
    let mut bestL? : Option (FVarId × Nat) := none
    for (lfv, lsig) in lEntries do
      if lfv == rfv then continue
      if lsig != rsig then continue
      if lhsFVar? == some lfv && rhsFVar? == some rfv then continue
      let ld := g.depth.getD lfv 0
      let rd := g.depth.getD rfv 0
      if ld == 0 && rd == 0 then continue
      match bestL? with
      | none => bestL? := some (lfv, ld)
      | some (_, bestD) => if ld < bestD then bestL? := some (lfv, ld)
    if let some (lfv, ld) := bestL? then
      if !seenPairs.contains (lfv, rfv) && !seenPairs.contains (rfv, lfv) then
        seenPairs := seenPairs.insert (lfv, rfv)
        matchedRight := matchedRight.insert rfv
        let rd := g.depth.getD rfv 0
        candidates := candidates.push {
          lhs := mkFVar lfv
          rhs := mkFVar rfv
          width := w
          maxDepth := max ld rd
          sumDepth := ld + rd
          orderIdx := orderIdx
        }
        orderIdx := orderIdx + 1

  let sorted := candidates.qsort fun a b =>
    if a.maxDepth != b.maxDepth then a.maxDepth < b.maxDepth
    else if a.sumDepth != b.sumDepth then a.sumDepth < b.sumDepth
    else a.orderIdx < b.orderIdx
  return { candidates := sorted, probableCex := false }

end BvDecideQbe
