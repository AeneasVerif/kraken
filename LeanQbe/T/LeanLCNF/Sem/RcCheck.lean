module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.LeanLCNF.Lower
meta import LeanQbe.T.LeanLCNF.Coverage
meta import LeanQbe.T.LeanLCNF.LcnfC0Demo
meta import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0RecDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo

/-!
# Executable λRC Ownership Checker (`RcCheck`) for Impure `LeanLCNF`

Decidable static ownership/RC-balance checker (`RcCheck : LcModule → Bool`) gating the Tier-P ⊑
Tier-H Perceus soundness theorem (`lcnf_semantics_design_plan.md` §2.4, §2.6, §4 `L4`).

Checks per declaration:
1. **Owned / borrowed / persistent / scalar contexts**: tracks exact owned token counts (`owned`),
   borrowed liveness (`borrowed` + `parent?` backing), persistent once-cell objects (`persistent`),
   and unboxed/tagged/erased values (`noRc`).
2. **`inc` / `dec` balance**: every owned variable must be consumed or `dec`'d down to `owned = 0`
   on every normal exit (`.ret`) and join-point transfer (`.jmp`); borrowed values cannot be
   consumed without `inc`; freeing/consuming a parent invalidates borrows backed by it.
3. **`isShared`-guarded FBIP updates**: `oset`, `uset`, `sset`, `setTag`, and `del` require an
   exclusive (`excl = true`, `owned = 1`, `!persistent`) target — established by fresh allocation
   (`.ctor`/`.reuse`) or the `Bool.false` (`cidx = 0`) branch of `cases (isShared x)`.
4. **Join points (`.jp` / `.jmp`)**: checks the continuation `k`, collects all residual outer
   contexts at every `jmp j`, requires exact agreement of owned counts (and zero leaked `k`-local
   owned variables), then checks `body` under the agreed context extended with `ps`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T.LeanLCNF

/-! ## 1. Variable & Context State -/

/-- Ownership state of a single live local variable. -/
structure RcVar where
  id : Nat
  ty : LcTy
  /-- No heap RC needed (scalar, erased, void, tagged). -/
  noRc : Bool := false
  /-- Persistent heap object (`m_rc = 0`: once-cell const / literal / `ByteArray.empty`). -/
  persistent : Bool := false
  /-- Number of owned RC tokens currently held by this frame. -/
  owned : Nat := 0
  /-- Valid borrowed reference (backed by caller `@&` or by `parent?`). -/
  borrowed : Bool := false
  /-- If borrowed via projection from an owned local, that parent's variable id. -/
  parent? : Option Nat := none
  /-- Proven exclusive (`m_rc = 1`): fresh allocation or `isShared x == false` branch. -/
  excl : Bool := false
  /-- Token created by `reset` (consumable by `reuse` or `dec`). -/
  resetTok : Bool := false
  deriving Repr, BEq, Inhabited

/-- Checking context for one point in an `LcCode` tree. -/
structure RcCtx where
  vars : List RcVar := []
  /-- Mapping `flagVar ↦ targetVar` recorded by `let flagVar := isShared targetVar`. -/
  sharedPreds : List (Nat × Nat) := []
  deriving Repr, BEq, Inhabited

/-- Metadata of an enclosing join point `jp j ps body k`. -/
structure RcJpInfo where
  id : Nat
  params : List LcParam
  /-- Variable IDs that were in scope at `jp` definition time. -/
  scopeIds : List Nat
  deriving Repr, BEq, Inhabited

/-- Module-level signature map for checking `fap`/`pap` ownership conventions and scalar ctors. -/
structure RcModEnv where
  /-- Local declarations: `name ↦ (paramBorrows, paramTys, retTy, isClosedConst)`. -/
  decls : List (String × List Bool × List LcTy × LcTy × Bool)
  /-- Verified nullary (0-field tagged-scalar) constructor names. -/
  scalarCtors : List String := []
  deriving Repr, Inhabited

/-! ## 2. Context Operations -/

/-- Look up a variable in `ctx`. -/
@[expose] def RcCtx.get? (ctx : RcCtx) (x : Nat) : Option RcVar :=
  ctx.vars.find? (·.id == x)

/-- Replace or insert a variable entry in `ctx`. -/
@[expose] def RcCtx.put (ctx : RcCtx) (v : RcVar) : RcCtx :=
  let rec go : List RcVar → List RcVar
    | [] => [v]
    | u :: rest => if u.id == v.id then v :: rest else u :: go rest
  { ctx with vars := go ctx.vars }

/-- Is `v` currently readable (alive as scalar, persistent, owned, or borrowed)? -/
@[expose] def RcVar.isLive (v : RcVar) : Bool :=
  v.noRc || v.persistent || v.owned > 0 || v.borrowed || v.resetTok

/-- Invalidate any borrowed variables whose backing parent `p` is no longer live. -/
@[expose] def RcCtx.invalidateChildren (ctx : RcCtx) (p : Nat) : RcCtx :=
  let vars' := ctx.vars.map fun v =>
    if v.parent? == some p then { v with borrowed := false, parent? := none } else v
  let preds' := ctx.sharedPreds.filter fun (_, tgt) => tgt != p
  { vars := vars', sharedPreds := preds' }

/-- Check that variable `x` is currently live (for borrowed / read-only use). -/
@[expose] def RcCtx.checkLive (ctx : RcCtx) (x : Nat) : Except String Unit :=
  match ctx.get? x with
  | some v => if v.isLive then pure () else throw s!"use of dead var x.{x}"
  | none => throw s!"unbound var x.{x}"

/-- Check that `LcArg` is live for a borrowed position. -/
@[expose] def RcCtx.checkArgLive (ctx : RcCtx) : LcArg → Except String Unit
  | .erased => pure ()
  | .var x => ctx.checkLive x

/-- Consume `n` owned tokens from variable `x` (no-op for `noRc` / `persistent`).
If `x` loses its last owned token and is not borrowed, invalidates child borrows backed by `x`. -/
@[expose] def RcCtx.consumeVar (ctx : RcCtx) (x : Nat) (n : Nat := 1) : Except String RcCtx :=
  match ctx.get? x with
  | none => throw s!"consume unbound var x.{x}"
  | some v =>
    if v.noRc || v.persistent then pure ctx
    else if n == 0 then pure ctx
    else if v.owned < n then
      throw s!"cannot consume {n} owned ref(s) of x.{x} (owned={v.owned}, borrowed={v.borrowed})"
    else
      let rem := v.owned - n
      let v' : RcVar :=
        { v with
          owned := rem
          excl := if rem == 0 then false else v.excl
          resetTok := if rem == 0 then false else v.resetTok }
      let ctx1 := ctx.put v'
      if rem == 0 && !v'.borrowed then pure (ctx1.invalidateChildren x)
      else pure ctx1

/-- Consume an `LcArg` for an owned position. -/
@[expose] def RcCtx.consumeArg (ctx : RcCtx) : LcArg → Except String RcCtx
  | .erased => pure ctx
  | .var x => ctx.consumeVar x 1

/-- Check `args` against a list of borrow flags (`true` = borrowed, `false` = owned). -/
@[expose] def RcCtx.applyArgs (ctx : RcCtx) : List LcArg → List Bool → Except String RcCtx
  | [], [] => pure ctx
  | a :: as, b :: bs => do
    if b then
      ctx.checkArgLive a
      ctx.applyArgs as bs
    else
      let ctx' ← ctx.consumeArg a
      ctx'.applyArgs as bs
  | _, _ => throw "argument arity mismatch"

/-- Verify all variables in `ctx` (or outside `keepIds`) have `owned == 0`. -/
@[expose] def RcCtx.checkNoLeaks (ctx : RcCtx) (keepIds : List Nat := []) : Except String Unit :=
  for v in ctx.vars do
    if !keepIds.contains v.id && !v.noRc && !v.persistent && v.owned != 0 then
      throw s!"leaked owned var x.{v.id} (owned={v.owned})"

/-- Restrict `ctx` to variables whose id is in `scopeIds`. -/
@[expose] def RcCtx.restrict (ctx : RcCtx) (scopeIds : List Nat) : RcCtx :=
  { vars := ctx.vars.filter fun v => scopeIds.contains v.id
    sharedPreds := ctx.sharedPreds.filter fun (b, x) =>
      scopeIds.contains b && scopeIds.contains x }

/-- Bind a fresh variable `x` of type `ty`. -/
@[expose] def RcCtx.bindOwned (ctx : RcCtx) (x : Nat) (ty : LcTy)
    (excl : Bool := false) (persistent : Bool := false) (resetTok : Bool := false) : RcCtx :=
  let noRc := !ty.needsRc
  let v : RcVar :=
    { id := x, ty, noRc, persistent := if noRc then false else persistent
      owned := if noRc || persistent then 0 else 1
      borrowed := false, parent? := none
      excl := if noRc || persistent then false else excl
      resetTok := if noRc || persistent then false else resetTok }
  ctx.put v

/-- Bind a fresh borrowed variable `x` of type `ty`, optionally backed by `parent?`. -/
@[expose] def RcCtx.bindBorrowed (ctx : RcCtx) (x : Nat) (ty : LcTy)
    (parent? : Option Nat := none) (persistent : Bool := false) : RcCtx :=
  let noRc := !ty.needsRc
  let v : RcVar :=
    { id := x, ty, noRc, persistent := if noRc then false else persistent
      owned := 0, borrowed := !noRc && !persistent
      parent? := if noRc || persistent then none else parent?
      excl := false, resetTok := false }
  ctx.put v

/-- Bind a list of `LcParam`s into `ctx`. -/
@[expose] def RcCtx.bindParams (ctx : RcCtx) (ps : List LcParam) : RcCtx :=
  ps.foldl (fun c p =>
    if p.borrow then c.bindBorrowed p.id p.ty none false
    else c.bindOwned p.id p.ty false false false) ctx

/-- Determine the borrow backing (`parent?`, `persistent`) when projecting from `x`. -/
@[expose] def RcCtx.projBacking (ctx : RcCtx) (x : Nat) : Except String (Option Nat × Bool) :=
  match ctx.get? x with
  | none => throw s!"projection from unbound var x.{x}"
  | some v =>
    if !v.isLive then throw s!"projection from dead var x.{x}"
    else if v.persistent then pure (none, true)
    else if v.borrowed then pure (v.parent?, false)
    else if v.owned > 0 then pure (some x, false)
    else pure (none, false)

/-- Mark variable `x` exclusive (if `owned == 1` and `!persistent` and `!noRc`). -/
@[expose] def RcCtx.markExcl (ctx : RcCtx) (x : Nat) : RcCtx :=
  match ctx.get? x with
  | some v =>
    if !v.noRc && !v.persistent && v.owned == 1 then ctx.put { v with excl := true }
    else ctx
  | none => ctx

/-- Refine a `.tobject`/`.tagged` scrutinee `x` to scalar (`noRc = true`) inside a nullary
constructor `cases` branch (`x = 2*cidx + 1`, so `x` holds no heap allocation on that path). -/
@[expose] def RcCtx.markScalarBranch (ctx : RcCtx) (x : Nat) : RcCtx :=
  match ctx.get? x with
  | some v =>
    if v.ty == .tobject || v.ty == .tagged then
      let v' : RcVar :=
        { v with noRc := true, persistent := false, owned := 0, borrowed := false,
                 parent? := none, excl := false, resetTok := false }
      (ctx.put v').invalidateChildren x
    else ctx
  | none => ctx

/-- Require variable `x` to be uniquely owned and exclusive (`excl = true`, `owned = 1`, not a reset
token). -/
@[expose] def RcCtx.checkExcl (ctx : RcCtx) (x : Nat) (op : String) : Except String Unit :=
  match ctx.get? x with
  | none => throw s!"{op}: unbound var x.{x}"
  | some v =>
    if v.noRc then throw s!"{op}: scalar var x.{x}"
    else if v.persistent then throw s!"{op}: persistent var x.{x}"
    else if v.resetTok then throw s!"{op}: reset token x.{x}"
    else if v.owned != 1 then throw s!"{op}: x.{x} has owned={v.owned} (need 1)"
    else if !v.excl then throw s!"{op}: x.{x} is not proven exclusive"
    else pure ()

/-- Merge two jump-site contexts arriving at the same join point `j`.
Owned counts must match identically; `borrowed`/`excl`/`sharedPreds` are intersected. -/
@[expose] def RcCtx.mergeJp (c1 c2 : RcCtx) : Except String RcCtx := do
  let mut merged : List RcVar := []
  for v1 in c1.vars do
    match c2.get? v1.id with
    | none => throw s!"jp merge: missing var x.{v1.id}"
    | some v2 =>
      if v1.noRc != v2.noRc || v1.persistent != v2.persistent || v1.owned != v2.owned then
        throw s!"jp merge: ownership mismatch on x.{v1.id} ({v1.owned} vs {v2.owned})"
      let b := v1.borrowed && v2.borrowed && v1.parent? == v2.parent?
      let p? := if b then v1.parent? else none
      merged := merged ++ [{ v1 with
        borrowed := b, parent? := p?, excl := v1.excl && v2.excl,
        resetTok := v1.resetTok && v2.resetTok }]
  let preds := c1.sharedPreds.filter fun p => c2.sharedPreds.contains p
  pure { vars := merged, sharedPreds := preds }

/-- Merge a non-empty list of jump-site contexts for join point `j`. -/
@[expose] def mergeJpList : List RcCtx → Except String (Option RcCtx)
  | [] => pure none
  | c :: cs => do
    let mut acc := c
    for c' in cs do
      acc ← acc.mergeJp c'
    pure (some acc)

/-! ## 3. Primitive Ownership Signatures -/

/-- Return ownership classification of a primitive result. -/
inductive PrimRetKind where
  | owned
  | borrowed (argIdx : Nat)
  | persistent
  deriving Repr, BEq

/-- Ownership signature `(paramBorrows, retKind)` for built-in extern primitives matching
`Lower.externPrim` and `lcnf_rt.c` (`true` = borrowed `@&`, `false` = owned/consumed). -/
@[expose] def primRcSig (name : String) (arity : Nat) :
    Option (List Bool × PrimRetKind) :=
  match splitDot name with
  | ["Nat", op] =>
    match op, arity with
    | "reprFast", 1 => some ([false], .owned)
    | "pred", 1 | "log2", 1 => some ([true], .owned)
    | _, 2 => some ([true, true], .owned)
    | _, _ => none
  | ["Int", op] =>
    match op, arity with
    | "ofNat", 1 | "negSucc", 1 => some ([false], .owned)
    | "neg", 1 | "natAbs", 1 | "decNonneg", 1 => some ([true], .owned)
    | "divExact", 3 => some ([true, true, true], .owned)
    | _, 2 => some ([true, true], .owned)
    | _, _ => none
  | ["Int64", op] =>
    match op, arity with
    | "ofNat", 1 | "toInt", 1 | "neg", 1 | "complement", 1 => some ([true], .owned)
    | _, 2 => some ([true, true], .owned)
    | _, _ => none
  | ["Char", op] =>
    match op, arity with
    | "ofNat", 1 | "utf8Size", 1 => some ([true], .owned)
    | "ofNatAux", 2 => some ([true, true], .owned)
    | _, _ => none
  | ["Float", op] =>
    match op, arity with
    | "ofScientific", 3 => some ([false, true, false], .owned)
    | _, 1 => some ([true], .owned)
    | _, 2 => some ([true, true], .owned)
    | _, _ => none
  | "String" :: rest =>
    match rest, arity with
    | ["toListImpl"], 1 | ["data"], 1 | ["ofList"], 1 | ["mk"], 1 => some ([false], .owned)
    | ["length"], 1 | ["Internal", "length"], 1 | ["utf8ByteSize"], 1 => some ([true], .owned)
    | ["push"], 2 | ["append"], 2 | ["Internal", "append"], 2 => some ([false, true], .owned)
    | ["propagateMark"], 2 => some ([true, false], .owned)
    | _, 2 => some ([true, true], .owned)
    | _, 3 => some ([true, true, true], .owned)
    | _, _ => none
  | ["Array", op] =>
    match op, arity with
    | "empty", 1 => some ([true], .owned)
    | "mkEmpty", 2 | "emptyWithCapacity", 2 | "size", 2 | "usize", 2 =>
      some ([true, true], .owned)
    | "mk", 2 | "toList", 2 | "pop", 2 => some ([true, false], .owned)
    | "push", 3 => some ([true, false, false], .owned)
    | "replicate", 3 => some ([true, true, false], .owned)
    | "get!Internal", 4 => some ([true, true, true, true], .owned)
    | "get!InternalBorrowed", 4 => some ([true, true, true, true], .borrowed 2)
    | "getInternal", 4 | "uget", 4 => some ([true, true, true, true], .owned)
    | "getInternalBorrowed", 4 | "ugetBorrowed", 4 => some ([true, true, true, true], .borrowed 1)
    | "set!", 4 => some ([true, false, true, false], .owned)
    | "set", 5 | "uset", 5 => some ([true, false, true, false, true], .owned)
    | "swapIfInBounds", 4 => some ([true, false, true, true], .owned)
    | "swap", 6 => some ([true, false, true, true, true, true], .owned)
    | "propagateMark", 4 => some ([true, true, true, false], .owned)
    | _, _ => none
  | ["ByteArray", op] =>
    match op, arity with
    | "empty", 0 => some ([], .persistent)
    | "emptyWithCapacity", 1 | "size", 1 | "usize", 1 => some ([true], .owned)
    | "mk", 1 | "data", 1 => some ([false], .owned)
    | "push", 2 => some ([false, true], .owned)
    | "get!", 2 | "beq", 2 | "decEq", 2 | "decidableLT", 2 | "compare", 2 =>
      some ([true, true], .owned)
    | "get", 3 | "uget", 3 => some ([true, true, true], .owned)
    | "set!", 3 => some ([false, true, true], .owned)
    | "set", 4 | "uset", 4 => some ([false, true, true, true], .owned)
    | "propagateMark", 2 => some ([true, false], .owned)
    | _, _ => none
  | ["getObjTagNat"] => some (List.replicate arity true, .owned)
  | ["System", "Platform", "getNumBits"] => some (List.replicate arity true, .owned)
  | ["outOfBounds", "_redArg"] =>
    if arity == 1 then some ([true], .owned) else none
  | [ty, op] =>
    match uintWidth? ty with
    | some _ =>
      match op, arity with
      | "ofBitVec", 1 => some ([false], .owned)
      | _, n => some (List.replicate n true, .owned)
    | none => none
  | _ => none

/-! ## 4. Value & Code Ownership Checking -/

/-- Check a single `let x : ty := v` step, returning the updated context. -/
@[expose] def checkVal (env : RcModEnv) (ctx : RcCtx) (x : Nat) (ty : LcTy)
    (v : LcVal) : Except String RcCtx := do
  match v with
  | .lit (.nat n) =>
    if !ty.needsRc then pure (ctx.bindOwned x ty)
    else if n < 2 ^ 63 then pure (ctx.bindOwned x ty)
    else pure (ctx.bindOwned x ty (persistent := true))
  | .lit (.str _) => pure (ctx.bindOwned x ty (persistent := true))
  | .lit (.scalar _) | .erased => pure (ctx.bindOwned x ty)
  | .ctor ci as =>
    if ci.isScalar then
      pure (ctx.bindOwned x ty (excl := false))
    else
      let ctx1 ← ctx.applyArgs as (List.replicate as.length false)
      pure (ctx1.bindOwned x ty (excl := true))
  | .oproj _ obj =>
    let (p?, pers) ← ctx.projBacking obj
    pure (ctx.bindBorrowed x ty p? pers)
  | .uproj _ obj | .sproj _ _ obj =>
    ctx.checkLive obj
    pure (ctx.bindOwned x ty)
  | .box _ y =>
    ctx.checkLive y
    pure (ctx.bindOwned x ty (excl := true))
  | .unbox y =>
    ctx.checkLive y
    pure (ctx.bindOwned x ty)
  | .isShared y =>
    ctx.checkLive y
    let ctx1 := ctx.bindOwned x ty
    pure { ctx1 with sharedPreds := (x, y) :: ctx1.sharedPreds }
  | .reset _ y =>
    let ctx1 ← ctx.consumeVar y 1
    pure (ctx1.bindOwned x ty (excl := true) (resetTok := true))
  | .reuse tok ci _ as =>
    let ctx1 ← ctx.consumeVar tok 1
    let ctx2 ← ctx1.applyArgs as (List.replicate as.length false)
    pure (ctx2.bindOwned x ty (excl := !ci.isScalar))
  | .pap f as =>
    match env.decls.find? (·.1 == f) with
    | none => throw s!"pap target {f} not found in module"
    | some (_, _, pts, _, _) =>
      if as.length >= pts.length then throw s!"pap {f}: too many fixed args"
      let ctx1 ← ctx.applyArgs as (List.replicate as.length false)
      pure (ctx1.bindOwned x ty (excl := true))
  | .ap f as =>
    let ctx1 ← ctx.consumeVar f 1
    let ctx2 ← ctx1.applyArgs as (List.replicate as.length false)
    pure (ctx2.bindOwned x ty)
  | .fap f as =>
    match env.decls.find? (·.1 == f) with
    | some (_, borrows, _, _, isConst) =>
      if isConst && as.isEmpty then
        pure (ctx.bindOwned x ty (persistent := true))
      else
        let ctx1 ← ctx.applyArgs as borrows
        pure (ctx1.bindOwned x ty)
    | none =>
      match primRcSig f as.length with
      | none => throw s!"unknown extern primitive '{f}/{as.length}'"
      | some (borrows, retKind) =>
        let ctx1 ← ctx.applyArgs as borrows
        match retKind with
        | .owned => pure (ctx1.bindOwned x ty)
        | .persistent => pure (ctx1.bindOwned x ty (persistent := true))
        | .borrowed idx =>
          match as[idx]? with
          | some (.var src) =>
            let (p?, pers) ← ctx1.projBacking src
            pure (ctx1.bindBorrowed x ty p? pers)
          | _ => pure (ctx1.bindBorrowed x ty none false)

mutual
/-- Structurally recursive ownership/RC-balance checker over `LcCode`.
Returns the list of `(jpId, residualOuterCtx)` snapshots collected from all reachable `jmp`s to
enclosing join points. -/
@[expose] def checkCode (env : RcModEnv) (retTy : LcTy) (jps : List RcJpInfo)
    (ctx : RcCtx) : LcCode → Except String (List (Nat × RcCtx))
  | .let_ x ty v k => do
    let ctx' ← checkVal env ctx x ty v
    checkCode env retTy jps ctx' k
  | .jp j ps body k => do
    let scopeIds := ctx.vars.map (·.id)
    let jInfo : RcJpInfo := { id := j, params := ps, scopeIds }
    let jumpsK ← checkCode env retTy (jInfo :: jps) ctx k
    let myJumps := (jumpsK.filter (·.1 == j)).map Prod.snd
    let outerK := jumpsK.filter (·.1 != j)
    let baseCtx ← match ← mergeJpList myJumps with
      | some c => pure c
      | none => pure ctx
    let jumpsBody ← checkCode env retTy jps (baseCtx.bindParams ps) body
    pure (outerK ++ jumpsBody)
  | .jmp j as => do
    match jps.find? (·.id == j) with
    | none => throw s!"jmp to unbound join point _jp.{j}"
    | some info =>
      let ctx1 ← ctx.applyArgs as (info.params.map (·.borrow))
      ctx1.checkNoLeaks info.scopeIds
      pure [(j, ctx1.restrict info.scopeIds)]
  | .cases x alts => do
    ctx.checkLive x
    let target? := (ctx.sharedPreds.find? (·.1 == x)).map Prod.snd
    checkAlts env retTy jps ctx x target? alts
  | .ret a => do
    let ctx1 ← if retTy.needsRc then ctx.consumeArg a
               else do ctx.checkArgLive a; pure ctx
    ctx1.checkNoLeaks
    pure []
  | .unreach => pure []
  | .oset x _ y k => do
    ctx.checkExcl x "oset"
    let ctx1 ← ctx.consumeArg y
    checkCode env retTy jps ctx1 k
  | .uset x _ y k => do
    ctx.checkExcl x "uset"
    ctx.checkLive y
    checkCode env retTy jps ctx k
  | .sset x _ _ y _ k => do
    ctx.checkExcl x "sset"
    ctx.checkLive y
    checkCode env retTy jps ctx k
  | .setTag x _ k => do
    ctx.checkExcl x "setTag"
    checkCode env retTy jps ctx k
  | .inc x n _ k => do
    match ctx.get? x with
    | none => throw s!"inc on unbound var x.{x}"
    | some v =>
      if !v.isLive then throw s!"inc on dead var x.{x}"
      if v.noRc || v.persistent || n == 0 then
        checkCode env retTy jps ctx k
      else
        let v' : RcVar := { v with owned := v.owned + n, excl := false }
        checkCode env retTy jps (ctx.put v') k
  | .dec x n _ k => do
    let ctx1 ← ctx.consumeVar x n
    checkCode env retTy jps ctx1 k
  | .del x k => do
    ctx.checkExcl x "del"
    let ctx1 ← ctx.consumeVar x 1
    checkCode env retTy jps ctx1 k

/-- Check all alternatives of a `cases` expression, refining nullary scalar branches and
`isShared == false` exclusivity. -/
@[expose] def checkAlts (env : RcModEnv) (retTy : LcTy) (jps : List RcJpInfo)
    (ctx : RcCtx) (scru : Nat) (sharedTarget? : Option Nat) :
    List (LcPat × LcCode) → Except String (List (Nat × RcCtx))
  | [] => pure []
  | (pat, body) :: rest => do
    let ctx1 := match pat with
      | .ctor _ cname =>
        if env.scalarCtors.contains cname then ctx.markScalarBranch scru else ctx
      | .dflt => ctx
    let ctxBranch := match sharedTarget?, pat with
      | some tgt, .ctor 0 _ => ctx1.markExcl tgt
      | _, _ => ctx1
    let j1 ← checkCode env retTy jps ctxBranch body
    let j2 ← checkAlts env retTy jps ctx scru sharedTarget? rest
    pure (j1 ++ j2)
end

/-! ## 5. Declaration & Module Entry Points (`RcCheck`) -/

/-- Standard prelude nullary constructors (always tagged scalars `2*cidx + 1`). -/
@[expose] def preludeScalarCtors : List String :=
  [ "List.nil", "Option.none", "Bool.false", "Bool.true",
    "Ordering.lt", "Ordering.eq", "Ordering.gt", "Unit.unit", "PUnit.unit" ]

mutual
/-- Collect `(ctorName, isScalar)` entries appearing in `code`. -/
@[expose] def collectCodeCtors : LcCode → List (String × Bool)
  | .let_ _ _ (.ctor ci _) k | .let_ _ _ (.reuse _ ci _ _) k =>
    (ci.name, ci.isScalar) :: collectCodeCtors k
  | .let_ _ _ _ k => collectCodeCtors k
  | .jp _ _ b k => collectCodeCtors b ++ collectCodeCtors k
  | .cases _ alts => collectAltsCtors alts
  | .oset _ _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k | .setTag _ _ k
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => collectCodeCtors k
  | .jmp _ _ | .ret _ | .unreach => []

/-- Collect `(ctorName, isScalar)` entries over `cases` alternatives. -/
@[expose] def collectAltsCtors : List (LcPat × LcCode) → List (String × Bool)
  | [] => []
  | (_, b) :: rest => collectCodeCtors b ++ collectAltsCtors rest
end

/-- Build the module signature table and verified scalar-constructor list from `m.decls`. -/
@[expose] def mkRcModEnv (m : LcModule) : RcModEnv :=
  let allCtors := m.decls.flatMap fun d => collectCodeCtors d.body
  let heapNames := dedupStr ((allCtors.filter fun p => !p.2).map Prod.fst)
  let modScalars := dedupStr ((allCtors.filter fun p => p.2).map Prod.fst)
  let scalarCtors := dedupStr ((preludeScalarCtors ++ modScalars).filter fun nm =>
    !heapNames.contains nm)
  { decls := m.decls.map fun d =>
      let isConst := d.params.isEmpty && !d.retTy.isScalar
      (d.name, d.params.map (·.borrow), d.params.map (·.ty), d.retTy, isConst)
    scalarCtors }

/-- Check a single declaration `d`, returning an informative error message on failure. -/
@[expose] def checkDeclRc (env : RcModEnv) (d : LcDecl) : Except String Unit := do
  let ctx0 := (RcCtx.mk [] []).bindParams d.params
  let _ ← checkCode env d.retTy [] ctx0 d.body
  pure ()

/-- Check every declaration of `m`, returning the first failing `(declName, error)` if any. -/
@[expose] def checkModuleRc (m : LcModule) : Except (String × String) Unit := do
  let env := mkRcModEnv m
  for d in m.decls do
    match checkDeclRc env d with
    | .ok () => pure ()
    | .error msg => throw (d.name, msg)

/-- Executable λRC ownership checker (`true` iff every declaration in `m` passes RC balance,
borrow-backing, and exclusivity checks). -/
@[expose] def RcCheck (m : LcModule) : Bool :=
  match checkModuleRc m with
  | .ok () => true
  | .error _ => false

end LeanQbe.T.LeanLCNF.Sem

end

/-! ## 6. `#guard` Verification on All 6 `LcnfC0*Demo` Modules and `Coverage.covMod` -/

section RcCheckGuards
open LeanQbe.T.LeanLCNF LeanQbe.T.LeanLCNF.Sem

#guard RcCheck demoNatStrLcMod = true
#guard RcCheck factLoopLcMod = true
#guard RcCheck recDemoLcMod = true
#guard RcCheck treeDemoLcMod = true
#guard RcCheck arrayDemoLcMod = true
#guard RcCheck mutRecDemoLcMod = true
#guard RcCheck Coverage.covMod = true

end RcCheckGuards
