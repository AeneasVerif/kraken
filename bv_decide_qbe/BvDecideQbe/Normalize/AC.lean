module

public import Lean.Meta.Tactic.BVDecide.Normalize

/-!
# Nested `BitVec` `HMul` Subterm `*`-Sorting Canonicalizer (`Gap #14`)

Kernel-proved (`≤ std3`, `0` C0, `0` TCB) `*`-gated subterm AC canonicalizer for `.enhanced` mode.
Upstream `bv_ac_nf` only canonicalizes top-level `Eq`/`BEq` between two `HMul` applications,
leaving nested products like `(x * y) ^^^ w = (y * x) ^^^ w` or `(a * b) >>> 32 = (b * a) >>> 32`
uncollapsed before bitblasting.

`bvMulAcSubtermSimproc` flattens maximal contiguous canonical `BitVec w` `HMul.hMul` trees into
left-associated factor chains, sorts factors by a canonical total order on `Expr`, and constructs
direct kernel proofs using `BitVec.mul_comm` and `BitVec.mul_assoc`.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe.Normalize.AC

open Lean
open Lean.Meta
open Lean.Meta.Tactic.BVDecide

/-! ## Canonical `BitVec` `HMul` Matching & Fast `*`-Presence Guard -/

/-- Match canonical `@HMul.hMul (BitVec w) (BitVec w) (BitVec w) (instHMul (BitVec.instMul w)) l r`.
-/
def matchBvMul? (e : Expr) : Option (Expr × Expr × Expr) :=
  match_expr e with
  | HMul.hMul α β γ inst l r =>
    let_expr BitVec w := α | none
    if β == α && γ == α then
      match_expr inst with
      | instHMul instTy mulInst =>
        if instTy == α then
          match_expr mulInst with
          | BitVec.instMul w' =>
            if w' == w then some (w, l, r) else none
          | _ => none
        else none
      | _ => none
    else none
  | _ => none

private def matchBvMulWithWidth? (w e : Expr) : Option (Expr × Expr) :=
  match matchBvMul? e with
  | some (w', l, r) => if w' == w then some (l, r) else none
  | none => none

/-- Fast `O(|DAG|)` scan checking whether `e` contains any canonical `BitVec` `HMul.hMul`. -/
def exprHasBvHMul (e : Expr) : Bool := Id.run do
  let mut stack : Array Expr := #[e]
  let mut visited : Std.HashSet Sym.ExprPtr := {}
  while !stack.isEmpty do
    let cur := stack.back!
    stack := stack.pop
    match cur with
    | .app f a =>
      if !visited.contains ⟨cur⟩ then
        visited := visited.insert ⟨cur⟩
        if (matchBvMul? cur).isSome then return true
        stack := stack.push a
        stack := stack.push f
    | .mdata _ b | .proj _ _ b =>
      if !visited.contains ⟨cur⟩ then
        visited := visited.insert ⟨cur⟩
        stack := stack.push b
    | .forallE _ d b _ | .lam _ d b _ =>
      if !visited.contains ⟨cur⟩ then
        visited := visited.insert ⟨cur⟩
        stack := stack.push d
        stack := stack.push b
    | .letE _ t v b _ =>
      if !visited.contains ⟨cur⟩ then
        visited := visited.insert ⟨cur⟩
        stack := stack.push t
        stack := stack.push v
        stack := stack.push b
    | _ => pure ()
  return false

/-! ## Left-Associated Flattening, Sorting & Direct Proof Construction -/

private structure MulCtx where
  w : Expr
  bvTy : Expr
  mulOp : Expr

private def mkMulCtx (w : Expr) : Sym.SymM MulCtx := do
  let bvTy ← Sym.share (mkApp (mkConst ``BitVec) w)
  let mulInst ← Sym.share (mkApp (mkConst ``BitVec.instMul) w)
  let hMulInst ← Sym.share (mkApp2 (mkConst ``instHMul [0]) bvTy mulInst)
  let mulOp ← Sym.share (mkApp4 (mkConst ``HMul.hMul [0, 0, 0]) bvTy bvTy bvTy hMulInst)
  return { w, bvTy, mulOp }

@[inline] private def MulCtx.mkMul (ctx : MulCtx) (l r : Expr) : Sym.SymM Expr :=
  Sym.share (mkApp2 ctx.mulOp l r)

@[inline] private def MulCtx.mkSymm (ctx : MulCtx) (a b hab : Expr) : Expr :=
  mkApp4 (mkConst ``Eq.symm [1]) ctx.bvTy a b hab

@[inline] private def MulCtx.mkTrans (ctx : MulCtx) (a b c hab hbc : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [1]) ctx.bvTy a b c hab hbc

@[inline] private def MulCtx.mkCongrLeft (ctx : MulCtx) (a a' c h : Expr) : Expr :=
  let fn := Expr.lam `x ctx.bvTy (mkApp2 ctx.mulOp (.bvar 0) (c.liftLooseBVars 0 1)) .default
  mkApp6 (mkConst ``congrArg [1, 1]) ctx.bvTy ctx.bvTy a a' fn h

@[inline] private def MulCtx.mkCongrRight (ctx : MulCtx) (a b b' h : Expr) : Expr :=
  mkApp6 (mkConst ``congrArg [1, 1]) ctx.bvTy ctx.bvTy b b' (mkApp ctx.mulOp a) h

private def MulCtx.mkCongrBoth (ctx : MulCtx) (a a' b b' ha hb : Expr) : Sym.SymM Expr := do
  let ab ← ctx.mkMul a b
  let a'b ← ctx.mkMul a' b
  let a'b' ← ctx.mkMul a' b'
  return ctx.mkTrans ab a'b a'b' (ctx.mkCongrLeft a a' b ha) (ctx.mkCongrRight a' b b' hb)

private def MulCtx.mkAssocSymm (ctx : MulCtx) (a b c : Expr) : Sym.SymM Expr := do
  let ab ← ctx.mkMul a b
  let abC ← ctx.mkMul ab c
  let bc ← ctx.mkMul b c
  let aBc ← ctx.mkMul a bc
  return ctx.mkSymm abC aBc (mkApp4 (mkConst ``BitVec.mul_assoc) ctx.w a b c)

private def MulCtx.mkRightComm (ctx : MulCtx) (a b c : Expr) : Sym.SymM Expr := do
  let ab ← ctx.mkMul a b
  let abC ← ctx.mkMul ab c
  let bc ← ctx.mkMul b c
  let aBc ← ctx.mkMul a bc
  let cb ← ctx.mkMul c b
  let aCb ← ctx.mkMul a cb
  let ac ← ctx.mkMul a c
  let acB ← ctx.mkMul ac b
  let h1 := mkApp4 (mkConst ``BitVec.mul_assoc) ctx.w a b c
  let h2 := ctx.mkCongrRight a bc cb (mkApp3 (mkConst ``BitVec.mul_comm) ctx.w b c)
  let h3 := ctx.mkSymm acB aCb (mkApp4 (mkConst ``BitVec.mul_assoc) ctx.w a c b)
  return ctx.mkTrans abC aBc acB h1 (ctx.mkTrans aBc aCb acB h2 h3)

@[inline] private def MulCtx.combineEq (ctx : MulCtx) (a b c : Expr)
    (h1? h2? : Option Expr) : Option Expr :=
  match h1?, h2? with
  | none, none => none
  | some h1, none => some h1
  | none, some h2 => some h2
  | some h1, some h2 => some (ctx.mkTrans a b c h1 h2)

private def isBvLit (e : Expr) : Bool :=
  match_expr e with
  | BitVec.ofNat _ _ => true
  | _ => false

/-- Total canonical order on `Expr` placing `BitVec.ofNat` literals last so `bv_blast_mul`
keeps constant factors on its right-hand bit-folding operand (`b_off`). -/
@[inline] private def exprLe (a b : Expr) : Bool :=
  if a == b then true
  else
    match isBvLit a, isBvLit b with
    | false, true => true
    | true, false => false
    | _, _ => Expr.lt a b

private inductive LeftProd where
  | single (x : Expr)
  | snoc (lhs : LeftProd) (rhs : Expr) (full : Expr)

private def LeftProd.expr : LeftProd → Expr
  | .single x => x
  | .snoc _ _ full => full

private def appendLeft (ctx : MulCtx) (a : LeftProd) :
    LeftProd → Sym.SymM (LeftProd × Option Expr)
  | .single y => do
    let full ← ctx.mkMul a.expr y
    return (.snoc a y full, none)
  | .snoc b1 b2 bFull => do
    let orig ← ctx.mkMul a.expr bFull
    let ab1Raw ← ctx.mkMul a.expr b1.expr
    let ab1b2Raw ← ctx.mkMul ab1Raw b2
    let hAssoc ← ctx.mkAssocSymm a.expr b1.expr b2
    let (ab1, hRec?) ← appendLeft ctx a b1
    let full ← ctx.mkMul ab1.expr b2
    let hFull := match hRec? with
      | none => hAssoc
      | some hRec =>
        let hCongr := ctx.mkCongrLeft ab1Raw ab1.expr b2 hRec
        ctx.mkTrans orig ab1b2Raw full hAssoc hCongr
    return (.snoc ab1 b2 full, some hFull)

private def flattenLeft (ctx : MulCtx) (e : Expr) : Nat → Sym.SymM (LeftProd × Option Expr)
  | 0 => return (.single e, none)
  | fuel + 1 =>
    match matchBvMulWithWidth? ctx.w e with
    | none => return (.single e, none)
    | some (l, r) => do
      let (lp, hl?) ← flattenLeft ctx l fuel
      let (rp, hr?) ← flattenLeft ctx r fuel
      let lrNew ← ctx.mkMul lp.expr rp.expr
      let hCongr? ← match hl?, hr? with
        | none, none => pure none
        | some hl, none => pure (some (ctx.mkCongrLeft l lp.expr r hl))
        | none, some hr => pure (some (ctx.mkCongrRight l r rp.expr hr))
        | some hl, some hr => pure (some (← ctx.mkCongrBoth l lp.expr r rp.expr hl hr))
      let (res, hApp?) ← appendLeft ctx lp rp
      return (res, ctx.combineEq e lrNew res.expr hCongr? hApp?)

private def insertLeft (ctx : MulCtx) (xs : LeftProd) (y : Expr) :
    Sym.SymM (LeftProd × Option Expr) :=
  match xs with
  | .single x => do
    if exprLe x y then
      let full ← ctx.mkMul x y
      return (.snoc (.single x) y full, none)
    else
      let full ← ctx.mkMul y x
      let h := mkApp3 (mkConst ``BitVec.mul_comm) ctx.w x y
      return (.snoc (.single y) x full, some h)
  | .snoc pre x xFull => do
    if exprLe x y then
      let full ← ctx.mkMul xFull y
      return (.snoc xs y full, none)
    else
      let orig ← ctx.mkMul xFull y
      let preY ← ctx.mkMul pre.expr y
      let swapped ← ctx.mkMul preY x
      let hRComm ← ctx.mkRightComm pre.expr x y
      let (ins, hRec?) ← insertLeft ctx pre y
      let full ← ctx.mkMul ins.expr x
      let hFull := match hRec? with
        | none => hRComm
        | some hRec =>
          let hCongr := ctx.mkCongrLeft preY ins.expr x hRec
          ctx.mkTrans orig swapped full hRComm hCongr
      return (.snoc ins x full, some hFull)

private def sortLeft (ctx : MulCtx) : LeftProd → Sym.SymM (LeftProd × Option Expr)
  | .single x => return (.single x, none)
  | .snoc pre x orig => do
    let (pre', hPre?) ← sortLeft ctx pre
    let mid ← ctx.mkMul pre'.expr x
    let hCongr? := hPre?.map fun h => ctx.mkCongrLeft pre.expr pre'.expr x h
    let (res, hIns?) ← insertLeft ctx pre' x
    return (res, ctx.combineEq orig mid res.expr hCongr? hIns?)

/-- `Sym.Simp.Simproc` canonicalizing any nested `BitVec w` `HMul.hMul` product tree into a
sorted left-associated product via `BitVec.mul_comm` and `BitVec.mul_assoc`. -/
def bvMulAcSubtermSimproc : Sym.Simp.Simproc := fun e =>
  Normalize.withDoneResult do
    let some (w, _, _) := matchBvMul? e | return .rfl
    let ctx ← mkMulCtx w
    let (flat, hFlat?) ← flattenLeft ctx e 64
    let (sorted, hSort?) ← sortLeft ctx flat
    match ctx.combineEq e flat.expr sorted.expr hFlat? hSort? with
    | none => return .rfl
    | some proof =>
      if sorted.expr == e then
        return .rfl
      return .step sorted.expr proof

/-- `*`-gated post-`bvNormalize` pass canonicalizing nested `BitVec` `HMul` subterms and
re-running rewrite/AC/embedded-constraint simplification when any product changed. -/
def bvMulSubtermNormalize : Normalize.PreProcessM Bool := do
  let hyps ← Normalize.PreProcessM.getHyps
  if !hyps.any (fun h => exprHasBvHMul h.type) then
    return false
  let cfg ← Normalize.PreProcessM.getConfig
  let simpCfg : Sym.Simp.Config := { maxSteps := cfg.maxSteps }
  let methods : Sym.Simp.Methods := { post := bvMulAcSubtermSimproc }
  Normalize.PreProcessM.resetDidChange
  let goal ← Normalize.PreProcessM.getTargetMVarId
  let solved ← goal.withContext do
    Normalize.PreProcessM.mapSimpHyps methods simpCfg
  if solved then
    return true
  if !(← Normalize.PreProcessM.didChange) then
    return false
  let mut passes : List Normalize.Pass :=
    [Normalize.rewriteRulesPass, Normalize.bvAcNormalizePass]
  if cfg.embeddedConstraintSubst && cfg.andFlattening then
    passes := passes ++ [Normalize.andFlatteningPass]
  if cfg.embeddedConstraintSubst then
    passes := passes ++ [Normalize.embeddedConstraintPass]
  Normalize.Pass.fixpointPipeline passes

end BvDecideQbe.Normalize.AC
