module

public import LeanQbe.T.Frontend.C0.Parser
public import LeanQbe.T.Frontend.C0.Lower
public import LeanQbe.T.FlatLemmas

/-!
# C0 Lowered `LExpr` → Scope-Checked `TFlat` Bridge

Converts lowered C0 functions (`LFn`) to scope-checked `LeanQbe.T.TFlat` (`TFlatFn`) with
optional promotion of designated exit-symbol calls into `.exit` terminators, yielding universal
well-formedness (`TFlatFn.toFn_wf`) via `Func.wf_of_denote`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Frontend.C0

open LeanQbe.T

/-- De Bruijn context mapping C0 `LVar` / label IDs to `TFlat` levels and types. -/
structure LFlatCtx where
  vdepth : Nat := 0
  ldepth : Nat := 0
  vars : List (Nat × Nat × Ty) := []
  lbls : List (Nat × Nat × List Ty) := []

/-- Push a single lowered variable onto `LFlatCtx`. -/
def LFlatCtx.pushVar (c : LFlatCtx) (lv : LVar) : LFlatCtx :=
  { c with vdepth := c.vdepth + 1, vars := (lv.id, c.vdepth, lv.ty) :: c.vars }

/-- Push a list of lowered variables in order onto `LFlatCtx`. -/
def LFlatCtx.pushVars (c : LFlatCtx) (lvs : List LVar) : LFlatCtx :=
  lvs.foldl LFlatCtx.pushVar c

/-- Push a join/loop label and its parameter signature onto `LFlatCtx`. -/
def LFlatCtx.pushLbl (c : LFlatCtx) (lid : Nat) (ts : List Ty) : LFlatCtx :=
  { c with ldepth := c.ldepth + 1, lbls := (lid, c.ldepth, ts) :: c.lbls }

/-- Resolve a lowered variable ID to a `TFlat` de Bruijn `Arg K t`. -/
def LFlatCtx.lookupVar (c : LFlatCtx) (id : Nat) (t : Ty) : Except String (Arg K t) :=
  match c.vars.find? (fun p => p.1 == id) with
  | some (_, lvl, t') =>
    if _ : t' = t then pure (.var (c.vdepth - 1 - lvl))
    else throw s!"LFlatCtx: variable {id} type mismatch"
  | none => throw s!"LFlatCtx: unbound variable {id}"

/-- Resolve a lowered label ID to a `TFlat` de Bruijn label index. -/
def LFlatCtx.lookupLbl (c : LFlatCtx) (lid : Nat) (ts : List Ty) : Except String Nat :=
  match c.lbls.find? (fun p => p.1 == lid) with
  | some (_, lvl, ts') =>
    if ts' == ts then pure (c.ldepth - 1 - lvl)
    else throw s!"LFlatCtx: label {lid} signature mismatch"
  | none => throw s!"LFlatCtx: unbound label {lid}"

/-- Lower an `LArg` at expected type `t` into a `TFlat` `Arg K t`. -/
def toFlatArg (c : LFlatCtx) (t : Ty) : LArg → Except String (Arg K t)
  | .var id t' => if t' == t then c.lookupVar id t else throw s!"toFlatArg: var {id} ty"
  | .imm t' v => if h : t' = t then pure (.imm (h ▸ v)) else throw "toFlatArg: imm ty"

/-- Lower a list of `LArg`s matching signature `ts` into a `Tup (Arg K) ts`. -/
def toFlatArgs (c : LFlatCtx) : (ts : List Ty) → List LArg → Except String (Tup (Arg K) ts)
  | [], [] => pure ()
  | t :: ts, a :: as => do pure (← toFlatArg c t a, ← toFlatArgs c ts as)
  | _, _ => throw "toFlatArgs: arity mismatch"

mutual
/-- Convert a lowered C0 `LExpr` into a scope-checked `TFlat rs`. -/
def lExprToTFlat (c : LFlatCtx) (rs : List Ty) : LExpr → Except String (TFlat rs)
  | .let_ op binders k => do
    let args ← toFlatArgs c op.sig op.args
    pure (.let_ ⟨op.code, args⟩ (← lExprToTFlat (c.pushVars binders) rs k))
  | .load t addr binder k => do
    pure (.load t (← toFlatArg c i64 addr) (← lExprToTFlat (c.pushVar binder) rs k))
  | .store t val addr k => do
    pure (.store (← toFlatArg c t val) (← toFlatArg c i64 addr) (← lExprToTFlat c rs k))
  | .call f as bs args binders k => do
    let fargs ← toFlatArgs c as args
    pure (.call f bs fargs (← lExprToTFlat (c.pushVars binders) rs k))
  | .jnz cond t e => do
    pure (.jnz (← toFlatArg c .bool cond) (← lExprToTFlat c rs t) (← lExprToTFlat c rs e))
  | .jump lid ts args => do
    pure (.jump (← c.lookupLbl lid ts) (← toFlatArgs c ts args))
  | .ret rs' args => do
    if _ : rs' = rs then pure (.ret (← toFlatArgs c rs args))
    else throw "lExprToTFlat: return signature mismatch"
  | .exit f as args => do pure (.exit f (← toFlatArgs c as args))
  | .hlt => pure .hlt
  | .group blocks k => do
    let c' := blocks.foldl (fun acc (lid, ps, _) => acc.pushLbl lid (ps.map (·.ty))) c
    pure (.group (← lBlocksToTBlocks c' rs blocks) (← lExprToTFlat c' rs k))

/-- Convert a list of lowered C0 `group` blocks into `TBlocks`. -/
def lBlocksToTBlocks (c : LFlatCtx) (rs : List Ty) :
    (blks : List (Nat × List LVar × LExpr)) →
    Except String (TBlocks rs (blks.map fun (_, ps, _) => ps.map (·.ty)))
  | [] => pure .nil
  | (_, ps, b) :: rest => do
    pure (.cons (← lExprToTFlat (c.pushVars ps) rs b) (← lBlocksToTBlocks c rs rest))
end

/-- `Type 0` packaged `TFlat` function descriptor for runtime lowering pipelines. -/
structure TFlatFn where
  name : Sym
  as : List Ty
  rs : List Ty
  flat : TFlat rs

/-- Reify `TFlatFn` into a well-formed `LeanQbe.T.Fn`. -/
def TFlatFn.toFn (tf : TFlatFn) : Fn :=
  ⟨tf.name, tf.as, tf.rs, denoteFunc tf.flat⟩

/-- Universal `Func.Wf` theorem for every `TFlatFn` via `Func.wf_of_denote`. -/
theorem TFlatFn.toFn_wf (tf : TFlatFn) : tf.toFn.Wf :=
  Func.wf_of_denote tf.flat rfl

/-- Lower a C0 `LFn` to `TFlatFn` after promoting exits and checking `TFlat.wfCheck`. -/
def lFnToTFlatFn (exits : List Sym) (lfn : LFn) : Except String TFlatFn := do
  let body := promoteExitCalls exits lfn.body
  let c0 := ({} : LFlatCtx).pushVars lfn.params
  let tf ← lExprToTFlat c0 lfn.rs body
  let as := lfn.params.map (·.ty)
  if tf.wfCheck (pushTypes as []) [] then
    pure { name := lfn.name, as, rs := lfn.rs, flat := tf }
  else throw s!"lFnToTFlatFn: wfCheck failed on '{lfn.name}'"

/-- Compile C0 source into a list of `TFlatFn`s. -/
def compileC0Source (exits : List Sym) (src : String) : Except String (List TFlatFn) := do
  let tu ← parseC0 src
  let lmod ← lowerTranslationUnit tu
  lmod.fns.mapM (lFnToTFlatFn exits)

end LeanQbe.T.Frontend.C0
