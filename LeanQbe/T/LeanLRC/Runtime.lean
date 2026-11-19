module

public import LeanQbe.T.LeanLRC.Basic
public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public meta import LeanQbe.T.Frontend.C0

/-!
# Tier-0a C0 Runtime & Defunctionalized `lean_apply_k` Generator (`X3-R0`)

Elaborates the Tier-0a `λRC` runtime via `LeanQbe.T.Frontend.C0`:
* `LeanRt` state (`base`, `cur`, `end`, `fuel`, `depth`, `env`)
* 64-bit LE `lean_object` header (`rc` 0-31, `cs_sz` 32-47, `other` 48-55, `tag` 56-63)
* Tagged scalars `(2*n + 1)`, `lean_box`/`lean_unbox`/`lean_obj_tag`
* `lean_rt_enter`/`tick`/`leave`, `lean_alloc_small`/`ctor`, `lean_inc`/`dec`/`is_shared`
* Defunctionalized closures and `genLeanApplyC0` (`jnz` dispatch tree over `fun_id`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLRC

open LeanQbe.T
open LeanQbe.T.Frontend.C0

/-- Runtime abnormal exit symbols used by Tier-0a C0 runtime helpers. -/
def rtExits : List Sym :=
  ["lean_out_of_fuel", "lean_stack_overflow", "lean_oom", "lean_panic"]

/-- Shared C0 struct and extern declarations for the Tier-0a `λRC` runtime. -/
def rtC0Header : String := "#include \"c0.h\"
typedef struct { u64 base; u64 cur; u64 end; u64 fuel; u64 depth; u64 env; } LeanRt;
typedef struct { i32 m_rc; u16 m_cs_sz; u8 m_other; u8 m_tag; } lean_object;
typedef struct { lean_object m_header; u64 m_objs[]; } lean_ctor_object;
typedef struct {
  lean_object m_header; u64 m_fun_id; u16 m_arity; u16 m_num_fixed; u32 m_pad; u64 m_objs[];
} lean_closure_object;
extern void lean_out_of_fuel(u64 rt);
extern void lean_stack_overflow(u64 rt);
extern void lean_oom(u64 rt);
extern void lean_panic(u64 rt);
"

/-! ## Lowered `LExpr` → `TFlat` Bridge (`Func.Wf` via `Func.wf_of_denote`) -/

/-- De Bruijn context mapping C0 `LVar` / label IDs to `TFlat` levels and types. -/
structure LFlatCtx where
  vdepth : Nat := 0
  ldepth : Nat := 0
  vars : List (Nat × Nat × Ty) := []
  lbls : List (Nat × Nat × List Ty) := []

def LFlatCtx.pushVar (c : LFlatCtx) (lv : LVar) : LFlatCtx :=
  { c with vdepth := c.vdepth + 1, vars := (lv.id, c.vdepth, lv.ty) :: c.vars }

def LFlatCtx.pushVars (c : LFlatCtx) (lvs : List LVar) : LFlatCtx :=
  lvs.foldl LFlatCtx.pushVar c

def LFlatCtx.pushLbl (c : LFlatCtx) (lid : Nat) (ts : List Ty) : LFlatCtx :=
  { c with ldepth := c.ldepth + 1, lbls := (lid, c.ldepth, ts) :: c.lbls }

def LFlatCtx.lookupVar (c : LFlatCtx) (id : Nat) (t : Ty) : Except String (Arg K t) :=
  match c.vars.find? (fun p => p.1 == id) with
  | some (_, lvl, t') =>
    if _ : t' = t then pure (.var (c.vdepth - 1 - lvl))
    else throw s!"LFlatCtx: variable {id} type mismatch"
  | none => throw s!"LFlatCtx: unbound variable {id}"

def LFlatCtx.lookupLbl (c : LFlatCtx) (lid : Nat) (ts : List Ty) : Except String Nat :=
  match c.lbls.find? (fun p => p.1 == lid) with
  | some (_, lvl, ts') =>
    if ts' == ts then pure (c.ldepth - 1 - lvl)
    else throw s!"LFlatCtx: label {lid} signature mismatch"
  | none => throw s!"LFlatCtx: unbound label {lid}"

def toFlatArg (c : LFlatCtx) (t : Ty) : LArg → Except String (Arg K t)
  | .var id t' => if t' == t then c.lookupVar id t else throw s!"toFlatArg: var {id} ty"
  | .imm t' v => if h : t' = t then pure (.imm (h ▸ v)) else throw "toFlatArg: imm ty"

def toFlatArgs (c : LFlatCtx) : (ts : List Ty) → List LArg → Except String (Tup (Arg K) ts)
  | [], [] => pure ()
  | t :: ts, a :: as => do pure (← toFlatArg c t a, ← toFlatArgs c ts as)
  | _, _ => throw "toFlatArgs: arity mismatch"

mutual
/-- Promote calls to runtime exit symbols into `.exit` terminators. -/
def promoteExitCalls (exits : List Sym) : LExpr → LExpr
  | .let_ op bs k => .let_ op bs (promoteExitCalls exits k)
  | .load t a b k => .load t a b (promoteExitCalls exits k)
  | .store t v a k => .store t v a (promoteExitCalls exits k)
  | .call f as bs args binders k =>
    if exits.contains f then .exit f as args
    else .call f as bs args binders (promoteExitCalls exits k)
  | .jnz c t e => .jnz c (promoteExitCalls exits t) (promoteExitCalls exits e)
  | .jump l ts args => .jump l ts args
  | .ret rs args => .ret rs args
  | .exit f as args => .exit f as args
  | .hlt => .hlt
  | .group blks k => .group (promoteExitBlocks exits blks) (promoteExitCalls exits k)

def promoteExitBlocks (exits : List Sym) :
    List (Nat × List LVar × LExpr) → List (Nat × List LVar × LExpr)
  | [] => []
  | (l, ps, b) :: rest => (l, ps, promoteExitCalls exits b) :: promoteExitBlocks exits rest
end

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

/-! ## Meta Elaboration of Static Tier-0a Runtime Definitions -/

meta section
open Lean Elab Command

def metaRtExits : List Sym :=
  ["lean_out_of_fuel", "lean_stack_overflow", "lean_oom", "lean_panic"]

mutual
def metaPromoteExits (exits : List Sym) : LExpr → LExpr
  | .let_ op bs k => .let_ op bs (metaPromoteExits exits k)
  | .load t a b k => .load t a b (metaPromoteExits exits k)
  | .store t v a k => .store t v a (metaPromoteExits exits k)
  | .call f as bs args binders k =>
    if exits.contains f then .exit f as args
    else .call f as bs args binders (metaPromoteExits exits k)
  | .jnz c t e => .jnz c (metaPromoteExits exits t) (metaPromoteExits exits e)
  | .jump l ts args => .jump l ts args
  | .ret rs args => .ret rs args
  | .exit f as args => .exit f as args
  | .hlt => .hlt
  | .group blks k => .group (metaPromoteBlocks exits blks) (metaPromoteExits exits k)

def metaPromoteBlocks (exits : List Sym) :
    List (Nat × List LVar × LExpr) → List (Nat × List LVar × LExpr)
  | [] => []
  | (l, ps, b) :: rest => (l, ps, metaPromoteExits exits b) :: metaPromoteBlocks exits rest
end

/-- Elaborate a C0 runtime translation unit directly into kernel `<name>_body` / `<name>` defs,
promoting runtime exit calls into `.exit` terminators. -/
elab "lrc_elab_rt_c0!" pfx:ident src:str : command => do
  let tu ← match parseC0 src.getString with
    | .ok t => pure t | .error err => throwError err
  let lmod ← match lowerTranslationUnit tu with
    | .ok m => pure m | .error err => throwError err
  let lmod' : LModule := {
    lmod with
    fns := lmod.fns.map fun f => { f with body := metaPromoteExits metaRtExits f.body }
  }
  if let .error err := checkLModuleAcyclic lmod' then throwError err
  let ns ← getCurrNamespace
  let mut fnConstNames : List Name := []
  for lfn in lmod'.fns do
    let leanName := ns ++ Name.mkSimple lfn.name
    let bodyName := ns ++ Name.mkSimple (lfn.name ++ "_body")
    let (funcExpr, asExpr, rsExpr) ← liftTermElabM (lFnToLeanExprM lfn)
    let funcTy := mkApp2 (Lean.mkConst ``LeanQbe.T.Func) asExpr rsExpr
    liftCoreM <| do
      let bDecl := .defnDecl {
        name := bodyName, levelParams := [], type := funcTy, value := funcExpr,
        hints := .regular 0, safety := .safe
      }
      addDecl bDecl (forceExpose := true)
      compileDecl bDecl
      enableRealizationsForConst bodyName
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let fnExpr := mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk)
      (mkStrLit lfn.name) asExpr rsExpr (Lean.mkConst bodyName)
    liftCoreM <| do
      let fDecl := .defnDecl {
        name := leanName, levelParams := [], type := fnTy, value := fnExpr,
        hints := .regular 0, safety := .safe
      }
      addDecl fDecl (forceExpose := true)
      compileDecl fDecl
      enableRealizationsForConst leanName
    fnConstNames := fnConstNames ++ [leanName]
  let fnType := Lean.mkConst ``LeanQbe.T.Fn
  let fnsName := ns ++ Name.mkSimple (pfx.getId.toString ++ "_fns")
  let fnsTy := mkApp (Lean.mkConst ``List [.one]) fnType
  let fnsVal := (fnConstNames.map Lean.mkConst).foldr
    (fun e acc => mkApp3 (Lean.mkConst ``List.cons [.one]) fnType e acc)
    (mkApp (Lean.mkConst ``List.nil [.one]) fnType)
  liftCoreM <| do
    let lDecl := .defnDecl {
      name := fnsName, levelParams := [], type := fnsTy, value := fnsVal,
      hints := .regular 0, safety := .safe
    }
    addDecl lDecl (forceExpose := true)
    compileDecl lDecl
    enableRealizationsForConst fnsName

end

/- Static Tier-0a C0 runtime elaborated directly via `LeanQbe.T.Frontend.C0`. -/
lrc_elab_rt_c0! rtBase "#include \"c0.h\"
typedef struct { u64 base; u64 cur; u64 end; u64 fuel; u64 depth; u64 env; } LeanRt;
typedef struct { i32 m_rc; u16 m_cs_sz; u8 m_other; u8 m_tag; } lean_object;
typedef struct { lean_object m_header; u64 m_objs[]; } lean_ctor_object;
typedef struct {
  lean_object m_header; u64 m_fun_id; u16 m_arity; u16 m_num_fixed; u32 m_pad; u64 m_objs[];
} lean_closure_object;
extern void lean_out_of_fuel(u64 rt);
extern void lean_stack_overflow(u64 rt);
extern void lean_oom(u64 rt);
extern void lean_panic(u64 rt);

bool lean_is_scalar(u64 o) { return (o & 1ULL) != 0ULL; }
u64 lean_box(u64 n) { return (n << 1) | 1ULL; }
u64 lean_unbox(u64 o) { return o >> 1; }
u64 lean_obj_tag(u64 o) {
  if ((o & 1ULL) != 0ULL) { return o >> 1; }
  u64 hdr = *(u64 *)o;
  return (hdr >> 56) & 0xFFULL;
}
void lean_rt_enter(u64 rt_raw) {
  LeanRt *rt = (LeanRt *)rt_raw;
  if (rt->fuel == 0ULL) { lean_out_of_fuel(rt_raw); return; }
  rt->fuel = rt->fuel - 1ULL;
  if (rt->depth == 0ULL) { lean_stack_overflow(rt_raw); return; }
  rt->depth = rt->depth - 1ULL;
}
void lean_rt_tick(u64 rt_raw) {
  LeanRt *rt = (LeanRt *)rt_raw;
  if (rt->fuel == 0ULL) { lean_out_of_fuel(rt_raw); return; }
  rt->fuel = rt->fuel - 1ULL;
}
void lean_rt_leave(u64 rt_raw) {
  LeanRt *rt = (LeanRt *)rt_raw;
  rt->depth = rt->depth + 1ULL;
}
u64 lean_alloc_small(u64 rt_raw, u64 bytes) {
  LeanRt *rt = (LeanRt *)rt_raw;
  u64 aligned = (bytes + 7ULL) & (~7ULL);
  u64 cur = rt->cur;
  if (aligned > rt->end - cur) { lean_oom(rt_raw); return 0ULL; }
  rt->cur = cur + aligned;
  return cur;
}
u64 lean_alloc_ctor(u64 rt_raw, u64 cidx, u64 num_objs, u64 scalar_bytes) {
  u64 total = 8ULL + num_objs * 8ULL + scalar_bytes;
  u64 obj = lean_alloc_small(rt_raw, total);
  u64 aligned = (total + 7ULL) & (~7ULL);
  u64 hdr = 1ULL | ((aligned & 0xFFFFULL) << 32)
    | ((num_objs & 0xFFULL) << 48) | ((cidx & 0xFFULL) << 56);
  *(u64 *)obj = hdr;
  return obj;
}
u64 lean_ctor_get(u64 o, u64 i) {
  lean_ctor_object *c = (lean_ctor_object *)o; return c->m_objs[i];
}
void lean_ctor_set(u64 o, u64 i, u64 v) {
  lean_ctor_object *c = (lean_ctor_object *)o; c->m_objs[i] = v;
}
void lean_ctor_set_tag(u64 o, u8 tag) { lean_object *obj = (lean_object *)o; obj->m_tag = tag; }
void lean_inc(u64 o) {
  if ((o & 1ULL) == 0ULL && o != 0ULL) {
    lean_object *obj = (lean_object *)o;
    i32 rc = obj->m_rc;
    if (rc > 0) { obj->m_rc = rc + 1; }
  }
}
void lean_dec(u64 o) {
  if ((o & 1ULL) == 0ULL && o != 0ULL) {
    lean_object *obj = (lean_object *)o;
    i32 rc = obj->m_rc;
    if (rc > 0) { obj->m_rc = rc - 1; }
  }
}
u8 lean_is_shared(u64 o) {
  if ((o & 1ULL) != 0ULL || o == 0ULL) { return (u8)1; }
  lean_object *obj = (lean_object *)o;
  if (obj->m_rc == 1) { return (u8)0; }
  return (u8)1;
}
u64 lean_alloc_closure(u64 rt_raw, u64 fun_id, u64 arity, u64 num_fixed) {
  u64 total = 24ULL + num_fixed * 8ULL;
  u64 obj = lean_alloc_small(rt_raw, total);
  u64 hdr = 1ULL | ((total & 0xFFFFULL) << 32) | (245ULL << 56);
  *(u64 *)obj = hdr;
  lean_closure_object *cl = (lean_closure_object *)obj;
  cl->m_fun_id = fun_id;
  cl->m_arity = (u16)arity;
  cl->m_num_fixed = (u16)num_fixed;
  cl->m_pad = (u32)0;
  return obj;
}
u64 lean_closure_get(u64 c, u64 i) {
  lean_closure_object *cl = (lean_closure_object *)c; return cl->m_objs[i];
}
void lean_closure_set(u64 c, u64 i, u64 v) {
  lean_closure_object *cl = (lean_closure_object *)c; cl->m_objs[i] = v;
}
u64 lean_box_u64(u64 rt_raw, u64 v) {
  u64 obj = lean_alloc_ctor(rt_raw, 0ULL, 0ULL, 8ULL);
  lean_ctor_object *c = (lean_ctor_object *)obj; c->m_objs[0] = v; return obj;
}
u64 lean_unbox_u64(u64 o) { lean_ctor_object *c = (lean_ctor_object *)o; return c->m_objs[0]; }
u64 lean_nat_add(u64 rt_raw, u64 a, u64 b) {
  if ((a & 1ULL) == 0ULL || (b & 1ULL) == 0ULL) { lean_panic(rt_raw); return 1ULL; }
  u64 na = a >> 1; u64 nb = b >> 1;
  if (na > 0x7FFFFFFFFFFFFFFFULL - nb) { lean_panic(rt_raw); return 1ULL; }
  return ((na + nb) << 1) | 1ULL;
}
u64 lean_nat_sub(u64 rt_raw, u64 a, u64 b) {
  if ((a & 1ULL) == 0ULL || (b & 1ULL) == 0ULL) { lean_panic(rt_raw); return 1ULL; }
  u64 na = a >> 1; u64 nb = b >> 1;
  u64 r = (na > nb) ? (na - nb) : 0ULL;
  return (r << 1) | 1ULL;
}
u64 lean_nat_mul(u64 rt_raw, u64 a, u64 b) {
  if ((a & 1ULL) == 0ULL || (b & 1ULL) == 0ULL) { lean_panic(rt_raw); return 1ULL; }
  u64 na = a >> 1; u64 nb = b >> 1;
  if (na != 0ULL && nb > 0x7FFFFFFFFFFFFFFFULL / na) { lean_panic(rt_raw); return 1ULL; }
  return ((na * nb) << 1) | 1ULL;
}
u64 lean_nat_div(u64 rt_raw, u64 a, u64 b) {
  if ((a & 1ULL) == 0ULL || (b & 1ULL) == 0ULL) { lean_panic(rt_raw); return 1ULL; }
  u64 na = a >> 1; u64 nb = b >> 1;
  u64 r = (nb == 0ULL) ? 0ULL : (na / nb);
  return (r << 1) | 1ULL;
}
u64 lean_nat_mod(u64 rt_raw, u64 a, u64 b) {
  if ((a & 1ULL) == 0ULL || (b & 1ULL) == 0ULL) { lean_panic(rt_raw); return 1ULL; }
  u64 na = a >> 1; u64 nb = b >> 1;
  u64 r = (nb == 0ULL) ? na : (na % nb);
  return (r << 1) | 1ULL;
}
u8 lean_nat_dec_eq(u64 a, u64 b) {
  if ((a & 1ULL) == 0ULL || (b & 1ULL) == 0ULL) { return (u8)0; }
  return (a == b) ? (u8)1 : (u8)0;
}
u8 lean_nat_dec_le(u64 a, u64 b) {
  if ((a & 1ULL) == 0ULL || (b & 1ULL) == 0ULL) { return (u8)0; }
  return ((a >> 1) <= (b >> 1)) ? (u8)1 : (u8)0;
}
u8 lean_nat_dec_lt(u64 a, u64 b) {
  if ((a & 1ULL) == 0ULL || (b & 1ULL) == 0ULL) { return (u8)0; }
  return ((a >> 1) < (b >> 1)) ? (u8)1 : (u8)0;
}
"

/-! ## Generator for Per-Arity `lean_apply_k` (`jnz` Binary Dispatch Tree) -/

/-- Render `u64 a0, u64 a1, ...` parameter or argument list for `k` arguments. -/
def mkApplyArgList (k : Nat) (withTypes : Bool) : String :=
  String.intercalate ", " <| (List.range k).map fun i =>
    if withTypes then s!"u64 a{i}" else s!"a{i}"

/-- Render a call `fnName(rt_raw, c0, ..., a0, ...)` loading captured closure fields. -/
def genSaturationLeaf (t : LrcClosureTarget) (k : Nat) : String :=
  let nfix := t.arity - k
  let loadCaps := String.join <| (List.range nfix).map fun i =>
    s!"      u64 c{i} = lean_closure_get(clo_raw, {i}ULL);\n      lean_inc(c{i});\n"
  let capArgs := (List.range nfix).map fun i => s!"c{i}"
  let appArgs := (List.range k).map fun i => s!"a{i}"
  let allArgs := String.intercalate ", " ("rt_raw" :: (capArgs ++ appArgs))
  loadCaps ++
  s!"      lean_dec(clo_raw);\n      u64 res = {t.fnName}({allArgs});\n" ++
  s!"      lean_rt_leave(rt_raw);\n      return res;\n"

/-- Build a balanced binary `jnz` dispatch tree over `fun_id` for exact arity `k`. -/
def genDispatchTree : List LrcClosureTarget → Nat → Nat → String
  | [], _, _ => "    lean_panic(rt_raw);\n    return 1ULL;\n"
  | [t], k, _ =>
    s!"    if (fid == {t.funId}ULL) \{\n" ++ genSaturationLeaf t k ++
    "    } else {\n      lean_panic(rt_raw);\n      return 1ULL;\n    }\n"
  | ts, k, fuel =>
    match fuel with
    | 0 => "    lean_panic(rt_raw);\n    return 1ULL;\n"
    | fuel' + 1 =>
      let mid := ts.length / 2
      let left := ts.take mid
      let right := ts.drop mid
      let pivotId := (right.head?.map (·.funId)).getD 0
      s!"    if (fid < {pivotId}ULL) \{\n" ++
      genDispatchTree left k fuel' ++
      "    } else {\n" ++
      genDispatchTree right k fuel' ++
      "    }\n"

/-- Generate C0 source for `lean_apply_k(u64 rt_raw, u64 clo_raw, u64 a0, ..., u64 a_{k-1})`. -/
def genLeanApplyC0 (targets : List LrcClosureTarget) (k : Nat) : String :=
  let rtDecls :=
    "extern void lean_rt_enter(u64 rt_raw);\n" ++
    "extern void lean_rt_leave(u64 rt_raw);\n" ++
    "extern u64 lean_alloc_closure(u64 rt_raw, u64 fun_id, u64 arity, u64 num_fixed);\n" ++
    "extern u64 lean_closure_get(u64 c, u64 i);\n" ++
    "extern void lean_closure_set(u64 c, u64 i, u64 v);\n" ++
    "extern void lean_inc(u64 o);\n" ++
    "extern void lean_dec(u64 o);\n"
  let prevApplies := String.join <| (List.range (k - 1)).map fun idx =>
    let r := idx + 1
    s!"extern u64 lean_apply_{r}(u64 rt_raw, u64 clo_raw, {mkApplyArgList r true});\n"
  let targetDecls := String.join <| targets.map fun t =>
    let ps := String.intercalate ", "
      ("u64 rt_raw" :: (List.range t.arity).map fun i => s!"u64 x{i}")
    s!"extern u64 {t.fnName}({ps});\n"
  let exactTargets :=
    (targets.filter fun t => t.arity >= k).mergeSort (fun a b => a.funId ≤ b.funId)
  let underSets := String.join <| (List.range k).map fun i =>
    s!"    lean_closure_set(c2, nfix + {i}ULL, a{i});\n"
  let overBranches := String.join <| (List.range (k - 1)).map fun idx =>
    let r := idx + 1
    let rArgs := String.intercalate ", " ((List.range r).map fun i => s!"a{i}")
    let remArgs := String.intercalate ", " ((List.range (k - r)).map fun i => s!"a{r + i}")
    s!"  if (rem == {r}ULL) \{\n" ++
    s!"    u64 tmp = lean_apply_{r}(rt_raw, clo_raw, {rArgs});\n" ++
    s!"    u64 res = lean_apply_{k - r}(rt_raw, tmp, {remArgs});\n" ++
    s!"    lean_rt_leave(rt_raw);\n    return res;\n  }\n"
  let paramsStr := mkApplyArgList k true
  let tree := genDispatchTree exactTargets k (exactTargets.length + 2)
  rtC0Header ++ rtDecls ++ prevApplies ++ targetDecls ++ "\n" ++
  s!"u64 lean_apply_{k}(u64 rt_raw, u64 clo_raw, {paramsStr}) \{\n" ++
  "  lean_rt_enter(rt_raw);\n  lean_closure_object *cl = (lean_closure_object *)clo_raw;\n" ++
  "  u64 fid = cl->m_fun_id;\n  u64 arity = (u64)cl->m_arity;\n" ++
  "  u64 nfix = (u64)cl->m_num_fixed;\n" ++
  "  if (nfix >= arity) { lean_panic(rt_raw); return 1ULL; }\n" ++
  "  u64 rem = arity - nfix;\n" ++
  s!"  if (rem > {k}ULL) \{\n" ++
  s!"    u64 c2 = lean_alloc_closure(rt_raw, fid, arity, nfix + {k}ULL);\n" ++
  "    u64 i = 0ULL;\n    while (i < nfix) {\n" ++
  "      u64 cap = lean_closure_get(clo_raw, i);\n      lean_inc(cap);\n" ++
  "      lean_closure_set(c2, i, cap);\n      i = i + 1ULL;\n    }\n" ++
  underSets ++
  "    lean_dec(clo_raw);\n    lean_rt_leave(rt_raw);\n    return c2;\n  }\n" ++
  overBranches ++ tree ++ "}\n"

/-- Lower generated `lean_apply_k` (`k ≥ 1`) via C0 frontend to a verified `TFlatFn`. -/
def genLeanApplyTFlatFn (targets : List LrcClosureTarget) (k : Nat) : Except String TFlatFn := do
  if k == 0 then throw "genLeanApplyTFlatFn: arity k must be ≥ 1"
  let fns ← compileC0Source rtExits (genLeanApplyC0 targets k)
  match fns with
  | [fn] => pure fn
  | _ => throw "genLeanApplyTFlatFn: expected single function"

/-- Lower `lean_apply_1 .. lean_apply_maxK` for closure table `targets`. -/
def genLeanApplyTFlatFns (targets : List LrcClosureTarget) (maxK : Nat) :
    Except String (List TFlatFn) :=
  (List.range maxK).mapM fun idx => genLeanApplyTFlatFn targets (idx + 1)

end LeanQbe.T.LeanLRC
