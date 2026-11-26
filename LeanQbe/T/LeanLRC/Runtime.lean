module

public import LeanQbe.T.LeanLRC.Basic
public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public meta import LeanQbe.T.LeanLRC.Basic
public meta import LeanQbe.T.Frontend.C0

/-!
# Minimal C0 Runtime & Defunctionalized `lean_apply_k` Generator

Elaborates the minimal `λRC` C0 runtime via `LeanQbe.T.Frontend.C0`:
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

/-- Shared C0 struct and extern declarations for the `λRC` runtime. -/
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

/-! ## Meta Elaboration of Static Runtime Definitions -/

meta section
open Lean Elab Command

/-- Elaborate a C0 runtime translation unit directly into kernel `<name>_body` / `<name>` defs
and `<pfx>_fns` (all `forceExpose`d, no `#c0_shape` metadata, no `<pfx>_module`), promoting
runtime exit calls into `.exit` terminators. -/
elab "lrc_elab_rt_c0!" pfx:ident src:str : command =>
  elabC0Module (some pfx.getId) src.getString rtExits (forceExpose := true)
    (registerShapes := false) (emitModule := false)

end

/- Static C0 runtime elaborated directly via `LeanQbe.T.Frontend.C0`. -/
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

/-- Lower generated `lean_apply_k` (`k ≥ 1`) via C0 frontend to a verified `Frontend.C0.TFlatFn`. -/
def genLeanApplyTFlatFn (targets : List LrcClosureTarget) (k : Nat) :
    Except String Frontend.C0.TFlatFn := do
  if k == 0 then throw "genLeanApplyTFlatFn: arity k must be ≥ 1"
  let fns ← compileC0Source rtExits (genLeanApplyC0 targets k)
  match fns with
  | [fn] => pure fn
  | _ => throw "genLeanApplyTFlatFn: expected single function"

/-- Lower `lean_apply_1 .. lean_apply_maxK` for closure table `targets`. -/
def genLeanApplyTFlatFns (targets : List LrcClosureTarget) (maxK : Nat) :
    Except String (List Frontend.C0.TFlatFn) :=
  (List.range maxK).mapM fun idx => genLeanApplyTFlatFn targets (idx + 1)

end LeanQbe.T.LeanLRC
