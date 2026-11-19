module

public import LeanQbe.T.LeanLRC.Runtime
public import LeanQbe.T.Module
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe

/-!
# `λRC` → `LeanQbe.T` Lowering, Benchmarks & Real `Lean.IR` Splicing (`X3-R0`)

Lowers typed `λRC` / `Lean.IR` modules (`LrcModule`) to scope-checked `LeanQbe.T.TFlat`
(`TFlatFn`) and reified PHOAS `Fn` / `Module`:
* Explicit `rt : i64` (`LeanRt *`) threaded as argument `0` of every lowered function and
  runtime allocator/arithmetic call.
* Entry calls `lean_rt_enter(rt)`, tail self-calls lower to `loop1` + `lean_rt_tick(rt)`,
  non-tail/mutual calls lower to `.call`, returns emit `lean_rt_leave(rt)` before `.ret`.
* `jdecl`/`jmp` lower to single-block `.group`/`.jump`; `reset`/`reuse` fall back to fresh
  `ctor` allocation; `pap`/`ap` lower to `lean_alloc_closure` + `lean_apply_k`.
* Includes 4 benchmark/validation `LrcModule`s (`sumToMod`, `mapAddMod`, `tree2Mod`,
  `foldMapMod`) plus `realLeanIrMod` spliced directly from real Lean 4 definitions via
  `lrc_of_lean!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLRC

open LeanQbe.T
open LeanQbe.T.Frontend.C0 (TFlatFn)

/-! ## Lowering Context & Type-Safe Argument Coercion -/

/-- De Bruijn lowering context for a single `LrcFn` -> `TFlat` pass. -/
structure LrcBuildCtx where
  fnName : String
  vdepth : Nat := 0
  ldepth : Nat := 0
  rtLvl : Nat := 0
  vars : List (Nat × Nat × LrcTy) := []
  jps : List (Nat × Nat × List LrcTy) := []
  loop? : Option (Nat × List Ty) := none

/-- Push a named or anonymous variable at `ctx.vdepth` with type `ty`. -/
def LrcBuildCtx.pushVar (c : LrcBuildCtx) (id? : Option Nat) (ty : LrcTy) :
    Nat × LrcBuildCtx :=
  let lvl := c.vdepth
  let vs := match id? with | some id => (id, lvl, ty) :: c.vars | none => c.vars
  (lvl, { c with vdepth := lvl + 1, vars := vs })

/-- Push a parameter list onto `ctx` left-to-right (matching `pushTypes`). -/
def LrcBuildCtx.pushParams (c : LrcBuildCtx) (ps : List LrcParam) : LrcBuildCtx :=
  ps.foldl (fun acc p => (acc.pushVar (some p.id) p.ty).2) c

/-- Push a join-point label at `ctx.ldepth` with parameter `LrcTy`s `ts`. -/
def LrcBuildCtx.pushJp (c : LrcBuildCtx) (jpId : Nat) (ts : List LrcTy) :
    Nat × LrcBuildCtx :=
  let lvl := c.ldepth
  (lvl, { c with ldepth := lvl + 1, jps := (jpId, lvl, ts) :: c.jps })

/-- Convert a de Bruijn variable level to a current de Bruijn index `.var`. -/
def LrcBuildCtx.varAt (c : LrcBuildCtx) (lvl : Nat) {t : Ty} : Arg K t :=
  .var (c.vdepth - 1 - lvl)

/-- Look up an LRC variable `id` in `c`, returning `(lvl, lrcTy)`. -/
def LrcBuildCtx.lookupVar (c : LrcBuildCtx) (id : Nat) : Except String (Nat × LrcTy) :=
  match c.vars.find? (fun p => p.1 == id) with
  | some (_, lvl, ty) => pure (lvl, ty)
  | none => throw s!"LeanLRC ({c.fnName}): unbound variable x_{id}"

/-- Look up a join point `jpId` in `c`, returning `(lvl, paramTys)`. -/
def LrcBuildCtx.lookupJp (c : LrcBuildCtx) (jpId : Nat) : Except String (Nat × List LrcTy) :=
  match c.jps.find? (fun p => p.1 == jpId) with
  | some (_, lvl, ts) => pure (lvl, ts)
  | none => throw s!"LeanLRC ({c.fnName}): unbound join point jp_{jpId}"

/-- Callee metadata used while lowering `fap`. -/
structure LrcCalleeSig where
  srcName : String
  cName : String
  params : List LrcTy
  retTy : LrcTy
  takesRt : Bool

/-- Build an `LrcExtern` list from compact `(name, params, retTy)` specs. -/
def mkRtExts (specs : List (String × List LrcTy × LrcTy)) : List LrcExtern :=
  specs.map fun (nm, ps, r) => { name := nm, cName := nm, params := ps, retTy := r }

/-- Runtime externs expecting `rt : i64` as first C ABI parameter. -/
def rtWithRtExterns : List LrcExtern := mkRtExts
  [ ("lean_alloc_small", [.uint64], .uint64)
  , ("lean_alloc_ctor", [.uint64, .uint64, .uint64], .tobject)
  , ("lean_alloc_closure", [.uint64, .uint64, .uint64], .tobject)
  , ("lean_box_u64", [.uint64], .tobject)
  , ("lean_nat_add", [.tobject, .tobject], .tobject)
  , ("lean_nat_sub", [.tobject, .tobject], .tobject)
  , ("lean_nat_mul", [.tobject, .tobject], .tobject)
  , ("lean_nat_div", [.tobject, .tobject], .tobject)
  , ("lean_nat_mod", [.tobject, .tobject], .tobject)
  ]

/-- Runtime externs taking no `rt` pointer. -/
def rtNoRtExterns : List LrcExtern := mkRtExts
  [ ("lean_is_scalar", [.tobject], .uint8)
  , ("lean_box", [.uint64], .tobject)
  , ("lean_unbox", [.tobject], .uint64)
  , ("lean_obj_tag", [.tobject], .uint64)
  , ("lean_ctor_get", [.tobject, .uint64], .tobject)
  , ("lean_ctor_set", [.tobject, .uint64, .tobject], .void)
  , ("lean_ctor_set_tag", [.tobject, .uint8], .void)
  , ("lean_inc", [.tobject], .void)
  , ("lean_dec", [.tobject], .void)
  , ("lean_is_shared", [.tobject], .uint8)
  , ("lean_closure_get", [.tobject, .uint64], .tobject)
  , ("lean_closure_set", [.tobject, .uint64, .tobject], .void)
  , ("lean_unbox_u64", [.tobject], .uint64)
  , ("lean_nat_dec_eq", [.tobject, .tobject], .uint8)
  , ("lean_nat_dec_le", [.tobject, .tobject], .uint8)
  , ("lean_nat_dec_lt", [.tobject, .tobject], .uint8)
  ]

def rtWithRtNames : List String := rtWithRtExterns.map (·.cName)

/-- Resolve an `LrcExtern` / internal `LrcFn` call target to `LrcCalleeSig`. -/
def resolveCallee (fns : List LrcFn) (exts : List LrcExtern) (nm : String) :
    Except String LrcCalleeSig :=
  let ofExt (takesRt : Bool) (ex : LrcExtern) : LrcCalleeSig :=
    { srcName := nm, cName := ex.cName, params := ex.params, retTy := ex.retTy, takesRt }
  match fns.find? (fun f => f.name == nm) with
  | some fn => pure
    { srcName := nm, cName := mangleSym fn.name
      params := fn.params.map (·.ty), retTy := fn.retTy, takesRt := true }
  | none =>
    match exts.find? (fun e => e.name == nm || e.cName == nm) with
    | some ex => pure (ofExt (rtWithRtNames.contains ex.cName) ex)
    | none =>
      match rtWithRtExterns.find? (fun e => e.name == nm) with
      | some ex => pure (ofExt true ex)
      | none =>
        match rtNoRtExterns.find? (fun e => e.name == nm) with
        | some ex => pure (ofExt false ex)
        | none => throw s!"LeanLRC: unknown call target '{nm}'"

/-- Construct a typed immediate `Arg K ty.toTTy` from a `Nat` without width casts. -/
def lrcImmArg (ty : LrcTy) (n : Nat) : Arg K ty.toTTy :=
  match ty with
  | .uint8 => .imm (BitVec.ofNat 8 n)
  | .uint16 => .imm (BitVec.ofNat 16 n)
  | .uint32 => .imm (BitVec.ofNat 32 n)
  | .uint64 | .usize | .object | .tobject | .tagged | .erased | .void =>
    .imm (BitVec.ofNat 64 n)

/-- Encode a literal `LrcVal` cleanly at expected `LrcTy`. -/
def encodeLitVal (fnName : String) (v : LrcVal) (ty : LrcTy) : Except String Nat :=
  match v with
  | .num n => pure (if ty.isScalar then n else 2 * n + 1)
  | .bool b =>
    let n := if b then 1 else 0
    pure (if ty.isScalar then n else 2 * n + 1)
  | .erased => pure (if ty.isScalar then 0 else 1)
  | .str _ => throw s!"LeanLRC ({fnName}): string literals unsupported in Tier-0a"

/-- Coerce a bound variable `srcLvl` (with `srcTy`) into a fresh variable at `dstTy` if widths
differ, continuing with `k dstLvl ctx'`. -/
def coerceLvl {rs : List Ty} (c : LrcBuildCtx) (srcLvl : Nat) (srcTy dstTy : LrcTy)
    (k : Nat → LrcBuildCtx → Except String (TFlat rs)) : Except String (TFlat rs) := do
  let sT := srcTy.toTTy
  let dT := dstTy.toTTy
  if sT == dT then
    k srcLvl c
  else
    match sT, dT with
    | .bits m, .bits n =>
      let (outLvl, c') := c.pushVar none dstTy
      let body ← k outLvl c'
      if m ≤ n then
        pure (.let_ ⟨OpCode.zext m n, (.var (c.vdepth - 1 - srcLvl), ())⟩ body)
      else
        pure (.let_ ⟨OpCode.trunc m n, (.var (c.vdepth - 1 - srcLvl), ())⟩ body)
    | _, _ => throw s!"LeanLRC ({c.fnName}): incompatible types {repr sT} -> {repr dT}"

/-- Materialize an `LrcArg` as a variable level of type `dstTy` before running `k`. -/
def materializeArg {rs : List Ty} (c : LrcBuildCtx) (arg : LrcArg) (dstTy : LrcTy)
    (k : Nat → LrcBuildCtx → Except String (TFlat rs)) : Except String (TFlat rs) := do
  match arg with
  | .var id =>
    let (lvl, srcTy) ← c.lookupVar id
    coerceLvl c lvl srcTy dstTy k
  | .val v =>
    let n ← encodeLitVal c.fnName v dstTy
    let (lvl, c') := c.pushVar none dstTy
    let body ← k lvl c'
    pure (.let_ ⟨OpCode.copy dstTy.toTTy, (lrcImmArg dstTy n, ())⟩ body)
  | .erased =>
    let n := if dstTy.isScalar then 0 else 1
    let (lvl, c') := c.pushVar none dstTy
    let body ← k lvl c'
    pure (.let_ ⟨OpCode.copy dstTy.toTTy, (lrcImmArg dstTy n, ())⟩ body)

/-- Materialize a list of `(LrcArg × LrcTy)` pairs in left-to-right order. -/
def materializePairs {rs : List Ty} (c : LrcBuildCtx) :
    List (LrcArg × LrcTy) → (List Nat → LrcBuildCtx → Except String (TFlat rs)) →
    Except String (TFlat rs)
  | [], k => k [] c
  | (a, ty) :: rest, k =>
    materializeArg c a ty fun lvl c' =>
      materializePairs c' rest fun lvls c'' =>
        k (lvl :: lvls) c''

/-- Build a `Tup (Arg K) ts` from aligned `(lvl, ty)` pairs. -/
def buildCallTuple (c : LrcBuildCtx) :
    (lvls : List Nat) → (ts : List Ty) → Except String (Tup (Arg K) ts)
  | [], [] => pure ()
  | lvl :: lvls, _ :: ts => do pure (c.varAt lvl, ← buildCallTuple c lvls ts)
  | _, _ => throw s!"LeanLRC ({c.fnName}): call argument tuple length mismatch"

/-- Emit `.call sym args -> [resTy]`, passing `resLvl` to `k`. -/
def emitCall1 {rs : List Ty} (c : LrcBuildCtx) (sym : Sym)
    (argTys : List Ty) (argLvls : List Nat) (resTy : LrcTy)
    (k : Nat → LrcBuildCtx → Except String (TFlat rs)) : Except String (TFlat rs) := do
  let tup ← buildCallTuple c argLvls argTys
  let (resLvl, c') := c.pushVar none resTy
  let rest ← k resLvl c'
  pure (.call sym [resTy.toTTy] tup rest)

/-- Emit void `.call sym args -> []`, continuing with `k c`. -/
def emitCall0 {rs : List Ty} (c : LrcBuildCtx) (sym : Sym)
    (argTys : List Ty) (argLvls : List Nat)
    (k : LrcBuildCtx → Except String (TFlat rs)) : Except String (TFlat rs) := do
  let tup ← buildCallTuple c argLvls argTys
  let rest ← k c
  pure (.call sym [] tup rest)

/-- Emit `lean_ctor_set` or `lean_closure_set` sequentially for indexed object fields. -/
def emitFieldSets {rs : List Ty} (c : LrcBuildCtx) (setterSym : Sym) (objLvl : Nat) :
    Nat → List Nat → (LrcBuildCtx → Except String (TFlat rs)) → Except String (TFlat rs)
  | _, [], k => k c
  | idx, aLvl :: rest, k =>
    let (idxLvl, c1) := c.pushVar none .uint64
    emitFieldSets c1 setterSym objLvl (idx + 1) rest k >>= fun inner =>
      let args : Tup (Arg K) [i64, i64, i64] :=
        (c1.varAt objLvl, c1.varAt idxLvl, c1.varAt aLvl, ())
      pure (.let_ ⟨OpCode.copy i64, (.imm (BitVec.ofNat 64 idx), ())⟩
        (.call setterSym [] args inner))

/-- Emit `n` calls to `lean_inc` or `lean_dec` when `!persistent` on an object variable. -/
def emitRefcountN {rs : List Ty} (c : LrcBuildCtx) (sym : Sym) (xLvl : Nat) :
    Nat → (LrcBuildCtx → Except String (TFlat rs)) → Except String (TFlat rs)
  | 0, k => k c
  | n + 1, k => emitCall0 c sym [i64] [xLvl] (fun c' => emitRefcountN c' sym xLvl n k)

/-! ## Scalar Primitive Op Lowering -/

/-- Infer comparison operand `LrcTy` from the first variable argument (default `uint64`). -/
def inferScalarArgTy (c : LrcBuildCtx) (args : List LrcArg) : Except String LrcTy := do
  match args.find? (fun | .var _ => true | _ => false) with
  | some (.var id) => pure (← c.lookupVar id).2
  | _ => pure .uint64

/-- Emit a binary integer `OpCode` `[outTy.toTTy, outTy.toTTy] -> [outTy.toTTy]`. -/
def emitBitsBinOp {rs : List Ty} (c : LrcBuildCtx) (outTy : LrcTy)
    (code : OpCode [outTy.toTTy, outTy.toTTy] [outTy.toTTy])
    (args : List LrcArg) (k : Nat → LrcBuildCtx → Except String (TFlat rs)) :
    Except String (TFlat rs) := do
  match args with
  | [a, b] =>
    materializeArg c a outTy fun la c1 =>
      materializeArg c1 b outTy fun lb c2 =>
        let (outLvl, c3) := c2.pushVar none outTy
        k outLvl c3 >>= fun rest =>
          pure (.let_ ⟨code, (c2.varAt la, c2.varAt lb, ())⟩ rest)
  | _ => throw s!"LeanLRC ({c.fnName}): binary scalar op expected 2 args"

/-- Emit a width-indexed binary `.bits w` `OpCode` matching `outTy.toTTy` without casts. -/
def emitBitsWBinOp {rs : List Ty} (c : LrcBuildCtx) (outTy : LrcTy)
    (mk : (n : Nat) → OpCode [.bits n, .bits n] [.bits n])
    (args : List LrcArg) (k : Nat → LrcBuildCtx → Except String (TFlat rs)) :
    Except String (TFlat rs) :=
  match outTy with
  | .uint8 => emitBitsBinOp c .uint8 (mk 8) args k
  | .uint16 => emitBitsBinOp c .uint16 (mk 16) args k
  | .uint32 => emitBitsBinOp c .uint32 (mk 32) args k
  | .uint64 => emitBitsBinOp c .uint64 (mk 64) args k
  | .usize => emitBitsBinOp c .usize (mk 64) args k
  | .object => emitBitsBinOp c .object (mk 64) args k
  | .tobject => emitBitsBinOp c .tobject (mk 64) args k
  | .tagged => emitBitsBinOp c .tagged (mk 64) args k
  | .erased => emitBitsBinOp c .erased (mk 64) args k
  | .void => emitBitsBinOp c .void (mk 64) args k

/-- Emit a unary integer `OpCode` `[outTy.toTTy] -> [outTy.toTTy]`. -/
def emitBitsUnaryOp {rs : List Ty} (c : LrcBuildCtx) (outTy : LrcTy)
    (code : OpCode [outTy.toTTy] [outTy.toTTy])
    (args : List LrcArg) (k : Nat → LrcBuildCtx → Except String (TFlat rs)) :
    Except String (TFlat rs) := do
  match args with
  | [a] =>
    materializeArg c a outTy fun la c1 =>
      let (outLvl, c2) := c1.pushVar none outTy
      k outLvl c2 >>= fun rest => pure (.let_ ⟨code, (c1.varAt la, ())⟩ rest)
  | _ => throw s!"LeanLRC ({c.fnName}): unary scalar op expected 1 arg"

/-- Emit an integer comparison `LrcScalarOp`, converting `.bool` into `outTy`. -/
def emitScalarCmp {rs : List Ty} (c : LrcBuildCtx) (outTy : LrcTy)
    (cmpOp : CmpOp) (args : List LrcArg)
    (k : Nat → LrcBuildCtx → Except String (TFlat rs)) : Except String (TFlat rs) := do
  match args with
  | [a, b] =>
    let argTy ← inferScalarArgTy c args
    materializeArg c a argTy fun la c1 =>
      materializeArg c1 b argTy fun lb c2 =>
        let (bLvl, c3) := c2.pushVar none .uint8
        let (iLvl, c4) := c3.pushVar none (if outTy.isScalar then outTy else .uint64)
        let resK : Except String (TFlat rs) :=
          if outTy.isScalar then k iLvl c4
          else emitCall1 c4 "lean_box" [i64] [iLvl] outTy k
        resK >>= fun rest =>
          let w := if outTy.isScalar then outTy.bitWidth else 64
          pure (.let_ ⟨.cmp cmpOp argTy.toTTy, (c2.varAt la, c2.varAt lb, ())⟩
            (.let_ ⟨.ofBool w, (c3.varAt bLvl, ())⟩ rest))
  | _ => throw s!"LeanLRC ({c.fnName}): scalar cmp expected 2 args"

/-- Lower `LrcRhs.scalar op args` returning at `outTy`. -/
def lowerScalarOp {rs : List Ty} (c : LrcBuildCtx) (outTy : LrcTy)
    (op : LrcScalarOp) (args : List LrcArg)
    (k : Nat → LrcBuildCtx → Except String (TFlat rs)) : Except String (TFlat rs) :=
  let t := outTy.toTTy
  match op with
  | .add => emitBitsBinOp c outTy (.add t) args k
  | .sub => emitBitsBinOp c outTy (.sub t) args k
  | .mul => emitBitsBinOp c outTy (.mul t) args k
  | .udiv => emitBitsWBinOp c outTy OpCode.udiv args k
  | .urem => emitBitsWBinOp c outTy OpCode.urem args k
  | .and => emitBitsBinOp c outTy (.and t) args k
  | .or => emitBitsBinOp c outTy (.or t) args k
  | .xor => emitBitsBinOp c outTy (.xor t) args k
  | .shl => emitBitsBinOp c outTy (.shl t) args k
  | .lshr => emitBitsBinOp c outTy (.lshr t) args k
  | .ashr => emitBitsBinOp c outTy (.ashr t) args k
  | .not => emitBitsUnaryOp c outTy (.not t) args k
  | .neg => emitBitsUnaryOp c outTy (.neg t) args k
  | .eq => emitScalarCmp c outTy .eq args k
  | .ne => emitScalarCmp c outTy .ne args k
  | .ult => emitScalarCmp c outTy .ult args k
  | .ule => emitScalarCmp c outTy .ule args k
  | .slt => emitScalarCmp c outTy .slt args k
  | .sle => emitScalarCmp c outTy .sle args k

/-! ## `LrcRhs` & `LrcExpr` → `TFlat` Lowering -/

/-- Lower `ctor` / `reuse`-fallback allocation to `lean_alloc_ctor` + `lean_ctor_set`s. -/
def lowerCtorAlloc {rs : List Ty} (c : LrcBuildCtx) (info : LrcCtorInfo) (args : List LrcArg)
    (outTy : LrcTy) (k : Nat → LrcBuildCtx → Except String (TFlat rs)) :
    Except String (TFlat rs) := do
  if info.isScalar then
    let valNat := if outTy.isScalar then info.cidx else 2 * info.cidx + 1
    let (lvl, c1) := c.pushVar none outTy
    k lvl c1 >>= fun rest =>
      pure (.let_ ⟨.copy outTy.toTTy, (lrcImmArg outTy valNat, ())⟩ rest)
  else
    let scalarBytes := 8 * info.usize + info.ssize
    materializePairs c
      [ (.val (.num info.cidx), .uint64)
      , (.val (.num info.size), .uint64)
      , (.val (.num scalarBytes), .uint64) ] fun hdrLvls c1 =>
      emitCall1 c1 "lean_alloc_ctor" [i64, i64, i64, i64] (c1.rtLvl :: hdrLvls) outTy fun objL c2 =>
        materializePairs c2 (args.map (·, .tobject)) fun argLvls c3 =>
          emitFieldSets c3 "lean_ctor_set" objL 0 argLvls (fun c4 => k objL c4)

/-- Lower an `LrcRhs` binding at `outTy`, passing bound value level to `k`. -/
def lowerRhs {rs : List Ty} (fns : List LrcFn) (exts : List LrcExtern)
    (targets : List LrcClosureTarget) (c : LrcBuildCtx) (outTy : LrcTy) (rhs : LrcRhs)
    (k : Nat → LrcBuildCtx → Except String (TFlat rs)) : Except String (TFlat rs) := do
  match rhs with
  | .ctor info args => lowerCtorAlloc c info args outTy k
  | .reset _ x =>
    let (xLvl, xTy) ← c.lookupVar x
    coerceLvl c xLvl xTy .tobject fun x64 c1 =>
      emitCall0 c1 "lean_dec" [i64] [x64] fun c2 =>
        let (lvl, c3) := c2.pushVar none outTy
        let n := if outTy.isScalar then 0 else 1
        k lvl c3 >>= fun rest =>
          pure (.let_ ⟨.copy outTy.toTTy, (lrcImmArg outTy n, ())⟩ rest)
  | .reuse _ info _ args => lowerCtorAlloc c info args outTy k
  | .proj i x | .uproj i x =>
    let (xLvl, _) ← c.lookupVar x
    materializeArg c (.val (.num i)) .uint64 fun iLvl c1 =>
      emitCall1 c1 "lean_ctor_get" [i64, i64] [xLvl, iLvl] outTy k
  | .sproj n offset x =>
    let (xLvl, _) ← c.lookupVar x
    let byteOff := 8 + 8 * n + offset
    let (ptrLvl, c1) := c.pushVar none .uint64
    let (valLvl, c2) := c1.pushVar none outTy
    k valLvl c2 >>= fun rest =>
      pure (.let_ ⟨.add i64, (c.varAt xLvl, .imm (BitVec.ofNat 64 byteOff), ())⟩
        (.load outTy.toTTy (c1.varAt ptrLvl) rest))
  | .fap fnName args =>
    let sig ← resolveCallee fns exts fnName
    if args.length != sig.params.length then
      throw s!"LeanLRC ({c.fnName}): fap '{fnName}' arity mismatch"
    let argPairs := args.zip sig.params
    materializePairs c argPairs fun argLvls c1 =>
      let allLvls := if sig.takesRt then c1.rtLvl :: argLvls else argLvls
      let allTys := (if sig.takesRt then [i64] else []) ++ sig.params.map (·.toTTy)
      emitCall1 c1 sig.cName allTys allLvls sig.retTy fun resLvl c2 =>
        coerceLvl c2 resLvl sig.retTy outTy k
  | .pap fnName args =>
    let mangled := mangleSym fnName
    match targets.find? (fun t => t.fnName == mangled) with
    | none => throw s!"LeanLRC ({c.fnName}): unknown pap target '{fnName}'"
    | some tgt =>
      materializePairs c
        [ (.val (.num tgt.funId), .uint64)
        , (.val (.num tgt.arity), .uint64)
        , (.val (.num args.length), .uint64) ] fun hdrLvls c1 =>
        emitCall1 c1 "lean_alloc_closure" [i64, i64, i64, i64] (c1.rtLvl :: hdrLvls) outTy
          fun cloL c2 =>
            materializePairs c2 (args.map (·, .tobject)) fun capLvls c3 =>
              emitFieldSets c3 "lean_closure_set" cloL 0 capLvls (fun c4 => k cloL c4)
  | .ap fnVar args =>
    if args.isEmpty || args.length > 4 then
      throw s!"LeanLRC ({c.fnName}): ap arity {args.length} outside [1..4]"
    let (fnLvl, fnTy) ← c.lookupVar fnVar
    coerceLvl c fnLvl fnTy .tobject fun cloLvl c1 =>
      materializePairs c1 (args.map (·, .tobject)) fun argLvls c2 =>
        let apSym := s!"lean_apply_{args.length}"
        let apTys := i64 :: i64 :: List.replicate args.length i64
        emitCall1 c2 apSym apTys (c2.rtLvl :: cloLvl :: argLvls) outTy k
  | .box ty x =>
    let (xLvl, xTy) ← c.lookupVar x
    coerceLvl c xLvl xTy ty fun xv c1 =>
      if ty == .uint64 || ty == .usize then
        emitCall1 c1 "lean_box_u64" [i64, i64] [c1.rtLvl, xv] outTy k
      else
        coerceLvl c1 xv ty .uint64 fun x64 c2 =>
          emitCall1 c2 "lean_box" [i64] [x64] outTy k
  | .unbox x =>
    let (xLvl, _) ← c.lookupVar x
    if outTy == .uint64 || outTy == .usize then
      emitCall1 c "lean_unbox_u64" [i64] [xLvl] outTy k
    else
      emitCall1 c "lean_unbox" [i64] [xLvl] .uint64 fun u64Lvl c1 =>
        coerceLvl c1 u64Lvl .uint64 outTy k
  | .lit v => materializeArg c (.val v) outTy k
  | .isShared x =>
    let (xLvl, _) ← c.lookupVar x
    emitCall1 c "lean_is_shared" [i64] [xLvl] .uint8 fun resLvl c1 =>
      coerceLvl c1 resLvl .uint8 outTy k
  | .scalar op args => lowerScalarOp c outTy op args k
  | .copy a => materializeArg c a outTy k

mutual
/-- Check if `expr` has any tail self-call `.vdecl z _ (.fap fnName args) (.ret (.var z))`. -/
def hasTailSelfCall (fnName : String) (arity : Nat) : LrcExpr → Bool
  | .vdecl z _ (.fap f args) (.ret (.var z')) =>
    f == fnName && z == z' && args.length == arity
  | .vdecl _ _ _ rest => hasTailSelfCall fnName arity rest
  | .jdecl _ _ v rest => hasTailSelfCall fnName arity v || hasTailSelfCall fnName arity rest
  | .set _ _ _ r | .setTag _ _ r | .uset _ _ _ r | .sset _ _ _ _ _ r
  | .inc _ _ _ _ r | .dec _ _ _ _ r | .del _ r => hasTailSelfCall fnName arity r
  | .case _ _ _ alts => altsHaveTailSelfCall fnName arity alts
  | .ret _ | .jmp _ _ | .unreachable => false

def altsHaveTailSelfCall (fnName : String) (arity : Nat) : List (LrcAltPat × LrcExpr) → Bool
  | [] => false
  | (_, b) :: rest => hasTailSelfCall fnName arity b || altsHaveTailSelfCall fnName arity rest
end

mutual
/-- Count AST nodes in `LrcExpr` (providing a total structural fuel bound for lowering). -/
def exprNodeCount : LrcExpr → Nat
  | .vdecl _ _ _ rest => 1 + exprNodeCount rest
  | .jdecl _ _ v rest => 1 + exprNodeCount v + exprNodeCount rest
  | .set _ _ _ r | .setTag _ _ r | .uset _ _ _ r | .sset _ _ _ _ _ r
  | .inc _ _ _ _ r | .dec _ _ _ _ r | .del _ r => 1 + exprNodeCount r
  | .case _ _ _ alts => 1 + altsNodeCount alts
  | .ret _ | .jmp _ _ | .unreachable => 1

def altsNodeCount : List (LrcAltPat × LrcExpr) → Nat
  | [] => 1
  | (_, b) :: rest => 1 + exprNodeCount b + altsNodeCount rest
end

/-- Order `case` alternatives with `.ctor` arms first and optional `.default` arm last. -/
def sortCaseAlts (alts : List (LrcAltPat × LrcExpr)) : List (LrcAltPat × LrcExpr) :=
  let ctors := alts.filter (fun | (.ctor _, _) => true | _ => false)
  let defs := alts.filter (fun | (.default, _) => true | _ => false)
  ctors ++ defs

mutual
/-- Lower `LrcExpr` to `TFlat [rT]` with bounded total fuel. -/
def lowerExpr (fns : List LrcFn) (exts : List LrcExtern) (targets : List LrcClosureTarget)
    (fnRetTy : LrcTy) (paramTys : List LrcTy) (rT : Ty) :
    Nat → LrcBuildCtx → LrcExpr → Except String (TFlat [rT])
  | 0, c, _ => throw s!"LeanLRC ({c.fnName}): internal lowering fuel exhausted"
  | _ + 1, c, .vdecl x _ (.fap f args) (.ret (.var x')) => do
    match c.loop? with
    | some (loopLvl, loopTys) =>
      if f == c.fnName && x == x' && args.length == paramTys.length then
        materializePairs c (args.zip paramTys) fun argLvls c1 =>
          emitCall0 c1 "lean_rt_tick" [i64] [c1.rtLvl] fun c2 => do
            let tup ← buildCallTuple c2 (c2.rtLvl :: argLvls) loopTys
            pure (.jump (c2.ldepth - 1 - loopLvl) tup)
      else
        lowerRhs fns exts targets c fnRetTy (.fap f args) fun resLvl c1 =>
          emitCall0 c1 "lean_rt_leave" [i64] [c1.rtLvl] fun c2 =>
            pure (.ret (c2.varAt resLvl, ()))
    | none =>
      lowerRhs fns exts targets c fnRetTy (.fap f args) fun resLvl c1 =>
        emitCall0 c1 "lean_rt_leave" [i64] [c1.rtLvl] fun c2 =>
          pure (.ret (c2.varAt resLvl, ()))
  | fuel + 1, c, .vdecl x ty rhs rest =>
    lowerRhs fns exts targets c ty rhs fun resLvl c1 =>
      let c2 := { c1 with vars := (x, resLvl, ty) :: c1.vars }
      lowerExpr fns exts targets fnRetTy paramTys rT fuel c2 rest
  | fuel + 1, c, .jdecl jp params val rest => do
    let jpTys := params.map (·.ty)
    let jpTTys := jpTys.map (·.toTTy)
    let (_, cLbl) := c.pushJp jp jpTys
    let cVal := cLbl.pushParams params
    let valFlat ← lowerExpr fns exts targets fnRetTy paramTys rT fuel cVal val
    let restFlat ← lowerExpr fns exts targets fnRetTy paramTys rT fuel cLbl rest
    pure (.group (sig := [jpTTys]) (.cons valFlat .nil) restFlat)
  | fuel + 1, c, .set x i y rest => do
    let (xLvl, _) ← c.lookupVar x
    materializeArg c (.val (.num i)) .uint64 fun iLvl c1 =>
      materializeArg c1 y .tobject fun yLvl c2 =>
        emitCall0 c2 "lean_ctor_set" [i64, i64, i64] [xLvl, iLvl, yLvl] fun c3 =>
          lowerExpr fns exts targets fnRetTy paramTys rT fuel c3 rest
  | fuel + 1, c, .setTag x cidx rest => do
    let (xLvl, _) ← c.lookupVar x
    materializeArg c (.val (.num cidx)) .uint8 fun tLvl c1 =>
      emitCall0 c1 "lean_ctor_set_tag" [i64, i8] [xLvl, tLvl] fun c2 =>
        lowerExpr fns exts targets fnRetTy paramTys rT fuel c2 rest
  | fuel + 1, c, .uset x i y rest => do
    let (xLvl, _) ← c.lookupVar x
    let (yLvl, yTy) ← c.lookupVar y
    coerceLvl c yLvl yTy .uint64 fun y64 c1 =>
      materializeArg c1 (.val (.num i)) .uint64 fun iLvl c2 =>
        emitCall0 c2 "lean_ctor_set" [i64, i64, i64] [xLvl, iLvl, y64] fun c3 =>
          lowerExpr fns exts targets fnRetTy paramTys rT fuel c3 rest
  | fuel + 1, c, .sset x i offset y ty rest => do
    let (xLvl, _) ← c.lookupVar x
    let (yLvl, yTy) ← c.lookupVar y
    coerceLvl c yLvl yTy ty fun yCast c1 =>
      let byteOff := 8 + 8 * i + offset
      let (ptrLvl, c2) := c1.pushVar none .uint64
      lowerExpr fns exts targets fnRetTy paramTys rT fuel c2 rest >>= fun restFlat =>
        pure (.let_ ⟨.add i64, (c1.varAt xLvl, .imm (BitVec.ofNat 64 byteOff), ())⟩
          (.store (t := ty.toTTy) (c2.varAt yCast) (c2.varAt ptrLvl) restFlat))
  | fuel + 1, c, .inc x n _ persistent rest =>
    lowerRcStep fns exts targets fnRetTy paramTys rT fuel c "lean_inc" x n persistent rest
  | fuel + 1, c, .dec x n _ persistent rest =>
    lowerRcStep fns exts targets fnRetTy paramTys rT fuel c "lean_dec" x n persistent rest
  | fuel + 1, c, .del x rest =>
    lowerRcStep fns exts targets fnRetTy paramTys rT fuel c "lean_dec" x 1 false rest
  | _ + 1, c, .ret x =>
    materializeArg c x fnRetTy fun resLvl c1 =>
      emitCall0 c1 "lean_rt_leave" [i64] [c1.rtLvl] fun c2 =>
        pure (.ret (c2.varAt resLvl, ()))
  | _ + 1, c, .jmp jp args => do
    let (jpLvl, paramTysJp) ← c.lookupJp jp
    if args.length != paramTysJp.length then
      throw s!"LeanLRC ({c.fnName}): jmp jp_{jp} arity mismatch"
    materializePairs c (args.zip paramTysJp) fun argLvls c1 => do
      let tup ← buildCallTuple c1 argLvls (paramTysJp.map (·.toTTy))
      pure (.jump (c1.ldepth - 1 - jpLvl) tup)
  | _ + 1, _, .unreachable => pure .hlt
  | fuel + 1, c, .case _ x xTy alts =>
    let orderedAlts := sortCaseAlts alts
    match orderedAlts with
    | [] => pure .hlt
    | [(_, b)] => lowerExpr fns exts targets fnRetTy paramTys rT fuel c b
    | _ :: _ => do
      let (xLvl, _) ← c.lookupVar x
      let emitTag : (Nat → LrcBuildCtx → Except String (TFlat [rT])) →
          Except String (TFlat [rT]) := fun k =>
        if xTy.isScalar then coerceLvl c xLvl xTy .uint64 k
        else emitCall1 c "lean_obj_tag" [i64] [xLvl] .uint64 k
      emitTag fun tagLvl c1 =>
        lowerCaseBranch fns exts targets fnRetTy paramTys rT fuel c1 tagLvl orderedAlts

/-- Shared RC step helper for `inc` / `dec` / `del`. -/
def lowerRcStep (fns : List LrcFn) (exts : List LrcExtern) (targets : List LrcClosureTarget)
    (fnRetTy : LrcTy) (paramTys : List LrcTy) (rT : Ty) (fuel : Nat) (c : LrcBuildCtx)
    (sym : Sym) (x n : Nat) (persistent : Bool) (rest : LrcExpr) :
    Except String (TFlat [rT]) := do
  if persistent || n == 0 then lowerExpr fns exts targets fnRetTy paramTys rT fuel c rest
  else
    let (xLvl, xTy) ← c.lookupVar x
    if xTy.isScalar then lowerExpr fns exts targets fnRetTy paramTys rT fuel c rest
    else emitRefcountN c sym xLvl n fun c1 =>
      lowerExpr fns exts targets fnRetTy paramTys rT fuel c1 rest

/-- Lower a non-empty sorted `LrcExpr.case` branch list using a linear `jnz` dispatch chain. -/
def lowerCaseBranch (fns : List LrcFn) (exts : List LrcExtern) (targets : List LrcClosureTarget)
    (fnRetTy : LrcTy) (paramTys : List LrcTy) (rT : Ty) :
    Nat → LrcBuildCtx → Nat → List (LrcAltPat × LrcExpr) → Except String (TFlat [rT])
  | 0, c, _, _ => throw s!"LeanLRC ({c.fnName}): internal case fuel exhausted"
  | _, _, _, [] => pure .hlt
  | fuel + 1, c, _, [(_, b)] => lowerExpr fns exts targets fnRetTy paramTys rT fuel c b
  | fuel + 1, c, _, (.default, b) :: _ => lowerExpr fns exts targets fnRetTy paramTys rT fuel c b
  | fuel + 1, c, tagLvl, (.ctor info, b) :: rest => do
    let (cmpLvl, c1) := c.pushVar none .uint8
    let thenBody ← lowerExpr fns exts targets fnRetTy paramTys rT fuel c1 b
    let elseBody ← lowerCaseBranch fns exts targets fnRetTy paramTys rT fuel c1 tagLvl rest
    pure (.let_ ⟨OpCode.eq i64, (c.varAt tagLvl, .imm (BitVec.ofNat 64 info.cidx), ())⟩
      (.jnz (c1.varAt cmpLvl) thenBody elseBody))
end

/-- Check ABI arity and compile one `LrcFn` into a `TFlatFn` (`rt : i64` prepended). -/
def lowerLrcFn (fns : List LrcFn) (exts : List LrcExtern) (targets : List LrcClosureTarget)
    (fn : LrcFn) : Except String TFlatFn := do
  if fn.params.length > 5 then
    throw s!"LeanLRC: '{fn.name}' has {fn.params.length} params (> 5 max for x64 ABI)"
  let mangled := mangleSym fn.name
  let paramTys := fn.params.map (·.ty)
  let tParamTys := i64 :: paramTys.map (·.toTTy)
  let retTTy := fn.retTy.toTTy
  let entryCtx0 : LrcBuildCtx :=
    { fnName := fn.name, vdepth := 0, ldepth := 0, rtLvl := 0 }
  let (rt0, entryCtx1) := entryCtx0.pushVar none .uint64
  let entryCtx := entryCtx1.pushParams fn.params
  let fuel := exprNodeCount fn.body + 16
  let isTail := hasTailSelfCall fn.name fn.params.length fn.body
  let flatBody ←
    if isTail then
      let (loopLvl, loopCtx0) := entryCtx.pushJp 0 (LrcTy.uint64 :: paramTys)
      let (_, loopCtx1) := loopCtx0.pushVar none .uint64
      let loopRtLvl := loopCtx0.vdepth
      let loopCtx := { loopCtx1.pushParams fn.params with
        rtLvl := loopRtLvl
        loop? := some (loopLvl, tParamTys) }
      let loopBody ← lowerExpr fns exts targets fn.retTy paramTys retTTy fuel loopCtx fn.body
      let entryTup ← buildCallTuple loopCtx0
        (rt0 :: (List.range fn.params.length).map (· + 1)) tParamTys
      emitCall0 entryCtx "lean_rt_enter" [i64] [rt0] fun _ =>
        pure (.group (sig := [tParamTys]) (.cons loopBody .nil)
          (.jump (loopCtx0.ldepth - 1 - loopLvl) entryTup))
    else
      emitCall0 entryCtx "lean_rt_enter" [i64] [rt0] fun c1 =>
        lowerExpr fns exts targets fn.retTy paramTys retTTy fuel c1 fn.body
  if flatBody.wfCheck (pushTypes tParamTys []) [] then
    pure { name := mangled, as := tParamTys, rs := [retTTy], flat := flatBody }
  else
    throw s!"LeanLRC: TFlat.wfCheck failed on lowered function '{fn.name}'"

/-- Lower an `LrcModule` (user functions + per-arity `lean_apply_k` dispatchers). -/
def lowerLrcProgram (m : LrcModule) : Except String (List TFlatFn) := do
  let targets ← m.closureTargets
  for t in targets do
    match m.fns.find? (fun f => mangleSym f.name == t.fnName) with
    | some fn =>
      if fn.retTy.toTTy != i64 || fn.params.any (fun p => p.ty.toTTy != i64) then
        throw s!"LeanLRC: closure target '{fn.name}' must use 64-bit boxed ABI"
    | none => throw s!"LeanLRC: missing closure target '{t.fnName}'"
  let userFns ← m.fns.mapM (lowerLrcFn m.fns m.externs targets)
  let maxK := m.maxApArity
  if maxK > 4 then
    throw s!"LeanLRC: max ap arity {maxK} > 4 (exceeds x64 6-reg ABI with rt+clo)"
  let applyFns ← genLeanApplyTFlatFns targets maxK
  let allFns := userFns ++ applyFns
  let names := allFns.map (·.name)
  if !listNodup names then
    throw s!"LeanLRC: duplicate lowered symbol names in module '{m.name}'"
  pure allFns

/-- Convert a list of `TFlatFn` into reified PHOAS `Fn`s (each guaranteed `Wf`). -/
def tflatFnsToFns (tfs : List TFlatFn) : List Fn :=
  tfs.map TFlatFn.toFn

/-- Build a full `LeanQbe.T.Module` combining `rtBase_fns` and lowered program functions. -/
def toLeanModuleWithRuntime (tfs : List TFlatFn) : Module :=
  { fns := rtBase_fns ++ tflatFnsToFns tfs, externs := [], exits := rtExits }

/-- Merge multiple `LrcModule`s into one namespace-clean module (deduplicating externs). -/
def mergeLrcModules (name : String) (ms : List LrcModule) : LrcModule :=
  let allFns := ms.flatMap (·.fns)
  let allExts := ms.flatMap (·.externs)
  let dedupExts := allExts.foldl (fun acc ex =>
    if acc.any (fun e => e.name == ex.name && e.cName == ex.cName) then acc
    else acc ++ [ex]) []
  { name, fns := allFns, externs := dedupExts }

/-- Every reified `TFlatFn` satisfies `Func.Wf`. -/
theorem tflatFnsToFns_wf (tfs : List TFlatFn) : ∀ f ∈ tflatFnsToFns tfs, f.Wf := by
  intro f hf
  simp only [tflatFnsToFns, List.mem_map] at hf
  rcases hf with ⟨tf, _, rfl⟩
  exact tf.toFn_wf

/-! ## Empirical IR Metrics (`TFlat` Op / Branch / Call Counts & Module Diagnostics) -/

mutual
/-- Compute `(opCount, jnzCount, callCount)` for `TFlat rs` in a single pass. -/
def tflatCounts {rs : List Ty} : TFlat rs → Nat × Nat × Nat
  | .let_ _ k | .load _ _ k | .store _ _ k =>
    let (o, j, c) := tflatCounts k; (o + 1, j, c)
  | .call _ _ _ k =>
    let (o, j, c) := tflatCounts k; (o, j, c + 1)
  | .jnz _ t e =>
    let (o1, j1, c1) := tflatCounts t
    let (o2, j2, c2) := tflatCounts e
    (o1 + o2, 1 + j1 + j2, c1 + c2)
  | .group bs k =>
    let (o1, j1, c1) := tblocksCounts bs
    let (o2, j2, c2) := tflatCounts k
    (o1 + o2, j1 + j2, c1 + c2)
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => (0, 0, 0)

/-- Mutual block counter for `tflatCounts`. -/
def tblocksCounts {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat × Nat × Nat
  | _, .nil => (0, 0, 0)
  | _, .cons b bs =>
    let (o1, j1, c1) := tflatCounts b
    let (o2, j2, c2) := tblocksCounts bs
    (o1 + o2, j1 + j2, c1 + c2)
end

/-- Number of `.let_`/`.load`/`.store` ops in `TFlat rs`. -/
def tflatOpCount {rs : List Ty} (t : TFlat rs) : Nat := (tflatCounts t).1

/-- Number of conditional branch `.jnz` nodes in `TFlat rs`. -/
def tflatJnzCount {rs : List Ty} (t : TFlat rs) : Nat := (tflatCounts t).2.1

/-- Number of `.call` nodes in `TFlat rs`. -/
def tflatCallCount {rs : List Ty} (t : TFlat rs) : Nat := (tflatCounts t).2.2

/-- Summary IR metrics for one `TFlatFn`. -/
structure LrcFnMetrics where
  name : String
  ops : Nat
  jnzes : Nat
  calls : Nat
  deriving Repr

/-- Collect per-function IR metrics for a list of `TFlatFn`s. -/
def collectMetrics (tfs : List TFlatFn) : List LrcFnMetrics :=
  tfs.map fun tf =>
    let (ops, jnzes, calls) := tflatCounts tf.flat
    { name := tf.name, ops, jnzes, calls }

/-! ## Four Concrete `LrcModule` Benchmark & Validation Programs -/

/-- `Bool.false` / `Bool.true` / `List.nil` / `List.cons` ctor descriptors. -/
def boolFalseCtor : LrcCtorInfo :=
  { name := "Bool.false", cidx := 0, size := 0, usize := 0, ssize := 0 }
def boolTrueCtor : LrcCtorInfo :=
  { name := "Bool.true", cidx := 1, size := 0, usize := 0, ssize := 0 }
def listNilCtor : LrcCtorInfo :=
  { name := "List.nil", cidx := 0, size := 0, usize := 0, ssize := 0 }
def listConsCtor : LrcCtorInfo :=
  { name := "List.cons", cidx := 1, size := 2, usize := 0, ssize := 0 }

/-- Shared tail-recursive list builder `[1, 2, ..., n]` parameterized by function symbol name. -/
def mkListBuildFn (fnName : String) : LrcFn :=
  { name := fnName
    params := [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]
    retTy := .tobject
    body :=
      .vdecl 3 .tobject (.lit (.num 0)) <|
      .vdecl 4 .uint8 (.fap "lean_nat_dec_eq" [.var 1, .var 3]) <|
      .case "Bool" 4 .uint8
        [ (.ctor boolTrueCtor, .ret (.var 2))
        , (.ctor boolFalseCtor,
            .vdecl 5 .tobject (.lit (.num 1)) <|
            .vdecl 6 .tobject (.fap "lean_nat_sub" [.var 1, .var 5]) <|
            .vdecl 7 .tobject (.ctor listConsCtor [.var 1, .var 2]) <|
            .vdecl 8 .tobject (.fap fnName [.var 6, .var 7]) <| .ret (.var 8)) ] }

/-- Program 1: `sumToMod` — tail-recursive accumulator sum `sum_{i=1}^n i` -> `loop1`. -/
def sumToMod : LrcModule :=
  let sumToAcc : LrcFn :=
    { name := "lrc_sumToAcc"
      params := [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }]
      retTy := .tobject
      body :=
        .vdecl 3 .tobject (.lit (.num 0)) <|
        .vdecl 4 .uint8 (.fap "lean_nat_dec_eq" [.var 1, .var 3]) <|
        .case "Bool" 4 .uint8
          [ (.ctor boolTrueCtor, .ret (.var 2))
          , (.ctor boolFalseCtor,
              .vdecl 5 .tobject (.lit (.num 1)) <|
              .vdecl 6 .tobject (.fap "lean_nat_sub" [.var 1, .var 5]) <|
              .vdecl 7 .tobject (.fap "lean_nat_add" [.var 2, .var 1]) <|
              .vdecl 8 .tobject (.fap "lrc_sumToAcc" [.var 6, .var 7]) <| .ret (.var 8)) ] }
  let sumTo : LrcFn :=
    { name := "lrc_sumTo", params := [{ id := 1, ty := .tobject }], retTy := .tobject
      body := .vdecl 2 .tobject (.lit (.num 0)) <|
        .vdecl 3 .tobject (.fap "lrc_sumToAcc" [.var 1, .var 2]) <| .ret (.var 3) }
  { name := "sumTo", fns := [sumToAcc, sumTo] }

/-- Program 2: `mapAddMod` — higher-order list map (`pap`/`lean_apply_1`) + heap `ctor`/`proj`. -/
def mapAddMod : LrcModule :=
  let buildFn := mkListBuildFn "lrc_mapAdd_build"
  let addKFn : LrcFn :=
    { name := "lrc_mapAdd_addK"
      params := [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }], retTy := .tobject
      body := .vdecl 3 .tobject (.fap "lean_nat_add" [.var 2, .var 1]) <| .ret (.var 3) }
  let mapFn : LrcFn :=
    { name := "lrc_mapAdd_map"
      params := [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }], retTy := .tobject
      body :=
        .case "List" 2 .tobject
          [ (.ctor listNilCtor, .dec 1 1 false false (.ret (.var 2)))
          , (.ctor listConsCtor,
              .vdecl 3 .tobject (.proj 0 2) <| .vdecl 4 .tobject (.proj 1 2) <|
              .inc 1 1 false false <| .vdecl 5 .tobject (.ap 1 [.var 3]) <|
              .vdecl 6 .tobject (.fap "lrc_mapAdd_map" [.var 1, .var 4]) <|
              .vdecl 7 .tobject (.ctor listConsCtor [.var 5, .var 6]) <| .ret (.var 7)) ] }
  let sumFn : LrcFn :=
    { name := "lrc_mapAdd_sum", params := [{ id := 1, ty := .tobject }], retTy := .tobject
      body :=
        .case "List" 1 .tobject
          [ (.ctor listNilCtor, .vdecl 2 .tobject (.lit (.num 0)) (.ret (.var 2)))
          , (.ctor listConsCtor,
              .vdecl 2 .tobject (.proj 0 1) <| .vdecl 3 .tobject (.proj 1 1) <|
              .vdecl 4 .tobject (.fap "lrc_mapAdd_sum" [.var 3]) <|
              .vdecl 5 .tobject (.fap "lean_nat_add" [.var 2, .var 4]) <| .ret (.var 5)) ] }
  let entryFn : LrcFn :=
    { name := "lrc_mapAdd"
      params := [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }], retTy := .tobject
      body :=
        .vdecl 3 .tobject (.ctor listNilCtor []) <|
        .vdecl 4 .tobject (.fap "lrc_mapAdd_build" [.var 1, .var 3]) <|
        .vdecl 5 .tobject (.pap "lrc_mapAdd_addK" [.var 2]) <|
        .vdecl 6 .tobject (.fap "lrc_mapAdd_map" [.var 5, .var 4]) <|
        .vdecl 7 .tobject (.fap "lrc_mapAdd_sum" [.var 6]) <| .ret (.var 7) }
  { name := "mapAdd", fns := [buildFn, addKFn, mapFn, sumFn, entryFn] }

/-- Program 3: `tree2Mod` — binary tree construction & non-tail recursive sum. -/
def tree2Mod : LrcModule :=
  let cLeaf : LrcCtorInfo := { name := "Tree.leaf", cidx := 0, size := 1, usize := 0, ssize := 0 }
  let cNode : LrcCtorInfo := { name := "Tree.node", cidx := 1, size := 2, usize := 0, ssize := 0 }
  let mkTreeFn : LrcFn :=
    { name := "lrc_mkTree"
      params := [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }], retTy := .object
      body :=
        .vdecl 3 .tobject (.lit (.num 0)) <|
        .vdecl 4 .uint8 (.fap "lean_nat_dec_eq" [.var 1, .var 3]) <|
        .case "Bool" 4 .uint8
          [ (.ctor boolTrueCtor, .vdecl 5 .object (.ctor cLeaf [.var 2]) (.ret (.var 5)))
          , (.ctor boolFalseCtor,
              .vdecl 5 .tobject (.lit (.num 1)) <|
              .vdecl 6 .tobject (.fap "lean_nat_sub" [.var 1, .var 5]) <|
              .vdecl 7 .object (.fap "lrc_mkTree" [.var 6, .var 2]) <|
              .vdecl 8 .tobject (.fap "lean_nat_add" [.var 2, .var 5]) <|
              .vdecl 9 .object (.fap "lrc_mkTree" [.var 6, .var 8]) <|
              .vdecl 10 .object (.ctor cNode [.var 7, .var 9]) <| .ret (.var 10)) ] }
  let treeSumFn : LrcFn :=
    { name := "lrc_treeSum", params := [{ id := 1, ty := .object }], retTy := .tobject
      body :=
        .case "Tree" 1 .object
          [ (.ctor cLeaf, .vdecl 2 .tobject (.proj 0 1) (.ret (.var 2)))
          , (.ctor cNode,
              .vdecl 2 .object (.proj 0 1) <| .vdecl 3 .object (.proj 1 1) <|
              .vdecl 4 .tobject (.fap "lrc_treeSum" [.var 2]) <|
              .vdecl 5 .tobject (.fap "lrc_treeSum" [.var 3]) <|
              .vdecl 6 .tobject (.fap "lean_nat_add" [.var 4, .var 5]) <| .ret (.var 6)) ] }
  let tree2Fn : LrcFn :=
    { name := "lrc_tree2", params := [{ id := 1, ty := .tobject }], retTy := .tobject
      body :=
        .vdecl 2 .tobject (.lit (.num 1)) <|
        .vdecl 3 .object (.fap "lrc_mkTree" [.var 1, .var 2]) <|
        .vdecl 4 .tobject (.fap "lrc_treeSum" [.var 3]) <| .ret (.var 4) }
  { name := "tree2", fns := [mkTreeFn, treeSumFn, tree2Fn] }

/-- Program 4: `foldMapMod` — exercises `lean_apply_1` under-application, `lean_apply_2` exact
saturation & over-application, `jdecl`/`jmp`, and `reset`/`reuse` ctor fallback. -/
def foldMapMod : LrcModule :=
  let pairCtor : LrcCtorInfo := { name := "Pair.mk", cidx := 0, size := 2, usize := 0, ssize := 0 }
  let buildFn := mkListBuildFn "lrc_foldMap_build"
  let add2Fn : LrcFn :=
    { name := "lrc_foldMap_add2"
      params := [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }], retTy := .tobject
      body := .vdecl 3 .tobject (.fap "lean_nat_add" [.var 1, .var 2]) <| .ret (.var 3) }
  let mkAdderFn : LrcFn :=
    { name := "lrc_foldMap_mkAdder", params := [{ id := 1, ty := .tobject }], retTy := .tobject
      body := .vdecl 2 .tobject (.pap "lrc_foldMap_add2" [.var 1]) <| .ret (.var 2) }
  let addMul3Fn : LrcFn :=
    { name := "lrc_foldMap_addMul3"
      params :=
        [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }, { id := 3, ty := .tobject }]
      retTy := .tobject
      body :=
        .vdecl 4 .tobject (.fap "lean_nat_add" [.var 2, .var 3]) <|
        .vdecl 5 .tobject (.fap "lean_nat_add" [.var 4, .var 1]) <| .ret (.var 5) }
  let foldlFn : LrcFn :=
    { name := "lrc_foldMap_foldl"
      params :=
        [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }, { id := 3, ty := .tobject }]
      retTy := .tobject
      body :=
        .case "List" 3 .tobject
          [ (.ctor listNilCtor, .dec 1 1 false false (.ret (.var 2)))
          , (.ctor listConsCtor,
              .vdecl 4 .tobject (.proj 0 3) <| .vdecl 5 .tobject (.proj 1 3) <|
              .vdecl 6 .tobject (.ctor pairCtor [.var 2, .var 4]) <|
              .vdecl 7 .tobject (.reset 2 6) <|
              .vdecl 8 .tobject (.reuse 7 pairCtor true [.var 2, .var 4]) <|
              .vdecl 9 .tobject (.proj 0 8) <| .vdecl 10 .tobject (.proj 1 8) <|
              .jdecl 1 [{ id := 11, ty := .tobject }, { id := 12, ty := .tobject }]
                (.inc 1 1 false false <|
                 .vdecl 13 .tobject (.ap 1 [.var 11, .var 12]) <|
                 .vdecl 14 .tobject (.fap "lrc_foldMap_foldl" [.var 1, .var 13, .var 5]) <|
                 .ret (.var 14))
                (.jmp 1 [.var 9, .var 10])) ] }
  let entryFn : LrcFn :=
    { name := "lrc_foldMap"
      params := [{ id := 1, ty := .tobject }, { id := 2, ty := .tobject }], retTy := .tobject
      body :=
        .vdecl 3 .tobject (.ctor listNilCtor []) <|
        .vdecl 4 .tobject (.fap "lrc_foldMap_build" [.var 1, .var 3]) <|
        .vdecl 5 .tobject (.pap "lrc_foldMap_mkAdder" []) <|
        .vdecl 6 .tobject (.lit (.num 1)) <|
        .vdecl 7 .tobject (.ap 5 [.var 2, .var 6]) <|
        .vdecl 8 .tobject (.pap "lrc_foldMap_addMul3" []) <|
        .vdecl 9 .tobject (.ap 8 [.var 7]) <|
        .vdecl 10 .tobject (.lit (.num 0)) <|
        .vdecl 11 .tobject (.fap "lrc_foldMap_foldl" [.var 9, .var 10, .var 4]) <|
        .ret (.var 11) }
  { name := "foldMap", fns := [buildFn, add2Fn, mkAdderFn, addMul3Fn, foldlFn, entryFn] }

/-! ## Real Lean 4 Functions & `lrc_of_lean!` IR Extraction -/

/-- Binary tree inductive compiled by real Lean 4 compiler (`realLeanIrMod`). -/
inductive LrcTree where
  | leaf (v : Nat)
  | node (l r : LrcTree)

/-- Tail-recursive sum `leanSumToAcc n acc = acc + sum_{i=1}^n i`. -/
def leanSumToAcc (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => leanSumToAcc k (acc + k + 1)

/-- Entry point for Lean-IR `sumTo`. -/
def leanSumTo (n : Nat) : Nat := leanSumToAcc n 0

/-- Build `[1, 2, ..., n]`. -/
def leanListBuild (n : Nat) (acc : List Nat) : List Nat :=
  match n with
  | 0 => acc
  | k + 1 => leanListBuild k ((k + 1) :: acc)

/-- Higher-order list map. -/
def leanListMap (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => f x :: leanListMap f xs

/-- Recursive list sum. -/
def leanListSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + leanListSum xs

/-- Build `[1..n]`, map `(+ k)`, and sum (`realLeanIrMod`). -/
def leanMapAddSum (n k : Nat) : Nat :=
  leanListSum (leanListMap (fun x => x + k) (leanListBuild n []))

/-- Construct complete binary tree of height `depth`. -/
def leanMkTree (depth base : Nat) : LrcTree :=
  match depth with
  | 0 => .leaf base
  | d + 1 => .node (leanMkTree d base) (leanMkTree d (base + 1))

/-- Recursive sum of leaves in `LrcTree`. -/
def leanTreeSum : LrcTree → Nat
  | .leaf v => v
  | .node l r => leanTreeSum l + leanTreeSum r

/-- Construct & sum binary tree (`realLeanIrMod`). -/
def leanTree2 (depth : Nat) : Nat :=
  leanTreeSum (leanMkTree depth 1)

/-- Left fold over `List Nat`. -/
def leanListFoldl (f : Nat → Nat → Nat) (acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: xs => leanListFoldl f (f acc x) xs

/-- Higher-order `foldl` over `[1..n]` capturing `k` (`ap` arity 2 via `lean_apply_2`). -/
def leanFoldMap (n k : Nat) : Nat :=
  leanListFoldl (fun a b => a + b + (k + 1)) 0 (leanListBuild n [])

/- Real `Lean.IR.Decl` module spliced from compiler environment! -/
lrc_of_lean! realLeanIrMod [leanSumTo, leanMapAddSum, leanTree2, leanFoldMap]

/-- Combined module merging all 4 hand-written `LrcModule`s + `realLeanIrMod`. -/
def allBenchLrcMod : LrcModule :=
  mergeLrcModules "all_lrc_bench"
    [sumToMod, mapAddMod, tree2Mod, foldMapMod, realLeanIrMod]

end LeanQbe.T.LeanLRC
