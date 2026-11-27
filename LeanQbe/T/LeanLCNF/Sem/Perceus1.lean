module

public import LeanQbe.T.LeanLCNF.Sem.ValRep
public import LeanQbe.T.Logic.ProofKit

/-!
# Perceus Tier-P → Tier-H Soundness, Part 1: Fragment, Resource WP, and Value/Prim Simulation

Defines:
- `PerceusModWf` / `PerceusCodeWf` / `PerceusValWf`: decidable Tier-H compliance companion
  to `RcCheck` covering the verified first-order + RC + FBIP + fast-path `Nat`/`UInt`/read-only
  fragment.
- `PRWp`, `PResOk`, `PResOkIdx`, and the Tier-P → Tier-H specification lifters `hOfP` / `hOfPIdx`.
- Heap preservation lemmas for allocation (`ctor`, 64-bit `box`), `bindOwned`/`bindBorrowed`,
  and `applyArgs` / `consumeVar`.
- `PVal.wp → HVal.wp` and `primP → HPrim.wp` simulation lemmas (`pVal_wp_sim_hVal_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

/-! ## 1. Decidable Tier-H Syntactic Fragment Check (`PerceusModWf`) -/

/-- Supported Tier-H primitives whose `HPrim.wp` semantics is exact and `Nodup`-preserving. -/
@[expose] def perceusPrimWf (name : String) (arity : Nat) : Bool :=
  match splitDot name with
  | ["Nat", op] =>
    match natBinSlowInfo? op, arity with
    | some _, 2 => true
    | none, _ => op == "pred" && arity == 1
    | _, _ => false
  | ["Array", op] =>
    match op, arity with
    | "size", 2 => true
    | "usize", 2 => true
    | "get!InternalBorrowed", 4 => true
    | "propagateMark", 4 => true
    | _, _ => false
  | ["ByteArray", op] =>
    match op, arity with
    | "size", 1 | "usize", 1 | "get!", 2 | "get", 3 | "propagateMark", 2 => true
    | _, _ => false
  | "String" :: rest =>
    match rest, arity with
    | ["length"], 1 | ["Internal", "length"], 1
    | ["utf8ByteSize"], 1 | ["propagateMark"], 2 => true
    | _, _ => false
  | ["System", "Platform", "getNumBits"] => arity == 0
  | ["getObjTagNat"] => arity == 1 || arity == 2
  | ["outOfBounds", "_redArg"] => arity == 1
  | [ty, op] =>
    match uintWidth? ty with
    | some _ =>
      match op, arity with
      | "add", 2 => true | "sub", 2 => true | "mul", 2 => true | "land", 2 => true
      | "lor", 2 => true | "xor", 2 => true | "shiftLeft", 2 => true | "shiftRight", 2 => true
      | "div", 2 => true | "mod", 2 => true | "complement", 1 => true | "neg", 1 => true
      | "decEq", 2 => true | "beq", 2 => true | "decLt", 2 => true | "blt", 2 => true
      | "decLe", 2 => true | "ble", 2 => true | "toUInt8", 1 => true | "toUInt16", 1 => true
      | "toUInt32", 1 => true | "toUInt64", 1 => true | "toUSize", 1 => true
      | "ofNat", 1 => true | "ofNatLT", 1 => true | "ofNatLT", 2 => true
      | "ofBitVec", 1 => true | "toNat", 1 => true | "toBitVec", 1 => true
      | _, _ => false
    | none => false
  | _ => false

/-- Return type compatibility for supported primitives. -/
@[expose] def perceusPrimRetWf (name : String) (ty : LcTy) : Bool :=
  match splitDot name with
  | ["Nat", op] =>
    if op == "decEq" || op == "beq" || op == "decLt" || op == "blt" ||
       op == "decLe" || op == "ble" then ty == .uint8
    else ty == .tobject || ty == .tagged
  | ["Array", "size"] => ty == .tobject || ty == .tagged
  | ["Array", "usize"] => ty == .usize || ty == .uint64
  | ["Array", "get!InternalBorrowed"] => ty == .tobject
  | ["Array", "propagateMark"] => ty.needsRc
  | ["ByteArray", "size"] => ty == .tobject || ty == .tagged
  | ["ByteArray", "usize"] => ty == .usize || ty == .uint64
  | ["ByteArray", "get!"] => ty == .uint8
  | ["ByteArray", "get"] => ty == .uint8
  | ["ByteArray", "propagateMark"] => ty.needsRc
  | "String" :: ["length"] => ty == .tobject || ty == .tagged
  | "String" :: ["Internal", "length"] => ty == .tobject || ty == .tagged
  | "String" :: ["utf8ByteSize"] => ty == .tobject || ty == .tagged
  | "String" :: ["propagateMark"] => ty.needsRc
  | ["System", "Platform", "getNumBits"] => ty == .tobject || ty == .tagged
  | ["getObjTagNat"] => ty == .tobject || ty == .tagged
  | ["outOfBounds", "_redArg"] => true
  | [u, op] =>
    match uintWidth? u with
    | some w =>
      if op == "decEq" || op == "beq" || op == "decLt" || op == "blt" ||
         op == "decLe" || op == "ble" then ty == .uint8
      else if op == "toNat" || op == "toBitVec" then ty == .tobject || ty == .tagged
      else if op == "toUInt8" then ty == .uint8
      else if op == "toUInt16" then ty == .uint16
      else if op == "toUInt32" then ty == .uint32
      else if op == "toUInt64" then ty == .uint64
      else if op == "toUSize" then ty == .usize
      else ty.isScalar && ty.width == w
    | none => false
  | _ => false

/-- Check `LcArg` list contains only non-scalar variables (or `.erased`). -/
@[expose] def argsNonScalar (ctx : RcCtx) (as : List LcArg) : Bool :=
  as.all fun a => match a with
    | .erased => true
    | .var x => match ctx.get? x with
      | some v => !v.ty.isScalar
      | none => false

/-- Check `LcArg` list contains no variable currently tracked as an active `sharedPreds` target. -/
@[expose] def argsNoSharedTarget (ctx : RcCtx) (as : List LcArg) (bs : List Bool) : Bool :=
  (as.zip bs).all fun (a, br) =>
    if br then true
    else match a with
      | .erased => true
      | .var x => ctx.sharedPreds.all fun (_, tgt) => tgt != x

/-- Check binding `x` does not clobber any live variable, parent backing, or `sharedPreds` entry. -/
@[expose] def binderFreshOwned (ctx : RcCtx) (x : Nat) : Bool :=
  (ctx.vars.all fun u => u.parent? != some x) &&
  (ctx.sharedPreds.all fun p => p.1 != x && p.2 != x) &&
  match ctx.get? x with
  | none => true
  | some v => !v.isLive

/-- Argument-type check for supported primitives matching `HPrim.wp`
scalar/non-scalar representations. -/
@[expose] def perceusPrimArgsWf (ctx : RcCtx) (name : String) (as : List LcArg) : Bool :=
  let argScalarW (a : LcArg) (w : Nat) : Bool := match a with
    | .erased => false
    | .var x => match ctx.get? x with
      | some v => v.ty.isScalar && v.ty.width == w
      | none => false
  let argNonSc (a : LcArg) : Bool := match a with
    | .erased => true
    | .var x => match ctx.get? x with
      | some v => !v.ty.isScalar
      | none => false
  match splitDot name, as with
  | [ty, op], [a] =>
    match uintWidth? ty with
    | some w =>
      if op == "ofNat" || op == "ofNatLT" || op == "ofBitVec" then argNonSc a
      else argScalarW a w
    | none => as.all argNonSc
  | [ty, op], [a, b] =>
    match uintWidth? ty with
    | some w =>
      if op == "ofNatLT" then argNonSc a
      else argScalarW a w && argScalarW b w
    | none => as.all argNonSc
  | _, _ => as.all argNonSc

/-- Check that no exclusive (`excl = true`) variable is passed in a borrowed position to a call. -/
@[expose] def argsNoExclBorrow (ctx : RcCtx) (as : List LcArg) (borrows : List Bool) : Bool :=
  (as.zip borrows).all fun (a, br) =>
    if !br then true
    else match a with
      | .erased => true
      | .var x => match ctx.get? x with
        | some v => !v.excl
        | none => true

/-- Check all borrowed args remain live after `applyArgs` consumes owned positions. -/
@[expose] def argsBorrowSurvive (ctxAfter : RcCtx) (as : List LcArg) (bs : List Bool) : Bool :=
  (as.zip bs).all fun (a, br) =>
    if !br then true
    else match a with
      | .erased => true
      | .var x => match ctxAfter.get? x with
        | some v => v.isLive
        | none => false

/-- Check all borrowed args at a `.jmp` come from caller-backed
(`noRc`/`persistent`/`parent?=none`). -/
@[expose] def argsBorrowFromExt (ctxAfter : RcCtx) (as : List LcArg) (bs : List Bool) : Bool :=
  (as.zip bs).all fun (a, br) =>
    if !br then true
    else match a with
      | .erased => true
      | .var x => match ctxAfter.get? x with
        | some v =>
          v.isLive && (v.noRc || v.persistent || (v.borrowed && v.parent?.isNone))
        | none => false

/-- Check argument variable types match callee parameter types at call/jump sites. -/
@[expose] def argsMatchTys (ctx : RcCtx) (as : List LcArg) (pts : List LcTy) : Bool :=
  as.length == pts.length &&
  (as.zip pts).all fun (a, pt) => match a with
    | .erased => !pt.isScalar && pt != .object && pt != .tagged
    | .var x => match ctx.get? x with
      | some v =>
        v.ty.isScalar == pt.isScalar && v.ty.width == pt.width &&
        (pt == .object → v.ty == .object) && (pt == .tagged → v.ty == .tagged) &&
        (pt.isScalar ||
          (if pt.needsRc then (v.ty.needsRc || (pt == .tobject && v.ty == .tagged))
           else (v.ty == .tagged || v.noRc)))
      | none => false

/-- Check `LcVal` compliance with Tier-H `HVal.wp` preconditions. -/
@[expose] def perceusValWf (env : RcModEnv) (ctx : RcCtx) (x : Nat) (ty : LcTy)
    (v : LcVal) : Bool :=
  binderFreshOwned ctx x &&
  match v with
  | .lit (.nat n) => decide (n < 2 ^ 63) && !ty.isScalar && ty != .object
  | .lit (.scalar _) => ty.isScalar
  | .lit (.str _) => false
  | .erased => !ty.isScalar && ty != .object
  | .ctor ci as =>
    if ci.isScalar then
      if ty.isScalar then decide (ci.cidx < 2 ^ ty.width)
      else decide (ci.cidx < 2 ^ 63) && ty != .object
    else
      ty.needsRc && decide (ci.cidx ≤ 244) && decide (ci.size < 256) &&
      decide (rtMinObjBytes ≤ ci.byteSize) && decide (ci.byteSize < 65536) &&
      argsNonScalar ctx as && argsNoSharedTarget ctx as (List.replicate as.length false)
  | .oproj _ y =>
    ty == .tobject &&
    (match ctx.get? y with | some vy => !vy.ty.isScalar && vy.ty != .tagged | none => false)
  | .uproj _ y =>
    ty.isScalar && ty.width == 64 &&
    (match ctx.get? y with | some vy => !vy.ty.isScalar && vy.ty != .tagged | none => false)
  | .sproj _ _ y =>
    ty.isScalar &&
    (match ctx.get? y with | some vy => !vy.ty.isScalar && vy.ty != .tagged | none => false)
  | .box t y =>
    t.isScalar &&
    (match ctx.get? y with
    | some vy => vy.ty.isScalar && vy.ty.width == t.width && !ty.isScalar &&
      if t == .uint64 || t == .usize || t == .float then ty.needsRc
      else ty != .object
    | none => false)
  | .unbox y =>
    ty.isScalar &&
    (match ctx.get? y with
    | some vy => !vy.ty.isScalar
    | none => false)
  | .isShared y =>
    ty == .uint8 &&
    (match ctx.get? y with
    | some vy => !vy.ty.isScalar && vy.ty != .tagged && decide (vy.owned ≤ 1)
    | none => false)
  | .fap f as =>
    match env.decls.find? (·.1 == f) with
    | some (_, borrows, pts, rty, isConst) =>
      !(isConst && as.isEmpty) &&
      argsMatchTys ctx as pts && argsNoSharedTarget ctx as borrows &&
      argsNoExclBorrow ctx as borrows &&
      (match ctx.applyArgs as borrows with
      | .ok ctx1 =>
        argsBorrowSurvive ctx1 as borrows &&
        (ctx1.vars.all fun u => !u.excl || as.all fun a => match a with
          | .erased => true
          | .var z => match ctx.get? z with
            | some vz =>
              vz.parent? != some u.id && !(vz.ty.isScalar && vz.ty.width == 64)
            | none => true)
      | .error _ => false) &&
      (ctx.sharedPreds.all fun (b, tgt) =>
        match ctx.get? b, ctx.get? tgt with
        | some vb, some vt =>
          if !vb.isLive || vt.noRc || vt.persistent || vt.owned == 0 then true
          else vt.excl && as.all (· != .var tgt)
        | _, _ => true) &&
      ty.isScalar == rty.isScalar && ty.width == rty.width &&
      (ty.needsRc == rty.needsRc || (ty == .tobject && rty == .tagged)) &&
      (ty == .object → rty == .object) && (ty == .tagged → rty == .tagged)
    | none =>
      perceusPrimWf f as.length && perceusPrimRetWf f ty && perceusPrimArgsWf ctx f as &&
      (if f == "Array.propagateMark" || f == "ByteArray.propagateMark" ||
          f == "String.propagateMark" then
        ty == .tobject || match as.getLast? with
          | some (.var y) => match ctx.get? y with | some vy => vy.ty == .object | none => false
          | _ => false
      else true) &&
      (match primRcSig f as.length with
      | some (borrows, _) => argsNoSharedTarget ctx as borrows
      | none => false)
  | .pap _ _ => false
  | .ap _ _ => false
  | .reset _ _ => false
  | .reuse _ _ _ _ => false

/-- Check `checkCode` helper returning the `baseCtx` computed for a `.jp` body. -/
@[expose] def jpBaseCtx (env : RcModEnv) (retTy : LcTy) (jps : List RcJpInfo) (ctx : RcCtx)
    (j : Nat) (ps : List LcParam) (k : LcCode) : RcCtx :=
  let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := ctx.vars.map (·.id) }
  match checkCode env retTy (jInfo :: jps) ctx k with
  | .ok jumpsK =>
    let myJumps := (jumpsK.filter (·.1 == j)).map Prod.snd
    match mergeJpList myJumps with
    | .ok (some c) => c
    | _ => ctx
  | .error _ => ctx

mutual
/-- True iff no path reaching `.jmp j _` mutates a variable in `liveIds`. -/
@[expose] def jpLiveNoMut (j : Nat) (liveIds mutated : List Nat) : LcCode → Bool
  | .let_ x _ _ k => jpLiveNoMut j liveIds (x :: mutated) k
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => jpLiveNoMut j liveIds mutated k
  | .jp _ ps body k =>
    jpLiveNoMut j liveIds (ps.map (·.id) ++ mutated) body && jpLiveNoMut j liveIds mutated k
  | .jmp j' _ => if j' == j then !mutated.any liveIds.contains else true
  | .cases _ alts => jpAltsLiveNoMut j liveIds mutated alts
  | .ret _ | .unreach => true
  | .oset x _ _ k | .uset x _ _ k | .sset x _ _ _ _ k | .setTag x _ k =>
    jpLiveNoMut j liveIds (x :: mutated) k
@[expose] def jpAltsLiveNoMut (j : Nat) (liveIds mutated : List Nat) :
    List (LcPat × LcCode) → Bool
  | [] => true
  | (_, b) :: rest => jpLiveNoMut j liveIds mutated b && jpAltsLiveNoMut j liveIds mutated rest
end

mutual
/-- Decidable Tier-H syntactic compliance check on `LcCode`, mirroring `checkCode`. -/
@[expose] def perceusCodeWf (env : RcModEnv) (retTy : LcTy) (jps : List RcJpInfo)
    (ctx : RcCtx) (sm : List (Nat × Nat × List Bool)) : LcCode → Bool
  | .let_ x ty v k =>
    perceusValWf env ctx x ty v && valScalarWf sm ty v &&
    match checkVal env ctx x ty v with
    | .ok ctx' =>
      let sm' := match v with
        | .ctor ci _ => ctorBindMask x ci sm
        | _ => sm.filter (·.1 != x)
      perceusCodeWf env retTy jps ctx' sm' k
    | .error _ => false
  | .jp j ps body k =>
    let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := ctx.vars.map (·.id) }
    let baseCtx := jpBaseCtx env retTy jps ctx j ps k
    jps.all (·.id != j) && (ps.map (·.id)).Nodup &&
    ps.all (fun p => binderFreshOwned baseCtx p.id) &&
    baseCtx.vars.all (fun v => !v.isLive || isVarScalarInit sm v.id) &&
    jpLiveNoMut j ((baseCtx.vars.filter (·.isLive)).map (·.id)) [] k &&
    perceusCodeWf env retTy (jInfo :: jps) ctx sm k &&
    perceusCodeWf env retTy jps (baseCtx.bindParams ps) [] body
  | .jmp j as =>
    as.all (argScalarInit sm) &&
    match jps.find? (·.id == j) with
    | none => false
    | some info =>
      let borrows := info.params.map (·.borrow)
      argsMatchTys ctx as (info.params.map (·.ty)) &&
      argsNoSharedTarget ctx as borrows &&
      match ctx.applyArgs as borrows with
      | .ok ctx1 => argsBorrowFromExt ctx1 as borrows | .error _ => false
  | .cases x alts =>
    match ctx.get? x with
    | none => false
    | some vx =>
      perceusAltsWf env retTy jps ctx sm x vx.ty
        ((ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) alts
  | .ret a =>
    argScalarInit sm a &&
    match a with
    | .erased => !retTy.isScalar && retTy != .object && retTy != .tagged
    | .var x => match ctx.get? x with
      | some vx =>
        vx.ty.isScalar == retTy.isScalar && vx.ty.width == retTy.width &&
        (retTy.needsRc == vx.ty.needsRc || (retTy == .tagged && vx.ty == .tobject) ||
          (retTy == .tobject && vx.ty == .tagged) ||
          (!retTy.isScalar && !retTy.needsRc && vx.noRc)) &&
        (retTy == .object → vx.ty == .object) && (retTy == .tagged → vx.ty == .tagged)
      | none => false
  | .unreach => true
  | .oset x _ y k =>
    argScalarInit sm y &&
    (match ctx.get? x, y with
    | some vx, .var yid =>
      !vx.ty.isScalar && vx.ty != .tagged &&
      match ctx.get? yid with
      | some vy => !vy.ty.isScalar && (ctx.sharedPreds.all fun (_, tgt) => tgt != yid)
      | none => false
    | some vx, .erased => !vx.ty.isScalar && vx.ty != .tagged
    | _, _ => false) &&
    match ctx.consumeArg y with
    | .ok ctx1 => perceusCodeWf env retTy jps ctx1 sm k | .error _ => false
  | .uset x i y k =>
    scalarSlotInBounds sm x i 0 8 && isVarScalarInit sm y &&
    (match ctx.get? x, ctx.get? y with
    | some vx, some vy =>
      !vx.ty.isScalar && vx.ty != .tagged && vy.ty.isScalar && vy.ty.width == 64
    | _, _ => false) && perceusCodeWf env retTy jps ctx (initScalarBytes sm x i 0 8) k
  | .sset x n off y ty k =>
    ty.isScalar && scalarSlotInBounds sm x n off ty.toTTy.bytes && isVarScalarInit sm y &&
    (match ctx.get? x, ctx.get? y with
    | some vx, some vy =>
      !vx.ty.isScalar && vx.ty != .tagged && vy.ty.isScalar && vy.ty.width == ty.width
    | _, _ => false) &&
    perceusCodeWf env retTy jps ctx (initScalarBytes sm x n off ty.toTTy.bytes) k
  | .setTag x cidx k =>
    decide (cidx ≤ 244) &&
    (match ctx.get? x with | some vx => !vx.ty.isScalar && vx.ty != .tagged | none => false) &&
    perceusCodeWf env retTy jps ctx sm k
  | .inc x n chk k =>
    isVarScalarInit sm x &&
    match ctx.get? x with
    | none => false
    | some v =>
      v.isLive && (v.ty.width == 64) && (v.ty == .tobject → chk) &&
      if v.noRc || v.persistent || n == 0 then perceusCodeWf env retTy jps ctx sm k
      else (0 < v.owned || ctx.sharedPreds.all (·.2 != x)) &&
        perceusCodeWf env retTy jps (ctx.put { v with owned := v.owned + n, excl := false }) sm k
  | .dec x n chk k =>
    match ctx.get? x with
    | none => false
    | some v =>
      v.isLive && (v.ty.width == 64) && (v.ty == .tobject → chk) &&
      (v.noRc || v.persistent || n == 0 || decide (n < v.owned) ||
        ctx.sharedPreds.all fun (b, tgt) => match ctx.get? b, ctx.get? tgt with
          | some vb, some vt =>
            !vb.isLive || vt.noRc || vt.persistent || vt.owned == 0 || tgt == x || vt.excl
          | _, _ => true) &&
      match ctx.consumeVar x n with
      | .ok ctx1 => perceusCodeWf env retTy jps ctx1 sm k | .error _ => false
  | .del x k =>
    match ctx.consumeVar x with
    | .ok ctx1 => perceusCodeWf env retTy jps ctx1 (sm.filter (·.1 != x)) k | .error _ => false

/-- Branch-wise Tier-H syntactic compliance check mirroring `checkAlts`. -/
@[expose] def perceusAltsWf (env : RcModEnv) (retTy : LcTy) (jps : List RcJpInfo)
    (ctx : RcCtx) (sm : List (Nat × Nat × List Bool)) (scru : Nat) (scruTy : LcTy)
    (target? : Option Nat) : List (LcPat × LcCode) → Bool
  | [] => true
  | (pat, body) :: rest =>
    let patOk := match pat with
      | .ctor _ cname => scruTy == .object → !env.scalarCtors.contains cname | .dflt => true
    let ctx1 := match pat with
      | .ctor _ cname =>
        if env.scalarCtors.contains cname then ctx.markScalarBranch scru else ctx
      | .dflt => ctx
    let ctxBranch := match target?, pat with
      | some tgt, .ctor 0 _ => ctx1.markExcl tgt | _, _ => ctx1
    patOk && perceusCodeWf env retTy jps ctxBranch sm body &&
      perceusAltsWf env retTy jps ctx sm scru scruTy target? rest
end

/-- Module-level Tier-H syntactic compliance check. -/
@[expose] def perceusModWf (m : LcModule) : Bool :=
  let env := mkRcModEnv m
  (m.decls.map (·.name)).Nodup &&
  m.decls.all fun d =>
    !isPrimName d.name &&
    (d.params.map (·.id)).Nodup &&
    perceusCodeWf env d.retTy [] ((RcCtx.mk [] []).bindParams d.params) [] d.body

/-! ## 2. Pure Tier-P Resource WP (`PRWp`, `PResOk`, `PResOkIdx`) and `hOfP` -/

/-- Check whether `pv : PVal` is represented as an odd tagged word (`bv &&& 1 ≠ 0`) in Tier H. -/
@[expose] def isTaggedPVal : PVal → Bool
  | .erased => true
  | .bits w _ => decide (w < 64)
  | .nat n => decide (n < 2 ^ 63)
  | .ctor cidx [] [] => decide (cidx < 2 ^ 63)
  | _ => false

/-- Check `primP` arguments & results stay inside the small-`Nat` / in-bounds Tier-H envelope. -/
@[expose] def primResSafe (name : String) (as : List PVal) : Prop :=
  match splitDot name, as with
  | ["Nat", "add"], [.nat a, .nat b] => a + b < 2 ^ 63
  | ["Nat", "mul"], [.nat a, .nat b] => a < 2 ^ 63 ∧ b < 2 ^ 63 ∧ a * b < 2 ^ 63
  | ["Nat", "shiftLeft"], [.nat a, .nat b] =>
    a < 2 ^ 63 ∧ b < 63 ∧ a <<< b < 2 ^ 63
  | ["Nat", "pred"], [.nat a] => a < 2 ^ 63
  | ["Nat", _], [.nat a, .nat b] => a < 2 ^ 63 ∧ b < 2 ^ 63
  | ["String", "length"], [.str s] => s.length < 2 ^ 63
  | ["String", "Internal", "length"], [.str s] => s.length < 2 ^ 63
  | ["String", "utf8ByteSize"], [.str s] => s.utf8ByteSize < 2 ^ 63
  | ["Array", "get!InternalBorrowed"], [_, _, .arr xs, .nat i] =>
    i < 2 ^ 63 ∧ i < xs.length
  | ["ByteArray", "get!"], [.barr _, .nat i] => i < 2 ^ 63
  | ["ByteArray", "get"], [.barr _, .nat i, _] => i < 2 ^ 63
  | ["getObjTagNat"], [_, v] =>
    match v with
    | .nat n => n < 2 ^ 63 | .bits w _ => w < 64
    | .ctor c _ _ => c < 2 ^ 63 | .erased => True | _ => False
  | ["getObjTagNat"], [v] =>
    match v with
    | .nat n => n < 2 ^ 63 | .bits w _ => w < 64
    | .ctor c _ _ => c < 2 ^ 63 | .erased => True | _ => False
  | [ty, op], [.nat n] =>
    match uintWidth? ty with
    | some _ => (op == "ofNat" ∨ op == "ofNatLT" ∨ op == "ofBitVec") ∧ n < 2 ^ 63
    | none => False
  | [ty, "ofNatLT"], [.nat n, _] => (uintWidth? ty).isSome ∧ n < 2 ^ 63
  | [ty, "toNat"], [.bits w bv] => (uintWidth? ty).isSome ∧ (w < 64 ∨ bv.toNat < 2 ^ 63)
  | [ty, "toBitVec"], [.bits w bv] => (uintWidth? ty).isSome ∧ (w < 64 ∨ bv.toNat < 2 ^ 63)
  | _, _ => True

abbrev PResPost := PVal → Nat → Nat → Nat → Prop
abbrev PResXPost := Nat → Nat → Nat → Nat → Prop
abbrev PResSpec := List PVal → Nat → Nat → Nat → PResPost → PResXPost → Prop
abbrev PResEnv := String → PResSpec
abbrev PResJEnv := Nat → List PVal → Nat → Nat → Nat → Prop

@[expose] def PResEnv.bot : PResEnv := fun _ _ _ _ _ _ _ => False

@[expose] def PResEnv.le (Δ₁ Δ₂ : PResEnv) : Prop :=
  ∀ f as rem wr rcr Q X, Δ₁ f as rem wr rcr Q X → Δ₂ f as rem wr rcr Q X

@[expose] def PResJEnv.empty : PResJEnv := fun _ _ _ _ _ => False

@[expose] def PResJEnv.set (J : PResJEnv) (j : Nat) (P : List PVal → Nat → Nat → Nat → Prop) :
    PResJEnv :=
  fun k as rem wr rcr => if k = j then P as rem wr rcr else J k as rem wr rcr

@[expose] def unboxResSafe (ty : LcTy) : PVal → Prop :=
  match ty with
  | .uint64 | .usize | .float => fun pv => ∃ v, pv = .bits 64 v
  | _ => fun
    | .bits w _ => w < 64
    | .nat n => n < 2 ^ 63
    | .ctor c [] [] => c < 2 ^ 63
    | .erased => True
    | _ => False

@[expose] def casesResSafe (ty : LcTy) : PVal → Prop
  | .ctor _ _ _ => True
  | .erased => True
  | .nat n => n < 2 ^ 63 ∧ ty ≠ .object
  | .bits w _ => ty.isScalar = true ∨ w < 64
  | _ => False

/-- Pure resource-checked `LcVal` weakest precondition tracking `(rem, workRoom, rcRoom)`. -/
@[expose] def PRValWp (env : RcModEnv) (Δr : PResEnv) (ρ : PValEnv)
    (ty : LcTy) (v : LcVal) (rem wr rcr : Nat) (K : PResPost) (X : PResXPost) : Prop :=
  match v with
  | .lit (.nat n) => n < 2 ^ 63 ∧ K (.nat n) rem wr rcr
  | .lit (.scalar n) => K (.bits ty.width (BitVec.ofNat ty.width n)) rem wr rcr
  | .erased => K .erased rem wr rcr
  | .ctor ci as =>
    match ρ.evalArgs as with
    | none => False
    | some vs =>
      match PVal.mkCtor ty ci vs with
      | none => False
      | some r =>
        if ci.isScalar then K r rem wr rcr
        else ci.byteSize ≤ rem ∧ 1 ≤ wr ∧ K r (rem - ci.byteSize) (wr - 1) rcr
  | .oproj i x =>
    match (ρ x).bind (·.getObj? i) with
    | some r => K r rem wr rcr
    | none => False
  | .uproj i x =>
    match (ρ x).bind (·.getUsize? i) with
    | some r => K r rem wr rcr
    | none => False
  | .sproj n off x =>
    match (ρ x).bind (·.getScalar? n off ty) with
    | some r => K r rem wr rcr
    | none => False
  | .box t x =>
    match (ρ x).bind (PVal.box t) with
    | none => False
    | some r =>
      if t == .uint64 || t == .usize || t == .float then
        16 ≤ rem ∧ 1 ≤ wr ∧ K r (rem - 16) (wr - 1) rcr
      else K r rem wr rcr
  | .unbox x =>
    match ρ x, (ρ x).bind (PVal.unbox ty) with
    | some pv, some r => unboxResSafe ty pv ∧ K r rem wr rcr
    | _, _ => False
  | .isShared x =>
    match ρ x with
    | some pv => isTaggedPVal pv = false ∧ ∀ b : Bool, K (PVal.bool b) rem wr rcr
    | none => False
  | .fap f as =>
    match ρ.evalArgs as with
    | none => False
    | some vs =>
      if f == "outOfBounds._redArg" then
        vs.length == 1 ∧ X panicOob rem wr rcr
      else if (env.decls.find? (·.1 == f)).isSome then
        ∃ P E, Δr f vs rem wr rcr P E ∧
          (∀ r rem' wr' rcr', P r rem' wr' rcr' → K r rem' wr' rcr') ∧
          (∀ c rem' wr' rcr', E c rem' wr' rcr' → X c rem' wr' rcr')
      else
        pIsPrimName f = true ∧
        match primP f vs with
        | some r => primResSafe f vs ∧ K r rem wr rcr
        | none => False
  | _ => False

/-- Predicate ensuring `.dec x n` stays off the `DecColdRel` cascade (tagged/persistent/guarded). -/
@[expose] def safeNonColdDec (ctx : RcCtx) (ρ : PValEnv) (x n : Nat) : Prop :=
  match ctx.get? x, ρ x with
  | some v, some pv =>
    v.noRc = true ∨ v.persistent = true ∨ isTaggedPVal pv = true ∨
    n < v.owned ∨ ∃ b, (b, x) ∈ ctx.sharedPreds ∧ (ρ b).bind PVal.tag? = some 1
  | _, _ => False

mutual
/-- Pure resource-aware weakest precondition over `LcCode`. -/
@[expose] def PRWp (m : LcModule) (env : RcModEnv) (retTy : LcTy) (Δr : PResEnv)
    (jps : List RcJpInfo) (ctx : RcCtx) (J : PResJEnv) (ρ : PValEnv)
    (rem wr rcr : Nat) (Q : PResPost) (X : PResXPost) : LcCode → Prop
  | .let_ x ty v k =>
    match checkVal env ctx x ty v with
    | .ok ctx' =>
      PRValWp env Δr ρ ty v rem wr rcr
        (fun r rem' wr' rcr' => PRWp m env retTy Δr jps ctx' J (ρ.set x r) rem' wr' rcr' Q X k) X
    | .error _ => False
  | .jp j ps body k =>
    let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := ctx.vars.map (·.id) }
    let baseCtx := jpBaseCtx env retTy jps ctx j ps k
    ∀ Jj : List PVal → Nat → Nat → Nat → Prop,
      (∀ as rem' wr' rcr', as.length = ps.length →
        PRWp m env retTy Δr jps (baseCtx.bindParams ps) (J.set j Jj)
          (ρ.bindAll ps as) rem' wr' rcr' Q X body →
        Jj as rem' wr' rcr') →
      PRWp m env retTy Δr (jInfo :: jps) ctx (J.set j Jj) ρ rem wr rcr Q X k
  | .jmp j as =>
    match ρ.evalArgs as with
    | some vs => J j vs rem wr rcr
    | none => False
  | .cases x alts =>
    match ctx.get? x, (ρ x).bind PVal.tag?, ρ x with
    | some vx, some tag, some pv =>
      casesResSafe vx.ty pv ∧
      let target? := (ctx.sharedPreds.find? (·.1 == x)).map Prod.snd
      PRWpCtorAlts m env retTy Δr jps ctx x target? pv J ρ tag rem wr rcr Q X alts
        (PRWpDfltAlts m env retTy Δr jps ctx J ρ rem wr rcr Q X alts)
    | _, _, _ => False
  | .ret a =>
    match ρ.evalArg a with
    | some r => Q r rem wr rcr
    | none => False
  | .unreach => X panicUnreachable rem wr rcr
  | .oset x i y k =>
    match ρ x, ρ.evalArg y, ctx.consumeArg y with
    | some xv, some yv, .ok ctx1 =>
      match xv.setObj i yv with
      | some xv' => PRWp m env retTy Δr jps ctx1 J (ρ.set x xv') rem wr rcr Q X k
      | none => False
    | _, _, _ => False
  | .uset x i y k =>
    match ρ x, ρ y with
    | some xv, some yv =>
      match xv.setUsize i yv with
      | some xv' => PRWp m env retTy Δr jps ctx J (ρ.set x xv') rem wr rcr Q X k
      | none => False
    | _, _ => False
  | .sset x n off y ty k =>
    match ρ x, ρ y with
    | some xv, some yv =>
      match xv.setScalar n off ty yv with
      | some xv' => PRWp m env retTy Δr jps ctx J (ρ.set x xv') rem wr rcr Q X k
      | none => False
    | _, _ => False
  | .setTag x cidx k =>
    match (ρ x).bind (·.setTag cidx) with
    | some xv' => PRWp m env retTy Δr jps ctx J (ρ.set x xv') rem wr rcr Q X k
    | none => False
  | .inc x n _ k =>
    match ctx.get? x with
    | none => False
    | some v =>
      if v.noRc || v.persistent || n == 0 then
        PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X k
      else
        let v' := { v with owned := v.owned + n, excl := false }
        n ≤ rcr ∧ PRWp m env retTy Δr jps (ctx.put v') J ρ rem wr (rcr - n) Q X k
  | .dec x n _ k =>
    match ctx.consumeVar x n with
    | .ok ctx1 =>
      safeNonColdDec ctx ρ x n ∧ PRWp m env retTy Δr jps ctx1 J ρ rem wr rcr Q X k
    | .error _ => False
  | .del x k =>
    match ctx.consumeVar x with
    | .ok ctx1 => PRWp m env retTy Δr jps ctx1 J ρ rem wr rcr Q X k
    | .error _ => False

@[expose] def PRWpDfltAlts (m : LcModule) (env : RcModEnv) (retTy : LcTy) (Δr : PResEnv)
    (jps : List RcJpInfo) (ctx : RcCtx) (J : PResJEnv) (ρ : PValEnv)
    (rem wr rcr : Nat) (Q : PResPost) (X : PResXPost) : List (LcPat × LcCode) → Prop
  | [] => False
  | (.dflt, b) :: _ => PRWp m env retTy Δr jps ctx J ρ rem wr rcr Q X b
  | (.ctor _ _, _) :: rest => PRWpDfltAlts m env retTy Δr jps ctx J ρ rem wr rcr Q X rest

@[expose] def PRWpCtorAlts (m : LcModule) (env : RcModEnv) (retTy : LcTy) (Δr : PResEnv)
    (jps : List RcJpInfo) (ctx : RcCtx) (scru : Nat) (target? : Option Nat) (pv : PVal)
    (J : PResJEnv) (ρ : PValEnv) (tag rem wr rcr : Nat) (Q : PResPost) (X : PResXPost) :
    List (LcPat × LcCode) → Prop → Prop
  | [], kDflt => kDflt
  | (.ctor ci cname, b) :: rest, kDflt =>
    if ci = tag then
      let ctx1 := if env.scalarCtors.contains cname then ctx.markScalarBranch scru else ctx
      let ctxBranch := match target?, ci with
        | some tgt, 0 => ctx1.markExcl tgt
        | _, _ => ctx1
      (env.scalarCtors.contains cname = true → isTaggedPVal pv = true) ∧
        PRWp m env retTy Δr jps ctxBranch J ρ rem wr rcr Q X b
    else PRWpCtorAlts m env retTy Δr jps ctx scru target? pv J ρ tag rem wr rcr Q X rest kDflt
  | (.dflt, _) :: rest, kDflt =>
    PRWpCtorAlts m env retTy Δr jps ctx scru target? pv J ρ tag rem wr rcr Q X rest kDflt
end

/-- Non-indexed resource soundness for module `m` wrt `Δr`. -/
@[expose] def PResOk (Δr : PResEnv) (m : LcModule) : Prop :=
  let env := mkRcModEnv m
  ∀ d ∈ m.decls, ∀ as rem wr rcr Q X,
    as.length = d.params.length →
    Δr d.name as rem wr rcr Q X →
    PRWp m env d.retTy Δr [] ((RcCtx.mk [] []).bindParams d.params) PResJEnv.empty
      (PValEnv.empty.bindAll d.params as) rem wr rcr Q X d.body

/-- Measure-indexed resource soundness for module `m` wrt `Δr : Nat → PResEnv`. -/
@[expose] def PResOkIdx (Δr : Nat → PResEnv) (m : LcModule) : Prop :=
  let env := mkRcModEnv m
  (∀ k, PResEnv.le (Δr k) (Δr (k + 1))) ∧
  ∀ k, ∀ d ∈ m.decls, ∀ as rem wr rcr Q X,
    as.length = d.params.length →
    Δr k d.name as rem wr rcr Q X →
    PRWp m env d.retTy (match k with | 0 => PResEnv.bot | k' + 1 => Δr k')
      [] ((RcCtx.mk [] []).bindParams d.params) PResJEnv.empty
      (PValEnv.empty.bindAll d.params as) rem wr rcr Q X d.body

/-- Maximum reference count appearing on any live object in `objs`. -/
@[expose] def maxObjRc (objs : List LcnfObj) : Nat :=
  objs.foldl (fun acc o => Nat.max acc o.rc.toNat) 0

theorem le_maxObjRc_of_mem {objs : List LcnfObj} {o : LcnfObj} (ho : o ∈ objs) :
    o.rc.toNat ≤ maxObjRc objs := by
  have hm : ∀ (l' : List LcnfObj) (z : Nat),
      z ≤ l'.foldl (fun u v => Nat.max u v.rc.toNat) z := by
    intro l'
    induction l' with
    | nil => intro z; exact Nat.le_refl z
    | cons y ys ihz =>
      intro z
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (ihz _)
  have aux : ∀ (l : List LcnfObj) (acc : Nat), o ∈ l →
      o.rc.toNat ≤ l.foldl (fun a x => Nat.max a x.rc.toNat) acc := by
    intro l
    induction l with
    | nil => intro _ h; cases h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | hxs
      · exact Nat.le_trans (Nat.le_max_right acc o.rc.toNat) (hm xs _)
      · exact ih _ hxs
  exact aux objs 0 ho

/-- Resource capacity relation linking Tier-H `σ` to Tier-P budget `(rem, wr, rcr)`. -/
@[expose] def ResStateInv (σ : HState) (rem wr rcr : Nat) : Prop :=
  rem ≤ σ.st.rem ∧
  σ.objs.length + wr ≤ σ.st.workCap ∧
  Nat.max 1 (maxObjRc σ.objs) + rcr < 2 ^ 31 - 1

/-- Handle multiset returned by a declaration of return type `retTy` with word `rw`. -/
@[expose] def retHandles (retTy : LcTy) (rw : Word) : List (BitVec 64) :=
  if retTy.needsRc && !retTy.isScalar then
    match rw.toBV64? with
    | some bv => if bv &&& 1#64 == 0#64 then [bv] else []
    | none => []
  else []

/-- Structural cleanliness invariant on a single `RcVar` (no `resetTok`, disjoint mode bits). -/
@[expose] def CleanVar (v : RcVar) : Prop :=
  ((v.noRc = true →
    v.persistent = false ∧ v.owned = 0 ∧ v.borrowed = false ∧ v.parent? = none ∧ v.excl = false) ∧
   (v.ty.isScalar = true → v.noRc = true)) ∧
  (v.persistent = true →
    v.noRc = false ∧ v.owned = 0 ∧ v.borrowed = false ∧ v.parent? = none ∧ v.excl = false) ∧
  (v.borrowed = true →
    v.noRc = false ∧ v.persistent = false ∧ v.excl = false) ∧
  (v.borrowed = false → v.parent? = none) ∧
  v.resetTok = false

/-- Context-wide `CleanVar` invariant. -/
@[expose] def CleanVars (ctx : RcCtx) : Prop :=
  ∀ v ∈ ctx.vars, CleanVar v

/-- Heap address `a` is an un-aliased `rc = 1` cell unreachable from any live local variable. -/
@[expose] def IsolatedAddr (a : BitVec 64) (rf : RcFrame) (objs : List LcnfObj) : Prop :=
  (∀ v ∈ rf.ctx.vars, v.isLive = true → !v.ty.isScalar = true →
    ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some a) ∧
  nonPersistRefs objs a = 0 ∧
  ∃ o ∈ objs, o.Wf ∧ o.addr = a ∧ o.rc = 1#32

/-- Preservation of runtime metadata and backed heap objects across execution steps. -/
@[expose] def HeapStepRel (ext : List (BitVec 64)) (σ σ' : HState) : Prop :=
  σ'.st.PreservesMeta σ.st ∧ σ'.scr = σ.scr ∧ σ'.scrLimbs = σ.scrLimbs ∧
  (∀ o ∈ σ.objs, o.Wf → Backed σ.objs ext o.addr →
    ∃ o' ∈ σ'.objs, ObjDataEq o o' ∧ (o.rc = 0#32 → o'.rc = 0#32) ∧
      (0 < o.rc.toInt → 0 < o'.rc.toInt)) ∧
  (∀ a, Backed σ.objs ext a → Backed σ'.objs ext a)

/-- Full call-boundary preservation (backed objects + isolated caller exclusives). -/
@[expose] def CallPreserve (as : List Word) (ext : List (BitVec 64)) (σ σ' : HState) : Prop :=
  HeapStepRel ext σ σ' ∧
  (∀ o ∈ σ.objs, o.Wf → o.addr ∈ ext → o.rc = 1#32 → nonPersistRefs σ.objs o.addr = 0 →
    (∀ w ∈ as, w.toBV64? ≠ some o.addr) →
    ∃ o' ∈ σ'.objs, ObjDataEq o o' ∧ o'.rc = 1#32)

/-- Preservation of any isolated external handle across a code fragment. -/
@[expose] def IsolPreserve (rf : RcFrame) (σ σ' : HState) : Prop :=
  ∀ a, a ∈ rf.extH ++ rf.ghostH → IsolatedAddr a rf σ.objs →
    ∃ o' ∈ σ'.objs, o'.Wf ∧ o'.addr = a ∧ o'.rc = 1#32 ∧ nonPersistRefs σ'.objs a = 0 ∧
      ∀ o ∈ σ.objs, o.addr = a → ObjDataEq o o'

/-- Every handle address in `hs` names an allocated object currently in `objs`. -/
@[expose] def HandlesInHeap (hs : List (BitVec 64)) (objs : List LcnfObj) : Prop :=
  ∀ a ∈ hs, ∃ o ∈ objs, o.addr = a

/-- Build initial `RcFrame` for a function entry `d` given argument list `as`, pure args `pvs`,
and caller external handles `extH` + `ghostH`. -/
@[expose] def entryRcFrame (d : LcDecl) (pvs : List PVal) (as : List Word)
    (extH ghostH : List (BitVec 64)) : RcFrame :=
  { ctx := (RcCtx.mk [] []).bindParams d.params
    envP := PValEnv.empty.bindAll d.params pvs
    envH := HValEnv.empty.bindAll d.params as
    extH := extH
    ghostH := ghostH }

/-- Tier-P + resource postcondition lift to Tier-H `HSpec` for `perceus_sound`. -/
@[expose] def hOfP (m : LcModule) (Δp : PEnv) : HEnv :=
  fun fn as σ Q X =>
    ∃ (rt : BitVec 64) (d : LcDecl) (Δr : PResEnv) (pvs : List PVal)
      (extH ghostH : List (BitVec 64)) (rem₀ wr₀ rcr₀ : Nat)
      (Qp : PPost) (Xp : PXPost) (Pr : PResPost) (Er : PResXPost),
      d ∈ m.decls ∧ d.name = fn ∧
      PResOk Δr m ∧
      RcInv rt (entryRcFrame d pvs as extH ghostH) σ ∧
      HandlesInHeap (extH ++ ghostH) σ.objs ∧
      ResStateInv σ rem₀ wr₀ rcr₀ ∧
      pvs.length = d.params.length ∧
      Δp fn pvs Qp Xp ∧
      Δr fn pvs rem₀ wr₀ rcr₀ Pr Er ∧
      (∀ r rw σ' rem' wr' rcr',
        Qp r → Pr r rem' wr' rcr' →
        HeapClean rt σ' →
        ResStateInv σ' rem' wr' rcr' →
        ValRep d.retTy r rw σ'.objs →
        (¬d.retTy.isScalar → ¬d.retTy.needsRc → ∃ bv, rw = Word.i64 bv ∧ (bv &&& 1#64) ≠ 0#64) →
        HandlesRcSound (retHandles d.retTy rw ++ extH ++ ghostH) σ'.objs →
        CallPreserve (nonScalarWords d.params as) (extH ++ ghostH) σ σ' →
        Q rw σ') ∧
      (∀ c rem' wr' rcr' σ', Xp c → Er c rem' wr' rcr' → X (BitVec.ofNat 64 c) σ')

/-- Measure-indexed Tier-P + resource lifter `hOfPIdx` for `perceus_sound_idx`. -/
@[expose] def hOfPIdx (m : LcModule) (Δp : Nat → PEnv) (k : Nat) : HEnv :=
  fun fn as σ Q X =>
    ∃ (rt : BitVec 64) (d : LcDecl) (Δr : Nat → PResEnv) (pvs : List PVal)
      (extH ghostH : List (BitVec 64)) (rem₀ wr₀ rcr₀ : Nat)
      (Qp : PPost) (Xp : PXPost) (Pr : PResPost) (Er : PResXPost),
      d ∈ m.decls ∧ d.name = fn ∧
      PResOkIdx Δr m ∧
      RcInv rt (entryRcFrame d pvs as extH ghostH) σ ∧
      HandlesInHeap (extH ++ ghostH) σ.objs ∧
      ResStateInv σ rem₀ wr₀ rcr₀ ∧
      pvs.length = d.params.length ∧
      Δp k fn pvs Qp Xp ∧
      Δr k fn pvs rem₀ wr₀ rcr₀ Pr Er ∧
      (∀ r rw σ' rem' wr' rcr',
        Qp r → Pr r rem' wr' rcr' →
        HeapClean rt σ' →
        ResStateInv σ' rem' wr' rcr' →
        ValRep d.retTy r rw σ'.objs →
        (¬d.retTy.isScalar → ¬d.retTy.needsRc → ∃ bv, rw = Word.i64 bv ∧ (bv &&& 1#64) ≠ 0#64) →
        HandlesRcSound (retHandles d.retTy rw ++ extH ++ ghostH) σ'.objs →
        CallPreserve (nonScalarWords d.params as) (extH ++ ghostH) σ σ' →
        Q rw σ') ∧
      (∀ c rem' wr' rcr' σ', Xp c → Er c rem' wr' rcr' → X (BitVec.ofNat 64 c) σ')

theorem hOfPIdx_le {m : LcModule} {Δp : Nat → PEnv}
    (hp : ∀ k, PEnv.le (Δp k) (Δp (k + 1))) (k : Nat) :
    HEnv.le (hOfPIdx m Δp k) (hOfPIdx m Δp (k + 1)) := by
  intro fn as σ Q X ⟨rt, d, Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀, Qp, Xp, Pr, Er,
    hd, hnm, hidx, hinv, hhih, hres, hlen, hdp, hdr, hq, hx⟩
  exact ⟨rt, d, Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀, Qp, Xp, Pr, Er,
    hd, hnm, hidx, hinv, hhih, hres, hlen, hp k _ _ _ _ hdp,
    hidx.1 k _ _ _ _ _ _ _ hdr, hq, hx⟩

/-! ## 3. Heap & `RcFrame` Transitions (`alloc`, `bind`, `consumeVar`, `applyArgs`) -/

private theorem nonPersistRefs_zero_of_not_in_closed {objs : List LcnfObj}
    (hcl : lcnfHeapClosed objs) {a : BitVec 64} (ha0 : (a &&& 1#64) = 0#64)
    (hnot : ∀ o ∈ objs, o.addr ≠ a) : nonPersistRefs objs a = 0 := by
  have haux : ∀ (l : List LcnfObj) (acc : Nat),
      (∀ o ∈ l, ∀ f ∈ o.childFields, (f &&& 1#64) = 0#64 → ∃ q ∈ objs, q.addr = f) →
      List.foldl (fun acc p => if p.rc = 0#32 then acc else acc + List.count a p.childFields)
        acc l = acc := by
    intro l
    induction l with
    | nil => intro acc _; rfl
    | cons x xs ih =>
      intro acc hcl'
      simp only [List.foldl_cons]
      have hcnt : List.count a x.childFields = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨q, hq, hqa⟩ := hcl' x List.mem_cons_self a hmem ha0
        exact hnot q hq hqa
      simp only [hcnt, Nat.add_zero, ite_self]
      exact ih acc (fun o ho => hcl' o (List.mem_cons_of_mem _ ho))
  exact haux objs 0 hcl

theorem heapClean_fresh_alloc {rt : BitVec 64} {σ : HState}
    (hc : HeapClean rt σ) {newObj : LcnfObj} {st' : RtC0State} {scrLimbs' : List (BitVec 64)}
    (hbn : BigNumRtWfR0 rt st' σ.scr scrLimbs')
    (hwfNew : newObj.Wf) (hrcNew : newObj.rc.toNat < 2 ^ 31 - 1)
    (hfresh : ∀ o ∈ σ.objs, o.addr ≠ newObj.addr)
    (hwc : σ.objs.length + 1 ≤ st'.workCap)
    (hcfClosed : ∀ f ∈ newObj.childFields, (f &&& 1#64) = 0#64 → ∃ q ∈ σ.objs, q.addr = f) :
    HeapClean rt { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := scrLimbs' } := by
  refine ⟨⟨hbn, ?_, ?_, hwc, ?_⟩, ?_⟩
  · intro o ho
    rcases List.mem_cons.mp ho with rfl | ho'
    · exact hwfNew
    · exact hc.1.2.1 o ho'
  · intro o ho f hf hf0
    rcases List.mem_cons.mp ho with rfl | ho'
    · obtain ⟨q, hq, hqa⟩ := hcfClosed f hf hf0
      exact ⟨q, List.mem_cons_of_mem _ hq, hqa⟩
    · obtain ⟨q, hq, hqa⟩ := hc.1.2.2.1 o ho' f hf hf0
      exact ⟨q, List.mem_cons_of_mem _ hq, hqa⟩
  · intro o ho
    rcases List.mem_cons.mp ho with rfl | ho'
    · exact hrcNew
    · exact hc.1.2.2.2.2 o ho'
  · simp only [List.map_cons, List.nodup_cons, List.mem_map]
    exact ⟨fun ⟨o, ho, hoa⟩ => hfresh o ho hoa, hc.2⟩

theorem handlesRcSound_fresh_alloc {objs : List LcnfObj} {handles newHandles : List (BitVec 64)}
    (hs : HandlesRcSound handles objs) (hcl : lcnfHeapClosed objs) {newObj : LcnfObj}
    (hwfNew : newObj.Wf) (hrcNew : newObj.rc = 1#32)
    (hfresh : ∀ o ∈ objs, o.addr ≠ newObj.addr)
    (hnotSelf : newObj.addr ∉ newObj.childFields)
    (hconsNew : newHandles.count newObj.addr ≤ 1)
    (hconsOld : ∀ o ∈ objs, newHandles.count o.addr + newObj.childFields.count o.addr ≤
      handles.count o.addr) :
    HandlesRcSound newHandles (newObj :: objs) := by
  constructor
  · intro p hp hrc0 f hf hf0
    rcases List.mem_cons.mp hp with rfl | hp'
    · rw [hrcNew] at hrc0; cases hrc0
    · obtain ⟨q, hq, hqa, hqrc⟩ := hs.1 p hp' hrc0 f hf hf0
      exact ⟨q, List.mem_cons_of_mem _ hq, hqa, hqrc⟩
  · intro y hy hpos
    rw [nonPersistRefs_cons]
    rcases List.mem_cons.mp hy with hyeq | hy'
    · rw [hyeq]
      have hnp : nonPersistRefs objs newObj.addr = 0 :=
        nonPersistRefs_zero_of_not_in_closed hcl (obj_addr_and1_zero hwfNew) hfresh
      have hc0 : newObj.childFields.count newObj.addr = 0 := List.count_eq_zero.mpr hnotSelf
      rw [hnp, hc0, hrcNew]
      simpa using hconsNew
    · have hprev := hs.2 y hy' hpos
      have hco := hconsOld y hy'
      have hrcn : newObj.rc ≠ 0#32 := by rw [hrcNew]; decide
      simp only [hrcn, ↓reduceIte]
      omega

theorem maxObjRc_cons {o : LcnfObj} {objs : List LcnfObj} (hrc : o.rc.toNat ≤ 1) :
    Nat.max 1 (maxObjRc (o :: objs)) = Nat.max 1 (maxObjRc objs) := by
  have hm_add : ∀ (l : List LcnfObj) (a : Nat),
      Nat.max 1 (l.foldl (fun u v => Nat.max u v.rc.toNat) a) =
      l.foldl (fun u v => Nat.max u v.rc.toNat) (Nat.max 1 a) := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x xs ih =>
      intro a
      simp only [List.foldl_cons]
      rw [ih]
      have hm : Nat.max 1 (Nat.max a x.rc.toNat) = Nat.max (Nat.max 1 a) x.rc.toNat := by
        simp only [Nat.max_def]
        repeat' split
        all_goals omega
      exact congrArg (fun m => List.foldl (fun u v => Nat.max u v.rc.toNat) m xs) hm
  unfold maxObjRc
  simp only [List.foldl_cons, Nat.zero_max]
  rw [hm_add objs o.rc.toNat, hm_add objs 0]
  have h1 : Nat.max 1 o.rc.toNat = 1 := Nat.max_eq_left hrc
  have h2 : Nat.max 1 0 = 1 := rfl
  rw [h1, h2]

theorem resStateInv_fresh_alloc {σ : HState} {rem wr rcr bytes : Nat}
    (hres : ResStateInv σ rem wr rcr) (hbytes : bytes ≤ rem) (hwr : 1 ≤ wr)
    {newObj : LcnfObj} (hrc1 : newObj.rc = 1#32)
    {st' : RtC0State} {scrLimbs' : List (BitVec 64)}
    (hrem' : σ.st.rem - bytes ≤ st'.rem) (hwc' : st'.workCap = σ.st.workCap) :
    ResStateInv { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := scrLimbs' }
      (rem - bytes) (wr - 1) rcr := by
  rcases hres with ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp only; omega
  · simp only [List.length_cons, hwc']; omega
  · rw [maxObjRc_cons (by rw [hrc1]; decide)]
    exact h3

theorem binderFresh_varHandles_empty {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {envH : HValEnv} {x : Nat} (hfr : binderFreshOwned ctx x = true) :
    ∀ v ∈ ctx.vars, v.id = x → varHandles envH v = [] := by
  intro v hv rfl
  simp only [binderFreshOwned, Bool.and_eq_true] at hfr
  have hgx := (RcCtx.mem_get?_iff hnd).mpr hv
  rw [hgx] at hfr
  have hnl : v.isLive = false := by cases h : v.isLive <;> simp_all
  simp only [RcVar.isLive, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt,
    Nat.le_zero] at hnl
  rcases hnl with ⟨⟨⟨⟨h1, h2⟩, h3⟩, _h4⟩, h5⟩
  unfold varHandles
  rw [h1, h2, h5, h3]
  rfl

theorem objDataEq_childFields {o o' : LcnfObj} (h : ObjDataEq o o') :
    o'.childFields = o.childFields := by
  rcases h with ⟨_, _, ht, hf, _⟩
  unfold LcnfObj.childFields
  rw [ht, hf]

theorem objDataEq_trans {o1 o2 o3 : LcnfObj} (h12 : ObjDataEq o1 o2) (h23 : ObjDataEq o2 o3) :
    ObjDataEq o1 o3 := by
  rcases h12 with ⟨a1, w1, t1, f1, s1, as1, sl1, l1, c1, o1', cs1⟩
  rcases h23 with ⟨a2, w2, t2, f2, s2, as2, sl2, l2, c2, o2', cs2⟩
  exact ⟨a2.trans a1, w2, t2.trans t1, f2.trans f1, s2.trans s1, as2.trans as1,
    sl2.trans sl1, l2.trans l1, c2.trans c1, o2'.trans o1', cs2.trans cs1⟩

theorem bigNumRtWfR0_of_preservesMeta {rt : BitVec 64} {st st' : RtC0State}
    {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    (hwf : BigNumRtWfR0 rt st scr scrLimbs) (hp : st'.PreservesMeta st) :
    BigNumRtWfR0 rt st' scr scrLimbs := by
  rcases hwf with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨?_, h2, h3, h4, h5, h6⟩
  unfold RtC0State.Bounded48 at h1 ⊢
  rw [← hp.2.2.2.1]
  exact h1

theorem rc_toInt_pos_of_ne_zero {rc : BitVec 32} (h0 : 0 ≤ rc.toInt) (hne : rc ≠ 0#32) :
    0 < rc.toInt := by
  have hne0 : rc.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  rw [BitVec.toInt_eq_toNat_cond] at h0 ⊢
  split at h0 <;> omega

theorem backed_of_objPres {ext : List (BitVec 64)} {objs objs' : List LcnfObj}
    (hwf : ∀ o ∈ objs, o.Wf)
    (hpres : ∀ o ∈ objs, o.Wf → Backed objs ext o.addr →
      ∃ o' ∈ objs', ObjDataEq o o' ∧ (o.rc = 0#32 → o'.rc = 0#32) ∧
        (0 < o.rc.toInt → 0 < o'.rc.toInt)) :
    ∀ a, Backed objs ext a → Backed objs' ext a := by
  intro a ha
  rcases ha with ⟨o, ho, hoa, hrc0⟩ | ⟨r, hr, hreach⟩
  · obtain ⟨o', ho', hd, h0, _⟩ := hpres o ho (hwf o ho) (Or.inl ⟨o, ho, rfl, hrc0⟩)
    exact Or.inl ⟨o', ho', hd.1.trans hoa, h0 hrc0⟩
  · suffices h : NonPersistReach objs' r a from Or.inr ⟨r, hr, h⟩
    induction hreach with
    | refl h =>
      rcases h with ⟨o, ho, hoa, hnz⟩
      have hpos : 0 < o.rc.toInt := rc_toInt_pos_of_ne_zero (hwf o ho).2.2.1 hnz
      have hbo : Backed objs ext o.addr :=
        hoa ▸ Or.inr ⟨r, hr, NonPersistReach.refl ⟨o, ho, hoa, hnz⟩⟩
      obtain ⟨o', ho', hd, _, hpos'⟩ := hpres o ho (hwf o ho) hbo
      have ho'nz : o'.rc ≠ 0#32 := by intro h0; have := hpos' hpos; rw [h0] at this; simp at this
      exact NonPersistReach.refl ⟨o', ho', hd.1.trans hoa, ho'nz⟩
    | @step u v _ hmem hv0 hnz ih =>
      rcases hmem with ⟨o, ho, hoa, hvcf⟩
      have hbu : Backed objs ext u := Or.inr ⟨r, hr, ‹NonPersistReach objs r u›⟩
      obtain ⟨o', ho', hd, _, _⟩ := hpres o ho (hwf o ho) (hoa ▸ hbu)
      rcases hnz with ⟨ov, hov, hova, hovnz⟩
      have hbv : Backed objs ext v :=
        Or.inr ⟨r, hr, NonPersistReach.step ‹_› ⟨o, ho, hoa, hvcf⟩ hv0 ⟨ov, hov, hova, hovnz⟩⟩
      have hvpos : 0 < ov.rc.toInt := rc_toInt_pos_of_ne_zero (hwf ov hov).2.2.1 hovnz
      obtain ⟨ov', hov', hdv, _, hvpos'⟩ := hpres ov hov (hwf ov hov) (hova ▸ hbv)
      have hov'nz : ov'.rc ≠ 0#32 := by
        intro h0; have := hvpos' hvpos; rw [h0] at this; simp at this
      have hcf' := objDataEq_childFields hd
      exact NonPersistReach.step ih ⟨o', ho', hd.1.trans hoa, hcf'.symm ▸ hvcf⟩
        hv0 ⟨ov', hov', hdv.1.trans hova, hov'nz⟩

theorem heapStepRel_refl (ext : List (BitVec 64)) (σ : HState) : HeapStepRel ext σ σ :=
  ⟨RtC0State.PreservesMeta.refl σ.st, rfl, rfl,
    fun o ho hwf _ => ⟨o, ho, objDataEq_refl o hwf, fun h => h, fun h => h⟩, fun _ h => h⟩

theorem heapStepRel_trans {ext : List (BitVec 64)} {σ₁ σ₂ σ₃ : HState}
    (h12 : HeapStepRel ext σ₁ σ₂) (h23 : HeapStepRel ext σ₂ σ₃) : HeapStepRel ext σ₁ σ₃ := by
  rcases h12 with ⟨pm12, sc12, sl12, op12, bp12⟩
  rcases h23 with ⟨pm23, sc23, sl23, op23, bp23⟩
  refine ⟨RtC0State.PreservesMeta.trans pm12 pm23, sc23.trans sc12, sl23.trans sl12, ?_, ?_⟩
  · intro o ho hwf hb
    obtain ⟨o2, ho2, hd12, h012, hp12⟩ := op12 o ho hwf hb
    have hb2 : Backed σ₂.objs ext o2.addr := hd12.1.symm ▸ bp12 o.addr hb
    obtain ⟨o3, ho3, hd23, h023, hp23⟩ := op23 o2 ho2 hd12.2.1 hb2
    exact ⟨o3, ho3, objDataEq_trans hd12 hd23, fun h => h023 (h012 h), fun h => hp23 (hp12 h)⟩
  · intro a ha; exact bp23 a (bp12 a ha)

theorem heapStepRel_mono_ext {ext₁ ext₂ : List (BitVec 64)} {σ σ' : HState}
    (hwf : ∀ o ∈ σ.objs, o.Wf) (hsub : ∀ a ∈ ext₁, a ∈ ext₂)
    (h : HeapStepRel ext₂ σ σ') : HeapStepRel ext₁ σ σ' := by
  rcases h with ⟨pm, sc, sl, op, _⟩
  have hpres : ∀ o ∈ σ.objs, o.Wf → Backed σ.objs ext₁ o.addr →
      ∃ o' ∈ σ'.objs, ObjDataEq o o' ∧ (o.rc = 0#32 → o'.rc = 0#32) ∧
        (0 < o.rc.toInt → 0 < o'.rc.toInt) :=
    fun o ho hwo hb => op o ho hwo (backed_mono_roots hsub hb)
  exact ⟨pm, sc, sl, hpres, backed_of_objPres hwf hpres⟩

theorem cleanVar_bindOwned (x : Nat) (ty : LcTy) (excl pers : Bool) :
    CleanVar { id := x, ty, noRc := !ty.needsRc
               persistent := if !ty.needsRc then false else pers
               owned := if !ty.needsRc || pers then 0 else 1
               borrowed := false, parent? := none
               excl := if !ty.needsRc || pers then false else excl
               resetTok := false } := by
  cases ty <;> cases pers <;> simp [CleanVar, LcTy.needsRc, LcTy.isScalar]

theorem cleanVar_bindBorrowed (x : Nat) (ty : LcTy) (parent? : Option Nat) (pers : Bool) :
    CleanVar { id := x, ty, noRc := !ty.needsRc
               persistent := if !ty.needsRc then false else pers
               owned := 0, borrowed := !!ty.needsRc && !pers
               parent? := if !ty.needsRc || pers then none else parent?
               excl := false, resetTok := false } := by
  cases ty <;> cases pers <;> simp [CleanVar, LcTy.needsRc, LcTy.isScalar]

theorem cleanVars_put {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) {v : RcVar} (hv : CleanVar v) : CleanVars (ctx.put v) := by
  intro w hw
  rcases (RcCtx.put_mem_iff hnd).mp hw with rfl | ⟨hwm, _⟩
  · exact hv
  · exact hc w hwm

theorem cleanVars_invalidateChildren {ctx : RcCtx} (hc : CleanVars ctx) (p : Nat) :
    CleanVars (ctx.invalidateChildren p) := by
  intro w hw
  unfold RcCtx.invalidateChildren at hw
  simp only [List.mem_map] at hw
  rcases hw with ⟨u, hu, rfl⟩
  have hcu := hc u hu
  by_cases hp : (u.parent? == some p) = true
  · simp only [hp, ↓reduceIte, CleanVar] at hcu ⊢
    rcases hcu with ⟨h1, h2, _, _, h5⟩
    exact ⟨⟨fun hn => by simp [h1.1 hn], h1.2⟩, fun hps => by simp [h2 hps],
      fun hb => Bool.noConfusion hb, fun _ => True.intro, h5⟩
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]; exact hcu

theorem cleanVars_bindOwned {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (x : Nat) (ty : LcTy) (excl pers : Bool) :
    CleanVars (ctx.bindOwned x ty excl pers false) := by
  have h := cleanVar_bindOwned x ty excl pers
  simpa [RcCtx.bindOwned] using cleanVars_put hnd hc h

theorem cleanVars_bindBorrowed {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (x : Nat) (ty : LcTy) (p? : Option Nat) (pers : Bool) :
    CleanVars (ctx.bindBorrowed x ty p? pers) :=
  cleanVars_put hnd hc (cleanVar_bindBorrowed x ty p? pers)

theorem cleanVars_consumeVar {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) {x n : Nat} {ctx' : RcCtx}
    (hcons : ctx.consumeVar x n = .ok ctx') : CleanVars ctx' := by
  unfold RcCtx.consumeVar at hcons
  cases hgx : ctx.get? x with
  | none => simp [hgx] at hcons
  | some v =>
    rw [hgx] at hcons
    have hcv := hc v (RcCtx.get?_mem hgx).1
    by_cases hnop : (v.noRc || v.persistent) = true
    · simp only [hnop, ↓reduceIte, pure] at hcons; cases hcons; exact hc
    · simp only [hnop, Bool.false_eq_true, ↓reduceIte] at hcons
      by_cases hn0 : n == 0
      · simp only [hn0, ↓reduceIte, pure] at hcons; cases hcons; exact hc
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte] at hcons
        by_cases hlt : v.owned < n
        · simp [hlt] at hcons
        · simp only [hlt, ↓reduceIte] at hcons
          have hno : v.noRc = false := by cases h : v.noRc <;> simp_all
          have hps : v.persistent = false := by cases h : v.persistent <;> simp_all
          let v' : RcVar :=
            { v with
              owned := v.owned - n
              excl := if v.owned - n == 0 then false else v.excl
              resetTok := if v.owned - n == 0 then false else v.resetTok }
          have hcv' : CleanVar v' := by
            refine ⟨⟨fun h => absurd h (by simp [v', hno]), hcv.1.2⟩,
              fun h => absurd h (by simp [v', hps]),
              fun hb => ⟨by simp [v', hno], by simp [v', hps], ?_⟩,
              fun hnb => hcv.2.2.2.1 hnb, ?_⟩
            · dsimp only [v']; split; rfl; exact (hcv.2.2.1 hb).2.2
            · dsimp only [v']; split; rfl; exact hcv.2.2.2.2
          have hput := cleanVars_put hnd hc hcv'
          change (if (v.owned - n == 0 && !v.borrowed) = true then
            Except.ok ((ctx.put v').invalidateChildren x) else Except.ok (ctx.put v')) =
              Except.ok ctx' at hcons
          by_cases hinv : (v.owned - n == 0 && !v.borrowed) = true
          · rw [ite_eq_left hinv] at hcons; cases hcons; exact cleanVars_invalidateChildren hput x
          · rw [ite_eq_right hinv] at hcons; cases hcons; exact hput

theorem consumeVar_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {x n : Nat} {ctx' : RcCtx} (hcons : ctx.consumeVar x n = .ok ctx') :
    (ctx'.vars.map RcVar.id).Nodup := by
  unfold RcCtx.consumeVar at hcons
  cases hgx : ctx.get? x with
  | none => simp [hgx] at hcons
  | some v =>
    rw [hgx] at hcons
    by_cases hnop : (v.noRc || v.persistent) = true
    · simp only [hnop, ↓reduceIte, pure] at hcons; cases hcons; exact hnd
    · simp only [hnop, Bool.false_eq_true, ↓reduceIte] at hcons
      by_cases hn0 : n == 0
      · simp only [hn0, ↓reduceIte, pure] at hcons; cases hcons; exact hnd
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte] at hcons
        by_cases hlt : v.owned < n
        · simp [hlt] at hcons
        · simp only [hlt, ↓reduceIte] at hcons
          let v' : RcVar :=
            { v with
              owned := v.owned - n
              excl := if v.owned - n == 0 then false else v.excl
              resetTok := if v.owned - n == 0 then false else v.resetTok }
          have hnd' := ctx.put_nodup hnd v'
          change (if (v.owned - n == 0 && !v.borrowed) = true then
            Except.ok ((ctx.put v').invalidateChildren x) else Except.ok (ctx.put v')) =
              Except.ok ctx' at hcons
          by_cases hinv : (v.owned - n == 0 && !v.borrowed) = true
          · rw [ite_eq_left hinv] at hcons; cases hcons
            unfold RcCtx.invalidateChildren
            dsimp only
            rw [List.map_map]
            have heq : (List.map (RcVar.id ∘ fun v_1 =>
                if v_1.parent? == some x then { v_1 with borrowed := false, parent? := none }
                else v_1) (ctx.put v').vars) = (ctx.put v').vars.map RcVar.id := by
              congr 1; funext u; by_cases hpx : u.parent? = some x <;> simp [hpx]
            rw [heq]; exact hnd'
          · rw [ite_eq_right hinv] at hcons; cases hcons; exact hnd'

theorem cleanVars_applyArgs {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (as : List LcArg) (bs : List Bool) {ctx' : RcCtx}
    (ha : ctx.applyArgs as bs = .ok ctx') :
    CleanVars ctx' ∧ (ctx'.vars.map RcVar.id).Nodup := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil => simp [RcCtx.applyArgs, pure] at ha; cases ha; exact ⟨hc, hnd⟩
    | cons _ _ => simp [RcCtx.applyArgs] at ha
  | cons a as ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hcarg : ctx.checkArgLive a with
        | error e => simp [hcarg] at ha
        | ok u =>
          simp only [hcarg] at ha
          exact ih hnd hc bs ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a with
        | error e => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          have ⟨hc1, hnd1⟩ : CleanVars ctx1 ∧ (ctx1.vars.map RcVar.id).Nodup := by
            cases a with
            | erased => simp [RcCtx.consumeArg, pure] at hcarg; cases hcarg; exact ⟨hc, hnd⟩
            | var id =>
              exact ⟨cleanVars_consumeVar hnd hc hcarg, consumeVar_nodup hnd hcarg⟩
          exact ih hnd1 hc1 bs ha

theorem cleanVars_bindParams {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (ps : List LcParam) :
    CleanVars (ctx.bindParams ps) ∧ ((ctx.bindParams ps).vars.map RcVar.id).Nodup := by
  induction ps generalizing ctx with
  | nil => exact ⟨hc, hnd⟩
  | cons p ps ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]
    by_cases hb : p.borrow = true
    · simp only [hb, ↓reduceIte]
      exact ih (ctx.put_nodup hnd _) (cleanVars_bindBorrowed hnd hc p.id p.ty none false)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact ih (ctx.put_nodup hnd _) (cleanVars_bindOwned hnd hc p.id p.ty false false)

theorem entryRcFrame_clean (d : LcDecl) :
    CleanVars ((RcCtx.mk [] []).bindParams d.params) ∧
    (((RcCtx.mk [] []).bindParams d.params).vars.map RcVar.id).Nodup :=
  cleanVars_bindParams (by simp : (List.map RcVar.id (RcCtx.mk [] []).vars).Nodup)
    (fun _ h => by cases h) d.params

private theorem filter_eq_self_of {α : Type} (p : α → Bool) :
    ∀ xs : List α, (∀ x ∈ xs, p x = true) → xs.filter p = xs
  | [], _ => rfl
  | x :: xs, hp => by
    simp only [List.filter_cons, hp x List.mem_cons_self, ↓reduceIte]
    exact congrArg (x :: ·) (filter_eq_self_of p xs fun y hy => hp y (List.mem_cons_of_mem _ hy))

theorem localHandlesExcept_fresh_perm {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {envH : HValEnv} {x : Nat} (hfr : binderFreshOwned ctx x = true) :
    (localHandlesExcept ctx envH x).Perm (localHandles ctx envH) := by
  cases hgx : ctx.get? x with
  | some u =>
    have ⟨hum, huid⟩ := RcCtx.get?_mem hgx
    have hperm := localHandles_perm_filter hnd envH u hum
    rw [huid] at hperm
    rw [binderFresh_varHandles_empty hnd hfr u hum huid, List.nil_append] at hperm
    exact hperm.symm
  | none =>
    have hflt : ctx.vars.filter (fun v => v.id != x) = ctx.vars := by
      apply filter_eq_self_of
      intro v hv
      simp only [bne_iff_ne, ne_eq]
      intro rfl
      exact absurd ((RcCtx.mem_get?_iff hnd).mpr hv) (by rw [hgx]; simp)
    unfold localHandlesExcept localHandles
    rw [hflt]

theorem localHandlesExcept_put_zero_count {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {envH envH' : HValEnv} {v : RcVar} (hfr : binderFreshOwned ctx v.id = true)
    (hother : ∀ y, y ≠ v.id → envH' y = envH y) (hv0 : varHandles envH' v = [])
    {s : Nat} (hne : s ≠ v.id) {u : RcVar} (hu : u ∈ ctx.vars) (hus : u.id = s)
    (a : BitVec 64) :
    (localHandlesExcept (ctx.put v) envH' s).count a =
      (localHandlesExcept ctx envH s).count a := by
  have hnd' := ctx.put_nodup hnd v
  have hu' : u ∈ (ctx.put v).vars := (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hu, hus ▸ hne⟩)
  have hp1 := localHandles_put_perm hnd envH' v
  rw [hv0, List.nil_append, localHandlesExcept_congr_env v.id hother] at hp1
  have hp2 := hp1.trans (localHandlesExcept_fresh_perm hnd hfr)
  have hpL := localHandles_perm_filter hnd' envH' u hu'
  have hpR := localHandles_perm_filter hnd envH u hu
  rw [hus] at hpL hpR
  have hvu : varHandles envH' u = varHandles envH u :=
    varHandles_subset_eq (hother u.id (hus ▸ hne)).symm
  have hcEq := hp2.count_eq a
  have hcL := hpL.count_eq a
  have hcR := hpR.count_eq a
  rw [hvu, List.count_append] at hcL
  rw [List.count_append] at hcR
  omega

theorem rcInv_put_fresh {rt : BitVec 64} {rf : RcFrame} {σ σ' : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {x : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    {vx : RcVar} (hxid : vx.id = x) (hcv : CleanVar vx)
    {pv : PVal} {w : Word} {ghostH' : List (BitVec 64)}
    (hc' : HeapClean rt σ')
    (hpres : ∀ o ∈ σ.objs, o.Wf → ∃ o' ∈ σ'.objs, ObjDataEq o o' ∧ o'.rc = o.rc)
    (hvarX : VarInv vx { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                         envH := rf.envH.set x vx.ty w, extH := rf.extH, ghostH := ghostH' }
               σ'.objs)
    (hhs : HandlesRcSound (varHandles (rf.envH.set x vx.ty w) vx ++
             localHandles rf.ctx rf.envH ++ rf.extH ++ ghostH') σ'.objs)
    (hback : ∀ bv, Backed σ.objs (frameHandles rf) bv →
      Backed σ'.objs (frameHandles { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                                     envH := rf.envH.set x vx.ty w
                                     extH := rf.extH, ghostH := ghostH' }) bv)
    (hbackExt : ∀ bv, Backed σ.objs (rf.extH ++ rf.ghostH) bv →
      Backed σ'.objs (rf.extH ++ ghostH') bv)
    (hsh : SharedPredInv { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                           envH := rf.envH.set x vx.ty w, extH := rf.extH, ghostH := ghostH' }
             σ'.objs) :
    let rf' : RcFrame :=
      { ctx := rf.ctx.put vx, envP := rf.envP.set x pv, envH := rf.envH.set x vx.ty w
        extH := rf.extH, ghostH := ghostH' }
    RcInv rt rf' σ' ∧ CleanVars rf'.ctx := by
  rcases hinv with ⟨hc, hnd, _, hvars, _⟩
  let rf' : RcFrame :=
    { ctx := rf.ctx.put vx, envP := rf.envP.set x pv, envH := rf.envH.set x vx.ty w
      extH := rf.extH, ghostH := ghostH' }
  have hotherP : ∀ y, y ≠ x → rf'.envP y = rf.envP y := fun y hy => by
    simp [rf', PValEnv.set, hy]
  have hotherH : ∀ y, y ≠ x → rf'.envH y = rf.envH y := fun y hy => by
    simp [rf', HValEnv.set, hy]
  have hpar : ∀ u ∈ rf.ctx.vars, u.parent? ≠ some x := by
    have ha := hfr
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at ha
    exact ha.1.1
  have hnd' := rf.ctx.put_nodup hnd vx
  have hpermH : (frameHandles rf').Perm
      (varHandles rf'.envH vx ++ localHandles rf.ctx rf.envH ++ rf.extH ++ ghostH') := by
    unfold frameHandles
    have hp := localHandles_put_perm hnd rf'.envH vx
    rw [hxid, localHandlesExcept_congr_env x hotherH] at hp
    have hp2 := hp.trans ((localHandlesExcept_fresh_perm hnd hfr).append_left _)
    have hp3 := (hp2.append_right rf.extH).append_right ghostH'
    simpa [List.append_assoc] using hp3
  refine ⟨⟨hc', hnd', handlesRcSound_of_perm hpermH.symm hhs, ?_, hsh⟩,
    cleanVars_put hnd hclean hcv⟩
  intro u hu hlive
  rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hum, hne⟩
  · exact hvarX hlive
  · rw [hxid] at hne
    obtain ⟨pu, wu, hpu, hwu, hrep, hnon⟩ := hvars u hum hlive
    have hrep' : ValRep u.ty pu wu σ'.objs :=
      valRep_mono_pred (P := fun _ => True)
        (fun o ho hwo _ => let ⟨o', ho', hd, _⟩ := hpres o ho hwo; ⟨o', ho', hd⟩)
        (fun _ _ _ _ _ _ _ => trivial) hrep (fun _ _ _ _ => trivial)
    refine ⟨pu, wu, (hotherP u.id hne).trans hpu, (hotherH u.id hne).trans hwu, hrep', ?_⟩
    intro hns
    obtain ⟨bv, hwbv, hno, hpers, hexcl, hbr⟩ := hnon hns
    refine ⟨bv, hwbv, hno, ?_, ?_, ?_⟩
    · intro hp bv0
      obtain ⟨o, ho, hoa, h0⟩ := hpers hp bv0
      obtain ⟨o', ho', hd, hrc⟩ := hpres o ho (hc.1.2.1 o ho)
      exact ⟨o', ho', hd.1.trans hoa, hrc.symm ▸ h0⟩
    · intro he
      obtain ⟨he1, he2, he3, he4⟩ := hexcl he
      refine ⟨he1, he2, he3, fun bv0 => ?_⟩
      obtain ⟨o, ho, hoa, h1⟩ := he4 bv0
      obtain ⟨o', ho', hd, hrc⟩ := hpres o ho (hc.1.2.1 o ho)
      exact ⟨o', ho', hd.1.trans hoa, hrc.symm ▸ h1⟩
    · intro hno0 hp0 hb0 bv0
      obtain ⟨hb1, hb2⟩ := hbr hno0 hp0 hb0 bv0
      refine ⟨hback bv hb1, ?_⟩
      cases hpar_u : u.parent? with
      | none => rw [hpar_u] at hb2; exact hbackExt bv hb2
      | some p =>
        rw [hpar_u] at hb2
        obtain ⟨pv', hpvm, hpvid, hpv1, hpv2, hpv3, hpback⟩ := hb2
        have hpne : pv'.id ≠ x := by rw [hpvid]; intro rfl; exact hpar u hum hpar_u
        have hpx : p ≠ x := hpvid ▸ hpne
        refine ⟨pv', (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hxid.symm ▸ hpne⟩),
          hpvid, hpv1, hpv2, hpv3, ?_⟩
        dsimp only
        rw [show rf.envH.set x vx.ty w p = rf.envH p from hotherH p hpx]
        rcases hpback with ⟨o, ho, hoa, hrc0⟩ | ⟨r, hr, hreach⟩
        · obtain ⟨o', ho', hd, hrc⟩ := hpres o ho (hc.1.2.1 o ho)
          exact Or.inl ⟨o', ho', hd.1.trans hoa, hrc.symm ▸ hrc0⟩
        · rcases List.mem_append.mp hr with hhead | htail
          · have hpres' : ∀ o ∈ σ.objs, o.Wf → True →
                ∃ o' ∈ σ'.objs, o'.addr = o.addr ∧ o'.rc = o.rc ∧ o'.childFields = o.childFields :=
              fun o ho hwo _ => let ⟨o', ho', hd, hrc⟩ := hpres o ho hwo;
                ⟨o', ho', hd.1, hrc, objDataEq_childFields hd⟩
            have hr' := (nonPersistReach_mono_pred hpres' (fun _ _ _ _ _ _ _ => trivial)
              hc.1.2.1 trivial hreach).1
            exact Or.inr ⟨r, List.mem_append.mpr (Or.inl hhead), hr'⟩
          · have hbe : Backed σ.objs (rf.extH ++ rf.ghostH) bv := Or.inr ⟨r, htail, hreach⟩
            exact backed_mono_roots
              (fun z hz => List.mem_append.mpr (Or.inr hz)) (hbackExt bv hbe)

theorem sharedPredInv_put_zero {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) {vx : RcVar} {x : Nat} (hxid : vx.id = x)
    (hfr : binderFreshOwned rf.ctx x = true) {pv : PVal} {w : Word}
    (hv0 : varHandles (rf.envH.set x vx.ty w) vx = []) :
    let rf' : RcFrame :=
      { ctx := rf.ctx.put vx, envP := rf.envP.set x pv, envH := rf.envH.set x vx.ty w
        extH := rf.extH, ghostH := rf.ghostH }
    ∀ p ∈ rf.ctx.sharedPreds, ∀ vb vx',
      rf'.ctx.get? p.1 = some vb → rf'.ctx.get? p.2 = some vx' →
      vb.isLive = true → vx'.noRc = false → vx'.persistent = false →
      (((rf'.envP p.1).bind PVal.tag? = some 0 →
        ∃ bv : BitVec 64, rf'.envH p.2 = some (vx'.ty, Word.i64 bv) ∧ (bv &&& 1#64) = 0#64 ∧
        (0 < vx'.owned → nonPersistRefs σ.objs bv +
          (localHandlesExcept rf'.ctx rf'.envH p.2 ++ rf'.extH ++ rf'.ghostH).count bv = 0 ∧
          ∃ o ∈ σ.objs, o.addr = bv ∧ o.rc.toNat = vx'.owned)) ∧
       ((rf'.envP p.1).bind PVal.tag? = some 1 → 0 < vx'.owned →
        ∃ bv : BitVec 64, rf'.envH p.2 = some (vx'.ty, Word.i64 bv) ∧ (bv &&& 1#64) = 0#64 ∧
          ∃ o ∈ σ.objs, o.addr = bv ∧ (o.rc = 0#32 ∨ vx'.owned < o.rc.toNat))) := by
  intro rf' p hp vb vx' hg1 hg2 hbl hno hps
  have hsh := hinv.2.2.2.2 p hp
  have hpreds : p.1 ≠ x ∧ p.2 ≠ x := by
    have ha := hfr
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true] at ha
    have hpx := ha.1.2 p hp
    simp only [bne_iff_ne] at hpx
    exact hpx
  have hg1' : rf.ctx.get? p.1 = some vb := by
    have he := RcCtx.put_get? hinv.2.1 vx p.1
    rw [hxid, beq_false_of_ne hpreds.1] at he; exact he.symm.trans hg1
  have hg2' : rf.ctx.get? p.2 = some vx' := by
    have he := RcCtx.put_get? hinv.2.1 vx p.2
    rw [hxid, beq_false_of_ne hpreds.2] at he; exact he.symm.trans hg2
  have hep : rf'.envP p.1 = rf.envP p.1 := by simp [rf', PValEnv.set, hpreds.1]
  have heh : rf'.envH p.2 = rf.envH p.2 := by simp [rf', HValEnv.set, hpreds.2]
  have hotherH : ∀ y, y ≠ x → rf'.envH y = rf.envH y := fun y hy => by
    simp [rf', HValEnv.set, hy]
  have hcnt : ∀ bv, (localHandlesExcept rf'.ctx rf'.envH p.2 ++ rf'.extH ++ rf'.ghostH).count bv =
      (localHandlesExcept rf.ctx rf.envH p.2 ++ rf.extH ++ rf.ghostH).count bv := by
    intro bv
    obtain ⟨hm, hid⟩ := RcCtx.get?_mem hg2'
    have hc := localHandlesExcept_put_zero_count hinv.2.1 (hxid.symm ▸ hfr)
      (hxid.symm ▸ hotherH) hv0 (hxid.symm ▸ hpreds.2) hm hid bv
    simp only [List.count_append, rf'] at hc ⊢; omega
  obtain ⟨h0, h1⟩ := hsh vb vx' hg1' hg2' hbl hno hps
  constructor
  · intro hp0
    obtain ⟨bv, hev, hb0, hpos⟩ := h0 (hep ▸ hp0)
    refine ⟨bv, heh.trans hev, hb0, fun hown => ?_⟩
    obtain ⟨hz, hobj⟩ := hpos hown
    rw [hcnt bv]
    exact ⟨hz, hobj⟩
  · intro hp1 hown
    obtain ⟨bv, hev, hb0, hobj⟩ := h1 (hep ▸ hp1) hown
    exact ⟨bv, heh.trans hev, hb0, hobj⟩

end
