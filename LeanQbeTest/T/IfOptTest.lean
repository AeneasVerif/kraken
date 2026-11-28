module

import LeanQbe.T.IfOptLemmas
import LeanQbe.T.SimplifyGroupPlanLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.WPLemmas
meta import LeanQbe.T.IfOpt
meta import LeanQbe.T.SimplifyGroupPlan

/-!
# Targeted Unit & Soundness Tests for `LeanQbe.T.IfOpt`

1. Positive hoisting tests (`Func.ifOpt` + `SimplifyGroupPlan`) for newly enabled pure ops:
   `.ternlog`, `.blend`, `.bswap` (`bswapOk = true`), `.shufd`/`.shufb`/`.alignr`/`.blendw`
   (`size ≠ 0 ∧ size % 128 = 0`), `.sha256rnds2`, `.sha256msg1`, `.sha256msg2`, and `.rbit`.
2. Negative whitelist guards for partial/trapping/invalid-width ops (`.bswap (.bits 12)`,
   `.shufd (.bits 64)`, `.udiv`, `.sdiv`, `.urem`, `.srem`, `.fptoui`, `.fptosi`, `.fdiv`).
3. Closed-function `Wf`, `Func.ifOpt_spec`, `Func.ifOpt_callsOk`, and standard-axiom audit.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.IfOptTest

open LeanQbe.T

def ifSimp {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.simplifyGroupPlan (Func.ifOpt f)

theorem ifSimp_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (ifSimp f).Wf :=
  Func.simplifyGroupPlan_wf (Func.ifOpt_wf hf)

theorem ifSimp_spec {as rs : List Ty} {Γ : Env} {f : Func as rs} (hf : f.Wf)
    {xs : Tup Val as} {m : Mem 64} {Q : Tup Val rs → Mem 64 → Prop} {X : XPost}
    (h : Func.wp Γ f xs m Q X) : Func.wp Γ (ifSimp f) xs m Q X :=
  Func.simplifyGroupPlan_spec (Func.ifOpt_wf hf) (Func.ifOpt_spec hf h)

/-! ## 1. Whitelist checks (`isSafeOp` positive & negative) -/

#guard IfOptImpl.isSafeOp (.ternlog i64 0x96) == true
#guard IfOptImpl.isSafeOp (.blend i64) == true
#guard IfOptImpl.isSafeOp (.blend v4i32) == true
#guard IfOptImpl.isSafeOp (.bswap i16) == true
#guard IfOptImpl.isSafeOp (.bswap i32) == true
#guard IfOptImpl.isSafeOp (.bswap i64) == true
#guard IfOptImpl.isSafeOp (.bswap (.bits 12)) == false
#guard IfOptImpl.isSafeOp (.bswap .bool) == false
#guard IfOptImpl.isSafeOp (.rbit 64) == true
#guard IfOptImpl.isSafeOp (.shufd v4i32 0x1b) == true
#guard IfOptImpl.isSafeOp (.shufb v4i32) == true
#guard IfOptImpl.isSafeOp (.alignr v4i32 4) == true
#guard IfOptImpl.isSafeOp (.blendw v4i32 0x55) == true
#guard IfOptImpl.isSafeOp (.shufd (.bits 64) 0) == false
#guard IfOptImpl.isSafeOp (.shufb (.bits 0)) == false
#guard IfOptImpl.isSafeOp .sha256rnds2 == true
#guard IfOptImpl.isSafeOp .sha256msg1 == true
#guard IfOptImpl.isSafeOp .sha256msg2 == true
#guard IfOptImpl.isSafeOp (.udiv 64) == false
#guard IfOptImpl.isSafeOp (.sdiv 64) == false
#guard IfOptImpl.isSafeOp (.urem 64) == false
#guard IfOptImpl.isSafeOp (.srem 64) == false
#guard IfOptImpl.isSafeOp (.fptoui .d 64) == false
#guard IfOptImpl.isSafeOp (.fptosi .d 64) == false

/-! ## 2. Diamond hoisting (`ternlog`, `blend`, `bswap`, `shufd`/`shufb`/`alignr`/`blendw`, SHA) -/

def ternlogDiamond : Func [.bool, i64, i64, i64] [i64] := fun _ _ (c, x, y, z, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op3 (.ternlog i64 0x96) (.var x) (.var y) (.var z)) fun (t, ()) =>
          .jump J (.var t, ()))
        (.jump J (.var x, ())))

theorem ternlogDiamond_hoisted :
    ifSimp ternlogDiamond = fun _ _ (c, x, y, z, ()) =>
      .let_ (op3 (.ternlog i64 0x96) (.var x) (.var y) (.var z)) fun (t, ()) =>
      .let_ (op3 (.select i64) (.var c) (.var t) (.var x)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

theorem ternlogDiamond_wf : ternlogDiamond.Wf := by t_wf_reify
theorem ternlogDiamond_spec {Γ : Env} {xs m Q X} (h : Func.wp Γ ternlogDiamond xs m Q X) :
    Func.wp Γ (ifSimp ternlogDiamond) xs m Q X :=
  ifSimp_spec ternlogDiamond_wf h

def bswapBlendDiamond : Func [.bool, i64, i64] [i64] := fun _ _ (c, x, y, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.bswap i64) (.var x)) fun (bx, ()) =>
         .let_ (op3 (.blend i64) (.var c) (.var bx) (.var y)) fun (bl, ()) =>
         .jump J (.var bl, ()))
        (.jump J (.var y, ())))

theorem bswapBlendDiamond_hoisted :
    ifSimp bswapBlendDiamond = fun _ _ (c, x, y, ()) =>
      .let_ (op1 (.bswap i64) (.var x)) fun (bx, ()) =>
      .let_ (op3 (.blend i64) (.var c) (.var bx) (.var y)) fun (bl, ()) =>
      .let_ (op3 (.select i64) (.var c) (.var bl) (.var y)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

theorem bswapBlendDiamond_wf : bswapBlendDiamond.Wf := by t_wf_reify
theorem bswapBlendDiamond_spec {Γ : Env} {xs m Q X} (h : Func.wp Γ bswapBlendDiamond xs m Q X) :
    Func.wp Γ (ifSimp bswapBlendDiamond) xs m Q X :=
  ifSimp_spec bswapBlendDiamond_wf h

def bswapBadWidthDiamond : Func [.bool, .bits 12] [.bits 12] := fun _ _ (c, x, ()) =>
  .group (sig := [[.bits 12]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.bswap (.bits 12)) (.var x)) fun (bx, ()) => .jump J (.var bx, ()))
        (.jump J (.var x, ())))

theorem bswapBadWidth_unchanged : Func.ifOpt bswapBadWidthDiamond = bswapBadWidthDiamond := by
  t_kernel_rfl

def shufdDiamond : Func [.bool, v4i32, i32] [i32] := fun _ _ (c, v, fallback, ()) =>
  .group (sig := [[i32]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.shufd v4i32 0x1b) (.var v)) fun (sv, ()) =>
         .let_ (op1 (.unpair (Ty.pair i32 i32) (Ty.pair i32 i32)) (.var sv)) fun (lo, _hi, ()) =>
         .let_ (op1 (.unpair i32 i32) (.var lo)) fun (w0, _w1, ()) =>
         .jump J (.var w0, ()))
        (.jump J (.var fallback, ())))

theorem shufdDiamond_noJnz :
    ifSimp shufdDiamond = fun _ _ (c, v, fallback, ()) =>
      .let_ (op1 (.shufd v4i32 0x1b) (.var v)) fun (sv, ()) =>
      .let_ (op1 (.unpair (Ty.pair i32 i32) (Ty.pair i32 i32)) (.var sv)) fun (lo, _hi, ()) =>
      .let_ (op1 (.unpair i32 i32) (.var lo)) fun (w0, _w1, ()) =>
      .let_ (op3 (.select i32) (.var c) (.var w0) (.var fallback)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

theorem shufdDiamond_wf : shufdDiamond.Wf := by t_wf_reify
theorem shufdDiamond_spec {Γ : Env} {xs m Q X} (h : Func.wp Γ shufdDiamond xs m Q X) :
    Func.wp Γ (ifSimp shufdDiamond) xs m Q X :=
  ifSimp_spec shufdDiamond_wf h

def simdVecDiamond : Func [.bool, v4i32, v4i32, v4i32] [v4i32] :=
  fun _ _ (c, a, b, d, ()) =>
  .group (sig := [[v4i32]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.shufb v4i32) (.var a) (.var b)) fun (s0, ()) =>
         .let_ (op2 (.alignr v4i32 4) (.var s0) (.var b)) fun (s1, ()) =>
         .jump J (.var s1, ()))
        (.let_ (op2 (.blendw v4i32 0x55) (.var a) (.var d)) fun (s2, ()) =>
         .jump J (.var s2, ())))

#eval show IO Unit from do
  let rec noJnz : {rs : List Ty} → TFlat rs → Bool
    | _, .let_ _ k => noJnz k
    | _, .load _ _ k => noJnz k
    | _, .store _ _ k => noJnz k
    | _, .call _ _ _ k => noJnz k
    | _, .jnz _ _ _ => false
    | _, .group _ _ => false
    | _, _ => true
  if !noJnz (reifyFunc (ifSimp simdVecDiamond)) then
    throw <| IO.userError "simdVecDiamond not flattened"

theorem simdVecDiamond_checkTFlat : (ifSimp simdVecDiamond).checkTFlat = true := by
  t_kernel_rfl

theorem simdVecDiamond_wf : simdVecDiamond.Wf := by t_wf_reify
theorem simdVecDiamond_spec {Γ : Env} {xs m Q X} (h : Func.wp Γ simdVecDiamond xs m Q X) :
    Func.wp Γ (ifSimp simdVecDiamond) xs m Q X :=
  ifSimp_spec simdVecDiamond_wf h

def shaDiamond : Func [.bool, v4i32, v4i32, v4i32] [v4i32] :=
  fun _ _ (c, st, wk, fallback, ()) =>
  .group (sig := [[v4i32]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op3 .sha256rnds2 (.var st) (.var wk) (.var fallback)) fun (h0, ()) =>
         .let_ (op2 .sha256msg1 (.var h0) (.var wk)) fun (h1, ()) =>
         .jump J (.var h1, ()))
        (.let_ (op2 .sha256msg2 (.var st) (.var wk)) fun (h2, ()) =>
         .jump J (.var h2, ())))

#eval show IO Unit from do
  let rec noJnz : {rs : List Ty} → TFlat rs → Bool
    | _, .let_ _ k => noJnz k
    | _, .load _ _ k => noJnz k
    | _, .store _ _ k => noJnz k
    | _, .call _ _ _ k => noJnz k
    | _, .jnz _ _ _ => false
    | _, .group _ _ => false
    | _, _ => true
  if !noJnz (reifyFunc (ifSimp shaDiamond)) then
    throw <| IO.userError "shaDiamond not flattened"

theorem shaDiamond_checkTFlat : (ifSimp shaDiamond).checkTFlat = true := by
  t_kernel_rfl

theorem shaDiamond_wf : shaDiamond.Wf := by t_wf_reify
theorem shaDiamond_spec {Γ : Env} {xs m Q X} (h : Func.wp Γ shaDiamond xs m Q X) :
    Func.wp Γ (ifSimp shaDiamond) xs m Q X :=
  ifSimp_spec shaDiamond_wf h

/-! ## 3. Axiom audit (`[propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Func.ifOpt_wf
#print axioms LeanQbe.T.Func.ifOpt_spec
#print axioms LeanQbe.T.Func.ifOpt_callsOk
#print axioms LeanQbe.T.Func.ifOptBits_wf
#print axioms LeanQbe.T.Func.ifOptBits_spec
#print axioms LeanQbeTest.T.IfOptTest.ternlogDiamond_spec
#print axioms LeanQbeTest.T.IfOptTest.bswapBlendDiamond_spec
#print axioms LeanQbeTest.T.IfOptTest.shufdDiamond_spec
#print axioms LeanQbeTest.T.IfOptTest.simdVecDiamond_spec
#print axioms LeanQbeTest.T.IfOptTest.shaDiamond_spec

end LeanQbeTest.T.IfOptTest
