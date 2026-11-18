module

public import LeanQbe.T.PrintCpp
public import LeanQbe.T.Examples.UnionFind
public import LeanQbe.T.Legal
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.Examples.UnionFind
meta import LeanQbe.T.Legal

set_option autoImplicit false

namespace LeanQbeTest.T.PrintCppTest

open LeanQbe.T
open LeanQbe.T.PrintCpp

private def let1 {V : Ty → Type} {L : List Ty → Type} {rs sig : List Ty} {r : Ty}
    (c : OpCode sig [r]) (args : Tup (Arg V) sig) (k : V r → Expr V L rs) : Expr V L rs :=
  .let_ { code := c, args := args } (fun (v, _) => k v)

private def let2 {V : Ty → Type} {L : List Ty → Type} {rs sig : List Ty} {r1 r2 : Ty}
    (c : OpCode sig [r1, r2]) (args : Tup (Arg V) sig) (k : V r1 → V r2 → Expr V L rs) : Expr V L rs :=
  .let_ { code := c, args := args } (fun (v1, v2, _) => k v1 v2)

-- ============================================================================
-- Pure Lean unit checks for PrintCpp naming, escaping, and determinism
-- ============================================================================

#guard baseMangle "union" == "fn_union"
#guard baseMangle "class" == "fn_class"
#guard baseMangle "main" == "fn_main"
#guard baseMangle "mem" == "fn_mem"
#guard baseMangle "std" == "fn_std"
#guard baseMangle "EOF" == "fn_EOF"
#guard baseMangle "v0" == "fn_v0"
#guard baseMangle "p12" == "fn_p12"
#guard baseMangle "b3_p0" == "fn_b3_p0"
#guard baseMangle "L_7" == "fn_L_7"
#guard baseMangle "_priv" == "fn__priv"
#guard baseMangle "123abc" == "fn_123abc"
#guard baseMangle "" == "fn_empty"
#guard baseMangle "foo.bar" == "foo_bar"
#guard escapeCString "a\"b\\c\nd\te\x01" == "a\\\"b\\\\c\\nd\\te\\001"
#guard escapeCString "ext\x01abc\x017" == "ext\\001abc\\0017"
#guard escapeCString "café€" == "caf\\303\\251\\342\\202\\254"

#guard
  let blks : Array Block :=
    #[ { id := 0, label := "L_0", body := "", outJumps := #[1, 2, 3, 4] }
     , { id := 1, label := "L_1", body := "", outJumps := #[] }
     , { id := 2, label := "L_2", body := "", outJumps := #[1] }
     , { id := 3, label := "L_3", body := "", outJumps := #[1, 2] }
     , { id := 4, label := "L_4", body := "", outJumps := #[1, 2, 3] }
     , { id := 5, label := "L_5", body := "", outJumps := #[] }
     ]
  let live := reachableBlockIds blks #[0, 5, 0]
  [0, 1, 2, 3, 4, 5].all fun i => live.contains i

private def mkTrivialFn (name : Sym) : Fn where
  name := name
  as := []
  rs := [i64]
  body := fun _ _ _ => .ret (.imm 0#64, PUnit.unit)

#guard (ppModule [mkTrivialFn "dup", mkTrivialFn "dup"]).isOk == false

#guard match buildSymMap [mkTrivialFn "foo.bar", mkTrivialFn "foo_bar", mkTrivialFn "foo_bar_2"] with
  | .ok m => m "foo.bar" == "foo_bar" && m "foo_bar" == "foo_bar_2" && m "foo_bar_2" == "foo_bar_2_2"
  | .error _ => false

-- ============================================================================
-- Core / Legalizable Edge-Case Module (passes pre-Legal and post-Legal)
-- ============================================================================

/-- Test `bool` comparisons (`slt true false = true`) and arithmetic/shifts on `bool`. -/
def fnBoolEdge : Fn where
  name := "bool_edge"
  as := [.bool, .bool]
  rs := [.bool, .bool, .bool, .bool, .bool, .bool]
  body := fun _ _ (a, b, _) =>
    let1 (.cmp .slt .bool) (.var a, .var b, PUnit.unit) fun slt =>
    let1 (.cmp .sle .bool) (.var a, .var b, PUnit.unit) fun sle =>
    let1 (.cmp .sgt .bool) (.var a, .var b, PUnit.unit) fun sgt =>
    let1 (.cmp .ult .bool) (.var a, .var b, PUnit.unit) fun ult =>
    let1 (.add .bool) (.var a, .var b, PUnit.unit) fun xorAdd =>
    let1 (.shl .bool) (.var a, .var b, PUnit.unit) fun shlKeep =>
      .ret (.var slt, .var sle, .var sgt, .var ult, .var xorAdd, .var shlKeep, PUnit.unit)

/-- Test `sdiv0` including `(INT64_MIN, -1)` and `(x, 0)`, plus `udiv0` and UB `sdiv`/`udiv`/`srem`. -/
def fnDivEdge : Fn where
  name := "div_edge"
  as := [i64, i64, Ty.bits 4]
  rs := [i64, i64, Ty.bits 4, i64]
  body := fun _ _ (a, b, mode, _) =>
    .jnz (.imm true) -- keep mode dispatch simple via cmp
      (let1 (.cmp .eq (Ty.bits 4)) (.var mode, .imm 0#4, PUnit.unit) fun isSafe =>
       .jnz (.var isSafe)
         (let1 (.sdiv0 64) (.var a, .var b, PUnit.unit) fun sd0 =>
          let1 (.udiv0 64) (.var a, .var b, PUnit.unit) fun ud0 =>
          let1 (.sdiv0 4) (.imm 8#4, .imm 15#4, PUnit.unit) fun sdiv4MinNeg1 =>
          let1 (.srem 64) (.imm 0xFFFFFFFFFFFFFFF9#64, .imm 3#64, PUnit.unit) fun sr =>
            .ret (.var sd0, .var ud0, .var sdiv4MinNeg1, .var sr, PUnit.unit))
         (let1 (.cmp .eq (Ty.bits 4)) (.var mode, .imm 1#4, PUnit.unit) fun isSdivUb =>
          .jnz (.var isSdivUb)
            (let1 (.sdiv 64) (.var a, .var b, PUnit.unit) fun r => .ret (.var r, .imm 0#64, .imm 0#4, .imm 0#64, PUnit.unit))
            (let1 (.cmp .eq (Ty.bits 4)) (.var mode, .imm 2#4, PUnit.unit) fun isSremUb =>
             .jnz (.var isSremUb)
               (let1 (.srem 64) (.var a, .var b, PUnit.unit) fun r => .ret (.var r, .imm 0#64, .imm 0#4, .imm 0#64, PUnit.unit))
               (let1 (.udiv 64) (.var a, .var b, PUnit.unit) fun r => .ret (.var r, .imm 0#64, .imm 0#4, .imm 0#64, PUnit.unit)))))
      .hlt

/-- Test shifts with `s = 0`, `s = width`, `s > width`, negative `ashr`, `rotl`, `rotr`, `fshl`, `fshr`. -/
def fnShiftEdge : Fn where
  name := "shift_edge"
  as := [i64, i64]
  rs := [i64, i64, i64, i64, i64, i64, i64]
  body := fun _ _ (x, s, _) =>
    let1 (.shl i64) (.var x, .var s, PUnit.unit) fun v1 =>
    let1 (.lshr i64) (.var x, .var s, PUnit.unit) fun v2 =>
    let1 (.ashr i64) (.var x, .var s, PUnit.unit) fun v3 =>
    let1 (.rotl i64) (.var x, .var s, PUnit.unit) fun v4 =>
    let1 (.rotr i64) (.var x, .var s, PUnit.unit) fun v5 =>
    let1 (.fshl 64) (.var x, .imm 0x0123456789ABCDEF#64, .var s, PUnit.unit) fun v6 =>
    let1 (.fshr 64) (.imm 0xFEDCBA9876543210#64, .var x, .var s, PUnit.unit) fun v7 =>
      .ret (.var v1, .var v2, .var v3, .var v4, .var v5, .var v6, .var v7, PUnit.unit)

/-- Test packed `Ty.pair` store/load (`pair .bool i8`, `pair .bool .bool`, lane-wise `add`/`cmp`/`bswap`). -/
def fnPairEdge : Fn where
  name := "pair_edge"
  as := [i64, i64]
  rs := [.pair .bool i8, .pair .bool .bool, .pair i8 i8, .pair .bool .bool, .pair i16 i16]
  body := fun _ _ (addr1, addr2, _) =>
    .store (t := .pair .bool i8) (.imm (true, 0xAA#8)) (.var addr1) <|
    .store (t := .pair .bool .bool) (.imm (true, false)) (.var addr2) <|
    .load (.pair .bool i8) (.var addr1) fun loaded1 =>
    .load (.pair .bool .bool) (.var addr2) fun loaded2 =>
    let1 (.add (.pair i8 i8)) (.imm (0xFF#8, 0#8), .imm (1#8, 0#8), PUnit.unit) fun pAdd =>
    let1 (.cmp .slt (.pair i8 i8)) (.imm (0xFF#8, 1#8), .imm (0#8, 2#8), PUnit.unit) fun pCmp =>
    let1 (.bswap (.pair i16 i16)) (.imm (0x1234#16, 0x5678#16), PUnit.unit) fun pSwap =>
      .ret (.var loaded1, .var loaded2, .var pAdd, .var pCmp, .var pSwap, PUnit.unit)

/-- Test `jnz c k .hlt`: returns `x + 42` if `c`, else `.hlt` (traps by default, throws if `-DTQBE_CATCH_UB`). -/
def fnJnzHlt : Fn where
  name := "jnz_hlt"
  as := [.bool, i64]
  rs := [i64]
  body := fun _ _ (c, x, _) =>
    .jnz (.var c)
      (let1 (.add i64) (.var x, .imm 42#64, PUnit.unit) fun res => .ret (.var res, PUnit.unit))
      .hlt

/-- Test `load .bool` UB if byte > 1 and unmapped store UB. -/
def fnMemUbEdge : Fn where
  name := "mem_ub_edge"
  as := [.bool, i64]
  rs := [.bool]
  body := fun _ _ (doLoad, addr, _) =>
    .jnz (.var doLoad)
      (.load .bool (.var addr) fun b => .ret (.var b, PUnit.unit))
      (.store (t := i64) (.imm 99#64) (.var addr) <| .ret (.imm false, PUnit.unit))

/-- Test carry/borrow/widening mul (`addc`, `subb`, `umulw`, `smulw`) and bit-count ops. -/
def fnWideBitOps : Fn where
  name := "wide_bit_ops"
  as := [i64, i64, .bool]
  rs := [i64, .bool, i64, .bool, i64, i64, i64, i64, i64, i64, i64, i64]
  body := fun _ _ (a, b, c, _) =>
    let2 (.addc 64) (.var a, .var b, .var c, PUnit.unit) fun addS addC =>
    let2 (.subb 64) (.var a, .var b, .var c, PUnit.unit) fun subD subB =>
    let2 (.umulw 64) (.var a, .var b, PUnit.unit) fun uLo uHi =>
    let2 (.smulw 64) (.var a, .var b, PUnit.unit) fun sLo sHi =>
    let1 (.clz 64) (.var a, PUnit.unit) fun clzV =>
    let1 (.ctz 64) (.var a, PUnit.unit) fun ctzV =>
    let1 (.cls 64) (.var a, PUnit.unit) fun clsV =>
    let1 (.popcnt 64) (.var a, PUnit.unit) fun popV =>
      .ret (.var addS, .var addC, .var subD, .var subB,
            .var uLo, .var uHi, .var sLo, .var sHi,
            .var clzV, .var ctzV, .var clsV, .var popV, PUnit.unit)

/-- Test parallel block-parameter swap loop `loop (a, b) -> (b, a+b)` (Fibonacci) and dead block suppression. -/
def fnParallelSwapAndDead : Fn where
  name := "fib_swap"
  as := [i64]
  rs := [i64]
  body := fun _ _ (n, _) =>
    let1 (.copy i64) (.imm 123#64, PUnit.unit) fun _unused =>
    .group (sig := [[i64, i64, i64], [i64]])
      (fun (lblLoop, lblDead, _) =>
        .cons (fun (k, a, b, _) =>
          let1 (.cmp .eq i64) (.var k, .imm 0#64, PUnit.unit) fun done =>
          .jnz (.var done)
            (.ret (.var a, PUnit.unit))
            (let1 (.sub i64) (.var k, .imm 1#64, PUnit.unit) fun k1 =>
             let1 (.add i64) (.var a, .var b, PUnit.unit) fun ab =>
               .jump (ts := [i64, i64, i64]) lblLoop (.var k1, .var b, .var ab, PUnit.unit)))
        (.cons (fun (x, _) => .jump (ts := [i64]) lblDead (.var x, PUnit.unit))
         .nil))
      (fun (lblLoop, _, _) =>
        .jump (ts := [i64, i64, i64]) lblLoop (.var n, .imm 0#64, .imm 1#64, PUnit.unit))

/-- Test infinite loop (`spin`) for `-Wreturn-type` cleanliness under `-Werror`. -/
def fnSpin : Fn where
  name := "spin_loop"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, _) =>
    loop1 (ts := [i64]) (fun lbl (v, _) => .jump (ts := [i64]) lbl (.var v, PUnit.unit))
      (fun lbl => .jump (ts := [i64]) lbl (.var x, PUnit.unit))

/-- Mutually recursive `even` / `odd` plus keyword/shadowing/dot-collision calls and 0-ret callee. -/
def fnEven : Fn where
  name := "even"
  as := [i64]
  rs := [.bool]
  body := fun _ _ (n, _) =>
    let1 (.cmp .eq i64) (.var n, .imm 0#64, PUnit.unit) fun z =>
    .jnz (.var z)
      (.ret (.imm true, PUnit.unit))
      (let1 (.sub i64) (.var n, .imm 1#64, PUnit.unit) fun n1 =>
        .call "odd" (as := [i64]) (bs := [.bool]) (.var n1, PUnit.unit) fun (r, _) =>
          .ret (.var r, PUnit.unit))

/-- Second half of mutual recursion test (`odd` calling `even`). -/
def fnOdd : Fn where
  name := "odd"
  as := [i64]
  rs := [.bool]
  body := fun _ _ (n, _) =>
    let1 (.cmp .eq i64) (.var n, .imm 0#64, PUnit.unit) fun z =>
    .jnz (.var z)
      (.ret (.imm false, PUnit.unit))
      (let1 (.sub i64) (.var n, .imm 1#64, PUnit.unit) fun n1 =>
        .call "even" (as := [i64]) (bs := [.bool]) (.var n1, PUnit.unit) fun (r, _) =>
          .ret (.var r, PUnit.unit))

/-- Function named after C++ keyword `union`, mangled to `fn_union`. -/
def fnKeywordUnion : Fn where
  name := "union"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, _) =>
    let1 (.add i64) (.var x, .imm 7#64, PUnit.unit) fun r => .ret (.var r, PUnit.unit)

/-- Symbol colliding under `.` → `_` mangling (`foo.bar`). -/
def fnCollisionA : Fn where
  name := "foo.bar"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, _) =>
    let1 (.add i64) (.var x, .imm 100#64, PUnit.unit) fun r => .ret (.var r, PUnit.unit)

/-- Second symbol colliding with `foo.bar` (`foo_bar`), disambiguated by `buildSymMap`. -/
def fnCollisionB : Fn where
  name := "foo_bar"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, _) =>
    let1 (.add i64) (.var x, .imm 200#64, PUnit.unit) fun r => .ret (.var r, PUnit.unit)

/-- Symbol matching local temporary pattern `v0`, mangled to `fn_v0`. -/
def fnLocalV0 : Fn where
  name := "v0"
  as := [i64]
  rs := [i64]
  body := fun _ _ (x, _) =>
    let1 (.add i64) (.var x, .imm 300#64, PUnit.unit) fun y =>
    let1 (.add i64) (.var y, .imm 1#64, PUnit.unit) fun z => .ret (.var z, PUnit.unit)

/-- Zero-return callee verifying `(void)callee(...)` and empty `return {};`. -/
def fnZeroRet : Fn where
  name := "noop_ret"
  as := [i64]
  rs := []
  body := fun _ _ (a, _) =>
    .store (t := i64) (.imm 0xCAFE#64) (.var a) (.ret PUnit.unit)

/-- Caller exercising mutual recursion, keyword/local-pattern mangling, and 0-return calls. -/
def fnCallKeywords : Fn where
  name := "call_keywords"
  as := [i64, i64]
  rs := [.bool, i64]
  body := fun _ _ (n, addr, _) =>
    .call "even" (as := [i64]) (bs := [.bool]) (.var n, PUnit.unit) fun (ev, _) =>
    .call "noop_ret" (as := [i64]) (bs := []) (.var addr, PUnit.unit) fun _ =>
    .call "union" (as := [i64]) (bs := [i64]) (.var n, PUnit.unit) fun (u, _) =>
    .call "foo.bar" (as := [i64]) (bs := [i64]) (.var u, PUnit.unit) fun (a, _) =>
    .call "foo_bar" (as := [i64]) (bs := [i64]) (.var a, PUnit.unit) fun (b, _) =>
    .call "v0" (as := [i64]) (bs := [i64]) (.var b, PUnit.unit) fun (c, _) =>
      .ret (.var ev, .var c, PUnit.unit)

/-- Test float32/float64 operations (`fadd`, `ffma`, `fsqrt`, `fcmp`, `fcvt`, `fptoui`, `fptosi`, `uitofp`, `sitofp`). -/
def fnFloatStd : Fn where
  name := "float_std"
  as := [Ty.float .s, Ty.float .d, Ty.float .d, Ty.float .d]
  rs := [Ty.float .d, Ty.float .d, .bool, .bool, i64, i64]
  body := fun _ _ (s0, d0, d1, d2, _) =>
    let1 (.fcvt .s .d) (.var s0, PUnit.unit) fun dFromS =>
    let1 (.ffma (Ty.float .d)) (.var dFromS, .var d0, .var d1, PUnit.unit) fun fmaV =>
    let1 (.fsqrt (Ty.float .d)) (.var d2, PUnit.unit) fun sqrtV =>
    let1 (.fcmp .ne (Ty.float .d)) (.var d0, .var d1, PUnit.unit) fun cmpNe =>
    let1 (.fcmp .eq (Ty.float .d)) (.var d0, .var d1, PUnit.unit) fun cmpEq =>
    let1 (.fptoui .d 64) (.var d0, PUnit.unit) fun u64 =>
    let1 (.fptosi .d 64) (.var d1, PUnit.unit) fun s64 =>
      .ret (.var fmaV, .var sqrtV, .var cmpNe, .var cmpEq, .var u64, .var s64, PUnit.unit)

/-- Test SIMD shuffles & SHA256 (`shufd`, `shufb`, `alignr`, `blendw`, `sha256rnds2`, `sha256msg1`, `sha256msg2`). -/
def fnSimdSha : Fn where
  name := "simd_sha"
  as := [v4i32, v4i32, v4i32]
  rs := [v4i32, v4i32, v4i32, v4i32, v4i32, v4i32, v4i32]
  body := fun _ _ (a, b, c, _) =>
    let1 (.shufd v4i32 0x1B#8) (.var a, PUnit.unit) fun rShufd =>
    let1 (.shufb v4i32) (.var a, .var b, PUnit.unit) fun rShufb =>
    let1 (.alignr v4i32 4#8) (.var a, .var b, PUnit.unit) fun rAlign =>
    let1 (.blendw v4i32 0xAA#8) (.var a, .var b, PUnit.unit) fun rBlendw =>
    let1 .sha256rnds2 (.var a, .var b, .var c, PUnit.unit) fun rRnds2 =>
    let1 .sha256msg1 (.var a, .var b, PUnit.unit) fun rMsg1 =>
    let1 .sha256msg2 (.var a, .var b, PUnit.unit) fun rMsg2 =>
      .ret (.var rShufd, .var rShufb, .var rAlign, .var rBlendw,
            .var rRnds2, .var rMsg1, .var rMsg2, PUnit.unit)

/-- Core edge-case function suite tested both pre-`Legal` and post-`Legal`. -/
def coreEdgeFns : List Fn :=
  [ fnBoolEdge
  , fnDivEdge
  , fnShiftEdge
  , fnPairEdge
  , fnJnzHlt
  , fnMemUbEdge
  , fnWideBitOps
  , fnParallelSwapAndDead
  , fnSpin
  , fnEven
  , fnOdd
  , fnKeywordUnion
  , fnCollisionA
  , fnCollisionB
  , fnLocalV0
  , fnZeroRet
  , fnCallKeywords
  , fnFloatStd
  , fnSimdSha
  ]

-- ============================================================================
-- Extended Pre-Legal Module (bits 0, bits 128, float h/q, f128 exit, dynamic UB)
-- ============================================================================

/-- Test 0-bit and 128-bit edge cases (`clz 128`, `cls 128`, `sdiv0`, `shl` mod 128, `udiv 0`). -/
def fnBits0And128 : Fn where
  name := "bits0_128"
  as := [Ty.bits 0, Ty.bits 128, Ty.bits 128, .bool]
  rs := [Ty.bits 0, Ty.bits 128, Ty.bits 128, Ty.bits 128, Ty.bits 128, Ty.bits 128]
  body := fun _ _ (b0, x, y, doDiv0Ub, _) =>
    let1 (.add (Ty.bits 0)) (.var b0, .var b0, PUnit.unit) fun z0 =>
    let1 (.clz 128) (.var x, PUnit.unit) fun clzV =>
    let1 (.cls 128) (.var x, PUnit.unit) fun clsV =>
    let1 (.sdiv0 128) (.var x, .var y, PUnit.unit) fun sd0 =>
    let1 (.shl (Ty.bits 128)) (.var x, .var y, PUnit.unit) fun sh =>
    .jnz (.var doDiv0Ub)
      (let1 (.udiv 0) (.var z0, .var z0, PUnit.unit) fun _ =>
        .ret (.var z0, .var clzV, .var clsV, .var sd0, .var sh, .var y, PUnit.unit))
      (let1 (.udiv 128) (.var x, .var y, PUnit.unit) fun ud =>
        .ret (.var z0, .var clzV, .var clsV, .var sd0, .var sh, .var ud, PUnit.unit))

/-- Test binary16 (`Fmt.h`) and binary128 (`Fmt.q`) FMA/sqrt/conversions without `-lquadmath`. -/
def fnFloatHalfQuad : Fn where
  name := "float_hq"
  as := [Ty.float .h, Ty.float .h, Ty.float .q, Ty.float .q, Ty.float .q]
  rs := [Ty.float .h, Ty.float .q, Ty.float .q, Ty.bits 128]
  body := fun _ _ (h0, h1, q0, q1, q2, _) =>
    let1 (.fadd (Ty.float .h)) (.var h0, .var h1, PUnit.unit) fun hSum =>
    let1 (.fcvt .h .q) (.var hSum, PUnit.unit) fun qFromH =>
    let1 (.ffma (Ty.float .q)) (.var q0, .var q1, .var q2, PUnit.unit) fun qFma =>
    let1 (.fsqrt (Ty.float .q)) (.var qFromH, PUnit.unit) fun qSqrt =>
    let1 (.fptoui .q 128) (.var q2, PUnit.unit) fun u128 =>
      .ret (.var hSum, .var qFma, .var qSqrt, .var u128, PUnit.unit)

/-- Test dynamic UB op paths (invalid `zext`, non-bit int ops, invalid float/bswap/shufd) guarded behind branches. -/
def fnDeadDynamicUb : Fn where
  name := "dead_dynamic_ub"
  as := [Ty.bits 8]
  rs := [i64]
  body := fun _ _ (which, _) =>
    let1 (.cmp .eq (Ty.bits 8)) (.var which, .imm 0#8, PUnit.unit) fun m0 =>
    .jnz (.var m0)
      (.ret (.imm 777#64, PUnit.unit))
      (let1 (.cmp .eq (Ty.bits 8)) (.var which, .imm 1#8, PUnit.unit) fun m1 =>
       .jnz (.var m1)
         (let1 (.zext 64 32) (.imm 1#64, PUnit.unit) fun v =>
          let1 (.zext 32 64) (.var v, PUnit.unit) fun r => .ret (.var r, PUnit.unit))
         (let1 (.cmp .eq (Ty.bits 8)) (.var which, .imm 2#8, PUnit.unit) fun m2 =>
          .jnz (.var m2)
            (let1 (.add (Ty.float .d)) (.imm 0#64, .imm 0#64, PUnit.unit) fun _ => .ret (.imm 0#64, PUnit.unit))
            (let1 (.cmp .eq (Ty.bits 8)) (.var which, .imm 3#8, PUnit.unit) fun m3 =>
             .jnz (.var m3)
               (let1 (.fadd i64) (.imm 1#64, .imm 2#64, PUnit.unit) fun r => .ret (.var r, PUnit.unit))
               (let1 (.cmp .eq (Ty.bits 8)) (.var which, .imm 4#8, PUnit.unit) fun m4 =>
                .jnz (.var m4)
                  (let1 (.bswap (.pair (Ty.bits 4) (Ty.bits 4))) (.imm (1#4, 2#4), PUnit.unit) fun _ =>
                    .ret (.imm 0#64, PUnit.unit))
                  (let1 (.shufd i64 0#8) (.imm 5#64, PUnit.unit) fun r => .ret (.var r, PUnit.unit))))))

/-- Test `exit` with escaped target name, 0 args, and `f128`/`bool`/`bits 0`/`pair` payload args. -/
def fnExitEdge : Fn where
  name := "exit_edge"
  as := [.bool, Ty.float .q]
  rs := []
  body := fun _ _ (emptyExit, qv, _) =>
    .jnz (.var emptyExit)
      (.exit "abort_zero" (as := []) PUnit.unit)
      (.exit "ext\"line\n1" (as := [Ty.float .q, .bool, Ty.bits 0, .pair .bool i8]) (.var qv, .imm true, .imm 0#0, .imm (true, 0xAB#8), PUnit.unit))

/-- Test elementwise float `pair` operations (`fadd`, `fcmp`, `blend`) and `ternlog` 0xE8. -/
def fnFloatPairAndTernlog : Fn where
  name := "float_pair_ternlog"
  as := [.pair (Ty.float .s) (Ty.float .d), .pair (Ty.float .s) (Ty.float .d), i64, i64, i64]
  rs := [.pair (Ty.float .s) (Ty.float .d), .pair .bool .bool, .pair (Ty.float .s) (Ty.float .d), i64]
  body := fun _ _ (p0, p1, a, b, c, _) =>
    let1 (.fadd (.pair (Ty.float .s) (Ty.float .d))) (.var p0, .var p1, PUnit.unit) fun fpSum =>
    let1 (.fcmp .gt (.pair (Ty.float .s) (Ty.float .d))) (.var p0, .var p1, PUnit.unit) fun fpGt =>
    let1 (.blend (.pair (Ty.float .s) (Ty.float .d))) (.var fpGt, .var p0, .var p1, PUnit.unit) fun fpBlend =>
    let1 (.ternlog i64 0xE8#8) (.var a, .var b, .var c, PUnit.unit) fun maj3 =>
      .ret (.var fpSum, .var fpGt, .var fpBlend, .var maj3, PUnit.unit)

/-- Test UBSan-safe range checking in `fptoui` for out-of-range binary128 floats. -/
def fnQuadHugeFptoui : Fn where
  name := "quad_huge_fptoui"
  as := [Ty.float .q]
  rs := [i64]
  body := fun _ _ (q, _) =>
    let1 (.fptoui .q 64) (.var q, PUnit.unit) fun r => .ret (.var r, PUnit.unit)

/-- Regression test for 6-block diamond DAG reachability (`0->[1..4], 4->[1..3], 3->[1..2], 2->[1]` + `5`). -/
def fnDagReachable : Fn where
  name := "dag_reachable"
  as := [i64]
  rs := [i64]
  body := fun _ _ (sel, _) =>
    .group (sig := [[i64], [i64], [i64], [i64], [i64], [i64]])
      (fun (b0, b1, b2, b3, b4, b5, _) =>
        .cons (fun (x, _) =>
          let1 (.cmp .eq i64) (.var x, .imm 1#64, PUnit.unit) fun c1 =>
          .jnz (.var c1)
            (.jump (ts := [i64]) b1 (.var x, PUnit.unit))
            (let1 (.cmp .eq i64) (.var x, .imm 2#64, PUnit.unit) fun c2 =>
             .jnz (.var c2)
               (.jump (ts := [i64]) b2 (.var x, PUnit.unit))
               (let1 (.cmp .eq i64) (.var x, .imm 3#64, PUnit.unit) fun c3 =>
                .jnz (.var c3)
                  (.jump (ts := [i64]) b3 (.var x, PUnit.unit))
                  (.jump (ts := [i64]) b4 (.var x, PUnit.unit)))))
        (.cons (fun (x, _) =>
          let1 (.add i64) (.var x, .imm 10#64, PUnit.unit) fun r => .ret (.var r, PUnit.unit))
        (.cons (fun (x, _) =>
          let1 (.add i64) (.var x, .imm 20#64, PUnit.unit) fun y =>
            .jump (ts := [i64]) b1 (.var y, PUnit.unit))
        (.cons (fun (x, _) =>
          let1 (.cmp .eq i64) (.var x, .imm 30#64, PUnit.unit) fun c =>
          .jnz (.var c)
            (.jump (ts := [i64]) b1 (.var x, PUnit.unit))
            (.jump (ts := [i64]) b2 (.var x, PUnit.unit)))
        (.cons (fun (x, _) =>
          let1 (.cmp .eq i64) (.var x, .imm 40#64, PUnit.unit) fun ca =>
          .jnz (.var ca)
            (.jump (ts := [i64]) b1 (.var x, PUnit.unit))
            (let1 (.cmp .eq i64) (.var x, .imm 41#64, PUnit.unit) fun cb =>
             .jnz (.var cb)
               (.jump (ts := [i64]) b2 (.var x, PUnit.unit))
               (.jump (ts := [i64]) b3 (.var x, PUnit.unit))))
        (.cons (fun (x, _) =>
          let1 (.add i64) (.var x, .imm 500#64, PUnit.unit) fun r => .ret (.var r, PUnit.unit))
         .nil))))))
      (fun (b0, _, _, _, _, b5, _) =>
        let1 (.cmp .slt i64) (.var sel, .imm 10#64, PUnit.unit) fun go0 =>
        .jnz (.var go0)
          (.jump (ts := [i64]) b0 (.var sel, PUnit.unit))
          (.jump (ts := [i64]) b5 (.var sel, PUnit.unit)))

/-- Regression test for non-greedy `\001abc\0017` and multi-byte UTF-8 C string escaping. -/
def fnExitEscapes : Fn where
  name := "exit_escapes"
  as := []
  rs := []
  body := fun _ _ _ =>
    .exit "ext\x01abc\x017café€" (as := []) PUnit.unit

#guard (String.splitOn (ppFn (fn := fnDagReachable)) "L_5:").length == 2
#guard (String.splitOn (ppFn (fn := fnExitEscapes)) "\"ext\\001abc\\0017caf\\303\\251\\342\\202\\254\"").length == 2

/-- Extended pre-`Legal` test suite covering non-legalized types (`bits 0`, `bits 128`, `Fmt.h`, `Fmt.q`) and escaping/CFG regressions. -/
def extPreFns : List Fn :=
  [ fnBits0And128
  , fnFloatHalfQuad
  , fnDeadDynamicUb
  , fnExitEdge
  , fnFloatPairAndTernlog
  , fnQuadHugeFptoui
  , fnDagReachable
  , fnExitEscapes
  ]

-- ============================================================================
-- Verification that UnionFind and coreEdgeFns lower cleanly under LegalTarget
-- ============================================================================

#guard (ppModule LeanQbe.T.Examples.UnionFind.ufFns).isOk
#guard (ppModule (LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (coreEdgeFns ++ extPreFns)).isOk
#guard (ppModule (coreEdgeFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (coreEdgeFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (coreEdgeFns.map (Fn.legal .x64SSE))).isOk
#guard (ppModule (coreEdgeFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (coreEdgeFns.map (Fn.legal .x64AVX512))).isOk

-- ============================================================================
-- Helper to emit a namespaced group of functions without repeating #include
-- ============================================================================

private def emitNamespace (ns : String) (fns : List Fn) : Except String String := do
  let symMap ← buildSymMap fns
  let decls := String.join (fns.map (ppFnDecl symMap))
  let defs := String.intercalate "\n" (fns.map (ppFn symMap))
  pure (s!"namespace {ns} " ++ "{\n" ++ decls ++ "\n" ++ defs ++ "\n} // namespace " ++ ns ++ "\n")

/-- Generate standalone C++ translation units and `gen_suite.hpp` in `outDir`. -/
public def runGenerate (outDir : String) : IO UInt32 := do
  let writeChecked (fname : String) (res : Except String String) : IO Unit := do
    match res with
    | .ok s => IO.FS.writeFile (s!"{outDir}/{fname}") s
    | .error e => throw (IO.userError s!"emit {fname} failed: {e}")

  -- 1. Standalone translation units using literal `ppModule` output
  writeChecked "gen_standalone_uf.cpp" (ppModule LeanQbe.T.Examples.UnionFind.ufFns)
  writeChecked "gen_standalone_uf_avx2.cpp" (ppModule (LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal .x64AVX2)))
  writeChecked "gen_standalone_edge.cpp" (ppModule (coreEdgeFns ++ extPreFns))
  writeChecked "gen_standalone_edge_aarch64.cpp" (ppModule (coreEdgeFns.map (Fn.legal .aarch64)))

  -- 2. Namespaced suite header for differential execution in test harnesses
  let blocks ← [
    ("uf_pre", LeanQbe.T.Examples.UnionFind.ufFns),
    ("uf_aarch64", LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal .aarch64)),
    ("uf_scalar64", LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal .scalar64)),
    ("uf_avx2", LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal .x64AVX2)),
    ("edge_pre", coreEdgeFns ++ extPreFns),
    ("edge_aarch64", coreEdgeFns.map (Fn.legal .aarch64)),
    ("edge_scalar64", coreEdgeFns.map (Fn.legal .scalar64)),
    ("edge_avx2", coreEdgeFns.map (Fn.legal .x64AVX2)),
    ("edge_avx512", coreEdgeFns.map (Fn.legal .x64AVX512))
  ].mapM fun (ns, fns) =>
    match emitNamespace ns fns with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"emitNamespace {ns}: {e}")

  let header := "#pragma once\n#include \"tqbe_rt.hpp\"\n\n" ++ String.intercalate "\n" blocks
  IO.FS.writeFile s!"{outDir}/gen_suite.hpp" header
  IO.println s!"Generated standalone C++ TUs and gen_suite.hpp in {outDir}."
  pure 0

end LeanQbeTest.T.PrintCppTest

/-- Entrypoint for standalone codegen CLI execution (`args[0]` = output directory). -/
public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.PrintCppTest.runGenerate (args.headD "/tmp/leanqbe-printcpp")
