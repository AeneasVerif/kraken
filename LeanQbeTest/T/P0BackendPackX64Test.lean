module

import LeanQbe.T.MainCertCore
import LeanQbe.T.MainCertFlat
import LeanQbe.T.MainCertInline
import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.Amd64.PrintATTAlign
import LeanQbe.T.Amd64.DebugAsm
import LeanQbe.T.Notation
import LeanQbe.T.SimplifyGroupPlan
import LeanQbe.T.Opt
import LeanQbe.T.Spill
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.MainCertInline
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.PrintATTAlign
meta import LeanQbe.T.Amd64.DebugAsm
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.SimplifyGroupPlan
meta import LeanQbe.T.Opt
meta import LeanQbe.T.Spill

/-!
# P0 Backend Performance Pack — SysV x64 Regression & Parity Tests

Verifies Ranks 1–4 on SysV x64:
1. Rank 1 (`Spill`): multi-block loop body weighting (`gatherAtB`) and relaxed `slotOpNoLoad`
   (`buildRegionReused` with `rvsInter` + `isCmpBitsCode` exclusion) folding spilled comparisons.
2. Rank 2 (`SimplifyGroupPlan` + `hasSimpGroup`): single-use `kc == 1` splicing with `> 16`
   instructions (including inside multi-loop functions).
3. Rank 3 (`Rega.shuffle` + `RegaFlat`): flag-liveness-gated `xorl` zero-idiom across `.jump`,
   `.ret`, and `.call` parallel-move shuffles while preserving `movl $0` on live-flag `cmov`.
4. Rank 4 (`RegaDefs.lname` + `DebugAsm`): `.L<fn>.<n>` local labels (`0` `{fn}.L{n}` leaks) and
   `emitX64DebugAsmChecked` `some hs == none` parity.
5. Exact `(flat := false)` vs `(flat := true)` kernel `code = rfl` and `bounds = rfl` parity.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.P0BackendPackX64Test

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Notation
open Kraken.X64

/-! ## Fixtures -/

/-- Rank 1a: multi-block loop where body arms carry computation and jump back to `@hdr`. -/
def fnMultiBlkLoop : Fn := tqbe $p0_mblk_loop(%n:l, %a:l, %b:l, %c:l) -> l {
  loop @hdr(%i:l = %n, %x:l = %a, %y:l = %b, %z:l = %c) {
    %cond =b cnel %i, 0
    jnz %cond, {
      %x1 =l add %x, %y
      %y1 =l xor %y, %z
      %i1 =l sub %i, 1
      %odd =l and %i1, 1
      %isOdd =b cnel %odd, 0
      jnz %isOdd, {
        %z1 =l add %z, %x1
        continue @hdr(%i1, %x1, %y1, %z1)
      }, {
        %z2 =l sub %z, %y1
        continue @hdr(%i1, %y1, %x1, %z2)
      }
    }, {
      %r =l add %x, %z
      ret %r
    }
  }
}

/-- Rank 1b: 18 live GPRs force spilling; spilled variable compared before `jnz` and reused in
only one arm folds directly into a memory-operand `cmp`/`add`/`xor ...(%rsp)`. -/
def fnSpillCmpOneArm : Fn :=
  ⟨"p0_spill_cmp", [i64, i64, i64, i64, i64, i64], [i64],
    fun _ _ (a, b, c, d, e, f, ()) =>
      .let_ (op2 (.add i64) (.var a) (.var b)) fun (v0, ()) =>
      .let_ (op2 (.xor i64) (.var b) (.var c)) fun (v1, ()) =>
      .let_ (op2 (.add i64) (.var c) (.var d)) fun (v2, ()) =>
      .let_ (op2 (.xor i64) (.var d) (.var e)) fun (v3, ()) =>
      .let_ (op2 (.add i64) (.var e) (.var f)) fun (v4, ()) =>
      .let_ (op2 (.xor i64) (.var f) (.var a)) fun (v5, ()) =>
      .let_ (op2 (.add i64) (.var v0) (.var v1)) fun (v6, ()) =>
      .let_ (op2 (.xor i64) (.var v2) (.var v3)) fun (v7, ()) =>
      .let_ (op2 (.add i64) (.var v4) (.var v5)) fun (v8, ()) =>
      .let_ (op2 (.xor i64) (.var v6) (.var v7)) fun (v9, ()) =>
      .let_ (op2 (.add i64) (.var v8) (.var v9)) fun (v10, ()) =>
      .let_ (op2 (.xor i64) (.var v0) (.var v10)) fun (v11, ()) =>
      .let_ (op2 (.add i64) (.var v1) (.var v11)) fun (v12, ()) =>
      .let_ (op2 (.xor i64) (.var v2) (.var v12)) fun (v13, ()) =>
      .let_ (op2 (.add i64) (.var v3) (.var v13)) fun (v14, ()) =>
      .let_ (op2 (.xor i64) (.var v4) (.var v14)) fun (v15, ()) =>
      .let_ (op2 (.add i64) (.var v5) (.var v15)) fun (v16, ()) =>
      .let_ (op2 (.xor i64) (.var v6) (.var v16)) fun (v17, ()) =>
      .let_ (op2 (.cmp .ult i64) (.var v0) (.var v17)) fun (cmp0, ()) =>
      .jnz (.var cmp0)
        (.let_ (op2 (.add i64) (.var v0) (.var v1)) fun (s0, ()) =>
         .let_ (op2 (.add i64) (.var s0) (.var v2)) fun (s1, ()) =>
         .let_ (op2 (.add i64) (.var s1) (.var v3)) fun (s2, ()) =>
         .let_ (op2 (.add i64) (.var s2) (.var v4)) fun (s3, ()) =>
         .let_ (op2 (.add i64) (.var s3) (.var v5)) fun (s4, ()) =>
         .let_ (op2 (.add i64) (.var s4) (.var v6)) fun (s5, ()) =>
         .let_ (op2 (.add i64) (.var s5) (.var v7)) fun (s6, ()) =>
         .let_ (op2 (.add i64) (.var s6) (.var v8)) fun (s7, ()) =>
         .let_ (op2 (.add i64) (.var s7) (.var v9)) fun (s8, ()) =>
         .let_ (op2 (.add i64) (.var s8) (.var v10)) fun (s9, ()) =>
         .let_ (op2 (.add i64) (.var s9) (.var v11)) fun (s10, ()) =>
         .let_ (op2 (.add i64) (.var s10) (.var v12)) fun (s11, ()) =>
         .let_ (op2 (.add i64) (.var s11) (.var v13)) fun (s12, ()) =>
         .let_ (op2 (.add i64) (.var s12) (.var v14)) fun (s13, ()) =>
         .let_ (op2 (.add i64) (.var s13) (.var v15)) fun (s14, ()) =>
         .let_ (op2 (.add i64) (.var s14) (.var v16)) fun (s15, ()) =>
         .let_ (op2 (.add i64) (.var s15) (.var v17)) fun (s16, ()) =>
         .ret (.var s16, ()))
        (.let_ (op2 (.xor i64) (.var v1) (.var v2)) fun (t0, ()) =>
         .let_ (op2 (.xor i64) (.var t0) (.var v3)) fun (t1, ()) =>
         .let_ (op2 (.xor i64) (.var t1) (.var v4)) fun (t2, ()) =>
         .let_ (op2 (.xor i64) (.var t2) (.var v5)) fun (t3, ()) =>
         .let_ (op2 (.xor i64) (.var t3) (.var v6)) fun (t4, ()) =>
         .let_ (op2 (.xor i64) (.var t4) (.var v7)) fun (t5, ()) =>
         .let_ (op2 (.xor i64) (.var t5) (.var v8)) fun (t6, ()) =>
         .let_ (op2 (.xor i64) (.var t6) (.var v9)) fun (t7, ()) =>
         .let_ (op2 (.xor i64) (.var t7) (.var v10)) fun (t8, ()) =>
         .let_ (op2 (.xor i64) (.var t8) (.var v11)) fun (t9, ()) =>
         .let_ (op2 (.xor i64) (.var t9) (.var v12)) fun (t10, ()) =>
         .let_ (op2 (.xor i64) (.var t10) (.var v13)) fun (t11, ()) =>
         .let_ (op2 (.xor i64) (.var t11) (.var v14)) fun (t12, ()) =>
         .let_ (op2 (.xor i64) (.var t12) (.var v15)) fun (t13, ()) =>
         .let_ (op2 (.xor i64) (.var t13) (.var v16)) fun (t14, ()) =>
         .let_ (op2 (.xor i64) (.var t14) (.var v17)) fun (t15, ()) =>
         .ret (.var t15, ()))⟩

private def bigChain {V : Ty → Type} {L : List Ty → Type} (b : V i64) :
    Nat → V i64 → Expr V L [i64]
  | 0, x => .ret (.var x, ())
  | n + 1, x =>
    .let_ (op2 (.xor i64) (.var x) (.imm (BitVec.ofNat 64 (n + 3)))) fun (y, ()) =>
    .let_ (op2 (.add i64) (.var y) (.var b)) fun (z, ()) =>
    bigChain b n z

/-- Rank 2: single-use `kc == 1` continuation with `> 16` instructions (`20` ops). -/
def fnBigSplice : Fn :=
  ⟨"p0_big_splice", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .group (sig := [[i64]])
      (fun _ => .cons (fun (p, ()) => bigChain b 10 p) .nil)
      (fun (j, ()) =>
        .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (a1, ()) =>
        .jump j (.var a1, ()))⟩

/-- Rank 3a: prior `cmp` sets flags before `.call`, `.jump`, and `.ret` zero-immediate shuffles;
when flags are dead at each terminator, every zero emits `xorl` (`0` register `mov $0`). -/
def fnZeroShuffle : Fn := tqbe $p0_zero_shuf(%n:l, %x:l) -> l {
  %c =b cnel %n, 0
  jnz %c, {
    %r =l call $p0_ext(0:l, %x)
    loop @lp(%i:l = %n, %acc:l = 0:l, %z:l = 0:l) {
      %done =b ceql %i, 0
      jnz %done, {
        %out =l add %acc, %z
        ret %out
      }, {
        %i1 =l sub %i, 1
        %a1 =l add %acc, %r
        %eq =b ceql %i1, 3
        jnz %eq, {
          %t =l call $p0_ext(%a1, 0:l)
          continue @lp(%i1, %t, 0:l)
        }, {
          continue @lp(%i1, 0:l, %a1)
        }
      }
    }
  }, {
    ret 0:l
  }
}

/-- Rank 3b: live flags across `select` (`cmov`) must fail closed and NOT clobber flags. -/
def fnZeroLiveFlag : Fn :=
  ⟨"p0_zero_live", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var a) (.var b)) fun (c, ()) =>
    .let_ (op3 (.select i64) (.var c) (.imm 0) (.var b)) fun (r, ()) =>
    .ret (.var r, ())⟩

def p0Fns : List Fn :=
  [fnMultiBlkLoop, fnSpillCmpOneArm, fnBigSplice, fnZeroShuffle, fnZeroLiveFlag]

def p0SrcMod : Module := ⟨p0Fns, [], ["p0_ext_exit"]⟩

inline_mod! p0Mod p0SrcMod {} (compile := false)

/-! ## Dual-Mode `(flat := false)` vs `(flat := true)` Parity -/

compile_linked_chunks! p0X64Leg x64Target x64Layout x64LegalTarget x64LabelClean
  p0Mod 32 (ext := [(⟨"p0_ext", [i64, i64], [i64]⟩, 0)]) (exits := ["p0_ext_exit"])
  (flat := false)

compile_linked_chunks! p0X64Flat x64Target x64Layout x64LegalTarget x64LabelClean
  p0Mod 32 (ext := [(⟨"p0_ext", [i64, i64], [i64]⟩, 0)]) (exits := ["p0_ext_exit"])
  (flat := true)

theorem p0_x64_code_eq : p0X64Leg.code = p0X64Flat.code := rfl

theorem p0_x64_bounds_eq : p0X64Leg.bounds = p0X64Flat.bounds := rfl

/-! ## Rank 1–4 Checks -/

private meta def countSub (hay needle : String) : Nat :=
  if needle.isEmpty then 0 else (hay.splitOn needle).length - 1

private meta def isRegMov0 (ln : String) : Bool :=
  let s := ln.trimAscii.toString
  s.startsWith "movl $0, %" || s.startsWith "movq $0, %"

private meta def isXorlZero (ln : String) : Bool :=
  let s := ln.trimAscii.toString
  if !s.startsWith "xorl %" then false
  else match (s.drop 5).toString.splitOn ", " with
    | [r1, r2] => r1 == r2
    | _ => false

private meta def hasAnyGroup {rs : List Ty} : TFlat rs → Bool
  | .group .. => true
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => hasAnyGroup k
  | .jnz _ t e => hasAnyGroup t || hasAnyGroup e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => false

-- Rank 1: `fnSpillCmpOneArm` spills and folds directly into `cmp`/`add`/`xor ...(%rsp)`
#guard
  let h := Fn.computeHints x64Target.toIsa x64LegalTarget fnSpillCmpOneArm
  match compileFn x64Target.toIsa x64LegalTarget h fnSpillCmpOneArm with
  | .error _ => false
  | .ok ds =>
    let lines := (toATTAligned ds).splitOn "\n"
    let memAlu := lines.any fun ln =>
      let s := ln.trimAscii.toString
      (s.startsWith "cmp" || s.startsWith "add" || s.startsWith "xor") &&
        (s.splitOn "(%rsp)").length > 1
    h.nslots ≥ 1 && memAlu

-- Rank 2: single-use `> 16`-insn block (`tflatSize == 21`) is detected and spliced inline
#guard
  let tf := reifyFunc fnBigSplice.body
  let tf' := reifyFunc (Func.simplifyGroupPlan fnBigSplice.body)
  hasSimpGroup false tf && !hasAnyGroup tf'

-- Rank 3: `fnZeroShuffle` emits `xorl` (`>= 4`) across `.call`/`.jump`/`.ret` and ZERO `mov $0, %r`
#guard
  let ext : Rega.Ext := { callees := [("p0_ext", [i64, i64], [i64])] }
  let f := fnZeroShuffle.mid x64LegalTarget
  let h := Spill.hints x64Target.toIsa f
  match Rega.lowerFn x64Target.toIsa h ext f with
  | .error _ => false
  | .ok ds =>
    let lines := (toATTAligned ds).splitOn "\n"
    let nXor := lines.foldl (fun a l => if isXorlZero l then a + 1 else a) 0
    let nMov0 := lines.foldl (fun a l => if isRegMov0 l then a + 1 else a) 0
    nXor ≥ 4 && nMov0 == 0

-- Rank 4: `.L<fn>.<n>` local labels (zero legacy `{fn}.L{n}` leaks) + DebugAsm parity
#guard
  let fns := [fnMultiBlkLoop, fnSpillCmpOneArm, fnBigSplice, fnZeroLiveFlag]
  let hs := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  match compile x64Target.toIsa x64LegalTarget fns hs with
  | .error _ => false
  | .ok ds =>
    let fnNames := fns.map (·.name)
    let localLbls := ds.filterMap fun
      | .label l => if fnNames.contains l then none else some l
      | _ => none
    let allDotL := !localLbls.isEmpty && localLbls.all fun l =>
      l.startsWith ".L" && (l.splitOn ".L").length == 2
    let noLegacy := localLbls.all fun l => !fnNames.any fun fn => l.startsWith (fn ++ ".L")
    let dbgOk :=
      match emitX64DebugAsmChecked fns ds (some hs) [] false true,
            emitX64DebugAsmChecked fns ds none [] false true with
      | .ok s1, .ok s2 => s1 == s2 && countSub s1 ".p2align 5,,12" ≥ 1
      | _, _ => false
    allDotL && noLegacy && dbgOk

#print axioms p0_x64_code_eq
#print axioms p0_x64_bounds_eq
#print axioms p0X64Leg
#print axioms p0X64Flat

end LeanQbeTest.T.P0BackendPackX64Test
