/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.IfOptLemmas
public import LeanQbe.T.OptFlatCfgLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas
public meta import LeanQbe.T.Examples.Kissat.Plain
public meta import LeanQbe.T.Inline
public meta import LeanQbe.T.Driver
public meta import LeanQbe.T.Arm64.Isa
public meta import Kraken.AArch64.Print

/-!
# Wave 6.1-C (`OPT-3` Compare Sinking next to `.select`) Tests

Covers:
1. Positive compare sinking (`clobberCmpSelect`, `nestedCmpDiamond`): a pure single-use `.bits`
   comparison separated from its `.select` condition consumer by another flag-clobbering op
   is deferred and emitted directly before that `.select`.
2. Shared multi-use compare (`twoUseCmpShared`): materialized once before its first `.select`
   condition consumer and reused via `lookupMat` at the second `.select`.
3. Negative guards:
   - Earlier non-`.select` consumer (`nonSelectUseCmpNotSunk`) is NOT deferred.
   - `.cmp` consumed as a `.select` value arm (`valueUseCmpNotSunk`) is NOT deferred.
   - Adjacent `.cmp` + `.select` with no intervening flag-clobber (`adjCmpNotMoved`) is untouched.
4. Soundness (`Wf`, `Func.cmpSink_spec`, `Func.ifOptBits_spec`, `callsOk`, `OptFlatCfg.ifOptFlat`)
   and clean `#print axioms` (`std3`).
5. Arm64 codegen activation + `Kissat.Plain` `#eval` guards (`plain_analyze_rsn`,
   `plain_prop_lit`, `plain_sweep`, and `plain_sort_reds` `4× csel`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.OptW61IfOptCmpSinkTest

open LeanQbe.T

/-- Outer `.cmp` separated from its `.select` condition by an intervening `.cmp` + `.select`. -/
def clobberCmpSelect : Func [i64, i64, i64, i64, i64] [i64] :=
  fun _ _ (a, b, x, t, e, ()) =>
  .let_ (op2 (.cmp .ult i64) (.var a) (.var b)) fun (c1, ()) =>
  .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0)) fun (c2, ()) =>
  .let_ (op3 (.select i64) (.var c2) (.var t) (.var e)) fun (s2, ()) =>
  .let_ (op3 (.select i64) (.var c1) (.var s2) (.var a)) fun (r, ()) =>
  .ret (.var r, ())

theorem clobberCmpSelect_cmpSink_out :
    Func.cmpSink clobberCmpSelect = fun _ _ (a, b, x, t, e, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var x) (.imm 0)) fun (c2, ()) =>
      .let_ (op3 (.select i64) (.var c2) (.var t) (.var e)) fun (s2, ()) =>
      .let_ (op2 (.cmp .ult i64) (.var a) (.var b)) fun (c1, ()) =>
      .let_ (op3 (.select i64) (.var c1) (.var s2) (.var a)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

theorem clobberCmpSelect_wf : clobberCmpSelect.Wf := by t_wf_reify

theorem clobberCmpSelect_cmpSink_wf : (Func.cmpSink clobberCmpSelect).Wf :=
  Func.cmpSink_wf clobberCmpSelect_wf

theorem clobberCmpSelect_cmpSink_callsOk :
    ((Func.cmpSink clobberCmpSelect) (fun _ => Unit) (fun _ => Unit)
      (Tup.units [i64, i64, i64, i64, i64])).callsOk [] [] :=
  Func.cmpSink_callsOk clobberCmpSelect_wf trivial

theorem clobberCmpSelect_cmpSink_spec (Γ : Env)
    (a b x t e : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.cmpSink clobberCmpSelect) (a, b, x, t, e, ()) m
      (fun (r, ()) m' =>
        let s2 := if x == 0#64 then t else e
        r = (if BitVec.ult a b then s2 else a) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.cmpSink_spec clobberCmpSelect_wf
  dsimp only [Func.spec, Func.wp, clobberCmpSelect, wp, Op.wp, OpCode.wp,
    op2, op3, vals, Arg.val, liftCmp, CmpOp.evalBits, i64]
  exact ⟨rfl, rfl⟩

/-- Nested `jnz` diamond lowered by `Func.ifOptBits`: both outer compare + inner compare become
adjacent to their `.select` consumers. -/
def nestedCmpDiamond : Func [i64, i64, i64] [i64] := fun _ _ (x, y, z, ()) =>
  .jnz (.imm true)
    (.let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c1, ()) =>
     .jnz (.var c1)
       (.let_ (op2 (.cmp .ult i64) (.var x) (.var z)) fun (c2, ()) =>
        .jnz (.var c2)
          (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (v, ()) => .ret (.var v, ()))
          (.ret (.imm 0, ())))
       (.ret (.imm 0, ())))
    (.ret (.imm 0, ()))

theorem nestedCmpDiamond_wf : nestedCmpDiamond.Wf := by t_wf_reify

theorem nestedCmpDiamond_ifOptBits_wf : (Func.ifOptBits nestedCmpDiamond).Wf :=
  Func.ifOptBits_wf nestedCmpDiamond_wf

theorem nestedCmpDiamond_ifOptFlat_eq :
    OptFlatCfg.ifOptFlat true [i64, i64, i64] (reifyFunc nestedCmpDiamond) =
      reifyFunc (Func.ifOptBits (denoteFunc (as := [i64, i64, i64])
        (reifyFunc nestedCmpDiamond))) :=
  OptFlatCfg.ifOptFlat_true_eq _ (by t_kernel_rfl)

/-- Shared compare across two `.select`s: sunk past the clobber and materialized once before the
first `.select`, then reused via `lookupMat` at the second `.select`. -/
def twoUseCmpShared : Func [i64, i64, i64, i64] [i64] := fun _ _ (a, b, t, e, ()) =>
  .let_ (op2 (.cmp .ult i64) (.var a) (.var b)) fun (c1, ()) =>
  .let_ (op2 (.cmp .eq i64) (.var a) (.imm 0)) fun (c2, ()) =>
  .let_ (op3 (.select i64) (.var c2) (.var t) (.var e)) fun (s1, ()) =>
  .let_ (op3 (.select i64) (.var c1) (.var s1) (.var t)) fun (s2, ()) =>
  .let_ (op3 (.select i64) (.var c1) (.var s2) (.var e)) fun (r, ()) =>
  .ret (.var r, ())

theorem twoUseCmpShared_out :
    Func.cmpSink twoUseCmpShared = fun _ _ (a, b, t, e, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var a) (.imm 0)) fun (c2, ()) =>
      .let_ (op3 (.select i64) (.var c2) (.var t) (.var e)) fun (s1, ()) =>
      .let_ (op2 (.cmp .ult i64) (.var a) (.var b)) fun (c1, ()) =>
      .let_ (op3 (.select i64) (.var c1) (.var s1) (.var t)) fun (s2, ()) =>
      .let_ (op3 (.select i64) (.var c1) (.var s2) (.var e)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

/-- Negative guard 1: `.cmp` consumed by an earlier non-`.select` op must NOT be deferred. -/
def nonSelectUseCmpNotSunk : Func [i64, i64, i64, i64] [i64] := fun _ _ (a, b, t, e, ()) =>
  .let_ (op2 (.cmp .ult i64) (.var a) (.var b)) fun (c1, ()) =>
  .let_ (op2 (.cmp .eq .bool) (.var c1) (.imm false)) fun (nc, ()) =>
  .let_ (op3 (.select i64) (.var nc) (.var t) (.var e)) fun (s1, ()) =>
  .let_ (op3 (.select i64) (.var c1) (.var s1) (.var t)) fun (r, ()) =>
  .ret (.var r, ())

theorem nonSelectUseCmpNotSunk_unchanged :
    Func.cmpSink nonSelectUseCmpNotSunk = nonSelectUseCmpNotSunk := by
  t_kernel_rfl

/-- Negative guard 2: `.cmp` used as a `.select` value operand (`aT`) must NOT be deferred. -/
def valueUseCmpNotSunk : Func [i64, i64, .bool] [.bool] := fun _ _ (a, b, flag, ()) =>
  .let_ (op2 (.cmp .ult i64) (.var a) (.var b)) fun (c1, ()) =>
  .let_ (op2 (.cmp .eq i64) (.var a) (.imm 0)) fun (c2, ()) =>
  .let_ (op3 (.select .bool) (.var flag) (.var c1) (.var c2)) fun (r, ()) =>
  .ret (.var r, ())

theorem valueUseCmpNotSunk_unchanged :
    Func.cmpSink valueUseCmpNotSunk = valueUseCmpNotSunk := by
  t_kernel_rfl

/-- Negative guard 3: `.cmp` before `.select` with no intervening flag-clobber stays in place. -/
def adjCmpNotMoved : Func [i64, i64, i64] [i64] := fun _ _ (x, y, a, ()) =>
  .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
  .let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) =>
  .let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) =>
  .let_ (op3 (.select i64) (.var c) (.var t) (.var e)) fun (s, ()) =>
  .ret (.var s, ())

theorem adjCmpNotMoved_unchanged :
    Func.cmpSink adjCmpNotMoved = adjCmpNotMoved := by
  t_kernel_rfl

end LeanQbeTest.T.OptW61IfOptCmpSinkTest

private abbrev clobberSpec :=
  @LeanQbeTest.T.OptW61IfOptCmpSinkTest.clobberCmpSelect_cmpSink_spec
private abbrev clobberCallsOk :=
  @LeanQbeTest.T.OptW61IfOptCmpSinkTest.clobberCmpSelect_cmpSink_callsOk

#print axioms clobberSpec
#print axioms clobberCallsOk
#print axioms LeanQbe.T.Func.cmpSink_wf
#print axioms LeanQbe.T.Func.cmpSink_spec
#print axioms LeanQbe.T.Func.cmpSink_callsOk
#print axioms LeanQbe.T.Func.ifOptBits_wf
#print axioms LeanQbe.T.Func.ifOptBits_spec
#print axioms LeanQbe.T.OptFlatCfg.ifOptFlat_true_eq

end

private meta def countInsnsArm (lines : List String) (pfx : String) : Nat :=
  lines.foldl (fun acc l =>
    let t := l.trimAscii.toString
    if t.startsWith pfx then acc + 1 else acc) 0

private meta def compileArmReport (f : LeanQbe.T.Fn) :
    Except String (Nat × List String) :=
  match LeanQbe.T.Driver.compileFnFlat
      LeanQbe.T.Arm64.armIsa LeanQbe.T.Arm64.armLegalTarget f with
  | .ok c =>
    let nReal := c.foldl (fun acc d => match d with | .instr _ => acc + 1 | _ => acc) 0
    .ok (nReal, c.map Kraken.AArch64.Print.directive)
  | .error e => .error s!"{f.name}: {e}"

#eval show IO Unit from do
  -- 1. Unit litmus: clobberCmpSelect emits 0 csinc on Arm64 (direct cmp+csel fusion).
  let fLit : LeanQbe.T.Fn :=
    ⟨"clobberCmpSelect",
     [LeanQbe.T.i64, LeanQbe.T.i64, LeanQbe.T.i64, LeanQbe.T.i64, LeanQbe.T.i64],
     [LeanQbe.T.i64], LeanQbeTest.T.OptW61IfOptCmpSinkTest.clobberCmpSelect⟩
  let (_, linesLit) ← match compileArmReport fLit with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let csincLit := countInsnsArm linesLit "csinc"
  let cselLit := countInsnsArm linesLit "csel"
  if csincLit != 0 then
    throw (IO.userError s!"clobberCmpSelect arm64: expected 0 csinc, got {csincLit}")
  if cselLit != 2 then
    throw (IO.userError s!"clobberCmpSelect arm64: expected 2 csel, got {cselLit}")
  -- 2. `Kissat.Plain` Arm64 activation & non-regression guards.
  let m := LeanQbe.T.Examples.Kissat.Plain.plainModule
  let mInl := m.inlinePolicy {}
  let checkTarget := fun (name : String) => do
    let some fn := (mInl.fns.map LeanQbe.T.Fn.renorm).find? (·.name == name)
      | throw (IO.userError s!"missing fn {name}")
    match compileArmReport fn with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let (nRsn, lRsn) ← checkTarget "plain_analyze_rsn"
  let (nPropLit, _) ← checkTarget "plain_prop_lit"
  let (nSweep, _) ← checkTarget "plain_sweep"
  let (nSrt, lSrt) ← checkTarget "plain_sort_reds"
  let cselSrt := countInsnsArm lSrt "csel"
  let csincRsn := countInsnsArm lRsn "csinc"
  if nRsn > 85 then
    throw (IO.userError s!"plain_analyze_rsn insns {nRsn} > 85")
  if csincRsn > 1 then
    throw (IO.userError s!"plain_analyze_rsn csinc {csincRsn} > 1")
  if nPropLit > 326 then
    throw (IO.userError s!"plain_prop_lit insns {nPropLit} > 326")
  if nSweep > 582 then
    throw (IO.userError s!"plain_sweep insns {nSweep} > 582")
  if nSrt != 120 || cselSrt != 4 then
    throw (IO.userError s!"plain_sort_reds regression: insns={nSrt} csel={cselSrt}")
