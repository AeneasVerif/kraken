module

import LeanQbe.T.CondThreadOptLemmas
import LeanQbe.T.TailDupLemmas
import LeanQbe.T.OptFlatBranchLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.MainLemmas
meta import LeanQbe.T.CondThreadOpt
meta import LeanQbe.T.TailDup
meta import LeanQbe.T.OptFlatBranch
meta import LeanQbe.T.MainInline
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.PrintATTAlign
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Wave 6.1-A Activation & Soundness Tests (`OPT-1` `CondThreadOpt` + `OPT-4` `TailDup` Latch)

Verifies:
1. `OPT-1` `jumpImmBools 64` window + `.group`/`.let_`-headed `.splitBool` + 2-iter cleanup on:
   - `wideBoolSplit10`: `10`-parameter block testing boolean param `8` (`≥ 8` old limit).
   - `chainedWide11`: chained `11`-parameter (`p10`) → `10`-parameter (`p8`) threading.
   - `groupHeadBoolSplit`: `.group`-headed block (`.group [L10] (.jnz flag ...)) modeling a
     nested exit join.
   - `letHeadBoolSplit`: `.let_`-headed block `.splitBool`.
2. `OPT-4` `TailDup` tiny `.jnz` loop-latch duplication (`allowJnzLatch := true` vs `false` default)
   and negative bounds (`requireLoopHdr`, `maxLatchInstrs := 3`, `maxLatchPreds := 3`).
3. Formal `Wf`, `Func.spec`, and `callsOk` soundness + `#print axioms` (`≤ std3`).
4. `Kissat.Plain` activation `#guard`s on `plain_prop_lit` (`LegalTarget.x64`,
   `LegalTarget.aarch64`, and `x64Target` instruction/spill-store bounds) and
   `plain_analyze_rsn`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.OptW61CfgThreadDupTest

open LeanQbe.T
open LeanQbe.T.Amd64

/-! ## Helpers -/

mutual
meta def countJnz {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => countJnz k
  | .jnz _ t e => 1 + countJnz t + countJnz e
  | .group bs k => countJnzB bs + countJnz k
  | _ => 0

meta def countJnzB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countJnz b + countJnzB bs
end

mutual
meta def countBlocks {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => countBlocks k
  | .jnz _ t e => countBlocks t + countBlocks e
  | .group (sig := sig) bs k => sig.length + countBlocksB bs + countBlocks k
  | _ => 0

meta def countBlocksB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countBlocks b + countBlocksB bs
end

/-! ## 1. `OPT-1` Unit Litmus Fixtures (`jumpImmBools 64`, `.group`/`.let_` head, 2-iter) -/

/-- `10`-parameter block with tested bool at parameter index `8`
(`≥ 8` old `jumpImmBools 8` cap). -/
def wideBoolSplit10 : Func [.bool, i64] [i64] := fun _ _ (c, y, ()) =>
  .group (sig := [[i64, i64, i64, i64, i64, i64, i64, i64, .bool, i64]])
    (fun _ =>
      .cons (fun (_, _, _, _, _, _, _, _, flag, v, ()) =>
        .jnz (.var flag)
          (.let_ (op2 (.add i64) (.var v) (.imm 1)) fun (r1, ()) => .ret (.var r1, ()))
          (.let_ (op2 (.sub i64) (.var v) (.imm 1)) fun (r2, ()) => .ret (.var r2, ()))) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.jump J (.imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
          .imm true, .var y, ()))
        (.jump J (.imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
          .imm false, .var y, ())))

theorem wideBoolSplit10_ct_eq : Func.condThreadOpt wideBoolSplit10 = fun _ _ (c, y, ()) =>
    .group (sig := []) (fun _ => .nil)
      (fun _ =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var y) (.imm 1)) fun (r1, ()) => .ret (.var r1, ()))
          (.let_ (op2 (.sub i64) (.var y) (.imm 1)) fun (r2, ()) => .ret (.var r2, ()))) := by
  t_kernel_rfl

#guard countJnz (reifyFunc (Func.condThreadOpt wideBoolSplit10)) == 1
#guard countBlocks (reifyFunc (Func.condThreadOpt wideBoolSplit10)) == 0
#guard Func.checkTFlat (Func.condThreadLateOpt wideBoolSplit10) == true

/-- Chained `11`-parameter block (`p10` bool) feeding a `10`-parameter block (`p8` bool):
threads both `p10` and `p8` away via `jumpImmBools 64`. -/
def chainedWide11 : Func [.bool, i64] [i64] := fun _ _ (c, y, ()) =>
  .group (sig := [[i64, i64, i64, i64, i64, i64, i64, i64, .bool, i64]])
    (fun _ =>
      .cons (fun (_, _, _, _, _, _, _, _, f8, v, ()) =>
        .jnz (.var f8)
          (.let_ (op2 (.add i64) (.var v) (.imm 10)) fun (r1, ()) => .ret (.var r1, ()))
          (.let_ (op2 (.sub i64) (.var v) (.imm 10)) fun (r2, ()) => .ret (.var r2, ())))
      .nil)
    (fun (B10, ()) =>
      .group (sig := [[i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, .bool]])
        (fun _ =>
          .cons (fun (x, _, _, _, _, _, _, _, _, _, f10, ()) =>
            .jnz (.var f10)
              (.jump B10 (.imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
                .imm true, .var x, ()))
              (.jump B10 (.imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
                .imm false, .var x, ())))
          .nil)
        (fun (B11, ()) =>
          .jnz (.var c)
            (.jump B11 (.var y, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
              .imm 0, .imm 0, .imm true, ()))
            (.jump B11 (.var y, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
              .imm 0, .imm 0, .imm false, ()))))

#guard countJnz (reifyFunc (Func.condThreadOpt chainedWide11)) == 1
#guard countBlocks (reifyFunc (Func.condThreadOpt chainedWide11)) == 0
#guard Func.checkTFlat (Func.condThreadLateOpt chainedWide11) == true

/-- `.group`-headed bool-parameter split modeling `full_propagate_ignore_hot` `L_9` -> `L_10`:
`L9` wraps inner `.group [L10: jnz flag ...]` before `.jnz flag (compute) (jump L10)`. -/
def groupHeadBoolSplit : Func [.bool, i64, i64] [i64] := fun _ _ (c, d, x, ()) =>
  .group (sig := [[i64], [i64]])
    (fun (hdr, done, ()) =>
      .cons (fun (n, ()) =>
        .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (isZ, ()) =>
        .jnz (.var isZ)
          (.jump done (.var n, ()))
          (.group (sig := [[i64, i64, i64, i64, i64, i64, i64, i64, .bool, i64]])
            (fun _ =>
              .cons (fun (_, _, _, _, _, _, _, _, flag, v, ()) =>
                .group (sig := [[]])
                  (fun _ =>
                    .cons (fun () =>
                      .jnz (.var flag)
                        (.let_ (op2 (.sub i64) (.var v) (.imm 1)) fun (v', ()) =>
                          .jump hdr (.var v', ()))
                        (.jump done (.var v, ()))) .nil)
                  (fun (L10, ()) =>
                    .jnz (.var flag)
                      (.let_ (op2 (.add i64) (.var v) (.imm 7)) fun (w, ()) =>
                        .jump done (.var w, ()))
                      (.jump L10 ()))) .nil)
            (fun (L9, ()) =>
              .jnz (.var c)
                (.jump L9 (.imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
                  .imm true, .var n, ()))
                (.jnz (.var c)
                  (.jump L9 (.imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
                    .imm false, .var n, ()))
                  (.jump L9 (.imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
                    .imm false, .var d, ()))))))
      (.cons (fun (res, ()) => .ret (.var res, ())) .nil))
    (fun (hdr, _, ()) => .jump hdr (.var x, ()))

#guard countJnz (reifyFunc groupHeadBoolSplit) == 5
#guard countJnz (reifyFunc (Func.condThreadOpt groupHeadBoolSplit)) == 2
#guard Func.checkTFlat (Func.condThreadLateOpt groupHeadBoolSplit) == true

/-- `.let_`-headed bool-parameter split. -/
def letHeadBoolSplit : Func [.bool, .bool, i64] [i64] := fun _ _ (c, d, x, ()) =>
  .group (sig := [[.bool, i64]])
    (fun _ =>
      .cons (fun (flag, v, ()) =>
        .let_ (op2 (.add i64) (.var v) (.imm 5)) fun (v5, ()) =>
        .jnz (.var flag)
          (.ret (.var v5, ()))
          (.let_ (op2 (.xor i64) (.var v5) (.imm 1)) fun (r, ()) => .ret (.var r, ()))) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.jump J (.imm true, .var x, ()))
        (.jnz (.var c)
          (.jump J (.imm false, .var x, ()))
          (.jump J (.var d, .var x, ()))))

#guard countJnz (reifyFunc letHeadBoolSplit) == 3
#guard countJnz (reifyFunc (Func.condThreadOpt letHeadBoolSplit)) == 2
#guard Func.checkTFlat (Func.condThreadLateOpt letHeadBoolSplit) == true

/-! ## 2. `OPT-4` `.jnz` Loop-Latch Unit Litmus & Negative Bounds -/

/-- Enclosing self-recursive loop `hdr` with an inner `2`-predecessor, `2`-insn `.jnz` loop latch
`latch` and non-duplicable `4`-insn `exitB`: untouched under default `allowJnzLatch = false`,
duplicated when `allowJnzLatch = true`. -/
def tinyJnzLatchLoop : Func [.bool, i64] [i64] := fun _ _ (c, x, ()) =>
  .group (sig := [[i64, i64], [i64]])
    (fun (hdr, exitB, ()) =>
      .cons (fun (i, acc, ()) =>
        .group (sig := [[i64, i64]])
          (fun _ =>
            .cons (fun (li, lacc, ()) =>
              .let_ (op2 (.sub i64) (.var li) (.imm 1)) fun (i', ()) =>
              .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (nz, ()) =>
              .jnz (.var nz)
                (.jump hdr (.var i', .var lacc, ()))
                (.jump exitB (.var lacc, ()))) .nil)
          (fun (latch, ()) =>
            .jnz (.var c)
              (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (a1, ()) =>
                .jump latch (.var i, .var a1, ()))
              (.let_ (op2 (.add i64) (.var acc) (.imm 2)) fun (a2, ()) =>
                .jump latch (.var i, .var a2, ()))))
      (.cons (fun (r, ()) =>
        .let_ (op2 (.add i64) (.var r) (.imm 1)) fun (r1, ()) =>
        .let_ (op2 (.xor i64) (.var r1) (.imm 2)) fun (r2, ()) =>
        .let_ (op2 (.add i64) (.var r2) (.imm 3)) fun (r3, ()) =>
        .ret (.var r3, ())) .nil))
    (fun (hdr, _, ()) => .jump hdr (.var x, .imm 0, ()))

#guard countBlocks (reifyFunc (Func.tailDup tinyJnzLatchLoop)) ==
  countBlocks (reifyFunc tinyJnzLatchLoop)
#guard countBlocks (reifyFunc (Func.tailDup tinyJnzLatchLoop { allowJnzLatch := true })) <
  countBlocks (reifyFunc tinyJnzLatchLoop)
#guard Func.checkTFlat (Func.tailDup tinyJnzLatchLoop { allowJnzLatch := true }) == true

/-- Non-loop `.jnz` join (does NOT target an enclosing loop header): NOT duplicated even when
`allowJnzLatch = true` under `requireLoopHdr = true`. -/
def nonLoopJnzBlock : Func [.bool, i64] [i64] := fun _ _ (c, x, ()) =>
  .group (sig := [[i64], [i64], [i64]])
    (fun (_, exit1, exit2, ()) =>
      .cons (fun (v, ()) =>
        .let_ (op2 (.ne i64) (.var v) (.imm 0)) fun (nz, ()) =>
        .jnz (.var nz) (.jump exit1 (.var v, ())) (.jump exit2 (.var v, ())))
      (.cons (fun (a, ()) =>
        .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (a1, ()) =>
        .let_ (op2 (.xor i64) (.var a1) (.imm 2)) fun (a2, ()) =>
        .let_ (op2 (.add i64) (.var a2) (.imm 3)) fun (a3, ()) =>
        .ret (.var a3, ()))
      (.cons (fun (b, ()) =>
        .let_ (op2 (.add i64) (.var b) (.imm 3)) fun (b1, ()) =>
        .let_ (op2 (.xor i64) (.var b1) (.imm 5)) fun (b2, ()) =>
        .let_ (op2 (.sub i64) (.var b2) (.imm 1)) fun (b3, ()) =>
        .ret (.var b3, ())) .nil)))
    (fun (J, _, _, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (x1, ()) => .jump J (.var x1, ()))
        (.let_ (op2 (.sub i64) (.var x) (.imm 1)) fun (x2, ()) => .jump J (.var x2, ())))

#guard countBlocks (reifyFunc (Func.tailDup nonLoopJnzBlock { allowJnzLatch := true })) ==
  countBlocks (reifyFunc nonLoopJnzBlock)

/-- `4`-instruction `.jnz` loop latch exceeds `maxLatchInstrs := 3` and is NOT duplicated. -/
def fourInstrJnzLatch : Func [.bool, i64] [i64] := fun _ _ (c, x, ()) =>
  .group (sig := [[i64, i64], [i64]])
    (fun (hdr, exitB, ()) =>
      .cons (fun (i, acc, ()) =>
        .group (sig := [[i64, i64]])
          (fun _ =>
            .cons (fun (li, lacc, ()) =>
              .let_ (op2 (.sub i64) (.var li) (.imm 1)) fun (i1, ()) =>
              .let_ (op2 (.add i64) (.var lacc) (.imm 5)) fun (acc1, ()) =>
              .let_ (op2 (.xor i64) (.var acc1) (.imm 3)) fun (acc2, ()) =>
              .let_ (op2 (.ne i64) (.var i1) (.imm 0)) fun (nz, ()) =>
              .jnz (.var nz)
                (.jump hdr (.var i1, .var acc2, ()))
                (.jump exitB (.var acc2, ()))) .nil)
          (fun (latch, ()) =>
            .jnz (.var c)
              (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (a1, ()) =>
                .jump latch (.var i, .var a1, ()))
              (.let_ (op2 (.add i64) (.var acc) (.imm 2)) fun (a2, ()) =>
                .jump latch (.var i, .var a2, ()))))
      (.cons (fun (r, ()) =>
        .let_ (op2 (.add i64) (.var r) (.imm 1)) fun (r1, ()) =>
        .let_ (op2 (.xor i64) (.var r1) (.imm 2)) fun (r2, ()) =>
        .let_ (op2 (.add i64) (.var r2) (.imm 3)) fun (r3, ()) =>
        .ret (.var r3, ())) .nil))
    (fun (hdr, _, ()) => .jump hdr (.var x, .imm 0, ()))

#guard countBlocks (reifyFunc (Func.tailDup fourInstrJnzLatch { allowJnzLatch := true })) ==
  countBlocks (reifyFunc fourInstrJnzLatch)

/-- `4`-predecessor `.jnz` loop latch exceeds `maxLatchPreds := 3` and is NOT duplicated. -/
def fourPredJnzLatch : Func [i64, i64] [i64] := fun _ _ (tag, x, ()) =>
  .group (sig := [[i64, i64], [i64]])
    (fun (hdr, exitB, ()) =>
      .cons (fun (i, acc, ()) =>
        .group (sig := [[i64, i64]])
          (fun _ =>
            .cons (fun (li, lacc, ()) =>
              .let_ (op2 (.sub i64) (.var li) (.imm 1)) fun (i', ()) =>
              .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (nz, ()) =>
              .jnz (.var nz)
                (.jump hdr (.var i', .var lacc, ()))
                (.jump exitB (.var lacc, ()))) .nil)
          (fun (latch, ()) =>
            .let_ (op2 (.eq i64) (.var tag) (.imm 0)) fun (c0, ()) =>
            .jnz (.var c0) (.jump latch (.var i, .var acc, ()))
              (.let_ (op2 (.eq i64) (.var tag) (.imm 1)) fun (c1, ()) =>
               .jnz (.var c1)
                 (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (a1, ()) =>
                   .jump latch (.var i, .var a1, ()))
                 (.let_ (op2 (.eq i64) (.var tag) (.imm 2)) fun (c2, ()) =>
                  .jnz (.var c2)
                    (.let_ (op2 (.add i64) (.var acc) (.imm 2)) fun (a2, ()) =>
                      .jump latch (.var i, .var a2, ()))
                    (.let_ (op2 (.add i64) (.var acc) (.imm 3)) fun (a3, ()) =>
                      .jump latch (.var i, .var a3, ()))))))
      (.cons (fun (r, ()) =>
        .let_ (op2 (.add i64) (.var r) (.imm 1)) fun (r1, ()) =>
        .let_ (op2 (.xor i64) (.var r1) (.imm 2)) fun (r2, ()) =>
        .let_ (op2 (.add i64) (.var r2) (.imm 3)) fun (r3, ()) =>
        .ret (.var r3, ())) .nil))
    (fun (hdr, _, ()) => .jump hdr (.var x, .imm 0, ()))

#guard countBlocks (reifyFunc (Func.tailDup fourPredJnzLatch { allowJnzLatch := true })) ==
  countBlocks (reifyFunc fourPredJnzLatch)

/-! ## 3. Formal Soundness Proofs (`Wf`, `Func.spec`, `callsOk`) -/

theorem wideBoolSplit10_wf : wideBoolSplit10.Wf := by t_wf_reify

theorem wideBoolSplit10_spec (Γ : Env) (c : Bool) (y : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ wideBoolSplit10 (c, y, ()) m
      (fun (r, ()) m' => m' = m ∧ r = if c then y + 1 else y - 1) X := by
  dsimp only [Func.spec, Func.wp, wideBoolSplit10]
  intro (J, ()) hClosed
  have hJ : ∀ b : Bool,
      b = c → J (0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, b, y, ()) m := by
    intro b hb
    apply hClosed.1 (0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, b, y, ()) m
    dsimp only [wp, Op.wp, op2, vals, Arg.val, OpCode.wp_add, OpCode.wp_sub, lift2,
      Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq]
    rw [← hb]
    cases b <;> simp
  dsimp only [wp, vals, Arg.val]
  exact ⟨fun hc => hJ true (by simp [hc]), fun hc => hJ false (by simp [hc])⟩

theorem wideBoolSplit10_ct_spec (Γ : Env) (c : Bool) (y : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.condThreadOpt wideBoolSplit10) (c, y, ()) m
      (fun (r, ()) m' => m' = m ∧ r = if c then y + 1 else y - 1) X :=
  condThread_ok wideBoolSplit10_wf (wideBoolSplit10_spec Γ c y m X)

theorem wideBoolSplit10_callsOk :
    ((Func.condThreadOpt wideBoolSplit10) (fun _ => Unit) (fun _ => Unit) (Tup.units _)).callsOk
      [] [] :=
  Func.condThreadOpt_callsOk wideBoolSplit10_wf (by
    simp [wideBoolSplit10, Expr.callsOk, Blocks.callsOk])

theorem groupHeadBoolSplit_wf : groupHeadBoolSplit.Wf := by t_wf_reify
theorem groupHeadBoolSplit_ct_wf : (Func.condThreadOpt groupHeadBoolSplit).Wf :=
  Func.condThreadOpt_wf groupHeadBoolSplit_wf
theorem groupHeadBoolSplit_ct_callsOk :
    ((Func.condThreadOpt groupHeadBoolSplit) (fun _ => Unit) (fun _ => Unit)
      (Tup.units _)).callsOk [] [] :=
  Func.condThreadOpt_callsOk groupHeadBoolSplit_wf (by
    simp [groupHeadBoolSplit, Expr.callsOk, Blocks.callsOk])

theorem tinyJnzLatchLoop_wf : tinyJnzLatchLoop.Wf := by t_wf_reify
theorem tinyJnzLatchLoop_td_wf :
    (Func.tailDup tinyJnzLatchLoop { allowJnzLatch := true }).Wf :=
  Func.tailDup_wf tinyJnzLatchLoop_wf { allowJnzLatch := true }

/-! ## 4. `Kissat.Plain` Activation `#guard`s (`plain_prop_lit`, `plain_analyze_rsn`) -/

meta def plainTargetFns : List Fn :=
  let m := LeanQbe.T.Examples.Kissat.Plain.plainModule
  (m.optInlinePolicy {}).fns.filter
    fun f => ["plain_prop_lit", "plain_analyze_rsn"].contains f.name

meta def findPlainFn? (nm : String) : Option Fn :=
  plainTargetFns.find? (·.name == nm)

meta def flatCompileX64Lines (f : Fn) : Except String (List String) := do
  let dirs ← Driver.compileFnFlat x64Target.toIsa x64LegalTarget f
  pure ((toATTAligned dirs).splitOn "\n")

meta def countX64Insns (lines : List String) : Nat :=
  lines.foldl (fun acc l =>
    let s := l.trimAscii.toString
    if s.isEmpty || s.startsWith "." || s.endsWith ":" then acc else acc + 1) 0

meta def countX64SpSt (lines : List String) : Nat :=
  lines.foldl (fun acc l =>
    let s := l.trimAscii.toString
    if s.contains ", " && s.endsWith "(%rsp)" then acc + 1 else acc) 0

meta def midCheckIr (lt : LegalTarget) (f : Fn) : Bool × Nat × Nat :=
  let ff := Driver.toFlatFn f
  let ef := earlyOptFlat ff
  let mf := midStageFlat lt ef
  (mf.wfCheck, tflatSize mf.body, countJnz mf.body)

#guard match findPlainFn? "plain_prop_lit" with
  | some f =>
    let (okX, nodesX, jnzX) := midCheckIr LegalTarget.x64 f
    let (okA, nodesA, jnzA) := midCheckIr LegalTarget.aarch64 f
    match flatCompileX64Lines f with
    | .ok lines =>
      okX && okA && nodesX ≤ 321 && jnzX ≤ 36 && nodesA ≤ 321 && jnzA ≤ 36 &&
        countX64Insns lines ≤ 319 && countX64SpSt lines ≤ 23
    | .error _ => false
  | none => false

#guard match findPlainFn? "plain_analyze_rsn" with
  | some f =>
    let (okX, _, _) := midCheckIr LegalTarget.x64 f
    let (okA, _, _) := midCheckIr LegalTarget.aarch64 f
    match flatCompileX64Lines f with
    | .ok lines => okX && okA && countX64Insns lines ≤ 90
    | .error _ => false
  | none => false

#eval show IO Unit from do
  for nm in ["plain_prop_lit", "plain_analyze_rsn"] do
    if let some f := findPlainFn? nm then
      let (_, nX, jX) := midCheckIr LegalTarget.x64 f
      let (_, nA, jA) := midCheckIr LegalTarget.aarch64 f
      let lines ← IO.ofExcept (flatCompileX64Lines f)
      let xIns := countX64Insns lines
      let xSp := countX64SpSt lines
      IO.println s!"[W6.1-A {nm}] irX=({nX},{jX}) irA=({nA},{jA}) x64Ins={xIns} spSt={xSp}"

/-! ## 5. Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbeTest.T.OptW61CfgThreadDupTest.wideBoolSplit10_ct_spec
#print axioms LeanQbeTest.T.OptW61CfgThreadDupTest.wideBoolSplit10_callsOk
#print axioms LeanQbeTest.T.OptW61CfgThreadDupTest.groupHeadBoolSplit_ct_wf
#print axioms LeanQbeTest.T.OptW61CfgThreadDupTest.groupHeadBoolSplit_ct_callsOk
#print axioms LeanQbeTest.T.OptW61CfgThreadDupTest.tinyJnzLatchLoop_td_wf
#print axioms LeanQbe.T.OptFlatBranch.condThreadPassFlat_eq
#print axioms LeanQbe.T.OptFlatBranch.tailDupFlat_eq

end LeanQbeTest.T.OptW61CfgThreadDupTest