module

import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.TailDupLemmas
import LeanQbe.T.Spill
import LeanQbe.T.Main
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.TailDup
meta import LeanQbe.T.Spill
meta import LeanQbe.T.Main
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbeTest.T.RegaTestKit

/-!
# Downstream AArch64 (`armTarget`) Lowering Tests for `LeanQbe.T.TailDup`

AArch64 twin of `LeanQbeTest.T.TailDupX64Test`: verifies end-to-end compilation
(`Rega.lowerFn` + `checkCompile`) through `armTarget` for `Fn.tailDup` on loop-latch
trampolines, multi-predecessor exit joins, 2-hop chains, and touched Kissat
`Kissat.Plain` functions, checking strict reduction in emitted Arm64 unconditional `B`
branches and `.label` directives.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.TailDupArm64Test

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit
open LeanQbe.T.Examples.Kissat.Plain

/-! ## Helpers -/

meta def hintsOfLeg (f : Fn) : armTarget.toIsa.Hints :=
  Spill.hints armTarget.toIsa f

meta def chkLeg (f : Fn) : Bool :=
  let lf := f.legal armLegalTarget
  let h := hintsOfLeg lf
  match Rega.lowerFn armTarget.toIsa h lf.ext lf,
      checkAndBoundMid armTarget.toIsa armTarget.frame.raBytes [] 0 [] h lf with
  | .ok c, some b =>
    b ≤ 2048 && checkCompile armTarget armLayout armLegalTarget [] [] 0 [f]
      [Fn.computeHints armTarget.toIsa armLegalTarget f] 2048 && !c.isEmpty
  | _, _ => false

meta def codeOfLeg (f : Fn) : List armTarget.toIsa.Directive :=
  let h := hintsOfLeg f
  match Rega.lowerFn armTarget.toIsa h f.ext f with
  | .ok c => c
  | .error _ => []

meta def isBDir : Directive → Bool
  | .instr { operation := .B _, .. } => true
  | _ => false

meta def isLabelDir : Directive → Bool
  | .label _ => true
  | _ => false

/-! ## Synthetic Trampoline Fixtures -/

def loopLatchFn : Fn :=
  ⟨"td_loop_latch_arm", [i64], [i64], fun _ _ (n, ()) =>
    .group (sig := [[i64, i64], [i64, i64, i64]])
      (fun (latch, join, ()) =>
        .cons (fun (i, acc, ()) =>
          .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
          .jnz (.var c)
            (.let_ (op2 (.and i64) (.var i) (.imm 1)) fun (m1, ()) =>
             .let_ (op2 (.ne i64) (.var m1) (.imm 0)) fun (odd, ()) =>
             .jnz (.var odd)
               (.jump join (.var i, .var acc, .var i, ()))
               (.jump join (.var i, .var acc, .imm 1, ())))
            (.ret (.var acc, ())))
        (.cons (fun (i, acc, delta, ()) =>
          .let_ (op2 (.add i64) (.var acc) (.var delta)) fun (acc', ()) =>
          .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
          .jump latch (.var i', .var acc', ()))
        .nil))
      (fun (latch, _, ()) => .jump latch (.var n, .imm 0, ()))⟩

def retJoinFn : Fn :=
  ⟨"td_ret_join_arm", [.bool, i64, i64], [i64], fun _ _ (c, x, y, ()) =>
    .group (sig := [[i64]])
      (fun _ =>
        .cons (fun (v, ()) =>
          .let_ (op2 (.add i64) (.var v) (.imm 10)) fun (v1, ()) =>
          .let_ (op2 (.xor i64) (.var v1) (.imm 3)) fun (v2, ()) =>
          .ret (.var v2, ())) .nil)
      (fun (exitJoin, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (a, ()) =>
           .jump exitJoin (.var a, ()))
          (.let_ (op2 (.sub i64) (.var y) (.imm 1)) fun (b, ()) =>
           .jump exitJoin (.var b, ())))⟩

def chainFn : Fn :=
  ⟨"td_chain_arm", [.bool, i64], [i64], fun _ _ (c, n, ()) =>
    .group (sig := [[i64], [i64], [i64]])
      (fun (latch, b1, b2, ()) =>
        .cons (fun (i, ()) =>
          .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (nz, ()) =>
          .jnz (.var nz)
            (.jnz (.var c) (.jump b1 (.var i, ())) (.jump b2 (.var i, ())))
            (.ret (.var i, ())))
        (.cons (fun (x, ()) =>
          .let_ (op2 (.sub i64) (.var x) (.imm 1)) fun (x', ()) =>
          .jump b2 (.var x', ()))
        (.cons (fun (y, ()) =>
          .let_ (op2 (.and i64) (.var y) (.imm 0xff)) fun (y', ()) =>
          .jump latch (.var y', ()))
        .nil)))
      (fun (latch, _, _, ()) => .jump latch (.var n, ()))⟩

/-! ## Arm64 Lowering & Codegen Assertions -/

#guard chkLeg loopLatchFn
#guard chkLeg (Fn.tailDup loopLatchFn)
#guard chkLeg retJoinFn
#guard chkLeg (Fn.tailDup retJoinFn)
#guard chkLeg chainFn
#guard chkLeg (Fn.tailDup chainFn)

#guard countDirs isBDir (codeOfLeg (Fn.tailDup (loopLatchFn.legal armLegalTarget))) <
  countDirs isBDir (codeOfLeg (loopLatchFn.legal armLegalTarget))
#guard countDirs isLabelDir (codeOfLeg (Fn.tailDup (loopLatchFn.legal armLegalTarget))) <
  countDirs isLabelDir (codeOfLeg (loopLatchFn.legal armLegalTarget))

#guard countDirs isBDir (codeOfLeg (Fn.tailDup (retJoinFn.legal armLegalTarget))) <
  countDirs isBDir (codeOfLeg (retJoinFn.legal armLegalTarget))
#guard countDirs isLabelDir (codeOfLeg (Fn.tailDup (retJoinFn.legal armLegalTarget))) <
  countDirs isLabelDir (codeOfLeg (retJoinFn.legal armLegalTarget))

#guard countDirs isBDir (codeOfLeg (Fn.tailDup (chainFn.legal armLegalTarget))) ≤
  countDirs isBDir (codeOfLeg (chainFn.legal armLegalTarget))
#guard countDirs isLabelDir (codeOfLeg (Fn.tailDup (chainFn.legal armLegalTarget))) <
  countDirs isLabelDir (codeOfLeg (chainFn.legal armLegalTarget))

/-! ## Kissat `Plain` Sample `Rega.lowerFn` Arm64 Verification -/

meta def fidSampleNames : List String :=
  ["kissat_skip_ws1", "plain_clear_marks", "plain_sort_tmp"]

meta def fidSampleFns : List Fn :=
  plainFns.filter fun f => fidSampleNames.contains f.name

meta def lowersArm (f : Fn) : Bool :=
  let h := Spill.hints armTarget.toIsa f
  match Rega.lowerFn armTarget.toIsa h f.ext f with
  | .ok _ => true
  | .error _ => false

meta def armBCount (f : Fn) : Nat :=
  let h := Spill.hints armTarget.toIsa f
  match Rega.lowerFn armTarget.toIsa h f.ext f with
  | .ok ds => countDirs isBDir ds
  | .error _ => 0

#guard fidSampleFns.length == 3
#guard fidSampleFns.all fun f =>
  let mf := f.mid armLegalTarget
  let td := Fn.tailDup mf
  lowersArm td && armBCount td ≤ armBCount mf

#eval show IO Unit from do
  for f in fidSampleFns do
    let mf := f.mid armLegalTarget
    let td := Fn.tailDup mf
    IO.println s!"[arm64] {f.name}: b {armBCount mf}->{armBCount td}"

/-! ## Axiom Audit -/

theorem tailDupArm64_wf : (Fn.tailDup loopLatchFn).Wf :=
  Fn.tailDup_wf (by t_wf_reify)

#print axioms tailDupArm64_wf

end LeanQbeTest.T.TailDupArm64Test
