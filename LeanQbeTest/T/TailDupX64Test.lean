module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.TailDupLemmas
public import LeanQbe.T.Spill
public import LeanQbe.T.Main
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.TailDup
meta import LeanQbe.T.Spill
meta import LeanQbe.T.Main
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbeTest.T.RegaTestKit

/-!
# Downstream x86-64 (`x64Target`) Lowering Tests for `LeanQbe.T.TailDup`

Verifies end-to-end compilation (`Rega.lowerFn` + `checkCompile`) through `x64Target`
for `Fn.tailDup` on loop-latch trampolines, multi-predecessor exit joins, 2-hop chains,
and touched Kissat `FullM7Fidelity` functions, checking strict reduction in emitted x64
unconditional `jmp` and `.label` directives.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.TailDupX64Test

open LeanQbe.T LeanQbe.T.Amd64
open LeanQbeTest.T.RegaTestKit
open LeanQbe.T.Examples.Kissat.FullM7Fidelity

/-! ## Helpers -/

meta def hintsOfLeg (f : Fn) : x64Target.toIsa.Hints :=
  Spill.hints x64Target.toIsa f

meta def chkLeg (f : Fn) : Bool :=
  let lf := f.legal x64LegalTarget
  let h := hintsOfLeg lf
  match Rega.lowerFn x64Target.toIsa h lf.ext lf,
      checkAndBoundMid x64Target.toIsa x64Target.frame.raBytes [] 0 [] h lf with
  | .ok c, some b =>
    b ≤ 2048 && checkCompile x64Target x64Layout x64LegalTarget [] [] 0 [f]
      [Fn.computeHints x64Target.toIsa x64LegalTarget f] 2048 && !c.isEmpty
  | _, _ => false

meta def codeOfLeg (f : Fn) : List x64Target.toIsa.Directive :=
  let h := hintsOfLeg f
  match Rega.lowerFn x64Target.toIsa h f.ext f with
  | .ok c => c
  | .error _ => []

meta def isJmpDir : Directive → Bool
  | .instr (.regular _ _ (.jmp _)) => true
  | _ => false

meta def isLabelDir : Directive → Bool
  | .label _ => true
  | _ => false

/-! ## Synthetic Trampoline Fixtures -/

def loopLatchFn : Fn :=
  ⟨"td_loop_latch_x64", [i64], [i64], fun _ _ (n, ()) =>
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
  ⟨"td_ret_join_x64", [.bool, i64, i64], [i64], fun _ _ (c, x, y, ()) =>
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
  ⟨"td_chain_x64", [.bool, i64], [i64], fun _ _ (c, n, ()) =>
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

/-! ## x64 Lowering & Codegen Assertions -/

#guard chkLeg loopLatchFn
#guard chkLeg (Fn.tailDup loopLatchFn)
#guard chkLeg retJoinFn
#guard chkLeg (Fn.tailDup retJoinFn)
#guard chkLeg chainFn
#guard chkLeg (Fn.tailDup chainFn)

#guard countDirs isJmpDir (codeOfLeg (Fn.tailDup (loopLatchFn.legal x64LegalTarget))) <
  countDirs isJmpDir (codeOfLeg (loopLatchFn.legal x64LegalTarget))
#guard countDirs isLabelDir (codeOfLeg (Fn.tailDup (loopLatchFn.legal x64LegalTarget))) <
  countDirs isLabelDir (codeOfLeg (loopLatchFn.legal x64LegalTarget))

#guard countDirs isJmpDir (codeOfLeg (Fn.tailDup (retJoinFn.legal x64LegalTarget))) <
  countDirs isJmpDir (codeOfLeg (retJoinFn.legal x64LegalTarget))
#guard countDirs isLabelDir (codeOfLeg (Fn.tailDup (retJoinFn.legal x64LegalTarget))) <
  countDirs isLabelDir (codeOfLeg (retJoinFn.legal x64LegalTarget))

#guard countDirs isJmpDir (codeOfLeg (Fn.tailDup (chainFn.legal x64LegalTarget))) ≤
  countDirs isJmpDir (codeOfLeg (chainFn.legal x64LegalTarget))
#guard countDirs isLabelDir (codeOfLeg (Fn.tailDup (chainFn.legal x64LegalTarget))) <
  countDirs isLabelDir (codeOfLeg (chainFn.legal x64LegalTarget))

/-! ## Kissat `FullM7Fidelity` Sample `Rega.lowerFn` x64 Verification -/

meta def fidSampleNames : List String :=
  ["kissat_skip_ws1", "full_clear_ana", "full_sort_tmp"]

meta def fidSampleFns : List Fn :=
  m7FidelityFns.filter fun f => fidSampleNames.contains f.name

meta def lowersX64 (f : Fn) : Bool :=
  let h := Spill.hints x64Target.toIsa f
  match Rega.lowerFn x64Target.toIsa h f.ext f with
  | .ok _ => true
  | .error _ => false

meta def x64JmpCount (f : Fn) : Nat :=
  let h := Spill.hints x64Target.toIsa f
  match Rega.lowerFn x64Target.toIsa h f.ext f with
  | .ok ds => countDirs isJmpDir ds
  | .error _ => 0

#guard fidSampleFns.length == 3
#guard fidSampleFns.all fun f =>
  let mf := f.mid x64LegalTarget
  let td := Fn.tailDup mf
  lowersX64 td && x64JmpCount td ≤ x64JmpCount mf

#eval show IO Unit from do
  for f in fidSampleFns do
    let mf := f.mid x64LegalTarget
    let td := Fn.tailDup mf
    IO.println s!"[x64] {f.name}: jmps {x64JmpCount mf}->{x64JmpCount td}"

/-! ## Axiom Audit -/

theorem tailDupX64_wf : (Fn.tailDup loopLatchFn).Wf :=
  Fn.tailDup_wf (by t_wf_reify)

#print axioms tailDupX64_wf

end LeanQbeTest.T.TailDupX64Test
