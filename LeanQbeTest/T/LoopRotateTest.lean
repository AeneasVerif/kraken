module

public import LeanQbe.T.LoopRotateLemmas
public import LeanQbe.T.Opt
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.Kissat.Full
meta import LeanQbe.T.LoopRotate
meta import LeanQbe.T.Opt
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Tests of `LeanQbe.T.LoopRotate` (`Fable Track C4`)

Covers:
1. Exact kernel-checked (`t_kernel_rfl`) loop rotation on `dir = true` (`sumWhileLoop`),
   `dir = false` (`exitTrueLoop`), multi-step `.let_` headers projecting out dead temporaries,
   `ExitMode.wrap` large exit blocks with dead parameter pruning, and multi-back-edge tail loops.
2. Heuristic rejection & safety fallbacks: `.load` header under `allowLoadHdr = false` vs `true`,
   non-tail-majority loop (`readLeb128`-style), `.group` inside header, over-budget header,
   and adversarial invalid `RotPlan` rejection via `Func.loopRotateWithPlan`.
3. End-to-end `Wf`, `Func.wp`/`Func.spec` (`sumWhileLoop` arbitrary `n` + `n = 0`),
   `Expr.callsOk`, and `Fn.loopRotate_{wf,spec,callsOk}` proofs.
4. Real-corpus validation (`checkTFlat = true` and rotation trigger checks) across all 6
   `LratBytes` functions and all 166 `Kissat.Full` functions.
5. `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.LoopRotateTest

open LeanQbe.T
open LeanQbe.T.LoopRotate
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full

/-! ## 1. Standard `while` loop (`dir = true`, `.inline` exit) -/

/-- `while (i != 0) { acc += i; i--; }` header-tested loop (`dir = true`). -/
def sumWhileLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ()))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem sumWhileLoop_plan_check :
    (buildRotPlan (as := [i64]) defaultRotConfig (reifyFunc sumWhileLoop)).hasRot = true := by
  t_kernel_rfl

theorem sumWhileLoop_rot_out : Func.loopRotate sumWhileLoop = fun _ _ (n, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopRot, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
        .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
        .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c1, ()) =>
        .jnz (.var c1)
          (.jump loopRot (.var i', .var acc', ()))
          (.ret (.var acc', ()))) .nil)
      (fun (loopRot, ()) =>
        .let_ (op2 (.ne i64) (.var n) (.imm 0)) fun (c0, ()) =>
        .jnz (.var c0) (.jump loopRot (.var n, .imm 0, ())) (.ret (.imm 0, ()))) := by
  t_kernel_rfl

theorem sumWhileLoop_wf : sumWhileLoop.Wf := by t_wf_reify
theorem sumWhileLoop_rot_wf : (Func.loopRotate sumWhileLoop).Wf :=
  Func.loopRotate_wf sumWhileLoop_wf
theorem sumWhileLoop_rot_checkTFlat : Func.checkTFlat (Func.loopRotate sumWhileLoop) = true := by
  t_kernel_rfl

theorem sumWhileLoop_rot_zero_spec (Γ : Env) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.loopRotate sumWhileLoop) (0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) X := by
  rw [sumWhileLoop_rot_out]
  dsimp only [Func.spec, Func.wp]
  simp only [wp]
  intro _ _
  wp_unfold
  simp [Op.wp, OpCode.wp, liftCmp, CmpOp.evalBits, vals, Arg.val]

theorem sumWhileLoop_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ sumWhileLoop (n, ()) m
      (fun (r, ()) m' => 2 * r.toNat % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64 ∧ m' = m)
      X := by
  dsimp only [Func.spec, Func.wp, sumWhileLoop]
  refine wp_loop1 _ _
    (fun k (x : Tup Val [i64, i64]) m' =>
      x.1.toNat = k ∧ m' = m ∧
      (2 * x.2.1.toNat + k * (k + 1)) % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64)
    ?_ ?_
  · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
    dsimp only at hk hinv
    wp_unfold
    by_cases hz : i = 0
    · subst hz
      simp at hk
      subst hk
      simp only [true_implies, not_true_eq_false, false_implies, true_and]
      simpa using hinv
    · have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [hz, false_implies, not_false_eq_true, true_implies, and_true]
      refine hJ (k - 1) _ m' (by omega) ?_
      have hsub : (i - 1).toNat = i.toNat - 1 :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
      refine ⟨by dsimp only; rw [hsub]; omega, rfl, ?_⟩
      dsimp only
      have hmod : (acc + i).toNat = (acc.toNat + i.toNat) % 2 ^ 64 := BitVec.toNat_add acc i
      have hk1 : (k - 1) * (k - 1 + 1) + 2 * i.toNat = k * (k + 1) := by
        have hkpos : k ≥ 1 := by omega
        have hkm : k - 1 + 1 = k := by omega
        rw [hkm, hk]
        calc (k - 1) * k + 2 * k = (k - 1 + 2) * k := by rw [Nat.add_mul]
          _ = (k + 1) * k := by congr 1; omega
          _ = k * (k + 1) := Nat.mul_comm _ _
      rw [hmod]
      calc (2 * ((acc.toNat + i.toNat) % 2 ^ 64) + (k - 1) * (k - 1 + 1)) % 2 ^ 64
          = (2 * (acc.toNat + i.toNat) + (k - 1) * (k - 1 + 1)) % 2 ^ 64 := by
              rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
        _ = (2 * acc.toNat + ((k - 1) * (k - 1 + 1) + 2 * i.toNat)) % 2 ^ 64 := by
              congr 1; omega
        _ = (2 * acc.toNat + k * (k + 1)) % 2 ^ 64 := by rw [hk1]
        _ = (n.toNat * (n.toNat + 1)) % 2 ^ 64 := hinv
  · intro J hJ
    wp_unfold
    exact hJ n.toNat (n, 0#64, ()) m ⟨rfl, rfl, by simp⟩

theorem sumWhileLoop_rot_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.loopRotate sumWhileLoop) (n, ()) m
      (fun (r, ()) m' => 2 * r.toNat % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64 ∧ m' = m)
      X :=
  Func.loopRotate_spec sumWhileLoop_wf defaultRotConfig (sumWhileLoop_spec Γ n m X)

theorem sumWhileLoop_rot_correct (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.wp Γ (Func.loopRotate sumWhileLoop) (n, ()) m
      (fun (r, ()) m' => 2 * r.toNat % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64 ∧ m' = m)
      X :=
  Func.loopRotate_correct sumWhileLoop_wf defaultRotConfig (sumWhileLoop_spec Γ n m X)

/-! ## 2. `dir = false`, multi-step masked headers, `ExitMode.wrap`, and multi-back-edge -/

/-- Header tests `i == 0` and exits on the `true` arm (`dir = false`). -/
def exitTrueLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem exitTrueLoop_rot_out : Func.loopRotate exitTrueLoop = fun _ _ (n, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopRot, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
        .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
        .let_ (op2 (.eq i64) (.var i') (.imm 0)) fun (z1, ()) =>
        .jnz (.var z1) (.ret (.var acc', ()))
          (.jump loopRot (.var i', .var acc', ()))) .nil)
      (fun (loopRot, ()) =>
        .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (z0, ()) =>
        .jnz (.var z0) (.ret (.imm 0, ())) (.jump loopRot (.var n, .imm 0, ()))) := by
  t_kernel_rfl

theorem exitTrueLoop_wf : exitTrueLoop.Wf := by t_wf_reify
theorem exitTrueLoop_rot_wf : (Func.loopRotate exitTrueLoop).Wf :=
  Func.loopRotate_wf exitTrueLoop_wf
theorem exitTrueLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate exitTrueLoop) = true := by
  t_kernel_rfl

/-- Multi-step `.let_` header where intermediate `step1` is live in `cont` and `c` is dead. -/
def twoStepHdrLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (iPlus1, ()) =>
      .let_ (op2 (.ne i64) (.var iPlus1) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var acc) (.var iPlus1)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ()))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem twoStepHdrLoop_rot_out : Func.loopRotate twoStepHdrLoop = fun _ _ (n, ()) =>
    .group (sig := [[i64, i64, i64]])
      (fun (loopRot, ()) => .cons (fun (p, i, acc, ()) =>
        .let_ (op2 (.add i64) (.var acc) (.var p)) fun (acc', ()) =>
        .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
        .let_ (op2 (.add i64) (.var i') (.imm 1)) fun (p', ()) =>
        .let_ (op2 (.ne i64) (.var p') (.imm 0)) fun (c1, ()) =>
        .jnz (.var c1)
          (.jump loopRot (.var p', .var i', .var acc', ()))
          (.ret (.var acc', ()))) .nil)
      (fun (loopRot, ()) =>
        .let_ (op2 (.add i64) (.var n) (.imm 1)) fun (p0, ()) =>
        .let_ (op2 (.ne i64) (.var p0) (.imm 0)) fun (c0, ()) =>
        .jnz (.var c0) (.jump loopRot (.var p0, .var n, .imm 0, ())) (.ret (.imm 0, ()))) := by
  t_kernel_rfl

theorem twoStepHdrLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate twoStepHdrLoop) = true := by
  t_kernel_rfl

/-- Large exit arm (`> inlineExitMax = 3`) with dead loop parameter `deadP` -> `ExitMode.wrap`
factored exit block dropping `deadP` and dead header boolean. -/
def wrapExitLoop : Func [i64, i64] [i64] := fun _ _ (n, k, ()) =>
  loop1 (ts := [i64, i64, i64])
    (fun loop (i, acc, _deadP, ()) =>
      .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var acc) (.var k)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', .var k, ()))
        (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (e1, ()) =>
         .let_ (op2 (.xor i64) (.var e1) (.imm 3)) fun (e2, ()) =>
         .let_ (op2 (.add i64) (.var e2) (.imm 5)) fun (e3, ()) =>
         .let_ (op2 (.sub i64) (.var e3) (.var k)) fun (e4, ()) =>
         .ret (.var e4, ())))
    (fun loop => .jump loop (.var n, .imm 0, .var k, ()))

theorem wrapExitLoop_plan_is_wrap :
    (match buildRotPlan (as := [i64, i64]) defaultRotConfig (reifyFunc wrapExitLoop) with
     | .groupRot _ _ _ (.wrap _ _) _ _ _ => true
     | _ => false) = true := by
  t_kernel_rfl

theorem wrapExitLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate wrapExitLoop) = true := by
  t_kernel_rfl

theorem wrapExitLoop_rot_wf : (Func.loopRotate wrapExitLoop).Wf :=
  Func.loopRotate_wf (by t_wf_reify)

/-- Multi-back-edge tail loop with external `call` preserving `callsOk`. -/
def multiBackCallLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.and i64) (.var i) (.imm 1)) fun (m1, ()) =>
         .let_ (op2 (.ne i64) (.var m1) (.imm 0)) fun (odd, ()) =>
         .jnz (.var odd)
           (.call "tick" (as := [i64]) (bs := [i64]) (.var i, ()) fun (v, ()) =>
            .let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc', ()) =>
            .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump loop (.var i', .var acc', ()))
           (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump loop (.var i', .var acc, ())))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem multiBackCallLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate multiBackCallLoop) = true := by
  t_kernel_rfl

theorem multiBackCallLoop_callsOk :
    let allowed : List SigEntry := [("tick", [i64], [i64])]
    let f := Func.loopRotate multiBackCallLoop
    (f (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])).callsOk allowed [] := by
  refine Func.loopRotate_callsOk (by t_wf_reify) defaultRotConfig ?_
  simp [multiBackCallLoop, loop1, Expr.callsOk, Blocks.callsOk]

/-! ## 3. Config gates, negative heuristic cases, and adversarial invalid `RotPlan`s -/

/-- `.load` header is skipped under `defaultRotConfig` (`allowLoadHdr = false`) and rotated
under `{ allowLoadHdr := true }`. -/
def loadHdrLoop : Func [i64, i64] [i64] := fun _ _ (n, ptr, ()) =>
  loop1 (ts := [i64])
    (fun loop (acc, ()) =>
      .load i64 (.var ptr) fun v =>
      .let_ (op2 (.ne i64) (.var v) (.var acc)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (acc', ()) =>
         .jump loop (.var acc', ()))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var n, ()))

theorem loadHdrLoop_default_noRot :
    (buildRotPlan (as := [i64, i64]) defaultRotConfig (reifyFunc loadHdrLoop)).hasRot = false := by
  t_kernel_rfl

theorem loadHdrLoop_allowLoad_rot :
    (buildRotPlan (as := [i64, i64]) { allowLoadHdr := true }
      (reifyFunc loadHdrLoop)).hasRot = true := by
  t_kernel_rfl

theorem loadHdrLoop_allowLoad_checkTFlat :
    Func.checkTFlat (Func.loopRotate loadHdrLoop { allowLoadHdr := true }) = true := by
  t_kernel_rfl

/-- `condJumps`-majority loop is skipped under `requireTailMajority = true`. -/
def condJumpsMajLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .let_ (op2 (.and i64) (.var i) (.imm 1)) fun (m1, ()) =>
         .let_ (op2 (.ne i64) (.var m1) (.imm 0)) fun (b1, ()) =>
         .jnz (.var b1) (.jump loop (.var i', .var acc, ())) (.ret (.var acc, ())))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem condJumpsMajLoop_noRot :
    (buildRotPlan (as := [i64]) defaultRotConfig
      (reifyFunc condJumpsMajLoop)).hasRot = false := by
  t_kernel_rfl

theorem condJumpsMajLoop_allowCond_rot :
    (buildRotPlan (as := [i64]) { requireTailMajority := false }
      (reifyFunc condJumpsMajLoop)).hasRot = true := by
  t_kernel_rfl

/-- Budget cap (`dupBudget := 1`) rejects rotation cleanly. -/
theorem sumWhileLoop_tinyBudget_noRot :
    (buildRotPlan (as := [i64]) { dupBudget := 1 }
      (reifyFunc sumWhileLoop)).hasRot = false := by
  t_kernel_rfl

/-- Adversarial invalid `RotPlan` (claiming dead param / flipped `dir` where exit jumps to loop /
wrong header op) are all safely rejected by `Func.loopRotateWithPlan` without modifying `f`. -/
def badPlanWrongDir : RotPlan :=
  .groupRot false [.let_ [.bool]] [[]] .inline .leaf .leaf .leaf

def badPlanWrongDead : RotPlan :=
  .groupRot true [.let_ [.bool]] [[false]] .inline .leaf .leaf .leaf

def badPlanBadHdr : RotPlan :=
  .groupRot true [.load i64] [[]] .inline .leaf .leaf .leaf

theorem badPlanWrongDir_noop :
    Func.loopRotateWithPlan badPlanWrongDir sumWhileLoop = sumWhileLoop := by
  t_kernel_rfl

theorem badPlanWrongDead_noop :
    Func.loopRotateWithPlan badPlanWrongDead twoStepHdrLoop = twoStepHdrLoop := by
  t_kernel_rfl

theorem badPlanBadHdr_noop :
    Func.loopRotateWithPlan badPlanBadHdr sumWhileLoop = sumWhileLoop := by
  t_kernel_rfl

/-- Nested inner loop whose small (`size = 1`, `noGroup = true`) `exitArm` jumps directly to an
enclosing loop must still force `ExitMode.wrap` (`!(shiftJumps 1 exitInfo.jumps).isEmpty`). -/
def nestedExitJumpLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64])
    (fun outer (x, ()) =>
      .let_ (op2 (.ne i64) (.var x) (.imm 0)) fun (cx, ()) =>
      .jnz (.var cx)
        (loop1 (ts := [i64])
          (fun inner (y, ()) =>
            .let_ (op2 (.ne i64) (.var y) (.imm 0)) fun (cy, ()) =>
            .jnz (.var cy)
              (.let_ (op2 (.sub i64) (.var y) (.imm 1)) fun (y', ()) =>
               .jump inner (.var y', ()))
              (.jump outer (.var x, ())))
          (fun inner => .jump inner (.var x, ())))
        (.ret (.var x, ())))
    (fun outer => .jump outer (.var n, ()))

mutual
def hasWrapGroupRot : RotPlan → Bool
  | .leaf => false
  | .letP k | .loadP k | .storeP k | .callP k => hasWrapGroupRot k
  | .jnzP t e => hasWrapGroupRot t || hasWrapGroupRot e
  | .groupKeep bs k => listHasWrapGroupRot bs || hasWrapGroupRot k
  | .groupRot _ _ _ (.wrap _ _) _ _ _ => true
  | .groupRot _ _ _ .inline c e k =>
    hasWrapGroupRot c || hasWrapGroupRot e || hasWrapGroupRot k

def listHasWrapGroupRot : List RotPlan → Bool
  | [] => false
  | p :: ps => hasWrapGroupRot p || listHasWrapGroupRot ps
end

theorem nestedExitJumpLoop_plan_forces_wrap :
    hasWrapGroupRot (buildRotPlan (as := [i64]) defaultRotConfig
      (reifyFunc nestedExitJumpLoop)) = true := by
  t_kernel_rfl

theorem nestedExitJumpLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate nestedExitJumpLoop) = true := by
  t_kernel_rfl

theorem nestedExitJumpLoop_rot_wf : (Func.loopRotate nestedExitJumpLoop).Wf :=
  Func.loopRotate_wf (by t_wf_reify)

/-! ## 4. `Fn.loopRotate` soundness & `callsOk` -/

def sumWhileFn : Fn := ⟨"sumWhile", [i64], [i64], sumWhileLoop⟩

theorem sumWhileFn_rot_sig :
    (Fn.loopRotate sumWhileFn).name = "sumWhile" ∧
      (Fn.loopRotate sumWhileFn).as = [i64] ∧
      (Fn.loopRotate sumWhileFn).rs = [i64] :=
  ⟨rfl, rfl, rfl⟩

theorem sumWhileFn_rot_wf : (Fn.loopRotate sumWhileFn).Wf :=
  Fn.loopRotate_wf sumWhileFn

theorem sumWhileFn_rot_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Fn.loopRotate sumWhileFn).body (n, ()) m
      (fun (r, ()) m' => 2 * r.toNat % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64 ∧ m' = m)
      X :=
  Fn.loopRotate_spec (fn := sumWhileFn) sumWhileLoop_wf defaultRotConfig
    (sumWhileLoop_spec Γ n m X)

theorem sumWhileFn_rot_callsOk : (Fn.loopRotate sumWhileFn).callsOk [] [] :=
  Fn.loopRotate_callsOk (fn := sumWhileFn) sumWhileLoop_wf defaultRotConfig (by
    simp [sumWhileFn, sumWhileLoop, loop1, Fn.callsOk, Expr.callsOk, Blocks.callsOk])

/-! ## 5. Pipeline integration (`Func.lateOpt`) -/

theorem sumWhile_lateOpt_out : Func.lateOpt sumWhileLoop = fun _ _ (n, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopRot, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.add i64) (.var i) (.var acc)) fun (acc', ()) =>
        .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
        .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c1, ()) =>
        .jnz (.var c1)
          (.jump loopRot (.var i', .var acc', ()))
          (.ret (.var acc', ()))) .nil)
      (fun (loopRot, ()) =>
        .let_ (op2 (.ne i64) (.var n) (.imm 0)) fun (c0, ()) =>
        .jnz (.var c0) (.jump loopRot (.var n, .imm 0, ())) (.ret (.imm 0, ()))) := by
  t_kernel_rfl

theorem sumWhile_lateOpt_wf : (Func.lateOpt sumWhileLoop).Wf :=
  Func.lateOpt_wf sumWhileLoop_wf

theorem sumWhile_lateOpt_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.lateOpt sumWhileLoop) (n, ()) m
      (fun (r, ()) m' => 2 * r.toNat % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64 ∧ m' = m)
      X :=
  Func.lateOpt_spec sumWhileLoop_wf (sumWhileLoop_spec Γ n m X)

theorem exitTrue_lateOpt_out : Func.lateOpt exitTrueLoop = fun _ _ (n, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopRot, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.add i64) (.var i) (.var acc)) fun (acc', ()) =>
        .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
        .let_ (op2 (.eq i64) (.var i') (.imm 0)) fun (z1, ()) =>
        .jnz (.var z1) (.ret (.var acc', ()))
          (.jump loopRot (.var i', .var acc', ()))) .nil)
      (fun (loopRot, ()) =>
        .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (z0, ()) =>
        .jnz (.var z0) (.ret (.imm 0, ())) (.jump loopRot (.var n, .imm 0, ()))) := by
  t_kernel_rfl

/-! ## 6. Real-corpus validation (`LratBytes` & `Kissat.Full`) -/

#guard lratBytesFns.length == 6
#guard lratBytesFns.all fun fn =>
  (Func.loopRotate (Func.earlyCore fn.body)).checkTFlat &&
    (Fn.loopRotate fn).body.checkTFlat &&
    (Func.lateOpt (Func.earlyOpt fn.body)).checkTFlat
#guard lratBytesFns.any fun fn =>
  (buildRotPlan (as := fn.as) defaultRotConfig (reifyFunc (Func.earlyCore fn.body))).hasRot

#guard fullFns.length == 166
#guard fullFns.all fun fn =>
  (Func.loopRotate (Func.earlyCore fn.body)).checkTFlat

/-! ## 7. Axiom audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Func.loopRotateWithPlan_wf
#print axioms LeanQbe.T.Func.loopRotateWithPlan_spec
#print axioms LeanQbe.T.Func.loopRotateWithPlan_callsOk
#print axioms LeanQbe.T.Func.loopRotate_wf_uncond
#print axioms LeanQbe.T.Func.loopRotate_wf
#print axioms LeanQbe.T.Func.loopRotate_spec
#print axioms LeanQbe.T.Func.loopRotate_correct
#print axioms LeanQbe.T.Func.loopRotate_callsOk
#print axioms LeanQbe.T.Fn.loopRotate_wf
#print axioms LeanQbe.T.Fn.loopRotate_spec
#print axioms LeanQbe.T.Fn.loopRotate_callsOk
#print axioms LeanQbeTest.T.LoopRotateTest.sumWhileLoop_rot_spec
#print axioms LeanQbeTest.T.LoopRotateTest.sumWhile_lateOpt_wf
#print axioms LeanQbeTest.T.LoopRotateTest.sumWhile_lateOpt_spec
#print axioms LeanQbeTest.T.LoopRotateTest.sumWhileFn_rot_callsOk
#print axioms LeanQbeTest.T.LoopRotateTest.multiBackCallLoop_callsOk

end LeanQbeTest.T.LoopRotateTest
