module

public import LeanQbe.T.TailDupLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Legal
public import LeanQbe.T.Main
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.Spill
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbeTest.T.RegaLitmusTarget
meta import LeanQbe.T.TailDup
meta import LeanQbe.T.Main
meta import LeanQbe.T.Spill
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# Targeted Unit, Soundness, `RegaLitmus`, `Kissat.Plain`, & Axiom Tests for `TailDup`

Covers:
1. Multi-predecessor join-trampoline elimination (`loopLatchTrampoline`, `retJoinTrampoline`,
   2-hop `chainTrampoline`, `loadStoreTrampoline`), verified via `t_kernel_rfl`.
2. Negative heuristic guards: `> maxPreds` (`3` preds), `> maxInstrs` (`3` instrs),
   self-recursive block, `.jnz` block, `allowMem = false`, and adversarial `DupPlan` rejection.
3. Formal `Func.Wf`, `Func.wp` / `Func.spec` refinement via `tailDup_wp` / `Func.tailDup_spec`,
   and `Func.tailDup_callsOk` / `Fn.tailDup_callsOk`.
4. `LegalTarget.{x64, aarch64}` legality and `Rega.lowerFn` + `checkCompile` on
   `RegaLitmus.litmusTarget`, verifying fewer emitted `jmp`s after `Fn.tailDup`.
5. `Kissat.Plain` (`59` functions) corpus check (`Func.checkTFlat` and static
   jump/block elimination counts).
6. `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.TailDupTest

open LeanQbe.T
open LeanQbe.T.TailDup
open LeanQbe.T.RegaLitmus
open LeanQbe.T.Examples.Kissat.Plain

/-! ## 1. Structural & Kernel-Checked Tail-Duplication Tests -/

/-- Loop with a 2-predecessor, 1-instruction latch trampoline (`join`) matching the
`Rega.lowerBlocks` layout bottleneck (`latch` has two `.jnz` arms jumping to `join`, and
`join` executes `acc + d` then jumps back to `latch`). -/
def loopLatchTrampoline : Func [i64] [i64] := fun _ _ (n, ()) =>
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
    (fun (latch, _, ()) => .jump latch (.var n, .imm 0, ()))

theorem loopLatchTrampoline_td : Func.tailDup loopLatchTrampoline = fun _ _ (n, ()) =>
    .group (sig := [[i64, i64]])
      (fun (latch, ()) =>
        .cons (fun (i, acc, ()) =>
          .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
          .jnz (.var c)
            (.let_ (op2 (.and i64) (.var i) (.imm 1)) fun (m1, ()) =>
             .let_ (op2 (.ne i64) (.var m1) (.imm 0)) fun (odd, ()) =>
             .jnz (.var odd)
               (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
                .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
                .jump latch (.var i', .var acc', ()))
               (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (acc', ()) =>
                .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
                .jump latch (.var i', .var acc', ())))
            (.ret (.var acc, ())))
        .nil)
      (fun (latch, ()) => .jump latch (.var n, .imm 0, ())) := by
  t_kernel_rfl

/-- Multi-predecessor 2-instruction `.ret` join trampoline (`exitJoin`) unwrapped completely. -/
def retJoinTrampoline : Func [.bool, i64, i64] [i64] := fun _ _ (c, x, y, ()) =>
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
         .jump exitJoin (.var b, ())))

theorem retJoinTrampoline_td : Func.tailDup retJoinTrampoline = fun _ _ (c, x, y, ()) =>
    .jnz (.var c)
      (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (a, ()) =>
       .let_ (op2 (.add i64) (.var a) (.imm 10)) fun (v1, ()) =>
       .let_ (op2 (.xor i64) (.var v1) (.imm 3)) fun (v2, ()) =>
       .ret (.var v2, ()))
      (.let_ (op2 (.sub i64) (.var y) (.imm 1)) fun (b, ()) =>
       .let_ (op2 (.add i64) (.var b) (.imm 10)) fun (v1, ()) =>
       .let_ (op2 (.xor i64) (.var v1) (.imm 3)) fun (v2, ()) =>
       .ret (.var v2, ())) := by
  t_kernel_rfl

/-- 2-hop chain of 1-instruction trampolines (`b1 -> b2 -> latch`), collapsed by `maxIters`. -/
def chainTrampoline : Func [.bool, i64] [i64] := fun _ _ (c, n, ()) =>
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
    (fun (latch, _, _, ()) => .jump latch (.var n, ()))

theorem chainTrampoline_td : Func.tailDup chainTrampoline = fun _ _ (c, n, ()) =>
    .group (sig := [[i64]])
      (fun (latch, ()) =>
        .cons (fun (i, ()) =>
          .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (nz, ()) =>
          .jnz (.var nz)
            (.jnz (.var c)
              (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (x', ()) =>
               .let_ (op2 (.and i64) (.var x') (.imm 0xff)) fun (y', ()) =>
               .jump latch (.var y', ()))
              (.let_ (op2 (.and i64) (.var i) (.imm 0xff)) fun (y', ()) =>
               .jump latch (.var y', ())))
            (.ret (.var i, ())))
        .nil)
      (fun (latch, ()) => .jump latch (.var n, ())) := by
  t_kernel_rfl

/-- Memory-op join block (`load` + `add`) duplicated under `allowMem = true`, preserved when
`allowMem = false`. -/
def loadJoinTrampoline : Func [.bool, i64, i64] [i64] := fun _ _ (c, p1, p2, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (p, ()) =>
        .load i64 (.var p) fun v =>
        .let_ (op2 (.add i64) (.var v) (.imm 1)) fun (r, ()) =>
        .ret (.var r, ())) .nil)
    (fun (J, ()) => .jnz (.var c) (.jump J (.var p1, ())) (.jump J (.var p2, ())))

theorem loadJoinTrampoline_mem_on :
    Func.tailDup loadJoinTrampoline = fun _ _ (c, p1, p2, ()) =>
      .jnz (.var c)
        (.load i64 (.var p1) fun v =>
         .let_ (op2 (.add i64) (.var v) (.imm 1)) fun (r, ()) =>
         .ret (.var r, ()))
        (.load i64 (.var p2) fun v =>
         .let_ (op2 (.add i64) (.var v) (.imm 1)) fun (r, ()) =>
         .ret (.var r, ())) := by
  t_kernel_rfl

theorem loadJoinTrampoline_mem_off :
    reifyFunc (Func.tailDup loadJoinTrampoline { allowMem := false }) =
      reifyFunc loadJoinTrampoline := by
  t_kernel_rfl

/-! ## 2. Negative Heuristic Guards & Adversarial Plan Rejection -/

/-- `3`-predecessor join block exceeds `maxPreds = 2` and is NOT duplicated. -/
def threePredJoin : Func [i64, i64] [i64] := fun _ _ (x, y, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (v, ()) =>
        .let_ (op2 (.add i64) (.var v) (.imm 1)) fun (r, ()) =>
        .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (c0, ()) =>
      .jnz (.var c0) (.jump J (.var y, ()))
        (.let_ (op2 (.eq i64) (.var x) (.imm 1)) fun (c1, ()) =>
         .jnz (.var c1) (.jump J (.var x, ())) (.jump J (.imm 7, ()))))

theorem threePredJoin_keep :
    reifyFunc (Func.tailDup threePredJoin) = reifyFunc threePredJoin := by
  t_kernel_rfl

/-- `3`-instruction join block exceeds `maxInstrs = 2` and is NOT duplicated. -/
def threeInstrJoin : Func [.bool, i64, i64] [i64] := fun _ _ (c, x, y, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (v, ()) =>
        .let_ (op2 (.add i64) (.var v) (.imm 1)) fun (a, ()) =>
        .let_ (op2 (.xor i64) (.var a) (.imm 2)) fun (b, ()) =>
        .let_ (op2 (.add i64) (.var b) (.imm 3)) fun (r, ()) =>
        .ret (.var r, ())) .nil)
    (fun (J, ()) => .jnz (.var c) (.jump J (.var x, ())) (.jump J (.var y, ())))

theorem threeInstrJoin_keep :
    reifyFunc (Func.tailDup threeInstrJoin) = reifyFunc threeInstrJoin := by
  t_kernel_rfl

/-- Adversarial invalid `DupPlan` claiming `.dup` when block `0` jumps to `.drop` block `1`. -/
def badDupPlan : DupPlan :=
  .group [.dup, .drop]
    (.cons (.node1 .leaf) (.cons .leaf .nil))
    (.node1 .leaf)

def twoBlockForBadPlan : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64], [i64]])
    (fun (_, b1, ()) =>
      .cons (fun (a, ()) => .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (a', ()) =>
        .jump b1 (.var a', ()))
      (.cons (fun (b, ()) => .ret (.var b, ())) .nil))
    (fun (b0, _, ()) => .jump b0 (.var x, ()))

theorem badDupPlan_rejected :
    Func.tailDupWithPlan badDupPlan twoBlockForBadPlan = twoBlockForBadPlan := by
  t_kernel_rfl

/-! ## 3. Formal `Wf`, `tailDup_wp` / `Func.spec`, and `callsOk` Soundness -/

theorem loopLatchTrampoline_wf : loopLatchTrampoline.Wf := by t_wf_reify
theorem loopLatchTrampoline_td_wf : (Func.tailDup loopLatchTrampoline).Wf :=
  Func.tailDup_wf loopLatchTrampoline_wf
theorem loopLatchTrampoline_td_check :
    Func.checkTFlat (Func.tailDup loopLatchTrampoline) = true := by
  t_kernel_rfl

theorem retJoinTrampoline_wf : retJoinTrampoline.Wf := by t_wf_reify
theorem retJoinTrampoline_td_wf : (Func.tailDup retJoinTrampoline).Wf :=
  Func.tailDup_wf retJoinTrampoline_wf
theorem retJoinTrampoline_td_check :
    Func.checkTFlat (Func.tailDup retJoinTrampoline) = true := by
  t_kernel_rfl

theorem chainTrampoline_wf : chainTrampoline.Wf := by t_wf_reify
theorem chainTrampoline_td_check :
    Func.checkTFlat (Func.tailDup chainTrampoline) = true := by
  t_kernel_rfl

theorem retJoinTrampoline_spec (Γ : Env) (c : Bool) (x y : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ retJoinTrampoline (c, x, y, ()) m
      (fun (r, ()) m' =>
        m' = m ∧ r = ((if c then x + 1 else y - 1) + 10) ^^^ 3) X := by
  dsimp only [Func.spec, Func.wp, retJoinTrampoline]
  intro (J, ()) hClosed
  have hc := hClosed.1
  dsimp only [wp, vals, Arg.val]
  constructor
  · intro hcTrue
    dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, cast_eq]
    apply hc (x + 1, ()) m
    dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, cast_eq]
    exact ⟨rfl, by simp [hcTrue]⟩
  · intro hcFalse
    dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, cast_eq]
    apply hc (y - 1, ()) m
    dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, cast_eq]
    exact ⟨rfl, by simp [hcFalse]⟩

theorem retJoinTrampoline_td_wp (Γ : Env) (c : Bool) (x y : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.wp Γ (Func.tailDup retJoinTrampoline) (c, x, y, ()) m
      (fun (r, ()) m' =>
        m' = m ∧ r = ((if c then x + 1 else y - 1) + 10) ^^^ 3) X :=
  tailDup_wp retJoinTrampoline_wf defaultConfig (retJoinTrampoline_spec Γ c x y m X)

/-- Specification of `loopLatchTrampoline`: sums `step k = if (k &&& 1 != 0) then k else 1`
down to `0` with memory preserved. -/
def loopStepSum : Nat → BitVec 64
  | 0 => 0
  | k + 1 =>
    let bv := BitVec.ofNat 64 (k + 1)
    let delta := if (bv &&& 1#64) != 0#64 then bv else 1#64
    delta + loopStepSum k

private theorem bv64_ofNat_sub_one {k : Nat} (hk : k + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (k + 1) - (1 : BitVec 64) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · simp [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  · rw [BitVec.le_def]; simp [Nat.mod_eq_of_lt hk]

theorem loopLatchTrampoline_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ loopLatchTrampoline (n, ()) m
      (fun (r, ()) m' => m' = m ∧ r = loopStepSum n.toNat) X := by
  dsimp only [Func.spec, Func.wp, loopLatchTrampoline]
  intro (J_latch, J_join, ()) hClosed
  have hInv : ∀ (k : Nat) (acc : BitVec 64), k < 2 ^ 64 →
      acc + loopStepSum k = loopStepSum n.toNat →
      J_latch (BitVec.ofNat 64 k, acc, ()) m := by
    intro k
    refine Nat.strongRecOn k fun k ih acc hk hAcc => ?_
    apply hClosed.1 (BitVec.ofNat 64 k, acc, ()) m
    dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, liftCmp, lift2,
      CmpOp.evalBits, Ty.hasFloat, cast_eq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases k with
    | zero =>
      constructor
      · intro h; simp at h
      · intro _; exact ⟨trivial, by simpa [loopStepSum] using hAcc⟩
    | succ k' =>
      have hne0 : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by
        intro h0
        have := congrArg BitVec.toNat h0
        simp [Nat.mod_eq_of_lt hk] at this
      constructor
      · intro _
        have hStep : ∀ delta : BitVec 64,
            delta = (if (BitVec.ofNat 64 (k' + 1) &&& 1#64 != 0#64) then
              BitVec.ofNat 64 (k' + 1) else 1#64) →
            J_join (BitVec.ofNat 64 (k' + 1), acc, delta, ()) m := by
          intro delta hdelta
          apply hClosed.2.1 (BitVec.ofNat 64 (k' + 1), acc, delta, ()) m
          dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, Ty.hasFloat, cast_eq]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [bv64_ofNat_sub_one hk]
          refine ih k' (Nat.lt_succ_self k') (acc + delta) (by omega) ?_
          calc
            (acc + delta) + loopStepSum k' = acc + (delta + loopStepSum k') :=
              BitVec.add_assoc acc delta (loopStepSum k')
            _ = acc + loopStepSum (k' + 1) := by simp only [loopStepSum, hdelta]
            _ = loopStepSum n.toNat := hAcc
        constructor
        · intro hodd
          have hne : BitVec.ofNat 64 (k' + 1) &&& 1#64 ≠ 0#64 := by
            simpa using of_decide_eq_true hodd
          exact hStep (BitVec.ofNat 64 (k' + 1)) (by simp [bne_iff_ne, hne])
        · intro heven
          have heq : BitVec.ofNat 64 (k' + 1) &&& 1#64 = 0#64 := by
            simpa using of_decide_eq_false heven
          exact hStep 1#64 (by simp [heq])
      · intro h
        exact absurd hne0 (of_decide_eq_false h)
  dsimp only [wp, vals, Arg.val]
  simpa [BitVec.ofNat_toNat] using hInv n.toNat 0#64 n.isLt (by simp)

theorem loopLatchTrampoline_td_wp (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.wp Γ (Func.tailDup loopLatchTrampoline) (n, ()) m
      (fun (r, ()) m' => m' = m ∧ r = loopStepSum n.toNat) X :=
  tailDup_wp loopLatchTrampoline_wf defaultConfig (loopLatchTrampoline_spec Γ n m X)

theorem retJoinTrampoline_td_callsOk :
    ((Func.tailDup retJoinTrampoline) UnitV (fun _ => Unit) (Tup.units _)).callsOk [] [] :=
  Func.tailDup_callsOk retJoinTrampoline_wf defaultConfig (by
    simp [retJoinTrampoline, Expr.callsOk, Blocks.callsOk])

/-! ## 4. `LegalTarget.{x64, aarch64}` & `RegaLitmus` Codegen Checks -/

def loopLatchFn : Fn := ⟨"loop_latch_tramp", [i64], [i64], loopLatchTrampoline⟩
def retJoinFn : Fn := ⟨"ret_join_tramp", [.bool, i64, i64], [i64], retJoinTrampoline⟩
def chainFn : Fn := ⟨"chain_tramp", [.bool, i64], [i64], chainTrampoline⟩

#guard (Fn.legal .x64 (Fn.tailDup loopLatchFn)).body.isLegal .x64
#guard (Fn.legal .aarch64 (Fn.tailDup loopLatchFn)).body.isLegal .aarch64
#guard (Fn.legal .x64 (Fn.tailDup retJoinFn)).body.isLegal .x64
#guard (Fn.legal .aarch64 (Fn.tailDup retJoinFn)).body.isLegal .aarch64
#guard (Fn.legal .x64 (Fn.tailDup chainFn)).body.isLegal .x64
#guard (Fn.legal .aarch64 (Fn.tailDup chainFn)).body.isLegal .aarch64

meta def litmusCode (f : Fn) : Option (List Instr) :=
  let h := Spill.hints litmusTarget.toIsa f
  match Rega.lowerFn litmusTarget.toIsa h f.ext f with
  | .ok c => some c
  | .error _ => none

meta def countLitmusJmps (ds : List Instr) : Nat :=
  (ds.filter fun | .jmp _ => true | _ => false).length

def retJoinLitmusFn : Fn := ⟨"ret_join_litmus", [i64, i64, i64], [i64], fun _ _ (a, x, y, ()) =>
  .let_ (op2 (.ne i64) (.var a) (.imm 0)) fun (c, ()) =>
  retJoinTrampoline _ _ (c, x, y, ())⟩

def chainLitmusFn : Fn := ⟨"chain_litmus", [i64, i64], [i64], fun _ _ (a, n, ()) =>
  .let_ (op2 (.ne i64) (.var a) (.imm 0)) fun (c, ()) =>
  chainTrampoline _ _ (c, n, ())⟩

#guard match litmusCode loopLatchFn, litmusCode (Fn.tailDup loopLatchFn) with
  | some c0, some c1 => countLitmusJmps c1 < countLitmusJmps c0
  | _, _ => false

#guard match litmusCode retJoinLitmusFn, litmusCode (Fn.tailDup retJoinLitmusFn) with
  | some c0, some c1 => countLitmusJmps c1 < countLitmusJmps c0
  | _, _ => false

#guard match litmusCode chainLitmusFn, litmusCode (Fn.tailDup chainLitmusFn) with
  | some c0, some c1 => countLitmusJmps c1 ≤ countLitmusJmps c0
  | _, _ => false

/-! ## 5. Kissat `Plain` (`59` Fns) Static Jump/Block Elimination -/

mutual
meta def countTFlatJumps {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => countTFlatJumps k
  | .jnz _ t e => countTFlatJumps t + countTFlatJumps e
  | .jump _ _ => 1
  | .ret _ | .exit _ _ | .hlt => 0
  | .group bs k => countTFlatJumpsB bs + countTFlatJumps k

meta def countTFlatJumpsB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countTFlatJumps b + countTFlatJumpsB bs
end

mutual
meta def countTFlatBlocks {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => countTFlatBlocks k
  | .jnz _ t e => countTFlatBlocks t + countTFlatBlocks e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := sig) bs k => sig.length + countTFlatBlocksB bs + countTFlatBlocks k

meta def countTFlatBlocksB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countTFlatBlocks b + countTFlatBlocksB bs
end

/-- `(name, checkTFlat, jumpsBefore, jumpsAfter, blocksBefore, blocksAfter)` on `Kissat.Plain`. -/
meta def plainTailDupReport : List (String × Bool × Nat × Nat × Nat × Nat) :=
  plainFns.map fun f =>
    let mf := f.mid LegalTarget.x64
    let td := Fn.tailDup mf
    let tf0 := reifyFunc mf.body
    let tf1 := reifyFunc td.body
    (f.name, Func.checkTFlat td.body, countTFlatJumps tf0, countTFlatJumps tf1,
      countTFlatBlocks tf0, countTFlatBlocks tf1)

#eval show IO Unit from do
  let totJ0 := plainTailDupReport.foldl (fun a r => a + r.2.2.1) 0
  let totJ1 := plainTailDupReport.foldl (fun a r => a + r.2.2.2.1) 0
  let totB0 := plainTailDupReport.foldl (fun a r => a + r.2.2.2.2.1) 0
  let totB1 := plainTailDupReport.foldl (fun a r => a + r.2.2.2.2.2) 0
  let touched := plainTailDupReport.filter fun r =>
    r.2.2.1 != r.2.2.2.1 || r.2.2.2.2.1 != r.2.2.2.2.2
  IO.println
    s!"[Kissat.Plain x64 mid] fns={plainTailDupReport.length} touched={touched.length}"
  IO.println s!"  jumps={totJ0}->{totJ1} (drop={totJ0 - totJ1})"
  IO.println s!"  blocks={totB0}->{totB1} (drop={totB0 - totB1})"

#guard plainTailDupReport.all (·.2.1)
#guard plainTailDupReport.foldl (fun a r => a + r.2.2.1) 0 >
  plainTailDupReport.foldl (fun a r => a + r.2.2.2.1) 0
#guard plainTailDupReport.foldl (fun a r => a + r.2.2.2.2.1) 0 >
  plainTailDupReport.foldl (fun a r => a + r.2.2.2.2.2) 0

/-! ## 6. Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Func.tailDupWithPlan_wf
#print axioms LeanQbe.T.Func.tailDupWithPlan_spec
#print axioms LeanQbe.T.Func.tailDupWithPlan_callsOk
#print axioms LeanQbe.T.Func.tailDupOnce_wf
#print axioms LeanQbe.T.Func.tailDupOnce_spec
#print axioms LeanQbe.T.Func.tailDupOnce_callsOk
#print axioms LeanQbe.T.Func.tailDup_wf
#print axioms LeanQbe.T.Func.tailDup_spec
#print axioms LeanQbe.T.tailDup_wp
#print axioms LeanQbe.T.Func.tailDup_callsOk
#print axioms LeanQbe.T.Fn.tailDup_wf
#print axioms LeanQbe.T.Fn.tailDup_spec
#print axioms LeanQbe.T.Fn.tailDup_callsOk
#print axioms LeanQbeTest.T.TailDupTest.retJoinTrampoline_td_wp
#print axioms LeanQbeTest.T.TailDupTest.loopLatchTrampoline_td_wp
#print axioms LeanQbeTest.T.TailDupTest.retJoinTrampoline_td_callsOk

end LeanQbeTest.T.TailDupTest
