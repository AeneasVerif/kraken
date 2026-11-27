module

public import LeanQbe.T.PeelLemmas
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules

/-!
# Tests of `LeanQbe.T.Peel`

Covers:
1. Structural/AST peeling on `loop1` (`sumLoop`), verifying 1st-iteration unrolling at `entry`'s
   jump with zero `.copy` bindings and remaining `.group` at the back-jump.
2. `0`-iteration / immediate-exit loop (`preCheckLoop` and `n = 0` paths executing without entering
   the remaining `.group`).
3. Nested loop peeling (`nestedDirectLoop` respecting `substJumps == 0`, and `nestedSeqLoop`
   peeling both inner and outer loops).
4. Budget and site-guard preservation (`maxLoopSize := 0`, `4`, default `40` on large loops,
   multi-entry, multi-back-jump, and multi-block `.group`).
5. End-to-end LICM synergy (`Func.gvn (Func.peel f)` and `Func.opt (Func.peel f)` hoisting
   loop-invariant pure arithmetic out of the remaining loop body).
6. Loop-invariant load & struct-field address shape (`mb5LoadLoop`), verifying
   first-iteration address/load unrolling, `Func.gvn` address elimination inside the loop,
   and memory-backed WP correctness (`wp_load_cell64`).
7. `Func.checkTFlat`, `t_wf_reify`, `Func.peel_spec`, `Fn.peel_spec`, and `#print axioms`.
-/

set_option autoImplicit false

section

namespace LeanQbe.T.PeelTest

open LeanQbe.T

/-! ## 1. Standard `loop1` (`sumLoop`) -/

/-- Sum `n + (n - 1) + … + 1`, exiting immediately when `i == 0`. -/
def sumLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem sumLoop_peel_out : Func.peel sumLoop = fun _ _ (n, ()) =>
    .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (z, ()) =>
    .jnz (.var z) (.ret (.imm 0, ()))
      (.let_ (op2 (.add i64) (.imm 0) (.var n)) fun (acc', ()) =>
       .let_ (op2 (.sub i64) (.var n) (.imm 1)) fun (i', ()) =>
       .group (sig := [[i64, i64]])
         (fun (loop, ()) => .cons (fun (i, acc, ()) =>
           .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z2, ()) =>
           .jnz (.var z2) (.ret (.var acc, ()))
             (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc2, ()) =>
              .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i2, ()) =>
              .jump loop (.var i2, .var acc2, ()))) .nil)
         (fun (loop, ()) => .jump loop (.var i', .var acc', ()))) := by
  t_kernel_rfl

theorem sumLoop_wf : sumLoop.Wf := by t_wf_reify
theorem sumLoop_peel_wf : (Func.peel sumLoop).Wf := Func.peel_wf sumLoop_wf
theorem sumLoop_peel_checkTFlat : Func.checkTFlat (Func.peel sumLoop) = true := by t_kernel_rfl

theorem sumLoop_peel_zero_spec (Γ : Env) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.peel sumLoop) (0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) X := by
  rw [sumLoop_peel_out]
  dsimp only [Func.spec, Func.wp]
  wp_unfold
  simp

theorem sumLoop_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ sumLoop (n, ()) m
      (fun (r, ()) m' => 2 * r.toNat % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64 ∧ m' = m)
      X := by
  dsimp only [Func.spec, Func.wp, sumLoop]
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
      simp only [true_implies, not_true_eq_false, false_implies, and_true]
      simpa using hinv
    · have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [hz, false_implies, not_false_eq_true, true_implies, true_and]
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

theorem sumLoop_peel_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.peel sumLoop) (n, ()) m
      (fun (r, ()) m' => 2 * r.toNat % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64 ∧ m' = m)
      X :=
  Func.peel_spec sumLoop_wf 40 (sumLoop_spec Γ n m X)

/-! ## 2. `0`-iteration / immediate-exit loop (`preCheckLoop`) -/

/-- `while (n != 0)` loop adding `k` `n` times, with a pre-loop zero guard in `entry`. -/
def preCheckLoop : Func [i64, i64] [i64] := fun _ _ (n, k, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.add i64) (.var acc) (.var k)) fun (acc', ()) =>
      .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
      .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c, ()) =>
      .jnz (.var c) (.jump loop (.var i', .var acc', ())) (.ret (.var acc', ())))
    (fun loop =>
      .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.imm 0, ())) (.jump loop (.var n, .imm 0, ())))

theorem preCheckLoop_peel_out : Func.peel preCheckLoop = fun _ _ (n, k, ()) =>
    .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (z, ()) =>
    .jnz (.var z) (.ret (.imm 0, ()))
      (.let_ (op2 (.add i64) (.imm 0) (.var k)) fun (acc', ()) =>
       .let_ (op2 (.sub i64) (.var n) (.imm 1)) fun (i', ()) =>
       .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c, ()) =>
       .jnz (.var c)
         (.group (sig := [[i64, i64]])
           (fun (loop, ()) => .cons (fun (i, acc, ()) =>
             .let_ (op2 (.add i64) (.var acc) (.var k)) fun (acc2, ()) =>
             .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i2, ()) =>
             .let_ (op2 (.ne i64) (.var i2) (.imm 0)) fun (c2, ()) =>
             .jnz (.var c2) (.jump loop (.var i2, .var acc2, ())) (.ret (.var acc2, ()))) .nil)
           (fun (loop, ()) => .jump loop (.var i', .var acc', ())))
         (.ret (.var acc', ()))) := by
  t_kernel_rfl

theorem preCheckLoop_wf : preCheckLoop.Wf := by t_wf_reify
theorem preCheckLoop_peel_checkTFlat : Func.checkTFlat (Func.peel preCheckLoop) = true := by
  t_kernel_rfl

theorem preCheckLoop_peel_zero_spec (Γ : Env) (k : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.peel preCheckLoop) (0#64, k, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) X := by
  rw [preCheckLoop_peel_out]
  dsimp only [Func.spec, Func.wp]
  wp_unfold
  simp

theorem preCheckLoop_peel_one_spec (Γ : Env) (k : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.peel preCheckLoop) (1#64, k, ()) m
      (fun (r, ()) m' => r = k ∧ m' = m) X := by
  rw [preCheckLoop_peel_out]
  dsimp only [Func.spec, Func.wp]
  wp_unfold
  simp

theorem preCheckLoop_peel_spec (Γ : Env) (n k : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.peel preCheckLoop) (n, k, ()) m
      (fun (r, ()) m' => r = n * k ∧ m' = m) X := by
  apply Func.peel_spec preCheckLoop_wf
  dsimp only [Func.spec, Func.wp, preCheckLoop]
  refine wp_loop1 _ _
    (fun cnt (x : Tup Val [i64, i64]) m' =>
      x.1.toNat = cnt ∧ cnt ≥ 1 ∧ m' = m ∧ x.2.1 + x.1 * k = n * k)
    ?_ ?_
  · rintro J cnt ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, hge, rfl, hinv⟩
    dsimp only at hk hinv
    wp_unfold
    by_cases hdone : i - 1 = 0
    · have hi1 : i = 1 := by
        have h := congrArg (· + (1 : BitVec 64)) hdone
        simpa [BitVec.sub_add_cancel] using h
      subst hi1
      simp only [hdone, not_true_eq_false, false_implies, true_implies, true_and]
      simpa using hinv
    · have hi1 : i ≠ 1 := fun h => hdone (by subst h; rfl)
      have hge2 : cnt ≥ 2 := by
        have : i.toNat ≠ 1 := fun h => hi1 (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      simp only [hdone, not_false_eq_true, true_implies, false_implies, and_true]
      refine hJ (cnt - 1) _ m' (by omega) ?_
      have hsub : (i - 1).toNat = i.toNat - 1 :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
      refine ⟨by dsimp only; rw [hsub]; omega, by omega, rfl, ?_⟩
      dsimp only
      calc acc + k + (i - 1) * k
          = acc + ((1 : BitVec 64) * k + (i - 1) * k) := by simp [BitVec.one_mul]; ac_rfl
        _ = acc + (1 + (i - 1)) * k := by rw [← BitVec.add_mul]
        _ = acc + i * k := by rw [BitVec.add_comm 1 (i - 1), BitVec.sub_add_cancel]
        _ = n * k := hinv
  · intro J hJ
    wp_unfold
    by_cases hn : n = 0
    · subst hn; simp
    · have hn0 : n.toNat ≠ 0 := fun h => hn (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [hn, false_implies, not_false_eq_true, true_implies, true_and]
      exact hJ n.toNat (n, 0, ()) m ⟨rfl, by omega, rfl, by simp⟩

/-! ## 3. Nested loops (`nestedDirectLoop` and `nestedSeqLoop`) -/

/-- Direct-exit nested loop (modeled on `RegaLitmusProgs.fnNested`): `inner` exits straight to
`outer` or returns. -/
def nestedDirectLoop : Func [i64, i64] [i64] := fun _ _ (n, m, ()) =>
  loop1 (ts := [i64, i64])
    (fun outer (i, acc, ()) =>
      loop1 (ts := [i64, i64])
        (fun inner (j, acc2, ()) =>
          .let_ (op2 (.add i64) (.var acc2) (.imm 1)) fun (acc3, ()) =>
          .let_ (op2 (.sub i64) (.var j) (.imm 1)) fun (j', ()) =>
          .let_ (op2 (.ne i64) (.var j') (.imm 0)) fun (cj, ()) =>
          .jnz (.var cj) (.jump inner (.var j', .var acc3, ()))
            (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
             .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (ci, ()) =>
             .jnz (.var ci) (.jump outer (.var i', .var acc3, ())) (.ret (.var acc3, ()))))
        (fun inner => .jump inner (.var m, .var acc, ())))
    (fun outer => .jump outer (.var n, .imm 0, ()))

/-- `outer` peels 1 iteration, `inner` inside `outer`'s remaining `.group` peels, while `inner`
inside `outer`'s peeled 1st iteration stays unpeeled (`substJumps = 1`) so `outer` is never
duplicated. -/
theorem nestedDirect_peel_out : Func.peel nestedDirectLoop = fun _ _ (n, m, ()) =>
    loop1 (ts := [i64, i64])
      (fun inner (j, acc2, ()) =>
        .let_ (op2 (.add i64) (.var acc2) (.imm 1)) fun (acc3, ()) =>
        .let_ (op2 (.sub i64) (.var j) (.imm 1)) fun (j', ()) =>
        .let_ (op2 (.ne i64) (.var j') (.imm 0)) fun (cj, ()) =>
        .jnz (.var cj) (.jump inner (.var j', .var acc3, ()))
          (.let_ (op2 (.sub i64) (.var n) (.imm 1)) fun (i', ()) =>
           .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (ci, ()) =>
           .jnz (.var ci)
             (.group (sig := [[i64, i64]])
               (fun (outer, ()) => .cons (fun (i, acc, ()) =>
                 .let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (acc3_1, ()) =>
                 .let_ (op2 (.sub i64) (.var m) (.imm 1)) fun (j'_1, ()) =>
                 .let_ (op2 (.ne i64) (.var j'_1) (.imm 0)) fun (cj_1, ()) =>
                 .jnz (.var cj_1)
                   (.group (sig := [[i64, i64]])
                     (fun (inner2, ()) => .cons (fun (j2, acc2_2, ()) =>
                       .let_ (op2 (.add i64) (.var acc2_2) (.imm 1)) fun (acc3_2, ()) =>
                       .let_ (op2 (.sub i64) (.var j2) (.imm 1)) fun (j'_2, ()) =>
                       .let_ (op2 (.ne i64) (.var j'_2) (.imm 0)) fun (cj_2, ()) =>
                       .jnz (.var cj_2) (.jump inner2 (.var j'_2, .var acc3_2, ()))
                         (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i'_2, ()) =>
                          .let_ (op2 (.ne i64) (.var i'_2) (.imm 0)) fun (ci_2, ()) =>
                          .jnz (.var ci_2) (.jump outer (.var i'_2, .var acc3_2, ()))
                            (.ret (.var acc3_2, ())))) .nil)
                     (fun (inner2, ()) => .jump inner2 (.var j'_1, .var acc3_1, ())))
                   (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i'_1, ()) =>
                    .let_ (op2 (.ne i64) (.var i'_1) (.imm 0)) fun (ci_1, ()) =>
                    .jnz (.var ci_1) (.jump outer (.var i'_1, .var acc3_1, ()))
                      (.ret (.var acc3_1, ())))) .nil)
               (fun (outer, ()) => .jump outer (.var i', .var acc3, ())))
             (.ret (.var acc3, ()))))
      (fun inner => .jump inner (.var m, .imm 0, ())) := by
  t_kernel_rfl

/-- At `maxLoopSize = 10`, `outer` (`size = 11 > 10`) stays unpeeled while `inner` (`size = 8`)
peels cleanly. -/
theorem nestedDirect_peel_cap10_out : Func.peel nestedDirectLoop 10 = fun _ _ (n, m, ()) =>
    loop1 (ts := [i64, i64])
      (fun outer (i, acc, ()) =>
        .let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (acc3_1, ()) =>
        .let_ (op2 (.sub i64) (.var m) (.imm 1)) fun (j'_1, ()) =>
        .let_ (op2 (.ne i64) (.var j'_1) (.imm 0)) fun (cj_1, ()) =>
        .jnz (.var cj_1)
          (.group (sig := [[i64, i64]])
            (fun (inner, ()) => .cons (fun (j, acc2, ()) =>
              .let_ (op2 (.add i64) (.var acc2) (.imm 1)) fun (acc3, ()) =>
              .let_ (op2 (.sub i64) (.var j) (.imm 1)) fun (j', ()) =>
              .let_ (op2 (.ne i64) (.var j') (.imm 0)) fun (cj, ()) =>
              .jnz (.var cj) (.jump inner (.var j', .var acc3, ()))
                (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
                 .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (ci, ()) =>
                 .jnz (.var ci) (.jump outer (.var i', .var acc3, ()))
                   (.ret (.var acc3, ())))) .nil)
            (fun (inner, ()) => .jump inner (.var j'_1, .var acc3_1, ())))
          (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (ci, ()) =>
           .jnz (.var ci) (.jump outer (.var i', .var acc3_1, ())) (.ret (.var acc3_1, ()))))
      (fun outer => .jump outer (.var n, .imm 0, ())) := by
  t_kernel_rfl

theorem nestedDirect_wf : nestedDirectLoop.Wf := by t_wf_reify
theorem nestedDirect_peel_wf : (Func.peel nestedDirectLoop).Wf := Func.peel_wf nestedDirect_wf
theorem nestedDirect_peel_checkTFlat : Func.checkTFlat (Func.peel nestedDirectLoop) = true := by
  t_kernel_rfl

/-- Structured nested loop where `inner` breaks to a join block before `outer`'s back-jump, so
both `outer` and `inner` (in both `iter1` and `remBodies`) peel cleanly. -/
def nestedSeqLoop : Func [i64, i64] [i64] := fun _ _ (n, m, ()) =>
  loop1 (ts := [i64, i64])
    (fun outer (i, acc, ()) =>
      .group (sig := [[i64]])
        (fun (_brk, ()) => .cons (fun (acc2, ()) =>
          .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
          .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (ci, ()) =>
          .jnz (.var ci) (.jump outer (.var i', .var acc2, ())) (.ret (.var acc2, ()))) .nil)
        (fun (brk, ()) =>
          loop1 (ts := [i64, i64])
            (fun inner (j, a, ()) =>
              .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (a', ()) =>
              .let_ (op2 (.sub i64) (.var j) (.imm 1)) fun (j', ()) =>
              .let_ (op2 (.ne i64) (.var j') (.imm 0)) fun (cj, ()) =>
              .jnz (.var cj) (.jump inner (.var j', .var a', ())) (.jump brk (.var a', ())))
            (fun inner => .jump inner (.var m, .var acc, ()))))
    (fun outer => .jump outer (.var n, .imm 0, ()))

theorem nestedSeq_wf : nestedSeqLoop.Wf := by t_wf_reify
theorem nestedSeq_peel_wf : (Func.peel nestedSeqLoop).Wf := Func.peel_wf nestedSeq_wf
theorem nestedSeq_peel_checkTFlat : Func.checkTFlat (Func.peel nestedSeqLoop) = true := by
  t_kernel_rfl

mutual
/-- Count single-block `.group` nodes in a `TFlat` term. -/
def countGroups {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => countGroups k
  | .jnz _ t e => countGroups t + countGroups e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group bodies k => 1 + countGroupsB bodies + countGroups k

def countGroupsB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countGroups b + countGroupsB bs
end

def funcTFlat {as rs : List Ty} (f : Func as rs) : TFlat rs :=
  toTFlat (f K KL (Tup.levels as 0)) as.length 0

/-- In `nestedSeqLoop` (originally `3` groups: `outer`, `brk`, `inner`), peeling `outer` plus
peeling `inner` in both `iter1` and `remBodies` yields `5` groups (`iter1` has `brk` + `inner_rem`,
`rem` has `outer_rem` wrapping `brk` + `inner_rem`). -/
theorem nestedSeq_peel_groupCount :
    countGroups (funcTFlat (Func.peel nestedSeqLoop)) = 5 := by
  t_kernel_rfl

/-! ## 4. Budget & site-guard cap preservation (`maxLoopSize`, multi-site, multi-block) -/

theorem sumLoop_cap0_untouched : Func.peel sumLoop 0 = sumLoop := by t_kernel_rfl
theorem sumLoop_cap4_untouched : Func.peel sumLoop 4 = sumLoop := by t_kernel_rfl

def addChain {V : Ty → Type} {L : List Ty → Type} (step : Nat) (x : V i64)
    (k : V i64 → Expr V L [i64]) : Expr V L [i64] :=
  match step with
  | 0 => k x
  | n + 1 => .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) => addChain n y k

/-- Loop whose body has `44 > 40` nodes, so default `maxLoopSize := 40` leaves it untouched. -/
def bigLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      addChain 40 acc fun acc' =>
      .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
      .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c, ()) =>
      .jnz (.var c) (.jump loop (.var i', .var acc', ())) (.ret (.var acc', ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem bigLoop_default_untouched : Func.peel bigLoop = bigLoop := by t_kernel_rfl

/-- Two entry jumps to the loop block (`eJumps = 2`): skipped so growth stays `≤ 1x`. -/
def multiEntryLoop : Func [.bool, i64] [i64] := fun _ _ (c, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ())))
    (fun loop => .jnz (.var c) (.jump loop (.var n, .imm 1, ())) (.jump loop (.var n, .imm 2, ())))

theorem multiEntry_untouched : Func.peel multiEntryLoop = multiEntryLoop := by t_kernel_rfl

/-- Two back-jumps inside the loop body (`bJumps = 2`): skipped so growth stays `≤ 1x`. -/
def multiBackLoop : Func [.bool, i64] [i64] := fun _ _ (c, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jnz (.var c)
           (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (a1, ()) =>
            .jump loop (.var i', .var a1, ()))
           (.let_ (op2 (.add i64) (.var acc) (.imm 2)) fun (a2, ()) =>
            .jump loop (.var i', .var a2, ()))))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem multiBack_untouched : Func.peel multiBackLoop = multiBackLoop := by t_kernel_rfl

/-- Two-block `.group` is untouched while its inner `loop1` still peels cleanly. -/
def twoBlockGroup : Func [.bool, i64] [i64] := fun _ _ (c, n, ()) =>
  .group (sig := [[i64], [i64]])
    (fun (_b0, _b1, ()) =>
      .cons (fun (x, ()) => sumLoop _ _ (x, ()))
      (.cons (fun (y, ()) => .ret (.var y, ())) .nil))
    (fun (b0, b1, ()) => .jnz (.var c) (.jump b0 (.var n, ())) (.jump b1 (.imm 7, ())))

theorem twoBlock_inner_peels :
    countGroups (funcTFlat (Func.peel twoBlockGroup)) = 2 := by
  t_kernel_rfl

theorem twoBlock_checkTFlat :
    Func.checkTFlat (Func.peel twoBlockGroup) = true := by
  t_kernel_rfl

/-! ## 5. LICM synergy: `Func.gvn (Func.peel f)` and `Func.opt (Func.peel f)` -/

/-- Loop with loop-invariant pure arithmetic `(a + b) * 3` computed on every trip. -/
def licmArithLoop : Func [i64, i64, i64] [i64] := fun _ _ (n, a, b, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var a) (.var b)) fun (k1, ()) =>
         .let_ (op2 (.mul i64) (.var k1) (.imm 3)) fun (k2, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var k2)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

/-- After `Func.peel`, `Func.gvn` hoists `k1 = a + b` and `k2 = k1 * 3` into the peeled 1st
iteration and removes both loop-invariant computations from the remaining `.group`. -/
theorem licmArith_peel_gvn_out : Func.gvn (Func.peel licmArithLoop) = fun _ _ (n, a, b, ()) =>
    .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (z, ()) =>
    .jnz (.var z) (.ret (.imm 0, ()))
      (.let_ (op2 (.add i64) (.var a) (.var b)) fun (k1, ()) =>
       .let_ (op2 (.mul i64) (.var k1) (.imm 3)) fun (k2, ()) =>
       .let_ (op2 (.add i64) (.imm 0) (.var k2)) fun (acc', ()) =>
       .let_ (op2 (.sub i64) (.var n) (.imm 1)) fun (i', ()) =>
       .group (sig := [[i64, i64]])
         (fun (loop, ()) => .cons (fun (i, acc, ()) =>
           .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z2, ()) =>
           .jnz (.var z2) (.ret (.var acc, ()))
             (.let_ (op2 (.add i64) (.var acc) (.var k2)) fun (acc2, ()) =>
              .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i2, ()) =>
              .jump loop (.var i2, .var acc2, ()))) .nil)
         (fun (loop, ()) => .jump loop (.var i', .var acc', ()))) := by
  t_kernel_rfl

/-- Full `Func.opt (Func.peel licmArithLoop)` additionally folds `0 + k2 → k2` in the peeled
pre-loop path while keeping the loop body free of `(a + b) * 3`. -/
theorem licmArith_peel_opt_out : Func.opt (Func.peel licmArithLoop) = fun _ _ (n, a, b, ()) =>
    .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (z, ()) =>
    .jnz (.var z) (.ret (.imm 0, ()))
      (.let_ (op2 (.add i64) (.var a) (.var b)) fun (k1, ()) =>
       .let_ (op2 (.mul i64) (.var k1) (.imm 3)) fun (k2, ()) =>
       .let_ (op2 (.sub i64) (.var n) (.imm 1)) fun (i', ()) =>
       .group (sig := [[i64, i64]])
         (fun (loop, ()) => .cons (fun (i, acc, ()) =>
           .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z2, ()) =>
           .jnz (.var z2) (.ret (.var acc, ()))
             (.let_ (op2 (.add i64) (.var acc) (.var k2)) fun (acc2, ()) =>
              .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i2, ()) =>
              .jump loop (.var i2, .var acc2, ()))) .nil)
         (fun (loop, ()) => .jump loop (.var i', .var k2, ()))) := by
  t_kernel_rfl

theorem licmArith_wf : licmArithLoop.Wf := by t_wf_reify
theorem licmArith_peel_opt_checkTFlat :
    Func.checkTFlat (Func.opt (Func.peel licmArithLoop)) = true := by
  t_kernel_rfl

theorem licmArith_peel_opt_spec (Γ : Env) (n a b : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.opt (Func.peel licmArithLoop)) (n, a, b, ()) m
      (fun (r, ()) m' => r = n * ((a + b) * 3#64) ∧ m' = m) X := by
  apply Func.opt_spec (Func.peel_wf licmArith_wf)
  apply Func.peel_spec licmArith_wf
  dsimp only [Func.spec, Func.wp, licmArithLoop]
  refine wp_loop1 _ _
    (fun k (x : Tup Val [i64, i64]) m' =>
      x.1.toNat = k ∧ m' = m ∧ x.2.1 + x.1 * ((a + b) * 3#64) = n * ((a + b) * 3#64))
    ?_ ?_
  · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
    dsimp only at hk hinv
    wp_unfold
    by_cases hz : i = 0
    · subst hz
      simp only [true_implies, not_true_eq_false, false_implies, and_true]
      simpa using hinv
    · have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [hz, false_implies, not_false_eq_true, true_implies, true_and]
      refine hJ (k - 1) _ m' (by omega) ?_
      have hsub : (i - 1).toNat = i.toNat - 1 :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
      refine ⟨by dsimp only; rw [hsub]; omega, rfl, ?_⟩
      dsimp only
      let c := (a + b) * 3#64
      calc acc + c + (i - 1) * c
          = acc + ((1 : BitVec 64) * c + (i - 1) * c) := by simp [BitVec.one_mul]; ac_rfl
        _ = acc + (1 + (i - 1)) * c := by rw [← BitVec.add_mul]
        _ = acc + i * c := by rw [BitVec.add_comm 1 (i - 1), BitVec.sub_add_cancel]
        _ = n * c := hinv
  · intro J hJ
    wp_unfold
    exact hJ n.toNat (n, 0#64, ()) m ⟨rfl, rfl, by simp⟩

/-! ## 6. Loop-invariant load & struct-field address AST synergy (`mb5LoadLoop`) -/

/-- Struct-field read (`base + 8`) inside `loop1`: computes `addr = add ptr 8` and
`fld = load i64 addr` each trip. -/
def mb5LoadLoop : Func [i64, i64] [i64] := fun _ _ (n, ptr, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var ptr) (.imm 8)) fun (addr, ()) =>
         .load i64 (.var addr) fun fld =>
         .let_ (op2 (.add i64) (.var acc) (.var fld)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

/-- `Func.peel` unrolls the first-iteration `addr = ptr + 8` and `fld = load i64 addr` into the
straight-line pre-loop path, and `Func.gvn` eliminates the duplicate `ptr + 8` inside the
remaining `.group` (leaving the invariant load at `addr` ready for downstream `MemLoad`). -/
theorem mb5Load_peel_gvn_out : Func.gvn (Func.peel mb5LoadLoop) = fun _ _ (n, ptr, ()) =>
    .let_ (op2 (.eq i64) (.var n) (.imm 0)) fun (z, ()) =>
    .jnz (.var z) (.ret (.imm 0, ()))
      (.let_ (op2 (.add i64) (.var ptr) (.imm 8)) fun (addr, ()) =>
       .load i64 (.var addr) fun fld =>
       .let_ (op2 (.add i64) (.imm 0) (.var fld)) fun (acc', ()) =>
       .let_ (op2 (.sub i64) (.var n) (.imm 1)) fun (i', ()) =>
       .group (sig := [[i64, i64]])
         (fun (loop, ()) => .cons (fun (i, acc, ()) =>
           .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z2, ()) =>
           .jnz (.var z2) (.ret (.var acc, ()))
             (.load i64 (.var addr) fun fld2 =>
              .let_ (op2 (.add i64) (.var acc) (.var fld2)) fun (acc2, ()) =>
              .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i2, ()) =>
              .jump loop (.var i2, .var acc2, ()))) .nil)
         (fun (loop, ()) => .jump loop (.var i', .var acc', ()))) := by
  t_kernel_rfl

theorem mb5Load_wf : mb5LoadLoop.Wf := by t_wf_reify
theorem mb5Load_peel_checkTFlat : Func.checkTFlat (Func.peel mb5LoadLoop) = true := by
  t_kernel_rfl

theorem mb5Load_peel_gvn_spec (Γ : Env) (n ptr v : BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell64 (ptr + 8#64) v ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.gvn (Func.peel mb5LoadLoop)) (n, ptr, ()) m
      (fun (r, ()) m' => r = n * v ∧ m' = m) X := by
  apply Func.gvn_spec (Func.peel_wf mb5Load_wf)
  apply Func.peel_spec mb5Load_wf
  dsimp only [Func.spec, Func.wp, mb5LoadLoop]
  refine wp_loop1 _ _
    (fun k (x : Tup Val [i64, i64]) m' =>
      x.1.toNat = k ∧ m' = m ∧ x.2.1 + x.1 * v = n * v)
    ?_ ?_
  · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
    dsimp only at hk hinv
    wp_unfold
    by_cases hz : i = 0
    · subst hz
      simp only [true_implies, not_true_eq_false, false_implies, and_true]
      simpa using hinv
    · have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [hz, false_implies, not_false_eq_true, true_implies, true_and]
      refine ⟨v, loadVal_cell64 hm, ?_⟩
      refine hJ (k - 1) _ m' (by omega) ?_
      have hsub : (i - 1).toNat = i.toNat - 1 :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
      refine ⟨by dsimp only; rw [hsub]; omega, rfl, ?_⟩
      dsimp only
      calc acc + v + (i - 1) * v
          = acc + ((1 : BitVec 64) * v + (i - 1) * v) := by simp [BitVec.one_mul]; ac_rfl
        _ = acc + (1 + (i - 1)) * v := by rw [← BitVec.add_mul]
        _ = acc + i * v := by rw [BitVec.add_comm 1 (i - 1), BitVec.sub_add_cancel]
        _ = n * v := hinv
  · intro J hJ
    wp_unfold
    exact hJ n.toNat (n, 0#64, ()) m ⟨rfl, rfl, by simp⟩

/-! ## 7. `Fn.peel` and axiom audit -/

def sumLoopFn : Fn := ⟨"sumLoop", [i64], [i64], sumLoop⟩

theorem sumLoopFn_peel_sig :
    sumLoopFn.peel.name = "sumLoop" ∧ sumLoopFn.peel.as = [i64] ∧ sumLoopFn.peel.rs = [i64] :=
  ⟨rfl, rfl, rfl⟩

theorem sumLoopFn_peel_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (sumLoopFn.peel 40).body (n, ()) m
      (fun (r, ()) m' => 2 * r.toNat % 2 ^ 64 = (n.toNat * (n.toNat + 1)) % 2 ^ 64 ∧ m' = m)
      X :=
  Fn.peel_spec sumLoopFn sumLoop_wf 40 (sumLoop_spec Γ n m X)

#print axioms LeanQbe.T.peel_wf
#print axioms LeanQbe.T.peel_wp
#print axioms LeanQbe.T.Func.peel_wf
#print axioms LeanQbe.T.Func.peel_spec
#print axioms LeanQbe.T.Fn.peel_spec
#print axioms LeanQbe.T.PeelTest.licmArith_peel_opt_spec
#print axioms LeanQbe.T.PeelTest.mb5Load_peel_gvn_spec

end LeanQbe.T.PeelTest
