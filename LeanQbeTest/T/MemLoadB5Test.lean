module

public import LeanQbe.T.MemLoadLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules

/-!
# Tests for Indexed `(base, idx, scale, off)` `MemLoad` & Acyclic `.group` CSE

Tests:
1. Indexed `base + (idx << 2) + off` load CSE, store-to-load forwarding, and disjoint
   same-index offset preservation (`off = 0, 8` across `(idx + 1) << 2` vs `idx * 4 + 4`).
2. `zext 32 64` / `sext 32 64` index forwarding and commutative `idx + base` equivalence.
3. Alias invalidation soundness: unknown store or different-index store kills cached indexed
   load, while disjoint offset with identical `(base, idx, scale)` survives.
4. Acyclic `.group` join-block preservation (`sift`-style load-before-store swap in `.group`
   forwards outer cached loads cleanly when `.group` does not loop back to itself) with
   `Func.memLoad_spec`.
5. Cyclic `.group` loop soundness: a `.group` that stores to `ar[i]` and loops back must
   flush `ar[i]` in `bodies` so the loop body reloads the updated value.
6. Axiom audit (`#print axioms`) confirming only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.MemLoadB5Test

open LeanQbe.T Std.ExtHashMap

/-! ## 1. Indexed `(base, idx, scale, off)` CSE, forwarding, and `(idx + 1) << 2` -/

/-- Store `v0` at `base + (idx << 2)` and `v1` at `base + (idx * 4 + 8)`, then reload via
independently recomputed `base + ((idx + 1) << 2) - 4` and `(base + 8) + (idx << 2)`. -/
def idxScaleProg : Func [i64, i64, i32, i32] [i32, i32] := fun _ _ p =>
  let base := p.1
  let idx := p.2.1
  let v0 := p.2.2.1
  let v1 := p.2.2.2.1
  .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun sh =>
  .let_ (op2 (.add i64) (.var base) (.var sh.1)) fun p0 =>
  .let_ (op2 (.mul i64) (.var idx) (.imm 4)) fun mu =>
  .let_ (op2 (.add i64) (.var base) (.var mu.1)) fun p0b =>
  .let_ (op2 (.add i64) (.var p0b.1) (.imm 8)) fun p8 =>
  .store (.var v0) (.var p0.1)
    (.store (.var v1) (.var p8.1)
      (.let_ (op2 (.add i64) (.var idx) (.imm 1)) fun idx1 =>
       .let_ (op2 (.shl i64) (.var idx1.1) (.imm 2)) fun sh1 =>
       .let_ (op2 (.add i64) (.var base) (.var sh1.1)) fun q4 =>
       .let_ (op2 (.sub i64) (.var q4.1) (.imm 4)) fun q0 =>
       .let_ (op2 (.add i64) (.var base) (.imm 8)) fun b8 =>
       .let_ (op2 (.add i64) (.var b8.1) (.var sh.1)) fun q8 =>
       .load i32 (.var q0.1) fun r0 =>
       .load i32 (.var q8.1) fun r1 =>
       .ret (.var r0, .var r1, ())))

theorem idxScale_out : Func.memLoad idxScaleProg = fun _ _ p =>
    let base := p.1
    let idx := p.2.1
    let v0 := p.2.2.1
    let v1 := p.2.2.2.1
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun sh =>
    .let_ (op2 (.add i64) (.var base) (.var sh.1)) fun p0 =>
    .let_ (op2 (.mul i64) (.var idx) (.imm 4)) fun mu =>
    .let_ (op2 (.add i64) (.var base) (.var mu.1)) fun p0b =>
    .let_ (op2 (.add i64) (.var p0b.1) (.imm 8)) fun p8 =>
    .store (.var v0) (.var p0.1)
      (.store (.var v1) (.var p8.1)
        (.let_ (op2 (.add i64) (.var idx) (.imm 1)) fun idx1 =>
         .let_ (op2 (.shl i64) (.var idx1.1) (.imm 2)) fun sh1 =>
         .let_ (op2 (.add i64) (.var base) (.var sh1.1)) fun q4 =>
         .let_ (op2 (.sub i64) (.var q4.1) (.imm 4)) fun _q0 =>
         .let_ (op2 (.add i64) (.var base) (.imm 8)) fun b8 =>
         .let_ (op2 (.add i64) (.var b8.1) (.var sh.1)) fun _q8 =>
         .ret (.var v0, .var v1, ()))) := by
  t_kernel_rfl

theorem idxScale_wf : idxScaleProg.Wf := by t_wf_reify
theorem idxScale_opt_wf : (Func.memLoad idxScaleProg).Wf := Func.memLoad_wf idxScale_wf
theorem idxScale_flat : Func.checkTFlat (Func.memLoad idxScaleProg) = true := by t_kernel_rfl

theorem idxScale_spec (Γ : Env) (base idx : BitVec 64) (v0 v1 o0 o1 : BitVec 32)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell (t := i32) (base + idx * 4#64) o0 ⋆
      (cell (t := i32) (base + idx * 4#64 + 8#64) o1 ⋆ R)) m) :
    Func.spec Γ (Func.memLoad idxScaleProg) (base, idx, v0, v1, ()) m
      (fun (r0, r1, ()) m' =>
        r0 = v0 ∧ r1 = v1 ∧
        (cell (t := i32) (base + idx * 4#64) v0 ⋆
          (cell (t := i32) (base + idx * 4#64 + 8#64) v1 ⋆ R)) m')
      (fun _ _ _ _ => False) := by
  apply Func.memLoad_spec idxScale_wf
  dsimp only [Func.spec, Func.wp, idxScaleProg]
  wp_unfold
  have hsh : idx <<< 2 = idx * 4#64 := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftLeft_eq]
  have hsh1 : (idx + 1#64) <<< 2 = idx * 4#64 + 4#64 := by
    have h1 : (idx + 1#64) <<< 2 = (idx + 1#64) * 4#64 := by
      apply BitVec.eq_of_toNat_eq
      simp [Nat.shiftLeft_eq]
      rw [Nat.add_one_mul]
    rw [h1, BitVec.add_mul, BitVec.one_mul]
  have h1c : (1 : BitVec 64) = 1#64 := rfl
  have h4c : (4 : BitVec 64) = 4#64 := rfl
  have h8c : (8 : BitVec 64) = 8#64 := rfl
  rw [h1c, h4c, h8c, hsh, hsh1]
  have hq0 : base + (idx * 4#64 + 4#64) - 4#64 = base + idx * 4#64 := by
    rw [← BitVec.add_assoc, BitVec.add_sub_cancel]
  have hq8 : base + 8#64 + idx * 4#64 = base + idx * 4#64 + 8#64 := by
    rw [BitVec.add_assoc, BitVec.add_comm 8#64 (idx * 4#64), ← BitVec.add_assoc]
  rw [hq0, hq8]
  obtain ⟨hok0, hm1⟩ := store_cell (t := i32) v0 (by decide) hm
  refine ⟨hok0, ?_⟩
  rw [sep_comm] at hm1; simp only [sep_assoc] at hm1
  obtain ⟨hok1, hm2⟩ := store_cell (t := i32) v1 (by decide) hm1
  refine ⟨hok1, ?_⟩
  rw [sep_comm] at hm2; rw [sep_assoc] at hm2; rw [sep_comm R] at hm2; rw [sep_assoc] at hm2
  have hl0 : loadVal _ i32 (base + idx * 4#64) = some v0 := loadVal_cell (by decide) hm2
  have hm2_1 := hm2
  rw [sep_comm] at hm2_1; rw [sep_assoc] at hm2_1
  have hl1 : loadVal _ i32 (base + idx * 4#64 + 8#64) = some v1 :=
    loadVal_cell (by decide) hm2_1
  exact ⟨v0, hl0, v1, hl1, rfl, rfl, hm2⟩

/-! ## 2. `zext 32 64` / `sext 32 64` indices and commutative `idx + base` -/

/-- Reload `vals[zext32 lit]` and commutative `(sext32 idx) + base` after storing/loading. -/
def zextSextProg : Func [i64, i32, i32, i64] [i32, i64] := fun _ _ p =>
  let base := p.1
  let lit32 := p.2.1
  let sidx32 := p.2.2.1
  let v := p.2.2.2.1
  .let_ (op1 (.zext 32 64) (.var lit32)) fun z1 =>
  .let_ (op2 (.shl i64) (.var z1.1) (.imm 2)) fun off1 =>
  .let_ (op2 (.add i64) (.var base) (.var off1.1)) fun ptr1 =>
  .let_ (op1 (.sext 32 64) (.var sidx32)) fun sx1 =>
  .let_ (op2 (.add i64) (.var sx1.1) (.var base)) fun ptr2 =>
  .load i32 (.var ptr1.1) fun a1 =>
  .store (.var v) (.var ptr2.1)
    (.let_ (op1 (.zext 32 64) (.var lit32)) fun z2 =>
     .let_ (op2 (.mul i64) (.var z2.1) (.imm 4)) fun off2 =>
     .let_ (op2 (.add i64) (.var off2.1) (.var base)) fun ptr1b =>
     .let_ (op1 (.sext 32 64) (.var sidx32)) fun sx2 =>
     .let_ (op2 (.add i64) (.var base) (.var sx2.1)) fun ptr2b =>
     .load i32 (.var ptr1b.1) fun a1b =>
     .load i64 (.var ptr2b.1) fun vb =>
     .let_ (op2 (.add i32) (.var a1) (.var a1b)) fun sum =>
     .ret (.var sum.1, .var vb, ()))

theorem zextSext_out : Func.memLoad zextSextProg = fun _ _ p =>
    let base := p.1
    let lit32 := p.2.1
    let sidx32 := p.2.2.1
    let v := p.2.2.2.1
    .let_ (op1 (.zext 32 64) (.var lit32)) fun z1 =>
    .let_ (op2 (.shl i64) (.var z1.1) (.imm 2)) fun off1 =>
    .let_ (op2 (.add i64) (.var base) (.var off1.1)) fun ptr1 =>
    .let_ (op1 (.sext 32 64) (.var sidx32)) fun sx1 =>
    .let_ (op2 (.add i64) (.var sx1.1) (.var base)) fun ptr2 =>
    .load i32 (.var ptr1.1) fun a1 =>
    .store (.var v) (.var ptr2.1)
      (.let_ (op1 (.zext 32 64) (.var lit32)) fun z2 =>
       .let_ (op2 (.mul i64) (.var z2.1) (.imm 4)) fun off2 =>
       .let_ (op2 (.add i64) (.var off2.1) (.var base)) fun _ptr1b =>
       .let_ (op1 (.sext 32 64) (.var sidx32)) fun sx2 =>
       .let_ (op2 (.add i64) (.var base) (.var sx2.1)) fun _ptr2b =>
       .load i32 (.var _ptr1b.1) fun a1b =>
       .let_ (op2 (.add i32) (.var a1) (.var a1b)) fun sum =>
       .ret (.var sum.1, .var v, ())) := by
  t_kernel_rfl

theorem zextSext_wf : (Func.memLoad zextSextProg).Wf := Func.memLoad_wf (by t_wf_reify)

/-! ## 3. Indexed alias invalidation vs same-base disjoint offset preservation -/

/-- Store to `base + (j << 2)` must kill `base + (i << 2)` (may alias `i = j`), while storing
to `(base + (i << 2)) + 8` must preserve `base + (i << 2) + 0`. -/
def idxAliasProg : Func [i64, i64, i64, i64, i64] [i64, i64] := fun _ _ p =>
  let base := p.1
  let i := p.2.1
  let j := p.2.2.1
  let v := p.2.2.2.1
  let w := p.2.2.2.2.1
  .let_ (op2 (.shl i64) (.var i) (.imm 2)) fun si =>
  .let_ (op2 (.add i64) (.var base) (.var si.1)) fun pi =>
  .let_ (op2 (.add i64) (.var pi.1) (.imm 8)) fun pi8 =>
  .let_ (op2 (.shl i64) (.var j) (.imm 2)) fun sj =>
  .let_ (op2 (.add i64) (.var base) (.var sj.1)) fun pj =>
  .load i64 (.var pi.1) fun r0 =>
  .store (.var v) (.var pi8.1)
    (.load i64 (.var pi.1) fun r1 =>
     .store (.var w) (.var pj.1)
       (.load i64 (.var pi.1) fun r2 =>
        .let_ (op2 (.add i64) (.var r0) (.var r1)) fun _ =>
        .ret (.var r1, .var r2, ())))

theorem idxAlias_out : Func.memLoad idxAliasProg = fun _ _ p =>
    let base := p.1
    let i := p.2.1
    let j := p.2.2.1
    let v := p.2.2.2.1
    let w := p.2.2.2.2.1
    .let_ (op2 (.shl i64) (.var i) (.imm 2)) fun si =>
    .let_ (op2 (.add i64) (.var base) (.var si.1)) fun pi =>
    .let_ (op2 (.add i64) (.var pi.1) (.imm 8)) fun pi8 =>
    .let_ (op2 (.shl i64) (.var j) (.imm 2)) fun sj =>
    .let_ (op2 (.add i64) (.var base) (.var sj.1)) fun pj =>
    .load i64 (.var pi.1) fun r0 =>
    .store (.var v) (.var pi8.1)
      (.store (.var w) (.var pj.1)
        (.load i64 (.var pi.1) fun r2 =>
         .let_ (op2 (.add i64) (.var r0) (.var r0)) fun _ =>
         .ret (.var r0, .var r2, ()))) := by
  t_kernel_rfl

theorem idxAlias_wf : (Func.memLoad idxAliasProg).Wf := Func.memLoad_wf (by t_wf_reify)

/-! ## 4. Acyclic `.group` join-block preservation (`full_sort_tmp_sift` pattern) -/

/-- Outer branches load `ar[idx]` and `ar[ch]`, then jump to an acyclic `.group` swap block
that reloads both before storing swapped values back. Both reloads in `.group` are eliminated. -/
def siftJoinProg : Func [i64, i64, i64, .bool] [i32] := fun _ _ p =>
  let ar := p.1
  let idx := p.2.1
  let ch := p.2.2.1
  let cond := p.2.2.2.1
  .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun s0 =>
  .let_ (op2 (.add i64) (.var ar) (.var s0.1)) fun p0 =>
  .let_ (op2 (.shl i64) (.var ch) (.imm 2)) fun s1 =>
  .let_ (op2 (.add i64) (.var ar) (.var s1.1)) fun p1 =>
  .load i32 (.var p0.1) fun a0 =>
  .load i32 (.var p1.1) fun _a1 =>
  .group (sig := [[]])
    (fun (_swap, ()) =>
      .cons (fun () =>
        .load i32 (.var p0.1) fun b0 =>
        .load i32 (.var p1.1) fun b1 =>
        .store (.var b1) (.var p0.1)
          (.store (.var b0) (.var p1.1) (.ret (.var b0, ()))))
      .nil)
    (fun (swap, ()) =>
      .jnz (.var cond) (.jump swap ()) (.ret (.var a0, ())))

theorem siftJoin_out : Func.memLoad siftJoinProg = fun _ _ p =>
    let ar := p.1
    let idx := p.2.1
    let ch := p.2.2.1
    let cond := p.2.2.2.1
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun s0 =>
    .let_ (op2 (.add i64) (.var ar) (.var s0.1)) fun p0 =>
    .let_ (op2 (.shl i64) (.var ch) (.imm 2)) fun s1 =>
    .let_ (op2 (.add i64) (.var ar) (.var s1.1)) fun p1 =>
    .load i32 (.var p0.1) fun a0 =>
    .load i32 (.var p1.1) fun a1 =>
    .group (sig := [[]])
      (fun (_swap, ()) =>
        .cons (fun () =>
          .store (.var a1) (.var p0.1)
            (.store (.var a0) (.var p1.1) (.ret (.var a0, ()))))
        .nil)
      (fun (swap, ()) =>
        .jnz (.var cond) (.jump swap ()) (.ret (.var a0, ()))) := by
  t_kernel_rfl

theorem siftJoin_wf : siftJoinProg.Wf := by t_wf_reify
theorem siftJoin_opt_wf : (Func.memLoad siftJoinProg).Wf := Func.memLoad_wf siftJoin_wf
theorem siftJoin_flat : Func.checkTFlat (Func.memLoad siftJoinProg) = true := by t_kernel_rfl

theorem siftJoin_spec (Γ : Env) (ar idx ch : BitVec 64) (cond : Bool) (v0 v1 : BitVec 32)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell (t := i32) (ar + idx * 4#64) v0 ⋆
      (cell (t := i32) (ar + ch * 4#64) v1 ⋆ R)) m) :
    Func.spec Γ (Func.memLoad siftJoinProg) (ar, idx, ch, cond, ()) m
      (fun (r, ()) m' => r = v0 ∧
        if cond then
          (cell (t := i32) (ar + idx * 4#64) v1 ⋆
            (cell (t := i32) (ar + ch * 4#64) v0 ⋆ R)) m'
        else
          (cell (t := i32) (ar + idx * 4#64) v0 ⋆
            (cell (t := i32) (ar + ch * 4#64) v1 ⋆ R)) m')
      (fun _ _ _ _ => False) := by
  apply Func.memLoad_spec siftJoin_wf
  dsimp only [Func.spec, Func.wp, siftJoinProg]
  wp_unfold
  have h4c : (4 : BitVec 64) = 4#64 := rfl
  have hsh0 : idx <<< 2 = idx * 4#64 := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq]
  have hsh1 : ch <<< 2 = ch * 4#64 := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq]
  rw [hsh0, hsh1]
  have hl0 : loadVal m i32 (ar + idx * 4#64) = some v0 := loadVal_cell (by decide) hm
  have hm_1 := hm
  rw [sep_comm] at hm_1; simp only [sep_assoc] at hm_1
  have hl1 : loadVal m i32 (ar + ch * 4#64) = some v1 := loadVal_cell (by decide) hm_1
  refine ⟨v0, hl0, v1, hl1, ?_⟩
  apply wp_join_group (ts := []) (fun _ m' => cond = true ∧
    (cell (t := i32) (ar + idx * 4#64) v0 ⋆ (cell (t := i32) (ar + ch * 4#64) v1 ⋆ R)) m')
  · intro _ () m' ⟨hct, hm'⟩
    have hl0' : loadVal m' i32 (ar + idx * 4#64) = some v0 := loadVal_cell (by decide) hm'
    have hm'_1 := hm'
    rw [sep_comm] at hm'_1; simp only [sep_assoc] at hm'_1
    have hl1' : loadVal m' i32 (ar + ch * 4#64) = some v1 := loadVal_cell (by decide) hm'_1
    refine ⟨v0, hl0', v1, hl1', ?_⟩
    obtain ⟨hok0, hm1⟩ := store_cell (t := i32) v1 (by decide) hm'
    refine ⟨hok0, ?_⟩
    rw [sep_comm] at hm1; simp only [sep_assoc] at hm1
    obtain ⟨hok1, hm2⟩ := store_cell (t := i32) v0 (by decide) hm1
    refine ⟨hok1, rfl, ?_⟩
    rw [sep_comm] at hm2; simp only [sep_assoc] at hm2
    rw [sep_comm R] at hm2; rw [sep_assoc] at hm2
    simp only [hct, ↓reduceIte, Arg.val]
    exact hm2
  · intro J hJ
    cases cond
    · exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, hm⟩⟩
    · exact ⟨fun _ => hJ () _ ⟨rfl, hm⟩, fun h => absurd h (by decide)⟩

/-! ## 5. Cyclic `.group` loop soundness: self-looping store flushes cached load -/

/-- A cyclic `.group` that stores `v1` to `base + (idx << 2)` and jumps to itself must flush
the pre-entry `store v0` so the loop body reloads from memory. -/
def cyclicGroupProg : Func [i64, i64, i64, i64] [i64] := fun _ _ p =>
  let base := p.1
  let idx := p.2.1
  let v0 := p.2.2.1
  let v1 := p.2.2.2.1
  .let_ (op2 (.shl i64) (.var idx) (.imm 3)) fun off =>
  .let_ (op2 (.add i64) (.var base) (.var off.1)) fun ptr =>
  .store (.var v0) (.var ptr.1)
    (.group (sig := [[.bool]])
      (fun (loop, ()) =>
        .cons (fun b =>
          .load i64 (.var ptr.1) fun x =>
          .jnz (.var b.1)
            (.store (.var v1) (.var ptr.1) (.jump loop (.imm false, ())))
            (.ret (.var x, ())))
        .nil)
      (fun (loop, ()) => .jump loop (.imm true, ())))

theorem cyclicGroup_out : Func.memLoad cyclicGroupProg = cyclicGroupProg := by
  t_kernel_rfl

theorem cyclicGroup_wf : cyclicGroupProg.Wf := by t_wf_reify

theorem cyclicGroup_spec (Γ : Env) (base idx v0 v1 o0 : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell64 (base + idx * 8#64) o0 ⋆ R) m) :
    Func.spec Γ (Func.memLoad cyclicGroupProg) (base, idx, v0, v1, ()) m
      (fun (r, ()) m' => r = v1 ∧ (cell64 (base + idx * 8#64) v1 ⋆ R) m')
      (fun _ _ _ _ => False) := by
  apply Func.memLoad_spec cyclicGroup_wf
  dsimp only [Func.spec, Func.wp, cyclicGroupProg]
  wp_unfold
  have h8 : BitVec.ofNat 64 (8 * idx.toNat) = idx * 8#64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [h8]
  obtain ⟨hok0, hm1⟩ := store_cell64 v0 hm
  refine ⟨hok0, ?_⟩
  apply wp_loop_group (ts := [.bool])
    (fun n (b, ()) m' => n = (if b then 1 else 0) ∧
      (cell64 (base + idx * 8#64) (if b then v0 else v1) ⋆ R) m')
  · intro J n (b, ()) m' hJ ⟨hn, hm'⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hm' ⊢
      wp_unfold
      exact ⟨v1, loadVal_cell64 hm', rfl, hm'⟩
    · simp only [↓reduceIte] at hn hm'
      subst hn
      wp_unfold
      obtain ⟨hok1, hm2⟩ := store_cell64 v1 hm'
      exact ⟨v0, loadVal_cell64 hm', hok1, hJ 0 (false, ()) _ Nat.zero_lt_one ⟨rfl, hm2⟩⟩
  · intro _ hJ
    exact hJ 1 (true, ()) _ ⟨rfl, hm1⟩

/-! ## 6. Axiom audit -/

#print axioms LeanQbe.T.memLoad_wp
#print axioms LeanQbe.T.memLoad_wf
#print axioms LeanQbe.T.Func.memLoad_wf
#print axioms LeanQbe.T.Func.memLoad_spec
#print axioms LeanQbe.T.MemLoadB5Test.idxScale_out
#print axioms LeanQbe.T.MemLoadB5Test.idxScale_spec
#print axioms LeanQbe.T.MemLoadB5Test.zextSext_out
#print axioms LeanQbe.T.MemLoadB5Test.idxAlias_out
#print axioms LeanQbe.T.MemLoadB5Test.siftJoin_out
#print axioms LeanQbe.T.MemLoadB5Test.siftJoin_spec
#print axioms LeanQbe.T.MemLoadB5Test.cyclicGroup_spec

end LeanQbe.T.MemLoadB5Test
