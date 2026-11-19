module

public import LeanQbe.T.DceLemmas
public import LeanQbe.T.MemLoadLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules

/-!
# Tests of `LeanQbe.T.MemLoad`, `Func.deadLoadElim`, and `Func.assumeElim` (`O-M2`)

Tests:
1. `MB5`-style struct-field store-to-load forwarding and disjoint-offset frame preservation
   (`off = 0, 8, 12, 16`, distinct non-overlapping sizes, chained `add`/`sub` wraparound),
   and forwarding to `ret`/`add`, `Func.checkTFlat`, `Func.memLoad_wf`, `Func.memLoad_spec`.
2. Aliasing store (unknown pointer `q` and overlapping `i32` store at `base + 4` inside `i64` at
   `base + 0`) kills overlapping entries while preserving disjoint `base + 16`.
3. `.call` flushes the dominating memory cache; `.jnz` inherits outer cache across both arms.
4. `.group` summaries (`MB5` read-only body preserves cache; disjoint-field body store preserves
   cache; write-aliasing in `bodies` OR group entry `k` flushes cache in `bodies`).
5. Optional `Func.deadLoadElim` drops unused `.load` while keeping used `.load`, and composes
   cleanly with `Func.memLoad`.
6. `Func.assumeElim` rewrites `.jnz c t .hlt → t` and `.jnz c .hlt e → e` (including nested and
   inside `.group`), verified by `Func.assumeElim_wf`, `Func.assumeElim_spec`, `Func.checkTFlat`.
7. Axiom audit (`#print axioms`) confirming only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.MemLoadTest

open LeanQbe.T Std.ExtHashMap

/-! ## 1. `MB5`-style struct fields (`i64`/`i32`/`.bool`/`i64`, chained `add`/`sub`) -/

/-- `store v0 (base+0); store v1 (base+8); store vb (base+12); store v2 (base+16);`
`load x0 (base+0); load x1 (p1 := base+4; p1+4); load x2 (p2 := base+24; p2-8); ret [x0, x1, x2]` -/
def structProg : Func [i64, i64, i32, .bool, i64] [i64, i32, i64] := fun _ _ p =>
  let base := p.1
  let v0 := p.2.1
  let v1 := p.2.2.1
  let vb := p.2.2.2.1
  let v2 := p.2.2.2.2.1
  .let_ (op2 (.add i64) (.var base) (.imm 8)) fun p8 =>
  .let_ (op2 (.add i64) (.var p8.1) (.imm 4)) fun p12 =>
  .let_ (op2 (.add i64) (.var p12.1) (.imm 4)) fun p16 =>
  .store (.var v0) (.var base)
    (.store (.var v1) (.var p8.1)
      (.store (.var vb) (.var p12.1)
        (.store (.var v2) (.var p16.1)
          (.let_ (op2 (.add i64) (.var base) (.imm 4)) fun q4 =>
           .let_ (op2 (.add i64) (.var q4.1) (.imm 4)) fun q8 =>
           .let_ (op2 (.add i64) (.var p16.1) (.imm 8)) fun q24 =>
           .let_ (op2 (.sub i64) (.var q24.1) (.imm 8)) fun q16 =>
           .load i64 (.var base) fun x0 =>
           .load i32 (.var q8.1) fun x1 =>
           .load i64 (.var q16.1) fun x2 =>
           .let_ (op2 (.add i64) (.var x0) (.var x2)) fun sum =>
           .ret (.var sum.1, .var x1, .var x0, ())))))

theorem struct_out : Func.memLoad structProg = fun _ _ p =>
    let base := p.1
    let v0 := p.2.1
    let v1 := p.2.2.1
    let vb := p.2.2.2.1
    let v2 := p.2.2.2.2.1
    .let_ (op2 (.add i64) (.var base) (.imm 8)) fun p8 =>
    .let_ (op2 (.add i64) (.var p8.1) (.imm 4)) fun p12 =>
    .let_ (op2 (.add i64) (.var p12.1) (.imm 4)) fun p16 =>
    .store (.var v0) (.var base)
      (.store (.var v1) (.var p8.1)
        (.store (.var vb) (.var p12.1)
          (.store (.var v2) (.var p16.1)
            (.let_ (op2 (.add i64) (.var base) (.imm 4)) fun _q4 =>
             .let_ (op2 (.add i64) (.var _q4.1) (.imm 4)) fun _q8 =>
             .let_ (op2 (.add i64) (.var p16.1) (.imm 8)) fun q24 =>
             .let_ (op2 (.sub i64) (.var q24.1) (.imm 8)) fun _q16 =>
             .let_ (op2 (.add i64) (.var v0) (.var v2)) fun sum =>
             .ret (.var sum.1, .var v1, .var v0, ()))))) := by
  t_kernel_rfl

theorem struct_wf : structProg.Wf := by t_wf_reify
theorem struct_opt_wf : (Func.memLoad structProg).Wf := Func.memLoad_wf struct_wf
theorem struct_flat : Func.checkTFlat (Func.memLoad structProg) = true := by t_kernel_rfl

theorem struct_spec (Γ : Env) (base v0 : BitVec 64) (v1 : BitVec 32) (vb : Bool) (v2 : BitVec 64)
    (o0 o2 : BitVec 64) (o1 : BitVec 32) (ob : Bool) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell64 base o0 ⋆ (cell (t := i32) (base + 8#64) o1 ⋆
      (cell (t := .bool) (base + 12#64) ob ⋆ (cell64 (base + 16#64) o2 ⋆ R)))) m) :
    Func.spec Γ (Func.memLoad structProg) (base, v0, v1, vb, v2, ()) m
      (fun (r0, r1, r2, ()) m' =>
        r0 = v0 + v2 ∧ r1 = v1 ∧ r2 = v0 ∧
        (cell64 base v0 ⋆ (cell (t := i32) (base + 8#64) v1 ⋆
          (cell (t := .bool) (base + 12#64) vb ⋆ (cell64 (base + 16#64) v2 ⋆ R)))) m')
      (fun _ _ _ _ => False) := by
  apply Func.memLoad_spec struct_wf
  dsimp only [Func.spec, Func.wp, structProg]
  wp_unfold
  have h4 : (4 : BitVec 64) = 4#64 := rfl
  have h8 : (8 : BitVec 64) = 8#64 := rfl
  have hp12 : base + 8#64 + 4#64 = base + 12#64 := by rw [BitVec.add_assoc]; rfl
  have hp16 : base + 8#64 + 4#64 + 4#64 = base + 16#64 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hq8 : base + 4#64 + 4#64 = base + 8#64 := by rw [BitVec.add_assoc]; rfl
  have hq16 : base + 8#64 + 4#64 + 4#64 + 8#64 - 8#64 = base + 16#64 := by
    rw [BitVec.add_sub_cancel]; exact hp16
  rw [h4, h8, hq16, hp16, hp12, hq8]
  obtain ⟨hok0, hm1⟩ := store_cell64 v0 hm
  refine ⟨hok0, ?_⟩
  rw [sep_comm] at hm1; simp only [sep_assoc] at hm1
  obtain ⟨hok1, hm2⟩ := store_cell (t := i32) v1 (by decide) hm1
  refine ⟨hok1, ?_⟩
  rw [sep_comm] at hm2; simp only [sep_assoc] at hm2
  obtain ⟨hokb, hm3⟩ := store_cell (t := .bool) vb (by decide) hm2
  refine ⟨hokb, ?_⟩
  rw [sep_comm] at hm3; simp only [sep_assoc] at hm3
  obtain ⟨hok2, hm4⟩ := store_cell64 v2 hm3
  refine ⟨hok2, ?_⟩
  rw [sep_comm] at hm4; simp only [sep_assoc] at hm4
  rw [sep_comm] at hm4; simp only [sep_assoc] at hm4
  have hl0 : loadVal _ i64 base = some v0 := loadVal_cell64 hm4
  have hm4_1 := hm4
  rw [sep_comm] at hm4_1; simp only [sep_assoc] at hm4_1
  have hl1 : loadVal _ i32 (base + 8#64) = some v1 := loadVal_cell (by decide) hm4_1
  have hm4_2 := hm4_1
  rw [sep_comm] at hm4_2; simp only [sep_assoc] at hm4_2
  rw [sep_comm] at hm4_2; simp only [sep_assoc] at hm4_2
  have hl2 : loadVal _ i64 (base + 16#64) = some v2 := loadVal_cell64 hm4_2
  refine ⟨v0, hl0, v1, hl1, v2, hl2, rfl, rfl, rfl, hm4⟩

/-- Wraparound offset `(base - 8)` vs `(base + 0)` cancels shared `base` across `2^64`. -/
def wrapProg : Func [i64, i64, i64] [i64, i64] := fun _ _ p =>
  let base := p.1
  let v0 := p.2.1
  let v1 := p.2.2.1
  .let_ (op2 (.sub i64) (.var base) (.imm 8)) fun pm8 =>
  .store (.var v0) (.var pm8.1)
    (.store (.var v1) (.var base)
      (.load i64 (.var pm8.1) fun r0 =>
       .load i64 (.var base) fun r1 =>
       .ret (.var r0, .var r1, ())))

theorem wrap_out : Func.memLoad wrapProg = fun _ _ p =>
    let base := p.1
    let v0 := p.2.1
    let v1 := p.2.2.1
    .let_ (op2 (.sub i64) (.var base) (.imm 8)) fun pm8 =>
    .store (.var v0) (.var pm8.1)
      (.store (.var v1) (.var base)
        (.ret (.var v0, .var v1, ()))) := by
  t_kernel_rfl

theorem wrap_wf : (Func.memLoad wrapProg).Wf := Func.memLoad_wf (by t_wf_reify)

/-! ## 2. Aliasing store kills overlapping entries while preserving disjoint entries -/

/-- Store to unknown `q` kills `base + 0`; partial overlapping `i32` store at `base + 4` kills
`i64` at `base + 0` while keeping `i64` at `base + 16` cached! -/
def aliasProg : Func [i64, i64, i64, i32] [i64, i64, i64] := fun _ _ p =>
  let base := p.1
  let q := p.2.1
  let val64 := p.2.2.1
  let val32 := p.2.2.2.1
  .let_ (op2 (.add i64) (.var base) (.imm 4)) fun p4 =>
  .let_ (op2 (.add i64) (.var base) (.imm 16)) fun p16 =>
  .load i64 (.var base) fun a0 =>
  .store (.var val64) (.var q)
    (.load i64 (.var base) fun a1 =>
     .store (.var val64) (.var p16.1)
       (.store (.var val32) (.var p4.1)
         (.load i64 (.var base) fun a2 =>
          .load i64 (.var p16.1) fun a3 =>
          .let_ (op2 (.add i64) (.var a0) (.var a1)) fun _s =>
          .ret (.var a1, .var a2, .var a3, ()))))

theorem alias_out : Func.memLoad aliasProg = fun _ _ p =>
    let base := p.1
    let q := p.2.1
    let val64 := p.2.2.1
    let val32 := p.2.2.2.1
    .let_ (op2 (.add i64) (.var base) (.imm 4)) fun p4 =>
    .let_ (op2 (.add i64) (.var base) (.imm 16)) fun p16 =>
    .load i64 (.var base) fun a0 =>
    .store (.var val64) (.var q)
      (.load i64 (.var base) fun a1 =>
       .store (.var val64) (.var p16.1)
         (.store (.var val32) (.var p4.1)
           (.load i64 (.var base) fun a2 =>
            .let_ (op2 (.add i64) (.var a0) (.var a1)) fun _s =>
            .ret (.var a1, .var a2, .var val64, ())))) := by
  t_kernel_rfl

theorem alias_wf : (Func.memLoad aliasProg).Wf := Func.memLoad_wf (by t_wf_reify)

/-! ## 3. `.call` flushes cache and `.jnz` inherits outer cache across branches -/

def callJnzProg : Func [i64, .bool, i64] [i64] := fun _ _ p =>
  let base := p.1
  let c := p.2.1
  let v := p.2.2.1
  .store (.var v) (.var base)
    (.jnz (.var c)
      (.load i64 (.var base) fun r1 => .ret (.var r1, ()))
      (.call "barrier" (as := []) (bs := [i64]) () fun _ =>
       .load i64 (.var base) fun r2 =>
       .ret (.var r2, ())))

theorem callJnz_out : Func.memLoad callJnzProg = fun _ _ p =>
    let base := p.1
    let c := p.2.1
    let v := p.2.2.1
    .store (.var v) (.var base)
      (.jnz (.var c)
        (.ret (.var v, ()))
        (.call "barrier" (as := []) (bs := [i64]) () fun _ =>
         .load i64 (.var base) fun r2 =>
         .ret (.var r2, ()))) := by
  t_kernel_rfl

theorem callJnz_wf : (Func.memLoad callJnzProg).Wf := Func.memLoad_wf (by t_wf_reify)

/-! ## 4. `.group` summaries (`MB5` read-only body, disjoint write, entry-kill soundness) -/

/-- `MB5`-style struct fields stored before read-only `.group`: both `entry` and `bodies` keep
and forward `(base+0)` and `(base+8)` directly without reloading from memory. -/
def mb5GroupProg : Func [i64, i64, i64, .bool] [i64] := fun _ _ p =>
  let base := p.1
  let v0 := p.2.1
  let v8 := p.2.2.1
  let cond := p.2.2.2.1
  .let_ (op2 (.add i64) (.var base) (.imm 8)) fun p8 =>
  .store (.var v0) (.var base)
    (.store (.var v8) (.var p8.1)
      (.group (sig := [[i64]])
        (fun (_blk, ()) =>
          .cons (fun arg =>
            .load i64 (.var base) fun r0 =>
            .load i64 (.var p8.1) fun r8 =>
            .let_ (op2 (.add i64) (.var r0) (.var r8)) fun s1 =>
            .let_ (op2 (.add i64) (.var s1.1) (.var arg.1)) fun s2 =>
            .ret (.var s2.1, ()))
          .nil)
        (fun (blk, ()) =>
          .load i64 (.var base) fun r =>
          .jnz (.var cond) (.jump blk (.var r, ())) (.ret (.var r, ())))))

theorem mb5Group_out : Func.memLoad mb5GroupProg = fun _ _ p =>
    let base := p.1
    let v0 := p.2.1
    let v8 := p.2.2.1
    let cond := p.2.2.2.1
    .let_ (op2 (.add i64) (.var base) (.imm 8)) fun p8 =>
    .store (.var v0) (.var base)
      (.store (.var v8) (.var p8.1)
        (.group (sig := [[i64]])
          (fun (_blk, ()) =>
            .cons (fun arg =>
              .let_ (op2 (.add i64) (.var v0) (.var v8)) fun s1 =>
              .let_ (op2 (.add i64) (.var s1.1) (.var arg.1)) fun s2 =>
              .ret (.var s2.1, ()))
            .nil)
          (fun (blk, ()) =>
            .jnz (.var cond) (.jump blk (.var v0, ())) (.ret (.var v0, ()))))) := by
  t_kernel_rfl

theorem mb5Group_wf : mb5GroupProg.Wf := by t_wf_reify
theorem mb5Group_opt_wf : (Func.memLoad mb5GroupProg).Wf := Func.memLoad_wf mb5Group_wf
theorem mb5Group_flat : Func.checkTFlat (Func.memLoad mb5GroupProg) = true := by t_kernel_rfl

/-- Group whose body writes disjoint `(base+16)` keeps `(base+0)` alive across `bodies` and `k`. -/
def groupDisjWriteProg : Func [i64, i64, i64] [i64] := fun _ _ p =>
  let base := p.1
  let v0 := p.2.1
  let v16 := p.2.2.1
  .let_ (op2 (.add i64) (.var base) (.imm 16)) fun p16 =>
  .store (.var v0) (.var base)
    (.group (sig := [[i64]])
      (fun (_blk, ()) =>
        .cons (fun _ =>
          .store (.var v16) (.var p16.1)
            (.load i64 (.var base) fun r0 => .ret (.var r0, ())))
        .nil)
      (fun (blk, ()) =>
        .load i64 (.var base) fun r0 => .jump blk (.var r0, ())))

theorem groupDisjWrite_out : Func.memLoad groupDisjWriteProg = fun _ _ p =>
    let base := p.1
    let v0 := p.2.1
    let v16 := p.2.2.1
    .let_ (op2 (.add i64) (.var base) (.imm 16)) fun p16 =>
    .store (.var v0) (.var base)
      (.group (sig := [[i64]])
        (fun (_blk, ()) =>
          .cons (fun _ =>
            .store (.var v16) (.var p16.1) (.ret (.var v0, ())))
          .nil)
        (fun (blk, ()) => .jump blk (.var v0, ()))) := by
  t_kernel_rfl

/-- Group soundness: `bodies` is read-only at `base`, while entry `k` writes `v1` to `base`
before jumping to `blk`. Cache in `bodies` MUST be flushed so `bodies` reloads `v1`, NOT `v0`. -/
def groupEntryKillProg : Func [i64, i64, i64] [i64] := fun _ _ p =>
  let base := p.1
  let v0 := p.2.1
  let v1 := p.2.2.1
  .store (.var v0) (.var base)
    (.group (sig := [[i64]])
      (fun (_blk, ()) =>
        .cons (fun _ => .load i64 (.var base) fun r => .ret (.var r, ())) .nil)
      (fun (blk, ()) =>
        .store (.var v1) (.var base) (.jump blk (.var v1, ()))))

theorem groupEntryKill_out : Func.memLoad groupEntryKillProg = groupEntryKillProg := by
  t_kernel_rfl

theorem groupEntryKill_wf : groupEntryKillProg.Wf := by t_wf_reify

theorem groupEntryKill_spec (Γ : Env) (base v0 v1 x0 : BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell64 base x0 ⋆ R) m) :
    Func.spec Γ (Func.memLoad groupEntryKillProg) (base, v0, v1, ()) m
      (fun (r, ()) m' => r = v1 ∧ (cell64 base v1 ⋆ R) m')
      (fun _ _ _ _ => False) := by
  apply Func.memLoad_spec groupEntryKill_wf
  dsimp only [Func.spec, Func.wp, groupEntryKillProg]
  obtain ⟨hok0, hm1⟩ := store_cell64 v0 hm
  refine ⟨hok0, ?_⟩
  apply wp_join_group (fun _ m' => (cell64 base v1 ⋆ R) m')
  · intro _ _ m' hcm'
    exact wp_load_cell64 hcm' ⟨rfl, hcm'⟩
  · intro J hJ
    obtain ⟨hok1, hm2⟩ := store_cell64 v1 hm1
    exact ⟨hok1, hJ (v1, ()) _ hm2⟩

/-! ## 5. Optional `Func.deadLoadElim` + composition with `Func.memLoad` -/

def deadLoadProg : Func [i64] [i64] := fun _ _ p =>
  let ptr := p.1
  .load i64 (.var ptr) fun _unused =>
  .load i64 (.var ptr) fun used =>
  .ret (.var used, ())

theorem deadLoad_out : Func.deadLoadElim deadLoadProg = fun _ _ p =>
    let ptr := p.1
    .load i64 (.var ptr) fun used =>
    .ret (.var used, ()) := by
  t_kernel_rfl

theorem deadLoadProg_wf : deadLoadProg.Wf := by t_wf_reify
theorem deadLoad_opt_wf : (Func.deadLoadElim deadLoadProg).Wf :=
  Func.deadLoadElim_wf deadLoadProg_wf
theorem deadLoad_flat : Func.checkTFlat (Func.deadLoadElim deadLoadProg) = true := by t_kernel_rfl

theorem deadLoad_spec (Γ : Env) (ptr v : BitVec 64) (m : Mem 64)
    (hl : loadVal m i64 ptr = some v) :
    Func.spec Γ (Func.deadLoadElim deadLoadProg) (ptr, ()) m
      (fun (r, ()) m' => r = v ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.deadLoadElim_spec deadLoadProg_wf
  dsimp only [Func.spec, Func.wp, deadLoadProg]
  exact ⟨v, hl, v, hl, rfl, rfl⟩

/-- Composing `Func.memLoad` then `Func.deadLoadElim` drops redundant reloads cleanly. -/
theorem memThenDead_wf : (Func.deadLoadElim (Func.memLoad aliasProg)).Wf :=
  Func.deadLoadElim_wf alias_wf

/-! ## 6. `AssumeElim` (`jnz c t .hlt → t`, `jnz c .hlt e → e`) -/

def assumeProg : Func [i64, .bool, .bool] [i64] := fun _ _ p =>
  let x := p.1
  let c1 := p.2.1
  let c2 := p.2.2.1
  .jnz (.var c1)
    (.jnz (.var c2) .hlt (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun r => .ret (.var r.1, ())))
    .hlt

theorem assume_out : Func.assumeElim assumeProg = fun _ _ p =>
    let x := p.1
    .let_ (op2 (.add i64) (.var x) (.imm 1)) fun r => .ret (.var r.1, ()) := by
  t_kernel_rfl

theorem assumeProg_wf : assumeProg.Wf := by t_wf_reify
theorem assume_opt_wf : (Func.assumeElim assumeProg).Wf := Func.assumeElim_wf assumeProg_wf
theorem assume_flat : Func.checkTFlat (Func.assumeElim assumeProg) = true := by t_kernel_rfl

theorem assume_spec (Γ : Env) (x : BitVec 64) (c1 c2 : Bool) (m : Mem 64)
    (h1 : c1 = true) (h2 : c2 = false) :
    Func.spec Γ (Func.assumeElim assumeProg) (x, c1, c2, ()) m
      (fun (r, ()) m' => r = x + 1#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.assumeElim_spec assumeProg_wf
  dsimp only [Func.spec, Func.wp, assumeProg]
  rw [h1, h2]
  exact ⟨fun _ => ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl⟩⟩,
         fun h => absurd h (by decide)⟩

def assumeGroupProg : Func [.bool, i64] [i64] := fun _ _ p =>
  let c := p.1
  let x := p.2.1
  .group (sig := [[i64]])
    (fun (_blk, ()) => .cons (fun y => .jnz (.var c) (.ret (.var y.1, ())) .hlt) .nil)
    (fun (blk, ()) => .jnz (.var c) .hlt (.jump blk (.var x, ())))

theorem assumeGroup_out : Func.assumeElim assumeGroupProg = fun _ _ p =>
    let x := p.2.1
    .group (sig := [[i64]])
      (fun (_blk, ()) => .cons (fun y => .ret (.var y.1, ())) .nil)
      (fun (blk, ()) => .jump blk (.var x, ())) := by
  t_kernel_rfl

theorem assumeGroup_wf : (Func.assumeElim assumeGroupProg).Wf := Func.assumeElim_wf (by t_wf_reify)

/-! ## 7. Axiom audit -/

#print axioms LeanQbe.T.memLoad_wp
#print axioms LeanQbe.T.memLoad_wf
#print axioms LeanQbe.T.Func.memLoad_wf
#print axioms LeanQbe.T.Func.memLoad_spec
#print axioms LeanQbe.T.Func.deadLoadElim_wf
#print axioms LeanQbe.T.Func.deadLoadElim_spec
#print axioms LeanQbe.T.assumeElim_wp
#print axioms LeanQbe.T.assumeElim_wf
#print axioms LeanQbe.T.Func.assumeElim_wf
#print axioms LeanQbe.T.Func.assumeElim_spec
#print axioms LeanQbe.T.MemLoadTest.struct_out
#print axioms LeanQbe.T.MemLoadTest.struct_opt_wf
#print axioms LeanQbe.T.MemLoadTest.struct_flat
#print axioms LeanQbe.T.MemLoadTest.struct_spec
#print axioms LeanQbe.T.MemLoadTest.alias_out
#print axioms LeanQbe.T.MemLoadTest.mb5Group_out
#print axioms LeanQbe.T.MemLoadTest.groupEntryKill_spec
#print axioms LeanQbe.T.MemLoadTest.deadLoad_spec
#print axioms LeanQbe.T.MemLoadTest.assume_out
#print axioms LeanQbe.T.MemLoadTest.assume_spec

end LeanQbe.T.MemLoadTest
