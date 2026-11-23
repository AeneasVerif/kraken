module

public import LeanQbe.T.Examples.Kissat.Full2
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena

/-!
# Kissat `D-Full` Conflict Analysis, OTFS & Eager Subsumption Helpers (Part 1)

Builds on `Full2` and `FullInv2` (`FullWitnessInv`, `FullCoreInv`) to provide:
1. Strictly `scoped` `FullAnalyzeTactics` adapters for `FullMem`, `c0_steps`, and bitwise leaves.
2. `FullAnalyzeSpecs`: canonical shared invariants (`FullLitMarksClear`, `FullArenaVarsNodup`,
   `FullLastLearnedWf`, `FullExtScratchOk`, `FullSparseInv`, `AnaWorkInv`,
   `FullWitnessCutInv`, `FullCoreCutInv`, `FullConflOk`), callee contracts, and Stage-4
   analysis `Spec` contracts.
3. Core / OTFS-cut / arena transition lemmas (`hdrBitsUpdate_preserves_fullWitnessCut`,
   `arenaBumpUsage_preserves_fullWitnessCut`, `clearRed_preserves_fullWitnessCut`,
   `inPlaceShrink_preserves_fullArena`, `markGarb_preserves_fullWitnessCut`,
   `swapCl_preserves_fullWitnessCut`, `chronoBacktrack_cut_to_fullCore`,
   `unsat_of_level0_bin_conflict`, `unsat_of_level0_conflict`, `anaWorkInv_step`,
   `clear_ana_restores_marksClear`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

/-! ## 1. Strictly scoped tactic & bitvector helpers (`FullAnalyzeTactics`) -/

namespace FullAnalyzeTactics

open scoped FullArenaTactics

theorem fa_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem fa_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem fa_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "fa_strip" : tactic =>
  `(tactic| first | apply fa_strip_32_64 | apply fa_strip_8_32 | apply fa_strip_8_64)

scoped macro "fa_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)

scoped macro "fa_steps" : tactic =>
  `(tactic| (
      (try fa_unmdata)
      (repeat fa_strip)
      c0_steps
      repeat (any_goals (fa_strip; repeat fa_strip); c0_steps)))

private theorem mask27_bit : ∀ i : Fin 32, (0x07FFFFFF#32)[i.val] = decide (i.val < 27) :=
  by decide
private theorem mask19_bit : ∀ i : Fin 32, (0x00080000#32)[i.val] = decide (i.val = 19) :=
  by decide
private theorem maskN22_bit : ∀ i : Fin 32, (0xFFBFFFFF#32)[i.val] = decide (i.val ≠ 22) :=
  by decide
private theorem mask23_bit : ∀ i : Fin 32, (0x00800000#32)[i.val] = decide (i.val = 23) :=
  by decide
private theorem mask31_bit : ∀ i : Fin 32, (0x80000000#32)[i.val] = decide (i.val = 31) :=
  by decide
private theorem maskLo31_bit : ∀ i : Fin 32, (0x7FFFFFFF#32)[i.val] = decide (i.val < 31) :=
  by decide

theorem bv32_mask_usage_garb (hdr u : BitVec 32) :
    (((hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)) &&& 0x00080000#32) =
      (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft,
    mask27_bit ⟨i, hi⟩, mask19_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_mask_usage_shrk (hdr u : BitVec 32) :
    (((hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)) &&& 0x00800000#32) =
      (hdr &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft,
    mask27_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bv32_or_shrk_garb (hdr : BitVec 32) :
    ((hdr ||| 0x00800000#32) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, mask19_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_or_shrk_shrk (hdr : BitVec 32) :
    ((hdr ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := by
  intro h; have h23 := congrArg (·[23]) h
  revert h23; simp [show (0x00800000#32)[23] = true from rfl]

theorem bv32_clear_red_garb (hdr : BitVec 32) :
    ((hdr &&& 0xFFBFFFFF#32) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, maskN22_bit ⟨i, hi⟩, mask19_bit ⟨i, hi⟩]
  by_cases h19 : i = 19 <;> simp [h19]

theorem bv32_clear_red_shrk (hdr : BitVec 32) :
    ((hdr &&& 0xFFBFFFFF#32) &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, maskN22_bit ⟨i, hi⟩, mask23_bit ⟨i, hi⟩]
  by_cases h23 : i = 23 <;> simp [h23]

theorem bin_rsn_mask_props {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    let rsn : BitVec 32 := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) ≠ 0#32 ∧
      (rsn &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  intro rsn
  have hbit31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by omega : l.toNat < 2 ^ 31)]; rfl
  have hand_hi : (rsn &&& 0x80000000#32) = 0x80000000#32 := by
    ext i hi; simp only [rsn, BitVec.getElem_and, BitVec.getElem_or, mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31 <;> simp [h31]
  have hand_lo : (rsn &&& 0x7FFFFFFF#32) = l := by
    ext i hi
    simp only [rsn, BitVec.getElem_and, BitVec.getElem_or, mask31_bit ⟨i, hi⟩,
      maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hbit31]
    · simp [h31, show i < 31 by omega]
  refine ⟨?_, ?_, congrArg BitVec.toNat hand_lo⟩
  · intro heq; have hnat := congrArg (fun x => (x &&& 0x7FFFFFFF#32).toNat) heq
    rw [hand_lo] at hnat
    have hff : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := rfl
    rw [hff] at hnat; omega
  · rw [hand_hi]; decide

theorem bv32_lit_lo31_props {l : BitVec 32} (hl : l.toNat < 2 ^ 31) :
    (l &&& 0x7FFFFFFF#32) = l ∧ ((l &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
      (l &&& 0x80000000#32) = 0#32 := by
  have hb31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt hl]; rfl
  have hlo : (l &&& 0x7FFFFFFF#32) = l := by
    ext i hi; simp only [BitVec.getElem_and, maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hb31]
    · simp [show i < 31 by omega]
  have hhi : (l &&& 0x80000000#32) = 0#32 := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero, mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hb31]
    · simp [h31]
  exact ⟨hlo, by rw [hlo]; exact hhi, hhi⟩

theorem bv64_confl_ref_u32 {r : BitVec 64} (hr : r.toNat < 2 ^ 31 - 1) :
    (r.setWidth 32).toNat = r.toNat ∧ r.setWidth 32 ≠ 0xFFFFFFFF#32 ∧
    (r.setWidth 32 &&& 0x80000000#32) = 0#32 := by
  have hto : (r.setWidth 32).toNat = r.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hto, fun heq => by
    have := congrArg BitVec.toNat heq; rw [hto] at this
    have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega, ?_⟩
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases h31 : i = 31
  · subst h31
    have hb : (r.setWidth 32)[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, hto, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (by omega : r.toNat < 2 ^ 31)]; rfl
    simp [hb]
  · simp [mask31_bit ⟨i, hi⟩, h31]

theorem bv32_lit_neq_ff {l : BitVec 32} (hl : l.toNat < 2 ^ 31 - 1) :
    l ≠ 0xFFFFFFFF#32 := fun h => by
  have := congrArg BitVec.toNat h
  have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega

theorem list_set_congr {α : Type} {xs : List α} {i j : Nat} {v w : α}
    (hij : i = j) (hvw : v = w) : xs.set i v = xs.set j w := by subst hij hvw; rfl

theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem ofNat64_pos {n : Nat} (h : ¬ BitVec.ofNat 64 n = 0#64) : 0 < n := by
  cases n with | zero => exact absurd rfl h | succ _ => omega

theorem ofNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) (h : BitVec.ofNat 64 n = 0#64) : n = 0 := by
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using congrArg BitVec.toNat h

theorem ofNat64_eq_one {n : Nat} (hn : n < 2 ^ 64) (h : BitVec.ofNat 64 n = 1#64) : n = 1 := by
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using congrArg BitVec.toNat h

theorem getElem_eq_of_idx {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (h : i = j) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

attribute [scoped bv_c0] bv32_lshr_1 Bool.true_eq_false

@[scoped bv_c0] theorem bv32_mask_lo31_toNat (x : BitVec 32) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat % 2 ^ 31 := by
  simpa [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod x.toNat 31

@[scoped bv_c0] theorem bv32_mask_glue19_toNat (x : BitVec 32) :
    (x &&& 0x7FFFF#32).toNat = x.toNat % 2 ^ 19 := by
  simpa [BitVec.toNat_and, show (0x7FFFF#32).toNat = 2 ^ 19 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod x.toNat 19

@[scoped bv_c0] theorem i8_sext32_zero : (0#8 : BitVec 8).signExtend 32 = 0#32 := rfl
@[scoped bv_c0] theorem u8_zext32_zero : (0#8 : BitVec 8).setWidth 32 = 0#32 := rfl

@[scoped bv_c0] theorem i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (by revert v; decide)

@[scoped bv_c0] theorem u8_zext32_eq0_prop (v : BitVec 8) :
    (v.setWidth 32 = 0#32) = (v = 0#8) := propext (by revert v; decide)

@[scoped c0_load] theorem c0_load_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pTmp = some (s.core.tmp[0]'hi) := by
  simpa using FullArenaTactics.load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem c0_store_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
    (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
      (storeMem m i32 c.pTmp v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

@[scoped c0_load] theorem c0_load_full_tmp1 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'hi) := by
  simpa using FullArenaTactics.load_full_tmp (i := 1) hi hm

@[scoped c0_store] theorem c0_store_full_tmp1 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 1 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
    (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
      (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 1) v hi hm

end FullAnalyzeTactics

open FullAnalyzeTactics
open scoped FullArenaTactics FullAnalyzeTactics

/-! ## 2. Canonical shared invariants, OTFS cut invariant & `FullAnalyzeSpecs` -/

namespace FullAnalyzeSpecs

/-- Both variable analysis marks (`mrk[0 ..< c.max_vars)`) and literal marks
(`lit_mark[0 ..< 2 * c.max_vars)`) are cleared. -/
@[expose] def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

theorem FullLitMarksClear.to_marks {c : FullCfg} {s : FullState}
    (h : FullLitMarksClear c s) (hlen : s.core.cur_vars ≤ c.max_vars) : FullMarksClear s :=
  fun v hv => h.1 v (by omega)

/-- Per-clause variable distinctness across live arena clauses. -/
@[expose] def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- All 8 eager-subsumption `last_learned` slots are either `0xFFFFFFFF#32` or a current
arena clause block reference. -/
@[expose] def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8, let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Extended scratch invariants preserved across CDCL/inprocessing. -/
@[expose] def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Canonical sparse 2WL CDCL solver invariant. -/
@[expose] def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
    FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Consistency between nonzero variable marks in `mrk[0 ..< c.max_vars)` and `work_stk1`
maintained across `full_analyze_lit` / `full_clear_ana`. -/
@[expose] def AnaWorkInv (c : FullCfg) (s : FullState) : Prop :=
  s.core.min_clr_len ≤ s.core.cur_vars ∧
  ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat).Nodup ∧
  (∀ k < s.core.min_clr_len,
    let w := (s.scratch.work_stk1[k]?.getD 0#32).toNat
    w < s.core.cur_vars ∧ s.core.mrk[w]?.getD 0#8 ≠ 0#8) ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    v < s.core.cur_vars ∧ ∃ k < s.core.min_clr_len,
      (s.scratch.work_stk1[k]?.getD 0#32).toNat = v)

/-- Reason-cut generalization of `FullWitnessInv`: `reason_inv` and `reason_lit_mem` hold at every
trail index `idx < k.trail_end` with `idx < cut` or level `< k.cur_level`. -/
structure FullWitnessCutInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (k : FullCoreState) : Prop where
  ext_sound : ExtUnsatSound F0 k.cur_vars F_cur
  inconsistent_sound : k.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat
  arena : FullArenaClausesInv c F_cur k
  watches : ModeWatchesInv F_cur k
  cur_level_le : k.cur_level ≤ k.trail_end
  trail_lits_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars
  trail_vars_nodup : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0#8 ∨ k.vals[l]?.getD 0#8 = 1#8 ∨ k.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level
  dec_earliest : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
    (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    (0 < (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      k.rsns[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) → j ≤ i
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∃ i < k.trail_end, (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(k.trl[i]?.getD 0#32).toNat])
  trail_pos_inv : ∀ i < k.trail_end,
    (k.trail_pos[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
  level0_rsn_none : ∀ idx < k.trail_end,
    (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  frame_trail_lt : ∀ L ≤ k.cur_level, (k.frame_trail[L]?.getD 0#32).toNat ≤ k.trail_end
  frame_trail_mono : ∀ L1 L2, L1 ≤ L2 → L2 ≤ k.cur_level →
    (k.frame_trail[L1]?.getD 0#32).toNat ≤ (k.frame_trail[L2]?.getD 0#32).toNat
  frame_trail_before_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∀ i < (k.frame_trail[L]?.getD 0#32).toNat,
      (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < L
  frame_dec_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    (k.frame_dec[L]?.getD 0#32).toNat < 2 * k.cur_vars
  reason_inv : ∀ idx < k.trail_end,
    (idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
        ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
      else
        rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
          q = p ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (k.lvl[q / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
  reason_lit_mem : ∀ idx < k.trail_end,
    (idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      p ∈ fullArenaClauseLitsCore k rsn.toNat

/-- Cut-generalized sparse invariant bundling `FullLitMarksClear`, `FullArenaVarsNodup`, and
`FullExtScratchOk`. -/
private structure FullCoreCutInv
    (c : FullCfg) (F0 : CNF Nat) (cut : Nat) (s : FullState) : Prop where
  lengths : s.LengthsOk c
  dense0 : s.core.dense_mode = 0#64
  cut_le : cut ≤ s.core.trail_end
  marks : FullLitMarksClear c s
  vars_nodup : FullArenaVarsNodup s
  ext_ok : FullExtScratchOk c s
  witness : ∃ F_cur, FullWitnessCutInv c F0 F_cur cut s.core

/-- Conflict readiness for `full_one_lit_confl`, `full_deduce_1uip`, and `full_analyze`. -/
@[expose] def FullConflOk (F_cur : List (List Nat)) (cut : Nat) (s : FullState) : Prop :=
  if s.core.confl_type = 1#64 then
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
    ((s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = s.core.confl_lit0.toNat ^^^ 1) ∧
    ((s.core.lvl[s.core.confl_lit1.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = s.core.confl_lit1.toNat ^^^ 1) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])
  else
    s.core.confl_ref.toNat < 2 ^ 31 - 1 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      ((s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level →
        ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)

/-! ### Callee specifications (`Full1`, `Full2`) -/

@[expose]
def fullUnwatchLargeWeakSpec : Spec [i64, i32, i32] [] := fun (h, _lit, _cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wusable' m',
      let s' : FullState :=
        { s with core :=
          { s.core with wvec := wvec', wstk := wstk', wusable := wusable' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullUnwatchLargeSpec : Spec [i64, i32, i32] [] := fun (h, lit, _cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wusable' m',
      let s' : FullState :=
        { s with core :=
          { s.core with wvec := wvec', wstk := wstk', wusable := wusable' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
        fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with wvec := wvec', wstk := wstk',
                                  wlen := wlen', wusable := wusable' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
          (∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * s.core.cur_vars →
            fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
            ∀ k < fullWatchSize s lit.toNat,
              s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
                s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          (s.core.cur_vars * 2 ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
            s'.core = s.core ∨ wusable' = 0#64)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullWstackDefragSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → WatchStackLayout s'.core → (1 ≤ s.core.wlen → 1 ≤ wlen') →
      (∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    if s.core.cur_level ≤ target_lvl.toNat then
      Q () m
    else
      ∀ vals' lvl' rsns' trl' tp' te' prop' unass' sc' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                trail_end := te', propagated := prop', cur_level := target_lvl.toNat,
                unassigned := unass' }
            scratch := sc' }
        s'.LengthsOk c → te' ≤ s.core.trail_end → prop' ≤ te' →
        s'.core.fuel = s.core.fuel → sc'.last_learned = s.scratch.last_learned →
        sc'.extend_len = s.scratch.extend_len → sc'.work_stk2 = s.scratch.work_stk2 →
        (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
        ((∃ F0 F_cur, FullWitnessCutInv c F0 F_cur 0 s.core) →
          (∀ l < 2 * s.core.cur_vars,
            vals'[l]?.getD 0#8 =
              if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
                s.core.vals[l]?.getD 0#8 else 0#8) ∧
          (∀ v < s.core.cur_vars,
            lvl'[v]?.getD 0#32 =
              if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat then
                s.core.lvl[v]?.getD 0#32 else 0#32)) →
        (∀ F0 F_cur, FullWitnessCutInv c F0 F_cur 0 s.core → FullWitnessInv c F0 F_cur s'.core) →
        (FullMem c s' ⋆ R) m' → Q () m'

@[expose]
def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] := fun (h, lit, rsn, alvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if c.max_vars ≤ s.core.trail_end ∨ s.core.cur_vars ≤ lit.toNat / 2 ∨
       s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let v := lit.toNat / 2
      let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
      let unfl' := if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed
      ∀ fl' unass' phases' m', fl'.length = c.max_vars → phases'.length = c.max_vars →
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                flags := fl', lvl := s.core.lvl.set v alvl, rsns := s.core.rsns.set v rsn'
                trl := s.core.trl.set s.core.trail_end lit
                trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                trail_end := s.core.trail_end + 1, unassigned := unass', unflushed := unfl' }
            scratch := { s.scratch with phases := phases' } }
        (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullScratchVarVoidSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ sc' m', sc'.LengthsOk c → sc'.last_learned = s.scratch.last_learned →
      sc'.extend_len = s.scratch.extend_len →
      (FullMem c { s with scratch := sc' } ⋆ R) m' → Q () m'

@[expose] def fullScratchVoidSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ sc' m', sc'.LengthsOk c → sc'.last_learned = s.scratch.last_learned →
      sc'.extend_len = s.scratch.extend_len →
      (FullMem c { s with scratch := sc' } ⋆ R) m' → Q () m'

@[expose] def fullScratchEmaSpec : Spec [i64, i64] [] := fun (h, _g, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ sc' m', sc'.LengthsOk c → sc'.last_learned = s.scratch.last_learned →
      sc'.extend_len = s.scratch.extend_len →
      (FullMem c { s with scratch := sc' } ⋆ R) m' → Q () m'

abbrev fullBumpVarSpec := fullScratchVarVoidSpec
abbrev fullQueueMtfSpec := fullScratchVarVoidSpec
abbrev fullBumpDecaySpec := fullScratchVoidSpec
abbrev fullTickRelSpec := fullScratchVoidSpec
abbrev fullEmaUpdateSpec := fullScratchEmaSpec

@[expose] def fullBumpAnalyzedSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ AnaWorkInv c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' mcl' sc' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → AnaWorkInv c s' →
      sc'.last_learned = s.scratch.last_learned → sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk2 = s.scratch.work_stk2 → (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullMinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ 1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    (∀ j < s.core.tmp_len,
      let l := (s.core.tmp[j]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (1 ≤ j → 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level)) ∧
    ((s.core.tmp.take s.core.tmp_len).map (fun x => x.toNat / 2)).Nodup ∧
    (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat))) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mclr' mcl' mcf' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp', tmp_len := tl', mrk := mrk',
                                min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }
          scratch := sc' }
      s'.LengthsOk c → FullSparseInv c F0 s' → s'.core.fuel = s.core.fuel →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      (∀ j < tl',
        let l := (tmp'[j]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (1 ≤ j → 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level)) →
      ((tmp'.take tl').map (fun x => x.toNat / 2)).Nodup →
      (∀ F_cur, FullWitnessInv c F0 F_cur s'.core →
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullAddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullCoreInv c F0 s ∧ len.toNat ≤ s.core.cur_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat)))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then
        Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r wvec' wstk' wlen' wu' nb' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                    wusable := wu', num_binary := nb' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          FullCoreInv c F0 s' → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wu' fred' ni' nr' wsort' m',
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          (r = 0xFFFFFFFF#64 →
            let s' : FullState :=
              { s with
                core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                      wstk := wstk', wlen := wlen', wusable := wu' }
                scratch := { s.scratch with wsort := wsort' } }
            FullCoreInv c F0 s' ∧ s'.core.fuel = s.core.fuel ∧ (FullMem c s' ⋆ R) m') →
          (r = BitVec.ofNat 64 s.core.arena_len →
            alen' = s.core.arena_len + 3 + len.toNat ∧
            let s' : FullState :=
              { s with
                core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                      wstk := wstk', wlen := wlen', wusable := wu',
                                      first_reducible := fred', num_irred := ni',
                                      num_redundant := nr' }
                scratch := { s.scratch with wsort := wsort' } }
            FullCoreInv c F0 s' ∧ s'.core.fuel = s.core.fuel ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat ∧
            (FullMem c s' ⋆ R) m') →
          Q (r, ()) m'

@[expose] def fullReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ rr s' m',
      s'.LengthsOk c → s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (rr = 20#64 ∨ rr = 1#64 ∨ rr = 0#64) →
      (rr = 20#64 → F0.Unsat) →
      (rr = 1#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level ≤ s.core.cur_level ∧
        (s'.core.cur_level = s.core.cur_level →
          ∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 ≠ 0#8 →
            s'.core.vals[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8 ∧
            s'.core.lvl[l / 2]?.getD 0#32 = s.core.lvl[l / 2]?.getD 0#32)) →
      (rr = 0#64 → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (rr, ()) m'

/-! ### Owned 12-function specifications (`Full2`) -/

@[expose]
def fullAnalyzeLitSpec : Spec [i64, i32, i32] [.bool] := fun (h, lit, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + 1 < 2 ^ 64 ∧
    AnaWorkInv c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' ws1' mcl' tc' tl' ant' res' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc',
                                tmp_len := tl', min_clr_len := mcl' }
          scratch := { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }
      s'.LengthsOk c → AnaWorkInv c s' → tl' ≤ s.core.cur_vars →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.tmp_len + 1 → s.core.tmp_cnt ≤ tc' →
      let v := lit.toNat / 2
      (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 ≠ 0#8 →
        mrk'[w]?.getD 0#8 = s.core.mrk[w]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
        v = w ∧ w ≠ skip_var.toNat ∧ 0 < (s.core.lvl[w]?.getD 0#32).toNat ∧
        (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' →
        (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧ v < s.core.cur_vars ∧
        v ≠ skip_var.toNat ∧ s.core.mrk[v]?.getD 0#8 = 0#8 ∧
        0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
        (s.core.lvl[v]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[v]?.getD 0#8 ≠ 0#8) →
      ant' = s.scratch.ant_sz +
        (if v < s.core.cur_vars ∧ 0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
            (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level then 1#64 else 0#64) →
      res' = s.scratch.res_sz +
        (if v < s.core.cur_vars ∧ s.core.mrk[v]?.getD 0#8 = 0#8 ∧ mrk'[v]?.getD 0#8 ≠ 0#8
         then 1#64 else 0#64) →
      (tc' = s.core.tmp_cnt +
        if v < s.core.cur_vars ∧ s.core.mrk[v]?.getD 0#8 = 0#8 ∧ mrk'[v]?.getD 0#8 ≠ 0#8 ∧
          (s.core.lvl[v]?.getD 0#32).toNat = s.core.cur_level then 1 else 0) →
      (ok = true →
        v < s.core.cur_vars ∧
        (v ≠ skip_var.toNat →
          (0 < (s.core.lvl[v]?.getD 0#32).toNat → mrk'[v]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[v]?.getD 0#8 = 0#8 → (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[v]?.getD 0#32).toNat →
              (s.core.lvl[v]?.getD 0#32).toNat = s.core.cur_level → tc' = s.core.tmp_cnt + 1) ∧
            (0 < (s.core.lvl[v]?.getD 0#32).toNat →
              (s.core.lvl[v]?.getD 0#32).toNat < s.core.cur_level →
              tl' = s.core.tmp_len + 1 ∧ tmp'[s.core.tmp_len]? = some lit)))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Helper list of reason literals (`full_analyze_rsn` / 1UIP). -/
@[expose] def fullRsnLits (s : FullState) (rsn : BitVec 32) : List Nat :=
  if rsn = 0xFFFFFFFF#32 then []
  else if (rsn &&& 0x80000000#32) ≠ 0#32 then [(rsn &&& 0x7FFFFFFF#32).toNat]
  else fullArenaClauseLits s rsn.toNat

@[expose]
def fullAnalyzeRsnSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + c.max_vars + 1 < 2 ^ 64 ∧
    AnaWorkInv c s ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' ws1' mcl' tc' tl' arena' gu' ant' res' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
          scratch := { s.scratch with work_stk1 := ws1', glue_used := gu',
                                      ant_sz := ant', res_sz := res' } }
      FullWitnessCutInv c F0 F_cur cut s'.core → s'.LengthsOk c → AnaWorkInv c s' →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 ≠ 0#8 →
        mrk'[w]?.getD 0#8 = s.core.mrk[w]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = w ∧ w ≠ skip_var.toNat ∧
          0 < (s.core.lvl[w]?.getD 0#32).toNat ∧
          (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt =
        ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
          decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (res' = s.scratch.res_sz + BitVec.ofNat 64
        ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true →
        rsn ≠ 0xFFFFFFFF#32 ∧
        ant' = s.scratch.ant_sz + BitVec.ofNat 64
          ((fullRsnLits s rsn).countP fun l =>
            decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ((rsn &&& 0x80000000#32) ≠ 0#32 → (rsn &&& 0x7FFFFFFF#32).toNat / 2 < s.core.cur_vars) ∧
        ((rsn &&& 0x80000000#32) = 0#32 →
          rsn.toNat + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSize s rsn.toNat ∧
          rsn.toNat + 3 + fullArenaClauseSize s rsn.toNat ≤ s.core.arena_len) ∧
        ∀ l ∈ fullRsnLits s rsn,
          l / 2 < s.core.cur_vars ∧
          (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                  (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullClearAnaSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ AnaWorkInv c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' m',
      let s' : FullState := { s with core := { s.core with mrk := mrk', min_clr_len := 0 } }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullOtfsLargeSpec : Spec [i64, i32, i32] [.bool] := fun (h, cref, uip, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut idx_u : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.dense_mode = 0#64 ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    uip.toNat < 2 * s.core.cur_vars ∧
    idx_u < cut ∧ idx_u < s.core.trail_end ∧
    (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat ∧
    s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref ∧
    (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    ((cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
        decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat))))) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', wvec := wvec', wstk := wstk',
                                wlen := wlen', wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      sc'.last_learned = s.scratch.last_learned → sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat,
          l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat ∧
          s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullOtfsBinSpec : Spec [i64, i32, i32] [.bool] := fun (h, cref, uip, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut idx_u : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.dense_mode = 0#64 ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    uip.toNat < 2 * s.core.cur_vars ∧
    idx_u < cut ∧ idx_u < s.core.trail_end ∧
    (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat ∧
    s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref ∧
    (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (∀ f0 f1 : BitVec 32,
      f0.toNat ∈ fullArenaClauseLits s cref.toNat → f1.toNat ∈ fullArenaClauseLits s cref.toNat →
      f0 ≠ uip → f1 ≠ uip → f0 ≠ f1 →
      0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat →
      0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) arena' ag' nb' wvec' wstk' wlen' wu' ct' c0' c1' cref' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', num_binary := nb',
                                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                                confl_type := ct', confl_lit0 := c0', confl_lit1 := c1',
                                confl_ref := cref', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      sc'.last_learned = s.scratch.last_learned → sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ FullConflOk F_cur idx_u s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullOtfsSubsumeSpec : Spec [i64, i32, i64, i64, .bool] [] :=
  fun (h, new_confl, old_ctype, old_cref, to_bin, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧
      FullArenaVarsNodup s ∧
      (old_ctype = 2#64 → old_cref ≠ 0xFFFFFFFF#64 →
        old_cref.toNat ∈ fullArenaClauseRefs s ∧
        (¬ to_bin = true → new_confl.toNat ∈ fullArenaClauseRefs s) ∧
        ∀ idx < s.core.trail_end,
          (idx < cut ∨ (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
            s.core.cur_level) →
          let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
          rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ old_cref.toNat) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ arena' ag' ni' nr' m',
        let s' : FullState :=
          { s with core := { s.core with arena := arena', arena_garbage := ag',
                                         num_irred := ni', num_redundant := nr' } }
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core →
        fullArenaClauseRefs s' = fullArenaClauseRefs s → FullArenaVarsNodup s' →
        (∀ r ∈ fullArenaClauseRefs s,
          fullArenaClauseLits s' r = fullArenaClauseLits s r ∧
          (old_ctype = 2#64 → r ≠ old_cref.toNat →
            fullArenaClauseGarb s' r = fullArenaClauseGarb s r)) →
        (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullDetNewLevelSpec : Spec [i64, i64] [i64] := fun (h, jump, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64,
      (s.core.cur_level = 0 → r = 0#64) →
      (0 < s.core.cur_level → jump.toNat < s.core.cur_level →
        jump.toNat ≤ r.toNat ∧ r.toNat < s.core.cur_level) →
      Q (r, ()) m

@[expose] def fullOneLitConflSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.dense_mode = 0#64 ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullLitMarksClear c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ cut ≤ s.core.trail_end ∧
    FullConflOk F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.core.dense_mode = 0#64 → s'.core.probing = s.core.probing →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      (r = 20#64 → F0.Unsat ∧ s' = s) →
      (r = 1#64 → FullWitnessInv c F0 F_cur s'.core ∧ s'.core.cur_level < s.core.cur_level) →
      (r = 2#64 → FullWitnessCutInv c F0 F_cur 0 s'.core) →
      (r = 0#64 → ∃ cut' ≤ s'.core.trail_end,
        FullWitnessCutInv c F0 F_cur cut' s'.core ∧ 0 < s'.core.cur_level ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.wvec = s.core.wvec ∧
        s'.core.wstk = s.core.wstk ∧ s'.core.wlen = s.core.wlen ∧
        s'.core.wusable = s.core.wusable ∧ FullConflOk F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullDeduce1uipSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.dense_mode = 0#64 ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullLitMarksClear c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ cut ≤ s.core.trail_end ∧
    0 < s.core.cur_level ∧ FullConflOk F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.core.dense_mode = 0#64 → s'.core.probing = s.core.probing →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      (r = 20#64 → F0.Unsat ∧ FullWitnessCutInv c F0 F_cur cut s'.core ∧
        s'.core.cur_level = s.core.cur_level ∧ s'.core.wvec = s.core.wvec ∧
        s'.core.wstk = s.core.wstk ∧ s'.core.wlen = s.core.wlen ∧
        s'.core.wusable = s.core.wusable) →
      (r = 0#64 → FullWitnessCutInv c F0 F_cur 0 s'.core) →
      (r = 1#64 → FullWitnessCutInv c F0 F_cur 0 s'.core ∧
        s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        FullWitnessCutInv c F0 F_cur cut' s'.core ∧ s'.core.cur_level = s.core.cur_level ∧
        FullConflOk F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullWitnessInv_to_cut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) (cut : Nat) :
    FullWitnessCutInv c F0 F_cur cut k :=
  { ext_sound := h.ext_sound, inconsistent_sound := h.inconsistent_sound
    arena := h.arena, watches := h.watches, cur_level_le := h.cur_level_le
    trail_lits_lt := h.trail_lits_lt, trail_vars_nodup := h.trail_vars_nodup
    vals_domain := h.vals_domain, vals_true_iff := h.vals_true_iff
    vals_false_iff := h.vals_false_iff, lvl_le := h.lvl_le, dec_earliest := h.dec_earliest
    levels_inhabited := h.levels_inhabited, level0_sound := h.level0_sound
    trail_pos_inv := h.trail_pos_inv, level0_rsn_none := h.level0_rsn_none
    frame_trail_lt := h.frame_trail_lt, frame_trail_mono := h.frame_trail_mono
    frame_trail_before_lt := h.frame_trail_before_lt, frame_dec_lt := h.frame_dec_lt
    reason_inv := fun idx hidx _ => h.reason_inv idx hidx
    reason_lit_mem := fun idx hidx _ => h.reason_lit_mem idx hidx }

theorem FullWitnessCutInv.to_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (hcut : k.trail_end ≤ cut) : FullWitnessInv c F0 F_cur k :=
  { ext_sound := h.ext_sound, inconsistent_sound := h.inconsistent_sound
    arena := h.arena, watches := h.watches, cur_level_le := h.cur_level_le
    trail_lits_lt := h.trail_lits_lt, trail_vars_nodup := h.trail_vars_nodup
    vals_domain := h.vals_domain, vals_true_iff := h.vals_true_iff
    vals_false_iff := h.vals_false_iff, lvl_le := h.lvl_le, dec_earliest := h.dec_earliest
    levels_inhabited := h.levels_inhabited, level0_sound := h.level0_sound
    trail_pos_inv := h.trail_pos_inv, level0_rsn_none := h.level0_rsn_none
    frame_trail_lt := h.frame_trail_lt, frame_trail_mono := h.frame_trail_mono
    frame_trail_before_lt := h.frame_trail_before_lt, frame_dec_lt := h.frame_dec_lt
    reason_inv := fun idx hidx => h.reason_inv idx hidx (Or.inl (by omega))
    reason_lit_mem := fun idx hidx => h.reason_lit_mem idx hidx (Or.inl (by omega)) }

theorem FullWitnessCutInv.shrink_cut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut cut' : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (hle : cut' ≤ cut) : FullWitnessCutInv c F0 F_cur cut' k :=
  { h with
    reason_inv := fun idx hidx hc =>
      h.reason_inv idx hidx (hc.elim (fun h1 => Or.inl (by omega)) Or.inr)
    reason_lit_mem := fun idx hidx hc =>
      h.reason_lit_mem idx hidx (hc.elim (fun h1 => Or.inl (by omega)) Or.inr) }

theorem FullWitnessCutInv.vals_zero_iff {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) {l : Nat}
    (hl : l < 2 * k.cur_vars) :
    k.vals[l]?.getD 0#8 = 0#8 ↔ ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  constructor
  · intro hz i hi hvar
    rcases (litVar_eq_iff _ l).mp hvar with h1 | h2
    · have ht := (h.vals_true_iff l hl).mpr ⟨i, hi, h1⟩; rw [hz] at ht; cases ht
    · have hf := (h.vals_false_iff l hl).mpr ⟨i, hi, h2⟩; rw [hz] at hf; cases hf
  · intro hnone
    rcases h.vals_domain l hl with h0 | h1 | h2
    · exact h0
    · obtain ⟨i, hi, heq⟩ := (h.vals_true_iff l hl).mp h1; exact absurd (by rw [heq]) (hnone i hi)
    · obtain ⟨i, hi, heq⟩ := (h.vals_false_iff l hl).mp h2
      exact absurd (by rw [heq, fullInv_var_xor1]) (hnone i hi)

theorem FullWitnessCutInv.with_watches {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hw : ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }) :
    FullWitnessCutInv c F0 F_cur cut
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :=
  { h with arena := { h.arena with len_ok := h.arena.len_ok }, watches := hw }

theorem FullWitnessCutInv.with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) (oom' : BitVec 64) :
    FullWitnessCutInv c F0 F_cur cut { k with oom := oom' } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

theorem FullWitnessCutInv.with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (ct' c0' c1' cref' : BitVec 64) :
    FullWitnessCutInv c F0 F_cur cut
      { k with confl_type := ct', confl_lit0 := c0', confl_lit1 := c1', confl_ref := cref' } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

end FullAnalyzeSpecs

open FullAnalyzeSpecs

/-! ## 3. Core / OTFS-cut / arena / `AnaWorkInv` preservation lemmas -/

namespace FullAnalyzeHelpers

/-- Level-0 binary conflict refutation without requiring `cur_level = 0`. -/
theorem unsat_of_level0_bin_conflict {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k) {l0 l1 : Nat}
    (h0lt : l0 < 2 * k.cur_vars) (h1lt : l1 < 2 * k.cur_vars)
    (hl0 : (k.lvl[l0 / 2]?.getD 0#32).toNat = 0)
    (hl1 : (k.lvl[l1 / 2]?.getD 0#32).toNat = 0)
    (hf0 : k.vals[l0]?.getD 0#8 = 0xFF#8) (hf1 : k.vals[l1]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0, l1])) : F0.Unsat := by
  refine hw.ext_sound.2
    (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l h0lt).mp hf0
    have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hl0)
    rwa [hieq] at hs
  · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l h1lt).mp hf1
    have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hl1)
    rwa [hieq] at hs

/-- Level-0 large conflict refutation without requiring `cur_level = 0`. -/
theorem unsat_of_level0_conflict {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (hg : fullArenaClauseGarbCore k cref = false)
    (hfals : ∀ l ∈ fullArenaClauseLitsCore k cref,
      k.vals[l]?.getD 0#8 = 0xFF#8 ∧ (k.lvl[l / 2]?.getD 0#32).toNat = 0) : F0.Unsat := by
  refine hw.ext_sound.2 (unsat_of_entails_nil
    (entails_of_mem_or_false (hw.arena.entails cref href hg) fun l hl => Or.inr ?_))
  obtain ⟨hf, hlv⟩ := hfals l hl
  obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt cref href hg l hl)).mp hf
  have hs := hw.level0_sound i hi (by rw [hieq, fullInv_var_xor1]; exact hlv)
  rwa [hieq] at hs

/-- Shared arena-only mutation wrapper for `FullWitnessCutInv` (`arena`, `arena_garbage`,
`num_irred`, `num_redundant`). -/
theorem arenaUpdate_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {arena' : List (BitVec 32)} {ag' ni' nr' : BitVec 64}
    (harena : FullArenaClausesInv c F_cur
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' })
    (hrefs : fullArenaClauseRefsCore
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' } =
      fullArenaClauseRefsCore k)
    (hact : ∀ idx < k.trail_end,
      (idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      fullArenaClauseGarbCore
        { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' }
        rsn.toNat = false ∧
      List.Perm
        (fullArenaClauseLitsCore
          { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' }
          rsn.toNat)
        (fullArenaClauseLitsCore k rsn.toNat)) :
    FullWitnessCutInv c F0 F_cur cut
      { k with arena := arena', arena_garbage := ag', num_irred := ni', num_redundant := nr' } := by
  exact { hw with
    arena := harena
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hc hne => by
      have hrs := hw.reason_inv idx hidx hc hne
      by_cases hlg : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32
      · rw [ite_eq_right (fun h => h hlg)] at hrs ⊢
        have ha := hact idx hidx hc hne hlg
        exact ⟨hrefs ▸ hrs.1, ha.1, fun q hq => hrs.2.2 q (ha.2.mem_iff.mp hq)⟩
      · rw [ite_eq_left (fun h => absurd h hlg)] at hrs ⊢; exact hrs
    reason_lit_mem := fun idx hidx hc hne hlg => by
      have ha := hact idx hidx hc hne hlg
      exact ha.2.symm.mem_iff.mp (hw.reason_lit_mem idx hidx hc hne hlg) }

/-- Updating header bits of `ar[cref]` while preserving `PH_GARB` (`bit 19`) and `PH_SHRK`
(`bit 23`) unifies `full_analyze_rsn` usage bumps and `full_otfs_subsume` `~PH_RED` clearing. -/
theorem hdrBitsUpdate_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k)
    (f : BitVec 32 → BitVec 32) (ag' ni' nr' : BitVec 64)
    (hgarb : (f (fullArenaHdrCore k cref) &&& 0x00080000#32) =
      (fullArenaHdrCore k cref &&& 0x00080000#32))
    (hshrk : (f (fullArenaHdrCore k cref) &&& 0x00800000#32) =
      (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let hdr' := f (fullArenaHdrCore k cref)
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref hdr', arena_garbage := ag',
               num_irred := ni', num_redundant := nr' }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro hdr' k'
  have hcref_wf := hw.arena.refs_wf cref hcref
  have hcref_lt : cref < k.arena.length := by
    have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
  have har_self : k'.arena[cref]? = some hdr' := List.getElem?_set_self hcref_lt
  have har_ne : ∀ j, j ≠ cref → k'.arena[j]? = k.arena[j]? := fun j hj =>
    List.getElem?_set_ne (Ne.symm hj)
  have hnxt_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r; unfold fullArenaNextOff
      have hnot : ¬ (cref + 3 > k.arena_len) := by omega
      simp only [hnot, ↓reduceIte, har_self, Option.getD_some, har_ne (cref + 2) (by omega)]
      split
      · rfl
      · change (if (hdr' &&& 0x00800000#32) ≠ 0#32 then _ else _) =
          if (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 then _ else _
        rw [hshrk]; split
        · exact fullArenaSkipShrk_congr fun j hj1 _ => har_ne j (by omega)
        · rfl
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr hcref hlt
        have := (hw.arena.refs_wf r hr).2.1
        have := (hw.arena.refs_wf r hr).2.2.1
        exact fullArenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun j _ hk2 => har_ne j (by omega)
      · exact fullArenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun j hj1 _ => har_ne j (by omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt_eq
  have hprops : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr; have hr_wf := hw.arena.refs_wf r hr
    have hnot_in : ∀ j, r + 2 ≤ j → j < r + 3 + fullArenaClauseSizeCore k r → j ≠ cref := by
      intro j hj1 hj2 heq; subst j; by_cases hrc : r = cref
      · omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := hw.arena.disjoint hr hcref hlt; omega
        · omega
    have hsz : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
      unfold fullArenaClauseSizeCore
      rw [har_ne (r + 2) (hnot_in (r + 2) (Nat.le_refl _) (by omega))]
    have hgarb : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; by_cases hrc : r = cref
      · subst r; rw [har_self, Option.getD_some]
        change (hdr' &&& 0x00080000#32 != 0#32) = _; rw [hgarb]; rfl
      · rw [har_ne r hrc]
    have hlits : fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
      have hbd1 : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
        have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
      exact fullArenaClauseLitsCore_eq_of_hold hbd1 (by simpa [k'] using hbd1) hsz
        fun j hj => har_ne (r + 3 + j) (hnot_in (r + 3 + j) (by omega) (by omega))
    exact ⟨hsz, hgarb, hlits⟩
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      change _ ∧ _ ∧ _ ∧ _ ∧ _; rw [hnxt_eq r hr, (hprops r hr).1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢; rwa [har_self, Option.getD_some, hshrk] at hsh
        · unfold fullArenaHdrCore at hsh ⊢; rwa [har_ne r hrc] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hr3 := (hw.arena.refs_wf r hr).1
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel hr3 hsh_ar ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; omega
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := fullArenaScanRefs_disjoint hr hcref hlt; omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [(hprops r hr).1]; exact ht0_lo, by dsimp [k']; omega, ?_⟩
      dsimp only [k']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng; rw [hrefs] at hr; rw [(hprops r hr).2.1] at hng
      rw [(hprops r hr).2.2]; exact hw.arena.lits_lt r hr hng
    · intro r hr hng; rw [hrefs] at hr; rw [(hprops r hr).2.1] at hng
      rw [(hprops r hr).2.2]; exact hw.arena.entails r hr hng
  refine ⟨arenaUpdate_preserves_fullWitnessCut hw harena' hrefs fun idx hidx hc hne hlg => ?_,
    hrefs, hprops⟩
  have hrs := hw.reason_inv idx hidx hc hne
  rw [ite_eq_right (fun h => absurd hlg h)] at hrs
  exact ⟨(hprops _ hrs.1).2.1.trans hrs.2.1, (hprops _ hrs.1).2.2 ▸ List.Perm.refl _⟩

theorem arenaBumpUsage_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k) (u : BitVec 32) :
    let hdr := fullArenaHdrCore k cref
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref ((hdr &&& 0x07FFFFFF#32) ||| (u <<< 27)) }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) :=
  hdrBitsUpdate_preserves_fullWitnessCut hlen hw hcref
    (fun x => (x &&& 0x07FFFFFF#32) ||| (u <<< 27))
    k.arena_garbage k.num_irred k.num_redundant
    (bv32_mask_usage_garb _ u) (bv32_mask_usage_shrk _ u)

theorem clearRed_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k) (ni' nr' : BitVec 64) :
    let hdr := fullArenaHdrCore k cref
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref (hdr &&& 0xFFBFFFFF#32)
               num_irred := ni', num_redundant := nr' }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) :=
  hdrBitsUpdate_preserves_fullWitnessCut hlen hw hcref (fun x => x &&& 0xFFBFFFFF#32)
    k.arena_garbage ni' nr' (bv32_clear_red_garb _) (bv32_clear_red_shrk _)

/-! ### `AnaWorkInv` / `clear_ana` preservation helpers -/

theorem anaWorkInv_init {c : FullCfg} {s : FullState}
    (hm : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) (hmcl : s.core.min_clr_len = 0) :
    AnaWorkInv c s :=
  ⟨by omega, by simp [hmcl], fun k hk => by omega, fun v hv hnz => absurd (hm v hv) hnz⟩

theorem anaWorkInv_step {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (hwork : AnaWorkInv c s) {v : Nat} (hv : v < s.core.cur_vars)
    (hm0 : s.core.mrk[v]?.getD 0#8 = 0#8) :
    let v32 := BitVec.ofNat 32 v
    let s' : FullState :=
      { s with
        core := { s.core with mrk := s.core.mrk.set v 1#8, min_clr_len := s.core.min_clr_len + 1 }
        scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set s.core.min_clr_len v32 } }
    s.core.min_clr_len < s.core.cur_vars ∧ AnaWorkInv c s' := by
  intro v32 s'
  obtain ⟨hle, hnd, hall, hcov⟩ := hwork
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len; have hm_len := hlen.core_ok.mrk_len
  have hv32 : v32.toNat = v := bv32_ofNat_toNat (by omega)
  let xs := (s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat
  have hxs_len : xs.length = s.core.min_clr_len := by
    simp [xs, List.length_map, List.length_take]; omega
  have hxs_lt : ∀ x ∈ xs, x < s.core.cur_vars := fun x hx => by
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    have hj_m : j < s.core.min_clr_len := by omega
    have hx_eq : x = (s.scratch.work_stk1[j]?.getD 0#32).toNat := by
      rw [← hget]; unfold xs; simp only [List.getElem_map, List.getElem_take]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hx_eq]; exact (hall j hj_m).1
  have hv_not_mem : v ∉ xs := fun hx => by
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    have hj_m : j < s.core.min_clr_len := by omega
    have hx_eq : v = (s.scratch.work_stk1[j]?.getD 0#32).toNat := by
      rw [← hget]; unfold xs; simp only [List.getElem_map, List.getElem_take]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact (hall j hj_m).2 (by rw [← hx_eq]; exact hm0)
  have hmcl_lt : s.core.min_clr_len < s.core.cur_vars := by
    rw [← hxs_len]; exact nodup_lt_of_missing hnd hxs_lt hv hv_not_mem
  have hmcl_ws : s.core.min_clr_len < s.scratch.work_stk1.length := by omega
  have htake_s' : ((s'.scratch.work_stk1.take (s.core.min_clr_len + 1)).map BitVec.toNat) =
      xs ++ [v] := by
    have h2 : s'.scratch.work_stk1.take (s.core.min_clr_len + 1) =
        s.scratch.work_stk1.take s.core.min_clr_len ++ [v32] := by
      apply List.ext_getElem
      · simp [s', List.length_take]; omega
      · intro j hj1 hj2
        have hj_le : j < s.core.min_clr_len + 1 := by simp [s', List.length_take] at hj1; omega
        by_cases hjm : j = s.core.min_clr_len
        · subst j
          rw [List.getElem_take, List.getElem_append_right (by simp [List.length_take]; omega),
            List.getElem_set_self (by simp [hmcl_ws])]
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hmcl_ws)]
        · have hj' : j < s.core.min_clr_len := by omega
          rw [List.getElem_take, List.getElem_append_left (by simp [List.length_take]; omega),
            List.getElem_take, List.getElem_set_ne (Ne.symm hjm)]
    rw [h2, List.map_append]; simp [xs, hv32]
  refine ⟨hmcl_lt, hmcl_lt, ?_, ?_, ?_⟩
  · rw [htake_s', List.nodup_append]
    exact ⟨hnd, by simp, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst b; intro heq; subst heq; exact hv_not_mem ha⟩
  · intro k hk
    dsimp only [s'] at hk
    by_cases hkm : k = s.core.min_clr_len
    · subst k
      simp only [s', List.getElem?_set_self hmcl_ws, Option.getD_some, hv32, hv, true_and]
      rw [List.getElem?_set_self (by omega)]; decide
    · have hk' : k < s.core.min_clr_len := by omega
      have hget : (s'.scratch.work_stk1[k]?.getD 0#32).toNat =
          (s.scratch.work_stk1[k]?.getD 0#32).toNat := by
        dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hkm)]
      rw [hget]; refine ⟨(hall k hk').1, ?_⟩
      by_cases hwe : (s.scratch.work_stk1[k]?.getD 0#32).toNat = v
      · exact absurd hm0 (hwe ▸ (hall k hk').2)
      · dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hwe)]; exact (hall k hk').2
  · intro w hw hnz
    by_cases hwv : w = v
    · subst w; refine ⟨hv, s.core.min_clr_len, Nat.lt_succ_self _, ?_⟩
      simp only [s', List.getElem?_set_self hmcl_ws, Option.getD_some, hv32]
    · have hnz0 : s.core.mrk[w]?.getD 0#8 ≠ 0#8 := by
        simpa [s', List.getElem?_set_ne (Ne.symm hwv)] using hnz
      obtain ⟨hw_lt, k, hk, hkeq⟩ := hcov w hw hnz0
      have hne_km : s.core.min_clr_len ≠ k := by omega
      refine ⟨hw_lt, k, by dsimp only [s']; omega, ?_⟩
      dsimp only [s']; rwa [List.getElem?_set_ne hne_km]

theorem clear_ana_restores_marksClear {c : FullCfg} {s : FullState} {mrk' : List (BitVec 8)}
    (hwork : AnaWorkInv c s)
    (hpres : ∀ v < c.max_vars,
      (∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat ≠ v) →
      mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8)
    (hclr : ∀ k < s.core.min_clr_len,
      mrk'[(s.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8) :
    ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8 := by
  intro v hv
  by_cases hnz : s.core.mrk[v]?.getD 0#8 = 0#8
  · by_cases hin : ∃ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat = v
    · obtain ⟨k, hk, hkeq⟩ := hin; rw [← hkeq]; exact hclr k hk
    · have hni : ∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat ≠ v :=
        fun k hk heq => hin ⟨k, hk, heq⟩
      rw [hpres v hv hni, hnz]
  · obtain ⟨_, k, hk, hkeq⟩ := hwork.2.2.2 v hv hnz; rw [← hkeq]; exact hclr k hk

theorem fullMem_eq_core {c : FullCfg} {s1 s2 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hk : s1.core = s2.core) (hsc : s1.scratch = s2.scratch)
    (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := by
  cases s1; cases s2; simp only at hk hsc; subst hk hsc; exact hm

theorem fullMem_of_eq {c : FullCfg} {s1 s2 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m)
    (hk : s1.core = s2.core) (hsc : s1.scratch = s2.scratch) : (FullMem c s2 ⋆ R) m :=
  fullMem_eq_core hk hsc hm

end FullAnalyzeHelpers

end LeanQbe.T.Examples.Kissat.Full
