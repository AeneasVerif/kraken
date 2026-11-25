/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1

/-!
# Kissat 4.0.4 Congruence Parity Proofs — Part 3a0 (`FullFidelityCongProof3a0`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for the upstream forward-subsumption subsystem
(`FullFidelityCong.lean` lines 810–1006, closing `BUG-CONG-00`):
1. `full_cong_sift_pairs_fid_wp` (`fidCongSiftPairsSpec`)
2. `full_cong_sort_pairs_fid_wp` (`fidCongSortPairsSpec`)
3. `full_cong_fwd_subsume_wp` (`m6CongFwdSubsumeSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullCongTactics M6bHeadTactics

/-! ## 1. Pure, Array, `FullDenseInvW`, Pair & Occurrence-List Helpers -/

section Helpers

theorem bv32_ult_lt {a b : BitVec 32} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv32_ult_not_lt {a b : BitVec 32} (h : a.ult b = false) :
    ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv64_ult_lt {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv64_ult_not_lt {a b : BitVec 64} (h : a.ult b = false) :
    ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv64_ule_le {a b : BitVec 64} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

theorem bv64_ule_not_le {a b : BitVec 64} (h : a.ule b = false) : b.toNat < a.toNat := by
  have h' : ¬ a.toNat ≤ b.toNat := by simpa [BitVec.ule] using h
  omega

theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv64_add1_lt {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) :
    (a + 1#64).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv64_add2_lt {a : BitVec 64} (h : a.toNat + 2 < 2 ^ 64) :
    (a + 2#64).toNat = a.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

theorem bv64_sub1_pos {a : BitVec 64} (h : 0 < a.toNat) :
    (a - 1#64).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ a.toNat; omega))]
  rfl

theorem bv64_shl1_lt {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< 1#64).toNat = 2 * x.toNat := by
  rw [show (x <<< 1#64 : BitVec 64) = x <<< (1 : Nat) from rfl,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem bv64_shl1_add1_lt {x : BitVec 64} (h : 2 * x.toNat + 1 < 2 ^ 64) :
    ((x <<< 1#64) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_add, bv64_shl1_lt (by omega), show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h]

theorem bv64_shr1_toNat (x : BitVec 64) :
    (x >>> 1#64).toNat = x.toNat / 2 := by
  rw [show (x >>> 1#64 : BitVec 64) = x >>> (1 : Nat) from rfl,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem bv64_shr2_toNat (x : BitVec 64) :
    (x >>> 2#64).toNat = x.toNat / 4 := by
  rw [show (x >>> 2#64 : BitVec 64) = x >>> (2 : Nat) from rfl,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem list_getElem_congr {α : Type _} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem list_eq_getElem_congr {α : Type _} {xs ys : List α} (h : xs = ys) {i : Nat}
    (hx : i < xs.length) (hy : i < ys.length) : xs[i]'hx = ys[i]'hy := by
  subst h; rfl

theorem bv8_slt0_iff {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) : v.slt 0#8 = true ↔ v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem bv8_sext32_slt0_true {x : BitVec 8}
    (h : (x.signExtend 32).slt 0#32 = true) : x.slt 0#8 = true := by
  have hi : (x.signExtend 32).toInt = x.toInt := by
    rw [BitVec.toInt_signExtend, show min 32 8 = 8 from rfl, Int.bmod_def]
    have h1 : -(2 ^ 7 : Int) ≤ x.toInt := BitVec.le_toInt x
    have h2 : x.toInt < 2 ^ 7 := @BitVec.toInt_lt 8 x
    have hpow : ((2 ^ 8 : Nat) : Int) = 256 := rfl
    rw [hpow]; split <;> omega
  simpa [BitVec.slt, hi] using h

theorem bv8_zext32_beq0_false {x : BitVec 8}
    (h : (x.setWidth 32 == 0#32) = false) : x ≠ 0#8 := by
  intro hx; subst hx; simp at h

theorem fid_garb_false_of_and {hdr : BitVec 32}
    (h : (hdr &&& 0x00080000#32) = 0#32) : ((hdr &&& 0x00080000#32) != 0#32) = false := by
  simp [h]

theorem fid_lit_false_of_vals_slt0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (_hcl0 : k.cur_level = 0) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hslt : (k.vals[l]?.getD 0#8).slt 0#8 = true) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → evalLitVal α l = false := by
  intro α hα
  have hff : k.vals[l]?.getD 0#8 = 0xFF#8 := (bv8_slt0_iff (hw.vals_domain l hl)).mp hslt
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hl).mp hff
  have hlv0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hsat := CNF.entails_clause_def.mp (hw.level0_sound i hi hlv0) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at hsat
  simp only [List.any_cons, List.any_nil, Bool.or_false, htrl,
    show l ^^^ 1 = litNeg l from rfl, evalLitVal_litNeg] at hsat
  cases h : evalLitVal α l <;> simp_all

theorem fid_litEquiv_eval {F : CNF Nat} {l1 l2 : Nat}
    (heqv : LitEquiv F l1 l2) {α : Nat → Bool} (hα : F.Sat α) :
    evalLitVal α l1 = evalLitVal α l2 := by
  have h12 := CNF.entails_clause_def.mp heqv.1 α hα
  have h21 := CNF.entails_clause_def.mp heqv.2 α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at h12 h21
  simp only [List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg] at h12 h21
  cases e1 : evalLitVal α l1 <;> cases e2 : evalLitVal α l2 <;> simp_all

theorem fid_denseInvW_with_repr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {r' : List (BitVec 32)} (hrl : r'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with repr := r' } } :=
  ⟨⟨{ hd.1.core_ok with repr_len := hrl }, hd.1.scratch_ok⟩,
   fullWitnessInv_with_repr hd.2.1 r', hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fid_denseInvW_with_mclr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {mc' : List (BitVec 32)} (hl : mc'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with min_clr := mc' } } := by
  have hw' : FullWitnessInv c F0 F_cur { s.core with min_clr := mc' } :=
    { hd.2.1 with
      arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨⟨{ hd.1.core_ok with min_clr_len_arr := hl }, hd.1.scratch_ok⟩, hw',
    fullLitMarksClear_of_eq hd.2.2.1 rfl rfl, fullArenaVarsNodup_of_eq hd.2.2.2.1 rfl rfl,
    fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fid_denseInvW_with_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hl }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fid_denseInvW_with_ws12 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {w1' w2' : List (BitVec 32)}
    (hl1 : w1'.length = 2 * c.max_vars) (hl2 : w2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with work_stk1 := w1', work_stk2 := w2' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk1_len := hl1, work_stk2_len := hl2 }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fid_denseInvW_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hd.1.core_ok with }, hd.1.scratch_ok⟩,
   fullWitnessInv_with_inconsistent hd.2.1 inc' (fun _ => hu),
   hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fid_fs_markGarb_dense {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } } := by
  have hcl0 := hd.2.2.2.2.2.1
  have hmg := markGarb_preserves_fullWitnessInv hd.1 hd.2.1 href ag' fun idx hidx hne _ => by
    have hr := hd.2.1.level0_rsn_none idx hidx (by have := hd.2.1.lvl_le idx hidx; omega)
    exact absurd hr hne
  exact ⟨hmg.1, hmg.2.2.1, fullLitMarksClear_of_eq hd.2.2.1 rfl rfl, hmg.2.2.2.2 hd.2.2.2.1,
    ⟨fun i hi => (hd.2.2.2.2.1.1 i hi).elim Or.inl fun h => Or.inr (hmg.2.1 ▸ h),
     hd.2.2.2.2.1.2⟩, hcl0, hd.2.2.2.2.2.2⟩

theorem fid_fs_markGarb_dense' {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hcr : cref < s.core.arena.length)
    (ag' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref ((s.core.arena[cref]'hcr) ||| 0x00080000#32)
          arena_garbage := ag' } } := by
  have hhdr : fullArenaHdr s cref = s.core.arena[cref]'hcr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr, Option.getD_some]
  simpa only [hhdr] using fid_fs_markGarb_dense hd href ag'

theorem fid_fs_markGarb_refs {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hcr : cref < s.core.arena.length)
    (ag' : BitVec 64) :
    fullArenaClauseRefs
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref ((s.core.arena[cref]'hcr) ||| 0x00080000#32)
          arena_garbage := ag' } } = fullArenaClauseRefs s := by
  have hcl0 := hd.2.2.2.2.2.1
  have hhdr : fullArenaHdr s cref = s.core.arena[cref]'hcr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr, Option.getD_some]
  have hmg := markGarb_preserves_fullWitnessInv hd.1 hd.2.1 href ag' fun idx hidx hne _ => by
    have hr := hd.2.1.level0_rsn_none idx hidx (by have := hd.2.1.lvl_le idx hidx; omega)
    exact absurd hr hne
  simpa only [hhdr] using hmg.2.1

theorem fid_addUnit_denseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hl' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hcl' : s'.core.cur_level = 0) (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' :=
  ⟨hl', hw', fullLitMarksClear_of_eq hd.2.2.1 hmrk' hlm',
   fullArenaVarsNodup_of_eq hd.2.2.2.1 har' hal',
   fullExtScratchOk_of_eq hd.2.2.2.2.1 har' hal' hll' hext',
   hcl', hdm' ▸ hd.2.2.2.2.2.2⟩

/-- Pair-invariant helper: appending `(key, cr)` at pair slot `n` extends `FidPairsOk`. -/
theorem fidPairsOk_push {P : BitVec 32 → BitVec 32 → Prop} {a : List (BitVec 32)}
    {n : Nat} {key cr : BitVec 32}
    (hok : FidPairsOk P a n) (hbd : 2 * n + 1 < a.length) (hp : P key cr) :
    FidPairsOk P ((a.set (2 * n) key).set (2 * n + 1) cr) (n + 1) := by
  intro i hi
  by_cases hin : i = n
  · subst hin
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      List.getElem?_set_self (by simp; omega), Option.getD_some, Option.getD_some]
    exact hp
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hok i (by omega)

/-- Pair-invariant helper: shrinking the prefix preserves `FidPairsOk`. -/
theorem fidPairsOk_mono {P : BitVec 32 → BitVec 32 → Prop} {a : List (BitVec 32)}
    {m n : Nat} (hle : m ≤ n) (hok : FidPairsOk P a n) : FidPairsOk P a m :=
  fun i hi => hok i (Nat.lt_of_lt_of_le hi hle)

/-- Pair-invariant helper: sifting prefix `[0 ..< m)` preserves `FidPairsOk` on `[0 ..< n)`. -/
theorem fidPairsOk_after_prefix {P : BitVec 32 → BitVec 32 → Prop}
    {a1 a2 : List (BitVec 32)} {m n : Nat} (_hle : m ≤ n)
    (hok1 : FidPairsOk P a1 n) (hok2 : FidPairsOk P a2 m)
    (htail : ∀ idx, 2 * m ≤ idx → a2[idx]? = a1[idx]?) : FidPairsOk P a2 n := by
  intro i hi
  by_cases him : i < m
  · exact hok2 i him
  · rw [htail (2 * i) (by omega), htail (2 * i + 1) (by omega)]
    exact hok1 i hi

/-- Pair-invariant helper: writing at an index `≥ 2*n` preserves `FidPairsOk P a n`. -/
theorem fidPairsOk_set_ge {P : BitVec 32 → BitVec 32 → Prop} {a : List (BitVec 32)}
    {n idx : Nat} {v : BitVec 32} (hok : FidPairsOk P a n) (hge : 2 * n ≤ idx) :
    FidPairsOk P (a.set idx v) n := fun i hi => by
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  exact hok i hi

/-- Valid forward-subsumption occurrence node pointer in `scr[base ..< occ_pos)`. -/
abbrev FidFsOccPtrOk (base occ_pos : Nat) (ptr : BitVec 32) : Prop :=
  ptr = 0xFFFFFFFF#32 ∨
    (base ≤ ptr.toNat ∧ ptr.toNat + 1 < occ_pos ∧ (ptr.toNat - base) % 2 = 0)

/-- Occurrence lists in `occ_head[0 ..< nlits)` and 2-word nodes in `scr[base ..< occ_pos)`
point only to valid arena clause references in `refs0` and valid aligned node pointers. -/
abbrev FidFsOccOk (refs0 : List Nat) (nlits base occ_pos : Nat)
    (occ_head scr : List (BitVec 32)) : Prop :=
  base ≤ occ_pos ∧ occ_pos ≤ scr.length ∧ (occ_pos - base) % 2 = 0 ∧
  (∀ l < nlits, FidFsOccPtrOk base occ_pos (occ_head[l]?.getD 0xFFFFFFFF#32)) ∧
  (∀ nd, base ≤ nd → nd + 1 < occ_pos → (nd - base) % 2 = 0 →
    (scr[nd]?.getD 0#32).toNat ∈ refs0 ∧
    FidFsOccPtrOk base occ_pos (scr[nd + 1]?.getD 0xFFFFFFFF#32))

theorem fidFsOccOk_init {refs0 : List Nat} {nlits base : Nat}
    {occ_head scr : List (BitVec 32)} (hbd : base ≤ scr.length)
    (hall : ∀ l < nlits, occ_head[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    FidFsOccOk refs0 nlits base base occ_head scr :=
  ⟨Nat.le_refl _, hbd, by simp,
   fun l hl => Or.inl (hall l hl),
   fun nd h1 h2 _ => by omega⟩

theorem fidFsOccOk_push {refs0 : List Nat} {nlits base occ_pos : Nat}
    {occ_head scr : List (BitVec 32)} {cref least_r : BitVec 32}
    (hok : FidFsOccOk refs0 nlits base occ_pos occ_head scr)
    (hcap : occ_pos + 2 ≤ scr.length) (hu32 : occ_pos < 2 ^ 32)
    (hcr : cref.toNat ∈ refs0) (hlr : least_r.toNat < nlits)
    (hlr_len : least_r.toNat < occ_head.length) :
    let head := occ_head[least_r.toNat]'hlr_len
    let scr' := (scr.set occ_pos cref).set (occ_pos + 1) head
    let occ_head' := occ_head.set least_r.toNat (BitVec.ofNat 32 occ_pos)
    FidFsOccOk refs0 nlits base (occ_pos + 2) occ_head' scr' := by
  intro head scr' occ_head'
  rcases hok with ⟨hbo, hos, hev, hheads, hnodes⟩
  have hup : ∀ p, FidFsOccPtrOk base occ_pos p → FidFsOccPtrOk base (occ_pos + 2) p := by
    rintro p (rfl | ⟨h1, h2, h3⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, by omega, h3⟩
  have hhead_ok : FidFsOccPtrOk base occ_pos head := by
    have h := hheads least_r.toNat hlr
    rwa [List.getElem?_eq_getElem hlr_len, Option.getD_some] at h
  have hnew_ptr : FidFsOccPtrOk base (occ_pos + 2) (BitVec.ofNat 32 occ_pos) := by
    right; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu32]; exact ⟨hbo, by omega, hev⟩
  refine ⟨by omega, by simp [scr', hcap], by omega, fun l hl => ?_, fun nd h1 h2 h3 => ?_⟩
  · by_cases hle : l = least_r.toNat
    · subst hle; dsimp only [occ_head']
      rw [List.getElem?_set_self hlr_len, Option.getD_some]; exact hnew_ptr
    · dsimp only [occ_head']
      rw [List.getElem?_set_ne (Ne.symm hle)]; exact hup _ (hheads l hl)
  · by_cases hnd : nd = occ_pos
    · subst hnd; dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
        List.getElem?_set_self (by simp; omega), Option.getD_some, Option.getD_some]
      exact ⟨hcr, hup _ hhead_ok⟩
    · have hnd_old : nd + 1 < occ_pos := by omega
      dsimp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      obtain ⟨hcr', hnxt'⟩ := hnodes nd h1 hnd_old h3
      exact ⟨hcr', hup _ hnxt'⟩

end Helpers

/-! ## 2. Pair Heapsort Proofs (`full_cong_sift_pairs_fid_wp`, `full_cong_sort_pairs_fid_wp`) -/

section SiftSortProofs

theorem full_cong_sift_pairs_fid_wp (Γ : Env) :
    ∀ a m Q X, fidCongSiftPairsSpec a m Q X →
      Func.wp Γ full_cong_sift_pairs_fid_body a m Q X := by
  rintro ⟨ap, start, n, ⟨⟩⟩ m0 Q X ⟨P, a0, R, hst_lt, h2n_le, hlen_bd, hok0, hm0, hQ⟩
  unfold Func.wp full_cong_sift_pairs_fid_body
  m6b_to_group
  refine wp_join_group (ts := [i64])
    (fun (_, ()) m_ret => ∃ a : List (BitVec 32),
      a.length = a0.length ∧ FidPairsOk P a n.toNat ∧
      (∀ idx, 2 * n.toNat ≤ idx → a[idx]? = a0[idx]?) ∧
      (array (t := i32) ap a ⋆ R) m_ret)
    (fun _ ⟨_, ⟨⟩⟩ m_ret ⟨a, hal, hok, htail, hm⟩ => by
      m6b_steps; exact hQ a m_ret hal hok htail hm)
    ?_
  intro Jbrk hJbrk
  m6b_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (root, ()) ml => ∃ a : List (BitVec 32),
      root.toNat < n.toNat ∧ a.length = a0.length ∧ FidPairsOk P a n.toNat ∧
      (∀ idx, 2 * n.toNat ≤ idx → a[idx]? = a0[idx]?) ∧
      (array (t := i32) ap a ⋆ R) ml)
    (fun (root, ()) _ => n.toNat - root.toNat)
    (fun J hJ => by
      m6b_steps
      exact hJ (start, ()) m0 ⟨a0, hst_lt, rfl, hok0, fun _ _ => rfl, hm0⟩)
    (fun J (root, ()) ml ⟨a, hroot_lt, hal, hok, htail, hml⟩ ih => ?_)
  m6b_split; rotate_left 1
  · exact Bool.noConfusion hc
  clear hc
  let child : BitVec 64 := (root <<< 1#64) + 1#64
  have hchild_n : child.toNat = 2 * root.toNat + 1 := bv64_shl1_add1_lt (by omega)
  m6b_split
  · m6b_let; exact hJbrk (root, ()) ml ⟨a, hal, hok, htail, hml⟩
  have hchild_lt : 2 * root.toNat + 1 < n.toNat := by
    have h := bv64_ule_not_le hc; change child.toNat < n.toNat at h; omega
  clear hc
  have hroot2_n : (root <<< 1#64).toNat = 2 * root.toNat := bv64_shl1_lt (by omega)
  have hroot2_arr : (root <<< 1#64).toNat < a.length := by rw [hroot2_n]; omega
  have hroot21_arr : ((root <<< 1#64) + 1#64).toNat < a.length := by
    change child.toNat < a.length; omega
  have hchild2_n : (child <<< 1#64).toNat = 2 * child.toNat := bv64_shl1_lt (by omega)
  have hchild21_n : ((child <<< 1#64) + 1#64).toNat = 2 * child.toNat + 1 :=
    bv64_shl1_add1_lt (by omega)
  have hchild2_arr : (child <<< 1#64).toNat < a.length := by rw [hchild2_n]; omega
  have hchild21_arr : ((child <<< 1#64) + 1#64).toNat < a.length := by rw [hchild21_n]; omega
  m6b_to_group
  refine wp_join_group (ts := [i64, i32, i32])
    (fun (sw, sw_s, sw_r, ()) m1 => m1 = ml ∧
      (sw = root ∨ sw = child) ∧
      sw_s = a[2 * sw.toNat]?.getD 0#32 ∧ sw_r = a[2 * sw.toNat + 1]?.getD 0#32)
    ?_
    (fun Jsw1 hJsw1 => by
      have hroot_keep :
          a[(root <<< 1#64).toNat]'hroot2_arr = a[2 * root.toNat]?.getD 0#32 ∧
          a[((root <<< 1#64) + 1#64).toNat]'hroot21_arr = a[2 * root.toNat + 1]?.getD 0#32 := by
        constructor
        · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact list_getElem_congr hroot2_n _ _
        · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact list_getElem_congr hchild_n _ _
      have hchild_keep :
          a[(child <<< 1#64).toNat]'hchild2_arr = a[2 * child.toNat]?.getD 0#32 ∧
          a[((child <<< 1#64) + 1#64).toNat]'hchild21_arr = a[2 * child.toNat + 1]?.getD 0#32 := by
        constructor
        · rw [List.getElem?_eq_getElem (by rw [← hchild2_n]; exact hchild2_arr), Option.getD_some]
          exact list_getElem_congr hchild2_n _ _
        · rw [List.getElem?_eq_getElem (by rw [← hchild21_n]; exact hchild21_arr), Option.getD_some]
          exact list_getElem_congr hchild21_n _ _
      m6b_split
      · m6b_let
        exact hJsw1 (child, a[(child <<< 1#64).toNat]'hchild2_arr,
          a[((child <<< 1#64) + 1#64).toNat]'hchild21_arr, ()) ml
          ⟨rfl, Or.inr rfl, hchild_keep.1, hchild_keep.2⟩
      clear hc; m6b_split
      · clear hc; m6b_split
        · m6b_let
          exact hJsw1 (child, a[(child <<< 1#64).toNat]'hchild2_arr,
            a[((child <<< 1#64) + 1#64).toNat]'hchild21_arr, ()) ml
            ⟨rfl, Or.inr rfl, hchild_keep.1, hchild_keep.2⟩
        m6b_let
        exact hJsw1 (root, a[(root <<< 1#64).toNat]'hroot2_arr,
          a[((root <<< 1#64) + 1#64).toNat]'hroot21_arr, ()) ml
          ⟨rfl, Or.inl rfl, hroot_keep.1, hroot_keep.2⟩
      m6b_let
      exact hJsw1 (root, a[(root <<< 1#64).toNat]'hroot2_arr,
        a[((root <<< 1#64) + 1#64).toNat]'hroot21_arr, ()) ml
        ⟨rfl, Or.inl rfl, hroot_keep.1, hroot_keep.2⟩)
  rintro _ ⟨sw1, sw_s1, sw_r1, ⟨⟩⟩ m1 ⟨hm1_eq, hsw1_eq, hsw1_s, hsw1_r⟩
  subst m1
  let right : BitVec 64 := child + 1#64
  have hright_n : right.toNat = 2 * root.toNat + 2 := by
    dsimp only [right]; rw [bv64_add1_lt (by omega), hchild_n]
  m6b_to_group
  refine wp_join_group (ts := [i64, i32, i32])
    (fun (sw2, sw_s2, sw_r2, ()) m2 => m2 = ml ∧
      (sw2 = root ∨ (root.toNat < sw2.toNat ∧ sw2.toNat < n.toNat)) ∧
      sw_s2 = a[2 * sw2.toNat]?.getD 0#32 ∧ sw_r2 = a[2 * sw2.toNat + 1]?.getD 0#32)
    ?_
    (fun Jsw2 hJsw2 => by
      have hsw1_ok : sw1 = root ∨ (root.toNat < sw1.toNat ∧ sw1.toNat < n.toNat) :=
        hsw1_eq.elim Or.inl fun h => Or.inr (by subst h; omega)
      m6b_split; rotate_left 1
      · m6b_let; exact hJsw2 (sw1, sw_s1, sw_r1, ()) ml ⟨rfl, hsw1_ok, hsw1_s, hsw1_r⟩
      have hright_lt : right.toNat < n.toNat := bv64_ult_lt hc
      have hright2_n : (right <<< 1#64).toNat = 2 * right.toNat := bv64_shl1_lt (by omega)
      have hright21_n : ((right <<< 1#64) + 1#64).toNat = 2 * right.toNat + 1 :=
        bv64_shl1_add1_lt (by omega)
      have hright2_arr : (right <<< 1#64).toNat < a.length := by rw [hright2_n]; omega
      have hright21_arr : ((right <<< 1#64) + 1#64).toNat < a.length := by rw [hright21_n]; omega
      have hright_keep :
          a[(right <<< 1#64).toNat]'hright2_arr = a[2 * right.toNat]?.getD 0#32 ∧
          a[((right <<< 1#64) + 1#64).toNat]'hright21_arr = a[2 * right.toNat + 1]?.getD 0#32 := by
        constructor
        · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact list_getElem_congr hright2_n _ _
        · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact list_getElem_congr hright21_n _ _
      clear hc; m6b_to_group
      refine wp_unroll_group fun Jsw2' hJsw2' => ?_
      have hpick_r : Jsw2' (right, a[(right <<< 1#64).toNat]'hright2_arr,
          a[((right <<< 1#64) + 1#64).toNat]'hright21_arr, ()) ml :=
        hJsw2' _ ml (by
          m6b_let
          exact hJsw2 (right, a[(right <<< 1#64).toNat]'hright2_arr,
            a[((right <<< 1#64) + 1#64).toNat]'hright21_arr, ()) ml
            ⟨rfl, Or.inr ⟨by omega, hright_lt⟩, hright_keep.1, hright_keep.2⟩)
      have hkeep_1 : Jsw2' (sw1, sw_s1, sw_r1, ()) ml :=
        hJsw2' _ ml (by
          m6b_let
          exact hJsw2 (sw1, sw_s1, sw_r1, ()) ml ⟨rfl, hsw1_ok, hsw1_s, hsw1_r⟩)
      m6b_split
      · m6b_let; exact hpick_r
      clear hc; m6b_split
      · clear hc; m6b_split
        · m6b_let; exact hpick_r
        m6b_let; exact hkeep_1
      m6b_let; exact hkeep_1)
  rintro _ ⟨sw2, sw_s2, sw_r2, ⟨⟩⟩ m2 ⟨hm2_eq, hsw2_ok, hsw2_s, hsw2_r⟩
  subst m2
  m6b_split
  · m6b_let; exact hJbrk (root, ()) ml ⟨a, hal, hok, htail, hml⟩
  have hsw2_ne : sw2 ≠ root := beq_eq_false_iff_ne.mp hc
  have ⟨hroot_lt_sw2, hsw2_lt⟩ := hsw2_ok.resolve_left hsw2_ne
  have hsw2_2_n : (sw2 <<< 1#64).toNat = 2 * sw2.toNat := bv64_shl1_lt (by omega)
  have hsw2_21_n : ((sw2 <<< 1#64) + 1#64).toNat = 2 * sw2.toNat + 1 :=
    bv64_shl1_add1_lt (by omega)
  have hsw2_2_arr : (sw2 <<< 1#64).toNat < a.length := by rw [hsw2_2_n]; omega
  have hsw2_21_arr : ((sw2 <<< 1#64) + 1#64).toNat < a.length := by rw [hsw2_21_n]; omega
  clear hc; m6b_steps
  have ht_s_eq : a[2 * root.toNat]'(by omega) = a[2 * root.toNat]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have ht_r_eq : a[2 * root.toNat + 1]'(by omega) = a[2 * root.toNat + 1]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hswp := fidPairsOk_swap hok hroot_lt hsw2_lt (by omega)
  have hm' : (array (t := i32) ap
      ((((a.set (2 * root.toNat) (a[2 * sw2.toNat]?.getD 0#32)).set (2 * root.toNat + 1)
        (a[2 * sw2.toNat + 1]?.getD 0#32)).set (2 * sw2.toNat) (a[2 * root.toNat]?.getD 0#32)).set
        (2 * sw2.toNat + 1) (a[2 * root.toNat + 1]?.getD 0#32)) ⋆ R) m := by
    change (array (t := i32) ap
      ((((a.set (root <<< 1#64).toNat sw_s2).set ((root <<< 1#64) + 1#64).toNat sw_r2).set
        (sw2 <<< 1#64).toNat (a[(root <<< 1#64).toNat]'hroot2_arr)).set
        ((sw2 <<< 1#64) + 1#64).toNat (a[((root <<< 1#64) + 1#64).toNat]'hroot21_arr)) ⋆ R) m at hm
    simp only [hroot2_n, show ((root <<< 1#64) + 1#64).toNat = 2 * root.toNat + 1 from hchild_n,
      hsw2_2_n, hsw2_21_n, hsw2_s, hsw2_r] at hm
    simpa only [← ht_s_eq, ← ht_r_eq] using hm
  refine ih (sw2, ()) m (by dsimp only; omega)
    ⟨_, hsw2_lt, hswp.1.trans hal, hswp.2.1,
     fun idx hidx => (hswp.2.2 idx hidx).trans (htail idx hidx), hm'⟩

theorem full_cong_sort_pairs_fid_wp (Γ : Env)
    (hSift : ∀ a m Q X, fidCongSiftPairsSpec a m Q X →
      Γ "full_cong_sift_pairs_fid" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fidCongSortPairsSpec a m Q X →
      Func.wp Γ full_cong_sort_pairs_fid_body a m Q X := by
  rintro ⟨ap, n, ⟨⟩⟩ m0 Q X ⟨P, a0, R, h2n_le, hlen_bd, hok0, hm0, hQ⟩
  unfold Func.wp full_cong_sort_pairs_fid_body
  m6b_split
  · m6b_steps; exact hQ a0 m0 rfl hok0 (fun _ _ => rfl) hm0
  have hn_gt1 : 1 < n.toNat := bv64_ule_not_le hc
  clear hc; m6b_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (st, ()) m1 => ∃ a : List (BitVec 32),
      st.toNat ≤ n.toNat ∧ a.length = a0.length ∧ FidPairsOk P a n.toNat ∧
      (∀ idx, 2 * n.toNat ≤ idx → a[idx]? = a0[idx]?) ∧
      (array (t := i32) ap a ⋆ R) m1)
    (fun (st, ()) _ => st.toNat)
    (fun J1 hJ1 => by
      m6b_steps
      exact hJ1 (n >>> 1#64, ()) m0
        ⟨a0, by rw [bv64_shr1_toNat]; omega, rfl, hok0, fun _ _ => rfl, hm0⟩)
    (fun J1 (st, ()) m1 ⟨a1, hst_le, hal1, hok1, htail1, hm1⟩ ih1 => ?_)
  m6b_split
  · have hst_pos : 0 < st.toNat := bv64_ult_lt hc
    have hst1_n : (st - 1#64).toNat = st.toNat - 1 := bv64_sub1_pos hst_pos
    clear hc; m6b_steps; m6b_call hSift
    refine ⟨P, a1, R, by change (st - 1#64).toNat < n.toNat; rw [hst1_n]; omega,
      by omega, by omega, hok1, hm1, fun a2 m2 hal2 hok2 htail2 hm2 => ?_⟩
    m6b_steps
    exact ih1 (st - 1#64, ()) m2 (by dsimp only; rw [hst1_n]; omega)
      ⟨a2, by rw [hst1_n]; omega, hal2.trans hal1, hok2,
       fun idx hidx => (htail2 idx hidx).trans (htail1 idx hidx), hm2⟩
  clear hc; m6b_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (ed, ()) m2 => ∃ a : List (BitVec 32),
      1 ≤ ed.toNat ∧ ed.toNat ≤ n.toNat ∧ a.length = a0.length ∧ FidPairsOk P a n.toNat ∧
      (∀ idx, 2 * n.toNat ≤ idx → a[idx]? = a0[idx]?) ∧
      (array (t := i32) ap a ⋆ R) m2)
    (fun (ed, ()) _ => ed.toNat)
    (fun J2 hJ2 => by
      m6b_steps
      exact hJ2 (n, ()) m1 ⟨a1, by omega, Nat.le_refl _, hal1, hok1, htail1, hm1⟩)
    (fun J2 (ed, ()) m2 ⟨a2, hed1, hed_le, hal2, hok2, htail2, hm2⟩ ih2 => ?_)
  m6b_split; rotate_left 1
  · m6b_steps; exact hQ a2 m2 hal2 hok2 htail2 hm2
  have hed_gt1 : 1 < ed.toNat := bv64_ult_lt hc
  have hed'_n : (ed - 1#64).toNat = ed.toNat - 1 := bv64_sub1_pos (by omega)
  let ed' : BitVec 64 := ed - 1#64
  have h0_arr : 0 < a2.length := by omega
  have h1_arr : 1 < a2.length := by omega
  have hed'2_n : (ed' <<< 1#64).toNat = 2 * ed'.toNat :=
    bv64_shl1_lt (by dsimp only [ed']; rw [hed'_n]; omega)
  have hed'21_n : ((ed' <<< 1#64) + 1#64).toNat = 2 * ed'.toNat + 1 :=
    bv64_shl1_add1_lt (by dsimp only [ed']; rw [hed'_n]; omega)
  have hed'2_arr : (ed' <<< 1#64).toNat < a2.length := by
    rw [hed'2_n]; dsimp only [ed']; rw [hed'_n]; omega
  have hed'21_arr : ((ed' <<< 1#64) + 1#64).toNat < a2.length := by
    rw [hed'21_n]; dsimp only [ed']; rw [hed'_n]; omega
  clear hc; m6b_steps
  have h0_bv : (BitVec.ofNat 64 0).toNat = 0 := rfl
  have h1_bv : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have h0_eq : a2[0]'h0_arr = a2[2 * 0]?.getD 0#32 := by
    rw [Nat.mul_zero, List.getElem?_eq_getElem h0_arr, Option.getD_some]
  have h1_eq : a2[1]'h1_arr = a2[2 * 0 + 1]?.getD 0#32 := by
    rw [Nat.mul_zero, Nat.zero_add, List.getElem?_eq_getElem h1_arr, Option.getD_some]
  have he2_eq : a2[2 * ed'.toNat]'(by dsimp only [ed']; rw [hed'_n]; omega) =
      a2[2 * ed'.toNat]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by dsimp only [ed']; rw [hed'_n]; omega), Option.getD_some]
  have he21_eq : a2[2 * ed'.toNat + 1]'(by dsimp only [ed']; rw [hed'_n]; omega) =
      a2[2 * ed'.toNat + 1]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by dsimp only [ed']; rw [hed'_n]; omega), Option.getD_some]
  have hswp := fidPairsOk_swap hok2 (i := 0) (j := ed'.toNat) (by omega)
    (by dsimp only [ed']; rw [hed'_n]; omega) (by omega)
  change (array (t := i32) ap
    ((((a2.set (BitVec.ofNat 64 0).toNat (a2[(ed' <<< 1#64).toNat]'hed'2_arr)).set
      (BitVec.ofNat 64 1).toNat
      ((a2.set (BitVec.ofNat 64 0).toNat (a2[(ed' <<< 1#64).toNat]'hed'2_arr))[
        ((ed' <<< 1#64) + 1#64).toNat]'(by rw [List.length_set]; exact hed'21_arr))
      ).set (ed' <<< 1#64).toNat (a2[(BitVec.ofNat 64 0).toNat]'h0_arr)).set
      ((ed' <<< 1#64) + 1#64).toNat (a2[(BitVec.ofNat 64 1).toNat]'h1_arr)) ⋆ R) m at hm
  simp only [h0_bv, h1_bv, hed'2_n, hed'21_n] at hm
  rw [List.getElem_set_ne (by dsimp only [ed']; rw [hed'_n]; omega)] at hm
  have hm3 : (array (t := i32) ap
      ((((a2.set (2 * 0) (a2[2 * ed'.toNat]?.getD 0#32)).set (2 * 0 + 1)
        (a2[2 * ed'.toNat + 1]?.getD 0#32)).set (2 * ed'.toNat) (a2[2 * 0]?.getD 0#32)).set
        (2 * ed'.toNat + 1) (a2[2 * 0 + 1]?.getD 0#32)) ⋆ R) m := by
    simpa only [Nat.mul_zero, Nat.zero_add, ← h0_eq, ← h1_eq, ← he2_eq, ← he21_eq] using hm
  let a3 := (((a2.set (2 * 0) (a2[2 * ed'.toNat]?.getD 0#32)).set (2 * 0 + 1)
    (a2[2 * ed'.toNat + 1]?.getD 0#32)).set (2 * ed'.toNat) (a2[2 * 0]?.getD 0#32)).set
    (2 * ed'.toNat + 1) (a2[2 * 0 + 1]?.getD 0#32)
  change (array (t := i32) ap a3 ⋆ R) m at hm3
  m6b_call hSift
  refine ⟨P, a3, R, by change 0 < ed'.toNat; dsimp only [ed']; rw [hed'_n]; omega,
    by rw [hswp.1]; change 2 * ed'.toNat ≤ a2.length; dsimp only [ed']; rw [hed'_n]; omega,
    by rw [hswp.1]; omega,
    fidPairsOk_mono (by change (ed - 1#64).toNat ≤ n.toNat; rw [hed'_n]; omega) hswp.2.1, hm3,
    fun a4 m4 hal4 hok4 htail4 hm4 => ?_⟩
  m6b_steps
  exact ih2 (ed', ()) m4 (by dsimp only [ed']; rw [hed'_n]; omega)
    ⟨a4, by dsimp only [ed']; rw [hed'_n]; omega, by dsimp only [ed']; rw [hed'_n]; omega,
     hal4.trans (hswp.1.trans hal2),
     fidPairsOk_after_prefix (by change (ed - 1#64).toNat ≤ n.toNat; rw [hed'_n]; omega)
       hswp.2.1 hok4 htail4,
     fun idx hidx =>
       (htail4 idx (by change 2 * (ed - 1#64).toNat ≤ idx; rw [hed'_n]; omega)).trans
         ((hswp.2.2 idx hidx).trans (htail2 idx hidx)),
     hm4⟩

end SiftSortProofs

/-! ## 3. Forward-Subsumption Clause-Reduction Helpers & `full_cong_fwd_subsume_wp` -/

section FwdSubsumeHelpers

/-- Core `fwd_subsume` invariant allowing `lit_mark` to be dirty on indices listed in `tmp`. -/
abbrev FidFsBaseOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 alen0 : Nat) (fuel0 : BitVec 64) (refs0 : List Nat) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
  s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
  s.core.cur_vars = cv0 ∧ s.core.arena_len = alen0 ∧ s.core.fuel = fuel0 ∧
  fullArenaClauseRefs s = refs0 ∧
  FullCongReprInv F_cur (2 * cv0) s.core.repr

theorem fidFsBaseOk_of_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hd : FullDenseInvW c F0 F_cur s)
    (hcv : s.core.cur_vars = cv0) (hal : s.core.arena_len = alen0) (hfl : s.core.fuel = fuel0)
    (hrefs : fullArenaClauseRefs s = refs0)
    (hrepr : FullCongReprInv F_cur (2 * cv0) s.core.repr) :
    FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s ∧
    (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8) :=
  ⟨⟨hd.1, hd.2.1, hd.2.2.1.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1,
    hd.2.2.2.2.2.2, hcv, hal, hfl, hrefs, hrepr⟩, hd.2.2.1.2⟩

theorem fidFsBaseOk_to_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s)
    (hlm : ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur s ∧
    s.core.cur_vars = cv0 ∧ s.core.arena_len = alen0 ∧ s.core.fuel = fuel0 ∧
    fullArenaClauseRefs s = refs0 ∧ FullCongReprInv F_cur (2 * cv0) s.core.repr :=
  ⟨⟨hb.1, hb.2.1, ⟨hb.2.2.1, hlm⟩, hb.2.2.2.1, hb.2.2.2.2.1,
    hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1⟩,
   hb.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.1,
   hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1,
   hb.2.2.2.2.2.2.2.2.2.2.2⟩

theorem fidFsBaseOk_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) {r' : List (BitVec 32)}
    (hrl : r'.length = 2 * c.max_vars) (hrepr' : FullCongReprInv F_cur (2 * cv0) r') :
    FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 { s with core := { s.core with repr := r' } } :=
  ⟨⟨{ hb.1.core_ok with repr_len := hrl }, hb.1.scratch_ok⟩,
   fullWitnessInv_with_repr hb.2.1 r', hb.2.2.1, hb.2.2.2.1,
   fullExtScratchOk_of_eq hb.2.2.2.2.1 rfl rfl rfl rfl,
   hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1,
   hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1, hrepr'⟩

theorem fidFsBaseOk_with_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) {lm' : List (BitVec 8)}
    (hlml : lm'.length = 2 * c.max_vars) :
    FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0
      { s with core := { s.core with lit_mark := lm' } } := by
  have hw' : FullWitnessInv c F0 F_cur { s.core with lit_mark := lm' } :=
    { hb.2.1 with
      arena := { hb.2.1.arena with len_ok := hb.2.1.arena.len_ok }
      watches := hb.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨⟨{ hb.1.core_ok with lit_mark_len := hlml }, hb.1.scratch_ok⟩,
    hw', hb.2.2.1, fullArenaVarsNodup_of_eq hb.2.2.2.1 rfl rfl,
    fullExtScratchOk_of_eq hb.2.2.2.2.1 rfl rfl rfl rfl,
    hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.2⟩

theorem fidFsBaseOk_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) {tmp' : List (BitVec 32)}
    (htl : tmp'.length = c.max_vars) :
    FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨{ hb.1.core_ok with tmp_len_arr := htl }, hb.1.scratch_ok⟩,
   fullWitnessInv_with_tmp hb.2.1 tmp', hb.2.2.1,
   fullArenaVarsNodup_of_eq hb.2.2.2.1 rfl rfl,
   fullExtScratchOk_of_eq hb.2.2.2.2.1 rfl rfl rfl rfl,
   hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1,
   hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1,
   hb.2.2.2.2.2.2.2.2.2.2.2⟩

theorem fidFs_lm_set_mark {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} {r : BitVec 32}
    (htmp_lt : ∀ j < msz, (tmp[j]?.getD 0#32).toNat < 2 * cv)
    (hlm_ok : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv))
    (hr_lt : r.toNat < 2 * cv) (hmsz_lt : msz < tmp.length) (_hr_len : r.toNat < lm.length) :
    let tmp' := tmp.set msz r
    let lm' := lm.set r.toNat 1#8
    (∀ j < msz + 1, (tmp'[j]?.getD 0#32).toNat < 2 * cv) ∧
    (∀ l < 2 * maxv, lm'[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz + 1, (tmp'[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) := by
  intro tmp' lm'; constructor
  · intro j hj; dsimp only [tmp']
    by_cases hjm : j = msz
    · subst hjm; rw [List.getElem?_set_self hmsz_lt, Option.getD_some]; exact hr_lt
    · rw [List.getElem?_set_ne (Ne.symm hjm)]; exact htmp_lt j (by omega)
  · intro l hl; dsimp only [lm', tmp']
    by_cases hlr : l = r.toNat
    · subst hlr; right
      refine ⟨msz, Nat.lt_succ_self msz, ?_, hr_lt⟩
      rw [List.getElem?_set_self hmsz_lt, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hlr)]
      rcases hlm_ok l hl with h0 | ⟨j, hj, hjl, hlc⟩
      · exact Or.inl h0
      · right; refine ⟨j, by omega, ?_, hlc⟩
        rw [List.getElem?_set_ne (by omega)]; exact hjl

theorem fidFs_lm_clear_step {maxv cv msz k : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} (hk : k < msz) (hk_lt : k < tmp.length)
    (htk_len : (tmp[k]'hk_lt).toNat < lm.length)
    (hinv : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, k ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, (lm.set (tmp[k]'hk_lt).toNat 0#8)[l]?.getD 0#8 = 0#8 ∨
      (∃ j, k + 1 ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv) := by
  intro l hl
  by_cases hlk : l = (tmp[k]'hk_lt).toNat
  · subst hlk; left; rw [List.getElem?_set_self htk_len, Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hlk)]
    rcases hinv l hl with h0 | ⟨j, hkj, hjm, hjl, hlc⟩
    · exact Or.inl h0
    · right
      have hjk : j ≠ k := by
        intro heq; subst heq
        rw [List.getElem?_eq_getElem hk_lt, Option.getD_some] at hjl
        exact hlk hjl.symm
      exact ⟨j, by omega, hjm, hjl, hlc⟩

theorem fidFs_lm_clear_from_zero {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)}
    (h : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, 0 ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv) :=
  fun l hl => (h l hl).elim Or.inl fun ⟨j, hj, hjl, hlc⟩ => Or.inr ⟨j, Nat.zero_le _, hj, hjl, hlc⟩

theorem fidFs_lm_clear_done {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)}
    (h : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, msz ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 := fun l hl =>
  (h l hl).elim id fun ⟨j, hj1, hj2, _⟩ => by omega

theorem fidFs_msz0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {p sz : Nat} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hp_ref : p ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s p = false)
    (hsz : fullArenaClauseSizeCore s.core p = sz)
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < sz, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true → False) :
    (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hwf := hw.arena.refs_wf p hp_ref
  have hbd : p + 3 + sz ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hsat := CNF.entails_clause_def.mp (hw.arena.entails p hp_ref hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat
  obtain ⟨l, hl_mem, hl_true⟩ := hsat
  obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff (hsz ▸ hbd)).mp hl_mem
  have hj' : j < sz := hsz ▸ hj
  have hget' : (s.core.arena[p + 3 + j]?.getD 0#32).toNat = l := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  exact hsem α hα j hj' (hget' ▸ hl_true)

theorem fidFs_msz1_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {p sz : Nat} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hp_ref : p ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s p = false)
    (hsz : fullArenaClauseSizeCore s.core p = sz) {u : Nat}
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < sz, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        evalLitVal α u = true) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  refine entails_of_eval_mem fun α hα => ⟨u, by simp, ?_⟩
  have hwf := hw.arena.refs_wf p hp_ref
  have hbd : p + 3 + sz ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hsat := CNF.entails_clause_def.mp (hw.arena.entails p hp_ref hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat
  obtain ⟨l, hl_mem, hl_true⟩ := hsat
  obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff (hsz ▸ hbd)).mp hl_mem
  have hj' : j < sz := hsz ▸ hj
  have hget' : (s.core.arena[p + 3 + j]?.getD 0#32).toNat = l := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  exact hsem α hα j hj' (hget' ▸ hl_true)

theorem fidFs_k_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {sp sk_in : FullState}
    {p : BitVec 64} {sz k : BitVec 32}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk_in)
    (har : sk_in.core.arena = sp.core.arena) (hp_ref : p.toNat ∈ refs0)
    (hng : fullArenaClauseGarbCore sp.core p.toNat = false)
    (hsz : fullArenaClauseSizeCore sp.core p.toNat = sz.toNat)
    (hp_le : p.toNat + 3 + sz.toNat ≤ alen0) (hk : k.toNat < sz.toNat) :
    ∃ hbd : (p + 3#64 + k.setWidth 64).toNat < sk_in.core.arena.length,
      (sk_in.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hbd).toNat < 2 * cv0 := by
  have hac := c.harena; unfold dimacsBound at hac
  have hp_sd : p.toNat ∈ fullArenaClauseRefsCore sk_in.core := by
    have h := hb.2.2.2.2.2.2.2.2.2.2.1
    change fullArenaClauseRefsCore sk_in.core = refs0 at h
    exact h.symm ▸ hp_ref
  have hng_sd : fullArenaClauseGarbCore sk_in.core p.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢; rwa [har]
  have hsz_sd : fullArenaClauseSizeCore sk_in.core p.toNat = sz.toNat := by
    unfold fullArenaClauseSizeCore at hsz ⊢; rwa [har]
  have hal := hb.2.2.2.2.2.2.2.2.1
  have hle := hb.1.core_ok.arena_len_le
  have harr := hb.1.core_ok.arena_len_arr
  have hadd : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
      show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbd : (p + 3#64 + k.setWidth 64).toNat < sk_in.core.arena.length := by rw [hadd]; omega
  refine ⟨hbd, ?_⟩
  let l := sk_in.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hbd
  have hl_mem : l.toNat ∈ fullArenaClauseLitsCore sk_in.core p.toNat := by
    refine (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨k.toNat, by omega, ?_⟩
    exact congrArg BitVec.toNat (list_getElem_congr hadd.symm _ _)
  have hlt := hb.2.1.arena.lits_lt p.toNat hp_sd hng_sd l.toNat hl_mem
  rwa [hb.2.2.2.2.2.2.2.1] at hlt

theorem fidFs_k_sem_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 : Nat} {s : FullState} {p k msz : Nat} (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0) (hcv : s.core.cur_vars = cv0)
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < s.core.arena.length)
    (hl_lt : (s.core.arena[p + 3 + k]'hk_arr).toNat < 2 * cv0)
    (hslt : (s.core.vals[(s.core.arena[p + 3 + k]'hk_arr).toNat]?.getD 0#8).slt 0#8 = true) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het
  by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := by omega
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    have hf := fid_lit_false_of_vals_slt0 hw hcl0 (hcv ▸ hl_lt) hslt α hα
    rw [het] at hf; cases hf

theorem fidFs_k_sem_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 : Nat} {s : FullState} {p k msz : Nat} {r : BitVec 32}
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (hcv : s.core.cur_vars = cv0)
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < s.core.arena.length) (hr_lt : r.toNat < 2 * cv0)
    (heqv : LitEquiv (cnfOfClauses F_cur) (s.core.arena[p + 3 + k]'hk_arr).toNat r.toNat)
    (hslt : (s.core.vals[r.toNat]?.getD 0#8).slt 0#8 = true) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het
  by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := by omega
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    have hev_r : evalLitVal α r.toNat = true := by
      have h := fid_litEquiv_eval heqv hα; rwa [← h]
    have hf := fid_lit_false_of_vals_slt0 hw hcl0 (hcv ▸ hr_lt) hslt α hα
    rw [hev_r] at hf; cases hf

theorem fidFs_k_sem_mem {F_cur : List (List Nat)} {maxv cv0 p k msz : Nat}
    {ar tmp : List (BitVec 32)} {lm : List (BitVec 8)} {r : BitVec 32}
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < ar.length) (hr_lt : r.toNat < 2 * cv0) (hcv : cv0 ≤ maxv)
    (hlm_ok : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0))
    (hneq : lm[r.toNat]?.getD 0#8 ≠ 0#8)
    (heqv : LitEquiv (cnfOfClauses F_cur) (ar[p + 3 + k]'hk_arr).toNat r.toNat) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (tmp[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het
  by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := by omega
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    rcases hlm_ok r.toNat (by omega) with h0 | ⟨q, hq, hqr, _⟩
    · exact absurd h0 hneq
    · refine ⟨q, hq, ?_⟩
      rw [hqr, ← fid_litEquiv_eval heqv hα]; exact het

theorem fidFs_k_sem_push {F_cur : List (List Nat)} {p k msz : Nat}
    {ar tmp : List (BitVec 32)} {r : BitVec 32}
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < ar.length) (hmsz_lt : msz < tmp.length)
    (heqv : LitEquiv (cnfOfClauses F_cur) (ar[p + 3 + k]'hk_arr).toNat r.toNat) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz + 1, evalLitVal α ((tmp.set msz r)[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het
  by_cases hjk : j < k
  · obtain ⟨q, hq, hqt⟩ := hsem α hα j hjk het
    refine ⟨q, by omega, ?_⟩
    rw [List.getElem?_set_ne (by omega)]; exact hqt
  · obtain rfl : j = k := by omega
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    refine ⟨msz, Nat.lt_succ_self _, ?_⟩
    rw [List.getElem?_set_self hmsz_lt, Option.getD_some, ← fid_litEquiv_eval heqv hα]
    exact het

theorem fidFs_base_vals_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState} {x : Nat}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) (hx : x < 2 * cv0) :
    x < s.core.vals.length := by
  have := hb.1.core_ok.vals_len; have := hb.1.core_ok.cur_vars_le
  have := hb.2.2.2.2.2.2.2.1; omega

theorem fidFs_base_lm_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState} {x : Nat}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) (hx : x < 2 * cv0) :
    x < s.core.lit_mark.length := by
  have := hb.1.core_ok.lit_mark_len; have := hb.1.core_ok.cur_vars_le
  have := hb.2.2.2.2.2.2.2.1; omega

/-- Shared state invariant for the inner subsumption scan (`k`/`nd`/`dj`) in Pass 2. -/
abbrev FidFsScanInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 alen0 : Nat) (fuel0 : BitVec 64) (refs0 : List Nat) (s2 sk : FullState) (msz : Nat)
    (s : FullState) : Prop :=
  FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s ∧
  s.core.arena = s2.core.arena ∧ s.core.vals = s2.core.vals ∧
  s.core.tmp = sk.core.tmp ∧ s.core.lit_mark = sk.core.lit_mark ∧
  s.core.inconsistent = 0#64 ∧ s.scratch = s2.scratch ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
    (∃ j < msz, (s.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0))

theorem fidFsScanInv_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s2 sk s : FullState} {msz : Nat}
    (h : FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz s)
    {r' : List (BitVec 32)} (hrl : r'.length = 2 * c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) r') :
    FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz
      { s with core := { s.core with repr := r' } } :=
  ⟨fidFsBaseOk_with_repr h.1 hrl hrepr', h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
   h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem fidFs_cr_ar {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState} {cr : BitVec 32}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) (hcr : cr.toNat ∈ refs0) :
    cr.toNat < s.core.arena.length ∧
    (cr.setWidth 64 + 2#64).toNat < s.core.arena.length ∧
    (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 ∧
    cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤ alen0 := by
  have hac := c.harena; unfold dimacsBound at hac
  have hcr_s : cr.toNat ∈ fullArenaClauseRefsCore s.core := by
    have h := hb.2.2.2.2.2.2.2.2.2.2.1
    change fullArenaClauseRefsCore s.core = refs0 at h
    exact h.symm ▸ hcr
  have hwf := hb.2.1.arena.refs_wf cr.toNat hcr_s
  have hle := hb.1.core_ok.arena_len_le
  have harr := hb.1.core_ok.arena_len_arr
  have hal := hb.2.2.2.2.2.2.2.2.1
  have h3 : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
    rw [bv64_add2_lt (by rw [bv_zext32_toNat]; have := cr.isLt; omega), bv_zext32_toNat]
  exact ⟨by omega, by rw [h3]; omega, h3, by omega⟩

end FwdSubsumeHelpers


end LeanQbe.T.Examples.Kissat.FullFidelityCong

end
