module

public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1

/-!
# Kissat M5 Wave 1 (`PR-W1A`) `Func.wp` Proofs — Part 2b (`FullM5HeurCoreProof2b`)

Proves UNSAT-only parametric `Func.wp` contracts (`XPost := False`, `0` SAT proofs) for:
1. `full_learn_clause_m5_wp` against canonical `Full.fullLearnClauseSpec` (`RC-09`: sets
   `used = 31u` via `ar[new_ref] |= 31u << 27` on every newly learned large clause).
2. `full_analyze_m5_wp` against canonical `Full.fullAnalyzeSpec` (`RC-10`: `probing == 0` guard
   around OTFS `tmp[0]` + `full_restore_bump_ana_m5`, post-`full_min_shrink`
   `full_restore_bump_ana_m5` + `full_tick_rel`, and `full_ema_update`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5HeurCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullLearnAnaTactics FullLearnAnaHelpers

open scoped FullArenaTactics FullLearnAnaTactics

section LearnAnalyzeProof

private theorem m5_la_bv32_lshr_1 (x : BitVec 32) :
    (x >>> 1#32).toNat = x.toNat / 2 := bv32_lshr_1 x
private theorem m5_la_i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (i8_sext32_eq0 v)
private theorem m5_la_bv32_0_sext_mul4 :
    ((0#32 : BitVec 32).signExtend 64 * 4#64) = 0#64 := rfl
private theorem m5_la_bv32_1_sext_mul4 :
    ((1#32 : BitVec 32).signExtend 64 * 4#64) = 4#64 := rfl
attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true m5_la_bv32_lshr_1
  m5_la_i8_sext32_eq0_prop m5_la_bv32_0_sext_mul4 m5_la_bv32_1_sext_mul4

private theorem m5_la_bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem m5_la_bv64_sub1_toNat {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx := x.isLt; bv_omega

private theorem m5_la_getElem_congr_idx {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) {hi : i < xs.length} {hj : j < xs.length} :
    xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem m5_la_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

private theorem m5_nat_lt31_bv32_msb0 {n : Nat} (hn : n < 2 ^ 31 - 1) :
    let v := (BitVec.ofNat 64 n).setWidth 32
    v.toNat = n ∧ v ≠ 0xFFFFFFFF#32 ∧ (v &&& 0x80000000#32) = 0#32 := by
  have hn_mod : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  have hto : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), hn_mod]
  refine ⟨hto, ?_, ?_⟩
  · intro heq; have h1 := congrArg BitVec.toNat heq; rw [hto] at h1
    have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
  · apply BitVec.eq_of_getElem_eq; intro i hi
    rw [BitVec.getElem_and, BitVec.getElem_zero]
    by_cases h31 : i = 31
    · subst h31; rw [BitVec.getElem_eq_testBit_toNat, hto, Nat.testBit,
        Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega : n < 2 ^ 31)]; simp
    · rw [show (0x80000000#32 : BitVec 32)[i]'hi = false from by revert i hi h31; decide]
      simp

private theorem m5_tmp_take1_eq {tmp : List (BitVec 32)} {u : BitVec 32} (h1 : 1 ≤ tmp.length)
    (h0 : tmp[0]? = some u) : (tmp.take 1).map BitVec.toNat = [u.toNat] := by
  cases tmp with
  | nil => simp at h1
  | cons a _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0; simp

private theorem m5_tmp_take2_eq {tmp : List (BitVec 32)} {u v : BitVec 32} (h2 : 2 ≤ tmp.length)
    (h0 : tmp[0]? = some u) (h1 : tmp[1]? = some v) :
    (tmp.take 2).map BitVec.toNat = [u.toNat, v.toNat] := by
  rcases tmp with _ | ⟨a, _ | ⟨b, _⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    subst h0 h1; simp

private theorem m5_fullArenaVarsNodup_congr_core {s s' : FullState}
    (h : FullArenaVarsNodup s) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) : FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
    fullArenaClauseGarbCore fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    fullArenaHdrCore
  rw [har, hal]; exact h

private theorem m5_safetySlice_core_eq {c : FullCfg} {s s' : FullState}
    (h : PreservesCoreSlice (fullSafetySlice c).coreProj s s') : s'.core = s.core :=
  fullCoreState_agrees_with_scratch h

/-! ### Bridge between `FullLearnAnaSpecs` and canonical `Full` invariants -/

private theorem m5_laOtfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem m5_canon_to_laOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem m5_laCut_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullLearnAnaSpecs.FullWitnessCutInv c F0 F_cur cut k) :
    FullWitnessCutInv c F0 F_cur cut k :=
  ⟨m5_laOtfs_to_canon h.toFullOtfsWitnessInv, h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

private theorem m5_canon_to_laCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) :
    FullLearnAnaSpecs.FullWitnessCutInv c F0 F_cur cut k :=
  ⟨m5_canon_to_laOtfs h.toFullOtfsWitnessInv, h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

private theorem m5_laOtfsInv_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s) :
    FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, m5_laOtfs_to_canon h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem m5_canon_to_laOtfsInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) :
    FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, m5_canon_to_laOtfs h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem m5_laCutInv_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullLearnAnaSpecs.FullCutInvW c F0 F_cur cut s) :
    FullCutInvW c F0 F_cur cut s :=
  ⟨h.1, m5_laCut_to_canon h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem m5_canon_to_laCutInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s) :
    FullLearnAnaSpecs.FullCutInvW c F0 F_cur cut s :=
  ⟨h.1, m5_canon_to_laCut h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem m5_sparse_to_canonOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullOtfsInvW c F0 F_cur s :=
  m5_laOtfsInv_to_canon (FullLearnAnaSpecs.FullSparseInvW.toOtfs h)

private theorem m5_sparse_to_canonCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) :
    FullCutInvW c F0 F_cur s.core.trail_end s :=
  m5_laCutInv_to_canon (FullLearnAnaSpecs.FullSparseInvW.toCut h)

private theorem m5_laSparse_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullSparseInvW c F0 F_cur s) :
    FullSparseInvW c F0 F_cur s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem m5_cut_to_canonOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s) : FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, h.2.1.toFullOtfsWitnessInv, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ### Setting `used = 31` (`||| 0xF8000000#32`) preserves `FullSparseInvW` -/

private theorem m5_bv32_or_used31_garb (h : BitVec 32) :
    ((h ||| 0xF8000000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_and]
  have h0 : ((0xF8000000#32 : BitVec 32)[i]'hi && (0x00080000#32 : BitVec 32)[i]'hi) = false := by
    revert i hi; decide
  cases h1 : (0x00080000#32 : BitVec 32)[i]'hi <;> cases h2 : (0xF8000000#32 : BitVec 32)[i]'hi <;>
    simp_all

private theorem m5_bv32_or_used31_shrk (h : BitVec 32) :
    ((h ||| 0xF8000000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_and]
  have h0 : ((0xF8000000#32 : BitVec 32)[i]'hi && (0x00800000#32 : BitVec 32)[i]'hi) = false := by
    revert i hi; decide
  cases h1 : (0x00800000#32 : BitVec 32)[i]'hi <;> cases h2 : (0xF8000000#32 : BitVec 32)[i]'hi <;>
    simp_all

private theorem m5_orUsed31_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hs : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) :
    let ar' := s.core.arena.set cref (fullArenaHdr s cref ||| 0xF8000000#32)
    let s' : FullState := { s with core := { s.core with arena := ar' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro ar' s'
  have hlen := hs.1.core_ok
  have hw := hs.2.1
  have ha := hw.arena
  have hcref_wf := ha.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : s.core.arena[cref]? = some (fullArenaHdrCore s.core cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have ha_cref : s'.core.arena[cref]? = some (fullArenaHdrCore s.core cref ||| 0xF8000000#32) :=
    List.getElem?_set_self har_len
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (ha.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]? :=
        List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [m5_bv32_or_used31_shrk,
        show fullArenaHdrCore s.core cref = s.core.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
        · have := (ha.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (ha.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s', ar']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
      · have := (ha.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    by_cases hrc : r = cref
    · subst r; rw [ha_cref, hget_cref, Option.getD_some, Option.getD_some, m5_bv32_or_used31_garb]
    · dsimp only [s', ar']; rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hszr := hsz_eq r hr
    unfold fullArenaClauseLitsCore
    rw [hszr]; congr 1
    apply List.ext_getElem
    · have hwf := ha.refs_wf r hr
      simp only [List.length_take, List.length_drop, s', ar', List.length_set]
    · intro j hj1 hj2
      simp only [List.getElem_take, List.getElem_drop]
      dsimp only [s', ar']
      have hne_idx : cref ≠ r + 3 + j := by
        by_cases hrc : r = cref
        · subst r; omega
        · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
          · simp only [List.length_take, List.length_drop, s', ar', List.length_set] at hj1
            omega
          · omega
      exact List.getElem_set_ne hne_idx _
  have ha' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := ha.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢
          simpa only [ha_cref, hget_cref, Option.getD_some, m5_bv32_or_used31_shrk] using hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa only [s', ar', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (ha.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, ht0_hi, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (ha.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (ha.refs_wf cref hr).2.1; omega
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
          · omega
          · have := (ha.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo,
        by dsimp only [s']; exact Nat.lt_of_le_of_lt ht0_hi ht2, ?_⟩
      dsimp only [s', ar']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr] at hl
      exact ha.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr]
      exact ha.entails r hr hng
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := ha'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        change if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
        split
        · rename_i hbin; rw [ite_eq_left hbin] at hrs; exact hrs
        · rename_i hlg; rw [ite_eq_right hlg] at hrs
          obtain ⟨hrr, hng, hall⟩ := hrs
          exact ⟨hrefs.symm ▸ hrr, (hgarb_eq _ hrr).trans hng,
            fun q hq => hall q ((hlits_eq _ hrr) ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hmem := hw.reason_lit_mem idx hidx hne hlg
        have hrs := hw.reason_inv idx hidx hne
        rw [ite_eq_right (fun h => h hlg)] at hrs
        change (s.core.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s'.core _
        rw [hlits_eq _ hrs.1]; exact hmem }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen with arena_len_arr := by simp [s', ar', hlen.arena_len_arr] }, hs.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgarb_eq r hr] at hng
    change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
    rw [hlits_eq r hr]; exact hs.2.2.2.1 r hr hng
  have hext' : FullExtScratchOk c s' :=
    Full.FullExtScratchOk.of_pres hs.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
  exact ⟨⟨hlen', hw', hs.2.2.1, hnd', hext', hs.2.2.2.2.2⟩, hrefs,
    fun r hr => ⟨hgarb_eq r hr, hlits_eq r hr⟩⟩

/-! ### Helper preservation lemmas for `full_analyze_m5` -/

private theorem m5_fullCutInvW_with_conflicts {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s) (k' : BitVec 64) :
    FullCutInvW c F0 F_cur cut { s with scratch := { s.scratch with conflicts := k' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with }⟩, h.2.1, h.2.2.1, h.2.2.2.1,
    Full.FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r), h.2.2.2.2.2⟩

private theorem m5_fullCutInvW_with_tmp_tl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s) (tmp' : List (BitVec 32)) (tl' : Nat)
    (htmp : tmp'.length = c.max_vars) (htl : tl' ≤ c.max_vars) :
    FullCutInvW c F0 F_cur cut
      { s with core := { s.core with tmp := tmp', tmp_len := tl' } } := by
  refine ⟨⟨{ h.1.core_ok with tmp_len_arr := htmp, tmp_len_le := htl }, h.1.scratch_ok⟩, ?_,
    h.2.2.1, h.2.2.2.1, Full.FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
    h.2.2.2.2.2⟩
  exact ⟨{ h.2.1.toFullOtfsWitnessInv with
    arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
    watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.1.cut_le, h.2.1.reason_inv_cut, h.2.1.reason_lit_mem_cut⟩

private theorem m5_fullCutInvW_of_restoreBump {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (h : FullCutInvW c F0 F_cur cut s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' }
                scratch := sc' } : FullState).LengthsOk c)
    (hm0' : FullMrkZero c
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' })
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    FullCutInvW c F0 F_cur cut
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } := by
  refine ⟨hlen', ?_, ⟨hm0', h.2.2.1.2⟩, h.2.2.2.1,
    Full.FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ r => r), h.2.2.2.2.2⟩
  exact ⟨{ h.2.1.toFullOtfsWitnessInv with
    arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
    watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.1.cut_le, h.2.1.reason_inv_cut, h.2.1.reason_lit_mem_cut⟩

private theorem m5_fullOtfsInvW_of_restoreBump {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullOtfsInvW c F0 F_cur s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' }
                scratch := sc' } : FullState).LengthsOk c)
    (hm0' : FullMrkZero c
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' })
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    FullOtfsInvW c F0 F_cur
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } :=
  ⟨hlen',
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    ⟨hm0', h.2.2.1.2⟩, h.2.2.2.1,
    Full.FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ r => r), h.2.2.2.2.2⟩

private theorem m5_fullOtfsInvW_of_safetySlice {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullOtfsInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullOtfsInvW c F0 F_cur s' :=
  m5_laOtfsInv_to_canon (FullOtfsInvW.of_safetySlice (m5_canon_to_laOtfsInv h) hlen' hcore hpres)

/-! ## 1. `full_learn_clause_m5` (`Full.fullLearnClauseSpec`) -/

private theorem m5_learn_clause_post_ac_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_ac : FullState} {R : Mem 64 → Prop} {m_ac : Mem 64}
    {uip_lit wm : BitVec 32} {new_ref64 : BitVec 64} {max_lvl : Nat}
    {tmp_sw : List (BitVec 32)}
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X)
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hac_sparse : FullSparseInvW c F0 F_cur s_ac)
    (hcur_lt : s_ac.core.cur_level < s.core.cur_level)
    (hmax_pos : 0 < max_lvl) (hmax_le : max_lvl ≤ s_ac.core.cur_level)
    (hmax_lt28 : max_lvl < 2 * 2 ^ 28)
    (hcv_eq : s_ac.core.cur_vars = s.core.cur_vars)
    (hfuel : s_ac.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hws2 : s_ac.scratch.work_stk2 = s.scratch.work_stk2)
    (htmp_eq : s_ac.core.tmp = tmp_sw) (htlen_eq : s_ac.core.tmp_len = s.core.tmp_len)
    (hsw_1 : tmp_sw[1]? = some wm)
    (htl_2 : 2 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (huip_lt : uip_lit.toNat < 2 * s.core.cur_vars)
    (hwm_lt : wm.toNat < 2 * s.core.cur_vars)
    (htmp_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hwm_on_bt : ∃ idx < s_ac.core.trail_end,
      (s_ac.core.trl[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
      (s_ac.core.lvl[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hlow : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
      q = uip_lit.toNat ∨ ∃ idx < s_ac.core.trail_end,
        (s_ac.core.trl[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s_ac.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hr_spec : new_ref64 = 0xFFFFFFFF#64 ∨
      (new_ref64 ≠ 0xFFFFFFFF#64 ∧
        if new_ref64 = 0xFFFFFFFE#64 then
          (cnfOfClauses F_cur).EntailsClause (cnfClause [uip_lit.toNat, wm.toNat])
        else
          new_ref64.toNat < 2 ^ 31 - 1 ∧
          new_ref64.toNat ∈ fullArenaClauseRefs s_ac ∧
          fullArenaClauseGarb s_ac new_ref64.toNat = false ∧
          (∀ q ∈ fullArenaClauseLits s_ac new_ref64.toNat,
            q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat) ∧
          uip_lit.toNat ∈ fullArenaClauseLits s_ac new_ref64.toNat))
    (hm_ac : (FullMem c s_ac ⋆ R) m_ac) :
    wp Γ Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
          args := (Arg.var new_ref64, Arg.imm 4294967295, ()) } fun p36 =>
        Expr.jnz (Arg.var p36.1) (Expr.ret (Arg.imm 0, ()))
          (Expr.let_
            { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var uip_lit, ()) } fun p37 =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.pVals, Arg.var p37.1, ()) } fun p38 =>
              Expr.load i8 (Arg.var p38.1) fun ld =>
                Expr.let_
                  { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p39 =>
                  Expr.let_
                    { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld, ()) } fun p40 =>
                    Expr.let_
                      { sig := [i8], code := OpCode.sext 8 32,
                        args := (Arg.var p39.1, ()) } fun p41 =>
                      Expr.let_
                        { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                          args := (Arg.var p40.1, Arg.var p41.1, ()) } fun p42 =>
                        Expr.jnz (Arg.var p42.1) (Expr.ret (Arg.imm 0, ()))
                          (Expr.group (sig := [[]])
                            (fun _Ju =>
                              Blocks.cons
                                (fun _ =>
                                  Expr.group (sig := [[i32]])
                                    (fun _Js =>
                                      Blocks.cons
                                        (fun p43 =>
                                          Expr.let_
                                            { sig := [i64], code := OpCode.trunc 64 32,
                                              args := (Arg.var (BitVec.ofNat 64 max_lvl), ()) }
                                            fun p44 =>
                                            Expr.call (as := [i64, i32, i32, i32]) (bs := [])
                                              (rs := [i64]) "full_assign_lvl"
                                              (Arg.var c.hdr, Arg.var uip_lit, Arg.var p43.1,
                                                Arg.var p44.1, ())
                                              fun (_ : Tup Val []) =>
                                              Expr.call (as := [i64, i64]) (bs := []) (rs := [i64])
                                                "full_eager_subsume"
                                                (Arg.var c.hdr, Arg.var new_ref64, ())
                                                fun (_ : Tup Val []) =>
                                                  Expr.ret (rs := [i64]) (Arg.imm 1, ()))
                                        Blocks.nil)
                                    fun Js =>
                                    Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                        args := (Arg.var new_ref64, Arg.imm 4294967294, ()) }
                                      fun p =>
                                      Expr.jnz (Arg.var p.1)
                                        (Expr.let_
                                          { sig := [i32], code := OpCode.sext 32 64,
                                            args := (Arg.imm 1, ()) } fun p =>
                                          Expr.let_
                                            { sig := [i64, i64], code := OpCode.mul i64,
                                              args := (Arg.var p.1, Arg.imm 4, ()) } fun p =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.add i64,
                                                args := (Arg.var c.pTmp, Arg.var p.1, ()) } fun p =>
                                              Expr.load i32 (Arg.var p.1) fun ld =>
                                                Expr.let_
                                                  { sig := [i32, i32], code := OpCode.and i32,
                                                    args := (Arg.var ld, Arg.imm 2147483647, ()) }
                                                  fun p =>
                                                  Expr.let_
                                                    { sig := [i32, i32], code := OpCode.or i32,
                                                      args :=
                                                        (Arg.var p.1, Arg.imm 2147483648, ()) }
                                                    fun p =>
                                                    Expr.jump Js.1 (Arg.var p.1, ()))
                                        (Expr.let_
                                          { sig := [i64], code := OpCode.trunc 64 32,
                                            args := (Arg.var new_ref64, ()) } fun p =>
                                          Expr.jump Js.1 (Arg.var p.1, ())))
                                Blocks.nil)
                            fun Ju =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                args := (Arg.var new_ref64, Arg.imm 4294967294, ()) } fun p =>
                              Expr.jnz (Arg.var p.1)
                                (Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p =>
                                  Expr.load i64 (Arg.var p.1) fun ld =>
                                    Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                                        args := (Arg.var new_ref64, Arg.var ld, ()) } fun p =>
                                      Expr.jnz (Arg.var p.1)
                                        (Expr.let_
                                          { sig := [i64, i64], code := OpCode.add i64,
                                            args := (Arg.var c.hdr, Arg.imm 112, ()) } fun p =>
                                          Expr.load i64 (Arg.var p.1) fun ld_ar =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.mul i64,
                                                args := (Arg.var new_ref64, Arg.imm 4, ()) }
                                              fun p =>
                                              Expr.let_
                                                { sig := [i64, i64], code := OpCode.add i64,
                                                  args := (Arg.var ld_ar, Arg.var p.1, ()) }
                                                fun p_el =>
                                                Expr.load i32 (Arg.var p_el.1) fun ld_h =>
                                                  Expr.let_
                                                    { sig := [i32, i32], code := OpCode.shl i32,
                                                      args := (Arg.imm 31, Arg.imm 27, ()) }
                                                    fun p_sh =>
                                                    Expr.let_
                                                      { sig := [i32, i32], code := OpCode.or i32,
                                                        args := (Arg.var ld_h, Arg.var p_sh.1, ()) }
                                                      fun p_nh =>
                                                      Expr.store (Arg.var p_nh.1)
                                                        (Arg.var p_el.1)
                                                        (Expr.jump Ju.1 ()))
                                        (Expr.jump Ju.1 ()))
                                (Expr.jump Ju.1 ()))))
      m_ac := by
  have hac_len := hac_sparse.1
  have hcl := hac_len.core_ok
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have huip_vlen : uip_lit.toNat < s_ac.core.vals.length := by
    rw [hcl.vals_len]; have := hcl.cur_vars_le; omega
  c0_split
  · c0_steps
    exact hQ 0#64 s_ac m_ac hac_len (Or.inl rfl) hcv_eq hfuel hws2
      (fun h => by cases h) (fun _ => hac_sparse) (fun h => by cases h) hm_ac
  · have hne_ff : new_ref64 ≠ 0xFFFFFFFF#64 := by assumption
    have hnr_ok := (hr_spec.resolve_left hne_ff).2
    c0_split
    · c0_steps
      exact hQ 0#64 s_ac m_ac hac_len (Or.inl rfl) hcv_eq hfuel hws2
        (fun h => by cases h) (fun _ => hac_sparse) (fun h => by cases h) hm_ac
    · have huip_z : s_ac.core.vals[uip_lit.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]
        exact (by assumption : s_ac.core.vals[uip_lit.toNat] = 0#8)
      -- Join after `if (new_ref != 0xFFFFFFFEULL && new_ref < arena_len) ar[new_ref] |= 31u << 27;`
      refine wp_join_group (ts := []) (fun () m_u =>
          ∃ ar_u : List (BitVec 32),
            let s_u : FullState := { s_ac with core := { s_ac.core with arena := ar_u } }
            FullSparseInvW c F0 F_cur s_u ∧ fullArenaClauseRefs s_u = fullArenaClauseRefs s_ac ∧
            (∀ r ∈ fullArenaClauseRefs s_ac,
              fullArenaClauseGarb s_u r = fullArenaClauseGarb s_ac r ∧
              fullArenaClauseLits s_u r = fullArenaClauseLits s_ac r) ∧
            (FullMem c s_u ⋆ R) m_u) ?_ ?_
      · rintro _ ⟨⟩ m_u ⟨ar_u, hu_sparse, hrefs_u, hprops_u, hm_u⟩
        let s_u : FullState := { s_ac with core := { s_ac.core with arena := ar_u } }
        have hu_len := hu_sparse.1
        refine wp_join_group (ts := [i32]) (fun (rsn_bv, ()) m_r =>
            m_r = m_u ∧ rsn_bv ≠ 0xFFFFFFFF#32 ∧
            (if (rsn_bv &&& 0x80000000#32) ≠ 0#32 then
              let ot := (rsn_bv &&& 0x7FFFFFFF#32).toNat
              ot < 2 * s_u.core.cur_vars ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [uip_lit.toNat, ot]) ∧
              ∃ m < s_u.core.trail_end, (s_u.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
                (s_u.core.lvl[ot / 2]?.getD 0#32).toNat ≤ max_lvl
            else
              rsn_bv.toNat ∈ fullArenaClauseRefsCore s_u.core ∧
              fullArenaClauseGarbCore s_u.core rsn_bv.toNat = false ∧
              (∀ q ∈ fullArenaClauseLitsCore s_u.core rsn_bv.toNat,
                q = uip_lit.toNat ∨ ∃ m < s_u.core.trail_end,
                  (s_u.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                  (s_u.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl) ∧
              uip_lit.toNat ∈ fullArenaClauseLitsCore s_u.core rsn_bv.toNat)) ?_ ?_
        · rintro _ ⟨rsn_bv, ⟨⟩⟩ m_r ⟨rfl, hrsn_ne, hrsn_prop⟩
          have hte_lt : s_u.core.trail_end < c.max_vars := by
            have h1 := hu_sparse.2.1.trail_end_lt_of_unassigned (hcv_eq ▸ huip_lt) huip_z
            have := hcl.cur_vars_le; dsimp only [s_u] at h1 ⊢; omega
          have hml_tr : ((BitVec.ofNat 64 max_lvl).setWidth 32).toNat = max_lvl := by
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : max_lvl < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
          have hml_nz : (BitVec.ofNat 64 max_lvl).setWidth 32 ≠ 0#32 := fun heq => by
            have h0 := congrArg BitVec.toNat heq
            rw [hml_tr, show (0#32 : BitVec 32).toNat = 0 from rfl] at h0; omega
          c0_to_group; c0_call hAsgn
          refine ⟨c, s_u, R, rfl, hu_len, hm_u, ?_⟩
          rw [ite_eq_right (fun h => by
            dsimp only [s_u] at h hte_lt
            rw [huip_z] at h
            have := hcv_eq ▸ huip_lt
            rcases h with h | h | h
            · omega
            · omega
            · exact h rfl)]
          intro v rsn_let unfl_let flags' unass' phases' m_as hfll hph s_as0 hm_as
          have hrsn_let : rsn_let = rsn_bv := ite_eq_right hml_nz
          have hunfl_let : unfl_let = s_u.core.unflushed := ite_eq_right hml_nz
          c0_clean; c0_to_group
          let s_as : FullState :=
            { s_u with
              core :=
                { s_u.core with
                  vals := (s_u.core.vals.set uip_lit.toNat 1#8).set (uip_lit.toNat ^^^ 1) 0xFF#8
                  flags := flags'
                  lvl := s_u.core.lvl.set (uip_lit.toNat / 2)
                    ((BitVec.ofNat 64 max_lvl).setWidth 32)
                  rsns := s_u.core.rsns.set (uip_lit.toNat / 2) rsn_bv
                  trl := s_u.core.trl.set s_u.core.trail_end uip_lit
                  trail_pos := s_u.core.trail_pos.set (uip_lit.toNat / 2)
                    (BitVec.ofNat 32 s_u.core.trail_end)
                  trail_end := s_u.core.trail_end + 1
                  unassigned := unass', unflushed := s_u.core.unflushed }
              scratch := { s_u.scratch with phases := phases' } }
          have hml_bv : (BitVec.ofNat 64 max_lvl).setWidth 32 = BitVec.ofNat 32 max_lvl :=
            BitVec.eq_of_toNat_eq (by rw [hml_tr, bv32_ofNat_toNat (by omega)])
          have hsc_as : s_as.scratch.LengthsOk c := { hu_len.scratch_ok with phases_len := hph }
          have ⟨has_len, has_w⟩ := chronoAssign_preserves_fullWitness hu_sparse.2.1 hu_len hsc_as
            (rsn := rsn_bv) (unassigned' := unass') (unflushed' := s_u.core.unflushed)
            hfll (hcv_eq ▸ huip_lt) huip_z hmax_le (fun _ => hrsn_ne)
            (fun h0 => absurd h0 (by omega))
            (fun _ _ => by
              split
              · rename_i hbin; rw [ite_eq_left hbin] at hrsn_prop; exact hrsn_prop
              · rename_i hnbin; rw [ite_eq_right hnbin] at hrsn_prop
                exact ⟨hrsn_prop.1, hrsn_prop.2.1, hrsn_prop.2.2.1⟩)
            (fun _ _ hzero => by
              rw [ite_eq_right (fun h => absurd hzero h)] at hrsn_prop; exact hrsn_prop.2.2.2)
          have hm_as' : (FullMem c s_as ⋆ R) m_as := by
            simpa only [s_as, s_as0, v, hrsn_let, hunfl_let] using hm_as
          have hmne0 : max_lvl ≠ 0 := by omega
          have has_sparse : FullSparseInvW c F0 F_cur s_as :=
            ⟨by simpa [s_as, hml_bv, hmne0] using has_len,
             by simpa [s_as, hml_bv, hmne0] using has_w,
             hu_sparse.2.2.1, hu_sparse.2.2.2.1, hu_sparse.2.2.2.2.1, hu_sparse.2.2.2.2.2⟩
          have htmp_as_lt : ∀ k < s_as.core.tmp_len,
              (s_as.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk => by
            simpa only [s_as, s_u, htmp_eq, htlen_eq] using
              htmp_lt k (by simpa [s_as, s_u, htlen_eq] using hk)
          c0_call hEsub
          refine ⟨c, F0, F_cur, s_as, R, rfl, has_sparse, htmp_as_lt, ?_, hm_as', ?_⟩
          · intro _
            by_cases hfe : new_ref64 = 0xFFFFFFFE#64
            · subst hfe; exfalso; have : (0xFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 32 - 2 := rfl
              omega
            · simp only [hfe, ↓reduceIte] at hnr_ok
              change new_ref64.toNat ∈ fullArenaClauseRefs s_u
              rw [hrefs_u]; exact hnr_ok.2.1
          · intro ar' ag' sc' m_fin _ hfin_sparse hws2' hm_fin
            c0_steps
            exact hQ 1#64 _ m_fin hfin_sparse.1 (Or.inr (Or.inl rfl)) hcv_eq hfuel
              (hws2'.trans (by simp [s_as, s_u, hws2])) (fun h => by cases h)
              (fun h => by cases h) (fun _ => ⟨hfin_sparse, hcur_lt⟩) hm_fin
        · intro Jrsn hJrsn; c0_split
          · have hfe : new_ref64 = 0xFFFFFFFE#64 := by assumption
            simp only [hfe, ↓reduceIte] at hnr_ok
            have := hcl.cur_vars_le
            have hwm_lt31 : wm.toNat < 2 ^ 31 - 1 := by omega
            have hmask := bin_rsn_mask_props (l := wm) hwm_lt31
            have h1_lt : 1 < s_u.core.tmp.length := by rw [hu_len.core_ok.tmp_len_arr]; omega
            have htmp1_eq : s_u.core.tmp[1]'h1_lt = wm := Option.some.inj
              (by rw [← List.getElem?_eq_getElem h1_lt, show s_u.core.tmp = tmp_sw from htmp_eq,
                hsw_1])
            c0_steps
            refine wp_load_of (load_full_tmp1 (c := c) (s := s_u) (R := R) h1_lt hm_u) ?_
            c0_steps
            rw [htmp1_eq]
            refine hJrsn ((wm &&& 0x7FFFFFFF#32) ||| 0x80000000#32, ()) m_u ⟨rfl, hmask.1, ?_⟩
            rw [ite_eq_left hmask.2.1, hmask.2.2]
            exact ⟨hcv_eq ▸ hwm_lt, hnr_ok, hwm_on_bt⟩
          · have hne_fe : new_ref64 ≠ 0xFFFFFFFE#64 := by assumption
            simp only [hne_fe, ↓reduceIte] at hnr_ok
            obtain ⟨hlt31, href, hng, hlits_sub, huip_in⟩ := hnr_ok
            have hnr_bv := m5_nat_lt31_bv32_msb0 hlt31
            rw [BitVec.eq_of_toNat_eq (bv64_ofNat_toNat new_ref64.isLt)] at hnr_bv
            c0_steps
            refine hJrsn (new_ref64.setWidth 32, ()) m_u ⟨rfl, hnr_bv.2.1, ?_⟩
            rw [ite_eq_right (fun h => absurd hnr_bv.2.2 h), hnr_bv.1]
            obtain ⟨hgu, hlu⟩ := hprops_u new_ref64.toNat href
            exact ⟨by change _ ∈ fullArenaClauseRefs s_u; rw [hrefs_u]; exact href,
              hgu.trans hng,
              fun q hq => hlow q (hlits_sub q (by
                change q ∈ fullArenaClauseLits s_ac _; rw [← hlu]; exact hq)),
              by change uip_lit.toNat ∈ fullArenaClauseLits s_u _; rw [hlu]; exact huip_in⟩
      · -- `if (new_ref != 0xFFFFFFFEULL && new_ref < arena_len) ar[new_ref] |= 31u << 27;`
        intro Ju hJu; c0_split
        · have hne_fe : new_ref64 ≠ 0xFFFFFFFE#64 := by assumption
          simp only [hne_fe, ↓reduceIte] at hnr_ok
          obtain ⟨_, href, _, _, _⟩ := hnr_ok
          c0_split
          · have hnr_ar : new_ref64.toNat < s_ac.core.arena.length := by
              have hwf := hac_sparse.2.1.arena.refs_wf new_ref64.toNat href
              have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
            have hhdr_eq : s_ac.core.arena[new_ref64.toNat]'hnr_ar =
                fullArenaHdr s_ac new_ref64.toNat := by
              unfold fullArenaHdr fullArenaHdrCore
              rw [List.getElem?_eq_getElem hnr_ar, Option.getD_some]
            have hmask31 : ((31 : BitVec 32) <<< (27 : BitVec 32)) = 0xF8000000#32 := by decide
            have hmask31n : ((31 : BitVec 32) <<< (27 : Nat)) = 0xF8000000#32 := by decide
            c0_steps
            refine wp_load_of (FullArenaTactics.load_full_arena_ptr hm_ac) ?_
            c0_steps
            obtain ⟨hu_sp, hrefs_u, hprops_u⟩ :=
              m5_orUsed31_preserves_fullSparseW hac_sparse href
            exact hJu () m ⟨_, hu_sp, hrefs_u, hprops_u,
              by simpa only [hhdr_eq, hmask31, hmask31n] using hm⟩
          · c0_steps; exact hJu () m_ac ⟨s_ac.core.arena, hac_sparse, rfl,
              fun _ _ => ⟨rfl, rfl⟩, hm_ac⟩
        · c0_steps; exact hJu () m_ac ⟨s_ac.core.arena, hac_sparse, rfl,
            fun _ _ => ⟨rfl, rfl⟩, hm_ac⟩

/-- `full_learn_clause_m5` (sets `used = 31u` on newly learned large clauses) satisfies canonical
`Full.fullLearnClauseSpec` parametrically in `Γ`. -/
theorem full_learn_clause_m5_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X →
      Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ args m Q X, fullLearnClauseSpec args m Q X →
      Func.wp Γ full_learn_clause_m5_body args m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hs_c, hcur_pos, htl1, htl_cv, htmp_nd,
    htmp_vals, htmp_lvls, hent, hm, hQ⟩
  have hs := m5_canon_to_laOtfsInv hs_c
  have hcl := hs.1.core_ok
  have hw := hs.2.1
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hcur_le := hw.cur_level_le
  have hte_le := hcl.trail_end_le
  have hcv_le := hcl.cur_vars_le
  have htmp_len_arr := hcl.tmp_len_arr
  have huip_in : 0 < s.core.tmp.length := by omega
  let uip := s.core.tmp[0]'huip_in
  have huip_0 : s.core.tmp[0]? = some uip := List.getElem?_eq_getElem huip_in
  have huip_lt : uip.toNat < 2 * s.core.cur_vars := by
    have := (htmp_vals 0 htl1).1; rwa [huip_0, Option.getD_some] at this
  unfold Func.wp full_learn_clause_m5_body
  c0_clean; c0_split
  · -- Unit learned clause (`tmp_len == 1`)
    have htl_is1 : s.core.tmp_len = 1 := by bv_omega
    have hent_unit : (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat]) := by
      rwa [htl_is1, m5_tmp_take1_eq huip_in huip_0] at hent
    c0_to_group; c0_call hBt
    refine ⟨c, s, R, rfl, hs.1, by omega, fun _ => by omega, hw.trail_lits_lt, hm, ?_⟩
    intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt s_bt
      hbt_len hbt_te _ hbt_cl hbt_pres _ _ _ _ hbt_otfs hm_bt
    have hcl_0 : cl' = 0 := by
      rw [hbt_cl, show (0 : BitVec 64).toNat = 0 from rfl, Nat.min_zero]
    have hbt_w : FullWitnessInv c F0 F_cur s_bt.core := hbt_otfs F0 F_cur hs_c.2.1 (by omega)
    have hbt_sparse := fullBacktrack_preserves_fullSparseW hs hbt_len hbt_w rfl rfl rfl rfl rfl
      hbt_pres.1
    have huip_vlen : uip.toNat < vals'.length := by
      have hvl := hbt_len.core_ok.vals_len; dsimp only [s_bt] at hvl; omega
    c0_clean; c0_split
    · c0_clean; c0_steps
      exact hQ 0#64 s_bt m_bt hbt_len (Or.inl rfl) rfl (Nat.le_refl _) hbt_pres.2.2.1
        (fun h => by cases h) (fun _ => hbt_sparse) (fun h => by cases h) hm_bt
    · have huip_z : vals'[uip.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]
        exact (by assumption : s_bt.core.vals[s.core.tmp[0].toNat] = 0#8)
      have hbt_te_lt : te' < c.max_vars := by
        have := hbt_w.trail_end_lt_of_unassigned huip_lt huip_z; dsimp only [s_bt] at this; omega
      c0_to_group; c0_call hAsgn
      refine ⟨c, s_bt, R, rfl, hbt_len, hm_bt, ?_⟩
      rw [ite_eq_right (fun h => by
        dsimp only [s_bt] at h
        rw [show s.core.tmp[0] = uip from rfl] at h
        simp only [huip_z, ne_eq, not_true_eq_false, or_false] at h; omega)]
      intro v rsn_let unfl_let flags' unass'' phases' m_f hfll hph s_f0 hm_f
      have hrsn_let : rsn_let = 0xFFFFFFFF#32 := ite_eq_left rfl
      have hunfl_let : unfl_let = s_bt.core.unflushed + 1#64 := ite_eq_left rfl
      c0_clean; c0_steps
      let s_fin : FullState :=
        { s_bt with
          core :=
            { s_bt.core with
              vals := (vals'.set uip.toNat 1#8).set (uip.toNat ^^^ 1) 0xFF#8
              flags := flags', lvl := lvl'.set (uip.toNat / 2) 0#32
              rsns := rsns'.set (uip.toNat / 2) 0xFFFFFFFF#32
              trl := trl'.set te' uip
              trail_pos := tp'.set (uip.toNat / 2) (BitVec.ofNat 32 te')
              trail_end := te' + 1, unassigned := unass''
              unflushed := s_bt.core.unflushed + 1#64 }
          scratch := { sc' with phases := phases' } }
      have hsc_f : s_fin.scratch.LengthsOk c := { hbt_len.scratch_ok with phases_len := hph }
      have ⟨hfin_len, hfin_w⟩ := chronoAssign_preserves_fullWitness hbt_w hbt_len hsc_f
        (rsn := 0xFFFFFFFF#32) (unassigned' := unass'') (unflushed' := s_bt.core.unflushed + 1#64)
        hfll huip_lt huip_z (Nat.zero_le _) (fun h => by omega) (fun _ => hent_unit)
        (fun h _ => by omega) (fun h _ _ => by omega)
      have hfin_sparse : FullSparseInvW c F0 F_cur s_fin :=
        ⟨hfin_len, hfin_w,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.2.2⟩
      have hm_f' : (FullMem c s_fin ⋆ R) m_f := by
        simpa only [s_fin, s_f0, s_bt, v, hrsn_let, hunfl_let,
          show (0 : BitVec 32) = 0#32 from rfl, show s.core.tmp[0] = uip from rfl] using hm_f
      exact hQ 1#64 s_fin m_f hfin_len (Or.inr (Or.inl rfl)) rfl (Nat.le_refl _)
        (by dsimp only [s_fin, s_bt]; exact hbt_pres.2.2.1) (fun h => by cases h)
        (fun h => by cases h)
        (fun _ => ⟨hfin_sparse, by dsimp only [s_fin, s_bt]; omega⟩) hm_f'
  · -- Non-unit learned clause (`2 ≤ tmp_len`)
    have htl_ge2 : 2 ≤ s.core.tmp_len := by
      have hne : s.core.tmp_len ≠ 1 := by
        intro h1; have heq : BitVec.ofNat 64 s.core.tmp_len = 1#64 := by rw [h1]
        contradiction
      omega
    have hmi_eq : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat = s.core.tmp_len - 1 := by
      rw [m5_la_bv64_sub1_toNat (x := BitVec.ofNat 64 s.core.tmp_len)
        (by rw [bv64_ofNat_toNat (by omega)]; omega), bv64_ofNat_toNat (by omega)]
    have hmi_tmp : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat < s.core.tmp.length := by
      rw [hmi_eq]; omega
    c0_clean; c0_steps
    let wm := s.core.tmp[s.core.tmp_len - 1]'(by omega)
    have hwm_eq : s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp = wm :=
      m5_la_getElem_congr_idx hmi_eq
    have hmi_post := htmp_lvls (s.core.tmp_len - 1) (by omega) (by omega)
    have hwm_get : s.core.tmp[s.core.tmp_len - 1]?.getD 0#32 = wm := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hwm_vals := htmp_vals (s.core.tmp_len - 1) (by omega)
    rw [hwm_get] at hmi_post hwm_vals
    have hwm_lt : wm.toNat < 2 * s.core.cur_vars := hwm_vals.1
    have hwm_v_lt : wm.toNat / 2 < s.core.lvl.length := by rw [hcl.lvl_len]; omega
    have hmi_lvl : ((s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp >>>
        1#32).setWidth 64).toNat < s.core.lvl.length := by
      rw [bv32_setWidth64_toNat, m5_la_bv32_lshr_1, hwm_eq]; exact hwm_v_lt
    refine wp_load_of (FullArenaTactics.c0_load_full_lvl (c := c) (s := s) (R := R) hmi_lvl hm) ?_
    let max_lvl := (s.core.lvl[wm.toNat / 2]?.getD 0#32).toNat
    have hml_pos : 0 < max_lvl := hmi_post.1
    have hml_lt : max_lvl < s.core.cur_level := hmi_post.2.1
    have hml_get : (s.core.lvl[((s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len -
        1#64).toNat]'hmi_tmp >>> 1#32).setWidth 64).toNat]'hmi_lvl).toNat = max_lvl := by
      have hidx : ((s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp >>>
          1#32).setWidth 64).toNat = wm.toNat / 2 := by
        rw [bv32_setWidth64_toNat, m5_la_bv32_lshr_1, hwm_eq]
      dsimp only [max_lvl]; rw [List.getElem?_eq_getElem hwm_v_lt, Option.getD_some]
      exact congrArg BitVec.toNat (m5_la_getElem_congr_idx hidx)
    c0_to_group
    refine wp_join_group (ts := [i64]) (fun (ml_v, ()) m_ml =>
        m_ml = m ∧ ml_v = BitVec.ofNat 64 max_lvl) ?_ ?_
    · rintro _ ⟨ml_v, ⟨⟩⟩ m_ml ⟨rfl, rfl⟩
      have h1_tmp : 1 < s.core.tmp.length := by omega
      c0_clean; c0_let_simp
      refine wp_load_of (load_full_tmp1 (c := c) (s := s) (R := R) h1_tmp hm) ?_
      c0_clean; c0_let_simp
      refine wp_load_of (FullArenaTactics.c0_load_full_tmp (c := c) (s := s) (R := R) hmi_tmp hm) ?_
      let w1 := s.core.tmp[1]'h1_tmp
      have hwm_bv_eq : s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp = wm :=
        hwm_eq
      refine wp_store_sep (store_full_tmp1 (c := c) (s := s) (R := R)
          (s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp) h1_tmp hm)
        fun m1 hm1 => ?_
      c0_clean; c0_let_simp
      let s_t1 : FullState := { s with core := { s.core with tmp := s.core.tmp.set 1 wm } }
      have hmi_t1 : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat < s_t1.core.tmp.length := by
        dsimp only [s_t1]; rw [List.length_set]; exact hmi_tmp
      have hm1' : (FullMem c s_t1 ⋆ R) m1 := by simpa only [s_t1, hwm_bv_eq] using hm1
      refine wp_store_sep
        (FullArenaTactics.c0_store_full_tmp (c := c) (s := s_t1) (R := R) w1 hmi_t1 hm1')
        fun m_sw hm_sw => ?_
      let tmp_sw := (s.core.tmp.set 1 wm).set (s.core.tmp_len - 1) w1
      let s_sw : FullState := { s with core := { s.core with tmp := tmp_sw } }
      have htmpsw_eq : (s.core.tmp.set 1 wm).set
          (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat w1 = tmp_sw := by
        rw [hmi_eq]
      have hm_sw' : (FullMem c s_sw ⋆ R) m_sw := by
        simpa only [s_sw, s_t1, show (1 : BitVec 64) = 1#64 from rfl, htmpsw_eq] using hm_sw
      have hsw_len : s_sw.LengthsOk c :=
        ⟨{ hcl with tmp_len_arr := by simp [s_sw, tmp_sw, htmp_len_arr] }, hs.1.scratch_ok⟩
      have hsw_inv : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s_sw :=
        ⟨hsw_len, FullLearnAnaHelpers.FullOtfsWitnessInv.with_tmp hw tmp_sw, hs.2.2.1,
          hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
      have hsw_inv_c : FullOtfsInvW c F0 F_cur s_sw := m5_laOtfsInv_to_canon hsw_inv
      obtain ⟨hsw_iff, hsw_mem, hsw_nd, hsw_0, hsw_1⟩ :=
        swap_tmp_props_full (tl := s.core.tmp_len) (max_idx := s.core.tmp_len - 1)
          htl_ge2 (by omega) (by omega) (by omega) huip_0 htmp_nd
      have hent_sw : (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((tmp_sw.take s.core.tmp_len).map BitVec.toNat)) :=
        entails_of_mem_or_false hent fun l hl => Or.inl ((hsw_iff l).mpr hl)
      have hsw_lits_lt : ∀ l ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
          l < 2 * s.core.cur_vars := fun l hl => by
        rcases hsw_mem l hl with rfl | ⟨j, hj1, hj2, hjeq⟩
        · exact huip_lt
        · rw [← hjeq]; exact (htmp_vals j hj2).1
      have htmp_sw_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars := by
        intro k hk
        have hlen_sw : k < tmp_sw.length := by simp [tmp_sw, htmp_len_arr]; omega
        have hmem : (tmp_sw[k]?.getD 0#32).toNat ∈
            (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
          rw [List.mem_map]
          refine ⟨tmp_sw[k]'hlen_sw, List.mem_iff_getElem.mpr ⟨k, by
            rw [List.length_take]; omega, by rw [List.getElem_take]⟩, ?_⟩
          rw [List.getElem?_eq_getElem hlen_sw, Option.getD_some]
        have := hsw_lits_lt _ hmem; omega
      c0_to_group; c0_call hDnl
      have hml_bv64 : (BitVec.ofNat 64 max_lvl).toNat = max_lvl := bv64_ofNat_toNat (by omega)
      refine ⟨c, s_sw, R, rfl, hsw_len, by dsimp [s_sw]; omega, hm_sw', fun nlvl _ hnlvl_pos => ?_⟩
      obtain ⟨hnlvl_ge, hnlvl_lt⟩ :=
        hnlvl_pos hcur_pos (by dsimp [s_sw]; rw [hml_bv64]; exact hml_lt)
      dsimp only [s_sw] at hnlvl_ge hnlvl_lt
      rw [hml_bv64] at hnlvl_ge
      c0_to_group; c0_call hBt
      refine ⟨c, s_sw, R, rfl, hsw_len, by dsimp [s_sw]; omega,
        fun _ => by have := hcl.cur_vars_le; omega, hsw_inv.2.1.trail_lits_lt, hm_sw', ?_⟩
      intro vals_bt lvl_bt rsns_bt trl_bt tp_bt te_bt prop_bt cl_bt unass_bt sc_bt m_bt s_bt
        hbt_len hbt_te_le hbt_prop_le hbt_cl hbt_pres hbt_ss _ hbt_keep _ hbt_otfs hm_bt
      have hcl_bt : cl_bt = nlvl.toNat := by dsimp [s_sw] at hbt_cl; omega
      have hbt_w : FullWitnessInv c F0 F_cur s_bt.core := hbt_otfs F0 F_cur hsw_inv_c.2.1 hnlvl_lt
      have hbt_sparse := fullBacktrack_preserves_fullSparseW hsw_inv hbt_len hbt_w rfl rfl rfl rfl
        rfl hbt_pres.1
      have ⟨hkeep_v, hkeep_l⟩ := hbt_keep ⟨F0, F_cur, Or.inr hsw_inv_c.2.1⟩
      have hlow_on_bt : ∀ j, 1 ≤ j → j < s.core.tmp_len →
          ∃ idx < te_bt, (trl_bt[idx]?.getD 0#32).toNat = (s.core.tmp[j]?.getD 0#32).toNat ^^^ 1 ∧
            (lvl_bt[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
        intro j hj1 hj2
        have hjv := htmp_vals j hj2; have hjl := htmp_lvls j hj1 hj2
        have hle_ml : (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            max_lvl := by simpa only [max_lvl, hwm_get] using hjl.2.2
        have hle_nl : (s_sw.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            nlvl.toNat := by dsimp only [s_sw]; omega
        have hv_bt : vals_bt[(s.core.tmp[j]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hkeep_v _ hjv.1, ite_eq_left hle_nl]; exact hjv.2
        have hl_bt : (lvl_bt[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
          obtain ⟨i0, hi0, hi0_eq⟩ := (hsw_inv.2.1.vals_false_iff _ hjv.1).mp hjv.2
          have hdiv : (s_sw.core.trl[i0]?.getD 0#32).toNat / 2 =
              (s.core.tmp[j]?.getD 0#32).toNat / 2 := by rw [hi0_eq, fullInv_var_xor1]
          have hl_eq := hkeep_l i0 hi0
          rw [hdiv] at hl_eq; rw [hl_eq, ite_eq_left hle_nl]; exact hle_ml
        obtain ⟨idx, hidx, heq⟩ := (hbt_w.vals_false_iff _ hjv.1).mp hv_bt
        exact ⟨idx, hidx, heq, hl_bt⟩
      have hwm_on_bt : ∃ idx < te_bt,
          (trl_bt[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
          (lvl_bt[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
        simpa only [hwm_get] using hlow_on_bt (s.core.tmp_len - 1) (by omega) (by omega)
      clear hDnl hBt htmp_vals htmp_lvls hent hm_sw hm_sw' hm1 hm1' hbt_ss hbt_keep hbt_otfs
        hbt_te_le hbt_prop_le
      c0_to_group
      refine wp_join_group (ts := []) (fun () m_gc =>
          ∃ s_gc : FullState,
            FullSparseInvW c F0 F_cur s_gc ∧ s_gc.core.cur_level = nlvl.toNat ∧
            s_gc.core.cur_vars = s.core.cur_vars ∧ s_gc.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            s_gc.core.tmp = tmp_sw ∧ s_gc.core.tmp_len = s.core.tmp_len ∧
            s_gc.core.vals = vals_bt ∧ s_gc.core.lvl = lvl_bt ∧ s_gc.core.trl = trl_bt ∧
            s_gc.core.trail_end = te_bt ∧ s_gc.scratch.work_stk2 = s.scratch.work_stk2 ∧
            (FullMem c s_gc ⋆ R) m_gc) ?_ ?_
      · rintro _ ⟨⟩ m_gc ⟨s_gc, hgc_sp, hgc_cl, hgc_cv, hgc_fu, hgc_tmp, hgc_tl, hgc_vals,
          hgc_lvl, hgc_trl, hgc_te, hgc_ws2, hm_gc⟩
        clear hDefrag hRed hbt_sparse hbt_w hbt_len hm_bt
        have hgc_len := hgc_sp.1
        have hgc_cl_lt : s_gc.core.cur_level < s.core.cur_level := by omega
        have htl_tr32 : ((BitVec.ofNat 64 s.core.tmp_len).setWidth 32).toNat = s.core.tmp_len := by
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : s.core.tmp_len < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
        c0_to_group; c0_call hAddCl
        refine ⟨c, F0, F_cur, s_gc, R, rfl, hgc_len, hgc_sp.2.1, hgc_sp.2.2.2.2.2,
          by rw [hgc_tl, htl_tr32]; omega, fun _ => ?_, hm_gc, ?_⟩
        · rw [hgc_tmp, hgc_tl, htl_tr32, hgc_cv]
          exact ⟨hsw_lits_lt, hsw_nd, hent_sw⟩
        · rw [hgc_tl, htl_tr32]
          simp only [show ¬ s.core.tmp_len < 2 by omega, ↓reduceIte]
          by_cases htl2 : s.core.tmp_len = 2
          · simp only [htl2, ↓reduceIte]
            intro r_ac wvec_a wstk_a wlen_a wu_a nb_a wsort_a m_ac hr_ac hac_len hac_w hm_ac
            let s_ac : FullState :=
              { s_gc with
                core := { s_gc.core with
                  wvec := wvec_a, wstk := wstk_a, wlen := wlen_a, wusable := wu_a,
                  num_binary := nb_a }
                scratch := { s_gc.scratch with wsort := wsort_a } }
            have hac_sp : FullSparseInvW c F0 F_cur s_ac :=
              ⟨hac_len, hac_w, hgc_sp.2.2.1, hgc_sp.2.2.2.1,
                Full.FullExtScratchOk.of_pres hgc_sp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
                hgc_sp.2.2.2.2.2⟩
            have hlow_ac : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
                q = uip.toNat ∨ ∃ idx < s_ac.core.trail_end,
                  (s_ac.core.trl[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
                  (s_ac.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl := by
              intro q hq
              rcases hsw_mem q hq with rfl | ⟨j, hj1, hj2, hjeq⟩
              · exact Or.inl rfl
              · right; rw [← hjeq]; dsimp only [s_ac]; rw [hgc_te, hgc_trl, hgc_lvl]
                exact hlow_on_bt j hj1 hj2
            have hwm_ac : ∃ idx < s_ac.core.trail_end,
                (s_ac.core.trl[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
                (s_ac.core.lvl[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
              dsimp only [s_ac]; rw [hgc_te, hgc_trl, hgc_lvl]; exact hwm_on_bt
            refine m5_learn_clause_post_ac_wp (new_ref64 := r_ac) hAsgn hEsub hQ hac_sp
              (by simpa [s_ac] using hgc_cl_lt) hml_pos (by dsimp [s_ac]; omega) (by omega)
              hgc_cv hgc_fu hgc_ws2 hgc_tmp hgc_tl hsw_1 htl_ge2 htl_cv huip_lt hwm_lt htmp_sw_lt
              hwm_ac hlow_ac ?_ hm_ac
            rcases hr_ac with rfl | rfl
            · exact Or.inl rfl
            · right; refine ⟨by decide, ?_⟩; simp only [↓reduceIte]
              have hlen2_sw : 2 ≤ tmp_sw.length := by
                simp only [tmp_sw, List.length_set, htmp_len_arr]; omega
              rw [htl2, m5_tmp_take2_eq hlen2_sw hsw_0 hsw_1] at hent_sw
              exact hent_sw
          · simp only [htl2, ↓reduceIte]
            intro r_ac arena_a alen_a wvec_a wstk_a wlen_a wu_a fred_a ni_a nr_a wsort_a m_ac
              hr_ac hac_len hac_w hrefs_sub hnd_imp hok_a hm_ac
            let s_ac : FullState :=
              { s_gc with
                core := { s_gc.core with
                  arena := arena_a, arena_len := alen_a, wvec := wvec_a, wstk := wstk_a,
                  wlen := wlen_a, wusable := wu_a, first_reducible := fred_a, num_irred := ni_a,
                  num_redundant := nr_a }
                scratch := { s_gc.scratch with wsort := wsort_a } }
            have hac_sp : FullSparseInvW c F0 F_cur s_ac :=
              ⟨hac_len, hac_w, hgc_sp.2.2.1, hnd_imp hgc_sp.2.2.2.1,
                Full.FullExtScratchOk.of_pres hgc_sp.2.2.2.2.1 ⟨rfl, rfl⟩ hrefs_sub,
                hgc_sp.2.2.2.2.2⟩
            have hlow_ac : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
                q = uip.toNat ∨ ∃ idx < s_ac.core.trail_end,
                  (s_ac.core.trl[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
                  (s_ac.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl := by
              intro q hq
              rcases hsw_mem q hq with rfl | ⟨j, hj1, hj2, hjeq⟩
              · exact Or.inl rfl
              · right; rw [← hjeq]; dsimp only [s_ac]; rw [hgc_te, hgc_trl, hgc_lvl]
                exact hlow_on_bt j hj1 hj2
            have hwm_ac : ∃ idx < s_ac.core.trail_end,
                (s_ac.core.trl[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
                (s_ac.core.lvl[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
              dsimp only [s_ac]; rw [hgc_te, hgc_trl, hgc_lvl]; exact hwm_on_bt
            refine m5_learn_clause_post_ac_wp (new_ref64 := r_ac) hAsgn hEsub hQ hac_sp
              (by simpa [s_ac] using hgc_cl_lt) hml_pos (by dsimp [s_ac]; omega) (by omega)
              hgc_cv hgc_fu hgc_ws2 hgc_tmp hgc_tl hsw_1 htl_ge2 htl_cv huip_lt hwm_lt htmp_sw_lt
              hwm_ac hlow_ac ?_ hm_ac
            rcases hr_ac with rfl | rfl
            · exact Or.inl rfl
            · obtain ⟨_, href_a, hng_a, hlits_a⟩ := hok_a rfl
              have hal_lt31 : s_gc.core.arena_len < 2 ^ 31 - 1 := by
                have := hgc_len.core_ok.arena_len_le; omega
              have hnr_toNat : (BitVec.ofNat 64 s_gc.core.arena_len).toNat = s_gc.core.arena_len :=
                bv64_ofNat_toNat (by omega)
              have hne_ff : BitVec.ofNat 64 s_gc.core.arena_len ≠ 0xFFFFFFFF#64 := fun heq => by
                have := congrArg BitVec.toNat heq; rw [hnr_toNat] at this
                have : (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1 := rfl; omega
              have hne_fe : BitVec.ofNat 64 s_gc.core.arena_len ≠ 0xFFFFFFFE#64 := fun heq => by
                have := congrArg BitVec.toNat heq; rw [hnr_toNat] at this
                have : (0xFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 32 - 2 := rfl; omega
              right; refine ⟨hne_ff, ?_⟩; simp only [hne_fe, ↓reduceIte, hnr_toNat]
              have hlits_eq : fullArenaClauseLits s_ac s_gc.core.arena_len =
                  (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
                change fullArenaClauseLits s_ac s_gc.core.arena_len =
                  (s_gc.core.tmp.take s.core.tmp_len).map BitVec.toNat at hlits_a
                rwa [hgc_tmp] at hlits_a
              refine ⟨hal_lt31, href_a, hng_a, fun q hq => by rwa [hlits_eq] at hq, ?_⟩
              rw [hlits_eq, List.mem_map]
              have h0_sw : 0 < tmp_sw.length := by simp [tmp_sw, htmp_len_arr]; omega
              have hu_sw : tmp_sw[0]'h0_sw = uip := by
                have := List.getElem?_eq_getElem h0_sw; rw [hsw_0] at this
                exact (Option.some.inj this).symm
              exact ⟨uip, List.mem_iff_getElem.mpr ⟨0, by rw [List.length_take]; omega,
                by rw [List.getElem_take]; exact hu_sw⟩, rfl⟩
      · -- GC `if` body
        clear hAddCl hAsgn hEsub hent_sw hsw_lits_lt hlow_on_bt hwm_on_bt htmp_sw_lt
        intro Jgc hJgc
        c0_to_group
        refine wp_join_group (ts := []) (fun () m_in => m_in = m_bt) ?_ ?_
        · rintro _ ⟨⟩ m_in rfl
          c0_to_group
          refine wp_join_group (ts := []) (fun () m_d => ∃ wvec_d wstk_d wlen_d wsort_d,
              let s_d : FullState :=
                { s_bt with
                  core := { s_bt.core with
                    wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                  scratch := { sc_bt with wsort := wsort_d } }
              FullSparseInvW c F0 F_cur s_d ∧ (FullMem c s_d ⋆ R) m_d) ?_ ?_
          · rintro _ ⟨⟩ m_d ⟨wvec_d, wstk_d, wlen_d, wsort_d, hd_sp, hm_d⟩
            let s_d : FullState :=
              { s_bt with
                core := { s_bt.core with
                  wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                scratch := { sc_bt with wsort := wsort_d } }
            have hd_cl : s_d.core.cur_level = nlvl.toNat := hcl_bt
            c0_to_group
            refine wp_join_group (ts := []) (fun () m_3 =>
                ∃ s_3 : FullState,
                  FullSparseInvW c F0 F_cur s_3 ∧ s_3.core.cur_level = nlvl.toNat ∧
                  s_3.core.cur_vars = s.core.cur_vars ∧ s_3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  s_3.core.tmp = tmp_sw ∧ s_3.core.tmp_len = s.core.tmp_len ∧
                  s_3.core.vals = vals_bt ∧ s_3.core.lvl = lvl_bt ∧ s_3.core.trl = trl_bt ∧
                  s_3.core.trail_end = te_bt ∧ s_3.scratch.work_stk2 = s.scratch.work_stk2 ∧
                  (FullMem c s_3 ⋆ R) m_3) ?_ ?_
            · rintro _ ⟨⟩ m_3 ⟨s_3, h3_sp, h3_cl, h3_cv, h3_fu, h3_tmp, h3_tl, h3_vals, h3_lvl,
                h3_trl, h3_te, h3_ws2, hm_3⟩
              c0_steps
              exact hJgc () m_3 ⟨s_3, h3_sp, h3_cl, h3_cv, h3_fu, h3_tmp, h3_tl, h3_vals, h3_lvl,
                h3_trl, h3_te, h3_ws2, hm_3⟩
            · intro J3 hJ3; c0_split
              · c0_to_group; c0_call hRed
                refine ⟨c, F0, F_cur, s_d, R, rfl, hd_sp, hm_d, ?_⟩
                intro rr s_r m_r hr_sp hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                  hr_20 hr_1 hr_pos hm_r
                dsimp only [s_d, s_bt, s_sw] at hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                dsimp only [s_d] at hr_pos
                have hr_ws2' : s_r.scratch.work_stk2 = s.scratch.work_stk2 :=
                  hr_ws2.trans hbt_pres.2.2.1
                c0_split
                · c0_steps
                  exact hQ 20#64 s_r m_r hr_sp.1 (Or.inr (Or.inr rfl)) hr_cv hr_fu hr_ws2'
                    (fun _ => ⟨hr_20 (by assumption), hr_sp, by omega⟩) (fun h => by cases h)
                    (fun h => by cases h) hm_r
                · c0_split
                  · c0_steps
                    exact hQ 0#64 s_r m_r hr_sp.1 (Or.inl rfl) hr_cv hr_fu hr_ws2'
                      (fun h => by cases h) (fun _ => hr_sp) (fun h => by cases h) hm_r
                  · have hrr1 : rr = 1#64 := by
                      rcases hr_dom with rfl | rfl | rfl <;> first | rfl | contradiction
                    c0_split
                    · c0_steps
                      exact hQ 1#64 s_r m_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv hr_fu hr_ws2'
                        (fun h => by cases h) (fun h => by cases h)
                        (fun _ => ⟨hr_sp, by omega⟩) hm_r
                    · have hcl_eq : s_r.core.cur_level = nlvl.toNat := by
                        have hbv : BitVec.ofNat 64 s_r.core.cur_level = nlvl := by assumption
                        have hsr_lt64 : s_r.core.cur_level < 2 ^ 64 := by
                          have := hr_sp.1.core_ok.cur_vars_le
                          have := hr_sp.2.1.cur_level_le
                          have := hr_sp.1.core_ok.trail_end_le; omega
                        have := congrArg BitVec.toNat hbv
                        rw [bv64_ofNat_toNat hsr_lt64] at this; exact this
                      have huip_r_lt : (BitVec.setWidth 64 (s.core.tmp[0]'huip_in)).toNat <
                          s_r.core.vals.length := by
                        rw [bv32_setWidth64_toNat, hr_sp.1.core_ok.vals_len]
                        change uip.toNat < 2 * c.max_vars; omega
                      c0_split
                      · c0_steps
                        exact hQ 1#64 s_r m_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv hr_fu hr_ws2'
                          (fun h => by cases h) (fun h => by cases h)
                          (fun _ => ⟨hr_sp, by omega⟩) hm_r
                      · obtain ⟨_, hr_vals, hr_lvl, hr_trl, _, hr_te⟩ :=
                          hr_pos hrr1 (by omega)
                        c0_steps
                        exact hJ3 () m_r ⟨s_r, hr_sp, hcl_eq, hr_cv, hr_fu, hr_tmp, hr_tl,
                          hr_vals, hr_lvl, hr_trl, hr_te, hr_ws2', hm_r⟩
              · c0_steps
                exact hJ3 () m_d ⟨s_d, hd_sp, hd_cl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl,
                  rfl, hbt_pres.2.2.1, hm_d⟩
          · intro Jdef hJdef; c0_split
            · have hbt_lay : WatchStackLayout s_bt.core := by
                have hm_w := hbt_sparse.2.1.watches
                unfold ModeWatchesInv at hm_w
                rw [ite_eq_left hbt_sparse.2.2.2.2.2] at hm_w
                exact hm_w.layout
              c0_call hDefrag
              refine ⟨c, s_bt, R, rfl, hbt_len, hbt_lay, hm_bt, ?_⟩
              intro wvec_d wstk_d wlen_d wsort_d m_d _ hd_len hd_lay _ hd_pres hm_d
              let s_d : FullState :=
                { s_bt with
                  core := { s_bt.core with
                    wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                  scratch := { sc_bt with wsort := wsort_d } }
              have hd_sp := fullWstackDefrag_preserves_fullSparseW hbt_sparse hd_len hd_lay hd_pres
              c0_steps
              exact hJdef () m_d ⟨wvec_d, wstk_d, wlen_d, wsort_d, hd_sp, hm_d⟩
            · have hwuz : s.core.wusable = 0#64 := by
                dsimp only [s_bt, s_sw] at *; apply BitVec.eq_of_toNat_eq; bv_omega
              c0_steps
              refine hJdef () m_in ⟨s_bt.core.wvec, s_bt.core.wstk, s_bt.core.wlen, sc_bt.wsort, ?_,
                ?_⟩
              · simpa only [s_bt, s_sw, hwuz] using m5_laSparse_to_canon hbt_sparse
              · simpa only [s_bt, s_sw, hwuz] using hm_bt
        · intro J_in hJ_in; c0_split
          · c0_steps; exact hJ_in () m_bt rfl
          · c0_split
            · c0_steps; exact hJ_in () m_bt rfl
            · c0_steps
              exact hJgc () m_bt ⟨s_bt, hbt_sparse, hcl_bt, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl,
                rfl, rfl, hbt_pres.2.2.1, hm_bt⟩
    · intro Jml hJml; c0_split
      c0_steps
      have hml_set : BitVec.setWidth 64
          (s.core.lvl[((s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp >>>
            1#32).setWidth 64).toNat]'hmi_lvl) = BitVec.ofNat 64 max_lvl := by
        apply BitVec.eq_of_toNat_eq
        rw [bv32_setWidth64_toNat, hml_get, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hml_set]
      exact hJml (BitVec.ofNat 64 max_lvl, ()) m ⟨rfl, rfl⟩

/-! ## 2. `full_analyze_m5` (`Full.fullAnalyzeSpec`) -/

/-- `full_analyze_m5` (probing-isolated OTFS bump, post-`full_min_shrink` bump + `tick_rel`, and
`ema_update`) satisfies canonical `Full.fullAnalyzeSpec` parametrically in `Γ`. -/
theorem full_analyze_m5_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
      Γ "full_deduce_1uip" [i64] [i64] a m Q X)
    (hRestoreBump : ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m5" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, fullMinShrinkSpec a m Q X →
      Γ "full_min_shrink" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, fullTickRelSpec a m Q X →
      Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ args m Q X, fullAnalyzeSpec args m Q X →
      Func.wp Γ full_analyze_m5_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hs, hconfl, hm, hQ⟩
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hacap := c.harena; unfold dimacsBound at hacap
  have hcl := hs.1.core_ok
  have hcv_le := hcl.cur_vars_le
  have hcur_le := hs.2.1.cur_level_le
  have hte_le := hcl.trail_end_le
  unfold Func.wp full_analyze_m5_body
  dsimp only
  c0_split
  · -- Level 0 conflict (`cur_level == 0`) -> UNSAT (`20`)
    have hcl0 : s.core.cur_level = 0 := by bv_omega
    c0_steps
    exact hQ 20#64 s m hs.1 (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _)
      ⟨rfl, fun _ => ⟨m5_sparse_to_canonOtfs hs, Nat.le_refl _, rfl⟩⟩
      (fun _ => level0_unsat_of_conflict_okW hs.2.1 hcl0 hconfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · have hcur_pos : 0 < s.core.cur_level := by bv_omega
    have hlim_nat : (BitVec.ofNat 64 s.core.cur_vars + 64#64).toNat = s.core.cur_vars + 64 := by
      bv_omega
    c0_to_group
    refine wp_loop_group (ts := [i64])
      (fun rem (iter_v, ()) m_i =>
        ∃ iter cut s_i,
          iter ≤ s.core.cur_vars + 64 ∧ rem = s.core.cur_vars + 64 - iter ∧
          iter_v = BitVec.ofNat 64 iter ∧ cut ≤ s_i.core.trail_end ∧
          FullCutInvW c F0 F_cur cut s_i ∧ 0 < s_i.core.cur_level ∧
          s_i.core.cur_level ≤ s.core.cur_level ∧ FullConflictOkCut F_cur cut s_i ∧
          s_i.core.cur_vars = s.core.cur_vars ∧ s_i.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          s_i.scratch.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c s_i ⋆ R) m_i) ?_ ?_
    · rintro L rem ⟨iter_v, ⟨⟩⟩ m_i ih
        ⟨iter, cut, s_i, hiter_le, rfl, rfl, hcut_le, hcut_inv, hcl_pos_i, hcl_le_i, hconfl_i,
          hcv_i, hfu_i, hws2_i, hm_i⟩
      c0_split
      · have hiter_lt : iter < s.core.cur_vars + 64 := by
          have hlt : iter % 2 ^ 64 < (s.core.cur_vars + (64#64 : BitVec 64).toNat) % 2 ^ 64 := by
            assumption
          rw [Nat.mod_eq_of_lt (by omega : iter < 2 ^ 64),
            show (64#64 : BitVec 64).toNat = 64 from rfl,
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars + 64 < 2 ^ 64)] at hlt
          exact hlt
        have hiter1_eq : (BitVec.ofNat 64 iter + 1#64).toNat = iter + 1 := by
          rw [m5_la_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
            bv64_ofNat_toNat (by omega)]
        have hiter1_bv : BitVec.ofNat 64 iter + 1#64 = BitVec.ofNat 64 (iter + 1) :=
          BitVec.eq_of_toNat_eq (by rw [hiter1_eq, bv64_ofNat_toNat (by omega)])
        c0_to_group; c0_call hOneLit
        refine ⟨c, F0, F_cur, cut, s_i, R, rfl, hcut_inv, hconfl_i, hm_i, ?_⟩
        intro ol s1 m1 h1_len hol_dom h1_cv h1_fu h1_ws2 h1_20 h1_1 h1_2 h1_0 hm1
        have h1_cv' : s1.core.cur_vars = s.core.cur_vars := h1_cv.trans hcv_i
        have h1_fu' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [h1_fu]; exact hfu_i
        have h1_ws2' : s1.scratch.work_stk2 = s.scratch.work_stk2 := h1_ws2.trans hws2_i
        c0_split
        · c0_steps
          obtain ⟨hu1, ho1, hcl1, hdm1⟩ := h1_20 (by assumption)
          exact hQ 20#64 s1 m1 h1_len (Or.inr (Or.inr rfl)) h1_cv' h1_fu'
            ⟨h1_ws2', fun _ => ⟨ho1, Nat.le_trans hcl1 hcl_le_i,
              hdm1.trans (hcut_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
            (fun _ => hu1) (fun h => by cases h) (fun h => by cases h) hm1
        · c0_split
          · obtain ⟨h1_sp, h1_cl_lt⟩ := h1_1 (by assumption)
            c0_steps
            exact hQ 1#64 s1 m1 h1_len (Or.inr (Or.inl rfl)) h1_cv' h1_fu'
              ⟨h1_ws2', fun h => by cases h⟩ (fun h => by cases h) (fun h => by cases h)
              (fun _ => ⟨h1_sp, by omega⟩) hm1
          · c0_split
            · c0_steps
              exact hQ 0#64 s1 m1 h1_len (Or.inl rfl) h1_cv' h1_fu'
                ⟨h1_ws2', fun h => by cases h⟩ (fun h => by cases h)
                (fun _ => h1_2 (by assumption)) (fun h => by cases h) hm1
            · have hol_0 : ol = 0#64 := by
                rcases hol_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
              obtain ⟨cut1, hcut1_le, hcut1_inv, hcl1_pos, hcl1_le, hconfl1⟩ := h1_0 hol_0
              have hcl1_le' : s1.core.cur_level ≤ s.core.cur_level := Nat.le_trans hcl1_le hcl_le_i
              c0_to_group; c0_call hDeduce
              refine ⟨c, F0, F_cur, cut1, s1, R, rfl, hcut1_inv, hcl1_pos, hconfl1, hm1, ?_⟩
              intro dst s2 m2 h2_len hdst_dom h2_cv h2_fu h2_ws2 h2_20 h2_0 h2_1 h2_2 hm2
              have h2_cv' : s2.core.cur_vars = s.core.cur_vars := h2_cv.trans h1_cv'
              have h2_fu' : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [h2_fu]; exact h1_fu'
              have h2_ws2' : s2.scratch.work_stk2 = s.scratch.work_stk2 := h2_ws2.trans h1_ws2'
              c0_split
              · c0_steps
                obtain ⟨hu2, ho2, hcl2, hdm2⟩ := h2_20 (by assumption)
                exact hQ 20#64 s2 m2 h2_len (Or.inr (Or.inr rfl)) h2_cv' h2_fu'
                  ⟨h2_ws2', fun _ => ⟨ho2, Nat.le_trans hcl2 hcl1_le',
                    hdm2.trans (hcut1_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
                  (fun _ => hu2) (fun h => by cases h) (fun h => by cases h) hm2
              · c0_split
                · c0_steps
                  exact hQ 0#64 s2 m2 h2_len (Or.inl rfl) h2_cv' h2_fu'
                    ⟨h2_ws2', fun h => by cases h⟩ (fun h => by cases h)
                    (fun _ => h2_0 (by assumption)) (fun h => by cases h) hm2
                · c0_split
                  · -- `dst == 2`: increment `conflicts`, probing-guarded OTFS `tmp[0]` + bump
                    obtain ⟨cut2, hcut2_le, hcut2_inv, hcl2_eq, hconfl2⟩ := h2_2 (by assumption)
                    c0_to_group
                    let s2c : FullState :=
                      { s2 with
                        scratch := { s2.scratch with conflicts := s2.scratch.conflicts + 1#64 } }
                    have h2c_inv :=
                      m5_fullCutInvW_with_conflicts hcut2_inv (s2.scratch.conflicts + 1#64)
                    have hm2c : (FullMem c s2c ⋆ R) m := hm
                    -- Outer join `Jprob2` after `if (h->probing == 0ULL)`
                    refine wp_join_group (ts := []) (fun () m_p2 =>
                        ∃ s_p2 : FullState,
                          cut2 ≤ s_p2.core.trail_end ∧ FullCutInvW c F0 F_cur cut2 s_p2 ∧
                          0 < s_p2.core.cur_level ∧ s_p2.core.cur_level ≤ s.core.cur_level ∧
                          FullConflictOkCut F_cur cut2 s_p2 ∧
                          s_p2.core.cur_vars = s.core.cur_vars ∧
                          s_p2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          s_p2.scratch.work_stk2 = s.scratch.work_stk2 ∧
                          (FullMem c s_p2 ⋆ R) m_p2) ?_ ?_
                    · rintro _ ⟨⟩ m_p2 ⟨s_p2, hcut_p2, hinv_p2, hcl_pos_p2, hcl_le_p2, hconfl_p2,
                        hcv_p2, hfu_p2, hws2_p2, hm_p2⟩
                      c0_steps
                      rw [show (1 : BitVec 64) = 1#64 from rfl, hiter1_bv]
                      exact ih (s.core.cur_vars + 64 - (iter + 1)) (BitVec.ofNat 64 (iter + 1), ())
                        m_p2 (by omega)
                        ⟨iter + 1, cut2, s_p2, by omega, rfl, rfl, hcut_p2, hinv_p2, hcl_pos_p2,
                          hcl_le_p2, hconfl_p2, hcv_p2, hfu_p2, hws2_p2, hm_p2⟩
                    · intro Jp2 hJp2; c0_split
                      · -- `probing == 0`: optional `tmp[0]` write + `full_restore_bump_ana_m5`
                        c0_to_group
                        refine wp_join_group (ts := []) (fun () m_t =>
                            ∃ tmp' tl',
                              let s_t : FullState :=
                                { s2c with core := { s2c.core with tmp := tmp', tmp_len := tl' } }
                              FullCutInvW c F0 F_cur cut2 s_t ∧ FullConflictOkCut F_cur cut2 s_t ∧
                              (FullMem c s_t ⋆ R) m_t) ?_ ?_
                        · rintro _ ⟨⟩ m_t ⟨tmp', tl', ht_inv, ht_confl, hm_t⟩
                          let s_t : FullState :=
                            { s2c with core := { s2c.core with tmp := tmp', tmp_len := tl' } }
                          c0_to_group; c0_call hRestoreBump
                          refine ⟨c, s_t, R, rfl, ht_inv.1, ht_inv.2.2.1.1, hm_t, ?_⟩
                          intro mrk' mcl' sc' m_rb _ hrb_len hrb_m0 hrb_pres hrb_ws2 hm_rb
                          let s_rb : FullState :=
                            { s_t with
                              core := { s_t.core with mrk := mrk', min_clr_len := mcl' }
                              scratch := sc' }
                          have hrb_inv :=
                            m5_fullCutInvW_of_restoreBump ht_inv hrb_len hrb_m0 hrb_pres
                          c0_steps
                          exact hJp2 () m_rb ⟨s_rb, hcut2_le, hrb_inv,
                            by dsimp only [s_rb, s_t, s2c]; omega,
                            by dsimp only [s_rb, s_t, s2c]; omega, ht_confl, h2_cv', h2_fu',
                            hrb_ws2.trans h2_ws2', hm_rb⟩
                        · intro Jt hJt; c0_split
                          · -- `cur_vars > 0`
                            have hcv2_pos : 0 < s2.core.cur_vars := by
                              have hlt : (0 : BitVec 64).toNat <
                                  (BitVec.ofNat 64 s2.core.cur_vars).toNat := by assumption
                              have := h2_len.core_ok.cur_vars_le
                              rw [bv64_ofNat_toNat (by omega)] at hlt; simp at hlt; omega
                            have h0_tmp : 0 < s2c.core.tmp.length := by
                              have := h2_len.core_ok.tmp_len_arr
                              have := h2_len.core_ok.cur_vars_le; dsimp only [s2c]; omega
                            have h1_le_mv : 1 ≤ c.max_vars := by
                              have := h2_len.core_ok.cur_vars_le; omega
                            c0_split
                            · -- `confl_type == 1`: `tmp[0] = (u32)confl_lit0; tmp_len = 1;`
                              c0_steps
                              exact hJt () m ⟨s2c.core.tmp.set 0 (s2c.core.confl_lit0.setWidth 32),
                                1, m5_fullCutInvW_with_tmp_tl h2c_inv _ 1
                                  (by simp [h2_len.core_ok.tmp_len_arr, s2c]) h1_le_mv,
                                hconfl2, by simpa only [show (1 : BitVec 64).toNat = 1 from rfl]
                                  using hm⟩
                            · c0_split
                              · c0_split
                                · have hcr_lt_al : s2.core.confl_ref.toNat < s2.core.arena_len := by
                                    have hlt : s2.core.confl_ref.toNat <
                                        (BitVec.ofNat 64 s2.core.arena_len).toNat := by assumption
                                    have := h2_len.core_ok.arena_len_le
                                    rw [bv64_ofNat_toNat (by omega)] at hlt; exact hlt
                                  c0_split
                                  · have h3_lt_diff :
                                        3 < s2.core.arena_len - s2.core.confl_ref.toNat := by
                                      have hlt : 3 < (2 ^ 64 - s2c.core.confl_ref.toNat +
                                          s2c.core.arena_len) % 2 ^ 64 := by assumption
                                      have hle := h2_len.core_ok.arena_len_le
                                      dsimp only [s2c] at hlt
                                      have hsum : 2 ^ 64 - s2.core.confl_ref.toNat +
                                          s2.core.arena_len =
                                          2 ^ 64 + (s2.core.arena_len - s2.core.confl_ref.toNat) :=
                                        by omega
                                      rw [hsum, Nat.add_mod_left,
                                        Nat.mod_eq_of_lt (by omega)] at hlt
                                      exact hlt
                                    have hcr3_nat : (s2c.core.confl_ref + 3#64).toNat =
                                        s2.core.confl_ref.toNat + 3 := by
                                      have hle := h2_len.core_ok.arena_len_le
                                      dsimp only [s2c]
                                      rw [BitVec.toNat_add,
                                        show (3#64 : BitVec 64).toNat = 3 from rfl,
                                        Nat.mod_eq_of_lt (by omega)]
                                    have hcr3_ar : (s2c.core.confl_ref + 3#64).toNat <
                                        s2c.core.arena.length := by
                                      have := h2_len.core_ok.arena_len_le
                                      have := h2_len.core_ok.arena_len_arr
                                      rw [hcr3_nat]; dsimp only [s2c]; omega
                                    c0_steps
                                    refine wp_load_of (FullArenaTactics.load_full_confl_ref hm2c) ?_
                                    c0_steps
                                    let lit0 :=
                                      s2c.core.arena[(s2c.core.confl_ref + 3#64).toNat]'hcr3_ar
                                    exact hJt () m ⟨s2c.core.tmp.set 0 lit0, 1,
                                      m5_fullCutInvW_with_tmp_tl h2c_inv _ 1
                                        (by simp [h2_len.core_ok.tmp_len_arr, s2c]) h1_le_mv,
                                      hconfl2, by simpa only [lit0,
                                        show (1 : BitVec 64).toNat = 1 from rfl,
                                        show (3 : BitVec 64) = 3#64 from rfl] using hm⟩
                                  · c0_steps; exact hJt () m ⟨s2c.core.tmp, s2c.core.tmp_len,
                                      h2c_inv, hconfl2, hm2c⟩
                                · c0_steps; exact hJt () m ⟨s2c.core.tmp, s2c.core.tmp_len,
                                    h2c_inv, hconfl2, hm2c⟩
                              · c0_steps; exact hJt () m ⟨s2c.core.tmp, s2c.core.tmp_len,
                                  h2c_inv, hconfl2, hm2c⟩
                          · c0_steps; exact hJt () m ⟨s2c.core.tmp, s2c.core.tmp_len,
                              h2c_inv, hconfl2, hm2c⟩
                      · -- `probing != 0`: skip OTFS bump
                        c0_steps
                        exact hJp2 () m ⟨s2c, hcut2_le, h2c_inv, by dsimp [s2c]; omega,
                          by dsimp [s2c]; omega, hconfl2, h2_cv', h2_fu', h2_ws2', hm2c⟩
                  · -- `dst == 1`: minimize, probing-guarded bump+tick, glue, ema, learn clause
                    have hdst_1 : dst = 1#64 := by
                      rcases hdst_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
                    obtain ⟨h2_otfs, h2_cl, h2_tl1, h2_tl_cv, h2_nd, h2_vals, h2_lvls, h2_lvl0,
                      h2_ent⟩ := h2_1 hdst_1
                    clear ih L hOneLit hDeduce hconfl hconfl_i hcut_inv hcut1_inv hconfl1 h1_20
                      h1_1 h1_2 h1_0 h2_20 h2_0 h2_1 h2_2 hiter_le hiter_lt hiter1_eq hiter1_bv
                      hcut_le hcut1_le hcl_pos_i hcl1_le hol_dom hol_0 hdst_dom hdst_1
                      h1_cv h1_fu h1_ws2 h2_cv h2_fu h2_ws2 hcv_i hfu_i hws2_i hm hm_i hm1
                    c0_to_group; c0_call hMinShrink
                    refine ⟨c, F0, F_cur, s2, R, rfl, h2_len, h2_otfs.2.1, h2_otfs.2.2.1,
                      h2_tl1, h2_tl_cv, h2_nd, h2_ent, h2_vals, h2_lvls, h2_lvl0, hm2, ?_⟩
                    intro tmp_ms tl_ms mrk_ms mstk_ms mclr_ms mcl_ms mcf_ms conf_ms llits_ms
                      mrem_ms sstk_ms m_ms _ hms_len hms_w hms_clr hms_tl1 hms_tl_le hms_0
                      hms_nd hms_post hms_ent hm_ms
                    let s_ms : FullState :=
                      { s2 with
                        core := { s2.core with
                          tmp := tmp_ms, tmp_len := tl_ms, mrk := mrk_ms, min_stk := mstk_ms,
                          min_clr := mclr_ms, min_clr_len := mcl_ms, min_clr_full := mcf_ms }
                        scratch := { s2.scratch with
                          conflicts := conf_ms, learned_lits := llits_ms,
                          min_removed := mrem_ms, shrink_stk := sstk_ms } }
                    have hms_otfs : FullOtfsInvW c F0 F_cur s_ms :=
                      ⟨hms_len, hms_w, hms_clr,
                        m5_fullArenaVarsNodup_congr_core h2_otfs.2.2.2.1 rfl rfl,
                        Full.FullExtScratchOk.of_pres h2_otfs.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
                        h2_otfs.2.2.2.2.2⟩
                    -- Join after `if (h->probing == 0ULL) { restore_bump_ana; tick_rel; }`
                    c0_to_group
                    refine wp_join_group (ts := []) (fun () m_tr =>
                        ∃ s_tr : FullState,
                          FullOtfsInvW c F0 F_cur s_tr ∧
                          s_tr.core.tmp = tmp_ms ∧ s_tr.core.tmp_len = tl_ms ∧
                          s_tr.core.vals = s2.core.vals ∧ s_tr.core.lvl = s2.core.lvl ∧
                          s_tr.core.cur_level = s2.core.cur_level ∧
                          s_tr.core.cur_vars = s2.core.cur_vars ∧
                          s_tr.core.fuel = s2.core.fuel ∧
                          s_tr.scratch.work_stk2 = s.scratch.work_stk2 ∧
                          (FullMem c s_tr ⋆ R) m_tr) ?_ ?_
                    · rintro _ ⟨⟩ m_tr ⟨s_tr, htr_otfs, htr_tmp, htr_tl, htr_vals, htr_lvl,
                        htr_cl, htr_cv, htr_fu, htr_ws2, hm_tr⟩
                      have htr_len := htr_otfs.1
                      c0_to_group
                      refine wp_loop_group (ts := [i64, i32, i64])
                        (fun r_gi (glue_v, last_v, gi_v, ()) m_gi =>
                          ∃ gi, 1 ≤ gi ∧ gi ≤ tl_ms ∧ r_gi = tl_ms - gi ∧
                            gi_v = BitVec.ofNat 64 gi ∧ (FullMem c s_tr ⋆ R) m_gi) ?_ ?_
                      · rintro Lgi _ ⟨glue_v, last_v, gi_v, ⟨⟩⟩ m_gi ih_gi
                          ⟨gi, hgi1, hgile, rfl, rfl, hm_gi⟩
                        have htr_tl_bd : tl_ms < 2 ^ 64 := by
                          have := h2_len.core_ok.cur_vars_le; omega
                        c0_split
                        · have hgi_bv : (BitVec.ofNat 64 gi).toNat = gi :=
                            bv64_ofNat_toNat (by omega)
                          have hgilt : gi < tl_ms := by
                            have hlt : (BitVec.ofNat 64 gi).toNat <
                                (BitVec.ofNat 64 s_tr.core.tmp_len).toNat := by assumption
                            rw [htr_tl, hgi_bv, bv64_ofNat_toNat htr_tl_bd] at hlt; exact hlt
                          have htr_tmp_len : s_tr.core.tmp.length = c.max_vars :=
                            htr_len.core_ok.tmp_len_arr
                          have hgi_idx : (BitVec.ofNat 64 gi).toNat < s_tr.core.tmp.length := by
                            rw [hgi_bv, htr_tmp_len]; have := h2_len.core_ok.cur_vars_le; omega
                          have hgi_post := hms_post gi hgi1 hgilt
                          have htr_tmp_gi_lt : gi < tmp_ms.length := by
                            rw [← htr_tmp, htr_tmp_len]; have := h2_len.core_ok.cur_vars_le; omega
                          have hgi_t_eq : s_tr.core.tmp[(BitVec.ofNat 64 gi).toNat]'hgi_idx =
                              tmp_ms[gi]'htr_tmp_gi_lt :=
                            m5_la_getElem_congr_list htr_tmp hgi_bv
                          have hgi_l_eq : (tmp_ms[gi]'htr_tmp_gi_lt).toNat / 2 =
                              ((tmp_ms[gi]?.getD 0#32).toNat / 2) := by
                            rw [List.getElem?_eq_getElem htr_tmp_gi_lt, Option.getD_some]
                          have hgi_lvl_lt : ((s_tr.core.tmp[(BitVec.ofNat 64 gi).toNat]'hgi_idx >>>
                              1#32).setWidth 64).toNat < s_tr.core.lvl.length := by
                            rw [bv32_setWidth64_toNat, m5_la_bv32_lshr_1, hgi_t_eq, hgi_l_eq,
                              htr_lvl, h2_len.core_ok.lvl_len]
                            have := h2_len.core_ok.cur_vars_le; have := hgi_post.1; omega
                          have hgi1_nat : (BitVec.ofNat 64 gi + 1#64).toNat = gi + 1 := by
                            rw [m5_la_bv64_add1_toNat (by rw [hgi_bv]; omega), hgi_bv]
                          c0_clean; c0_steps
                          all_goals exact (ih_gi (tl_ms - (gi + 1)) _ m_gi (by omega)
                            ⟨gi + 1, by omega, by omega, rfl,
                              BitVec.eq_of_toNat_eq (by
                                rw [show (1 : BitVec 64) = 1#64 from rfl, hgi1_nat,
                                  bv64_ofNat_toNat (by omega)]),
                              hm_gi⟩)
                        · -- Post-glue: `if (h->probing == 0ULL) { full_ema_update(h, glue); }`
                          c0_to_group
                          refine wp_join_group (ts := []) (fun () m_em =>
                              ∃ s_em : FullState,
                                s_em.core = s_tr.core ∧ FullOtfsInvW c F0 F_cur s_em ∧
                                s_em.scratch.work_stk2 = s.scratch.work_stk2 ∧
                                (FullMem c s_em ⋆ R) m_em) ?_ ?_
                          · rintro _ ⟨⟩ m_em ⟨s_em, hem_core_eq, hem_otfs, hem_ws2, hm_em⟩
                            c0_to_group; c0_call hLearnCl
                            refine ⟨c, F0, F_cur, s_em, R, rfl, hem_otfs, ?_, ?_, ?_, ?_, ?_, ?_,
                              ?_, hm_em, ?_⟩
                            · rw [hem_core_eq, htr_cl]; omega
                            · rw [hem_core_eq, htr_tl]; exact hms_tl1
                            · rw [hem_core_eq, htr_tl, htr_cv]; omega
                            · rw [hem_core_eq, htr_tmp, htr_tl]; exact hms_nd
                            · intro k hk
                              rw [hem_core_eq, htr_tl] at hk
                              rw [hem_core_eq, htr_tmp, htr_vals, htr_cv]
                              cases k with
                              | zero =>
                                have h0_s2 := h2_vals 0 h2_tl1
                                have h0_eq : tmp_ms[0]? = s2.core.tmp[0]? := hms_0
                                rw [h0_eq]; exact h0_s2
                              | succ k' =>
                                have hk_p := hms_post (k' + 1) (by omega) hk
                                exact ⟨hk_p.1, hk_p.2.1⟩
                            · intro k hk1 hk2
                              rw [hem_core_eq, htr_tl] at hk2
                              rw [hem_core_eq, htr_tmp, htr_tl, htr_lvl, htr_cl]
                              have hk_p := hms_post k hk1 hk2
                              exact ⟨hk_p.2.2.1, hk_p.2.2.2.1, hk_p.2.2.2.2⟩
                            · rw [hem_core_eq, htr_tmp, htr_tl]; exact hms_ent
                            · intro rl s_lc m_lc hlc_len hlc_dom hlc_cv hlc_fu hlc_ws2 hlc_20
                                hlc_0 hlc_1 hm_lc
                              have hlc_cv' : s_lc.core.cur_vars = s.core.cur_vars :=
                                hlc_cv.trans (by rw [hem_core_eq, htr_cv]; exact h2_cv')
                              have hlc_fu' : s_lc.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                have hem_fu : s_em.core.fuel = s2.core.fuel := by
                                  rw [hem_core_eq, htr_fu]
                                rw [hem_fu] at hlc_fu; exact Nat.le_trans hlc_fu h2_fu'
                              have hlc_ws2' : s_lc.scratch.work_stk2 = s.scratch.work_stk2 :=
                                hlc_ws2.trans hem_ws2
                              c0_steps
                              exact hQ rl s_lc m_lc hlc_len hlc_dom hlc_cv' hlc_fu'
                                ⟨hlc_ws2', fun h20 => let ⟨_, hsp, hcl⟩ := hlc_20 h20
                                  ⟨m5_sparse_to_canonOtfs hsp, by
                                    rw [hem_core_eq, htr_cl] at hcl; omega,
                                    hsp.2.2.2.2.2.trans hs.2.2.2.2.2.symm⟩⟩
                                (fun h20 => (hlc_20 h20).1)
                                (fun h0 => m5_sparse_to_canonOtfs (hlc_0 h0))
                                (fun h1 => let ⟨hs1, hcl1⟩ := hlc_1 h1
                                  ⟨hs1, by rw [hem_core_eq, htr_cl] at hcl1; omega⟩)
                                hm_lc
                          · intro Jem hJem; c0_split
                            · c0_to_group; c0_call hEma
                              refine ⟨c, s_tr, R, rfl, htr_len, hm_gi,
                                fun _ s_em m_em hem_core hem_len hem_pres hm_em => ?_⟩
                              have hem_otfs :=
                                m5_fullOtfsInvW_of_safetySlice htr_otfs hem_len hem_core hem_pres.1
                              c0_steps
                              exact hJem () m_em ⟨s_em, m5_safetySlice_core_eq hem_core, hem_otfs,
                                hem_pres.2.2.1.trans htr_ws2, hm_em⟩
                            · c0_steps; exact hJem () m_gi ⟨s_tr, rfl, htr_otfs, htr_ws2, hm_gi⟩
                      · intro Jgl hJgl; c0_steps
                        exact hJgl (tl_ms - 1) (1#64, 0#32, 1#64, ()) m_tr
                          ⟨1, Nat.le_refl _, hms_tl1, rfl, rfl, hm_tr⟩
                    · -- `if (h->probing == 0ULL) { restore_bump_ana; tick_rel; }` body
                      intro Jpms hJpms; c0_split
                      · c0_to_group; c0_call hRestoreBump
                        refine ⟨c, s_ms, R, rfl, hms_len, hms_clr.1, hm_ms, ?_⟩
                        intro mrk_rb mcl_rb sc_rb m_rb _ hrb_len hrb_m0 hrb_pres hrb_ws2 hm_rb
                        let s_rb : FullState :=
                          { s_ms with
                            core := { s_ms.core with mrk := mrk_rb, min_clr_len := mcl_rb }
                            scratch := sc_rb }
                        have hrb_otfs :=
                          m5_fullOtfsInvW_of_restoreBump hms_otfs hrb_len hrb_m0 hrb_pres
                        c0_to_group; c0_call hTickRel
                        refine ⟨c, s_rb, R, rfl, hrb_len, hm_rb,
                          fun _ s_tr m_tr htr_core htr_len htr_pres hm_tr => ?_⟩
                        have htr_otfs :=
                          m5_fullOtfsInvW_of_safetySlice hrb_otfs htr_len htr_core htr_pres.1
                        have htr_ceq : s_tr.core = s_rb.core := m5_safetySlice_core_eq htr_core
                        c0_steps
                        exact hJpms () m_tr ⟨s_tr, htr_otfs,
                          by rw [htr_ceq], by rw [htr_ceq], by rw [htr_ceq], by rw [htr_ceq],
                          by rw [htr_ceq], by rw [htr_ceq], by rw [htr_ceq],
                          htr_pres.2.2.1.trans (hrb_ws2.trans h2_ws2'), hm_tr⟩
                      · c0_steps
                        exact hJpms () m_ms ⟨s_ms, hms_otfs, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                          by dsimp [s_ms]; exact h2_ws2', hm_ms⟩
      · -- Loop exit (`iter = cur_vars + 64`) -> return `0`
        c0_steps
        exact hQ 0#64 s_i m_i hcut_inv.1 (Or.inl rfl) hcv_i hfu_i
          ⟨hws2_i, fun h => by cases h⟩ (fun h => by cases h)
          (fun _ => m5_cut_to_canonOtfs hcut_inv) (fun h => by cases h) hm_i
    · intro L hL; c0_steps
      exact hL (s.core.cur_vars + 64) (0#64, ()) m
        ⟨0, s.core.trail_end, s, Nat.zero_le _, rfl, rfl, Nat.le_refl _, m5_sparse_to_canonCut hs,
          hcur_pos, Nat.le_refl _, hconfl.toCut hs.2.1, rfl, Nat.le_refl _, rfl, hm⟩

end LearnAnalyzeProof

end LeanQbe.T.Examples.Kissat.FullM5HeurCore
