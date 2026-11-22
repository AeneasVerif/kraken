module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof1
import LeanQbe.T.Examples.Kissat.FullMinLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 `PR-W2B` Proof Shard 2a (`full_min_lit_dfs_m6`, `full_min_lit_m6`, `shrink_lower`)

Proves `Func.wp` for `3` minimization DFS/lower-literal functions in `FullM6MinShrink.lean`
(UNSAT-only, no `@[expose]`):
1. `full_min_lit_dfs_m6` (`m6MinLitDfsSpec`)
2. `full_min_lit_m6` (`Full.fullMinLitSpec`)
3. `full_shrink_lower_m6` (`Full.fullShrinkLowerSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  FullMinMarkInv fullMinMarkCore fullMinMarkState fullMinMarkSpec
  fullMinLitSpec fullShrinkLowerSpec fullShrinkBlkSpec fullMinShrinkSpec
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

/-! ## 1. Wave-2B Spec & `Full` <-> `FullMinSpecs` Bridges -/

private theorem toSpecsMinInv {k : FullCoreState} {keep : List Nat}
    (h : Full.FullMinMarkInv k keep) : FullMinMarkInv k keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

private theorem toFullMinInv {k : FullCoreState} {keep : List Nat}
    (h : FullMinMarkInv k keep) : Full.FullMinMarkInv k keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

private theorem specs_minMarkSpec_of_full {args m Q X}
    (h : fullMinMarkSpec args m Q X) : Full.fullMinMarkSpec args m Q X := by
  rcases args with ⟨h0, v, tag, ⟨⟩⟩
  rcases h with ⟨c, s, R, rfl, hlen, hm, hrest⟩
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  dsimp only at hrest ⊢
  split
  · simpa only [↓reduceIte, ite_eq_left ‹_›] using hrest
  · rename_i hneg
    simp only [ite_eq_right hneg] at hrest ⊢
    intro m' hm'
    dsimp only [Full.fullMinMarkState, Full.fullMinMarkCore] at hm'
    by_cases hcz : s.core.mrk[v.toNat]?.getD 0#8 = 0#8
    · by_cases hlt : s.core.min_clr_len < s.core.cur_vars
      · simp only [hcz, hlt, ↓reduceIte, not_true_eq_false, and_self, and_false,
          bv_ofNat_toNat_eq] at hrest hm'
        exact hrest m' hm'
      · simp only [hcz, hlt, ↓reduceIte, not_false_eq_true, and_self, and_false] at hrest hm'
        exact hrest m' hm'
    · simp only [hcz, ↓reduceIte, ne_eq, not_false_eq_true, false_and] at hrest hm'
      exact hrest m' hm'

/-- Conflict minimization DFS contract for `full_min_lit_dfs_m6(h, root_lit, min, check_used)`.
Reads `shrink_stk` (`used`) read-only on optional early bailout without modifying `MinLitStInv`. -/
def m6MinLitDfsSpec : Spec [i64, i32, .bool, .bool] [.bool] :=
  fun (h, root_lit, _minimizing, _check_used, ()) m Q X =>
    Full.fullMinLitSpec (h, root_lit, ()) m Q X

theorem m6MinLitDfsSpec_of {h : BitVec 64} {root_lit : BitVec 32} {minimizing check_used : Bool}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hspec : Full.fullMinLitSpec (h, root_lit, ()) m Q X) :
    m6MinLitDfsSpec (h, root_lit, minimizing, check_used, ()) m Q X :=
  hspec

theorem m6MinLitDfsSpec_monoX {xs : Tup Val [i64, i32, .bool, .bool]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost}
    (h : m6MinLitDfsSpec xs m Q X) : m6MinLitDfsSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

/-! ## 2. Bit-31 `pword` & `FrameCov` / `MinLitStkInv` / `MinLitStInv` Helpers -/

private theorem bv32_mask31_lt (pw : BitVec 32) : (pw &&& 0x7FFFFFFF#32).toNat < 2 ^ 31 := by
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by omega)

private theorem bv32_mask31_bit_true {i : Nat} (hi : i < 32) (h31 : i ≠ 31) :
    (0x7FFFFFFF#32 : BitVec 32)[i] = true := by
  rw [BitVec.getElem_eq_testBit_toNat,
    show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.testBit_two_pow_sub_one]
  exact decide_eq_true (by omega)

private theorem bv32_mask31_test31 : Nat.testBit (0x7FFFFFFF#32 : BitVec 32).toNat 31 = false :=
  by decide

private theorem bv32_one_test31 : Nat.testBit (1#32 : BitVec 32).toNat 31 = false :=
  by decide

private theorem bv32_mask31_or1_eq {pw : BitVec 32} (h0 : (pw &&& 0x7FFFFFFF#32) = 0#32) :
    ((pw ||| 1#32) &&& 0x7FFFFFFF#32).toNat = 1 := by
  have heq : (pw ||| 1#32) &&& 0x7FFFFFFF#32 = 1#32 := by
    ext i hi
    by_cases h31 : i = 31
    · subst h31
      rw [BitVec.getElem_and, BitVec.getElem_eq_testBit_toNat (x := 0x7FFFFFFF#32),
        bv32_mask31_test31, Bool.and_false, BitVec.getElem_eq_testBit_toNat, bv32_one_test31]
    · have hm := bv32_mask31_bit_true hi h31
      have hpwi : pw[i] = false := by
        have ht := congrArg (·[i]'hi) h0
        simpa [hm] using ht
      simp [hm, hpwi]
  rw [heq]; rfl

private theorem bv32_mask31_hi_or {pw v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (((pw &&& 0x80000000#32) ||| v) &&& 0x7FFFFFFF#32).toNat = v.toNat := by
  have heq : ((pw &&& 0x80000000#32) ||| v) &&& 0x7FFFFFFF#32 = v &&& 0x7FFFFFFF#32 := by
    ext i hi
    by_cases h31 : i = 31
    · subst h31
      rw [BitVec.getElem_and, BitVec.getElem_and,
        BitVec.getElem_eq_testBit_toNat (x := 0x7FFFFFFF#32), bv32_mask31_test31, Bool.and_false,
        Bool.and_false]
    · have hm := bv32_mask31_bit_true hi h31
      have hmsb : (0x80000000#32 : BitVec 32)[i] = false := by
        rw [BitVec.getElem_eq_testBit_toNat,
          show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl, Nat.testBit_two_pow]
        exact decide_eq_false (by omega)
      simp [hm, hmsb]
  rw [heq, BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv]

private theorem bv32_mask31_eq_of_lt {v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (v &&& 0x7FFFFFFF#32) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv]

private theorem bv32_mask31_hi_eq0 :
    ((0x80000000#32 : BitVec 32) &&& 0x7FFFFFFF#32).toNat = 0 := rfl

private theorem bv32_mask31_zero_eq0 : ((0#32 : BitVec 32) &&& 0x7FFFFFFF#32).toNat = 0 := rfl

private def minLitRsnLit (k : FullCoreState) (rsn : BitVec 32) (pos : Nat) : Nat :=
  if (rsn &&& 0x80000000#32) ≠ 0#32 then (rsn &&& 0x7FFFFFFF#32).toNat
  else (k.arena[rsn.toNat + 3 + pos]?.getD 0#32).toNat

private def FrameCov (k : FullCoreState) (mrk1 : List (BitVec 8)) (idx lim : Nat) : Prop :=
  let p := (k.trl[idx]?.getD 0#32).toNat
  let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
  rsn ≠ 0xFFFFFFFF#32 ∧
  if (rsn &&& 0x80000000#32) ≠ 0#32 then
    let ot := (rsn &&& 0x7FFFFFFF#32).toNat
    ot < 2 * k.cur_vars ∧
    (0 < lim →
      ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
        ((k.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8))
  else
    rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
    3 ≤ fullArenaClauseSizeCore k rsn.toNat ∧
    ∀ pos < lim, pos < fullArenaClauseSizeCore k rsn.toNat →
      let q := (k.arena[rsn.toNat + 3 + pos]?.getD 0#32).toNat
      q = p ∨ ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((k.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)

private def EdgeChild (k : FullCoreState) (idx pos cidx : Nat) : Prop :=
  let p := (k.trl[idx]?.getD 0#32).toNat
  let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
  let l := minLitRsnLit k rsn pos
  cidx < idx ∧ (k.trl[cidx]?.getD 0#32).toNat = l ^^^ 1

private theorem frameCov_zero {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) (mrk1 : List (BitVec 8)) {idx : Nat}
    (hi : idx < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hne : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32) :
    FrameCov s.core mrk1 idx 0 := by
  obtain ⟨_, hw⟩ := hcore.2
  have hrs := hw.reason_inv_below idx hi hlvl hne
  refine ⟨hne, ?_⟩
  split at hrs <;> split
  · exact ⟨hrs.1, fun h => by omega⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · have hwf := hw.arena.refs_wf _ hrs.1
    exact ⟨hrs.1, hrs.2.1, hwf.2.1, fun _ h => by omega⟩

private theorem frameCov_arena_lits_bd {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore s.core) :
    cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
  obtain ⟨_, hw⟩ := hcore.2
  have hwf := hw.arena.refs_wf cref href
  have := hwf.2.2.1; have := hwf.2.2.2.1
  have := hcore.1.core_ok.arena_len_le; have := hcore.1.core_ok.arena_len_arr; omega

private theorem frameCov_arena_lits_mem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {cref pos : Nat}
    (href : cref ∈ fullArenaClauseRefsCore s.core)
    (hp : pos < fullArenaClauseSizeCore s.core cref) :
    (s.core.arena[cref + 3 + pos]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s.core cref := by
  have hbd := frameCov_arena_lits_bd hcore href
  rw [mem_fullArenaClauseLitsCore_iff hbd]
  exact ⟨pos, hp, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

private theorem frameCov_mono {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hmono : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx lim : Nat} (hcov : FrameCov s.core mrk1 idx lim) : FrameCov s.core mrk2 idx lim := by
  obtain ⟨_, hw⟩ := hcore.2
  rcases hcov with ⟨hne, hif⟩
  refine ⟨hne, ?_⟩
  split at hif <;> split
  · refine ⟨hif.1, fun hl => ?_⟩
    obtain ⟨j, hj, hjeq, hdep⟩ := hif.2 hl
    exact ⟨j, hj, hjeq, hdep.elim Or.inl fun h2 => Or.inr (hmono _ (by omega) h2)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · refine ⟨hif.1, hif.2.1, hif.2.2.1, fun pos hp1 hp2 => ?_⟩
    rcases hif.2.2.2 pos hp1 hp2 with heq | ⟨j, hj, hjeq, hdep⟩
    · exact Or.inl heq
    · have hqlt := hw.arena.lits_lt _ hif.1 hif.2.1 _ (frameCov_arena_lits_mem hcore hif.1 hp2)
      exact Or.inr ⟨j, hj, hjeq, hdep.elim Or.inl fun h2 => Or.inr (hmono _ (by omega) h2)⟩

private theorem frameCov_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx pos : Nat}
    (hi : idx < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hcov : FrameCov s.core mrk1 idx pos)
    (hlt : pos < if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hstep :
      let p := (s.core.trl[idx]?.getD 0#32).toNat
      let rsn := s.core.rsns[p / 2]?.getD 0xFFFFFFFF#32
      let q := minLitRsnLit s.core rsn pos
      q / 2 = p / 2 ∨
      ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    FrameCov s.core mrk1 idx (pos + 1) := by
  obtain ⟨_, hw⟩ := hcore.2
  dsimp only [FrameCov] at hcov ⊢
  rcases hcov with ⟨hne, hif⟩
  have hrs := hw.reason_inv_below idx hi hlvl hne
  refine ⟨hne, ?_⟩
  dsimp only [minLitRsnLit] at hstep ⊢
  dsimp only at hif hrs hlt hstep ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlt hstep ⊢
    refine ⟨hif.1, fun _ => ?_⟩
    rcases hstep with hvar | ⟨j, hj, hjeq, hdep⟩
    · obtain ⟨j, hj, hjeq, _⟩ := hrs.2.2
      have hln := litVar_litNeg (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat
      unfold litVar litNeg at hln
      have hjp : j = idx := hw.trail_vars_nodup j idx (by omega) hi (by rw [hjeq, hln]; exact hvar)
      omega
    · exact ⟨j, hj, hjeq, hdep⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlt hstep ⊢
    refine ⟨hif.1, hif.2.1, hif.2.2.1, fun j hj1 hj2 => ?_⟩
    by_cases hjp : j < pos
    · exact hif.2.2.2 j hjp hj2
    · have hjeq : j = pos := by omega
      subst hjeq
      rcases hstep with hvar | hok
      · have hmem := frameCov_arena_lits_mem hcore hif.1 hj2
        rcases hrs.2.2 _ hmem with hqeq | ⟨k, hk, hkeq, _⟩
        · exact Or.inl hqeq
        · have hln := litVar_litNeg (s.core.arena[(s.core.rsns[(s.core.trl[idx]?.getD
            0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD 0#32).toNat
          unfold litVar litNeg at hln
          have hkp : k = idx := hw.trail_vars_nodup k idx (by omega) hi
            (by rw [hkeq, hln]; exact hvar)
          omega
      · exact Or.inr hok

private theorem frameCov_to_hrsn {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx lim : Nat}
    (hcov : FrameCov s.core mrk1 idx lim)
    (hlim : (if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim) :
    let p0 := (s.core.trl[idx]?.getD 0#32).toNat
    let rsn := s.core.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 ∧
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * s.core.cur_vars ∧
      ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
        ((s.core.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    else
      rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
      fullArenaClauseGarbCore s.core rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
        q = p0 ∨ ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  dsimp only [FrameCov] at hcov
  rcases hcov with ⟨hne, hif⟩
  refine ⟨hne, ?_⟩
  dsimp only at hif hlim ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hlim ⊢
    exact ⟨hif.1, hif.2 (by omega)⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hlim ⊢
    refine ⟨hif.1, hif.2.1, fun q hq => ?_⟩
    have hbd := frameCov_arena_lits_bd hcore hif.1
    obtain ⟨j, hj, hjeq⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hq
    have hq' := hif.2.2.2 j (by omega) hj
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hjeq] at hq'

private theorem frameCov_edge_exists {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx pos : Nat}
    (hi : idx < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hcov : FrameCov s.core mrk1 idx pos)
    (hlt : pos < if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hneq : minLitRsnLit s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos / 2 ≠
      (s.core.trl[idx]?.getD 0#32).toNat / 2) :
    let q := minLitRsnLit s.core
      (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos
    q < 2 * s.core.cur_vars ∧
    ∃ cidx < idx, (s.core.trl[cidx]?.getD 0#32).toNat = q ^^^ 1 ∧
      (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
  obtain ⟨_, hw⟩ := hcore.2
  dsimp only [FrameCov, minLitRsnLit] at hcov hlt hneq ⊢
  rcases hcov with ⟨hne, hif⟩
  have hrs := hw.reason_inv_below idx hi hlvl hne
  dsimp only at hif hrs hlt hneq ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlt hneq ⊢
    exact ⟨hrs.1, hrs.2.2⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlt hneq ⊢
    have hmem := frameCov_arena_lits_mem hcore hif.1 hlt
    have hqlt := hw.arena.lits_lt _ hif.1 hif.2.1 _ hmem
    refine ⟨hqlt, ?_⟩
    rcases hrs.2.2 _ hmem with heq | hex
    · exact absurd (by rw [heq]) hneq
    · exact hex

private theorem dec_chain_lt : ∀ {idxs : List Nat} {i j : Nat},
    (∀ k (hk : k + 1 < idxs.length), idxs[k + 1] < idxs[k]) →
    i < j → (hi : i < idxs.length) → (hj : j < idxs.length) → idxs[j] < idxs[i] := by
  intro idxs i j hdec hij hi hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hj_lt := hdec j hj
    by_cases heq : i = j
    · subst heq; exact hj_lt
    · exact Nat.lt_trans hj_lt (ih (by omega) (by omega))

private structure MinLitStkInv (k : FullCoreState) (mstk1 : List (BitVec 32))
    (mrk1 : List (BitVec 8)) (sp idx0 : Nat) (idxs : List Nat) (reqCov : Bool) : Prop where
  len : idxs.length = sp + 1
  idx0_eq : idxs[0]? = some idx0
  bd : ∀ j (hj : j < idxs.length), idxs[j] < k.trail_end
  dec : ∀ j (hj : j + 1 < idxs.length), idxs[j + 1] < idxs[j]
  lvl_le_root : ∀ j (hj : j < idxs.length),
    (k.lvl[(k.trl[idxs[j]]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (k.lvl[(k.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  slot : ∀ j (hj : j < idxs.length),
    let vj := (k.trl[idxs[j]]?.getD 0#32).toNat / 2
    (mstk1[2 * j]?.getD 0#32).toNat = vj ∧ (1 ≤ j → mrk1[vj]?.getD 0#8 = 0#8)
  cov : reqCov = true → ∀ j (hj : j < idxs.length),
    let posj := (mstk1[2 * j + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat
    let rsn := k.rsns[(k.trl[idxs[j]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
    (∀ _hj1 : j + 1 < idxs.length, 1 ≤ posj ∧
      posj ≤ (if (rsn &&& 0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore k rsn.toNat) ∧
      EdgeChild k idxs[j] (posj - 1) idxs[j + 1]) ∧
    FrameCov k mrk1 idxs[j] (if j + 1 = idxs.length then posj else posj - 1)

private theorem minLitStkInv_drop_cov {k : FullCoreState} {mstk1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv k mstk1 mrk1 sp idx0 idxs true) :
    MinLitStkInv k mstk1 mrk1 sp idx0 idxs false :=
  ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, h.slot, fun hc => by cases hc⟩

private theorem minLitStkInv_var_ne {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 : Nat} {idxs : List Nat} {req}
    (h : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs req)
    {i j : Nat} (hi : i < idxs.length) (hj : j < idxs.length) (hne : i ≠ j) :
    (s.core.trl[idxs[i]]?.getD 0#32).toNat / 2 ≠ (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 := by
  obtain ⟨_, hw⟩ := hcore.2
  intro heq
  have hij := hw.trail_vars_nodup idxs[i] idxs[j] (h.bd i hi) (h.bd j hj) heq
  rcases Nat.lt_or_gt_of_ne hne with h1 | h2
  · have := dec_chain_lt h.dec h1 hi hj; omega
  · have := dec_chain_lt h.dec h2 hj hi; omega

private theorem minLitStkInv_poison_other {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mstk1 mclr1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {sp idx0 u_idx mcl1 : Nat} {mcf1 : BitVec 64}
    {idxs : List Nat} (h : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs false)
    (hu_idx : ∀ j (hj : j < idxs.length), u_idx < idxs[j])
    (hmrk_eq : ∀ w < s.core.cur_vars, w ≠ (s.core.trl[u_idx]?.getD 0#32).toNat / 2 →
      mrk1[w]?.getD 0#8 = (fullMinMarkCore
        (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core
        ((s.core.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk[w]?.getD 0#8) :
    MinLitStkInv s.core mstk1
      (fullMinMarkCore (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core
        ((s.core.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk sp idx0 idxs false := by
  obtain ⟨_, hw⟩ := hcore.2
  refine ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, fun j hj => ?_, fun hc => by cases hc⟩
  refine ⟨(h.slot j hj).1, fun hj1 => ?_⟩
  have hvj : (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
    have := hw.trail_lits_lt idxs[j] (h.bd j hj); omega
  have hne : (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 ≠
      (s.core.trl[u_idx]?.getD 0#32).toNat / 2 := fun heq => by
    have hlt := hu_idx j hj
    have := hw.trail_vars_nodup idxs[j] u_idx (h.bd j hj) (Nat.lt_trans hlt (h.bd j hj)) heq
    omega
  rw [← hmrk_eq _ hvj hne]
  exact (h.slot j hj).2 hj1

private theorem minLitStkInv_step_top {c : FullCfg} {k : FullCoreState}
    {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)} {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv k mstk1 mrk1 sp idx0 idxs true)
    (hmstk_len : mstk1.length = 2 * c.minDepth) (hsp : sp < c.minDepth) (newPos : BitVec 32)
    (hcov_top : ∀ hk : sp < idxs.length,
      FrameCov k mrk1 idxs[sp] (newPos &&& 0x7FFFFFFF#32).toNat) :
    MinLitStkInv k (mstk1.set (2 * sp + 1) newPos) mrk1 sp idx0 idxs true := by
  have hlt_stk : 2 * sp + 1 < mstk1.length := by omega
  refine ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact h.slot j hj
  · have hlen := h.len
    by_cases htop : j = sp
    · subst htop
      rw [List.getElem?_set_self hlt_stk, Option.getD_some]
      refine ⟨fun hk1 => by omega, ?_⟩
      simp only [show j + 1 = idxs.length by omega, ↓reduceIte]
      exact hcov_top hj
    · have hne_len : ¬ (j + 1 = idxs.length) := by omega
      rw [List.getElem?_set_ne (by omega)]
      simpa only [hne_len, ↓reduceIte] using h.cov rfl j hj

private theorem minLitStkInv_push {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 u_idx : Nat} {idxs : List Nat}
    (h : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs true)
    (hroot_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hmstk_len : mstk1.length = 2 * c.minDepth) (hsp1 : sp + 1 < c.minDepth)
    {u_bv par_pw ch_pw : BitVec 32}
    (hpos_eq : (par_pw &&& 0x7FFFFFFF#32).toNat =
      (mstk1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hch_eq : (ch_pw &&& 0x7FFFFFFF#32).toNat = 0)
    (hu_bd : u_idx < idxs[sp]'(by have := h.len; omega))
    (hu_eq : u_bv.toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
    (hu_lvl : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hpos_lt : (mstk1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat <
      (if (s.core.rsns[(s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
        else fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp]'(by
          have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat))
    (hmrk_u : mrk1[u_bv.toNat]?.getD 0#8 = 0#8)
    (hrsn_u : s.core.rsns[u_bv.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hedge : EdgeChild s.core (idxs[sp]'(by have := h.len; omega))
      (mstk1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat u_idx) :
    let mstk2 := ((mstk1.set (2 * sp + 1) par_pw).set (2 * (sp + 1)) u_bv).set
      (2 * (sp + 1) + 1) ch_pw
    MinLitStkInv s.core mstk2 mrk1 (sp + 1) idx0 (idxs ++ [u_idx]) true := by
  intro mstk2
  have hlen := h.len
  have hb1 : 2 * sp + 1 < mstk1.length := by omega
  have hb2 : 2 * (sp + 1) < (mstk1.set (2 * sp + 1) par_pw).length := by simp [hmstk_len]; omega
  have hb3 : 2 * (sp + 1) + 1 <
      ((mstk1.set (2 * sp + 1) par_pw).set (2 * (sp + 1)) u_bv).length := by
    simp [hmstk_len]; omega
  have idx_lt : ∀ j (hj : j < idxs.length), (idxs ++ [u_idx])[j]'(by simp; omega) = idxs[j] :=
    fun j hj => List.getElem_append_left hj
  have idx_last : (idxs ++ [u_idx])[idxs.length]'(by simp) = u_idx := by simp
  refine ⟨by simp [hlen], ?_, ?_, ?_, ?_, fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [List.getElem?_append_left (by omega)]; exact h.idx0_eq
  · intro j hj
    by_cases hjl : j < idxs.length
    · rw [idx_lt j hjl]; exact h.bd j hjl
    · have hjeq : j = idxs.length := by simp at hj; omega
      subst j; rw [idx_last]; exact Nat.lt_trans hu_bd (h.bd sp (by omega))
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j + 1 < idxs.length
    · rw [idx_lt j (by omega), idx_lt (j + 1) hjl]; exact h.dec j hjl
    · have hjeq : j = sp := by omega
      subst j
      rw [idx_lt sp (by omega), List.getElem_append_right (by omega : idxs.length ≤ sp + 1)]
      simp only [hlen, Nat.sub_self, List.getElem_cons_zero]; exact hu_bd
  · intro j hj
    by_cases hjl : j < idxs.length
    · rw [idx_lt j hjl]; exact h.lvl_le_root j hjl
    · have hjeq : j = idxs.length := by simp at hj; omega
      subst j; rw [idx_last]; exact hu_lvl
  · by_cases hjl : j < idxs.length
    · rw [idx_lt j hjl]; dsimp only [mstk2]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]
      exact h.slot j hjl
    · have hjeq : j = idxs.length := by simp at hj; omega
      subst j; rw [idx_last]; dsimp only [mstk2]
      rw [List.getElem?_set_ne (by omega), show 2 * idxs.length = 2 * (sp + 1) by omega,
        List.getElem?_set_self hb2, Option.getD_some]
      exact ⟨hu_eq, fun _ => by rwa [← hu_eq]⟩
  · by_cases hjl : j < idxs.length
    · rw [idx_lt j hjl]
      by_cases htop : j = sp
      · subst j; dsimp only [mstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self hb1, Option.getD_some]
        refine ⟨fun _ => ?_, ?_⟩
        · rw [hpos_eq]; refine ⟨by omega, by omega, ?_⟩
          rw [List.getElem_append_right (by omega : idxs.length ≤ sp + 1)]
          simp only [hlen, Nat.sub_self, List.getElem_cons_zero]; exact hedge
        · have hne : sp + 1 ≠ (idxs ++ [u_idx]).length := by
            rw [List.length_append, List.length_singleton, hlen]; omega
          simp only [hne, ↓reduceIte, hpos_eq, Nat.add_sub_cancel]
          have hcov_sp := (h.cov rfl sp hjl).2
          have heq_sp : sp + 1 = idxs.length := by omega
          simpa only [heq_sp, ↓reduceIte] using hcov_sp
      · have hj1 : j + 1 < idxs.length := by omega
        dsimp only [mstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]
        have hprev := h.cov rfl j hjl
        have hne1 : j + 1 ≠ (idxs ++ [u_idx]).length := by
          rw [List.length_append, List.length_singleton, hlen]; omega
        have hne2 : j + 1 ≠ idxs.length := by omega
        simp only [hne1, hne2, ↓reduceIte] at hprev ⊢
        refine ⟨fun _ => ?_, hprev.2⟩
        rw [idx_lt (j + 1) hj1]; exact hprev.1 hj1
    · have hjeq : j = idxs.length := by simp at hj; omega
      subst j; rw [idx_last]; dsimp only [mstk2]
      rw [show 2 * idxs.length + 1 = 2 * (sp + 1) + 1 by omega, List.getElem?_set_self hb3,
        Option.getD_some]
      refine ⟨fun hk1 => by simp only [List.length_append, List.length_singleton] at hk1; omega,
        ?_⟩
      simp only [List.length_append, List.length_singleton, ↓reduceIte, hch_eq]
      exact frameCov_zero hcore mrk1 (Nat.lt_trans hu_bd (h.bd sp (by omega)))
        (Nat.lt_of_le_of_lt hu_lvl hroot_lvl) (by rw [← hu_eq]; exact hrsn_u)

private theorem minLitStkInv_pop {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 mrk2 : List (BitVec 8)}
    {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs true) (hsp : 0 < sp)
    (hroot_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hmono : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hmrk_top : (mrk2[(s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD
      0#8 &&& 2#8) ≠ 0#8)
    (hmrk_keep : ∀ j (hj : j < sp),
      mrk2[(s.core.trl[idxs[j]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0#8 =
        mrk1[(s.core.trl[idxs[j]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0#8) :
    MinLitStkInv s.core mstk1 mrk2 (sp - 1) idx0 (idxs.take sp) true := by
  have hlen := h.len
  have htake_len : (idxs.take sp).length = sp := by rw [List.length_take, hlen]; omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [← h.idx0_eq]; exact List.getElem?_take_of_lt hsp
  · intro j hj; rw [List.getElem_take]; exact h.bd j (by omega)
  · intro j hj; rw [List.getElem_take, List.getElem_take]; exact h.dec j (by omega)
  · intro j hj; rw [List.getElem_take]; exact h.lvl_le_root j (by omega)
  · rw [List.getElem_take]
    refine ⟨(h.slot j (by omega)).1, fun hj1 => ?_⟩
    rw [hmrk_keep j (by omega)]; exact (h.slot j (by omega)).2 hj1
  · rw [List.getElem_take]
    have hprev := h.cov rfl j (by omega)
    have hne : j + 1 ≠ idxs.length := by omega
    simp only [hne, ↓reduceIte] at hprev
    by_cases hntop : j = sp - 1
    · subst j
      refine ⟨fun hk1 => by omega, ?_⟩
      simp only [htake_len, show sp - 1 + 1 = sp by omega, ↓reduceIte]
      have hpos1 :
          1 ≤ (mstk1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat :=
        (hprev.1 (by omega)).1
      have hpos_le := (hprev.1 (by omega)).2.1
      have hedge := (hprev.1 (by omega)).2.2
      simp only [show sp - 1 + 1 = sp by omega] at hedge
      have hcov_m := frameCov_mono hcore hmono hprev.2
      dsimp only [EdgeChild] at hedge
      have hsz_lt : (mstk1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat - 1 <
          if (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
              0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
            (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32).toNat := by omega
      have hstep := frameCov_step hcore (h.bd (sp - 1) (by omega))
        (Nat.lt_of_le_of_lt (h.lvl_le_root (sp - 1) (by omega)) hroot_lvl) hcov_m hsz_lt ?_
      · simpa only [show (mstk1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat - 1 + 1 =
          (mstk1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat by omega] using hstep
      · have hdec_sp : idxs[sp]'(by omega) < idxs[sp - 1]'(by omega) := by
          simpa [show sp - 1 + 1 = sp by omega] using h.dec (sp - 1) (by omega)
        refine Or.inr ⟨idxs[sp]'(by omega), hdec_sp, hedge.2, Or.inr ?_⟩
        have hvar : (minLitRsnLit s.core
            (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
            ((mstk1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat - 1)) / 2 =
            (s.core.trl[idxs[sp]]?.getD 0#32).toNat / 2 := by
          have hl := litVar_litNeg (minLitRsnLit s.core
            (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
            ((mstk1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat - 1))
          unfold litVar litNeg at hl; rw [← hl, ← hedge.2]
        rwa [hvar]
    · have hne2 : j + 1 ≠ (idxs.take sp).length := by omega
      simp only [hne2, ↓reduceIte]
      refine ⟨fun _ => ?_, frameCov_mono hcore hmono hprev.2⟩
      rw [List.getElem_take]; exact hprev.1 (by omega)

private structure MinLitStInv (c : FullCfg) (s : FullState) (keepSet : List Nat)
    (mrk1 : List (BitVec 8)) (mstk1 mclr1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 : BitVec 64) : Prop where
  mrk_len : mrk1.length = c.max_vars
  mstk_len : mstk1.length = 2 * c.minDepth
  mclr_len : mclr1.length = c.max_vars
  mcl_le : mcl1 ≤ c.max_vars
  mrk_above : ∀ w, s.core.cur_vars ≤ w → mrk1[w]? = s.core.mrk[w]?
  min_inv : FullMinMarkInv (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core keepSet
  mono2 : ∀ w < s.core.cur_vars,
    (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8 : ∀ w < s.core.cur_vars,
    (mrk1[w]?.getD 0#8 &&& 8#8) = (s.core.mrk[w]?.getD 0#8 &&& 8#8)

private theorem MinLitStInv.core {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} (hcore : FullOtfsCoreInv c F0 s)
    (h : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1) :
    FullOtfsCoreInv c F0 (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) :=
  fullOtfsCoreInv_with_min hcore h.mrk_len h.mstk_len h.mclr_len h.mcl_le

private theorem minLitStInv_with_mstk {c : FullCfg} {s : FullState} {keepSet : List Nat}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 mstk' : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (h : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    (hmstk' : mstk'.length = 2 * c.minDepth) :
    MinLitStInv c s keepSet mrk1 mstk' mclr1 mcl1 mcf1 :=
  { h with
    mstk_len := hmstk'
    min_inv := fullMinMarkInv_with_mstk h.min_inv mstk' }

private theorem minLitStInv_mark {c : FullCfg} {s : FullState} {keepSet : List Nat}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hsi : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    {v : Nat} (hv : v < s.core.cur_vars) (hz : mrk1[v]?.getD 0#8 = 0#8) (tag : BitVec 8)
    (htag : tag = 2#8 ∨ tag = 4#8)
    (hmin' : FullMinMarkInv
      (fullMinMarkCore (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core v tag) keepSet) :
    let k_p := (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core
    let k' := fullMinMarkCore k_p v tag
    MinLitStInv c s keepSet k'.mrk mstk1 k'.min_clr k'.min_clr_len k'.min_clr_full ∧
    (∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  intro k_p k'
  have hv_max : v < c.max_vars := by omega
  have hmono_prev : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro w _ hw2; dsimp only [k', fullMinMarkCore]
    by_cases hweq : w = v
    · subst w; rw [hz] at hw2; exact absurd rfl hw2
    · rwa [List.getElem?_set_ne (Ne.symm hweq)]
  have hbit8' : ∀ w < s.core.cur_vars,
      (k'.mrk[w]?.getD 0#8 &&& 8#8) = (s.core.mrk[w]?.getD 0#8 &&& 8#8) := by
    intro w hw; dsimp only [k', fullMinMarkCore]
    by_cases hweq : w = v
    · subst w
      rw [List.getElem?_set_self (by rw [hsi.mrk_len]; exact hv_max), Option.getD_some]
      have hz' : k_p.mrk[v]?.getD 0#8 = 0#8 := hz
      rw [hz', ← hsi.bit8 v hv, hz']
      rcases htag with rfl | rfl <;> decide
    · rw [List.getElem?_set_ne (Ne.symm hweq)]; exact hsi.bit8 w hw
  have hab' : ∀ w, s.core.cur_vars ≤ w → k'.mrk[w]? = s.core.mrk[w]? := fun w hw => by
    dsimp only [k', fullMinMarkCore]
    rw [List.getElem?_set_ne (by omega)]; exact hsi.mrk_above w hw
  have hmclr' : k'.min_clr.length = c.max_vars := by
    dsimp only [k', k_p, fullMinMarkCore]; split <;> simp [hsi.mclr_len]
  have hmcl' : k'.min_clr_len ≤ c.max_vars := by
    have hmcl_le := hsi.mcl_le; dsimp only [k', k_p, fullMinMarkCore]; split <;> omega
  have hmrk' : k'.mrk.length = c.max_vars := by
    dsimp only [k', k_p, fullMinMarkCore]; rw [List.length_set]; exact hsi.mrk_len
  refine ⟨⟨hmrk', hsi.mstk_len, hmclr', hmcl', hab', hmin',
    fun w hw hws => hmono_prev w hw (hsi.mono2 w hw hws), hbit8'⟩, hmono_prev⟩

private theorem fullMinMarkSpec_zero_inv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} {m1 : Mem 64} {Q' : Post []} {X' : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (hmrk : mrk1.length = c.max_vars)
    (hmstk : mstk1.length = 2 * c.minDepth) (hmclr : mclr1.length = c.max_vars)
    (hmcl : mcl1 ≤ c.max_vars)
    (hm1 : (FullMem c (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) ⋆ R) m1)
    {v : BitVec 32} (hv : v.toNat < s.core.cur_vars) (hz : mrk1[v.toNat]?.getD 0#8 = 0#8)
    (tag : BitVec 8)
    (hpost : ∀ m',
      let k1 := (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core
      let k2 := fullMinMarkCore k1 v.toNat tag
      (FullMem c (minLitState s k2.mrk mstk1 k2.min_clr k2.min_clr_len k2.min_clr_full) ⋆ R)
        m' → Q' () m') :
    fullMinMarkSpec (c.hdr, v, tag, ()) m1 Q' X' := by
  let st1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
  have hlen1 : st1.LengthsOk c :=
    (fullOtfsCoreInv_with_min hcore hmrk hmstk hmclr hmcl).1
  refine ⟨c, st1, R, rfl, hlen1, hm1, ?_⟩
  dsimp only
  have hc1 : ¬ (st1.core.cur_vars ≤ v.toNat ∨ (st1.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) :=
    fun h => h.elim (fun hle => by dsimp only [st1, minLitState] at hle; omega) fun hne => by
      change (mrk1[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 at hne; rw [hz] at hne; simp at hne
  have hc2 : ¬ (st1.core.mrk[v.toNat]?.getD 0#8 ≠ 0#8) := fun h => h hz
  simp only [eq_false hc1, eq_false hc2, ↓reduceIte]
  have hzor : (0#8 : BitVec 8) ||| tag = tag := BitVec.zero_or
  by_cases hlt : mcl1 < s.core.cur_vars
  · have hlt' : st1.core.min_clr_len < st1.core.cur_vars := hlt
    simp only [eq_true hlt', ↓reduceIte]
    intro m' hm'
    have hp := hpost m'
    dsimp only [fullMinMarkCore, minLitState] at hp ⊢
    have hmcl1' : mcl1 < s.core.cur_vars := hlt
    simp only [hz, hmcl1', and_self, not_true_eq_false, and_false, ↓reduceIte, hzor] at hp
    have hv_eq : BitVec.ofNat 32 v.toNat = v := bv_ofNat_toNat_eq v
    dsimp only [st1, minLitState] at hm'
    rw [hz, hzor] at hm'; rw [hv_eq] at hp; exact hp hm'
  · have hlt' : ¬ st1.core.min_clr_len < st1.core.cur_vars := hlt
    simp only [eq_false hlt', ↓reduceIte]
    intro m' hm'
    have hp := hpost m'
    dsimp only [fullMinMarkCore, minLitState] at hp ⊢
    have hmcl1' : ¬ mcl1 < s.core.cur_vars := hlt
    simp only [hz, hmcl1', and_self, and_false, not_false_eq_true, ↓reduceIte, hzor] at hp
    dsimp only [st1, minLitState] at hm'
    rw [hz, hzor] at hm'; exact hp hm'

private theorem store_minLit_stk {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hbi : i.toNat < mstk.length)
    (hm : (FullMem c (minLitState s mrk mstk mclr mcl mcf) ⋆ R) m) :
    storeOk m i32 (c.pMinStk + i * 4) ∧
    (FullMem c (minLitState s mrk (mstk.set i.toNat v) mclr mcl mcf) ⋆ R)
      (storeMem m i32 (c.pMinStk + i * 4) v) :=
  c0_store_full_min_stk (s := minLitState s mrk mstk mclr mcl mcf) (i := i) v hbi hm

private theorem minLit_maxSteps_toNat {c : FullCfg} {s : FullState}
    (hle : s.core.arena_len ≤ c.arena_cap) (hcv : s.core.cur_vars ≤ c.max_vars) :
    ((BitVec.ofNat 64 s.core.arena_len + BitVec.ofNat 64 s.core.cur_vars) * 4 + 64).toNat =
      (s.core.arena_len + s.core.cur_vars) * 4 + 64 := by
  have hmx := c.hmaxv; have har := c.harena; unfold dimacsBound at hmx har
  have hbd : (s.core.arena_len + s.core.cur_vars) * 4 + 64 < 2 ^ 64 := by omega
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4, h64]
  rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : s.core.arena_len + s.core.cur_vars < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (s.core.arena_len + s.core.cur_vars) * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt hbd]

private theorem minLitDfs_ok_post {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {root_lit : BitVec 32} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    {m' : Mem 64} {idx0 lim : Nat}
    (hcore : FullOtfsCoreInv c F0 s) (hrl_lvl :
      (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hsi : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    (hm' : (FullMem c (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) ⋆ R) m')
    (hi0 : idx0 < s.core.trail_end)
    (hi0_eq : (s.core.trl[idx0]?.getD 0#32).toNat = root_lit.toNat ^^^ 1)
    (hlim : (if (s.core.rsns[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim)
    (hcov : FrameCov s.core mrk1 idx0 lim)
    (hQ : ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_stk := mstk', min_clr := mclr',
                                       min_clr_len := mcl', min_clr_full := mcf' } }
      s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv s'.core keepSet →
      (ok = true →
        (∀ keep' : List Nat,
          (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') → FullMinMarkInv s'.core keep') ∧
        FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (true, ()) m' := by
  have hcore1 := hsi.core hcore
  have hh := frameCov_to_hrsn hcore hcov hlim
  have hrv : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
    have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl; rw [hi0_eq, hl]
  refine hQ true mrk1 mstk1 mclr1 mcl1 mcf1 m' hcore1.1 hsi.mrk_above hsi.mono2 hsi.bit8
    hsi.min_inv (fun _ => ⟨fun keep' hsub => ?_, ?_⟩) hm'
  · refine fullMinMarkInv_drop hcore1 hsi.min_inv hsub hrl_lvl hi0 hi0_eq ?_
    simp only [hi0_eq] at hh; exact hh
  · have hno8_w : (mrk1[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
      rw [hrv, hsi.bit8 _ (by rw [← hrv]; have := hcore.2.choose_spec.trail_lits_lt _ hi0; omega)]
      exact hno8 _ (by rw [← hrv]; have := hcore.2.choose_spec.trail_lits_lt _ hi0; omega)
        (le_refl _)
    have hmrk := fullMinMarkInv_mark_rem hcore1 hsi.min_inv hi0 (by rw [hrv]; exact hrl_lvl)
      hno8_w hh
    simpa only [hrv] using hmrk

/-! ## 3. Shared DFS Pop, Poison, and Ret Helpers -/

private theorem minLitDfs_pop_state {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} {sp idx0 : Nat} {idxs : List Nat}
    {v : BitVec 32} (hcore : FullOtfsCoreInv c F0 s)
    (hsi : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    (hstk : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs true)
    (hsp_gt0 : 0 < sp) (hsp_idxs : sp < idxs.length)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hv_nat : v.toNat = (s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2)
    (hv_lt : v.toNat < s.core.cur_vars)
    {lim : Nat}
    (hlim : (if (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
      else fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim)
    (hcov_sp : FrameCov s.core mrk1 idxs[sp] lim)
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hm' : (FullMem c (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) ⋆ R) m')
    {Q' : Post []} {X' : XPost}
    (hpost : ∀ (k4 : FullCoreState) (m4 : Mem 64),
      k4 = fullMinMarkCore (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core v.toNat 2#8 →
      MinLitStInv c s keepSet k4.mrk mstk1 k4.min_clr k4.min_clr_len k4.min_clr_full →
      MinLitStkInv s.core mstk1 k4.mrk (sp - 1) idx0 (idxs.take sp) true →
      (FullMem c (minLitState s k4.mrk mstk1 k4.min_clr k4.min_clr_len k4.min_clr_full) ⋆ R) m4 →
      Q' () m4) :
    fullMinMarkSpec (c.hdr, v, (2 : BitVec 32).setWidth 8, ()) m' Q' X' := by
  have hz_v : mrk1[v.toNat]?.getD 0#8 = 0#8 := by
    rw [hv_nat]; exact (hstk.slot sp hsp_idxs).2 hsp_gt0
  refine fullMinMarkSpec_zero_inv hcore hsi.mrk_len hsi.mstk_len hsi.mclr_len hsi.mcl_le hm'
    hv_lt hz_v ((2 : BitVec 32).setWidth 8) fun m4 hm4 => ?_
  have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
  rw [h2_eq] at hm4
  let st_p := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
  let k4 := fullMinMarkCore st_p.core v.toNat 2#8
  have hcore_p := hsi.core hcore
  have hhrsn := frameCov_to_hrsn hcore hcov_sp hlim
  have hno8_v : (st_p.core.mrk[(s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0#8 &&& 8#8) = 0#8 := by
    have h1 : st_p.core.mrk[v.toNat]?.getD 0#8 = 0#8 := hz_v
    rw [← hv_nat, h1]; rfl
  have hmin4 : FullMinMarkInv k4 keepSet := by
    simpa only [k4, hv_nat.symm] using fullMinMarkInv_mark_rem hcore_p hsi.min_inv
      (hstk.bd sp hsp_idxs) (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp hsp_idxs) hi0_lvl)
      hno8_v hhrsn
  obtain ⟨hsi4, hmono_step⟩ := minLitStInv_mark hcore.1.core_ok.cur_vars_le hsi hv_lt hz_v 2#8
    (Or.inl rfl) hmin4
  have hstk4 := minLitStkInv_pop hcore hstk hsp_gt0 hi0_lvl hmono_step
    (by rw [← hv_nat]; dsimp only [k4, fullMinMarkCore]
        rw [List.getElem?_set_self
          (by rw [hsi.mrk_len]; have := hcore.1.core_ok.cur_vars_le; omega),
          Option.getD_some, hz_v]; decide)
    (fun k hk => by
      have hne : (s.core.trl[idxs[k]]?.getD 0#32).toNat / 2 ≠ v.toNat := by
        rw [hv_nat]
        exact minLitStkInv_var_ne hcore hstk (by rw [hstk.len]; omega) hsp_idxs (by omega)
      dsimp only [k4, fullMinMarkCore]
      rw [List.getElem?_set_ne (Ne.symm hne)])
  exact hpost k4 m4 rfl hsi4 hstk4 hm4

private theorem minLitDfs_poison_leaf {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {mstk2 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} {sp idx0 u_idx : Nat} {idxs : List Nat}
    {u_bv : BitVec 32} (hcore : FullOtfsCoreInv c F0 s)
    (hsi : MinLitStInv c s keepSet mrk1 mstk2 mclr1 mcl1 mcf1)
    (hstk : MinLitStkInv s.core mstk2 mrk1 sp idx0 idxs false)
    (hsp_idxs : sp < idxs.length)
    (hu_bd : u_idx < idxs[sp]'hsp_idxs)
    (hu_nat : u_bv.toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
    (hu_lt : u_bv.toNat < s.core.cur_vars)
    (hno8_u : (mrk1[u_bv.toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (h2z : (mrk1[u_bv.toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (h4z : (mrk1[u_bv.toNat]?.getD 0#8 &&& 4#8) = 0#8)
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hm' : (FullMem c (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) ⋆ R) m')
    {Q' : Post []} {X' : XPost}
    (hpost : ∀ mrk4 mclr4 mcl4 mcf4 m4,
      MinLitStInv c s keepSet mrk4 mstk2 mclr4 mcl4 mcf4 →
      (FullMem c (minLitState s mrk4 mstk2 mclr4 mcl4 mcf4) ⋆ R) m4 →
      MinLitStkInv s.core mstk2 mrk4 sp idx0 idxs false → Q' () m4) :
    fullMinMarkSpec (c.hdr, u_bv, (4 : BitVec 32).setWidth 8, ()) m' Q' X' := by
  have hdom := hsi.min_inv.mrk_dom u_bv.toNat hu_lt
  have hmu0 : mrk1[u_bv.toNat]?.getD 0#8 = 0#8 := bv8_zero_of_masks24 _ hdom hno8_u h2z h4z
  refine fullMinMarkSpec_zero_inv hcore hsi.mrk_len hsi.mstk_len hsi.mclr_len hsi.mcl_le hm'
    hu_lt hmu0 ((4 : BitVec 32).setWidth 8) fun m4 hm4 => ?_
  have h4_eq : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
  rw [h4_eq] at hm4
  let st_p := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1
  let k4 := fullMinMarkCore st_p.core u_bv.toNat 4#8
  have hcore_p := hsi.core hcore
  have hmin4 : FullMinMarkInv k4 keepSet :=
    fullMinMarkInv_poison hcore_p hsi.min_inv hu_lt
      (by change (mrk1[u_bv.toNat]?.getD 0#8 &&& 8#8) = 0#8; rw [hmu0]; rfl)
  obtain ⟨hsi4, _⟩ := minLitStInv_mark hcore.1.core_ok.cur_vars_le hsi hu_lt hmu0 4#8
    (Or.inr rfl) hmin4
  have hstk4 := minLitStkInv_poison_other hcore hstk (u_idx := u_idx) (mclr1 := mclr1)
    (mcl1 := mcl1) (mcf1 := mcf1)
    (fun k hk => by
      by_cases hksp : k = sp
      · subst hksp; exact hu_bd
      · exact Nat.lt_trans hu_bd (dec_chain_lt hstk.dec (by have := hstk.len; omega) hk hsp_idxs))
    (fun w _ hne => by dsimp only [fullMinMarkCore]; rw [List.getElem?_set_ne (Ne.symm hne)])
  rw [← hu_nat] at hstk4
  exact hpost k4.mrk k4.min_clr k4.min_clr_len k4.min_clr_full m4 hsi4 hm4 hstk4

/-! ## 4. Shared Child-Check & Init State Helpers for `full_min_lit_dfs_m6` -/

private theorem minLitDfs_ok_res {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {mrk1 : List (BitVec 8)} {mstk1 : List (BitVec 32)}
    {sp idx0 u_idx : Nat} {idxs : List Nat}
    {mstk2 : List (BitVec 32)} {lit par_pw : BitVec 32} {pos : BitVec 32}
    (hcore : FullOtfsCoreInv c F0 s) (hstk : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs true)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hmstk_len : mstk1.length = 2 * c.minDepth) (hsp : sp < c.minDepth)
    (hsp_idxs : sp < idxs.length)
    (hmstk2 : mstk2 = mstk1.set (2 * sp + 1) par_pw)
    (hpos_nat : pos.toNat = (mstk1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hpar_eq : (par_pw &&& 0x7FFFFFFF#32).toNat =
      (mstk1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
      else fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hcov_sp : FrameCov s.core mrk1 idxs[sp] pos.toNat)
    (hlit_eq : lit.toNat = minLitRsnLit s.core
      (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
      pos.toNat)
    (hstep :
      lit.toNat / 2 = (s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2 ∨
      (u_idx < idxs[sp]'hsp_idxs ∧ (s.core.trl[u_idx]?.getD 0#32).toNat = lit.toNat ^^^ 1 ∧
        ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0 ∨
          (mrk1[lit.toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8))) :
    MinLitStkInv s.core mstk2 mrk1 sp idx0 idxs true := by
  subst hmstk2
  refine minLitStkInv_step_top (c := c) hstk hmstk_len hsp par_pw fun _ => ?_
  rw [hpar_eq, ← hpos_nat]
  refine frameCov_step hcore (hstk.bd sp hsp_idxs)
    (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp hsp_idxs) hi0_lvl) hcov_sp hsz_lt ?_
  dsimp only; rw [← hlit_eq]
  rcases hstep with heq | ⟨hj, hjeq, hdep⟩
  · exact Or.inl heq
  · exact Or.inr ⟨u_idx, hj, hjeq, hdep⟩

/-! ## 5. `full_min_lit_dfs_m6`, `full_min_lit_m6`, and `full_shrink_lower_m6` `Func.wp` proofs -/

private abbrev minLitMaxSteps (s : FullState) : Nat :=
  (s.core.arena_len + s.core.cur_vars) * 4 + 64

private abbrev MinLitBrkPost (c : FullCfg) (s : FullState) (keepSet : List Nat)
    (root_lit : Val i32) (idx0 : Nat) (R : Mem 64 → Prop) :
    Tup Val [i64, i64, .bool, i64] → Mem 64 → Prop :=
  fun (sp, _cd, ok, _steps, ()) m' =>
    ∃ mrk1 mstk1 mclr1 mcl1 mcf1,
      let st := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
      MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1 ∧
      (FullMem c st ⋆ R) m' ∧
      if ok then
        ∃ idx0_w < s.core.trail_end,
          (s.core.trl[idx0_w]?.getD 0#32).toNat = root_lit.toNat ^^^ 1 ∧
          ∃ lim,
            (if (s.core.rsns[(s.core.trl[idx0_w]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
             else fullArenaClauseSizeCore s.core
               (s.core.rsns[(s.core.trl[idx0_w]?.getD 0#32).toNat / 2]?.getD
                 0xFFFFFFFF#32).toNat) ≤ lim ∧
            FrameCov s.core mrk1 idx0_w lim
      else
        sp.toNat < c.minDepth ∧
        ∃ idxs, MinLitStkInv s.core mstk1 mrk1 sp.toNat idx0 idxs false

private abbrev MinLitLpInv (c : FullCfg) (s : FullState) (keepSet : List Nat) (idx0 : Nat)
    (R : Mem 64 → Prop) : Nat → Tup Val [i64, i64, i64] → Mem 64 → Prop :=
  fun n (sp, _cd, steps, ()) m' =>
    sp.toNat < c.minDepth ∧ steps.toNat ≤ minLitMaxSteps s ∧
    n = minLitMaxSteps s - steps.toNat ∧
    ∃ mrk1 mstk1 mclr1 mcl1 mcf1 idxs,
      let st := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
      MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1 ∧
      (FullMem c st ⋆ R) m' ∧
      MinLitStkInv s.core mstk1 mrk1 sp.toNat idx0 idxs true

private def minLitDfsBrkExpr (h pMinStk : Val i64)
    (r : Tup Val [i64, i64, .bool, i64]) : Expr Val Cont [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
  .jnz (.var r.snd.snd.fst) (.ret (.imm true, ()))
    (.group (sig := [[i64]]) (fun Js => .cons (fun p32 =>
      .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var p32.fst, .var r.fst, ())) fun p33 =>
      .jnz (.var p33.fst)
        (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p34 =>
         .let_ (op64 (.shl i64) (.var p32.fst) (.var p34.fst)) fun p35 =>
         .let_ (op64 (.mul i64) (.var p35.fst) (.imm 4)) fun p36 =>
         .let_ (op64 (.add i64) (.var pMinStk) (.var p36.fst)) fun p37 =>
         .load i32 (.var p37.fst) fun ld =>
         .let_ (Op.mk (.trunc 32 8) (.imm 4, ())) fun p38 =>
         .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
           (.var h, .var ld, .var p38.fst, ()) fun _ =>
         .let_ (op64 (.add i64) (.var p32.fst) (.imm 1)) fun p =>
         .jump Js.fst (.var p.fst, ()))
        (.ret (.imm false, ()))) .nil)
      (fun Js => .jump Js.fst (.imm 1, ())))

private theorem minLitDfs_brk_wp {Γ : Env}
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {keepSet : List Nat}
    {root_lit : Val i32} {idx0 : Nat} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s)
    (hrl_lvl : (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hQ : ∀ ok mrk' mstk' mclr' mcl' mcf' m',
      let s' := minLitState s mrk' mstk' mclr' mcl' mcf'
      s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars,
        (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv s'.core keepSet →
      (ok = true →
        (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
          FullMinMarkInv s'.core keep') ∧
        FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    {r : Tup Val [i64, i64, .bool, i64]} {m' : Mem 64}
    (hBrk : MinLitBrkPost c s keepSet root_lit idx0 R r m') :
    wp Γ Q X (minLitDfsBrkExpr c.hdr c.pMinStk r) m' := by
  rcases r with ⟨sp, cd, ok, steps, ⟨⟩⟩
  rcases hBrk with ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hsi, hm', hrest⟩
  dsimp only [minLitDfsBrkExpr]
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨F_cur0, hw0⟩ := hcore.2
  ml_lets; ml_jnz; refine ⟨fun hok => ?_, fun hnok => ?_⟩
  · ml_lets; rw [wp]
    rw [hok] at hrest; simp only [↓reduceIte] at hrest
    obtain ⟨idx0_w, hi0_w, hroot_w, lim, hlim_w, hcov_w⟩ := hrest
    exact minLitDfs_ok_post hcore hrl_lvl hno8 hsi hm' hi0_w hroot_w hlim_w hcov_w hQ
  · rw [hnok] at hrest; simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    obtain ⟨hsp_lt, idxs, hstk⟩ := hrest
    ml_lets
    let AfterInv : Nat → Tup Val [i64] → Mem 64 → Prop :=
      fun n' (j, ()) m2 =>
        1 ≤ j.toNat ∧ j.toNat ≤ sp.toNat + 1 ∧ n' = sp.toNat + 1 - j.toNat ∧
        ∃ mrk2 mclr2 mcl2 mcf2,
          let st2 := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2
          MinLitStInv c s keepSet mrk2 mstk1 mclr2 mcl2 mcf2 ∧
          (FullMem c st2 ⋆ R) m2 ∧
          ∀ k (hk : k < idxs.length), j.toNat ≤ k →
            mrk2[(s.core.trl[idxs[k]]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
    refine wp_loop_group (ts := [i64]) AfterInv ?_ ?_
    · rintro J n' ⟨j, ⟨⟩⟩ m2 hJ ⟨hj1, hj_le, rfl,
        mrk2, mclr2, mcl2, mcf2, hsi2, hm2, hzero2⟩
      rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hj_ule => ?_, fun _ => ?_⟩
      · have hj_le_sp : j.toNat ≤ sp.toNat := by c0_cond hj_ule; bv_omega
        have hj_idxs : j.toNat < idxs.length := by rw [hstk.len]; omega
        have hmd_le : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
        have hj_stk : (j <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
            mstk1.length := by rw [bv64_shl1_toNat (by omega), hsi2.mstk_len]; omega
        ml_ld c0_load_full_min_stk (s := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2)
          (i := j <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) hj_stk hm2
        ml_lets
        let v_bv := mstk1[(j <<<
          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat]'hj_stk
        have hv_nat : v_bv.toNat =
            (s.core.trl[idxs[j.toNat]'hj_idxs]?.getD 0#32).toNat / 2 := by
          have hsh := bv64_shl1_toNat (x := j) (by omega)
          have hslot := (hstk.slot j.toNat hj_idxs).1
          rw [List.getElem?_eq_getElem (by rw [hsi2.mstk_len]; omega), Option.getD_some] at hslot
          dsimp only [v_bv]; simp only [hsh]; exact hslot
        have hv_lt : v_bv.toNat < s.core.cur_vars := by
          rw [hv_nat]; have := hw0.trail_lits_lt _ (hstk.bd j.toNat hj_idxs); omega
        have hz_bv : mrk2[v_bv.toNat]?.getD 0#8 = 0#8 := by
          rw [hv_nat]; exact hzero2 j.toNat hj_idxs (le_refl _)
        apply wp_call_of_spec; apply hMm
        refine fullMinMarkSpec_zero_inv hcore hsi2.mrk_len hsi2.mstk_len hsi2.mclr_len
          hsi2.mcl_le hm2 hv_lt hz_bv ((4 : BitVec 32).setWidth 8) fun m3 hm3 => ?_
        ml_lets; rw [wp]
        let st2 := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2
        let k3 := fullMinMarkCore st2.core v_bv.toNat 4#8
        have h4_eq : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
        rw [h4_eq] at hm3
        have hcore2 := hsi2.core hcore
        have hno8_v : (st2.core.mrk[v_bv.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
          have hz2 : st2.core.mrk[v_bv.toNat]?.getD 0#8 = 0#8 := hz_bv
          rw [hz2]; rfl
        have hmin3 := fullMinMarkInv_poison hcore2 hsi2.min_inv hv_lt hno8_v
        obtain ⟨hsi3, _⟩ := minLitStInv_mark hcv hsi2 hv_lt hz_bv 4#8 (Or.inr rfl) hmin3
        have hj1_nat : (j + 1).toNat = j.toNat + 1 := min_bv64_add1 (by omega)
        refine hJ (sp.toNat + 1 - (j + 1).toNat) (j + 1, ()) m3 (by omega)
          ⟨by omega, by omega, rfl,
            k3.mrk, k3.min_clr, k3.min_clr_len, k3.min_clr_full,
            hsi3, hm3, fun k hk hjk => ?_⟩
        have hne_k : (s.core.trl[idxs[k]]?.getD 0#32).toNat / 2 ≠ v_bv.toNat := by
          rw [hv_nat]; exact minLitStkInv_var_ne hcore hstk hk hj_idxs (by omega)
        dsimp only [k3, fullMinMarkCore]
        rw [List.getElem?_set_ne (Ne.symm hne_k)]
        exact hzero2 k hk (by omega)
      · ml_lets; rw [wp]
        have hcore2 := hsi2.core hcore
        exact hQ false mrk2 mstk1 mclr2 mcl2 mcf2 m2 hcore2.1 hsi2.mrk_above
          hsi2.mono2 hsi2.bit8 hsi2.min_inv (fun hc => by cases hc) hm2
    · intro J hJ; wp_unfold
      exact hJ sp.toNat (1#64, ()) m' ⟨le_refl _, Nat.succ_le_of_lt (by omega), rfl,
        mrk1, mclr1, mcl1, mcf1, hsi, hm', fun k hk hk1 => (hstk.slot k hk).2 hk1⟩

private def minLitDfsBigExpr
    (h cvVal pReason pMark pLevel pArena pMinStk pShrinkStk sp cd steps1 : Val i64)
    (checkUsed : Val .bool) (v pword pos rsn : Val i32)
    (B : Cont [i64, i64, .bool, i64]) (L : Cont [i64, i64, i64]) : Expr Val Cont [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
  let op32 (c : OpCode [i32, i32] [i32]) (a b : Arg Val i32) : Op Val [i32] :=
    Op.mk c (a, b, ())
  .let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun p52 =>
  .let_ (op64 (.add i64) (.var p52.fst) (.imm 3)) fun p53 =>
  .let_ (op64 (.add i64) (.var h) (.imm 48)) fun p54 =>
  .load i64 (.var p54.fst) fun ld14 =>
  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var p53.fst, .var ld14, ())) fun p55 =>
  .jnz (.var p55.fst) (.jump B (.var sp, .var cd, .imm false, .var steps1, ()))
    (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun p56 =>
     .let_ (op64 (.add i64) (.var p56.fst) (.imm 2)) fun p57 =>
     .let_ (op64 (.mul i64) (.var p57.fst) (.imm 4)) fun p58 =>
     .let_ (op64 (.add i64) (.var pArena) (.var p58.fst)) fun p59 =>
     .load i32 (.var p59.fst) fun ld15 =>
     .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var ld15, .imm 3, ())) fun p60 =>
     .jnz (.var p60.fst) (.jump B (.var sp, .var cd, .imm false, .var steps1, ()))
       (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun p61 =>
        .let_ (op64 (.add i64) (.var p61.fst) (.imm 3)) fun p62 =>
        .let_ (Op.mk (.zext 32 64) (.var ld15, ())) fun p63 =>
        .let_ (op64 (.add i64) (.var p62.fst) (.var p63.fst)) fun p64 =>
        .let_ (op64 (.add i64) (.var h) (.imm 48)) fun p65 =>
        .load i64 (.var p65.fst) fun ld16 =>
        .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var p64.fst, .var ld16, ())) fun p66 =>
        .jnz (.var p66.fst) (.jump B (.var sp, .var cd, .imm false, .var steps1, ()))
          (.let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var pos, .var ld15, ())) fun p67 =>
           .jnz (.var p67.fst)
             (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p68 =>
              .let_ (op64 (.shl i64) (.var sp) (.var p68.fst)) fun p69 =>
              .let_ (op64 (.add i64) (.var p69.fst) (.imm 1)) fun p70 =>
              .let_ (op64 (.mul i64) (.var p70.fst) (.imm 4)) fun p71 =>
              .let_ (op64 (.add i64) (.var pMinStk) (.var p71.fst)) fun p72 =>
              .let_ (op32 (.and i32) (.var pword) (.imm 2147483648)) fun p73 =>
              .let_ (op32 (.add i32) (.var pos) (.imm 1)) fun p74 =>
              .let_ (op32 (.or i32) (.var p73.fst) (.var p74.fst)) fun p75 =>
              .store (.var p75.fst) (.var p72.fst)
                (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun p76 =>
                 .let_ (op64 (.add i64) (.var p76.fst) (.imm 3)) fun p77 =>
                 .let_ (Op.mk (.zext 32 64) (.var pos, ())) fun p78 =>
                 .let_ (op64 (.add i64) (.var p77.fst) (.var p78.fst)) fun p79 =>
                 .let_ (op64 (.mul i64) (.var p79.fst) (.imm 4)) fun p80 =>
                 .let_ (op64 (.add i64) (.var pArena) (.var p80.fst)) fun p81 =>
                 .load i32 (.var p81.fst) fun ld17 =>
                 .let_ (op32 (.lshr i32) (.var ld17) (.imm 1)) fun p82 =>
                 .let_ (Op.mk (.zext 32 64) (.var p82.fst, ())) fun p83 =>
                 .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var p83.fst, .var cvVal, ()))
                   fun p84 =>
                 .jnz (.var p84.fst) (.jump B (.var sp, .var cd, .imm false, .var steps1, ()))
                   (.let_ (Op.mk (.zext 32 64) (.var p82.fst, ())) fun p85 =>
                    .let_ (op64 (.mul i64) (.var p85.fst) (.imm 4)) fun p86 =>
                    .let_ (op64 (.add i64) (.var pLevel) (.var p86.fst)) fun p87 =>
                    .load i32 (.var p87.fst) fun ld18 =>
                    .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var p82.fst, .var v, ()))
                      fun p88 =>
                    .jnz (.var p88.fst) (.jump L (.var sp, .var cd, .var steps1, ()))
                      (.let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld18, .imm 0, ()))
                         fun p89 =>
                       .jnz (.var p89.fst) (.jump L (.var sp, .var cd, .var steps1, ()))
                         (.let_ (Op.mk (.zext 32 64) (.var p82.fst, ())) fun p90 =>
                          .let_ (op64 (.add i64) (.var pMark) (.var p90.fst)) fun p91 =>
                          .load i8 (.var p91.fst) fun ld19 =>
                          .let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun p92 =>
                          .let_ (Op.mk (.zext 8 32) (.var ld19, ())) fun p93 =>
                          .let_ (Op.mk (.zext 8 32) (.var p92.fst, ())) fun p94 =>
                          .let_ (op32 (.and i32) (.var p93.fst) (.var p94.fst)) fun p95 =>
                          .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p96 =>
                          .let_ (Op.mk (.zext 8 32) (.var p96.fst, ())) fun p97 =>
                          .let_ (Op.mk (.cmp .ne i32 .bool rfl)
                              (.var p95.fst, .var p97.fst, ())) fun p98 =>
                          .jnz (.var p98.fst) (.jump L (.var sp, .var cd, .var steps1, ()))
                            (.let_ (Op.mk (.trunc 32 8) (.imm 4, ())) fun p99 =>
                             .let_ (Op.mk (.zext 8 32) (.var ld19, ())) fun p100 =>
                             .let_ (Op.mk (.zext 8 32) (.var p99.fst, ())) fun p101 =>
                             .let_ (op32 (.and i32) (.var p100.fst) (.var p101.fst)) fun p102 =>
                             .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p103 =>
                             .let_ (Op.mk (.zext 8 32) (.var p103.fst, ())) fun p104 =>
                             .let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                 (.var p102.fst, .var p104.fst, ())) fun p105 =>
                             .jnz (.var p105.fst)
                               (.jump B (.var sp, .var cd, .imm false, .var steps1, ()))
                               (.let_ (Op.mk (.zext 32 64) (.var p82.fst, ())) fun p106 =>
                                .let_ (op64 (.mul i64) (.var p106.fst) (.imm 4)) fun p107 =>
                                .let_ (op64 (.add i64) (.var pReason) (.var p107.fst)) fun p108 =>
                                .load i32 (.var p108.fst) fun ld20 =>
                                .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                                    (.var ld20, .imm 4294967295, ())) fun p109 =>
                                .jnz (.var p109.fst)
                                  (.let_ (Op.mk (.trunc 32 8) (.imm 4, ())) fun p110 =>
                                   .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
                                     (.var h, .var p82.fst, .var p110.fst, ()) fun _ =>
                                   .jump B (.var sp, .var cd, .imm false, .var steps1, ()))
                                  (.group (sig := [[]]) (fun _ => .cons (fun _ =>
                                     .let_ (op64 (.add i64) (.var cd) (.imm 1)) fun p111 =>
                                     .let_ (op64 (.add i64) (.var h) (.imm 264)) fun p112 =>
                                     .load i64 (.var p112.fst) fun ld_d1 =>
                                     .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                                         (.var p111.fst, .var ld_d1, ())) fun p113 =>
                                     .jnz (.var p113.fst)
                                       (.jump B (.var sp, .var cd, .imm false, .var steps1, ()))
                                       (.let_ (op64 (.add i64) (.var sp) (.imm 1)) fun p114 =>
                                        .let_ (op64 (.add i64) (.var h) (.imm 264)) fun p_d2 =>
                                        .load i64 (.var p_d2.fst) fun ld_d2 =>
                                        .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                                            (.var p114.fst, .var ld_d2, ())) fun p_d3 =>
                                        .jnz (.var p_d3.fst)
                                          (.jump B (.var sp, .var cd, .imm false, .var steps1, ()))
                                          (.let_ (op64 (.add i64) (.var cd) (.imm 1)) fun p_cd =>
                                           .let_ (op64 (.add i64) (.var sp) (.imm 1)) fun p115 =>
                                           .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p116 =>
                                           .let_ (op64 (.shl i64) (.var p115.fst) (.var p116.fst))
                                             fun p117 =>
                                           .let_ (op64 (.mul i64) (.var p117.fst) (.imm 4))
                                             fun p118 =>
                                           .let_ (op64 (.add i64) (.var pMinStk) (.var p118.fst))
                                             fun p119 =>
                                           .store (.var p82.fst) (.var p119.fst)
                                             (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p120 =>
                                              .let_ (op64 (.shl i64) (.var p115.fst)
                                                (.var p120.fst)) fun p121 =>
                                              .let_ (op64 (.add i64) (.var p121.fst) (.imm 1))
                                                fun p122 =>
                                              .let_ (op64 (.mul i64) (.var p122.fst) (.imm 4))
                                                fun p123 =>
                                              .let_ (op64 (.add i64) (.var pMinStk)
                                                (.var p123.fst)) fun p124 =>
                                              .store (t := i32) (.imm 2147483648) (.var p124.fst)
                                                (.jump L (.var p115.fst, .var p_cd.fst,
                                                  .var steps1, ())))))) .nil)
                                     fun Js2 => .jnz (.var checkUsed)
                                       (.let_ (Op.mk (.zext 32 64) (.var ld18, ())) fun p110 =>
                                        .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                            (.var p110.fst, .var cvVal, ())) fun p111 =>
                                        .jnz (.var p111.fst)
                                          (.let_ (Op.mk (.zext 32 64) (.var ld18, ())) fun p112 =>
                                           .let_ (op64 (.add i64) (.var h) (.imm 160)) fun p_cl =>
                                           .load i64 (.var p_cl.fst) fun ld_cl =>
                                           .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                               (.var p112.fst, .var ld_cl, ())) fun p_ltcl =>
                                           .jnz (.var p_ltcl.fst)
                                             (.let_ (Op.mk (.zext 32 64) (.var ld18, ())) fun p_u =>
                                              .let_ (op64 (.mul i64) (.var p_u.fst) (.imm 4))
                                                fun p_um =>
                                              .let_ (op64 (.add i64) (.var pShrinkStk)
                                                (.var p_um.fst)) fun p_ua =>
                                              .load i32 (.var p_ua.fst) fun ld_used =>
                                              .let_ (Op.mk (.cmp .ule i32 .bool rfl)
                                                  (.var ld_used, .imm 1, ())) fun p_le1 =>
                                              .jnz (.var p_le1.fst)
                                                (.jump B (.var sp, .var cd, .imm false,
                                                  .var steps1, ()))
                                                (.jump Js2.fst ()))
                                             (.jump Js2.fst ()))
                                          (.jump Js2.fst ()))
                                       (.jump Js2.fst ())))))))))
             (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var sp, .imm 0, ())) fun p68 =>
              .jnz (.var p68.fst) (.jump B (.var sp, .var cd, .imm true, .var steps1, ()))
                (.let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun p69 =>
                 .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
                   (.var h, .var v, .var p69.fst, ()) fun _ =>
                 .group (sig := [[i64]]) (fun _ => .cons (fun p_cd =>
                    .let_ (op64 (.sub i64) (.var sp) (.imm 1)) fun p70 =>
                    .jump L (.var p70.fst, .var p_cd.fst, .var steps1, ())) .nil)
                   fun Js3 =>
                   .let_ (op32 (.and i32) (.var pword) (.imm 2147483648)) fun p_hi =>
                   .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var p_hi.fst, .imm 0, ()))
                     fun p_hnz =>
                   .jnz (.var p_hnz.fst)
                     (.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var cd, .imm 0, ()))
                        fun p_cgt =>
                      .jnz (.var p_cgt.fst)
                        (.let_ (op64 (.sub i64) (.var cd) (.imm 1)) fun p_cm1 =>
                         .jump Js3.fst (.var p_cm1.fst, ()))
                        (.jump Js3.fst (.var cd, ())))
                     (.jump Js3.fst (.var cd, ())))))))

private theorem minLitDfs_big_wp {Γ : Env}
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur0 : List (List Nat)} {s : FullState}
    {keepSet : List Nat} {root_lit : Val i32} {idx0 : Nat} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {B : Cont [i64, i64, .bool, i64]} {L : Cont [i64, i64, i64]}
    {sp cd steps : Val i64} {check_used : Val .bool} {m' : Mem 64}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    {idxs : List Nat} {v pword pos rsn : Val i32}
    (hcore : FullOtfsCoreInv c F0 s) (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hmx : c.max_vars < 2 * 2 ^ 28) (har : c.arena_cap < 2 * 2 ^ 28)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hi0 : idx0 < s.core.trail_end)
    (hi0_eq : (s.core.trl[idx0]?.getD 0#32).toNat = root_lit.toNat ^^^ 1)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hi0_lvl :
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hB : ∀ r m', MinLitBrkPost c s keepSet root_lit idx0 R r m' → B r m')
    (hsp_lt : sp.toNat < c.minDepth) (hsteps_le1 : (steps + 1).toNat ≤ minLitMaxSteps s)
    (hL : ∀ n' ys m', n' < minLitMaxSteps s - steps.toNat →
      MinLitLpInv c s keepSet idx0 R n' ys m' → L ys m')
    (hsi : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    (hm' : (FullMem c (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) ⋆ R) m')
    (hstk : MinLitStkInv s.core mstk1 mrk1 sp.toNat idx0 idxs true)
    (hdec_n : minLitMaxSteps s - (steps + 1).toNat < minLitMaxSteps s - steps.toNat)
    (hmd_le : c.minDepth ≤ 1000)
    (hstk_od : (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
      mstk1.length)
    (hsp_idxs : sp.toNat < idxs.length)
    (hv_nat : v.toNat = (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2)
    (hv_lt : v.toNat < s.core.cur_vars)
    (hpos_nat : pos.toNat = (mstk1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
      0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hcov_sp : FrameCov s.core mrk1 idxs[sp.toNat] pos.toNat)
    (hbig : ((rsn &&& 0x80000000#32) != 0#32) = false) :
    wp Γ Q X (minLitDfsBigExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pReason c.pMark
      c.pLevel c.pArena c.pMinStk c.pShrinkStk sp cd (steps + 1) check_used v pword pos rsn B L)
      m' := by
  dsimp only [minLitDfsBigExpr]
  have hlen0 := hcore.1.core_ok
  have hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := by
    c0_cond hbig; intro hne; exact hne hbig
  have hcov_big := hcov_sp
  dsimp only [FrameCov] at hcov_big
  rcases hcov_big with ⟨_, hif⟩
  simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte] at hif
  have hwf := hw0.arena.refs_wf _ hif.1
  ml_ld load_full_arena_len (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) hm'
  ml_lets; ml_jnz; refine ⟨fun har1 => ?_, fun _ => ?_⟩
  · exfalso; dsimp only [minLitState] at har1
    have hlt1 := bv64_lt_zext32_add3 (by have := hlen0.arena_len_le; omega) rsn har1
    have := hwf.1; omega
  · have har2 : (rsn.setWidth 64 + 2).toNat <
        (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core.arena.length := by
      rw [bv64_zext32_add2]
      have := hwf.1; have := hlen0.arena_len_le; have := hlen0.arena_len_arr
      dsimp only [minLitState]; omega
    ml_ld c0_load_full_arena (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
      (i := rsn.setWidth 64 + 2) har2 hm'
    let sz := s.core.arena[(rsn.setWidth 64 + 2).toNat]'har2
    have hsz_e : sz.toNat = fullArenaClauseSizeCore s.core rsn.toNat := by
      have hopt : s.core.arena[(rsn.setWidth 64 + 2).toNat]? =
          s.core.arena[rsn.toNat + 2]? := by rw [bv64_zext32_add2]
      rw [List.getElem?_eq_getElem har2] at hopt
      exact congrArg (fun o => (o.getD 0#32).toNat) hopt
    ml_lets; ml_jnz; refine ⟨fun hsz3 => ?_, fun _ => ?_⟩
    · exfalso; rw [BitVec.ult, decide_eq_true_eq] at hsz3
      have h3 : (3 : BitVec 32).toNat = 3 := rfl
      rw [h3, hsz_e] at hsz3; have := hwf.2.1; omega
    · ml_ld load_full_arena_len (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) hm'
      ml_lets; ml_jnz; refine ⟨fun har_oob => ?_, fun _ => ?_⟩
      · exfalso; dsimp only [minLitState] at har_oob
        have hlt2 := bv64_lt_zext32_add3_add (by have := hlen0.arena_len_le; omega) rsn sz har_oob
        have := hwf.2.2.1; have := hwf.2.2.2.1; rw [hsz_e] at hlt2; omega
      · ml_lets; ml_jnz; refine ⟨fun hpos_lt => ?_, fun hpos_ge => ?_⟩
        · have hpos_lt' : pos.toNat < sz.toNat := by
            change pos.ult sz = true at hpos_lt
            rw [BitVec.ult, decide_eq_true_eq] at hpos_lt; exact hpos_lt
          have hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
              0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
            else fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'
              hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
            simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e]; exact hpos_lt'
          have hpos_add1_lt : (pos + 1#32).toNat < 2 ^ 31 := by
            have := hwf.2.2.1; have := hlen0.arena_len_le; have := c.harena
            unfold dimacsBound at *; rw [hsz_e] at hpos_lt'
            have hp1 : pos.toNat + 1 < 2 ^ 31 := by omega
            rw [BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : pos.toNat + 1 < 2 ^ 32)]
            exact hp1
          have hpos_add1 : (pos + 1#32).toNat = pos.toNat + 1 := by
            have := hwf.2.2.1; have := hlen0.arena_len_le; have := c.harena
            unfold dimacsBound at *; rw [hsz_e] at hpos_lt'
            rw [BitVec.toNat_add, BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt (by omega)
          let par_pw := (pword &&& 0x80000000#32) ||| (pos + 1#32)
          have hpar_eq : (par_pw &&& 0x7FFFFFFF#32).toNat =
              (mstk1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1 := by
            rw [← hpos_nat, bv32_mask31_hi_or hpos_add1_lt, hpos_add1]
          ml_st m_p, hm_p_raw := store_minLit_stk (s := s) (mrk := mrk1)
            (mstk := mstk1) (mclr := mclr1) (mcl := mcl1) (mcf := mcf1)
            (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
            par_pw hstk_od hm'
          rw [bv64_shl1_add1_toNat (x := sp) (by omega)] at hm_p_raw
          obtain ⟨mstk2, hmstk2_eq, hm_p'⟩ :
              ∃ mstk2, mstk2 = mstk1.set (2 * sp.toNat + 1) par_pw ∧
                (FullMem c (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) ⋆ R) m_p :=
            ⟨_, rfl, hm_p_raw⟩
          have hmstk2_len : mstk2.length = 2 * c.minDepth := by
            rw [hmstk2_eq, List.length_set, hsi.mstk_len]
          have hsi_p := minLitStInv_with_mstk hsi hmstk2_len
          have hstk2_drop : MinLitStkInv s.core mstk2 mrk1 sp.toNat idx0 idxs false := by
            refine ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root,
              fun j hj => ?_, fun hc => by cases hc⟩
            rw [hmstk2_eq, List.getElem?_set_ne (by omega)]; exact hstk.slot j hj
          have har_bd : (rsn.setWidth 64 + 3 + pos.setWidth 64).toNat <
              (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.arena.length := by
            have hbd := frameCov_arena_lits_bd hcore hif.1
            rw [bv64_zext32_add3_add]; dsimp only [minLitState]
            rw [hsz_e] at hpos_lt'; omega
          ml_ld c0_load_full_arena (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
            (i := rsn.setWidth 64 + 3 + pos.setWidth 64) har_bd hm_p'
          generalize hlit_def : (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.arena[(rsn.setWidth
            64 + 3 + pos.setWidth 64).toNat]'har_bd = lit
          have hlit_eq : lit.toNat = minLitRsnLit s.core rsn pos.toNat := by
            have har_bd' : rsn.toNat + 3 + pos.toNat < s.core.arena.length := by
              rw [← bv64_zext32_add3_add]; exact har_bd
            rw [← hlit_def]; dsimp only [minLitRsnLit, minLitState]
            simp only [eq_false hbin_f, ↓reduceIte, bv64_zext32_add3_add]
            rw [List.getElem?_eq_getElem har_bd', Option.getD_some]
          ml_lets; ml_jnz; refine ⟨fun hu_ge => ?_, fun hu_lt_cv => ?_⟩
          · exfalso
            change (BitVec.ofNat 64 s.core.cur_vars).ule ((lit >>> 1).setWidth 64) = true at hu_ge
            c0_cond hu_ge
            have hu_lt_2v : lit.toNat < 2 * s.core.cur_vars := by
              by_cases heq_var : lit.toNat / 2 =
                  (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2
              · have hl1 := hw0.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
              · have hfc := frameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
                    (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
                    hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
                rw [← hrsn_eq, ← hlit_eq] at hfc; exact hfc.1
            have := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at *; omega
          · have hu_cv : (lit >>> 1).toNat < s.core.cur_vars := by
              change (BitVec.ofNat 64 s.core.cur_vars).ule ((lit >>> 1).setWidth 64) = false
                at hu_lt_cv
              c0_cond hu_lt_cv
              have := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at *; omega
            have hu_lvl_len : ((lit >>> 1).setWidth 64).toNat <
                (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.lvl.length := by
              dsimp only [minLitState]; rw [hlen0.lvl_len, bv_c0_zext32_64]; omega
            ml_ld c0_load_full_lvl (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
              (i := (lit >>> 1).setWidth 64) hu_lvl_len hm_p'
            let ul := s.core.lvl[((lit >>> 1).setWidth 64).toNat]'hu_lvl_len
            ml_lets; ml_jnz; refine ⟨fun heq_uv => ?_, fun hne_uv => ?_⟩
            · change ((lit >>> 1) == v) = true at heq_uv
              c0_cond heq_uv
              have heq_var : lit.toNat / 2 =
                  (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                rw [← hv_nat, ← bv32_lshr_1, heq_uv]
              refine hL (minLitMaxSteps s - (steps + 1).toNat)
                (sp, cd, steps + 1, ()) _ hdec_n
                ⟨hsp_lt, hsteps_le1, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                  hsi_p, hm_p', minLitDfs_ok_res hcore hstk hi0_lvl hsi.mstk_len
                    hsp_lt hsp_idxs hmstk2_eq hpos_nat hpar_eq hsz_lt hcov_sp
                    (by rwa [← hrsn_eq]) (u_idx := 0) (Or.inl heq_var)⟩
            · have hu_neq : lit.toNat / 2 ≠
                  (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                change ((lit >>> 1) == v) = false at hne_uv
                c0_cond hne_uv; rw [← hv_nat]; intro heq; apply hne_uv
                apply BitVec.eq_of_toNat_eq; simpa only [bv32_lshr_1] using heq
              have hfc := frameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
                (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
                hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
              rw [← hrsn_eq, ← hlit_eq] at hfc
              obtain ⟨hu_lt2, u_idx, hu_idx_lt, hu_idx_eq, hu_lvl_le⟩ := hfc
              have hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars := by
                rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hu_lt2
              ml_lets; ml_jnz; refine ⟨fun hlvl0 => ?_, fun _ => ?_⟩
              · c0_cond hlvl0
                have hlw : lit.toNat / 2 < s.core.lvl.length := by
                  rw [hlen0.lvl_len, ← bv32_lshr_1]; omega
                refine hL (minLitMaxSteps s - (steps + 1).toNat)
                  (sp, cd, steps + 1, ()) _ hdec_n
                  ⟨hsp_lt, hsteps_le1, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                    hsi_p, hm_p', minLitDfs_ok_res hcore hstk hi0_lvl hsi.mstk_len
                      hsp_lt hsp_idxs hmstk2_eq hpos_nat hpar_eq hsz_lt hcov_sp
                      (by rwa [← hrsn_eq]) (u_idx := u_idx) (Or.inr ⟨hu_idx_lt, hu_idx_eq,
                        Or.inl (by
                          rw [List.getElem?_eq_getElem hlw, Option.getD_some, hlvl0]; rfl)⟩)⟩
              · have hu_mrk_len : ((lit >>> 1).setWidth 64).toNat <
                    (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.mrk.length := by
                  dsimp only [minLitState]; rw [hsi.mrk_len, bv_c0_zext32_64, bv32_lshr_1]; omega
                ml_ld c0_load_full_mrk (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                  (i := (lit >>> 1).setWidth 64) hu_mrk_len hm_p'
                let mu := mrk1[((lit >>> 1).setWidth 64).toNat]'hu_mrk_len
                have hmu_eq : mu = mrk1[(lit >>> 1).toNat]?.getD 0#8 := by
                  have hvw := bv_c0_zext32_64 (lit >>> 1)
                  dsimp only [mu]
                  rw [List.getElem?_eq_getElem (by rw [hsi.mrk_len]; omega), Option.getD_some]
                  congr 1
                ml_lets; ml_jnz; refine ⟨fun hmu2 => ?_, fun hmu_n2 => ?_⟩
                · have hmu_is2 : (mu &&& 2#8) ≠ 0#8 := bv8_c0_bit_ne0 hmu2
                  refine hL (minLitMaxSteps s - (steps + 1).toNat)
                    (sp, cd, steps + 1, ()) _ hdec_n
                    ⟨hsp_lt, hsteps_le1, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                      hsi_p, hm_p', minLitDfs_ok_res hcore hstk hi0_lvl hsi.mstk_len hsp_lt
                        hsp_idxs hmstk2_eq hpos_nat hpar_eq hsz_lt hcov_sp (by rwa [← hrsn_eq])
                        (u_idx := u_idx) (Or.inr ⟨hu_idx_lt, hu_idx_eq, Or.inr (by
                          rw [← bv32_lshr_1, ← hmu_eq]; exact hmu_is2)⟩)⟩
                · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hmu_n4 => ?_⟩
                  · ml_lets; apply hB
                    exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p', ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                  · have hu_nat_idx : (lit >>> 1).toNat =
                        (s.core.trl[u_idx]?.getD 0#32).toNat / 2 := by
                      have hl := litVar_litNeg lit.toNat
                      unfold litVar litNeg at hl; rw [bv32_lshr_1, ← hl, ← hu_idx_eq]
                    have hu_lvl_root : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD
                          0#32).toNat ≤
                        (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                      have h1 : (s.core.trl[u_idx]?.getD 0#32).toNat / 2 = lit.toNat / 2 := by
                        rw [← hu_nat_idx, bv32_lshr_1]
                      rw [h1]; exact Nat.le_trans hu_lvl_le (hstk.lvl_le_root sp.toNat hsp_idxs)
                    have hno8_u : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
                      rw [hsi.bit8 _ hu_bd_lt]; refine hno8 _ hu_bd_lt ?_
                      rw [hu_nat_idx, ← hrv_root]; exact hu_lvl_root
                    have hu_rsns_len : ((lit >>> 1).setWidth 64).toNat <
                        (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.rsns.length := by
                      dsimp only [minLitState]; rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]
                      omega
                    ml_ld c0_load_full_rsns (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                      (i := (lit >>> 1).setWidth 64) hu_rsns_len hm_p'
                    ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hur_some => ?_⟩
                    · ml_lets; apply wp_call_of_spec; apply hMm
                      refine minLitDfs_poison_leaf hcore hsi_p hstk2_drop hsp_idxs hu_idx_lt
                        hu_nat_idx hu_bd_lt (u_bv := lit >>> 1) hno8_u
                        (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n2)
                        (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n4) hm_p'
                        fun mrk4 mclr4 mcl4 mcf4 m4 hsi4 hm4 hstk4 => by
                          ml_lets; apply hB
                          exact ⟨mrk4, mstk2, mclr4, mcl4, mcf4, hsi4, hm4, ⟨hsp_lt, idxs, hstk4⟩⟩
                    · refine wp_join_group (ts := []) (fun _ m_cu => m_cu = m_p) ?_ ?_
                      · rintro _ ⟨⟩ m_cu rfl; rw [Blocks.get_here]
                        ml_ld load_full_min_depth (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                          hm_p'
                        ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hcd_lt => ?_⟩
                        · ml_lets; apply hB
                          exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p',
                            ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                        · ml_ld load_full_min_depth
                            (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) hm_p'
                          ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hsp_ok => ?_⟩
                          · ml_lets; apply hB
                            exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p',
                              ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                          · c0_cond hsp_ok
                            have hsp1_nat : (sp + 1).toNat = sp.toNat + 1 :=
                              min_bv64_add1 (by omega)
                            have hsp1_lt : sp.toNat + 1 < c.minDepth := by
                              have h1 : (1 : BitVec 64).toNat = 1 := rfl
                              rw [h1, Nat.mod_eq_of_lt (by omega),
                                Nat.mod_eq_of_lt (by omega)] at hsp_ok
                              omega
                            have hstk_ev1 : ((sp + 1) <<<
                                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                                mstk2.length := by
                              rw [bv64_shl1_toNat (x := sp + 1) (by omega), hmstk2_len]; omega
                            have hstk_od1 : ((sp + 1) <<<
                                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
                                mstk2.length := by
                              rw [bv64_shl1_add1_toNat (x := sp + 1) (by omega), hmstk2_len]; omega
                            ml_st m_u, hm_u' := store_minLit_stk (s := s) (mrk := mrk1)
                              (mstk := mstk2) (mclr := mclr1) (mcl := mcl1) (mcf := mcf1)
                              (i := (sp + 1) <<<
                                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))
                              (lit >>> 1) hstk_ev1 hm_p'
                            let mstk_mid := mstk2.set (2 * (sp.toNat + 1)) (lit >>> 1)
                            rw [bv64_shl1_toNat (x := sp + 1) (by omega), hsp1_nat] at hm_u'
                            have hmstk_mid_len : mstk_mid.length = 2 * c.minDepth := by
                              simp [mstk_mid, hmstk2_len]
                            ml_st m_z, hm_z' := store_minLit_stk (s := s) (mrk := mrk1)
                              (mstk := mstk_mid) (mclr := mclr1) (mcl := mcl1) (mcf := mcf1)
                              (i := (sp + 1) <<<
                                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                              (0x80000000#32 : BitVec 32)
                              (by rw [hmstk_mid_len, ← hmstk2_len]; exact hstk_od1) hm_u'
                            ml_lets
                            let mstk3 := ((mstk1.set (2 * sp.toNat + 1) par_pw).set
                              (2 * (sp.toNat + 1)) (lit >>> 1)).set (2 * (sp.toNat + 1) + 1)
                              0x80000000#32
                            have hmstk3_len : mstk3.length = 2 * c.minDepth := by
                              simp [mstk3, hsi.mstk_len]
                            rw [bv64_shl1_add1_toNat (x := sp + 1) (by omega), hsp1_nat] at hm_z'
                            have hm_z'' : (FullMem c (minLitState s mrk1 mstk3 mclr1 mcl1 mcf1) ⋆
                                R) m_z := by
                              simpa only [mstk3, mstk_mid, hmstk2_eq] using hm_z'
                            have hrsn_u_ne : s.core.rsns[(lit >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠
                                0xFFFFFFFF#32 := by
                              have hvw := bv_c0_zext32_64 (lit >>> 1)
                              have hrlu : ((lit >>> 1).setWidth 64).toNat < s.core.rsns.length := by
                                rw [hlen0.rsns_len, hvw]; omega
                              rw [← hvw, List.getElem?_eq_getElem hrlu, Option.getD_some]
                              dsimp only [minLitState] at hur_some
                              intro heq
                              have ht : (s.core.rsns[((lit >>> 1).setWidth 64).toNat] ==
                                  (4294967295 : BitVec 32)) = true := beq_iff_eq.mpr heq
                              rw [ht] at hur_some; cases hur_some
                            have hz_u : mrk1[(lit >>> 1).toNat]?.getD 0#8 = 0#8 := by
                              have hdom := hsi.min_inv.mrk_dom (lit >>> 1).toNat hu_bd_lt
                              have h2z := bv8_c0_bit_eq0 hmu_n2
                              have h4z := bv8_c0_bit_eq0 hmu_n4
                              rw [← hmu_eq] at hdom hno8_u
                              have hmu0 := bv8_zero_of_masks24 _ hdom hno8_u h2z h4z
                              rw [← hmu_eq]; exact hmu0
                            have hstk3 := minLitStkInv_push hcore hstk hi0_lvl hsi.mstk_len hsp1_lt
                              (u_bv := lit >>> 1) (par_pw := par_pw) (ch_pw := 0x80000000#32)
                              hpar_eq bv32_mask31_hi_eq0 hu_idx_lt hu_nat_idx hu_lvl_root
                              (by rwa [← hpos_nat]) hz_u hrsn_u_ne
                              ⟨hu_idx_lt, by rw [← hpos_nat, ← hrsn_eq, ← hlit_eq]; exact hu_idx_eq⟩
                            exact hL (minLitMaxSteps s - (steps + 1).toNat)
                              (sp + 1, cd + 1, steps + 1, ()) m_z hdec_n
                              ⟨by rw [hsp1_nat]; exact hsp1_lt, hsteps_le1, rfl, mrk1, mstk3, mclr1,
                                mcl1, mcf1, idxs ++ [u_idx], minLitStInv_with_mstk hsi hmstk3_len,
                                hm_z'', by rwa [hsp1_nat]⟩
                      · rintro Jcu hJcu; ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                        · ml_lets; ml_jnz; refine ⟨fun hul_cv => ?_, fun _ => ?_⟩
                          · have hul_cv' : ul.toNat < s.core.cur_vars := by
                              c0_cond hul_cv
                              rw [Nat.mod_eq_of_lt (by omega)] at hul_cv
                              dsimp only [ul]
                              simpa only [bv_c0_zext32_64, bv32_lshr_1] using hul_cv
                            ml_ld load_full_cur_level (s := minLitState s mrk1 mstk2 mclr1 mcl1
                              mcf1) hm_p'
                            ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                            · have hul_ss : (ul.setWidth 64).toNat < (minLitState s mrk1 mstk2
                                  mclr1 mcl1 mcf1).scratch.shrink_stk.length := by
                                dsimp only [minLitState]
                                rw [hcore.1.scratch_ok.shrink_stk_len, bv_c0_zext32_64]; omega
                              ml_ld c0_load_full_shrink_stk (s := minLitState s mrk1 mstk2 mclr1
                                mcl1 mcf1) (i := ul.setWidth 64) hul_ss hm_p'
                              ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                              · ml_lets; apply hB
                                exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p',
                                  ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                              · ml_lets; apply hJcu; rfl
                            · ml_lets; apply hJcu; rfl
                          · ml_lets; apply hJcu; rfl
                        · ml_lets; apply hJcu; rfl
        · have hpos_ge' : sz.toNat ≤ pos.toNat := by
            change pos.ult sz = false at hpos_ge
            rw [BitVec.ult, decide_eq_false_iff_not, not_lt] at hpos_ge; exact hpos_ge
          ml_lets; ml_jnz; refine ⟨fun hsp0 => ?_, fun hsp_pos => ?_⟩
          · ml_lets; apply hB; c0_cond hsp0
            have hsp0' : sp.toNat = 0 := congrArg BitVec.toNat hsp0
            have hi0_eq_w : idxs[sp.toNat]'hsp_idxs = idx0 := by
              have he := hstk.idx0_eq
              have hz : idxs[sp.toNat]'hsp_idxs = idxs[0]'(by rw [hstk.len]; omega) := by
                simp only [hsp0']
              rw [hz]; rw [List.getElem?_eq_getElem (by rw [hstk.len]; omega)] at he
              exact Option.some.inj he
            simp only [hi0_eq_w] at hcov_sp hrsn_eq
            exact ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hsi, hm', ⟨idx0, hi0, hi0_eq, pos.toNat,
              by simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e]; exact hpos_ge',
              hcov_sp⟩⟩
          · c0_cond hsp_pos
            have hsp_gt0 : 0 < sp.toNat := bv64_pos_of_ne0 hsp_pos
            ml_lets; apply wp_call_of_spec; apply hMm
            refine minLitDfs_pop_state hcore hsi hstk hsp_gt0 hsp_idxs hi0_lvl hv_nat hv_lt
              (lim := pos.toNat) (by simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e]
                                     exact hpos_ge') hcov_sp hm' fun k4 m4 hk4 hsi4 hstk4 hm4 => ?_
            ml_lets
            refine wp_join_group (ts := [i64]) (fun _ m_cd => m_cd = m4) ?_ ?_
            · rintro _ ⟨cd', ⟨⟩⟩ m_cd rfl; rw [Blocks.get_here]; ml_lets
              have hsp_m1 : (sp - 1).toNat = sp.toNat - 1 := min_bv64_sub1 (by omega)
              exact hL (minLitMaxSteps s - (steps + 1).toNat)
                (sp - 1, cd', steps + 1, ()) m_cd hdec_n
                ⟨by rw [hsp_m1]; omega, hsteps_le1, rfl, k4.mrk, mstk1, k4.min_clr,
                  k4.min_clr_len, k4.min_clr_full, idxs.take sp.toNat, hsi4, hm4,
                  by rwa [hsp_m1]⟩
            · rintro Jcd hJcd; ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
              · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                · ml_lets; apply hJcd; rfl
                · ml_lets; apply hJcd; rfl
              · ml_lets; apply hJcd; rfl

private theorem full_min_lit_dfs_m6_specs_wp (Γ : Env)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X) :
    ∀ args m Q X, fullMinLitSpec (args.1, args.2.1, ()) m Q X →
      Func.wp Γ full_min_lit_dfs_m6_body args m Q X := by
  rintro ⟨h, root_lit, minimizing, check_used, ⟨⟩⟩ m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hrl, hval, hrl_lvl, hno8, hm, hQ⟩
  dsimp only [vals, Arg.val] at hrl hval hrl_lvl hno8
  unfold Func.wp full_min_lit_dfs_m6_body; dsimp only [full_min_lit_dfs_m6_body]
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; have har := c.harena; unfold dimacsBound at hmx har
  have hcv := hlen0.cur_vars_le
  ml_ld load_full_cur_vars hm
  ml_lets; ml_jnz; refine ⟨fun hge => ?_, fun _ => ?_⟩
  · exfalso; c0_cond hge; bv_omega
  · ml_ld load_full_min_depth hm
    ml_lets; ml_jnz; refine ⟨fun hz => ?_, fun _ => ?_⟩
    · exfalso; c0_cond hz; have := fullMinDepthOf_pos c.max_vars
      have := fullMinDepthOf_le c.max_vars; unfold FullCfg.minDepth at *; bv_omega
    · ml_ld load_full_reason_ptr hm
      ml_ld c0_load_full_rsns (i := (root_lit >>> 1).setWidth 64)
        (by rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega) hm
      ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hrsn_some => ?_⟩
      · ml_lets; rw [wp]
        exact hQ false s.core.mrk s.core.min_stk s.core.min_clr s.core.min_clr_len
          s.core.min_clr_full m hcore.1 (fun _ _ => rfl) (fun _ _ h => h)
          (fun _ _ => rfl) hmin (fun hc => by cases hc) hm
      · ml_ld load_full_mark_ptr hm
        ml_ld load_full_level_ptr hm
        ml_ld load_full_arena_ptr hm
        ml_ld load_full_min_stk_ptr hm
        ml_ld load_full_shrink_stk_ptr hm
        ml_ld c0_load_full_lvl (i := (root_lit >>> 1).setWidth 64)
          (by rw [hlen0.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega) hm
        ml_lets
        refine wp_join_group (ts := []) (fun _ m0 => m0 = m) ?_ ?_
        · rintro _ ⟨⟩ m0 hm0; subst m0; rw [Blocks.get_here]
          have hmd_pos := fullMinDepthOf_pos c.max_vars
          have hmstkl := hlen0.min_stk_len
          ml_st m0, hm0 := store_minLit_stk (s := s) (mrk := s.core.mrk)
            (mstk := s.core.min_stk) (mclr := s.core.min_clr) (mcl := s.core.min_clr_len)
            (mcf := s.core.min_clr_full) (i := BitVec.signExtend 64 (0 : BitVec 32))
            (root_lit >>> 1) (by show 0 < s.core.min_stk.length; rw [hmstkl]
                                 unfold FullCfg.minDepth at *; omega) hm
          ml_st m1, hm1 := store_minLit_stk (s := s) (mrk := s.core.mrk)
            (mstk := s.core.min_stk.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat
              (root_lit >>> 1))
            (mclr := s.core.min_clr) (mcl := s.core.min_clr_len) (mcf := s.core.min_clr_full)
            (i := BitVec.signExtend 64 (1 : BitVec 32)) 0#32
            (by show 1 < _; rw [List.length_set, hmstkl]
                unfold FullCfg.minDepth at *; omega) hm0
          ml_ld load_full_arena_len hm1
          clear hm hm0 m0
          ml_lets
          obtain ⟨F_cur0, hw0⟩ := hcore.2
          obtain ⟨idx0, hi0, hi0_eq⟩ := (hw0.vals_false_iff root_lit.toNat hrl).mp hval
          have hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
            have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl; rw [hi0_eq, hl]
          have hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
              s.core.cur_level := by rw [hrv_root]; exact hrl_lvl
          have hrsn_ne0 : s.core.rsns[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            have hrl_lt : (root_lit >>> 1).toNat < s.core.rsns.length := by
              rw [hlen0.rsns_len, bv32_lshr_1]; omega
            rw [hrv_root, ← bv32_lshr_1, List.getElem?_eq_getElem hrl_lt, Option.getD_some]
            intro heq; c0_cond hrsn_some
            apply hrsn_some; simp only [← bv32_lshr_1]; exact heq.trans rfl
          let maxSteps := minLitMaxSteps s
          let BrkPost := MinLitBrkPost c s keepSet root_lit idx0 R
          let LpInv := MinLitLpInv c s keepSet idx0 R
          refine wp_loop_break_group (brkTs := [i64, i64, .bool, i64]) (lpTs := [i64, i64, i64])
            BrkPost LpInv ?_ ?_ ?_
          · rintro B r m' hBrk
            rw [Blocks.get_here]
            exact minLitDfs_brk_wp hMm hcore hrl_lvl hno8 hQ hBrk
          · rintro B L n ⟨sp, cd, steps, ⟨⟩⟩ m' hB hL
              ⟨hsp_lt, hsteps_le, rfl, mrk1, mstk1, mclr1, mcl1, mcf1, idxs, hsi, hm', hstk⟩
            clear hm1 m1
            rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt_st => ?_, fun _ => ?_⟩
            · have hms_eq := minLit_maxSteps_toNat hlen0.arena_len_le hcv
              rw [BitVec.ult, decide_eq_true_eq] at hlt_st
              dsimp only [maxSteps, minLitMaxSteps] at hms_eq hlt_st
              rw [hms_eq] at hlt_st
              have hsteps1 : (steps + 1).toNat = steps.toNat + 1 := min_bv64_add1 (by omega)
              have hdec_n : maxSteps - (steps + 1).toNat < maxSteps - steps.toNat := by
                dsimp only [maxSteps, minLitMaxSteps]; omega
              have hmd_le : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
              have hstk_ev :
                  (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                    mstk1.length := by rw [bv64_shl1_toNat (by omega), hsi.mstk_len]; omega
              have hstk_od :
                  (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
                    mstk1.length := by rw [bv64_shl1_add1_toNat (by omega), hsi.mstk_len]; omega
              have hsp_idxs : sp.toNat < idxs.length := by rw [hstk.len]; omega
              ml_ld c0_load_full_min_stk (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) hstk_ev hm'
              ml_ld c0_load_full_min_stk (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1) hstk_od hm'
              let v := mstk1[(sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat]'
                hstk_ev
              let pword := mstk1[(sp <<<
                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od
              let pos := pword &&& 0x7FFFFFFF#32
              have hv_nat : v.toNat =
                  (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                have hslot := (hstk.slot sp.toNat hsp_idxs).1
                rw [List.getElem?_eq_getElem (by rw [hsi.mstk_len]; omega), Option.getD_some]
                  at hslot
                dsimp only [v]; simp only [bv64_shl1_toNat (x := sp) (by omega)]; exact hslot
              have hv_lt : v.toNat < s.core.cur_vars := by
                rw [hv_nat]; have := hw0.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
              have hpos_nat :
                  pos.toNat = (mstk1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat := by
                dsimp only [pos, pword]; simp only [bv64_shl1_add1_toNat (x := sp) (by omega)]
                rw [List.getElem?_eq_getElem (by rw [hsi.mstk_len]; omega), Option.getD_some]
              ml_lets; ml_jnz; refine ⟨fun hv_ge => ?_, fun _ => ?_⟩
              · exfalso
                change (BitVec.ofNat 64 s.core.cur_vars).ule (v.setWidth 64) = true at hv_ge
                c0_cond hv_ge; rw [Nat.mod_eq_of_lt (by omega)] at hv_ge; omega
              · have hv_rsns : (v.setWidth 64).toNat <
                    (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core.rsns.length := by
                  dsimp only [minLitState]; rw [hlen0.rsns_len, bv_c0_zext32_64]; omega
                ml_ld c0_load_full_rsns (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                  (i := v.setWidth 64) hv_rsns hm'
                let rsn := s.core.rsns[(v.setWidth 64).toNat]'hv_rsns
                have hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
                    0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
                  have hvl : v.toNat < s.core.rsns.length := by rw [hlen0.rsns_len]; omega
                  have hvw : (v.setWidth 64).toNat = v.toNat := bv_c0_zext32_64 v
                  dsimp only [rsn]; simp only [hvw]
                  rw [← hv_nat, List.getElem?_eq_getElem hvl, Option.getD_some]
                have hcov_sp := (hstk.cov rfl sp.toNat hsp_idxs).2
                have hilen := hstk.len
                simp only [show sp.toNat + 1 = idxs.length by omega, ↓reduceIte, ← hpos_nat]
                  at hcov_sp
                ml_lets; ml_jnz; refine ⟨fun hno_rsn => ?_, fun _ => ?_⟩
                · exfalso; dsimp only [FrameCov] at hcov_sp
                  c0_cond hno_rsn; exact hcov_sp.1 (hrsn_eq.symm.trans hno_rsn)
                · ml_lets; ml_jnz; refine ⟨fun hbin => ?_, fun hbig => ?_⟩
                  · have hbin' : (rsn &&& 0x80000000#32) ≠ 0#32 := by
                      change ((rsn &&& 0x80000000#32) != 0#32) = true at hbin
                      c0_cond hbin; exact hbin
                    ml_lets; ml_jnz; refine ⟨fun hpos0 => ?_, fun hpos_nz => ?_⟩
                    · c0_cond hpos0
                      have hpos_0 : pos.toNat = 0 := congrArg BitVec.toNat hpos0
                      have hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'
                          hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                          0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
                          (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
                            0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
                        simp only [← hrsn_eq, eq_true hbin', ↓reduceIte]; omega
                      have hpar_eq : ((pword ||| 1#32) &&& 0x7FFFFFFF#32).toNat =
                          (mstk1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1 := by
                        rw [← hpos_nat, hpos_0]; exact bv32_mask31_or1_eq hpos0
                      ml_st m_p, hm_p' := store_minLit_stk (s := s) (mrk := mrk1) (mstk := mstk1)
                        (mclr := mclr1) (mcl := mcl1) (mcf := mcf1)
                        (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                        (pword ||| 1#32) hstk_od hm'
                      let mstk2 := mstk1.set (2 * sp.toNat + 1) (pword ||| 1#32)
                      rw [bv64_shl1_add1_toNat (x := sp) (by omega)] at hm_p'
                      have hmstk2_len : mstk2.length = 2 * c.minDepth := by
                        simp [mstk2, hsi.mstk_len]
                      have hsi_p := minLitStInv_with_mstk hsi hmstk2_len
                      let lit := rsn &&& 0x7FFFFFFF#32
                      have hlit_eq : lit.toNat = minLitRsnLit s.core rsn pos.toNat := by
                        dsimp only [minLitRsnLit, lit]; simp only [eq_true hbin', ↓reduceIte]
                      have hstk2_drop :
                          MinLitStkInv s.core mstk2 mrk1 sp.toNat idx0 idxs false := by
                        refine ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root,
                          fun j hj => ?_, fun hc => by cases hc⟩
                        dsimp only [mstk2]
                        rw [List.getElem?_set_ne (by omega)]; exact hstk.slot j hj
                      ml_lets; ml_jnz; refine ⟨fun hu_ge => ?_, fun hu_lt_cv => ?_⟩
                      · exfalso
                        change (BitVec.ofNat 64 s.core.cur_vars).ule
                          ((lit >>> 1).setWidth 64) = true at hu_ge
                        c0_cond hu_ge
                        have hu_lt_2v : lit.toNat < 2 * s.core.cur_vars := by
                          by_cases heq_var : lit.toNat / 2 =
                              (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2
                          · have hl1 := hw0.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
                          · have hfc := frameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
                              (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
                              hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
                            rw [← hrsn_eq, ← hlit_eq] at hfc; exact hfc.1
                        have := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at *; omega
                      · have hu_cv : (lit >>> 1).toNat < s.core.cur_vars := by
                          change (BitVec.ofNat 64 s.core.cur_vars).ule
                            ((lit >>> 1).setWidth 64) = false at hu_lt_cv
                          c0_cond hu_lt_cv
                          have := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at *; omega
                        have hu_lvl_len : ((lit >>> 1).setWidth 64).toNat <
                            (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.lvl.length := by
                          dsimp only [minLitState]; rw [hlen0.lvl_len, bv_c0_zext32_64]; omega
                        ml_ld c0_load_full_lvl
                          (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                          (i := (lit >>> 1).setWidth 64) hu_lvl_len hm_p'
                        let ul := s.core.lvl[((lit >>> 1).setWidth 64).toNat]'hu_lvl_len
                        ml_lets; ml_jnz; refine ⟨fun heq_uv => ?_, fun hne_uv => ?_⟩
                        · change ((lit >>> 1) == v) = true at heq_uv
                          c0_cond heq_uv
                          have heq_var : lit.toNat / 2 =
                              (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                            rw [← hv_nat, ← bv32_lshr_1, heq_uv]
                          refine hL (maxSteps - (steps + 1).toNat)
                            (sp, cd, steps + 1, ()) _ hdec_n
                            ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                              hsi_p, hm_p', minLitDfs_ok_res hcore hstk hi0_lvl hsi.mstk_len
                                hsp_lt hsp_idxs rfl hpos_nat hpar_eq hsz_lt hcov_sp
                                (by rwa [← hrsn_eq]) (u_idx := 0) (Or.inl heq_var)⟩
                        · have hu_neq : lit.toNat / 2 ≠
                              (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                            change ((lit >>> 1) == v) = false at hne_uv
                            c0_cond hne_uv; rw [← hv_nat]; intro heq; apply hne_uv
                            apply BitVec.eq_of_toNat_eq
                            simpa only [bv32_lshr_1] using heq
                          have hfc := frameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
                            (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
                            hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
                          rw [← hrsn_eq, ← hlit_eq] at hfc
                          obtain ⟨hu_lt2, u_idx, hu_idx_lt, hu_idx_eq, hu_lvl_le⟩ := hfc
                          have hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars := by
                            rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hu_lt2
                          ml_lets; ml_jnz; refine ⟨fun hlvl0 => ?_, fun _ => ?_⟩
                          · c0_cond hlvl0
                            refine hL (maxSteps - (steps + 1).toNat)
                              (sp, cd, steps + 1, ()) _ hdec_n
                              ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                                hsi_p, hm_p', ?_⟩
                            refine minLitStkInv_step_top (c := c) hstk hsi.mstk_len hsp_lt
                              (pword ||| 1#32) fun _ => ?_
                            rw [hpar_eq, ← hpos_nat]
                            refine frameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
                              (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
                              hcov_sp hsz_lt (Or.inr ⟨u_idx, hu_idx_lt,
                                by rwa [← hrsn_eq, ← hlit_eq], Or.inl ?_⟩)
                            rw [← hrsn_eq, ← hlit_eq]
                            have hlw : lit.toNat / 2 < s.core.lvl.length := by
                              rw [hlen0.lvl_len, ← bv32_lshr_1]; omega
                            rw [List.getElem?_eq_getElem hlw, Option.getD_some, hlvl0]; rfl
                          · have hu_mrk_len : ((lit >>> 1).setWidth 64).toNat <
                                (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.mrk.length := by
                              dsimp only [minLitState]; rw [hsi.mrk_len]; bv_omega
                            ml_ld c0_load_full_mrk
                              (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                              (i := (lit >>> 1).setWidth 64) hu_mrk_len hm_p'
                            let mu := mrk1[((lit >>> 1).setWidth 64).toNat]'hu_mrk_len
                            have hmu_eq : mu = mrk1[(lit >>> 1).toNat]?.getD 0#8 := by
                              have hvw := bv_c0_zext32_64 (lit >>> 1)
                              dsimp only [mu]
                              rw [List.getElem?_eq_getElem (by rw [hsi.mrk_len]; omega),
                                Option.getD_some]
                              congr 1
                            ml_lets; ml_jnz; refine ⟨fun hmu2 => ?_, fun hmu_n2 => ?_⟩
                            · have hmu_is2 : (mu &&& 2#8) ≠ 0#8 := bv8_c0_bit_ne0 hmu2
                              refine hL (maxSteps - (steps + 1).toNat)
                                (sp, cd, steps + 1, ()) _ hdec_n
                                ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                                  hsi_p, hm_p', ?_⟩
                              refine minLitStkInv_step_top (c := c) hstk hsi.mstk_len hsp_lt
                                (pword ||| 1#32) fun _ => ?_
                              rw [hpar_eq, ← hpos_nat]
                              refine frameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
                                (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
                                hcov_sp hsz_lt (Or.inr ⟨u_idx, hu_idx_lt,
                                  by rwa [← hrsn_eq, ← hlit_eq], Or.inr ?_⟩)
                              rw [← hrsn_eq, ← hlit_eq, ← bv32_lshr_1, ← hmu_eq]; exact hmu_is2
                            · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hmu_n4 => ?_⟩
                              · ml_lets; apply hB
                                exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p',
                                  ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                              · have hu_nat_idx : (lit >>> 1).toNat =
                                    (s.core.trl[u_idx]?.getD 0#32).toNat / 2 := by
                                  have hl := litVar_litNeg lit.toNat
                                  unfold litVar litNeg at hl
                                  rw [bv32_lshr_1, ← hl, ← hu_idx_eq]
                                have hu_lvl_root : (s.core.lvl[(s.core.trl[u_idx]?.getD
                                      0#32).toNat / 2]?.getD 0#32).toNat ≤
                                    (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD
                                      0#32).toNat := by
                                  have h1 : (s.core.trl[u_idx]?.getD 0#32).toNat / 2 =
                                      lit.toNat / 2 := by rw [← hu_nat_idx, bv32_lshr_1]
                                  rw [h1]
                                  exact Nat.le_trans hu_lvl_le (hstk.lvl_le_root sp.toNat hsp_idxs)
                                have hno8_u :
                                    (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
                                  rw [hsi.bit8 _ hu_bd_lt]
                                  refine hno8 _ hu_bd_lt ?_
                                  rw [hu_nat_idx, ← hrv_root]; exact hu_lvl_root
                                have hu_rsns_len : ((lit >>> 1).setWidth 64).toNat <
                                    (minLitState s mrk1 mstk2 mclr1 mcl1
                                      mcf1).core.rsns.length := by
                                  dsimp only [minLitState]
                                  rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega
                                ml_ld c0_load_full_rsns
                                  (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                                  (i := (lit >>> 1).setWidth 64) hu_rsns_len hm_p'
                                ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hur_some => ?_⟩
                                · ml_lets; apply wp_call_of_spec; apply hMm
                                  refine minLitDfs_poison_leaf hcore hsi_p hstk2_drop hsp_idxs
                                    hu_idx_lt hu_nat_idx hu_bd_lt (u_bv := lit >>> 1) hno8_u
                                    (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n2)
                                    (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n4) hm_p'
                                    fun mrk4 mclr4 mcl4 mcf4 m4 hsi4 hm4 hstk4 => by
                                      ml_lets; apply hB
                                      exact ⟨mrk4, mstk2, mclr4, mcl4, mcf4, hsi4, hm4,
                                        ⟨hsp_lt, idxs, hstk4⟩⟩
                                · refine wp_join_group (ts := []) (fun _ m_cu => m_cu = m_p) ?_ ?_
                                  · rintro _ ⟨⟩ m_cu rfl; rw [Blocks.get_here]
                                    ml_ld load_full_min_depth
                                      (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) hm_p'
                                    ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hdepth_ok => ?_⟩
                                    · ml_lets; apply hB
                                      exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p',
                                        ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                                    · c0_cond hdepth_ok
                                      have hsp1_nat : (sp + 1).toNat = sp.toNat + 1 :=
                                        min_bv64_add1 (by omega)
                                      have hsp1_lt : sp.toNat + 1 < c.minDepth := by
                                        have h1 : (1 : BitVec 64).toNat = 1 := rfl
                                        rw [h1, Nat.mod_eq_of_lt (by omega),
                                          Nat.mod_eq_of_lt (by omega)] at hdepth_ok
                                        omega
                                      have hstk_ev1 : ((sp + 1) <<< ((BitVec.signExtend 64
                                          (1 : BitVec 32)).toNat % 64)).toNat < mstk2.length := by
                                        rw [bv64_shl1_toNat (x := sp + 1) (by omega), hmstk2_len]
                                        omega
                                      have hstk_od1 : ((sp + 1) <<<
                                          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) +
                                          1).toNat < mstk2.length := by
                                        rw [bv64_shl1_add1_toNat (x := sp + 1) (by omega),
                                          hmstk2_len]; omega
                                      ml_st m_u, hm_u' := store_minLit_stk (s := s) (mrk := mrk1)
                                        (mstk := mstk2) (mclr := mclr1) (mcl := mcl1) (mcf := mcf1)
                                        (i := (sp + 1) <<<
                                          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))
                                        (lit >>> 1) hstk_ev1 hm_p'
                                      let mstk_mid := mstk2.set (2 * (sp.toNat + 1)) (lit >>> 1)
                                      rw [bv64_shl1_toNat (x := sp + 1) (by omega), hsp1_nat]
                                        at hm_u'
                                      have hmstk_mid_len : mstk_mid.length = 2 * c.minDepth := by
                                        simp [mstk_mid, hmstk2_len]
                                      ml_st m_z, hm_z' := store_minLit_stk (s := s) (mrk := mrk1)
                                        (mstk := mstk_mid) (mclr := mclr1) (mcl := mcl1)
                                        (mcf := mcf1)
                                        (i := (sp + 1) <<<
                                          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                                        (0 : BitVec 32)
                                        (by rw [hmstk_mid_len, ← hmstk2_len]; exact hstk_od1)
                                        hm_u'
                                      ml_lets
                                      let mstk3 := ((mstk1.set (2 * sp.toNat + 1)
                                        (pword ||| 1#32)).set (2 * (sp.toNat + 1))
                                        (lit >>> 1)).set (2 * (sp.toNat + 1) + 1) 0#32
                                      have hmstk3_len : mstk3.length = 2 * c.minDepth := by
                                        simp [mstk3, hsi.mstk_len]
                                      rw [bv64_shl1_add1_toNat (x := sp + 1) (by omega), hsp1_nat]
                                        at hm_z'
                                      have hrsn_u_ne : s.core.rsns[(lit >>> 1).toNat]?.getD
                                          0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                                        have hvw := bv_c0_zext32_64 (lit >>> 1)
                                        have hrlu : ((lit >>> 1).setWidth 64).toNat <
                                            s.core.rsns.length := by
                                          rw [hlen0.rsns_len, hvw]; omega
                                        rw [← hvw, List.getElem?_eq_getElem hrlu, Option.getD_some]
                                        dsimp only [minLitState] at hur_some
                                        intro heq
                                        have ht : (s.core.rsns[((lit >>> 1).setWidth 64).toNat] ==
                                            (4294967295 : BitVec 32)) = true := beq_iff_eq.mpr heq
                                        rw [ht] at hur_some; cases hur_some
                                      have hz_u : mrk1[(lit >>> 1).toNat]?.getD 0#8 = 0#8 := by
                                        have hdom := hsi.min_inv.mrk_dom (lit >>> 1).toNat hu_bd_lt
                                        have h2z := bv8_c0_bit_eq0 hmu_n2
                                        have h4z := bv8_c0_bit_eq0 hmu_n4
                                        rw [← hmu_eq] at hdom hno8_u
                                        have hmu0 := bv8_zero_of_masks24 _ hdom hno8_u h2z h4z
                                        rw [← hmu_eq]; exact hmu0
                                      have hstk3 := minLitStkInv_push hcore hstk hi0_lvl
                                        hsi.mstk_len hsp1_lt (u_bv := lit >>> 1)
                                        (par_pw := pword ||| 1#32) (ch_pw := 0#32) hpar_eq
                                        bv32_mask31_zero_eq0 hu_idx_lt hu_nat_idx hu_lvl_root
                                        (by rwa [← hpos_nat]) hz_u hrsn_u_ne
                                        ⟨hu_idx_lt, by
                                          rw [← hpos_nat, ← hrsn_eq, ← hlit_eq]; exact hu_idx_eq⟩
                                      exact hL (maxSteps - (steps + 1).toNat)
                                        (sp + 1, cd, steps + 1, ()) m_z hdec_n
                                        ⟨by rw [hsp1_nat]; exact hsp1_lt, by omega, rfl, mrk1,
                                          mstk3, mclr1, mcl1, mcf1, idxs ++ [u_idx],
                                          minLitStInv_with_mstk hsi hmstk3_len, hm_z',
                                          by rwa [hsp1_nat]⟩
                                  · rintro Jcu hJcu; ml_lets; ml_jnz
                                    refine ⟨fun _ => ?_, fun _ => ?_⟩
                                    · ml_lets; ml_jnz; refine ⟨fun hul_cv => ?_, fun _ => ?_⟩
                                      · have hul_cv' : ul.toNat < s.core.cur_vars := by
                                          c0_cond hul_cv
                                          rw [Nat.mod_eq_of_lt (by omega)] at hul_cv
                                          dsimp only [ul]
                                          simpa only [bv_c0_zext32_64, bv32_lshr_1] using hul_cv
                                        ml_ld load_full_cur_level
                                          (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) hm_p'
                                        ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                                        · have hul_ss : (ul.setWidth 64).toNat <
                                              (minLitState s mrk1 mstk2 mclr1 mcl1
                                                mcf1).scratch.shrink_stk.length := by
                                            dsimp only [minLitState]
                                            rw [hcore.1.scratch_ok.shrink_stk_len,
                                              bv_c0_zext32_64]
                                            omega
                                          ml_ld c0_load_full_shrink_stk
                                            (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                                            (i := ul.setWidth 64) hul_ss hm_p'
                                          ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                                          · ml_lets; apply hB
                                            exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p',
                                              ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                                          · ml_lets; apply hJcu; rfl
                                        · ml_lets; apply hJcu; rfl
                                      · ml_lets; apply hJcu; rfl
                                    · ml_lets; apply hJcu; rfl
                    · have hpos_ge : 1 ≤ pos.toNat := by
                        have hne : pos ≠ 0#32 := by
                          intro h0
                          have hpw : mstk1[(sp <<< ((BitVec.signExtend 64
                              (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od &&&
                              0x7FFFFFFF#32 = 0#32 := h0
                          change ((mstk1[(sp <<< ((BitVec.signExtend 64
                              (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od &&&
                              0x7FFFFFFF#32) == 0#32) = false at hpos_nz
                          rw [hpw] at hpos_nz; cases hpos_nz
                        have : pos.toNat ≠ 0 :=
                          fun h => hne (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
                        omega
                      ml_lets; ml_jnz; refine ⟨fun hsp0 => ?_, fun hsp_pos => ?_⟩
                      · ml_lets; apply hB; c0_cond hsp0
                        have hsp0' : sp.toNat = 0 := congrArg BitVec.toNat hsp0
                        have hi0_eq_w : idxs[sp.toNat]'hsp_idxs = idx0 := by
                          have he := hstk.idx0_eq
                          have hz : idxs[sp.toNat]'hsp_idxs =
                              idxs[0]'(by rw [hstk.len]; omega) := by simp only [hsp0']
                          rw [hz]
                          rw [List.getElem?_eq_getElem (by rw [hstk.len]; omega)] at he
                          exact Option.some.inj he
                        simp only [hi0_eq_w] at hcov_sp hrsn_eq
                        refine ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hsi, hm',
                          ⟨idx0, hi0, hi0_eq, pos.toNat, ?_, hcov_sp⟩⟩
                        simp only [← hrsn_eq, eq_true hbin', ↓reduceIte]; exact hpos_ge
                      · c0_cond hsp_pos
                        have hsp_gt0 : 0 < sp.toNat := bv64_pos_of_ne0 hsp_pos
                        ml_lets; apply wp_call_of_spec; apply hMm
                        refine minLitDfs_pop_state hcore hsi hstk hsp_gt0 hsp_idxs hi0_lvl hv_nat
                          hv_lt (lim := pos.toNat)
                          (by simp only [← hrsn_eq, eq_true hbin', ↓reduceIte]; exact hpos_ge)
                          hcov_sp hm' fun k4 m4 hk4 hsi4 hstk4 hm4 => ?_
                        ml_lets
                        refine wp_join_group (ts := [i64]) (fun _ m_cd => m_cd = m4) ?_ ?_
                        · rintro _ ⟨cd', ⟨⟩⟩ m_cd rfl; rw [Blocks.get_here]; ml_lets
                          have hsp_m1 : (sp - 1).toNat = sp.toNat - 1 := min_bv64_sub1 (by omega)
                          exact hL (maxSteps - (steps + 1).toNat)
                            (sp - 1, cd', steps + 1, ()) m_cd hdec_n
                            ⟨by rw [hsp_m1]; omega, by omega, rfl, k4.mrk, mstk1, k4.min_clr,
                              k4.min_clr_len, k4.min_clr_full, idxs.take sp.toNat, hsi4, hm4,
                              by rwa [hsp_m1]⟩
                        · rintro Jcd hJcd; ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                          · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                            · ml_lets; apply hJcd; rfl
                            · ml_lets; apply hJcd; rfl
                          · ml_lets; apply hJcd; rfl
                  · exact minLitDfs_big_wp hMm hcore hw0 hmx har hcv hi0 hi0_eq hrv_root hi0_lvl
                      hno8 hB hsp_lt (by rw [hsteps1]; omega) hL hsi hm' hstk hdec_n hmd_le
                      hstk_od hsp_idxs hv_nat hv_lt hpos_nat hrsn_eq hcov_sp hbig
            · ml_lets; apply hB
              exact ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hsi, hm',
                ⟨hsp_lt, idxs, minLitStkInv_drop_cov hstk⟩⟩
          · rintro B L hB hL; ml_lets
            let mstk0 := (s.core.min_stk.set 0 (root_lit >>> 1)).set 1 0#32
            have hmstkl' : mstk0.length = 2 * c.minDepth := by simp [mstk0, hmstkl]
            have hstk0 : MinLitStkInv s.core mstk0 s.core.mrk 0 idx0 [idx0] true := by
              refine ⟨rfl, rfl, fun k hk => ?_, fun k hk => by simp at hk, fun k hk => ?_,
                fun k hk => ?_, fun _ k hk => ?_⟩
              · have hk0 : k = 0 := by simp at hk; omega
                subst k; exact hi0
              · have hk0 : k = 0 := by simp at hk; omega
                subst k; exact le_refl _
              · have hk0 : k = 0 := by simp at hk; omega
                subst k
                rw [List.getElem?_set_ne (by decide), List.getElem?_set_self
                  (by unfold FullCfg.minDepth at *; omega), Option.getD_some]
                refine ⟨?_, fun h1 => by omega⟩
                have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl
                simp only [List.getElem_cons_zero]; rw [hi0_eq, hl, bv32_lshr_1]
              · have hk0 : k = 0 := by simp at hk; omega
                subst k
                rw [List.getElem?_set_self (by simp; unfold FullCfg.minDepth at *; omega),
                  Option.getD_some]
                refine ⟨fun hk1 => by simp at hk1, ?_⟩
                simp only [List.length_singleton, ↓reduceIte, bv32_mask31_zero_eq0]
                exact frameCov_zero hcore s.core.mrk hi0 hi0_lvl hrsn_ne0
            have hsi0 : MinLitStInv c s keepSet s.core.mrk mstk0 s.core.min_clr
                s.core.min_clr_len s.core.min_clr_full :=
              ⟨hlen0.mrk_len, hmstkl', hlen0.min_clr_len_arr, hlen0.min_clr_len_le,
                fun _ _ => rfl, fullMinMarkInv_with_mstk hmin mstk0,
                fun _ _ h => h, fun _ _ => rfl⟩
            have hm1' : (FullMem c (minLitState s s.core.mrk mstk0 s.core.min_clr
                s.core.min_clr_len s.core.min_clr_full) ⋆ R) m1 := by
              simpa only [mstk0, show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl,
                show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 from rfl] using hm1
            exact hL maxSteps (0#64, 0#64, 0#64, ()) m1
              ⟨hmd_pos, Nat.zero_le _, rfl, s.core.mrk, mstk0, s.core.min_clr,
                s.core.min_clr_len, s.core.min_clr_full, [idx0], hsi0, hm1', hstk0⟩
        · rintro Jpre hJpre; ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
          · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
            · ml_lets; ml_jnz; refine ⟨fun hrlvl_cv => ?_, fun _ => ?_⟩
              · c0_cond hrlvl_cv
                ml_ld load_full_cur_level hm
                ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                · have hrlvl_cv' :
                      (s.core.lvl[(root_lit >>> 1).setWidth 64 |>.toNat]'
                        (by rw [hlen0.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega) |>.setWidth
                          64).toNat < s.core.cur_vars := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hrlvl_cv
                    have h_sw := bv_c0_zext32_64 (s.core.lvl[((root_lit >>> 1).setWidth 64).toNat]'
                      (by rw [hlen0.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega))
                    rw [h_sw]; simpa only [bv_c0_zext32_64, bv32_lshr_1] using hrlvl_cv
                  have hrlvl_ss : (s.core.lvl[(root_lit >>> 1).setWidth 64 |>.toNat]'
                      (by rw [hlen0.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega) |>.setWidth
                        64).toNat < s.scratch.shrink_stk.length := by
                    rw [hcore.1.scratch_ok.shrink_stk_len]; exact lt_of_lt_of_le hrlvl_cv' hcv
                  ml_ld c0_load_full_shrink_stk (i := _) hrlvl_ss hm
                  ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                  · ml_lets; rw [wp]
                    exact hQ false s.core.mrk s.core.min_stk s.core.min_clr s.core.min_clr_len
                      s.core.min_clr_full m hcore.1 (fun _ _ => rfl) (fun _ _ h => h)
                      (fun _ _ => rfl) hmin (fun hc => by cases hc) hm
                  · ml_lets; apply hJpre; rfl
                · ml_lets; apply hJpre; rfl
              · ml_lets; apply hJpre; rfl
            · ml_lets; apply hJpre; rfl
          · ml_lets; apply hJpre; rfl

theorem full_min_lit_dfs_m6_wp (Γ : Env)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X) :
    ∀ args m Q X, m6MinLitDfsSpec args m Q X →
      Func.wp Γ full_min_lit_dfs_m6_body args m Q X := by
  rintro ⟨h, root_lit, minimizing, check_used, ⟨⟩⟩ m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hrl, hval, hrl_lvl, hno8, hm, hQ⟩
  refine full_min_lit_dfs_m6_specs_wp Γ
    (fun args m' Q' X' h' => hMm args m' Q' X' (specs_minMarkSpec_of_full h'))
    (c.hdr, root_lit, minimizing, check_used, ()) m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, toSpecsMinInv hmin, hrl, hval, hrl_lvl, hno8, hm, ?_⟩
  intro ok mrk' mstk' mclr' mcl' mcf' m' _s' hlen' hab' hm2' h8' hmin' hok' hm'
  exact hQ ok mrk' mstk' mclr' mcl' mcf' m' hlen' hab' hm2' h8' (toFullMinInv hmin')
    (fun hok => ⟨fun keep' hk => toFullMinInv ((hok' hok).1 keep' hk),
      toFullMinInv ((hok' hok).2)⟩) hm'

theorem full_min_lit_m6_wp (Γ : Env)
    (hDfs : ∀ args m Q X, m6MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullMinLitSpec args m Q X →
      Func.wp Γ full_min_lit_m6_body args m Q X := by
  rintro ⟨h, root_lit, ⟨⟩⟩ m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hrl, hval, hrl_lvl, hno8, hm, hQ⟩
  unfold Func.wp full_min_lit_m6_body; dsimp only [full_min_lit_m6_body]
  ml_lets; apply wp_call_of_spec; apply hDfs
  refine ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hrl, hval, hrl_lvl, hno8, hm, ?_⟩
  intro ok mrk' mstk' mclr' mcl' mcf' m' _s' hlen' hab' hm2' h8' hmin' hok' hm'
  ml_lets; rw [wp]
  exact hQ ok mrk' mstk' mclr' mcl' mcf' m' hlen' hab' hm2' h8' hmin' hok' hm'

private theorem full_shrink_lower_m6_specs_wp (Γ : Env)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m6MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] args m Q X) :
    ∀ args m Q X, fullShrinkLowerSpec args m Q X →
      Func.wp Γ full_shrink_lower_m6_body args m Q X := by
  rintro ⟨h, ot, ov, ⟨⟩⟩ m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hov_eq, hot_lt, hval, hlv_ov, hno8, hm, hQ⟩
  unfold Func.wp full_shrink_lower_m6_body; dsimp only [full_shrink_lower_m6_body]
  have hlen := hcore.1
  have hov_lt : ov.toNat < s.core.cur_vars := by omega
  have hov_mrk : (ov.setWidth 64).toNat < s.core.mrk.length := by
    rw [bv_c0_zext32_64, hlen.core_ok.mrk_len]; have := hlen.core_ok.cur_vars_le; omega
  have hov_mrk' : ov.toNat < s.core.mrk.length := by rwa [bv_c0_zext32_64] at hov_mrk
  ml_ld load_full_mark_ptr hm
  ml_ld c0_load_full_mrk (i := ov.setWidth 64) hov_mrk hm
  ml_lets; ml_jnz; refine ⟨fun hbit2 => ?_, fun _ => ?_⟩
  · have hb2 : (s.core.mrk[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
      rw [List.getElem?_eq_getElem hov_mrk', Option.getD_some]
      rw [show BitVec.setWidth 32 (BitVec.setWidth 8 (2 : BitVec 32)) = (2#8).setWidth 32 from rfl,
        show BitVec.setWidth 32 (BitVec.setWidth 8 (0 : BitVec 32)) = 0#32 from rfl] at hbit2
      c0_cond hbit2; simpa [bv_c0_zext32_64] using hbit2
    ml_lets; rw [wp]
    exact hQ true s.core.mrk s.core.min_stk s.core.min_clr s.core.min_clr_len
      s.core.min_clr_full m hlen (fun _ _ => rfl) (fun _ _ h => h) (fun _ _ => rfl)
      hmin (fun _ => hb2) hm
  · let FailJoin : Tup Val [] → Mem 64 → Prop := fun () m1 =>
      ∃ mrk1 mstk1 mclr1 mcl1 mcf1,
        let s1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
        s1.LengthsOk c ∧
        (∀ v, s.core.cur_vars ≤ v → mrk1[v]? = s.core.mrk[v]?) ∧
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[v]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ v < s.core.cur_vars,
          (mrk1[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) ∧
        FullMinMarkInv s1.core keepSet ∧
        (FullMem c s1 ⋆ R) m1
    refine wp_join_group (ts := []) FailJoin ?_ ?_
    · rintro _ ⟨⟩ m1 ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hlen1, hab1, hm2_1, h8_1, hmin1, hm1⟩
      rw [Blocks.get_here]; ml_lets
      apply wp_call_of_spec; apply hMm
      refine fullMinMarkSpec_step hlen1 hm1 ov hov_lt ((4 : BitVec 32).setWidth 8)
        fun m2 hm2 => ?_
      have h4 : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
      rw [h4] at hm2
      let s1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
      let s2 := fullMinMarkStepState s1 ov.toNat 4#8
      have hcore1 : FullOtfsCoreInv c F0 s1 :=
        fullOtfsCoreInv_with_min hcore hlen1.core_ok.mrk_len hlen1.core_ok.min_stk_len
          hlen1.core_ok.min_clr_len_arr hlen1.core_ok.min_clr_len_le
      have hno8_1 : (s1.core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
        dsimp only [s1, minLitState]
        rw [h8_1 ov.toNat hov_lt]; exact hno8 ov.toNat hov_lt (le_refl _)
      have hlen2 := fullMinMarkStepState_lengths hlen1 ov.toNat 4#8
      have hab2 := fullMinMarkStepState_mrk_above (s := s1) hov_lt 4#8
      obtain ⟨h8_2, hm2_2⟩ := fullMinMarkStepState_bit8_mono2 hlen1 hov_lt (Or.inr rfl) hno8_1
      have hmin2 := fullMinMarkInv_step_poison hcore1 hmin1 hov_lt hno8_1
      have hst2 : s2 = minLitState s s2.core.mrk mstk1 s2.core.min_clr
          s2.core.min_clr_len s2.core.min_clr_full := minLitState_step ov.toNat 4#8
      change FullState.LengthsOk c s2 at hlen2
      change FullMinMarkInv s2.core keepSet at hmin2
      change (FullMem c s2 ⋆ R) m2 at hm2
      rw [hst2] at hlen2 hmin2 hm2
      ml_lets; rw [wp]
      exact hQ false s2.core.mrk mstk1 s2.core.min_clr s2.core.min_clr_len
        s2.core.min_clr_full m2 hlen2
        (fun v hv => (hab2 v hv).trans (hab1 v hv))
        (fun v hv h2 => hm2_2 v hv (hm2_1 v hv h2))
        (fun v hv => (h8_2 v hv).trans (h8_1 v hv))
        hmin2 (fun hc => by cases hc) hm2
    · rintro Jf hJf
      ml_ld c0_load_full_mrk (i := ov.setWidth 64) hov_mrk hm
      ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
      · exact hJf () m ⟨s.core.mrk, s.core.min_stk, s.core.min_clr, s.core.min_clr_len,
          s.core.min_clr_full, hlen, fun _ _ => rfl, fun _ _ h => h, fun _ _ => rfl, hmin, hm⟩
      · apply wp_call_of_spec; apply hDfs
        dsimp only [m6MinLitDfsSpec, Full.fullMinLitSpec, vals, Arg.val]
        refine ⟨c, F0, s, keepSet, R, rfl, hcore, toFullMinInv hmin, hot_lt, hval,
          by rwa [← hov_eq], fun v hv hle => hno8 v hv (by rwa [hov_eq]), hm, ?_⟩
        intro ok mrk1 mstk1 mclr1 mcl1 mcf1 m1 hlen1 hab1 hm2_1 h8_1 hmin1 hok1 hm1
        ml_lets; ml_jnz; refine ⟨fun hok_t => ?_, fun _ => ?_⟩
        · have hmark2 : FullMinMarkInv (fullMinMarkCore
              (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core ov.toNat 2#8) keepSet := by
            rw [hov_eq]; dsimp only [minLitState]; exact toSpecsMinInv ((hok1 hok_t).2)
          ml_lets; apply wp_call_of_spec; apply hMm
          refine fullMinMarkSpec_step hlen1 hm1 ov hov_lt ((2 : BitVec 32).setWidth 8)
            fun m2 hm2 => ?_
          have h2eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
          rw [h2eq] at hm2
          let s1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
          let s2 := fullMinMarkStepState s1 ov.toNat 2#8
          have hno8_1 : (s1.core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
            dsimp only [s1, minLitState]
            rw [h8_1 ov.toNat hov_lt]; exact hno8 ov.toNat hov_lt (le_refl _)
          have hlen2 := fullMinMarkStepState_lengths hlen1 ov.toNat 2#8
          have hab2 := fullMinMarkStepState_mrk_above (s := s1) hov_lt 2#8
          obtain ⟨h8_2, hm2_2⟩ := fullMinMarkStepState_bit8_mono2 hlen1 hov_lt (Or.inl rfl) hno8_1
          have hmin2 : FullMinMarkInv s2.core keepSet := by
            dsimp only [s2, fullMinMarkStepState, fullMinMarkStepCore]
            split
            · exact toSpecsMinInv hmin1
            · exact hmark2
          have hov2 : (s2.core.mrk[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
            dsimp only [s2, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore]
            split
            · rename_i hc; rcases hc with hge | hset
              · exact absurd hov_lt (Nat.not_lt.mpr hge)
              · exact hset
            · have hm_len : mrk1.length = c.max_vars := hlen1.core_ok.mrk_len
              have hcv := hlen.core_ok.cur_vars_le
              dsimp only [s1, minLitState]
              rw [List.getElem?_set_self (by omega), Option.getD_some]
              exact bv8_and2_of_or2 _
          have hst2 : s2 = minLitState s s2.core.mrk mstk1 s2.core.min_clr
              s2.core.min_clr_len s2.core.min_clr_full := minLitState_step ov.toNat 2#8
          change FullState.LengthsOk c s2 at hlen2
          change FullMinMarkInv s2.core keepSet at hmin2
          change (FullMem c s2 ⋆ R) m2 at hm2
          rw [hst2] at hlen2 hmin2 hm2
          ml_lets; rw [wp]
          exact hQ true s2.core.mrk mstk1 s2.core.min_clr s2.core.min_clr_len
            s2.core.min_clr_full m2 hlen2
            (fun v hv => (hab2 v hv).trans (hab1 v hv))
            (fun v hv h2 => hm2_2 v hv (hm2_1 v hv h2))
            (fun v hv => (h8_2 v hv).trans (h8_1 v hv))
            hmin2 (fun _ => hov2) hm2
        · exact hJf () m1 ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hlen1, hab1, hm2_1, h8_1,
            toSpecsMinInv hmin1, hm1⟩

theorem full_shrink_lower_m6_wp (Γ : Env)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m6MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullShrinkLowerSpec args m Q X →
      Func.wp Γ full_shrink_lower_m6_body args m Q X := by
  rintro ⟨h, ot, ov, ⟨⟩⟩ m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hov_eq, hot_lt, hval, hlv_ov, hno8, hm, hQ⟩
  refine full_shrink_lower_m6_specs_wp Γ
    (fun args m' Q' X' h' => hMm args m' Q' X' (specs_minMarkSpec_of_full h'))
    hDfs (c.hdr, ot, ov, ()) m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, toSpecsMinInv hmin, hov_eq, hot_lt, hval, hlv_ov, hno8,
      hm, fun ok mrk' mstk' mclr' mcl' mcf' m' hlen' hab' hm2' h8' hmin' hok' hm' =>
        hQ ok mrk' mstk' mclr' mcl' mcf' m' hlen' hab' hm2' h8' (toFullMinInv hmin') hok' hm'⟩

end LeanQbe.T.Examples.Kissat.FullM6MinShrink
