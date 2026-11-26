module

public import LeanQbe.T.Examples.Kissat.FullM6BveFwd
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 BVE/Forward Proofs — Part 1 (Shared Lemmas & Cluster 1)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
1. Shared pure `FullDenseInvW` / `PH_SUBSUME` / `DenseWatchSliceOk` / `full_add_unit` /
   `full_watch_push` / `full_wstack_defrag` transport lemmas.
2. **Cluster 1**: `full_dense_prop_unit_m6_wp` and `full_dense_flush_units_m6_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BveFwd

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m6_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Shared Pure `FullDenseInvW` & BitVec Transport Lemmas -/

section SharedHelpers

theorem m6_getElem_congr {α : Type} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem m6_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem m6_xor1_mod2 (a : Nat) : (a ^^^ 1) % 2 = 1 - a % 2 := by
  have htb : (a ^^^ 1).testBit 0 = !(a.testBit 0) := by
    rw [Nat.testBit_xor]; cases a.testBit 0 <;> decide
  have h1 : ∀ n : Nat, n.testBit 0 = decide (n % 2 = 1) := fun n => Nat.testBit_zero n
  rw [h1, h1] at htb
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : (a ^^^ 1) % 2 = 0 ∨ (a ^^^ 1) % 2 = 1 := by omega
  rcases ha with h0 | h1' <;> rcases hb with k0 | k1 <;> simp_all

theorem m6_bv8_dom_pos_sle {v : BitVec 8} (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (v.signExtend 32).sle (BitVec.ofNat 32 0) = false) : v = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem m6_bv8_dom_pos_slt {v : BitVec 8} (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (BitVec.ofNat 32 0).slt (v.signExtend 32) = true) : v = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem m6_bv8_dom_neg_slt {v : BitVec 8} (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (v.signExtend 32).slt (BitVec.ofNat 32 0) = true) : v = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem m6_bv8_dom_neg_of_not_pos_ne0 {v : BitVec 8}
    (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h1 : (BitVec.ofNat 32 0).slt (v.signExtend 32) = false)
    (h2 : v.signExtend 32 ≠ 0#32) : v = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl
  · exact absurd rfl h2
  · simp at h1
  · rfl

theorem m6_bv8_dom_zero_of_not_pos_neg {v : BitVec 8}
    (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h1 : (BitVec.ofNat 32 0).slt (v.signExtend 32) = false)
    (h2 : (v.signExtend 32).slt (BitVec.ofNat 32 0) = false) : v = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem m6_vals_pos_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {l : Nat} (hl : l < 2 * k.cur_vars) (h1 : k.vals[l]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_true_iff l hl).mp h1
  have hv0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hs := hw.level0_sound idx hidx hv0
  rwa [htrl] at hs

theorem m6_vals_neg_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hff : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_false_iff l hl).mp hff
  have hv0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hs := hw.level0_sound idx hidx hv0
  rwa [htrl] at hs

theorem m6_resolve_bin_unit {F : CNF Nat} {a b : Nat}
    (hbin : F.EntailsClause (cnfClause [a ^^^ 1, b]))
    (hu : F.EntailsClause (cnfClause [a])) :
    F.EntailsClause (cnfClause [b]) := by
  rw [CNF.entails_clause_def] at hbin hu ⊢
  intro α hα
  have h1 := hbin α hα
  have h2 := hu α hα
  rw [clause_sat_cnfClause_iff] at h1 h2 ⊢
  obtain ⟨l2, hl2, hs2⟩ := h2
  rw [List.mem_singleton] at hl2
  rw [hl2] at hs2
  obtain ⟨l1, hl1, hs1⟩ := h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1
  rcases hl1 with h1a | h1b
  · exfalso
    rw [h1a] at hs1
    simp only [litVar, litSign] at hs1 hs2
    have hdiv := fullInv_var_xor1 a
    have hmod := m6_xor1_mod2 a
    rw [hdiv, hmod] at hs1
    cases h : α (a / 2) <;> simp [h] at hs1 hs2 <;> omega
  · rw [h1b] at hs1
    exact ⟨b, List.mem_singleton_self b, hs1⟩

theorem m6_unsat_of_lit_and_neg {F : CNF Nat} {a : Nat}
    (h1 : F.EntailsClause (cnfClause [a]))
    (h2 : F.EntailsClause (cnfClause [a ^^^ 1])) : F.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have s1 := (CNF.entails_clause_def.mp h1) α hα
  have s2 := (CNF.entails_clause_def.mp h2) α hα
  rw [clause_sat_cnfClause_iff] at s1 s2
  obtain ⟨l1, hl1, hs1⟩ := s1; obtain ⟨l2, hl2, hs2⟩ := s2
  rw [List.mem_singleton] at hl1 hl2
  rw [hl1] at hs1; rw [hl2] at hs2
  simp only [litVar, litSign] at hs1 hs2
  have hdiv := fullInv_var_xor1 a
  have hmod := m6_xor1_mod2 a
  rw [hdiv, hmod] at hs2
  cases h : α (a / 2) <;> simp [h] at hs1 hs2 <;> omega

theorem m6_clause_all_false_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {cl : List Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hlt : ∀ l ∈ cl, l < 2 * k.cur_vars)
    (hfalse : ∀ l ∈ cl, k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hs := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hs
  obtain ⟨l, hl, hsl⟩ := hs
  have hneg := m6_vals_neg_entails hw hl0 (hlt l hl) (hfalse l hl)
  have hsn := (CNF.entails_clause_def.mp hneg) α hα
  rw [clause_sat_cnfClause_iff] at hsn
  obtain ⟨l', hl', hsl'⟩ := hsn
  rw [List.mem_singleton] at hl'; rw [hl'] at hsl'
  simp only [litVar, litSign] at hsl hsl'
  have hdiv := fullInv_var_xor1 l
  have hmod := m6_xor1_mod2 l
  rw [hdiv, hmod] at hsl'
  cases h : α (l / 2) <;> simp [h] at hsl hsl' <;> omega

theorem m6_clause_one_unass_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {cl : List Nat} {u : Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hlt : ∀ l ∈ cl, l < 2 * k.cur_vars)
    (hoth : ∀ l ∈ cl, l ≠ u → k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have hs := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hs ⊢
  obtain ⟨l, hl, hsl⟩ := hs
  by_cases hlu : l = u
  · subst hlu; exact ⟨l, List.mem_singleton_self _, hsl⟩
  · exfalso
    have hneg := m6_vals_neg_entails hw hl0 (hlt l hl) (hoth l hl hlu)
    have hsn := (CNF.entails_clause_def.mp hneg) α hα
    rw [clause_sat_cnfClause_iff] at hsn
    obtain ⟨l', hl', hsl'⟩ := hsn
    rw [List.mem_singleton] at hl'; rw [hl'] at hsl'
    simp only [litVar, litSign] at hsl hsl'
    have hdiv := fullInv_var_xor1 l
    have hmod := m6_xor1_mod2 l
    rw [hdiv, hmod] at hsl'
    cases h : α (l / 2) <;> simp [h] at hsl hsl' <;> omega

private theorem nodup_lt_len_le : ∀ (n : Nat) (xs : List Nat),
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hlt => by have := hlt x List.mem_cons_self; omega
  | n + 1, xs, hnd, hlt => by
    by_cases hm : n ∈ xs
    · have hlen := nodup_lt_len_le n (xs.erase n) (hnd.erase n) fun x hx => by
        have hne : x ≠ n := fun heq => by
          subst heq
          have hnm := (List.Nodup.mem_erase_iff hnd).mp hx
          exact hnm.1 rfl
        have hmx := List.mem_of_mem_erase hx
        have := hlt x hmx; omega
      have her := List.length_erase_of_mem hm
      omega
    · have hlen := nodup_lt_len_le n xs hnd fun x hx => by
        have hne : x ≠ n := fun heq => hm (heq ▸ hx)
        have := hlt x hx; omega
      omega

theorem m6_clause_nodup_len_le {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false) :
    fullArenaClauseSize s cref ≤ s.core.cur_vars := by
  have hnd := h.2.2.2.1 cref href hng
  have hwf := h.2.1.arena.refs_wf cref href
  have hal := h.1.core_ok.arena_len_le
  have haa := h.1.core_ok.arena_len_arr
  have hlen : ((fullArenaClauseLits s cref).map (· / 2)).length = fullArenaClauseSize s cref := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  rw [← hlen]
  refine nodup_lt_len_le s.core.cur_vars _ hnd fun v hv => ?_
  rw [List.mem_map] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  have hlt := h.2.1.arena.lits_lt cref href hng l hl
  omega

private theorem bv32_bit24_disj (x : BitVec 32) (mask : BitVec 32)
    (hm : (0x01000000#32 &&& mask) = 0#32) :
    ((x ||| 0x01000000#32) &&& mask) = (x &&& mask) ∧
    ((x &&& ~~~0x01000000#32) &&& mask) = (x &&& mask) := by
  have h1 : ((x ||| 0x01000000#32) &&& mask) = (x &&& mask) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, hmi, Bool.or_false]
  have h2 : ((x &&& ~~~0x01000000#32) &&& mask) = (x &&& mask) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : mask[i]
    · simp
    · simp only [h, Bool.and_true] at hmi ⊢
      simp [hmi]
  exact ⟨h1, h2⟩

theorem m6_bit24_or_pres (x : BitVec 32) :
    ((x ||| 0x01000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    ((x ||| 0x01000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) :=
  ⟨(bv32_bit24_disj x 0x00080000#32 (by decide)).1,
   (bv32_bit24_disj x 0x00800000#32 (by decide)).1⟩

theorem m6_bit24_clear_pres (x : BitVec 32) :
    ((x &&& ~~~0x01000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    ((x &&& ~~~0x01000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) :=
  ⟨(bv32_bit24_disj x 0x00080000#32 (by decide)).2,
   (bv32_bit24_disj x 0x00800000#32 (by decide)).2⟩

theorem m6_garb_sub_bits (x : BitVec 32) :
    (((x ||| 0x00080000#32) ||| 0x01000000#32) &&& 0x00080000#32) ≠ 0#32 ∧
    (((x ||| 0x00080000#32) ||| 0x01000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  have h1 := bv32_or_garb_bits x
  have h2 := m6_bit24_or_pres (x ||| 0x00080000#32)
  exact ⟨by rw [h2.1]; exact h1.1, by rw [h2.2]; exact h1.2.2⟩

theorem m6_fullDenseInvW_set_hdr_bit24 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {v' : BitVec 32}
    (h19 : (v' &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (h23 : (v' &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref v' } }
    FullDenseInvW c F0 F_cur s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  have hcl := h.1.core_ok
  have hw := h.2.1
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have ha_cref : s'.core.arena[cref]? = some v' := List.getElem?_set_self har_len
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
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
      rw [h23, show fullArenaHdr s cref = s.core.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨_, hgt⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hper : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
    intro r hr
    have hwf := hw.arena.refs_wf r hr
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r
      have hsz : fullArenaClauseSizeCore s'.core cref = fullArenaClauseSizeCore s.core cref := by
        unfold fullArenaClauseSizeCore; dsimp only [s']; rw [List.getElem?_set_ne (by omega)]
      have hgb : fullArenaClauseGarbCore s'.core cref = fullArenaClauseGarbCore s.core cref := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        rw [ha_cref, Option.getD_some, h19]; rfl
      have hlits : fullArenaClauseLitsCore s'.core cref = fullArenaClauseLitsCore s.core cref :=
        fullArenaClauseLitsCore_eq_of_hold hbd (by simp [s', hbd]) hsz fun j _ =>
          List.getElem?_set_ne (by omega)
      exact ⟨hsz, hgb, hlits⟩
    · have hout : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r :=
        (hne_outside r hr hrc).imp (fun h => h.1) (fun h => by omega)
      have hpair := fullArenaClauseLitsCore_set_outside (v := v') hbd hout
      have hgb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [List.getElem?_set_ne (Ne.symm hrc)]
      exact ⟨hpair.1, hgb, hpair.2⟩
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, h.1.scratch_ok⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, (hper r hr).1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh; rw [ha_cref, Option.getD_some, h23] at hsh
          exact hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa [s', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1
          (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [(hper r hr).1]; exact ht0_lo, by dsimp only [s']; omega, ?_⟩
      dsimp only [s']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
      exact hw.arena.entails r hr hng
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs.symm ▸ hr)
      reason_inv := fun idx hidx hne => by
        have := hw.lvl_le idx hidx; have hl0 := h.2.2.2.2.2.1
        exact absurd (hw.level0_rsn_none idx hidx (by omega)) hne
      reason_lit_mem := fun idx hidx hne => by
        have := hw.lvl_le idx hidx; have hl0 := h.2.2.2.2.2.1
        exact absurd (hw.level0_rsn_none idx hidx (by omega)) hne }
  refine ⟨⟨hlen', hw', h.2.2.1, fun r hr hng => ?_,
    ⟨fun i hi => by change _ = 0xFFFFFFFF#32 ∨ _ ∈ fullArenaClauseRefsCore s'.core
                    rw [hrefs]; exact h.2.2.2.2.1.1 i hi, h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, hrefs, hper⟩
  change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
  change fullArenaClauseGarbCore s'.core r = false at hng; rw [(hper r hr).2.1] at hng
  change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup; rw [(hper r hr).2.2]
  exact h.2.2.2.1 r hr hng

theorem m6_fullDenseInvW_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {arena' : List (BitVec 32)} {ag' : BitVec 64}
    (hal : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some (fullArenaHdr s cref ||| 0x00080000#32) ∨
      arena'[cref]? = some ((fullArenaHdr s cref ||| 0x00080000#32) ||| 0x01000000#32))
    (hout : ∀ i, i ≠ cref → (i < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i) →
      arena'[i]? = s.core.arena[i]?) :
    let s' : FullState := { s with core := { s.core with arena := arena', arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := h.1.core_ok; have hw := h.2.1
  have hcref_wf := hw.arena.refs_wf cref href
  have hgarb_bit : (fullArenaHdrCore s'.core cref &&& 0x00080000#32) ≠ 0#32 := by
    unfold fullArenaHdrCore; dsimp only [s']
    rcases hhdr' with h1 | h2
    · rw [h1, Option.getD_some]; exact (bv32_or_garb_bits _).1
    · rw [h2, Option.getD_some]; exact (m6_garb_sub_bits _).1
  have hshrk_bit : (fullArenaHdrCore s'.core cref &&& 0x00800000#32) =
      (fullArenaHdrCore s.core cref &&& 0x00800000#32) := by
    unfold fullArenaHdrCore; dsimp only [s']
    rcases hhdr' with h1 | h2
    · rw [h1, Option.getD_some]; exact (bv32_or_garb_bits _).2.2
    · rw [h2, Option.getD_some]; exact (m6_garb_sub_bits _).2
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore s.core cref ≤ r ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := fullArenaScanRefs_disjoint hr href hlt
      have := (hw.arena.refs_wf r hr).2.2.1; exact Or.inl ⟨by omega, by omega⟩
    · have := fullArenaScanRefs_disjoint href hr hgt; exact Or.inr ⟨by omega, by omega⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : arena'[cref + 2]? = s.core.arena[cref + 2]? :=
        hout (cref + 2) (by omega) (Or.inl (by omega))
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2]
      have h23 : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) =
          (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) := hshrk_bit
      rw [h23]; split
      · exact fullArenaSkipShrk_congr fun i hi _ => hout i (by omega) (Or.inr hi)
      · rfl
    · refine fullArenaNextOff_congr_block
        (hout r hrc ((hne_outside r hr hrc).imp (fun h => by omega) (fun h => by omega)))
        (hout (r + 2) (by rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
          ((hne_outside r hr hrc).imp (fun h => by
            have := (hw.arena.refs_wf r hr).2.1; omega) (fun h => by omega)))
        fun i hi1 _ => hout i (by rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
          ((hne_outside r hr hrc).imp (fun h => by omega) (fun h => by
            have := (hw.arena.refs_wf r hr).2.2.1; omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst r; rw [hout (cref + 2) (by omega) (Or.inl (by omega))]
    · rw [hout (r + 2) (by rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
        ((hne_outside r hr hrc).imp (fun h => by
          have := (hw.arena.refs_wf r hr).2.1; omega) (fun h => by omega))]
  have hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr hne => by
    have hwf := hw.arena.refs_wf r hr
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    have hgb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
      rw [hout r hne ((hne_outside r hr hne).imp (fun h => by omega) (fun h => by omega))]
    have hlits : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
      fullArenaClauseLitsCore_eq_of_hold hbd
        (by dsimp only [s']; rw [hal, ← hcl.arena_len_arr]; omega)
        (hsz_eq r hr) fun j hj => hout (r + 3 + j)
          (by rcases hne_outside r hr hne with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
          ((hne_outside r hr hne).imp (fun h => by omega) (fun h => by omega))
    exact ⟨hgb, hlits⟩
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := hal }, h.1.scratch_ok⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; rwa [hshrk_bit] at hsh
        · unfold fullArenaHdrCore at hsh ⊢
          have hget := hout r hrc
            ((hne_outside r hr hrc).imp (fun h => by omega) (fun h => by omega))
          simpa [s', hget] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1
          (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by dsimp only [s']; omega, ?_⟩
      dsimp only [s']
      have ht0_out :
          t0 ≠ cref ∧ (t0 < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ t0) := by
        by_cases hrc : r = cref
        · subst r; exact ⟨by omega, Or.inr ht0_lo⟩
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
          · exact ⟨by omega, Or.inl (by omega)⟩
          · exact ⟨by omega, Or.inr (by omega)⟩
      rw [hout t0 ht0_out.1 ht0_out.2]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      have hne : r ≠ cref := by
        rintro rfl; unfold fullArenaClauseGarbCore at hng
        simp [hgarb_bit] at hng
      rw [(hother r hr hne).1] at hng; rw [(hother r hr hne).2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      have hne : r ≠ cref := by
        rintro rfl; unfold fullArenaClauseGarbCore at hng
        simp [hgarb_bit] at hng
      rw [(hother r hr hne).1] at hng; rw [(hother r hr hne).2]
      exact hw.arena.entails r hr hng
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs.symm ▸ hr)
      reason_inv := fun idx hidx hne => by
        have := hw.lvl_le idx hidx; have hl0 := h.2.2.2.2.2.1
        exact absurd (hw.level0_rsn_none idx hidx (by omega)) hne
      reason_lit_mem := fun idx hidx hne => by
        have := hw.lvl_le idx hidx; have hl0 := h.2.2.2.2.2.1
        exact absurd (hw.level0_rsn_none idx hidx (by omega)) hne }
  refine ⟨⟨hlen', hw', h.2.2.1, fun r hr hng => ?_,
    ⟨fun i hi => by change _ = 0xFFFFFFFF#32 ∨ _ ∈ fullArenaClauseRefsCore s'.core
                    rw [hrefs]; exact h.2.2.2.2.1.1 i hi, h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, hrefs⟩
  change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
  have hne : r ≠ cref := by
    intro heq; subst heq; change fullArenaClauseGarbCore s'.core r = false at hng
    unfold fullArenaClauseGarbCore at hng; simp [hgarb_bit] at hng
  change fullArenaClauseGarbCore s'.core r = false at hng; rw [(hother r hr hne).1] at hng
  change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup; rw [(hother r hr hne).2]
  exact h.2.2.2.1 r hr hng

theorem m6_fullDenseInvW_set_inc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     inconsistent_sound := fun _ => hu
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {sc' : FullScratch}
    (hok : sc'.LengthsOk c) (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur { s with scratch := sc' } :=
  ⟨⟨h.1.core_ok, hok⟩, h.2.1, h.2.2.1, h.2.2.2.1,
   ⟨fun i hi => by change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
                     (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s
                   rw [hll]; exact h.2.2.2.2.1.1 i hi,
    hext ▸ h.2.2.2.2.1.2⟩,
   h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {tmp' : List (BitVec 32)}
    (htl : tmp'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htl }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {p' : Nat} (hp : p' ≤ s.core.trail_end) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with propagated := p' } } :=
  ⟨⟨{ h.1.core_ok with propagated_le := hp }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (o' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := o' } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_of_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hcl' : s'.core.cur_level = 0) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw', ⟨fun v hv => by rw [hmrk]; exact h.2.2.1.1 v hv,
    fun l hl => by rw [hlm]; exact h.2.2.1.2 l hl⟩, ?_, ?_, hcl', hdm ▸ h.2.2.2.2.2.2⟩
  · intro r hr hng
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    have hlits : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hrefs] at hr; rw [hgb] at hng; rw [hlits]; exact h.2.2.2.1 r hr hng
  · refine ⟨fun i hi => ?_, hext ▸ h.2.2.2.2.1.2⟩
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    dsimp only; rw [hll, hrefs]; exact h.2.2.2.2.1.1 i hi

theorem m6_fullDenseInvW_of_wstackDefrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hslice : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l =
        fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l + k]? =
        s.core.wstk[fullWatchOff s l + k]?) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } }
  have hdm := h.2.2.2.2.2.2
  have hdw : DenseWatchesInv F_cur s.core := by
    have := h.2.1.watches; unfold ModeWatchesInv at this; rwa [ite_eq_right hdm] at this
  have hent_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hdw' : DenseWatchesInv F_cur s'.core := by
    refine ⟨hlay', fun l hl => ?_⟩
    obtain ⟨hsz, hget⟩ := hslice l hl
    change DenseWatchSliceOk F_cur s'.core l (fullWatchOffCore s'.core l)
      (fullWatchSizeCore s'.core l)
    rw [hsz]
    exact denseWatchSliceOk_relocate (k := s.core) (k' := s'.core) hent_refl (Nat.le_refl _)
      (fun _ hr => hr) hget (hdw.slices l hl)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' }
  exact ⟨hlen', hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, hdm⟩

theorem m6_fullDenseInvW_of_watchPush_occ {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {lit w0 w1 : BitVec 32} {ok : Bool}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefs s)
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } l =
        fullWatchSize s l ∧
      ∀ i < fullWatchSize s l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } l + i]? =
        s.core.wstk[fullWatchOff s l + i]?)
    (hok_t : ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } lit.toNat =
        fullWatchSize s lit.toNat + 2 ∧
      (∀ i < fullWatchSize s lit.toNat,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          lit.toNat + i]? = s.core.wstk[fullWatchOff s lit.toNat + i]?) ∧
      wstk'[fullWatchOffCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
      wstk'[fullWatchOffCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)
    (hok_f : ok = false → lit.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } lit.toNat =
        fullWatchSize s lit.toNat ∧
      ∀ i < fullWatchSize s lit.toNat,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          lit.toNat + i]? = s.core.wstk[fullWatchOff s lit.toNat + i]?) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { s.scratch with wsort := wsort' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { s.scratch with wsort := wsort' } }
  have hdm := h.2.2.2.2.2.2
  have hdw : DenseWatchesInv F_cur s.core := by
    have := h.2.1.watches; unfold ModeWatchesInv at this; rwa [ite_eq_right hdm] at this
  have hdw' := fullWatchPush_preserves_denseWatchesInv (s := s) (s' := s') (ok := ok)
    hdw hlay' rfl (fun _ hr => hr) hflag hsz hlt href hother hok_t hok_f
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' }
  exact ⟨hlen', hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, hdm⟩

theorem m6_denseWatchesInv_of_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : DenseWatchesInv F_cur s.core := by
  have := h.2.1.watches; unfold ModeWatchesInv at this; rwa [ite_eq_right h.2.2.2.2.2.2] at this

theorem m6_denseWatchSliceOk_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p + i]? = k.wstk[p + i]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p + rem]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hne : w0 ≠ 0xFFFFFFFF#32) (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    DenseWatchSliceOk F_cur k' lit p (rem + 1) := by
  induction h with
  | @empty p => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih
      (fun j hj => by
        simpa [show p + 1 + j = p + (j + 1) by omega] using hwstk (j + 1) (by omega))
      (by simpa [show p + 1 + rem = p + (rem + 1) by omega] using hw0)
  | @occ p rem w cr hp hp1 hf hs hl hr _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hs hl (hsub _ hr) ?_
    exact ih
      (fun j hj => by
        simpa [show p + 2 + j = p + (j + 2) by omega] using hwstk (j + 2) (by omega))
      (by simpa [show p + 2 + rem = p + (rem + 2) by omega] using hw0)

theorem m6_denseInvW_of_shrink_watch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {l nsz : Nat}
    (hl : l < 2 * s.core.cur_vars) (hnsz : nsz ≤ fullWatchSizeCore s.core l)
    {wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hwl : wstk'.length = c.wcap)
    (hout : ∀ idx,
      idx < fullWatchOffCore s.core l ∨
      fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ idx →
      wstk'[idx]? = s.core.wstk[idx]?)
    (hpref : DenseWatchSliceOk F_cur { s.core with wstk := wstk' } l
      (fullWatchOffCore s.core l) nsz) :
    let wvec' := s.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 nsz)
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } := by
  intro wvec'
  let s' : FullState :=
    { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
  have hdw := m6_denseWatchesInv_of_w h
  have hlay := hdw.layout
  have hcl := h.1.core_ok
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hbd_l := hlay.bounds l hl
  have hnsz32 : nsz < 2 ^ 32 := by have := hcl.wlen_le; omega
  have hwv_len : wvec'.length = 4 * c.max_vars := by simp [wvec', hcl.wvec_len]
  have hoff' : ∀ x < 2 * s.core.cur_vars,
      fullWatchOffCore s'.core x = fullWatchOffCore s.core x := by
    intro x _; unfold fullWatchOffCore; dsimp only [s', wvec']
    rw [List.getElem?_set_ne (by omega)]
  have hsz' : ∀ x < 2 * s.core.cur_vars,
      fullWatchSizeCore s'.core x =
        if x = l then nsz else fullWatchSizeCore s.core x := by
    intro x hx; unfold fullWatchSizeCore; dsimp only [s', wvec']
    by_cases hxl : x = l
    · subst hxl; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by rw [hcl.wvec_len]; have := hcl.cur_vars_le; omega),
        Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnsz32]
    · simp only [hxl, ↓reduceIte]; rw [List.getElem?_set_ne (by omega)]
  have hent_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hdw' : DenseWatchesInv F_cur s'.core := by
    refine DenseWatchesInv.of_slices ?_ ?_ ?_ ?_
    · intro x hx
      have hx0 : x < 2 * s.core.cur_vars := hx
      rw [hoff' x hx0, hsz' x hx0]
      change fullWatchOffCore s.core x + _ ≤ s.core.wlen
      split
      · subst ‹x = l›; omega
      · exact hlay.bounds x hx0
    · intro x hx hp
      have hx0 : x < 2 * s.core.cur_vars := hx
      rw [hoff' x hx0]; rw [hsz' x hx0] at hp
      split at hp
      · exact hlay.pos_off x hx0 (by rw [‹x = l›]; omega)
      · exact hlay.pos_off x hx0 hp
    · intro l1 l2 h1 h2 hne hp1 hp2
      have h10 : l1 < 2 * s.core.cur_vars := h1
      have h20 : l2 < 2 * s.core.cur_vars := h2
      rw [hoff' l1 h10, hoff' l2 h20, hsz' l1 h10, hsz' l2 h20]
      rw [hsz' l1 h10] at hp1; rw [hsz' l2 h20] at hp2
      have h1p : 0 < fullWatchSizeCore s.core l1 := by
        split at hp1
        · subst ‹l1 = l›; omega
        · exact hp1
      have h2p : 0 < fullWatchSizeCore s.core l2 := by
        split at hp2
        · subst ‹l2 = l›; omega
        · exact hp2
      rcases hlay.disjoint l1 l2 h10 h20 hne h1p h2p with hd | hd
      · left; split
        · subst ‹l1 = l›; omega
        · exact hd
      · right; split
        · subst ‹l2 = l›; omega
        · exact hd
    · intro x hx
      have hx0 : x < 2 * s.core.cur_vars := hx
      rw [hoff' x hx0, hsz' x hx0]
      by_cases hxl : x = l
      · subst hxl; simp only [↓reduceIte]
        exact hpref.mono (k := { s.core with wstk := wstk' }) (k' := s'.core)
          hent_refl (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl)
      · simp only [hxl, ↓reduceIte]
        by_cases hpx : fullWatchSizeCore s.core x = 0
        · rw [hpx]; exact .empty
        · by_cases hpl : fullWatchSizeCore s.core l = 0
          · exact (hdw.slices x hx0).mono (k := s.core) (k' := s'.core)
              hent_refl (Nat.le_refl _) (fun _ hr => hr) fun idx _ _ => hout idx (by omega)
          · have hdj := hlay.disjoint x l hx0 hl hxl (by omega) (by omega)
            exact (hdw.slices x hx0).mono (k := s.core) (k' := s'.core)
              hent_refl (Nat.le_refl _) (fun _ hr => hr) fun idx hi1 hi2 =>
              hout idx (by rcases hdj with h1 | h2 <;> omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := by unfold ModeWatchesInv; rw [ite_eq_right h.2.2.2.2.2.2]; exact hdw' }
  exact ⟨⟨{ hcl with wvec_len := hwv_len, wstk_len_arr := hwl }, h.1.scratch_ok⟩,
    hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end SharedHelpers

/-! ## 2. Cluster 1 — Dense-Mode Unit Propagation & Flush (`full_dense_*_m6`) -/

section Cluster1

/-- Contract for `full_dense_prop_unit_m6`: propagates level-`0` unit `lit` across dense binary
and large occurrences, marks root-satisfied clauses `PH_GARB`, and preserves `FullDenseInvW`,
`cur_vars`, `arena_len`, `fullArenaClauseRefs`, `fuel`, `tarjan_mark`, and scratch buffers. -/
def fullDensePropUnitM6Spec : Spec [i64, i32] [.bool] := fun (h, _lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullDensePropUnitM6Spec_noExit :
    ∀ xs m Q X, fullDensePropUnitM6Spec xs m Q X →
      fullDensePropUnitM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullDensePropUnitM6Spec_elim {h : BitVec 64} {lit : BitVec 32} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hs : fullDensePropUnitM6Spec (h, lit, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.red_refs = s.scratch.red_refs →
        s'.scratch.scratch_buf = s.scratch.scratch_buf →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        s'.scratch.sim_sig = s.scratch.sim_sig →
        (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m' :=
  hs

/-- Contract for `full_dense_flush_units_m6`: flushes all pending level-`0` trail units while
dense watches are connected, preserving `FullDenseInvW`, `cur_vars`, `arena_len`,
`fullArenaClauseRefs`, `fuel`, `tarjan_mark`, and scratch buffers. -/
def fullDenseFlushUnitsM6Spec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullDenseFlushUnitsM6Spec_noExit :
    ∀ xs m Q X, fullDenseFlushUnitsM6Spec xs m Q X →
      fullDenseFlushUnitsM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullDenseFlushUnitsM6Spec_intro {h : BitVec 64} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullDenseFlushUnitsM6Spec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hm, hQ⟩

private def DpStatePres (s s' : FullState) : Prop :=
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.arena_len = s.core.arena_len ∧
  s'.core.fuel = s.core.fuel ∧
  s'.core.wvec = s.core.wvec ∧
  s'.core.wstk = s.core.wstk ∧
  s'.core.wlen = s.core.wlen ∧
  fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.red_refs = s.scratch.red_refs ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

private theorem dpStatePres_refl (s : FullState) : DpStatePres s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem dpStatePres_trans {s1 s2 s3 : FullState}
    (h12 : DpStatePres s1 s2) (h23 : DpStatePres s2 s3) : DpStatePres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1, h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Parametric `Func.wp` proof for `full_dense_prop_unit_m6`. -/
theorem full_dense_prop_unit_m6_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullDensePropUnitM6Spec a m Q X →
      Func.wp Γ full_dense_prop_unit_m6_body a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have harc := c.harena
  unfold dimacsBound at hmx hwc harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hret_t : ∀ s1 m1, FullDenseInvW c F0 F_cur s1 → DpStatePres s0 s1 →
      (FullMem c s1 ⋆ R) m1 → Q (true, ()) m1 :=
    fun s1 m1 hdw1 hp hm1 => hQ true s1 m1 hdw1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.2.2 (fun h => by cases h) hm1
  have hret_f : ∀ s1 m1, FullDenseInvW c F0 F_cur s1 → DpStatePres s0 s1 → F0.Unsat →
      (FullMem c s1 ⋆ R) m1 → Q (false, ()) m1 :=
    fun s1 m1 hdw1 hp hu hm1 => hQ false s1 m1 hdw1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.2.2 (fun _ => hu) hm1
  unfold Func.wp full_dense_prop_unit_m6_body
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!; exact hret_t s0 m0 hdw0 (dpStatePres_refl s0) hm0
  · have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by omega
    have hlit_val_idx : (lit.setWidth 64).toNat < s0.core.vals.length := by
      rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
    c0_hsteps_nogrp
    c0_hsplit
    · c0_hsteps!; exact hret_t s0 m0 hdw0 (dpStatePres_refl s0) hm0
    · have hv_lit1 : s0.core.vals[lit.toNat]?.getD 0#8 = 1#8 := by
        have hdom := hdw0.2.1.vals_domain lit.toNat hlit_lt
        have hlt_v : lit.toNat < s0.core.vals.length := by rw [hdw0.1.core_ok.vals_len]; omega
        rw [List.getElem?_eq_getElem hlt_v, Option.getD_some] at hdom ⊢
        exact m6_bv8_dom_pos_sle hdom hc
      have hent_lit : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) :=
        m6_vals_pos_entails hdw0.2.1 hdw0.2.2.2.2.2.1 hlit_lt hv_lit1
      have hnl_toNat : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := rfl
      have hnl_lt : (lit ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
        rw [hnl_toNat]; have := fullInv_var_xor1 lit.toNat; omega
      have hdw_s0 := m6_denseWatchesInv_of_w hdw0
      have hbd_nl := hdw_s0.layout.bounds _ hnl_lt
      have hwlen_le := hdw0.1.core_ok.wlen_le
      have hnl_wv0 : ((lit ^^^ 1#32).setWidth 64 <<< (1 : Nat)).toNat < s0.core.wvec.length := by
        rw [hdw0.1.core_ok.wvec_len]; c0_bound
      have hnl_wv1 : ((lit ^^^ 1#32).setWidth 64 <<< (1 : Nat) + 1#64).toNat <
          s0.core.wvec.length := by
        rw [hdw0.1.core_ok.wvec_len]; c0_bound
      c0_hsteps_nogrp
      let off_nl :=
        (s0.core.wvec[((lit ^^^ 1#32).setWidth 64 <<< (1 : Nat)).toNat]'hnl_wv0).setWidth 64
      let sz_nl :=
        (s0.core.wvec[((lit ^^^ 1#32).setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hnl_wv1).setWidth 64
      let end_nl := off_nl + sz_nl
      have hoff_nl_eq : off_nl.toNat = fullWatchOffCore s0.core (lit ^^^ 1#32).toNat := by
        unfold off_nl fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some,
          m6_zext32_toNat]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hsz_nl_eq : sz_nl.toNat = fullWatchSizeCore s0.core (lit ^^^ 1#32).toNat := by
        unfold sz_nl fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega), Option.getD_some,
          m6_zext32_toNat]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hend_nl_eq : end_nl.toNat = off_nl.toNat + sz_nl.toNat := by
        dsimp only [end_nl]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hnl_c0_eq :
          (s0.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]?.getD 0#32).toNat +
          (s0.core.wvec[(2 * (lit.toNat ^^^ 1) + 1) % 2 ^ 64]?.getD 0#32).toNat =
          end_nl.toNat := by
        rw [hend_nl_eq, hoff_nl_eq, hsz_nl_eq]
        unfold fullWatchOffCore fullWatchSizeCore
        have hm0 : 2 * (lit.toNat ^^^ 1) % 2 ^ 64 = 2 * (lit ^^^ 1#32).toNat := by
          rw [hnl_toNat]; omega
        have hm1 : (2 * (lit.toNat ^^^ 1) + 1) % 2 ^ 64 = 2 * (lit ^^^ 1#32).toNat + 1 := by
          rw [hnl_toNat]; omega
        rw [hm0, hm1]
      -- Loop 1: propagate watches on `nl = lit ^ 1`
      refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
        (fun (_, ()) mb => ∃ s1 : FullState,
          FullDenseInvW c F0 F_cur s1 ∧ DpStatePres s0 s1 ∧ (FullMem c s1 ⋆ R) mb)
        (fun rem (p, ()) mp => ∃ sp : FullState,
          p.toNat ≤ end_nl.toNat ∧ rem = end_nl.toNat - p.toNat ∧
          FullDenseInvW c F0 F_cur sp ∧ DpStatePres s0 sp ∧
          DenseWatchSliceOk F_cur sp.core (lit ^^^ 1#32).toNat p.toNat rem ∧
          (FullMem c sp ⋆ R) mp)
        ?_ ?_ ?_
      · -- Loop 2: scan `lit` watches to mark root-satisfied large clauses `PH_GARB`
        rintro _ ⟨_, ⟨⟩⟩ m1 ⟨s1, hdw1, hp1, hm1⟩
        have hdw_s1 := m6_denseWatchesInv_of_w hdw1
        have hwlen1_le := hdw1.1.core_ok.wlen_le
        have hlit_lt1 : lit.toNat < 2 * s1.core.cur_vars := by rw [hp1.1]; exact hlit_lt
        have hbd_l := hdw_s1.layout.bounds _ hlit_lt1
        have hlit_wv0 : (lit.setWidth 64 <<< (1 : Nat)).toNat < s1.core.wvec.length := by
          rw [hdw1.1.core_ok.wvec_len]; c0_bound
        have hlit_wv1 : (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s1.core.wvec.length := by
          rw [hdw1.1.core_ok.wvec_len]; c0_bound
        c0_hsteps_nogrp
        let off_l := (s1.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlit_wv0).setWidth 64
        let sz_l :=
          (s1.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hlit_wv1).setWidth 64
        let end_l := off_l + sz_l
        have hoff_l_eq : off_l.toNat = fullWatchOffCore s1.core lit.toNat := by
          unfold off_l fullWatchOffCore
          rw [List.getElem?_eq_getElem (by rw [hdw1.1.core_ok.wvec_len]; omega), Option.getD_some,
            m6_zext32_toNat]
          exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
        have hsz_l_eq : sz_l.toNat = fullWatchSizeCore s1.core lit.toNat := by
          unfold sz_l fullWatchSizeCore
          rw [List.getElem?_eq_getElem (by rw [hdw1.1.core_ok.wvec_len]; omega), Option.getD_some,
            m6_zext32_toNat]
          exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
        have hend_l_eq : end_l.toNat = off_l.toNat + sz_l.toNat := by
          dsimp only [end_l]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
          (fun (_, ()) m2 => ∃ s2 : FullState,
            FullDenseInvW c F0 F_cur s2 ∧ DpStatePres s0 s2 ∧ (FullMem c s2 ⋆ R) m2)
          (fun rem (p, ()) mp => ∃ sp : FullState,
            p.toNat ≤ end_l.toNat ∧ rem = end_l.toNat - p.toNat ∧
            FullDenseInvW c F0 F_cur sp ∧ DpStatePres s0 sp ∧
            DenseWatchSliceOk F_cur sp.core lit.toNat p.toNat rem ∧
            (FullMem c sp ⋆ R) mp)
          ?_ ?_ ?_
        · rintro _ ⟨_, ⟨⟩⟩ m2 ⟨s2, hdw2, hp2, hm2⟩
          c0_hsteps!; exact hret_t s2 m2 hdw2 hp2 hm2
        · rintro B2 L2 rem ⟨p, ⟨⟩⟩ mp hB2 hL2 ⟨sp, hp_le, hrem, hdwp, hpp, hslice, hmp⟩
          have hlt1 : (s1.core.wvec[2 * lit.toNat % 2 ^ 64]'(by
              rw [hdw1.1.core_ok.wvec_len]; omega)).toNat = off_l.toNat := by
            rw [hoff_l_eq]; unfold fullWatchOffCore
            rw [List.getElem?_eq_getElem (by rw [hdw1.1.core_ok.wvec_len]; omega),
              Option.getD_some]
            exact congrArg BitVec.toNat (m6_getElem_congr (by omega) _ _)
          have hlt2 : (s1.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hdw1.1.core_ok.wvec_len]; simp; omega)).toNat = sz_l.toNat := by
            rw [hsz_l_eq]; unfold fullWatchSizeCore
            rw [List.getElem?_eq_getElem (by rw [hdw1.1.core_ok.wvec_len]; omega),
              Option.getD_some]
            exact congrArg BitVec.toNat (m6_getElem_congr (by simp; omega) _ _)
          have hsum_l : (off_l.toNat + sz_l.toNat) % 2 ^ 64 = end_l.toNat := by
            rw [Nat.mod_eq_of_lt (by omega), hend_l_eq]
          c0_hsplit
          · have hp_lt : p.toNat < end_l.toNat := by
              rw [hlt1, hlt2, hsum_l] at hc; exact hc
            have hpw : p.toNat < sp.core.wstk.length := by
              rw [hdwp.1.core_ok.wstk_len_arr]; omega
            have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
            cases hslice with
            | empty => omega
            | @bin _ rem1 w0 hwp hflag _ _ _ hrest =>
              have hw0_eq : sp.core.wstk[p.toNat]'hpw = w0 := by
                rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
              c0_hsplit
              · c0_hsteps!
                exact hL2 rem1 (p + 1#64, ()) mp (by omega)
                  ⟨sp, by omega, by omega, hdwp, hpp, by rw [hp1_nat]; exact hrest, hmp⟩
              · rw [hw0_eq] at hc; exact absurd hc hflag
            | @occ _ rem2 w0 cr hwp hwp1 hflag _ _ href hrest =>
              have hw0_eq : sp.core.wstk[p.toNat]'hpw = w0 := by
                rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
              have hrem2 : end_l.toNat - p.toNat = rem2 + 2 := by omega
              have hp1_lt : (p + 1#64).toNat < end_l.toNat := by omega
              have hp1_w : (p + 1#64).toNat < sp.core.wstk.length := by
                rw [hdwp.1.core_ok.wstk_len_arr]; omega
              have hp1_c0 : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
                simp; omega
              have hcr_eq :
                  sp.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hdwp.1.core_ok.wstk_len_arr]; omega) = cr := by
                rw [List.getElem?_eq_getElem (by omega)] at hwp1
                exact (m6_getElem_congr hp1_c0 _ _).trans (Option.some.inj hwp1)
              have hcr_eq' : sp.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_w = cr :=
                (m6_getElem_congr (by c0_bound) _ _).trans hcr_eq
              have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
              have hrest' : DenseWatchSliceOk F_cur sp.core lit.toNat (p + 1#64 + 1#64).toNat
                  rem2 := by
                rw [hp2_nat]; exact hrest
              have hwf_cr := hdwp.2.1.arena.refs_wf cr.toNat href
              have har_le := hdwp.1.core_ok.arena_len_le
              have hcr_ar : (cr.setWidth 64).toNat < sp.core.arena.length := by
                rw [hdwp.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
              c0_hsplit
              · rw [hw0_eq] at hc; exact absurd hflag hc
              · c0_hsplit
                · rw [hlt1, hlt2, hsum_l] at hc; simp at hc; omega
                · c0_hsplit
                  · c0_hsteps!
                    exact hL2 rem2 (p + 1#64 + 1#64, ()) mp
                      (by omega) ⟨sp, by omega, by omega, hdwp, hpp, hrest', hmp⟩
                  · simp only [hcr_eq, hcr_eq'] at hc ⊢
                    have har_len_cr : cr.toNat < sp.core.arena.length := by
                      rw [hdwp.1.core_ok.arena_len_arr]; omega
                    have hng : fullArenaClauseGarb sp cr.toNat = false := by
                      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                      rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                      change (sp.core.arena[cr.toNat]'har_len_cr &&& 0x00080000#32) = 0#32 at hc
                      rw [hc]; rfl
                    have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < sp.core.arena.length := by
                      rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                    let sz_c := sp.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
                    have hsz_eq : sz_c.toNat = fullArenaClauseSizeCore sp.core cr.toNat := by
                      unfold sz_c fullArenaClauseSizeCore
                      rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
                        Option.getD_some]
                      exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                    c0_hsteps_nogrp
                    refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                      (fun (_, _, ()) ms => ms = mp)
                      (fun rem_k (k, ()) mk => k.toNat ≤ sz_c.toNat ∧
                        rem_k = sz_c.toNat - k.toNat ∧ mk = mp)
                      ?_ ?_ ?_
                    · rintro _ ⟨sat_b, _, ⟨⟩⟩ ms rfl
                      refine wp_join0 (P := fun mj => ∃ sm : FullState,
                        FullDenseInvW c F0 F_cur sm ∧ DpStatePres s0 sm ∧
                        DenseWatchSliceOk F_cur sm.core lit.toNat (p + 1#64 + 1#64).toNat rem2 ∧
                        (FullMem c sm ⋆ R) mj)
                        (fun _ mj ⟨sm, hdwm, hpm, hrestm, hmm⟩ => by
                          c0_hsteps!
                          exact hL2 rem2 (p + 1#64 + 1#64, ()) mj (by omega)
                            ⟨sm, by omega, by omega, hdwm, hpm, hrestm, hmm⟩)
                        (fun Jm hJm => by
                          c0_hsplit
                          · have hhdr_eq : sp.core.arena[cr.toNat]'har_len_cr =
                                fullArenaHdr sp cr.toNat := by
                              unfold fullArenaHdr fullArenaHdrCore
                              rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                            c0_hsteps!
                            let ag' := sp.core.arena_garbage + 3#64 + sz_c.setWidth 64
                            let ar' := sp.core.arena.set (cr.setWidth 64).toNat
                              (sp.core.arena[(cr.setWidth 64).toNat]'hcr_ar ||| 0x00080000#32)
                            let smg : FullState :=
                              { sp with core :=
                                { sp.core with arena := ar', arena_garbage := ag' } }
                            have har'_eq : ar' = sp.core.arena.set cr.toNat
                                (fullArenaHdr sp cr.toNat ||| 0x00080000#32) := by
                              dsimp only [ar']; rw [← hhdr_eq]
                              have hval := m6_getElem_congr (m6_zext32_toNat cr) hcr_ar har_len_cr
                              rw [hval, m6_zext32_toNat]
                            have hmg := m6_fullDenseInvW_markGarb hdwp href (arena' := ar')
                              (ag' := ag')
                              (by simp [ar', hdwp.1.core_ok.arena_len_arr])
                              (Or.inl (by rw [har'_eq]; exact List.getElem?_set_self har_len_cr))
                              (fun i hne _ => by
                                rw [har'_eq]; exact List.getElem?_set_ne hne.symm)
                            have hpres_mg : DpStatePres sp smg :=
                              ⟨rfl, rfl, rfl, rfl, rfl, rfl, hmg.2, rfl, rfl, rfl, rfl, rfl, rfl⟩
                            have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                              rw [CNF.entails_def]; exact fun _ hx => hx
                            have hrest_mg := hrest'.mono (k := sp.core) (k' := smg.core) hent_r
                              (Nat.le_refl _) (fun r hr => by
                                change r ∈ fullArenaClauseRefs smg; rw [hmg.2]; exact hr)
                              (fun _ _ _ => rfl)
                            have hmg_mem : (FullMem c smg ⋆ R) m := hm
                            exact hJm m ⟨smg, hmg.1, dpStatePres_trans hpp hpres_mg, hrest_mg,
                              hmg_mem⟩
                          · c0_hsteps!
                            exact hJm ms ⟨sp, hdwp, hpp, hrest', hmp⟩)
                    · rintro Bk Lk rem_k ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hk_le, rfl, rfl⟩
                      have hsz_c0 : sp.core.arena[(cr.toNat + BitVec.toNat (2 : BitVec 64)) %
                          2 ^ 64]'(by rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) = sz_c :=
                        m6_getElem_congr (by c0_bound) _ _
                      c0_hsplit
                      · have hk_lt : k.toNat < sz_c.toNat := by rw [hsz_c0] at hc; exact hc
                        have hcri : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                            sp.core.arena.length := by
                          rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                        have hcl_lt : (sp.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'
                            hcri).toNat < 2 * sp.core.cur_vars := by
                          have hmem : (sp.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'
                              hcri).toNat ∈ fullArenaClauseLitsCore sp.core cr.toNat := by
                            rw [mem_fullArenaClauseLitsCore_iff (by
                              rw [hdwp.1.core_ok.arena_len_arr]; omega)]
                            exact ⟨k.toNat, by omega, congrArg BitVec.toNat
                              (m6_getElem_congr (by c0_bound) _ _)⟩
                          exact hdwp.2.1.arena.lits_lt cr.toNat href hng _ hmem
                        have hcl_v : ((sp.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'
                            hcri).setWidth 64).toNat < sp.core.vals.length := by
                          rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; c0_bound
                        c0_hsplit
                        · c0_hsteps!; exact hBk (true, k, ()) mk rfl
                        · c0_hsteps!
                          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                          exact hLk (sz_c.toNat - (k + 1#32).toNat) (k + 1#32, ()) mk
                            (by omega) ⟨by omega, rfl, rfl⟩
                      · c0_hsteps!; exact hBk (false, k, ()) mk rfl
                    · intro _ Lk _ hLk; c0_hsteps!
                      exact hLk sz_c.toNat (0#32, ()) mp ⟨Nat.zero_le _, by simp, rfl⟩
          · c0_hsteps!; exact hB2 (p, ()) mp ⟨sp, hdwp, hpp, hmp⟩
        · intro _ L2 _ hL2; c0_hsteps!
          exact hL2 sz_l.toNat (off_l, ()) m1
            ⟨s1, by omega, by omega, hdw1, hp1, by
              rw [hoff_l_eq, hsz_l_eq]
              exact hdw_s1.slices lit.toNat hlit_lt1, hm1⟩
      · -- Loop 1 body: process watch entry at `p` on `nl = lit ^ 1`
        rintro B1 L1 rem ⟨p, ⟨⟩⟩ mp hB1 hL1 ⟨sp, hp_le, hrem, hdwp, hpp, hslice, hmp⟩
        have hlt1 : (s0.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'(by
            rw [hdw0.1.core_ok.wvec_len]; omega)).toNat = off_nl.toNat := by
          rw [hoff_nl_eq]; unfold fullWatchOffCore
          rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega),
            Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr (by rw [hnl_toNat]; omega) _ _)
        have hlt2 : (s0.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by rw [hdw0.1.core_ok.wvec_len]; simp; omega)).toNat = sz_nl.toNat := by
          rw [hsz_nl_eq]; unfold fullWatchSizeCore
          rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.wvec_len]; omega),
            Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr (by simp [hnl_toNat]; omega) _ _)
        have hsum_nl : (off_nl.toNat + sz_nl.toNat) % 2 ^ 64 = end_nl.toNat := by
          rw [Nat.mod_eq_of_lt (by omega), hend_nl_eq]
        c0_hsplit
        · have hp_lt : p.toNat < end_nl.toNat := by
            rw [hlt1, hlt2, hsum_nl] at hc; exact hc
          have hpw : p.toNat < sp.core.wstk.length := by
            rw [hdwp.1.core_ok.wstk_len_arr]; omega
          have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
          cases hslice with
          | empty => omega
          | @bin _ rem1 w0 hwp hflag _ hot_lt hent_bin hrest =>
            have hw0_eq : sp.core.wstk[p.toNat]'hpw = w0 := by
              rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
            let ot := w0 &&& 0x7FFFFFFF#32
            have hot_lt' : ot.toNat < 2 * sp.core.cur_vars := hot_lt
            have hot_v : (ot.setWidth 64).toNat < sp.core.vals.length := by
              rw [hdwp.1.core_ok.vals_len, m6_zext32_toNat]; have := hdwp.1.core_ok.cur_vars_le
              omega
            have hent_ot : (cnfOfClauses F_cur).EntailsClause (cnfClause [ot.toNat]) :=
              m6_resolve_bin_unit (a := lit.toNat) hent_bin hent_lit
            c0_hsplit
            · rw [hw0_eq]
              c0_hsplit
              · have hv_ff : sp.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 := by
                  have hdom := hdwp.2.1.vals_domain ot.toNat hot_lt'
                  have hlt_ov : ot.toNat < sp.core.vals.length := by
                    rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; omega
                  rw [List.getElem?_eq_getElem hlt_ov, Option.getD_some] at hdom ⊢
                  exact m6_bv8_dom_neg_slt hdom hc
                have hneg_ot := m6_vals_neg_entails hdwp.2.1 hdwp.2.2.2.2.2.1 hot_lt' hv_ff
                have hunsat : (cnfOfClauses F_cur).Unsat :=
                  m6_unsat_of_lit_and_neg hent_ot hneg_ot
                c0_hsteps!
                let sinc := { sp with core := { sp.core with inconsistent := 1#64 } }
                exact hret_f sinc _ (m6_fullDenseInvW_set_inc hdwp hunsat)
                  (dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                    rfl, rfl, rfl⟩) (hdwp.2.1.ext_sound.2 hunsat) hm
              · c0_hsplit
                · c0_hsteps_nogrp
                  m6_call hAddUnit
                  refine ⟨c, F0, F_cur, sp, R, rfl, hdwp.1, hdwp.2.1, fun _ => hent_ot, hmp, ?_⟩
                  intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
                    phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m_u su hlen_u hw_u hcl_u
                    hfu _ hm_u
                  have hdw_u : FullDenseInvW c F0 F_cur su :=
                    m6_fullDenseInvW_of_addUnit hdwp hlen_u hw_u hcl_u rfl rfl rfl rfl rfl rfl rfl
                  have hp_u : DpStatePres s0 su :=
                    dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                      rfl, rfl, rfl⟩
                  c0_hsplit
                  · c0_hsteps!
                    have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                      rw [CNF.entails_def]; exact fun _ hx => hx
                    have hrest_u := hrest.mono (k := sp.core) (k' := su.core) hent_r
                      (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl)
                    exact hL1 rem1 (p + 1#64, ()) m_u (by omega)
                      ⟨su, by omega, by omega, hdw_u, hp_u, by rw [hp1_nat]; exact hrest_u, hm_u⟩
                  · c0_hsteps!
                    exact hret_f su m_u hdw_u hp_u (hfu hot_lt' (by simpa using hc)).1 hm_u
                · c0_hsteps!
                  exact hL1 rem1 (p + 1#64, ()) mp (by omega)
                    ⟨sp, by omega, by omega, hdwp, hpp, by rw [hp1_nat]; exact hrest, hmp⟩
            · rw [hw0_eq] at hc; exact absurd hc hflag
          | @occ _ rem2 w0 cr hwp hwp1 hflag _ _ href hrest =>
            have hw0_eq : sp.core.wstk[p.toNat]'hpw = w0 := by
              rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
            have hrem2 : end_nl.toNat - p.toNat = rem2 + 2 := by omega
            have hp1_lt : (p + 1#64).toNat < end_nl.toNat := by omega
            have hp1_w : (p + 1#64).toNat < sp.core.wstk.length := by
              rw [hdwp.1.core_ok.wstk_len_arr]; omega
            have hp1_c0 : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              simp; omega
            have hcr_eq :
                sp.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hdwp.1.core_ok.wstk_len_arr]; omega) = cr := by
              rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.wstk_len_arr]; omega)] at hwp1
              exact (m6_getElem_congr hp1_c0 _ _).trans (Option.some.inj hwp1)
            have hcr_eq' : sp.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_w = cr :=
              (m6_getElem_congr (by c0_bound) _ _).trans hcr_eq
            have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
            have hrest' : DenseWatchSliceOk F_cur sp.core (lit ^^^ 1#32).toNat
                (p + 1#64 + 1#64).toNat rem2 := by
              rw [hp2_nat]; exact hrest
            have hwf_cr := hdwp.2.1.arena.refs_wf cr.toNat href
            have har_le := hdwp.1.core_ok.arena_len_le
            have har_len_cr : cr.toNat < sp.core.arena.length := by
              rw [hdwp.1.core_ok.arena_len_arr]; omega
            have hcr_ar : (cr.setWidth 64).toNat < sp.core.arena.length := by
              rw [hdwp.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
            c0_hsplit
            · rw [hw0_eq] at hc; exact absurd hflag hc
            · c0_hsplit
              · rw [hlt1, hlt2, hsum_nl] at hc; simp at hc; omega
              · c0_hsplit
                · c0_hsteps!
                  exact hL1 rem2 (p + 1#64 + 1#64, ()) mp
                    (by omega) ⟨sp, by omega, by omega, hdwp, hpp, hrest', hmp⟩
                · simp only [hcr_eq, hcr_eq'] at hc ⊢
                  have hng : fullArenaClauseGarb sp cr.toNat = false := by
                    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                    rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                    change (sp.core.arena[cr.toNat]'har_len_cr &&& 0x00080000#32) = 0#32 at hc
                    rw [hc]; rfl
                  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < sp.core.arena.length := by
                    rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                  let sz_c := sp.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
                  have hsz_eq : sz_c.toNat = fullArenaClauseSizeCore sp.core cr.toNat := by
                    unfold sz_c fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
                      Option.getD_some]
                    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                  have hhdr_eq : sp.core.arena[(cr.setWidth 64).toNat]'hcr_ar =
                      fullArenaHdr sp cr.toNat := by
                    unfold fullArenaHdr fullArenaHdrCore
                    rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                    exact m6_getElem_congr (m6_zext32_toNat cr) _ _
                  c0_hsteps_nogrp
                  refine wp_loop_break_group (brkTs := [.bool, i32, i32, i32])
                    (lpTs := [i32, i32, i32])
                    (fun (sat_b, unass_b, ulit_b, k_b, ()) ms => ms = mp ∧
                      (sat_b = false →
                        k_b = sz_c ∧
                        (unass_b = 0#32 → ∀ j < sz_c.toNat,
                          sp.core.vals[(sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat]?.getD
                            0#8 = 0xFF#8) ∧
                        (unass_b = 1#32 →
                          ulit_b.toNat < 2 * sp.core.cur_vars ∧
                          ∀ j < sz_c.toNat,
                            let lj := (sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat
                            lj ≠ ulit_b.toNat → sp.core.vals[lj]?.getD 0#8 = 0xFF#8)))
                    (fun rem_k (unass_k, ulit_k, k, ()) mk =>
                      mk = mp ∧ k.toNat ≤ sz_c.toNat ∧
                      rem_k = sz_c.toNat - k.toNat ∧ unass_k.toNat ≤ k.toNat ∧
                      (unass_k = 0#32 → ∀ j < k.toNat,
                        sp.core.vals[(sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat]?.getD
                          0#8 = 0xFF#8) ∧
                      (unass_k = 1#32 →
                        ulit_k.toNat < 2 * sp.core.cur_vars ∧
                        ∀ j < k.toNat,
                          let lj := (sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat
                          lj ≠ ulit_k.toNat → sp.core.vals[lj]?.getD 0#8 = 0xFF#8))
                    ?_ ?_ ?_
                  · rintro _ ⟨sat_b, unass_b, ulit_b, k_b, ⟨⟩⟩ ms ⟨rfl, hpost⟩
                    refine wp_join0 (P := fun mj => ∃ sm : FullState,
                      FullDenseInvW c F0 F_cur sm ∧ DpStatePres s0 sm ∧
                      DenseWatchSliceOk F_cur sm.core (lit ^^^ 1#32).toNat
                        (p + 1#64 + 1#64).toNat rem2 ∧ (FullMem c sm ⋆ R) mj)
                      (fun _ mj ⟨sm, hdwm, hpm, hrestm, hmm⟩ => by
                        c0_hsteps!
                        exact hL1 rem2 (p + 1#64 + 1#64, ()) mj (by omega)
                          ⟨sm, by omega, by omega, hdwm, hpm, hrestm, hmm⟩)
                      (fun Jm hJm => by
                        c0_hsplit
                        · have hhdr_eq' : sp.core.arena[cr.toNat]'har_len_cr =
                              fullArenaHdr sp cr.toNat := by
                            unfold fullArenaHdr fullArenaHdrCore
                            rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                          c0_hsteps!
                          let ag' := sp.core.arena_garbage + 3#64 + sz_c.setWidth 64
                          let ar' := sp.core.arena.set (cr.setWidth 64).toNat
                            (sp.core.arena[(cr.setWidth 64).toNat]'hcr_ar ||| 0x00080000#32)
                          let smg : FullState :=
                            { sp with core := { sp.core with arena := ar', arena_garbage := ag' } }
                          have har'_eq : ar' = sp.core.arena.set cr.toNat
                              (fullArenaHdr sp cr.toNat ||| 0x00080000#32) := by
                            dsimp only [ar']; rw [← hhdr_eq']
                            have hval := m6_getElem_congr (m6_zext32_toNat cr) hcr_ar har_len_cr
                            rw [hval, m6_zext32_toNat]
                          have hmg := m6_fullDenseInvW_markGarb hdwp href (arena' := ar')
                            (ag' := ag')
                            (by simp [ar', hdwp.1.core_ok.arena_len_arr])
                            (Or.inl (by rw [har'_eq]; exact List.getElem?_set_self har_len_cr))
                            (fun i hne _ => by rw [har'_eq]; exact List.getElem?_set_ne hne.symm)
                          have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                            rw [CNF.entails_def]; exact fun _ hx => hx
                          have hrest_mg := hrest'.mono (k := sp.core) (k' := smg.core) hent_r
                            (Nat.le_refl _) (fun r hr => by
                              change r ∈ fullArenaClauseRefs smg; rw [hmg.2]; exact hr)
                            (fun _ _ _ => rfl)
                          have hmg_mem : (FullMem c smg ⋆ R) m := hm
                          exact hJm m ⟨smg, hmg.1,
                            dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, hmg.2, rfl, rfl,
                              rfl, rfl, rfl, rfl⟩, hrest_mg, hmg_mem⟩
                        · obtain ⟨_, h0, h1⟩ := hpost hc
                          c0_hsplit
                          · have hall_f : ∀ l ∈ fullArenaClauseLitsCore sp.core cr.toNat,
                                sp.core.vals[l]?.getD 0#8 = 0xFF#8 := fun l hl => by
                              rw [mem_fullArenaClauseLitsCore_iff (by
                                rw [hdwp.1.core_ok.arena_len_arr]; omega)] at hl
                              obtain ⟨j, hj, rfl⟩ := hl
                              have hfj := h0 hc j (by omega)
                              have hlt_j : cr.toNat + 3 + j < sp.core.arena.length := by
                                rw [hdwp.1.core_ok.arena_len_arr]; omega
                              rwa [List.getElem?_eq_getElem hlt_j, Option.getD_some] at hfj
                            have hunsat : (cnfOfClauses F_cur).Unsat :=
                              m6_clause_all_false_unsat hdwp.2.1 hdwp.2.2.2.2.2.1
                                (hdwp.2.1.arena.entails cr.toNat href hng)
                                (hdwp.2.1.arena.lits_lt cr.toNat href hng) hall_f
                            c0_hsteps!
                            let sinc := { sp with core := { sp.core with inconsistent := 1#64 } }
                            exact hret_f sinc _ (m6_fullDenseInvW_set_inc hdwp hunsat)
                              (dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                                rfl, rfl, rfl, rfl⟩) (hdwp.2.1.ext_sound.2 hunsat) hm
                          · refine wp_join0 (P := fun mj => ∃ sm : FullState,
                              FullDenseInvW c F0 F_cur sm ∧ DpStatePres s0 sm ∧
                              DenseWatchSliceOk F_cur sm.core (lit ^^^ 1#32).toNat
                                (p + 1#64 + 1#64).toNat rem2 ∧ (FullMem c sm ⋆ R) mj)
                              (fun _ mj h => by c0_hsteps!; exact hJm mj h)
                              (fun _ hJ1 => by
                                c0_hsplit
                                · obtain ⟨hu_lt, hu_oth⟩ := h1 hc
                                  have hent_u : (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause [ulit_b.toNat]) :=
                                    m6_clause_one_unass_entails hdwp.2.1 hdwp.2.2.2.2.2.1
                                      (hdwp.2.1.arena.entails cr.toNat href hng)
                                      (hdwp.2.1.arena.lits_lt cr.toNat href hng) fun l hl hne => by
                                        rw [mem_fullArenaClauseLitsCore_iff (by
                                          rw [hdwp.1.core_ok.arena_len_arr]; omega)] at hl
                                        obtain ⟨j, hj, rfl⟩ := hl
                                        have hfj := hu_oth j (by omega)
                                        have hlt_j : cr.toNat + 3 + j < sp.core.arena.length := by
                                          rw [hdwp.1.core_ok.arena_len_arr]; omega
                                        rw [List.getElem?_eq_getElem hlt_j, Option.getD_some] at hfj
                                        exact hfj hne
                                  have hhdr_eq'' : sp.core.arena[cr.toNat]'har_len_cr =
                                      fullArenaHdr sp cr.toNat := by
                                    unfold fullArenaHdr fullArenaHdrCore
                                    rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                                  c0_hsteps_nogrp
                                  let ag' := sp.core.arena_garbage + 3#64 + sz_c.setWidth 64
                                  let ar' := sp.core.arena.set (cr.setWidth 64).toNat
                                    (sp.core.arena[(cr.setWidth 64).toNat]'hcr_ar ||| 0x00080000#32)
                                  let smg : FullState :=
                                    { sp with core :=
                                      { sp.core with arena := ar', arena_garbage := ag' } }
                                  have har'_eq : ar' = sp.core.arena.set cr.toNat
                                      (fullArenaHdr sp cr.toNat ||| 0x00080000#32) := by
                                    dsimp only [ar']; rw [← hhdr_eq'']
                                    have hval :=
                                      m6_getElem_congr (m6_zext32_toNat cr) hcr_ar har_len_cr
                                    rw [hval, m6_zext32_toNat]
                                  have hmg :=
                                    m6_fullDenseInvW_markGarb hdwp href (arena' := ar') (ag' := ag')
                                      (by simp [ar', hdwp.1.core_ok.arena_len_arr])
                                      (Or.inl (by
                                        rw [har'_eq]; exact List.getElem?_set_self har_len_cr))
                                      (fun i hne _ => by
                                        rw [har'_eq]; exact List.getElem?_set_ne hne.symm)
                                  have hmg_mem : (FullMem c smg ⋆ R) m := hm
                                  m6_call hAddUnit
                                  refine ⟨c, F0, F_cur, smg, R, rfl, hmg.1.1, hmg.1.2.1,
                                    fun _ => hent_u, hmg_mem, ?_⟩
                                  intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass'
                                    unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m_u su
                                    hlen_u hw_u hcl_u hfu _ hm_u
                                  have hdw_u : FullDenseInvW c F0 F_cur su :=
                                    m6_fullDenseInvW_of_addUnit hmg.1 hlen_u hw_u hcl_u
                                      rfl rfl rfl rfl rfl rfl rfl
                                  have hp_u : DpStatePres s0 su :=
                                    dpStatePres_trans hpp ⟨rfl, rfl, rfl, rfl, rfl, rfl, hmg.2, rfl,
                                      rfl, rfl, rfl, rfl, rfl⟩
                                  c0_hsplit
                                  · c0_hsteps!
                                    have hent_r :
                                        (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                                      rw [CNF.entails_def]; exact fun _ hx => hx
                                    have hrest_u := hrest'.mono (k := sp.core) (k' := su.core)
                                      hent_r (Nat.le_refl _) (fun r hr => by
                                        change r ∈ fullArenaClauseRefs smg; rw [hmg.2]; exact hr)
                                      (fun _ _ _ => rfl)
                                    exact hJ1 m_u ⟨su, hdw_u, hp_u, hrest_u, hm_u⟩
                                  · c0_hsteps!
                                    exact hret_f su m_u hdw_u hp_u (hfu hu_lt (by simpa using hc)).1
                                      hm_u
                                · c0_hsteps!
                                  exact hJ1 ms ⟨sp, hdwp, hpp, hrest', hmp⟩))
                  · rintro Bk Lk rem_k ⟨unass_k, ulit_k, k, ⟨⟩⟩ mk hBk hLk
                      ⟨rfl, hk_le, rfl, hun_le, h0k, h1k⟩
                    have hsz_c0 : sp.core.arena[(cr.toNat + BitVec.toNat (2 : BitVec 64)) %
                        2 ^ 64]'(by rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) = sz_c :=
                      m6_getElem_congr (by c0_bound) _ _
                    c0_hsplit
                    · have hk_lt : k.toNat < sz_c.toNat := by rw [hsz_c0] at hc; exact hc
                      have hcri : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                          sp.core.arena.length := by
                        rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                      let cl_k := sp.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hcri
                      have hclk_eq :
                          (sp.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32) = cl_k := by
                        rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
                          Option.getD_some]
                        exact m6_getElem_congr (by c0_bound) _ _
                      have hcl_lt : cl_k.toNat < 2 * sp.core.cur_vars := by
                        have hmem : cl_k.toNat ∈ fullArenaClauseLitsCore sp.core cr.toNat := by
                          rw [mem_fullArenaClauseLitsCore_iff (by
                            rw [hdwp.1.core_ok.arena_len_arr]; omega)]
                          exact ⟨k.toNat, by omega, congrArg BitVec.toNat
                            (m6_getElem_congr (by c0_bound) _ _)⟩
                        exact hdwp.2.1.arena.lits_lt cr.toNat href hng _ hmem
                      have hcl_v : (cl_k.setWidth 64).toNat < sp.core.vals.length := by
                        rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; c0_bound
                      have hdom_k := hdwp.2.1.vals_domain cl_k.toNat hcl_lt
                      have hlt_cv : cl_k.toNat < sp.core.vals.length := by
                        rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; omega
                      have hclk_c0 :
                          sp.core.arena[(cr.toNat + BitVec.toNat (3 : BitVec 64) +
                            k.toNat) % 2 ^ 64]'(by
                              rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) = cl_k :=
                        m6_getElem_congr (by c0_bound) _ _
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      c0_hsplit
                      · c0_hsteps!; exact hBk (true, unass_k, ulit_k, k, ()) mk ⟨rfl, by simp⟩
                      · have hnpos : (BitVec.ofNat 32 0).slt
                            ((sp.core.vals[cl_k.toNat]'hlt_cv).signExtend 32) = false := by
                          simpa only [hclk_c0] using hc
                        refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                          (fun p => (p.1, p.2, ()))
                          (fun p => p.1.toNat ≤ (k + 1#32).toNat ∧
                            (p.1 = 0#32 → ∀ j < (k + 1#32).toNat,
                              sp.core.vals[(sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat]?.getD
                                0#8 = 0xFF#8) ∧
                            (p.1 = 1#32 →
                              p.2.toNat < 2 * sp.core.cur_vars ∧
                              ∀ j < (k + 1#32).toNat,
                                let lj := (sp.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat
                                lj ≠ p.2.toNat → sp.core.vals[lj]?.getD 0#8 = 0xFF#8))
                          (fun _ ⟨un', ul'⟩ ⟨hun', h0', h1'⟩ => by
                            c0_hsteps!
                            exact hLk (sz_c.toNat - (k + 1#32).toNat) (un', ul', k + 1#32, ()) mk
                              (by omega) ⟨rfl, by omega, rfl, hun', h0', h1'⟩)
                          (fun Jv hJv => by
                            c0_hsplit
                            · have hun1 : (unass_k + 1#32).toNat = unass_k.toNat + 1 := by c0_bound
                              c0_hsteps!
                              refine hJv (unass_k + 1#32, cl_k) ⟨by dsimp only; omega, ?_, ?_⟩
                              · intro hz; exfalso
                                have := congrArg BitVec.toNat hz; rw [hun1] at this; simp at this
                              · intro ho
                                have ho0 : unass_k = 0#32 := by
                                  apply BitVec.eq_of_toNat_eq
                                  have := congrArg BitVec.toNat ho; rw [hun1] at this
                                  simp at this ⊢; omega
                                refine ⟨hcl_lt, fun j hj hne => ?_⟩
                                have hj_lt : j < k.toNat := by
                                  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hk1 ▸ hj))
                                    with h | h
                                  · exact h
                                  · subst h; rw [hclk_eq] at hne; exact absurd rfl hne
                                exact h0k ho0 j hj_lt
                            · have hvk_ff : sp.core.vals[cl_k.toNat]?.getD 0#8 = 0xFF#8 := by
                                rw [List.getElem?_eq_getElem hlt_cv, Option.getD_some] at hdom_k ⊢
                                have hc' : (sp.core.vals[cl_k.toNat]'hlt_cv).signExtend 32 ≠
                                    0#32 := by simpa only [hclk_c0] using hc
                                exact m6_bv8_dom_neg_of_not_pos_ne0 hdom_k hnpos hc'
                              c0_hsteps!
                              refine hJv (unass_k, ulit_k) ⟨by dsimp only; omega, ?_, ?_⟩
                              · intro hz j hj
                                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hk1 ▸ hj)) with h | h
                                · exact h0k hz j h
                                · subst h; rw [hclk_eq]; exact hvk_ff
                              · intro ho
                                obtain ⟨hul, hoth⟩ := h1k ho
                                refine ⟨hul, fun j hj hne => ?_⟩
                                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hk1 ▸ hj)) with h | h
                                · exact hoth j h hne
                                · subst h; rw [hclk_eq]; exact hvk_ff)
                    · have hk_eq : k = sz_c := by
                        rw [hsz_c0] at hc; apply BitVec.eq_of_toNat_eq; omega
                      c0_hsteps!
                      exact hBk (false, unass_k, ulit_k, k, ()) mk
                        ⟨rfl, fun _ =>
                          ⟨hk_eq, by subst hk_eq; exact h0k, by subst hk_eq; exact h1k⟩⟩
                  · intro _ Lk _ hLk; c0_hsteps!
                    exact hLk sz_c.toNat (0#32, 0#32, 0#32, ()) mp
                      ⟨rfl, Nat.zero_le _, by simp, Nat.zero_le _,
                       fun _ _ h => by simp at h, fun h => by cases h⟩
        · c0_hsteps!; exact hB1 (p, ()) mp ⟨sp, hdwp, hpp, hmp⟩
      · intro _ L1 _ hL1; c0_hsteps!
        exact hL1 sz_nl.toNat (off_nl, ()) m0
          ⟨s0, by omega, by omega, hdw0, dpStatePres_refl s0, by
            rw [hoff_nl_eq, hsz_nl_eq]
            exact hdw_s0.slices _ hnl_lt, hm0⟩

/-- Parametric `Func.wp` proof for `full_dense_flush_units_m6`. -/
theorem full_dense_flush_units_m6_wp (Γ : Env)
    (hPropUnit : ∀ a m Q X, fullDensePropUnitM6Spec a m Q X →
      Γ "full_dense_prop_unit_m6" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Func.wp Γ full_dense_flush_units_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hprop_le := hdw0.1.core_ok.propagated_le
  have hte_le := hdw0.1.core_ok.trail_end_le
  unfold Func.wp full_dense_flush_units_m6_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem (q, ()) ml => ∃ sl : FullState,
      q.toNat ≤ s0.core.cur_vars ∧ rem = s0.core.cur_vars - q.toNat ∧
      FullDenseInvW c F0 F_cur sl ∧ sl.core.cur_vars = s0.core.cur_vars ∧
      sl.core.arena_len = s0.core.arena_len ∧ sl.core.fuel = s0.core.fuel ∧
      fullArenaClauseRefs sl = fullArenaClauseRefs s0 ∧
      sl.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      sl.scratch.red_refs = s0.scratch.red_refs ∧
      sl.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      sl.scratch.work_stk1 = s0.scratch.work_stk1 ∧
      sl.scratch.work_stk2 = s0.scratch.work_stk2 ∧
      sl.scratch.sim_sig = s0.scratch.sim_sig ∧
      (FullMem c sl ⋆ R) ml)
    ?_ ?_
  · rintro L rem ⟨q, ⟨⟩⟩ ml hL ⟨sl, hq_le, rfl, hdwl, hcvl, hall, hfll, hrefsl, htmkl, hrrl,
      hscrl, hws1l, hws2l, hsigl, hml⟩
    refine wp_join0 (P := fun mb => mb = ml)
      (fun _ mb hmb => by
        subst hmb
        c0_hsteps_nogrp
        have hte_l := hdwl.1.core_ok.trail_end_le
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun pv => (pv, ()))
          (fun pv => pv.toNat ≤ sl.core.trail_end)
          (fun _ pv hpv => by
            c0_hsteps!
            let sf : FullState := { sl with core := { sl.core with propagated := pv.toNat } }
            have hdwf := m6_fullDenseInvW_with_prop hdwl hpv
            exact hQ (sl.core.inconsistent == 0#64) sf _ hdwf hcvl hall hfll hrefsl htmkl hrrl
              hscrl hws1l hws2l hsigl (fun hf => by
                have hne : sl.core.inconsistent ≠ 0#64 := beq_eq_false_iff_ne.mp hf
                exact hdwl.2.1.ext_sound.2 (hdwl.2.1.inconsistent_sound hne)) hm)
          (fun Jp hJp => by
            c0_hsplit
            · c0_hsteps!; exact hJp q (by omega)
            · c0_hsteps!
              exact hJp (BitVec.ofNat 64 sl.core.trail_end) (by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _)))
      (fun B hB => by
        c0_hsplit
        · have hte_l := hdwl.1.core_ok.trail_end_le
          have hq_lt_te : q.toNat < sl.core.trail_end := by
            rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
          c0_hsplit
          · have hq_trl : q.toNat < sl.core.trl.length := by
              rw [hdwl.1.core_ok.trl_len]; omega
            have hq1 : (q + 1#64).toNat = q.toNat + 1 := by c0_bound
            c0_hsteps_nogrp
            m6_call hPropUnit
            refine ⟨c, F0, F_cur, sl, R, rfl, hdwl, hml, ?_⟩
            intro ok s1 m1 hdw1 hcv1 hal1 hfl1 hrefs1 htmk1 hrr1 hscr1 hws11 hws21 hsig1 hf1 hm1
            c0_hsplit
            · c0_hsteps!
              exact hL (s0.core.cur_vars - (q + 1#64).toNat) (q + 1#64, ()) m1 (by omega)
                ⟨s1, by omega, rfl, hdw1, hcv1.trans hcvl, hal1.trans hall, hfl1.trans hfll,
                 hrefs1.trans hrefsl, htmk1.trans htmkl, hrr1.trans hrrl, hscr1.trans hscrl,
                 hws11.trans hws1l, hws21.trans hws2l, hsig1.trans hsigl, hm1⟩
            · c0_hsteps!
              exact hQ false s1 m1 hdw1 (hcv1.trans hcvl) (hal1.trans hall) (hfl1.trans hfll)
                (hrefs1.trans hrefsl) (htmk1.trans htmkl) (hrr1.trans hrrl) (hscr1.trans hscrl)
                (hws11.trans hws1l) (hws21.trans hws2l) (hsig1.trans hsigl)
                (fun _ => hf1 (by simpa using hc)) hm1
          · c0_hsteps!; exact hB ml rfl
        · c0_hsteps!; exact hB ml rfl)
  · intro L hL; c0_hsteps!
    exact hL (s0.core.cur_vars - (BitVec.ofNat 64 s0.core.propagated).toNat)
      (BitVec.ofNat 64 s0.core.propagated, ()) m0
      ⟨s0, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega, rfl,
       hdw0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm0⟩

end Cluster1

end LeanQbe.T.Examples.Kissat.FullM6BveFwd
