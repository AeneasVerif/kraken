/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof0

/-!
# Kissat M7 Hot-Path Fused BCP Proofs — Part 1a (Pure State / Invariant / Memory Helpers)

Zero `import all`, plain `public section` (`0` `@[expose]`).
Provides shared semantic, arithmetic, memory, unit-assign, replacement, overflow, and
finish/chrono transition lemmas for `full_propagate_ignore_hot_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. Arithmetic, List & Trail-End Pigeonhole Helpers -/

theorem m7_list_set_eq_self {α : Type} {xs : List α} {i : Nat} {v : α}
    (hget : xs[i]? = some v) : xs.set i v = xs := by
  by_cases hi : i < xs.length
  · have hv : xs[i]'hi = v := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hget)
    rw [← hv]; exact List.set_getElem_self hi
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt hi)] at hget
    cases hget

theorem m7_bv64_sub_toNat {a b : BitVec 64} (hba : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]
  have ha := a.isLt
  omega

theorem m7_bv64_add_toNat {a b : BitVec 64} (hab : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := bv64_add_toNat hab

theorem m7_bv64_add1_toNat {a : BitVec 64} (ha : a.toNat + 1 < 2 ^ 64) :
    (a + 1#64).toNat = a.toNat + 1 := bv64_add1_toNat ha

theorem m7_bv64_add2_toNat {a : BitVec 64} (ha : a.toNat + 2 < 2 ^ 64) :
    (a + 2#64).toNat = a.toNat + 2 := bv64_add2_toNat ha

theorem m7_bv64_shl1_u32_nat (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := fc_bv64_shl1_u32_nat x

theorem m7_bv64_shl1_add1_nat (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [show (1#64 : BitVec 64) = (1 : BitVec 64) from rfl]
  exact fc_bv64_shl1_add1_nat x

theorem m7_bv32_rshift1_toNat (x : BitVec 32) :
    ((x >>> 1#32).setWidth 64).toNat = x.toNat / 2 := by
  have hx := x.isLt
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem m7_bv32_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem m7_bv64_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem m7_bv32_mask7f_eq {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    x &&& 0x7FFFFFFF#32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from by decide]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 31 |>.trans (Nat.mod_eq_of_lt hx)

private theorem m7_nodup_lt_len :
    ∀ {n : Nat} {l : List Nat}, l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n
  | 0, l, _, hl => by
    cases l with
    | nil => simp
    | cons x _ => exact absurd (hl x (by simp)) (Nat.not_lt_zero _)
  | n + 1, l, hnd, hl => by
    by_cases hmem : n ∈ l
    · have hnd' := hnd.erase n
      have hlt' : ∀ x ∈ l.erase n, x < n := fun x hx => by
        have hne : x ≠ n := fun heq => absurd (heq ▸ hx) hnd.not_mem_erase
        have := hl x (List.erase_subset hx)
        omega
      have hlen' := m7_nodup_lt_len hnd' hlt'
      have hlen_eq : (l.erase n).length + 1 = l.length := by
        have := List.length_erase_of_mem hmem
        have : l.length ≥ 1 := List.length_pos_of_mem hmem
        omega
      omega
    · exact Nat.le_trans (m7_nodup_lt_len hnd fun x hx => by
        have hlt := hl x hx
        have hne : x ≠ n := fun heq => hmem (heq ▸ hx)
        omega) (Nat.le_succ n)

theorem m7_trail_end_lt_of_unassigned {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {other : BitVec 32}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hother : other.toNat < 2 * k.cur_vars) (hun : k.vals[other.toNat]?.getD 0#8 = 0#8) :
    k.trail_end < k.cur_vars := by
  let xs : List Nat := (List.range k.trail_end).map fun i => (k.trl[i]?.getD 0#32).toNat / 2
  have hnd_fn : ∀ n, n ≤ k.trail_end →
      ((List.range n).map fun i => (k.trl[i]?.getD 0#32).toNat / 2).Nodup := by
    intro n hn
    induction n with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.nodup_append]
      refine ⟨ih (Nat.le_of_succ_le hn), by simp, fun a ha b hb heq => ?_⟩
      rw [List.mem_map] at ha
      rw [List.mem_singleton] at hb
      obtain ⟨i, hi, rfl⟩ := ha
      rw [List.mem_range] at hi
      subst hb
      have him := hnw.trail_vars_nodup i m (by change i < k.trail_end; omega)
        (by change m < k.trail_end; omega) heq
      omega
  have hnd_xs : xs.Nodup := hnd_fn k.trail_end (Nat.le_refl _)
  have hnotin : other.toNat / 2 ∉ xs := by
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨i, hi, heq⟩ := hmem
    rw [List.mem_range] at hi
    have hlt_i : (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars := hnw.trail_lits_lt i hi
    have hcases : (k.trl[i]?.getD 0#32).toNat = other.toNat ∨
        (k.trl[i]?.getD 0#32).toNat = other.toNat ^^^ 1 := by
      rw [fc_nat_xor_one]; split <;> omega
    rcases hcases with h1 | h2
    · have ht := (hnw.vals_true_iff other.toNat hother).mpr ⟨i, hi, h1⟩
      rw [hun] at ht; cases ht
    · have hf := (hnw.vals_false_iff other.toNat hother).mpr ⟨i, hi, h2⟩
      rw [hun] at hf; cases hf
  have hnd_cons : (other.toNat / 2 :: xs).Nodup := List.nodup_cons.mpr ⟨hnotin, hnd_xs⟩
  have hlt_all : ∀ x ∈ other.toNat / 2 :: xs, x < k.cur_vars := fun x hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · rw [List.mem_map] at hx
      obtain ⟨i, hi, heq⟩ := hx
      rw [List.mem_range] at hi
      have hlt_i : (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars := hnw.trail_lits_lt i hi
      omega
  have hlen := m7_nodup_lt_len hnd_cons hlt_all
  simp only [List.length_cons, xs, List.length_map, List.length_range] at hlen
  omega

theorem m7_fullConflOkW_of_perm {F_cur : List (List Nat)} {k1 k2 : FullCoreState}
    (hperm : FullPropDecSpecs.FullArenaPermEq k1 k2)
    (hcv : k2.cur_vars = k1.cur_vars) (hvals : k2.vals = k1.vals)
    (hct : k2.confl_type = k1.confl_type) (hcr : k2.confl_ref = k1.confl_ref)
    (hc0 : k2.confl_lit0 = k1.confl_lit0) (hc1 : k2.confl_lit1 = k1.confl_lit1)
    (hconfl : FullPropDecSpecs.FullConflOkW F_cur k1) :
    FullPropDecSpecs.FullConflOkW F_cur k2 := by
  rcases hconfl with hbin | ⟨hct2, href1, hng1, hall1⟩
  · exact Or.inl (by simpa only [hct, hc0, hc1, hcv, hvals] using hbin)
  · have href2 : k2.confl_ref.toNat ∈ fullArenaClauseRefsCore k2 := by
      rw [hcr, hperm.1]; exact href1
    have hpm := hperm.2 k1.confl_ref.toNat href1
    refine Or.inr ⟨hct.trans hct2, href2, ?_, fun l hl => ?_⟩
    · rw [hcr, hpm.2.1]; exact hng1
    · rw [hcr] at hl
      rw [hvals]
      exact hall1 l (hpm.2.2.mem_iff.mp hl)

/-! ## 2. `fastPropMem` Field Preservation & Sync Helpers -/

theorem m7_fastPropMem_propagated (s0 sem : FullState) :
    (fastPropMem s0 sem).core.propagated = sem.core.propagated := rfl

theorem m7_fastPropMem_probing (s0 sem : FullState) :
    (fastPropMem s0 sem).core.probing = sem.core.probing := rfl

theorem m7_fastPropMem_cur_level (s0 sem : FullState) :
    (fastPropMem s0 sem).core.cur_level = sem.core.cur_level := rfl

theorem m7_fastPropMem_fuel (s0 sem : FullState) :
    (fastPropMem s0 sem).core.fuel = sem.core.fuel := rfl

theorem m7_fastPropMem_oom (s0 sem : FullState) :
    (fastPropMem s0 sem).core.oom = sem.core.oom := rfl

theorem m7_fastPropMem_wlen (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wlen = sem.core.wlen := rfl

theorem m7_fastPropMem_confl_type (s0 sem : FullState) :
    (fastPropMem s0 sem).core.confl_type = sem.core.confl_type := rfl

theorem m7_fastPropMem_confl_ref (s0 sem : FullState) :
    (fastPropMem s0 sem).core.confl_ref = sem.core.confl_ref := rfl

theorem m7_fastPropMem_confl_lit0 (s0 sem : FullState) :
    (fastPropMem s0 sem).core.confl_lit0 = sem.core.confl_lit0 := rfl

theorem m7_fastPropMem_confl_lit1 (s0 sem : FullState) :
    (fastPropMem s0 sem).core.confl_lit1 = sem.core.confl_lit1 := rfl

theorem m7_fastPropMem_with_vals (s0 sem : FullState) (vs' : List (BitVec 8)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with vals := vs' } } =
      fastPropMem s0 { sem with core := { sem.core with vals := vs' } } := rfl

theorem m7_fastPropMem_with_flags (s0 sem : FullState) (fl' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with flags := fl' } } =
      fastPropMem s0 { sem with core := { sem.core with flags := fl' } } := rfl

theorem m7_fastPropMem_with_lvl (s0 sem : FullState) (lv' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with lvl := lv' } } =
      fastPropMem s0 { sem with core := { sem.core with lvl := lv' } } := rfl

theorem m7_fastPropMem_with_rsns (s0 sem : FullState) (rs' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with rsns := rs' } } =
      fastPropMem s0 { sem with core := { sem.core with rsns := rs' } } := rfl

theorem m7_fastPropMem_with_trl (s0 sem : FullState) (tr' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with trl := tr' } } =
      fastPropMem s0 { sem with core := { sem.core with trl := tr' } } := rfl

theorem m7_fastPropMem_with_trail_pos (s0 sem : FullState) (tp' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with trail_pos := tp' } } =
      fastPropMem s0 { sem with core := { sem.core with trail_pos := tp' } } := rfl

theorem m7_fastPropMem_with_phases (s0 sem : FullState) (ph' : List (BitVec 8)) :
    { fastPropMem s0 sem with scratch := { (fastPropMem s0 sem).scratch with phases := ph' } } =
      fastPropMem s0 { sem with scratch := { sem.scratch with phases := ph' } } := rfl

theorem m7_fastPropMem_with_oom (s0 sem : FullState) (oom' : BitVec 64) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with oom := oom' } } =
      fastPropMem s0 { sem with core := { sem.core with oom := oom' } } := rfl

/-! ## 3. Shared Unit-Assign Transitions (Binary & Large) -/

theorem m7_bin_assign_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem : FullState} {not_lit blk nl_lvl0 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    {wstk' flags' : List (BitVec 32)} {ph' : List (BitVec 8)} {unas' unfl' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hsw : SplitWatchesInv F_cur { sem.core with wstk := wstk' } not_lit.toNat off_v.toNat
      (q_v.toNat + 1) (p_v.toNat + 1) end_v.toNat)
    (hwstk : wstk'.length = c.wcap) (hfl : flags'.length = c.max_vars)
    (hph : ph'.length = c.max_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hblk_lt : blk.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[blk.toNat]?.getD 0#8 = 0#8)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, blk.toNat]))
    (hp1 : (p_v + 1#64).toNat = p_v.toNat + 1) (hq1 : (q_v + 1#64).toNat = q_v.toNat + 1) :
    let bin_rsn := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let rsn' := if nl_lvl0 = 0#32 then 0xFFFFFFFF#32 else bin_rsn
    let sem2 : FullState :=
      { core :=
          { sem.core with
            wstk := wstk'
            vals := (sem.core.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := sem.core.lvl.set (blk.toNat / 2) nl_lvl0
            rsns := sem.core.rsns.set (blk.toNat / 2) rsn'
            trl := sem.core.trl.set sem.core.trail_end blk
            trail_pos := sem.core.trail_pos.set (blk.toNat / 2) (BitVec.ofNat 32 sem.core.trail_end)
            trail_end := sem.core.trail_end + 1, unassigned := unas', unflushed := unfl' }
        scratch := { sem.scratch with phases := ph' } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v + 1#64).toNat end_v.toNat ∧
    sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
  intro bin_rsn rsn' sem2
  let sem1c := { sem.core with wstk := wstk' }
  have hlen1 : sem1c.LengthsOk c :=
    { hpi.len.core_ok with wstk_len_arr := hwstk }
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1c) :=
    fullWitnessInv_nw_congr hlen1.cur_vars_le hpi.nw rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
  have hstep := full_bin_assign_nw_step hlen1 hnw1 hnot_lt hblk_lt hun hpi.not_f hent
    (flags' := flags') (unas' := unas') (unfl' := unfl')
  have hm := fastPropMem_eq_of_eq (q_v := q_v.toNat + 1) (p_v := p_v.toNat + 1) hpi hsw hwstk
    hfl hph hnot_lt hblk_lt hun hnl (by
      simpa only [sem1c, bin_rsn, rsn', ← hnl] using hstep)
  rw [← hp1, ← hq1] at hm
  dsimp only at hm
  rw [hnl] at hm
  have hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v + 1#64).toNat end_v.toNat := by
    refine PropLitInv.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only [sem2, bin_rsn, rsn']
    · exact hm.1
    · exact hm.2.1
    · exact hm.2.2.1
    · exact hm.2.2.2.1
    · exact hm.2.2.2.2.1
    · exact hm.2.2.2.2.2.1
    · exact hm.2.2.2.2.2.2.1
    · exact hm.2.2.2.2.2.2.2.1
  exact ⟨hpi2, by dsimp only [sem2]; exact hm.2.2.2.2.2.2.2.2⟩

theorem m7_large_assign_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem : FullState} {not_lit other cref alvl nl_lvl0 : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {flags' : List (BitVec 32)} {ph' : List (BitVec 8)}
    {unas' unfl' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat (q_v + 2#64).toNat
      (p_v.toNat + 2) end_v.toNat)
    (hfl : flags'.length = c.max_vars) (hph : ph'.length = c.max_vars)
    (hcr_lt : cref.toNat < 0x80000000) (hcref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hng : fullArenaClauseGarbCore sem.core cref.toNat = false)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hother_lt : other.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[other.toNat]?.getD 0#8 = 0#8)
    (_hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem.core cref.toNat)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem.core cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore sem.core cref.toNat,
      l = other.toNat ∨ sem.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hmax_ge : ∀ l ∈ fullArenaClauseLitsCore sem.core cref.toNat, l ≠ other.toNat →
      (sem.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hmax_att : alvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem.core cref.toNat,
      l ≠ other.toNat ∧ alvl = sem.core.lvl[l / 2]?.getD 0#32) :
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else cref
    let sem2 : FullState :=
      { core :=
          { sem.core with
            vals := (sem.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := sem.core.lvl.set (other.toNat / 2) alvl
            rsns := sem.core.rsns.set (other.toNat / 2) rsn'
            trl := sem.core.trl.set sem.core.trail_end other
            trail_pos := sem.core.trail_pos.set (other.toNat / 2)
              (BitVec.ofNat 32 sem.core.trail_end)
            trail_end := sem.core.trail_end + 1, unassigned := unas', unflushed := unfl' }
        scratch := { sem.scratch with phases := ph' } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat (q_v + 2#64).toNat
      (p_v.toNat + 2) end_v.toNat ∧
    sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
  intro rsn' sem2
  have hstep := full_large_assign_nw_step hpi.len.core_ok hpi.nw hcr_lt hcref hng hother_lt hun
    hnot_lt hpi.not_f hother_mem hunit hmax_ge hmax_att
    (flags' := flags') (unas' := unas') (unfl' := unfl')
  have hsw' : SplitWatchesInv F_cur { sem.core with wstk := sem.core.wstk } not_lit.toNat
      off_v.toNat (q_v + 2#64).toNat (p_v.toNat + 2) end_v.toNat := by
    exact hpi.sw
  have hm := fastPropMem_eq_of_eq (q_v := (q_v + 2#64).toNat) (p_v := p_v.toNat + 2) hpi hsw'
    hpi.len.core_ok.wstk_len_arr hfl hph hnot_lt hother_lt hun hnl (by
      simpa only [sem2, rsn'] using hstep)
  refine ⟨?_, hm.2.2.2.2.2.2.2.2⟩
  exact
    { len := hm.1, nw := hm.2.1, sw := hm.2.2.1, ag := hm.2.2.2.1, tr := hm.2.2.2.2.1,
      perm := hm.2.2.2.2.2.1, sc_eq := hm.2.2.2.2.2.2.1, not_f := hm.2.2.2.2.2.2.2.1 }

theorem m7_nonchrono_alvl_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {cref other not_lit nl_lvl : BitVec 32}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref.toNat = false)
    (hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore k cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l = other.toNat ∨ k.vals[l]?.getD 0#8 = 0xFF#8)
    (hnl : k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hge : nl_lvl.ult (BitVec.ofNat 32 k.cur_level) = false)
    (hcl : k.cur_level < 2 ^ 32) :
    (∀ l ∈ fullArenaClauseLitsCore k cref.toNat, l ≠ other.toNat →
      (k.lvl[l / 2]?.getD 0#32).toNat ≤ nl_lvl.toNat) ∧
    (nl_lvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l ≠ other.toNat ∧ nl_lvl = k.lvl[l / 2]?.getD 0#32) :=
  fastProp_nonchrono_alvl hnw hcref hng hnot_f hun hnot_mem hunit hnl hge hcl

/-! ## 4. Replacement Search / Swap / Inline Push / Overflow Helpers -/

theorem m7_setSrch_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem1 : FullState} {not_lit other cref repl : BitVec 32}
    {ri_n : Nat} {ri32 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (_hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some other)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (_hri2 : 2 ≤ ri_n) (_hri_lt : ri_n < fullArenaClauseSizeCore sem1.core cref.toNat)
    (har_ri : sem1.core.arena[cref.toNat + 3 + ri_n]? = some repl) :
    let sem2 : FullState :=
      { sem1 with core := { sem1.core with arena := sem1.core.arena.set (cref.toNat + 1) ri32 } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat ∧
    sem2.LengthsOk c ∧
    FullPropDecSpecs.FullArenaPermEq sem1.core sem2.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore sem2.core ∧
    fullArenaClauseSizeCore sem2.core cref.toNat = fullArenaClauseSizeCore sem1.core cref.toNat ∧
    sem2.core.arena[cref.toNat + 3]? = some other ∧
    sem2.core.arena[cref.toNat + 4]? = some not_lit ∧
    sem2.core.arena[cref.toNat + 3 + ri_n]? = some repl := by
  intro sem2
  have haren := hpi.len.core_ok.arena_len_arr
  have halen_le := hpi.len.core_ok.arena_len_le
  have hstep := full_setSrch_preserves_nw hpi.len.core_ok hpi.nw (srch := ri32) hcref
  have hlen2 : sem2.LengthsOk c :=
    ⟨{ hpi.len.core_ok with arena_len_arr := by simp [sem2, haren] }, hpi.len.scratch_ok⟩
  have hnw2 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem2.core) :=
    fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hstep.1 rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl
  have hperm2 : FullPropDecSpecs.FullArenaPermEq sem1.core sem2.core := hstep.2
  have hsw2 := hpi.sw.with_nonwatch (k' := sem2.core) rfl rfl rfl rfl hperm2.1
  have hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat :=
    { len := hlen2, nw := hnw2, sw := hsw2
      ag := hpi.ag.update (fun k => { k with arena := sem2.core.arena })
      tr := ⟨hpi.tr.te_ge, hpi.tr.trl_pref, hpi.tr.lvl_pres⟩
      perm := hpi.perm.trans hperm2
      sc_eq := hpi.sc_eq
      not_f := hpi.not_f }
  refine ⟨hpi2, hlen2, hperm2, hperm2.1.symm ▸ hcref, (hperm2.2 _ hcref).1, ?_, ?_, ?_⟩
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har3
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har4
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har_ri

theorem m7_swapCl_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem2 : FullState} {not_lit other repl cref : BitVec 32}
    {ri_n : Nat} {off_v p_v q_v end_v : BitVec 64}
    (hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcref2 : cref.toNat ∈ fullArenaClauseRefsCore sem2.core)
    (hfit2 : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤ sem2.core.arena_len)
    (har3 : sem2.core.arena[cref.toNat + 3]? = some other)
    (har4 : sem2.core.arena[cref.toNat + 4]? = some not_lit)
    (hri2 : 2 ≤ ri_n) (hri_lt : ri_n < fullArenaClauseSizeCore sem2.core cref.toNat)
    (har_ri : sem2.core.arena[cref.toNat + 3 + ri_n]? = some repl) :
    let ar3 := ((sem2.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) repl).set
      (cref.toNat + 3 + ri_n) not_lit
    let st3 : FullState := { sem2 with core := { sem2.core with arena := ar3 } }
    st3.core = { sem2.core with arena := st3.core.arena } ∧
    st3.scratch = sem2.scratch ∧
    st3.LengthsOk c ∧
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core) ∧
    SplitWatchesInv F_cur st3.core not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat ∧
    FullPropDecSpecs.FullArenaPermEq sem2.core st3.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore st3.core := by
  intro ar3 st3
  have haren2 := hpi2.len.core_ok.arena_len_arr
  have halen_le2 := hpi2.len.core_ok.arena_len_le
  have hbd : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤
      sem2.core.arena.length := haren2 ▸ Nat.le_trans hfit2 halen_le2
  have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem2.core cref.toNat :=
    (hpi2.nw.arena.refs_wf _ hcref2).2.1
  have h1_lt : 1 < fullArenaClauseSizeCore sem2.core cref.toNat := by omega
  have hcr1_lt : cref.toNat + 1 < sem2.core.arena.length := by omega
  let srch0 := sem2.core.arena[cref.toNat + 1]'hcr1_lt
  have hswap := full_swapCl_preserves_nw hpi2.len.core_ok hpi2.nw (srch := srch0)
    hcref2 h1_lt hri_lt
  have h1_idx : cref.toNat + 3 + 1 = cref.toNat + 4 := by omega
  have har1_eq : sem2.core.arena[cref.toNat + 3 + 1]'(by omega) = not_lit :=
    Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans (h1_idx ▸ har4))
  have har2_eq : sem2.core.arena[cref.toNat + 3 + ri_n]'(by omega) = repl :=
    Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans har_ri)
  have har_set1 : sem2.core.arena.set (cref.toNat + 1) srch0 = sem2.core.arena :=
    m7_list_set_eq_self (List.getElem?_eq_getElem hcr1_lt)
  have har_set3 : sem2.core.arena.set (cref.toNat + 3) other = sem2.core.arena :=
    m7_list_set_eq_self har3
  have har3_eq : ar3 =
      ((sem2.core.arena.set (cref.toNat + 1) srch0).set (cref.toNat + 3 + 1)
        (sem2.core.arena[cref.toNat + 3 + ri_n]'(by omega))).set (cref.toNat + 3 + ri_n)
        (sem2.core.arena[cref.toNat + 3 + 1]'(by omega)) := by
    simp only [ar3, har_set3, har_set1, h1_idx, har1_eq, har2_eq]
  have hst3_ar : ((sem2.core.arena.set (cref.toNat + 1) srch0).set (cref.toNat + 3 + 1)
        (sem2.core.arena[cref.toNat + 3 + ri_n]'(by omega))).set (cref.toNat + 3 + ri_n)
        (sem2.core.arena[cref.toNat + 3 + 1]'(by omega)) = st3.core.arena := har3_eq.symm
  have hlen3 : st3.LengthsOk c :=
    ⟨{ hpi2.len.core_ok with arena_len_arr := by simp [st3, ar3, haren2] }, hpi2.len.scratch_ok⟩
  have hnw3 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core) :=
    fullWitnessInv_nw_congr hlen3.core_ok.cur_vars_le hswap.1 rfl rfl rfl hst3_ar.symm rfl rfl rfl
      rfl rfl rfl rfl rfl rfl
  have hperm3 : FullPropDecSpecs.FullArenaPermEq sem2.core st3.core := by
    refine ⟨?_, fun r hr => ?_⟩
    · have := hswap.2.1; simp only [st3, ← har3_eq] at this ⊢; exact this
    · have := hswap.2.2 r hr; simp only [st3, ← har3_eq] at this ⊢; exact this
  have hsw3 := hpi2.sw.with_nonwatch (k' := st3.core) rfl rfl rfl rfl hperm3.1
  exact ⟨rfl, rfl, hlen3, hnw3, hsw3, hperm3, hperm3.1.symm ▸ hcref2⟩

theorem m7_ovf_fail_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem2 st4 : FullState} {not_lit other cref ovf_rw : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64}
    (hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen4 : st4.LengthsOk c)
    (hcv4 : st4.core.cur_vars = sem2.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * sem2.core.cur_vars)
    (hlay4 : WatchStackLayout st4.core)
    (hperm24 : FullPropDecSpecs.FullArenaPermEq sem2.core st4.core)
    (hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core))
    (hag4 : AgreesExcept propLitCoreMask s_pi.core st4.core)
    (htr4 : FullPropDecSpecs.FullTrailExt s_pi.core st4.core)
    (hsc4 : st4.scratch = { s_pi.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases })
    (hnot_f4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hovf_lt : ovf_rw.toNat < 2 * sem2.core.cur_vars)
    (hovf_ne : ovf_rw.toNat ≠ not_lit.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref2 : cref.toNat ∈ fullArenaClauseRefsCore sem2.core)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hoth_lt : (other &&& 0x7FFFFFFF#32) = other)
    (hother_pres : ∀ l < 2 * sem2.core.cur_vars, l ≠ ovf_rw.toNat →
      fullWatchSizeCore st4.core l = fullWatchSizeCore sem2.core l ∧
      ∀ k < fullWatchSizeCore sem2.core l,
        st4.core.wstk[fullWatchOffCore st4.core l + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core l + k]?)
    (hovf_pres : fullWatchSizeCore st4.core ovf_rw.toNat =
        fullWatchSizeCore sem2.core ovf_rw.toNat ∧
      ∀ k < fullWatchSizeCore sem2.core ovf_rw.toNat,
        st4.core.wstk[fullWatchOffCore st4.core ovf_rw.toNat + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core ovf_rw.toNat + k]?) :
    let off4_v := st4.core.wvec[2 * not_lit.toNat]?.getD 0#32 |>.setWidth 64
    let q4_v := off4_v + (q_v - off_v)
    let p4_v := off4_v + (p_v + 1#64 + 1#64 - off_v)
    let end4_v := off4_v + (end_v - off_v)
    let st5 : FullState :=
      { st4 with
        core :=
          { st4.core with
            wstk := (st4.core.wstk.set q4_v.toNat other).set (q4_v.toNat + 1) cref } }
    q4_v.toNat < st4.core.wstk.length ∧
    q4_v.toNat + 1 < st4.core.wstk.length ∧
    (q4_v + 1#64).toNat = q4_v.toNat + 1 ∧
    (q4_v + 2#64).toNat = q4_v.toNat + 2 ∧
    off4_v.toNat = fullWatchOffCore st4.core not_lit.toNat ∧
    p4_v.toNat = fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat + 2 - off_v.toNat) ∧
    end4_v.toNat = fullWatchOffCore st4.core not_lit.toNat + (end_v.toNat - off_v.toNat) ∧
    PropLitInv c F0 F_cur s_pi st5 not_lit.toNat off4_v.toNat (q4_v + 2#64).toNat
      p4_v.toNat end4_v.toNat := by
  intro off4_v q4_v p4_v end4_v st5
  have hwvc4 := hlen4.core_ok.wvec_len
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hcv := hpi2.len.core_ok.cur_vars_le
  have hnot_c : not_lit.toNat < 2 * c.max_vars := by omega
  have hidx0_lt : 2 * not_lit.toNat < st4.core.wvec.length := by rw [hwvc4]; omega
  have hoff4_eq : off4_v = (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt).setWidth 64 := by
    simp only [off4_v, List.getElem?_eq_getElem hidx0_lt, Option.getD_some]
  have hsw4_prep := propLit_b1_after_push (c := c) (F_cur := F_cur) (st3 := sem2) (st4 := st4)
    (lit := not_lit ^^^ 1#32) (other := other) (cref := cref) (repl := ovf_rw)
    (off_v := off_v) (p_v := p_v) (q_v := q_v) (end_v := end_v) (pok := false)
    (idx0 := 2 * not_lit.toNat) (by rw [BitVec.xor_assoc]; simp) hcv4
    (by simp [BitVec.xor_assoc, hnot_lt]) hlen4 hlay4
    (by simpa [BitVec.xor_assoc] using hpi2.sw) hperm24.1
    hovf_lt (by simpa [BitVec.xor_assoc] using hovf_ne) hcr_lt hcr_ref2
    hp2_nat hq_le
    (fun l hl hne => hother_pres l hl hne)
    (fun h => False.elim (Bool.false_ne_true h))
    (fun _ => hovf_pres)
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at hsw4_prep
  rw [← hoff4_eq] at hsw4_prep
  rcases hsw4_prep with ⟨hlen_bd4, hoff4_n, hp4_n, hq4_n, hend4_n, hq4_1, hq4_2, hsw4⟩
  have hq4_def : q4_v = off4_v + (q_v - off_v) := rfl
  have hp4_def : p4_v = off4_v + (p_v + 1 + 1 - off_v) := rfl
  have hend4_def : end4_v = off4_v + (end_v - off_v) := rfl
  rw [← hq4_def] at hq4_n hq4_1 hq4_2 hsw4
  rw [← hp4_def] at hp4_n hsw4
  rw [← hend4_def] at hend4_n hsw4
  have hwlen4 := hlen4.core_ok.wlen_le
  have hwstk4 := hlen4.core_ok.wstk_len_arr
  have hq_ge := hpi2.sw.q_ge
  have hp_ge : off_v.toNat ≤ p_v.toNat := Nat.le_trans hq_ge hq_le
  have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat := hpi2.sw.p_le_end
  have hq4_lt : q4_v.toNat < st4.core.wstk.length := by rw [hwstk4, hq4_n]; omega
  have hq41_lt : q4_v.toNat + 1 < st4.core.wstk.length := by rw [hwstk4, hq4_n]; omega
  have hflag0 : other &&& 0x80000000#32 = 0#32 := by
    rw [← hoth_lt]; exact bv32_mask7f_flag0 other
  have hcr_ref4 : cref.toNat ∈ fullArenaClauseRefsCore st4.core := hperm24.1.symm ▸ hcr_ref2
  have hp4_split : p4_v.toNat =
      fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat - off_v.toNat) + 2 := by
    rw [hp4_n]; omega
  have hsw4' : SplitWatchesInv F_cur st4.core not_lit.toNat off4_v.toNat q4_v.toNat
      ((fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat - off_v.toNat)) + 2)
      end4_v.toNat := by rwa [← hp4_split]
  have hsw5 := hsw4'.write_large (hcv4.symm ▸ hnot_lt) (by rw [hq4_n]; omega) hq4_lt hq41_lt
    hflag0 hcr_lt hcr_ref4
  have hq4_2_eq : q4_v.toNat + 2 = (q4_v + 2#64).toNat :=
    (show (q4_v + 2#64).toNat = q4_v.toNat + 2 from hq4_2).symm
  have hsw5' : SplitWatchesInv F_cur st5.core not_lit.toNat off4_v.toNat (q4_v + 2#64).toNat
      p4_v.toNat end4_v.toNat := by
    rw [hp4_split, ← hq4_2_eq]; exact hsw5
  have hlen5 : st5.LengthsOk c :=
    ⟨{ hlen4.core_ok with wstk_len_arr := by simp [st5, hwstk4] }, hlen4.scratch_ok⟩
  have hnw5 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st5.core) :=
    fullWitnessInv_nw_congr hlen5.core_ok.cur_vars_le hnw4 rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl
  refine ⟨hq4_lt, hq41_lt, hq4_1, hq4_2, hoff4_n, hp4_n, hend4_n,
    { len := hlen5, nw := hnw5, sw := hsw5'
      ag := hag4.update (fun k => { k with wstk := st5.core.wstk })
      tr := ⟨htr4.te_ge, htr4.trl_pref, htr4.lvl_pres⟩
      perm := hpi2.perm.trans hperm24
      sc_eq := hsc4
      not_f := hnot_f4 }⟩

theorem m7_ovf_ok_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem2 st4 : FullState} {not_lit other repl cref : BitVec 32}
    {ri_n : Nat} {off_v p_v q_v end_v : BitVec 64}
    (hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen4 : st4.LengthsOk c)
    (hcv4 : st4.core.cur_vars = sem2.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * sem2.core.cur_vars)
    (hlay4 : WatchStackLayout st4.core)
    (hperm24 : FullPropDecSpecs.FullArenaPermEq sem2.core st4.core)
    (hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core))
    (hag4 : AgreesExcept propLitCoreMask s_pi.core st4.core)
    (htr4 : FullPropDecSpecs.FullTrailExt s_pi.core st4.core)
    (hsc4 : st4.scratch = { s_pi.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases })
    (hnot_f4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (har4_eq : st4.core.arena = sem2.core.arena)
    (har_fit2 : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤
      sem2.core.arena_len)
    (hal_4 : st4.core.arena_len = sem2.core.arena_len)
    (har3 : sem2.core.arena[cref.toNat + 3]? = some other)
    (har4 : sem2.core.arena[cref.toNat + 4]? = some not_lit)
    (hri2 : 2 ≤ ri_n) (hri_lt2 : ri_n < fullArenaClauseSizeCore sem2.core cref.toNat)
    (har_ri : sem2.core.arena[cref.toNat + 3 + ri_n]? = some repl)
    (hrepl_lt : repl.toNat < 2 * sem2.core.cur_vars)
    (hrepl_ne : repl.toNat ≠ not_lit.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref2 : cref.toNat ∈ fullArenaClauseRefsCore sem2.core)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (_hoth_lt : (other &&& 0x7FFFFFFF#32) = other)
    (hother_pres : ∀ l < 2 * sem2.core.cur_vars, l ≠ repl.toNat →
      fullWatchSizeCore st4.core l = fullWatchSizeCore sem2.core l ∧
      ∀ k < fullWatchSizeCore sem2.core l,
        st4.core.wstk[fullWatchOffCore st4.core l + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core l + k]?)
    (hrepl_ok : fullWatchSizeCore st4.core repl.toNat = fullWatchSizeCore sem2.core repl.toNat + 2 ∧
      (∀ k < fullWatchSizeCore sem2.core repl.toNat,
        st4.core.wstk[fullWatchOffCore st4.core repl.toNat + k]? =
          sem2.core.wstk[fullWatchOffCore sem2.core repl.toNat + k]?) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore sem2.core repl.toNat]? = some (other &&& 0x7FFFFFFF#32) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore sem2.core repl.toNat + 1]? = some cref) :
    let off4_v := st4.core.wvec[2 * not_lit.toNat]?.getD 0#32 |>.setWidth 64
    let q4_v := off4_v + (q_v - off_v)
    let p4_v := off4_v + (p_v + 1#64 + 1#64 - off_v)
    let end4_v := off4_v + (end_v - off_v)
    let st5 : FullState :=
      { st4 with
        core :=
          { st4.core with
            arena := ((st4.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) repl).set
              (cref.toNat + 3 + ri_n) not_lit } }
    off4_v.toNat = fullWatchOffCore st4.core not_lit.toNat ∧
    q4_v.toNat = fullWatchOffCore st4.core not_lit.toNat + (q_v.toNat - off_v.toNat) ∧
    p4_v.toNat = fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat + 2 - off_v.toNat) ∧
    end4_v.toNat = fullWatchOffCore st4.core not_lit.toNat + (end_v.toNat - off_v.toNat) ∧
    end4_v.toNat - p4_v.toNat = end_v.toNat - (p_v.toNat + 2) ∧
    PropLitInv c F0 F_cur s_pi st5 not_lit.toNat off4_v.toNat q4_v.toNat
      p4_v.toNat end4_v.toNat := by
  intro off4_v q4_v p4_v end4_v st5
  have hwvc4 := hlen4.core_ok.wvec_len
  have hcv := hpi2.len.core_ok.cur_vars_le
  have hnot_c : not_lit.toNat < 2 * c.max_vars := by omega
  have hidx0_lt : 2 * not_lit.toNat < st4.core.wvec.length := by rw [hwvc4]; omega
  have hoff4_eq : off4_v = (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt).setWidth 64 := by
    simp only [off4_v, List.getElem?_eq_getElem hidx0_lt, Option.getD_some]
  have hsw4_prep := propLit_b1_after_push (c := c) (F_cur := F_cur) (st3 := sem2) (st4 := st4)
    (lit := not_lit ^^^ 1#32) (other := other) (cref := cref) (repl := repl)
    (off_v := off_v) (p_v := p_v) (q_v := q_v) (end_v := end_v) (pok := true)
    (idx0 := 2 * not_lit.toNat) (by rw [BitVec.xor_assoc]; simp) hcv4
    (by simp [BitVec.xor_assoc, hnot_lt]) hlen4 hlay4
    (by simpa [BitVec.xor_assoc] using hpi2.sw) hperm24.1
    hrepl_lt (by simpa [BitVec.xor_assoc] using hrepl_ne) hcr_lt hcr_ref2
    hp2_nat hq_le
    (fun l hl hne => hother_pres l hl hne)
    (fun _ => hrepl_ok)
    (fun h => by cases h)
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at hsw4_prep
  rw [← hoff4_eq] at hsw4_prep
  rcases hsw4_prep with ⟨_, hoff4_n, hp4_n, hq4_n, hend4_n, _, _, hsw4⟩
  have hq4_def : q4_v = off4_v + (q_v - off_v) := rfl
  have hp4_def : p4_v = off4_v + (p_v + 1 + 1 - off_v) := rfl
  have hend4_def : end4_v = off4_v + (end_v - off_v) := rfl
  rw [← hq4_def] at hq4_n hsw4
  rw [← hp4_def] at hp4_n hsw4
  rw [← hend4_def] at hend4_n hsw4
  have hpi4 : PropLitInv c F0 F_cur s_pi st4 not_lit.toNat off4_v.toNat q4_v.toNat
      p4_v.toNat end4_v.toNat :=
    { len := hlen4, nw := hnw4, sw := hsw4, ag := hag4, tr := htr4
      perm := hpi2.perm.trans hperm24, sc_eq := hsc4, not_f := hnot_f4 }
  have hcr_ref4 : cref.toNat ∈ fullArenaClauseRefsCore st4.core := hperm24.1.symm ▸ hcr_ref2
  have hpm4 := hperm24.2 cref.toNat hcr_ref2
  have hcsz4_eq : fullArenaClauseSizeCore st4.core cref.toNat =
      fullArenaClauseSizeCore sem2.core cref.toNat := hpm4.1
  have hcsz3_4 : 3 ≤ fullArenaClauseSizeCore st4.core cref.toNat :=
    (hnw4.arena.refs_wf cref.toNat hcr_ref4).2.1
  have hfit4 : cref.toNat + 3 + fullArenaClauseSizeCore st4.core cref.toNat ≤
      st4.core.arena_len := by
    rw [hal_4, hcsz4_eq]; exact har_fit2
  have hri_lt4 : ri_n < fullArenaClauseSizeCore st4.core cref.toNat := hcsz4_eq ▸ hri_lt2
  have har3_4 : st4.core.arena[cref.toNat + 3]? = some other := by rw [har4_eq]; exact har3
  have har4_4 : st4.core.arena[cref.toNat + 4]? = some not_lit := by rw [har4_eq]; exact har4
  have har_ri_4 : st4.core.arena[cref.toNat + 3 + ri_n]? = some repl := by
    rw [har4_eq]; exact har_ri
  have hpi5 := m7_ovf_swap_step hpi4 hcr_ref4 hcsz3_4 hfit4 har3_4 har4_4 hri2 hri_lt4 har_ri_4
  refine ⟨hoff4_n, hq4_n, hp4_n, hend4_n, ?_, hpi5⟩
  have hq_ge := hpi2.sw.q_ge
  have hq_le2 := hpi2.sw.q_le_p
  have hp_le : p_v.toNat + 2 ≤ end_v.toNat := hpi2.sw.p_le_end
  rw [hp4_n, hend4_n]; omega

/-! ## 5. Watch-Compaction Finish & Chrono-Exit Packaging -/

theorem m7_compact_finish_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi st : FullState} {not_lit : BitVec 32} {off_v p_v q_v end_v q_c : BitVec 64}
    {wstk_c wstk_k : List (BitVec 32)}
    (hpi : PropLitInv c F0 F_cur s_pi st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hdense : s_pi.core.dense_mode = 0#64)
    (hnot_lt : not_lit.toNat < 2 * st.core.cur_vars)
    (hwl_k : wstk_k.length = c.wcap)
    (hqc_eq : q_c.toNat = q_v.toNat + (end_v.toNat - p_v.toNat))
    (hpre : ∀ j, off_v.toNat ≤ j → j < q_v.toNat → wstk_c[j]? = st.core.wstk[j]?)
    (hsuf : ∀ j < end_v.toNat - p_v.toNat, wstk_c[q_v.toNat + j]? = st.core.wstk[p_v.toNat + j]?)
    (hout : ∀ j, (j < off_v.toNat ∨ end_v.toNat ≤ j) → wstk_c[j]? = st.core.wstk[j]?)
    (hk_keep : ∀ i, (i < q_c.toNat ∨ end_v.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) :
    let st_fin : FullState :=
      { st with
        core :=
          { st.core with
            wstk := wstk_k
            wvec := st.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
            wusable := st.core.wusable + (end_v - q_c) } }
    st_fin.LengthsOk c ∧
    FullWitnessInv c F0 F_cur st_fin.core ∧
    AgreesExcept propLitCoreMask s_pi.core st_fin.core ∧
    FullPropDecSpecs.FullTrailExt s_pi.core st_fin.core ∧
    FullPropDecSpecs.FullArenaPermEq s_pi.core st_fin.core ∧
    st_fin.core.oom = st.core.oom ∧
    st_fin.core.confl_type = st.core.confl_type ∧
    st_fin.core.confl_ref = st.core.confl_ref ∧
    st_fin.core.confl_lit0 = st.core.confl_lit0 ∧
    st_fin.core.confl_lit1 = st.core.confl_lit1 ∧
    st_fin.core.cur_vars = st.core.cur_vars ∧
    st_fin.core.vals = st.core.vals ∧
    st_fin.core.trail_end = st.core.trail_end ∧
    st_fin.core.unassigned = st.core.unassigned ∧
    st_fin.core.unflushed = st.core.unflushed ∧
    st_fin.core.arena_len = st.core.arena_len ∧
    st_fin.core.cur_level = st.core.cur_level := by
  intro st_fin
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hwlen := hpi.len.core_ok.wlen_le
  have hq_ge := hpi.sw.q_ge
  have hq_le := hpi.sw.q_le_p
  have hp_le := hpi.sw.p_le_end
  have hend_le : end_v.toNat ≤ c.wcap := by
    have := hpi.end_lt_wcap hnot_lt; omega
  have hqc_le : q_c.toNat ≤ end_v.toNat := by omega
  have hqc_sub : (q_c - off_v).toNat = q_v.toNat + (end_v.toNat - p_v.toNat) - off_v.toNat := by
    rw [m7_bv64_sub_toNat (by omega), hqc_eq]
  have hsub_lt32 : q_v.toNat + (end_v.toNat - p_v.toNat) - off_v.toNat < 2 ^ 32 := by omega
  have hsw_pre : ∀ j, off_v.toNat ≤ j → j < q_v.toNat → wstk_k[j]? = st.core.wstk[j]? :=
    fun j hj1 hj2 => (hk_keep j (Or.inl (by omega))).trans (hpre j hj1 hj2)
  have hsw_suf : ∀ j < end_v.toNat - p_v.toNat,
      wstk_k[q_v.toNat + j]? = st.core.wstk[p_v.toNat + j]? := fun j hj =>
    (hk_keep (q_v.toNat + j) (Or.inl (by omega))).trans (hsuf j hj)
  have hsw_out : ∀ j, (j < off_v.toNat ∨ end_v.toNat ≤ j) → wstk_k[j]? = st.core.wstk[j]? :=
    fun j hj => by
      rcases hj with hj | hj
      · exact (hk_keep j (Or.inl (by omega))).trans (hout j (Or.inl hj))
      · exact (hk_keep j (Or.inr hj)).trans (hout j (Or.inr hj))
  have hwat := SplitWatchesInv.finish hpi.sw hnot_lt hpi.len.core_ok.cur_vars_le
    hpi.len.core_ok.wvec_len hwlen hsw_pre hsw_suf hsw_out
    (wu' := st.core.wusable + (end_v - q_c))
  have hset_eq : (q_c - off_v).setWidth 32 =
      BitVec.ofNat 32 (q_v.toNat + (end_v.toNat - p_v.toNat) - off_v.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hqc_sub, Nat.mod_eq_of_lt hsub_lt32]
  have hdm_st : st.core.dense_mode = 0#64 := (hpi.ag.get FullCoreState.dense_mode).trans hdense
  have hst_fin_dm : st_fin.core.dense_mode = 0#64 := hdm_st
  have hnw_fin : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_fin.core) :=
    fullWitnessInv_nw_congr hpi.len.core_ok.cur_vars_le hpi.nw rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl
  have hwat_fin : WatchesInv F_cur st_fin.core := by
    simpa only [st_fin, hset_eq] using hwat
  have hwf_fin := fullWitnessInv_of_nw hnw_fin hst_fin_dm hwat_fin
  have hlen_fin : st_fin.LengthsOk c :=
    ⟨{ hpi.len.core_ok with
        wvec_len := by simp [st_fin, hpi.len.core_ok.wvec_len]
        wstk_len_arr := by simp [st_fin, hwl_k] },
     hpi.len.scratch_ok⟩
  have hag_fin : AgreesExcept propLitCoreMask s_pi.core st_fin.core :=
    hpi.ag.update (fun k =>
      { k with wstk := wstk_k, wvec := st_fin.core.wvec, wusable := st_fin.core.wusable })
  refine ⟨hlen_fin, hwf_fin, hag_fin, ⟨hpi.tr.te_ge, hpi.tr.trl_pref, hpi.tr.lvl_pres⟩,
    hpi.perm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanQbe.T.Examples.Kissat.FullM7BcpHot
