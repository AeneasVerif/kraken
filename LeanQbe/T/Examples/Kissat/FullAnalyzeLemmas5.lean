module

public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Conflict Analysis & OTFS (Part 5)

Proves `otfs_large_shrink_ok`, WatchStack update helpers, and `full_otfs_large_wp`
(`fullOtfsLargeSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

open FullAnalyzeTactics FullAnalyzeSpecs FullAnalyzeHelpers
open scoped FullArenaTactics FullAnalyzeTactics

/-! ## 1. `full_otfs_large` invariant & shrink helpers -/

def otfsActCnt (k : FullCoreState) (cref j : Nat) : Nat :=
  ((List.range j).drop 2).countP fun q =>
    decide (0 < (k.lvl[(k.arena[cref + 3 + q]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)

theorem otfsActCnt_le (k : FullCoreState) (cref j : Nat) : otfsActCnt k cref j ≤ j - 2 := by
  unfold otfsActCnt; refine Nat.le_trans List.countP_le_length ?_
  simp [List.length_drop, List.length_range]

theorem otfsActCnt_succ {k : FullCoreState} {cref j : Nat} (hj : 2 ≤ j) :
    otfsActCnt k cref (j + 1) = otfsActCnt k cref j +
      if 0 < (k.lvl[(k.arena[cref + 3 + j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat then 1
      else 0 := by
  unfold otfsActCnt
  rw [List.range_succ, List.drop_append_of_le_length (by simp [List.length_range]; omega),
    List.countP_append]; simp [List.countP_cons]

theorem otfs_large_swap01 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    {cref l0 uip : BitVec 32} (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip)) :
    let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
    let s1 : FullState := { s with core := { s.core with arena := ar1 } }
    FullWitnessCutInv c F0 F_cur cut s1.core ∧ FullArenaVarsNodup s1 ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
    fullArenaClauseSize s1 cref.toNat = fullArenaClauseSize s cref.toNat ∧
    fullArenaClauseGarb s1 cref.toNat = false ∧
    (∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?) ∧
    ar1[cref.toNat + 3]? = some l0 ∧ ar1[cref.toNat + 4]? = some uip := by
  intro ar1 s1; have hwf := hw.arena.refs_wf cref.toNat hcref
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have h3 : cref.toNat + 3 < s.core.arena.length := by omega
  have h4 : cref.toNat + 4 < s.core.arena.length := by omega
  rcases hs01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ha1 : ar1 = s.core.arena := by
      dsimp only [ar1]; rw [List.getElem?_eq_getElem h3, List.getElem?_eq_getElem h4,
        Option.getD_some, Option.getD_some, List.set_getElem_self, List.set_getElem_self]
    have h0 : s.core.arena[cref.toNat + 3]? = some (s.core.arena[cref.toNat + 3]?.getD 0#32) := by
      rw [List.getElem?_eq_getElem h3, Option.getD_some]
    have h1 : s.core.arena[cref.toNat + 4]? = some (s.core.arena[cref.toNat + 4]?.getD 0#32) := by
      rw [List.getElem?_eq_getElem h4, Option.getD_some]
    simpa only [s1, ha1] using (⟨hw, hnd, rfl, rfl, hng, fun _ _ => rfl, h0, h1⟩ :
      FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
      fullArenaClauseRefs s = fullArenaClauseRefs s ∧
      fullArenaClauseSize s cref.toNat = fullArenaClauseSize s cref.toNat ∧
      fullArenaClauseGarb s cref.toNat = false ∧
      (∀ q, 2 ≤ q → s.core.arena[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?) ∧
      s.core.arena[cref.toNat + 3]? = some (s.core.arena[cref.toNat + 3]?.getD 0#32) ∧
      s.core.arena[cref.toNat + 4]? = some (s.core.arena[cref.toNat + 4]?.getD 0#32))
  · obtain ⟨hw1, hrefs1, hsz1, hng1, hperm1, hother1⟩ :=
      fa_swapCl_preserves_fullWitnessCut hlen.core_ok hw hcref (i := 0) (j := 1)
        (by omega) (by omega)
    have hnd1 : FullArenaVarsNodup s1 := fun r hr hngr => by
      change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs1] at hr
      by_cases hrc : r = cref.toNat
      · subst r; exact (hperm1.map (· / 2)).nodup_iff.mpr (hnd _ hr hng)
      · have ho := hother1 r hr hrc; change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup
        rw [ho.2.2]; exact hnd r hr (by
          change fullArenaClauseGarbCore s.core r = false; rw [← ho.2.1]; exact hngr)
    refine ⟨hw1, hnd1, hrefs1, hsz1, hng1.trans hng, fun q hq => by
        dsimp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
      by dsimp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h3],
      by dsimp only [ar1]; rw [List.getElem?_set_self (by simp [h4])]⟩

private theorem pw_lt_map_nodup {α : Type} (f : Nat → α) (bd : Nat)
    (hinj : ∀ p1 p2, p1 < bd → p2 < bd → f p1 = f p2 → p1 = p2) :
    ∀ l : List Nat, l.Pairwise (· < ·) → (∀ p ∈ l, p < bd) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | p :: l, hpw, hlt => by
    rw [List.pairwise_cons] at hpw; rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, pw_lt_map_nodup f bd hinj l hpw.2 fun q hq =>
      hlt q (List.mem_cons_of_mem _ hq)⟩
    obtain ⟨q, hq, hfeq⟩ := List.mem_map.mp hm
    have heq := hinj q p (hlt q (List.mem_cons_of_mem _ hq)) (hlt p List.mem_cons_self) hfeq
    have := hpw.1 q hq; omega

theorem otfs_large_shrink_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u nsz : Nat} {s s2 : FullState} {cref l0 uip : BitVec 32}
    {ar3 : List (BitVec 32)} {origMap : List Nat}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hlen2 : s2.LengthsOk c)
    (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core) (hnd2 : FullArenaVarsNodup s2)
    (hcv2 : s2.core.cur_vars = s.core.cur_vars) (htrl2 : s2.core.trl = s.core.trl)
    (hrsns2 : s2.core.rsns = s.core.rsns) (hlvl2 : s2.core.lvl = s.core.lvl)
    (hte2 : s2.core.trail_end = s.core.trail_end) (hcl2 : s2.core.cur_level = s.core.cur_level)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hcref2 : cref.toNat ∈ fullArenaClauseRefs s2)
    (hng2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = fullArenaClauseSize s cref.toNat)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hent_f : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
        decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))))
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSize s cref.toNat)
    (hlen_map : origMap.length = nsz) (hpw : origMap.Pairwise (· < ·))
    (hlt_map : ∀ p ∈ origMap, p < fullArenaClauseSize s cref.toNat)
    (h01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip ∧ 0 ∈ origMap ∧ 1 ∉ origMap) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip ∧ 1 ∈ origMap ∧ 0 ∉ origMap))
    (hcov : ∀ p, 2 ≤ p → p < fullArenaClauseSize s cref.toNat →
      0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      p ∈ origMap)
    (hmap_eq : ∀ k, k < nsz →
      ar3[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?)
    (har3_len : ar3.length = c.arena_cap)
    (hhdr3 : ar3[cref.toNat]? = some
      (if (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32 then
        fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32
      else fullArenaHdrCore s2.core cref.toNat))
    (hsz3 : ar3[cref.toNat + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_ne : ∀ j, nsz ≤ j → j < fullArenaClauseSize s cref.toNat - 1 →
      ar3[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hlast_sent : (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32 →
      ar3[cref.toNat + 3 + fullArenaClauseSize s cref.toNat - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) ≠ 0#32 →
      ar3[cref.toNat + 3 + fullArenaClauseSize s cref.toNat - 1]?.getD 0xFFFFFFFF#32 ≠
        0xFFFFFFFF#32)
    (hout : ∀ i, i < cref.toNat ∨ cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ i →
      ar3[i]? = s2.core.arena[i]?) :
    let s3 : FullState := { s2 with core := { s2.core with arena := ar3 } }
    s3.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur idx_u s3.core ∧ FullArenaVarsNodup s3 ∧
    fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s2.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore s3.core ∧
    fullArenaClauseSizeCore s3.core cref.toNat = nsz ∧
    fullArenaClauseGarbCore s3.core cref.toNat = false ∧ ar3[cref.toNat + 3]? = some l0 ∧
    (∀ l ∈ fullArenaClauseLitsCore s3.core cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) ∧
    (ar3[cref.toNat + 4]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
  intro s3; let k3 : FullCoreState := s3.core
  let old_sz := fullArenaClauseSizeCore s.core cref.toNat
  unfold fullArenaClauseSize at hsz2 hnsz_lt hlt_map
  have hwf := hw.arena.refs_wf cref.toNat hcref; have hwf2 := hw2.arena.refs_wf cref.toNat hcref2
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have har2_le := hlen2.core_ok.arena_len_le
  have hold_bd : cref.toNat + 3 + old_sz ≤ s.core.arena_len := by
    have := hwf.2.2.1; have := hwf.2.2.2.1; dsimp only [old_sz]; omega
  have hnsz_s2 : nsz < fullArenaClauseSizeCore s2.core cref.toNat := by
    change fullArenaClauseSizeCore s2.core cref.toNat = old_sz at hsz2; omega
  have hnsz32 : nsz < 2 ^ 32 := by
    have : old_sz < 2 ^ 32 := (s.core.arena[cref.toNat + 2]?.getD 0#32).isLt; omega
  have hlits_rw : fullArenaClauseLits s cref.toNat =
      (List.range old_sz).map fun p => (s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat := by
    have htake : (s.core.arena.drop (cref.toNat + 3)).take old_sz =
        (List.range old_sz).map fun p => s.core.arena[cref.toNat + 3 + p]?.getD 0#32 := by
      refine List.ext_getElem (by simp; omega) fun k _ hk2 => ?_
      simp only [List.length_map, List.length_range] at hk2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    change (((s.core.arena.drop (cref.toNat + 3)).take old_sz).map BitVec.toNat) = _
    rw [htake, List.map_map]; rfl
  have hszv : fullArenaClauseSizeCore k3 cref.toNat = nsz := by
    unfold fullArenaClauseSizeCore k3 s3; rw [hsz3, Option.getD_some, bv32_ofNat_toNat hnsz32]
  have hlits_map : fullArenaClauseLitsCore k3 cref.toNat =
      origMap.map fun p => (s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat := by
    have htake3 : (ar3.drop (cref.toNat + 3)).take nsz =
        origMap.map fun p => s.core.arena[cref.toNat + 3 + p]?.getD 0#32 := by
      refine List.ext_getElem (by simp [har3_len, hlen_map]; omega) fun k _ hk2 => ?_
      simp only [List.length_map, hlen_map] at hk2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map]
      have hmp_lt : origMap[k]'(by omega) < old_sz :=
        hlt_map _ (List.getElem_mem (by omega : k < origMap.length))
      have hm := hmap_eq k hk2
      have hbo : cref.toNat + 3 + origMap[k] < s.core.arena.length := by omega
      rw [List.getElem?_eq_getElem (by rw [har3_len]; omega),
        List.getElem?_eq_getElem (by omega : k < origMap.length), Option.getD_some,
        List.getElem?_eq_getElem hbo] at hm
      exact (Option.some.inj hm).trans (by rw [List.getElem?_eq_getElem hbo, Option.getD_some])
    unfold fullArenaClauseLitsCore; dsimp only [k3, s3]; rw [hszv, htake3, List.map_map]; rfl
  have hinj_old : ∀ p1 p2, p1 < old_sz → p2 < old_sz →
      (s.core.arena[cref.toNat + 3 + p1]?.getD 0#32).toNat / 2 =
      (s.core.arena[cref.toNat + 3 + p2]?.getD 0#32).toNat / 2 → p1 = p2 := by
    have hnd_r := hnd cref.toNat hcref hng; rw [hlits_rw, List.map_map] at hnd_r
    have hget := List.pairwise_iff_getElem.mp (List.pairwise_map.mp hnd_r)
    intro p1 p2 hp1 hp2 heq; exact Classical.byContradiction fun hne =>
      (Nat.lt_or_gt_of_ne hne).elim
        (fun h => hget p1 p2 (by simp; omega) (by simp; omega) h (by simpa using heq))
        (fun h => hget p2 p1 (by simp; omega) (by simp; omega) h (by simpa using heq.symm))
  have hlits_sub : ∀ l ∈ fullArenaClauseLitsCore k3 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat := fun l hl => by
    rw [hlits_map, List.mem_map] at hl; obtain ⟨p, hp_in, rfl⟩ := hl; have hp_lt := hlt_map p hp_in
    refine ⟨fun heq => ?_, by rw [hlits_rw, List.mem_map]; exact ⟨p, List.mem_range.mpr hp_lt, rfl⟩⟩
    rcases h01 with ⟨_, hu4, _, h1no⟩ | ⟨_, hu3, _, h0no⟩
    · exact h1no (hinj_old p 1 hp_lt (by omega) (by rw [heq, hu4]) ▸ hp_in)
    · exact h0no (hinj_old p 0 hp_lt (by omega) (by rw [heq, hu3]) ▸ hp_in)
  have hlits_lt' : ∀ l ∈ fullArenaClauseLitsCore k3 cref.toNat, l < 2 * s2.core.cur_vars :=
    fun l hl => hcv2 ▸ hw.arena.lits_lt cref.toNat hcref hng l (hlits_sub l hl).2
  have hnodup' : ((fullArenaClauseLitsCore k3 cref.toNat).map (· / 2)).Nodup := by
    rw [hlits_map, List.map_map]; exact pw_lt_map_nodup _ old_sz hinj_old origMap hpw hlt_map
  have hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore k3 cref.toNat)) := by
    refine entails_of_mem_or_false hent_f fun l hl => Or.inl ?_
    simp only [List.mem_filter, decide_eq_true_eq] at hl; obtain ⟨hl_mem, hne_u, hcond⟩ := hl
    rw [hlits_rw, List.mem_map] at hl_mem; obtain ⟨p, hp_r, rfl⟩ := hl_mem
    have hp_lt := List.mem_range.mp hp_r
    have hp_in : p ∈ origMap := by
      rcases Nat.lt_trichotomy p 1 with hp0 | rfl | hp2
      · have hpz : p = 0 := by omega
        subst hpz; rcases h01 with ⟨_, _, h0, _⟩ | ⟨_, hu3, _, _⟩
        · exact h0
        · exact absurd (congrArg BitVec.toNat hu3) hne_u
      · rcases h01 with ⟨_, hu4, _, _⟩ | ⟨_, _, h1, _⟩
        · exact absurd (congrArg BitVec.toNat hu4) hne_u
        · exact h1
      · refine hcov p (by omega) hp_lt ?_; rcases hcond with hpos | hl3 | hl4
        · exact hpos
        · have := hinj_old p 0 hp_lt (by omega) (by rw [hl3]); omega
        · have := hinj_old p 1 hp_lt (by omega) (by rw [hl4]); omega
    rw [hlits_map, List.mem_map]; exact ⟨p, hp_in, rfl⟩
  have hna := otfs_nonactive_on_trail hw2 hlen2.core_ok hiu_cut (hte2 ▸ hiu_te)
    (htrl2 ▸ ht_u) (hrsns2 ▸ hr_u) (hlvl2 ▸ hcl2 ▸ hlev_u) hcref2
  obtain ⟨hw3, hrefs3, hsz_3, hng_3, hother3⟩ := fa_inPlaceShrink_preserves_fullWitnessCut
    hw2 hlen2.core_ok (Nat.le_of_lt hiu_cut) hcref2 hng2 hnsz3 hnsz_s2 har3_len hhdr3 hsz3
    (fun j hj1 hj2 => hpad_ne j hj1 (by simpa [hsz2] using hj2))
    (by simpa [hsz2] using hlast_sent) (by simpa [hsz2] using hlast_keep)
    (fun i hi => hout i (by simpa [hsz2] using hi)) hlits_lt' hent'
    (fun idx hi hc => hna idx hi (hc.elim (fun h => Or.inl (by omega)) Or.inr))
  have hnd3 : FullArenaVarsNodup s3 := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s3.core at hr; rw [hrefs3] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact hnodup'
    · have ho := hother3 r hr hrc; change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
      rw [ho.2.2]; exact hnd2 r hr (by
        change fullArenaClauseGarbCore s2.core r = false; rw [← ho.2.1]; exact hngr)
  have hcref3 : cref.toNat ∈ fullArenaClauseRefsCore s3.core := by rw [hrefs3]; exact hcref2
  have har3_l0 : ar3[cref.toNat + 3]? = some l0 := by
    rw [hmap_eq 0 (by omega)]; rcases origMap with _ | ⟨a, tl⟩ <;> simp at hlen_map
    · omega
    · simp only [List.pairwise_cons] at hpw
      rcases h01 with ⟨rfl, _, h0in, _⟩ | ⟨rfl, _, h1in, h0no⟩
      · have ha : a = 0 := (List.mem_cons.mp h0in).elim Eq.symm fun h =>
          absurd (hpw.1 0 h) (Nat.not_lt_zero _)
        simp [ha, List.getElem?_eq_getElem (by omega : cref.toNat + 3 < s.core.arena.length)]
      · have ha : a = 1 := (List.mem_cons.mp h1in).elim Eq.symm fun h => by
          have := hpw.1 1 h; have : a ≠ 0 := fun hz => h0no (hz ▸ List.mem_cons_self); omega
        simp [ha, List.getElem?_eq_getElem (by omega : cref.toNat + 4 < s.core.arena.length)]
  have hm4 : (ar3[cref.toNat + 4]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s3.core cref.toNat := by
    simp only [fullArenaClauseLitsCore, List.mem_map]; dsimp only [s3]
    refine ⟨ar3[cref.toNat + 4]'(by rw [har3_len]; omega), List.mem_iff_getElem.mpr ⟨1,
      by simp [show fullArenaClauseSizeCore { s2.core with arena := ar3 } cref.toNat = nsz from
        hsz_3, har3_len]; omega, by simp [List.getElem_take, List.getElem_drop]⟩,
      by rw [List.getElem?_eq_getElem (by rw [har3_len]; omega), Option.getD_some]⟩
  exact ⟨⟨{ hlen2.core_ok with arena_len_arr := har3_len }, hlen2.scratch_ok⟩, hw3, hnd3,
    hrefs3, hcref3, hsz_3, hng_3, har3_l0, hlits_sub, hcv2 ▸ hw3.arena.lits_lt _ hcref3 hng_3 _ hm4⟩

/-! ## 2. Factored `full_otfs_large` stage & proof -/

private theorem otfs_bv_idx3_64 (cref : BitVec 32) (k : Nat) (hbd : cref.toNat + 3 + k < 2 ^ 32)
    (hk : k < 2 ^ 32) :
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 k).setWidth 64).toNat = cref.toNat + 3 + k := by
  have hz1 : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hz2 : ((BitVec.ofNat 32 k).setWidth 64).toNat = k := by
    rw [zext_toNat _ (by decide), bv32_ofNat_toNat hk]
  bv_omega

private def OtfsShrinkInv (c : FullCfg) (s : FullState) (ar1 : List (BitVec 32))
    (cref l0 uip : BitVec 32) (old_sz r i_nat nsz : Nat)
    (ar_cur : List (BitVec 32)) (origMap : List Nat) : Prop :=
  ar_cur.length = c.arena_cap ∧ r = old_sz - i_nat ∧ 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧
  1 ≤ nsz ∧ nsz = 1 + otfsActCnt s.core cref.toNat i_nat ∧
  origMap.length = nsz ∧ origMap.Pairwise (· < ·) ∧ (∀ p ∈ origMap, p < i_nat) ∧
  ((l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
      s.core.arena[cref.toNat + 4]?.getD 0#32 = uip ∧ 0 ∈ origMap ∧ 1 ∉ origMap) ∨
   (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
      s.core.arena[cref.toNat + 3]?.getD 0#32 = uip ∧ 1 ∈ origMap ∧ 0 ∉ origMap)) ∧
  (∀ p, 2 ≤ p → p < i_nat →
    0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    p ∈ origMap) ∧
  (∀ k, k < nsz →
    ar_cur[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?) ∧
  (∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?)

private theorem otfs_shrink_loop_step {c : FullCfg} {s : FullState} {ar1 ar_cur : List (BitVec 32)}
    {cref l0 uip : BitVec 32} {old_sz i_nat nsz : Nat} {origMap : List Nat}
    (har_len : s.core.arena.length = c.arena_cap) (hinv : OtfsShrinkInv c s ar1 cref l0 uip
      old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap)
    (hilt : i_nat < old_sz) (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hlv : 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat) :
    let ot := s.core.arena[cref.toNat + 3 + i_nat]'(by omega)
    let ar' := ar_cur.set (cref.toNat + 3 + nsz) ot
    OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - (i_nat + 1)) (i_nat + 1) (nsz + 1)
      ar' (origMap ++ [i_nat]) := by
  intro ot ar'
  obtain ⟨har_c, _, hi2, _, hns1, hact, hlm, hpw, hlt_m, h01, hcov, hmapeq, hout⟩ := hinv
  have hnsz_lt_i : nsz < i_nat := by have := otfsActCnt_le s.core cref.toNat i_nat; omega
  have hpw' := List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb => by
    simp only [List.mem_singleton] at hb; subst b; exact hlt_m a ha⟩
  have hlt' : ∀ p ∈ origMap ++ [i_nat], p < i_nat + 1 := fun p hp =>
    (List.mem_append.mp hp).elim (fun h => Nat.lt_succ_of_lt (hlt_m p h)) fun h => by
      simp only [List.mem_singleton] at h; omega
  have h01' : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
      s.core.arena[cref.toNat + 4]?.getD 0#32 = uip ∧ 0 ∈ origMap ++ [i_nat] ∧
      1 ∉ origMap ++ [i_nat]) ∨ (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
      s.core.arena[cref.toNat + 3]?.getD 0#32 = uip ∧ 1 ∈ origMap ++ [i_nat] ∧
      0 ∉ origMap ++ [i_nat]) := by
    rcases h01 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2, List.mem_append.mpr (Or.inl h3), fun hm => by
        rcases List.mem_append.mp hm with h | h <;> simp_all <;> omega⟩
    · exact Or.inr ⟨h1, h2, List.mem_append.mpr (Or.inl h3), fun hm => by
        rcases List.mem_append.mp hm with h | h <;> simp_all <;> omega⟩
  refine ⟨by simp [ar', har_c], rfl, by omega, by omega, by omega,
    by rw [hact, otfsActCnt_succ hi2, ite_eq_left hlv, Nat.add_assoc], by simp [hlm], hpw',
    hlt', h01', fun p hp2 hplt hpos => by
      by_cases hpi : p = i_nat
      · subst p; simp
      · exact List.mem_append.mpr (Or.inl (hcov p hp2 (by omega) hpos)),
    fun k hk => by
      by_cases hkn : k = nsz
      · subst k; dsimp only [ar']
        rw [List.getElem?_set_self (by rw [har_c]; omega), List.getElem?_append_right (by omega)]
        simp [hlm, ot, List.getElem?_eq_getElem (by omega : cref.toNat + 3 + i_nat <
          s.core.arena.length)]
      · dsimp only [ar']; rw [List.getElem?_set_ne (by omega), hmapeq k (by omega),
          List.getElem?_append_left (by omega)],
    fun q hq => by
      dsimp only [ar']; rw [List.getElem?_set_ne (by rcases hq with h | h <;> omega)]
      exact hout q (hq.imp_right (by omega))⟩

private theorem otfs_large_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s' : FullState} {cref uip : BitVec 32}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hvals' : s'.core.vals = s.core.vals) (hlvl' : s'.core.lvl = s.core.lvl)
    (htrl' : s'.core.trl = s.core.trl) (hcl' : s'.core.cur_level = s.core.cur_level)
    (hsub : ∀ l ∈ fullArenaClauseLits s' cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) :
    ∀ l ∈ fullArenaClauseLits s' cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
        ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1) := by
  have hwf := hw.arena.refs_wf cref.toNat hcref; have har_le := hlen.core_ok.arena_len_le
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hcr_lt : cref.toNat < 2 ^ 31 - 1 := by have := hwf.2.2.1; have := hwf.2.2.2.1; omega
  have hrs := hw.reason_inv idx_u hiu_te (Or.inl hiu_cut)
  dsimp only at hrs; rw [ht_u, hr_u] at hrs; have hrs' := hrs (bv32_lit_neq_ff hcr_lt)
  rw [ite_eq_right (fun h => h (bv32_lit_lo31_props (by omega : cref.toNat < 2 ^ 31)).2.2)] at hrs'
  intro l hl; obtain ⟨hne_u, hl_old⟩ := hsub l hl
  have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt cref.toNat hcref hng l hl_old
  rcases hrs'.2.2 l hl_old with rfl | ⟨m, hm, hmeq, _⟩
  · exact absurd rfl hne_u
  · rw [hvals', hlvl', htrl', hcl']
    exact ⟨hne_u, hl_old, (hw.vals_false_iff l hl_lt).mpr ⟨m, by omega, hmeq⟩,
      fun _ => ⟨m, hm, hmeq⟩⟩

private def OtfsHdrPost (c : FullCfg) (s s2 : FullState) (R : Mem 64 → Prop)
    (cref : BitVec 32) (old_sz nsz : Nat) (origMap : List Nat) (ml3 : Mem 64) : Prop :=
  ∃ ar3 : List (BitVec 32),
    (FullMem c { s2 with core := { s2.core with arena := ar3 } } ⋆ R) ml3 ∧
    ar3.length = c.arena_cap ∧
    ar3[cref.toNat]? = some (if (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32
      then fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32
      else fullArenaHdrCore s2.core cref.toNat) ∧
    ar3[cref.toNat + 2]? = some (BitVec.ofNat 32 nsz) ∧
    (∀ k, k < nsz →
      ar3[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?) ∧
    (∀ j, nsz ≤ j → j < old_sz - 1 →
      ar3[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
    ((fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32 →
      ar3[cref.toNat + 3 + old_sz - 1]? = some 0xFFFFFFFF#32) ∧
    ((fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) ≠ 0#32 →
      ar3[cref.toNat + 3 + old_sz - 1]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
    (∀ i, i < cref.toNat ∨ cref.toNat + 3 + old_sz ≤ i → ar3[i]? = s2.core.arena[i]?)

private theorem otfs_large_hdr_ok {c : FullCfg} {s s2 : FullState}
    {ar1 ar_cur ar3_in : List (BitVec 32)} {cref : BitVec 32} {old_sz nsz : Nat}
    {origMap : List Nat} {R : Mem 64 → Prop} {ml3 : Mem 64} (sh0 : Bool)
    (har_len : s.core.arena.length = c.arena_cap) (har_c : ar_cur.length = c.arena_cap)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4 : 4 ≤ old_sz)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < old_sz)
    (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (hmapeq : ∀ k, k < nsz →
      ar_cur[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?)
    (hout_m : ∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?)
    (har1_q : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]?)
    (hhdr_eq : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat))
    (hsh : (sh0 = true ∧ (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32) ∨
      (sh0 = false ∧ (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) ≠ 0#32))
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar3_in } } ⋆ R) ml3)
    (har3_def : ar3_in = if sh0 then
        (((ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32).set
          cref.toNat (fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32)).set
          (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
      else (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32) :
    OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3 := by
  subst har3_def
  have hkeep_s0 : ∀ j, nsz ≤ j → j < old_sz →
      ar_cur[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32 =
        s.core.arena[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32 := fun j hj1 _ => by
    rw [hout_m _ (Or.inr (by omega)), har1_q j (by omega)]
  have hne_old : ∀ j, j < old_sz →
      (s.core.arena[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32) ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hbd : cref.toNat + 3 + j < s.core.arena.length := by omega
    have hi := (hlits_info j hj).2
    rw [List.getElem?_eq_getElem hbd, Option.getD_some] at hi
    rw [List.getElem?_eq_getElem hbd, Option.getD_some]; exact hi
  cases sh0 <;> rcases hsh with ⟨hb, hshv⟩ | ⟨hb, hshv⟩ <;> try exact absurd hb (by decide)
  · let ar3 := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
    refine ⟨ar3, hm, by simp [ar3, har_c], by
      simp [hshv]; dsimp only [ar3]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hhdr_eq,
      by dsimp only [ar3]
         rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [har_c]; omega)],
      fun k hk => by dsimp only [ar3]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]; exact hmapeq k hk,
      fun j hj1 hj2 => by dsimp only [ar3]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), hkeep_s0 j hj1 (by omega)]; exact hne_old j (by omega),
      fun h0 => absurd h0 hshv, fun _ => by
        dsimp only [ar3]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          show cref.toNat + 3 + old_sz - 1 = cref.toNat + 3 + (old_sz - 1) by omega,
          hkeep_s0 (old_sz - 1) (by omega) (by omega)]; exact hne_old (old_sz - 1) (by omega),
      fun i hi => by
        dsimp only [ar3]; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          hout_m i (hi.imp (fun h => by omega) (fun h => by omega))]
        exact har1_s2 i (hi.imp (fun h => by omega) (fun h => by omega))⟩
  · let ar_a := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
    let ar_b := ar_a.set cref.toNat (fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32)
    let ar3 := ar_b.set (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
    have har_al : ar_a.length = c.arena_cap := by simp [ar_a, har_c]
    refine ⟨ar3, hm, by simp [ar3, ar_b, har_al], by
      simp [hshv]; dsimp only [ar3, ar_b]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [har_al]; omega)],
      by dsimp only [ar3, ar_b, ar_a]
         rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
           List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [har_c]; omega)],
      fun k hk => by dsimp only [ar3, ar_b, ar_a]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]; exact hmapeq k hk,
      fun j hj1 hj2 => by dsimp only [ar3, ar_b, ar_a]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), hkeep_s0 j hj1 (by omega)]; exact hne_old j (by omega),
      fun _ => by dsimp only [ar3]; rw [List.getElem?_set_self (by simp [ar_b, har_al]; omega)],
      fun hn => absurd hshv hn, fun i hi => by
        dsimp only [ar3, ar_b, ar_a]
        rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          hout_m i (hi.imp (fun h => by omega) (fun h => by omega))]
        exact har1_s2 i (hi.imp (fun h => by omega) (fun h => by omega))⟩

private theorem otfs_ar_idx3_lt_len {ar : List (BitVec 32)} {cref : BitVec 32}
    {cap old_sz j : Nat} (hcap : cap < 2 ^ 31 - 1) (har : ar.length = cap)
    (hold : cref.toNat + 3 + old_sz ≤ cap) (hj : j < old_sz) :
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 j).setWidth 64).toNat = cref.toNat + 3 + j ∧
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 j).setWidth 64).toNat < ar.length := by
  have hz := otfs_bv_idx3_64 cref j (by omega) (by omega); exact ⟨hz, by rw [hz, har]; omega⟩

private structure OtfsLoop3Bds (c : FullCfg) (ar3 : List (BitVec 32))
    (cref : BitVec 32) (i_n : Nat) : Prop where
  hc1 : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_n % 2 ^ 32) % 2 ^ 64 = cref.toNat + 3 + i_n
  hb1 : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_n % 2 ^ 32) % 2 ^ 64 < ar3.length
  hc2 : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_n).setWidth 64).toNat = cref.toNat + 3 + i_n
  hb2 : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_n).setWidth 64).toNat < ar3.length
  hl1 : (ar3[(cref.toNat + BitVec.toNat (3 : BitVec 64) + i_n % 2 ^ 32) % 2 ^ 64]'hb1).toNat / 2 <
    c.max_vars
  hl2 : (ar3[(cref.setWidth 64 + 3#64 +
    (BitVec.ofNat 32 i_n).setWidth 64).toNat]'hb2).toNat / 2 < c.max_vars

private theorem otfs_large_loop3_bds {c : FullCfg} {ar3 arena0 : List (BitVec 32)}
    {origMap : List Nat} {cref : BitVec 32} {old_sz nsz i_n cv : Nat}
    (hcap : c.arena_cap < 2 ^ 31 - 1) (hcv : cv ≤ c.max_vars)
    (har3_l : ar3.length = c.arena_cap) (hold : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hnsz_lt : nsz < old_sz) (hi_lt : i_n < nsz)
    (hlen_map : origMap.length = nsz) (hlt_m : ∀ p ∈ origMap, p < old_sz)
    (hlits_info : ∀ j < old_sz,
      (arena0[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * cv ∧
      arena0[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (hmap3 : ∀ k, k < nsz →
      ar3[cref.toNat + 3 + k]? = arena0[cref.toNat + 3 + origMap[k]?.getD 0]?) :
    OtfsLoop3Bds c ar3 cref i_n := by
  have hc1 : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_n % 2 ^ 32) % 2 ^ 64 =
      cref.toNat + 3 + i_n := by simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
  have hb1 : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_n % 2 ^ 32) % 2 ^ 64 <
      ar3.length := by rw [hc1, har3_l]; omega
  obtain ⟨hc2, hb2⟩ := otfs_ar_idx3_lt_len (j := i_n) hcap har3_l hold (by omega)
  have hm_orig : origMap[i_n]?.getD 0 = origMap[i_n]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hlt_l : (ar3[cref.toNat + 3 + i_n]?.getD 0#32).toNat < 2 * cv := by
    rw [hmap3 i_n hi_lt, hm_orig]; exact (hlits_info _ (hlt_m _ (List.getElem_mem (by omega)))).1
  have hbd_n : cref.toNat + 3 + i_n < ar3.length := by rw [har3_l]; omega
  rw [List.getElem?_eq_getElem hbd_n, Option.getD_some] at hlt_l
  have hdiv := Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hlt_l) hcv
  exact ⟨hc1, hb1, hc2, hb2, by rw [getElem_eq_of_idx hc1]; exact hdiv,
    by rw [getElem_eq_of_idx hc2]; exact hdiv⟩

private theorem otfs_cr_end_z {ar0 : List (BitVec 32)} {cref : BitVec 32}
    {cap old_sz : Nat} (h3o : cref.toNat + 3 + old_sz ≤ cap) (h4_old : 4 ≤ old_sz)
    (hcap : cap < 2 ^ 31 - 1) (hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2)
    (hcr3_z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hcr2_bd : (cref.setWidth 64 + 2#64).toNat < ar0.length)
    (hsz32 : ar0[cref.toNat + 2]'(by rw [← hcr2_z]; exact hcr2_bd) = BitVec.ofNat 32 old_sz) :
    (cref.setWidth 64 + 3#64 +
      (ar0[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz - 1 := by
  have hsz_at : ar0[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd = BitVec.ofNat 32 old_sz := by
    rw [getElem_eq_of_idx (hj := by rw [← hcr2_z]; exact hcr2_bd) hcr2_z]; exact hsz32
  have hz_s : ((BitVec.ofNat 32 old_sz).setWidth 64).toNat = old_sz := by
    rw [zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
  have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hsum_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64).toNat =
      cref.toNat + 3 + old_sz := by rw [BitVec.toNat_add, hcr3_z, hz_s]; omega
  rw [hsz_at, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1_64, hsum_z]; omega), h1_64, hsum_z]

private theorem getElem_eq_of_list_idx {α : Type} {xs ys : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < ys.length} (hl : xs = ys) (hij : i = j) :
    xs[i]'hi = ys[j]'hj := by subst hl; subst hij; rfl

private theorem otfs_large_loop2_init {c : FullCfg} {s : FullState}
    {cref l0 uip : BitVec 32} {old_sz : Nat}
    (har_len : s.core.arena.length = c.arena_cap)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4_old : 4 ≤ old_sz)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip)) :
    let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
    ∃ origMap, OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - 2) 2 1 ar1 origMap := by
  intro ar1
  have har1_len : ar1.length = c.arena_cap := by simp [ar1, List.length_set, har_len]
  have har1_0 : ar1[cref.toNat + 3]? = some l0 := by
    dsimp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  have hact0 : otfsActCnt s.core cref.toNat 2 = 0 := by
    simp [otfsActCnt, List.drop_eq_nil_of_le (show (List.range 2).length ≤ 2 by simp)]
  rcases hs01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine ⟨[0], har1_len, rfl, Nat.le_refl _, by omega, Nat.le_refl _, by rw [hact0], rfl,
      List.pairwise_singleton _ _, fun p hp => by simp only [List.mem_singleton] at hp; omega,
      Or.inl ⟨h0, h1, by decide, by decide⟩, fun _ _ _ => by omega, fun k hk => ?_, fun _ _ => rfl⟩
    have : k = 0 := by omega
    subst this; rw [Nat.add_zero, har1_0, h0, show ([0][0]? : Option Nat).getD 0 = 0 from rfl,
      Nat.add_zero, List.getElem?_eq_getElem (by omega : cref.toNat + 3 < s.core.arena.length),
      Option.getD_some]
  · refine ⟨[1], har1_len, rfl, Nat.le_refl _, by omega, Nat.le_refl _, by rw [hact0], rfl,
      List.pairwise_singleton _ _, fun p hp => by simp only [List.mem_singleton] at hp; omega,
      Or.inr ⟨h0, h1, by decide, by decide⟩, fun _ _ _ => by omega, fun k hk => ?_, fun _ _ => rfl⟩
    have : k = 0 := by omega
    subst this; rw [Nat.add_zero, har1_0, h0, show ([1][0]? : Option Nat).getD 0 = 1 from rfl,
      List.getElem?_eq_getElem (by omega : cref.toNat + 4 < s.core.arena.length), Option.getD_some]

private theorem otfs_large_j4_swap_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u nsz old_sz hp_n : Nat} {s s3 : FullState} {cref l0 uip : BitVec 32}
    {ar_sw : List (BitVec 32)} {R : Mem 64 → Prop} {ml4 : Mem 64}
    (hlen3 : s3.LengthsOk c) (hw3 : FullWitnessCutInv c F0 F_cur idx_u s3.core)
    (hnd3 : FullArenaVarsNodup s3) (hcref3 : cref.toNat ∈ fullArenaClauseRefs s3)
    (hsz_3 : fullArenaClauseSize s3 cref.toNat = nsz)
    (hng_3 : fullArenaClauseGarb s3 cref.toNat = false)
    (har3_l0 : s3.core.arena[cref.toNat + 3]? = some l0)
    (hlits_3 : ∀ l ∈ fullArenaClauseLits s3 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)
    (har3_s3_l : s3.core.arena.length = c.arena_cap) (_hnsz_lt : nsz < old_sz)
    (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4) (hhp1 : 1 ≤ hp_n)
    (hhp_lt : hp_n < nsz) (h_hp_z : (cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 hp_n).setWidth 64).toNat = cref.toNat + 3 + hp_n)
    (hbd_hp : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
      s3.core.arena.length) (hbd_4 : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length)
    (har_sw : ar_sw = (s3.core.arena.set (cref.setWidth 64 + 4#64).toNat
      (s3.core.arena[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp)).set (cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 hp_n).setWidth 64).toNat
        (s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'hbd_4))
    (hm_sw : (FullMem c { s3 with core := { s3.core with arena := ar_sw } } ⋆ R) ml4) :
    ∃ ar4 : List (BitVec 32),
      (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) ml4 ∧
      ar4.length = c.arena_cap ∧ FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 } ∧
      FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } } ∧
      fullArenaClauseRefsCore { s3.core with arena := ar4 } = fullArenaClauseRefsCore s3.core ∧
      fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz ∧
      fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false ∧
      ar4[cref.toNat + 3]? = some l0 ∧
      (∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) := by
  have h4_s3 : cref.toNat + 4 < s3.core.arena.length := by rw [har3_s3_l]; omega
  have hhp_s3 : cref.toNat + 3 + hp_n < s3.core.arena.length := by rw [har3_s3_l]; omega
  have hget4 : s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'hbd_4 =
      s3.core.arena[cref.toNat + 4]?.getD 0#32 := by
    rw [getElem_eq_of_idx (hj := h4_s3) hcr4_z, List.getElem?_eq_getElem h4_s3, Option.getD_some]
  have hget_hp : s3.core.arena[(cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp =
      s3.core.arena[cref.toNat + 3 + hp_n]?.getD 0#32 := by
    rw [getElem_eq_of_idx (hj := hhp_s3) h_hp_z, List.getElem?_eq_getElem hhp_s3, Option.getD_some]
  let ar4 := (s3.core.arena.set (cref.toNat + 4) (s3.core.arena[cref.toNat + 3 + hp_n]?.getD
    0#32)).set (cref.toNat + 3 + hp_n) (s3.core.arena[cref.toNat + 4]?.getD 0#32)
  have hsw_eq : ar_sw = ar4 := by rw [har_sw]; dsimp only [ar4]; rw [hget4, hget_hp, hcr4_z, h_hp_z]
  let s4 : FullState := { s3 with core := { s3.core with arena := ar4 } }
  obtain ⟨hw4, hrefs4, hsz4, hng4, hperm4, hother4⟩ :=
    fa_swapCl_preserves_fullWitnessCut hlen3.core_ok hw3 hcref3 (i := 1) (j := hp_n)
      (by rw [show fullArenaClauseSizeCore s3.core cref.toNat = nsz from hsz_3]; omega)
      (by rw [show fullArenaClauseSizeCore s3.core cref.toNat = nsz from hsz_3]; exact hhp_lt)
  have hnd4 : FullArenaVarsNodup s4 := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s4.core at hr; rw [hrefs4] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact (hperm4.map (· / 2)).nodup_iff.mpr (hnd3 _ hr hng_3)
    · have ho := hother4 r hr hrc; change ((fullArenaClauseLitsCore s4.core r).map (· / 2)).Nodup
      rw [ho.2.2]; exact hnd3 r hr (by
        change fullArenaClauseGarbCore s3.core r = false; rw [← ho.2.1]; exact hngr)
  exact ⟨ar4, fullMem_of_eq hm_sw (by rw [hsw_eq]) rfl, by simp [ar4, har3_s3_l], hw4, hnd4,
    hrefs4, hsz4.trans hsz_3, hng4.trans hng_3,
    by dsimp only [ar4]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
       exact har3_l0, fun l hl => hlits_3 l (hperm4.mem_iff.mp hl)⟩

private theorem otfs_large_l4_brk_wp {c : FullCfg} {F_cur : List (List Nat)}
    {s5 : FullState} {ws5 ws_brk ar4 : List (BitVec 32)} {cref l0 : BitVec 32}
    {p_n off_n sz_n end_n rem_t : Nat} {R : Mem 64 → Prop} {m_w : Mem 64} {w0_t : BitVec 32}
    (hdm5 : s5.core.dense_mode = 0#64) (hmw5 : ModeWatchesInv F_cur s5.core)
    (hmaxv : c.max_vars < 2 * 2 ^ 28) (hcv5 : s5.core.cur_vars ≤ c.max_vars)
    (hl0_lt5 : l0.toNat < 2 * s5.core.cur_vars)
    (hnl1_lt : (ar4[cref.toNat + 4]?.getD 0#32).toNat < 2 * s5.core.cur_vars)
    (hlo : off_n ≤ p_n) (hp1_lt : p_n + 1 < end_n)
    (hoff : off_n = fullWatchOffCore s5.core l0.toNat)
    (hsz : sz_n = fullWatchSizeCore s5.core l0.toNat) (hend : end_n = off_n + sz_n)
    (hbnd5 : fullWatchOffCore s5.core l0.toNat + fullWatchSizeCore s5.core l0.toNat ≤ s5.core.wlen)
    (hw5_wle : s5.core.wlen ≤ s5.core.wstk.length) (hw5_len : s5.core.wstk.length = c.wcap)
    (hws5_c : s5.core.wstk = ws5) (hcr_lt : cref.toNat < 0x80000000)
    (hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s5.core)
    (hw1 : s5.core.wstk[p_n + 1]? = some cref) (_hw0 : s5.core.wstk[p_n]? = some w0_t)
    (htail : WatchSliceOk F_cur s5.core l0.toNat (p_n + 2) rem_t) (hrem_e : end_n - p_n = rem_t + 2)
    (hcont : ∀ wf : List (BitVec 32), (∀ q < p_n, wf[q]? = ws5[q]?) →
      WatchSliceOk F_cur { s5.core with wstk := wf } l0.toNat p_n (end_n - p_n) →
      WatchSliceOk F_cur { s5.core with wstk := wf } l0.toNat off_n sz_n)
    (hws_brk : ws_brk = ws5.set (BitVec.ofNat 64 p_n + 1 - 1).toNat
      (ar4[cref.toNat + 4]?.getD 0#32 &&& 0x7FFFFFFF#32))
    (hm_w : (FullMem c { s5 with core := { s5.core with wstk := ws_brk } } ⋆ R) m_w) :
    ∃ ws_f : List (BitVec 32),
      (FullMem c { s5 with core := { s5.core with wstk := ws_f } } ⋆ R) m_w ∧
      ws_f.length = c.wcap ∧ ModeWatchesInv F_cur { s5.core with wstk := ws_f } := by
  subst off_n sz_n hend
  let nl1 := ar4[cref.toNat + 4]?.getD 0#32; let b' := nl1 &&& 0x7FFFFFFF#32
  let k' : FullCoreState := { s5.core with wstk := s5.core.wstk.set p_n b' }
  have hp_len : p_n < s5.core.wstk.length := by omega
  have h2cv : 2 * c.max_vars < 2 ^ 31 := by omega
  have hnl1_p := bv32_lit_lo31_props (l := nl1) (by dsimp only [nl1]; omega)
  have hb'_ne : b' ≠ 0xFFFFFFFF#32 := by
    dsimp only [b']; rw [hnl1_p.1]; exact bv32_lit_neq_ff (by dsimp only [nl1]; omega)
  have htail' : WatchSliceOk F_cur k' l0.toNat (p_n + 2) rem_t :=
    fa_watchSlice_relocate (k := s5.core) (k' := k') (by rw [CNF.entails_def]; exact fun _ h => h)
      (Nat.le_refl s5.core.cur_vars) (fun _ r => r)
      (fun idx _ => by dsimp only [k']; rw [List.getElem?_set_ne (by omega)]) htail
  have hslice_p : WatchSliceOk F_cur k' l0.toNat p_n
      (fullWatchOffCore s5.core l0.toNat + fullWatchSizeCore s5.core l0.toNat - p_n) :=
    hrem_e ▸ .large (List.getElem?_set_self hp_len)
      (by dsimp only [k']; rw [List.getElem?_set_ne (by omega)]; exact hw1)
      hnl1_p.2.1 hcr_lt hcref4 htail'
  have hm_brk := fa_modeWatches_set_in_slice hdm5 hmw5 hl0_lt5 hp_len hlo (by omega) hb'_ne
    (hcont k'.wstk (fun q hq => by rw [← hws5_c]; exact List.getElem?_set_ne (by omega)) hslice_p)
  have hp64 : p_n < 2 ^ 64 := by
    unfold fullWatchOffCore fullWatchSizeCore at hp1_lt
    have := (s5.core.wvec[2 * l0.toNat]?.getD 0#32).isLt
    have := (s5.core.wvec[2 * l0.toNat + 1]?.getD 0#32).isLt; omega
  have hceq : ({ s5.core with wstk := ws_brk } : FullCoreState) = k' := by
    dsimp only [k', b', nl1]
    rw [hws_brk, ← hws5_c, show (BitVec.ofNat 64 p_n + 1 - 1).toNat = p_n from by
      rw [show BitVec.ofNat 64 p_n + 1 - 1 = BitVec.ofNat 64 p_n from by bv_omega,
        bv64_ofNat_toNat hp64]]
  exact ⟨ws_brk, hm_w, by rw [hws_brk, List.length_set, ← hws5_c, hw5_len], hceq ▸ hm_brk⟩

private def OtfsLargePost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (idx_u : Nat) (s : FullState) (cref uip : BitVec 32) (R : Mem 64 → Prop) (Q : Post [.bool]) :
    Prop :=
  ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' sc' m',
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', wvec := wvec', wstk := wstk',
                              wlen := wlen', wusable := wu', oom := oom' }
        scratch := sc' }
    s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
    sc'.last_learned = s.scratch.last_learned → sc'.extend_len = s.scratch.extend_len →
    sc'.work_stk2 = s.scratch.work_stk2 → fullArenaClauseRefs s' = fullArenaClauseRefs s →
    (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
      fullArenaClauseGarb s' cref.toNat = false ∧
      ∀ l ∈ fullArenaClauseLits s' cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat ∧
        s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
          ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
    (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

private theorem otfs_large_loop4_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u : Nat} {s5 : FullState} {ws5 ar4 : List (BitVec 32)} {cref l0 : BitVec 32}
    {R : Mem 64 → Prop} {m5 : Mem 64} {J_out : Cont [i64]}
    {hw0_p : (BitVec.setWidth 64 l0 <<< 1).toNat < s5.core.wvec.length}
    {hw1_p : (BitVec.setWidth 64 l0 <<< 1 + 1).toNat < s5.core.wvec.length}
    (hmaxv : c.max_vars < 2 * 2 ^ 28) (hdm5 : s5.core.dense_mode = 0#64)
    (hw5 : FullWitnessCutInv c F0 F_cur idx_u s5.core) (hlen5 : s5.LengthsOk c)
    (hl0_lt5 : l0.toNat < 2 * s5.core.cur_vars)
    (hnl1_lt : (ar4[cref.toNat + 4]?.getD 0#32).toNat < 2 * s5.core.cur_vars)
    (hws5_c : s5.core.wstk = ws5) (hcr_lt : cref.toNat < 0x80000000)
    (hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s5.core) (hm5 : (FullMem c s5 ⋆ R) m5)
    (hJ_out : ∀ xs ml,
      (∃ ws_f : List (BitVec 32),
        (FullMem c { s5 with core := { s5.core with wstk := ws_f } } ⋆ R) ml ∧
        ws_f.length = c.wcap ∧ ModeWatchesInv F_cur { s5.core with wstk := ws_f }) →
      J_out xs ml) :
    wp Γ Q X (Expr.group (fun (Js : Tup Cont [[i64]]) =>
      Blocks.cons (fun (p : Tup Val [i64]) =>
      Expr.let_ (Op.mk (.cmp .ult (.bits 64) .bool rfl) (Arg.var p.fst,
        Arg.var (BitVec.setWidth 64 (s5.core.wvec[(BitVec.setWidth 64 l0 <<< 1).toNat]'hw0_p) +
          BitVec.setWidth 64 (s5.core.wvec[(BitVec.setWidth 64 l0 <<< 1 + 1).toNat]'hw1_p)),
        ())) fun p_1 => Expr.jnz (Arg.var p_1.fst)
        (Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p_2 =>
         Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pWstk, Arg.var p_2.fst, ())) fun p_3 =>
         Expr.load i32 (Arg.var p_3.fst) fun ld =>
         Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
         Expr.group (fun (_ : Tup Cont [[i64]]) => Blocks.cons (fun (p : Tup Val [i64]) =>
           Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_in =>
         Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var ld, Arg.imm 2147483648, ())) fun p_4 =>
         Expr.let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl) (Arg.var p_4.fst, Arg.imm 0, ()))
           fun p_5 => Expr.jnz (Arg.var p_5.fst)
           (Expr.let_ (Op.mk (.cmp .ult (.bits 64) .bool rfl) (Arg.var p.fst,
              Arg.var (BitVec.setWidth 64
                (s5.core.wvec[(BitVec.setWidth 64 l0 <<< 1).toNat]'hw0_p) +
                BitVec.setWidth 64
                (s5.core.wvec[(BitVec.setWidth 64 l0 <<< 1 + 1).toNat]'hw1_p)), ())) fun p_6 =>
            Expr.jnz (Arg.var p_6.fst)
              (Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p_7 =>
               Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pWstk, Arg.var p_7.fst, ())) fun p_8 =>
               Expr.load i32 (Arg.var p_8.fst) fun ld =>
               Expr.let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl) (Arg.var ld, Arg.var cref, ()))
                 fun p_9 => Expr.jnz (Arg.var p_9.fst)
                 (Expr.let_ (Op.mk (.sub (.bits 64)) (Arg.var p.fst, Arg.imm 1, ())) fun p_10 =>
                  Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_10.fst, Arg.imm 4, ())) fun p_11 =>
                  Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pWstk, Arg.var p_11.fst, ()))
                    fun p_12 => Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var
                      (ar4[cref.toNat + 4]?.getD 0#32), Arg.imm 2147483647, ())) fun p_13 =>
                  Expr.store (Arg.var p_13.fst) (Arg.var p_12.fst)
                    (Expr.jump J_out (Arg.var p.fst, ())))
                 (Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                  Expr.jump Js_in.fst (Arg.var p.fst, ())))
              (Expr.jump Js_in.fst (Arg.var p.fst, ())))
           (Expr.jump Js_in.fst (Arg.var p.fst, ())))
        (Expr.jump J_out (Arg.var p.fst, ()))) Blocks.nil) fun Js => Expr.jump Js.fst
        (Arg.var (BitVec.setWidth 64 (s5.core.wvec[(BitVec.setWidth 64 l0 <<< 1).toNat]'hw0_p)),
          ())) m5 := by
  let off_n := fullWatchOffCore s5.core l0.toNat
  let sz_n := fullWatchSizeCore s5.core l0.toNat; let end_n := off_n + sz_n
  have hmw5 := hw5.watches; unfold ModeWatchesInv at hmw5; simp only [hdm5, ↓reduceIte] at hmw5
  have hlay5' := hmw5.layout; have hw5_wvec := hlen5.core_ok.wvec_len
  have hcv_le := hlen5.core_ok.cur_vars_le; have hw5_len := hlen5.core_ok.wstk_len_arr
  have hw5_wle := hlen5.core_ok.wlen_le; have hbnd5 := hlay5'.bounds l0.toNat hl0_lt5
  have hshl0 : (BitVec.setWidth 64 l0 <<< 1).toNat = 2 * l0.toNat := by
    rw [BitVec.toNat_shiftLeft, zext_toNat l0 (by decide), Nat.shiftLeft_eq]; simp; omega
  have hw5_bd0 : 2 * l0.toNat < s5.core.wvec.length := by rw [hw5_wvec]; omega
  have hw5_bd1 : 2 * l0.toNat + 1 < s5.core.wvec.length := by rw [hw5_wvec]; omega
  have hoff5 : (s5.core.wvec[2 * l0.toNat]'hw5_bd0).toNat = off_n := by
    unfold off_n fullWatchOffCore; rw [List.getElem?_eq_getElem hw5_bd0, Option.getD_some]
  have hsz5' : (s5.core.wvec[2 * l0.toNat + 1]'hw5_bd1).toNat = sz_n := by
    unfold sz_n fullWatchSizeCore; rw [List.getElem?_eq_getElem hw5_bd1, Option.getD_some]
  have hwc0 : (s5.core.wvec[2 * l0.toNat % 2 ^ 64]'(by
      rw [Nat.mod_eq_of_lt (by omega)]; exact hw5_bd0)).toNat = off_n := by
    rw [getElem_eq_of_idx (Nat.mod_eq_of_lt (by omega)) (hj := hw5_bd0)]; exact hoff5
  have hwc1 : (s5.core.wvec[(2 * l0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
      rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      exact hw5_bd1)).toNat = sz_n := by
    rw [getElem_eq_of_idx (by rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega)
      (hj := hw5_bd1)]; exact hsz5'
  have hidx0 (pf) : s5.core.wvec[(BitVec.setWidth 64 l0 <<< 1).toNat]'pf =
      s5.core.wvec[2 * l0.toNat]'hw5_bd0 := getElem_eq_of_idx hshl0
  refine wp_loop_group (fun r (pv, ()) ml => ∃ p_n : Nat,
    ml = m5 ∧ r = end_n - p_n ∧ off_n ≤ p_n ∧ p_n ≤ end_n ∧ pv = BitVec.ofNat 64 p_n ∧
    WatchSliceOk F_cur s5.core l0.toNat p_n (end_n - p_n) ∧
    (∀ wf : List (BitVec 32), (∀ q < p_n, wf[q]? = ws5[q]?) →
      WatchSliceOk F_cur { s5.core with wstk := wf } l0.toNat p_n (end_n - p_n) →
      WatchSliceOk F_cur { s5.core with wstk := wf } l0.toNat off_n sz_n)) ?_ ?_
  · rintro L4 r4 ⟨pv, ⟨⟩⟩ ml ih4 ⟨p_n, hml4, rfl, hlo, hle, rfl, hrem, hcont⟩
    subst ml; fa_fast_steps_nogrp
    · have hp_lt : p_n < end_n := by
        have hb : p_n % 2 ^ 64 < ((s5.core.wvec[2 * l0.toNat % 2 ^ 64]'_).toNat +
            (s5.core.wvec[(2 * l0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'_).toNat) %
            2 ^ 64 := ‹_›
        rw [hwc0, hwc1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hb; exact hb
      have hp_bd : p_n < s5.core.wstk.length := by omega
      have hp_z_ws : p_n % 2 ^ 64 < s5.core.wstk.length := by
        rw [Nat.mod_eq_of_lt (by omega)]; exact hp_bd
      fa_fast_steps_nogrp
      refine wp_join_group (ts := [i64]) (fun (pv', ()) ml' =>
        ∃ p_n' : Nat, ml' = m5 ∧ p_n < p_n' ∧ p_n' ≤ end_n ∧ pv' = BitVec.ofNat 64 p_n' ∧
        WatchSliceOk F_cur s5.core l0.toNat p_n' (end_n - p_n') ∧
        (∀ wf : List (BitVec 32), (∀ q < p_n', wf[q]? = ws5[q]?) →
          WatchSliceOk F_cur { s5.core with wstk := wf } l0.toNat p_n' (end_n - p_n') →
          WatchSliceOk F_cur { s5.core with wstk := wf } l0.toNat off_n sz_n)) ?_ ?_
      · rintro _ ⟨pv', ⟨⟩⟩ ml' ⟨p_n', hml', hlt', hle', rfl, hrem', hcont'⟩
        subst ml'; fa_fast_steps; exact ih4 (end_n - p_n') _ m5 (by omega) ⟨p_n', rfl, rfl,
          by omega, hle', rfl, hrem', hcont'⟩
      · intro J4 hJ4
        have hw0_eq_of (hraw : (s5.core.wstk[p_n % 2 ^ 64]'hp_z_ws &&& 0x80000000#32) = 0#32) :
            (s5.core.wstk[p_n]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
          rw [List.getElem?_eq_getElem hp_bd, Option.getD_some]
          exact (congrArg (· &&& 0x80000000#32) (getElem_eq_of_idx
            (Nat.mod_eq_of_lt (by omega)).symm)).trans hraw
        fa_fast_steps
        · have hw0_eq := hw0_eq_of ‹_›
          have hp1_lt : p_n + 1 < end_n := by
            have hb : (p_n + (1 : BitVec 64).toNat) % 2 ^ 64 <
                ((s5.core.wvec[2 * l0.toNat % 2 ^ 64]'_).toNat +
                (s5.core.wvec[(2 * l0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'_).toNat) %
                2 ^ 64 := ‹_›
            rw [hwc0, hwc1, show (1 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hb; exact hb
          have hp1_ws : (p_n + (1 : BitVec 64).toNat) % 2 ^ 64 < s5.core.wstk.length := by
            rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega), hw5_len]
            omega
          have hp1_ws' : (BitVec.ofNat 64 p_n + 1).toNat < s5.core.wstk.length := by
            rw [BitVec.toNat_add, bv64_ofNat_toNat (by omega),
              show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega), hw5_len]
            omega
          have hp0_ws' : (BitVec.ofNat 64 p_n + 1 - 1).toNat < s5.core.wstk.length := by
            rw [show BitVec.ofNat 64 p_n + 1 - 1 = BitVec.ofNat 64 p_n from by bv_omega,
              bv64_ofNat_toNat (by omega)]; exact hp_bd
          fa_fast_steps
          · generalize hrem_e : end_n - p_n = rem_e at hrem; cases hrem with
            | empty => omega
            | bin hw0 hfl => rw [hw0, Option.getD_some] at hw0_eq; exact absurd hw0_eq hfl
            | @large _ rem_t _ cr_t hw0 hw1 hfl _ _ htail =>
              have hcr_idx : (p_n + (1 : BitVec 64).toNat) % 2 ^ 64 = p_n + 1 := by
                rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega
              have hw1_t : s5.core.wstk[p_n + 1]? = some cref := by
                rw [List.getElem?_eq_getElem (by rw [hw5_len]; omega)]
                exact congrArg some ((getElem_eq_of_idx hcr_idx).symm.trans
                  ‹s5.core.wstk[(p_n + (1 : BitVec 64).toNat) % 2 ^ 64]'_ = cref›)
              have hcr_eq : cr_t = cref := Option.some.inj (hw1.symm.trans hw1_t); subst cr_t
              have hm_raw : (FullMem c { s5 with core := { s5.core with
                  wstk := s5.core.wstk.set (BitVec.ofNat 64 p_n + 1 - 1).toNat
                    (ar4[cref.toNat + 4]?.getD 0#32 &&& 0x7FFFFFFF#32) } } ⋆ R) m := by
                assumption
              have hm_b : (FullMem c { s5 with
                    core := { s5.core with
                      wstk := ws5.set (BitVec.ofNat 64 p_n + 1 - 1).toNat
                        (ar4[cref.toNat + 4]?.getD 0#32 &&& 0x7FFFFFFF#32) } } ⋆ R) m :=
                fullMem_of_eq hm_raw (congrArg (fun w => { s5.core with wstk := w })
                  (by rw [hws5_c])) rfl
              exact hJ_out _ _ (otfs_large_l4_brk_wp hdm5 hw5.watches hmaxv hcv_le hl0_lt5
                hnl1_lt hlo hp1_lt rfl rfl rfl hbnd5 (by rw [hw5_len]; exact hw5_wle) hw5_len hws5_c
                hcr_lt hcref4 hw1 hw0 htail hrem_e hcont rfl hm_b)
          · generalize hrem_e : end_n - p_n = rem_e at hrem; cases hrem with
            | empty => omega
            | bin hw0 hfl => rw [hw0, Option.getD_some] at hw0_eq; exact absurd hw0_eq hfl
            | @large _ rem_t _ _ hw0 hw1 hfl hlt hr_t htail =>
              rw [show BitVec.ofNat 64 p_n + 1 + 1 = BitVec.ofNat 64 (p_n + 2) from
                BitVec.eq_of_toNat_eq (by bv_omega)]
              refine hJ4 _ _ ⟨p_n + 2, rfl, by omega, by omega, rfl,
                by simpa only [show end_n - (p_n + 2) = rem_t by omega] using htail,
                fun wf hwf_p hsl_tail => hcont wf (fun q hq => hwf_p q (by omega)) (by
                  rw [show end_n - p_n = (end_n - (p_n + 2)) + 2 by omega]
                  exact .large (by rw [hwf_p p_n (by omega), ← hws5_c]; exact hw0)
                    (by rw [hwf_p (p_n + 1) (by omega), ← hws5_c]; exact hw1)
                    hfl hlt hr_t hsl_tail)⟩
        · have hw0_eq := hw0_eq_of ‹_›
          generalize hrem_e : end_n - p_n = rem_e at hrem; cases hrem with
          | empty => omega
          | bin hw0 hfl => rw [hw0, Option.getD_some] at hw0_eq; exact absurd hw0_eq hfl
          | large =>
            have hba : ¬ (p_n + (1 : BitVec 64).toNat) % 2 ^ 64 <
                ((s5.core.wvec[2 * l0.toNat % 2 ^ 64]'_).toNat +
                (s5.core.wvec[(2 * l0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'_).toNat) %
                2 ^ 64 := ‹_›
            rw [hwc0, hwc1, show (1 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hba; omega
        · have hfl : (s5.core.wstk[p_n]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
            have hraw : (s5.core.wstk[p_n % 2 ^ 64]'hp_z_ws &&& 0x80000000#32) ≠ 0#32 := ‹_›
            rw [List.getElem?_eq_getElem hp_bd, Option.getD_some]
            exact fun he => hraw ((congrArg (· &&& 0x80000000#32) (getElem_eq_of_idx
              (i := p_n % 2 ^ 64) (j := p_n) (Nat.mod_eq_of_lt (by omega)))).trans he)
          generalize hrem_e : end_n - p_n = rem_e at hrem; cases hrem with
          | empty => omega
          | @bin _ rem_t _ hw0 hfl_t hne_t hlt_t hent_t htail =>
            rw [show BitVec.ofNat 64 p_n + 1 = BitVec.ofNat 64 (p_n + 1) from
              BitVec.eq_of_toNat_eq (by bv_omega)]
            refine hJ4 _ _ ⟨p_n + 1, rfl, by omega, by omega, rfl,
              by simpa only [show end_n - (p_n + 1) = rem_t by omega] using htail,
              fun wf hwf_p hsl_tail => hcont wf (fun q hq => hwf_p q (by omega)) (by
                rw [show end_n - p_n = (end_n - (p_n + 1)) + 1 by omega]
                exact .bin (by rw [hwf_p p_n (by omega), ← hws5_c]; exact hw0)
                  hfl_t hne_t hlt_t hent_t hsl_tail)⟩
          | large hw0 _ hfl_t => rw [hw0, Option.getD_some] at hfl; exact absurd hfl_t hfl
    · have hilt : p_n = end_n := by
        have hba : ¬ p_n % 2 ^ 64 < ((s5.core.wvec[2 * l0.toNat % 2 ^ 64]'_).toNat +
            (s5.core.wvec[(2 * l0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'_).toNat) %
            2 ^ 64 := ‹_›
        rw [hwc0, hwc1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hba; omega
      subst p_n
      exact hJ_out _ _ ⟨ws5, fullMem_of_eq hm5 (congrArg (fun w => { s5.core with wstk := w })
        hws5_c) rfl, by rw [← hws5_c, hw5_len], by rw [← hws5_c]; exact hw5.watches⟩
  · intro L4 hL4; fa_fast_steps
    refine hL4 sz_n _ m5 ⟨off_n, rfl, by omega, Nat.le_refl _, by omega, ?_,
      by simpa only [show end_n - off_n = sz_n by omega] using hmw5.slices l0.toNat hl0_lt5,
      fun _ _ hsl => by simpa only [show end_n - off_n = sz_n by omega] using hsl⟩
    rw [hidx0]; apply BitVec.eq_of_toNat_eq
    rw [zext_toNat _ (by decide), hoff5, bv64_ofNat_toNat (by omega)]

private theorem otfs_large_nodup_same_arena {s4 s5 : FullState} {ar : List (BitVec 32)}
    (hs5_ar : s5.core.arena = ar) (hs5_al : s5.core.arena_len = s4.core.arena_len)
    (hs4_ar : s4.core.arena = ar) (hnd4 : FullArenaVarsNodup s4) :
    FullArenaVarsNodup s5 := fun r hr hngr => by
  have hrf : fullArenaClauseRefsCore s5.core = fullArenaClauseRefsCore s4.core := by
    simp [fullArenaClauseRefsCore, hs5_ar, hs5_al, hs4_ar]
  have hgr : fullArenaClauseGarb s4 r = false := by
    dsimp only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore] at hngr ⊢
    rw [hs4_ar, ← hs5_ar]; exact hngr
  change r ∈ fullArenaClauseRefsCore s5.core at hr; rw [hrf] at hr
  change ((fullArenaClauseLitsCore s5.core r).map (· / 2)).Nodup
  have hl : fullArenaClauseLitsCore s5.core r = fullArenaClauseLitsCore s4.core r := by
    simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs5_ar, hs4_ar]
  rw [hl]; exact hnd4 r hr hgr

private theorem otfs_large_fin_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s4 s5 : FullState} {ar4 wv5 ws_f wso5 : List (BitVec 32)}
    {wu5 : BitVec 64} {wl5 : Nat} {cref uip : BitVec 32} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {m_sc : Mem 64}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hs4_ar : s4.core.arena = ar4) (hs4_sc : s4.scratch = s.scratch)
    (hs4_base : ∃ wv2 ws2 wu2,
      s4.core = { s.core with arena := ar4, wvec := wv2, wstk := ws2, wusable := wu2 })
    (hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s) (hnd4 : FullArenaVarsNodup s4)
    (hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s4.core)
    (hng4 : fullArenaClauseGarb s4 cref.toNat = false)
    (hlits4 : ∀ l ∈ fullArenaClauseLits s4 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)
    (hs5_c : s5.core =
      { s4.core with wvec := wv5, wstk := s5.core.wstk, wlen := wl5, wusable := wu5 })
    (hs5_sc : s5.scratch = { s4.scratch with wsort := wso5 })
    (hw5 : FullWitnessCutInv c F0 F_cur idx_u s5.core) (hlen5' : s5.LengthsOk c)
    (hws_fl : ws_f.length = c.wcap) (hmw_f : ModeWatchesInv F_cur { s5.core with wstk := ws_f })
    (hm_sc : (FullMem c
      { s5 with core := { s5.core with wstk := ws_f }
                scratch := { s5.scratch with otfs_cnt := s5.scratch.otfs_cnt + 1#64 } } ⋆ R) m_sc)
    (hQ : OtfsLargePost c F0 F_cur idx_u s cref uip R Q) : Q (true, ()) m_sc := by
  obtain ⟨wv2, ws2, wu2, hs4_core⟩ := hs4_base
  let k_fin : FullCoreState :=
    { s.core with
      arena := ar4, wvec := wv5, wstk := ws_f, wlen := wl5, wusable := wu5, oom := s.core.oom }
  let sc_fin : FullScratch :=
    { s.scratch with wsort := wso5, otfs_cnt := s5.scratch.otfs_cnt + 1#64 }
  let s_fin : FullState := { s with core := k_fin, scratch := sc_fin }
  have hk_eq : k_fin = { s5.core with wstk := ws_f } := by dsimp only [k_fin]; rw [hs5_c, hs4_core]
  have hsc_eq : sc_fin = { s5.scratch with otfs_cnt := s5.scratch.otfs_cnt + 1#64 } := by
    dsimp only [sc_fin]; rw [hs5_sc, hs4_sc]
  have hm_f' : (FullMem c s_fin ⋆ R) m_sc := fullMem_of_eq hm_sc hk_eq.symm hsc_eq.symm
  have hw_f : FullWitnessCutInv c F0 F_cur idx_u s_fin.core := by
    change FullWitnessCutInv c F0 F_cur idx_u k_fin; rw [hk_eq]
    exact { hw5 with arena := { hw5.arena with len_ok := hw5.arena.len_ok }, watches := hmw_f }
  have hlen_f : s_fin.LengthsOk c := by
    change ({ s with core := k_fin, scratch := sc_fin } : FullState).LengthsOk c; rw [hk_eq, hsc_eq]
    exact ⟨{ hlen5'.core_ok with wstk_len_arr := hws_fl }, { hlen5'.scratch_ok with }⟩
  have hnd_f := otfs_large_nodup_same_arena (s4 := s4) (s5 := s_fin) (ar := ar4)
    rfl (by dsimp only [s_fin, k_fin]; rw [hs4_core]) hs4_ar hnd4
  have hrefs_s4 : fullArenaClauseRefsCore s_fin.core = fullArenaClauseRefsCore s4.core := by
    change fullArenaClauseRefsCore k_fin = _; rw [hk_eq, hs5_c]; rfl
  have hcref_f : cref.toNat ∈ fullArenaClauseRefs s_fin := by
    change cref.toNat ∈ fullArenaClauseRefsCore s_fin.core; rw [hrefs_s4]; exact hcref4
  have hng_f : fullArenaClauseGarb s_fin cref.toNat = false := by
    dsimp only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, s_fin, k_fin]
      at hng4 ⊢
    rw [← hs4_ar]; exact hng4
  have hlits_f := otfs_large_fin hlen hw hcref hng hiu_cut hiu_te ht_u hr_u (s' := s_fin)
    rfl rfl rfl rfl (fun l hl => hlits4 l (by
      dsimp only [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_fin,
        k_fin] at hl ⊢
      rw [← hs4_ar] at hl; exact hl))
  exact hQ true ar4 wv5 ws_f wl5 wu5 s.core.oom sc_fin m_sc hlen_f hw_f hnd_f rfl rfl rfl
    (hrefs_s4.trans hrefs4) (fun _ => ⟨hcref_f, hng_f, hlits_f⟩) hm_f'

private theorem otfs_large_oom_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u : Nat} {s s4 s5 : FullState} {ar4 wv5 ws5 wso5 : List (BitVec 32)}
    {wu5 : BitVec 64} {wl5 : Nat} {cref uip : BitVec 32} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {m_o : Mem 64} (hs4_ar : s4.core.arena = ar4) (hs4_sc : s4.scratch = s.scratch)
    (hs4_base : ∃ wv2 ws2 wu2,
      s4.core = { s.core with arena := ar4, wvec := wv2, wstk := ws2, wusable := wu2 })
    (hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s) (hnd4 : FullArenaVarsNodup s4)
    (hs5_c : s5.core =
      { s4.core with wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5, oom := 1#64 })
    (hs5_sc : s5.scratch = { s4.scratch with wsort := wso5 })
    (hw5 : FullWitnessCutInv c F0 F_cur idx_u s5.core) (hlen5' : s5.LengthsOk c)
    (hm_o : (FullMem c s5 ⋆ R) m_o)
    (hQ : OtfsLargePost c F0 F_cur idx_u s cref uip R Q) : Q (false, ()) m_o := by
  obtain ⟨wv2, ws2, wu2, hs4_core⟩ := hs4_base
  let k_o : FullCoreState := { s.core with
      arena := ar4, wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5, oom := 1#64 }
  let sc_o : FullScratch := { s.scratch with wsort := wso5 }
  let s5_o : FullState := { s with core := k_o, scratch := sc_o }
  have hk_eq : k_o = s5.core := by dsimp only [k_o]; rw [hs5_c, hs4_core]
  have hsc_eq : sc_o = s5.scratch := by dsimp only [sc_o]; rw [hs5_sc, hs4_sc]
  have hm_o' : (FullMem c s5_o ⋆ R) m_o := fullMem_of_eq hm_o hk_eq.symm hsc_eq.symm
  have hw_o : FullWitnessCutInv c F0 F_cur idx_u s5_o.core := by
    change FullWitnessCutInv c F0 F_cur idx_u k_o; rw [hk_eq]; exact hw5
  have hlen_o : s5_o.LengthsOk c := by
    change ({ s with core := k_o, scratch := sc_o } : FullState).LengthsOk c
    rw [hk_eq, hsc_eq]; exact hlen5'
  have hnd_o := otfs_large_nodup_same_arena (s4 := s4) (s5 := s5_o) (ar := ar4)
    rfl (by dsimp only [s5_o, k_o]; rw [hs4_core]) hs4_ar hnd4
  have hrefs_s4 : fullArenaClauseRefsCore s5_o.core = fullArenaClauseRefsCore s4.core := by
    change fullArenaClauseRefsCore k_o = _; rw [hk_eq, hs5_c]; rfl
  exact hQ false ar4 wv5 ws5 wl5 wu5 1#64 sc_o m_o hlen_o hw_o hnd_o rfl rfl rfl
    (hrefs_s4.trans hrefs4) (fun h => by cases h) hm_o'

private theorem otfs_large_swap1_nl1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u nsz : Nat} {s s4 : FullState} {ar4 : List (BitVec 32)} {cref : BitVec 32}
    (hw4 : FullWitnessCutInv c F0 F_cur idx_u s4.core) (hcv4 : s4.core.cur_vars = s.core.cur_vars)
    (hs4_ar : s4.core.arena = ar4) (h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1)
    (hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s4.core)
    (hng4 : fullArenaClauseGarbCore s4.core cref.toNat = false)
    (hsz4 : fullArenaClauseSizeCore s4.core cref.toNat = nsz) (hnsz3 : 3 ≤ nsz)
    (har4_l : ar4.length = c.arena_cap) (hcap : cref.toNat + 3 + nsz ≤ c.arena_cap)
    (h4bd : cref.toNat + 4 < ar4.length) :
    (ar4[cref.toNat + 4]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
    ((ar4[cref.toNat + 4]'h4bd &&& 0x7FFFFFFF#32) = ar4[cref.toNat + 4]'h4bd ∧
     ((ar4[cref.toNat + 4]'h4bd &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
     (ar4[cref.toNat + 4]'h4bd &&& 0x80000000#32) = 0#32) := by
  have hm_mem : (ar4[cref.toNat + 4]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s4.core cref.toNat := by
    simp only [fullArenaClauseLitsCore, List.mem_map]
    refine ⟨ar4[cref.toNat + 4]'h4bd, List.mem_iff_getElem.mpr ⟨1,
      by rw [List.length_take, List.length_drop, hs4_ar, hsz4, har4_l]; omega,
      by simp only [List.getElem_take, List.getElem_drop, Nat.add_assoc]
         exact getElem_eq_of_list_idx hs4_ar rfl⟩,
      by rw [List.getElem?_eq_getElem h4bd, Option.getD_some]⟩
  have hlt : (ar4[cref.toNat + 4]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
    hcv4 ▸ hw4.arena.lits_lt _ hcref4 hng4 _ hm_mem
  refine ⟨hlt, bv32_lit_lo31_props (l := ar4[cref.toNat + 4]'h4bd) ?_⟩
  rw [List.getElem?_eq_getElem h4bd, Option.getD_some] at hlt; omega

private theorem otfs_large_loop2_step_bds {c : FullCfg} {s s2 : FullState}
    {ar1 ar_cur : List (BitVec 32)} {cref l0 uip : BitVec 32}
    {old_sz i_nat nsz : Nat} {origMap : List Nat}
    (hcap : c.arena_cap < 2 ^ 31 - 1) (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (hs2_lvl_l : s2.core.lvl.length = c.max_vars) (har_len : s.core.arena.length = c.arena_cap)
    (hinv : OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap)
    (hilt : i_nat < old_sz)
    (har1_q : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32) :
    ∃ (hc_bd : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 <
        ar_cur.length)
      (hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat <
        ar_cur.length)
      (_hnsz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 nsz).setWidth 64).toNat <
        ar_cur.length)
      (har_bd : cref.toNat + 3 + i_nat < s.core.arena.length),
      nsz < i_nat ∧
      (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 =
        cref.toNat + 3 + i_nat ∧
      (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat =
        cref.toNat + 3 + i_nat ∧
      (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 nsz).setWidth 64).toNat =
        cref.toNat + 3 + nsz ∧
      ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
        i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd ∧
      ar_cur[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hz_bd =
        s.core.arena[cref.toNat + 3 + i_nat]'har_bd ∧
      (ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
        i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd).toNat / 2 < s2.core.lvl.length ∧
      (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 < s.core.lvl.length := by
  have har_c := hinv.1; have hi2 := hinv.2.2.1
  have hnsz_lt_i : nsz < i_nat := by
    have := otfsActCnt_le s.core cref.toNat i_nat; rw [hinv.2.2.2.2.2.1]; omega
  have hc_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 =
      cref.toNat + 3 + i_nat := by simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
  have hc_z := otfs_bv_idx3_64 cref i_nat (by omega) (by omega)
  have hnsz_z := otfs_bv_idx3_64 cref nsz (by omega) (by omega)
  have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by omega
  have hc_bd : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 <
      ar_cur.length := by rw [hc_idx, har_c]; omega
  have hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat <
      ar_cur.length := by rw [hc_z, har_c]; omega
  have hnsz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 nsz).setWidth 64).toNat <
      ar_cur.length := by rw [hnsz_z, har_c]; omega
  have hout := hinv.2.2.2.2.2.2.2.2.2.2.2.2
  have hot_c_eq : ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
      i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd := by
    have ho := hout (cref.toNat + 3 + i_nat) (Or.inr (by omega))
    rw [har1_q i_nat hi2, List.getElem?_eq_getElem har_bd,
      List.getElem?_eq_getElem (by rw [har_c]; omega)] at ho
    exact (getElem_eq_of_idx hc_idx).trans (Option.some.inj ho)
  have hot_z_eq : ar_cur[(cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hz_bd =
      s.core.arena[cref.toNat + 3 + i_nat]'har_bd :=
    (getElem_eq_of_idx (hc_z.trans hc_idx.symm)).trans hot_c_eq
  have hi_lit := (hlits_info i_nat hilt).1
  rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hi_lit
  exact ⟨hc_bd, hz_bd, hnsz_bd, har_bd, hnsz_lt_i, hc_idx, hc_z, hnsz_z, hot_c_eq, hot_z_eq,
    by rw [hot_c_eq, hs2_lvl_l]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hi_lit) hcv_le,
    by rw [hlvl_len, List.getElem?_eq_getElem har_bd, Option.getD_some]
       exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hi_lit) hcv_le⟩

private theorem otfs_large_loop1_step_bds {c : FullCfg} {s : FullState} {cref : BitVec 32}
    {old_sz i_nat : Nat} (hcap : c.arena_cap < 2 ^ 31 - 1)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (har_len : s.core.arena.length = c.arena_cap) (hold_bd : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hilt : i_nat < old_sz) (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32) :
    ∃ (har_bd : cref.toNat + 3 + i_nat < s.core.arena.length)
      (hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat <
        s.core.arena.length)
      (hc_bd : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 <
        s.core.arena.length),
      (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 =
        cref.toNat + 3 + i_nat ∧
      s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
        i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd ∧
      (s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
        i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd).toNat / 2 < s.core.cur_vars ∧
      ((s.core.arena[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hz_bd >>> 1).setWidth 64).toNat <
        s.core.lvl.length ∧
      (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 < s.core.lvl.length := by
  have hc_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 =
      cref.toNat + 3 + i_nat := by simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
  have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by rw [har_len]; omega
  have hz := otfs_bv_idx3_64 cref i_nat (by omega) (by omega)
  have hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat <
      s.core.arena.length := by rw [hz]; exact har_bd
  have hc_bd : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 <
      s.core.arena.length := by rw [hc_idx]; exact har_bd
  have hot_eq : s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
      i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd :=
    getElem_eq_of_idx hc_idx
  have hi_lit := (hlits_info i_nat hilt).1
  rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hi_lit
  exact ⟨har_bd, hz_bd, hc_bd, hc_idx, hot_eq,
    by rw [hot_eq]; exact Nat.div_lt_of_lt_mul hi_lit,
    by rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, getElem_eq_of_idx (hj := har_bd) hz]
       exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hi_lit) hcv_le,
    by rw [hlvl_len, List.getElem?_eq_getElem har_bd, Option.getD_some]
       exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hi_lit) hcv_le⟩

private theorem otfs_large_push_inv_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u : Nat} {s s1 s2 s3 s4 : FullState} {ar4 wv5 ws5 wso5 : List (BitVec 32)}
    {wu5 : BitVec 64} {wl5 : Nat} {cref l0 : BitVec 32}
    (ok5 : Bool) (hcr_lt : cref.toNat < 2 ^ 31 - 1)
    (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hs2_c : s2.core.arena = s1.core.arena ∧ s2.core.arena_len = s1.core.arena_len)
    (hs4_ar : s4.core.arena = ar4) (hdm4 : s4.core.dense_mode = 0#64)
    (hcv4 : s4.core.cur_vars = s.core.cur_vars) (hw4 : FullWitnessCutInv c F0 F_cur idx_u s4.core)
    (hrefs3 : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s2.core)
    (hrefs4 : fullArenaClauseRefsCore s4.core = fullArenaClauseRefsCore s3.core)
    (hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s4.core)
    (h4bd : cref.toNat + 4 < ar4.length) (h4_z_bd : (cref.setWidth 64 + 4#64).toNat < ar4.length)
    (h4_s4_eq :
      s4.core.arena[(BitVec.setWidth 64 cref + 4).toNat]'(by rw [hs4_ar]; exact h4_z_bd) =
        ar4[cref.toNat + 4]'h4bd)
    (hl0_and : ((l0 &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32)
    (hnl1_lt : (ar4[cref.toNat + 4]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hlen5 : ({ s4 with
      core := { s4.core with wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5 }
      scratch := { s4.scratch with wsort := wso5 } } : FullState).LengthsOk c)
    (hlay5 : WatchStackLayout
      { s4.core with wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5 })
    (hother5 : ∀ l < 2 * s4.core.cur_vars, l ≠ (ar4[cref.toNat + 4]?.getD 0#32).toNat →
      let k' : FullCoreState :=
        { s4.core with wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5 }
      fullWatchSizeCore k' l = fullWatchSizeCore s4.core l ∧
      ∀ k < fullWatchSizeCore s4.core l,
        ws5[fullWatchOffCore k' l + k]? = s4.core.wstk[fullWatchOffCore s4.core l + k]?)
    (hok5t : ok5 = true →
      let k' : FullCoreState :=
        { s4.core with wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5 }
      let nl1 := (ar4[cref.toNat + 4]?.getD 0#32).toNat
      nl1 < 2 * s4.core.cur_vars ∧ ((2 : BitVec 32).toNat = 1 ∨ (2 : BitVec 32).toNat = 2) ∧
      fullWatchSizeCore k' nl1 = fullWatchSizeCore s4.core nl1 + (2 : BitVec 32).toNat ∧
      (∀ k < fullWatchSizeCore s4.core nl1,
        ws5[fullWatchOffCore k' nl1 + k]? = s4.core.wstk[fullWatchOffCore s4.core nl1 + k]?) ∧
      ws5[fullWatchOffCore k' nl1 + fullWatchSizeCore s4.core nl1]? = some (l0 &&& 0x7FFFFFFF#32) ∧
      ((2 : BitVec 32).toNat = 2 →
        ws5[fullWatchOffCore k' nl1 + fullWatchSizeCore s4.core nl1 + 1]? = some cref))
    (hok5f : ok5 = false →
      let k' : FullCoreState :=
        { s4.core with wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5 }
      let nl1 := (ar4[cref.toNat + 4]?.getD 0#32).toNat
      (nl1 < 2 * s4.core.cur_vars →
        fullWatchSizeCore k' nl1 = fullWatchSizeCore s4.core nl1 ∧
        ∀ k < fullWatchSizeCore s4.core nl1,
          ws5[fullWatchOffCore k' nl1 + k]? = s4.core.wstk[fullWatchOffCore s4.core nl1 + k]?) ∧
      (s4.core.cur_vars * 2 ≤ nl1 ∨ ((2 : BitVec 32).toNat ≠ 1 ∧ (2 : BitVec 32).toNat ≠ 2) ∨
        k' = s4.core ∨ wu5 = 0#64)) :
    ∃ s5 : FullState,
      s5.core = { s4.core with wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5 } ∧
      s5.scratch = { s4.scratch with wsort := wso5 } ∧ s5.core.arena = s4.core.arena ∧
      s5.core.cur_vars = s.core.cur_vars ∧ s5.core.dense_mode = 0#64 ∧ s5.LengthsOk c ∧
      (ok5 = true → FullWitnessCutInv c F0 F_cur idx_u s5.core) ∧
      (ok5 = false → FullWitnessCutInv c F0 F_cur idx_u { s5.core with oom := 1#64 }) ∧
      fullArenaClauseRefs s4 = fullArenaClauseRefs s ∧
      (∀ h1 h2, s5.core.arena[(cref.setWidth 64 + 4#64).toNat]'h1 = ar4[cref.toNat + 4]'h2) ∧
      (cref.setWidth 64 + 4#64).toNat < s5.core.arena.length := by
  let s5 : FullState :=
    { s4 with
      core := { s4.core with wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5 }
      scratch := { s4.scratch with wsort := wso5 } }
  have hw5_t : ok5 = true → FullWitnessCutInv c F0 F_cur idx_u s5.core := fun hok5 => by
    obtain ⟨_, _, hsz5, hsame5, hw05, hw15⟩ := hok5t hok5
    have hm := fa_watchPush_large_preserves hdm4 hw4.watches (by rw [hcv4]; exact hnl1_lt)
      hlay5 hother5 hsz5 hsame5 hw05 (hw15 rfl) hl0_and (by omega) hcref4
    exact hw4.with_watches hm
  have hw5_f : ok5 = false → FullWitnessCutInv c F0 F_cur idx_u { s5.core with oom := 1#64 } :=
    fun hokf => by
      obtain ⟨hsame_f, _⟩ := hok5f hokf
      have hm := fa_watchPush_fail_preserves hdm4 hw4.watches hlay5 fun l hl =>
        if hle : l = (ar4[cref.toNat + 4]?.getD 0#32).toNat then
          hle ▸ hsame_f (by rw [hcv4]; exact hnl1_lt)
        else hother5 l hl hle
      exact (hw4.with_watches hm).with_oom 1#64
  have hr2 : fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s.core := by
    change fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core at hrefs1
    rw [show fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s1.core by
      simp [fullArenaClauseRefsCore, hs2_c.1, hs2_c.2]]; exact hrefs1
  have hlen5' : s5.LengthsOk c := ⟨{ hlen5.core_ok with }, hlen5.scratch_ok⟩
  have hs5_ar : s5.core.arena = s4.core.arena := rfl
  refine ⟨s5, rfl, rfl, hs5_ar, hcv4, hdm4, hlen5', hw5_t, hw5_f, hrefs4.trans (hrefs3.trans hr2),
    fun _ _ => h4_s4_eq, by rw [hs5_ar, hs4_ar]; exact h4_z_bd⟩

theorem full_otfs_large_wp_weak (Γ : Env)
    (hUnw : ∀ args m Q X, fullUnwatchLargeWeakSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullOtfsLargeSpec args m Q X →
      Func.wp Γ full_otfs_large_body args m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hdm, hw, hnd, hcref, hng, hu_lt,
      hiu_cut, hiu_te, ht_u, hr_u, hlev_u, hent_f, hm, hQ⟩
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len; have hwv_len := hlen.core_ok.wvec_len
  have hcv_le := hlen.core_ok.cur_vars_le; have hcap31_orig := c.harena; have hmaxv := c.hmaxv
  unfold dimacsBound at hcap31_orig hmaxv
  have hcap31 : c.arena_cap < 2 ^ 31 - 1 := by omega
  have h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by omega
  let old_sz := fullArenaClauseSizeCore s.core cref.toNat
  have hold_bd : cref.toNat + 3 + old_sz ≤ s.core.arena_len := by
    have := hwf.2.2.1; have := hwf.2.2.2.1; dsimp only [old_sz]; omega
  have hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hm_j : (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat ∈
        fullArenaClauseLits s cref.toNat := by
      simp only [fullArenaClauseLits, fullArenaClauseLitsCore, List.mem_map]
      refine ⟨s.core.arena[cref.toNat + 3 + j]'(by omega), List.mem_iff_getElem.mpr
        ⟨j, by simp; omega, by simp [List.getElem_take, List.getElem_drop]⟩,
        by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
    have hl_lt := hw.arena.lits_lt cref.toNat hcref hng _ hm_j
    exact ⟨hl_lt, bv32_lit_neq_ff (Nat.lt_trans hl_lt h2cv_lt)⟩
  have hcr0_z : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hcr_add {k : Nat} (hk : cref.toNat + k < 2 ^ 64) (hk' : k < 2 ^ 64) :
      (cref.setWidth 64 + BitVec.ofNat 64 k).toNat = cref.toNat + k := by
    rw [BitVec.toNat_add, hcr0_z, bv64_ofNat_toNat hk']; omega
  have hcr1_z := hcr_add (k := 1) (by omega) (by decide)
  have hcr2_z := hcr_add (k := 2) (by omega) (by decide)
  have hcr3_z := hcr_add (k := 3) (by omega) (by decide)
  have hcr4_z := hcr_add (k := 4) (by omega) (by decide)
  have hsz_eq : (s.core.arena[cref.toNat + 2]'(by omega)).toNat = old_sz := by
    unfold old_sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsz32 : s.core.arena[cref.toNat + 2]'(by omega) = BitVec.ofNat 32 old_sz :=
    BitVec.eq_of_toNat_eq (by rw [hsz_eq, bv32_ofNat_toNat (by omega)])
  have hcr3_bd : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by rw [hcr3_z]; omega
  have hcr4_bd : (cref.setWidth 64 + 4#64).toNat < s.core.arena.length := by rw [hcr4_z]; omega
  let orig0 := s.core.arena[cref.toNat + 3]?.getD 0#32
  let orig1 := s.core.arena[cref.toNat + 4]?.getD 0#32
  have hor0 : s.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_bd = orig0 := by
    rw [getElem_eq_of_idx (hj := by omega) hcr3_z]
    simp [orig0, List.getElem?_eq_getElem (by omega : cref.toNat + 3 < s.core.arena.length)]
  have hor1 : s.core.arena[(cref.setWidth 64 + 4#64).toNat]'hcr4_bd = orig1 := by
    rw [getElem_eq_of_idx (hj := by omega) hcr4_z]
    simp [orig1, List.getElem?_eq_getElem (by omega : cref.toNat + 4 < s.core.arena.length)]
  have hfail : Q (false, ()) m :=
    hQ false s.core.arena s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.oom
      s.scratch _ hlen (hw.shrink_cut (Nat.le_of_lt hiu_cut)) hnd rfl rfl rfl rfl
      (fun h => by cases h) hm
  fa_fast_steps_nogrp
  refine wp_join_group (ts := [i32]) (fun p ml0 => ml0 = m ∧
      ((p.1 = orig0 ∧ orig1 = uip) ∨ (p.1 = orig1 ∧ orig0 = uip))) ?_ ?_
  · rintro _ ⟨l0, ⟨⟩⟩ ml0 ⟨hml0, hs01⟩; subst ml0
    have hl0_lt : l0.toNat < 2 * s.core.cur_vars := by
      rcases hs01 with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact (hlits_info 0 (by omega)).1
      · exact (hlits_info 1 (by omega)).1
    have hcr2_bd : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by rw [hcr2_z]; omega
    fa_fast_steps_nogrp
    refine wp_loop_group (fun r (cnt, iv, ()) ml => ∃ i_nat : Nat,
      ml = m ∧ r = old_sz - i_nat ∧ 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧ iv = BitVec.ofNat 32 i_nat ∧
      cnt = BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat i_nat)) ?_ ?_
    · rintro L r ⟨cnt, iv, ⟨⟩⟩ ml ih ⟨i_nat, hml, rfl, hi2, hile, rfl, rfl⟩
      subst ml; fa_fast_steps_nogrp
      · have hilt : i_nat < old_sz := by
          have hb : (BitVec.ofNat 32 i_nat).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
          rw [bv32_ofNat_toNat (by omega), getElem_eq_of_idx (hj := by omega) hcr2_z, hsz_eq] at hb
          exact hb
        obtain ⟨har_bd, hz_bd, hc_bd, hc_idx, hot_eq, _, hlvl1_bd_len, hv_bd⟩ :=
          otfs_large_loop1_step_bds hcap31 hcv_le hlvl_len har_len (by omega) hilt hlits_info
        fa_fast_steps_nogrp
        refine wp_join_group (ts := [i32]) (fun (cnt', ()) ml' => ml' = m ∧
            cnt' = BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat (i_nat + 1))) ?_ ?_
        · rintro _ ⟨cnt', ⟨⟩⟩ ml' ⟨hml', rfl⟩; subst ml'; fa_fast_steps
          rw [show BitVec.ofNat 32 i_nat + 1 = BitVec.ofNat 32 (i_nat + 1) from
            BitVec.eq_of_toNat_eq (by bv_omega)]
          exact ih (old_sz - (i_nat + 1)) _ m (by omega)
            ⟨i_nat + 1, rfl, rfl, by omega, by omega, rfl, rfl⟩
        · intro J1 hJ1; fa_fast_steps
          · have hlv_pos : 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD
                0#32).toNat / 2]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
                List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd,
                  Option.getD_some] at hv_bd; exact hv_bd), Option.getD_some]
              exact Nat.lt_of_lt_of_eq ‹BitVec.toNat 0 < _› (congrArg BitVec.toNat
                (getElem_eq_of_idx (congrArg (·.toNat / 2) hot_eq)))
            rw [show BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat i_nat) + 1 =
                BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat (i_nat + 1)) from
                BitVec.eq_of_toNat_eq (by
                  simp only [bv_c0, show (1 : BitVec 32).toNat = 1 from rfl]
                  rw [otfsActCnt_succ hi2, ite_eq_left hlv_pos]; omega)]
            exact hJ1 _ _ ⟨rfl, rfl⟩
          · have hlv_0 : ¬ 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD
                0#32).toNat / 2]?.getD 0#32).toNat := fun hpos => by
              rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
                List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd,
                  Option.getD_some] at hv_bd; exact hv_bd), Option.getD_some] at hpos
              exact ‹¬ BitVec.toNat 0 < _› (Nat.lt_of_lt_of_eq hpos (congrArg BitVec.toNat
                (getElem_eq_of_idx (congrArg (·.toNat / 2) hot_eq.symm))))
            have hcnt_eq : otfsActCnt s.core cref.toNat (i_nat + 1) =
                otfsActCnt s.core cref.toNat i_nat := by
              rw [otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero]
            exact hJ1 _ _ ⟨rfl, congrArg (fun x => BitVec.ofNat 32 (1 + x)) hcnt_eq.symm⟩
      · exact hfail
      · have hilt : i_nat = old_sz := by
          have hba : ¬ (BitVec.ofNat 32 i_nat).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
          rw [bv32_ofNat_toNat (by omega), getElem_eq_of_idx (hj := by omega) hcr2_z, hsz_eq] at hba
          omega
        subst i_nat
        have hact_lt : 1 + otfsActCnt s.core cref.toNat old_sz < old_sz := by
          have := otfsActCnt_le s.core cref.toNat old_sz; omega
        have hcnt3 : 3 ≤ 1 + otfsActCnt s.core cref.toNat old_sz := by
          have hb : ¬ (1 + otfsActCnt s.core cref.toNat old_sz) % 2 ^ 32 <
              BitVec.toNat (3 : BitVec 32) := ‹_›
          rw [Nat.mod_eq_of_lt (by omega), show BitVec.toNat (3 : BitVec 32) = 3 from rfl] at hb
          omega
        have h4_old : 4 ≤ old_sz := by omega
        obtain ⟨hw1, hnd1, hrefs1, hsz1, hng1, har1_q, har1_0, har1_1⟩ :=
          otfs_large_swap01 hlen hw hnd hcref hng hs01
        let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
        have har1_eq : (s.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).set
            (cref.setWidth 64 + 4#64).toNat uip = ar1 := by dsimp only [ar1]; rw [hcr3_z, hcr4_z]
        obtain ⟨s1, hs1_eq, hm1⟩ : ∃ s1 : FullState,
            s1 = { s with core := { s.core with arena := ar1 } } ∧ (FullMem c s1 ⋆ R) m :=
          ⟨_, rfl, fullMem_of_eq hm (congrArg (fun a => { s.core with arena := a }) har1_eq) rfl⟩
        have hs1_c : s1.core = { s.core with arena := ar1 } := congrArg FullState.core hs1_eq
        have hlen1 : s1.LengthsOk c := by
          rw [hs1_eq]; exact ⟨{ hlen.core_ok with arena_len_arr := by simp [ar1, har_len] },
            hlen.scratch_ok⟩
        rw [← hs1_eq] at hnd1 hrefs1 hsz1 hng1; rw [← hs1_c] at hw1
        clear hm; c0_call hUnw
        · refine ⟨c, s1, R, rfl, hlen1, by
            have h := hw1.watches; unfold ModeWatchesInv at h
            rw [show s1.core.dense_mode = 0#64 by rw [hs1_c]; exact hdm] at h
            simp only [↓reduceIte] at h; exact h.layout,
            hm1, fun wv2 ws2 wu2 m2 hlen2 _ hmw2 hm2 => ?_⟩
          obtain ⟨s2, hs2_eq, hm2'⟩ : ∃ s2 : FullState,
              s2 = { s1 with core := { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 } } ∧
              (FullMem c s2 ⋆ R) m2 := ⟨_, rfl, hm2⟩
          clear hm1 hm2
          have hs2_base : s2.core =
              { s.core with arena := ar1, wvec := wv2, wstk := ws2, wusable := wu2 } := by
            rw [hs2_eq]; dsimp only; rw [hs1_c]
          have hlen2' : s2.LengthsOk c := by
            rw [hs2_eq]; exact ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩
          have hw2 : FullWitnessCutInv c F0 F_cur cut s2.core := by
            rw [hs2_eq]; exact hw1.with_watches (hmw2 F_cur hw1.watches)
          have hnd2 : FullArenaVarsNodup s2 := by rw [hs2_eq]; exact hnd1
          have hcref2 : cref.toNat ∈ fullArenaClauseRefs s2 := by
            rw [hs2_eq]; change cref.toNat ∈ fullArenaClauseRefs s1; rw [hrefs1]; exact hcref
          have hng2 : fullArenaClauseGarb s2 cref.toNat = false := by rw [hs2_eq]; exact hng1
          have hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz := by rw [hs2_eq]; exact hsz1
          have har2_len : s2.core.arena.length = c.arena_cap := hlen2'.core_ok.arena_len_arr
          have har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i →
              ar1[i]? = s2.core.arena[i]? := by rw [hs2_base]; exact fun _ _ => rfl
          have hs2_lvl : s2.core.lvl = s.core.lvl := by rw [hs2_base]
          have hs2_sc : s2.scratch = s.scratch := by rw [hs2_eq, hs1_eq]
          clear hlen2; fa_fast_steps_nogrp
          refine wp_loop_group (fun r (iv, nszv, ()) ml => ∃ (i_n nsz : Nat)
              (ar_cur : List (BitVec 32)) (origMap : List Nat),
            (FullMem c { s2 with core := { s2.core with arena := ar_cur } } ⋆ R) ml ∧
            iv = BitVec.ofNat 32 i_n ∧ nszv = BitVec.ofNat 32 nsz ∧
            OtfsShrinkInv c s ar1 cref l0 uip old_sz r i_n nsz ar_cur origMap) ?_ ?_
          · rintro L2 r2 ⟨iv, nszv, ⟨⟩⟩ ml ih2
              ⟨i_nat, nsz, ar_cur, origMap, hm_c, rfl, rfl, hinv_l⟩
            clear hm2'; have hr2_eq : r2 = old_sz - i_nat := hinv_l.2.1; subst r2
            have ⟨har_c, _, hi2, hile, hns1, hact, hlm, hpw, hlt_m, h01, hcov, hmapeq, hout_m⟩ :=
              hinv_l
            let sc : FullState := { s2 with core := { s2.core with arena := ar_cur } }
            have hlen_c : sc.LengthsOk c :=
              ⟨{ hlen2'.core_ok with arena_len_arr := har_c }, hlen2'.scratch_ok⟩
            have har_c_bd : (cref.setWidth 64 + 2#64).toNat < ar_cur.length := by
              rw [har_c, hcr2_z]; omega
            have hsz_c : ar_cur[cref.toNat + 2]'(by rw [har_c]; omega) =
                BitVec.ofNat 32 old_sz := by
              have hopt := hout_m (cref.toNat + 2) (Or.inl (by omega))
              rw [List.getElem?_eq_getElem (by rw [har_c]; omega)] at hopt
              have ho1 : ar1[cref.toNat + 2]? = s.core.arena[cref.toNat + 2]? := by
                dsimp only [ar1]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              rw [← hopt, List.getElem?_eq_getElem (by omega)] at ho1
              exact (Option.some.inj ho1).trans hsz32
            fa_steps_n 3
            · have hilt : i_nat < old_sz := by
                have hb : i_nat % 2 ^ 32 < (s.core.arena[(cref.toNat + BitVec.toNat
                    (2 : BitVec 64)) % 2 ^ 64]'(by simp only [BitVec.reduceToNat]; omega)).toNat
                    := ‹_›
                rw [Nat.mod_eq_of_lt (by omega), getElem_eq_of_idx (j := cref.toNat + 2)
                  (hj := by omega) (by simp only [BitVec.reduceToNat]; omega), hsz_eq] at hb
                exact hb
              obtain ⟨hc_idx_bd, hc_z_bd, har_nsz_bd2, har_bd, hnsz_lt_i, hc_idx, hc_z, hnsz_z,
                hot_c_eq, hot_z_eq, h2_lvl_bd, hv_bd⟩ :=
                otfs_large_loop2_step_bds hcap31 (by omega) hcv_le hlvl_len hlen2'.core_ok.lvl_len
                  har_len hinv_l hilt har1_q hlits_info
              fa_fast_steps_nogrp
              refine wp_join_group (ts := [i32]) (fun (nszv', ()) ml' =>
                ∃ (nsz' : Nat) (ar' : List (BitVec 32)) (omap' : List Nat),
                  (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆ R) ml' ∧
                  nszv' = BitVec.ofNat 32 nsz' ∧ OtfsShrinkInv c s ar1 cref l0 uip old_sz
                    (old_sz - (i_nat + 1)) (i_nat + 1) nsz' ar' omap') ?_ ?_
              · rintro _ ⟨nszv', ⟨⟩⟩ ml' ⟨nsz', ar', omap', hm', rfl, hinv'⟩; fa_fast_steps
                rw [show BitVec.ofNat 32 i_nat + 1 = BitVec.ofNat 32 (i_nat + 1) from
                  BitVec.eq_of_toNat_eq (by bv_omega)]
                exact ih2 (old_sz - (i_nat + 1)) _ ml' (by omega)
                  ⟨i_nat + 1, nsz', ar', omap', hm', rfl, rfl, hinv'⟩
              · intro J2 hJ2; fa_fast_steps
                · have hlv_lt_hc : (0#32 : BitVec 32).toNat <
                      (s2.core.lvl[(ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                        i_nat % 2 ^ 32) % 2 ^ 64]'hc_idx_bd).toNat / 2]'h2_lvl_bd).toNat := ‹_›
                  have hlv_pos : 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD
                      0#32).toNat / 2]?.getD 0#32).toNat := by
                    rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
                      List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd,
                        Option.getD_some] at hv_bd; exact hv_bd), Option.getD_some]
                    exact Nat.lt_of_lt_of_eq hlv_lt_hc (congrArg BitVec.toNat
                      (getElem_eq_of_list_idx hs2_lvl (congrArg (·.toNat / 2) hot_c_eq)))
                  let ar' := ar_cur.set (cref.toNat + 3 + nsz) (s.core.arena[cref.toNat + 3 +
                    i_nat]'har_bd)
                  have har_st_eq : ar_cur.set (cref.setWidth 64 + 3#64 +
                      (BitVec.ofNat 32 nsz).setWidth 64).toNat
                      (ar_cur[(cref.setWidth 64 + 3#64 +
                        (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hc_z_bd) = ar' := by
                    dsimp only [ar']; rw [hnsz_z, hot_z_eq]
                  have hm_st : (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆ R) m
                      := fullMem_of_eq hm (congrArg (fun a => { s2.core with arena := a })
                        har_st_eq) rfl
                  rw [show BitVec.ofNat 32 nsz + 1 = BitVec.ofNat 32 (nsz + 1) from
                    BitVec.eq_of_toNat_eq (by bv_omega)]
                  exact hJ2 _ _ ⟨nsz + 1, ar', origMap ++ [i_nat], hm_st, rfl,
                    otfs_shrink_loop_step har_len hinv_l hilt (by omega) hlv_pos⟩
                · have hlv_nlt_hc : ¬ (0#32 : BitVec 32).toNat <
                      (s2.core.lvl[(ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                        i_nat % 2 ^ 32) % 2 ^ 64]'hc_idx_bd).toNat / 2]'h2_lvl_bd).toNat := ‹_›
                  have hlv_0 : ¬ 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD
                      0#32).toNat / 2]?.getD 0#32).toNat := fun hpos => by
                    rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
                      List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd,
                        Option.getD_some] at hv_bd; exact hv_bd), Option.getD_some] at hpos
                    exact hlv_nlt_hc (Nat.lt_of_lt_of_eq hpos (congrArg BitVec.toNat
                      (getElem_eq_of_list_idx hs2_lvl.symm (congrArg (·.toNat / 2)
                        hot_c_eq.symm))))
                  refine hJ2 _ _ ⟨nsz, ar_cur, origMap, hm_c, rfl, har_c, rfl, by omega, by omega,
                    hns1, by rw [hact, otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero], hlm,
                    hpw, fun p hp => Nat.lt_succ_of_lt (hlt_m p hp), h01, fun p hp2 hplt hpos => by
                      by_cases hpi : p = i_nat
                      · subst p; exact absurd hpos hlv_0
                      · exact hcov p hp2 (by omega) hpos, hmapeq, hout_m⟩
            · have hilt : i_nat = old_sz := by
                have hba : ¬ i_nat % 2 ^ 32 < (s.core.arena[(cref.toNat + BitVec.toNat
                    (2 : BitVec 64)) % 2 ^ 64]'(by simp only [BitVec.reduceToNat]; omega)).toNat
                    := ‹_›
                rw [Nat.mod_eq_of_lt (by omega), getElem_eq_of_idx (j := cref.toNat + 2)
                  (hj := by omega) (by simp only [BitVec.reduceToNat]; omega), hsz_eq] at hba
                omega
              subst i_nat
              have hnsz3 : 3 ≤ nsz := by rw [hact]; exact hcnt3
              have hnsz_lt : nsz < old_sz := by rw [hact]; exact hact_lt
              have har1_len : ar1.length = c.arena_cap := by simp [ar1, har_len]
              have har_c_0 : (cref.setWidth 64).toNat < ar_cur.length := by
                rw [har_c, hcr0_z]; omega
              have har_c_1 : (cref.setWidth 64 + 1#64).toNat < ar_cur.length := by
                rw [har_c, hcr1_z]; omega
              have har_c_2 : (cref.setWidth 64 + 2#64).toNat < ar_cur.length := by
                rw [har_c, hcr2_z]; omega
              have hhdr_eq : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat) := by
                rw [hout_m cref.toNat (Or.inl (by omega))]
                unfold fullArenaHdrCore
                rw [hs2_base, List.getElem?_eq_getElem (by rw [har1_len]; omega), Option.getD_some]
              have hhdr_s2 : ar_cur[(cref.setWidth 64).toNat]'har_c_0 =
                  fullArenaHdrCore s2.core cref.toNat := by
                have hg := hhdr_eq; rw [List.getElem?_eq_getElem (by rw [har_c]; omega)] at hg
                exact (getElem_eq_of_idx hcr0_z).trans (Option.some.inj hg)
              have hlen_ca : sc.LengthsOk c := hlen_c
              fa_fast_steps_nogrp
              refine wp_join_group (ts := []) (fun () ml3 =>
                  OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3) ?_ ?_
              · rintro _ ⟨⟩ ml3 ⟨ar3, hm3, har3_l, hhdr3, hsz3, hmap3, hpad3, hsent3, hkeep3, hout3⟩
                obtain ⟨s3, hs3_eq, hm3'⟩ : ∃ s3 : FullState,
                    s3 = { s2 with core := { s2.core with arena := ar3 } } ∧
                    (FullMem c s3 ⋆ R) ml3 := ⟨_, rfl, hm3⟩
                clear hm3
                obtain ⟨hlen3, hw3, hnd3, hrefs3, hcref3, hsz_3, hng_3, har3_l0, hlits_3, har3_4⟩ :=
                  otfs_large_shrink_ok hlen hw hnd hlen2' hw2 hnd2 (by rw [hs2_base])
                    (by rw [hs2_base]) (by rw [hs2_base]) (by rw [hs2_base]) (by rw [hs2_base])
                    (by rw [hs2_base]) hcref hng hcref2 hng2 hsz2 hiu_cut hiu_te ht_u hr_u hlev_u
                    hent_f hnsz3 hnsz_lt hlm hpw hlt_m h01 hcov hmap3 har3_l hhdr3 hsz3 hpad3 hsent3
                    hkeep3 hout3
                rw [← hs3_eq] at hlen3 hw3 hnd3 hrefs3 hcref3 hsz_3 hng_3 hlits_3
                clear hw2 hnd2 hlen2' hw1 hnd1 hlen1 hinv_l hlen_c hlen_ca
                have hs3_ar : s3.core.arena = ar3 := by rw [hs3_eq]
                have hs3_c : s3.core = { s2.core with arena := ar3 } :=
                  congrArg FullState.core hs3_eq
                rw [← hs3_ar] at har3_l0
                have har3_s3_l : s3.core.arena.length = c.arena_cap := hlen3.core_ok.arena_len_arr
                have hs3_lvl : s3.core.lvl.length = c.max_vars := hlen3.core_ok.lvl_len
                have hcr2_bd3 : (cref.setWidth 64 + 2#64).toNat < s3.core.arena.length := by
                  rw [hcr2_z, har3_s3_l]; omega
                have har3_4_bd : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length := by
                  rw [hcr4_z, har3_s3_l]; omega
                have hlvl_s3_4_max : (s3.core.arena[(cref.setWidth 64 +
                    4#64).toNat]'har3_4_bd).toNat / 2 < c.max_vars := by
                  have h4_eq : s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'har3_4_bd =
                      ar3[cref.toNat + 4]'(by rw [har3_l]; omega) := by
                    simp only [hs3_ar]; exact getElem_eq_of_idx hcr4_z
                  rw [List.getElem?_eq_getElem (by rw [har3_l]; omega), Option.getD_some] at har3_4
                  rw [h4_eq]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul har3_4) hcv_le
                have hlvl_s3_4_len : ((s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'har3_4_bd >>>
                    1).setWidth 64).toNat < s3.core.lvl.length := by
                  rw [hs3_lvl, bv_c0_zext32_64, bv32_lshr_1]; exact hlvl_s3_4_max
                have hmap3_s3 : ∀ k, k < nsz → s3.core.arena[cref.toNat + 3 + k]? =
                    s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]? := by
                  rw [hs3_ar]; exact hmap3
                fa_fast_steps_nogrp
                refine wp_loop_group (fun r (iv3, hpv, hlv, ()) ml => ∃ i_n hp_n : Nat,
                  ml = ml3 ∧ r = nsz - i_n ∧ 2 ≤ i_n ∧ i_n ≤ nsz ∧ iv3 = BitVec.ofNat 32 i_n ∧
                  hpv = BitVec.ofNat 32 hp_n ∧ 1 ≤ hp_n ∧ hp_n < nsz) ?_ ?_
                · rintro L3 r3 ⟨iv3, hpv, hlv, ⟨⟩⟩ ml ih3
                    ⟨i_n, hp_n, hm_ml, rfl, hi3, hile3, rfl, rfl, hhp1, hhp_lt⟩
                  subst ml; fa_steps_n 3
                  · have hilt3 : i_n < nsz := by
                      have hc_lt : i_n % 2 ^ 32 < nsz % 2 ^ 32 := ‹_›
                      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc_lt
                    obtain ⟨hc_i3, har_i3_bd, hc_i3_z, har_i3_z_bd, hlvl3_bd_max, hlvl3_z_bd⟩ :=
                      otfs_large_loop3_bds hcap31 hcv_le har3_s3_l (by omega) hnsz_lt hilt3 hlm
                        hlt_m hlits_info hmap3_s3
                    have hlvl3_s3_len : ((s3.core.arena[(cref.setWidth 64 + 3#64 +
                        (BitVec.ofNat 32 i_n).setWidth 64).toNat]'har_i3_z_bd >>>
                        1).setWidth 64).toNat < s3.core.lvl.length := by
                      rw [hs3_lvl, bv_c0_zext32_64, bv32_lshr_1]; exact hlvl3_z_bd
                    fa_fast_steps_nogrp
                    refine wp_join_group (ts := [i32, i32]) (fun p ml' => ∃ hp' : Nat,
                      ml' = ml3 ∧ p.1 = BitVec.ofNat 32 hp' ∧ 1 ≤ hp' ∧ hp' < nsz) ?_ ?_
                    · rintro _ ⟨hpv', hlv', ⟨⟩⟩ ml' ⟨hp', hm_ml', rfl, h1', hlt'⟩; fa_fast_steps
                      rw [show BitVec.ofNat 32 i_n + 1 = BitVec.ofNat 32 (i_n + 1) from
                        BitVec.eq_of_toNat_eq (by bv_omega)]
                      exact ih3 (nsz - (i_n + 1)) _ ml' (Nat.sub_lt (Nat.sub_pos_of_lt hilt3)
                        Nat.zero_lt_one)
                        ⟨i_n + 1, hp', hm_ml', rfl, by omega, hilt3, rfl, rfl, h1', hlt'⟩
                    · intro J3 hJ3; fa_fast_steps
                      · exact hJ3 _ _ ⟨i_n, rfl, rfl, by omega, hilt3⟩
                      · exact hJ3 _ _ ⟨hp_n, rfl, rfl, hhp1, hhp_lt⟩
                  · have hilt3 : i_n = nsz := by
                      have hba : ¬ i_n % 2 ^ 32 < nsz % 2 ^ 32 := ‹_›
                      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hba
                      exact Nat.le_antisymm hile3 (Nat.not_lt.mp hba)
                    subst i_n
                    have h_hp_bd_pre : (cref.setWidth 64 + 3#64 +
                        (BitVec.ofNat 32 hp_n).setWidth 64).toNat < s3.core.arena.length :=
                      (otfs_ar_idx3_lt_len (cref := cref) (old_sz := old_sz) (j := hp_n)
                        hcap31 har3_s3_l (by omega) (Nat.lt_trans hhp_lt hnsz_lt)).2
                    fa_fast_steps_nogrp
                    refine wp_join_group (ts := []) (fun () ml4 => ∃ ar4 : List (BitVec 32),
                      (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) ml4 ∧
                      ar4.length = c.arena_cap ∧
                      FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 } ∧
                      FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } } ∧
                      fullArenaClauseRefsCore { s3.core with arena := ar4 } =
                        fullArenaClauseRefsCore s3.core ∧
                      fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz ∧
                      fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false ∧
                      ar4[cref.toNat + 3]? = some l0 ∧
                      (∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
                        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)) ?_ ?_
                    · rintro _ ⟨⟩ ml4 ⟨ar4, hm4, har4_l, hw4, hnd4, hrefs4, hsz4, hng4,
                        har4_l0, hlits4⟩
                      obtain ⟨s4, hs4_eq, hm4'⟩ : ∃ s4 : FullState,
                          s4 = { s3 with core := { s3.core with arena := ar4 } } ∧
                          (FullMem c s4 ⋆ R) ml4 := ⟨_, rfl, hm4⟩
                      clear hm4
                      have hs4_c : s4.core = { s3.core with arena := ar4 } :=
                        congrArg FullState.core hs4_eq
                      have hs4_ar : s4.core.arena = ar4 := by rw [hs4_c]
                      have hs4_sc : s4.scratch = s.scratch := by rw [hs4_eq, hs3_eq, hs2_sc]
                      have hs4_base : ∃ wv2 ws2 wu2, s4.core =
                          { s.core with arena := ar4, wvec := wv2, wstk := ws2, wusable := wu2 } :=
                        ⟨wv2, ws2, wu2, by rw [hs4_c, hs3_c, hs2_base]⟩
                      rw [← hs4_eq] at hnd4; rw [← hs4_c] at hw4 hrefs4 hsz4 hng4 hlits4
                      have hlen4 : s4.LengthsOk c := by
                        rw [hs4_eq]; exact ⟨{ hlen3.core_ok with arena_len_arr := har4_l },
                          hlen3.scratch_ok⟩
                      have h4_z_bd : (cref.setWidth 64 + 4#64).toNat < s4.core.arena.length := by
                        rw [hcr4_z, hlen4.core_ok.arena_len_arr]; omega
                      have hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s4.core := by
                        rw [hrefs4]; exact hcref3
                      have h4bd : cref.toNat + 4 < ar4.length := by rw [har4_l]; omega
                      have hcv4 : s4.core.cur_vars = s.core.cur_vars := by
                        rw [hs4_c, hs3_c, hs2_base]
                      have hdm4 : s4.core.dense_mode = 0#64 := by
                        rw [hs4_c, hs3_c, hs2_base]; exact hdm
                      have hl0_lt4 : l0.toNat < 2 * s4.core.cur_vars := by rwa [hcv4]
                      obtain ⟨hnl1_lt, _⟩ := otfs_large_swap1_nl1 hw4 hcv4 hs4_ar h2cv_lt
                        hcref4 hng4 hsz4 hnsz3 har4_l (by omega) h4bd
                      have hl0_p := bv32_lit_lo31_props (l := l0) (by omega)
                      have hcr_ne4 : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff (by omega)
                      have hl0_m_ne : l0 &&& 0x7FFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                        rw [hl0_p.1]; exact bv32_lit_neq_ff (by omega)
                      have h4_z_bd' : (BitVec.setWidth 64 cref + 4).toNat < ar4.length := by
                        rw [show (4 : BitVec 64) = 4#64 from rfl, ← hs4_ar]; exact h4_z_bd
                      have h4_s4_eq : s4.core.arena[(BitVec.setWidth 64 cref + 4).toNat]'h4_z_bd =
                          ar4[cref.toNat + 4]'h4bd :=
                        (getElem_eq_of_list_idx (hj := h4_z_bd') hs4_ar rfl).trans
                          (getElem_eq_of_idx
                            (by rw [show (4 : BitVec 64) = 4#64 from rfl]; exact hcr4_z))
                      have h4_get : s4.core.arena[(BitVec.setWidth 64 cref + 4).toNat]'h4_z_bd =
                          ar4[cref.toNat + 4]?.getD 0#32 :=
                        h4_s4_eq.trans (by rw [List.getElem?_eq_getElem h4bd, Option.getD_some])
                      fa_fast_steps_nogrp; rw [h4_get]; c0_call hPush
                      · refine ⟨c, s4, R, rfl, hlen4, by
                          have h := hw4.watches; unfold ModeWatchesInv at h
                          simp only [hdm4, ↓reduceIte] at h; exact h.layout,
                          fun h => absurd h (by decide), fun _ => ⟨hl0_m_ne, hcr_ne4⟩, hm4',
                          fun ok5 wv5 ws5 wl5 wu5 wso5 m5 hlen5 hlay5 hother5 hok5t hok5f hm5 => ?_⟩
                        clear hm4' hlen4
                        obtain ⟨s5, hs5_c, hs5_sc, hs5_ar, hcv5, hdm5, hlen5', hw5_t, hw5_f,
                            hrefs4_s, _, _⟩ :=
                          otfs_large_push_inv_ok ok5 (by omega) hrefs1
                            ⟨by rw [hs2_eq], by rw [hs2_eq]⟩ hs4_ar hdm4 hcv4 hw4 hrefs3 hrefs4
                            hcref4 h4bd (by rw [← hs4_ar]; exact h4_z_bd) h4_s4_eq hl0_p.2.1
                            hnl1_lt hlen5 hlay5 hother5 hok5t hok5f
                        have hm5' : (FullMem c s5 ⋆ R) m5 :=
                          fullMem_of_eq hm5 hs5_c.symm hs5_sc.symm
                        by_cases hok5 : ok5 = true
                        · subst hok5; have hw5 := hw5_t rfl
                          have hshl0 : (BitVec.setWidth 64 l0 <<< 1).toNat = 2 * l0.toNat := by
                            rw [BitVec.toNat_shiftLeft, zext_toNat l0 (by decide), Nat.shiftLeft_eq]
                            simp; omega
                          have hw0_p : (BitVec.setWidth 64 l0 <<< 1).toNat < s5.core.wvec.length
                              := by rw [hshl0, hlen5'.core_ok.wvec_len]; omega
                          have hw1_p : (BitVec.setWidth 64 l0 <<< 1 + 1).toNat <
                              s5.core.wvec.length := by
                            rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
                              hshl0, hlen5'.core_ok.wvec_len]; omega
                          fa_fast_steps_nogrp
                          refine wp_join_group (ts := [i64]) (fun _ ml_f =>
                            ∃ ws_f : List (BitVec 32),
                              (FullMem c { s5 with core := { s5.core with wstk := ws_f } } ⋆ R)
                                ml_f ∧ ws_f.length = c.wcap ∧
                              ModeWatchesInv F_cur { s5.core with wstk := ws_f }) ?_ ?_
                          · rintro _ ⟨_pf, ⟨⟩⟩ ml_f ⟨ws_f, hm_f, hws_fl, hmw_f⟩; clear hm5'
                            fa_fast_steps
                            exact otfs_large_fin_wp hlen hw hcref hng hiu_cut hiu_te ht_u hr_u
                              hs4_ar hs4_sc hs4_base hrefs4_s hnd4 hcref4 hng4 hlits4
                              (by rw [hs5_c]) hs5_sc hw5 hlen5' hws_fl hmw_f
                              (by assumption) hQ
                          · intro J_out hJ_out
                            have hws5_c : s5.core.wstk = ws5 := by rw [hs5_c]
                            fa_fast_steps_nogrp
                            exact otfs_large_loop4_wp hmaxv hdm5 hw5 hlen5' (by rwa [hcv5])
                              (by rwa [hcv5]) hws5_c (by omega) (by rw [hs5_c]; exact hcref4)
                              hm5' hJ_out
                        · have hok5f : ok5 = false := Bool.eq_false_iff.mpr hok5; subst hok5f
                          let s5_o : FullState := { s5 with core := { s5.core with oom := 1#64 } }
                          have hs5_oc : s5_o.core =
                              { s4.core with
                                wvec := wv5, wstk := ws5, wlen := wl5, wusable := wu5,
                                oom := 1#64 } := by
                            dsimp only [s5_o]; rw [hs5_c]
                          have hs5_osc : s5_o.scratch = { s4.scratch with wsort := wso5 } := hs5_sc
                          have hw5_o : FullWitnessCutInv c F0 F_cur idx_u s5_o.core := hw5_f rfl
                          have hlen5_o : s5_o.LengthsOk c :=
                            ⟨{ hlen5'.core_ok with }, hlen5'.scratch_ok⟩
                          fa_fast_steps
                          exact otfs_large_oom_wp hs4_ar hs4_sc hs4_base hrefs4_s hnd4 hs5_oc
                            hs5_osc hw5_o hlen5_o (by assumption) hQ
                    · intro J4 hJ4
                      have h_hp_z := otfs_bv_idx3_64 cref hp_n (by omega) (by omega)
                      have hbd_hp : (cref.setWidth 64 + 3#64 +
                          (BitVec.ofNat 32 hp_n).setWidth 64).toNat < s3.core.arena.length := by
                        rw [h_hp_z, har3_s3_l]; omega
                      have hbd_4 : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length := by
                        rw [hcr4_z, har3_s3_l]; omega
                      clear hfail hUnw hPush hQ hw hnd hlen hent_f hlits_info hmapeq hout_m har1_q
                        har1_s2 hmap3 hhdr3 hsz3 hpad3 hsent3 hkeep3 hout3 hmap3_s3 har3_4 hhdr_eq
                        hhdr_s2 har1_len hsz_c har_c har_c_0 har_c_1 har_c_2 har2_len hs2_lvl
                        hs3_lvl hlvl_s3_4_max hlvl_s3_4_len hcr2_bd3 har3_l hs3_eq hs2_eq hs1_eq
                        hs1_c
                      fa_fast_steps
                      · exact hJ4 () _ (otfs_large_j4_swap_wp hlen3 hw3 hnd3 hcref3 hsz_3 hng_3
                          har3_l0 hlits_3 har3_s3_l hnsz_lt hcr4_z hhp1 hhp_lt h_hp_z hbd_hp hbd_4
                          rfl (by assumption))
                      · exact hJ4 () _ ⟨s3.core.arena,
                          fullMem_of_eq hm3' (by rcases s3 with ⟨⟨⟩, _⟩; rfl) rfl,
                          har3_s3_l, hw3, hnd3, rfl, hsz_3, hng_3, har3_l0, hlits_3⟩
                · intro L3 hL3; fa_fast_steps
                  exact hL3 (nsz - 2) _ ml3 ⟨2, 1, rfl, rfl, Nat.le_refl _, by omega, rfl, rfl,
                    Nat.le_refl _, by omega⟩
              · intro J3 hJ3; have h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap := by omega
                clear hw2 hnd2 hlen2' hw1 hnd1 hlen1 hcref2 hng2 hsz2 hinv_l hlen_c hlen_ca hfail
                  hUnw hPush hQ hw hnd hlen hent_f hlm hpw hlt_m h01 hcov hrefs1 hsz_c har2_len
                  hs2_lvl orig0 orig1 hor0 hor1 hs01 hiu_cut hiu_te ht_u hr_u hlev_u hcnt3 hact_lt
                  hact
                have hcr_end_z := otfs_cr_end_z (by omega) h4_old hcap31 hcr2_z hcr3_z hcr2_bd hsz32
                have hcr_end_bd : (cref.setWidth 64 + 3#64 +
                    (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).setWidth 64 -
                      1#64).toNat < c.arena_cap := by rw [hcr_end_z]; omega
                have har_c0_st : (cref.setWidth 64).toNat <
                    ((ar_cur.set (cref.setWidth 64 + 2#64).toNat (BitVec.ofNat 32 nsz)).set
                      (cref.setWidth 64 + 1#64).toNat 2#32).length := by
                  simp only [List.length_set]; exact har_c_0
                have har_end_st : (cref.setWidth 64 + 3#64 +
                    (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).setWidth 64 -
                      1#64).toNat <
                    (((ar_cur.set (cref.setWidth 64 + 2#64).toNat (BitVec.ofNat 32 nsz)).set
                      (cref.setWidth 64 + 1#64).toNat 2#32).set
                      (cref.setWidth 64).toNat (ar_cur[(cref.setWidth 64).toNat]'har_c_0 |||
                        0x00800000#32)).length := by
                  simp only [List.length_set]; rw [har_c]; exact hcr_end_bd
                fa_fast_steps
                · have hsh0_raw : ar_cur[(cref.setWidth 64).toNat]'har_c_0 &&& 0x00800000#32 =
                      0#32 := by assumption
                  have hsh0 : (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32 := by
                    rwa [← hhdr_s2]
                  let ar_st0_raw := (((ar_cur.set (cref.setWidth 64 + 2#64).toNat
                      (BitVec.ofNat 32 nsz)).set (cref.setWidth 64 + 1#64).toNat 2#32).set
                      (cref.setWidth 64).toNat (ar_cur[(cref.setWidth 64).toNat]'har_c_0 |||
                        0x00800000#32)).set (cref.setWidth 64 + 3#64 +
                        (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).setWidth 64 -
                          1#64).toNat 0xFFFFFFFF#32
                  let ar_st0 := (((ar_cur.set (cref.toNat + 2)
                      (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32).set cref.toNat
                      (fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32)).set
                      (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
                  have har_st0 : ar_st0_raw = ar_st0 := by
                    dsimp only [ar_st0_raw, ar_st0]
                    rw [hhdr_s2, hcr_end_z, hcr0_z, hcr1_z, hcr2_z]
                  have hm_st0 :
                      (FullMem c { s2 with core := { s2.core with arena := ar_st0 } } ⋆ R) _ :=
                    fullMem_of_eq (s1 := { s2 with core := { s2.core with arena := ar_st0_raw } })
                      (s2 := { s2 with core := { s2.core with arena := ar_st0 } })
                      (by assumption) (congrArg (fun a => { s2.core with arena := a }) har_st0) rfl
                  exact hJ3 () _ (otfs_large_hdr_ok true har_len har_c (by omega) h4_old hnsz3
                    hnsz_lt hlits_info hmapeq hout_m har1_q har1_s2 hhdr_eq (Or.inl ⟨rfl, hsh0⟩)
                    hm_st0 rfl)
                · have hsh1_raw : ar_cur[(cref.setWidth 64).toNat]'har_c_0 &&& 0x00800000#32 ≠
                      0#32 := by assumption
                  have hsh1 : (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) ≠ 0#32 := by
                    rwa [← hhdr_s2]
                  let ar_st1_raw := (ar_cur.set (cref.setWidth 64 + 2#64).toNat
                      (BitVec.ofNat 32 nsz)).set (cref.setWidth 64 + 1#64).toNat 2#32
                  let ar_st1 := (ar_cur.set (cref.toNat + 2)
                      (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
                  have har_st1 : ar_st1_raw = ar_st1 := by
                    dsimp only [ar_st1_raw, ar_st1]; rw [hcr2_z, hcr1_z]
                  have hm_st1 :
                      (FullMem c { s2 with core := { s2.core with arena := ar_st1 } } ⋆ R) _ :=
                    fullMem_of_eq (s1 := { s2 with core := { s2.core with arena := ar_st1_raw } })
                      (s2 := { s2 with core := { s2.core with arena := ar_st1 } })
                      (by assumption) (congrArg (fun a => { s2.core with arena := a }) har_st1) rfl
                  exact hJ3 () _ (otfs_large_hdr_ok false har_len har_c (by omega) h4_old hnsz3
                    hnsz_lt hlits_info hmapeq hout_m har1_q har1_s2 hhdr_eq (Or.inr ⟨rfl, hsh1⟩)
                    hm_st1 rfl)
          · intro L2 hL2; fa_fast_steps; dsimp only at hs01
            have har1_eq_s2 : s2.core.arena = ar1 := by rw [hs2_eq, hs1_c]
            have hm2_ar1 :
                (FullMem c { s2 with core := { s2.core with arena := ar1 } } ⋆ R) m2 :=
              fullMem_of_eq hm2' (congrArg (fun a => { s2.core with arena := a }) har1_eq_s2) rfl
            obtain ⟨omap0, hinv0⟩ := otfs_large_loop2_init har_len (by omega) h4_old hs01
            exact hL2 (old_sz - 2) _ m2 ⟨2, 1, ar1, omap0, hm2_ar1, rfl, rfl, hinv0⟩
    · intro L hL; fa_fast_steps
      exact hL (old_sz - 2) (1#32, 2#32, ()) m ⟨2, rfl, rfl, Nat.le_refl _, by omega, rfl,
        by simp [otfsActCnt, List.drop_eq_nil_of_le (show (List.range 2).length ≤ 2 by simp)]⟩
  · intro J0 hJ0; fa_fast_steps
    · exact hJ0 _ _ ⟨rfl, Or.inr ⟨hor1, hor0 ▸ ‹_›⟩⟩
    · exact hfail
    · exact hJ0 _ _ ⟨rfl, Or.inl ⟨hor0, hor1 ▸ ‹_›⟩⟩

theorem full_otfs_large_wp (Γ : Env)
    (hUnw : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullOtfsLargeSpec args m Q X →
      Func.wp Γ full_otfs_large_body args m Q X :=
  full_otfs_large_wp_weak Γ (fun a m Q X ⟨c, s, R, hh, hl, hly, hm, hQ⟩ =>
    hUnw a m Q X ⟨c, s, R, hh, hl, hly, hm, fun wv ws wu m' hl' hly' hmw _ hm' =>
      hQ wv ws wu m' hl' hly' hmw hm'⟩) hPush

end LeanQbe.T.Examples.Kissat.Full
