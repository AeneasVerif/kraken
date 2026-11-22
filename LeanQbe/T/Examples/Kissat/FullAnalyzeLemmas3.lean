module

public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas2

/-!
# Kissat `D-Full` Conflict Analysis, OTFS & Eager Subsumption (Part 3)

Provides in-place shrink, watch-slice push/blocker update, and clause-swap helpers in
`FullAnalyzeHelpers`, plus `Func.wp` proofs for `full_det_new_level`, `full_otfs_subsume`,
and `full_otfs_bin`.
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

open FullAnalyzeTactics FullAnalyzeSpecs FullAnalyzeHelpers
open scoped FullArenaTactics FullAnalyzeTactics

/-! ## 1. Shared in-place shrink, watch-blocker, swap helpers -/

namespace FullAnalyzeHelpers

private theorem skipShrk_of_first_sent {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 →
      (∀ i, p ≤ i → i < t → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      t - p + 1 ≤ fuel → fullArenaSkipShrk ar alen p fuel = t + 1
  | 0, _, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hne_lt, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]
    by_cases hpeq : p = t
    · subst p; simp [hsent]
    · have hne := hne_lt p (Nat.le_refl p) (by omega)
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      exact skipShrk_of_first_sent (by omega) hta hsent
        (fun i hi1 hi2 => hne_lt i (by omega) hi2) (by omega)

private theorem skipShrk_first_sent {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 → t - p + 1 ≤ fuel →
      ∃ t0, p ≤ t0 ∧ t0 ≤ t ∧ fullArenaSkipShrk ar alen p fuel = t0 + 1 ∧
        ar[t0]? = some 0xFFFFFFFF#32 ∧
        (∀ i, p ≤ i → i < t0 → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
  | 0, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]; split
    · rename_i hne
      have hp_ne : p ≠ t := by rintro rfl; simp [hsent] at hne
      obtain ⟨t0, h1, h2, h3, h4, h5⟩ :=
        skipShrk_first_sent (fuel := fuel) (p := p + 1) (by omega) hta hsent (by omega)
      refine ⟨t0, by omega, h2, h3, h4, fun i hi1 hi2 => ?_⟩
      by_cases hip : i = p
      · subst i; exact hne
      · exact h5 i (by omega) hi2
    · rename_i heq
      have heqv : ar[p]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
        Classical.byContradiction fun hn => heq hn
      have hlen_t : t < ar.length := (List.getElem?_eq_some_iff.mp hsent).1
      have hp_some : ar[p]? = some (ar[p]'(by omega)) := List.getElem?_eq_getElem (by omega)
      rw [hp_some, Option.getD_some] at heqv
      exact ⟨p, Nat.le_refl p, hpt, rfl, by rw [hp_some, heqv], fun _ h1 h2 => by omega⟩

theorem fa_inPlaceShrink_preserves_fullArena {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {arena' : List (BitVec 32)} {cref nsz : Nat}
    (ha : FullArenaClausesInv c F_cur k) (hlen : k.LengthsOk c)
    (hcref : cref ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSizeCore k cref)
    (har_len' : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some
      (if (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdrCore k cref ||| 0x00800000#32
      else fullArenaHdrCore k cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_ne : ∀ j, nsz ≤ j → j < fullArenaClauseSizeCore k cref - 1 →
      arena'[cref + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hlast_sent : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ i →
      arena'[i]? = k.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLitsCore { k with arena := arena' } cref,
      l < 2 * k.cur_vars)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { k with arena := arena' } cref))) :
    let k' := { k with arena := arena' }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∧
    fullArenaClauseSizeCore k' cref = nsz ∧ fullArenaClauseGarbCore k' cref = false ∧
    FullArenaClausesInv c F_cur k' := by
  intro k'
  let old_sz := fullArenaClauseSizeCore k cref
  have hwf := ha.refs_wf cref hcref
  have hnsz_lt32 : nsz < 2 ^ 32 := by
    have := (k.arena[cref + 2]?.getD 0#32).isLt; unfold fullArenaClauseSizeCore at hnsz_lt; omega
  have hsz_cref' : fullArenaClauseSizeCore k' cref = nsz := by
    unfold fullArenaClauseSizeCore k'; rw [hsz', Option.getD_some, bv32_ofNat_toNat hnsz_lt32]
  have hcref_shrk' : (fullArenaHdrCore k' cref &&& 0x00800000#32) ≠ 0#32 := by
    unfold fullArenaHdrCore k'; rw [hhdr', Option.getD_some]; split
    · exact bv32_or_shrk_shrk _
    · rename_i hne; exact hne
  have hcref_garb' : fullArenaClauseGarbCore k' cref = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [hhdr', Option.getD_some]
    unfold fullArenaClauseGarbCore at hng
    split
    · rw [bv32_or_shrk_garb]; exact hng
    · exact hng
  have hcref_nxt : fullArenaNextOff arena' k.arena_len cref =
      fullArenaNextOff k.arena k.arena_len cref := by
    have hn1 : ¬ (cref + 3 > k.arena_len) := by omega
    have hn2' : ¬ (cref + 3 + nsz > k.arena_len) := by omega
    have hshk' : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
      simpa [fullArenaHdrCore, k'] using hcref_shrk'
    conv => lhs; unfold fullArenaNextOff
    simp only [hn1, ↓reduceIte, hsz', Option.getD_some, bv32_ofNat_toNat hnsz_lt32, hn2', hshk',
      ne_eq, not_false_eq_true]
    by_cases hsh0 : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
    · have hn2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      have hnxt0 : fullArenaNextOff k.arena k.arena_len cref = cref + 3 + old_sz := by
        unfold fullArenaNextOff
        simp only [hn1, ↓reduceIte, hn2, show (k.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
          from hsh0, ne_eq]; rfl
      rw [hnxt0]
      have hss := skipShrk_of_first_sent (ar := arena') (alen := k.arena_len)
        (t := cref + 3 + old_sz - 1) (p := cref + 3 + nsz) (fuel := k.arena_len - (cref + 3 + nsz))
        (by dsimp only [old_sz]; omega) (by dsimp only [old_sz]; omega) (hlast_sent hsh0)
        (fun i hi1 hi2 => hpad_ne (i - (cref + 3)) (by omega) (by dsimp only [old_sz] at hi2; omega)
          |> fun hne => by rwa [show cref + 3 + (i - (cref + 3)) = i by omega] at hne)
        (by dsimp only [old_sz]; omega)
      rw [hss]; dsimp only [old_sz]; omega
    · obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref hcref hsh0
      have hget_c : k.arena[cref]? = some (fullArenaHdrCore k cref) := by
        have := hlen.arena_len_arr; have := hlen.arena_len_le
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hn2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      have hsh_ar : (k.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_c, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, ht0_hi, ht0_nxt, ht0_sent, ht0_first⟩ := skipShrk_first_sent
        (ar := k.arena) (alen := k.arena_len) (t := t) (p := cref + 3 + old_sz)
        (fuel := k.arena_len - (cref + 3 + old_sz)) (by omega) ht2 hsent (by omega)
      have hnxt0 : fullArenaNextOff k.arena k.arena_len cref = t0 + 1 := by
        unfold fullArenaNextOff; simp only [hn1, ↓reduceIte, hn2, hsh_ar, ne_eq,
          not_false_eq_true]; exact ht0_nxt
      rw [hnxt0]
      refine skipShrk_of_first_sent (ar := arena') (alen := k.arena_len) (t := t0)
        (p := cref + 3 + nsz) (fuel := k.arena_len - (cref + 3 + nsz))
        (by omega) (by omega) (by rw [hout t0 (Or.inr ht0_lo)]; exact ht0_sent)
        (fun i hi1 hi2 => ?_) (by omega)
      by_cases hmid : i < cref + 3 + old_sz
      · by_cases hlast : i = cref + 3 + old_sz - 1
        · rw [hlast]; exact hlast_keep hsh0
        · have hj := hpad_ne (i - (cref + 3)) (by omega)
            (by dsimp only [old_sz] at hmid hlast; omega)
          rwa [show cref + 3 + (i - (cref + 3)) = i by omega] at hj
      · rw [hout i (Or.inr (by omega))]; exact ht0_first i (by omega) hi2
  have hout_ref : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      cref + 3 + old_sz ≤ r := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨ha.disjoint hr hcref hlt, fullArenaScanRefs_disjoint hr hcref hlt⟩
    · exact Or.inr (ha.disjoint hcref hr hgt)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r; exact hcref_nxt
    · rcases hout_ref r hr hrc with ⟨hlt, _⟩ | hgt
      · have hr3 := (ha.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (hout r (Or.inl (by omega)))
          (hout (r + 2) (Or.inl (by omega))) fun i _ _ => hout i (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (hout r (Or.inr hgt))
          (hout (r + 2) (Or.inr (by omega))) fun i _ _ => hout i (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hother : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr hne; have hrwf := ha.refs_wf r hr
    have := hlen.arena_len_arr; have := hlen.arena_len_le
    rcases hout_ref r hr hne with ⟨hlt, _⟩ | hgt
    · have hszr : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
        unfold fullArenaClauseSizeCore k'; rw [hout (r + 2) (Or.inl (by omega))]
      have hgar : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [hout r (Or.inl (by omega))]
      refine ⟨hszr, hgar, fullArenaClauseLitsCore_eq_of_hold (by omega)
        (by dsimp only [k']; rw [har_len']; omega) hszr
        fun j hj => hout (r + 3 + j) (Or.inl (by omega))⟩
    · have hszr : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
        unfold fullArenaClauseSizeCore k'; rw [hout (r + 2) (Or.inr (by omega))]
      have hgar : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [hout r (Or.inr hgt)]
      refine ⟨hszr, hgar, fullArenaClauseLitsCore_eq_of_hold (by omega)
        (by dsimp only [k']; rw [har_len']; omega) hszr
        fun j hj => hout (r + 3 + j) (Or.inr (by omega))⟩
  refine ⟨hrefs, hother, hsz_cref', hcref_garb', ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr; rw [hrefs] at hr; dsimp only [k']; rw [hnxt r hr]
    by_cases hrc : r = cref
    · subst r; rw [hsz_cref']; exact ⟨hwf.1, hnsz3, by omega, hwf.2.2.2.1, hwf.2.2.2.2⟩
    · rw [(hother r hr hrc).1]; exact ha.refs_wf r hr
  · intro r hr hsh; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; rw [hsz_cref']
      by_cases hsh0 : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
      · exact ⟨cref + 3 + old_sz - 1, by dsimp only [old_sz]; omega,
          by dsimp only [k', old_sz]; omega, hlast_sent hsh0⟩
      · obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref hr hsh0
        exact ⟨t, by omega, ht2, by rw [hout t (Or.inr ht1)]; exact hsent⟩
    · rcases hout_ref r hr hrc with ⟨_, _⟩ | hgt
      · have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore k' at hsh; rwa [hout r (Or.inl (by omega))] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
        obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel (ha.refs_wf r hr).1 hsh0 ht1 ht2 hsent
        rw [(hother r hr hrc).1]
        exact ⟨t0, ht0_lo, by dsimp only [k']; omega,
          by dsimp only [k']; rw [hout t0 (Or.inl (by omega))]; exact ht0_sent⟩
      · have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore k' at hsh; rwa [hout r (Or.inr hgt)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
        rw [(hother r hr hrc).1]
        exact ⟨t, ht1, ht2, by rw [hout t (Or.inr (by omega))]; exact hsent⟩
  · intro r hr hng l hl; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hlits_lt' l hl
    · rw [(hother r hr hrc).2.1] at hng; rw [(hother r hr hrc).2.2] at hl
      exact ha.lits_lt r hr hng l hl
  · intro r hr hng; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hent'
    · rw [(hother r hr hrc).2.1] at hng; rw [(hother r hr hrc).2.2]
      exact ha.entails r hr hng

theorem fa_inPlaceShrink_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut cut' : Nat} {k : FullCoreState}
    {arena' : List (BitVec 32)} {cref nsz : Nat}
    (hw : FullWitnessCutInv c F0 F_cur cut k) (hlen : k.LengthsOk c)
    (hcut : cut' ≤ cut) (hcref : cref ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSizeCore k cref)
    (har_len' : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some
      (if (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdrCore k cref ||| 0x00800000#32
      else fullArenaHdrCore k cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_ne : ∀ j, nsz ≤ j → j < fullArenaClauseSizeCore k cref - 1 →
      arena'[cref + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hlast_sent : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ i →
      arena'[i]? = k.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLitsCore { k with arena := arena' } cref,
      l < 2 * k.cur_vars)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { k with arena := arena' } cref)))
    (hnonact : ∀ idx < k.trail_end,
      (idx < cut' ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let k' := { k with arena := arena' }
    FullWitnessCutInv c F0 F_cur cut' k' ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    fullArenaClauseSizeCore k' cref = nsz ∧ fullArenaClauseGarbCore k' cref = false ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro k'
  obtain ⟨hrefs, hother, hsz_c, hng_c, harena'⟩ := fa_inPlaceShrink_preserves_fullArena hw.arena
    hlen hcref hng hnsz3 hnsz_lt har_len' hhdr' hsz' hpad_ne hlast_sent hlast_keep hout hlits_lt'
    hent'
  have hcw := arenaUpdate_preserves_fullWitnessCut (hw.shrink_cut hcut) harena' hrefs
    fun idx hidx hc hne hlg => by
      have hrs := hw.reason_inv idx hidx (hc.elim (fun h => Or.inl (by omega)) Or.inr) hne
      rw [ite_eq_right (fun h => absurd hlg h)] at hrs
      have hne_c := hnonact idx hidx hc hne hlg
      have ho := hother _ hrs.1 hne_c
      exact ⟨ho.2.1.trans hrs.2.1, ho.2.2 ▸ List.Perm.refl _⟩
  exact ⟨hcw, hrefs, hsz_c, hng_c, hother⟩

theorem fa_watchSlice_append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .large (by simpa using hw0) (by simpa using hw1) hflag hlt href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw1))
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr)
      (ih (p' := p' + 2) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw1))

private theorem modeWatches_eq {F : List (List Nat)} {k : FullCoreState} (h : k.dense_mode = 0#64) :
    ModeWatchesInv F k = WatchesInv F k := by
  unfold ModeWatchesInv; simp [h]

theorem fa_modeWatches_set_in_slice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p : Nat} {b' : BitVec 32} (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    (hlit : lit < 2 * k.cur_vars) (hp_len : p < k.wstk.length)
    (hlo : fullWatchOffCore k lit ≤ p)
    (hhi : p < fullWatchOffCore k lit + fullWatchSizeCore k lit)
    (hne' : b' ≠ 0xFFFFFFFF#32)
    (hslice' : WatchSliceOk F_cur { k with wstk := k.wstk.set p b' } lit
      (fullWatchOffCore k lit) (fullWatchSizeCore k lit)) :
    ModeWatchesInv F_cur { k with wstk := k.wstk.set p b' } := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  rw [modeWatches_eq hdm] at hw
  let k' : FullCoreState := { k with wstk := k.wstk.set p b' }
  change ModeWatchesInv F_cur k'
  rw [modeWatches_eq (k := k') hdm]
  refine ⟨⟨hw.layout.bounds, hw.layout.pos_off, hw.layout.disjoint, fun l hl idx hidx => ?_⟩,
    fun l hl => ?_⟩
  · change (k.wstk.set p b')[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32
    by_cases hp : fullWatchOffCore k l + idx = p
    · rw [hp, List.getElem?_set_self hp_len]; exact fun he => hne' (Option.some.inj he)
    · rw [List.getElem?_set_ne (Ne.symm hp)]; exact hw.layout.no_sentinel l hl idx hidx
  · change WatchSliceOk F_cur k' l (fullWatchOffCore k l) (fullWatchSizeCore k l)
    by_cases hll : l = lit
    · subst hll; exact hslice'
    · have hdisj_all := hw.layout.disjoint l lit hl hlit hll
      refine (hw.slices l hl).mono (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
        fun idx hi1 hi2 => ?_
      have hdisj := hdisj_all (by omega) (by omega)
      change (k.wstk.set p b')[idx]? = k.wstk[idx]?
      rw [List.getElem?_set_ne (by rcases hdisj with h1 | h2 <;> omega)]

theorem fa_watchPush_bin_preserves {F_cur : List (List Nat)} {k : FullCoreState}
    {lit : Nat} {w0 : BitVec 32}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' oom' nb' : BitVec 64}
    (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    (hlit : lit < 2 * k.cur_vars)
    (hlay : WatchStackLayout
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom',
               num_binary := nb' })
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore { k with wvec := wvec' } l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec' } l + idx]? =
          k.wstk[fullWatchOffCore k l + idx]?)
    (hsz : fullWatchSizeCore { k with wvec := wvec' } lit = fullWatchSizeCore k lit + 1)
    (hsame : ∀ idx < fullWatchSizeCore k lit,
      wstk'[fullWatchOffCore { k with wvec := wvec' } lit + idx]? =
        k.wstk[fullWatchOffCore k lit + idx]?)
    (hw0 : wstk'[fullWatchOffCore { k with wvec := wvec' } lit + fullWatchSizeCore k lit]? =
      some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom',
               num_binary := nb' } := by
  let k' : FullCoreState := { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := wu', oom := oom', num_binary := nb' }
  rw [modeWatches_eq hdm] at hw
  change ModeWatchesInv F_cur k'; rw [modeWatches_eq (k := k') hdm]
  refine ⟨hlay, fun l hl => ?_⟩
  by_cases hll : l = lit
  · subst hll; change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l + 1 from hsz]
    refine fa_watchSlice_append_bin (k := k) (k' := k') (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsame idx hi)
      (hw.slices l hl) ?_ hflag hne hlt hent
    simpa only [k', fullWatchOffCore] using hw0
  · obtain ⟨hszl, hsl⟩ := hother l hl hll
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l from hszl]
    exact fa_watchSlice_relocate (k := k) (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsl idx hi) (hw.slices l hl)

theorem fa_watchPush_large_preserves {F_cur : List (List Nat)} {k : FullCoreState}
    {lit : Nat} {w0 cref : BitVec 32}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' oom' : BitVec 64}
    (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    (hlit : lit < 2 * k.cur_vars)
    (hlay : WatchStackLayout
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' })
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore { k with wvec := wvec' } l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec' } l + idx]? =
          k.wstk[fullWatchOffCore k l + idx]?)
    (hsz : fullWatchSizeCore { k with wvec := wvec' } lit = fullWatchSizeCore k lit + 2)
    (hsame : ∀ idx < fullWatchSizeCore k lit,
      wstk'[fullWatchOffCore { k with wvec := wvec' } lit + idx]? =
        k.wstk[fullWatchOffCore k lit + idx]?)
    (hw0 : wstk'[fullWatchOffCore { k with wvec := wvec' } lit + fullWatchSizeCore k lit]? =
      some w0)
    (hw1 : wstk'[fullWatchOffCore { k with wvec := wvec' } lit + fullWatchSizeCore k lit + 1]? =
      some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k) :
    ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' } := by
  let k' : FullCoreState := { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := wu', oom := oom' }
  rw [modeWatches_eq hdm] at hw
  change ModeWatchesInv F_cur k'; rw [modeWatches_eq (k := k') hdm]
  refine ⟨hlay, fun l hl => ?_⟩
  by_cases hll : l = lit
  · subst hll; change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l + 2 from hsz]
    refine fa_watchSlice_append_large (k := k) (k' := k') (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsame idx hi)
      (hw.slices l hl) ?_ ?_ hflag hlt href
    · simpa only [k', fullWatchOffCore] using hw0
    · simpa only [k', fullWatchOffCore] using hw1
  · obtain ⟨hszl, hsl⟩ := hother l hl hll
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l from hszl]
    exact fa_watchSlice_relocate (k := k) (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
      (fun idx hi => by simpa only [k', fullWatchOffCore] using hsl idx hi) (hw.slices l hl)

private theorem list_countP_set {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (i : Nat) (y : α) (_ : i < xs.length),
      (xs.set i y).countP p + (if p xs[i] then 1 else 0) = xs.countP p + (if p y then 1 else 0)
  | [], _, _, hi => by simp at hi
  | x :: xs, 0, y, _ => by
    simp only [List.set_cons_zero, List.countP_cons, List.getElem_cons_zero]
    by_cases hpx : p x <;> by_cases hpy : p y <;> simp [hpx, hpy] <;> omega
  | x :: xs, i + 1, y, hi => by
    have ih := list_countP_set p xs i y (by simpa using hi)
    simp only [List.set_cons_succ, List.countP_cons, List.getElem_cons_succ]
    by_cases hpx : p x <;> simp [hpx] <;> omega

private theorem list_swap_perm {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)).Perm xs := by
  by_cases hij : j = i
  · subst hij; simp [List.set_getElem_self]
  · rw [List.perm_iff_count]; intro a
    have hc1 := list_countP_set (· == a) (xs.set i (xs[j]'hj)) j (xs[i]'hi) (by simpa using hj)
    have hc2 := list_countP_set (· == a) xs i (xs[j]'hj) hi
    simp only [List.count] at hc1 hc2 ⊢
    rw [List.getElem_set_ne (Ne.symm hij)] at hc1; omega

theorem fa_swapCl_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k) {cref i j : Nat}
    (hcref : cref ∈ fullArenaClauseRefsCore k)
    (hi : i < fullArenaClauseSizeCore k cref) (hj : j < fullArenaClauseSizeCore k cref) :
    let lits := k.arena
    let li := lits[cref + 3 + i]?.getD 0#32
    let lj := lits[cref + 3 + j]?.getD 0#32
    let arena' := (lits.set (cref + 3 + i) lj).set (cref + 3 + j) li
    let k' := { k with arena := arena' }
    FullWitnessCutInv c F0 F_cur cut k' ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref ∧
    fullArenaClauseGarbCore k' cref = fullArenaClauseGarbCore k cref ∧
    (fullArenaClauseLitsCore k' cref).Perm (fullArenaClauseLitsCore k cref) ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro lits li lj arena' k'
  have ha := hw.arena
  have hwf := ha.refs_wf cref hcref
  have hlen_ar : lits.length = c.arena_cap := hlen.arena_len_arr
  have hle_ar : k.arena_len ≤ c.arena_cap := hlen.arena_len_le
  have hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ lits.length := by omega
  have har'_len : arena'.length = c.arena_cap := by simp [arena', lits, hlen_ar]
  have hout : ∀ idx, idx < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ idx →
      arena'[idx]? = lits[idx]? := fun idx hidx => by
    dsimp [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' k.arena_len r = fullArenaNextOff lits k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      exact fullArenaNextOff_congr_block (hout _ (Or.inl (by omega)))
        (hout _ (Or.inl (by omega))) (fun q hq1 _ => hout q (Or.inr hq1))
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := ha.disjoint hr hcref hlt
        have hdn : fullArenaNextOff lits k.arena_len r ≤ cref :=
          fullArenaScanRefs_disjoint hr hcref hlt
        have := (ha.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (hout _ (Or.inl (by omega)))
          (hout _ (Or.inl (by omega))) fun q _ hq2 => hout q (Or.inl (by omega))
      · have hgt_d := ha.disjoint hcref hr hgt
        exact fullArenaNextOff_congr_block (hout _ (Or.inr hgt_d))
          (hout _ (Or.inr (by omega))) fun q hq1 _ => hout q (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_c : fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref := by
    unfold fullArenaClauseSizeCore k'; rw [hout (cref + 2) (Or.inl (by omega))]
  have hng_c : fullArenaClauseGarbCore k' cref = fullArenaClauseGarbCore k cref := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [hout cref (Or.inl (by omega))]
  have hperm : (fullArenaClauseLitsCore k' cref).Perm (fullArenaClauseLitsCore k cref) := by
    let xs := (lits.drop (cref + 3)).take (fullArenaClauseSizeCore k cref)
    have hxs_len : xs.length = fullArenaClauseSizeCore k cref := by
      simp [xs, List.length_take, List.length_drop]; omega
    have hli : li = xs[i]'(by omega) := by
      dsimp only [li]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [xs, List.getElem_take, List.getElem_drop]
    have hlj : lj = xs[j]'(by omega) := by
      dsimp only [lj]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [xs, List.getElem_take, List.getElem_drop]
    have hswap : (arena'.drop (cref + 3)).take (fullArenaClauseSizeCore k cref) =
        (xs.set i lj).set j li := by
      apply List.ext_getElem
      · simp [xs, arena', List.length_take, List.length_drop]
      · intro p hp1 hp2
        have hplt : p < fullArenaClauseSizeCore k cref := by
          simp [List.length_take, List.length_drop] at hp1; omega
        rw [List.getElem_take, List.getElem_drop]
        have hopt : arena'[cref + 3 + p]? = some (((xs.set i lj).set j li)[p]'hp2) := by
          dsimp only [arena']
          by_cases hpj : p = j
          · subst p; rw [List.getElem?_set_self (by simp [List.length_set, hlen_ar]; omega),
              List.getElem_set_self (by simp [List.length_set, hxs_len]; omega), hli]
          · rw [List.getElem?_set_ne (by omega), List.getElem_set_ne (Ne.symm hpj)]
            by_cases hpi : p = i
            · subst p; rw [List.getElem?_set_self (by rw [hlen_ar]; omega),
                List.getElem_set_self (by rw [List.length_set, hxs_len]; exact hi), hlj]
            · rw [List.getElem?_set_ne (by omega), List.getElem_set_ne (Ne.symm hpi),
                List.getElem?_eq_getElem (by omega)]
              simp [xs, List.getElem_take, List.getElem_drop]
        have hopt0 := List.getElem?_eq_getElem (show cref + 3 + p < arena'.length by
          rw [har'_len]; omega)
        rw [hopt0] at hopt; exact Option.some.inj hopt
    unfold fullArenaClauseLitsCore k'; rw [hsz_c, hswap]
    have hsw : ((xs.set i lj).set j li).Perm xs := by
      simpa only [hli, hlj] using list_swap_perm xs (hxs_len ▸ hi) (hxs_len ▸ hj)
    exact hsw.map BitVec.toNat
  have hother : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr hne
    have hdisj : r + 3 + fullArenaClauseSizeCore k r ≤ cref ∨
        cref + 3 + fullArenaClauseSizeCore k cref ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (ha.disjoint hr hcref hlt)
      · exact Or.inr (ha.disjoint hcref hr hgt)
    have hrwf := ha.refs_wf r hr
    have hszr : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
      unfold fullArenaClauseSizeCore k'
      rcases hdisj with h1 | h2
      · rw [hout (r + 2) (Or.inl (by omega))]
      · rw [hout (r + 2) (Or.inr (by omega))]
    have hgar : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore k'
      rcases hdisj with h1 | h2
      · rw [hout r (Or.inl (by omega))]
      · rw [hout r (Or.inr h2)]
    have := hlen.arena_len_arr; have := hlen.arena_len_le
    refine ⟨hszr, hgar, fullArenaClauseLitsCore_eq_of_hold (by omega)
      (by dsimp [k']; rw [har'_len]; omega) hszr fun q hq => ?_⟩
    rcases hdisj with h1 | h2
    · exact hout (r + 3 + q) (Or.inl (by omega))
    · exact hout (r + 3 + q) (Or.inr (by omega))
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp [k']; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_c]; exact ha.refs_wf cref hr
      · rw [(hother r hr hrc).1]; exact ha.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hr_out : r < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ r := by
        by_cases hrc : r = cref
        · subst r; exact Or.inl (by omega)
        · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
          · have := ha.disjoint hr hcref hlt; exact Or.inl (by omega)
          · exact Or.inr (ha.disjoint hcref hr hgt)
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh; rwa [hout r hr_out] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
      by_cases hrc : r = cref
      · subst r; rw [hsz_c]; exact ⟨t, ht1, ht2, by dsimp [k']; rwa [hout t (Or.inr ht1)]⟩
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have hdisj := ha.disjoint hr hcref hlt
          have hnxt_lt := fullArenaScanRefs_disjoint hr hcref hlt
          have hr3 := (ha.refs_wf r hr).1
          have hget_r : lits[r]? = some (fullArenaHdrCore k r) := by
            unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsh_ar : (lits[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
            rw [hget_r, Option.getD_some]; exact hsh0
          obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
            fullArenaNextOff_hits_sentinel hr3 hsh_ar ht1 ht2 hsent
          dsimp only [lits] at ht0_nxt
          rw [(hother r hr hrc).1]
          exact ⟨t0, ht0_lo, by dsimp [k']; omega,
            by dsimp [k']; rw [hout t0 (Or.inl (by omega))]; exact ht0_sent⟩
        · have hdisj := ha.disjoint hcref hr hgt
          rw [(hother r hr hrc).1]
          exact ⟨t, ht1, ht2, by dsimp [k']; rw [hout t (Or.inr (by omega))]; exact hsent⟩
    · intro r hr hng l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hng_c] at hng; exact ha.lits_lt cref hr hng l (hperm.mem_iff.mp hl)
      · rw [(hother r hr hrc).2.1] at hng; rw [(hother r hr hrc).2.2] at hl
        exact ha.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hng_c] at hng
        exact entails_of_mem_or_false (ha.entails cref hr hng) fun l hl =>
          Or.inl (hperm.symm.mem_iff.mp hl)
      · rw [(hother r hr hrc).2.1] at hng; rw [(hother r hr hrc).2.2]
        exact ha.entails r hr hng
  refine ⟨arenaUpdate_preserves_fullWitnessCut hw harena' hrefs fun idx hidx hc hne hlg => ?_,
    hrefs, hsz_c, hng_c, hperm, hother⟩
  have hrs := hw.reason_inv idx hidx hc hne
  rw [ite_eq_right (fun h => absurd hlg h)] at hrs
  by_cases hrc : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = cref
  · rw [hrc] at hrs ⊢; exact ⟨hng_c.trans hrs.2.1, hperm⟩
  · have ho := hother _ hrs.1 hrc; exact ⟨ho.2.1.trans hrs.2.1, ho.2.2 ▸ List.Perm.refl _⟩

theorem fa_watchPush_fail_preserves {F_cur : List (List Nat)} {k : FullCoreState}
    (hdm : k.dense_mode = 0#64) (hw : ModeWatchesInv F_cur k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' oom' : BitVec 64}
    (hlay : WatchStackLayout
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' })
    (hsame : ∀ l < 2 * k.cur_vars,
      fullWatchSizeCore { k with wvec := wvec' } l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec' } l + idx]? =
          k.wstk[fullWatchOffCore k l + idx]?) :
    ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', oom := oom' } := by
  let k' : FullCoreState := { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := wu', oom := oom' }
  rw [modeWatches_eq hdm] at hw
  change ModeWatchesInv F_cur k'; rw [modeWatches_eq (k := k') hdm]
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  refine ⟨hlay, fun l hl => ?_⟩
  obtain ⟨hszl, hsl⟩ := hsame l hl
  change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
  rw [show fullWatchSizeCore k' l = fullWatchSizeCore k l from hszl]
  exact fa_watchSlice_relocate (k := k) (k' := k') hrefl (Nat.le_refl k.cur_vars) (fun _ r => r)
    (fun idx hi => by simpa only [k', fullWatchOffCore] using hsl idx hi) (hw.slices l hl)

theorem nodup_map_getElem_inj {α β : Type} (f : α → β) :
    ∀ {xs : List α} {j1 j2 : Nat} (h1 : j1 < xs.length) (h2 : j2 < xs.length),
      (xs.map f).Nodup → f (xs[j1]'h1) = f (xs[j2]'h2) → j1 = j2
  | [], _, _, h1, _, _, _ => by simp at h1
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | _ :: xs, 0, j2 + 1, _, h2, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact absurd (List.mem_map.mpr ⟨xs[j2]'(by simpa using h2), List.getElem_mem .., heq.symm⟩)
      hnd.1
  | _ :: xs, j1 + 1, 0, h1, _, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact absurd (List.mem_map.mpr ⟨xs[j1]'(by simpa using h1), List.getElem_mem .., heq⟩) hnd.1
  | _ :: xs, j1 + 1, j2 + 1, h1, h2, hnd, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_map_getElem_inj f (by simpa using h1) (by simpa using h2)
      hnd.2 heq)

end FullAnalyzeHelpers

/-! ## 2. `full_det_new_level` (`fullDetNewLevelSpec`) -/

theorem full_det_new_level_wp (Γ : Env) :
    ∀ args m Q X, fullDetNewLevelSpec args m Q X →
      Func.wp Γ full_det_new_level_body args m Q X := by
  rintro ⟨h, jump, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl_lt, hm, hQ⟩
  fa_fast_steps
  · have h0 : s.core.cur_level = 0 := ofNat64_eq_zero hcl_lt ‹_›
    exact hQ 0#64 (fun _ => rfl) (fun hpos => by omega)
  · have hpos : 0 < s.core.cur_level := ofNat64_pos ‹_›
    exact hQ jump (fun h0 => by omega) (fun _ hlt => ⟨Nat.le_refl _, hlt⟩)
  · have hpos : 0 < s.core.cur_level := ofNat64_pos ‹_›
    have hsub1 : (BitVec.ofNat 64 s.core.cur_level - 1).toNat = s.core.cur_level - 1 := by
      simpa [bv64_ofNat_toNat hcl_lt] using
        bv64_sub1_toNat (f := BitVec.ofNat 64 s.core.cur_level) ‹_›
    have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
    exact hQ (BitVec.ofNat 64 s.core.cur_level - 1) (fun h0 => by omega)
      (fun _ _ => by rw [hsub1]; constructor <;> omega)
  · have hpos : 0 < s.core.cur_level := ofNat64_pos ‹_›
    exact hQ jump (fun h0 => by omega) (fun _ hlt => ⟨Nat.le_refl _, hlt⟩)

/-! ## 3. `full_otfs_subsume` (`fullOtfsSubsumeSpec`) -/

theorem full_otfs_subsume_wp (Γ : Env) :
    ∀ args m Q X, fullOtfsSubsumeSpec args m Q X →
      Func.wp Γ full_otfs_subsume_body args m Q X := by
  rintro ⟨h, new_confl, old_ctype, old_cref, to_bin, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hw, hnd, hpre, hm, hQ⟩
  have hsame : Q () m := hQ s.core.arena s.core.arena_garbage s.core.num_irred
    s.core.num_redundant m hlen hw rfl hnd (fun _ _ => ⟨rfl, fun _ _ => rfl⟩) hm
  by_cases hct : old_ctype = 2#64
  · subst old_ctype
    by_cases hcr : old_cref = 0xFFFFFFFF#64
    · subst old_cref; fa_fast_steps; exact hsame
    · obtain ⟨hold_ref, hnew_ref, hnonact⟩ := hpre rfl hcr
      have hwf := hw.arena.refs_wf old_cref.toNat hold_ref
      have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
      have hcap31 := c.harena; unfold dimacsBound at hcap31
      have hcr_bd : old_cref.toNat + 2 < s.core.arena.length := by omega
      have hcr2 : (old_cref + 2#64).toNat = old_cref.toNat + 2 := by
        rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
      have hd_eq : fullArenaHdrCore s.core old_cref.toNat =
          s.core.arena[old_cref.toNat]'(by omega) := by
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      obtain ⟨arena1, h_arena1⟩ : ∃ xs, xs = s.core.arena.set old_cref.toNat
          (fullArenaHdrCore s.core old_cref.toNat ||| 0x00080000#32) := ⟨_, rfl⟩
      have har1_len : arena1.length = c.arena_cap := by rw [h_arena1]; simp [har_len]
      obtain ⟨ag1, h_ag1⟩ : ∃ x, x = s.core.arena_garbage + 3#64 +
          (arena1[old_cref.toNat + 2]'(by rw [har1_len]; omega)).setWidth 64 := ⟨_, rfl⟩
      let s1 : FullState :=
        { s with core := { s.core with arena := arena1, arena_garbage := ag1 } }
      have hmg1 := markGarb_preserves_fullWitnessCut hlen.core_ok hw (Nat.le_refl cut)
        hold_ref ag1 hnonact
      rw [← h_arena1] at hmg1
      obtain ⟨hw1, hrefs1, hprops1⟩ := hmg1
      have hgarb_c : fullArenaClauseGarbCore s1.core old_cref.toNat = true := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        dsimp only [s1]; rw [h_arena1, List.getElem?_set_self (by omega), Option.getD_some]
        simp [bv32_or_garb_garb]
      have hlen1 : s1.LengthsOk c :=
        ⟨{ hlen.core_ok with arena_len_arr := har1_len }, hlen.scratch_ok⟩
      have hnd1 : FullArenaVarsNodup s1 := fullArenaVarsNodup_markGarb hnd hrefs1 hgarb_c
        fun r hr hne => ⟨(hprops1 r hr).2.1, (hprops1 r hr).2.2 hne⟩
      have ha1_eq : s.core.arena.set old_cref.toNat
          (s.core.arena[old_cref.toNat]'(by omega) ||| 0x00080000#32) = arena1 := by
        rw [← hd_eq]; exact h_arena1.symm
      have hget_ag {xs : List (BitVec 32)} (hx : xs = arena1)
          (h1 : (old_cref + 2#64).toNat < xs.length) :
          s.core.arena_garbage + 3#64 + (xs[(old_cref + 2#64).toNat]'h1).setWidth 64 = ag1 := by
        subst hx; rw [h_ag1]; congr 1; congr 1; exact getElem_eq_of_idx hcr2
      have hcore1_eq {ml : Mem 64} {a' : List (BitVec 32)} {g' : BitVec 64}
          (ha : a' = arena1) (hg : g' = ag1)
          (hm' : (FullMem c { s with core := { s.core with arena := a', arena_garbage := g' } }
            ⋆ R) ml) :
          (FullMem c s1 ⋆ R) ml := by
        subst ha hg; exact hm'
      fa_fast_steps
      · exfalso; exact hcr ‹_›
      · exact hsame
      · exact hQ arena1 ag1 s.core.num_irred s.core.num_redundant _ hlen1 hw1 hrefs1 hnd1
          (fun r hr => ⟨(hprops1 r hr).2.1, fun _ hne => (hprops1 r hr).2.2 hne⟩)
          (hcore1_eq ha1_eq (hget_ag ha1_eq _) ‹_›)
      · have hnc_ref := hnew_ref (fun ht => by cases ht.symm.trans ‹to_bin = false›)
        have hnc_wf := hw.arena.refs_wf new_confl.toNat hnc_ref
        have hnc_bd : new_confl.toNat < arena1.length := by rw [har1_len]; omega
        have hs1_hm : (FullMem c s1 ⋆ R) _ := hcore1_eq ha1_eq (hget_ag ha1_eq _) ‹_›
        have har_nc : fullArenaHdrCore s1.core new_confl.toNat =
            arena1[new_confl.toNat]'hnc_bd := by
          unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hnc_bd, Option.getD_some]
        let arena2 := s1.core.arena.set new_confl.toNat
          (fullArenaHdrCore s1.core new_confl.toNat &&& 0xFFBFFFFF#32)
        have hnc_ref1 : new_confl.toNat ∈ fullArenaClauseRefsCore s1.core := by
          rw [hrefs1]; exact hnc_ref
        have hstep_red (ni2 nr2 : BitVec 64) (ml : Mem 64)
            (hm2 : (FullMem c { s1 with core :=
              { s1.core with arena := arena2, num_irred := ni2, num_redundant := nr2 } } ⋆ R) ml) :
            Q () ml := by
          obtain ⟨hw2, hrefs2, hprops2⟩ :=
            clearRed_preserves_fullWitnessCut hlen1.core_ok hw1 hnc_ref1 ni2 nr2
          have hlen2 : ({ s1 with core := { s1.core with
              arena := arena2, num_irred := ni2, num_redundant := nr2 } } :
              FullState).LengthsOk c :=
            ⟨{ hlen1.core_ok with arena_len_arr := by simp [arena2, s1, har1_len] },
              hlen.scratch_ok⟩
          have hnd2 : FullArenaVarsNodup { s1 with core :=
              { s1.core with arena := arena2, num_irred := ni2, num_redundant := nr2 } } :=
            fun r hr hng2 => by
              change r ∈ fullArenaClauseRefsCore _ at hr; rw [hrefs2] at hr
              obtain ⟨_, hgarb2, hlits2⟩ := hprops2 r hr
              change ((fullArenaClauseLitsCore _ r).map (· / 2)).Nodup
              rw [hlits2]; refine hnd1 r hr ?_
              change fullArenaClauseGarbCore s1.core r = false; rw [← hgarb2]; exact hng2
          exact hQ arena2 ag1 ni2 nr2 ml hlen2 hw2 (hrefs2.trans hrefs1) hnd2 (fun r hr => by
            have hr1 : r ∈ fullArenaClauseRefsCore s1.core := by rw [hrefs1]; exact hr
            refine ⟨(hprops2 r hr1).2.2.trans (hprops1 r hr).2.1, fun _ hne => ?_⟩
            exact (hprops2 r hr1).2.1.trans ((hprops1 r hr).2.2 hne)) hm2
        have hnot_ff : ~~~(4194304#32 : BitVec 32) = 0xFFBFFFFF#32 := by decide
        have hnc_z : (new_confl.setWidth 64).toNat = new_confl.toNat :=
          zext_toNat new_confl (by decide)
        let ar2_c0 := s1.core.arena.set (new_confl.setWidth 64).toNat
          (s1.core.arena[(new_confl.setWidth 64).toNat]'(by rw [hnc_z]; exact hnc_bd) &&&
            ~~~(4194304#32 : BitVec 32))
        have har2_eq : ar2_c0 = arena2 := by
          dsimp only [ar2_c0, arena2, s1]
          exact list_set_congr hnc_z
            (by rw [getElem_eq_of_idx (hj := hnc_bd) hnc_z, har_nc, hnot_ff])
        have hm_s1 : (FullMem c s1 ⋆ R) _ := hs1_hm
        fa_fast_steps
        · exact hstep_red (s.core.num_irred + 1#64) (s.core.num_redundant - 1#64) _
            (fullMem_of_eq (s1 := { s1 with core := { s1.core with
              num_irred := s.core.num_irred + 1#64,
              num_redundant := s.core.num_redundant - 1#64, arena := ar2_c0 } })
              ‹_› (by dsimp only [s1]; rw [har2_eq]) rfl)
        · exact hstep_red (s.core.num_irred + 1#64) s.core.num_redundant _
            (fullMem_of_eq (s1 := { s1 with core := { s1.core with
              num_irred := s.core.num_irred + 1#64, arena := ar2_c0 } })
              ‹_› (by dsimp only [s1]; rw [har2_eq]) rfl)
        · exact hQ arena1 ag1 s.core.num_irred s.core.num_redundant _ hlen1 hw1 hrefs1 hnd1
            (fun r hr => ⟨(hprops1 r hr).2.1, fun _ hne => (hprops1 r hr).2.2 hne⟩) hm_s1
      · exact hQ arena1 ag1 s.core.num_irred s.core.num_redundant _ hlen1 hw1 hrefs1 hnd1
          (fun r hr => ⟨(hprops1 r hr).2.1, fun _ hne => (hprops1 r hr).2.2 hne⟩)
          (hcore1_eq ha1_eq (hget_ag ha1_eq _) ‹_›)
  · fa_fast_steps
    · exact hsame
    all_goals (exfalso; exact hct ‹_›)

/-! ## 4. `full_otfs_bin` (`fullOtfsBinSpec`) -/

private theorem otfs_bin_oom_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {wv ws : List (BitVec 32)} {wl : Nat} {wu : BitVec 64} {wso : List (BitVec 32)}
    {m' : Mem 64} (hiu : idx_u < cut) (hnd : FullArenaVarsNodup s)
    (hlen_in : ({ s with
      core := { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu },
      scratch := { s.scratch with wsort := wso } } : FullState).LengthsOk c)
    (hw_in : FullWitnessCutInv c F0 F_cur cut
      { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu })
    (hm' : (FullMem c { s with
      core := { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu, oom := 1#64 },
      scratch := { s.scratch with wsort := wso } } ⋆ R) m')
    (hQ : ∀ (ok : Bool) arena' ag' nb' wvec' wstk' wlen' wu' ct' c0' c1' cref' oom' sc' m'',
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
      sc'.res_sz = s.scratch.res_sz → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ FullConflOk F_cur idx_u s') →
      (FullMem c s' ⋆ R) m'' → Q (ok, ()) m'') :
    Q (false, ()) m' :=
  hQ false s.core.arena s.core.arena_garbage s.core.num_binary wv ws wl wu
    s.core.confl_type s.core.confl_lit0 s.core.confl_lit1 s.core.confl_ref 1#64
    { s.scratch with wsort := wso } m' ⟨{ hlen_in.core_ok with }, hlen_in.scratch_ok⟩
    ((hw_in.with_oom 1#64).shrink_cut (Nat.le_of_lt hiu))
    (by unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
        exact hnd)
    rfl rfl rfl rfl rfl rfl (fun hc => by cases hc) hm'

private theorem otfs_bin_mark_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {wv4 ws4 : List (BitVec 32)} {wl2 : Nat} {wu4 : BitVec 64} {wso2 : List (BitVec 32)}
    {m' : Mem 64} (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s)
    {cref uip f0 f1 : BitVec 32} (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (_hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hf0_m : f0.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf1_m : f1.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf0_u : f0 ≠ uip) (hf1_u : f1 ≠ uip)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hf1_lt : f1.toNat < 2 * s.core.cur_vars)
    (hent_f : (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]))
    (har_len : s.core.arena.length = c.arena_cap) (_h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1)
    (hcref_bd : cref.toNat + 2 < s.core.arena.length)
    (hcr0_bd : (cref.setWidth 64).toNat < s.core.arena.length)
    (hcr2_bd4 : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length)
    (hlen4 : ({ s with
      core := { s.core with num_binary := s.core.num_binary + 1#64, wvec := wv4, wstk := ws4,
                            wlen := wl2, wusable := wu4 }
      scratch := { s.scratch with wsort := wso2 } } : FullState).LengthsOk c)
    (hw4 : FullWitnessCutInv c F0 F_cur cut
      { s.core with num_binary := s.core.num_binary + 1#64, wvec := wv4, wstk := ws4,
                    wlen := wl2, wusable := wu4 })
    (hm' : (FullMem c { s with
      core := { s.core with
        num_binary := s.core.num_binary + 1#64, wvec := wv4, wstk := ws4,
        wlen := wl2, wusable := wu4,
        arena := s.core.arena.set (cref.setWidth 64).toNat
          (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32),
        arena_garbage := s.core.arena_garbage + 3#64 +
          (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd4).setWidth 64,
        confl_type := 1#64, confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64,
        confl_ref := 0xFFFFFFFF#64 },
      scratch := { s.scratch with wsort := wso2, otfs_cnt := s.scratch.otfs_cnt + 1#64 } } ⋆ R) m')
    (hQ : ∀ (ok : Bool) arena' ag' nb' wvec' wstk' wlen' wu' ct' c0' c1' cref' oom' sc' m'',
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
      sc'.res_sz = s.scratch.res_sz → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ FullConflOk F_cur idx_u s') →
      (FullMem c s' ⋆ R) m'' → Q (ok, ()) m'') :
    Q (true, ()) m' := by
  let s4 : FullState :=
    { s with
      core := { s.core with num_binary := s.core.num_binary + 1#64, wvec := wv4, wstk := ws4,
                            wlen := wl2, wusable := wu4 }
      scratch := { s.scratch with wsort := wso2 } }
  have hna := otfs_nonactive_on_trail hw4 hlen4.core_ok hiu_cut hiu_te ht_u hr_u hlev_u hcref
  obtain ⟨arena5, h_arena5⟩ : ∃ xs, xs = s4.core.arena.set cref.toNat
      (fullArenaHdrCore s4.core cref.toNat ||| 0x00080000#32) := ⟨_, rfl⟩
  obtain ⟨ag5, h_ag5⟩ : ∃ x, x = s.core.arena_garbage + 3#64 +
      (s.core.arena[cref.toNat + 2]'(by omega)).setWidth 64 := ⟨_, rfl⟩
  have hd_c : fullArenaHdrCore s4.core cref.toNat = s.core.arena[cref.toNat]'(by omega) := by
    unfold fullArenaHdrCore; dsimp only [s4]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hmg5 := markGarb_preserves_fullWitnessCut hlen4.core_ok hw4 (Nat.le_of_lt hiu_cut)
    hcref ag5 fun idx hidx hc => hna idx hidx
      (hc.elim (fun h => Or.inl (Nat.lt_min.mpr ⟨Nat.lt_trans h hiu_cut, h⟩)) Or.inr)
  rw [← h_arena5] at hmg5
  obtain ⟨hw5_a, hrefs5, hprops5⟩ := hmg5
  have hgarb5 : fullArenaClauseGarbCore
      { s4.core with arena := arena5, arena_garbage := ag5 } cref.toNat = true := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    rw [h_arena5]; dsimp only [s4]; rw [List.getElem?_set_self (by omega), Option.getD_some]
    simp [bv32_or_garb_garb]
  let s5_pre : FullState :=
    { s4 with core := { s4.core with arena := arena5, arena_garbage := ag5 } }
  have hnd5_pre : FullArenaVarsNodup s5_pre := fullArenaVarsNodup_markGarb
    (by unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb
          fullArenaClauseLits; exact hnd)
    hrefs5 hgarb5 fun r hr hne => ⟨(hprops5 r hr).2.1, (hprops5 r hr).2.2 hne⟩
  have hw_fin : FullWitnessCutInv c F0 F_cur idx_u
      { s.core with
        arena := arena5, arena_garbage := ag5, num_binary := s.core.num_binary + 1#64,
        wvec := wv4, wstk := ws4, wlen := wl2, wusable := wu4, confl_type := 1#64,
        confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64, confl_ref := 0xFFFFFFFF#64 } :=
    hw5_a.with_confl 1#64 (f0.setWidth 64) (f1.setWidth 64) 0xFFFFFFFF#64
  let s_fin : FullState :=
    { s with
      core :=
        { s.core with
          arena := arena5, arena_garbage := ag5, num_binary := s.core.num_binary + 1#64,
          wvec := wv4, wstk := ws4, wlen := wl2, wusable := wu4, confl_type := 1#64,
          confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64, confl_ref := 0xFFFFFFFF#64 },
      scratch := { s.scratch with wsort := wso2, otfs_cnt := s.scratch.otfs_cnt + 1#64 } }
  have harena := c.harena; unfold dimacsBound at harena
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff (by omega)
  have hcref_lg : (cref &&& 0x80000000#32) = 0#32 := (bv32_lit_lo31_props (by omega)).2.2
  have hri := hw.reason_inv idx_u hiu_te (Or.inl hiu_cut)
  dsimp only at hri; rw [ht_u, hr_u] at hri
  have hri := hri hcref_ne
  rw [ite_eq_right (fun h => absurd hcref_lg h)] at hri
  have hconfl_ok : FullConflOk F_cur idx_u s_fin := by
    simp only [FullConflOk, s_fin, ↓reduceIte]
    have hto0 : (f0.setWidth 64).toNat = f0.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hto1 : (f1.setWidth 64).toNat = f1.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    rw [hto0, hto1]
    have hm_ex (f : BitVec 32) (hfm : f.toNat ∈ fullArenaClauseLits s cref.toNat)
        (hfu : f ≠ uip) (hflt : f.toNat < 2 * s.core.cur_vars) :
        s.core.vals[f.toNat]?.getD 0#8 = 0xFF#8 ∧
        ((s.core.lvl[f.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
          ∃ m < idx_u, (s.core.trl[m]?.getD 0#32).toNat = f.toNat ^^^ 1) := by
      have hneq : f.toNat ≠ uip.toNat := fun he => hfu (BitVec.eq_of_toNat_eq he)
      obtain ⟨m0, hm0, hm0_eq, _⟩ := (hri.2.2 f.toNat hfm).resolve_left hneq
      exact ⟨(hw.vals_false_iff f.toNat hflt).mpr ⟨m0, by omega, hm0_eq⟩,
        fun _ => ⟨m0, hm0, hm0_eq⟩⟩
    have p0 := hm_ex f0 hf0_m hf0_u hf0_lt
    have p1 := hm_ex f1 hf1_m hf1_u hf1_lt
    exact ⟨hf0_lt, hf1_lt, p0.1, p1.1, p0.2, p1.2, hent_f⟩
  have hlen_fin : s_fin.LengthsOk c :=
    ⟨{ hlen4.core_ok with arena_len_arr :=
        (by dsimp [s_fin]; rw [h_arena5]; dsimp [s4]; simp [har_len]) },
      { hlen4.scratch_ok with }⟩
  have hnd_fin : FullArenaVarsNodup s_fin := by
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    exact hnd5_pre
  have hcr2_idx : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
    rw [BitVec.toNat_add, zext_toNat cref (by decide)]; simp only [BitVec.reduceToNat]; omega
  have har5_eq : s.core.arena.set (cref.setWidth 64).toNat
      (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32) = arena5 := by
    rw [h_arena5]; dsimp only [s4]
    exact list_set_congr (zext_toNat cref (by decide))
      (by rw [hd_c, getElem_eq_of_idx (zext_toNat cref (by decide))])
  have hag5_eq : s.core.arena_garbage + 3#64 +
      (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd4).setWidth 64 = ag5 := by
    rw [h_ag5]; congr 1; congr 1; exact getElem_eq_of_idx hcr2_idx
  exact hQ true arena5 ag5 (s.core.num_binary + 1#64) wv4 ws4 wl2 wu4
    1#64 (f0.setWidth 64) (f1.setWidth 64) 0xFFFFFFFF#64 s.core.oom
    s_fin.scratch m' hlen_fin hw_fin hnd_fin rfl rfl rfl rfl rfl hrefs5
    (fun _ => ⟨rfl, hconfl_ok⟩) (fullMem_of_eq hm' (by rw [har5_eq, hag5_eq]) rfl)

theorem full_otfs_bin_wp_weak (Γ : Env)
    (hUnw : ∀ args m Q X, fullUnwatchLargeWeakSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullOtfsBinSpec args m Q X →
      Func.wp Γ full_otfs_bin_body args m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hdm, hw, hnd, hcref, hng, huip_lt,
      hiu_cut, hiu_te, ht_u, hr_u, hlev_u, hent, hm, hQ⟩
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have hcv_le := hlen.core_ok.cur_vars_le; have hmaxv := c.hmaxv; have harena := c.harena
  unfold dimacsBound at hmaxv harena
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by omega
  obtain ⟨old_sz, h_old_sz⟩ : ∃ n, n = fullArenaClauseSizeCore s.core cref.toNat := ⟨_, rfl⟩
  have hsz_lt_ar : cref.toNat + 3 + old_sz ≤ s.core.arena.length := by rw [h_old_sz]; omega
  have hcref_bd : cref.toNat + 2 < s.core.arena.length := by omega
  have hsz_get : s.core.arena[cref.toNat + 2]'(by omega) = BitVec.ofNat 32 old_sz := by
    apply BitVec.eq_of_toNat_eq
    have hlt32 : old_sz < 2 ^ 32 := by
      rw [h_old_sz]; exact (s.core.arena[cref.toNat + 2]?.getD 0#32).isLt
    rw [bv32_ofNat_toNat hlt32, h_old_sz]
    unfold fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hlits_info : ∀ j (hj : j < old_sz),
      let ot := s.core.arena[cref.toNat + 3 + j]'(by omega)
      ot.toNat ∈ fullArenaClauseLits s cref.toNat ∧ ot.toNat < 2 * s.core.cur_vars ∧
      ot ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hmem : (s.core.arena[cref.toNat + 3 + j]'(by omega)).toNat ∈
        fullArenaClauseLitsCore s.core cref.toNat :=
      (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨j, h_old_sz ▸ hj, rfl⟩
    have hlt := hw.arena.lits_lt cref.toNat hcref hng _ hmem
    exact ⟨hmem, hlt, bv32_lit_neq_ff (by omega)⟩
  have hnodup_j : ∀ j1 j2 (h1 : j1 < old_sz) (h2 : j2 < old_sz), j1 ≠ j2 →
      s.core.arena[cref.toNat + 3 + j1]'(by omega) ≠
      s.core.arena[cref.toNat + 3 + j2]'(by omega) :=
    fun j1 j2 h1 h2 hne heq => by
      have hndc := hnd cref.toNat hcref hng
      let raw := (s.core.arena.drop (cref.toNat + 3)).take old_sz
      have hraw_len : raw.length = old_sz := by
        simp [raw, List.length_take, List.length_drop]; omega
      have hnd_raw : (raw.map fun l : BitVec 32 => l.toNat / 2).Nodup := by
        simpa [fullArenaClauseLits, fullArenaClauseLitsCore, h_old_sz, raw, List.map_map,
          Function.comp_def] using hndc
      have hraw_eq : ∀ j (hj : j < old_sz),
          raw[j]'(hraw_len ▸ hj) = s.core.arena[cref.toNat + 3 + j]'(by omega) :=
        fun j hj => by simp [raw, List.getElem_take, List.getElem_drop]
      have hij := nodup_map_getElem_inj (fun l : BitVec 32 => l.toNat / 2)
        (hraw_len ▸ h1) (hraw_len ▸ h2) hnd_raw (by rw [hraw_eq j1 h1, hraw_eq j2 h2, heq])
      exact hne hij
  have hret_same : Q (false, ()) m :=
    hQ false s.core.arena s.core.arena_garbage s.core.num_binary s.core.wvec s.core.wstk
      s.core.wlen s.core.wusable s.core.confl_type s.core.confl_lit0 s.core.confl_lit1
      s.core.confl_ref s.core.oom s.scratch m hlen (hw.shrink_cut (Nat.le_of_lt hiu_cut)) hnd
      rfl rfl rfl rfl rfl rfl (fun hc => by cases hc) hm
  fa_fast_steps_nogrp
  refine wp_join_group (ts := [i32, i32, i32]) (fun p ml =>
      let f0 := p.1; let f1 := p.2.1
      ml = m ∧ ((f0 = 0xFFFFFFFF#32 ∨ f1 = 0xFFFFFFFF#32) ∨
        (f0.toNat ∈ fullArenaClauseLits s cref.toNat ∧
         f1.toNat ∈ fullArenaClauseLits s cref.toNat ∧
         f0 ≠ uip ∧ f1 ≠ uip ∧ f0 ≠ f1 ∧
         0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat ∧
         0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat))) ?_ ?_
  · rintro _ ⟨f0, f1, _iv, ⟨⟩⟩ ml ⟨rfl, hpost⟩
    rcases hpost with hf_eq | ⟨hf0_m, hf1_m, hf0_u, hf1_u, hf_ne, hl0_pos, hl1_pos⟩
    · fa_fast_steps
      · exact hret_same
      · exact hret_same
      · exfalso; rcases hf_eq with h | h <;> exact absurd h ‹_›
    · have hf0_lt := hw.arena.lits_lt cref.toNat hcref hng _ hf0_m
      have hf1_lt := hw.arena.lits_lt cref.toNat hcref hng _ hf1_m
      have hf0_31 : f0.toNat < 2 ^ 31 - 1 := Nat.lt_trans hf0_lt h2cv_lt
      have hf1_31 : f1.toNat < 2 ^ 31 - 1 := Nat.lt_trans hf1_lt h2cv_lt
      have hf0_ff : f0 ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hf0_31
      have hf1_ff : f1 ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hf1_31
      have hb0_p := bin_rsn_mask_props (l := f1) hf1_31
      have hb1_p := bin_rsn_mask_props (l := f0) hf0_31
      let b0 := (f1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
      let b1 := (f0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
      have hent_f := hent f0 f1 hf0_m hf1_m hf0_u hf1_u hf_ne hl0_pos hl1_pos
      have hent_sym : (cnfOfClauses F_cur).EntailsClause (cnfClause [f1.toNat, f0.toNat]) :=
        entails_of_mem_or_false hent_f fun l hl => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
          exact Or.inl (by rcases hl with rfl | rfl <;> simp)
      have hlay0 : WatchStackLayout s.core := by
        have h := hw.watches; unfold ModeWatchesInv at h; simp only [hdm, ↓reduceIte] at h
        exact h.layout
      fa_fast_steps
      · exfalso; exact hf0_ff ‹_›
      · exfalso; exact hf1_ff ‹_›
      · c0_call hPush
        · refine ⟨c, s, R, rfl, hlen, hlay0,
            (fun _ => hb0_p.1), (fun hk => by cases hk), hm, fun ok1 wv1 ws1 wl1 wu1 wso1 m1
              hlen1 hlay1 hother1 hok1t hok1f hm1 => ?_⟩
          clear hm
          let s1 : FullState :=
            { s with
              core := { s.core with wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 }
              scratch := { s.scratch with wsort := wso1 } }
          have hw_k1 : ModeWatchesInv F_cur s1.core := by
            by_cases hok1 : ok1 = true
            · subst hok1
              obtain ⟨_, _, hsz1, hsame1, hw01, _⟩ := hok1t rfl
              exact fa_watchPush_bin_preserves hdm hw.watches (lit := f0.toNat) (w0 := b0)
                (nb' := s.core.num_binary) (oom' := s.core.oom) hf0_lt hlay1 hother1 hsz1 hsame1
                hw01 hb0_p.2.1 hb0_p.1 (by rw [hb0_p.2.2]; exact hf1_lt)
                (by rw [hb0_p.2.2]; exact hent_f)
            · have hokf : ok1 = false := Bool.eq_false_iff.mpr hok1
              obtain ⟨hsame_f, _⟩ := hok1f hokf
              exact fa_watchPush_fail_preserves hdm hw.watches hlay1 fun l hl =>
                if hle : l = f0.toNat then by subst l; exact hsame_f hf0_lt
                else hother1 l hl hle
          have hw1 : FullWitnessCutInv c F0 F_cur cut s1.core := hw.with_watches hw_k1
          by_cases hok1 : ok1 = true
          · subst hok1; clear hok1t hok1f
            fa_fast_steps_nogrp
            c0_call hPush
            · refine ⟨c, s1, R, rfl, hlen1, hlay1,
                (fun _ => hb1_p.1), (fun hk => by cases hk), hm1,
                fun ok2 wv2 ws2 wl2 wu2 wso2 m2 hlen2 hlay2 hother2 hok2t hok2f hm2 => ?_⟩
              clear hm1
              let s2 : FullState :=
                { s with
                  core := { s.core with wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2 },
                  scratch := { s.scratch with wsort := wso2 } }
              have hm2' : (FullMem c s2 ⋆ R) m2 :=
                fullMem_of_eq hm2 (by dsimp only [s2, s1]) (by dsimp only [s2, s1])
              clear hm2
              have hlen2' : s2.LengthsOk c := ⟨{ hlen2.core_ok with }, { hlen2.scratch_ok with }⟩
              have hw_k2 : ModeWatchesInv F_cur s2.core := by
                by_cases hok2 : ok2 = true
                · subst hok2
                  obtain ⟨_, _, hsz2, hsame2, hw02, _⟩ := hok2t rfl
                  exact fa_watchPush_bin_preserves (k := s1.core) hdm hw1.watches
                    (lit := f1.toNat) (w0 := b1) (nb' := s.core.num_binary) (oom' := s.core.oom)
                    hf1_lt hlay2 hother2 hsz2 hsame2 hw02 hb1_p.2.1 hb1_p.1
                    (by rw [hb1_p.2.2]; exact hf0_lt) (by rw [hb1_p.2.2]; exact hent_sym)
                · have hokf : ok2 = false := Bool.eq_false_iff.mpr hok2
                  obtain ⟨hsame_f, _⟩ := hok2f hokf
                  exact fa_watchPush_fail_preserves (k := s1.core) hdm hw1.watches hlay2
                    fun l hl => if hle : l = f1.toNat then by subst l; exact hsame_f hf1_lt
                      else hother2 l hl hle
              have hw2 : FullWitnessCutInv c F0 F_cur cut s2.core := hw1.with_watches hw_k2
              by_cases hok2 : ok2 = true
              · subst hok2
                have hcr3_bd : (cref.setWidth 64 + 3#64).toNat < s2.core.arena.length := by
                  rw [BitVec.toNat_add, zext_toNat cref (by decide)]
                  simp only [BitVec.reduceToNat]; dsimp [s2]; omega
                fa_fast_steps_nogrp
                have hnb_l : { s2 with core :=
                    { s2.core with num_binary := s2.core.num_binary + 1#64 } }.LengthsOk c :=
                  ⟨{ hlen2'.core_ok with }, hlen2'.scratch_ok⟩
                c0_call hUnw
                · refine ⟨c, _, R, rfl, hnb_l, { hlay2 with }, ‹_›,
                    fun wv3 ws3 wu3 m3 hlen3 hlay3 hmw3 hm3 => ?_⟩
                  let s3 : FullState :=
                    { s with
                      core :=
                        { s.core with
                          num_binary := s.core.num_binary + 1#64, wvec := wv3, wstk := ws3,
                          wlen := wl2, wusable := wu3 },
                      scratch := { s.scratch with wsort := wso2 } }
                  have hm3' : (FullMem c s3 ⋆ R) m3 :=
                    fullMem_of_eq hm3 (by dsimp only [s3, s2]) (by dsimp only [s3, s2])
                  clear hm3
                  have hw3 : FullWitnessCutInv c F0 F_cur cut s3.core :=
                    { hw2 with
                      arena := { hw2.arena with len_ok := hw2.arena.len_ok }
                      watches := hmw3 F_cur
                        (hw2.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr) }
                  have hcr4_bd : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length := by
                    rw [BitVec.toNat_add, zext_toNat cref (by decide)]
                    simp only [BitVec.reduceToNat]; dsimp [s3]; omega
                  fa_fast_steps_nogrp
                  c0_call hUnw
                  · refine ⟨c, s3, R, rfl, ⟨{ hlen3.core_ok with }, { hlen3.scratch_ok with }⟩,
                      hlay3, hm3', fun wv4 ws4 wu4 m4 hlen4 _ hmw4 hm4 => ?_⟩
                    clear hm3'
                    let s4 : FullState :=
                      { s with
                        core :=
                          { s.core with
                            num_binary := s.core.num_binary + 1#64, wvec := wv4, wstk := ws4,
                            wlen := wl2, wusable := wu4 },
                        scratch := { s.scratch with wsort := wso2 } }
                    have hm4' : (FullMem c s4 ⋆ R) m4 :=
                      fullMem_of_eq hm4 (by dsimp only [s4, s3]) (by dsimp only [s4, s3])
                    clear hm4
                    have hw4 : FullWitnessCutInv c F0 F_cur cut s4.core :=
                      hw3.with_watches (hmw4 F_cur hw3.watches)
                    have hcr0_bd : (cref.setWidth 64).toNat < s4.core.arena.length := by
                      rw [zext_toNat cref (by decide)]; dsimp only [s4]; omega
                    have hcr2_bd4 : (cref.setWidth 64 + 2#64).toNat < s4.core.arena.length := by
                      rw [BitVec.toNat_add, zext_toNat cref (by decide)]
                      simp only [BitVec.reduceToNat]; dsimp only [s4]; omega
                    fa_fast_steps
                    exact otfs_bin_mark_fin hw hnd hcref hng hiu_cut hiu_te ht_u hr_u hlev_u
                      hf0_m hf1_m hf0_u hf1_u hf0_lt hf1_lt hent_f har_len h2cv_lt hcref_bd
                      hcr0_bd hcr2_bd4 ⟨{ hlen4.core_ok with }, { hlen4.scratch_ok with }⟩ hw4
                      ‹_› hQ
              · have hok2f : ok2 = false := Bool.eq_false_iff.mpr hok2
                subst hok2f
                fa_fast_steps
                have hm_oom : (FullMem c { s with
                    core := { s.core with wvec := wv2, wstk := ws2, wlen := wl2,
                                          wusable := wu2, oom := 1#64 },
                    scratch := { s.scratch with wsort := wso2 } } ⋆ R) _ :=
                  fullMem_of_eq hm (by dsimp only [s2]; try rfl) (by dsimp only [s2]; try rfl)
                exact otfs_bin_oom_exit hiu_cut hnd hlen2' hw2 hm_oom hQ
          · have hok1f : ok1 = false := Bool.eq_false_iff.mpr hok1
            subst hok1f
            fa_fast_steps
            have hm_oom : (FullMem c { s with
                core := { s.core with wvec := wv1, wstk := ws1, wlen := wl1,
                                      wusable := wu1, oom := 1#64 },
                scratch := { s.scratch with wsort := wso1 } } ⋆ R) _ :=
              fullMem_of_eq hm (by dsimp only [s1]; try rfl) (by dsimp only [s1]; try rfl)
            exact otfs_bin_oom_exit hiu_cut hnd hlen1 hw1 hm_oom hQ
  · intro J hJ; fa_fast_steps_nogrp
    refine wp_loop_group (fun r (f0, iv, ()) ml => ∃ i : Nat,
      ml = m ∧ r = old_sz - i ∧ i ≤ old_sz ∧ iv = BitVec.ofNat 32 i ∧
      (f0 = 0xFFFFFFFF#32 ∨ ∃ j < i,
        f0 = s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ∧
        f0 ≠ uip ∧ 0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat)) ?_ ?_
    · rintro L r ⟨f0, iv, ⟨⟩⟩ ml ih ⟨i, rfl, rfl, hile, rfl, hf0⟩
      fa_fast_steps_nogrp
      · have hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
          rw [BitVec.toNat_add, zext_toNat cref (by decide)]; simp; omega
        have hcr2_bd : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by
          rw [hcr2_z]; omega
        have hilt : i < old_sz := by
          have hb : (BitVec.ofNat 32 i).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
          rw [bv32_ofNat_toNat (by omega)] at hb
          rwa [getElem_eq_of_idx (hj := by omega) hcr2_z, hsz_get,
            bv32_ofNat_toNat (by omega)] at hb
        obtain ⟨hot_mem, hot_lt, hot_ff⟩ := hlits_info i hilt
        let ot := s.core.arena[cref.toNat + 3 + i]'(by omega)
        have hot_get : ot = s.core.arena[cref.toNat + 3 + i]?.getD 0#32 := by
          dsimp only [ot]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hcr_i_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat =
            cref.toNat + 3 + i := by
          rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
            zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
          simp only [BitVec.reduceToNat]; omega
        have hcr_i_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat <
            s.core.arena.length := by rw [hcr_i_z]; omega
        have hot_idx_eq : s.core.arena[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 i).setWidth 64).toNat]'hcr_i_bd = ot :=
          getElem_eq_of_idx hcr_i_z
        have hot_lvl_lt : (s.core.arena[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 i).setWidth 64).toNat]'hcr_i_bd).toNat / 2 < s.core.cur_vars := by
          rw [hot_idx_eq]; exact Nat.div_lt_of_lt_mul hot_lt
        have hc_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i % 2 ^ 32) % 2 ^ 64 =
            cref.toNat + 3 + i := by
          simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
        have hot_c0_eq : s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
            i % 2 ^ 32) % 2 ^ 64]'(by rw [hc_idx]; omega) = ot :=
          getElem_eq_of_idx hc_idx
        have hot_lvl_c0 : (s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
            i % 2 ^ 32) % 2 ^ 64]'(by rw [hc_idx]; omega)).toNat / 2 < s.core.cur_vars := by
          rw [hot_c0_eq]; exact Nat.div_lt_of_lt_mul hot_lt
        fa_fast_steps_nogrp
        refine wp_join_group (ts := [i32, i32]) (fun p ml_post =>
            let f0' := p.1
            ml_post = ml ∧
            (f0' = 0xFFFFFFFF#32 ∨ ∃ j < i + 1,
              f0' = s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ∧
              f0' ≠ uip ∧ 0 < (s.core.lvl[f0'.toNat / 2]?.getD 0#32).toNat)) ?_ ?_
        · rintro _ ⟨f0', _f1, ⟨⟩⟩ ml_post ⟨rfl, hf0'⟩
          fa_fast_steps
          have hi1 : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
            apply BitVec.eq_of_toNat_eq; bv_omega
          rw [hi1]
          exact ih (old_sz - (i + 1)) _ ml_post (by omega) ⟨i + 1, rfl, rfl, by omega, rfl, hf0'⟩
        · intro J2 hJ2; fa_fast_steps
          · have hot_v_lvl : ot.toNat / 2 < s.core.lvl.length := by
              rw [hlvl_len]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hot_lt) hcv_le
            have hpos_ot : 0 < (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem hot_v_lvl, Option.getD_some]
              exact Nat.lt_of_lt_of_eq ‹BitVec.toNat 0 < _› (congrArg BitVec.toNat
                (getElem_eq_of_idx (congrArg (fun x : BitVec 32 => x.toNat / 2)
                  (getElem_eq_of_idx hc_idx))))
            have hot_ne_uip : ot ≠ uip := fun he =>
              ‹¬ _ = uip› ((getElem_eq_of_idx hc_idx).trans he)
            have h_ot_g (pf) : s.core.arena[(cref.setWidth 64 + 3 +
                (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = ot := getElem_eq_of_idx hcr_i_z
            rw [h_ot_g]
            exact hJ2 (ot, 0xFFFFFFFF#32, ()) ml
              ⟨rfl, Or.inr ⟨i, Nat.lt_succ_self i, hot_get, hot_ne_uip, hpos_ot⟩⟩
          · have hot_v_lvl : ot.toNat / 2 < s.core.lvl.length := by
              rw [hlvl_len]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hot_lt) hcv_le
            have hpos_ot : 0 < (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem hot_v_lvl, Option.getD_some]
              exact Nat.lt_of_lt_of_eq ‹BitVec.toNat 0 < _› (congrArg BitVec.toNat
                (getElem_eq_of_idx (congrArg (fun x : BitVec 32 => x.toNat / 2)
                  (getElem_eq_of_idx hc_idx))))
            have hot_ne_uip : ot ≠ uip := fun he =>
              ‹¬ _ = uip› ((getElem_eq_of_idx hc_idx).trans he)
            have h_ot_g (pf) : s.core.arena[(cref.setWidth 64 + 3 +
                (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = ot := getElem_eq_of_idx hcr_i_z
            rcases hf0 with rfl | ⟨j, hj, rfl, hju, hjl⟩
            · exfalso; exact ‹¬ (0xFFFFFFFF#32 = 0xFFFFFFFF#32)› rfl
            · have hj_get : s.core.arena[cref.toNat + 3 + j]?.getD 0#32 =
                  s.core.arena[cref.toNat + 3 + j]'(by omega) := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hf_ne : s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ ot := by
                rw [hj_get]; exact hnodup_j j i (by omega) hilt (by omega)
              have hj_info := hlits_info j (by omega)
              rw [← hj_get] at hj_info
              rw [h_ot_g]
              exact hJ (s.core.arena[cref.toNat + 3 + j]?.getD 0#32, ot, BitVec.ofNat 32 i, ()) ml
                ⟨rfl, Or.inr ⟨hj_info.1, hot_mem, hju, hot_ne_uip, hf_ne, hjl, hpos_ot⟩⟩
          · exact hJ2 _ _ ⟨rfl, hf0.imp_right fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
          · exact hJ2 _ _ ⟨rfl, hf0.imp_right fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
      · fa_fast_steps; exact hJ _ _ ⟨rfl, Or.inl (Or.inr rfl)⟩
    · intro L hL; fa_fast_steps
      exact hL old_sz (0xFFFFFFFF#32, 0#32, ()) m
        ⟨0, rfl, rfl, Nat.zero_le _, rfl, Or.inl rfl⟩

theorem full_otfs_bin_wp (Γ : Env)
    (hUnw : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullOtfsBinSpec args m Q X →
      Func.wp Γ full_otfs_bin_body args m Q X :=
  full_otfs_bin_wp_weak Γ (fun a m Q X ⟨c, s, R, hh, hl, hly, hm, hQ⟩ =>
    hUnw a m Q X ⟨c, s, R, hh, hl, hly, hm, fun wv ws wu m' hl' hly' hmw _ hm' =>
      hQ wv ws wu m' hl' hly' hmw hm'⟩) hPush

end LeanQbe.T.Examples.Kissat.Full

