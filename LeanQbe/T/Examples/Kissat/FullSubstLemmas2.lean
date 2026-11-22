module

public import LeanQbe.T.Examples.Kissat.FullSubstLemmas1

/-!
# Kissat `D-Full` BIG SCC Substitution — Part 2 (`Stage 4`, UNSAT-Only)

Defines:
1. Watch-slice binary scanning & compaction helpers (`WatchSliceOk.step_bin`, `step_nonbin`,
   `append_bin`, `append_large`, `bin_lt_of_flag`, `rewriteBins_slice_preserves_fullSparse`).
2. `full_subst_rewrite_bins_wp` (`Full3.lean` #27).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullSubstSpecs FullSubstTactics
open scoped FullArenaTactics FullSubstTactics

/-! ## 1. Watch-Slice Scanning, Compaction, and Sparse Preservation Helpers -/

namespace FullSubstHelpers

theorem wsStepNonbin {F_cur : List (List Nat)} {k : FullCoreState} {nl p rem : Nat}
    (h : WatchSliceOk F_cur k nl p rem) (hpos : 0 < rem)
    (hflag : (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) = 0#32) :
    ∃ w0 cref,
      2 ≤ rem ∧ k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cref ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cref.toNat < 0x80000000 ∧
      cref.toNat ∈ fullArenaClauseRefsCore k ∧
      WatchSliceOk F_cur k nl (p + 2) (rem - 2) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf =>
    rw [hp, Option.getD_some] at hflag; exact absurd hflag hf
  | @large _ r w0 cref hp hp1 hf hlt href hrest =>
    exact ⟨w0, cref, by omega, hp, hp1, hf, hlt, href, by simpa using hrest⟩

theorem wsStepBin {F_cur : List (List Nat)} {k : FullCoreState} {nl p rem : Nat}
    (h : WatchSliceOk F_cur k nl p rem) (hpos : 0 < rem)
    (hflag : (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    ∃ w0,
      k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [nl, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k nl (p + 1) (rem - 1) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf hne hlt hent hrest =>
    exact ⟨w0, hp, hf, hne, hlt, hent, by simpa using hrest⟩
  | @large _ _ w0 _ hp _ hf =>
    rw [hp, Option.getD_some] at hflag; exact absurd hf hflag

theorem wsRelocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem wsAppendBin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @large p rem w cref hp hp1 hf hl href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ href) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

theorem wsAppendLarge {F_cur : List (List Nat)} {k k' : FullCoreState}
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
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem wsBinLtOfFlag {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceOk F_cur k lit p rem) :
    ∀ c, p ≤ c → c < p + rem →
      (k.wstk[c]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 →
      (k.wstk[c]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars := by
  induction h with
  | empty => intro c hc1 hc2; omega
  | @bin p r w0 hp _ _ hlt _ _ ih =>
    intro c hc1 hc2 hf
    by_cases hcp : c = p
    · subst hcp; rw [hp, Option.getD_some]; exact hlt
    · exact ih c (by omega) (by omega) hf
  | @large p r w0 cr hp hp1 hfw hlt _ _ ih =>
    intro c hc1 hc2 hf
    by_cases hcp : c = p
    · subst hcp; rw [hp, Option.getD_some] at hf; exact absurd hfw hf
    · by_cases hcp1 : c = p + 1
      · subst hcp1; rw [hp1, Option.getD_some] at hf
        exact absurd (bv32_bit31_eq_zero_of_lt hlt) hf
      · exact ih c (by omega) (by omega) hf

theorem rewriteBins_slice_preserves_fullSparse {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) {l q : Nat}
    (hl : l < 2 * s.core.cur_vars)
    (hq_lo : fullWatchOff s l ≤ q) (hq_hi : q ≤ fullWatchOff s l + fullWatchSize s l)
    {wstk' : List (BitVec 32)} {lm' : List (BitVec 8)} {wu' nb' : BitVec 64}
    {ws1' ws2' : List (BitVec 32)}
    (hwstk_len : wstk'.length = c.wcap)
    (hlm_len : lm'.length = 2 * c.max_vars)
    (hws1_len : ws1'.length = 2 * c.max_vars)
    (hws2_len : ws2'.length = 2 * c.max_vars)
    (hlm_zero : ∀ x < 2 * c.max_vars, lm'[x]?.getD 0#8 = 0#8)
    (hwstk_out : ∀ idx, (idx < fullWatchOff s l ∨ fullWatchOff s l + fullWatchSize s l ≤ idx) →
      wstk'[idx]? = s.core.wstk[idx]?)
    (hwstk_slice : WatchSliceOk F_cur
      { s.core with wstk := wstk' } l (fullWatchOff s l) (q - fullWatchOff s l)) :
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            lit_mark := lm'
            wvec := s.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - fullWatchOff s l))
            wstk := wstk', wusable := wu', num_binary := nb' }
        scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2' } }
    FullSparseInvW c F0 F_cur s' := by
  intro s'
  dsimp only [fullWatchOff, fullWatchSize] at *
  have hcl := hsp.1.core_ok; have hsl := hsp.1.scratch_ok
  have hw := c.hwcap; have hmx := c.hmaxv; unfold dimacsBound at hw hmx
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len; have hwle := hcl.wlen_le
  have hwat : WatchesInv F_cur s.core := by
    have hm := hsp.2.1.watches; unfold ModeWatchesInv at hm
    simp only [hsp.2.2.2.2.2, ↓reduceIte] at hm; exact hm
  have hbound_l := hwat.layout.bounds l hl
  have hsz_lt32 : fullWatchSizeCore s.core l < 2 ^ 32 := (s.core.wvec[2 * l + 1]?.getD 0#32).isLt
  have hq_lt32 : q - fullWatchOffCore s.core l < 2 ^ 32 := by omega
  have hsz_l' : fullWatchSizeCore s'.core l = q - fullWatchOffCore s.core l := by
    unfold fullWatchSizeCore; dsimp only [s']
    rw [List.getElem?_set_self (by omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq_lt32]
  have hoff_l' : fullWatchOffCore s'.core l = fullWatchOffCore s.core l := by
    unfold fullWatchOffCore; dsimp only [s']
    rw [List.getElem?_set_ne (by omega)]
  have hother_w : ∀ l' ≠ l,
      fullWatchOffCore s'.core l' = fullWatchOffCore s.core l' ∧
      fullWatchSizeCore s'.core l' = fullWatchSizeCore s.core l' := by
    intro l' hne
    unfold fullWatchOffCore fullWatchSizeCore; dsimp only [s']
    exact ⟨by rw [List.getElem?_set_ne (by omega)],
           by rw [List.getElem?_set_ne (by omega)]⟩
  have hcv' : s'.core.cur_vars = s.core.cur_vars := rfl
  have hwle' : s'.core.wlen = s.core.wlen := rfl
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hwat' : ModeWatchesInv F_cur s'.core := by
    unfold ModeWatchesInv
    simp only [show s'.core.dense_mode = 0#64 from hsp.2.2.2.2.2, ↓reduceIte]
    refine WatchesInv.of_slices (fun l' hl' => ?_) (fun l' hl' hp => ?_)
      (fun l1 l2 h1 h2 hne hp1 hp2 => ?_) (fun l' hl' => ?_)
    · rw [hcv'] at hl'; rw [hwle']
      by_cases hll : l' = l
      · rw [hll, hoff_l', hsz_l']; omega
      · obtain ⟨ho, hs⟩ := hother_w l' hll; rw [ho, hs]; exact hwat.layout.bounds l' hl'
    · rw [hcv'] at hl'
      by_cases hll : l' = l
      · rw [hll, hoff_l']; rw [hll, hsz_l'] at hp
        exact hwat.layout.pos_off l hl (by omega)
      · obtain ⟨ho, hs⟩ := hother_w l' hll; rw [ho]; rw [hs] at hp
        exact hwat.layout.pos_off l' hl' hp
    · rw [hcv'] at h1 h2
      have hle1 : fullWatchOffCore s'.core l1 = fullWatchOffCore s.core l1 ∧
          fullWatchSizeCore s'.core l1 ≤ fullWatchSizeCore s.core l1 ∧
          0 < fullWatchSizeCore s.core l1 := by
        by_cases h1l : l1 = l
        · rw [h1l, hoff_l', hsz_l']; rw [h1l, hsz_l'] at hp1
          exact ⟨rfl, by omega, by omega⟩
        · obtain ⟨ho, hs⟩ := hother_w l1 h1l; rw [ho, hs]
          exact ⟨rfl, by omega, by omega⟩
      have hle2 : fullWatchOffCore s'.core l2 = fullWatchOffCore s.core l2 ∧
          fullWatchSizeCore s'.core l2 ≤ fullWatchSizeCore s.core l2 ∧
          0 < fullWatchSizeCore s.core l2 := by
        by_cases h2l : l2 = l
        · rw [h2l, hoff_l', hsz_l']; rw [h2l, hsz_l'] at hp2
          exact ⟨rfl, by omega, by omega⟩
        · obtain ⟨ho, hs⟩ := hother_w l2 h2l; rw [ho, hs]
          exact ⟨rfl, by omega, by omega⟩
      have hd := hwat.layout.disjoint l1 l2 h1 h2 hne hle1.2.2 hle2.2.2
      omega
    · rw [hcv'] at hl'
      by_cases hll : l' = l
      · rw [hll, hoff_l', hsz_l']
        exact wsRelocate (k := { s.core with wstk := wstk' }) (k' := s'.core)
          hrefl (Nat.le_refl _) (fun _ hr => hr) (fun _ _ => rfl) hwstk_slice
      · obtain ⟨ho, hs⟩ := hother_w l' hll; rw [ho, hs]
        by_cases hsz0 : fullWatchSizeCore s.core l' = 0
        · rw [hsz0]; exact .empty
        · by_cases hszl0 : fullWatchSizeCore s.core l = 0
          · exact (hwat.slices l' hl').mono (k := s.core) (k' := s'.core) hrefl (Nat.le_refl _)
              (fun _ hr => hr) fun idx hi1 hi2 => hwstk_out idx (by omega)
          · have hszl : 0 < fullWatchSizeCore s.core l := by omega
            have hd := hwat.layout.disjoint l' l hl' hl hll (by omega) hszl
            exact (hwat.slices l' hl').mono (k := s.core) (k' := s'.core) hrefl (Nat.le_refl _)
              (fun _ hr => hr) fun idx hi1 hi2 =>
                hwstk_out idx (by rcases hd with hlt | hgt <;> omega)
  exact ⟨⟨{ hcl with lit_mark_len := hlm_len, wvec_len := by simp [s', hwvl],
                      wstk_len_arr := hwstk_len },
           { hsl with work_stk1_len := hws1_len, work_stk2_len := hws2_len }⟩,
    { hsp.2.1 with
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hwat' },
    ⟨hsp.2.2.1.1, hlm_zero⟩,
    FullArenaVarsNodup.of_arena_eq rfl rfl hsp.2.2.2.1,
    hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem fullArenaSkipShrk_of_first_sentinel {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 →
      (∀ i, p ≤ i → i < t → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      t - p + 1 ≤ fuel → fullArenaSkipShrk ar alen p fuel = t + 1
  | 0, _, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hne_lt, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]
    by_cases hpeq : p = t
    · subst p; simp [hsent]
    · have hne : ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
        hne_lt p (Nat.le_refl p) (by omega)
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      exact fullArenaSkipShrk_of_first_sentinel (by omega) hta hsent
        (fun i hi1 hi2 => hne_lt i (by omega) hi2) (by omega)

theorem fullArenaSkipShrk_first_sentinel {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 →
      t - p + 1 ≤ fuel →
      ∃ t0, p ≤ t0 ∧ t0 ≤ t ∧ fullArenaSkipShrk ar alen p fuel = t0 + 1 ∧
        ar[t0]? = some 0xFFFFFFFF#32 ∧
        (∀ i, p ≤ i → i < t0 → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
  | 0, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]; split
    · rename_i hne
      have hp_ne : p ≠ t := by rintro rfl; simp [hsent] at hne
      obtain ⟨t0, h1, h2, h3, h4, h5⟩ := fullArenaSkipShrk_first_sentinel (ar := ar)
        (alen := alen) (t := t) (fuel := fuel) (p := p + 1) (by omega) hta hsent (by omega)
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

theorem fullArenaScanRefs_next {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos p : Nat}, alen - pos ≤ fuel →
      (∀ r ∈ fullArenaScanRefs ar alen pos fuel,
        fullArenaNextOff ar alen r = alen ∨ fullArenaNextOff ar alen r + 3 ≤ alen) →
      p ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen p = alen ∨
        fullArenaNextOff ar alen p ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, _, hp => by simp [fullArenaScanRefs] at hp
  | fuel + 1, pos, p, hfl, hch, hp => by
    unfold fullArenaScanRefs at hp hch ⊢; split at hp
    · rename_i hle
      have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hp hch ⊢
      rcases hp with rfl | hrest
      · rcases hch p (Or.inl rfl) with hend | hmore
        · exact Or.inl hend
        · right; right
          cases hfuel : fuel with
          | zero => omega
          | succ f' =>
            have hle' : alen - fullArenaNextOff ar alen p ≤ f' + 1 := by omega
            unfold fullArenaScanRefs; simp [hmore]
      · exact (fullArenaScanRefs_next (by omega)
          (fun r hr => hch r (Or.inr hr)) hrest).elim Or.inl fun hm => Or.inr (Or.inr hm)
    · simp at hp

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) :
    0 = k.arena_len ∨ 0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · exact Or.inl hz.symm
  · right; cases hal : k.arena_len with
    | zero => omega
    | succ f =>
      rw [hal] at h3
      unfold fullArenaClauseRefsCore; rw [hal]; unfold fullArenaScanRefs; simp [h3]

theorem fullArenaClauseRefs_next_or_end {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) {p : Nat}
    (hp : p ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len p = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len p ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next (Nat.sub_le _ _) (fun r hr => (ha.refs_wf r hr).2.2.2.2) hp

theorem fullState_eq_replace_arena_lm_ag {a b : FullState}
    (hsc : a.scratch = b.scratch)
    (hc : { a.core with
        arena := b.core.arena, lit_mark := b.core.lit_mark,
        arena_garbage := b.core.arena_garbage } = b.core) :
    a = { b with
      core := { b.core with
        arena := a.core.arena, lit_mark := a.core.lit_mark,
        arena_garbage := a.core.arena_garbage } } := by
  rcases a with ⟨ac, as⟩; rcases b with ⟨bc, bs⟩
  rcases ac; rcases bc; dsimp only at hsc hc; subst hsc; cases hc; rfl

theorem core_eq_of_arena_lm {a b : FullState}
    (hc : { a.core with arena := b.core.arena, lit_mark := b.core.lit_mark } = b.core) :
    { a.core with
      arena := b.core.arena, lit_mark := b.core.lit_mark,
      arena_garbage := b.core.arena_garbage } = b.core := by
  rcases a with ⟨ac, _⟩; rcases b with ⟨bc, _⟩; rcases ac; rcases bc; cases hc; rfl

theorem replace_ag_eq {s0 s3 : FullState}
    (hc3 : { s3.core with arena := s0.core.arena, lit_mark := s0.core.lit_mark } = s0.core)
    {ar4 : List (BitVec 32)} {ag4 : BitVec 64} :
    { ({ s3 with core := { s3.core with arena := ar4, arena_garbage := ag4 } }).core with
        arena := s0.core.arena, lit_mark := s0.core.lit_mark,
        arena_garbage := s0.core.arena_garbage } = s0.core := by
  rcases s0 with ⟨c0, _⟩; rcases s3 with ⟨c3, _⟩; rcases c0; rcases c3; cases hc3; rfl

theorem fullSparseInvW_afterArenaSweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hsok : s'.LengthsOk c) (hext : s'.scratch.extend_len = s.scratch.extend_len)
    (hll : FullLastLearnedWf s') (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hnd' : FullArenaVarsNodup s') (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (hdm : s'.core.dense_mode = s.core.dense_mode) :
    FullSparseInvW c F0 F_cur s' :=
  ⟨hsok, hw',
   ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
    fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩,
   hnd', ⟨hll, hext ▸ hsp.2.2.2.2.1.2⟩, hdm ▸ hsp.2.2.2.2.2⟩

theorem fullSparseInv_afterBacktrack {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInv c F0 s)
    (hsok : s'.LengthsOk c) (hprsc : FullProbeScratchPres s s')
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm : s'.core.dense_mode = s.core.dense_mode) :
    FullSparseInv c F0 s' :=
  ⟨⟨hsok, F_cur, hw'⟩,
   ⟨fun v hv => by rw [hmrk]; exact hsp.2.1.1 v hv,
    fun l hl => by rw [hlm]; exact hsp.2.1.2 l hl⟩,
   FullArenaVarsNodup.of_arena_eq har hal hsp.2.2.1,
   hsp.2.2.2.1.of_pres hprsc.1 (fun r hr => by
     unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rw [har, hal]; exact hr),
   hdm ▸ hsp.2.2.2.2⟩

end FullSubstHelpers

open FullSubstHelpers

/-! ## 2. `full_subst_rewrite_bins` `Func.wp` Proof (`Full3.lean` #27) -/

private def rewriteBinsInnerMask (s : FullState) : FullState :=
  { s with
    core := { s.core with lit_mark := [], wstk := [], num_binary := 0#64 }
    scratch := { s.scratch with work_stk1 := [], work_stk2 := [] } }

private def rewriteBinsClearLmMask (s : FullState) : FullState :=
  { s with core := { s.core with lit_mark := [] } }

private def rewriteBinsZeroMask (s : FullState) : FullState :=
  { s with core := { s.core with wstk := [] } }

private theorem bv32_and_binFlag_ne0_props {w0 : BitVec 32}
    (hf : (w0 &&& 0x80000000#32) ≠ 0#32) (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 0x7FFFFFFF) :
    w0 ≠ 0xFFFFFFFF#32 := by
  intro heq; subst heq; revert hlt; decide

private def withWstk (k : FullCoreState) (ws : List (BitVec 32)) : FullCoreState :=
  { k with wstk := ws }

private def RewriteBinsOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (l : BitVec 64) (ml : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st : FullState,
    FullSparseInvW c F0 F_cur st ∧
    st.core.cur_vars = s0.core.cur_vars ∧ st.core.cur_level = 0 ∧
    st.core.fuel = s0.core.fuel ∧ FullReprEquiv F_cur st ∧
    l.toNat ≤ 2 * s0.core.cur_vars ∧ (FullMem c st ⋆ R) ml

private def RewriteBinsLargeInv (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (l off sz : Nat) (pn p p' q' : BitVec 64) (m2 : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st2 : FullState,
    AgreesExcept rewriteBinsInnerMask st st2 ∧ st2.LengthsOk c ∧
    off ≤ q'.toNat ∧ q'.toNat ≤ p'.toNat ∧ p'.toNat ≤ off + sz ∧
    p.toNat < p'.toNat ∧
    (∀ idx, p'.toNat ≤ idx → st2.core.wstk[idx]? = st.core.wstk[idx]?) ∧
    (∀ idx, (idx < off ∨ off + sz ≤ idx) → st2.core.wstk[idx]? = st.core.wstk[idx]?) ∧
    WatchSliceOk F_cur st.core l p'.toNat (off + sz - p'.toNat) ∧
    WatchSliceOk F_cur (withWstk st.core st2.core.wstk) l off (q'.toNat - off) ∧
    (∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
      ∃ idx, off ≤ idx ∧ idx < q'.toNat ∧
        (st2.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
        (st2.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∧
    (∀ k < pn.toNat,
      (st2.scratch.work_stk1[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
      (st2.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(st2.scratch.work_stk1[k]?.getD 0#32).toNat,
                    (st2.scratch.work_stk2[k]?.getD 0#32).toNat])) ∧
    (FullMem c st2 ⋆ R) m2

private def RewriteBinsNbInv (c : FullCfg) (st1 : FullState)
    (m_nb : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ nb' : BitVec 64,
    (FullMem c { st1 with core := { st1.core with num_binary := nb' } } ⋆ R) m_nb

private def RewriteBinsInner1Inv (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (l off sz : Nat) (pn p q : BitVec 64) (m1 : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st1 : FullState,
    AgreesExcept rewriteBinsInnerMask st st1 ∧ st1.LengthsOk c ∧
    off ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ off + sz ∧
    pn.toNat ≤ 2 * st.core.cur_vars ∧
    (∀ idx, p.toNat ≤ idx → st1.core.wstk[idx]? = st.core.wstk[idx]?) ∧
    (∀ idx, (idx < off ∨ off + sz ≤ idx) → st1.core.wstk[idx]? = st.core.wstk[idx]?) ∧
    WatchSliceOk F_cur st.core l p.toNat (off + sz - p.toNat) ∧
    WatchSliceOk F_cur (withWstk st.core st1.core.wstk) l off (q.toNat - off) ∧
    (∀ x < 2 * c.max_vars, st1.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
      ∃ idx, off ≤ idx ∧ idx < q.toNat ∧
        (st1.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
        (st1.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∧
    (∀ k < pn.toNat,
      (st1.scratch.work_stk1[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
      (st1.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(st1.scratch.work_stk1[k]?.getD 0#32).toNat,
                    (st1.scratch.work_stk2[k]?.getD 0#32).toNat])) ∧
    (FullMem c st1 ⋆ R) m1

private def RewriteBinsInner2Inv (c : FullCfg) (st st1 : FullState) (off q ci : BitVec 64)
    (m2 : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st2 : FullState,
    AgreesExcept rewriteBinsInnerMask st st2 ∧ st2.LengthsOk c ∧
    st2.core.wstk = st1.core.wstk ∧ st2.core.num_binary = st1.core.num_binary ∧
    st2.scratch.work_stk1 = st1.scratch.work_stk1 ∧
    st2.scratch.work_stk2 = st1.scratch.work_stk2 ∧
    off.toNat ≤ ci.toNat ∧ ci.toNat ≤ q.toNat ∧
    (∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
      ∃ idx, ci.toNat ≤ idx ∧ idx < q.toNat ∧
        (st2.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
        (st2.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∧
    (FullMem c st2 ⋆ R) m2

private def RewriteBinsInner3Inv (c : FullCfg) (st st1 st2 : FullState) (off sz : Nat)
    (q ci3 : BitVec 64) (m3 : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st3 : FullState,
    AgreesExcept rewriteBinsInnerMask st st3 ∧ st3.LengthsOk c ∧
    st3.core.lit_mark = st2.core.lit_mark ∧
    st3.core.num_binary = st1.core.num_binary ∧
    st3.scratch.work_stk1 = st1.scratch.work_stk1 ∧
    st3.scratch.work_stk2 = st1.scratch.work_stk2 ∧
    q.toNat ≤ ci3.toNat ∧ ci3.toNat ≤ off + sz ∧
    (∀ idx, (idx < q.toNat ∨ off + sz ≤ idx) →
      st3.core.wstk[idx]? = st1.core.wstk[idx]?) ∧
    (FullMem c st3 ⋆ R) m3

private def RewriteBinsInner4Inv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 _st st4 : FullState) (pn ci4 : BitVec 64) (m5 : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st5 : FullState,
    FullSparseInvW c F0 F_cur st5 ∧
    st5.core.cur_vars = s0.core.cur_vars ∧ st5.core.cur_level = 0 ∧
    st5.core.fuel = s0.core.fuel ∧ FullReprEquiv F_cur st5 ∧
    st5.scratch.work_stk1 = st4.scratch.work_stk1 ∧
    st5.scratch.work_stk2 = st4.scratch.work_stk2 ∧
    ci4.toNat ≤ pn.toNat ∧ (FullMem c st5 ⋆ R) m5

private theorem rewriteBins_st4_eq (st st3 : FullState)
    (hag : AgreesExcept rewriteBinsInnerMask st st3)
    (wv' : List (BitVec 32)) (wu' : BitVec 64) :
    ({ st3 with core := { st3.core with wvec := wv', wusable := wu' } } : FullState) =
      { st with
        core := { st.core with
          lit_mark := st3.core.lit_mark, wvec := wv', wstk := st3.core.wstk,
          wusable := wu', num_binary := st3.core.num_binary }
        scratch := { st.scratch with
          work_stk1 := st3.scratch.work_stk1, work_stk2 := st3.scratch.work_stk2 } } := by
  have hc := congrArg (rewriteBinsInnerMask · |>.core) hag
  have hs := congrArg (rewriteBinsInnerMask · |>.scratch) hag
  cases st3 with | mk c3 sc3 => cases st with | mk cs scs =>
  cases c3; cases cs; simp only [rewriteBinsInnerMask] at hc; cases hc
  cases sc3; cases scs; simp only [rewriteBinsInnerMask] at hs; cases hs; rfl

theorem full_subst_rewrite_bins_wp (Γ : Env)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullSubstRewriteBinsSpec args m Q X →
      Func.wp Γ full_subst_rewrite_bins_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hrepr0, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  -- Outer loop: `while (l < nlits)`
  s_to_group
  refine wp_loop_inv
    (fun (l, ()) ml => RewriteBinsOuterInv c F0 F_cur s0 l ml R)
    (fun (l, ()) _ => 2 * s0.core.cur_vars - l.toNat)
    ?_ ?_
  · intro J hJ; s_steps
    exact hJ (0#64, ()) m ⟨s0, hsp0, rfl, hl0, rfl, hrepr0, Nat.zero_le _, hm⟩
  · rintro J ⟨l, ⟨⟩⟩ ml ⟨st, hsp, hcv, hl0_st, hfl, hrepr, hl_le, hml⟩ hJ
    have hcl := hsp.1.core_ok; have hsl := hsp.1.scratch_ok
    have hcv_le := hcl.cur_vars_le
    have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr
    have hrpl := hcl.repr_len; have hlml := hcl.lit_mark_len
    have hws1l := hsl.work_stk1_len; have hws2l := hsl.work_stk2_len
    have hwle := hcl.wlen_le
    have hwat : WatchesInv F_cur st.core := by
      have hm_w := hsp.2.1.watches; unfold ModeWatchesInv at hm_w
      simp only [hsp.2.2.2.2.2, ↓reduceIte] at hm_w; exact hm_w
    s_split
    · -- `l < nlits`
      have hl_lt : l.toNat < 2 * s0.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
      have hl1 : (l + 1#64).toNat = l.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hl_lt32 : l.toNat < 2 ^ 32 := by omega
      have h2l_eq : (l <<< (1 : BitVec 64)).toNat = 2 * l.toNat := by
        rw [bv64_shl_one, Nat.mod_eq_of_lt (by omega)]
      have h2l1_eq : ((l <<< (1 : BitVec 64)) + 1).toNat = 2 * l.toNat + 1 := by
        rw [BitVec.toNat_add, h2l_eq, bv64_one_toNat, Nat.mod_eq_of_lt (by omega)]
      have h2l_lt : (l <<< (1 : BitVec 64)).toNat < st.core.wvec.length := by
        rw [h2l_eq, hwvl]; omega
      have h2l1_lt : ((l <<< (1 : BitVec 64)) + 1).toNat < st.core.wvec.length := by
        rw [h2l1_eq, hwvl]; omega
      let off := fullWatchOff st l.toNat
      let sz := fullWatchSize st l.toNat
      have hoff_eq : (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'(h2l_lt)).toNat = off := by
        dsimp only [off, fullWatchOff, fullWatchOffCore]
        rw [← h2l_eq, List.getElem?_eq_getElem h2l_lt, Option.getD_some]
      have hsz_eq :
          (st.core.wvec[((l <<< (1 : BitVec 64)) + 1).toNat]'(h2l1_lt)).toNat = sz := by
        dsimp only [sz, fullWatchSize, fullWatchSizeCore]
        rw [← h2l1_eq, List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
      have hwv0_eq : ∀ h, (st.core.wvec[2 * l.toNat % 2 ^ 64]'h).toNat = off := fun h => by
        have heq : 2 * l.toNat % 2 ^ 64 = (l <<< (1 : BitVec 64)).toNat := by omega
        have := congrArg (Option.getD · 0#32)
          ((List.getElem?_eq_getElem h).symm.trans (by rw [heq, List.getElem?_eq_getElem h2l_lt]))
        exact (congrArg BitVec.toNat this).trans hoff_eq
      have hwv1_eq : ∀ h, (st.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'h).toNat = sz := fun h => by
        have heq : (2 * l.toNat + 1) % 2 ^ 64 = ((l <<< (1 : BitVec 64)) + 1).toNat := by omega
        have := congrArg (Option.getD · 0#32)
          ((List.getElem?_eq_getElem h).symm.trans (by rw [heq, List.getElem?_eq_getElem h2l1_lt]))
        exact (congrArg BitVec.toNat this).trans hsz_eq
      have hbound := hwat.layout.bounds l.toNat (hcv ▸ hl_lt)
      have hslice_orig := hwat.slices l.toNat (hcv ▸ hl_lt)
      change off + sz ≤ st.core.wlen at hbound
      change WatchSliceOk F_cur st.core l.toNat off sz at hslice_orig
      have hend_lt : off + sz ≤ c.wcap := by omega
      s_split
      · -- `sz == 0`: skip
        s_steps
        exact hJ (l + 1#64, ()) ml (by dsimp only; omega)
          ⟨st, hsp, hcv, hl0_st, hfl, hrepr, by omega, hml⟩
      · -- `sz ≠ 0`: compact `wstk[off ..< off + sz)`
        have hidx_w1 : (2 * l.toNat + 1) % 2 ^ 64 =
            ((l <<< (1 : BitVec 64)) + 1).toNat := by rw [h2l1_eq, Nat.mod_eq_of_lt (by omega)]
        have hsz_pos : 0 < sz := Nat.zero_lt_of_ne_zero fun hz => by
          have hne0 :
              (st.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'(by
                rw [hidx_w1]; exact h2l1_lt)).setWidth 64 ≠ 0#64 := by
            assumption
          have heq0 :
              (st.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'(by
                rw [hidx_w1]; exact h2l1_lt)).setWidth 64 = 0#64 := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            exact (hwv1_eq _).trans hz
          exact hne0 heq0
        have hrl_lt : (st.core.repr[l.toNat]'(by omega)).toNat < 2 * st.core.cur_vars := by
          have := FullReprEquiv.lt hrepr (hcv ▸ hl_lt)
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        have hrl_eqv : LitEquiv (cnfOfClauses F_cur) l.toNat
            (st.core.repr[l.toNat]'(by omega)).toNat := by
          have := FullReprEquiv.litEquiv hrepr (hcv ▸ hl_lt)
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        s_to_group
        -- Inner Loop 1: compact `[off, off + sz)` into `[off, q)` while building `pa, pb`
        refine wp_loop_inv
          (fun (pn, p, q, ()) m1 => RewriteBinsInner1Inv c F_cur st l.toNat off sz pn p q m1 R)
          (fun (_, p, _, ()) _ => off + sz - p.toNat)
          ?_ ?_
        · intro J1 hJ1; s_steps
          have h0_eq : ∀ (h : (l <<< (1 : BitVec 64)).toNat < st.core.wvec.length),
              (BitVec.setWidth 64 (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h)).toNat = off :=
            fun _ => by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
          refine hJ1 _ _ ?_
          refine ⟨st, AgreesExcept.refl _ _, hsp.1,
            Nat.le_of_eq (h0_eq _).symm, Nat.le_refl _,
            Nat.le_trans (Nat.le_of_eq (h0_eq _)) (Nat.le_add_right _ _), Nat.zero_le _,
            fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, fun _ h => by simp at h, hml⟩
          · refine Eq.subst
              (motive := fun x => WatchSliceOk F_cur st.core l.toNat x (off + sz - x))
              (h0_eq _).symm ?_
            rw [Nat.add_sub_cancel_left]; exact hslice_orig
          · refine Eq.subst
              (motive := fun x =>
                WatchSliceOk F_cur (withWstk st.core st.core.wstk) l.toNat off (x - off))
              (h0_eq _).symm ?_
            rw [Nat.sub_self]; exact .empty
          · intro x hx hnz; exfalso; exact hnz (hsp.2.2.1.2 x hx)
        · rintro J1 ⟨pn, p, q, ⟨⟩⟩ m1
            ⟨st1, hag1, hlen1, hq_lo, hqp, hp_hi, hpn_le, htail1, hout1,
             hrem1, hkept1, hlm1, hpa1, hm1⟩ hJ1
          have hcl1 := hlen1.core_ok; have hsl1 := hlen1.scratch_ok
          have hwsl1 := hcl1.wstk_len_arr; have hlml1 := hcl1.lit_mark_len
          have hrpl1 := hcl1.repr_len
          have hws1l1 := hsl1.work_stk1_len; have hws2l1 := hsl1.work_stk2_len
          have har1 : st1.core.arena = st.core.arena := hag1.get (·.core.arena)
          have harl1 : st1.core.arena_len = st.core.arena_len := hag1.get (·.core.arena_len)
          have hcv1 : st1.core.cur_vars = st.core.cur_vars := hag1.get (·.core.cur_vars)
          have hrp1 : st1.core.repr = st.core.repr := hag1.get (·.core.repr)
          s_split
          · -- `p < end`
            have hp_lt : p.toNat < off + sz := by
              rw [hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt (by omega)] at hc; omega
            have hp1 : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := by
              rw [BitVec.toNat_add, bv64_one_toNat, Nat.mod_eq_of_lt (by omega)]
            let w0 := st1.core.wstk[p.toNat]'(by omega)
            have hw0_eq : st.core.wstk[p.toNat]? = some w0 := by
              rw [← htail1 p.toNat (Nat.le_refl _), List.getElem?_eq_getElem (by omega)]
            s_split
            · -- `(w0 &&& PW_BIN_FLAG) == 0u`: large 2-word watch
              have hfl0 : (w0 &&& 0x80000000#32) = 0#32 := by assumption
              obtain ⟨w0', cref, hrem2, hw0_s, hcr_s, hfw, hcr_lt, hcr_ref, hrem_next⟩ :=
                wsStepNonbin hrem1 (by omega)
                  (by rw [hw0_eq, Option.getD_some]; exact hfl0)
              have hw0_id : w0' = w0 := Option.some.inj (hw0_s.symm.trans hw0_eq)
              subst hw0_id
              have hcr_eq1 :
                  st1.core.wstk[(p + (1 : BitVec 64)).toNat]'(by rw [hp1]; omega) = cref := by
                have hg := htail1 (p.toNat + 1) (by omega)
                have hs : st1.core.wstk[p.toNat + 1]? = some cref := hg.trans hcr_s
                rw [← hp1, List.getElem?_eq_getElem (by rw [hp1]; omega)] at hs
                exact Option.some.inj hs
              s_to_group
              refine wp_join_group (ts := [i64, i64])
                (fun (p', q', ()) m2 =>
                  RewriteBinsLargeInv c F_cur st l.toNat off sz pn p p' q' m2 R)
                ?_ ?_
              · rintro _ ⟨p', q', ⟨⟩⟩ m2
                  ⟨st2, hag2, hlen2, hq2_lo, hqp2, hp2_hi, hpp2, htail2, hout2,
                   hrem2', hkept2, hlm2, hpa2, hm2⟩
                s_steps
                exact hJ1 (pn, p', q', ()) m2 (by dsimp only; omega)
                  ⟨st2, hag2, hlen2, hq2_lo, hqp2, hp2_hi, hpn_le, htail2, hout2,
                   hrem2', hkept2, hlm2, hpa2, hm2⟩
              · intro Jnb hNb
                s_split
                · -- `p + 1 < end`
                  have hq_add1 : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := by
                    rw [BitVec.toNat_add, bv64_one_toNat, Nat.mod_eq_of_lt (by omega)]
                  have hq_add2 : (q + (2 : BitVec 64)).toNat = q.toNat + 2 := by
                    rw [BitVec.toNat_add, bv64_two_toNat, Nat.mod_eq_of_lt (by omega)]
                  have hp_add2 : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := by
                    rw [BitVec.toNat_add, bv64_two_toNat, Nat.mod_eq_of_lt (by omega)]
                  s_steps
                  let wstk2 := (st1.core.wstk.set q.toNat w0).set (q.toNat + 1) cref
                  let st2 : FullState := { st1 with core := { st1.core with wstk := wstk2 } }
                  have hwstk2_len : wstk2.length = c.wcap := by
                    dsimp only [wstk2]; rw [List.length_set, List.length_set, hwsl1]
                  have hlen2 : st2.LengthsOk c :=
                    ⟨{ hcl1 with wstk_len_arr := hwstk2_len }, hsl1⟩
                  have htail2 : ∀ idx, (p + (2 : BitVec 64)).toNat ≤ idx →
                      st2.core.wstk[idx]? = st.core.wstk[idx]? := fun idx hidx => by
                    dsimp only [st2, wstk2]
                    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                    exact htail1 idx (by omega)
                  have hout2 : ∀ idx, (idx < off ∨ off + sz ≤ idx) →
                      st2.core.wstk[idx]? = st.core.wstk[idx]? := fun idx hidx => by
                    dsimp only [st2, wstk2]
                    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                    exact hout1 idx hidx
                  have hkept2 : WatchSliceOk F_cur (withWstk st.core st2.core.wstk)
                      l.toNat off ((q + (2 : BitVec 64)).toNat - off) := by
                    rw [hq_add2, show q.toNat + 2 - off = (q.toNat - off) + 2 by omega]
                    refine wsAppendLarge (k := withWstk st.core st1.core.wstk)
                      (Nat.le_refl _) (fun _ r => r) (fun idx hidx => by
                        dsimp only [st2, wstk2, withWstk]
                        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
                      hkept1
                      (by dsimp only [st2, wstk2, withWstk]
                          rw [show off + (q.toNat - off) = q.toNat by omega]
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)])
                      (by dsimp only [st2, wstk2, withWstk]
                          rw [show off + (q.toNat - off) + 1 = q.toNat + 1 by omega]
                          exact List.getElem?_set_self (by rw [List.length_set, hwsl1]; omega))
                      hfl0 hcr_lt hcr_ref
                  have hlm2 : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                      ∃ idx, off ≤ idx ∧ idx < (q + (2 : BitVec 64)).toNat ∧
                        (st2.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
                        (st2.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x := by
                    intro x hx hnz
                    obtain ⟨idx, hi1, hi2, hf, hv⟩ := hlm1 x hx hnz
                    refine ⟨idx, hi1, by omega, ?_, ?_⟩
                    · dsimp only [st2, wstk2]
                      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                      exact hf
                    · dsimp only [st2, wstk2]
                      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                      exact hv
                  have hm2_eq :
                      wstk2 = (st1.core.wstk.set q.toNat w0).set (q + (1 : BitVec 64)).toNat
                        ((st1.core.wstk.set q.toNat w0)[(p + (1 : BitVec 64)).toNat]'(
                          by rw [List.length_set, hp1]; omega)) := by
                    have hval : (st1.core.wstk.set q.toNat w0)[(p + (1 : BitVec 64)).toNat]'(
                        by rw [List.length_set, hp1]; omega) = cref := by
                      rw [List.getElem_set_ne (by rw [hp1]; omega)]; exact hcr_eq1
                    dsimp only [wstk2]; rw [hq_add1, hval]
                  have hag2 : AgreesExcept rewriteBinsInnerMask st st2 := hag1
                  have hp_11 : (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p.toNat + 2 := by
                    rw [BitVec.toNat_add, hp1, bv64_one_toNat, Nat.mod_eq_of_lt (by omega)]
                  refine hNb _ _ ?_
                  refine ⟨st2, hag2, hlen2, by rw [hq_add2]; omega, by rw [hp_11, hq_add2]; omega,
                    by rw [hp_11]; omega, by rw [hp_11]; omega,
                    fun idx hidx => htail2 idx (by rw [hp_11] at hidx; omega), hout2,
                    by rw [hp_11, show off + sz - (p.toNat + 2) = off + sz - p.toNat - 2 by omega]
                       exact hrem_next,
                    hkept2, hlm2, hpa1, ?_⟩
                  · dsimp only [st2]; rw [hm2_eq]; assumption
                · exfalso
                  try rw [hwv0_eq, hwv1_eq] at hc
                  try rw [BitVec.toNat_add, bv64_one_toNat] at hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hc
                  try rw [Nat.mod_eq_of_lt (by omega)] at hc
                  omega
            · -- `(w0 &&& PW_BIN_FLAG) ≠ 0u`: binary watch `[l, ot]`
              have hfl_ne : (w0 &&& 0x80000000#32) ≠ 0#32 := by assumption
              obtain ⟨w0', hw0_s, hfl_bin, hne_ff, hot_lt, hent_bin, hrem_next⟩ :=
                wsStepBin hrem1 (by omega)
                  (by rw [hw0_eq, Option.getD_some]; exact hfl_ne)
              have hw0_id : w0' = w0 := Option.some.inj (hw0_s.symm.trans hw0_eq)
              subst hw0_id
              let ot := w0 &&& 0x7FFFFFFF#32
              have hot_nat : ot.toNat < 2 * st.core.cur_vars := hot_lt
              have hot_eqv := FullReprEquiv.litEquiv hrepr hot_lt
              let rot := st1.core.repr[ot.toNat]'(by omega)
              have hrot_eq : st.core.repr[ot.toNat]?.getD 0#32 = rot := by
                have hget1 : st1.core.repr[ot.toNat]?.getD 0#32 = rot := by
                  dsimp only [rot]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                rw [hrp1] at hget1; exact hget1
              have hrot_lt : rot.toNat < 2 * st.core.cur_vars := by
                rw [← hrot_eq]; exact FullReprEquiv.lt hrepr hot_lt
              have hrot_eqv : LitEquiv (cnfOfClauses F_cur) ot.toNat rot.toNat := by
                rw [← hrot_eq]; exact hot_eqv
              have hent_sub : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [(st.core.repr[l.toNat]'(by omega)).toNat, rot.toNat]) :=
                entails_bin_subst hrl_eqv hrot_eqv hent_bin
              have hrem_p1 : WatchSliceOk F_cur st.core l.toNat
                  (p + (1 : BitVec 64)).toNat (off + sz - (p + (1 : BitVec 64)).toNat) := by
                rw [hp1, show off + sz - (p.toNat + 1) = off + sz - p.toNat - 1 by omega]
                exact hrem_next
              s_to_group
              -- `Js_rot : (rot, ())`
              refine wp_join_group (ts := [i32])
                (fun (rot_v, ()) m_r => rot_v = rot ∧ (FullMem c st1 ⋆ R) m_r) ?_ ?_
              · rintro _ ⟨rot_v, ⟨⟩⟩ m_r ⟨hrot_v, hm_r⟩
                subst hrot_v
                s_to_group
                -- `Js_bin : (pn', q', ())`
                refine wp_join_group (ts := [i64, i64])
                  (fun (pn', q', ()) m2 =>
                    RewriteBinsInner1Inv c F_cur st l.toNat off sz pn'
                      (p + (1 : BitVec 64)) q' m2 R)
                  ?_ ?_
                · rintro _ ⟨pn', q', ⟨⟩⟩ m2 h2
                  s_steps
                  exact hJ1 (pn', p + (1 : BitVec 64), q', ()) m2 (by dsimp only; omega) h2
                · intro Jbin hBin
                  s_to_group
                  -- `Js_else : (pn', ())` (`else` of `rl == (u32)l && rot == ot`)
                  refine wp_join_group (ts := []) (fun () m_e => (FullMem c st1 ⋆ R) m_e) ?_ ?_
                  · rintro _ ⟨⟩ m_e hm_e
                    s_to_group
                    refine wp_join_group (ts := [i64])
                      (fun (pn', ()) m2 =>
                        RewriteBinsInner1Inv c F_cur st l.toNat off sz pn'
                          (p + (1 : BitVec 64)) q m2 R)
                      ?_ ?_
                    · rintro _ ⟨pn', ⟨⟩⟩ m2 h2
                      s_steps; exact hBin (pn', q, ()) m2 h2
                    · intro Jelse hElse
                      s_split
                      · -- `l < ot`: optional `num_binary--`, optional push `(rl, rot)`
                        s_to_group
                        refine wp_join_group (ts := [])
                          (fun () m_nb => RewriteBinsNbInv c st1 m_nb R)
                          ?_ ?_
                        · rintro _ ⟨⟩ m_nb ⟨nb', hnb⟩
                          let st2 : FullState :=
                            { st1 with core := { st1.core with num_binary := nb' } }
                          have hlen2 : st2.LengthsOk c :=
                            ⟨{ hcl1 with wstk_len_arr := hwsl1 }, hsl1⟩
                          have hag2 : AgreesExcept rewriteBinsInnerMask st st2 := hag1
                          s_to_group
                          refine wp_join_group (ts := [i64])
                            (fun (pn', ()) m2 =>
                              RewriteBinsInner1Inv c F_cur st l.toNat off sz pn'
                                (p + (1 : BitVec 64)) q m2 R)
                            ?_ ?_
                          · rintro _ ⟨pn', ⟨⟩⟩ m2 h2
                            s_steps; exact hElse (pn', ()) m2 h2
                          · intro Jsc hSc
                            s_split
                            · -- `rl != rot ^ 1 && pn < nlits`
                              s_split
                              · -- `pn < nlits`
                                have hpn_lt : pn.toNat < 2 * st.core.cur_vars := by
                                  rw [Nat.mod_eq_of_lt (by omega),
                                    Nat.mod_eq_of_lt (by omega)] at hc
                                  omega
                                have hpn1 : (pn + 1#64).toNat = pn.toNat + 1 := by
                                  rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
                                    Nat.mod_eq_of_lt (by omega)]
                                s_steps
                                let ws1' := st1.scratch.work_stk1.set pn.toNat
                                  (st.core.repr[l.toNat]'(by omega))
                                let ws2' := st1.scratch.work_stk2.set pn.toNat rot
                                let st3 : FullState :=
                                  { core := { st1.core with num_binary := nb' }
                                    scratch := { st1.scratch with
                                      work_stk1 := ws1', work_stk2 := ws2' } }
                                have hws1_eq : st3.scratch.work_stk1 = ws1' := rfl
                                have hws2_eq : st3.scratch.work_stk2 = ws2' := rfl
                                have hlen3 : st3.LengthsOk c :=
                                  ⟨{ hcl1 with wstk_len_arr := hwsl1 },
                                   { hsl1 with
                                     work_stk1_len := by
                                       rw [hws1_eq]; dsimp only [ws1']
                                       rw [List.length_set, hws1l1],
                                     work_stk2_len := by
                                       rw [hws2_eq]; dsimp only [ws2']
                                       rw [List.length_set, hws2l1] }⟩
                                have hpa3 : ∀ k < (pn + 1#64).toNat,
                                    (st3.scratch.work_stk1[k]?.getD 0#32).toNat <
                                      2 * st.core.cur_vars ∧
                                    (st3.scratch.work_stk2[k]?.getD 0#32).toNat <
                                      2 * st.core.cur_vars ∧
                                    (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause [(st3.scratch.work_stk1[k]?.getD 0#32).toNat,
                                                  (st3.scratch.work_stk2[k]?.getD 0#32).toNat]) :=
                                  by
                                  intro k hk; rw [hws1_eq, hws2_eq]; dsimp only [ws1', ws2']
                                  by_cases hkp : k = pn.toNat
                                  · subst hkp
                                    rw [List.getElem?_set_self (by omega),
                                      List.getElem?_set_self (by omega),
                                      Option.getD_some, Option.getD_some]
                                    exact ⟨hrl_lt, by omega, hent_sub⟩
                                  · rw [List.getElem?_set_ne (Ne.symm hkp),
                                      List.getElem?_set_ne (Ne.symm hkp)]
                                    exact hpa1 k (by omega)
                                refine hSc (pn + 1#64, ()) _
                                  ⟨st3, hag2, hlen3, hq_lo, by omega, by omega, by omega,
                                   fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                                   hkept1, hlm1, hpa3, ?_⟩
                                exact (by assumption : (FullMem c st3 ⋆ R) _)
                              · s_steps
                                exact hSc (pn, ()) m_nb
                                  ⟨st2, hag2, hlen2, hq_lo, by omega, by omega, hpn_le,
                                   fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                                   hkept1, hlm1, hpa1, hnb⟩
                            · s_steps
                              exact hSc (pn, ()) m_nb
                                ⟨st2, hag2, hlen2, hq_lo, by omega, by omega, hpn_le,
                                 fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                                 hkept1, hlm1, hpa1, hnb⟩
                        · intro Jnb hNb
                          s_split
                          · s_steps; exact hNb () _ ⟨st1.core.num_binary - 1#64, by assumption⟩
                          · s_steps; exact hNb () m_e ⟨st1.core.num_binary, hm_e⟩
                      · s_steps
                        exact hElse (pn, ()) m_e
                          ⟨st1, hag1, hlen1, hq_lo, by omega, by omega, hpn_le,
                           fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                           hkept1, hlm1, hpa1, hm_e⟩
                  · intro Jelse hElse
                    s_split
                    · -- `rl == (u32)l`
                      s_split
                      · -- `rot == ot`: `then` branch
                        have hot_lm_lt :
                            (BitVec.setWidth 64
                              (st1.core.wstk[p.toNat]'(by omega) &&& 0x7FFFFFFF#32)).toNat <
                              st1.core.lit_mark.length := by
                          have hlt := bv32_and_litMask_lt (st1.core.wstk[p.toNat]'(by omega))
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                          change ot.toNat < _; omega
                        s_to_group
                        refine wp_join_group (ts := [i64])
                          (fun (q', ()) m2 =>
                            RewriteBinsInner1Inv c F_cur st l.toNat off sz pn
                              (p + (1 : BitVec 64)) q' m2 R)
                          ?_ ?_
                        · rintro _ ⟨q', ⟨⟩⟩ m2 h2
                          s_steps
                          exact hBin (pn, q', ()) m2 h2
                        · intro Jth hTh
                          s_split
                          · -- `lm[ot] == 0#8`
                            have hq_add1 : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := by
                              rw [BitVec.toNat_add, bv64_one_toNat, Nat.mod_eq_of_lt (by omega)]
                            s_steps
                            let st2 : FullState :=
                              { st1 with core := { st1.core with
                                  lit_mark := st1.core.lit_mark.set ot.toNat 1#8
                                  wstk := st1.core.wstk.set q.toNat w0 } }
                            have hlm_len2 : st2.core.lit_mark.length = 2 * c.max_vars := by
                              rw [show st2.core.lit_mark = _ from rfl, List.length_set, hlml1]
                            have hws_len2 : st2.core.wstk.length = c.wcap := by
                              rw [show st2.core.wstk = _ from rfl, List.length_set, hwsl1]
                            have hlen2 : st2.LengthsOk c :=
                              ⟨{ hcl1 with lit_mark_len := hlm_len2, wstk_len_arr := hws_len2 },
                               hsl1⟩
                            have htail2 : ∀ idx, (p + (1 : BitVec 64)).toNat ≤ idx →
                                st2.core.wstk[idx]? = st.core.wstk[idx]? := fun idx hidx => by
                              dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]
                              exact htail1 idx (by omega)
                            have hout2 : ∀ idx, (idx < off ∨ off + sz ≤ idx) →
                                st2.core.wstk[idx]? = st.core.wstk[idx]? := fun idx hidx => by
                              dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]
                              exact hout1 idx hidx
                            have hkept2 : WatchSliceOk F_cur (withWstk st.core st2.core.wstk)
                                l.toNat off ((q + (1 : BitVec 64)).toNat - off) := by
                              rw [hq_add1, show q.toNat + 1 - off = (q.toNat - off) + 1 by omega]
                              exact wsAppendBin
                                (k := withWstk st.core st1.core.wstk)
                                (Nat.le_refl _) (fun _ r => r)
                                (fun idx hidx => by
                                  dsimp only [st2, withWstk]; rw [List.getElem?_set_ne (by omega)])
                                hkept1
                                (by dsimp only [st2, withWstk]
                                    rw [show off + (q.toNat - off) = q.toNat by omega]
                                    exact List.getElem?_set_self (by omega))
                                hfl_bin hne_ff hot_lt hent_bin
                            have hlm2 : ∀ x < 2 * c.max_vars,
                                st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                                ∃ idx, off ≤ idx ∧ idx < (q + (1 : BitVec 64)).toNat ∧
                                  (st2.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
                                  (st2.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x := by
                              intro x hx hnz; dsimp only [st2] at hnz ⊢
                              by_cases hxot : x = ot.toNat
                              · subst hxot
                                refine ⟨q.toNat, hq_lo, by omega, ?_, ?_⟩
                                · rw [List.getElem?_set_self (by omega), Option.getD_some]
                                  exact hfl_bin
                                · rw [List.getElem?_set_self (by omega), Option.getD_some]
                              · rw [List.getElem?_set_ne (Ne.symm hxot)] at hnz
                                obtain ⟨idx, hi1, hi2, hf, hv⟩ := hlm1 x hx hnz
                                refine ⟨idx, hi1, by omega, ?_, ?_⟩
                                · rw [List.getElem?_set_ne (by omega)]; exact hf
                                · rw [List.getElem?_set_ne (by omega)]; exact hv
                            exact hTh (q + (1 : BitVec 64), ()) _
                              ⟨st2, hag1, hlen2, by omega, by omega, by omega, hpn_le, htail2,
                               hout2, hrem_p1,
                               hkept2, hlm2, hpa1, (by assumption : (FullMem c st2 ⋆ R) _)⟩
                          · -- `lm[ot] != 0#8`: `else if (l < ot && num_binary > 0)`
                            s_to_group
                            refine wp_join_group (ts := [])
                              (fun () m_nb => RewriteBinsNbInv c st1 m_nb R)
                              ?_ ?_
                            · rintro _ ⟨⟩ m_nb ⟨nb', hnb⟩
                              let st2 : FullState :=
                                { st1 with core := { st1.core with num_binary := nb' } }
                              exact hTh (q, ()) m_nb
                                ⟨st2, hag1, ⟨{ hcl1 with wstk_len_arr := hwsl1 }, hsl1⟩,
                                 hq_lo, by omega, by omega, hpn_le,
                                 fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                                 hkept1, hlm1, hpa1, hnb⟩
                            · intro Jt3 hT3
                              s_split
                              · s_split
                                · s_steps
                                  exact hT3 () _ ⟨st1.core.num_binary - 1#64, by assumption⟩
                                · s_steps
                                  exact hT3 () m_r ⟨st1.core.num_binary, hm_r⟩
                              · s_steps
                                exact hT3 () m_r ⟨st1.core.num_binary, hm_r⟩
                      · s_steps; exact hElse () m_r hm_r
                    · s_steps; exact hElse () m_r hm_r
              · intro Jrot hJrot
                s_split
                · s_steps; exact hJrot (rot, ()) m1 ⟨rfl, hm1⟩
                · exfalso
                  change ¬ ot.toNat < 2 * (s0.core.cur_vars % 2 ^ 64) % 2 ^ 64 at hc
                  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
                  omega
          · -- Exit Inner Loop 1 (`p.toNat = off + sz`): Loop 2, Loop 3, update wvec/wusable, Loop 4
            rw [hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt (by omega)] at hc
            have hp_end : p.toNat = off + sz := by omega
            have hq_hi : q.toNat ≤ off + sz := by omega
            clear hrem1 htail1 hJ1 hqp hp_hi
            s_to_group
            -- Inner Loop 2: `c = off; while (c < q) clear lm`
            refine wp_loop_inv
              (fun (ci, ()) m2 => RewriteBinsInner2Inv c st st1 (BitVec.ofNat 64 off) q ci m2 R)
              (fun (ci, ()) _ => q.toNat - ci.toNat)
              ?_ ?_
            · intro J2 hJ2; s_steps
              refine hJ2 _ m1 ?_
              have h0_eq : ∀ (h : (l <<< (1 : BitVec 64)).toNat < st.core.wvec.length),
                  (BitVec.setWidth 64 (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h)).toNat =
                  off :=
                fun _ => by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
              refine ⟨st1, hag1, hlen1, rfl, rfl, rfl, rfl,
                by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                   exact Nat.le_of_eq (h0_eq _).symm,
                Nat.le_trans (Nat.le_of_eq (h0_eq _)) hq_lo, fun x hx hnz => by
                  obtain ⟨idx, hi1, hi2, hf, hv⟩ := hlm1 x hx hnz
                  exact ⟨idx, Nat.le_trans (Nat.le_of_eq (h0_eq _)) hi1, hi2, hf, hv⟩, hm1⟩
            · rintro J2 ⟨ci, ⟨⟩⟩ m2
                ⟨st2, hag2, hlen2, hws_eq2, hnb_eq2, hws1_eq2, hws2_eq2, hci_lo, hci_hi, hlm2, hm2⟩
                hJ2
              have hci_off : off ≤ ci.toNat := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hci_lo; exact hci_lo
              have hcl2 := hlen2.core_ok; have hsl2 := hlen2.scratch_ok
              have hwsl2 := hcl2.wstk_len_arr; have hlml2 := hcl2.lit_mark_len
              s_split
              · have hci_lt : ci.toNat < q.toNat := hc
                have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                s_to_group
                refine wp_join_group (ts := [])
                  (fun () m2' =>
                    RewriteBinsInner2Inv c st st1 (BitVec.ofNat 64 off) q (ci + 1#64) m2' R)
                  ?_ ?_
                · rintro _ ⟨⟩ m2' h2'
                  s_steps
                  exact hJ2 (ci + 1#64, ()) m2' (by dsimp only; omega) h2'
                · intro Jc hC
                  s_split
                  · have hf_ne : (st2.core.wstk[ci.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by
                      assumption
                    have hbin_lt : (st2.core.wstk[ci.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat <
                        2 * st.core.cur_vars := by
                      have hb := wsBinLtOfFlag hkept1 ci.toNat hci_off (by omega)
                        (by dsimp only [withWstk]
                            rw [← hws_eq2, List.getElem?_eq_getElem (by omega), Option.getD_some]
                            exact hf_ne)
                      dsimp only [withWstk] at hb
                      rwa [← hws_eq2, List.getElem?_eq_getElem (by omega), Option.getD_some] at hb
                    have hbin_lt_b :
                        (BitVec.setWidth 64
                          (st2.core.wstk[ci.toNat]'(by omega) &&& 0x7FFFFFFF#32)).toNat <
                          st2.core.lit_mark.length := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
                    s_steps
                    let clit := (st2.core.wstk[ci.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat
                    have hclit_zext : ∀ h,
                        (BitVec.setWidth 64
                          (st2.core.wstk[ci.toNat]'h &&& 0x7FFFFFFF#32)).toNat = clit :=
                      fun _ => by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    let st2' : FullState :=
                      { st2 with core := { st2.core with
                          lit_mark := st2.core.lit_mark.set clit 0#8 } }
                    have hlm2' : ∀ x < 2 * c.max_vars, st2'.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                        ∃ idx, (ci + 1#64).toNat ≤ idx ∧ idx < q.toNat ∧
                          (st2'.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
                          (st2'.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x := by
                      intro x hx hnz; dsimp only [st2'] at hnz ⊢
                      by_cases hxc : x = clit
                      · subst hxc; rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz
                        exact absurd rfl hnz
                      · rw [List.getElem?_set_ne (Ne.symm hxc)] at hnz
                        obtain ⟨idx, hi1, hi2, hf, hv⟩ := hlm2 x hx hnz
                        have hne_ci : idx ≠ ci.toNat := by
                          rintro rfl
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hv
                          exact hxc hv.symm
                        exact ⟨idx, by omega, hi2, hf, hv⟩
                    have hlm_len2' : st2'.core.lit_mark.length = 2 * c.max_vars := by
                      rw [show st2'.core.lit_mark = _ from rfl, List.length_set, hcl2.lit_mark_len]
                    refine hC () _
                      ⟨st2', hag2, ⟨{ hcl2 with lit_mark_len := hlm_len2' }, hsl2⟩,
                        hws_eq2, hnb_eq2, hws1_eq2, hws2_eq2,
                        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega,
                        by omega, hlm2', ?_⟩
                    dsimp only [st2']; rw [← hclit_zext]
                    try rw [show (0#8 : BitVec 8) = BitVec.setWidth 8 (0 : BitVec 32) from rfl]
                    assumption
                  · have hf_eq : (st2.core.wstk[ci.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by
                      assumption
                    s_steps
                    have hlm2' : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                        ∃ idx, (ci + 1#64).toNat ≤ idx ∧ idx < q.toNat ∧
                          (st2.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
                          (st2.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x := by
                      intro x hx hnz
                      obtain ⟨idx, hi1, hi2, hf, hv⟩ := hlm2 x hx hnz
                      have hne_ci : idx ≠ ci.toNat := by
                        rintro rfl
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hf
                        exact hf hf_eq
                      exact ⟨idx, by omega, hi2, hf, hv⟩
                    exact hC () m2
                      ⟨st2, hag2, hlen2, hws_eq2, hnb_eq2, hws1_eq2, hws2_eq2,
                       by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega,
                       by omega, hlm2', hm2⟩
              · -- Exit Inner Loop 2 (`ci.toNat = q.toNat`): `lit_mark` all zero
                have hlm_zero : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 = 0#8 := by
                  intro x hx
                  exact Classical.byContradiction fun hnz => by
                    obtain ⟨idx, hi1, hi2, _⟩ := hlm2 x hx hnz
                    have : ¬ ci.toNat < q.toNat := hc
                    omega
                s_to_group
                -- Inner Loop 3: `c = q; while (c < end) { wstk[c] = 0xFFFFFFFFu; c++; }`
                refine wp_loop_inv
                  (fun (ci3, ()) m3 => RewriteBinsInner3Inv c st st1 st2 off sz q ci3 m3 R)
                  (fun (ci3, ()) _ => off + sz - ci3.toNat)
                  ?_ ?_
                · intro J3 hJ3; s_steps
                  exact hJ3 (q, ()) m2 ⟨st2, hag2, hlen2, rfl, hnb_eq2, hws1_eq2, hws2_eq2,
                    Nat.le_refl _, by omega, fun _ _ => by rw [hws_eq2], hm2⟩
                · rintro J3 ⟨ci3, ⟨⟩⟩ m3
                    ⟨st3, hag3, hlen3, hlm_eq3, hnb_eq3, hw1_eq3, hw2_eq3, hci3_lo, hci3_hi,
                     hwstk3, hm3⟩ hJ3
                  have hcl3 := hlen3.core_ok; have hsl3 := hlen3.scratch_ok
                  have hwsl3 := hcl3.wstk_len_arr
                  s_split
                  · have hci3_lt : ci3.toNat < off + sz := by
                      rw [hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt (by omega)] at hc; omega
                    have hci3_1 : (ci3 + 1#64).toNat = ci3.toNat + 1 := by
                      rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    s_steps
                    let st3' : FullState := { st3 with core := { st3.core with
                        wstk := st3.core.wstk.set ci3.toNat 0xFFFFFFFF#32 } }
                    have hws_len3' : st3'.core.wstk.length = c.wcap := by
                      rw [show st3'.core.wstk = _ from rfl, List.length_set, hcl3.wstk_len_arr]
                    exact hJ3 (ci3 + 1#64, ()) _ (by dsimp only; omega)
                      ⟨st3', hag3, ⟨{ hcl3 with wstk_len_arr := hws_len3' }, hsl3⟩,
                        hlm_eq3, hnb_eq3, hw1_eq3, hw2_eq3, by omega, by omega,
                        fun idx hidx => by
                          dsimp only [st3']; rw [List.getElem?_set_ne (by omega)]
                          exact hwstk3 idx hidx,
                        (by assumption : (FullMem c st3' ⋆ R) _)⟩
                  · -- Exit Inner Loop 3: update `wvec[(l<<1)+1]`, `wusable`
                    have hwu_idx : (2 * l.toNat + 1) % 2 ^ 64 <
                        st3.core.wvec.length := by
                      have : st3.core.wvec = st.core.wvec := hag3.get (·.core.wvec)
                      rw [this, hwvl, Nat.mod_eq_of_lt (by omega)]; omega
                    s_steps
                    let st4 : FullState :=
                      { st with
                        core :=
                          { st.core with
                            lit_mark := st3.core.lit_mark
                            wvec := st.core.wvec.set (2 * l.toNat + 1)
                              (BitVec.ofNat 32 (q.toNat - off))
                            wstk := st3.core.wstk
                            wusable := st3.core.wusable +
                              ((st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'(h2l_lt)).setWidth 64 +
                               (st.core.wvec[((l <<< (1 : BitVec 64)) + 1).toNat]'(
                                 h2l1_lt)).setWidth 64 - q)
                            num_binary := st3.core.num_binary }
                        scratch :=
                          { st.scratch with
                            work_stk1 := st3.scratch.work_stk1
                            work_stk2 := st3.scratch.work_stk2 } }
                    have hsp4 : FullSparseInvW c F0 F_cur st4 := by
                      refine rewriteBins_slice_preserves_fullSparse hsp (hcv ▸ hl_lt) hq_lo
                        (by change q.toNat ≤ off + sz; omega)
                        hcl3.wstk_len_arr hcl3.lit_mark_len hsl3.work_stk1_len hsl3.work_stk2_len
                        (fun x hx => by rw [hlm_eq3]; exact hlm_zero x hx)
                        (fun idx hidx => by
                          have hidx' : idx < q.toNat ∨ off + sz ≤ idx := by
                            rcases hidx with h1 | h2
                            · exact Or.inl (by omega)
                            · exact Or.inr (by omega)
                          rw [hwstk3 idx hidx']
                          exact hout1 idx hidx)
                        (wsRelocate (k := withWstk st.core st1.core.wstk)
                          (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _)
                          (fun _ r => r)
                          (fun idx hidx => by
                            dsimp only [withWstk]; exact hwstk3 (off + idx) (by left; omega))
                          hkept1)
                    have hwvec_eq4 :
                        st3.core.wvec.set ((l <<< (1 : BitVec 64)) + 1).toNat
                          (BitVec.setWidth 32 (q -
                            (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'(h2l_lt)).setWidth 64)) =
                        st.core.wvec.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - off)) := by
                      have hw3 : st3.core.wvec = st.core.wvec := hag3.get (·.core.wvec)
                      have hbv_eq : BitVec.setWidth 32 (q -
                          (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'(h2l_lt)).setWidth 64) =
                          BitVec.ofNat 32 (q.toNat - off) := by
                        apply BitVec.eq_of_toNat_eq
                        have hoff_s :
                            (BitVec.setWidth 64
                              (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'(
                                h2l_lt))).toNat = off := by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
                        have hsub :
                            (q - (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'(
                              h2l_lt)).setWidth 64).toNat = q.toNat - off := by
                          rw [BitVec.toNat_sub]; omega
                        rw [BitVec.toNat_setWidth, hsub, BitVec.toNat_ofNat]
                      rw [hw3, h2l1_eq, hbv_eq]
                    have hm4 : (FullMem c st4 ⋆ R) m := by
                      have heq_s :
                          ({ st3 with
                            core := { st3.core with
                              wvec := st3.core.wvec.set ((l <<< (1 : BitVec 64)) + 1).toNat
                                (BitVec.setWidth 32 (q -
                                  (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'(
                                    h2l_lt)).setWidth 64))
                              wusable := st3.core.wusable +
                                ((st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'(
                                   h2l_lt)).setWidth 64 +
                                 (st.core.wvec[((l <<< (1 : BitVec 64)) + 1).toNat]'(
                                   h2l1_lt)).setWidth 64 - q) } } : FullState) = st4 := by
                        rw [hwvec_eq4]; exact rewriteBins_st4_eq st st3 hag3 _ _
                      rw [← heq_s]; assumption
                    have hpa4 : ∀ k < pn.toNat,
                        (st4.scratch.work_stk1[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
                        (st4.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
                        (cnfOfClauses F_cur).EntailsClause
                          (cnfClause [(st4.scratch.work_stk1[k]?.getD 0#32).toNat,
                                      (st4.scratch.work_stk2[k]?.getD 0#32).toNat]) := by
                      intro k hk; dsimp only [st4]; rw [hw1_eq3, hw2_eq3]; exact hpa1 k hk
                    clear hkept1 hout1 hlm1 hpa1 hcl1 hsl1 hwsl1 hlml1 hrpl1 hws1l1 hws2l1
                      har1 harl1 hcv1 hrp1 hag1 hlen1 hcl2 hsl2 hwsl2 hlml2 hag2 hlen2 hlm2
                      hm2 hJ2 hlm_zero hcl3 hsl3 hag3 hlen3 hwstk3 hJ3
                    s_to_group
                    -- Inner Loop 4: `c = 0; while (c < pn) add unit or bin`
                    refine wp_loop_inv
                      (fun (ci4, ()) m5 =>
                        RewriteBinsInner4Inv c F0 F_cur s0 st st4 pn ci4 m5 R)
                      (fun (ci4, ()) _ => pn.toNat - ci4.toNat)
                      ?_ ?_
                    · intro J4 hJ4; s_steps
                      exact hJ4 (0#64, ()) _
                        ⟨st4, hsp4, hcv, hl0_st, hfl, hrepr, rfl, rfl, Nat.zero_le _, hm4⟩
                    · rintro J4 ⟨ci4, ⟨⟩⟩ m5
                        ⟨st5, hsp5, hcv5, hl05, hfl5, hrepr5, hw1_5, hw2_5, hci4_le, hm5⟩ hJ4
                      have hcl5 := hsp5.1.core_ok; have hsl5 := hsp5.1.scratch_ok
                      have hws1l5 := hsl5.work_stk1_len; have hws2l5 := hsl5.work_stk2_len
                      have hcv_le5 := hcl5.cur_vars_le
                      s_split
                      · have hci4_lt : ci4.toNat < pn.toNat := hc
                        have hci4_1 : (ci4 + 1#64).toNat = ci4.toNat + 1 := by
                          rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        obtain ⟨ha_lt, hb_lt, hab_ent⟩ := hpa4 ci4.toNat hci4_lt
                        have ha_get : st5.scratch.work_stk1[ci4.toNat]?.getD 0#32 =
                            st4.scratch.work_stk1[ci4.toNat]?.getD 0#32 := by rw [hw1_5]
                        have hb_get : st5.scratch.work_stk2[ci4.toNat]?.getD 0#32 =
                            st4.scratch.work_stk2[ci4.toNat]?.getD 0#32 := by rw [hw2_5]
                        have h1_get : st5.scratch.work_stk1[ci4.toNat]'(by omega) =
                            st5.scratch.work_stk1[ci4.toNat]?.getD 0#32 := by
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                        have h2_get : st5.scratch.work_stk2[ci4.toNat]'(by omega) =
                            st5.scratch.work_stk2[ci4.toNat]?.getD 0#32 := by
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                        have hpa_lt5 : (st5.scratch.work_stk1[ci4.toNat]'(by omega)).toNat <
                            2 * st5.core.cur_vars := by
                          rw [h1_get, ha_get, hcv5, ← hcv]; exact ha_lt
                        have hpb_lt5 : (st5.scratch.work_stk2[ci4.toNat]'(by omega)).toNat <
                            2 * st5.core.cur_vars := by
                          rw [h2_get, hb_get, hcv5, ← hcv]; exact hb_lt
                        have hab_ent5 : (cnfOfClauses F_cur).EntailsClause
                            (cnfClause [(st5.scratch.work_stk1[ci4.toNat]'(by omega)).toNat,
                                        (st5.scratch.work_stk2[ci4.toNat]'(by omega)).toNat]) := by
                          rw [h1_get, h2_get, ha_get, hb_get]; exact hab_ent
                        s_to_group
                        refine wp_join_group (ts := [])
                          (fun () m6 =>
                            RewriteBinsInner4Inv c F0 F_cur s0 st st4 pn (ci4 + 1#64) m6 R)
                          ?_ ?_
                        · rintro _ ⟨⟩ m6 h6
                          s_steps
                          exact hJ4 (ci4 + 1#64, ()) m6 (by dsimp only; omega) h6
                        · intro J4b hJ4b
                          s_split
                          · -- `pa[c] == pb[c]` -> `full_add_unit`
                            have heq_ab : st5.scratch.work_stk1[ci4.toNat]'(by omega) =
                                st5.scratch.work_stk2[ci4.toNat]'(by omega) := by assumption
                            s_steps
                            s_call hAddUnit
                            refine ⟨c, F0, F_cur, st5, R, rfl, hsp5.1, hsp5.2.1,
                              fun _ => entails_unit_of_dup (by simpa [heq_ab] using hab_ent5),
                              hm5, ?_⟩
                            intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl'
                              inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m6 st6 hlen6
                              hw6 hcl6 hfail6 _ hm6
                            have hsp6 : FullSparseInvW c F0 F_cur st6 :=
                              fullSparseInvW_afterAddUnit hsp5 hlen6 hw6
                            have hrepr6 : FullReprEquiv F_cur st6 := by
                              intro l' hl'; exact hrepr5 l' hl'
                            s_steps
                            · exact hJ4b () m6 ⟨st6, hsp6, hcv5, hcl6, hfl5, hrepr6,
                                hw1_5, hw2_5, by omega, hm6⟩
                            · exact hQ false st6 m6 hsp6 hcl6 hcv5 hfl5 hrepr6
                                (fun _ => (hfail6 hpa_lt5
                                  (by cases ok <;>
                                    first | rfl | contradiction | exact absurd rfl hc)).1)
                                hm6
                          · -- `pa[c] != pb[c]` -> `full_add_bin`
                            s_steps
                            s_call hAddBin
                            refine ⟨c, F0, F_cur, st5, R, rfl, hsp5.1, hsp5.2.1, hl05,
                              fun _ _ => hab_ent5, hm5, ?_⟩
                            intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk'
                              wlen' wu' nb' oom' inc' ph' ws' m6 st6 hlen6 hw6 _ hr20 _ hm6
                            have hsp6 : FullSparseInvW c F0 F_cur st6 :=
                              fullSparseInvW_afterAddBin hsp5 hlen6 hw6
                            have hrepr6 : FullReprEquiv F_cur st6 := by
                              intro l' hl'; exact hrepr5 l' hl'
                            s_steps
                            · exact hQ false st6 m6 hsp6 hl05 hcv5 hfl5 hrepr6
                                (fun _ => (hr20 (by assumption)).1) hm6
                            · exact hJ4b () m6 ⟨st6, hsp6, hcv5, hl05, hfl5, hrepr6,
                                hw1_5, hw2_5, by omega, hm6⟩
                      · -- Exit Inner Loop 4: advance `l = l + 1`
                        s_steps
                        exact hJ (l + 1#64, ()) m5 (by dsimp only; omega)
                          ⟨st5, hsp5, hcv5, hl05, hfl5, hrepr5, by omega, hm5⟩
    · -- Exit Outer Loop: return `true`
      s_steps
      exact hQ true st ml hsp hl0_st hcv hfl hrepr (fun h => by cases h) hml

end LeanQbe.T.Examples.Kissat.Full