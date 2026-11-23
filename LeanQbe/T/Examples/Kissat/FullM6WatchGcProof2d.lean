module

public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2c

/-!
# Kissat M6 Watch/GC Proofs Part 2d: Pure Arena Sweep & Reason Bridges

Pure arena compaction prefix, header bitfield, and `SweepReasonMapInv` bridge theorems
used by `full_arena_sweep_m6_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6WatchGc

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat.Full
open FullReduceSpecs FullReduceHelpers
open Kraken.Bedrock2.Test

/-! ## 1. Pure compaction prefix & reason-remapping bridges -/

theorem m6_refs_lt_compactPrefix {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {k : FullCoreState} {p : Nat} (hcmp : CompactPrefixOk c F_cur s k p)
    (hp_le : p ≤ k.arena_len) :
    ∀ r ∈ fullArenaClauseRefsCore k, r < p →
      r ∈ fullArenaClauseRefsCore { k with arena_len := p } := by
  intro r hr hrlt
  have hp_pos : 0 < p := by omega
  have hp3 : 3 ≤ p := hcmp.1.len_ok.elim (fun h0 => by dsimp at h0; omega) id
  have hnext := hcmp.1.arenaNextOff_extend (arena' := k.arena) (alen' := k.arena_len) hp_le
    (fun _ _ => rfl)
  have go : ∀ fuel pos, p - pos ≤ fuel → pos ≤ p →
      (pos = p ∨ (pos + 3 ≤ p ∧ pos ∈ fullArenaClauseRefsCore { k with arena_len := p })) →
      fullArenaScanRefs k.arena k.arena_len pos (fuel + (k.arena_len - p)) =
        fullArenaScanRefs k.arena p pos fuel ++
          fullArenaScanRefs k.arena k.arena_len p (k.arena_len - p) := by
    intro fuel
    induction fuel with
    | zero =>
      intro pos hf hle hpos
      have rfl_p : pos = p := by omega
      subst rfl_p; simp [fullArenaScanRefs]
    | succ f ih =>
      intro pos hf hle hpos
      rcases hpos with rfl | ⟨hp3_p, hmem⟩
      · have hnot : ¬ (pos + 3 ≤ pos) := by omega
        have h0 : fullArenaScanRefs k.arena pos pos (f + 1) = [] := by
          unfold fullArenaScanRefs; simp [hnot]
        rw [h0, List.nil_append]
        exact fullArenaScanRefs_fuel_ge (by omega) (Nat.le_refl _)
      · have hp_al : pos + 3 ≤ k.arena_len := by omega
        have hloc := hnext pos hmem
        have hwf := hcmp.1.refs_wf pos hmem
        have hb : fullArenaNextOff k.arena p pos ≤ p := by dsimp at hwf; exact hwf.2.2.2.1
        have hplus : f + 1 + (k.arena_len - p) = (f + (k.arena_len - p)) + 1 := by omega
        have hL : fullArenaScanRefs k.arena k.arena_len pos (f + 1 + (k.arena_len - p)) =
            pos :: fullArenaScanRefs k.arena k.arena_len (fullArenaNextOff k.arena p pos)
              (f + (k.arena_len - p)) := by
          rw [hplus, fullArenaScanRefs.eq_2]; simp [hp_al, hloc]
        have hR : fullArenaScanRefs k.arena p pos (f + 1) =
            pos :: fullArenaScanRefs k.arena p (fullArenaNextOff k.arena p pos) f := by
          rw [fullArenaScanRefs.eq_2]; simp [hp3_p]
        rw [hL, hR, List.cons_append]
        congr 1
        have hgt_nx := (fullArenaNextOff_bounds hp3_p (ar := k.arena)).1
        refine ih (fullArenaNextOff k.arena p pos) (by omega) hb ?_
        rcases fullArenaClauseRefs_next_or_end hcmp.1 hmem with he | hm
        · exact Or.inl he
        · exact Or.inr ⟨(hcmp.1.refs_wf _ hm).1, hm⟩
  have h0_mem : 0 ∈ fullArenaClauseRefsCore { k with arena_len := p } :=
    fullArenaClauseRefs_zero_mem hcmp.1 (by dsimp; omega)
  have hsp := go p 0 (Nat.le_refl _) (Nat.zero_le _) (Or.inr ⟨by omega, h0_mem⟩)
  unfold fullArenaClauseRefsCore at hr ⊢
  rw [fullArenaScanRefs_fuel_ge (f1 := k.arena_len) (f2 := p + (k.arena_len - p))
    (Nat.le_refl _) (by omega), hsp, List.mem_append] at hr
  rcases hr with hr_p | hr_tail
  · exact hr_p
  · exfalso; have := (fullArenaScanRefs_mem_bounds hr_tail).1; omega

theorem m6_refs_lt_prefix_transfer {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {k k' : FullCoreState} {start : Nat} (hcmp : CompactPrefixOk c F_cur s k start)
    (hcv : k'.cur_vars = k.cur_vars) (hl : k.arena.length = c.arena_cap)
    (hl' : k'.arena.length = c.arena_cap) (hs1 : start ≤ k.arena_len)
    (hs2 : start ≤ k'.arena_len) (hcap : start ≤ c.arena_cap)
    (hpre : PrefixAgrees start k.arena k'.arena) :
    CompactPrefixOk c F_cur s k' start ∧
    ∀ r ∈ fullArenaClauseRefsCore k, r < start → r ∈ fullArenaClauseRefsCore k' := by
  obtain ⟨hcmp', hcongr⟩ := arenaPrefix_preserves_compact hcmp hcv hl hl' hcap hpre
  refine ⟨hcmp', fun r hr hrlt => ?_⟩
  have h1 := m6_refs_lt_compactPrefix hcmp hs1 r hr hrlt
  rw [← hcongr.1] at h1
  exact (fullArenaClauseRefsCore_mono_prefix hs2 hcmp'.1 r h1).1

theorem m6_set_hdr_at_ref_preserves {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {k : FullCoreState} {cp dst : Nat} {newHdr : BitVec 32}
    (hcmp : CompactPrefixOk c F_cur s k dst) (har_len : k.arena.length = c.arena_cap)
    (hdst_cap : dst ≤ c.arena_cap)
    (hcp_mem : cp ∈ fullArenaClauseRefsCore { k with arena_len := dst })
    (hsh_v : (newHdr &&& 0x00800000#32) = 0#32)
    (hgb_v : (newHdr &&& 0x00080000#32) = 0#32) :
    let k' : FullCoreState := { k with arena := k.arena.set cp newHdr }
    CompactPrefixOk c F_cur s k' dst ∧
    fullArenaClauseRefsCore { k' with arena_len := dst } =
      fullArenaClauseRefsCore { k with arena_len := dst } ∧
    (∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaClauseSizeCore { k' with arena_len := dst } r =
        fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore { k' with arena_len := dst } r = false ∧
      fullArenaClauseLitsCore { k' with arena_len := dst } r =
        fullArenaClauseLitsCore { k with arena_len := dst } r) := by
  intro k'
  have har'_len : k'.arena.length = c.arena_cap := by simp [k', har_len]
  have hwf_cp :
      cp + 3 ≤ dst ∧ 3 ≤ (k.arena[cp + 2]?.getD 0#32).toNat ∧
      cp + 3 + (k.arena[cp + 2]?.getD 0#32).toNat ≤ fullArenaNextOff k.arena dst cp ∧
      fullArenaNextOff k.arena dst cp ≤ dst ∧
      (fullArenaNextOff k.arena dst cp = dst ∨
        fullArenaNextOff k.arena dst cp + 3 ≤ dst) :=
    hcmp.1.refs_wf cp hcp_mem
  have hcp_lt_ar : cp < k.arena.length := by omega
  have hsh0' : (k.arena[cp]?.getD 0#32 &&& 0x00800000#32) = 0#32 := (hcmp.2.1 cp hcp_mem).1
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaNextOff k'.arena dst r = fullArenaNextOff k.arena dst r := fun r hr => by
    by_cases hrc : r = cp
    · subst r
      have h0 : (k'.arena[cp]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
        dsimp only [k']; rw [List.getElem?_set_self hcp_lt_ar, Option.getD_some]; exact hsh_v
      have h2 : k'.arena[cp + 2]? = k.arena[cp + 2]? := List.getElem?_set_ne (by omega)
      unfold fullArenaNextOff
      simp [show ¬ (cp + 3 > dst) by omega, h2,
        show ¬ (cp + 3 + (k.arena[cp + 2]?.getD 0#32).toNat > dst) by omega,
        h0, hsh0']
    · have hwf :
          r + 3 ≤ dst ∧ 3 ≤ (k.arena[r + 2]?.getD 0#32).toNat ∧
          r + 3 + (k.arena[r + 2]?.getD 0#32).toNat ≤ fullArenaNextOff k.arena dst r ∧
          fullArenaNextOff k.arena dst r ≤ dst ∧
          (fullArenaNextOff k.arena dst r = dst ∨
            fullArenaNextOff k.arena dst r + 3 ≤ dst) :=
        hcmp.1.refs_wf r hr
      rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj : fullArenaNextOff k.arena dst r ≤ cp :=
          fullArenaScanRefs_disjoint hr hcp_mem hlt
        refine fullArenaNextOff_congr_block (List.getElem?_set_ne (by omega))
          (List.getElem?_set_ne (by omega)) (fun i hi1 hi2 => List.getElem?_set_ne (by omega))
      · have hdisj : fullArenaNextOff k.arena dst cp ≤ r :=
          fullArenaScanRefs_disjoint hcp_mem hr hgt
        have hnx_cp : fullArenaNextOff k.arena dst cp =
            cp + 3 + (k.arena[cp + 2]?.getD 0#32).toNat := by
          unfold fullArenaNextOff
          simp [show ¬ (cp + 3 > dst) by omega,
            show ¬ (cp + 3 + (k.arena[cp + 2]?.getD 0#32).toNat > dst) by omega, hsh0']
        rw [hnx_cp] at hdisj
        refine fullArenaNextOff_congr_block (List.getElem?_set_ne (by omega))
          (List.getElem?_set_ne (by omega)) (fun i hi1 hi2 => List.getElem?_set_ne (by omega))
  have hrefs : fullArenaClauseRefsCore { k' with arena_len := dst } =
      fullArenaClauseRefsCore { k with arena_len := dst } :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hcl : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      (fullArenaHdrCore { k' with arena_len := dst } r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseSizeCore { k' with arena_len := dst } r =
        fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore { k' with arena_len := dst } r = false ∧
      fullArenaClauseLitsCore { k' with arena_len := dst } r =
        fullArenaClauseLitsCore { k with arena_len := dst } r := fun r hr => by
    have hwf :
        r + 3 ≤ dst ∧ 3 ≤ (k.arena[r + 2]?.getD 0#32).toNat ∧
        r + 3 + (k.arena[r + 2]?.getD 0#32).toNat ≤ fullArenaNextOff k.arena dst r ∧
        fullArenaNextOff k.arena dst r ≤ dst ∧
        (fullArenaNextOff k.arena dst r = dst ∨
          fullArenaNextOff k.arena dst r + 3 ≤ dst) :=
      hcmp.1.refs_wf r hr
    have hszr : fullArenaClauseSizeCore { k' with arena_len := dst } r =
        fullArenaClauseSizeCore { k with arena_len := dst } r := by
      change ((k.arena.set cp newHdr)[r + 2]?.getD 0#32).toNat =
        (k.arena[r + 2]?.getD 0#32).toNat
      rw [List.getElem?_set_ne (by
        intro he
        rcases Nat.lt_or_gt_of_ne (show r ≠ cp by omega) with hlt | hgt
        · have hd : fullArenaNextOff k.arena dst r ≤ cp :=
            fullArenaScanRefs_disjoint hr hcp_mem hlt
          omega
        · have hd : fullArenaNextOff k.arena dst cp ≤ r :=
            fullArenaScanRefs_disjoint hcp_mem hr hgt
          omega)]
    have hdisj_body :
        ∀ j < (k.arena[r + 2]?.getD 0#32).toNat, r + 3 + j ≠ cp := by
      intro j hj heq
      by_cases hrc : r = cp
      · subst r; omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have hd : fullArenaNextOff k.arena dst r ≤ cp :=
            fullArenaScanRefs_disjoint hr hcp_mem hlt
          omega
        · have hd : fullArenaNextOff k.arena dst cp ≤ r :=
            fullArenaScanRefs_disjoint hcp_mem hr hgt
          omega
    have hlits : fullArenaClauseLitsCore { k' with arena_len := dst } r =
        fullArenaClauseLitsCore { k with arena_len := dst } r :=
      fullArenaClauseLitsCore_eq_of_hold
        (by change r + 3 + (k.arena[r + 2]?.getD 0#32).toNat ≤ k.arena.length; omega)
        (by change r + 3 + (k.arena[r + 2]?.getD 0#32).toNat ≤ (k.arena.set cp newHdr).length
            rw [List.length_set]; omega)
        hszr (fun j hj => by
          change (k.arena.set cp newHdr)[r + 3 + j]? = k.arena[r + 3 + j]?
          exact List.getElem?_set_ne (Ne.symm (hdisj_body j hj)))
    by_cases hrc : r = cp
    · subst r
      have hh0 :
          (fullArenaHdrCore { k' with arena_len := dst } cp &&& 0x00800000#32) = 0#32 := by
        change ((k.arena.set cp newHdr)[cp]?.getD 0#32 &&& 0x00800000#32) = 0#32
        rw [List.getElem?_set_self hcp_lt_ar, Option.getD_some]; exact hsh_v
      have hgb : fullArenaClauseGarbCore { k' with arena_len := dst } cp = false := by
        change (((k.arena.set cp newHdr)[cp]?.getD 0#32 &&& 0x00080000#32) != 0#32) = false
        rw [List.getElem?_set_self hcp_lt_ar, Option.getD_some]; simp [hgb_v]
      exact ⟨hh0, hszr, hgb, hlits⟩
    · have hh_eq : fullArenaHdrCore { k' with arena_len := dst } r =
          fullArenaHdrCore { k with arena_len := dst } r := by
        change (k.arena.set cp newHdr)[r]?.getD 0#32 = k.arena[r]?.getD 0#32
        rw [List.getElem?_set_ne (Ne.symm hrc)]
      refine ⟨hh_eq ▸ (hcmp.2.1 r hr).1, hszr, ?_, hlits⟩
      unfold fullArenaClauseGarbCore; rw [hh_eq]; exact (hcmp.2.1 r hr).2
  have hcmp' : CompactPrefixOk c F_cur s k' dst := by
    refine ⟨⟨hcmp.1.len_ok, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hcmp.1.refs_wf r hr; dsimp at hwf ⊢
      rw [hnxt r hr, (hcl r hr).2.1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr; exact absurd (hcl r hr).1 hsh
    · intro r hr hng l hl; rw [hrefs] at hr; rw [(hcl r hr).2.2.2] at hl
      exact hcmp.1.lits_lt r hr (hcmp.2.1 r hr).2 l hl
    · intro r hr hng; rw [hrefs] at hr; rw [(hcl r hr).2.2.2]
      exact hcmp.1.entails r hr (hcmp.2.1 r hr).2
    · intro r hr; rw [hrefs] at hr; exact ⟨(hcl r hr).1, (hcl r hr).2.2.1⟩
    · intro hs r hr; rw [hrefs] at hr; rw [(hcl r hr).2.2.2]; exact hcmp.2.2 hs r hr
  exact ⟨hcmp', hrefs, fun r hr => (hcl r hr).2⟩

theorem m6_set_hdr_preserves_srm {k k0 : FullCoreState} {cp dst nsrc : Nat}
    {newHdr : BitVec 32}
    (hrefs : fullArenaClauseRefsCore { { k with arena := k.arena.set cp newHdr } with
                                       arena_len := dst } =
      fullArenaClauseRefsCore { k with arena_len := dst })
    (hcl : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaClauseSizeCore { { k with arena := k.arena.set cp newHdr } with
                                arena_len := dst } r =
        fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore { { k with arena := k.arena.set cp newHdr } with
                                arena_len := dst } r = false ∧
      fullArenaClauseLitsCore { { k with arena := k.arena.set cp newHdr } with
                                arena_len := dst } r =
        fullArenaClauseLitsCore { k with arena_len := dst } r)
    (hrm : SweepReasonMapInv k0 k nsrc dst) :
    SweepReasonMapInv k0 { k with arena := k.arena.set cp newHdr } nsrc dst := by
  intro idx hidx; have h1 := hrm idx hidx; dsimp only at h1 ⊢
  split at h1
  · split; exact h1; contradiction
  · split
    · contradiction
    · split at h1
      · split
        · obtain ⟨ha, hb, hc, hd, he, _, hlits⟩ := h1
          exact ⟨ha, hb, hc, hd, hrefs ▸ he, (hcl _ he).2.1, (hcl _ he).2.2.trans hlits⟩
        · contradiction
      · split; contradiction; exact h1

theorem m6_sweep_copy_new_props {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s0 sL sC : FullState} {start : Nat} {src dst st : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hstart0 : s.core.cur_level = 0 → start = 0)
    (hltL : ∀ l < 2 * sL.core.cur_vars,
      WatchSliceLtOk start F_cur sL.core l (fullWatchOff sL l) (fullWatchSize sL l))
    (hlayL : WatchStackLayout sL.core)
    (hkeep_lt : 0 < s.core.cur_level →
      ∀ r ∈ fullArenaClauseRefsCore sL.core, r < start → r ∈ fullArenaClauseRefsCore sC.core)
    (hout : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz at_root st)
    (hdec : ∀ b : Bool, at_root = b ↔ (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hcvL : sL.core.cur_vars = s.core.cur_vars)
    (hcvC : sC.core.cur_vars = sL.core.cur_vars)
    (hsz3 : 3 ≤ old_sz.toNat) (harL_len : sL.core.arena.length = c.arena_cap)
    (harC_len : sC.core.arena.length = c.arena_cap)
    (hsrc_fit : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hdst_src : dst.toNat ≤ src.toNat)
    (hsrc_ref : src.toNat ∈ fullArenaClauseRefs s0)
    (hng_src : fullArenaClauseGarbCore s0.core src.toNat = false)
    (hsrc_lits : ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore s0.core src.toNat)
    (hlits_lt : ∀ j < old_sz.toNat,
      (sL.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hne_e : st ≠ 0xFFFFFFFE#64) (hne_d : st ≠ 0xFFFFFFFD#64)
    (hne_1 : st ≠ 1#64) (hne_f : st ≠ 0xFFFFFFFF#64) :
    3 ≤ st.toNat ∧ st.toNat ≤ old_sz.toNat ∧
    (∀ j < st.toNat, (sC.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)
      (fullArenaClauseLitsCore s0.core src.toNat) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)) ∧
    WatchStackLayout sC.core ∧
    ∀ l < 2 * sC.core.cur_vars,
      WatchSliceLtOk start F_cur sC.core l (fullWatchOff sC l) (fullWatchSize sC l) := by
  by_cases hcl0 : s.core.cur_level = 0
  · obtain ⟨_, hbinC, _, hcases, _, _, _, _, hge3⟩ := hout.2 ((hdec true).mpr hcl0)
    have hrange : 3 ≤ st.toNat ∧ st.toNat ≤ old_sz.toNat := by
      rcases hcases with h | h | h | h | h
      · exact absurd h hne_e
      · exact absurd h hne_d
      · exact absurd h hne_1
      · exact absurd h hne_f
      · exact h
    obtain ⟨hl, hs, he⟩ := hge3 hrange
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    exact ⟨hrange.1, hrange.2, fun j hj => hcvL ▸ hl j hj, by rwa [hsrc_lits] at hs, he,
      hbinC.layout, fun l hl => by
        rw [hstart0 hcl0]; exact WatchSliceLtOk.ofBinOnly (hbinC.slices l hl)⟩
  · have hpos : 0 < s.core.cur_level := Nat.pos_of_ne_zero hcl0
    obtain ⟨hst_eq, _, _, _, _, _, _, _, _, _, hwv, hws, hwl, _, _, _, _, _, hcp⟩ :=
      hout.1 ((hdec false).mpr hpos)
    have hst_nat : st.toNat = old_sz.toNat := by rw [hst_eq, zext_toNat _ (by decide)]
    have hcopy_eq : ((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat =
        fullArenaClauseLitsCore s0.core src.toNat := by
      rw [← hsrc_lits, hst_nat]; congr 1
      apply List.ext_getElem (by simp [harL_len, harC_len]; omega)
      intro j hj1 _; have hj : j < old_sz.toNat := by simp [harC_len] at hj1; omega
      simp only [List.getElem_take, List.getElem_drop]
      have h1 := hcp j hj
      rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < sC.core.arena.length),
        List.getElem?_eq_getElem (by omega : src.toNat + 3 + j < sL.core.arena.length)] at h1
      exact Option.some.inj h1
    have hlayC : WatchStackLayout sC.core := hlayL.with_wstk hcvC hwv hws hwl
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    exact ⟨by omega, by omega,
      fun j hj => by rw [hcp j (by omega)]; exact hlits_lt j (by omega),
      by rw [hcopy_eq]; exact List.Sublist.refl _,
      by rw [hcopy_eq]; exact hw0.arena.entails src.toNat hsrc_ref hng_src,
      hlayC, fun l hl => by
        rw [show fullWatchOff sC l = fullWatchOff sL l by
            unfold fullWatchOff fullWatchOffCore; rw [hwv],
          show fullWatchSize sC l = fullWatchSize sL l by
            unfold fullWatchSize fullWatchSizeCore; rw [hwv]]
        exact (hltL l (hcvC ▸ hl)).relocate hrefl (by omega) (hkeep_lt hpos)
          (fun _ _ => by rw [hws])⟩

abbrev SweepHappenedCore (k0 kL kn : FullCoreState) (dst src : Nat) : Prop :=
  fullArenaClauseRefsCore kn = fullArenaClauseRefsCore { kL with arena_len := dst } ++ [dst] ∧
  (∀ r ∈ fullArenaClauseRefsCore { kL with arena_len := dst },
    fullArenaClauseGarbCore kn r = fullArenaClauseGarbCore { kL with arena_len := dst } r ∧
    fullArenaClauseLitsCore kn r = fullArenaClauseLitsCore { kL with arena_len := dst } r) ∧
  fullArenaClauseGarbCore kn dst = false ∧
  fullArenaClauseLitsCore kn dst = fullArenaClauseLitsCore k0 src

theorem m6_write_hdr_wrap {c : FullCfg} {F_cur : List (List Nat)}
    {s s0 sL sC : FullState} {R : Mem 64 → Prop} {m : Mem 64} {dst : BitVec 64}
    {src st : Nat} {hdr0 : BitVec 32} (hcmpC : CompactPrefixOk c F_cur s sC.core dst.toNat)
    (hcongrC : CompactPrefixCongr sL.core sC.core dst.toNat)
    (hcv_eq : sC.core.cur_vars = s.core.cur_vars)
    (hnew3 : 3 ≤ st) (harC_len : sC.core.arena.length = c.arena_cap)
    (hfit : dst.toNat + 3 + st ≤ c.arena_cap)
    (hd1_eq : (dst + (1 : BitVec 64)).toNat = dst.toNat + 1)
    (hd2_eq : (dst + (2 : BitVec 64)).toNat = dst.toNat + 2)
    (hnsz32_eq : (BitVec.ofNat 32 st).toNat = st)
    (hsrc_ref : src ∈ fullArenaClauseRefs s0)
    (hng_src : fullArenaClauseGarbCore s0.core src = false)
    (hhdr_orig : hdr0 = fullArenaHdrCore s0.core src)
    (hnd_s0 : FullArenaVarsNodup s → FullArenaVarsNodup s0)
    (hnew_lt : ∀ j < st, (sC.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnew_sub : List.Sublist (((sC.core.arena.drop (dst.toNat + 3)).take st).map BitVec.toNat)
      (fullArenaClauseLitsCore s0.core src))
    (hnew_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((sC.core.arena.drop (dst.toNat + 3)).take st).map BitVec.toNat)))
    (hm_raw : (FullMem c
      { sC with core := { sC.core with arena := (((sC.core.arena.set dst.toNat
          (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32))).set
          (dst + (1 : BitVec 64)).toNat 2#32).set (dst + (2 : BitVec 64)).toNat
          (BitVec.ofNat 32 st)) } } ⋆ R) m) :
    ∃ arH : List (BitVec 32), arH.length = c.arena_cap ∧
      (∀ i < dst.toNat, arH[i]? = sC.core.arena[i]?) ∧
      (∀ j, dst.toNat + 3 ≤ j → arH[j]? = sC.core.arena[j]?) ∧
      arH[dst.toNat]? = some (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ∧
      (arH[dst.toNat + 2]?.getD 0#32).toNat = st ∧
      ((arH.drop (dst.toNat + 3)).take st).map BitVec.toNat =
        ((sC.core.arena.drop (dst.toNat + 3)).take st).map BitVec.toNat ∧
      CompactPrefixOk c F_cur s { sC.core with arena := arH } (dst.toNat + 3 + st) ∧
      dst.toNat ∈ fullArenaClauseRefsCore
        { sC.core with arena := arH, arena_len := dst.toNat + 3 + st } ∧
      (∀ rsns' : List (BitVec 32),
        fullArenaClauseLitsCore { sC.core with arena := arH, arena_len := dst.toNat + 3 + st }
          dst.toNat = fullArenaClauseLitsCore s0.core src →
        SweepHappenedCore s0.core sL.core
          { sL.core with arena := arH, rsns := rsns', arena_len := dst.toNat + 3 + st }
          dst.toNat src) ∧
      (FullMem c { sC with core := { sC.core with arena := arH } } ⋆ R) m := by
  let nhdr := hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)
  let arH := ((sC.core.arena.set dst.toNat nhdr).set
    (dst + (1 : BitVec 64)).toNat 2#32).set (dst + (2 : BitVec 64)).toNat (BitVec.ofNat 32 st)
  obtain ⟨haCmp_C, hnoC, hndC⟩ := hcmpC
  have harH_len : arH.length = c.arena_cap := by simp [arH, harC_len]
  have hpreH : PrefixAgrees dst.toNat sC.core.arena arH := fun idx hidx => by
    dsimp only [arH]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hbodyH : ∀ j, dst.toNat + 3 ≤ j → arH[j]? = sC.core.arena[j]? := fun j hj => by
    dsimp only [arH]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have harH_0 : arH[dst.toNat]? = some nhdr := by
    dsimp only [arH]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have hcl_bits := bv32_clear_shrk_rsn hdr0 (by
    have hng0 : (fullArenaHdrCore s0.core src &&& 0x00080000#32) = 0#32 := by
      unfold fullArenaClauseGarbCore at hng_src; simpa [bne_iff_ne] using hng_src
    rwa [hhdr_orig])
  have hnoshrkH : (arH[dst.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
    rw [harH_0, Option.getD_some]; exact hcl_bits.1
  have hnogarbH : (arH[dst.toNat]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
    rw [harH_0, Option.getD_some]; exact hcl_bits.2
  have hszH : (arH[dst.toNat + 2]?.getD 0#32).toNat = st := by
    dsimp only [arH]; rw [← hd2_eq, List.getElem?_set_self (by simp; omega), Option.getD_some,
      hnsz32_eq]
  have hdropH : ((arH.drop (dst.toNat + 3)).take st).map BitVec.toNat =
      ((sC.core.arena.drop (dst.toNat + 3)).take st).map BitVec.toNat := by
    congr 1; refine List.ext_getElem (by simp [harH_len, harC_len]) fun j hj1 _ => ?_
    have hj : j < st := by simp [harH_len] at hj1; omega
    simp only [List.getElem_take, List.getElem_drop]
    have h1 := hbodyH (dst.toNat + 3 + j) (by omega)
    rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < arH.length),
      List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < sC.core.arena.length)] at h1
    exact Option.some.inj h1
  obtain ⟨hrefsN, haN, holdN, hnoN⟩ := compactArena_append_block (k := sC.core)
    (k' := { sC.core with arena := arH }) (dst := dst.toNat) (new_sz := st) haCmp_C hnoC rfl hnew3
    harC_len harH_len hfit hpreH hnoshrkH hnogarbH hszH
    (fun j hj => by rw [hbodyH (dst.toNat + 3 + j) (by omega)]; rw [hcv_eq]; exact hnew_lt j hj)
    (by rw [hdropH]; exact hnew_ent)
  have hgarb_dst : fullArenaClauseGarbCore
      { sC.core with arena := arH, arena_len := dst.toNat + 3 + st } dst.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; simp [hnogarbH]
  refine ⟨arH, harH_len, hpreH, hbodyH, harH_0, hszH, hdropH, ⟨haN, hnoN, fun hnd r hr => ?_⟩,
    by rw [hrefsN, List.mem_append, List.mem_singleton]; exact Or.inr rfl,
    fun rsns' hlits_eq => ?_, hm_raw⟩
  · rw [hrefsN, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · rw [(holdN r hr).2.2]; exact hndC hnd r hr
    · unfold fullArenaClauseLitsCore
      rw [show fullArenaClauseSizeCore
            { sC.core with arena := arH, arena_len := dst.toNat + 3 + st } dst.toNat = st from
          hszH,
        hdropH]
      exact (hnew_sub.map (· / 2)).nodup (hnd_s0 hnd src hsrc_ref hng_src)
  · refine ⟨?_, fun r hr => ?_, hgarb_dst, hlits_eq⟩
    · change fullArenaClauseRefsCore
        { sC.core with arena := arH, arena_len := dst.toNat + 3 + st } = _
      rw [hrefsN, hcongrC.1]
    · exact ⟨(holdN r (hcongrC.1.symm ▸ hr)).2.1.trans (hcongrC.2 r hr).1,
        (holdN r (hcongrC.1.symm ▸ hr)).2.2.trans (hcongrC.2 r hr).2⟩

theorem m6_bv32_nhdr_bits (hdr0 : BitVec 32)
    (hng : (hdr0 &&& 0x00080000#32) = 0#32) :
    (((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32) &&& 0x00800000#32) =
      0#32 ∧
    (((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32) &&& 0x00080000#32) =
      0#32 ∧
    ((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00880000#32) = 0#32 ∧
    (((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32) &&& 0x00880000#32) =
      0#32 ∧
    ((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00400000#32) =
      (hdr0 &&& 0x00400000#32) ∧
    (((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32) &&& 0x00400000#32) =
      (hdr0 &&& 0x00400000#32) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
      show (~~~(0x00800000#32 ||| 0x00200000#32) &&& 0x00800000#32) = 0#32 from rfl,
      show (0x00200000#32 &&& 0x00800000#32) = 0#32 from rfl]
    simp
  · rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
      show (~~~(0x00800000#32 ||| 0x00200000#32) &&& 0x00080000#32) = 0x00080000#32 from rfl,
      show (0x00200000#32 &&& 0x00080000#32) = 0#32 from rfl]
    simp [hng]
  · rw [BitVec.and_assoc,
      show (~~~(0x00800000#32 ||| 0x00200000#32) &&& 0x00880000#32) = 0x00080000#32 from rfl]
    exact hng
  · rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
      show (~~~(0x00800000#32 ||| 0x00200000#32) &&& 0x00880000#32) = 0x00080000#32 from rfl,
      show (0x00200000#32 &&& 0x00880000#32) = 0#32 from rfl]
    simp [hng]
  · rw [BitVec.and_assoc,
      show (~~~(0x00800000#32 ||| 0x00200000#32) &&& 0x00400000#32) = 0x00400000#32 from rfl]
  · rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
      show (~~~(0x00800000#32 ||| 0x00200000#32) &&& 0x00400000#32) = 0x00400000#32 from rfl,
      show (0x00200000#32 &&& 0x00400000#32) = 0#32 from rfl]
    simp

theorem m6_sweep_rsn_unmarked_pos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sL sC : FullState} {arH : List (BitVec 32)} {src dst nsrc st start : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hstart : start ≤ src)
    (hrmk0 : ∀ idx < s0.core.trail_end,
      let v := (s0.core.trl[idx]?.getD 0#32).toNat / 2
      let rsn := s0.core.rsns[v]?.getD 0xFFFFFFFF#32
      0 < (s0.core.lvl[v]?.getD 0#32).toNat →
      (rsn &&& 0x80000000#32) = 0#32 → start ≤ rsn.toNat →
      (fullArenaHdr s0 rsn.toNat &&& 0x00200000#32) ≠ 0#32)
    (hsrc_ref : src ∈ fullArenaClauseRefs s0)
    (hnsrc64 : nsrc = fullArenaNextOff s0.core.arena s0.core.arena_len src)
    (hdst_src : dst ≤ src) (hsrc_lt8 : src < 0x80000000)
    (hrmL : SweepReasonMapInv s0.core sL.core src dst)
    (hhapp : SweepHappenedCore s0.core sL.core
      { sL.core with arena := arH, rsns := sC.core.rsns, arena_len := dst + 3 + st } dst src)
    (hrC : sC.core.rsns = sL.core.rsns)
    (h0 : (fullArenaHdrCore s0.core src &&& 0x00200000#32) = 0#32) :
    SweepReasonMapInv s0.core { sC.core with arena := arH, rsns := sC.core.rsns }
      nsrc (dst + 3 + st) := by
  refine SweepReasonMapInv.congr_rsns_arena rfl rfl
    (SweepReasonMapInv.keep_step (kL := sL.core) hw0 hsrc_ref hnsrc64 hdst_src hsrc_lt8 hrmL hhapp
      (fun _ _ _ => by rw [hrC]) (fun idx hidx heq_s => ?_))
  exfalso
  have hne_s : BitVec.ofNat 32 src ≠ 0xFFFFFFFF#32 := fun h => by
    have := congrArg BitVec.toNat h; rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
  have hlg_s : (BitVec.ofNat 32 src &&& 0x80000000#32) = 0#32 :=
    (bv32_lt_highbit_iff _).mp (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8)
  have hlvl_pos : 0 < (s0.core.lvl[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
    Classical.byContradiction fun h0' => by
      have := hw0.level0_rsn_none idx hidx (by omega); rw [heq_s] at this; exact hne_s this
  have hmk := hrmk0 idx hidx hlvl_pos (heq_s ▸ hlg_s)
    (by rw [heq_s, bv32_ofNat_toNat (by omega)]; exact hstart)
  rw [heq_s, bv32_ofNat_toNat (by omega)] at hmk; exact hmk h0

theorem m6_rsn_ne_dst_of_not_src_val {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL : FullCoreState} {src dst idx : Nat}
    (_hw0 : FullWitnessInv c F0 F_cur k0) (hds : dst ≤ src) (hdst_lt8 : dst < 0x80000000)
    (hrmL : SweepReasonMapInv k0 kL src dst)
    (hnot : k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ BitVec.ofNat 32 src)
    (_hsrc_lt8 : src < 0x80000000) (hidx : idx < k0.trail_end) :
    (kL.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≠ dst := by
  intro heq
  have hL := hrmL idx hidx; dsimp only at hL
  let v := (k0.trl[idx]?.getD 0#32).toNat / 2
  let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
  change (if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _) at hL
  split at hL
  · rename_i hc1; rw [hL] at heq
    rcases hc1 with hff | hhi
    · change r0.toNat = dst at heq; rw [hff] at heq; simp at heq; omega
    · exact hhi ((bv32_lt_highbit_iff _).mp
        (by change r0.toNat < 0x80000000; dsimp only [r0, v] at *; omega))
  · split at hL
    · omega
    · rename_i hge
      rw [hL] at heq
      apply hnot; apply BitVec.eq_of_toNat_eq
      rw [bv32_ofNat_toNat (by omega)]
      change ¬ r0.toNat < src at hge; dsimp only [r0, v] at *; omega

theorem m6_rsn_not_src_of_miss {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL kC : FullCoreState} {arH : List (BitVec 32)} {src dst st idx : Nat}
    (hw0 : FullWitnessInv c F0 F_cur k0)
    (hrmL : SweepReasonMapInv k0 kL src dst) (hvC : kC.vals = k0.vals)
    (hrC : kC.rsns = kL.rsns) (hszH : (arH[dst + 2]?.getD 0#32).toNat = st)
    (hfit : dst + 3 + st ≤ arH.length) (hsrc_lt8 : src < 0x80000000)
    (hlits_eq : fullArenaClauseLitsCore { kC with arena := arH, arena_len := dst + 3 + st }
      dst = fullArenaClauseLitsCore k0 src)
    (hmiss : ∀ j < st,
      let lit := arH[dst + 3 + j]?.getD 0#32
      ¬ (lit.toNat / 2 < k0.cur_vars ∧
         (0#32).slt ((kC.vals[lit.toNat]?.getD 0#8).signExtend 32) = true ∧
         kC.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src))
    (hidx : idx < k0.trail_end) :
    k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ BitVec.ofNat 32 src := by
  intro heq_s
  have hne_s : BitVec.ofNat 32 src ≠ 0xFFFFFFFF#32 := fun h => by
    have := congrArg BitVec.toNat h
    rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
  have hlg_s : (BitVec.ofNat 32 src &&& 0x80000000#32) = 0#32 :=
    (bv32_lt_highbit_iff _).mp (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8)
  have hmem := hw0.reason_lit_mem idx hidx (heq_s ▸ hne_s) (heq_s ▸ hlg_s)
  rw [heq_s, bv32_ofNat_toNat (by omega), ← hlits_eq] at hmem
  have hbd : dst + 3 + fullArenaClauseSizeCore
      { kC with arena := arH, arena_len := dst + 3 + st } dst ≤ arH.length := by
    rw [show fullArenaClauseSizeCore { kC with arena := arH, arena_len := dst + 3 + st } dst =
      st from hszH]; omega
  obtain ⟨j, hj, hjeq⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hmem
  rw [show fullArenaClauseSizeCore { kC with arena := arH, arena_len := dst + 3 + st } dst =
    st from hszH] at hj
  have hlt_tl := hw0.trail_lits_lt idx hidx
  have hval1 : k0.vals[(k0.trl[idx]?.getD 0#32).toNat]?.getD 0#8 = 1#8 :=
    (hw0.vals_true_iff _ hlt_tl).mpr ⟨idx, hidx, rfl⟩
  have hlit_j : (arH[dst + 3 + j]?.getD 0#32).toNat = (k0.trl[idx]?.getD 0#32).toNat := by
    rw [List.getElem?_eq_getElem (by omega : dst + 3 + j < arH.length), Option.getD_some]
    exact hjeq
  have hrsn_j : kC.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src := by
    have hrm_i := hrmL idx hidx; dsimp only at hrm_i; rw [heq_s] at hrm_i
    split at hrm_i
    · rename_i hbad; exact absurd hbad (fun hc => hc.elim hne_s (fun h => h hlg_s))
    · split at hrm_i
      · rename_i hlt; rw [bv32_ofNat_toNat (by omega)] at hlt; omega
      · rw [hrC, hrm_i]
  exact hmiss j hj ⟨by rw [hlit_j]; omega, by rw [hlit_j, hvC, hval1]; decide,
    by rw [hlit_j]; exact hrsn_j⟩

theorem m6_rsn_not_src_of_unmarked {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src start idx : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hstart : start ≤ src)
    (hrmk0 : ∀ idx < s0.core.trail_end,
      let v := (s0.core.trl[idx]?.getD 0#32).toNat / 2
      let rsn := s0.core.rsns[v]?.getD 0xFFFFFFFF#32
      0 < (s0.core.lvl[v]?.getD 0#32).toNat →
      (rsn &&& 0x80000000#32) = 0#32 → start ≤ rsn.toNat →
      (fullArenaHdr s0 rsn.toNat &&& 0x00200000#32) ≠ 0#32)
    (hsrc_lt8 : src < 0x80000000)
    (h0 : (fullArenaHdrCore s0.core src &&& 0x00200000#32) = 0#32)
    (hidx : idx < s0.core.trail_end) :
    s0.core.rsns[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      BitVec.ofNat 32 src := by
  intro heq_s
  have hne_s : BitVec.ofNat 32 src ≠ 0xFFFFFFFF#32 := fun h => by
    have := congrArg BitVec.toNat h
    rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
  have hlg_s : (BitVec.ofNat 32 src &&& 0x80000000#32) = 0#32 :=
    (bv32_lt_highbit_iff _).mp (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8)
  have hlvl_pos : 0 < (s0.core.lvl[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
    Classical.byContradiction fun h0' => by
      have := hw0.level0_rsn_none idx hidx (by omega); rw [heq_s] at this; exact hne_s this
  have hmk := hrmk0 idx hidx hlvl_pos (heq_s ▸ hlg_s)
    (by rw [heq_s, bv32_ofNat_toNat (by omega)]; exact hstart)
  rw [heq_s, bv32_ofNat_toNat (by omega)] at hmk; exact hmk h0

theorem m6_rsn_eq_lit_of_hit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL kC : FullCoreState} {litI : BitVec 32} {src dst idx : Nat}
    (hw0 : FullWitnessInv c F0 F_cur k0) (hds : dst ≤ src) (hsrc_lt8 : src < 0x80000000)
    (hrmL : SweepReasonMapInv k0 kL src dst) (hrC : kC.rsns = kL.rsns)
    (hvC : kC.vals = k0.vals) (_hrsns_len : kC.rsns.length = c.max_vars)
    (_hcv_le : k0.cur_vars ≤ c.max_vars) (hlitI_lt : litI.toNat < 2 * k0.cur_vars)
    (hlitI_v : litI.toNat < kC.vals.length)
    (hvg : (0#32).slt ((kC.vals[litI.toNat]'hlitI_v).signExtend 32) = true)
    (hrsn_eq : (kC.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = src)
    (hidx : idx < k0.trail_end)
    (heq : ((kC.rsns.set (litI.toNat / 2) ((BitVec.ofNat 64 dst).setWidth 32))[
      (k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = dst) :
    (k0.trl[idx]?.getD 0#32).toNat / 2 = litI.toNat / 2 ∧
    kC.vals[litI.toNat]?.getD 0#8 = 1#8 := by
  have hv1 : k0.vals[litI.toNat]?.getD 0#8 = 1#8 := by
    have hdom := hw0.vals_domain litI.toNat hlitI_lt
    have hg : kC.vals[litI.toNat]?.getD 0#8 = kC.vals[litI.toNat]'hlitI_v := by
      rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some]
    have h1 : (0#32).slt ((kC.vals[litI.toNat]?.getD 0#8).signExtend 32) = true := by rwa [hg]
    rw [hvC] at h1; exact (bv8_gt0_of_dom hdom).1.mp h1
  have hvalC : kC.vals[litI.toNat]?.getD 0#8 = 1#8 := hvC ▸ hv1
  by_cases hve : (k0.trl[idx]?.getD 0#32).toNat / 2 = litI.toNat / 2
  · exact ⟨hve, hvalC⟩
  · exfalso
    rw [List.getElem?_set_ne (Ne.symm hve), hrC] at heq
    obtain ⟨idx0, hidx0, hieq0⟩ := (hw0.vals_true_iff litI.toNat hlitI_lt).mp hv1
    have hr_src_L : kL.rsns[(k0.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        BitVec.ofNat 32 src := by
      apply BitVec.eq_of_toNat_eq
      rw [bv32_ofNat_toNat (by omega), hieq0, ← hrC]; exact hrsn_eq
    have hr0_src : k0.rsns[(k0.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        BitVec.ofNat 32 src := by
      have hm0' := hrmL idx0 hidx0; dsimp only at hm0'
      split at hm0'
      · rename_i hc1; rw [hr_src_L] at hm0'
        rcases hc1 with hff | hhi
        · rw [hff] at hm0'; have := congrArg BitVec.toNat hm0'
          rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
        · rw [← hm0'] at hhi
          exact absurd ((bv32_lt_highbit_iff _).mp
            (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8)) hhi
      · split at hm0'
        · rw [hr_src_L] at hm0'; have := hm0'.1
          rw [bv32_ofNat_toNat (by omega)] at this; omega
        · rw [hr_src_L] at hm0'; exact hm0'.symm
    have hnot : k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
        BitVec.ofNat 32 src := fun h => by
      have hid_eq := fullWitness_reason_unique hw0 hidx hidx0 hsrc_lt8 h hr0_src
      subst hid_eq; exact hve (congrArg (· / 2) hieq0)
    exact m6_rsn_ne_dst_of_not_src_val hw0 hds (by omega) hrmL hnot hsrc_lt8 hidx heq


/-! ## 1. Sweep state framing & pure bridge helpers (`private`) -/

inductive M6SweepLike (s s' : FullState) : Prop where
  | mk (vals' : List (BitVec 8)) (flags' lvl' rsns' trl' tp' : List (BitVec 32))
      (te' : Nat) (unass' unfl' : BitVec 64) (wvec' wstk' arena' : List (BitVec 32))
      (wlen' : Nat) (wu' nb' oom' : BitVec 64) (ph' : List (BitVec 8)) (ws' : List (BitVec 32))
      (hEq : s' =
        { core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
              wvec := wvec', wstk := wstk', arena := arena', wlen := wlen', wusable := wu',
              num_binary := nb', oom := oom' }
          scratch := { s.scratch with phases := ph', wsort := ws' } }) :
      M6SweepLike s s'

theorem M6SweepLike.of_copy {s sL : FullState} (h : M6SweepLike s sL)
    {arC : List (BitVec 32)} {valsC : List (BitVec 8)}
    {flagsC lvlC rsnsC trlC tpC : List (BitVec 32)} {teC : Nat} {unassC unflC : BitVec 64}
    {wvecC wstkC : List (BitVec 32)} {wlenC : Nat} {wuC nbC oomC : BitVec 64}
    {phC : List (BitVec 8)} {wsC : List (BitVec 32)} :
    M6SweepLike s
      { core := { sL.core with arena := arC, vals := valsC, flags := flagsC, lvl := lvlC,
                               rsns := rsnsC, trl := trlC, trail_pos := tpC, trail_end := teC,
                               unassigned := unassC, unflushed := unflC, wvec := wvecC,
                               wstk := wstkC, wlen := wlenC, wusable := wuC, num_binary := nbC,
                               oom := oomC }
        scratch := { sL.scratch with phases := phC, wsort := wsC } } := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  exact ⟨valsC, flagsC, lvlC, rsnsC, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, arC, wlenC,
    wuC, nbC, oomC, phC, wsC, rfl⟩

theorem m6_binOnlySlice_of_full {F_cur : List (List Nat)} {k : FullCoreState}
    (hwlen : k.wlen ≤ k.wstk.length) (hbin : FullBinOnlyWatchesInv F_cur k)
    {l : Nat} (hl : l < 2 * k.cur_vars) :
    BinOnlyWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  have hb := Nat.le_trans (hbin.1.bounds l hl) hwlen
  suffices h : ∀ rem idx, idx + rem = fullWatchSizeCore k l →
      BinOnlyWatchSliceOk F_cur k l (fullWatchOffCore k l + idx) rem from
    by simpa using h (fullWatchSizeCore k l) 0 (Nat.zero_add _)
  intro rem; induction rem with
  | zero => intro _ _; exact .empty
  | succ rem ih =>
    intro idx heq
    have hlt_sz : idx < fullWatchSizeCore k l := by omega
    have hlt_len : fullWatchOffCore k l + idx < k.wstk.length := by omega
    obtain ⟨hf, hltv, hent⟩ := hbin.2 l hl idx hlt_sz
    have hget : k.wstk[fullWatchOffCore k l + idx]? =
        some (k.wstk[fullWatchOffCore k l + idx]'hlt_len) := List.getElem?_eq_getElem hlt_len
    simp only [hget, Option.getD_some] at hf hltv hent
    have hne : k.wstk[fullWatchOffCore k l + idx]'hlt_len ≠ 0xFFFFFFFF#32 := fun hsq =>
      hbin.1.no_sentinel l hl idx hlt_sz (by rw [hget, hsq])
    exact .bin hget hf hne hltv hent
      (by rw [Nat.add_assoc]; exact ih (idx + 1) (by omega))

theorem m6_binOnly_of_full {F_cur : List (List Nat)} {k : FullCoreState}
    (hwlen : k.wlen ≤ k.wstk.length) (hbin : FullBinOnlyWatchesInv F_cur k) :
    BinOnlyWatchesInv F_cur k :=
  ⟨hbin.1, fun _ hl => m6_binOnlySlice_of_full hwlen hbin hl⟩

theorem M6SweepLike.of_ar_rsns {s sC : FullState} (h : M6SweepLike s sC)
    {arH rsnsR : List (BitVec 32)} :
    M6SweepLike s { sC with core := { sC.core with arena := arH, rsns := rsnsR } } := by
  rcases h with ⟨valsC, flagsC, lvlC, _, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, _,
    wlenC, wuC, nbC, oomC, phC, wsC, rfl⟩
  exact ⟨valsC, flagsC, lvlC, rsnsR, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, arH, wlenC,
    wuC, nbC, oomC, phC, wsC, rfl⟩

theorem M6SweepLike.unchanged {s s' : FullState} (h : M6SweepLike s s') :
    s'.core.cur_vars = s.core.cur_vars ∧ s'.core.arena_len = s.core.arena_len ∧
    s'.core.cur_level = s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode ∧
    s'.core.frame_trail = s.core.frame_trail ∧ s'.core.frame_dec = s.core.frame_dec ∧
    s'.core.inconsistent = s.core.inconsistent ∧
    s'.scratch.extend_len = s.scratch.extend_len ∧ s'.scratch.work_stk2 = s.scratch.work_stk2 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure M6SweepLoopRootOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) (start dst : Nat) (new_unit : Bool) : Prop where
  get : s.core.cur_level = 0 →
    start = 0 ∧
    FullWitnessInv c F0 F_cur { sL.core with arena_len := dst } ∧
    s.core.trail_end ≤ sL.core.trail_end ∧
    (new_unit = true → s.core.trail_end < sL.core.trail_end)

structure M6SweepLoopPosOk (s sPre sL : FullState) (src dst : Nat) (new_unit : Bool) :
    Prop where
  get : 0 < s.core.cur_level →
    new_unit = false ∧ sL.core.vals = s.core.vals ∧ sL.core.lvl = s.core.lvl ∧
    sL.core.trl = s.core.trl ∧ sL.core.trail_pos = s.core.trail_pos ∧
    sL.core.trail_end = s.core.trail_end ∧
    SweepReasonMapInv sPre.core sL.core src dst

/-! ## 2. Join & loop invariants for `full_arena_sweep_m6_wp` (`private`) -/

inductive PreSweepClrInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (fp : Nat)
    (cp : BitVec 64) (mL : Mem 64) : Prop where
  | mk
      (hcp_le : cp.toNat ≤ fp)
      (hdone : CleanIrredChain s.core.arena 0 cp.toNat)
      (hrem : CleanIrredChain s.core.arena cp.toNat fp)
      (hcp_in : cp.toNat < fp →
        cp.toNat ∈ fullArenaClauseRefsCore { s.core with arena_len := fp })
      (arL : List (BitVec 32))
      (harL_l : arL.length = c.arena_cap)
      (htailL : ∀ i, cp.toNat ≤ i → i < s.core.arena_len → arL[i]? = s.core.arena[i]?)
      (hmatchL : ∀ r ∈ fullArenaClauseRefsCore { s.core with arena_len := fp },
        r < cp.toNat →
        (arL[r]?.getD 0#32 &&& 0x00C80000#32) = 0#32 ∧ arL[r + 2]? = s.core.arena[r + 2]? ∧
        ∀ j < (s.core.arena[r + 2]?.getD 0#32).toNat, arL[r + 3 + j]? = s.core.arena[r + 3 + j]?)
      (hmL : (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL) :
      PreSweepClrInv c s R fp cp mL

structure M6ReasonMarkRange (sPre sL : FullState) (first_red dst : Nat) : Prop where
  get : 0 < sPre.core.cur_level → ∀ r, RefInChain sL.core.arena first_red dst r →
    ∀ idx < sPre.core.trail_end,
      (sL.core.rsns[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32).toNat = r →
      (sL.core.arena[r]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
      ∃ j < (sL.core.arena[r + 2]?.getD 0#32).toNat,
        let lit := (sL.core.arena[r + 3 + j]?.getD 0#32).toNat
        lit / 2 = (sPre.core.trl[idx]?.getD 0#32).toNat / 2 ∧
        sL.core.vals[lit]?.getD 0#8 = 1#8

inductive M6FirstRedOk (c : FullCfg) (F_cur : List (List Nat)) (s sPre sL : FullState)
    (start dst rwL : Nat) (first_red : BitVec 64) : Prop where
  | inl (heq : first_red = 0xFFFFFFFF#64) :
      M6FirstRedOk c F_cur s sPre sL start dst rwL first_red
  | inr (h : start ≤ first_red.toNat ∧ first_red.toNat < dst ∧
      CompactPrefixOk c F_cur s sL.core first_red.toNat ∧
      0 < rwL ∧ MoveRangeChain sL.core.arena first_red.toNat dst rwL ∧
      first_red.toNat ∈ fullArenaClauseRefsCore { sL.core with arena_len := dst } ∧
      M6ReasonMarkRange sPre sL first_red.toNat dst) :
      M6FirstRedOk c F_cur s sPre sL start dst rwL first_red

inductive M6SweepLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sPre : FullState) (R : Mem 64 → Prop) (start : Nat)
    (src dst first_red : BitVec 64) (has_iar new_unit : Bool) (mL : Mem 64) : Prop where
  | mk
      (hst_dst : start ≤ dst.toNat)
      (hdst_src : dst.toNat ≤ src.toNat)
      (hsrc_le : src.toNat ≤ s.core.arena_len)
      (hsrc_mem : src.toNat < s.core.arena_len → src.toNat ∈ fullArenaClauseRefs sPre)
      (hhas_iar : has_iar = true → first_red ≠ 0xFFFFFFFF#64)
      (sL : FullState)
      (rwL : Nat)
      (hlikeL : M6SweepLike s sL)
      (hlenL : sL.LengthsOk c)
      (hcmpL : CompactPrefixOk c F_cur s sL.core dst.toNat)
      (hcmpL_st : CompactPrefixOk c F_cur s sL.core start)
      (hlayL : WatchStackLayout sL.core)
      (hltL : ∀ l < 2 * sL.core.cur_vars,
        WatchSliceLtOk start F_cur sL.core l (fullWatchOff sL l) (fullWatchSize sL l))
      (hstL_in : start < dst.toNat →
        start ∈ fullArenaClauseRefsCore { sL.core with arena_len := dst.toNat })
      (hfrL : M6FirstRedOk c F_cur s sPre sL start dst.toNat rwL first_red)
      (htailL : ∀ i, src.toNat ≤ i → i < s.core.arena_len →
        sL.core.arena[i]? = sPre.core.arena[i]?)
      (hrootL : M6SweepLoopRootOk c F0 F_cur s sL start dst.toNat new_unit)
      (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
      (hmL : (FullMem c sL ⋆ R) mL) :
      M6SweepLoopInv c F0 F_cur s sPre R start src dst first_red has_iar new_unit mL

theorem m6_trivial_post_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {dst : Nat} {fr : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur { k with arena_len := dst }) :
    FullWitnessInv c F0 F_cur { { k with first_reducible := fr } with arena_len := dst } :=
  { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound,
    arena :=
      { len_ok := hw.arena.len_ok, refs_wf := hw.arena.refs_wf, shrk_term := hw.arena.shrk_term,
        lits_lt := hw.arena.lits_lt, entails := hw.arena.entails },
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr),
    cur_level_le := hw.cur_level_le, trail_lits_lt := hw.trail_lits_lt,
    trail_vars_nodup := hw.trail_vars_nodup, vals_domain := hw.vals_domain,
    vals_true_iff := hw.vals_true_iff, vals_false_iff := hw.vals_false_iff, lvl_le := hw.lvl_le,
    dec_earliest := hw.dec_earliest, levels_inhabited := hw.levels_inhabited,
    level0_sound := hw.level0_sound, trail_pos_inv := hw.trail_pos_inv,
    level0_rsn_none := hw.level0_rsn_none, frame_trail_lt := hw.frame_trail_lt,
    frame_trail_mono := hw.frame_trail_mono, frame_trail_before_lt := hw.frame_trail_before_lt,
    frame_dec_lt := hw.frame_dec_lt, reason_inv := hw.reason_inv,
    reason_lit_mem := hw.reason_lit_mem }

inductive M6PostLike (s sM : FullState) : Prop where
  | mk (v : List (BitVec 8)) (f l r t tp : List (BitVec 32)) (te : Nat) (u uf : BitVec 64)
      (wv ws ar : List (BitVec 32)) (wl : Nat) (wu fr nb o : BitVec 64)
      (hEq : sM.core =
        { s.core with
          vals := v, flags := f, lvl := l, rsns := r, trl := t, trail_pos := tp, trail_end := te,
          unassigned := u, unflushed := uf, wvec := wv, wstk := ws, arena := ar, wlen := wl,
          wusable := wu, first_reducible := fr, num_binary := nb, oom := o }) :
      M6PostLike s sM

theorem m6_core_lengths_upd {c : FullCfg} {k : FullCoreState} (h : k.LengthsOk c)
    {al : Nat} (hal : al ≤ c.arena_cap) (ag fr ni nr : BitVec 64) :
    FullCoreState.LengthsOk c
      { k with
        arena_len := al, arena_garbage := ag, first_reducible := fr, num_irred := ni,
        num_redundant := nr } := by
  cases h; constructor <;> (try exact hal) <;> assumption

theorem m6_witness_upd_stats {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (ag ni nr : BitVec 64) :
    FullWitnessInv c F0 F_cur
      { k with arena_garbage := ag, num_irred := ni, num_redundant := nr } :=
  { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound,
    arena :=
      { len_ok := hw.arena.len_ok, refs_wf := hw.arena.refs_wf, shrk_term := hw.arena.shrk_term,
        lits_lt := hw.arena.lits_lt, entails := hw.arena.entails },
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr),
    cur_level_le := hw.cur_level_le, trail_lits_lt := hw.trail_lits_lt,
    trail_vars_nodup := hw.trail_vars_nodup, vals_domain := hw.vals_domain,
    vals_true_iff := hw.vals_true_iff, vals_false_iff := hw.vals_false_iff, lvl_le := hw.lvl_le,
    dec_earliest := hw.dec_earliest, levels_inhabited := hw.levels_inhabited,
    level0_sound := hw.level0_sound, trail_pos_inv := hw.trail_pos_inv,
    level0_rsn_none := hw.level0_rsn_none, frame_trail_lt := hw.frame_trail_lt,
    frame_trail_mono := hw.frame_trail_mono, frame_trail_before_lt := hw.frame_trail_before_lt,
    frame_dec_lt := hw.frame_dec_lt, reason_inv := hw.reason_inv,
    reason_lit_mem := hw.reason_lit_mem }

theorem m6_start_in_post_move {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {kE kM : FullCoreState} {start fr dst : Nat}
    (hcmpE_fr : CompactPrefixOk c F_cur s kE fr) (harE : kE.arena.length = c.arena_cap)
    (harM : kM.arena.length = c.arena_cap) (hcv : kM.cur_vars = kE.cur_vars)
    (hdst_cap : dst ≤ c.arena_cap) (hfr_lt : fr < dst) (hfr_st : start ≤ fr)
    (hpre : PrefixAgrees fr kE.arena kM.arena)
    (hstE : start < dst → start ∈ fullArenaClauseRefsCore { kE with arena_len := dst })
    (hfrM : fr ∈ fullArenaClauseRefsCore { kM with arena_len := dst }) :
    start < dst → start ∈ fullArenaClauseRefsCore { kM with arena_len := dst } := fun hst_lt => by
  have hcmp' : CompactPrefixOk c F_cur s { kE with arena_len := dst } fr :=
    (arenaPrefix_preserves_compact (k := kE) (k' := { kE with arena_len := dst }) hcmpE_fr rfl
      harE harE (by omega) (fun _ _ => rfl)).1
  rcases Nat.eq_or_lt_of_le hfr_st with heq | hlt
  · rw [heq]; exact hfrM
  · have hst_e := m6_refs_lt_compactPrefix hcmp' (by dsimp only; omega) start (hstE hst_lt) hlt
    have htr := arenaPrefix_preserves_compact (k' := { kM with arena_len := dst }) hcmp' hcv harE
      harM (by omega) hpre
    rw [← htr.2.1] at hst_e
    exact (fullArenaClauseRefsCore_mono_prefix (Nat.le_of_lt hfr_lt) htr.1.1 _ hst_e).1

inductive M6PostMoveInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (start : Nat) (dst : BitVec 64)
    (unsat new_unit : Bool) (_ : Tup Val []) (mM : Mem 64) : Prop where
  | mk (sM : FullState)
      (hpostM : M6PostLike s sM)
      (hlenM : sM.LengthsOk c)
      (hcvM : sM.core.cur_vars = s.core.cur_vars)
      (halM : sM.core.arena_len = s.core.arena_len)
      (hclM : sM.core.cur_level = s.core.cur_level)
      (hdmM : sM.core.dense_mode = s.core.dense_mode)
      (hftM : sM.core.frame_trail = s.core.frame_trail)
      (hfdM : sM.core.frame_dec = s.core.frame_dec)
      (hincM : sM.core.inconsistent = s.core.inconsistent)
      (helM : sM.scratch.extend_len = s.scratch.extend_len)
      (hws2M : sM.scratch.work_stk2 = s.scratch.work_stk2)
      (hwM : FullWitnessInv c F0 F_cur { sM.core with arena_len := dst.toNat })
      (hnoM : ∀ r ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat },
        (fullArenaHdrCore { sM.core with arena_len := dst.toNat } r &&& 0x00800000#32) = 0#32 ∧
        fullArenaClauseGarbCore { sM.core with arena_len := dst.toNat } r = false)
      (hndM : FullArenaVarsNodup s →
        ∀ r ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat },
          ((fullArenaClauseLitsCore { sM.core with arena_len := dst.toNat } r).map (· / 2)).Nodup)
      (hstM_in : start < dst.toNat →
        start ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat })
      (hunsM : unsat = true → s.core.cur_level = 0 ∧ F0.Unsat)
      (hunitM : new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sM.core.trail_end)
      (hposM : 0 < s.core.cur_level → unsat = false ∧ new_unit = false ∧
        sM.core.vals = s.core.vals ∧ sM.core.lvl = s.core.lvl ∧ sM.core.trl = s.core.trl ∧
        sM.core.trail_pos = s.core.trail_pos ∧ sM.core.trail_end = s.core.trail_end)
      (hmM : (FullMem c sM ⋆ R) mM) :
      M6PostMoveInv c F0 F_cur s R start dst unsat new_unit () mM

inductive M6RsnBranchInv (c : FullCfg) (F_cur : List (List Nat)) (s sPre sC : FullState)
    (R : Mem 64 → Prop) (arH : List (BitVec 32)) (nsrc dst st : Nat) (mark_allowed : Bool)
    (_ : Tup Val []) (mR : Mem 64) : Prop where
  | mk (arR rsnsR : List (BitVec 32))
      (harR_len : arR.length = c.arena_cap)
      (hrsnsR_len : rsnsR.length = c.max_vars)
      (hpreR : ∀ i < dst, arR[i]? = arH[i]?)
      (hbodyR : ∀ j, dst + 3 ≤ j → arR[j]? = arH[j]?)
      (hszR : (arR[dst + 2]?.getD 0#32).toNat = st)
      (hflR : (arR[dst]?.getD 0#32 &&& 0x00880000#32) = 0#32)
      (hredR : (arR[dst]?.getD 0#32 &&& 0x00400000#32) =
        (arH[dst]?.getD 0#32 &&& 0x00400000#32))
      (hcmpR : CompactPrefixOk c F_cur s { sC.core with arena := arR, rsns := rsnsR }
        (dst + 3 + st))
      (hdst_inR : dst ∈ fullArenaClauseRefsCore
        { sC.core with arena := arR, rsns := rsnsR, arena_len := dst + 3 + st })
      (hrsns_lt_dst : ∀ idx < sPre.core.trail_end,
        (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < dst →
        rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          sC.core.rsns[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
      (hrsns_r0 : s.core.cur_level = 0 → rsnsR = sC.core.rsns)
      (hrmR : 0 < s.core.cur_level →
        SweepReasonMapInv sPre.core { sC.core with arena := arR, rsns := rsnsR } nsrc
          (dst + 3 + st))
      (hmkR : 0 < s.core.cur_level → mark_allowed = true →
        ∀ idx < sPre.core.trail_end,
          (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = dst →
          (arR[dst]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j < (arR[dst + 2]?.getD 0#32).toNat,
            let lit := (arR[dst + 3 + j]?.getD 0#32).toNat
            lit / 2 = (sPre.core.trl[idx]?.getD 0#32).toNat / 2 ∧
            sC.core.vals[lit]?.getD 0#8 = 1#8)
      (hmR : (FullMem c { sC with core := { sC.core with arena := arR, rsns := rsnsR } } ⋆ R) mR) :
      M6RsnBranchInv c F_cur s sPre sC R arH nsrc dst st mark_allowed () mR

inductive M6ClearFallInv (c : FullCfg) (F_cur : List (List Nat)) (s sPre sE : FullState)
    (R : Mem 64 → Prop) (first_red dst : Nat) (cp : BitVec 64) (mF : Mem 64) : Prop where
  | mk
      (hfr_cp : first_red ≤ cp.toNat)
      (hcp_le : cp.toNat ≤ dst)
      (arL : List (BitVec 32))
      (rwRem : Nat)
      (harL_l : arL.length = c.arena_cap)
      (hpreL : ∀ i, i < first_red → arL[i]? = sE.core.arena[i]?)
      (htailL : ∀ i, cp.toNat ≤ i → i < dst → arL[i]? = sE.core.arena[i]?)
      (hmvRem : MoveRangeChain sE.core.arena cp.toNat dst rwRem)
      (hcmpL : CompactPrefixOk c F_cur s { sE.core with arena := arL } dst)
      (hrmL : 0 < s.core.cur_level →
        SweepReasonMapInv sPre.core { sE.core with arena := arL } sPre.core.arena_len dst)
      (hrefsL : fullArenaClauseRefsCore { sE.core with arena := arL, arena_len := dst } =
        fullArenaClauseRefsCore { sE.core with arena_len := dst })
      (hcp_in : cp.toNat < dst →
        cp.toNat ∈ fullArenaClauseRefsCore { sE.core with arena := arL, arena_len := dst })
      (hmF : (FullMem c { sE with core := { sE.core with arena := arL } } ⋆ R) mF) :
      M6ClearFallInv c F_cur s sPre sE R first_red dst cp mF

/-! ## 3. `full_arena_sweep_m6_wp` (`Full.fullArenaSweepSpec`) -/

theorem m6_root_post_move_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {kE kM : FullCoreState} {dst : Nat}
    (hwEnd : FullWitnessInv c F0 F_cur { kE with arena_len := dst })
    (haM : FullArenaClausesInv c F_cur { kM with arena_len := dst })
    (hwatM : ModeWatchesInv F_cur { kM with arena_len := dst })
    (hvals : kM.vals = kE.vals) (hlvl : kM.lvl = kE.lvl) (htrl : kM.trl = kE.trl)
    (htp : kM.trail_pos = kE.trail_pos) (hte : kM.trail_end = kE.trail_end)
    (hcl : kM.cur_level = kE.cur_level) (hcv : kM.cur_vars = kE.cur_vars)
    (hft : kM.frame_trail = kE.frame_trail) (hfd : kM.frame_dec = kE.frame_dec)
    (hinc : kM.inconsistent = kE.inconsistent) (hcl0 : kE.cur_level = 0)
    (hrsn_ff : ∀ idx < kE.trail_end,
      kM.rsns[(kE.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    FullWitnessInv c F0 F_cur { kM with arena_len := dst } :=
  { ext_sound := by dsimp only; rw [hcv]; exact hwEnd.ext_sound
    inconsistent_sound := by dsimp only; rw [hinc]; exact hwEnd.inconsistent_sound
    arena := haM
    watches := hwatM
    cur_level_le := by dsimp only; rw [hcl, hte]; exact hwEnd.cur_level_le
    trail_lits_lt := fun i hi => by
      dsimp only at hi ⊢; rw [htrl, hcv]; exact hwEnd.trail_lits_lt i (hte ▸ hi)
    trail_vars_nodup := fun i j hi hj h => by
      dsimp only at hi hj h; rw [htrl] at h
      exact hwEnd.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj) h
    vals_domain := fun l hl => by
      dsimp only at hl ⊢; rw [hvals]; exact hwEnd.vals_domain l (hcv ▸ hl)
    vals_true_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals, hte, htrl]; exact hwEnd.vals_true_iff l (hcv ▸ hl)
    vals_false_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals, hte, htrl]; exact hwEnd.vals_false_iff l (hcv ▸ hl)
    lvl_le := fun i hi => by
      dsimp only at hi ⊢; rw [hlvl, htrl, hcl]; exact hwEnd.lvl_le i (hte ▸ hi)
    dec_earliest := fun i j hi hj hlt hdec => by
      dsimp only at hi hj hlt hdec; rw [hlvl, htrl] at hlt hdec
      exact hwEnd.dec_earliest i j (hte ▸ hi) (hte ▸ hj) hlt
        ⟨hdec.1, hwEnd.level0_rsn_none j (hte ▸ hj)
          (by have := hwEnd.lvl_le j (hte ▸ hj); change _ ≤ kE.cur_level at this; omega)⟩
    levels_inhabited := fun L h1 h2 => by
      dsimp only at h2 ⊢; rw [hte, hlvl, htrl]; exact hwEnd.levels_inhabited L h1 (hcl ▸ h2)
    level0_sound := fun i hi h0 => by
      dsimp only at hi h0 ⊢; rw [hlvl, htrl] at h0; rw [htrl]
      exact hwEnd.level0_sound i (hte ▸ hi) h0
    trail_pos_inv := fun i hi => by
      dsimp only at hi ⊢; rw [htp, htrl]; exact hwEnd.trail_pos_inv i (hte ▸ hi)
    level0_rsn_none := fun idx hidx _ => by
      dsimp only at hidx ⊢; rw [htrl]; exact hrsn_ff idx (hte ▸ hidx)
    frame_trail_lt := fun L hL => by
      dsimp only at hL ⊢; rw [hft, hte]; exact hwEnd.frame_trail_lt L (hcl ▸ hL)
    frame_trail_mono := fun L1 L2 h1 h2 => by
      dsimp only at h2 ⊢; rw [hft]; exact hwEnd.frame_trail_mono L1 L2 h1 (hcl ▸ h2)
    frame_trail_before_lt := fun L h1 h2 i hi => by
      dsimp only at h2 hi ⊢; rw [hft] at hi; rw [hlvl, htrl]
      exact hwEnd.frame_trail_before_lt L h1 (hcl ▸ h2) i hi
    frame_dec_lt := fun L h1 h2 => by
      dsimp only at h2 ⊢; rw [hfd, hcv]; exact hwEnd.frame_dec_lt L h1 (hcl ▸ h2)
    reason_inv := fun idx hidx hne => by
      dsimp only at hidx hne; rw [htrl] at hne
      exact absurd (hrsn_ff idx (hte ▸ hidx)) hne
    reason_lit_mem := fun idx hidx hne => by
      dsimp only at hidx hne; rw [htrl] at hne
      exact absurd (hrsn_ff idx (hte ▸ hidx)) hne }

theorem cleanIrredChain_three_le {ar : List (BitVec 32)} {lo hi : Nat}
    (h : CleanIrredChain ar lo hi) (hlt : lo < hi) : lo + 3 ≤ hi := by
  cases h with
  | empty => omega
  | step h3 => exact h3

theorem m6_refInChain_mem_refs {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {hi : Nat}
    (ha : FullArenaClausesInv c F_cur { k with arena_len := hi }) :
    ∀ p rw, MoveRangeChain k.arena p hi rw →
      (p = hi ∨ p ∈ fullArenaClauseRefsCore { k with arena_len := hi }) →
      ∀ r, RefInChain k.arena p hi r → r ∈ fullArenaClauseRefsCore { k with arena_len := hi } := by
  intro p rw hmv
  induction hmv with
  | empty => intro _ r hr; exfalso; have := hr.bounds; omega
  | @step p hi rw h3 hfl hsz hfit _ ih =>
    intro hp_mem r hr
    have hp_m : p ∈ fullArenaClauseRefsCore { k with arena_len := hi } :=
      hp_mem.resolve_left (by omega)
    cases hr with
    | head => exact hp_m
    | tail _ _ _ _ hr_tl =>
      have hsh : (k.arena[p]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
        have h1 : (k.arena[p]?.getD 0#32 &&& (0x00880000#32 &&& 0x00800000#32)) = 0#32 := by
          rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
        rwa [show (0x00880000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl] at h1
      have hnx : fullArenaNextOff k.arena hi p =
          p + 3 + (k.arena[p + 2]?.getD 0#32).toNat := by
        unfold fullArenaNextOff
        simp [show ¬ (p + 3 > hi) by omega,
          show ¬ (p + 3 + (k.arena[p + 2]?.getD 0#32).toNat > hi) by omega, hsh]
      have hnx_or := fullArenaClauseRefs_next_or_end ha hp_m
      rw [hnx] at hnx_or
      rcases hnx_or with h_end | hnx_mem
      · exfalso; dsimp only at h_end
        have h1 := hr_tl.bounds.1; rw [h_end] at h1
        have h2 := hr_tl.bounds.2; omega
      · exact ih ha (Or.inr hnx_mem) r hr_tl

theorem m6_pre_val_all_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre : FullState} {fp : Nat} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd : FullArenaVarsNodup s)
    (hrmk : 0 < s.core.cur_level → FullReasonsMarked s)
    (hfp_pos : 0 < fp) (hfp_lt : fp < s.core.arena_len) (hc0 : CleanIrredChain s.core.arena 0 fp)
    {ar' : List (BitVec 32)} (har' : ar'.length = c.arena_cap)
    (htail : ∀ i, fp ≤ i → i < s.core.arena_len → ar'[i]? = s.core.arena[i]?)
    (hmatch : ∀ r ∈ fullArenaClauseRefsCore { s.core with arena_len := fp },
      (ar'[r]?.getD 0#32 &&& 0x00C80000#32) = 0#32 ∧
      ar'[r + 2]? = s.core.arena[r + 2]? ∧
      ∀ j < (s.core.arena[r + 2]?.getD 0#32).toNat, ar'[r + 3 + j]? = s.core.arena[r + 3 + j]?)
    (hsPre : sPre = { s with core := { s.core with arena := ar' } }) :
    sPre.LengthsOk c ∧ FullWitnessInv c F0 F_cur sPre.core ∧ FullArenaVarsNodup sPre ∧
    (fp < s.core.arena_len → fp ∈ fullArenaClauseRefs sPre) ∧
    CompactPrefixOk c F_cur s sPre.core fp ∧
    SweepReasonMapInv sPre.core sPre.core fp fp ∧
    (0 < s.core.cur_level →
      ∀ idx < sPre.core.trail_end,
        let v := (sPre.core.trl[idx]?.getD 0#32).toNat / 2
        let rsn := sPre.core.rsns[v]?.getD 0xFFFFFFFF#32
        0 < (sPre.core.lvl[v]?.getD 0#32).toNat →
        (rsn &&& 0x80000000#32) = 0#32 → fp ≤ rsn.toNat →
        (fullArenaHdr sPre rsn.toNat &&& 0x00200000#32) ≠ 0#32) := by
  subst hsPre
  obtain ⟨hfp_mem, hcmp', hrm', hw', hnd', _⟩ := prefix_cleared_ok hlen.core_ok hw hnd
    hfp_pos hfp_lt hc0 har' htail hmatch
  have hrm_self : SweepReasonMapInv { s.core with arena := ar' }
      { s.core with arena := ar' } fp fp := by
    intro idx hidx
    have h1 := hrm' idx hidx; dsimp only at h1 ⊢
    split at h1
    · split; exact h1; contradiction
    · split
      · contradiction
      · split at h1
        · obtain ⟨ha, hb, hc, hd, he, hf, _⟩ := h1
          split
          · exact ⟨ha, hb, hc, hd, he, hf, rfl⟩
          · contradiction
        · split; contradiction; exact h1
  refine ⟨⟨{ hlen.core_ok with arena_len_arr := har' }, hlen.scratch_ok⟩, hw', hnd',
    fun _ => hfp_mem, hcmp', hrm_self, fun hpos idx hidx hlvl hlg hge => ?_⟩
  have hmk := hrmk hpos idx hidx hlvl hlg
  have hri := hw.reason_inv idx hidx (fun hff => by rw [hff] at hlg; simp at hlg)
  rw [ite_eq_right (fun h => h hlg)] at hri
  have hr_eq : ({ s.core with arena := ar' }).arena[
      (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat]? =
      s.core.arena[
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat]? :=
    htail _ hge (by have := (hw.arena.refs_wf _ hri.1).1; omega)
  unfold fullArenaHdr fullArenaHdrCore at hmk ⊢; dsimp only; rw [hr_eq]; exact hmk

/-! ## 3. `full_arena_sweep_m6_wp` (`Full.fullArenaSweepSpec`) -/

theorem m6_rsn_post_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL sC : FullState} {R : Mem 64 → Prop} {arH arR rsnsR : List (BitVec 32)}
    {hdr0 : BitVec 32} {start dst nsrc src st fr' first_red : BitVec 64}
    {old_sz : BitVec 32} {rwL : Nat} {hcl_beq hia' new_unit mark_allowed : Bool}
    {mR : Mem 64}
    (_hwPre : FullWitnessInv c F0 F_cur sPre.core)
    (hst_dst : start.toNat ≤ dst.toNat) (_hdst_src : dst.toNat ≤ src.toNat)
    (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hdst_next_eq :
      (dst + (3 : BitVec 64) + (st.setWidth 32).setWidth 64).toNat = dst.toNat + 3 + st.toNat)
    (hnew3 : 3 ≤ st.toNat) (hfit_next : dst.toNat + 3 + st.toNat ≤ nsrc.toNat)
    (hnxt_le_al : nsrc.toNat ≤ s.core.arena_len)
    (hnxt_mem : nsrc.toNat = s.core.arena_len ∨ nsrc.toNat ∈ fullArenaClauseRefs sPre)
    (hlikeC : M6SweepLike s sC) (hlenC0 : sC.LengthsOk c)
    (_hcvL : sL.core.cur_vars = s.core.cur_vars)
    (hcl_pre : sPre.core.cur_level = s.core.cur_level)
    (harC_len : sC.core.arena.length = c.arena_cap)
    (hcmpC : CompactPrefixOk c F_cur s sC.core dst.toNat)
    (hcmpC_st : CompactPrefixOk c F_cur s sC.core start.toNat)
    (hlayC : WatchStackLayout sC.core)
    (hltC : ∀ l < 2 * sC.core.cur_vars,
      WatchSliceLtOk start.toNat F_cur sC.core l (fullWatchOff sC l) (fullWatchSize sC l))
    (hstC_in : start.toNat < dst.toNat →
      start.toNat ∈ fullArenaClauseRefsCore { sC.core with arena_len := dst.toNat })
    (hfr_to_C : M6FirstRedOk c F_cur s sPre sC start.toNat dst.toNat rwL first_red)
    (htailC : ∀ i, nsrc.toNat ≤ i → i < s.core.arena_len →
      sC.core.arena[i]? = sPre.core.arena[i]?)
    (hrootL : M6SweepLoopRootOk c F0 F_cur s sL start.toNat dst.toNat new_unit)
    (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
    (hdec_cl0 : ∀ b : Bool,
      hcl_beq = b ↔ (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hout_ok0 : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz hcl_beq st)
    (hpreH : ∀ i < dst.toNat, arH[i]? = sC.core.arena[i]?)
    (hbodyH : ∀ j, dst.toNat + 3 ≤ j → arH[j]? = sC.core.arena[j]?)
    (harH_0 : arH[dst.toNat]? = some (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)))
    (hhdr_orig : hdr0 = fullArenaHdrCore sPre.core src.toNat)
    (hng_src : fullArenaClauseGarbCore sPre.core src.toNat = false)
    (harR_len : arR.length = c.arena_cap) (hrsnsR_len : rsnsR.length = c.max_vars)
    (hpreR : ∀ i < dst.toNat, arR[i]? = arH[i]?)
    (hbodyR : ∀ j, dst.toNat + 3 ≤ j → arR[j]? = arH[j]?)
    (hszR : (arR[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (hflR : (arR[dst.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hredR : (arR[dst.toNat]?.getD 0#32 &&& 0x00400000#32) =
      (arH[dst.toNat]?.getD 0#32 &&& 0x00400000#32))
    (hcmpR : CompactPrefixOk c F_cur s { sC.core with arena := arR, rsns := rsnsR }
      (dst.toNat + 3 + st.toNat))
    (hdst_inR : dst.toNat ∈ fullArenaClauseRefsCore
      { sC.core with arena := arR, rsns := rsnsR, arena_len := dst.toNat + 3 + st.toNat })
    (hrsns_lt_dst : ∀ idx < sPre.core.trail_end,
      (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < dst.toNat →
      rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        sC.core.rsns[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hrsns_r0 : s.core.cur_level = 0 → rsnsR = sC.core.rsns)
    (hrmR : 0 < s.core.cur_level → SweepReasonMapInv sPre.core
      { sC.core with arena := arR, rsns := rsnsR } nsrc.toNat (dst.toNat + 3 + st.toNat))
    (hmkR : 0 < s.core.cur_level → mark_allowed = true →
      ∀ idx < sPre.core.trail_end,
        (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = dst.toNat →
        (arR[dst.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        ∃ j < (arR[dst.toNat + 2]?.getD 0#32).toNat,
          let lit := (arR[dst.toNat + 3 + j]?.getD 0#32).toNat
          lit / 2 = (sPre.core.trl[idx]?.getD 0#32).toNat / 2 ∧ sC.core.vals[lit]?.getD 0#8 = 1#8)
    (hmR : (FullMem c { sC with core := { sC.core with arena := arR, rsns := rsnsR } } ⋆ R) mR)
    (hmark_eq : mark_allowed = (!(decide (s.core.cur_level = 0)) &&
      (decide (first_red ≠ 0xFFFFFFFF#64) || decide ((hdr0 &&& 0x00400000#32) ≠ 0#32))))
    (_hfr_nil : fr' = 0xFFFFFFFF#64 →
      first_red = 0xFFFFFFFF#64 ∧ (hdr0 &&& 0x00400000#32) = 0#32)
    (hfr_some : fr' ≠ 0xFFFFFFFF#64 →
      (first_red = 0xFFFFFFFF#64 → fr' = dst ∧ (hdr0 &&& 0x00400000#32) ≠ 0#32) ∧
      (first_red ≠ 0xFFFFFFFF#64 → fr' = first_red))
    (hhia : hia' = true → fr' ≠ 0xFFFFFFFF#64) :
    M6SweepLoopInv c F0 F_cur s sPre R start.toNat
      nsrc (dst + (3 : BitVec 64) + (st.setWidth 32).setWidth 64) fr' hia' new_unit mR := by
  let sNext : FullState := { sC with core := { sC.core with arena := arR, rsns := rsnsR } }
  have hlenNext : sNext.LengthsOk c :=
    ⟨{ hlenC0.core_ok with arena_len_arr := harR_len, rsns_len := hrsnsR_len }, hlenC0.scratch_ok⟩
  have hcvC : sC.core.cur_vars = s.core.cur_vars := hlikeC.unchanged.1
  have halC : sC.core.arena_len = s.core.arena_len := hlikeC.unchanged.2.1
  have hdst_next_cap : dst.toNat + 3 + st.toNat ≤ c.arena_cap :=
    Nat.le_trans hfit_next (Nat.le_trans hnxt_le_al hal_le)
  have hdst_le_al : dst.toNat ≤ s.core.arena_len :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ 3) (Nat.le_add_right _ _))
      (Nat.le_trans hfit_next hnxt_le_al)
  have hdst_cap : dst.toNat ≤ c.arena_cap := Nat.le_trans hdst_le_al hal_le
  have hst_al : start.toNat ≤ s.core.arena_len := Nat.le_trans hst_dst hdst_le_al
  have hst_cap : start.toNat ≤ c.arena_cap := Nat.le_trans hst_al hal_le
  have hpre_CR : PrefixAgrees dst.toNat sC.core.arena arR := fun i hi =>
    (hpreR i hi).trans (hpreH i hi)
  obtain ⟨hcmpR_st, hkeepR_st⟩ :=
    m6_refs_lt_prefix_transfer hcmpC_st (k' := sNext.core) rfl harC_len harR_len
      (by show start.toNat ≤ sC.core.arena_len; rw [halC]; exact hst_al)
      (by show start.toNat ≤ sNext.core.arena_len; rw [halC]; exact hst_al)
      hst_cap (fun i hi => hpre_CR i (Nat.lt_of_lt_of_le hi hst_dst))
  have htr_C : CompactPrefixOk c F_cur s sNext.core dst.toNat ∧
      CompactPrefixCongr sC.core sNext.core dst.toNat :=
    arenaPrefix_preserves_compact (k := sC.core) (k' := sNext.core) hcmpC rfl harC_len harR_len
      hdst_cap hpre_CR
  have hlayNext : WatchStackLayout sNext.core := hlayC.with_wstk rfl rfl rfl rfl
  have hltNext : ∀ l < 2 * sNext.core.cur_vars,
      WatchSliceLtOk start.toNat F_cur sNext.core l (fullWatchOff sNext l)
        (fullWatchSize sNext l) := fun l hl =>
    (hltC l hl).relocate (k := sC.core) (k' := sNext.core)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _) hkeepR_st (fun _ _ => rfl)
  have hstNext_in : start.toNat < dst.toNat + 3 + st.toNat →
      start.toNat ∈ fullArenaClauseRefsCore
        { sNext.core with arena_len := dst.toNat + 3 + st.toNat } := fun _ => by
    rcases Nat.eq_or_lt_of_le hst_dst with heq | hlt
    · rw [heq]; exact hdst_inR
    · have h1 := hstC_in hlt
      rw [← htr_C.2.1] at h1
      exact (fullArenaClauseRefsCore_mono_prefix
        (Nat.le_trans (Nat.le_add_right _ 3) (Nat.le_add_right _ _)) htr_C.1.1 _ h1).1
  have hfr_next : ∃ rwN, M6FirstRedOk c F_cur s sPre sNext start.toNat
      (dst.toNat + 3 + st.toNat) rwN fr' := by
    by_cases hfe : fr' = 0xFFFFFFFF#64
    · exact ⟨0, .inl hfe⟩
    · obtain ⟨h_first, h_keep⟩ := hfr_some hfe
      by_cases hfr0_e : first_red = 0xFFFFFFFF#64
      · obtain ⟨hfr_eq, hred_ne⟩ := h_first hfr0_e
        rw [hfr_eq]
        have hredR_ne : (arR[dst.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
          rw [hredR, harH_0, Option.getD_some,
            (m6_bv32_nhdr_bits hdr0 (by
              unfold fullArenaClauseGarbCore at hng_src
              simpa [hhdr_orig, bne_iff_ne] using hng_src)).2.2.2.2.1]
          exact hred_ne
        have hmv1 : MoveRangeChain arR dst.toNat (dst.toNat + 3 + st.toNat) (3 + st.toNat) := by
          have h1 := moveRangeChain_snoc (ar := arR) (a := dst.toNat) (p := dst.toNat)
            (p' := dst.toNat + 3 + st.toNat) .empty (by omega)
            hflR (by rw [hszR]; exact hnew3) (by rw [hszR])
          rw [ite_eq_left hredR_ne, hszR, Nat.zero_add] at h1
          exact h1
        refine ⟨3 + st.toNat, .inr ⟨hst_dst, by omega, htr_C.1, by omega, hmv1, hdst_inR,
          ⟨fun hp r hr idx hidx heq => ?_⟩⟩⟩
        have hps : 0 < s.core.cur_level := hcl_pre ▸ hp
        have hmk_t : mark_allowed = true := by
          simp [hmark_eq, hred_ne, show s.core.cur_level ≠ 0 by omega]
        cases hr with
        | head => exact hmkR hps hmk_t idx hidx heq
        | tail _ _ _ _ hr_tl => exfalso; have := hr_tl.bounds; rw [hszR] at this; omega
      · obtain hfr_eq := h_keep hfr0_e
        rw [hfr_eq]
        rcases hfr_to_C with hbad | ⟨h1, h2, hcmpC_fr, hrw0, hmvC, hfr_inC, hmkC⟩
        · exact absurd hbad hfr0_e
        · have hmvR_pre : MoveRangeChain arR first_red.toNat dst.toNat rwL :=
            hmvC.congr (fun i _ hi => (hpreR i hi).trans (hpreH i hi))
          have hmvR_nxt := moveRangeChain_snoc hmvR_pre (p' := dst.toNat + 3 + st.toNat) (by omega)
            hflR (by rw [hszR]; exact hnew3) (by rw [hszR])
          rw [hszR] at hmvR_nxt
          have hcmpR_fr := (arenaPrefix_preserves_compact (k := sC.core) (k' := sNext.core)
            hcmpC_fr rfl harC_len harR_len (Nat.le_trans (Nat.le_of_lt h2) hdst_cap)
            (fun i hi => hpre_CR i (Nat.lt_trans hi h2))).1
          have hfr_inR : first_red.toNat ∈ fullArenaClauseRefsCore
              { sNext.core with arena_len := dst.toNat } := by
            rw [htr_C.2.1]; exact hfr_inC
          refine ⟨rwL + if (arR[dst.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
              3 + st.toNat else 0,
            .inr ⟨h1, by omega, hcmpR_fr, by omega, hmvR_nxt,
            (fullArenaClauseRefsCore_mono_prefix
              (Nat.le_trans (Nat.le_add_right _ 3) (Nat.le_add_right _ _))
              htr_C.1.1 _ hfr_inR).1,
            ⟨fun hp r hr idx hidx heq => ?_⟩⟩⟩
          rcases refInChain_split hmvR_pre hr with hprev | hcur
          · have hprevC := hprev.congr (fun i _ hi => (hpre_CR i hi).symm)
            have hpb := hprevC.bounds
            have hrsn_ne : sC.core.rsns[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32 = sNext.core.rsns[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32 := by
              have hrsn_eq_r := heq
              rw [show sNext.core.rsns = rsnsR from rfl] at hrsn_eq_r
              have hpb2 := hpb.2
              exact (hrsns_lt_dst idx hidx (by rw [hrsn_eq_r]; omega)).symm
            obtain ⟨ha, j, hj, hlv, hval⟩ :=
              hmkC.get hp r hprevC idx hidx (by rw [hrsn_ne]; exact heq)
            exact ⟨by rw [hpre_CR r (by have := hpb.2; omega)]; exact ha, j,
              by rw [hpre_CR (r + 2) (by have := hpb.2; omega)]; exact hj,
              by rw [hpre_CR (r + 3 + j) (by have := hpb.2; omega)]; exact hlv,
              by rw [hpre_CR (r + 3 + j) (by have := hpb.2; omega)]; exact hval⟩
          · cases hcur with
            | head =>
              have hps : 0 < s.core.cur_level := hcl_pre ▸ hp
              have hmk_t : mark_allowed = true := by
                simp [hmark_eq, hfr0_e, show s.core.cur_level ≠ 0 by omega]
              exact hmkR hps hmk_t idx hidx heq
            | tail _ _ _ _ hr_tl => exfalso; have := hr_tl.bounds; rw [hszR] at this; omega
  rcases hfr_next with ⟨rwN, hfrN⟩
  refine ⟨by rw [hdst_next_eq]; exact Nat.le_trans hst_dst (Nat.le_trans (Nat.le_add_right _ 3)
      (Nat.le_add_right _ _)),
    by rw [hdst_next_eq]; exact hfit_next, hnxt_le_al,
    fun hlt => hnxt_mem.resolve_left (Nat.ne_of_lt hlt),
    hhia, sNext, rwN, hlikeC.of_ar_rsns, hlenNext,
    by rw [hdst_next_eq]; exact hcmpR, hcmpR_st, hlayNext, hltNext,
    fun hlt => by rw [hdst_next_eq] at hlt ⊢; exact hstNext_in hlt,
    by rw [hdst_next_eq]; exact hfrN,
    fun i hi1 hi2 => by
      have hi_g : dst.toNat + 3 ≤ i :=
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hfit_next hi1)
      rw [hbodyR i hi_g, hbodyH i hi_g]; exact htailC i hi1 hi2,
    ⟨fun hcl0 => ?_⟩, ⟨fun hpos => ?_⟩, fullMem_cast hmR rfl⟩
  · obtain ⟨hwC, hbinC, hteC, _⟩ := hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
    have hcl0C : sC.core.cur_level = 0 := hlikeC.unchanged.2.2.1.trans hcl0
    have hwC_dst : FullWitnessInv c F0 F_cur { sC.core with arena_len := dst.toNat } :=
      { hwC with
        arena := hcmpC.1
        watches := (hbinC.with_core (k' := { sC.core with arena_len := dst.toNat })
          rfl rfl rfl rfl).toModeWatchesInv
        reason_inv := fun i hi h => absurd (hwC.level0_rsn_none i hi (by
          have := hwC.lvl_le i hi; rw [hcl0C] at this; omega)) h
        reason_lit_mem := fun i hi h => absurd (hwC.level0_rsn_none i hi (by
          have := hwC.lvl_le i hi; rw [hcl0C] at this; omega)) h }
    rw [hdst_next_eq]
    have hst0 := (hrootL.get hcl0).1
    have hwN := fullWitnessInv_append_root hwC_dst hbinC hcl0C
      (by simpa [sNext, hrsns_r0 hcl0] using hcmpR.1)
    have hkn : ({ sNext.core with arena_len := dst.toNat + 3 + st.toNat } : FullCoreState) =
        { { sC.core with arena := arR } with arena_len := dst.toNat + 3 + st.toNat } := by
      dsimp [sNext]; rw [hrsns_r0 hcl0]
    exact ⟨hst0, by rw [hkn]; exact hwN,
      Nat.le_trans (hrootL.get hcl0).2.2.1 hteC,
      fun hnu => Nat.lt_of_lt_of_le ((hrootL.get hcl0).2.2.2 hnu) hteC⟩
  · obtain ⟨_, hvC, _, hlC, _, htC, htpC, hteC, _⟩ := hout_ok0.1 ((hdec_cl0 false).mpr hpos)
    obtain ⟨hnu0, hv0, hl0, ht0, htp0, hte0, _⟩ := hposL.get hpos
    exact ⟨hnu0, hvC.trans hv0, hlC.trans hl0, htC.trans ht0, htpC.trans htp0,
      hteC.trans hte0, by rw [hdst_next_eq]; exact hrmR hpos⟩

theorem m6_pre_clr_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {cp : BitVec 64} {arL : List (BitVec 32)} {m' : Mem 64}
    (hcp_lt : cp.toNat < s.core.first_reducible.toNat)
    (hfp_lt : s.core.first_reducible.toNat < s.core.arena_len)
    (hal_le : s.core.arena_len ≤ c.arena_cap)
    (harL_l : arL.length = c.arena_cap)
    (hdone : CleanIrredChain s.core.arena 0 cp.toNat)
    (h3 : 3 ≤ (s.core.arena[cp.toNat + 2]?.getD 0#32).toNat)
    (hfl : (s.core.arena[cp.toNat]?.getD 0#32 &&& 0x00C80000#32) = 0#32)
    (hsz : 3 ≤ (s.core.arena[cp.toNat + 2]?.getD 0#32).toNat)
    (hfit : cp.toNat + 3 + (s.core.arena[cp.toNat + 2]?.getD 0#32).toNat ≤
      s.core.first_reducible.toNat)
    (htl : CleanIrredChain s.core.arena
      (cp.toNat + 3 + (s.core.arena[cp.toNat + 2]?.getD 0#32).toNat)
      s.core.first_reducible.toNat)
    (hcp_in : cp.toNat ∈ fullArenaClauseRefsCore
      { s.core with arena_len := s.core.first_reducible.toNat })
    (htailL : ∀ i, cp.toNat ≤ i → i < s.core.arena_len → arL[i]? = s.core.arena[i]?)
    (hmatchL : ∀ r ∈ fullArenaClauseRefsCore
        { s.core with arena_len := s.core.first_reducible.toNat }, r < cp.toNat →
      (arL[r]?.getD 0#32 &&& 0x00C80000#32) = 0#32 ∧ arL[r + 2]? = s.core.arena[r + 2]? ∧
      ∀ j < (s.core.arena[r + 2]?.getD 0#32).toNat, arL[r + 3 + j]? = s.core.arena[r + 3 + j]?)
    (hm' :
      (FullMem c { s with core := { s.core with
        arena := arL.set cp.toNat ((arL[cp.toNat]'(by omega)) &&& ~~~0x00200000#32) } } ⋆ R) m') :
    let sz32 := arL[(cp + 2#64).toNat]'(by
      have := bv64_add2_lt (x := cp) (by omega); omega)
    let cp' := cp + 3#64 + sz32.setWidth 64
    cp'.toNat = cp.toNat + 3 + sz32.toNat ∧
    sz32.toNat = (s.core.arena[cp.toNat + 2]?.getD 0#32).toNat ∧
    PreSweepClrInv c s R s.core.first_reducible.toNat cp' m' := by
  have hcp3_ar : cp.toNat + 3 ≤ arL.length := by omega
  have hcp2_eq : (cp + 2#64).toNat = cp.toNat + 2 := bv64_add2_lt (by omega)
  have hcp_lt_ar : cp.toNat < arL.length := by omega
  have hcp2_lt_ar : (cp + 2#64).toNat < arL.length := by rw [hcp2_eq]; omega
  let hdrL := arL[cp.toNat]'hcp_lt_ar
  let sz32 := arL[(cp + 2#64).toNat]'hcp2_lt_ar
  have hsz_eq : sz32.toNat = (s.core.arena[cp.toNat + 2]?.getD 0#32).toNat := by
    have h1 := htailL (cp.toNat + 2) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega : cp.toNat + 2 < arL.length)] at h1
    have h2 := congrArg (fun o => (o.getD 0#32).toNat) h1
    dsimp only [sz32]; simp only [hcp2_eq]
    simpa only [Option.getD_some] using h2
  have hhdr_eq : hdrL = s.core.arena[cp.toNat]?.getD 0#32 := by
    have h1 := htailL cp.toNat (Nat.le_refl _) (by omega)
    rw [List.getElem?_eq_getElem hcp_lt_ar] at h1
    dsimp only [hdrL]; rw [← Option.getD_some (a := arL[cp.toNat]'hcp_lt_ar), ← h1]
  have hcp_nxt : (cp + 3#64 + sz32.setWidth 64).toNat = cp.toNat + 3 + sz32.toNat :=
    bv64_add3_zext_lt (by omega)
  let arL' := arL.set cp.toNat (hdrL &&& ~~~0x00200000#32)
  have hdone' : CleanIrredChain s.core.arena 0 (cp.toNat + 3 + sz32.toNat) :=
    hdone.snoc (by omega) hfl hsz (by rw [hsz_eq])
  have hsh_cp : (s.core.arena[cp.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 :=
    (bv32_mask_00C80000_props _ hfl).1
  have hnx_cp : fullArenaNextOff s.core.arena s.core.first_reducible.toNat cp.toNat =
      cp.toNat + 3 + sz32.toNat := by
    unfold fullArenaNextOff
    simp [show ¬ (cp.toNat + 3 > s.core.first_reducible.toNat) by omega,
      show ¬ (cp.toNat + 3 + (s.core.arena[cp.toNat + 2]?.getD 0#32).toNat >
        s.core.first_reducible.toNat) by omega, hsh_cp, hsz_eq]
  have hnxt_in_fp : cp.toNat + 3 + sz32.toNat < s.core.first_reducible.toNat →
      cp.toNat + 3 + sz32.toNat ∈ fullArenaClauseRefsCore
        { s.core with arena_len := s.core.first_reducible.toNat } := fun hlt => by
    rw [← hnx_cp]
    refine fullArenaScanRefs_mem_next (by omega) hcp_in ?_
    rw [hnx_cp]; exact cleanIrredChain_three_le (by rw [hsz_eq]; exact htl) hlt
  refine ⟨hcp_nxt, hsz_eq, PreSweepClrInv.mk ?_ ?_ ?_ ?_ arL' ?_ ?_ ?_ hm'⟩
  · rw [hcp_nxt, hsz_eq]; exact hfit
  · rw [hcp_nxt]; exact hdone'
  · rw [hcp_nxt, hsz_eq]; exact htl
  · intro hlt; rw [hcp_nxt] at hlt ⊢; exact hnxt_in_fp hlt
  · simp [arL', harL_l]
  · intro i hi1 hi2
    rw [List.getElem?_set_ne (by rw [hcp_nxt] at hi1; omega)]
    exact htailL i (by rw [hcp_nxt] at hi1; omega) hi2
  · intro r hr hrlt
    rw [hcp_nxt] at hrlt
    have hfit_r := cleanIrredChain_disjoint_lt hdone (.step (by omega) hfl hsz hfit htl)
    by_cases hr_lt_cp : r < cp.toNat
    · obtain ⟨h1, h2, h3'⟩ := hmatchL r hr hr_lt_cp
      have hfit_r' : r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat ≤ cp.toNat :=
        hfit_r r hr hr_lt_cp
      refine ⟨by dsimp [arL']; rw [List.getElem?_set_ne (by omega)]; exact h1,
        by dsimp [arL']; rw [List.getElem?_set_ne (by omega)]; exact h2,
        fun j hj => by dsimp [arL']; rw [List.getElem?_set_ne (by omega)]; exact h3' j hj⟩
    · have hr_eq : r = cp.toNat := by
        by_cases heq : r = cp.toNat
        · exact heq
        · exfalso
          have h_disj := fullArenaScanRefs_disjoint hcp_in hr (by omega)
          rw [hnx_cp] at h_disj; omega
      subst r
      refine ⟨by
          dsimp [arL']; rw [List.getElem?_set_self hcp_lt_ar, Option.getD_some]
          change ((hdrL &&& ~~~0x00200000#32) &&& 0x00C80000#32) = 0#32
          rw [bv32_clear_rsn_keeps_clean, hhdr_eq]; exact hfl,
        by dsimp [arL']; rw [List.getElem?_set_ne (by omega)]
           exact htailL (cp.toNat + 2) (by omega) (by omega),
        fun j hj => by
          dsimp [arL']; rw [List.getElem?_set_ne (by omega)]
          exact htailL (cp.toNat + 3 + j) (by omega) (by omega)⟩

theorem m6_sweep_rsn_hit_pos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sL sC : FullState} {arH rsnsR : List (BitVec 32)} {litI : BitVec 32}
    {src nsrc st : Nat} {dst : BitVec 64}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hsrc_ref : src ∈ fullArenaClauseRefs s0)
    (hnsrc64 : nsrc = fullArenaNextOff s0.core.arena s0.core.arena_len src)
    (hdst_src : dst.toNat ≤ src) (hsrc_lt8 : src < 0x80000000)
    (hrmL : SweepReasonMapInv s0.core sL.core src dst.toNat)
    (hhapp : SweepHappenedCore s0.core sL.core
      { sL.core with arena := arH, rsns := rsnsR, arena_len := dst.toNat + 3 + st }
      dst.toNat src)
    (hrs_eq : rsnsR = sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32))
    (hvC : sC.core.vals = s0.core.vals) (hrC : sC.core.rsns = sL.core.rsns)
    (hrsns_len : sC.core.rsns.length = c.max_vars) (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hlitI_lt : litI.toNat < 2 * s0.core.cur_vars) (hlitI_v : litI.toNat < sC.core.vals.length)
    (hvg : (0#32).slt ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) = true)
    (hrsn_eq : (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = src) :
    SweepReasonMapInv s0.core { sC.core with arena := arH, rsns := rsnsR }
      nsrc (dst.toNat + 3 + st) := by
  have hv1 : s0.core.vals[litI.toNat]?.getD 0#8 = 1#8 := by
    have hdom := hw0.vals_domain litI.toNat hlitI_lt
    have hg : sC.core.vals[litI.toNat]?.getD 0#8 = sC.core.vals[litI.toNat]'hlitI_v := by
      rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some]
    have h1 : (0#32).slt ((sC.core.vals[litI.toNat]?.getD 0#8).signExtend 32) = true := by rwa [hg]
    rw [hvC] at h1; exact (bv8_gt0_of_dom hdom).1.mp h1
  obtain ⟨idx0, hidx0, hieq0⟩ := (hw0.vals_true_iff litI.toNat hlitI_lt).mp hv1
  have hr_src_L : sL.core.rsns[(s0.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src := by
    apply BitVec.eq_of_toNat_eq
    rw [bv32_ofNat_toNat (by omega), hieq0, ← hrC]; exact hrsn_eq
  have hr0_src : s0.core.rsns[(s0.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src := by
    have hm0' := hrmL idx0 hidx0; dsimp only at hm0'
    split at hm0'
    · rename_i hc1; rw [hr_src_L] at hm0'
      rcases hc1 with hff | hhi
      · rw [hff] at hm0'; have := congrArg BitVec.toNat hm0'
        rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
      · rw [← hm0'] at hhi
        exact absurd ((bv32_lt_highbit_iff _).mp
          (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8)) hhi
    · split at hm0'
      · rw [hr_src_L] at hm0'; have := hm0'.1
        rw [bv32_ofNat_toNat (by omega)] at this; omega
      · rw [hr_src_L] at hm0'; exact hm0'.symm
  have hdst_sw : dst.setWidth 32 = BitVec.ofNat 32 dst.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
  refine SweepReasonMapInv.congr_rsns_arena rfl rfl
    (SweepReasonMapInv.keep_step (kL := sL.core) hw0 hsrc_ref hnsrc64 hdst_src hsrc_lt8 hrmL hhapp
      (fun idx hidx hne => ?_) (fun idx hidx heq_s => ?_))
  · have hne_idx : idx ≠ idx0 := fun heq => hne (heq ▸ hr0_src)
    have hve_ne : (s0.core.trl[idx]?.getD 0#32).toNat / 2 ≠ litI.toNat / 2 := by
      intro hveq
      exact hne_idx (hw0.trail_vars_nodup idx idx0 hidx hidx0 (by rw [hveq, hieq0]))
    rw [hrs_eq, List.getElem?_set_ne (Ne.symm hve_ne), hrC]
  · have hid_eq := fullWitness_reason_unique hw0 hidx hidx0 hsrc_lt8 heq_s hr0_src
    subst hid_eq
    rw [hrs_eq, hieq0, List.getElem?_set_self (by omega), Option.getD_some, hdst_sw]

theorem m6_hit_rsn_mark_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL sC : FullState} {R : Mem 64 → Prop} {arH : List (BitVec 32)}
    {hdr0 litI : BitVec 32} {src dst nsrc st : BitVec 64} {old_sz : BitVec 32}
    {hcl_beq mark_allowed : Bool} {i : BitVec 32} {new_unit : Bool} {mS : Mem 64}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core)
    (hpre_vals : sPre.core.vals = s.core.vals) (hpre_cv : sPre.core.cur_vars = s.core.cur_vars)
    (hlenC0 : sC.LengthsOk c) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (_hcvL : sL.core.cur_vars = s.core.cur_vars)
    (harL_len : sL.core.arena.length = c.arena_cap)
    (harC_len : sC.core.arena.length = c.arena_cap)
    (harH_len : arH.length = c.arena_cap) (hszH : (arH[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (harH_0 : arH[dst.toNat]? = some (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)))
    (_hbodyH : ∀ j, dst.toNat + 3 ≤ j → arH[j]? = sC.core.arena[j]?)
    (hdropH : ((arH.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat =
      ((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)
    (hcmpH : CompactPrefixOk c F_cur s { sC.core with arena := arH } (dst.toNat + 3 + st.toNat))
    (hdst_inH : dst.toNat ∈ fullArenaClauseRefsCore
      { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat })
    (hfit_cap : dst.toNat + 3 + st.toNat ≤ c.arena_cap) (hdst_src : dst.toNat ≤ src.toNat)
    (hsrc_lt8 : src.toNat < 0x80000000) (hsrc_ref : src.toNat ∈ fullArenaClauseRefs sPre)
    (hnsrc64 : nsrc.toNat = fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat)
    (hsrc_fit_cap : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hsrc_lits_eq :
      ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore sPre.core src.toNat)
    (hout_ok0 : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz hcl_beq st)
    (hdec_cl0 : ∀ b : Bool,
      hcl_beq = b ↔ (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
    (happend_mk : ∀ rsns' : List (BitVec 32),
      fullArenaClauseLitsCore
          { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat } dst.toNat =
        fullArenaClauseLitsCore sPre.core src.toNat →
      SweepHappenedCore sPre.core sL.core
        { sL.core with arena := arH, rsns := rsns', arena_len := dst.toNat + 3 + st.toNat }
        dst.toNat src.toNat)
    (hbits :
      (((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32) &&& 0x00800000#32) =
        0#32 ∧
      (((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32) &&& 0x00080000#32) =
        0#32 ∧
      ((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00880000#32) = 0#32 ∧
      (((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32) &&& 0x00880000#32) =
        0#32 ∧
      ((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00400000#32) =
        (hdr0 &&& 0x00400000#32) ∧
      (((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32) &&& 0x00400000#32) =
        (hdr0 &&& 0x00400000#32))
    (hi_lt : i.toNat < st.toNat)
    (hlitI_lt : litI.toNat < 2 * s.core.cur_vars) (hlitI_v : litI.toNat < sC.core.vals.length)
    (hvI_r' : litI.toNat / 2 < sC.core.rsns.length)
    (hvg : (0#32).slt ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) = true)
    (hrsn_eq : (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = src.toNat)
    (hlitI_eq : arH[dst.toNat + 3 + i.toNat]?.getD 0#32 = litI)
    (hpos : 0 < s.core.cur_level)
    (hmS :
      (FullMem c { sC with core := { sC.core with
        arena := arH.set dst.toNat
          ((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) ||| 0x00200000#32)
        rsns := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32) } } ⋆ R) mS) :
    M6RsnBranchInv c F_cur s sPre sC R arH nsrc.toNat dst.toNat st.toNat mark_allowed () mS := by
  let nhdr := hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)
  let arR := arH.set dst.toNat (nhdr ||| 0x00200000#32)
  let rsnsR := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32)
  have hdst_lt_ar : dst.toNat < arH.length := by rw [harH_len]; omega
  obtain ⟨hcmpR, hrefsR, hclR⟩ :=
    m6_set_hdr_at_ref_preserves (k := { sC.core with arena := arH, rsns := rsnsR })
      hcmpH.with_rsns harH_len hfit_cap hdst_inH hbits.1 hbits.2.1
  have hrm_hit : ∀ hp : 0 < s.core.cur_level, SweepReasonMapInv sPre.core
      { sC.core with arena := arH, rsns := rsnsR } nsrc.toNat (dst.toNat + 3 + st.toNat) :=
    fun hp => by
      obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ :=
        sweep_pos_lits_eq hout_ok0 ((hdec_cl0 false).mpr hp) harL_len harC_len hsrc_fit_cap
          hdst_src hsrc_lits_eq hszH hdropH
      exact m6_sweep_rsn_hit_pos hwPre hsrc_ref hnsrc64 hdst_src hsrc_lt8
        (hposL.get hp).2.2.2.2.2.2 (happend_mk rsnsR hlits_eq) rfl
        (hvC.trans ((hposL.get hp).2.1.trans hpre_vals.symm)) hrC hlenC0.core_ok.rsns_len
        (hpre_cv ▸ hcv_le) (hpre_cv ▸ hlitI_lt) hlitI_v hvg hrsn_eq
  refine ⟨arR, rsnsR, by simp [arR, harH_len], by rw [List.length_set, hlenC0.core_ok.rsns_len],
    fun i hi => List.getElem?_set_ne (by omega), fun j hj => List.getElem?_set_ne (by omega),
    by dsimp [arR]; rw [List.getElem?_set_ne (by omega)]; exact hszH,
    by dsimp [arR]; rw [List.getElem?_set_self hdst_lt_ar, Option.getD_some]; exact hbits.2.2.2.1,
    by dsimp [arR]; rw [List.getElem?_set_self hdst_lt_ar, harH_0, Option.getD_some,
         Option.getD_some]; exact hbits.2.2.2.2.2.trans hbits.2.2.2.2.1.symm,
    hcmpR, hrefsR ▸ hdst_inH,
    fun idx hidx hlt => by
      by_cases hve : (sPre.core.trl[idx]?.getD 0#32).toNat / 2 = litI.toNat / 2
      · rw [hve, List.getElem?_set_self hvI_r', Option.getD_some, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega)] at hlt
        omega
      · dsimp [rsnsR]; rw [List.getElem?_set_ne (Ne.symm hve)],
    fun hcl0 => absurd hcl0 (by omega),
    fun hp => m6_set_hdr_preserves_srm hrefsR hclR (hrm_hit hp),
    fun hp _ idx hidx heq => ?_, hmS⟩
  obtain ⟨hvC, hrC⟩ := by
    have h1 := hout_ok0.1 ((hdec_cl0 false).mpr hp); exact And.intro h1.2.1 h1.2.2.2.2.1
  have hdst_sw64 : dst.setWidth 32 = (BitVec.ofNat 64 dst.toNat).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, bv64_ofNat_toNat_id (by omega)]
  dsimp [rsnsR] at heq; rw [hdst_sw64] at heq
  have hve_lit := m6_rsn_eq_lit_of_hit hwPre hdst_src hsrc_lt8 (hposL.get hp).2.2.2.2.2.2 hrC
    (hvC.trans ((hposL.get hp).2.1.trans hpre_vals.symm)) hlenC0.core_ok.rsns_len
    (hpre_cv ▸ hcv_le) (hpre_cv ▸ hlitI_lt) hlitI_v hvg hrsn_eq hidx heq
  refine ⟨(by
      dsimp [arR]; rw [List.getElem?_set_self hdst_lt_ar, Option.getD_some,
        BitVec.and_or_distrib_right,
        show (0x00200000#32 &&& 0x00200000#32) = 0x00200000#32 from rfl]
      intro h0; have := congrArg (·[21]) h0; simp at this),
    i.toNat, (by rw [List.getElem?_set_ne (by omega), hszH]; exact hi_lt), ?_⟩
  have hl_eq : arR[dst.toNat + 3 + i.toNat]?.getD 0#32 = litI := by
    dsimp [arR]; rw [List.getElem?_set_ne (by omega)]; exact hlitI_eq
  rw [hl_eq]; exact ⟨hve_lit.1.symm, hve_lit.2⟩

theorem m6_hit_rsn_nomark_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL sC : FullState} {R : Mem 64 → Prop} {arH : List (BitVec 32)}
    {hdr0 litI : BitVec 32} {src dst nsrc st first_red : BitVec 64} {old_sz : BitVec 32}
    {hcl_beq new_unit : Bool} {mS : Mem 64}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core)
    (hpre_vals : sPre.core.vals = s.core.vals) (hpre_cv : sPre.core.cur_vars = s.core.cur_vars)
    (hlikeC : M6SweepLike s sC)
    (hlenC0 : sC.LengthsOk c) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (_hcvL : sL.core.cur_vars = s.core.cur_vars)
    (harL_len : sL.core.arena.length = c.arena_cap)
    (harC_len : sC.core.arena.length = c.arena_cap)
    (harH_len : arH.length = c.arena_cap) (hszH : (arH[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (harH_0 : arH[dst.toNat]? = some (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)))
    (hdropH : ((arH.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat =
      ((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)
    (hcmpH : CompactPrefixOk c F_cur s { sC.core with arena := arH } (dst.toNat + 3 + st.toNat))
    (hdst_inH : dst.toNat ∈ fullArenaClauseRefsCore
      { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat })
    (hdst_src : dst.toNat ≤ src.toNat)
    (hsrc_lt8 : src.toNat < 0x80000000) (hsrc_ref : src.toNat ∈ fullArenaClauseRefs sPre)
    (hnsrc64 : nsrc.toNat = fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat)
    (hsrc_fit_cap : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hsrc_lits_eq :
      ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore sPre.core src.toNat)
    (hout_ok0 : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz hcl_beq st)
    (hdec_cl0 : ∀ b : Bool,
      hcl_beq = b ↔ (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
    (happend_mk : ∀ rsns' : List (BitVec 32),
      fullArenaClauseLitsCore
          { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat } dst.toNat =
        fullArenaClauseLitsCore sPre.core src.toNat →
      SweepHappenedCore sPre.core sL.core
        { sL.core with arena := arH, rsns := rsns', arena_len := dst.toNat + 3 + st.toNat }
        dst.toNat src.toNat)
    (hflH : ((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00880000#32) = 0#32)
    (hlitI_lt : litI.toNat < 2 * s.core.cur_vars) (hlitI_v : litI.toNat < sC.core.vals.length)
    (hvI_r' : litI.toNat / 2 < sC.core.rsns.length) (hdst_lt8 : dst.toNat < 0x80000000)
    (hvg : (0#32).slt ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) = true)
    (hrsn_eq : (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = src.toNat)
    (hnomark : s.core.cur_level = 0 ∨
      (first_red = 0xFFFFFFFF#64 ∧ (hdr0 &&& 0x00400000#32) = 0#32))
    (hmS :
      (FullMem c { sC with core := { sC.core with
        arena := arH
        rsns := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32) } } ⋆ R) mS) :
    let mark_allowed := !(decide (s.core.cur_level = 0)) &&
      (decide (first_red ≠ 0xFFFFFFFF#64) || decide ((hdr0 &&& 0x00400000#32) ≠ 0#32))
    M6RsnBranchInv c F_cur s sPre sC R arH nsrc.toNat dst.toNat st.toNat mark_allowed () mS := by
  let rsnsR := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32)
  have hrm_hit : ∀ hpos : 0 < s.core.cur_level,
      SweepReasonMapInv sPre.core { sC.core with arena := arH, rsns := rsnsR }
        nsrc.toNat (dst.toNat + 3 + st.toNat) := fun hpos => by
    obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ :=
      sweep_pos_lits_eq hout_ok0 ((hdec_cl0 false).mpr hpos) harL_len harC_len hsrc_fit_cap
        hdst_src hsrc_lits_eq hszH hdropH
    exact m6_sweep_rsn_hit_pos hwPre hsrc_ref hnsrc64 hdst_src hsrc_lt8 (hposL.get hpos).2.2.2.2.2.2
      (happend_mk rsnsR hlits_eq) rfl (hvC.trans ((hposL.get hpos).2.1.trans hpre_vals.symm)) hrC
      hlenC0.core_ok.rsns_len (hpre_cv ▸ hcv_le) (hpre_cv ▸ hlitI_lt) hlitI_v hvg hrsn_eq
  refine ⟨arH, rsnsR, harH_len, by rw [List.length_set, hlenC0.core_ok.rsns_len],
    fun _ _ => rfl, fun _ _ => rfl, hszH,
    by rw [harH_0, Option.getD_some]; exact hflH, rfl, hcmpH.with_rsns, hdst_inH,
    fun idx hidx hlt => by
      by_cases hve : (sPre.core.trl[idx]?.getD 0#32).toNat / 2 = litI.toNat / 2
      · rw [hve, List.getElem?_set_self hvI_r', Option.getD_some, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega)] at hlt
        omega
      · dsimp [rsnsR]; rw [List.getElem?_set_ne (Ne.symm hve)],
    fun hcl0 => by
      have hrt := (hout_ok0.2 ((hdec_cl0 true).mpr hcl0)).1
      exact False.elim (sweep_rsn_hit_false_at_root hrt (hlikeC.unchanged.2.2.1.trans hcl0)
        (by rw [hlikeC.unchanged.1]; exact hlitI_lt) hlitI_v hlenC0.core_ok.rsns_len
        (by rw [hlikeC.unchanged.1]; exact hcv_le) hsrc_lt8 hvg hrsn_eq),
    hrm_hit, fun hp hma => ?_, hmS⟩
  exfalso
  have hcl_ne : s.core.cur_level ≠ 0 := by omega
  simp only [decide_eq_false hcl_ne, Bool.not_false, Bool.true_and, Bool.or_eq_true,
    decide_eq_true_eq] at hma
  rcases hnomark with hcl0 | ⟨rfl, hred0⟩
  · omega
  · rcases hma with hfr_ne | hred_ne
    · exact hfr_ne rfl
    · exact hred_ne hred0

theorem m6_sweep_end_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL : FullState} {start dst : BitVec 64} {_rwL : Nat} {new_unit : Bool}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core)
    (hpre_eq : sPre.core = { s.core with arena := sPre.core.arena })
    (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hdst_le : dst.toNat ≤ s.core.arena_len)
    (hdm0 : s.core.dense_mode = 0#64)
    (hcvL : sL.core.cur_vars = s.core.cur_vars)
    (halL : sL.core.arena_len = s.core.arena_len)
    (hclL : sL.core.cur_level = s.core.cur_level)
    (hdmL : sL.core.dense_mode = s.core.dense_mode)
    (hftL : sL.core.frame_trail = s.core.frame_trail)
    (hfdL : sL.core.frame_dec = s.core.frame_dec)
    (hincL : sL.core.inconsistent = s.core.inconsistent)
    (harL_len : sL.core.arena.length = c.arena_cap)
    (hst_dst : start.toNat ≤ dst.toNat)
    (hlenL : sL.LengthsOk c)
    (hcmpL : CompactPrefixOk c F_cur s sL.core dst.toNat)
    (hcmpL_st : CompactPrefixOk c F_cur s sL.core start.toNat)
    (hlayL : WatchStackLayout sL.core)
    (hltL : ∀ l < 2 * sL.core.cur_vars,
      WatchSliceLtOk start.toNat F_cur sL.core l (fullWatchOff sL l) (fullWatchSize sL l))
    (hrootL : M6SweepLoopRootOk c F0 F_cur s sL start.toNat dst.toNat new_unit)
    (hposL : M6SweepLoopPosOk s sPre sL s.core.arena_len dst.toNat new_unit) :
    FullWitnessInv c F0 F_cur { sL.core with arena_len := dst.toNat } := by
  by_cases hcl0 : s.core.cur_level = 0
  · exact (hrootL.get hcl0).2.1
  · obtain ⟨_, hv, hl, ht, htp, hte, hrmL⟩ := hposL.get (Nat.pos_of_ne_zero hcl0)
    exact SweepReasonMapInv.toFullWitnessInvLt (c := c) (F0 := F0) (F_cur := F_cur)
      (k0 := sPre.core) (kL := { sL.core with arena_len := dst.toNat })
      (keep := start.toNat) (dst := dst.toNat)
      ({ hlenL.core_ok with arena_len_le := by dsimp; omega } :
        FullCoreState.LengthsOk c { sL.core with arena_len := dst.toNat })
      hwPre hcmpL.1 (fun _ => hdmL.trans hdm0) (hlayL.with_wstk rfl rfl rfl rfl)
      (fun l hl => (hltL l hl).relocate (k := sL.core)
        (k' := { sL.core with arena_len := dst.toNat })
        (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
        (m6_refs_lt_prefix_transfer hcmpL_st
          (k' := { sL.core with arena_len := dst.toNat })
          rfl harL_len harL_len (by omega) (by omega) (by omega) (fun _ _ => rfl)).2
        (fun _ _ => rfl))
      (fun _ hr _ => hr)
      (by dsimp only; rw [hv, hpre_eq]) (by dsimp only; rw [hl, hpre_eq])
      (by dsimp only; rw [ht, hpre_eq]) (by dsimp only; rw [htp, hpre_eq])
      (by dsimp only; rw [hte, hpre_eq]) (by dsimp only; rw [hclL, hpre_eq])
      (by dsimp only; rw [hcvL, hpre_eq]) (by dsimp only; rw [hftL, hpre_eq])
      (by dsimp only; rw [hfdL, hpre_eq]) (by dsimp only; rw [hincL, hpre_eq])
      (by
        have hal_pre : sPre.core.arena_len = s.core.arena_len := by rw [hpre_eq]
        exact hal_pre ▸ hrmL)

theorem m6_post_ll_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sM : FullState} {R : Mem 64 → Prop}
    {vM : List (BitVec 8)} {fM lM rM tM tpM wvM wsM arM llL : List (BitVec 32)}
    {teM wlM : Nat} {uM ufM wuM frM nbM oomM dst irred redd : BitVec 64} {mL : Mem 64}
    (hcoreM : sM.core =
      { s.core with
        vals := vM, flags := fM, lvl := lM, rsns := rM, trl := tM, trail_pos := tpM,
        trail_end := teM, unassigned := uM, unflushed := ufM, wvec := wvM, wstk := wsM,
        arena := arM, wlen := wlM, wusable := wuM, first_reducible := frM, num_binary := nbM,
        oom := oomM })
    (hlenM : sM.LengthsOk c) (hdst_cap : dst.toNat ≤ c.arena_cap) (hllL : llL.length = 16)
    (hallL : ∀ j < 16, llL[j]? = some 0xFFFFFFFF#32)
    (hwM : FullWitnessInv c F0 F_cur { sM.core with arena_len := dst.toNat })
    (hnoM : ∀ r ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat },
      (fullArenaHdrCore { sM.core with arena_len := dst.toNat } r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseGarbCore { sM.core with arena_len := dst.toNat } r = false)
    (hndM : FullArenaVarsNodup s →
      ∀ r ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat },
        ((fullArenaClauseLitsCore { sM.core with arena_len := dst.toNat } r).map (· / 2)).Nodup)
    (hnd0 : FullArenaVarsNodup s)
    (start : Nat) (hstM0 : start < dst.toNat →
      start ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat })
    (hmRaw : (FullMem c
      { core := { sM.core with arena_len := dst.toNat, arena_garbage := 0#64,
                               num_irred := irred, num_redundant := redd }
        scratch := { sM.scratch with last_learned := llL } } ⋆ R) mL) :
    let scLL : FullScratch := { sM.scratch with last_learned := llL }
    let sLL : FullState :=
      { core :=
          { s.core with
            vals := vM, flags := fM, lvl := lM, rsns := rM, trl := tM, trail_pos := tpM,
            trail_end := teM, unassigned := uM, unflushed := ufM, wvec := wvM, wstk := wsM,
            arena := arM, arena_len := dst.toNat, wlen := wlM, wusable := wuM,
            arena_garbage := 0#64, first_reducible := frM, num_irred := irred,
            num_redundant := redd, num_binary := nbM, oom := oomM },
        scratch := scLL }
    sLL.LengthsOk c ∧ FullLastLearnedWf sLL ∧ FullWitnessInv c F0 F_cur sLL.core ∧
    FullArenaVarsNodup sLL ∧
    (∀ r ∈ fullArenaClauseRefs sLL,
      (fullArenaHdr sLL r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb sLL r = false) ∧
    (start < sLL.core.arena_len → start ∈ fullArenaClauseRefs sLL) ∧
    (FullMem c sLL ⋆ R) mL := by
  let scLL : FullScratch := { sM.scratch with last_learned := llL }
  let sLL : FullState :=
    { core :=
        { s.core with
          vals := vM, flags := fM, lvl := lM, rsns := rM, trl := tM, trail_pos := tpM,
          trail_end := teM, unassigned := uM, unflushed := ufM, wvec := wvM, wstk := wsM,
          arena := arM, arena_len := dst.toNat, wlen := wlM, wusable := wuM,
          arena_garbage := 0#64, first_reducible := frM, num_irred := irred,
          num_redundant := redd, num_binary := nbM, oom := oomM },
      scratch := scLL }
  have hsM_dst : { sM.core with arena_len := dst.toNat } =
      { sLL.core with
        arena_garbage := s.core.arena_garbage, num_irred := s.core.num_irred,
        num_redundant := s.core.num_redundant } := by rw [hcoreM]
  have hlenLL : sLL.LengthsOk c :=
    ⟨by have hc_ok := m6_core_lengths_upd hlenM.core_ok hdst_cap 0#64 frM irred redd
        rwa [hcoreM] at hc_ok,
     { hlenM.scratch_ok with last_learned_len := hllL }⟩
  have hll_wf : FullLastLearnedWf sLL :=
    fullLastLearnedWf_of_all_sentinel (fun j hj => hallL j (by omega))
  have hwLL : FullWitnessInv c F0 F_cur sLL.core := by
    simpa [sLL] using m6_witness_upd_stats (hsM_dst ▸ hwM) 0#64 irred redd
  have hndLL : FullArenaVarsNodup sLL := fun r hr _ => by
    have h1 : r ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat } := by
      change r ∈ fullArenaClauseRefsCore sLL.core at hr; rw [hsM_dst]; exact hr
    have h2 := hndM hnd0 r h1
    change ((fullArenaClauseLitsCore sLL.core r).map (· / 2)).Nodup
    have h3 : fullArenaClauseLitsCore sLL.core r =
        fullArenaClauseLitsCore { sM.core with arena_len := dst.toNat } r := by
      rw [hsM_dst]; rfl
    rw [h3]; exact h2
  have hnoLL : ∀ r ∈ fullArenaClauseRefs sLL,
      (fullArenaHdr sLL r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb sLL r = false :=
    fun r hr => by
      have hrM : r ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat } := by
        change r ∈ fullArenaClauseRefsCore sLL.core at hr; rw [hsM_dst]; exact hr
      have h1 := hnoM r hrM
      change (fullArenaHdrCore sLL.core r &&& 0x00800000#32) = 0#32 ∧
        fullArenaClauseGarbCore sLL.core r = false
      have h2 : fullArenaHdrCore sLL.core r =
          fullArenaHdrCore { sM.core with arena_len := dst.toNat } r := by rw [hsM_dst]; rfl
      have h3 : fullArenaClauseGarbCore sLL.core r =
          fullArenaClauseGarbCore { sM.core with arena_len := dst.toNat } r := by
        rw [hsM_dst]; rfl
      rw [h2, h3]; exact h1
  have hstLL_in : start < sLL.core.arena_len → start ∈ fullArenaClauseRefs sLL := fun hlt => by
    change start ∈ fullArenaClauseRefsCore sLL.core
    have h1 := hstM0 (by change start < dst.toNat at hlt; omega)
    rw [hcoreM] at h1; exact h1
  have hmLL : (FullMem c sLL ⋆ R) mL := by
    let cLL : FullCoreState :=
      { sM.core with
        arena_len := dst.toNat, arena_garbage := 0#64, num_irred := irred, num_redundant := redd }
    have h1 : ({ core := cLL, scratch := scLL } : FullState) = sLL :=
      congrArg (fun k =>
        ({ core := { k with arena_len := dst.toNat, arena_garbage := 0#64,
                            num_irred := irred, num_redundant := redd },
           scratch := scLL } : FullState)) hcoreM
    rwa [← h1]
  exact ⟨hlenLL, hll_wf, hwLL, hndLL, hnoLL, hstLL_in, hmLL⟩

theorem m6_clear_fall_step {c : FullCfg} {F_cur : List (List Nat)}
    {s sPre sE sE1 : FullState} {R : Mem 64 → Prop} {arL : List (BitVec 32)}
    {cp first_red dst : BitVec 64} {rwTl : Nat} {m : Mem 64}
    (hsE1 : sE1 = { sE with core := { sE.core with first_reducible := first_red } })
    (hfr_cp : first_red.toNat ≤ cp.toNat) (hcp_lt : cp.toNat < dst.toNat)
    (hal_le : s.core.arena_len ≤ c.arena_cap) (hdst_le : dst.toNat ≤ s.core.arena_len)
    (harL_l : arL.length = c.arena_cap)
    (hpreL : ∀ i, i < first_red.toNat → arL[i]? = sE.core.arena[i]?)
    (htailL : ∀ i, cp.toNat ≤ i → i < dst.toNat → arL[i]? = sE.core.arena[i]?)
    (hp3 : cp.toNat + 3 ≤ dst.toNat)
    (hfl : (sE.core.arena[cp.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hsz : 3 ≤ (sE.core.arena[cp.toNat + 2]?.getD 0#32).toNat)
    (hfit : cp.toNat + 3 + (sE.core.arena[cp.toNat + 2]?.getD 0#32).toNat ≤ dst.toNat)
    (htl : MoveRangeChain sE.core.arena
      (cp.toNat + 3 + (sE.core.arena[cp.toNat + 2]?.getD 0#32).toNat) dst.toNat rwTl)
    (hcp_in : cp.toNat ∈ fullArenaClauseRefsCore
      { sE1.core with arena := arL, arena_len := dst.toNat })
    (hcmpL : CompactPrefixOk c F_cur s { sE1.core with arena := arL } dst.toNat)
    (hrmL : 0 < s.core.cur_level →
      SweepReasonMapInv sPre.core { sE1.core with arena := arL } sPre.core.arena_len dst.toNat)
    (hrefsL : fullArenaClauseRefsCore { sE1.core with arena := arL, arena_len := dst.toNat } =
      fullArenaClauseRefsCore { sE1.core with arena_len := dst.toNat })
    (hm : (FullMem c { sE1 with core := { sE1.core with
      arena := arL.set cp.toNat (arL[cp.toNat]' (by omega) &&& ~~~0x00200000#32) } } ⋆ R) m) :
    let sz32 := arL[(cp + 2#64).toNat]'(by
      have := bv64_add2_lt (x := cp) (by omega); omega)
    (cp + 3#64 + sz32.setWidth 64).toNat = cp.toNat + 3 + sz32.toNat ∧
    sz32.toNat = (sE.core.arena[cp.toNat + 2]?.getD 0#32).toNat ∧
    M6ClearFallInv c F_cur s sPre sE1 R first_red.toNat dst.toNat
      (cp + 3#64 + sz32.setWidth 64) m := by
  have hcp2_eq : (cp + 2#64).toNat = cp.toNat + 2 := bv64_add2_lt (by omega)
  have hcp_lt_ar : cp.toNat < arL.length := by omega
  have hcp2_lt_ar : (cp + 2#64).toNat < arL.length := by rw [hcp2_eq]; omega
  let hdrL := arL[cp.toNat]'hcp_lt_ar
  let sz32 := arL[(cp + 2#64).toNat]'hcp2_lt_ar
  have hsz_eq : sz32.toNat = (sE.core.arena[cp.toNat + 2]?.getD 0#32).toNat := by
    have h1 := htailL (cp.toNat + 2) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega : cp.toNat + 2 < arL.length)] at h1
    have h2 := congrArg (fun o => (o.getD 0#32).toNat) h1
    dsimp only [sz32]; simp only [hcp2_eq]
    simpa only [Option.getD_some] using h2
  have hhdr_eq : hdrL = sE.core.arena[cp.toNat]?.getD 0#32 := by
    have h1 := htailL cp.toNat (Nat.le_refl _) hcp_lt
    rw [List.getElem?_eq_getElem hcp_lt_ar] at h1
    symm at h1; dsimp only [hdrL]; rw [h1, Option.getD_some]
  have hcp_nxt : (cp + 3#64 + sz32.setWidth 64).toNat = cp.toNat + 3 + sz32.toNat :=
    bv64_add3_zext_lt (by omega)
  let arL' := arL.set cp.toNat (hdrL &&& ~~~0x00200000#32)
  have hsh_new : ((hdrL &&& ~~~0x00200000#32) &&& 0x00800000#32) = 0#32 := by
    rw [BitVec.and_assoc,
      show (~~~0x00200000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl, hhdr_eq]
    have h1 : (sE.core.arena[cp.toNat]?.getD 0#32 &&& (0x00880000#32 &&& 0x00800000#32)) =
        0#32 := by
      rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
    rwa [show (0x00880000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl] at h1
  have hgb_new : ((hdrL &&& ~~~0x00200000#32) &&& 0x00080000#32) = 0#32 := by
    rw [BitVec.and_assoc,
      show (~~~0x00200000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl, hhdr_eq]
    have h1 : (sE.core.arena[cp.toNat]?.getD 0#32 &&& (0x00880000#32 &&& 0x00080000#32)) =
        0#32 := by
      rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
    rwa [show (0x00880000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl] at h1
  obtain ⟨hcmpL', hrefs', hcl'⟩ := m6_set_hdr_at_ref_preserves hcmpL harL_l
    (Nat.le_trans hdst_le hal_le) hcp_in hsh_new hgb_new
  have hrmL' : 0 < s.core.cur_level → SweepReasonMapInv sPre.core
      { sE1.core with arena := arL' } sPre.core.arena_len dst.toNat :=
    fun hp => m6_set_hdr_preserves_srm hrefs' hcl' (hrmL hp)
  have hnx_eq : fullArenaNextOff arL' dst.toNat cp.toNat = cp.toNat + 3 + sz32.toNat := by
    have hsh_ar : (arL'[cp.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
      dsimp only [arL']; rw [List.getElem?_set_self hcp_lt_ar, Option.getD_some]; exact hsh_new
    have hsz_ar : (arL'[cp.toNat + 2]?.getD 0#32).toNat = sz32.toNat := by
      dsimp only [arL']; rw [List.getElem?_set_ne (by omega)]
      have := htailL (cp.toNat + 2) (by omega) (by omega); rw [this, ← hsz_eq]
    unfold fullArenaNextOff
    simp [show ¬ (cp.toNat + 3 > dst.toNat) by omega, hsz_ar,
      show ¬ (cp.toNat + 3 + sz32.toNat > dst.toNat) by omega, hsh_ar]
  have hnxt_in : cp.toNat + 3 + sz32.toNat < dst.toNat →
      cp.toNat + 3 + sz32.toNat ∈
        fullArenaClauseRefsCore { sE1.core with arena := arL', arena_len := dst.toNat } :=
    fun hlt => by
      have hor := fullArenaClauseRefs_next_or_end hcmpL'.1 (hrefs' ▸ hcp_in)
      dsimp only at hor; rw [hnx_eq] at hor; exact hor.resolve_left (by omega)
  have htl' : MoveRangeChain sE1.core.arena (cp.toNat + 3 + sz32.toNat) dst.toNat rwTl := by
    rw [hsE1, hsz_eq]; exact htl
  refine ⟨hcp_nxt, hsz_eq, by rw [hcp_nxt]; omega,
    by rw [hcp_nxt, hsz_eq]; exact hfit, arL', rwTl,
    by simp [arL', harL_l],
    fun i hi => by rw [List.getElem?_set_ne (by omega), hsE1]; exact hpreL i hi,
    fun i hi1 hi2 => by
      rw [List.getElem?_set_ne (by rw [hcp_nxt] at hi1; omega), hsE1]
      exact htailL i (by rw [hcp_nxt] at hi1; omega) hi2,
    by rw [hcp_nxt]; exact htl', hcmpL', hrmL', hrefs'.trans hrefsL,
    fun hlt => by rw [hcp_nxt] at hlt ⊢; exact hnxt_in hlt, hm⟩

open Classical in
theorem m6_move_red_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sE : FullState} {R : Mem 64 → Prop} {start dst first_red fred' : BitVec 64}
    {rwE rwOut : Nat} {unsat new_unit : Bool} {arM rsnsM : List (BitVec 32)} {sc' : FullScratch}
    {mM : Mem 64}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core)
    (hpre_eq : sPre.core = { s.core with arena := sPre.core.arena })
    (hwEnd : FullWitnessInv c F0 F_cur { sE.core with arena_len := dst.toNat })
    (_hnd0 : FullArenaVarsNodup s) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hdst_le : dst.toNat ≤ s.core.arena_len) (hdm0 : s.core.dense_mode = 0#64)
    (hfr_lt_dst : first_red.toNat < dst.toNat) (hfr_st : start.toNat ≤ first_red.toNat)
    (hlikeE : M6SweepLike s sE) (hlenE : sE.LengthsOk c)
    (hcvE : sE.core.cur_vars = s.core.cur_vars) (halE : sE.core.arena_len = s.core.arena_len)
    (hclE : sE.core.cur_level = s.core.cur_level) (hdmE : sE.core.dense_mode = s.core.dense_mode)
    (hftE : sE.core.frame_trail = s.core.frame_trail) (hfdE : sE.core.frame_dec = s.core.frame_dec)
    (hincE : sE.core.inconsistent = s.core.inconsistent)
    (helE : sE.scratch.extend_len = s.scratch.extend_len)
    (hws2E : sE.scratch.work_stk2 = s.scratch.work_stk2)
    (harE_len : sE.core.arena.length = c.arena_cap)
    (hcmpE : CompactPrefixOk c F_cur s sE.core dst.toNat)
    (hcmpE_st : CompactPrefixOk c F_cur s sE.core start.toNat)
    (hcmpE_fr : CompactPrefixOk c F_cur s sE.core first_red.toNat)
    (_hrw_pos : 0 < rwE) (hmvE : MoveRangeChain sE.core.arena first_red.toNat dst.toNat rwE)
    (hfr_inE : first_red.toNat ∈ fullArenaClauseRefsCore { sE.core with arena_len := dst.toNat })
    (hrs_mk : M6ReasonMarkRange sPre sE first_red.toNat dst.toNat)
    (hlayE : WatchStackLayout sE.core)
    (hltE : ∀ l < 2 * sE.core.cur_vars,
      WatchSliceLtOk start.toNat F_cur sE.core l (fullWatchOff sE l) (fullWatchSize sE l))
    (hstE_in : start.toNat < dst.toNat →
      start.toNat ∈ fullArenaClauseRefsCore { sE.core with arena_len := dst.toNat })
    (hrmE : 0 < s.core.cur_level →
      SweepReasonMapInv sPre.core sE.core sPre.core.arena_len dst.toNat)
    (hunsatE : unsat = true → s.core.cur_level = 0 ∧ F0.Unsat)
    (hunitE : new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sE.core.trail_end)
    (hposE : 0 < s.core.cur_level → unsat = false ∧ new_unit = false ∧
      sE.core.vals = s.core.vals ∧ sE.core.lvl = s.core.lvl ∧ sE.core.trl = s.core.trl ∧
      sE.core.trail_pos = s.core.trail_pos ∧ sE.core.trail_end = s.core.trail_end)
    (harM_l : arM.length = c.arena_cap) (hrsnsM_l : rsnsM.length = c.max_vars)
    (hscM_ok : sc'.LengthsOk c) (helM : sc'.extend_len = sE.scratch.extend_len)
    (hws2M : sc'.work_stk2 = sE.scratch.work_stk2)
    (hpreM : ∀ i < first_red.toNat, arM[i]? = sE.core.arena[i]?)
    (hmvM : MoveRangeChain arM first_red.toNat dst.toNat rwOut)
    (hblkM : ∀ r, RefInChain arM first_red.toNat dst.toNat r →
      let sz := (arM[r + 2]?.getD 0#32).toNat
      (arM[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src0, RefInChain sE.core.arena first_red.toNat dst.toNat src0 ∧
        (sE.core.arena[src0 + 2]?.getD 0#32).toNat = sz ∧
        ∀ j < sz, arM[r + 3 + j]? = sE.core.arena[src0 + 3 + j]?)
    (hrsnsM : ∀ v < sE.core.cur_vars,
      let r0 := sE.core.rsns[v]?.getD 0xFFFFFFFF#32
      if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
          RefInChain sE.core.arena first_red.toNat dst.toNat r0.toNat ∧
          (sE.core.arena[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j < (sE.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
            let lit := (sE.core.arena[r0.toNat + 3 + j]?.getD 0#32).toNat
            lit / 2 = v ∧ sE.core.vals[lit]?.getD 0#8 = 1#8
      then
        let r' := (rsnsM[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
        RefInChain arM first_red.toNat dst.toNat r' ∧
        (arM[r' + 2]?.getD 0#32).toNat = (sE.core.arena[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (sE.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
          arM[r' + 3 + j]? = sE.core.arena[r0.toNat + 3 + j]?
      else rsnsM[v]?.getD 0xFFFFFFFF#32 = r0)
    (hmM : (FullMem c { sE with core := { sE.core with arena := arM, rsns := rsnsM,
                                                        first_reducible := fred' }
                                scratch := sc' } ⋆ R) mM) :
    M6PostMoveInv c F0 F_cur s R start.toNat dst unsat new_unit () mM := by
  let sM : FullState :=
    { sE with
      core := { sE.core with arena := arM, rsns := rsnsM, first_reducible := fred' }
      scratch := sc' }
  have hlikeM : M6PostLike s sM := by
    rcases hlikeE with ⟨v, f, l, r, t, tp, te, u, uf, wv, ws, _, wl, wu, nb, o, _, _, hEq⟩
    exact ⟨v, f, l, rsnsM, t, tp, te, u, uf, wv, ws, arM, wl, wu, fred', nb, o,
      by rw [show sM.core = { sE.core with arena := arM, rsns := rsnsM,
                                           first_reducible := fred' } from rfl, hEq]⟩
  have hlenM : sM.LengthsOk c :=
    ⟨{ hlenE.core_ok with arena_len_arr := harM_l, rsns_len := hrsnsM_l }, hscM_ok⟩
  have hmvM_refs :
      first_red.toNat ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat } := by
    have hcmpM_fr := (arenaPrefix_preserves_compact
      (k' := { sM.core with arena_len := first_red.toNat }) hcmpE_fr rfl harE_len harM_l
      (by omega) (fun i hi => hpreM i (by omega))).1
    generalize hfr_nat : first_red.toNat = frn at hmvM
    cases hmvM with
    | empty => omega
    | step h3 hfl hsz hfit _ =>
      rw [← hfr_nat] at h3 hfl hsz hfit
      have hsh : (arM[first_red.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
        have h1 :
            (arM[first_red.toNat]?.getD 0#32 &&& (0x00880000#32 &&& 0x00800000#32)) = 0#32 := by
          rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
        rwa [show (0x00880000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl] at h1
      have hgb : (arM[first_red.toNat]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
        have h1 :
            (arM[first_red.toNat]?.getD 0#32 &&& (0x00880000#32 &&& 0x00080000#32)) = 0#32 := by
          rw [← BitVec.and_assoc, hfl, BitVec.zero_and]
        rwa [show (0x00880000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl] at h1
      have hlen_sub : fullArenaClauseRefsCore
          { sM.core with arena_len := first_red.toNat + 3 +
            (arM[first_red.toNat + 2]?.getD 0#32).toNat } =
          fullArenaClauseRefsCore
            { sM.core with arena_len := first_red.toNat } ++ [first_red.toNat] :=
        fullArenaClauseRefsCore_append hcmpM_fr.1 hsz rfl (fun _ _ => rfl) hsh rfl
      have hfr_in_step : first_red.toNat ∈ fullArenaClauseRefsCore
          { sM.core with arena_len := first_red.toNat + 3 +
            (arM[first_red.toNat + 2]?.getD 0#32).toNat } := by
        rw [hlen_sub, List.mem_append, List.mem_singleton]; exact Or.inr rfl
      have ha_step : FullArenaClausesInv c F_cur
          { sM.core with arena_len := first_red.toNat + 3 +
            (arM[first_red.toNat + 2]?.getD 0#32).toNat } := by
        obtain ⟨_, src0, hsrc0_ch, hsz_e, hlits_e⟩ := hblkM first_red.toNat (.head h3 hfl hsz hfit)
        have hsrc0_mem := m6_refInChain_mem_refs hcmpE.1 first_red.toNat rwE hmvE
          (Or.inr hfr_inE) src0 hsrc0_ch
        have hwf0 := hcmpE.1.refs_wf src0 hsrc0_mem
        have hbd0 :
            src0 + 3 + fullArenaClauseSizeCore { sE.core with arena_len := dst.toNat } src0 ≤
              sE.core.arena.length := by
          unfold fullArenaClauseSizeCore; rw [harE_len]
          exact Nat.le_trans hwf0.2.2.1 (Nat.le_trans hwf0.2.2.2.1 (Nat.le_trans hdst_le hal_le))
        have hbd0' : src0 + 3 + (sE.core.arena[src0 + 2]?.getD 0#32).toNat ≤
            sE.core.arena.length := hbd0
        have hlits_lt0 : ∀ j < (arM[first_red.toNat + 2]?.getD 0#32).toNat,
            (arM[first_red.toNat + 3 + j]?.getD 0#32).toNat < 2 * sM.core.cur_vars := fun j hj => by
          have hj' : j < (sE.core.arena[src0 + 2]?.getD 0#32).toNat := by omega
          rw [hlits_e j (hsz_e ▸ hj'),
            List.getElem?_eq_getElem (by omega : src0 + 3 + j < sE.core.arena.length),
            Option.getD_some]
          exact hcmpE.1.lits_lt src0 hsrc0_mem (hcmpE.2.1 src0 hsrc0_mem).2 _
            ((mem_fullArenaClauseLitsCore_iff hbd0).mpr ⟨j, hj', rfl⟩)
        have hent0 : (cnfOfClauses F_cur).EntailsClause
            (cnfClause (((arM.drop (first_red.toNat + 3)).take
              (arM[first_red.toNat + 2]?.getD 0#32).toNat).map BitVec.toNat)) := by
          have hl_eq : ((arM.drop (first_red.toNat + 3)).take
                (arM[first_red.toNat + 2]?.getD 0#32).toNat).map BitVec.toNat =
              fullArenaClauseLitsCore { sE.core with arena_len := dst.toNat } src0 := by
            unfold fullArenaClauseLitsCore
            rw [show fullArenaClauseSizeCore { sE.core with arena_len := dst.toNat } src0 =
                (sE.core.arena[src0 + 2]?.getD 0#32).toNat from rfl, hsz_e]
            congr 1; apply List.ext_getElem
            · simp [harM_l, harE_len]; omega
            · intro j hj1 _
              have hj' : j < (sE.core.arena[src0 + 2]?.getD 0#32).toNat := by
                simp [harM_l] at hj1; omega
              simp only [List.getElem_take, List.getElem_drop]
              have h1 := hlits_e j (hsz_e ▸ hj')
              rw [List.getElem?_eq_getElem (by omega : first_red.toNat + 3 + j < arM.length),
                  List.getElem?_eq_getElem (by omega : src0 + 3 + j < sE.core.arena.length)] at h1
              exact Option.some.inj h1
          rw [hl_eq]
          exact hcmpE.1.entails src0 hsrc0_mem (hcmpE.2.1 src0 hsrc0_mem).2
        exact (compactArena_append_block hcmpM_fr.1 hcmpM_fr.2.1 rfl hsz harM_l harM_l
          (by omega) (fun _ _ => rfl) hsh hgb rfl hlits_lt0 hent0).2.1
      rw [← hfr_nat]
      exact (fullArenaClauseRefsCore_mono_prefix hfit ha_step _ hfr_in_step).1
  obtain ⟨hcmpM, hrmM⟩ := move_red_end_compact_and_rsn hwPre hcmpE hcmpE_fr harE_len
    harM_l hrsnsM_l hfr_lt_dst (Nat.le_trans hdst_le hal_le) hfr_inE hmvE hmvM
    hpreM (fun r hr => let ⟨h0, src0, hs0, hsz0, hl0⟩ := hblkM r hr
      ⟨h0, src0, hs0, hsz0.symm, fun j hj => hl0 j (hsz0 ▸ hj)⟩)
    hrmE (fun hpos => hrs_mk.get (by rw [hpre_eq]; exact hpos))
    (by rw [hcvE, hpre_eq]) hwPre.trail_lits_lt hrsnsM
  have hcmpM' : CompactPrefixOk c F_cur s sM.core dst.toNat :=
    (arenaPrefix_preserves_compact (k' := sM.core) hcmpM rfl harM_l harM_l
      (Nat.le_trans hdst_le hal_le) (fun _ _ => rfl)).1
  let kM_dst : FullCoreState := { sM.core with arena_len := dst.toNat }
  have hcmpE_st_dst :
      CompactPrefixOk c F_cur s { sE.core with arena_len := dst.toNat } start.toNat :=
    (arenaPrefix_preserves_compact (k' := { sE.core with arena_len := dst.toNat })
      hcmpE_st rfl harE_len harE_len (by omega) (fun _ _ => rfl)).1
  obtain ⟨_, hkeep_st⟩ := m6_refs_lt_prefix_transfer
    (k := { sE.core with arena_len := dst.toNat }) (k' := kM_dst) hcmpE_st_dst
    rfl harE_len harM_l (by dsimp; omega) (by dsimp [kM_dst]; omega)
    (by omega) (fun i hi => hpreM i (by omega))
  have hltM : ∀ l < 2 * kM_dst.cur_vars,
      WatchSliceLtOk start.toNat F_cur kM_dst l
        (fullWatchOffCore kM_dst l) (fullWatchSizeCore kM_dst l) := fun l hl =>
    (hltE l hl).relocate (k := sE.core) (k' := kM_dst)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun r hr hrlt =>
        hkeep_st r (m6_refs_lt_compactPrefix hcmpE
          (by rw [halE]; exact hdst_le) r hr (by omega)) hrlt)
      (fun _ _ => rfl)
  have hlayM : WatchStackLayout kM_dst := hlayE.with_wstk rfl rfl rfl rfl
  have hcoreM_ok : FullCoreState.LengthsOk c kM_dst :=
    { hlenM.core_ok with arena_len_le := by dsimp [kM_dst]; omega }
  have hwM : FullWitnessInv c F0 F_cur kM_dst := by
    by_cases hcl0 : s.core.cur_level = 0
    · have hwatM : ModeWatchesInv F_cur kM_dst :=
        modeWatchesInv_of_watchSliceLtOk (k := kM_dst) (dst := dst.toNat)
          (fun _ => hdmE.trans hdm0) hltM hlayM (fun _ hr _ => hr)
      have hrsn_ff : ∀ idx < sE.core.trail_end,
          kM_dst.rsns[(sE.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 = 0xFFFFFFFF#32 := fun idx hidx => by
        have hv_lt : (sE.core.trl[idx]?.getD 0#32).toNat / 2 < sE.core.cur_vars := by
          have h1 : (sE.core.trl[idx]?.getD 0#32).toNat < 2 * sE.core.cur_vars :=
            hwEnd.trail_lits_lt idx hidx
          omega
        have h0 := hwEnd.level0_rsn_none idx hidx
          (by have := hwEnd.lvl_le idx hidx; change _ ≤ sE.core.cur_level at this; omega)
        have h1 := hrsnsM _ hv_lt
        rw [ite_eq_right (fun hcond => by
          rw [h0] at hcond
          have hlt_ff : (0xFFFFFFFF#32).toNat < dst.toNat := hcond.2.1
          rw [show (0xFFFFFFFF#32).toNat = 4294967295 from rfl] at hlt_ff
          have harena_lt := c.harena; unfold dimacsBound at harena_lt; omega)] at h1
        exact h1.trans h0
      exact m6_root_post_move_witness hwEnd hcmpM'.1 hwatM rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl (hclE.trans hcl0) hrsn_ff
    · have hpos : 0 < s.core.cur_level := Nat.pos_of_ne_zero hcl0
      obtain ⟨_, _, hvE, hlE, htE, htpE, hteE⟩ := hposE hpos
      have hrmM' : SweepReasonMapInv sPre.core kM_dst sPre.core.arena_len dst.toNat :=
        fun idx hidx => hrmM hpos idx hidx
      exact SweepReasonMapInv.toFullWitnessInvLt (c := c) (F0 := F0)
        (F_cur := F_cur) (k0 := sPre.core) (kL := kM_dst)
        (keep := start.toNat) (dst := dst.toNat) hcoreM_ok hwPre hcmpM'.1
        (fun _ => hdmE.trans hdm0) hlayM hltM (fun _ hr _ => hr)
        (by dsimp only [kM_dst, sM]; rw [hvE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [hlE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [htE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [htpE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [hteE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [hclE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [hcvE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [hftE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [hfdE, hpre_eq])
        (by dsimp only [kM_dst, sM]; rw [hincE, hpre_eq]) hrmM'
  have hstM_in : start.toNat < dst.toNat →
      start.toNat ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat } :=
    m6_start_in_post_move hcmpE_fr harE_len harM_l rfl
      (Nat.le_trans hdst_le hal_le) hfr_lt_dst hfr_st (fun i hi => hpreM i hi) hstE_in hmvM_refs
  exact ⟨sM, hlikeM, hlenM, hcvE, halE, hclE, hdmE, hftE, hfdE, hincE,
    helM.trans helE, hws2M.trans hws2E, hwM, hcmpM'.2.1, hcmpM'.2.2, hstM_in,
    hunsatE, hunitE, hposE, hmM⟩


end LeanQbe.T.Examples.Kissat.FullM6WatchGc
