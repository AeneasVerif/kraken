/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersArena
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveSweep
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1

/-!
# Arena Sweep Pure Compaction & Reason Bridges (`Proof.Collect.HelpersSweep0`)

Pure compaction prefix, header bitfield, `full_sweep_copy` extraction, and
`SweepReasonMapInv` bridge theorems used by `full_arena_sweep_m6_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Compaction Prefix, Header Bitfield & Reason-Remapping Bridges -/

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

/-- Canonical `full_sweep_copy` outcome bundle extracted from `Proof.Spec.fullSweepCopySpec`. -/
@[expose] def fullSweepCopyOutcome (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) (src dst : BitVec 64) (old_sz : BitVec 32) (at_root : Bool)
    (r : BitVec 64) : Prop :=
  (at_root = false →
    r = old_sz.setWidth 64 ∧ s'.core.vals = s.core.vals ∧ s'.core.flags = s.core.flags ∧
    s'.core.lvl = s.core.lvl ∧ s'.core.rsns = s.core.rsns ∧ s'.core.trl = s.core.trl ∧
    s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end ∧
    s'.core.unassigned = s.core.unassigned ∧ s'.core.unflushed = s.core.unflushed ∧
    s'.core.wvec = s.core.wvec ∧ s'.core.wstk = s.core.wstk ∧ s'.core.wlen = s.core.wlen ∧
    s'.core.wusable = s.core.wusable ∧ s'.core.num_binary = s.core.num_binary ∧
    s'.core.oom = s.core.oom ∧ s'.scratch.phases = s.scratch.phases ∧
    s'.scratch.wsort = s.scratch.wsort ∧
    ∀ j < old_sz.toNat, s'.core.arena[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?) ∧
  (at_root = true →
    FullWitnessInv c F0 F_cur { s'.core with arena_len := dst.toNat } ∧
    FullBinOnlyWatchesInv F_cur s'.core ∧
    s.core.trail_end ≤ s'.core.trail_end ∧
    (r = 0xFFFFFFFE#64 ∨ r = 0xFFFFFFFD#64 ∨ r = 1#64 ∨ r = 0xFFFFFFFF#64 ∨
      (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat)) ∧
    (r = 0xFFFFFFFE#64 → F0.Unsat) ∧
    (r = 0xFFFFFFFD#64 → s'.core.oom = 1#64) ∧
    (r ≠ 0xFFFFFFFD#64 → s'.core.oom = s.core.oom) ∧
    (r = 1#64 → s.core.trail_end < s'.core.trail_end) ∧
    (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat →
      (∀ j < r.toNat, (s'.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      List.Sublist (((s'.core.arena.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)
        (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (((s'.core.arena.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat))))

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
    have hbinC' : BinOnlyWatchesInv F_cur sC.core := FullBinOnlyWatchesInv.toBinOnly hbinC
    exact ⟨hrange.1, hrange.2, fun j hj => hcvL ▸ hl j hj, by rwa [hsrc_lits] at hs, he,
      hbinC'.layout, fun l hl => by
        rw [hstart0 hcl0]; exact WatchSliceLtOk.ofBinOnly (hbinC'.slices l hl)⟩
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

@[expose] def SweepHappenedCore (k0 kL kn : FullCoreState) (dst src : Nat) : Prop :=
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
    (hnew_lt : ∀ j < st,
      (sC.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
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

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
