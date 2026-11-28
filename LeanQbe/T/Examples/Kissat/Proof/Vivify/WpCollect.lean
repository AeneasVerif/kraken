/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Src.Vivify
import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Vivify Collect & Tier-Clear WP Proofs (`Proof.Vivify.WpCollect`)

Parametric `(Γ : Env)` `Func.wp` proofs for:
1. `full_viv_tier_match_m6_wp` (`Spec.fullVivTierMatchM6Spec`)
2. `full_viv_clear_tier_m6_wp` (`Spec.fullVivClearTierM6Spec`)
3. `full_viv_collect_fid_wp` (`Spec.vivCollectFidSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Vivify
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics

private theorem fullSparseInv_set_hdr_non_gs {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (harr : cref < s.core.arena.length) (v : BitVec 32)
    (h19 : (v &&& 0x00080000#32) = (s.core.arena[cref] &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (s.core.arena[cref] &&& 0x00800000#32)) :
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref v } }
    FullSparseInv c F0 s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have h19' : (v &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32) := by
    rw [fullArenaHdr, fullArenaHdrCore, List.getElem?_eq_getElem harr, Option.getD_some]
    exact h19
  have h23' : (v &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32) := by
    rw [fullArenaHdr, fullArenaHdrCore, List.getElem?_eq_getElem harr, Option.getD_some]
    exact h23
  obtain ⟨F_cur, hw⟩ := hsp.1.2
  obtain ⟨hlen_c, hrefs, hw', hall⟩ :=
    fullWitnessInv_set_hdr_non_gs hsp.1.1.core_ok hw href v h19' h23'
  have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s := hrefs
  have hlen' : s'.LengthsOk c := ⟨hlen_c, hsp.1.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hr0 : r ∈ fullArenaClauseRefs s := hrefs' ▸ hr
    obtain ⟨hg, _, hl⟩ := hall r hr0
    have hl' : fullArenaClauseLits s' r = fullArenaClauseLits s r := hl
    have hg' : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := hg
    rw [hl']; exact hsp.2.2.1 r hr0 (hg'.symm.trans hng)
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => (hsp.2.2.2.1.1 i hi).imp id (fun h => hrefs' ▸ h), hsp.2.2.2.1.2⟩
  exact ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, hsp.2.1, hnd', hext', hsp.2.2.2.2⟩, hrefs'⟩

private abbrev collectState (s : FullState) (ari rri : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with arena := ari }
    scratch := { s.scratch with red_refs := rri } }

private theorem arena_lt_of_clause_ref {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) :
    cref < s.core.arena_len ∧ cref < s.core.arena.length ∧ cref < 2 ^ 32 := by
  obtain ⟨_, hw⟩ := hsp.1.2
  have hwf := hw.arena.refs_wf cref href
  have harena_bound := c.harena; unfold dimacsBound at harena_bound
  have har_len := hsp.1.1.core_ok.arena_len_arr
  have har_le := hsp.1.1.core_ok.arena_len_le
  exact ⟨by omega, by omega, by omega⟩

private theorem red_refs_set_mem {c_red_cap : Nat} {rr : List (BitVec 32)} {p : Nat → Prop}
    {bn : BitVec 64} {pos : BitVec 32} (hlen : rr.length = c_red_cap) (hbn : bn.toNat < c_red_cap)
    (hprev : ∀ k < bn.toNat, p (rr[k]?.getD 0#32).toNat) (hpos : p pos.toNat) :
    ∀ k < (bn + 1#64).toNat, p ((rr.set bn.toNat pos)[k]?.getD 0#32).toNat := by
  intro k hk
  have hbn_lt64 : bn.toNat < 2 ^ 64 := bn.isLt
  have hbn1 : (bn + 1#64).toNat = bn.toNat + 1 := by bv_omega
  rw [hbn1] at hk
  have hk_len : k < (rr.set bn.toNat pos).length := by rw [List.length_set]; omega
  rw [List.getElem?_eq_getElem hk_len, Option.getD_some]
  by_cases heq : k = bn.toNat
  · subst heq; rw [List.getElem_set_self (by omega)]; exact hpos
  · simp only [List.getElem_set_ne (Ne.symm heq)]
    have hk_prev := hprev k (by omega)
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hk_prev

public section

theorem full_viv_tier_match_m6_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullVivTierMatchM6Spec a m Q X →
      Func.wp Γ full_viv_tier_match_m6_body a m Q X := by
  intro ⟨h, hdr, tier_mode, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, s, R, rfl, hm, hQ⟩
  unfold Func.wp full_viv_tier_match_m6_body
  viv_to_group
  · exact hQ _
  · viv_to_group; viv_steps; all_goals exact hQ _
  · viv_to_group; viv_steps; all_goals exact hQ _
  · viv_to_group; viv_steps; all_goals exact hQ _

theorem full_viv_clear_tier_m6_wp (Γ : Env)
    (hMatch : Γ.Has "full_viv_tier_match_m6" Spec.fullVivTierMatchM6Spec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec) :
    ∀ a m Q X, Spec.fullVivClearTierM6Spec a m Q X →
      Func.wp Γ full_viv_clear_tier_m6_body a m Q X := by
  intro ⟨h, tier_mode, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, F0, s, R, rfl, hsp, hlvl, hm, hQ⟩
  have harena_bound := c.harena; unfold dimacsBound at harena_bound
  unfold Func.wp full_viv_clear_tier_m6_body
  viv_to_group
  refine wp_while_state1 (α := BitVec 64 × FullState) (fun st => st.1)
    (fun st => s.core.arena_len - st.1.toNat)
    (fun (p, si) mi =>
      p.toNat ≤ si.core.arena_len ∧ si.core.arena_len = s.core.arena_len ∧
      (p.toNat ∈ fullArenaClauseRefs si ∨ p.toNat = si.core.arena_len) ∧
      FullSparseInv c F0 si ∧ si.core.cur_level = 0 ∧ si.core.fuel = s.core.fuel ∧
      (FullMem c si ⋆ R) mi)
    ?_ ?_
  · intro J hJ; viv_steps
    refine hJ (0#64, s) m ⟨Nat.zero_le _, rfl, ?_, hsp, hlvl, rfl, hm⟩
    by_cases h0 : s.core.arena_len = 0
    · exact Or.inr h0.symm
    · obtain ⟨_, hw⟩ := hsp.1.2
      exact Or.inl (fullArenaClauseRefs_zero_mem hw.arena (Nat.zero_lt_of_ne_zero h0))
  · rintro J ⟨p, si⟩ mi ⟨hp_le, hal_eq, hp_mem, hsp_i, hlvl_i, hfuel_i, hm_i⟩ ih
    viv_steps
    · have hp_lt : p.toNat < si.core.arena_len := by
        have := hsp_i.1.1.core_ok.arena_len_le
        omega
      have hp_ref : p.toNat ∈ fullArenaClauseRefs si := by
        rcases hp_mem with h1 | h2
        · exact h1
        · omega
      have hp_arr : p.toNat < si.core.arena.length := by
        have := hsp_i.1.1.core_ok.arena_len_arr
        have := hsp_i.1.1.core_ok.arena_len_le
        omega
      viv_to_group
      refine wp_join_state0 (α := FullState)
        (fun sj mj =>
          FullSparseInv c F0 sj ∧ sj.core.arena_len = s.core.arena_len ∧
          sj.core.cur_level = 0 ∧ sj.core.fuel = s.core.fuel ∧
          p.toNat ∈ fullArenaClauseRefs sj ∧ (FullMem c sj ⋆ R) mj)
        ?_ ?_
      · intro _ sj mj ⟨hsp_j, hal_j, hlvl_j, hfuel_j, hp_ref_j, hm_j⟩
        viv_steps
        viv_call hNext
        refine ⟨c, sj, R, rfl, hsp_j.1.1, hm_j, ?_⟩
        viv_steps
        obtain ⟨_, hw_j⟩ := hsp_j.1.2
        have hwf := hw_j.arena.refs_wf p.toNat hp_ref_j
        have hlt32 : sj.core.arena_len < 2 ^ 32 := by
          have := hsp_j.1.1.core_ok.arena_len_le; omega
        have htrunc : (BitVec.truncate 32 p).toNat = p.toNat := by bv_omega
        have hzw : (BitVec.setWidth 64
            (BitVec.ofNat 32 (fullArenaNextOff sj.core.arena sj.core.arena_len
              (BitVec.truncate 32 p).toNat))).toNat =
            fullArenaNextOff sj.core.arena sj.core.arena_len p.toNat := by
          rw [htrunc]; bv_omega
        have hmem := fullArenaClauseRefs_next_mem_or_end hw_j.arena hp_ref_j
        refine ih (BitVec.setWidth 64
            (BitVec.ofNat 32 (fullArenaNextOff sj.core.arena sj.core.arena_len
              (BitVec.truncate 32 p).toNat)), sj)
          mj (by dsimp only; omega) ⟨?_, hal_j, ?_, hsp_j, hlvl_j, hfuel_j, hm_j⟩
        · rw [hzw]; exact hwf.2.2.2.1
        · rw [hzw]; exact hmem.symm
      · intro J1 hJ1
        viv_steps
        · viv_to_group
          viv_call hMatch
          refine ⟨c, si, R, rfl, hm_i, fun r => ?_⟩
          viv_steps
          · have hset := fullSparseInv_set_hdr_non_gs hsp_i hp_ref hp_arr
              (si.core.arena[p.toNat] &&& ~~~1048576#32)
              (bv32_clr_viv_garb _) (bv32_clr_viv_shrk _)
            exact hJ1 _ _ ⟨hset.1, hal_eq, hlvl_i, hfuel_i, hset.2 ▸ hp_ref, by assumption⟩
          · exact hJ1 si mi ⟨hsp_i, hal_eq, hlvl_i, hfuel_i, hp_ref, hm_i⟩
        · exact hJ1 si mi ⟨hsp_i, hal_eq, hlvl_i, hfuel_i, hp_ref, hm_i⟩
    · exact hQ si mi hsp_i hlvl_i hfuel_i hm_i

theorem full_viv_collect_fid_wp (Γ : Env)
    (hMatch : Γ.Has "full_viv_tier_match_m6" Spec.fullVivTierMatchM6Spec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec) :
    ∀ a m Q X, Spec.vivCollectFidSpec a m Q X →
      Func.wp Γ full_viv_collect_fid_body a m Q X := by
  intro ⟨h, tier_mode, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  have harena_bound := c.harena; unfold dimacsBound at harena_bound
  have hred_bound := c.hred; unfold dimacsBound at hred_bound
  unfold Func.wp full_viv_collect_fid_body
  viv_to_group
  refine wp_while_state
    (α := BitVec 64 × Bool × BitVec 64 × List (BitVec 32) × List (BitVec 32))
    (fun st => (st.1, st.2.1, st.2.2.1, ()))
    (fun st => 2 - st.2.2.1.toNat)
    (fun (bn, found, retry, ari, rri) mi =>
      let si := collectState s ari rri
      retry.toNat ≤ 2 ∧ bn.toNat ≤ c.red_cap ∧
      FullSparseInv c F0 si ∧ fullArenaClauseRefs si = fullArenaClauseRefs s ∧
      (∀ k < bn.toNat, (rri[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs si) ∧
      (FullMem c si ⋆ R) mi)
    ?_ ?_
  · intro J hJ; viv_steps
    exact hJ (0#64, false, 0#64, s.core.arena, s.scratch.red_refs) m
      ⟨by decide, Nat.zero_le _, hsp, rfl, fun _ hk => by simp at hk, hm⟩
  · rintro J ⟨bn, found, retry, ari, rri⟩ mi
      ⟨hr_le, hbn_le, hsp_i, hrefs_i, hrr_i, hm_i⟩ ih
    dsimp only [Blocks.get]
    refine wp_join_state0 (α := List (BitVec 32) × List (BitVec 32))
      (fun (arj, rrj) mj =>
        let sj := collectState s arj rrj
        bn.toNat ≤ c.red_cap ∧ FullSparseInv c F0 sj ∧
        fullArenaClauseRefs sj = fullArenaClauseRefs s ∧
        (∀ k < bn.toNat, (rrj[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sj) ∧
        (FullMem c sj ⋆ R) mj)
      ?_ ?_
    · intro _ ⟨arj, rrj⟩ mj ⟨hbn_j, hsp_j, hrefs_j, hrr_j, hm_j⟩
      dsimp only [Blocks.get]
      viv_steps
      · exact hQ bn arj rrj mj hbn_j hsp_j.1.1.scratch_ok.red_refs_len
          hsp_j hrefs_j hrr_j hm_j
      · refine wp_while_state1 (α := BitVec 64 × List (BitVec 32)) (fun st => st.1)
          (fun st => bn.toNat - st.1.toNat)
          (fun (k, ark) mk =>
            let sk := collectState s ark rrj
            k.toNat ≤ bn.toNat ∧ FullSparseInv c F0 sk ∧
            fullArenaClauseRefs sk = fullArenaClauseRefs s ∧
            (∀ i < bn.toNat, (rrj[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs sk) ∧
            (FullMem c sk ⋆ R) mk)
          ?_ ?_
        · intro Jk hJk; viv_steps
          exact hJk (0#64, arj) mj ⟨Nat.zero_le _, hsp_j, hrefs_j, hrr_j, hm_j⟩
        · rintro Jk ⟨k, ark⟩ mk ⟨hk_le, hsp_k, hrefs_k, hrr_k, hm_k⟩ ihk
          viv_steps
          · have hk_lt : k.toNat < bn.toNat := by omega
            have hrr_len : rrj.length = c.red_cap := hsp_k.1.1.scratch_ok.red_refs_len
            have hk_rr : k.toNat < rrj.length := by omega
            have href_cr := hrr_k k.toNat hk_lt
            rw [List.getElem?_eq_getElem hk_rr, Option.getD_some] at href_cr
            have hcr := arena_lt_of_clause_ref hsp_k href_cr
            have hcr_zw : (BitVec.setWidth 64 rrj[k.toNat]).toNat = rrj[k.toNat].toNat := by
              bv_omega
            have hcr_arr : (BitVec.setWidth 64 rrj[k.toNat]).toNat < ark.length := by
              rw [hcr_zw]; exact hcr.2.1
            viv_steps
            have hset := fullSparseInv_set_hdr_non_gs hsp_k href_cr hcr.2.1
              (ark[rrj[k.toNat].toNat] ||| 1048576#32)
              (bv32_or_viv_garb _) (bv32_or_viv_shrk _)
            refine ihk (k + 1#64, ark.set (BitVec.setWidth 64 rrj[k.toNat]).toNat
              (ark[(BitVec.setWidth 64 rrj[k.toNat]).toNat] ||| 1048576#32)) _
              (by dsimp only; bv_omega) ⟨by bv_omega, ?_, ?_, ?_, by assumption⟩
            all_goals simp only [hcr_zw]
            · exact hset.1
            · rw [hset.2]; exact hrefs_k
            · intro i hi; rw [hset.2]; exact hrr_k i hi
          · exact hQ bn ark rrj mk hbn_j hsp_k.1.1.scratch_ok.red_refs_len
              hsp_k hrefs_k hrr_k hm_k
    · intro J_exit hJ_exit
      viv_steps
      · have hbn_lt : bn.toNat < c.red_cap := Nat.lt_of_lt_of_le hc (Nat.mod_le _ _)
        refine wp_while_state
          (α := BitVec 64 × Bool × BitVec 64 × List (BitVec 32) × List (BitVec 32))
          (fun st => (st.1, st.2.1, st.2.2.1, ()))
          (fun st => s.core.arena_len - st.2.2.1.toNat)
          (fun (bn2, found2, pos, arj, rrj) mj =>
            let sj := collectState s arj rrj
            bn2.toNat ≤ c.red_cap ∧ pos.toNat ≤ sj.core.arena_len ∧
            (pos.toNat ∈ fullArenaClauseRefs sj ∨ pos.toNat = sj.core.arena_len) ∧
            FullSparseInv c F0 sj ∧ fullArenaClauseRefs sj = fullArenaClauseRefs s ∧
            (∀ k < bn2.toNat, (rrj[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sj) ∧
            (FullMem c sj ⋆ R) mj)
          ?_ ?_
        · intro Jp hJp; viv_steps
          refine hJp (bn, found, 0#64, ari, rri) mi ⟨hbn_le, Nat.zero_le _, ?_,
            hsp_i, hrefs_i, hrr_i, hm_i⟩
          by_cases h0 : s.core.arena_len = 0
          · exact Or.inr h0.symm
          · obtain ⟨_, hw_i⟩ := hsp_i.1.2
            exact Or.inl (fullArenaClauseRefs_zero_mem hw_i.arena (Nat.zero_lt_of_ne_zero h0))
        · rintro Jp ⟨bn2, found2, pos, arj, rrj⟩ mj
            ⟨hbn2_le, hpos_le, hpos_mem, hsp_j, hrefs_j, hrr_j, hm_j⟩ ihp
          viv_steps
          · have hlen_arr : arj.length = c.arena_cap := hsp_j.1.1.core_ok.arena_len_arr
            have hlen_le : s.core.arena_len ≤ c.arena_cap := hsp_j.1.1.core_ok.arena_len_le
            have hpos_lt : pos.toNat < s.core.arena_len := Nat.lt_of_lt_of_le hc (Nat.mod_le _ _)
            have hpos_arr : pos.toNat < arj.length := by omega
            have hpos_ref : pos.toNat ∈ fullArenaClauseRefs (collectState s arj rrj) := by
              rcases hpos_mem with h1 | h2
              · exact h1
              · change pos.toNat = s.core.arena_len at h2; omega
            viv_to_group
            viv_call hNext
            refine ⟨c, collectState s arj rrj, R, rfl, hsp_j.1.1, hm_j, ?_⟩
            viv_to_group
            refine wp_join_state
              (α := BitVec 64 × Bool × List (BitVec 32))
              (fun st => (st.1, st.2.1, ()))
              (fun (bn3, found3, rrk) mk =>
                let sk := collectState s arj rrk
                bn3.toNat ≤ c.red_cap ∧ FullSparseInv c F0 sk ∧
                fullArenaClauseRefs sk = fullArenaClauseRefs s ∧
                (∀ k < bn3.toNat, (rrk[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sk) ∧
                (FullMem c sk ⋆ R) mk)
              ?_ ?_
            · intro _ ⟨bn3, found3, rrk⟩ mk ⟨hbn3_le, hsp_k, hrefs_k, hrr_k, hm_k⟩
              viv_steps
              obtain ⟨_, hw_k⟩ := hsp_k.1.2
              have hpos_ref_k : pos.toNat ∈ fullArenaClauseRefs (collectState s arj rrk) := by
                rw [hrefs_k, ← hrefs_j]; exact hpos_ref
              have hwf := hw_k.arena.refs_wf pos.toNat hpos_ref_k
              dsimp only [collectState] at hwf
              have hlt32 : s.core.arena_len < 2 ^ 32 := by omega
              have htrunc : (BitVec.truncate 32 pos).toNat = pos.toNat := by bv_omega
              have hzw : (BitVec.setWidth 64
                  (BitVec.ofNat 32 (fullArenaNextOff arj s.core.arena_len
                    (BitVec.truncate 32 pos).toNat))).toNat =
                  fullArenaNextOff arj s.core.arena_len pos.toNat := by
                rw [htrunc]; bv_omega
              have hmem := fullArenaClauseRefs_next_mem_or_end hw_k.arena hpos_ref_k
              have hlt_next : pos.toNat < fullArenaNextOff arj s.core.arena_len pos.toNat := by
                have := hwf.2.1; have := hwf.2.2.1; omega
              have hle_next : fullArenaNextOff arj s.core.arena_len pos.toNat ≤ s.core.arena_len :=
                hwf.2.2.2.1
              refine ihp (bn3, found3, BitVec.setWidth 64
                  (BitVec.ofNat 32 (fullArenaNextOff arj s.core.arena_len
                    (BitVec.truncate 32 pos).toNat)), arj, rrk)
                mk (by dsimp only; rw [hzw]; omega) ⟨hbn3_le, ?_, ?_, hsp_k, hrefs_k, hrr_k, hm_k⟩
              · rw [hzw]; exact hle_next
              · rw [hzw]; exact hmem.symm
            · intro J_step hJ_step
              viv_to_group
              · refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                  (fun _ mk => mk = mj) ?_ ?_
                · rintro _ cond mk rfl
                  viv_steps
                  · viv_to_group
                    viv_call hMatch
                    refine ⟨c, collectState s arj rrj, R, rfl, hm_j, fun r => ?_⟩
                    viv_steps
                    · have hbn2_lt : bn2.toNat < c.red_cap :=
                        Nat.lt_of_lt_of_le hc (Nat.mod_le _ _)
                      have hrr_len : rrj.length = c.red_cap :=
                        hsp_j.1.1.scratch_ok.red_refs_len
                      viv_steps
                      all_goals
                        exact hJ_step (bn2 + 1#64, _, rrj.set bn2.toNat (pos.truncate 32)) _
                          ⟨by bv_omega,
                           viv_sparse_with_rr hsp_j (by rw [List.length_set]; exact hrr_len),
                           hrefs_j,
                           red_refs_set_mem hrr_len hbn2_lt hrr_j (by
                             have : (pos.truncate 32).toNat = pos.toNat := by
                               have : s.core.arena_len < 2 ^ 32 := by omega
                               bv_omega
                             rwa [this]),
                           by assumption⟩
                    · exact hJ_step (bn2, found2, rrj) mk
                        ⟨hbn2_le, hsp_j, hrefs_j, hrr_j, hm_j⟩
                    · exact hJ_step (bn2, found2, rrj) mk
                        ⟨hbn2_le, hsp_j, hrefs_j, hrr_j, hm_j⟩
                  · exact hJ_step (bn2, found2, rrj) mk
                      ⟨hbn2_le, hsp_j, hrefs_j, hrr_j, hm_j⟩
                · intro Jc hJc; viv_steps <;> exact hJc _ mj rfl
              · exact hJ_step (bn2, found2, rrj) mj ⟨hbn2_le, hsp_j, hrefs_j, hrr_j, hm_j⟩
          · exact ih (bn2, found2, retry + 1#64, arj, rrj) mj (by dsimp only; bv_omega)
              ⟨by bv_omega, hbn2_le, hsp_j, hrefs_j, hrr_j, hm_j⟩
      · exact hJ_exit (ari, rri) mi ⟨hbn_le, hsp_i, hrefs_i, hrr_i, hm_i⟩
      · exact hJ_exit (ari, rri) mi ⟨hbn_le, hsp_i, hrefs_i, hrr_i, hm_i⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
