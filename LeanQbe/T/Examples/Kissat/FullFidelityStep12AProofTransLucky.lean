/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12A
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof0
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM5Sched
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof1a
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof2
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFixProof
public import LeanQbe.T.Examples.Kissat.FullM7CompactFixProof
public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiersProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCoreProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4b
import LeanQbe.T.Examples.Kissat.FullTransLemmas
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Examples.Kissat.FullReduceLemmas2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 12A Proofs — Transitive Sort & Lucky Preprocessing

Parametric `(Γ : Env)` WP proofs (`0` `import all`, `public section`, `0` `@[expose]` on theorems,
`std3`, `XPost`-polymorphic) for:
1. **`P0-3a` (`full_trans_sort_m6_step12a_wp`):** Knuth-gap Shellsort (`1, 4, 13, ...`) with `n ≤ 1`
   fast return against `FullM6VivBackbone.fullTransSortM6Spec`.
2. **`P1-11` (`full_preprocess_m6_step12a_wp`):** Preprocessing calling `full_lucky_late_m7`
   against `FullM6.fullM6PreprocessSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12A

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullTransHelpers
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Search
open scoped FullArenaTactics

/-! ## 1. `P0-3a`: `full_trans_sort_m6` (Knuth Gaps) -/

section TransSortStep12A

private theorem s12a_bv32_setWidth64 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem s12a_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem s12a_ws1_set_lt_bound {ws1 : List (BitVec 32)} {n cv idx : Nat}
    {v : BitVec 32} (hidx : idx < ws1.length) (hv : v.toNat < cv)
    (hbd : ∀ i < n, (ws1[i]?.getD 0#32).toNat < cv) :
    ∀ i < n, ((ws1.set idx v)[i]?.getD 0#32).toNat < cv := by
  intro i hi
  by_cases h : i = idx
  · subst h; rw [List.getElem?_set_self hidx, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm h)]; exact hbd i hi

private theorem s12a_sparse_with_ws1 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) {ws1' : List (BitVec 32)}
    (hws : ws1'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with work_stk1 := ws1' } } := by
  obtain ⟨⟨hl, F_cur, hw⟩, hlm, hnd, hex, hdm⟩ := hsp
  exact ⟨⟨⟨hl.core_ok, { hl.scratch_ok with work_stk1_len := hws }⟩, F_cur, hw⟩,
    hlm, hnd, hex, hdm⟩

/-- `full_trans_sort_m6` with Knuth gaps satisfies `FullM6VivBackbone.fullTransSortM6Spec`. -/
theorem full_trans_sort_m6_step12a_wp (Γ : Env) :
    ∀ a m Q X, fullTransSortM6Spec a m Q X →
      Func.wp Γ full_trans_sort_m6_body a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp, hn_le, hok0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp.1.lengths.core_ok; have hscl0 := hsp.1.lengths.scratch_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcl0.cur_vars_le
  have hsc_len : s.scratch.score.length = c.max_vars := hscl0.score_len
  have hqs_len : s.scratch.q_stamp.length = c.max_vars := hscl0.q_stamp_len
  unfold Func.wp full_trans_sort_m6_body
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps
    exact hQ s.scratch.work_stk1 m0 hscl0.work_stk1_len hsp hok0 hm0
  · have hn_gt1 : 1 < n.toNat := by
      have hnot : ¬ n.toNat ≤ 1 := by
        simpa [BitVec.ule, BitVec.toNat_ofNat] using hc
      omega
    c0_hsteps_nogrp
    have hn3_eq : (n / 3#64).toNat = n.toNat / 3 := by
      rw [BitVec.toNat_udiv, show (3#64 : BitVec 64).toNat = 3 from rfl]
    refine wp_loop_inv (ts := [i64])
      (fun (gap, ()) mk => 1 ≤ gap.toNat ∧ gap.toNat ≤ n.toNat ∧ mk = m0)
      (fun (gap, ()) _ => n.toNat - gap.toNat)
      (fun Jk hJk => by
        c0_hsteps
        exact hJk (1#64, ()) m0
          ⟨by decide, by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega, rfl⟩)
      (fun Jk ⟨gap, ⟨⟩⟩ mk ⟨hgap_ge1, hgap_le, hmk⟩ ihk => ?_)
    subst mk
    c0_hsplit
    · have hgap_lt_n3 : gap.toNat < n.toNat / 3 := by
        have hlt : gap.toNat < (n / 3#64).toNat := hc
        rwa [hn3_eq] at hlt
      have hnext_le : 3 * gap.toNat + 1 ≤ n.toNat := by omega
      have hnext_eq : (3#64 * gap + 1#64).toNat = 3 * gap.toNat + 1 := by
        have hmax_n : n.toNat < 2 ^ 64 := by omega
        bv_omega
      c0_hsteps
      exact ihk (3#64 * gap + 1#64, ()) m0
        (by dsimp only; rw [hnext_eq]; omega)
        ⟨by rw [hnext_eq]; omega, by rw [hnext_eq]; omega, rfl⟩
    · refine wp_loop_inv (ts := [i64])
        (fun (gap_o, ()) mg => ∃ ws1 : List (BitVec 32),
          gap_o.toNat ≤ n.toNat ∧ ws1.length = 2 * c.max_vars ∧
          (∀ i < n.toNat, (ws1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mg)
        (fun (gap_o, ()) _ => gap_o.toNat)
        (fun Jg hJg => by
          c0_hsteps
          exact hJg (gap, ()) m0 ⟨s.scratch.work_stk1, hgap_le, hscl0.work_stk1_len, hok0, hm0⟩)
        (fun Jg ⟨gap_o, ⟨⟩⟩ mg ⟨wsg, hgapo_le, hwsg_len, hokg, hmg⟩ ihg => ?_)
      c0_hsplit
      · have hgap_pos : 0 < gap_o.toNat := by c0_bound
        c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i64])
          (fun (si, ()) msi => ∃ wss : List (BitVec 32),
            gap_o.toNat ≤ si.toNat ∧ si.toNat ≤ n.toNat ∧ wss.length = 2 * c.max_vars ∧
            (∀ i < n.toNat, (wss[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := wss } } ⋆ R) msi)
          (fun (si, ()) _ => n.toNat - si.toNat)
          (fun Ji hJi => by
            c0_hsteps
            exact hJi (gap_o, ()) mg ⟨wsg, Nat.le_refl _, hgapo_le, hwsg_len, hokg, hmg⟩)
          (fun Ji ⟨si, ⟨⟩⟩ msi ⟨wss, hgsi, hsi_le, hwss_len, hoks, hmsi⟩ ihi => ?_)
        c0_hsplit
        · have hsi_lt : si.toNat < n.toNat := by c0_bound
          have hsi_len : si.toNat < wss.length := by omega
          let v := wss[si.toNat]'hsi_len
          have hv_lt : v.toNat < s.core.cur_vars := by
            have h := hoks si.toNat hsi_lt
            rwa [List.getElem?_eq_getElem hsi_len, Option.getD_some] at h
          have hv64 : (BitVec.setWidth 64 v).toNat = v.toNat := s12a_bv32_setWidth64 v
          have hv_sc : (BitVec.setWidth 64 v).toNat <
              ({ s with scratch := { s.scratch with work_stk1 := wss } } :
                FullState).scratch.score.length := by
            dsimp only; rw [hv64, hsc_len]; omega
          have hv_qs : (BitVec.setWidth 64 v).toNat <
              ({ s with scratch := { s.scratch with work_stk1 := wss } } :
                FullState).scratch.q_stamp.length := by
            dsimp only; rw [hv64, hqs_len]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ mk => mk = msi) ?_
            (fun Jk hJk => by
              c0_hsplit
              · c0_hsteps; exact hJk _ msi rfl
              · c0_hsteps; exact hJk _ msi rfl)
          rintro _ ⟨kv, ⟨⟩⟩ mk rfl
          c0_hsteps_nogrp
          refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
            (BrkPost := fun (sj_b, ()) mb => ∃ wsb : List (BitVec 32),
              sj_b.toNat < n.toNat ∧ wsb.length = 2 * c.max_vars ∧
              (∀ i < n.toNat, (wsb[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
              (FullMem c { s with scratch := { s.scratch with work_stk1 := wsb } } ⋆ R) mb)
            (Inv := fun rem (sj, ()) mj => ∃ wsj : List (BitVec 32),
              sj.toNat < n.toNat ∧ rem = sj.toNat ∧ wsj.length = 2 * c.max_vars ∧
              (∀ i < n.toNat, (wsj[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
              (FullMem c { s with scratch := { s.scratch with work_stk1 := wsj } } ⋆ R) mj)
            ?_ ?_ ?_
          · rintro _ ⟨sj_b, ⟨⟩⟩ mb ⟨wsb, hsjb_lt, hwsb_len, hokb, hmb⟩
            have hsjb_len : sj_b.toNat < wsb.length := by omega
            have hsi1 : (si + 1#64).toNat = si.toNat + 1 := s12a_bv64_add1 (by omega)
            c0_hsteps
            exact ihi (si + 1#64, ()) _ (by dsimp only; omega)
              ⟨wsb.set sj_b.toNat v, by rw [hsi1]; omega, by rw [hsi1]; omega,
               by simp [hwsb_len], s12a_ws1_set_lt_bound hsjb_len hv_lt hokb, (by assumption)⟩
          · rintro B L rem ⟨sj, ⟨⟩⟩ mj hB hL ⟨wsj, hsj_lt, hrem, hwsj_len, hokj, hmj⟩
            c0_hsplit
            · have hsj_ge : gap_o.toNat ≤ sj.toNat := by c0_bound
              have hpj_eq : (sj - gap_o).toNat = sj.toNat - gap_o.toNat := by bv_omega
              have hpj_len : (sj - gap_o).toNat < wsj.length := by omega
              let pv := wsj[(sj - gap_o).toNat]'hpj_len
              have hpv_lt : pv.toNat < s.core.cur_vars := by
                have h := hokj (sj - gap_o).toNat (by omega)
                rwa [List.getElem?_eq_getElem hpj_len, Option.getD_some] at h
              have hpv64 : (BitVec.setWidth 64 pv).toNat = pv.toNat := s12a_bv32_setWidth64 pv
              have hpv_sc : (BitVec.setWidth 64 pv).toNat <
                  ({ s with scratch := { s.scratch with work_stk1 := wsj } } :
                    FullState).scratch.score.length := by
                dsimp only; rw [hpv64, hsc_len]; omega
              have hpv_qs : (BitVec.setWidth 64 pv).toNat <
                  ({ s with scratch := { s.scratch with work_stk1 := wsj } } :
                    FullState).scratch.q_stamp.length := by
                dsimp only; rw [hpv64, hqs_len]; omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ mp => mp = mj) ?_
                (fun Jp hJp => by
                  c0_hsplit
                  · c0_hsteps; exact hJp _ mj rfl
                  · c0_hsteps; exact hJp _ mj rfl)
              rintro _ ⟨kpv, ⟨⟩⟩ mp rfl
              c0_hsplit
              · c0_hsteps; exact hB (sj, ()) mp ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
              · refine wp_join_group (ts := []) (fun _ m_c => m_c = mp)
                  (fun _ _ m_c heq => by
                    subst heq
                    have hsj_len : sj.toNat < wsj.length := by omega
                    c0_hsteps
                    exact hL (sj.toNat - gap_o.toNat) (sj - gap_o, ()) _ (by omega)
                      ⟨wsj.set sj.toNat pv, by rw [hpj_eq]; omega, by rw [hpj_eq],
                       by simp [hwsj_len], s12a_ws1_set_lt_bound hsj_len hpv_lt hokj,
                       (by assumption)⟩)
                  (fun Jc hJc => by
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsteps; exact hB (sj, ()) mp ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
                      · c0_hsteps; exact hJc () mp rfl
                    · c0_hsteps; exact hJc () mp rfl)
            · c0_hsteps; exact hB (sj, ()) mj ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
          · intro B L hB hL; c0_hsteps
            exact hL si.toNat (si, ()) mk ⟨wss, hsi_lt, rfl, hwss_len, hoks, hmsi⟩
        · c0_hsteps
          have hdiv3 : (gap_o / 3#64).toNat = gap_o.toNat / 3 := by
            rw [BitVec.toNat_udiv, show (3#64 : BitVec 64).toNat = 3 from rfl]
          exact ihg (gap_o / 3#64, ()) msi (by dsimp only; rw [hdiv3]; omega)
            ⟨wss, by rw [hdiv3]; omega, hwss_len, hoks, hmsi⟩
      · c0_hsteps
        exact hQ wsg mg hwsg_len (s12a_sparse_with_ws1 hsp hwsg_len) hokg hmg

end TransSortStep12A

/-! ## 2. `P1-11`: `full_preprocess_m6` (`full_lucky_late_m7`) -/

section PreprocessStep12A

private theorem s12a_fullWitnessInv_with_unflushed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with unflushed := 0#64 } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem s12a_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' →
      Γ "full_propagate" [i64] [i64] a m' Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom hr0 hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr0 hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem s12a_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private abbrev S12aPrePost (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) c' ext' s' m',
    FullM4Compact.FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' →
    M6HdrExtOk ext' → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
    s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
    (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
    (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem s12aPre_ret10 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : S12aPrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (10#64, ()) m' :=
  hQ 10#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk
    (Or.inr (Or.inr (Or.inl rfl))) hfu (fun h => by cases h) (fun h => by cases h)
    (fun _ => hinv.sparse.2.2.2.1.2) hm

private theorem s12aPre_ret20 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : S12aPrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hlen : s'.LengthsOk c') (hcfg : FullM6HdrCfgOk c') (hext : M6HdrExtOk ext')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hu : F0.Unsat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (20#64, ()) m' :=
  hQ 20#64 c' ext' s' m' hcmp hlen hcfg hext (Or.inr (Or.inr (Or.inr rfl))) hfu
    (fun _ => hu) (fun h => by cases h) (fun h => by cases h) hm

private theorem s12aPre_ret20_inc {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : S12aPrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hinc : s'.core.inconsistent ≠ 0#64) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (20#64, ()) m' :=
  s12aPre_ret20 hQ hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk hfu
    (fullM6HdrInv_inconsistent_unsat hinv hinc) hm

private theorem s12aPre_ret0_inv {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : S12aPrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (0#64, ()) m' :=
  hQ 0#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk (Or.inl rfl) hfu
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm

private theorem s12a_pre_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {Q : Post [i64]} {X : XPost} {J2 : Cont []}
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hinv1 : FullM6HdrInv c F0 ext s1) (hcl1' : s1.core.cur_level = 0)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm1 : (FullM6HdrMem c ext s1 ⋆ R) m1)
    (hJ2 : ∀ xs m2, (∃ s2, FullM6HdrInv c F0 ext s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s2 ⋆ R) m2) → J2 xs m2)
    (hQ : S12aPrePost c F0 s R Q) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_7 =>
      Expr.load i64 (Arg.var p_7.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_8 =>
          Expr.jnz (Arg.var p_8.fst)
            (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ())
                fun p_9 =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_9.fst, Arg.imm 2, ()))
                  fun p_10 =>
                Expr.jnz (Arg.var p_10.fst) (Expr.ret (Arg.imm 20, ()))
                  (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                      fun p_11 =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                        (Arg.var p_11.fst, Arg.imm 1, ())) fun p_12 =>
                      Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm 20, ()))
                        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                          Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump J2 ()))))
            (Expr.jump J2 ())) m1 := by
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
    c0_call hSweep
    refine ⟨c, F0, F_cur1, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
      hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2,
      fun hpos => by omega, hm1f,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
        wu' fred' ni' nr' nb' oom' sc' mS hlenS hsr hexlenS _ hllS hwS hndS
        _ _ _ h20S _ hmS => ?_⟩
    have hmS' := fullM6HdrMem_unfocus hmS
    let sSc : FullCoreState := { s1.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      arena := arena', arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := 0#64,
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      oom := oom' }
    let sS : FullState := { core := sSc, scratch := sc' }
    have hinvWS : FullM6HdrInvW c F0 F_cur1 ext sS :=
      FullM6HdrInvW.mk_inv hinv1.cfgOk hinv1.extOk
        ⟨hlenS, hwS, hinv1.sparse.2.1, hndS,
          ⟨hllS, (by change sc'.extend_len ≤ c.extend_cap; rw [hexlenS]
                     exact hinv1.sparse.2.2.2.1.2)⟩,
          hinv1.sparse.2.2.2.2⟩
    c0_hsteps_nogrp
    · exact s12aPre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfu1 (h20S ‹_›).2 hmS'
    · refine s12a_call_bcp rfl hProp hinvWS hmS'
        fun pr sP mP hinvWP hclP _ _ hfuP _ _ hrP1 hmP => ?_
      have hinvP := hinvWP.toInv; have hfuP' := Nat.le_trans hfuP hfu1
      c0_hsteps_nogrp
      · exact s12aPre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk hinvP.extOk hfuP'
          (s12a_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hcl1') (hrP1 ‹_›).2.2) hmP
      · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
        c0_hsteps_nogrp
        have hinvP' : FullM6HdrInv c F0 ext
            { sP with core := { sP.core with unflushed := 0#64 } } :=
          FullM6HdrInv.mk_inv hinvP.cfgOk hinvP.extOk ⟨⟨⟨{ hinvP.sparse.lengths.core_ok with
              vals_len := hinvP.sparse.lengths.core_ok.vals_len }, hinvP.sparse.lengths.scratch_ok⟩,
            ⟨F_cur1, { hinvWP.sparseW.2.1 with
              arena := { hinvWP.sparseW.2.1.arena with len_ok := hinvWP.sparseW.2.1.arena.len_ok }
              watches := hinvWP.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
              }⟩⟩, hinvP.sparse.2.1, hinvP.sparse.2.2.1, hinvP.sparse.2.2.2.1, hinvP.sparse.2.2.2.2⟩
        exact hJ2 () _ ⟨_, hinvP', hclP ▸ hcl1', hfuP', fullM6HdrMem_unfocus (by assumption)⟩
  · exact hJ2 () m1 ⟨s1, hinv1, hcl1', hfu1, fullM6HdrMem_unfocus hm1f⟩

private theorem s12a_pre_compact_step {Γ : Env} {c c0 : FullCfg} {hdr : BitVec 64}
    {F0 : CNF Nat} {ext : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [i64]} {X : XPost} {JC : Cont []}
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hhdr : c0.hdr = hdr)
    (hcmp0 : FullM4Compact.FullCfgCompat c c0) (hinv0 : FullM6HdrInv c0 F0 ext s0)
    (hcl0 : s0.core.cur_level = 0) (hfu0 : s0.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm0f : (FullMem c0 s0 ⋆ (m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R)) m0)
    (hJC : ∀ xs mC, (∃ cC sC, FullM4Compact.FullCfgCompat c cC ∧
      FullM6HdrInv cC F0 ext sC ∧ sC.core.cur_level = 0 ∧
      sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem cC ext sC ⋆ R) mC) → JC xs mC)
    (hQ : S12aPrePost c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var hdr, ())
        fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var hdr, ()) fun p_13 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 20, ()))
              fun p_14 =>
            Expr.jnz (Arg.var p_14.fst) (Expr.ret (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
                  fun p_15 =>
                Expr.jnz (Arg.var p_15.fst) (Expr.ret (Arg.imm 0, ())) (Expr.jump JC ())))
        (Expr.jump JC ())) m0 := by
  subst hhdr
  have hlen0 := hinv0.sparse.lengths
  c0_hsteps_nogrp; c0_call hCompNeed
  refine ⟨c0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hlen0,
    by have := hlen0.core_ok.trail_end_le; have := hlen0.core_ok.cur_vars_le
       have := c0.hmaxv; unfold dimacsBound at *; omega,
    hm0f, fun need _ => ?_⟩
  c0_hsteps_nogrp
  · c0_call hCompact
    refine ⟨c0, F0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hinv0.sparse, hm0f,
      fun rC cC sC mC hcmpC hspC hrC _ hfuC huC h1C hmC => ?_⟩
    have hcfgC := M6HdrCfgOk_of_le (by rw [hcmpC.hdr]; exact M6HdrCfgOk_le hinv0.cfgOk)
    have hinvC := FullM6HdrInv.mk_inv hcfgC hinv0.extOk hspC; have hfuC' := Nat.le_trans hfuC hfu0
    have hmC' := fullM6HdrMem_unfocus (hcmpC.hdr ▸ hmC); have hcmpC' := hcmp0.trans hcmpC
    c0_hsteps_nogrp
    · exact s12aPre_ret20 hQ hcmpC' hspC.lengths hcfgC hinvC.extOk hfuC' (huC ‹_›) hmC'
    · exact s12aPre_ret0_inv hQ hcmpC' hinvC hfuC' hmC'
    · exact hJC () mC ⟨cC, sC, hcmpC', hinvC, h1C ‹_›, hfuC', hmC'⟩
  · exact hJC () m0 ⟨c0, s0, hcmp0, hinv0, hcl0, hfu0, fullM6HdrMem_unfocus hm0f⟩

/-- Step-12A `full_preprocess_m6` (invoking `full_lucky_late_m7`) satisfies
`FullM6.fullM6PreprocessSpec` parametrically in `Γ`. -/
theorem full_preprocess_m6_step12a_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLuckyLate : ∀ a m Q X, FullM7Search.m7LuckyLateSpec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, FullM6Orch.m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ full_preprocess_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_preprocess_m6_body
  obtain ⟨F_cur, hw0⟩ := hinv.sparse.1.witness
  have hinvW0 : FullM6HdrInvW c F0 F_cur ext s := FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
    ⟨hinv.sparse.lengths, hw0, hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1,
      hinv.sparse.2.2.2.2⟩
  c0_hsteps_nogrp
  refine s12a_call_bcp rfl hProp hinvW0 hm
    fun r1 s1 m1 hinvW1 hcl1 _ _ hfu1 _ _ hr1_1 hm1 => ?_
  have hinv1 := hinvW1.toInv; have hcl1' : s1.core.cur_level = 0 := hcl1 ▸ hcl0
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · exact s12aPre_ret20 hQ (.refl c) hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk hfu1
      (s12a_conflict_level0_unsat hinvW1.sparseW.2.1 hcl1' (hr1_1 ‹_›).2.2)
      (fullM6HdrMem_unfocus hm1f)
  · exact s12aPre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · exact s12aPre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hsteps_nogrp
      · exact s12aPre_ret10 hQ (.refl c) hinv2 hfu2 (fullM6HdrMem_unfocus hm2f)
      · c0_call (fun a m' Q' X' h => hLuckyLate a m' Q' X' (m7LuckyLateSpec_to_canon h))
        refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hcl2, hm2f,
          fun lk s3 m3 hlen3 hlk hfu3 _ hu3 hsp3 h10_3 hm3 => ?_⟩
        have hm3' := fullM6HdrMem_unfocus hm3; have hfu3' := Nat.le_trans hfu3 hfu2
        let mkInv3 : lk ≠ 20#64 → lk ≠ 10#64 →
            FullM6HdrInv c F0 ext s3 ∧ s3.core.cur_level = 0 := fun h20 h10 =>
          let h02 : lk = 0#64 ∨ lk = 2#64 := by
            rcases hlk with rfl | rfl | rfl | rfl <;>
              (first | exact Or.inl rfl | exact Or.inr rfl | contradiction)
          let ⟨hs3, hc3⟩ := hsp3 h02
          ⟨FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hs3, hc3⟩
        c0_hsteps_nogrp
        · rw [‹lk = 20#64›]
          exact s12aPre_ret20 hQ (.refl c) hlen3 hinv2.cfgOk hinv2.extOk hfu3' (hu3 ‹_›) hm3'
        · rw [‹lk = 10#64›]
          exact hQ 10#64 c ext s3 m3 (.refl c) hlen3 hinv2.cfgOk hinv2.extOk
            (Or.inr (Or.inr (Or.inl rfl))) hfu3' (fun _ => by cases ‹_›)
            (fun h => by cases h) (fun _ => h10_3 ‹_›) hm3'
        · exact s12aPre_ret20_inc hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' ‹_› hm3'
        · exact s12aPre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · exact s12aPre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' hm3'
        · obtain ⟨hinv3, hcl3⟩ := mkInv3 ‹_› ‹_›
          refine wp_join_group (ts := []) (fun (_ : Tup Val []) m3u => ∃ s3u,
              FullM6HdrInv c F0 ext s3u ∧ s3u.core.cur_level = 0 ∧
              s3u.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s3u ⋆ R) m3u) ?_ ?_
          · rintro _ _ m3u ⟨s3u, hinv3u, hcl3u, hfu3u, hm3u⟩
            refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ c4 s4,
                FullM4Compact.FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext s4 ∧
                s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c4 ext s4 ⋆ R) m4) ?_ ?_
            · rintro _ _ m4 ⟨c4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩; rw [← hcmp4.hdr]
              refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
              c0_hsteps_nogrp
              · exact s12aPre_ret20_inc hQ hcmp4 hinv4 hfu4 ‹_› (fullM6HdrMem_unfocus hm4f)
              · exact s12aPre_ret0_inv hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
              · exact s12aPre_ret10 hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
              · c0_call hScale
                refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl, hinv4.sparse.lengths,
                  hm4f, fun sd1 => ?_⟩
                c0_hsteps_nogrp; c0_call hScale
                refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl,
                  (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                  by assumption, fun sd2 => ?_⟩
                c0_hsteps_nogrp
                have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
                have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                  s4.scratch.elim_bound
                have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
                have hm4' := fullM6HdrMem_unfocus (by assumption)
                c0_call hProbe
                refine FullM6Orch.m6ProbeSpec_of hinv4' (by rw [hst4'.2.1, hst4.2.1]; exact hcl4)
                  hm4' fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
                have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
                c0_hsteps_nogrp
                · exact s12aPre_ret20 hQ hcmp4 hlen5 hinv4'.cfgOk hext5 hfu5' (hu5 ‹_›) hm5
                · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                  refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                  c0_hsteps_nogrp
                  · exact s12aPre_ret20_inc hQ hcmp4 hinv5 hfu5' ‹_› (fullM6HdrMem_unfocus hm5f)
                  · exact s12aPre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                  · exact s12aPre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                  · refine wp_join_group (fun (_ : Tup Val []) m6 => ∃ c6 s6,
                          FullM4Compact.FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext5 s6 ∧
                          s6.core.cur_level = 0 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c6 ext5 s6 ⋆ R) m6) ?_ ?_
                    · rintro _ _ m6 ⟨c6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
                      rw [hcmp4.hdr, ← hcmp6.hdr]
                      refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
                      c0_hsteps_nogrp
                      · exact s12aPre_ret20_inc hQ hcmp6 hinv6 hfu6 ‹_›
                          (fullM6HdrMem_unfocus hm6f)
                      · exact s12aPre_ret0_inv hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                      · exact s12aPre_ret10 hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                      · c0_call hScale
                        refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                          hinv6.sparse.lengths, hm6f, fun sd3 => ?_⟩
                        c0_hsteps_nogrp; c0_call hScale
                        refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                          (fullState_upd_probe_step hinv6.sparse.lengths sd3
                            s6.scratch.probings).1,
                          by assumption, fun sd4 => ?_⟩
                        c0_hsteps_nogrp
                        have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd3
                          s6.scratch.probings
                        have hst6' := fullState_upd_elim_step hst6.1 sd4 s6.scratch.eliminations
                          s6.scratch.elim_bound
                        have hinv6' := fullM6HdrInv_of_probeStep hinv6
                          (probeStep_trans hst6 hst6')
                        exact hQ 1#64 c6 ext5 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk
                          hinv6'.extOk (Or.inr (Or.inl rfl))
                          (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
                          (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
                          (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
                    · exact fun _ hJC2 => wp_m6Hdr_focus_frame hm5 fun hm5f =>
                        s12a_pre_compact_step hCompNeed hCompact rfl hcmp4 hinv5 hcl5 hfu5' hm5f
                          hJC2 hQ
            · exact fun _ hJC1 => wp_m6Hdr_focus_frame hm3u fun hm3uf =>
                s12a_pre_compact_step hCompNeed hCompact rfl (.refl c) hinv3u hcl3u hfu3u hm3uf
                  hJC1 hQ
          · intro _ hJ3u
            refine wp_m6Hdr_focus_frame hm3' fun hm3f => ?_
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ m_b => m3 = m_b) ?_ ?_
            · rintro _ ⟨⟩ mb hmb; subst mb
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ m_w => ∃ sW,
                  FullM6HdrInv c F0 ext sW ∧ sW.core.cur_level = 0 ∧
                  sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c sW ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m_w) ?_ ?_
              · rintro _ _ m_w ⟨sW, hinvW, hclW, hfuW, hmW⟩
                c0_hsteps
                have hinvW' : FullM6HdrInv c F0 ext
                    { sW with core := { sW.core with unflushed := 0#64 } } := by
                  obtain ⟨F_curW, hwW⟩ := hinvW.sparse.1.witness
                  exact FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk
                    ⟨⟨⟨{ hinvW.sparse.lengths.core_ok with
                           vals_len := hinvW.sparse.lengths.core_ok.vals_len },
                       hinvW.sparse.lengths.scratch_ok⟩,
                      ⟨F_curW, s12a_fullWitnessInv_with_unflushed hwW⟩⟩,
                     hinvW.sparse.2.1, hinvW.sparse.2.2.1, hinvW.sparse.2.2.2.1,
                     hinvW.sparse.2.2.2.2⟩
                exact hJ3u () _ ⟨_, hinvW', hclW, hfuW, fullM6HdrMem_unfocus (by assumption)⟩
              · intro J_brk hJ_brk
                have hJ_brkF : ∀ (sW : FullState) m_w,
                    FullM6HdrInv c F0 ext sW → sW.core.cur_level = 0 →
                    sW.core.fuel.toNat ≤ s.core.fuel.toNat →
                    (FullMem c sW ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m_w →
                    J_brk () m_w := fun sW m_w h1 h2 h3 hmW => hJ_brk () m_w ⟨sW, h1, h2, h3, hmW⟩
                c0_hsteps_nogrp
                refine wp_while_state0 (α := FullState)
                  (μ := fun st => st.core.fuel.toNat)
                  (Inv := fun sL mL => FullM6HdrInv c F0 ext sL ∧ sL.core.cur_level = 0 ∧
                    sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) mL) ?_ ?_
                · intro JL hJL; c0_hsteps; exact hJL s3 m3 ⟨hinv3, hcl3, hfu3', hm3f⟩
                · intro JL sL mL ⟨hinvL, hclL, hfuL, hmL⟩ ihL
                  rw [Blocks.get_here]; dsimp only
                  obtain ⟨F_curL, hwL⟩ := hinvL.sparse.1.witness
                  have hpr_le : sL.core.propagated ≤ sL.core.trail_end :=
                    hinvL.sparse.lengths.core_ok.propagated_le
                  c0_hsteps_nogrp
                  · c0_call hSweep
                    refine ⟨c, F0, F_curL, sL, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
                      hinvL.sparse.lengths, hwL, hinvL.sparse.2.2.1, hinvL.sparse.2.2.2.2,
                      fun hpos => by omega, hmL,
                      fun sr2 valsS flagsS lvlS rsnsS trlS tpS teS unassS unflS wvecS wstkS
                        arenaS alenS wlenS wuS fredS niS nrS nbS oomS scS mS
                        hlenS hsr2 hexlenS _ hllS hwS hndS _ _ hsr1 h20S _ hmS => ?_⟩
                    let sS : FullState :=
                      { sL with
                        core := { sL.core with
                          vals := valsS, flags := flagsS, lvl := lvlS, rsns := rsnsS, trl := trlS,
                          trail_pos := tpS, trail_end := teS, unassigned := unassS,
                          unflushed := unflS, wvec := wvecS, wstk := wstkS, arena := arenaS,
                          arena_len := alenS, wlen := wlenS, wusable := wuS,
                          arena_garbage := 0#64, first_reducible := fredS, num_irred := niS,
                          num_redundant := nrS, num_binary := nbS, oom := oomS }
                        scratch := scS }
                    have hinvWS : FullM6HdrInvW c F0 F_curL ext sS :=
                      FullM6HdrInvW.mk_inv hinvL.cfgOk hinvL.extOk
                        ⟨hlenS, hwS, hinvL.sparse.2.1, hndS,
                          ⟨hllS, by
                            change scS.extend_len ≤ c.extend_cap
                            rw [hexlenS]; exact hinvL.sparse.2.2.2.1.2⟩,
                          hinvL.sparse.2.2.2.2⟩
                    have hinvS := hinvWS.toInv
                    c0_hsteps_nogrp
                    · exact s12aPre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfuL
                        (h20S ‹_›).2 (fullM6HdrMem_unfocus hmS)
                    · exact hJ_brkF sS mS hinvS hclL hfuL hmS
                    · refine s12a_call_bcp rfl hProp hinvWS (fullM6HdrMem_unfocus hmS)
                        fun pr2 sP mP hinvWP hclP _ _ hfuP hdomP hrP0 hrP1 hmP => ?_
                      have hinvP := hinvWP.toInv
                      have hfuP' : sP.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuP hfuL
                      c0_hsplit
                      · c0_hsteps
                        exact s12aPre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk
                          hinvP.extOk hfuP' (s12a_conflict_level0_unsat hinvWP.sparseW.2.1
                            (hclP ▸ hclL) (hrP1 ‹_›).2.2) hmP
                      · c0_hsplit
                        · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
                          c0_hsteps
                          exact hJ_brkF sP _ hinvP (hclP ▸ hclL) hfuP' hmPf
                        · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
                          have hpr2_0 : pr2 = 0#64 := by
                            rcases hdomP with rfl | rfl | rfl <;> first | rfl | contradiction
                          have hpeq := (hrP0 hpr2_0).1
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsteps
                              exact hJ_brkF sP _ hinvP (hclP ▸ hclL) hfuP' hmPf
                            · exfalso
                              have hbv_eq : BitVec.ofNat 64 sP.core.propagated =
                                  BitVec.ofNat 64 sP.core.trail_end :=
                                congrArg (BitVec.ofNat 64) hpeq
                              rw [hbv_eq] at *
                              bv_omega
                          · have hsr1_ne : sr2 ≠ 0#64 := by assumption
                            have hsr1_eq : sr2 = 1#64 := by
                              rcases hsr2 with rfl | rfl | rfl | rfl <;>
                                first | rfl | contradiction
                            have hte_lt := (hrP0 hpr2_0).2.2 (by
                              change sL.core.propagated < teS
                              have := (hsr1 hsr1_eq).2; omega)
                            have hfu_lt : sP.core.fuel.toNat < sL.core.fuel.toNat := hte_lt
                            c0_hsteps
                            exact ihL sP _ hfu_lt ⟨hinvP, hclP ▸ hclL, hfuP', hmPf⟩
                  · cases hc
            · intro Jb hJb; c0_hsplit
              · exact hJb () m3 rfl
              · c0_hsplit
                · exact hJb () m3 rfl
                · exact hJ3u () m3 ⟨s3, hinv3, hcl3, hfu3', hm3'⟩
    · exact fun _ hJ2 =>
        s12a_pre_unflushed hProp hSweep hinv1 hcl1' hfu1 (fullM6HdrMem_unfocus hm1f) hJ2 hQ

end PreprocessStep12A

end LeanQbe.T.Examples.Kissat.FullFidelityStep12A
