module

public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 `FullM6Hdr` Decision-Rate & Composed Hook Proofs (`FullM6HdrProof2`)

M1-clean proof module (`public section`, opaque definitions, standard imports, UNSAT-only):
Proves parametric `(Γ : Env)` `Func.wp` contracts for all `6` Group-C functions:
1. `m6_hdr_dr_init` (`m6HdrDrMutSpec`, writes only `M6HdrExt` words `1..7`, zero `FullMem` writes)
2. `m6_hdr_dr_update` (`m6HdrDrMutSpec`, writes only `M6HdrExt` words `1..7`, zero `FullMem` writes)
3. `m6_hdr_dr_allow` (`m6HdrDrAllowSpec`, pure read when initialized, zero `FullMem` writes)
4. `m6_hdr_decide` (`m6HdrDecideSpec`, decision wrapper updating `e[M6W_DR_STATE]`)
5. `m6_hdr_analyze_rsn` (`m6HdrAnalyzeRsnSpec`, glue-bin hook + `full_analyze_rsn`)
6. `m6_hdr_analyze` (`m6HdrAnalyzeSpec`, composing `m6_hdr_update_tier_limits` +
   `m6_hdr_dr_update` + `full_analyze` over disjoint `M6HdrExt` slices)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Hdr

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem bv64_add_small2 {k x : BitVec 64} {n : Nat} (hk : k.toNat = n)
    (hsum : n + x.toNat < 2 ^ 64) : (k + x).toNat = n + x.toNat := by
  rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt hsum]

private theorem w2b_pres_of_init {ext ext1 ext' : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → ext1 = ext) (h2 : M6ExtW2aPres ext1 ext') :
    M6HdrExtInitOk ext → M6ExtW2aPres ext ext' :=
  fun hi => (h1 hi) ▸ h2

private theorem bv32_dec_lit_even2 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : Nat)).setWidth 32).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : v.toNat * 2 ^ 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : v.toNat * 2 ^ 1 < 2 ^ 32)]
  omega

private theorem bv32_dec_lit_odd2 {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (((v <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hev := bv32_dec_lit_even2 hv
  have hor : (((v <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat =
      ((v <<< (1 : Nat)).setWidth 32).toNat ||| 1 := by
    rw [BitVec.toNat_or]; rfl
  rw [hor, hev]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp
  | succ k =>
    have hd1 : (2 * v.toNat + 1) / 2 = v.toNat := by omega
    have hd2 : (2 * v.toNat) / 2 = v.toNat := by omega
    have h10 : (1 : Nat) / 2 = 0 := rfl
    simp [Nat.testBit_succ, hd1, hd2, h10]

private theorem fullSparseInvW_of_core_eq {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (heq : s'.core = s.core) (hpres : FullExtScratchPres s s') :
    FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', ?_, ?_, ?_, ?_, heq ▸ hsp.2.2.2.2.2⟩
  · rw [heq]; exact hsp.2.1
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact hsp.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact hsp.2.2.2.1
  · exact hsp.2.2.2.2.1.of_pres hpres fun r hr => by unfold fullArenaClauseRefs; rwa [heq]

private theorem fullAnaMarksCov_of_core_eq {c : FullCfg} {s s' : FullState}
    (h : FullAnaMarksCov c s) (heq : s'.core = s.core)
    (hws1 : s'.scratch.work_stk1 = s.scratch.work_stk1) : FullAnaMarksCov c s' := by
  unfold FullAnaMarksCov at h ⊢; rwa [heq, hws1]

private theorem fullConflictOkW_of_core_eq {F_cur : List (List Nat)} {s s' : FullState}
    (h : FullConflictOkW F_cur s) (heq : s'.core = s.core) : FullConflictOkW F_cur s' := by
  unfold FullConflictOkW fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits at h ⊢
  rwa [heq]

/-! ## 1. `FullM6Hdr` `decision_rate` Helpers (`3` Functions) -/

theorem m6_hdr_dr_init_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X → Func.wp Γ m6_hdr_dr_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrMutSpec_elim hs
  unfold Func.wp m6_hdr_dr_init_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps
  · exact hQ ext1 m1 hinit1 (w2b_pres_of_init hpres1 (M6ExtW2aPres.refl ext1))
      ((fullM6HdrMem_iff ..).mpr hm1)
  · refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact ((((((hinit1.set_pos _ (by decide)).set_pos _ (by decide)).set_pos _
        (by decide)).set_pos _ (by decide)).set_pos _ (by decide)).set_pos _
        (by decide)).set_pos _ (by decide)
    · refine w2b_pres_of_init hpres1 ?_
      exact (((((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        ((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
          (M6ExtW2aPres.set_w2b _ (by decide) (by decide)))

theorem m6_hdr_dr_update_wp (Γ : Env)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X → Func.wp Γ m6_hdr_dr_update_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrMutSpec_elim hs
  unfold Func.wp m6_hdr_dr_update_body
  c0_hsteps_nogrp
  m6h_call hDrInit
  refine m6HdrDrMutSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hw1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (mode, ()) m2 => m2 = m1 ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
    (fun _ hJm => by
      c0_hsteps
      · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  subst m2
  have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
  have hp_eq : ((2 : BitVec 64) + mode).toNat = 2 + mode.toNat :=
    bv64_add_small2 (n := 2) rfl (by omega)
  have hsb_eq : ((4 : BitVec 64) + mode).toNat = 4 + mode.toNat :=
    bv64_add_small2 (n := 4) rfl (by omega)
  have hse_eq : ((6 : BitVec 64) + mode).toNat = 6 + mode.toNat :=
    bv64_add_small2 (n := 6) rfl (by omega)
  have hp_lt : ((2 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hp_eq]; omega
  have hsb_lt : ((4 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hsb_eq]; omega
  have hse_lt : ((6 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hse_eq]; omega
  c0_hsteps_nogrp
  · c0_hsteps
    refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (((hinit1.set_pos _ (by decide)).set_pos _ (by rw [hp_eq]; omega)).set_pos _
        (by rw [hsb_eq]; omega)).set_pos _ (by rw [hse_eq]; omega)
    · intro hi
      exact (hw1 hi).trans (((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
        (M6ExtW2aPres.set_w2b _ (by rw [hp_eq]; omega) (by rw [hp_eq]; omega))).trans
        ((M6ExtW2aPres.set_w2b _ (by rw [hsb_eq]; omega) (by rw [hsb_eq]; omega)).trans
          (M6ExtW2aPres.set_w2b _ (by rw [hse_eq]; omega) (by rw [hse_eq]; omega))))
  · obtain ⟨ext2, hm2, hl2, hinit2, hw12⟩ :
        ∃ ext2 : List (BitVec 64), (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m ∧
          ext2.length = 288 ∧ M6HdrExtInitOk ext2 ∧ M6ExtW2aPres ext1 ext2 :=
      ⟨_, hm, by simp [hl1], hinit1.set_pos _ (by rw [hp_eq]; omega),
        M6ExtW2aPres.set_w2b _ (by rw [hp_eq]; omega) (by rw [hp_eq]; omega)⟩
    have hsb2_lt : ((4 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, hsb_eq]; omega
    have hse2_lt : ((6 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, hse_eq]; omega
    let m2 := m
    have hm2' : (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m2 := hm2
    clear hm hm2
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
      (fun _ (_d, ()) m3 hm3 => ?_) (fun _ hJd => by c0_hsteps <;> exact hJd (_, ()) m2 rfl)
    subst m3
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
      (fun _ (_dc, ()) m3 hm3 => ?_) (fun _ hJc => by c0_hsteps <;> exact hJc (_, ()) m2 rfl)
    subst m3
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
      (fun _ (sb, ()) m3 hm3 => ?_) (fun _ hJsb => by c0_hsteps <;> exact hJsb (_, ()) m2 rfl)
    subst m3
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
      (fun _ (se, ()) m3 hm3 => ?_)
      (fun _ hJse => by
        c0_hsteps_nogrp
        · refine wp_join_group (ts := [i64]) (fun _ m4 => m4 = m2)
            (fun _ (se1, ()) m4 hm4 => by subst m4; exact hJse (se1, ()) m2 rfl)
            (fun _ hJse1 => by c0_hsteps <;> exact hJse1 (_, ()) m2 rfl)
        · exact hJse (_, ()) m2 rfl)
    subst m3
    c0_hsteps
    refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (hinit2.set_pos sb (by rw [hsb_eq]; omega)).set_pos se (by rw [hse_eq]; omega)
    · intro hi
      exact ((hw1 hi).trans hw12).trans
        ((M6ExtW2aPres.set_w2b sb (by rw [hsb_eq]; omega) (by rw [hsb_eq]; omega)).trans
          (M6ExtW2aPres.set_w2b se (by rw [hse_eq]; omega) (by rw [hse_eq]; omega)))

theorem m6_hdr_dr_allow_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrAllowSpec a m Q X → Func.wp Γ m6_hdr_dr_allow_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrAllowSpec_elim hs
  unfold Func.wp m6_hdr_dr_allow_body
  c0_hsteps_nogrp
  m6h_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  · exact hQ true ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)
  · refine wp_join_group (ts := [i64]) (fun (mode, ()) m2 => m2 = m1 ∧ (mode = 0#64 ∨ mode = 1#64))
      (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
      (fun _ hJm => by
        c0_hsteps
        · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
        · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
    subst m2
    have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
    have hsb_lt : ((4 : BitVec 64) + mode).toNat < ext1.length := by
      rw [hl1, bv64_add_small2 (n := 4) rfl (by omega)]; omega
    have hse_lt : ((6 : BitVec 64) + mode).toNat < ext1.length := by
      rw [hl1, bv64_add_small2 (n := 6) rfl (by omega)]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m1)
      (fun _ (_sd, ()) m2 hm2 => by
        subst m2; c0_hsteps
        · exact hQ true ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)
        · exact hQ _ ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1))
      (fun _ hJsd => by c0_hsteps <;> exact hJsd (_, ()) m1 rfl)

/-! ## 2. Repointed `m6_hdr_decide`, `m6_hdr_analyze_rsn` & Composed `m6_hdr_analyze` -/

theorem m6_hdr_decide_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, Full.fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDecideSpec a m Q X → Func.wp Γ m6_hdr_decide_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩ := m6HdrDecideSpec_elim hs
  have hcfg := hinv.cfgOk
  have hext := hinv.extOk
  have hcore0 := hinv.coreInv
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold Func.wp m6_hdr_decide_body
  c0_hsteps_nogrp
  m6h_call hNextDec
  refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hcore0.lengths,
    (fullM6HdrMem_iff ..).mp hm,
    fun ⟨chosen, ⟨⟩⟩ s1 m1 hs1_core hs1_safe hch hm1 => ?_⟩
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
    Full.fullSafetySlice_safe] at hs1_core hs1_safe hm1 hch ⊢
  clear hs m hm
  have hcs1 : s1.core = s.core := @Full.fullCoreState_agrees_with_scratch c s s1 hs1_core
  have hinv1 : FullCoreInv c F0 s1 := hcore0.with_scratch hs1_safe hs1_core
  rcases s1 with ⟨c1, sc1⟩; dsimp only at hcs1; subst hcs1
  have hcl1 := hinv1.lengths.core_ok
  have hsc1_ok := hinv1.lengths.scratch_ok
  have hcv1 : s.core.cur_vars ≤ c.max_vars := hcl1.cur_vars_le
  have hph1 := hsc1_ok.phases_len; have hptgt1 := hsc1_ok.phases_target_len
  have hftrl1 : s.core.frame_trail.length = c.max_vars + 1 := hcl1.frame_trail_len
  have hfdec1 : s.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
  c0_hsteps_nogrp
  · exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.cur_level s.core.unassigned
      s.core.unflushed sc1 ext m1 (FullM6HdrCoreInv.mk_inv hcfg hext hinv1) hch.1 (Or.inl rfl)
      (fun _ => ⟨rfl, rfl⟩) (fun h1 => by cases h1) ((fullM6HdrMem_iff ..).mpr hm1)
  · have hch_ne : chosen ≠ 0xFFFFFFFFFFFFFFFF#64 := hc
    obtain ⟨hv_lt, hval0⟩ := hch.2.resolve_left hch_ne
    have hch_lt_max : chosen.toNat < c.max_vars := by omega
    have hch_lt30 : chosen.toNat < 2 ^ 30 := by omega
    c0_hsteps_nogrp
    refine wp_join_group (fun (dph, ()) m2 => m1 = m2) ?_ ?_
    · rintro _ ⟨dph, ⟨⟩⟩ _ hm2; rcases hm2 with rfl
      c0_hsteps_nogrp
      refine wp_join_group (fun (lit, ()) m3 =>
        m1 = m3 ∧ (lit.toNat = 2 * chosen.toNat ∨ lit.toNat = 2 * chosen.toNat + 1)) ?_ ?_
      · rintro _ ⟨lit, ⟨⟩⟩ _ ⟨hm3, hlit_eq⟩; rcases hm3 with rfl
        have hnlvl_nat : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat =
            s.core.cur_level + 1 := by
          have hte1 : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
          obtain ⟨_, hw⟩ := hinv1.witness
          have hcl1_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (1#64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        c0_hsteps_nogrp
        · exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
            s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.cur_level s.core.unassigned
            s.core.unflushed sc1 ext m1 (FullM6HdrCoreInv.mk_inv hcfg hext hinv1) hch.1 (Or.inl rfl)
            (fun _ => ⟨rfl, rfl⟩) (fun h1 => by cases h1) ((fullM6HdrMem_iff ..).mpr hm1)
        · have hnlvl_le : s.core.cur_level + 1 ≤ c.max_vars := by
            have hte1 : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
            obtain ⟨_, hw⟩ := hinv1.witness
            have hcl1_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
            have hlt : ¬ c.max_vars % 2 ^ 64 <
                (s.core.cur_level + (1#64).toNat) % 2 ^ 64 := hc
            rw [Nat.mod_eq_of_lt (by omega), show (1#64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)] at hlt
            omega
          have ⟨_, hun, hte_lt, _⟩ := Full.full_decide_preserves_fullCore hinv1 hsc1_ok
            hcl1.flags_len hv_lt hval0 hlit_eq (flags' := s.core.flags)
            (unas' := s.core.unassigned) (unfl' := s.core.unflushed)
          let nlvl := s.core.cur_level + 1
          let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
          let fdec' := s.core.frame_dec.set nlvl lit
          let s2 : FullState :=
            { core := { s.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl }
              scratch := sc1 }
          have hlen2 : s2.LengthsOk c :=
            ⟨{ hcl1 with
                frame_trail_len := by simp [s2, ftrl', hftrl1]
                frame_dec_len := by simp [s2, fdec', hfdec1] }, hsc1_ok⟩
          have hm2' : (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m := by
            have hte_le : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
            have hte_bv : (BitVec.ofNat 64 s.core.trail_end).setWidth 32 =
                BitVec.ofNat 32 s.core.trail_end := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : s.core.trail_end < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : s.core.trail_end < 2 ^ 32)]
            have hnlvl_nat' : (BitVec.ofNat 64 s.core.cur_level + 1).toNat =
                s.core.cur_level + 1 := hnlvl_nat
            simpa only [s2, ftrl', fdec', nlvl, hnlvl_nat', hte_bv] using hm
          have hng : ¬ (s2.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s2.core.trail_end ∨
              s2.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
            change ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
              s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
            simp only [hun, ne_eq, not_true_eq_false, or_false]
            have hte_lt' : s.core.trail_end < s.core.cur_vars := hte_lt
            omega
          c0_call hAssign
          refine ⟨c, s2, array64 (c.hdr - 2304) ext ⋆ R, rfl, hlen2,
            by dsimp [s2, nlvl]; omega, hm2', ?_⟩
          simp only [hng, ↓reduceIte]
          intro flags' unas' phases' m3 hfl_l hph_l hm3
          clear hm
          have hsc3 : ({ sc1 with phases := phases' } : FullScratch).LengthsOk c :=
            { hsc1_ok with phases_len := hph_l }
          have ⟨hinv3, _, _, _⟩ := Full.full_decide_preserves_fullCore hinv1 hsc3 hfl_l
            hv_lt hval0 hlit_eq (flags' := flags') (unas' := unas') (unfl' := s.core.unflushed)
          have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
          have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
          let s3 : FullState :=
            { core := { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
                flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
                rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
                trl := s.core.trl.set s.core.trail_end lit,
                trail_pos := s.core.trail_pos.set (lit.toNat / 2)
                  (BitVec.ofNat 32 s.core.trail_end),
                frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1,
                cur_level := nlvl, unassigned := unas' },
              scratch := { sc1 with phases := phases' } }
          have hm3' : (FullMem c s3 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m3 := by
            simpa only [s3, s2, hnl_ne0, ↓reduceIte, hff] using hm3
          have hinv3' : FullCoreInv c F0 s3 := by
            simpa only [s3, nlvl, hnl_ne0, ↓reduceIte] using hinv3
          c0_hsteps_nogrp
          m6h_call hDrInit
          refine m6HdrDrMutSpec_of hcfg hext hinv3'.lengths ((fullM6HdrMem_iff ..).mpr hm3')
            fun ext4 m4 hinit4 hw4 hm4 => ?_
          have hl4 : ext4.length = 288 := hinit4.toOk.len
          rw [fullM6HdrMem_iff] at hm4
          c0_hsteps
          · refine hQ 1#64 s3.core.vals flags' s3.core.lvl s3.core.rsns s3.core.trl
              s3.core.trail_pos ftrl' fdec' (s.core.trail_end + 1) nlvl unas' s.core.unflushed
              s3.scratch _ _ ?_ ⟨hch.1.1, hch.1.2⟩ (Or.inr rfl) (fun h0 => by cases h0) ?_
              ((fullM6HdrMem_iff ..).mpr (by assumption))
            · exact FullM6HdrCoreInv.mk_inv hcfg (hinit4.set_pos _ (by decide)).toOk hinv3'
            · exact fun _ => ⟨rfl, rfl, hinit4.set_pos _ (by decide),
                fun hi => (hw4 hi).trans (M6ExtW2aPres.set_w2b _ (by decide) (by decide))⟩
          · exact hQ 1#64 s3.core.vals flags' s3.core.lvl s3.core.rsns s3.core.trl
              s3.core.trail_pos ftrl' fdec' (s.core.trail_end + 1) nlvl unas' s.core.unflushed
              s3.scratch ext4 m4 (FullM6HdrCoreInv.mk_inv hcfg hinit4.toOk hinv3')
              ⟨hch.1.1, hch.1.2⟩ (Or.inr rfl) (fun h0 => by cases h0)
              (fun _ => ⟨rfl, rfl, hinit4, hw4⟩) ((fullM6HdrMem_iff ..).mpr hm4)
      · intro Jlit hJlit; c0_hsteps
        · exact hJlit ((chosen <<< (1 : Nat)).setWidth 32 ||| 1#32, ()) m1
            ⟨rfl, Or.inr (bv32_dec_lit_odd2 hch_lt30)⟩
        · exact hJlit ((chosen <<< (1 : Nat)).setWidth 32, ()) m1
            ⟨rfl, Or.inl (bv32_dec_lit_even2 hch_lt30)⟩
    · intro Jdph hJdph; c0_hsteps
      · exact hJdph _ m1 rfl
      · exact hJdph _ m1 rfl
      · exact hJdph _ m1 rfl

theorem m6_hdr_analyze_rsn_wp (Γ : Env)
    (hRecUsed : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_record_used" [i64, i64] [] a m Q X)
    (hAnaRsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m6HdrAnalyzeRsnSpec a m Q X → Func.wp Γ m6_hdr_analyze_rsn_body a m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hlen, hcut, hcov, htl, htc, href, hm,
    hQ⟩ := m6HdrAnalyzeRsnSpec_elim hs
  unfold Func.wp m6_hdr_analyze_rsn_body
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ ext1 s1, s1.core = s.core ∧ s1.LengthsOk c ∧ M6HdrScratchPres s s1 ∧
      M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext → M6ExtW2bPres ext ext1) ∧
      (FullM6HdrMem c ext1 s1 ⋆ R) m1)
    (fun _ () m1 ⟨ext1, s1, heq1, hlen1, hpres1, hext1, hw1, hm1⟩ => ?_)
    (fun _ hJr => ?_)
  · clear hs hm
    c0_hsteps_nogrp
    c0_call hAnaRsn
    have href1 : rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
        rsn.toNat ∈ fullArenaClauseRefs s1 := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rwa [heq1]
    refine ⟨c, F0, F_cur, cut, s1, array64 (c.hdr - 2304) ext1 ⋆ R, rfl, hlen1,
      heq1 ▸ hcut, fullAnaMarksCov_of_core_eq hcov heq1 hpres1.ws1,
      heq1 ▸ htl, heq1 ▸ htc, href1, (fullM6HdrMem_iff ..).mp hm1,
      fun ok mrk' tmp' tc' tl' mcl' arena' sc' m' hlen' hcut' hcov' hpre' hws2'
        htl_le htl_cv htc_le hrefs' har_pres hmrk_keep htmp_keep hmrk_new hj_ok hj_nodup
        htc_diff hres_sz hok_post hm' => ?_⟩
    c0_hsteps
    let s2 : FullState :=
      { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr_len := mcl', arena := arena' }
        scratch := sc' }
    have hs2_eq :
        ({ s1 with
            core := { s1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                   min_clr_len := mcl', arena := arena' }
            scratch := sc' } : FullState) = s2 := by
      cases s1; cases s; dsimp only at heq1; simp only [s2]; subst heq1; rfl
    rw [hs2_eq] at hlen' hcut' hcov' hrefs' har_pres hm'
    have hpre2 : FullExtScratchPres s s2 :=
      ⟨hpre'.1.trans hpres1.extPres.1, hpre'.2.trans hpres1.extPres.2⟩
    have hrl_eq : fullRsnLits s1 rsn = fullRsnLits s rsn := by
      unfold fullRsnLits fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      rw [heq1]
    have hmrk_s : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8 := by
      intro v hv hne; exact (hmrk_keep v hv (heq1 ▸ hne)).trans (by rw [heq1])
    have hmrk_new_s : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 →
        mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level := by
      intro v hv hz hnz
      have h := hmrk_new v hv (heq1 ▸ hz) hnz
      rw [hrl_eq, heq1] at h; exact h
    have hj_ok_s : ∀ j, s.core.tmp_len ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8 := by
      intro j hj1 hj2
      have h := hj_ok j (heq1 ▸ hj1) hj2
      rwa [hrl_eq, heq1] at h
    have hres_s : sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64
        ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length := by
      rw [hres_sz, hpres1.res_sz, heq1]
    have hok_s : ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64
          ((fullRsnLits s rsn).countP fun l =>
            decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧
          (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                  (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))) := by
      intro hok
      have h := hok_post hok
      rwa [hrl_eq, hpres1.ant_sz, heq1] at h
    exact hQ ok mrk' tmp' tc' tl' mcl' arena' sc' ext1 m' hext1 hw1 hlen' hcut' hcov' hpre2
      (hws2'.trans hpres1.ws2) (heq1 ▸ htl_le) (heq1 ▸ htl_cv) (heq1 ▸ htc_le)
      (by unfold fullArenaClauseRefs fullArenaClauseRefsCore at hrefs' ⊢
          rw [heq1] at hrefs'; exact hrefs')
      (fun r hr => by
        have hp := har_pres r
          (by unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rw [heq1]; exact hr)
        unfold fullArenaClauseSize fullArenaClauseSizeCore fullArenaClauseGarb
          fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLits
          fullArenaClauseLitsCore at hp ⊢
        rwa [heq1] at hp)
      hmrk_s (by intro k hk; exact (htmp_keep k (heq1 ▸ hk)).trans (by rw [heq1]))
      hmrk_new_s hj_ok_s
      (fun j1 j2 h1 h2 h3 => hj_nodup j1 j2 (heq1 ▸ h1) h2 h3) (by rwa [heq1] at htc_diff)
      hres_s hok_s ((fullM6HdrMem_iff ..).mpr hm')
  · rw [fullM6HdrMem_iff] at hm
    c0_hsplit
    · c0_hsplit
      · c0_hsplit
        · have hal_le := hlen.core_ok.arena_len_le
          have har_len := hlen.core_ok.arena_len_arr
          have hmax : c.arena_cap < 2 * dimacsBound := c.harena
          unfold dimacsBound at hmax
          have hal_3 : rsn.toNat + 3 ≤ s.core.arena_len := by
            have h32 := rsn.isLt
            have h3 : (3 : BitVec 64).toNat = 3 := rfl
            rw [h3, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
            omega
          have hrsn_ar : (rsn.setWidth 64).toNat < s.core.arena.length := by
            have h32 := rsn.isLt
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
          have hrsn2_ar : (rsn.setWidth 64 + 2).toNat < s.core.arena.length := by
            have h32 := rsn.isLt
            have hsw : (rsn.setWidth 64).toNat = rsn.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            rw [BitVec.toNat_add, hsw, show (2 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega)]
            omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun () m1 => ∃ ext1 s1, s1.core = s.core ∧ s1.LengthsOk c ∧ M6HdrScratchPres s s1 ∧
              M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext → M6ExtW2bPres ext ext1) ∧
              (FullM6HdrMem c ext1 s1 ⋆ R) m1)
            (fun _ () m1 h1 => hJr () m1 h1)
            (fun _ hJs => by
              c0_hsteps
              · m6h_call hRecUsed
                refine m6HdrW2aSpec_of rfl hcfg hext hlen ((fullM6HdrMem_iff ..).mpr hm)
                  fun () ext1 s1 m1 hcore1 hlen1 hsc1 hext1 hw1 hm1 => ?_
                c0_hsteps
                exact hJs () m1 ⟨ext1, s1, hcore1, hlen1, hsc1, hext1, fun hi => (hw1 hi).2, hm1⟩
              · exact hJs () m ⟨ext, s, rfl, hlen, M6HdrScratchPres.refl s, hext,
                  fun _ => M6ExtW2bPres.refl ext, (fullM6HdrMem_iff ..).mpr hm⟩
              · exact hJs () m ⟨ext, s, rfl, hlen, M6HdrScratchPres.refl s, hext,
                  fun _ => M6ExtW2bPres.refl ext, (fullM6HdrMem_iff ..).mpr hm⟩
              · exact hJs () m ⟨ext, s, rfl, hlen, M6HdrScratchPres.refl s, hext,
                  fun _ => M6ExtW2bPres.refl ext, (fullM6HdrMem_iff ..).mpr hm⟩)
        · c0_hsteps
          exact hJr () m ⟨ext, s, rfl, hlen, M6HdrScratchPres.refl s, hext,
            fun _ => M6ExtW2bPres.refl ext, (fullM6HdrMem_iff ..).mpr hm⟩
      · c0_hsteps
        exact hJr () m ⟨ext, s, rfl, hlen, M6HdrScratchPres.refl s, hext,
          fun _ => M6ExtW2bPres.refl ext, (fullM6HdrMem_iff ..).mpr hm⟩
    · c0_hsteps
      exact hJr () m ⟨ext, s, rfl, hlen, M6HdrScratchPres.refl s, hext,
        fun _ => M6ExtW2bPres.refl ext, (fullM6HdrMem_iff ..).mpr hm⟩

theorem m6_hdr_analyze_wp (Γ : Env)
    (hUpd : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_update_tier_limits" [i64] [] a m Q X)
    (hDrUpd : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_update" [i64] [] a m Q X)
    (hAna : ∀ a m Q X, Full.fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6HdrAnalyzeSpec a m Q X → Func.wp Γ m6_hdr_analyze_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hconf, hm, hQ⟩ := m6HdrAnalyzeSpec_elim hs
  have hcfg := hinv.cfgOk
  have hext := hinv.extOk
  have hsp := hinv.sparseW
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp m6_hdr_analyze_body
  c0_hsteps_nogrp
  · have hcl0 : s.core.cur_level = 0 := by
      have hle := hsp.2.1.cur_level_le
      have hte := hsp.1.core_ok.trail_end_le
      have hcv := hsp.1.core_ok.cur_vars_le
      have hmv := c.hmaxv; unfold dimacsBound at hmv
      have h0 : BitVec.ofNat 64 s.core.cur_level = 0#64 := hc
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      exact h1
    exact hQ 20#64 ext s m hext hsp.1 (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _)
      ⟨rfl, fun _ => ⟨hsp.toOtfs, Nat.le_refl _, rfl⟩⟩
      (fun _ => level0_unsat_of_conflict_okW hsp.2.1 hcl0 hconf)
      (fun h0 => by cases h0) (fun h1 => by cases h1) ((fullM6HdrMem_iff ..).mpr hm)
  · refine wp_join_group (ts := [])
      (fun () m2 => ∃ ext2 s2, s2.core = s.core ∧ s2.LengthsOk c ∧ M6HdrScratchPres s s2 ∧
        M6HdrExtOk ext2 ∧ (FullM6HdrMem c ext2 s2 ⋆ R) m2)
      (fun _ () m2 ⟨ext2, s2, heq2, hlen2, hsc2, hext2, hm2⟩ => ?_)
      (fun _ hJp => ?_)
    · have hsp2 : FullSparseInvW c F0 F_cur s2 :=
        fullSparseInvW_of_core_eq hsp hlen2 heq2 hsc2.extPres
      c0_hsteps_nogrp
      m6h_call hAna
      refine fullM6Hdr_frame_analyze hsp2 (fullConflictOkW_of_core_eq hconf heq2) hm2
        fun r s3 m3 hlen3 hdom hcv3 hfu3 ⟨hws3, h20s⟩ hu3 h0 h1 hm3 => ?_
      c0_hsteps
      exact hQ r ext2 s3 m3 hext2 hlen3 hdom (by rw [heq2] at hcv3; exact hcv3)
        (by rw [heq2] at hfu3; exact hfu3)
        ⟨hws3.trans hsc2.ws2, fun h20 => by
          have ⟨ho20, hcl20, hdm20⟩ := h20s h20
          rw [heq2] at hcl20 hdm20; exact ⟨ho20, hcl20, hdm20⟩⟩
        hu3 h0 (fun h1eq => by
          have ⟨hsp3, hcl3⟩ := h1 h1eq
          rw [heq2] at hcl3
          exact ⟨FullM6HdrInvW.mk_inv hcfg hext2 hsp3, hcl3⟩) hm3
    · c0_hsteps_nogrp
      · m6h_call hUpd
        refine m6HdrW2aSpec_of rfl hcfg hext hsp.1 ((fullM6HdrMem_iff ..).mpr hm)
          fun () ext1 s1 m1 hcore1 hlen1 hsc1 hext1 _ hm1 => ?_
        c0_hsteps_nogrp
        m6h_call hDrUpd
        refine m6HdrDrMutSpec_of hcfg hext1 hlen1 hm1 fun ext2 m2 hinit2 _ hm2 => ?_
        c0_hsteps
        exact hJp () m2 ⟨ext2, s1, hcore1, hlen1, hsc1, hinit2.toOk, hm2⟩
      · exact hJp () m ⟨ext, s, rfl, hsp.1, M6HdrScratchPres.refl s, hext,
          (fullM6HdrMem_iff ..).mpr hm⟩

end LeanQbe.T.Examples.Kissat.FullM6Hdr
