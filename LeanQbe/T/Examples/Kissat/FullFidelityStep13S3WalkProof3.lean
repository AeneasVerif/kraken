/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Walk
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Spec
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas

/-!
# Kissat Fidelity Step 13 Shard S3-A Proofs — Part 3 (`FullFidelityStep13S3WalkProof3`)

Callee-parametric (`Γ : Env`, `XPost := False`, `0` SAT model proofs) `Func.wp` proof for
`full_warmup_m7_step13_wp` (`step13WarmupM6Spec`, `FullM6HdrMem`-threaded).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM6Hdr
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Warmup Helpers -/

section Helpers

private theorem w3_shl1 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt hx]

private theorem w3_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem w3_arenaPermEq_refl (s : FullCoreState) : FullArenaPermEq s s :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem w3_arenaPermEq_trans {s1 s2 s3 : FullCoreState}
    (h1 : FullArenaPermEq s1 s2) (h2 : FullArenaPermEq s2 s3) : FullArenaPermEq s1 s3 := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr => ?_⟩
  have hr1 : r ∈ fullArenaClauseRefsCore s2 := by rw [h1.2.1]; exact hr
  obtain ⟨hs1, hg1, hp1⟩ := h1.2.2 r hr
  obtain ⟨hs2, hg2, hp2⟩ := h2.2.2 r hr1
  exact ⟨hs2.trans hs1, hg2.trans hg1, hp2.trans hp1⟩

private theorem w3_sparse_with_fuel_and_scratch {c : FullCfg} {F0 : CNF Nat}
    {s s' : FullState} {fuel' : BitVec 64}
    (hsp : FullSparseInv c F0 s) (hcore : s'.core = { s.core with fuel := fuel' })
    (hlen : s'.LengthsOk c) (hpres : FullExtScratchPres s s') :
    FullSparseInv c F0 s' :=
  hsp.with_fuel_scratch hlen hcore hpres

private theorem w3_lit_pos_shl64 {r : BitVec 64} (hr : r.toNat < 2 ^ 29) :
    ((r <<< BitVec.signExtend 64 1#32).truncate 32).toNat = 2 * r.toNat := by
  change (BitVec.setWidth 32 (r <<< (1 : Nat))).toNat = 2 * r.toNat
  rw [BitVec.toNat_setWidth, w3_shl1 (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem w3_lit_neg_shl64 {r : BitVec 64} (hr : r.toNat < 2 ^ 29) :
    (((r <<< BitVec.signExtend 64 1#32).truncate 32) ||| 1#32).toNat = 2 * r.toNat + 1 := by
  rw [BitVec.toNat_or, w3_lit_pos_shl64 hr, show (1#32 : BitVec 32).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    simp [Nat.testBit_succ, show (2 * r.toNat + 1) / 2 = r.toNat by omega,
      show (2 * r.toNat) / 2 = r.toNat by omega]

private theorem w3_sparse_with_probing_st {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (p st : BitVec 64) :
    FullSparseInv c F0 (FullState.mk { s.core with probing := p }
      { s.scratch with search_ticks := st }) := by
  obtain ⟨⟨⟨hc, hs⟩, F_cur, hw⟩, hlm, hnd, hscr, hd0⟩ := hsp
  refine ⟨⟨⟨{ hc with }, { hs with }⟩, F_cur,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    hlm, hnd, hscr, hd0⟩

private theorem w3_backtrack_sparse_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    (hhdr : args.fst.val = c.hdr) (hsp : FullSparseInv c F0 s)
    (htgt : args.snd.fst.val.toNat ≤ s.core.cur_level) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = min s.core.cur_level args.snd.fst.val.toNat →
      s'.core.fuel = s.core.fuel → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_backtrack" args k) m := by
  obtain ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hscr, hd0⟩ := hsp
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  have htv : args.snd.fst.val.toNat < s.core.cur_level → args.snd.fst.val.toNat < c.max_vars := by
    intro hlt; have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  refine wp_call_of_spec args k
    (hBT _ _ _ _ ⟨c, s, R, hhdr, hlen, hcl_lt, htv, hw.trail_lits_lt, hm, ?_⟩)
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hs' _ _ hcl hpres _ _ _ hw1 _ hm'
  have hperm : FullArenaPermEq s.core s'.core := ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩
  have hsp' : FullSparseInv c F0 s' :=
    ⟨⟨hs', F_cur, hw1 F0 F_cur hw htgt⟩, hlm, hnd, hscr.of_pres hpres.1 (fun _ hr => hr), hd0⟩
  exact hk s' m' hsp' hperm rfl hcl rfl hpres.1 hm'

end Helpers

/-! ## 2. `full_warmup_m7_step13_wp` (`step13WarmupM6Spec`) -/

/-- Step-13 `full_warmup_m7` satisfies `step13WarmupM6Spec`: `FullM6HdrMem`-threaded warmup calling
`S2`'s `full_propagate_beyond_m7` (`step13PropBeyondM6Spec`). -/
theorem full_warmup_m7_step13_wp (Γ : Env)
    (hNDV : ∀ a m Q X, fullNextDecVarSpec a m Q X → Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropBey : ∀ a m Q X, step13PropBeyondM6Spec a m Q X →
      Γ "full_propagate_beyond_m7" [i64] [i64] a m Q X)
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, step13WarmupM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_warmup_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  have hcfg := hinv.cfgOk; have hext := hinv.extOk; have hsp := hinv.sparse
  have hlen := hsp.lengths
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hcl0_lt : s.core.cur_level ≤ s.core.cur_vars := by
    obtain ⟨_, hw0⟩ := hsp.1.witness; exact Nat.le_trans hw0.cur_level_le hlen.core_ok.trail_end_le
  rw [fullM6HdrMem_iff] at hm
  have hret0 : Q () m := hQ ext s m hinv (w3_arenaPermEq_refl _) rfl rfl
    (Nat.le_refl _) (fun h => h) ⟨rfl, rfl⟩ ((fullM6HdrMem_iff ..).mpr hm)
  dsimp only [Func.wp, FullFidelityStep13S3.full_warmup_m7_body]
  c0_hsteps_nogrp; c0_hsteps_nogrp
  all_goals try exact hret0
  have hcv_le_entry : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hcl_entry : s.core.cur_level = 0 := by
    have hcl_eq0 : BitVec.ofNat 64 s.core.cur_level = 0 := by assumption
    have h1 := congrArg BitVec.toNat hcl_eq0
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] using h1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun _ mE => ∃ extE sE, FullM6HdrInv c F0 extE sE ∧ FullArenaPermEq s.core sE.core ∧
      sE.core.cur_vars = s.core.cur_vars ∧ sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      FullExtScratchPres s sE ∧ (FullMem c sE ⋆ (array64 (c.hdr - 2304) extE ⋆ R)) mE)
    (fun _ _ mE ⟨extE, sE, hinvE, hpermE, hcvE, hfuelE, hpresE, _hmE⟩ => by
      c0_hsteps_nogrp
      let sE1 : FullState := FullState.mk { sE.core with probing := 1#64 } sE.scratch
      have hspE1 : FullSparseInv c F0 sE1 := w3_sparse_with_probing_st hinvE.sparse 1#64
        sE.scratch.search_ticks
      have hpermE1 : FullArenaPermEq s.core sE1.core := hpermE
      refine w3_backtrack_sparse_call hBT rfl hspE1 (Nat.zero_le _) ‹_›
        fun sB mB hspB hpermB hcvB hclB hfuelB hpresB _hmB => ?_
      c0_hsteps
      let sF : FullState := FullState.mk { sB.core with probing := s.core.probing }
        { sB.scratch with search_ticks := s.scratch.search_ticks }
      have hinvF : FullM6HdrInv c F0 extE sF := .mk_inv hcfg hinvE.extOk
        (w3_sparse_with_probing_st hspB s.core.probing s.scratch.search_ticks)
      have hclF : sF.core.cur_level = s.core.cur_level := by
        show sB.core.cur_level = s.core.cur_level; rw [hclB, hcl_entry]; simp
      have hfuelF : sF.core.fuel.toNat ≤ s.core.fuel.toNat := by
        change sB.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfuelB]; exact hfuelE
      exact hQ extE sF _ hinvF (w3_arenaPermEq_trans hpermE1 hpermB) (hcvB.trans hcvE) hclF hfuelF
        (fun h => h) ⟨hpresB.1.trans hpresE.1, hpresB.2.trans hpresE.2⟩
        ((fullM6HdrMem_iff ..).mpr ‹_›))
    (fun J46E hJ46E => by
      refine wp_loop_group (ts := [i64])
        (fun fn ⟨k, ⟨⟩⟩ mL => ∃ extL sL, k.toNat ≤ s.core.cur_vars ∧
          fn = s.core.cur_vars - k.toNat ∧ FullM6HdrInv c F0 extL sL ∧
          FullArenaPermEq s.core sL.core ∧ sL.core.cur_vars = s.core.cur_vars ∧
          sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sL ∧
          (FullMem c sL ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) mL) ?_ ?_
      · intro J46 fn ⟨k, ⟨⟩⟩ mL hJ46
          ⟨extL, sL, hk_le, hfn, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        have hlenL := hinvL.sparse.lengths
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ46E (k, ()) mL ⟨extL, sL, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        have hk_lt : k.toNat < s.core.cur_vars := by
          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
        have hk1 : (k + 1#64).toNat = k.toNat + 1 := w3_add1 (by omega)
        have hlt_n : s.core.cur_vars - (k.toNat + 1) < fn := by omega
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ46E (k, ()) mL ⟨extL, sL, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ46E (k, ()) mL ⟨extL, sL, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ46E (k, ()) mL ⟨extL, sL, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hNDV _ _ _ _ ⟨c, sL, array64 (c.hdr - 2304) extL ⋆ R, rfl,
          hlenL, hmL, ?_⟩)
        rintro ⟨r, ⟨⟩⟩ sL2 mL2 hcoreL2 hlenL2 ⟨hpresL2, hresL2⟩ hmL2
        dsimp only [PreservesCoreSlice, fullSafetySlice] at hcoreL2 hlenL2 hmL2
        have hinvL2 : FullM6HdrInv c F0 extL sL2 :=
          .mk_inv hcfg hinvL.extOk (w3_sparse_with_fuel_and_scratch hinvL.sparse
            (by rw [hcoreL2]) hlenL2 hpresL2)
        have hpermL2 : FullArenaPermEq s.core sL2.core := by rw [hcoreL2]; exact hpermL
        have hcvL2 : sL2.core.cur_vars = s.core.cur_vars := by rw [hcoreL2]; exact hcvL
        have hfuelL2 : sL2.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcoreL2]; exact hfuelL
        have hpresL20 : FullExtScratchPres s sL2 :=
          ⟨hpresL2.1.trans hpresL.1, hpresL2.2.trans hpresL.2⟩
        c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps; exact hJ46E (k, ()) mL2
            ⟨extL, sL2, hinvL2, hpermL2, hcvL2, hfuelL2, hpresL20, hmL2⟩
        have hr_spec : r.toNat < sL2.core.cur_vars ∧
            sL2.core.vals[2 * r.toNat]?.getD 0#8 = 0#8 := by
          rcases hresL2 with h0 | hok
          · exact absurd h0 hc
          · simpa [hcoreL2] using hok
        have hr_lt : r.toNat < c.max_vars := by have := hlenL2.core_ok.cur_vars_le; omega
        have hr_ph : r.toNat < sL2.scratch.phases.length := by
          rw [hlenL2.scratch_ok.phases_len]; exact hr_lt
        have hr_pt : r.toNat < sL2.scratch.phases_target.length := by
          rw [hlenL2.scratch_ok.phases_target_len]; exact hr_lt
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i8])
          (fun _ m61 => (FullMem c sL2 ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) m61)
          (fun _ ⟨_, ⟨⟩⟩ m61 hm61 => by
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32])
              (fun ⟨lit, ⟨⟩⟩ m62 =>
                (lit.toNat = 2 * r.toNat ∨ lit.toNat = 2 * r.toNat + 1) ∧
                (FullMem c sL2 ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) m62)
              (fun _ ⟨lit, ⟨⟩⟩ m62 ⟨hlit_eq, hm62⟩ => by
                have hcl_L2 : sL2.core.cur_level ≤ sL2.core.cur_vars := by
                  obtain ⟨_, hwL2⟩ := hinvL2.sparse.1.witness
                  exact Nat.le_trans hwL2.cur_level_le hlenL2.core_ok.trail_end_le
                c0_hsplit
                · c0_hsteps; exact hJ46E (k, ()) m62
                    ⟨extL, sL2, hinvL2, hpermL2, hcvL2, hfuelL2, hpresL20, hm62⟩
                have hnlvl_le : sL2.core.cur_level + 1 ≤ c.max_vars := by
                  have hcv := hlenL2.core_ok.cur_vars_le
                  change ¬ c.max_vars % 2 ^ 64 < (sL2.core.cur_level + 1) % 2 ^ 64 at hc
                  rw [Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : sL2.core.cur_level + 1 < 2 ^ 64)] at hc; omega
                have hnlvl_ft : sL2.core.cur_level + 1 < sL2.core.frame_trail.length := by
                  rw [hlenL2.core_ok.frame_trail_len]; omega
                have hnlvl_fd : sL2.core.cur_level + 1 < sL2.core.frame_dec.length := by
                  rw [hlenL2.core_ok.frame_dec_len]; omega
                c0_hsteps_nogrp
                let nlvl := sL2.core.cur_level + 1
                let ft' := sL2.core.frame_trail.set nlvl (BitVec.ofNat 32 sL2.core.trail_end)
                let fd' := sL2.core.frame_dec.set nlvl lit
                let sDec : FullState := { sL2 with core := { sL2.core with
                  frame_trail := ft', frame_dec := fd', cur_level := nlvl } }
                have hlenDec : sDec.LengthsOk c :=
                  ⟨{ hlenL2.core_ok with
                    frame_trail_len := by
                      dsimp [sDec, ft']; rw [List.length_set, hlenL2.core_ok.frame_trail_len]
                    frame_dec_len := by
                      dsimp [sDec, fd']; rw [List.length_set, hlenL2.core_ok.frame_dec_len] },
                   hlenL2.scratch_ok⟩
                have hdec_probe := full_decide_preserves_fullCore
                  (unas' := sL2.core.unassigned) (unfl' := sL2.core.unflushed)
                  hinvL2.sparse.1 hlenL2.scratch_ok hlenL2.core_ok.flags_len hr_spec.1 hr_spec.2
                  hlit_eq
                have hguard_false : ¬(sDec.core.cur_vars ≤ lit.toNat / 2 ∨
                    c.max_vars ≤ sDec.core.trail_end ∨
                    sDec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                  have hcv_le2 := hlenL2.core_ok.cur_vars_le
                  rintro (h1 | h2 | h3)
                  · exact absurd (show lit.toNat / 2 = r.toNat by omega ▸ h1)
                      (Nat.not_le.mpr hr_spec.1)
                  · exact absurd h2 (Nat.not_le.mpr (Nat.lt_of_lt_of_le hdec_probe.2.2.1 hcv_le2))
                  · exact h3 hdec_probe.2.1
                have hte_bv : (BitVec.ofNat 64 sL2.core.trail_end).truncate 32 =
                    BitVec.ofNat 32 sL2.core.trail_end := by apply BitVec.eq_of_toNat_eq; simp
                have hnlvl_nat : (BitVec.ofNat 64 sL2.core.cur_level + 1#64).toNat = nlvl := by
                  dsimp [nlvl]
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                refine wp_call_of_spec _ _ (hAssign _ _ _ _ ?_)
                refine ⟨c, sDec, array64 (c.hdr - 2304) extL ⋆ R, rfl, hlenDec,
                  (by dsimp [sDec, nlvl]; omega),
                  (by simp only [sDec, nlvl, ft', fd', ← hnlvl_nat, ← hte_bv]; exact hm), ?_⟩
                split
                · rename_i h; exact False.elim (hguard_false h)
                · intro v rsn' unfl' flagsA unassA phasesA mA hflA hphA sA' hmA
                  have hdec_ok := full_decide_preserves_fullCore
                    (unas' := unassA) (unfl' := sL2.core.unflushed)
                    (scratch' := { sL2.scratch with phases := phasesA }) hinvL2.sparse.1
                    { hlenL2.scratch_ok with phases_len := hphA } hflA
                    hr_spec.1 hr_spec.2 hlit_eq
                  let sA : FullState :=
                    { core := { sL2.core with
                        unassigned := unassA, trail_end := sL2.core.trail_end + 1,
                        vals := (sL2.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 255#8,
                        flags := flagsA,
                        lvl := sL2.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
                        rsns := sL2.core.rsns.set (lit.toNat / 2) 4294967295#32,
                        trl := sL2.core.trl.set sL2.core.trail_end lit,
                        trail_pos := sL2.core.trail_pos.set (lit.toNat / 2)
                          (BitVec.ofNat 32 sL2.core.trail_end),
                        frame_trail := ft', frame_dec := fd', cur_level := nlvl },
                      scratch := { sL2.scratch with phases := phasesA } }
                  have hsA_eq : sA = sA' := by dsimp [sA, sA', sDec, v, rsn', unfl']
                  rw [← hsA_eq] at hmA
                  have hinvA : FullM6HdrInv c F0 extL sA := .mk_inv hcfg hinvL2.extOk
                    ⟨hdec_ok.1, hinvL2.sparse.2.1, hinvL2.sparse.2.2.1, hinvL2.sparse.2.2.2.1,
                      hinvL2.sparse.2.2.2.2⟩
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun _ mJ => ∃ extJ sJ, FullM6HdrInv c F0 extJ sJ ∧
                      FullArenaPermEq s.core sJ.core ∧ sJ.core.cur_vars = s.core.cur_vars ∧
                      sJ.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sJ ∧
                      (FullMem c sJ ⋆ (array64 (c.hdr - 2304) extJ ⋆ R)) mJ)
                    (fun _ ⟨⟩ mJ ⟨extJ, sJ, hinvJ, hpermJ, hcvJ, hfuelJ, hpresJ, hmJ⟩ => by
                      c0_hsteps
                      exact hJ46 (s.core.cur_vars - (k.toNat + 1)) (k + 1#64, ()) mJ hlt_n
                        ⟨extJ, sJ, by rw [hk1]; omega, by rw [hk1], hinvJ, hpermJ, hcvJ, hfuelJ,
                          hpresJ, hmJ⟩)
                    (fun J75 hJ75 => by
                      refine wp_loop_group (ts := [])
                        (fun fn _ mP => ∃ extP sP, fn = sP.core.fuel.toNat ∧
                          FullM6HdrInv c F0 extP sP ∧ FullArenaPermEq s.core sP.core ∧
                          sP.core.cur_vars = s.core.cur_vars ∧
                          sP.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sP ∧
                          (FullMem c sP ⋆ (array64 (c.hdr - 2304) extP ⋆ R)) mP) ?_ ?_
                      · intro J_prop fn ⟨⟩ mP hJ_prop
                          ⟨extP, sP, hfnP, hinvP, hpermP, hcvP, hfuelP, hpresP, hmP⟩
                        have hlenP := hinvP.sparse.lengths
                        c0_hsplit; rotate_left
                        · c0_hsteps; exact hJ75 () mP
                            ⟨extP, sP, hinvP, hpermP, hcvP, hfuelP, hpresP, hmP⟩
                        have hprop_lt : sP.core.propagated < sP.core.trail_end := by
                          have := hlenP.core_ok.trail_end_le; have := hlenP.core_ok.propagated_le
                          have := hlenP.core_ok.cur_vars_le
                          change (BitVec.ofNat 64 sP.core.propagated).toNat <
                            (BitVec.ofNat 64 sP.core.trail_end).toNat at hc
                          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
                          exact hc
                        c0_hsplit; rotate_left
                        · c0_hsteps; exact hJ75 () mP
                            ⟨extP, sP, hinvP, hpermP, hcvP, hfuelP, hpresP, hmP⟩
                        c0_hsplit; rotate_left
                        · c0_hsteps; exact hJ75 () mP
                            ⟨extP, sP, hinvP, hpermP, hcvP, hfuelP, hpresP, hmP⟩
                        c0_hsteps_nogrp
                        c0_call hPropBey
                        refine ⟨c, F0, extP, sP, R, rfl, hinvP, (fullM6HdrMem_iff ..).mpr hmP,
                          fun r extP2 sP2 mP2 hinvP2 hpermP2 hcvP2 _ _ hfuelP2 hdecP2 hpresP2
                              hmP2 => ?_⟩
                        rw [fullM6HdrMem_iff] at hmP2
                        have hpermP0 := w3_arenaPermEq_trans hpermP hpermP2
                        have hcvP0 := hcvP2.trans hcvP
                        have hfuelP0 : sP2.core.fuel.toNat ≤ s.core.fuel.toNat :=
                          Nat.le_trans hfuelP2 hfuelP
                        have hpresP0 : FullExtScratchPres s sP2 :=
                          ⟨hpresP2.1.trans hpresP.1, hpresP2.2.trans hpresP.2⟩
                        c0_hsplit
                        · c0_hsteps; exact hJ75 () mP2
                            ⟨extP2, sP2, hinvP2, hpermP0, hcvP0, hfuelP0, hpresP0, hmP2⟩
                        · have hlt_fuel : sP2.core.fuel.toNat < fn := by
                            rw [hfnP]; exact hdecP2 hc hprop_lt
                          c0_hsteps; exact hJ_prop sP2.core.fuel.toNat () mP2 hlt_fuel
                            ⟨extP2, sP2, rfl, hinvP2, hpermP0, hcvP0, hfuelP0, hpresP0, hmP2⟩
                      · intro J_prop hJ_prop; c0_hsteps
                        exact hJ_prop sA.core.fuel.toNat () mA
                          ⟨extL, sA, rfl, hinvA, hpermL2, hcvL2, hfuelL2, hpresL20, hmA⟩))
              (fun J62 hJ62 => by
                have hr29 : r.toNat < 2 ^ 29 := by omega
                c0_hsplit
                · c0_hsteps; exact hJ62
                    (((r <<< BitVec.signExtend 64 1#32).truncate 32 ||| 1#32), ()) _
                    ⟨Or.inr (w3_lit_neg_shl64 hr29), hm61⟩
                · c0_hsteps; exact hJ62 (((r <<< BitVec.signExtend 64 1#32).truncate 32), ()) _
                    ⟨Or.inl (w3_lit_pos_shl64 hr29), hm61⟩))
          (fun J61 hJ61 => by
            c0_hsplit
            · c0_hsplit
              · c0_hsteps; exact hJ61 _ _ hmL2
              · c0_hsteps; exact hJ61 _ _ hmL2
            · c0_hsteps; exact hJ61 _ _ hmL2)
      · intro J46 hJ46; c0_hsteps
        exact hJ46 s.core.cur_vars (0#64, ()) m
          ⟨ext, s, Nat.zero_le _, by simp, hinv, w3_arenaPermEq_refl _, rfl, Nat.le_refl _,
            ⟨rfl, rfl⟩, hm⟩)

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
