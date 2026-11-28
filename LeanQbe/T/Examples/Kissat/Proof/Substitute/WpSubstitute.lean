/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Src.Substitute
import LeanQbe.T.Examples.Kissat.Proof.Substitute.Helpers
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# WP Proof for `full_substitute` (`Proof.Substitute.WpSubstitute`)

Proves `full_substitute_wp` parametrically over `Γ : Env` against
`Spec.fullSubstituteM6Spec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Substitute
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
open scoped Proof.Spec.FullArenaTactics SubstArenaTactics
open Kraken.Bedrock2.Test

public section

theorem full_substitute_wp (Γ : Env)
    (hBacktrack : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hTarjan : Γ.Has "full_tarjan_scc" Spec.fullTarjanSccSpec)
    (hElimVars : Γ.Has "full_subst_elim_vars" fullSubstElimVarsM6Spec)
    (hRewriteBins : Γ.Has "full_subst_rewrite_bins" Spec.fullSubstRewriteBinsSpec)
    (hRewriteAr : Γ.Has "full_subst_rewrite_ar" Spec.fullSubstRewriteArSpec)
    (hArenaSweep : Γ.Has "full_arena_sweep" fullArenaSweepSpec)
    (hProp : Γ.Has "full_propagate" Proof.PropSearch.Spec.propagateM6Spec) :
    ∀ args m Q X, fullSubstituteM6Spec args m Q X →
      Func.wp Γ full_substitute_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext0, s0, R, rfl, hinv0, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hsp0 := hinv0.sparse
  obtain ⟨F_cur0, hw0⟩ := hsp0.exists_witness
  have hcl0 := hsp0.1.lengths.core_ok
  have hclv_lt : s0.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  unfold Func.wp full_substitute_body
  have hm_f := fullM6HdrMem_focus_full hm
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState × List (BitVec 64))
    (fun p m1 => FullM6HdrInv c F0 p.2 p.1 ∧ p.1.core.cur_level = 0 ∧
      p.1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c p.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) p.2 ⋆ R)) m1) ?_ ?_
  · rintro _ ⟨st1, ext1⟩ m1 ⟨hinv1, hl01, hfl1, hm1_f⟩
    dsimp only at hinv1 hl01 hfl1 hm1_f
    c0_hsplit
    · c0_hsteps
      exact hQ 1#64 ext1 st1 m1 hinv1 hl01 hfl1 (Or.inl rfl) (fun h => by cases h)
        (fullM6HdrMem_unfocus_full hm1_f)
    · c0_hsplit
      · c0_hsteps
        exact hQ 1#64 ext1 st1 m1 hinv1 hl01 hfl1 (Or.inl rfl) (fun h => by cases h)
          (fullM6HdrMem_unfocus_full hm1_f)
      · c0_hsteps_nogrp
        refine wp_while_break_state (α := BitVec 64 × FullState × List (BitVec 64))
          (β := BitVec 64 × FullState × List (BitVec 64))
          (fun p => (p.1, ()))
          (fun p mb => FullM6HdrInv c F0 p.2.2 p.2.1 ∧ p.2.1.core.cur_level = 0 ∧
            p.2.1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
            (FullMem c p.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) p.2.2 ⋆ R)) mb)
          (fun p => (p.1, ()))
          (fun p => 2 - p.1.toNat)
          (fun p ml => FullM6HdrInv c F0 p.2.2 p.2.1 ∧ p.2.1.core.cur_level = 0 ∧
            p.2.1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ p.1.toNat ≤ 2 ∧
            (FullMem c p.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) p.2.2 ⋆ R)) ml)
          ?_ ?_ ?_
        · rintro _ ⟨_r, stb, extb⟩ mb ⟨hinvb, hl0b, hflb, hmb_f⟩
          c0_hsteps
          exact hQ 1#64 extb stb mb hinvb hl0b hflb (Or.inl rfl) (fun h => by cases h)
            (fullM6HdrMem_unfocus_full hmb_f)
        · rintro B L ⟨round, st, ext⟩ ml hB hL ⟨hinv, hl0_st, hfl_st, hr_le, hml⟩
          dsimp only at hinv hl0_st hfl_st hr_le hml
          c0_hsplit
          · have hr_lt : round.toNat < 2 := hc
            have hr1 := bv64_add1_toNat (x := round) (by omega)
            c0_hsplit
            · c0_hsplit
              · obtain ⟨F_cur, hspw⟩ := hinv.sparse.exists_witness
                c0_hsteps; c0_hcall hTarjan
                refine ⟨c, F0, F_cur, st, _, rfl, hspw, hl0_st, hml, ?_⟩
                intro ucnt _ _ inc1 _ _ _ _ _ sstk1 _ m1 st1 hspw1 huc_le hus1 hrepr1 hm1_f
                have hinvw1 : FullM6HdrInvW c F0 F_cur ext st1 :=
                  FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk hspw1
                have hl01' : st1.core.cur_level = 0 := hl0_st
                have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl_st
                c0_hsplit
                · c0_hsteps; exact hQ 20#64 ext st1 m1 hinvw1.toInv hl01' hfl1' (Or.inr rfl)
                    (fun _ => hspw1.2.1.ext_sound.2 (hspw1.2.1.inconsistent_sound hc))
                    (fullM6HdrMem_unfocus_full hm1_f)
                · c0_hsteps; c0_hcall hElimVars
                  refine ⟨c, F0, F_cur, ext, st1, R, rfl, hinvw1, hl01', hrepr1 hc, huc_le,
                    hus1, fullM6HdrMem_unfocus_full hm1_f, ?_⟩
                  intro ok2 ext2 st2 m2 hinvw2 hl02 _ hfl2 hrepr2 hfail2 hm2
                  have hfl2' : st2.core.fuel.toNat ≤ s0.core.fuel.toNat :=
                    Nat.le_trans hfl2 hfl1'
                  have hm2_f := fullM6HdrMem_focus_full hm2
                  c0_hsplit
                  · clear hm2
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun () m_c => m_c = m2) ?_ ?_
                    · rintro _ ⟨⟩ m_c rfl
                      c0_hsteps; c0_hcall hRewriteBins
                      refine ⟨c, F0, F_cur, st2, _, rfl, hinvw2.sparseW, hl02, hrepr2, hm2_f, ?_⟩
                      intro ok3 st3 m3 hspw3 hl03 _ hfl3 hrepr3 hfail3 hm3_f
                      have hinv3 := FullM6HdrInv.mk_inv hinvw2.cfgOk hinvw2.extOk hspw3.toSparse
                      have hfl3' : st3.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        rw [hfl3]; exact hfl2'
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps
                          exact hQ 1#64 ext2 st3 m3 hinv3 hl03 hfl3' (Or.inl rfl)
                            (fun h => by cases h) (fullM6HdrMem_unfocus_full hm3_f)
                        · c0_hsteps; c0_hcall hRewriteAr
                          refine ⟨c, F0, F_cur, st3, _, rfl, hspw3, hl03, hrepr3, hm3_f, ?_⟩
                          intro ok4 st4 m4 hspw4 hl04 _ hfl4 hfail4 hm4_f
                          have hinv4 :=
                            FullM6HdrInv.mk_inv hinvw2.cfgOk hinvw2.extOk hspw4.toSparse
                          have hfl4' : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4 ▸ hfl3'
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsteps
                              exact hQ 1#64 ext2 st4 m4 hinv4 hl04 hfl4' (Or.inl rfl)
                                (fun h => by cases h) (fullM6HdrMem_unfocus_full hm4_f)
                            · c0_hsteps; c0_hcall hArenaSweep
                              refine ⟨c, F0, F_cur, st4, _, rfl, hspw4.1, hspw4.2.1,
                                hspw4.2.2.2.1, hspw4.2.2.2.2.2, fun hpos => by omega, hm4_f, ?_⟩
                              intro sr vals5 fl5 lvl5 rsns5 trl5 tp5 te5 unass5 unfl5
                                wvec5 wstk5 arena5 alen5 wlen5 wu5 fred5 ni5 nr5 nb5 oom5 sc5
                                m5 _ hlen5 _ hext5 hws25 hll5 hw5 hnd5 _ _ _ hsr2 _ hm5_f
                              let st5 : FullState :=
                                { core := { st4.core with
                                    vals := vals5, flags := fl5, lvl := lvl5, rsns := rsns5,
                                    trl := trl5, trail_pos := tp5, trail_end := te5,
                                    unassigned := unass5, unflushed := unfl5, wvec := wvec5,
                                    wstk := wstk5, arena := arena5, arena_len := alen5,
                                    wlen := wlen5, wusable := wu5, arena_garbage := 0#64,
                                    first_reducible := fred5, num_irred := ni5,
                                    num_redundant := nr5, num_binary := nb5, oom := oom5 }
                                  scratch := sc5 }
                              have hspw5 := fullSparseInvW_after_sweep hspw4 hlen5 hw5 hnd5 hll5
                                hext5 rfl rfl rfl
                              have hinv5 :=
                                FullM6HdrInv.mk_inv hinvw2.cfgOk hinvw2.extOk hspw5.toSparse
                              have hl05 : st5.core.cur_level = 0 := hl04
                              c0_hsplit
                              · c0_hsteps
                                exact hQ 20#64 ext2 st5 m5 hinv5 hl05 hfl4' (Or.inr rfl)
                                  (fun _ => (hsr2 hc).2) (fullM6HdrMem_unfocus_full hm5_f)
                              · c0_hsplit
                                · c0_hsteps
                                  exact hQ 1#64 ext2 st5 m5 hinv5 hl05 hfl4' (Or.inl rfl)
                                    (fun h => by cases h) (fullM6HdrMem_unfocus_full hm5_f)
                                · c0_hsplit
                                  · c0_hsteps
                                    exact hQ 1#64 ext2 st5 m5 hinv5 hl05 hfl4' (Or.inl rfl)
                                      (fun h => by cases h) (fullM6HdrMem_unfocus_full hm5_f)
                                  · c0_hsteps; c0_hcall hProp
                                    refine ⟨c, F0, F_cur, ext2, st5, R, rfl, hinvw2.cfgOk,
                                      hinvw2.extOk, hspw5.1, hspw5.2.1, hspw5.2.2.2.2.2,
                                      fullM6HdrMem_unfocus_full hm5_f, ?_⟩
                                    intro pr ext6 vals6 fl6 lvl6 rsns6 trl6 tp6 te6 prop6
                                      unass6 unfl6 wvec6 arena6 wstk6 wlen6 wu6 fuel6 ctype6
                                      cref6 c06 c16 oom6 sc6 m6 _ hext6 _ hlen6 hw6 _ _ hperm6
                                      hsc6 _ _ _ _ hfl6 _ _ hpr1 _ _ hm6
                                    let st6 : FullState :=
                                      { core := { st5.core with
                                          vals := vals6, flags := fl6, lvl := lvl6,
                                          rsns := rsns6, trl := trl6, trail_pos := tp6,
                                          trail_end := te6, propagated := prop6,
                                          unassigned := unass6, unflushed := unfl6, wvec := wvec6,
                                          arena := arena6, wstk := wstk6, wlen := wlen6,
                                          wusable := wu6, fuel := fuel6, confl_type := ctype6,
                                          confl_ref := cref6, confl_lit0 := c06,
                                          confl_lit1 := c16, oom := oom6 }
                                        scratch := sc6 }
                                    have hspw6 := fullSparseInvW_of_bcp hspw5 hlen6 hw6
                                      hperm6 hsc6
                                    have hinv6 := FullM6HdrInv.mk_inv hinvw2.cfgOk hext6
                                      hspw6.toSparse
                                    have hfl6' : st6.core.fuel.toNat ≤ s0.core.fuel.toNat :=
                                      Nat.le_trans hfl6 hfl4'
                                    c0_hsplit
                                    · c0_hsteps
                                      exact hQ 20#64 ext6 st6 m6 hinv6 hl05 hfl6' (Or.inr rfl)
                                        (fun _ => level0_unsat_of_conflict_okW hw6 hl05
                                          (hpr1 hc).2.2) hm6
                                    · c0_hsteps
                                      exact hL (round + 1#64, st6, ext6) m6 (by dsimp only; omega)
                                        ⟨hinv6, hl05, hfl6', by dsimp only; omega,
                                          fullM6HdrMem_focus_full hm6⟩
                          · c0_hsteps
                            exact hQ 20#64 ext2 st4 m4 hinv4 hl04 hfl4' (Or.inr rfl)
                              (fun _ => hfail4 (by
                                cases ok4 <;>
                                  first | rfl | exact absurd hc (by decide)))
                              (fullM6HdrMem_unfocus_full hm4_f)
                      · c0_hsteps
                        exact hQ 20#64 ext2 st3 m3 hinv3 hl03 hfl3' (Or.inr rfl)
                          (fun _ => hfail3 (by
                            cases ok3 <;> first | rfl | exact absurd hc (by decide)))
                          (fullM6HdrMem_unfocus_full hm3_f)
                    · intro Jc hJc
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps_nogrp
                          first
                          | exact hJc () m2 rfl
                          | exact hB (round, st2, ext2) m2 ⟨hinvw2.toInv, hl02, hfl2', hm2_f⟩
                        · c0_hsteps_nogrp
                          first
                          | exact hJc () m2 rfl
                          | exact hB (round, st2, ext2) m2 ⟨hinvw2.toInv, hl02, hfl2', hm2_f⟩
                      · c0_hsteps_nogrp; exact hJc () m2 rfl
                  · c0_hsteps
                    exact hQ 20#64 ext2 st2 m2 hinvw2.toInv hl02 hfl2' (Or.inr rfl)
                      (fun _ => hfail2 (by
                        cases ok2 <;> first | rfl | exact absurd hc (by decide))) hm2
              · c0_hsteps; exact hB (round, st, ext) ml ⟨hinv, hl0_st, hfl_st, hml⟩
            · c0_hsteps; exact hB (round, st, ext) ml ⟨hinv, hl0_st, hfl_st, hml⟩
          · c0_hsteps; exact hB (round, st, ext) ml ⟨hinv, hl0_st, hfl_st, hml⟩
        · intro B L _ hL; c0_hsteps
          exact hL (0#64, st1, ext1) m1 ⟨hinv1, hl01, hfl1, Nat.zero_le _, hm1_f⟩
  · intro Jbt hJbt; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s0, _, rfl, hsp0.1.lengths, hclv_lt, fun _ => by
        have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega,
        hw0.2.1.trail_lits_lt, hm_f, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 st1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1_f
      have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
      have hl01 : st1.core.cur_level = 0 := by dsimp only [st1]; rw [hcl1]; simp
      have hsp1 := fullSparseInvW_of_perm
        ⟨hsp0.1.lengths, hw0.2.1, hsp0.2.1, hsp0.2.2.1, hsp0.2.2.2.1, hsp0.2.2.2.2⟩
        hlen1 hw1 ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩
        rfl rfl rfl hprsc1.1
      c0_hsteps
      exact hJbt (st1, ext0) m1
        ⟨FullM6HdrInv.mk_inv hinv0.cfgOk hinv0.extOk hsp1.toSparse, hl01, Nat.le_refl _, hm1_f⟩
    · have hl00 : s0.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps; exact hJbt (s0, ext0) m ⟨hinv0, hl00, Nat.le_refl _, hm_f⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
