/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Src.Vivify
import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Vivify Count & Core Helper WP Proofs (`Proof.Vivify.WpCounts`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, zero expose attributes on theorems,
zero legacy/private-import hacks, `std3`) for:
1. `full_viv_best_implied_m6_wp` (`Spec.fullVivBestImpliedM6Spec`)
2. `full_viv_reestablish_m6_wp` (`Spec.fullVivReestablishM6Spec`)
3. `full_viv_inst_check_m6_wp` (`Spec.fullVivInstCheckM6Spec`)
4. `full_viv_sift_counts_m6_wp` (`Spec.fullVivSiftCountsM6Spec`)
5. `full_viv_sort_counts_m6_wp` (`Spec.fullVivSortCountsM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
open LeanQbe.T.Examples.Kissat.Src.Vivify
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics

private theorem bv8_sext32_sgt0_eq1 {b : BitVec 8}
    (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8)
    (hsgt : (0#32 : BitVec 32).slt (b.signExtend 32) = true) :
    b = 1#8 := by
  rcases hd with rfl | rfl | rfl
  · exfalso; revert hsgt; decide
  · rfl
  · exfalso; revert hsgt; decide

private theorem bv8_sext32_ne0_iff' (b : BitVec 8) :
    b.signExtend 32 ≠ 0#32 ↔ b ≠ 0#8 := by
  constructor
  · rintro hne rfl; exact hne (by decide)
  · intro hne heq
    apply hne; ext i hi
    have h1 := congrArg (·[i]) heq
    simpa [BitVec.getElem_signExtend, hi, show i < 32 by omega] using h1

private theorem bv64_zext32_toNat' (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem bv64_shl1_nat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt hx]

private theorem vals_ne0_lvl_le {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcv_lt : 2 * s.core.cur_vars < 2 ^ 32)
    (hw : FullWitnessInv c F0 F_cur s.core) {l : Nat}
    (hl : l < 2 * s.core.cur_vars) (hne : s.core.vals[l]?.getD 0#8 ≠ 0#8) :
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level := by
  rcases hw.vals_domain l hl with h0 | h1 | hff
  · exact absurd h0 hne
  · obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
    have hlv := hw.lvl_le i hi
    rwa [heq] at hlv
  · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hff
    have hlv := hw.lvl_le i hi
    have hlt32 : l < 2 ^ 32 := by omega
    have hdiv : (s.core.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by
      rw [heq, ← show (BitVec.ofNat 32 l ^^^ 1#32).toNat = l ^^^ 1 by
        rw [viv_bv32_xor1_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32],
        viv_bv32_xor1_div2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
    rwa [hdiv] at hlv

private theorem bv64_lshr1_nat (x : BitVec 64) :
    (x >>> 1#64).toNat = x.toNat / 2 := by
  change (x >>> 1).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

private theorem bv32_lshr1_nat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem list_swap_take_perm {α : Type} {xs : List α} {n i j : Nat}
    {vi vj : α} (hi : i < n) (hj : j < n) (hn : n ≤ xs.length)
    (hvi : xs[i]? = some vi) (hvj : xs[j]? = some vj) :
    let xs' := (xs.set i vj).set j vi
    (xs'.take n).Perm (xs.take n) := by
  intro xs'
  have hi_len : i < xs.length := Nat.lt_of_lt_of_le hi hn
  have hj_len : j < xs.length := Nat.lt_of_lt_of_le hj hn
  rw [List.getElem?_eq_getElem hi_len, Option.some.injEq] at hvi
  rw [List.getElem?_eq_getElem hj_len, Option.some.injEq] at hvj
  have htlen : (xs.take n).length = n := List.length_take_of_le hn
  have hi_t : i < (xs.take n).length := by omega
  have hj_t : j < (xs.take n).length := by omega
  have h1 : xs'.take n =
      ((xs.take n).set i ((xs.take n)[j]'hj_t)).set j ((xs.take n)[i]'hi_t) := by
    simp only [xs', List.take_set, List.getElem_take, hvi, hvj]
  rw [h1]
  exact viv_list_swap_perm (xs.take n) hi_t hj_t

private theorem list_swap_suffix_eq {α : Type} {xs : List α} {n k i j : Nat}
    {v1 v2 : α} (hi : i < n) (hj : j < n) (hk : n ≤ k) :
    ((xs.set i v1).set j v2)[k]? = xs[k]? := by
  have hki : i ≠ k := by omega
  have hkj : j ≠ k := by omega
  simp [hkj, hki]

private theorem list_swap_lt_bound {xs : List (BitVec 32)} {n i j : Nat}
    {v1 v2 : BitVec 32} (hn : n ≤ xs.length)
    (hb : ∀ k < n, (xs[k]?.getD 0#32).toNat < 2 * xs.length)
    (hv1 : v1.toNat < 2 * xs.length) (hv2 : v2.toNat < 2 * xs.length)
    {m : Nat} (hm : m < n) :
    (((xs.set i v1).set j v2)[m]?.getD 0#32).toNat < 2 * xs.length := by
  have hm_len : m < xs.length := Nat.lt_of_lt_of_le hm hn
  by_cases hmj : m = j
  · subst hmj
    rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some,
      List.getElem_set_self (by simp; omega)]
    exact hv2
  · rw [List.getElem?_set_ne (Ne.symm hmj)]
    by_cases hmi : m = i
    · subst hmi
      rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some,
        List.getElem_set_self (by simp; omega)]
      exact hv1
    · rw [List.getElem?_set_ne (Ne.symm hmi)]; exact hb m hm

theorem full_viv_best_implied_m6_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullVivBestImpliedM6Spec a m Q X →
      Func.wp Γ full_viv_best_implied_m6_body a m Q X := by
  rintro ⟨h, sz, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hsz, htmp, hm, hQ⟩
  have hcl := hsp.1.core_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hcl.cur_vars_le
  have htl := hcl.tmp_len_arr
  have hvl := hcl.vals_len
  have htpl := hcl.trail_pos_len
  unfold Func.wp full_viv_best_implied_m6_body
  viv_hsteps_nogrp
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (best, _blvl, i, ()) mL =>
      mL = m ∧ i.toNat ≤ sz.toNat ∧
      (best ≠ 0xFFFFFFFF#32 →
        best.toNat < 2 * s.core.cur_vars ∧ s.core.vals[best.toNat]?.getD 0#8 = 1#8))
    (fun (_best, _blvl, i, ()) _ => sz.toNat - i.toNat)
    (fun J hLoop => ?_)
    (fun J (best, blvl, i, ()) mL ⟨hm_eq, hi_le, hbest⟩ hLoop => ?_)
  · refine hLoop _ m ⟨rfl, Nat.zero_le _, fun hne => False.elim (hne rfl)⟩
  · subst hm_eq
    rw [Blocks.get_here]; dsimp only
    viv_hsteps_nogrp
    · have hi_lt : i.toNat < sz.toNat := by c0_bound
      have hi1_lt : i.toNat + 1 < 2 ^ 32 := by omega
      have hi_bv : (i.setWidth 64).toNat = i.toNat := bv64_zext32_toNat' i
      have hlit_lt : (s.core.tmp[i.toNat]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
        htmp i.toNat hi_lt
      have hi_len : (i.setWidth 64).toNat < s.core.tmp.length := by rw [hi_bv]; omega
      have hi_len' : i.toNat < s.core.tmp.length := by omega
      have hlit_lt' : (s.core.tmp[(i.setWidth 64).toNat]'hi_len).toNat < 2 * s.core.cur_vars := by
        have h1 := hlit_lt
        rw [List.getElem?_eq_getElem hi_len', Option.getD_some] at h1
        simpa only [hi_bv] using h1
      have hlit_max : (s.core.tmp[(i.setWidth 64).toNat]'hi_len).toNat < 2 * c.max_vars := by
        omega
      have hlit_zext : (BitVec.setWidth 64 (s.core.tmp[(i.setWidth 64).toNat]'hi_len)).toNat <
          2 * c.max_vars := by
        rw [bv64_zext32_toNat']; exact hlit_max
      have hlit_var : ((s.core.tmp[(i.setWidth 64).toNat]'hi_len) >>> (1 : Nat)).toNat <
          c.max_vars := by
        rw [bv32_lshr1_nat]; omega
      have hlit_vzext : (BitVec.setWidth 64
          ((s.core.tmp[(i.setWidth 64).toNat]'hi_len) >>> (1 : Nat))).toNat < c.max_vars := by
        rw [bv64_zext32_toNat']; exact hlit_var
      viv_hsteps_nogrp
      refine wp_join_group (ts := [i32, i32])
        (fun (best', _blvl', ()) m1 =>
          m1 = mL ∧
          (best' ≠ 0xFFFFFFFF#32 →
            best'.toNat < 2 * s.core.cur_vars ∧ s.core.vals[best'.toNat]?.getD 0#8 = 1#8))
        (fun _ (best', blvl', ()) m1 ⟨hm1, hbest'⟩ => ?_)
        (fun _ hJ1 => ?_)
      · subst m1
        rw [Blocks.get_here]; dsimp only
        viv_hsteps_nogrp
        refine hLoop (best', blvl', i + 1#32, ()) mL (by dsimp only; bv_omega)
          ⟨rfl, by bv_omega, hbest'⟩
      · viv_hsteps_nogrp
        · have hdom := hsp.2.1.vals_domain (s.core.tmp[(i.setWidth 64).toNat]'hi_len).toNat hlit_lt'
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom
          have hsgt : (0#32 : BitVec 32).slt
              ((s.core.vals[(s.core.tmp[(i.setWidth 64).toNat]'hi_len).toNat]'(by
                omega)).signExtend 32) = true := by
            simpa only [hi_bv] using hc
          have hv1_elem :
              s.core.vals[(s.core.tmp[(i.setWidth 64).toNat]'hi_len).toNat]'(by omega) = 1#8 :=
            bv8_sext32_sgt0_eq1 hdom hsgt
          have hv1 : s.core.vals[(s.core.tmp[(i.setWidth 64).toNat]'hi_len).toNat]?.getD 0#8 =
              1#8 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hv1_elem
          viv_hsteps_nogrp
          refine wp_join_group (ts := [i32, i32])
            (fun (best', _blvl', ()) m2 =>
              m2 = mL ∧
              (best' ≠ 0xFFFFFFFF#32 →
                best'.toNat < 2 * s.core.cur_vars ∧ s.core.vals[best'.toNat]?.getD 0#8 = 1#8))
            (fun _ (best', blvl', ()) m2 ⟨hm2, hbest2⟩ => by
              subst m2; rw [Blocks.get_here]; dsimp only
              viv_hsteps_nogrp; exact hJ1 (best', blvl', ()) mL ⟨rfl, hbest2⟩)
            (fun _ hJ2 => by
              viv_hsteps_nogrp <;> refine hJ2 _ mL ⟨rfl, fun hne => ?_⟩
              · exact ⟨hlit_lt', hv1⟩
              · exact ⟨hlit_lt', hv1⟩
              · exact hbest hne)
        · exact hJ1 (best, blvl, ()) mL ⟨rfl, hbest⟩
    · exact hQ best hbest

theorem full_viv_reestablish_m6_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec) :
    ∀ a m Q X, Spec.fullVivReestablishM6Spec a m Q X →
      Func.wp Γ full_viv_reestablish_m6_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, href, hm, hQ⟩
  have hcl := hsp.1.core_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hcl.cur_vars_le
  have hal_len := hcl.arena_len_arr
  have hal_le := hcl.arena_len_le
  have hvl := hcl.vals_len
  have hll := hcl.lvl_len
  have hwf := hsp.2.1.arena.refs_wf cref.toNat href
  unfold Func.wp full_viv_reestablish_m6_body
  viv_hsteps_nogrp
  · exact hQ s m hsp rfl rfl rfl rfl rfl rfl rfl hm
  · exact hQ s m hsp rfl rfl rfl rfl rfl rfl rfl hm
  · have hcr3 : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
      have := cref.isLt; bv_omega
    have hcr4 : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by
      have := cref.isLt; bv_omega
    have hng : fullArenaClauseGarb s cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h0 : s.core.arena[cref.toNat] &&& 524288#32 = 0#32 := by c0_bound
      simpa using h0
    have hsz3 : 3 ≤ fullArenaClauseSize s cref.toNat := hwf.2.1
    have hbd_ar : cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤
        s.core.arena.length := by
      unfold fullArenaClauseSize; have := hwf.2.2.1; have := hwf.2.2.2.1; omega
    have hl0_mem : (s.core.arena[cref.toNat + 3]'(by omega)).toNat ∈
        fullArenaClauseLits s cref.toNat := by
      rw [fullArenaClauseLits, mem_fullArenaClauseLitsCore_iff hbd_ar]
      exact ⟨0, by omega, rfl⟩
    have hl1_mem : (s.core.arena[cref.toNat + 4]'(by omega)).toNat ∈
        fullArenaClauseLits s cref.toNat := by
      rw [fullArenaClauseLits, mem_fullArenaClauseLitsCore_iff hbd_ar]
      exact ⟨1, by omega, rfl⟩
    have hl0_lt : (s.core.arena[cref.toNat + 3]'(by omega)).toNat < 2 * s.core.cur_vars :=
      hsp.2.1.arena.lits_lt cref.toNat href hng _ hl0_mem
    have hl1_lt : (s.core.arena[cref.toNat + 4]'(by omega)).toNat < 2 * s.core.cur_vars :=
      hsp.2.1.arena.lits_lt cref.toNat href hng _ hl1_mem
    have hl0_lt' :
        (s.core.arena[(cref.setWidth 64 + 3#64).toNat]'(by rw [hcr3]; omega)).toNat <
          2 * s.core.cur_vars := by
      simpa only [hcr3] using hl0_lt
    have hl1_lt' :
        (s.core.arena[(cref.setWidth 64 + 4#64).toNat]'(by rw [hcr4]; omega)).toNat <
          2 * s.core.cur_vars := by
      simpa only [hcr4] using hl1_lt
    have hl0v_lt :
        (s.core.arena[(cref.setWidth 64 + 3#64).toNat]'(by rw [hcr3]; omega)).toNat / 2 <
          c.max_vars := by omega
    have hl1v_lt :
        (s.core.arena[(cref.setWidth 64 + 4#64).toNat]'(by rw [hcr4]; omega)).toNat / 2 <
          c.max_vars := by omega
    viv_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun (p0, ()) m1 => m1 = m ∧ p0.toNat ≤ s.core.cur_level)
      (fun _ (p0, ()) m1 ⟨hm1, hp0_le⟩ => ?_)
      (fun _ hJ1 => ?_)
    · subst m1
      rw [Blocks.get_here]; dsimp only
      refine wp_join_group (ts := [i64])
        (fun (p1, ()) m2 => m2 = m ∧ p1.toNat ≤ s.core.cur_level)
        (fun _ (p1, ()) m2 ⟨hm2, hp1_le⟩ => ?_)
        (fun _ hJ2 => ?_)
      · subst m2
        rw [Blocks.get_here]; dsimp only
        refine wp_join_group (ts := [i64])
          (fun (p2, ()) m3 => m3 = m ∧ p2.toNat ≤ s.core.cur_level)
          (fun _ (p2, ()) m3 ⟨hm3, hp2_le⟩ => ?_)
          (fun _ hJ3 => ?_)
        · subst m3
          rw [Blocks.get_here]; dsimp only
          refine wp_join_group (ts := [])
            (fun () m4 =>
              ∃ s' : FullState,
                FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_vars = s.core.cur_vars ∧
                s'.core.arena = s.core.arena ∧ s'.core.arena_len = s.core.arena_len ∧
                s'.core.probing = s.core.probing ∧ s'.core.fuel = s.core.fuel ∧
                s'.scratch.red_refs = s.scratch.red_refs ∧
                s'.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
                (FullMem c s' ⋆ R) m4)
            (fun _ () m4 ⟨s', hsp', h1, h2, h3, h4, h5, h6, h7, hm4⟩ => by
              rw [Blocks.get_here]
              viv_hsteps_nogrp
              exact hQ s' m4 hsp' h1 h2 h3 h4 h5 h6 h7 hm4)
            (fun _ hJ4 => ?_)
          viv_hsteps_nogrp
          · have hp2_pos : 0 < p2.toNat := by c0_bound
            have hp2_sub : (p2 - 1#64).toNat = p2.toNat - 1 := by
              rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]
              have := p2.isLt
              rw [show (2 ^ 64 - 1 + p2.toNat) % 2 ^ 64 = p2.toNat - 1 by omega]
            have hlt_lvl : (p2 - 1#64).toNat < s.core.cur_level := by rw [hp2_sub]; omega
            have hcl_max : s.core.cur_level ≤ c.max_vars := by
              have := hsp.2.1.cur_level_le; have := hcl.trail_end_le; omega
            have hcl_lt : s.core.cur_level < 2 ^ 64 := by omega
            have hbt_tle : (p2 - (1 : BitVec 64)).toNat ≤ s.core.cur_level := by
              change (p2 - 1#64).toNat ≤ s.core.cur_level; omega
            viv_call hBt
            refine ⟨c, s, R, rfl, hsp.1, hcl_lt,
              fun _ => by change (p2 - 1#64).toNat < c.max_vars; omega,
              hsp.2.1.trail_lits_lt, hm,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
                hlen' _hte' _hprop' _hcl' hpres' hsc' _htrl' _hinv_eq' hw' _hotfs' hm' => ?_⟩
            let s' : FullState :=
              { core :=
                  { s.core with
                    unassigned := unass', vals := vals', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                    cur_level := cl' },
                scratch := sc' }
            have hsp' : FullSparseInvW c F0 F_cur s' :=
              viv_sparseW_of_backtrack hsp hbt_tle hlen' hpres' (hw' F0 F_cur hsp.2.1 hbt_tle)
            obtain ⟨ta', ba', pt', pb', hp', ps', hl', qsi', qss', hsc_eq⟩ := hsc'
            exact hJ4 () m' ⟨s', hsp', rfl, rfl, rfl, rfl, rfl,
              by simp [s', hsc_eq], by simp [s', hsc_eq], hm'⟩
          · exact hJ4 () m ⟨s, hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩
          · exact hJ4 () m ⟨s, hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩
        · viv_hsteps_nogrp
          · refine wp_join_group (ts := [i64])
              (fun (p, ()) m4 => m4 = m ∧ p.toNat ≤ s.core.cur_level)
              (fun _ (p, ()) m4 ⟨hm4, hp_le⟩ => ?_)
              (fun _ hJ4 => ?_)
            · subst m4; rw [Blocks.get_here]; dsimp only
              viv_hsteps_nogrp; exact hJ3 (p, ()) m ⟨rfl, hp_le⟩
            · viv_hsteps_nogrp
              · refine wp_join_group (ts := [i64])
                  (fun (p, ()) m5 => m5 = m ∧ p.toNat ≤ s.core.cur_level)
                  (fun _ (p, ()) m5 ⟨hm5, hp_le⟩ => ?_)
                  (fun _ hJ5 => ?_)
                · subst m5; rw [Blocks.get_here]; dsimp only
                  viv_hsteps_nogrp; exact hJ4 (p, ()) m ⟨rfl, hp_le⟩
                · viv_hsteps_nogrp
                  · exact hJ5 (p0, ()) m ⟨rfl, hp0_le⟩
                  · exact hJ5 (p1, ()) m ⟨rfl, hp1_le⟩
              · refine wp_join_group (ts := [i64])
                  (fun (p, ()) m5 => m5 = m ∧ p.toNat ≤ s.core.cur_level)
                  (fun _ (p, ()) m5 ⟨hm5, hp_le⟩ => ?_)
                  (fun _ hJ5 => ?_)
                · subst m5; rw [Blocks.get_here]; dsimp only
                  viv_hsteps_nogrp; exact hJ4 (p, ()) m ⟨rfl, hp_le⟩
                · viv_hsteps_nogrp
                  · exact hJ5 (p0, ()) m ⟨rfl, hp0_le⟩
                  · refine wp_join_group (ts := [i64])
                      (fun (p, ()) m6 => m6 = m ∧ p.toNat ≤ s.core.cur_level)
                      (fun _ (p, ()) m6 ⟨hm6, hp_le⟩ => ?_)
                      (fun _ hJ6 => ?_)
                    · subst m6; rw [Blocks.get_here]; dsimp only
                      viv_hsteps_nogrp; exact hJ5 (p, ()) m ⟨rfl, hp_le⟩
                    · viv_hsteps_nogrp
                      · exact hJ6 (p0, ()) m ⟨rfl, hp0_le⟩
                      · exact hJ6 (0#64, ()) m ⟨rfl, by simp only [BitVec.toNat_ofNat]; omega⟩
          · refine wp_join_group (ts := [i64])
              (fun (p, ()) m4 => m4 = m ∧ p.toNat ≤ s.core.cur_level)
              (fun _ (p, ()) m4 ⟨hm4, hp_le⟩ => ?_)
              (fun _ hJ4 => ?_)
            · subst m4; rw [Blocks.get_here]; dsimp only
              viv_hsteps_nogrp; exact hJ3 (p, ()) m ⟨rfl, hp_le⟩
            · viv_hsteps_nogrp
              · refine wp_join_group (ts := [i64])
                  (fun (p, ()) m5 => m5 = m ∧ p.toNat ≤ s.core.cur_level)
                  (fun _ (p, ()) m5 ⟨hm5, hp_le⟩ => ?_)
                  (fun _ hJ5 => ?_)
                · subst m5; rw [Blocks.get_here]; dsimp only
                  viv_hsteps_nogrp; exact hJ4 (p, ()) m ⟨rfl, hp_le⟩
                · viv_hsteps_nogrp
                  · exact hJ5 (p1, ()) m ⟨rfl, hp1_le⟩
                  · refine wp_join_group (ts := [i64])
                      (fun (p, ()) m6 => m6 = m ∧ p.toNat ≤ s.core.cur_level)
                      (fun _ (p, ()) m6 ⟨hm6, hp_le⟩ => ?_)
                      (fun _ hJ6 => ?_)
                    · subst m6; rw [Blocks.get_here]; dsimp only
                      viv_hsteps_nogrp; exact hJ5 (p, ()) m ⟨rfl, hp_le⟩
                    · viv_hsteps_nogrp
                      · exact hJ6 (p1, ()) m ⟨rfl, hp1_le⟩
                      · exact hJ6 (0#64, ()) m ⟨rfl, by simp only [BitVec.toNat_ofNat]; omega⟩
              · exact hJ4 (0#64, ()) m ⟨rfl, by simp only [BitVec.toNat_ofNat]; omega⟩
      · viv_hsteps_nogrp
        · have hne1 : s.core.vals[
              (s.core.arena[(cref.setWidth 64 + 4#64).toNat]'(by rw [hcr4]; omega)).toNat]?.getD
                0#8 ≠ 0#8 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have h4_eq : (cref.toNat + BitVec.toNat (4 : BitVec 64)) % 2 ^ 64 =
                (cref.setWidth 64 + 4#64).toNat := by
              rw [hcr4, show BitVec.toNat (4 : BitVec 64) = 4 from rfl]; omega
            have hc1 : BitVec.signExtend 32
                s.core.vals[s.core.arena[(cref.setWidth 64 + 4#64).toNat].toNat] ≠ 0#32 := by
              simp only [← h4_eq]; exact hc
            exact (bv8_sext32_ne0_iff' _).mp hc1
          have hl1_lv := vals_ne0_lvl_le (by omega) hsp.2.1 hl1_lt' hne1
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hl1_lv
          exact hJ2 _ m ⟨rfl, by
            simpa only [bv64_zext32_toNat', bv32_lshr1_nat, hcr4,
              show (4 : BitVec 64) = 4#64 from rfl] using hl1_lv⟩
        · exact hJ2 (0#64, ()) m ⟨rfl, by simp only [BitVec.toNat_ofNat]; omega⟩
    · viv_hsteps_nogrp
      · have hne0 : s.core.vals[
            (s.core.arena[(cref.setWidth 64 + 3#64).toNat]'(by rw [hcr3]; omega)).toNat]?.getD
              0#8 ≠ 0#8 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have h3_eq : (cref.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
              (cref.setWidth 64 + 3#64).toNat := by
            rw [hcr3, show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
          have hc0 : BitVec.signExtend 32
              s.core.vals[s.core.arena[(cref.setWidth 64 + 3#64).toNat].toNat] ≠ 0#32 := by
            simp only [← h3_eq]; exact hc
          exact (bv8_sext32_ne0_iff' _).mp hc0
        have hl0_lv := vals_ne0_lvl_le (by omega) hsp.2.1 hl0_lt' hne0
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hl0_lv
        exact hJ1 _ m ⟨rfl, by
          simpa only [bv64_zext32_toNat', bv32_lshr1_nat, hcr3,
            show (3 : BitVec 64) = 3#64 from rfl] using hl0_lv⟩
      · exact hJ1 (0#64, ()) m ⟨rfl, by simp only [BitVec.toNat_ofNat]; omega⟩

theorem full_viv_inst_check_m6_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullVivInstCheckM6Spec a m Q X →
      Func.wp Γ full_viv_inst_check_m6_body a m Q X := by
  rintro ⟨h, sz, iolen, not_lit, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp, hsz1, hsz_le, hio_le, htmp, hws2, hm, hQ⟩
  have hcl := hsp.1.core_ok
  have hsc := hsp.1.scratch_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hcl.cur_vars_le
  have htl := hcl.tmp_len_arr
  have hml := hcl.lit_mark_len
  have hws2l := hsc.work_stk2_len
  let markedPred (lm : List (BitVec 8)) (j : Nat) : Prop :=
    lm.length = 2 * c.max_vars ∧
    (∀ k < j, lm[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8) ∧
    (∀ l < 2 * c.max_vars,
      (∃ k < j, l = (s.core.tmp[k]?.getD 0#32).toNat) ∨ lm[l]? = s.core.lit_mark[l]?)
  unfold Func.wp full_viv_inst_check_m6_body
  viv_hsteps_nogrp
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) mL =>
      i.toNat + 1 ≤ sz.toNat ∧
      ∃ lm : List (BitVec 8), markedPred lm i.toNat ∧
        (FullMem c { s with core := { s.core with lit_mark := lm } } ⋆ R) mL)
    (fun (i, ()) _ => sz.toNat - 1 - i.toNat)
    (fun J hLoop => hLoop (0#32, ()) m ⟨by simp only [BitVec.toNat_ofNat]; omega, s.core.lit_mark,
      ⟨hml, fun _ hk => by simp only [BitVec.toNat_ofNat] at hk; omega, fun _ _ => Or.inr rfl⟩,
      hm⟩)
    (fun J (i, ()) mL ⟨hi_le, lm, hlm, hmL⟩ hLoop => ?_)
  · rw [Blocks.get_here]; dsimp only
    viv_hsteps_nogrp
    · have hi1_lt : i.toNat + 1 < sz.toNat := by c0_bound
      have hi_lt : i.toNat < sz.toNat := by omega
      have hi_bv : (i.setWidth 64).toNat = i.toNat := bv64_zext32_toNat' i
      have hlit_lt : (s.core.tmp[i.toNat]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
        htmp i.toNat hi_lt
      have hi_len : (i.setWidth 64).toNat < s.core.tmp.length := by rw [hi_bv]; omega
      let lit := s.core.tmp[(i.setWidth 64).toNat]'hi_len
      have hlit_eq : lit = s.core.tmp[i.toNat]?.getD 0#32 := by
        simp only [lit, hi_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hlit_lt' : lit.toNat < 2 * s.core.cur_vars :=
        (congrArg BitVec.toNat hlit_eq) ▸ hlit_lt
      have hlit_max : lit.toNat < 2 * c.max_vars := by omega
      have hlm_len : lm.length = 2 * c.max_vars := hlm.1
      have hlit_zext : (BitVec.setWidth 64 (s.core.tmp[(i.setWidth 64).toNat]'hi_len)).toNat <
          lm.length := by
        rw [bv64_zext32_toNat']; exact Nat.lt_of_lt_of_eq hlit_max hlm_len.symm
      viv_hsteps_nogrp
      let lm' := lm.set lit.toNat 1#8
      have hlm'_len : lm'.length = 2 * c.max_vars := by simp [lm', hlm_len]
      have hlm_set_len : lit.toNat < (lm.set lit.toNat 1#8).length := by
        simp only [List.length_set, hlm_len]; exact hlit_max
      have hmk' : markedPred lm' (i.toNat + 1) := by
        refine ⟨hlm'_len, fun k hk => ?_, fun l hl => ?_⟩
        · by_cases hki : k = i.toNat
          · subst hki
            rw [← hlit_eq, List.getElem?_eq_getElem (by rw [hlm'_len]; exact hlit_max),
              Option.getD_some, List.getElem_set_self hlm_set_len]
          · have hlt_i : k < i.toNat := by omega
            have hprev := hlm.2.1 k hlt_i
            by_cases hsame : (s.core.tmp[k]?.getD 0#32).toNat = lit.toNat
            · rw [hsame, List.getElem?_eq_getElem (by rw [hlm'_len]; exact hlit_max),
                Option.getD_some, List.getElem_set_self hlm_set_len]
            · rw [List.getElem?_set_ne (Ne.symm hsame)]; exact hprev
        · by_cases hli : l = lit.toNat
          · exact Or.inl ⟨i.toNat, by omega, hli.trans (congrArg BitVec.toNat hlit_eq)⟩
          · rw [List.getElem?_set_ne (Ne.symm hli)]
            rcases hlm.2.2 l hl with ⟨k, hk, heq⟩ | hsame
            · exact Or.inl ⟨k, by omega, heq⟩
            · exact Or.inr hsame
      have hi1_bv : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      refine hLoop (i + 1#32, ()) _ (by dsimp only; bv_omega) ⟨by bv_omega, lm', ?_, ?_⟩
      · rw [hi1_bv]; exact hmk'
      · simpa only [lm', lit, bv64_zext32_toNat', hi_bv] using hm
    · have hi_eq : i.toNat = sz.toNat - 1 := by c0_bound
      have hlm_sz : markedPred lm (sz.toNat - 1) := hi_eq ▸ hlm
      refine wp_join_group (ts := [Ty.bool, i32])
        (fun (ok, _j, ()) m1 =>
          ∃ lm1 : List (BitVec 8),
            lm1.length = 2 * c.max_vars ∧
            (∀ l < 2 * c.max_vars,
              (∃ k, k + 1 < sz.toNat ∧ l = (s.core.tmp[k]?.getD 0#32).toNat) ∨
                lm1[l]? = s.core.lit_mark[l]?) ∧
            (ok = true → ∀ idx < iolen.toNat,
              s.scratch.work_stk2[idx]?.getD 0#32 = not_lit ∨
              ∃ k, k + 1 < sz.toNat ∧
                s.scratch.work_stk2[idx]?.getD 0#32 = s.core.tmp[k]?.getD 0#32) ∧
            (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) m1)
        (fun _ (ok, _j, ()) m1 ⟨lm1, hlm1_len, hlm1_pres, hok_post, hm1⟩ => ?_)
        (fun _ hJ1 => ?_)
      · rw [Blocks.get_here]; dsimp only
        viv_hsteps_nogrp
        refine wp_loop_inv (ts := [i32])
          (fun (k, ()) mC =>
            k.toNat + 1 ≤ sz.toNat ∧
            ∃ lmC : List (BitVec 8), lmC.length = 2 * c.max_vars ∧
              (∀ j < k.toNat, lmC[(s.core.tmp[j]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
              (∀ l < 2 * c.max_vars,
                (∃ j, k.toNat ≤ j ∧ j + 1 < sz.toNat ∧
                  l = (s.core.tmp[j]?.getD 0#32).toNat) ∨
                (∃ j, j + 1 < sz.toNat ∧ l = (s.core.tmp[j]?.getD 0#32).toNat ∧
                  lmC[l]? = some 0#8) ∨
                lmC[l]? = s.core.lit_mark[l]?) ∧
              (FullMem c { s with core := { s.core with lit_mark := lmC } } ⋆ R) mC)
          (fun (k, ()) _ => sz.toNat - 1 - k.toNat)
          (fun J2 hLoop2 => hLoop2 (0#32, ()) m1
            ⟨by simp only [BitVec.toNat_ofNat]; omega, lm1, hlm1_len,
              fun _ hj => by simp only [BitVec.toNat_ofNat] at hj; omega,
              fun l hl => by
                rcases hlm1_pres l hl with ⟨k, hk, heq⟩ | hsame
                · exact Or.inl ⟨k, Nat.zero_le _, hk, heq⟩
                · exact Or.inr (Or.inr hsame),
              hm1⟩)
          (fun J2 (k, ()) mC ⟨hk_le, lmC, hlmC_len, hzero, hpresC, hmC⟩ hLoop2 => ?_)
        · rw [Blocks.get_here]; dsimp only
          viv_hsteps_nogrp
          · have hk1_lt : k.toNat + 1 < sz.toNat := by c0_bound
            have hk_bv : (k.setWidth 64).toNat = k.toNat := bv64_zext32_toNat' k
            have hlit_lt : (s.core.tmp[k.toNat]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
              htmp k.toNat (by omega)
            have hk_len : (k.setWidth 64).toNat < s.core.tmp.length := by rw [hk_bv]; omega
            let lit := s.core.tmp[(k.setWidth 64).toNat]'hk_len
            have hlit_eq : lit = s.core.tmp[k.toNat]?.getD 0#32 := by
              simp only [lit, hk_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hlit_lt' : lit.toNat < 2 * s.core.cur_vars :=
              (congrArg BitVec.toNat hlit_eq) ▸ hlit_lt
            have hlit_max : lit.toNat < 2 * c.max_vars := by omega
            have hlmC_len' : lmC.length = 2 * c.max_vars := hlmC_len
            have hlit_zext :
                (BitVec.setWidth 64 (s.core.tmp[(k.setWidth 64).toNat]'hk_len)).toNat <
                  lmC.length := by
              rw [bv64_zext32_toNat']; exact Nat.lt_of_lt_of_eq hlit_max hlmC_len.symm
            viv_hsteps_nogrp
            let lmC' := lmC.set lit.toNat 0#8
            have hlmC'_len : lmC'.length = 2 * c.max_vars := by simp [lmC', hlmC_len]
            have hlmC_set_len : lit.toNat < (lmC.set lit.toNat 0#8).length := by
              simp only [List.length_set, hlmC_len]; exact hlit_max
            have hk1_bv : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
            refine hLoop2 (k + 1#32, ()) _ (by dsimp only; bv_omega)
              ⟨by bv_omega, lmC', hlmC'_len, fun j hj => ?_, fun l hl => ?_, ?_⟩
            · have hj' : j < k.toNat + 1 := hk1_bv ▸ hj
              by_cases hjk : j = k.toNat
              · subst hjk
                rw [← hlit_eq, List.getElem?_eq_getElem (by rw [hlmC'_len]; exact hlit_max),
                  Option.getD_some, List.getElem_set_self hlmC_set_len]
              · have hj_old := hzero j (by omega)
                by_cases hsame : (s.core.tmp[j]?.getD 0#32).toNat = lit.toNat
                · rw [hsame, List.getElem?_eq_getElem (by rw [hlmC'_len]; exact hlit_max),
                    Option.getD_some, List.getElem_set_self hlmC_set_len]
                · rw [List.getElem?_set_ne (Ne.symm hsame)]; exact hj_old
            · rw [hk1_bv]
              by_cases hlk : l = lit.toNat
              · by_cases hex : ∃ j, k.toNat + 1 ≤ j ∧ j + 1 < sz.toNat ∧
                    l = (s.core.tmp[j]?.getD 0#32).toNat
                · exact Or.inl hex
                · refine Or.inr (Or.inl ⟨k.toNat, hk1_lt,
                    hlk.trans (congrArg BitVec.toNat hlit_eq), ?_⟩)
                  rw [hlk, List.getElem?_eq_getElem (by rw [hlmC'_len]; exact hlit_max),
                    List.getElem_set_self hlmC_set_len]
              · rw [List.getElem?_set_ne (Ne.symm hlk)]
                rcases hpresC l hl with ⟨j, hge, hj, heq⟩ | h0 | hsame
                · exact Or.inl ⟨j, by
                    have hne : j ≠ k.toNat := by
                      intro hjeq; subst hjeq
                      exact hlk (heq.trans (congrArg BitVec.toNat hlit_eq).symm)
                    omega, hj, heq⟩
                · exact Or.inr (Or.inl h0)
                · exact Or.inr (Or.inr hsame)
            · simpa only [lmC', lit, bv64_zext32_toNat', hk_bv] using hm
          · have hk_eq : k.toNat + 1 = sz.toNat := by c0_bound
            let s' : FullState := { s with core := { s.core with lit_mark := lmC } }
            have hclr' : FullLitMarksClear c s' := by
              refine ⟨hsp.2.2.1.1, fun l hl => ?_⟩
              rcases hpresC l (by omega) with ⟨j, hjge, hjlt, _⟩ | ⟨j, _, _, hl0⟩ | hsame
              · omega
              · rw [hl0]; rfl
              · rw [hsame]; exact hsp.2.2.1.2 l hl
            have hlen' : FullState.LengthsOk c s' :=
              ⟨{ hcl with lit_mark_len := hlmC_len }, hsc⟩
            have hsp' : FullSparseInvW c F0 F_cur s' :=
              ⟨hlen',
                { hsp.2.1 with
                  arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok },
                  watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
                hclr', hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
            exact hQ ok lmC mC hsp' hok_post hmC
      · refine wp_loop_inv (ts := [i32])
          (fun (j, ()) m2 =>
            m2 = mL ∧ j.toNat ≤ iolen.toNat ∧
            ∀ idx < j.toNat,
              s.scratch.work_stk2[idx]?.getD 0#32 = not_lit ∨
              ∃ k, k + 1 < sz.toNat ∧
                s.scratch.work_stk2[idx]?.getD 0#32 = s.core.tmp[k]?.getD 0#32)
          (fun (j, ()) _ => iolen.toNat - j.toNat)
          (fun J2 hLoop2 => hLoop2 (0#32, ()) mL
            ⟨rfl, Nat.zero_le _, fun _ h => by simp only [BitVec.toNat_ofNat] at h; omega⟩)
          (fun J2 (j, ()) m2 ⟨hm2, hj_le, hpre⟩ hLoop2 => ?_)
        · subst m2
          rw [Blocks.get_here]; dsimp only
          viv_hsteps_nogrp
          · have hj_lt : j.toNat < iolen.toNat := by c0_bound
            have hj_bv : (j.setWidth 64).toNat = j.toNat := bv64_zext32_toNat' j
            have hws_lt : (s.scratch.work_stk2[j.toNat]?.getD 0#32).toNat <
                2 * s.core.cur_vars := hws2 j.toNat hj_lt
            have hj_len : (j.setWidth 64).toNat < s.scratch.work_stk2.length := by
              rw [hj_bv]; omega
            let wl := s.scratch.work_stk2[(j.setWidth 64).toNat]'hj_len
            have hwl_eq : wl = s.scratch.work_stk2[j.toNat]?.getD 0#32 := by
              simp only [wl, hj_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hwl_lt' : wl.toNat < 2 * s.core.cur_vars :=
              (congrArg BitVec.toNat hwl_eq) ▸ hws_lt
            have hwl_max : wl.toNat < 2 * c.max_vars := by omega
            have hwl_zext :
                (BitVec.setWidth 64 (s.scratch.work_stk2[(j.setWidth 64).toNat]'hj_len)).toNat <
                  lm.length := by
              rw [bv64_zext32_toNat']
              exact Nat.lt_of_lt_of_eq hwl_max hlm_sz.1.symm
            viv_hsteps_nogrp
            refine wp_join_group (ts := [])
              (fun () m3 => m3 = mL ∧
                (wl = not_lit ∨
                  ∃ k, k + 1 < sz.toNat ∧ wl = s.core.tmp[k]?.getD 0#32))
              (fun _ () m3 ⟨hm3, hwl_ok⟩ => ?_)
              (fun _ hJ3 => ?_)
            · subst m3
              rw [Blocks.get_here]
              viv_hsteps_nogrp
              have hj1_bv : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
              refine hLoop2 (j + 1#32, ()) mL (by dsimp only; bv_omega)
                ⟨rfl, by bv_omega, fun idx hidx => ?_⟩
              have hidx' : idx < j.toNat + 1 := hj1_bv ▸ hidx
              by_cases hidx_j : idx = j.toNat
              · subst hidx_j; simpa [← hwl_eq] using hwl_ok
              · exact hpre idx (by omega)
            · viv_hsteps_nogrp
              · exact hJ1 (false, j, ()) mL ⟨lm, hlm_sz.1, fun l hl => by
                  rcases hlm_sz.2.2 l hl with ⟨k, hk, heq⟩ | hsame
                  · exact Or.inl ⟨k, by omega, heq⟩
                  · exact Or.inr hsame,
                  fun hfalse => Bool.noConfusion hfalse, hmL⟩
              · have hlm_len : lm.length = 2 * c.max_vars := hlm_sz.1
                have hmk_ne0 : lm[wl.toNat]?.getD 0#8 ≠ 0#8 := by
                  have hc' : (lm[wl.toNat]'(by omega)).setWidth 32 ≠ 0#32 := by
                    simpa only [wl, bv64_zext32_toNat'] using hc
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  exact fun h0 => hc' ((bv8_zext32_eq0_iff _).mpr h0)
                have hex_k : ∃ k, k + 1 < sz.toNat ∧ wl = s.core.tmp[k]?.getD 0#32 := by
                  rcases hlm_sz.2.2 wl.toNat hwl_max with ⟨k, hk, heq⟩ | hsame
                  · refine ⟨k, by omega, ?_⟩
                    apply BitVec.eq_of_toNat_eq; exact heq
                  · exfalso; apply hmk_ne0
                    rw [hsame]
                    exact hsp.2.2.1.2 wl.toNat (by omega)
                exact hJ3 () mL ⟨rfl, Or.inr hex_k⟩
              · exact hJ3 () mL ⟨rfl, Or.inl (by
                  rw [hwl_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hc)⟩
          · have hj_eq : j.toNat = iolen.toNat := by c0_bound
            rw [hj_eq] at hpre
            exact hJ1 (true, j, ()) mL ⟨lm, hlm_sz.1, fun l hl => by
              rcases hlm_sz.2.2 l hl with ⟨k, hk, heq⟩ | hsame
              · exact Or.inl ⟨k, by omega, heq⟩
              · exact Or.inr hsame,
              fun _ => hpre, hmL⟩

theorem full_viv_sift_counts_m6_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullVivSiftCountsM6Spec a m Q X →
      Func.wp Γ full_viv_sift_counts_m6_body a m Q X := by
  rintro ⟨h, start, n, ⟨⟩⟩ m Q X ⟨c, s, R, sz, rfl, hlen, hn_le, hsz_le, hst_lt, htmp, hm, hQ⟩
  have hcl := hlen.core_ok
  have hsc := hlen.scratch_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have htl := hcl.tmp_len_arr
  have htr_len := hsc.tarjan_reach_len
  unfold Func.wp full_viv_sift_counts_m6_body
  viv_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) mL =>
      i.toNat < n.toNat ∧
      ∃ tmpL : List (BitVec 32), tmpL.length = c.max_vars ∧
        (tmpL.take sz).Perm (s.core.tmp.take sz) ∧
        (∀ k, sz ≤ k → k < c.max_vars → tmpL[k]? = s.core.tmp[k]?) ∧
        (∀ k < sz, (tmpL[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
        (FullMem c { s with core := { s.core with tmp := tmpL } } ⋆ R) mL)
    (fun (i, ()) _ => n.toNat - i.toNat)
    (fun J hLoop => hLoop (start, ()) m ⟨hst_lt, s.core.tmp, htl, List.Perm.refl _,
      fun _ _ _ => rfl, htmp, hm⟩)
    (fun J (i, ()) mL ⟨hi_lt, tmpL, htmpL_len, hperm, htail, hbd, hmL⟩ hLoop => ?_)
  · rw [Blocks.get_here]; dsimp only
    have hi_le_mv : i.toNat ≤ c.max_vars := by omega
    have h2i_lt64 : 2 * i.toNat + 2 < 2 ^ 64 := by omega
    have hshl1 : (i <<< (1 : Nat)).toNat = 2 * i.toNat := bv64_shl1_nat (by omega)
    have h2i1_bv : (i <<< (1 : Nat) + (1 : BitVec 64)).toNat = 2 * i.toNat + 1 := by
      rw [BitVec.toNat_add, hshl1, show ((1 : BitVec 64)).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    viv_hsteps_nogrp
    · have hch0_lt : 2 * i.toNat + 1 < n.toNat := by c0_bound
      have hch0_sz : 2 * i.toNat + 1 < sz := by omega
      have hi_sz : i.toNat < sz := by omega
      have hl0_lt : (tmpL[2 * i.toNat + 1]?.getD 0#32).toNat < 2 * c.max_vars :=
        hbd (2 * i.toNat + 1) hch0_sz
      have h2i1_len : (i <<< (1 : Nat) + (1 : BitVec 64)).toNat < tmpL.length := by
        rw [h2i1_bv]; omega
      have hget0 : tmpL[(i <<< (1 : Nat) + (1 : BitVec 64)).toNat]'h2i1_len =
          tmpL[2 * i.toNat + 1]?.getD 0#32 := by
        simp only [h2i1_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hl0_lt' : (tmpL[(i <<< (1 : Nat) + (1 : BitVec 64)).toNat]'h2i1_len).toNat <
          2 * c.max_vars := by
        rw [hget0]; exact hl0_lt
      have hl0_zext : (BitVec.setWidth 64
          (tmpL[(i <<< (1 : Nat) + (1 : BitVec 64)).toNat]'h2i1_len)).toNat < 2 * c.max_vars := by
        rw [bv64_zext32_toNat']; exact hl0_lt'
      have hl0_tr :
          (BitVec.setWidth 64 ({ s with core := { s.core with tmp := tmpL } }.core.tmp[(i <<<
            (1 : Nat) + (1 : BitVec 64)).toNat]'(by dsimp only; exact h2i1_len))).toNat <
            { s with core := { s.core with tmp := tmpL } }.scratch.tarjan_reach.length := by
        dsimp only; rw [htr_len]; exact hl0_zext
      viv_hsteps_nogrp
      refine wp_join_group (ts := [i64, i32, i32])
        (fun (cIdx, cLit, _cCnt, ()) m1 =>
          m1 = mL ∧ i.toNat < cIdx.toNat ∧ cIdx.toNat < n.toNat ∧
          cLit = tmpL[cIdx.toNat]?.getD 0#32)
        (fun _ (cIdx, cLit, cCnt, ()) m1 ⟨hm1, hi_c, hc_lt, hcLit⟩ => ?_)
        (fun _ hJ1 => ?_)
      · subst m1
        rw [Blocks.get_here]; dsimp only
        have hc_sz : cIdx.toNat < sz := by omega
        have hi_len : i.toNat < tmpL.length := by omega
        have hl_i_lt : (tmpL[i.toNat]?.getD 0#32).toNat < 2 * c.max_vars := hbd i.toNat hi_sz
        have hl_i_lt' : (tmpL[i.toNat]'hi_len).toNat < 2 * c.max_vars := by
          simpa [List.getElem?_eq_getElem (by omega)] using hl_i_lt
        have hl_i_zext : (BitVec.setWidth 64 (tmpL[i.toNat]'hi_len)).toNat <
            2 * c.max_vars := by
          rw [bv64_zext32_toNat']; exact hl_i_lt'
        have hl_c_lt : (tmpL[cIdx.toNat]?.getD 0#32).toNat < 2 * c.max_vars :=
          hbd cIdx.toNat hc_sz
        have hl_i_tr :
            (BitVec.setWidth 64 ({ s with core := { s.core with tmp := tmpL } }.core.tmp[
              i.toNat]'hi_len)).toNat <
              { s with core := { s.core with tmp := tmpL } }.scratch.tarjan_reach.length := by
          dsimp only; rw [htr_len]; exact hl_i_zext
        viv_hsteps_nogrp
        refine wp_join_group (ts := []) (fun () m2 => m2 = mL)
          (fun _ () m2 hm2 => ?_)
          (fun _ hJ2 => ?_)
        · subst m2
          rw [Blocks.get_here]; dsimp only
          let vi := tmpL[i.toNat]'hi_len
          let vc := tmpL[cIdx.toNat]'(by omega)
          let tmpL' := (tmpL.set i.toNat vc).set cIdx.toNat vi
          have hvc_cLit : vc = cLit := by
            rw [hcLit]; simp only [vc]
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hvi_eq : tmpL[i.toNat]? = some vi := List.getElem?_eq_getElem (by omega)
          have hvc_eq : tmpL[cIdx.toNat]? = some vc := List.getElem?_eq_getElem (by omega)
          have hvi_lt : vi.toNat < 2 * c.max_vars := hl_i_lt'
          have hvc_lt : vc.toNat < 2 * c.max_vars := by
            simpa [hvc_eq] using hl_c_lt
          have hlen' : tmpL'.length = c.max_vars := by simp [tmpL', htmpL_len]
          have hperm' : (tmpL'.take sz).Perm (s.core.tmp.take sz) :=
            (list_swap_take_perm hi_sz hc_sz (by omega) hvi_eq hvc_eq).trans hperm
          have htail' : ∀ k, sz ≤ k → k < c.max_vars → tmpL'[k]? = s.core.tmp[k]? :=
            fun k hk1 hk2 => by
              rw [list_swap_suffix_eq hi_sz hc_sz hk1]; exact htail k hk1 hk2
          have hbd' : ∀ k < sz, (tmpL'[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk => by
            simpa [htmpL_len] using list_swap_lt_bound (xs := tmpL) (by omega)
              (by simpa [htmpL_len] using hbd)
              (by simpa [htmpL_len] using hvc_lt) (by simpa [htmpL_len] using hvi_lt) hk
          viv_hsteps_nogrp
          refine hLoop (cIdx, ()) _ (by dsimp only; omega)
            ⟨hc_lt, tmpL', hlen', hperm', htail', hbd', ?_⟩
          dsimp only [tmpL', vi]; rw [hvc_cLit]; exact hm
        · viv_hsteps_nogrp
          · exact hJ2 () mL rfl
          · exact hJ2 () mL rfl
          · exact hQ tmpL mL htmpL_len hperm htail hmL
          · exact hQ tmpL mL htmpL_len hperm htail hmL
      · viv_hsteps_nogrp
        · have hch1_lt : 2 * i.toNat + 2 < n.toNat := by c0_bound
          have hch1_sz : 2 * i.toNat + 2 < sz := by omega
          have hl1_lt : (tmpL[2 * i.toNat + 2]?.getD 0#32).toNat < 2 * c.max_vars :=
            hbd (2 * i.toNat + 2) hch1_sz
          have h2i2_bv :
              ((i <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat = 2 * i.toNat + 2 := by
            rw [BitVec.toNat_add, h2i1_bv, show ((1 : BitVec 64)).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          have h2i2_len :
              ((i <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat < tmpL.length := by
            rw [h2i2_bv]; omega
          have hget1 :
              tmpL[((i <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat]'h2i2_len =
                tmpL[2 * i.toNat + 2]?.getD 0#32 := by
            simp only [h2i2_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hl1_lt' :
              (tmpL[((i <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat]'h2i2_len).toNat <
                2 * c.max_vars := by
            rw [hget1]; exact hl1_lt
          have hl1_zext : (BitVec.setWidth 64 (tmpL[
              ((i <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat]'h2i2_len)).toNat <
                2 * c.max_vars := by
            rw [bv64_zext32_toNat']; exact hl1_lt'
          have hl1_tr :
              (BitVec.setWidth 64 ({ s with core := { s.core with tmp := tmpL } }.core.tmp[
                ((i <<< (1 : Nat) + (1 : BitVec 64)) +
                  (1 : BitVec 64)).toNat]'(by dsimp only; exact h2i2_len))).toNat <
                { s with core := { s.core with tmp := tmpL } }.scratch.tarjan_reach.length := by
            dsimp only; rw [htr_len]; exact hl1_zext
          viv_hsteps_nogrp
          refine wp_join_group (ts := [i64, i32, i32])
            (fun (cIdx, cLit, _cCnt, ()) m2 =>
              m2 = mL ∧ i.toNat < cIdx.toNat ∧ cIdx.toNat < n.toNat ∧
              cLit = tmpL[cIdx.toNat]?.getD 0#32)
            (fun _ (cIdx, cLit, cCnt, ()) m2 ⟨hm2, hi_c, hc_lt, hcLit⟩ => ?_)
            (fun _ hJ2 => ?_)
          · subst m2; rw [Blocks.get_here]; dsimp only
            viv_hsteps_nogrp
            exact hJ1 (cIdx, cLit, cCnt, ()) mL ⟨rfl, hi_c, hc_lt, hcLit⟩
          · viv_hsteps_nogrp <;>
              (refine hJ2 _ mL ⟨rfl, ?_, ?_, ?_⟩ <;>
                first
                | (rw [h2i1_bv]; omega)
                | (rw [h2i2_bv]; omega)
                | (dsimp only; rw [List.getElem?_eq_getElem (by rw [h2i1_bv]; omega),
                    Option.getD_some])
                | (dsimp only; rw [List.getElem?_eq_getElem (by rw [h2i2_bv]; omega),
                    Option.getD_some]))
        · refine hJ1 _ mL ⟨rfl, ?_, ?_, ?_⟩ <;>
            first
            | (rw [h2i1_bv]; omega)
            | (dsimp only; rw [List.getElem?_eq_getElem (by rw [h2i1_bv]; omega),
                Option.getD_some])
    · exact hQ tmpL mL htmpL_len hperm htail hmL

theorem full_viv_sort_counts_m6_wp (Γ : Env)
    (hSift : Γ.Has "full_viv_sift_counts_m6" Spec.fullVivSiftCountsM6Spec) :
    ∀ a m Q X, Spec.fullVivSortCountsM6Spec a m Q X →
      Func.wp Γ full_viv_sort_counts_m6_body a m Q X := by
  rintro ⟨h, sz, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hsz_le, htmp, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have htl := hcl.tmp_len_arr
  let InvSort (tmpL : List (BitVec 32)) (mL : Mem 64) : Prop :=
    tmpL.length = c.max_vars ∧
    (tmpL.take sz.toNat).Perm (s.core.tmp.take sz.toNat) ∧
    (∀ k, sz.toNat ≤ k → k < c.max_vars → tmpL[k]? = s.core.tmp[k]?) ∧
    (∀ k < sz.toNat, (tmpL[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c { s with core := { s.core with tmp := tmpL } } ⋆ R) mL
  unfold Func.wp full_viv_sort_counts_m6_body
  viv_hsteps_nogrp
  · exact hQ s.core.tmp m htl (List.Perm.refl _) (fun _ _ _ => rfl) hm
  · have hsz_gt1 : 1 < sz.toNat := by c0_bound
    have hmid_le : ((sz.setWidth 64) >>> 1#64).toNat ≤ sz.toNat := by
      rw [bv64_lshr1_nat, bv64_zext32_toNat']; omega
    refine wp_loop_inv (ts := [i64])
      (fun (k, ()) mL =>
        k.toNat ≤ sz.toNat ∧ ∃ tmpL, InvSort tmpL mL)
      (fun (k, ()) _ => k.toNat)
      (fun J hLoop => hLoop ((sz.setWidth 64) >>> 1#64, ()) m ⟨hmid_le, s.core.tmp,
        htl, List.Perm.refl _, fun _ _ _ => rfl, htmp, hm⟩)
      (fun J (k, ()) mL ⟨hk_le, tmpL, htmpL_len, hperm, htail, hbd, hmL⟩ hLoop => ?_)
    · rw [Blocks.get_here]; dsimp only
      viv_hsteps_nogrp
      · have hk_pos : 0 < k.toNat := by c0_bound
        have hk1_lt : k.toNat - 1 < sz.toNat := by omega
        viv_call hSift
        · refine ⟨c, { s with core := { s.core with tmp := tmpL } }, R, sz.toNat, rfl,
            ⟨{ hcl with tmp_len_arr := htmpL_len }, hlen.scratch_ok⟩,
            by bv_omega, hsz_le, by bv_omega, hbd, hmL,
            fun tmp' m' hlen' hperm' htail' hm' => ?_⟩
          refine hLoop (k - 1#64, ()) m' (by bv_omega) ⟨by bv_omega, tmp', hlen',
            hperm'.trans hperm, fun j hj1 hj2 => by rw [htail' j hj1 hj2]; exact htail j hj1 hj2,
            fun j hj => ?_, hm'⟩
          have hmem_take : tmp'[j]?.getD 0#32 ∈ tmp'.take sz.toNat := by
            rw [List.mem_take_iff_getElem]
            refine ⟨j, by omega, ?_⟩
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hmem_old : tmp'[j]?.getD 0#32 ∈ tmpL.take sz.toNat := hperm'.mem_iff.mp hmem_take
          rw [List.mem_take_iff_getElem] at hmem_old
          obtain ⟨j0, hj0, heq0⟩ := hmem_old
          have hj0' : j0 < sz.toNat := by omega
          have hget0 : tmpL[j0]?.getD 0#32 = tmp'[j]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq0]
          rw [← hget0]; exact hbd j0 hj0'
      · refine wp_loop_inv (ts := [i64])
          (fun (n, ()) m2 => n.toNat ≤ sz.toNat ∧ ∃ tmp2, InvSort tmp2 m2)
          (fun (n, ()) _ => n.toNat)
          (fun J2 hLoop2 => hLoop2 (sz.setWidth 64, ()) mL
            ⟨by rw [bv64_zext32_toNat']; exact Nat.le_refl _,
              tmpL, htmpL_len, hperm, htail, hbd, hmL⟩)
          (fun J2 (n, ()) m2 ⟨hn_le, tmp2, htmp2_len, hperm2, htail2, hbd2, hm2⟩ hLoop2 => ?_)
        · rw [Blocks.get_here]; dsimp only
          have hmax_pos : 0 < c.max_vars := by omega
          have h0_64 : (BitVec.ofNat 64 0).toNat < tmp2.length := by simp [htmp2_len, hmax_pos]
          viv_hsteps_nogrp
          · have hn_gt1 : 1 < n.toNat := by c0_bound
            have hm1_lt : n.toNat - 1 < sz.toNat := by omega
            have h0_lt : 0 < sz.toNat := by omega
            have hl0_lt : (tmp2[0]?.getD 0#32).toNat < 2 * c.max_vars := hbd2 0 h0_lt
            have hlm_lt : (tmp2[n.toNat - 1]?.getD 0#32).toNat < 2 * c.max_vars :=
              hbd2 (n.toNat - 1) hm1_lt
            let v0 := tmp2[0]'(by omega)
            let vm := tmp2[n.toNat - 1]'(by omega)
            have hv0_eq : tmp2[0]? = some v0 := List.getElem?_eq_getElem (by omega)
            have hvm_eq : tmp2[n.toNat - 1]? = some vm := List.getElem?_eq_getElem (by omega)
            have hv0_lt : v0.toNat < 2 * c.max_vars := by
              simpa [hv0_eq] using hl0_lt
            have hvm_lt : vm.toNat < 2 * c.max_vars := by
              simpa [hvm_eq] using hlm_lt
            let tmp2' := (tmp2.set 0 vm).set (n.toNat - 1) v0
            have hlen' : tmp2'.length = c.max_vars := by simp [tmp2', htmp2_len]
            have hperm' : (tmp2'.take sz.toNat).Perm (s.core.tmp.take sz.toNat) :=
              (list_swap_take_perm h0_lt hm1_lt (by omega) hv0_eq hvm_eq).trans hperm2
            have htail' : ∀ j, sz.toNat ≤ j → j < c.max_vars → tmp2'[j]? = s.core.tmp[j]? :=
              fun j hj1 hj2 => by
                rw [list_swap_suffix_eq h0_lt hm1_lt hj1]; exact htail2 j hj1 hj2
            have hbd' : ∀ j < sz.toNat, (tmp2'[j]?.getD 0#32).toNat < 2 * c.max_vars :=
              fun j hj => by
                simpa [htmp2_len] using list_swap_lt_bound (xs := tmp2) (by omega)
                  (by simpa [htmp2_len] using hbd2)
                  (by simpa [htmp2_len] using hvm_lt) (by simpa [htmp2_len] using hv0_lt) hj
            have hn1_bv : (n - (1 : BitVec 64)).toNat = n.toNat - 1 := by bv_omega
            viv_hsteps_nogrp
            viv_call hSift
            · refine ⟨c, { s with core := { s.core with tmp := tmp2' } }, R, sz.toNat, rfl,
                ⟨{ hcl with tmp_len_arr := hlen' }, hlen.scratch_ok⟩,
                by bv_omega, hsz_le, by bv_omega, hbd', ?_,
                fun tmp'' m'' hlen'' hperm'' htail'' hm'' => ?_⟩
              · dsimp only [tmp2', v0, vm]
                simpa only [hn1_bv,
                  show (BitVec.ofNat 64 0).toNat = 0 from rfl] using hm
              refine hLoop2 (n - 1#64, ()) m'' (by bv_omega) ⟨by bv_omega, tmp'', hlen'',
                hperm''.trans hperm',
                fun j hj1 hj2 => by rw [htail'' j hj1 hj2]; exact htail' j hj1 hj2,
                fun j hj => ?_, hm''⟩
              have hmem_take : tmp''[j]?.getD 0#32 ∈ tmp''.take sz.toNat := by
                rw [List.mem_take_iff_getElem]
                refine ⟨j, by omega, ?_⟩
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hmem_old : tmp''[j]?.getD 0#32 ∈ tmp2'.take sz.toNat :=
                hperm''.mem_iff.mp hmem_take
              rw [List.mem_take_iff_getElem] at hmem_old
              obtain ⟨j0, hj0, heq0⟩ := hmem_old
              have hj0' : j0 < sz.toNat := by omega
              have hget0 : tmp2'[j0]?.getD 0#32 = tmp''[j]?.getD 0#32 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq0]
              rw [← hget0]; exact hbd' j0 hj0'
          · exact hQ tmp2 m2 htmp2_len hperm2 htail2 hm2

end LeanQbe.T.Examples.Kissat.Proof.Vivify
