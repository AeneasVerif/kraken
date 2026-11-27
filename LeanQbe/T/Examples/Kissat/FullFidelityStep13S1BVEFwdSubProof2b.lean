/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1BVEFwdSubProof2a
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullM6SweepProofDenseProp
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-B Proofs — Part 2b
(`cert_{finish_unit,loop2_large,loop1_large,loop1}_wp`)

`0` `import all`, `0` `@[expose]` on theorems/lemmas, `<= 100` cols, `< 1,400` LOC, every
theorem `<= 420` lines.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve

open scoped FullArenaTactics CertMkTactics
open CertMkTactics

public section

theorem cert_finish_unit_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s_cur : FullState) (R : Mem 64 → Prop) (unit : BitVec 32) (m_cur : Mem 64)
    (hinv_cur : FullDenseInvW c F0 F_cur s_cur) (htmk_cur : TmkZero s_cur)
    (hunit : unit.toNat < 2 * s_cur.core.cur_vars)
    (hentU : (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))
    (hm_cur : (Full.FullMem c s_cur ⋆ R) m_cur)
    (hQ_ok : ∀ (s' : FullState) (m' : Mem 64), FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s_cur.core.cur_vars → s'.core.arena = s_cur.core.arena →
      s'.core.arena_len = s_cur.core.arena_len → s'.core.fuel = s_cur.core.fuel →
      s'.scratch.scratch_buf = s_cur.scratch.scratch_buf →
      (Full.FullMem c s' ⋆ R) m' → Q (true, ()) m') :
    wp Γ Q X (certFinishUnitExpr c.hdr c.pVals unit) m_cur := by
  have hunit_len : (BitVec.zeroExtend 64 unit).toNat < s_cur.core.vals.length := by
    have hvl := hinv_cur.1.core_ok.vals_len; have hcv := hinv_cur.1.core_ok.cur_vars_le
    rw [cert_zext64_toNat]; omega
  unfold certFinishUnitExpr; c0_hsteps_nogrp
  refine wp_join_state (α := FullState) (fun _ => ())
    (fun s3 m3 => FullDenseInvW c F0 F_cur s3 ∧ TmkZero s3 ∧
      s3.core.cur_vars = s_cur.core.cur_vars ∧ s3.core.arena = s_cur.core.arena ∧
      s3.core.arena_len = s_cur.core.arena_len ∧ s3.core.fuel = s_cur.core.fuel ∧
      s3.scratch.scratch_buf = s_cur.scratch.scratch_buf ∧ (Full.FullMem c s3 ⋆ R) m3)
    (fun J_u s3 m3 ⟨hinv3, htmk3, hcv3, har3, hal3, hfl3, hscr3, hm3⟩ => by
      c0_hsteps; exact hQ_ok s3 m3 hinv3 htmk3 hcv3 har3 hal3 hfl3 hscr3 hm3)
    (fun J_u hJu => by
      c0_hsteps_nogrp
      · have hu' : unit.toNat < s_cur.core.vals.length := by rwa [cert_zext64_toNat] at hunit_len
        have hvu255 : s_cur.core.vals[unit.toNat]?.getD 0#8 = 255#8 := by
          have hdom := hinv_cur.2.1.vals_domain unit.toNat hunit
          rw [List.getElem?_eq_getElem hu'] at hdom ⊢
          first | exact cert_i8_slt0_eq_255 _ hdom hc | exact cert_i8_slt_zero_eq_255 _ hdom hc
        have hinv3 := cert_denseInvW_set_inconsistent hinv_cur (cert_lvl0_unit_contra_unsat hentU
          (cert_lvl0_false_entails hinv_cur.2.1 hinv_cur.2.2.2.2.2.1 hunit hvu255))
        c0_hsteps; exact hJu { s_cur with core := { s_cur.core with inconsistent := 1#64 } } _
          ⟨hinv3, htmk_cur, rfl, rfl, rfl, rfl, rfl, by assumption⟩
      · c0_hsteps_nogrp
        refine wp_join_state (α := FullState) (fun _ => ())
          (fun s3 m3 => FullDenseInvW c F0 F_cur s3 ∧ TmkZero s3 ∧
            s3.core.cur_vars = s_cur.core.cur_vars ∧ s3.core.arena = s_cur.core.arena ∧
            s3.core.arena_len = s_cur.core.arena_len ∧ s3.core.fuel = s_cur.core.fuel ∧
            s3.scratch.scratch_buf = s_cur.scratch.scratch_buf ∧ (Full.FullMem c s3 ⋆ R) m3)
          (fun J_u2 s3 m3 hst3 => by c0_hsteps; exact hJu s3 m3 hst3)
          (fun J_u2 hJu2 => by
            c0_hsteps
            · have hu' : unit.toNat < s_cur.core.vals.length := by
                rwa [cert_zext64_toNat] at hunit_len
              have hvu0 : s_cur.core.vals[unit.toNat]?.getD 0#8 = 0#8 := by
                rw [List.getElem?_eq_getElem hu']; exact hc
              have htr_lt : s_cur.core.trail_end < c.max_vars :=
                Nat.lt_of_lt_of_le (cert_trail_end_lt_of_val0 hinv_cur.2.1
                  hinv_cur.1.core_ok.trail_end_le hunit hvu0) hinv_cur.1.core_ok.cur_vars_le
              fid_call hAssign; dsimp only [vals, Arg.val]
              refine ⟨c, s_cur, R, rfl, hinv_cur.1, hm_cur, ?_⟩
              have hno : ¬ (s_cur.core.cur_vars ≤ unit.toNat / 2 ∨
                  c.max_vars ≤ s_cur.core.trail_end ∨
                  s_cur.core.vals[unit.toNat]?.getD 0#8 ≠ 0#8) := by
                rw [hvu0]; simp only [ne_self_iff_false, or_false]; omega
              rw [ite_eq_right (fun h => absurd h hno)]; dsimp only
              intro flags' unass' phases' m3 hfl hlph hm3
              simp only [show ((0 : BitVec 32) = 0#32) = True from eq_true rfl, ↓reduceIte] at hm3 ⊢
              have hp_dens := @assignLvl0_preserves_denseInvW c F0 F_cur s_cur hinv_cur
                unit flags' unass' (s_cur.core.unflushed + 1#64) phases' hfl hlph hunit hvu0 hentU
              c0_hsteps; exact hJu2 _ m3 ⟨hp_dens.1, htmk_cur, rfl, rfl, rfl, rfl, rfl, hm3⟩
            · exact hJu2 s_cur m_cur ⟨hinv_cur, htmk_cur, rfl, rfl, rfl, rfl, rfl, hm_cur⟩))

theorem cert_loop2_large_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (Js : Cont [.bool, .bool, i32, i32]) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (tmp' exp tmk scr' gu' : List (BitVec 32)) (w lsz unit nv max_csz : BitVec 32) (ok2 : Bool)
    (P : (Nat → Bool) → Prop) (m' : Mem 64)
    (hP : P = certModelSet F_cur exp nv.toNat unit.toNat) (hok2_t : ok2 = true)
    (hinv : FullDenseInvW c F0 F_cur s) (htmp'_len : tmp'.length = c.max_vars)
    (_hexp_len : exp.length = 2 * c.max_vars) (htmk_len : tmk.length = 2 * c.max_vars)
    (_hscr'_len : scr'.length = c.scratch_cap) (_hgu'_len : gu'.length = 64)
    (_hcur_pos : 0 < s.core.cur_vars)
    (_hmaxv_pos : 0 < c.max_vars) (hnv_mv : nv.toNat ≤ k6MaxV c.scratch_cap)
    (hmv_le : k6MaxV c.scratch_cap ≤ 8192) (hnv_cv : nv.toNat ≤ s.core.cur_vars)
    (hmcsz_pos : 0 < max_csz.toNat) (hmcsz_le : max_csz.toNat ≤ c.max_vars)
    (_hmcsz_lt : max_csz.toNat < 2 ^ 32) (hok : certExportOk s.core.cur_vars nv.toNat tmk exp)
    (hwref : w.toNat ∈ fullArenaClauseRefs s)
    (hwgarb : fullArenaClauseGarbCore s.core w.toNat = false)
    (hlsz_eq : lsz.toNat = fullArenaClauseSizeCore s.core w.toNat)
    (hlsz_bound : w.toNat + 3 + lsz.toNat ≤ s.core.arena.length) (hlsz_lt_29 : lsz.toNat < 2 ^ 29)
    (hm' : (Full.FullMem c (certMkStateGu s tmp' exp tmk scr' gu') ⋆ R) m')
    (hB3 : ∀ bst : Bool × Bool × BitVec 32 × BitVec 32 × List (BitVec 32) × Mem 64,
      ∀ m2_in : Mem 64,
      (match bst with
       | (ok2_l, sat2, csz2, _, tmp2, m_n) => m2_in = m_n ∧ tmp2.length = c.max_vars ∧
         (ok2_l = true → sat2 = false → csz2.toNat ≤ max_csz.toNat ∧
           (∀ j < csz2.toNat, (tmp2[j]?.getD 0#32).toNat < 2 * nv.toNat) ∧
           SemEntails P (List.map BitVec.toNat (List.take csz2.toNat tmp2))) ∧
         (Full.FullMem c (certMkStateGu s tmp2 exp tmk scr' gu') ⋆ R) m_n) →
      Js (match bst with | (ok2_l, sat2, csz2, k2, _, _) => (ok2_l, sat2, csz2, k2, ())) m2_in) :
    wp Γ Q X (certLoop2LargeExpr Js c.pArena c.pVals c.pTarjanMark c.pTmp w lsz unit nv max_csz ok2)
      m' := by
  subst hP; subst hok2_t
  let clits := fullArenaClauseLits s w.toNat
  have hcl_ent := hinv.2.1.arena.entails w.toNat hwref hwgarb
  have hcl_lt := hinv.2.1.arena.lits_lt w.toNat hwref hwgarb
  have hcl_len : clits.length = lsz.toNat := by
    simp [clits, fullArenaClauseLitsCore, hlsz_eq]; omega
  have hcv_le := hinv.1.core_ok.cur_vars_le; have hvals_len := hinv.1.core_ok.vals_len
  unfold certLoop2LargeExpr
  refine wp_while_state (fun st : BitVec 32 × BitVec 32 × List (BitVec 32) => (st.1, st.2.1, ()))
    (fun (_, k, _) => lsz.toNat - k.toNat)
    (fun (csz2, k, tmp2) m2_in => k.toNat ≤ lsz.toNat ∧ csz2.toNat ≤ max_csz.toNat ∧
      tmp2.length = c.max_vars ∧ (∀ j < csz2.toNat, (tmp2[j]?.getD 0#32).toNat < 2 * nv.toNat) ∧
      (∀ β, certModelSet F_cur exp nv.toNat unit.toNat β →
        ∀ α, (cnfOfClauses F_cur).Sat α → ¬ (cnfClause [unit.toNat]).Sat α →
        (∀ i < nv.toNat, β i = α (exp[i]?.getD 0#32).toNat) →
        (∃ p < k.toNat, (cnfClause [clits[p]?.getD 0]).Sat α) →
        ∃ j < csz2.toNat, (cnfClause [(tmp2[j]?.getD 0#32).toNat]).Sat β) ∧
      (Full.FullMem c (certMkStateGu s tmp2 exp tmk scr' gu') ⋆ R) m2_in)
    (fun L3 hL3 => by
      c0_hsteps; exact hL3 (0#32, 0#32, tmp') m' ⟨Nat.zero_le _, Nat.zero_le _, htmp'_len,
        fun _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ _ _ _ _ ⟨_, hp, _⟩ => absurd hp (Nat.not_lt_zero _), hm'⟩)
    (fun L3 (csz2, k, tmp2) m2_in ⟨hk_le, hcsz_le, htmp2_len, hlts, hsat_ih, hm2_mem⟩ ih => ?_)
  c0_hsplit
  · have hk_lt : k.toNat < lsz.toNat := by c0_bound
    have hw32 : w.toNat < 2 ^ 32 := w.isLt; have hk32 : k.toNat < 2 ^ 32 := k.isLt
    have har_idx_eq : (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k).toNat =
        w.toNat + 3 + k.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, cert_zext64_toNat, cert_zext64_toNat,
        show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have har_idx_lt : (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k).toNat <
        s.core.arena.length := by rw [har_idx_eq]; omega
    let q := s.core.arena[w.toNat + 3 + k.toNat]
    have har_eq2 : (certMkStateGu s tmp2 exp tmk scr' gu').core.arena[(BitVec.zeroExtend 64 w +
        3#64 + BitVec.zeroExtend 64 k).toNat] = q :=
      cert_list_getElem_eq (certMkStateGu_arena ..) har_idx_eq
        (by rw [certMkStateGu_arena]; exact har_idx_lt) (by omega)
    have hq_cl : clits[k.toNat]? = some q.toNat := by
      have hidx_ar : w.toNat + 3 + k.toNat < s.core.arena.length := by omega
      simp [clits, fullArenaClauseLitsCore, ← hlsz_eq, hk_lt, List.getElem?_drop,
        List.getElem?_eq_getElem hidx_ar, q]
    have hq_lt : q.toNat < 2 * s.core.cur_vars := hcl_lt q.toNat (List.mem_of_getElem? hq_cl)
    have hq_len : (BitVec.zeroExtend 64 ((certMkStateGu s tmp2 exp tmk scr' gu').core.arena[
        (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k).toNat])).toNat <
        (certMkStateGu s tmp2 exp tmk scr' gu').core.vals.length := by
      rw [certMkStateGu_vals, har_eq2, cert_zext64_toNat]; exact Nat.lt_of_lt_of_le hq_lt (by omega)
    have hidx_mod : (w.toNat + BitVec.toNat (3#64) + k.toNat) % 2 ^ 64 =
        w.toNat + 3 + k.toNat := by
      rw [show BitVec.toNat (3#64) = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
    have har_mod_lt : (w.toNat + BitVec.toNat (3#64) + k.toNat) % 2 ^ 64 <
        s.core.arena.length := by rw [hidx_mod]; omega
    let q_mod := s.core.arena[(w.toNat + BitVec.toNat (3#64) + k.toNat) % 2 ^ 64]'har_mod_lt
    have hq_ar_eq : q_mod = q := cert_list_getElem_eq rfl hidx_mod har_mod_lt (by omega)
    have hu_eq := cert_shr1_toNat q
    have hq_mod_div : q_mod.toNat / 2 < tmk.length := by rw [hq_ar_eq]; omega
    have hq_mod_lt : q_mod.toNat < s.core.vals.length := by rw [hq_ar_eq]; omega
    have hu_lt_tmk : (BitVec.zeroExtend 64 ((certMkStateGu s tmp2 exp tmk scr' gu').core.arena[
        (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k).toNat] >>> 1#32)).toNat <
        tmk.length := by rw [har_eq2, cert_zext64_toNat, hu_eq]; omega
    have hFail3 : Js (false, false, csz2, k, ()) m2_in :=
      hB3 (false, false, csz2, k, tmp2, m2_in) m2_in
        ⟨rfl, htmp2_len, fun hc => absurd hc (by decide), hm2_mem⟩
    have hStepKeep : (∀ α, (cnfOfClauses F_cur).Sat α → ¬ (cnfClause [unit.toNat]).Sat α →
          ¬ (cnfClause [q.toNat]).Sat α) → L3 (csz2, k + 1#32, ()) m2_in := fun hq_false =>
      ih (csz2, k + 1#32, tmp2) m2_in (by simp [BitVec.toNat_add]; omega)
        ⟨by simp [BitVec.toNat_add]; omega, hcsz_le, htmp2_len, hlts,
         fun β hPβ α hsat hnu hmap ⟨p, hp, hps⟩ => by
           have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hk1] at hp; by_cases hpk : p = k.toNat
           · subst hpk; rw [show clits[k.toNat]?.getD 0 = q.toNat by simp [hq_cl]] at hps
             exact absurd hps (hq_false α hsat hnu)
           · exact hsat_ih β hPβ α hsat hnu hmap ⟨p, by omega, hps⟩, hm2_mem⟩
    c0_hsteps
    · exact hB3 (true, true, csz2, k, tmp2, m2_in) m2_in
        ⟨rfl, htmp2_len, fun _ hc => absurd hc (by decide), hm2_mem⟩
    · exact hFail3
    · exact hFail3
    · exact hFail3
    · have hcsz_lt : csz2.toNat < max_csz.toNat := by c0_bound
      have hcsz_tmp_lt : (BitVec.zeroExtend 64 csz2).toNat < tmp2.length := by
        rw [cert_zext64_toNat]; omega
      have hloc_ar : tmk[q_mod.toNat / 2]'hq_mod_div = tmk[q.toNat / 2] :=
        cert_list_getElem_eq rfl (by rw [hq_ar_eq]) hq_mod_div (by omega)
      have hloc_nz : tmk[q.toNat / 2] ≠ 0#32 := by rw [← hloc_ar]; dsimp only [q_mod]; c0_bound
      have hloc_le : tmk[q.toNat / 2].toNat ≤ nv.toNat := by
        rw [← hloc_ar]; dsimp only [q_mod]; c0_bound
      have hget_loc := cert_getElemD (by omega : q.toNat / 2 < tmk.length) 0#32
      have hok_q := hok.1 (q.toNat / 2) (by omega) (by rwa [hget_loc])
      have hloc1 : 1 ≤ tmk[q.toNat / 2].toNat := by rw [← hget_loc]; exact hok_q.1
      let loc := tmk[(q >>> 1#32).toNat]
      have hloc_eq : loc = tmk[q.toNat / 2] :=
        cert_list_getElem_eq rfl hu_eq (by rw [hu_eq]; omega) (by omega)
      let ml := ((loc - 1#32) <<< 1#32) ||| (q &&& 1#32)
      let tmp2' := tmp2.set (BitVec.zeroExtend 64 csz2).toNat ml
      have htmp2'_eq : tmp2' = tmp2.set csz2.toNat ml := by
        dsimp only [tmp2']; rw [cert_zext64_toNat]
      have hml_toNat : ml.toNat = 2 * (loc.toNat - 1) + q.toNat % 2 :=
        cert_packed_lit_toNat loc q (by rw [hloc_eq]; exact hloc1) (by rw [hloc_eq]; omega)
      have hml_lt : ml.toNat < 2 * nv.toNat := by rw [hml_toNat, hloc_eq]; omega
      refine ih (csz2 + 1#32, k + 1#32, tmp2') _ (by simp [BitVec.toNat_add]; omega)
        ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega,
         by rw [htmp2'_eq, List.length_set]; exact htmp2_len,
         fun j hj => by
           have hcsz1 : (csz2 + 1#32).toNat = csz2.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hcsz1] at hj; rw [htmp2'_eq]
           by_cases hjc : j = csz2.toNat
           · subst hjc
             rw [List.getElem?_set_self
               (by rw [← cert_zext64_toNat csz2]; exact hcsz_tmp_lt), Option.getD_some]
             exact hml_lt
           · rw [List.getElem?_set_ne (Ne.symm hjc)]; exact hlts j (by omega),
         fun β hPβ α hsat hnu hmap ⟨p, hp, hps⟩ => by
           have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hk1] at hp
           by_cases hpk : p = k.toNat
           · subst hpk
             have hpeq : clits[k.toNat]?.getD 0 = q.toNat := by rw [hq_cl, Option.getD_some]
             rw [hpeq] at hps
             have hexp_loc : (exp[loc.toNat - 1]?.getD 0#32).toNat = q.toNat / 2 := by
               rw [← show tmk[q.toNat / 2]?.getD 0#32 = loc from hloc_eq ▸ hget_loc]
               exact hok_q.2.2
             refine ⟨csz2.toNat, by simp [BitVec.toNat_add]; omega, ?_⟩
             rw [htmp2'_eq, List.getElem?_set_self (by omega), Option.getD_some]
             exact cert_mapped_lit_sat (hloc_eq ▸ hloc1) (hloc_eq ▸ hloc_le)
               hexp_loc hmap (by rw [hml_toNat]; omega) (by rw [hml_toNat]; omega) hps
           · rcases hsat_ih β hPβ α hsat hnu hmap ⟨p, by omega, hps⟩ with ⟨j, hj, hjs⟩
             refine ⟨j, by simp [BitVec.toNat_add]; omega, ?_⟩
             rw [htmp2'_eq, List.getElem?_set_ne (by omega : csz2.toNat ≠ j)]; exact hjs,
         by
           have har_sw : (certMkStateGu s tmp2 exp tmk scr' gu').core.arena[(BitVec.setWidth 64 w +
               3 + BitVec.setWidth 64 k).toNat] = q := har_eq2
           have htm_ar : (certMkStateGu s tmp2 exp tmk scr' gu').scratch.tarjan_mark[
               (BitVec.setWidth 64 ((certMkStateGu s tmp2 exp tmk scr' gu').core.arena[
                 (BitVec.setWidth 64 w + 3 + BitVec.setWidth 64 k).toNat] >>>
                   OfNat.ofNat 1)).toNat] = loc :=
             cert_list_getElem_eq (certMkStateGu_tmk s tmp2 exp tmk scr' gu')
               (by rw [har_sw, cert_zext64_toNat]; rfl)
               (by rw [certMkStateGu_tmk]; exact hu_lt_tmk) (by rw [hu_eq]; omega)
           have hm0 := hm
           simp only [har_sw] at hm0; exact hm0⟩
    · have hvq255 : s.core.vals[q.toNat]?.getD 0#8 = 255#8 := by
        have hvs_eq : s.core.vals[q_mod.toNat]'hq_mod_lt = s.core.vals[q.toNat] :=
          cert_list_getElem_eq rfl (by rw [hq_ar_eq]) hq_mod_lt (by omega)
        have hns : (0#8 : BitVec 8).slt s.core.vals[q.toNat] = false := by
          rw [← hvs_eq]; dsimp only [q_mod]; c0_bound
        have hne : s.core.vals[q.toNat] ≠ 0#8 := by rw [← hvs_eq]; dsimp only [q_mod]; c0_bound
        have hdom := hinv.2.1.vals_domain q.toNat hq_lt
        rw [List.getElem?_eq_getElem (by omega : q.toNat < s.core.vals.length)] at hdom ⊢
        exact cert_i8_dom_255_bv8 _ hdom hns hne
      have hneg_q := cert_lvl0_false_entails hinv.2.1 hinv.2.2.2.2.2.1 hq_lt hvq255
      exact hStepKeep fun α hsat _ hqs => by
        rw [CNF.entails_clause_def] at hneg_q; have hcx := hneg_q α hsat
        rw [cert_clause_sat_xor_neg] at hcx; exact hcx hqs
    · have hqu : q.toNat = unit.toNat := by
        have hqeq : q_mod = unit := by dsimp only [q_mod]; c0_bound
        rw [hq_ar_eq] at hqeq; exact congrArg BitVec.toNat hqeq
      exact hStepKeep fun _ _ hnu hqs => hnu (hqu ▸ hqs)
  · have hk_eq : k.toNat = lsz.toNat := by c0_bound
    refine hB3 (true, false, csz2, k, tmp2, m2_in) m2_in
      ⟨rfl, htmp2_len, fun _ _ => ⟨hcsz_le, hlts, ?_⟩, hm2_mem⟩
    intro β ⟨α, hsat, hnu, hmap⟩
    rcases cert_entails_in_modelSet hcl_ent hsat hnu with ⟨q, hqm, _, hqs⟩
    rcases List.mem_iff_getElem.mp hqm with ⟨p, hplen, hpeq⟩
    rcases hsat_ih β ⟨α, hsat, hnu, hmap⟩ α hsat hnu hmap
      ⟨p, by rw [hk_eq, ← hcl_len]; exact hplen, by rw [cert_getElemD hplen, hpeq]; exact hqs⟩
      with ⟨j, hj, hjs⟩
    rw [cert_clause_sat_iff_mem]
    exact ⟨(tmp2[j]?.getD 0#32).toNat, List.mem_map.mpr ⟨tmp2[j]?.getD 0#32,
      List.mem_take_iff_getElem.mpr ⟨j, by rw [htmp2_len]; omega,
        (cert_getElemD (by omega : j < tmp2.length) 0#32).symm⟩, rfl⟩, hjs⟩

theorem cert_loop1_large_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (Js : Cont [i32, .bool, .bool, i32, i32]) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop) (exp tmk : List (BitVec 32))
    (w lsz unit nv mv : BitVec 32) (ab : Bool) (m' : Mem 64)
    (hinv : FullDenseInvW c F0 F_cur s) (hexp_len : exp.length = 2 * c.max_vars)
    (htmk_len : tmk.length = 2 * c.max_vars) (hmaxv_lt : c.max_vars < 2 ^ 32)
    (hnv_mv : nv.toNat ≤ mv.toNat) (hnv_cv : nv.toNat ≤ s.core.cur_vars)
    (hok : certExportOk s.core.cur_vars nv.toNat tmk exp) (hwref : w.toNat ∈ fullArenaClauseRefs s)
    (hwgarb : fullArenaClauseGarbCore s.core w.toNat = false)
    (hlsz_eq : lsz.toNat = fullArenaClauseSizeCore s.core w.toNat)
    (hlsz_bound : w.toNat + 3 + lsz.toNat ≤ s.core.arena.length) (hlsz_lt_29 : lsz.toNat < 2 ^ 29)
    (hm' : (Full.FullMem c (certMkState s s.core.tmp exp tmk s.scratch.scratch_buf) ⋆ R) m')
    (hB3 : ∀ bst : BitVec 32 × Bool × Bool × BitVec 32 × BitVec 32 ×
        List (BitVec 32) × List (BitVec 32) × Mem 64, ∀ m_in : Mem 64,
      (match bst with
       | (nv', ab', sat', csz', _, tmk', exp', m_n) => m_in = m_n ∧ nv'.toNat ≤ mv.toNat ∧
         nv'.toNat ≤ s.core.cur_vars ∧ tmk'.length = 2 * c.max_vars ∧ exp'.length = 2 * c.max_vars ∧
         certExportOk s.core.cur_vars nv'.toNat tmk' exp' ∧
         (ab' = false → sat' = false → csz' = 0#32 →
           (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat])) ∧
         (Full.FullMem c (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf) ⋆ R) m_n) →
      Js (match bst with | (nv', ab', sat', csz', k', _, _, _) => (nv', ab', sat', csz', k', ()))
        m_in) :
    wp Γ Q X (certLoop1LargeExpr Js c.hdr c.pArena c.pVals c.pTarjanMark c.pWsort
      w lsz unit nv mv ab) m' := by
  let clits := fullArenaClauseLits s w.toNat
  have hcl_ent := hinv.2.1.arena.entails w.toNat hwref hwgarb
  have hcl_lt := hinv.2.1.arena.lits_lt w.toNat hwref hwgarb
  have hcl_len : clits.length = lsz.toNat := by
    simp [clits, fullArenaClauseLitsCore, hlsz_eq]; omega
  have hcv_le := hinv.1.core_ok.cur_vars_le; have hvals_len := hinv.1.core_ok.vals_len
  unfold certLoop1LargeExpr
  refine wp_while_state (fun st : BitVec 32 × BitVec 32 × BitVec 32 ×
      List (BitVec 32) × List (BitVec 32) => (st.1, st.2.1, st.2.2.1, ()))
    (fun (_, _, k', _, _) => lsz.toNat - k'.toNat)
    (fun (nv', csz', k', tmk', exp') m_in => k'.toNat ≤ lsz.toNat ∧ csz'.toNat ≤ k'.toNat ∧
      nv'.toNat ≤ mv.toNat ∧ nv'.toNat ≤ s.core.cur_vars ∧ tmk'.length = 2 * c.max_vars ∧
      exp'.length = 2 * c.max_vars ∧ certExportOk s.core.cur_vars nv'.toNat tmk' exp' ∧
      (csz' = 0#32 → ∀ p < k'.toNat, let ql := clits[p]?.getD 0; ql ≠ unit.toNat →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [ql ^^^ 1])) ∧
      (Full.FullMem c (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf) ⋆ R) m_in)
    (fun L3 hL3 => by
      c0_hsteps; exact hL3 (nv, 0#32, 0#32, tmk, exp) m' ⟨Nat.zero_le _, Nat.zero_le _, hnv_mv,
        hnv_cv, htmk_len, hexp_len, hok, fun _ _ hp => absurd hp (Nat.not_lt_zero _), hm'⟩)
    (fun L3 (nv', csz', k', tmk', exp') m_in
      ⟨hk_le, hcsz_le, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok', hzero', hm_in⟩ ih => ?_)
  c0_hsplit
  · have hk_lt : k'.toNat < lsz.toNat := by c0_bound
    have hw32 : w.toNat < 2 ^ 32 := w.isLt; have hk32 : k'.toNat < 2 ^ 32 := k'.isLt
    have har_idx_eq : (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k').toNat =
        w.toNat + 3 + k'.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, cert_zext64_toNat, cert_zext64_toNat,
        show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have har_idx_lt : (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k').toNat <
        (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf).core.arena.length := by
      rw [certMkState_arena, har_idx_eq]; omega
    let q := s.core.arena[w.toNat + 3 + k'.toNat]
    have har_eq2 : (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf).core.arena[
        (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k').toNat] = q :=
      cert_list_getElem_eq (certMkState_arena s s.core.tmp exp' tmk' s.scratch.scratch_buf)
        har_idx_eq (by rw [certMkState_arena]; exact har_idx_eq ▸ by omega) (by omega)
    have hq_cl : clits[k'.toNat]? = some q.toNat := by
      have hi : w.toNat + 3 + k'.toNat < s.core.arena.length := by omega
      simp [clits, fullArenaClauseLitsCore, ← hlsz_eq, hk_lt, List.getElem?_drop,
        List.getElem?_eq_getElem hi, q]
    have hq_lt : q.toNat < 2 * s.core.cur_vars := hcl_lt q.toNat (List.mem_of_getElem? hq_cl)
    have hq_len : (BitVec.zeroExtend 64 ((certMkState s s.core.tmp exp' tmk'
        s.scratch.scratch_buf).core.arena[(BitVec.zeroExtend 64 w + 3#64 +
          BitVec.zeroExtend 64 k').toNat])).toNat <
        (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf).core.vals.length := by
      rw [certMkState_vals, har_eq2, cert_zext64_toNat]; exact Nat.lt_of_lt_of_le hq_lt (by omega)
    have hidx_mod : (w.toNat + BitVec.toNat (3#64) + k'.toNat) % 2 ^ 64 =
        w.toNat + 3 + k'.toNat := by
      rw [show BitVec.toNat (3#64) = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
    have har_mod_lt : (w.toNat + BitVec.toNat (3#64) + k'.toNat) % 2 ^ 64 <
        s.core.arena.length := by rw [hidx_mod]; omega
    let q_mod := s.core.arena[(w.toNat + BitVec.toNat (3#64) + k'.toNat) % 2 ^ 64]'har_mod_lt
    have hq_ar_eq : q_mod = q := cert_list_getElem_eq rfl hidx_mod har_mod_lt (by omega)
    have hu_eq := cert_shr1_toNat q
    have hq_mod_lt : q_mod.toNat < s.core.vals.length := by rw [hq_ar_eq]; omega
    c0_hsteps
    · exact hB3 (nv', ab, true, csz', k', tmk', exp', m_in) m_in
        ⟨rfl, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok',
         fun _ hs _ => absurd hs (by decide), hm_in⟩
    · have hu_lt_cv : q.toNat / 2 < s.core.cur_vars := by omega
      have hu_lt_tmk : (BitVec.zeroExtend 64 ((certMkState s s.core.tmp exp' tmk'
          s.scratch.scratch_buf).core.arena[(BitVec.zeroExtend 64 w + 3#64 +
            BitVec.zeroExtend 64 k').toNat] >>> 1#32)).toNat < tmk'.length := by
        rw [har_eq2, cert_zext64_toNat, hu_eq]; omega
      have hcsz_add : (csz' + 1#32).toNat = csz'.toNat + 1 := by simp [BitVec.toNat_add]; omega
      have hcsz_nz : csz' + 1#32 ≠ 0#32 := fun heq => by
        have ht := congrArg BitVec.toNat heq; rw [hcsz_add] at ht; simp at ht
      c0_hsteps
      · exact hB3 (nv', true, false, csz', k', tmk', exp', m_in) m_in
          ⟨rfl, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok',
           fun ha _ _ => absurd ha (by decide), hm_in⟩
      · exact hB3 (nv', true, false, csz', k', tmk', exp', m_in) m_in
          ⟨rfl, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok',
           fun ha _ _ => absurd ha (by decide), hm_in⟩
      · have hnv_lt_mv : nv'.toNat < mv.toNat := by c0_bound
        have hnv_lt_cv : nv'.toNat < s.core.cur_vars := by
          change ¬s.core.cur_vars % 2 ^ 64 ≤ nv'.toNat at hc
          rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hnv_lt_exp : (BitVec.zeroExtend 64 nv').toNat < exp'.length := by
          rw [cert_zext64_toNat]; omega
        have ht0 : tmk'[q.toNat / 2]?.getD 0#32 = 0#32 := by
          have heq0 : tmk'[q_mod.toNat / 2] = 0#32 := by dsimp only [q_mod]; c0_bound
          have hta : tmk'[q_mod.toNat / 2] = tmk'[q.toNat / 2] :=
            cert_list_getElem_eq rfl (by rw [hq_ar_eq]) (by rw [hq_ar_eq]; omega) (by omega)
          rw [hta] at heq0; rw [cert_getElemD (by omega : q.toNat / 2 < tmk'.length)]; exact heq0
        c0_hsteps
        let exp'' := exp'.set (BitVec.zeroExtend 64 nv').toNat (q >>> 1#32)
        let tmk'' := tmk'.set (BitVec.zeroExtend 64 (q >>> 1#32)).toNat (nv' + 1#32)
        have hexp''_eq : exp'' = exp'.set nv'.toNat (q >>> 1#32) := by
          dsimp only [exp'']; rw [cert_zext64_toNat]
        have htmk''_eq : tmk'' = tmk'.set (q.toNat / 2) (nv' + 1#32) := by
          dsimp only [tmk'']; rw [cert_zext64_toNat, hu_eq]
        have hnv1_lt : nv'.toNat + 1 < 2 ^ 32 := by omega
        have hok'' : certExportOk s.core.cur_vars (nv' + 1#32).toNat tmk'' exp'' :=
          cert_export_add_bv hok' hu_lt_cv ht0 hnv_lt_exp
            (by rw [cert_zext64_toNat, hu_eq]; omega) hcv_le hmaxv_lt hnv_lt_cv
        have hsh : q >>> (1 : Nat) = q >>> 1#32 := rfl
        have hnvz : (BitVec.setWidth 64 nv').toNat = nv'.toNat := cert_zext64_toNat nv'
        have hqz : (BitVec.setWidth 64 (q >>> 1#32)).toNat = q.toNat / 2 := by
          rw [cert_zext64_toNat, hu_eq]
        have hm_upd : (Full.FullMem c (certMkState s s.core.tmp exp'' tmk''
            s.scratch.scratch_buf) ⋆ R) m := by
          rw [hexp''_eq, htmk''_eq]; have hm0 := hm; erw [har_eq2, hnvz, hsh, hqz] at hm0; exact hm0
        exact ih (nv' + 1#32, csz' + 1#32, k' + 1#32, tmk'', exp'') m
          (by simp [BitVec.toNat_add]; omega)
          ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega,
           by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega,
           by simp [htmk''_eq, htmk'_len], by simp [hexp''_eq, hexp'_len], hok'',
           fun h => absurd h hcsz_nz, hm_upd⟩
      · exact ih (nv', csz' + 1#32, k' + 1#32, tmk', exp') m_in (by simp [BitVec.toNat_add]; omega)
          ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega, hnv'_mv, hnv'_cv,
           htmk'_len, hexp'_len, hok', fun h => absurd h hcsz_nz, hm_in⟩
    · have hvq255 : s.core.vals[q.toNat]?.getD 0#8 = 255#8 := by
        have hvs_eq : s.core.vals[q_mod.toNat]'hq_mod_lt = s.core.vals[q.toNat] :=
          cert_list_getElem_eq rfl (by rw [hq_ar_eq]) hq_mod_lt (by omega)
        have hns : (0#8 : BitVec 8).slt s.core.vals[q.toNat] = false := by
          rw [← hvs_eq]; dsimp only [q_mod]; c0_bound
        have hne : s.core.vals[q.toNat] ≠ 0#8 := by rw [← hvs_eq]; dsimp only [q_mod]; c0_bound
        have hdom := hinv.2.1.vals_domain q.toNat hq_lt
        rw [List.getElem?_eq_getElem (by omega : q.toNat < s.core.vals.length)] at hdom ⊢
        exact cert_i8_dom_255_bv8 _ hdom hns hne
      have hneg_q := cert_lvl0_false_entails hinv.2.1 hinv.2.2.2.2.2.1 hq_lt hvq255
      exact ih (nv', csz', k' + 1#32, tmk', exp') m_in (by simp [BitVec.toNat_add]; omega)
        ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega, hnv'_mv, hnv'_cv,
         htmk'_len, hexp'_len, hok', fun h0 p hp => by
           have hk1 : (k' + 1#32).toNat = k'.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hk1] at hp; by_cases hpk : p = k'.toNat
           · subst hpk; dsimp only; intro _
             rw [show clits[k'.toNat]?.getD 0 = q.toNat by simp [hq_cl]]; exact hneg_q
           · exact hzero' h0 p (by omega), hm_in⟩
    · have hqu : q.toNat = unit.toNat := by rw [← hq_ar_eq]; exact congrArg BitVec.toNat hc
      exact ih (nv', csz', k' + 1#32, tmk', exp') m_in (by simp [BitVec.toNat_add]; omega)
        ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega, hnv'_mv, hnv'_cv,
         htmk'_len, hexp'_len, hok', fun h0 p hp => by
           have hk1 : (k' + 1#32).toNat = k'.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hk1] at hp; by_cases hpk : p = k'.toNat
           · subst hpk; dsimp only; rw [show clits[k'.toNat]?.getD 0 = q.toNat by simp [hq_cl], hqu]
             intro hne; exact absurd rfl hne
           · exact hzero' h0 p (by omega), hm_in⟩
  · have hk_eq : k'.toNat = lsz.toNat := by c0_bound
    refine hB3 (nv', ab, false, csz', k', tmk', exp', m_in) m_in
      ⟨rfl, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok', fun _ _ hc0 => by
         refine cert_lvl0_clause_unit_entails hcl_ent fun r hr hrnu => ?_
         rcases List.mem_iff_getElem.mp hr with ⟨p, hplen, hpeq⟩
         have h1 := hzero' hc0 p (by rw [hk_eq, ← hcl_len]; exact hplen)
         rw [cert_getElemD hplen, hpeq] at h1; exact h1 hrnu, hm_in⟩

theorem cert_loop1_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (Js : Cont [i32, .bool, .bool, i32]) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (unit side_off side_cnt side_mask mv_sw max_csz : BitVec 32) (m : Mem 64)
    (hmv_toNat : mv_sw.toNat = k6MaxV c.scratch_cap) (hinv : FullDenseInvW c F0 F_cur s)
    (htmk : TmkZero s) (hcap : 16384 ≤ c.scratch_cap) (hmaxv_lt : c.max_vars < 2 ^ 32)
    (hcnt : side_cnt.toNat ≤ 2001) (hoff_cnt : side_off.toNat + side_cnt.toNat ≤ 4002)
    (hmask : side_mask = 4002#32 ∨ side_mask = 4066#32)
    (hent : ∀ i < side_cnt.toNat,
      FullBveEntryOkW F_cur s unit.toNat (s.scratch.scratch_buf[side_off.toNat + i]?.getD 0#32))
    (hm : (Full.FullMem c s ⋆ R) m)
    (hB : ∀ bst : BitVec 32 × Bool × Bool × BitVec 32 × List (BitVec 32) × List (BitVec 32),
      ∀ m'' : Mem 64,
      (match bst with
       | (nv, de, _ab, _, tmk, exp) => certL1Inv c s R (k6MaxV c.scratch_cap) nv tmk exp m'' ∧
         (de = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))) →
      Js (match bst with | (nv, de, ab, idx, _, _) => (nv, de, ab, idx, ())) m'') :
    wp Γ Q X (certLoop1Expr Js c.hdr c.pScratchBuf c.pArena c.pVals c.pTarjanMark c.pWsort
      unit side_off side_cnt side_mask mv_sw max_csz) m := by
  let mv_nat := k6MaxV c.scratch_cap
  have hmv_le : mv_nat ≤ 8192 := by
    by_cases hlt : c.scratch_cap < k6MinScr
    · have : mv_nat = 0 := by simp [mv_nat, k6MaxV, hlt]
      omega
    · exact (k6MaxV_bounds (Nat.not_lt.mp hlt)).2.1
  have hbuf_len := hinv.1.scratch_ok.scratch_buf_len; have hcv_le := hinv.1.core_ok.cur_vars_le
  have har_le := hinv.1.core_ok.arena_len_le; have har_arr := hinv.1.core_ok.arena_len_arr
  have har_cap := c.harena; unfold dimacsBound at har_cap
  unfold certLoop1Expr
  refine wp_while_state
    (α := BitVec 32 × Bool × BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun (nv, ab, idx, _, _) => (nv, ab, idx, ()))
    (fun (_, _, idx, _, _) => side_cnt.toNat - idx.toNat)
    (fun (nv, _ab, idx, tmk, exp) m' =>
      idx.toNat ≤ side_cnt.toNat ∧ certL1Inv c s R mv_nat nv tmk exp m')
    (fun L1 hL1 => by
      c0_hsteps; exact hL1 (0#32, false, 0#32, s.scratch.tarjan_mark, s.scratch.wsort) m
        ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, hinv.1.scratch_ok.tarjan_mark_len,
         hinv.1.scratch_ok.wsort_len, cert_export_zero htmk, hm⟩)
    (fun L1 ⟨nv, ab, idx, tmk, exp⟩ m'
      ⟨hidx_le, hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩ ih => ?_)
  c0_hsplit
  · have hidx_lt : idx.toNat < side_cnt.toNat := by c0_bound
    c0_hsteps_nogrp
    · exact hB (nv, false, ab, idx, tmk, exp) m'
        ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩, fun h => absurd h (by decide)⟩
    · refine wp_join_state (ts := [i32, .bool, .bool])
        (α := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32) × Mem 64)
        (fun (nv', ab', _, _, _) => (nv', false, ab', ()))
        (fun (nv', _ab', tmk', exp', m_n) m_in =>
          m_in = m_n ∧ certL1Inv c s R mv_nat nv' tmk' exp' m_n) ?_ ?_
      · rintro J_next ⟨nv', ab', tmk', exp', m_n⟩ m_in ⟨hm_eq, hrest⟩
        rw [hm_eq]; c0_hsteps; exact ih (nv', ab', idx + 1#32, tmk', exp') m_n
          (by simp [BitVec.toNat_add]; omega) ⟨by simp [BitVec.toNat_add]; omega, hrest⟩
      · intro J_next hJnext
        have hmask_idx_lt : (BitVec.zeroExtend 64 (side_mask + (idx >>> 5#32))).toNat <
            s.scratch.scratch_buf.length := by
          have hshr := cert_shr5_toNat idx
          have hm_lt : side_mask.toNat ≤ 4066 := by rcases hmask with rfl | rfl <;> decide
          rw [cert_zext64_toNat, BitVec.toNat_add, hshr]; omega
        c0_hsteps_nogrp
        · have hw_idx_eq : (side_off + idx).toNat = side_off.toNat + idx.toNat := by
            simp [BitVec.toNat_add]; omega
          have hw_idx_lt : (BitVec.zeroExtend 64 (side_off + idx)).toNat <
              s.scratch.scratch_buf.length := by rw [cert_zext64_toNat, hw_idx_eq]; omega
          have hw_idx_lt' : (side_off + idx).toNat < s.scratch.scratch_buf.length := by
            rw [← cert_zext64_toNat]; exact hw_idx_lt
          have hwe : FullBveEntryOkW F_cur s unit.toNat
              (s.scratch.scratch_buf[(side_off + idx).toNat]'hw_idx_lt') := by
            rw [← cert_getElemD hw_idx_lt' 0#32, hw_idx_eq]; exact hent idx.toNat hidx_lt
          c0_hsteps_nogrp
          refine wp_join_state (ts := [i32, .bool, .bool])
            (α := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32) × Mem 64)
            (fun (nv', ab', _, _, _) => (nv', false, ab', ()))
            (fun (nv', _ab', tmk', exp', m_n) m_in =>
              m_in = m_n ∧ certL1Inv c s R mv_nat nv' tmk' exp' m_n) ?_ ?_
          · rintro J_m ⟨nv', ab', tmk', exp', m_n⟩ m_in ⟨hm_eq, hrest⟩
            rw [hm_eq]; c0_hsteps; exact hJnext (nv', ab', tmk', exp', m_n) m_n ⟨rfl, hrest⟩
          · intro J_m hJm; c0_hsteps_nogrp
            · let w := s.scratch.scratch_buf[(side_off + idx).toNat]'hw_idx_lt'
              have hbit : w &&& 2147483648#32 ≠ 0#32 := by c0_bound
              dsimp only [FullBveEntryOkW] at hwe
              rw [ite_eq_left hbit] at hwe; rcases hwe with ⟨hot_lt, hot_ent⟩
              let ot := w &&& 2147483647#32
              have hot_lt' : ot.toNat < 2 * s.core.cur_vars := hot_lt
              have hscr_ot_eq : (certMkState s s.core.tmp exp tmk
                  s.scratch.scratch_buf).scratch.scratch_buf[
                  (BitVec.zeroExtend 64 (side_off + idx)).toNat] = w :=
                cert_list_getElem_eq (certMkState_buf s s.core.tmp exp tmk s.scratch.scratch_buf)
                  (cert_zext64_toNat _) (by rw [certMkState_buf]; exact hw_idx_lt) hw_idx_lt'
              have hot_len : (BitVec.zeroExtend 64 ((certMkState s s.core.tmp exp tmk
                  s.scratch.scratch_buf).scratch.scratch_buf[(BitVec.zeroExtend 64
                    (side_off + idx)).toNat] &&& 2147483647#32)).toNat <
                  (certMkState s s.core.tmp exp tmk s.scratch.scratch_buf).core.vals.length := by
                have := hinv.1.core_ok.vals_len
                rw [certMkState_vals, hscr_ot_eq, cert_zext64_toNat]
                change ot.toNat < s.core.vals.length; omega
              c0_hsteps_nogrp
              · have hu' : ot.toNat < s.core.vals.length := by
                  have := hinv.1.core_ok.vals_len; omega
                have hvo255 : s.core.vals[ot.toNat]?.getD 0#8 = 255#8 := by
                  have hslt : s.core.vals[ot.toNat].slt 0#8 = true := by
                    dsimp only [ot, w]; c0_bound
                  have hdom := hinv.2.1.vals_domain ot.toNat hot_lt
                  rw [List.getElem?_eq_getElem hu'] at hdom ⊢
                  exact cert_i8_slt0_eq_255 _ hdom hslt
                have hneg := cert_lvl0_false_entails hinv.2.1 hinv.2.2.2.2.2.1 hot_lt hvo255
                exact hB (nv, true, ab, idx, tmk, exp) m'
                  ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩,
                   fun _ => cert_entails_resolve_unit hot_ent hneg⟩
              · have hu_eq := cert_shr1_toNat ot
                have hu_lt_cv : ot.toNat / 2 < s.core.cur_vars := by omega
                have hu_lt_tmk : (BitVec.zeroExtend 64 (ot >>> 1#32)).toNat < tmk.length := by
                  rw [cert_zext64_toNat, hu_eq]; omega
                have hu_lt_tmk_mk : (BitVec.zeroExtend 64 (((certMkState s s.core.tmp exp tmk
                    s.scratch.scratch_buf).scratch.scratch_buf[(BitVec.zeroExtend 64
                      (side_off + idx)).toNat] &&& 2147483647#32) >>> 1#32)).toNat <
                    (certMkState s s.core.tmp exp tmk
                      s.scratch.scratch_buf).scratch.tarjan_mark.length := by
                  rw [certMkState_tmk, hscr_ot_eq]; exact hu_lt_tmk
                c0_hsteps_nogrp
                refine wp_join_state (ts := [i32, .bool])
                  (α := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32) × Mem 64)
                  (fun (nv', ab', _, _, _) => (nv', ab', ()))
                  (fun (nv', _ab', tmk', exp', m_n) m_in =>
                    m_in = m_n ∧ certL1Inv c s R mv_nat nv' tmk' exp' m_n) ?_ ?_
                · rintro J_b ⟨nv', ab', tmk', exp', m_n⟩ m_in ⟨hm_eq, hrest⟩
                  rw [hm_eq]; c0_hsteps; exact hJm (nv', ab', tmk', exp', m_n) m_n ⟨rfl, hrest⟩
                · intro J_b hJb; c0_hsteps
                  · exact hB (nv, false, true, idx, tmk, exp) m'
                      ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩,
                       fun h => absurd h (by decide)⟩
                  · exact hB (nv, false, true, idx, tmk, exp) m'
                      ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩,
                       fun h => absurd h (by decide)⟩
                  · have hnv_lt_mv : nv.toNat < mv_nat := by c0_bound
                    have hnv_lt_cv : nv.toNat < s.core.cur_vars := by
                      change ¬s.core.cur_vars % 2 ^ 64 ≤ nv.toNat at hc
                      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
                    have hnv_lt_exp : (BitVec.zeroExtend 64 nv).toNat < exp.length := by
                      rw [cert_zext64_toNat]; omega
                    have ht0 : tmk[ot.toNat / 2]?.getD 0#32 = 0#32 := by
                      have heq0 : tmk[ot.toNat / 2] = 0#32 := by dsimp only [ot, w]; c0_bound
                      rw [cert_getElemD (by omega : ot.toNat / 2 < tmk.length)]; exact heq0
                    c0_hsteps
                    let exp' := exp.set (BitVec.zeroExtend 64 nv).toNat (ot >>> 1#32)
                    let tmk' := tmk.set (BitVec.zeroExtend 64 (ot >>> 1#32)).toNat (nv + 1#32)
                    have hexp'_eq : exp' = exp.set nv.toNat (ot >>> 1#32) := by
                      dsimp only [exp']; rw [cert_zext64_toNat]
                    have htmk'_eq : tmk' = tmk.set (ot.toNat / 2) (nv + 1#32) := by
                      dsimp only [tmk']; rw [cert_zext64_toNat, hu_eq]
                    have hnv1_lt : nv.toNat + 1 < 2 ^ 32 := by omega
                    have hok' := cert_export_add_bv hok hu_lt_cv ht0 hnv_lt_exp
                      (by rw [cert_zext64_toNat, hu_eq]; omega) hcv_le hmaxv_lt hnv_lt_cv
                    have hnv1_eq : (nv + 1#32).toNat = nv.toNat + 1 := by
                      simp [BitVec.toNat_add, Nat.mod_eq_of_lt hnv1_lt]
                    have hsh : (w &&& 2147483647#32) >>> (1 : Nat) = ot >>> 1#32 := rfl
                    have hnvz : (BitVec.setWidth 64 nv).toNat = nv.toNat := cert_zext64_toNat nv
                    have hotz : (BitVec.setWidth 64 (ot >>> 1#32)).toNat = ot.toNat / 2 := by
                      rw [cert_zext64_toNat, hu_eq]
                    have hm_upd : (Full.FullMem c (certMkState s s.core.tmp exp' tmk'
                        s.scratch.scratch_buf) ⋆ R) m := by
                      rw [hexp'_eq, htmk'_eq]; have hm0 := hm
                      erw [hscr_ot_eq, hnvz, hsh, hotz] at hm0; exact hm0
                    exact hJb (nv + 1#32, ab, tmk', exp', m) m
                      ⟨rfl, by rw [hnv1_eq]; omega, by rw [hnv1_eq]; omega,
                       by simp [htmk'_eq, htmk_len], by simp [hexp'_eq, hexp_len], hok', hm_upd⟩
                  · exact hJb (nv, ab, tmk, exp, m') m'
                      ⟨rfl, hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩
                  · exact hJb (nv, ab, tmk, exp, m') m'
                      ⟨rfl, hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩
            · let w := s.scratch.scratch_buf[(side_off + idx).toNat]'hw_idx_lt'
              have h1 : w &&& 2147483648#32 = 0#32 := by dsimp only [w]; c0_bound
              dsimp only [FullBveEntryOkW] at hwe
              rw [ite_eq_right (fun h => absurd h1 h)] at hwe; rcases hwe with ⟨hwref, hwgarb⟩
              have href_wf := hinv.2.1.arena.refs_wf w.toNat hwref
              have hw3 := href_wf.1; have hn1 := href_wf.2.2.1; have hn2 := href_wf.2.2.2.1
              have h2 : w.toNat < 2 ^ 32 := w.isLt
              have hw_idx_eq : (BitVec.zeroExtend 64 w + 2#64).toNat = w.toNat + 2 := by
                rw [BitVec.toNat_add, cert_zext64_toNat,
                  show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
              have hw_len : (BitVec.zeroExtend 64 w + 2#64).toNat < s.core.arena.length := by
                rw [hw_idx_eq]; omega
              c0_hsteps_nogrp
              have hwa2 : w.toNat + 2 < s.core.arena.length := by omega
              let lsz := s.core.arena[w.toNat + 2]'hwa2
              have hlsz_eq : lsz.toNat = fullArenaClauseSizeCore s.core w.toNat := by
                simp [lsz, fullArenaClauseSizeCore, List.getElem?_eq_getElem hwa2]
              have hlsz_bound : w.toNat + 3 + lsz.toNat ≤ s.core.arena.length := by
                rw [hlsz_eq]; omega
              have hlsz_lt_29 : lsz.toNat < 2 ^ 29 := by omega
              refine wp_join_state (ts := [i32, .bool, .bool, i32, i32])
                (α := BitVec 32 × Bool × Bool × BitVec 32 × BitVec 32 ×
                  List (BitVec 32) × List (BitVec 32) × Mem 64)
                (fun (nv', ab', sat', csz', k', _, _, _) => (nv', ab', sat', csz', k', ()))
                (fun (nv', ab', sat', csz', _, tmk', exp', m_n) m_in => m_in = m_n ∧
                  certL1Inv c s R mv_nat nv' tmk' exp' m_n ∧
                  (ab' = false → sat' = false → csz' = 0#32 →
                    (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))) ?_ ?_
              · rintro B3 ⟨nv', ab', sat', csz', _, tmk', exp', m_n⟩ m_in ⟨hm_eq, hrest, hent'⟩
                rw [hm_eq]; c0_hsteps
                · exact hB (nv', false, ab', idx, tmk', exp') m_n
                    ⟨hrest, fun h => absurd h (by decide)⟩
                · exact hJm (nv', ab', tmk', exp', m_n) m_n ⟨rfl, hrest⟩
                · exact hB (nv', true, ab', idx, tmk', exp') m_n
                    ⟨hrest, fun _ => hent' (by c0_bound) (by c0_bound) (by c0_bound)⟩
                · exact hB (nv', false, true, idx, tmk', exp') m_n
                    ⟨hrest, fun h => absurd h (by decide)⟩
                · exact hJm (nv', ab', tmk', exp', m_n) m_n ⟨rfl, hrest⟩
              · intro Js4 hB3
                have hgw : (certMkState s s.core.tmp exp tmk
                    s.scratch.scratch_buf).scratch.scratch_buf[
                    (BitVec.setWidth 64 (side_off + idx)).toNat] = w :=
                  cert_list_getElem_eq (certMkState_buf ..) (cert_zext64_toNat _)
                    (by rw [certMkState_buf]; exact hw_idx_lt) hw_idx_lt'
                have hgl : (certMkState s s.core.tmp exp tmk
                    s.scratch.scratch_buf).core.arena[(BitVec.setWidth 64
                      ((certMkState s s.core.tmp exp tmk
                        s.scratch.scratch_buf).scratch.scratch_buf[(BitVec.setWidth 64
                          (side_off + idx)).toNat]) + 2).toNat] = lsz :=
                  cert_list_getElem_eq (certMkState_arena ..) (by erw [hgw, hw_idx_eq])
                    (by rw [certMkState_arena]; erw [hgw, hw_idx_eq]; omega) hwa2
                dsimp -zeta only; erw [hgl, hgw]
                exact cert_loop1_large_wp Γ Q X Js4 c F0 F_cur s R exp tmk w lsz
                  unit nv mv_sw ab m' hinv hexp_len htmk_len hmaxv_lt
                  (by rw [hmv_toNat]; exact hnv_mv) hnv_cv hok hwref hwgarb hlsz_eq
                  hlsz_bound hlsz_lt_29 hm'
                  (fun bst m_in ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
                    hB3 bst m_in
                      ⟨h1, ⟨by rw [hmv_toNat] at h2; exact h2, h3, h4, h5, h6, h8⟩, h7⟩)
        · exact hJnext (nv, ab, tmk, exp, m') m'
            ⟨rfl, hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩
  · exact hB (nv, false, ab, idx, tmk, exp) m'
      ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩, fun h => absurd h (by decide)⟩

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
