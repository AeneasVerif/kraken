/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12C
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofLearn
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
public import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof0
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullKittenLemmas1
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 12 Bundle C — `Func.wp` Proofs (`FullFidelityStep12CProof`)

Certifies all `7` Step-12C patch functions (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`, `XPost`-polymorphic):
1. Re-exports `FullM7V2Robust` proofs (`full_watch_pop_c0_wp`, `full_add_clause_wp`,
   `full_sweep_copy_wp`, `full_reduce_purge_c0_wp`).
2. `full_learn_clause_m6_step12c_wp` (`FullFidelityStep10.step10LearnClauseM6Spec` verbatim):
   3-step OOM retry ladder (`full_wstack_defrag`, `full_reduce_m6(h, true)`,
   `full_reduce_purge_c0(h)`) threading `M6HdrExt` cleanly.
3. `full_viv_sift_counts_m6_wp` (`fullVivSiftCountsM6Spec`) and
   `full_viv_sort_counts_m6_step12c_wp` (`FullM6VivBackbone.fullVivSortCountsM6Spec` verbatim):
   $O(K \log K)$ in-place heapsort permutation over `tmp_lits[0 ..< sz)`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12C

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7V2Robust
open LeanQbe.T.Examples.Kissat.FullFidelityStep10
open Kraken.Bedrock2.Test

/-! ## 1. `P1-9b` Specification & $O(K \log K)$ Vivify Heapsort Proofs -/

/-- `full_viv_sift_counts_m6(h, start, n)`: sifts element `start` down within `tmp_lits[0 ..< n)`
in place, preserving `tmp_lits.take sz` as a permutation (`n ≤ sz ≤ max_vars`). -/
def fullVivSiftCountsM6Spec : Spec [i64, i64, i64] [] := fun (h, start, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (sz : Nat),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ sz ∧ sz ≤ c.max_vars ∧
    start.toNat < n.toNat ∧
    (∀ k < sz, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m', tmp'.length = c.max_vars →
      (tmp'.take sz).Perm (s.core.tmp.take sz) →
      (∀ k, sz ≤ k → k < c.max_vars → tmp'[k]? = s.core.tmp[k]?) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

theorem fullVivSiftCountsM6Spec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : fullVivSiftCountsM6Spec xs m Q X) :
    fullVivSiftCountsM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

section VivSortProof

open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics

@[local c0_load] private theorem s12c_load_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 0#64) = some s.core.tmp[0] :=
  FullArenaTactics.load_full_tmp (i := 0) hi hm

@[local c0_store] private theorem s12c_store_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) :=
  FullArenaTactics.store_full_tmp (i := 0) v hi hm

private theorem s12c_viv_lt_of_perm {xs orig : List (BitVec 32)} {sz B : Nat}
    (hxs : sz ≤ xs.length) (hperm : (xs.take sz).Perm (orig.take sz))
    (hlt : ∀ idx < sz, (orig[idx]?.getD 0#32).toNat < B) :
    ∀ k < sz, (xs[k]?.getD 0#32).toNat < B := fun k hk => by
  have hm : xs[k]'(by omega) ∈ orig.take sz := hperm.mem_iff.mp (by
    rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩)
  obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hm
  have hidx_sz : idx < sz := by rw [List.length_take] at hidx; omega
  have hidx_orig : idx < orig.length :=
    Nat.lt_of_lt_of_le hidx (by rw [List.length_take]; exact Nat.min_le_right _ _)
  have hget := hlt idx hidx_sz
  rw [List.getElem_take] at heq
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq]
  rwa [List.getElem?_eq_getElem hidx_orig, Option.getD_some] at hget

private theorem s12c_viv_swap_perm {xs orig : List (BitVec 32)} {sz a b : Nat}
    (hlen : xs.length = orig.length) (hsz : sz ≤ orig.length)
    (ha : a < sz) (hb : b < sz) (hp : (xs.take sz).Perm (orig.take sz)) :
    (((xs.set a (xs[b]'(by omega))).set b (xs[a]'(by omega))).take sz).Perm
      (orig.take sz) := by
  have hta : a < (xs.take sz).length := by simp [List.length_take, hlen]; omega
  have htb : b < (xs.take sz).length := by simp [List.length_take, hlen]; omega
  rw [List.take_set, List.take_set]
  have e1 : xs[b]'(by omega) = (xs.take sz)[b]'htb := by simp [List.getElem_take]
  have e2 : xs[a]'(by omega) = (xs.take sz)[a]'hta := by simp [List.getElem_take]
  rw [e1, e2]
  exact (list_swap_perm _ hta htb).trans hp

private theorem s12c_viv_swap_out {xs orig : List (BitVec 32)} {sz a b : Nat}
    (hsz : sz ≤ xs.length) (ha : a < sz) (hb : b < sz)
    (hout : ∀ k, sz ≤ k → k < orig.length → xs[k]? = orig[k]?) :
    ∀ k, sz ≤ k → k < orig.length →
      ((xs.set a (xs[b]'(by omega))).set b (xs[a]'(by omega)))[k]? = orig[k]? := by
  intro k hk1 hk2
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  exact hout k hk1 hk2

/-- `full_viv_sift_counts_m6` satisfies `fullVivSiftCountsM6Spec`. -/
theorem full_viv_sift_counts_m6_wp (Γ : Env) :
    ∀ a m Q X, fullVivSiftCountsM6Spec a m Q X →
      Func.wp Γ fidStep12CVivSiftCountsM6Fn.body a m Q X := by
  rintro ⟨h, start, n, ⟨⟩⟩ m Q X ⟨c, s, R, sz, rfl, hlen, hn_le, hsz_le, hst_lt, hlt_orig, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htl0 := hlen.core_ok.tmp_len_arr; have htrl0 := hlen.scratch_ok.tarjan_reach_len
  unfold Func.wp fidStep12CVivSiftCountsM6Fn full_viv_sift_counts_m6_body
  dsimp only
  fvt_steps
  refine wp_loop_inv (ts := [i64])
    (fun (r, ()) m1 => ∃ tmp1 : List (BitVec 32),
      r.toNat < n.toNat ∧ tmp1.length = c.max_vars ∧
      (tmp1.take sz).Perm (s.core.tmp.take sz) ∧
      (∀ k, sz ≤ k → k < c.max_vars → tmp1[k]? = s.core.tmp[k]?) ∧
      (FullMem c { s with core := { s.core with tmp := tmp1 } } ⋆ R) m1)
    (fun (r, ()) _ => n.toNat - r.toNat)
    (fun J_lp hJ_lp => by
      fvt_steps
      exact hJ_lp (start, ()) m ⟨s.core.tmp, hst_lt, htl0, .refl _, fun _ _ _ => rfl, hm0⟩)
    (fun J_lp ⟨r, ⟨⟩⟩ m1 ⟨tmp1, hr_lt, htl1, hperm1, hout1, hm1⟩ ih => ?_)
  have hr_bd : 2 * r.toNat + 2 < 2 ^ 64 := by omega
  have hc1_nat : ((r <<< (1 : Nat)) + 1).toNat = 2 * r.toNat + 1 := by bv_omega
  fvt_steps
  · have hc1_lt : 2 * r.toNat + 1 < n.toNat := by bv_omega
    have hc1_tmp : (r <<< (1 : Nat) + 1).toNat < tmp1.length := by rw [hc1_nat]; omega
    have htmp1_lt := s12c_viv_lt_of_perm (by omega) hperm1 hlt_orig
    let wlit0 : BitVec 32 := tmp1[2 * r.toNat + 1]'(by omega)
    have hwlit0_eq : tmp1[(r <<< (1 : Nat) + 1).toNat]'hc1_tmp = wlit0 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hc1_tmp, hc1_nat, List.getElem?_eq_getElem (by omega)])
    have hwlit0_lt : wlit0.toNat < 2 * c.max_vars := by
      have h := htmp1_lt (2 * r.toNat + 1) (by omega)
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
    have hwlit0_tr : ((tmp1[(r <<< (1 : Nat) + 1).toNat]'hc1_tmp).setWidth 64).toNat <
        s.scratch.tarjan_reach.length := by
      rw [hwlit0_eq, bv32_setWidth64_toNat, htrl0]; omega
    fvt_to_group
    refine wp_join_group (ts := [i64, i32, i32])
      (fun (worst, wlit, _wc, ()) m2 =>
        m2 = m1 ∧ r.toNat < worst.toNat ∧ worst.toNat < n.toNat ∧
        tmp1[worst.toNat]? = some wlit ∧ wlit.toNat < 2 * c.max_vars)
      ?_ ?_
    · rintro _ ⟨worst, wlit, wc, ⟨⟩⟩ m2 ⟨rfl, hrw, hwn, hwget, hwlt⟩
      have hr_tmp : r.toNat < tmp1.length := by omega
      let rlit : BitVec 32 := tmp1[r.toNat]'hr_tmp
      have hrlit_lt : rlit.toNat < 2 * c.max_vars := by
        have h := htmp1_lt r.toNat (by omega)
        rwa [List.getElem?_eq_getElem hr_tmp, Option.getD_some] at h
      have hrlit_tr : (rlit.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
        rw [bv32_setWidth64_toNat, htrl0]; omega
      have hworst_tmp : worst.toNat < tmp1.length := by omega
      have hwlit_eq : wlit = tmp1[worst.toNat]'hworst_tmp :=
        Option.some.inj (hwget.symm.trans (List.getElem?_eq_getElem hworst_tmp))
      have hperm_sw := s12c_viv_swap_perm (orig := s.core.tmp) (by omega) (by omega)
        (a := r.toNat) (b := worst.toNat) (by omega) (by omega) hperm1
      have hout_sw := s12c_viv_swap_out (orig := s.core.tmp) (sz := sz) (by rw [htl1]; exact hsz_le)
        (a := r.toNat) (b := worst.toNat) (by omega) (by omega) (by simpa [htl0] using hout1)
      have hstep : ∀ m',
          (FullMem c { s with core := { s.core with
            tmp := (tmp1.set r.toNat wlit).set worst.toNat rlit } } ⋆ R) m' →
          J_lp (worst, ()) m' := fun m' hm' =>
        ih (worst, ()) m' (by dsimp only; omega)
          ⟨(tmp1.set r.toNat wlit).set worst.toNat rlit, hwn, by simp [htl1],
           by simpa only [hwlit_eq] using hperm_sw,
           fun k hk1 hk2 => by
             simpa only [hwlit_eq, htl0] using hout_sw k hk1 (by omega),
           hm'⟩
      fvt_steps
      · exact hstep _ hm
      · exact hstep _ hm
      · exact hQ tmp1 _ htl1 hperm1 hout1 (by assumption)
      · exact hQ tmp1 _ htl1 hperm1 hout1 (by assumption)
    · intro J2 hJ2
      have hc2_nat : (((r <<< (1 : Nat)) + 1) + 1).toNat = 2 * r.toNat + 2 := by bv_omega
      fvt_steps
      · have hc2_lt : 2 * r.toNat + 2 < n.toNat := by bv_omega
        have hc2_tmp : (((r <<< (1 : Nat)) + 1) + 1).toNat < tmp1.length := by
          rw [hc2_nat]; omega
        let lit2 : BitVec 32 := tmp1[2 * r.toNat + 2]'(by omega)
        have hlit2_eq : tmp1[(((r <<< (1 : Nat)) + 1) + 1).toNat]'hc2_tmp = lit2 :=
          Option.some.inj (by
            rw [← List.getElem?_eq_getElem hc2_tmp, hc2_nat, List.getElem?_eq_getElem (by omega)])
        have hlit2_lt : lit2.toNat < 2 * c.max_vars := by
          have h := htmp1_lt (2 * r.toNat + 2) (by omega)
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
        have hlit2_tr : ((tmp1[(((r <<< (1 : Nat)) + 1) + 1).toNat]'hc2_tmp).setWidth 64).toNat <
            s.scratch.tarjan_reach.length := by
          rw [hlit2_eq, bv32_setWidth64_toNat, htrl0]; omega
        fvt_steps
        · exact hJ2 _ m1 ⟨rfl, by bv_omega, by bv_omega,
            List.getElem?_eq_getElem (by bv_omega), by
              have h := htmp1_lt (r <<< (1 : Nat) + 1 + 1).toNat (by bv_omega)
              rwa [List.getElem?_eq_getElem (by bv_omega), Option.getD_some] at h⟩
        · exact hJ2 _ m1 ⟨rfl, by bv_omega, by bv_omega,
            List.getElem?_eq_getElem (by bv_omega), by
              have h := htmp1_lt (r <<< (1 : Nat) + 1 + 1).toNat (by bv_omega)
              rwa [List.getElem?_eq_getElem (by bv_omega), Option.getD_some] at h⟩
        · exact hJ2 _ m1 ⟨rfl, by bv_omega, by bv_omega,
            List.getElem?_eq_getElem (by bv_omega), by
              have h := htmp1_lt (r <<< (1 : Nat) + 1).toNat (by bv_omega)
              rwa [List.getElem?_eq_getElem (by bv_omega), Option.getD_some] at h⟩
        · exact hJ2 _ m1 ⟨rfl, by bv_omega, by bv_omega,
            List.getElem?_eq_getElem (by bv_omega), by
              have h := htmp1_lt (r <<< (1 : Nat) + 1).toNat (by bv_omega)
              rwa [List.getElem?_eq_getElem (by bv_omega), Option.getD_some] at h⟩
      · exact hJ2 _ m1 ⟨rfl, by bv_omega, by bv_omega,
          List.getElem?_eq_getElem (by bv_omega), by
            have h := htmp1_lt (r <<< (1 : Nat) + 1).toNat (by bv_omega)
            rwa [List.getElem?_eq_getElem (by bv_omega), Option.getD_some] at h⟩
  · exact hQ tmp1 m1 htl1 hperm1 hout1 hm1

/-- `FullFidelityStep12C.full_viv_sort_counts_m6` satisfies
`FullM6VivBackbone.fullVivSortCountsM6Spec` verbatim ($O(K \log K)$ heapsort permutation). -/
theorem full_viv_sort_counts_m6_step12c_wp (Γ : Env)
    (hSift : ∀ a m Q X, fullVivSiftCountsM6Spec a m Q X →
      Γ "full_viv_sift_counts_m6" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullVivSortCountsM6Spec a m Q X →
      Func.wp Γ fidStep12CVivSortCountsM6Fn.body a m Q X := by
  rintro ⟨h, sz, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hsz_le, hlt_orig, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htl0 := hlen.core_ok.tmp_len_arr
  unfold Func.wp fidStep12CVivSortCountsM6Fn full_viv_sort_counts_m6_body
  dsimp only
  fvt_steps
  · exact hQ s.core.tmp m htl0 (.refl _) (fun _ _ _ => rfl) hm0
  · have hsz_gt1 : 1 < sz.toNat := by c0_bound
    have hn_eq : (sz.setWidth 64).toNat = sz.toNat := bv32_setWidth64_toNat sz
    have hshr_eq : ((sz.setWidth 64) >>> (1 : Nat)).toNat = sz.toNat / 2 := by bv_omega
    fvt_to_group
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) m1 => i.toNat ≤ sz.toNat ∧
        ∃ tmp1 : List (BitVec 32), tmp1.length = c.max_vars ∧
          (tmp1.take sz.toNat).Perm (s.core.tmp.take sz.toNat) ∧
          (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp1[k]? = s.core.tmp[k]?) ∧
          (FullMem c { s with core := { s.core with tmp := tmp1 } } ⋆ R) m1)
      (fun (i, ()) _ => i.toNat)
      (fun J1 hJ1 => by
        fvt_steps
        exact hJ1 _ m ⟨by bv_omega, s.core.tmp, htl0, .refl _, fun _ _ _ => rfl, hm0⟩)
      (fun J1 ⟨i, ⟨⟩⟩ m1 ⟨hi_le, tmp1, htl1, hperm1, hout1, hm1⟩ ih1 => ?_)
    fvt_steps
    · have hi_pos : 0 < i.toNat := by c0_bound
      have hi1_nat : (i - 1#64).toNat = i.toNat - 1 := by bv_omega
      c0_call hSift
      refine ⟨c, { s with core := { s.core with tmp := tmp1 } }, R, sz.toNat, rfl,
        ⟨{ hlen.core_ok with tmp_len_arr := htl1 }, hlen.scratch_ok⟩,
        by rw [hn_eq]; exact Nat.le_refl _, hsz_le, by bv_omega,
        s12c_viv_lt_of_perm (by rw [htl1]; exact hsz_le) hperm1 hlt_orig, hm1,
        fun tmp2 m2 htl2 hperm2 hout2 hm2 => ?_⟩
      exact ih1 (i - 1#64, ()) m2 (by dsimp only; bv_omega)
        ⟨by bv_omega, tmp2, htl2, hperm2.trans hperm1,
         fun k hk1 hk2 => (hout2 k hk1 hk2).trans (hout1 k hk1 hk2), hm2⟩
    · fvt_to_group
      refine wp_loop_inv (ts := [i64])
        (fun (mv, ()) m2 => 1 ≤ mv.toNat ∧ mv.toNat ≤ sz.toNat ∧
          ∃ tmp2 : List (BitVec 32), tmp2.length = c.max_vars ∧
            (tmp2.take sz.toNat).Perm (s.core.tmp.take sz.toNat) ∧
            (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp2[k]? = s.core.tmp[k]?) ∧
            (FullMem c { s with core := { s.core with tmp := tmp2 } } ⋆ R) m2)
        (fun (mv, ()) _ => mv.toNat)
        (fun J2 hJ2 => by
          fvt_steps
          exact hJ2 _ m1 ⟨by rw [hn_eq]; omega, by rw [hn_eq]; exact Nat.le_refl _,
            tmp1, htl1, hperm1, hout1, hm1⟩)
        (fun J2 ⟨mv, ⟨⟩⟩ m2 ⟨hmv1, hmv_le, tmp2, htl2, hperm2, hout2, hm2⟩ ih2 => ?_)
      fvt_steps
      · have hmv_gt1 : 1 < mv.toNat := by c0_bound
        have hmv1_nat : (mv - 1#64).toNat = mv.toNat - 1 := by bv_omega
        have h0_tmp : (0 : Nat) < tmp2.length := by omega
        have hm_tmp : (mv - 1#64).toNat < tmp2.length := by rw [hmv1_nat]; omega
        let top : BitVec 32 := tmp2[0]'h0_tmp
        let bot : BitVec 32 := tmp2[(mv - 1#64).toNat]'hm_tmp
        have hperm_sw := s12c_viv_swap_perm (orig := s.core.tmp) (by omega) (by omega)
          (a := 0) (b := (mv - 1#64).toNat) (by omega) (by rw [hmv1_nat]; omega) hperm2
        have hout_sw := s12c_viv_swap_out (orig := s.core.tmp) (sz := sz.toNat)
          (by rw [htl2]; exact hsz_le) (a := 0) (b := (mv - 1#64).toNat) (by omega)
          (by rw [hmv1_nat]; omega) (by simpa [htl0] using hout2)
        fvt_steps
        c0_call hSift
        let tmp2' := (tmp2.set 0 bot).set (mv - 1#64).toNat top
        refine ⟨c, { s with core := { s.core with tmp := tmp2' } }, R, sz.toNat, rfl,
          ⟨{ hlen.core_ok with tmp_len_arr := by simp [tmp2', htl2] }, hlen.scratch_ok⟩,
          by bv_omega, hsz_le,
          by show (0#64 : BitVec 64).toNat < (mv - 1#64).toNat; bv_omega,
          s12c_viv_lt_of_perm (by simp [tmp2', htl2]; omega) hperm_sw hlt_orig,
          (by assumption :
            (FullMem c { s with core := { s.core with tmp := tmp2' } } ⋆ R) _),
          fun tmp3 m3 htl3 hperm3 hout3 hm3 => ?_⟩
        exact ih2 (mv - 1#64, ()) m3 (by dsimp only; bv_omega)
          ⟨by bv_omega, by bv_omega, tmp3, htl3,
           hperm3.trans hperm_sw,
           fun k hk1 hk2 => (hout3 k hk1 hk2).trans (by
             dsimp only [tmp2', top, bot]
             simpa [htl0] using hout_sw k hk1 (by omega)),
           hm3⟩
      · exact hQ tmp2 m2 htl2 hperm2 hout2 hm2

end VivSortProof

/-! ## 2. `P1-4a` `full_learn_clause_m6` with 3-Step OOM Recovery Ladder -/

section LearnStep12CProof

open FullLearnAnaTactics FullLearnAnaHelpers
open scoped FullArenaTactics FullLearnAnaTactics

private def S12cTpi (t0 t : List (BitVec 32)) (n : Nat) : Prop :=
  t.length = t0.length ∧ t[0]? = t0[0]? ∧ (t.take n).Perm (t0.take n)

private def s12cLv (lvl : List (BitVec 32)) (x : BitVec 32) : Nat :=
  (lvl[x.toNat / 2]?.getD 0#32).toNat

private theorem s12cTpi_refl (t0 : List (BitVec 32)) (n : Nat) : S12cTpi t0 t0 n :=
  ⟨rfl, rfl, .refl _⟩

private theorem s12cTpi_swap {t0 t : List (BitVec 32)} {n a b : Nat} (h : S12cTpi t0 t n)
    (ha1 : 1 ≤ a) (ha : a < n) (hb1 : 1 ≤ b) (hb : b < n) (hn : n ≤ t0.length)
    (hat : a < t.length) (hbt : b < t.length) :
    S12cTpi t0 ((t.set a (t[b]'hbt)).set b (t[a]'hat)) n := by
  obtain ⟨hl, h0, hp⟩ := h
  refine ⟨by simp [hl], ?_, ?_⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), h0]
  · have hta : a < (t.take n).length := by simp; omega
    have htb : b < (t.take n).length := by simp; omega
    rw [List.take_set, List.take_set]
    have e1 : t[b]'hbt = (t.take n)[b]'htb := by simp [List.getElem_take]
    have e2 : t[a]'hat = (t.take n)[a]'hta := by simp [List.getElem_take]
    rw [e1, e2]
    exact (list_swap_perm _ hta htb).trans hp

private theorem s12cTpi_lt {t0 t : List (BitVec 32)} {n B : Nat} (h : S12cTpi t0 t n)
    (hn : n ≤ t0.length) (hlt : ∀ k < n, (t0[k]?.getD 0#32).toNat < B) :
    ∀ k < n, (t[k]?.getD 0#32).toNat < B := fun k hk => by
  obtain ⟨hl, _, hperm⟩ := h
  have hm : t[k]'(by omega) ∈ t0.take n := hperm.mem_iff.mp (by
    rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩)
  obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hm
  have hidx_n : idx < n := by rw [List.length_take] at hidx; omega
  have hget := hlt idx hidx_n
  rw [List.getElem_take] at heq
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq]
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget

private theorem s12c_tmp_shift_hole {xs orig : List (BitVec 32)} {sz j : Nat}
    {x prev : BitVec 32} (hlen : xs.length = orig.length) (hsz : sz ≤ orig.length)
    (hj0 : 0 < j) (hjsz : j < sz) (hprev : xs[j - 1]? = some prev)
    (hperm : ((xs.set j x).take sz).Perm (orig.take sz)) :
    (((xs.set j prev).set (j - 1) x).take sz).Perm (orig.take sz) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj0)
  rw [Nat.succ_sub_one] at hprev ⊢
  let A := (xs.set (m + 1) x).take sz; let B := ((xs.set (m + 1) prev).set m x).take sz
  have hAl : A.length = sz := by simp [A, List.length_take, hlen]; omega
  let head := A.take m; let tail := A.drop (m + 2)
  have htk : head.length = m := by simp [head, List.length_take, hAl]; omega
  have hsp : ∀ (C : List (BitVec 32)) (a b : BitVec 32), C.length = sz →
      (∀ k < m, C[k]? = A[k]?) → C[m]? = some a → C[m + 1]? = some b →
      (∀ k, m + 2 ≤ k → C[k]? = A[k]?) → C = head ++ a :: b :: tail := by
    intro C a b hCl hk_lt hk_m hk_j hk_gt; refine List.ext_getElem? fun k => ?_
    by_cases hkm : k < m
    · rw [List.getElem?_append_left (by omega), List.getElem?_take]; simp [hkm, hk_lt k hkm]
    · rw [List.getElem?_append_right (by omega), htk]
      by_cases hk0 : k = m
      · subst hk0; simp [hk_m]
      · by_cases hk1 : k = m + 1
        · subst hk1; simp [hk_j]
        · rw [show k - m = (k - (m + 2)) + 2 by omega]
          simp only [List.getElem?_cons_succ, tail, List.getElem?_drop]
          rw [show m + 2 + (k - (m + 2)) = k by omega]; exact hk_gt k (by omega)
  have hA := hsp A prev x hAl (fun _ _ => rfl)
    (by simp only [A, List.getElem?_take, show m < sz by omega, ↓reduceIte,
          List.getElem?_set_ne (by omega : m + 1 ≠ m)]; exact hprev)
    (by simp only [A, List.getElem?_take, hjsz, ↓reduceIte]
        exact List.getElem?_set_self (by omega))
    fun _ _ => rfl
  have hB := hsp B x prev (by simp [B, List.length_take, hlen]; omega)
    (fun k hk => by
      simp only [A, B, List.getElem?_take, List.getElem?_set_ne (by omega : m ≠ k),
        List.getElem?_set_ne (by omega : m + 1 ≠ k)])
    (by simp only [B, List.getElem?_take, show m < sz by omega, ↓reduceIte]
        exact List.getElem?_set_self (by simp; omega))
    (by simp only [B, List.getElem?_take, hjsz, ↓reduceIte,
          List.getElem?_set_ne (by omega : m ≠ m + 1)]
        exact List.getElem?_set_self (by omega))
    fun k hk => by
      simp only [A, B, List.getElem?_take, List.getElem?_set_ne (by omega : m ≠ k),
        List.getElem?_set_ne (by omega : m + 1 ≠ k)]
  have hswap : B.Perm A := by
    rw [hA, hB]; exact List.Perm.append_left head (List.Perm.swap prev x tail)
  exact hswap.trans hperm

private theorem s12c_perm_pos {A B : List (BitVec 32)} {n j : Nat}
    (hp : (A.take n).Perm (B.take n)) (h0 : A[0]? = B[0]?)
    (hnd : ((B.take n).map fun x => x.toNat / 2).Nodup) (hj1 : 1 ≤ j) (hjn : j < n)
    (hnB : n ≤ B.length) : ∃ k, 1 ≤ k ∧ k < n ∧ A[k]? = B[j]? := by
  have hjB : j < B.length := by omega
  have hmem : B[j] ∈ A.take n := hp.mem_iff.mpr (List.mem_iff_getElem.mpr
    ⟨j, by simp; omega, by simp [List.getElem_take]⟩)
  obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
  simp only [List.length_take] at hk
  rw [List.getElem_take] at hkeq
  refine ⟨k, ?_, by omega, by
    rw [List.getElem?_eq_getElem (by omega), hkeq, List.getElem?_eq_getElem hjB]⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exfalso
    have hB0 : 0 < B.length := by omega
    have hA0 : 0 < A.length := by omega
    have hbeq : B[0] = B[j] := by
      rw [List.getElem?_eq_getElem hA0, List.getElem?_eq_getElem hB0] at h0
      exact (Option.some.inj h0).symm.trans hkeq
    have hlen : ((B.take n).map fun x => x.toNat / 2).length = n := by simp; omega
    have := (List.Nodup.getElem_inj hnd (i := 0) (j := j) (hi := by omega)
      (hj := by omega)).mp (by simp [List.getElem_take, hbeq])
    omega
  · exact hk0

private theorem s12c_final_props {t0 t lvl : List (BitVec 32)} {n : Nat} {uip : BitVec 32}
    (h : S12cTpi t0 t n) (h2 : 2 ≤ n) (hn : n ≤ t0.length) (h0 : t0[0]? = some uip)
    (hnd : ((t0.take n).map fun x => x.toNat / 2).Nodup)
    (hmax : ∀ k, 1 ≤ k → k < n →
      s12cLv lvl (t[k]?.getD 0#32) ≤ s12cLv lvl (t[1]?.getD 0#32)) :
    (∀ l, l ∈ (t.take n).map BitVec.toNat ↔ l ∈ (t0.take n).map BitVec.toNat) ∧
    (∀ l ∈ (t.take n).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < n ∧ (t0[j]?.getD 0#32).toNat = l) ∧
    ((t.take n).map fun x => x.toNat / 2).Nodup ∧ t[0]? = some uip ∧
    (∃ j, 1 ≤ j ∧ j < n ∧ t0[j]?.getD 0#32 = t[1]?.getD 0#32) ∧
    (∀ j, 1 ≤ j → j < n →
      s12cLv lvl (t0[j]?.getD 0#32) ≤ s12cLv lvl (t[1]?.getD 0#32)) := by
  obtain ⟨hl, ht0, hp⟩ := h
  have hiff : ∀ l, l ∈ (t.take n).map BitVec.toNat ↔ l ∈ (t0.take n).map BitVec.toNat := by
    intro l; simp only [List.mem_map]
    exact ⟨fun ⟨x, hx, he⟩ => ⟨x, hp.mem_iff.mp hx, he⟩,
      fun ⟨x, hx, he⟩ => ⟨x, hp.mem_iff.mpr hx, he⟩⟩
  have hnd' : ((t.take n).map fun x => x.toNat / 2).Nodup := (hp.map _).nodup_iff.mpr hnd
  refine ⟨hiff, ?_, hnd', ht0.trans h0, ?_, ?_⟩
  · intro l hl'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((hiff l).mp hl')
    obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_take] at hidx
    rw [List.getElem_take] at heq
    rcases Nat.eq_zero_or_pos idx with rfl | hpos
    · left
      rw [List.getElem?_eq_getElem (by omega)] at h0
      rw [← heq, Option.some.inj h0]
    · right
      exact ⟨idx, hpos, by omega, by rw [List.getElem?_eq_getElem (by omega), ← heq]; rfl⟩
  · obtain ⟨k, hk1, hkn, hkeq⟩ :=
      s12c_perm_pos hp.symm ht0.symm hnd' (j := 1) (Nat.le_refl _) (by omega) (by omega)
    exact ⟨k, hk1, hkn, by rw [hkeq]⟩
  · intro j hj1 hjn
    obtain ⟨k, hk1, hkn, hkeq⟩ := s12c_perm_pos hp ht0 hnd hj1 hjn (by omega)
    rw [← hkeq]; exact hmax k hk1 hkn

private theorem s12c_ins_step {lvl t3 : List (BitVec 32)} {x : BitVec 32} {i j j' M : Nat}
    (hjj : j' + 1 = j) (hj1 : 1 < j) (hji : j ≤ i) (hil : i < t3.length)
    (hA : ∀ k, 1 ≤ k → k ≤ i → k ≠ j → s12cLv lvl (t3[k]?.getD 0#32) ≤ M)
    (hB : 1 < j → s12cLv lvl (t3[1]?.getD 0#32) = M)
    (hcond : s12cLv lvl (t3[j']?.getD 0#32) < s12cLv lvl x) (v : BitVec 32)
    (hv : t3[j']? = some v) :
    (∀ k, 1 ≤ k → k ≤ i → k ≠ j' → s12cLv lvl ((t3.set j v)[k]?.getD 0#32) ≤ M) ∧
    (1 < j' → s12cLv lvl ((t3.set j v)[1]?.getD 0#32) = M) ∧
    (j' = 1 → M < s12cLv lvl x) := by
  subst hjj
  refine ⟨fun k hk1 hki hkj => ?_, fun hj2 => ?_, fun hj2 => ?_⟩
  · by_cases hkj' : k = j' + 1
    · subst hkj'
      rw [List.getElem?_set_self (by omega)]
      have := hA j' (by omega) (by omega) (by omega)
      rwa [hv] at this
    · rw [List.getElem?_set_ne (Ne.symm hkj')]; exact hA k hk1 hki hkj'
  · rw [List.getElem?_set_ne (by omega)]; exact hB hj1
  · subst hj2; rw [← hB hj1]; exact hcond

private theorem s12c_ins_exit {lvl t3 : List (BitVec 32)} {x : BitVec 32} {i j j' M : Nat}
    (hjj : j' + 1 = j) (hji : j ≤ i) (hil : i < t3.length)
    (hA : ∀ k, 1 ≤ k → k ≤ i → k ≠ j → s12cLv lvl (t3[k]?.getD 0#32) ≤ M)
    (hB : 1 < j → s12cLv lvl (t3[1]?.getD 0#32) = M)
    (hC : j = 1 → M < s12cLv lvl x)
    (hexit : j = 1 ∨ s12cLv lvl x ≤ s12cLv lvl (t3[j']?.getD 0#32)) :
    ∀ k, 1 ≤ k → k < i + 1 →
      s12cLv lvl ((t3.set j x)[k]?.getD 0#32) ≤ s12cLv lvl ((t3.set j x)[1]?.getD 0#32) := by
  subst hjj
  intro k hk1 hki
  rcases Nat.lt_or_ge 1 (j' + 1) with hj | hj
  · rw [List.getElem?_set_ne (show j' + 1 ≠ 1 by omega), hB hj]
    by_cases hkj : k = j' + 1
    · subst hkj
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      rcases hexit with h | h
      · omega
      · exact Nat.le_trans h (hA j' (by omega) (by omega) (by omega))
    · rw [List.getElem?_set_ne (Ne.symm hkj)]; exact hA k hk1 (by omega) hkj
  · have hj1' : j' = 0 := by omega
    subst hj1'
    rw [List.getElem?_set_self (by omega), Option.getD_some]
    by_cases hk : k = 1
    · subst hk; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact Nat.le_refl _
    · rw [List.getElem?_set_ne (Ne.symm hk)]
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hA k hk1 (by omega) hk) (hC rfl))

private theorem s12c_shift' {xs orig : List (BitVec 32)} {sz j j' : Nat} {x prev : BitVec 32}
    (hjj : j' + 1 = j) (hlen : xs.length = orig.length) (hsz : sz ≤ orig.length) (hjsz : j < sz)
    (hprev : xs[j']? = some prev) (hperm : ((xs.set j x).take sz).Perm (orig.take sz)) :
    (((xs.set j prev).set j' x).take sz).Perm (orig.take sz) := by
  subst hjj
  have h := s12c_tmp_shift_hole (j := j' + 1) hlen hsz (Nat.succ_pos _) hjsz
    (by simpa using hprev) hperm
  simpa using h

private theorem s12cLv_of_idx {lvl : List (BitVec 32)} {y : BitVec 32} {idx : Nat}
    (hidx : idx = y.toNat / 2) (h : idx < lvl.length) :
    s12cLv lvl y = (lvl[idx]'h).toNat := by
  subst hidx; unfold s12cLv; rw [List.getElem?_eq_getElem h, Option.getD_some]

private theorem s12c_getElem?_of_idx {t : List (BitVec 32)} {k k' : Nat} (hk : k = k')
    (h : k < t.length) : t[k']? = some (t[k]'h) := by
  subst hk; exact List.getElem?_eq_getElem h

private theorem s12cLv_eq_lvl {lvl t : List (BitVec 32)} {k k' i1 : Nat} (hk : k = k')
    (hkt : k < t.length) (hi1 : i1 = (t[k]'hkt).toNat / 2) (h1 : i1 < lvl.length) :
    s12cLv lvl (t[k']?.getD 0#32) = (lvl[i1]'h1).toNat := by
  subst hk hi1; unfold s12cLv
  rw [List.getElem?_eq_getElem hkt, Option.getD_some, List.getElem?_eq_getElem h1,
    Option.getD_some]

private theorem s12c_lt_of_lvl {lvl t : List (BitVec 32)} {x : BitVec 32} {k k' i1 i2 : Nat}
    (hk : k = k') (hkt : k < t.length) (hi1 : i1 = (t[k]'hkt).toNat / 2)
    (hi2 : i2 = x.toNat / 2) {h1 : i1 < lvl.length} {h2 : i2 < lvl.length}
    (hc : (lvl[i1]'h1).toNat < (lvl[i2]'h2).toNat) :
    s12cLv lvl (t[k']?.getD 0#32) < s12cLv lvl x := by
  rw [s12cLv_eq_lvl hk hkt hi1 h1, s12cLv_of_idx hi2 h2]; exact hc

private theorem s12c_le_of_lvl {lvl t : List (BitVec 32)} {x : BitVec 32} {k k' i1 i2 : Nat}
    (hk : k = k') (hkt : k < t.length) (hi1 : i1 = (t[k]'hkt).toNat / 2)
    (hi2 : i2 = x.toNat / 2) {h1 : i1 < lvl.length} {h2 : i2 < lvl.length}
    (hc : ¬ (lvl[i1]'h1).toNat < (lvl[i2]'h2).toNat) :
    s12cLv lvl x ≤ s12cLv lvl (t[k']?.getD 0#32) := by
  rw [s12cLv_eq_lvl hk hkt hi1 h1, s12cLv_of_idx hi2 h2]; omega

private theorem s12c_lshr1 (y : BitVec 32) : (y.setWidth 64 >>> 1).toNat = y.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, bv32_setWidth64_toNat]

private theorem s12c_la_bv32_lshr_1 (x : BitVec 32) :
    (x >>> 1#32).toNat = x.toNat / 2 := bv32_lshr_1 x
private theorem s12c_la_i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (i8_sext32_eq0 v)
private theorem s12c_la_bv32_0_sext_mul4 :
    ((0#32 : BitVec 32).signExtend 64 * 4#64) = 0#64 := rfl
private theorem s12c_la_bv32_1_sext_mul4 :
    ((1#32 : BitVec 32).signExtend 64 * 4#64) = 4#64 := rfl
attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true s12c_la_bv32_lshr_1
  s12c_la_i8_sext32_eq0_prop s12c_la_bv32_0_sext_mul4 s12c_la_bv32_1_sext_mul4

private theorem s12c_la_bv64_sub1_toNat {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx := x.isLt; bv_omega

private theorem s12c_nat_lt31_bv32_msb0 {n : Nat} (hn : n < 2 ^ 31 - 1) :
    let v := (BitVec.ofNat 64 n).setWidth 32
    v.toNat = n ∧ v ≠ 0xFFFFFFFF#32 ∧ (v &&& 0x80000000#32) = 0#32 := by
  have hn_mod : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  have hto : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), hn_mod]
  refine ⟨hto, ?_, ?_⟩
  · intro heq; have h1 := congrArg BitVec.toNat heq; rw [hto] at h1
    have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
  · apply BitVec.eq_of_getElem_eq; intro i hi
    rw [BitVec.getElem_and, BitVec.getElem_zero]
    by_cases h31 : i = 31
    · subst h31; rw [BitVec.getElem_eq_testBit_toNat, hto, Nat.testBit,
        Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega : n < 2 ^ 31)]; simp
    · rw [show (0x80000000#32 : BitVec 32)[i]'hi = false from by revert i hi h31; decide]
      simp

private theorem s12c_tmp_take1_eq {tmp : List (BitVec 32)} {u : BitVec 32} (h1 : 1 ≤ tmp.length)
    (h0 : tmp[0]? = some u) : (tmp.take 1).map BitVec.toNat = [u.toNat] := by
  cases tmp with
  | nil => simp at h1
  | cons a _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0; simp

private theorem s12c_tmp_take2_eq {tmp : List (BitVec 32)} {u v : BitVec 32} (h2 : 2 ≤ tmp.length)
    (h0 : tmp[0]? = some u) (h1 : tmp[1]? = some v) :
    (tmp.take 2).map BitVec.toNat = [u.toNat, v.toNat] := by
  rcases tmp with _ | ⟨a, _ | ⟨b, _⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    subst h0 h1; simp

private theorem s12c_laOtfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem s12c_canon_to_laOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem s12c_laOtfsInv_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s) :
    FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, s12c_laOtfs_to_canon h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem s12c_canon_to_laOtfsInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) :
    FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, s12c_canon_to_laOtfs h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem s12c_laSparse_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullSparseInvW c F0 F_cur s) :
    FullSparseInvW c F0 F_cur s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem s12c_bv32_or_used31_garb (h : BitVec 32) :
    ((h ||| 0xF8000000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_and]
  have h0 : ((0xF8000000#32 : BitVec 32)[i]'hi && (0x00080000#32 : BitVec 32)[i]'hi) = false := by
    revert i hi; decide
  cases h1 : (0x00080000#32 : BitVec 32)[i]'hi <;>
    cases h2 : (0xF8000000#32 : BitVec 32)[i]'hi <;> simp_all

private theorem s12c_bv32_or_used31_shrk (h : BitVec 32) :
    ((h ||| 0xF8000000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_and]
  have h0 : ((0xF8000000#32 : BitVec 32)[i]'hi && (0x00800000#32 : BitVec 32)[i]'hi) = false := by
    revert i hi; decide
  cases h1 : (0x00800000#32 : BitVec 32)[i]'hi <;>
    cases h2 : (0xF8000000#32 : BitVec 32)[i]'hi <;> simp_all

private theorem s12c_orUsed31_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hs : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) :
    let ar' := s.core.arena.set cref (fullArenaHdr s cref ||| 0xF8000000#32)
    let s' : FullState := { s with core := { s.core with arena := ar' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro ar' s'
  have hlen := hs.1.core_ok
  have hw := hs.2.1
  have ha := hw.arena
  have hcref_wf := ha.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : s.core.arena[cref]? = some (fullArenaHdrCore s.core cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have ha_cref : s'.core.arena[cref]? = some (fullArenaHdrCore s.core cref ||| 0xF8000000#32) :=
    List.getElem?_set_self har_len
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (ha.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]? :=
        List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [s12c_bv32_or_used31_shrk,
        show fullArenaHdrCore s.core cref = s.core.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
        · have := (ha.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (ha.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s', ar']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
      · have := (ha.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    by_cases hrc : r = cref
    · subst r
      rw [ha_cref, hget_cref, Option.getD_some, Option.getD_some, s12c_bv32_or_used31_garb]
    · dsimp only [s', ar']; rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hszr := hsz_eq r hr
    unfold fullArenaClauseLitsCore
    rw [hszr]; congr 1
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, s', ar', List.length_set]
    · intro j hj1 hj2
      simp only [List.getElem_take, List.getElem_drop]
      dsimp only [s', ar']
      have hne_idx : cref ≠ r + 3 + j := by
        by_cases hrc : r = cref
        · subst r; omega
        · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
          · simp only [List.length_take, List.length_drop, s', ar', List.length_set] at hj1
            omega
          · omega
      exact List.getElem_set_ne hne_idx _
  have ha' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := ha.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢
          simpa only [ha_cref, hget_cref, Option.getD_some, s12c_bv32_or_used31_shrk] using hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa only [s', ar', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (ha.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, ht0_hi, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (ha.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (ha.refs_wf cref hr).2.1; omega
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
          · omega
          · have := (ha.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo,
        by dsimp only [s']; exact Nat.lt_of_le_of_lt ht0_hi ht2, ?_⟩
      dsimp only [s', ar']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr] at hl
      exact ha.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng
      change (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLitsCore s'.core r))
      rw [hlits_eq r hr]
      exact ha.entails r hr hng
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := ha'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        change if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
        split
        · rename_i hbin; rw [ite_eq_left hbin] at hrs; exact hrs
        · rename_i hlg; rw [ite_eq_right hlg] at hrs
          obtain ⟨hrr, hng, hall⟩ := hrs
          exact ⟨hrefs.symm ▸ hrr, (hgarb_eq _ hrr).trans hng,
            fun q hq => hall q ((hlits_eq _ hrr) ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hmem := hw.reason_lit_mem idx hidx hne hlg
        have hrs := hw.reason_inv idx hidx hne
        rw [ite_eq_right (fun h => h hlg)] at hrs
        change (s.core.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s'.core _
        rw [hlits_eq _ hrs.1]; exact hmem }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen with arena_len_arr := by simp [s', ar', hlen.arena_len_arr] }, hs.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgarb_eq r hr] at hng
    change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
    rw [hlits_eq r hr]; exact hs.2.2.2.1 r hr hng
  have hext' : FullExtScratchOk c s' :=
    Full.FullExtScratchOk.of_pres hs.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
  exact ⟨⟨hlen', hw', hs.2.2.1, hnd', hext', hs.2.2.2.2.2⟩, hrefs,
    fun r hr => ⟨hgarb_eq r hr, hlits_eq r hr⟩⟩

private theorem s12c_learn_clause_post_ac_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_ac : FullState} {R : Mem 64 → Prop} {m_ac : Mem 64}
    {uip_lit wm : BitVec 32} {new_ref64 : BitVec 64} {max_lvl : Nat}
    {tmp_sw : List (BitVec 32)}
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X)
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hac_sparse : FullSparseInvW c F0 F_cur s_ac)
    (hcur_lt : s_ac.core.cur_level < s.core.cur_level)
    (hmax_pos : 0 < max_lvl) (hmax_le : max_lvl ≤ s_ac.core.cur_level)
    (hmax_lt28 : max_lvl < 2 * 2 ^ 28)
    (hcv_eq : s_ac.core.cur_vars = s.core.cur_vars)
    (hfuel : s_ac.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hws2 : s_ac.scratch.work_stk2 = s.scratch.work_stk2)
    (htmp_eq : s_ac.core.tmp = tmp_sw) (htlen_eq : s_ac.core.tmp_len = s.core.tmp_len)
    (hsw_1 : tmp_sw[1]? = some wm)
    (htl_2 : 2 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (huip_lt : uip_lit.toNat < 2 * s.core.cur_vars)
    (hwm_lt : wm.toNat < 2 * s.core.cur_vars)
    (htmp_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hwm_on_bt : ∃ idx < s_ac.core.trail_end,
      (s_ac.core.trl[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
      (s_ac.core.lvl[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hlow : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
      q = uip_lit.toNat ∨ ∃ idx < s_ac.core.trail_end,
        (s_ac.core.trl[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s_ac.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hr_spec : new_ref64 = 0xFFFFFFFF#64 ∨
      (new_ref64 ≠ 0xFFFFFFFF#64 ∧
        if new_ref64 = 0xFFFFFFFE#64 then
          (cnfOfClauses F_cur).EntailsClause (cnfClause [uip_lit.toNat, wm.toNat])
        else
          new_ref64.toNat < 2 ^ 31 - 1 ∧
          new_ref64.toNat ∈ fullArenaClauseRefs s_ac ∧
          fullArenaClauseGarb s_ac new_ref64.toNat = false ∧
          (∀ q ∈ fullArenaClauseLits s_ac new_ref64.toNat,
            q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat) ∧
          uip_lit.toNat ∈ fullArenaClauseLits s_ac new_ref64.toNat))
    (hm_ac : (FullMem c s_ac ⋆ R) m_ac) :
    wp Γ Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
          args := (Arg.var new_ref64, Arg.imm 4294967295, ()) } fun p36 =>
        Expr.jnz (Arg.var p36.1) (Expr.ret (Arg.imm 0, ()))
          (Expr.let_
            { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var uip_lit, ()) } fun p37 =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.pVals, Arg.var p37.1, ()) } fun p38 =>
              Expr.load i8 (Arg.var p38.1) fun ld =>
                Expr.let_
                  { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p39 =>
                  Expr.let_
                    { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld, ()) } fun p40 =>
                    Expr.let_
                      { sig := [i8], code := OpCode.sext 8 32,
                        args := (Arg.var p39.1, ()) } fun p41 =>
                      Expr.let_
                        { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                          args := (Arg.var p40.1, Arg.var p41.1, ()) } fun p42 =>
                        Expr.jnz (Arg.var p42.1) (Expr.ret (Arg.imm 0, ()))
                          (Expr.group (sig := [[]])
                            (fun _Ju =>
                              Blocks.cons
                                (fun _ =>
                                  Expr.group (sig := [[i32]])
                                    (fun _Js =>
                                      Blocks.cons
                                        (fun p43 =>
                                          Expr.let_
                                            { sig := [i64], code := OpCode.trunc 64 32,
                                              args := (Arg.var (BitVec.ofNat 64 max_lvl), ()) }
                                            fun p44 =>
                                            Expr.call (as := [i64, i32, i32, i32]) (bs := [])
                                              (rs := [i64]) "full_assign_lvl"
                                              (Arg.var c.hdr, Arg.var uip_lit, Arg.var p43.1,
                                                Arg.var p44.1, ())
                                              fun (_ : Tup Val []) =>
                                              Expr.call (as := [i64, i64]) (bs := []) (rs := [i64])
                                                "full_eager_subsume"
                                                (Arg.var c.hdr, Arg.var new_ref64, ())
                                                fun (_ : Tup Val []) =>
                                                  Expr.ret (rs := [i64]) (Arg.imm 1, ()))
                                        Blocks.nil)
                                    fun Js =>
                                    Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                        args := (Arg.var new_ref64, Arg.imm 4294967294, ()) }
                                      fun p =>
                                      Expr.jnz (Arg.var p.1)
                                        (Expr.let_
                                          { sig := [i32], code := OpCode.sext 32 64,
                                            args := (Arg.imm 1, ()) } fun p =>
                                          Expr.let_
                                            { sig := [i64, i64], code := OpCode.mul i64,
                                              args := (Arg.var p.1, Arg.imm 4, ()) } fun p =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.add i64,
                                                args := (Arg.var c.pTmp, Arg.var p.1, ()) } fun p =>
                                              Expr.load i32 (Arg.var p.1) fun ld =>
                                                Expr.let_
                                                  { sig := [i32, i32], code := OpCode.and i32,
                                                    args := (Arg.var ld, Arg.imm 2147483647, ()) }
                                                  fun p =>
                                                  Expr.let_
                                                    { sig := [i32, i32], code := OpCode.or i32,
                                                      args :=
                                                        (Arg.var p.1, Arg.imm 2147483648, ()) }
                                                    fun p =>
                                                    Expr.jump Js.1 (Arg.var p.1, ()))
                                        (Expr.let_
                                          { sig := [i64], code := OpCode.trunc 64 32,
                                            args := (Arg.var new_ref64, ()) } fun p =>
                                          Expr.jump Js.1 (Arg.var p.1, ())))
                                Blocks.nil)
                            fun Ju =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                args := (Arg.var new_ref64, Arg.imm 4294967294, ()) } fun p =>
                              Expr.jnz (Arg.var p.1)
                                (Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p =>
                                  Expr.load i64 (Arg.var p.1) fun ld =>
                                    Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                                        args := (Arg.var new_ref64, Arg.var ld, ()) } fun p =>
                                      Expr.jnz (Arg.var p.1)
                                        (Expr.let_
                                          { sig := [i64, i64], code := OpCode.add i64,
                                            args := (Arg.var c.hdr, Arg.imm 112, ()) } fun p =>
                                          Expr.load i64 (Arg.var p.1) fun ld_ar =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.mul i64,
                                                args := (Arg.var new_ref64, Arg.imm 4, ()) }
                                              fun p =>
                                              Expr.let_
                                                { sig := [i64, i64], code := OpCode.add i64,
                                                  args := (Arg.var ld_ar, Arg.var p.1, ()) }
                                                fun p_el =>
                                                Expr.load i32 (Arg.var p_el.1) fun ld_h =>
                                                  Expr.let_
                                                    { sig := [i32, i32], code := OpCode.shl i32,
                                                      args := (Arg.imm 31, Arg.imm 27, ()) }
                                                    fun p_sh =>
                                                    Expr.let_
                                                      { sig := [i32, i32], code := OpCode.or i32,
                                                        args := (Arg.var ld_h, Arg.var p_sh.1, ()) }
                                                      fun p_nh =>
                                                      Expr.store (Arg.var p_nh.1)
                                                        (Arg.var p_el.1)
                                                        (Expr.jump Ju.1 ()))
                                        (Expr.jump Ju.1 ()))
                                (Expr.jump Ju.1 ()))))
      m_ac := by
  have hac_len := hac_sparse.1
  have hcl := hac_len.core_ok
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have huip_vlen : uip_lit.toNat < s_ac.core.vals.length := by
    rw [hcl.vals_len]; have := hcl.cur_vars_le; omega
  c0_split
  · c0_steps
    exact hQ 0#64 s_ac m_ac hac_len (Or.inl rfl) hcv_eq hfuel hws2
      (fun h => by cases h) (fun _ => hac_sparse) (fun h => by cases h) hm_ac
  · have hne_ff : new_ref64 ≠ 0xFFFFFFFF#64 := by assumption
    have hnr_ok := (hr_spec.resolve_left hne_ff).2
    c0_split
    · c0_steps
      exact hQ 0#64 s_ac m_ac hac_len (Or.inl rfl) hcv_eq hfuel hws2
        (fun h => by cases h) (fun _ => hac_sparse) (fun h => by cases h) hm_ac
    · have huip_z : s_ac.core.vals[uip_lit.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]
        exact (by assumption : s_ac.core.vals[uip_lit.toNat] = 0#8)
      refine wp_join_group (ts := []) (fun () m_u =>
          ∃ ar_u : List (BitVec 32),
            let s_u : FullState := { s_ac with core := { s_ac.core with arena := ar_u } }
            FullSparseInvW c F0 F_cur s_u ∧ fullArenaClauseRefs s_u = fullArenaClauseRefs s_ac ∧
            (∀ r ∈ fullArenaClauseRefs s_ac,
              fullArenaClauseGarb s_u r = fullArenaClauseGarb s_ac r ∧
              fullArenaClauseLits s_u r = fullArenaClauseLits s_ac r) ∧
            (FullMem c s_u ⋆ R) m_u) ?_ ?_
      · rintro _ ⟨⟩ m_u ⟨ar_u, hu_sparse, hrefs_u, hprops_u, hm_u⟩
        let s_u : FullState := { s_ac with core := { s_ac.core with arena := ar_u } }
        have hu_len := hu_sparse.1
        refine wp_join_group (ts := [i32]) (fun (rsn_bv, ()) m_r =>
            m_r = m_u ∧ rsn_bv ≠ 0xFFFFFFFF#32 ∧
            (if (rsn_bv &&& 0x80000000#32) ≠ 0#32 then
              let ot := (rsn_bv &&& 0x7FFFFFFF#32).toNat
              ot < 2 * s_u.core.cur_vars ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [uip_lit.toNat, ot]) ∧
              ∃ m < s_u.core.trail_end, (s_u.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
                (s_u.core.lvl[ot / 2]?.getD 0#32).toNat ≤ max_lvl
            else
              rsn_bv.toNat ∈ fullArenaClauseRefsCore s_u.core ∧
              fullArenaClauseGarbCore s_u.core rsn_bv.toNat = false ∧
              (∀ q ∈ fullArenaClauseLitsCore s_u.core rsn_bv.toNat,
                q = uip_lit.toNat ∨ ∃ m < s_u.core.trail_end,
                  (s_u.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                  (s_u.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl) ∧
              uip_lit.toNat ∈ fullArenaClauseLitsCore s_u.core rsn_bv.toNat)) ?_ ?_
        · rintro _ ⟨rsn_bv, ⟨⟩⟩ m_r ⟨rfl, hrsn_ne, hrsn_prop⟩
          have hte_lt : s_u.core.trail_end < c.max_vars := by
            have h1 := hu_sparse.2.1.trail_end_lt_of_unassigned (hcv_eq ▸ huip_lt) huip_z
            have := hcl.cur_vars_le; dsimp only [s_u] at h1 ⊢; omega
          have hml_tr : ((BitVec.ofNat 64 max_lvl).setWidth 32).toNat = max_lvl := by
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : max_lvl < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
          have hml_nz : (BitVec.ofNat 64 max_lvl).setWidth 32 ≠ 0#32 := fun heq => by
            have h0 := congrArg BitVec.toNat heq
            rw [hml_tr, show (0#32 : BitVec 32).toNat = 0 from rfl] at h0; omega
          c0_to_group; c0_call hAsgn
          refine ⟨c, s_u, R, rfl, hu_len, hm_u, ?_⟩
          rw [ite_eq_right (fun h => by
            dsimp only [s_u] at h hte_lt
            rw [huip_z] at h
            have := hcv_eq ▸ huip_lt
            rcases h with h | h | h
            · omega
            · omega
            · exact h rfl)]
          intro v rsn_let unfl_let flags' unass' phases' m_as hfll hph s_as0 hm_as
          have hrsn_let : rsn_let = rsn_bv := ite_eq_right hml_nz
          have hunfl_let : unfl_let = s_u.core.unflushed := ite_eq_right hml_nz
          c0_clean; c0_to_group
          let s_as : FullState :=
            { s_u with
              core :=
                { s_u.core with
                  vals := (s_u.core.vals.set uip_lit.toNat 1#8).set (uip_lit.toNat ^^^ 1) 0xFF#8
                  flags := flags'
                  lvl := s_u.core.lvl.set (uip_lit.toNat / 2)
                    ((BitVec.ofNat 64 max_lvl).setWidth 32)
                  rsns := s_u.core.rsns.set (uip_lit.toNat / 2) rsn_bv
                  trl := s_u.core.trl.set s_u.core.trail_end uip_lit
                  trail_pos := s_u.core.trail_pos.set (uip_lit.toNat / 2)
                    (BitVec.ofNat 32 s_u.core.trail_end)
                  trail_end := s_u.core.trail_end + 1
                  unassigned := unass', unflushed := s_u.core.unflushed }
              scratch := { s_u.scratch with phases := phases' } }
          have hml_bv : (BitVec.ofNat 64 max_lvl).setWidth 32 = BitVec.ofNat 32 max_lvl :=
            BitVec.eq_of_toNat_eq (by rw [hml_tr, bv32_ofNat_toNat (by omega)])
          have hsc_as : s_as.scratch.LengthsOk c := { hu_len.scratch_ok with phases_len := hph }
          have ⟨has_len, has_w⟩ := chronoAssign_preserves_fullWitness hu_sparse.2.1 hu_len hsc_as
            (rsn := rsn_bv) (unassigned' := unass') (unflushed' := s_u.core.unflushed)
            hfll (hcv_eq ▸ huip_lt) huip_z hmax_le (fun _ => hrsn_ne)
            (fun h0 => absurd h0 (by omega))
            (fun _ _ => by
              split
              · rename_i hbin; rw [ite_eq_left hbin] at hrsn_prop; exact hrsn_prop
              · rename_i hnbin; rw [ite_eq_right hnbin] at hrsn_prop
                exact ⟨hrsn_prop.1, hrsn_prop.2.1, hrsn_prop.2.2.1⟩)
            (fun _ _ hzero => by
              rw [ite_eq_right (fun h => absurd hzero h)] at hrsn_prop; exact hrsn_prop.2.2.2)
          have hm_as' : (FullMem c s_as ⋆ R) m_as := by
            simpa only [s_as, s_as0, v, hrsn_let, hunfl_let] using hm_as
          have hmne0 : max_lvl ≠ 0 := by omega
          have has_sparse : FullSparseInvW c F0 F_cur s_as :=
            ⟨by simpa [s_as, hml_bv, hmne0] using has_len,
             by simpa [s_as, hml_bv, hmne0] using has_w,
             hu_sparse.2.2.1, hu_sparse.2.2.2.1, hu_sparse.2.2.2.2.1, hu_sparse.2.2.2.2.2⟩
          have htmp_as_lt : ∀ k < s_as.core.tmp_len,
              (s_as.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk => by
            simpa only [s_as, s_u, htmp_eq, htlen_eq] using
              htmp_lt k (by simpa [s_as, s_u, htlen_eq] using hk)
          c0_call hEsub
          refine ⟨c, F0, F_cur, s_as, R, rfl, has_sparse, htmp_as_lt, ?_, hm_as', ?_⟩
          · intro _
            by_cases hfe : new_ref64 = 0xFFFFFFFE#64
            · subst hfe; exfalso; have : (0xFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 32 - 2 := rfl
              omega
            · simp only [hfe, ↓reduceIte] at hnr_ok
              change new_ref64.toNat ∈ fullArenaClauseRefs s_u
              rw [hrefs_u]; exact hnr_ok.2.1
          · intro ar' ag' sc' m_fin _ hfin_sparse hws2' hm_fin
            c0_steps
            exact hQ 1#64 _ m_fin hfin_sparse.1 (Or.inr (Or.inl rfl)) hcv_eq hfuel
              (hws2'.trans (by simp [s_as, s_u, hws2])) (fun h => by cases h)
              (fun h => by cases h) (fun _ => ⟨hfin_sparse, hcur_lt⟩) hm_fin
        · intro Jrsn hJrsn; c0_split
          · have hfe : new_ref64 = 0xFFFFFFFE#64 := by assumption
            simp only [hfe, ↓reduceIte] at hnr_ok
            have := hcl.cur_vars_le
            have hwm_lt31 : wm.toNat < 2 ^ 31 - 1 := by omega
            have hmask := bin_rsn_mask_props (l := wm) hwm_lt31
            have h1_lt : 1 < s_u.core.tmp.length := by rw [hu_len.core_ok.tmp_len_arr]; omega
            have htmp1_eq : s_u.core.tmp[1]'h1_lt = wm := Option.some.inj
              (by rw [← List.getElem?_eq_getElem h1_lt, show s_u.core.tmp = tmp_sw from htmp_eq,
                hsw_1])
            c0_steps
            refine wp_load_of (load_full_tmp1 (c := c) (s := s_u) (R := R) h1_lt hm_u) ?_
            c0_steps
            rw [htmp1_eq]
            refine hJrsn ((wm &&& 0x7FFFFFFF#32) ||| 0x80000000#32, ()) m_u ⟨rfl, hmask.1, ?_⟩
            rw [ite_eq_left hmask.2.1, hmask.2.2]
            exact ⟨hcv_eq ▸ hwm_lt, hnr_ok, hwm_on_bt⟩
          · have hne_fe : new_ref64 ≠ 0xFFFFFFFE#64 := by assumption
            simp only [hne_fe, ↓reduceIte] at hnr_ok
            obtain ⟨hlt31, href, hng, hlits_sub, huip_in⟩ := hnr_ok
            have hnr_bv := s12c_nat_lt31_bv32_msb0 hlt31
            rw [BitVec.eq_of_toNat_eq (bv64_ofNat_toNat new_ref64.isLt)] at hnr_bv
            c0_steps
            refine hJrsn (new_ref64.setWidth 32, ()) m_u ⟨rfl, hnr_bv.2.1, ?_⟩
            rw [ite_eq_right (fun h => absurd hnr_bv.2.2 h), hnr_bv.1]
            obtain ⟨hgu, hlu⟩ := hprops_u new_ref64.toNat href
            exact ⟨by change _ ∈ fullArenaClauseRefs s_u; rw [hrefs_u]; exact href,
              hgu.trans hng,
              fun q hq => hlow q (hlits_sub q (by
                change q ∈ fullArenaClauseLits s_ac _; rw [← hlu]; exact hq)),
              by change uip_lit.toNat ∈ fullArenaClauseLits s_u _; rw [hlu]; exact huip_in⟩
      · intro Ju hJu; c0_split
        · have hne_fe : new_ref64 ≠ 0xFFFFFFFE#64 := by assumption
          simp only [hne_fe, ↓reduceIte] at hnr_ok
          obtain ⟨_, href, _, _, _⟩ := hnr_ok
          c0_split
          · have hnr_ar : new_ref64.toNat < s_ac.core.arena.length := by
              have hwf := hac_sparse.2.1.arena.refs_wf new_ref64.toNat href
              have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
            have hhdr_eq : s_ac.core.arena[new_ref64.toNat]'hnr_ar =
                fullArenaHdr s_ac new_ref64.toNat := by
              unfold fullArenaHdr fullArenaHdrCore
              rw [List.getElem?_eq_getElem hnr_ar, Option.getD_some]
            have hmask31 : ((31 : BitVec 32) <<< (27 : BitVec 32)) = 0xF8000000#32 := by decide
            have hmask31n : ((31 : BitVec 32) <<< (27 : Nat)) = 0xF8000000#32 := by decide
            c0_steps
            refine wp_load_of (FullArenaTactics.load_full_arena_ptr hm_ac) ?_
            c0_steps
            obtain ⟨hu_sp, hrefs_u, hprops_u⟩ :=
              s12c_orUsed31_preserves_fullSparseW hac_sparse href
            exact hJu () m ⟨_, hu_sp, hrefs_u, hprops_u,
              by simpa only [hhdr_eq, hmask31, hmask31n] using hm⟩
          · c0_steps; exact hJu () m_ac ⟨s_ac.core.arena, hac_sparse, rfl,
              fun _ _ => ⟨rfl, rfl⟩, hm_ac⟩
        · c0_steps; exact hJu () m_ac ⟨s_ac.core.arena, hac_sparse, rfl,
            fun _ _ => ⟨rfl, rfl⟩, hm_ac⟩

private theorem s12c_rev_phase_wp {Γ : Env} {Q : Post [i64]} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} (Jr : Cont [])
    (hm : (FullMem c s ⋆ R) m) (htl3 : 2 < s.core.tmp_len)
    (htl_cv : s.core.tmp_len ≤ s.core.cur_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (htmp_len_arr : s.core.tmp.length = c.max_vars) (hll : s.core.lvl.length = c.max_vars)
    (hmv : c.max_vars < 2 * 2 ^ 28)
    (hlits : ∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hJr : ∀ m' : Mem 64, (∃ t1 : List (BitVec 32), S12cTpi s.core.tmp t1 s.core.tmp_len ∧
      (FullMem c { s with core := { s.core with tmp := t1 } } ⋆ R) m') → Jr () m') :
    wp Γ Q X
      (Expr.group (sig := [[i64, i64]])
      (fun Js =>
      Blocks.cons
      (fun p =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var (Prod.fst p), Arg.var (Prod.fst (Prod.snd p)), ()) }
      fun p_1 =>
      Expr.jnz (Arg.var (Prod.fst p_1))
      (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p),
        Arg.imm 4, ()) }
      fun p_2 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.pTmp,
        Arg.var (Prod.fst p_2), ()) }
      fun p_3 =>
      Expr.load i32 (Arg.var (Prod.fst p_3)) fun ld =>
      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p),
        Arg.imm 4, ()) }
      fun p_4 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_4), ()) }
      fun p_5 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64,
        args := (Arg.var (Prod.fst (Prod.snd p)), Arg.imm 4, ()) }
      fun p_6 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_6), ()) }
      fun p_7 =>
      Expr.load i32 (Arg.var (Prod.fst p_7)) fun ld_1 =>
      Expr.store (Arg.var ld_1) (Arg.var (Prod.fst p_5))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64,
        args := (Arg.var (Prod.fst (Prod.snd p)), Arg.imm 4, ()) }
      fun p_8 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_8), ()) }
      fun p_9 =>
      Expr.store (Arg.var ld) (Arg.var (Prod.fst p_9))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_10 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64,
        args := (Arg.var (Prod.fst (Prod.snd p)), Arg.imm 1, ()) }
      fun p => Expr.jump (Prod.fst Js) (Arg.var (Prod.fst p_10), Arg.var (Prod.fst p), ()))))
      (Expr.group (sig := [[i64]])
      (fun Js =>
      Blocks.cons
      (fun p =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var (Prod.fst p), Arg.var (BitVec.ofNat 64 s.core.tmp_len), ()) }
      fun p_2 =>
      Expr.jnz (Arg.var (Prod.fst p_2))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p), Arg.imm 4, ()) }
      fun p_3 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_3), ()) }
      fun p_4 =>
      Expr.load i32 (Arg.var (Prod.fst p_4)) fun ld =>
      Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) }
      fun p_5 =>
      Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
      fun p_6 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.lshr i64,
        args := (Arg.var (Prod.fst p_5), Arg.var (Prod.fst p_6), ()) }
      fun p_7 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p_7), Arg.imm 4, ()) }
      fun p_8 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pLevel, Arg.var (Prod.fst p_8), ()) }
      fun p_9 =>
      Expr.load i32 (Arg.var (Prod.fst p_9)) fun ld =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_10 =>
      Expr.group (sig := [[i64]])
      (fun Js_1 =>
      Blocks.cons
      (fun p_11 =>
      Expr.group (sig := [[]])
      (fun _ =>
      Blocks.cons
      (fun _ =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64,
        args := (Arg.var (Prod.fst p_11), Arg.imm 1, ()) }
      fun p_13 =>
      Expr.group (sig := [[i64, i64]])
      (fun Js_3 =>
      Blocks.cons
      (fun p =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var (Prod.fst p), Arg.var (Prod.fst (Prod.snd p)), ()) }
      fun p_14 =>
      Expr.jnz (Arg.var (Prod.fst p_14))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p), Arg.imm 4, ()) }
      fun p_15 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_15), ()) }
      fun p_16 =>
      Expr.load i32 (Arg.var (Prod.fst p_16))
      fun ld =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p), Arg.imm 4, ()) }
      fun p_17 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_17), ()) }
      fun p_18 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64,
        args := (Arg.var (Prod.fst (Prod.snd p)), Arg.imm 4, ()) }
      fun p_19 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_19), ()) }
      fun p_20 =>
      Expr.load i32
      (Arg.var (Prod.fst p_20))
      fun ld_1 =>
      Expr.store (Arg.var ld_1)
      (Arg.var (Prod.fst p_18))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64,
        args := (Arg.var (Prod.fst (Prod.snd p)), Arg.imm 4, ()) }
      fun p_21 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_21), ()) }
      fun p_22 =>
      Expr.store
      (Arg.var ld)
      (Arg.var (Prod.fst p_22))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_23 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64,
        args := (Arg.var (Prod.fst (Prod.snd p)), Arg.imm 1, ()) }
      fun p =>
      Expr.jump
      (Prod.fst Js_3)
      (Arg.var
      (Prod.fst p_23),
      Arg.var
      (Prod.fst p),
      ()))))
      (Expr.jump (Prod.fst Js) (Arg.var (Prod.fst p_11), ())))
      Blocks.nil)
      fun Js =>
      Expr.jump (Prod.fst Js)
      (Arg.var (Prod.fst p), Arg.var (Prod.fst p_13), ()))
      Blocks.nil)
      fun Js =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var (Prod.fst p_11), Arg.var (BitVec.ofNat 64 s.core.tmp_len), ()) }
      fun p =>
      Expr.jnz (Arg.var (Prod.fst p))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64,
        args := (Arg.var (Prod.fst p_11), Arg.imm 4, ()) }
      fun p =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p), ()) }
      fun p =>
      Expr.load i32 (Arg.var (Prod.fst p)) fun ld_1 =>
      Expr.let_
      { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_1, ()) }
      fun p =>
      Expr.let_
      { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
      fun p_12 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.lshr i64,
        args := (Arg.var (Prod.fst p), Arg.var (Prod.fst p_12), ()) }
      fun p =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p), Arg.imm 4, ()) }
      fun p =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pLevel, Arg.var (Prod.fst p), ()) }
      fun p =>
      Expr.load i32 (Arg.var (Prod.fst p)) fun ld_2 =>
      Expr.let_
      { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var ld_2, Arg.var ld, ()) }
      fun p =>
      Expr.jnz (Arg.var (Prod.fst p))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var (Prod.fst p_11), Arg.imm 1, ()) }
      fun p =>
      Expr.jump (Prod.fst Js_1)
      (Arg.var (Prod.fst p), ()))
      (Expr.jump (Prod.fst Js) ()))
      (Expr.jump (Prod.fst Js) ()))
      Blocks.nil)
      fun Js => Expr.jump (Prod.fst Js) (Arg.var (Prod.fst p_10), ()))
      (Expr.jump Jr ()))
      Blocks.nil)
      fun Js => Expr.jump (Prod.fst Js) (Arg.imm 1, ())))
      Blocks.nil)
      fun Js => Expr.jump (Prod.fst Js) (Arg.imm 1, Arg.var (BitVec.ofNat 64 s.core.tmp_len - 1),
        ()))
      m := by
  have htl_lt : s.core.tmp_len < 2 ^ 64 := by omega
  have hone : (1 : BitVec 64).toNat = 1 := rfl
  have hmi_eq : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat = s.core.tmp_len - 1 := by
    rw [s12c_la_bv64_sub1_toNat (x := BitVec.ofNat 64 s.core.tmp_len)
      (by rw [bv64_ofNat_toNat (by omega)]; omega), bv64_ofNat_toNat (by omega)]
  c0_to_group
  refine wp_loop_inv (ts := [i64, i64])
    (fun (lo, hi, ()) m2 => ∃ t2 : List (BitVec 32), 1 ≤ lo.toNat ∧
      hi.toNat < s.core.tmp_len ∧ S12cTpi s.core.tmp t2 s.core.tmp_len ∧
      (FullMem c { s with core := { s.core with tmp := t2 } } ⋆ R) m2)
    (fun (lo, hi, ()) _ => hi.toNat + 1 - lo.toNat) ?_ ?_
  · intro J hJ
    c0_steps
    exact hJ _ m ⟨s.core.tmp, by decide,
      by show (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat < _; omega, s12cTpi_refl _ _, hm⟩
  intro J ⟨lo, hi, ⟨⟩⟩ m2 ⟨t2, hlo, hhi, ht2, hm2⟩ ih
  have ht2l := ht2.1
  c0_split
  · have hlh : lo.toNat < hi.toNat := by bv_omega
    have hlo_t : lo.toNat < t2.length := by omega
    have hhi_t : hi.toNat < t2.length := by omega
    c0_clean; c0_steps
    refine ih (lo + 1, hi - 1, ()) m ?_ ⟨_, by bv_omega, by bv_omega,
      s12cTpi_swap ht2 hlo (by omega) (by omega) hhi (by omega) hlo_t hhi_t, hm⟩
    dsimp only; bv_omega
  refine wp_loop_inv (ts := [i64])
    (fun (rb, ()) m3 => ∃ t3 : List (BitVec 32), 1 ≤ rb.toNat ∧
      rb.toNat ≤ s.core.tmp_len ∧ S12cTpi s.core.tmp t3 s.core.tmp_len ∧
      (FullMem c { s with core := { s.core with tmp := t3 } } ⋆ R) m3)
    (fun (rb, ()) _ => s.core.tmp_len - rb.toNat) ?_ ?_
  · intro J hJ
    c0_steps
    exact hJ _ m2 ⟨t2, by decide, by omega, ht2, hm2⟩
  intro J3 ⟨rb, ⟨⟩⟩ m3 ⟨t3, hrb1, hrbn, ht3, hm3⟩ ih3
  have ht3l := ht3.1
  have ht3_lt := s12cTpi_lt ht3 (by omega) hlits
  c0_split
  · have hrb : rb.toNat < s.core.tmp_len := by bv_omega
    have hrb_t : rb.toNat < t3.length := by omega
    have hx_lt : (t3[rb.toNat]'hrb_t).toNat < 2 * s.core.cur_vars := by
      have := ht3_lt rb.toNat hrb
      rwa [List.getElem?_eq_getElem hrb_t, Option.getD_some] at this
    c0_clean; c0_steps
    refine wp_loop_inv (ts := [i64])
      (fun (re, ()) m4 => rb.toNat < re.toNat ∧ re.toNat ≤ s.core.tmp_len ∧
        (FullMem c { s with core := { s.core with tmp := t3 } } ⋆ R) m4)
      (fun (re, ()) _ => s.core.tmp_len - re.toNat) ?_ ?_
    · intro J hJ
      c0_steps
      exact hJ _ m3 ⟨by bv_omega, by bv_omega, hm3⟩
    intro J4 ⟨re, ⟨⟩⟩ m4 ⟨hre1, hre2, hm4⟩ ih4
    refine wp_join_group (ts := [])
      (fun () m5 => (FullMem c { s with core := { s.core with tmp := t3 } } ⋆ R) m5) ?_ ?_
    · rintro _ ⟨⟩ m5 hm5
      c0_clean; c0_to_group
      refine wp_loop_inv (ts := [i64, i64])
        (fun (a, b, ()) m6 => ∃ t4 : List (BitVec 32), rb.toNat ≤ a.toNat ∧
          b.toNat < re.toNat ∧ S12cTpi s.core.tmp t4 s.core.tmp_len ∧
          (FullMem c { s with core := { s.core with tmp := t4 } } ⋆ R) m6)
        (fun (a, b, ()) _ => b.toNat + 1 - a.toNat) ?_ ?_
      · intro J hJ
        c0_steps
        exact hJ _ m5 ⟨t3, Nat.le_refl _, by bv_omega, ht3, hm5⟩
      intro J5 ⟨a, b, ⟨⟩⟩ m6 ⟨t4, ha, hb, ht4, hm6⟩ ih5
      have ht4l := ht4.1
      c0_split
      · have hab : a.toNat < b.toNat := by bv_omega
        have ha_t : a.toNat < t4.length := by omega
        have hb_t : b.toNat < t4.length := by omega
        c0_clean; c0_steps
        refine ih5 (a + 1, b - 1, ()) m ?_ ⟨_, by bv_omega, by bv_omega,
          s12cTpi_swap ht4 (by omega) (by omega) (by omega) (by omega) (by omega) ha_t hb_t, hm⟩
        dsimp only; bv_omega
      · c0_clean; c0_steps
        refine ih3 (re, ()) m6 ?_ ⟨t4, by omega, hre2, ht4, hm6⟩
        dsimp only; omega
    · intro Jx hJx
      c0_clean; c0_split
      · have hre : re.toNat < s.core.tmp_len := by bv_omega
        have hre_t : re.toNat < t3.length := by omega
        have hy_lt : (t3[re.toNat]'hre_t).toNat < 2 * s.core.cur_vars := by
          have := ht3_lt re.toNat hre
          rwa [List.getElem?_eq_getElem hre_t, Option.getD_some] at this
        c0_clean; c0_steps
        all_goals first
          | exact hJx () m4 hm4
          | exact ih4 (re + 1, ()) m4 (by dsimp only; bv_omega) ⟨by bv_omega, by bv_omega, hm4⟩
      · c0_clean; c0_steps
        exact hJx () m4 hm4
  · c0_clean; c0_steps
    exact hJr m3 ⟨t3, ht3, hm3⟩

private theorem s12c_ins_body_wp {Γ : Env} {Q : Post [i64]} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {t2 : List (BitVec 32)} {i : BitVec 64}
    {m2 : Mem 64} (J : Cont [i64])
    (hi : i.toNat < s.core.tmp_len) (hi2 : 2 ≤ i.toNat) (ht2 : S12cTpi s.core.tmp t2 s.core.tmp_len)
    (hmax2 : ∀ k, 1 ≤ k → k < i.toNat →
      s12cLv s.core.lvl (t2[k]?.getD 0#32) ≤ s12cLv s.core.lvl (t2[1]?.getD 0#32))
    (hm2 : (FullMem c { s with core := { s.core with tmp := t2 } } ⋆ R) m2)
    (htl_cv : s.core.tmp_len ≤ s.core.cur_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (htmp_len_arr : s.core.tmp.length = c.max_vars) (hll : s.core.lvl.length = c.max_vars)
    (hmv : c.max_vars < 2 * 2 ^ 28)
    (hlits : ∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (ih : ∀ (i' : BitVec 64) (m' : Mem 64), s.core.tmp_len - i'.toNat < s.core.tmp_len - i.toNat →
      (∃ t2' : List (BitVec 32), 2 ≤ i'.toNat ∧ i'.toNat ≤ s.core.tmp_len ∧
        S12cTpi s.core.tmp t2' s.core.tmp_len ∧
        (∀ k, 1 ≤ k → k < i'.toNat →
          s12cLv s.core.lvl (t2'[k]?.getD 0#32) ≤ s12cLv s.core.lvl (t2'[1]?.getD 0#32)) ∧
        (FullMem c { s with core := { s.core with tmp := t2' } } ⋆ R) m') → J (i', ()) m') :
    wp Γ Q X
      (Expr.load i32 (Arg.var (c.pTmp + i * 4)) fun ld =>
      Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
      Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p_1 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var (Prod.fst p),
        Arg.var (Prod.fst p_1), ()) }
      fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p),
        Arg.imm 4, ()) } fun p =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.pLevel,
        Arg.var (Prod.fst p), ()) }
      fun p =>
      Expr.load i32 (Arg.var (Prod.fst p)) fun ld_1 =>
      Expr.group (sig := [[i64]])
      (fun Js =>
      Blocks.cons
      (fun p =>
      Expr.group (sig := [[]])
      (fun _ =>
      Blocks.cons
      (fun _ =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p), Arg.imm 4, ()) }
      fun p =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p), ()) }
      fun p =>
      Expr.store (Arg.var ld) (Arg.var (Prod.fst p))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var i, Arg.imm 1, ()) }
      fun p => Expr.jump J (Arg.var (Prod.fst p), ())))
      Blocks.nil)
      fun Js_1 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_2 =>
      Expr.jnz (Arg.var (Prod.fst p_2))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_3 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p_3), Arg.imm 4, ()) }
      fun p_4 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_4), ()) }
      fun p_5 =>
      Expr.load i32 (Arg.var (Prod.fst p_5)) fun ld =>
      Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) }
      fun p_6 =>
      Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
      fun p_7 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.lshr i64,
        args := (Arg.var (Prod.fst p_6), Arg.var (Prod.fst p_7), ()) }
      fun p_8 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p_8), Arg.imm 4, ()) }
      fun p_9 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pLevel, Arg.var (Prod.fst p_9), ()) }
      fun p_10 =>
      Expr.load i32 (Arg.var (Prod.fst p_10)) fun ld =>
      Expr.let_
      { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (Eq.refl Ty.bool),
        args := (Arg.var ld, Arg.var ld_1, ()) }
      fun p_11 =>
      Expr.jnz (Arg.var (Prod.fst p_11))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var (Prod.fst p), Arg.imm 4, ()) }
      fun p_12 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_12), ()) }
      fun p_13 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p_14 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.mul i64,
        args := (Arg.var (Prod.fst p_14), Arg.imm 4, ()) }
      fun p_15 =>
      Expr.let_
      { sig := [i64, i64], code := OpCode.add i64,
        args := (Arg.var c.pTmp, Arg.var (Prod.fst p_15), ()) }
      fun p_16 =>
      Expr.load i32 (Arg.var (Prod.fst p_16)) fun ld =>
      Expr.store (Arg.var ld) (Arg.var (Prod.fst p_13))
      (Expr.let_
      { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var (Prod.fst p), Arg.imm 1, ()) }
      fun p => Expr.jump (Prod.fst Js) (Arg.var (Prod.fst p), ())))
      (Expr.jump (Prod.fst Js_1) ()))
      (Expr.jump (Prod.fst Js_1) ()))
      Blocks.nil)
      fun Js => Expr.jump (Prod.fst Js) (Arg.var i, ()))
      m2 := by
  have ht2l := ht2.1
  have ht2_lt := s12cTpi_lt ht2 (by omega) hlits
  have hi_t : i.toNat < t2.length := by omega
  have hx_lt : (t2[i.toNat]'hi_t).toNat < 2 * s.core.cur_vars := by
    have := ht2_lt i.toNat hi
    rwa [List.getElem?_eq_getElem hi_t, Option.getD_some] at this
  c0_clean; c0_steps
  refine wp_loop_inv (ts := [i64])
    (fun (j, ()) m3 => ∃ t3 : List (BitVec 32), 1 ≤ j.toNat ∧ j.toNat ≤ i.toNat ∧
      t3.length = s.core.tmp.length ∧ t3[0]? = s.core.tmp[0]? ∧
      ((t3.set j.toNat (t2[i.toNat]'hi_t)).take s.core.tmp_len).Perm
        (s.core.tmp.take s.core.tmp_len) ∧
      (∀ k, 1 ≤ k → k ≤ i.toNat → k ≠ j.toNat →
        s12cLv s.core.lvl (t3[k]?.getD 0#32) ≤ s12cLv s.core.lvl (t2[1]?.getD 0#32)) ∧
      (1 < j.toNat →
        s12cLv s.core.lvl (t3[1]?.getD 0#32) = s12cLv s.core.lvl (t2[1]?.getD 0#32)) ∧
      (j.toNat = 1 →
        s12cLv s.core.lvl (t2[1]?.getD 0#32) < s12cLv s.core.lvl (t2[i.toNat]'hi_t)) ∧
      (FullMem c { s with core := { s.core with tmp := t3 } } ⋆ R) m3)
    (fun (j, ()) _ => j.toNat) ?_ ?_
  · intro J2 hJ2
    c0_steps
    refine hJ2 _ m2 ⟨t2, by omega, Nat.le_refl _, ht2l, ht2.2.1, ?_,
      fun k hk1 hk2 hk3 => hmax2 k hk1 (by omega), fun _ => rfl, fun h => by omega, hm2⟩
    rw [List.set_getElem_self]; exact ht2.2.2
  intro J2 ⟨j, ⟨⟩⟩ m3 ⟨t3, hj1, hji, ht3l, ht30, hp3, hA, hB, hC, hm3⟩ ih2
  have hj_t : j.toNat < t3.length := by omega
  have hjm1 : (j - 1).toNat + 1 = j.toNat := by bv_omega
  refine wp_join_group (ts := [])
    (fun () m4 => (FullMem c { s with core := { s.core with tmp := t3 } } ⋆ R) m4 ∧
      (j.toNat = 1 ∨ s12cLv s.core.lvl (t2[i.toNat]'hi_t) ≤
        s12cLv s.core.lvl (t3[(j - 1).toNat]?.getD 0#32))) ?_ ?_
  · rintro _ ⟨⟩ m4 ⟨hm4, hexit⟩
    c0_clean; c0_steps
    have hi1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
    refine ih (i + 1) m ?_ ⟨t3.set j.toNat (t2[i.toNat]'hi_t), by omega, by omega,
      ⟨by simp [ht3l], by rw [List.getElem?_set_ne (by omega)]; exact ht30, hp3⟩, ?_, hm⟩
    · omega
    · rw [hi1]
      exact s12c_ins_exit hjm1 hji (by omega) hA hB hC hexit
  · intro Jx hJx
    c0_clean; c0_split
    · have hj2 : 1 < j.toNat := by bv_omega
      have hb3 : ∀ k < s.core.tmp_len, (((t3.set j.toNat (t2[i.toNat]'hi_t)))[k]?.getD
          0#32).toNat < 2 * s.core.cur_vars :=
        s12cTpi_lt ⟨by simp [ht3l], by rw [List.getElem?_set_ne (by omega)]; exact ht30, hp3⟩
          (by omega) hlits
      have hjm1_t : (j - 1).toNat < t3.length := by omega
      have hprev_lt : (t3[(j - 1).toNat]'hjm1_t).toNat < 2 * s.core.cur_vars := by
        have := hb3 (j - 1).toNat (by omega)
        rwa [List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hjm1_t,
          Option.getD_some] at this
      have hjm1n : (2 ^ 64 - 1 + j.toNat) % 2 ^ 64 = (j - 1).toNat := by bv_omega
      c0_clean; c0_steps
      · have hjt' : (2 ^ 64 - 1 + j.toNat) % 2 ^ 64 < t3.length := by omega
        have hcond := s12c_lt_of_lvl (lvl := s.core.lvl) hjm1n hjt' (s12c_lshr1 _) (s12c_lshr1 _) hc
        have hv := s12c_getElem?_of_idx hjm1n hjt'
        obtain ⟨hA', hB', hC'⟩ :=
          s12c_ins_step hjm1 hj2 hji (by omega) hA hB hcond (t3[_]'hjt') hv
        refine ih2 (j - 1, ()) m (by dsimp only; omega) ⟨_, by omega, by omega,
          by simp [ht3l], by rw [List.getElem?_set_ne (by omega)]; exact ht30,
          s12c_shift' hjm1 (by omega) (by omega) (by omega) hv hp3, hA', hB', hC', hm⟩
      · exact hJx () m3 ⟨hm3, Or.inr (s12c_le_of_lvl (lvl := s.core.lvl) hjm1n (by omega)
          (s12c_lshr1 _) (s12c_lshr1 _) hc)⟩
    · c0_clean; c0_steps
      exact hJx () m3 ⟨hm3, Or.inl (by bv_omega)⟩

private def S12cAddClPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (nlvl : BitVec 64) (tmp_sw : List (BitVec 32)) (vals_bt : List (BitVec 8))
    (lvl_bt trl_bt : List (BitVec 32)) (te_bt : Nat) (sg : FullState) : Prop :=
  FullSparseInvW c F0 F_cur sg ∧ sg.core.cur_level = nlvl.toNat ∧
  sg.core.cur_vars = s.core.cur_vars ∧ sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  sg.core.tmp = tmp_sw ∧ sg.core.tmp_len = s.core.tmp_len ∧
  sg.core.vals = vals_bt ∧ sg.core.lvl = lvl_bt ∧ sg.core.trl = trl_bt ∧
  sg.core.trail_end = te_bt ∧ sg.scratch.work_stk2 = s.scratch.work_stk2

private def S12cNrSpec (F_cur : List (List Nat)) (s : FullState) (uip wm : BitVec 32)
    (tmp_sw : List (BitVec 32)) (sac : FullState) (r_ac : BitVec 64) : Prop :=
  r_ac = 0xFFFFFFFF#64 ∨
  (r_ac ≠ 0xFFFFFFFF#64 ∧
    if r_ac = 0xFFFFFFFE#64 then
      (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat, wm.toNat])
    else
      r_ac.toNat < 2 ^ 31 - 1 ∧
      r_ac.toNat ∈ fullArenaClauseRefs sac ∧
      fullArenaClauseGarb sac r_ac.toNat = false ∧
      (∀ q ∈ fullArenaClauseLits sac r_ac.toNat,
        q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat) ∧
      uip.toNat ∈ fullArenaClauseLits sac r_ac.toNat)

/-- Generalized Step-12C `full_learn_clause_m6` taking canonical `Full.fullReduceSpec (h, true, ())`
directly for `"full_reduce_purge_c0"`, parametrically in `Γ` and `X`. -/
theorem full_learn_clause_m6_step12c_full_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hRedPurge : ∀ h m Q X, Full.fullReduceSpec (h, true, ()) m Q X →
      Γ "full_reduce_purge_c0" [i64] [i64] (h, ()) m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ args m Q X, step10LearnClauseM6Spec args m Q X →
      Func.wp Γ fidStep12CLearnClauseM6Fn.body args m Q X := by
  intro ⟨h, glue, ⟨⟩⟩ m Q X hspec
  rcases step10LearnClauseM6Spec_elim hspec with
    ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext, hs_c, hcur_pos, htl1,
    htl_cv, htmp_nd, htmp_vals, htmp_lvls, hent, hm0, hQ⟩
  have hs := s12c_canon_to_laOtfsInv hs_c
  have hcl := hs.1.core_ok
  have hw := hs.2.1
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hcur_le := hw.cur_level_le
  have hte_le := hcl.trail_end_le
  have hcv_le := hcl.cur_vars_le
  have htmp_len_arr := hcl.tmp_len_arr
  have huip_in : 0 < s.core.tmp.length := by omega
  let uip := s.core.tmp[0]'huip_in
  have huip_0 : s.core.tmp[0]? = some uip := List.getElem?_eq_getElem huip_in
  have huip_lt : uip.toNat < 2 * s.core.cur_vars := by
    have := (htmp_vals 0 htl1).1; rwa [huip_0, Option.getD_some] at this
  unfold Func.wp fidStep12CLearnClauseM6Fn full_learn_clause_m6_body
  dsimp only
  refine wp_m6Hdr_focus_frame hm0 fun hm => ?_
  let Rext : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R
  change (FullMem c s ⋆ Rext) m at hm
  c0_clean; c0_split
  · have htl_is1 : s.core.tmp_len = 1 := by bv_omega
    have hent_unit : (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat]) := by
      rwa [htl_is1, s12c_tmp_take1_eq huip_in huip_0] at hent
    c0_to_group; c0_call hBt
    refine ⟨c, s, Rext, rfl, hs.1, by omega, fun _ => by omega, hw.trail_lits_lt, hm, ?_⟩
    intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt s_bt
      hbt_len hbt_te _ hbt_cl hbt_pres _ _ _ _ hbt_otfs hm_bt
    have hcl_0 : cl' = 0 := by
      rw [hbt_cl, show (0 : BitVec 64).toNat = 0 from rfl, Nat.min_zero]
    have hbt_w : FullWitnessInv c F0 F_cur s_bt.core := hbt_otfs F0 F_cur hs_c.2.1 (by omega)
    have hbt_sparse := fullBacktrack_preserves_fullSparseW hs hbt_len hbt_w rfl rfl rfl rfl rfl
      hbt_pres.1
    have huip_vlen : uip.toNat < vals'.length := by
      have hvl := hbt_len.core_ok.vals_len; dsimp only [s_bt] at hvl; omega
    c0_clean; c0_split
    · c0_clean; c0_steps
      exact hQ 0#64 ext s_bt m_bt hext hbt_len (Or.inl rfl) rfl (Nat.le_refl _) hbt_pres.2.2.1
        (fun h => by cases h) (fun _ => hbt_sparse) (fun h => by cases h)
        (fullM6HdrMem_unfocus hm_bt)
    · have huip_z : vals'[uip.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]
        exact (by assumption : s_bt.core.vals[s.core.tmp[0].toNat] = 0#8)
      have hbt_te_lt : te' < c.max_vars := by
        have := hbt_w.trail_end_lt_of_unassigned huip_lt huip_z; dsimp only [s_bt] at this; omega
      c0_to_group; c0_call hAsgn
      refine ⟨c, s_bt, Rext, rfl, hbt_len, hm_bt, ?_⟩
      rw [ite_eq_right (fun h => by
        dsimp only [s_bt] at h
        rw [show s.core.tmp[0] = uip from rfl] at h
        simp only [huip_z, ne_eq, not_true_eq_false, or_false] at h; omega)]
      intro v rsn_let unfl_let flags' unass'' phases' m_f hfll hph s_f0 hm_f
      have hrsn_let : rsn_let = 0xFFFFFFFF#32 := ite_eq_left rfl
      have hunfl_let : unfl_let = s_bt.core.unflushed + 1#64 := ite_eq_left rfl
      c0_clean; c0_steps
      let s_fin : FullState :=
        { s_bt with
          core :=
            { s_bt.core with
              vals := (vals'.set uip.toNat 1#8).set (uip.toNat ^^^ 1) 0xFF#8
              flags := flags', lvl := lvl'.set (uip.toNat / 2) 0#32
              rsns := rsns'.set (uip.toNat / 2) 0xFFFFFFFF#32
              trl := trl'.set te' uip
              trail_pos := tp'.set (uip.toNat / 2) (BitVec.ofNat 32 te')
              trail_end := te' + 1, unassigned := unass''
              unflushed := s_bt.core.unflushed + 1#64 }
          scratch := { sc' with phases := phases' } }
      have hsc_f : s_fin.scratch.LengthsOk c := { hbt_len.scratch_ok with phases_len := hph }
      have ⟨hfin_len, hfin_w⟩ := chronoAssign_preserves_fullWitness hbt_w hbt_len hsc_f
        (rsn := 0xFFFFFFFF#32) (unassigned' := unass'') (unflushed' := s_bt.core.unflushed + 1#64)
        hfll huip_lt huip_z (Nat.zero_le _) (fun h => by omega) (fun _ => hent_unit)
        (fun h _ => by omega) (fun h _ _ => by omega)
      have hfin_sparse : FullSparseInvW c F0 F_cur s_fin :=
        ⟨hfin_len, hfin_w,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.2.2⟩
      have hm_f' : (FullMem c s_fin ⋆ Rext) m_f := by
        simpa only [s_fin, s_f0, s_bt, v, hrsn_let, hunfl_let,
          show (0 : BitVec 32) = 0#32 from rfl, show s.core.tmp[0] = uip from rfl] using hm_f
      exact hQ 1#64 ext s_fin m_f hext hfin_len (Or.inr (Or.inl rfl)) rfl (Nat.le_refl _)
        (by dsimp only [s_fin, s_bt]; exact hbt_pres.2.2.1) (fun h => by cases h)
        (fun h => by cases h)
        (fun _ => ⟨hfin_sparse, by dsimp only [s_fin, s_bt]; omega⟩) (fullM6HdrMem_unfocus hm_f')
  · have htl_ge2 : 2 ≤ s.core.tmp_len := by
      have hne : s.core.tmp_len ≠ 1 := by
        intro h1; have heq : BitVec.ofNat 64 s.core.tmp_len = 1#64 := by rw [h1]
        contradiction
      omega
    have hmi_eq : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat = s.core.tmp_len - 1 := by
      rw [s12c_la_bv64_sub1_toNat (x := BitVec.ofNat 64 s.core.tmp_len)
        (by rw [bv64_ofNat_toNat (by omega)]; omega), bv64_ofNat_toNat (by omega)]
    have hmi_tmp : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat < s.core.tmp.length := by
      rw [hmi_eq]; omega
    have htl_lt : s.core.tmp_len < 2 ^ 64 := by omega
    have hone : (1 : BitVec 64).toNat = 1 := rfl
    have htl_bv : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := bv64_ofNat_toNat htl_lt
    c0_clean; c0_to_group
    refine wp_join_group (ts := []) (fun () m1 => ∃ t1 : List (BitVec 32),
        S12cTpi s.core.tmp t1 s.core.tmp_len ∧
        (FullMem c { s with core := { s.core with tmp := t1 } } ⋆ Rext) m1) ?_ ?_
    rotate_left
    · intro Jr hJr
      c0_split
      · have htl3 : 2 < s.core.tmp_len := by
          simp only [Nat.mod_eq_of_lt htl_lt] at hc; omega
        exact s12c_rev_phase_wp Jr hm htl3 htl_cv hcv_le htmp_len_arr hcl.lvl_len hmv
          (fun k hk => (htmp_vals k hk).1) (fun m' h => hJr () m' h)
      · c0_steps
        exact hJr () m ⟨s.core.tmp, s12cTpi_refl _ _, hm⟩
    rintro _ ⟨⟩ m1 ⟨t1, ht1, hm1⟩
    c0_clean; c0_to_group
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) m2 => ∃ t2 : List (BitVec 32), 2 ≤ i.toNat ∧ i.toNat ≤ s.core.tmp_len ∧
        S12cTpi s.core.tmp t2 s.core.tmp_len ∧
        (∀ k, 1 ≤ k → k < i.toNat →
          s12cLv s.core.lvl (t2[k]?.getD 0#32) ≤ s12cLv s.core.lvl (t2[1]?.getD 0#32)) ∧
        (FullMem c { s with core := { s.core with tmp := t2 } } ⋆ Rext) m2)
      (fun (i, ()) _ => s.core.tmp_len - i.toNat) ?_ ?_
    · intro J hJ
      c0_steps
      refine hJ _ m1 ⟨t1, by decide, htl_ge2, ht1, fun k hk1 hk2 => ?_, hm1⟩
      have hk : k = 1 := by
        have : (2 : BitVec 64).toNat = 2 := rfl
        omega
      subst hk; exact Nat.le_refl _
    intro J ⟨i, ⟨⟩⟩ m2 ⟨t2, hi2, hin, ht2, hmax2, hm2⟩ ih
    have ht2l := ht2.1
    have hll := hcl.lvl_len
    c0_clean; c0_split
    · exact s12c_ins_body_wp J (by bv_omega) hi2 ht2 hmax2 hm2 htl_cv hcv_le htmp_len_arr hll hmv
          (fun k hk => (htmp_vals k hk).1) (fun i' m' h1 h2 => ih (i', ()) m' h1 h2)
    have hi_eq : i.toNat = s.core.tmp_len := by bv_omega
    obtain ⟨hsw_iff, hsw_mem, hsw_nd, hsw_0, ⟨jw, hjw1, hjwn, hjw_eq⟩, hle_all⟩ :=
      s12c_final_props (lvl := s.core.lvl) ht2 htl_ge2 (by omega) huip_0 htmp_nd
        (fun k hk1 hk2 => hmax2 k hk1 (by omega))
    have h1_t : 1 < t2.length := by omega
    have hsw_1 : t2[1]? = some (t2[1]'h1_t) := List.getElem?_eq_getElem h1_t
    have hwm_getD : t2[1]?.getD 0#32 = t2[1]'h1_t := by rw [hsw_1, Option.getD_some]
    rw [hwm_getD] at hjw_eq
    have hmi_post := htmp_lvls jw hjw1 hjwn
    have hwm_vals := htmp_vals jw hjwn
    rw [hjw_eq] at hmi_post hwm_vals
    have hwm_lt : (t2[1]'h1_t).toNat < 2 * s.core.cur_vars := hwm_vals.1
    have hwm_v_lt : (t2[1]'h1_t).toNat / 2 < s.core.lvl.length := by rw [hcl.lvl_len]; omega
    have hml_pos : 0 < (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat := hmi_post.1
    have hml_lt : (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat < s.core.cur_level :=
      hmi_post.2.1
    have hidx1_lt : ((t2[1]'h1_t).setWidth 64 >>> 1).toNat < s.core.lvl.length := by
      rw [s12c_lshr1]; exact hwm_v_lt
    have hml_get : (s.core.lvl[((t2[1]'h1_t).setWidth 64 >>> 1).toNat]'hidx1_lt).toNat =
        (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat :=
      (s12cLv_of_idx (s12c_lshr1 _) hidx1_lt).symm
    c0_clean; c0_to_group
    refine wp_join_group (ts := [i64]) (fun (ml_v, ()) m_ml =>
        m_ml = m2 ∧ ml_v =
          BitVec.ofNat 64 (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat) ?_ ?_
    rotate_left
    · intro Jml hJml; c0_split
      c0_steps
      have hml_set : BitVec.setWidth 64
          (s.core.lvl[((t2[1]'h1_t).setWidth 64 >>> 1).toNat]'hidx1_lt) =
          BitVec.ofNat 64 (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat := by
        apply BitVec.eq_of_toNat_eq
        rw [bv32_setWidth64_toNat, hml_get, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hml_set]
      exact hJml _ m2 ⟨rfl, rfl⟩
    rintro _ ⟨ml_v, ⟨⟩⟩ m_ml ⟨hm_ml, rfl⟩
    rw [hm_ml]
    have hwm_get : ∀ j, 1 ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(t2[1]'h1_t).toNat / 2]?.getD 0#32).toNat :=
      fun j hj1 hj2 => by
        have := hle_all j hj1 hj2; unfold s12cLv at this; rwa [hwm_getD] at this
    clear ih hmax2 hi2 hin hi_eq hc hml_get hidx1_lt hwm_v_lt hmi_post hwm_vals ht1 hm1
      hle_all hwm_getD
    generalize t2[1]'h1_t = wm at hsw_1 hwm_lt hml_pos hml_lt hjw_eq hwm_get ⊢
    generalize (s.core.lvl[wm.toNat / 2]?.getD 0#32).toNat = max_lvl at hml_pos hml_lt hwm_get ⊢
    let tmp_sw := t2
    let s_sw : FullState := { s with core := { s.core with tmp := tmp_sw } }
    have hm_sw' : (FullMem c s_sw ⋆ Rext) m2 := hm2
    have hsw_len : s_sw.LengthsOk c :=
      ⟨{ hcl with tmp_len_arr := by simp [s_sw, tmp_sw, ht2l, htmp_len_arr] }, hs.1.scratch_ok⟩
    have hsw_inv : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s_sw :=
      ⟨hsw_len, FullLearnAnaHelpers.FullOtfsWitnessInv.with_tmp hw tmp_sw, hs.2.2.1,
        hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
    have hsw_inv_c : FullOtfsInvW c F0 F_cur s_sw := s12c_laOtfsInv_to_canon hsw_inv
    have hent_sw : (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((tmp_sw.take s.core.tmp_len).map BitVec.toNat)) :=
      entails_of_mem_or_false hent fun l hl => Or.inl ((hsw_iff l).mpr hl)
    have hsw_lits_lt : ∀ l ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
        l < 2 * s.core.cur_vars := fun l hl => by
      rcases hsw_mem l hl with rfl | ⟨j, hj1, hj2, hjeq⟩
      · exact huip_lt
      · rw [← hjeq]; exact (htmp_vals j hj2).1
    have htmp_sw_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars := by
      intro k hk
      have hlen_sw : k < tmp_sw.length := by simp [tmp_sw, ht2l, htmp_len_arr]; omega
      have hmem : (tmp_sw[k]?.getD 0#32).toNat ∈
          (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
        rw [List.mem_map]
        refine ⟨tmp_sw[k]'hlen_sw, List.mem_iff_getElem.mpr ⟨k, by
          rw [List.length_take]; omega, by rw [List.getElem_take]⟩, ?_⟩
        rw [List.getElem?_eq_getElem hlen_sw, Option.getD_some]
      have := hsw_lits_lt _ hmem; omega
    c0_to_group; c0_call hDnl
    have hml_bv64 : (BitVec.ofNat 64 max_lvl).toNat = max_lvl := bv64_ofNat_toNat (by omega)
    refine ⟨c, s_sw, Rext, rfl, hsw_len, by dsimp [s_sw]; omega, hm_sw', fun nlvl _ hnlvl_pos => ?_⟩
    obtain ⟨hnlvl_ge, hnlvl_lt⟩ :=
      hnlvl_pos hcur_pos (by dsimp [s_sw]; rw [hml_bv64]; exact hml_lt)
    dsimp only [s_sw] at hnlvl_ge hnlvl_lt
    rw [hml_bv64] at hnlvl_ge
    c0_to_group; c0_call hBt
    refine ⟨c, s_sw, Rext, rfl, hsw_len, by dsimp [s_sw]; omega,
      fun _ => by have := hcl.cur_vars_le; omega, hsw_inv.2.1.trail_lits_lt, hm_sw', ?_⟩
    intro vals_bt lvl_bt rsns_bt trl_bt tp_bt te_bt prop_bt cl_bt unass_bt sc_bt m_bt s_bt
      hbt_len hbt_te_le hbt_prop_le hbt_cl hbt_pres hbt_ss _ hbt_keep _ hbt_otfs hm_bt
    have hcl_bt : cl_bt = nlvl.toNat := by dsimp [s_sw] at hbt_cl; omega
    have hbt_w : FullWitnessInv c F0 F_cur s_bt.core := hbt_otfs F0 F_cur hsw_inv_c.2.1 hnlvl_lt
    have hbt_sparse := fullBacktrack_preserves_fullSparseW hsw_inv hbt_len hbt_w rfl rfl rfl rfl
      rfl hbt_pres.1
    have ⟨hkeep_v, hkeep_l⟩ := hbt_keep ⟨F0, F_cur, Or.inr hsw_inv_c.2.1⟩
    have hlow_on_bt : ∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ idx < te_bt, (trl_bt[idx]?.getD 0#32).toNat = (s.core.tmp[j]?.getD 0#32).toNat ^^^ 1 ∧
          (lvl_bt[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
      intro j hj1 hj2
      have hjv := htmp_vals j hj2
      have hle_ml : (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          max_lvl := hwm_get j hj1 hj2
      have hle_nl : (s_sw.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          nlvl.toNat := by dsimp only [s_sw]; omega
      have hv_bt : vals_bt[(s.core.tmp[j]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
        rw [hkeep_v _ hjv.1, ite_eq_left hle_nl]; exact hjv.2
      have hl_bt : (lvl_bt[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
        obtain ⟨i0, hi0, hi0_eq⟩ := (hsw_inv.2.1.vals_false_iff _ hjv.1).mp hjv.2
        have hdiv : (s_sw.core.trl[i0]?.getD 0#32).toNat / 2 =
            (s.core.tmp[j]?.getD 0#32).toNat / 2 := by rw [hi0_eq, fullInv_var_xor1]
        have hl_eq := hkeep_l i0 hi0
        rw [hdiv] at hl_eq; rw [hl_eq, ite_eq_left hle_nl]; exact hle_ml
      obtain ⟨idx, hidx, heq⟩ := (hbt_w.vals_false_iff _ hjv.1).mp hv_bt
      exact ⟨idx, hidx, heq, hl_bt⟩
    have hwm_on_bt : ∃ idx < te_bt,
        (trl_bt[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
        (lvl_bt[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
      simpa only [hjw_eq] using hlow_on_bt jw hjw1 hjwn
    clear hDnl hBt htmp_vals htmp_lvls hent hm_sw' hm2 hbt_ss hbt_keep hbt_otfs
      hbt_te_le hbt_prop_le hkeep_v hkeep_l
    let AddClPre := S12cAddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt
    let NrSpec := S12cNrSpec F_cur s uip wm tmp_sw
    -- Pre-add GC headroom check
    c0_to_group
    refine wp_join_group (ts := []) (fun () m_gc =>
        ∃ (ext_gc : List (BitVec 64)) (s_gc : FullState),
          M6HdrExtOk ext_gc ∧ AddClPre s_gc ∧ (FullM6HdrMem c ext_gc s_gc ⋆ R) m_gc) ?_ ?_
    · rintro _ ⟨⟩ m_gc ⟨ext_gc, s_gc, hext_gc, hgc_pre, hm_gc⟩
      have htl_tr32 : ((BitVec.ofNat 64 s.core.tmp_len).setWidth 32).toNat = s.core.tmp_len := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : s.core.tmp_len < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
      -- Local helper packaging any `full_add_clause(h, (u32)h->tmp_len, (u32)glue, true)` call
      have hAddCall : ∀ (extg : List (BitVec 64)) (sg : FullState) (mg : Mem 64)
          (k : Tup Val [i64] → Expr Val Cont [i64]),
          M6HdrExtOk extg → AddClPre sg → (FullM6HdrMem c extg sg ⋆ R) mg →
          (∀ new_ref64 s_ac m_ac,
            AddClPre s_ac → NrSpec s_ac new_ref64 → (FullM6HdrMem c extg s_ac ⋆ R) m_ac →
            wp Γ Q X (k (new_ref64, ())) m_ac) →
          wp Γ Q X
            (Expr.call (as := [i64, i32, i32, .bool]) (bs := [i64]) (rs := [i64])
              "full_add_clause"
              (Arg.var c.hdr, Arg.var ((BitVec.ofNat 64 sg.core.tmp_len).setWidth 32),
                Arg.var (glue.setWidth 32), Arg.imm true, ()) k) mg := by
        intro extg sg mg k hextg hsg_pre hm_g hk
        obtain ⟨hsp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s, htrl_s, hte_s,
          hws2_s⟩ := hsg_pre
        have hlen_s := hsp.1
        refine wp_m6Hdr_focus_frame hm_g fun hm_gf => ?_
        let Rg : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) extg ⋆ R
        change (FullMem c sg ⋆ Rg) mg at hm_gf
        refine wp_call_of_spec _ _ ?_
        dsimp only [Arg.val_var, vals]
        refine hAddCl _ _ _ _ ⟨c, F0, F_cur, sg, Rg, rfl, hlen_s, hsp.2.1, hsp.2.2.2.2.2,
          by rw [htl_s, htl_tr32]; omega,
          fun _ => by rw [htmp_s, htl_s, htl_tr32, hcv_s]; exact ⟨hsw_lits_lt, hsw_nd, hent_sw⟩,
          hm_gf, ?_⟩
        rw [htl_s, htl_tr32]
        simp only [show ¬ s.core.tmp_len < 2 by omega, ↓reduceIte]
        by_cases htl2 : s.core.tmp_len = 2
        · simp only [htl2, ↓reduceIte]
          intro r_ac wvec_a wstk_a wlen_a wu_a nb_a wsort_a m_ac hr_ac hac_len hac_w hm_ac
          let s_ac : FullState :=
            { sg with
              core := { sg.core with
                wvec := wvec_a, wstk := wstk_a, wlen := wlen_a, wusable := wu_a,
                num_binary := nb_a }
              scratch := { sg.scratch with wsort := wsort_a } }
          have hac_sp : FullSparseInvW c F0 F_cur s_ac :=
            ⟨hac_len, hac_w, hsp.2.2.1, hsp.2.2.2.1,
              Full.FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
              hsp.2.2.2.2.2⟩
          have hnr : NrSpec s_ac r_ac := by
            rcases hr_ac with rfl | rfl
            · exact Or.inl rfl
            · right; refine ⟨by decide, ?_⟩; simp only [↓reduceIte]
              have hlen2_sw : 2 ≤ tmp_sw.length := by show 2 ≤ t2.length; omega
              rw [htl2, s12c_tmp_take2_eq hlen2_sw hsw_0 hsw_1] at hent_sw
              exact hent_sw
          exact hk r_ac s_ac m_ac ⟨hac_sp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s,
            htrl_s, hte_s, hws2_s⟩ hnr (fullM6HdrMem_unfocus hm_ac)
        · simp only [htl2, ↓reduceIte]
          intro r_ac arena_a alen_a wvec_a wstk_a wlen_a wu_a fred_a ni_a nr_a wsort_a m_ac
            hr_ac hac_len hac_w hrefs_sub hnd_imp hok_a hm_ac
          let s_ac : FullState :=
            { sg with
              core := { sg.core with
                arena := arena_a, arena_len := alen_a, wvec := wvec_a, wstk := wstk_a,
                wlen := wlen_a, wusable := wu_a, first_reducible := fred_a, num_irred := ni_a,
                num_redundant := nr_a }
              scratch := { sg.scratch with wsort := wsort_a } }
          have hac_sp : FullSparseInvW c F0 F_cur s_ac :=
            ⟨hac_len, hac_w, hsp.2.2.1, hnd_imp hsp.2.2.2.1,
              Full.FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ hrefs_sub,
              hsp.2.2.2.2.2⟩
          have hnr : NrSpec s_ac r_ac := by
            rcases hr_ac with rfl | rfl
            · exact Or.inl rfl
            · obtain ⟨_, href_a, hng_a, hlits_a⟩ := hok_a rfl
              have hal_lt31 : sg.core.arena_len < 2 ^ 31 - 1 := by
                have := hlen_s.core_ok.arena_len_le; omega
              have hnr_toNat : (BitVec.ofNat 64 sg.core.arena_len).toNat = sg.core.arena_len :=
                bv64_ofNat_toNat (by omega)
              have hne_ff : BitVec.ofNat 64 sg.core.arena_len ≠ 0xFFFFFFFF#64 := fun heq => by
                have := congrArg BitVec.toNat heq; rw [hnr_toNat] at this
                have : (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1 := rfl; omega
              have hne_fe : BitVec.ofNat 64 sg.core.arena_len ≠ 0xFFFFFFFE#64 := fun heq => by
                have := congrArg BitVec.toNat heq; rw [hnr_toNat] at this
                have : (0xFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 32 - 2 := rfl; omega
              right; refine ⟨hne_ff, ?_⟩; simp only [hne_fe, ↓reduceIte, hnr_toNat]
              have hlits_eq : fullArenaClauseLits s_ac sg.core.arena_len =
                  (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
                change fullArenaClauseLits s_ac sg.core.arena_len =
                  (sg.core.tmp.take s.core.tmp_len).map BitVec.toNat at hlits_a
                rwa [htmp_s] at hlits_a
              refine ⟨hal_lt31, href_a, hng_a, fun q hq => by rwa [hlits_eq] at hq, ?_⟩
              rw [hlits_eq, List.mem_map]
              have h0_sw : 0 < tmp_sw.length := by simp only [tmp_sw]; omega
              have hu_sw : tmp_sw[0]'h0_sw = uip := by
                have := List.getElem?_eq_getElem h0_sw; rw [hsw_0] at this
                exact (Option.some.inj this).symm
              exact ⟨uip, List.mem_iff_getElem.mpr ⟨0, by rw [List.length_take]; omega,
                by rw [List.getElem_take]; exact hu_sw⟩, rfl⟩
          exact hk r_ac s_ac m_ac ⟨hac_sp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s,
            htrl_s, hte_s, hws2_s⟩ hnr (fullM6HdrMem_unfocus hm_ac)
      -- First `full_add_clause` call before retry loop:
      refine wp_m6Hdr_focus_frame hm_gc fun hm_gcf => ?_
      c0_to_group
      refine hAddCall ext_gc s_gc m_gc _ hext_gc hgc_pre (fullM6HdrMem_unfocus hm_gcf)
        fun new_ref0 s_ac0 m_ac0 h0_pre h0_nr hm_ac0 => ?_
      have hlow_bt : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
          q = uip.toNat ∨ ∃ idx < te_bt,
            (trl_bt[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
            (lvl_bt[q / 2]?.getD 0#32).toNat ≤ max_lvl := fun q hq => by
        rcases hsw_mem q hq with rfl | ⟨j, hj1, hj2, hjeq⟩
        · exact Or.inl rfl
        · right; rw [← hjeq]; exact hlow_on_bt j hj1 hj2
      clear hAddCl hsw_mem hlow_on_bt hgc_pre
      c0_to_group
      refine wp_loop_inv
        (fun (new_ref64, step, ()) mL =>
          step.toNat ≤ 3 ∧
          ∃ (ext_lp : List (BitVec 64)) (s_lp : FullState),
            M6HdrExtOk ext_lp ∧ AddClPre s_lp ∧ NrSpec s_lp new_ref64 ∧
            (FullM6HdrMem c ext_lp s_lp ⋆ R) mL)
        (fun (_, step, ()) _ => 3 - step.toNat)
        (fun JL hLoop =>
          hLoop (new_ref0, 0#64, ()) m_ac0
            ⟨Nat.zero_le _, ext_gc, s_ac0, hext_gc, h0_pre, h0_nr, hm_ac0⟩)
        (fun JL (new_ref64, step, ()) mL
            ⟨hstep_le, ext_lp, s_lp, hext_lp, hlp_pre, hlp_nr, hmL⟩ hLoop => ?_)
      refine wp_join_group (ts := [])
        (fun () m_ex => ∃ ext_ex s_ex,
          M6HdrExtOk ext_ex ∧ AddClPre s_ex ∧ NrSpec s_ex new_ref64 ∧
          (FullM6HdrMem c ext_ex s_ex ⋆ R) m_ex)
        ?_ ?_
      · rintro _ ⟨⟩ m_ex ⟨ext_ex, s_ex, hext_ex, hex_pre, hex_nr, hm_ex⟩
        simp only [Blocks.get]
        refine wp_m6Hdr_focus_frame hm_ex fun hm_exf => ?_
        let Rex : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext_ex ⋆ R
        change (FullMem c s_ex ⋆ Rex) m_ex at hm_exf
        have hQ_ex : ∀ r s' m',
            s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
            s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
            s'.scratch.work_stk2 = s.scratch.work_stk2 →
            (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
              s'.core.cur_level < s.core.cur_level) →
            (r = 0#64 → FullSparseInvW c F0 F_cur s') →
            (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
            (FullMem c s' ⋆ Rex) m' → Q (r, ()) m' :=
          fun r s' m' a1 a2 a3 a4 a5 a6 a7 a8 hm' =>
            hQ r ext_ex s' m' hext_ex a1 a2 a3 a4 a5 a6 a7 a8 (fullM6HdrMem_unfocus hm')
        exact s12c_learn_clause_post_ac_wp (c := c) (F0 := F0) (F_cur := F_cur) (s := s)
          (s_ac := s_ex) (R := Rex) (uip_lit := uip) (wm := wm) (new_ref64 := new_ref64)
          (max_lvl := max_lvl) (tmp_sw := tmp_sw) hAsgn hEsub hQ_ex
          hex_pre.1 (by rw [hex_pre.2.1]; exact hnlvl_lt) hml_pos
          (by rw [hex_pre.2.1]; omega) (by omega) hex_pre.2.2.1 hex_pre.2.2.2.1
          hex_pre.2.2.2.2.2.2.2.2.2.2 hex_pre.2.2.2.2.1 hex_pre.2.2.2.2.2.1 hsw_1 htl_ge2
          htl_cv huip_lt hwm_lt htmp_sw_lt
          (by rw [hex_pre.2.2.2.2.2.2.2.2.1, hex_pre.2.2.2.2.2.2.2.1,
                hex_pre.2.2.2.2.2.2.2.2.2.1]; exact hwm_on_bt)
          (by rw [hex_pre.2.2.2.2.2.2.2.2.1, hex_pre.2.2.2.2.2.2.2.1,
                hex_pre.2.2.2.2.2.2.2.2.2.1]; exact hlow_bt)
          hex_nr hm_exf
      · intro J_post hJ_post
        clear hAsgn hEsub hsw_1 hwm_on_bt hlow_bt
        refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
        c0_split
        · c0_split
          · have hstep_lt : step.toNat < 3 := by c0_bound
            have hstep1 : (step + 1#64).toNat = step.toNat + 1 := by c0_bound
            c0_to_group
            refine wp_join_group (ts := [])
              (fun () m_pre => ∃ ext_pre s_pre,
                M6HdrExtOk ext_pre ∧ AddClPre s_pre ∧ (FullM6HdrMem c ext_pre s_pre ⋆ R) m_pre)
              ?_ ?_
            · rintro _ ⟨⟩ m_pre ⟨ext_pre, s_pre, hext_pre, hpre_ok, hm_pre⟩
              refine wp_m6Hdr_focus_frame hm_pre fun hm_pref => ?_
              c0_steps
              refine hAddCall ext_pre s_pre m_pre _ hext_pre hpre_ok (fullM6HdrMem_unfocus hm_pref)
                fun nr' sac' mac' hsac' hnr' hmac' => ?_
              c0_steps
              exact hLoop (nr', step + 1#64, ()) mac' (by dsimp only; rw [hstep1]; omega)
                ⟨by omega, ext_pre, sac', hext_pre, hsac', hnr', hmac'⟩
            · intro J1 hJ1
              c0_split
              · c0_to_group
                refine wp_join_group (ts := [])
                  (fun () m_d => ∃ s_d : FullState, AddClPre s_d ∧
                    (FullM6HdrMem c ext_lp s_d ⋆ R) m_d)
                  ?_ ?_
                · rintro _ ⟨⟩ m_d ⟨s_d, hd_pre, hm_d⟩
                  c0_steps; exact hJ1 () m_d ⟨ext_lp, s_d, hext_lp, hd_pre, hm_d⟩
                · intro Jd hJd
                  have ⟨hlp_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl, hlp_vals, hlp_lvl,
                    hlp_trl, hlp_te, hlp_ws2⟩ := hlp_pre
                  c0_split
                  · have hlp_lay : WatchStackLayout s_lp.core := by
                      have hm_w := hlp_sp.2.1.watches
                      unfold ModeWatchesInv at hm_w
                      rw [ite_eq_left hlp_sp.2.2.2.2.2] at hm_w
                      exact hm_w.layout
                    c0_call hDefrag
                    refine ⟨c, s_lp, m6ExtMem (m6ExtAddr c.hdr) ext_lp ⋆ R,
                      rfl, hlp_sp.1, hlp_lay, hmLf, ?_⟩
                    intro wvec_d wstk_d wlen_d wsort_d m_d _ hd_len hd_lay _ hd_pres hm_d
                    let s_d : FullState :=
                      { s_lp with
                        core := { s_lp.core with
                          wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                        scratch := { s_lp.scratch with wsort := wsort_d } }
                    have hd_sp :=
                      fullWstackDefrag_preserves_fullSparseW hlp_sp hd_len hd_lay hd_pres
                    c0_steps
                    exact hJd () m_d ⟨s_d, ⟨hd_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl,
                      hlp_vals, hlp_lvl, hlp_trl, hlp_te, hlp_ws2⟩, fullM6HdrMem_unfocus hm_d⟩
                  · have hwuz : s_lp.core.wusable = 0#64 := by
                      apply BitVec.eq_of_toNat_eq; bv_omega
                    c0_steps
                    exact hJd () mL ⟨s_lp, hlp_pre, by simpa only [hwuz] using hmL⟩
              · c0_to_group
                refine wp_join_group (ts := [i64])
                  (fun (gr, ()) m_r => ∃ (ext_r : List (BitVec 64)) (s_r : FullState),
                    M6HdrExtOk ext_r ∧ FullSparseInvW c F0 F_cur s_r ∧
                    (gr = 0#64 ∨ gr = 1#64 ∨ gr = 20#64) ∧
                    s_r.core.cur_level ≤ s_lp.core.cur_level ∧
                    s_r.core.fuel.toNat ≤ s_lp.core.fuel.toNat ∧
                    s_r.core.cur_vars = s_lp.core.cur_vars ∧
                    s_r.core.tmp = s_lp.core.tmp ∧ s_r.core.tmp_len = s_lp.core.tmp_len ∧
                    s_r.scratch.work_stk2 = s_lp.scratch.work_stk2 ∧
                    (gr = 20#64 → F0.Unsat) ∧
                    (gr = 1#64 → 0 < s_r.core.cur_level →
                      s_r.core.cur_level = s_lp.core.cur_level ∧ s_r.core.vals = s_lp.core.vals ∧
                      s_r.core.lvl = s_lp.core.lvl ∧ s_r.core.trl = s_lp.core.trl ∧
                      s_r.core.trail_pos = s_lp.core.trail_pos ∧
                      s_r.core.trail_end = s_lp.core.trail_end) ∧
                    (FullM6HdrMem c ext_r s_r ⋆ R) m_r)
                  ?_ ?_
                · rintro _ ⟨gr, ⟨⟩⟩ m_r ⟨ext_r, s_r, hext_r, hr_sp, hr_dom, hr_cl, hr_fu, hr_cv,
                    hr_tmp, hr_tl, hr_ws2, hr_20, hr_pos, hm_r⟩
                  have ⟨hlp_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl, hlp_vals, hlp_lvl,
                    hlp_trl, hlp_te, hlp_ws2⟩ := hlp_pre
                  have hr_cv' : s_r.core.cur_vars = s.core.cur_vars := hr_cv.trans hlp_cv
                  have hr_fu' : s_r.core.fuel.toNat ≤ s.core.fuel.toNat :=
                    Nat.le_trans hr_fu hlp_fu
                  have hr_ws2' : s_r.scratch.work_stk2 = s.scratch.work_stk2 :=
                    hr_ws2.trans hlp_ws2
                  clear hlp_pre hlp_sp hlp_cv hlp_fu hlp_ws2
                  refine wp_m6Hdr_focus_frame hm_r fun hm_rf => ?_
                  c0_hsplit
                  · c0_hsteps
                    exact hQ 20#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inr rfl)) hr_cv'
                      hr_fu' hr_ws2'
                      (fun _ => ⟨hr_20 (by simpa [bv_c0] using hc), hr_sp, by omega⟩)
                      (fun h => by cases h) (fun h => by cases h) hm_r
                  · c0_hsplit
                    · c0_hsteps
                      exact hQ 0#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inl rfl) hr_cv' hr_fu' hr_ws2'
                        (fun h => by cases h) (fun _ => hr_sp) (fun h => by cases h) hm_r
                    · have hgr1 : gr = 1#64 := by
                        rcases hr_dom with rfl | rfl | rfl
                        · exfalso; simp [bv_c0] at hc
                        · rfl
                        · exfalso; simp [bv_c0] at hc
                      c0_hsplit
                      · c0_hsteps
                        exact hQ 1#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv'
                          hr_fu' hr_ws2' (fun h => by cases h) (fun h => by cases h)
                          (fun _ => ⟨hr_sp, by omega⟩) hm_r
                      · have hcl_eq : s_r.core.cur_level = nlvl.toNat := by
                          have hbv : BitVec.ofNat 64 s_r.core.cur_level = nlvl := by
                            simpa [bv_c0] using hc
                          have hsr_lt64 : s_r.core.cur_level < 2 ^ 64 := by
                            have := hr_sp.1.core_ok.cur_vars_le
                            have := hr_sp.2.1.cur_level_le
                            have := hr_sp.1.core_ok.trail_end_le; omega
                          have := congrArg BitVec.toNat hbv
                          rw [bv64_ofNat_toNat hsr_lt64] at this; exact this
                        have huip_r_lt : (BitVec.setWidth 64 (s.core.tmp[0]'huip_in)).toNat <
                            s_r.core.vals.length := by
                          rw [bv32_setWidth64_toNat, hr_sp.1.core_ok.vals_len]
                          change uip.toNat < 2 * c.max_vars; omega
                        c0_hsplit
                        · c0_hsteps
                          exact hQ 1#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv'
                            hr_fu' hr_ws2' (fun h => by cases h) (fun h => by cases h)
                            (fun _ => ⟨hr_sp, by omega⟩) hm_r
                        · obtain ⟨_, hr_vals, hr_lvl, hr_trl, _, hr_te⟩ :=
                            hr_pos hgr1 (by omega)
                          c0_hsteps
                          exact hJ1 () m_r ⟨ext_r, s_r, hext_r, ⟨hr_sp, hcl_eq, hr_cv', hr_fu',
                            hr_tmp.trans hlp_tmp, hr_tl.trans hlp_tl, hr_vals.trans hlp_vals,
                            hr_lvl.trans hlp_lvl, hr_trl.trans hlp_trl, hr_te.trans hlp_te,
                            hr_ws2'⟩, hm_r⟩
                · intro Jr hJr
                  c0_split
                  · c0_call hRedM6
                    refine m6ReduceSpec_of (FullM6HdrInvW.mk_inv hcfg hext_lp hlp_pre.1) hmL ?_
                    intro rr ext_r s_r m_r hr_inv hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                      hr_20 _ hr_pos hm_r
                    c0_steps
                    exact hJr (rr, ()) m_r
                      ⟨ext_r, s_r, hr_inv.extOk, hr_inv.sparseW, hr_dom, hr_cl, hr_fu, hr_cv,
                        hr_tmp, hr_tl, hr_ws2, hr_20, hr_pos, hm_r⟩
                  · c0_call hRedPurge
                    refine ⟨c, F0, F_cur, s_lp, m6ExtMem (m6ExtAddr c.hdr) ext_lp ⋆ R,
                      rfl, hlp_pre.1, hmLf, ?_⟩
                    intro rr s_r m_r hr_sp hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                      hr_20 _ hr_pos hm_r
                    c0_steps
                    exact hJr (rr, ()) m_r
                      ⟨ext_lp, s_r, hext_lp, hr_sp, hr_dom, hr_cl, hr_fu, hr_cv, hr_tmp, hr_tl,
                        hr_ws2, hr_20, hr_pos, fullM6HdrMem_unfocus hm_r⟩
          · c0_hsteps; exact hJ_post () mL ⟨ext_lp, s_lp, hext_lp, hlp_pre, hlp_nr, hmL⟩
        · c0_hsteps; exact hJ_post () mL ⟨ext_lp, s_lp, hext_lp, hlp_pre, hlp_nr, hmL⟩
    · -- Pre-add GC headroom `if` body
      clear hAddCl hAsgn hEsub hent_sw hsw_lits_lt hlow_on_bt hwm_on_bt htmp_sw_lt
        hRedPurge
      intro Jgc hJgc
      c0_to_group
      refine wp_join_group (ts := []) (fun () m_in => m_in = m_bt) ?_ ?_
      · rintro _ ⟨⟩ m_in rfl
        c0_to_group
        refine wp_join_group (ts := []) (fun () m_d => ∃ wvec_d wstk_d wlen_d wsort_d,
            let s_d : FullState :=
              { s_bt with
                core := { s_bt.core with
                  wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                scratch := { sc_bt with wsort := wsort_d } }
            FullSparseInvW c F0 F_cur s_d ∧ (FullMem c s_d ⋆ Rext) m_d) ?_ ?_
        · rintro _ ⟨⟩ m_d ⟨wvec_d, wstk_d, wlen_d, wsort_d, hd_sp, hm_d⟩
          let s_d : FullState :=
            { s_bt with
              core := { s_bt.core with
                wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
              scratch := { sc_bt with wsort := wsort_d } }
          have hd_cl : s_d.core.cur_level = nlvl.toNat := hcl_bt
          c0_to_group
          refine wp_join_group (ts := []) (fun () m_3 =>
              ∃ (ext_3 : List (BitVec 64)) (s_3 : FullState),
                M6HdrExtOk ext_3 ∧ AddClPre s_3 ∧ (FullM6HdrMem c ext_3 s_3 ⋆ R) m_3) ?_ ?_
          · rintro _ ⟨⟩ m_3 ⟨ext_3, s_3, hext_3, h3_pre, hm_3⟩
            c0_steps; exact hJgc () m_3 ⟨ext_3, s_3, hext_3, h3_pre, hm_3⟩
          · intro J3 hJ3; c0_split
            · c0_to_group; c0_call hRedM6
              refine m6ReduceSpec_of (FullM6HdrInvW.mk_inv hcfg hext hd_sp)
                (fullM6HdrMem_unfocus hm_d) ?_
              intro rr ext_r s_r m_r hr_inv hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                hr_20 _ hr_pos hm_r
              have hr_sp : FullSparseInvW c F0 F_cur s_r := hr_inv.sparseW
              have hext_r : M6HdrExtOk ext_r := hr_inv.extOk
              dsimp only [s_d, s_bt, s_sw] at hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
              dsimp only [s_d] at hr_pos
              have hr_ws2' : s_r.scratch.work_stk2 = s.scratch.work_stk2 :=
                hr_ws2.trans hbt_pres.2.2.1
              refine wp_m6Hdr_focus_frame hm_r fun hm_rf => ?_
              c0_hsplit
              · c0_hsteps
                exact hQ 20#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inr rfl)) hr_cv hr_fu
                  hr_ws2' (fun _ => ⟨hr_20 (by simpa [bv_c0] using hc), hr_sp, by omega⟩)
                  (fun h => by cases h) (fun h => by cases h) hm_r
              · c0_hsplit
                · c0_hsteps
                  exact hQ 0#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inl rfl) hr_cv hr_fu hr_ws2'
                    (fun h => by cases h) (fun _ => hr_sp) (fun h => by cases h) hm_r
                · have hrr1 : rr = 1#64 := by
                    rcases hr_dom with rfl | rfl | rfl
                    · exfalso; simp [bv_c0] at hc
                    · rfl
                    · exfalso; simp [bv_c0] at hc
                  c0_hsplit
                  · c0_hsteps
                    exact hQ 1#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv hr_fu
                      hr_ws2' (fun h => by cases h) (fun h => by cases h)
                      (fun _ => ⟨hr_sp, by omega⟩) hm_r
                  · have hcl_eq : s_r.core.cur_level = nlvl.toNat := by
                      have hbv : BitVec.ofNat 64 s_r.core.cur_level = nlvl := by
                        simpa [bv_c0] using hc
                      have hsr_lt64 : s_r.core.cur_level < 2 ^ 64 := by
                        have := hr_sp.1.core_ok.cur_vars_le
                        have := hr_sp.2.1.cur_level_le
                        have := hr_sp.1.core_ok.trail_end_le; omega
                      have := congrArg BitVec.toNat hbv
                      rw [bv64_ofNat_toNat hsr_lt64] at this; exact this
                    have huip_r_lt : (BitVec.setWidth 64 (s.core.tmp[0]'huip_in)).toNat <
                        s_r.core.vals.length := by
                      rw [bv32_setWidth64_toNat, hr_sp.1.core_ok.vals_len]
                      change uip.toNat < 2 * c.max_vars; omega
                    c0_hsplit
                    · c0_hsteps
                      exact hQ 1#64 ext_r s_r m_r hext_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv hr_fu
                        hr_ws2' (fun h => by cases h) (fun h => by cases h)
                        (fun _ => ⟨hr_sp, by omega⟩) hm_r
                    · obtain ⟨_, hr_vals, hr_lvl, hr_trl, _, hr_te⟩ :=
                        hr_pos hrr1 (by omega)
                      c0_hsteps
                      exact hJ3 () m_r ⟨ext_r, s_r, hext_r, ⟨hr_sp, hcl_eq, hr_cv, hr_fu, hr_tmp,
                        hr_tl, hr_vals, hr_lvl, hr_trl, hr_te, hr_ws2'⟩, hm_r⟩
            · c0_steps
              exact hJ3 () m_d ⟨ext, s_d, hext, ⟨hd_sp, hd_cl, rfl, Nat.le_refl _, rfl, rfl, rfl,
                rfl, rfl, rfl, hbt_pres.2.2.1⟩, fullM6HdrMem_unfocus hm_d⟩
        · intro Jdef hJdef; c0_split
          · have hbt_lay : WatchStackLayout s_bt.core := by
              have hm_w := hbt_sparse.2.1.watches
              unfold ModeWatchesInv at hm_w
              rw [ite_eq_left hbt_sparse.2.2.2.2.2] at hm_w
              exact hm_w.layout
            c0_call hDefrag
            refine ⟨c, s_bt, Rext, rfl, hbt_len, hbt_lay, hm_bt, ?_⟩
            intro wvec_d wstk_d wlen_d wsort_d m_d _ hd_len hd_lay _ hd_pres hm_d
            let s_d : FullState :=
              { s_bt with
                core := { s_bt.core with
                  wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                scratch := { sc_bt with wsort := wsort_d } }
            have hd_sp := fullWstackDefrag_preserves_fullSparseW hbt_sparse hd_len hd_lay hd_pres
            c0_steps
            exact hJdef () m_d ⟨wvec_d, wstk_d, wlen_d, wsort_d, hd_sp, hm_d⟩
          · have hwuz : s.core.wusable = 0#64 := by
              dsimp only [s_bt, s_sw] at *; apply BitVec.eq_of_toNat_eq; bv_omega
            c0_steps
            refine hJdef () m_in ⟨s_bt.core.wvec, s_bt.core.wstk, s_bt.core.wlen, sc_bt.wsort, ?_,
              ?_⟩
            · simpa only [s_bt, s_sw, hwuz] using s12c_laSparse_to_canon hbt_sparse
            · simpa only [s_bt, s_sw, hwuz] using hm_bt
      · intro J_in hJ_in; c0_split
        · c0_steps; exact hJ_in () m_bt rfl
        · c0_split
          · c0_steps; exact hJ_in () m_bt rfl
          · c0_steps
            exact hJgc () m_bt ⟨ext, s_bt, hext, ⟨s12c_laSparse_to_canon hbt_sparse, hcl_bt, rfl,
              Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, hbt_pres.2.2.1⟩,
              fullM6HdrMem_unfocus hm_bt⟩

/-- Step-12C `full_learn_clause_m6` (pre-add headroom + 3-step `defrag` / `full_reduce_m6(h, true)`
/ `full_reduce_purge_c0(h)` OOM retry ladder) satisfies `step10LearnClauseM6Spec` verbatim,
parametrically in `Γ` and `X`. -/
theorem full_learn_clause_m6_step12c_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRedM6 : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hRedPurge : ∀ a m Q X, fullReducePurgeC0Spec a m Q X →
      Γ "full_reduce_purge_c0" [i64] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ args m Q X, step10LearnClauseM6Spec args m Q X →
      Func.wp Γ fidStep12CLearnClauseM6Fn.body args m Q X :=
  full_learn_clause_m6_step12c_full_wp Γ hBt hAsgn hDnl hDefrag hRedM6
    (fun _ m Q X hs => hRedPurge _ m Q X (fullReducePurgeC0Spec_of_full hs))
    hAddCl hEsub

end LearnStep12CProof

end LeanQbe.T.Examples.Kissat.FullFidelityStep12C
