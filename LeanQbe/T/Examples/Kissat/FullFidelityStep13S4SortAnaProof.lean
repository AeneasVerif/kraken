/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-A Proofs — `full_sort_ana_qs_m6` (`PERF-R3` LSD Radix Bump Sort)

UNSAT-only `Func.wp` proof (`public section`, `0` `@[expose]` on theorems/lemmas, `0` `import all`,
`XPost`-polymorphic) for `full_sort_ana_qs_m6` (`s13SortAnaQsSpec`), cleanly split into 3 branch
theorems (`<= 280` lines each):
1. `s13_sort_ana_ins_wp`: Insertion sort (`n < 32`) via `rk = (u64 *)h->repr`.
2. `s13_sort_ana_radix_wp`: 4-pass 8-bit LSD radix sort (`n >= 32 ∧ scratch_cap >= 512`).
3. `s13_sort_ana_heap_wp`: Heapsort fallback (`full_ana_sift_m6`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open Kraken.Bedrock2.Test

section SortAnaWp

open scoped FullArenaTactics

private theorem bv64_ushr_eq_nat (w s : BitVec 64) : (w >>> s) = w >>> s.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight]

private theorem s13_pack_word_lo64 (q a : BitVec 32) :
    (((q.setWidth 64 <<< (32 : BitVec 64)) ||| a.setWidth 64).setWidth 32) = a := by
  have hsh : (q.setWidth 64 <<< (32 : BitVec 64)) = (q.setWidth 64 <<< (32 : Nat)) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft]
  rw [hsh]; exact s13_pack_word_lo q a

private theorem sep_rot4_rk {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ (B ⋆ (D ⋆ emp)))) m) : (A ⋆ B ⋆ C ⋆ D) m := by
  simp only [sep_emp] at h; exact sep_ac h

private theorem sep_rot6_rk {A B C D E F : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ (B ⋆ (D ⋆ (E ⋆ (F ⋆ emp)))))) m) : (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F) m := by
  simp only [sep_emp] at h; exact sep_ac h

private theorem sep_rot6_cnt {A B C D E F : Mem 64 → Prop} {m : Mem 64}
    (h : (E ⋆ (A ⋆ (B ⋆ (C ⋆ (D ⋆ (F ⋆ emp)))))) m) : (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F) m := by
  simp only [sep_emp] at h; exact sep_ac h

private theorem sep_rot6_ds {A B C D E F : Mem 64 → Prop} {m : Mem 64}
    (h : (D ⋆ (E ⋆ (A ⋆ (B ⋆ (C ⋆ (F ⋆ emp)))))) m) : (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F) m := by
  simp only [sep_emp] at h; exact sep_ac h

private theorem rdx_count_step_all (shift : Nat) (s_arr : List (BitVec 64))
    {cnt : List (BitVec 64)} {i : Nat} (hcnt : cnt.length = 256)
    (hi : i < s_arr.length) (hi_bd : i < 2 ^ 30)
    (hinv : ∀ b (hb : b < 256), (cnt[b]'(by omega)).toNat = rdxSeen shift s_arr i b) :
    let bv := rdxBkt shift (s_arr[i]'hi)
    let cnt' := cnt.set bv ((cnt[bv]'(by rw [hcnt]; exact rdxBkt_lt shift _)) + 1#64)
    ∀ b (hb : b < 256),
      (cnt'[b]'(by simp only [cnt', List.length_set, hcnt]; exact hb)).toNat =
        rdxSeen shift s_arr (i + 1) b := by
  intro bv cnt' b hb
  have hbv : bv < 256 := rdxBkt_lt shift _
  have hcur := hinv bv hbv
  have hseen_le : rdxSeen shift s_arr i bv ≤ i := rdxSeen_le shift s_arr i bv
  rw [rdxSeen_succ shift s_arr hi b]
  by_cases hbe : bv = b
  · subst hbe
    simp only [cnt', List.getElem_set_self]
    have heq : rdxBkt shift (s_arr[i]'hi) = bv := rfl
    rw [ite_eq_left heq, BitVec.toNat_add, hcur]
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [h1, Nat.mod_eq_of_lt (by omega)]
  · simp only [cnt', List.getElem_set_ne hbe]
    have hne : rdxBkt shift (s_arr[i]'hi) ≠ b := hbe
    rw [ite_eq_right hne, Nat.add_zero]
    exact hinv b hb

private theorem rdx_scatter_cnt_step (shift : Nat) (s_arr : List (BitVec 64))
    {cnt : List (BitVec 64)} {n i : Nat} (hcnt : cnt.length = 256)
    (hn : n ≤ s_arr.length) (hi : i < n) (hn_bd : n < 2 ^ 30)
    (hinv : ∀ b (hb : b < 256), (cnt[b]'(by omega)).toNat =
      rdxStart (fun b => rdxSeen shift s_arr n b) b + rdxSeen shift s_arr i b) :
    let bv := rdxBkt shift (s_arr[i]'(by omega))
    let cnt' := cnt.set bv ((cnt[bv]'(by rw [hcnt]; exact rdxBkt_lt shift _)) + 1#64)
    ∀ b (hb : b < 256),
      (cnt'[b]'(by simp only [cnt', List.length_set, hcnt]; exact hb)).toNat =
        rdxStart (fun b => rdxSeen shift s_arr n b) b + rdxSeen shift s_arr (i + 1) b := by
  intro bv cnt' b hb
  have hbv : bv < 256 := rdxBkt_lt shift _
  have hcur := hinv bv hbv
  have htot := rdxStart_sum_all shift s_arr n hn
  have hseen_lt : rdxSeen shift s_arr i bv < rdxSeen shift s_arr n bv := by
    have h1 := rdxSeen_succ shift s_arr (by omega : i < s_arr.length) bv
    have h2 := rdxSeen_mono shift s_arr (by omega : i + 1 ≤ n) hn bv
    rw [ite_eq_left rfl] at h1; omega
  have hle_n : rdxStart (fun b => rdxSeen shift s_arr n b) bv + rdxSeen shift s_arr i bv < n := by
    have h1 := rdxStart_mono (fun b => rdxSeen shift s_arr n b) (by omega : bv + 1 ≤ 256)
    rw [rdxStart_succ] at h1; omega
  rw [rdxSeen_succ shift s_arr (by omega : i < s_arr.length) b]
  by_cases hbe : bv = b
  · subst hbe
    simp only [cnt', List.getElem_set_self]
    have heq : rdxBkt shift (s_arr[i]'(by omega)) = bv := rfl
    rw [ite_eq_left heq, BitVec.toNat_add, hcur]
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [h1, Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [cnt', List.getElem_set_ne hbe]
    have hne : rdxBkt shift (s_arr[i]'(by omega)) ≠ b := hbe
    rw [ite_eq_right hne, Nat.add_zero]
    exact hinv b hb

private theorem rdx_scatter_p_lt (shift : Nat) (s_arr : List (BitVec 64))
    {n i : Nat} (hn : n ≤ s_arr.length) (hi : i < n) :
    let bv := rdxBkt shift (s_arr[i]'(by omega))
    rdxStart (fun b => rdxSeen shift s_arr n b) bv + rdxSeen shift s_arr i bv < n := by
  intro bv
  have hbv : bv < 256 := rdxBkt_lt shift _
  have htot := rdxStart_sum_all shift s_arr n hn
  have hseen_lt : rdxSeen shift s_arr i bv < rdxSeen shift s_arr n bv := by
    have h1 := rdxSeen_succ shift s_arr (by omega : i < s_arr.length) bv
    have h2 := rdxSeen_mono shift s_arr (by omega : i + 1 ≤ n) hn bv
    rw [ite_eq_left rfl] at h1; omega
  have h1 := rdxStart_mono (fun b => rdxSeen shift s_arr n b) (by omega : bv + 1 ≤ 256)
  rw [rdxStart_succ] at h1; omega

private theorem rdx_flatMap_zero_count (shift : Nat) (s_arr d_arr : List (BitVec 64))
    (n : Nat) (y : BitVec 64) :
    ((List.range 256).flatMap fun b =>
      (d_arr.drop (rdxStart (fun b => rdxSeen shift s_arr n b) b)).take
        (rdxSeen shift s_arr 0 b)).count y = (s_arr.take 0).count y := by
  have hnil : ((List.range 256).flatMap fun b =>
      (d_arr.drop (rdxStart (fun b => rdxSeen shift s_arr n b) b)).take 0) = [] := by
    simp
  simpa [rdxSeen_zero] using congrArg (List.count y) hnil

/-! ### Branch 1: Insertion Sort (`n < 32`) -/

private theorem s13_sort_ana_ins_wp (Γ : Env) {c : FullCfg} {s : FullState}
    {n : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars) (hn_lt32 : n.toNat < 32)
    (hcov : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { core := { s.core with repr := repr' },
                   scratch := { s.scratch with
                     work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
      Q () m') :
    Func.wp Γ full_sort_ana_qs_m6_body (c.hdr, n, ()) m Q X := by
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwsl := hlen.scratch_ok.work_stk1_len
  have hqsl := hlen.scratch_ok.q_stamp_len
  have hreprl := hlen.core_ok.repr_len
  have hwsrt := hlen.scratch_ok.wsort_len
  have hsbufl := hlen.scratch_ok.scratch_buf_len
  have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    bv64_ofNat_toNat (by omega)
  unfold Func.wp full_sort_ana_qs_m6_body
  c0_hsteps_nogrp
  · exact hQ s.scratch.work_stk1 s.core.repr s.scratch.wsort s.scratch.scratch_buf m
      hwsl hreprl hwsrt hsbufl (List.Perm.refl _) (fun _ _ => rfl) hcov hm
  · have hn_ge2 : 2 ≤ n.toNat := by
      have h1 : ¬ n.toNat ≤ (1#64).toNat := by c0_bound
      rw [show (1#64).toNat = 1 from rfl] at h1; omega
    have hm5 := fullMem_to_sortAna5 hm
    clear hm
    let ws0 := s.scratch.work_stk1
    have hws0_len : ws0.length = 2 * c.max_vars := hwsl
    let R5 := sortAnaRestSans5 c s ⋆ R
    let rk0 := s13PackPairs64 s.core.repr
    have hrk0_len : rk0.length = c.max_vars := by
      dsimp only [rk0]; rw [s13PackPairs64_length, hreprl]; omega
    have hm_ins : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ws0 ⋆ array64 c.pRepr rk0 ⋆
        (array (t := i32) c.pWsort s.scratch.wsort ⋆
          array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ R5)) m := by
      dsimp only [ws0, rk0, R5]
      rw [s13_array_i32_eq_array64_pack c.pRepr s.core.repr (by omega)] at hm5
      exact sep_ac hm5
    let R_ins := array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ R5
    clear hm5
    refine wp_loop_inv
      (fun (i, ()) m1 => ∃ (_hi : i.toNat ≤ n.toNat), ∃ rkL : List (BitVec 64),
        ∃ (_hrk : rkL.length = c.max_vars),
        (∀ k (hk : k < i.toNat), (rkL[k]'(by omega)).setWidth 32 = ws0[k]'(by omega)) ∧
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ws0 ⋆ array64 c.pRepr rkL ⋆ R_ins) m1)
      (fun (i, ()) _ => n.toNat - i.toNat)
      (fun J1 hJ1 => by
        c0_hsteps; exact hJ1 (0#64, ()) m ⟨Nat.zero_le _, rk0, hrk0_len, fun _ h => by simp at h,
          hm_ins⟩)
      (fun J1 (i, ()) m1 ⟨hi_le, rk1, hrk1, heq1, hm1⟩ ih1 => ?_)
    rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < n.toNat := by c0_bound
      have hi_ws : i.toNat < ws0.length := by rw [hwsl]; omega
      have hi_rk : i.toNat < rk1.length := by rw [hrk1]; omega
      have hip1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
      let a := ws0[i.toNat]'hi_ws
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (q, ()) m1' => m1' = m1)
        (fun _ (q, ()) m1' hm1' => ?_) (fun Jq hJq => ?_)
      · rcases hm1'.symm with rfl; rw [Blocks.get_here]; dsimp only
        c0_hsteps
        have hm' := sep_rot4_rk hm
        refine ih1 (i + 1, ()) _ (by dsimp only; omega)
          ⟨by omega, _, by rw [List.length_set, hrk1], fun k hk => ?_, hm'⟩
        by_cases hki : k = i.toNat
        · subst hki; simp only [List.getElem_set_self]
          exact s13_pack_word_lo q (ws0[i.toNat]'hi_ws)
        · rw [List.getElem_set_ne (Ne.symm hki)]; exact heq1 k (by omega)
      · c0_hsteps
        · exact hJq _ m1 rfl
        · exact hJq _ m1 rfl
    · have hi_eq : i.toNat = n.toNat := by
        have h1 : ¬ i.toNat < n.toNat := by c0_bound
        omega
      have hpack : (rk1.take n.toNat).map (BitVec.setWidth 32) = ws0.take n.toNat :=
        s13_take_map_eq_of_eq (by omega) (by omega) (fun k hk => heq1 k (by omega))
      refine wp_loop_inv
        (fun (i, ()) m2 => 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat ∧ ∃ rkL : List (BitVec 64),
          rkL.length = c.max_vars ∧ (rkL.take n.toNat).Perm (rk1.take n.toNat) ∧
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            array (t := i32) c.pWorkStk1 ws0 ⋆ array64 c.pRepr rkL ⋆ R_ins) m2)
        (fun (i, ()) _ => n.toNat - i.toNat)
        (fun J2 hJ2 => by
          c0_hsteps; exact hJ2 (1#64, ()) m1 ⟨by decide, by
            rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega, rk1, hrk1,
            List.Perm.refl _, hm1⟩)
        (fun J2 (i, ()) m2 ⟨hi1, hi_le2, rk2, hrk2, hperm2, hm2⟩ ih2 => ?_)
      rw [Blocks.get_here]; dsimp only
      c0_hsteps_nogrp
      · have hi_lt : i.toNat < n.toNat := by c0_bound
        have hi_rk : i.toNat < rk2.length := by rw [hrk2]; omega
        have hip1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
        let x := rk2[i.toNat]'hi_rk
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (j, ()) m3 => j.toNat ≤ i.toNat ∧ ∃ rkL : List (BitVec 64),
            rkL.length = c.max_vars ∧
            ((rkL.set j.toNat x).take n.toNat).Perm (rk1.take n.toNat) ∧
            (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
              array (t := i32) c.pWorkStk1 ws0 ⋆ array64 c.pRepr rkL ⋆ R_ins) m3)
          (fun (j, ()) _ => j.toNat)
          (fun J3 hJ3 => by
            c0_hsteps
            exact hJ3 (i, ()) m2 ⟨Nat.le_refl _, rk2, hrk2, by
              rwa [List.set_getElem_self hi_rk], hm2⟩)
          (fun J3 (j, ()) m3 ⟨hj_le, rk3, hrk3, hperm3, hm3⟩ ih3 => ?_)
        rw [Blocks.get_here]; dsimp only
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun () m3' => m3' = m3)
          (fun _ () m3' hm3' => ?_) (fun Jbrk hJbrk => ?_)
        · rcases hm3'.symm with rfl; rw [Blocks.get_here]
          have hj_lt : j.toNat < rk3.length := by rw [hrk3]; omega
          c0_hsteps
          exact ih2 (i + 1, ()) _ (by dsimp only; omega)
            ⟨by omega, by omega, rk3.set j.toNat x, by rw [List.length_set, hrk3], hperm3,
              sep_rot4_rk hm⟩
        · c0_hsteps_nogrp
          · have hj_pos : 0 < j.toNat := by c0_bound
            have hjm1 : (j - 1).toNat = j.toNat - 1 := by bv_omega
            have hjm1_lt : (j - 1).toNat < rk3.length := by rw [hrk3]; omega
            have hj_lt : j.toNat < rk3.length := by rw [hrk3]; omega
            c0_hsteps
            have hshift := s13_ins_shift_perm (xs := rk3) (n := n.toNat) (j := j.toNat) (x := x)
              hj_pos (by omega) (by rw [hrk3]; omega)
            have hm' := sep_rot4_rk hm
            refine ih3 (j - 1, ()) _ (by dsimp only; omega)
              ⟨by omega, _, by rw [List.length_set, hrk3], ?_, hm'⟩
            have hval : rk3[(j - 1).toNat]'hjm1_lt = rk3[j.toNat - 1]'(by omega) := by
              congr 1
            rw [hval, hjm1]; exact hshift.trans hperm3
          · exact hJbrk () m3 rfl
          · exact hJbrk () m3 rfl
      · refine wp_loop_inv
          (fun (i, ()) m3 => ∃ (_hi : i.toNat ≤ n.toNat), ∃ wsL : List (BitVec 32),
            ∃ (_hws : wsL.length = 2 * c.max_vars),
            (∀ k (hk : k < i.toNat), wsL[k]'(by omega) = (rk2[k]'(by omega)).setWidth 32) ∧
            (∀ k, n.toNat ≤ k → wsL[k]? = ws0[k]?) ∧
            (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
              array (t := i32) c.pWorkStk1 wsL ⋆ array64 c.pRepr rk2 ⋆ R_ins) m3)
          (fun (i, ()) _ => n.toNat - i.toNat)
          (fun J4 hJ4 => by
            c0_hsteps; exact hJ4 (0#64, ()) m2 ⟨Nat.zero_le _, ws0, hwsl,
              fun _ h => by simp at h, fun _ _ => rfl, hm2⟩)
          (fun J4 (i, ()) m3 ⟨hi_le3, ws3, hws3, hcb3, hsuf3, hm3⟩ ih4 => ?_)
        rw [Blocks.get_here]; dsimp only
        c0_hsteps_nogrp
        · have hi_lt : i.toNat < n.toNat := by c0_bound
          have hip1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
          have hi_rk : i.toNat < rk2.length := by rw [hrk2]; omega
          have hi_ws : i.toNat < ws3.length := by rw [hws3]; omega
          c0_hsteps
          let ws4 := ws3.set i.toNat ((rk2[i.toNat]'hi_rk).setWidth 32)
          refine ih4 (i + 1, ()) _ (by dsimp only; omega)
            ⟨by omega, ws4, by rw [List.length_set, hws3], fun k hk => ?_, fun k hk => ?_, by
              simp only [sep_emp] at hm; exact sep_ac hm⟩
          · dsimp only [ws4]
            by_cases hki : k = i.toNat
            · subst hki; simp
            · rw [List.getElem_set_ne (Ne.symm hki)]; exact hcb3 k (by omega)
          · dsimp only [ws4]
            rw [List.getElem?_set_ne (by omega)]; exact hsuf3 k hk
        · have hi_eq : i.toNat = n.toNat := by
            have h1 : ¬ i.toNat < n.toNat := by c0_bound
            omega
          have hws_eq : ws3.take n.toNat = (rk2.take n.toNat).map (BitVec.setWidth 32) := by
            symm; exact s13_take_map_eq_of_eq (by omega) (by omega)
              (fun k hk => (hcb3 k (by omega)).symm)
          have hperm_ws : (ws3.take n.toNat).Perm (ws0.take n.toNat) := by
            rw [hws_eq, ← hpack]; exact hperm2.map (BitVec.setWidth 32)
          have hlt_ws := s13_lt_cv_of_perm (by omega) (by omega) hperm_ws hcov
          let s_out : FullState :=
            { core := { s.core with repr := s13UnpackPairs32 rk2 },
              scratch := { s.scratch with work_stk1 := ws3 } }
          have hm_out : (FullMem c s_out ⋆ R) m3 := by
            apply fullMem_of_sortAna5
            dsimp only [R_ins, R5] at hm3
            rw [s13_array64_eq_array_i32_unpack c.pRepr rk2] at hm3
            exact sep_ac hm3
          exact hQ ws3 (s13UnpackPairs32 rk2) s.scratch.wsort s.scratch.scratch_buf m3
            hws3 (by rw [s13UnpackPairs32_length, hrk2]) hwsrt hsbufl
            hperm_ws hsuf3 hlt_ws hm_out

/-! ### Branch 2: 4-Pass 8-Bit LSD Radix Sort (`n >= 32 ∧ scratch_cap >= 512`) -/

private theorem s13_sort_ana_load_sbuf {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {ws0 : List (BitVec 32)} {rk1 tmp0 cnt0 : List (BitVec 64)} {sbuf_hi : List (BitVec 32)}
    {m1 : Mem 64} (hcnt0_len : cnt0.length = 256)
    (hws0 : ws0 = s.scratch.work_stk1)
    (hm1 : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ws0 ⋆ array64 c.pRepr rk1 ⋆
      array64 c.pWsort tmp0 ⋆ array64 c.pScratchBuf cnt0 ⋆
      (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) sbuf_hi ⋆
        (sortAnaRestSans5 c s ⋆ R))) m1) :
    loadVal m1 i64 (c.hdr + 920#64) = some c.pScratchBuf := by
  have hsb_eq : array64 c.pScratchBuf cnt0 ⋆
      array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) sbuf_hi =
      array (t := i32) c.pScratchBuf (s13UnpackPairs32 cnt0 ++ sbuf_hi) := by
    rw [s13_array_i32_append c.pScratchBuf (s13UnpackPairs32 cnt0) sbuf_hi,
      s13_array64_eq_array_i32_unpack c.pScratchBuf cnt0, s13UnpackPairs32_length, hcnt0_len]
  let s1f : FullState :=
    { core := { s.core with repr := s13UnpackPairs32 rk1 }
      scratch :=
        { s.scratch with
          wsort := s13UnpackPairs32 tmp0
          scratch_buf := s13UnpackPairs32 cnt0 ++ sbuf_hi } }
  have hm1f : (FullMem c s1f ⋆ R) m1 := by
    apply fullMem_of_sortAna5
    rw [s13_array64_eq_array_i32_unpack c.pRepr rk1,
      s13_array64_eq_array_i32_unpack c.pWsort tmp0] at hm1
    have h2 : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ws0 ⋆
        array (t := i32) c.pRepr (s13UnpackPairs32 rk1) ⋆
        array (t := i32) c.pWsort (s13UnpackPairs32 tmp0) ⋆
        (array64 c.pScratchBuf cnt0 ⋆
          array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) sbuf_hi) ⋆
        (sortAnaRestSans5 c s ⋆ R)) m1 := sep_ac hm1
    rw [hsb_eq, hws0] at h2; exact sep_ac h2
  exact Full.FullArenaTactics.load_full_scratch_buf_ptr hm1f

private theorem s13_sort_ana_radix_finish {c : FullCfg} {s : FullState} {n s_ptr d_ptr : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post []} {m3 : Mem 64}
    {ws3 : List (BitVec 32)} {rk1 sL dL cntL : List (BitVec 64)}
    (hwsl : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hsbufl : s.scratch.scratch_buf.length = c.scratch_cap)
    (hcap512 : 512 ≤ c.scratch_cap) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcov : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hws3 : ws3.length = 2 * c.max_vars) (hsL : sL.length = c.max_vars)
    (hdL : dL.length = c.max_vars) (hcntL : cntL.length = 256)
    (hpack : (rk1.take n.toNat).map (BitVec.setWidth 32) = s.scratch.work_stk1.take n.toNat)
    (hpermL : (sL.take n.toNat).Perm (rk1.take n.toNat))
    (hcb3 : ∀ k (hk : k < n.toNat), ws3[k]'(by omega) = (sL[k]'(by omega)).setWidth 32)
    (hsuf3 : ∀ k, n.toNat ≤ k → ws3[k]? = s.scratch.work_stk1[k]?)
    (hptrs : (s_ptr = c.pRepr ∧ d_ptr = c.pWsort) ∨ (s_ptr = c.pWsort ∧ d_ptr = c.pRepr))
    (hm3 : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ws3 ⋆ array64 s_ptr sL ⋆
      array64 d_ptr dL ⋆ array64 c.pScratchBuf cntL ⋆
      (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) (s.scratch.scratch_buf.drop 512) ⋆
        (sortAnaRestSans5 c s ⋆ R))) m3)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { core := { s.core with repr := repr' },
                   scratch := { s.scratch with
                     work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
      Q () m') :
    Q () m3 := by
  have hws_eq : ws3.take n.toNat = (sL.take n.toNat).map (BitVec.setWidth 32) := by
    symm; exact s13_take_map_eq_of_eq (by omega) (by omega) (fun k hk => (hcb3 k hk).symm)
  have hperm_ws : (ws3.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) := by
    rw [hws_eq, ← hpack]; exact hpermL.map (BitVec.setWidth 32)
  have hlt_ws := s13_lt_cv_of_perm (by omega) (by omega) hperm_ws hcov
  let sbuf_hi := s.scratch.scratch_buf.drop 512
  let sbuf' := s13UnpackPairs32 cntL ++ sbuf_hi
  have hsbuf'_len : sbuf'.length = c.scratch_cap := by
    dsimp only [sbuf', sbuf_hi]
    rw [List.length_append, s13UnpackPairs32_length, hcntL, List.length_drop, hsbufl]; omega
  have hcnt_arr : array64 c.pScratchBuf cntL ⋆
      array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) sbuf_hi =
      array (t := i32) c.pScratchBuf sbuf' := by
    dsimp only [sbuf']
    rw [s13_array_i32_append c.pScratchBuf (s13UnpackPairs32 cntL) sbuf_hi,
      s13_array64_eq_array_i32_unpack c.pScratchBuf cntL, s13UnpackPairs32_length, hcntL]
  rcases hptrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · let s_out : FullState :=
      { core := { s.core with repr := s13UnpackPairs32 sL },
        scratch :=
          { s.scratch with
            work_stk1 := ws3, wsort := s13UnpackPairs32 dL, scratch_buf := sbuf' } }
    have hm_out : (FullMem c s_out ⋆ R) m3 := by
      apply fullMem_of_sortAna5
      rw [s13_array64_eq_array_i32_unpack c.pRepr sL,
        s13_array64_eq_array_i32_unpack c.pWsort dL] at hm3
      have hm3' : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ws3 ⋆ array (t := i32) c.pRepr (s13UnpackPairs32 sL) ⋆
          array (t := i32) c.pWsort (s13UnpackPairs32 dL) ⋆
          (array64 c.pScratchBuf cntL ⋆
            array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) sbuf_hi) ⋆
          (sortAnaRestSans5 c s ⋆ R)) m3 := sep_ac hm3
      rw [hcnt_arr] at hm3'; exact sep_ac hm3'
    exact hQ ws3 (s13UnpackPairs32 sL) (s13UnpackPairs32 dL) sbuf' m3
      hws3 (by rw [s13UnpackPairs32_length, hsL])
      (by rw [s13UnpackPairs32_length, hdL]) hsbuf'_len hperm_ws hsuf3 hlt_ws hm_out
  · let s_out : FullState :=
      { core := { s.core with repr := s13UnpackPairs32 dL },
        scratch :=
          { s.scratch with
            work_stk1 := ws3, wsort := s13UnpackPairs32 sL, scratch_buf := sbuf' } }
    have hm_out : (FullMem c s_out ⋆ R) m3 := by
      apply fullMem_of_sortAna5
      rw [s13_array64_eq_array_i32_unpack c.pWsort sL,
        s13_array64_eq_array_i32_unpack c.pRepr dL] at hm3
      have hm3' : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ws3 ⋆ array (t := i32) c.pRepr (s13UnpackPairs32 dL) ⋆
          array (t := i32) c.pWsort (s13UnpackPairs32 sL) ⋆
          (array64 c.pScratchBuf cntL ⋆
            array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) sbuf_hi) ⋆
          (sortAnaRestSans5 c s ⋆ R)) m3 := sep_ac hm3
      rw [hcnt_arr] at hm3'; exact sep_ac hm3'
    exact hQ ws3 (s13UnpackPairs32 dL) (s13UnpackPairs32 sL) sbuf' m3
      hws3 (by rw [s13UnpackPairs32_length, hdL])
      (by rw [s13UnpackPairs32_length, hsL]) hsbuf'_len hperm_ws hsuf3 hlt_ws hm_out

private def s13RadixPassesExpr {V : Ty → Type} {C : List Ty → Type}
    (n i0 ana rk tmp cnt : V i64) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64, i64, i64]]) (fun Js => .cons (fun (p : Tup V [i64, i64, i64, i64]) =>
    let s_arr := p.snd.fst; let d_arr := p.snd.snd.fst; let shift := p.snd.snd.snd.fst
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var shift, .imm 64, ())) fun p3 =>
    .jnz (.var p3.fst)
      (.group (sig := [[i64]]) (fun Js1 => .cons (fun (p4 : Tup V [i64]) =>
        .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p4.fst, .imm 256, ())) fun p5 =>
        .jnz (.var p5.fst)
          (.let_ (op64 (.mul i64) (.var p4.fst) (.imm 8)) fun m1 =>
           .let_ (op64 (.add i64) (.var cnt) (.var m1.fst)) fun m2 =>
           .store (t := i64) (.imm 0) (.var m2.fst)
             (.let_ (op64 (.add i64) (.var p4.fst) (.imm 1)) fun m3 =>
              .jump Js1.fst (.var m3.fst, ())))
          (.group (sig := [[i64, i64, i64]]) (fun Js2 => .cons (fun (p6 : Tup V [i64, i64, i64]) =>
            let i := p6.fst; let lo := p6.snd.fst; let hi := p6.snd.snd.fst
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var i, .var n, ())) fun p7 =>
            .jnz (.var p7.fst)
              (.let_ (op64 (.mul i64) (.var i) (.imm 8)) fun c1 =>
               .let_ (op64 (.add i64) (.var s_arr) (.var c1.fst)) fun c2 =>
               .load i64 (.var c2.fst) fun x =>
               .let_ (op64 (.lshr i64) (.var x) (.var shift)) fun c3 =>
               .let_ (op64 (.and i64) (.var c3.fst) (.imm 255)) fun bv =>
               .let_ (op64 (.mul i64) (.var bv.fst) (.imm 8)) fun c4 =>
               .let_ (op64 (.add i64) (.var cnt) (.var c4.fst)) fun c5 =>
               .let_ (op64 (.mul i64) (.var bv.fst) (.imm 8)) fun c6 =>
               .let_ (op64 (.add i64) (.var cnt) (.var c6.fst)) fun c7 =>
               .load i64 (.var c7.fst) fun cv0 =>
               .let_ (op64 (.add i64) (.var cv0) (.imm 1)) fun cv1 =>
               .store (.var cv1.fst) (.var c5.fst)
                 (.group (sig := [[i64]]) (fun _ => .cons (fun (lo1 : Tup V [i64]) =>
                   .group (sig := [[i64]]) (fun _ => .cons (fun (hi1 : Tup V [i64]) =>
                     .let_ (op64 (.add i64) (.var i) (.imm 1)) fun i1 =>
                     .jump Js2.fst (.var i1.fst, .var lo1.fst, .var hi1.fst, ())) .nil)
                     fun Jh =>
                       .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var bv.fst, .var hi, ()))
                         fun hcmp =>
                       .jnz (.var hcmp.fst) (.jump Jh.fst (.var bv.fst, ()))
                         (.jump Jh.fst (.var hi, ()))) .nil)
                   fun Jl =>
                     .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var bv.fst, .var lo, ())) fun lcmp =>
                     .jnz (.var lcmp.fst) (.jump Jl.fst (.var bv.fst, ()))
                       (.jump Jl.fst (.var lo, ()))))
              (.group (sig := [[i64, i64, i64, i64]]) (fun _ =>
                .cons (fun (q : Tup V [i64, i64, i64, i64]) =>
                  .let_ (op64 (.add i64) (.var shift) (.imm 8)) fun sh1 =>
                  .jump Js.fst (.var q.fst, .var q.snd.fst, .var q.snd.snd.fst, .var sh1.fst, ()))
                  .nil)
                fun Jp =>
                  .let_ (Op.mk (.cmp .ne i64 .bool rfl) (.var lo, .var hi, ())) fun neq =>
                  .jnz (.var neq.fst)
                    (.group (sig := [[i64, i64]]) (fun Jpre =>
                      .cons (fun (r : Tup V [i64, i64]) =>
                        let b := r.fst; let pos := r.snd.fst
                        .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var b, .imm 256, ())) fun bc =>
                        .jnz (.var bc.fst)
                          (.let_ (op64 (.mul i64) (.var b) (.imm 8)) fun b1 =>
                           .let_ (op64 (.add i64) (.var cnt) (.var b1.fst)) fun b2 =>
                           .load i64 (.var b2.fst) fun cb =>
                           .let_ (op64 (.mul i64) (.var b) (.imm 8)) fun b3 =>
                           .let_ (op64 (.add i64) (.var cnt) (.var b3.fst)) fun b4 =>
                           .store (.var pos) (.var b4.fst)
                             (.let_ (op64 (.add i64) (.var pos) (.var cb)) fun pos1 =>
                              .let_ (op64 (.add i64) (.var b) (.imm 1)) fun bnext =>
                              .jump Jpre.fst (.var bnext.fst, .var pos1.fst, ())))
                          (.group (sig := [[i64]]) (fun Jsc => .cons (fun (sc : Tup V [i64]) =>
                            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var sc.fst, .var n, ()))
                              fun scc =>
                            .jnz (.var scc.fst)
                              (.let_ (op64 (.mul i64) (.var sc.fst) (.imm 8)) fun s1 =>
                               .let_ (op64 (.add i64) (.var s_arr) (.var s1.fst)) fun s2 =>
                               .load i64 (.var s2.fst) fun sx =>
                               .let_ (op64 (.lshr i64) (.var sx) (.var shift)) fun s3 =>
                               .let_ (op64 (.and i64) (.var s3.fst) (.imm 255)) fun sbv =>
                               .let_ (op64 (.mul i64) (.var sbv.fst) (.imm 8)) fun s4 =>
                               .let_ (op64 (.add i64) (.var cnt) (.var s4.fst)) fun s5 =>
                               .load i64 (.var s5.fst) fun sp =>
                               .let_ (op64 (.mul i64) (.var sbv.fst) (.imm 8)) fun s6 =>
                               .let_ (op64 (.add i64) (.var cnt) (.var s6.fst)) fun s7 =>
                               .let_ (op64 (.add i64) (.var sp) (.imm 1)) fun sp1 =>
                               .store (.var sp1.fst) (.var s7.fst)
                                 (.let_ (op64 (.mul i64) (.var sp) (.imm 8)) fun s8 =>
                                  .let_ (op64 (.add i64) (.var d_arr) (.var s8.fst)) fun s9 =>
                                  .store (.var sx) (.var s9.fst)
                                    (.let_ (op64 (.add i64) (.var sc.fst) (.imm 1)) fun sc1 =>
                                     .jump Jsc.fst (.var sc1.fst, ()))))
                              (.jump Jp.fst (.var sc.fst, .var d_arr, .var s_arr, .var b, ())))
                              .nil)
                            fun Jsc => .jump Jsc.fst (.imm 0, ()))) .nil)
                      fun Jpre => .jump Jpre.fst (.imm 0, .imm 0, ()))
                    (.jump Jp.fst (.var i, .var s_arr, .var d_arr, .var p4.fst, ())))) .nil)
            fun Js2 => .jump Js2.fst (.imm 0, .imm 256, .imm 0, ()))) .nil)
        fun Js1 => .jump Js1.fst (.imm 0, ()))
      (.group (sig := [[i64]]) (fun Jcb => .cons (fun (cb : Tup V [i64]) =>
        .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var cb.fst, .var n, ())) fun cbc =>
        .jnz (.var cbc.fst)
          (.let_ (op64 (.mul i64) (.var cb.fst) (.imm 4)) fun d1 =>
           .let_ (op64 (.add i64) (.var ana) (.var d1.fst)) fun d2 =>
           .let_ (op64 (.mul i64) (.var cb.fst) (.imm 8)) fun d3 =>
           .let_ (op64 (.add i64) (.var s_arr) (.var d3.fst)) fun d4 =>
           .load i64 (.var d4.fst) fun dx =>
           .let_ (Op.mk (.trunc 64 32) (.var dx, ())) fun dx32 =>
           .store (.var dx32.fst) (.var d2.fst)
             (.let_ (op64 (.add i64) (.var cb.fst) (.imm 1)) fun cb1 =>
              .jump Jcb.fst (.var cb1.fst, ())))
          (.ret ())) .nil)
        fun Jcb => .jump Jcb.fst (.imm 0, ()))) .nil)
    fun Js => .jump Js.fst (.var i0, .var rk, .var tmp, .imm 32, ())

private theorem s13_sort_ana_radix_passes_wp (Γ : Env) {c : FullCfg} {s : FullState}
    {n i0 : BitVec 64} {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post []} {X : XPost}
    {rk1 tmp0 cnt0 : List (BitVec 64)}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hcap512 : 512 ≤ c.scratch_cap)
    (hcov : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hrk1 : rk1.length = c.max_vars) (htmp0_len : tmp0.length = c.max_vars)
    (hcnt0_len : cnt0.length = 256)
    (hpack : (rk1.take n.toNat).map (BitVec.setWidth 32) = s.scratch.work_stk1.take n.toNat)
    (hm1 : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ array64 c.pRepr rk1 ⋆
      array64 c.pWsort tmp0 ⋆ array64 c.pScratchBuf cnt0 ⋆
      (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) (s.scratch.scratch_buf.drop 512) ⋆
        (sortAnaRestSans5 c s ⋆ R))) m1)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { core := { s.core with repr := repr' },
                   scratch := { s.scratch with
                     work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
      Q () m') :
    wp Γ Q X (s13RadixPassesExpr n i0 c.pWorkStk1 c.pRepr c.pWsort c.pScratchBuf) m1 := by
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcs : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax hcs
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwsl := hlen.scratch_ok.work_stk1_len
  have hsbufl := hlen.scratch_ok.scratch_buf_len
  let ws0 := s.scratch.work_stk1
  let R_rad := array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048)
    (s.scratch.scratch_buf.drop 512) ⋆ (sortAnaRestSans5 c s ⋆ R)
  have hn_le_mv : n.toNat ≤ c.max_vars := Nat.le_trans hn_cv hcv_le
  have hn_lt30 : n.toNat < 2 ^ 30 := Nat.lt_of_le_of_lt hn_le_mv (by omega)
  have hn_lt64 : n.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hn_lt30 (by decide)
  have hn_le_2mv : n.toNat ≤ 2 * c.max_vars :=
    Nat.le_trans hn_le_mv (Nat.le_mul_of_pos_left _ (by decide))
  dsimp only [s13RadixPassesExpr]
  refine wp_loop_inv (ts := [i64, i64, i64, i64])
    (fun (_i_unused, s_ptr, d_ptr, shift, ()) m2 =>
      shift.toNat ≤ 64 ∧ shift.toNat % 8 = 0 ∧
      ((s_ptr = c.pRepr ∧ d_ptr = c.pWsort) ∨ (s_ptr = c.pWsort ∧ d_ptr = c.pRepr)) ∧
      ∃ sL dL cntL : List (BitVec 64),
        sL.length = c.max_vars ∧ dL.length = c.max_vars ∧ cntL.length = 256 ∧
        (sL.take n.toNat).Perm (rk1.take n.toNat) ∧
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ws0 ⋆ array64 s_ptr sL ⋆
          array64 d_ptr dL ⋆ array64 c.pScratchBuf cntL ⋆ R_rad) m2)
    (fun (_, _, _, shift, ()) _ => 64 - shift.toNat)
    (fun J2 hJ2 => ?_)
    (fun J2 (_i_unused, s_ptr, d_ptr, shift, ()) m2
      ⟨hsh_le, hsh_m8, hptrs, sL, dL, cntL, hsL, hdL, hcntL, hpermL, hm2⟩ ih2 => ?_)
  · c0_hsteps
    exact hJ2 (i0, c.pRepr, c.pWsort, 32#64, ()) m1
      ⟨by decide, by decide, Or.inl ⟨rfl, rfl⟩, rk1, tmp0, cnt0, hrk1, htmp0_len, hcnt0_len,
        List.Perm.refl _, hm1⟩
  rw [Blocks.get_here]; dsimp only
  c0_hsteps_nogrp
  · have hsh_lt : shift.toNat < 64 := by c0_bound
    have hsh_p8 : (shift + 8).toNat = shift.toNat + 8 := by bv_omega
    refine wp_loop_inv
      (fun (b, ()) m3 => ∃ (_hb : b.toNat ≤ 256), ∃ cntZ : List (BitVec 64),
        ∃ (_hc : cntZ.length = 256), (∀ j (hj : j < b.toNat), cntZ[j]'(by omega) = 0#64) ∧
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ws0 ⋆ array64 s_ptr sL ⋆
          array64 d_ptr dL ⋆ array64 c.pScratchBuf cntZ ⋆ R_rad) m3)
      (fun (b, ()) _ => 256 - b.toNat)
      (fun Jz hJz => by
        c0_hsteps; exact hJz (0#64, ()) m2 ⟨Nat.zero_le _, cntL, hcntL,
          fun _ h => by simp at h, hm2⟩)
      (fun Jz (b, ()) m3 ⟨hb_le, cntZ, hcntZ, hzero, hm3⟩ ihz => ?_)
    rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    · have hb_lt : b.toNat < 256 := by c0_bound
      have hbp1 : (b + 1).toNat = b.toNat + 1 := by bv_omega
      have hb_c : b.toNat < cntZ.length := by rw [hcntZ]; omega
      c0_hsteps
      let cntZ' := cntZ.set b.toNat 0#64
      refine ihz (b + 1, ()) _ (by dsimp only; omega)
        ⟨by omega, cntZ', by rw [List.length_set, hcntZ], fun j hj => ?_, by
          simp only [sep_emp] at hm; exact sep_ac hm⟩
      dsimp only [cntZ']
      by_cases hjb : j = b.toNat
      · subst hjb; simp
      · rw [List.getElem_set_ne (Ne.symm hjb)]; exact hzero j (by omega)
    · have hb_eq : b.toNat = 256 := by
        have h1 : ¬ b.toNat < 256 := by c0_bound
        omega
      refine wp_loop_inv (ts := [i64, i64, i64])
        (fun (i, lo, hi, ()) m4 => ∃ (_hi : i.toNat ≤ n.toNat), ∃ cntC : List (BitVec 64),
          ∃ (_hc : cntC.length = 256),
          (∀ j (hj : j < 256), (cntC[j]'(by omega)).toNat = rdxSeen shift.toNat sL i.toNat j) ∧
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            array (t := i32) c.pWorkStk1 ws0 ⋆ array64 s_ptr sL ⋆
            array64 d_ptr dL ⋆ array64 c.pScratchBuf cntC ⋆ R_rad) m4)
        (fun (i, _, _, ()) _ => n.toNat - i.toNat)
        (fun Jc hJc => ?_)
        (fun Jc (i, lo, hi, ()) m4 ⟨hi_le4, cntC, hcntC, hseen, hm4⟩ ihc => ?_)
      · c0_hsteps
        exact hJc (0#64, 256#64, 0#64, ()) m3 ⟨Nat.zero_le _, cntZ, hcntZ,
          fun j hj => by
            rw [show (0#64 : BitVec 64).toNat = 0 from rfl, hzero j (by omega), rdxSeen_zero]; rfl,
          hm3⟩
      rw [Blocks.get_here]; dsimp only
      c0_hsteps_nogrp
      · have hi_lt : i.toNat < n.toNat := by c0_bound
        have hip1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
        have hip1' : (i + 1#64).toNat = i.toNat + 1 := hip1
        have hi_s : i.toNat < sL.length := by rw [hsL]; omega
        have hbv_eq : ((sL[i.toNat]'hi_s >>> (shift.toNat % 64)) &&& (255 : BitVec 64)).toNat =
            rdxBkt shift.toNat (sL[i.toNat]'hi_s) := by
          rw [Nat.mod_eq_of_lt hsh_lt, show (255 : BitVec 64) = 255#64 from rfl, rdxBkt_eq]
        have hbv_lt : ((sL[i.toNat]'hi_s >>> (shift.toNat % 64)) &&& (255 : BitVec 64)).toNat <
            cntC.length := by rw [hcntC, hbv_eq]; exact rdxBkt_lt _ _
        have hstep := rdx_count_step_all shift.toNat sL hcntC hi_s (by omega) hseen
        c0_hsteps
        all_goals
          have hm' := sep_rot6_cnt hm
          refine ihc (i + 1, _, _, ()) m (by dsimp only; omega)
            ⟨by omega, _, by rw [List.length_set, hcntC], ?_, hm'⟩
          intro j hj
          simpa only [hbv_eq, hip1', show (1 : BitVec 64) = 1#64 from rfl] using hstep j hj
      · have hi_eq4 : i.toNat = n.toNat := by
          have h1 : ¬ i.toNat < n.toNat := by c0_bound
          omega
        have hseenN : ∀ j (hj : j < 256),
            (cntC[j]'(by omega)).toNat = rdxSeen shift.toNat sL n.toNat j := by
          intro j hj; simpa [hi_eq4] using hseen j hj
        let tot := fun j => rdxSeen shift.toNat sL n.toNat j
        have htot_sum : rdxStart tot 256 = n.toNat :=
          rdxStart_sum_all shift.toNat sL n.toNat (by rw [hsL]; exact hn_le_mv)
        refine wp_join_group (ts := [i64, i64, i64, i64])
          (fun (_ii, sp', dp', _bb, ()) m5 =>
            ((sp' = c.pRepr ∧ dp' = c.pWsort) ∨ (sp' = c.pWsort ∧ dp' = c.pRepr)) ∧
            ∃ sL' dL' cnt' : List (BitVec 64),
              sL'.length = c.max_vars ∧ dL'.length = c.max_vars ∧ cnt'.length = 256 ∧
              (sL'.take n.toNat).Perm (rk1.take n.toNat) ∧
              (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                array (t := i32) c.pWorkStk1 ws0 ⋆ array64 sp' sL' ⋆
                array64 dp' dL' ⋆ array64 c.pScratchBuf cnt' ⋆ R_rad) m5)
          (fun _ (_ii, sp', dp', _bb, ()) m5
              ⟨hptrs', sL', dL', cnt', hs', hd', hc', hp', hm5⟩ => ?_)
          (fun Jp hJp => ?_)
        · rw [Blocks.get_here]; dsimp only
          c0_hsteps
          exact ih2 (_ii, sp', dp', shift + 8, ()) m5 (by dsimp only; omega)
            ⟨by omega, by omega, hptrs', sL', dL', cnt', hs', hd', hc', hp', hm5⟩
        c0_hsteps_nogrp
        · refine wp_loop_inv (ts := [i64, i64])
            (fun (b, pos, ()) m5 => ∃ (_hb : b.toNat ≤ 256), pos.toNat = rdxStart tot b.toNat ∧
              ∃ cntP : List (BitVec 64), ∃ (_hc : cntP.length = 256),
                (∀ j (hj : j < b.toNat), (cntP[j]'(by omega)).toNat = rdxStart tot j) ∧
                (∀ j, b.toNat ≤ j → ∀ (hj : j < 256), (cntP[j]'(by omega)).toNat = tot j) ∧
                (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                  array (t := i32) c.pWorkStk1 ws0 ⋆ array64 s_ptr sL ⋆
                  array64 d_ptr dL ⋆ array64 c.pScratchBuf cntP ⋆ R_rad) m5)
            (fun (b, _, ()) _ => 256 - b.toNat)
            (fun Jpre hJpre => ?_)
            (fun Jpre (b, pos, ()) m5 ⟨hb_le5, hpos5, cntP, hcntP, hlo5, hhi5, hm5⟩ ihp => ?_)
          · c0_hsteps
            exact hJpre (0#64, 0#64, ()) m4 ⟨Nat.zero_le _,
              by change 0 = rdxStart tot 0; rw [rdxStart_zero],
              cntC, hcntC, fun _ h => by simp at h, fun j _ hj => hseenN j hj, hm4⟩
          rw [Blocks.get_here]; dsimp only
          c0_hsteps_nogrp
          · have hb_lt : b.toNat < 256 := by c0_bound
            have hbp1 : (b + 1).toNat = b.toNat + 1 := by bv_omega
            have hb_c : b.toNat < cntP.length := by rw [hcntP]; omega
            have hcb : (cntP[b.toNat]'hb_c).toNat = tot b.toNat :=
              hhi5 b.toNat (Nat.le_refl _) hb_lt
            have hsum_le : rdxStart tot (b.toNat + 1) ≤ n.toNat := by
              rw [← htot_sum]; exact rdxStart_mono tot (by omega)
            have hpos_add : (pos + cntP[b.toNat]'hb_c).toNat =
                rdxStart tot (b.toNat + 1) := by
              rw [BitVec.toNat_add, hpos5, hcb, ← rdxStart_succ,
                Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hsum_le hn_lt64)]
            c0_hsteps
            let cntP' := cntP.set b.toNat pos
            refine ihp (b + 1, pos + cntP[b.toNat]'hb_c, ()) _ (by dsimp only; omega)
              ⟨by omega, by rw [hbp1]; exact hpos_add, cntP', by rw [List.length_set, hcntP],
                fun j hj => ?_, fun j hj1 hj2 => ?_, by
                  simp only [sep_emp] at hm; exact sep_ac hm⟩
            · dsimp only [cntP']
              by_cases hjb : j = b.toNat
              · subst hjb; simp [hpos5]
              · rw [List.getElem_set_ne (Ne.symm hjb)]; exact hlo5 j (by omega)
            · dsimp only [cntP']
              rw [List.getElem_set_ne (by omega)]; exact hhi5 j (by omega) hj2
          · have hb_eq5 : b.toNat = 256 := by
              have h1 : ¬ b.toNat < 256 := by c0_bound
              omega
            refine wp_loop_inv
              (fun (i, ()) m6 => ∃ (_hi : i.toNat ≤ n.toNat),
                ∃ cntS dS : List (BitVec 64),
                  ∃ (_hc : cntS.length = 256), ∃ (_hd : dS.length = c.max_vars),
                  (∀ j (hj : j < 256), (cntS[j]'(by omega)).toNat =
                    rdxStart tot j + rdxSeen shift.toNat sL i.toNat j) ∧
                  (∀ y, ((List.range 256).flatMap fun j =>
                      (dS.drop (rdxStart tot j)).take
                        (rdxSeen shift.toNat sL i.toNat j)).count y =
                    (sL.take i.toNat).count y) ∧
                  (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                    array (t := i32) c.pWorkStk1 ws0 ⋆ array64 s_ptr sL ⋆
                    array64 d_ptr dS ⋆ array64 c.pScratchBuf cntS ⋆ R_rad) m6)
              (fun (i, ()) _ => n.toNat - i.toNat)
              (fun Js hJs => by
                c0_hsteps
                exact hJs (0#64, ()) m5 ⟨Nat.zero_le _, cntP, dL, hcntP, hdL,
                  fun j hj => by simpa [rdxSeen_zero] using hlo5 j (by omega),
                  fun y => rdx_flatMap_zero_count shift.toNat sL dL n.toNat y, hm5⟩)
              (fun Js (i, ()) m6 ⟨hi_le6, cntS, dS, hcntS, hdS, hcntInv, hfmInv, hm6⟩ ihs => ?_)
            rw [Blocks.get_here]; dsimp only
            c0_hsteps_nogrp
            · have hi_lt : i.toNat < n.toNat := by c0_bound
              have hip1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
              have hip1' : (i + 1#64).toNat = i.toNat + 1 := hip1
              have hi_s : i.toNat < sL.length := by rw [hsL]; omega
              have hbv_eq :
                  ((sL[i.toNat]'hi_s >>> (shift.toNat % 64)) &&& (255 : BitVec 64)).toNat =
                  rdxBkt shift.toNat (sL[i.toNat]'hi_s) := by
                rw [Nat.mod_eq_of_lt hsh_lt, show (255 : BitVec 64) = 255#64 from rfl, rdxBkt_eq]
              have hbv_lt :
                  ((sL[i.toNat]'hi_s >>> (shift.toNat % 64)) &&& (255 : BitVec 64)).toNat <
                  cntS.length := by rw [hcntS, hbv_eq]; exact rdxBkt_lt _ _
              have hp_eq : (cntS[((sL[i.toNat]'hi_s >>> (shift.toNat % 64)) &&&
                    (255 : BitVec 64)).toNat]'hbv_lt).toNat =
                  rdxStart tot (rdxBkt shift.toNat (sL[i.toNat]'hi_s)) +
                    rdxSeen shift.toNat sL i.toNat (rdxBkt shift.toNat (sL[i.toNat]'hi_s)) := by
                have h1 := hcntInv (rdxBkt shift.toNat (sL[i.toNat]'hi_s)) (rdxBkt_lt _ _)
                simpa only [hbv_eq] using h1
              have hn_sL : n.toNat ≤ sL.length := hsL.symm ▸ hn_le_mv
              have hp_lt_n : (cntS[((sL[i.toNat]'hi_s >>> (shift.toNat % 64)) &&&
                    (255 : BitVec 64)).toNat]'hbv_lt).toNat <
                  n.toNat := by rw [hp_eq]; exact rdx_scatter_p_lt shift.toNat sL hn_sL hi_lt
              have hp_lt_d : (cntS[((sL[i.toNat]'hi_s >>> (shift.toNat % 64)) &&&
                    (255 : BitVec 64)).toNat]'hbv_lt).toNat <
                  dS.length := hdS.symm ▸ Nat.lt_of_lt_of_le hp_lt_n hn_le_mv
              have hstepC := rdx_scatter_cnt_step shift.toNat sL hcntS hn_sL hi_lt hn_lt30 hcntInv
              c0_hsteps
              have hm' := sep_rot6_ds hm
              refine ihs (i + 1, ()) m (by dsimp only; omega)
                ⟨by omega, _, _, by rw [List.length_set, hcntS], by rw [List.length_set, hdS],
                  fun j hj => by
                    simpa only [hbv_eq, hip1', show (1 : BitVec 64) = 1#64 from rfl] using
                      hstepC j hj,
                  fun y => ?_, hm'⟩
              have hfm :=
                rdx_flatMap_count_step shift.toNat sL dS hn_sL (hdS.symm ▸ hn_le_mv) hi_lt y
              rw [hip1, hp_eq, hfm, hfmInv y, List.take_succ_eq_append_getElem hi_s,
                List.count_append, List.count_singleton]
            · have hi_eq6 : i.toNat = n.toNat := by
                have h1 : ¬ i.toNat < n.toNat := by c0_bound
                omega
              have hperm_d : (dS.take n.toNat).Perm (sL.take n.toNat) :=
                s13_radix_pass_perm shift.toNat sL dS (hsL.symm ▸ hn_le_mv) (hdS.symm ▸ hn_le_mv)
                  (fun y => by simpa [hi_eq6] using hfmInv y)
              c0_hsteps
              refine hJp (i, d_ptr, s_ptr, b, ()) m6
                ⟨by rcases hptrs with ⟨h1, h2⟩ | ⟨h1, h2⟩
                    · exact Or.inr ⟨h2, h1⟩
                    · exact Or.inl ⟨h2, h1⟩,
                  dS, sL, cntS, hdS, hsL, hcntS, hperm_d.trans hpermL, sep_ac hm6⟩
        · c0_hsteps
          exact hJp (i, s_ptr, d_ptr, b, ()) m4
            ⟨hptrs, sL, dL, cntC, hsL, hdL, hcntC, hpermL, hm4⟩
  · -- Copy-back loop
    refine wp_loop_inv
      (fun (i, ()) m3 => ∃ (hi : i.toNat ≤ n.toNat), ∃ wsL : List (BitVec 32),
        ∃ (hws : wsL.length = 2 * c.max_vars),
        (∀ k (hk : k < i.toNat),
          wsL[k]'(hws.symm ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hk hi) hn_le_2mv) =
            (sL[k]'(hsL.symm ▸
              Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hk hi) hn_le_mv)).setWidth 32) ∧
        (∀ k, n.toNat ≤ k → wsL[k]? = ws0[k]?) ∧
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 wsL ⋆ array64 s_ptr sL ⋆
          array64 d_ptr dL ⋆ array64 c.pScratchBuf cntL ⋆ R_rad) m3)
      (fun (i, ()) _ => n.toNat - i.toNat)
      (fun J3 hJ3 => by
        c0_hsteps; exact hJ3 (0#64, ()) m2 ⟨Nat.zero_le _, ws0, hwsl,
          fun _ h => by simp at h, fun _ _ => rfl, hm2⟩)
      (fun J3 (i, ()) m3 ⟨hi_le3, ws3, hws3, hcb3, hsuf3, hm3⟩ ih3 => ?_)
    rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < n.toNat := by c0_bound
      have hip1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
      have hi_s : i.toNat < sL.length := hsL.symm ▸ Nat.lt_of_lt_of_le hi_lt hn_le_mv
      have hi_ws : i.toNat < ws3.length := hws3.symm ▸ Nat.lt_of_lt_of_le hi_lt hn_le_2mv
      c0_hsteps
      let ws4 := ws3.set i.toNat ((sL[i.toNat]'hi_s).setWidth 32)
      refine ih3 (i + 1, ()) _ (by dsimp only; omega)
        ⟨by omega, ws4, by rw [List.length_set, hws3], fun k hk => ?_, fun k hk => ?_, by
          simp only [sep_emp] at hm; exact sep_ac hm⟩
      · dsimp only [ws4]
        by_cases hki : k = i.toNat
        · subst hki; simp
        · rw [List.getElem_set_ne (Ne.symm hki)]; exact hcb3 k (by omega)
      · dsimp only [ws4]
        rw [List.getElem?_set_ne (by omega)]; exact hsuf3 k hk
    · have hi_eq : i.toNat = n.toNat := by
        have h1 : ¬ i.toNat < n.toNat := by c0_bound
        omega
      exact s13_sort_ana_radix_finish hwsl hsbufl hcap512 hn_cv hcv_le hcov hws3 hsL hdL hcntL
        hpack hpermL (fun k hk => hcb3 k (hi_eq.symm ▸ hk)) hsuf3 hptrs hm3 hQ

private theorem s13_sort_ana_radix_wp (Γ : Env) {c : FullCfg} {s : FullState}
    {n : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hn_ge32 : 32 ≤ n.toNat) (hcap512 : 512 ≤ c.scratch_cap)
    (hcov : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { core := { s.core with repr := repr' },
                   scratch := { s.scratch with
                     work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
      Q () m') :
    Func.wp Γ full_sort_ana_qs_m6_body (c.hdr, n, ()) m Q X := by
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcs : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax hcs
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwsl := hlen.scratch_ok.work_stk1_len
  have hqsl := hlen.scratch_ok.q_stamp_len
  have hreprl := hlen.core_ok.repr_len
  have hwsrt := hlen.scratch_ok.wsort_len
  have hsbufl := hlen.scratch_ok.scratch_buf_len
  have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    bv64_ofNat_toNat (by omega)
  unfold Func.wp full_sort_ana_qs_m6_body
  c0_hsteps_nogrp
  have hm5 := fullMem_to_sortAna5 hm
  clear hm
  let ws0 := s.scratch.work_stk1
  have hws0_len : ws0.length = 2 * c.max_vars := hwsl
  let R5 := sortAnaRestSans5 c s ⋆ R
  let rk0 := s13PackPairs64 s.core.repr
  let tmp0 := s13PackPairs64 s.scratch.wsort
  let sbuf_lo := s.scratch.scratch_buf.take 512
  let sbuf_hi := s.scratch.scratch_buf.drop 512
  let cnt0 := s13PackPairs64 sbuf_lo
  have hrk0_len : rk0.length = c.max_vars := by
    dsimp only [rk0]; rw [s13PackPairs64_length, hreprl]; omega
  have htmp0_len : tmp0.length = c.max_vars := by
    dsimp only [tmp0]; rw [s13PackPairs64_length, hwsrt]; omega
  have hsblo_len : sbuf_lo.length = 512 := by simp [sbuf_lo, hsbufl]; omega
  have hcnt0_len : cnt0.length = 256 := by
    dsimp only [cnt0]; rw [s13PackPairs64_length, hsblo_len]
  have hm_rad : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ws0 ⋆ array64 c.pRepr rk0 ⋆
      array64 c.pWsort tmp0 ⋆ array64 c.pScratchBuf cnt0 ⋆
      (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) sbuf_hi ⋆ R5)) m := by
    have hsb_split : s.scratch.scratch_buf = sbuf_lo ++ sbuf_hi := (List.take_append_drop ..).symm
    dsimp only [ws0, rk0, tmp0, cnt0, R5]
    rw [hsb_split, s13_array_i32_append c.pScratchBuf sbuf_lo sbuf_hi, hsblo_len,
      s13_array_i32_eq_array64_pack c.pScratchBuf sbuf_lo (by rw [hsblo_len]),
      s13_array_i32_eq_array64_pack c.pRepr s.core.repr (by omega),
      s13_array_i32_eq_array64_pack c.pWsort s.scratch.wsort (by omega)] at hm5
    exact sep_ac hm5
  let R_rad := array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 2048) sbuf_hi ⋆ R5
  clear hm5
  -- Pack loop
  refine wp_loop_inv
    (fun (i, ()) m1 => ∃ (_hi : i.toNat ≤ n.toNat), ∃ rkL : List (BitVec 64),
      ∃ (_hrk : rkL.length = c.max_vars),
      (∀ k (hk : k < i.toNat), (rkL[k]'(by omega)).setWidth 32 = ws0[k]'(by omega)) ∧
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ws0 ⋆ array64 c.pRepr rkL ⋆
        array64 c.pWsort tmp0 ⋆ array64 c.pScratchBuf cnt0 ⋆ R_rad) m1)
    (fun (i, ()) _ => n.toNat - i.toNat)
    (fun J1 hJ1 => by
      c0_hsteps; exact hJ1 (0#64, ()) m ⟨Nat.zero_le _, rk0, hrk0_len, fun _ h => by simp at h,
        hm_rad⟩)
    (fun J1 (i, ()) m1 ⟨hi_le, rk1, hrk1, heq1, hm1⟩ ih1 => ?_)
  rw [Blocks.get_here]; dsimp only
  c0_hsteps_nogrp
  · have hi_lt : i.toNat < n.toNat := by c0_bound
    have hi_ws : i.toNat < ws0.length := by rw [hwsl]; omega
    have hi_rk : i.toNat < rk1.length := by rw [hrk1]; omega
    have hip1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
    let a := ws0[i.toNat]'hi_ws
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i32]) (fun (q, ()) m1' => m1' = m1)
      (fun _ (q, ()) m1' hm1' => ?_) (fun Jq hJq => ?_)
    · rcases hm1'.symm with rfl; rw [Blocks.get_here]; dsimp only
      c0_hsteps
      have hm' := sep_rot6_rk hm
      refine ih1 (i + 1, ()) _ (by dsimp only; omega)
        ⟨by omega, _, by rw [List.length_set, hrk1], fun k hk => ?_, hm'⟩
      by_cases hki : k = i.toNat
      · subst hki; simp only [List.getElem_set_self]
        exact s13_pack_word_lo q (ws0[i.toNat]'hi_ws)
      · rw [List.getElem_set_ne (Ne.symm hki)]; exact heq1 k (by omega)
    · c0_hsteps
      · exact hJq _ m1 rfl
      · exact hJq _ m1 rfl
  · have hi_eq : i.toNat = n.toNat := by
      have h1 : ¬ i.toNat < n.toNat := by c0_bound
      omega
    have hpack : (rk1.take n.toNat).map (BitVec.setWidth 32) = ws0.take n.toNat :=
      s13_take_map_eq_of_eq (by omega) (by omega) (fun k hk => heq1 k (by omega))
    have hld_sb : loadVal m1 i64 (c.hdr + 920#64) = some c.pScratchBuf :=
      s13_sort_ana_load_sbuf hcnt0_len rfl hm1
    refine wp_load_of hld_sb ?_
    exact s13_sort_ana_radix_passes_wp Γ hlen hn_cv hcap512 hcov hrk1 htmp0_len hcnt0_len hpack
      hm1 hQ

/-! ### Branch 3: Heapsort Fallback (`n >= 32 ∧ scratch_cap < 512`) -/

private theorem s13_sort_ana_heap_wp (Γ : Env)
    (hSift : ∀ args m Q X, s13AnaSiftSpec args m Q X →
      Γ "full_ana_sift_m6" [i64, i64, i64, i64, i64] [] args m Q X)
    {c : FullCfg} {s : FullState} {n : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hn_ge32 : 32 ≤ n.toNat) (hcap_lt : c.scratch_cap < 512)
    (hcov : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { core := { s.core with repr := repr' },
                   scratch := { s.scratch with
                     work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
      Q () m') :
    Func.wp Γ full_sort_ana_qs_m6_body (c.hdr, n, ()) m Q X := by
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcs : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax hcs
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwsl := hlen.scratch_ok.work_stk1_len
  have hqsl := hlen.scratch_ok.q_stamp_len
  have hreprl := hlen.core_ok.repr_len
  have hwsrt := hlen.scratch_ok.wsort_len
  have hsbufl := hlen.scratch_ok.scratch_buf_len
  have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    bv64_ofNat_toNat (by omega)
  unfold Func.wp full_sort_ana_qs_m6_body
  c0_hsteps_nogrp
  have hm5 := fullMem_to_sortAna5 hm
  clear hm
  let ws0 := s.scratch.work_stk1
  let R5 := sortAnaRestSans5 c s ⋆ R
  let R_hp := array (t := i32) c.pRepr s.core.repr ⋆
    array (t := i32) c.pWsort s.scratch.wsort ⋆
    array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ R5
  have hm_hp : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ws0 ⋆ R_hp) m := by
    dsimp only [R_hp, R5, ws0]; exact sep_ac hm5
  clear hm5
  let LoopInv : List (BitVec 32) → Prop := fun wsL =>
    wsL.length = 2 * c.max_vars ∧ (wsL.take n.toNat).Perm (ws0.take n.toNat) ∧
    (∀ k, n.toNat ≤ k → wsL[k]? = ws0[k]?) ∧
    (∀ k < n.toNat, (wsL[k]?.getD 0#32).toNat < s.core.cur_vars)
  refine wp_loop_inv
    (fun (start, ()) m1 => start.toNat ≤ n.toNat / 2 ∧ ∃ wsL,
      LoopInv wsL ∧ (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 wsL ⋆ R_hp) m1)
    (fun (start, ()) _ => start.toNat)
    (fun J1 hJ1 => by
      c0_hsteps
      exact hJ1 (n >>> (1 : Nat), ()) m ⟨by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
        exact Nat.le_refl _, ws0, ⟨hwsl, List.Perm.refl _, fun _ _ => rfl, hcov⟩, hm_hp⟩)
    (fun J1 (start, ()) m1 ⟨hst_le, ws1, hli1, hm1⟩ ih1 => ?_)
  rw [Blocks.get_here]; dsimp only
  c0_hsteps_nogrp
  · have hst_pos : 0 < start.toNat := by c0_bound
    have hst_m1 : (start - 1).toNat = start.toNat - 1 := by bv_omega
    c0_call hSift
    refine s13AnaSiftSpec_of
      (by rw [hqsl, hcv64]; exact hcv_le)
      (by rw [hst_m1]; omega) (by rw [hli1.1]; omega) (by omega)
      (by rw [hcv64]; exact hli1.2.2.2) hm1 ?_
    intro ws2 m2 hl2 hp2 hsuf2 hcov2 hm2
    rw [hcv64] at hcov2
    exact ih1 (start - 1, ()) m2 (by dsimp only; omega)
      ⟨by rw [hst_m1]; omega, ws2,
        ⟨by rw [hl2, hli1.1], hp2.trans hli1.2.1,
          fun k hk => (hsuf2 k hk).trans (hli1.2.2.1 k hk), hcov2⟩, hm2⟩
  · have hnm1 : (n - 1#64).toNat = n.toNat - 1 := by bv_omega
    refine wp_loop_inv
      (fun (endb, ()) m2 => endb.toNat < n.toNat ∧ ∃ wsL,
        LoopInv wsL ∧ (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 wsL ⋆ R_hp) m2)
      (fun (endb, ()) _ => endb.toNat)
      (fun J2 hJ2 => by c0_hsteps; exact hJ2 (n - 1#64, ()) m1 ⟨by rw [hnm1]; omega,
        ws1, hli1, hm1⟩)
      (fun J2 (endb, ()) m2 ⟨hend_lt, ws2, hli2, hm2⟩ ih2 => ?_)
    rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    · have hend_pos : 0 < endb.toNat := by c0_bound
      have h0_lt : 0 < ws2.length := by rw [hli2.1]; omega
      have he_lt : endb.toNat < ws2.length := by rw [hli2.1]; omega
      have hend_m1 : (endb - 1).toNat = endb.toNat - 1 := by bv_omega
      let ws3 := (ws2.set 0 (ws2[endb.toNat]'he_lt)).set endb.toNat (ws2[0]'h0_lt)
      obtain ⟨hsl3, hsp3, hso3⟩ := s13_swap_take_perm (xs := ws2)
        (by omega : 0 < n.toNat) hend_lt (by rw [hli2.1]; omega)
      have hcov3 := s13_lt_cv_of_perm (by rw [hsl3, hli2.1]; omega)
        (by rw [hli2.1]; omega) hsp3 hli2.2.2.2
      c0_hsteps_nogrp
      c0_call hSift
      refine s13AnaSiftSpec_of (R := R_hp)
        (by rw [hqsl, hcv64]; exact hcv_le)
        (Nat.zero_le _) (by rw [hsl3, hli2.1]; omega) (by omega)
        (by rw [hcv64]; exact fun k hk => hcov3 k (by omega))
        (by
          have h0bv : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 := rfl
          simp only [h0bv, sep_emp] at hm
          exact sep_ac hm) ?_
      intro ws4 m4 hl4 hp4 hsuf4 hcov4 hm4
      rw [hcv64] at hcov4
      have hp4_n := s13_perm_take_lift (by omega : endb.toNat ≤ n.toNat)
        (by rw [hsl3, hli2.1]; omega) hl4 hp4 hsuf4
      have hcov4_n := s13_lt_cv_of_perm (by rw [hl4, hsl3, hli2.1]; omega)
        (by rw [hsl3, hli2.1]; omega) hp4_n hcov3
      c0_hsteps
      exact ih2 (endb - 1, ()) m4 (by dsimp only; omega)
        ⟨by rw [hend_m1]; omega, ws4,
          ⟨by rw [hl4, hsl3, hli2.1], hp4_n.trans (hsp3.trans hli2.2.1),
            fun k hk => (hsuf4 k (by omega)).trans ((hso3 k hk).trans (hli2.2.2.1 k hk)),
            hcov4_n⟩, hm4⟩
    · let s_out : FullState :=
        { core := { s.core with repr := s.core.repr },
          scratch :=
            { s.scratch with
              work_stk1 := ws2, wsort := s.scratch.wsort,
              scratch_buf := s.scratch.scratch_buf } }
      have hm_out : (FullMem c s_out ⋆ R) m2 := by
        apply fullMem_of_sortAna5
        dsimp only [R_hp, R5] at hm2
        exact sep_ac hm2
      exact hQ ws2 s.core.repr s.scratch.wsort s.scratch.scratch_buf m2
        hli2.1 hreprl hwsrt hsbufl hli2.2.1 hli2.2.2.1 hli2.2.2.2 hm_out

/-- Step-13 `full_sort_ana_qs_m6` (`PERF-R3` insertion + LSD radix + heapsort fallback) satisfies
`s13SortAnaQsSpec`. -/
theorem full_sort_ana_qs_m6_step13_wp (Γ : Env)
    (hSift : ∀ args m Q X, s13AnaSiftSpec args m Q X →
      Γ "full_ana_sift_m6" [i64, i64, i64, i64, i64] [] args m Q X) :
    ∀ args m Q X, s13SortAnaQsSpec args m Q X →
      Func.wp Γ full_sort_ana_qs_m6_body args m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, R, rfl, hlen, hn_cv, hcov, hm, hQ⟩ := s13SortAnaQsSpec_elim hs
  by_cases hn32 : n.toNat < 32
  · exact s13_sort_ana_ins_wp Γ hlen hn_cv hn32 hcov hm hQ
  · by_cases hcap : 512 ≤ c.scratch_cap
    · exact s13_sort_ana_radix_wp Γ hlen hn_cv (by omega) hcap hcov hm hQ
    · exact s13_sort_ana_heap_wp Γ hSift hlen hn_cv (by omega) (by omega) hcov hm hQ

/-- Transparent Step-13 `Func.wp` lift for unchanged `full_ana_sift_m6` against `s13AnaSiftSpec`. -/
theorem full_ana_sift_m6_step13_wp (Γ : Env) :
    ∀ args m Q X, s13AnaSiftSpec args m Q X →
      Func.wp Γ full_ana_sift_m6_body args m Q X := by
  rintro ⟨qs_ptr, ana_ptr, cv, start, n, ⟨⟩⟩ m Q X hs
  obtain ⟨qs, ana, R, hcv_qs, hst_n, hn_ana, hn62, hcov, hm, hQ⟩ := s13AnaSiftSpec_elim hs
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m1 => Q () m1)
    (fun _ _ _ hq => by c0_hsteps; exact hq) ?_
  intro Jbrk hBrk
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (root, ()) mL =>
      root.toNat ≤ n.toNat ∧ ∃ anaL : List (BitVec 32),
        anaL.length = ana.length ∧ (anaL.take n.toNat).Perm (ana.take n.toNat) ∧
        (∀ k, n.toNat ≤ k → anaL[k]? = ana[k]?) ∧
        (∀ k < n.toNat, (anaL[k]?.getD 0#32).toNat < cv.toNat) ∧
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr anaL ⋆ R) mL)
    (fun (root, ()) _ => n.toNat - root.toNat) (fun J hLoop => ?_)
    (fun J (root, ()) mL ⟨hrt_le, anaL, hlenL, hpermL, houtL, hcovL, hmL⟩ hLoop => ?_)
  · c0_hsteps
    exact hLoop (start, ()) m ⟨hst_n, ana, rfl, List.Perm.refl _, fun _ _ => rfl, hcov, hm⟩
  · have hch_eq : ((root <<< (1 : Nat)) + 1#64).toNat = 2 * root.toNat + 1 := by
      have hsh : (root <<< (1 : Nat)).toNat = 2 * root.toNat := by c0_bound
      rw [BitVec.toNat_add, hsh]; simp; omega
    c0_hsteps_nogrp
    · exact hBrk _ mL (hQ anaL mL hlenL hpermL houtL hcovL hmL)
    · have hch_lt : 2 * root.toNat + 1 < n.toNat := by
        have : ((root <<< (1 : Nat)) + 1#64).toNat < n.toNat := by c0_bound
        omega
      have hrt_lt : root.toNat < n.toNat := by omega
      have hch_ana : ((root <<< (1 : Nat)) + 1#64).toNat < anaL.length := by omega
      let ac := anaL[((root <<< (1 : Nat)) + 1#64).toNat]'hch_ana
      have hac_lt : (ac.setWidth 64).toNat < qs.length := by
        have hg := hcovL (2 * root.toNat + 1) hch_lt
        rw [List.getElem?_eq_getElem (by omega : 2 * root.toNat + 1 < anaL.length),
          Option.getD_some] at hg
        rw [zext_toNat _ (by decide)]
        have hac_eq : ac.toNat = (anaL[2 * root.toNat + 1]'(by omega)).toNat := by
          dsimp only [ac]; congr 2
        omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (qc, ()) m1 => mL = m1)
        (fun Jqc (qc, ()) m1 hm1 => ?_) (fun Jqc hJqc => ?_)
      · rcases hm1 with rfl; rw [Blocks.get_here]; dsimp only
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i32])
          (fun (ch, qc', ()) m2 =>
            mL = m2 ∧ ch.toNat < n.toNat ∧ root.toNat < ch.toNat)
          (fun Jch (ch, qc', ()) m2 ⟨hm2, hch_n, hrt_ch⟩ => ?_) (fun Jch hJch => ?_)
        · rcases hm2 with rfl; rw [Blocks.get_here]; dsimp only
          have hrt_ana : root.toNat < anaL.length := by omega
          let ar := anaL[root.toNat]'hrt_ana
          have har_lt : (ar.setWidth 64).toNat < qs.length := by
            have hg := hcovL root.toNat hrt_lt
            rw [List.getElem?_eq_getElem hrt_ana, Option.getD_some] at hg
            rw [zext_toNat _ (by decide)]
            dsimp only [ar]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32]) (fun (qr, ()) m3 => mL = m3)
            (fun Jqr (qr, ()) m3 hm3 => ?_) (fun Jqr hJqr => ?_)
          · rcases hm3 with rfl; rw [Blocks.get_here]; dsimp only
            c0_hsteps_nogrp
            · exact hBrk _ mL (hQ anaL mL hlenL hpermL houtL hcovL hmL)
            · have hch_ana' : ch.toNat < anaL.length := by omega
              have hrt_ana' :
                  root.toNat < (anaL.set ch.toNat (anaL[ch.toNat]'hch_ana')).length :=
                by simp [hrt_ana]
              c0_hsteps
              obtain ⟨hsl, hsp, hso⟩ :=
                s13_swap_take_perm (xs := anaL) hrt_lt hch_n (by omega)
              have hcov' := s13_lt_cv_of_perm (by omega) (by omega) hsp hcovL
              refine hLoop (ch, ()) m (by dsimp only; omega) ⟨by omega, _,
                by simpa only [hlenL] using hsl, hsp.trans hpermL,
                fun k hk => (hso k hk).trans (houtL k hk), hcov', ?_⟩
              simp only [sep_emp] at hm
              simpa only [hrt_ana, hch_ana'] using sep_ac hm
          · c0_hsteps
            · exact hJqr _ mL rfl
            · exact hJqr _ mL rfl
        · c0_hsteps_nogrp
          · have hch1_eq : (((root <<< (1 : Nat)) + 1#64) + 1#64).toNat =
                2 * root.toNat + 2 := by
              rw [BitVec.toNat_add, hch_eq]; simp; omega
            have hch1_lt : 2 * root.toNat + 2 < n.toNat := by
              have : (((root <<< (1 : Nat)) + 1#64) + 1#64).toNat < n.toNat := by c0_bound
              omega
            have hch1_ana : (((root <<< (1 : Nat)) + 1#64) + 1#64).toNat < anaL.length := by omega
            let ac1 := anaL[(((root <<< (1 : Nat)) + 1#64) + 1#64).toNat]'hch1_ana
            have hac1_lt : (ac1.setWidth 64).toNat < qs.length := by
              have hg := hcovL (2 * root.toNat + 2) hch1_lt
              rw [List.getElem?_eq_getElem (by omega : 2 * root.toNat + 2 < anaL.length),
                Option.getD_some] at hg
              rw [zext_toNat _ (by decide)]
              have hac1_eq : ac1.toNat =
                  (anaL[2 * root.toNat + 2]'(by omega)).toNat := by
                dsimp only [ac1]; congr 2
              omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32]) (fun (qc1, ()) m2 => mL = m2)
              (fun Jqc1 (qc1, ()) m2 hm2 => ?_) (fun Jqc1 hJqc1 => ?_)
            · rcases hm2 with rfl; rw [Blocks.get_here]; dsimp only
              c0_hsteps
              · exact hJch _ mL ⟨rfl, by erw [hch1_eq]; exact hch1_lt, by erw [hch1_eq]; omega⟩
              · exact hJch _ mL ⟨rfl, by erw [hch_eq]; exact hch_lt, by erw [hch_eq]; omega⟩
            · c0_hsteps
              · exact hJqc1 _ mL rfl
              · exact hJqc1 _ mL rfl
          · exact hJch _ mL ⟨rfl, by erw [hch_eq]; exact hch_lt, by erw [hch_eq]; omega⟩
      · c0_hsteps
        · exact hJqc _ mL rfl
        · exact hJqc _ mL rfl
    · cases hc

end SortAnaWp

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
