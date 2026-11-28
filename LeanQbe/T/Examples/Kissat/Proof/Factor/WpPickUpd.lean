/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Candidate Picker and Heap-Update WP Proofs for `Src.Factor` (`2` Functions)

Proves parametric `Func.wp` contracts (`0` legacy imports, `0` placeholders,
`XPost`-polymorphic) for:
- `full_bva_pick_cand` (`step13BvaPickCandSpec`)
- `full_bva_upd_lit_fid` (`step9BvaUpdLitSpec`)
-/

set_option autoImplicit false

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

public section

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

/-! ## 1. Zero-Hop Upstream Candidate Picker (`full_bva_pick_cand`) -/

theorem full_bva_pick_cand_wp (Γ : Env) :
    ∀ a m Q X, step13BvaPickCandSpec a m Q X → Func.wp Γ full_bva_pick_cand_body a m Q X := by
  rintro ⟨h, ncntd, f0, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hf0_lt, hnc_le, hcntd_ok, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hrepr_len := hcl.repr_len
  have hws_len := hsc.wsort_len; have hws1_len := hsc.work_stk1_len
  unfold Func.wp full_bva_pick_cand_body
  c0_hsteps
  refine wp_loop_inv
    (fun (best_c, best_deg, best_lit, ci, ()) ml =>
      ml = m ∧ ci.toNat ≤ ncntd.toNat ∧
      (2 ≤ best_c.toNat → best_lit.toNat < 2 * s.core.cur_vars))
    (fun (_, _, _, ci, _) _ => ncntd.toNat - ci.toNat)
    (fun J1 hJ1 => by
      c0_hsteps
      exact hJ1 (0#32, 0#32, 0xFFFFFFFF#32, 0#32, ()) m
        ⟨rfl, Nat.zero_le _, fun h => by simp only [bv_c0] at h; omega⟩)
    (fun J1 (best_c, best_deg, best_lit, ci, ()) ml ⟨hml, hci_le, hbl_ok⟩ ih1 => ?_)
  rcases hml with rfl
  c0_hsteps_nogrp
  · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
    have hci64 : (BitVec.setWidth 64 ci).toNat = ci.toNat := by c0_bound
    have hclit_lt :
        (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
      have := hcntd_ok ci.toNat hci_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps
    all_goals first
      | exact ih1 (_, _, _, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, fun _ => by simpa only [hci64] using hclit_lt⟩
      | exact ih1 (_, _, best_lit, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, hbl_ok⟩
  · let mkSt (ws : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := s.core.repr, min_clr := s.core.min_clr,
                              tmp_cnt := s.core.tmp_cnt, tmp_len := s.core.tmp_len }
        scratch := { s.scratch with wsort := ws, ant_sz := s.scratch.ant_sz,
                                    sim_sig := s.scratch.sim_sig,
                                    shrink_stk := s.scratch.shrink_stk } }
    c0_hsteps
    refine wp_loop_inv
      (fun (ci, ()) m2 => ∃ ws2,
        ci.toNat ≤ ncntd.toNat ∧ ws2.length = 2 * c.max_vars ∧
        (FullMem c (mkSt ws2) ⋆ R) m2)
      (fun (ci, ()) _ => ncntd.toNat - ci.toNat)
      (fun J2 hJ2 => by
        c0_hsteps
        exact hJ2 (0#32, ()) ml ⟨s.scratch.wsort, Nat.zero_le _, hws_len, hm⟩)
      (fun J2 (ci, ()) m2 ⟨ws2, hci_le, hws2_len, hm2⟩ ih2 => ?_)
    dsimp only [mkSt] at hm2
    c0_hsteps_nogrp
    · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
      have hclit_lt :
          (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        have := hcntd_ok ci.toNat hci_lt
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
      c0_hsteps
      exact ih2 (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by simp [hws2_len], hm⟩
    · have hinv_fin : FullDenseInvNoLm c F0 F_cur (mkSt ws2) :=
        fullDenseInvNoLm_with_core_aux hinv hcl.repr_len hcl.min_clr_len_arr hcl.tmp_len_arr
          hcl.flags_len hcl.tmp_len_le { hsc with wsort_len := hws2_len } rfl rfl
      c0_hsteps
      · exact hQ 0xFFFFFFFF#32 s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin (Or.inl rfl) hm2
      · exact hQ best_lit s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin
          (Or.inr (hbl_ok (by c0_bound))) hm2

/-! ## 2. Packed-Arg Heap Update Helpers & Proof (`full_bva_upd_lit_fid`) -/

section UpdHelpers

private def S9FheapRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
  FullCoreU32A c s.core ⋆ array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
  array (t := i32) c.pFrameDec s.core.frame_dec ⋆ array (t := i32) c.pMinStk s.core.min_stk ⋆
  array (t := i32) c.pWvec s.core.wvec ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  array (t := i32) c.pWsort s.scratch.wsort ⋆ array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
  array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

private theorem s9_focus_fheap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
      array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
      array (t := i32) c.pRepr s.core.repr ⋆ (S9FheapRest c s ⋆ R)) m := by
  have h0 : (FullMem c s ⋆ R) =
      (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array (t := i32) c.pRepr s.core.repr ⋆ (S9FheapRest c s ⋆ R)) := by
    unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs S9FheapRest
    ac_rfl
  rw [h0] at hm; exact hm

private theorem s9_unfocus_fheap {c : FullCfg} {s : FullState} {hp' ps' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTarjanMark hp' ⋆
      array (t := i32) c.pTarjanReach ps' ⋆
      array (t := i32) c.pRepr s.core.repr ⋆ (S9FheapRest c s ⋆ R)) m) :
    (FullMem c
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆ R) m := by
  have h0 : (FullMem c
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆ R) =
      (array (t := i32) c.pTarjanMark hp' ⋆
        array (t := i32) c.pTarjanReach ps' ⋆
        array (t := i32) c.pRepr s.core.repr ⋆ (S9FheapRest c s ⋆ R)) := by
    unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs S9FheapRest
    ac_rfl
  rw [h0]; exact hm

private theorem s9_dense_set_fheap {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {hp' ps' : List (BitVec 32)}
    (hhp : hp'.length = 2 * c.max_vars) (hps : ps'.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } :=
  hinv.of_safetySlice
    ⟨hinv.1.lengths.core_ok,
      { hinv.1.lengths.scratch_ok with tarjan_mark_len := hhp, tarjan_reach_len := hps }⟩
    rfl ⟨rfl, rfl⟩

private theorem s9_dense_set_repr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {rp' : List (BitVec 32)} (hrp : rp'.length = 2 * c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with repr := rp' } } := by
  obtain ⟨F_cur, hinvW⟩ := hinv.exists_witness
  exact (fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := s.scratch) hinvW hrp hinvW.1.core_ok.min_clr_len_arr hinvW.1.core_ok.tmp_len_arr
    hinvW.1.core_ok.flags_len hinvW.1.core_ok.tmp_len_le hinvW.1.scratch_ok rfl rfl).toDense

private def S9HeapFr (s st : FullState) : Prop :=
  ∃ rp hp ps : List (BitVec 32), st =
    { s with core := { s.core with repr := rp }
             scratch := { s.scratch with tarjan_mark := hp, tarjan_reach := ps } }

private theorem s9HeapFr_refl (s : FullState) : S9HeapFr s s := ⟨_, _, _, rfl⟩

private theorem s9HeapFr_set_repr {s st : FullState} (h : S9HeapFr s st)
    (rp' : List (BitVec 32)) :
    S9HeapFr s { st with core := { st.core with repr := rp' } } := by
  obtain ⟨rp, hp, ps, rfl⟩ := h; exact ⟨rp', hp, ps, rfl⟩

private theorem s9HeapFr_set_fheap {s st : FullState} (h : S9HeapFr s st)
    (hp' ps' : List (BitVec 32)) :
    S9HeapFr s
      { st with scratch := { st.scratch with tarjan_mark := hp', tarjan_reach := ps' } } := by
  obtain ⟨rp, hp, ps, rfl⟩ := h; exact ⟨rp, hp', ps', rfl⟩

private theorem s9_heap_set_lt {hp : List (BitVec 32)} {n p lim : Nat} {v : BitVec 32}
    (hv : v.toNat < lim) (hprev : ∀ k < n, k ≠ p → (hp[k]?.getD 0#32).toNat < lim)
    (hp_lt : p < hp.length) :
    ∀ k < n, ((hp.set p v)[k]?.getD 0#32).toNat < lim := by
  intro k hk
  by_cases heq : k = p
  · subst heq; rw [List.getElem?_set_self hp_lt, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm heq)]; exact hprev k hk heq

private theorem s9_call_fheap_up {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx : BitVec 32} {k : Tup Val [] → Expr Val Cont rs} {n lim : Nat}
    (hinv : FullDenseInv c F0 st) (hidx : idx.toNat < n) (hn : n ≤ lim)
    (hlim : lim ≤ 2 * c.max_vars)
    (hhp : ∀ i < n, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < lim)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ hp' ps' m',
      FullDenseInv c F0
        { st with scratch := { st.scratch with tarjan_mark := hp', tarjan_reach := ps' } } →
      (∀ i < n, (hp'[i]?.getD 0#32).toNat < lim) →
      (FullMem c
        { st with scratch := { st.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆
        R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32]) "full_fheap_up_fid"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr, Arg.var idx, ()) k) m := by
  have hl := hinv.1.lengths
  have hmax31 : c.max_vars < 2 * 268435456 := c.hmaxv
  refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
  refine ⟨lim, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.repr,
    S9FheapRest c st ⋆ R,
    by rw [hl.scratch_ok.tarjan_mark_len]; exact hlim,
    by rw [hl.scratch_ok.tarjan_reach_len]; exact hlim,
    by rw [hl.core_ok.repr_len]; exact hlim,
    by omega,
    by change idx.toNat < lim; omega,
    fun i hi => hhp i (Nat.lt_of_le_of_lt hi hidx),
    s9_focus_fheap hm,
    fun hp' ps' m' hhp' hps' hperm hfix hm' => ?_⟩
  refine hk hp' ps' m'
    (s9_dense_set_fheap hinv (by rw [hhp', hl.scratch_ok.tarjan_mark_len])
      (by rw [hps', hl.scratch_ok.tarjan_reach_len])) (fun i hi => ?_) (s9_unfocus_fheap hm')
  by_cases hle : i ≤ idx.toNat
  · obtain ⟨j, hj, heq⟩ := hperm i hle; rw [heq]
    exact hhp j (Nat.lt_of_le_of_lt hj hidx)
  · rw [hfix i (Nat.lt_of_not_le hle)]; exact hhp i hi

private theorem s9_call_fheap_down {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx n : BitVec 32} {k : Tup Val [] → Expr Val Cont rs} {lim : Nat}
    (hinv : FullDenseInv c F0 st) (hidx : idx.toNat < n.toNat) (hn : n.toNat ≤ lim)
    (hlim : lim ≤ 2 * c.max_vars)
    (hhp : ∀ i < n.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < lim)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ hp' ps' m',
      FullDenseInv c F0
        { st with scratch := { st.scratch with tarjan_mark := hp', tarjan_reach := ps' } } →
      (∀ i < n.toNat, (hp'[i]?.getD 0#32).toNat < lim) →
      (FullMem c
        { st with scratch := { st.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆
        R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32, i32]) "full_fheap_down_fid"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
       Arg.var idx, Arg.var n, ()) k) m := by
  have hl := hinv.1.lengths
  have hmax31 : c.max_vars < 2 * 268435456 := c.hmaxv
  refine wp_call_of_spec _ _ (hDown _ _ _ _ ?_)
  refine ⟨lim, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.repr,
    S9FheapRest c st ⋆ R,
    by rw [hl.scratch_ok.tarjan_mark_len]; exact hlim,
    by rw [hl.scratch_ok.tarjan_reach_len]; exact hlim,
    by rw [hl.core_ok.repr_len]; exact hlim,
    by omega, hidx, hn, hhp, s9_focus_fheap hm,
    fun hp' ps' m' hhp' hps' hperm _ hm' => ?_⟩
  refine hk hp' ps' m'
    (s9_dense_set_fheap hinv (by rw [hhp', hl.scratch_ok.tarjan_mark_len])
      (by rw [hps', hl.scratch_ok.tarjan_reach_len])) (fun i hi => ?_) (s9_unfocus_fheap hm')
  obtain ⟨j, hj, heq⟩ := hperm i hi; rw [heq]; exact hhp j hj

private def S9UpdInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop)
    (hsz' : BitVec 32) (m' : Mem 64) : Prop :=
  ∃ st : FullState, FullDenseInv c F0 st ∧ S9HeapFr s st ∧
    hsz'.toNat ≤ 2 * s.core.cur_vars ∧
    (∀ k < hsz'.toNat, (st.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c st ⋆ R) m'

end UpdHelpers

theorem full_bva_upd_lit_fid_wp (Γ : Env)
    (hCountDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, step9BvaUpdLitSpec a m Q X →
      Func.wp Γ full_bva_upd_lit_fid_body a m Q X := by
  rintro ⟨h, fheap, fpos, deg, cur_nl, hsz_tl, ⟨⟩⟩ m0 Q X
    ⟨c, F0, s, R, hsz, tl, rfl, rfl, rfl, rfl, hpack, hinv, hnl, htl, hhsz, hhp, hm0, hQ⟩
  subst hpack
  have hmaxv := c.hmaxv
  have hmax29 : c.max_vars < 2 ^ 29 := by
    change c.max_vars < 2 * 268435456 at hmaxv; omega
  have hl := hinv.1.lengths
  have hcv_le := hl.core_ok.cur_vars_le
  unfold Func.wp full_bva_upd_lit_fid_body
  c0_hfast_nogrp
  rw [bv64_pack32_hi hsz tl, bv64_pack32_lo hsz tl]
  obtain ⟨F_cur, hdw⟩ := hinv.exists_witness
  fid_call hCountDeg
  refine ⟨c, F0, F_cur, s, R, rfl, hdw, htl, hm0, fun nd => ?_⟩
  have htl_rp : (BitVec.setWidth 64 tl).toNat < s.core.repr.length := by
    rw [fid_bv64_32, hl.core_ok.repr_len]; omega
  have htl_rc : (BitVec.setWidth 64 tl).toNat < s.scratch.tarjan_reach.length := by
    rw [fid_bv64_32, hl.scratch_ok.tarjan_reach_len]; omega
  c0_hfast_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32) id (S9UpdInv c F0 s R)
    (fun _ h' m' ⟨st, hinv', hfr, hle', hhp', hm'⟩ => by
      dsimp only [Blocks.get, id]; c0_hfast
      obtain ⟨rp, hp, ps, rfl⟩ := hfr
      exact hQ h' rp hp ps m' hinv' hle' hhp' hm')
    (fun Jret hJret => ?_)
  c0_hfast_nogrp
  · refine wp_join0 (S9UpdInv c F0 s R hsz) ?_ (fun J1 hJ1 => ?_)
    · rintro _ m1 ⟨st, hinvt, hfrt, -, hhpt, hmt⟩
      have hlt := hinvt.1.lengths
      have htl_rct : (BitVec.setWidth 64 tl).toNat < st.scratch.tarjan_reach.length := by
        rw [fid_bv64_32, hlt.scratch_ok.tarjan_reach_len]; omega
      dsimp only [Blocks.get]
      refine wp_join_state1 (t := i32) (α := BitVec 32) id (S9UpdInv c F0 s R)
        (fun _ h' m' hI => by dsimp only [Blocks.get, id]; c0_hfast; exact hJret h' m' hI)
        (fun J2 hJ2 => ?_)
      c0_hfast_nogrp
      · have hsz_lt : hsz.toNat < 2 * s.core.cur_vars := by rw [← hnl]; exact hc
        have hsz_mk : (BitVec.setWidth 64 hsz).toNat < st.scratch.tarjan_mark.length := by
          rw [fid_bv64_32, hlt.scratch_ok.tarjan_mark_len]; omega
        have hadd1 : (hsz + 1#32).toNat = hsz.toNat + 1 := s9_bv32_add1 (by omega)
        c0_hfast_nogrp
        let st1 : FullState :=
          { st with scratch :=
            { st.scratch with
              tarjan_mark := st.scratch.tarjan_mark.set (BitVec.setWidth 64 hsz).toNat tl
              tarjan_reach := st.scratch.tarjan_reach.set (BitVec.setWidth 64 tl).toNat hsz } }
        have hinv_t1 : FullDenseInv c F0 st1 :=
          s9_dense_set_fheap hinvt (by simp [hlt.scratch_ok.tarjan_mark_len])
            (by simp [hlt.scratch_ok.tarjan_reach_len])
        refine s9_call_fheap_up hUp hinv_t1 (n := hsz.toNat + 1) (lim := 2 * s.core.cur_vars)
          (Nat.lt_succ_self _) (by omega) (by omega) ?_ (by assumption)
          fun hp2 ps2 m2 hinv2 hhp2 hm2 => ?_
        · dsimp only [st1]; rw [fid_bv64_32]
          exact s9_heap_set_lt htl (fun k hk _ => hhpt k (by omega))
            (by rw [hlt.scratch_ok.tarjan_mark_len]; omega)
        · c0_hfast
          exact hJ2 (hsz + 1#32) m2 ⟨_, hinv2,
            s9HeapFr_set_fheap (s9HeapFr_set_fheap hfrt _ _) _ _, by rw [hadd1]; omega,
            fun k hk => hhp2 k (by rw [hadd1] at hk; exact hk), hm2⟩
      all_goals exact hJ2 hsz _ ⟨st, hinvt, hfrt, hhsz, hhpt, by assumption⟩
    · c0_hfast_nogrp
      · let s1 : FullState :=
          { s with core :=
            { s.core with repr := s.core.repr.set (BitVec.setWidth 64 tl).toNat nd } }
        have hinv1 : FullDenseInv c F0 s1 :=
          s9_dense_set_repr hinv (by simp [hl.core_ok.repr_len])
        have hfr1 : S9HeapFr s s1 := s9HeapFr_set_repr (s9HeapFr_refl s) _
        refine wp_join0 (S9UpdInv c F0 s R hsz)
          (fun _ m' hI => by c0_hfast; exact hJ1 m' hI) (fun J3 hJ3 => ?_)
        c0_hfast_nogrp
        · have hp_lt := hc
          refine wp_join0 (S9UpdInv c F0 s R hsz)
            (fun _ m' hI => by c0_hfast; exact hJ3 m' hI) (fun J4 hJ4 => ?_)
          c0_hfast_nogrp
          · refine s9_call_fheap_up hUp hinv1 (n := hsz.toNat) (lim := 2 * s.core.cur_vars)
              hp_lt hhsz (by omega) hhp (by assumption) fun hp2 ps2 m2 hinv2 hhp2 hm2 => ?_
            c0_hfast
            exact hJ4 m2 ⟨_, hinv2, s9HeapFr_set_fheap hfr1 _ _, hhsz, hhp2, hm2⟩
          · refine s9_call_fheap_down hDown hinv1 (lim := 2 * s.core.cur_vars)
              hp_lt hhsz (by omega) hhp (by assumption) fun hp2 ps2 m2 hinv2 hhp2 hm2 => ?_
            c0_hfast
            exact hJ4 m2 ⟨_, hinv2, s9HeapFr_set_fheap hfr1 _ _, hhsz, hhp2, hm2⟩
        · exact hJ3 _ ⟨s1, hinv1, hfr1, hhsz, hhp, by assumption⟩
      · exact hJ1 _ ⟨s, hinv, s9HeapFr_refl s, hhsz, hhp, hm0⟩
  · let s1 : FullState :=
      { s with core :=
        { s.core with repr := s.core.repr.set (BitVec.setWidth 64 tl).toNat nd } }
    have hinv1 : FullDenseInv c F0 s1 := s9_dense_set_repr hinv (by simp [hl.core_ok.repr_len])
    have hfr1 : S9HeapFr s s1 := s9HeapFr_set_repr (s9HeapFr_refl s) _
    refine wp_join_state1 (t := i32) (α := BitVec 32) id (S9UpdInv c F0 s R)
      (fun _ h' m' hI => by dsimp only [Blocks.get, id]; c0_hfast; exact hJret h' m' hI)
      (fun J5 hJ5 => ?_)
    c0_hfast_nogrp
    · have hp_lt := hc
      have hsz_pos : 0 < hsz.toNat := by omega
      have hsz1 : (hsz - 1#32).toNat = hsz.toNat - 1 := s9_bv32_sub1 hsz_pos
      have hsz1_mk :
          (BitVec.setWidth 64 (hsz - 1#32)).toNat < s1.scratch.tarjan_mark.length := by
        rw [fid_bv64_32, hsz1]; change _ < s.scratch.tarjan_mark.length
        rw [hl.scratch_ok.tarjan_mark_len]; omega
      let last : BitVec 32 :=
        s1.scratch.tarjan_mark[(BitVec.setWidth 64 (hsz - 1#32)).toNat]'hsz1_mk
      have hlast_lt : last.toNat < 2 * s.core.cur_vars := by
        have h1 := hhp (hsz - 1#32).toNat (by rw [hsz1]; omega)
        rw [List.getElem?_eq_getElem (by rw [hl.scratch_ok.tarjan_mark_len]; omega),
          Option.getD_some] at h1
        simpa only [last, fid_bv64_32] using h1
      have hlast_rc :
          (BitVec.setWidth 64 last).toNat < s1.scratch.tarjan_reach.length := by
        rw [fid_bv64_32]; change _ < s.scratch.tarjan_reach.length
        rw [hl.scratch_ok.tarjan_reach_len]; omega
      have htl_rc1 : (BitVec.setWidth 64 tl).toNat <
          (s1.scratch.tarjan_reach.set (BitVec.setWidth 64 last).toNat 0xFFFFFFFF#32).length := by
        rw [List.length_set]; exact htl_rc
      c0_hfast_nogrp
      let s2 : FullState :=
        { s1 with scratch :=
          { s1.scratch with
            tarjan_reach :=
              (s1.scratch.tarjan_reach.set (BitVec.setWidth 64 last).toNat 0xFFFFFFFF#32).set
                (BitVec.setWidth 64 tl).toNat 0xFFFFFFFF#32 } }
      have hinv2 : FullDenseInv c F0 s2 :=
        s9_dense_set_fheap hinv1 hl.scratch_ok.tarjan_mark_len
          (by simp [s1, hl.scratch_ok.tarjan_reach_len])
      have hfr2 : S9HeapFr s s2 := s9HeapFr_set_fheap hfr1 _ _
      have hhp_pop : ∀ k < (hsz - 1#32).toNat,
          (s.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
        fun k hk => hhp k (by rw [hsz1] at hk; omega)
      refine wp_join0 (S9UpdInv c F0 s R (hsz - 1#32))
        (fun _ m' hI => by c0_hfast; exact hJ5 (hsz - 1#32) m' hI) (fun J6 hJ6 => ?_)
      c0_hfast_nogrp
      · let pv : BitVec 32 := s.scratch.tarjan_reach[(BitVec.setWidth 64 tl).toNat]'htl_rc
        have hp_lt1 : pv.toNat < (hsz - 1#32).toNat := hc
        have hpv_mk : (BitVec.setWidth 64 pv).toNat < s2.scratch.tarjan_mark.length := by
          rw [fid_bv64_32]; change _ < s.scratch.tarjan_mark.length
          rw [hl.scratch_ok.tarjan_mark_len]; omega
        have hlast_rc2 :
            (BitVec.setWidth 64 last).toNat < s2.scratch.tarjan_reach.length := by
          dsimp only [s2]; rw [List.length_set, List.length_set]; exact hlast_rc
        c0_hfast_nogrp
        let s3 : FullState :=
          { s2 with scratch :=
            { s2.scratch with
              tarjan_mark := s2.scratch.tarjan_mark.set (BitVec.setWidth 64 pv).toNat last
              tarjan_reach := s2.scratch.tarjan_reach.set (BitVec.setWidth 64 last).toNat pv } }
        have hinv3 : FullDenseInv c F0 s3 :=
          s9_dense_set_fheap hinv2 (by simp [s2, s1, hl.scratch_ok.tarjan_mark_len])
            (by simp [s2, s1, hl.scratch_ok.tarjan_reach_len])
        have hfr3 : S9HeapFr s s3 := s9HeapFr_set_fheap hfr2 _ _
        refine s9_call_fheap_up hUp hinv3 (n := (hsz - 1#32).toNat)
          (lim := 2 * s.core.cur_vars) hp_lt1 (by rw [hsz1]; omega) (by omega) ?_ (by assumption)
          fun hp4 ps4 m4 hinv4 hhp4 hm4 => ?_
        · dsimp only [s3, s2, s1]; rw [fid_bv64_32]
          exact s9_heap_set_lt hlast_lt (fun k hk _ => hhp_pop k hk)
            (by rw [hl.scratch_ok.tarjan_mark_len]; omega)
        · have hlast_rc4 : (BitVec.setWidth 64 last).toNat < ps4.length := by
            have h4 : ps4.length = 2 * c.max_vars := hinv4.1.lengths.scratch_ok.tarjan_reach_len
            rw [fid_bv64_32, h4]; omega
          c0_hfast_nogrp
          refine wp_join0 (S9UpdInv c F0 s R (hsz - 1#32))
            (fun _ m' hI => by c0_hfast; exact hJ6 m' hI) (fun J7 hJ7 => ?_)
          c0_hfast_nogrp
          · refine s9_call_fheap_down hDown hinv4 (lim := 2 * s.core.cur_vars) hc
              (by change (hsz - 1#32).toNat ≤ _; rw [hsz1]; omega) (by omega) hhp4 hm4
              fun hp5 ps5 m5 hinv5 hhp5 hm5 => ?_
            c0_hfast
            exact hJ7 m5 ⟨_, hinv5, s9HeapFr_set_fheap (s9HeapFr_set_fheap hfr3 _ _) _ _,
              by rw [hsz1]; omega, hhp5, hm5⟩
          · exact hJ7 _ ⟨_, hinv4, s9HeapFr_set_fheap hfr3 _ _, by rw [hsz1]; omega, hhp4, hm4⟩
      · exact hJ6 _ ⟨s2, hinv2, hfr2, by rw [hsz1]; omega, hhp_pop, by assumption⟩
    · exact hJ5 hsz _ ⟨s1, hinv1, hfr1, hhsz, hhp, by assumption⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
