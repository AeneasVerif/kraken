/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
/-!
# Kissat Fidelity BVA Proofs — Part 3a (`full_factor_fid_wp`)

M1-clean UNSAT-only parametric `(Γ : Env)` `Func.wp` proof (`public section`, firewall-clean,
`0` axioms, `XPost`-polymorphic) for `full_factor_body` against
canonical `FullBvaHeap.fullFactorHeapSpec` (`GAP-BVA-01/02/03`: dynamic `steps_cap`,
`connect_clauses` peeling, `deg = h->repr` binary max-heap with `pop_heap` on `deg <= 1`,
lexicographic termination `(c.max_vars - cur_vars) * (2 * c.max_vars + 1) + hsz` under
arbitrary tick budgets).
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics
/-! ## 1. `full_factor` Heap-Focusing & Arithmetic Helpers -/

section FactorHelpers

private def FullMemFidFheapRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
  FullCoreU32A c s.core ⋆ array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
  array (t := i32) c.pFrameDec s.core.frame_dec ⋆ array (t := i32) c.pMinStk s.core.min_stk ⋆
  array (t := i32) c.pWvec s.core.wvec ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  array (t := i32) c.pWsort s.scratch.wsort ⋆ array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
  array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

private theorem focus_fid_fheap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
      array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
      array (t := i32) c.pRepr s.core.repr ⋆ (FullMemFidFheapRest c s ⋆ R)) m := by
  have h0 : (FullMem c s ⋆ R) =
      (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array (t := i32) c.pRepr s.core.repr ⋆ (FullMemFidFheapRest c s ⋆ R)) := by
    unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs FullMemFidFheapRest
    ac_rfl
  rw [h0] at hm; exact hm

private theorem unfocus_fid_fheap {c : FullCfg} {s : FullState} {hp' ps' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTarjanMark hp' ⋆
      array (t := i32) c.pTarjanReach ps' ⋆
      array (t := i32) c.pRepr s.core.repr ⋆ (FullMemFidFheapRest c s ⋆ R)) m) :
    (FullMem c
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆ R) m := by
  have h0 : (FullMem c
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆ R) =
      (array (t := i32) c.pTarjanMark hp' ⋆
        array (t := i32) c.pTarjanReach ps' ⋆
        array (t := i32) c.pRepr s.core.repr ⋆ (FullMemFidFheapRest c s ⋆ R)) := by
    unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs FullMemFidFheapRest
    ac_rfl
  rw [h0]; exact hm

private def setWtpFid (s : FullState) (ws hp ps : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with wsort := ws, tarjan_mark := hp, tarjan_reach := ps } }

private theorem fullDenseInv_set_ant {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) (a : BitVec 64) :
    FullDenseInv c F0 { s with scratch := { s.scratch with ant_sz := a } } :=
  hinv.of_safetySlice
    ⟨hinv.1.lengths.core_ok,
      { hinv.1.lengths.scratch_ok with wsort_len := hinv.1.lengths.scratch_ok.wsort_len }⟩
    rfl ⟨rfl, rfl⟩

private theorem fullDenseInv_set_fheap {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {hp' ps' : List (BitVec 32)}
    (hhp : hp'.length = 2 * c.max_vars) (hps : ps'.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } :=
  hinv.of_safetySlice
    ⟨hinv.1.lengths.core_ok,
      { hinv.1.lengths.scratch_ok with tarjan_mark_len := hhp, tarjan_reach_len := hps }⟩
    rfl ⟨rfl, rfl⟩

private theorem fullDenseInv_set_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hinvW⟩ := hinv.exists_witness
  exact (FullBvaHeap.fullDenseInvW_set_flags hinvW hfl).toDense

private theorem fullDenseInv_set_repr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {rp' : List (BitVec 32)} (hrp : rp'.length = 2 * c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with repr := rp' } } := by
  obtain ⟨F_cur, hinvW⟩ := hinv.exists_witness
  exact (fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := s.scratch) hinvW hrp hinvW.1.core_ok.min_clr_len_arr hinvW.1.core_ok.tmp_len_arr
    hinvW.1.core_ok.flags_len hinvW.1.core_ok.tmp_len_le hinvW.1.scratch_ok rfl rfl).toDense

private theorem fullDenseInv_set_qstamp {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {qs' : List (BitVec 32)} {qcs' qss' : BitVec 64}
    (hqs : qs'.length = c.max_vars) :
    FullDenseInv c F0
      { s with scratch :=
        { s.scratch with q_stamp := qs', q_cur_stamp := qcs', q_search_stamp := qss' } } :=
  hinv.of_safetySlice
    ⟨hinv.1.lengths.core_ok, { hinv.1.lengths.scratch_ok with q_stamp_len := hqs }⟩
    rfl ⟨rfl, rfl⟩

private theorem fheap_push_pre_lt_bv {hp : List (BitVec 32)} {hlen : Nat} {lit : BitVec 32}
    {lim : Nat} (hlt : lit.toNat < lim) (hhl_lt : hlen < hp.length)
    (hprev : ∀ k < hlen, (hp[k]?.getD 0#32).toNat < lim) :
    ∀ i ≤ hlen, ((hp.set hlen lit)[i]?.getD 0#32).toNat < lim := by
  intro i hi
  by_cases heq : i = hlen
  · subst heq; rw [List.getElem?_set_self hhl_lt, Option.getD_some]; exact hlt
  · rw [List.getElem?_set_ne (Ne.symm heq)]
    exact hprev i (Nat.lt_of_le_of_ne hi heq)

private theorem fheap_up_post_lt {hp_pre hp' : List (BitVec 32)} {p hlen_new lim : Nat}
    (hpre : ∀ i ≤ p, (hp_pre[i]?.getD 0#32).toNat < lim)
    (hprev : ∀ k < hlen_new, k > p → (hp_pre[k]?.getD 0#32).toNat < lim)
    (hperm : ∀ i ≤ p, ∃ j ≤ p, hp'[i]? = hp_pre[j]?)
    (hfix : ∀ i, p < i → hp'[i]? = hp_pre[i]?) :
    ∀ k < hlen_new, (hp'[k]?.getD 0#32).toNat < lim := by
  intro k hk
  by_cases hle : k ≤ p
  · obtain ⟨j, hj, heq⟩ := hperm k hle; rw [heq]; exact hpre j hj
  · have hgt : p < k := Nat.lt_of_not_le hle; rw [hfix k hgt]; exact hprev k hk hgt

private theorem fheap_down_post_lt {hp_pre hp' : List (BitVec 32)} {n lim : Nat}
    (hpre : ∀ i < n, (hp_pre[i]?.getD 0#32).toNat < lim)
    (hperm : ∀ i < n, ∃ j < n, hp'[i]? = hp_pre[j]?) :
    ∀ k < n, (hp'[k]?.getD 0#32).toNat < lim := by
  intro k hk; obtain ⟨j, hj, heq⟩ := hperm k hk; rw [heq]; exact hpre j hj

private theorem fac_pl_bv32_toNat {vi : BitVec 64} {cv : Nat}
    (hvi : vi.toNat < cv) (hcv : 2 * cv < 2 ^ 32) :
    (BitVec.setWidth 32 (vi <<< (1 : Nat))).toNat = 2 * vi.toNat := by
  have hsh : (vi <<< (1 : Nat)).toNat = 2 * vi.toNat := by
    simp [BitVec.toNat_shiftLeft]; omega
  rw [BitVec.toNat_setWidth, hsh]; exact Nat.mod_eq_of_lt (by omega)

private theorem fac_nl_bv32_toNat {vi : BitVec 64} {cv : Nat}
    (hvi : vi.toNat < cv) (hcv : 2 * cv < 2 ^ 32) :
    (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32).toNat = 2 * vi.toNat + 1 := by
  have hsw := fac_pl_bv32_toNat hvi hcv
  rw [FullBvaFwdTactics.bv32_or1_of_even (by omega), hsw]

private theorem fac_nl_64 {vi : BitVec 64} {cv : Nat}
    (hvi : vi.toNat < cv) (hcv : 2 * cv < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat =
      2 * vi.toNat + 1 := by
  rw [fid_bv64_32, fac_nl_bv32_toNat hvi hcv]

private theorem fac_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fac_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fac_bv32_sub1 {x : BitVec 32} (h : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  have hle : (1#32 : BitVec 32).toNat ≤ x.toNat := h
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]; rfl

private theorem fac_fl_lit_lt {lit : BitVec 32} {len cv : Nat}
    (hlt : lit.toNat < 2 * cv) (hlen : cv ≤ len) :
    (BitVec.setWidth 64 (lit >>> (1 : Nat))).toNat < len := by
  rw [fid_bv64_32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega

private theorem fac_fl_lit_lt_bv {lit : BitVec 32} {len cv : Nat}
    (hlt : lit.toNat < 2 * cv) (hlen : cv ≤ len) :
    (BitVec.setWidth 64 (lit >>> (1 : BitVec 32))).toNat < len := by
  rw [fid_bv64_32]
  have hsh : (lit >>> (1 : BitVec 32)).toNat = lit.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem fac_lex_dec_cv {maxv cv1 cv2 h1 h2 : Nat}
    (hcv_lt : cv1 < cv2) (hcv2_le : cv2 ≤ maxv) (hh2 : h2 ≤ 2 * maxv) :
    (maxv - cv2) * (2 * maxv + 1) + h2 < (maxv - cv1) * (2 * maxv + 1) + h1 := by
  have hsub : maxv - cv2 + 1 ≤ maxv - cv1 := by omega
  have hmul : (maxv - cv2 + 1) * (2 * maxv + 1) ≤ (maxv - cv1) * (2 * maxv + 1) :=
    Nat.mul_le_mul_right _ hsub
  rw [Nat.add_one_mul] at hmul
  omega

private theorem fac_lex_dec_hsz {maxv cv1 cv2 h1 h2 : Nat}
    (hcv_le : cv1 ≤ cv2) (hh_lt : h2 < h1) :
    (maxv - cv2) * (2 * maxv + 1) + h2 < (maxv - cv1) * (2 * maxv + 1) + h1 := by
  have hmul : (maxv - cv2) * (2 * maxv + 1) ≤ (maxv - cv1) * (2 * maxv + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

private theorem fid_wp_call_fheap_up {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx : BitVec 32} {k : Tup Val [] → Expr Val Cont rs} {hlen_chk : Nat}
    (hinv : FullDenseInv c F0 st) (hmaxv : c.max_vars < 2 * dimacsBound)
    (hidx_lt : idx.toNat < hlen_chk) (hhlen_le : hlen_chk ≤ 2 * st.core.cur_vars)
    (hhpp : ∀ i < hlen_chk, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ st' m',
      FullDenseInv c F0 st' →
      st'.core = st.core →
      st'.scratch.work_stk2 = st.scratch.work_stk2 →
      (∀ i < hlen_chk, (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) →
      (FullMem c st' ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32]) "full_fheap_up_fid"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr, Arg.var idx, ()) k) m := by
  have hl := hinv.1.lengths
  have hcv_le := hl.core_ok.cur_vars_le
  have hmax31 : c.max_vars < 2 * 268435456 := hmaxv
  refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
  refine ⟨2 * st.core.cur_vars, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.repr,
    FullMemFidFheapRest c st ⋆ R,
    by rw [hl.scratch_ok.tarjan_mark_len]; omega,
    by rw [hl.scratch_ok.tarjan_reach_len]; omega,
    by rw [hl.core_ok.repr_len]; omega,
    by omega,
    by change idx.toNat < 2 * st.core.cur_vars; exact Nat.lt_of_lt_of_le hidx_lt hhlen_le,
    fun i hi => hhpp i (Nat.lt_of_le_of_lt hi hidx_lt),
    focus_fid_fheap hm,
    fun hp' ps' m' hhp' hps' hperm hfix hm' => ?_⟩
  let st' : FullState :=
    { st with scratch := { st.scratch with tarjan_mark := hp', tarjan_reach := ps' } }
  have hinv' : FullDenseInv c F0 st' :=
    fullDenseInv_set_fheap hinv
      (by rw [hhp', hl.scratch_ok.tarjan_mark_len])
      (by rw [hps', hl.scratch_ok.tarjan_reach_len])
  have hhp'2 : ∀ i < hlen_chk,
      (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars :=
    fheap_up_post_lt (fun i hi => hhpp i (Nat.lt_of_le_of_lt hi hidx_lt))
      (fun i hi _ => hhpp i hi) hperm hfix
  exact hk st' m' hinv' rfl rfl hhp'2 (unfocus_fid_fheap hm')

private theorem fid_wp_call_fheap_down {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx n : BitVec 32} {k : Tup Val [] → Expr Val Cont rs}
    (hinv : FullDenseInv c F0 st) (hmaxv : c.max_vars < 2 * dimacsBound)
    (hidx_lt : idx.toNat < n.toNat) (hn_le : n.toNat ≤ 2 * st.core.cur_vars)
    (hhpp : ∀ i < n.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ st' m',
      FullDenseInv c F0 st' →
      st'.core = st.core →
      st'.scratch.work_stk2 = st.scratch.work_stk2 →
      (∀ i < n.toNat, (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) →
      (FullMem c st' ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32, i32]) "full_fheap_down_fid"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
       Arg.var idx, Arg.var n, ()) k) m := by
  have hl := hinv.1.lengths
  have hcv_le := hl.core_ok.cur_vars_le
  have hmax31 : c.max_vars < 2 * 268435456 := hmaxv
  refine wp_call_of_spec _ _ (hDown _ _ _ _ ?_)
  refine ⟨2 * st.core.cur_vars, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.repr,
    FullMemFidFheapRest c st ⋆ R,
    by rw [hl.scratch_ok.tarjan_mark_len]; omega,
    by rw [hl.scratch_ok.tarjan_reach_len]; omega,
    by rw [hl.core_ok.repr_len]; omega,
    by omega, hidx_lt, hn_le, hhpp, focus_fid_fheap hm,
    fun hp' ps' m' hhp' hps' hperm _ hm' => ?_⟩
  let st' : FullState :=
    { st with scratch := { st.scratch with tarjan_mark := hp', tarjan_reach := ps' } }
  have hinv' : FullDenseInv c F0 st' :=
    fullDenseInv_set_fheap hinv
      (by rw [hhp', hl.scratch_ok.tarjan_mark_len])
      (by rw [hps', hl.scratch_ok.tarjan_reach_len])
  have hhp'2 : ∀ i < n.toNat,
      (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars :=
    fheap_down_post_lt hhpp hperm
  exact hk st' m' hinv' rfl rfl hhp'2 (unfocus_fid_fheap hm')

end FactorHelpers

private theorem fid_wp_call_steps_cap {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    {x : BitVec 64} {m : Mem 64} {k : Tup Val [i32] → Expr Val Cont rs}
    (hk : wp Γ Q X (k (BitVec.ofNat 32 (fidStepsCap x.toNat), ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) "full_bva_steps_cap_fid" (Arg.var x, ()) k) m :=
  wp_call_of_spec _ _ (hSteps _ _ _ _ hk)

private def fidLoop4VmtfExpr (c : FullCfg) (init_cv cv : Nat) : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun Js => Blocks.cons
      (fun p =>
        .let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
            (Arg.var p.fst, Arg.var (BitVec.ofNat 64 cv <<< (1 : Nat)), ())) fun p_1 =>
        .jnz (Arg.var p_1.fst)
          (.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_2 =>
           .let_ (Op.mk (.add i64) (Arg.var c.pTarjanMark, Arg.var p_2.fst, ())) fun p_3 =>
           .store (t := i32) (Arg.imm 0) (Arg.var p_3.fst)
             (.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_4 =>
              .let_ (Op.mk (.add i64) (Arg.var c.pTarjanReach, Arg.var p_4.fst, ())) fun p_5 =>
              .store (t := i32) (Arg.imm 0) (Arg.var p_5.fst)
                (.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p_6 =>
                  .jump Js.fst (Arg.var p_6.fst, ()))))
          (.group (sig := [[]])
            (fun _ => Blocks.cons (fun _ => .ret (Arg.imm 1, ())) Blocks.nil) fun Js =>
           .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p0 =>
           .load i64 (Arg.var p0.fst) fun ld =>
           .let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
               (Arg.var ld, Arg.var (BitVec.ofNat 64 init_cv), ())) fun p1 =>
           .jnz (Arg.var p1.fst)
             (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p2 =>
              .load i64 (Arg.var p2.fst) fun ld =>
              .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 376, ())) fun p3 =>
              .load i64 (Arg.var p3.fst) fun ld_1 =>
              .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 384, ())) fun p4 =>
              .load i64 (Arg.var p4.fst) fun ld_2 =>
              .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 608, ())) fun p5 =>
              .load i64 (Arg.var p5.fst) fun ld_3 =>
              .group (sig := [[i64, i64]])
                (fun Js_1 => Blocks.cons
                  (fun p =>
                    .group (sig := [[]])
                      (fun _ => Blocks.cons
                        (fun _ =>
                          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 640, ())) fun p_3 =>
                          .store (t := i64) (Arg.var p.snd.fst) (Arg.var p_3.fst)
                            (.group (sig := [[]])
                              (fun _ => Blocks.cons (fun _ => .jump Js.fst ()) Blocks.nil)
                              fun Js =>
                              .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 624, ())) fun pa =>
                              .load i64 (Arg.var pa.fst) fun ld_4 =>
                              .let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                                  (Arg.var ld_4, Arg.var ld, ())) fun pb =>
                              .jnz (Arg.var pb.fst)
                                (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 624, ()))
                                    fun pc =>
                                  .load i64 (Arg.var pc.fst) fun ld =>
                                  .let_ (Op.mk (.mul i64) (Arg.var ld, Arg.imm 4, ())) fun pd =>
                                  .let_ (Op.mk (.add i64) (Arg.var ld_2, Arg.var pd.fst, ()))
                                    fun pe =>
                                  .load i32 (Arg.var pe.fst) fun ld =>
                                  .let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun pf =>
                                  .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 632, ()))
                                    fun p_4 =>
                                  .store (t := i64) (Arg.var pf.fst) (Arg.var p_4.fst)
                                    (.jump Js.fst ()))
                                (.jump Js.fst ())))
                        Blocks.nil)
                      fun Js =>
                      .let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                          (Arg.var p.fst, Arg.var ld, ())) fun p_2 =>
                      .jnz (Arg.var p_2.fst)
                        (.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                            (Arg.var p.snd.fst, Arg.var ld, ())) fun p_3 =>
                         .jnz (Arg.var p_3.fst)
                           (.let_ (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p_4 =>
                            .let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_5 =>
                            .let_ (Op.mk (.add i64) (Arg.var ld_2, Arg.var p_5.fst, ())) fun p_6 =>
                            .let_ (Op.mk (.trunc 64 32) (Arg.var p_4.fst, ())) fun p_7 =>
                            .store (t := i32) (Arg.var p_7.fst) (Arg.var p_6.fst)
                              (.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun pg =>
                               .let_ (Op.mk (.add i64) (Arg.var ld_1, Arg.var pg.fst, ())) fun ph =>
                               .load i32 (Arg.var ph.fst) fun ld =>
                               .let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun pi =>
                               .jump Js_1.fst (Arg.var pi.fst, Arg.var p_4.fst, ())))
                           (.jump Js.fst ()))
                        (.jump Js.fst ()))
                  Blocks.nil)
                (fun Js => .jump Js.fst (Arg.var ld_3, Arg.imm 0, ())))
             (.jump Js.fst ())))
      Blocks.nil)
    (fun Js => .jump Js.fst (Arg.imm 0, ()))

private theorem factor_loop4_vmtf_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {stb : FullState} {init_cv : Nat} {init_fuel : BitVec 64}
    {R : Mem 64 → Prop} {mb : Mem 64}
    (hinvb : FullDenseInv c F0 stb) (hcvb : init_cv ≤ stb.core.cur_vars)
    (hfub : stb.core.fuel = init_fuel)
    (hmb : (FullMem c stb ⋆ R) mb)
    (hQ : ∀ r s' m', FullDenseInv c F0 s' → init_cv ≤ s'.core.cur_vars →
      s'.core.fuel = init_fuel → r = 1#64 → (FullMem c s' ⋆ R) m' →
      Q (r, ()) m') :
    wp Γ Q X (fidLoop4VmtfExpr c init_cv stb.core.cur_vars) mb := by
  have hbl := hinvb.1.lengths
  have hb_cv_le := hbl.core_ok.cur_vars_le
  have hmaxv := c.hmaxv
  have hmax_lt32 : c.max_vars < 2 ^ 29 := by
    change c.max_vars < 2 * 268435456 at hmaxv; omega
  have hb_lt64 : 2 * stb.core.cur_vars < 2 ^ 64 := by omega
  unfold fidLoop4VmtfExpr
  refine wp_loop_inv
    (fun (ci, ()) mf => ∃ hpf psf,
      ci.toNat ≤ 2 * stb.core.cur_vars ∧
      hpf.length = 2 * c.max_vars ∧ psf.length = 2 * c.max_vars ∧
      (FullMem c
        ({ stb with scratch :=
          { stb.scratch with tarjan_mark := hpf, tarjan_reach := psf } } : FullState) ⋆
        R) mf)
    (fun (ci, ()) _ => 2 * stb.core.cur_vars - ci.toNat)
    (fun J4 hJ4 => by
      c0_hfast
      exact hJ4 (0#64, ()) mb ⟨stb.scratch.tarjan_mark, stb.scratch.tarjan_reach,
        Nat.zero_le _, hbl.scratch_ok.tarjan_mark_len, hbl.scratch_ok.tarjan_reach_len, hmb⟩)
    (fun J4 (ci, ()) mf ⟨hpf, psf, hci_le, hhpf_l, hpsf_l, hmf⟩ ih4 => ?_)
  c0_hfast_nogrp
  · have hci_lt : ci.toNat < 2 * stb.core.cur_vars := by
      have h1 := hc
      have hmod : stb.core.cur_vars % 2 ^ 64 = stb.core.cur_vars := Nat.mod_eq_of_lt (by omega)
      simp only [hmod, Nat.mod_eq_of_lt hb_lt64] at h1; exact h1
    have h1 : ci.toNat < hpf.length := by omega
    have h2 : ci.toNat < psf.length := by omega
    have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := fac_bv64_add1 (by omega)
    c0_hfast
    exact ih4 (ci + 1#64, ()) _ (by dsimp only; rw [hci1]; omega)
      ⟨hpf.set ci.toNat 0#32, psf.set ci.toNat 0#32, by rw [hci1]; omega,
        by simpa using hhpf_l, by simpa using hpsf_l, by assumption⟩
  · have hinv_f : FullDenseInv c F0
        { stb with scratch :=
          { stb.scratch with tarjan_mark := hpf, tarjan_reach := psf } } :=
      fullDenseInv_set_fheap hinvb hhpf_l hpsf_l
    clear ih4 hc hci_le
    let stf : FullState :=
      { stb with scratch :=
        { stb.scratch with tarjan_mark := hpf, tarjan_reach := psf } }
    have hstf_cv : stf.core.cur_vars = stb.core.cur_vars := rfl
    have hstf_cv_lt64 : stf.core.cur_vars < 2 ^ 64 := by omega
    have hfl := hinv_f.1.lengths
    c0_hfast_nogrp
    refine wp_join0
      (fun mq => ∃ stq : FullState,
        FullDenseInv c F0 stq ∧ stq.core.cur_vars = stb.core.cur_vars ∧
        stq.core.fuel = stb.core.fuel ∧ (FullMem c stq ⋆ R) mq)
      (fun _ mq ⟨stq, hinvq, hcvq, hfuq, hmq⟩ => by
        c0_hfast
        exact hQ 1#64 stq mq hinvq (by rw [hcvq]; exact hcvb) (hfuq.trans hfub) rfl hmq)
      (fun Jv hJv => ?_)
    c0_hfast_nogrp
    · refine wp_loop_inv
        (fun (qidx, qst, ()) mq => ∃ qs' : List (BitVec 32),
          qst.toNat ≤ stf.core.cur_vars ∧ qs'.length = c.max_vars ∧
          (FullMem c
            ({ stf with scratch := { stf.scratch with q_stamp := qs' } } : FullState) ⋆
            R) mq)
        (fun (_, qst, ()) _ => stf.core.cur_vars - qst.toNat)
        (fun J9 hJ9 => by
          c0_hfast
          exact hJ9 (stf.scratch.q_first, 0#64, ()) mf ⟨stf.scratch.q_stamp,
            Nat.zero_le _, hfl.scratch_ok.q_stamp_len, hmf⟩)
        (fun J9 (qidx, qst, ()) mq ⟨qs', hqst_le, hqs'_l, hmq⟩ ih9 => ?_)
      c0_hfast
      · have hmod64 : stb.core.cur_vars % 2 ^ 64 = stb.core.cur_vars :=
          Nat.mod_eq_of_lt (by omega)
        have hqi_lt : qidx.toNat < stf.core.cur_vars := by
          have h1 : qidx.toNat < stb.core.cur_vars % 2 ^ 64 := by assumption
          rw [hmod64] at h1; exact h1
        have hqs_lt : qst.toNat < stf.core.cur_vars := by
          have h1 := hc
          rw [hmod64] at h1; exact h1
        have h1 : qidx.toNat < qs'.length := by rw [hqs'_l]; omega
        have h2 : qidx.toNat < stf.scratch.q_next.length := by
          rw [hfl.scratch_ok.q_next_len]; omega
        have hqst1 : (qst + 1#64).toNat = qst.toNat + 1 := fac_bv64_add1 (by omega)
        c0_hfast_nogrp
        exact ih9 (BitVec.setWidth 64 (stf.scratch.q_next[qidx.toNat]'h2),
          qst + 1#64, ()) _ (by dsimp only; rw [hqst1]; omega)
          ⟨qs'.set qidx.toNat (BitVec.setWidth 32 (qst + 1#64)),
            by rw [hqst1]; omega, by simpa using hqs'_l, by assumption⟩
      all_goals
        clear ih9
        c0_hfast_nogrp
        first
        | (have hqsi_lt : stf.scratch.q_search_idx.toNat < qs'.length := by
             have hmod64 : stb.core.cur_vars % 2 ^ 64 = stb.core.cur_vars :=
               Nat.mod_eq_of_lt (by omega)
             have h1 : stf.scratch.q_search_idx.toNat < stb.core.cur_vars % 2 ^ 64 :=
               by assumption
             rw [hmod64] at h1; rw [hqs'_l]; omega
           c0_hfast
           exact hJv _ ⟨_, fullDenseInv_set_qstamp hinv_f hqs'_l, rfl, rfl,
             by assumption⟩)
        | (c0_hfast
           exact hJv _ ⟨_, fullDenseInv_set_qstamp hinv_f hqs'_l, rfl, rfl,
             by assumption⟩)
    · exact hJv _ ⟨stf, hinv_f, rfl, rfl, hmf⟩

namespace FidFast
open Lean Meta Elab Tactic C0HeadStep

private meta partial def fidSepClauses (e : Lean.Expr) : List Lean.Expr :=
  let e := e.consumeMData
  if e.isAppOf ``Std.ExtHashMap.sep && e.getAppNumArgs ≥ 2 then
    fidSepClauses (e.getArg! (e.getAppNumArgs - 2)) ++
      fidSepClauses (e.getArg! (e.getAppNumArgs - 1))
  else [e]

private meta def fidFootprints : TacticM (Array Name) := withMainContext do
  let mut keys : Array Name := #[]
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if t.isAppOf ``Std.ExtHashMap.sep && t.getAppNumArgs ≥ 3 then
      for c in fidSepClauses t.appFn! do
        if let some k := c.getAppFn.consumeMData.constName? then
          unless keys.contains k do keys := keys.push k
  return keys

private meta def fidTryMemFast (g : MVarId) (nm : Name) : TacticM Bool := do
  let s ← saveState
  let gs ← try withReducible <| g.apply (← mkConstWithFreshMVarLevels nm)
    catch _ => s.restore; return false
  for g' in gs do
    let ty ← instantiateMVars (← g'.getType)
    if ty.isAppOf ``Std.ExtHashMap.sep then
      let ok ← try withReducible g'.assumption; pure true catch _ => pure false
      unless ok do
        let s2 ← saveState
        let ok2 ← try
          setGoals [g']; evalTactic (← `(tactic| c0_frame))
          pure (← getUnsolvedGoals).isEmpty
        catch _ => pure false
        unless ok2 do s2.restore; s.restore; return false
  for g' in gs do
    if ← g'.isAssigned then continue
    if ← isProp (← g'.getType) then
      let ok ← try g'.assumption; pure true
        catch _ => try g'.refl; pure true catch _ => pure false
      unless ok do s.restore; return false
  for g' in gs do
    unless ← g'.isAssigned do s.restore; return false
  return true

private meta def fidMemFast (isLoad : Bool) (g : MVarId) (addr : Lean.Expr) : TacticM Bool := do
  setGoals [g]
  let keys ← fidFootprints
  let env ← getEnv
  let mut tried : NameSet := {}
  for k in keys do
    for nm in C0Step.c0MemLemmasForAddr env isLoad k addr do
      if tried.contains nm then continue
      tried := tried.insert nm
      if ← fidTryMemFast g nm then return true
  for k in keys do
    for nm in C0Step.c0MemLemmas env isLoad k do
      if tried.contains nm then continue
      tried := tried.insert nm
      if ← fidTryMemFast g nm then return true
  return false

private meta def fidStepOnceFast (cfg : HeadStepConfig) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isAppOfArity ``LeanQbe.T.wp 6 then
    let wpArgs := ty.getAppArgs
    let e0 := (peelBlocksGet wpArgs[4]!).consumeMData.headBeta
    let e ← if e0.isAppOf ``LeanQbe.T.Expr.let_ || e0.isAppOf ``LeanQbe.T.Expr.load ||
               e0.isAppOf ``LeanQbe.T.Expr.store || e0.isAppOf ``LeanQbe.T.Expr.jnz ||
               e0.isAppOf ``LeanQbe.T.Expr.jump || e0.isAppOf ``LeanQbe.T.Expr.ret ||
               e0.isAppOf ``LeanQbe.T.Expr.exit || e0.isAppOf ``LeanQbe.T.Expr.group ||
               e0.isAppOf ``LeanQbe.T.Expr.call
             then pure e0 else (peelBlocksGet <$> whnfCore e0)
    if e.isAppOf ``LeanQbe.T.Expr.load && e.getAppNumArgs == 6 then
      let t := e.getArg! 3; let a := e.getArg! 4; let k := e.getArg! 5
      let addr := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val)
        (Lean.mkConst ``LeanQbe.T.i64) a)
      let vMVar ← mkFreshExprMVar (some (Lean.mkApp (Lean.mkConst ``LeanQbe.T.Val) t))
      let s ← saveState
      try
        let lemInfo ← getConstInfo ``head_wp_load
        let pfx : Array Lean.Expr := #[wpArgs[0]!, wpArgs[1]!, wpArgs[2]!, wpArgs[3]!,
          wpArgs[5]!, t, a, addr, k, vMVar,
          Lean.mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero])
            (Lean.mkApp (Lean.mkConst ``BitVec) (Lean.mkNatLit 64)) addr]
        let .forallE _ sTy body1 _ ← instantiateForall lemInfo.type pfx
          | s.restore; return false
        let hl ← mkFreshExprSyntheticOpaqueMVar sTy
        let .forallE _ hkTy _ _ := body1.instantiate1 hl | s.restore; return false
        let hk ← mkFreshExprSyntheticOpaqueMVar hkTy
        g.assign (Lean.mkAppN (Lean.mkConst ``head_wp_load) ((pfx.push hl).push hk))
        if ← fidMemFast true hl.mvarId! addr then setGoals [hk.mvarId!]; return true
        s.restore; return false
      catch _ => s.restore; return false
    if e.isAppOf ``LeanQbe.T.Expr.store && e.getAppNumArgs == 7 then
      let t := e.getArg! 3; let v := e.getArg! 4; let a := e.getArg! 5; let k := e.getArg! 6
      let val := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val) t v)
      let addr := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val)
        (Lean.mkConst ``LeanQbe.T.i64) a)
      let memTy ← inferType wpArgs[5]!
      let memPredTy := Lean.Expr.forallE `m memTy (.sort Level.zero) .default
      let pMVar ← mkFreshExprMVar (some memPredTy)
      let rMVar ← mkFreshExprMVar (some memPredTy)
      let s ← saveState
      try
        let lemInfo ← getConstInfo ``head_wp_store
        let pfx : Array Lean.Expr := #[wpArgs[0]!, wpArgs[1]!, wpArgs[2]!, wpArgs[3]!,
          wpArgs[5]!, t, v, a, val, addr, k, pMVar, rMVar,
          Lean.mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero])
            (Lean.mkApp (Lean.mkConst ``LeanQbe.T.Val) t) val,
          Lean.mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero])
            (Lean.mkApp (Lean.mkConst ``BitVec) (Lean.mkNatLit 64)) addr]
        let .forallE _ sTy body1 _ ← instantiateForall lemInfo.type pfx
          | s.restore; return false
        let hs ← mkFreshExprSyntheticOpaqueMVar sTy
        let .forallE _ hkTy _ _ := body1.instantiate1 hs | s.restore; return false
        let hk ← mkFreshExprSyntheticOpaqueMVar hkTy
        g.assign (Lean.mkAppN (Lean.mkConst ``head_wp_store) ((pfx.push hs).push hk))
        if ← fidMemFast false hs.mvarId! addr then
          let (_, hk') ← hk.mvarId!.intro `m
          let (_, hk'') ← hk'.intro `hm
          setGoals [hk'']
          let hIdent := mkIdent `hm
          evalTactic (← `(tactic| try simp only [Std.ExtHashMap.sep_emp] at $hIdent:ident))
          let .fvar mId := wpArgs[5]! | return true
          for d in (← getLCtx).decls.toArray.reverse do
            let some d := d | continue
            let dt ← instantiateMVars d.type
            if dt.isAppOf ``Std.ExtHashMap.sep && dt.appArg! == wpArgs[5]! then
              try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
          try liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()
          return true
        s.restore; return false
      catch _ => s.restore; return false
  match ← headStepOnceRes cfg with
  | .progressed => return true
  | _ => return false

private meta partial def fidHeadSteps (cfg : HeadStepConfig) (fuel : Nat := 10000) :
    TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    if ← fidStepOnceFast cfg then
      fidHeadSteps cfg (fuel - 1)
      out := out ++ (← getUnsolvedGoals)
    else
      let ty0 ← instantiateMVars (← g.getType)
      let ty := ty0.consumeMData.headBeta
      if ty.isAppOfArity ``LeanQbe.T.wp 6 then
        let e := ty.getArg! 4
        let e' := peelBlocksGet (← whnfCore (peelBlocksGet e))
        let g' ← if e' != e || ty != ty0 then
          g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e')) (checkDefEq := false)
        else pure g
        out := out.push g'
      else out := out.push g
  setGoals out.toList

end FidFast

local elab "fid_hfast" : tactic => FidFast.fidHeadSteps { pruneJnz := false } 10000
local elab "fid_hfast_nogrp" : tactic =>
  FidFast.fidHeadSteps { unrollGroup := false, pruneJnz := false } 10000

/-! ## 2. `full_factor_fid_wp` (`FullBvaHeap.fullFactorHeapSpec`) -/

/-- Parametric `Func.wp` proof for `full_factor_body` against canonical
`FullBvaHeap.fullFactorHeapSpec` (`GAP-BVA-01/02/03`). -/
theorem full_factor_fid_wp (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hConnect : ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
      Γ "full_bva_connect_clauses_fid" [i64] [] a m Q X)
    (hCountDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    (hTryLit : ∀ a m Q X, fidBvaTryLitSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Func.wp Γ full_factor_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hinv0, hm0, hQ⟩
  have hmaxv := c.hmaxv
  have hmax_lt32 : c.max_vars < 2 ^ 29 := by
    change c.max_vars < 2 * 268435456 at hmaxv; omega
  have hmax_lt64 : 2 * c.max_vars < 2 ^ 64 := by omega
  unfold Func.wp full_factor_body
  c0_hfast_nogrp
  refine fid_wp_call_steps_cap hSteps ?_
  c0_hfast
  · exact hQ 1#64 s0 m0 hinv0 (Nat.le_refl _) rfl rfl hm0
  · exact hQ 1#64 s0 m0 hinv0 (Nat.le_refl _) rfl rfl hm0
  · exact hQ 1#64 s0 m0 hinv0 (Nat.le_refl _) rfl rfl hm0
  · obtain ⟨F_cur0, hdw0⟩ := hinv0.exists_witness
    fid_call hConnect
    refine ⟨c, F0, F_cur0, s0, R, rfl, hdw0, hm0, fun s1 m1 hdw1 hcv1 hfu1 _ _ _ hm1 => ?_⟩
    have hinv1 : FullDenseInv c F0 s1 := hdw1.toDense
    c0_hfast_nogrp
    · exact hQ 1#64 s1 m1 hinv1 (Nat.le_of_eq hcv1.symm) hfu1 rfl hm1
    · let s1a : FullState := { s1 with scratch := { s1.scratch with ant_sz := budget } }
      have hinv1a : FullDenseInv c F0 s1a := fullDenseInv_set_ant hinv1 budget
      have h1al := hinv1a.1.lengths
      have hcv1a_le := h1al.core_ok.cur_vars_le
      have hcv1a_lt32 : 2 * s1a.core.cur_vars < 2 ^ 32 := by omega
      have hcv1a_lt64 : 2 * s1a.core.cur_vars < 2 ^ 64 := by omega
      have hmnl_eq : (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat = 2 * c.max_vars := by
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one]
        rw [Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
          Nat.mul_comm, Nat.mod_eq_of_lt hmax_lt64]
      c0_hfast_nogrp
      -- Loop 1: zero `tmark`/`fheap` and set `fpos = 0xFFFFFFFF` over `[0 .. 2*max_vars)`
      refine wp_loop_inv
        (fun (zi, ()) mz => ∃ wsi hpi psi,
          zi.toNat ≤ 2 * c.max_vars ∧
          wsi.length = 2 * c.max_vars ∧ hpi.length = 2 * c.max_vars ∧
          psi.length = 2 * c.max_vars ∧
          (FullMem c (setWtpFid s1a wsi hpi psi) ⋆ R) mz)
        (fun (zi, ()) _ => 2 * c.max_vars - zi.toNat)
        (fun Lz hLz => by
          c0_hfast
          exact hLz (0#64, ()) _ ⟨_, _, _, Nat.zero_le _, h1al.scratch_ok.wsort_len,
            h1al.scratch_ok.tarjan_mark_len, h1al.scratch_ok.tarjan_reach_len, by assumption⟩)
        (fun Lz (zi, ()) mz ⟨wsi, hpi, psi, hzi_le, hwsi_l, hhpi_l, hpsi_l, hmz⟩ ihz => ?_)
      dsimp only [setWtpFid] at hmz
      c0_hfast_nogrp
      · have hzi_lt : zi.toNat < 2 * c.max_vars := by
          have h1 := hc
          have hmod : c.max_vars % 2 ^ 64 = c.max_vars := Nat.mod_eq_of_lt (by omega)
          simp only [hmod, Nat.mod_eq_of_lt hmax_lt64] at h1; exact h1
        have h1 : zi.toNat < wsi.length := by omega
        have h2 : zi.toNat < hpi.length := by omega
        have h3 : zi.toNat < psi.length := by omega
        have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := fac_bv64_add1 (by omega)
        c0_hfast
        exact ihz (zi + 1#64, ()) _ (by dsimp only; rw [hzi1]; omega)
          ⟨wsi.set zi.toNat 0#32, hpi.set zi.toNat 0#32, psi.set zi.toNat 0xFFFFFFFF#32,
            by rw [hzi1]; omega, by simpa using hwsi_l, by simpa using hhpi_l,
            by simpa using hpsi_l, by assumption⟩
      · have hstz_inv : FullDenseInv c F0 (setWtpFid s1a wsi hpi psi) :=
          hinv1a.of_safetySlice
            ⟨h1al.core_ok,
              { h1al.scratch_ok with
                  wsort_len := hwsi_l, tarjan_mark_len := hhpi_l, tarjan_reach_len := hpsi_l }⟩
            rfl ⟨rfl, rfl⟩
        clear ihz hc hzi_le
        -- Loop 2: push active unassigned literals (`FL_FACT_P/N` & `deg > 1`) into `fheap`
        refine wp_loop_inv
          (fun (hsz, vi, ()) mv => ∃ st1 : FullState,
            vi.toNat ≤ s1a.core.cur_vars ∧ hsz.toNat ≤ 2 * vi.toNat ∧
            FullDenseInv c F0 st1 ∧ st1.core.cur_vars = s1a.core.cur_vars ∧
            st1.core.fuel = s1a.core.fuel ∧
            (∀ k < hsz.toNat,
              (st1.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * s1a.core.cur_vars) ∧
            (FullMem c st1 ⋆ R) mv)
          (fun (_, vi, ()) _ => s1a.core.cur_vars - vi.toNat)
          (fun J1 hJ1 => by
            c0_hfast
            exact hJ1 (0#32, 0#64, ()) mz ⟨setWtpFid s1a wsi hpi psi, Nat.zero_le _, Nat.zero_le _,
              hstz_inv, rfl, rfl, fun _ hk => by simp at hk, hmz⟩)
          (fun J1 (hsz, vi, ()) mv ⟨st1, hvi_le, hhl_le, hinv_1, hcv_1, hfu_1, hhp1, hmv⟩ ih1 => ?_)
        c0_hfast
        · have hvi_lt : vi.toNat < s1a.core.cur_vars := by
            have hcmp : vi.toNat < s1.core.cur_vars % 2 ^ 64 := hc
            have h1cv : s1.core.cur_vars = s1a.core.cur_vars := rfl
            rw [Nat.mod_eq_of_lt (by omega)] at hcmp; exact hcmp
          have hvi1 : (vi + 1#64).toNat = vi.toNat + 1 := fac_bv64_add1 (by omega)
          have hhl1 : (hsz + 1#32).toNat = hsz.toNat + 1 := fac_bv32_add1 (by omega)
          have hhl2 : (hsz + 1#32 + 1#32).toNat = hsz.toNat + 2 := by
            rw [fac_bv32_add1 (by rw [hhl1]; omega), hhl1]
          have h1l := hinv_1.1.lengths
          have hfl_lt : vi.toNat < st1.core.flags.length := by rw [h1l.core_ok.flags_len]; omega
          have hvl_lt : (vi.toNat * 2 ^ 1) % 2 ^ 64 < st1.core.vals.length := by
            rw [h1l.core_ok.vals_len, Nat.mod_eq_of_lt (by omega)]; omega
          have hpl_deg_lt : (2 * vi.toNat) % 2 ^ 64 < st1.core.repr.length := by
            rw [h1l.core_ok.repr_len, Nat.mod_eq_of_lt (by omega)]; omega
          have hnl_deg_lt :
              (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                st1.core.repr.length := by
            rw [fac_nl_64 hvi_lt hcv1a_lt32, h1l.core_ok.repr_len]; omega
          c0_hfast
          · -- Push P (`2 * vi`) then check N (`2 * vi + 1`)
            have hhl_lt : hsz.toNat < 2 * s1a.core.cur_vars := by omega
            have hhp_p_lt : hsz.toNat < st1.scratch.tarjan_mark.length := by
              rw [h1l.scratch_ok.tarjan_mark_len]; omega
            have hps_p_lt : (2 * vi.toNat) % 2 ^ 64 < st1.scratch.tarjan_reach.length := by
              rw [h1l.scratch_ok.tarjan_reach_len, Nat.mod_eq_of_lt (by omega)]; omega
            c0_hfast
            let st_p0 : FullState :=
              { st1 with scratch :=
                { st1.scratch with
                  tarjan_mark := st1.scratch.tarjan_mark.set (BitVec.setWidth 64 hsz).toNat
                    (BitVec.setWidth 32 (vi <<< (1 : Nat)))
                  tarjan_reach := st1.scratch.tarjan_reach.set
                    (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)))).toNat hsz } }
            have hinv_p0 : FullDenseInv c F0 st_p0 :=
              fullDenseInv_set_fheap hinv_1
                (by simp [h1l.scratch_ok.tarjan_mark_len])
                (by simp [h1l.scratch_ok.tarjan_reach_len])
            refine fid_wp_call_fheap_up hUp hinv_p0 hmaxv (hlen_chk := hsz.toNat + 1)
              (Nat.lt_succ_self _) (by dsimp [st_p0]; omega) ?_ (by assumption)
              fun st_p m' hinv_p hcore_p _ hhp_p hm' => ?_
            · intro k hk; dsimp only [st_p0]; rw [fid_bv64_32, hcv_1]
              exact fheap_push_pre_lt_bv (by rw [fac_pl_bv32_toNat hvi_lt hcv1a_lt32]; omega)
                hhp_p_lt hhp1 k (Nat.lt_succ_iff.mp hk)
            · have hcv_p : st_p.core.cur_vars = s1a.core.cur_vars :=
                (congrArg (·.cur_vars) hcore_p).trans hcv_1
              have hfu_p : st_p.core.fuel = s1a.core.fuel :=
                (congrArg (·.fuel) hcore_p).trans hfu_1
              have hhp_p' : ∀ k < (hsz + 1#32).toNat,
                  (st_p.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * s1a.core.cur_vars := by
                intro k hk; rw [hhl1] at hk
                have h := hhp_p k hk
                dsimp only [st_p0] at h; rw [hcv_1] at h; exact h
              have hpl_p := hinv_p.1.lengths
              have hflp_lt : vi.toNat < st_p.core.flags.length := by
                rw [hpl_p.core_ok.flags_len]; omega
              have hnld_p_lt :
                  (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                    st_p.core.repr.length := by
                rw [fac_nl_64 hvi_lt hcv1a_lt32, hpl_p.core_ok.repr_len]; omega
              c0_hfast
              · have hphl_lt : (hsz + 1#32).toNat < 2 * s1a.core.cur_vars := by rw [hhl1]; omega
                have hhp_np_lt : (hsz + 1#32).toNat < st_p.scratch.tarjan_mark.length := by
                  rw [hpl_p.scratch_ok.tarjan_mark_len]; omega
                have hps_np_lt :
                    (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                      st_p.scratch.tarjan_reach.length := by
                  rw [fac_nl_64 hvi_lt hcv1a_lt32, hpl_p.scratch_ok.tarjan_reach_len]; omega
                c0_hfast
                let st_pn0 : FullState :=
                  { st_p with scratch :=
                    { st_p.scratch with
                      tarjan_mark := st_p.scratch.tarjan_mark.set
                        (BitVec.setWidth 64 (hsz + 1#32)).toNat
                        (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)
                      tarjan_reach := st_p.scratch.tarjan_reach.set
                        (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat
                        (hsz + 1#32) } }
                have hinv_pn0 : FullDenseInv c F0 st_pn0 :=
                  fullDenseInv_set_fheap hinv_p
                    (by simp [hpl_p.scratch_ok.tarjan_mark_len])
                    (by simp [hpl_p.scratch_ok.tarjan_reach_len])
                refine fid_wp_call_fheap_up hUp hinv_pn0 hmaxv (hlen_chk := (hsz + 1#32).toNat + 1)
                  (Nat.lt_succ_self _) (by dsimp [st_pn0]; rw [hcv_p]; omega) ?_ (by assumption)
                  fun st_pn m2 hinv_pn hcore_pn _ hhp_pn hm2 => ?_
                · intro k hk; dsimp only [st_pn0]; rw [fid_bv64_32, hcv_p]
                  exact fheap_push_pre_lt_bv (by rw [fac_nl_bv32_toNat hvi_lt hcv1a_lt32]; omega)
                    hhp_np_lt hhp_p' k (Nat.lt_succ_iff.mp hk)
                · c0_hfast
                  refine ih1 (hsz + 1#32 + 1#32, vi + 1#64, ()) m2
                    (by dsimp only; rw [hvi1]; omega)
                    ⟨st_pn, by rw [hvi1]; omega, by rw [hhl2, hvi1]; omega, hinv_pn,
                      (congrArg (·.cur_vars) hcore_pn).trans hcv_p,
                      (congrArg (·.fuel) hcore_pn).trans hfu_p, ?_, hm2⟩
                  intro k hk; rw [hhl2] at hk
                  have h := hhp_pn k (by rw [hhl1]; omega)
                  dsimp only [st_pn0] at h; rw [hcv_p] at h; exact h
              · exact ih1 (hsz + 1#32, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
                  ⟨st_p, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_p, hcv_p, hfu_p,
                    hhp_p', by assumption⟩
              · exact ih1 (hsz + 1#32, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
                  ⟨st_p, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_p, hcv_p, hfu_p,
                    hhp_p', by assumption⟩
          · -- P skipped (`deg[pl] <= 1`), push N (`2 * vi + 1`)
            have hhl_lt : hsz.toNat < 2 * s1a.core.cur_vars := by omega
            have hhp_n_lt : hsz.toNat < st1.scratch.tarjan_mark.length := by
              rw [h1l.scratch_ok.tarjan_mark_len]; omega
            have hhp_n_lt64 : (BitVec.setWidth 64 hsz).toNat < st1.scratch.tarjan_mark.length := by
              rw [fid_bv64_32]; exact hhp_n_lt
            have hps_n_lt :
                (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                  st1.scratch.tarjan_reach.length := by
              rw [fac_nl_64 hvi_lt hcv1a_lt32, h1l.scratch_ok.tarjan_reach_len]; omega
            c0_hfast_nogrp
            let st_n0 : FullState :=
              { st1 with scratch :=
                { st1.scratch with
                  tarjan_mark := st1.scratch.tarjan_mark.set (BitVec.setWidth 64 hsz).toNat
                    (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)
                  tarjan_reach := st1.scratch.tarjan_reach.set
                    (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat
                    hsz } }
            have hinv_n0 : FullDenseInv c F0 st_n0 :=
              fullDenseInv_set_fheap hinv_1
                (by simp [h1l.scratch_ok.tarjan_mark_len])
                (by simp [h1l.scratch_ok.tarjan_reach_len])
            refine fid_wp_call_fheap_up hUp hinv_n0 hmaxv (hlen_chk := hsz.toNat + 1)
              (Nat.lt_succ_self _) (by dsimp [st_n0]; omega) ?_ (by assumption)
              fun st_n m' hinv_n hcore_n _ hhp_n hm' => ?_
            · intro k hk; dsimp only [st_n0]; rw [fid_bv64_32, hcv_1]
              exact fheap_push_pre_lt_bv (by rw [fac_nl_bv32_toNat hvi_lt hcv1a_lt32]; omega)
                hhp_n_lt hhp1 k (Nat.lt_succ_iff.mp hk)
            · c0_hfast
              refine ih1 (hsz + 1#32, vi + 1#64, ()) m' (by dsimp only; rw [hvi1]; omega)
                ⟨st_n, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_n,
                  (congrArg (·.cur_vars) hcore_n).trans hcv_1,
                  (congrArg (·.fuel) hcore_n).trans hfu_1, ?_, hm'⟩
              intro k hk; rw [hhl1] at hk
              have h := hhp_n k hk; dsimp only [st_n0] at h; rw [hcv_1] at h; exact h
          · exact ih1 (hsz, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
              ⟨st1, by rw [hvi1]; omega, by rw [hvi1]; omega, hinv_1, hcv_1, hfu_1, hhp1,
                by assumption⟩
          · exact ih1 (hsz, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
              ⟨st1, by rw [hvi1]; omega, by rw [hvi1]; omega, hinv_1, hcv_1, hfu_1, hhp1,
                by assumption⟩
          · -- P skipped (`FL_FACT_P == 0`), push N (`2 * vi + 1`)
            have hhl_lt : hsz.toNat < 2 * s1a.core.cur_vars := by omega
            have hhp_n_lt : hsz.toNat < st1.scratch.tarjan_mark.length := by
              rw [h1l.scratch_ok.tarjan_mark_len]; omega
            have hhp_n_lt64 : (BitVec.setWidth 64 hsz).toNat < st1.scratch.tarjan_mark.length := by
              rw [fid_bv64_32]; exact hhp_n_lt
            have hps_n_lt :
                (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                  st1.scratch.tarjan_reach.length := by
              rw [fac_nl_64 hvi_lt hcv1a_lt32, h1l.scratch_ok.tarjan_reach_len]; omega
            c0_hfast_nogrp
            let st_n0 : FullState :=
              { st1 with scratch :=
                { st1.scratch with
                  tarjan_mark := st1.scratch.tarjan_mark.set (BitVec.setWidth 64 hsz).toNat
                    (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)
                  tarjan_reach := st1.scratch.tarjan_reach.set
                    (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat
                    hsz } }
            have hinv_n0 : FullDenseInv c F0 st_n0 :=
              fullDenseInv_set_fheap hinv_1
                (by simp [h1l.scratch_ok.tarjan_mark_len])
                (by simp [h1l.scratch_ok.tarjan_reach_len])
            refine fid_wp_call_fheap_up hUp hinv_n0 hmaxv (hlen_chk := hsz.toNat + 1)
              (Nat.lt_succ_self _) (by dsimp [st_n0]; omega) ?_ (by assumption)
              fun st_n m' hinv_n hcore_n _ hhp_n hm' => ?_
            · intro k hk; dsimp only [st_n0]; rw [fid_bv64_32, hcv_1]
              exact fheap_push_pre_lt_bv (by rw [fac_nl_bv32_toNat hvi_lt hcv1a_lt32]; omega)
                hhp_n_lt hhp1 k (Nat.lt_succ_iff.mp hk)
            · c0_hfast
              refine ih1 (hsz + 1#32, vi + 1#64, ()) m' (by dsimp only; rw [hvi1]; omega)
                ⟨st_n, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_n,
                  (congrArg (·.cur_vars) hcore_n).trans hcv_1,
                  (congrArg (·.fuel) hcore_n).trans hfu_1, ?_, hm'⟩
              intro k hk; rw [hhl1] at hk
              have h := hhp_n k hk; dsimp only [st_n0] at h; rw [hcv_1] at h; exact h
          all_goals
            exact ih1 (hsz, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
              ⟨st1, by rw [hvi1]; omega, by rw [hvi1]; omega, hinv_1, hcv_1, hfu_1, hhp1,
                by assumption⟩
        · -- Exit Loop 2 -> Loop 3: main factor heap loop
          clear ih1 hc hvi_le hmz hstz_inv hwsi_l hhpi_l hpsi_l
          fid_hfast_nogrp
          refine wp_while_state
            (α := BitVec 32 × FullState)
            (fun (chsz, _) => (chsz, ()))
            (fun (chsz, stp) => (c.max_vars - stp.core.cur_vars) * (2 * c.max_vars + 1) +
              chsz.toNat)
            (fun (chsz, stp) mp => FullDenseInv c F0 stp ∧
              s0.core.cur_vars ≤ stp.core.cur_vars ∧ stp.core.fuel = s0.core.fuel ∧
              chsz.toNat ≤ 2 * stp.core.cur_vars ∧
              (∀ k < chsz.toNat,
                (stp.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * stp.core.cur_vars) ∧
              (FullMem c stp ⋆ R) mp)
            (fun J3 hJ3 => by
              fid_hfast
              exact hJ3 (hsz, st1) mv ⟨hinv_1, by rw [hcv_1]; exact Nat.le_of_eq hcv1.symm,
                hfu_1.trans hfu1, by rw [hcv_1]; omega,
                fun k hk => by rw [hcv_1]; exact hhp1 k hk, hmv⟩)
            (fun J3 (chsz, stp) mp ⟨hinvp, hcvp, hfup, hhlp, hhpp, hmp⟩ ih3 => ?_)
          dsimp only [Blocks.get]
          -- Exit join of Loop 3 -> Loop 4 (clear `fheap`/`fpos`) -> VMTF renumber -> `return 1`
          refine wp_join0
            (fun mb => ∃ stb : FullState,
              FullDenseInv c F0 stb ∧ s0.core.cur_vars ≤ stb.core.cur_vars ∧
              stb.core.fuel = s0.core.fuel ∧ (FullMem c stb ⋆ R) mb)
            (fun _ mb ⟨stb, hinvb, hcvb, hfub, hmb⟩ => by
              clear ih3 hinvp hcvp hfup hhlp hhpp hmp
              fid_hfast_nogrp
              refine factor_loop4_vmtf_wp hinvb (by rw [← hcv1] at hcvb; exact hcvb) hfub hmb
                (fun r s' m' h1 h2 h3 h4 h5 => ?_)
              have hcv_s' : s0.core.cur_vars ≤ s'.core.cur_vars := by rw [← hcv1]; exact h2
              exact hQ r s' m' h1 hcv_s' h3 h4 h5)
            (fun J3x hJ3x => by
              fid_hfast
              · -- Loop 3 body: pop `f0 = fheap[0]`
                have hpl := hinvp.1.lengths
                have hcvp_le := hpl.core_ok.cur_vars_le
                have hchsz_pos : 0 < chsz.toNat := by
                  simpa using (by assumption : BitVec.toNat 0 < chsz.toNat)
                have hchsz1 : (chsz - 1#32).toNat = chsz.toNat - 1 := fac_bv32_sub1 hchsz_pos
                have h0_lt_hp : 0 < stp.scratch.tarjan_mark.length := by
                  rw [hpl.scratch_ok.tarjan_mark_len]; omega
                have hhp0_lt :
                    (BitVec.ofNat 64 0).toNat < stp.scratch.tarjan_mark.length := h0_lt_hp
                obtain ⟨f0, hf0_def⟩ :
                    ∃ f0 : BitVec 32,
                      f0 = stp.scratch.tarjan_mark[(BitVec.ofNat 64 0).toNat]'hhp0_lt := ⟨_, rfl⟩
                have hf0_lt : f0.toNat < 2 * stp.core.cur_vars := by
                  have h1 := hhpp 0 hchsz_pos
                  rw [List.getElem?_eq_getElem h0_lt_hp, Option.getD_some] at h1
                  simpa [BitVec.toNat_ofNat, hf0_def] using h1
                have hf0_lt_ps :
                    (BitVec.setWidth 64
                      (stp.scratch.tarjan_mark[(BitVec.ofNat 64 0).toNat]'hhp0_lt)).toNat <
                      stp.scratch.tarjan_reach.length := by
                  rw [fid_bv64_32, ← hf0_def, hpl.scratch_ok.tarjan_reach_len]; omega
                fid_hfast_nogrp
                rw [← hf0_def]
                have hf064_nat : (BitVec.setWidth 64 f0).toNat = f0.toNat := fid_bv64_32 f0
                let stp0 : FullState :=
                  { stp with scratch :=
                    { stp.scratch with
                      tarjan_reach := stp.scratch.tarjan_reach.set f0.toNat 0xFFFFFFFF#32 } }
                have hinv_p0 : FullDenseInv c F0 stp0 :=
                  fullDenseInv_set_fheap hinvp hpl.scratch_ok.tarjan_mark_len
                    (by simp [hpl.scratch_ok.tarjan_reach_len])
                -- Join after `if (hsz > 0)` pop-sift
                refine wp_join0
                  (fun mp1 => ∃ stp1 : FullState, FullDenseInv c F0 stp1 ∧
                    stp1.core.cur_vars = stp.core.cur_vars ∧ stp1.core.fuel = stp.core.fuel ∧
                    (∀ k < (chsz - 1#32).toNat,
                      (stp1.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * stp.core.cur_vars) ∧
                    (FullMem c stp1 ⋆ R) mp1)
                  (fun _ mp1 ⟨stp1, hinvp1, hcvp1, hfup1, hhpp1, hmp1⟩ => by
                    have hp1l := hinvp1.1.lengths
                    refine wp_join_state1 (t := i32) (α := BitVec 32) id
                      (fun fbit mp2 => (fbit = 32#32 ∨ fbit = 64#32) ∧ (FullMem c stp1 ⋆ R) mp2)
                      (fun _ fbit mp2 ⟨_, hmp2⟩ => by
                        have hskip : ∀ st_sk m_sk,
                            FullDenseInv c F0 st_sk →
                            st_sk.core.cur_vars = stp.core.cur_vars →
                            st_sk.core.fuel = stp.core.fuel →
                            (∀ k < (chsz - 1#32).toNat,
                              (st_sk.scratch.tarjan_mark[k]?.getD 0#32).toNat <
                                2 * stp.core.cur_vars) →
                            (FullMem c st_sk ⋆ R) m_sk →
                            J3 (chsz - 1#32, ()) m_sk :=
                          fun st_sk m_sk hik hck hfk hhpk hmk =>
                          ih3 (chsz - 1#32, st_sk) m_sk
                            (fac_lex_dec_hsz (by omega) (by rw [hchsz1]; omega))
                            ⟨hik, by omega, hfk.trans hfup, by rw [hck, hchsz1]; omega,
                              fun k hk => by rw [hck]; exact hhpk k hk, hmk⟩
                        have hf0_fl_lt :
                            (BitVec.setWidth 64 (f0 >>> (1 : Nat))).toNat <
                              stp1.core.flags.length :=
                          fac_fl_lit_lt hf0_lt (by rw [hp1l.core_ok.flags_len]; omega)
                        have hf0_fl_lt_bv :
                            (BitVec.setWidth 64 (f0 >>> (1 : BitVec 32))).toNat <
                              stp1.core.flags.length :=
                          fac_fl_lit_lt_bv hf0_lt (by rw [hp1l.core_ok.flags_len]; omega)
                        have hf0_vl_lt : f0.toNat < stp1.core.vals.length := by
                          rw [hp1l.core_ok.vals_len]; omega
                        fid_hfast
                        · exact hskip stp1 _ hinvp1 hcvp1 hfup1 hhpp1 (by assumption)
                        · exact hskip stp1 _ hinvp1 hcvp1 hfup1 hhpp1 (by assumption)
                        · exact hskip stp1 _ hinvp1 hcvp1 hfup1 hhpp1 (by assumption)
                        · let stp2 : FullState :=
                            { stp1 with core :=
                              { stp1.core with
                                flags := stp1.core.flags.set
                                  (BitVec.setWidth 64 (f0 >>> (1 : BitVec 32))).toNat
                                  ((stp1.core.flags[(BitVec.setWidth 64
                                    (f0 >>> (1 : BitVec 32))).toNat]'hf0_fl_lt_bv) &&& ~~~fbit) } }
                          have hinv_p2 : FullDenseInv c F0 stp2 :=
                            fullDenseInv_set_flags hinvp1
                              (by simp [hp1l.core_ok.flags_len])
                          have hcv_p2 : stp2.core.cur_vars = stp.core.cur_vars := hcvp1
                          have hfu_p2 : stp2.core.fuel = stp.core.fuel := hfup1
                          have hp2l := hinv_p2.1.lengths
                          have hf0_deg_lt : f0.toNat < stp2.core.repr.length := by
                            rw [hp2l.core_ok.repr_len]; omega
                          fid_hfast
                          · exact hskip stp2 _ hinv_p2 hcv_p2 hfu_p2 hhpp1 (by assumption)
                          · -- Call `full_bva_try_lit(h, f0, init_cv)`
                            fid_call hTryLit
                            refine ⟨c, F0, stp2, R, rfl, hinv_p2, by dsimp [stp2]; omega,
                              by assumption,
                              fun ok st3 m3 hinv3 hcv3_le hcv3_gt hfu3 htm3 _ hm3 => ?_⟩
                            have h3l := hinv3.1.lengths
                            have hcv3_max := h3l.core_ok.cur_vars_le
                            refine wp_jnz_bool ok rfl (fun hok => ?_) (fun _ => ?_)
                            · -- `ok = true`: strict `cur_vars` growth (`stp < st3`)
                              have hcv_strict : stp.core.cur_vars < st3.core.cur_vars := by
                                rw [← hcv_p2]; exact hcv3_gt hok
                              have hcv3_shl :
                                  (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat =
                                    2 * st3.core.cur_vars := by
                                simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                                  Nat.shiftLeft_eq, Nat.pow_one]
                                rw [Nat.mod_eq_of_lt (by omega : st3.core.cur_vars < 2 ^ 64),
                                  Nat.mul_comm,
                                  Nat.mod_eq_of_lt (by omega : 2 * st3.core.cur_vars < 2 ^ 64)]
                              fid_hfast_nogrp
                              refine wp_join_state1 (t := i64) (α := BitVec 64) id
                                (fun n2 m2 => n2.toNat ≤ 2 * st3.core.cur_vars ∧
                                  (FullMem c st3 ⋆ R) m2)
                                (fun _ n2 m2 ⟨hn2_le, hm2⟩ => by
                                  dsimp only [Blocks.get, id]
                                  -- Sub-loop 3a: recompute `deg[tl]` (`repr`) for `di < n2`
                                  refine wp_loop_inv
                                    (fun (di, ()) md => ∃ std : FullState,
                                      di.toNat ≤ n2.toNat ∧ FullDenseInv c F0 std ∧
                                      std.core.cur_vars = st3.core.cur_vars ∧
                                      std.core.fuel = st3.core.fuel ∧
                                      std.scratch.tarjan_mark = st3.scratch.tarjan_mark ∧
                                      (FullMem c std ⋆ R) md)
                                    (fun (di, ()) _ => n2.toNat - di.toNat)
                                    (fun Ld hLd => by
                                      fid_hfast
                                      exact hLd (0#64, ()) m2
                                        ⟨st3, Nat.zero_le _, hinv3, rfl, rfl, rfl, hm2⟩)
                                    (fun Ld (di, ()) md ⟨std, hdi_le, hinvd, hcvd, hfud, htmd,
                                      hmd⟩ ihd => ?_)
                                  have hdl := hinvd.1.lengths
                                  fid_hfast_nogrp
                                  · have hdi_lt : di.toNat < n2.toNat := by exact hc
                                    have hdi1 : (di + 1#64).toNat = di.toNat + 1 :=
                                      fac_bv64_add1 (by omega)
                                    have hdi_ws2 : di.toNat < std.scratch.work_stk2.length := by
                                      rw [hdl.scratch_ok.work_stk2_len]; omega
                                    fid_hfast_nogrp
                                    refine wp_join_group (ts := [])
                                      (fun _ md' => ∃ std' : FullState,
                                        FullDenseInv c F0 std' ∧
                                        std'.core.cur_vars = st3.core.cur_vars ∧
                                        std'.core.fuel = st3.core.fuel ∧
                                        std'.scratch.tarjan_mark = st3.scratch.tarjan_mark ∧
                                        (FullMem c std' ⋆ R) md')
                                      (fun _ _ md' ⟨std', h1, h2, h3, h4, h5⟩ => by
                                        fid_hfast
                                        exact ihd (di + 1#64, ()) md' (by dsimp only; omega)
                                          ⟨std', by omega, h1, h2, h3, h4, h5⟩)
                                      (fun Jd hJd => ?_)
                                    fid_hfast_nogrp
                                    · have htl_lt :
                                          (std.scratch.work_stk2[di.toNat]'hdi_ws2).toNat <
                                            2 * std.core.cur_vars := by
                                        have hmod : st3.core.cur_vars % 2 ^ 64 =
                                            st3.core.cur_vars :=
                                          Nat.mod_eq_of_lt (by omega)
                                        have h1 := hc
                                        simp only [hmod,
                                          Nat.mod_eq_of_lt
                                            (by omega : 2 * st3.core.cur_vars < 2 ^ 64)]
                                          at h1
                                        rw [hcvd]; exact h1
                                      obtain ⟨F_d, hdwd⟩ := hinvd.exists_witness
                                      fid_call hCountDeg
                                      refine ⟨c, F0, F_d, std, R, rfl, hdwd, htl_lt, hmd,
                                        fun degv => ?_⟩
                                      have htl_rp :
                                          (BitVec.setWidth 64
                                            (std.scratch.work_stk2[di.toNat]'hdi_ws2)).toNat <
                                            std.core.repr.length := by
                                        rw [fid_bv64_32, hdl.core_ok.repr_len]; omega
                                      fid_hfast
                                      exact hJd () _
                                        ⟨{ std with core :=
                                            { std.core with
                                              repr := std.core.repr.set
                                                (BitVec.setWidth 64
                                                  (std.scratch.work_stk2[di.toNat]'hdi_ws2)).toNat
                                                degv } },
                                          fullDenseInv_set_repr hinvd
                                            (by simp [hdl.core_ok.repr_len]),
                                          hcvd, hfud, htmd, by assumption⟩
                                    · exact hJd () md ⟨std, hinvd, hcvd, hfud, htmd, hmd⟩
                                  · -- Sub-loop 3b: sift/pop/push touched literals `tj < n2`
                                    clear ihd hc hdi_le
                                    fid_hfast_nogrp
                                    refine wp_loop_inv (ts := [i32, i64])
                                      (fun (thsz, tj, ()) mt => ∃ stt : FullState,
                                        FullDenseInv c F0 stt ∧
                                        stt.core.cur_vars = st3.core.cur_vars ∧
                                        stt.core.fuel = st3.core.fuel ∧
                                        thsz.toNat ≤ 2 * st3.core.cur_vars ∧
                                        (∀ k < thsz.toNat,
                                          (stt.scratch.tarjan_mark[k]?.getD 0#32).toNat <
                                            2 * st3.core.cur_vars) ∧
                                        (FullMem c stt ⋆ R) mt)
                                      (fun (_, tj, ()) _ => n2.toNat - tj.toNat)
                                      (fun Lt hLt => by
                                        fid_hfast
                                        exact hLt (chsz - 1#32, 0#64, ()) md
                                          ⟨std, hinvd, hcvd, hfud, by rw [hchsz1]; omega,
                                            fun k hk => by
                                              rw [htmd, htm3]; dsimp only [stp2]
                                              exact Nat.lt_trans (hhpp1 k hk) (by omega), hmd⟩)
                                      (fun Lt (thsz, tj, ()) mt
                                        ⟨stt, hinvt, hcvt, hfut, hthl_le, hthp, hmt⟩ iht => ?_)
                                    fid_hfast_nogrp
                                    · have htj_lt : tj.toNat < n2.toNat := by exact hc
                                      have htj1 : (tj + 1#64).toNat = tj.toNat + 1 :=
                                        fac_bv64_add1 (by omega)
                                      have htl := hinvt.1.lengths
                                      have htj_ws2 : tj.toNat < stt.scratch.work_stk2.length := by
                                        rw [htl.scratch_ok.work_stk2_len]; omega
                                      let tl : BitVec 32 := stt.scratch.work_stk2[tj.toNat]'htj_ws2
                                      let L3bInv : BitVec 32 → Mem 64 → Prop := fun th' mt' =>
                                        ∃ stt' : FullState,
                                          FullDenseInv c F0 stt' ∧
                                          stt'.core.cur_vars = st3.core.cur_vars ∧
                                          stt'.core.fuel = st3.core.fuel ∧
                                          th'.toNat ≤ 2 * st3.core.cur_vars ∧
                                          (∀ k < th'.toNat,
                                            (stt'.scratch.tarjan_mark[k]?.getD 0#32).toNat <
                                              2 * st3.core.cur_vars) ∧
                                          (FullMem c stt' ⋆ R) mt'
                                      have hstt_skip : ∀ mt',
                                          (FullMem c stt ⋆ R) mt' → L3bInv thsz mt' :=
                                        fun mt' hm' => ⟨stt, hinvt, hcvt, hfut, hthl_le, hthp, hm'⟩
                                      fid_hfast_nogrp
                                      refine wp_join_state1 (t := i32) (α := BitVec 32) id L3bInv
                                        (fun _ th' mt' h => by
                                          dsimp only [Blocks.get, id]; fid_hfast
                                          exact iht (th', tj + 1#64, ()) mt'
                                            (by dsimp only; omega) h)
                                        (fun Jt hJt => ?_)
                                      fid_hfast_nogrp
                                      · have htl_lt : tl.toNat < 2 * st3.core.cur_vars := by
                                          have hmod : st3.core.cur_vars % 2 ^ 64 =
                                            st3.core.cur_vars :=
                                            Nat.mod_eq_of_lt (by omega)
                                          have h1 := hc
                                          simp only [hmod,
                                            Nat.mod_eq_of_lt
                                              (by omega : 2 * st3.core.cur_vars < 2 ^ 64)] at h1
                                          exact h1
                                        have htl_lt_t : tl.toNat < 2 * stt.core.cur_vars := by
                                          rw [hcvt]; exact htl_lt
                                        have htl_rc :
                                            (BitVec.setWidth 64 tl).toNat <
                                              stt.scratch.tarjan_reach.length := by
                                          rw [fid_bv64_32, htl.scratch_ok.tarjan_reach_len]; omega
                                        have htl_rp :
                                            (BitVec.setWidth 64 tl).toNat <
                                              stt.core.repr.length := by
                                          rw [fid_bv64_32, htl.core_ok.repr_len]; omega
                                        fid_hfast_nogrp
                                        refine wp_join_state1 (t := i32) (α := BitVec 32) id L3bInv
                                          (fun _ th' mt' h => hJt th' mt' h)
                                          (fun Jp hJp => ?_)
                                        fid_hfast_nogrp
                                        · -- `p = fpos[tl] < thsz`: pop (`deg[tl] <= 1`) or sift
                                          let pv : BitVec 32 :=
                                            stt.scratch.tarjan_reach[(BitVec.setWidth 64
                                              tl).toNat]'htl_rc
                                          have hpv_lt : pv.toNat < thsz.toNat := by exact hc
                                          refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                            L3bInv (fun _ th' mt' h => by
                                              fid_hfast; exact hJp th' mt' h)
                                            (fun Jp1 hJp1 => ?_)
                                          fid_hfast_nogrp
                                          · -- `deg[tl] <= 1`: pop `pv` from heap
                                            have hth_pos : 0 < thsz.toNat := by omega
                                            have hth1 : (thsz - 1#32).toNat = thsz.toNat - 1 :=
                                              fac_bv32_sub1 hth_pos
                                            have hth1_mk :
                                                (BitVec.setWidth 64 (thsz - 1#32)).toNat <
                                                  stt.scratch.tarjan_mark.length := by
                                              rw [fid_bv64_32, htl.scratch_ok.tarjan_mark_len]
                                              omega
                                            let last := stt.scratch.tarjan_mark[(BitVec.setWidth 64
                                              (thsz - 1#32)).toNat]'hth1_mk
                                            have hlast_lt : last.toNat < 2 * st3.core.cur_vars := by
                                              have h1 := hthp (thsz - 1#32).toNat
                                                (by rw [hth1]; omega)
                                              rw [List.getElem?_eq_getElem (by
                                                rw [htl.scratch_ok.tarjan_mark_len]; omega),
                                                Option.getD_some] at h1
                                              simpa only [last, fid_bv64_32] using h1
                                            have hlast_rc :
                                                (BitVec.setWidth 64 last).toNat <
                                                  stt.scratch.tarjan_reach.length := by
                                              rw [fid_bv64_32, htl.scratch_ok.tarjan_reach_len]
                                              omega
                                            fid_hfast_nogrp
                                            let st_pop0 : FullState :=
                                              { stt with scratch :=
                                                { stt.scratch with
                                                  tarjan_reach := stt.scratch.tarjan_reach.set
                                                    (BitVec.setWidth 64 last).toNat
                                                    0xFFFFFFFF#32 } }
                                            have hinv_pop0 : FullDenseInv c F0 st_pop0 :=
                                              fullDenseInv_set_fheap hinvt
                                                htl.scratch_ok.tarjan_mark_len
                                                (by simp [htl.scratch_ok.tarjan_reach_len])
                                            refine wp_join0 (L3bInv (thsz - 1#32))
                                              (fun _ mp' h => by
                                                fid_hfast; exact hJp1 (thsz - 1#32) mp' h)
                                              (fun Jpop hJpop => ?_)
                                            fid_hfast_nogrp
                                            · have hpv_lt1 : pv.toNat < (thsz - 1#32).toNat := by
                                                exact hc
                                              have hpv_mk :
                                                  (BitVec.setWidth 64 pv).toNat <
                                                    st_pop0.scratch.tarjan_mark.length := by
                                                rw [fid_bv64_32, htl.scratch_ok.tarjan_mark_len]
                                                omega
                                              have htl_rc1 :
                                                  (BitVec.setWidth 64 tl).toNat <
                                                    st_pop0.scratch.tarjan_reach.length := by
                                                dsimp [st_pop0]; rw [List.length_set]; exact htl_rc
                                              have hlast_rc2 :
                                                  (BitVec.setWidth 64 last).toNat <
                                                    (st_pop0.scratch.tarjan_reach.set
                                                      (BitVec.setWidth 64 tl).toNat
                                                      0xFFFFFFFF#32).length := by
                                                rw [List.length_set]; dsimp [st_pop0]
                                                rw [List.length_set]; exact hlast_rc
                                              fid_hfast_nogrp
                                              let st_pop1 : FullState :=
                                                { st_pop0 with scratch :=
                                                  { st_pop0.scratch with
                                                    tarjan_mark := st_pop0.scratch.tarjan_mark.set
                                                      (BitVec.setWidth 64 pv).toNat last
                                                    tarjan_reach :=
                                                      (st_pop0.scratch.tarjan_reach.set
                                                        (BitVec.setWidth 64 tl).toNat
                                                        0xFFFFFFFF#32).set
                                                        (BitVec.setWidth 64 last).toNat pv } }
                                              have hinv_pop1 : FullDenseInv c F0 st_pop1 :=
                                                fullDenseInv_set_fheap hinv_pop0
                                                  (by simp [st_pop0,
                                                    htl.scratch_ok.tarjan_mark_len])
                                                  (by simp [st_pop0,
                                                    htl.scratch_ok.tarjan_reach_len])
                                              refine fid_wp_call_fheap_up hUp hinv_pop1 hmaxv
                                                (hlen_chk := (thsz - 1#32).toNat) hpv_lt1
                                                (by
                                                  have hcvp1 :
                                                      st_pop1.core.cur_vars = stt.core.cur_vars :=
                                                    rfl
                                                  rw [hcvp1, hcvt, hth1]; omega)
                                                ?_ (by assumption)
                                                fun st_pu m_pu hinv_pu hcore_pu _ hhp_pu
                                                  hm_pu => ?_
                                              · intro i hi; dsimp only [st_pop1, st_pop0]
                                                rw [hcvt, fid_bv64_32]
                                                by_cases hip : i = pv.toNat
                                                · subst hip
                                                  rw [List.getElem?_set_self (by
                                                    rw [htl.scratch_ok.tarjan_mark_len]; omega),
                                                    Option.getD_some]
                                                  exact hlast_lt
                                                · rw [List.getElem?_set_ne (Ne.symm hip)]
                                                  exact hthp i (by rw [hth1] at hi; omega)
                                              · have hcv_pu :
                                                    st_pu.core.cur_vars = st3.core.cur_vars :=
                                                  (congrArg (·.cur_vars) hcore_pu).trans hcvt
                                                have hfu_pu : st_pu.core.fuel = st3.core.fuel :=
                                                  (congrArg (·.fuel) hcore_pu).trans hfut
                                                have hpul := hinv_pu.1.lengths
                                                have hlast_rc_pu :
                                                    (BitVec.setWidth 64 last).toNat <
                                                      st_pu.scratch.tarjan_reach.length := by
                                                  rw [fid_bv64_32, hpul.scratch_ok.tarjan_reach_len]
                                                  omega
                                                fid_hfast_nogrp
                                                refine wp_join0 (L3bInv (thsz - 1#32))
                                                  (fun _ mp' h => hJpop mp' h)
                                                  (fun Jpd hJpd => ?_)
                                                fid_hfast_nogrp
                                                · have hlp_lt :
                                                      (st_pu.scratch.tarjan_reach[(BitVec.setWidth
                                                        64 last).toNat]'hlast_rc_pu).toNat <
                                                        (thsz - 1#32).toNat := by exact hc
                                                  refine fid_wp_call_fheap_down hDown hinv_pu hmaxv
                                                    hlp_lt
                                                    (by
                                                      change (thsz - 1#32).toNat ≤
                                                        2 * st_pu.core.cur_vars
                                                      rw [hcv_pu, hth1]; omega)
                                                    (fun i hi => by
                                                      rw [hcv_pu, ← hcvt]; exact hhp_pu i hi)
                                                    hm_pu
                                                    fun st_pd m_pd hinv_pd hcore_pd _ hhp_pd
                                                      hm_pd => ?_
                                                  exact hJpd m_pd ⟨st_pd, hinv_pd,
                                                    (congrArg (·.cur_vars) hcore_pd).trans hcv_pu,
                                                    (congrArg (·.fuel) hcore_pd).trans hfu_pu,
                                                    by
                                                      change (thsz - 1#32).toNat ≤
                                                        2 * st3.core.cur_vars
                                                      rw [hth1]; omega,
                                                    fun k hk => by
                                                      rw [← hcv_pu]; exact hhp_pd k hk, hm_pd⟩
                                                · exact hJpd m_pu ⟨st_pu, hinv_pu, hcv_pu, hfu_pu,
                                                    by
                                                      change (thsz - 1#32).toNat ≤
                                                        2 * st3.core.cur_vars
                                                      rw [hth1]; omega,
                                                    fun k hk => by rw [← hcvt]; exact hhp_pu k hk,
                                                    hm_pu⟩
                                            · exact hJpop _ ⟨st_pop0, hinv_pop0, hcvt, hfut,
                                                by rw [hth1]; omega,
                                                fun k hk => hthp k (by rw [hth1] at hk; omega),
                                                by assumption⟩
                                          · -- `deg[tl] > 1`: sift up then down
                                            refine fid_wp_call_fheap_up hUp hinvt hmaxv hpv_lt
                                              (by rw [hcvt]; exact hthl_le)
                                              (fun i hi => by rw [hcvt]; exact hthp i hi) hmt
                                              fun st_u1 m_u1 hinv_u1 hcore_u1 _ hhp_u1 hm_u1 => ?_
                                            have hcv_u1 : st_u1.core.cur_vars = st3.core.cur_vars :=
                                              (congrArg (·.cur_vars) hcore_u1).trans hcvt
                                            have hfu_u1 : st_u1.core.fuel = st3.core.fuel :=
                                              (congrArg (·.fuel) hcore_u1).trans hfut
                                            have hu1l := hinv_u1.1.lengths
                                            have htl_rc_u1 :
                                                (BitVec.setWidth 64 tl).toNat <
                                                  st_u1.scratch.tarjan_reach.length := by
                                              rw [fid_bv64_32, hu1l.scratch_ok.tarjan_reach_len]
                                              omega
                                            fid_hfast_nogrp
                                            refine wp_join0 (L3bInv thsz)
                                              (fun _ mu2 h => by fid_hfast; exact hJp1 thsz mu2 h)
                                              (fun Jd2 hJd2 => ?_)
                                            fid_hfast_nogrp
                                            · have hp2_lt :
                                                  (st_u1.scratch.tarjan_reach[(BitVec.setWidth 64
                                                    tl).toNat]'htl_rc_u1).toNat < thsz.toNat := by
                                                exact hc
                                              refine fid_wp_call_fheap_down hDown hinv_u1 hmaxv
                                                hp2_lt (by rw [hcv_u1]; exact hthl_le)
                                                (fun k hk => by
                                                  rw [hcv_u1, ← hcvt]; exact hhp_u1 k hk)
                                                hm_u1
                                                fun st_u2 m_u2 hinv_u2 hcore_u2 _ hhp_u2 hm_u2 => ?_
                                              exact hJd2 m_u2 ⟨st_u2, hinv_u2,
                                                (congrArg (·.cur_vars) hcore_u2).trans hcv_u1,
                                                (congrArg (·.fuel) hcore_u2).trans hfu_u1,
                                                hthl_le,
                                                fun k hk => by rw [← hcv_u1]; exact hhp_u2 k hk,
                                                hm_u2⟩
                                            · exact hJd2 m_u1 ⟨st_u1, hinv_u1, hcv_u1, hfu_u1,
                                                hthl_le,
                                                fun k hk => by rw [← hcvt]; exact hhp_u1 k hk,
                                                hm_u1⟩
                                        · -- `p >= thsz`: maybe push `tl` if `thsz < cur_nl`
                                          refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                            L3bInv (fun _ th' mt' h => hJp th' mt' h)
                                            (fun Je hJe => ?_)
                                          fid_hfast_nogrp
                                          · have hth_lt_cv :
                                                thsz.toNat < 2 * st3.core.cur_vars := by
                                              have hmod : st3.core.cur_vars % 2 ^ 64 =
                                                  st3.core.cur_vars :=
                                                Nat.mod_eq_of_lt (by omega)
                                              have h1 := hc
                                              simp only [hmod,
                                                Nat.mod_eq_of_lt
                                                  (by omega : 2 * st3.core.cur_vars < 2 ^ 64)]
                                                at h1
                                              exact h1
                                            refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                              (fun tbit mt1 =>
                                                (tbit = 32#32 ∨ tbit = 64#32) ∧
                                                  (FullMem c stt ⋆ R) mt1)
                                              (fun _ tbit mt1 ⟨_, hmt1⟩ => by
                                                dsimp only [Blocks.get, id]
                                                fid_hfast_nogrp
                                                refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                                  L3bInv (fun _ th' mt' h => hJe th' mt' h)
                                                  (fun Jb2 hJb2 => ?_)
                                                have htv_fl_lt :
                                                    (BitVec.setWidth 64
                                                      (tl >>> (1 : BitVec 32))).toNat <
                                                      stt.core.flags.length :=
                                                  fac_fl_lit_lt_bv htl_lt_t
                                                    (by rw [htl.core_ok.flags_len]
                                                        exact htl.core_ok.cur_vars_le)
                                                have hvl_tl_lt :
                                                    (BitVec.setWidth 64 tl).toNat <
                                                      stt.core.vals.length := by
                                                  rw [fid_bv64_32, htl.core_ok.vals_len]; omega
                                                have hthl_mk_lt :
                                                    (BitVec.setWidth 64 thsz).toNat <
                                                      stt.scratch.tarjan_mark.length := by
                                                  rw [fid_bv64_32, htl.scratch_ok.tarjan_mark_len]
                                                  omega
                                                have hth_add1 :
                                                    (thsz + 1#32).toNat = thsz.toNat + 1 :=
                                                  fac_bv32_add1 (by omega)
                                                fid_hfast_nogrp
                                                all_goals
                                                  try exact hJb2 thsz mt1 (hstt_skip mt1 hmt1)
                                                fid_hfast_nogrp
                                                all_goals
                                                  try exact hJb2 thsz mt1 (hstt_skip mt1 hmt1)
                                                fid_hfast_nogrp
                                                all_goals
                                                  try exact hJb2 thsz mt1 (hstt_skip mt1 hmt1)
                                                let st_push : FullState :=
                                                  { stt with scratch :=
                                                    { stt.scratch with
                                                      tarjan_mark := stt.scratch.tarjan_mark.set
                                                        (BitVec.setWidth 64 thsz).toNat tl
                                                      tarjan_reach := stt.scratch.tarjan_reach.set
                                                        (BitVec.setWidth 64 tl).toNat thsz } }
                                                have hinv_push : FullDenseInv c F0 st_push :=
                                                  fullDenseInv_set_fheap hinvt
                                                    (by simp [htl.scratch_ok.tarjan_mark_len])
                                                    (by simp [htl.scratch_ok.tarjan_reach_len])
                                                refine fid_wp_call_fheap_up hUp hinv_push hmaxv
                                                  (hlen_chk := thsz.toNat + 1) (Nat.lt_succ_self _)
                                                  (by dsimp [st_push]; rw [hcvt]; omega) ?_
                                                  (by assumption)
                                                  fun st_u2 m_u2 hinv_u2 hcore_u2 _ hhp_u2
                                                    hm_u2 => ?_
                                                · intro k hk; dsimp only [st_push]
                                                  rw [fid_bv64_32, hcvt]
                                                  exact fheap_push_pre_lt_bv htl_lt
                                                    (by rw [htl.scratch_ok.tarjan_mark_len]; omega)
                                                    hthp k (Nat.lt_succ_iff.mp hk)
                                                · fid_hfast_nogrp
                                                  exact hJb2 (thsz + 1#32) m_u2
                                                    ⟨st_u2, hinv_u2,
                                                      (congrArg (·.cur_vars) hcore_u2).trans hcvt,
                                                      (congrArg (·.fuel) hcore_u2).trans hfut,
                                                      by rw [hth_add1]; omega,
                                                      fun k hk => by
                                                        rw [hth_add1] at hk
                                                        have h := hhp_u2 k hk
                                                        dsimp only [st_push] at h
                                                        rw [hcvt] at h; exact h,
                                                      hm_u2⟩)
                                              (fun Jtb hJtb => by
                                                fid_hfast_nogrp
                                                · exact hJtb 64#32 mt ⟨Or.inr rfl, hmt⟩
                                                · exact hJtb 32#32 mt ⟨Or.inl rfl, hmt⟩)
                                          · exact hJe thsz mt (hstt_skip mt hmt)
                                      · exact hJt thsz mt (hstt_skip mt hmt)
                                    · -- Exit Sub-loop 3b -> back-edge of Loop 3 (`cur_vars` grew!)
                                      fid_hfast_nogrp
                                      exact ih3 (thsz, stt) mt
                                        (fac_lex_dec_cv (by rw [hcvt]; exact hcv_strict)
                                          (by rw [hcvt]; exact hcv3_max) (by omega))
                                        ⟨hinvt, by rw [hcvt]; omega,
                                          hfut.trans (hfu3.trans (hfu_p2.trans hfup)),
                                          by rw [hcvt]; exact hthl_le,
                                          fun k hk => by rw [hcvt]; exact hthp k hk, hmt⟩)
                                (fun J15 hJ15 => by
                                  fid_hfast_nogrp
                                  · exact hJ15 (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)) m3
                                      ⟨by rw [hcv3_shl]; exact Nat.le_refl _, hm3⟩
                                  · exact hJ15 st3.scratch.res_sz m3 ⟨by
                                      have hmod1 : st3.core.cur_vars % 2 ^ 64 = st3.core.cur_vars :=
                                        Nat.mod_eq_of_lt (by omega)
                                      have hmod2 :
                                          2 * st3.core.cur_vars % 2 ^ 64 = 2 * st3.core.cur_vars :=
                                        Nat.mod_eq_of_lt (by omega)
                                      have hnlt :
                                          ¬2 * st3.core.cur_vars < st3.scratch.res_sz.toNat := by
                                        have h1 := hc
                                        simp only [hmod1, hmod2] at h1
                                        exact h1
                                      omega, hm3⟩)
                            · -- `ok = false`: `hsz` decremented, `cur_vars` non-decreasing
                              fid_hfast_nogrp
                              exact ih3 (chsz - 1#32, st3) m3
                                (fac_lex_dec_hsz (by rw [← hcv_p2]; exact hcv3_le)
                                  (by rw [hchsz1]; omega))
                                ⟨hinv3, by omega, hfu3.trans (hfu_p2.trans hfup),
                                  by rw [hchsz1]; omega,
                                  fun k hk => by
                                    rw [htm3]; dsimp only [stp2]
                                    exact Nat.lt_of_lt_of_le (hhpp1 k hk) (by rw [← hcv_p2]; omega),
                                  hm3⟩
                        all_goals exact hskip stp1 _ hinvp1 hcvp1 hfup1 hhpp1 (by assumption))
                      (fun Jbit hJbit => by
                        fid_hfast_nogrp
                        · exact hJbit 64#32 mp1 ⟨Or.inr rfl, hmp1⟩
                        · exact hJbit 32#32 mp1 ⟨Or.inl rfl, hmp1⟩))
                  (fun Jd hJd => by
                    fid_hfast_nogrp
                    · have hhsz1_pos : 0 < (chsz - 1#32).toNat := by simpa using hc
                      have hhsz1_eq64 :
                          (BitVec.setWidth 64 (chsz - 1#32)).toNat = (chsz - 1#32).toNat :=
                        fid_bv64_32 _
                      have hhsz1_lt64 :
                          (BitVec.setWidth 64 (chsz - 1#32)).toNat <
                            stp0.scratch.tarjan_mark.length := by
                        rw [hhsz1_eq64, hpl.scratch_ok.tarjan_mark_len]; omega
                      obtain ⟨last, hlast_def⟩ :
                          ∃ last : BitVec 32,
                            last = stp.scratch.tarjan_mark[(BitVec.setWidth 64
                              (chsz - 1#32)).toNat]'hhsz1_lt64 := ⟨_, rfl⟩
                      have hlast_lt : last.toNat < 2 * stp.core.cur_vars := by
                        have h1 := hhpp (chsz - 1#32).toNat (by rw [hchsz1]; omega)
                        rw [List.getElem?_eq_getElem (by
                          rw [hpl.scratch_ok.tarjan_mark_len]; omega), Option.getD_some] at h1
                        simpa only [hlast_def, hhsz1_eq64] using h1
                      have hlast64_nat : (BitVec.setWidth 64 last).toNat = last.toNat :=
                        fid_bv64_32 last
                      have hlast_lt_ps :
                          (BitVec.setWidth 64
                            (stp.scratch.tarjan_mark[(BitVec.setWidth 64
                              (chsz - 1#32)).toNat]'hhsz1_lt64)).toNat <
                            stp0.scratch.tarjan_reach.length := by
                        dsimp only [stp0]
                        rw [List.length_set, hpl.scratch_ok.tarjan_reach_len, ← hlast_def,
                          hlast64_nat]
                        omega
                      c0_hfast_nogrp
                      dsimp only
                      rw [List.getElem_set_self (by rw [List.length_set]; exact hhp0_lt)]
                      have hlast_def1 :
                          stp.scratch.tarjan_mark[(BitVec.setWidth 64 (chsz - 1)).toNat]'
                            hhsz1_lt64 = last := hlast_def.symm
                      rw [hlast_def1]
                      let st_m0 : FullState :=
                        { stp0 with scratch :=
                          { stp0.scratch with tarjan_mark := stp0.scratch.tarjan_mark.set 0 last } }
                      have hz64 : (BitVec.ofNat 64 0).toNat = 0 := rfl
                      replace hm : (FullMem c st_m0 ⋆ R) m := by
                        dsimp only [st_m0, stp0]
                        rw [← hf064_nat, hf0_def]
                        simp only [hlast_def1, hz64] at hm ⊢
                        exact hm
                      have hlast_lt_ps_bv :
                          (BitVec.setWidth 64 last).toNat < st_m0.scratch.tarjan_reach.length := by
                        dsimp only [st_m0, stp0]
                        rw [List.length_set, hpl.scratch_ok.tarjan_reach_len, hlast64_nat]; omega
                      c0_hfast_nogrp
                      let st_d0 : FullState :=
                        { stp0 with scratch :=
                          { stp0.scratch with
                            tarjan_mark := stp0.scratch.tarjan_mark.set 0 last
                            tarjan_reach := stp0.scratch.tarjan_reach.set last.toNat 0#32 } }
                      have hm_d0_eq : (FullMem c st_d0 ⋆ R) m := by
                        dsimp only [st_d0, st_m0]; rw [← hlast64_nat]; exact hm
                      have hinv_d0 : FullDenseInv c F0 st_d0 :=
                        fullDenseInv_set_fheap hinv_p0
                          (by simp [stp0, hpl.scratch_ok.tarjan_mark_len])
                          (by simp [stp0, hpl.scratch_ok.tarjan_reach_len])
                      refine fid_wp_call_fheap_down hDown hinv_d0 hmaxv
                        (by simpa using hhsz1_pos)
                        (by change (chsz - 1#32).toNat ≤ 2 * stp.core.cur_vars
                            rw [hchsz1]; omega)
                        ?_ hm_d0_eq fun st_d1 m_d1 hinv_d hcore_d _ hhp_d hm_d1 => ?_
                      · intro i hi; dsimp [st_d0, stp0]
                        by_cases hi0 : i = 0
                        · subst hi0; rw [List.getElem?_set_self h0_lt_hp, Option.getD_some]
                          exact hlast_lt
                        · rw [List.getElem?_set_ne (Ne.symm hi0)]
                          exact hhpp i
                            (by rw [show (chsz - 1 : BitVec 32) = chsz - 1#32 from rfl,
                                  hchsz1] at hi; omega)
                      · exact hJd m_d1 ⟨st_d1, hinv_d, congrArg (·.cur_vars) hcore_d,
                          congrArg (·.fuel) hcore_d, hhp_d, hm_d1⟩
                    · refine hJd m ⟨stp0, hinv_p0, rfl, rfl, fun k hk => ?_, ?_⟩
                      · exact hhpp k (by rw [hchsz1] at hk; omega)
                      · dsimp only [stp0]; rw [← hf064_nat, hf0_def]
                        simp only [BitVec.toNat_ofNat] at hm ⊢; exact hm)
              · exact hJ3x mp ⟨stp, hinvp, hcvp, hfup, hmp⟩
              · exact hJ3x mp ⟨stp, hinvp, hcvp, hfup, hmp⟩
              · exact hJ3x mp ⟨stp, hinvp, hcvp, hfup, hmp⟩
              · exact hJ3x mp ⟨stp, hinvp, hcvp, hfup, hmp⟩)


end LeanQbe.T.Examples.Kissat.FullFidelityBva

end
