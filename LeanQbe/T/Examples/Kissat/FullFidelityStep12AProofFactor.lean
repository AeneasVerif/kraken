/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12A
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7BvaSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva4
public import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a0
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-12A Factor Proof (`FullFidelityStep12AProofFactor`)

Parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`, `XPost`-polymorphic) for `full_factor` (`P0-2`: deduplicates
touched literals per BVA commit via `lit_mark` and `work_stk2`, clears `lit_mark`, and calls
`full_bva_upd_lit_fid` at most once per unique touched literal, preserving
`FullBvaHeap.fullFactorHeapSpec`).
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12A

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullFidelityBva FullFidelityStep7 FullFidelityStep9
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Fheap & Core State Framing Helpers -/

private def S12aFheapRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆
   (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
    array (t := i32) c.pFrameDec s.core.frame_dec ⋆
    array (t := i32) c.pWvec s.core.wvec ⋆
    array (t := i32) c.pMinStk s.core.min_stk) ⋆
   FullCoreDynArrs c s.core) ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
   (array (t := i32) c.pWsort s.scratch.wsort ⋆
    array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
    array (t := i32) c.pWorkStk2 s.scratch.work_stk2) ⋆
   FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

private theorem s12a_focus_fheap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
      array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
      array (t := i32) c.pRepr s.core.repr ⋆ (S12aFheapRest c s ⋆ R)) m := by
  unfold S12aFheapRest
  unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs at hm
  exact sep_ac hm

private theorem s12a_unfocus_fheap {c : FullCfg} {s : FullState} {hp' ps' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTarjanMark hp' ⋆ array (t := i32) c.pTarjanReach ps' ⋆
      array (t := i32) c.pRepr s.core.repr ⋆ (S12aFheapRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆
      R) m := by
  unfold S12aFheapRest at hm
  unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs
  exact sep_ac hm

private theorem s12a_dense_set_fheap {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {hp' ps' : List (BitVec 32)}
    (hhp : hp'.length = 2 * c.max_vars) (hps : ps'.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } :=
  hinv.of_safetySlice
    ⟨hinv.1.lengths.core_ok,
      { hinv.1.lengths.scratch_ok with tarjan_mark_len := hhp, tarjan_reach_len := hps }⟩
    rfl ⟨rfl, rfl⟩

private theorem s12a_dense_set_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := hinv.1.witness
  let k' : FullCoreState := { s.core with flags := fl' }
  have hw' : FullWitnessInv c F0 F_cur k' :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨⟨{ hinv.1.lengths.core_ok with flags_len := hfl }, hinv.1.lengths.scratch_ok⟩,
    F_cur, hw'⟩, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩

private theorem s12a_dense_set_qstamp {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {qs' : List (BitVec 32)} (hqs : qs'.length = c.max_vars) :
    FullDenseInv c F0 { s with scratch := { s.scratch with q_stamp := qs' } } :=
  hinv.of_safetySlice
    ⟨hinv.1.lengths.core_ok, { hinv.1.lengths.scratch_ok with q_stamp_len := hqs }⟩
    rfl ⟨rfl, rfl⟩

private def s12aSetLmWs2 (s : FullState) (tmk : List (BitVec 8)) (tlits : List (BitVec 32)) :
    FullState :=
  { s with
    core := { s.core with lit_mark := tmk }
    scratch := { s.scratch with work_stk2 := tlits } }

private theorem s12a_dense_set_lm_ws2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {tmk : List (BitVec 8)} {tlits : List (BitVec 32)}
    (hlm : tmk.length = 2 * c.max_vars) (hws2 : tlits.length = 2 * c.max_vars)
    (hzero : ∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 = 0#8) :
    FullDenseInv c F0 (s12aSetLmWs2 s tmk tlits) := by
  obtain ⟨F_cur, hw⟩ := hinv.1.witness
  let s' := s12aSetLmWs2 s tmk tlits
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨⟨{ hinv.1.lengths.core_ok with lit_mark_len := hlm },
      { hinv.1.lengths.scratch_ok with work_stk2_len := hws2 }⟩, F_cur, hw'⟩,
    ⟨hinv.2.1.1, hzero⟩, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩

private def S12aHeapFr (s st : FullState) : Prop :=
  ∃ rp hp ps, st = { s with core := { s.core with repr := rp }
                            scratch := { s.scratch with tarjan_mark := hp, tarjan_reach := ps } }

private theorem s12aHeapFr_refl (s : FullState) : S12aHeapFr s s := ⟨_, _, _, rfl⟩

private theorem s12aHeapFr_set_repr {s st : FullState} (h : S12aHeapFr s st)
    (rp' : List (BitVec 32)) :
    S12aHeapFr s { st with core := { st.core with repr := rp' } } := by
  obtain ⟨_, hp, ps, rfl⟩ := h; exact ⟨rp', hp, ps, rfl⟩

private theorem s12aHeapFr_set_fheap {s st : FullState} (h : S12aHeapFr s st)
    (hp' ps' : List (BitVec 32)) :
    S12aHeapFr s
      { st with scratch := { st.scratch with tarjan_mark := hp', tarjan_reach := ps' } } := by
  obtain ⟨rp, _, _, rfl⟩ := h; exact ⟨rp, hp', ps', rfl⟩

private theorem s12aHeapFr_cur_vars {s st : FullState} (h : S12aHeapFr s st) :
    st.core.cur_vars = s.core.cur_vars := by
  obtain ⟨_, _, _, rfl⟩ := h; rfl

private theorem s12aHeapFr_fuel {s st : FullState} (h : S12aHeapFr s st) :
    st.core.fuel = s.core.fuel := by
  obtain ⟨_, _, _, rfl⟩ := h; rfl

private theorem s12aHeapFr_work_stk2 {s st : FullState} (h : S12aHeapFr s st) :
    st.scratch.work_stk2 = s.scratch.work_stk2 := by
  obtain ⟨_, _, _, rfl⟩ := h; rfl

private def S12aUpdInv (c : FullCfg) (F0 : CNF Nat) (s0 : FullState) (R : Mem 64 → Prop)
    (hsz : BitVec 32) (m : Mem 64) : Prop :=
  ∃ st, FullDenseInv c F0 st ∧ S12aHeapFr s0 st ∧ hsz.toNat ≤ 2 * s0.core.cur_vars ∧
    (∀ i < hsz.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
    (FullMem c st ⋆ R) m

/-! ## 2. Arithmetic, Callee & Touched-Literal Deduplication Helpers -/

private theorem fac12a_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fac12a_bv32_sub1 {x : BitVec 32} (h : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

private theorem fac12a_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fac12a_lex_dec_cv {maxv cv1 cv2 h1 h2 : Nat}
    (hcv_lt : cv1 < cv2) (hcv2_le : cv2 ≤ maxv) (hh2 : h2 ≤ 2 * maxv) :
    (maxv - cv2) * (2 * maxv + 1) + h2 < (maxv - cv1) * (2 * maxv + 1) + h1 := by
  have hsub : maxv - cv2 + 1 ≤ maxv - cv1 := by omega
  have hmul : (maxv - cv2 + 1) * (2 * maxv + 1) ≤ (maxv - cv1) * (2 * maxv + 1) :=
    Nat.mul_le_mul_right _ hsub
  rw [Nat.add_one_mul] at hmul
  omega

private theorem fac12a_lex_dec_hsz {maxv cv1 cv2 h1 h2 : Nat}
    (hcv_le : cv1 ≤ cv2) (hh_lt : h2 < h1) :
    (maxv - cv2) * (2 * maxv + 1) + h2 < (maxv - cv1) * (2 * maxv + 1) + h1 := by
  have hmul : (maxv - cv2) * (2 * maxv + 1) ≤ (maxv - cv1) * (2 * maxv + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

private theorem fac12a_push_pre_lt {hp : List (BitVec 32)} {hlen : Nat} {lit : BitVec 32}
    {lim : Nat} (hlt : lit.toNat < lim) (hhl_lt : hlen < hp.length)
    (hprev : ∀ k < hlen, (hp[k]?.getD 0#32).toNat < lim) :
    ∀ i ≤ hlen, ((hp.set hlen lit)[i]?.getD 0#32).toNat < lim := by
  intro i hi
  by_cases heq : i = hlen
  · subst heq; rw [List.getElem?_set_self hhl_lt, Option.getD_some]; exact hlt
  · rw [List.getElem?_set_ne (Ne.symm heq)]; exact hprev i (Nat.lt_of_le_of_ne hi heq)

private theorem s12a_call_steps_cap {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    {c : FullCfg} {m : Mem 64} {k : Tup Val [i32] → Expr Val Cont rs}
    (hk : ∀ scb : BitVec 32, scb.toNat = fidStepsCap c.scratch_cap →
      wp Γ Q X (k (scb, ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) "full_bva_steps_cap_fid"
      (Arg.var (BitVec.ofNat 64 c.scratch_cap), ()) k) m := by
  refine wp_call_of_spec _ _ (hSteps _ _ _ _ (hk _ ?_))
  have h1 := c.hscr; unfold dimacsBound at h1
  have h2 := fidStepsCap_le_256 c.scratch_cap
  change (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat)).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := c.scratch_cap) (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem s12a_call_fheap_up {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx : BitVec 32} {k : Tup Val [] → Expr Val Cont rs} {hlen_chk : Nat}
    (hinv : FullDenseInv c F0 st)
    (hidx_lt : idx.toNat < hlen_chk) (hhlen_le : hlen_chk ≤ 2 * st.core.cur_vars)
    (hhpp : ∀ i < hlen_chk, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ st' m',
      FullDenseInv c F0 st' → st'.core = st.core →
      (∀ i < hlen_chk, (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32]) "full_fheap_up_fid"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr, Arg.var idx, ()) k) m := by
  have hcv_le := hinv.1.lengths.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hnl_lt30 : 2 * st.core.cur_vars < 2 ^ 30 := by omega
  have hlen := hinv.1.lengths
  refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
  refine ⟨2 * st.core.cur_vars, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.repr,
    S12aFheapRest c st ⋆ R, by rw [hlen.scratch_ok.tarjan_mark_len]; omega,
    by rw [hlen.scratch_ok.tarjan_reach_len]; omega,
    by rw [hlen.core_ok.repr_len]; omega, hnl_lt30, Nat.lt_of_lt_of_le hidx_lt hhlen_le,
    (fun i hi => hhpp i (Nat.lt_of_le_of_lt (by simpa using hi) hidx_lt)),
    s12a_focus_fheap hm, fun hp' ps' m' hhp' hps' hsub hrest hm' => ?_⟩
  have hhhp' : hp'.length = 2 * c.max_vars := hhp'.trans hlen.scratch_ok.tarjan_mark_len
  have hhps' : ps'.length = 2 * c.max_vars := hps'.trans hlen.scratch_ok.tarjan_reach_len
  refine hk _ m' (s12a_dense_set_fheap hinv hhhp' hhps') rfl (fun i hi => ?_)
    (s12a_unfocus_fheap hm')
  by_cases hle : i ≤ idx.toNat
  · obtain ⟨j, hj, hget⟩ := hsub i (by simpa using hle)
    rw [hget]; exact hhpp j (Nat.lt_of_le_of_lt (by simpa using hj) hidx_lt)
  · rw [hrest i (by simpa using Nat.lt_of_not_ge hle)]; exact hhpp i hi

private theorem s12a_call_fheap_down {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx n : BitVec 32} {k : Tup Val [] → Expr Val Cont rs}
    (hinv : FullDenseInv c F0 st)
    (hidx_lt : idx.toNat < n.toNat) (hn_le : n.toNat ≤ 2 * st.core.cur_vars)
    (hhpp : ∀ i < n.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ st' m',
      FullDenseInv c F0 st' → st'.core = st.core →
      (∀ i < n.toNat, (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32, i32]) "full_fheap_down_fid"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
       Arg.var idx, Arg.var n, ()) k) m := by
  have hcv_le := hinv.1.lengths.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hnl_lt30 : 2 * st.core.cur_vars < 2 ^ 30 := by omega
  have hlen := hinv.1.lengths
  refine wp_call_of_spec _ _ (hDown _ _ _ _ ?_)
  refine ⟨2 * st.core.cur_vars, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.repr,
    S12aFheapRest c st ⋆ R, by rw [hlen.scratch_ok.tarjan_mark_len]; omega,
    by rw [hlen.scratch_ok.tarjan_reach_len]; omega,
    by rw [hlen.core_ok.repr_len]; omega, hnl_lt30, hidx_lt, hn_le,
    (fun i hi => hhpp i (by simpa using hi)),
    s12a_focus_fheap hm, fun hp' ps' m' hhp' hps' hsub hrest hm' => ?_⟩
  have hhhp' : hp'.length = 2 * c.max_vars := hhp'.trans hlen.scratch_ok.tarjan_mark_len
  have hhps' : ps'.length = 2 * c.max_vars := hps'.trans hlen.scratch_ok.tarjan_reach_len
  refine hk _ m' (s12a_dense_set_fheap hinv hhhp' hhps') rfl (fun i hi => ?_)
    (s12a_unfocus_fheap hm')
  by_cases hlt_n : i < n.toNat
  · obtain ⟨j, hj, hget⟩ := hsub i (by simpa using hlt_n)
    rw [hget]; exact hhpp j (by simpa using hj)
  · exact absurd hi hlt_n

private theorem s12a_call_upd_lit {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hUpd : ∀ a m Q X, step9BvaUpdLitSpec a m Q X →
      Γ "full_bva_upd_lit_fid" [i64, i64, i64, i64, i64, i64] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s0 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {hsz : BitVec 32} {cur_nl : BitVec 64} {tl : BitVec 32}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hnl : cur_nl.toNat = 2 * s0.core.cur_vars) (htl : tl.toNat < 2 * s0.core.cur_vars)
    (hI : S12aUpdInv c F0 s0 R hsz m)
    (hk : ∀ hsz' m', S12aUpdInv c F0 s0 R hsz' m' → wp Γ Q X (k (hsz', ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i64, i64, i64]) (bs := [i32])
      "full_bva_upd_lit_fid"
      (Arg.var c.hdr, Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
       Arg.var cur_nl, Arg.var ((BitVec.setWidth 64 hsz <<< (32 : Nat)) ||| BitVec.setWidth 64 tl),
       ()) k) m := by
  obtain ⟨st, hinv, hfr, hle, hhp, hm⟩ := hI
  have hcv := s12aHeapFr_cur_vars hfr
  refine wp_call_of_spec _ _ (hUpd _ _ _ _ ?_)
  refine ⟨c, F0, st, R, hsz, tl, rfl, rfl, rfl, rfl, rfl, hinv, by rw [hcv]; exact hnl,
    by rw [hcv]; exact htl, by rw [hcv]; exact hle, fun i hi => by rw [hcv]; exact hhp i hi,
    hm, fun hsz' rp hp ps m' hinv' hle' hhp' hm' => ?_⟩
  have hfr' : S12aHeapFr s0
      { core := { st.core with repr := rp },
        scratch := { st.scratch with tarjan_mark := hp, tarjan_reach := ps } } := by
    obtain ⟨_, _, _, rfl⟩ := hfr; exact ⟨rp, hp, ps, rfl⟩
  exact hk hsz' m' ⟨_, hinv', hfr',
    by rw [← hcv]; exact hle', fun i hi => by rw [← hcv]; exact hhp' i hi, hm'⟩

private def S12aTouchInv (c : FullCfg) (st3 : FullState) (R : Mem 64 → Prop)
    (nt : BitVec 64) (tmk : List (BitVec 8)) (tlits : List (BitVec 32)) (m : Mem 64) : Prop :=
  tmk.length = 2 * c.max_vars ∧ tlits.length = 2 * c.max_vars ∧
  nt.toNat ≤ 2 * st3.core.cur_vars ∧
  (∀ i < nt.toNat, (tlits[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars) ∧
  (∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 ≠ 0#8 →
    ∃ k < nt.toNat, (tlits[k]?.getD 0#32).toNat = l) ∧
  (FullMem c (s12aSetLmWs2 st3 tmk tlits) ⋆ R) m

private theorem s12a_push_touched_step {c : FullCfg} {st3 : FullState}
    (hcv_le : st3.core.cur_vars ≤ c.max_vars)
    {nt : BitVec 64} {tmk : List (BitVec 8)} {tlits : List (BitVec 32)} {x : BitVec 32}
    (htmk_len : tmk.length = 2 * c.max_vars) (htlits_len : tlits.length = 2 * c.max_vars)
    (hx_lt : x.toNat < 2 * st3.core.cur_vars) (hnt_lt : nt.toNat < 2 * st3.core.cur_vars)
    (hnt1 : (nt + 1#64).toNat = nt.toNat + 1)
    (htlits_b : ∀ i < nt.toNat, (tlits[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars)
    (hcov : ∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 ≠ 0#8 →
      ∃ k < nt.toNat, (tlits[k]?.getD 0#32).toNat = l) :
    let tmk' := tmk.set (BitVec.setWidth 64 x).toNat 1#8
    let tlits' := tlits.set nt.toNat x
    tmk'.length = 2 * c.max_vars ∧ tlits'.length = 2 * c.max_vars ∧
    (nt + 1#64).toNat ≤ 2 * st3.core.cur_vars ∧
    (∀ i < (nt + 1#64).toNat, (tlits'[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars) ∧
    (∀ l < 2 * c.max_vars, tmk'[l]?.getD 0#8 ≠ 0#8 →
      ∃ k < (nt + 1#64).toNat, (tlits'[k]?.getD 0#32).toNat = l) := by
  intro tmk' tlits'
  have hx64 : (BitVec.setWidth 64 x).toNat = x.toNat := fid_bv64_32 x
  have htlits_nt : nt.toNat < tlits.length := by rw [htlits_len]; omega
  refine ⟨by simp [tmk', htmk_len], by simp [tlits', htlits_len], by rw [hnt1]; omega,
    fun i hi => ?_, fun l hl hnz => ?_⟩
  · rw [hnt1] at hi
    by_cases heq : i = nt.toNat
    · subst heq; simp only [tlits', List.getElem?_set_self htlits_nt, Option.getD_some]; exact hx_lt
    · simp only [tlits', List.getElem?_set_ne (Ne.symm heq)]; exact htlits_b i (by omega)
  · by_cases hlx : l = x.toNat
    · refine ⟨nt.toNat, by rw [hnt1]; omega, ?_⟩
      simp only [tlits', List.getElem?_set_self htlits_nt, Option.getD_some, hlx]
    · have hne : (BitVec.setWidth 64 x).toNat ≠ l := by rw [hx64]; exact Ne.symm hlx
      have hpre : tmk[l]?.getD 0#8 ≠ 0#8 := by
        dsimp only [tmk'] at hnz
        rwa [List.getElem?_set_ne hne] at hnz
      obtain ⟨k, hk, hkl⟩ := hcov l hl hpre
      refine ⟨k, by rw [hnt1]; omega, ?_⟩
      simp only [tlits', List.getElem?_set_ne (by omega : nt.toNat ≠ k), hkl]

private theorem s12a_clear_step {c : FullCfg} {st3 : FullState}
    (hcv_le : st3.core.cur_vars ≤ c.max_vars)
    {ui nt : BitVec 64} {tmk : List (BitVec 8)} {tlits : List (BitVec 32)}
    (htmk_len : tmk.length = 2 * c.max_vars)
    (htlits_b : ∀ i < nt.toNat, (tlits[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars)
    (hui_lt : ui.toNat < nt.toNat) (hui1 : (ui + 1#64).toNat = ui.toNat + 1)
    (hcov : ∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 ≠ 0#8 →
      ∃ k, ui.toNat ≤ k ∧ k < nt.toNat ∧ (tlits[k]?.getD 0#32).toNat = l) :
    ∀ l < 2 * c.max_vars,
      (tmk.set (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat 0#8)[l]?.getD 0#8 ≠ 0#8 →
      ∃ k, (ui + 1#64).toNat ≤ k ∧ k < nt.toNat ∧ (tlits[k]?.getD 0#32).toNat = l := by
  intro l hl hnz
  have hx64 : (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat =
      (tlits[ui.toNat]?.getD 0#32).toNat := fid_bv64_32 _
  have hlen : (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat < tmk.length := by
    have := htlits_b ui.toNat hui_lt; rw [hx64, htmk_len]; omega
  by_cases hlx : l = (tlits[ui.toNat]?.getD 0#32).toNat
  · exfalso
    have heq : (tmk.set (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat 0#8)[l]?.getD 0#8 =
        0#8 := by
      have hidx : (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat = l := by rw [hx64, hlx]
      rw [hidx] at hlen ⊢
      rw [List.getElem?_set_self hlen, Option.getD_some]
    exact hnz heq
  · have hne : (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat ≠ l := by
      rw [hx64]; exact Ne.symm hlx
    have hpre : tmk[l]?.getD 0#8 ≠ 0#8 := by
      rwa [List.getElem?_set_ne hne] at hnz
    obtain ⟨k, hk1, hk2, hkl⟩ := hcov l hl hpre
    refine ⟨k, ?_, hk2, hkl⟩
    rw [hui1]
    by_cases hku : k = ui.toNat
    · subst hku; exact absurd hkl.symm hlx
    · omega

/-! ## 3. Parametric `Func.wp` Proof for `full_factor` -/

private abbrev facZeroSt (s : FullState) (ws hp ps : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with wsort := ws, tarjan_mark := hp, tarjan_reach := ps } }

private theorem s12a_lengths_set_ant_sz {c : FullCfg} {sc : FullScratch}
    (h : sc.LengthsOk c) (b : BitVec 64) : ({ sc with ant_sz := b } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, h.phases_len, h.phases_target_len, h.phases_best_len, h.walk_best_len,
   h.heap_len_arr, h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len,
   h.wsort_len, h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len,
   h.score_len, h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr,
   h.red_refs_len, h.extend_stk_len, h.scratch_buf_len⟩

private theorem fac12a_bv32_shl1_or1 (x : BitVec 64) (hx : x.toNat < 2 ^ 30) :
    (BitVec.setWidth 32 (x <<< (1 : Nat)) ||| 1#32).toNat = 2 * x.toNat + 1 := by
  have h1 : (BitVec.setWidth 32 (x <<< (1 : Nat))).toNat = 2 * x.toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 32)]
    omega
  rw [BitVec.toNat_or, h1, show (1#32 : BitVec 32).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    rw [show 1 / 2 = 0 from rfl, show (2 * x.toNat) / 2 = x.toNat from by omega,
      show (2 * x.toNat + 1) / 2 = x.toNat from by omega, Nat.zero_testBit, Bool.or_false]

/-- Step-12A `full_factor` (`P0-2`: touched-literal deduplication) preserves
`FullBvaHeap.fullFactorHeapSpec`. -/
private theorem fac12a_sub1_lt {a b : Nat} (h : a < b) : b - (a + 1) < b - a := by omega

private theorem fac12a_cw_ar2_lt {cw_n csz ar_len cap : Nat}
    (hle : cw_n + 3 + csz ≤ ar_len) (har : ar_len ≤ cap) : cw_n + 2 < cap := by omega

private theorem fac12a_cw_32_add2 {cw_n csz ar_len : Nat}
    (hle : cw_n + 3 + csz ≤ ar_len) (hb : ar_len < 2 ^ 32) : cw_n + 2 < 2 ^ 64 := by omega

private theorem fac12a_arl_idx_lt1 {cw_n csz ar_len : Nat}
    (hle : cw_n + 3 + csz ≤ ar_len) (hb : ar_len < 2 ^ 32) : cw_n + 3 < 2 ^ 64 := by omega

private theorem fac12a_arl_idx_lt2 {cw_n lj_n csz ar_len : Nat}
    (hlj : lj_n < csz) (hle : cw_n + 3 + csz ≤ ar_len) (hb : ar_len < 2 ^ 32) :
    cw_n + 3 + lj_n < 2 ^ 64 := by omega

private theorem fac12a_arl_ar_lt {cw_n lj_n csz ar_len cap : Nat}
    (hlj : lj_n < csz) (hle : cw_n + 3 + csz ≤ ar_len) (har : ar_len ≤ cap) :
    cw_n + 3 + lj_n < cap := by omega

private theorem s12a_set_sb_eq (st : FullState) (tmk : List (BitVec 8))
    (tlits : List (BitVec 32)) :
    (s12aSetLmWs2 st tmk tlits).scratch.scratch_buf = st.scratch.scratch_buf := rfl

private theorem fac12a_clear_upd_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hUpd : ∀ a m Q X, step9BvaUpdLitSpec a m Q X →
      Γ "full_bva_upd_lit_fid" [i64, i64, i64, i64, i64, i64] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {st3 : FullState} {R : Mem 64 → Prop} {mA : Mem 64}
    {nt : BitVec 64} {tmk : List (BitVec 8)} {tlits : List (BitVec 32)} {hsz' : BitVec 32}
    {Js : Cont [i32]}
    (hinv3 : FullDenseInv c F0 st3)
    (htmk_l : tmk.length = 2 * c.max_vars) (htlits_l : tlits.length = 2 * c.max_vars)
    (hnt_le : nt.toNat ≤ 2 * st3.core.cur_vars)
    (htlits_b : ∀ i < nt.toNat, (tlits[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars)
    (hcov : ∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 ≠ 0#8 →
      ∃ k < nt.toNat, (tlits[k]?.getD 0#32).toNat = l)
    (hhsz'_le : hsz'.toNat ≤ 2 * st3.core.cur_vars)
    (hhp3 : ∀ i < hsz'.toNat,
      (st3.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars)
    (hmA : (FullMem c (s12aSetLmWs2 st3 tmk tlits) ⋆ R) mA)
    (hOut : ∀ hsz_u mU,
      (∃ st_end : FullState, FullDenseInv c F0 st_end ∧
        st_end.core.cur_vars = st3.core.cur_vars ∧ st_end.core.fuel = st3.core.fuel ∧
        hsz_u.toNat ≤ 2 * st_end.core.cur_vars ∧
        (∀ i < hsz_u.toNat,
          (st_end.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st_end.core.cur_vars) ∧
        (FullMem c st_end ⋆ R) mU) →
      Js (hsz_u, ()) mU) :
    wp Γ Q X
      (Expr.group (sig := [[i64]])
        (fun Js_c =>
          Blocks.cons
            (fun p =>
              Expr.let_
                (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool rfl) (Arg.var p.fst, Arg.var nt, ()))
                fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_2 =>
                    Expr.let_
                      (Op.mk (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p_2.fst, ())) fun p_3 =>
                      Expr.load i32 (Arg.var p_3.fst) fun ld =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_4 =>
                          Expr.let_
                            (Op.mk (OpCode.add i64) (Arg.var c.pLitMark, Arg.var p_4.fst, ()))
                            fun p_5 =>
                            Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_6 =>
                              Expr.store (Arg.var p_6.fst) (Arg.var p_5.fst)
                                (Expr.let_
                                  (Op.mk (OpCode.add i64) (Arg.var p.fst, Arg.imm 1, ()))
                                  fun p => Expr.jump Js_c.fst (Arg.var p.fst, ())))
                  (Expr.group (sig := [[i32, i64]])
                    (fun Js_u =>
                      Blocks.cons
                        (fun p =>
                          Expr.let_
                            (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool rfl)
                              (Arg.var p.snd.fst, Arg.var nt, ())) fun p_2 =>
                            Expr.jnz (Arg.var p_2.fst)
                              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p_3 =>
                                Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 32, ()))
                                  fun p_4 =>
                                  Expr.let_
                                    (Op.mk (OpCode.shl i64) (Arg.var p_3.fst, Arg.var p_4.fst, ()))
                                    fun p_5 =>
                                    Expr.let_
                                      (Op.mk (OpCode.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ()))
                                      fun p_6 =>
                                      Expr.let_
                                        (Op.mk (OpCode.add i64)
                                          (Arg.var c.pWorkStk2, Arg.var p_6.fst, ())) fun p_7 =>
                                        Expr.load i32 (Arg.var p_7.fst) fun ld =>
                                          Expr.let_
                                            (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_8 =>
                                            Expr.let_
                                              (Op.mk (OpCode.or i64)
                                                (Arg.var p_5.fst, Arg.var p_8.fst, ())) fun p_9 =>
                                              Expr.call (as := [i64, i64, i64, i64, i64, i64])
                                                (bs := [i32]) "full_bva_upd_lit_fid"
                                                (Arg.var c.hdr, Arg.var c.pTarjanMark,
                                                 Arg.var c.pTarjanReach, Arg.var c.pRepr,
                                                 Arg.var (BitVec.ofNat 64 st3.core.cur_vars <<<
                                                   (1 : Nat)),
                                                 Arg.var p_9.fst, ()) fun p_10 =>
                                                Expr.let_
                                                  (Op.mk (OpCode.add i64)
                                                    (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
                                                  Expr.jump Js_u.fst (Arg.var p_10.fst,
                                                    Arg.var p.fst, ()))
                              (Expr.jump Js (Arg.var p.fst, ())))
                        Blocks.nil)
                    fun Js_u => Expr.jump Js_u.fst (Arg.var hsz', Arg.imm 0, ())))
            Blocks.nil)
        fun Js_c => Expr.jump Js_c.fst (Arg.imm 0, ())) mA := by
  have h3_cv_le := hinv3.1.lengths.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hnt_30 : nt.toNat < 2 ^ 30 := Nat.lt_of_le_of_lt hnt_le (by omega)
  have hcnl_eq : (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat =
      2 * st3.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]; omega
  refine wp_loop_inv
    (fun (ui, ()) mC => ui.toNat ≤ nt.toNat ∧ ∃ tmkC : List (BitVec 8),
      tmkC.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars, tmkC[l]?.getD 0#8 ≠ 0#8 →
        ∃ k, ui.toNat ≤ k ∧ k < nt.toNat ∧ (tlits[k]?.getD 0#32).toNat = l) ∧
      (FullMem c (s12aSetLmWs2 st3 tmkC tlits) ⋆ R) mC)
    (fun (ui, ()) _ => nt.toNat - ui.toNat)
    (fun Jc hJc => by
      c0_hfast_nogrp
      exact hJc (0#64, ()) mA ⟨Nat.zero_le _, tmk, htmk_l,
        fun l hl hnz => let ⟨k, hk, hkl⟩ := hcov l hl hnz; ⟨k, Nat.zero_le _, hk, hkl⟩, hmA⟩)
    (fun Jc (ui, ()) mC ⟨hui_le, tmkC, htmkC_l, hcovC, hmC⟩ ihc => ?_)
  · c0_hfast_nogrp
    · have hui_lt : ui.toNat < nt.toNat := BitVec.lt_def.mp (by assumption)
      have hui1 : (ui + 1#64).toNat = ui.toNat + 1 :=
        fac12a_bv64_add1 (Nat.lt_trans (Nat.add_lt_add_right hui_lt 1) (by omega))
      have htl_i : ui.toNat < tlits.length := by
        rw [htlits_l]; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hui_lt hnt_le) (by omega)
      have hlm_x : (BitVec.setWidth 64 (tlits[ui.toNat]'htl_i)).toNat < tmkC.length := by
        have h := htlits_b ui.toNat hui_lt
        rw [List.getElem?_eq_getElem htl_i, Option.getD_some] at h
        rw [fid_bv64_32, htmkC_l]; omega
      c0_hfast_nogrp
      have hcovC' := s12a_clear_step h3_cv_le htmkC_l htlits_b hui_lt hui1 hcovC
      rw [List.getElem?_eq_getElem htl_i, Option.getD_some] at hcovC'
      exact ihc (ui + 1#64, ()) _ (by dsimp only; rw [hui1]; omega)
        ⟨by rw [hui1]; omega, _, by simp [htmkC_l], hcovC', by assumption⟩
    · clear ihc
      have hui_ge : nt.toNat ≤ ui.toNat :=
        Nat.le_of_not_lt fun h => (by assumption : ¬ ui < nt) (BitVec.lt_def.mpr h)
      have hzero : ∀ l < 2 * c.max_vars, tmkC[l]?.getD 0#8 = 0#8 := by
        intro l hl
        cases hget : (tmkC[l]?.getD 0#8 == 0#8)
        · exfalso
          have hnz : tmkC[l]?.getD 0#8 ≠ 0#8 := by simp_all
          obtain ⟨k, hk1, hk2, _⟩ := hcovC l hl hnz
          omega
        · exact beq_iff_eq.mp hget
      let st_clr := s12aSetLmWs2 st3 tmkC tlits
      have hinv_clr : FullDenseInv c F0 st_clr :=
        s12a_dense_set_lm_ws2 hinv3 htmkC_l htlits_l hzero
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (hsz_u, ui, ()) mU => ui.toNat ≤ nt.toNat ∧ S12aUpdInv c F0 st_clr R hsz_u mU)
        (fun (_, ui, ()) _ => nt.toNat - ui.toNat)
        (fun Ju hJu => by
          c0_hfast_nogrp
          refine hJu (hsz', 0#64, ()) mC
            ⟨Nat.zero_le _, st_clr, hinv_clr, s12aHeapFr_refl st_clr, hhsz'_le,
             hhp3, hmC⟩)
        (fun Ju (hsz_u, ui, ()) mU ⟨hui_leU, hU⟩ ihu => ?_)
      · c0_hfast_nogrp
        · have hui_ltU : ui.toNat < nt.toNat := BitVec.lt_def.mp (by assumption)
          have hui1U : (ui + 1#64).toNat = ui.toNat + 1 :=
            fac12a_bv64_add1 (Nat.lt_trans (Nat.add_lt_add_right hui_ltU 1) (by omega))
          have ⟨stU, _, hfrU, _, _, _⟩ := hU
          have hws_u_eq : stU.scratch.work_stk2 = tlits := s12aHeapFr_work_stk2 hfrU
          have htl_u_lt : ui.toNat < stU.scratch.work_stk2.length := by
            rw [hws_u_eq, htlits_l]
            exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hui_ltU hnt_le) (by omega)
          have htl_val_lt : (stU.scratch.work_stk2[ui.toNat]'htl_u_lt).toNat <
              2 * st_clr.core.cur_vars := by
            have h := htlits_b ui.toNat hui_ltU
            have htl_i' : ui.toNat < tlits.length := by rw [← hws_u_eq]; exact htl_u_lt
            rw [List.getElem?_eq_getElem htl_i', Option.getD_some] at h
            dsimp only [st_clr, s12aSetLmWs2]; simp only [hws_u_eq]; exact h
          c0_hfast_nogrp
          refine s12a_call_upd_lit (s0 := st_clr) hUpd
            (by dsimp only [st_clr, s12aSetLmWs2]; exact hcnl_eq) htl_val_lt hU
            fun hsz_u' mU' hU' => ?_
          exact ihu (hsz_u', ui + 1#64, ()) mU' (by dsimp only; rw [hui1U]; omega)
            ⟨by rw [hui1U]; omega, hU'⟩
        · clear ihu
          obtain ⟨st_end, hinv_end, hfr_end, hhsz_end, hhp_end, hm_end⟩ := hU
          have hcv_end := s12aHeapFr_cur_vars hfr_end
          have hfu_end := s12aHeapFr_fuel hfr_end
          exact hOut hsz_u mU
            ⟨st_end, hinv_end, hcv_end, hfu_end, by rw [hcv_end]; exact hhsz_end,
             by rw [hcv_end]; exact hhp_end, hm_end⟩

private theorem fac12a_fheap_pop_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {st st1a : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {init_cv : Nat} {init_fuel : BitVec 64} {hsz : BitVec 32} {J : Cont []}
    (hhsz_pos : 0 < hsz.toNat) (hhsz1 : (hsz - 1#32).toNat = hsz.toNat - 1)
    (hhsz_le : hsz.toNat ≤ 2 * st.core.cur_vars)
    (hcv_st : init_cv ≤ st.core.cur_vars) (hfu_st : st.core.fuel = init_fuel)
    (hinv1a : FullDenseInv c F0 st1a)
    (hc_eq : st1a.core = st.core)
    (htm_eq : st1a.scratch.tarjan_mark = st.scratch.tarjan_mark)
    (hhp_st : ∀ i < hsz.toNat,
      (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hm : (FullMem c st1a ⋆ R) m)
    (hJ : ∀ xs m2, (∃ st2 : FullState,
        init_cv ≤ st2.core.cur_vars ∧ st2.core.fuel = init_fuel ∧
        st2.core.cur_vars = st.core.cur_vars ∧ FullDenseInv c F0 st2 ∧
        (∀ i < (hsz - 1#32).toNat,
          (st2.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st2.core.cur_vars) ∧
        (FullMem c st2 ⋆ R) m2) → J xs m2) :
    wp Γ Q X
      (Expr.let_
        (Op.mk (OpCode.cmp CmpOp.ugt i32 Ty.bool rfl) (Arg.var (hsz - 1#32), Arg.imm 0, ()))
        fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 0, ())) fun p =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p.fst, ()))
                fun p =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var (hsz - 1#32), ())) fun p_1 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_1.fst, Arg.imm 4, ()))
                    fun p_2 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pTarjanMark, Arg.var p_2.fst, ())) fun p_3 =>
                      Expr.load i32 (Arg.var p_3.fst) fun ld =>
                        Expr.store (Arg.var ld) (Arg.var p.fst)
                          (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 0, ())) fun p =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()))
                              fun p =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.pTarjanMark, Arg.var p.fst, ())) fun p =>
                                Expr.load i32 (Arg.var p.fst) fun ld =>
                                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ()))
                                    fun p =>
                                    Expr.let_ (Op.mk (OpCode.mul i64)
                                        (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                                      Expr.let_ (Op.mk (OpCode.add i64)
                                          (Arg.var c.pTarjanReach, Arg.var p.fst, ())) fun p =>
                                        Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                                          (Expr.call (as := [i64, i64, i64, i32, i32]) (bs := [])
                                            "full_fheap_down_fid"
                                            (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach,
                                             Arg.var c.pRepr, Arg.imm 0,
                                             Arg.var (hsz - 1#32), ())
                                            fun _ => Expr.jump J ())))
          (Expr.jump J ())) m := by
  have h1al := hinv1a.1.lengths
  have hcv1a : st1a.core.cur_vars = st.core.cur_vars := congrArg (·.cur_vars) hc_eq
  have h1a_cv_le := h1al.core_ok.cur_vars_le
  c0_hfast_nogrp
  · have hhsz1_pos : 0 < (hsz - 1#32).toNat :=
      by simpa using (by assumption : BitVec.toNat 0 < (hsz - 1#32).toNat)
    have hhsz1_lt : (hsz - 1#32).toNat < 2 * st.core.cur_vars := by rw [hhsz1]; omega
    have hlast_lt : (BitVec.setWidth 64 (hsz - 1#32)).toNat < st1a.scratch.tarjan_mark.length := by
      rw [fid_bv64_32, h1al.scratch_ok.tarjan_mark_len]; omega
    obtain ⟨last, hlast_def⟩ : ∃ last : BitVec 32,
        last = st1a.scratch.tarjan_mark[(BitVec.setWidth 64 (hsz - 1#32)).toNat]'hlast_lt :=
      ⟨_, rfl⟩
    have hlast_lt2 : last.toNat < 2 * st.core.cur_vars := by
      have hhsz1_lt_hsz : (hsz - 1#32).toNat < hsz.toNat := by rw [hhsz1]; omega
      have h1 := hhp_st (hsz - 1#32).toNat hhsz1_lt_hsz
      have hmlt : (hsz - 1#32).toNat < st1a.scratch.tarjan_mark.length := by
        rw [h1al.scratch_ok.tarjan_mark_len]; omega
      rw [← htm_eq, List.getElem?_eq_getElem hmlt, Option.getD_some] at h1
      have hidx : (BitVec.setWidth 64 (hsz - 1#32)).toNat = (hsz - 1#32).toNat :=
        fid_bv64_32 (hsz - 1#32)
      simpa only [hlast_def, hidx] using h1
    have h0_lt : 0 < st1a.scratch.tarjan_mark.length := by
      rw [h1al.scratch_ok.tarjan_mark_len]; omega
    have h0_lt64 : (BitVec.ofNat 64 0).toNat < st1a.scratch.tarjan_mark.length := by
      simpa using h0_lt
    c0_hfast_nogrp
    let st1m : FullState :=
      { st1a with scratch := { st1a.scratch with
        tarjan_mark := st1a.scratch.tarjan_mark.set 0 last } }
    have hz64 : (BitVec.ofNat 64 0).toNat = 0 := rfl
    replace hm : (FullMem c st1m ⋆ R) m := by
      dsimp only [st1m]
      simpa only [← hlast_def, hz64] using hm
    have htm0_eq :
        ({ st1a with scratch := { st1a.scratch with
            tarjan_mark := st1a.scratch.tarjan_mark.set (BitVec.ofNat 64 0).toNat
              st1a.scratch.tarjan_mark[(BitVec.setWidth 64 (hsz - 1#32)).toNat] }
          }).scratch.tarjan_mark[(BitVec.ofNat 64 0).toNat]'(
            by dsimp; rw [List.length_set]; exact h0_lt) = last := by
      dsimp only
      rw [List.getElem_set_self (by rw [List.length_set]; exact h0_lt64)]
      exact hlast_def.symm
    rw [htm0_eq]
    have hval_last_lt : (BitVec.setWidth 64 last).toNat < st1m.scratch.tarjan_reach.length := by
      dsimp only [st1m]; rw [fid_bv64_32, h1al.scratch_ok.tarjan_reach_len]; omega
    c0_hfast_nogrp
    let st1b : FullState :=
      { st1m with scratch := { st1m.scratch with
        tarjan_reach := st1m.scratch.tarjan_reach.set last.toNat 0#32 } }
    have hm_b : (FullMem c st1b ⋆ R) m := by
      dsimp only [st1b, st1m]
      rw [← fid_bv64_32 (x := last)]
      exact hm
    have hinv1b : FullDenseInv c F0 st1b :=
      s12a_dense_set_fheap hinv1a
        (by dsimp [st1b, st1m]; rw [List.length_set, h1al.scratch_ok.tarjan_mark_len])
        (by
          dsimp [st1b, st1m]
          rw [List.length_set, h1al.scratch_ok.tarjan_reach_len])
    have hhp1b : ∀ i < (hsz - 1#32).toNat,
        (st1b.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st1b.core.cur_vars := by
      intro i hi
      dsimp only [st1b, st1m]
      rw [hcv1a]
      by_cases hi0 : i = 0
      · subst hi0; rw [List.getElem?_set_self h0_lt, Option.getD_some]; exact hlast_lt2
      · rw [List.getElem?_set_ne (Ne.symm hi0), htm_eq]; exact hhp_st i (by omega)
    refine s12a_call_fheap_down (idx := 0#32) (n := hsz - 1#32) hDown hinv1b
      hhsz1_pos (by dsimp only [st1b, st1m]; rw [hcv1a]; omega) hhp1b hm_b
      fun st2 m2 hinv2 hcore2 hhp2 hm2 => ?_
    exact hJ () m2 ⟨st2, by rw [congrArg (·.cur_vars) hcore2, hcv1a]; exact hcv_st,
      (congrArg (·.fuel) hcore2).trans ((congrArg (·.fuel) hc_eq).trans hfu_st),
      (congrArg (·.cur_vars) hcore2).trans hcv1a,
      hinv2, by rw [congrArg (·.cur_vars) hcore2]; exact hhp2, hm2⟩
  · exact hJ () m ⟨st1a, hcv1a ▸ hcv_st, (congrArg (·.fuel) hc_eq).trans hfu_st, hcv1a, hinv1a,
      fun i hi => by exfalso; have h0 : hsz - 1#32 = 0#32 := by bv_omega
                     rw [h0] at hi; simp at hi, hm⟩

private theorem fac12a_zero_build_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s1 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {max_nlits64 : Val i64} {K : Tup Val [i32, i64] → Expr Val Cont [i64]}
    (hmx : c.max_vars < 2 * dimacsBound) (hinv1 : FullDenseInv c F0 s1)
    (hmnl_64 : max_nlits64.toNat = 2 * c.max_vars) (hm : (FullMem c s1 ⋆ R) m)
    (hK : ∀ (hsz : Val i32) (vi : Val i64) (mh : Mem 64),
      (∃ st1 : FullState, hsz.toNat ≤ 2 * s1.core.cur_vars ∧ FullDenseInv c F0 st1 ∧
        st1.core.cur_vars = s1.core.cur_vars ∧ st1.core.fuel = s1.core.fuel ∧
        (∀ i < hsz.toNat,
          (st1.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
        (FullMem c st1 ⋆ R) mh) → wp Γ Q X (K (hsz, vi, ())) mh) :
    wp Γ Q X
      (Expr.group (sig := [[i64]])
        (fun Js =>
          Blocks.cons
            (fun p =>
              Expr.let_
                (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p.fst, Arg.var max_nlits64, ()))
                fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_2 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pWsort, Arg.var p_2.fst, ()))
                      fun p_3 =>
                      Expr.store (t := i32) (Arg.imm 0) (Arg.var p_3.fst)
                        (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_4 =>
                          Expr.let_
                            (Op.mk (.add i64) (Arg.var c.pTarjanMark, Arg.var p_4.fst, ()))
                            fun p_5 =>
                            Expr.store (t := i32) (Arg.imm 0) (Arg.var p_5.fst)
                              (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ()))
                                fun p_6 =>
                                Expr.let_
                                  (Op.mk (.add i64) (Arg.var c.pTarjanReach, Arg.var p_6.fst, ()))
                                  fun p_7 =>
                                  Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p_7.fst)
                                    (Expr.let_
                                      (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ()))
                                      fun p => Expr.jump Js.fst (Arg.var p.fst, ())))))
                  (Expr.group (sig := [[i32, i64]])
                    (fun Js =>
                      Blocks.cons
                        (fun p =>
                          Expr.let_
                            (Op.mk (.cmp .ult i64 .bool rfl)
                              (Arg.var p.snd.fst, Arg.var (BitVec.ofNat 64 s1.core.cur_vars), ()))
                            fun p_2 =>
                            Expr.jnz (Arg.var p_2.fst)
                              (Expr.group (sig := [[i32]])
                                (fun _Js_1 =>
                                  Blocks.cons
                                    (fun p_3 =>
                                      Expr.let_
                                        (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ()))
                                        fun p =>
                                        Expr.jump Js.fst (Arg.var p_3.fst, Arg.var p.fst, ()))
                                    Blocks.nil)
                                fun Js =>
                                Expr.let_ (Op.mk (.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ()))
                                  fun p_3 =>
                                  Expr.let_
                                    (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_3.fst, ()))
                                    fun p_4 =>
                                    Expr.load i32 (Arg.var p_4.fst) fun ld =>
                                      Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 1, ()))
                                        fun p_5 =>
                                        Expr.let_
                                          (Op.mk (.cmp .ne i32 .bool rfl)
                                            (Arg.var p_5.fst, Arg.imm 0, ()))
                                          fun p_6 =>
                                          Expr.jnz (Arg.var p_6.fst)
                                            (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ()))
                                              fun p_7 =>
                                              Expr.let_
                                                (Op.mk (.shl i64)
                                                  (Arg.var p.snd.fst, Arg.var p_7.fst, ()))
                                                fun p_8 =>
                                                Expr.let_
                                                  (Op.mk (.add i64)
                                                    (Arg.var c.pVals, Arg.var p_8.fst, ()))
                                                  fun p_9 =>
                                                  Expr.load i8 (Arg.var p_9.fst) fun ld =>
                                                    Expr.let_
                                                      (Op.mk (.trunc 32 8) (Arg.imm 0, ()))
                                                      fun p_10 =>
                                                      Expr.let_
                                                        (Op.mk (.sext 8 32) (Arg.var ld, ()))
                                                        fun p_11 =>
                                                        Expr.let_
                                                          (Op.mk (.sext 8 32)
                                                            (Arg.var p_10.fst, ()))
                                                          fun p_12 =>
                                                          Expr.let_
                                                            (Op.mk (.cmp .eq i32 .bool rfl)
                                                              (Arg.var p_11.fst,
                                                               Arg.var p_12.fst, ()))
                                                            fun p_13 =>
                                                            Expr.jnz (Arg.var p_13.fst)
                                                              (Expr.let_
                                                                (Op.mk (.sext 32 64)
                                                                  (Arg.imm 1, ()))
                                                                fun p_14 =>
                                                                Expr.let_
                                                                  (Op.mk (.shl i64)
                                                                    (Arg.var p.snd.fst,
                                                                     Arg.var p_14.fst, ()))
                                                                  fun p_15 =>
                                                                  Expr.let_
                                                                    (Op.mk (.trunc 64 32)
                                                                      (Arg.var p_15.fst, ()))
                                                                    fun p_16 =>
                                                                    Expr.let_
                                                                      (Op.mk (.or i32)
                                                                        (Arg.var p_16.fst,
                                                                         Arg.imm 1, ()))
                                                                      fun p_17 =>
                                                                      Expr.group (sig := [[i32]])
                                                                        (fun _Js_1 =>
                                                                          Blocks.cons
                                                                            (fun p_18 =>
                                                                              Expr.group
                                                                                (sig := [[i32]])
                                                                                (fun _Js_2 =>
                                                                                  Blocks.cons
                                                                                    (fun p =>
                                                                                      Expr.jump
                                                                                        Js.fst
                                                                                        (Arg.var
                                                                                           p.fst,
                                                                                         ()))
                                                                                    Blocks.nil)
                                                                                fun Js =>
                                                                                Expr.let_
                                                                                  (Op.mk (.mul i64)
                                                                                    (Arg.var
                                                                                       p.snd.fst,
                                                                                     Arg.imm 4,
                                                                                     ()))
                                                                                  fun p =>
                                                                                  Expr.let_
                                                                                    (Op.mk
                                                                                      (.add i64)
                                                                                      (Arg.var
                                                                                         c.pFlags,
                                                                                       Arg.var
                                                                                         p.fst,
                                                                                       ()))
                                                                                    fun p =>
                                                                                    Expr.load i32
                                                                                      (Arg.var
                                                                                         p.fst)
                                                                                      fun ld =>
                                                                                      Expr.let_
                                                                                        (Op.mk
                                                                                          (.and i32)
                                                                                          (Arg.var
                                                                                             ld,
                                                                                           Arg.imm
                                                                                             64,
                                                                                           ()))
                                                                                        fun p =>
                                                                                        Expr.let_
                                                                                          (Op.mk
                                                                                            (.cmp
                                                                                              .ne
                                                                                              i32
                                                                                              .bool
                                                                                              rfl)
                                                                                            (Arg.var
                   p.fst,
                                                                                             Arg.imm
                                                                                               0,
                                                                                             ()))
                                                                                          fun p =>
                                                                                          Expr.jnz
                                                                                            (Arg.var
                                                                                              p.fst)
                (Expr.let_
                                                                                              (Op.mk
                (.zext 32 64)
                (Arg.var
                  p_17.fst,
                 ()))
                  fun p =>
                  Expr.let_
                (Op.mk
                  (.mul i64)
                  (Arg.var
                p.fst,
                   Arg.imm 4,
                   ()))
                fun p =>
                Expr.let_
                  (Op.mk
                (.add i64)
                (Arg.var c.pRepr,
                 Arg.var p.fst,
                 ()))
                  fun p =>
                  Expr.load i32
                (Arg.var p.fst)
                fun ld =>
                Expr.let_
                  (Op.mk
                (.cmp .ugt i32 .bool rfl)
                (Arg.var ld,
                 Arg.imm 1,
                 ()))
                  fun p =>
                  Expr.jnz
                (Arg.var p.fst)
                (Expr.let_
                  (Op.mk (.zext 32 64)
                (Arg.var p_18.fst, ()))
                  fun p =>
                  Expr.let_
                (Op.mk (.mul i64)
                  (Arg.var p.fst, Arg.imm 4, ()))
                fun p =>
                Expr.let_
                  (Op.mk (.add i64)
                (Arg.var c.pTarjanMark, Arg.var p.fst, ()))
                  fun p =>
                  Expr.store (Arg.var p_17.fst) (Arg.var p.fst)
                (Expr.let_
                  (Op.mk (.zext 32 64)
                (Arg.var p_17.fst, ()))
                  fun p =>
                  Expr.let_
                (Op.mk (.mul i64)
                  (Arg.var p.fst, Arg.imm 4, ()))
                fun p =>
                Expr.let_
                  (Op.mk (.add i64)
                (Arg.var c.pTarjanReach, Arg.var p.fst, ()))
                  fun p =>
                  Expr.store (Arg.var p_18.fst) (Arg.var p.fst)
                (Expr.call
                  (as := [i64, i64, i64, i32])
                  (bs := [])
                  "full_fheap_up_fid"
                  (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
                  Arg.var p_18.fst, ())
                  fun _ =>
                  Expr.let_
                (Op.mk (.add i32)
                  (Arg.var p_18.fst, Arg.imm 1, ()))
                fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ()))))
                (Expr.jump Js.fst (Arg.var p_18.fst, ())))
                (Expr.jump
                                                                                              Js.fst
                  (Arg.var
                 p_18.fst,
                                                                                               ())))
                                                                            Blocks.nil)
                                                                        fun Js =>
                                                                        Expr.let_
                                                                          (Op.mk (.mul i64)
                                                                            (Arg.var p.snd.fst,
                                                                             Arg.imm 4, ()))
                                                                          fun p_18 =>
                                                                          Expr.let_
                                                                            (Op.mk (.add i64)
                                                                              (Arg.var c.pFlags,
                                                                               Arg.var p_18.fst,
                                                                               ()))
                                                                            fun p_19 =>
                                                                            Expr.load i32
                                                                              (Arg.var p_19.fst)
                                                                              fun ld =>
                                                                              Expr.let_
                                                                                (Op.mk (.and i32)
                                                                                  (Arg.var ld,
                                                                                   Arg.imm 32, ()))
                                                                                fun p_20 =>
                                                                                Expr.let_
                                                                                  (Op.mk
                                                                                    (.cmp .ne i32
                                                                                      .bool rfl)
                                                                                    (Arg.var
                                                                                       p_20.fst,
                                                                                     Arg.imm 0, ()))
                                                                                  fun p_21 =>
                                                                                  Expr.jnz
                                                                                    (Arg.var
                                                                                       p_21.fst)
                                                                                    (Expr.let_
                                                                                      (Op.mk
                                                                                        (.zext 32
                                                                                          64)
                                                                                        (Arg.var
                                                                                           p_16.fst,
                                                                                         ()))
                                                                                      fun p_22 =>
                                                                                      Expr.let_
                                                                                        (Op.mk
                                                                                          (.mul i64)
                                                                                          (Arg.var
                 p_22.fst,
                                                                                           Arg.imm
                                                                                             4, ()))
                                                                                        fun p_23 =>
                                                                                        Expr.let_
                                                                                          (Op.mk
                                                                                            (.add
                                                                                              i64)
                                                                                            (Arg.var
                   c.pRepr,
                                                                                             Arg.var
                   p_23.fst,
                                                                                             ()))
                  fun p_24 =>
                                                                                          Expr.load
                                                                                            i32
                                                                                            (Arg.var
                  p_24.fst)
                fun ld =>
                Expr.let_
                                                                                              (Op.mk
                (.cmp .ugt i32 .bool rfl)
                (Arg.var ld,
                 Arg.imm 1,
                 ()))
                  fun p_25 =>
                  Expr.jnz
                (Arg.var p_25.fst)
                (Expr.let_
                  (Op.mk (.zext 32 64)
                (Arg.var p.fst, ()))
                  fun p_26 =>
                  Expr.let_
                (Op.mk (.mul i64)
                  (Arg.var p_26.fst, Arg.imm 4, ()))
                fun p_27 =>
                Expr.let_
                  (Op.mk (.add i64)
                (Arg.var c.pTarjanMark, Arg.var p_27.fst, ()))
                  fun p_28 =>
                  Expr.store (Arg.var p_16.fst) (Arg.var p_28.fst)
                (Expr.let_
                  (Op.mk (.zext 32 64)
                (Arg.var p_16.fst, ()))
                  fun p_29 =>
                  Expr.let_
                (Op.mk (.mul i64)
                  (Arg.var p_29.fst, Arg.imm 4, ()))
                fun p_30 =>
                Expr.let_
                  (Op.mk (.add i64)
                (Arg.var c.pTarjanReach, Arg.var p_30.fst, ()))
                  fun p_31 =>
                  Expr.store (Arg.var p.fst) (Arg.var p_31.fst)
                (Expr.call
                  (as := [i64, i64, i64, i32])
                  (bs := [])
                  "full_fheap_up_fid"
                  (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr, Arg.var p.fst,
                  ())
                  fun _p_32 =>
                  Expr.let_
                (Op.mk (.add i32)
                  (Arg.var p.fst, Arg.imm 1, ()))
                fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ()))))
                (Expr.jump Js.fst (Arg.var p.fst, ())))
                                                                                    (Expr.jump
                                                                                      Js.fst
                                                                                      (Arg.var
                 p.fst, ())))
                  (Expr.jump Js.fst (Arg.var p.fst, ())))
                                            (Expr.jump Js.fst (Arg.var p.fst, ())))
                              (K p))
                        Blocks.nil)
                    fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())))
            Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m := by
  unfold dimacsBound at hmx
  have h1l := hinv1.1.lengths
  have h1_cv_le := h1l.core_ok.cur_vars_le
  refine wp_loop_inv (ts := [i64])
    (fun (zi, ()) mz => zi.toNat ≤ 2 * c.max_vars ∧ ∃ wsZ hpZ psZ : List (BitVec 32),
      wsZ.length = 2 * c.max_vars ∧ hpZ.length = 2 * c.max_vars ∧ psZ.length = 2 * c.max_vars ∧
      (FullMem c (facZeroSt s1 wsZ hpZ psZ) ⋆ R) mz)
    (fun (zi, ()) _ => 2 * c.max_vars - zi.toNat)
    (fun Jz hJz => by
      c0_hfast_nogrp
      exact hJz (0#64, ()) _ ⟨Nat.zero_le _, s1.scratch.wsort, s1.scratch.tarjan_mark,
        s1.scratch.tarjan_reach, h1l.scratch_ok.wsort_len, h1l.scratch_ok.tarjan_mark_len,
        h1l.scratch_ok.tarjan_reach_len, hm⟩)
    (fun Jz (zi, ()) mz ⟨hzi_le, wsZ, hpZ, psZ, hwsZ, hhpZ, hpsZ, hmz⟩ ihz => ?_)
  · c0_hfast_nogrp
    · have hzi_lt : zi.toNat < 2 * c.max_vars := by
        have h1 := BitVec.lt_def.mp (by assumption : zi < max_nlits64)
        rw [hmnl_64] at h1; exact h1
      have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := fac12a_bv64_add1 (by omega)
      c0_hfast_nogrp
      exact ihz (zi + 1#64, ()) _ (by dsimp only; rw [hzi1]; omega)
        ⟨by rw [hzi1]; omega, wsZ.set zi.toNat 0#32, hpZ.set zi.toNat 0#32,
         psZ.set zi.toNat 0xFFFFFFFF#32, by rw [List.length_set, hwsZ],
         by rw [List.length_set, hhpZ], by rw [List.length_set, hpsZ], by assumption⟩
    · clear ihz
      let sZ : FullState := facZeroSt s1 wsZ hpZ psZ
      let h1sc := h1l.scratch_ok
      have hinvZ : FullDenseInv c F0 sZ :=
        hinv1.of_safetySlice ⟨h1l.core_ok,
          { h1sc with wsort_len := hwsZ, tarjan_mark_len := hhpZ, tarjan_reach_len := hpsZ }⟩
          rfl ⟨rfl, rfl⟩
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (hsz, vi, ()) mh => ∃ st1 : FullState,
          vi.toNat ≤ s1.core.cur_vars ∧ hsz.toNat ≤ 2 * vi.toNat ∧ FullDenseInv c F0 st1 ∧
          st1.core.cur_vars = s1.core.cur_vars ∧ st1.core.fuel = s1.core.fuel ∧
          (∀ i < hsz.toNat,
            (st1.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
          (FullMem c st1 ⋆ R) mh)
        (fun (_, vi, ()) _ => s1.core.cur_vars - vi.toNat)
        (fun Jh hJh => by
          c0_hfast_nogrp
          exact hJh (0#32, 0#64, ()) mz
            ⟨sZ, Nat.zero_le _, Nat.zero_le _, hinvZ, rfl, rfl,
             fun _ hi => absurd hi (Nat.not_lt_zero _), hmz⟩)
        (fun Jh (hsz, vi, ()) mh ⟨st1, hvi_le, hhsz_le, hinv_1, hcv_1, hfu_1, hhp1, hmh⟩ ih1 => ?_)
      · c0_hfast_nogrp
        · have hvi_lt : vi.toNat < s1.core.cur_vars := by
            have h1 : vi.toNat < s1.core.cur_vars % 2 ^ 64 := by assumption
            rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
          have hcv1_lt32 : 2 * st1.core.cur_vars < 2 ^ 32 := by
            have := hinv_1.1.lengths.core_ok.cur_vars_le; omega
          have hvi1 : (vi + 1#64).toNat = vi.toNat + 1 := fac12a_bv64_add1 (by omega)
          have hhl1 : (hsz + 1#32).toNat = hsz.toNat + 1 := fac12a_bv32_add1 (by omega)
          have hhl2 : (hsz + 1#32 + 1#32).toNat = hsz.toNat + 2 := by
            rw [fac12a_bv32_add1 (by rw [hhl1]; omega), hhl1]
          have h1l := hinv_1.1.lengths
          have hfl_lt : vi.toNat < st1.core.flags.length := by rw [h1l.core_ok.flags_len]; omega
          have hvl_lt : (vi.toNat * 2 ^ 1) % 2 ^ 64 < st1.core.vals.length := by
            rw [h1l.core_ok.vals_len, Nat.mod_eq_of_lt (by omega)]; omega
          have hpl_deg_lt : (2 * vi.toNat) % 2 ^ 64 < st1.core.repr.length := by
            rw [h1l.core_ok.repr_len, Nat.mod_eq_of_lt (by omega)]; omega
          have hpl32_toNat : (BitVec.setWidth 32 (vi <<< (1 : Nat))).toNat = 2 * vi.toNat := by
            rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
              Nat.mod_eq_of_lt (by omega : vi.toNat * 2 ^ 1 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : vi.toNat * 2 ^ 1 < 2 ^ 32)]
            omega
          have hnl32_toNat : (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32).toNat =
              2 * vi.toNat + 1 := fac12a_bv32_shl1_or1 vi (by omega)
          have hnl_deg_lt :
              (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                st1.core.repr.length := by
            rw [fid_bv64_32, hnl32_toNat, h1l.core_ok.repr_len]; omega
          c0_hfast
          · have hhl_lt : hsz.toNat < 2 * st1.core.cur_vars := by omega
            have hhp_p_lt : hsz.toNat < st1.scratch.tarjan_mark.length := by
              rw [h1l.scratch_ok.tarjan_mark_len]; omega
            have hps_p_lt : (2 * vi.toNat) % 2 ^ 64 < st1.scratch.tarjan_reach.length := by
              rw [h1l.scratch_ok.tarjan_reach_len, Nat.mod_eq_of_lt (by omega)]; omega
            c0_hfast
            let st_p0 : FullState :=
              { st1 with scratch := { st1.scratch with
                tarjan_mark := st1.scratch.tarjan_mark.set (BitVec.setWidth 64 hsz).toNat
                  (BitVec.setWidth 32 (vi <<< (1 : Nat)))
                tarjan_reach := st1.scratch.tarjan_reach.set
                  (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)))).toNat hsz } }
            have hinv_p0 : FullDenseInv c F0 st_p0 :=
              s12a_dense_set_fheap hinv_1 (by simp [h1l.scratch_ok.tarjan_mark_len])
                (by simp [h1l.scratch_ok.tarjan_reach_len])
            refine s12a_call_fheap_up hUp hinv_p0 (hlen_chk := hsz.toNat + 1)
              (Nat.lt_succ_self _) (by dsimp [st_p0]; omega) ?_ (by assumption)
              fun st_p m' hinv_p hcore_p hhp_p hm' => ?_
            · intro k hk; dsimp only [st_p0]; rw [fid_bv64_32, hcv_1]
              exact fac12a_push_pre_lt (by rw [hpl32_toNat]; omega) hhp_p_lt hhp1 k
                (Nat.lt_succ_iff.mp hk)
            · have hcv_p : st_p.core.cur_vars = s1.core.cur_vars :=
                (congrArg (·.cur_vars) hcore_p).trans hcv_1
              have hfu_p : st_p.core.fuel = s1.core.fuel := (congrArg (·.fuel) hcore_p).trans hfu_1
              have hhp_p' : ∀ k < (hsz + 1#32).toNat,
                  (st_p.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * s1.core.cur_vars := by
                intro k hk; rw [hhl1] at hk
                have h := hhp_p k hk; dsimp only [st_p0] at h; rw [hcv_1] at h; exact h
              have hpl_p := hinv_p.1.lengths
              have hflp_lt : vi.toNat < st_p.core.flags.length := by
                rw [hpl_p.core_ok.flags_len]; omega
              have hnld_p_lt :
                  (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                    st_p.core.repr.length := by
                rw [fid_bv64_32, hnl32_toNat, hpl_p.core_ok.repr_len]; omega
              c0_hfast
              · have hphl_lt : (hsz + 1#32).toNat < 2 * st_p.core.cur_vars := by
                  rw [hcv_p, hhl1]; omega
                have hhp_np_lt : (hsz + 1#32).toNat < st_p.scratch.tarjan_mark.length := by
                  rw [hpl_p.scratch_ok.tarjan_mark_len]; omega
                have hps_np_lt :
                    (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                      st_p.scratch.tarjan_reach.length := by
                  rw [fid_bv64_32, hnl32_toNat, hpl_p.scratch_ok.tarjan_reach_len]; omega
                c0_hfast
                let st_pn0 : FullState :=
                  { st_p with scratch := { st_p.scratch with
                    tarjan_mark := st_p.scratch.tarjan_mark.set
                      (BitVec.setWidth 64 (hsz + 1#32)).toNat
                      (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)
                    tarjan_reach := st_p.scratch.tarjan_reach.set
                      (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat
                      (hsz + 1#32) } }
                have hinv_pn0 : FullDenseInv c F0 st_pn0 :=
                  s12a_dense_set_fheap hinv_p (by simp [hpl_p.scratch_ok.tarjan_mark_len])
                    (by simp [hpl_p.scratch_ok.tarjan_reach_len])
                refine s12a_call_fheap_up hUp hinv_pn0 (hlen_chk := (hsz + 1#32).toNat + 1)
                  (Nat.lt_succ_self _) (by dsimp [st_pn0]; rw [hcv_p]; omega) ?_ (by assumption)
                  fun st_pn m2 hinv_pn hcore_pn hhp_pn hm2 => ?_
                · intro k hk; dsimp only [st_pn0]; rw [fid_bv64_32, hcv_p]
                  exact fac12a_push_pre_lt (by rw [hnl32_toNat]; omega) hhp_np_lt hhp_p' k
                    (Nat.lt_succ_iff.mp hk)
                · c0_hfast
                  refine ih1 (hsz + 1#32 + 1#32, vi + 1#64, ()) m2 (by dsimp only; rw [hvi1]; omega)
                    ⟨st_pn, by rw [hvi1]; omega, by rw [hhl2, hvi1]; omega, hinv_pn,
                     (congrArg (·.cur_vars) hcore_pn).trans hcv_p,
                     (congrArg (·.fuel) hcore_pn).trans hfu_p, fun k hk => by
                       rw [hhl2] at hk
                       have h := hhp_pn k (by rw [hhl1]; omega)
                       dsimp only [st_pn0] at h; rw [hcv_p] at h; exact h, hm2⟩
              all_goals
                exact ih1 (hsz + 1#32, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
                  ⟨st_p, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_p, hcv_p, hfu_p,
                   hhp_p', by assumption⟩
          all_goals
            (try c0_hfast)
            first
            | exact ih1 (hsz, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
                ⟨st1, by rw [hvi1]; omega, by rw [hvi1]; omega, hinv_1, hcv_1, hfu_1, hhp1,
                 by assumption⟩
            | (have hhl_lt : hsz.toNat < 2 * st1.core.cur_vars := by omega
               have hhp_n_lt : hsz.toNat < st1.scratch.tarjan_mark.length := by
                 rw [h1l.scratch_ok.tarjan_mark_len]; omega
               have hps_n_lt :
                   (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                     st1.scratch.tarjan_reach.length := by
                 rw [fid_bv64_32, hnl32_toNat, h1l.scratch_ok.tarjan_reach_len]; omega
               c0_hfast_nogrp
               let st_n0 : FullState :=
                 { st1 with scratch := { st1.scratch with
                   tarjan_mark := st1.scratch.tarjan_mark.set (BitVec.setWidth 64 hsz).toNat
                     (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)
                   tarjan_reach := st1.scratch.tarjan_reach.set
                     (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat
                     hsz } }
               have hinv_n0 : FullDenseInv c F0 st_n0 :=
                 s12a_dense_set_fheap hinv_1 (by simp [h1l.scratch_ok.tarjan_mark_len])
                   (by simp [h1l.scratch_ok.tarjan_reach_len])
               refine s12a_call_fheap_up hUp hinv_n0 (hlen_chk := hsz.toNat + 1)
                 (Nat.lt_succ_self _) (by dsimp [st_n0]; omega) ?_ (by assumption)
                 fun st_n m' hinv_n hcore_n hhp_n hm' => ?_
               · intro k hk; dsimp only [st_n0]; rw [fid_bv64_32, hcv_1]
                 exact fac12a_push_pre_lt (by rw [hnl32_toNat]; omega) hhp_n_lt hhp1 k
                   (Nat.lt_succ_iff.mp hk)
               · c0_hfast
                 refine ih1 (hsz + 1#32, vi + 1#64, ()) m' (by dsimp only; rw [hvi1]; omega)
                   ⟨st_n, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_n,
                    (congrArg (·.cur_vars) hcore_n).trans hcv_1,
                    (congrArg (·.fuel) hcore_n).trans hfu_1, fun k hk => by
                      rw [hhl1] at hk
                      have h := hhp_n k hk
                      dsimp only [st_n0] at h; rw [hcv_1] at h; exact h, hm'⟩)
        · clear ih1
          exact hK hsz vi mh ⟨st1, by omega, hinv_1, hcv_1, hfu_1, hhp1, hmh⟩

private theorem fac12a_qi_scan_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {st3 : FullState} {R : Mem 64 → Prop} {mP2 : Mem 64}
    {nt2 : Val i64} {ro_bv qn_bv fac_lit qs_dec : Val i32} {nl64 : Val i64}
    {tmk2 : List (BitVec 8)} {tlits2 : List (BitVec 32)} {Ja : Cont [i64, i32]}
    (hmx : c.max_vars < 2 * dimacsBound) (hscr_b : c.scratch_cap < 2 ^ 28)
    (hinv3 : FullDenseInv c F0 st3) (hnl64 : nl64.toNat = 2 * st3.core.cur_vars)
    (hroqn_bnd : ro_bv.toNat + qn_bv.toNat ≤ c.scratch_cap)
    (hrow_ok : ∀ qi_n < qn_bv.toNat,
      Step7RowRefOk st3 (st3.scratch.scratch_buf[ro_bv.toNat + qi_n]?.getD 0#32))
    (hT2 : S12aTouchInv c st3 R nt2 tmk2 tlits2 mP2)
    (hJa_next : ∀ ntQ mQ, (∃ tmkQ tlitsQ, S12aTouchInv c st3 R ntQ tmkQ tlitsQ mQ) →
      Ja (ntQ, qs_dec, ()) mQ) :
    wp Γ Q X
      (Expr.group (sig := [[i64, i32]])
        (fun Js =>
          Blocks.cons
            (fun p =>
              Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.snd.fst, Arg.var qn_bv, ()))
                fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ (Op.mk (.add i32) (Arg.var ro_bv, Arg.var p.snd.fst, ())) fun p_2 =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
                      Expr.let_ (Op.mk (.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
                          fun p_5 =>
                          Expr.load i32 (Arg.var p_5.fst) fun ld =>
                            Expr.group (sig := [[i64]])
                              (fun _Js_1 =>
                                Blocks.cons
                                  (fun p_6 =>
                                    Expr.let_
                                      (Op.mk (.add i32) (Arg.var p.snd.fst, Arg.imm 1, ()))
                                      fun p =>
                                      Expr.jump Js.fst (Arg.var p_6.fst, Arg.var p.fst, ()))
                                  Blocks.nil)
                              fun Js =>
                              Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 2147483648, ()))
                                fun p_6 =>
                                Expr.let_
                                  (Op.mk (.cmp .ne i32 .bool rfl)
                                    (Arg.var p_6.fst, Arg.imm 0, ())) fun p_7 =>
                                  Expr.jnz (Arg.var p_7.fst)
                                    (Expr.let_
                                      (Op.mk (.and i32) (Arg.var ld, Arg.imm 2147483647, ()))
                                      fun p_8 =>
                                      Expr.group (sig := [[i64]])
                                        (fun _Js_1 =>
                                          Blocks.cons
                                            (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
                                            Blocks.nil)
                                        fun Js =>
                                        Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_8.fst, ()))
                                          fun p_9 =>
                                          Expr.let_
                                            (Op.mk (.cmp .ult i64 .bool rfl)
                                              (Arg.var p_9.fst, Arg.var nl64, ())) fun p_10 =>
                                            Expr.jnz (Arg.var p_10.fst)
                                              (Expr.let_
                                                (Op.mk (.zext 32 64) (Arg.var p_8.fst, ()))
                                                fun p_11 =>
                                                Expr.let_
                                                  (Op.mk (.add i64)
                                                    (Arg.var c.pLitMark, Arg.var p_11.fst, ()))
                                                  fun p_12 =>
                                                  Expr.load i8 (Arg.var p_12.fst) fun ld =>
                                                    Expr.let_
                                                      (Op.mk (.trunc 32 8) (Arg.imm 0, ()))
                                                      fun p_13 =>
                                                      Expr.let_
                                                        (Op.mk (.zext 8 32) (Arg.var ld, ()))
                                                        fun p_14 =>
                                                        Expr.let_
                                                          (Op.mk (.zext 8 32)
                                                            (Arg.var p_13.fst, ())) fun p_15 =>
                                                          Expr.let_
                                                            (Op.mk (.cmp .eq i32 .bool rfl)
                                                              (Arg.var p_14.fst,
                                                               Arg.var p_15.fst, ())) fun p_16 =>
                                                            Expr.jnz (Arg.var p_16.fst)
                                                              (Expr.let_
                                                                (Op.mk (.cmp .ult i64 .bool rfl)
                                                                  (Arg.var p.fst, Arg.var nl64, ()))
                                                                fun p_17 =>
                                                                Expr.jnz (Arg.var p_17.fst)
                                                                  (Expr.let_
                                                                    (Op.mk (.zext 32 64)
                                                                      (Arg.var p_8.fst, ()))
                                                                    fun p_18 =>
                                                                    Expr.let_
                                                                      (Op.mk (.add i64)
                                                                        (Arg.var c.pLitMark,
                                                                         Arg.var p_18.fst, ()))
                                                                      fun p_19 =>
                                                                      Expr.let_
                                                                        (Op.mk (.trunc 32 8)
                                                                          (Arg.imm 1, ()))
                                                                        fun p_20 =>
                                                                        Expr.store
                                                                          (Arg.var p_20.fst)
                                                                          (Arg.var p_19.fst)
                                                                          (Expr.let_
                                                                            (Op.mk (.mul i64)
                                                                              (Arg.var p.fst,
                                                                               Arg.imm 4, ()))
                                                                            fun p_21 =>
                                                                            Expr.let_
                                                                              (Op.mk (.add i64)
                                                                                (Arg.var
                                                                                   c.pWorkStk2,
                                                                                 Arg.var p_21.fst,
                                                                                 ())) fun p_22 =>
                                                                              Expr.store
                                                                                (Arg.var p_8.fst)
                                                                                (Arg.var p_22.fst)
                                                                                (Expr.let_
                                                                                  (Op.mk (.add i64)
                                                                                    (Arg.var p.fst,
                                                                                     Arg.imm 1,
                                                                                     ())) fun p =>
                                                                                  Expr.jump Js.fst
                                                                                    (Arg.var p.fst,
                                                                                     ()))))
                                                                  (Expr.jump Js.fst
                                                                    (Arg.var p.fst, ())))
                  (Expr.jump Js.fst (Arg.var p.fst, ())))
                                              (Expr.jump Js.fst (Arg.var p.fst, ())))
                                    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_8 =>
                                      Expr.let_
                                        (Op.mk (.add i64) (Arg.var p_8.fst, Arg.imm 2, ()))
                                        fun p_9 =>
                                        Expr.let_
                                          (Op.mk (.mul i64) (Arg.var p_9.fst, Arg.imm 4, ()))
                                          fun p_10 =>
                                          Expr.let_
                                            (Op.mk (.add i64)
                                              (Arg.var c.pArena, Arg.var p_10.fst, ()))
                                            fun p_11 =>
                                            Expr.load i32 (Arg.var p_11.fst) fun ld_1 =>
                                              Expr.group (sig := [[i64, i32]])
                                                (fun Js_1 =>
                                                  Blocks.cons
                                                    (fun p =>
                                                      Expr.let_
                                                        (Op.mk (.cmp .ult i32 .bool rfl)
                                                          (Arg.var p.snd.fst, Arg.var ld_1, ()))
                                                        fun p_12 =>
                                                        Expr.jnz (Arg.var p_12.fst)
                                                          (Expr.let_
                                                            (Op.mk (.zext 32 64) (Arg.var ld, ()))
                                                            fun p_13 =>
                                                            Expr.let_
                                                              (Op.mk (.add i64)
                                                                (Arg.var p_13.fst, Arg.imm 3, ()))
                                                              fun p_14 =>
                                                              Expr.let_
                                                                (Op.mk (.zext 32 64)
                                                                  (Arg.var p.snd.fst, ()))
                                                                fun p_15 =>
                                                                Expr.let_
                                                                  (Op.mk (.add i64)
                                                                    (Arg.var p_14.fst,
                                                                     Arg.var p_15.fst, ()))
                                                                  fun p_16 =>
                                                                  Expr.let_
                                                                    (Op.mk (.mul i64)
                                                                      (Arg.var p_16.fst,
                                                                       Arg.imm 4, ())) fun p_17 =>
                                                                    Expr.let_
                                                                      (Op.mk (.add i64)
                                                                        (Arg.var c.pArena,
                                                                         Arg.var p_17.fst, ()))
                                                                      fun p_18 =>
                                                                      Expr.load i32
                                                                        (Arg.var p_18.fst)
                                                                        fun ld =>
                                                                        Expr.group (sig := [[i64]])
                                                                          (fun _Js =>
                                                                            Blocks.cons
                                                                              (fun p_19 =>
                                                                                Expr.let_
                                                                                  (Op.mk (.add i32)
                                                                                    (Arg.var
                                                                                       p.snd.fst,
                                                                                     Arg.imm 1,
                                                                                     ())) fun p =>
                                                                                  Expr.jump Js_1.fst
                                                                                    (Arg.var
                                                                                       p_19.fst,
                                                                                     Arg.var p.fst,
                                                                                     ()))
                                                                              Blocks.nil)
                                                                          fun Js =>
                                                                          Expr.let_
                                                                            (Op.mk
                                                                              (.cmp .ne i32 .bool
                                                                                rfl)
                                                                              (Arg.var ld,
                                                                               Arg.var fac_lit, ()))
                                                                            fun p_19 =>
                                                                            Expr.jnz
                                                                              (Arg.var p_19.fst)
                                                                              (Expr.let_
                                                                                (Op.mk (.zext 32 64)
                                                                                  (Arg.var ld, ()))
                                                                                fun p_20 =>
                                                                                Expr.let_
                                                                                  (Op.mk
                                                                                    (.cmp .ult i64
                                                                                      .bool rfl)
                                                                                    (Arg.var
                                                                                       p_20.fst,
                                                                                     Arg.var nl64,
                 ())) fun p_21 =>
                                                                                  Expr.jnz
                                                                                    (Arg.var
                                                                                       p_21.fst)
                                                                                    (Expr.let_
                                                                                      (Op.mk
                                                                                        (.zext 32
                                                                                          64)
                                                                                        (Arg.var ld,
                                                                                         ()))
                                                                                      fun p_22 =>
                                                                                      Expr.let_
                                                                                        (Op.mk
                                                                                          (.add i64)
                                                                                          (Arg.var
                c.pLitMark,
                                                                                           Arg.var
                p_22.fst,
                                                                                           ()))
                                                                                        fun p_23 =>
                                                                                        Expr.load i8
                                                                                          (Arg.var
                p_23.fst)
                  fun ld_2 =>
                                                                                          Expr.let_
                (Op.mk (.trunc 32 8) (Arg.imm 0, ()))
                fun p_24 =>
                Expr.let_
                  (Op.mk (.zext 8 32) (Arg.var ld_2, ()))
                  fun p_25 =>
                  Expr.let_
                (Op.mk (.zext 8 32) (Arg.var p_24.fst, ()))
                fun p_26 =>
                Expr.let_
                  (Op.mk (.cmp .eq i32 .bool rfl)
                (Arg.var p_25.fst, Arg.var p_26.fst, ()))
                  fun p_27 =>
                  Expr.jnz (Arg.var p_27.fst)
                (Expr.let_
                  (Op.mk (.cmp .ult i64 .bool rfl)
                (Arg.var p.fst, Arg.var nl64, ()))
                  fun p_28 =>
                  Expr.jnz (Arg.var p_28.fst)
                (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_29 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pLitMark, Arg.var p_29.fst, ()))
                  fun p_30 =>
                Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 1, ())) fun p_31 =>
                  Expr.store (Arg.var p_31.fst) (Arg.var p_30.fst)
                (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_32 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pWorkStk2, Arg.var p_32.fst, ()))
                  fun p_33 =>
                Expr.store (Arg.var ld) (Arg.var p_33.fst)
                  (Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ()))))
                (Expr.jump Js.fst (Arg.var p.fst, ())))
                (Expr.jump Js.fst (Arg.var p.fst, ())))
                                                                                    (Expr.jump
                                                                                      Js.fst
                                                                                      (Arg.var
                                                                                         p.fst,
                                                                                       ())))
                                                                              (Expr.jump Js.fst
                (Arg.var p.fst, ())))
                                                          (Expr.jump Js.fst (Arg.var p.fst, ())))
                                                    Blocks.nil)
                                                fun Js =>
                                                Expr.jump Js.fst (Arg.var p.fst, Arg.imm 0, ())))
                  (Expr.jump Ja (Arg.var p.fst, Arg.var qs_dec, ())))
            Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.var nt2, Arg.imm 0, ())) mP2 := by
  unfold dimacsBound at hmx
  have h3l := hinv3.1.lengths
  have h3_cv_le := h3l.core_ok.cur_vars_le
  have h3_cv32 : 2 * c.max_vars < 2 ^ 30 := by omega
  obtain ⟨htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩ := hT2
  refine wp_loop_inv
    (fun (ntQ, qi, ()) mQ => qi.toNat ≤ qn_bv.toNat ∧ ∃ tmkQ tlitsQ,
      S12aTouchInv c st3 R ntQ tmkQ tlitsQ mQ)
    (fun (_, qi, ()) _ => qn_bv.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hfast_nogrp
      exact hJq (nt2, 0#32, ()) mP2 ⟨Nat.zero_le _, tmk2, tlits2,
        htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩)
    (fun Jq (ntQ, qi, ()) mQ
        ⟨hqi_le, tmkQ, tlitsQ, htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩ ihq => ?_)
  · c0_hfast_nogrp
    · have hqi_lt : qi.toNat < qn_bv.toNat := BitVec.lt_def.mp (by assumption)
      have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 :=
        fac12a_bv32_add1 (Nat.lt_of_le_of_lt hqi_lt qn_bv.isLt)
      have hro_add_qi : ro_bv.toNat + qi.toNat < c.scratch_cap :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hqi_lt _) hroqn_bnd
      have hcw_idx : (ro_bv + qi).toNat = ro_bv.toNat + qi.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt
          (Nat.lt_trans hro_add_qi (Nat.lt_trans hscr_b (by decide)))]
      have hcw_sc : (BitVec.setWidth 64 (ro_bv + qi)).toNat <
          st3.scratch.scratch_buf.length := by
        rw [fid_bv64_32, hcw_idx, h3l.scratch_ok.scratch_buf_len]; exact hro_add_qi
      let cw := st3.scratch.scratch_buf[(BitVec.setWidth 64 (ro_bv + qi)).toNat]'hcw_sc
      have hcw_ok : Step7RowRefOk st3 cw := by
        have h := hrow_ok qi.toNat hqi_lt
        rw [List.getElem?_eq_getElem (by rw [h3l.scratch_ok.scratch_buf_len]; exact hro_add_qi),
          Option.getD_some] at h
        simpa only [cw, fid_bv64_32, hcw_idx] using h
      have hcw_sc_Q : (BitVec.setWidth 64 (ro_bv + qi)).toNat <
          (s12aSetLmWs2 st3 tmkQ tlitsQ).scratch.scratch_buf.length := by
        dsimp only [s12aSetLmWs2]; exact hcw_sc
      c0_hfast_nogrp
      refine wp_join_group (ts := [i64]) (fun (nt', ()) mQ' =>
          ∃ tmk' tlits', S12aTouchInv c st3 R nt' tmk' tlits' mQ') ?_ ?_
      · rintro _ ⟨nt', ⟨⟩⟩ mQ' ⟨tmk', tlits', hT'⟩
        c0_hstraight
        exact ihq (nt', qi + 1#32, ()) mQ'
          (by dsimp only; rw [hqi1]; exact fac12a_sub1_lt hqi_lt)
          ⟨by rw [hqi1]; exact hqi_lt, tmk', tlits', hT'⟩
      · intro _ hJs
        c0_hstraight
        refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
        · intro hcBin
          have hbin : (cw &&& 0x80000000#32) ≠ 0#32 := by
            have h1 := bne_iff_ne.mp hcBin
            dsimp only [s12aSetLmWs2] at h1; exact h1
          have hol_lt : (cw &&& 0x7FFFFFFF#32).toNat < 2 * st3.core.cur_vars := by
            unfold Step7RowRefOk at hcw_ok; rwa [ite_eq_left hbin] at hcw_ok
          c0_hstraight
          refine wp_join_group (ts := [i64]) (fun (nt', ()) mQ' =>
              ∃ tmk' tlits', S12aTouchInv c st3 R nt' tmk' tlits' mQ') ?_ ?_
          · rintro _ ⟨nt', ⟨⟩⟩ mQ' ⟨tmk', tlits', hT'⟩
            c0_hstraight; exact hJs (nt', ()) mQ' ⟨tmk', tlits', hT'⟩
          · intro _ hJo
            c0_hfast_nogrp
            · have hlm_x : (BitVec.setWidth 64 (cw &&& 0x7FFFFFFF#32)).toNat < tmkQ.length := by
                rw [fid_bv64_32, htmkQ_l]
                exact Nat.lt_of_lt_of_le hol_lt (Nat.mul_le_mul_left 2 h3_cv_le)
              c0_hfast_nogrp
              · have hntQ_lt : ntQ.toNat < 2 * st3.core.cur_vars := by
                  have h1 : ntQ.toNat < nl64.toNat := BitVec.lt_def.mp (by assumption)
                  rwa [hnl64] at h1
                have hntQ1 : (ntQ + 1#64).toNat = ntQ.toNat + 1 :=
                  fac12a_bv64_add1 (Nat.lt_trans (Nat.add_lt_add_right hntQ_lt 1)
                    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h3_cv_le) 1)
                      (Nat.lt_trans (Nat.add_lt_add_right h3_cv32 1) (by decide))))
                have hws_nt : ntQ.toNat < tlitsQ.length := by
                  rw [htlitsQ_l]; exact Nat.lt_of_lt_of_le hntQ_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                c0_hfast_nogrp
                have hpsQ := s12a_push_touched_step h3_cv_le htmkQ_l htlitsQ_l hol_lt hntQ_lt hntQ1
                  htlitsQ_b hcovQ
                exact hJo (ntQ + 1#64, ()) _ ⟨_, _,
                  hpsQ.1, hpsQ.2.1, hpsQ.2.2.1, hpsQ.2.2.2.1, hpsQ.2.2.2.2, by assumption⟩
              all_goals
                exact hJo (ntQ, ()) mQ ⟨tmkQ, tlitsQ, htmkQ_l, htlitsQ_l,
                  hntQ_le, htlitsQ_b, hcovQ, hmQ⟩
            · exact hJo (ntQ, ()) mQ ⟨tmkQ, tlitsQ, htmkQ_l, htlitsQ_l,
                hntQ_le, htlitsQ_b, hcovQ, hmQ⟩
        · intro hcCls
          have hnbin : (cw &&& 0x80000000#32) = 0#32 := by
            exact if h : (cw &&& 0x80000000#32) = 0#32 then h else
              False.elim <| by
                have hb := bne_iff_ne.mpr h
                have hfl : ((cw &&& 0x80000000#32) != 0#32) = false := by
                  have h1 := hcCls; dsimp only [s12aSetLmWs2] at h1; exact h1
                rw [hfl] at hb; cases hb
          have hcw_lg : cw.toNat ∈ fullArenaClauseRefs st3 ∧
              cw.toNat + 3 + fullArenaClauseSize st3 cw.toNat ≤ st3.core.arena_len ∧
              ∀ l ∈ fullArenaClauseLits st3 cw.toNat, l < 2 * st3.core.cur_vars := by
            unfold Step7RowRefOk at hcw_ok; rwa [ite_eq_right (fun h => h hnbin)] at hcw_ok
          have har_lt32 : st3.core.arena_len < 2 ^ 32 := by
            have := h3l.core_ok.arena_len_le; have := h3l.core_ok.arena_len_arr
            have := c.harena; unfold dimacsBound at *; omega
          have har2_lt : (BitVec.setWidth 64 cw + 2#64).toNat < st3.core.arena.length := by
            rw [BitVec.toNat_add, fid_bv64_32, show (2#64 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (fac12a_cw_32_add2 hcw_lg.2.1 har_lt32), h3l.core_ok.arena_len_arr]
            exact fac12a_cw_ar2_lt hcw_lg.2.1
              (h3l.core_ok.arena_len_arr ▸ h3l.core_ok.arena_len_le)
          c0_hstraight
          let csz_bv := st3.core.arena[(BitVec.setWidth 64 cw + 2#64).toNat]'har2_lt
          have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore st3.core cw.toNat := by
            dsimp only [csz_bv]; unfold fullArenaClauseSizeCore
            have hidx : (BitVec.setWidth 64 cw + 2#64).toNat = cw.toNat + 2 := by
              rw [BitVec.toNat_add, fid_bv64_32, show (2#64 : BitVec 64).toNat = 2 from rfl,
                Nat.mod_eq_of_lt (fac12a_cw_32_add2 hcw_lg.2.1 har_lt32)]
            simp only [hidx]
            rw [List.getElem?_eq_getElem (by
              rw [h3l.core_ok.arena_len_arr]
              exact fac12a_cw_ar2_lt hcw_lg.2.1
                (h3l.core_ok.arena_len_arr ▸ h3l.core_ok.arena_len_le)), Option.getD_some]
          refine wp_loop_inv
            (fun (ntL, lj, ()) mL => lj.toNat ≤ csz_bv.toNat ∧
              ∃ tmkL tlitsL, S12aTouchInv c st3 R ntL tmkL tlitsL mL)
            (fun (_, lj, ()) _ => csz_bv.toNat - lj.toNat)
            (fun Jl hJl => by
              c0_hstraight
              exact hJl (ntQ, 0#32, ()) mQ ⟨Nat.zero_le _, tmkQ, tlitsQ,
                htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩)
            (fun Jl (ntL, lj, ()) mL
                ⟨hlj_le, tmkL, tlitsL, htmkL_l, htlitsL_l, hntL_le, htlitsL_b, hcovL, hmL⟩
                ihl => ?_)
          · c0_hfast_nogrp
            · have hlj_lt : lj.toNat < csz_bv.toNat := BitVec.lt_def.mp (by assumption)
              have hcsz_le_ar : csz_bv.toNat ≤ st3.core.arena_len := by
                rw [hcsz_eq]; exact Nat.le_trans (Nat.le_add_left _ _) hcw_lg.2.1
              have hlj1 : (lj + 1#32).toNat = lj.toNat + 1 := fac12a_bv32_add1 (by omega)
              have hcsz_cl : csz_bv.toNat = fullArenaClauseSize st3 cw.toNat := hcsz_eq
              have harl_idx : (BitVec.setWidth 64 cw + 3#64 + BitVec.setWidth 64 lj).toNat =
                  cw.toNat + 3 + lj.toNat := by
                rw [BitVec.toNat_add, BitVec.toNat_add, fid_bv64_32, fid_bv64_32,
                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                  Nat.mod_eq_of_lt (fac12a_arl_idx_lt1 hcw_lg.2.1 har_lt32),
                  Nat.mod_eq_of_lt (fac12a_arl_idx_lt2 (hcsz_cl ▸ hlj_lt) hcw_lg.2.1 har_lt32)]
              have harl_lt : (BitVec.setWidth 64 cw + 3#64 + BitVec.setWidth 64 lj).toNat <
                  st3.core.arena.length := by
                rw [harl_idx, h3l.core_ok.arena_len_arr]
                exact fac12a_arl_ar_lt (hcsz_cl ▸ hlj_lt) hcw_lg.2.1
                  (h3l.core_ok.arena_len_arr ▸ h3l.core_ok.arena_len_le)
              have hl_lt : (st3.core.arena[(BitVec.setWidth 64 cw + 3#64 +
                  BitVec.setWidth 64 lj).toNat]'harl_lt).toNat < 2 * st3.core.cur_vars := by
                have hg := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                  (k := st3.core) (r := cw.toNat) (j := lj.toNat)
                  (by rw [← hcsz_eq]; exact hlj_lt) (by rw [← harl_idx]; exact harl_lt)
                have hmem : (st3.core.arena[(BitVec.setWidth 64 cw + 3#64 +
                    BitVec.setWidth 64 lj).toNat]'harl_lt).toNat ∈
                    fullArenaClauseLits st3 cw.toNat := by
                  apply List.mem_iff_getElem?.mpr; refine ⟨lj.toNat, ?_⟩
                  simpa only [harl_idx] using hg
                exact hcw_lg.2.2 _ hmem
              c0_hfast_nogrp
              · refine wp_join_group (ts := [i64]) (fun (ntL', ()) mL' =>
                    ∃ tmkL' tlitsL', S12aTouchInv c st3 R ntL' tmkL' tlitsL' mL') ?_ ?_
                · rintro _ ⟨ntL', ⟨⟩⟩ mL' ⟨tmkL', tlitsL', hTL'⟩
                  c0_hfast_nogrp
                  exact ihl (ntL', lj + 1#32, ()) mL'
                    (by dsimp only; rw [hlj1]; exact fac12a_sub1_lt hlj_lt)
                    ⟨by rw [hlj1]; exact hlj_lt, tmkL', tlitsL', hTL'⟩
                · intro _ hJl'
                  c0_hfast_nogrp
                  · have hlm_l : (BitVec.setWidth 64 (st3.core.arena[(BitVec.setWidth 64 cw + 3#64 +
                        BitVec.setWidth 64 lj).toNat]'harl_lt)).toNat < tmkL.length := by
                      rw [fid_bv64_32, htmkL_l]
                      exact Nat.lt_of_lt_of_le hl_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                    c0_hfast_nogrp
                    · have hntL_lt : ntL.toNat < 2 * st3.core.cur_vars := by
                        have h1 : ntL.toNat < nl64.toNat := BitVec.lt_def.mp (by assumption)
                        rwa [hnl64] at h1
                      have hntL1 : (ntL + 1#64).toNat = ntL.toNat + 1 :=
                        fac12a_bv64_add1 (by omega)
                      have hws_nt : ntL.toNat < tlitsL.length := by
                        rw [htlitsL_l]
                        exact Nat.lt_of_lt_of_le hntL_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                      c0_hfast_nogrp
                      have hpsL := s12a_push_touched_step h3_cv_le htmkL_l htlitsL_l hl_lt hntL_lt
                        hntL1 htlitsL_b hcovL
                      exact hJl' (ntL + 1#64, ()) _ ⟨_, _,
                        hpsL.1, hpsL.2.1, hpsL.2.2.1, hpsL.2.2.2.1, hpsL.2.2.2.2, by assumption⟩
                    all_goals
                      exact hJl' (ntL, ()) mL ⟨tmkL, tlitsL, htmkL_l, htlitsL_l,
                        hntL_le, htlitsL_b, hcovL, hmL⟩
                  all_goals
                    exact hJl' (ntL, ()) mL ⟨tmkL, tlitsL, htmkL_l, htlitsL_l,
                      hntL_le, htlitsL_b, hcovL, hmL⟩
            · exact hJs (ntL, ()) mL ⟨tmkL, tlitsL, htmkL_l, htlitsL_l,
                hntL_le, htlitsL_b, hcovL, hmL⟩
    · exact hJa_next ntQ mQ ⟨tmkQ, tlitsQ, htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩

theorem full_factor_step12a_wp (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hConnect : ∀ a m Q X, fidBvaConnectClausesSpec a m Q X →
      Γ "full_bva_connect_clauses_fid" [i64] [] a m Q X)
    (hUp : ∀ a m Q X, fidFheapUpSpec a m Q X →
      Γ "full_fheap_up_fid" [i64, i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fidFheapDownSpec a m Q X →
      Γ "full_fheap_down_fid" [i64, i64, i64, i32, i32] [] a m Q X)
    (hTryLit : ∀ a m Q X, step7BvaTryLitSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m Q X)
    (hUpd : ∀ a m Q X, step9BvaUpdLitSpec a m Q X →
      Γ "full_bva_upd_lit_fid" [i64, i64, i64, i64, i64, i64] [i32] a m Q X) :
    ∀ args m Q X, fullFactorHeapSpec args m Q X →
      Func.wp Γ full_factor_body args m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_factor_body
  have hmx := c.hmaxv
  have hmx_n : c.max_vars < 2 * 2 ^ 28 := by simpa [dimacsBound] using hmx
  have hscr_b := c.hscr; unfold dimacsBound at hscr_b
  have hlen := hinv.1.lengths
  have hcv_le := hlen.core_ok.cur_vars_le
  c0_hfast_nogrp
  refine s12a_call_steps_cap hSteps fun scb hscb => ?_
  c0_hsplit
  · c0_hfast; exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  c0_hsplit
  · c0_hfast; exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  c0_hsplit
  · c0_hfast; exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  obtain ⟨F_cur0, hw0⟩ := hinv.1.witness
  have hdw0 : FullDenseInvW c F0 F_cur0 s :=
    ⟨hlen, hw0, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩
  refine wp_call_of_spec _ _ (hConnect (c.hdr, ()) m (fun r m' => wp Γ Q X _ m') X
    ⟨c, F0, F_cur0, s, R, rfl, hdw0, hm, fun s0 m0 hdw1 hcv0 hfu0 _ _ _ hm0 => ?_⟩)
  have hinv0 : FullDenseInv c F0 s0 :=
    ⟨⟨hdw1.1, F_cur0, hdw1.2.1⟩, hdw1.2.2.1, hdw1.2.2.2.1, hdw1.2.2.2.2.1,
     hdw1.2.2.2.2.2.1, hdw1.2.2.2.2.2.2⟩
  c0_hfast_nogrp
  · exact hQ 1#64 s0 m0 hinv0 (Nat.le_of_eq hcv0.symm) hfu0 rfl hm0
  let s1 : FullState := { s0 with scratch := { s0.scratch with ant_sz := budget } }
  have hinv1 : FullDenseInv c F0 s1 :=
    hinv0.of_safetySlice ⟨hdw1.1.core_ok, s12a_lengths_set_ant_sz hdw1.1.scratch_ok budget⟩
      rfl ⟨rfl, rfl⟩
  let init_cv := s1.core.cur_vars
  let init_fuel := s1.core.fuel
  have hinit_cv_eq : init_cv = s.core.cur_vars := hcv0
  have hinit_fuel_eq : init_fuel = s.core.fuel := hfu0
  have h1l := hinv1.1.lengths
  have h1_cv_le := h1l.core_ok.cur_vars_le
  have hmnl_64 : (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat = 2 * c.max_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  refine fac12a_zero_build_wp (R := R) hUp hmx hinv1 hmnl_64 (by assumption)
    fun hsz _vi mh ⟨st1, hhsz_1, hinv_1, hcv_1, hfu_1, hhp1, hmh⟩ => ?_
  c0_hfast_nogrp
  refine wp_while_state (ts := [i32]) (α := FullState × BitVec 32)
    (fun p => (p.2, ()))
    (fun p => (c.max_vars - p.1.core.cur_vars) * (2 * c.max_vars + 1) + p.2.toNat)
    (fun (st, hsz) mw => init_cv ≤ st.core.cur_vars ∧ st.core.fuel = init_fuel ∧
      hsz.toNat ≤ 2 * st.core.cur_vars ∧ FullDenseInv c F0 st ∧
      (∀ i < hsz.toNat,
        (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) ∧
      (FullMem c st ⋆ R) mw)
    (fun Jm hJm => by
      c0_hfast_nogrp
      exact hJm (st1, hsz) mh ⟨Nat.le_of_eq hcv_1.symm, hfu_1,
        by rw [hcv_1]; exact hhsz_1, hinv_1,
        fun i hi => by rw [hcv_1]; exact hhp1 i hi, hmh⟩)
    (fun Jm (st, hsz) mw ⟨hcv_st, hfu_st, hhsz_st, hinv_st, hhp_st, hmw⟩ ihm => ?_)
  c0_hfast_nogrp
  refine wp_join_group (ts := []) (fun _ mEx => mEx = mw) ?_ ?_
  · -- Exit main loop: zero `fheap`/`fpos`, optional VMTF `q_stamp` refresh, return `1ULL`
    rintro _ ⟨⟩ mEx rfl
    clear ihm
    have hstl := hinv_st.1.lengths
    have hst_cv_le := hstl.core_ok.cur_vars_le
    have henl_eq : (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)).toNat =
        2 * st.core.cur_vars := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
    c0_hfast_nogrp
    refine wp_loop_inv (ts := [i64])
      (fun (ci, ()) mf => ci.toNat ≤ 2 * st.core.cur_vars ∧ ∃ hpf psf,
        hpf.length = 2 * c.max_vars ∧ psf.length = 2 * c.max_vars ∧
        (FullMem c
          { st with scratch := { st.scratch with tarjan_mark := hpf, tarjan_reach := psf } }
          ⋆ R) mf)
      (fun (ci, ()) _ => 2 * st.core.cur_vars - ci.toNat)
      (fun J4 hJ4 => by
        c0_hfast_nogrp
        exact hJ4 (0#64, ()) mEx ⟨Nat.zero_le _, st.scratch.tarjan_mark,
          st.scratch.tarjan_reach, hstl.scratch_ok.tarjan_mark_len,
          hstl.scratch_ok.tarjan_reach_len, hmw⟩)
      (fun J4 (ci, ()) mf ⟨hci_le, hpf, psf, hhpf, hpsf, hmf⟩ ih4 => ?_)
    · c0_hfast_nogrp
      · have hci_lt : ci.toNat < 2 * st.core.cur_vars := by
          have h1 := BitVec.lt_def.mp
            (by assumption : ci < (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)))
          rwa [henl_eq] at h1
        have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := fac12a_bv64_add1 (by omega)
        c0_hfast_nogrp
        refine ih4 (ci + 1#64, ()) _ (by dsimp only; rw [hci1]; omega)
          ⟨by rw [hci1]; omega, _, _, ?_, ?_, by assumption⟩ <;>
          simp [hhpf, hpsf]
      · clear ih4
        let stf : FullState :=
          { st with scratch := { st.scratch with tarjan_mark := hpf, tarjan_reach := psf } }
        have hinvf := s12a_dense_set_fheap hinv_st hhpf hpsf
        have hfl := hinvf.1.lengths
        have hstf_cv : stf.core.cur_vars = st.core.cur_vars := rfl
        have hstf_cv_le : stf.core.cur_vars ≤ c.max_vars := hfl.core_ok.cur_vars_le
        c0_hfast_nogrp
        refine wp_join0
          (fun mq => ∃ stq : FullState, FullDenseInv c F0 stq ∧
            init_cv ≤ stq.core.cur_vars ∧ stq.core.fuel = init_fuel ∧
            (FullMem c stq ⋆ R) mq)
          (fun _ mq ⟨stq, hinvq, hcvq, hfuq, hmq⟩ => by
            c0_hfast
            exact hQ 1#64 stq mq hinvq (by rw [← hinit_cv_eq]; exact hcvq)
              (hfuq.trans hinit_fuel_eq) rfl hmq)
          (fun Jv hJv => ?_)
        c0_hfast_nogrp
        · refine wp_loop_inv
            (fun (qidx, qst, ()) mq => qst.toNat ≤ stf.core.cur_vars ∧
              ∃ qs' : List (BitVec 32), qs'.length = c.max_vars ∧
              (FullMem c { stf with scratch := { stf.scratch with q_stamp := qs' } } ⋆ R)
                mq)
            (fun (_, qst, ()) _ => stf.core.cur_vars - qst.toNat)
            (fun J9 hJ9 => by
              c0_hfast_nogrp
              exact hJ9 (stf.scratch.q_first, 0#64, ()) mf
                ⟨Nat.zero_le _, stf.scratch.q_stamp, hfl.scratch_ok.q_stamp_len, hmf⟩)
            (fun J9 (qidx, qst, ()) mq ⟨hqst_le, qs', hqs', hmq⟩ ih9 => ?_)
          · refine wp_join_group (ts := []) (fun _ mq' => mq' = mq) ?_ ?_
            · rintro _ ⟨⟩ mq' rfl
              clear ih9
              c0_hfast_nogrp
              refine wp_join_group (ts := []) (fun _ mq2 => ∃ stq : FullState,
                  FullDenseInv c F0 stq ∧ init_cv ≤ stq.core.cur_vars ∧
                  stq.core.fuel = init_fuel ∧ (FullMem c stq ⋆ R) mq2)
                (fun _ ⟨⟩ mq2 ⟨stq, hinvq, hcvq, hfuq, hmq2⟩ => by
                  c0_hfast
                  exact hJv mq2 ⟨stq, hinvq, hcvq, hfuq, hmq2⟩) ?_
              intro _ hJ2
              c0_hfast_nogrp
              · have hqsi_lt : stf.scratch.q_search_idx.toNat < qs'.length := by
                  have h1 : stf.scratch.q_search_idx.toNat < st.core.cur_vars % 2 ^ 64 :=
                    by assumption
                  rw [Nat.mod_eq_of_lt (by omega)] at h1; rw [hqs']; omega
                c0_hfast_nogrp
                let stq1 : FullState :=
                  { stf with scratch := { stf.scratch with
                    q_stamp := qs', q_cur_stamp := qst,
                    q_search_stamp := BitVec.setWidth 64
                      (qs'[stf.scratch.q_search_idx.toNat]'hqsi_lt) } }
                have hinv_stq1 : FullDenseInv c F0 stq1 :=
                  hinvf.of_safetySlice
                    ⟨hfl.core_ok, { hfl.scratch_ok with q_stamp_len := hqs' }⟩
                    rfl ⟨rfl, rfl⟩
                exact hJ2 () _ ⟨stq1, hinv_stq1, hcv_st, hfu_st, by assumption⟩
              · let stq2 : FullState :=
                  { stf with scratch := { stf.scratch with
                    q_stamp := qs', q_cur_stamp := qst } }
                have hinv_stq2 : FullDenseInv c F0 stq2 :=
                  hinvf.of_safetySlice
                    ⟨hfl.core_ok, { hfl.scratch_ok with q_stamp_len := hqs' }⟩
                    rfl ⟨rfl, rfl⟩
                exact hJ2 () _ ⟨stq2, hinv_stq2, hcv_st, hfu_st, by assumption⟩
            · intro _ hEx
              c0_hfast_nogrp
              · have hqi_lt : qidx.toNat < stf.core.cur_vars := by
                  have h1 : qidx.toNat < st.core.cur_vars % 2 ^ 64 := by assumption
                  rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
                have hqs_lt : qst.toNat < stf.core.cur_vars := by
                  have h1 : qst.toNat < st.core.cur_vars % 2 ^ 64 := by assumption
                  rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
                have hqs_idx : qidx.toNat < qs'.length := by rw [hqs']; omega
                have hqn_idx : qidx.toNat < stf.scratch.q_next.length := by
                  rw [hfl.scratch_ok.q_next_len]; omega
                have hqst1 : (qst + 1#64).toNat = qst.toNat + 1 :=
                  fac12a_bv64_add1 (by omega)
                c0_hfast_nogrp
                refine ih9 (BitVec.setWidth 64 (stf.scratch.q_next[qidx.toNat]'hqn_idx),
                    qst + 1#64, ()) _ (by dsimp only; rw [hqst1]; omega)
                  ⟨by rw [hqst1]; omega, _, ?_, by assumption⟩
                simp [hqs']
              all_goals exact hEx () mq rfl
        · exact hJv _ ⟨stf, hinvf, hcv_st, hfu_st, hmf⟩
  · -- Loop body (`hsz > 0 && cur_vars < max_vars && ant_sz > 0 && oom == 0`)
    intro Jex hJex
    c0_hfast_nogrp
    rotate_left 1
    iterate 4 exact hJex () mw rfl
    have hhsz_pos : 0 < hsz.toNat :=
      by simpa using (by assumption : BitVec.toNat 0 < hsz.toNat)
    have hhsz1 : (hsz - 1#32).toNat = hsz.toNat - 1 := fac12a_bv32_sub1 hhsz_pos
    have hstl := hinv_st.1.lengths
    have hst_cv_le := hstl.core_ok.cur_vars_le
    have hf0_lt : (st.scratch.tarjan_mark[0]'(by
        rw [hstl.scratch_ok.tarjan_mark_len]; omega)).toNat < 2 * st.core.cur_vars := by
      have h := hhp_st 0 hhsz_pos
      rwa [List.getElem?_eq_getElem (by rw [hstl.scratch_ok.tarjan_mark_len]; omega),
        Option.getD_some] at h
    let f0 := st.scratch.tarjan_mark[0]'(by rw [hstl.scratch_ok.tarjan_mark_len]; omega)
    have hf0_lt' : f0.toNat < 2 * st.core.cur_vars := hf0_lt
    have hf0_ps_lt : (BitVec.setWidth 64 f0).toNat < st.scratch.tarjan_reach.length := by
      rw [fid_bv64_32, hstl.scratch_ok.tarjan_reach_len]; omega
    have htm0 : 0 < st.scratch.tarjan_mark.length := by
      rw [hstl.scratch_ok.tarjan_mark_len]; omega
    c0_hfast_nogrp
    let st1a : FullState :=
      { st with scratch := { st.scratch with
        tarjan_reach := st.scratch.tarjan_reach.set (BitVec.setWidth 64 f0).toNat
          0xFFFFFFFF#32 } }
    have hinv1a : FullDenseInv c F0 st1a :=
      s12a_dense_set_fheap hinv_st hstl.scratch_ok.tarjan_mark_len
        (by simp [hstl.scratch_ok.tarjan_reach_len])
    refine wp_join_group (ts := []) (fun _ mf => ∃ st2 : FullState,
        init_cv ≤ st2.core.cur_vars ∧ st2.core.fuel = init_fuel ∧
        st2.core.cur_vars = st.core.cur_vars ∧ FullDenseInv c F0 st2 ∧
        (∀ i < (hsz - 1#32).toNat,
          (st2.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st2.core.cur_vars) ∧
        (FullMem c st2 ⋆ R) mf)
      ?_ ?_
    · rintro _ ⟨⟩ mf ⟨st2, hcv2, hfu2, hcv2_eq, hinv2, hhp2, hmf⟩
      have h2l := hinv2.1.lengths
      have h2_cv_le := h2l.core_ok.cur_vars_le
      have hf0_lt2 : f0.toNat < 2 * st2.core.cur_vars := hcv2_eq ▸ hf0_lt
      have hfv_lt :
          (BitVec.setWidth 64 (f0 >>> (1 : Nat))).toNat < st2.core.flags.length := by
        rw [fid_bv64_32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one,
          h2l.core_ok.flags_len]
        omega
      have hval_lt : (BitVec.setWidth 64 f0).toNat < st2.core.vals.length := by
        rw [fid_bv64_32, h2l.core_ok.vals_len]; omega
      have hdeg_lt : (BitVec.setWidth 64 f0).toNat < st2.core.repr.length := by
        rw [fid_bv64_32, h2l.core_ok.repr_len]; omega
      have hhsz1_lt : (hsz - 1#32).toNat < hsz.toNat := by omega
      c0_hfast_nogrp
      refine wp_join_group (ts := [i32])
        (fun (fbit, ()) mf0 =>
          (fbit = 32#32 ∨ fbit = 64#32) ∧ (FullMem c st2 ⋆ R) mf0)
        ?_ (fun _ hJfb => by
          c0_hfast_nogrp
          · exact hJfb (64#32, ()) mf ⟨Or.inr rfl, hmf⟩
          · exact hJfb (32#32, ()) mf ⟨Or.inl rfl, hmf⟩)
      rintro _ ⟨fbit, ⟨⟩⟩ mf ⟨_, hmf⟩
      have hdec_hsz : ∀ st' : FullState, st'.core.cur_vars = st.core.cur_vars →
          (c.max_vars - st'.core.cur_vars) * (2 * c.max_vars + 1) + (hsz - 1#32).toNat <
            (c.max_vars - st.core.cur_vars) * (2 * c.max_vars + 1) + hsz.toNat :=
        fun st' h => by rw [h, hhsz1]; omega
      have hhsz1_le : (hsz - 1#32).toNat ≤ 2 * st2.core.cur_vars := by
        rw [hcv2_eq, hhsz1]; omega
      have h_jm_st2a : ∀ {fl' : List (BitVec 32)} {m' : Mem 64},
          (FullMem c { st2 with core := { st2.core with flags := fl' } } ⋆ R) m' →
          fl'.length = c.max_vars →
          Jm (hsz - 1#32, ()) m' := fun {fl' m'} hm' hlen =>
        ihm ({ st2 with core := { st2.core with flags := fl' } }, hsz - 1#32) m'
          (hdec_hsz _ hcv2_eq)
          ⟨hcv2, hfu2, hhsz1_le, s12a_dense_set_flags hinv2 hlen, hhp2, hm'⟩
      c0_hfast_nogrp
      all_goals
        try
          (c0_hfast_nogrp
           exact ihm (st2, hsz - 1#32) mf (hdec_hsz st2 hcv2_eq)
            ⟨hcv2, hfu2, hhsz1_le, hinv2, hhp2, hmf⟩)
      all_goals
        try
          (c0_hfast_nogrp
           refine h_jm_st2a hm ?_
           rw [List.length_set]
           exact h2l.core_ok.flags_len)
      · have hfl_ex : ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
            (FullMem c { st2 with core := { st2.core with flags := fl' } } ⋆ R) m := by
          refine ⟨_, ?_, hm⟩
          rw [List.length_set]
          exact h2l.core_ok.flags_len
        obtain ⟨fl', hfl'_len, hm2a⟩ := hfl_ex
        let st2a : FullState := { st2 with core := { st2.core with flags := fl' } }
        have hinv2a : FullDenseInv c F0 st2a := s12a_dense_set_flags hinv2 hfl'_len
        refine wp_join_group (ts := [i32]) Jm
          (fun _ p_j m_j h_j => by c0_hfast_nogrp; exact h_j)
          (fun _ hJs => ?_)
        refine wp_call_of_spec _ _ (hTryLit _ _ _ _ ?_)
        refine ⟨c, F0, st2a, R, rfl, hinv2a, hf0_lt2, hm2a, ?_⟩
        · intro ok3 st3 m3 hinv3 hcv3_le hcv3_lt hcom3 hfu3 htm3 _ hm3
          c0_hsplit
          · have hok_t : ok3 = true := by assumption
            have hcv3_gt : st2.core.cur_vars < st3.core.cur_vars := hcv3_lt hok_t
            obtain ⟨bkNat, hbk⟩ := hcom3 hok_t
            have h3l := hinv3.1.lengths
            have h3_cv_le := h3l.core_ok.cur_vars_le
            have h3_cv32 : 2 * c.max_vars < 2 ^ 30 := by omega
            c0_hfast_nogrp
            refine s12a_call_steps_cap hSteps fun sc_b hsc_b => ?_
            c0_hfast_nogrp
            -- Read res_sz = bkNat < fidStepsCap c.scratch_cap
            have hbk_sc : bkNat < fidStepsCap c.scratch_cap := hbk.1
            have hbk_eq : (BitVec.setWidth 32 st3.scratch.res_sz).toNat = bkNat := by
              rw [hbk.2.1, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by have := fidStepsCap_le_256 c.scratch_cap; omega),
                Nat.mod_eq_of_lt (by have := fidStepsCap_le_256 c.scratch_cap; omega)]
            have hq0_bnd : bkNat + 1 < 2 ^ 32 := by
              have := fidStepsCap_le_256 c.scratch_cap; omega
            have hcnl_eq : (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat =
                2 * st3.core.cur_vars := by
              rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq,
                Nat.mod_eq_of_lt (by omega)]; omega
            -- Phase A: collect unique touched literals
            refine wp_loop_inv
              (fun (nt, qs_idx, ()) mA => qs_idx.toNat ≤ bkNat + 1 ∧ ∃ tmk tlits,
                S12aTouchInv c st3 R nt tmk tlits mA)
              (fun (_, qs_idx, ()) _ => qs_idx.toNat)
              (fun Ja hJa => by
                c0_hfast_nogrp
                exact hJa (0#64, BitVec.setWidth 32 st3.scratch.res_sz + 1#32, ()) m3
                  ⟨by rw [fac12a_bv32_add1 (by rw [hbk_eq]; omega), hbk_eq]; omega,
                   st3.core.lit_mark, st3.scratch.work_stk2,
                   h3l.core_ok.lit_mark_len, h3l.scratch_ok.work_stk2_len,
                   Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _),
                   fun l hl hnz => absurd (hinv3.2.1.2 l hl) hnz, hm3⟩)
              (fun Ja (nt, qs_idx, ()) mA
                  ⟨hqs_le, tmk, tlits, htmk_l, htlits_l, hnt_le, htlits_b, hcov, hmA⟩
                  iha => ?_)
            · c0_hfast_nogrp
              · have hqs_pos : 0 < qs_idx.toNat := by
                  first
                  | exact Nat.pos_of_ne_zero
                      (fun h => (by assumption : qs_idx ≠ 0#32) (BitVec.eq_of_toNat_eq h))
                  | simpa using BitVec.lt_def.mp (by assumption : 0#32 < qs_idx)
                have hqs1 : (qs_idx - 1#32).toNat = qs_idx.toNat - 1 :=
                  fac12a_bv32_sub1 hqs_pos
                have hrow := hbk.2.2 (qs_idx - 1#32).toNat (by omega)
                have hsc_lt : (qs_idx - 1#32).toNat < st3.scratch.scratch_buf.length := by
                  rw [h3l.scratch_ok.scratch_buf_len]
                  have := fidStepsCap_mul4_le c.scratch_cap; have := hbk.1; omega
                have hfac_lt : (st3.scratch.scratch_buf[
                    (qs_idx - 1#32).toNat]'hsc_lt).toNat < 2 * st3.core.cur_vars := by
                  have h := hrow.1
                  rwa [List.getElem?_eq_getElem hsc_lt, Option.getD_some] at h
                have hfneg_lt : ((st3.scratch.scratch_buf[
                    (qs_idx - 1#32).toNat]'hsc_lt) ^^^ 1#32).toNat <
                    2 * st3.core.cur_vars := by
                  let fv := st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt
                  have h1 : (fv ^^^ 1#32).toNat =
                      2 * (fv.toNat / 2) + (1 - fv.toNat % 2) := by
                    rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
                    apply Nat.eq_of_testBit_eq
                    intro i
                    rw [Nat.testBit_xor]
                    cases i with
                    | zero =>
                      simp only [Nat.testBit_zero]
                      rcases Nat.mod_two_eq_zero_or_one fv.toNat with h | h <;> simp [h]
                    | succ k =>
                      simp only [Nat.testBit_succ]
                      have h1_sh : 1 / 2 = 0 := by decide
                      have h1_rhs : (2 * (fv.toNat / 2) + (1 - fv.toNat % 2)) / 2 =
                          fv.toNat / 2 := by omega
                      simp [Nat.testBit, Nat.shiftRight_eq_div_pow,
                        Nat.div_div_eq_div_mul, h1_rhs, h1_sh]
                  have hfv_lt : fv.toNat < 2 * st3.core.cur_vars := hfac_lt
                  change (fv ^^^ 1#32).toNat < 2 * st3.core.cur_vars
                  omega
                c0_hfast_nogrp
                -- Push `factor`
                refine wp_join_group (ts := [i64]) (fun (nt1, ()) mP1 => ∃ tmk1 tlits1,
                    S12aTouchInv c st3 R nt1 tmk1 tlits1 mP1) ?_ ?_
                · rintro _ ⟨nt1, ⟨⟩⟩ mP1
                    ⟨tmk1, tlits1, htmk1_l, htlits1_l, hnt1_le, htlits1_b, hcov1, hmP1⟩
                  c0_hfast_nogrp
                  -- Push `fneg`
                  refine wp_join_group (ts := [i64]) (fun (nt2, ()) mP2 => ∃ tmk2 tlits2,
                      S12aTouchInv c st3 R nt2 tmk2 tlits2 mP2) ?_ ?_
                  · rintro _ ⟨nt2, ⟨⟩⟩ mP2
                      ⟨tmk2, tlits2, htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩
                    have hro_idx : (sc_b + (qs_idx - 1#32)).toNat =
                        sc_b.toNat + (qs_idx - 1#32).toNat := by
                      rw [BitVec.toNat_add, hsc_b, Nat.mod_eq_of_lt (by
                        have := fidStepsCap_le_256 c.scratch_cap; omega)]
                    have hro_sc : (BitVec.setWidth 64 (sc_b + (qs_idx - 1#32))).toNat <
                        st3.scratch.scratch_buf.length := by
                      rw [fid_bv64_32, hro_idx, h3l.scratch_ok.scratch_buf_len]
                      have := fidStepsCap_mul4_le c.scratch_cap; have := hbk.1; omega
                    have hqn_idx : (2#32 * sc_b + (qs_idx - 1#32)).toNat =
                        2 * sc_b.toNat + (qs_idx - 1#32).toNat := by
                      rw [BitVec.toNat_add, BitVec.toNat_mul, hsc_b,
                        show (2#32 : BitVec 32).toNat = 2 from rfl,
                        Nat.mod_eq_of_lt (by
                          have := fidStepsCap_le_256 c.scratch_cap; omega),
                        Nat.mod_eq_of_lt (by
                          have := fidStepsCap_le_256 c.scratch_cap; omega)]
                    have hqn_sc : (BitVec.setWidth 64
                        (2#32 * sc_b + (qs_idx - 1#32))).toNat <
                        st3.scratch.scratch_buf.length := by
                      rw [fid_bv64_32, hqn_idx, h3l.scratch_ok.scratch_buf_len]
                      have := fidStepsCap_mul4_le c.scratch_cap; have := hbk.1; omega
                    let ro_bv := st3.scratch.scratch_buf[(BitVec.setWidth 64
                      (sc_b + (qs_idx - 1#32))).toNat]'hro_sc
                    let qn_bv := st3.scratch.scratch_buf[(BitVec.setWidth 64
                      (2#32 * sc_b + (qs_idx - 1#32))).toNat]'hqn_sc
                    have hroqn_bnd : ro_bv.toNat + qn_bv.toNat ≤ c.scratch_cap := by
                      have h := hrow.2.1
                      dsimp only [ro_bv, qn_bv]
                      simp only [fid_bv64_32, hro_idx, hqn_idx, hsc_b]
                      rw [List.getElem?_eq_getElem (by
                            rw [h3l.scratch_ok.scratch_buf_len]
                            have := fidStepsCap_mul4_le c.scratch_cap; omega),
                          List.getElem?_eq_getElem (by
                            rw [h3l.scratch_ok.scratch_buf_len]
                            have := fidStepsCap_mul4_le c.scratch_cap; omega),
                          Option.getD_some, Option.getD_some] at h
                      exact h
                    c0_hfast_nogrp
                    refine fac12a_qi_scan_wp hmx hscr_b hinv3 hcnl_eq hroqn_bnd ?_
                      ⟨htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩
                      (fun ntQ mQ ⟨tmkQ, tlitsQ, hT⟩ =>
                        iha (ntQ, qs_idx - 1#32, ()) mQ (by dsimp only; rw [hqs1]; omega)
                          ⟨by rw [hqs1]; omega, tmkQ, tlitsQ, hT⟩)
                    · intro qi_n hqi_n
                      change qi_n < st3.scratch.scratch_buf[
                        (2#32 * sc_b + (qs_idx - 1#32)).toNat].toNat at hqi_n
                      have hro_sc' : fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat <
                          st3.scratch.scratch_buf.length := by
                        rw [← hsc_b, ← hro_idx, ← fid_bv64_32]; exact hro_sc
                      have hqn_sc' : 2 * fidStepsCap c.scratch_cap +
                          (qs_idx - 1#32).toNat < st3.scratch.scratch_buf.length := by
                        rw [← hsc_b, ← hqn_idx, ← fid_bv64_32]; exact hqn_sc
                      have heq_ro : ro_bv.toNat = (st3.scratch.scratch_buf[
                          fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat]?.getD
                          0#32).toNat := by
                        simp only [ro_bv, fid_bv64_32, hro_idx, hsc_b]
                        rw [List.getElem?_eq_getElem hro_sc', Option.getD_some]
                      have hqi_row : qi_n < (st3.scratch.scratch_buf[
                          2 * fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat]?.getD
                          0#32).toNat := by
                        rw [List.getElem?_eq_getElem hqn_sc', Option.getD_some]
                        simpa only [hqn_idx, hsc_b] using hqi_n
                      have h := hrow.2.2 qi_n hqi_row
                      first
                      | rwa [← heq_ro] at h
                      | (have heq_ro' : (st3.scratch.scratch_buf[
                             (sc_b + (qs_idx - 1#32)).toNat]'(by
                               rw [hro_idx, hsc_b]; exact hro_sc')).toNat =
                             (st3.scratch.scratch_buf[
                               fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat]?.getD
                               0#32).toNat := by
                           simp only [List.getElem?_eq_getElem hro_sc', Option.getD_some,
                             hro_idx, hsc_b]
                         change Step7RowRefOk st3 (st3.scratch.scratch_buf[
                           (st3.scratch.scratch_buf[
                             (sc_b + (qs_idx - 1#32)).toNat]'(by
                               rw [hro_idx, hsc_b]; exact hro_sc')).toNat +
                             qi_n]?.getD 0#32)
                         rwa [← heq_ro'] at h)
                  · -- `fneg` push branches
                    intro Jp2 hJp2
                    c0_hfast_nogrp
                    · have hlm_fn : (BitVec.setWidth 64
                          ((st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt) ^^^
                            1#32)).toNat < tmk1.length := by
                        rw [fid_bv64_32, htmk1_l]
                        exact Nat.lt_of_lt_of_le hfneg_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                      c0_hfast_nogrp
                      · have hnt1_lt : nt1.toNat < 2 * st3.core.cur_vars := by
                          have h1 : nt1.toNat <
                              (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat := by
                            assumption
                          rw [hcnl_eq] at h1; exact h1
                        have hnt1_1 : (nt1 + 1#64).toNat = nt1.toNat + 1 :=
                          fac12a_bv64_add1
                            (Nat.lt_trans (Nat.add_lt_add_right hnt1_lt 1)
                              (Nat.lt_of_le_of_lt
                                (Nat.add_le_add_right
                                  (Nat.mul_le_mul_left 2 h3_cv_le) 1)
                                (Nat.lt_trans (Nat.add_lt_add_right h3_cv32 1)
                                  (by decide))))
                        have hws_nt1 : nt1.toNat < tlits1.length := by
                          rw [htlits1_l]
                          exact Nat.lt_of_lt_of_le hnt1_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                        c0_hfast_nogrp
                        have hps1 := s12a_push_touched_step h3_cv_le htmk1_l htlits1_l
                          hfneg_lt hnt1_lt hnt1_1 htlits1_b hcov1
                        exact hJp2 (nt1 + 1#64, ()) _ ⟨_, _,
                          hps1.1, hps1.2.1, hps1.2.2.1, hps1.2.2.2.1, hps1.2.2.2.2,
                          by assumption⟩
                      all_goals
                        exact hJp2 (nt1, ()) mP1 ⟨tmk1, tlits1, htmk1_l, htlits1_l, hnt1_le,
                          htlits1_b, hcov1, hmP1⟩
                    · exact hJp2 (nt1, ()) mP1 ⟨tmk1, tlits1, htmk1_l, htlits1_l, hnt1_le,
                        htlits1_b, hcov1, hmP1⟩
                · -- `factor` push branches
                  intro Jp1 hJp1
                  c0_hfast_nogrp
                  · have hlm_f : (BitVec.setWidth 64
                        (st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt)).toNat <
                        tmk.length := by
                      rw [fid_bv64_32, htmk_l]
                      exact Nat.lt_of_lt_of_le hfac_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                    c0_hfast_nogrp
                    · have hnt_lt : nt.toNat < 2 * st3.core.cur_vars := by
                        have h1 : nt.toNat <
                            (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat := by
                          assumption
                        rw [hcnl_eq] at h1; exact h1
                      have hnt1 : (nt + 1#64).toNat = nt.toNat + 1 :=
                        fac12a_bv64_add1
                          (Nat.lt_trans (Nat.add_lt_add_right hnt_lt 1)
                            (Nat.lt_of_le_of_lt
                              (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h3_cv_le) 1)
                              (Nat.lt_trans (Nat.add_lt_add_right h3_cv32 1) (by decide))))
                      have hws_nt : nt.toNat < tlits.length := by
                        rw [htlits_l]
                        exact Nat.lt_of_lt_of_le hnt_lt (Nat.mul_le_mul_left 2 h3_cv_le)
                      c0_hfast_nogrp
                      have hpsF := s12a_push_touched_step h3_cv_le htmk_l htlits_l
                        hfac_lt hnt_lt hnt1 htlits_b hcov
                      exact hJp1 (nt + 1#64, ()) _ ⟨_, _,
                        hpsF.1, hpsF.2.1, hpsF.2.2.1, hpsF.2.2.2.1, hpsF.2.2.2.2,
                        by assumption⟩
                    all_goals
                      exact hJp1 (nt, ()) mA
                        ⟨tmk, tlits, htmk_l, htlits_l, hnt_le, htlits_b, hcov, hmA⟩
                  · exact hJp1 (nt, ()) mA ⟨tmk, tlits, htmk_l, htlits_l, hnt_le, htlits_b,
                      hcov, hmA⟩
              · -- Exit Phase A: Clear loop (`ui < nt`) then Phase B `upd_lit` loop
                clear iha
                c0_hfast_nogrp
                have hcv3_ge2 : st2.core.cur_vars ≤ st3.core.cur_vars := hcv3_le
                have htm2a : st2a.scratch.tarjan_mark = st2.scratch.tarjan_mark := rfl
                have hhsz'_le : (hsz - 1#32).toNat ≤ 2 * st3.core.cur_vars := by omega
                have hhp3 : ∀ i < (hsz - 1#32).toNat,
                    (st3.scratch.tarjan_mark[i]?.getD 0#32).toNat <
                      2 * st3.core.cur_vars := fun i hi => by
                  rw [htm3, htm2a]; have := hhp2 i hi; omega
                refine fac12a_clear_upd_wp hUpd hinv3 htmk_l htlits_l hnt_le htlits_b hcov
                  hhsz'_le hhp3 hmA fun hsz_u mU ⟨st_end, hinv_end, hcv_end, hfu_end,
                    hhsz_end, hhp_end, hm_end⟩ => ?_
                exact hJs (hsz_u, ()) mU (ihm (st_end, hsz_u) mU
                  (fac12a_lex_dec_cv (by dsimp only; rw [hcv_end, ← hcv2_eq]; exact hcv3_gt)
                    hinv_end.1.lengths.core_ok.cur_vars_le (by dsimp only; omega))
                  ⟨by omega, hfu_end.trans (hfu3.trans hfu2), hhsz_end,
                   hinv_end, hhp_end, hm_end⟩)
          · c0_hfast_nogrp
            refine hJs (hsz - 1#32, ()) m3 (ihm (st3, hsz - 1#32) m3 ?_ ?_)
            · have hcv3_ge2 : st2.core.cur_vars ≤ st3.core.cur_vars := hcv3_le
              rcases Nat.lt_or_eq_of_le hcv3_ge2 with hcv3_gt | hcv3_eq
              · exact fac12a_lex_dec_cv (by dsimp only; rw [← hcv2_eq]; exact hcv3_gt)
                  hinv3.1.lengths.core_ok.cur_vars_le (by dsimp only; omega)
              · exact hdec_hsz st3 (by rw [← hcv3_eq, hcv2_eq])
            · have hcv3_ge2 : st2.core.cur_vars ≤ st3.core.cur_vars := hcv3_le
              have htm2a : st2a.scratch.tarjan_mark = st2.scratch.tarjan_mark := rfl
              refine ⟨Nat.le_trans hcv2 hcv3_ge2, hfu3.trans hfu2, by omega, hinv3, ?_, hm3⟩
              intro i hi
              rw [htm3, htm2a]
              have := hhp2 i hi
              omega
    · -- `if (hsz > 0)` swap + `full_fheap_down_fid`
      intro Jf hJf
      exact fac12a_fheap_pop_wp hDown hhsz_pos hhsz1 hhsz_st hcv_st hfu_st hinv1a
        rfl rfl hhp_st (by assumption) hJf

end LeanQbe.T.Examples.Kissat.FullFidelityStep12A

end
