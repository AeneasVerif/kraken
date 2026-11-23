module

public import LeanQbe.T.Examples.Kissat.FullM7BvaFactorProof0
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
public import LeanQbe.T.Examples.Kissat.FullM5
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Wave-4F `FullM7BvaFactor` WP Soundness & Closed `270`-Fn Assembly

Proves:
1. `full_factor_m7_wp`: parametric `(Γ : Env)` WP contract for `full_factor_m7_body` against
   `FullBvaHeap.fullFactorHeapSpec` (handling `wvec[2*u+1] > 1` precheck, `L_16` touched-lit
   heap sift/reschedule, heap zeroing, and `L_9` VMTF stamp renumber).
2. Standalone `9`-row `m7BvaFactorSpecTable`, `m7BvaFactorEnv`, unconditional
   `m7BvaFactor_moduleOk : ModuleOk m7BvaFactorEnv m7BvaFactorModule`, and concrete `Mem 64`
   non-vacuity (`nv_m7_init_fresh_var`, `nv_m7_bva_try_lit`, `nv_m7_factor`).
3. Closed `270`-function `FullM5`-spliced `m7BvaFullModule`, `m7BvaFull_acyclic`,
   `m7BvaFull_fns_wf`, and parametric `m7BvaFull_moduleOk_of`.
-/

set_option autoImplicit false

public section

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

namespace LeanQbe.T.Examples.Kissat.FullM7BvaFactor

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullBvaHeap FullBvaHeapTactics FullBvaHeapHelpers
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. FHeap Separation Focusing & State-Preservation Helpers -/

private def FullMemFheapRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
  FullCoreU32A c s.core ⋆ array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
  array (t := i32) c.pFrameDec s.core.frame_dec ⋆ array (t := i32) c.pRepr s.core.repr ⋆
  array (t := i32) c.pMinStk s.core.min_stk ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  array (t := i32) c.pWsort s.scratch.wsort ⋆ array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
  array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

private theorem focus_fheap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
      array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
      array (t := i32) c.pWvec s.core.wvec ⋆ (FullMemFheapRest c s ⋆ R)) m := by
  have h0 : (FullMem c s ⋆ R) =
      (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array (t := i32) c.pWvec s.core.wvec ⋆ (FullMemFheapRest c s ⋆ R)) := by
    unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs FullMemFheapRest
    ac_rfl
  rw [h0] at hm; exact hm

private theorem unfocus_fheap {c : FullCfg} {s : FullState} {hp' ps' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTarjanMark hp' ⋆
      array (t := i32) c.pTarjanReach ps' ⋆
      array (t := i32) c.pWvec s.core.wvec ⋆ (FullMemFheapRest c s ⋆ R)) m) :
    (FullMem c
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆ R) m := by
  have h0 : (FullMem c
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆ R) =
      (array (t := i32) c.pTarjanMark hp' ⋆
        array (t := i32) c.pTarjanReach ps' ⋆
        array (t := i32) c.pWvec s.core.wvec ⋆ (FullMemFheapRest c s ⋆ R)) := by
    unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs FullMemFheapRest
    ac_rfl
  rw [h0]; exact hm

private def setWtp (s : FullState) (ws hp ps : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with wsort := ws, tarjan_mark := hp, tarjan_reach := ps } }

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
  have ⟨F_cur, hinvW⟩ := hinv.exists_witness
  exact (FullBvaHeap.fullDenseInvW_set_flags hinvW hfl).toDense

private theorem fullDenseInv_set_qstamp {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {qs' : List (BitVec 32)} {qcs' qss' : BitVec 64}
    (hqs : qs'.length = c.max_vars) :
    FullDenseInv c F0
      { s with scratch :=
        { s.scratch with q_stamp := qs', q_cur_stamp := qcs', q_search_stamp := qss' } } :=
  hinv.of_safetySlice
    ⟨hinv.1.lengths.core_ok, { hinv.1.lengths.scratch_ok with q_stamp_len := hqs }⟩
    rfl ⟨rfl, rfl⟩

private theorem fheap_push_pre_lt {hp : List (BitVec 32)} {hlen lit lim : Nat}
    (hlt : lit < lim) (hprev : ∀ k < hlen, (hp[k]?.getD 0#32).toNat < lim) :
    ∀ i ≤ hlen, ((hp.set hlen (BitVec.ofNat 32 lit))[i]?.getD 0#32).toNat < lim := by
  intro i hi
  by_cases heq : i = hlen
  · rcases Nat.lt_or_ge hlen hp.length with h1 | h1
    · rw [heq, List.getElem?_set_self h1, Option.getD_some, BitVec.toNat_ofNat]
      exact lt_of_le_of_lt (Nat.mod_le _ _) hlt
    · rw [heq, List.getElem?_eq_none (by rw [List.length_set]; exact h1), Option.getD_none]
      simp only [BitVec.toNat_ofNat]; omega
  · have hlt_i : i < hlen := Nat.lt_of_le_of_ne hi heq
    rw [List.getElem?_set_ne (Ne.symm heq)]
    exact hprev i hlt_i

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
  · obtain ⟨j, hj, heq⟩ := hperm k hle
    rw [heq]; exact hpre j hj
  · have hgt : p < k := Nat.lt_of_not_le hle
    rw [hfix k hgt]; exact hprev k hk hgt

private theorem fheap_down_post_lt {hp_pre hp' : List (BitVec 32)} {n lim : Nat}
    (hpre : ∀ i < n, (hp_pre[i]?.getD 0#32).toNat < lim)
    (hperm : ∀ i < n, ∃ j < n, hp'[i]? = hp_pre[j]?) :
    ∀ k < n, (hp'[k]?.getD 0#32).toNat < lim := by
  intro k hk
  obtain ⟨j, hj, heq⟩ := hperm k hk
  rw [heq]; exact hpre j hj

private theorem m7_bv64_32 (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_trans (BitVec.isLt x) (by decide))

private theorem m7_pl_bv32_toNat {vi : BitVec 64} {cv : Nat}
    (hvi : vi.toNat < cv) (hcv : 2 * cv < 2 ^ 32) :
    (BitVec.setWidth 32 (vi <<< (1 : Nat))).toNat = 2 * vi.toNat := by
  have hsh : (vi <<< (1 : Nat)).toNat = 2 * vi.toNat := by
    simp [BitVec.toNat_shiftLeft]; omega
  rw [BitVec.toNat_setWidth, hsh]; exact Nat.mod_eq_of_lt (by omega)

private theorem m7_nl_bv32_toNat {vi : BitVec 64} {cv : Nat}
    (hvi : vi.toNat < cv) (hcv : 2 * cv < 2 ^ 32) :
    (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32).toNat = 2 * vi.toNat + 1 := by
  have hsh : (vi <<< (1 : Nat)).toNat = 2 * vi.toNat := by
    simp [BitVec.toNat_shiftLeft]; omega
  have hsw : (BitVec.setWidth 32 (vi <<< (1 : Nat))).toNat = 2 * vi.toNat := by
    rw [BitVec.toNat_setWidth, hsh]; exact Nat.mod_eq_of_lt (by omega)
  rw [FullBvaFwdTactics.bv32_or1_of_even (by omega), hsw]

private theorem m7_nl_32 {vi : BitVec 64} {cv : Nat}
    (hvi : vi.toNat < cv) (hcv : 2 * cv < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat =
      2 * vi.toNat + 1 := by
  have h := m7_nl_bv32_toNat hvi hcv
  rw [BitVec.toNat_setWidth, h]; exact Nat.mod_eq_of_lt (by omega)

private theorem m7_nl_wvec_lt {vi : BitVec 64} (len : Nat) {cv : Nat}
    (hvi : vi.toNat < cv) (hcv : 2 * cv < 2 ^ 32) (hlen : 4 * cv ≤ len) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32) <<< (1 : Nat) +
      1#64).toNat < len := by
  have h := m7_nl_32 hvi hcv
  have hsh :
      (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32) <<< (1 : Nat)).toNat =
        2 * (2 * vi.toNat + 1) := by
    rw [BitVec.toNat_shiftLeft, h, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm _ 2]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, hsh]; simp only [BitVec.toNat_ofNat]
  have hlt : 2 * (2 * vi.toNat + 1) + 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]; omega

private theorem m7_bv32_add1_toNat {x : BitVec 32} {n : Nat}
    (hx : x.toNat < n) (hn : n < 2 ^ 32) : (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have hlt : x.toNat + 1 < 2 ^ 32 := by omega
  exact Nat.mod_eq_of_lt hlt

private theorem m7_bv64_add1_toNat {x : BitVec 64} {n : Nat}
    (hx : x.toNat < n) (hn : n < 2 ^ 64) : (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl]
  have hlt : x.toNat + 1 < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt hlt

private theorem m7_bv32_sub1_toNat {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  have hle : (1#32).toNat ≤ x.toNat := hx
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]; rfl

private theorem m7_bv64_sub1_toNat {x : BitVec 64} (hx : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hle : (1#64).toNat ≤ x.toNat := hx
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]; rfl

private theorem m7_bud_dec_thlen {cbud : BitVec 64} {maxv chlen thlen : Nat}
    (hpos : 0 < cbud.toNat) (hth : thlen ≤ 2 * maxv) :
    (cbud - 1#64).toNat * (2 * maxv + 1) + thlen < cbud.toNat * (2 * maxv + 1) + chlen := by
  have h1 : (cbud - 1#64).toNat = cbud.toNat - 1 := m7_bv64_sub1_toNat hpos
  have hsub :
      (cbud.toNat - 1) * (2 * maxv + 1) + (2 * maxv + 1) = cbud.toNat * (2 * maxv + 1) := by
    calc (cbud.toNat - 1) * (2 * maxv + 1) + (2 * maxv + 1)
        = (cbud.toNat - 1 + 1) * (2 * maxv + 1) := (Nat.add_one_mul _ _).symm
      _ = cbud.toNat * (2 * maxv + 1) := by rw [Nat.sub_add_cancel hpos]
  rw [h1]; omega

private theorem m7_fl_lit_lt {lit : BitVec 32} {len cv : Nat}
    (hlt : lit.toNat < 2 * cv) (hlen : cv ≤ len) :
    (BitVec.setWidth 64 (lit >>> (1 : Nat))).toNat < len := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hlt64 : lit.toNat / 2 < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _)
    (lt_trans (BitVec.isLt lit) (by decide))
  rw [Nat.mod_eq_of_lt hlt64]; omega

private theorem m7_wvec_lit_lt {lit : BitVec 32} {len cv : Nat}
    (hlt : lit.toNat < 2 * cv) (hlen : 4 * cv ≤ len) :
    (BitVec.setWidth 64 lit <<< (1 : Nat) + 1#64).toNat < len := by
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, m7_bv64_32, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.pow_one]
  have hlt32 : lit.toNat < 2 ^ 32 := BitVec.isLt lit
  have h1 : lit.toNat * 2 < 2 ^ 64 := by omega
  have h2 : lit.toNat * 2 + 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]; omega

private theorem m7_wp_call_fheap_up {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hUp : ∀ args m Q X, fullFheapUpSpec args m Q X →
      Γ "full_fheap_up" [i64, i64, i64, i32] [] args m Q X)
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
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32]) "full_fheap_up"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pWvec, Arg.var idx, ()) k) m := by
  have hl := hinv.1.lengths
  have hcv_le := hl.core_ok.cur_vars_le
  have hmax31 : c.max_vars < 2 * 268435456 := hmaxv
  refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
  refine ⟨2 * st.core.cur_vars, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.wvec,
    FullMemFheapRest c st ⋆ R,
    by rw [hl.scratch_ok.tarjan_mark_len]; omega,
    by rw [hl.scratch_ok.tarjan_reach_len]; omega,
    by rw [hl.core_ok.wvec_len]; omega,
    by omega,
    by change idx.toNat < 2 * st.core.cur_vars; exact Nat.lt_of_lt_of_le hidx_lt hhlen_le,
    fun i hi => hhpp i (Nat.lt_of_le_of_lt hi hidx_lt),
    focus_fheap hm,
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
  exact hk st' m' hinv' rfl rfl hhp'2 (unfocus_fheap hm')

private theorem m7_wp_call_fheap_down {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hDown : ∀ args m Q X, fullFheapDownSpec args m Q X →
      Γ "full_fheap_down" [i64, i64, i64, i32, i32] [] args m Q X)
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
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32, i32]) "full_fheap_down"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pWvec,
       Arg.var idx, Arg.var n, ()) k) m := by
  have hl := hinv.1.lengths
  have hcv_le := hl.core_ok.cur_vars_le
  have hmax31 : c.max_vars < 2 * 268435456 := hmaxv
  refine wp_call_of_spec _ _ (hDown _ _ _ _ ?_)
  refine ⟨2 * st.core.cur_vars, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.wvec,
    FullMemFheapRest c st ⋆ R,
    by rw [hl.scratch_ok.tarjan_mark_len]; omega,
    by rw [hl.scratch_ok.tarjan_reach_len]; omega,
    by rw [hl.core_ok.wvec_len]; omega,
    by omega, hidx_lt, hn_le, hhpp, focus_fheap hm,
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
  exact hk st' m' hinv' rfl rfl hhp'2 (unfocus_fheap hm')

/-! ## 2. `full_factor_m7_wp` Soundness Proof -/

theorem full_factor_m7_wp (Γ : Env)
    (hUp : ∀ args m Q X, fullFheapUpSpec args m Q X →
      Γ "full_fheap_up" [i64, i64, i64, i32] [] args m Q X)
    (hDown : ∀ args m Q X, fullFheapDownSpec args m Q X →
      Γ "full_fheap_down" [i64, i64, i64, i32, i32] [] args m Q X)
    (hTryLit : ∀ args m Q X, fullBvaTryLitHeapSpec args m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] args m Q X)
    (args : Tup Val [i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hs : fullFactorHeapSpec args m Q X) :
    Func.wp Γ full_factor_m7_body args m Q X := by
  rcases args with ⟨h, budget, ⟨⟩⟩
  rcases hs with ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hlen := hinv.1.lengths
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmaxv := c.hmaxv
  have hmax_lt32 : c.max_vars < 2 ^ 29 := by
    change c.max_vars < 2 * 268435456 at hmaxv; omega
  have hmax_lt64 : c.max_vars < 2 ^ 64 := by omega
  have hcv_lt32 : 2 * s.core.cur_vars < 2 ^ 32 := by omega
  have hcv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 := by omega
  c0_hfast
  · exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  · exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  · exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  · -- L_0: zero `wsort`, `tarjan_mark` (`fheap`), set `tarjan_reach` (`fpos`) to `0xFFFFFFFF`
    refine wp_loop_inv
      (fun (zi, ()) mz => ∃ wsi hpi psi,
        zi.toNat ≤ 2 * s.core.cur_vars ∧
        wsi.length = 2 * c.max_vars ∧ hpi.length = 2 * c.max_vars ∧
        psi.length = 2 * c.max_vars ∧
        (FullMem c (setWtp s wsi hpi psi) ⋆ R) mz)
      (fun (zi, ()) _ => 2 * s.core.cur_vars - zi.toNat)
      (fun J hJ => by
        c0_hfast
        exact hJ (0#64, ()) m ⟨_, _, _, Nat.zero_le _, hlen.scratch_ok.wsort_len,
          hlen.scratch_ok.tarjan_mark_len, hlen.scratch_ok.tarjan_reach_len, hm⟩)
      (fun J p mz hloop hrec => ?_)
    rcases p with ⟨zi, ⟨⟩⟩
    rcases hloop with ⟨wsi, hpi, psi, hzi_le, hwsi_l, hhpi_l, hpsi_l, hmz⟩
    dsimp only [setWtp] at hmz
    c0_hfast
    · have hzi_lt : zi.toNat < 2 * s.core.cur_vars := by
        simpa [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hcv_lt64] using hc
      have h1 : zi.toNat < wsi.length := by omega
      have h2 : zi.toNat < hpi.length := by omega
      have h3 : zi.toNat < psi.length := by omega
      c0_hfast
      have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := m7_bv64_add1_toNat hzi_lt (by omega)
      refine hrec (zi + 1#64, ()) _ (by dsimp only; rw [hzi1]; omega)
        ⟨wsi.set zi.toNat 0#32, hpi.set zi.toNat 0#32, psi.set zi.toNat 0xFFFFFFFF#32,
          by rw [hzi1]; omega, by simpa using hwsi_l, by simpa using hhpi_l,
          by simpa using hpsi_l, ?_⟩
      assumption
    · have hstz_inv : FullDenseInv c F0 (setWtp s wsi hpi psi) :=
        hinv.of_safetySlice
          ⟨hlen.core_ok,
            { hlen.scratch_ok with
                wsort_len := hwsi_l, tarjan_mark_len := hhpi_l, tarjan_reach_len := hpsi_l }⟩
          rfl ⟨rfl, rfl⟩
      clear hrec
      -- L_1: push active unassigned literals with `FL_FACT_P`/`FL_FACT_N` & `wvec > 1`
      refine wp_loop_inv
        (fun (hlen, vi, ()) mv => ∃ st1 : FullState,
          vi.toNat ≤ s.core.cur_vars ∧ hlen.toNat ≤ 2 * vi.toNat ∧
          FullDenseInv c F0 st1 ∧ st1.core.cur_vars = s.core.cur_vars ∧
          st1.core.fuel = s.core.fuel ∧
          (∀ k < hlen.toNat, (st1.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c st1 ⋆ R) mv)
        (fun (_, vi, ()) _ => s.core.cur_vars - vi.toNat)
        (fun J1 hJ1 => by
          c0_hfast
          exact hJ1 (0#32, 0#64, ()) mz ⟨setWtp s wsi hpi psi, Nat.zero_le _, Nat.zero_le _,
            hstz_inv, rfl, rfl, fun k hk => by simp at hk, hmz⟩)
        (fun J1 p mv hL1 hrec1 => ?_)
      rcases p with ⟨hlen, vi, ⟨⟩⟩
      rcases hL1 with ⟨st1, hvi_le, hhl_le, hinv1, hcv1, hfu1, hhp1, hmv⟩
      c0_hfast
      · have hvi_lt : vi.toNat < s.core.cur_vars := by
          simpa [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] using hc
        have hvi1 : (vi + 1#64).toNat = vi.toNat + 1 := m7_bv64_add1_toNat hvi_lt (by omega)
        have hhl1 : (hlen + 1#32).toNat = hlen.toNat + 1 :=
          m7_bv32_add1_toNat (by omega : hlen.toNat < 2 * s.core.cur_vars) (by omega)
        have hhl2 : (hlen + 1#32 + 1#32).toNat = hlen.toNat + 2 := by
          rw [m7_bv32_add1_toNat
            (by rw [hhl1]; omega : (hlen + 1#32).toNat < 2 * s.core.cur_vars + 1)
            (by omega : 2 * s.core.cur_vars + 1 < 2 ^ 32), hhl1]
        have h1l := hinv1.1.lengths
        have hfl_lt : vi.toNat < st1.core.flags.length := by rw [h1l.core_ok.flags_len]; omega
        have hvl_lt : (vi.toNat * 2 ^ 1) % 2 ^ 64 < st1.core.vals.length := by
          rw [h1l.core_ok.vals_len, Nat.mod_eq_of_lt (by omega)]; omega
        have hwv1_lt : (2 * (2 * vi.toNat) + 1) % 2 ^ 64 < st1.core.wvec.length := by
          rw [h1l.core_ok.wvec_len, Nat.mod_eq_of_lt (by omega)]; omega
        have hwvn_lt := m7_nl_wvec_lt st1.core.wvec.length hvi_lt hcv_lt32
          (by rw [h1l.core_ok.wvec_len]; omega)
        c0_hfast
        · -- P active (`FL_FACT_P` & `wvec[4*vi+1] > 1`): push `pl = 2 * vi` then handle `FL_FACT_N`
          have hhl_lt : hlen.toNat < 2 * s.core.cur_vars := by omega
          have hhp_p_lt : hlen.toNat < st1.scratch.tarjan_mark.length := by
            rw [h1l.scratch_ok.tarjan_mark_len]; omega
          have hps_p_lt : (2 * vi.toNat) % 2 ^ 64 < st1.scratch.tarjan_reach.length := by
            rw [h1l.scratch_ok.tarjan_reach_len, Nat.mod_eq_of_lt (by omega)]; omega
          c0_hfast
          let st_p0 : FullState :=
            { st1 with scratch :=
              { st1.scratch with
                tarjan_mark := st1.scratch.tarjan_mark.set (BitVec.setWidth 64 hlen).toNat
                  (BitVec.setWidth 32 (vi <<< (1 : Nat)))
                tarjan_reach := st1.scratch.tarjan_reach.set
                  (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)))).toNat hlen } }
          refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
          refine ⟨2 * s.core.cur_vars, st_p0.scratch.tarjan_mark,
            st_p0.scratch.tarjan_reach, st_p0.core.wvec, FullMemFheapRest c st_p0 ⋆ R,
            by dsimp only [st_p0]; rw [List.length_set, h1l.scratch_ok.tarjan_mark_len]; omega,
            by dsimp only [st_p0]; rw [List.length_set, h1l.scratch_ok.tarjan_reach_len]; omega,
            by dsimp only [st_p0]; rw [h1l.core_ok.wvec_len]; omega,
            by omega, hhl_lt, ?_, ?_, fun hp' ps' m' hhp' hps' hperm hfix hm' => ?_⟩
          · dsimp only [st_p0]; rw [m7_bv64_32]
            exact fheap_push_pre_lt_bv (by rw [m7_pl_bv32_toNat hvi_lt hcv_lt32]; omega)
              hhp_p_lt hhp1
          · exact focus_fheap (by assumption)
          · have hinv_p : FullDenseInv c F0
                { st_p0 with scratch :=
                  { st_p0.scratch with tarjan_mark := hp', tarjan_reach := ps' } } :=
              fullDenseInv_set_fheap hinv1
                (by rw [hhp']; dsimp only [st_p0]
                    rw [List.length_set, h1l.scratch_ok.tarjan_mark_len])
                (by rw [hps']; dsimp only [st_p0]
                    rw [List.length_set, h1l.scratch_ok.tarjan_reach_len])
            let st_p := { st_p0 with scratch :=
              { st_p0.scratch with tarjan_mark := hp', tarjan_reach := ps' } }
            have huf_p : (FullMem c st_p ⋆ R) m' := unfocus_fheap hm'
            have hhp_p : ∀ k < (hlen + 1#32).toNat,
                (st_p.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
              rw [hhl1]
              exact fheap_up_post_lt
                (fheap_push_pre_lt_bv (by rw [m7_pl_bv32_toNat hvi_lt hcv_lt32]; omega)
                  hhp_p_lt hhp1)
                (fun k hk hgt => by omega) hperm hfix
            have hpl_p := hinv_p.1.lengths
            have hflp_lt : vi.toNat < st_p.core.flags.length := by
              rw [hpl_p.core_ok.flags_len]; omega
            have hwvnp_lt := m7_nl_wvec_lt st_p.core.wvec.length hvi_lt hcv_lt32
              (by rw [hpl_p.core_ok.wvec_len]; omega)
            c0_hfast
            · -- FL_FACT_N & wvec > 1 after P push
              have hphl_lt : (hlen + 1#32).toNat < 2 * s.core.cur_vars := by rw [hhl1]; omega
              have hhp_np_lt : (hlen + 1#32).toNat < st_p.scratch.tarjan_mark.length := by
                rw [hpl_p.scratch_ok.tarjan_mark_len]; omega
              have hps_np_lt :
                  (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                    st_p.scratch.tarjan_reach.length := by
                rw [m7_nl_32 hvi_lt hcv_lt32, hpl_p.scratch_ok.tarjan_reach_len]; omega
              c0_hfast
              let st_pn0 : FullState :=
                { st_p with scratch :=
                  { st_p.scratch with
                    tarjan_mark := st_p.scratch.tarjan_mark.set
                      (BitVec.setWidth 64 (hlen + 1#32)).toNat
                      (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)
                    tarjan_reach := st_p.scratch.tarjan_reach.set
                      (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat
                      (hlen + 1#32) } }
              have htm_pn0_len : st_pn0.scratch.tarjan_mark.length = 2 * c.max_vars := by
                dsimp only [st_pn0, st_p, st_p0]
                rw [List.length_set, hhp', List.length_set, h1l.scratch_ok.tarjan_mark_len]
              have htr_pn0_len : st_pn0.scratch.tarjan_reach.length = 2 * c.max_vars := by
                dsimp only [st_pn0, st_p, st_p0]
                rw [List.length_set, hps', List.length_set, h1l.scratch_ok.tarjan_reach_len]
              refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
              refine ⟨2 * s.core.cur_vars, st_pn0.scratch.tarjan_mark,
                st_pn0.scratch.tarjan_reach, st_pn0.core.wvec, FullMemFheapRest c st_pn0 ⋆ R,
                by rw [htm_pn0_len]; omega,
                by rw [htr_pn0_len]; omega,
                by dsimp only [st_pn0, st_p, st_p0]; rw [h1l.core_ok.wvec_len]; omega,
                by omega, hphl_lt, ?_, ?_, fun hp2 ps2 m2 hhp2 hps2 hperm2 hfix2 hm2 => ?_⟩
              · dsimp only [st_pn0]; rw [m7_bv64_32]
                exact fheap_push_pre_lt_bv (by rw [m7_nl_bv32_toNat hvi_lt hcv_lt32]; omega)
                  hhp_np_lt hhp_p
              · exact focus_fheap (by assumption)
              · have hinv_pn : FullDenseInv c F0
                    { st_pn0 with scratch :=
                      { st_pn0.scratch with tarjan_mark := hp2, tarjan_reach := ps2 } } :=
                  fullDenseInv_set_fheap hinv_p
                    (by rw [hhp2]; exact htm_pn0_len)
                    (by rw [hps2]; exact htr_pn0_len)
                have huf_pn := unfocus_fheap hm2
                c0_hfast
                refine hrec1 (hlen + 1#32 + 1#32, vi + 1#64, ()) m2
                  (by dsimp only; rw [hvi1]; omega)
                  ⟨_, by rw [hvi1]; omega, by rw [hhl2, hvi1]; omega, hinv_pn, hcv1, hfu1, ?_,
                    huf_pn⟩
                rw [hhl2]
                exact fheap_up_post_lt
                  (fheap_push_pre_lt_bv (by rw [m7_nl_bv32_toNat hvi_lt hcv_lt32]; omega)
                    hhp_np_lt hhp_p)
                  (fun k hk hgt => by omega) hperm2 hfix2
            · exact hrec1 (hlen + 1#32, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
                ⟨st_p, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_p, hcv1, hfu1, hhp_p,
                  by assumption⟩
            · exact hrec1 (hlen + 1#32, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
                ⟨st_p, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_p, hcv1, hfu1, hhp_p,
                  by assumption⟩
        · -- P skipped (wvec <= 1), FL_FACT_N != 0 & wvec[N] > 1
          have hhl_lt : hlen.toNat < 2 * s.core.cur_vars := by omega
          have hhp_n_lt : hlen.toNat < st1.scratch.tarjan_mark.length := by
            rw [h1l.scratch_ok.tarjan_mark_len]; omega
          have hhp_n_lt64 : (BitVec.setWidth 64 hlen).toNat < st1.scratch.tarjan_mark.length := by
            rw [m7_bv64_32]; exact hhp_n_lt
          have hps_n_lt :
              (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                st1.scratch.tarjan_reach.length := by
            rw [m7_nl_32 hvi_lt hcv_lt32, h1l.scratch_ok.tarjan_reach_len]; omega
          c0_hsteps_nogrp
          let st_n0 : FullState :=
            { st1 with scratch :=
              { st1.scratch with
                tarjan_mark := st1.scratch.tarjan_mark.set (BitVec.setWidth 64 hlen).toNat
                  (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)
                tarjan_reach := st1.scratch.tarjan_reach.set
                  (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat
                  hlen } }
          refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
          refine ⟨2 * s.core.cur_vars, st_n0.scratch.tarjan_mark,
            st_n0.scratch.tarjan_reach, st_n0.core.wvec, FullMemFheapRest c st_n0 ⋆ R,
            by dsimp only [st_n0]; rw [List.length_set, h1l.scratch_ok.tarjan_mark_len]; omega,
            by dsimp only [st_n0]; rw [List.length_set, h1l.scratch_ok.tarjan_reach_len]; omega,
            by dsimp only [st_n0]; rw [h1l.core_ok.wvec_len]; omega,
            by omega, hhl_lt, ?_, ?_, fun hp' ps' m' hhp' hps' hperm hfix hm' => ?_⟩
          · dsimp only [st_n0]; rw [m7_bv64_32]
            exact fheap_push_pre_lt_bv (by rw [m7_nl_bv32_toNat hvi_lt hcv_lt32]; omega)
              hhp_n_lt hhp1
          · exact focus_fheap (by assumption)
          · have hinv_n : FullDenseInv c F0
                { st_n0 with scratch :=
                  { st_n0.scratch with tarjan_mark := hp', tarjan_reach := ps' } } :=
              fullDenseInv_set_fheap hinv1
                (by rw [hhp']; dsimp only [st_n0]
                    rw [List.length_set, h1l.scratch_ok.tarjan_mark_len])
                (by rw [hps']; dsimp only [st_n0]
                    rw [List.length_set, h1l.scratch_ok.tarjan_reach_len])
            have huf_n := unfocus_fheap hm'
            c0_hfast
            refine hrec1 (hlen + 1#32, vi + 1#64, ()) m' (by dsimp only; rw [hvi1]; omega)
              ⟨_, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_n, hcv1, hfu1, ?_, huf_n⟩
            rw [hhl1]
            exact fheap_up_post_lt
              (fheap_push_pre_lt_bv (by rw [m7_nl_bv32_toNat hvi_lt hcv_lt32]; omega)
                hhp_n_lt hhp1)
              (fun k hk hgt => by omega) hperm hfix
        · exact hrec1 (hlen, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
            ⟨st1, by rw [hvi1]; omega, by rw [hvi1]; omega, hinv1, hcv1, hfu1, hhp1, by assumption⟩
        · exact hrec1 (hlen, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
            ⟨st1, by rw [hvi1]; omega, by rw [hvi1]; omega, hinv1, hcv1, hfu1, hhp1, by assumption⟩
        · -- P skipped (FL_FACT_P == 0), FL_FACT_N != 0 & wvec[N] > 1
          have hhl_lt : hlen.toNat < 2 * s.core.cur_vars := by omega
          have hhp_n_lt : hlen.toNat < st1.scratch.tarjan_mark.length := by
            rw [h1l.scratch_ok.tarjan_mark_len]; omega
          have hhp_n_lt64 : (BitVec.setWidth 64 hlen).toNat < st1.scratch.tarjan_mark.length := by
            rw [m7_bv64_32]; exact hhp_n_lt
          have hps_n_lt :
              (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat <
                st1.scratch.tarjan_reach.length := by
            rw [m7_nl_32 hvi_lt hcv_lt32, h1l.scratch_ok.tarjan_reach_len]; omega
          c0_hsteps_nogrp
          let st_n0 : FullState :=
            { st1 with scratch :=
              { st1.scratch with
                tarjan_mark := st1.scratch.tarjan_mark.set (BitVec.setWidth 64 hlen).toNat
                  (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)
                tarjan_reach := st1.scratch.tarjan_reach.set
                  (BitVec.setWidth 64 (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32)).toNat
                  hlen } }
          refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
          refine ⟨2 * s.core.cur_vars, st_n0.scratch.tarjan_mark,
            st_n0.scratch.tarjan_reach, st_n0.core.wvec, FullMemFheapRest c st_n0 ⋆ R,
            by dsimp only [st_n0]; rw [List.length_set, h1l.scratch_ok.tarjan_mark_len]; omega,
            by dsimp only [st_n0]; rw [List.length_set, h1l.scratch_ok.tarjan_reach_len]; omega,
            by dsimp only [st_n0]; rw [h1l.core_ok.wvec_len]; omega,
            by omega, hhl_lt, ?_, ?_, fun hp' ps' m' hhp' hps' hperm hfix hm' => ?_⟩
          · dsimp only [st_n0]; rw [m7_bv64_32]
            exact fheap_push_pre_lt_bv (by rw [m7_nl_bv32_toNat hvi_lt hcv_lt32]; omega)
              hhp_n_lt hhp1
          · exact focus_fheap (by assumption)
          · have hinv_n : FullDenseInv c F0
                { st_n0 with scratch :=
                  { st_n0.scratch with tarjan_mark := hp', tarjan_reach := ps' } } :=
              fullDenseInv_set_fheap hinv1
                (by rw [hhp']; dsimp only [st_n0]
                    rw [List.length_set, h1l.scratch_ok.tarjan_mark_len])
                (by rw [hps']; dsimp only [st_n0]
                    rw [List.length_set, h1l.scratch_ok.tarjan_reach_len])
            have huf_n := unfocus_fheap hm'
            c0_hfast
            refine hrec1 (hlen + 1#32, vi + 1#64, ()) m' (by dsimp only; rw [hvi1]; omega)
              ⟨_, by rw [hvi1]; omega, by rw [hhl1, hvi1]; omega, hinv_n, hcv1, hfu1, ?_, huf_n⟩
            rw [hhl1]
            exact fheap_up_post_lt
              (fheap_push_pre_lt_bv (by rw [m7_nl_bv32_toNat hvi_lt hcv_lt32]; omega)
                hhp_n_lt hhp1)
              (fun k hk hgt => by omega) hperm hfix
        all_goals
          exact hrec1 (hlen, vi + 1#64, ()) _ (by dsimp only; rw [hvi1]; omega)
            ⟨st1, by rw [hvi1]; omega, by rw [hvi1]; omega, hinv1, hcv1, hfu1, hhp1, by assumption⟩
      · -- exit L_1 -> L_5 main factor loop
        c0_hfast
        refine wp_while_state
          (α := BitVec 64 × BitVec 32 × FullState)
          (fun (cbud, chlen, _) => (cbud, chlen, ()))
          (fun (cbud, chlen, _) => cbud.toNat * (2 * c.max_vars + 1) + chlen.toNat)
          (fun (cbud, chlen, stp) mp => FullDenseInv c F0 stp ∧
            s.core.cur_vars ≤ stp.core.cur_vars ∧ stp.core.fuel = s.core.fuel ∧
            chlen.toNat ≤ 2 * stp.core.cur_vars ∧
            (∀ k < chlen.toNat,
              (stp.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * stp.core.cur_vars) ∧
            (FullMem c stp ⋆ R) mp)
          (fun J5 hJ5 => by
            c0_hfast
            exact hJ5 (budget, hlen, st1) mv ⟨hinv1, Nat.le_of_eq hcv1.symm, hfu1,
              by rw [hcv1]; omega,
              fun k hk => by rw [hcv1]; exact hhp1 k hk, hmv⟩)
          (fun J5 (cbud, chlen, stp) mp ⟨hinvp, hcvp, hfup, hhlp, hhpp, hmp⟩ hrec5 => ?_)
        dsimp only [Blocks.get]
        refine wp_join0
          (fun mb => ∃ stb : FullState,
            FullDenseInv c F0 stb ∧ s.core.cur_vars ≤ stb.core.cur_vars ∧
            stb.core.fuel = s.core.fuel ∧ (FullMem c stb ⋆ R) mb)
          (fun _ mb ⟨stb, hinvb, hcvb, hfub, hmb⟩ => by
            -- L_6 -> L_7 zero fheap[0..2*cur_vars) and fpos[0..2*cur_vars)
            have hbl := hinvb.1.lengths
            have hb_cv_le := hbl.core_ok.cur_vars_le
            have hb_lt64 : 2 * stb.core.cur_vars < 2 ^ 64 := by
              change c.max_vars < 2 * 268435456 at hmaxv; omega
            c0_hfast
            refine wp_loop_inv
              (fun (fi, ()) mf => ∃ hpf psf,
                fi.toNat ≤ 2 * stb.core.cur_vars ∧
                hpf.length = 2 * c.max_vars ∧ psf.length = 2 * c.max_vars ∧
                (FullMem c
                  ({ stb with scratch :=
                    { stb.scratch with tarjan_mark := hpf, tarjan_reach := psf } } : FullState) ⋆
                  R) mf)
              (fun (fi, ()) _ => 2 * stb.core.cur_vars - fi.toNat)
              (fun J7 hJ7 => by
                c0_hfast
                exact hJ7 (0#64, ()) mb ⟨stb.scratch.tarjan_mark, stb.scratch.tarjan_reach,
                  Nat.zero_le _, hbl.scratch_ok.tarjan_mark_len, hbl.scratch_ok.tarjan_reach_len,
                  hmb⟩)
              (fun J7 p mf hL7 hrec7 => ?_)
            rcases p with ⟨fi, ⟨⟩⟩
            rcases hL7 with ⟨hpf, psf, hfi_le, hhpf_l, hpsf_l, hmf⟩
            c0_hfast
            · have hfi_lt : fi.toNat < 2 * stb.core.cur_vars := by
                simpa [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                  Nat.mod_eq_of_lt hb_lt64] using hc
              have h1 : fi.toNat < hpf.length := by omega
              have h2 : fi.toNat < psf.length := by omega
              c0_hfast_nogrp
              have hfi1 : (fi + 1#64).toNat = fi.toNat + 1 :=
                m7_bv64_add1_toNat hfi_lt (by omega)
              refine hrec7 (fi + 1#64, ()) _ (by dsimp only; rw [hfi1]; omega)
                ⟨hpf.set fi.toNat 0#32, psf.set fi.toNat 0#32, by rw [hfi1]; omega,
                  by simpa using hhpf_l, by simpa using hpsf_l, ?_⟩
              assumption
            · -- Exit L_7 -> L_8 (`cur_vars > init_cv`) -> L_9 VMTF stamp renumber
              have hinv_f : FullDenseInv c F0
                  { stb with scratch :=
                    { stb.scratch with tarjan_mark := hpf, tarjan_reach := psf } } :=
                fullDenseInv_set_fheap hinvb hhpf_l hpsf_l
              clear hrec7
              let stf : FullState :=
                { stb with scratch := { stb.scratch with tarjan_mark := hpf, tarjan_reach := psf } }
              have hstf_cv : stf.core.cur_vars = stb.core.cur_vars := rfl
              have hstf_cv_lt64 : stf.core.cur_vars < 2 ^ 64 := by
                rw [hstf_cv]; change c.max_vars < 2 * 268435456 at hmaxv; omega
              have hfl := hinv_f.1.lengths
              refine wp_loop_inv
                (fun (qidx, qst, ()) mq => ∃ qs' : List (BitVec 32),
                  qst.toNat ≤ stf.core.cur_vars ∧ qs'.length = c.max_vars ∧
                  (FullMem c
                    ({ stf with scratch := { stf.scratch with q_stamp := qs' } } : FullState) ⋆
                    R) mq)
                (fun (_, qst, ()) _ => stf.core.cur_vars - qst.toNat)
                ?_ ?_
              · intro J9 hJ9
                c0_hfast
                exact hJ9 (stf.scratch.q_first, 0#64, ()) mf ⟨stf.scratch.q_stamp,
                  Nat.zero_le _, hfl.scratch_ok.q_stamp_len, hmf⟩
              · intro J9 pq mq hL9 hrec9
                rcases pq with ⟨qidx, qst, ⟨⟩⟩
                rcases hL9 with ⟨qs', hqst_le, hqs'_l, hmq⟩
                c0_hfast
                · -- qidx < cur_vars && qst < cur_vars
                  have hmod64 : stb.core.cur_vars % 2 ^ 64 = stb.core.cur_vars := by
                    rw [← hstf_cv] at hstf_cv_lt64; exact Nat.mod_eq_of_lt hstf_cv_lt64
                  have hqi_lt : qidx.toNat < stf.core.cur_vars := by
                    have h1 : qidx.toNat < stb.core.cur_vars % 2 ^ 64 := by assumption
                    rw [hmod64] at h1; rw [hstf_cv]; exact h1
                  have hqs_lt : qst.toNat < stf.core.cur_vars := by
                    have h1 : qst.toNat < stb.core.cur_vars % 2 ^ 64 := by assumption
                    rw [hmod64] at h1; rw [hstf_cv]; exact h1
                  have h1 : qidx.toNat < qs'.length := by
                    rw [hqs'_l]; exact lt_of_lt_of_le hqi_lt hb_cv_le
                  have h2 : qidx.toNat < stf.scratch.q_next.length := by
                    rw [hfl.scratch_ok.q_next_len]; exact lt_of_lt_of_le hqi_lt hb_cv_le
                  c0_hfast_nogrp
                  have hqst1 : (qst + 1#64).toNat = qst.toNat + 1 :=
                    m7_bv64_add1_toNat hqs_lt (by omega)
                  refine hrec9 (BitVec.setWidth 64 (stf.scratch.q_next[qidx.toNat]'h2),
                    qst + 1#64, ()) _ (by dsimp only; rw [hqst1]; omega)
                    ⟨qs'.set qidx.toNat (BitVec.setWidth 32 (qst + 1#64)),
                      by rw [hqst1]; omega, by simpa using hqs'_l, ?_⟩
                  assumption
                all_goals
                  clear hrec9
                  c0_hfast
                  first
                  | exact hQ 1#64 _ _ (fullDenseInv_set_qstamp hinv_f hqs'_l) hcvb hfub rfl
                      (by assumption)
                  | (have hqsi_lt : stf.scratch.q_search_idx.toNat < qs'.length := by
                       have hmod64 : stb.core.cur_vars % 2 ^ 64 = stb.core.cur_vars := by
                         rw [← hstf_cv] at hstf_cv_lt64; exact Nat.mod_eq_of_lt hstf_cv_lt64
                       have h1 : stf.scratch.q_search_idx.toNat < stb.core.cur_vars % 2 ^ 64 := by
                         assumption
                       rw [hmod64] at h1
                       rw [hqs'_l]; exact lt_of_lt_of_le h1 hb_cv_le
                     c0_hfast
                     exact hQ 1#64 _ _ (fullDenseInv_set_qstamp hinv_f hqs'_l) hcvb hfub rfl
                       (by assumption))
            · -- Exit L_7 -> `!(cur_vars > init_cv)` -> `ret 1`
              clear hrec7
              exact hQ 1#64 _ mf (fullDenseInv_set_fheap hinvb hhpf_l hpsf_l)
                hcvb hfub rfl hmf )
          (fun J6 hJ6 => by
            c0_hfast
            · -- Inside L_5 iteration: pop root `u = fheap[0]`
              have hpl := hinvp.1.lengths
              have hcvp_le := hpl.core_ok.cur_vars_le
              have hcvp_lt32 : 2 * stp.core.cur_vars < 2 ^ 32 := by
                change c.max_vars < 2 * 268435456 at hmaxv; omega
              have hcvp_lt64 : 2 * stp.core.cur_vars < 2 ^ 64 := by omega
              have hchlen_pos : 0 < chlen.toNat := by
                simpa using (by assumption : BitVec.toNat 0 < chlen.toNat)
              have hp_cv_lt : stp.core.cur_vars < c.max_vars := by
                simpa [Nat.mod_eq_of_lt (by omega : stp.core.cur_vars < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64)] using
                  (by assumption : stp.core.cur_vars % 2 ^ 64 < c.max_vars % 2 ^ 64)
              have hcbud_pos : 0 < cbud.toNat := by
                simpa using (by assumption : BitVec.toNat 0 < cbud.toNat)
              have h0_lt_hp : 0 < stp.scratch.tarjan_mark.length := by
                rw [hpl.scratch_ok.tarjan_mark_len]; omega
              have hhp0_lt : (BitVec.ofNat 64 0).toNat < stp.scratch.tarjan_mark.length := by
                simp only [BitVec.toNat_ofNat]; exact h0_lt_hp
              obtain ⟨u, hu_def⟩ :
                  ∃ u : BitVec 32,
                    u = stp.scratch.tarjan_mark[(BitVec.ofNat 64 0).toNat]'hhp0_lt := ⟨_, rfl⟩
              have hu_lt : u.toNat < 2 * stp.core.cur_vars := by
                have h1 := hhpp 0 hchlen_pos
                rw [List.getElem?_eq_getElem h0_lt_hp, Option.getD_some] at h1
                simpa [BitVec.toNat_ofNat, hu_def] using h1
              have hu_lt_ps :
                  (BitVec.setWidth 64
                    (stp.scratch.tarjan_mark[(BitVec.ofNat 64 0).toNat]'hhp0_lt)).toNat <
                    stp.scratch.tarjan_reach.length := by
                rw [BitVec.toNat_setWidth, ← hu_def, Nat.mod_eq_of_lt (by omega),
                  hpl.scratch_ok.tarjan_reach_len]
                omega
              c0_hsteps_nogrp
              rw [← hu_def]
              have hu64_nat : (BitVec.setWidth 64 u).toNat = u.toNat := by
                rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
              let stp0 : FullState :=
                { stp with scratch :=
                  { stp.scratch with
                    tarjan_reach := stp.scratch.tarjan_reach.set u.toNat 0xFFFFFFFF#32 } }
              have hinv_p0 : FullDenseInv c F0 stp0 :=
                fullDenseInv_set_fheap hinvp hpl.scratch_ok.tarjan_mark_len
                  (by simp only [List.length_set, hpl.scratch_ok.tarjan_reach_len])
              -- `if (hlen1 > 0)` sift down join
              refine wp_join0
                (fun mp1 => ∃ stp1 : FullState, FullDenseInv c F0 stp1 ∧
                  stp1.core.cur_vars = stp.core.cur_vars ∧ stp1.core.fuel = stp.core.fuel ∧
                  (∀ k < (chlen - 1#32).toNat,
                    (stp1.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * stp.core.cur_vars) ∧
                  (FullMem c stp1 ⋆ R) mp1)
                (fun _ mp1 ⟨stp1, hinvp1, hcvp1, hfup1, hhpp1, hmp1⟩ => by
                  -- `L_12`: load `fl[u >>> 1]`, compute `fbit = (u & 1 != 0) ? 64 : 32`
                  have hp1l := hinvp1.1.lengths
                  have huv_lt : u.toNat / 2 < stp1.core.flags.length := by
                    rw [hp1l.core_ok.flags_len]; omega
                  refine wp_join_state1 (t := i32) (α := BitVec 32) id
                    (fun fbit mp2 => (fbit = 32#32 ∨ fbit = 64#32) ∧ (FullMem c stp1 ⋆ R) mp2)
                    (fun _ fbit mp2 ⟨hfbit, hmp2⟩ => by
                      have huv_lt2 : u.toNat / 2 < stp1.core.flags.length := huv_lt
                      have hvl_u_lt : u.toNat < stp1.core.vals.length := by
                        rw [hp1l.core_ok.vals_len]; omega
                      have hhlen1_eq : (chlen - 1#32).toNat = chlen.toNat - 1 :=
                        m7_bv32_sub1_toNat hchlen_pos
                      have hhlen1_le : (chlen - 1#32).toNat ≤ 2 * stp.core.cur_vars := by
                        rw [hhlen1_eq]; omega
                      have hmu_lt :
                          (cbud.toNat * (2 * c.max_vars + 1) + (chlen - 1#32).toNat) <
                            (cbud.toNat * (2 * c.max_vars + 1) + chlen.toNat) := by
                        rw [hhlen1_eq]; omega
                      have hskip : ∀ st_skip m_skip,
                          FullDenseInv c F0 st_skip →
                          st_skip.core.cur_vars = stp.core.cur_vars →
                          st_skip.core.fuel = stp.core.fuel →
                          (∀ k < (chlen - 1#32).toNat,
                            (st_skip.scratch.tarjan_mark[k]?.getD 0#32).toNat <
                              2 * stp.core.cur_vars) →
                          (FullMem c st_skip ⋆ R) m_skip →
                          J5 (cbud, chlen - 1#32, ()) m_skip :=
                        fun st_sk m_sk hik hck hfk hhpk hmk =>
                        hrec5 (cbud, chlen - 1#32, st_sk) m_sk hmu_lt
                          ⟨hik, Nat.le_trans hcvp (Nat.le_of_eq hck.symm), hfk.trans hfup,
                            by rw [hck]; exact hhlen1_le,
                            fun k hk => by rw [hck]; exact hhpk k hk, hmk⟩
                      have huv_lt2_bv : (BitVec.setWidth 64 (u >>> (1 : Nat))).toNat <
                          stp1.core.flags.length := by
                        rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
                        have hsh_lt : u.toNat >>> 1 < 2 ^ 64 := by
                          rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega
                        rw [Nat.mod_eq_of_lt hsh_lt, Nat.shiftRight_eq_div_pow, Nat.pow_one]
                        exact huv_lt2
                      c0_hfast
                      · exact hskip stp1 _ hinvp1 hcvp1 hfup1 hhpp1 (by assumption)
                      · exact hskip stp1 _ hinvp1 hcvp1 hfup1 hhpp1 (by assumption)
                      · exact hskip stp1 _ hinvp1 hcvp1 hfup1 hhpp1 (by assumption)
                      · -- Active, fbit set, unassigned -> clear `fl`, check wvec > 1
                        have huv64_div :
                            (BitVec.setWidth 64 (u >>> (1 : Nat))).toNat = u.toNat / 2 := by
                          rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
                            Nat.shiftRight_eq_div_pow, Nat.pow_one]
                          exact Nat.mod_eq_of_lt (by omega)
                        have hfl_set_l :
                            (stp1.core.flags.set (BitVec.setWidth 64 (u >>> (1 : Nat))).toNat
                              ((stp1.core.flags[(BitVec.setWidth 64 (u >>> (1 : Nat))).toNat]'
                                huv_lt2_bv) &&& ~~~fbit)).length = c.max_vars := by
                          rw [List.length_set, hp1l.core_ok.flags_len]
                        let stp2 : FullState :=
                          { stp1 with core :=
                            { stp1.core with
                              flags := stp1.core.flags.set
                                (BitVec.setWidth 64 (u >>> (1 : Nat))).toNat
                                ((stp1.core.flags[(BitVec.setWidth 64 (u >>> (1 : Nat))).toNat]'
                                  huv_lt2_bv) &&& ~~~fbit) } }
                        have hinv_p2 : FullDenseInv c F0 stp2 :=
                          fullDenseInv_set_flags hinvp1 hfl_set_l
                        have hcv_p2 : stp2.core.cur_vars = stp.core.cur_vars := hcvp1
                        have hfu_p2 : stp2.core.fuel = stp.core.fuel := hfup1
                        have hp2l := hinv_p2.1.lengths
                        have hwvu_lt : (BitVec.setWidth 64 u <<< (1 : Nat) + 1#64).toNat <
                            stp2.core.wvec.length := by
                          rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, hu64_nat]
                          simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
                          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                            hp2l.core_ok.wvec_len]
                          omega
                        c0_hfast
                        · exact hskip stp2 _ hinv_p2 hcv_p2 hfu_p2 hhpp1 (by assumption)
                        · -- `wvec[2*u+1] > 1`: decrement budget & call `full_bva_try_lit`
                          refine wp_call_of_spec _ _ (hTryLit _ _ _ _ ?_)
                          refine ⟨c, F0, stp2, R, rfl, hinv_p2, by dsimp [stp2]; omega,
                            by assumption,
                            fun ok st3 m3 hinv3 hcv3 hfu3 htm3 htr3 hm3 => ?_⟩
                          have h3l := hinv3.1.lengths
                          have hcv3_le := h3l.core_ok.cur_vars_le
                          have hbud_dec :
                              ((cbud - 1#64).toNat * (2 * c.max_vars + 1) +
                                  (chlen - 1#32).toNat) <
                                cbud.toNat * (2 * c.max_vars + 1) + chlen.toNat :=
                            m7_bud_dec_thlen hcbud_pos (by omega)
                          refine wp_jnz_bool ok rfl (fun hok => ?_) (fun hok => ?_)
                          · -- `ok = true`: `L_15` -> `L_16` touched-lit reschedule loop
                            let init_nlits : Nat := 2 * s.core.cur_vars
                            have hinit_le_cv3 : init_nlits ≤ 2 * st3.core.cur_vars := by
                              dsimp [init_nlits]; rw [hcv_p2] at hcv3; omega
                            c0_hfast_nogrp
                            refine wp_join_state1 (t := i64) (α := BitVec 64) id
                              (fun rcnt mt =>
                                rcnt.toNat ≤ init_nlits ∧ (FullMem c st3 ⋆ R) mt)
                              ?_ ?_
                            · intro _ rcnt mt ⟨hrcnt_le, hmt15⟩
                              dsimp only [Blocks.get, id]
                              refine wp_loop_inv (ts := [i32, i64])
                                (fun (thlen, ti, ()) mt => ∃ stt : FullState,
                                  FullDenseInv c F0 stt ∧
                                  stt.core.cur_vars = st3.core.cur_vars ∧
                                  stt.core.fuel = st3.core.fuel ∧
                                  thlen.toNat ≤ 2 * st3.core.cur_vars ∧
                                  (∀ k < thlen.toNat,
                                    (stt.scratch.tarjan_mark[k]?.getD 0#32).toNat <
                                      2 * st3.core.cur_vars) ∧
                                  (FullMem c stt ⋆ R) mt)
                                (fun (_, ti, ()) _ => init_nlits - ti.toNat)
                                ?_ ?_
                              · intro J16 hJ16
                                c0_hfast_nogrp
                                exact hJ16 (chlen - 1#32, 0#64, ()) mt
                                  ⟨st3, hinv3, rfl, rfl, by omega,
                                    fun k hk => by
                                      rw [htm3]; dsimp only [stp2]
                                      exact Nat.lt_of_lt_of_le (hhpp1 k hk)
                                        (by rw [← hcv_p2]; omega),
                                    hmt15⟩
                              · intro J16 pt mt hL16 hrec16
                                rcases pt with ⟨thlen, ti, ⟨⟩⟩
                                rcases hL16 with
                                  ⟨stt, hinvt, hcvt, hfut, hthl_le, hthp, hmt⟩
                                c0_hsplit
                                · -- `ti < rcnt`
                                  have htl := hinvt.1.lengths
                                  have hti_lt_init : ti.toNat < init_nlits := by
                                    have h1 : ti.toNat < rcnt.toNat := by
                                      simpa using (by assumption : ti.toNat < rcnt.toNat)
                                    exact lt_of_lt_of_le h1 hrcnt_le
                                  clear hc
                                  have hti_lt_ws2 :
                                      ti.toNat < stt.scratch.work_stk2.length := by
                                    rw [htl.scratch_ok.work_stk2_len]
                                    dsimp [init_nlits] at hti_lt_init
                                    have := htl.core_ok.cur_vars_le; omega
                                  c0_hsplit
                                  let tl : BitVec 32 := stt.scratch.work_stk2[ti.toNat]'hti_lt_ws2
                                  let L16Inv : BitVec 32 → Mem 64 → Prop := fun thl' mt' =>
                                    ∃ stt' : FullState,
                                      FullDenseInv c F0 stt' ∧
                                      stt'.core.cur_vars = st3.core.cur_vars ∧
                                      stt'.core.fuel = st3.core.fuel ∧
                                      thl'.toNat ≤ 2 * st3.core.cur_vars ∧
                                      (∀ k < thl'.toNat,
                                        (stt'.scratch.tarjan_mark[k]?.getD 0#32).toNat <
                                          2 * st3.core.cur_vars) ∧
                                      (FullMem c stt' ⋆ R) mt'
                                  have hstt_skip : ∀ thl' m_sk,
                                      thl' = thlen → (FullMem c stt ⋆ R) m_sk → L16Inv thl' m_sk :=
                                    fun _ m_sk hth_eq hm_sk => by
                                      subst hth_eq
                                      exact ⟨stt, hinvt, hcvt, hfut, hthl_le, hthp, hm_sk⟩
                                  refine wp_join_state1 (t := i32) (α := BitVec 32) id L16Inv ?_ ?_
                                  · intro _ thlen' mt' hL16'
                                    dsimp only [Blocks.get, id]
                                    c0_hfast_nogrp
                                    have hti1 : (ti + 1#64).toNat = ti.toNat + 1 :=
                                      m7_bv64_add1_toNat hti_lt_init (by dsimp [init_nlits]; omega)
                                    exact hrec16 (thlen', ti + 1#64, ()) mt'
                                      (by dsimp only; rw [hti1]; omega) hL16'
                                  · intro Jt hJt
                                    c0_hsplit
                                    · have htl_lt_init : tl.toNat < init_nlits := by
                                        have hm1 : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
                                          Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)
                                        have hm2 :
                                            2 * s.core.cur_vars % 2 ^ 64 = 2 * s.core.cur_vars :=
                                          Nat.mod_eq_of_lt hcv_lt64
                                        dsimp only [tl, init_nlits] at hc ⊢
                                        rw [hm1, hm2] at hc; exact hc
                                      clear hc
                                      have htl_lt : tl.toNat < 2 * stt.core.cur_vars := by
                                        rw [hcvt]; exact Nat.lt_of_lt_of_le htl_lt_init hinit_le_cv3
                                      have htl_rc_lt :
                                          (BitVec.setWidth 64
                                            (stt.scratch.work_stk2[ti.toNat]'hti_lt_ws2)).toNat <
                                            stt.scratch.tarjan_reach.length := by
                                        rw [m7_bv64_32, htl.scratch_ok.tarjan_reach_len]
                                        change tl.toNat < 2 * c.max_vars
                                        have := htl.core_ok.cur_vars_le; omega
                                      c0_hfast_nogrp
                                      refine wp_join_state1 (t := i32) (α := BitVec 32) id L16Inv
                                        (fun _ thl' mt' h => hJt thl' mt' h) ?_
                                      intro Jp hJp
                                      c0_hsplit
                                      · have hp_lt :
                                            (stt.scratch.tarjan_reach[(BitVec.setWidth 64
                                              (stt.scratch.work_stk2[ti.toNat]'hti_lt_ws2)).toNat]'
                                                htl_rc_lt).toNat < thlen.toNat := by
                                          simpa only [m7_bv64_32] using hc
                                        clear hc
                                        c0_hfast_nogrp
                                        refine m7_wp_call_fheap_up hUp hinvt hmaxv hp_lt
                                          (by rw [hcvt]; exact hthl_le)
                                          (fun i hi => by rw [hcvt]; exact hthp i hi) hmt
                                          fun st_u1 m_u1 hinv_u1 hcore_u1 hws2_u1 hhp_u1 hm_u1 => ?_
                                        have h1l := hinv_u1.1.lengths
                                        have hcv_u1 : st_u1.core.cur_vars = stt.core.cur_vars :=
                                          congrArg (·.cur_vars) hcore_u1
                                        have hfu_u1 : st_u1.core.fuel = stt.core.fuel :=
                                          congrArg (·.fuel) hcore_u1
                                        have htl_rc_u1 :
                                            (BitVec.setWidth 64
                                              (st_u1.scratch.work_stk2[ti.toNat]'(by
                                                rw [hws2_u1]; exact hti_lt_ws2))).toNat <
                                              st_u1.scratch.tarjan_reach.length := by
                                          rw [m7_bv64_32, h1l.scratch_ok.tarjan_reach_len]
                                          have hteq :
                                              (st_u1.scratch.work_stk2[ti.toNat]'(by
                                                rw [hws2_u1]; exact hti_lt_ws2)) = tl := by
                                            simp only [tl, hws2_u1]
                                          rw [hteq]
                                          have := h1l.core_ok.cur_vars_le; omega
                                        have htl_rc_u1_eq :
                                            (BitVec.setWidth 64
                                              (stt.scratch.work_stk2[ti.toNat]'hti_lt_ws2)).toNat <
                                              st_u1.scratch.tarjan_reach.length := by
                                          simpa only [hws2_u1] using htl_rc_u1
                                        c0_hfast_nogrp
                                        refine wp_join0 (L16Inv thlen)
                                          (fun _ mu2 h => by
                                            c0_hfast_nogrp
                                            exact hJp thlen mu2 h) ?_
                                        intro Jd2 hJd2
                                        c0_hsplit
                                        · have hp2_lt :
                                              (st_u1.scratch.tarjan_reach[(BitVec.setWidth 64
                                                (stt.scratch.work_stk2[ti.toNat]'
                                                  hti_lt_ws2)).toNat]'
                                                  htl_rc_u1_eq).toNat < thlen.toNat := by
                                            simpa only [m7_bv64_32] using hc
                                          clear hc
                                          c0_hfast_nogrp
                                          refine m7_wp_call_fheap_down hDown hinv_u1 hmaxv hp2_lt
                                            (by rw [hcv_u1, hcvt]; exact hthl_le)
                                            (fun k hk => by rw [hcv_u1]; exact hhp_u1 k hk) hm_u1
                                            fun st_u2 m_u2 hinv_u2 hcore_u2 _ hhp_u2 hm_u2 => ?_
                                          c0_hfast_nogrp
                                          exact hJd2 m_u2
                                            ⟨st_u2, hinv_u2,
                                              by rw [congrArg (·.cur_vars) hcore_u2, hcv_u1, hcvt],
                                              by rw [congrArg (·.fuel) hcore_u2, hfu_u1, hfut],
                                              hthl_le,
                                              fun k hk => by
                                                rw [← hcvt, ← hcv_u1]; exact hhp_u2 k hk,
                                              hm_u2⟩
                                        · clear hc
                                          c0_hfast_nogrp
                                          exact hJd2 m_u1
                                            ⟨st_u1, hinv_u1, by rw [hcv_u1, hcvt],
                                              by rw [hfu_u1, hfut], hthl_le,
                                              fun k hk => by rw [← hcvt]; exact hhp_u1 k hk, hm_u1⟩
                                      · clear hc
                                        refine wp_join_state1 (t := i32) (α := BitVec 32) id L16Inv
                                          (fun _ thl' mt' h => hJp thl' mt' h) ?_
                                        intro Je hJe
                                        c0_hsplit
                                        · have hth_lt_init : thlen.toNat < init_nlits := by
                                            have hm1 :
                                                s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
                                              Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)
                                            have hm2 :
                                                2 * s.core.cur_vars % 2 ^ 64 =
                                                  2 * s.core.cur_vars :=
                                              Nat.mod_eq_of_lt hcv_lt64
                                            dsimp only [init_nlits] at hc ⊢
                                            simpa only [hm1, hm2, m7_bv64_32] using hc
                                          clear hc
                                          have hth_lt_cv : thlen.toNat < 2 * stt.core.cur_vars := by
                                            rw [hcvt]
                                            exact Nat.lt_of_lt_of_le hth_lt_init hinit_le_cv3
                                          c0_hfast_nogrp
                                          refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                            (fun tbit mt1 =>
                                              (tbit = 32#32 ∨ tbit = 64#32) ∧
                                                (FullMem c stt ⋆ R) mt1)
                                            ?_ ?_
                                          · intro _ tbit mt1 ⟨htbit, hmt1⟩
                                            dsimp only [Blocks.get, id]
                                            c0_hfast_nogrp
                                            refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                              L16Inv (fun _ thl' mt' h => hJe thl' mt' h) ?_
                                            intro Jb2 hJb2
                                            have htv_fl_lt :
                                                (BitVec.setWidth 64
                                                  ((stt.scratch.work_stk2[ti.toNat]'hti_lt_ws2) >>>
                                                    (1 : Nat))).toNat < stt.core.flags.length :=
                                              m7_fl_lit_lt htl_lt
                                                (by rw [htl.core_ok.flags_len]
                                                    exact htl.core_ok.cur_vars_le)
                                            have hwv_tl_lt :
                                                (BitVec.setWidth 64
                                                  (stt.scratch.work_stk2[ti.toNat]'hti_lt_ws2) <<<
                                                    (1 : Nat) + 1#64).toNat <
                                                  stt.core.wvec.length :=
                                              m7_wvec_lit_lt htl_lt
                                                (by rw [htl.core_ok.wvec_len]
                                                    exact Nat.mul_le_mul_left 4
                                                      htl.core_ok.cur_vars_le)
                                            have hvl_tl_lt :
                                                (BitVec.setWidth 64
                                                  (stt.scratch.work_stk2[ti.toNat]'
                                                    hti_lt_ws2)).toNat < stt.core.vals.length := by
                                              rw [m7_bv64_32, htl.core_ok.vals_len]
                                              change tl.toNat < 2 * c.max_vars
                                              have := htl.core_ok.cur_vars_le; omega
                                            have hthl_mk_lt :
                                                (BitVec.setWidth 64 thlen).toNat <
                                                  stt.scratch.tarjan_mark.length := by
                                              rw [m7_bv64_32, htl.scratch_ok.tarjan_mark_len]
                                              have := htl.core_ok.cur_vars_le; omega
                                            have hth_add1 :
                                                (thlen + 1#32).toNat = thlen.toNat + 1 :=
                                              m7_bv32_add1_toNat hth_lt_cv
                                                (by change c.max_vars < 2 * 268435456 at hmaxv
                                                    have := htl.core_ok.cur_vars_le; omega)
                                            c0_hfast_nogrp
                                            all_goals
                                              try exact (hJb2 thlen mt1
                                                (hstt_skip thlen mt1 rfl hmt1))
                                            c0_hfast_nogrp
                                            all_goals
                                              try exact (hJb2 thlen mt1
                                                (hstt_skip thlen mt1 rfl hmt1))
                                            have htl_rc_lt2 :
                                                (BitVec.setWidth 64
                                                  (stt.scratch.work_stk2[ti.toNat]'
                                                    hti_lt_ws2)).toNat <
                                                  ({ stt with scratch :=
                                                    { stt.scratch with
                                                      tarjan_mark :=
                                                        stt.scratch.tarjan_mark.set
                                                          (BitVec.setWidth 64 thlen).toNat
                                                          (stt.scratch.work_stk2[ti.toNat]'
                                                            hti_lt_ws2) } } :
                                                    FullState).scratch.tarjan_reach.length := by
                                              simpa only using htl_rc_lt
                                            c0_hfast_nogrp
                                            all_goals
                                              try exact (hJb2 thlen mt1
                                                (hstt_skip thlen mt1 rfl hmt1))
                                            let st_push : FullState :=
                                              { stt with scratch :=
                                                { stt.scratch with
                                                  tarjan_mark :=
                                                    stt.scratch.tarjan_mark.set thlen.toNat tl
                                                  tarjan_reach :=
                                                    stt.scratch.tarjan_reach.set tl.toNat
                                                      thlen } }
                                            have hm_push :
                                                (FullMem c st_push ⋆ R) m := by
                                              dsimp only [st_push, tl]
                                              rw [← m7_bv64_32 thlen, ← m7_bv64_32
                                                (stt.scratch.work_stk2[ti.toNat]'hti_lt_ws2)]
                                              exact hm
                                            have hinv_push : FullDenseInv c F0 st_push :=
                                              fullDenseInv_set_fheap hinvt
                                                (by rw [List.length_set,
                                                      htl.scratch_ok.tarjan_mark_len])
                                                (by rw [List.length_set,
                                                      htl.scratch_ok.tarjan_reach_len])
                                            refine m7_wp_call_fheap_up hUp hinv_push hmaxv
                                              (hlen_chk := thlen.toNat + 1)
                                              (Nat.lt_succ_self _)
                                              (by dsimp [st_push]; omega) ?_ hm_push
                                              fun st_u2 m_u2 hinv_u2 hcore_u2 _ hhp_u2
                                                  hm_u2 => ?_
                                            · intro k hk
                                              exact fheap_push_pre_lt_bv htl_lt
                                                (by rw [htl.scratch_ok.tarjan_mark_len]
                                                    have := htl.core_ok.cur_vars_le; omega)
                                                (fun i hi => by rw [hcvt]; exact hthp i hi)
                                                k (Nat.lt_succ_iff.mp hk)
                                            · c0_hfast_nogrp
                                              exact hJb2 (thlen + 1#32) m_u2
                                                ⟨st_u2, hinv_u2,
                                                  by rw [congrArg (·.cur_vars) hcore_u2,
                                                         hcvt],
                                                  by rw [congrArg (·.fuel) hcore_u2, hfut],
                                                  by rw [hth_add1]; omega,
                                                  fun k hk => by
                                                    rw [hth_add1] at hk
                                                    rw [← hcvt]
                                                    exact hhp_u2 k hk,
                                                  hm_u2⟩
                                          · intro Jtb hJtb
                                            c0_hfast_nogrp
                                            · exact hJtb 64#32 mt ⟨Or.inr rfl, hmt⟩
                                            · exact hJtb 32#32 mt ⟨Or.inl rfl, hmt⟩
                                        · clear hc
                                          c0_hfast_nogrp
                                          exact hJe thlen mt (hstt_skip thlen mt rfl hmt)
                                    · clear hc
                                      c0_hfast_nogrp
                                      exact hJt thlen mt (hstt_skip thlen mt rfl hmt)
                                · -- Exit L_16 -> jump to L_5 (cbud - 1, thlen)
                                  c0_hfast_nogrp
                                  have hbud16 :
                                      ((cbud - 1#64).toNat * (2 * c.max_vars + 1) +
                                          thlen.toNat) <
                                        cbud.toNat * (2 * c.max_vars + 1) + chlen.toNat :=
                                    m7_bud_dec_thlen hcbud_pos (by omega)
                                  exact hrec5 (cbud - 1#64, thlen, stt) mt hbud16
                                    ⟨hinvt,
                                      Nat.le_trans hcvp
                                        (Nat.le_trans (Nat.le_of_eq hcvp1.symm)
                                          (Nat.le_trans hcv3 (Nat.le_of_eq hcvt.symm))),
                                      hfut.trans (hfu3.trans (hfu_p2.trans hfup)),
                                      by rw [hcvt]; exact hthl_le,
                                      fun k hk => by rw [hcvt]; exact hthp k hk, hmt⟩
                            · intro J15 hJ15
                              c0_hfast_nogrp
                              · have hnl_bv :
                                    ((BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat))).toNat ≤
                                      init_nlits := by
                                  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                                    Nat.shiftLeft_eq, Nat.pow_one]
                                  dsimp [init_nlits]
                                  rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                                    Nat.mul_comm, Nat.mod_eq_of_lt hcv_lt64]
                                  exact Nat.le_refl _
                                exact hJ15 (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)) m3
                                  ⟨hnl_bv, hm3⟩
                              · exact hJ15 st3.scratch.res_sz m3 ⟨by
                                  have hmod1 : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
                                    Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)
                                  have hmod2 :
                                      2 * s.core.cur_vars % 2 ^ 64 = 2 * s.core.cur_vars :=
                                    Nat.mod_eq_of_lt hcv_lt64
                                  have hnlt : ¬2 * s.core.cur_vars < st3.scratch.res_sz.toNat := by
                                    simpa [hmod1, hmod2] using hc
                                  dsimp [init_nlits]; omega, hm3⟩
                          · -- `ok = false`
                            c0_hfast_nogrp
                            exact hrec5 (cbud - 1#64, chlen - 1#32, st3) m3 hbud_dec
                              ⟨hinv3,
                                Nat.le_trans hcvp
                                  (Nat.le_trans (Nat.le_of_eq hcvp1.symm) hcv3),
                                hfu3.trans hfu_p2 |>.trans hfup,
                                by omega,
                                fun k hk => by
                                  rw [htm3]; dsimp only [stp2]
                                  exact Nat.lt_of_lt_of_le (hhpp1 k hk)
                                    (by rw [← hcv_p2]; omega),
                                hm3⟩
                      all_goals exact hskip stp1 _ hinvp1 hcvp1 hfup1 hhpp1 (by assumption))
                    (fun Jbit hJbit => by
                      c0_hfast_nogrp
                      · exact hJbit 64#32 mp1 ⟨Or.inr rfl, hmp1⟩
                      · exact hJbit 32#32 mp1 ⟨Or.inl rfl, hmp1⟩))
                (fun Jd hJd => by
                  c0_hfast_nogrp
                  · -- `hlen1 > 0`: move last element to root & `full_fheap_down`
                    have hhlen1_pos : 0 < (chlen - 1#32).toNat := by simpa using hc
                    have hhlen1_sub : (chlen - 1#32).toNat = chlen.toNat - 1 :=
                      m7_bv32_sub1_toNat hchlen_pos
                    have hhlen1_eq64 :
                        (BitVec.setWidth 64 (chlen - 1#32)).toNat = (chlen - 1#32).toNat :=
                      m7_bv64_32 _
                    have h0_lt_d64 :
                        (BitVec.ofNat 64 0).toNat < stp0.scratch.tarjan_mark.length := by
                      simp only [BitVec.toNat_ofNat]; exact h0_lt_hp
                    have hhlen1_lt64 :
                        (BitVec.setWidth 64 (chlen - 1#32)).toNat <
                          stp0.scratch.tarjan_mark.length := by
                      rw [hhlen1_eq64, hpl.scratch_ok.tarjan_mark_len]; omega
                    obtain ⟨last, hlast_def⟩ :
                        ∃ last : BitVec 32,
                          last = stp.scratch.tarjan_mark[(BitVec.setWidth 64 (chlen - 1#32)).toNat]'
                            hhlen1_lt64 := ⟨_, rfl⟩
                    have hlast_lt : last.toNat < 2 * stp.core.cur_vars := by
                      have hh1_lt_p :
                          (chlen - 1#32).toNat < stp.scratch.tarjan_mark.length := by
                        rw [← hhlen1_eq64]; exact hhlen1_lt64
                      have h1 := hhpp (chlen - 1#32).toNat (by rw [hhlen1_sub]; omega)
                      rw [List.getElem?_eq_getElem hh1_lt_p, Option.getD_some] at h1
                      simpa only [hlast_def, hhlen1_eq64] using h1
                    have hlast64_nat : (BitVec.setWidth 64 last).toNat = last.toNat :=
                      m7_bv64_32 last
                    have h0_lt_d : 0 < stp0.scratch.tarjan_mark.length := h0_lt_hp
                    have hlast_lt_ps :
                        (BitVec.setWidth 64
                          (stp.scratch.tarjan_mark[(BitVec.setWidth 64 (chlen - 1#32)).toNat]'
                            hhlen1_lt64)).toNat <
                          stp0.scratch.tarjan_reach.length := by
                      dsimp only [stp0]; rw [List.length_set, hpl.scratch_ok.tarjan_reach_len,
                        ← hlast_def, hlast64_nat]
                      omega
                    c0_hsteps_nogrp
                    dsimp only
                    rw [List.getElem_set_self (by rw [List.length_set]; exact h0_lt_d64)]
                    have hlast_def1 :
                        stp.scratch.tarjan_mark[(BitVec.setWidth 64 (chlen - 1)).toNat]'
                          hhlen1_lt64 = last :=
                      hlast_def.symm
                    rw [hlast_def1]
                    let st_m0 : FullState :=
                      { stp0 with scratch :=
                        { stp0.scratch with tarjan_mark := stp0.scratch.tarjan_mark.set 0 last } }
                    have hz64 : (BitVec.ofNat 64 0).toNat = 0 := rfl
                    replace hm : (FullMem c st_m0 ⋆ R) m := by
                      dsimp only [st_m0, stp0]
                      simp only [hlast_def1, ← hu_def] at hm
                      simp only [hz64, hu64_nat] at hm
                      exact hm
                    have hlast_lt_ps_bv :
                        (BitVec.setWidth 64 last).toNat < st_m0.scratch.tarjan_reach.length := by
                      dsimp only [st_m0, stp0]
                      rw [List.length_set, hpl.scratch_ok.tarjan_reach_len, hlast64_nat]
                      omega
                    c0_hsteps_nogrp
                    let st_d0 : FullState :=
                      { stp0 with scratch :=
                        { stp0.scratch with
                          tarjan_mark := stp0.scratch.tarjan_mark.set 0 last
                          tarjan_reach := stp0.scratch.tarjan_reach.set last.toNat 0#32 } }
                    have hm_d0_eq : (FullMem c st_d0 ⋆ R) m := by
                      dsimp only [st_d0, st_m0]
                      rw [← hlast64_nat]
                      exact hm
                    have hinv_d0 : FullDenseInv c F0 st_d0 :=
                      fullDenseInv_set_fheap hinv_p0
                        (by dsimp [st_d0, stp0]
                            rw [List.length_set, hpl.scratch_ok.tarjan_mark_len])
                        (by dsimp [st_d0, stp0]
                            rw [List.length_set, List.length_set, hpl.scratch_ok.tarjan_reach_len])
                    refine m7_wp_call_fheap_down hDown hinv_d0 hmaxv
                      (by simpa using hhlen1_pos)
                      (by change (chlen - 1#32).toNat ≤ 2 * stp.core.cur_vars
                          rw [hhlen1_sub]; omega)
                      ?_ hm_d0_eq fun st_d1 m_d1 hinv_d hcore_d _ hhp_d hm_d1 => ?_
                    · intro i hi
                      dsimp [st_d0, stp0]
                      by_cases hi0 : i = 0
                      · subst hi0
                        rw [List.getElem?_set_self h0_lt_d, Option.getD_some]; exact hlast_lt
                      · rw [List.getElem?_set_ne (Ne.symm hi0)]
                        exact hhpp i
                          (by rw [show (chlen - 1 : BitVec 32) = chlen - 1#32 from rfl,
                                hhlen1_sub] at hi
                              omega)
                    · exact hJd m_d1 ⟨st_d1, hinv_d, by rw [congrArg (·.cur_vars) hcore_d],
                        by rw [congrArg (·.fuel) hcore_d], hhp_d, hm_d1⟩
                  · refine hJd m ⟨stp0, hinv_p0, rfl, rfl, fun k hk => ?_, ?_⟩
                    · exact hhpp k (by rw [m7_bv32_sub1_toNat hchlen_pos] at hk; omega)
                    · dsimp only [stp0]; rw [← hu64_nat, hu_def]
                      simp only [BitVec.toNat_ofNat] at hm ⊢
                      exact hm)
            · exact hJ6 mp ⟨stp, hinvp, hcvp, hfup, hmp⟩
            · exact hJ6 mp ⟨stp, hinvp, hcvp, hfup, hmp⟩
            · exact hJ6 mp ⟨stp, hinvp, hcvp, hfup, hmp⟩
            · exact hJ6 mp ⟨stp, hinvp, hcvp, hfup, hmp⟩)

/-! ## 3. Standalone `9`-Row `m7BvaFactorSpecTable` & Concrete `Mem 64` Non-Vacuity -/

private theorem m7_wp_noExit_lift {Γ : Env} {rs : List Ty} {e : Expr Val Cont rs}
    {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : wp Γ Q (fun _ _ _ _ => False) e m) : wp Γ Q X e m :=
  wp_mono (fun _ _ hq => hq) (fun _ _ _ _ hf => hf.elim) e m h

private theorem m7_ofTable_iff_of_mem {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} :
    Env.ofTable tbl e.name e.as e.rs xs m Q X ↔ e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact Env.ofTable_cons_self _ _ _ _ _ _
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact (Env.ofTable_cons_ne hne _ _ _ _).trans (ih hmem hnd.2)

/-- Standalone `9`-row external contract table (`3` owned Wave-4F fns + `6` externs,
`noExit = true`) for `m7BvaFactorModule`. -/
def m7BvaFactorSpecTable : List SpecEntry :=
  [ ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarHeapSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fullBvaTryLitHeapSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      FullM4Bva.m4BvaScanCandsSpec, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4Bva.m4BvaFilterRowSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], FullM4Bva.m4BvaCommitSpec, true⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], [], fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], fullFheapDownSpec, true⟩ ]

/-- Standalone specification environment for `m7BvaFactorModule`. -/
def m7BvaFactorEnv : Env :=
  Env.ofTable m7BvaFactorSpecTable

theorem m7BvaFactorSpecTable_nodup :
    (m7BvaFactorSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m7BvaFactorSpecTable_noExit :
    ∀ e ∈ m7BvaFactorSpecTable, e.noExit = true := by
  intro e he
  simp only [m7BvaFactorSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m7BvaFactorEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7BvaFactorEnv f as bs xs m Q X → m7BvaFactorEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7BvaFactorSpecTable_noExit

private theorem m7BvaFactorEnv_mem {e : SpecEntry} (he : e ∈ m7BvaFactorSpecTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (hno : e.noExit = true := by rfl)
    (h : e.spec xs m Q (fun _ _ _ _ => False)) :
    m7BvaFactorEnv e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem he m7BvaFactorSpecTable_nodup
    (by dsimp only [SpecEntry.eff]; rw [hno]; exact h)

private theorem m7BvaFactorEnv_elim {e : SpecEntry} (he : e ∈ m7BvaFactorSpecTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (hno : e.noExit = true := by rfl)
    (h : m7BvaFactorEnv e.name e.as e.rs xs m Q X) :
    e.spec xs m Q (fun _ _ _ _ => False) := by
  have heff := (m7_ofTable_iff_of_mem he m7BvaFactorSpecTable_nodup).mp h
  simpa only [SpecEntry.eff, hno, ↓reduceIte] using heff

/-- Unconditional standalone `ModuleOk` certification of all `3` Wave-4F BVA/factor functions
in `m7BvaFactorModule` against `m7BvaFactorEnv`. -/
theorem m7BvaFactor_moduleOk : ModuleOk m7BvaFactorEnv m7BvaFactorModule := by
  refine Module.moduleOk_of_checkAcyclic m7BvaFactor_acyclic m7BvaFactorFns_wf ?_
  intro fn hfn xs m Q X hs
  have hScan : ∀ a m' Q' X', FullM4Bva.m4BvaScanCandsSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_scan_cands", [i64, i32, i32, i64],
      [i32], FullM4Bva.m4BvaScanCandsSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hPick : ∀ a m' Q' X', fullBvaPickCandSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_pick_cand" [i64, i32, i32] [i32] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_pick_cand", [i64, i32, i32],
      [i32], fullBvaPickCandSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hFilter : ∀ a m' Q' X', FullM4Bva.m4BvaFilterRowSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32]
        a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_filter_row",
      [i64, i32, i32, i32, i32, i32], [i32], FullM4Bva.m4BvaFilterRowSpec, true⟩)
      (by simp [m7BvaFactorSpecTable]) rfl h
  have hCommit : ∀ a m' Q' X', FullM4Bva.m4BvaCommitSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_commit" [i64, i32] [.bool] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_commit", [i64, i32], [.bool],
      FullM4Bva.m4BvaCommitSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hTryLit : ∀ a m' Q' X', fullBvaTryLitHeapSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_try_lit" [i64, i32, i64] [.bool] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_try_lit", [i64, i32, i64], [.bool],
      fullBvaTryLitHeapSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hUp : ∀ a m' Q' X', fullFheapUpSpec a m' Q' X' →
      m7BvaFactorEnv "full_fheap_up" [i64, i64, i64, i32] [] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_fheap_up", [i64, i64, i64, i32], [],
      fullFheapUpSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hDown : ∀ a m' Q' X', fullFheapDownSpec a m' Q' X' →
      m7BvaFactorEnv "full_fheap_down" [i64, i64, i64, i32, i32] [] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_fheap_down", [i64, i64, i64, i32, i32],
      [], fullFheapDownSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  simp only [m7BvaFactorModule, m7BvaFactorFns, List.mem_cons, List.not_mem_nil, or_false]
    at hfn
  rcases hfn with rfl | rfl | rfl
  · exact m7_wp_noExit_lift (full_init_fresh_var_m7_heap_wp m7BvaFactorEnv xs m Q _
      (m7BvaFactorEnv_elim (e := ⟨"full_init_fresh_var", [i64, i32], [],
        fullInitFreshVarHeapSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl hs))
  · exact m7_wp_noExit_lift (full_bva_try_lit_m7_wp m7BvaFactorEnv hScan hPick hFilter
      hCommit xs m Q _ (m7BvaFactorEnv_elim (e := ⟨"full_bva_try_lit", [i64, i32, i64],
        [.bool], fullBvaTryLitHeapSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl hs))
  · exact m7_wp_noExit_lift (full_factor_m7_wp m7BvaFactorEnv hUp hDown hTryLit xs m Q _
      (m7BvaFactorEnv_elim (e := ⟨"full_factor", [i64, i64], [i64],
        fullFactorHeapSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl hs))

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_init_fresh_var_m7`. -/
theorem nv_m7_init_fresh_var :
    Func.wp m7BvaFactorEnv full_init_fresh_var_m7_body
      (nvOneLitCfg.hdr, 0#32, ()) nvBvaDenseMem
      (fun () m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ s'.core.vals[0]?.getD 1#8 = 0#8 ∧
        s'.core.vals[1]?.getD 1#8 = 0#8 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact full_init_fresh_var_m7_heap_wp m7BvaFactorEnv _ _ _ _
    ⟨nvOneLitCfg, nvBvaDenseState, emp, rfl, nvBvaDense_invW.1, by decide, hm,
      fun _ _ _ _ _ _ _ _ m' hlen _ _ _ _ _ _ hv0 hv1 _ _ _ _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen, hv0, hv1, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_try_lit_m7`. -/
theorem nv_m7_bva_try_lit :
    Func.wp m7BvaFactorEnv full_bva_try_lit_m7_body
      (nvOneLitCfg.hdr, 0#32, 1#64, ()) nvBvaDenseMem
      (fun (_ok, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hScan : ∀ a m' Q' X', FullM4Bva.m4BvaScanCandsSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_scan_cands", [i64, i32, i32, i64],
      [i32], FullM4Bva.m4BvaScanCandsSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hPick : ∀ a m' Q' X', fullBvaPickCandSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_pick_cand" [i64, i32, i32] [i32] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_pick_cand", [i64, i32, i32],
      [i32], fullBvaPickCandSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hFilter : ∀ a m' Q' X', FullM4Bva.m4BvaFilterRowSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32]
        a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_filter_row",
      [i64, i32, i32, i32, i32, i32], [i32], FullM4Bva.m4BvaFilterRowSpec, true⟩)
      (by simp [m7BvaFactorSpecTable]) rfl h
  have hCommit : ∀ a m' Q' X', FullM4Bva.m4BvaCommitSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_commit" [i64, i32] [.bool] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_commit", [i64, i32], [.bool],
      FullM4Bva.m4BvaCommitSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  exact full_bva_try_lit_m7_wp m7BvaFactorEnv hScan hPick hFilter hCommit _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense,
      by decide, hm, fun _ s' m' hd _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_factor_m7`. -/
theorem nv_m7_factor :
    Func.wp m7BvaFactorEnv full_factor_m7_body
      (nvOneLitCfg.hdr, 10#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ r = 1#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hUp : ∀ a m' Q' X', fullFheapUpSpec a m' Q' X' →
      m7BvaFactorEnv "full_fheap_up" [i64, i64, i64, i32] [] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_fheap_up", [i64, i64, i64, i32], [],
      fullFheapUpSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hDown : ∀ a m' Q' X', fullFheapDownSpec a m' Q' X' →
      m7BvaFactorEnv "full_fheap_down" [i64, i64, i64, i32, i32] [] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_fheap_down", [i64, i64, i64, i32, i32],
      [], fullFheapDownSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  have hTryLit : ∀ a m' Q' X', fullBvaTryLitHeapSpec a m' Q' X' →
      m7BvaFactorEnv "full_bva_try_lit" [i64, i32, i64] [.bool] a m' Q' X' :=
    fun _ _ _ _ h => m7BvaFactorEnv_mem (e := ⟨"full_bva_try_lit", [i64, i32, i64], [.bool],
      fullBvaTryLitHeapSpec, true⟩) (by simp [m7BvaFactorSpecTable]) rfl h
  exact full_factor_m7_wp m7BvaFactorEnv hUp hDown hTryLit _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, hm,
      fun r s' m' hd _ _ hr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, hr, nvDeduceF0_unsat, hm'⟩⟩

/-! ## 4. Closed `270`-Function Spliced `FullM5` Wave-4F Certification -/

/-- Closed `270`-function Unified M5 + Wave-4F BVA/factor function list (`FullM5.m5Fns` with
`"full_init_fresh_var"`, `"full_bva_try_lit"`, and `"full_factor"` upgraded). -/
def m7BvaFullFns : List Fn :=
  spliceM7BvaFactorFns FullM5.m5Fns

/-- Closed `270`-function compiled module splicing Wave-4F `FullM7BvaFactor` into `FullM5`. -/
def m7BvaFullModule : LeanQbe.T.Module :=
  { fns := m7BvaFullFns, externs := [], exits := [] }

theorem m7BvaFullFns_length : m7BvaFullFns.length = 270 := by
  simp only [m7BvaFullFns, spliceM7BvaFactorFns, List.length_map, FullM5.m5Fns_length]

theorem m7BvaFull_acyclic : m7BvaFullModule.checkAcyclic = true := by
  t_kernel_rfl

theorem m7BvaFull_fns_wf : ∀ f ∈ m7BvaFullFns, f.Wf := by
  intro f hf
  simp only [m7BvaFullFns, spliceM7BvaFactorFns, List.mem_map] at hf
  obtain ⟨orig, horig, rfl⟩ := hf
  split
  · exact m7InitFreshVarFn_wf
  · split
    · exact m7BvaTryLitFn_wf
    · split
      · exact m7FactorFn_wf
      · exact FullM5.m5Fns_wf orig horig

/-- Parametric `270`-function `ModuleOk` lift for `m7BvaFullModule`: any environment `Γ` that
certifies all `FullM5.m5Fns`, supplies the `7` BVA/heap callee contracts, and eliminates the `3`
replaced functions into their canonical `FullBvaHeap` contracts yields `ModuleOk Γ m7BvaFullModule`
with zero re-proof of the `267` unchanged `FullM5` functions. -/
theorem m7BvaFull_moduleOk_of (Γ : Env)
    (hM5 : ∀ fn ∈ FullM5.m5Fns, ∀ xs m Q X,
      Γ fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X)
    (hScan : ∀ a m' Q' X', FullM4Bva.m4BvaScanCandsSpec a m' Q' X' →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m' Q' X')
    (hPick : ∀ a m' Q' X', fullBvaPickCandSpec a m' Q' X' →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m' Q' X')
    (hFilter : ∀ a m' Q' X', FullM4Bva.m4BvaFilterRowSpec a m' Q' X' →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m' Q' X')
    (hCommit : ∀ a m' Q' X', FullM4Bva.m4BvaCommitSpec a m' Q' X' →
      Γ "full_bva_commit" [i64, i32] [.bool] a m' Q' X')
    (hTryLit : ∀ a m' Q' X', fullBvaTryLitHeapSpec a m' Q' X' →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] a m' Q' X')
    (hUp : ∀ a m' Q' X', fullFheapUpSpec a m' Q' X' →
      Γ "full_fheap_up" [i64, i64, i64, i32] [] a m' Q' X')
    (hDown : ∀ a m' Q' X', fullFheapDownSpec a m' Q' X' →
      Γ "full_fheap_down" [i64, i64, i64, i32, i32] [] a m' Q' X')
    (hElimInit : ∀ xs m Q X, Γ "full_init_fresh_var" [i64, i32] [] xs m Q X →
      fullInitFreshVarHeapSpec xs m Q (fun _ _ _ _ => False))
    (hElimTry : ∀ xs m Q X, Γ "full_bva_try_lit" [i64, i32, i64] [.bool] xs m Q X →
      fullBvaTryLitHeapSpec xs m Q (fun _ _ _ _ => False))
    (hElimFac : ∀ xs m Q X, Γ "full_factor" [i64, i64] [i64] xs m Q X →
      fullFactorHeapSpec xs m Q (fun _ _ _ _ => False)) :
    ModuleOk Γ m7BvaFullModule := by
  refine Module.moduleOk_of_checkAcyclic m7BvaFull_acyclic m7BvaFull_fns_wf ?_
  intro fn' hfn'
  simp only [m7BvaFullModule, m7BvaFullFns, spliceM7BvaFactorFns, List.mem_map] at hfn'
  obtain ⟨orig, horig, heq⟩ := hfn'
  by_cases h1 : orig.name = "full_init_fresh_var"
  · simp only [h1, ↓reduceIte] at heq
    subst heq
    intro xs m Q X hs
    exact m7_wp_noExit_lift
      (full_init_fresh_var_m7_heap_wp Γ xs m Q _ (hElimInit xs m Q X hs))
  · by_cases h2 : orig.name = "full_bva_try_lit"
    · simp only [h2, ↓reduceIte] at heq
      subst heq
      intro xs m Q X hs
      exact m7_wp_noExit_lift
        (full_bva_try_lit_m7_wp Γ hScan hPick hFilter hCommit xs m Q _ (hElimTry xs m Q X hs))
    · by_cases h3 : orig.name = "full_factor"
      · simp only [h3, ↓reduceIte] at heq
        subst heq
        intro xs m Q X hs
        exact m7_wp_noExit_lift
          (full_factor_m7_wp Γ hUp hDown hTryLit xs m Q _ (hElimFac xs m Q X hs))
      · simp only [h1, h2, h3, ↓reduceIte] at heq
        subst heq
        exact hM5 orig horig

end LeanQbe.T.Examples.Kissat.FullM7BvaFactor
