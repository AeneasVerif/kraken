/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullIngestLemmas2
import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas2
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.MemLemmas

/-!
# Kissat Fidelity Step-9 BVA Helpers (`FullFidelityStep9ProofBva0`, `S9-P1.2`)

Parametric `(Γ : Env)` helper module (`0` `import all`, `public section`, `0` `@[expose]` on
theorems/lemmas) for Step-9 `FullFidelityStep9.full_bva_commit_body`:
1. `full_fill_u64_m7_step9_wp` (`m7FillU64Spec`), `s9_pWsort_fit`, & `s9_call_fill_u64_wsort`:
   word-wide `cnt` (`wsort`) zero-wipe over `[0 .. cur_vars)`.
2. `toBytes_u32_pair`, `pair32_eq_cell64`, `s9_load_tmp_pair32`, `s9_store_arena_pair32`:
   unaligned/aligned `u64` load/store equivalence for two consecutive `i32` slots in `Mem 64`.
3. `s9BvaLargeWatchExpr` & `s9_bva_large_watch_wp`, `s9BvaLargeTopExpr` & `s9_bva_large_top_wp`:
   Step-9 large-clause copy (`(ncr &&& 1) != 0` `u64` copy + tail / scalar fallback) & watch
   push / rollback threading `(garb_add, irred_add)` cleanly in local registers.
-/

set_option autoImplicit false

local elab "c0_hsteps_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva FullM7MemShrink
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. `full_fill_u64_m7` Step-9 Proof & `wsort` Prefix Wipe Helper -/

private theorem s9_fill_tail_step_inv {xs cur : List (BitVec 64)} {i : Nat} {val : BitVec 64}
    (hlen : cur.length = xs.length) (hlt : i < xs.length)
    (hpre : ∀ k < i, cur[k]? = some val) : ∀ k < i + 1, (cur.set i val)[k]? = some val := by
  intro k hk
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt' | rfl
  · rw [List.getElem?_set_ne (by omega)]; exact hpre k hlt'
  · rw [List.getElem?_set_self (by omega)]

private theorem s9_fill_unroll4_inv {xs cur : List (BitVec 64)} {i : Nat} {val : BitVec 64}
    (hlen : cur.length = xs.length) (hle : i + 4 ≤ xs.length)
    (hpre : ∀ k < i, cur[k]? = some val) :
    ∀ k < i + 4,
      ((((cur.set i val).set (i + 1) val).set (i + 2) val).set (i + 3) val)[k]? =
        some val := by
  have h1 : (cur.set i val).length = xs.length := by simp [hlen]
  have hp1 := s9_fill_tail_step_inv hlen (by omega) hpre
  have h2 : ((cur.set i val).set (i + 1) val).length = xs.length := by simp [h1]
  have hp2 := s9_fill_tail_step_inv h1 (by omega) hp1
  have h3 : (((cur.set i val).set (i + 1) val).set (i + 2) val).length = xs.length := by simp [h2]
  exact s9_fill_tail_step_inv h3 (by omega) (s9_fill_tail_step_inv h2 (by omega) hp2)

private theorem s9_list_eq_replicate {α : Type _} {xs : List α} {v : α}
    (h : ∀ k < xs.length, xs[k]? = some v) : xs = List.replicate xs.length v := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi' := h i hi
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hi'
    rw [List.getElem_replicate]
    exact hi'

theorem full_fill_u64_m7_step9_wp (Γ : Env) :
    ∀ a m Q X, m7FillU64Spec a m Q X →
      Func.wp Γ FullFidelityStep9.full_fill_u64_m7_body a m Q X := by
  rintro ⟨dst, n, val, _⟩ m Q X hspec
  rw [m7FillU64Spec_eq] at hspec
  obtain ⟨xs, R, hn, hfit, hm, hpost⟩ := hspec
  unfold FullFidelityStep9.full_fill_u64_m7_body; dsimp only [Func.wp]
  have hnl : xs.length ≤ 2 ^ 61 := by omega
  have hn_bv : n = BitVec.ofNat 64 xs.length := by
    apply BitVec.eq_of_toNat_eq; simp [hn]; omega
  subst hn_bv
  c0_hsteps_nogrp
  refine wp_while_state1 (α := Nat × List (BitVec 64)) (proj := fun st => BitVec.ofNat 64 st.1)
    (μ := fun st => xs.length - st.1)
    (Inv := fun st m' => st.1 ≤ xs.length ∧ st.2.length = xs.length ∧
      (∀ k < st.1, st.2[k]? = some val) ∧ (array64 dst st.2 ⋆ R) m')
    ?_ ?_
  · intro J hJ; exact hJ (0, xs) m ⟨by omega, rfl, fun _ hk => by omega, hm⟩
  · rintro J1 ⟨i, cur⟩ m1 ⟨hi, hcl, hpre, hm1⟩ ih1
    dsimp only at hi hcl hpre hm1
    dsimp only [Blocks.get]; c0_hsplit
    · rw [show BitVec.toNat 4 = 4 from by decide] at hc
      have hle : i + 4 ≤ xs.length := by omega
      c0_hsteps
      have hi0 : (BitVec.ofNat 64 i).toNat = i := by simp; omega
      have hi1 : (BitVec.ofNat 64 i + 1).toNat = i + 1 := by simp [BitVec.toNat_add]; omega
      have hi2 : (BitVec.ofNat 64 i + 2).toNat = i + 2 := by simp [BitVec.toNat_add]; omega
      have hi3 : (BitVec.ofNat 64 i + 3).toNat = i + 3 := by simp [BitVec.toNat_add]; omega
      rw [hi0, hi1, hi2, hi3] at hm
      have hst : BitVec.ofNat 64 i + 4 = BitVec.ofNat 64 (i + 4) := by
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
      rw [hst]
      exact ih1 (i + 4, _) m (by omega) ⟨hle, by simp [hcl], s9_fill_unroll4_inv hcl hle hpre, hm⟩
    · rw [show BitVec.toNat 4 = 4 from by decide] at hc
      have hgt : xs.length < i + 4 := by omega
      c0_hsteps_nogrp
      refine wp_while_state1 (α := Nat × List (BitVec 64))
        (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => xs.length - st.1)
        (Inv := fun st m' => st.1 ≤ xs.length ∧ st.2.length = xs.length ∧
          (∀ k < st.1, st.2[k]? = some val) ∧ (array64 dst st.2 ⋆ R) m')
        (fun J2 hJ2 => hJ2 (i, cur) m1 ⟨hi, hcl, hpre, hm1⟩) ?_
      rintro J2 ⟨j, cur2⟩ m2 ⟨hj, hcl2, hpre2, hm2⟩ ih2
      dsimp only at hj hcl2 hpre2 hm2
      dsimp only [Blocks.get]; c0_hsplit
      · have hjlt : j < xs.length := by omega
        c0_hsteps
        rw [show (BitVec.ofNat 64 j).toNat = j from by simp; omega] at hm
        have hst : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
          rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
        rw [hst]
        exact ih2 (j + 1, cur2.set j val) m (by omega)
          ⟨hjlt, by simp [hcl2], s9_fill_tail_step_inv hcl2 hjlt hpre2, hm⟩
      · have hj_eq : j = xs.length := by omega
        c0_hsteps
        apply hpost
        have hrep : cur2 = List.replicate xs.length val := by
          rw [s9_list_eq_replicate (xs := cur2) (v := val)
            (fun k hk => hpre2 k (by rw [hcl2] at hk; omega)), hcl2]
        rw [hrep] at hm2
        simpa [hn] using hm2

theorem s9_pWsort_fit (c : FullCfg) {cv : Nat} (hcv : cv ≤ c.max_vars) :
    c.pWsort.toNat + 8 * cv ≤ 2 ^ 64 := by
  have hfit := c.havail_fit; have hsz := c.hsize; have hmx := c.hmaxv
  have hmd_pos := fullMinDepthOf_pos c.max_vars
  unfold fullFixedBytes at hsz
  unfold dimacsBound at hmx
  have hpw : c.pWsort = c.hdr + BitVec.ofNat 64
      (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
        15 * u32FullBytes c.max_vars + 24 * c.max_vars) := by
    unfold FullCfg.pWsort FullCfg.pRepr FullCfg.pWvec FullCfg.pFrameDec FullCfg.pFrameTrail
      FullCfg.pQStamp FullCfg.pQNext FullCfg.pQPrev FullCfg.pShrinkStk FullCfg.pMinClr FullCfg.pPos
      FullCfg.pHeap FullCfg.pTmp FullCfg.pTrailPos FullCfg.pTrail FullCfg.pReason FullCfg.pLevel
      FullCfg.pFlags FullCfg.pWalkBest FullCfg.pPhasesBest FullCfg.pPhasesTarget FullCfg.pPhases
      FullCfg.pMark FullCfg.pLitMark FullCfg.pWalkVals FullCfg.pVals
    repeat rw [ptr_add_ofNat]
    exact congrArg (fun n => c.hdr + BitVec.ofNat 64 n) (by omega)
  let off := 1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
    15 * u32FullBytes c.max_vars + 24 * c.max_vars
  have hoff_le : off + 8 * c.max_vars ≤ c.avail := by dsimp only [off]; omega
  have hoff_nat : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpwn : c.pWsort.toNat = c.hdr.toNat + off := by
    rw [hpw, BitVec.toNat_add, hoff_nat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem s9_focus_wsort {c : FullCfg} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c st ⋆ R) m) :
    (array (t := i32) c.pWsort st.scratch.wsort ⋆
      (array (t := i32) c.pWorkStk1 st.scratch.work_stk1 ⋆
       array (t := i32) c.pWorkStk2 st.scratch.work_stk2 ⋆
       array (t := i32) c.pTarjanMark st.scratch.tarjan_mark ⋆
       array (t := i32) c.pTarjanReach st.scratch.tarjan_reach ⋆
       (FullScrByteArrs c st.scratch ⋆ FullScrU32A c st.scratch ⋆
        FullScrMetaArrs c st.scratch ⋆ FullScrDynArrs c st.scratch ⋆
        fullScrOuter c st) ⋆ R)) m := by
  have h1 := hm
  rw [fullMem_eq_scrWks] at h1
  unfold FullScrWksArrs at h1
  exact sep_ac h1

private theorem s9_unfocus_wsort {c : FullCfg} {st : FullState} {ws' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pWsort ws' ⋆
      (array (t := i32) c.pWorkStk1 st.scratch.work_stk1 ⋆
       array (t := i32) c.pWorkStk2 st.scratch.work_stk2 ⋆
       array (t := i32) c.pTarjanMark st.scratch.tarjan_mark ⋆
       array (t := i32) c.pTarjanReach st.scratch.tarjan_reach ⋆
       (FullScrByteArrs c st.scratch ⋆ FullScrU32A c st.scratch ⋆
        FullScrMetaArrs c st.scratch ⋆ FullScrDynArrs c st.scratch ⋆
        fullScrOuter c st) ⋆ R)) m) :
    (FullMem c { st with scratch := { st.scratch with wsort := ws' } } ⋆ R) m := by
  have h0 : FullMem c { st with scratch := { st.scratch with wsort := ws' } } =
      (array (t := i32) c.pWsort ws' ⋆
        (array (t := i32) c.pWorkStk1 st.scratch.work_stk1 ⋆
         array (t := i32) c.pWorkStk2 st.scratch.work_stk2 ⋆
         array (t := i32) c.pTarjanMark st.scratch.tarjan_mark ⋆
         array (t := i32) c.pTarjanReach st.scratch.tarjan_reach ⋆
         (FullScrByteArrs c st.scratch ⋆ FullScrU32A c st.scratch ⋆
          FullScrMetaArrs c st.scratch ⋆ FullScrDynArrs c st.scratch ⋆
          fullScrOuter c st))) := by
    rw [fullMem_eq_scrWks]; unfold FullScrWksArrs; dsimp only; ac_rfl
  rw [h0, sep_assoc]
  exact hm

theorem s9_call_fill_u64_wsort {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFillU64 : ∀ a m Q X, m7FillU64Spec a m Q X →
      Γ "full_fill_u64_m7" [i64, i64, i64] [] a m Q X)
    {c : FullCfg} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {a0 a1 a2 : Arg Val i64} {k : Tup Val [] → Expr Val Cont rs}
    (hws_len : st.scratch.wsort.length = 2 * c.max_vars)
    (hcv_le : st.core.cur_vars ≤ c.max_vars)
    (ha0 : a0.val = c.pWsort)
    (ha1 : a1.val = BitVec.ofNat 64 st.core.cur_vars)
    (ha2 : a2.val = 0#64)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ ws' : List (BitVec 32), ∀ m' : Mem 64, ws'.length = 2 * c.max_vars →
      (FullMem c { st with scratch := { st.scratch with wsort := ws' } } ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64]) (bs := []) "full_fill_u64_m7"
      (a0, a1, a2, ()) k)
      m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  let cv := st.core.cur_vars
  have htake_len : (st.scratch.wsort.take (2 * cv)).length = 2 * cv := by
    rw [List.length_take_of_le (by omega)]
  have hfit_cv : 8 * cv ≤ 2 ^ 64 := by omega
  have hm_foc := s9_focus_wsort hm
  have hsplit : array (t := i32) c.pWsort st.scratch.wsort =
      (array (t := i32) c.pWsort (st.scratch.wsort.take (2 * cv)) ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * cv)))
         (st.scratch.wsort.drop (2 * cv))) := by
    conv => lhs; rw [← List.take_append_drop (2 * cv) st.scratch.wsort]
    rw [array_append, htake_len]; rfl
  rw [hsplit, sep_assoc] at hm_foc
  obtain ⟨ys, hys_len, hm_u64⟩ := array_i32_to_u64_exact htake_len hfit_cv hm_foc
  have hcv_nat : (BitVec.ofNat 64 cv).toNat = cv := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine wp_call_of_spec _ _ (hFillU64 _ _ _ _ ?_)
  rw [m7FillU64Spec_eq]
  dsimp only [vals]
  rw [ha0, ha1, ha2]
  refine ⟨ys, _, by rw [hcv_nat, hys_len], by rw [hys_len]; exact s9_pWsort_fit c hcv_le,
    hm_u64, fun m' hm' => ?_⟩
  rw [hcv_nat] at hm'
  have hm_i32 := array64_rep_to_i32_exact hfit_cv bytes64_zero_i32 hm'
  let ws' := List.replicate (2 * cv) 0#32 ++ st.scratch.wsort.drop (2 * cv)
  have hws'_len : ws'.length = 2 * c.max_vars := by
    dsimp only [ws']; simp [List.length_drop, hws_len]; omega
  refine hk ws' m' hws'_len (s9_unfocus_wsort ?_)
  dsimp only [ws']
  rw [array_append (t := i32),
    show Ty.bytes i32 * (List.replicate (2 * cv) 0#32).length = 4 * (2 * cv) by
      simp [Ty.bytes, Ty.size]]
  rwa [sep_assoc]

/-! ## 2. `u32` Pair / `cell64` Equivalence & Direct `Mem 64` Pair Accessors -/

private theorem nat_add_pow2_eq_or : ∀ (n a b : Nat), a < 2 ^ n →
    a + 2 ^ n * b = a ||| (b <<< n)
  | 0, a, b, ha => by
    have : a = 0 := by omega
    subst this; simp [Nat.shiftLeft_eq]
  | n + 1, a, b, ha => by
    apply Nat.eq_of_testBit_eq; intro k; cases k with
    | zero =>
      have hpow : 2 ^ (n + 1) * b = 2 * (2 ^ n * b) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
      have ha2 : (a + 2 ^ (n + 1) * b) % 2 = a % 2 := by rw [hpow]; omega
      have hb2 : (b <<< (n + 1)) % 2 = 0 := by
        rw [Nat.shiftLeft_eq, Nat.pow_succ, ← Nat.mul_assoc]
        exact Nat.mul_mod_left (b * 2 ^ n) 2
      simp [Nat.testBit_zero, ha2, hb2]
    | succ k =>
      have ih := nat_add_pow2_eq_or n (a / 2) b (by omega)
      have hpow : 2 ^ (n + 1) * b = 2 * (2 ^ n * b) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
      have h1 : (a + 2 ^ (n + 1) * b) / 2 = a / 2 + 2 ^ n * b := by rw [hpow]; omega
      have h2 : (b <<< (n + 1)) / 2 = b <<< n := by
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.pow_succ, ← Nat.mul_assoc,
          Nat.mul_div_cancel _ (by decide)]
      rw [Nat.testBit_succ, Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, h1, h2, ih,
        Nat.testBit_or]

private theorem toBytes_split8 : ∀ (k m a b : Nat), a < 2 ^ (8 * k) →
    Int.toBytes (k + m) ((a + 2 ^ (8 * k) * b : Nat) : Int) =
      Int.toBytes k (a : Int) ++ Int.toBytes m (b : Int)
  | 0, m, a, b, ha => by
    have : a = 0 := by omega
    subst this; simp [Int.toBytes]
  | k + 1, m, a, b, ha => by
    have hk : 2 ^ (8 * (k + 1)) = 256 * 2 ^ (8 * k) := by
      have hmul : 8 * (k + 1) = 8 * k + 8 := by omega
      rw [hmul, Nat.pow_add, show 2 ^ 8 = 256 from rfl, Nat.mul_comm]
    have hsplit : a + 2 ^ (8 * (k + 1)) * b = a + 256 * (2 ^ (8 * k) * b) := by
      rw [hk, Nat.mul_assoc]
    have hmod : (((a + 2 ^ (8 * (k + 1)) * b : Nat) : Int).take 8) = ((a : Int).take 8) := by
      unfold Int.take
      rw [show (2 : Int) ^ 8 = 256 from rfl, hsplit, Int.natCast_add, Int.natCast_mul,
        show ((256 : Nat) : Int) = 256 from rfl]
      exact Int.add_mul_emod_self_left (a : Int) 256 _
    have hdiv : ((a + 2 ^ (8 * (k + 1)) * b : Nat) : Int) / 256 =
        ((a / 256 + 2 ^ (8 * k) * b : Nat) : Int) := by
      rw [show (256 : Int) = ((256 : Nat) : Int) from rfl, ← Int.natCast_ediv, hsplit,
        Nat.add_mul_div_left _ _ (by decide)]
    have ha' : a / 256 < 2 ^ (8 * k) := by rw [hk] at ha; omega
    have ih := toBytes_split8 k m (a / 256) b ha'
    rw [Nat.add_right_comm k 1 m]
    dsimp only [Int.toBytes]
    rw [hmod, hdiv, ih, show (256 : Int) = ((256 : Nat) : Int) from rfl, ← Int.natCast_ediv]
    rfl

private theorem toBytes_bv_toInt_eq_toNat {n : Nat} (_hn : 1 ≤ n) (x : BitVec (8 * n)) :
    Int.toBytes n x.toInt = Int.toBytes n (x.toNat : Int) := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (x.toNat : Int))]
  congr 1; dsimp only [Int.take]
  have h1 := x.isLt
  have hpow : (2 : Int) ^ (8 * n) = ((2 ^ (8 * n) : Nat) : Int) := by push_cast; rfl
  rw [hpow, BitVec.toInt_eq_toNat_cond]
  split
  · rfl
  · rw [Int.sub_emod_right]

theorem toBytes_u32_pair (x0 x1 : BitVec 32) :
    Int.toBytes 8 (x0.setWidth 64 ||| (x1.setWidth 64 <<< 32)).toInt =
      Int.toBytes 4 x0.toInt ++ Int.toBytes 4 x1.toInt := by
  let w : BitVec 64 := x0.setWidth 64 ||| (x1.setWidth 64 <<< 32)
  have hw_nat : w.toNat = x0.toNat + 2 ^ 32 * x1.toNat := by
    have hx0 : (x0.setWidth 64).toNat = x0.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hx1 : (x1.setWidth 64 <<< 32).toNat = x1.toNat <<< 32 := by
      have hlt : x1.toNat * 2 ^ 32 < 2 ^ 64 := by have := x1.isLt; omega
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (a := x1.toNat) (by omega),
        Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt, ← Nat.shiftLeft_eq]
    dsimp only [w]
    rw [BitVec.toNat_or, hx0, hx1, ← nat_add_pow2_eq_or 32 x0.toNat x1.toNat x0.isLt]
  rw [toBytes_bv_toInt_eq_toNat (n := 8) (by decide) w,
    toBytes_bv_toInt_eq_toNat (n := 4) (by decide) x0,
    toBytes_bv_toInt_eq_toNat (n := 4) (by decide) x1, hw_nat]
  exact toBytes_split8 4 4 x0.toNat x1.toNat x0.isLt

theorem pair32_eq_cell64 (a : BitVec 64) (x0 x1 : BitVec 32) :
    array (t := i32) a [x0, x1] = cell64 a (x0.setWidth 64 ||| (x1.setWidth 64 <<< 32)) := by
  funext m; apply propext; constructor
  · intro hm
    have hbm := array_eq_bytesOf (t := i32) a [x0, x1] (by simp [Ty.bytes, Ty.size, i32]) hm
    have hbo : bytesOf (t := i32) [x0, x1] =
        Int.toBytes 8 (x0.setWidth 64 ||| (x1.setWidth 64 <<< 32)).toInt := by
      unfold bytesOf; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact (toBytes_u32_pair x0 x1).symm
    change (Int.toBytes 8 (x0.setWidth 64 ||| (x1.setWidth 64 <<< 32)).toInt).At a = m
    rw [← hbo]; exact hbm.symm
  · intro hm
    change (Int.toBytes 8 (x0.setWidth 64 ||| (x1.setWidth 64 <<< 32)).toInt).At a = m at hm
    rw [toBytes_u32_pair x0 x1] at hm
    have hbm : m = (bytesOf (t := i32) [x0, x1]).At a := hm.symm
    rw [hbm]
    exact array_bytes (t := i32) a [x0, x1] (by simp [Ty.bytes, Ty.size, i32])

private theorem list_pair_split {α : Type _} (xs : List α) {i : Nat} (hi : i + 1 < xs.length) :
    xs = xs.take i ++ [xs[i], xs[i + 1]] ++ xs.drop (i + 2) := by
  have h1 : xs.drop i = xs[i] :: xs.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
  have h2 : xs.drop (i + 1) = xs[i + 1] :: xs.drop (i + 2) := List.drop_eq_getElem_cons hi
  conv => lhs; rw [← List.take_append_drop i xs, h1, h2]
  simp [List.append_assoc]

private theorem list_set2_split {α : Type _} (xs : List α) {i : Nat} (hi : i + 1 < xs.length)
    (v0 v1 : α) :
    (xs.set i v0).set (i + 1) v1 = xs.take i ++ [v0, v1] ++ xs.drop (i + 2) := by
  have hl0 : (xs.set i v0).length = xs.length := List.length_set
  have hl1 : ((xs.set i v0).set (i + 1) v1).length = xs.length := by simp [hl0]
  have hi_s : i + 1 < ((xs.set i v0).set (i + 1) v1).length := by omega
  have hs := list_pair_split ((xs.set i v0).set (i + 1) v1) hi_s
  have htk : ((xs.set i v0).set (i + 1) v1).take i = xs.take i := by
    rw [List.take_set_of_le (by omega), List.take_set_of_le (Nat.le_refl i)]
  have hg0 : ((xs.set i v0).set (i + 1) v1)[i]'(by omega) = v0 := by
    rw [List.getElem_set_ne (by omega), List.getElem_set_self (by omega)]
  have hg1 : ((xs.set i v0).set (i + 1) v1)[i + 1]'hi_s = v1 := by
    rw [List.getElem_set_self (by omega)]
  have hdr : ((xs.set i v0).set (i + 1) v1).drop (i + 2) = xs.drop (i + 2) := by
    rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]
  rw [hs, htk, hg0, hg1, hdr]

private theorem array_focus_pair32 (a : BitVec 64) (xs : List (BitVec 32)) {i : Nat}
    (hi : i + 1 < xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (4 * i))
        (xs[i].setWidth 64 ||| (xs[i + 1].setWidth 64 <<< 32)) ⋆
       (array (t := i32) a (xs.take i) ⋆
        array (t := i32) (a + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 8)
          (xs.drop (i + 2)))) := by
  conv => lhs; rw [list_pair_split xs hi]
  rw [List.append_assoc, array_append (t := i32), array_append (t := i32),
    List.length_take_of_le (by omega), pair32_eq_cell64]
  simp only [Ty.bytes, Ty.size, i32, List.length_cons, List.length_nil]
  rw [show (32 + 7) / 8 * i = 4 * i by omega,
    show (32 + 7) / 8 * (0 + 1 + 1) = 8 from by decide,
    show BitVec.ofNat 64 8 = 8#64 from rfl, ← sep_assoc,
    sep_comm (array (t := i32) a (xs.take i)), sep_assoc]

theorem s9_load_pair32 {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i + 1 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (4 * i)) =
      some (xs[i].setWidth 64 ||| (xs[i + 1].setWidth 64 <<< 32)) := by
  rw [array_focus_pair32 a xs hi, sep_assoc] at hm
  exact loadVal_cell64 hm

theorem s9_store_pair32 {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat} (v0 v1 : BitVec 32)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i + 1 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) a ((xs.set i v0).set (i + 1) v1) ⋆ R)
        (storeMem m i64 (a + BitVec.ofNat 64 (4 * i))
          (v0.setWidth 64 ||| (v1.setWidth 64 <<< 32))) := by
  have hm1 := hm
  rw [array_focus_pair32 a xs hi, sep_assoc] at hm1
  obtain ⟨hok, hst⟩ := store_cell64 (v0.setWidth 64 ||| (v1.setWidth 64 <<< 32)) hm1
  refine ⟨hok, ?_⟩
  have heq : array (t := i32) a ((xs.set i v0).set (i + 1) v1) =
      (cell64 (a + BitVec.ofNat 64 (4 * i)) (v0.setWidth 64 ||| (v1.setWidth 64 <<< 32)) ⋆
       (array (t := i32) a (xs.take i) ⋆
        array (t := i32) (a + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 8)
          (xs.drop (i + 2)))) := by
    have hsplit := list_set2_split xs hi v0 v1
    conv => lhs; rw [hsplit]
    rw [List.append_assoc, array_append (t := i32), array_append (t := i32),
      List.length_take_of_le (by omega), pair32_eq_cell64]
    simp only [Ty.bytes, Ty.size, i32, List.length_cons, List.length_nil]
    rw [show (32 + 7) / 8 * i = 4 * i by omega,
      show (32 + 7) / 8 * (0 + 1 + 1) = 8 from by decide,
      show BitVec.ofNat 64 8 = 8#64 from rfl, ← sep_assoc,
      sep_comm (array (t := i32) a (xs.take i)), sep_assoc]
  rwa [heq, sep_assoc]

theorem s9_load_tmp_pair32 {c : FullCfg} {s : FullState} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i + 1 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pTmp + BitVec.ofNat 64 (4 * i)) =
      some (s.core.tmp[i].setWidth 64 ||| (s.core.tmp[i + 1].setWidth 64 <<< 32)) := by
  have hm1 := hm
  rw [fullMem_eq_coreU32A] at hm1
  unfold FullCoreU32A at hm1
  exact s9_load_pair32 hi (by ecancel)

theorem s9_store_arena_pair32 {c : FullCfg} {s : FullState} {i : Nat} (v0 v1 : BitVec 32)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i + 1 < s.core.arena.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pArena + BitVec.ofNat 64 (4 * i)) ∧
      (FullMem c { s with core := { s.core with arena := (s.core.arena.set i v0).set (i + 1) v1 } }
        ⋆ R) (storeMem m i64 (c.pArena + BitVec.ofNat 64 (4 * i))
          (v0.setWidth 64 ||| (v1.setWidth 64 <<< 32))) := by
  have hm1 := hm
  rw [fullMem_eq_coreDyn] at hm1
  unfold FullCoreDynArrs at hm1
  rw [sep_assoc, sep_assoc] at hm1
  obtain ⟨hok, hst⟩ := s9_store_pair32 (xs := s.core.arena) v0 v1 hi hm1
  refine ⟨hok, ?_⟩
  let s' : FullState :=
    { s with core := { s.core with arena := (s.core.arena.set i v0).set (i + 1) v1 } }
  have hc : FullCoreByteArrs c s'.core = FullCoreByteArrs c s.core := rfl
  have hua : FullCoreU32A c s'.core = FullCoreU32A c s.core := rfl
  have hub : FullCoreU32B c s'.core = FullCoreU32B c s.core := rfl
  have hou : fullCoreOuter c s' = fullCoreOuter c s := rfl
  rw [fullMem_eq_coreDyn c s', hc, hua, hub, hou]
  unfold FullCoreDynArrs; dsimp only [s']
  rwa [sep_assoc, sep_assoc]

/-! ## 3. Local Shared Helpers (`S7StOk` Transitions) -/

private theorem s9_nodup_lt_length_le : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.zero_le _
  | 0, x :: _, _, hlt => absurd (hlt x (by simp)) (by omega)
  | n + 1, xs, hnd, hlt => by
    by_cases hn : n ∈ xs
    · have hperm := List.perm_cons_erase hn; have hnd' := List.nodup_cons.mp (hnd.perm hperm)
      have hlt' : ∀ y ∈ xs.erase n, y < n := fun y hy => by
        have hmem := List.mem_of_mem_erase hy
        have hne : y ≠ n := fun he => by subst he; exact hnd'.1 hy
        have := hlt y hmem; omega
      have ih := s9_nodup_lt_length_le hnd'.2 hlt'
      have hlen := hperm.length_eq; simp only [List.length_cons] at hlen; omega
    · have hlt' : ∀ y ∈ xs, y < n := fun y hy => by
        have hne : y ≠ n := fun he => by subst he; exact hn hy
        have := hlt y hy; omega
      exact Nat.le_trans (s9_nodup_lt_length_le hnd hlt') (Nat.le_succ _)

theorem s9_fullDenseInvW_of_append_clause {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {sz : Nat}
    (hsz3 : 3 ≤ sz) {ar' wvec' wstk' fl' wsort' : List (BitVec 32)} {wlen' : Nat}
    {wu' ni' : BitVec 64}
    (hlen' : let k' := { s.core with
      arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', flags := fl', num_irred := ni' }
      ({ s with core := k', scratch := { s.scratch with wsort := wsort' } } :
        FullState).LengthsOk c)
    (hhold : ∀ i < s.core.arena_len, ar'[i]? = s.core.arena[i]?)
    (hns : (ar'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_new : (ar'[s.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (hlits_lt : ∀ l ∈ fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len,
      l < 2 * s.core.cur_vars)
    (hlits_nd : ((fullArenaClauseLitsCore { s.core with arena := ar' }
      s.core.arena_len).map (· / 2)).Nodup)
    (hlits_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len)))
    (hwat' : ModeWatchesInv F_cur { s.core with
      arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', flags := fl', num_irred := ni' }) :
    let s' : FullState := { s with
      core := { s.core with
        arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
        wlen := wlen', wusable := wu', flags := fl', num_irred := ni' },
      scratch := { s.scratch with wsort := wsort' } }
    FullDenseInvW c F0 F_cur s' ∧ FidBvaArenaMono s.core s'.core := by
  intro s'; have hw := hinv.2.1; have hcl := hinv.1.core_ok
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + sz)
    (by omega) hhold
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hsz3 rfl hhold hns hsz_new
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1; unfold fullArenaClauseGarbCore fullArenaHdrCore s'
    simp [hhold r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1; unfold fullArenaClauseSizeCore s'
    simp [hhold (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    exact fullArenaClauseLitsCore_congr (hold_sz r hr) fun j hj => hhold (r + 3 + j) (by omega)
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr; rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + sz := by unfold fullArenaNextOff s'; simp [hsz_new, hns]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = sz from hsz_new]
        refine ⟨by dsimp [s']; omega, hsz3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh; rwa [hhold r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hns hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · exact hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · exact hlits_ent
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by
      have := hw.lvl_le idx hidx; have := hinv.2.2.2.2.2.1; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat',
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne,
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  have hnodup' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr; rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng; rw [hold_garb r hr] at hng
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [hold_lits r hr]; exact hinv.2.2.2.1 r hr hng
    · exact hlits_nd
  have hext' : FullExtScratchOk c s' := ⟨(fun i hi => by
    rcases hinv.2.2.2.2.1.1 i hi with h1 | h2
    · exact Or.inl h1
    · refine Or.inr ?_
      change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact List.mem_append_left _ h2),
    hinv.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnodup', hext', hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩,
    fun r hr => ⟨by rw [hrefs]; exact List.mem_append_left _ hr, hold_sz r hr, hold_lits r hr⟩⟩

theorem s9_fullDenseInvW_with_num_irred {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (ni' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with num_irred := ni' } } :=
  ⟨⟨{ hinv.1.core_ok with vals_len := hinv.1.core_ok.vals_len }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem s9_fullDenseInvW_set_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {tmp' : List (BitVec 32)} (htmp : tmp'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    hinv hinv.1.core_ok.repr_len hinv.1.core_ok.min_clr_len_arr htmp hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le hinv.1.scratch_ok rfl rfl

theorem s9_fullArenaLitsCore_eq_map {k : FullCoreState} {r sz : Nat}
    (hsz : fullArenaClauseSizeCore k r = sz) (hb : r + 3 + sz ≤ k.arena.length) :
    fullArenaClauseLitsCore k r =
      (List.range sz).map (fun j => (k.arena[r + 3 + j]?.getD 0#32).toNat) := by
  apply List.ext_getElem?; intro j; by_cases hj : j < sz
  · rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega),
      List.getElem?_map, List.getElem?_range hj, Option.map_some,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_eq_none (by
        rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by omega), hsz]; omega),
      List.getElem?_eq_none (by simp; omega)]

theorem s9_bv32_lit_mask_eq {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

private theorem s9_wp_jump_eq {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {L : Cont ts} {args : Tup (Arg Val) ts} {m : Mem 64} :
    wp Γ Q X (.jump L args) m = L (vals args) m := rfl

private theorem s9_is_wp_goal {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {e : Expr Val Cont rs} {m : Mem 64} (h : wp Γ Q X e m) : wp Γ Q X e m := h

local macro "s9_hsteps_to_jump" : tactic =>
  `(tactic| repeat (
    apply s9_is_wp_goal
    first | (rw [s9_wp_jump_eq]; dsimp only [vals, Arg.val]) | c0_hstep))

private theorem s9_dst_cl_ptr (pAr : BitVec 64) (ncr0 j : Nat) :
    (pAr + (BitVec.ofNat 64 ncr0 + 3#64) * 4#64) + BitVec.ofNat 64 j * 4#64 =
      pAr + BitVec.ofNat 64 (4 * (ncr0 + 3 + j)) := by
  rw [BitVec.add_assoc]; congr 1
  rw [← BitVec.add_mul, show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl,
    show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_mul, Nat.mul_comm]

private theorem s9_sw64_32 (x : BitVec 32) :
    BitVec.setWidth 64 x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-! ## 4. Step-9 Large-Clause Copy (`u64` + Scalar), Watch-Push & Subtree Expressions -/

@[expose] def s9BZext (a : Arg Val i32) (k : Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (a, ()) } fun p => k p.fst
@[expose] def s9BOp64 (op : OpCode [i64, i64] [i64]) (a b : Arg Val i64)
    (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i64, i64], code := op, args := (a, b, ()) } fun p => k p.fst
@[expose] def s9BOp32 (op : OpCode [i32, i32] [i32]) (a b : Arg Val i32)
    (k : Val i32 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32, i32], code := op, args := (a, b, ()) } fun p => k p.fst
@[expose] def s9BCmp32 (op : CmpOp) (a b : Arg Val i32)
    (k : Val .bool → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32, i32], code := OpCode.cmp op i32, args := (a, b, ()) } fun p => k p.fst
@[expose] def s9BPtr32 (base idx : Val i64) (k : Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  s9BOp64 (.mul i64) (Arg.var idx) (Arg.imm 4) fun off =>
    s9BOp64 (.add i64) (Arg.var base) (Arg.var off) k
@[expose] def s9BLd32 (base idx : Val i64) (k : Val i32 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] := s9BPtr32 base idx fun ptr => Expr.load i32 (Arg.var ptr) k

@[expose] def s9BvaLargeWatchExpr (h pAr pFl pTmp : Val i64) (tk : Val i32)
    (ncr garb_add irred_add : Val i64) (dd : Val .bool)
    (Jtop : Cont [.bool, .bool, i64, i64]) : Expr Val Cont [.bool] :=
  Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [.bool, i64, i32]) =>
    Expr.group (fun _ => Blocks.cons (fun (pir : Tup Val [i64]) =>
      Expr.jump Jtop (Arg.var dd, Arg.var p.fst, Arg.var p.snd.fst, Arg.var pir.fst, ()))
      Blocks.nil) fun Jir =>
    Expr.jnz (Arg.var p.fst)
      (s9BOp64 (.add i64) (Arg.var irred_add) (Arg.imm 1) fun ia1 =>
        Expr.jump Jir.fst (Arg.var ia1, ()))
      (Expr.jump Jir.fst (Arg.var irred_add, ()))) Blocks.nil) fun Jw_exit =>
  Expr.group (fun Jw => Blocks.cons (fun (pj : Tup Val [i32]) =>
    s9BCmp32 .ult (Arg.var pj.fst) (Arg.var tk) fun c => Expr.jnz (Arg.var c)
      (s9BZext (Arg.var pj.fst) fun j64 => s9BLd32 pTmp j64 fun lj =>
       s9BOp32 (.and i32) (Arg.var tk) (Arg.imm 2147483647) fun tkm =>
       Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var ncr, ()) } fun n32 =>
       Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
         (Arg.var h, Arg.var lj, Arg.var tkm, Arg.var n32.fst, Arg.imm 2, ()) fun okw =>
       Expr.jnz (Arg.var okw.fst)
         (s9BZext (Arg.var pj.fst) fun j64b => s9BLd32 pTmp j64b fun ljb =>
          s9BOp32 (.lshr i32) (Arg.var ljb) (Arg.imm 1) fun tv =>
          s9BZext (Arg.var tv) fun tv64 => s9BPtr32 pFl tv64 fun pfv =>
          s9BZext (Arg.var tv) fun tv64b => s9BLd32 pFl tv64b fun flv =>
          Expr.group (fun _ => Blocks.cons (fun (pf : Tup Val [i32]) =>
            s9BOp32 (.or i32) (Arg.var flv) (Arg.var pf.fst) fun nfl =>
            Expr.store (Arg.var nfl) (Arg.var pfv) (s9BOp32 (.add i32) (Arg.var pj.fst)
              (Arg.imm 1) fun j1 => Expr.jump Jw.fst (Arg.var j1, ()))) Blocks.nil) fun Jt =>
          s9BZext (Arg.var pj.fst) fun j64c => s9BLd32 pTmp j64c fun ljc =>
          s9BOp32 (.and i32) (Arg.var ljc) (Arg.imm 1) fun b1 =>
          s9BCmp32 .ne (Arg.var b1) (Arg.imm 0) fun c1 =>
          Expr.jnz (Arg.var c1) (Expr.jump Jt.fst (Arg.imm 64, ()))
            (Expr.jump Jt.fst (Arg.imm 32, ())))
         (Expr.group (fun Juk => Blocks.cons (fun (pu : Tup Val [i32]) =>
            s9BCmp32 .ult (Arg.var pu.fst) (Arg.var pj.fst) fun cu => Expr.jnz (Arg.var cu)
              (s9BZext (Arg.var pu.fst) fun u64 => s9BLd32 pTmp u64 fun lu =>
               Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var ncr, ()) }
                 fun n32u => Expr.call "full_unwatch_large" (as := [i64, i32, i32]) (bs := [])
                 (Arg.var h, Arg.var lu, Arg.var n32u.fst, ()) fun _ =>
               s9BOp32 (.add i32) (Arg.var pu.fst) (Arg.imm 1) fun u1 =>
               Expr.jump Juk.fst (Arg.var u1, ()))
              (s9BPtr32 pAr ncr fun par1 => s9BLd32 pAr ncr fun hdrv => s9BOp32 (.or i32)
                 (Arg.var hdrv) (Arg.imm 524288) fun nhdr => Expr.store (Arg.var nhdr)
                 (Arg.var par1) (s9BOp64 (.add i64) (Arg.var garb_add) (Arg.imm 3) fun g3 =>
                  s9BZext (Arg.var tk) fun tk64 => s9BOp64 (.add i64) (Arg.var g3) (Arg.var tk64)
                    fun gn => Expr.jump Jw_exit.fst (Arg.imm false, Arg.var gn, Arg.var pj.fst,
                      ())))) Blocks.nil)
          fun Juk => Expr.jump Juk.fst (Arg.imm 0, ())))
      (Expr.jump Jw_exit.fst (Arg.var true, Arg.var garb_add, Arg.var pj.fst, ()))) Blocks.nil)
  fun Jw => Expr.jump Jw.fst (Arg.imm 0, ())

@[expose] def s9BvaCopyExpr (dst_cl pTmp : Val i64) (tk : Val i32) (ncr : Val i64)
    (Jcp : Cont [i32]) : Expr Val Cont [.bool] :=
  s9BOp64 (.and i64) (Arg.var ncr) (Arg.imm 1) fun nb =>
  Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ne i64,
              args := (Arg.var nb, Arg.imm 0, ()) } fun cne =>
  Expr.jnz (Arg.var cne.fst)
    (Expr.group (fun Ju => Blocks.cons (fun (pju : Tup Val [i32]) =>
      s9BOp32 (.add i32) (Arg.var pju.fst) (Arg.imm 2) fun j2 =>
      s9BCmp32 .ule (Arg.var j2) (Arg.var tk) fun c2 =>
      Expr.jnz (Arg.var c2)
        (s9BZext (Arg.var pju.fst) fun j64a => s9BPtr32 dst_cl j64a fun dp =>
         s9BZext (Arg.var pju.fst) fun j64b => s9BPtr32 pTmp j64b fun sp =>
         Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun z0 =>
         s9BOp64 (.mul i64) (Arg.var z0.fst) (Arg.imm 8) fun z08 =>
         s9BOp64 (.add i64) (Arg.var dp) (Arg.var z08) fun dp0 =>
         Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun z1 =>
         s9BOp64 (.mul i64) (Arg.var z1.fst) (Arg.imm 8) fun z18 =>
         s9BOp64 (.add i64) (Arg.var sp) (Arg.var z18) fun sp0 =>
         Expr.load i64 (Arg.var sp0) fun w => Expr.store (Arg.var w) (Arg.var dp0)
           (s9BOp32 (.add i32) (Arg.var pju.fst) (Arg.imm 2) fun j2' =>
             Expr.jump Ju.fst (Arg.var j2', ())))
        (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
          Expr.jump Jcp (Arg.var pju.fst, ())) Blocks.nil) fun Jif1 =>
         s9BCmp32 .ult (Arg.var pju.fst) (Arg.var tk) fun clt => Expr.jnz (Arg.var clt)
           (s9BZext (Arg.var pju.fst) fun j64c => s9BPtr32 dst_cl j64c fun dp1 =>
            s9BZext (Arg.var pju.fst) fun j64d => s9BLd32 pTmp j64d fun tv =>
            Expr.store (Arg.var tv) (Arg.var dp1) (Expr.jump Jif1.fst ()))
           (Expr.jump Jif1.fst ()))) Blocks.nil)
     fun Ju => Expr.jump Ju.fst (Arg.imm 0, ()))
    (Expr.group (fun Jsc => Blocks.cons (fun (pjc : Tup Val [i32]) =>
      s9BCmp32 .ult (Arg.var pjc.fst) (Arg.var tk) fun cjc => Expr.jnz (Arg.var cjc)
        (s9BZext (Arg.var pjc.fst) fun jc64 => s9BPtr32 dst_cl jc64 fun parj =>
         s9BZext (Arg.var pjc.fst) fun jc64b => s9BLd32 pTmp jc64b fun tv =>
         Expr.store (Arg.var tv) (Arg.var parj) (s9BOp32 (.add i32) (Arg.var pjc.fst) (Arg.imm 1)
           fun jc1 => Expr.jump Jsc.fst (Arg.var jc1, ())))
        (Expr.jump Jcp (Arg.var pjc.fst, ()))) Blocks.nil)
     fun Jsc => Expr.jump Jsc.fst (Arg.imm 0, ()))

@[expose] def s9BvaLargeTopExpr (h pAr pFl pTmp : Val i64)
    (mi c_top csz flit fresh : Val i32) (dd : Val .bool) (garb_add irred_add : Val i64)
    (J1b : Cont [i32, .bool, .bool, i64, i64]) (Jtop : Cont [.bool, .bool, i64, i64]) :
    Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun z64 =>
  s9BPtr32 pTmp z64.fst fun ptmp0 => s9BOp32 (.xor i32) (Arg.var fresh) (Arg.imm 1) fun f1 =>
  Expr.store (Arg.var f1) (Arg.var ptmp0)
    (Expr.group (fun Jf => Blocks.cons (fun (pf : Tup Val [i32, i32]) =>
      s9BCmp32 .ult (Arg.var pf.snd.fst) (Arg.var csz) fun c => Expr.jnz (Arg.var c)
        (s9BZext (Arg.var c_top) fun ct64b => s9BOp64 (.add i64) (Arg.var ct64b) (Arg.imm 3)
           fun ct3 => s9BZext (Arg.var pf.snd.fst) fun j64 => s9BOp64 (.add i64) (Arg.var ct3)
           (Arg.var j64) fun idx => s9BLd32 pAr idx fun l => Expr.group (fun _ => Blocks.cons
           (fun (ptk : Tup Val [i32]) => s9BOp32 (.add i32) (Arg.var pf.snd.fst) (Arg.imm 1)
             fun j1 => Expr.jump Jf.fst (Arg.var ptk.fst, Arg.var j1, ())) Blocks.nil) fun Jif =>
         s9BCmp32 .ne (Arg.var l) (Arg.var flit) fun cne => Expr.jnz (Arg.var cne)
           (s9BZext (Arg.var pf.fst) fun tk64 => s9BPtr32 pTmp tk64 fun ptmpt => Expr.store
              (Arg.var l) (Arg.var ptmpt) (s9BOp32 (.add i32) (Arg.var pf.fst) (Arg.imm 1)
                fun tk1 => Expr.jump Jif.fst (Arg.var tk1, ())))
           (Expr.jump Jif.fst (Arg.var pf.fst, ())))
        (Expr.call "full_alloc_cl" (as := [i64, i32, i32, .bool]) (bs := [i64])
           (Arg.var h, Arg.var pf.fst, Arg.imm 0, Arg.imm false, ()) fun pncr =>
         Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64,
                     args := (Arg.var pncr.fst, Arg.imm 4294967295, ()) } fun ceq =>
         Expr.jnz (Arg.var ceq.fst)
           (Expr.jump J1b (Arg.var mi, Arg.var dd, Arg.imm false, Arg.var garb_add,
             Arg.var irred_add, ()))
           (s9BOp64 (.add i64) (Arg.var pncr.fst) (Arg.imm 3) fun n3 =>
            s9BOp64 (.mul i64) (Arg.var n3) (Arg.imm 4) fun n3_4 =>
            s9BOp64 (.add i64) (Arg.var pAr) (Arg.var n3_4) fun dst_cl =>
            Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val [i32]) =>
              s9BvaLargeWatchExpr h pAr pFl pTmp pf.fst pncr.fst garb_add irred_add dd Jtop)
              Blocks.nil)
            fun Jcp => s9BvaCopyExpr dst_cl pTmp pf.fst pncr.fst Jcp.fst))) Blocks.nil)
     fun Jf => Expr.jump Jf.fst (Arg.imm 1, Arg.imm 0, ()))

/-! ## 5. Large-Clause Copy (`u64` / Scalar) & Watch-Push WP over `S7StOk` -/

theorem s9_bva_large_watch_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hWPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {tk : Val i32} {garb_add irred_add : Val i64} {dd : Val .bool}
    {Jtop : Cont [.bool, .bool, i64, i64]} {tmpj arj : List (BitVec 32)} {mjc : Mem 64}
    (hstm : S7StOk c F0 F_next s stm) (htmpj_l : tmpj.length = c.max_vars)
    (htk_ge3 : 3 ≤ tk.toNat) (htk_le_mv : tk.toNat ≤ c.max_vars)
    (hncr_cap : stm.core.arena_len + 3 + tk.toNat ≤ c.arena_cap)
    (hhold_j : ∀ i < stm.core.arena_len, arj[i]? = stm.core.arena[i]?)
    (hns_cp : (arj[stm.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_cp : (arj[stm.core.arena_len + 2]?.getD 0#32).toNat = tk.toNat)
    (hnew_lt : ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arj } stm.core.arena_len,
      l < 2 * stm.core.cur_vars)
    (hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arj }
      stm.core.arena_len).map (· / 2)).Nodup)
    (hnew_ent : (cnfOfClauses F_next).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arj } stm.core.arena_len)))
    (htmp_lt : ∀ t (ht : t < tk.toNat),
      (tmpj[t]'(by rw [htmpj_l]; omega)).toNat < 2 * (s.core.cur_vars + 1))
    (hlen_cp : ({ stm with core := { stm.core with
        tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } } :
      FullState).LengthsOk c)
    (hrefs_cp : fullArenaClauseRefsCore
        { stm.core with
          tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } =
      fullArenaClauseRefsCore stm.core ++ [stm.core.arena_len])
    (hwat_cp : ModeWatchesInv F_next
      { stm.core with tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat })
    (hmjc : (FullMem c { stm with core := { stm.core with
      tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } } ⋆ R) mjc)
    (hDone : ∀ (ok' : Bool) (ga' ia' : Val i64) st1 m1, (FullMem c st1 ⋆ R) m1 →
      S7StOk c F0 F_next s st1 → Jtop (dd, ok', ga', ia', ()) m1) :
    wp Γ Q X (s9BvaLargeWatchExpr c.hdr c.pArena c.pFlags c.pTmp tk
      (BitVec.ofNat 64 stm.core.arena_len) garb_add irred_add dd Jtop) mjc := by
  obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ := hstm
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hclm := hinvm.1.core_ok; let old_cv := s.core.cur_vars; let ncr0 := stm.core.arena_len
  let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
  have hinv_tmp : FullDenseInvW c F0 F_next st_tmp := s9_fullDenseInvW_set_tmp hinvm htmpj_l
  let st_cp : FullState :=
    { st_tmp with core := { st_tmp.core with arena := arj, arena_len := ncr0 + 3 + tk.toNat } }
  have hncr_nat : (BitVec.ofNat 64 ncr0).toNat = ncr0 := by have := hclm.arena_len_le; c0_bound
  have hcv_le := hclm.cur_vars_le
  have htk_lt31 : tk.toNat < 2 ^ 31 := by omega
  dsimp only [s9BvaLargeWatchExpr, s9BZext, s9BOp64, s9BOp32, s9BCmp32, s9BPtr32, s9BLd32]
  refine wp_join_group (ts := [.bool, i64, i32])
    (fun (ok', ga', _, ()) mw => ∃ stw : FullState,
      (FullMem c stw ⋆ R) mw ∧ S7StOk c F0 F_next s stw)
    (fun _ (ok', ga', _, ()) mw ⟨stw, hmw, hstw⟩ => by
      refine wp_join_group (ts := [i64]) (fun _ m1 => m1 = mw)
        (fun _ (ia', ()) m1 hm1 => by
          subst m1; s9_hsteps_to_jump; exact hDone ok' ga' ia' stw mw hmw hstw)
        (fun Jir hJir => by
          c0_hsplit
          · s9_hsteps_to_jump; exact hJir (irred_add + 1#64, ()) mw rfl
          · s9_hsteps_to_jump; exact hJir (irred_add, ()) mw rfl))
    (fun Jw_exit hJw_exit => ?_)
  refine wp_loop_inv
    (fun (jw, ()) mjw => ∃ wvecw wstkw flw wsortw wlenw wuw, jw.toNat ≤ tk.toNat ∧
      let sw : FullState :=
        { st_cp with core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                               wusable := wuw, flags := flw }
                     scratch := { st_cp.scratch with wsort := wsortw } }
      sw.LengthsOk c ∧ ModeWatchesInv F_next sw.core ∧ (FullMem c sw ⋆ R) mjw)
    (fun (jw, _) _ => tk.toNat - jw.toNat) (fun Jw hJw => by
      s9_hsteps_to_jump; exact hJw (0#32, ()) mjc
        ⟨st_cp.core.wvec, st_cp.core.wstk, st_cp.core.flags,
         st_cp.scratch.wsort, st_cp.core.wlen, st_cp.core.wusable, Nat.zero_le _,
         hlen_cp, hwat_cp, hmjc⟩)
    (fun Jw (jw, ()) mjw ⟨wvecw, wstkw, flw, wsortw, wlenw, wuw, hjw_le, hlenw,
        hwatw, hmjw⟩ ihw => ?_)
  let sw : FullState :=
    { st_cp with core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                           wusable := wuw, flags := flw }
                 scratch := { st_cp.scratch with wsort := wsortw } }
  c0_hsplit
  · have hjw_lt : jw.toNat < tk.toNat := by c0_bound
    have hjw1 : (jw + 1#32).toNat = jw.toNat + 1 := by c0_bound
    have hjw_tmp : jw.toNat < tmpj.length := by omega
    have hjw_tmp_sw : (BitVec.setWidth 64 jw).toNat < sw.core.tmp.length := by
      rw [bv64_setWidth_32]; exact hjw_tmp
    have htk_mask : (tk &&& (2147483647 : BitVec 32)) = tk := s9_bv32_lit_mask_eq htk_lt31
    have htk_ne : (tk &&& (2147483647 : BitVec 32)) ≠ 0xFFFFFFFF#32 := by
      rw [htk_mask]; intro h; have := congrArg BitVec.toNat h
      have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    have hncr32_nat : (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat = ncr0 := by
      have := hclm.arena_len_le; c0_bound
    have hncr32_ne : BitVec.setWidth 32 (BitVec.ofNat 64 ncr0) ≠ 0xFFFFFFFF#32 := by
      intro h; have := congrArg BitVec.toNat h; rw [hncr32_nat] at this
      have := hclm.arena_len_le; have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    c0_hsteps; c0_call hWPush
    refine ⟨c, sw, R, rfl, hlenw, hwatw.layout, (fun h => absurd h (by decide)),
      (fun _ => ⟨htk_ne, hncr32_ne⟩), hmjw,
      fun okw wvec' wstk' wlen' wu' wsort' mw' hlenw' hlayw' hothw hokt hokf hmw' => ?_⟩
    have hwatw' : ModeWatchesInv F_next
        { sw.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } := by
      refine fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hwatw hlayw'
        rfl rfl (fun _ hr => hr) (fun h => absurd h (by decide)) ?_ hothw hokt
        (fun hf => (hokf hf).1)
      intro _; have htk_nb : (tk &&& 0x80000000#32) = 0#32 :=
        bv32_bin_flag_zero_of_lt htk_lt31
      refine ⟨by rw [htk_mask]; exact htk_nb, fun _ => by rw [htk_mask]; omega,
        by rw [hncr32_nat]; have := hclm.arena_len_le; omega, ?_⟩
      change (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat ∈ fullArenaClauseRefsCore st_cp.core
      rw [hncr32_nat, hrefs_cp]; exact List.mem_append_right _ (by dsimp only [ncr0]; simp)
    have htv_shr : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
        rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : BitVec 32))).toNat < flw.length := by
      rw [bv64_setWidth_32, bv32_lshr1_bv, hlenw'.core_ok.flags_len]
      simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
    have htv_shr_n : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
        rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : Nat))).toNat < flw.length := by
      rw [bv64_setWidth_32, bv32_lshr1_nat, hlenw'.core_ok.flags_len]
      simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
    c0_hsteps_nogrp
    · c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (_ : Tup Val [i32]) mf => mf = mw')
        (fun _ _ mf hmf => by
          subst mf; s9_hsteps_to_jump
          refine ihw (jw + 1#32, ()) m (by dsimp only; rw [hjw1]; omega)
            ⟨wvec', wstk', _, wsort', wlen', wu', by rw [hjw1]; omega, ?_, ?_, hm⟩
          · exact ⟨{ hlenw'.core_ok with flags_len := by simp [hlenw'.core_ok.flags_len] },
              hlenw'.scratch_ok⟩
          · exact hwatw'.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr))
        (fun Jt hJt => by
          c0_hsplit
          · s9_hsteps_to_jump; exact hJt (64#32, ()) mw' rfl
          · s9_hsteps_to_jump; exact hJt (32#32, ()) mw' rfl)
    · let sw_fail : FullState :=
        { sw with core := { sw.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                         wusable := wu' }
                  scratch := { sw.scratch with wsort := wsort' } }
      refine wp_loop_inv
        (fun (uk, ()) muk => ∃ wvecu wstku wuu, uk.toNat ≤ jw.toNat ∧ let su : FullState :=
            { sw_fail with core := { sw_fail.core with wvec := wvecu, wstk := wstku,
                                                       wusable := wuu } }
          su.LengthsOk c ∧ ModeWatchesInv F_next su.core ∧ (FullMem c su ⋆ R) muk)
        (fun (uk, _) _ => jw.toNat - uk.toNat) (fun Juk hJuk => by
          s9_hsteps_to_jump
          exact hJuk (0#32, ()) mw' ⟨wvec', wstk', wu', Nat.zero_le _, hlenw', hwatw', hmw'⟩)
        (fun Juk (uk, ()) muk ⟨wvecu, wstku, wuu, huk_le, hlenu, hwatu, hmuk⟩ ihuk => ?_)
      let su : FullState :=
        { sw_fail with core := { sw_fail.core with wvec := wvecu, wstk := wstku, wusable := wuu } }
      c0_hsplit
      · have huk_lt : uk.toNat < jw.toNat := by c0_bound
        have huk1 : (uk + 1#32).toNat = uk.toNat + 1 := by c0_bound
        have huk_tmp : (BitVec.setWidth 64 uk).toNat < su.core.tmp.length := by
          rw [bv64_setWidth_32, hlenu.core_ok.tmp_len_arr]; omega
        c0_hsteps; c0_call hUnwatch; refine ⟨c, su, R, rfl, hlenu, hwatu.layout, hmuk,
          fun wvecu' wstku' wuu' mu' hlenu' _ hwatu' hmu' => ?_⟩
        s9_hsteps_to_jump; exact ihuk (uk + 1#32, ()) mu' (by dsimp only; rw [huk1]; omega)
          ⟨wvecu', wstku', wuu', by rw [huk1]; omega, hlenu', hwatu' F_next hwatu, hmu'⟩
      · have hncr_ar_u : (BitVec.ofNat 64 ncr0).toNat < su.core.arena.length := by
          rw [hncr_nat, hlenu.core_ok.arena_len_arr]; omega
        s9_hsteps_to_jump; have ⟨hinv_app, hmono_app⟩ := s9_fullDenseInvW_of_append_clause hinv_tmp
          htk_ge3 hlenu hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwatu
        have hncr_ref : ncr0 ∈ fullArenaClauseRefsCore su.core := by
          change ncr0 ∈ fullArenaClauseRefsCore st_cp.core
          rw [hrefs_cp]; exact List.mem_append_right _ (by dsimp only [ncr0]; simp)
        have ⟨hinv_mg, hmono_mg⟩ :=
          fullDenseInvW_of_markGarb hinv_app hncr_ref su.core.arena_garbage
        have hm_mg : (FullMem c { su with core := { su.core with
            arena := su.core.arena.set ncr0
              (fullArenaHdrCore su.core ncr0 ||| 0x00080000#32) } } ⋆ R) m := by
          have hhdr : fullArenaHdrCore su.core ncr0 =
              su.core.arena[ncr0]'(by rw [hlenu.core_ok.arena_len_arr]; omega) := by
            unfold fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by rw [hlenu.core_ok.arena_len_arr]; omega),
              Option.getD_some]
          rw [hhdr]; dsimp only [ncr0] at hncr_nat ⊢
          simp only [hncr_nat, show (524288 : BitVec 32) = 0x00080000#32 from rfl] at hm ⊢
          exact hm
        exact hJw_exit (false, garb_add + 3#64 + BitVec.setWidth 64 tk, jw, ()) m
          ⟨_, hm_mg, hinv_mg, hcvm, hfuelm, hsbm, htmm, htrm,
            fidBvaArenaMono_trans hmono (fidBvaArenaMono_trans hmono_app hmono_mg), hresm⟩
  · s9_hsteps_to_jump
    have ⟨hinv_app, hmono_app⟩ := s9_fullDenseInvW_of_append_clause hinv_tmp
      htk_ge3 hlenw hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwatw
    exact hJw_exit (true, garb_add, jw, ()) mjw ⟨sw, hmjw, hinv_app, hcvm, hfuelm, hsbm, htmm, htrm,
      fidBvaArenaMono_trans hmono hmono_app, hresm⟩

private theorem s9_store_arena_i32 {c : FullCfg} {s : FullState} {i : Nat} (v : BitVec 32)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < s.core.arena.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pArena + BitVec.ofNat 64 (4 * i)) ∧
      (FullMem c { s with core := { s.core with arena := s.core.arena.set i v } } ⋆ R)
        (storeMem m i32 (c.pArena + BitVec.ofNat 64 (4 * i)) v) := by
  have hm1 := hm; rw [fullMem_eq_coreDyn] at hm1; unfold FullCoreDynArrs at hm1
  rw [sep_assoc, sep_assoc] at hm1
  obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hi hm1
  refine ⟨hok, ?_⟩
  let s' : FullState := { s with core := { s.core with arena := s.core.arena.set i v } }
  have hc : FullCoreByteArrs c s'.core = FullCoreByteArrs c s.core := rfl
  have hua : FullCoreU32A c s'.core = FullCoreU32A c s.core := rfl
  have hub : FullCoreU32B c s'.core = FullCoreU32B c s.core := rfl
  have hou : fullCoreOuter c s' = fullCoreOuter c s := rfl
  rw [fullMem_eq_coreDyn c s', hc, hua, hub, hou]; unfold FullCoreDynArrs; dsimp only [s']
  rwa [sep_assoc, sep_assoc]

private theorem s9_bva_copy_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {stm : FullState} {R : Mem 64 → Prop} {tk : Val i32}
    {tmpj ar1 : List (BitVec 32)} {ncr0 : Nat} {Jcp : Cont [i32]} {ma1 : Mem 64}
    (hmax29 : c.max_vars < 2 ^ 29)
    (htk_le_mv : tk.toNat ≤ c.max_vars)
    (hncr_cap : ncr0 + 3 + tk.toNat ≤ c.arena_cap)
    (har1_len : ar1.length = c.arena_cap)
    (htmpj_l : tmpj.length = c.max_vars)
    (hhold_a1 : ∀ i < ncr0, ar1[i]? = stm.core.arena[i]?)
    (hma1 : (FullMem c { stm with core := { stm.core with
      tmp := tmpj, arena := ar1, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) ma1)
    (hJcp : ∀ (j_out : Val i32) (arj : List (BitVec 32)) (mjc : Mem 64),
      arj.length = c.arena_cap →
      (∀ i < ncr0, arj[i]? = stm.core.arena[i]?) →
      arj[ncr0]? = ar1[ncr0]? →
      arj[ncr0 + 2]? = ar1[ncr0 + 2]? →
      (∀ t < tk.toNat, arj[ncr0 + 3 + t]? = tmpj[t]?) →
      (FullMem c { stm with core := { stm.core with
        tmp := tmpj, arena := arj, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mjc →
      Jcp (j_out, ()) mjc) :
    wp Γ Q X (s9BvaCopyExpr (c.pArena + (BitVec.ofNat 64 ncr0 + 3#64) * 4#64) c.pTmp tk
      (BitVec.ofNat 64 ncr0) Jcp) ma1 := by
  let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
  dsimp only [s9BvaCopyExpr, s9BZext, s9BOp64, s9BOp32, s9BCmp32, s9BPtr32, s9BLd32]
  c0_hsteps_nogrp
  · refine wp_loop_inv
      (fun (ju, ()) mju => ∃ arj : List (BitVec 32), ju.toNat ≤ tk.toNat ∧
        arj.length = c.arena_cap ∧ (∀ i < ncr0, arj[i]? = stm.core.arena[i]?) ∧
        arj[ncr0]? = ar1[ncr0]? ∧ arj[ncr0 + 2]? = ar1[ncr0 + 2]? ∧
        (∀ t < ju.toNat, arj[ncr0 + 3 + t]? = tmpj[t]?) ∧
        (FullMem c { st_tmp with core := { st_tmp.core with
          arena := arj, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mju)
      (fun (ju, _) _ => tk.toNat - ju.toNat) (fun Ju hJu => by
        s9_hsteps_to_jump
        exact hJu (0#32, ()) ma1 ⟨ar1, Nat.zero_le _, har1_len, hhold_a1, rfl, rfl,
          fun _ h => by simp only [bv_c0] at h; omega, hma1⟩)
      (fun Ju (ju, ()) mju ⟨arj, hju_le, harj_l, hhold_j, harj0, harj2, hcp_j, hmju⟩ ihu => ?_)
    have hju2_nat : (ju + 2#32).toNat = ju.toNat + 2 := by
      rw [BitVec.toNat_add, show (2#32 : BitVec 32).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    c0_hsteps_nogrp
    · have hju2_le : ju.toNat + 2 ≤ tk.toNat := by
        have h1 : (ju + 2#32).toNat ≤ tk.toNat := by assumption
        omega
      have hju_tmp : ju.toNat + 1 < tmpj.length := by omega
      have hju_ar : ncr0 + 3 + ju.toNat + 1 < arj.length := by omega
      have hdp_eq : (c.pArena + (BitVec.ofNat 64 ncr0 + 3#64) * 4#64) +
          BitVec.setWidth 64 ju * 4#64 + BitVec.signExtend 64 0#32 * 8#64 =
          c.pArena + BitVec.ofNat 64 (4 * (ncr0 + 3 + ju.toNat)) := by
        rw [show BitVec.signExtend 64 0#32 * 8#64 = 0#64 from by decide, BitVec.add_zero,
          s9_sw64_32]
        exact s9_dst_cl_ptr c.pArena ncr0 ju.toNat
      have hsp_eq : c.pTmp + BitVec.setWidth 64 ju * 4#64 + BitVec.signExtend 64 0#32 * 8#64 =
          c.pTmp + BitVec.ofNat 64 (4 * ju.toNat) := by
        rw [show BitVec.signExtend 64 0#32 * 8#64 = 0#64 from by decide, BitVec.add_zero,
          s9_sw64_32, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          ← BitVec.ofNat_mul, Nat.mul_comm]
      refine head_wp_load (v := ((tmpj[ju.toNat]'(by omega)).setWidth 64 |||
          ((tmpj[ju.toNat + 1]'hju_tmp).setWidth 64 <<< 32))) hsp_eq
        (s9_load_tmp_pair32 (s := { st_tmp with core := { st_tmp.core with
            arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
          (i := ju.toNat) (by dsimp only [st_tmp]; exact hju_tmp) hmju) ?_
      let x0 := tmpj[ju.toNat]'(by omega)
      let x1 := tmpj[ju.toNat + 1]'hju_tmp
      have hst := s9_store_arena_pair32 (s := { st_tmp with core := { st_tmp.core with
          arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
        (i := ncr0 + 3 + ju.toNat) x0 x1 (by dsimp only; omega) hmju
      refine head_wp_store rfl hdp_eq hst fun m' hm' => ?_
      s9_hsteps_to_jump
      let arj' := (arj.set (ncr0 + 3 + ju.toNat) x0).set (ncr0 + 3 + ju.toNat + 1) x1
      refine ihu (ju + 2#32, ()) m' (by dsimp only; rw [hju2_nat]; omega)
        ⟨arj', by rw [hju2_nat]; omega, by simp [arj', harj_l],
         fun i hi => by
           rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
           exact hhold_j i hi,
         by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact harj0,
         by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact harj2,
         fun t ht => ?_, by simpa [arj'] using hm'⟩
      rw [hju2_nat] at ht
      dsimp only [arj']
      by_cases ht1 : t = ju.toNat + 1
      · subst ht1
        rw [← Nat.add_assoc (ncr0 + 3) ju.toNat 1,
          List.getElem?_set_self (by simp [harj_l]; omega), List.getElem?_eq_getElem hju_tmp]
      · by_cases ht0 : t = ju.toNat
        · subst ht0
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
            List.getElem?_eq_getElem (by omega)]
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact hcp_j t (by omega)
    · have hnot : ¬ ju.toNat + 2 ≤ tk.toNat := by
        have h1 : ¬ (ju + 2#32).toNat ≤ tk.toNat := by assumption
        omega
      refine wp_join_group (ts := [])
        (fun (_ : Tup Val []) mf => ∃ arj' : List (BitVec 32),
          arj'.length = c.arena_cap ∧ (∀ i < ncr0, arj'[i]? = stm.core.arena[i]?) ∧
          arj'[ncr0]? = ar1[ncr0]? ∧ arj'[ncr0 + 2]? = ar1[ncr0 + 2]? ∧
          (∀ t < tk.toNat, arj'[ncr0 + 3 + t]? = tmpj[t]?) ∧
          (FullMem c { st_tmp with core := { st_tmp.core with
            arena := arj', arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mf)
        (fun _ _ mf ⟨arj', harj'_l, hhold_j', harj0', harj2', hcp_j', hmf⟩ => by
          s9_hsteps_to_jump; exact hJcp ju arj' mf harj'_l hhold_j' harj0' harj2' hcp_j' hmf)
        (fun Jif1 hJif1 => ?_)
      c0_hsplit
      · have hju_lt : ju.toNat < tk.toNat := by c0_bound
        have hju_eq1 : ju.toNat + 1 = tk.toNat := by omega
        have hju_tmp : ju.toNat < tmpj.length := by omega
        have htmp_ju : (BitVec.setWidth 64 ju).toNat < tmpj.length := by
          rw [bv64_setWidth_32]; exact hju_tmp
        have hdp_eq : (c.pArena + (BitVec.ofNat 64 ncr0 + 3#64) * 4#64) +
            BitVec.setWidth 64 ju * 4#64 =
            c.pArena + BitVec.ofNat 64 (4 * (ncr0 + 3 + ju.toNat)) := by
          rw [s9_sw64_32]; exact s9_dst_cl_ptr c.pArena ncr0 ju.toNat
        have hst := s9_store_arena_i32 (s := { st_tmp with core := { st_tmp.core with
            arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
          (i := ncr0 + 3 + ju.toNat) (tmpj[(BitVec.setWidth 64 ju).toNat]'htmp_ju)
          (by dsimp only; omega) hmju
        c0_hsteps_nogrp
        refine head_wp_store rfl hdp_eq hst fun m' hm' => ?_
        s9_hsteps_to_jump
        refine hJif1 () m' ⟨arj.set (ncr0 + 3 + ju.toNat) _, by simp [harj_l],
          fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hhold_j i hi,
          by rw [List.getElem?_set_ne (by omega)]; exact harj0,
          by rw [List.getElem?_set_ne (by omega)]; exact harj2, fun t ht => ?_, hm'⟩
        by_cases hte : t = ju.toNat
        · subst hte; rw [List.getElem?_set_self (by omega), ← List.getElem?_eq_getElem htmp_ju,
            bv64_setWidth_32]
        · rw [List.getElem?_set_ne (by omega)]; exact hcp_j t (by omega)
      · have hju_eq : ju.toNat = tk.toNat := by c0_bound
        rw [hju_eq] at hcp_j
        s9_hsteps_to_jump; exact hJif1 () mju ⟨arj, harj_l, hhold_j, harj0, harj2, hcp_j, hmju⟩
  · refine wp_loop_inv
      (fun (jc, ()) mjc => ∃ arj : List (BitVec 32), jc.toNat ≤ tk.toNat ∧
        arj.length = c.arena_cap ∧ (∀ i < ncr0, arj[i]? = stm.core.arena[i]?) ∧
        arj[ncr0]? = ar1[ncr0]? ∧ arj[ncr0 + 2]? = ar1[ncr0 + 2]? ∧
        (∀ t < jc.toNat, arj[ncr0 + 3 + t]? = tmpj[t]?) ∧
        (FullMem c { st_tmp with core := { st_tmp.core with
          arena := arj, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mjc)
      (fun (jc, _) _ => tk.toNat - jc.toNat) (fun Jsc hJsc => by
        s9_hsteps_to_jump
        exact hJsc (0#32, ()) ma1 ⟨ar1, Nat.zero_le _, har1_len, hhold_a1, rfl, rfl,
          fun _ h => by simp only [bv_c0] at h; omega, hma1⟩)
      (fun Jsc (jc, ()) mjc ⟨arj, hjc_le, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩ ihsc => ?_)
    c0_hsteps_nogrp
    · have hjc_lt : jc.toNat < tk.toNat := by c0_bound
      have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
      have hjc_tmp : jc.toNat < tmpj.length := by omega
      have htmp_jc : (BitVec.setWidth 64 jc).toNat < tmpj.length := by
        rw [bv64_setWidth_32]; exact hjc_tmp
      have hdp_eq : (c.pArena + (BitVec.ofNat 64 ncr0 + 3#64) * 4#64) +
          BitVec.setWidth 64 jc * 4#64 =
          c.pArena + BitVec.ofNat 64 (4 * (ncr0 + 3 + jc.toNat)) := by
        rw [s9_sw64_32]; exact s9_dst_cl_ptr c.pArena ncr0 jc.toNat
      have hst := s9_store_arena_i32 (s := { st_tmp with core := { st_tmp.core with
          arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
        (i := ncr0 + 3 + jc.toNat) (tmpj[(BitVec.setWidth 64 jc).toNat]'htmp_jc)
        (by dsimp only; omega) hmjc
      c0_hsteps_nogrp
      refine head_wp_store rfl hdp_eq hst fun m' hm' => ?_
      s9_hsteps_to_jump; refine ihsc (jc + 1#32, ()) m' (by dsimp only; rw [hjc1]; omega)
        ⟨arj.set (ncr0 + 3 + jc.toNat) _, by rw [hjc1]; omega, by simp [harj_l],
         fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hhold_j i hi,
         by rw [List.getElem?_set_ne (by omega)]; exact harj0,
         by rw [List.getElem?_set_ne (by omega)]; exact harj2, fun t ht => by
           rw [hjc1] at ht; by_cases hte : t = jc.toNat
           · subst hte; rw [List.getElem?_set_self (by omega), ← List.getElem?_eq_getElem htmp_jc,
               bv64_setWidth_32]
           · rw [List.getElem?_set_ne (by omega)]; exact hcp_j t (by omega), hm'⟩
    · have hjc_eq : jc.toNat = tk.toNat := by c0_bound
      rw [hjc_eq] at hcp_j
      s9_hsteps_to_jump; exact hJcp jc arj mjc harj_l hhold_j harj0 harj2 hcp_j hmjc

theorem s9_bva_large_top_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAllocCl : ∀ a m Q X, Full.fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {best_k mi c_top csz flit fresh : Val i32} {dd : Val .bool}
    {garb_add irred_add : Val i64} {J1b : Cont [i32, .bool, .bool, i64, i64]}
    {Jtop : Cont [.bool, .bool, i64, i64]} {mm : Mem 64} {resm : List Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hcsz_eq : csz.toNat = fullArenaClauseSizeCore s.core c_top.toNat)
    (hflit_eq : flit = s.scratch.scratch_buf[best_k.toNat]?.getD 0#32)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hresm_lt : ∀ x ∈ resm, x < 2 * s.core.cur_vars) (hresm_nd : (resm.map (· / 2)).Nodup)
    (hresm_ent : (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) ::
      resm)))
    (hct_ref0 : c_top.toNat ∈ fullArenaClauseRefsCore s.core)
    (hct_ng0 : fullArenaClauseGarbCore s.core c_top.toNat = false)
    (hct_sz3 : 3 ≤ fullArenaClauseSizeCore s.core c_top.toNat)
    (hfbk_mem : (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core c_top.toNat)
    (hres_perm_f : resm.Perm ((fullArenaClauseLitsCore s.core c_top.toNat).filter
      (· != (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat)))
    (hmm : (FullMem c stm ⋆ R) mm) (hstm : S7StOk c F0 F_next s stm)
    (hAbort : ∀ st1 m1, (FullMem c st1 ⋆ R) m1 → S7StOk c F0 F_next s st1 →
      J1b (mi, dd, false, garb_add, irred_add, ()) m1)
    (hDone : ∀ (ok' : Bool) (ga' ia' : Val i64) st1 m1, (FullMem c st1 ⋆ R) m1 →
      S7StOk c F0 F_next s st1 → Jtop (dd, ok', ga', ia', ()) m1) :
    wp Γ Q X (s9BvaLargeTopExpr c.hdr c.pArena c.pFlags c.pTmp
      mi c_top csz flit fresh dd garb_add irred_add J1b Jtop) mm := by
  obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ := hstm
  have hmx := c.hmaxv; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx har_b hscr_b; have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le :=
    hclm.cur_vars_le; have hsb_len := hsc.scratch_buf_len; let old_cv := s.core.cur_vars
  obtain ⟨hct_refm, hct_szm, hct_litsm⟩ := hmono c_top.toNat hct_ref0
  have hct_wfm := hinvm.2.1.arena.refs_wf c_top.toNat hct_refm
  have hcsz_s : csz.toNat = fullArenaClauseSizeCore s.core c_top.toNat := hcsz_eq
  let C_lits := fullArenaClauseLitsCore s.core c_top.toNat
  have hC_len : C_lits.length = csz.toNat := by
    rw [hcsz_s]; exact FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.1
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
  have hC_nd_vars : (C_lits.map (· / 2)).Nodup := hinv.2.2.2.1 c_top.toNat hct_ref0 hct_ng0
  have hC_nd : C_lits.Nodup := nodup_of_map_div2 hC_nd_vars
  have hC_len_le_cv : csz.toNat ≤ old_cv := by
    rw [← hC_len, ← List.length_map (· / 2)]
    exact s9_nodup_lt_length_le hC_nd_vars fun v hv => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      have := hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 l hl; omega
  have hfbk_mem' : flit.toNat ∈ C_lits := by rwa [hflit_eq]
  have hfilt_len : (C_lits.filter (· != flit.toNat)).length + 1 = csz.toNat := by
    rw [← hC_len]; exact filter_ne_nodup_length hC_nd hfbk_mem'
  have htmp0_lt : 0 < stm.core.tmp.length := by rw [hclm.tmp_len_arr]; omega
  dsimp only [s9BvaLargeTopExpr, s9BZext, s9BOp64, s9BOp32, s9BCmp32, s9BPtr32, s9BLd32]
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (tk, j, ()) mj => ∃ tmpj : List (BitVec 32),
      j.toNat ≤ csz.toNat ∧ tmpj.length = c.max_vars ∧
      tk.toNat = 1 + ((C_lits.take j.toNat).filter (· != flit.toNat)).length ∧
      tmpj[0]? = some (fresh ^^^ 1#32) ∧ (∀ t, 1 ≤ t → t < tk.toNat →
        (tmpj[t]?.getD 0#32).toNat = ((C_lits.take j.toNat).filter (· != flit.toNat))[t - 1]?.getD
          0) ∧
      (FullMem c { stm with core := { stm.core with tmp := tmpj } } ⋆ R) mj)
    (fun (_, j, _) _ => csz.toNat - j.toNat) (fun Jf hJf => by
      dsimp only [wp, vals, Arg.val]
      exact hJf (1#32, 0#32, ()) m ⟨_, Nat.zero_le _, by simp [hclm.tmp_len_arr], rfl,
        by rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl,
          List.getElem?_set_self (by rw [hclm.tmp_len_arr]; omega)]; rfl,
        fun _ h1 h2 => by simp only [bv_c0] at h2; omega, hm⟩)
    (fun Jf (tk, j, ()) mj ⟨tmpj, hj_le, htmpj_l, htk_eq, htmp0, htmp_rest, hmj⟩ ihf => ?_)
  c0_hsteps
  · have hj_lt : j.toNat < csz.toNat := by assumption
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
    have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 j).toNat =
        c_top.toNat + 3 + j.toNat := by
      change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat = _; c0_bound
    have hctj_ar : c_top.toNat + 3 + j.toNat < stm.core.arena.length := by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
    have hCj_eq : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) =
        (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar).toNat := by
      have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stm.core)
        (r := c_top.toNat) (j := j.toNat) (by rw [hct_szm]; omega) hctj_ar
      rw [hct_litsm, List.getElem?_eq_getElem (by rw [hC_len]; exact hj_lt)] at h1
      exact Option.some.inj h1
    have htake_succ := FullBvaFwdHelpers.take_succ_filter_eq (l := C_lits)
      (i := j.toNat) (x := flit.toNat) (by rw [hC_len]; exact hj_lt)
    have hsub_len : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ≤
        (C_lits.filter (· != flit.toNat)).length :=
      List.Sublist.length_le (List.Sublist.filter _ (List.take_sublist _ _))
    have hctj_mod : (c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
        c_top.toNat + 3 + j.toNat := by
      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
    c0_hsteps_nogrp; refine wp_join_group (ts := [i32])
      (fun (tk', ()) m' => ∃ tmp' : List (BitVec 32), tmp'.length = c.max_vars ∧
        tk'.toNat = 1 + ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ∧
        tmp'[0]? = some (fresh ^^^ 1#32) ∧
        (∀ t, 1 ≤ t → t < tk'.toNat → (tmp'[t]?.getD 0#32).toNat =
          ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat))[t - 1]?.getD 0) ∧
        (FullMem c { stm with core := { stm.core with tmp := tmp' } } ⋆ R) m')
      (fun _ (tk', ()) m' ⟨tmp', htl', htk', h0', hrest', hm'⟩ => by
        s9_hsteps_to_jump; exact ihf (tk', j + 1#32, ()) m' (by dsimp only; rw [hj1]; omega)
          ⟨tmp', by rw [hj1]; omega, htl', by rw [hj1]; exact htk', h0',
           fun t ht1 ht2 => by rw [hj1]; exact hrest' t ht1 ht2, hm'⟩)
      (fun Jif hJif => ?_)
    c0_hsplit
    · have hne_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar ≠ flit := by
        have h1 : ¬ stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) = flit := by assumption
        simpa only [hctj_mod] using h1
      have hne_nat : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) ≠ flit.toNat := by
        rw [hCj_eq]; intro h; exact hne_bv (BitVec.eq_of_toNat_eq h)
      have htk_succ_eq : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length =
          ((C_lits.take j.toNat).filter (· != flit.toNat)).length + 1 := by
        rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat), List.length_append]; rfl
      have htk_lt_tmp : tk.toNat < tmpj.length := by omega
      have htk1 : (tk + 1#32).toNat = tk.toNat + 1 := by c0_bound
      s9_hsteps_to_jump; refine hJif (tk + 1#32, ()) m
        ⟨tmpj.set tk.toNat (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar),
         by simp [htmpj_l], by rw [htk1, htk_succ_eq]; omega,
         by rw [List.getElem?_set_ne (by omega)]; exact htmp0, fun t ht1 ht2 => ?_, ?_⟩
      · rw [htk1] at ht2; rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat)]
        by_cases hte : t = tk.toNat
        · subst hte
          rw [List.getElem?_set_self htk_lt_tmp, Option.getD_some,
            List.getElem?_append_right (by omega),
            show tk.toNat - 1 - ((C_lits.take j.toNat).filter (· != flit.toNat)).length = 0 by
              omega]
          simp [hCj_eq]
        · rw [List.getElem?_set_ne (Ne.symm hte), List.getElem?_append_left (by omega)]
          exact htmp_rest t ht1 (by omega)
      · simp only [hctj_n, bv64_setWidth_32] at hm; exact hm
    · have heq_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar = flit := by
        have h1 : stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) = flit := by assumption
        simpa only [hctj_mod] using h1
      have heq_nat : (C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) != flit.toNat) = false := by
        rw [hCj_eq, heq_bv]; simp
      have htake_eq : (C_lits.take (j.toNat + 1)).filter (· != flit.toNat) =
          (C_lits.take j.toNat).filter (· != flit.toNat) := by
        rw [htake_succ, heq_nat]; simp
      dsimp only [wp, vals, Arg.val]; exact hJif (tk, ()) mj
        ⟨tmpj, htmpj_l, by rw [htake_eq]; exact htk_eq, htmp0,
         fun t ht1 ht2 => by rw [htake_eq]; exact htmp_rest t ht1 ht2, hmj⟩
  · have hj_eq : j.toNat = csz.toNat := by
      have h1 : ¬ j.toNat < csz.toNat := by assumption
      omega
    rw [hj_eq, ← hC_len, List.take_length] at htk_eq htmp_rest
    have htk_csz : tk.toNat = csz.toNat := by omega
    let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
    have hinv_tmp : FullDenseInvW c F0 F_next st_tmp := s9_fullDenseInvW_set_tmp hinvm htmpj_l
    c0_call hAllocCl; refine ⟨c, st_tmp, R, rfl, hinv_tmp.1, hmj, ?_⟩; split
    · s9_hsteps_to_jump; exact hAbort st_tmp mj hmj ⟨hinv_tmp, hcvm, hfuelm, hsbm, htmm, htrm,
        hmono, hresm⟩
    · intro ar1 ma1; dsimp only; intro hlen_a1 hhold_a1 hns_a1 hng_a1 _ hsz_a1 hma1
      let ncr0 := stm.core.arena_len
      have hncr_cap : ncr0 + 3 + tk.toNat ≤ c.arena_cap := hlen_a1.core_ok.arena_len_le
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32])
        (fun _ mjc => ∃ arj : List (BitVec 32), arj.length = c.arena_cap ∧
          (∀ i < ncr0, arj[i]? = stm.core.arena[i]?) ∧ arj[ncr0]? = ar1[ncr0]? ∧
          arj[ncr0 + 2]? = ar1[ncr0 + 2]? ∧ (∀ t < tk.toNat, arj[ncr0 + 3 + t]? = tmpj[t]?) ∧
          (FullMem c { st_tmp with core := { st_tmp.core with
            arena := arj, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mjc)
        (fun _ _ mjc ⟨arj, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩ => ?_)
        (fun Jcp hJcp => ?_)
      · let st_cp : FullState :=
          { st_tmp with core := { st_tmp.core with arena := arj,
                                                   arena_len := ncr0 + 3 + tk.toNat } }
        have hlen_cp : st_cp.LengthsOk c :=
          ⟨{ hlen_a1.core_ok with arena_len_arr := harj_l }, hlen_a1.scratch_ok⟩
        have hns_cp : (arj[ncr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
          rw [harj0]; exact hns_a1
        have hsz_cp : (arj[ncr0 + 2]?.getD 0#32).toNat = tk.toNat := by
          rw [harj2]; exact hsz_a1
        have hrefs_cp : fullArenaClauseRefsCore st_cp.core =
            fullArenaClauseRefsCore stm.core ++ [ncr0] :=
          fullArenaClauseRefsCore_append hinvm.2.1.arena (by omega) rfl hhold_j hns_cp hsz_cp
        have hwat_cp : ModeWatchesInv F_next st_cp.core :=
          hinvm.2.1.watches.with_wstk rfl rfl rfl rfl rfl
            (fun r hr => by rw [hrefs_cp]; exact List.mem_append_left _ hr)
        have hnew_lits_eq : fullArenaClauseLitsCore { stm.core with arena := arj } ncr0 =
            (2 * old_cv + 1) :: C_lits.filter (· != flit.toNat) := by
          rw [s9_fullArenaLitsCore_eq_map (sz := tk.toNat)
            (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
          apply List.ext_getElem?; intro t; cases t with
          | zero =>
            rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
              Nat.add_zero, hcp_j 0 (by omega), htmp0, Option.getD_some, hfresh1]; rfl
          | succ t' =>
            by_cases ht : t' + 1 < tk.toNat
            · rw [List.getElem?_map, List.getElem?_range ht, Option.map_some,
                hcp_j (t' + 1) ht, htmp_rest (t' + 1) (by omega) ht, Nat.add_sub_cancel,
                List.getElem?_cons_succ,
                List.getElem?_eq_getElem (by omega : t' < (C_lits.filter (· !=
                  flit.toNat)).length),
                Option.getD_some]
            · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        have hnew_perm : (fullArenaClauseLitsCore { stm.core with arena := arj }
            ncr0).Perm ((2 * old_cv + 1) :: resm) := by
          rw [hnew_lits_eq]; have hf' : resm.Perm (C_lits.filter (· != flit.toNat)) := by
            rw [hflit_eq]; exact hres_perm_f
          exact List.Perm.cons _ hf'.symm
        have hnew_lt :
            ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arj } ncr0,
            l < 2 * stm.core.cur_vars := by
          intro l hl; rw [hcvm]; rcases List.mem_cons.mp (hnew_perm.subset hl) with rfl | hr
          · omega
          · have := hresm_lt l hr; omega
        have hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arj }
            ncr0).map (· / 2)).Nodup := by
          have hp := hnew_perm.map (· / 2)
          refine (List.nodup_cons.mpr ⟨?_, hresm_nd⟩).perm hp.symm
          intro hmem; obtain ⟨x, hx, hdiv⟩ := List.mem_map.mp hmem
          have := hresm_lt x hx; dsimp only [old_cv] at *; omega
        have hnew_ent : (cnfOfClauses F_next).EntailsClause
            (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arj } ncr0)) :=
          clause_entails_of_perm hnew_perm.symm hresm_ent
        have htmp_lt :
            ∀ t (ht : t < tk.toNat), (tmpj[t]'(by omega)).toNat < 2 * (old_cv + 1) := by
          intro t ht; have hmem : (tmpj[t]'(by omega)).toNat ∈
              fullArenaClauseLitsCore { stm.core with arena := arj } ncr0 := by
            rw [s9_fullArenaLitsCore_eq_map (sz := tk.toNat)
              (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
            refine List.mem_map.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
            rw [hcp_j t ht, List.getElem?_eq_getElem (by omega), Option.getD_some]
          simpa only [hcvm] using hnew_lt _ hmem
        exact s9_bva_large_watch_wp (stm := stm) hWPush hUnwatch
          ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ htmpj_l (by omega) (by omega)
          hncr_cap hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent (fun t ht => htmp_lt t ht)
          hlen_cp hrefs_cp hwat_cp hmjc hDone
      · have hcp := s9_bva_copy_wp (Γ := Γ) (Q := Q) (X := X) (c := c) (stm := stm) (R := R)
          (tk := tk) (tmpj := tmpj) (ar1 := ar1) (ncr0 := ncr0) (Jcp := Jcp) (ma1 := ma1)
          (by omega) (by omega) hncr_cap hlen_a1.core_ok.arena_len_arr htmpj_l hhold_a1 hma1
          fun j_out arj mjc harj_l hhold_j harj0 harj2 hcp_j hmjc =>
            hJcp (j_out, ()) mjc ⟨arj, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩
        dsimp only [s9BvaCopyExpr, s9BZext, s9BOp64, s9BOp32, s9BCmp32, s9BPtr32, s9BLd32] at hcp
        exact hcp

end LeanQbe.T.Examples.Kissat.FullFidelityStep9

end
