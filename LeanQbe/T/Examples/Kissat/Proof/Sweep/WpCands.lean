/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCommon

/-!
# Sweep Candidate Sift & Collection WP Proofs (`Kissat.Proof.Sweep.WpCands`)

Clean flat-`CanonicalEnv` `Func.wp` proofs against `Src.Sweep` and `Proof.Sweep.Spec`:
1. `full_m6_cand_sift_wp` (`fullM6CandSiftSpec`)
2. `full_m6_collect_cands_wp` (`fullM6CollectCandsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Sweep
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
open LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
open FullArenaTactics
open scoped FullArenaTactics M6SweepTactics

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

/-! ## 1. Pure BitVector, `array` Focusing, `FullMem` Framing, & Callee Helpers -/

private theorem bv32_zext_mul4_eq (idx : BitVec 32) :
    idx.setWidth 64 * 4 = BitVec.ofNat 64 (4 * idx.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : idx.toNat < 2 ^ 32 := idx.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  rw [h4, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

private theorem bv32_shl1_toNat (r : BitVec 32) (hr : 2 * r.toNat < 2 ^ 32) :
    (r <<< (1 : Nat)).toNat = 2 * r.toNat := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

private theorem bv32_shl1_add1_toNat (r : BitVec 32) (hr : 2 * r.toNat + 1 < 2 ^ 32) :
    ((r <<< (1 : Nat)) + 1#32).toNat = 2 * r.toNat + 1 := by
  have hsh := bv32_shl1_toNat r (by omega)
  rw [BitVec.toNat_add, hsh, show (1#32 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

private theorem bv32_sub1_toNat {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

private theorem bv32_lshr1_toNat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by bv_omega

private theorem bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem bv64_shl1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

private theorem nat_two_mul_lor_one (n : Nat) : 2 * n ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    rw [show 1 / 2 = 0 from rfl, show (2 * n) / 2 = n from by omega,
      show (2 * n + 1) / 2 = n from by omega, Nat.zero_testBit, Bool.or_false]

private theorem bv64_shl1_or1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
  have h0 := bv64_shl1_toNat hv
  rw [BitVec.toNat_or, h0, show (1#64 : BitVec 64).toNat = 1 from rfl]
  exact nat_two_mul_lor_one v.toNat

private theorem maxVars_lt_2p31 (c : FullCfg) : c.max_vars < 2 ^ 31 := by
  have hm := c.hmaxv; unfold dimacsBound at hm; omega

namespace CandsMemTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64

@[scoped bv_c0 high] theorem bv_ofNat64_zero_toNat : (BitVec.ofNat 64 0).toNat = 0 := rfl

@[scoped bv_c0] theorem bv_zext32_mul4 (idx : BitVec 32) :
    idx.setWidth 64 * 4 = BitVec.ofNat 64 (4 * idx.toNat) :=
  bv32_zext_mul4_eq idx

@[scoped c0_load] theorem load_array_i32_ofNat {base : BitVec 64} {xs : List (BitVec 32)}
    {i : Nat} {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m) :
    loadVal m i32 (base + BitVec.ofNat 64 (4 * i)) = some xs[i] :=
  loadVal_array (t := i32) (by decide) hi hm

@[scoped c0_load] theorem load_array_i32_zero {base : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m) :
    loadVal m i32 base = some xs[0] := by
  have h := loadVal_array (t := i32) (a := base) (i := 0) (by decide) hi hm
  simpa using h

@[scoped c0_store] theorem store_array_i32_ofNat {base : BitVec 64} {xs : List (BitVec 32)}
    {i : Nat} (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m) :
    storeOk m i32 (base + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) base (xs.set i v) ⋆ R)
        (storeMem m i32 (base + BitVec.ofNat 64 (4 * i)) v) :=
  store_array (t := i32) v (by decide) hi hm

@[scoped c0_store] theorem store_array_i32_zero {base : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m) :
    storeOk m i32 base ∧
      (array (t := i32) base (xs.set 0 v) ⋆ R) (storeMem m i32 base v) := by
  have h := store_array (t := i32) v (a := base) (i := 0) (by decide) hi hm
  simpa using h

@[scoped c0_load] theorem load_glue_used_28 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 28 < s.scratch.glue_used.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pGlueUsed + 112#64) = some s.scratch.glue_used[28] :=
  load_full_glue_used (i := 28) hi hm

@[scoped c0_load] theorem load_glue_used_30 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 30 < s.scratch.glue_used.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pGlueUsed + 120#64) = some s.scratch.glue_used[30] :=
  load_full_glue_used (i := 30) hi hm

end CandsMemTactics

open scoped CandsMemTactics

private def FullCandsFrame (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
     array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
     array (t := i32) c.pTarjanMark s.scratch.tarjan_mark) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

private theorem fullCandsFrame_irrel (c : FullCfg) (s : FullState)
    (trc' ws2' : List (BitVec 32)) :
    FullCandsFrame c
      { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } =
      FullCandsFrame c s := rfl

private theorem fullMem_eq_candsFrame (c : FullCfg) (s : FullState) :
    FullMem c s =
      (array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
        FullCandsFrame c s) := by
  unfold FullMem FullScratchArrays FullScrWksArrs FullCandsFrame
  ac_rfl

private theorem fullCands_split_array {a : BitVec 64} {xs : List (BitVec 32)} {n : Nat}
    (hn : n ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) a (xs.take n) ⋆
        array (t := i32) (a + BitVec.ofNat 64 (4 * n)) (xs.drop n)) := by
  have htake : (xs.take n).length = n := List.length_take_of_le hn
  conv => lhs; rw [← List.take_append_drop n xs]
  rw [array_append, htake]
  rfl

private theorem fullCands_join_array {a : BitVec 64} {pref suff : List (BitVec 32)}
    {n : Nat} (hp : pref.length = n) :
    (array (t := i32) a pref ⋆ array (t := i32) (a + BitVec.ofNat 64 (4 * n)) suff) =
      array (t := i32) a (pref ++ suff) := by
  rw [array_append, hp]; rfl

private theorem m6_lengthsOk_trc_ws2 {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {trc' ws2' : List (BitVec 32)} (htrc : trc'.length = 2 * c.max_vars)
    (hws2 : ws2'.length = 2 * c.max_vars) :
    ({ s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with tarjan_reach_len := htrc, work_stk2_len := hws2 }⟩

private theorem m6_call_dense_occ_cnt {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hOcc : Γ.Has "full_dense_occ_cnt_fid" fullDenseOccCntSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {lit : BitVec 32} {cap : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r : BitVec 64, wp Γ Q X (k (r, ())) m) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i64]) (bs := [i64]) "full_dense_occ_cnt_fid"
        (Arg.var c.hdr, Arg.var lit, Arg.var cap, ()) k) m :=
  wp_call_of_spec _ k
    (hOcc (c.hdr, lit, cap, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, R, rfl, hlen, hlay, hlit, hm, hk⟩)

private theorem m6_call_cand_sift {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSift : Γ.Has "full_m6_cand_sift" fullM6CandSiftSpec)
    {cands_ptr deg_ptr : BitVec 64} (start n : BitVec 32)
    {cands deg : List (BitVec 32)} {bound : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont rs}
    (hsn : start.toNat < n.toNat) (hnc : n.toNat ≤ cands.length) (hn31 : n.toNat < 2 ^ 31)
    (hbd : bound ≤ deg.length) (hclt : ∀ i < n.toNat, (cands[i]?.getD 0#32).toNat < bound)
    (hm : (array (t := i32) cands_ptr cands ⋆ array (t := i32) deg_ptr deg ⋆ R) m)
    (hk : ∀ cands' m', cands'.length = cands.length →
      (∀ i < n.toNat, (cands'[i]?.getD 0#32).toNat < bound) →
      (array (t := i32) cands_ptr cands' ⋆ array (t := i32) deg_ptr deg ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i64, i32, i32]) (bs := []) "full_m6_cand_sift"
        (Arg.var cands_ptr, Arg.var deg_ptr, Arg.var start, Arg.var n, ()) k) m :=
  wp_call_of_spec _ k
    (hSift (cands_ptr, deg_ptr, start, n, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨cands, deg, bound, R, hsn, hnc, hn31, hbd, hclt, hm, hk⟩)

private theorem list_set_swap_bound {xs : List (BitVec 32)} {r c n bound : Nat}
    (hr : r < n) (hc : c < n) (hn : n ≤ xs.length)
    (hbd : ∀ i < n, (xs[i]?.getD 0#32).toNat < bound) :
    ∀ i < n, (((xs.set r (xs[c]'(by omega))).set c
      (xs[r]'(by omega)))[i]?.getD 0#32).toNat < bound := by
  intro i hi
  by_cases hic : i = c
  · subst hic
    rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
    have := hbd r hr
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    by_cases hir : i = r
    · subst hir
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      have := hbd c hc
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    · rw [List.getElem?_set_ne (Ne.symm hir)]
      exact hbd i hi

/-! ## 2. `full_m6_cand_sift_wp` -/

theorem full_m6_cand_sift_wp (Γ : Env) :
    ∀ args m Q X, fullM6CandSiftSpec args m Q X →
      Func.wp Γ full_m6_cand_sift_body args m Q X := by
  rintro ⟨cands_ptr, deg_ptr, start, n, ⟨⟩⟩ m Q X
    ⟨cands, deg, bound, R, hsn, hnc, hn31, hbd, hclt, hm, hQ⟩
  unfold Func.wp full_m6_cand_sift_body
  c0_hsteps_nogrp
  refine wp_while_break_state
    (α := BitVec 32) (β := BitVec 32)
    (fun b => (b, ()))
    (fun _ mb => ∃ candsL : List (BitVec 32), candsL.length = cands.length ∧
      (∀ i < n.toNat, (candsL[i]?.getD 0#32).toNat < bound) ∧
      (array (t := i32) cands_ptr candsL ⋆ array (t := i32) deg_ptr deg ⋆ R) mb)
    (fun r => (r, ()))
    (fun r => n.toNat - r.toNat)
    (fun r ml => r.toNat < n.toNat ∧ ∃ candsL : List (BitVec 32),
      candsL.length = cands.length ∧
      (∀ i < n.toNat, (candsL[i]?.getD 0#32).toNat < bound) ∧
      (array (t := i32) cands_ptr candsL ⋆ array (t := i32) deg_ptr deg ⋆ R) ml)
    (fun _ _ mb ⟨candsL, hlenL, hbdL, hmL⟩ => by
      c0_hfast
      exact hQ candsL mb hlenL hbdL hmL)
    (fun _ L r ml hB hL ⟨hrn, candsL, hlenL, hbdL, hmL⟩ => by
      c0_hsplit; rotate_left
      · c0_hfast; exact hB r ml ⟨candsL, hlenL, hbdL, hmL⟩
      have hr_shl : (r <<< (1 : Nat)).toNat = 2 * r.toNat := bv32_shl1_toNat r (by omega)
      have hc_eq : ((r <<< (1 : Nat)) + 1#32).toNat = 2 * r.toNat + 1 :=
        bv32_shl1_add1_toNat r (by omega)
      c0_hsplit
      · c0_hfast; exact hB r ml ⟨candsL, hlenL, hbdL, hmL⟩
      have hcn : (r <<< (1 : Nat) + 1#32).toNat < n.toNat := by
        rw [hc_eq]
        change ¬ n.toNat ≤ (r.toNat * 2 ^ 1 + 1) % 2 ^ 32 at hc
        rw [Nat.pow_one, Nat.mod_eq_of_lt (by omega)] at hc; omega
      have hc1_eq : ((r <<< (1 : Nat) + 1#32) + 1#32).toNat = 2 * r.toNat + 2 := by
        rw [bv32_add1_toNat (by omega), hc_eq]
      have hdeg_idx : ∀ (i : BitVec 32) (hi : i.toNat < n.toNat),
          (candsL[i.toNat]'(by omega)).toNat < deg.length := fun i hi => by
        have h1 := hbdL i.toNat hi
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
        omega
      have hcr_deg := hdeg_idx r hrn
      c0_hsteps_nogrp
      refine wp_join_state1 (fun c' : BitVec 32 => c')
        (fun c' mj => mj = ml ∧ r.toNat < c'.toNat ∧ c'.toNat < n.toNat)
        (fun _ c' mj ⟨hmj, hrc', hc'n⟩ => by
          have hcc'_deg := hdeg_idx c' hc'n
          rw [← hmj] at hmL
          c0_hsplit
          · c0_hfast
            exact hB r mj ⟨candsL, hlenL, hbdL, hmL⟩
          · c0_hfast
            have hswap := list_set_swap_bound hrn hc'n (by omega) hbdL
            refine hL c' _ (by omega) ⟨hc'n, _, by simp [hlenL], hswap, ?_⟩
            exact sep_ac hm)
        (fun _ hJ => by
          c0_hsplit
          · have hc1n : ((r <<< (1 : Nat) + 1#32) + 1#32).toNat < n.toNat := by
              rw [hc1_eq]
              change (r.toNat * 2 ^ 1 + 1 + 1) % 2 ^ 32 < n.toNat at hc
              rw [Nat.pow_one, Nat.mod_eq_of_lt (by omega)] at hc; omega
            have hc0_deg := hdeg_idx (r <<< (1 : Nat) + 1#32) hcn
            have hc1_deg := hdeg_idx (r <<< (1 : Nat) + 1#32 + 1#32) hc1n
            c0_hsplit
            · c0_hfast
              exact hJ (r <<< (1 : Nat) + 1#32 + 1#32) ml ⟨rfl, by omega, hc1n⟩
            · c0_hfast
              exact hJ (r <<< (1 : Nat) + 1#32) ml ⟨rfl, by omega, hcn⟩
          · c0_hfast
            exact hJ (r <<< (1 : Nat) + 1#32) ml ⟨rfl, by omega, hcn⟩))
    (fun _ _ _ hL => by
      c0_hfast
      exact hL start m ⟨hsn, cands, rfl, hclt, hm⟩)

/-! ## 3. `full_m6_collect_cands_wp` -/

theorem full_m6_collect_cands_wp (Γ : Env)
    (hOcc : Γ.Has "full_dense_occ_cnt_fid" fullDenseOccCntSpec)
    (hSift : Γ.Has "full_m6_cand_sift" fullM6CandSiftSpec) :
    ∀ args m Q X, fullM6CollectCandsSpec args m Q X →
      Func.wp Γ full_m6_collect_cands_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := maxVars_lt_2p31 c
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hcv_mod : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64]
  have hfl_len := hlen.core_ok.flags_len
  have hvals_len := hlen.core_ok.vals_len
  have htrc_len := hlen.scratch_ok.tarjan_reach_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  have hgu_len := hlen.scratch_ok.glue_used_len
  have hgu28 : 28 < s.scratch.glue_used.length := by omega
  have hgu30 : 30 < s.scratch.glue_used.length := by omega
  unfold Func.wp full_m6_collect_cands_body
  c0_hsplit
  · c0_hfast
    have h0 : (0#32 : BitVec 32).toNat ≤ s.core.cur_vars := Nat.zero_le _
    exact hQ 0#32 s.scratch.tarjan_reach s.scratch.work_stk2 m hlen h0
      (fun _ hi => by simp at hi) hm
  have hcv_pos : 0 < s.core.cur_vars := by
    apply Nat.pos_of_ne_zero; intro hz
    have hne : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64 := ‹_›
    apply hne; rw [hz]
  c0_hsteps_nogrp
  refine wp_join_state1 (fun comp : BitVec 32 => comp) (fun _ mj => mj = m)
    (fun _ comp mj hmj => by
      cases hmj
      c0_hsteps_nogrp
      refine wp_join_state1 (fun cur : BitVec 64 => cur)
        (fun cur mj => mj = m ∧ cur.toNat < s.core.cur_vars)
        (fun _ cur mj ⟨hmj, hcur_lt⟩ => by
          cases hmj
          c0_hsteps_nogrp
          refine wp_while_state (ts := [i32, i64])
            (α := BitVec 32 × BitVec 64)
            (fun st => (st.1, st.2, ()))
            (fun st => s.core.cur_vars - st.2.toNat)
            (fun st ml => st.1.toNat ≤ st.2.toNat ∧ st.2.toNat ≤ s.core.cur_vars ∧
              ∃ trc ws2, trc.length = 2 * c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
              (∀ i < st.1.toNat, (trc[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
              (FullMem c { s with scratch :=
                { s.scratch with tarjan_reach := trc, work_stk2 := ws2 } } ⋆ R) ml)
            (fun _ hJ => by
              c0_hfast
              exact hJ (0#32, 0#64) m ⟨Nat.zero_le _, Nat.zero_le _, s.scratch.tarjan_reach,
                s.scratch.work_stk2, htrc_len, hws2_len, fun _ hi => by simp at hi, hm⟩)
            (fun _ ⟨nc, step⟩ ml ⟨hnc_le, hst_le, trc, ws2, htrcL, hws2L, hbdL, hmL⟩ hJ => by
              dsimp only at hnc_le hst_le hbdL
              let sL : FullState :=
                { s with scratch := { s.scratch with tarjan_reach := trc, work_stk2 := ws2 } }
              have hlenL : sL.LengthsOk c := m6_lengthsOk_trc_ws2 hlen htrcL hws2L
              change (FullMem c sL ⋆ R) ml at hmL
              c0_hsplit
              · have hst_lt : step.toNat < s.core.cur_vars := by rw [← hcv_mod]; exact ‹_›
                have hst1 : (step + 1#64).toNat = step.toNat + 1 := bv64_add1_toNat (by omega)
                have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := bv32_add1_toNat (by omega)
                have hcs_sum : (cur + step).toNat = cur.toNat + step.toNat := by bv_omega
                c0_hsteps_nogrp
                refine wp_join_state1 (fun v : BitVec 64 => v)
                  (fun v mj => mj = ml ∧ v.toNat < s.core.cur_vars)
                  (fun _ v mj ⟨hmj, hv_lt⟩ => by
                    cases hmj
                    have hv_fl : v.toNat < sL.core.flags.length := by dsimp [sL]; omega
                    have hv_2v : (v <<< (1 : Nat)).toNat = 2 * v.toNat :=
                      bv64_shl1_toNat (by omega)
                    have hv_vals : (v <<< (1 : Nat)).toNat < sL.core.vals.length := by
                      rw [hv_2v]; dsimp [sL]; omega
                    have hv_2v1 : ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 :=
                      bv64_shl1_or1_toNat (by omega)
                    have hv_ws2 : v.toNat < sL.scratch.work_stk2.length := by dsimp [sL]; omega
                    have hnc_trc : nc.toNat < sL.scratch.tarjan_reach.length := by
                      dsimp [sL]; omega
                    c0_hsteps_nogrp
                    refine wp_join_state1 (fun nc' : BitVec 32 => nc')
                      (fun nc' mj' => nc'.toNat ≤ step.toNat + 1 ∧
                        ∃ trc' ws2', trc'.length = 2 * c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
                        (∀ i < nc'.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                        (FullMem c { s with scratch :=
                          { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) mj')
                      (fun _ nc' mj' ⟨h1, trc', ws2', htrc', hws2', hbd', hm'⟩ => by
                        c0_hfast
                        exact hJ (nc', step + 1#64) mj' (by dsimp only; omega)
                          ⟨by dsimp only; omega, by dsimp only; omega, trc', ws2',
                           htrc', hws2', hbd', hm'⟩)
                      (fun _ hJin => by
                        c0_hsplit; rotate_left
                        · c0_hfast
                          exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                        c0_hsplit; rotate_left
                        · c0_hfast
                          exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                        c0_hsteps_nogrp
                        refine m6_call_dense_occ_cnt hOcc hlenL hlay
                          (by rw [BitVec.toNat_setWidth, hv_2v, Nat.mod_eq_of_lt (by omega)]
                              dsimp only [sL]; omega)
                          hmL fun dp => ?_
                        c0_hsteps_nogrp
                        refine m6_call_dense_occ_cnt hOcc hlenL hlay
                          (by rw [BitVec.toNat_setWidth,
                                show (v <<< OfNat.ofNat 1 ||| 1) = (v <<< (1 : Nat) ||| 1#64)
                                  from rfl, hv_2v1, Nat.mod_eq_of_lt (by omega)]
                              dsimp only [sL]; omega)
                          hmL fun dn => ?_
                        c0_hsteps_nogrp
                        refine wp_unroll_group fun _ _ => ?_
                        c0_hsplit; rotate_left
                        · c0_hfast
                          exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                        c0_hsplit; rotate_left
                        · c0_hfast
                          exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                        c0_hsplit; rotate_left
                        · c0_hfast
                          exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                        c0_hsplit; rotate_left
                        · c0_hfast
                          exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                        have hbd_new : ∀ i < (nc + 1#32).toNat,
                            ((trc.set nc.toNat (v.setWidth 32))[i]?.getD 0#32).toNat <
                              s.core.cur_vars := by
                          intro i hi
                          by_cases hinc : i = nc.toNat
                          · subst hinc
                            rw [List.getElem?_set_self (by dsimp [sL] at hnc_trc; omega),
                              Option.getD_some, BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (by omega)]
                            exact hv_lt
                          · rw [List.getElem?_set_ne (Ne.symm hinc)]
                            exact hbdL i (by omega)
                        c0_hsteps_nogrp
                        refine wp_join_state1 (fun d32 : BitVec 32 => d32) (fun _ mj' => mj' = ml)
                          (fun _ d32 mj' hmj' => by
                            cases hmj'
                            c0_hsteps_nogrp
                            refine wp_join_state1 (fun d32' : BitVec 32 => d32')
                              (fun _ mj'' => mj'' = ml)
                              (fun _ d32' mj'' hmj'' => by
                                cases hmj''
                                c0_hfast
                                have hm_upd : (FullMem c { s with scratch := { s.scratch with
                                    tarjan_reach := trc.set nc.toNat (v.setWidth 32),
                                    work_stk2 := ws2.set v.toNat d32' } } ⋆ R) m := by
                                  rw [← bv_c0_zext32_64 (x := nc)]
                                  dsimp only [sL]
                                  assumption
                                exact hJin (nc + 1#32) m ⟨by omega,
                                  trc.set nc.toNat (v.setWidth 32), ws2.set v.toNat d32',
                                  by simp [htrcL], by simp [hws2L], hbd_new, hm_upd⟩)
                              (fun _ hJd2 => by
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_unroll_group fun _ _ => ?_
                                  c0_hsplit
                                  · c0_hfast; exact hJd2 _ ml rfl
                                  · c0_hfast; exact hJd2 _ ml rfl
                                · c0_hfast; exact hJd2 _ ml rfl))
                          (fun _ hJd1 => by
                            c0_hsplit
                            · c0_hfast; exact hJd1 _ ml rfl
                            · c0_hfast; exact hJd1 _ ml rfl)))
                  (fun _ hJv => by
                    c0_hsplit
                    · c0_hfast
                      refine hJv ((cur + step) - BitVec.ofNat 64 s.core.cur_vars) ml ⟨rfl, ?_⟩
                      have hge : s.core.cur_vars ≤ (cur + step).toNat := by
                        rw [← hcv_mod]; exact ‹_›
                      bv_omega
                    · c0_hfast
                      refine hJv (cur + step) ml ⟨rfl, ?_⟩
                      have hlt : (cur + step).toNat < s.core.cur_vars := by
                        rw [← hcv_mod]; bv_omega
                      exact hlt)
              · have hst_eq : step.toNat = s.core.cur_vars := by rw [← hcv_mod] at *; bv_omega
                have hnc_cur : nc.toNat ≤ s.core.cur_vars := by omega
                c0_hsplit
                · c0_hfast
                  exact hQ nc trc ws2 ml hlenL hnc_cur hbdL hmL
                have hnc_ge2 : 2 ≤ nc.toNat := by bv_omega
                c0_hsteps_nogrp
                refine wp_while_state1 (t := i32) (α := BitVec 32)
                  (fun x => x) (fun x => x.toNat)
                  (fun x ml1 => x.toNat ≤ nc.toNat ∧ ∃ trc1, trc1.length = 2 * c.max_vars ∧
                    (∀ i < nc.toNat, (trc1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                    (FullMem c { s with scratch :=
                      { s.scratch with tarjan_reach := trc1, work_stk2 := ws2 } } ⋆ R) ml1)
                  (fun _ hJs => by
                    c0_hfast
                    exact hJs (nc >>> 1#32) ml
                      ⟨by rw [show nc >>> 1#32 = nc >>> (1 : Nat) from rfl, bv32_lshr1_toNat]
                          omega,
                       trc, htrcL, hbdL, hmL⟩)
                  (fun _ s_i ml1 ⟨hsi_le, trc1, htrc1L, hbd1L, hm1⟩ hJs => by
                    c0_hsplit
                    · have hsi_pos : 0 < s_i.toNat := by bv_omega
                      have hsi1 : (s_i - 1#32).toNat = s_i.toNat - 1 := bv32_sub1_toNat hsi_pos
                      c0_hsteps_nogrp
                      have hm_focus : (array (t := i32) c.pTarjanReach trc1 ⋆
                          array (t := i32) c.pWorkStk2 ws2 ⋆
                          (FullCandsFrame c { s with scratch :=
                            { s.scratch with tarjan_reach := trc1, work_stk2 := ws2 } } ⋆ R))
                            ml1 := by
                        rw [fullMem_eq_candsFrame] at hm1; exact sep_ac hm1
                      refine m6_call_cand_sift hSift (bound := s.core.cur_vars) (s_i - 1#32) nc
                        (by omega) (by omega) (by omega) (by omega) hbd1L hm_focus
                        fun trc2 m2 htrc2L hbd2L hm2 => ?_
                      have hm2_full : (FullMem c { s with scratch :=
                          { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆ R) m2 := by
                        rw [fullMem_eq_candsFrame, fullCandsFrame_irrel]; exact sep_ac hm2
                      c0_hfast
                      exact hJs (s_i - 1#32) m2 (by omega)
                        ⟨by omega, trc2, by omega, hbd2L, hm2_full⟩
                    · c0_hsteps_nogrp
                      refine wp_while_state1 (t := i32) (α := BitVec 32)
                        (fun x => x) (fun x => x.toNat)
                        (fun x ml2 => 1 ≤ x.toNat ∧ x.toNat ≤ nc.toNat ∧ ∃ trc2,
                          trc2.length = 2 * c.max_vars ∧
                          (∀ i < nc.toNat, (trc2[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                          (FullMem c { s with scratch :=
                            { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆ R) ml2)
                        (fun _ hJe => by
                          c0_hfast
                          exact hJe nc ml1 ⟨by omega, Nat.le_refl _, trc1, htrc1L, hbd1L, hm1⟩)
                        (fun _ end_v ml2 ⟨hend1, hend_le, trc2, htrc2L, hbd2L, hm2⟩ hJe => by
                          c0_hsplit; rotate_left
                          · c0_hfast
                            exact hQ nc trc2 ws2 ml2 (m6_lengthsOk_trc_ws2 hlen htrc2L hws2L)
                              hnc_cur hbd2L hm2
                          have hend_gt1 : 1 < end_v.toNat := by bv_omega
                          have hend1_eq : (end_v - 1#32).toNat = end_v.toNat - 1 :=
                            bv32_sub1_toNat (by omega)
                          let end' := end_v - 1#32
                          have hend'_eq : end'.toNat = end_v.toNat - 1 := hend1_eq
                          have h0_trc : 0 < trc2.length := by omega
                          have hend'_trc : end'.toNat < trc2.length := by omega
                          have hm2_arr : (array (t := i32) c.pTarjanReach trc2 ⋆
                              (array (t := i32) c.pWorkStk2 ws2 ⋆
                               (FullCandsFrame c { s with scratch :=
                                 { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                                R))) ml2 := by
                            rw [fullMem_eq_candsFrame] at hm2; exact sep_ac hm2
                          c0_hsteps_nogrp
                          let trc3 := (trc2.set 0 (trc2[end'.toNat]'hend'_trc)).set end'.toNat
                            (trc2[0]'h0_trc)
                          have htrc3L : trc3.length = 2 * c.max_vars := by
                            dsimp only [trc3]; simp [htrc2L]
                          have hbd3L :
                              ∀ i < nc.toNat, (trc3[i]?.getD 0#32).toNat < s.core.cur_vars := by
                            simpa [trc3] using list_set_swap_bound (n := nc.toNat) (by omega)
                              (by omega) (by omega) hbd2L
                          have hm3_split : (array (t := i32) c.pTarjanReach (trc3.take end'.toNat) ⋆
                              array (t := i32) c.pWorkStk2 ws2 ⋆
                              (array (t := i32) (c.pTarjanReach + BitVec.ofNat 64 (4 * end'.toNat))
                                (trc3.drop end'.toNat) ⋆
                               FullCandsFrame c { s with scratch :=
                                 { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                               R)) m := by
                            have hm_sw : (array (t := i32) c.pTarjanReach trc3 ⋆
                                (array (t := i32) c.pWorkStk2 ws2 ⋆
                                 (FullCandsFrame c { s with scratch :=
                                   { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                                  R))) m := by
                              have h1 := hm
                              simp only [bv_c0_zext32_64,
                                CandsMemTactics.bv_ofNat64_zero_toNat] at h1
                              have hend_trc : (end_v - 1).toNat < trc2.length := hend'_trc
                              have hlist :
                                  (trc2.set 0 trc2[(end_v - 1).toNat]).set (end_v - 1).toNat
                                    trc2[0] = trc3 := by
                                dsimp only [trc3, end']; rfl
                              rwa [hlist] at h1
                            rw [fullCands_split_array (n := end'.toNat) (by omega)] at hm_sw
                            exact sep_ac hm_sw
                          refine m6_call_cand_sift hSift (bound := s.core.cur_vars) 0#32 end'
                            (by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega)
                            (by simp [htrc3L]; omega) (by omega) (by omega)
                            (fun i hi => by
                              rw [List.getElem?_take_of_lt hi]; exact hbd3L i (by omega))
                            hm3_split fun pref' m3 hprefL hbdP hm3' => ?_
                          have hprefL' : pref'.length = end'.toNat := by
                            rw [hprefL, List.length_take_of_le (by omega)]
                          let trc4 := pref' ++ trc3.drop end'.toNat
                          have htrc4L : trc4.length = 2 * c.max_vars := by
                            dsimp only [trc4]
                            rw [List.length_append, hprefL', List.length_drop, htrc3L]
                            omega
                          have hbd4L :
                              ∀ i < nc.toNat, (trc4[i]?.getD 0#32).toNat < s.core.cur_vars := by
                            intro i hi
                            by_cases hie : i < end'.toNat
                            · dsimp only [trc4]
                              rw [List.getElem?_append_left (by rw [hprefL']; exact hie)]
                              exact hbdP i hie
                            · dsimp only [trc4]
                              rw [List.getElem?_append_right (by rw [hprefL']; omega),
                                hprefL', List.getElem?_drop]
                              have heq : end'.toNat + (i - end'.toNat) = i := by omega
                              rw [heq]; exact hbd3L i hi
                          have hm4 : (FullMem c { s with scratch :=
                              { s.scratch with tarjan_reach := trc4, work_stk2 := ws2 } } ⋆ R)
                              m3 := by
                            have hm3_arr : (array (t := i32) c.pTarjanReach trc4 ⋆
                                array (t := i32) c.pWorkStk2 ws2 ⋆
                                FullCandsFrame c { s with scratch :=
                                  { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                                R) m3 := by
                              have hm3a : ((array (t := i32) c.pTarjanReach pref' ⋆
                                  array (t := i32)
                                    (c.pTarjanReach + BitVec.ofNat 64 (4 * end'.toNat))
                                    (trc3.drop end'.toNat)) ⋆
                                  array (t := i32) c.pWorkStk2 ws2 ⋆
                                  FullCandsFrame c { s with scratch :=
                                    { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                                  R) m3 := sep_ac hm3'
                              rwa [fullCands_join_array hprefL'] at hm3a
                            rw [fullMem_eq_candsFrame, fullCandsFrame_irrel]
                            exact sep_ac hm3_arr
                          c0_hfast
                          exact hJe end' m3 (by omega)
                            ⟨by omega, by omega, trc4, htrc4L, hbd4L, hm4⟩))))
        (fun _ hJcur => by
          c0_hsplit
          · c0_hfast
            exact hJcur 0#64 m ⟨rfl, hcv_pos⟩
          · c0_hfast
            refine hJcur _ m ⟨rfl, ?_⟩
            rw [← hcv_mod]; bv_omega))
    (fun _ hJcomp => by
      c0_hsplit
      · c0_hfast; exact hJcomp 5#32 m rfl
      · c0_hfast; exact hJcomp _ m rfl)

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
