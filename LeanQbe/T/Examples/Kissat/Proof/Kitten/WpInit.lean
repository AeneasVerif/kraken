/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasBtAdd
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1

/-!
# Step-13 `Func.wp` Proof for `full_k6_init` (`3/14`, `Kissat.Proof.Kitten.WpInit`)

Certifies `full_k6_init_wp` (`step13K6InitSpec`) with `glue_used[33]` HWM skipping, clean scalar
header initialization, and `K6HwmClean` preservation. Zero legacy `Full*` imports; zero `@[expose]`
on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open LeanQbe.T.Examples.Kissat.Src.Kitten

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics FullArenaTactics

/-! ## 1. `full_k6_init` Loop State & Pure Preservation Helpers -/

private structure S13InitScalar (L : K6Layout) (nv : BitVec 32) (ks : K6State) : Prop where
  sh : ks.ShapesOk L
  nv_eq : ks.nv = nv
  nc_eq : ks.nc = 0#32
  lvl_eq : ks.lvl = 0#32
  prop_eq : ks.prop = 0#32
  te_eq : ks.trl_end = 0#32
  un_eq : ks.unass = nv
  inc_eq : ks.incons = 0#32
  tk_eq : ks.ticks = 0#32
  tkl_eq : ks.tick_lim = 16384#32
  al_eq : ks.alen = 0#32
  ac_eq : ks.acap = BitVec.ofNat 32 L.acap
  na_eq : ks.nassump = 0#32
  nk_eq : ks.nkl = 0#32
  nan_eq : ks.nana = 0#32
  st_eq : ks.status = 0#32
  ph_eq : ks.phase = 0#32
  op_eq : ks.openCnt = 0#32
  mv_eq : ks.max_v = L.mv32
  mo_eq : ks.max_orig = BitVec.ofNat 32 L.maxOrig
  mc_eq : ks.max_cl = BitVec.ofNat 32 L.maxCl
  nq_eq : ks.neq = 0#32

private theorem S13InitScalar.putArr {L : K6Layout} {nv : BitVec 32} {ks : K6State}
    (s : S13InitScalar L nv ks) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
    S13InitScalar L nv (ks.putArr f i v) := by
  refine ⟨s.sh.putArr f i v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩ <;>
    (cases f <;> simp only [K6State.putArr] <;> first
      | exact s.nv_eq | exact s.nc_eq | exact s.lvl_eq | exact s.prop_eq | exact s.te_eq
      | exact s.un_eq | exact s.inc_eq | exact s.tk_eq | exact s.tkl_eq | exact s.al_eq
      | exact s.ac_eq | exact s.na_eq | exact s.nk_eq | exact s.nan_eq | exact s.st_eq
      | exact s.ph_eq | exact s.op_eq | exact s.mv_eq | exact s.mo_eq | exact s.mc_eq
      | exact s.nq_eq)

private structure S13ArrInv (L : K6Layout) (ks0 : K6State) (nv lim : BitVec 32)
    (nLvl nRsn nFl nVal nWh : Nat) (ks : K6State) : Prop where
  sc : S13InitScalar L nv ks
  lvl_tail : ∀ v, lim.toNat ≤ v → v < L.maxV → ks.lvlArr[v]? = ks0.lvlArr[v]?
  rsn_tail : ∀ v, lim.toNat ≤ v → v < L.maxV → ks.rsn[v]? = ks0.rsn[v]?
  flags_tail : ∀ v, lim.toNat ≤ v → v < L.maxV → ks.flags[v]? = ks0.flags[v]?
  vals_tail : ∀ l, 2 * lim.toNat ≤ l → l < 2 * L.maxV → ks.vals[l]? = ks0.vals[l]?
  whead_tail : ∀ l, 2 * lim.toNat ≤ l → l < 2 * L.maxV → ks.whead[l]? = ks0.whead[l]?
  lvl : ∀ v < nLvl, ks.lvlArr[v]? = some 0#32
  rsn : ∀ v < nRsn, ks.rsn[v]? = some 0xFFFFFFFF#32
  fl : ∀ v < nFl, ks.flags[v]? = some 0#32
  val : ∀ l < nVal, ks.vals[l]? = some 0#32
  wh : ∀ l < nWh, ks.whead[l]? = some 0xFFFFFFFF#32

private theorem s13_arr_step (arr : List (BitVec 32)) {n : Nat} (hlen : arr.length = n)
    (i : Nat) (hi : i < n) (v : BitVec 32) (hv : ∀ j < i, arr[j]? = some v)
    (hbi : (BitVec.ofNat 32 i).toNat = i) :
    ∀ j < i + 1, (arr.set (BitVec.ofNat 32 i).toNat v)[j]? = some v := fun j hj => by
  by_cases hji : j = i
  · subst hji; rw [hbi, List.getElem?_set_self (by omega)]
  · rw [hbi, List.getElem?_set_ne (Ne.symm hji)]; exact hv j (by omega)

private theorem S13ArrInv.putQ {L : K6Layout} {ks0 ks : K6State} {nv lim : BitVec 32}
    {a b c d e : Nat} (h : S13ArrInv L ks0 nv lim a b c d e ks) (f : K6ArrField)
    (hf : f = .qprev ∨ f = .qnext ∨ f = .qstampArr) (i : Nat) (val : BitVec 32) :
    S13ArrInv L ks0 nv lim a b c d e (ks.putArr f i val) := by
  rcases hf with rfl | rfl | rfl <;> exact ⟨h.sc.putArr _ i val,
    h.lvl_tail, h.rsn_tail, h.flags_tail, h.vals_tail, h.whead_tail,
    h.lvl, h.rsn, h.fl, h.val, h.wh⟩

private theorem S13ArrInv.putVar {L : K6Layout} {ks0 ks : K6State} {nv lim : BitVec 32}
    {i n1 n2 n3 n4 n5 : Nat} (h : S13ArrInv L ks0 nv lim n1 n2 n3 n4 n5 ks)
    (hlim : lim.toNat ≤ L.maxV) (f : K6ArrField)
    (hf : f = .lvlArr ∨ f = .rsn ∨ f =
      .flags) (hi : i < lim.toNat) (hbi : (BitVec.ofNat 32 i).toNat = i)
    (val : BitVec 32) :
    let st' := ks.putArr f (BitVec.ofNat 32 i).toNat val
    (f = .lvlArr → i = n1 → val = 0#32 → S13ArrInv L ks0 nv lim (i + 1) n2 n3 n4 n5 st') ∧
    (f = .rsn → i = n2 → val = 0xFFFFFFFF#32 → S13ArrInv L ks0 nv lim n1 (i + 1) n3 n4 n5 st') ∧
    (f = .flags → i = n3 → val = 0#32 → S13ArrInv L ks0 nv lim n1 n2 (i + 1) n4 n5 st') := by
  have hne : ∀ v, lim.toNat ≤ v → (BitVec.ofNat 32 i).toNat ≠ v := fun v hv => by rw [hbi]; omega
  refine ⟨fun hf1 hn1 hv1 => ?_, fun hf2 hn2 hv2 => ?_, fun hf3 hn3 hv3 => ?_⟩
  · subst hf1 hn1 hv1
    exact ⟨h.sc.putArr _ _ _,
      fun v hv hlt => by k6_field; rw [List.getElem?_set_ne (hne v hv)]; exact h.lvl_tail v hv hlt,
      h.rsn_tail, h.flags_tail, h.vals_tail, h.whead_tail,
      fun v hv => by
        k6_field; exact s13_arr_step _ h.sc.sh.lvlArr_len i (by omega) _ h.lvl hbi v hv,
      h.rsn, h.fl, h.val, h.wh⟩
  · subst hf2 hn2 hv2
    exact ⟨h.sc.putArr _ _ _, h.lvl_tail,
      fun v hv hlt => by k6_field; rw [List.getElem?_set_ne (hne v hv)]; exact h.rsn_tail v hv hlt,
      h.flags_tail, h.vals_tail, h.whead_tail, h.lvl,
      fun v hv => by k6_field; exact s13_arr_step _ h.sc.sh.rsn_len i (by omega) _ h.rsn hbi v hv,
      h.fl, h.val, h.wh⟩
  · subst hf3 hn3 hv3
    exact ⟨h.sc.putArr _ _ _, h.lvl_tail, h.rsn_tail,
      fun v hv hlt => by
        k6_field; rw [List.getElem?_set_ne (hne v hv)]; exact h.flags_tail v hv hlt,
      h.vals_tail, h.whead_tail, h.lvl, h.rsn,
      fun v hv => by k6_field; exact s13_arr_step _ h.sc.sh.flags_len i (by omega) _ h.fl hbi v hv,
      h.val, h.wh⟩

private theorem S13ArrInv.putLit {L : K6Layout} {ks0 ks : K6State} {nv lim : BitVec 32}
    {i n1 n2 n3 n4 n5 : Nat} (h : S13ArrInv L ks0 nv lim n1 n2 n3 n4 n5 ks)
    (hlim : lim.toNat ≤ L.maxV) (f : K6ArrField)
    (hf : f = .vals ∨ f = .whead) (hi : i < 2 * lim.toNat) (hbi : (BitVec.ofNat 32 i).toNat = i)
    (val : BitVec 32) :
    let st' := ks.putArr f (BitVec.ofNat 32 i).toNat val
    (f = .vals → i = n4 → val = 0#32 → S13ArrInv L ks0 nv lim n1 n2 n3 (i + 1) n5 st') ∧
    (f = .whead → i = n5 → val = 0xFFFFFFFF#32 → S13ArrInv L ks0 nv lim n1 n2 n3 n4 (i + 1) st') :=
      by
  have hne : ∀ l, 2 * lim.toNat ≤ l → (BitVec.ofNat 32 i).toNat ≠ l := fun l hl => by
    rw [hbi]; omega
  refine ⟨fun hf1 hn1 hv1 => ?_, fun hf2 hn2 hv2 => ?_⟩
  · subst hf1 hn1 hv1
    exact ⟨h.sc.putArr _ _ _, h.lvl_tail, h.rsn_tail, h.flags_tail,
      fun l hl hlt => by k6_field; rw [List.getElem?_set_ne (hne l hl)]; exact h.vals_tail l hl hlt,
      h.whead_tail, h.lvl, h.rsn, h.fl,
      fun l hl => by k6_field; exact s13_arr_step _ h.sc.sh.vals_len i (by omega) _ h.val hbi l hl,
      h.wh⟩
  · subst hf2 hn2 hv2
    exact ⟨h.sc.putArr _ _ _, h.lvl_tail, h.rsn_tail, h.flags_tail, h.vals_tail,
      fun l hl hlt => by
        k6_field; rw [List.getElem?_set_ne (hne l hl)]; exact h.whead_tail l hl hlt,
      h.lvl, h.rsn, h.fl, h.val,
      fun l hl => by k6_field; exact s13_arr_step _ h.sc.sh.whead_len i (by omega) _ h.wh hbi l hl⟩

private theorem s13_k6_minScr_of_maxV_pos {cap : Nat} (hpos : k6MaxV cap ≠ 0) :
    k6MinScr ≤ cap := by
  unfold k6MaxV k6MinScr at *; split at hpos <;> simp_all

private theorem s13_k6_maxV_pos {cap : Nat} (hge : k6MinScr ≤ cap) :
    0 < k6MaxV cap := by
  unfold k6MaxV k6MinScr k6MaxVCap at *
  split
  · omega
  · split
    · decide
    · dsimp only; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_max_left 512 _)

private theorem s13_k6_maxV_le (cap : Nat) : k6MaxV cap ≤ 8192 := by
  unfold k6MaxV k6MaxVCap
  split
  · omega
  · split
    · decide
    · dsimp only; exact Nat.max_le.mpr ⟨by decide, Nat.min_le_left 8192 _⟩

private theorem s13_k6_acap_eq {L : K6Layout} (c : FullCfg) (hlen : L.scrLen = c.scratch_cap)
    (hmv : L.maxV = k6MaxV c.scratch_cap) :
    let mv := BitVec.ofNat 32 (k6MaxV c.scratch_cap)
    ((BitVec.ofNat 64 c.scratch_cap -
      ((1280#32 + (mv <<< (1 : Nat)) + 32#32 + 38#32 * mv).setWidth 64)).setWidth 32) =
      BitVec.ofNat 32 L.acap := by
  have h1 := L.hmaxV; have h2 := L.hacap
  unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed at hlen
  apply BitVec.eq_of_toNat_eq
  have : (BitVec.ofNat 32 (k6MaxV c.scratch_cap)).toNat = L.maxV := by
    rw [← hmv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  bv_omega

private theorem s13_init_ksZ {L : K6Layout} {kPtr : BitVec 64} {ks0 : K6State}
    {hdr : List (BitVec 32)}
    (hsh0 : ks0.ShapesOk L) (hlen : hdr.length = 32) (hzero : ∀ j < 32, hdr[j]? = some 0#32) :
    let ksZ : K6State :=
      { ks0 with
        nv := 0#32, nc := 0#32, lvl := 0#32, prop := 0#32, trl_end := 0#32, unass := 0#32,
        incons := 0#32, qfirst := 0#32, qlast := 0#32, qsearch := 0#32, qstamp := 0#32,
        ticks := 0#32, tick_lim := 0#32, alen := 0#32, acap := 0#32, nassump := 0#32,
        nkl := 0#32, nana := 0#32, status := 0#32, phase := 0#32, openCnt := 0#32,
        max_v := 0#32, max_orig := 0#32, max_cl := 0#32, neq := 0#32,
        hdrTail := List.replicate 7 0#32 }
    ksZ.ShapesOk L ∧ hdr = k6HdrWords ksZ ∧
      ((K6Tree L kPtr ks0).set (k6Path 0) (array (t := i32) kPtr (k6HdrWords ksZ))).eval =
        K6Mem L kPtr ksZ := by
  intro ksZ
  have hhk : hdr = k6HdrWords ksZ := by
    change hdr = List.replicate 32 0#32; apply List.ext_getElem?; intro j
    by_cases hj : j < 32
    · rw [hzero j hj, List.getElem?_eq_getElem (by simp; omega), List.getElem_replicate]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  exact ⟨{ hsh0 with hdrTail_len := List.length_replicate }, hhk, rfl⟩

private theorem s13_getD_some {xs : List (BitVec 32)} {i : Nat} {x : BitVec 32}
    (hi : i < xs.length) (h : xs[i]?.getD 0#32 = x) : xs[i]? = some x := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at h
  rw [List.getElem?_eq_getElem hi, h]

private theorem s13_k6_init_finish {L : K6Layout} {ks0 ks' : K6State} {hw nv lim : BitVec 32}
    (hsh0 : ks0.ShapesOk L) (hnv_le : nv.toNat ≤ L.maxV)
    (hlim_eq : lim = if nv = L.mv32 ∧ hw.ult L.mv32 then hw else nv)
    (hhwm0 : K6HwmClean L hw ks0) (hst : S13ArrInv L ks0 nv lim lim.toNat lim.toNat lim.toNat
      (2 * lim.toNat) (2 * lim.toNat) ks') :
    (∀ P, K6Inv L P ks') ∧ K6TrailSynced ks' ∧
    K6HwmClean L
      (if nv = L.mv32 then 0#32 else if hw.ult nv then nv else hw) ks' := by
  have hm := L.hmaxV; have hsh' := hst.sc.sh
  have hmv_toNat : L.mv32.toNat = L.maxV := by
    unfold K6Layout.mv32; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hult_iff : ∀ a b : BitVec 32, a.ult b = true ↔ a.toNat < b.toNat := fun a b =>
    decide_eq_true_iff
  have hclean0 : ∀ v, lim.toNat ≤ v → v < nv.toNat →
      ks0.lvlArr[v]? = some 0#32 ∧ ks0.rsn[v]? = some 0xFFFFFFFF#32 ∧
      ks0.flags[v]? = some 0#32 ∧ ks0.vals[2 * v]? = some 0#32 ∧
      ks0.vals[2 * v + 1]?.getD 0#32 = 0#32 ∧ ks0.whead[2 * v]?.getD 0#32 = 0xFFFFFFFF#32 ∧
      ks0.whead[2 * v + 1]?.getD 0#32 = 0xFFFFFFFF#32 := by
    intro v hlv hvnv; rw [hlim_eq] at hlv; split at hlv
    · rename_i hc
      rcases hhwm0 with rfl | ⟨_, hcl⟩
      · have hult_c : (0xFFFFFFFF#32 : BitVec 32).toNat < L.mv32.toNat := (hult_iff _ _).mp hc.2
        change 0xFFFFFFFF < L.mv32.toNat at hult_c; omega
      · have hvc := hcl v hlv (by omega)
        exact ⟨s13_getD_some (by rw [hsh0.lvlArr_len]; omega) hvc.1,
          s13_getD_some (by rw [hsh0.rsn_len]; omega) hvc.2.1,
          s13_getD_some (by rw [hsh0.flags_len]; omega) hvc.2.2.1,
          s13_getD_some (by rw [hsh0.vals_len]; omega) hvc.2.2.2.1,
          hvc.2.2.2.2.1, hvc.2.2.2.2.2.1, hvc.2.2.2.2.2.2⟩
    · omega
  have hvars' : ∀ v < nv.toNat, ks'.lvlArr[v]? = some 0#32 ∧ ks'.rsn[v]? = some 0xFFFFFFFF#32 ∧
      ks'.flags[v]? = some 0#32 := fun v hv => by
    by_cases hvl : v < lim.toNat
    · exact ⟨hst.lvl v hvl, hst.rsn v hvl, hst.fl v hvl⟩
    · have hc := hclean0 v (by omega) hv
      rw [hst.lvl_tail v (by omega) (by omega), hst.rsn_tail v (by omega) (by omega),
        hst.flags_tail v (by omega) (by omega)]
      exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  have hlits' : ∀ l < 2 * nv.toNat, ks'.vals[l]? = some 0#32 ∧
      ks'.whead[l]? = some 0xFFFFFFFF#32 := fun l hl => by
    by_cases hll : l < 2 * lim.toNat
    · exact ⟨hst.val l hll, hst.wh l hll⟩
    · have hc := hclean0 (l / 2) (by omega) (by omega)
      rw [hst.vals_tail l (by omega) (by omega), hst.whead_tail l (by omega) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one l with hm0 | hm1
      · rw [show l = 2 * (l / 2) by omega]
        exact ⟨hc.2.2.2.1, s13_getD_some (by rw [hsh0.whead_len]; omega) hc.2.2.2.2.2.1⟩
      · rw [show l = 2 * (l / 2) + 1 by omega]
        exact ⟨s13_getD_some (by rw [hsh0.vals_len]; omega) hc.2.2.2.2.1,
          s13_getD_some (by rw [hsh0.whead_len]; omega) hc.2.2.2.2.2.2⟩
  have hinv := k6Init_finish_inv hsh' hnv_le hst.sc.nv_eq hst.sc.nc_eq hst.sc.lvl_eq hst.sc.prop_eq
    hst.sc.te_eq hst.sc.un_eq hst.sc.ac_eq hst.sc.mv_eq hst.sc.mo_eq hst.sc.mc_eq hst.sc.al_eq
    hst.sc.inc_eq hst.sc.na_eq hst.sc.nk_eq hst.sc.nan_eq hvars' hlits'
  refine ⟨hinv.1, hinv.2, ?_⟩
  by_cases hmv_eq : nv = L.mv32
  · simp only [hmv_eq, ↓reduceIte]
    refine Or.inr ⟨Nat.zero_le _, fun v _ hvL => ?_⟩
    have hv' := hvars' v (by rw [hmv_eq, hmv_toNat]; exact hvL)
    have hl0 := hlits' (2 * v) (by rw [hmv_eq, hmv_toNat]; omega)
    have hl1 := hlits' (2 * v + 1) (by rw [hmv_eq, hmv_toNat]; omega)
    simp [hv'.1, hv'.2.1, hv'.2.2, hl0.1, hl0.2, hl1.1, hl1.2]
  · simp only [hmv_eq, ↓reduceIte]
    have hlim_nv : lim = nv := by rw [hlim_eq]; simp [hmv_eq]
    rcases hhwm0 with rfl | ⟨hwle, hcl⟩
    · have hno : (0xFFFFFFFF#32 : BitVec 32).ult nv = false :=
        Bool.eq_false_iff.mpr fun h => by
          have := (hult_iff _ _).mp h; change 0xFFFFFFFF < nv.toNat at this; omega
      simp only [hno, Bool.false_eq_true, ↓reduceIte]; exact Or.inl rfl
    · by_cases hult : hw.ult nv = true
      · simp only [hult, ↓reduceIte]
        refine Or.inr ⟨hnv_le, fun v hvL hvm => ?_⟩
        rw [hst.lvl_tail v (by rw [hlim_nv]; omega) hvm,
          hst.rsn_tail v (by rw [hlim_nv]; omega) hvm,
          hst.flags_tail v (by rw [hlim_nv]; omega) hvm,
          hst.vals_tail (2 * v) (by rw [hlim_nv]; omega) (by omega),
          hst.vals_tail (2 * v + 1) (by rw [hlim_nv]; omega) (by omega),
          hst.whead_tail (2 * v) (by rw [hlim_nv]; omega) (by omega),
          hst.whead_tail (2 * v + 1) (by rw [hlim_nv]; omega) (by omega)]
        exact hcl v (by have := (hult_iff _ _).mp hult; omega) hvm
      · simp only [hult, Bool.false_eq_true, ↓reduceIte]
        have hle_hw : nv.toNat ≤ hw.toNat :=
          Nat.le_of_not_lt fun h => hult ((hult_iff _ _).mpr h)
        refine Or.inr ⟨hwle, fun v hvL hvm => ?_⟩
        have hlv_le : lim.toNat ≤ v := by rw [hlim_nv]; exact Nat.le_trans hle_hw hvL
        rw [hst.lvl_tail v hlv_le hvm, hst.rsn_tail v hlv_le hvm, hst.flags_tail v hlv_le hvm,
          hst.vals_tail (2 * v) (by omega) (by omega),
          hst.vals_tail (2 * v + 1) (by omega) (by omega),
          hst.whead_tail (2 * v) (by omega) (by omega),
          hst.whead_tail (2 * v + 1) (by omega) (by omega)]
        exact hcl v hvL hvm

private theorem s13_ofNat_lt_of_bv {i n : Nat} (hn : n ≤ 2 * 8192) (hi : i ≤ n)
    (h : (BitVec.ofNat 32 i).toNat < n) : i < n := by
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h

private theorem s13_ofNat_eq_of_nlt {i n : Nat} (hn : n ≤ 2 * 8192) (hi : i ≤ n)
    (h : ¬ (BitVec.ofNat 32 i).toNat < n) : i = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h; omega

private theorem s13_toNat_lt {i n : Nat} (hn : n ≤ 2 * 8192) (h : i < n) :
    (BitVec.ofNat 32 i).toNat < n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h

private theorem s13_init_bv_succ (i : Nat) (h : i + 1 < 2 ^ 32) :
    (BitVec.ofNat 32 i + 1 : BitVec 32) = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt h]

@[local c0_store] private theorem s13_store_k6_qprev0 (v : BitVec 32)
    {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64}
    (h0 : (0#32 : BitVec 32).toNat < K6MemATactics.szV L) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.setWidth 64 (32 + 2 * L.mv32) * 4 +
      BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4) ∧
    (K6MemA L kPtr (ks.putArr .qprev 0 v) ⋆ R) (storeMem m i32 (kPtr +
      BitVec.setWidth 64 (32 + 2 * L.mv32) * 4 +
      BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 4) v) := by
  simpa using K6PtrTactics.store_k6_qprev_dyn v h0 hm

private theorem s13_init_scr_prep {c : FullCfg} {s : FullState} {L : K6Layout} {stW : K6State}
    {R : Mem 64 → Prop} {mW : Mem 64}
    (hscr_len : s.scratch.scratch_buf.length = L.scrLen) (hL_scr : L.scrLen = c.scratch_cap)
    (hlen : FullState.LengthsOk c s) (hmW : (K6MemA L (L.kPtr c.pScratchBuf) stW ⋆
      (FullK6Frame c L s ⋆ R)) mW) :
    let scr' := s.scratch.scratch_buf.take L.k6Base ++ stW.toSlab
    let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    k6StateOfScratch L scr' = stW ∧ s1.LengthsOk c ∧
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) ∧
      (FullMem c s1 ⋆ R) mW := by
  intro scr' s1
  obtain ⟨hshW, hmW_mem⟩ := k6MemA_to_mem hmW
  have hkbase : L.k6Base ≤ s.scratch.scratch_buf.length := by
    rw [hscr_len]; unfold K6Layout.scrLen; omega
  have hscr'_len : scr'.length = c.scratch_cap := by
    dsimp only [scr']
    rw [List.length_append, List.length_take_of_le hkbase, stW.toSlab_length hshW, ← hL_scr]
    unfold K6Layout.scrLen; omega
  exact ⟨by unfold k6StateOfScratch
            rw [k6_slab_drop_exact _ _ (List.length_take_of_le hkbase), K6State.ofSlab_toSlab hshW],
    k6_fullState_lengthsOk_scratch hlen hscr'_len,
    fun i hi => by
      dsimp only [scr']
      rw [List.getElem?_append_left (by rw [List.length_take_of_le hkbase]; omega),
        List.getElem?_take_of_lt hi],
    fullMem_join_k6 hkbase hshW (sep_ac hmW_mem : (FullK6Frame c L s ⋆ K6Mem L _ stW ⋆ R) mW)⟩

/-! ## 2. Parametric `Func.wp` Theorem for `full_k6_init` (`3/14`) -/

private theorem s13_init_fin
    {c : FullCfg} {s : FullState} {L : K6Layout} {nv hw : BitVec 32} {ksW : K6State}
    {gu' scr' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []}
    (hlen1 : FullState.LengthsOk c
      { core := s.core, scratch := { s.scratch with scratch_buf := scr' } })
    (hscr_pref : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?)
    (hstW : S13InitScalar L nv ksW) (hinvF : ∀ P, K6Inv L P ksW) (hsyncF : K6TrailSynced ksW)
    (hgu_other : ∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?)
    (hgu'_len : gu'.length = 64) (hmv_toNat : L.mv32.toNat = L.maxV)
    (hgu33_eq : gu'[33]? = some (if nv = L.mv32 then 0#32 else if hw.ult nv then nv else hw))
    (hhwmF : K6HwmClean L (if nv = L.mv32 then 0#32 else if hw.ult nv then nv else hw) ksW)
    (hcont : ∀ (scr' gu' : List (BitVec 32)) (m' : Mem 64),
      have ks' := k6StateOfScratch L scr';
      have s' :=
        { core := s.core, scratch := { s.scratch with glue_used := gu', scratch_buf := scr' } };
      FullState.LengthsOk c s' →
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (nv.toNat = L.maxV → gu'[33]? = some 0#32) →
      (nv.toNat < L.maxV →
        gu'[33]? = some 0xFFFFFFFF#32 ∨ nv.toNat ≤ (gu'[33]?.getD 0#32).toNat) →
      K6HwmClean L (gu'[33]?.getD 0#32) ks' →
      (∀ P, K6Inv L P ks') → K6TrailSynced ks' →
      ks'.nv = nv → ks'.nc = 0#32 → ks'.lvl = 0#32 → ks'.prop = 0#32 →
      ks'.trl_end = 0#32 → ks'.unass = nv → ks'.incons = 0#32 →
      ks'.nassump = 0#32 → ks'.status = 0#32 → ks'.openCnt = 0#32 →
      ks'.neq = 0#32 → (FullMem c s' ⋆ R) m' → Q () m')
    (hks'_eq : k6StateOfScratch L scr' = ksW)
    (hm : (FullMem c
        { s with scratch := { s.scratch with glue_used := gu', scratch_buf := scr' } } ⋆ R) m) :
    Q () m := by
  have hgu33_mv : nv.toNat = L.maxV → gu'[33]? = some 0#32 := fun h => by
    simpa [BitVec.eq_of_toNat_eq (h.trans hmv_toNat.symm)] using hgu33_eq
  have hhwm_lt : nv.toNat < L.maxV →
      gu'[33]? = some 0xFFFFFFFF#32 ∨ nv.toNat ≤ (gu'[33]?.getD 0#32).toNat := fun hlt => by
    have hne : nv ≠ L.mv32 := fun heq => Nat.ne_of_lt hlt (by rw [heq, hmv_toNat])
    rw [hgu33_eq]; simp only [hne, ↓reduceIte]; split
    · right; simp
    · rename_i hnult
      have hle_nv : nv.toNat ≤ hw.toNat := Nat.le_of_not_lt fun h => hnult (decide_eq_true h)
      by_cases hff : hw = 0xFFFFFFFF#32
      · left; simp [hff]
      · right; simp; omega
  exact hcont scr' gu' m ⟨hlen1.core_ok, { hlen1.scratch_ok with glue_used_len := hgu'_len }⟩
    hscr_pref hgu_other hgu33_mv hhwm_lt
    (hks'_eq ▸ (by rw [hgu33_eq, Option.getD_some]; exact hhwmF))
    (fun P => hks'_eq ▸ hinvF P) (hks'_eq ▸ hsyncF) (hks'_eq ▸ hstW.nv_eq)
    (hks'_eq ▸ hstW.nc_eq) (hks'_eq ▸ hstW.lvl_eq) (hks'_eq ▸ hstW.prop_eq)
    (hks'_eq ▸ hstW.te_eq) (hks'_eq ▸ hstW.un_eq) (hks'_eq ▸ hstW.inc_eq)
    (hks'_eq ▸ hstW.na_eq) (hks'_eq ▸ hstW.st_eq) (hks'_eq ▸ hstW.op_eq)
    (hks'_eq ▸ hstW.nq_eq) hm

open Lean Elab Tactic in
local elab "s13_init_step " i:ident st:ident hi:ident ih:ident
    szFn:ident fld:term:max val:term:max hlimBv:term:max upd:term:max : tactic => do
  let lId := mkIdent `L; let hm := mkIdent `hm
  let hiLt := mkIdent `hi_lt; let hbi := mkIdent `hbi
  evalTactic (← `(tactic| (
    have h_rw := $hlimBv
    try rw [h_rw] at *
    have $hiLt := s13_ofNat_lt_of_bv (by omega) $hi (by bv_omega)
    have hlt_sz : (BitVec.ofNat 32 $i).toNat < $szFn $lId := by
      unfold $szFn; exact s13_toNat_lt (by omega) (by omega)
    have $hbi : (BitVec.ofNat 32 $i).toNat = $i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    c0_hfast; rw [s13_init_bv_succ $i (by omega)]
    exact $ih ($i + 1, ($st).putArr $fld (BitVec.ofNat 32 $i).toNat $val) _
      (by omega) ⟨by omega, $upd, $hm⟩)))

/-- `3/14`: Parametric `Func.wp` proof for `full_k6_init`. -/
theorem full_k6_init_wp (Γ : Env) (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, step13K6InitSpec args m Q X → Func.wp Γ full_k6_init_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hbad, hok⟩
  have hscr_c := c.hscr
  have hcap64 : c.scratch_cap < 2 ^ 64 := by unfold dimacsBound at hscr_c; omega
  have hgu_len : 33 < s.scratch.glue_used.length := by rw [hlen.scratch_ok.glue_used_len]; omega
  have hgu33 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 33)).toNat <
      s.scratch.glue_used.length := by rw [hlen.scratch_ok.glue_used_len]; decide
  c0_hsteps_nogrp; refine k6_maxV_call_step hMaxV hcap64 ?_; c0_hsteps_nogrp
  · apply hbad; left; exact Nat.lt_of_not_ge fun hmin => by
      have := s13_k6_maxV_pos hmin; have := s13_k6_maxV_le c.scratch_cap
      have hz : ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) = 0#32 := ‹_›; bv_omega
  · apply hbad; right; have := s13_k6_maxV_le c.scratch_cap; bv_omega
  · have hmv_nz : ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) ≠ 0#32 := ‹_›
    have hm_pos : k6MaxV c.scratch_cap ≠ 0 := fun h0 =>
      hmv_nz (BitVec.eq_of_toNat_eq (by simp [h0]))
    have hge := s13_k6_minScr_of_maxV_pos hm_pos; have hm_le := s13_k6_maxV_le c.scratch_cap
    have hnv_le : nv.toNat ≤ k6MaxV c.scratch_cap := by bv_omega
    obtain ⟨L, hL_scr, hL_mv, hhwm0, hcont⟩ := hok hge hnv_le
    have hL_max := L.hmaxV; let hw := s.scratch.glue_used[33]
    have hmv32 : ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) = L.mv32 := by
      unfold K6Layout.mv32; rw [← hL_mv]; apply BitVec.eq_of_toNat_eq; bv_omega
    have hmv_toNat : L.mv32.toNat = L.maxV := by
      unfold K6Layout.mv32; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    let lim0 := if nv = L.mv32 ∧ hw.ult L.mv32 then hw else nv
    have hscr_len : s.scratch.scratch_buf.length = L.scrLen :=
      hlen.scratch_ok.scratch_buf_len.trans hL_scr.symm
    have hmF := hm; clear hm; rw [fullMem_eq_k6Frame hscr_len] at hmF
    let ks0 := k6StateOfScratch L s.scratch.scratch_buf
    have hsh0 : ks0.ShapesOk L := K6State.shapesOk_ofSlab_eq (by
      rw [List.length_drop, hscr_len]; unfold K6Layout.scrLen; omega)
    let kPtr := L.kPtr c.pScratchBuf
    have hmA : (K6MemA L kPtr ks0 ⋆ (FullK6Frame c L s ⋆ R)) m := k6Mem_to_amem hsh0 (sep_ac hmF)
    have hhdr0 := k6Focus_hdr (k6MemA_to_mem hmA).2
    have hmv_le : L.maxV ≤ 8192 := hL_mv ▸ hm_le
    have h33 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 33) : BitVec 64).toNat = 33 := rfl
    refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun lim m' => lim = lim0 ∧ m' = m) ?_ ?_
    · rintro _ _ m' ⟨rfl, rfl⟩; clear hscr_c hcap64; c0_hsteps_nogrp
      rw [hmv32, k6_ptr_base L c.pScratchBuf]
      refine wp_while_state (ts := [i32]) (α := Nat × List (BitVec 32))
        (fun st => (BitVec.ofNat 32 st.1, ())) (fun st => 32 - st.1)
        (fun st m' => st.1 ≤ 32 ∧ st.2.length = 32 ∧ (∀ j < st.1, st.2[j]? = some 0#32) ∧
          (array (t := i32) kPtr st.2 ⋆
            ((K6Tree L kPtr ks0).rest (k6Path 0) ⋆ (FullK6Frame c L s ⋆ R))) m') ?_ ?_
      · intro J0 hJ0; c0_hsteps!
        exact hJ0 (0, k6HdrWords ks0) _ ⟨by omega, k6HdrWords_length hsh0,
          fun _ hj => absurd hj (Nat.not_lt_zero _), hhdr0⟩
      · rintro J0 ⟨i, hdr⟩ m' ⟨hi_le, hhdr_len, hzero, hhm⟩ ih
        c0_hsteps_nogrp
        · have hi_lt : i < 32 := by bv_omega
          have hlt_arr : (BitVec.ofNat 32 i).toNat < hdr.length := by bv_omega
          have hbi : (BitVec.ofNat 32 i).toNat = i := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          c0_hsteps!; rw [s13_init_bv_succ i (by omega)]
          exact ih (i + 1, hdr.set (BitVec.ofNat 32 i).toNat 0#32) _ (by omega)
            ⟨by omega, by rw [List.length_set]; exact hhdr_len,
              s13_arr_step hdr hhdr_len i hi_lt 0#32 hzero hbi, by assumption⟩
        · have hi32 : i = 32 := by bv_omega
          subst hi32; dsimp only
          obtain ⟨hshZ, rfl, heval⟩ := s13_init_ksZ hsh0 hhdr_len hzero
          have hmZ : (K6MemA L kPtr _ ⋆ (FullK6Frame c L s ⋆ R)) m' :=
            k6Mem_to_amem hshZ (k6Unfocus_hdr heval hhm)
          clear hhm hhdr0 hmF hmA
          have hacap_eq := s13_k6_acap_eq c hL_scr hL_mv
          dsimp only at hacap_eq
          rw [show BitVec.ofNat 32 (k6MaxV c.scratch_cap) = L.mv32 from
            by rw [← hL_mv]; rfl] at hacap_eq
          c0_hsteps_nogrp
          refine wp_join_state (ts := []) (α := K6State) (fun _ => ())
            (fun st m'' => S13ArrInv L ks0 nv lim0 0 0 0 0 0 st ∧
              (K6MemA L kPtr st ⋆ (FullK6Frame c L s ⋆ R)) m'') ?_ ?_
          · intro Jsc st m1 ⟨hA0, hm1⟩
            have hlim_le : lim0.toNat ≤ L.maxV := by
              dsimp only [lim0]; split
              · rename_i hc; rw [← hmv_toNat]; exact Nat.le_of_lt (decide_eq_true_iff.mp hc.2)
              · rw [hL_mv]; exact hnv_le
            have hlim_szV : lim0.toNat ≤ szV L := hlim_le
            have hlim2_sz : 2 * lim0.toNat ≤ sz2V L := by unfold sz2V; omega
            let InvA := fun (n1 n2 n3 n4 n5 : Nat) (p : K6State) (m'' : Mem 64) =>
              S13ArrInv L ks0 nv lim0 n1 n2 n3 n4 n5 p ∧
                (K6MemA L kPtr p ⋆ (FullK6Frame c L s ⋆ R)) m''
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (α := K6State × BitVec 32) (fun p => (p.2, ()))
              (fun st m'' => InvA lim0.toNat lim0.toNat lim0.toNat 0 0 st.1 m'') ?_ ?_
            · rintro Jv ⟨st2, _⟩ m2 hA2
              have hlim2_bv : (2#32 * lim0).toNat = 2 * lim0.toNat := by
                rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              c0_hsteps_nogrp
              refine wp_while_state (ts := [i32]) (α := Nat × K6State)
                (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => 2 * lim0.toNat - p.1)
                (fun p m'' => p.1 ≤ 2 * lim0.toNat ∧
                  InvA lim0.toNat lim0.toNat lim0.toNat p.1 0 p.2 m'') ?_ ?_
              · intro Jp hJp; c0_hfast; exact hJp (0, st2) _ ⟨Nat.zero_le _, hA2⟩
              · rintro Jp ⟨iV, stV⟩ mV ⟨hiV, hAV, hmV⟩ ihV
                dsimp only at hiV hAV hmV ihV ⊢
                c0_hfast_nogrp
                · s13_init_step iV stV hiV ihV sz2V K6ArrField.vals 0#32 hlim2_bv
                    ((hAV.putLit hlim_le .vals (Or.inl rfl) hi_lt hbi 0#32).1 rfl rfl rfl)
                · have hiV_eq := s13_ofNat_eq_of_nlt (by omega) hiV (by rw [← hlim2_bv]; assumption)
                  subst hiV_eq
                  refine wp_while_state (ts := [i32]) (α := Nat × K6State)
                    (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => 2 * lim0.toNat - p.1)
                    (fun p m'' => p.1 ≤ 2 * lim0.toNat ∧
                      InvA lim0.toNat lim0.toNat lim0.toNat (2 * lim0.toNat) p.1 p.2 m'') ?_ ?_
                  · intro Jw hJw; c0_hfast; exact hJw (0, stV) _ ⟨Nat.zero_le _, hAV, hmV⟩
                  · rintro Jw ⟨iW, stW⟩ mW ⟨hiW, hAW, hmW⟩ ihW
                    dsimp only at hiW hAW hmW ihW ⊢
                    c0_hfast_nogrp
                    · s13_init_step iW stW hiW ihW sz2V K6ArrField.whead 0xFFFFFFFF#32 hlim2_bv
                        ((hAW.putLit hlim_le .whead (Or.inr rfl) hi_lt hbi 0xFFFFFFFF#32).2 rfl rfl
                          rfl)
                    · have hiW_eq :=
                        s13_ofNat_eq_of_nlt (by omega) hiW (by rw [← hlim2_bv]; assumption)
                      subst hiW_eq
                      have ⟨hinvF, hsyncF, hhwmF⟩ := s13_k6_init_finish hsh0 (hL_mv ▸ hnv_le)
                        (by dsimp only [lim0, hw]; simp only [List.getElem?_eq_getElem hgu_len,
                              Option.getD_some]) hhwm0 hAW
                      rw [List.getElem?_eq_getElem hgu_len, Option.getD_some] at hhwmF
                      obtain ⟨hks'_eq, hlen1, hscr_pref, hm_full⟩ :=
                        s13_init_scr_prep hscr_len hL_scr hlen hmW
                      have hgu_set : ∀ x : BitVec 32,
                      (s.scratch.glue_used.set 33 x)[33]? = some x :=
                        fun x => List.getElem?_set_self
                          (by rw [hlen.scratch_ok.glue_used_len]; omega)
                      have hgu_go := fun (gu' : List (BitVec 32)) (hlen_gu : gu'.length = 64)
                          (hother : ∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?)
                          (h33eq : gu'[33]? =
                            some (if nv = L.mv32 then 0#32 else if hw.ult nv then nv else hw))
                          {mF : Mem 64}
                          (hmF : (FullMem c { s with scratch := { s.scratch with
                            glue_used := gu',
                            scratch_buf :=
                              s.scratch.scratch_buf.take L.k6Base ++ stW.toSlab } } ⋆ R)
                              mF) =>
                        s13_init_fin hlen1 hscr_pref hAW.sc hinvF hsyncF hother hlen_gu hmv_toNat
                          h33eq hhwmF hcont hks'_eq hmF
                      c0_hsteps_nogrp
                      try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                      c0_hsplit
                      · have hnv_mv : nv = L.mv32 := by rw [← hmv32] at *; bv_omega
                        c0_hsteps!; try rw [h33] at hm
                        exact hgu_go _ (by simp [hlen.scratch_ok.glue_used_len])
                          (fun _ _ hne => List.getElem?_set_ne hne.symm)
                          (by rw [hgu_set]; simp [hnv_mv]) hm
                      · have hnv_ne : nv ≠ L.mv32 := by rw [← hmv32] at *; bv_omega
                        c0_hsteps_nogrp
                        try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                        c0_hsplit
                        · have hult : hw.ult nv = true := decide_eq_true (by
                            dsimp only [hw]; try rw [h33] at *
                            try simp only [show (OfNat.ofNat 33 % 2 ^ 64 : Nat) = 33 from rfl] at *
                            try rw [List.getElem?_eq_getElem hgu_len, Option.getD_some] at *
                            bv_omega)
                          c0_hsteps!; try rw [h33] at hm
                          exact hgu_go _ (by simp [hlen.scratch_ok.glue_used_len])
                            (fun _ _ hne => List.getElem?_set_ne hne.symm)
                            (by rw [hgu_set]; simp [hnv_ne, hult]) hm
                        · have hnult : hw.ult nv = false := Bool.eq_false_iff.mpr fun h => by
                            have hlt := decide_eq_true_iff.mp h
                            dsimp only [hw] at hlt; try rw [h33] at *
                            try simp only [show (OfNat.ofNat 33 % 2 ^ 64 : Nat) = 33 from rfl] at *
                            try rw [List.getElem?_eq_getElem hgu_len, Option.getD_some] at *
                            bv_omega
                          c0_hsteps!
                          exact hgu_go s.scratch.glue_used hlen.scratch_ok.glue_used_len
                            (fun _ _ _ => rfl)
                            (by rw [List.getElem?_eq_getElem hgu_len]; simp [hnv_ne, hnult]; rfl)
                            hm_full
            · intro Jv hJv
              c0_hfast_nogrp
              · have hpos_lim : 0 < lim0.toNat := by
                  have hc0 : (0#32 : BitVec 32).toNat < lim0.toNat := ‹_›; simpa using hc0
                refine wp_while_state (ts := [i32]) (α := Nat × K6State)
                  (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => lim0.toNat - p.1)
                  (fun p m'' => p.1 ≤ lim0.toNat ∧ InvA p.1 0 0 0 0 p.2 m'') ?_ ?_
                · intro J1 hJ1; c0_hfast; exact hJ1 (0, st) _ ⟨Nat.zero_le _, hA0, hm1⟩
                · rintro J1 ⟨i1, s1⟩ m1' ⟨hi1, hA1, hm1'⟩ ih1
                  dsimp only at hi1 hA1 hm1' ih1 ⊢
                  c0_hfast_nogrp
                  · s13_init_step i1 s1 hi1 ih1 szV K6ArrField.lvlArr 0#32 (Eq.refl lim0.toNat)
                      ((hA1.putVar hlim_le .lvlArr (Or.inl rfl) hi_lt hbi 0#32).1 rfl rfl rfl)
                  · have hi1_eq := s13_ofNat_eq_of_nlt (by omega) hi1 (by assumption)
                    subst hi1_eq
                    refine wp_while_state (ts := [i32]) (α := Nat × K6State)
                      (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => lim0.toNat - p.1)
                      (fun p m'' => p.1 ≤ lim0.toNat ∧ InvA lim0.toNat p.1 0 0 0 p.2 m'') ?_ ?_
                    · intro J2 hJ2; c0_hfast; exact hJ2 (0, s1) _ ⟨Nat.zero_le _, hA1, hm1'⟩
                    · rintro J2 ⟨i2, s2⟩ m2' ⟨hi2, hA2, hm2'⟩ ih2
                      dsimp only at hi2 hA2 hm2' ih2 ⊢
                      c0_hfast_nogrp
                      · s13_init_step i2 s2 hi2 ih2 szV K6ArrField.rsn 0xFFFFFFFF#32
                          (Eq.refl lim0.toNat) ((hA2.putVar hlim_le .rsn (Or.inr (Or.inl rfl))
                            hi_lt hbi 0xFFFFFFFF#32).2.1 rfl rfl rfl)
                      · have hi2_eq := s13_ofNat_eq_of_nlt (by omega) hi2 (by assumption)
                        subst hi2_eq
                        refine wp_while_state (ts := [i32]) (α := Nat × K6State)
                          (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => lim0.toNat - p.1)
                          (fun p m'' => p.1 ≤ lim0.toNat ∧
                            InvA lim0.toNat lim0.toNat p.1 0 0 p.2 m'') ?_ ?_
                        · intro J3 hJ3; c0_hfast; exact hJ3 (0, s2) _ ⟨Nat.zero_le _, hA2, hm2'⟩
                        · rintro J3 ⟨i3, s3⟩ m3' ⟨hi3, hA3, hm3'⟩ ih3
                          dsimp only at hi3 hA3 hm3' ih3 ⊢
                          c0_hfast_nogrp
                          · s13_init_step i3 s3 hi3 ih3 szV K6ArrField.flags 0#32
                              (Eq.refl lim0.toNat) ((hA3.putVar hlim_le .flags (Or.inr (Or.inr rfl))
                                hi_lt hbi 0#32).2.2 rfl rfl rfl)
                          · have hi3_eq := s13_ofNat_eq_of_nlt (by omega) hi3 (by assumption)
                            subst hi3_eq
                            refine wp_while_state (ts := [i32]) (α := Nat × K6State)
                              (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => lim0.toNat - p.1)
                              (fun p m'' => p.1 ≤ lim0.toNat ∧
                                InvA lim0.toNat lim0.toNat lim0.toNat 0 0 p.2 m'') ?_ ?_
                            · intro J4 hJ4; c0_hfast; exact hJ4 (0, s3) _ ⟨Nat.zero_le _, hA3, hm3'⟩
                            · rintro J4 ⟨i4, s4⟩ m4' ⟨hi4, hA4, hm4'⟩ ih4
                              c0_hfast_nogrp
                              · s13_init_step i4 s4 hi4 ih4 szV K6ArrField.qstampArr
                                  (BitVec.ofNat 32 i4 + 1#32) (Eq.refl lim0.toNat)
                                  (hA4.putQ .qstampArr (Or.inr (Or.inr rfl)) _ _)
                              · have h0_sz : (0#32 : BitVec 32).toNat < szV L := by
                                  unfold szV; bv_omega
                                c0_hfast_nogrp
                                refine wp_while_state (ts := [i32]) (α := Nat × K6State)
                                  (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => lim0.toNat - p.1)
                                  (fun p m'' => 1 ≤ p.1 ∧ p.1 ≤ lim0.toNat ∧
                                    InvA lim0.toNat lim0.toNat lim0.toNat 0 0 p.2 m'') ?_ ?_
                                · intro J5 hJ5; c0_hfast
                                  exact hJ5 (1, s4.putArr .qprev 0 0xFFFFFFFF#32) _
                                    ⟨Nat.le_refl _, hpos_lim,
                                      hA4.putQ .qprev (Or.inl rfl) _ _, hm⟩
                                · rintro J5 ⟨i5, s5⟩ m5' ⟨hi5_ge, hi5, hA5, hm5'⟩ ih5
                                  c0_hfast_nogrp
                                  · have hi5_lt := s13_ofNat_lt_of_bv (by omega) hi5 (by assumption)
                                    have hlt5 : (BitVec.ofNat 32 i5).toNat < szV L := by
                                      unfold szV; exact s13_toNat_lt (by omega) (by omega)
                                    c0_hfast; rw [s13_init_bv_succ i5 (by omega)]
                                    exact ih5 (i5 + 1, s5.putArr .qprev (BitVec.ofNat 32 i5).toNat
                                        (BitVec.ofNat 32 i5 - 1#32)) _ (by omega)
                                      ⟨by omega, by omega, hA5.putQ .qprev (Or.inl rfl) _ _, hm⟩
                                  · refine wp_while_state (ts := [i32]) (α := Nat × K6State)
                                      (fun p => (BitVec.ofNat 32 p.1, ()))
                                      (fun p => lim0.toNat - p.1)
                                      (fun p m'' => p.1 ≤ lim0.toNat ∧
                                        InvA lim0.toNat lim0.toNat lim0.toNat 0 0 p.2 m'') ?_ ?_
                                    · intro J6 hJ6; c0_hfast
                                      exact hJ6 (0, s5) _ ⟨Nat.zero_le _, hA5, hm5'⟩
                                    · rintro J6 ⟨i6, s6⟩ m6' ⟨hi6, hA6, hm6'⟩ ih6
                                      c0_hfast_nogrp
                                      · s13_init_step i6 s6 hi6 ih6 szV K6ArrField.qnext
                                          (BitVec.ofNat 32 i6 + 1#32) (Eq.refl lim0.toNat)
                                          (hA6.putQ .qnext (Or.inr (Or.inl rfl)) _ _)
                                      · try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                                        c0_hsteps_nogrp
                                        · have hnv1_lt : (nv - 1#32).toNat < szV L := by
                                            unfold szV; bv_omega
                                          c0_hfast
                                          exact hJv (s6.putArr .qnext (nv - 1#32).toNat
                                            0xFFFFFFFF#32, _) _
                                            ⟨hA6.putQ .qnext (Or.inr (Or.inl rfl)) _ _, hm⟩
                                        all_goals (c0_hfast; exact hJv (s6, _) _ ⟨hA6, hm6'⟩)
              · have hlim0 : lim0 = 0#32 := BitVec.eq_of_toNat_eq (by
                  have hc0 : ¬ (0#32 : BitVec 32).toNat < lim0.toNat := ‹_›
                  simp at hc0; exact hc0)
                exact hJv (st, _) _ ⟨{ hA0 with
                  lvl := fun v hv => by rw [hlim0] at hv; simp at hv,
                  rsn := fun v hv => by rw [hlim0] at hv; simp at hv,
                  fl := fun v hv => by rw [hlim0] at hv; simp at hv }, hm1⟩
          · intro Jsc hJsc
            have e_max_orig : L.mv32 * 3#32 = BitVec.ofNat 32 L.maxOrig := by
              unfold K6Layout.mv32 K6Layout.maxOrig; apply BitVec.eq_of_toNat_eq; bv_omega
            have e_max_cl : L.mv32 * 4#32 = BitVec.ofNat 32 L.maxCl := by
              unfold K6Layout.mv32 K6Layout.maxCl; apply BitVec.eq_of_toNat_eq; bv_omega
            c0_hsteps_nogrp <;> (
              c0_hsteps!; obtain ⟨hsh_sc, _⟩ := k6MemA_to_mem hm
              dsimp only [K6State.putHdr] at hsh_sc hm ⊢
              exact hJsc _ _ ⟨⟨⟨hsh_sc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                hacap_eq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, e_max_orig, e_max_cl, rfl⟩,
                fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
                fun _ _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h,
                fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩, hm⟩)
    · intro Jlim hJlim
      c0_hsteps!
      · have h1 : nv = L.mv32 := by rw [← hmv32]; assumption
        have h2 : hw.ult L.mv32 = true := decide_eq_true (by
          dsimp only [hw]; rw [← hmv32]; try rw [h33] at *
          try simp only [show (OfNat.ofNat 33 % 2 ^ 64 : Nat) = 33 from rfl] at *
          try rw [List.getElem?_eq_getElem hgu_len, Option.getD_some] at *; bv_omega)
        exact hJlim hw m ⟨by dsimp only [lim0]; simp [h1, h2], rfl⟩
      · have h1 : nv = L.mv32 := by rw [← hmv32]; assumption
        have h2 : hw.ult L.mv32 = false := Bool.eq_false_iff.mpr fun h => by
          have hlt := decide_eq_true_iff.mp h
          dsimp only [hw] at hlt; rw [← hmv32] at hlt; try rw [h33] at *
          try simp only [show (OfNat.ofNat 33 % 2 ^ 64 : Nat) = 33 from rfl] at *
          try rw [List.getElem?_eq_getElem hgu_len, Option.getD_some] at *; bv_omega
        exact hJlim nv m ⟨by dsimp only [lim0]; simp [h1, h2], rfl⟩
      · exact hJlim nv m ⟨by dsimp only [lim0]; simp [show nv ≠ L.mv32 by
          rw [← hmv32]; assumption], rfl⟩
end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
