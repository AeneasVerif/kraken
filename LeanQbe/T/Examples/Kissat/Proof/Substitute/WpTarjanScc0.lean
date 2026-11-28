/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.TarjanInv1

/-!
# Step Helpers for `full_tarjan_scc` (`Proof.Substitute.WpTarjanScc0`)

Factored state-preservation, `bv_c0`, and watch-slice helper theorems used by
`WpTarjanScc.lean` so every declaration remains compact (`<= 450` LOC).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

namespace SubstSccTactics

@[scoped bv_c0]
theorem bv64_ushr1_nat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0]
theorem bv64_ushr1_bv (x : BitVec 64) : (x >>> (1 : BitVec 64)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0]
theorem bv32_ushr1_nat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0]
theorem bv32_ushr1_bv (x : BitVec 32) : (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0]
theorem bv32_ushr1_mod (x : BitVec 32) :
    (x >>> (BitVec.toNat (1 : BitVec 32) % 32)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0]
theorem bv64_ofNat_toNat (n : Nat) : (BitVec.ofNat 64 n).toNat = n % 2 ^ 64 :=
  BitVec.toNat_ofNat n 64

@[scoped bv_c0]
theorem bv32_ofNat_toNat (n : Nat) : (BitVec.ofNat 32 n).toNat = n % 2 ^ 32 :=
  BitVec.toNat_ofNat n 32

@[scoped bv_c0]
theorem bv64_zero_toNat : (0 : BitVec 64).toNat = 0 := rfl

@[scoped bv_c0]
theorem bv32_zero_toNat : (0 : BitVec 32).toNat = 0 := rfl

@[scoped c0_store]
theorem c0_store_full_work_stk2_nat {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {n : Nat} {v : BitVec 32}
    (hm : (FullMem c s ⋆ R) m) (hn : n < s.scratch.work_stk2.length) (hfit : n < 2 ^ 64) :
    storeOk m i32 (c.pWorkStk2 + BitVec.ofNat 64 n * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
          work_stk2 := s.scratch.work_stk2.set n v } } ⋆ R)
        (storeMem m i32 (c.pWorkStk2 + BitVec.ofNat 64 n * 4) v) := by
  have hi : (BitVec.ofNat 64 n).toNat < (ArrayField.work_stk2.get s).length := by
    dsimp only [ArrayField.get]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]; exact hn
  have h := fullArr_store_bv .work_stk2 (i := BitVec.ofNat 64 n) v hi hm
  dsimp only [ArrayField.elemTy, ArrayField.elemAddrBv, ArrayField.ptr,
    ArrayField.set, ArrayField.get] at h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit] at h

@[scoped c0_store]
theorem c0_store_full_wsort_nat {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {n : Nat} {v : BitVec 32}
    (hm : (FullMem c s ⋆ R) m) (hn : n < s.scratch.wsort.length) (hfit : n < 2 ^ 64) :
    storeOk m i32 (c.pWsort + BitVec.ofNat 64 n * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
          wsort := s.scratch.wsort.set n v } } ⋆ R)
        (storeMem m i32 (c.pWsort + BitVec.ofNat 64 n * 4) v) := by
  have hi : (BitVec.ofNat 64 n).toNat < (ArrayField.wsort.get s).length := by
    dsimp only [ArrayField.get]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]; exact hn
  have h := fullArr_store_bv .wsort (i := BitVec.ofNat 64 n) v hi hm
  dsimp only [ArrayField.elemTy, ArrayField.elemAddrBv, ArrayField.ptr,
    ArrayField.set, ArrayField.get] at h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit] at h

@[scoped c0_store]
theorem c0_store_full_work_stk1_nat {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {n : Nat} {v : BitVec 32}
    (hm : (FullMem c s ⋆ R) m) (hn : n < s.scratch.work_stk1.length) (hfit : n < 2 ^ 64) :
    storeOk m i32 (c.pWorkStk1 + BitVec.ofNat 64 n * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
          work_stk1 := s.scratch.work_stk1.set n v } } ⋆ R)
        (storeMem m i32 (c.pWorkStk1 + BitVec.ofNat 64 n * 4) v) := by
  have hi : (BitVec.ofNat 64 n).toNat < (ArrayField.work_stk1.get s).length := by
    dsimp only [ArrayField.get]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]; exact hn
  have h := fullArr_store_bv .work_stk1 (i := BitVec.ofNat 64 n) v hi hm
  dsimp only [ArrayField.elemTy, ArrayField.elemAddrBv, ArrayField.ptr,
    ArrayField.set, ArrayField.get] at h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit] at h

@[scoped c0_store]
theorem c0_store_full_work_stk2_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {z : Nat} {v : BitVec 32}
    (hm : (FullMem c s ⋆ R) m) (hz : z = 0) (hn : 0 < s.scratch.work_stk2.length) :
    storeOk m i32 (c.pWorkStk2 + BitVec.ofNat 64 z * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
          work_stk2 := s.scratch.work_stk2.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pWorkStk2 + BitVec.ofNat 64 z * 4) v) := by
  subst hz; exact c0_store_full_work_stk2_nat hm hn (by decide)

@[scoped c0_store]
theorem c0_store_full_wsort_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {z : Nat} {v : BitVec 32}
    (hm : (FullMem c s ⋆ R) m) (hz : z = 0) (hn : 0 < s.scratch.wsort.length) :
    storeOk m i32 (c.pWsort + BitVec.ofNat 64 z * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
          wsort := s.scratch.wsort.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pWsort + BitVec.ofNat 64 z * 4) v) := by
  subst hz; exact c0_store_full_wsort_nat hm hn (by decide)

end SubstSccTactics

theorem tarjan_bv64_ushr1_nat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 :=
  SubstSccTactics.bv64_ushr1_nat x

theorem tarjan_bv32_ushr1_nat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 :=
  SubstSccTactics.bv32_ushr1_nat x

theorem m6_tarjan_init_step {c : FullCfg} {s0 st : FullState}
    (hag : AgreesExcept tarjanSccMask s0 st) (hlen : st.LengthsOk c)
    (hinc_st : st.core.inconsistent = s0.core.inconsistent)
    {i : Nat} (hi_lt : i < 2 * s0.core.cur_vars)
    (hinit : ∀ l < i,
      st.core.repr[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∧
      (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = 0 ∧
      (st.scratch.tarjan_reach[l]?.getD 0#32).toNat = 0) :
    let st1 : FullState :=
      { st with
        core := { st.core with repr := st.core.repr.set i 0xFFFFFFFF#32 }
        scratch := { st.scratch with
          tarjan_mark := st.scratch.tarjan_mark.set i 0#32
          tarjan_reach := st.scratch.tarjan_reach.set i 0#32 } }
    AgreesExcept tarjanSccMask s0 st1 ∧ st1.LengthsOk c ∧
    st1.core.inconsistent = s0.core.inconsistent ∧
    ∀ l < i + 1,
      st1.core.repr[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∧
      (st1.scratch.tarjan_mark[l]?.getD 0#32).toNat = 0 ∧
      (st1.scratch.tarjan_reach[l]?.getD 0#32).toNat = 0 := by
  have hcv_le := hlen.core_ok.cur_vars_le; have hcv := hag.get (·.core.cur_vars)
  have hrp_l := hlen.core_ok.repr_len; have htmk_l := hlen.scratch_ok.tarjan_mark_len
  have htrc_l := hlen.scratch_ok.tarjan_reach_len
  intro st1
  refine ⟨hag.update _,
    ⟨{ hlen.core_ok with repr_len := by dsimp only [st1]; rw [List.length_set, hrp_l] },
     { hlen.scratch_ok with
       tarjan_mark_len := by dsimp only [st1]; rw [List.length_set, htmk_l]
       tarjan_reach_len := by dsimp only [st1]; rw [List.length_set, htrc_l] }⟩,
    hinc_st, fun l hl => ?_⟩
  by_cases hli : l = i
  · subst hli; dsimp only [st1]
    rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
      List.getElem?_set_self (by omega)]
    exact ⟨rfl, rfl, rfl⟩
  · dsimp only [st1]
    rw [List.getElem?_set_ne (Ne.symm hli), List.getElem?_set_ne (Ne.symm hli),
      List.getElem?_set_ne (Ne.symm hli)]
    exact hinit l (by omega)

theorem m6_tarjan_fill_set_repr {c : FullCfg} {F_cur : List (List Nat)}
    {s0 st4 : FullState} {idx : Nat}
    (hag4 : AgreesExcept tarjanSccMask s0 st4) (hlen4 : st4.LengthsOk c)
    (hpr4 : FullPartialReprInv F_cur st4.core)
    (hfill4 : ∀ l < idx, st4.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hidx_lt : idx < 2 * s0.core.cur_vars) (hidx_lt32 : idx < 2 ^ 32) :
    let st5 : FullState := { st4 with core := { st4.core with
      repr := st4.core.repr.set idx (BitVec.setWidth 32 (BitVec.ofNat 64 idx)) } }
    AgreesExcept tarjanSccMask s0 st5 ∧ st5.LengthsOk c ∧
    FullPartialReprInv F_cur st5.core ∧
    st5.core.repr[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
    ∀ l < idx, st5.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
  have hrp4 := hlen4.core_ok.repr_len; have hcv4 := hag4.get (·.core.cur_vars)
  have hcv0_le := hlen4.core_ok.cur_vars_le
  have hbv32 : BitVec.setWidth 32 (BitVec.ofNat 64 idx) = BitVec.ofNat 32 idx := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64), Nat.mod_eq_of_lt hidx_lt32]
  intro st5
  have hpr5 : FullPartialReprInv F_cur st5.core := fun l hl hne => by
    dsimp only [st5] at hl ⊢; by_cases hli : l = idx
    · subst hli; rw [List.getElem?_set_self (by omega), Option.getD_some, hbv32,
        bv32_ofNat_toNat_lt hidx_lt32]; exact ⟨by omega, LitEquiv.refl _ _⟩
    · rw [List.getElem?_set_ne (Ne.symm hli)] at hne ⊢; exact hpr4 l hl hne
  have hfill_i : st5.core.repr[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    dsimp only [st5]; rw [List.getElem?_set_self (by omega), Option.getD_some, hbv32]; intro heq
    have := congrArg BitVec.toNat heq; rw [bv32_ofNat_toNat_lt hidx_lt32] at this
    have _hx := c.hmaxv; unfold dimacsBound at _hx
    revert this; simp; omega
  exact ⟨hag4.update _, ⟨{ hlen4.core_ok with repr_len := by simp [st5, hrp4] }, hlen4.scratch_ok⟩,
    hpr5, hfill_i, fun l hl => by
      dsimp only [st5]; rw [List.getElem?_set_ne (by omega)]; exact hfill4 l hl⟩

theorem m6_tarjan_fill_zero_step {c : FullCfg} {s0 st5 : FullState}
    {idx : Nat} {tarjan_mark4 tarjan_reach4 : List (BitVec 32)}
    (hag5 : AgreesExcept tarjanSccMask s0 st5) (hlen5 : st5.LengthsOk c)
    (htmk_eq : st5.scratch.tarjan_mark = tarjan_mark4)
    (htrc_eq : st5.scratch.tarjan_reach = tarjan_reach4)
    (hfill_i : st5.core.repr[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hfill_prev : ∀ l < idx, st5.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hprev4 : ∀ l < idx,
      tarjan_mark4[l]?.getD 0#32 = 0#32 ∧ tarjan_reach4[l]?.getD 0#32 = 0#32)
    (hidx_lt : idx < 2 * s0.core.cur_vars) :
    let st6 : FullState := { st5 with scratch := { st5.scratch with
      tarjan_mark := st5.scratch.tarjan_mark.set idx 0#32
      tarjan_reach := st5.scratch.tarjan_reach.set idx 0#32 } }
    AgreesExcept tarjanSccMask s0 st6 ∧ st6.LengthsOk c ∧
    ∀ l < idx + 1, st6.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      st6.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
      st6.scratch.tarjan_reach[l]?.getD 0#32 = 0#32 := by
  have hcv0_le := hlen5.core_ok.cur_vars_le; have hcv5 := hag5.get (·.core.cur_vars)
  have htmk5 := hlen5.scratch_ok.tarjan_mark_len
  have htrc5 := hlen5.scratch_ok.tarjan_reach_len
  intro st6
  refine ⟨hag5.update _,
    ⟨hlen5.core_ok, { hlen5.scratch_ok with
      tarjan_mark_len := by simp [st6, htmk5], tarjan_reach_len := by simp [st6, htrc5] }⟩,
    fun l hl => ?_⟩
  by_cases hli : l = idx
  · subst hli; dsimp only [st6]
    exact ⟨hfill_i, by rw [List.getElem?_set_self (by omega), Option.getD_some],
      by rw [List.getElem?_set_self (by omega), Option.getD_some]⟩
  · dsimp only [st6]
    rw [List.getElem?_set_ne (Ne.symm hli), List.getElem?_set_ne (Ne.symm hli),
      htmk_eq, htrc_eq]
    exact ⟨hfill_prev l (by omega), hprev4 l (by omega)⟩

theorem m6_tarjan_nb_slice_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root mroot reached dsp : Nat} {lit pos32 : BitVec 32}
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st3)
    (hdsp_pos : 0 < dsp) (hlit_get : lit = st3.scratch.work_stk2[dsp - 1]?.getD 0#32)
    (hpos_get : pos32 = st3.scratch.wsort[dsp - 1]?.getD 0#32)
    (hpos_lt : pos32.toNat < fullWatchSizeCore s0.core (lit.toNat ^^^ 1))
    (hflag0 : (s0.core.wstk[fullWatchOffCore s0.core (lit.toNat ^^^ 1) +
      pos32.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32)
    (hp2 : (pos32 + 2#32).toNat = pos32.toNat + 2) :
    let st4 : FullState := { st3 with scratch := { st3.scratch with
      wsort := st3.scratch.wsort.set (dsp - 1) (pos32 + 2#32) } }
    M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st4 ∧
    M6TarjanDfsInv.measure c s0 st4 reached dsp < M6TarjanDfsInv.measure c s0 st3 reached dsp := by
  have hslc3 := hd3.dpos_slice (dsp - 1) (by omega); rw [← hlit_get] at hslc3
  have hsc_nb : ∃ sc, sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
        (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)) =
      sc ++ sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + pos32.toNat)
        (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - pos32.toNat) ∧
      ∀ x ∈ sc, activeLit s0 x →
        1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
        (onScc st3 x →
          (st3.scratch.tarjan_reach[(lit.toNat ^^^ 1) ^^^ 1]?.getD 0#32).toNat ≤
            (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat) := by
    obtain ⟨sc, hseq, hsok⟩ := hslc3.2.2
    refine ⟨sc, by rw [← hpos_get] at hseq; exact hseq, fun x hx hax => ?_⟩
    have hs := hsok x hx hax
    have hnn : (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat := by
      simpa [litNeg] using litNeg_litNeg lit.toNat
    exact ⟨hs.1, fun hso => by rw [hnn]; exact hs.2.1 hso (fun h => by omega)⟩
  have hslc_nb := dpos_step_nonbin hpos_lt hp2 (hpos_get ▸ hslc3.2.1) hflag0 hsc_nb
  exact m6_tarjan_advance_dpos (pos' := pos32 + 2#32) hd3 hdsp_pos
    (by rw [← hpos_get, hp2]; omega) (by
      rw [← hlit_get]
      refine ⟨hslc_nb.1, hslc_nb.2.1, ?_⟩
      obtain ⟨sc, hseq, hsok⟩ := hslc_nb.2.2
      exact ⟨sc, hseq, fun x hx hax =>
        ⟨(hsok x hx hax).1, fun hso => by
          have hnn : (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat := by
            simpa [litNeg] using litNeg_litNeg lit.toNat
          have := (hsok x hx hax).2 hso; rwa [hnn] at this⟩⟩)

theorem m6_tarjan_bin_slice_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root mroot reached dsp : Nat} {lit pos32 : BitVec 32}
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st3)
    (hdsp_pos : 0 < dsp) (hlit_get : lit = st3.scratch.work_stk2[dsp - 1]?.getD 0#32)
    (hpos_get : pos32 = st3.scratch.wsort[dsp - 1]?.getD 0#32)
    (hpos_lt : pos32.toNat < fullWatchSizeCore s0.core (lit.toNat ^^^ 1))
    (hflag1 : (s0.core.wstk[fullWatchOffCore s0.core (lit.toNat ^^^ 1) +
      pos32.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32)
    (hp1 : (pos32 + 1#32).toNat = pos32.toNat + 1) :
    ∃ w0, s0.core.wstk[fullWatchOffCore s0.core (lit.toNat ^^^ 1) + pos32.toNat]? = some w0 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars ∧
      (w0 &&& 0x7FFFFFFF#32).toNat ∈ sliceBinsFrom s0.core.wstk
        (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
        (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)) ∧
      ((¬ activeLit s0 (w0 &&& 0x7FFFFFFF#32).toNat ∨
          (1 ≤ (st3.scratch.tarjan_mark[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#32).toNat ∧
            (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
              (st3.scratch.tarjan_reach[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#32).toNat)) →
        let st3a : FullState := { st3 with scratch := { st3.scratch with
          wsort := st3.scratch.wsort.set (dsp - 1) (pos32 + 1#32) } }
        M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st3a ∧
        M6TarjanDfsInv.measure c s0 st3a reached dsp <
          M6TarjanDfsInv.measure c s0 st3 reached dsp) ∧
      ((pos32 + 1#32).toNat ≤ fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ∧
        WatchSliceOk F_cur s0.core (lit.toNat ^^^ 1)
          (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + (pos32 + 1#32).toNat)
          (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - (pos32 + 1#32).toNat) ∧
        ∃ sc, sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
            (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)) =
          sc ++ sliceBinsFrom s0.core.wstk
            (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + (pos32 + 1#32).toNat)
            (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - (pos32 + 1#32).toNat) ∧
          ∀ x ∈ sc, activeLit s0 x →
            x = (w0 &&& 0x7FFFFFFF#32).toNat ∨
            (1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
              (onScc st3 x →
                (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
                  (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat))) := by
  have hslc3 := hd3.dpos_slice (dsp - 1) (by omega); rw [← hlit_get] at hslc3
  have hsc_b1 : ∃ sc, sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
        (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)) =
      sc ++ sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + pos32.toNat)
        (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - pos32.toNat) ∧
      ∀ x ∈ sc, activeLit s0 x →
        1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
        (onScc st3 x →
          (st3.scratch.tarjan_reach[(lit.toNat ^^^ 1) ^^^ 1]?.getD 0#32).toNat ≤
            (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat) := by
    obtain ⟨sc, hseq, hsok⟩ := hslc3.2.2
    refine ⟨sc, by rw [← hpos_get] at hseq; exact hseq, fun x hx hax => ?_⟩
    have hs := hsok x hx hax
    have hnn : (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat := by
      simpa [litNeg] using litNeg_litNeg lit.toNat
    exact ⟨hs.1, fun hso => by rw [hnn]; exact hs.2.1 hso (fun h => by omega)⟩
  obtain ⟨w0, hw0_eq, hot_lt, hbins_ot, hslc_b1_raw⟩ :=
    dpos_step_bin hpos_lt hp1 (hpos_get ▸ hslc3.2.1) hflag1 hsc_b1
  have hslc_b1 : (pos32 + 1#32).toNat ≤ fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ∧
      WatchSliceOk F_cur s0.core (lit.toNat ^^^ 1)
        (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + (pos32 + 1#32).toNat)
        (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - (pos32 + 1#32).toNat) ∧
      ∃ sc, sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
          (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)) =
        sc ++ sliceBinsFrom s0.core.wstk
          (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + (pos32 + 1#32).toNat)
          (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - (pos32 + 1#32).toNat) ∧
        ∀ x ∈ sc, activeLit s0 x →
          x = (w0 &&& 0x7FFFFFFF#32).toNat ∨
          (1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
            (onScc st3 x →
              (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
                (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat)) := by
    refine ⟨hslc_b1_raw.1, hslc_b1_raw.2.1, ?_⟩
    obtain ⟨sc, hseq, hsok⟩ := hslc_b1_raw.2.2
    exact ⟨sc, hseq, fun x hx hax =>
      (hsok x hx hax).elim Or.inl fun hs => Or.inr ⟨hs.1, fun hso => by
        have hnn : (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat := by
          simpa [litNeg] using litNeg_litNeg lit.toNat
        have := hs.2 hso; rwa [hnn] at this⟩⟩
  refine ⟨w0, hw0_eq, hot_lt, hbins_ot, fun hsk => ?_, hslc_b1⟩
  obtain ⟨hle, hslc, sc, hseq, hsok⟩ := hslc_b1
  exact m6_tarjan_advance_dpos (pos' := pos32 + 1#32) hd3 hdsp_pos
    (by rw [← hpos_get, hp1]; omega)
    (by rw [← hlit_get]; refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
        rcases hsok x hx hax with rfl | hpos
        · exact hsk.elim (fun hna => absurd hax hna) fun ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
        · exact hpos)

theorem m6_tarjan_pop_scan_done {F_cur : List (List Nat)} {c : FullCfg} {F0 : CNF Nat}
    {s0 st3 : FullState} {root mroot reached dsp : Nat} {lit : BitVec 32}
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st3)
    (hdsp_pos : 0 < dsp) (hlit_get : lit = st3.scratch.work_stk2[dsp - 1]?.getD 0#32)
    (hpos_ge : fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ≤
      (st3.scratch.wsort[dsp - 1]?.getD 0#32).toNat) :
    ∀ v, activeEdge s0 lit.toNat v → onScc st3 v →
      (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
        (st3.scratch.tarjan_reach[v]?.getD 0#32).toNat := by
  have hslc3 := hd3.dpos_slice (dsp - 1) (by omega); rw [← hlit_get] at hslc3
  intro v hv hov; obtain ⟨_, _, sc, hseq, hsok⟩ := hslc3
  have h0 : fullWatchSizeCore s0.core (lit.toNat ^^^ 1) -
      (st3.scratch.wsort[dsp - 1]?.getD 0#32).toNat = 0 := by omega
  rw [h0] at hseq
  rw [show sliceBinsFrom s0.core.wstk _ 0 = [] from rfl, List.append_nil] at hseq
  exact (hsok v (hseq ▸ hv.2.2) hv.2.1).2.1 hov (fun h => by omega)

theorem tarjan_u64_lt_2cv {c : FullCfg} {cur_vars : Nat} (hcv_le : cur_vars ≤ c.max_vars)
    (hmx : c.max_vars < 2 * 2 ^ 28) {x : BitVec 64}
    (hx : x.toNat < 2 * (cur_vars % 2 ^ 64) % 2 ^ 64) : x.toNat < 2 * cur_vars := by
  rw [Nat.mod_eq_of_lt (by omega : cur_vars < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * cur_vars < 2 ^ 64)] at hx
  exact hx

theorem tarjan_u64_eq_2cv {c : FullCfg} {cur_vars : Nat} (hcv_le : cur_vars ≤ c.max_vars)
    (hmx : c.max_vars < 2 * 2 ^ 28) {x : BitVec 64} (hle : x.toNat ≤ 2 * cur_vars)
    (hx : ¬x.toNat < 2 * (cur_vars % 2 ^ 64) % 2 ^ 64) : x.toNat = 2 * cur_vars := by
  rw [Nat.mod_eq_of_lt (by omega : cur_vars < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * cur_vars < 2 ^ 64)] at hx
  omega

theorem tarjan_bv32_zext_nat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

theorem tarjan_bv32_ushr1_zext_nat (x : BitVec 32) :
    (BitVec.setWidth 64 (x >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat = x.toNat / 2 := by
  rw [zext_toNat _ (by decide), show BitVec.toNat (1 : BitVec 32) % 32 = 1 from rfl,
    tarjan_bv32_ushr1_nat]

theorem tarjan_u32_ofNat_bv64 {n : Nat} (hn : n < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt hn]

theorem tarjan_bv32_add1_eq {r : BitVec 32} (h : r.toNat + 1 < 2 ^ 32)
    (h1 : (r + (1 : BitVec 32)).toNat = r.toNat + 1) :
    r + (1 : BitVec 32) = BitVec.ofNat 32 (r.toNat + 1) :=
  BitVec.eq_of_toNat_eq (by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h])

theorem tarjan_u64_dsp_sub1 {dsp : BitVec 64} (hdsp : 0 < dsp.toNat) :
    (dsp - 1#64).toNat = dsp.toNat - 1 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ _; omega))]; rfl

theorem tarjan_u64_dsp_sub2 {dsp : BitVec 64} (hdsp : 1 < dsp.toNat) :
    (dsp - 1#64 - 1#64).toNat = dsp.toNat - 2 := by
  have h1 := tarjan_u64_dsp_sub1 (by omega : 0 < dsp.toNat)
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1]; change 1 ≤ _; omega)), h1]; rfl

theorem m6_tarjan_root_init_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root : BitVec 64} {reached : BitVec 32}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm0 : s0.core.dense_mode = 0#64)
    (hag : AgreesExcept tarjanSccMask s0 st) (hlen : st.LengthsOk c)
    (hdfs : M6TarjanDfsInv c F0 F_cur s0 0 1 reached.toNat 0 st)
    (htop0 : st.core.tmp_cnt = 0) (hrt_lt : root.toNat < 2 * s0.core.cur_vars)
    (hc_tmk : st.scratch.tarjan_mark[root.toNat]'(by
      rw [hlen.scratch_ok.tarjan_mark_len]; have := hlen.core_ok.cur_vars_le
      have := hag.get (·.core.cur_vars); omega) = 0#32)
    (hc_fl : (st.core.flags[(root >>> (1 : Nat)).toNat]'(by
      rw [hlen.core_ok.flags_len, tarjan_bv64_ushr1_nat]; have := hlen.core_ok.cur_vars_le
      have := hag.get (·.core.cur_vars); omega) &&& (1 : BitVec 32)) ≠ 0#32) :
    reached.toNat < 2 * s0.core.cur_vars ∧
    (reached + (1 : BitVec 32)).toNat = reached.toNat + 1 ∧
    BitVec.setWidth 32 root = BitVec.ofNat 32 root.toNat ∧
    reached + (1 : BitVec 32) = BitVec.ofNat 32 (reached.toNat + 1) ∧
    let st_init : FullState :=
      { st with
        core := { st.core with tmp_cnt := 1 }
        scratch := { st.scratch with
          work_stk2 := st.scratch.work_stk2.set 0 (BitVec.ofNat 32 root.toNat)
          wsort := st.scratch.wsort.set 0 0#32
          tarjan_mark := st.scratch.tarjan_mark.set root.toNat (BitVec.ofNat 32 (reached.toNat + 1))
          tarjan_reach :=
            st.scratch.tarjan_reach.set root.toNat (BitVec.ofNat 32 (reached.toNat + 1))
          work_stk1 := st.scratch.work_stk1.set 0 (BitVec.ofNat 32 root.toNat) } }
    TarjanLoopBase c F_cur s0 st_init ∧
      M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1)
        (reached + (1 : BitVec 32)).toNat 1 st_init := by
  have hcv_le := hlen.core_ok.cur_vars_le; have hcv_eq := hag.get (·.core.cur_vars)
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htmk_rt0 : (st.scratch.tarjan_mark[root.toNat]?.getD 0#32).toNat = 0 := by
    rw [List.getElem?_eq_getElem (by rw [hlen.scratch_ok.tarjan_mark_len]; omega),
      Option.getD_some, hc_tmk]; rfl
  have hact_rt : activeLit s0 root.toNat := by
    refine ⟨hrt_lt, ?_⟩
    rw [← hag.get (·.core.flags),
      List.getElem?_eq_getElem (by rw [hlen.core_ok.flags_len]; omega), Option.getD_some]
    simpa only [tarjan_bv64_ushr1_nat, show (1 : BitVec 32) = 1#32 from rfl] using hc_fl
  have hr_lt := hdfs.reached_lt_of_unvisited hrt_lt htmk_rt0
  have hr1_nat : (reached + (1 : BitVec 32)).toNat = reached.toNat + 1 := bv32_add1_toNat (by omega)
  have hrt32_eq : BitVec.setWidth 32 root = BitVec.ofNat 32 root.toNat :=
    BitVec.eq_of_toNat_eq (by
      rw [bv32_trunc_toNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hr32_eq : reached + (1 : BitVec 32) = BitVec.ofNat 32 (reached.toNat + 1) :=
    tarjan_bv32_add1_eq (by omega) hr1_nat
  have hinit := m6_tarjan_init_root hw0 hdm0 hdfs htop0 hact_rt htmk_rt0
  refine ⟨hr_lt, hr1_nat, hrt32_eq, hr32_eq, hinit.2.toBase, ?_⟩
  rw [hr1_nat]; exact hinit.2

theorem m6_tarjan_dfs_head_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root mroot reached dsp : Nat} {lit : BitVec 32}
    (hwat0 : WatchesInv F_cur s0.core) (hcv3 : st3.core.cur_vars = s0.core.cur_vars)
    (hlen3 : st3.LengthsOk c) (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st3)
    (hdsp_pos : 0 < dsp) (hlit_get : lit = st3.scratch.work_stk2[dsp - 1]?.getD 0#32) :
    dsp ≤ 2 * s0.core.cur_vars ∧ lit.toNat < 2 * s0.core.cur_vars ∧
    lit.toNat ^^^ 1 < 2 * s0.core.cur_vars ∧
    (lit ^^^ 1#32).toNat < 2 * s0.core.cur_vars ∧
    activeLit s0 lit.toNat ∧
    (BitVec.setWidth 64 (lit ^^^ 1#32) <<< (1 : Nat)).toNat =
      2 * (lit.toNat ^^^ 1) ∧
    ((BitVec.setWidth 64 (lit ^^^ 1#32) <<< (1 : Nat)) + 1#64).toNat =
      2 * (lit.toNat ^^^ 1) + 1 ∧
    fullWatchOffCore s0.core (lit.toNat ^^^ 1) + fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ≤
      s0.core.wlen ∧
    (BitVec.setWidth 64 lit).toNat = lit.toNat ∧
    (BitVec.setWidth 64 lit).toNat < 2 * c.max_vars := by
  have hcv_le := hlen3.core_ok.cur_vars_le; have _ := c.hmaxv; unfold dimacsBound at *
  have hdsp_lt3 : dsp ≤ 2 * s0.core.cur_vars := by
    have := hd3.dsp_le; have := hd3.top_le; have := hd3.reached_le; omega
  have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by rw [hlit_get]; exact hd3.dv_lt (by omega)
  have hnl_lt_nat : lit.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hlit_lt
  have hnl_lt : (lit ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
    rw [bv32_xor1_toNat]; exact hnl_lt_nat
  have hlit_act : activeLit s0 lit.toNat := by
    obtain ⟨j, hj, hjeq⟩ := hd3.dv_on_scc (dsp - 1) (by omega); rw [← hlit_get] at hjeq
    exact hd3.tmk_active lit.toNat hlit_lt
      (by have := hd3.scc_tmk_ge j hj; rw [hjeq] at this; omega)
  have hnl2 : (BitVec.setWidth 64 (lit ^^^ 1#32) <<< (1 : Nat)).toNat =
      2 * (lit.toNat ^^^ 1) := by
    rw [FullArenaTactics.bv64_shl1_nat, zext_toNat _ (by decide), bv32_xor1_toNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hnl2_1 : ((BitVec.setWidth 64 (lit ^^^ 1#32) <<< (1 : Nat)) +
      1#64).toNat = 2 * (lit.toNat ^^^ 1) + 1 :=
    (bv64_add1_toNat (by rw [hnl2]; omega)).trans (by rw [hnl2])
  have hsb := hwat0.layout.bounds (lit.toNat ^^^ 1) hnl_lt_nat
  have hz_lit : (BitVec.setWidth 64 lit).toNat = lit.toNat := zext_toNat lit (by decide)
  exact ⟨hdsp_lt3, hlit_lt, hnl_lt_nat, hnl_lt, hlit_act, hnl2, hnl2_1, hsb, hz_lit,
    by rw [hz_lit]; omega⟩

theorem m6_tarjan_wvec_off {s0 st3 : FullState} (hwv3 : st3.core.wvec = s0.core.wvec)
    {idx nl : Nat} (hi : idx < st3.core.wvec.length) (hidx : idx = 2 * nl) :
    (st3.core.wvec[idx]'hi).toNat = fullWatchOffCore s0.core nl := by
  unfold fullWatchOffCore; rw [← hwv3, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [hidx]

theorem m6_tarjan_wvec_sz {s0 st3 : FullState} (hwv3 : st3.core.wvec = s0.core.wvec)
    {idx nl : Nat} (hi : idx < st3.core.wvec.length) (hidx : idx = 2 * nl + 1) :
    (st3.core.wvec[idx]'hi).toNat = fullWatchSizeCore s0.core nl := by
  unfold fullWatchSizeCore; rw [← hwv3, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [hidx]

theorem m6_tarjan_wstk_flag0 {s0 st3 : FullState} {woff pos : Nat} {off32 pos32 : BitVec 32}
    (hws3 : st3.core.wstk = s0.core.wstk)
    (hmod : (off32.toNat + pos32.toNat) % 2 ^ 64 = woff + pos)
    (hlt : woff + pos < st3.core.wstk.length)
    (hltm : (off32.toNat + pos32.toNat) % 2 ^ 64 < st3.core.wstk.length)
    (hc : (st3.core.wstk[(off32.toNat + pos32.toNat) % 2 ^ 64]'hltm &&&
      0x80000000#32) = 0#32) :
    (s0.core.wstk[woff + pos]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
  have hge := getElem_congr_idx hltm hlt hmod
  rw [hge] at hc
  rw [← hws3, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact hc

theorem m6_tarjan_wstk_flag1 {s0 st3 : FullState} {woff pos : Nat} {off32 pos32 : BitVec 32}
    (hws3 : st3.core.wstk = s0.core.wstk)
    (hmod : (off32.toNat + pos32.toNat) % 2 ^ 64 = woff + pos)
    (hlt : woff + pos < st3.core.wstk.length)
    (hltm : (off32.toNat + pos32.toNat) % 2 ^ 64 < st3.core.wstk.length)
    (hc : ¬(st3.core.wstk[(off32.toNat + pos32.toNat) % 2 ^ 64]'hltm &&&
      0x80000000#32) = 0#32) :
    (s0.core.wstk[woff + pos]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
  have hge := getElem_congr_idx hltm hlt hmod
  rw [hge] at hc
  rw [← hws3, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact hc

theorem m6_tarjan_ot_bounds {c : FullCfg} {s0 : FullState} {w0 : BitVec 32}
    (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars) :
    (BitVec.setWidth 64 (w0 &&& 0x7FFFFFFF#32)).toNat = (w0 &&& 0x7FFFFFFF#32).toNat ∧
    (BitVec.setWidth 64 ((w0 &&& 0x7FFFFFFF#32) >>>
      (BitVec.toNat (1 : BitVec 32) % 32))).toNat = (w0 &&& 0x7FFFFFFF#32).toNat / 2 ∧
    (BitVec.setWidth 64 (w0 &&& 0x7FFFFFFF#32)).toNat < 2 * c.max_vars ∧
    (BitVec.setWidth 64 ((w0 &&& 0x7FFFFFFF#32) >>>
      (BitVec.toNat (1 : BitVec 32) % 32))).toNat < c.max_vars := by
  have hz : (BitVec.setWidth 64 (w0 &&& 0x7FFFFFFF#32)).toNat =
      (w0 &&& 0x7FFFFFFF#32).toNat := zext_toNat _ (by decide)
  have hd : (BitVec.setWidth 64 ((w0 &&& 0x7FFFFFFF#32) >>>
      (BitVec.toNat (1 : BitVec 32) % 32))).toNat = (w0 &&& 0x7FFFFFFF#32).toNat / 2 :=
    tarjan_bv32_ushr1_zext_nat _
  exact ⟨hz, hd, by rw [hz]; omega, by rw [hd]; omega⟩

theorem m6_tarjan_nonroot_lt_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root mroot reached dsp : Nat} {lit rlit par : BitVec 32}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm0 : s0.core.dense_mode = 0#64)
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st3) (hdsp_pos : 0 < dsp)
    (hlit_get : lit = st3.scratch.work_stk2[dsp - 1]?.getD 0#32)
    (hrlit_eq : rlit = st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32)
    (hpos_ge : fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ≤
      (st3.scratch.wsort[dsp - 1]?.getD 0#32).toNat)
    (hne_tmk : rlit.toNat ≠ (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat)
    (hpar_get : par.toNat = (st3.scratch.work_stk2[dsp - 2]?.getD 0#32).toNat)
    (hz_par : (BitVec.setWidth 64 par).toNat = par.toNat)
    (hpar_lt_len : par.toNat < st3.scratch.tarjan_reach.length)
    (hz_par_lt_len : (BitVec.setWidth 64 par).toNat < st3.scratch.tarjan_reach.length)
    (hc : rlit.toNat <
      (st3.scratch.tarjan_reach[(BitVec.setWidth 64 par).toNat]'hz_par_lt_len).toNat) :
    let st4 : FullState := { st3 with scratch := { st3.scratch with
      tarjan_reach := st3.scratch.tarjan_reach.set
        (st3.scratch.work_stk2[dsp - 2]?.getD 0#32).toNat rlit } }
    1 < dsp ∧ TarjanLoopBase c F_cur s0 st4 ∧
    M6TarjanDfsInv c F0 F_cur s0 root mroot reached (dsp - 1) st4 ∧
    M6TarjanDfsInv.measure c s0 st4 reached (dsp - 1) <
      M6TarjanDfsInv.measure c s0 st3 reached dsp := by
  obtain ⟨hdsp_gt1, hpop_upd⟩ := m6_tarjan_pop_nonroot (rlit := rlit) hw0 hdm0 hd3 hdsp_pos
    (hlit_get ▸ hrlit_eq) (hlit_get ▸ hpos_ge) (hlit_get ▸ hne_tmk)
  have hge := getElem_congr_idx hz_par_lt_len hpar_lt_len hz_par
  rw [hge] at hc
  have hlt_par : rlit.toNat < (st3.scratch.tarjan_reach[(st3.scratch.work_stk2[dsp - 2]?.getD
      0#32).toNat]?.getD 0#32).toNat := by
    rw [← hpar_get, List.getElem?_eq_getElem hpar_lt_len, Option.getD_some]; exact hc
  obtain ⟨hd4, hm4⟩ := hpop_upd true (fun _ => hlt_par) (fun h => by cases h)
  rw [ite_eq_left rfl] at hd4 hm4
  exact ⟨hdsp_gt1, hd4.toBase, hd4, hm4⟩

theorem m6_tarjan_nonroot_ge_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root mroot reached dsp : Nat} {lit rlit par : BitVec 32}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm0 : s0.core.dense_mode = 0#64)
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st3) (hdsp_pos : 0 < dsp)
    (hlit_get : lit = st3.scratch.work_stk2[dsp - 1]?.getD 0#32)
    (hrlit_eq : rlit = st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32)
    (hpos_ge : fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ≤
      (st3.scratch.wsort[dsp - 1]?.getD 0#32).toNat)
    (hne_tmk : rlit.toNat ≠ (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat)
    (hpar_get : par.toNat = (st3.scratch.work_stk2[dsp - 2]?.getD 0#32).toNat)
    (hz_par : (BitVec.setWidth 64 par).toNat = par.toNat)
    (hpar_lt_len : par.toNat < st3.scratch.tarjan_reach.length)
    (hz_par_lt_len : (BitVec.setWidth 64 par).toNat < st3.scratch.tarjan_reach.length)
    (hc : ¬rlit.toNat <
      (st3.scratch.tarjan_reach[(BitVec.setWidth 64 par).toNat]'hz_par_lt_len).toNat) :
    1 < dsp ∧ TarjanLoopBase c F_cur s0 st3 ∧
    M6TarjanDfsInv c F0 F_cur s0 root mroot reached (dsp - 1) st3 ∧
    M6TarjanDfsInv.measure c s0 st3 reached (dsp - 1) <
      M6TarjanDfsInv.measure c s0 st3 reached dsp := by
  obtain ⟨hdsp_gt1, hpop_upd⟩ := m6_tarjan_pop_nonroot (rlit := rlit) hw0 hdm0 hd3 hdsp_pos
    (hlit_get ▸ hrlit_eq) (hlit_get ▸ hpos_ge) (hlit_get ▸ hne_tmk)
  have hge := getElem_congr_idx hz_par_lt_len hpar_lt_len hz_par
  rw [hge] at hc
  have hge_par : (st3.scratch.tarjan_reach[(st3.scratch.work_stk2[dsp - 2]?.getD
      0#32).toNat]?.getD 0#32).toNat ≤ rlit.toNat := by
    rw [← hpar_get, List.getElem?_eq_getElem hpar_lt_len, Option.getD_some]
    exact Nat.le_of_not_lt hc
  obtain ⟨hd4, hm4⟩ := hpop_upd false (fun h => by cases h) (fun _ => hge_par)
  rw [ite_eq_right Bool.false_ne_true] at hd4 hm4
  exact ⟨hdsp_gt1, hd4.toBase, hd4, hm4⟩

theorem m6_tarjan_disc_pure {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root mroot : Nat} {rch : BitVec 32} {dsp : BitVec 64}
    {lit pos32 ot : BitVec 32}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm0 : s0.core.dense_mode = 0#64)
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot rch.toNat dsp.toNat st3)
    (hdsp_pos : 0 < dsp.toNat)
    (hlit_get : lit = st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32)
    (hpos_get : pos32 = st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32)
    (hp1 : (pos32 + 1#32).toNat = pos32.toNat + 1)
    (hlit_act : activeLit s0 lit.toNat) (hact_ot : activeLit s0 ot.toNat)
    (hbins_ot : ot.toNat ∈ sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
      (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)))
    (htmk_ot0 : (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat = 0)
    (hslc_b1 : (pos32 + 1#32).toNat ≤ fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ∧
      WatchSliceOk F_cur s0.core (lit.toNat ^^^ 1)
        (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + (pos32 + 1#32).toNat)
        (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - (pos32 + 1#32).toNat) ∧
      ∃ sc, sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
          (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)) =
        sc ++ sliceBinsFrom s0.core.wstk
          (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + (pos32 + 1#32).toNat)
          (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - (pos32 + 1#32).toNat) ∧
        ∀ x ∈ sc, activeLit s0 x →
          x = ot.toNat ∨ (1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
            (onScc st3 x → (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
              (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat))) :
    let st4 : FullState :=
      { st3 with
        core := { st3.core with tmp_cnt := st3.core.tmp_cnt + 1 }
        scratch := { st3.scratch with
          wsort := (st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + 1#32)).set dsp.toNat 0#32
          tarjan_mark := st3.scratch.tarjan_mark.set ot.toNat (BitVec.ofNat 32 (rch.toNat + 1))
          tarjan_reach := st3.scratch.tarjan_reach.set ot.toNat (BitVec.ofNat 32 (rch.toNat + 1))
          work_stk1 := st3.scratch.work_stk1.set st3.core.tmp_cnt ot
          work_stk2 := st3.scratch.work_stk2.set dsp.toNat ot } }
    rch.toNat < 2 * s0.core.cur_vars ∧ st3.core.tmp_cnt < 2 * s0.core.cur_vars ∧
    dsp.toNat < 2 * s0.core.cur_vars ∧ (rch + 1#32).toNat = rch.toNat + 1 ∧
    rch + 1#32 = BitVec.ofNat 32 (rch.toNat + 1) ∧
    (dsp + 1#64).toNat = dsp.toNat + 1 ∧
    M6TarjanDfsInv c F0 F_cur s0 root mroot (rch + 1#32).toNat (dsp + 1#64).toNat st4 ∧
    M6TarjanDfsInv.measure c s0 st4 (rch + 1#32).toNat (dsp + 1#64).toNat <
      M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat := by
  have hcv_le := hd3.len_ok.core_ok.cur_vars_le; have hcv3 := hd3.agrees.get (·.core.cur_vars)
  have _ := c.hmaxv; unfold dimacsBound at *
  have hr_lt3 := hd3.reached_lt_of_unvisited hact_ot.1 htmk_ot0
  have htop_lt3 : st3.core.tmp_cnt < 2 * s0.core.cur_vars := by have := hd3.top_le; omega
  have hdsp_lt3 : dsp.toNat < 2 * s0.core.cur_vars := by have := hd3.dsp_le; omega
  have hr1_3 : (rch + 1#32).toNat = rch.toNat + 1 := bv32_add1_toNat (by omega)
  have hr32_3 := tarjan_bv32_add1_eq (by omega) hr1_3
  have hdsp1 : (dsp + 1#64).toNat = dsp.toNat + 1 := bv64_add1_toNat (by omega)
  obtain ⟨_, hdisc, hm_disc⟩ := m6_tarjan_discover_node hw0 hdm0 hd3 hdsp_pos
    (by rw [← hpos_get]; exact hp1) (by rw [← hlit_get]; exact ⟨hlit_act, hact_ot, hbins_ot⟩)
    htmk_ot0 (by rw [← hlit_get]; exact hslc_b1)
  exact ⟨hr_lt3, htop_lt3, hdsp_lt3, hr1_3, hr32_3, hdsp1,
    by rw [hr1_3, hdsp1]; exact hdisc, by rw [hr1_3, hdsp1]; exact hm_disc⟩

theorem m6_tarjan_be_pure {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root mroot reached dsp : Nat}
    {lit pos32 ot : BitVec 32}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm0 : s0.core.dense_mode = 0#64)
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st3)
    (hdsp_pos : 0 < dsp)
    (hlit_get : lit = st3.scratch.work_stk2[dsp - 1]?.getD 0#32)
    (hpos_get : pos32 = st3.scratch.wsort[dsp - 1]?.getD 0#32)
    (hp1 : (pos32 + 1#32).toNat = pos32.toNat + 1)
    (hlit_act : activeLit s0 lit.toNat) (hact_ot : activeLit s0 ot.toNat)
    (hbins_ot : ot.toNat ∈ sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
      (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)))
    (htmk_pos : 1 ≤ (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat)
    (htrc_lt : (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat <
      (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat)
    (hslc_b1 : (pos32 + 1#32).toNat ≤ fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ∧
      WatchSliceOk F_cur s0.core (lit.toNat ^^^ 1)
        (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + (pos32 + 1#32).toNat)
        (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - (pos32 + 1#32).toNat) ∧
      ∃ sc, sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (lit.toNat ^^^ 1))
          (fullWatchSizeCore s0.core (lit.toNat ^^^ 1)) =
        sc ++ sliceBinsFrom s0.core.wstk
          (fullWatchOffCore s0.core (lit.toNat ^^^ 1) + (pos32 + 1#32).toNat)
          (fullWatchSizeCore s0.core (lit.toNat ^^^ 1) - (pos32 + 1#32).toNat) ∧
        ∀ x ∈ sc, activeLit s0 x →
          x = ot.toNat ∨ (1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
            (onScc st3 x → (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
              (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat))) :
    let st4 : FullState := { st3 with scratch := { st3.scratch with
      wsort := st3.scratch.wsort.set (dsp - 1) (pos32 + 1#32)
      tarjan_reach := st3.scratch.tarjan_reach.set lit.toNat
        (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32) } }
    M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st4 ∧
    M6TarjanDfsInv.measure c s0 st4 reached dsp < M6TarjanDfsInv.measure c s0 st3 reached dsp := by
  obtain ⟨hinv, hm⟩ := m6_tarjan_back_edge hw0 hdm0 hd3 hdsp_pos
    (by rw [← hpos_get]; exact hp1) (by rw [← hlit_get]; exact ⟨hlit_act, hact_ot, hbins_ot⟩)
    htmk_pos rfl (by rw [← hlit_get]; exact htrc_lt) (by rw [← hlit_get]; exact hslc_b1)
  rw [← hlit_get] at hinv hm; exact ⟨hinv, hm⟩

theorem m6_tarjan_par_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root mroot reached : Nat} {dsp : BitVec 64}
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp.toNat st3)
    (hdsp_gt1 : 1 < dsp.toNat) :
    have hdv_l3 : st3.scratch.work_stk2.length = 2 * c.max_vars :=
      hd3.len_ok.scratch_ok.work_stk2_len
    have hdsp_lt3 : dsp.toNat ≤ 2 * s0.core.cur_vars := by
      have := hd3.dsp_le; have := hd3.top_le; have := hd3.reached_le; omega
    have hpar_idx : (dsp - 1#64 - 1#64).toNat = dsp.toNat - 2 :=
      tarjan_u64_dsp_sub2 hdsp_gt1
    have hpar_lt_stk : dsp.toNat - 2 < st3.scratch.work_stk2.length := by
      have hcv_le := hd3.len_ok.core_ok.cur_vars_le
      have : 2 * s0.core.cur_vars ≤ 2 * c.max_vars := by
        rw [← hd3.agrees.get (·.core.cur_vars)]; omega
      rw [hdv_l3]; omega
    have hpar_stk_lt : (dsp - 1#64 - 1#64).toNat <
        st3.scratch.work_stk2.length := by rw [hpar_idx]; exact hpar_lt_stk
    let par := st3.scratch.work_stk2[(dsp - 1#64 - 1#64).toNat]'hpar_stk_lt
    par.toNat = (st3.scratch.work_stk2[dsp.toNat - 2]?.getD 0#32).toNat ∧
    par.toNat < 2 * s0.core.cur_vars ∧
    (BitVec.setWidth 64 par).toNat = par.toNat ∧
    (BitVec.setWidth 64 par).toNat < st3.scratch.tarjan_reach.length := by
  have hcv_le := hd3.len_ok.core_ok.cur_vars_le; have _ := c.hmaxv; unfold dimacsBound at *
  have hcv_eq := hd3.agrees.get (·.core.cur_vars)
  have hdv_l3 := hd3.len_ok.scratch_ok.work_stk2_len
  have htrc_l3 := hd3.len_ok.scratch_ok.tarjan_reach_len
  have hdsp_lt3 : dsp.toNat ≤ 2 * s0.core.cur_vars := by
    have := hd3.dsp_le; have := hd3.top_le; have := hd3.reached_le; omega
  have hpar_idx := tarjan_u64_dsp_sub2 hdsp_gt1
  have hpar_lt_stk : dsp.toNat - 2 < st3.scratch.work_stk2.length := by rw [hdv_l3]; omega
  have hpar_stk_lt : (dsp - 1#64 - 1#64).toNat <
      st3.scratch.work_stk2.length := by rw [hpar_idx]; exact hpar_lt_stk
  let par := st3.scratch.work_stk2[(dsp - 1#64 - 1#64).toNat]'hpar_stk_lt
  have hpar_get : par.toNat = (st3.scratch.work_stk2[dsp.toNat - 2]?.getD 0#32).toNat := by
    dsimp only [par]; rw [List.getElem?_eq_getElem hpar_lt_stk, Option.getD_some]
    exact congrArg BitVec.toNat (getElem_congr_idx _ _ hpar_idx)
  have hpar_lt_cv : par.toNat < 2 * s0.core.cur_vars := by
    rw [hpar_get]; exact hd3.dv_lt (by omega)
  have hz_par : (BitVec.setWidth 64 par).toNat = par.toNat := zext_toNat par (by decide)
  exact ⟨hpar_get, hpar_lt_cv, hz_par, by rw [hz_par, htrc_l3]; omega⟩

theorem m6_tarjan_root_mr_reach {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root : BitVec 64} {reached rch : BitVec 32} {dsp : Nat}
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp st3)
    (hdsp_pos : 0 < dsp) (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hcv3 : st3.core.cur_vars = s0.core.cur_vars)
    (hrt_lt : root.toNat < 2 * s0.core.cur_vars)
    (hr1_nat : (reached + (1 : BitVec 32)).toNat = reached.toNat + 1) (k0 : Nat) :
    reached + (1 : BitVec 32) ≠ 0xFFFFFFFF#32 →
    (∀ j, k0 ≤ j → j < st3.core.tmp_cnt → BinReach (cnfOfClauses F_cur)
      (BitVec.setWidth 32 root).toNat (st3.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
    (∀ l < 2 * st3.core.cur_vars,
      (reached + (1 : BitVec 32)).toNat ≤ (st3.scratch.tarjan_mark[l]?.getD 0#32).toNat →
      BinReach (cnfOfClauses F_cur) (BitVec.setWidth 32 root).toNat l) := fun _ => by
  have _ := c.hmaxv; unfold dimacsBound at *
  rw [hr1_nat, bv32_trunc_toNat (x := root) (by omega)]
  exact ⟨fun j _ hj => hd3.mroot_reach hdsp_pos (st3.scratch.work_stk1[j]?.getD 0#32).toNat
      (hd3.scc_lt j hj) (hd3.scc_tmk_ge j hj).2,
    fun l hl hge => hd3.mroot_reach hdsp_pos l (by rw [← hcv3]; exact hl) hge⟩

theorem tarjan_bv64_nl_eq {c : FullCfg} {cv : Nat} (hcv_le : cv ≤ c.max_vars)
    (hmx : c.max_vars < 2 * 2 ^ 28) :
    (BitVec.ofNat 64 cv <<< (1 : Nat)).toNat = 2 * cv := by
  rw [FullArenaTactics.bv64_shl1_nat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : cv < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

theorem m6_tarjan_root_call_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st3 : FullState} {root : BitVec 64} {reached rch : BitVec 32} {dsp : Nat}
    {lit rlit : BitVec 32}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm0 : s0.core.dense_mode = 0#64)
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp st3)
    (hdsp_pos : 0 < dsp) (hcv3 : st3.core.cur_vars = s0.core.cur_vars)
    (hrt_lt : root.toNat < 2 * s0.core.cur_vars)
    (hr1_nat : (reached + 1#32).toNat = reached.toNat + 1)
    (hlit_get : lit = st3.scratch.work_stk2[dsp - 1]?.getD 0#32)
    (hrlit_eq : rlit = st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32)
    (hpos_ge : fullWatchSizeCore s0.core (lit.toNat ^^^ 1) ≤
      (st3.scratch.wsort[dsp - 1]?.getD 0#32).toNat)
    (hr_eq_bv : rlit = st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32) :
    ∃ k0, k0 < st3.core.tmp_cnt ∧
      st3.scratch.work_stk1[k0]?.getD 0#32 = st3.scratch.work_stk2[dsp - 1]?.getD 0#32 ∧
      (∀ j, k0 < j → j < st3.core.tmp_cnt →
        st3.scratch.work_stk1[j]?.getD 0#32 ≠ st3.scratch.work_stk2[dsp - 1]?.getD 0#32) ∧
      (dsp = 1 → k0 = 0) ∧
      (∀ j, k0 ≤ j → j < st3.core.tmp_cnt → LitEquiv (cnfOfClauses F_cur)
        (st3.scratch.work_stk1[j]?.getD 0#32).toNat
        (st3.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat) ∧
      (reached + 1#32 ≠ 0xFFFFFFFF#32 →
        (∀ j, k0 ≤ j → j < st3.core.tmp_cnt → BinReach (cnfOfClauses F_cur)
          (BitVec.setWidth 32 root).toNat (st3.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
        (∀ l < 2 * st3.core.cur_vars,
          (reached + 1#32).toNat ≤ (st3.scratch.tarjan_mark[l]?.getD 0#32).toNat →
          BinReach (cnfOfClauses F_cur) (BitVec.setWidth 32 root).toNat l)) := by
  have hcv_le := hd3.len_ok.core_ok.cur_vars_le
  have hscan := m6_tarjan_pop_scan_done hd3 hdsp_pos hlit_get hpos_ge
  have hr_eq := congrArg BitVec.toNat hr_eq_bv
  obtain ⟨k0, hk0_lt, hk0_bv, hk0_uniq, hk0_zero, hk0_eqv⟩ :=
    hd3.scc_pop_equiv hw0 hdm0 hdsp_pos (by rw [← hlit_get, ← hrlit_eq, ← hr_eq])
      (by rw [← hlit_get]; intro v hv hov
          exact Nat.le_trans (Nat.le_of_eq (hr_eq ▸ hrlit_eq ▸ rfl)) (hscan v hv hov))
  exact ⟨k0, hk0_lt, hk0_bv, hk0_uniq, hk0_zero, hk0_eqv,
    m6_tarjan_root_mr_reach hd3 hdsp_pos (hcv3 ▸ hcv_le) hcv3 hrt_lt hr1_nat k0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
