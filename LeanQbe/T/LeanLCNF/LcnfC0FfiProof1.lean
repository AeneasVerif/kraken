module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiSpec
import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof2
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proofs for `LcnfC0Ffi`, Part 1: Scratch Carve/Reclaim, `ByteArray`, & `FfiRes.ok`

Proves `Func.wp ffiEnv` contracts (`0` `import all`, `0` `@[expose]` on theorems/lemmas,
`XPost := False` / `noExit := true`) for the 8 core scratch and `ByteArray` FFI adapters:
- `lcnf_ffi_get_end` (`lcnf_ffi_get_end_wp`)
- `lcnf_ffi_carve_scratch` (`lcnf_ffi_carve_scratch_wp`)
- `lcnf_ffi_restore_scratch` (`lcnf_ffi_restore_scratch_wp`)
- `lcnf_ffi_ba_ptr` (`lcnf_ffi_ba_ptr_wp`)
- `lcnf_ffi_ba_len` (`lcnf_ffi_ba_len_wp`)
- `lcnf_ffi_mk_ok` (`lcnf_ffi_mk_ok_wp`)
- `lcnf_ffi_ba_of_bytes` (`lcnf_ffi_ba_of_bytes_wp`)
- `lcnf_ffi_ba_wrap_ok` (`lcnf_ffi_ba_wrap_ok_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil

local macro "ffi_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hsteps))
local macro "ffi_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_); try c0_let_simp))

/-! ## 1. Shared `@[c0_load]` / Framing Helpers for `rtC0Inv` & `ffi_ba_*` -/

theorem rtC0Inv_hdr_focus1 {rt : BitVec 64} {st : RtC0State} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    (LcnfC0Rt.At rt st.hdr ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ array64 st.hdr.s_work st.workBuf ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        largeFreeList st.hdr.s_large_free st.largeNodes ⋆
        region st.hdr.s_cur st.rem ⋆ R)) m := by
  unfold rtC0Inv at hm
  exact sep_ac hm

theorem rtC0Inv_store_s_end {rt : BitVec 64} {st : RtC0State} (newEnd : BitVec 64)
    (hle : st.hdr.s_cur.toNat ≤ newEnd.toNat) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (rtC0Inv rt st ⋆ R) m) :
    storeOk m i64 (rt + 33560) ∧
      (array64 rt st.extraArgs ⋆
        array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆
        LcnfC0Rt.At rt (st.withEnd newEnd hle).hdr ⋆
        array64 st.hdr.s_work st.workBuf ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        largeFreeList st.hdr.s_large_free st.largeNodes ⋆
        region st.hdr.s_cur st.rem ⋆ R) (storeMem m i64 (rt + 33560) newEnd) := by
  have h1 := LcnfC0Rt.store_s_end newEnd (rtC0Inv_hdr_focus1 hm)
  refine ⟨h1.1, ?_⟩
  exact sep_ac h1.2

@[local c0_load] private theorem ffi_load_rt_cur {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    loadVal m i64 (rt + 33552) = some st.hdr.s_cur :=
  LcnfC0Rt.load_s_cur (rtC0Inv_hdr_focus1 hm)

@[local c0_load] private theorem ffi_load_rt_end {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    loadVal m i64 (rt + 33560) = some st.hdr.s_end :=
  LcnfC0Rt.load_s_end (rtC0Inv_hdr_focus1 hm)

@[local c0_load] private theorem ffi_load_ba_len {baObj : LcnfObj} (hc : BaCanon baObj)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem baObj ⋆ R) m) :
    loadVal m i64 (baObj.addr + 8) = some (BitVec.ofNat 64 baObj.scalarData.length) := by
  rw [lcnfObjMem_sarray_eq hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1] at hm
  have hm1 : (cell64 (baObj.addr + 8#64) (BitVec.ofNat 64 baObj.scalarData.length) ⋆
      (cell64 baObj.addr baObj.header ⋆
        cell64 (baObj.addr + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
        bytes (baObj.addr + 24#64) baObj.scalarData ⋆
        region (baObj.addr + BitVec.ofNat 64 (24 + baObj.scalarData.length))
          (baObj.totalBytes - (24 + baObj.scalarData.length)) ⋆ R)) m := sep_ac hm
  exact r2_c0_load_cell64_add8 hm1

theorem region_to_2cells_rem_ffi {p : BitVec 64} {bytes : Nat} (hge : 16 ≤ bytes)
    (hfit : bytes ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region p bytes ⋆ R) m) :
    ∃ w0 w1 : BitVec 64,
      (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ region (p + 16#64) (bytes - 16) ⋆ R) m := by
  obtain ⟨w0, h0⟩ := region_pop_cell64 (by omega) hfit hm
  have h1in : (region (p + 8#64) (bytes - 8) ⋆ (cell64 p w0 ⋆ R)) m := sep_ac h0
  obtain ⟨w1, h1⟩ := region_pop_cell64 (by omega) (by omega) h1in
  rw [ptr_add_nat_r2, show bytes - 8 - 8 = bytes - 16 by omega] at h1
  exact ⟨w0, w1, (sep_ac h1 : (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆
    region (p + 16#64) (bytes - 16) ⋆ R) m)⟩

theorem ffi_ba_sz_mask_toNat (len : BitVec 64) (h : len.toNat ≤ ffiBaMaxCap) :
    ((24 + len + 7 &&& 18446744073709551608 : BitVec 64)).toNat = baAllocBytes len.toNat := by
  have hcap : len.toNat ≤ 268435416 := by unfold ffiBaMaxCap at h; exact h
  have hsum : (24 + len + 7 : BitVec 64).toNat = 24 + len.toNat + 7 := by
    have hlt1 : 24 + len.toNat < 2 ^ 64 := by omega
    have hlt2 : 24 + len.toNat + 7 < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_add, show (24 : BitVec 64).toNat = 24 from rfl,
      show (7 : BitVec 64).toNat = 7 from rfl, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  rw [show (18446744073709551608 : BitVec 64) = 0xfffffffffffffff8#64 from rfl,
    bv64_and_not7_toNat, hsum]
  unfold baAllocBytes align8
  omega

theorem ffi_ba_sz_mask_lt (len : BitVec 64) (h : len.toNat ≤ ffiBaMaxCap) :
    ((24 + len + 7 &&& 18446744073709551608 : BitVec 64)).toNat ≤ 268435448 := by
  rw [ffi_ba_sz_mask_toNat len h]
  unfold baAllocBytes align8 ffiBaMaxCap at *
  omega

theorem ffi_ba_alloc_bytes_bounds (len : Nat) (h : len ≤ ffiBaMaxCap) :
    rtMinObjBytes ≤ baAllocBytes len ∧ baAllocBytes len < rtMaxObjBytes ∧
    24 ≤ baAllocBytes len ∧ baAllocBytes len ≤ 2 ^ 64 ∧
    baAllocBytes len ≤ 268435448 := by
  unfold baAllocBytes align8 ffiBaMaxCap rtMinObjBytes rtMaxObjBytes at *
  omega

theorem ffi_rtC0Inv_withEnd_eq {rt : BitVec 64} {st : RtC0State} {wptr wend : BitVec 64}
    {wcap tailPad : Nat} {hle : st.hdr.s_cur.toNat ≤ wptr.toNat} {R : Mem 64 → Prop} {m : Mem 64}
    (hsplit : region st.hdr.s_cur st.rem =
      (region (st.withEnd wptr hle).hdr.s_cur (st.withEnd wptr hle).rem ⋆
        region wptr wcap ⋆ region wend tailPad))
    (hm : (array64 rt st.extraArgs ⋆
      array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      array64 (rt + 33024#64) st.freeList ⋆
      LcnfC0Rt.At rt (st.withEnd wptr hle).hdr ⋆
      array64 st.hdr.s_work st.workBuf ⋆
      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      region st.hdr.s_cur st.rem ⋆ R) m) :
    (rtC0Inv rt (st.withEnd wptr hle) ⋆ region wptr wcap ⋆ region wend tailPad ⋆ R) m := by
  rw [hsplit] at hm
  unfold rtC0Inv
  change (array64 rt st.extraArgs ⋆
    array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
    array64 (rt + 33024#64) st.freeList ⋆
    LcnfC0Rt.At rt (st.withEnd wptr hle).hdr ⋆
    array64 st.hdr.s_work st.workBuf ⋆
    smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
    largeFreeList st.hdr.s_large_free st.largeNodes ⋆
    region (st.withEnd wptr hle).hdr.s_cur (st.withEnd wptr hle).rem ⋆
    region wptr wcap ⋆ region wend tailPad ⋆ R) m
  exact sep_ac hm

/-! ## 2. Scratch Carve & Reclaim WP Proofs -/

theorem lcnf_ffi_get_end_wp :
    ∀ xs m Q X, ffiGetEndSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_get_end.body xs m Q X := by
  intro ⟨rt, ⟨⟩⟩ m Q X ⟨st, R, hm, hQ⟩
  dsimp only [Func.wp, lcnf_ffi_get_end, lcnf_ffi_get_end_body]
  ffi_steps
  exact hQ

theorem lcnf_ffi_carve_scratch_wp :
    ∀ xs m Q X, ffiCarveScratchSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_carve_scratch.body xs m Q X := by
  intro ⟨rt, reqBytes, ⟨⟩⟩ m Q X ⟨st, R, hm, hPost⟩
  dsimp only [Func.wp, lcnf_ffi_carve_scratch, lcnf_ffi_carve_scratch_body]
  by_cases hvalid : reqBytes = 0#64 ∨ 18446744073709551608#64 < reqBytes
  · have hnotOk : ¬ ffiCarveOk st reqBytes := by
      intro ⟨hnz, hhi, _⟩
      rcases hvalid with h0 | hgt
      · exact hnz h0
      · rw [BitVec.lt_def] at hgt
        have hval : (18446744073709551608#64 : BitVec 64).toNat = 2 ^ 64 - 8 := by decide
        omega
    rw [dite_eq_right (fun h => hnotOk h)] at hPost
    ffi_steps <;> first
      | exact hPost
      | (exfalso
         rcases hvalid with rfl | hgt
         · exact ‹(0#64 : BitVec 64) ≠ 0› rfl
         · rw [BitVec.lt_def] at hgt
           have : ¬ (18446744073709551608#64 : BitVec 64).toNat < reqBytes.toNat := by assumption
           exact this hgt)
  · have hnz : reqBytes ≠ 0#64 := fun h => hvalid (Or.inl h)
    have hhi : reqBytes.toNat ≤ 2 ^ 64 - 8 := by
      by_cases h : reqBytes.toNat ≤ 2 ^ 64 - 8
      · exact h
      · exfalso
        apply hvalid
        right
        rw [BitVec.lt_def, show (18446744073709551608#64 : BitVec 64).toNat = 2 ^ 64 - 8 by decide]
        exact Nat.lt_of_not_le h
    have hwcapBv := ffiCarveWcap_bv_eq hhi
    have hwcapLt : ffiCarveWcap reqBytes < 2 ^ 64 := by unfold ffiCarveWcap align8; omega
    have hwcapToNat : ((reqBytes + 7 &&& 18446744073709551608 : BitVec 64)).toNat =
        ffiCarveWcap reqBytes := by
      rw [show (7 : BitVec 64) = 7#64 from rfl,
        show (18446744073709551608 : BitVec 64) = 0xfffffffffffffff8#64 from rfl, hwcapBv,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt]
    by_cases hfit : st.hdr.s_cur.toNat ≤ (ffiCarveWend st.hdr.s_end).toNat ∧
        ffiCarveWcap reqBytes ≤ (ffiCarveWend st.hdr.s_end).toNat - st.hdr.s_cur.toNat
    · have hok : ffiCarveOk st reqBytes := ⟨hnz, hhi, hfit.1, hfit.2⟩
      rw [dite_eq_left hok] at hPost
      have hwprops := ffiCarveWptr_props hok
      have hcurLeWptr := hwprops.2.2.2.2.1
      have hwptrNz := hwprops.2.2.2.2.2.1
      have hwptrMod := hwprops.2.2.2.2.2.2.1
      have hsplit := rtC0Inv_carve_top_split hok
      have hst := rtC0Inv_store_s_end (ffiCarveWptr st reqBytes) hcurLeWptr hm
      ffi_steps <;> first
        | (exfalso
           have hwendLt : (ffiCarveWend st.hdr.s_end).toNat < st.hdr.s_cur.toNat := by assumption
           omega)
        | (exfalso
           have hc : (2 ^ 64 - st.hdr.s_cur.toNat +
               (ffiCarveWend st.hdr.s_end).toNat) % 2 ^ 64 < ffiCarveWcap reqBytes := by
             rw [← hwcapToNat]
             exact (by assumption : _)
           have hltEnd := (ffiCarveWend st.hdr.s_end).isLt
           omega)
        | (refine ⟨hst.1, ?_⟩
           let m' := storeMem m i64 (rt + 33560) (ffiCarveWptr st reqBytes)
           have hm' := hst.2
           ffi_steps
           dsimp only [Arg.val]
           have hmCarved := ffi_rtC0Inv_withEnd_eq hsplit.1 hm'
           have hwcapGe : reqBytes.toNat ≤ ffiCarveWcap reqBytes := by
             unfold ffiCarveWcap align8; omega
           have hwptrEq : (st.hdr.s_end &&& 18446744073709551608) -
               (reqBytes + 7 &&& 18446744073709551608) = ffiCarveWptr st reqBytes := by
             rw [show (7 : BitVec 64) = 7#64 from rfl,
               show (18446744073709551608 : BitVec 64) = 0xfffffffffffffff8#64 from rfl,
               hwcapBv]
             rfl
           rw [hwptrEq]
           exact hPost m' hwptrNz hwptrMod hwcapGe hsplit.2.2 rfl hmCarved)
    · have hnotOk : ¬ ffiCarveOk st reqBytes := fun h => hfit ⟨h.2.2.1, h.2.2.2⟩
      rw [dite_eq_right (fun h => hnotOk h)] at hPost
      ffi_steps <;> first
        | exact hPost
        | (exfalso
           have hc : ¬ (ffiCarveWend st.hdr.s_end).toNat < st.hdr.s_cur.toNat := by assumption
           have hle : st.hdr.s_cur.toNat ≤ (ffiCarveWend st.hdr.s_end).toNat := by omega
           have hhc : ¬ (2 ^ 64 - st.hdr.s_cur.toNat +
               (ffiCarveWend st.hdr.s_end).toNat) % 2 ^ 64 <
               ((reqBytes + 7 &&& 18446744073709551608 : BitVec 64)).toNat := by assumption
           rw [hwcapToNat] at hhc
           have hltEnd := (ffiCarveWend st.hdr.s_end).isLt
           exact hfit ⟨hle, by omega⟩)

theorem lcnf_ffi_restore_scratch_wp :
    ∀ xs m Q X, ffiRestoreScratchSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_restore_scratch.body xs m Q X := by
  intro ⟨rt, savedEnd, ⟨⟩⟩ m Q X
    ⟨stMid, wptr, wend, wcap, tailPad, R, hMidEnd, hadd1, hnat1, hnat2, hm, hk⟩
  dsimp only [Func.wp, lcnf_ffi_restore_scratch, lcnf_ffi_restore_scratch_body]
  have hmerge := rtC0Inv_restore_top_merge (st := stMid) hMidEnd hadd1 hnat1 hnat2
  have hle : stMid.hdr.s_cur.toNat ≤ savedEnd.toNat := by
    have := stMid.curLeEnd; rw [hMidEnd] at this; omega
  have hst := rtC0Inv_store_s_end savedEnd hle
    (sep_ac hm : (rtC0Inv rt stMid ⋆ (region wptr wcap ⋆ region wend tailPad ⋆ R)) m)
  ffi_steps
  refine ⟨hst.1, ?_⟩
  let m' := storeMem m i64 (rt + 33560) savedEnd
  have hm' := hst.2
  ffi_steps
  dsimp only [Arg.val] at ⊢
  have hmRestored : (rtC0Inv rt (stMid.withEnd savedEnd hle) ⋆ R) m' := by
    unfold rtC0Inv
    have hm1 : (array64 rt stMid.extraArgs ⋆
        array64 (rt + BitVec.ofNat 64 rtGlobalsOff) stMid.globals ⋆
        array64 (rt + 33024#64) stMid.freeList ⋆
        LcnfC0Rt.At rt (stMid.withEnd savedEnd hle).hdr ⋆
        array64 stMid.hdr.s_work stMid.workBuf ⋆
        smallPoolsAt stMid.freeList stMid.smallPools rtNumClasses ⋆
        largeFreeList stMid.hdr.s_large_free stMid.largeNodes ⋆
        (region stMid.hdr.s_cur stMid.rem ⋆ region wptr wcap ⋆ region wend tailPad) ⋆
        R) m' := sep_ac hm'
    rw [hmerge.1] at hm1
    exact sep_ac hm1
  exact hk (stMid.withEnd savedEnd hle) m'
    (stMid.withEnd_preservesMetaExceptEnd savedEnd hle) rfl hmerge.2.1 hmRestored

/-! ## 3. `ByteArray` & `FfiRes.ok` Adapter WP Proofs -/

theorem lcnf_ffi_ba_ptr_wp :
    ∀ xs m Q X, ffiBaPtrSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_ba_ptr.body xs m Q X := by
  intro ⟨ba, ⟨⟩⟩ m Q X hQ
  dsimp only [Func.wp, lcnf_ffi_ba_ptr, lcnf_ffi_ba_ptr_body, ffiBaPtrSpec] at hQ ⊢
  ffi_steps
  exact hQ

theorem lcnf_ffi_ba_len_wp :
    ∀ xs m Q X, ffiBaLenSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_ba_len.body xs m Q X := by
  intro ⟨ba, ⟨⟩⟩ m Q X ⟨baObj, R, haddr, hcanon, hm, hQ⟩
  subst haddr
  dsimp only [Func.wp, lcnf_ffi_ba_len, lcnf_ffi_ba_len_body]
  ffi_steps
  exact hQ

theorem lcnf_ffi_mk_ok_wp :
    ∀ xs m Q X, ffiMkOkSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_mk_ok.body xs m Q X := by
  intro ⟨rt, val, ⟨⟩⟩ m Q X ⟨st, R, hm, hPost⟩
  dsimp only [Func.wp, lcnf_ffi_mk_ok, lcnf_ffi_mk_ok_body]
  by_cases hrem : 16 ≤ st.rem
  · rw [ite_eq_left hrem] at hPost
    ffi_steps
    · exfalso
      have hc : st.hdr.s_end.toNat < st.hdr.s_cur.toNat := by assumption
      have := st.curLeEnd; omega
    · exfalso
      have hsub : (st.hdr.s_end - st.hdr.s_cur).toNat = st.rem := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr st.curLeEnd)]
        rfl
      have hc : (st.hdr.s_end - st.hdr.s_cur).toNat < 16 := by assumption
      rw [hsub] at hc; omega
    · ffi_call ffiEnv_lcnf_alloc
      dsimp only [lcnfAllocRemSpec, vals, Tup.map, Arg.val]
      refine ⟨st, R, by decide, by decide, by decide, Or.inr hrem, hm,
        fun p st' m1 hp0 hp8 hpr hremLe hremLo hm1 => ?_⟩
      obtain ⟨w0, w1, hp2⟩ := region_to_2cells_rem_ffi (by decide) (by decide)
        (sep_ac hm1 : (region p 16 ⋆ (rtC0Inv rt st' ⋆ R)) m1)
      have hpc : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆ (rtC0Inv rt st' ⋆ R))) m1 := by
        rw [show (16 - 16 : Nat) = 0 by decide, region_zero, sep_emp] at hp2
        exact sep_ac hp2
      change LeanQbe.T.wp _ _ _ _ _
      apply wp_store_sep (store_cell64 ffiResOkHeader hpc)
      intro m2 hm2
      ffi_steps
      have hm2' : (cell64 (p + 8#64) w1 ⋆ (cell64 p ffiResOkHeader ⋆ rtC0Inv rt st' ⋆ R)) m2 :=
        sep_ac hm2
      apply wp_store_sep (store_cell64 val hm2')
      intro m3 hm3
      ffi_steps
      have hmObj : (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p val) ⋆ R) m3 := by
        rw [lcnfObjMem_mkFfiResOkObj]
        exact sep_ac hm3
      exact hPost p st' m3 hp0 hp8 hpr hremLe hremLo (mkFfiResOkObj_canon hp0 hp8) hmObj
  · rw [ite_eq_right hrem] at hPost
    ffi_steps <;> first
      | exact hPost
      | (exfalso
         have hsub : (st.hdr.s_end - st.hdr.s_cur).toNat = st.rem := by
           rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr st.curLeEnd)]; rfl
         have hc : ¬ (st.hdr.s_end - st.hdr.s_cur).toNat < 16 := by assumption
         rw [hsub] at hc; omega)

theorem lcnf_ffi_ba_of_bytes_wp :
    ∀ xs m Q X, ffiBaOfBytesSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_ba_of_bytes.body xs m Q X := by
  intro ⟨rt, srcPtr, len, ⟨⟩⟩ m Q X ⟨st, srcData, R, hlen, hm, hPost⟩
  dsimp only [Func.wp, lcnf_ffi_ba_of_bytes, lcnf_ffi_ba_of_bytes_body]
  by_cases hvalid : len.toNat ≤ ffiBaMaxCap ∧ baAllocBytes len.toNat ≤ st.rem
  · rw [ite_eq_left hvalid] at hPost
    have hbaEq := ffi_ba_sz_mask_toNat len hvalid.1
    have hbaLe := ffi_ba_sz_mask_lt len hvalid.1
    have hbounds := ffi_ba_alloc_bytes_bounds len.toNat hvalid.1
    have hbaBv : ((24 + len + 7 &&& 18446744073709551608 : BitVec 64)) =
        BitVec.ofNat 64 (baAllocBytes len.toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [hbaEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hid : align8 (baAllocBytes len.toNat) = baAllocBytes len.toNat :=
      align8_idemp (24 + len.toNat)
    ffi_steps
    · exfalso; unfold ffiBaMaxCap at hvalid
      have hc : 268435416 < len.toNat := by assumption
      omega
    · exfalso; have hc : st.hdr.s_end.toNat < st.hdr.s_cur.toNat := by assumption
      have := st.curLeEnd; omega
    · exfalso
      have hsub : (st.hdr.s_end - st.hdr.s_cur).toNat = st.rem := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr st.curLeEnd)]; rfl
      have hc : (st.hdr.s_end - st.hdr.s_cur).toNat <
          ((24 + len + 7 &&& 18446744073709551608 : BitVec 64)).toNat := by assumption
      rw [hsub, hbaEq] at hc; omega
    · ffi_call ffiEnv_lcnf_alloc
      dsimp only [lcnfAllocRemSpec, vals, Tup.map, Arg.val]
      rw [hbaEq, hid]
      refine ⟨st, bytes srcPtr srcData ⋆ R, by rw [← hbaEq]; exact hbaLe, hbounds.1, hbounds.2.1,
        Or.inr hvalid.2, (sep_ac hm : (rtC0Inv rt st ⋆ (bytes srcPtr srcData ⋆ R)) m),
        fun p st' m1 hp0 hp8 hpr hremLe hremLo hm1 => ?_⟩
      obtain ⟨w0, w1, w2, hp3⟩ := region_to_3cells_rem hbounds.2.2.1 hbounds.2.2.2.1
        (sep_ac hm1 : (region p (baAllocBytes len.toNat) ⋆ (rtC0Inv rt st' ⋆
          bytes srcPtr srcData ⋆ R)) m1)
      have hpc : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
          region (p + 24#64) (baAllocBytes len.toNat - 24) ⋆
          rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) m1 := sep_ac hp3
      change LeanQbe.T.wp _ _ _ _ _
      apply wp_store_sep (store_cell64 baHeaderWord hpc)
      intro m2 hm2
      ffi_steps
      have hm2' : (cell64 (p + 8#64) w1 ⋆ (cell64 p baHeaderWord ⋆
          cell64 (p + 16#64) w2 ⋆ region (p + 24#64) (baAllocBytes len.toNat - 24) ⋆
          rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) m2 := sep_ac hm2
      apply wp_store_sep (store_cell64 len hm2')
      intro m3 hm3
      ffi_steps
      have hm3' : (cell64 (p + 16#64) w2 ⋆ (cell64 p baHeaderWord ⋆
          cell64 (p + 8#64) len ⋆ region (p + 24#64) (baAllocBytes len.toNat - 24) ⋆
          rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) m3 := sep_ac hm3
      apply wp_store_sep (store_cell64 len hm3')
      intro m4 hm4
      ffi_steps
      · have hpos : 0 < len.toNat := by assumption
        ffi_call ffiEnv_r2_mem_copy_bytes
        dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
        have hm4' : (bytes srcPtr srcData ⋆ region (p + 24#64) (baAllocBytes len.toNat - 24) ⋆
            (rtC0Inv rt st' ⋆ cell64 p baHeaderWord ⋆ cell64 (p + 8#64) len ⋆
              cell64 (p + 16#64) len ⋆ R)) m4 := sep_ac hm4
        refine ⟨srcData, baAllocBytes len.toNat - 24, _, hlen,
          by unfold baAllocBytes align8 at *; omega,
          by unfold baAllocBytes align8 ffiBaMaxCap at *; omega, hm4', fun m5 hm5 => ?_⟩
        ffi_steps
        apply hJ
        ffi_steps
        have hmParts : (cell64 p baHeaderWord ⋆
            cell64 (p + 8#64) (BitVec.ofNat 64 srcData.length) ⋆
            cell64 (p + 16#64) (BitVec.ofNat 64 len.toNat) ⋆
            bytes (p + 24#64) srcData ⋆
            region (p + 24#64 + BitVec.ofNat 64 srcData.length)
              (baAllocBytes len.toNat - 24 - srcData.length) ⋆
            (rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) m5 := by
          rw [hlen, show BitVec.ofNat 64 len.toNat = len from by simp]
          exact sep_ac hm5
        have hbaMem := mkBaObj_mem_of_parts hmParts
        have hbaCanon : BaCanon (mkBaObj p 1#32 len.toNat srcData) :=
          mkBaObj_canon hp0 hp8 (by decide) (by omega)
            (by unfold ffiBaMaxCap baMaxCap at *; exact hvalid.1)
        exact hPost p st' m5 hp0 hp8 hpr hremLe hremLo hbaCanon
          (sep_ac hbaMem : (rtC0Inv rt st' ⋆ lcnfObjMem (mkBaObj p 1#32 len.toNat srcData) ⋆
            bytes srcPtr srcData ⋆ R) m5)
      · have hlen0 : len.toNat = 0 := by
          have hc : ¬ 0 < len.toNat := by assumption
          omega
        have hlenbv : len = 0#64 := BitVec.eq_of_toNat_eq hlen0
        have hnil : srcData = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        have hmParts : (cell64 p baHeaderWord ⋆
            cell64 (p + 8#64) (BitVec.ofNat 64 ([] : List UInt8).length) ⋆
            cell64 (p + 16#64) (BitVec.ofNat 64 len.toNat) ⋆
            bytes (p + 24#64) [] ⋆
            region (p + 24#64 + BitVec.ofNat 64 ([] : List UInt8).length)
              (baAllocBytes len.toNat - 24 - ([] : List UInt8).length) ⋆
            (rtC0Inv rt st' ⋆ bytes srcPtr [] ⋆ R)) m4 := by
          rw [List.length_nil, bytes_nil_eq, show BitVec.ofNat 64 0 = len from hlenbv.symm,
            show BitVec.ofNat 64 len.toNat = len from by simp,
            show p + 24#64 + len = p + 24#64 from by rw [hlenbv, BitVec.add_zero],
            Nat.sub_zero, sep_emp]
          exact sep_ac hm4
        have hbaMem := mkBaObj_mem_of_parts hmParts
        have hbaCanon : BaCanon (mkBaObj p 1#32 len.toNat []) :=
          mkBaObj_canon hp0 hp8 (by decide) (by omega)
            (by unfold ffiBaMaxCap baMaxCap at *; exact hvalid.1)
        exact hPost p st' m4 hp0 hp8 hpr hremLe hremLo hbaCanon
          (sep_ac hbaMem : (rtC0Inv rt st' ⋆ lcnfObjMem (mkBaObj p 1#32 len.toNat []) ⋆
            bytes srcPtr [] ⋆ R) m4)
  · rw [ite_eq_right hvalid] at hPost
    by_cases hcap : len.toNat ≤ ffiBaMaxCap
    · have hbaEq := ffi_ba_sz_mask_toNat len hcap
      ffi_steps <;> first
        | exact hPost
        | (exfalso; unfold ffiBaMaxCap at hcap
           have hc : 268435416 < len.toNat := by assumption
           omega)
        | (exfalso
           have hsub : (st.hdr.s_end - st.hdr.s_cur).toNat = st.rem := by
             rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr st.curLeEnd)]; rfl
           have hc : ¬ (st.hdr.s_end - st.hdr.s_cur).toNat <
               ((24 + len + 7 &&& 18446744073709551608 : BitVec 64)).toNat := by assumption
           rw [hsub, hbaEq] at hc
           exact hvalid ⟨hcap, by omega⟩)
    · ffi_steps <;> first
        | exact hPost
        | (exfalso; unfold ffiBaMaxCap at hcap
           have hc : ¬ 268435416 < len.toNat := by assumption
           omega)

theorem lcnf_ffi_ba_wrap_ok_wp :
    ∀ xs m Q X, ffiBaWrapOkSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_ba_wrap_ok.body xs m Q X := by
  intro ⟨rt, srcPtr, len, ⟨⟩⟩ m Q X ⟨st, srcData, R, hlen, hm, hPost⟩
  dsimp only [Func.wp, lcnf_ffi_ba_wrap_ok, lcnf_ffi_ba_wrap_ok_body]
  by_cases hvalid : len.toNat ≤ ffiBaMaxCap ∧ baAllocBytes len.toNat + 16 ≤ st.rem
  · rw [ite_eq_left hvalid] at hPost
    have hbaEq := ffi_ba_sz_mask_toNat len hvalid.1
    ffi_steps
    · exfalso; unfold ffiBaMaxCap at hvalid
      have hc : 268435416 < len.toNat := by assumption
      omega
    · exfalso; have hc : st.hdr.s_end.toNat < st.hdr.s_cur.toNat := by assumption
      have := st.curLeEnd; omega
    · exfalso
      have hsub : (st.hdr.s_end - st.hdr.s_cur).toNat = st.rem := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr st.curLeEnd)]; rfl
      have hc : (st.hdr.s_end - st.hdr.s_cur).toNat <
          ((24 + len + 7 &&& 18446744073709551608 : BitVec 64) + 16).toNat := by assumption
      have hsum : ((24 + len + 7 &&& 18446744073709551608 : BitVec 64) + 16).toNat =
          baAllocBytes len.toNat + 16 := by
        have hlt : baAllocBytes len.toNat + 16 < 2 ^ 64 := by
          unfold baAllocBytes align8 ffiBaMaxCap at *; omega
        rw [BitVec.toNat_add, hbaEq, show (16 : BitVec 64).toNat = 16 from rfl,
          Nat.mod_eq_of_lt hlt]
      rw [hsub, hsum] at hc; omega
    · ffi_call ffiEnv_ba_of_bytes
      dsimp only [ffiBaOfBytesSpec, vals, Tup.map, Arg.val]
      refine ⟨st, srcData, R, hlen, hm, ?_⟩
      rw [ite_eq_left ⟨hvalid.1, by omega⟩]
      intro ba st1 m1 hba0 hba8 hpr1 hrem1Le hrem1Lo hbaCanon hm1
      ffi_steps
      ffi_call ffiEnv_mk_ok
      dsimp only [ffiMkOkSpec, vals, Tup.map, Arg.val]
      refine ⟨st1, lcnfObjMem (mkBaObj ba 1#32 len.toNat srcData) ⋆ bytes srcPtr srcData ⋆ R,
        sep_ac hm1, ?_⟩
      have hrem16 : 16 ≤ st1.rem := by omega
      rw [ite_eq_left hrem16]
      intro p st2 m2 hp0 hp8 hpr2 hrem2Le hrem2Lo hokCanon hm2
      ffi_steps
      exact hPost p ba st2 m2 hp0 hp8 hba0 hba8 (hpr1.trans hpr2) (by omega) (by omega)
        hbaCanon hokCanon (sep_ac hm2)
  · rw [ite_eq_right hvalid] at hPost
    by_cases hcap : len.toNat ≤ ffiBaMaxCap
    · have hbaEq := ffi_ba_sz_mask_toNat len hcap
      have hsum : ((24 + len + 7 &&& 18446744073709551608 : BitVec 64) + 16).toNat =
          baAllocBytes len.toNat + 16 := by
        have hlt : baAllocBytes len.toNat + 16 < 2 ^ 64 := by
          unfold baAllocBytes align8 ffiBaMaxCap at *; omega
        rw [BitVec.toNat_add, hbaEq, show (16 : BitVec 64).toNat = 16 from rfl,
          Nat.mod_eq_of_lt hlt]
      ffi_steps <;> first
        | exact hPost
        | (exfalso; unfold ffiBaMaxCap at hcap
           have hc : 268435416 < len.toNat := by assumption
           omega)
        | (exfalso
           have hsub : (st.hdr.s_end - st.hdr.s_cur).toNat = st.rem := by
             rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr st.curLeEnd)]; rfl
           have hc : ¬ (st.hdr.s_end - st.hdr.s_cur).toNat <
               ((24 + len + 7 &&& 18446744073709551608 : BitVec 64) + 16).toNat := by assumption
           rw [hsub, hsum] at hc
           exact hvalid ⟨hcap, by omega⟩)
    · ffi_steps <;> first
        | exact hPost
        | (exfalso; unfold ffiBaMaxCap at hcap
           have hc : ¬ 268435416 < len.toNat := by assumption
           omega)

end LeanQbe.T.LeanLCNF
