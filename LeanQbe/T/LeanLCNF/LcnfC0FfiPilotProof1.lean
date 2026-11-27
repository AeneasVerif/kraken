/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiPilotProof0
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.ControlComb

/-!
# Shard `F3` Pilot XOR Wrapper WP Proofs & C0 ModuleOk (`LcnfC0FfiPilotProof1`)

Proves `lcnf_c0_xor_ba_wp` and `lcnf_c0_xor_nat_wp` (`XPost := False`, top-down `s_end`
carve/reclaim, non-aborting `5#64 = FfiRes.oom` / `3#64 = FfiRes.invalidInput`), and packages
the C0 wrapper composition `pilotC0Mod_moduleOk`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.LcnfC0FfiPilot

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Examples.Kissat.Plain
open scoped LeanQbe.T.ProofUtil

local macro "p1_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hfast))
local macro "p1_straight" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hstraight))
local macro "p1_call " h:ident : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_))

public section

private theorem bv64_len_shr56_eq_zero (len : Nat) (h : len ≤ 0x00ffffffffffffff) :
    (BitVec.ofNat 64 len >>> 56) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : len < 2 ^ 64), Nat.shiftRight_eq_div_pow,
    show (0#64 : BitVec 64).toNat = 0 from rfl]
  exact Nat.div_eq_of_lt (by omega)

private theorem bv64_len_and_mask56_eq (len : Nat) (h : len ≤ 0x00ffffffffffffff) :
    (BitVec.ofNat 64 len &&& 0x00ffffffffffffff#64) = BitVec.ofNat 64 len := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,
    show (0x00ffffffffffffff#64 : BitVec 64).toNat = 2 ^ 56 - 1 from by decide,
    Nat.mod_eq_of_lt (by omega : len < 2 ^ 64), Nat.and_two_pow_sub_one_eq_mod _ 56,
    Nat.mod_eq_of_lt (by omega)]

theorem lcnf_c0_xor_ba_wp :
    ∀ xs m Q X, pilotXorBASpec xs m Q X →
      Func.wp pilotC0Env lcnf_c0_xor_ba.body xs m Q X := by
  intro ⟨rt, ba, key, ⟨⟩⟩ m Q X ⟨st, baObj, R, haddr, hcanon, hfit, hm, hPost⟩
  dsimp only [Func.wp, lcnf_c0_xor_ba, lcnf_c0_xor_ba_body]
  subst haddr
  let len := baObj.scalarData.length
  let outData := baObj.scalarData.map (· ^^^ UInt8.ofNat key.toNat)
  have hbaMax : len ≤ ffiBaMaxCap := by
    have hlenEq := hcanon.2.2.2.2.2.2.1
    have hleCap := hcanon.2.2.2.2.2.2.2.1
    have hcapMax := hcanon.2.2.2.2.2.2.2.2
    unfold baMaxCap at hcapMax; unfold ffiBaMaxCap; omega
  have hlt56 : len ≤ 0x00ffffffffffffff := by unfold ffiBaMaxCap at hbaMax; omega
  p1_steps
  p1_call pilotC0Env_ba_len
  dsimp only [ffiBaLenSpec, vals, Tup.map, Arg.val]
  refine ⟨baObj, rtC0Inv rt st ⋆ R, rfl, hcanon, sep_ac hm, ?_⟩
  by_cases hzero : len = 0
  · have hlenBv0 : BitVec.ofNat 64 len = 0#64 := by simp [hzero]
    rw [hlenBv0]
    p1_steps
    · p1_call pilotC0Env_ba_wrap_ok
      dsimp only [ffiBaWrapOkSpec, vals, Tup.map, Arg.val]
      refine ⟨st, [], lcnfObjMem baObj ⋆ R, rfl, ?_, ?_⟩
      · rw [bytes_nil_eq, Std.ExtHashMap.sep_emp]
        exact sep_ac hm
      · have hzeroOk : (0 ≤ ffiBaMaxCap ∧ baAllocBytes 0 + 16 ≤ st.rem) ↔
            pilotXorBaOk st len := by
          simp [pilotXorBaOk, hzero]
        rw [show (0 : BitVec 64).toNat = 0 from rfl]
        simp only [bytes_nil_eq, Std.ExtHashMap.sep_emp]
        by_cases hok : pilotXorBaOk st len
        · rw [ite_eq_left hok] at hPost
          rw [ite_eq_left (hzeroOk.mpr hok)]
          intro p baNew st' m1 hp0 hp8 hba0 hba8 hpres hle hrem hbC hokC hm1
          have hnil : outData = [] := by
            have h0 : baObj.scalarData = [] := List.eq_nil_of_length_eq_zero hzero
            simp [outData, h0]
          have hlen0 : baObj.scalarData.length = 0 := hzero
          rw [hlen0] at hPost
          have hm1' : (rtC0Inv rt st' ⋆
              lcnfObjMem (mkFfiResOkObj p baNew) ⋆
              lcnfObjMem (mkBaObj baNew 1#32 0 outData) ⋆
              lcnfObjMem baObj ⋆ R) m1 := by
            rw [hnil]
            exact sep_ac hm1
          have hbC' : BaCanon (mkBaObj baNew 1#32 0 outData) := by rw [hnil]; exact hbC
          exact hPost p baNew st' m1 hp0 hp8 hba0 hba8 hpres.toExceptEnd hpres.2.2.2.1.symm
            hle hrem hbC' hokC hm1'
        · rw [ite_eq_right hok] at hPost
          rw [ite_eq_right (fun h => hok (hzeroOk.mp h))]
          exact hPost st m (RtC0State.PreservesMetaExceptEnd.refl st) rfl rfl hm
    · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl
  · have hlenPos : 0 < len := Nat.pos_of_ne_zero hzero
    have hlenBvNz : BitVec.ofNat 64 len ≠ 0#64 := fun h => by
      have ht := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
        show (0#64 : BitVec 64).toNat = 0 from rfl] at ht
      omega
    p1_steps
    · exfalso; exact hlenBvNz (by assumption)
    · p1_call pilotC0Env_ba_ptr
      dsimp only [ffiBaPtrSpec, vals, Tup.map, Arg.val]
      p1_steps
      p1_call pilotC0Env_get_end
      dsimp only [ffiGetEndSpec, vals, Tup.map, Arg.val]
      refine ⟨st, lcnfObjMem baObj ⋆ R, sep_ac hm, ?_⟩
      p1_steps
      p1_call pilotC0Env_carve_scratch
      dsimp only [ffiCarveScratchSpec, vals, Tup.map, Arg.val]
      refine ⟨st, lcnfObjMem baObj ⋆ R, sep_ac hm, ?_⟩
      by_cases hcarve : ffiCarveOk st (BitVec.ofNat 64 len)
      · rw [dite_eq_left hcarve]
        intro m1 hwptrNz hwptrMod hwcapGe hpresEnd hmidEnd hm1
        have hwprops := ffiCarveWptr_props hcarve
        let wptr := ffiCarveWptr st (BitVec.ofNat 64 len)
        let wend := ffiCarveWend st.hdr.s_end
        let wcap := ffiCarveWcap (BitVec.ofNat 64 len)
        let tailPad := st.hdr.s_end.toNat - wend.toNat
        let stCarved := st.withEnd wptr hwprops.2.2.2.2.1
        have hhi : (BitVec.ofNat 64 len).toNat ≤ 2 ^ 64 - 8 := hcarve.2.1
        have hwcapBv := ffiCarveWcap_bv_eq hhi
        have hwcapLt : wcap < 2 ^ 64 := hwprops.2.2.1
        have hlenLeWcap : len ≤ wcap := by
          have hc := hwcapGe
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)] at hc
        have hwcapLeEnd : wcap ≤ wend.toNat := Nat.le_trans hcarve.2.2.2 (Nat.sub_le _ _)
        have hwptrNat : wptr.toNat = wend.toNat - wcap := hwprops.2.2.2.1
        have hwfit : wptr.toNat + wcap < 2 ^ 64 := by
          have := wend.isLt; omega
        have hinFit : (baObj.addr + 24#64).toNat + len < 2 ^ 64 := by
          rw [BitVec.toNat_add, show (24#64 : BitVec 64).toNat = 24 from rfl,
            Nat.mod_eq_of_lt (by omega : baObj.addr.toNat + 24 < 2 ^ 64)]
          exact hfit
        have hKeyExt : (BitVec.setWidth 64 key).toNat = key.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans key.isLt (by decide))]
        p1_steps
        · exfalso; exact hwptrNz (by assumption)
        rw [show (7 : BitVec 64) = 7#64 from rfl,
          show (18446744073709551608 : BitVec 64) = 0xfffffffffffffff8#64 from rfl, hwcapBv]
        p1_call pilotC0Env_c0_xor_bytes
        dsimp only [c0XorBytesSpec, vals, Tup.map, Arg.val]
        have hnotBad : ¬ ((BitVec.ofNat 64 len).toNat > 0x00ffffffffffffff ∨
            (BitVec.ofNat 64 len).toNat > (BitVec.ofNat 64 wcap).toNat ∨
            (baObj.addr + 24#64).toNat + (BitVec.ofNat 64 len).toNat ≥ 2 ^ 64 ∨
            wptr.toNat + (BitVec.ofNat 64 wcap).toNat ≥ 2 ^ 64) := by
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
            Nat.mod_eq_of_lt hwcapLt]
          omega
        rw [ite_eq_right (by decide), ite_eq_right hnotBad]
        let xorFrame := rtC0Inv rt stCarved ⋆ region wend tailPad ⋆ R
        have hm1Obj : (lcnfObjMem baObj ⋆ (region wptr wcap ⋆ xorFrame)) m1 := by
          dsimp only [xorFrame, wptr, wend, wcap, tailPad, stCarved, len]
          exact sep_ac hm1
        have hm1Split : (bytes (baObj.addr + 24#64) baObj.scalarData ⋆
            region wptr (BitVec.ofNat 64 wcap).toNat ⋆
            (baObjShell baObj ⋆ xorFrame)) m1 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt]
          exact sep_ac (baObj_payload_split hcanon (R := region wptr wcap ⋆ xorFrame) hm1Obj)
        refine ⟨baObj.scalarData, baObjShell baObj ⋆ xorFrame,
          by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)], hm1Split, fun m2 hm2 => ?_⟩
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)] at hm2
        have hm2Obj : (lcnfObjMem baObj ⋆
            (bytes wptr outData ⋆ region (wptr + BitVec.ofNat 64 len) (wcap - len) ⋆
              xorFrame)) m2 := by
          have hm2' : (bytes (baObj.addr + 24#64) baObj.scalarData ⋆ (baObjShell baObj ⋆
              (bytes wptr outData ⋆ region (wptr + BitVec.ofNat 64 len) (wcap - len) ⋆
                xorFrame))) m2 := by
            dsimp only [wptr, len] at hm2 ⊢
            try rw [BitVec.add_comm (BitVec.ofNat 64 baObj.scalarData.length)
              (ffiCarveWptr st (BitVec.ofNat 64 baObj.scalarData.length))] at hm2
            simpa only [outData, hKeyExt] using sep_ac hm2
          exact baObj_payload_merge hcanon hm2'
        p1_straight
        dsimp only [len] at hlt56
        rw [bv64_len_shr56_eq_zero baObj.scalarData.length hlt56,
          show (72057594037927935 : BitVec 64) = 0x00ffffffffffffff#64 from rfl,
          bv64_len_and_mask56_eq baObj.scalarData.length hlt56]
        p1_steps
        · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl
        · p1_call pilotC0Env_ba_wrap_ok
          dsimp only [ffiBaWrapOkSpec, vals, Tup.map, Arg.val]
          let scratchRest := region (wptr + BitVec.ofNat 64 len) (wcap - len) ⋆
            region wend tailPad ⋆ lcnfObjMem baObj ⋆ R
          have hm2Wrap : (rtC0Inv rt stCarved ⋆ bytes wptr outData ⋆ scratchRest) m2 := by
            dsimp only [scratchRest]
            dsimp only [xorFrame] at hm2Obj
            exact sep_ac hm2Obj
          refine ⟨stCarved, outData, scratchRest,
            by rw [List.length_map, BitVec.toNat_ofNat,
                 Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)],
            hm2Wrap, ?_⟩
          have hwrapOkIff : ((BitVec.ofNat 64 len).toNat ≤ ffiBaMaxCap ∧
                baAllocBytes (BitVec.ofNat 64 len).toNat + 16 ≤ stCarved.rem) ↔
                pilotXorBaOk st len := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)]
            have hremC : stCarved.rem =
                (ffiCarveWend st.hdr.s_end).toNat -
                  ffiCarveWcap (BitVec.ofNat 64 len) - st.hdr.s_cur.toNat := by
              dsimp [stCarved, RtC0State.rem, RtC0State.withEnd]
              rw [hwprops.2.2.2.1]
            rw [hremC, pilotXorBaOk, ite_eq_right hzero]
            constructor
            · intro h; exact ⟨h.1, hcarve, h.2⟩
            · intro h; exact ⟨h.1, h.2.2⟩
          by_cases hok : pilotXorBaOk st len
          · rw [ite_eq_left (hwrapOkIff.mpr hok)]
            rw [ite_eq_left hok] at hPost
            intro p baNew stMid m3 hp0 hp8 hba0 hba8 hpresM hleM hremM hbC hokC hm3
            p1_steps
            let okTail := lcnfObjMem (mkFfiResOkObj p baNew) ⋆
              lcnfObjMem (mkBaObj baNew 1#32 (BitVec.ofNat 64 len).toNat outData) ⋆
              lcnfObjMem baObj ⋆ R
            have hm3Reg : (rtC0Inv rt stMid ⋆ region wptr wcap ⋆
                region wend tailPad ⋆ okTail) m3 := by
              have h3a : (bytes wptr outData ⋆
                  region (wptr + BitVec.ofNat 64 len) (wcap - len) ⋆
                  (rtC0Inv rt stMid ⋆ region wend tailPad ⋆ okTail)) m3 := by
                dsimp only [scratchRest, okTail] at hm3 ⊢
                exact sep_ac hm3
              have h3r := restore_xor_scratch_region
                (by rw [List.length_map]) hlenLeWcap (by omega) h3a
              exact sep_ac h3r
            p1_call pilotC0Env_restore_scratch
            dsimp only [ffiRestoreScratchSpec, vals, Tup.map, Arg.val]
            have hmidEndM : stMid.hdr.s_end = wptr := by
              rw [← hpresM.2.2.2.1]; exact hmidEnd
            have hm3Reg' : (rtC0Inv rt stMid ⋆ region wptr wcap ⋆
                region wend tailPad ⋆ okTail) m3 := hm3Reg
            refine ⟨stMid, wptr, wend, wcap, tailPad, okTail,
              hmidEndM, hwprops.2.2.2.2.2.2.2.2,
              ffiCarve_wptr_add_wcap hcarve, ffiCarve_wend_add_tail st,
              sep_cast hm3Reg' (by ac_rfl), fun stRestored m4 hpresR hendR hremR hm4 => ?_⟩
            p1_steps
            have hremC : stCarved.rem + wcap + tailPad = st.rem := ffiCarve_rem_reclaim hcarve
            have hlenEq : (BitVec.ofNat 64 len).toNat = len := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)]
            have hremLe : stRestored.rem ≤ st.rem := by omega
            have hremLo : st.rem - (baAllocBytes len + 16) ≤ stRestored.rem := by
              rw [hlenEq] at hremM; omega
            rw [hlenEq] at hbC
            have hm4Out : (rtC0Inv rt stRestored ⋆ lcnfObjMem (mkFfiResOkObj p baNew) ⋆
                lcnfObjMem (mkBaObj baNew 1#32 len outData) ⋆ lcnfObjMem baObj ⋆ R) m4 := by
              dsimp only [okTail] at hm4
              rw [hlenEq] at hm4
              exact sep_ac hm4
            exact hPost p baNew stRestored m4 hp0 hp8 hba0 hba8
              (hpresEnd.trans (hpresM.toExceptEnd.trans hpresR)) hendR hremLe hremLo
              hbC hokC hm4Out
          · rw [ite_eq_right (fun h => hok (hwrapOkIff.mp h))]
            rw [ite_eq_right hok] at hPost
            p1_steps
            have hm2Reg : (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                region wend tailPad ⋆ lcnfObjMem baObj ⋆ R) m2 := by
              have h2a : (bytes wptr outData ⋆
                  region (wptr + BitVec.ofNat 64 len) (wcap - len) ⋆
                  (rtC0Inv rt stCarved ⋆ region wend tailPad ⋆
                    lcnfObjMem baObj ⋆ R)) m2 := by
                dsimp only [scratchRest] at hm2Wrap
                exact sep_ac hm2Wrap
              exact sep_ac (restore_xor_scratch_region (wcap := wcap) (len := len)
                (by rw [List.length_map]) hlenLeWcap (by omega) h2a)
            p1_call pilotC0Env_restore_scratch
            dsimp only [ffiRestoreScratchSpec, vals, Tup.map, Arg.val]
            have hm2Reg' : (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                region wend tailPad ⋆ lcnfObjMem baObj ⋆ R) m2 := hm2Reg
            refine ⟨stCarved, wptr, wend, wcap, tailPad,
              lcnfObjMem baObj ⋆ R, hmidEnd, hwprops.2.2.2.2.2.2.2.2,
              ffiCarve_wptr_add_wcap hcarve, ffiCarve_wend_add_tail st,
              sep_cast hm2Reg' (by ac_rfl), fun stRestored m3 hpresR hendR hremR hm3 => ?_⟩
            p1_steps
            have hremC : stCarved.rem + wcap + tailPad = st.rem := ffiCarve_rem_reclaim hcarve
            have hremEq : stRestored.rem = st.rem := by omega
            exact hPost stRestored m3 (hpresEnd.trans hpresR) hendR hremEq (sep_ac hm3)
      · rw [dite_eq_right hcarve]
        have hnotOk : ¬ pilotXorBaOk st len := fun h => by
          rw [pilotXorBaOk, ite_eq_right hzero] at h
          exact hcarve h.2.1
        rw [ite_eq_right hnotOk] at hPost
        p1_steps
        · exact hPost st m (RtC0State.PreservesMetaExceptEnd.refl st) rfl rfl hm
        · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl

theorem lcnf_c0_xor_nat_wp :
    ∀ xs m Q X, pilotXorNatSpec xs m Q X →
      Func.wp pilotC0Env lcnf_c0_xor_nat.body xs m Q X := by
  intro ⟨rt, a, key, ⟨⟩⟩ m Q X
    ⟨st, scr, scrLimbs, val, objs, R, hscrLt, hrep, hm, hPost⟩
  dsimp only [Func.wp, lcnf_c0_xor_nat, lcnf_c0_xor_nat_body]
  p1_steps
  p1_call pilotC0Env_nat_bytes_len
  dsimp only [ffiNatBytesLenSpec, vals, Tup.map, Arg.val]
  refine ⟨val, objs, rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrLimbs ⋆ R,
    hrep, sep_ac hm, ?_⟩
  cases hbs : bytesOfNatS val with
  | none =>
    rw [hbs] at hPost
    dsimp only at hPost ⊢
    p1_steps <;> first
      | exact hPost
      | (exfalso; exact ‹ffiInvalidLen ≠ 18446744073709551615#64› rfl)
  | some bs =>
    rw [hbs] at hPost
    dsimp only at hPost ⊢
    have hbsMax := bytesOfNatS_len_le hrep hbs
    have hlt56 : bs.length ≤ 0x00ffffffffffffff := by unfold ffiNatMaxBytes at hbsMax; omega
    have hbsNeInv : BitVec.ofNat 64 bs.length ≠ 18446744073709551615#64 := fun h => by
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold ffiNatMaxBytes at hbsMax; omega),
        show (18446744073709551615#64 : BitVec 64).toNat = 2 ^ 64 - 1 from by decide] at hn
      unfold ffiNatMaxBytes at hbsMax; omega
    let outBs := bs.map (· ^^^ UInt8.ofNat key.toNat)
    by_cases hzero : bs.length = 0
    · have hbsNil : bs = [] := List.eq_nil_of_length_eq_zero hzero
      have hlenBv0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hzero]
      have hnoScrF : ¬ ((a &&& 1#64) ≠ 0#64 ∧ 0 < bs.length ∧
          (scr = 0#64 ∨ scrLimbs.length = 0)) := fun h => by omega
      rw [ite_eq_right hnoScrF] at hPost
      rcases hPost with ⟨_, _, hPost0⟩
      rw [hlenBv0]
      p1_steps
      · exact absurd (by assumption : (0#64 : BitVec 64) = 18446744073709551615#64) (by decide)
      · p1_call pilotC0Env_nat_wrap_ok
        dsimp only [ffiNatWrapOkSpec, vals, Tup.map, Arg.val]
        refine ⟨st, [], cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R, rfl, ?_, ?_⟩
        · rw [bytes_nil_eq, Std.ExtHashMap.sep_emp]
          exact sep_ac hm
        · rw [show (0 : BitVec 64).toNat = 0 from rfl]
          simp only [bytes_nil_eq, Std.ExtHashMap.sep_emp]
          have hokIff : 16 ≤ st.rem ↔ pilotXorNatOk st 0 := by
            simp [pilotXorNatOk, natSAllocBytes]
          rw [hzero] at hPost0
          rw [ite_eq_left (by decide : 0 ≤ 7)] at hPost0 ⊢
          by_cases hok : pilotXorNatOk st 0
          · rw [ite_eq_left (hokIff.mpr hok)]
            rw [ite_eq_left hok] at hPost0
            intro p st' m1 hp0 hp8 hpres hle hrem hokC hm1
            have hm1' : (rtC0Inv rt st' ⋆
                lcnfObjMem (mkFfiResOkObj p (boxNat (natOfBytesS outBs))) ⋆
                cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m1 := by
              simpa [outBs, hbsNil, bytes] using sep_ac hm1
            have hokC' : FfiResOkCanon (mkFfiResOkObj p (boxNat (natOfBytesS outBs)))
                (boxNat (natOfBytesS outBs)) := by
              simpa [outBs, hbsNil] using hokC
            exact hPost0 p st' scrLimbs m1 hp0 hp8 rfl hpres.toExceptEnd hpres.2.2.2.1.symm
              hle hrem hokC' hm1'
          · rw [ite_eq_right (fun h => hok (hokIff.mp h))]
            rw [ite_eq_right hok] at hPost0
            exact hPost0 st scrLimbs m rfl (RtC0State.PreservesMetaExceptEnd.refl st) rfl
              rfl hm
      · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl
    · have hlenPos : 0 < bs.length := Nat.pos_of_ne_zero hzero
      have hlenBvNz : BitVec.ofNat 64 bs.length ≠ 0#64 := fun h => by
        have ht := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64),
          show (0#64 : BitVec 64).toNat = 0 from rfl] at ht
        omega
      p1_steps
      · exfalso; exact hbsNeInv (by assumption)
      · exfalso; exact hlenBvNz (by assumption)
      · p1_call pilotC0Env_nat_bytes_ptr
        dsimp only [ffiNatBytesPtrSpec, vals, Tup.map, Arg.val]
        by_cases hodd : (a &&& 1#64) ≠ 0#64
        · rw [ite_eq_left hodd]
          refine ⟨scr, scrLimbs, rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R, hscrLt, sep_ac hm, ?_⟩
          by_cases hnoScr : scr = 0#64 ∨ scrLimbs.length = 0
          · rw [ite_eq_left hnoScr]
            rw [ite_eq_left ⟨hodd, hlenPos, hnoScr⟩] at hPost
            p1_steps
            · exact hPost
            · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl
          · rw [ite_eq_right hnoScr]
            rw [ite_eq_right (fun ⟨_, _, h⟩ => hnoScr h)] at hPost
            rcases hPost with ⟨hscrFit, _, hXorPost⟩
            have hscrNe : scr ≠ 0#64 := fun h => hnoScr (Or.inl h)
            have hscrPos : 0 < scrLimbs.length :=
              Nat.pos_of_ne_zero fun h => hnoScr (Or.inr h)
            have hnatEq : natOfBytesS bs = val := natOfBytesS_of_bytesOfNatS hbs
            have hvalSmall : val < 2 ^ 63 := Nat.lt_of_not_le fun hbig => by
              rw [RtNatRep, ite_eq_right (Nat.not_lt_of_ge hbig)] at hrep
              exact hodd hrep.1
            have hle7 : bs.length ≤ 7 := (natOfBytesS_lt_2p63_iff bs).mp (by rwa [hnatEq])
            have haEq : a = BitVec.ofNat 64 (2 * val + 1) := by
              simpa [RtNatRep, hvalSmall] using hrep
            have hash : (a >>> 1) = BitVec.ofNat 64 (natOfBytesS bs) := by
              rw [haEq, hnatEq]
              apply BitVec.eq_of_toNat_eq
              have hlt : 2 * val + 1 < 2 ^ 64 := by
                have := natOfBytesS_lt_2p63 hle7; omega
              have hv : val < 2 ^ 64 := by
                have := natOfBytesS_lt_2p63 hle7; omega
              rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow, Nat.pow_one,
                Nat.mod_eq_of_lt hv]
              omega
            intro m1 hm1
            let scrLimbs' := scrLimbs.set 0 (a >>> 1)
            have hlenSet : scrLimbs'.length = scrLimbs.length := List.length_set
            have hsplitCons : scrLimbs' = (a >>> 1) :: scrLimbs'.tail := by
              cases hL : scrLimbs with
              | nil => simp [hL] at hscrPos
              | cons hd tl => simp [scrLimbs', hL]
            p1_steps
            · exfalso; exact hscrNe (by assumption)
            · p1_call pilotC0Env_get_end
              dsimp only [ffiGetEndSpec, vals, Tup.map, Arg.val]
              refine ⟨st, cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R, sep_ac hm1, ?_⟩
              p1_steps
              p1_call pilotC0Env_carve_scratch
              dsimp only [ffiCarveScratchSpec, vals, Tup.map, Arg.val]
              refine ⟨st, cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R, sep_ac hm1, ?_⟩
              by_cases hcarve : ffiCarveOk st (BitVec.ofNat 64 bs.length)
              · rw [dite_eq_left hcarve]
                intro m2 hwptrNz hwptrMod hwcapGe hpresEnd hmidEnd hm2
                have hwprops := ffiCarveWptr_props hcarve
                let wptr := ffiCarveWptr st (BitVec.ofNat 64 bs.length)
                let wend := ffiCarveWend st.hdr.s_end
                let wcap := ffiCarveWcap (BitVec.ofNat 64 bs.length)
                let tailPad := st.hdr.s_end.toNat - wend.toNat
                let stCarved := st.withEnd wptr hwprops.2.2.2.2.1
                have hhi : (BitVec.ofNat 64 bs.length).toNat ≤ 2 ^ 64 - 8 := hcarve.2.1
                have hwcapBv := ffiCarveWcap_bv_eq hhi
                have hwcapLt : wcap < 2 ^ 64 := hwprops.2.2.1
                have hlenLeWcap : bs.length ≤ wcap := by
                  have hc := hwcapGe
                  rwa [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)] at hc
                have hwcapLeEnd : wcap ≤ wend.toNat :=
                  Nat.le_trans hcarve.2.2.2 (Nat.sub_le _ _)
                have hwptrNat : wptr.toNat = wend.toNat - wcap := hwprops.2.2.2.1
                have hwfit : wptr.toNat + wcap < 2 ^ 64 := by
                  have := wend.isLt; omega
                have hscrBfit : scr.toNat + bs.length < 2 ^ 64 := by
                  have := hscrFit hodd; omega
                have hKeyExt : (BitVec.setWidth 64 key).toNat = key.toNat := by
                  rw [BitVec.toNat_setWidth,
                    Nat.mod_eq_of_lt (Nat.lt_trans key.isLt (by decide))]
                p1_steps
                · exfalso; exact hwptrNz (by assumption)
                rw [show (7 : BitVec 64) = 7#64 from rfl,
                  show (18446744073709551608 : BitVec 64) =
                    0xfffffffffffffff8#64 from rfl, hwcapBv]
                p1_call pilotC0Env_c0_xor_bytes
                dsimp only [c0XorBytesSpec, vals, Tup.map, Arg.val]
                have hnotBad : ¬ ((BitVec.ofNat 64 bs.length).toNat >
                      0x00ffffffffffffff ∨
                    (BitVec.ofNat 64 bs.length).toNat >
                      (BitVec.ofNat 64 wcap).toNat ∨
                    scr.toNat + (BitVec.ofNat 64 bs.length).toNat ≥ 2 ^ 64 ∨
                    wptr.toNat + (BitVec.ofNat 64 wcap).toNat ≥ 2 ^ 64) := by
                  simp only [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64),
                    Nat.mod_eq_of_lt hwcapLt]
                  omega
                rw [ite_eq_right (by decide), ite_eq_right hnotBad]
                let scrMeta := cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length)
                let tailConst := scrMeta ⋆ lcnfHeap objs ⋆ R
                let xorTail := rtC0Inv rt stCarved ⋆ region wend tailPad ⋆
                  taggedScrTail scr bs scrLimbs'.tail ⋆ tailConst
                have hm2Arr : (array64 scr
                    (BitVec.ofNat 64 (natOfBytesS bs) :: scrLimbs'.tail) ⋆
                    (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆ tailConst)) m2 := by
                  rw [← hash, ← hsplitCons]
                  dsimp only [tailConst, scrMeta, wptr, wend, wcap, tailPad, stCarved]
                  exact sep_ac hm2
                have hm2Split : (bytes scr bs ⋆
                    region wptr (BitVec.ofNat 64 wcap).toNat ⋆ xorTail) m2 := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt]
                  dsimp only [xorTail]
                  exact sep_ac (tagged_array64_split hle7 hm2Arr)
                refine ⟨bs, xorTail, by rw [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)],
                  hm2Split, fun m3 hm3 => ?_⟩
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt,
                  BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)] at hm3
                have hm3' : (bytes scr bs ⋆ bytes wptr outBs ⋆
                    region (wptr + BitVec.ofNat 64 bs.length) (wcap - bs.length) ⋆
                    xorTail) m3 := by
                  dsimp only [wptr] at hm3 ⊢
                  try rw [BitVec.add_comm (BitVec.ofNat 64 bs.length)
                    (ffiCarveWptr st (BitVec.ofNat 64 bs.length))] at hm3
                  simpa only [outBs, hKeyExt] using sep_ac hm3
                p1_straight
                rw [bv64_len_shr56_eq_zero bs.length hlt56,
                  show (72057594037927935 : BitVec 64) =
                    0x00ffffffffffffff#64 from rfl,
                  bv64_len_and_mask56_eq bs.length hlt56]
                p1_steps
                · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl
                p1_call pilotC0Env_nat_wrap_ok
                dsimp only [ffiNatWrapOkSpec, vals, Tup.map, Arg.val]
                let scratchRest := region (wptr + BitVec.ofNat 64 bs.length)
                    (wcap - bs.length) ⋆ region wend tailPad ⋆ bytes scr bs ⋆
                  taggedScrTail scr bs scrLimbs'.tail ⋆ tailConst
                have hm3Wrap : (rtC0Inv rt stCarved ⋆ bytes wptr outBs ⋆
                    scratchRest) m3 := by
                  dsimp only [scratchRest, xorTail] at hm3' ⊢
                  exact sep_ac hm3'
                refine ⟨stCarved, outBs, scratchRest,
                  by rw [List.length_map, BitVec.toNat_ofNat,
                       Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)],
                  hm3Wrap, ?_⟩
                have hle7Bv : (BitVec.ofNat 64 bs.length).toNat ≤ 7 := by
                  rw [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)]
                  exact hle7
                rw [ite_eq_left hle7Bv]
                have hokIff : 16 ≤ stCarved.rem ↔
                    pilotXorNatOk st bs.length := by
                  have hremC : stCarved.rem =
                      (ffiCarveWend st.hdr.s_end).toNat -
                        ffiCarveWcap (BitVec.ofNat 64 bs.length) -
                        st.hdr.s_cur.toNat := by
                    dsimp [stCarved, RtC0State.rem, RtC0State.withEnd]
                    rw [hwprops.2.2.2.1]
                  rw [hremC, pilotXorNatOk, ite_eq_right hzero]
                  have hns : natSAllocBytes bs.length = 0 := by
                    simp [natSAllocBytes, hle7]
                  rw [hns]
                  constructor
                  · intro h; exact ⟨hbsMax, hcarve, by omega⟩
                  · intro h; exact Nat.le_trans (Nat.le_of_eq (by omega)) h.2.2
                rw [ite_eq_left hle7] at hXorPost
                by_cases hok : pilotXorNatOk st bs.length
                · rw [ite_eq_left (hokIff.mpr hok)]
                  rw [ite_eq_left hok] at hXorPost
                  intro p stMid m4 hp0 hp8 hpresM hleM hremM hokC hm4
                  p1_steps
                  let okObj := lcnfObjMem
                    (mkFfiResOkObj p (boxNat (natOfBytesS outBs)))
                  have hm4Scr : (rtC0Inv rt stMid ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆ okObj ⋆
                      cell64 (rt + 33672#64) scr ⋆
                      cell64 (rt + 33680#64)
                        (BitVec.ofNat 64 scrLimbs'.length) ⋆
                      array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m4 := by
                    have h4a : (bytes wptr outBs ⋆
                        region (wptr + BitVec.ofNat 64 bs.length)
                          (wcap - bs.length) ⋆
                        (rtC0Inv rt stMid ⋆ region wend tailPad ⋆ okObj ⋆
                          bytes scr bs ⋆ taggedScrTail scr bs scrLimbs'.tail ⋆
                          tailConst)) m4 := by
                      dsimp only [scratchRest, okObj] at hm4 ⊢
                      exact sep_ac hm4
                    have h4r := restore_xor_scratch_region
                      (by rw [List.length_map]) hlenLeWcap (by omega) h4a
                    have h4b : (bytes scr bs ⋆
                        (taggedScrTail scr bs scrLimbs'.tail ⋆
                          (rtC0Inv rt stMid ⋆ region wptr wcap ⋆
                            region wend tailPad ⋆ okObj ⋆ tailConst))) m4 :=
                      sep_ac h4r
                    have h4m := tagged_array64_merge hle7 h4b
                    rw [← hash, ← hsplitCons] at h4m
                    dsimp only [tailConst, scrMeta] at h4m
                    rw [← hlenSet] at h4m
                    exact sep_ac h4m
                  p1_call pilotC0Env_restore_scratch
                  dsimp only [ffiRestoreScratchSpec, vals, Tup.map, Arg.val]
                  have hmidEndM : stMid.hdr.s_end = wptr := by
                    rw [← hpresM.2.2.2.1]; exact hmidEnd
                  have hm4Scr' : (rtC0Inv rt stMid ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆
                      (okObj ⋆ cell64 (rt + 33672#64) scr ⋆
                        cell64 (rt + 33680#64)
                          (BitVec.ofNat 64 scrLimbs'.length) ⋆
                        array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R)) m4 :=
                    sep_ac hm4Scr
                  refine ⟨stMid, wptr, wend, wcap, tailPad, _, hmidEndM,
                    hwprops.2.2.2.2.2.2.2.2,
                    ffiCarve_wptr_add_wcap hcarve, ffiCarve_wend_add_tail st,
                    hm4Scr', fun stRestored m5 hpresR hendR hremR hm5 => ?_⟩
                  p1_steps
                  have hremC : stCarved.rem + wcap + tailPad = st.rem := ffiCarve_rem_reclaim hcarve
                  have hremLe : stRestored.rem ≤ st.rem := by omega
                  have hremLo : st.rem - 16 ≤ stRestored.rem := by omega
                  have hm5' : (rtC0Inv rt stRestored ⋆
                      lcnfObjMem (mkFfiResOkObj p (boxNat (natOfBytesS outBs))) ⋆
                      cell64 (rt + 33672#64) scr ⋆
                      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
                      array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m5 := by
                    dsimp only [okObj, outBs] at hm5 ⊢
                    exact sep_ac hm5
                  exact hXorPost p stRestored scrLimbs' m5 hp0 hp8 hlenSet
                    (hpresEnd.trans (hpresM.toExceptEnd.trans hpresR)) hendR
                    hremLe hremLo hokC hm5'
                · rw [ite_eq_right (fun h => hok (hokIff.mp h))]
                  rw [ite_eq_right hok] at hXorPost
                  p1_steps
                  have hm3Scr : (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆
                      cell64 (rt + 33672#64) scr ⋆
                      cell64 (rt + 33680#64)
                        (BitVec.ofNat 64 scrLimbs'.length) ⋆
                      array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m3 := by
                    have h3a : (bytes wptr outBs ⋆
                        region (wptr + BitVec.ofNat 64 bs.length)
                          (wcap - bs.length) ⋆
                        (rtC0Inv rt stCarved ⋆ region wend tailPad ⋆
                          bytes scr bs ⋆ taggedScrTail scr bs scrLimbs'.tail ⋆
                          tailConst)) m3 := by
                      dsimp only [scratchRest] at hm3Wrap
                      exact sep_ac hm3Wrap
                    have h3r := restore_xor_scratch_region
                      (by rw [List.length_map]) hlenLeWcap (by omega) h3a
                    have h3b : (bytes scr bs ⋆
                        (taggedScrTail scr bs scrLimbs'.tail ⋆
                          (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                            region wend tailPad ⋆ tailConst))) m3 :=
                      sep_ac h3r
                    have h3m := tagged_array64_merge hle7 h3b
                    rw [← hash, ← hsplitCons] at h3m
                    dsimp only [tailConst, scrMeta] at h3m
                    rw [← hlenSet] at h3m
                    exact sep_ac h3m
                  p1_call pilotC0Env_restore_scratch
                  dsimp only [ffiRestoreScratchSpec, vals, Tup.map, Arg.val]
                  have hm3Scr' : (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆
                      (cell64 (rt + 33672#64) scr ⋆
                        cell64 (rt + 33680#64)
                          (BitVec.ofNat 64 scrLimbs'.length) ⋆
                        array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R)) m3 :=
                    sep_ac hm3Scr
                  refine ⟨stCarved, wptr, wend, wcap, tailPad, _, hmidEnd,
                    hwprops.2.2.2.2.2.2.2.2,
                    ffiCarve_wptr_add_wcap hcarve, ffiCarve_wend_add_tail st,
                    hm3Scr', fun stRestored m4 hpresR hendR hremR hm4 => ?_⟩
                  p1_steps
                  have hremC : stCarved.rem + wcap + tailPad = st.rem := ffiCarve_rem_reclaim hcarve
                  have hremEq : stRestored.rem = st.rem := by omega
                  exact hXorPost stRestored scrLimbs' m4 hlenSet
                    (hpresEnd.trans hpresR) hendR hremEq (sep_ac hm4)
              · rw [dite_eq_right hcarve]
                have hnotOk : ¬ pilotXorNatOk st bs.length := fun h => by
                  rw [pilotXorNatOk, ite_eq_right hzero] at h
                  exact hcarve h.2.1
                rw [ite_eq_right hnotOk] at hXorPost
                p1_steps
                · exact hXorPost st scrLimbs' m1 hlenSet
                    (RtC0State.PreservesMetaExceptEnd.refl st) rfl rfl (by
                      dsimp only [scrLimbs']
                      rw [hlenSet]
                      exact sep_ac hm1)
                · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl
        · have heven : (a &&& 1#64) = 0#64 := Classical.not_not.mp hodd
          rw [ite_eq_right hodd]
          rw [ite_eq_right (fun ⟨h, _⟩ => hodd h)] at hPost
          rcases hPost with ⟨_, hmpzFit, hXorPost⟩
          have hbig : ¬ val < 2 ^ 63 := fun hlt => by
            have ha : a = BitVec.ofNat 64 (2 * val + 1) := by
              simpa [RtNatRep, hlt] using hrep
            have hand : (a &&& 1#64) = 1#64 := by
              rw [ha]
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_and, BitVec.toNat_ofNat,
                show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : 2 * val + 1 < 2 ^ 64),
                Nat.and_one_is_mod]
              omega
            rw [hand] at heven; exact absurd heven (by decide)
          have hrepBig := hrep
          rw [RtNatRep, ite_eq_right hbig] at hrepBig
          rcases hrepBig with ⟨_, obj, hobjMem, hobjAddr, hcanon⟩
          have hnatEq : natOfBytesS bs = val := natOfBytesS_of_bytesOfNatS hbs
          have hcanonBs : RtMpzNatCanon obj (natOfBytesS bs) := by rwa [hnatEq]
          have ha16Nz : a + 16#64 ≠ 0#64 := fun h => by
            have hf := hmpzFit heven
            have h16 := congrArg BitVec.toNat h
            rw [BitVec.toNat_add, show (16#64 : BitVec 64).toNat = 16 from rfl,
              Nat.mod_eq_of_lt (by omega : a.toNat + 16 < 2 ^ 64),
              show (0#64 : BitVec 64).toNat = 0 from rfl] at h16
            omega
          have ha16Fit : (a + 16#64).toNat + bs.length < 2 ^ 64 := by
            have hf := hmpzFit heven
            rw [BitVec.toNat_add, show (16#64 : BitVec 64).toNat = 16 from rfl,
              Nat.mod_eq_of_lt (by omega : a.toNat + 16 < 2 ^ 64)]
            exact hf
          obtain ⟨idx, hidx, hobjEq⟩ := List.mem_iff_getElem.mp hobjMem
          p1_steps
          · exfalso; exact ha16Nz (by assumption)
          · p1_call pilotC0Env_get_end
            dsimp only [ffiGetEndSpec, vals, Tup.map, Arg.val]
            refine ⟨st, cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R, sep_ac hm, ?_⟩
            p1_steps
            p1_call pilotC0Env_carve_scratch
            dsimp only [ffiCarveScratchSpec, vals, Tup.map, Arg.val]
            refine ⟨st, cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R, sep_ac hm, ?_⟩
            by_cases hcarve : ffiCarveOk st (BitVec.ofNat 64 bs.length)
            · rw [dite_eq_left hcarve]
              intro m1 hwptrNz hwptrMod hwcapGe hpresEnd hmidEnd hm1
              have hwprops := ffiCarveWptr_props hcarve
              let wptr := ffiCarveWptr st (BitVec.ofNat 64 bs.length)
              let wend := ffiCarveWend st.hdr.s_end
              let wcap := ffiCarveWcap (BitVec.ofNat 64 bs.length)
              let tailPad := st.hdr.s_end.toNat - wend.toNat
              let stCarved := st.withEnd wptr hwprops.2.2.2.2.1
              have hhi : (BitVec.ofNat 64 bs.length).toNat ≤ 2 ^ 64 - 8 := hcarve.2.1
              have hwcapBv := ffiCarveWcap_bv_eq hhi
              have hwcapLt : wcap < 2 ^ 64 := hwprops.2.2.1
              have hlenLeWcap : bs.length ≤ wcap := by
                have hc := hwcapGe
                rwa [BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)] at hc
              have hwcapLeEnd : wcap ≤ wend.toNat :=
                Nat.le_trans hcarve.2.2.2 (Nat.sub_le _ _)
              have hwptrNat : wptr.toNat = wend.toNat - wcap := hwprops.2.2.2.1
              have hwfit : wptr.toNat + wcap < 2 ^ 64 := by
                have := wend.isLt; omega
              have hKeyExt : (BitVec.setWidth 64 key).toNat = key.toNat := by
                rw [BitVec.toNat_setWidth,
                  Nat.mod_eq_of_lt (Nat.lt_trans key.isLt (by decide))]
              p1_steps
              · exfalso; exact hwptrNz (by assumption)
              · rw [show (7 : BitVec 64) = 7#64 from rfl,
                  show (18446744073709551608 : BitVec 64) =
                    0xfffffffffffffff8#64 from rfl, hwcapBv]
                p1_call pilotC0Env_c0_xor_bytes
                dsimp only [c0XorBytesSpec, vals, Tup.map, Arg.val]
                have hnotBad : ¬ ((BitVec.ofNat 64 bs.length).toNat >
                      0x00ffffffffffffff ∨
                    (BitVec.ofNat 64 bs.length).toNat >
                      (BitVec.ofNat 64 wcap).toNat ∨
                    (a + 16#64).toNat + (BitVec.ofNat 64 bs.length).toNat ≥ 2 ^ 64 ∨
                    wptr.toNat + (BitVec.ofNat 64 wcap).toNat ≥ 2 ^ 64) := by
                  simp only [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64),
                    Nat.mod_eq_of_lt hwcapLt]
                  omega
                rw [ite_eq_right (by decide), ite_eq_right hnotBad]
                let scrFull := cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  array64 scr scrLimbs
                let mpzRest := rtC0Inv rt stCarved ⋆ region wend tailPad ⋆
                  scrFull ⋆ R
                have hm1Heap : (lcnfHeap objs ⋆ (region wptr wcap ⋆ mpzRest)) m1 := by
                  dsimp only [mpzRest, scrFull, wptr, wend, wcap, tailPad, stCarved]
                  exact sep_ac hm1
                have hm1Split : (bytes (a + 16#64) bs ⋆
                    region wptr (BitVec.ofNat 64 wcap).toNat ⋆
                    (mpzHeapShell objs idx a obj bs ⋆ mpzRest)) m1 := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt]
                  exact sep_ac (mpz_heap_split hidx hobjEq hobjAddr hcanonBs hm1Heap)
                refine ⟨bs, mpzHeapShell objs idx a obj bs ⋆ mpzRest,
                  by rw [BitVec.toNat_ofNat,
                       Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)],
                  hm1Split, fun m2 hm2 => ?_⟩
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt,
                  BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)] at hm2
                have hm2Heap : (lcnfHeap objs ⋆
                    (bytes wptr outBs ⋆
                      region (wptr + BitVec.ofNat 64 bs.length) (wcap - bs.length) ⋆
                      mpzRest)) m2 := by
                  have hm2a : (bytes (a + 16#64) bs ⋆ (mpzHeapShell objs idx a obj bs ⋆
                      (bytes wptr outBs ⋆
                        region (wptr + BitVec.ofNat 64 bs.length) (wcap - bs.length) ⋆
                        mpzRest))) m2 := by
                    dsimp only [wptr] at hm2 ⊢
                    try rw [BitVec.add_comm (BitVec.ofNat 64 bs.length)
                      (ffiCarveWptr st (BitVec.ofNat 64 bs.length))] at hm2
                    simpa only [outBs, hKeyExt] using sep_ac hm2
                  exact mpz_heap_merge hidx hobjEq hobjAddr hcanonBs hm2a
                p1_straight
                rw [bv64_len_shr56_eq_zero bs.length hlt56,
                  show (72057594037927935 : BitVec 64) =
                    0x00ffffffffffffff#64 from rfl,
                  bv64_len_and_mask56_eq bs.length hlt56]
                p1_steps
                · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl
                p1_call pilotC0Env_nat_wrap_ok
                dsimp only [ffiNatWrapOkSpec, vals, Tup.map, Arg.val]
                let scratchRest := region (wptr + BitVec.ofNat 64 bs.length)
                    (wcap - bs.length) ⋆ region wend tailPad ⋆
                  scrFull ⋆ lcnfHeap objs ⋆ R
                have hm2Wrap : (rtC0Inv rt stCarved ⋆ bytes wptr outBs ⋆
                    scratchRest) m2 := by
                  dsimp only [scratchRest, mpzRest] at hm2Heap ⊢
                  exact sep_ac hm2Heap
                refine ⟨stCarved, outBs, scratchRest,
                  by rw [List.length_map, BitVec.toNat_ofNat,
                       Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)],
                  hm2Wrap, ?_⟩
                have hnotLe7Bv : ¬ (BitVec.ofNat 64 bs.length).toNat ≤ 7 := by
                  rw [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)]
                  have := (mpzNatCanon_natOfBytesS_bytesN8 hcanonBs).1; omega
                have hnotLe7 : ¬ bs.length ≤ 7 := by
                  have := (mpzNatCanon_natOfBytesS_bytesN8 hcanonBs).1; omega
                rw [ite_eq_right hnotLe7Bv]
                have hokIff : ((BitVec.ofNat 64 bs.length).toNat ≤
                      ffiNatMaxBytes ∧
                      natSAllocBytes (BitVec.ofNat 64 bs.length).toNat + 16 ≤
                        stCarved.rem) ↔ pilotXorNatOk st bs.length := by
                  have hlenEq : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
                    rw [BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)]
                  have hremC : stCarved.rem =
                      (ffiCarveWend st.hdr.s_end).toNat -
                        ffiCarveWcap (BitVec.ofNat 64 bs.length) -
                        st.hdr.s_cur.toNat := by
                    dsimp [stCarved, RtC0State.rem, RtC0State.withEnd]
                    rw [hwprops.2.2.2.1]
                  rw [hlenEq, hremC, pilotXorNatOk, ite_eq_right hzero]
                  constructor
                  · intro h; exact ⟨h.1, hcarve, h.2⟩
                  · intro h; exact ⟨h.1, h.2.2⟩
                rw [ite_eq_right hnotLe7] at hXorPost
                by_cases hok : pilotXorNatOk st bs.length
                · rw [ite_eq_left (hokIff.mpr hok)]
                  rw [ite_eq_left hok] at hXorPost
                  intro p natP stMid newObj m3 hp0 hp8 hn0 hn8 hnEven hpresM
                    hleM hremM hnAddr hcanonOut hmpzOut hokC hm3
                  p1_steps
                  let okTail := lcnfObjMem (mkFfiResOkObj p natP) ⋆
                    lcnfObjMem newObj ⋆ scrFull ⋆ lcnfHeap objs ⋆ R
                  have hm3Reg : (rtC0Inv rt stMid ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆ okTail) m3 := by
                    have h3a : (bytes wptr outBs ⋆
                        region (wptr + BitVec.ofNat 64 bs.length)
                          (wcap - bs.length) ⋆
                        (rtC0Inv rt stMid ⋆ region wend tailPad ⋆ okTail)) m3 := by
                      dsimp only [scratchRest, okTail] at hm3 ⊢
                      exact sep_ac hm3
                    exact sep_ac (restore_xor_scratch_region
                      (by rw [List.length_map]) hlenLeWcap (by omega) h3a)
                  p1_call pilotC0Env_restore_scratch
                  dsimp only [ffiRestoreScratchSpec, vals, Tup.map, Arg.val]
                  have hmidEndM : stMid.hdr.s_end = wptr := by
                    rw [← hpresM.2.2.2.1]; exact hmidEnd
                  have hm3Reg' : (rtC0Inv rt stMid ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆ okTail) m3 := hm3Reg
                  refine ⟨stMid, wptr, wend, wcap, tailPad, okTail, hmidEndM,
                    hwprops.2.2.2.2.2.2.2.2,
                    ffiCarve_wptr_add_wcap hcarve, ffiCarve_wend_add_tail st,
                    sep_cast hm3Reg' (by ac_rfl), fun stRestored m4 hpresR hendR hremR hm4 => ?_⟩
                  p1_steps
                  have hremC : stCarved.rem + wcap + tailPad = st.rem := ffiCarve_rem_reclaim hcarve
                  have hlenEq : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
                    rw [BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)]
                  have hremLe : stRestored.rem ≤ st.rem := by omega
                  have hremLo : st.rem - (natSAllocBytes bs.length + 16) ≤
                      stRestored.rem := by
                    rw [hlenEq] at hremM; omega
                  have hm4Out : (rtC0Inv rt stRestored ⋆
                      lcnfObjMem (mkFfiResOkObj p natP) ⋆
                      lcnfObjMem newObj ⋆ cell64 (rt + 33672#64) scr ⋆
                      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m4 := by
                    dsimp only [okTail, scrFull] at hm4
                    exact sep_ac hm4
                  exact hXorPost p natP stRestored newObj scrLimbs m4 hp0 hp8 hn0
                    hn8 hnEven rfl
                    (hpresEnd.trans (hpresM.toExceptEnd.trans hpresR)) hendR hremLe
                    hremLo hcanonOut hnAddr hmpzOut hokC hm4Out
                · rw [ite_eq_right (fun h => hok (hokIff.mp h))]
                  rw [ite_eq_right hok] at hXorPost
                  p1_steps
                  let failTail := scrFull ⋆ lcnfHeap objs ⋆ R
                  have hm2Reg : (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆ failTail) m2 := by
                    have h2a : (bytes wptr outBs ⋆
                        region (wptr + BitVec.ofNat 64 bs.length)
                          (wcap - bs.length) ⋆
                        (rtC0Inv rt stCarved ⋆ region wend tailPad ⋆
                          failTail)) m2 := by
                      dsimp only [scratchRest, failTail] at hm2Wrap ⊢
                      exact sep_ac hm2Wrap
                    exact sep_ac (restore_xor_scratch_region
                      (by rw [List.length_map]) hlenLeWcap (by omega) h2a)
                  p1_call pilotC0Env_restore_scratch
                  dsimp only [ffiRestoreScratchSpec, vals, Tup.map, Arg.val]
                  have hm2Reg' : (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                      region wend tailPad ⋆ failTail) m2 := hm2Reg
                  refine ⟨stCarved, wptr, wend, wcap, tailPad, failTail, hmidEnd,
                    hwprops.2.2.2.2.2.2.2.2,
                    ffiCarve_wptr_add_wcap hcarve, ffiCarve_wend_add_tail st,
                    sep_cast hm2Reg' (by ac_rfl), fun stRestored m3 hpresR hendR hremR hm3 => ?_⟩
                  p1_steps
                  have hremC : stCarved.rem + wcap + tailPad = st.rem := ffiCarve_rem_reclaim hcarve
                  have hremEq : stRestored.rem = st.rem := by omega
                  have hm3Out : (rtC0Inv rt stRestored ⋆
                      cell64 (rt + 33672#64) scr ⋆
                      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m3 := by
                    dsimp only [failTail, scrFull] at hm3
                    exact sep_ac hm3
                  exact hXorPost stRestored scrLimbs m3 rfl
                    (hpresEnd.trans hpresR) hendR hremEq hm3Out
            · rw [dite_eq_right hcarve]
              have hnotOk : ¬ pilotXorNatOk st bs.length := fun h => by
                rw [pilotXorNatOk, ite_eq_right hzero] at h
                exact hcarve h.2.1
              rw [ite_eq_right hnotOk] at hXorPost
              p1_steps
              · exact hXorPost st scrLimbs m rfl
                  (RtC0State.PreservesMetaExceptEnd.refl st) rfl rfl hm
              · exfalso; exact (by assumption : (0#64 : BitVec 64) ≠ 0#64) rfl

theorem pilotC0_table_impl : TableImpl pilotC0Env pilotC0_fns pilotC0SpecEntries := by
  dsimp only [pilotC0_fns, pilotC0SpecEntries, TableImpl]
  refine ⟨SpecEntry.Impl.of c0_xor_bytes_wp, SpecEntry.Impl.of lcnf_c0_kissat_raw_wp,
    SpecEntry.Impl.of lcnf_c0_kissat_solve_ba_wp,
    SpecEntry.Impl.of lcnf_c0_kissat_solve_nat_wp,
    SpecEntry.Impl.of lcnf_c0_xor_ba_wp, SpecEntry.Impl.of lcnf_c0_xor_nat_wp, trivial⟩

end

end LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
