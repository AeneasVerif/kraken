module

public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Containers`, Part 2: `ByteArray` (`tag 248`, `m_other = 1`)

Proves `Func.wp` contracts against `rtR2Env` for all `ByteArray` runtime helpers and primitives:
- `r2_alloc_sarray` (`r2_alloc_sarray_wp`)
- `r2_ensure_excl_ba` (`r2_ensure_excl_ba_wp`)
- `lcnf_ba_empty` (`lcnf_ba_empty_wp`)
- `lcnf_ba_mk_empty` (`lcnf_ba_mk_empty_wp`)
- `lcnf_ba_mk` (`lcnf_ba_mk_wp`)
- `lcnf_ba_get` (`lcnf_ba_get_wp`)
- `lcnf_ba_set` (`lcnf_ba_set_wp`)
- `lcnf_ba_push` (`lcnf_ba_push_wp`)
- `lcnf_ba_cmp_op` (`lcnf_ba_cmp_op_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

local macro "r2_step" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_step))

/-! ## 1. `align8` & `ByteArray` Allocation/Assembly Helpers -/

theorem align8_idemp (n : Nat) : align8 (align8 n) = align8 n := by
  unfold align8; omega

theorem baAllocBytes_ge (cap : Nat) : 24 + cap ≤ baAllocBytes cap := by
  unfold baAllocBytes align8; omega

theorem baAllocBytes_mod8 (cap : Nat) : baAllocBytes cap % 8 = 0 := by
  unfold baAllocBytes align8; omega

theorem bv64_and_not7_eq (x : BitVec 64) :
    (x &&& 0xfffffffffffffff8#64).toNat = (x.toNat / 8) * 8 := by
  have hlt1 : (x &&& 0xfffffffffffffff8#64).toNat < 2 ^ 64 := BitVec.isLt _
  have hlt2 : (x.toNat / 8) * 8 < 2 ^ 64 := by
    have := Nat.div_mul_le_self x.toNat 8
    have := x.isLt
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_and]
  have hm : (0xfffffffffffffff8#64 : BitVec 64).toNat = 8 * (2 ^ 61 - 1) := by decide
  have hr : (x.toNat / 8) * 8 = (x.toNat >>> 3) <<< 3 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hm2 : 8 * (2 ^ 61 - 1) = (2 ^ 61 - 1) <<< 3 := by
    decide
  rw [hm, hr, hm2]
  by_cases hi3 : i < 3
  · simp only [Nat.testBit_and, Nat.testBit_shiftLeft, show ¬ 3 ≤ i by omega, decide_false,
      Bool.false_and, Bool.and_false]
  · have hi3' : 3 ≤ i := by omega
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, decide_eq_true hi3', Bool.true_and,
      Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    by_cases hi64 : i < 64
    · have hsub : i - 3 < 61 := by omega
      have hadd : 3 + (i - 3) = i := by omega
      simp [hsub, hadd]
    · have h1 : Nat.testBit x.toNat i = false := Nat.testBit_lt_two_pow (by
        have := x.isLt
        have : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        omega)
      have h2 : ¬ i - 3 < 61 := by omega
      have hadd : 3 + (i - 3) = i := by omega
      simp [h1, h2, hadd]

theorem ba_sz_mask_toNat (cap : BitVec 64) (hcap : cap.toNat ≤ baMaxCap) :
    ((24#64 + cap + 7#64) &&& 0xfffffffffffffff8#64).toNat = baAllocBytes cap.toNat := by
  have hfit : 24 + cap.toNat + 7 < 2 ^ 64 := by unfold baMaxCap at hcap; omega
  have hsum : (24#64 + cap + 7#64).toNat = 24 + cap.toNat + 7 := by
    have h24 : (24#64 : BitVec 64).toNat = 24 := rfl
    have h7 : (7#64 : BitVec 64).toNat = 7 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, h24, h7]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [bv64_and_not7_eq, hsum]
  unfold baAllocBytes align8
  omega

theorem region_pop_cell64 {a : BitVec 64} {rem : Nat} (hrem : 8 ≤ rem) (hfit : rem ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a rem ⋆ R) m) :
    ∃ w : BitVec 64, (cell64 a w ⋆ region (a + 8#64) (rem - 8) ⋆ R) m := by
  have heq : rem = 8 + (rem - 8) := by omega
  rw [heq, region_split (by omega), sep_assoc] at hm
  obtain ⟨f1, f2, hu, hd, hr1, hr2⟩ := hm
  obtain ⟨w, hw⟩ := region_to_cell64 hr1
  have hwSep : (cell64 a w ⋆ (region (a + 8#64) (rem - 8) ⋆ R)) m := ⟨f1, f2, hu, hd, hw, hr2⟩
  exact ⟨w, sep_cast hwSep (by ac_rfl)⟩

theorem region_to_3cells_rem {p : BitVec 64} {bytes : Nat} (hge : 24 ≤ bytes)
    (hfit : bytes ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region p bytes ⋆ R) m) :
    ∃ w0 w1 w2 : BitVec 64,
      (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
        region (p + 24#64) (bytes - 24) ⋆ R) m := by
  obtain ⟨w0, h0⟩ := region_pop_cell64 (by omega) hfit hm
  have h1in : (region (p + 8#64) (bytes - 8) ⋆ (cell64 p w0 ⋆ R)) m := sep_cast h0 (by ac_rfl)
  obtain ⟨w1, h1⟩ := region_pop_cell64 (by omega) (by omega) h1in
  have h2in : (region (p + 16#64) (bytes - 16) ⋆ (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ R)) m := by
    rw [ptr_add_nat_r2, show bytes - 8 - 8 = bytes - 16 by omega] at h1
    exact sep_cast h1 (by ac_rfl)
  obtain ⟨w2, h2⟩ := region_pop_cell64 (by omega) (by omega) h2in
  rw [ptr_add_nat_r2, show bytes - 16 - 8 = bytes - 24 by omega] at h2
  exact ⟨w0, w1, w2, sep_cast h2 (by ac_rfl)⟩

theorem mkBaObj_totalBytes (r : BitVec 64) (rc : BitVec 32) (cap : Nat) (data : List UInt8) :
    (mkBaObj r rc cap data).totalBytes = baAllocBytes cap := by
  simp [LcnfObj.totalBytes, mkBaObj, sarrayTag, arrayTag, baAllocBytes]

theorem mkBaObj_mem_of_parts {r : BitVec 64} {cap : Nat} {data : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (cell64 r baHeaderWord ⋆
      cell64 (r + 8#64) (BitVec.ofNat 64 data.length) ⋆
      cell64 (r + 16#64) (BitVec.ofNat 64 cap) ⋆
      bytes (r + 24#64) data ⋆
      region (r + 24#64 + BitVec.ofNat 64 data.length) (baAllocBytes cap - 24 - data.length) ⋆
      R) m) :
    (lcnfObjMem (mkBaObj r 1#32 cap data) ⋆ R) m := by
  rw [lcnfObjMem_sarray_eq rfl, mkBaObj_header]
  have h1 : (mkBaObj r 1#32 cap data).arrSize = data.length := rfl
  have h2 : (mkBaObj r 1#32 cap data).cap = cap := rfl
  have h3 : (mkBaObj r 1#32 cap data).scalarData = data := rfl
  have h4 : (mkBaObj r 1#32 cap data).totalBytes = baAllocBytes cap := mkBaObj_totalBytes _ _ _ _
  have haddr : (mkBaObj r 1#32 cap data).addr = r := rfl
  rw [haddr, h1, h2, h3, h4]
  rw [ptr_add_nat_r2,
    show baAllocBytes cap - 24 - data.length = baAllocBytes cap - (24 + data.length) by omega] at hm
  exact hm

theorem lcnfObjMem_mkBaObj_eq_of_canon {o : LcnfObj} (hc : BaCanon o) :
    lcnfObjMem (mkBaObj o.addr o.rc o.cap o.scalarData) = lcnfObjMem o := by
  rw [lcnfObjMem_sarray_eq rfl, lcnfObjMem_sarray_eq hc.2.2.2.2.2.1]
  have hhdr : (mkBaObj o.addr o.rc o.cap o.scalarData).header = o.header := by
    unfold LcnfObj.header mkBaObj
    rw [hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1]
  have htb1 : (mkBaObj o.addr o.rc o.cap o.scalarData).totalBytes = baAllocBytes o.cap :=
    mkBaObj_totalBytes _ _ _ _
  have htb2 : o.totalBytes = baAllocBytes o.cap := by
    unfold LcnfObj.totalBytes
    simp [hc.2.2.2.2.2.1, hc.2.2.2.2.1, sarrayTag, arrayTag, baAllocBytes]
  have haddr : (mkBaObj o.addr o.rc o.cap o.scalarData).addr = o.addr := rfl
  have hars : (mkBaObj o.addr o.rc o.cap o.scalarData).arrSize = o.arrSize :=
    hc.2.2.2.2.2.2.1.symm
  have hcap : (mkBaObj o.addr o.rc o.cap o.scalarData).cap = o.cap := rfl
  have hdat : (mkBaObj o.addr o.rc o.cap o.scalarData).scalarData = o.scalarData := rfl
  rw [hhdr, htb1, htb2, haddr, hars, hcap, hdat]

theorem lcnfObjMem_sarray_elim {o : LcnfObj} (hc : BaCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    (cell64 o.addr o.header ⋆
      cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      bytes (o.addr + 24#64) o.scalarData ⋆
      region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
        (baAllocBytes o.cap - (24 + o.scalarData.length)) ⋆ R) m := by
  rw [lcnfObjMem_sarray_eq hc.2.2.2.2.2.1] at hm
  have htb : o.totalBytes = baAllocBytes o.cap := by
    unfold LcnfObj.totalBytes
    simp [hc.2.2.2.2.2.1, hc.2.2.2.2.1, sarrayTag, arrayTag, baAllocBytes]
  rwa [htb] at hm

private theorem ba_load_header_mid {o : LcnfObj} {A R : Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ lcnfObjMem o ⋆ R) m) : loadVal m i64 o.addr = some o.header :=
  r2_lcnfObjMem_load_header (R := A ⋆ R) (sep_cast hm (by ac_rfl))

private theorem ba_load_sz {o : LcnfObj} (hc : BaCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.arrSize) := by
  have hmS := lcnfObjMem_sarray_elim hm (hc := hc)
  exact r2_c0_load_cell64_add8 (R := cell64 o.addr o.header ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    bytes (o.addr + 24#64) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
      (baAllocBytes o.cap - (24 + o.scalarData.length)) ⋆ R) (sep_cast hmS (by ac_rfl))

private theorem ba_load_sz_mid {o : LcnfObj} (hc : BaCanon o) {A R : Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.arrSize) :=
  ba_load_sz hc (R := A ⋆ R) (sep_cast hm (by ac_rfl))

private theorem ba_load_cap_mid {o : LcnfObj} (hc : BaCanon o) {A R : Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 16#64) = some (BitVec.ofNat 64 o.cap) := by
  have hmS := lcnfObjMem_sarray_elim hc (R := A ⋆ R) (sep_cast hm (by ac_rfl))
  exact r2_c0_load_cell64_add16 (R := cell64 o.addr o.header ⋆
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
    bytes (o.addr + 24#64) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
      (baAllocBytes o.cap - (24 + o.scalarData.length)) ⋆ A ⋆ R) (sep_cast hmS (by ac_rfl))

private theorem arr_load_sz_mid {o : LcnfObj} (hc : ArrCanon o) {A R : Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.fields.length) := by
  have hmA : (lcnfObjMem o ⋆ (A ⋆ R)) m := sep_cast hm (by ac_rfl)
  rw [lcnfObjMem_array_eq hc.2.2.2.2.2.1] at hmA
  exact r2_c0_load_cell64_add8 (R := cell64 o.addr o.header ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    array64 (o.addr + 24#64) o.fields ⋆
    region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
      (8 * (o.cap - o.fields.length)) ⋆ A ⋆ R) (sep_cast hmA (by ac_rfl))

private theorem arr_load_elem_mid {o : LcnfObj} (hc : ArrCanon o) {i : BitVec 64}
    {A R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < o.fields.length)
    (hm : (A ⋆ lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 24#64 + 8#64 * i) = some o.fields[i.toNat] := by
  have hmA : (lcnfObjMem o ⋆ (A ⋆ R)) m := sep_cast hm (by ac_rfl)
  rw [lcnfObjMem_array_eq hc.2.2.2.2.2.1] at hmA
  exact r2_c0_load_array64_add24_mul8 (R := cell64 o.addr o.header ⋆
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
      (8 * (o.cap - o.fields.length)) ⋆ A ⋆ R) (sep_cast hmA (by ac_rfl)) hi

theorem BaCanon.arrSize_lt_64 {o : LcnfObj} (hc : BaCanon o) : o.arrSize < 2 ^ 64 := by
  have := hc.2.2.2.2.2.2.2.1
  have := hc.2.2.2.2.2.2.2.2
  unfold baMaxCap at *; omega

theorem BaCanon.cap_lt_64 {o : LcnfObj} (hc : BaCanon o) : o.cap < 2 ^ 64 := by
  have := hc.2.2.2.2.2.2.2.2
  unfold baMaxCap at *; omega

theorem RtC0State.workCap_eq_of_preservesMeta {st st' : RtC0State} (h : st'.PreservesMeta st) :
    st'.workCap = st.workCap := by
  simp [RtC0State.workCap, h.2.2.2.2.2.1]

theorem uint8_ofNat_truncate8 (w : BitVec 64) :
    UInt8.ofNat (BitVec.truncate 8 w).toNat = UInt8.ofNat w.toNat := by
  apply UInt8.eq_of_toFin_eq
  apply Fin.ext
  change (BitVec.setWidth 8 w).toNat % 256 = w.toNat % 256
  simp [BitVec.toNat_setWidth]

theorem ba_rc_of_mask_eq1 {o : LcnfObj} (hwf : o.Wf)
    (hm : (o.header &&& 4294967295#64) = 1#64) : o.rc = 1#32 := by
  have hrcEq := LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
  rw [hrcEq] at hm
  have htn : (BitVec.ofNat 64 o.rc.toNat).toNat = 1 := by rw [hm]; rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans o.rc.isLt (by decide))] at htn
  exact BitVec.eq_of_toNat_eq htn

theorem ba_rc_ne1_of_mask {o : LcnfObj} (hwf : o.Wf)
    (hm : (o.header &&& 4294967295#64) ≠ 1#64) : o.rc ≠ 1#32 := by
  have hrcEq := LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
  intro h1
  rw [h1] at hrcEq
  apply hm
  rw [hrcEq]
  rfl

/-! ## 2. `r2_alloc_sarray` & `r2_ensure_excl_ba` WP Proofs -/

theorem r2_alloc_sarray_wp :
    ∀ xs m Q X, r2AllocSarraySpec xs m Q X → Func.wp rtR2Env r2_alloc_sarray_body xs m Q X := by
  intro ⟨rt, size, cap, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2_alloc_sarray_body, r2AllocSarraySpec] at hPre ⊢
  change LeanQbe.T.wp _ _ _ _ _
  by_cases hvalid : size.toNat ≤ cap.toNat ∧ cap.toNat ≤ baMaxCap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hvalid)] at hPre
    rcases hPre with ⟨st, R, hav, hm, hk⟩
    r2_steps
    · exfalso
      have hc : 268435416 < cap.toNat := by assumption
      unfold baMaxCap at hvalid; omega
    · have hszEq : ((24 + cap + 7 &&& 18446744073709551608 : BitVec 64)).toNat =
          baAllocBytes cap.toNat := ba_sz_mask_toNat cap hvalid.2
      have hszLe : ((24 + cap + 7 &&& 18446744073709551608 : BitVec 64)).toNat ≤ 268435448 := by
        rw [hszEq]; unfold baAllocBytes align8 baMaxCap at *; omega
      r2_call rtR2Env_lcnf_alloc
      dsimp only [lcnfAllocRemSpec, vals, Tup.map, Arg.val]
      have hid : align8 (baAllocBytes cap.toNat) = baAllocBytes cap.toNat :=
        align8_idemp (24 + cap.toNat)
      rw [hszEq, hid]
      refine ⟨st, R, by rw [← hszEq]; exact hszLe, ?_, ?_, hav, hm,
        fun p st' m1 hp0 hp8 hpr hrem hrem2 hm1 => ?_⟩
      · have := baAllocBytes_ge cap.toNat; unfold rtMinObjBytes; omega
      · unfold baAllocBytes align8 rtMaxObjBytes baMaxCap at *; omega
      · have hm1' : (region p (baAllocBytes cap.toNat) ⋆ (rtC0Inv rt st' ⋆ R)) m1 :=
          sep_cast hm1 (by ac_rfl)
        have hge24 : 24 ≤ baAllocBytes cap.toNat := by
          have := baAllocBytes_ge cap.toNat; omega
        have hfit24 : baAllocBytes cap.toNat ≤ 2 ^ 64 := by
          unfold baAllocBytes align8 baMaxCap at *; omega
        obtain ⟨w0, w1, w2, hp3⟩ := region_to_3cells_rem hge24 hfit24 hm1'
        change LeanQbe.T.wp _ _ _ _ _
        have hpc : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
            region (p + 24#64) (baAllocBytes cap.toNat - 24) ⋆ rtC0Inv rt st' ⋆ R)) m1 :=
          sep_cast hp3 (by ac_rfl)
        apply wp_store_sep
        · exact store_cell64 baHeaderWord hpc
        · intro m2 hm2
          r2_step
          have hm2' : (cell64 (p + 8#64) w1 ⋆ (cell64 p baHeaderWord ⋆
              cell64 (p + 16#64) w2 ⋆ region (p + 24#64) (baAllocBytes cap.toNat - 24) ⋆
              rtC0Inv rt st' ⋆ R)) m2 := sep_cast hm2 (by ac_rfl)
          apply wp_store_sep
          · exact store_cell64 size hm2'
          · intro m3 hm3
            r2_step
            have hm3' : (cell64 (p + 16#64) w2 ⋆ (cell64 p baHeaderWord ⋆
                cell64 (p + 8#64) size ⋆ region (p + 24#64) (baAllocBytes cap.toNat - 24) ⋆
                rtC0Inv rt st' ⋆ R)) m3 := sep_cast hm3 (by ac_rfl)
            apply wp_store_sep
            · exact store_cell64 cap hm3'
            · intro m4 hm4
              r2_steps
              dsimp only [Arg.val] at hm4
              rw [show (16 : BitVec 64) = 16#64 from rfl] at hm4
              exact hk p st' m4 hp0 hp8 hpr hrem hrem2 (sep_cast hm4 (by ac_rfl))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hvalid)] at hPre
    r2_steps <;> first
      | exact hPre
      | (exfalso
         have h1 : ¬ 268435416 < cap.toNat := by assumption
         have h2 : ¬ cap.toNat < size.toNat := by assumption
         unfold baMaxCap at hvalid; omega)

private theorem ba_ensure_fast_ok {rt ba : BitVec 64} {st : RtC0State} {baObj : LcnfObj}
    {expand : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {P_panic : Prop}
    (hcanon : BaCanon baObj) (haddr : baObj.addr = ba) (hrc1 : baObj.rc = 1#32)
    (hfast : expand = 0#64 ∨ baObj.arrSize < baObj.cap)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m)
    (hk : if expand ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap then
        P_panic
      else
        let newCap := baEnsureCap baObj.arrSize baObj.cap expand
        let needAlloc := baObj.rc ≠ 1#32 ∨ (expand ≠ 0#64 ∧ baObj.arrSize ≥ baObj.cap)
        let reqBytes := baAllocBytes newCap
        (needAlloc → st.hasFree reqBytes ∨ reqBytes ≤ st.rem) ∧
        ∀ r st' m',
          r ≠ 0#64 → r.toNat % 8 = 0 →
          st'.PreservesMeta st → st'.rem ≤ st.rem →
          (baObj.rc = 1#32 → (expand = 0#64 ∨ baObj.arrSize < baObj.cap) → r = ba ∧ st' = st) →
          (expand ≠ 0#64 → baObj.arrSize < newCap) →
          newCap ≤ baMaxCap →
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkBaObj r 1#32 newCap baObj.scalarData) ⋆
            (if baObj.rc = 1#32 then emp else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))) ⋆
            R) m' →
          Q (r, ()) m') :
    Q (ba, ()) m := by
  have hnotPanic : ¬ (expand ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap) := by
    rcases hfast with rfl | hlt
    · simp
    · omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnotPanic)] at hk
  have hcapEq : baEnsureCap baObj.arrSize baObj.cap expand = baObj.cap := by
    rcases hfast with rfl | hlt
    · simp [baEnsureCap]
    · simp [baEnsureCap, hlt]
  have hmemEq : lcnfObjMem (mkBaObj ba 1#32 (baEnsureCap baObj.arrSize baObj.cap expand)
      baObj.scalarData) = lcnfObjMem baObj := by
    rw [hcapEq, ← haddr, ← hrc1, lcnfObjMem_mkBaObj_eq_of_canon hcanon]
  have hm' : (rtC0Inv rt st ⋆
      lcnfObjMem (mkBaObj ba 1#32 (baEnsureCap baObj.arrSize baObj.cap expand) baObj.scalarData) ⋆
      (if baObj.rc = 1#32 then emp else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))) ⋆
      R) m := by
    rw [hmemEq, ite_eq_left_of_eq_true _ _ (eq_true hrc1)]
    exact sep_cast hm (by ac_rfl)
  refine hk.2 ba st m (haddr ▸ hcanon.1) (haddr ▸ hcanon.2.1) (RtC0State.PreservesMeta.refl st)
    (Nat.le_refl _) (fun _ _ => ⟨rfl, rfl⟩) ?_ ?_ hm'
  · intro hex
    rcases hfast with h0 | hlt
    · exact absurd h0 hex
    · rw [hcapEq]; exact hlt
  · rw [hcapEq]; exact hcanon.2.2.2.2.2.2.2.2

private theorem baEnsureCap_props {baObj : LcnfObj} (hcanon : BaCanon baObj)
    {expand : BitVec 64}
    (hnotPanic : ¬ (expand ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap)) :
    baObj.arrSize ≤ baEnsureCap baObj.arrSize baObj.cap expand ∧
      baEnsureCap baObj.arrSize baObj.cap expand ≤ baMaxCap ∧
      (expand ≠ 0#64 → baObj.arrSize < baEnsureCap baObj.arrSize baObj.cap expand) := by
  have hleCap := hcanon.2.2.2.2.2.2.2.1
  have hmax := hcanon.2.2.2.2.2.2.2.2
  by_cases hexp : expand = 0#64
  · simp [baEnsureCap, hexp, hleCap, hmax]
  · by_cases hlt : baObj.arrSize < baObj.cap
    · unfold baMaxCap at hmax ⊢
      have hcap : baEnsureCap baObj.arrSize baObj.cap expand = baObj.cap := by
        simp [baEnsureCap, hexp, hlt]
      rw [hcap]
      exact ⟨hleCap, hmax, fun _ => hlt⟩
    · unfold baMaxCap at hmax hnotPanic
      have hnotge : ¬ (268435416 ≤ baObj.cap) :=
        fun h => hnotPanic ⟨hexp, Nat.le_of_not_lt hlt, h⟩
      have hltMax : baObj.cap < baMaxCap := by unfold baMaxCap; omega
      by_cases hcap0 : baObj.cap = 0
      · have hars0 : baObj.arrSize = 0 := by omega
        have hcap : baEnsureCap baObj.arrSize baObj.cap expand = 8 := by
          simp [baEnsureCap, hexp, hcap0, hars0]
        rw [hcap]
        unfold baMaxCap
        exact ⟨by omega, by omega, fun _ => by omega⟩
      · have hcap : baEnsureCap baObj.arrSize baObj.cap expand = min baMaxCap (baObj.cap * 2) := by
          simp [baEnsureCap, hexp, hlt, hcap0]
        rw [hcap]
        unfold baMaxCap at hltMax ⊢
        exact ⟨by omega, by omega, fun _ => by omega⟩

theorem r2_ensure_excl_ba_wp :
    ∀ xs m Q X, r2EnsureExclBaSpec xs m Q X → Func.wp rtR2Env r2_ensure_excl_ba_body xs m Q X := by
  intro ⟨rt, ba, expand, ⟨⟩⟩ m Q X ⟨st, baObj, R, haddr, hcanon, hm, hPost⟩
  subst haddr
  have hwf := hcanon.wf
  have hsz64 := hcanon.arrSize_lt_64
  have hcap64 := hcanon.cap_lt_64
  have harsMod : baObj.arrSize % 2 ^ 64 = baObj.arrSize := Nat.mod_eq_of_lt hsz64
  have hcapMod : baObj.cap % 2 ^ 64 = baObj.cap := Nat.mod_eq_of_lt hcap64
  have hrcEq := LcnfObj.header_rc baObj hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1
  dsimp only [Func.wp, r2_ensure_excl_ba_body]
  change LeanQbe.T.wp _ _ _ _ _
  apply wp_load_of (ba_load_header_mid hm)
  r2_step
  apply wp_load_of (ba_load_sz_mid hcanon hm)
  r2_step
  apply wp_load_of (ba_load_cap_mid hcanon hm)
  apply wp_join_group
    (P := fun _ m' => m' = m ∧ (baObj.rc ≠ 1#32 ∨ (expand ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize)))
  · intro _ ⟨⟩ m' ⟨hmEq, hslow⟩
    subst hmEq
    change LeanQbe.T.wp _ _ _ _ _
    by_cases hpanic : expand ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hpanic)] at hPost
      apply wp_join_group (P := fun _ _ => False)
      · intro _ _ _ hFalse; exact hFalse.elim
      · intro _ hJ
        have hcapMax : baObj.cap = 268435416 := by
          have := hcanon.2.2.2.2.2.2.2.2; unfold baMaxCap at *; omega
        have harsMax : baObj.arrSize = 268435416 := by
          have := hcanon.2.2.2.2.2.2.2.1; omega
        r2_steps <;> first
          | exact hPost
          | (exfalso
             simp only [harsMod, hcapMod, BitVec.toNat_ofNat] at *
             try (have hcap0 : BitVec.ofNat 64 baObj.cap = 0 := by assumption
                  have := congrArg BitVec.toNat hcap0
                  rw [BitVec.toNat_ofNat, hcapMod] at this
                  omega)
             omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hpanic)] at hPost
      rcases hPost with ⟨hav, hpost⟩
      have hcapProps := baEnsureCap_props hcanon hpanic
      let newCap := baEnsureCap baObj.arrSize baObj.cap expand
      have hszLe : baObj.arrSize ≤ newCap := hcapProps.1
      have hcapMax : newCap ≤ baMaxCap := hcapProps.2.1
      have hexLt : expand ≠ 0#64 → baObj.arrSize < newCap := hcapProps.2.2
      have hcap64New : newCap < 2 ^ 64 := by unfold baMaxCap at hcapMax; omega
      apply wp_join_group
        (P := fun (xs : Tup Val [i64]) m1 => match xs with
          | (nc, PUnit.unit) => m1 = m' ∧ nc = BitVec.ofNat 64 newCap)
      · intro _ ⟨nc, ⟨⟩⟩ m1 ⟨rfl, hnc⟩
        subst hnc
        change LeanQbe.T.wp _ _ _ _ _
        r2_call rtR2Env_r2_alloc_sarray
        dsimp only [r2AllocSarraySpec, vals, Tup.map, Arg.val]
        have hszTo : (BitVec.ofNat 64 baObj.arrSize).toNat = baObj.arrSize := by
          rw [BitVec.toNat_ofNat, harsMod]
        have hncTo : (BitVec.ofNat 64 newCap).toNat = newCap := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap64New]
        have hvalidA : (BitVec.ofNat 64 baObj.arrSize).toNat ≤ (BitVec.ofNat 64 newCap).toNat ∧
            (BitVec.ofNat 64 newCap).toNat ≤ baMaxCap := by
          rw [hszTo, hncTo]; exact ⟨hszLe, hcapMax⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true hvalidA)]
        refine ⟨st, lcnfObjMem baObj ⋆ R, ?_, sep_cast hm (by ac_rfl),
          fun r st1 m1 hr0 hr8 hpr1 hrem1 _ hm1 => ?_⟩
        · rw [hncTo]; exact hav hslow
        · rw [hncTo] at hm1
          change LeanQbe.T.wp _ _ _ _ _
          r2_steps
          have hlenData : baObj.scalarData.length = (BitVec.ofNat 64 baObj.arrSize).toNat := by
            rw [hszTo]; exact hcanon.2.2.2.2.2.2.1.symm
          have hgeData : baObj.scalarData.length ≤ baAllocBytes newCap - 24 := by
            have := baAllocBytes_ge newCap; have := hcanon.2.2.2.2.2.2.1; omega
          have hfitRem : baAllocBytes newCap - 24 ≤ 2 ^ 64 := by
            unfold baAllocBytes align8 baMaxCap at *; omega
          r2_call rtR2Env_r2_mem_copy_bytes
          dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
          have hm1' : (bytes (baObj.addr + 24#64) baObj.scalarData ⋆
              region (r + 24#64) (baAllocBytes newCap - 24) ⋆
              (rtC0Inv rt st1 ⋆ cell64 r baHeaderWord ⋆
                cell64 (r + 8#64) (BitVec.ofNat 64 baObj.arrSize) ⋆
                cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                cell64 baObj.addr baObj.header ⋆
                cell64 (baObj.addr + 8#64) (BitVec.ofNat 64 baObj.arrSize) ⋆
                cell64 (baObj.addr + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
                region (baObj.addr + BitVec.ofNat 64 (24 + baObj.scalarData.length))
                  (baAllocBytes baObj.cap - (24 + baObj.scalarData.length)) ⋆ R)) m1 := by
            have h1S := lcnfObjMem_sarray_elim hcanon
              (R := rtC0Inv rt st1 ⋆ cell64 r baHeaderWord ⋆
                cell64 (r + 8#64) (BitVec.ofNat 64 baObj.arrSize) ⋆
                cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                region (r + 24#64) (baAllocBytes newCap - 24) ⋆ R)
              (sep_cast hm1 (by ac_rfl))
            exact sep_cast h1S (by ac_rfl)
          refine ⟨baObj.scalarData, baAllocBytes newCap - 24, _, hlenData,
            by rw [hszTo]; have := baAllocBytes_ge newCap; omega, hfitRem, hm1',
            fun m2 hm2 => ?_⟩
          change LeanQbe.T.wp _ _ _ _ _
          have hlenB : BitVec.ofNat 64 baObj.arrSize =
              BitVec.ofNat 64 baObj.scalarData.length := by rw [hcanon.2.2.2.2.2.2.1]
          have hm2Bytes : (cell64 r baHeaderWord ⋆
              cell64 (r + 8#64) (BitVec.ofNat 64 baObj.scalarData.length) ⋆
              cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
              bytes (r + 24#64) baObj.scalarData ⋆
              region (r + 24#64 + BitVec.ofNat 64 baObj.scalarData.length)
                (baAllocBytes newCap - 24 - baObj.scalarData.length) ⋆
              (rtC0Inv rt st1 ⋆
                cell64 baObj.addr baObj.header ⋆
                cell64 (baObj.addr + 8#64) (BitVec.ofNat 64 baObj.scalarData.length) ⋆
                cell64 (baObj.addr + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
                bytes (baObj.addr + 24#64) baObj.scalarData ⋆
                region (baObj.addr + BitVec.ofNat 64 (24 + baObj.scalarData.length))
                  (baAllocBytes baObj.cap - (24 + baObj.scalarData.length)) ⋆ R)) m2 := by
            have hlenTo : (BitVec.ofNat 64 baObj.scalarData.length).toNat =
                baObj.scalarData.length := by
              have hlenLt64 : baObj.scalarData.length < 2 ^ 64 := by
                rw [← hcanon.2.2.2.2.2.2.1]; exact hsz64
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenLt64]
            rw [hlenB] at hm2
            rw [hlenTo] at hm2
            rw [show (24 : BitVec 64) = 24#64 from rfl] at hm2
            let regR := region (r + 24#64 + BitVec.ofNat 64 baObj.scalarData.length)
              (baAllocBytes newCap - 24 - baObj.scalarData.length)
            let regA := region (baObj.addr + BitVec.ofNat 64 (24 + baObj.scalarData.length))
              (baAllocBytes baObj.cap - (24 + baObj.scalarData.length))
            have hm2A : (bytes (baObj.addr + 24#64) baObj.scalarData ⋆
                bytes (r + 24#64) baObj.scalarData ⋆ regR ⋆
                (rtC0Inv rt st1 ⋆ cell64 r baHeaderWord ⋆
                  cell64 (r + 8#64) (BitVec.ofNat 64 baObj.scalarData.length) ⋆
                  cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
                  cell64 baObj.addr baObj.header ⋆
                  cell64 (baObj.addr + 8#64) (BitVec.ofNat 64 baObj.scalarData.length) ⋆
                  cell64 (baObj.addr + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
                  regA ⋆ R)) m2 := hm2
            change (cell64 r baHeaderWord ⋆
              cell64 (r + 8#64) (BitVec.ofNat 64 baObj.scalarData.length) ⋆
              cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
              bytes (r + 24#64) baObj.scalarData ⋆ regR ⋆
              (rtC0Inv rt st1 ⋆ cell64 baObj.addr baObj.header ⋆
                cell64 (baObj.addr + 8#64) (BitVec.ofNat 64 baObj.scalarData.length) ⋆
                cell64 (baObj.addr + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
                bytes (baObj.addr + 24#64) baObj.scalarData ⋆ regA ⋆ R)) m2
            exact sep_cast hm2A (by ac_rfl)
          have hnewM := mkBaObj_mem_of_parts hm2Bytes
          have hmOld : (lcnfObjMem baObj ⋆
              (rtC0Inv rt st1 ⋆ lcnfObjMem (mkBaObj r 1#32 newCap baObj.scalarData) ⋆ R)) m2 := by
            rw [lcnfObjMem_sarray_eq hcanon.2.2.2.2.2.1, hcanon.2.2.2.2.2.2.1]
            have htb : baObj.totalBytes = baAllocBytes baObj.cap := by
              unfold LcnfObj.totalBytes
              simp [hcanon.2.2.2.2.2.1, hcanon.2.2.2.2.1, sarrayTag, arrayTag, baAllocBytes]
            rw [htb]
            exact sep_cast hnewM (by ac_rfl)
          let oldKeep :=
            if baObj.rc = 1#32 then emp else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))
          apply wp_join_group (P := fun _ m3 =>
            ∃ st3 : RtC0State, st3.PreservesMeta st1 ∧ st3.rem ≤ st1.rem ∧
              (rtC0Inv rt st3 ⋆ lcnfObjMem (mkBaObj r 1#32 newCap baObj.scalarData) ⋆
                oldKeep ⋆ R) m3)
          · intro _ ⟨⟩ m3 ⟨st3, hpr3, hrem3, hm3⟩
            r2_steps
            refine hpost r st3 m3 hr0 hr8 (hpr1.trans hpr3) (by omega) ?_ hexLt hcapMax hm3
            intro hrc1 hfast
            rcases hslow with hne | ⟨hex, hge⟩
            · exact absurd hrc1 hne
            · rcases hfast with rfl | hlt
              · exact absurd rfl hex
              · omega
          · intro Jret hJret
            r2_steps
            · have hrc1 : baObj.rc = 1#32 := ba_rc_of_mask_eq1 hwf (by assumption)
              have hand0 : (baObj.addr &&& 1#64) = 0#64 := bv64_and1_zero_of_mod8 hcanon.2.1
              have hnotAnd : ¬ (baObj.addr &&& 1#64) ≠ 0#64 := by simp [hand0]
              r2_call rtR2Env_lcnf_free_obj
              dsimp only [lcnfFreeObjSpec, vals, Tup.map, Arg.val]
              rw [ite_eq_right_of_eq_false _ _ (eq_false hnotAnd)]
              obtain ⟨f1, f2, hu, hd, hbaFree, hrest⟩ := hmOld
              have hfreeLay := lcnfObjMem_to_freeObjLayout hwf hbaFree
              have hmFree0 : (freeObjLayout baObj.addr baObj.totalBytes baObj.header ⋆
                  (rtC0Inv rt st1 ⋆
                    lcnfObjMem (mkBaObj r 1#32 newCap baObj.scalarData) ⋆ R)) m2 :=
                ⟨f1, f2, hu, hd, hfreeLay, hrest⟩
              have hmFree : (rtC0Inv rt st1 ⋆
                  freeObjLayout baObj.addr baObj.totalBytes baObj.header ⋆
                  (lcnfObjMem (mkBaObj r 1#32 newCap baObj.scalarData) ⋆ R)) m2 :=
                sep_cast hmFree0 (by ac_rfl)
              refine ⟨st1, baObj.header, baObj.totalBytes, _, hcanon.1, hcanon.2.1,
                hwf.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.2.1, hmFree, ?_⟩
              intro st2 m3 hpr2 hrem2 _ hm3
              r2_steps
              apply hJret
              refine ⟨st2, hpr2, Nat.le_of_eq hrem2, ?_⟩
              dsimp only [oldKeep]
              rw [ite_eq_left_of_eq_true _ _ (eq_true hrc1)]
              exact sep_cast hm3 (by ac_rfl)
            · have hrcNe1 : baObj.rc ≠ 1#32 := ba_rc_ne1_of_mask hwf (by assumption)
              have hgt1 : 1 < baObj.rc.toNat := by
                have hc1 : 1 < (baObj.header &&& 4294967295#64).toNat := by assumption
                rw [hrcEq, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (Nat.lt_trans baObj.rc.isLt (by decide))] at hc1
                exact hc1
              have hgtInt : 1 < baObj.rc.toInt := by
                have hlt231 : baObj.rc.toNat < 2147483648 := by
                  have hc2 : (baObj.header &&& 4294967295#64).toNat < 2147483648 := by assumption
                  rw [hrcEq, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (Nat.lt_trans baObj.rc.isLt (by decide))] at hc2
                  exact hc2
                have h0 := hwf.2.2.1
                rw [BitVec.toInt_eq_toNat_cond] at h0 ⊢; split at h0 <;> omega
              have hmRcHdr := hm
              rw [show (1 : BitVec 64) = 1#64 from rfl,
                lcnfObjHeader_sub1 baObj hwf hgt1] at hmRcHdr
              apply hJret
              refine ⟨st1, RtC0State.PreservesMeta.refl st1, Nat.le_refl _, ?_⟩
              dsimp only [oldKeep]
              rw [ite_eq_right_of_eq_false _ _ (eq_false hrcNe1)]
              simp only [decNonExclRc, hgtInt, ↓reduceIte]
              have htb : (baObj.withRc (baObj.rc - 1#32)).totalBytes = baAllocBytes baObj.cap := by
                unfold LcnfObj.totalBytes LcnfObj.withRc
                simp [hcanon.2.2.2.2.2.1, hcanon.2.2.2.2.1, sarrayTag, arrayTag, baAllocBytes]
              have htagRc : (baObj.withRc (baObj.rc - 1#32)).tag = sarrayTag :=
                hcanon.2.2.2.2.2.1
              rw [lcnfObjMem_sarray_eq htagRc, htb]
              dsimp only [LcnfObj.withRc]
              rw [hcanon.2.2.2.2.2.2.1]
              exact sep_cast hmRcHdr (by ac_rfl)
            · exfalso
              have hnot : ¬ (baObj.header &&& 4294967295#64).toNat < 2147483648 := by assumption
              have h0 := hwf.2.2.1
              rw [hrcEq, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (Nat.lt_trans baObj.rc.isLt (by decide))] at hnot
              rw [BitVec.toInt_eq_toNat_cond] at h0; split at h0 <;> omega
            · have hrcNe1 : baObj.rc ≠ 1#32 := ba_rc_ne1_of_mask hwf (by assumption)
              have hnot : ¬ 1 < (baObj.header &&& 4294967295#64).toNat := by assumption
              have h0 := hwf.2.2.1
              have hlt231 : baObj.rc.toNat < 2147483648 := by
                rw [BitVec.toInt_eq_toNat_cond] at h0; split at h0 <;> omega
              have hrc0Nat : baObj.rc.toNat = 0 := by
                rw [hrcEq, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (Nat.lt_trans baObj.rc.isLt (by decide))] at hnot
                have hne1Nat : baObj.rc.toNat ≠ 1 := fun h => hrcNe1 (BitVec.eq_of_toNat_eq h)
                omega
              have hrc0 : baObj.rc = 0#32 := BitVec.eq_of_toNat_eq hrc0Nat
              have hdec0 : decNonExclRc baObj.rc = baObj.rc := by simp [decNonExclRc, hrc0]
              apply hJret
              refine ⟨st1, RtC0State.PreservesMeta.refl st1, Nat.le_refl _, ?_⟩
              dsimp only [oldKeep]
              rw [ite_eq_right_of_eq_false _ _ (eq_false hrcNe1), hdec0]
              have hself : baObj.withRc baObj.rc = baObj := by cases baObj; rfl
              rw [hself]
              exact sep_cast hmOld (by ac_rfl)
      · intro Jnc hJnc
        r2_steps
        · exfalso
          have hc0 : BitVec.ofNat 64 baObj.cap = 0 := by assumption
          have h0 : baObj.cap = 0 := by
            have := congrArg BitVec.toNat hc0
            rw [BitVec.toNat_ofNat, hcapMod] at this; exact this
          have h8 : (8#64 : BitVec 64).toNat ≤ baObj.arrSize % 2 ^ 64 := by assumption
          rw [harsMod] at h8
          have h8n : (8#64 : BitVec 64).toNat = 8 := rfl
          have := hcanon.2.2.2.2.2.2.2.1; omega
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hne : expand ≠ 0#64 := by assumption
          have hc0 : BitVec.ofNat 64 baObj.cap = 0 := by assumption
          have h0 : baObj.cap = 0 := by
            have := congrArg BitVec.toNat hc0
            rw [BitVec.toNat_ofNat, hcapMod] at this; exact this
          have hars0 : baObj.arrSize = 0 := by have := hcanon.2.2.2.2.2.2.2.1; omega
          simp [newCap, baEnsureCap, hne, h0, hars0]
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hne : expand ≠ 0#64 := by assumption
          have hlt : baObj.arrSize % 2 ^ 64 < baObj.cap % 2 ^ 64 := by assumption
          rw [harsMod, hcapMod] at hlt
          simp [newCap, baEnsureCap, hne, hlt]
        · exfalso
          have hne : expand ≠ 0#64 := by assumption
          have hge : 268435416 ≤ baObj.cap % 2 ^ 64 := by assumption
          have hnlt : ¬ baObj.arrSize % 2 ^ 64 < baObj.cap % 2 ^ 64 := by assumption
          rw [hcapMod] at hge; rw [harsMod, hcapMod] at hnlt
          unfold baMaxCap at hpanic; exact hpanic ⟨hne, by omega, hge⟩
        · exfalso
          have hgt : 268435416 < baObj.arrSize % 2 ^ 64 := by assumption
          rw [harsMod] at hgt
          have := hcanon.2.2.2.2.2.2.2.1; have := hcanon.2.2.2.2.2.2.2.2
          unfold baMaxCap at *; omega
        · exfalso
          have hne : expand ≠ 0#64 := by assumption
          have hge : 268435416 ≤ baObj.arrSize % 2 ^ 64 := by assumption
          rw [harsMod] at hge
          have := hcanon.2.2.2.2.2.2.2.1; have := hcanon.2.2.2.2.2.2.2.2
          unfold baMaxCap at *; apply hpanic; exact ⟨hne, by omega, by omega⟩
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hne : expand ≠ 0#64 := by assumption
          have hnlt : ¬ baObj.arrSize % 2 ^ 64 < baObj.cap % 2 ^ 64 := by assumption
          rw [harsMod, hcapMod] at hnlt
          have hc0 : BitVec.ofNat 64 baObj.cap ≠ 0 := by assumption
          have hcapNe0 : baObj.cap ≠ 0 := fun h0 => hc0 (by simp [h0])
          have hgtMax : 268435416 < baObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 :=
            by assumption
          have hmul : baObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 = baObj.cap * 2 :=
            by
            rw [hcapMod]; have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from h2, Nat.mod_eq_of_lt
              (by have := hcanon.2.2.2.2.2.2.2.2; unfold baMaxCap at *; omega)]
          rw [hmul] at hgtMax
          have hmin : min baMaxCap (baObj.cap * 2) = 268435416 := by unfold baMaxCap; omega
          simp [newCap, baEnsureCap, hne, hnlt, hcapNe0, hmin]
        · exfalso
          have hge2 : baObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 ≤
              baObj.arrSize % 2 ^ 64 := by assumption
          have hc0 : BitVec.ofNat 64 baObj.cap ≠ 0 := by assumption
          have hcapNe0 : baObj.cap ≠ 0 := fun h0 => hc0 (by simp [h0])
          have hmul : baObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 = baObj.cap * 2 :=
            by
            rw [hcapMod]; have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from h2, Nat.mod_eq_of_lt
              (by have := hcanon.2.2.2.2.2.2.2.2; unfold baMaxCap at *; omega)]
          rw [hmul, harsMod] at hge2
          have := hcanon.2.2.2.2.2.2.2.1; omega
        · exfalso
          have hge2 : baObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 ≤
              baObj.arrSize % 2 ^ 64 := by assumption
          have hc0 : BitVec.ofNat 64 baObj.cap ≠ 0 := by assumption
          have hcapNe0 : baObj.cap ≠ 0 := fun h0 => hc0 (by simp [h0])
          have hmul : baObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 = baObj.cap * 2 :=
            by
            rw [hcapMod]; have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from h2, Nat.mod_eq_of_lt
              (by have := hcanon.2.2.2.2.2.2.2.2; unfold baMaxCap at *; omega)]
          rw [hmul, harsMod] at hge2
          have := hcanon.2.2.2.2.2.2.2.1; omega
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hne : expand ≠ 0#64 := by assumption
          have hnlt : ¬ baObj.arrSize % 2 ^ 64 < baObj.cap % 2 ^ 64 := by assumption
          rw [harsMod, hcapMod] at hnlt
          have hc0 : BitVec.ofNat 64 baObj.cap ≠ 0 := by assumption
          have hcapNe0 : baObj.cap ≠ 0 := fun h0 => hc0 (by simp [h0])
          have hngt : ¬ 268435416 < baObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 :=
            by assumption
          have hmul : baObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 = baObj.cap * 2 :=
            by
            rw [hcapMod]; have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from h2, Nat.mod_eq_of_lt
              (by have := hcanon.2.2.2.2.2.2.2.2; unfold baMaxCap at *; omega)]
          rw [hmul] at hngt
          have hmin : min baMaxCap (baObj.cap * 2) = baObj.cap * 2 := by unfold baMaxCap; omega
          simp only [newCap, baEnsureCap, hne, ↓reduceIte, hnlt, hcapNe0, hmin]
          rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_mul]
        · apply hJnc
          refine ⟨rfl, ?_⟩
          have hex : expand = 0#64 := by assumption
          simp [newCap, baEnsureCap, hex]
  · intro Jouter hJouter
    r2_steps
    · have hrc1 := ba_rc_of_mask_eq1 hwf (by assumption)
      have hex : expand = 0#64 := by assumption
      exact ba_ensure_fast_ok hcanon rfl hrc1 (Or.inl hex) hm hPost
    · have hrc1 := ba_rc_of_mask_eq1 hwf (by assumption)
      have hlt : baObj.arrSize % 2 ^ 64 < baObj.cap % 2 ^ 64 := by assumption
      rw [harsMod, hcapMod] at hlt
      exact ba_ensure_fast_ok hcanon rfl hrc1 (Or.inr hlt) hm hPost
    · apply hJouter
      refine ⟨rfl, Or.inr ⟨by assumption, ?_⟩⟩
      have hnlt : ¬ baObj.arrSize % 2 ^ 64 < baObj.cap % 2 ^ 64 := by assumption
      rw [harsMod, hcapMod] at hnlt
      omega
    · apply hJouter
      exact ⟨rfl, Or.inl (ba_rc_ne1_of_mask hwf (by assumption))⟩

/-! ## 3. `lcnf_ba_empty` & `lcnf_ba_mk_empty` WP Proofs -/

private theorem rtC0Inv_load_s_ba_empty_2 {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    loadVal m i64 (rt + 33544#64) = some st.hdr.s_ba_empty := by
  have hm' : (rtC0Inv rt st ⋆ emp ⋆ R) m := by
    rw [← Std.ExtHashMap.sep_emp (rtC0Inv rt st)] at hm
    exact hm
  exact rtC0Inv_load_s_ba_empty hm'

private theorem markPersist_singleton_baEmpty {p : BitVec 64} {objs' : List LcnfObj}
    (hmp : MarkPersistRel p [mkBaObj p 1#32 0 []] objs') :
    objs' = [mkBaObj p 0#32 0 []] := by
  rcases hmp with ⟨hlen, _, _, _, hzip⟩
  cases objs' with
  | nil => simp at hlen
  | cons o' tl =>
    cases tl with
    | cons _ _ => simp at hlen
    | nil =>
      have hpair := hzip (mkBaObj p 1#32 0 [], o') (by simp)
      rcases hpair with ⟨_, haddr, hcs, hot, htag, hfun, har, hcap, hars, hstr,
        hfld, hdat, hlmb, hrc0, _⟩
      have hrc := hrc0 rfl
      rcases o' with ⟨ad, rc, cs, ot, tg, fn, ar, cp, az, sl, fl, sd, lm⟩
      dsimp only [mkBaObj] at haddr hcs hot htag hfun har hcap hars hstr hfld hdat hlmb hrc
      subst haddr hcs hot htag hfun har hcap hars hstr hfld hdat hlmb hrc
      rfl

theorem lcnf_ba_empty_wp :
    ∀ xs m Q X, lcnfBaEmptySpec xs m Q X → Func.wp rtR2Env lcnf_ba_empty_body xs m Q X := by
  intro ⟨rt, ⟨⟩⟩ m Q X ⟨st, R, hm, hSpec⟩
  dsimp only [Func.wp, lcnf_ba_empty_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_step
  rw [wp_load]
  refine ⟨st.hdr.s_ba_empty, rtC0Inv_load_s_ba_empty_2 hm, ?_⟩
  by_cases hempty : st.hdr.s_ba_empty ≠ 0#64
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hempty)] at hSpec
    r2_steps
    exact hSpec
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hempty)] at hSpec
    have hempty0 : st.hdr.s_ba_empty = 0#64 := Classical.not_not.mp hempty
    rcases hSpec with ⟨hw1, hav, hk⟩
    r2_steps
    r2_call rtR2Env_r2_alloc_sarray
    dsimp only [r2AllocSarraySpec, vals, Tup.map, Arg.val]
    have h00 : (0 : BitVec 64).toNat ≤ (0 : BitVec 64).toNat ∧
        (0 : BitVec 64).toNat ≤ baMaxCap := by simp [baMaxCap]
    rw [ite_eq_left_of_eq_true _ _ (eq_true h00)]
    have hba24 : baAllocBytes (0 : BitVec 64).toNat = 24 := by
      simp [baAllocBytes, align8]
    rw [hba24]
    refine ⟨st, R, hav, hm, fun p st1 m1 hp0 hp8 hpr1 hrem1 _ hm1 => ?_⟩
    change LeanQbe.T.wp _ _ _ _ _
    have hmObj1 : (rtC0Inv rt st1 ⋆ lcnfObjMem (mkBaObj p 1#32 0 []) ⋆ R) m1 := by
      have hpParts : (cell64 p baHeaderWord ⋆
          cell64 (p + 8#64) (BitVec.ofNat 64 ([] : List UInt8).length) ⋆
          cell64 (p + 16#64) (BitVec.ofNat 64 0) ⋆
          bytes (p + 24#64) [] ⋆
          region (p + 24#64 + BitVec.ofNat 64 ([] : List UInt8).length)
            (baAllocBytes 0 - 24 - ([] : List UInt8).length) ⋆
          (rtC0Inv rt st1 ⋆ R)) m1 := by
        have hb0 : baAllocBytes 0 = 24 := by simp [baAllocBytes, align8]
        rw [hb0, List.length_nil, show 24 - 24 - 0 = 0 by rfl, region_zero, bytes_nil_eq,
          Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_emp]
        rw [show (0#64 : BitVec 64) = (0 : BitVec 64) from rfl]
        rw [show 24 - 24 = 0 by rfl, region_zero, Std.ExtHashMap.sep_emp] at hm1
        exact sep_cast hm1 (by ac_rfl)
      exact sep_cast (mkBaObj_mem_of_parts hpParts) (by ac_rfl)
    r2_call rtR2Env_lcnf_mark_persistent
    dsimp only [lcnfMarkPersistentSpec, vals, Tup.map, Arg.val]
    have hand0 : (p &&& 1#64) = 0#64 := bv64_and1_zero_of_mod8 hp8
    have hnotAnd : ¬ (p &&& 1#64) ≠ 0#64 := by simp [hand0]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnotAnd)]
    have hcan1 : BaCanon (mkBaObj p 1#32 0 []) :=
      mkBaObj_canon hp0 hp8 (by decide) (by simp) (by unfold baMaxCap; omega)
    have hwf1 : (mkBaObj p 1#32 0 []).Wf := hcan1.wf
    have hmHeap1 : (rtC0Inv rt st1 ⋆ lcnfHeap [mkBaObj p 1#32 0 []] ⋆ R) m1 := by
      simpa [lcnfHeap, Std.ExtHashMap.sep_emp] using hmObj1
    have hwc1 : ([mkBaObj p 1#32 0 []] : List LcnfObj).length ≤ st1.workCap := by
      rw [RtC0State.workCap_eq_of_preservesMeta hpr1]; exact hw1
    have hcl1 : lcnfHeapClosed [mkBaObj p 1#32 0 []] := by
      intro o ho a ha
      simp only [List.mem_singleton] at ho; subst ho
      simp [LcnfObj.childFields, mkBaObj, sarrayTag, closureTag, arrayTag] at ha
    refine ⟨st1, [mkBaObj p 1#32 0 []], R, hwc1, hmHeap1,
      ⟨mkBaObj p 1#32 0 [], by simp, rfl⟩,
      fun o ho => by simp at ho; subst ho; exact hwf1, hcl1, ?_⟩
    intro st2 objs' m2 hpr2 hrem2 hmp hm2
    rw [markPersist_singleton_baEmpty hmp] at hm2
    have hm2' : (rtC0Inv rt st2 ⋆ emp ⋆ (lcnfObjMem (mkBaObj p 0#32 0 []) ⋆ R)) m2 := by
      simp only [lcnfHeap, Std.ExtHashMap.sep_emp] at hm2
      rw [← Std.ExtHashMap.sep_emp (rtC0Inv rt st2)]
      exact sep_cast hm2 (by ac_rfl)
    r2_step
    obtain ⟨hstOk, hstMem⟩ := rtC0Inv_store_s_ba_empty p hm2'
    rw [wp_store]
    refine ⟨hstOk, ?_⟩
    r2_steps
    rw [show (33544 : BitVec 64) = 33544#64 from rfl]
    let st3 : RtC0State := { st2 with hdr := { st2.hdr with s_ba_empty := p } }
    have hm3' : (rtC0Inv rt st3 ⋆ lcnfObjMem (mkBaObj p 0#32 0 []) ⋆ R)
        (storeMem m2 i64 (rt + 33544#64) p) := by
      rw [Std.ExtHashMap.sep_emp] at hstMem
      exact sep_cast hstMem (by ac_rfl)
    have hpm12 : st2.PreservesMeta st := hpr1.trans hpr2
    refine hk p st3 (storeMem m2 i64 (rt + 33544#64) p) hp0 hp8
      ⟨hpm12.1, hpm12.2.1, hpm12.2.2.2.1, hpm12.2.2.2.2.1,
        hpm12.2.2.2.2.2.1, hpm12.2.2.2.2.2.2.1, hpm12.2.2.2.2.2.2.2.1,
        hpm12.2.2.2.2.2.2.2.2⟩ ?_ rfl hm3'
    change st2.rem ≤ st.rem; omega

theorem lcnf_ba_mk_empty_wp :
    ∀ xs m Q X,
      lcnfBaMkEmptySpec xs m Q X → Func.wp rtR2Env lcnf_ba_mk_empty_body xs m Q X := by
  intro ⟨rt, cap, ⟨⟩⟩ m Q X hSpec
  dsimp only [Func.wp, lcnf_ba_mk_empty_body, lcnfBaMkEmptySpec] at hSpec ⊢
  change LeanQbe.T.wp _ _ _ _ _
  let c64 : BitVec 64 := if (cap &&& 1#64) ≠ 0#64 then cap >>> 1#64 else 0#64
  apply wp_join_group (P := fun (xs : Tup Val [i64]) m' => match xs with
    | (x, PUnit.unit) => m' = m ∧ x = c64)
  · intro _ ⟨x, ⟨⟩⟩ m' ⟨rfl, hx⟩
    subst hx
    change LeanQbe.T.wp _ _ _ _ _
    have hcEq : c64.toNat = if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0 := by
      dsimp only [c64]; split <;> simp
    by_cases hvalid : (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) ≤ baMaxCap
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hvalid)] at hSpec
      rcases hSpec with ⟨st, R, hav, hm, hk⟩
      r2_call rtR2Env_r2_alloc_sarray
      dsimp only [r2AllocSarraySpec, vals, Tup.map, Arg.val]
      have h0c : (0 : BitVec 64).toNat ≤ c64.toNat ∧ c64.toNat ≤ baMaxCap := by
        rw [hcEq]; exact ⟨Nat.zero_le _, hvalid⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0c)]
      refine ⟨st, R, by rw [hcEq]; exact hav, hm, fun p st' m1 hp0 hp8 hpr hrem _ hm1 => ?_⟩
      r2_steps
      have hmObj : (rtC0Inv rt st' ⋆
          lcnfObjMem (mkBaObj p 1#32 (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) []) ⋆
          R) m1 := by
        have hpParts : (cell64 p baHeaderWord ⋆
            cell64 (p + 8#64) (BitVec.ofNat 64 ([] : List UInt8).length) ⋆
            cell64 (p + 16#64) (BitVec.ofNat 64
              (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0)) ⋆
            bytes (p + 24#64) [] ⋆
            region (p + 24#64 + BitVec.ofNat 64 ([] : List UInt8).length)
              (baAllocBytes (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) - 24 -
                ([] : List UInt8).length) ⋆
            (rtC0Inv rt st' ⋆ R)) m1 := by
          rw [List.length_nil, Nat.sub_zero, bytes_nil_eq, Std.ExtHashMap.sep_emp]
          rw [← hcEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [show (0#64 : BitVec 64) = (0 : BitVec 64) from rfl]
          rw [show p + 24#64 + (0 : BitVec 64) = p + 24#64 by simp]
          exact sep_cast hm1 (by ac_rfl)
        exact sep_cast (mkBaObj_mem_of_parts hpParts) (by ac_rfl)
      have hcan : BaCanon
          (mkBaObj p 1#32 (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) []) :=
        mkBaObj_canon hp0 hp8 (by decide) (by simp) hvalid
      exact hk p st' m1 hp0 hp8 hpr hrem hcan hmObj
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hvalid)] at hSpec
      r2_call rtR2Env_r2_alloc_sarray
      dsimp only [r2AllocSarraySpec, vals, Tup.map, Arg.val]
      have hnot : ¬ ((0 : BitVec 64).toNat ≤ c64.toNat ∧ c64.toNat ≤ baMaxCap) := by
        rw [hcEq]; intro ⟨_, hle⟩; exact hvalid hle
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)]
      exact hSpec
  · intro J hJ
    r2_steps
    · apply hJ
      refine ⟨rfl, ?_⟩
      dsimp only [c64]
      have hne : (cap &&& 1#64) ≠ 0#64 := by assumption
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      rfl
    · apply hJ
      refine ⟨rfl, ?_⟩
      have heq : (cap &&& 1#64) = 0#64 := by assumption
      simp [c64, heq]

/-! ## 4. `lcnf_ba_mk`, `lcnf_ba_get`, `lcnf_ba_set`, `lcnf_ba_push`, `lcnf_ba_cmp_op` -/

theorem lcnf_ba_mk_wp :
    ∀ xs m Q X, lcnfBaMkSpec xs m Q X → Func.wp rtR2Env lcnf_ba_mk_body xs m Q X := by
  intro ⟨rt, arr, ⟨⟩⟩ m Q X
    ⟨st, arrObj, objs, R, harrMem, haddr, hcanon, hscal, hwfObjs, hrc1Ok, hav, hm, hk⟩
  obtain ⟨k, hklen, hobjk⟩ := List.getElem_of_mem harrMem
  subst hobjk
  let rest := lcnfHeap (objs.eraseIdx k)
  have hmSplit : (rtC0Inv rt st ⋆ lcnfObjMem objs[k] ⋆ (rest ⋆ R)) m := by
    have hf := lcnfHeap_focus objs hklen
    have he := lcnfHeap_eraseIdx objs (i := k)
    rw [hf, ← he] at hm
    exact sep_cast hm (by ac_rfl)
  dsimp only [Func.wp, lcnf_ba_mk_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_step
  have hloadSz := arr_load_sz_mid hcanon hmSplit
  rw [haddr] at hloadSz
  apply wp_load_of hloadSz
  let n := objs[k].fields.length
  have hnMax : n ≤ baMaxCap := by
    have := hcanon.2.2.2.2.2.2.1
    have := hcanon.2.2.2.2.2.2.2
    unfold baMaxCap arrMaxCap at *; omega
  have hn64 : n < 2 ^ 64 := by unfold baMaxCap at hnMax; omega
  have hnTo : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  r2_call rtR2Env_r2_alloc_sarray
  dsimp only [r2AllocSarraySpec, vals, Tup.map, Arg.val]
  have hnn : (BitVec.ofNat 64 n).toNat ≤ (BitVec.ofNat 64 n).toNat ∧
      (BitVec.ofNat 64 n).toNat ≤ baMaxCap := by rw [hnTo]; exact ⟨Nat.le_refl _, hnMax⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true hnn)]
  refine ⟨st, lcnfObjMem objs[k] ⋆ (rest ⋆ R), by rw [hnTo]; exact hav,
    sep_cast hmSplit (by ac_rfl), fun ba st1 m1 hba0 hba8 hpr1 hrem1 _ hm1 => ?_⟩
  rw [hnTo] at hm1
  change LeanQbe.T.wp _ _ _ _ _
  let Inv : Tup Val [i64] → Mem 64 → Prop := fun xs m' => match xs with
    | (iv, PUnit.unit) =>
      ∃ i : Nat, i ≤ n ∧ iv = BitVec.ofNat 64 i ∧
        (bytes (ba + 24#64)
            ((objs[k].fields.take i).map (fun elem => UInt8.ofNat (elem >>> 1#64).toNat)) ⋆
          region (ba + 24#64 + BitVec.ofNat 64 i) (baAllocBytes n - 24 - i) ⋆
          cell64 ba baHeaderWord ⋆
          cell64 (ba + 8#64) (BitVec.ofNat 64 n) ⋆
          cell64 (ba + 16#64) (BitVec.ofNat 64 n) ⋆
          rtC0Inv rt st1 ⋆ lcnfObjMem objs[k] ⋆ (rest ⋆ R)) m'
  let μ : Tup Val [i64] → Mem 64 → Nat := fun xs _ => match xs with
    | (iv, PUnit.unit) => n - iv.toNat
  apply wp_loop_inv Inv μ
  · intro J hJ
    apply hJ
    refine ⟨0, Nat.zero_le _, rfl, ?_⟩
    simp only [List.take_zero, List.map_nil, bytes_nil_eq, Std.ExtHashMap.emp_sep, Nat.sub_zero,
      show ba + 24#64 + BitVec.ofNat 64 0 = ba + 24#64 by simp]
    exact sep_cast hm1 (by ac_rfl)
  · intro J ⟨iv, ⟨⟩⟩ m' ⟨i, hle, hiv, hmLoop⟩ hRec
    subst hiv
    have hi64 : i < 2 ^ 64 := lt_of_le_of_lt hle hn64
    have hiTo : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    by_cases hlt : i < n
    · r2_steps
      · have hloadElem : loadVal m' i64 (arr + 24#64 + 8#64 * BitVec.ofNat 64 i) =
            some objs[k].fields[i] := by
          have hl := arr_load_elem_mid hcanon (i := BitVec.ofNat 64 i)
            (A := bytes (ba + 24#64)
              ((objs[k].fields.take i).map (fun elem => UInt8.ofNat (elem >>> 1#64).toNat)) ⋆
              region (ba + 24#64 + BitVec.ofNat 64 i) (baAllocBytes n - 24 - i) ⋆
              cell64 ba baHeaderWord ⋆ cell64 (ba + 8#64) (BitVec.ofNat 64 n) ⋆
              cell64 (ba + 16#64) (BitVec.ofNat 64 n) ⋆ rtC0Inv rt st1)
            (R := rest ⋆ R) (by rw [hiTo]; exact hlt) (sep_cast hmLoop (by ac_rfl))
          simpa [haddr, hiTo] using hl
        apply wp_load_of hloadElem
        r2_step
        have hremPos : 0 < baAllocBytes n - 24 - i := by
          have := baAllocBytes_ge n; omega
        have hremFit : baAllocBytes n - 24 - i ≤ 2 ^ 64 := by
          unfold baMaxCap at hnMax; unfold baAllocBytes align8; omega
        have hmReg : (region (ba + 24#64 + BitVec.ofNat 64 i) (baAllocBytes n - 24 - i) ⋆
            (bytes (ba + 24#64)
              ((objs[k].fields.take i).map (fun elem => UInt8.ofNat (elem >>> 1#64).toNat)) ⋆
            cell64 ba baHeaderWord ⋆ cell64 (ba + 8#64) (BitVec.ofNat 64 n) ⋆
            cell64 (ba + 16#64) (BitVec.ofNat 64 n) ⋆
            rtC0Inv rt st1 ⋆ lcnfObjMem objs[k] ⋆ (rest ⋆ R))) m' := by
          have hregAc : ba + (BitVec.ofNat 64 i + 24#64) = ba + 24#64 + BitVec.ofNat 64 i :=
            by ac_rfl
          exact sep_cast hmLoop (by rw [← hregAc]; ac_rfl)
        let elem := objs[k].fields[i]
        have hst := region_pop_store_byte (BitVec.truncate 8 (elem >>> 1#64)) hremPos hremFit hmReg
        apply wp_store_sep hst
        intro m2 hm2
        r2_steps
        have hbvAdd : BitVec.ofNat 64 i + (1 : BitVec 64) = BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq; simp
        rw [hbvAdd]
        apply hRec (BitVec.ofNat 64 (i + 1), ()) m2
        · dsimp only [μ]
          have hi1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          rw [hiTo, hi1]; omega
        · refine ⟨i + 1, hlt, rfl, ?_⟩
          have htake : objs[k].fields.take (i + 1) = objs[k].fields.take i ++ [elem] :=
            List.take_succ_eq_append_getElem hlt
          rw [htake, List.map_append, List.map_singleton]
          rw [uint8_ofNat_truncate8] at hm2
          have hlenP : ((objs[k].fields.take i).map
              (fun elem => UInt8.ofNat (elem >>> 1#64).toNat)).length = i := by
            simp [List.length_take]; omega
          have hlenFit : ((objs[k].fields.take i).map
              (fun elem => UInt8.ofNat (elem >>> 1#64).toNat)).length +
              [UInt8.ofNat (elem >>> 1#64).toNat].length ≤ 2 ^ 64 := by
            rw [hlenP]; simp; omega
          rw [bytes_append (ba + 24#64) _ _ hlenFit, hlenP,
            show baAllocBytes n - 24 - (i + 1) = baAllocBytes n - 24 - i - 1 by omega]
          have ha2 : ba + 24#64 + BitVec.ofNat 64 i + 1#64 =
              ba + 24#64 + BitVec.ofNat 64 (i + 1) := by
            rw [BitVec.add_assoc, show (1#64 : BitVec 64) = (1 : BitVec 64) from rfl, hbvAdd]
          rw [ha2] at hm2
          exact sep_cast hm2 (by ac_rfl)
    · have hiEq : i = n := by omega
      subst hiEq
      r2_steps
      let data := objs[k].fields.map (fun elem => UInt8.ofNat (elem >>> 1#64).toNat)
      let baObj := mkBaObj ba 1#32 n data
      have hlenD : data.length = n := by simp [data, n]
      have hmObj : (lcnfObjMem baObj ⋆ rtC0Inv rt st1 ⋆ lcnfObjMem objs[k] ⋆ (rest ⋆ R)) m' := by
        have hparts : (cell64 ba baHeaderWord ⋆
            cell64 (ba + 8#64) (BitVec.ofNat 64 data.length) ⋆
            cell64 (ba + 16#64) (BitVec.ofNat 64 n) ⋆
            bytes (ba + 24#64) data ⋆
            region (ba + 24#64 + BitVec.ofNat 64 data.length)
              (baAllocBytes n - 24 - data.length) ⋆
            (rtC0Inv rt st1 ⋆ lcnfObjMem objs[k] ⋆ (rest ⋆ R))) m' := by
          dsimp only [data] at hmLoop ⊢
          rw [hlenD, ← List.take_length (l := objs[k].fields)]
          exact sep_cast hmLoop (by ac_rfl)
        exact sep_cast (mkBaObj_mem_of_parts hparts) (by ac_rfl)
      have hmDec : (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ (lcnfObjMem baObj ⋆ R)) m' := by
        have hf := lcnfHeap_focus objs hklen
        have he := lcnfHeap_eraseIdx objs (i := k)
        rw [hf, ← he]
        exact sep_cast hmObj (by ac_rfl)
      r2_call rtR2Env_r2_dec_obj
      dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
      have hand0 : (arr &&& 1#64) = 0#64 := bv64_and1_zero_of_mod8 (haddr ▸ hcanon.2.1)
      have hnotOr : ¬ (arr = 0#64 ∨ (arr &&& 1#64) ≠ 0#64) := by
        simp [haddr ▸ hcanon.1, hand0]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnotOr)]
      refine ⟨st1, objs, lcnfObjMem baObj ⋆ R, ⟨objs[k], harrMem, haddr, fun h1 => ?_⟩,
        hwfObjs, hmDec, fun st2 objs' m2 hpr2 hrem2 hdec hm2 => ?_⟩
      · have := hrc1Ok h1
        rw [RtC0State.workCap_eq_of_preservesMeta hpr1]; exact this
      · r2_steps
        have hbc : BaCanon baObj :=
          mkBaObj_canon hba0 hba8 (by decide) (by rw [hlenD]; exact Nat.le_refl _) hnMax
        exact hk ba st2 objs' m2 hba0 hba8 (hpr1.trans hpr2) (by omega) hbc hdec
          (sep_cast hm2 (by ac_rfl))

theorem lcnf_ba_get_wp :
    ∀ xs m Q X, lcnfBaGetSpec xs m Q X → Func.wp rtR2Env lcnf_ba_get_body xs m Q X := by
  intro ⟨_rt, ba, idx, unboxed, ⟨⟩⟩ m Q X ⟨baObj, R, haddr, hcanon, hm, hPost⟩
  subst haddr
  have hmS := lcnfObjMem_sarray_elim hcanon hm
  have hsz64 := hcanon.arrSize_lt_64
  have hlenEq : baObj.scalarData.length = baObj.arrSize := hcanon.2.2.2.2.2.2.1.symm
  have hszTo : (BitVec.ofNat 64 baObj.arrSize).toNat = baObj.arrSize := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64]
  dsimp only [Func.wp, lcnf_ba_get_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_step
  apply wp_load_of (ba_load_sz hcanon hm)
  let iNat :=
    if unboxed ≠ 0#64 then idx.toNat
    else if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
    else baObj.scalarData.length
  let iBv : BitVec 64 :=
    if unboxed ≠ 0#64 then idx
    else if (idx &&& 1#64) ≠ 0#64 then idx >>> 1#64
    else BitVec.ofNat 64 baObj.arrSize
  have hiTo : iBv.toNat = iNat := by
    dsimp only [iBv, iNat]
    split
    · simp
    · split <;> simp [hszTo, hlenEq]
  apply wp_join_group (P := fun (xs : Tup Val [i64]) m' => match xs with
    | (iv, PUnit.unit) => m' = m ∧ iv = iBv)
  · intro _ ⟨iv, ⟨⟩⟩ m' ⟨hmEq, hiv⟩
    subst hmEq; subst hiv
    change LeanQbe.T.wp _ _ _ _ _
    r2_step
    by_cases hlt : iNat < baObj.scalarData.length
    · have hmBytes : (bytes (baObj.addr + 24#64) baObj.scalarData ⋆
          (cell64 baObj.addr baObj.header ⋆
            cell64 (baObj.addr + 8#64) (BitVec.ofNat 64 baObj.arrSize) ⋆
            cell64 (baObj.addr + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
            region (baObj.addr + BitVec.ofNat 64 (24 + baObj.scalarData.length))
              (baAllocBytes baObj.cap - (24 + baObj.scalarData.length)) ⋆ R)) m' :=
        sep_cast hmS (by ac_rfl)
      have hfit : baObj.scalarData.length ≤ 2 ^ 64 := by rw [hlenEq]; exact Nat.le_of_lt hsz64
      r2_steps
      r2_step
      apply wp_load_of (r2_c0_load_bytes_add24 hmBytes (by rw [hiTo]; exact hlt) hfit)
      r2_steps
      have hzext : BitVec.setWidth 64 (BitVec.ofNat 8 baObj.scalarData[iBv.toNat].toNat) =
          baGetVal baObj.scalarData idx unboxed := by
        have hlt' : (if unboxed ≠ 0#64 then BitVec.toNat idx
            else if idx &&& 1#64 ≠ 0#64 then (idx >>> 1).toNat else baObj.scalarData.length) <
            baObj.scalarData.length := hlt
        have hiEq : iBv.toNat = (if unboxed ≠ 0#64 then BitVec.toNat idx
            else if idx &&& 1#64 ≠ 0#64 then (idx >>> 1).toNat else baObj.scalarData.length) :=
          hiTo
        rw [baGetVal, dite_eq_left hlt']
        simp only [← hiEq]
        apply BitVec.eq_of_toNat_eq
        have hlt8 : baObj.scalarData[iBv.toNat].toNat < 2 ^ 8 :=
          baObj.scalarData[iBv.toNat].toBitVec.isLt
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega
      rwa [hzext]
    · r2_steps
      have hval0 : (0 : BitVec 64) = baGetVal baObj.scalarData idx unboxed := by
        have hnlt' : ¬ (if unboxed ≠ 0#64 then BitVec.toNat idx
            else if idx &&& 1#64 ≠ 0#64 then (idx >>> 1).toNat else baObj.scalarData.length) <
            baObj.scalarData.length := hlt
        rw [baGetVal, dite_eq_right hnlt']
        rfl
      rwa [hval0]
  · intro Jout hJout
    r2_steps
    · apply hJout
      refine ⟨rfl, ?_⟩
      have hu : unboxed ≠ 0#64 := fun h => (by assumption : ¬ unboxed = 0) h
      simp [iBv, hu]
    · apply hJout
      refine ⟨rfl, ?_⟩
      have hu : unboxed = 0#64 := by assumption
      have hi1 : (idx &&& 1#64) ≠ 0#64 := by assumption
      simp [iBv, hu, hi1]
    · apply hJout
      refine ⟨rfl, ?_⟩
      have hu : unboxed = 0#64 := by assumption
      have hi0 : (idx &&& 1#64) = 0#64 := by assumption
      simp [iBv, hu, hi0]

theorem lcnf_ba_set_wp :
    ∀ xs m Q X, lcnfBaSetSpec xs m Q X → Func.wp rtR2Env lcnf_ba_set_body xs m Q X := by
  intro ⟨rt, ba, idx, b, unboxed, ⟨⟩⟩ m Q X ⟨st, baObj, R, haddr, hcanon, hm, hPost⟩
  subst haddr
  have hsz64 := hcanon.arrSize_lt_64
  have hlenEq : baObj.scalarData.length = baObj.arrSize := hcanon.2.2.2.2.2.2.1.symm
  have hszTo : (BitVec.ofNat 64 baObj.arrSize).toNat = baObj.arrSize := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64]
  dsimp only [Func.wp, lcnf_ba_set_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_step
  apply wp_load_of (ba_load_sz_mid hcanon hm)
  let iNat :=
    if unboxed ≠ 0#64 then idx.toNat
    else if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat
    else baObj.arrSize
  let iBv : BitVec 64 :=
    if unboxed ≠ 0#64 then idx
    else if (idx &&& 1#64) ≠ 0#64 then idx >>> 1#64
    else BitVec.ofNat 64 baObj.arrSize
  have hiTo : iBv.toNat = iNat := by
    dsimp only [iBv, iNat]
    split
    · simp
    · split <;> simp [hszTo]
  apply wp_join_group (P := fun (xs : Tup Val [i64]) m' => match xs with
    | (iv, PUnit.unit) => m' = m ∧ iv = iBv)
  · intro _ ⟨iv, ⟨⟩⟩ m' ⟨hmEq, hiv⟩
    subst hmEq; subst hiv
    change LeanQbe.T.wp _ _ _ _ _
    by_cases hoob : iNat ≥ baObj.arrSize
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hoob)] at hPost
      r2_steps
      exact hPost
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hoob)] at hPost
      rcases hPost with ⟨hav, hk⟩
      have hlt : iNat < baObj.scalarData.length := by rw [hlenEq]; omega
      r2_steps
      r2_call rtR2Env_r2_ensure_excl_ba
      dsimp only [r2EnsureExclBaSpec, vals, Tup.map, Arg.val]
      refine ⟨st, baObj, R, rfl, hcanon, hm, ?_⟩
      have hnp : ¬ ((0 : BitVec 64) ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧
          baMaxCap ≤ baObj.cap) := by simp
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnp)]
      have hcapEq : baEnsureCap baObj.arrSize baObj.cap (0 : BitVec 64) = baObj.cap := by
        simp [baEnsureCap]
      rw [hcapEq]
      refine ⟨fun hne => hav (by rcases hne with h1 | ⟨h0, _⟩; exact h1; exact absurd rfl h0), ?_⟩
      intro r st' m1 hr0 hr8 hpr1 hrem1 hfp1 _ _ hm1
      change LeanQbe.T.wp _ _ _ _ _
      r2_step
      let oldKeep :=
        if baObj.rc = 1#32 then emp else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))
      let rPre := mkBaObj r 1#32 baObj.cap baObj.scalarData
      have hcanPre : BaCanon rPre :=
        mkBaObj_canon hr0 hr8 (by decide) (by rw [hlenEq]; exact hcanon.2.2.2.2.2.2.2.1)
          hcanon.2.2.2.2.2.2.2.2
      have hm1' : (lcnfObjMem rPre ⋆ (rtC0Inv rt st' ⋆ oldKeep ⋆ R)) m1 := by
        dsimp only [rPre, oldKeep]
        exact sep_cast hm1 (by ac_rfl)
      have hm1S := lcnfObjMem_sarray_elim hcanPre hm1'
      have hmBytes : (bytes (r + 24#64) baObj.scalarData ⋆
          (cell64 r rPre.header ⋆
            cell64 (r + 8#64) (BitVec.ofNat 64 rPre.arrSize) ⋆
            cell64 (r + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
            region (r + BitVec.ofNat 64 (24 + baObj.scalarData.length))
              (baAllocBytes baObj.cap - (24 + baObj.scalarData.length)) ⋆
            rtC0Inv rt st' ⋆ oldKeep ⋆ R)) m1 := sep_cast hm1S (by ac_rfl)
      have hfit : baObj.scalarData.length ≤ 2 ^ 64 := by
        rw [hlenEq]; exact Nat.le_of_lt hsz64
      have hst := r2_c0_store_bytes_add24 (BitVec.truncate 8 b) hmBytes
        (by rw [hiTo]; exact hlt) hfit
      apply wp_store_sep hst
      intro m2 hm2
      r2_steps
      rw [hiTo, uint8_ofNat_truncate8] at hm2
      let newData := baObj.scalarData.set iNat (UInt8.ofNat b.toNat)
      let rObj := mkBaObj r 1#32 baObj.cap newData
      have hlenNew : newData.length = baObj.scalarData.length := by simp [newData]
      have hcanNew : BaCanon rObj :=
        mkBaObj_canon hr0 hr8 (by decide)
          (by rw [hlenNew, hlenEq]; exact hcanon.2.2.2.2.2.2.2.1) hcanon.2.2.2.2.2.2.2.2
      have hm2Obj : (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ R) m2 := by
        have hrPre : rPre.arrSize = newData.length := by simp [rPre, mkBaObj, hlenNew]
        have hrHdr : rPre.header = baHeaderWord := mkBaObj_header r baObj.cap baObj.scalarData
        rw [hrPre, hrHdr, ← hlenNew] at hm2
        have hparts : (cell64 r baHeaderWord ⋆
            cell64 (r + 8#64) (BitVec.ofNat 64 newData.length) ⋆
            cell64 (r + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
            bytes (r + 24#64) newData ⋆
            region (r + 24#64 + BitVec.ofNat 64 newData.length)
              (baAllocBytes baObj.cap - 24 - newData.length) ⋆
            (rtC0Inv rt st' ⋆ oldKeep ⋆ R)) m2 := by
          rw [ptr_add_nat_r2, show baAllocBytes baObj.cap - 24 - newData.length =
            baAllocBytes baObj.cap - (24 + newData.length) by omega]
          exact sep_cast hm2 (by ac_rfl)
        exact sep_cast (mkBaObj_mem_of_parts hparts) (by ac_rfl)
      exact hk r st' m2 hr0 hr8 hpr1 hrem1 (fun h1 => hfp1 h1 (Or.inl rfl)) hcanNew hm2Obj
  · intro Jout hJout
    r2_steps
    · apply hJout
      refine ⟨rfl, ?_⟩
      have hu : unboxed ≠ 0#64 := fun h => (by assumption : ¬ unboxed = 0) h
      simp [iBv, hu]
    · apply hJout
      refine ⟨rfl, ?_⟩
      have hu : unboxed = 0#64 := by assumption
      have hi1 : (idx &&& 1#64) ≠ 0#64 := by assumption
      simp [iBv, hu, hi1]
    · apply hJout
      refine ⟨rfl, ?_⟩
      have hu : unboxed = 0#64 := by assumption
      have hi0 : (idx &&& 1#64) = 0#64 := by assumption
      simp [iBv, hu, hi0]

theorem lcnf_ba_push_wp :
    ∀ xs m Q X, lcnfBaPushSpec xs m Q X → Func.wp rtR2Env lcnf_ba_push_body xs m Q X := by
  intro ⟨rt, ba, b, ⟨⟩⟩ m Q X ⟨st, baObj, R, haddr, hcanon, hm, hPost⟩
  subst haddr
  have hsz64 := hcanon.arrSize_lt_64
  have hlenEq : baObj.scalarData.length = baObj.arrSize := hcanon.2.2.2.2.2.2.1.symm
  dsimp only [Func.wp, lcnf_ba_push_body]
  change LeanQbe.T.wp _ _ _ _ _
  r2_call rtR2Env_r2_ensure_excl_ba
  dsimp only [r2EnsureExclBaSpec, vals, Tup.map, Arg.val]
  refine ⟨st, baObj, R, rfl, hcanon, hm, ?_⟩
  by_cases hpanic : baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hpanic)] at hPost
    have hp1 : (1 : BitVec 64) ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap :=
      ⟨by decide, hpanic⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hp1)]
    exact hPost
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hpanic)] at hPost
    have hp1 : ¬ ((1 : BitVec 64) ≠ 0#64 ∧ baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap) :=
      by intro ⟨_, h⟩; exact hpanic h
    rw [ite_eq_right_of_eq_false _ _ (eq_false hp1)]
    rcases hPost with ⟨hav, hk⟩
    refine ⟨fun hne => hav (by rcases hne with h1 | ⟨_, hge⟩; exact Or.inl h1; exact Or.inr hge),
      fun r st' m1 hr0 hr8 hpr1 hrem1 hfp1 hltCap hmaxCap hm1 => ?_⟩
    have harsLt : baObj.arrSize < baEnsureCap baObj.arrSize baObj.cap 1#64 := hltCap (by decide)
    let newCap := baEnsureCap baObj.arrSize baObj.cap 1#64
    let rPre := mkBaObj r 1#32 newCap baObj.scalarData
    have hcanPre : BaCanon rPre :=
      mkBaObj_canon hr0 hr8 (by decide) (by rw [hlenEq]; exact le_of_lt harsLt) hmaxCap
    let oldKeep :=
      if baObj.rc = 1#32 then emp else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))
    have hm1' : (lcnfObjMem rPre ⋆ (rtC0Inv rt st' ⋆ oldKeep ⋆ R)) m1 := by
      dsimp only [rPre, newCap, oldKeep]
      rw [show (1 : BitVec 64) = 1#64 from rfl] at hm1
      exact sep_cast hm1 (by ac_rfl)
    have hm1S := lcnfObjMem_sarray_elim hcanPre hm1'
    have hAddrPre : rPre.addr = r := rfl
    have hSizePre : rPre.arrSize = baObj.arrSize := by simp [rPre, mkBaObj, hlenEq]
    have hCapPre : rPre.cap = newCap := rfl
    have hDataPre : rPre.scalarData = baObj.scalarData := rfl
    rw [hAddrPre, hSizePre, hCapPre, hDataPre] at hm1S
    change LeanQbe.T.wp _ _ _ _ _
    r2_step
    have hloadR : loadVal m1 i64 (r + 8#64) = some (BitVec.ofNat 64 baObj.arrSize) := by
      exact r2_c0_load_cell64_add8 (a := r)
        (R := cell64 r rPre.header ⋆ cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
          bytes (r + 24#64) baObj.scalarData ⋆
          region (r + BitVec.ofNat 64 (24 + baObj.scalarData.length))
            (baAllocBytes newCap - (24 + baObj.scalarData.length)) ⋆
          rtC0Inv rt st' ⋆ oldKeep ⋆ R) (sep_cast hm1S (by ac_rfl))
    apply wp_load_of hloadR
    r2_step
    have hremPos : 0 < baAllocBytes newCap - (24 + baObj.scalarData.length) := by
      rw [show (1 : BitVec 64) = 1#64 from rfl] at *
      have := baAllocBytes_ge newCap; unfold baAllocBytes align8 at *; rw [hlenEq]; omega
    have hremFit : baAllocBytes newCap - (24 + baObj.scalarData.length) ≤ 2 ^ 64 := by
      rw [show (1 : BitVec 64) = 1#64 from rfl] at *
      unfold baMaxCap at hmaxCap; unfold baAllocBytes align8; omega
    have hmReg : (region (r + BitVec.ofNat 64 (24 + baObj.scalarData.length))
          (baAllocBytes newCap - (24 + baObj.scalarData.length)) ⋆
        (cell64 r rPre.header ⋆
          cell64 (r + 8#64) (BitVec.ofNat 64 baObj.arrSize) ⋆
          cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
          bytes (r + 24#64) baObj.scalarData ⋆
          rtC0Inv rt st' ⋆ oldKeep ⋆ R)) m1 :=
      sep_cast hm1S (by ac_rfl)
    have hstB := region_pop_store_byte (BitVec.truncate 8 b) hremPos hremFit hmReg
    have hptrEq : r + 24#64 + BitVec.ofNat 64 baObj.arrSize =
        r + BitVec.ofNat 64 (24 + baObj.scalarData.length) := by
      rw [← hlenEq, ptr_add_nat_r2]
    rw [← hptrEq] at hstB
    apply wp_store_sep hstB
    intro m2 hm2
    r2_step
    have hmCell8 : (cell64 (r + 8#64) (BitVec.ofNat 64 baObj.arrSize) ⋆
        (cell64 r rPre.header ⋆
          cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
          bytes (r + 24#64) baObj.scalarData ⋆
          bytes (r + 24#64 + BitVec.ofNat 64 baObj.arrSize)
            [UInt8.ofNat (BitVec.truncate 8 b).toNat] ⋆
          region (r + 24#64 + BitVec.ofNat 64 baObj.arrSize + 1#64)
            (baAllocBytes newCap - (24 + baObj.scalarData.length) - 1) ⋆
          rtC0Inv rt st' ⋆ oldKeep ⋆ R)) m2 := sep_cast hm2 (by ac_rfl)
    have hstSz := r2_c0_store_cell64_add8 (BitVec.ofNat 64 baObj.arrSize + 1#64) hmCell8
    apply wp_store_sep hstSz
    intro m3 hm3
    r2_steps
    let newData := baObj.scalarData ++ [UInt8.ofNat b.toNat]
    let rObj := mkBaObj r 1#32 newCap newData
    have hlenNew : newData.length = baObj.arrSize + 1 := by simp [newData, hlenEq]
    have hcanNew : BaCanon rObj :=
      mkBaObj_canon hr0 hr8 (by decide) (by rw [hlenNew]; exact harsLt)
        (by rw [show (1 : BitVec 64) = 1#64 from rfl] at hmaxCap; exact hmaxCap)
    have hm3Obj : (rtC0Inv rt st' ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ R) m3 := by
      rw [uint8_ofNat_truncate8] at hm3
      have hlenApp : baObj.scalarData.length + [UInt8.ofNat b.toNat].length ≤ 2 ^ 64 := by
        rw [show (1 : BitVec 64) = 1#64 from rfl] at hmaxCap
        rw [hlenEq]; simp; unfold baMaxCap at hmaxCap; omega
      have hbytes : bytes (r + 24#64) baObj.scalarData ⋆
          bytes (r + 24#64 + BitVec.ofNat 64 baObj.arrSize) [UInt8.ofNat b.toNat] =
          bytes (r + 24#64) newData := by
        rw [← hlenEq, ← bytes_append (r + 24#64) baObj.scalarData [UInt8.ofNat b.toNat] hlenApp]
      have hszInc : BitVec.ofNat 64 baObj.arrSize + 1#64 = BitVec.ofNat 64 newData.length := by
        rw [hlenNew, ← BitVec.ofNat_add]
      have hregLen : baAllocBytes newCap - (24 + baObj.scalarData.length) - 1 =
          baAllocBytes newCap - 24 - newData.length := by rw [hlenNew, hlenEq]; omega
      have hrHdr : rPre.header = baHeaderWord := mkBaObj_header r newCap baObj.scalarData
      have hm3' : (cell64 r baHeaderWord ⋆
          cell64 (r + 8#64) (BitVec.ofNat 64 baObj.arrSize + 1#64) ⋆
          cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
          (bytes (r + 24#64) baObj.scalarData ⋆
            bytes (r + 24#64 + BitVec.ofNat 64 baObj.arrSize) [UInt8.ofNat b.toNat]) ⋆
          region (r + 24#64 + (BitVec.ofNat 64 baObj.arrSize + 1#64))
            (baAllocBytes newCap - (24 + baObj.scalarData.length) - 1) ⋆
          (rtC0Inv rt st' ⋆ oldKeep ⋆ R)) m3 := by
        rw [← hrHdr]
        have hm3a := sep_cast hm3 (by ac_rfl :
          (cell64 (r + 8#64) (BitVec.ofNat 64 baObj.arrSize + 1#64) ⋆
            (cell64 r rPre.header ⋆
              cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
              bytes (r + 24#64) baObj.scalarData ⋆
              bytes (r + 24#64 + BitVec.ofNat 64 baObj.arrSize) [UInt8.ofNat b.toNat] ⋆
              region (r + 24#64 + BitVec.ofNat 64 baObj.arrSize + 1#64)
                (baAllocBytes newCap - (24 + baObj.scalarData.length) - 1) ⋆
              rtC0Inv rt st' ⋆ oldKeep ⋆ R)) =
          (cell64 r rPre.header ⋆
            cell64 (r + 8#64) (BitVec.ofNat 64 baObj.arrSize + 1#64) ⋆
            cell64 (r + 16#64) (BitVec.ofNat 64 newCap) ⋆
            (bytes (r + 24#64) baObj.scalarData ⋆
              bytes (r + 24#64 + BitVec.ofNat 64 baObj.arrSize) [UInt8.ofNat b.toNat]) ⋆
            region (r + 24#64 + BitVec.ofNat 64 baObj.arrSize + 1#64)
              (baAllocBytes newCap - (24 + baObj.scalarData.length) - 1) ⋆
            (rtC0Inv rt st' ⋆ oldKeep ⋆ R)))
        rw [BitVec.add_assoc (r + 24#64)] at hm3a
        exact hm3a
      rw [hszInc, hbytes, hregLen] at hm3'
      exact sep_cast (mkBaObj_mem_of_parts hm3') (by ac_rfl)
    refine hk r st' m3 hr0 hr8 hpr1 hrem1 (fun h1 hlt => hfp1 h1 (Or.inr hlt)) hcanNew hm3Obj

theorem lcnf_ba_cmp_op_wp :
    ∀ xs m Q X,
      lcnfBaCmpOpSpec xs m Q X → Func.wp rtR2Env lcnf_ba_cmp_op_body xs m Q X := by
  intro ⟨_rt, op, a, b, ⟨⟩⟩ m Q X ⟨aObj, bObj, RA, RB, ha, hb, hca, hcb, hma, hmb, hPost⟩
  subst ha hb
  dsimp only [Func.wp, lcnf_ba_cmp_op_body]
  change LeanQbe.T.wp _ _ _ _ _
  by_cases hab : aObj.addr = bObj.addr
  · r2_steps
    · have hop0 : op = 0#64 := by assumption
      simpa [baCmpOpVal, hab, hop0] using hPost
    · have hop0 : op ≠ 0#64 := by assumption
      have hop1 : op = 1#64 := by assumption
      simpa [baCmpOpVal, hab, hop0, hop1] using hPost
    · have hop0 : op ≠ 0#64 := by assumption
      have hop1 : op ≠ 1#64 := by assumption
      simpa [baCmpOpVal, hab, hop0, hop1] using hPost
  · have hlenA : aObj.scalarData.length = aObj.arrSize := hca.2.2.2.2.2.2.1.symm
    have hlenB : bObj.scalarData.length = bObj.arrSize := hcb.2.2.2.2.2.2.1.symm
    have hsa64 := hca.arrSize_lt_64
    have hsb64 := hcb.arrSize_lt_64
    have hlaTo : (BitVec.ofNat 64 aObj.arrSize).toNat = aObj.scalarData.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsa64, hlenA]
    have hlbTo : (BitVec.ofNat 64 bObj.arrSize).toNat = bObj.scalarData.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsb64, hlenB]
    r2_step; r2_step
    r2_step
    apply wp_load_of (ba_load_sz hca hma)
    r2_step
    apply wp_load_of (ba_load_sz hcb hmb)
    apply wp_join_group
      (P := fun _ m' => m' = m ∧ (op = 0#64 → aObj.scalarData.length = bObj.scalarData.length))
    · intro _ ⟨⟩ m' ⟨hmEq, hlenEq0⟩
      subst hmEq
      change LeanQbe.T.wp _ _ _ _ _
      r2_step
      r2_call rtR2Env_r2_cmp_byte_slices
      dsimp only [r2CmpByteSlicesSpec, vals, Tup.map, Arg.val]
      have hmA' : (bytes (aObj.addr + 24#64) aObj.scalarData ⋆
          (cell64 aObj.addr aObj.header ⋆
            cell64 (aObj.addr + 8#64) (BitVec.ofNat 64 aObj.arrSize) ⋆
            cell64 (aObj.addr + 16#64) (BitVec.ofNat 64 aObj.cap) ⋆
            region (aObj.addr + BitVec.ofNat 64 (24 + aObj.scalarData.length))
              (baAllocBytes aObj.cap - (24 + aObj.scalarData.length)) ⋆ RA)) m' :=
        sep_cast (lcnfObjMem_sarray_elim hca (R := RA) hma) (by ac_rfl)
      have hmB' : (bytes (bObj.addr + 24#64) bObj.scalarData ⋆
          (cell64 bObj.addr bObj.header ⋆
            cell64 (bObj.addr + 8#64) (BitVec.ofNat 64 bObj.arrSize) ⋆
            cell64 (bObj.addr + 16#64) (BitVec.ofNat 64 bObj.cap) ⋆
            region (bObj.addr + BitVec.ofNat 64 (24 + bObj.scalarData.length))
              (baAllocBytes bObj.cap - (24 + bObj.scalarData.length)) ⋆ RB)) m' :=
        sep_cast (lcnfObjMem_sarray_elim hcb (R := RB) hmb) (by ac_rfl)
      refine ⟨aObj.scalarData, bObj.scalarData, _, _, hlaTo.symm, hlbTo.symm, hmA', hmB', ?_⟩
      r2_steps
      · have hop0 : op = 0#64 := by assumption
        have hcmp : cmpByteSlices aObj.scalarData bObj.scalarData = 1#64 := by assumption
        simpa [baCmpOpVal, hab, hop0, hlenEq0 hop0, hcmp] using hPost
      · have hop0 : op = 0#64 := by assumption
        have hcmp : cmpByteSlices aObj.scalarData bObj.scalarData ≠ 1#64 := by assumption
        simpa [baCmpOpVal, hab, hop0, hcmp] using hPost
      · have hop0 : op ≠ 0#64 := by assumption
        have hop1 : op = 1#64 := by assumption
        have hcmp : cmpByteSlices aObj.scalarData bObj.scalarData = 0#64 := by assumption
        simpa [baCmpOpVal, hab, hop0, hop1, hcmp] using hPost
      · have hop0 : op ≠ 0#64 := by assumption
        have hop1 : op = 1#64 := by assumption
        have hcmp : cmpByteSlices aObj.scalarData bObj.scalarData ≠ 0#64 := by assumption
        simpa [baCmpOpVal, hab, hop0, hop1, hcmp] using hPost
      · have hop0 : op ≠ 0#64 := by assumption
        have hop1 : op ≠ 1#64 := by assumption
        simpa [baCmpOpVal, hab, hop0, hop1] using hPost
    · intro J hJ
      r2_steps
      · have hop0 : op = 0#64 := by assumption
        have hneLen : BitVec.ofNat 64 aObj.arrSize ≠ BitVec.ofNat 64 bObj.arrSize := by assumption
        have hneNat : aObj.scalarData.length ≠ bObj.scalarData.length := by
          intro h
          apply hneLen
          rw [← hlenA, ← hlenB, h]
        simpa [baCmpOpVal, hab, hop0, hneNat] using hPost
      · have hop0 : op = 0#64 := by assumption
        have heqLen : BitVec.ofNat 64 aObj.arrSize = BitVec.ofNat 64 bObj.arrSize := by assumption
        have hnat : aObj.scalarData.length = bObj.scalarData.length := by
          have := congrArg BitVec.toNat heqLen
          rwa [hlaTo, hlbTo] at this
        exact hJ () m ⟨rfl, fun _ => hnat⟩
      · exact hJ () m ⟨rfl, fun h0 => absurd h0 (by assumption)⟩

end LeanQbe.T.LeanLCNF
