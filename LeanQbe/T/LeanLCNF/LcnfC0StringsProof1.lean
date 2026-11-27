module

public import LeanQbe.T.LeanLCNF.LcnfC0Strings
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProofAlloc
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof2
public import LeanQbe.T.Logic.C0Step
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Strings`, Part 1: Helpers & Core Alloc/Char Ops

Provides `@[c0_load]`/`@[c0_store]` bridge lemmas for String, ListCons, MPZ, and offset-`+32`/
`+24`/`+16`/`+8` layouts, canonical heap elimination/introduction lemmas, and `Func.wp rtR2bEnv`
proofs for the 6 `r2b_*` helper functions (alloc/UTF-8) plus `lcnf_str_alloc` and `lcnf_char_op`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

local macro "r2b_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_steps))
local macro "r2b_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_); try c0_let_simp))

/-! ## 1. Pointer, Byte-Slice, Region, and `@[c0_load]` / `@[c0_store]` Bridges -/

theorem ptr_add_nat_r2b (a : BitVec 64) (m n : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem bv64_add8_add8 (p : BitVec 64) : p + 8#64 + 8#64 = p + 16#64 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem bv64_add8_add8_raw (p : BitVec 64) : p + 8#64 + 8 = p + 16#64 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem bv64_add16_add8 (p : BitVec 64) : p + 16#64 + 8#64 = p + 24#64 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem bv64_add24_add8 (p : BitVec 64) : p + 24#64 + 8#64 = p + 32#64 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

@[c0_load] theorem r2b_c0_load_cell64_add24 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 24#64) v ⋆ R) m) : loadVal m i64 (a + 24#64) = some v :=
  loadVal_cell64 h

@[c0_store] theorem r2b_c0_store_cell64_add24 {a v0 : BitVec 64} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (cell64 (a + 24#64) v0 ⋆ R) m) :
    storeOk m i64 (a + 24#64) ∧ (cell64 (a + 24#64) v ⋆ R) (storeMem m i64 (a + 24#64) v) :=
  store_cell64 v h

@[c0_load] theorem r2b_c0_load_array64_add8_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 8#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 8#64 + 8#64 * i) = some xs[i.toNat] := by
  rw [bv64_8mul_eq_ofNat]
  exact loadVal_array64 hi h

@[c0_store] theorem r2b_c0_store_array64_add8_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (a + 8#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + 8#64 + 8#64 * i) ∧
      (array64 (a + 8#64) (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + 8#64 + 8#64 * i) v) := by
  rw [bv64_8mul_eq_ofNat]
  exact store_array64 v hi h

@[c0_load] theorem r2b_c0_load_array64_add16_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (a + 16#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    loadVal m i64 (a + 16#64 + 8#64 * i) = some xs[i.toNat] := by
  rw [bv64_8mul_eq_ofNat]
  exact loadVal_array64 hi h

@[c0_store] theorem r2b_c0_store_array64_add16_mul8 {a i : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 (a + 16#64) xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + 16#64 + 8#64 * i) ∧
      (array64 (a + 16#64) (xs.set i.toNat v) ⋆ R)
        (storeMem m i64 (a + 16#64 + 8#64 * i) v) := by
  rw [bv64_8mul_eq_ofNat]
  exact store_array64 v hi h

@[c0_load] theorem r2b_c0_load_bytes_add32 {a i : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (bytes (a + 32#64) bs ⋆ R) m)
    (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    loadVal m i8 (a + 32#64 + i) = some (BitVec.ofNat 8 bs[i.toNat].toNat) :=
  r2_c0_load_bytes_bv h hi hlen

@[c0_store] theorem r2b_c0_store_bytes_add32 {a i : BitVec 64} {bs : List UInt8}
    (v : BitVec 8) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes (a + 32#64) bs ⋆ R) m) (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    storeOk m i8 (a + 32#64 + i) ∧
      (bytes (a + 32#64) (bs.set i.toNat (UInt8.ofNat v.toNat)) ⋆ R)
        (storeMem m i8 (a + 32#64 + i) v) :=
  r2_c0_store_bytes_bv v h hi hlen

@[c0_load] theorem r2b_c0_load_bytes_bv_addk {a i k : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (bytes a bs ⋆ R) m)
    (hi : (i + k).toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    loadVal m i8 (a + i + k) = some (BitVec.ofNat 8 bs[(i + k).toNat].toNat) := by
  have ha : a + i + k = a + (i + k) := BitVec.add_assoc a i k
  rw [ha]
  exact r2_c0_load_bytes_bv h hi hlen

@[c0_load] theorem r2b_c0_load_bytes_head {a : BitVec 64} {b : UInt8} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (bytes a (b :: bs) ⋆ R) m)
    (hlen : (b :: bs).length ≤ 2 ^ 64) :
    loadVal m i8 a = some (BitVec.ofNat 8 b.toNat) := by
  have ha : a = a + 0#64 := (BitVec.add_zero a).symm
  rw [ha]
  exact r2_c0_load_bytes_bv (a := a) (i := 0#64) h (by simp) hlen

@[c0_store] theorem r2b_c0_store_bytes_single {a : BitVec 64} {b : UInt8} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (h : (bytes a [b] ⋆ R) m) :
    storeOk m i8 a ∧ (bytes a [UInt8.ofNat v.toNat] ⋆ R) (storeMem m i8 a v) := by
  have ha : a = a + 0#64 := (BitVec.add_zero a).symm
  rw [ha]
  simpa using r2_c0_store_bytes_bv (a := a) (i := 0#64) (bs := [b]) v h (by simp) (by simp)

theorem region_pop_bytes {a : BitVec 64} {rem k : Nat} (hk : k ≤ rem) (hfit : rem ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a rem ⋆ R) m) :
    ∃ bs : List UInt8, bs.length = k ∧
      (bytes a bs ⋆ region (a + BitVec.ofNat 64 k) (rem - k) ⋆ R) m := by
  have hsp : region a rem = region a k ⋆ region (a + BitVec.ofNat 64 k) (rem - k) := by
    conv => lhs; rw [show rem = k + (rem - k) by omega]
    exact region_split (by omega)
  rw [hsp, sep_assoc] at hm
  obtain ⟨m1, m23, rfl, hd1, ⟨bs, hbsLen, hm1⟩, hm23⟩ := hm
  have hbytes : bytes a bs m1 := by rcases hm1 with rfl; simp only [bytes]
  have hm' : (bytes a bs ⋆ (region (a + BitVec.ofNat 64 k) (rem - k) ⋆ R)) (m1.union m23) :=
    ⟨m1, m23, rfl, hd1, hbytes, hm23⟩
  exact ⟨bs, hbsLen, sep_cast hm' (by ac_rfl)⟩

theorem region_to_2cells_rem {p : BitVec 64} {bytes : Nat} (hge : 16 ≤ bytes)
    (hfit : bytes ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region p bytes ⋆ R) m) :
    ∃ w0 w1, (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ region (p + 16#64) (bytes - 16) ⋆ R) m := by
  obtain ⟨w0, hm1⟩ := region_pop_cell64 (by omega) hfit hm
  have hm1' : (region (p + 8#64) (bytes - 8) ⋆ (cell64 p w0 ⋆ R)) m := sep_cast hm1 (by ac_rfl)
  obtain ⟨w1, hm2⟩ := region_pop_cell64 (by omega) (by omega) hm1'
  rw [bv64_add8_add8, show bytes - 8 - 8 = bytes - 16 by omega] at hm2
  exact ⟨w0, w1, sep_cast hm2 (by ac_rfl)⟩

theorem region_to_4cells_rem {p : BitVec 64} {bytes : Nat} (hge : 32 ≤ bytes)
    (hfit : bytes ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region p bytes ⋆ R) m) :
    ∃ w0 w1 w2 w3,
      (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆ cell64 (p + 24#64) w3 ⋆
        region (p + 32#64) (bytes - 32) ⋆ R) m := by
  obtain ⟨w0, w1, w2, hm3⟩ := region_to_3cells_rem (by omega) hfit hm
  have hm3' : (region (p + 24#64) (bytes - 24) ⋆
      (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆ R)) m :=
    sep_cast hm3 (by ac_rfl)
  obtain ⟨w3, hm4⟩ := region_pop_cell64 (by omega) (by omega) hm3'
  rw [bv64_add24_add8, show bytes - 24 - 8 = bytes - 32 by omega] at hm4
  exact ⟨w0, w1, w2, w3, sep_cast hm4 (by ac_rfl)⟩

theorem region_to_array64_sep {a : BitVec 64} {n : Nat} (hfit : 8 * n ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a (8 * n) ⋆ R) m) :
    ∃ xs : List (BitVec 64), xs.length = n ∧ (array64 a xs ⋆ R) m := by
  obtain ⟨m1, m2, rfl, hd, hm1, hm2⟩ := hm
  obtain ⟨xs, hlen, hxs⟩ := region_to_array64 n hfit hm1
  exact ⟨xs, hlen, m1, m2, rfl, hd, hxs, hm2⟩

theorem bytes_to_region {a : BitVec 64} {bs : List UInt8} {m : Mem 64}
    (h : bytes a bs m) : region a bs.length m := by
  rcases h with rfl
  exact ⟨bs, rfl, rfl⟩

/-! ## 2. Arithmetic, Alloc-Size, and Canonical Object Layout Lemmas -/

theorem strAllocBytes_ge (cap : Nat) : 32 + cap ≤ strAllocBytes cap := by
  unfold strAllocBytes align8; omega

theorem strAllocBytes_mod8 (cap : Nat) : strAllocBytes cap % 8 = 0 := by
  unfold strAllocBytes align8; omega

theorem str_sz_mask_toNat (cap : BitVec 64) (hcap : cap.toNat ≤ strMaxCap) :
    ((32 + cap + 7 &&& 18446744073709551608 : BitVec 64)).toNat = strAllocBytes cap.toNat := by
  rw [show (18446744073709551608 : BitVec 64) = 18446744073709551608#64 from rfl,
    bv64_and_not7_eq]
  have hlt : 32 + cap.toNat + 7 < 2 ^ 64 := by unfold strMaxCap at hcap; omega
  have hsum : (32 + cap + 7 : BitVec 64).toNat = 32 + cap.toNat + 7 := by
    simp only [BitVec.toNat_add]
    rw [show (32 : BitVec 64).toNat = 32 from rfl, show (7 : BitVec 64).toNat = 7 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hsum]
  unfold strAllocBytes align8
  omega

theorem mpz_sz_mask_toNat (cap : BitVec 64) (hcap : cap.toNat ≤ 33554429) :
    ((16 : BitVec 64) + 8 * cap).toNat = mpzAllocBytes cap.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  rw [show (8 : BitVec 64).toNat = 8 from rfl, show (16 : BitVec 64).toNat = 16 from rfl]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

theorem lcnfObjMem_string_eq {o : LcnfObj} (h : o.tag = stringTag) :
    lcnfObjMem o =
      cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
        bytes (o.addr + 32#64) o.scalarData ⋆
        region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length))
          (o.totalBytes - (32 + o.scalarData.length)) := by
  unfold lcnfObjMem
  rw [ite_eq_right (by rw [h]; decide), ite_eq_right (by rw [h]; decide),
    ite_eq_right (by rw [h]; decide), ite_eq_left h]

theorem mkStrObj_totalBytes (r : BitVec 64) (rc : BitVec 32) (cap len : Nat)
    (payload : List UInt8) :
    (mkStrObj r rc cap payload len).totalBytes = strAllocBytes cap := by
  unfold LcnfObj.totalBytes mkStrObj strAllocBytes
  simp [stringTag, arrayTag, sarrayTag]

theorem mkStrObj_header (r : BitVec 64) (cap len : Nat) (payload : List UInt8) :
    (mkStrObj r 1#32 cap payload len).header = strHeaderWord := by
  dsimp only [LcnfObj.header, mkStrObj, strHeaderWord, stringTag]
  decide

theorem mkStrObj_mem_of_parts {r : BitVec 64} {cap len : Nat} {payload : List UInt8}
    {m : Mem 64} {R : Mem 64 → Prop} (hcap : cap ≤ strMaxCap)
    (hfit : payload.length + 1 ≤ cap)
    (hm : (cell64 r strHeaderWord ⋆
      cell64 (r + 8#64) (BitVec.ofNat 64 (payload.length + 1)) ⋆
      cell64 (r + 16#64) (BitVec.ofNat 64 cap) ⋆
      cell64 (r + 24#64) (BitVec.ofNat 64 len) ⋆
      bytes (r + 32#64) payload ⋆
      bytes (r + 32#64 + BitVec.ofNat 64 payload.length) [(0 : UInt8)] ⋆
      region (r + 32#64 + BitVec.ofNat 64 payload.length + 1#64)
        (strAllocBytes cap - (32 + payload.length + 1)) ⋆ R) m) :
    (lcnfObjMem (mkStrObj r 1#32 cap payload len) ⋆ R) m := by
  rw [lcnfObjMem_string_eq (by rfl), mkStrObj_header, mkStrObj_totalBytes]
  dsimp only [mkStrObj]
  have hApp := bytes_append (r + 32#64) payload [(0 : UInt8)]
    (by simp only [List.length_singleton]; unfold strMaxCap at hcap; omega)
  have hPos : r + 32#64 + BitVec.ofNat 64 payload.length + 1#64 =
      r + BitVec.ofNat 64 (32 + (payload ++ [(0 : UInt8)]).length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_append, List.length_singleton]
    omega
  have hRem : strAllocBytes cap - (32 + (payload ++ [(0 : UInt8)]).length) =
      strAllocBytes cap - (32 + payload.length + 1) := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [hApp, ← hPos, hRem]
  exact sep_cast hm (by ac_rfl)

theorem strPayload_length {o : LcnfObj} (hc : StrCanon o) :
    (strPayload o).length = o.arrSize - 1 := by
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, hsl, _, _⟩
  unfold strPayload
  rw [List.length_dropLast, hsl]

theorem str_scalarData_eq_payload_nul {o : LcnfObj} (hc : StrCanon o) :
    o.scalarData = strPayload o ++ [(0 : UInt8)] := by
  rcases hc with ⟨_, _, _, _, _, _, ha1, _, _, hsl, hlast, _⟩
  unfold strPayload
  have hne : o.scalarData ≠ [] := by intro h; simp [h] at hsl; omega
  have hspec := List.dropLast_concat_getLast hne
  have hgl : o.scalarData.getLast hne = 0 := by
    have h1 := List.getLast?_eq_some_getLast hne
    rw [hlast] at h1
    injection h1 with h2
    exact h2.symm
  rw [← hgl]
  exact hspec.symm

theorem lcnfObjMem_string_elim {o : LcnfObj} (hc : StrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    (cell64 o.addr o.header ⋆
      cell64 (o.addr + 8#64) (BitVec.ofNat 64 ((strPayload o).length + 1)) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
      bytes (o.addr + 32#64) (strPayload o) ⋆
      bytes (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length) [(0 : UInt8)] ⋆
      region (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64)
        (strAllocBytes o.cap - (32 + (strPayload o).length + 1)) ⋆ R) m := by
  have hplen : (strPayload o).length = o.arrSize - 1 := strPayload_length hc
  have hdata : o.scalarData = strPayload o ++ [(0 : UInt8)] := str_scalarData_eq_payload_nul hc
  rcases hc with ⟨_, _, _, _, _, htag, ha1, hac, hcap, hsl, _, _⟩
  have htb : o.totalBytes = strAllocBytes o.cap := by
    unfold LcnfObj.totalBytes strAllocBytes; simp [htag, stringTag, arrayTag, sarrayTag]
  rw [lcnfObjMem_string_eq htag, htb] at hm
  have hApp := bytes_append (o.addr + 32#64) (strPayload o) [(0 : UInt8)]
    (by simp only [List.length_singleton]; unfold strMaxCap at hcap; omega)
  have hPos : o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64 =
      o.addr + BitVec.ofNat 64 (32 + o.scalarData.length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hplen, hsl]
    omega
  rw [show o.arrSize = (strPayload o).length + 1 by omega] at hm
  rw [← hPos, hsl, show o.arrSize = (strPayload o).length + 1 by omega] at hm
  have hm2 : (cell64 o.addr o.header ⋆
      cell64 (o.addr + 8#64) (BitVec.ofNat 64 ((strPayload o).length + 1)) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
      (bytes (o.addr + 32#64) (strPayload o) ⋆
        bytes (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length) [(0 : UInt8)]) ⋆
      region (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64)
        (strAllocBytes o.cap - (32 + ((strPayload o).length + 1))) ⋆ R) m := by
    rwa [← hApp, ← hdata]
  rw [show 32 + ((strPayload o).length + 1) = 32 + (strPayload o).length + 1 by omega] at hm2
  exact sep_cast hm2 (by ac_rfl)

theorem lcnfObjMem_listCons_eq {o : LcnfObj} (hc : ListConsCanon o) :
    ∃ hd tl, o.fields = [hd, tl] ∧
      lcnfObjMem o =
        cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) hd ⋆ cell64 (o.addr + 16#64) tl := by
  rcases hc with ⟨_, _, _, hcs, ho, htag, hf, hs⟩
  obtain ⟨hd, tl, hft⟩ : ∃ hd tl, o.fields = [hd, tl] := by
    match o.fields, hf with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  refine ⟨hd, tl, hft, ?_⟩
  unfold lcnfObjMem
  rw [ite_eq_right (by rw [htag]; decide), ite_eq_right (by rw [htag]; decide),
    ite_eq_right (by rw [htag]; decide), ite_eq_right (by rw [htag]; decide),
    ite_eq_right (by rw [htag]; decide)]
  dsimp only
  rw [hft, hs, hcs]
  simp only [List.length_cons, List.length_nil, Nat.add_zero, Nat.mul_succ, Nat.mul_zero,
    Nat.add_assoc]
  rw [show 24 - 24 = 0 by decide, region_zero, bytes_nil_eq,
    array64_cons, array64_cons, array64_nil, bv64_add8_add8_raw]
  ext m
  simp only [sep_emp, sep_assoc]

theorem mkListConsObj_header (p : BitVec 64) (hd tl : BitVec 64) :
    (mkListConsObj p 1#32 hd tl).header = listConsHeaderWord := by
  dsimp only [LcnfObj.header, mkListConsObj, listConsHeaderWord, listConsTag]
  decide

theorem mkListConsObj_mem {p hd tl : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0)
    (hm : (cell64 p listConsHeaderWord ⋆ cell64 (p + 8#64) hd ⋆ cell64 (p + 16#64) tl ⋆ R) m) :
    (lcnfObjMem (mkListConsObj p 1#32 hd tl) ⋆ R) m := by
  have hc : ListConsCanon (mkListConsObj p 1#32 hd tl) :=
    mkListConsObj_canon hp0 hp8 (by decide)
  obtain ⟨h1, t1, hft, hmem⟩ := lcnfObjMem_listCons_eq hc
  dsimp only [mkListConsObj] at hft
  injection hft with h_hd hft2
  injection hft2 with h_tl _
  subst h_hd; subst h_tl
  rw [hmem, mkListConsObj_header]
  exact hm

theorem r2b_lcnfObjMem_mpz_eq {o : LcnfObj} (h : o.tag = mpzTag) :
    lcnfObjMem o =
      cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) o.mpzMeta ⋆
        array64 (o.addr + 16#64) o.limbs := by
  unfold lcnfObjMem
  rw [ite_eq_right (by rw [h]; decide), ite_eq_right (by rw [h]; decide),
    ite_eq_right (by rw [h]; decide), ite_eq_right (by rw [h]; decide), ite_eq_left h]

theorem mkMpzObj_header (p : BitVec 64) (cap sz : Nat) (limbs : List (BitVec 64)) :
    ({ addr := p, rc := 1#32, csSz := 0, other := 0, tag := mpzTag,
       cap := cap, arrSize := sz, limbs := limbs : LcnfObj }).header = mpzHeaderWord := by
  dsimp only [LcnfObj.header, mpzHeaderWord, mpzTag]
  decide

theorem obj_rc_of_mask_eq1 {o : LcnfObj} (hwf : o.Wf)
    (hm : (o.header &&& 4294967295#64) = 1#64) : o.rc = 1#32 :=
  ba_rc_of_mask_eq1 hwf hm

theorem obj_rc_ne1_of_mask {o : LcnfObj} (hwf : o.Wf)
    (hm : (o.header &&& 4294967295#64) ≠ 1#64) : o.rc ≠ 1#32 :=
  ba_rc_ne1_of_mask hwf hm

theorem header_and_mask_eq_rc (o : LcnfObj) (hwf : o.Wf) :
    o.header &&& 4294967295#64 = BitVec.ofNat 64 o.rc.toNat :=
  LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1

theorem str_sz_lt_max_iff (sObj : LcnfObj) (hc : StrCanon sObj) :
    (BitVec.ofNat 64 (strPayload sObj).length).toNat < 268435415 := by
  have hplen := strPayload_length hc
  rcases hc with ⟨_, _, _, _, _, _, _, hac, hcap, hsl, _, _⟩
  rw [hplen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · unfold strMaxCap at hcap; omega
  · unfold strMaxCap at hcap; omega

/-! ## 3. Helper Function WP Proofs (`r2b_alloc_mpz` .. `r2b_utf8_decode_cp`) -/

private theorem r2b_mpz_sep_reorder {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C ⋆ D ⋆ E)) m) : (D ⋆ B ⋆ A ⋆ C ⋆ E) m :=
  sep_cast h (by ac_rfl)

theorem r2b_alloc_mpz_wp :
    ∀ xs m Q X, r2bAllocMpzSpec xs m Q X → Func.wp rtR2bEnv r2b_alloc_mpz_body xs m Q X := by
  intro ⟨rt, cap, sz, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2b_alloc_mpz_body, r2bAllocMpzSpec] at hPre ⊢
  by_cases hvalid : sz.toNat ≤ cap.toNat ∧ cap.toNat ≤ 33554429
  · rw [ite_eq_left hvalid] at hPre
    rcases hPre with ⟨st, R, hav, hm, hk⟩
    have hcapLe := hvalid.2
    have hszLe' := hvalid.1
    have hszEq := mpz_sz_mask_toNat cap hcapLe
    have hszLe : ((16 : BitVec 64) + 8 * cap).toNat ≤ 268435448 := by
      rw [hszEq]; unfold mpzAllocBytes; omega
    have hid : align8 (mpzAllocBytes cap.toNat) = mpzAllocBytes cap.toNat := by
      unfold mpzAllocBytes align8; omega
    r2b_steps
    r2b_call rtR2bEnv_lcnf_alloc
    dsimp only [lcnfAllocRemSpec, vals, Tup.map, Arg.val]
    rw [hszEq, hid]
    refine ⟨st, R, by rw [← hszEq]; exact hszLe, ?_, ?_, hav, hm,
      fun p st' m1 hp0 hp8 hpr hrem1 hrem2 hm1 => ?_⟩
    · unfold mpzAllocBytes rtMinObjBytes; omega
    · unfold mpzAllocBytes rtMaxObjBytes; omega
    · have hm1' : (region p (mpzAllocBytes cap.toNat) ⋆ (rtC0Inv rt st' ⋆ R)) m1 :=
        sep_cast hm1 (by ac_rfl)
      have hge16 : 16 ≤ mpzAllocBytes cap.toNat := by unfold mpzAllocBytes; omega
      have hfit16 : mpzAllocBytes cap.toNat ≤ 2 ^ 64 := by unfold mpzAllocBytes; omega
      obtain ⟨w0, w1, hp2⟩ := region_to_2cells_rem hge16 hfit16 hm1'
      have hpc : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆
          region (p + 16#64) (mpzAllocBytes cap.toNat - 16) ⋆ rtC0Inv rt st' ⋆ R)) m1 :=
        sep_cast hp2 (by ac_rfl)
      apply wp_store_sep (store_cell64 mpzHeaderWord hpc)
      intro m2 hm2
      r2b_steps
      have hm2' : (cell64 (p + 8#64) w1 ⋆ (cell64 p mpzHeaderWord ⋆
          region (p + 16#64) (mpzAllocBytes cap.toNat - 16) ⋆ rtC0Inv rt st' ⋆ R)) m2 :=
        sep_cast hm2 (by ac_rfl)
      have hst : storeOk m2 i64 (Arg.var (t := i64) (p + 8)).val ∧
          (cell64 (p + 8#64) (Arg.var (t := i64) (cap ||| sz <<< 32)).val ⋆
            (cell64 p mpzHeaderWord ⋆ region (p + 16#64) (mpzAllocBytes cap.toNat - 16) ⋆
              rtC0Inv rt st' ⋆ R))
            (storeMem m2 i64 (Arg.var (t := i64) (p + 8)).val
              (Arg.var (t := i64) (cap ||| sz <<< 32)).val) := by
        simp only [Arg.val_var]
        exact store_cell64 _ hm2'
      apply wp_store_sep hst
      intro m3 hm3
      simp only [Arg.val_var] at hm3
      r2b_steps
      have hremEq : mpzAllocBytes cap.toNat - 16 = 8 * cap.toNat := by
        unfold mpzAllocBytes; omega
      have hsh32 : (sz <<< (32 : BitVec 64)) = sz <<< (32 : Nat) := by
        rw [BitVec.shiftLeft_eq']; rfl
      rw [hremEq] at hm3
      have hm3' := r2b_mpz_sep_reorder hm3
      first | exact hk p st' m3 hp0 hp8 hpr hrem1 hrem2 hm3' | (
        rw [hsh32] at hm3'
        exact hk p st' m3 hp0 hp8 hpr hrem1 hrem2 hm3') | (
        rw [← hsh32] at hm3'
        exact hk p st' m3 hp0 hp8 hpr hrem1 hrem2 hm3')
  · rw [ite_eq_right hvalid] at hPre
    r2b_steps <;> first
      | exact hPre
      | (exfalso
         have h1 : ¬ (33554429#64).toNat < cap.toNat := by assumption
         have h2 : ¬ cap.toNat < sz.toNat := by assumption
         omega)

theorem r2b_str_alloc_cap_wp :
    ∀ xs m Q X, r2bStrAllocCapSpec xs m Q X →
      Func.wp rtR2bEnv r2b_str_alloc_cap_body xs m Q X := by
  intro ⟨rt, cap, sz, len, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2b_str_alloc_cap_body, r2bStrAllocCapSpec] at hPre ⊢
  by_cases hvalid : sz.toNat < strMaxCap ∧ sz.toNat < cap.toNat ∧ cap.toNat ≤ strMaxCap
  · rw [ite_eq_left hvalid] at hPre
    rcases hPre with ⟨st, R, hav, hm, hk⟩
    have hszMax : sz.toNat < 268435415 := by unfold strMaxCap at hvalid; exact hvalid.1
    have hszCap : sz.toNat < cap.toNat := hvalid.2.1
    have hcapMax : cap.toNat ≤ 268435415 := by unfold strMaxCap at hvalid; exact hvalid.2.2
    have hszEq : ((32 + cap + 7 &&& 18446744073709551608 : BitVec 64)).toNat =
        strAllocBytes cap.toNat := str_sz_mask_toNat cap hvalid.2.2
    have hszLe : ((32 + cap + 7 &&& 18446744073709551608 : BitVec 64)).toNat ≤ 268435448 := by
      rw [hszEq]; unfold strAllocBytes align8; omega
    have hid : align8 (strAllocBytes cap.toNat) = strAllocBytes cap.toNat :=
      align8_idemp (32 + cap.toNat)
    r2b_steps
    r2b_call rtR2bEnv_lcnf_alloc
    dsimp only [lcnfAllocRemSpec, vals, Tup.map, Arg.val]
    rw [show (~~~7 : BitVec 64) = 18446744073709551608 from by decide, hszEq, hid]
    refine ⟨st, R, by rw [← hszEq]; exact hszLe, ?_, ?_, hav, hm,
      fun p st' m1 hp0 hp8 hpr hrem1 hrem2 hm1 => ?_⟩
    · have := strAllocBytes_ge cap.toNat; unfold rtMinObjBytes; omega
    · unfold strAllocBytes align8 rtMaxObjBytes; omega
    · have hfit : strAllocBytes cap.toNat ≤ 2 ^ 64 := by
        unfold strAllocBytes align8; omega
      have hge32 : 32 + sz.toNat + 1 ≤ strAllocBytes cap.toNat := by
        have := strAllocBytes_ge cap.toNat; omega
      obtain ⟨w0, w1, w2, w3, hp4⟩ := region_to_4cells_rem (by omega) hfit
        (sep_cast hm1 (by ac_rfl) : (region p (strAllocBytes cap.toNat) ⋆ (rtC0Inv rt st' ⋆ R)) m1)
      have hp4' : (region (p + 32#64) (strAllocBytes cap.toNat - 32) ⋆
          (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
            cell64 (p + 24#64) w3 ⋆ rtC0Inv rt st' ⋆ R)) m1 :=
        sep_cast hp4 (by ac_rfl)
      have hsp1 : region (p + 32#64) (strAllocBytes cap.toNat - 32) =
          region (p + 32#64) sz.toNat ⋆
            region (p + 32#64 + sz) (strAllocBytes cap.toNat - 32 - sz.toNat) := by
        conv => lhs; rw [show strAllocBytes cap.toNat - 32 =
            sz.toNat + (strAllocBytes cap.toNat - 32 - sz.toNat) by omega]
        rw [region_split (by omega),
          show BitVec.ofNat 64 sz.toNat = sz from BitVec.eq_of_toNat_eq (by simp)]
      rw [hsp1] at hp4'
      have hp5 : (region (p + 32#64 + sz) (strAllocBytes cap.toNat - 32 - sz.toNat) ⋆
          (cell64 p w0 ⋆ cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
            cell64 (p + 24#64) w3 ⋆ region (p + 32#64) sz.toNat ⋆
            rtC0Inv rt st' ⋆ R)) m1 := sep_cast hp4' (by ac_rfl)
      obtain ⟨bsNul, hNulLen, hp6⟩ := region_pop_bytes (k := 1) (by omega) (by omega) hp5
      rcases bsNul with _ | ⟨b0, _ | _⟩ <;> simp at hNulLen
      rw [show (BitVec.ofNat 64 1 : BitVec 64) = 1#64 from rfl,
        show strAllocBytes cap.toNat - 32 - sz.toNat - 1 =
          strAllocBytes cap.toNat - (32 + sz.toNat + 1) by omega] at hp6
      have hpc : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆ cell64 (p + 16#64) w2 ⋆
          cell64 (p + 24#64) w3 ⋆ bytes (p + 32#64 + sz) [b0] ⋆
          region (p + 32#64 + sz + 1#64) (strAllocBytes cap.toNat - (32 + sz.toNat + 1)) ⋆
          region (p + 32#64) sz.toNat ⋆ rtC0Inv rt st' ⋆ R)) m1 := sep_cast hp6 (by ac_rfl)
      apply wp_store_sep (store_cell64 strHeaderWord hpc)
      intro m2 hm2
      r2b_steps
      have hm2' : (cell64 (p + 8#64) w1 ⋆ (cell64 p strHeaderWord ⋆
          cell64 (p + 16#64) w2 ⋆ cell64 (p + 24#64) w3 ⋆
          bytes (p + 32#64 + sz) [b0] ⋆
          region (p + 32#64 + sz + 1#64) (strAllocBytes cap.toNat - (32 + sz.toNat + 1)) ⋆
          region (p + 32#64) sz.toNat ⋆ rtC0Inv rt st' ⋆ R)) m2 := sep_cast hm2 (by ac_rfl)
      have hst : storeOk m2 i64 (Arg.var (t := i64) (p + 8)).val ∧
          (cell64 (p + 8#64) (Arg.var (t := i64) (sz + 1)).val ⋆
            (cell64 p strHeaderWord ⋆ cell64 (p + 16#64) w2 ⋆ cell64 (p + 24#64) w3 ⋆
              bytes (p + 32#64 + sz) [b0] ⋆
              region (p + 32#64 + sz + 1#64) (strAllocBytes cap.toNat - (32 + sz.toNat + 1)) ⋆
              region (p + 32#64) sz.toNat ⋆ rtC0Inv rt st' ⋆ R))
            (storeMem m2 i64 (Arg.var (t := i64) (p + 8)).val
              (Arg.var (t := i64) (sz + 1)).val) := by
        simp only [Arg.val_var]
        exact store_cell64 _ hm2'
      apply wp_store_sep hst
      intro m3 hm3
      simp only [Arg.val_var] at hm3
      r2b_steps
      have hm3' : (cell64 (p + 16#64) w2 ⋆ (cell64 p strHeaderWord ⋆
          cell64 (p + 8#64) (sz + 1#64) ⋆ cell64 (p + 24#64) w3 ⋆
          bytes (p + 32#64 + sz) [b0] ⋆
          region (p + 32#64 + sz + 1#64) (strAllocBytes cap.toNat - (32 + sz.toNat + 1)) ⋆
          region (p + 32#64) sz.toNat ⋆ rtC0Inv rt st' ⋆ R)) m3 := sep_cast hm3 (by ac_rfl)
      apply wp_store_sep (store_cell64 cap hm3')
      intro m4 hm4
      r2b_steps
      have hm4' : (cell64 (p + 24#64) w3 ⋆ (cell64 p strHeaderWord ⋆
          cell64 (p + 8#64) (sz + 1#64) ⋆ cell64 (p + 16#64) cap ⋆
          bytes (p + 32#64 + sz) [b0] ⋆
          region (p + 32#64 + sz + 1#64) (strAllocBytes cap.toNat - (32 + sz.toNat + 1)) ⋆
          region (p + 32#64) sz.toNat ⋆ rtC0Inv rt st' ⋆ R)) m4 := sep_cast hm4 (by ac_rfl)
      apply wp_store_sep (store_cell64 len hm4')
      intro m5 hm5
      r2b_steps
      have hm5' : (bytes (p + 32#64 + sz) [b0] ⋆ (cell64 p strHeaderWord ⋆
          cell64 (p + 8#64) (sz + 1#64) ⋆ cell64 (p + 16#64) cap ⋆ cell64 (p + 24#64) len ⋆
          region (p + 32#64 + sz + 1#64) (strAllocBytes cap.toNat - (32 + sz.toNat + 1)) ⋆
          region (p + 32#64) sz.toNat ⋆ rtC0Inv rt st' ⋆ R)) m5 := sep_cast hm5 (by ac_rfl)
      have hst6 : storeOk m5 i8 (Arg.var (t := i64) (p + 32 + sz)).val ∧
          (bytes (p + 32#64 + sz)
              [UInt8.ofNat (Arg.var (t := i8) (BitVec.setWidth 8 0#64)).val.toNat] ⋆
            (cell64 p strHeaderWord ⋆ cell64 (p + 8#64) (sz + 1#64) ⋆
              cell64 (p + 16#64) cap ⋆ cell64 (p + 24#64) len ⋆
              region (p + 32#64 + sz + 1#64) (strAllocBytes cap.toNat - (32 + sz.toNat + 1)) ⋆
              region (p + 32#64) sz.toNat ⋆ rtC0Inv rt st' ⋆ R))
            (storeMem m5 i8 (Arg.var (t := i64) (p + 32 + sz)).val
              (Arg.var (t := i8) (BitVec.setWidth 8 0#64)).val) := by
        simp only [Arg.val_var]
        exact r2b_c0_store_bytes_single _ hm5'
      apply wp_store_sep hst6
      intro m6 hm6
      simp only [Arg.val_var] at hm6
      r2b_steps
      apply hk p st' m6 hp0 hp8 hpr hrem1 hrem2
      have hzero : UInt8.ofNat (BitVec.setWidth 8 0#64).toNat = (0 : UInt8) := rfl
      rw [← hzero]
      exact sep_cast hm6 (by ac_rfl)
  · rw [ite_eq_right hvalid] at hPre
    unfold strMaxCap at hvalid
    r2b_steps <;> first
      | exact hPre
      | (exfalso
         have h1 : ¬ (268435415#64).toNat ≤ sz.toNat := by assumption
         have h2 : ¬ cap.toNat ≤ sz.toNat := by assumption
         have h3 : ¬ (268435415#64).toNat < cap.toNat := by assumption
         omega)

theorem r2b_utf8_len_wp :
    ∀ xs m Q X, r2bUtf8LenSpec xs m Q X → Func.wp rtR2bEnv r2b_utf8_len_body xs m Q X := by
  intro ⟨cp, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2b_utf8_len_body, r2bUtf8LenSpec, utf8LenNat] at hPre ⊢
  r2b_steps
  all_goals first
    | (have h1 : cp.toNat ≤ 127 := by simpa using (by assumption : cp.toNat ≤ (127#64).toNat)
       rw [ite_eq_left h1] at hPre; exact hPre)
    | (have h1 : ¬ cp.toNat ≤ 127 := by simpa using (by assumption : ¬ cp.toNat ≤ (127#64).toNat)
       have h2 : cp.toNat ≤ 2047 := by simpa using (by assumption : cp.toNat ≤ (2047#64).toNat)
       rw [ite_eq_right h1, ite_eq_left h2] at hPre; exact hPre)
    | (have h1 : ¬ cp.toNat ≤ 127 := by simpa using (by assumption : ¬ cp.toNat ≤ (127#64).toNat)
       have h2 : ¬ cp.toNat ≤ 2047 := by
         simpa using (by assumption : ¬ cp.toNat ≤ (2047#64).toNat)
       have h3 : cp.toNat ≤ 65535 := by simpa using (by assumption : cp.toNat ≤ (65535#64).toNat)
       rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] at hPre; exact hPre)
    | (have h1 : ¬ cp.toNat ≤ 127 := by simpa using (by assumption : ¬ cp.toNat ≤ (127#64).toNat)
       have h2 : ¬ cp.toNat ≤ 2047 := by
         simpa using (by assumption : ¬ cp.toNat ≤ (2047#64).toNat)
       have h3 : ¬ cp.toNat ≤ 65535 := by
         simpa using (by assumption : ¬ cp.toNat ≤ (65535#64).toNat)
       rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at hPre; exact hPre)

private theorem uint8_ofNat_setWidth_eq (x : BitVec 64) :
    UInt8.ofNat (BitVec.setWidth 8 x).toNat = UInt8.ofNat (x.toNat % 256) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

private theorem r2b_bytes_sep_congr2 {a : BitVec 64} {bs1 bs2 : List UInt8}
    {P1 P2 R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes a bs1 ⋆ (P1 ⋆ R)) m) (hbs : bs1 = bs2) (hP : P1 = P2) :
    (bytes a bs2 ⋆ P2 ⋆ R) m := by
  subst hbs; subst hP; exact sep_cast h (by ac_rfl)

private theorem u8_bv_ofNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat % 256 = n % 256) :
    UInt8.ofNat (BitVec.setWidth 8 x).toNat = UInt8.ofNat n := by
  apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 8 (BitVec.setWidth 8 x).toNat).toNat = (BitVec.ofNat 8 n).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mod_mod]
  simpa using h

private theorem utf8_b0_1_eq (cp : BitVec 64) (h1 : cp.toNat ≤ 0x7f) :
    UInt8.ofNat (BitVec.setWidth 8 cp).toNat = UInt8.ofNat cp.toNat := by
  rw [uint8_ofNat_setWidth_eq, Nat.mod_eq_of_lt (by omega)]

private theorem r2b_c0_store_bytes_0 {a : BitVec 64} {bs : List UInt8}
    (v : BitVec 8) {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes a bs ⋆ R) m) (hi : 0 < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    storeOk m i8 a ∧ (bytes a (bs.set 0 (UInt8.ofNat v.toNat)) ⋆ R) (storeMem m i8 a v) := by
  rw [← BitVec.add_zero a]
  simpa using r2_c0_store_bytes_bv (a := a) (i := 0#64) v h (by simpa using hi) hlen

private theorem wp_store8_bytes0 {env : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a : BitVec 64} {bs : List UInt8} (v : BitVec 8)
    {R : Mem 64 → Prop} {k : Expr Val Cont rs} {m : Mem 64}
    (hm : (bytes a bs ⋆ R) m) (hi : 0 < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hk : ∀ m', (bytes a (bs.set 0 (UInt8.ofNat v.toNat)) ⋆ R) m' → wp env Q X k m') :
    wp env Q X (Expr.store (Arg.var (t := i8) v) (Arg.var (t := i64) a) k) m :=
  wp_store_sep (R := R)
    (by simpa only [Arg.val_var] using r2b_c0_store_bytes_0 v hm hi hlen) hk

private theorem wp_store8_bytes {env : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a : BitVec 64} {bs : List UInt8} (i : BitVec 64) (v : BitVec 8)
    {R : Mem 64 → Prop} {k : Expr Val Cont rs} {m : Mem 64}
    (hm : (bytes a bs ⋆ R) m) (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hk : ∀ m', (bytes a (bs.set i.toNat (UInt8.ofNat v.toNat)) ⋆ R) m' → wp env Q X k m') :
    wp env Q X (Expr.store (Arg.var (t := i8) v) (Arg.var (t := i64) (a + i)) k) m :=
  wp_store_sep (R := R)
    (by simpa only [Arg.val_var] using r2_c0_store_bytes_bv v hm hi hlen) hk

theorem r2b_utf8_write_wp :
    ∀ xs m Q X, r2bUtf8WriteSpec xs m Q X → Func.wp rtR2bEnv r2b_utf8_write_body xs m Q X := by
  intro ⟨dst, cp, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2b_utf8_write_body, r2bUtf8WriteSpec] at hPre ⊢
  rcases hPre with ⟨remCap, R, hLe, hFit, hm, hk⟩
  by_cases h1 : cp.toNat ≤ 0x7f
  · have hbs : utf8EncodeBytes cp.toNat = [UInt8.ofNat cp.toNat] := by
      unfold utf8EncodeBytes; rw [ite_eq_left h1]
    rw [hbs] at hLe hk
    obtain ⟨bs0, h0Len, hm0⟩ := region_pop_bytes (k := 1) (by simp at hLe; omega) hFit hm
    rcases bs0 with _ | ⟨b0, _ | _⟩ <;> simp at h0Len
    r2b_steps
    exact apply_wp_store_1 hk (sep_cast (by assumption) (by ac_rfl)) (utf8_b0_1_eq cp h1)
  · by_cases h2 : cp.toNat ≤ 0x7ff
    · have hbs : utf8EncodeBytes cp.toNat =
          [ UInt8.ofNat (0xc0 ||| (cp.toNat >>> 6))
          , UInt8.ofNat (0x80 ||| (cp.toNat &&& 0x3f)) ] := by
        unfold utf8EncodeBytes; rw [ite_eq_right h1, ite_eq_left h2]
      rw [hbs] at hLe hk
      r2b_steps
      all_goals first
        | (exfalso
           have hle : cp.toNat ≤ 127 := by simpa using (by assumption : cp.toNat ≤ (127#64).toNat)
           omega)
        | (exfalso
           have hgt : ¬ cp.toNat ≤ 2047 := by
             simpa using (by assumption : ¬ cp.toNat ≤ (2047#64).toNat)
           exact hgt h2)
        | (obtain ⟨bs, hbsLen, hm0⟩ := region_pop_bytes (k := 2) (by simp at hLe; omega) hFit hm
           rcases bs with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> simp at hbsLen
           have hm0' : (bytes dst [b0, b1] ⋆ (region (dst + 2#64) (remCap - 2) ⋆ R)) m :=
             sep_cast hm0 (by ac_rfl)
           apply wp_store8_bytes0 _ hm0' (by simp) (by simp)
           intro m1 hm1
           simp only [List.set_cons_zero] at hm1
           r2b_steps
           apply wp_store8_bytes 1 _ hm1 (by simp) (by simp)
           intro m2 hm2
           have hi1 : (1 : BitVec 64).toNat = 1 := rfl
           simp only [hi1, List.set_cons_succ, List.set_cons_zero] at hm2
           r2b_steps
           refine hk m2 (r2b_bytes_sep_congr2 hm2 ?_ rfl)
           simp only [List.cons.injEq, and_true]
           refine ⟨?_, ?_⟩ <;> (
             apply u8_bv_ofNat_eq
             try rw [BitVec.ushiftRight_eq']
             simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight]
             rfl))
    · by_cases h3 : cp.toNat ≤ 0xffff
      · have hbs : utf8EncodeBytes cp.toNat =
            [ UInt8.ofNat (0xe0 ||| (cp.toNat >>> 12))
            , UInt8.ofNat (0x80 ||| ((cp.toNat >>> 6) &&& 0x3f))
            , UInt8.ofNat (0x80 ||| (cp.toNat &&& 0x3f)) ] := by
          unfold utf8EncodeBytes; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
        rw [hbs] at hLe hk
        r2b_steps
        all_goals first
          | (exfalso
             have hle : cp.toNat ≤ 127 := by simpa using (by assumption : cp.toNat ≤ (127#64).toNat)
             omega)
          | (exfalso
             have hle : cp.toNat ≤ 2047 := by
               simpa using (by assumption : cp.toNat ≤ (2047#64).toNat)
             omega)
          | (exfalso
             have hgt : ¬ cp.toNat ≤ 65535 := by
               simpa using (by assumption : ¬ cp.toNat ≤ (65535#64).toNat)
             exact hgt h3)
          | (obtain ⟨bs, hbsLen, hm0⟩ := region_pop_bytes (k := 3) (by simp at hLe; omega) hFit hm
             rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | _⟩⟩⟩ <;> simp at hbsLen
             have hm0' : (bytes dst [b0, b1, b2] ⋆
                 (region (dst + 3#64) (remCap - 3) ⋆ R)) m :=
               sep_cast hm0 (by ac_rfl)
             apply wp_store8_bytes0 _ hm0' (by simp) (by simp)
             intro m1 hm1
             simp only [List.set_cons_zero] at hm1
             r2b_steps
             apply wp_store8_bytes 1 _ hm1 (by simp) (by simp)
             intro m2 hm2
             have hi1 : (1 : BitVec 64).toNat = 1 := rfl
             simp only [hi1, List.set_cons_succ, List.set_cons_zero] at hm2
             r2b_steps
             apply wp_store8_bytes 2 _ hm2 (by simp) (by simp)
             intro m3 hm3
             have hi2 : (2 : BitVec 64).toNat = 2 := rfl
             simp only [hi2, List.set_cons_succ, List.set_cons_zero] at hm3
             r2b_steps
             refine hk m3 (r2b_bytes_sep_congr2 hm3 ?_ rfl)
             simp only [List.cons.injEq, and_true]
             refine ⟨?_, ?_, ?_⟩ <;> (
               apply u8_bv_ofNat_eq
               try rw [BitVec.ushiftRight_eq']
               simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight]
               rfl))
      · have hbs : utf8EncodeBytes cp.toNat =
            [ UInt8.ofNat (0xf0 ||| ((cp.toNat >>> 18) &&& 0x07))
            , UInt8.ofNat (0x80 ||| ((cp.toNat >>> 12) &&& 0x3f))
            , UInt8.ofNat (0x80 ||| ((cp.toNat >>> 6) &&& 0x3f))
            , UInt8.ofNat (0x80 ||| (cp.toNat &&& 0x3f)) ] := by
          unfold utf8EncodeBytes; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
        rw [hbs] at hLe hk
        r2b_steps
        all_goals first
          | (exfalso
             have hle : cp.toNat ≤ 127 := by simpa using (by assumption : cp.toNat ≤ (127#64).toNat)
             omega)
          | (exfalso
             have hle : cp.toNat ≤ 2047 := by
               simpa using (by assumption : cp.toNat ≤ (2047#64).toNat)
             omega)
          | (exfalso
             have hle : cp.toNat ≤ 65535 := by
               simpa using (by assumption : cp.toNat ≤ (65535#64).toNat)
             omega)
          | (obtain ⟨bs, hbsLen, hm0⟩ := region_pop_bytes (k := 4) (by simp at hLe; omega) hFit hm
             rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> simp at hbsLen
             have hm0' : (bytes dst [b0, b1, b2, b3] ⋆
                 (region (dst + 4#64) (remCap - 4) ⋆ R)) m :=
               sep_cast hm0 (by ac_rfl)
             apply wp_store8_bytes0 _ hm0' (by simp) (by simp)
             intro m1 hm1
             simp only [List.set_cons_zero] at hm1
             r2b_steps
             apply wp_store8_bytes 1 _ hm1 (by simp) (by simp)
             intro m2 hm2
             have hi1 : (1 : BitVec 64).toNat = 1 := rfl
             simp only [hi1, List.set_cons_succ, List.set_cons_zero] at hm2
             r2b_steps
             apply wp_store8_bytes 2 _ hm2 (by simp) (by simp)
             intro m3 hm3
             have hi2 : (2 : BitVec 64).toNat = 2 := rfl
             simp only [hi2, List.set_cons_succ, List.set_cons_zero] at hm3
             r2b_steps
             apply wp_store8_bytes 3 _ hm3 (by simp) (by simp)
             intro m4 hm4
             have hi3 : (3 : BitVec 64).toNat = 3 := rfl
             simp only [hi3, List.set_cons_succ, List.set_cons_zero] at hm4
             r2b_steps
             refine hk m4 (r2b_bytes_sep_congr2 hm4 ?_ rfl)
             simp only [List.cons.injEq, and_true]
             refine ⟨?_, ?_, ?_, ?_⟩ <;> (
               apply u8_bv_ofNat_eq
               try rw [BitVec.ushiftRight_eq']
               simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight]
               rfl))
where
  apply_wp_store_1 {dst cp : BitVec 64} {remCap : Nat} {R : Mem 64 → Prop}
      {Q : Post [i64]} {m' : Mem 64}
      (hk : ∀ m', (bytes dst [UInt8.ofNat cp.toNat] ⋆
        region (dst + BitVec.ofNat 64 [UInt8.ofNat cp.toNat].length)
          (remCap - [UInt8.ofNat cp.toNat].length) ⋆ R) m' →
        Q (BitVec.ofNat 64 [UInt8.ofNat cp.toNat].length, ()) m')
      (hm : (bytes dst [UInt8.ofNat (BitVec.setWidth 8 cp).toNat] ⋆
        region (dst + 1#64) (remCap - 1) ⋆ R) m')
      (heq : UInt8.ofNat (BitVec.setWidth 8 cp).toNat = UInt8.ofNat cp.toNat) :
      Q (1#64, ()) m' := by
    rw [heq] at hm
    exact hk m' (sep_cast hm (by ac_rfl))

private theorem bv8_zext_mask_eq (b : UInt8) (mask : Nat) :
    (BitVec.setWidth 64 (BitVec.ofNat 8 b.toNat) &&& BitVec.ofNat 64 mask).toNat =
      b.toNat &&& mask := by
  have hblt : b.toNat < 256 := b.toBitVec.isLt
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.testBit_and]
  by_cases hi : i < 8
  · have h64 : i < 64 := by omega
    rw [Nat.mod_eq_of_lt hblt, Nat.mod_eq_of_lt (by omega), Nat.testBit_mod_two_pow]
    simp [h64]
  · have hpow : 256 ≤ 2 ^ i :=
      Nat.le_trans (by decide : 256 ≤ 2 ^ 8) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    have hbf : b.toNat.testBit i = false := Nat.testBit_lt_two_pow (i := i) (by omega)
    rw [Nat.mod_eq_of_lt hblt]
    simp [hbf]

theorem r2b_utf8_decode_step_wp :
    ∀ xs m Q X, r2bUtf8DecodeStepSpec xs m Q X →
      Func.wp rtR2bEnv r2b_utf8_decode_step_body xs m Q X := by
  intro ⟨data, sz, idx, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2b_utf8_decode_step_body, r2bUtf8DecodeStepSpec] at hPre ⊢
  rcases hPre with ⟨bs, R, hLen, hm, hQ⟩
  unfold utf8DecodeStepAt at hQ
  by_cases hge : sz.toNat ≤ idx.toNat
  · rw [ite_eq_left (by omega)] at hQ
    r2b_steps
    exact hQ
  · rw [ite_eq_right (by omega)] at hQ
    have hlt : idx.toNat < bs.length := by omega
    rw [getElem!_pos bs idx.toNat hlt] at hQ
    have _ := r2_c0_load_bytes_bv hm hlt (by omega)
    have hsub : (sz - idx).toNat = sz.toNat - idx.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    r2b_steps
    all_goals first
      | (have hb0 : (bs[idx.toNat].toNat &&& 0x80) = 0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) =
               0#64 := by assumption
           have htn := congrArg BitVec.toNat hc
           rw [bv8_zext_mask_eq] at htn; exact htn
         simpa [hb0] using hQ)
      | (have h1 : (bs[idx.toNat].toNat &&& 0x80) ≠ 0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) ≠
               0#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have hb0 : (bs[idx.toNat].toNat &&& 0xe0) = 0xc0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) =
               192#64 := by assumption
           have htn := congrArg BitVec.toNat hc
           rw [bv8_zext_mask_eq] at htn; exact htn
         have hlt1 : idx.toNat + 1 < bs.length := by
           have hc : (1#64).toNat < (sz - idx).toNat := by assumption
           rw [hsub] at hc; change 1 < sz.toNat - idx.toNat at hc; omega
         simpa [h1, hb0, hlt1] using hQ)
      | (have h1 : (bs[idx.toNat].toNat &&& 0x80) ≠ 0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) ≠
               0#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have hb0 : (bs[idx.toNat].toNat &&& 0xe0) = 0xc0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) =
               192#64 := by assumption
           have htn := congrArg BitVec.toNat hc
           rw [bv8_zext_mask_eq] at htn; exact htn
         have hge1 : ¬ idx.toNat + 1 < bs.length := by
           have hc : ¬ (1#64).toNat < (sz - idx).toNat := by assumption
           rw [hsub] at hc; change ¬ 1 < sz.toNat - idx.toNat at hc; omega
         simpa [h1, hb0, hge1] using hQ)
      | (have h1 : (bs[idx.toNat].toNat &&& 0x80) ≠ 0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) ≠
               0#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h2 : (bs[idx.toNat].toNat &&& 0xe0) ≠ 0xc0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) ≠
               192#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have hb0 : (bs[idx.toNat].toNat &&& 0xf0) = 0xe0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 240#64) =
               224#64 := by assumption
           have htn := congrArg BitVec.toNat hc
           rw [bv8_zext_mask_eq] at htn; exact htn
         have hlt2 : idx.toNat + 2 < bs.length := by
           have hc : (2#64).toNat < (sz - idx).toNat := by assumption
           rw [hsub] at hc; change 2 < sz.toNat - idx.toNat at hc; omega
         simpa [h1, h2, hb0, hlt2] using hQ)
      | (have h1 : (bs[idx.toNat].toNat &&& 0x80) ≠ 0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) ≠
               0#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h2 : (bs[idx.toNat].toNat &&& 0xe0) ≠ 0xc0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) ≠
               192#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have hb0 : (bs[idx.toNat].toNat &&& 0xf0) = 0xe0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 240#64) =
               224#64 := by assumption
           have htn := congrArg BitVec.toNat hc
           rw [bv8_zext_mask_eq] at htn; exact htn
         have hge2 : ¬ idx.toNat + 2 < bs.length := by
           have hc : ¬ (2#64).toNat < (sz - idx).toNat := by assumption
           rw [hsub] at hc; change ¬ 2 < sz.toNat - idx.toNat at hc; omega
         simpa [h1, h2, hb0, hge2] using hQ)
      | (have h1 : (bs[idx.toNat].toNat &&& 0x80) ≠ 0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) ≠
               0#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h2 : (bs[idx.toNat].toNat &&& 0xe0) ≠ 0xc0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) ≠
               192#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h3 : (bs[idx.toNat].toNat &&& 0xf0) ≠ 0xe0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 240#64) ≠
               224#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have hb0 : (bs[idx.toNat].toNat &&& 0xf8) = 0xf0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 248#64) =
               240#64 := by assumption
           have htn := congrArg BitVec.toNat hc
           rw [bv8_zext_mask_eq] at htn; exact htn
         have hlt3 : idx.toNat + 3 < bs.length := by
           have hc : (3#64).toNat < (sz - idx).toNat := by assumption
           rw [hsub] at hc; change 3 < sz.toNat - idx.toNat at hc; omega
         simpa [h1, h2, h3, hb0, hlt3] using hQ)
      | (have h1 : (bs[idx.toNat].toNat &&& 0x80) ≠ 0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) ≠
               0#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h2 : (bs[idx.toNat].toNat &&& 0xe0) ≠ 0xc0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) ≠
               192#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h3 : (bs[idx.toNat].toNat &&& 0xf0) ≠ 0xe0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 240#64) ≠
               224#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have hb0 : (bs[idx.toNat].toNat &&& 0xf8) = 0xf0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 248#64) =
               240#64 := by assumption
           have htn := congrArg BitVec.toNat hc
           rw [bv8_zext_mask_eq] at htn; exact htn
         have hge3 : ¬ idx.toNat + 3 < bs.length := by
           have hc : ¬ (3#64).toNat < (sz - idx).toNat := by assumption
           rw [hsub] at hc; change ¬ 3 < sz.toNat - idx.toNat at hc; omega
         simpa [h1, h2, h3, hb0, hge3] using hQ)
      | (have h1 : (bs[idx.toNat].toNat &&& 0x80) ≠ 0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) ≠
               0#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h2 : (bs[idx.toNat].toNat &&& 0xe0) ≠ 0xc0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) ≠
               192#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h3 : (bs[idx.toNat].toNat &&& 0xf0) ≠ 0xe0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 240#64) ≠
               224#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         have h4 : (bs[idx.toNat].toNat &&& 0xf8) ≠ 0xf0 := by
           have hc : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 248#64) ≠
               240#64 := by assumption
           intro h0; apply hc; apply BitVec.eq_of_toNat_eq
           rw [bv8_zext_mask_eq]; exact h0
         simpa [h1, h2, h3, h4] using hQ)

private theorem bv8_decode2_eq (b0 b1 : UInt8) {sh6 m0 m1 : BitVec 64}
    (hm0 : m0.toNat = 31) (hm1 : m1.toNat = 63) (hsh6 : sh6.toNat = 6) :
    (((BitVec.setWidth 64 (BitVec.ofNat 8 b0.toNat) &&& m0) <<< sh6) |||
      (BitVec.setWidth 64 (BitVec.ofNat 8 b1.toNat) &&& m1)) =
      BitVec.ofNat 64 (((b0.toNat &&& 0x1f) <<< 6) ||| (b1.toNat &&& 0x3f)) := by
  apply BitVec.eq_of_toNat_eq
  have hm0' : m0 = BitVec.ofNat 64 31 := BitVec.eq_of_toNat_eq hm0
  have hm1' : m1 = BitVec.ofNat 64 63 := BitVec.eq_of_toNat_eq hm1
  rw [hm0', hm1', BitVec.shiftLeft_eq']
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, hsh6, bv8_zext_mask_eq]
  have ha1 : (b0.toNat &&& 31) <<< 6 < 2 ^ 64 := by
    have : b0.toNat &&& 31 ≤ 31 := Nat.and_le_right
    rw [Nat.shiftLeft_eq]; omega
  have ha2 : b1.toNat &&& 63 < 2 ^ 64 := by
    have : b1.toNat &&& 63 ≤ 63 := Nat.and_le_right; omega
  have hor := Nat.or_lt_two_pow (n := 64) ha1 ha2
  rw [Nat.mod_eq_of_lt ha1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hor]

private theorem bv8_decode3_eq (b0 b1 b2 : UInt8) {sh12 sh6 m0 m1 m2 : BitVec 64}
    (hm0 : m0.toNat = 15) (hm1 : m1.toNat = 63) (hm2 : m2.toNat = 63)
    (hsh12 : sh12.toNat = 12) (hsh6 : sh6.toNat = 6) :
    (((BitVec.setWidth 64 (BitVec.ofNat 8 b0.toNat) &&& m0) <<< sh12) |||
      ((BitVec.setWidth 64 (BitVec.ofNat 8 b1.toNat) &&& m1) <<< sh6) |||
      (BitVec.setWidth 64 (BitVec.ofNat 8 b2.toNat) &&& m2)) =
      BitVec.ofNat 64
        (((b0.toNat &&& 0x0f) <<< 12) ||| ((b1.toNat &&& 0x3f) <<< 6) ||| (b2.toNat &&& 0x3f)) := by
  apply BitVec.eq_of_toNat_eq
  have hm0' : m0 = BitVec.ofNat 64 15 := BitVec.eq_of_toNat_eq hm0
  have hm1' : m1 = BitVec.ofNat 64 63 := BitVec.eq_of_toNat_eq hm1
  have hm2' : m2 = BitVec.ofNat 64 63 := BitVec.eq_of_toNat_eq hm2
  rw [hm0', hm1', hm2', BitVec.shiftLeft_eq', BitVec.shiftLeft_eq']
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, hsh12, hsh6, bv8_zext_mask_eq]
  have ha1 : (b0.toNat &&& 15) <<< 12 < 2 ^ 64 := by
    have : b0.toNat &&& 15 ≤ 15 := Nat.and_le_right
    rw [Nat.shiftLeft_eq]; omega
  have ha2 : (b1.toNat &&& 63) <<< 6 < 2 ^ 64 := by
    have : b1.toNat &&& 63 ≤ 63 := Nat.and_le_right
    rw [Nat.shiftLeft_eq]; omega
  have ha3 : b2.toNat &&& 63 < 2 ^ 64 := by
    have : b2.toNat &&& 63 ≤ 63 := Nat.and_le_right; omega
  have hor1 := Nat.or_lt_two_pow (n := 64) ha1 ha2
  have hor2 := Nat.or_lt_two_pow (n := 64) hor1 ha3
  rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hor2]

private theorem bv8_decode4_eq (b0 b1 b2 b3 : UInt8) {sh18 sh12 sh6 m0 m1 m2 m3 : BitVec 64}
    (hm0 : m0.toNat = 7) (hm1 : m1.toNat = 63) (hm2 : m2.toNat = 63) (hm3 : m3.toNat = 63)
    (hsh18 : sh18.toNat = 18) (hsh12 : sh12.toNat = 12) (hsh6 : sh6.toNat = 6) :
    ((((BitVec.setWidth 64 (BitVec.ofNat 8 b0.toNat) &&& m0) <<< sh18) |||
        ((BitVec.setWidth 64 (BitVec.ofNat 8 b1.toNat) &&& m1) <<< sh12)) |||
      (((BitVec.setWidth 64 (BitVec.ofNat 8 b2.toNat) &&& m2) <<< sh6) |||
        (BitVec.setWidth 64 (BitVec.ofNat 8 b3.toNat) &&& m3))) =
      BitVec.ofNat 64
        (((b0.toNat &&& 0x07) <<< 18) ||| ((b1.toNat &&& 0x3f) <<< 12) |||
         ((b2.toNat &&& 0x3f) <<< 6) ||| (b3.toNat &&& 0x3f)) := by
  apply BitVec.eq_of_toNat_eq
  have hm0' : m0 = BitVec.ofNat 64 7 := BitVec.eq_of_toNat_eq hm0
  have hm1' : m1 = BitVec.ofNat 64 63 := BitVec.eq_of_toNat_eq hm1
  have hm2' : m2 = BitVec.ofNat 64 63 := BitVec.eq_of_toNat_eq hm2
  have hm3' : m3 = BitVec.ofNat 64 63 := BitVec.eq_of_toNat_eq hm3
  rw [hm0', hm1', hm2', hm3', BitVec.shiftLeft_eq', BitVec.shiftLeft_eq', BitVec.shiftLeft_eq']
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, hsh18, hsh12, hsh6, bv8_zext_mask_eq]
  have ha1 : (b0.toNat &&& 7) <<< 18 < 2 ^ 64 := by
    have : b0.toNat &&& 7 ≤ 7 := Nat.and_le_right
    rw [Nat.shiftLeft_eq]; omega
  have ha2 : (b1.toNat &&& 63) <<< 12 < 2 ^ 64 := by
    have : b1.toNat &&& 63 ≤ 63 := Nat.and_le_right
    rw [Nat.shiftLeft_eq]; omega
  have ha3 : (b2.toNat &&& 63) <<< 6 < 2 ^ 64 := by
    have : b2.toNat &&& 63 ≤ 63 := Nat.and_le_right
    rw [Nat.shiftLeft_eq]; omega
  have ha4 : b3.toNat &&& 63 < 2 ^ 64 := by
    have : b3.toNat &&& 63 ≤ 63 := Nat.and_le_right; omega
  have hor1 := Nat.or_lt_two_pow (n := 64) ha1 ha2
  have hor' : ((b0.toNat &&& 7) <<< 18 ||| (b1.toNat &&& 63) <<< 12 |||
      (b2.toNat &&& 63) <<< 6 ||| b3.toNat &&& 63) < 2 ^ 64 :=
    Nat.or_lt_two_pow (n := 64) (Nat.or_lt_two_pow (n := 64) hor1 ha3) ha4
  rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt ha3,
    BitVec.toNat_ofNat, ← Nat.or_assoc, Nat.mod_eq_of_lt hor']

theorem r2b_utf8_decode_cp_wp :
    ∀ xs m Q X, r2bUtf8DecodeCpSpec xs m Q X →
      Func.wp rtR2bEnv r2b_utf8_decode_cp_body xs m Q X := by
  intro ⟨data, sz, idx, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, r2b_utf8_decode_cp_body, r2bUtf8DecodeCpSpec] at hPre ⊢
  rcases hPre with ⟨bs, R, hLen, hm, hQ⟩
  unfold utf8DecodeCpAt at hQ
  by_cases hge : sz.toNat ≤ idx.toNat
  · rw [ite_eq_left (by omega)] at hQ
    r2b_steps
    exact hQ
  · rw [ite_eq_right (by omega)] at hQ
    have hlt : idx.toNat < bs.length := by omega
    rw [getElem!_pos bs idx.toNat hlt] at hQ
    have _ := r2_c0_load_bytes_bv hm hlt (by omega)
    have hsub : (sz - idx).toNat = sz.toNat - idx.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    have hsubRaw : (2 ^ 64 - idx.toNat + sz.toNat) % 2 ^ 64 = sz.toNat - idx.toNat := by
      have := sz.isLt; omega
    have hbvNotEq : ∀ (a b : BitVec 64) (x : Nat),
        BitVec.toNat a ≠ BitVec.toNat b → a ≠ b :=
      fun _ _ _ hne heq => hne (congrArg BitVec.toNat heq)
    by_cases h1 : (bs[idx.toNat].toNat &&& 0x80) = 0
    · have hc1 : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) = 0#64 :=
        BitVec.eq_of_toNat_eq (by rw [bv8_zext_mask_eq]; exact h1)
      simp only [h1, ↓reduceIte] at hQ
      have hres : BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) =
          BitVec.ofNat 64 bs[idx.toNat].toNat := by
        have hblt : bs[idx.toNat].toNat < 256 := bs[idx.toNat].toBitVec.isLt
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hblt, Nat.mod_eq_of_lt (by omega)]
      r2b_steps
      rw [hres]; exact hQ
    · have hc1 : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 128#64) ≠ 0#64 :=
        fun heq => h1 (by simpa [bv8_zext_mask_eq] using congrArg BitVec.toNat heq)
      by_cases hb0 : (bs[idx.toNat].toNat &&& 0xe0) = 0xc0
      · have hc2 : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) =
            192#64 := BitVec.eq_of_toNat_eq (by rw [bv8_zext_mask_eq]; exact hb0)
        by_cases hlt1 : idx.toNat + 1 < bs.length
        · have hi1 : (idx + 1#64).toNat = idx.toNat + 1 := by
            simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
          have hi1' : (idx + 1).toNat = idx.toNat + 1 := hi1
          have _ := r2b_c0_load_bytes_bv_addk hm (i := idx) (k := 1#64)
            (by rw [hi1]; exact hlt1) (by omega)
          rw [getElem!_pos bs (idx.toNat + 1) hlt1] at hQ
          simp only [h1, hb0, hlt1, ↓reduceIte] at hQ
          r2b_steps
          all_goals first
            | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 128#64 = 0#64) |> hc1)
            | (exfalso; exact (by assumption : ¬ BitVec.setWidth 64 _ &&& 224#64 = 192#64) hc2)
            | (exfalso; first
                | (have hc : ¬ (1#64).toNat < (sz - idx).toNat := by assumption
                   rw [hsub] at hc; change ¬ 1 < sz.toNat - idx.toNat at hc; omega)
                | (have hc : ¬ BitVec.toNat (1 : BitVec 64) <
                       (2 ^ 64 - idx.toNat + sz.toNat) % 2 ^ 64 := by assumption
                   rw [hsubRaw] at hc; change ¬ 1 < sz.toNat - idx.toNat at hc; omega))
            | (refine Eq.mp (congrArg (fun v => Q (v, ()) _) ?_) hQ
               simp only [hi1']
               have hdec := bv8_decode2_eq bs[idx.toNat] bs[idx.toNat + 1]
                 (sh6 := BitVec.signExtend 64 6#32) (m0 := 31#64) (m1 := 63#64)
                 (by decide) (by decide) (by decide)
               exact hdec.symm)
        · simp only [h1, hb0, hlt1, ↓reduceIte] at hQ
          r2b_steps
          all_goals first
            | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 128#64 = 0#64) |> hc1)
            | (exfalso; exact (by assumption : ¬ BitVec.setWidth 64 _ &&& 224#64 = 192#64) hc2)
            | (exfalso; first
                | (have hc : (1#64).toNat < (sz - idx).toNat := by assumption
                   rw [hsub] at hc; change 1 < sz.toNat - idx.toNat at hc; omega)
                | (have hc : BitVec.toNat (1 : BitVec 64) <
                       (2 ^ 64 - idx.toNat + sz.toNat) % 2 ^ 64 := by assumption
                   rw [hsubRaw] at hc; change 1 < sz.toNat - idx.toNat at hc; omega))
            | exact hQ
      · have hc2 : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 224#64) ≠
            192#64 := fun heq => hb0 (by simpa [bv8_zext_mask_eq] using congrArg BitVec.toNat heq)
        by_cases hb3 : (bs[idx.toNat].toNat &&& 0xf0) = 0xe0
        · have hc3 : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 240#64) =
              224#64 := BitVec.eq_of_toNat_eq (by rw [bv8_zext_mask_eq]; exact hb3)
          by_cases hlt2 : idx.toNat + 2 < bs.length
          · have hi1 : (idx + 1#64).toNat = idx.toNat + 1 := by
              simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
            have hi2 : (idx + 2#64).toNat = idx.toNat + 2 := by
              simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
            have hi1' : (idx + 1).toNat = idx.toNat + 1 := hi1
            have hi2' : (idx + 2).toNat = idx.toNat + 2 := hi2
            have _ := r2b_c0_load_bytes_bv_addk hm (i := idx) (k := 1#64)
              (by rw [hi1]; omega) (by omega)
            have _ := r2b_c0_load_bytes_bv_addk hm (i := idx) (k := 2#64)
              (by rw [hi2]; exact hlt2) (by omega)
            rw [getElem!_pos bs (idx.toNat + 1) (by omega),
              getElem!_pos bs (idx.toNat + 2) hlt2] at hQ
            simp only [h1, hb0, hb3, hlt2, ↓reduceIte] at hQ
            r2b_steps
            all_goals first
              | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 128#64 = 0#64) |> hc1)
              | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 224#64 = 192#64) |> hc2)
              | (exfalso; exact (by assumption : ¬ BitVec.setWidth 64 _ &&& 240#64 = 224#64) hc3)
              | (exfalso; first
                  | (have hc : ¬ (2#64).toNat < (sz - idx).toNat := by assumption
                     rw [hsub] at hc; change ¬ 2 < sz.toNat - idx.toNat at hc; omega)
                  | (have hc : ¬ BitVec.toNat (2 : BitVec 64) <
                         (2 ^ 64 - idx.toNat + sz.toNat) % 2 ^ 64 := by assumption
                     rw [hsubRaw] at hc; change ¬ 2 < sz.toNat - idx.toNat at hc; omega))
              | (refine Eq.mp (congrArg (fun v => Q (v, ()) _) ?_) hQ
                 simp only [hi1', hi2']
                 have hdec := bv8_decode3_eq bs[idx.toNat] bs[idx.toNat + 1] bs[idx.toNat + 2]
                   (sh12 := BitVec.signExtend 64 12#32) (sh6 := BitVec.signExtend 64 6#32)
                   (m0 := 15#64) (m1 := 63#64) (m2 := 63#64)
                   (by decide) (by decide) (by decide) (by decide) (by decide)
                 first
                   | exact hdec.symm
                   | (rw [← BitVec.or_assoc]; exact hdec.symm)
                   | (rw [BitVec.or_assoc]; exact hdec.symm))
          · simp only [h1, hb0, hb3, hlt2, ↓reduceIte] at hQ
            r2b_steps
            all_goals first
              | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 128#64 = 0#64) |> hc1)
              | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 224#64 = 192#64) |> hc2)
              | (exfalso; exact (by assumption : ¬ BitVec.setWidth 64 _ &&& 240#64 = 224#64) hc3)
              | (exfalso; first
                  | (have hc : (2#64).toNat < (sz - idx).toNat := by assumption
                     rw [hsub] at hc; change 2 < sz.toNat - idx.toNat at hc; omega)
                  | (have hc : BitVec.toNat (2 : BitVec 64) <
                         (2 ^ 64 - idx.toNat + sz.toNat) % 2 ^ 64 := by assumption
                     rw [hsubRaw] at hc; change 2 < sz.toNat - idx.toNat at hc; omega))
              | exact hQ
        · have hc3 : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 240#64) ≠
              224#64 := fun heq => hb3 (by simpa [bv8_zext_mask_eq] using congrArg BitVec.toNat heq)
          by_cases hb4 : (bs[idx.toNat].toNat &&& 0xf8) = 0xf0
          · have hc4 : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 248#64) =
                240#64 := BitVec.eq_of_toNat_eq (by rw [bv8_zext_mask_eq]; exact hb4)
            by_cases hlt3 : idx.toNat + 3 < bs.length
            · have hi1 : (idx + 1#64).toNat = idx.toNat + 1 := by
                simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
              have hi2 : (idx + 2#64).toNat = idx.toNat + 2 := by
                simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
              have hi3 : (idx + 3#64).toNat = idx.toNat + 3 := by
                simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
              have hi1' : (idx + 1).toNat = idx.toNat + 1 := hi1
              have hi2' : (idx + 2).toNat = idx.toNat + 2 := hi2
              have hi3' : (idx + 3).toNat = idx.toNat + 3 := hi3
              have _ := r2b_c0_load_bytes_bv_addk hm (i := idx) (k := 1#64)
                (by rw [hi1]; omega) (by omega)
              have _ := r2b_c0_load_bytes_bv_addk hm (i := idx) (k := 2#64)
                (by rw [hi2]; omega) (by omega)
              have _ := r2b_c0_load_bytes_bv_addk hm (i := idx) (k := 3#64)
                (by rw [hi3]; exact hlt3) (by omega)
              rw [getElem!_pos bs (idx.toNat + 1) (by omega),
                getElem!_pos bs (idx.toNat + 2) (by omega),
                getElem!_pos bs (idx.toNat + 3) hlt3] at hQ
              simp only [h1, hb0, hb3, hb4, hlt3, ↓reduceIte] at hQ
              r2b_steps
              all_goals first
                | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 128#64 = 0#64) |> hc1)
                | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 224#64 = 192#64) |> hc2)
                | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 240#64 = 224#64) |> hc3)
                | (exfalso; exact (by assumption : ¬ BitVec.setWidth 64 _ &&& 248#64 = 240#64) hc4)
                | (exfalso; first
                    | (have hc : ¬ (3#64).toNat < (sz - idx).toNat := by assumption
                       rw [hsub] at hc; change ¬ 3 < sz.toNat - idx.toNat at hc; omega)
                    | (have hc : ¬ BitVec.toNat (3 : BitVec 64) <
                           (2 ^ 64 - idx.toNat + sz.toNat) % 2 ^ 64 := by assumption
                       rw [hsubRaw] at hc; change ¬ 3 < sz.toNat - idx.toNat at hc; omega))
                | (refine Eq.mp (congrArg (fun v => Q (v, ()) _) ?_) hQ
                   simp only [hi1', hi2', hi3']
                   have hdec := bv8_decode4_eq bs[idx.toNat] bs[idx.toNat + 1]
                     bs[idx.toNat + 2] bs[idx.toNat + 3]
                     (sh18 := BitVec.signExtend 64 18#32) (sh12 := BitVec.signExtend 64 12#32)
                     (sh6 := BitVec.signExtend 64 6#32)
                     (m0 := 7#64) (m1 := 63#64) (m2 := 63#64) (m3 := 63#64)
                     (by decide) (by decide) (by decide) (by decide)
                     (by decide) (by decide) (by decide)
                   exact hdec.symm)
            · simp only [h1, hb0, hb3, hb4, hlt3, ↓reduceIte] at hQ
              r2b_steps
              all_goals first
                | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 128#64 = 0#64) |> hc1)
                | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 224#64 = 192#64) |> hc2)
                | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 240#64 = 224#64) |> hc3)
                | (exfalso; exact (by assumption : ¬ BitVec.setWidth 64 _ &&& 248#64 = 240#64) hc4)
                | (exfalso; first
                    | (have hc : (3#64).toNat < (sz - idx).toNat := by assumption
                       rw [hsub] at hc; change 3 < sz.toNat - idx.toNat at hc; omega)
                    | (have hc : BitVec.toNat (3 : BitVec 64) <
                           (2 ^ 64 - idx.toNat + sz.toNat) % 2 ^ 64 := by assumption
                       rw [hsubRaw] at hc; change 3 < sz.toNat - idx.toNat at hc; omega))
                | exact hQ
          · have hc4 : (BitVec.setWidth 64 (BitVec.ofNat 8 bs[idx.toNat].toNat) &&& 248#64) ≠
                240#64 :=
              fun heq => hb4 (by simpa [bv8_zext_mask_eq] using congrArg BitVec.toNat heq)
            simp only [h1, hb0, hb3, hb4, ↓reduceIte] at hQ
            r2b_steps
            all_goals first
              | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 128#64 = 0#64) |> hc1)
              | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 224#64 = 192#64) |> hc2)
              | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 240#64 = 224#64) |> hc3)
              | (exfalso; exact (by assumption : BitVec.setWidth 64 _ &&& 248#64 = 240#64) |> hc4)
              | exact hQ

/-! ## 4. Exported WP Proofs (`lcnf_str_alloc`, `lcnf_char_op`) -/

theorem lcnf_str_alloc_wp :
    ∀ xs m Q X, lcnfStrAllocSpec xs m Q X → Func.wp rtR2bEnv lcnf_str_alloc_body xs m Q X := by
  intro ⟨rt, sz, len, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, lcnf_str_alloc_body, lcnfStrAllocSpec] at hPre ⊢
  by_cases hov : strMaxCap ≤ sz.toNat
  · rw [ite_eq_left hov] at hPre
    unfold strMaxCap at hov
    r2b_steps
    exact hPre
  · rw [ite_eq_right hov] at hPre
    rcases hPre with ⟨st, R, hav, hm, hk⟩
    have hlt : sz.toNat < 268435415 := by unfold strMaxCap at hov; omega
    have hcapNat : (sz + 1).toNat = sz.toNat + 1 := by
      simp [BitVec.toNat_add]; omega
    r2b_steps
    r2b_call rtR2bEnv_r2b_str_alloc_cap
    dsimp only [r2bStrAllocCapSpec, vals, Tup.map, Arg.val]
    rw [ite_eq_left (by rw [hcapNat]; unfold strMaxCap; omega)]
    rw [hcapNat]
    exact ⟨st, R, hav, hm, hk⟩

theorem lcnf_char_op_wp :
    ∀ xs m Q X, lcnfCharOpSpec xs m Q X → Func.wp rtR2bEnv lcnf_char_op_body xs m Q X := by
  intro ⟨rt, op, arg, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, lcnf_char_op_body, lcnfCharOpSpec, charOpVal, charOfNatVal] at hPre ⊢
  by_cases h0 : op = 0#64
  · subst h0
    rw [ite_eq_left (Or.inl rfl)] at hPre
    simp only [↓reduceIte] at hPre
    have hsh : (arg >>> BitVec.signExtend 64 1#32) = arg >>> 1 := by
      have h1 : (BitVec.signExtend 64 1#32).toNat = 1 := by decide
      rw [BitVec.ushiftRight_eq', h1]
    have heq : BitVec.ofNat 64 (arg >>> 1).toNat = arg >>> 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (arg >>> 1).isLt]
    by_cases ha0 : (arg &&& 1#64) = 0#64
    · rw [ite_eq_left ha0] at hPre
      r2b_steps
      all_goals first
        | (exfalso; exact (by assumption : ¬ (0#64 : BitVec 64) = 0#64) rfl)
        | (exfalso; exact (by assumption : ¬ arg &&& 1#64 = 0#64) ha0)
        | exact hPre
    · rw [ite_eq_right ha0] at hPre
      by_cases hv1 : (arg >>> 1).toNat < 0xd800
      · have hv : isValidCharNat (arg >>> 1).toNat = true := by
          dsimp only [isValidCharNat]; rw [decide_eq_true hv1, Bool.true_or]
        rw [hv, ite_eq_left rfl, heq] at hPre
        r2b_steps
        all_goals first
          | (exfalso; exact (by assumption : ¬ (0#64 : BitVec 64) = 0#64) rfl)
          | (exfalso; exact ha0 (by assumption : arg &&& 1 = 0))
          | (exfalso; exact (by assumption : ¬ (arg >>> 1).toNat < 55296) hv1)
          | exact hPre
      · by_cases hv2 : 0xe000 ≤ (arg >>> 1).toNat ∧ (arg >>> 1).toNat < 0x110000
        · have hv : isValidCharNat (arg >>> 1).toNat = true := by
            dsimp only [isValidCharNat]
            rw [decide_eq_true hv2.1, decide_eq_true hv2.2, Bool.and_self, Bool.or_true]
          rw [hv, ite_eq_left rfl, heq] at hPre
          r2b_steps
          all_goals first
            | (exfalso; exact (by assumption : ¬ (0#64 : BitVec 64) = 0#64) rfl)
            | (exfalso; exact ha0 (by assumption : arg &&& 1 = 0))
            | (exfalso; exact hv1 (by simpa using (by assumption : (arg >>> 1).toNat < 55296)))
            | (exfalso; exact (by assumption : ¬ BitVec.toNat 57344 ≤ (arg >>> 1).toNat)
                (by simpa using hv2.1))
            | (exfalso; exact (by assumption : ¬ (arg >>> 1).toNat < BitVec.toNat 1114112)
                (by simpa using hv2.2))
            | exact hPre
        · have hv : isValidCharNat (arg >>> 1).toNat = false := by
            simp only [isValidCharNat, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
              decide_eq_false_iff_not]
            exact ⟨hv1, not_and.mp hv2 |> fun h =>
              if hlo : 57344 ≤ (arg >>> 1).toNat then Or.inr (h hlo) else Or.inl hlo⟩
          rw [hv, ite_eq_right (by decide)] at hPre
          r2b_steps
          all_goals first
            | (exfalso; exact (by assumption : ¬ (0#64 : BitVec 64) = 0#64) rfl)
            | (exfalso; exact ha0 (by assumption : arg &&& 1 = 0))
            | (exfalso; exact hv1 (by simpa using (by assumption : (arg >>> 1).toNat < 55296)))
            | (exfalso
               have hlo : 57344 ≤ (arg >>> 1).toNat :=
                 by simpa using (by assumption : BitVec.toNat 57344 ≤ (arg >>> 1).toNat)
               have hhi : (arg >>> 1).toNat < 1114112 :=
                 by simpa using (by assumption : (arg >>> 1).toNat < BitVec.toNat 1114112)
               exact hv2 ⟨hlo, hhi⟩)
            | exact hPre
  · by_cases h1 : op = 1#64
    · subst h1
      rw [ite_eq_left (Or.inr rfl), ite_eq_right (by decide)] at hPre
      r2b_steps
      · r2b_call rtR2bEnv_r2b_utf8_len
        dsimp only [r2bUtf8LenSpec, vals, Tup.map, Arg.val]
        r2b_steps
        unfold boxNat at hPre
        have hbox : ((BitVec.ofNat 64 (utf8LenNat (arg &&& 4294967295).toNat) <<< 1) ||| 1) =
            BitVec.ofNat 64 (2 * utf8LenNat (arg &&& 4294967295#64).toNat + 1) := by
          have hlenLt : utf8LenNat (arg &&& 4294967295#64).toNat ≤ 4 := by
            unfold utf8LenNat; (split <;> try split <;> try split) <;> omega
          rcases hCases : utf8LenNat (arg &&& 4294967295#64).toNat with _ | _ | _ | _ | _ | _
          · simp
          · decide
          · decide
          · decide
          · decide
          · omega
        rw [hbox]
        exact hPre
      · exfalso; exact (by assumption : ¬ (1#64 : BitVec 64) = 1#64) rfl
    · rw [ite_eq_right (fun h => h.elim h0 h1)] at hPre
      r2b_steps
      exact hPre

end LeanQbe.T.LeanLCNF
