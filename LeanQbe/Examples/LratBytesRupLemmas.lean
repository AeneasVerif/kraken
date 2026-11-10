module

public import LeanQbe.Examples.LratBytesSpec
import all Kraken.Mem
import all Kraken.Separation

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.LratRup

/-! ## 1. `readLeb128` pure properties and QBE step lemma -/

private theorem lo7_shift_lt {x sh : Nat} (hsh : sh ≤ 21) :
    (x &&& 127) <<< sh < 2 ^ 28 := by
  rw [Nat.shiftLeft_eq]
  have h1 : x &&& 127 < 2 ^ 7 := Nat.and_lt_two_pow x (n := 7) (by decide)
  have h2 : 2 ^ sh ≤ 2 ^ 21 := Nat.pow_le_pow_right (by omega) hsh
  have h3 : (x &&& 127) * 2 ^ sh < 2 ^ 7 * 2 ^ 21 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h2)
      (Nat.mul_lt_mul_of_pos_right h1 (by decide))
  omega

theorem readLeb128Aux_some {fuel acc sh : Nat} {bs bs' : List UInt8} {u : Nat}
    (hacc : acc < 2 ^ 28) (hsh : sh + 7 * fuel ≤ 28)
    (h : readLeb128Aux fuel acc sh bs = some (u, bs')) :
    u < 2 ^ 28 ∧ ∃ k, 0 < k ∧ k ≤ bs.length ∧ bs' = bs.drop k := by
  induction fuel generalizing acc sh bs with
  | zero => simp [readLeb128Aux] at h
  | succ fuel ih =>
    cases bs with
    | nil => simp [readLeb128Aux] at h
    | cons b rest =>
      have hacc2 : (acc ||| ((b.toNat &&& 127) <<< sh)) < 2 ^ 28 :=
        Nat.or_lt_two_pow hacc (lo7_shift_lt (by omega))
      simp only [readLeb128Aux] at h
      split at h
      · split at h
        · obtain ⟨hu, k, hk0, hkle, rfl⟩ := ih hacc2 (by omega) h
          exact ⟨hu, k + 1, by omega, by simp; omega, by simp⟩
        · simp at h
      · injection h with hp
        injection hp with hu_eq hbs_eq
        subst hu_eq hbs_eq
        exact ⟨hacc2, 1, by omega, by simp, by simp⟩

theorem readLeb128Pure_some {bs bs' : List UInt8} {u : Nat}
    (h : readLeb128Pure bs = some (u, bs')) :
    u < 2 ^ 28 ∧ bs'.length < bs.length ∧
    ∃ k, 0 < k ∧ k ≤ bs.length ∧ bs' = bs.drop k := by
  obtain ⟨hu, k, hk0, hkle, rfl⟩ := readLeb128Aux_some (by decide) (by decide) h
  exact ⟨hu, by simp; omega, k, hk0, hkle, rfl⟩

theorem readLeb128Pure_drop {prfBytes : List UInt8} {idx u : Nat} {bs' : List UInt8}
    (hidx : idx ≤ prfBytes.length)
    (h : readLeb128Pure (prfBytes.drop idx) = some (u, bs')) :
    u < 2 ^ 28 ∧
    bs'.length < (prfBytes.drop idx).length ∧
    prfBytes.length - bs'.length ≤ prfBytes.length ∧
    idx < prfBytes.length - bs'.length ∧
    bs' = prfBytes.drop (prfBytes.length - bs'.length) := by
  obtain ⟨hu, hlt, k, hk0, hkle, hdrop⟩ := readLeb128Pure_some h
  rw [List.length_drop] at hkle hlt
  rw [List.drop_drop] at hdrop
  have hlen' : bs'.length = prfBytes.length - (idx + k) := by
    rw [hdrop, List.length_drop]
  have hidx' : prfBytes.length - bs'.length = idx + k := by omega
  exact ⟨hu, by rw [List.length_drop]; omega, by omega, by omega, by rwa [hidx']⟩

private theorem ptr_eq_iff {base : Val} {i j : Nat}
    (hi : base.toNat + i < 2 ^ 64) (hj : base.toNat + j < 2 ^ 64) :
    base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 j ↔ i = j := by
  constructor
  · intro heq
    have h1 := congrArg BitVec.toNat heq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
      Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h1
    omega
  · rintro rfl; rfl

private theorem ptr_step_1 (base : Val) (i : Nat) :
    base + BitVec.ofNat 64 i + 1 = base + BitVec.ofNat 64 (i + 1) :=
  BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add]; omega)

theorem readLeb128_spec {Γ : Env} {Q : Post} {X : XPost} {fail : Cont}
    {cur pend prf_ptr : Val} {prfBytes : List UInt8} {idx : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {done : Val → Val → Expr Val Cont}
    (hfit : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hidx : idx ≤ prfBytes.length)
    (hcur : cur = prf_ptr + BitVec.ofNat 64 idx)
    (hpend : pend = prf_ptr + BitVec.ofNat 64 prfBytes.length)
    (hm : (Eq (prfBytes.At prf_ptr) ⋆ R) m)
    (hfail : readLeb128Pure (prfBytes.drop idx) = none → fail [] m)
    (hdone : ∀ u bs',
      readLeb128Pure (prfBytes.drop idx) = some (u, bs') →
      u < 2 ^ 28 →
      bs'.length < (prfBytes.drop idx).length →
      bs' = prfBytes.drop (prfBytes.length - bs'.length) →
      idx < prfBytes.length - bs'.length →
      wp Γ Q X (done (BitVec.ofNat 64 u)
        (prf_ptr + BitVec.ofNat 64 (prfBytes.length - bs'.length))) [] [] m) :
    wp Γ Q X (readLeb128 fail cur pend done) [] [] m := by
  subst hcur hpend
  unfold readLeb128
  apply wp_join (fun as m' => ∃ u idx',
    as = [BitVec.ofNat 64 u, prf_ptr + BitVec.ofNat 64 idx'] ∧
    m' = m ∧ idx' ≤ prfBytes.length ∧
    readLeb128Pure (prfBytes.drop idx) = some (u, prfBytes.drop idx'))
  · rintro _ _ ⟨u, idx', rfl, rfl, hidx', hres⟩
    wp_unfold
    obtain ⟨hu, hlt, _, hgt, hdrop⟩ := readLeb128Pure_drop hidx hres
    have heq_idx : prfBytes.length - (prfBytes.drop idx').length = idx' := by
      rw [List.length_drop]; omega
    rw [← heq_idx]
    exact hdone u (prfBytes.drop idx') hres hu hlt hdrop hgt
  · intro Jdone hJdone
    apply wp_loop (fun fuel as m' => ∃ i acc sh,
      1 ≤ fuel ∧ sh + 7 * fuel = 28 ∧ acc < 2 ^ 28 ∧
      i ≤ prfBytes.length ∧ m' = m ∧
      as = [prf_ptr + BitVec.ofNat 64 i, BitVec.ofNat 64 acc, BitVec.ofNat 64 sh] ∧
      readLeb128Pure (prfBytes.drop idx) = readLeb128Aux fuel acc sh (prfBytes.drop i))
    · rintro Jleb fuel as _ ⟨i, acc, sh, hfuel1, hsh_eq, hacc, hi, rfl, rfl, hpure⟩ ih
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      wp_unfold
      refine ⟨fun heof => ?_, fun hneof => ?_⟩
      · have hi_eq : i = prfBytes.length :=
          (ptr_eq_iff (by omega) hfit).mp heof
        subst hi_eq
        rw [List.drop_length] at hpure
        exact hfail hpure
      · have hilt : i < prfBytes.length := by
          rcases Nat.eq_or_lt_of_le hi with rfl | h
          · exact absurd rfl hneof
          · exact h
        have hld := loadub_At hilt (by omega) hm
        refine ⟨_, hld, ?_⟩
        rw [List.drop_eq_getElem_cons hilt] at hpure
        have hb : prfBytes[i].toNat < 256 := prfBytes[i].toNat_lt
        have hsh_lt : sh < 28 := by omega
        have hlo_bv :
            BitVec.ofNat 64 prfBytes[i].toNat &&& 127 =
              BitVec.ofNat 64 (prfBytes[i].toNat &&& 127) := by
          apply BitVec.eq_of_toNat_eq; simp
        have hlo_lt : prfBytes[i].toNat &&& 127 < 128 :=
          Nat.and_lt_two_pow prfBytes[i].toNat (n := 7) (by decide)
        have hsl_lt : (prfBytes[i].toNat &&& 127) <<< sh < 2 ^ 28 :=
          lo7_shift_lt (by omega)
        have hsl_bv :
            BitVec.ofNat 64 (prfBytes[i].toNat &&& 127) <<< ((BitVec.ofNat 64 sh).toNat % 64) =
              BitVec.ofNat 64 ((prfBytes[i].toNat &&& 127) <<< sh) := by
          have hsh_mod : (BitVec.ofNat 64 sh).toNat % 64 = sh := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sh < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : sh < 64)]
          rw [hsh_mod]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : (prfBytes[i].toNat &&& 127) < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : ((prfBytes[i].toNat &&& 127) <<< sh) < 2 ^ 64)]
        have hacc2_lt : (acc ||| ((prfBytes[i].toNat &&& 127) <<< sh)) < 2 ^ 28 :=
          Nat.or_lt_two_pow hacc hsl_lt
        have hacc2_bv :
            BitVec.ofNat 64 acc ||| BitVec.ofNat 64 ((prfBytes[i].toNat &&& 127) <<< sh) =
              BitVec.ofNat 64 (acc ||| ((prfBytes[i].toNat &&& 127) <<< sh)) := by
          apply BitVec.eq_of_toNat_eq; simp
        have hhi_bv :
            BitVec.ofNat 64 prfBytes[i].toNat &&& 128 =
              BitVec.ofNat 64 (prfBytes[i].toNat &&& 128) := by
          apply BitVec.eq_of_toNat_eq; simp
        have hhi_lt : prfBytes[i].toNat &&& 128 < 256 :=
          Nat.and_lt_two_pow prfBytes[i].toNat (n := 8) (by decide)
        rw [hlo_bv, hsl_bv, hacc2_bv, hhi_bv, ptr_step_1]
        refine ⟨fun hmore => ?_, fun hnmore => ?_⟩
        · have hmore_nat : ((prfBytes[i].toNat &&& 128) != 0) = true := by
            rw [bne_iff_ne]
            intro hz; apply hmore; rw [hz]; rfl
          simp only [readLeb128Aux, hmore_nat, ↓reduceIte] at hpure
          have hsh2_bv : BitVec.ofNat 64 sh + 7 = BitVec.ofNat 64 (sh + 7) :=
            BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add])
          rw [hsh2_bv]
          refine ⟨fun hoksh => ?_, fun hnoksh => ?_⟩
          · have hlt28 : sh + 7 < 28 := by
              rw [BitVec.ult, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : sh + 7 < 2 ^ 64)] at hoksh
              simpa using hoksh
            simp only [hlt28, ↓reduceIte] at hpure
            exact ih fuel' _ _ (by omega)
              ⟨i + 1, _, sh + 7, by omega, by omega, hacc2_lt, hilt, rfl, rfl, hpure⟩
          · have hnlt28 : ¬ (sh + 7 < 28) := by
              intro hlt28
              have hult : (BitVec.ofNat 64 (sh + 7)).ult 28 = true := by
                rw [BitVec.ult, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : sh + 7 < 2 ^ 64)]
                simpa using hlt28
              rw [hult] at hnoksh; cases hnoksh
            simp only [hnlt28, ↓reduceIte] at hpure
            exact hfail hpure
        · have hnmore_nat : ((prfBytes[i].toNat &&& 128) != 0) = false := by
            rw [Bool.eq_false_iff, ne_eq, bne_iff_ne, Classical.not_not]
            have h0 : BitVec.ofNat 64 (prfBytes[i].toNat &&& 128) = 0 :=
              Classical.not_not.mp hnmore
            have h0n := congrArg BitVec.toNat h0
            rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : (prfBytes[i].toNat &&& 128) < 2 ^ 64)] at h0n
            exact h0n
          simp only [readLeb128Aux, hnmore_nat, Bool.false_eq_true, ↓reduceIte] at hpure
          exact hJdone _ _ ⟨_, i + 1, rfl, rfl, hilt, hpure⟩
    · intro Jleb hJleb
      wp_unfold
      exact hJleb 4 _ _ ⟨idx, 0, 0, by decide, by decide, by decide, hidx, rfl,
        by simp, rfl⟩

/-! ## 2. `WorkCfg` layout helpers, zig-zag decoding, and `lbReadAddLits_correct` -/

namespace WorkCfg

theorem fit_active (c : WorkCfg) : c.hdr.toNat + c.activeBytes < 2 ^ 64 := by
  have := c.hfit
  unfold activeBytes vBytes tBytes tRaw
  omega

theorem toNat_vb (c : WorkCfg) : c.vb.toNat = c.hdr.toNat + 80 := by
  have := c.fit_active; unfold activeBytes at this
  unfold vb
  rw [BitVec.toNat_add]
  have h80 : (80 : Val).toNat = 80 := rfl
  rw [h80, Nat.mod_eq_of_lt (by omega)]

theorem toNat_tb (c : WorkCfg) : c.tb.toNat = c.vb.toNat + c.vBytes := by
  have := c.fit_active; have := c.toNat_vb; unfold activeBytes at *
  unfold tb
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : c.vBytes < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

theorem toNat_tlim (c : WorkCfg) : c.tlim.toNat = c.tb.toNat + c.tRaw := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have htb : c.tRaw ≤ c.tBytes := by unfold tBytes; omega
  unfold activeBytes at *
  unfold tlim
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : c.tRaw < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

theorem toNat_cb (c : WorkCfg) : c.cb.toNat = c.tb.toNat + c.tBytes := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  unfold activeBytes at *
  unfold cb
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : c.tBytes < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

theorem toNat_pbase (c : WorkCfg) : c.pbase.toNat = c.cb.toNat + 8 * c.cap := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb; have := c.toNat_cb
  unfold activeBytes at *
  unfold pbase
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 8 * c.cap < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

theorem toNat_plim (c : WorkCfg) : c.plim.toNat = c.pbase.toNat + 4 * c.poolInts := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have := c.toNat_cb; have := c.toNat_pbase
  unfold activeBytes at *
  unfold plim
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 4 * c.poolInts < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

end WorkCfg

theorem workState_sep {c : WorkCfg} {poolUsedInts poolRemInts : Nat} {cur : Val}
    {ptrs : List Val} {table : List (Option (List Val))} {PoolUsed F : Mem 64 → Prop}
    {m : Mem 64} :
    (WorkState c poolUsedInts poolRemInts cur ptrs table PoolUsed ⋆ F) m ↔
      poolUsedInts + poolRemInts = c.poolInts ∧
      TableRel c.mv c.cap ptrs table PoolUsed ∧
      (∀ f, PoolUsed f → region c.pbase (4 * poolUsedInts) f) ∧
      ((word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) cur) ⋆
        byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        region c.tb c.tRaw ⋆
        region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb ptrs ⋆
        PoolUsed ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) (4 * poolRemInts)) ⋆ F) m := by
  unfold WorkState; simp only [sep_pure_l]

theorem loadl_hdr {c : WorkCfg} {pcur cur : Val} {sg : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 10)
    (h : (word8Array c.hdr (c.hdrWords pcur cur) ⋆ R) m)
    {a : Val} (ha : a = c.hdr + BitVec.ofNat 64 (8 * i)) :
    loadVal m .l .l sg a =
      some ((c.hdrWords pcur cur)[i]'(by simpa [WorkCfg.hdrWords] using hi)) := by
  subst ha
  exact loadl_word8Array _ h

theorem TableRel.frame_right {mv cap : Nat} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} (P : Mem 64 → Prop)
    (h : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap ptrs table (PoolUsed ⋆ P) := by
  obtain ⟨hplen, htlen, hrel⟩ := h
  refine ⟨hplen, htlen, fun i hi => ?_⟩
  have hi_spec := hrel i hi
  cases hti : table[i]'(htlen ▸ hi) with
  | none =>
    rw [hti] at hi_spec
    exact hi_spec
  | some lits =>
    rw [hti] at hi_spec
    obtain ⟨hne, hv, R_i, hpu⟩ := hi_spec
    exact ⟨hne, hv, R_i ⋆ P, by rw [hpu, sep_assoc]⟩

private theorem zigzag_eq {u : Nat} (hu : u < 2 ^ 28) :
    let v : Val := BitVec.ofNat 64 (u / 2)
    let sbit : Val := BitVec.ofNat 64 u &&& 1
    let mask : Val := 0 - sbit
    (v ^^^ mask) - mask = decodeZigZag u := by
  dsimp only [decodeZigZag]
  have hsbit : BitVec.ofNat 64 u &&& 1 = BitVec.ofNat 64 (u % 2) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : Val).toNat = 1 := rfl
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1,
      Nat.mod_eq_of_lt (by omega : u < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : u % 2 < 2 ^ 64)]
    exact Nat.and_one_is_mod u
  have hmask : (0 : Val) - (BitVec.ofNat 64 u &&& 1) = if u % 2 == 1 then -1 else 0 := by
    rw [hsbit]
    rcases Nat.mod_two_eq_zero_or_one u with h | h <;> rw [h] <;> decide
  rw [hmask, negif]

private theorem isValidLit_ofNat {mv v : Nat} (hv1 : 1 ≤ v) (hvm : v ≤ mv)
    (hmv : mv < dimacsBound) : IsValidLit mv (BitVec.ofNat 64 v) := by
  unfold dimacsBound at hmv
  have hv_lt31 : v < 2 ^ 31 := by omega
  have hv_lt64 : v < 2 ^ 64 := by omega
  have h32 : IsInt32 (BitVec.ofNat 64 v) := by
    unfold IsInt32; grind
  have hne : BitVec.ofNat 64 v ≠ 0 := by
    intro h0
    have h0n := congrArg BitVec.toNat h0
    have h0z : (0 : Val).toNat = 0 := rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv_lt64, h0z] at h0n
    omega
  have hslt : (BitVec.ofNat 64 v).slt 0 = false := by
    unfold BitVec.slt; grind
  refine ⟨h32, hne, ?_, by omega⟩
  unfold bvAbs
  rw [hslt]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv_lt64]
  exact hvm

theorem isValidLit_decodeZigZag {mv u : Nat} (_hu : u < 2 ^ 28)
    (hv1 : 1 ≤ u / 2) (hvm : u / 2 ≤ mv) (hmv : mv < dimacsBound) :
    IsValidLit mv (decodeZigZag u) := by
  unfold decodeZigZag
  have hv := isValidLit_ofNat hv1 hvm hmv
  split
  · exact isValidLit_neg hv
  · exact hv

private theorem region_pop_int4 {a : Val} {rem : Nat} (hrem : 0 < rem)
    (hfit : 4 * rem ≤ 2 ^ 64) {f : Mem 64} (hf : region a (4 * rem) f) :
    ∃ v0 : Val, (int4 a v0 ⋆ region (a + 4) (4 * (rem - 1))) f := by
  have heq : 4 * rem = 4 * 1 + 4 * (rem - 1) := by omega
  rw [heq, region_split (by omega)] at hf
  obtain ⟨f1, f2, hu, hd, hf1, hf2⟩ := hf
  obtain ⟨xs, hxs, h1⟩ := region_to_int4Array 1 (by omega) hf1
  rcases xs with _ | ⟨v0, _ | _⟩ <;> simp at hxs
  simp only [int4Array_cons, int4Array_nil, sep_emp] at h1
  exact ⟨v0, f1, f2, hu, hd, h1, by simpa using hf2⟩

private abbrev wsFixed (c : WorkCfg) (ptrs : List Val) (PoolUsed : Mem 64 → Prop) :
    Mem 64 → Prop :=
  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tb c.tRaw ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆
  word8Array c.cb ptrs ⋆
  PoolUsed

theorem lbReadAddLits_correct (Γ : Env) :
    ∀ args m Q X, lbReadAddLitsSpec args m Q X → Func.spec Γ lbReadAddLits args m Q X := by
  rintro _ m Q X ⟨c, prf_ptr, prfBytes, idx0, poolUsed, poolRem, ptrs, table, PoolUsed, R,
    rfl, hprf_fit, hidx0, hm, hQ⟩
  unfold lbReadAddLits Func.spec
  have hm_ws0 :
      (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆
        (Eq (prfBytes.At prf_ptr) ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨hsum, htbl, hpu, hm_u⟩ := workState_sep.mp hm_ws0
  let c_ptr : Val := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let cur0 : Val := prf_ptr + BitVec.ofNat 64 idx0
  have hpbase_fit : c.pbase.toNat + 4 * c.poolInts < 2 ^ 64 := by
    have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
    have := c.toNat_cb; have := c.toNat_pbase
    unfold WorkCfg.activeBytes at *; omega
  have hcptr_toNat : c_ptr.toNat = c.pbase.toNat + 4 * poolUsed := by
    dsimp only [c_ptr]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 4 * poolUsed < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  have hcptr_ne0 : c_ptr ≠ 0 := by
    intro h0
    have h0n := congrArg BitVec.toNat h0
    have := c.toNat_vb; have := c.toNat_tb; have := c.toNat_cb; have := c.toNat_pbase
    have h0z : (0 : Val).toNat = 0 := rfl
    rw [hcptr_toNat, h0z] at h0n
    omega
  have hm_hdr :
      (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
        (wsFixed c ptrs PoolUsed ⋆ region c_ptr (4 * poolRem) ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m :=
    sep_cast hm_u (by dsimp only [c_ptr, cur0, wsFixed]; ac_rfl)
  wp_unfold
  refine ⟨_, loadl_hdr 0 (by decide) hm_hdr (by simp),
    _, loadl_hdr 7 (by decide) hm_hdr rfl,
    _, loadl_hdr 8 (by decide) hm_hdr rfl,
    _, loadl_hdr 9 (by decide) hm_hdr rfl, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  -- `@fail`: returns 0 when `readAddLitsPure = none` and memory collapses to `region c.hdr c.activeBytes`
  apply wp_join (fun as m' => as = [] ∧
    readAddLitsPure c.mv poolRem (prfBytes.drop idx0) = none ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
  · rintro _ m' ⟨rfl, hnone, hreg⟩
    wp_unfold
    refine hQ 0 m' ?_
    rw [hnone]
    exact ⟨rfl, hreg⟩
  intro Jfail hJfail
  have collapseFail : ∀ (acc : List Val) (rem : Nat) (m' : Mem 64),
      acc.length + rem = poolRem →
      readAddLitsPure c.mv poolRem (prfBytes.drop idx0) = none →
      (Eq (prfBytes.At prf_ptr) ⋆
        (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
          int4Array c_ptr acc.reverse ⋆
          region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m' →
      Jfail [] m' := by
    intro acc rem m' hlen_rem hnone hm'
    have hr_acc : ∀ f, int4Array c_ptr acc.reverse f → region c_ptr (4 * acc.length) f :=
      fun f hf => by
        have := int4Array_to_region (by simp; omega) hf
        simpa using this
    have e_pool :
        (region c_ptr (4 * acc.length) ⋆
          region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) =
        region c_ptr (4 * poolRem) := by
      have : 4 * poolRem = 4 * acc.length + 4 * rem := by omega
      rw [this, region_split (by omega)]
    have hm1 :
        ((word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
          (int4Array c_ptr acc.reverse ⋆
            region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem))) ⋆
          (Eq (prfBytes.At prf_ptr) ⋆ R)) m' := sep_cast hm' (by ac_rfl)
    have hm2 :
        ((word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
          region c_ptr (4 * poolRem)) ⋆
          (Eq (prfBytes.At prf_ptr) ⋆ R)) m' := by
      have hsub : ∀ f,
          (int4Array c_ptr acc.reverse ⋆
            region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) f →
          region c_ptr (4 * poolRem) f := fun f hf => by
        rw [← e_pool]; exact sep_mono hr_acc hf
      exact sep_mono (sep_mono2 (fun _ h => h) hsub) hm1
    have hws' :
        (WorkState c poolUsed poolRem cur0 ptrs table PoolUsed ⋆
          (Eq (prfBytes.At prf_ptr) ⋆ R)) m' :=
      workState_sep.mpr ⟨hsum, htbl, hpu,
        sep_cast hm2 (by dsimp only [c_ptr, wsFixed]; ac_rfl)⟩
    have hreg : (region c.hdr c.activeBytes ⋆ (Eq (prfBytes.At prf_ptr) ⋆ R)) m' :=
      sep_mono (fun _ => WorkState.to_region) hws'
    exact hJfail [] m' ⟨rfl, hnone, sep_cast hreg (by ac_rfl)⟩
  -- `@rd_loop(%cur, %wcur)`
  apply wp_loop (fun fuel as m' => ∃ (idx rem : Nat) (acc : List Val),
    (prfBytes.drop idx).length < fuel ∧
    idx ≤ prfBytes.length ∧
    acc.length + rem = poolRem ∧
    (∀ x ∈ acc, IsValidLit c.mv x) ∧
    as = [prf_ptr + BitVec.ofNat 64 idx, c_ptr + BitVec.ofNat 64 (4 * acc.length)] ∧
    readAddLitsPure c.mv poolRem (prfBytes.drop idx0) =
      readAddLitsAux fuel c.mv rem acc (prfBytes.drop idx) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
        int4Array c_ptr acc.reverse ⋆
        region (c_ptr + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m')
  · rintro Jloop fuel as m' ⟨idx, rem, acc, hfuel_gt, hidx, hrem_sum, hacc_valid, rfl, hpure, hm'⟩ ih
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    let wcur : Val := c_ptr + BitVec.ofNat 64 (4 * acc.length)
    have hwcur_eq : wcur = c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length)) := by
      dsimp only [wcur, c_ptr]
      exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add]; omega)
    wp_unfold
    refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
    · have hrem0 : rem = 0 := by
        have hfull' : wcur = c.plim := hfull
        rw [hwcur_eq] at hfull'
        unfold WorkCfg.plim at hfull'
        have := (ptr_eq_iff (by omega) hpbase_fit).mp hfull'
        omega
      subst hrem0
      simp only [readAddLitsAux, beq_self_eq_true, ↓reduceIte] at hpure
      exact collapseFail acc 0 m' hrem_sum hpure hm'
    · have hrem_pos : 0 < rem := by
        rcases Nat.eq_zero_or_pos rem with rfl | hpos
        · exfalso; apply hnfull
          show wcur = c.plim
          rw [hwcur_eq]; unfold WorkCfg.plim
          exact (ptr_eq_iff (by omega) hpbase_fit).mpr (by omega)
        · exact hpos
      have hrem_b : (rem == 0) = false := by
        rw [beq_eq_false_iff_ne]; omega
      have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
          ((word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
            int4Array c_ptr acc.reverse ⋆
            region wcur (4 * rem)) ⋆ R)) m' :=
        sep_cast hm' (by dsimp only [wcur]; ac_rfl)
      refine readLeb128_spec hprf_fit hidx rfl rfl hm_prf
        (fun hleb_none => ?_)
        (fun u bs' hleb_some hu hlen_lt hbs' hidx_lt => ?_)
      · simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_none] at hpure
        exact collapseFail acc rem m' hrem_sum hpure hm'
      · let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine ⟨fun huz => ?_, fun hnuz => ?_⟩
        · have hu0 : u = 0 := by
            have h0n := congrArg BitVec.toNat huz
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u < 2 ^ 64)] at h0n
            exact h0n
          subst hu0
          simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_some] at hpure
          have hm_reg :
              (region wcur (4 * rem) ⋆
                (Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                  wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr acc.reverse ⋆ R)) m' :=
            sep_cast hm' (by dsimp only [wcur]; ac_rfl)
          obtain ⟨f_r, f_o, hu_m, hd_m, hf_r, hf_o⟩ := hm_reg
          obtain ⟨v0, hf_r'⟩ := region_pop_int4 hrem_pos (by omega) hf_r
          have hm_pop :
              (int4 wcur v0 ⋆
                (region (wcur + 4) (4 * (rem - 1)) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                  wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr acc.reverse ⋆ R)) m' :=
            sep_cast (show ((int4 wcur v0 ⋆ region (wcur + 4) (4 * (rem - 1))) ⋆ _) m' from
              ⟨f_r, f_o, hu_m, hd_m, hf_r', hf_o⟩) (by ac_rfl)
          obtain ⟨ok_z, hm1⟩ := store_int4 0 hm_pop
          refine ⟨ok_z, ?_⟩
          let clits := acc.reverse
          have hzt : (ZeroTermInts c_ptr clits) = (int4Array c_ptr clits ⋆ int4 wcur 0) := by
            rw [zeroTermInts_eq_append]
            have hcl_len : clits.length = acc.length := List.length_reverse
            rw [hcl_len]
          have hm1_hdr :
              (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                (ZeroTermInts c_ptr clits ⋆ region (wcur + 4) (4 * (rem - 1)) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ wsFixed c ptrs PoolUsed ⋆ R))
                (storeMem m' .w wcur 0) := by
            have htmp :
                (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                  ((int4Array c_ptr clits ⋆ int4 wcur 0) ⋆ region (wcur + 4) (4 * (rem - 1)) ⋆
                    Eq (prfBytes.At prf_ptr) ⋆ wsFixed c ptrs PoolUsed ⋆ R))
                  (storeMem m' .w wcur 0) := sep_cast hm1 (by dsimp only [clits]; ac_rfl)
            rwa [← hzt] at htmp
          let cur2 : Val := prf_ptr + BitVec.ofNat 64 idx'
          obtain ⟨ok_p64, hm2⟩ := storel_word8Array (i := 8) (wcur + 4)
            (by simp [WorkCfg.hdrWords]) hm1_hdr
          refine ⟨ok_p64, ?_⟩
          obtain ⟨ok_p72, hm3⟩ := storel_word8Array (i := 9) cur2
            (by simp [WorkCfg.hdrWords]) hm2
          refine ⟨ok_p72, ?_⟩
          let m_end : Mem 64 :=
            storeMem (storeMem (storeMem m' .w wcur 0) .l (c.hdr + 64) (wcur + 4))
              .l (c.hdr + 72) cur2
          have hm3_end :
              (word8Array c.hdr
                (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (clits.length + 1)))) cur2) ⋆
                (ZeroTermInts c_ptr clits ⋆
                  region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (clits.length + 1))))
                    (4 * (rem - 1)) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ wsFixed c ptrs PoolUsed ⋆ R)) m_end := by
            have hhdr_eq :
                (((c.hdrWords c_ptr cur0).set 8 (wcur + 4)).set 9 cur2) =
                  c.hdrWords (wcur + 4) cur2 := rfl
            have hwcur2_eq :
                wcur + 4 = c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (clits.length + 1))) := by
              have hcl_len : clits.length = acc.length := List.length_reverse
              rw [hcl_len, hwcur_eq]
              exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add]; omega)
            have hpred : ∀ mf : Mem 64,
                (word8Array c.hdr (((c.hdrWords c_ptr cur0).set 8 (wcur + 4)).set 9 cur2) ⋆
                  (ZeroTermInts c_ptr clits ⋆ region (wcur + 4) (4 * (rem - 1)) ⋆
                    Eq (prfBytes.At prf_ptr) ⋆ wsFixed c ptrs PoolUsed ⋆ R)) mf →
                (word8Array c.hdr
                  (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (clits.length + 1)))) cur2) ⋆
                  (ZeroTermInts c_ptr clits ⋆
                    region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (clits.length + 1))))
                      (4 * (rem - 1)) ⋆
                    Eq (prfBytes.At prf_ptr) ⋆ wsFixed c ptrs PoolUsed ⋆ R)) mf := by
              intro mf hmf
              rw [hhdr_eq, hwcur2_eq] at hmf
              exact hmf
            exact hpred m_end hm3
          have hpu' : ∀ f, (PoolUsed ⋆ ZeroTermInts c_ptr clits) f →
              region c.pbase (4 * (poolUsed + (clits.length + 1))) f := by
            intro f hf
            have hr_zt : ∀ g, ZeroTermInts c_ptr clits g →
                region c_ptr (4 * (clits.length + 1)) g :=
              fun _ hg => zeroTermInts_to_region (by simp [clits]; omega) hg
            have hboth := sep_mono2 hpu hr_zt f hf
            have heq_p :
                4 * (poolUsed + (clits.length + 1)) =
                  4 * poolUsed + 4 * (clits.length + 1) := by omega
            rw [heq_p, region_split (by simp [clits]; omega)]
            exact hboth
          have hws_done :
              (WorkState c (poolUsed + (clits.length + 1)) (rem - 1) cur2
                ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr clits) ⋆
                (Eq (prfBytes.At prf_ptr) ⋆ R)) m_end := by
            refine workState_sep.mpr ⟨by simp [clits]; omega, TableRel.frame_right _ htbl, hpu', ?_⟩
            exact sep_cast hm3_end (by dsimp only [wsFixed]; ac_rfl)
          have hm_done :
              (Eq (prfBytes.At prf_ptr) ⋆
                WorkState c (poolUsed + (clits.length + 1)) (rem - 1) cur2
                  ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr clits) ⋆ R) m_end :=
            sep_cast hws_done (by ac_rfl)
          have hvalid_clits : ∀ x ∈ clits, IsValidLit c.mv x := by
            intro x hx; exact hacc_valid x (List.mem_reverse.mp hx)
          refine ⟨fun hemp => ?_, fun hnemp => ?_⟩
          · have hlen0 : acc.length = 0 := by
              have h0 : c_ptr + BitVec.ofNat 64 (4 * acc.length) = c_ptr + BitVec.ofNat 64 0 := by
                simpa [wcur] using hemp
              have := (ptr_eq_iff (by rw [hcptr_toNat]; omega) (by rw [hcptr_toNat]; omega)).mp h0
              omega
            have his_emp : acc.reverse.isEmpty = true := by
              simp [List.length_eq_zero_iff.mp hlen0]
            refine hQ 2 _ ?_
            rw [hpure]
            exact ⟨by rw [his_emp]; rfl, hbs', hidx'_le, by rw [List.length_reverse]; omega,
              hcptr_ne0, hvalid_clits, hm_done⟩
          · have hlen_ne0 : acc.length ≠ 0 := by
              intro h0; apply hnemp; show wcur = c_ptr; simp [wcur, h0]
            have his_nemp : acc.reverse.isEmpty = false := by
              cases acc <;> simp at hlen_ne0 ⊢
            refine hQ 1 _ ?_
            rw [hpure]
            exact ⟨by rw [his_nemp]; rfl, hbs', hidx'_le, by rw [List.length_reverse]; omega,
              hcptr_ne0, hvalid_clits, hm_done⟩
        · have hu_ne0 : u ≠ 0 := by
            intro h0; apply hnuz; rw [h0]; rfl
          have hpure_step :
              readAddLitsAux (fuel' + 1) c.mv rem acc (prfBytes.drop idx) =
                (let v := u / 2
                 if v == 0 || c.mv < v then none
                 else readAddLitsAux fuel' c.mv (rem - 1) (decodeZigZag u :: acc) bs') := by
            cases u with
            | zero => exact absurd rfl hu_ne0
            | succ _ => simp only [readAddLitsAux, hrem_b, Bool.false_eq_true, ↓reduceIte, hleb_some]
          rw [hpure_step] at hpure
          have hv_bv : BitVec.ofNat 64 u >>> 1 = BitVec.ofNat 64 (u / 2) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.shiftRight_eq_div_pow,
              Nat.mod_eq_of_lt (by omega : u < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)]
          rw [hv_bv]
          refine ⟨fun hvz => ?_, fun hnvz => ?_⟩
          · have hv0 : u / 2 = 0 := by
              have h0n := congrArg BitVec.toNat hvz
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)] at h0n
              exact h0n
            simp only [hv0, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hpure
            exact collapseFail acc rem m' hrem_sum hpure hm'
          · have hv_pos : 1 ≤ u / 2 := by
              rcases Nat.eq_zero_or_pos (u / 2) with h0 | hpos
              · exfalso; apply hnvz; rw [h0]; rfl
              · exact hpos
            have hv_ne0_b : ((u / 2) == 0) = false := by
              rw [beq_eq_false_iff_ne]; omega
            have hmv_lt64 : c.mv < 2 ^ 64 := by
              have := c.hmv; unfold dimacsBound at this; omega
            refine ⟨fun hvbig => ?_, fun hnvbig => ?_⟩
            · have hmv_lt_v : c.mv < u / 2 := by
                rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hmv_lt64,
                  Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)] at hvbig
                simpa using hvbig
              simp only [hv_ne0_b, hmv_lt_v, decide_true, Bool.false_or, ↓reduceIte] at hpure
              exact collapseFail acc rem m' hrem_sum hpure hm'
            · have hv_le_mv : u / 2 ≤ c.mv := by
                have hnlt : ¬ (c.mv < u / 2) := by
                  intro hlt
                  have hult : (BitVec.ofNat 64 c.mv).ult (BitVec.ofNat 64 (u / 2)) = true := by
                    rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt hmv_lt64,
                      Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)]
                    simpa using hlt
                  rw [hult] at hnvbig; cases hnvbig
                omega
              have hv_le_b : decide (c.mv < u / 2) = false :=
                decide_eq_false (by omega)
              simp only [hv_ne0_b, hv_le_b, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hpure
              rw [zigzag_eq hu]
              have hm_reg :
                  (region wcur (4 * rem) ⋆
                    (Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                      wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr acc.reverse ⋆ R)) m' :=
                sep_cast hm' (by dsimp only [wcur]; ac_rfl)
              obtain ⟨f_r, f_o, hu_m, hd_m, hf_r, hf_o⟩ := hm_reg
              obtain ⟨v0, hf_r'⟩ := region_pop_int4 hrem_pos (by omega) hf_r
              have hm_pop :
                  (int4 wcur v0 ⋆
                    (region (wcur + 4) (4 * (rem - 1)) ⋆
                      Eq (prfBytes.At prf_ptr) ⋆ word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆
                      wsFixed c ptrs PoolUsed ⋆ int4Array c_ptr acc.reverse ⋆ R)) m' :=
                sep_cast (show ((int4 wcur v0 ⋆ region (wcur + 4) (4 * (rem - 1))) ⋆ _) m' from
                  ⟨f_r, f_o, hu_m, hd_m, hf_r', hf_o⟩) (by ac_rfl)
              obtain ⟨ok_lit, hm1⟩ := store_int4 (decodeZigZag u) hm_pop
              refine ⟨ok_lit, ?_⟩
              have harr_snoc :
                  int4Array c_ptr (decodeZigZag u :: acc).reverse =
                    (int4Array c_ptr acc.reverse ⋆ int4 wcur (decodeZigZag u)) := by
                rw [List.reverse_cons, int4Array_append, List.length_reverse]
                simp [wcur, sep_emp]
              have hm1_next :
                  (Eq (prfBytes.At prf_ptr) ⋆
                    (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
                      int4Array c_ptr (decodeZigZag u :: acc).reverse ⋆
                      region (c_ptr + BitVec.ofNat 64 (4 * (decodeZigZag u :: acc).length))
                        (4 * (rem - 1))) ⋆ R)
                    (storeMem m' .w wcur (decodeZigZag u)) := by
                have hwcur_step :
                    wcur + 4 = c_ptr + BitVec.ofNat 64 (4 * (decodeZigZag u :: acc).length) := by
                  simp only [wcur, List.length_cons, ptr4]
                rw [hwcur_step] at hm1
                rw [harr_snoc]
                exact sep_cast hm1 (by ac_rfl)
              have hlit_valid := isValidLit_decodeZigZag hu hv_pos hv_le_mv c.hmv
              refine ih fuel' _ _ (by omega)
                ⟨idx', rem - 1, decodeZigZag u :: acc, ?_, by omega, by simp; omega, ?_,
                  ?_, ?_, hm1_next⟩
              · rw [← hbs']; omega
              · intro x hx
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hlit_valid
                · exact hacc_valid x hx
              · simp only [List.length_cons, ptr4]; rfl
              · rwa [← hbs']
  · intro Jloop hJloop
    wp_unfold
    have hm_init :
        (Eq (prfBytes.At prf_ptr) ⋆
          (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
            int4Array c_ptr ([] : List Val).reverse ⋆
            region (c_ptr + BitVec.ofNat 64 (4 * ([] : List Val).length)) (4 * poolRem)) ⋆ R) m := by
      simp only [List.reverse_nil, int4Array_nil, List.length_nil, Nat.mul_zero, BitVec.add_zero]
      have hemp_r : (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed ⋆ emp) =
          (word8Array c.hdr (c.hdrWords c_ptr cur0) ⋆ wsFixed c ptrs PoolUsed) := by simp [sep_emp]
      rw [hemp_r]
      exact sep_cast hm_u (by dsimp only [c_ptr, cur0, wsFixed]; ac_rfl)
    exact hJloop ((prfBytes.drop idx0).length + 1) _ _
      ⟨idx0, poolRem, [], by omega, hidx0, by simp, by simp,
        by simp [cur0, c_ptr], rfl, hm_init⟩

/-! ## 3. `assignLitChecked_spec`, `rupPhase1_spec`, `rupInner_spec`, and `lbRupCheck_correct` -/

private theorem assignBytes_getD {mv : Nat} (assign : Assignment) {lit : Val}
    (hlit : IsValidLit mv lit) :
    (assignBytes mv assign).getD (bvAbs lit).toNat 0 = assignByte assign (toLiteral lit).1 := by
  have hi : (bvAbs lit).toNat < mv + 1 := by have := hlit.2.2.1; omega
  have hi' : (bvAbs lit).toNat < (assignBytes mv assign).length := by simpa using hi
  simp only [List.getD, List.getElem?_eq_getElem hi', Option.getD_some,
    getElem_assignBytes mv assign hi, toLiteral]

private theorem bv_and_one {u : Nat} (hu : u < 2 ^ 28) :
    BitVec.ofNat 64 u &&& 1 = BitVec.ofNat 64 (u % 2) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : Val).toNat = 1 := rfl
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1,
    Nat.mod_eq_of_lt (by omega : u < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : u % 2 < 2 ^ 64)]
  exact Nat.and_one_is_mod u

private theorem bv_shr_one {u : Nat} (hu : u < 2 ^ 28) :
    BitVec.ofNat 64 u >>> 1 = BitVec.ofNat 64 (u / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : u < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)]

theorem assignLitChecked_spec {Γ : Env} {Q : Post} {X : XPost} {fail : Cont}
    {vb tb tlim te wlit idx : Val} {mv : Nat}
    {assign : Assignment} {trail tf : List Val} {R : Mem 64 → Prop}
    {m : Mem 64} {k : Val → Expr Val Cont}
    (hwlit : IsValidLit mv wlit) (hidx : idx = bvAbs wlit)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb te assign trail tf (mv + 1) ⋆ R) m)
    (hfail : trail.length = mv + 1 → fail [] m)
    (hk : ∀ m' tf',
      trail.length ≠ mv + 1 →
      (PState mv vb tb (te + 4)
        (assign.insert (toLiteral wlit).1 (toLiteral wlit).2)
        (trail ++ [wlit]) tf' (mv + 1) ⋆ R) m' →
      wp Γ Q X (k (te + 4)) [] [] m') :
    wp Γ Q X (assignLitChecked fail vb tlim te wlit idx k) [] [] m := by
  obtain ⟨hte, hcov, htv, hlen, hm0⟩ := pstate_sep.mp hm
  unfold assignLitChecked
  subst hidx hte htlim
  wp_unfold
  refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
  · have h4 : 4 * trail.length = 4 * (mv + 1) :=
      (ptr_eq_iff (by omega) htfit).mp hfull
    exact hfail (by omega)
  · have hne_len : trail.length ≠ mv + 1 := by
      intro heq; apply hnfull; rw [heq]
    rcases tf with _ | ⟨t0, tf'⟩
    · simp at hlen; exact absurd hlen hne_len
    rw [show (BitVec.sshiftRight wlit 63 ||| 1) = bvSignByte wlit from rfl]
    have hi : (toLiteral wlit).1 < (assignBytes mv assign).length := by
      simp [toLiteral]; have := hwlit.2.2.1; omega
    rw [sep_assoc] at hm0
    obtain ⟨ok1, hm1⟩ := storeb_byte1Array (bvSignByte wlit) hi hm0
    rw [assignBytes_set_insert mv assign hwlit, sep_comm_l] at hm1
    obtain ⟨ok2, hm2⟩ := storew_int4Array (i := trail.length) wlit (by simp) hm1
    rw [show (trail ++ t0 :: tf').set trail.length wlit = (trail ++ [wlit]) ++ tf' by
      simp [List.set_append_right]] at hm2
    have ha : vb + bvAbs wlit = vb + BitVec.ofNat 64 (toLiteral wlit).1 := by
      simp [toLiteral]
    rw [ha]
    refine ⟨ok1, ok2, hk _ tf' hne_len
      (pstate_sep.mpr ⟨?_, trailCoversAssign_insert wlit hcov, ?_, ?_, sep_cast hm2 (by ac_rfl)⟩)⟩
    · rw [List.length_append, List.length_singleton]
      exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add]; omega)
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact htv t h
      · rw [List.mem_singleton.mp h]; exact hwlit
    · simp at hlen ⊢; omega

theorem rupPhase1_spec {Γ : Env} {Q : Post} {X : XPost} {fail taut ph2 : Cont}
    {vb tb tlim c_ptr cur0 : Val} {mv : Nat} {clits tf0 : List Val}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ clits, IsValidLit mv x)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb tb Assignment.empty [] tf0 (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m)
    (hfail : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 = .fail →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      fail [] m')
    (htaut : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 = .taut →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      taut [cur0, te] m')
    (hph2 : ∀ m' te assign trail tf,
      rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 =
        .ok (assignBytes mv assign) trail.length →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' →
      ph2 [cur0, te] m') :
    wp Γ Q X (rupPhase1 fail taut ph2 vb tlim c_ptr tb cur0) [] [] m := by
  unfold rupPhase1
  have h32 : ∀ x ∈ clits, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ clits, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  apply wp_loop (fun r as m' => ∃ (i : Nat) (te : Val) (assign : Assignment) (trail tf : List Val),
    as = [c_ptr + BitVec.ofNat 64 (4 * i), te] ∧
    i ≤ clits.length ∧ r = clits.length - i ∧
    (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts c_ptr clits ⋆ R)) m' ∧
    rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 =
      rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trail.length)
  · rintro J r as m' ⟨i, te, assign, trail, tf, rfl, hi, rfl, hm', hpure⟩ ih
    wp_unfold
    obtain ⟨_, _, _, _, hm0⟩ := pstate_sep.mp hm'
    have hld := loadsw_zeroTerm hi h32 (by rw [sep_comm_l] at hm0; exact hm0)
    refine ⟨_, hld, fun hnz => ?_, fun hz => ?_⟩
    · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i)] at hnz
      have hlt := (zeroTermGet_ne_zero_iff hi hne0).mp hnz
      simp only [zeroTermGet, hlt, ↓reduceDIte]
      have hlit := hvalid clits[i] (List.getElem_mem hlt)
      rw [List.drop_eq_getElem_cons hlt] at hpure
      simp only [rupPhase1Pure, assignBytes_getD assign hlit] at hpure
      refine assignedLit_spec hlit (by rw [sep_assoc] at hm0; exact hm0) ?_
      wp_unfold
      refine ⟨fun hneg => ?_, fun hnneg => ?_⟩
      · simp only [hneg, ↓reduceIte] at hpure
        exact ih _ _ _ (by omega) ⟨i + 1, te, assign, trail, tf, by rw [ptr4], hlt, rfl, hm', hpure⟩
      · refine ⟨fun hpos => ?_, fun hnpos => ?_⟩
        · simp only [hnneg, hpos, Bool.false_eq_true, ↓reduceIte] at hpure
          exact htaut m' te assign trail tf hpure hm'
        · rw [show (0 : Val) - clits[i] = -clits[i] by simp]
          refine assignLitChecked_spec (isValidLit_neg hlit) (bvAbs_neg hlit).symm htlim htfit hm'
            (fun hfull => ?_)
            (fun m'' tf' hne_len hm'' => ?_)
          · simp only [hnneg, hnpos, hfull, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hpure
            exact hfail m' te assign trail tf hpure hm'
          · have hfull_f : (trail.length == mv + 1) = false := beq_eq_false_iff_ne.mpr hne_len
            simp only [hnneg, hnpos, hfull_f, Bool.false_eq_true, ↓reduceIte] at hpure
            have hidx_neg : (bvAbs clits[i]).toNat = (toLiteral (-clits[i])).1 := by
              simp [toLiteral, bvAbs_neg hlit]
            rw [hidx_neg, assignBytes_set_insert mv assign (isValidLit_neg hlit)] at hpure
            wp_unfold
            exact ih _ _ _ (by omega)
              ⟨i + 1, te + 4, _, trail ++ [-clits[i]], tf', by rw [ptr4], hlt, rfl, hm'', by simpa using hpure⟩
    · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i), Classical.not_not] at hz
      obtain rfl := (zeroTermGet_eq_zero_iff hi hne0).mp hz
      simp only [List.drop_length, rupPhase1Pure] at hpure
      exact hph2 m' te assign trail tf hpure hm'
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, tb, Assignment.empty, [], tf0, by simp, Nat.zero_le _, rfl, hm,
      by simp [assignBytes_empty]⟩

theorem rupInner_spec {Γ : Env} {Q : Post} {X : XPost} {fail done : Cont}
    {vb tb tlim als te0 : Val} {mv : Nat} {alits : List Val}
    {curAssign : Assignment} {curTrail curTf : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ alits, IsValidLit mv x)
    (htlim : tlim = tb + BitVec.ofNat 64 (4 * (mv + 1)))
    (htfit : tb.toNat + 4 * (mv + 1) < 2 ^ 64)
    (hm : (PState mv vb tb te0 curAssign curTrail curTf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m)
    (hfail : ∀ m' te assign trail tf,
      rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length = none →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' →
      fail [] m')
    (hdone : ∀ m' unit te assign trail tf,
      rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length =
        some (unit, assignBytes mv assign, trail.length) →
      (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' →
      done [unit, te] m') :
    wp Γ Q X (rupInner fail done vb tlim als te0) [] [] m := by
  unfold rupInner
  have h32 : ∀ x ∈ alits, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ alits, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  apply wp_loop (fun r as m' => ∃ (i : Nat) (unit te : Val) (assign : Assignment) (trail tf : List Val),
    as = [als + BitVec.ofNat 64 (4 * i), unit, te] ∧
    i ≤ alits.length ∧ r = alits.length - i ∧
    (PState mv vb tb te assign trail tf (mv + 1) ⋆ (ZeroTermInts als alits ⋆ R)) m' ∧
    rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length =
      rupInnerPure mv (alits.drop i) unit (assignBytes mv assign) trail.length)
  · rintro J r as m' ⟨i, unit, te, assign, trail, tf, rfl, hi, rfl, hm', hpure⟩ ih
    wp_unfold
    obtain ⟨_, _, _, _, hm0⟩ := pstate_sep.mp hm'
    have hld := loadsw_zeroTerm hi h32 (by rw [sep_comm_l] at hm0; exact hm0)
    refine ⟨_, hld, fun hnz => ?_, fun hz => ?_⟩
    · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i)] at hnz
      have hlt := (zeroTermGet_ne_zero_iff hi hne0).mp hnz
      simp only [zeroTermGet, hlt, ↓reduceDIte]
      have hlit := hvalid alits[i] (List.getElem_mem hlt)
      rw [List.drop_eq_getElem_cons hlt] at hpure
      simp only [rupInnerPure, assignBytes_getD assign hlit] at hpure
      refine assignedLit_spec hlit (by rw [sep_assoc] at hm0; exact hm0) ?_
      wp_unfold
      let val := evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]
      refine ⟨fun hneg => ?_, fun hnneg => ?_⟩
      · rw [show (0 : Val) - alits[i] = -alits[i] by simp]
        refine ⟨fun heq => ?_, fun hne => ?_⟩
        · simp only [hneg, heq, beq_self_eq_true, ↓reduceIte] at hpure
          exact hfail m' te assign trail tf hpure hm'
        · have hne_b : (unit == -alits[i]) = false := beq_eq_false_iff_ne.mpr hne
          simp only [hneg, hne_b, Bool.false_eq_true, ↓reduceIte] at hpure
          exact ih _ _ _ (by omega) ⟨i + 1, unit, te, assign, trail, tf, by rw [ptr4], hlt, rfl, hm', hpure⟩
      · simp only [hnneg, Bool.false_eq_true, ↓reduceIte] at hpure
        let stepUnit : Option (Val × List Val × Nat) :=
          if val == 0 then
            if trail.length == mv + 1 then none
            else
              rupInnerPure mv (alits.drop (i + 1)) alits[i]
                ((assignBytes mv assign).set (bvAbs alits[i]).toNat (bvSignByte alits[i]))
                (trail.length + 1)
          else
            rupInnerPure mv (alits.drop (i + 1)) alits[i] (assignBytes mv assign) trail.length
        apply wp_join (fun as m'' => as = [] ∧ m'' = m' ∧
          rupInnerPure mv alits 0 (assignBytes mv curAssign) curTrail.length = stepUnit)
        · rintro _ m_su ⟨rfl, hm_su, hpure_su⟩
          rw [hm_su]
          wp_unfold
          dsimp only [stepUnit, val] at hpure_su
          refine ⟨fun hvz => ?_, fun hnvz => ?_⟩
          · simp only [hvz, beq_self_eq_true, ↓reduceIte] at hpure_su
            refine assignLitChecked_spec hlit rfl htlim htfit hm'
              (fun hfull => ?_)
              (fun m'' tf' hne_len hm'' => ?_)
            · simp only [hfull, beq_self_eq_true, ↓reduceIte] at hpure_su
              exact hfail m' te assign trail tf hpure_su hm'
            · have hfull_f : (trail.length == mv + 1) = false := beq_eq_false_iff_ne.mpr hne_len
              simp only [hfull_f, Bool.false_eq_true, ↓reduceIte] at hpure_su
              have hidx_pos : (bvAbs alits[i]).toNat = (toLiteral alits[i]).1 := rfl
              rw [hidx_pos, assignBytes_set_insert mv assign hlit] at hpure_su
              wp_unfold
              exact ih _ _ _ (by omega)
                ⟨i + 1, alits[i], te + 4, _, trail ++ [alits[i]], tf',
                  by rw [ptr4], hlt, rfl, hm'', by simpa using hpure_su⟩
          · have hvz_f : (val == 0) = false := beq_eq_false_iff_ne.mpr hnvz
            dsimp only [val] at hvz_f
            simp only [hvz_f, Bool.false_eq_true, ↓reduceIte] at hpure_su
            exact ih _ _ _ (by omega)
              ⟨i + 1, alits[i], te, assign, trail, tf, by rw [ptr4], hlt, rfl, hm', hpure_su⟩
        · intro Jsu hJsu
          wp_unfold
          refine ⟨fun htu => ?_, fun hntu => ?_⟩
          · have htu_b : (lo32 unit != 0) = true := bne_iff_ne.mpr htu
            rw [htu_b] at hpure
            refine ⟨fun heq => ?_, fun hne => ?_⟩
            · simp only [heq, beq_self_eq_true, ↓reduceIte] at hpure
              exact hJsu [] m' ⟨rfl, rfl, hpure⟩
            · have hne_b : (unit == alits[i]) = false := beq_eq_false_iff_ne.mpr hne
              simp only [hne_b, Bool.false_eq_true, ↓reduceIte] at hpure
              exact hfail m' te assign trail tf hpure hm'
          · have hntu_b : (lo32 unit != 0) = false := by
              rw [Bool.eq_false_iff, ne_eq, bne_iff_ne]; exact hntu
            simp only [hntu_b, Bool.false_eq_true, ↓reduceIte] at hpure
            exact hJsu [] m' ⟨rfl, rfl, hpure⟩
    · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i), Classical.not_not] at hz
      obtain rfl := (zeroTermGet_eq_zero_iff hi hne0).mp hz
      simp only [List.drop_length, rupInnerPure] at hpure
      exact hdone m' unit te assign trail tf hpure hm'
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, 0, te0, curAssign, curTrail, curTf, by simp, Nat.zero_le _, rfl, hm, rfl⟩

private abbrev wsRupRest (c : WorkCfg) (pcur cur0 : Val) (ptrs : List Val)
    (PoolUsed : Mem 64 → Prop) (poolRem : Nat) : Mem 64 → Prop :=
  word8Array c.hdr (c.hdrWords pcur cur0) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆
  word8Array c.cb ptrs ⋆
  PoolUsed ⋆
  region pcur (4 * poolRem)

private theorem pstate_rupRest_to_region {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur0 te : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {assign : Assignment} {trail tf : List Val} {m : Mem 64}
    (hsum : poolUsed + poolRem = c.poolInts)
    (htbl : TableRel c.mv c.cap ptrs table PoolUsed)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
      wsRupRest c (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur0 ptrs PoolUsed poolRem) m) :
    region c.hdr c.activeBytes m := by
  obtain ⟨_, _, _, hlen, hm0⟩ := pstate_sep.mp hm
  obtain ⟨hplen, _, _⟩ := htbl
  have hfit := c.hfit
  have hmv := c.hmv
  unfold dimacsBound at hmv
  have hvb : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  have r_hdr : ∀ f, word8Array c.hdr (c.hdrWords pcur cur0) f → region c.hdr 80 f := fun f hf => by
    have := word8Array_to_region (by simp [WorkCfg.hdrWords]) hf
    simpa [WorkCfg.hdrWords] using this
  have r_val : ∀ f, byte1Array c.vb (assignBytes c.mv assign) f →
      region c.vb (c.mv + 1) f := fun f hf => by
    have := byte1Array_to_region (by simp; omega) hf
    simpa using this
  have r_tr : ∀ f, int4Array c.tb (trail ++ tf) f → region c.tb c.tRaw f := fun f hf => by
    have htr_len : 4 * (trail ++ tf).length = c.tRaw := by
      unfold WorkCfg.tRaw; rw [List.length_append]; omega
    have := int4Array_to_region (by rw [htr_len]; unfold WorkCfg.tRaw; omega) hf
    rwa [htr_len] at this
  have r_cb : ∀ f, word8Array c.cb ptrs f → region c.cb (8 * c.cap) f := fun f hf => by
    have := word8Array_to_region
      (by rw [hplen]; unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega) hf
    rwa [hplen] at this
  have hm_ord :
      (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
        byte1Array c.vb (assignBytes c.mv assign) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        int4Array c.tb (trail ++ tf) ⋆
        region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb ptrs ⋆
        PoolUsed ⋆
        region pcur (4 * poolRem)) m :=
    sep_cast hm0 (by dsimp only [pcur, wsRupRest]; ac_rfl)
  have hm1 : (region c.hdr 80 ⋆
      region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆
      region c.tlim (c.tBytes - c.tRaw) ⋆
      region c.cb (8 * c.cap) ⋆
      region c.pbase (4 * poolUsed) ⋆
      region pcur (4 * poolRem)) m :=
    sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      r_hdr r_val) (fun _ h => h)) r_tr) (fun _ h => h)) r_cb) hpu) (fun _ h => h) m hm_ord
  have e_pool : (region c.pbase (4 * poolUsed) ⋆ region pcur (4 * poolRem)) =
      region c.pbase (4 * c.poolInts) := by
    have : 4 * c.poolInts = 4 * poolUsed + 4 * poolRem := by omega
    rw [this, region_split (by omega)]
  have e_cb : (region c.cb (8 * c.cap) ⋆ region c.pbase (4 * c.poolInts)) =
      region c.cb (8 * c.cap + 4 * c.poolInts) := by
    conv => rhs; rw [region_split (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  have e_t : (region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw)) = region c.tb c.tBytes := by
    have : c.tBytes = c.tRaw + (c.tBytes - c.tRaw) := by omega
    conv => rhs; rw [this, region_split (by unfold WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  have e_v : (region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) =
      region c.vb c.vBytes := by
    have : c.vBytes = (c.mv + 1) + (c.vBytes - (c.mv + 1)) := by omega
    conv => rhs; rw [this, region_split (by unfold WorkCfg.vBytes at *; omega)]
  have hm2 : (region c.hdr 80 ⋆
      ((region c.vb (c.mv + 1) ⋆ region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) ⋆
        ((region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw)) ⋆
          (region c.cb (8 * c.cap) ⋆ (region c.pbase (4 * poolUsed) ⋆ region pcur (4 * poolRem)))))) m :=
    sep_cast hm1 (by ac_rfl)
  rw [e_v, e_t, e_pool, e_cb] at hm2
  have e_tcb : (region c.tb c.tBytes ⋆ region c.cb (8 * c.cap + 4 * c.poolInts)) =
      region c.tb (c.tBytes + (8 * c.cap + 4 * c.poolInts)) := by
    conv => rhs; rw [region_split (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  have e_vtcb : (region c.vb c.vBytes ⋆ region c.tb (c.tBytes + (8 * c.cap + 4 * c.poolInts))) =
      region c.vb (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) := by
    conv => rhs; rw [region_split (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  have e_all : (region c.hdr 80 ⋆ region c.vb (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts)))) =
      region c.hdr c.activeBytes := by
    have : c.activeBytes = 80 + (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) := by
      unfold WorkCfg.activeBytes; omega
    conv => rhs; rw [this, region_split (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  rwa [e_tcb, e_vtcb, e_all] at hm2

theorem lbRupCheck_correct (Γ : Env) :
    ∀ args m Q X, lbRupCheckSpec args m Q X → Func.spec Γ lbRupCheck args m Q X := by
  rintro _ m Q X ⟨c, id, c_ptr, prf_ptr, prfBytes, idx0, poolUsed, poolRem, clits, ptrs,
    table, PoolUsed, R, rfl, hid_cap, hprf_fit, hidx0, hvalid_c, ⟨R_c, hpu_c⟩, hm, hQ⟩
  unfold lbRupCheck Func.spec
  have hm_ws0 :
      (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆
        (Eq (prfBytes.At prf_ptr) ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨hsum, htbl, hpu, hm_u⟩ := workState_sep.mp hm_ws0
  let pcur : Val := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let cur0 : Val := prf_ptr + BitVec.ofNat 64 idx0
  have hcap_fit : 8 * c.cap < 2 ^ 64 := by
    have := c.fit_active; unfold WorkCfg.activeBytes at this; omega
  have htfit : c.tb.toNat + 4 * (c.mv + 1) < 2 ^ 64 := by
    have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
    have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
    unfold WorkCfg.activeBytes WorkCfg.tRaw at *; omega
  have hm_hdr :
      (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
        (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
          region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆
          region c.tlim (c.tBytes - c.tRaw) ⋆
          word8Array c.cb ptrs ⋆
          PoolUsed ⋆
          region pcur (4 * poolRem) ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m :=
    sep_cast hm_u (by dsimp only [pcur, cur0]; ac_rfl)
  wp_unfold
  refine ⟨_, loadl_hdr 3 (by decide) hm_hdr rfl,
    _, loadl_hdr 4 (by decide) hm_hdr rfl,
    _, loadl_hdr 5 (by decide) hm_hdr rfl,
    _, loadl_hdr 6 (by decide) hm_hdr rfl,
    _, loadl_hdr 9 (by decide) hm_hdr rfl, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  -- `@fail()`
  apply wp_join (fun as m' => as = [] ∧
    rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
  · rintro _ m' ⟨rfl, hnone, hreg⟩
    wp_unfold
    refine hQ 0 m' ?_
    rw [hnone]
    exact ⟨rfl, hreg⟩
  intro Jfail hJfail
  have goFail : ∀ (te : Val) (assign : Assignment) (trail tf : List Val) (m' : Mem 64),
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) = none →
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m' →
      Jfail [] m' := by
    intro te assign trail tf m' hnone hm'
    have hm1 :
        ((PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
          wsRupRest c pcur cur0 ptrs PoolUsed poolRem) ⋆
          (Eq (prfBytes.At prf_ptr) ⋆ R)) m' :=
      sep_cast hm' (by ac_rfl)
    have hreg := sep_mono (fun _ => pstate_rupRest_to_region hsum htbl hpu) hm1
    exact hJfail [] m' ⟨rfl, hnone, sep_cast hreg (by ac_rfl)⟩
  -- `@consume(%ccur, %cte)`
  apply wp_join (fun as m' => ∃ (idx_c : Nat) (cte : Val) (assign : Assignment) (trail tf : List Val),
    as = [prf_ptr + BitVec.ofNat 64 idx_c, cte] ∧
    idx_c ≤ prfBytes.length ∧
    rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
      consumeHintsPure id table (prfBytes.drop idx_c) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      PState c.mv c.vb c.tb cte assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
  · rintro _ m_c ⟨idx_c, cte, assign_c, trail_c, tf_c, rfl, hidx_c, hpure_c, hm_c⟩
    wp_unfold
    -- `@cloop(%p)`
    apply wp_loop (fun fuel as m' => ∃ (idx : Nat),
      (prfBytes.drop idx).length < fuel ∧
      idx ≤ prfBytes.length ∧
      as = [prf_ptr + BitVec.ofNat 64 idx] ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        consumeHintsAux fuel id table (prfBytes.drop idx) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
    · rintro Jcloop fuel as m' ⟨idx, hfuel_gt, hidx, rfl, hpure, hm'⟩ ih
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      wp_unfold
      have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
          (PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m' :=
        sep_cast hm' (by ac_rfl)
      refine readLeb128_spec hprf_fit hidx rfl rfl hm_prf
        (fun hleb_none => ?_)
        (fun u bs' hleb_some hu hlen_lt hbs' _ => ?_)
      · simp only [consumeHintsAux, hleb_none] at hpure
        exact goFail cte assign_c trail_c tf_c m' hpure hm'
      · let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine ⟨fun huz => ?_, fun hnuz => ?_⟩
        · have hu0 : u = 0 := by
            have h0n := congrArg BitVec.toNat huz
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u < 2 ^ 64)] at h0n
            exact h0n
          subst hu0
          simp only [consumeHintsAux, hleb_some] at hpure
          obtain ⟨hte_c, hcov_c, htv_c, hlen_c, hm_ps⟩ := pstate_sep.mp
            (sep_cast hm' (by ac_rfl) :
              (PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
                (Eq (prfBytes.At prf_ptr) ⋆ wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m')
          have hmv_lt := c.hmv
          unfold dimacsBound at hmv_lt
          refine backtrack_spec hte_c htv_c (by omega) hcov_c hm_ps (fun m_bt hm_bt => ?_)
          wp_unfold
          have r_tr : ∀ f, int4Array c.tb (trail_c ++ tf_c) f → region c.tb c.tRaw f := fun f hf => by
            have htr_len : 4 * (trail_c ++ tf_c).length = c.tRaw := by
              unfold WorkCfg.tRaw; rw [List.length_append]; omega
            have := int4Array_to_region (by rw [htr_len]; unfold WorkCfg.tRaw; omega) hf
            rwa [htr_len] at this
          have hm_bt_tr :
              (int4Array c.tb (trail_c ++ tf_c) ⋆
                (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
                  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                  region c.tlim (c.tBytes - c.tRaw) ⋆
                  word8Array c.cb ptrs ⋆ PoolUsed ⋆ region pcur (4 * poolRem) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ R)) m_bt :=
            sep_cast hm_bt (by dsimp only [wsRupRest]; ac_rfl)
          have hm_bt_reg := sep_mono r_tr hm_bt_tr
          have hm_bt_hdr :
              (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
                  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                  region c.tb c.tRaw ⋆
                  region c.tlim (c.tBytes - c.tRaw) ⋆
                  word8Array c.cb ptrs ⋆ PoolUsed ⋆ region pcur (4 * poolRem) ⋆
                  Eq (prfBytes.At prf_ptr) ⋆ R)) m_bt :=
            sep_cast hm_bt_reg (by ac_rfl)
          let p2 : Val := prf_ptr + BitVec.ofNat 64 idx'
          obtain ⟨ok_p72, hm_fin⟩ := storel_word8Array (i := 9) p2
            (by simp [WorkCfg.hdrWords]) hm_bt_hdr
          refine ⟨ok_p72, ?_⟩
          have hhdr_eq : (c.hdrWords pcur cur0).set 9 p2 = c.hdrWords pcur p2 := rfl
          rw [hhdr_eq] at hm_fin
          have hws_fin :
              (WorkState c poolUsed poolRem p2 ptrs table PoolUsed ⋆
                (Eq (prfBytes.At prf_ptr) ⋆ R))
                (storeMem m_bt .l (c.hdr + 72) p2) :=
            workState_sep.mpr ⟨hsum, htbl, hpu, sep_cast hm_fin (by dsimp only [pcur]; ac_rfl)⟩
          refine hQ 1 _ ?_
          rw [hpure]
          exact ⟨rfl, hbs', hidx'_le, sep_cast hws_fin (by ac_rfl)⟩
        · have hu_ne0 : u ≠ 0 := by intro h0; apply hnuz; rw [h0]; rfl
          obtain ⟨u_pred, hu_succ⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
          rw [hu_succ] at hleb_some
          simp only [consumeHintsAux, hleb_some] at hpure
          rw [← hu_succ] at hpure hleb_some
          rw [bv_and_one hu]
          refine ⟨fun hodd => ?_, fun hnodd => ?_⟩
          · have hodd_b : (u % 2 != 0) = true := by
              rw [bne_iff_ne]; intro hz; apply hodd; rw [hz]; rfl
            simp only [hodd_b, ↓reduceIte] at hpure
            exact goFail cte assign_c trail_c tf_c m' hpure hm'
          · have heven : u % 2 = 0 := by
              have h0 : BitVec.ofNat 64 (u % 2) = 0 := Classical.not_not.mp hnodd
              have h0n := congrArg BitVec.toNat h0
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u % 2 < 2 ^ 64)] at h0n
              exact h0n
            have heven_b : (u % 2 != 0) = false := by simp [heven]
            simp only [heven_b, Bool.false_eq_true, ↓reduceIte] at hpure
            rw [bv_shr_one hu]
            let aid := u / 2
            refine ⟨fun hlt_id => ?_, fun hnlt_id => ?_⟩
            · have haid_lt : u / 2 < id := by
                rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)] at hlt_id
                simpa using hlt_id
              have haid_cap : aid < c.cap := by omega
              simp only [haid_lt, ↓reduceIte] at hpure
              have haid_toNat : (BitVec.ofNat 64 (u / 2)).toNat = aid := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)]
              rw [haid_toNat]
              obtain ⟨hplen, htlen, hrel⟩ := htbl
              have hm_cb :
                  (word8Array c.cb ptrs ⋆
                    (Eq (prfBytes.At prf_ptr) ⋆
                      PState c.mv c.vb c.tb cte assign_c trail_c tf_c (c.mv + 1) ⋆
                      word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                      region c.tlim (c.tBytes - c.tRaw) ⋆
                      PoolUsed ⋆ region pcur (4 * poolRem) ⋆ R)) m' :=
                sep_cast hm' (by dsimp only [wsRupRest]; ac_rfl)
              have hld_cb := loadl_word8Array (i := aid) (sg := true) (hplen ▸ haid_cap) hm_cb
              refine ⟨_, hld_cb, fun hact => ?_, fun hnact => ?_⟩
              · have hspec_a := hrel aid haid_cap
                rw [List.getElem?_eq_getElem (htlen ▸ haid_cap)] at hpure
                cases ht_a : table[u / 2]'(htlen ▸ haid_cap) with
                | none =>
                  rw [ht_a] at hspec_a
                  exact absurd hspec_a hact
                | some alits =>
                  simp only [ht_a] at hpure
                  refine ih fuel' _ _ (by omega) ⟨idx', ?_, hidx'_le, rfl, ?_, hm'⟩
                  · rw [← hbs']; omega
                  · rwa [← hbs']
              · have hptr0 : ptrs[aid]'(hplen ▸ haid_cap) = 0 := Classical.not_not.mp hnact
                have hspec_a := hrel aid haid_cap
                rw [List.getElem?_eq_getElem (htlen ▸ haid_cap)] at hpure
                cases ht_a : table[u / 2]'(htlen ▸ haid_cap) with
                | none =>
                  simp only [ht_a] at hpure
                  exact goFail cte assign_c trail_c tf_c m' hpure hm'
                | some alits =>
                  rw [ht_a] at hspec_a
                  exact absurd hptr0 hspec_a.1
            · have hnaid_lt : ¬ (u / 2 < id) := by
                intro hlt
                have hult : (BitVec.ofNat 64 (u / 2)).ult (BitVec.ofNat 64 id) = true := by
                  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)]
                  simpa using hlt
                rw [hult] at hnlt_id; cases hnlt_id
              simp only [hnaid_lt, ↓reduceIte] at hpure
              exact goFail cte assign_c trail_c tf_c m' hpure hm'
    · intro Jcloop hJcloop
      wp_unfold
      exact hJcloop ((prfBytes.drop idx_c).length + 1) _ _
        ⟨idx_c, by omega, hidx_c, rfl, hpure_c, hm_c⟩
  intro Jconsume hJconsume
  -- `@ph2(%hcur, %hte)`
  apply wp_join (fun as m' => ∃ (hte : Val) (assign : Assignment) (trail tf : List Val),
    as = [cur0, hte] ∧
    rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
      rupPhase2Aux ((prfBytes.drop idx0).length + 1) c.mv id table
        (assignBytes c.mv assign) trail.length (prfBytes.drop idx0) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      PState c.mv c.vb c.tb hte assign trail tf (c.mv + 1) ⋆
      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
  · rintro _ m_p2 ⟨hte, assign0, trail0, tf0_p2, rfl, hpure_p2, hm_p2⟩
    wp_unfold
    -- `@outer(%p, %t)`
    apply wp_loop (fun fuel as m' => ∃ (idx : Nat) (te : Val)
      (assign : Assignment) (trail tf : List Val),
      (prfBytes.drop idx).length < fuel ∧
      idx ≤ prfBytes.length ∧
      as = [prf_ptr + BitVec.ofNat 64 idx, te] ∧
      rupCheckPure c.mv id clits table (prfBytes.drop idx0) =
        rupPhase2Aux fuel c.mv id table (assignBytes c.mv assign) trail.length
          (prfBytes.drop idx) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m')
    · rintro Jouter fuel as m' ⟨idx, te, assign, trail, tf, hfuel_gt, hidx, rfl, hpure, hm'⟩ ih
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      wp_unfold
      have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
          (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R)) m' :=
        sep_cast hm' (by ac_rfl)
      refine readLeb128_spec hprf_fit hidx rfl rfl hm_prf
        (fun hleb_none => ?_)
        (fun u bs' hleb_some hu hlen_lt hbs' _ => ?_)
      · simp only [rupPhase2Aux, hleb_none] at hpure
        exact goFail te assign trail tf m' hpure hm'
      · let idx' := prfBytes.length - bs'.length
        have hidx'_le : idx' ≤ prfBytes.length := by omega
        wp_unfold
        refine ⟨fun huz => ?_, fun hnuz => ?_⟩
        · have hu0 : u = 0 := by
            have h0n := congrArg BitVec.toNat huz
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u < 2 ^ 64)] at h0n
            exact h0n
          subst hu0
          simp only [rupPhase2Aux, hleb_some] at hpure
          exact goFail te assign trail tf m' hpure hm'
        · have hu_ne0 : u ≠ 0 := by intro h0; apply hnuz; rw [h0]; rfl
          obtain ⟨u_pred, hu_succ⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
          rw [hu_succ] at hleb_some
          simp only [rupPhase2Aux, hleb_some] at hpure
          rw [← hu_succ] at hpure hleb_some
          rw [bv_and_one hu]
          refine ⟨fun hodd => ?_, fun hnodd => ?_⟩
          · have hodd_b : (u % 2 != 0) = true := by
              rw [bne_iff_ne]; intro hz; apply hodd; rw [hz]; rfl
            simp only [hodd_b, ↓reduceIte] at hpure
            exact goFail te assign trail tf m' hpure hm'
          · have heven : u % 2 = 0 := by
              have h0 : BitVec.ofNat 64 (u % 2) = 0 := Classical.not_not.mp hnodd
              have h0n := congrArg BitVec.toNat h0
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u % 2 < 2 ^ 64)] at h0n
              exact h0n
            have heven_b : (u % 2 != 0) = false := by simp [heven]
            simp only [heven_b, Bool.false_eq_true, ↓reduceIte] at hpure
            rw [bv_shr_one hu]
            let aid := u / 2
            refine ⟨fun hlt_id => ?_, fun hnlt_id => ?_⟩
            · have haid_lt : u / 2 < id := by
                rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)] at hlt_id
                simpa using hlt_id
              have haid_cap : aid < c.cap := by omega
              simp only [haid_lt, ↓reduceIte] at hpure
              have haid_toNat : (BitVec.ofNat 64 (u / 2)).toNat = aid := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)]
              rw [haid_toNat]
              obtain ⟨hplen, htlen, hrel⟩ := htbl
              have hm_cb :
                  (word8Array c.cb ptrs ⋆
                    (Eq (prfBytes.At prf_ptr) ⋆
                      PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
                      word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                      region c.tlim (c.tBytes - c.tRaw) ⋆
                      PoolUsed ⋆ region pcur (4 * poolRem) ⋆ R)) m' :=
                sep_cast hm' (by dsimp only [wsRupRest]; ac_rfl)
              have hld_cb := loadl_word8Array (i := aid) (sg := true) (hplen ▸ haid_cap) hm_cb
              refine ⟨_, hld_cb, fun hact => ?_, fun hnact => ?_⟩
              · have hspec_a := hrel aid haid_cap
                rw [List.getElem?_eq_getElem (htlen ▸ haid_cap)] at hpure
                cases ht_a : table[u / 2]'(htlen ▸ haid_cap) with
                | none =>
                  rw [ht_a] at hspec_a
                  exact absurd hspec_a hact
                | some alits =>
                  rw [ht_a] at hspec_a
                  simp only [ht_a] at hpure
                  obtain ⟨_, hvalid_a, R_a, hpu_a⟩ := hspec_a
                  let als := ptrs[aid]'(hplen ▸ haid_cap)
                  -- `@idone(%unit, %t2)`
                  apply wp_join (fun as m'' => ∃ (unit t2 : Val)
                    (assign2 : Assignment) (trail2 tf2 : List Val),
                    as = [unit, t2] ∧
                    rupInnerPure c.mv alits 0 (assignBytes c.mv assign) trail.length =
                      some (unit, assignBytes c.mv assign2, trail2.length) ∧
                    (Eq (prfBytes.At prf_ptr) ⋆
                      PState c.mv c.vb c.tb t2 assign2 trail2 tf2 (c.mv + 1) ⋆
                      wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m'')
                  · rintro _ m'' ⟨unit, t2, assign2, trail2, tf2, rfl, hinner_ok, hm''⟩
                    wp_unfold
                    simp only [hinner_ok] at hpure
                    refine ⟨fun htu => ?_, fun hntu => ?_⟩
                    · have htu_b : (lo32 unit != 0) = true := bne_iff_ne.mpr htu
                      simp only [htu_b, ↓reduceIte] at hpure
                      refine ih fuel' _ _ (by omega)
                        ⟨idx', t2, assign2, trail2, tf2, ?_, hidx'_le, rfl, ?_, hm''⟩
                      · rw [← hbs']; omega
                      · rwa [← hbs']
                    · have hntu_b : (lo32 unit != 0) = false := by
                        rw [Bool.eq_false_iff, ne_eq, bne_iff_ne]; exact hntu
                      simp only [hntu_b, Bool.false_eq_true, ↓reduceIte] at hpure
                      exact hJconsume _ m''
                        ⟨idx', t2, assign2, trail2, tf2, rfl, hidx'_le, by rwa [← hbs'], hm''⟩
                  · intro Jidone hJidone
                    have hm_in :
                        (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
                          (ZeroTermInts als alits ⋆
                            (R_a ⋆ Eq (prfBytes.At prf_ptr) ⋆
                              word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                              region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                              region c.tlim (c.tBytes - c.tRaw) ⋆
                              word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R))) m' := by
                      have htmp :
                          (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
                            PoolUsed ⋆
                            (Eq (prfBytes.At prf_ptr) ⋆
                              word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                              region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                              region c.tlim (c.tBytes - c.tRaw) ⋆
                              word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R)) m' :=
                        sep_cast hm' (by dsimp only [wsRupRest]; ac_rfl)
                      rw [hpu_a] at htmp
                      exact sep_cast htmp (by dsimp only [als]; ac_rfl)
                    refine rupInner_spec hvalid_a rfl htfit hm_in
                      (fun m'' t2 assign2 trail2 tf2 hinner_none hm''_in => ?_)
                      (fun m'' unit t2 assign2 trail2 tf2 hinner_ok hm''_in => ?_)
                    · simp only [hinner_none] at hpure
                      have hm''_ws :
                          (Eq (prfBytes.At prf_ptr) ⋆
                            PState c.mv c.vb c.tb t2 assign2 trail2 tf2 (c.mv + 1) ⋆
                            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m'' := by
                        have htmp :
                            (PState c.mv c.vb c.tb t2 assign2 trail2 tf2 (c.mv + 1) ⋆
                              (ZeroTermInts als alits ⋆ R_a) ⋆
                              (Eq (prfBytes.At prf_ptr) ⋆
                                word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                                region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                                region c.tlim (c.tBytes - c.tRaw) ⋆
                                word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R)) m'' :=
                          sep_cast hm''_in (by ac_rfl)
                        rw [← hpu_a] at htmp
                        exact sep_cast htmp (by dsimp only [wsRupRest]; ac_rfl)
                      exact goFail t2 assign2 trail2 tf2 m'' hpure hm''_ws
                    · have hm''_ws :
                          (Eq (prfBytes.At prf_ptr) ⋆
                            PState c.mv c.vb c.tb t2 assign2 trail2 tf2 (c.mv + 1) ⋆
                            wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m'' := by
                        have htmp :
                            (PState c.mv c.vb c.tb t2 assign2 trail2 tf2 (c.mv + 1) ⋆
                              (ZeroTermInts als alits ⋆ R_a) ⋆
                              (Eq (prfBytes.At prf_ptr) ⋆
                                word8Array c.hdr (c.hdrWords pcur cur0) ⋆
                                region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                                region c.tlim (c.tBytes - c.tRaw) ⋆
                                word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R)) m'' :=
                          sep_cast hm''_in (by ac_rfl)
                        rw [← hpu_a] at htmp
                        exact sep_cast htmp (by dsimp only [wsRupRest]; ac_rfl)
                      exact hJidone _ m'' ⟨unit, t2, assign2, trail2, tf2, rfl, hinner_ok, hm''_ws⟩
              · have hptr0 : ptrs[aid]'(hplen ▸ haid_cap) = 0 := Classical.not_not.mp hnact
                have hspec_a := hrel aid haid_cap
                rw [List.getElem?_eq_getElem (htlen ▸ haid_cap)] at hpure
                cases ht_a : table[u / 2]'(htlen ▸ haid_cap) with
                | none =>
                  simp only [ht_a] at hpure
                  exact goFail te assign trail tf m' hpure hm'
                | some alits =>
                  rw [ht_a] at hspec_a
                  exact absurd hptr0 hspec_a.1
            · have hnaid_lt : ¬ (u / 2 < id) := by
                intro hlt
                have hult : (BitVec.ofNat 64 (u / 2)).ult (BitVec.ofNat 64 id) = true := by
                  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)]
                  simpa using hlt
                rw [hult] at hnlt_id; cases hnlt_id
              simp only [hnaid_lt, ↓reduceIte] at hpure
              exact goFail te assign trail tf m' hpure hm'
    · intro Jouter hJouter
      wp_unfold
      exact hJouter ((prfBytes.drop idx0).length + 1) _ _
        ⟨idx0, hte, assign0, trail0, tf0_p2, by omega, hidx0, rfl, hpure_p2, hm_p2⟩
  intro Jph2 hJph2
  -- Entry: convert `region c.tb c.tRaw` to `int4Array c.tb tf0` and invoke `rupPhase1_spec`
  have hm_tb :
      (region c.tb (4 * (c.mv + 1)) ⋆
        (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
          wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    have : c.tRaw = 4 * (c.mv + 1) := rfl
    rw [← this]
    exact sep_cast hm_u (by dsimp only [pcur, cur0, wsRupRest]; ac_rfl)
  obtain ⟨f_t, f_o, hu_t, hd_t, hf_t, hf_o⟩ := hm_tb
  have hmv_lt := c.hmv
  unfold dimacsBound at hmv_lt
  obtain ⟨tf0, htf0_len, htf0_arr⟩ := region_to_int4Array (c.mv + 1) (by omega) hf_t
  have hm_arr :
      ((byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆ int4Array c.tb ([] ++ tf0)) ⋆
        (wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m := by
    have h1 : (int4Array c.tb tf0 ⋆
        (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
          wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆
          Eq (prfBytes.At prf_ptr) ⋆ R)) m :=
      ⟨f_t, f_o, hu_t, hd_t, htf0_arr, hf_o⟩
    simpa only [List.nil_append] using sep_cast h1 (by ac_rfl)
  have hm_ps0 :
      (PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
        (wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ Eq (prfBytes.At prf_ptr) ⋆ R)) m :=
    pstate_sep.mpr ⟨by simp, trailCoversAssign_empty c.mv, by simp, by simp [htf0_len], hm_arr⟩
  have hm_p1 :
      (PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
        (ZeroTermInts c_ptr clits ⋆
          (R_c ⋆ Eq (prfBytes.At prf_ptr) ⋆
            word8Array c.hdr (c.hdrWords pcur cur0) ⋆
            region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
            region c.tlim (c.tBytes - c.tRaw) ⋆
            word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R))) m := by
    have htmp :
        (PState c.mv c.vb c.tb c.tb Assignment.empty [] tf0 (c.mv + 1) ⋆
          PoolUsed ⋆
          (Eq (prfBytes.At prf_ptr) ⋆
            word8Array c.hdr (c.hdrWords pcur cur0) ⋆
            region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
            region c.tlim (c.tBytes - c.tRaw) ⋆
            word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R)) m :=
      sep_cast hm_ps0 (by dsimp only [wsRupRest]; ac_rfl)
    rw [hpu_c] at htmp
    exact sep_cast htmp (by ac_rfl)
  have rewrapC : ∀ (te : Val) (assign : Assignment) (trail tf : List Val) (m' : Mem 64),
      (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        (ZeroTermInts c_ptr clits ⋆
          (R_c ⋆ Eq (prfBytes.At prf_ptr) ⋆
            word8Array c.hdr (c.hdrWords pcur cur0) ⋆
            region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
            region c.tlim (c.tBytes - c.tRaw) ⋆
            word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R))) m' →
      (Eq (prfBytes.At prf_ptr) ⋆
        PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
        wsRupRest c pcur cur0 ptrs PoolUsed poolRem ⋆ R) m' := by
    intro te assign trail tf m' hm'
    have htmp :
        (PState c.mv c.vb c.tb te assign trail tf (c.mv + 1) ⋆
          (ZeroTermInts c_ptr clits ⋆ R_c) ⋆
          (Eq (prfBytes.At prf_ptr) ⋆
            word8Array c.hdr (c.hdrWords pcur cur0) ⋆
            region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
            region c.tlim (c.tBytes - c.tRaw) ⋆
            word8Array c.cb ptrs ⋆ region pcur (4 * poolRem) ⋆ R)) m' :=
      sep_cast hm' (by ac_rfl)
    rw [← hpu_c] at htmp
    exact sep_cast htmp (by dsimp only [wsRupRest]; ac_rfl)
  refine rupPhase1_spec hvalid_c rfl htfit hm_p1
    (fun m' te assign trail tf hp1_fail hm' => ?_)
    (fun m' te assign trail tf hp1_taut hm' => ?_)
    (fun m' te assign trail tf hp1_ok hm' => ?_)
  · exact goFail te assign trail tf m' (by unfold rupCheckPure; rw [hp1_fail])
      (rewrapC te assign trail tf m' hm')
  · exact hJconsume _ m' ⟨idx0, te, assign, trail, tf, rfl, hidx0,
      by unfold rupCheckPure; rw [hp1_taut], rewrapC te assign trail tf m' hm'⟩
  · exact hJph2 _ m' ⟨te, assign, trail, tf, rfl,
      by unfold rupCheckPure; rw [hp1_ok], rewrapC te assign trail tf m' hm'⟩

/-! ## 4. Pure RUP soundness (`rupCheckPure_sound`) -/

private theorem cnf_append_left {f1 f2 g : CNF Nat} (h : CNF.Entails f1 f2) :
    CNF.Entails (f1 ++ g) (f2 ++ g) :=
  CNF.entails_append_of_entails (CNF.entails_trans CNF.append_entails_left h)
    CNF.append_entails_right

private theorem unsat_of_entailsClause_all_falsified {F : CNF Nat}
    {initAssign curAssign : Assignment} {c : CNF.Clause Nat}
    (hc : CNF.EntailsClause F c)
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, curAssign.get? lit.1 = some !lit.2) :
    CNF.Unsat (F ++ initAssign.toCNF) := by
  have hF_add : CNF.Entails F (F.add c) := CNF.entails_add_iff.mpr ⟨CNF.entails_refl F, hc⟩
  have hadd_F : CNF.Entails (F.add c) F := (CNF.entails_add_iff.mp (CNF.entails_refl (F.add c))).1
  have hent' : CNF.Entails (F.add c ++ initAssign.toCNF) (F.add c ++ curAssign.toCNF) :=
    CNF.entails_trans (cnf_append_left hadd_F) (CNF.entails_trans hent (cnf_append_left hF_add))
  exact CNF.unsat_of_entails_unsat
    (unsat_of_all_falsified (CNF.mem_add.mpr (Or.inl rfl)) hent' hall)
    (cnf_append_left hF_add)

private theorem entails_insert_of_entailsClause_unit_prop {F : CNF Nat}
    {initAssign curAssign : Assignment} {c : CNF.Clause Nat} {unit : Literal Nat}
    (hc : CNF.EntailsClause F c)
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF))
    (hall : ∀ lit ∈ c, lit = unit ∨ curAssign.get? lit.1 = some !lit.2) :
    CNF.Entails (F ++ initAssign.toCNF) (F ++ (curAssign.insert unit.1 unit.2).toCNF) := by
  have hF_add : CNF.Entails F (F.add c) := CNF.entails_add_iff.mpr ⟨CNF.entails_refl F, hc⟩
  have hadd_F : CNF.Entails (F.add c) F := (CNF.entails_add_iff.mp (CNF.entails_refl (F.add c))).1
  have hent' : CNF.Entails (F.add c ++ initAssign.toCNF) (F.add c ++ curAssign.toCNF) :=
    CNF.entails_trans (cnf_append_left hadd_F) (CNF.entails_trans hent (cnf_append_left hF_add))
  exact CNF.entails_trans (cnf_append_left hF_add)
    (CNF.entails_trans (entails_insert_of_unit_prop (CNF.mem_add.mpr (Or.inl rfl)) hent' hall)
      (cnf_append_left hadd_F))

private theorem rupPhase1Pure_loop_sound {mv : Nat} {clits : List Val}
    (hvalid : ∀ x ∈ clits, IsValidLit mv x) :
    ∀ (rem i : Nat) (assign : Assignment) (trailLen : Nat),
      i ≤ clits.length →
      rem = clits.length - i →
      (∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral ↔ assign.get? x.1 = some !x.2) →
      (rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trailLen = .taut →
        ∃ atom pol, (atom, pol) ∈ toClause clits ∧ (atom, !pol) ∈ toClause clits) ∧
      (∀ vals' trailLen',
        rupPhase1Pure mv (clits.drop i) (assignBytes mv assign) trailLen = .ok vals' trailLen' →
        ∃ assign', vals' = assignBytes mv assign' ∧
          ∀ x : Literal Nat, x ∈ toClause clits ↔ assign'.get? x.1 = some !x.2)
  | 0, i, assign, trailLen, hi, hrem, hinv => by
    obtain rfl : i = clits.length := by omega
    simp only [List.drop_length, rupPhase1Pure]
    refine ⟨fun h => (nomatch h), fun vals' trailLen' h => ?_⟩
    injection h with hvals _
    subst hvals
    rw [List.take_length] at hinv
    exact ⟨assign, rfl, fun x => by rw [← CNF.Clause.mem_literals_iff, literals_toClause, hinv x]⟩
  | rem + 1, i, assign, trailLen, _, hrem, hinv => by
    have hlt : i < clits.length := by omega
    have hlit : IsValidLit mv clits[i] := hvalid clits[i] (List.getElem_mem hlt)
    have hcases := evalAssignedLit_cases assign hlit
    rw [List.drop_eq_getElem_cons hlt]
    simp only [rupPhase1Pure, assignBytes_getD assign hlit]
    cases hneg : (evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i]).slt 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hpos : (0 : Val).slt (evalAssignedLit (assignByte assign (toLiteral clits[i]).1) clits[i])
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hfull : (trailLen == mv + 1)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hidx_neg : (bvAbs clits[i]).toNat = (toLiteral (-clits[i])).1 := by
            simp [toLiteral, bvAbs_neg hlit]
          rw [hidx_neg, assignBytes_set_insert mv assign (isValidLit_neg hlit)]
          have hun := (hcases.2.2 ⟨hneg, hpos⟩).1
          exact rupPhase1Pure_loop_sound hvalid rem (i + 1)
            (assign.insert (toLiteral (-clits[i])).1 (toLiteral (-clits[i])).2)
            (trailLen + 1) hlt (by omega) (phase1_step_insert hlt hlit hinv hun)
        · simp only [↓reduceIte]
          exact ⟨fun h => (nomatch h), fun _ _ h => (nomatch h)⟩
      · simp only [↓reduceIte]
        exact ⟨fun _ => phase1_step_tautology hlt hinv (hcases.2.1 ⟨hneg, hpos⟩),
          fun _ _ h => (nomatch h)⟩
    · simp only [↓reduceIte]
      exact rupPhase1Pure_loop_sound hvalid rem (i + 1) assign trailLen hlt (by omega)
        (phase1_step_already_falsified hlt hinv (hcases.1 hneg))

private def PureInnerSt (mv : Nat) (alits : List Val) (curAssign : Assignment)
    (i : Nat) (unit : Val) (assign : Assignment) : Prop :=
  (unit = 0 ∧ assign = curAssign ∧
    ∀ x : Literal Nat, x ∈ (alits.take i).map toLiteral → curAssign.get? x.1 = some !x.2) ∨
  (unit ≠ 0 ∧ IsValidLit mv unit ∧ assign.get? (toLiteral unit).1 = some (toLiteral unit).2 ∧
    ((curAssign.get? (toLiteral unit).1 = none ∧
      assign = curAssign.insert (toLiteral unit).1 (toLiteral unit).2) ∨ assign = curAssign) ∧
    ∀ x : Literal Nat, x ∈ (alits.take i).map toLiteral →
      x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2)

private theorem lo32_bne_zero_of_valid {mv : Nat} {unit : Val}
    (hu : unit ≠ 0) (huv : IsValidLit mv unit) :
    (lo32 unit != 0) = true :=
  bne_iff_ne.mpr ((truthy_iff unit huv.1).mpr hu)

private theorem rupInnerPure_loop_sound {mv : Nat} {alits : List Val} {F : CNF Nat}
    {initAssign curAssign : Assignment}
    (hvalid : ∀ x ∈ alits, IsValidLit mv x)
    (hcl : CNF.EntailsClause F (toClause alits))
    (hent : CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF)) :
    ∀ (rem i : Nat) (unit : Val) (assign : Assignment) (trailLen : Nat)
      (unit' : Val) (vals' : List Val) (trailLen' : Nat),
      i ≤ alits.length →
      rem = alits.length - i →
      PureInnerSt mv alits curAssign i unit assign →
      rupInnerPure mv (alits.drop i) unit (assignBytes mv assign) trailLen =
        some (unit', vals', trailLen') →
      ((lo32 unit' != 0) = false ∧ CNF.Unsat (F ++ initAssign.toCNF)) ∨
      ((lo32 unit' != 0) = true ∧ ∃ assign', vals' = assignBytes mv assign' ∧
        CNF.Entails (F ++ initAssign.toCNF) (F ++ assign'.toCNF))
  | 0, i, unit, assign, trailLen, unit', vals', trailLen', hi, hrem, hst, hres => by
    obtain rfl : i = alits.length := by omega
    simp only [List.drop_length, rupInnerPure] at hres
    cases hres
    rw [PureInnerSt, List.take_length] at hst
    rcases hst with ⟨rfl, rfl, hall⟩ | ⟨hu, huv, _, hrel, hinv⟩
    · refine Or.inl ⟨by decide, unsat_of_entailsClause_all_falsified hcl hent fun x hx => ?_⟩
      rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx
      exact hall x hx
    · refine Or.inr ⟨lo32_bne_zero_of_valid hu huv, assign, rfl, ?_⟩
      rcases hrel with ⟨_, rfl⟩ | rfl
      · exact entails_insert_of_entailsClause_unit_prop hcl hent fun x hx => by
          rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx
          exact hinv x hx
      · exact hent
  | rem + 1, i, unit, assign, trailLen, unit', vals', trailLen', _, hrem, hst, hres => by
    have hlt : i < alits.length := by omega
    have hlit : IsValidLit mv alits[i] := hvalid alits[i] (List.getElem_mem hlt)
    have hcases := evalAssignedLit_cases assign hlit
    rw [List.drop_eq_getElem_cons hlt] at hres
    simp only [rupInnerPure, assignBytes_getD assign hlit] at hres
    cases hneg : (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]).slt 0
    · simp only [hneg, Bool.false_eq_true, ↓reduceIte] at hres
      let stepUnit : Option (Val × List Val × Nat) :=
        if evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] == 0 then
          if trailLen == mv + 1 then none
          else
            rupInnerPure mv (alits.drop (i + 1)) alits[i]
              ((assignBytes mv assign).set (bvAbs alits[i]).toNat (bvSignByte alits[i]))
              (trailLen + 1)
        else
          rupInnerPure mv (alits.drop (i + 1)) alits[i] (assignBytes mv assign) trailLen
      have hsu : (unit = 0 ∨ unit = alits[i]) ∧ stepUnit = some (unit', vals', trailLen') := by
        rcases hst with ⟨rfl, _⟩ | ⟨hu, huv, _⟩
        · have hz : (lo32 (0 : Val) != 0) = false := by decide
          simp only [hz, Bool.false_eq_true, ↓reduceIte] at hres
          exact ⟨Or.inl rfl, hres⟩
        · rw [lo32_bne_zero_of_valid hu huv] at hres
          simp only [↓reduceIte] at hres
          cases heq : (unit == alits[i])
          · simp [heq] at hres
          · simp only [heq, ↓reduceIte] at hres
            exact ⟨Or.inr (eq_of_beq heq), hres⟩
      obtain ⟨hu_cases, hres_su⟩ := hsu
      dsimp only [stepUnit] at hres_su
      cases hvz : (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] == 0)
      · have hnv0 : evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] ≠ 0 :=
          beq_eq_false_iff_ne.mp hvz
        simp only [hvz, Bool.false_eq_true, ↓reduceIte] at hres_su
        have hpos : (0 : Val).slt
            (evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i]) = true := by
          cases hp : (0 : Val).slt _
          · exact absurd (hcases.2.2 ⟨hneg, hp⟩).2 hnv0
          · rfl
        have hsat := hcases.2.1 ⟨hneg, hpos⟩
        have hst' : PureInnerSt mv alits curAssign (i + 1) alits[i] assign := by
          rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu, huv, hus, hrel, hinv⟩
          · exact Or.inr ⟨hlit.2.1, hlit, hsat, Or.inr rfl, phase2_inner_new_unit hlt hinv⟩
          · rcases hu_cases with rfl | rfl
            · exact absurd rfl hu
            · exact Or.inr ⟨hu, huv, hus, hrel, phase2_inner_dup_unit hlt rfl hinv⟩
        exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) alits[i] assign trailLen
          unit' vals' trailLen' hlt (by omega) hst' hres_su
      · have hv0 : evalAssignedLit (assignByte assign (toLiteral alits[i]).1) alits[i] = 0 :=
          eq_of_beq hvz
        have hun : assign.get? (toLiteral alits[i]).1 = none :=
          (hcases.2.2 ⟨hneg, by rw [hv0]; decide⟩).1
        simp only [hvz, ↓reduceIte] at hres_su
        cases hfull : (trailLen == mv + 1)
        · simp only [hfull, Bool.false_eq_true, ↓reduceIte] at hres_su
          rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu, _, hus, _, _⟩
          · have hidx_pos : (bvAbs alits[i]).toNat = (toLiteral alits[i]).1 := rfl
            rw [hidx_pos, assignBytes_set_insert mv assign hlit] at hres_su
            have hst' : PureInnerSt mv alits assign (i + 1) alits[i]
                (assign.insert (toLiteral alits[i]).1 (toLiteral alits[i]).2) :=
              Or.inr ⟨hlit.2.1, hlit, Assignment.get?_insert_of_eq rfl,
                Or.inl ⟨hun, rfl⟩, phase2_inner_new_unit hlt hinv⟩
            exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) alits[i]
              (assign.insert (toLiteral alits[i]).1 (toLiteral alits[i]).2)
              (trailLen + 1) unit' vals' trailLen' hlt (by omega) hst' hres_su
          · rcases hu_cases with rfl | rfl
            · exact absurd rfl hu
            · rw [hun] at hus; nomatch hus
        · simp [hfull] at hres_su
    · have hfals := hcases.1 hneg
      simp only [hneg, ↓reduceIte] at hres
      cases heq : (unit == -alits[i])
      · have hne : unit ≠ -alits[i] := beq_eq_false_iff_ne.mp heq
        simp only [heq, Bool.false_eq_true, ↓reduceIte] at hres
        have hst' : PureInnerSt mv alits curAssign (i + 1) unit assign := by
          rcases hst with ⟨rfl, rfl, hinv⟩ | ⟨hu, huv, hus, hrel, hinv⟩
          · exact Or.inl ⟨rfl, rfl, phase2_inner_falsified_unit0 hlt hinv hfals⟩
          · exact Or.inr ⟨hu, huv, hus, hrel,
              phase2_inner_falsified_unit_ne0 hlt hlit hus hrel hinv hfals hne⟩
        exact rupInnerPure_loop_sound hvalid hcl hent rem (i + 1) unit assign trailLen
          unit' vals' trailLen' hlt (by omega) hst' hres
      · simp [heq] at hres

private theorem rupPhase2Aux_sound {mv id : Nat} {table : List (Option (List Val))} {F : CNF Nat}
    {initAssign : Assignment}
    (htable : ∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
      (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits)) :
    ∀ (fuel : Nat) (curAssign : Assignment) (trailLen : Nat) (bs bs_out : List UInt8),
      CNF.Entails (F ++ initAssign.toCNF) (F ++ curAssign.toCNF) →
      rupPhase2Aux fuel mv id table (assignBytes mv curAssign) trailLen bs = some bs_out →
      CNF.Unsat (F ++ initAssign.toCNF)
  | 0, _, _, _, _, _, hp2 => nomatch hp2
  | fuel + 1, curAssign, trailLen, bs, bs_out, hent, hp2 => by
    cases hleb : readLeb128Pure bs with
    | none => simp only [rupPhase2Aux, hleb] at hp2; nomatch hp2
    | some p =>
      rcases p with ⟨u, bs'⟩
      cases u with
      | zero => simp only [rupPhase2Aux, hleb] at hp2; nomatch hp2
      | succ u_pred =>
        simp only [rupPhase2Aux, hleb] at hp2
        cases hodd : ((u_pred + 1) % 2 != 0)
        · rw [hodd] at hp2
          simp only [Bool.false_eq_true, ↓reduceIte] at hp2
          by_cases haid : (u_pred + 1) / 2 < id
          · simp only [haid, ↓reduceIte] at hp2
            cases htbl : table[(u_pred + 1) / 2]? with
            | none => simp only [htbl] at hp2; nomatch hp2
            | some opt =>
              cases opt with
              | none => simp only [htbl] at hp2; nomatch hp2
              | some alits =>
                simp only [htbl] at hp2
                obtain ⟨halits_valid, halits_ent⟩ := htable ((u_pred + 1) / 2) haid alits htbl
                cases hinner : rupInnerPure mv alits 0 (assignBytes mv curAssign) trailLen with
                | none => simp only [hinner] at hp2; nomatch hp2
                | some res =>
                  rcases res with ⟨unit, vals', trailLen'⟩
                  simp only [hinner] at hp2
                  have hsound := rupInnerPure_loop_sound halits_valid halits_ent hent
                    alits.length 0 0 curAssign trailLen unit vals' trailLen'
                    (Nat.zero_le _) (by simp) (Or.inl ⟨rfl, rfl, by simp⟩)
                    (by simpa using hinner)
                  rcases hsound with ⟨_, hunsat⟩ | ⟨hu_t, assign', rfl, hent'⟩
                  · exact hunsat
                  · simp only [hu_t, ↓reduceIte] at hp2
                    exact rupPhase2Aux_sound htable fuel assign' trailLen' bs' bs_out hent' hp2
          · simp [haid] at hp2
        · rw [hodd] at hp2; nomatch hp2

theorem rupCheckPure_sound {mv id : Nat} {clits : List Val}
    {table : List (Option (List Val))} {bs bs' : List UInt8} {F : CNF Nat}
    (hmv : mv < dimacsBound)
    (hclits : ∀ x ∈ clits, IsValidLit mv x)
    (htable : ∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
      (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits))
    (hrup : rupCheckPure mv id clits table bs = some bs') :
    CNF.EntailsClause F (toClause clits) := by
  let _ := hmv
  unfold rupCheckPure at hrup
  have he : List.replicate (mv + 1) (0 : Val) = assignBytes mv Assignment.empty :=
    (assignBytes_empty mv).symm
  rw [he] at hrup
  have hp1_sound := rupPhase1Pure_loop_sound hclits clits.length 0 Assignment.empty 0
    (Nat.zero_le _) (by simp) (by simp)
  rw [List.drop_zero] at hp1_sound
  cases hp1 : rupPhase1Pure mv clits (assignBytes mv Assignment.empty) 0 with
  | fail => rw [hp1] at hrup; nomatch hrup
  | taut => exact entailsClause_of_tautology (hp1_sound.1 hp1)
  | ok vals trailLen =>
    rw [hp1] at hrup
    dsimp only at hrup
    obtain ⟨initAssign, rfl, hiff⟩ := hp1_sound.2 vals trailLen hp1
    exact entailsClause_of_unsat_of_iff_falsified hiff
      (rupPhase2Aux_sound htable (bs.length + 1) initAssign trailLen bs bs'
        (CNF.entails_refl _) hrup)

end LeanQbe.LratBytes
