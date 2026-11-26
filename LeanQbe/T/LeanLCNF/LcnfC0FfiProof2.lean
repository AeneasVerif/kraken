module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiProof1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proofs for `LcnfC0Ffi`, Part 2: Sentineled `Nat` & Bidirectional Bridges

Proves `Func.wp ffiEnv` contracts (`0` `import all`, `0` `@[expose]` on theorems/lemmas,
`XPost := False` / `noExit := true`) for the 7 sentineled-`Nat` and bridge FFI adapters:
- `lcnf_ffi_sentinel_byte_idx` (`lcnf_ffi_sentinel_byte_idx_wp`)
- `lcnf_ffi_nat_bytes_len` (`lcnf_ffi_nat_bytes_len_wp`)
- `lcnf_ffi_nat_bytes_ptr` (`lcnf_ffi_nat_bytes_ptr_wp`)
- `lcnf_ffi_nat_of_bytes` (`lcnf_ffi_nat_of_bytes_wp`)
- `lcnf_ffi_nat_wrap_ok` (`lcnf_ffi_nat_wrap_ok_wp`)
- `lcnf_ffi_ba_to_nat_s` (`lcnf_ffi_ba_to_nat_s_wp`)
- `lcnf_ffi_nat_s_to_ba` (`lcnf_ffi_nat_s_to_ba_wp`)
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

local macro "ffi2_steps" : tactic =>
  `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hsteps))
local macro "ffi2_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_); try c0_let_simp))

/-! ## 1. Local Memory Rules, `BitVec` Byte/Shift Algebra, and `MPZ` Helpers -/

@[local c0_load] private theorem ffi2_load_rt_cur {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    loadVal m i64 (rt + 33552) = some st.hdr.s_cur :=
  LcnfC0Rt.load_s_cur (rtC0Inv_hdr_focus1 hm)

@[local c0_load] private theorem ffi2_load_rt_end {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (rtC0Inv rt st ⋆ R) m) :
    loadVal m i64 (rt + 33560) = some st.hdr.s_end :=
  LcnfC0Rt.load_s_end (rtC0Inv_hdr_focus1 hm)

@[local c0_load] private theorem ffi2_load_cell64_add8 {a v : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (cell64 (a + 8#64) v ⋆ R) m) :
    loadVal m i64 (a + 8) = some v :=
  r2_c0_load_cell64_add8 hm

private theorem ffi2_sub_rem_eq (st : RtC0State) :
    (2 ^ 64 - st.hdr.s_cur.toNat + st.hdr.s_end.toNat) % 2 ^ 64 = st.rem := by
  have h1 : (st.hdr.s_end - st.hdr.s_cur).toNat =
      (2 ^ 64 - st.hdr.s_cur.toNat + st.hdr.s_end.toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_sub]
  have h2 : (st.hdr.s_end - st.hdr.s_cur).toNat = st.rem := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr st.curLeEnd)]; rfl
  exact h1.symm.trans h2

private theorem ffi2_sz_rhs_eq (len : BitVec 64)
    (hmax : len.toNat ≤ ffiNatMaxBytes) (hgt : 7 < len.toNat) :
    ((16 : BitVec 64).toNat + (8 : BitVec 64).toNat *
      ((len.toNat / 2 ^ (OfNat.ofNat 3 : Nat) + (1 : BitVec 64).toNat) % 2 ^ 64)) % 2 ^ 64 =
      natSAllocBytes len.toNat := by
  have hnl : len.toNat / 8 + 1 < 2 ^ 64 := by unfold ffiNatMaxBytes at hmax; omega
  have hsz : 16 + 8 * (len.toNat / 8 + 1) < 2 ^ 64 := by unfold ffiNatMaxBytes at hmax; omega
  change (16 + 8 * ((len.toNat / 8 + 1) % 2 ^ 64)) % 2 ^ 64 = natSAllocBytes len.toNat
  unfold natSAllocBytes natSLimbCount
  rw [ite_eq_right (by omega : ¬ len.toNat ≤ 7), Nat.mod_eq_of_lt hnl, Nat.mod_eq_of_lt hsz]

private theorem ffi2_wrap_sz_rhs_eq (len : BitVec 64)
    (hmax : len.toNat ≤ ffiNatMaxBytes) (hgt : 7 < len.toNat) :
    ((16 : BitVec 64).toNat + (8 : BitVec 64).toNat *
      ((len.toNat / 2 ^ (OfNat.ofNat 3 : Nat) + (1 : BitVec 64).toNat) % 2 ^ 64) +
      (16 : BitVec 64).toNat) % 2 ^ 64 =
      natSAllocBytes len.toNat + 16 := by
  have hnl : len.toNat / 8 + 1 < 2 ^ 64 := by unfold ffiNatMaxBytes at hmax; omega
  have hsz : 16 + 8 * (len.toNat / 8 + 1) + 16 < 2 ^ 64 := by
    unfold ffiNatMaxBytes at hmax; omega
  change (16 + 8 * ((len.toNat / 8 + 1) % 2 ^ 64) + 16) % 2 ^ 64 = natSAllocBytes len.toNat + 16
  unfold natSAllocBytes natSLimbCount
  rw [ite_eq_right (by omega : ¬ len.toNat ≤ 7), Nat.mod_eq_of_lt hnl, Nat.mod_eq_of_lt hsz]

@[local c0_load] private theorem ffi_load_scratch {rt scr : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (cell64 (rt + 33672#64) scr ⋆ R) m) :
    loadVal m i64 (rt + 33672) = some scr :=
  loadVal_cell64 hm

@[local c0_load] private theorem ffi_load_scratch_cap {rt cap : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (cell64 (rt + 33680#64) cap ⋆ R) m) :
    loadVal m i64 (rt + 33680) = some cap :=
  loadVal_cell64 hm

@[local c0_load] private theorem ffi_load_array64_zero {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (array64 a xs ⋆ R) m) (h0 : 0 < xs.length) :
    loadVal m i64 a = some xs[0] := by
  simpa using loadVal_array64 (i := 0) h0 hm

@[local c0_store] private theorem ffi_store_array64_zero {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (hm : (array64 a xs ⋆ R) m)
    (h0 : 0 < xs.length) :
    storeOk m i64 a ∧ (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 a v) := by
  simpa using store_array64 (i := 0) v h0 hm

@[local c0_load] private theorem ffi_load_array64_sub1_mul8 {a n : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (hm : (array64 a xs ⋆ R) m)
    (hpos : 0 < n.toNat) (hle : n.toNat ≤ xs.length) :
    loadVal m i64 (a + (n - 1) * 8) = some (xs[n.toNat - 1]'(by omega)) := by
  have hsub : (n - 1 : BitVec 64).toNat = n.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hpos)]
    rfl
  have hmul : ((n - 1 : BitVec 64) * 8) = BitVec.ofNat 64 (8 * (n.toNat - 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, hsub, show (8 : BitVec 64).toNat = 8 from rfl, BitVec.toNat_ofNat,
      Nat.mul_comm]
  rw [hmul]
  exact loadVal_array64 (by omega) hm

@[local c0_load] private theorem ffi_load_array64_sub1_shl3 {a n : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (hm : (array64 a xs ⋆ R) m)
    (hpos : 0 < n.toNat) (hle : n.toNat ≤ xs.length) :
    loadVal m i64 (a + ((n - 1) <<< 3)) = some (xs[n.toNat - 1]'(by omega)) := by
  have hsub : (n - 1 : BitVec 64).toNat = n.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hpos)]
    rfl
  have hshl : ((n - 1 : BitVec 64) <<< 3) = BitVec.ofNat 64 (8 * (n.toNat - 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, hsub, Nat.shiftLeft_eq, show (2 ^ 3 : Nat) = 8 from rfl,
      BitVec.toNat_ofNat, Nat.mul_comm]
  rw [hshl]
  exact loadVal_array64 (by omega) hm

theorem ffi2_lcnfObjMem_mpz_eq {o : LcnfObj} (h : o.tag = mpzTag) :
    lcnfObjMem o =
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) o.mpzMeta ⋆
        array64 (o.addr + 16#64) o.limbs) := by
  simp [lcnfObjMem, h, show mpzTag ≠ closureTag by decide, show mpzTag ≠ arrayTag by decide,
    show mpzTag ≠ sarrayTag by decide, show mpzTag ≠ stringTag by decide]

@[local c0_load] private theorem ffi_load_mpz_meta {o : LcnfObj} (htag : o.tag = mpzTag)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8) = some o.mpzMeta := by
  rw [ffi2_lcnfObjMem_mpz_eq htag] at hm
  exact r2_c0_load_cell64_add8 (sep_ac hm : (cell64 (o.addr + 8#64) o.mpzMeta ⋆
    (cell64 o.addr o.header ⋆ array64 (o.addr + 16#64) o.limbs ⋆ R)) m)

theorem mpzMeta_shr32_of_obj (o : LcnfObj) (hcap : o.cap < 2 ^ 32) (harr : o.arrSize < 2 ^ 32) :
    (o.mpzMeta >>> 32) = BitVec.ofNat 64 o.arrSize := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hm : o.mpzMeta = BitVec.ofNat 64 o.cap ||| (BitVec.ofNat 64 o.arrSize <<< 32) := rfl
  rw [hm]
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat]
  by_cases hi32 : i < 32
  · have hcf : o.cap.testBit (32 + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcap (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [show i < 64 by omega, show 32 + i < 64 by omega, hcf]
  · have haf : o.arrSize.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le harr (Nat.pow_le_pow_right (by decide) (by omega)))
    have hnot : ¬ (32 + i < 64) := by omega
    by_cases hi64 : i < 64 <;> simp [hi64, haf, hnot]

theorem bv64_shr_mul8_and_ff (w k : BitVec 64) (hk : k.toNat < 8) :
    ((w >>> (8 * k)) &&& 255#64).toNat = (w.toNat / 2 ^ (8 * k.toNat)) % 256 := by
  have hmul : (8 * k : BitVec 64).toNat = 8 * k.toNat := by
    rw [BitVec.toNat_mul, show (8 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_and, show (255#64 : BitVec 64).toNat = 2 ^ 8 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod,
    show (w >>> (8 * k)) = w >>> (8 * k).toNat from rfl,
    BitVec.toNat_ushiftRight, hmul, Nat.shiftRight_eq_div_pow,
    Nat.pow_succ, show 2 ^ 7 * 2 = 256 by decide]

theorem bv64_c0_shr_byte_nat (w : BitVec 64) {k : Nat} (hk : k < 8) :
    (w >>> ((8 : BitVec 64).toNat * k % 2 ^ 64 % 64) &&& 255 : BitVec 64) =
      BitVec.ofNat 64 ((w.toNat / 2 ^ (8 * k)) % 256) := by
  have hsh : (8 : BitVec 64).toNat * k % 2 ^ 64 % 64 = 8 * k := by
    rw [show (8 : BitVec 64).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 8 * k < 64)]
  apply BitVec.eq_of_toNat_eq
  rw [hsh, BitVec.toNat_and, show (255 : BitVec 64).toNat = 2 ^ 8 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.pow_succ, show 2 ^ 7 * 2 = 256 by decide, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]

theorem bv64_byte_log2_gt_zero {w : BitVec 64} (hne : w ≠ 0#64) {k : Nat}
    (hgt : w.toNat.log2 / 8 < k) (_hk : k < 8) :
    (w.toNat / 2 ^ (8 * k)) % 256 = 0 := by
  have hnz : w.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
  have hlt : w.toNat < 2 ^ (w.toNat.log2 + 1) := (Nat.log2_lt hnz).mp (Nat.lt_succ_self _)
  have hpow : 2 ^ (w.toNat.log2 + 1) ≤ 2 ^ (8 * k) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hdiv : w.toNat / 2 ^ (8 * k) = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)
  simp [hdiv]

theorem bv64_byte_log2_top_props {w : BitVec 64} (hne : w ≠ 0#64) :
    let t := w.toNat.log2 / 8
    t < 8 ∧
    (w.toNat / 2 ^ (8 * t)) % 256 ≠ 0 ∧
    ((w.toNat / 2 ^ (8 * t)) % 256 = 1 ↔ w.toNat.log2 % 8 = 0) := by
  have hnz : w.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
  have hlogLt64 : w.toNat.log2 < 64 := (Nat.log2_lt hnz).mpr w.isLt
  have htLt : w.toNat.log2 / 8 < 8 := by omega
  have hlo : 2 ^ w.toNat.log2 ≤ w.toNat := (Nat.le_log2 hnz).mp (Nat.le_refl _)
  have hhi : w.toNat < 2 ^ (w.toNat.log2 + 1) := (Nat.log2_lt hnz).mp (Nat.lt_succ_self _)
  have hpowLo : 2 ^ (8 * (w.toNat.log2 / 8)) ≤ 2 ^ w.toNat.log2 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpowHi : 2 ^ (w.toNat.log2 + 1) ≤ 2 ^ (8 * (w.toNat.log2 / 8) + 8) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hmulPow : 2 ^ (8 * (w.toNat.log2 / 8) + 8) = 2 ^ (8 * (w.toNat.log2 / 8)) * 256 := by
    rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
  have hdivGe1 : 1 ≤ w.toNat / 2 ^ (8 * (w.toNat.log2 / 8)) :=
    Nat.div_pos (Nat.le_trans hpowLo hlo) (Nat.pow_pos (by decide))
  have hdivLt256 : w.toNat / 2 ^ (8 * (w.toNat.log2 / 8)) < 256 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← hmulPow]
    exact Nat.lt_of_lt_of_le hhi hpowHi
  dsimp only
  rw [Nat.mod_eq_of_lt hdivLt256]
  refine ⟨htLt, by omega, ⟨fun h1 => ?_, fun hmod => ?_⟩⟩
  · have hlt2 : w.toNat < 2 ^ (8 * (w.toNat.log2 / 8) + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
      have := Nat.div_add_mod w.toNat (2 ^ (8 * (w.toNat.log2 / 8)))
      have hm := Nat.mod_lt w.toNat (Nat.pow_pos (by decide) : 0 < 2 ^ (8 * (w.toNat.log2 / 8)))
      rw [h1, Nat.mul_one] at this
      omega
    have hlogLt : w.toNat.log2 < 8 * (w.toNat.log2 / 8) + 1 := (Nat.log2_lt hnz).mpr hlt2
    omega
  · have hlogEq : 8 * (w.toNat.log2 / 8) = w.toNat.log2 := by omega
    rw [hlogEq]
    have hlt2 : w.toNat < 2 * 2 ^ w.toNat.log2 := by rwa [Nat.mul_comm, ← Nat.pow_succ]
    have hdivLt2 : w.toNat / 2 ^ w.toNat.log2 < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
      simpa [Nat.mul_comm] using hlt2
    have hdivGe : 1 ≤ w.toNat / 2 ^ w.toNat.log2 := Nat.div_pos hlo (Nat.pow_pos (by decide))
    omega

theorem sentinelByteIdx_le_8 (w : BitVec 64) : sentinelByteIdx w ≤ 8 := by
  unfold sentinelByteIdx
  split
  · decide
  · next hne =>
    have hnz : w.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
    have hlog : w.toNat.log2 < 64 := (Nat.log2_lt hnz).mpr w.isLt
    split <;> omega

theorem sentinelByteIdx_tagged_iff {val : Nat} (hlt : val < 2 ^ 63) :
    let k := sentinelByteIdx (BitVec.ofNat 64 val)
    match bytesOfNatS val with
    | some bs => k < 8 ∧ k = bs.length
    | none => 8 ≤ k := by
  by_cases h0 : val = 0
  · subst h0
    simp [sentinelByteIdx, bytesOfNatS]
  · have hpos : 0 < val := Nat.pos_of_ne_zero h0
    have hbv : BitVec.ofNat 64 val ≠ 0#64 := fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact h0 this
    have hlogLt : val.log2 < 63 := (Nat.log2_lt h0).mpr hlt
    have htoNat : (BitVec.ofNat 64 val).toNat = val :=
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold sentinelByteIdx bytesOfNatS
    rw [ite_eq_right hbv, htoNat]
    by_cases hmod : val.log2 % 8 = 0
    · rw [ite_eq_left hmod, ite_eq_left ⟨hpos, hmod⟩]
      simp [natToBytesLE_length]
      omega
    · have hnot : ¬ (0 < val ∧ val.log2 % 8 = 0) := fun ⟨_, hm⟩ => hmod hm
      rw [ite_eq_right hmod, ite_eq_right hnot]
      omega

theorem bv64_or_byte_shift {a k b : Nat} (hk : k < 8) (ha : a < 2 ^ (8 * k)) (hb : b < 256) :
    (BitVec.ofNat 64 a ||| (BitVec.ofNat 64 b <<< (8#64 * BitVec.ofNat 64 k))) =
      BitVec.ofNat 64 (a + 2 ^ (8 * k) * b) := by
  have ha64 : a < 2 ^ 64 := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))
  have hb64 : b < 2 ^ 64 := Nat.lt_trans hb (by decide)
  have hsum64 : a + 2 ^ (8 * k) * b < 2 ^ 64 := by
    have hmul : 2 ^ (8 * k) * b ≤ 2 ^ (8 * k) * 255 := Nat.mul_le_mul_left _ (by omega)
    have hpow : 2 ^ (8 * (k + 1)) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    have h256 : 2 ^ (8 * k) * 256 = 2 ^ (8 * (k + 1)) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
    omega
  have hsh : (8#64 * BitVec.ofNat 64 k).toNat = 8 * k := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (8 : Nat) % 2 ^ 64 = 8 by decide, show k % 2 ^ 64 = k by omega,
      Nat.mod_eq_of_lt (by omega)]
  have hand : (BitVec.ofNat 64 a &&&
      (BitVec.ofNat 64 b <<< (8#64 * BitVec.ofNat 64 k))) = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    rw [show (BitVec.ofNat 64 b <<< (8#64 * BitVec.ofNat 64 k)) =
        BitVec.ofNat 64 b <<< (8#64 * BitVec.ofNat 64 k).toNat from rfl,
      BitVec.getLsbD_shiftLeft, hsh]
    by_cases hi8 : i < 8 * k
    · have hnot : ¬ (8 * k ≤ i) := by omega
      simp [hnot]
    · have haBit : (BitVec.ofNat 64 a).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]
        have hlt : a < 2 ^ i := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))
        simp [hi, Nat.testBit_lt_two_pow hlt]
      simp [haBit]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  have hmul64 : 2 ^ (8 * k) * b < 2 ^ 64 := by omega
  rw [BitVec.toNat_add,
    show (BitVec.ofNat 64 b <<< (8#64 * BitVec.ofNat 64 k)) =
      BitVec.ofNat 64 b <<< (8#64 * BitVec.ofNat 64 k).toNat from rfl,
    BitVec.toNat_shiftLeft, hsh, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hb64, Nat.shiftLeft_eq,
    Nat.mul_comm b (2 ^ (8 * k)), Nat.mod_eq_of_lt hmul64, Nat.mod_eq_of_lt hsum64]

theorem bv64_or_sentinel_shift {a k : Nat} (hk : k ≤ 7) (ha : a < 2 ^ (8 * k)) :
    (BitVec.ofNat 64 a ||| (1#64 <<< (8#64 * BitVec.ofNat 64 k))) =
      BitVec.ofNat 64 (2 ^ (8 * k) + a) := by
  have h := bv64_or_byte_shift (a := a) (k := k) (b := 1) (by omega) ha (by decide)
  simpa [Nat.mul_one, Nat.add_comm] using h

theorem bv64_shl1_or1_boxNat {n : Nat} (hn : n < 2 ^ 63) :
    ((BitVec.ofNat 64 n <<< 1#64) ||| 1#64) = boxNat n := by
  have hand : ((BitVec.ofNat 64 n <<< 1#64) &&& 1#64) = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    rw [show (BitVec.ofNat 64 n <<< 1#64) =
        BitVec.ofNat 64 n <<< (1#64 : BitVec 64).toNat from rfl, BitVec.getLsbD_shiftLeft,
      show (1#64 : BitVec 64).toNat = 1 from rfl]
    cases i with
    | zero => simp
    | succ j =>
      have h1lt : 1 < 2 ^ (j + 1) :=
        Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
      have htb : Nat.testBit 1 (j + 1) = false := Nat.testBit_lt_two_pow h1lt
      simp only [BitVec.getLsbD_ofNat, htb, Bool.and_false]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (BitVec.ofNat 64 n <<< 1#64) =
      BitVec.ofNat 64 n <<< (1#64 : BitVec 64).toNat from rfl,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega : n * 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : n * 2 + 1 < 2 ^ 64)]
  unfold boxNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 2 * n + 1 < 2 ^ 64)]
  omega

theorem limbsVal_lt_pow_of_last_zero :
    ∀ (xs : List (BitVec 64)), xs ≠ [] → xs.getLast! = 0#64 →
      limbsVal xs < 2 ^ (64 * (xs.length - 1))
  | [], hne, _ => absurd rfl hne
  | [x], _, hlast => by
    have hx : x = 0#64 := by simpa [List.getLast!] using hlast
    simp [hx, limbsVal]
  | x :: y :: ys, _, hlast => by
    have hne1 : x :: y :: ys ≠ [] := by simp
    have hne' : y :: ys ≠ [] := by simp
    have hlast' : (y :: ys).getLast! = 0#64 := by
      rw [list_getLast!_eq_getLast _ hne1, List.getLast_cons hne'] at hlast
      rwa [list_getLast!_eq_getLast _ hne']
    have ih := limbsVal_lt_pow_of_last_zero (y :: ys) hne' hlast'
    have hx := x.isLt
    have hpow : 2 ^ (64 * ((x :: y :: ys).length - 1)) =
        2 ^ 64 * 2 ^ (64 * ((y :: ys).length - 1)) := by
      have heq : 64 * ((x :: y :: ys).length - 1) = 64 + 64 * ((y :: ys).length - 1) := by
        simp; omega
      rw [heq, Nat.pow_add]
    rw [limbsVal_cons, hpow]
    omega

theorem mkMpzNatObj_canon_of_natOfBytesS {p : BitVec 64} {srcData : List UInt8}
    {limbs : List (BitVec 64)}
    (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0)
    (hge8 : 8 ≤ srcData.length) (hlenMax : srcData.length ≤ ffiNatMaxBytes)
    (hlimbsLen : limbs.length = natSLimbCount srcData.length)
    (hval : limbsVal limbs = natOfBytesS srcData) :
    RtMpzNatCanon (mkMpzNatObj p limbs) (natOfBytesS srcData) ∧
      MpzCanon (mkMpzNatObj p limbs) := by
  have hn1 : 1 ≤ limbs.length := by rw [hlimbsLen]; unfold natSLimbCount; omega
  have hne : limbs ≠ [] := fun h => by simp [h] at hn1
  have hnMax : limbs.length ≤ ffiMpzMaxLimbs := by
    rw [hlimbsLen]; unfold natSLimbCount ffiNatMaxBytes ffiMpzMaxLimbs at *; omega
  have hlast : limbs.getLast! ≠ 0#64 := by
    intro hz
    have hlt := limbsVal_lt_pow_of_last_zero limbs hne hz
    have hlb : 2 ^ (64 * (limbs.length - 1)) ≤ natOfBytesS srcData := by
      have hpow : 64 * (limbs.length - 1) ≤ 8 * srcData.length := by
        rw [hlimbsLen]; unfold natSLimbCount; omega
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hpow) (natOfBytesS_bounds srcData).1
    rw [hval] at hlt
    omega
  have htb : (mkMpzNatObj p limbs).totalBytes = 16 + 8 * limbs.length := by
    simp [LcnfObj.totalBytes, mkMpzNatObj, mpzTag, arrayTag, sarrayTag, stringTag]
  have hwf : (mkMpzNatObj p limbs).Wf := by
    refine ⟨hp0, hp8, by dsimp [mkMpzNatObj]; decide, by dsimp [mkMpzNatObj]; decide,
      by dsimp [mkMpzNatObj]; decide, by simp [mkMpzNatObj, mpzTag], ?_, ?_, ?_, ?_⟩
    · rw [htb]; unfold rtMinObjBytes; omega
    · rw [htb]; unfold rtMaxObjBytes ffiMpzMaxLimbs at *; omega
    · rw [htb]; omega
    · simp only [mkMpzNatObj, mpzTag, closureTag, arrayTag, sarrayTag, stringTag,
        show (250 : Nat) ≠ 245 by decide, show (250 : Nat) ≠ 246 by decide,
        show (250 : Nat) ≠ 248 by decide, show (250 : Nat) ≠ 249 by decide, ↓reduceIte]
      unfold ffiMpzMaxLimbs at *
      exact ⟨trivial, hnMax, by omega⟩
  have hge63 : 2 ^ 63 ≤ natOfBytesS srcData := natOfBytesS_ge_2p63 hge8
  refine ⟨⟨hwf, rfl, rfl, rfl, hn1, hnMax, hlast, hval, hge63⟩,
    ⟨hp0, hp8, by dsimp [mkMpzNatObj]; decide, rfl, rfl, rfl, rfl,
      by dsimp [mkMpzNatObj]; omega, ?_⟩⟩
  dsimp [mkMpzNatObj]
  unfold ffiMpzMaxLimbs at hnMax
  omega

theorem ffi_nat_nlimbs_bv (len : BitVec 64) :
    ((len >>> 3) + 1 : BitVec 64) = BitVec.ofNat 64 (natSLimbCount len.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (2 ^ 3 : Nat) = 8 from rfl, BitVec.toNat_ofNat]
  change (len.toNat / 8 + 1) % 2 ^ 64 = natSLimbCount len.toNat % 2 ^ 64
  have hl : len.toNat / 8 + 1 < 2 ^ 64 := by have := len.isLt; omega
  unfold natSLimbCount
  rw [Nat.mod_eq_of_lt hl]

theorem ffi_nat_sz_bv (len : BitVec 64) (hmax : len.toNat ≤ ffiNatMaxBytes) (hgt : 7 < len.toNat) :
    (16 + 8 * ((len >>> 3) + 1) : BitVec 64) = BitVec.ofNat 64 (natSAllocBytes len.toNat) := by
  have hszEq : natSAllocBytes len.toNat = 16 + 8 * natSLimbCount len.toNat := by
    unfold natSAllocBytes; rw [ite_eq_right (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [ffi_nat_nlimbs_bv, hszEq, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  change (16 + 8 * (natSLimbCount len.toNat % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 =
    (16 + 8 * natSLimbCount len.toNat) % 2 ^ 64
  have hnl : natSLimbCount len.toNat < 2 ^ 64 := by unfold natSLimbCount; omega
  have hmul : 8 * natSLimbCount len.toNat < 2 ^ 64 := by
    unfold natSLimbCount ffiNatMaxBytes at *; omega
  have hsz64 : 16 + 8 * natSLimbCount len.toNat < 2 ^ 64 := by
    unfold natSLimbCount ffiNatMaxBytes at *; omega
  rw [Nat.mod_eq_of_lt hnl, Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt hsz64]

theorem ffi_nat_wrap_sz_bv (len : BitVec 64) (hmax : len.toNat ≤ ffiNatMaxBytes)
    (hgt : 7 < len.toNat) :
    (16 + 8 * ((len >>> 3) + 1) + 16 : BitVec 64) =
      BitVec.ofNat 64 (natSAllocBytes len.toNat + 16) := by
  rw [ffi_nat_sz_bv len hmax hgt]
  apply BitVec.eq_of_toNat_eq
  have hsz64 : natSAllocBytes len.toNat + 16 < 2 ^ 64 := by
    unfold natSAllocBytes natSLimbCount ffiNatMaxBytes at *
    split <;> omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (16 : BitVec 64).toNat = 16 from rfl,
    Nat.mod_eq_of_lt (by omega : natSAllocBytes len.toNat < 2 ^ 64), Nat.mod_eq_of_lt hsz64]

/-! ## 2. WP Proofs for Sentineled `Nat` Inspection Helpers -/

theorem lcnf_ffi_sentinel_byte_idx_wp :
    ∀ xs m Q X, ffiSentinelByteIdxSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_sentinel_byte_idx.body xs m Q X := by
  intro ⟨w, ⟨⟩⟩ m Q X hQ
  dsimp only [Func.wp, lcnf_ffi_sentinel_byte_idx, lcnf_ffi_sentinel_byte_idx_body,
    ffiSentinelByteIdxSpec] at hQ ⊢
  by_cases hw0 : w = 0#64
  · subst hw0
    ffi2_steps <;> first
      | exact (by simpa [sentinelByteIdx] using hQ)
      | (exfalso; contradiction)
  · ffi2_steps
    let target : Nat := w.toNat.log2 / 8
    have htProps := bv64_byte_log2_top_props hw0
    have htLt : target < 8 := htProps.1
    refine wp_while_state1
      (proj := fun k : BitVec 64 => k)
      (μ := fun k : BitVec 64 => k.toNat)
      (Inv := fun k m' => m' = m ∧ target ≤ k.toNat ∧ k.toNat ≤ 7)
      ?_ ?_
    · intro L hL
      exact hL 7#64 m ⟨rfl, by rw [show (7#64 : BitVec 64).toNat = 7 from rfl]; omega, by decide⟩
    · intro L k m' ⟨hmEq, htle, hk7⟩ ih
      rcases hmEq with rfl
      have hbyteTarget : (w.toNat / 2 ^ (8 * target)) % 256 =
          ((BitVec.ofNat 64 ((w.toNat / 2 ^ (8 * target)) % 256)).toNat) := by
        have hlt264 : (w.toNat / 2 ^ (8 * target)) % 256 < 2 ^ 64 :=
          Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt264]
      ffi2_steps
      · -- k > 0, byte != 0, byte != 1 -> Q (8, ()) m
        have hkpos : 0 < k.toNat := by assumption
        have hneq0 : w >>> ((8 : BitVec 64).toNat * k.toNat % 2 ^ 64 % 64) &&& 255 ≠ 0 := by
          assumption
        have hneq1 : w >>> ((8 : BitVec 64).toNat * k.toNat % 2 ^ 64 % 64) &&& 255 ≠ 1 := by
          assumption
        have hkEqT : k.toNat = target := by
          by_cases hgt : target < k.toNat
          · exfalso
            have hb := bv64_c0_shr_byte_nat w (by omega : k.toNat < 8)
            have hz := bv64_byte_log2_gt_zero hw0 hgt (by omega)
            rw [hz] at hb
            exact hneq0 hb
          · omega
        rw [hkEqT, bv64_c0_shr_byte_nat w htLt] at hneq1
        have hnotMod : w.toNat.log2 % 8 ≠ 0 := fun hmod => by
          apply hneq1
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)),
            htProps.2.2.mpr hmod]
        simpa [sentinelByteIdx, ite_eq_right hw0, ite_eq_right hnotMod] using hQ
      · -- k > 0, byte != 0, byte = 1 -> Q (k, ()) m
        have hkpos : 0 < k.toNat := by assumption
        have hneq0 : w >>> ((8 : BitVec 64).toNat * k.toNat % 2 ^ 64 % 64) &&& 255 ≠ 0 := by
          assumption
        have heq1 : w >>> ((8 : BitVec 64).toNat * k.toNat % 2 ^ 64 % 64) &&& 255 = 1 := by
          assumption
        have hkEqT : k.toNat = target := by
          by_cases hgt : target < k.toNat
          · exfalso
            have hb := bv64_c0_shr_byte_nat w (by omega : k.toNat < 8)
            have hz := bv64_byte_log2_gt_zero hw0 hgt (by omega)
            rw [hz] at hb
            exact hneq0 hb
          · omega
        rw [hkEqT, bv64_c0_shr_byte_nat w htLt] at heq1
        have h1 : (w.toNat / 2 ^ (8 * target)) % 256 = 1 := by
          have := congrArg BitVec.toNat heq1
          rw [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))] at this
          exact this
        have hmod : w.toNat.log2 % 8 = 0 := htProps.2.2.mp h1
        have hkbv : k = BitVec.ofNat 64 target := BitVec.eq_of_toNat_eq (by
          rw [hkEqT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
        rw [hkbv]
        simpa [sentinelByteIdx, ite_eq_right hw0, ite_eq_left hmod] using hQ
      · -- k > 0, byte = 0 -> L (k - 1, ()) m
        have hkpos : 0 < k.toNat := by assumption
        have heq0 : w >>> ((8 : BitVec 64).toNat * k.toNat % 2 ^ 64 % 64) &&& 255 = 0 := by
          assumption
        have hgt : target < k.toNat := by
          by_cases heqt : k.toNat = target
          · exfalso
            rw [heqt, bv64_c0_shr_byte_nat w htLt] at heq0
            have h0 := congrArg BitVec.toNat heq0
            rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl,
              Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))] at h0
            exact htProps.2.1 h0
          · omega
        have hk1lt : (k - 1#64).toNat < k.toNat := by
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hkpos)]
          simp [BitVec.toNat_ofNat]; omega
        have hk1ge : target ≤ (k - 1#64).toNat ∧ (k - 1#64).toNat ≤ 7 := by
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hkpos)]
          simp [BitVec.toNat_ofNat]; omega
        exact ih (k - 1#64) m' hk1lt ⟨rfl, hk1ge⟩
      · -- ¬ 0 < k, byte != 1 -> Q (8, ()) m
        have hnotPos : ¬ 0 < k.toNat := by assumption
        have hneq1 : w >>> ((8 : BitVec 64).toNat * k.toNat % 2 ^ 64 % 64) &&& 255 ≠ 1 := by
          assumption
        have hk0 : k.toNat = 0 := by omega
        have ht0 : target = 0 := by omega
        rw [hk0, ← ht0, bv64_c0_shr_byte_nat w htLt] at hneq1
        have hnotMod : w.toNat.log2 % 8 ≠ 0 := fun hmod => by
          apply hneq1
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)),
            htProps.2.2.mpr hmod]
        have hlogNz : w.toNat.log2 ≠ 0 := fun h0 => by apply hnotMod; simp [h0]
        simpa [sentinelByteIdx, ite_eq_right hw0, ite_eq_right hnotMod,
          ite_eq_right hlogNz] using hQ
      · -- ¬ 0 < k, byte = 1 -> Q (k, ()) m
        have hnotPos : ¬ 0 < k.toNat := by assumption
        have heq1 : w >>> ((8 : BitVec 64).toNat * k.toNat % 2 ^ 64 % 64) &&& 255 = 1 := by
          assumption
        have hk0 : k.toNat = 0 := by omega
        have ht0 : target = 0 := by omega
        rw [hk0, ← ht0, bv64_c0_shr_byte_nat w htLt] at heq1
        have h1 : (w.toNat / 2 ^ (8 * target)) % 256 = 1 := by
          have := congrArg BitVec.toNat heq1
          rw [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))] at this
          exact this
        have hmod : w.toNat.log2 % 8 = 0 := htProps.2.2.mp h1
        have hlog0 : w.toNat.log2 = 0 := by
          have : w.toNat.log2 < 8 := Nat.lt_of_div_eq_zero (by decide : 0 < 8) ht0; omega
        have hkbv : k = BitVec.ofNat 64 target := BitVec.eq_of_toNat_eq (by rw [hk0, ht0]; rfl)
        rw [hkbv, ht0]
        simpa [sentinelByteIdx, ite_eq_right hw0, ite_eq_left hmod, hlog0] using hQ

theorem lcnf_ffi_nat_bytes_len_wp :
    ∀ xs m Q X, ffiNatBytesLenSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_nat_bytes_len.body xs m Q X := by
  intro ⟨a, ⟨⟩⟩ m Q X ⟨val, objs, R, hrep, hm, hPost⟩
  dsimp only [Func.wp, lcnf_ffi_nat_bytes_len, lcnf_ffi_nat_bytes_len_body]
  by_cases hsmall : val < 2 ^ 63
  · rw [RtNatRep, ite_eq_left hsmall] at hrep
    subst hrep
    have hand1 : (BitVec.ofNat 64 (2 * val + 1) &&& 1#64) = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (1 : Nat) % 2 ^ 64 = 1 from rfl,
        Nat.mod_eq_of_lt (by omega : 2 * val + 1 < 2 ^ 64)]
      change (2 * val + 1) &&& (2 ^ 1 - 1) = 1
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.pow_one]
      omega
    have hshr1 : (BitVec.ofNat 64 (2 * val + 1) >>> 1) = BitVec.ofNat 64 val := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.pow_one,
        Nat.mod_eq_of_lt (by omega : 2 * val + 1 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : val < 2 ^ 64)]
      omega
    ffi2_steps
    ffi2_call ffiEnv_sentinel_byte_idx
    dsimp only [ffiSentinelByteIdxSpec, vals, Tup.map, Arg.val]
    rw [hshr1]
    have hspec := sentinelByteIdx_tagged_iff hsmall
    have hle8 := sentinelByteIdx_le_8 (BitVec.ofNat 64 val)
    cases hbs : bytesOfNatS val with
    | none =>
      rw [hbs] at hspec hPost
      dsimp only at hspec hPost
      ffi2_steps <;> first
        | exact hPost
        | (exfalso
           simp only [show (8 : BitVec 64).toNat = 8 from rfl] at *
           rw [Nat.mod_eq_of_lt (by omega : sentinelByteIdx (BitVec.ofNat 64 val) < 2 ^ 64)] at *
           omega)
    | some bs =>
      rw [hbs] at hspec hPost
      dsimp only at hspec hPost
      ffi2_steps <;> first
        | (rw [hspec.2]; exact hPost)
        | (exfalso
           simp only [show (8 : BitVec 64).toNat = 8 from rfl] at *
           rw [Nat.mod_eq_of_lt (by omega : sentinelByteIdx (BitVec.ofNat 64 val) < 2 ^ 64)] at *
           omega)
  · rw [RtNatRep, ite_eq_right hsmall] at hrep
    rcases hrep with ⟨heven, obj, hmem, haddr, hcanon⟩
    subst haddr
    obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmem
    rw [lcnfHeap_focus objs hidx] at hm
    have hwf := hcanon.1
    have htag : objs[idx].tag = mpzTag := hcanon.2.1
    have harrLen : objs[idx].arrSize = objs[idx].limbs.length := hcanon.2.2.2.1
    have hge1 : 1 ≤ objs[idx].limbs.length := hcanon.2.2.2.2.1
    have hleMax : objs[idx].limbs.length ≤ ffiMpzMaxLimbs := hcanon.2.2.2.2.2.1
    have hcap32 : objs[idx].cap < 2 ^ 32 := by
      have := hwf.2.2.2.2.2.2.2.2.2
      simp only [htag, mpzTag, closureTag, arrayTag, sarrayTag, stringTag,
        show (250 : Nat) ≠ 245 by decide, show (250 : Nat) ≠ 246 by decide,
        show (250 : Nat) ≠ 248 by decide, show (250 : Nat) ≠ 249 by decide, ↓reduceIte] at this
      have hcapMax : objs[idx].cap ≤ 33554429 := by rcases this with ⟨_, hc, _⟩; exact hc
      omega
    have harr32 : objs[idx].arrSize < 2 ^ 32 := by
      rw [harrLen]; unfold ffiMpzMaxLimbs at hleMax; omega
    have hmeta : (objs[idx].mpzMeta >>> 32) = BitVec.ofNat 64 objs[idx].limbs.length := by
      rw [← harrLen]; exact mpzMeta_shr32_of_obj objs[idx] hcap32 harr32
    have hloadMeta : loadVal m i64 (objs[idx].addr + 8) = some objs[idx].mpzMeta :=
      ffi_load_mpz_meta htag (sep_ac hm : (lcnfObjMem objs[idx] ⋆
        (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1)) ⋆ R)) m)
    have hlimLt : objs[idx].limbs.length < 2 ^ 64 := by unfold ffiMpzMaxLimbs at hleMax; omega
    have hne : objs[idx].limbs ≠ [] := fun h => by simp [h] at hge1
    have htopEq : objs[idx].limbs[objs[idx].limbs.length - 1]'(by omega) =
        objs[idx].limbs.getLast! := by
      rw [list_getLast!_eq_getLast _ hne, List.getLast_eq_getElem]
    have hspec := sentinelByteIdx_mpz_spec hcanon
    rw [ffi2_lcnfObjMem_mpz_eq htag] at hm
    have hmeta' : objs[idx].mpzMeta >>> (OfNat.ofNat 32 : Nat) =
        BitVec.ofNat 64 objs[idx].limbs.length := hmeta
    have hdiv : objs[idx].mpzMeta.toNat / 2 ^ (OfNat.ofNat 32 : Nat) = objs[idx].limbs.length := by
      rw [show (OfNat.ofNat 32 : Nat) = 32 from rfl, ← Nat.shiftRight_eq_div_pow,
        ← BitVec.toNat_ushiftRight, hmeta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimLt]
    have hlimPos : 0 < (BitVec.ofNat 64 objs[idx].limbs.length).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimLt]; exact hge1
    have hlimLe : (BitVec.ofNat 64 objs[idx].limbs.length).toNat ≤ objs[idx].limbs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimLt]; exact Nat.le_refl _
    ffi2_steps <;> first
      | (exfalso
         have h0 : objs[idx].mpzMeta >>> (OfNat.ofNat 32 : Nat) = 0#64 := by assumption
         rw [hmeta'] at h0
         have h0nat := congrArg BitVec.toNat h0
         rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimLt] at h0nat
         omega)
      | (exfalso
         try rw [hdiv] at *
         try rw [show (33554429 : BitVec 64).toNat = 33554429 from rfl] at *
         unfold ffiMpzMaxLimbs at hleMax
         omega)
      | (try rw [hmeta']
         have hmArr : (array64 (objs[idx].addr + 16#64) objs[idx].limbs ⋆
             (cell64 objs[idx].addr objs[idx].header ⋆
               cell64 (objs[idx].addr + 8#64) objs[idx].mpzMeta ⋆
               lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1)) ⋆ R)) m := sep_ac hm
         dsimp only
         refine wp_load_of (ffi_load_array64_sub1_mul8 hmArr hlimPos hlimLe) ?_
         ffi2_steps
         ffi2_call ffiEnv_sentinel_byte_idx
         dsimp only [ffiSentinelByteIdxSpec, vals, Tup.map, Arg.val]
         simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimLt]
         rw [htopEq]
         have hle8 := sentinelByteIdx_le_8 objs[idx].limbs.getLast!
         cases hbs : bytesOfNatS val with
         | none =>
           rw [hbs] at hPost
           dsimp only at hPost
           have hge8 : 8 ≤ sentinelByteIdx objs[idx].limbs.getLast! := by
             by_cases hlt : sentinelByteIdx objs[idx].limbs.getLast! < 8
             · obtain ⟨bs, hbs'⟩ := hspec.1.mp hlt
               rw [hbs] at hbs'; nomatch hbs'
             · omega
           ffi2_steps <;> first
             | exact hPost
             | (exfalso
                simp only [show (8 : BitVec 64).toNat = 8 from rfl] at *
                rw [Nat.mod_eq_of_lt (by omega :
                  sentinelByteIdx objs[idx].limbs.getLast! < 2 ^ 64)] at *
                omega)
         | some bs =>
           rw [hbs] at hPost
           dsimp only at hPost
           obtain ⟨hlt8, hlenEq⟩ := hspec.2 bs hbs
           ffi2_steps <;> first
             | (have hsum : 8 * (BitVec.ofNat 64 objs[idx].limbs.length - 1) +
                    BitVec.ofNat 64 (sentinelByteIdx objs[idx].limbs.getLast!) =
                    BitVec.ofNat 64 bs.length := by
                  apply BitVec.eq_of_toNat_eq
                  have hsub : (BitVec.ofNat 64 objs[idx].limbs.length - 1 : BitVec 64).toNat =
                      objs[idx].limbs.length - 1 := by
                    have hleBv : (1 : BitVec 64) ≤ BitVec.ofNat 64 objs[idx].limbs.length := by
                      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimLt]
                      exact hge1
                    rw [BitVec.toNat_sub_of_le hleBv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimLt]
                    rfl
                  have hbsLt : bs.length < 2 ^ 64 := by
                    unfold ffiMpzMaxLimbs at hleMax; omega
                  have hmulLt : 8 * (objs[idx].limbs.length - 1) < 2 ^ 64 := by
                    unfold ffiMpzMaxLimbs at hleMax; omega
                  rw [BitVec.toNat_add, BitVec.toNat_mul, show (8 : BitVec 64).toNat = 8 from rfl,
                    hsub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : sentinelByteIdx objs[idx].limbs.getLast! < 2 ^ 64),
                    Nat.mod_eq_of_lt hbsLt, Nat.mod_eq_of_lt hmulLt]
                  change (8 * (objs[idx].limbs.length - 1) +
                    sentinelByteIdx objs[idx].limbs.getLast!) % 2 ^ 64 = bs.length
                  rw [hlenEq, Nat.mod_eq_of_lt hbsLt]
                rw [hsum]
                exact hPost)
             | (exfalso
                simp only [show (8 : BitVec 64).toNat = 8 from rfl] at *
                rw [Nat.mod_eq_of_lt (by omega :
                  sentinelByteIdx objs[idx].limbs.getLast! < 2 ^ 64)] at *
                omega))

theorem lcnf_ffi_nat_bytes_ptr_wp :
    ∀ xs m Q X, ffiNatBytesPtrSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_nat_bytes_ptr.body xs m Q X := by
  intro ⟨rt, a, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, lcnf_ffi_nat_bytes_ptr, lcnf_ffi_nat_bytes_ptr_body,
    ffiNatBytesPtrSpec] at hPre ⊢
  by_cases hodd : (a &&& 1#64) ≠ 0#64
  · rw [ite_eq_left hodd] at hPre
    rcases hPre with ⟨scr, scrLimbs, R, hcapLt, hm, hPost⟩
    by_cases hfail : scr = 0#64 ∨ scrLimbs.length = 0
    · rw [ite_eq_left hfail] at hPost
      ffi2_steps <;> first
        | exact hPost
        | (exfalso; exact hodd ‹(a &&& 1#64) = 0#64›)
        | (exfalso
           rcases hfail with rfl | h0
           · exact ‹(0#64 : BitVec 64) ≠ 0› rfl
           · apply ‹BitVec.ofNat 64 scrLimbs.length ≠ 0›
             rw [h0]; rfl)
    · rw [ite_eq_right hfail] at hPost
      have hscrNz : scr ≠ 0#64 := fun h => hfail (Or.inl h)
      have hlenPos : 0 < scrLimbs.length :=
        Nat.pos_of_ne_zero fun h0 => hfail (Or.inr h0)
      ffi2_steps <;> first
        | (exact hPost _ (sep_ac (by assumption) : (cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 scr (scrLimbs.set 0 (a >>> 1)) ⋆ R) _))
        | (exfalso; exact hodd ‹(a &&& 1#64) = 0#64›)
        | (exfalso; exact hscrNz (by assumption))
        | (exfalso
           have hlen0 : BitVec.ofNat 64 scrLimbs.length = 0#64 := by assumption
           have hnat := congrArg BitVec.toNat hlen0
           rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcapLt] at hnat
           omega)
  · rw [ite_eq_right hodd] at hPre
    have heven : (a &&& 1#64) = 0#64 := Classical.not_not.mp hodd
    ffi2_steps <;> first
      | exact hPre
      | (exfalso; exact ‹(a &&& 1#64) ≠ 0› heven)

/-! ## 3. WP Proofs for Sentineled `Nat` Constructors (`nat_of_bytes`, `nat_wrap_ok`) -/

theorem lcnf_ffi_nat_of_bytes_wp :
    ∀ xs m Q X, ffiNatOfBytesSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_nat_of_bytes.body xs m Q X := by
  intro ⟨rt, srcPtr, len, ⟨⟩⟩ m Q X ⟨st, srcData, R, hlen, hm, hPost⟩
  dsimp only [Func.wp, lcnf_ffi_nat_of_bytes, lcnf_ffi_nat_of_bytes_body]
  by_cases hle7 : len.toNat ≤ 7
  · rw [ite_eq_left hle7] at hPost
    ffi2_steps
    refine wp_while_state
      (proj := fun k : Nat => (BitVec.ofNat 64 (bytesToNatLE (srcData.take k)),
        BitVec.ofNat 64 k, ()))
      (μ := fun k : Nat => len.toNat - k)
      (Inv := fun k m' => m' = m ∧ k ≤ len.toNat)
      ?_ ?_
    · intro L hL
      exact hL 0 m ⟨rfl, Nat.zero_le _⟩
    · intro L k m' ⟨hmEq, hkLe⟩ ih
      rcases hmEq with rfl
      ffi2_steps
      · have hltNat : k < len.toNat := by
          have hc : (BitVec.ofNat 64 k).toNat < len.toNat := by assumption
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
        have hltSrc : k < srcData.length := by omega
        have hmBytes : (bytes srcPtr srcData ⋆ (rtC0Inv rt st ⋆ R)) m' := sep_ac hm
        have hload := r2_c0_load_bytes_bv hmBytes
          (i := BitVec.ofNat 64 k)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hltSrc)
          (by omega)
        ffi2_steps
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
        have htake : srcData.take (k + 1) = srcData.take k ++ [srcData[k]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hltSrc, Option.toList_some]
        have hbytesSum : bytesToNatLE (srcData.take (k + 1)) =
            bytesToNatLE (srcData.take k) + 2 ^ (8 * k) * srcData[k].toNat := by
          rw [htake, bytesToNatLE_append, List.length_take_of_le (by omega), bytesToNatLE_cons,
            bytesToNatLE_nil, Nat.mul_zero, Nat.add_zero]
        have hvLt : bytesToNatLE (srcData.take k) < 2 ^ (8 * k) := by
          have := bytesToNatLE_lt (srcData.take k)
          rwa [List.length_take_of_le (by omega)] at this
        have hset64 : ((BitVec.ofNat 8 srcData[k].toNat).setWidth 64) =
            BitVec.ofNat 64 srcData[k].toNat := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt srcData[k].toNat_lt,
            Nat.mod_eq_of_lt (Nat.lt_trans srcData[k].toNat_lt (by decide))]
        rw [hset64]
        have hshEqk : (BitVec.ofNat 64 srcData[k].toNat <<< ((8 * BitVec.ofNat 64 k).toNat % 64)) =
            (BitVec.ofNat 64 srcData[k].toNat <<< (8 * BitVec.ofNat 64 k)) := by
          have h8k' : (8 * BitVec.ofNat 64 k).toNat = 8 * k := by
            rw [BitVec.toNat_mul, show (8 : BitVec 64).toNat = 8 from rfl, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64)]
          rw [show (BitVec.ofNat 64 srcData[k].toNat <<< (8 * BitVec.ofNat 64 k)) =
              BitVec.ofNat 64 srcData[k].toNat <<< (8 * BitVec.ofNat 64 k).toNat from rfl,
            h8k', Nat.mod_eq_of_lt (by omega : 8 * k < 64)]
        have hor : (BitVec.ofNat 64 (bytesToNatLE (srcData.take k)) |||
            (BitVec.ofNat 64 srcData[k].toNat <<< ((8 * BitVec.ofNat 64 k).toNat % 64))) =
            BitVec.ofNat 64 (bytesToNatLE (srcData.take (k + 1))) := by
          rw [hshEqk, hbytesSum]
          exact bv64_or_byte_shift (by omega) hvLt srcData[k].toNat_lt
        have hadd1 : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          change (k % 2 ^ 64 + 1) % 2 ^ 64 = (k + 1) % 2 ^ 64
          rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
        rw [hor, hadd1]
        exact ih (k + 1) m' (by omega) ⟨rfl, by omega⟩
      · have hkEq : k = len.toNat := by
          have hc : ¬ (BitVec.ofNat 64 k).toNat < len.toNat := by assumption
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
          omega
        subst hkEq
        rw [← hlen, List.take_length]
        have h8len : (8 * len).toNat % 64 = 8 * srcData.length := by
          rw [BitVec.toNat_mul, show (8 : BitVec 64).toNat = 8 from rfl, ← hlen,
            Nat.mod_eq_of_lt (by omega : 8 * srcData.length < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 8 * srcData.length < 64)]
        have hor := bv64_or_sentinel_shift (a := bytesToNatLE srcData) (k := srcData.length)
          (by omega) (bytesToNatLE_lt srcData)
        have hshEq : (1 : BitVec 64) <<< (8 * srcData.length) =
            1#64 <<< (8#64 * BitVec.ofNat 64 srcData.length) := by
          rw [show 1#64 <<< (8#64 * BitVec.ofNat 64 srcData.length) =
              1#64 <<< (8#64 * BitVec.ofNat 64 srcData.length).toNat from rfl]
          congr 1
          rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : srcData.length < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 8 * srcData.length < 2 ^ 64)]
        rw [h8len, hshEq, hor]
        change Q (((BitVec.ofNat 64 (natOfBytesS srcData) <<< 1#64) ||| 1#64), ()) m'
        rw [bv64_shl1_or1_boxNat (natOfBytesS_lt_2p63 (by omega))]
        exact hPost
  · rw [ite_eq_right hle7] at hPost
    have hgt7 : 7 < len.toNat := Nat.lt_of_not_le hle7
    have hnlimbsEq := ffi_nat_nlimbs_bv len
    by_cases hvalid : len.toNat ≤ ffiNatMaxBytes ∧ natSAllocBytes len.toNat ≤ st.rem
    · rw [ite_eq_left hvalid] at hPost
      have hszEq : natSAllocBytes len.toNat = 16 + 8 * natSLimbCount len.toNat := by
        unfold natSAllocBytes; rw [ite_eq_right hle7]
      have hszLt : natSAllocBytes len.toNat < rtMaxObjBytes := by
        rw [hszEq]; unfold natSLimbCount rtMaxObjBytes ffiNatMaxBytes at *; omega
      have hszLo : rtMinObjBytes ≤ natSAllocBytes len.toNat := by
        rw [hszEq]; unfold natSLimbCount rtMinObjBytes; omega
      have hszAlign : align8 (natSAllocBytes len.toNat) = natSAllocBytes len.toNat := by
        rw [hszEq]; unfold align8; omega
      have hszBv := ffi_nat_sz_bv len hvalid.1 hgt7
      ffi2_steps <;> first
        | (exfalso; unfold ffiNatMaxBytes at hvalid
           have hc : 268435431 < len.toNat := by assumption
           omega)
        | (exfalso
           have hc : st.hdr.s_end.toNat < st.hdr.s_cur.toNat := by assumption
           have := st.curLeEnd; omega)
        | (exfalso
           have hc : (2 ^ 64 - st.hdr.s_cur.toNat + st.hdr.s_end.toNat) % 2 ^ 64 <
               ((16 : BitVec 64).toNat + (8 : BitVec 64).toNat *
                 ((len.toNat / 2 ^ (OfNat.ofNat 3 : Nat) +
                   (1 : BitVec 64).toNat) % 2 ^ 64)) % 2 ^ 64 := by assumption
           rw [ffi2_sub_rem_eq st, ffi2_sz_rhs_eq len hvalid.1 hgt7] at hc; omega)
        | (ffi2_call ffiEnv_lcnf_alloc
           dsimp only [lcnfAllocRemSpec, vals, Tup.map, Arg.val]
           rw [show (16 + 8 * (len >>> (OfNat.ofNat 3 : Nat) + 1) : BitVec 64) =
               BitVec.ofNat 64 (natSAllocBytes len.toNat) from hszBv,
             BitVec.toNat_ofNat,
             Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hszLt; omega), hszAlign]
           refine ⟨st, bytes srcPtr srcData ⋆ R,
             by unfold rtMaxObjBytes at hszLt; omega, hszLo, hszLt, Or.inr hvalid.2,
             (sep_ac hm : (rtC0Inv rt st ⋆ (bytes srcPtr srcData ⋆ R)) m),
             fun p st' m1 hp0 hp8 hpr hremLe hremLo hm1 => ?_⟩
           obtain ⟨w0, w1, hp2⟩ := region_to_2cells_rem_ffi (by omega)
             (by unfold rtMaxObjBytes at hszLt; omega)
             (sep_ac hm1 : (region p (natSAllocBytes len.toNat) ⋆
               (rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) m1)
           rw [hszEq, show 16 + 8 * natSLimbCount len.toNat - 16 =
               8 * natSLimbCount len.toNat by omega] at hp2
           have hp2' : (cell64 p w0 ⋆ (cell64 (p + 8#64) w1 ⋆
               region (p + 16#64) (8 * natSLimbCount len.toNat) ⋆
               rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) m1 := sep_ac hp2
           change LeanQbe.T.wp _ _ _ _ _
           apply wp_store_sep (store_cell64 mpzHeaderWord hp2')
           intro m2 hm2
           ffi2_steps
           have hm2' : (cell64 (p + 8#64) w1 ⋆ (cell64 p mpzHeaderWord ⋆
               region (p + 16#64) (8 * natSLimbCount len.toNat) ⋆
               rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) m2 := sep_ac hm2
           obtain ⟨metaW, hmetaDef⟩ : ∃ metaW : BitVec 64,
               metaW = (BitVec.ofNat 64 (natSLimbCount len.toNat) |||
                 (BitVec.ofNat 64 (natSLimbCount len.toNat) <<< 32)) := ⟨_, rfl⟩
           have hmetaC0 : ((len >>> (OfNat.ofNat 3 : Nat) + 1 : BitVec 64) |||
               ((len >>> (OfNat.ofNat 3 : Nat) + 1 : BitVec 64) <<< 32)) = metaW := by
             rw [hnlimbsEq, ← hmetaDef]
           rw [hmetaC0]
           change LeanQbe.T.wp _ _ _ _ _
           apply wp_store_sep (store_cell64 metaW hm2')
           intro m3 hm3
           ffi2_steps
           ffi2_call ffiEnv_r2_mem_copy_bytes
           dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
           have hm3' : (bytes srcPtr srcData ⋆ region (p + 16#64) (8 * natSLimbCount len.toNat) ⋆
               (rtC0Inv rt st' ⋆ cell64 p mpzHeaderWord ⋆
                 cell64 (p + 8#64) metaW ⋆ R)) m3 :=
             sep_ac hm3
           refine ⟨srcData, 8 * natSLimbCount len.toNat, _, hlen,
             by unfold natSLimbCount; omega,
             by unfold natSLimbCount ffiNatMaxBytes at *; omega, hm3', fun m4 hm4 => ?_⟩
           ffi2_steps
           have hm4reg : (region (p + 16#64 + len) (8 * natSLimbCount len.toNat - len.toNat) ⋆
               (bytes (p + 16#64) srcData ⋆ cell64 p mpzHeaderWord ⋆
                 cell64 (p + 8#64) metaW ⋆
                 rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) m4 := sep_ac hm4
           have hremSent : 0 < 8 * natSLimbCount len.toNat - len.toNat := by
             unfold natSLimbCount; omega
           have hfitSent : 8 * natSLimbCount len.toNat - len.toNat ≤ 2 ^ 64 := by
             unfold natSLimbCount ffiNatMaxBytes at *; omega
           obtain ⟨hokS, hm5⟩ := region_pop_store_byte 1#8 hremSent hfitSent hm4reg
           refine ⟨hokS, ?_⟩
           have hlenBv' : BitVec.ofNat 64 srcData.length = len := by
             rw [hlen]; apply BitVec.eq_of_toNat_eq; simp
           have hjoinSent : (bytes (p + 16#64) srcData ⋆
               bytes (p + 16#64 + len) [UInt8.ofNat (1#8 : BitVec 8).toNat]) =
               bytes (p + 16#64) (srcData ++ [1]) := by
             rw [show UInt8.ofNat (1#8 : BitVec 8).toNat = 1 from rfl, ← hlenBv',
               bytes_append (p + 16#64) srcData [1]
                 (by simp only [List.length_singleton]; unfold ffiNatMaxBytes at *; omega)]
           have hptr1 : p + 16#64 + len + 1#64 = p + 16#64 + (len + 1) := by bv_omega
           have hm5' : (bytes (p + 16#64) (srcData ++ [1]) ⋆
               region (p + 16#64 + (len + 1)) (8 * natSLimbCount len.toNat - len.toNat - 1) ⋆
               cell64 p mpzHeaderWord ⋆
               cell64 (p + 8#64) metaW ⋆
               rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)
               (storeMem m4 i8 (p + 16#64 + len) 1#8) := by
             rw [← hjoinSent, ← hptr1]
             exact sep_ac hm5
           let totalB : Nat := 8 * natSLimbCount len.toNat
           have htotalBv : 8 * ((len >>> (OfNat.ofNat 3 : Nat)) + 1) = BitVec.ofNat 64 totalB := by
             apply BitVec.eq_of_toNat_eq; dsimp only [totalB]
             have hnl : natSLimbCount len.toNat < 2 ^ 64 := by
               unfold natSLimbCount ffiNatMaxBytes at *; omega
             have htb : 8 * natSLimbCount len.toNat < 2 ^ 64 := by
               unfold natSLimbCount ffiNatMaxBytes at *; omega
             rw [hnlimbsEq]
             simp only [BitVec.toNat_mul, show (8 : BitVec 64).toNat = 8 from rfl,
               BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnl, Nat.mod_eq_of_lt htb]
           ffi2_steps
           rw [htotalBv]
           refine wp_while_state1
             (proj := fun pad : Nat => BitVec.ofNat 64 pad)
             (μ := fun pad : Nat => totalB - pad)
             (Inv := fun pad mL =>
               len.toNat + 1 ≤ pad ∧ pad ≤ totalB ∧
               (bytes (p + 16#64) (srcData ++ [1] ++ List.replicate (pad - len.toNat - 1) 0) ⋆
                 region (p + 16#64 + BitVec.ofNat 64 pad) (totalB - pad) ⋆
                 cell64 p mpzHeaderWord ⋆ cell64 (p + 8#64) metaW ⋆
                 rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R) mL)
             ?_ ?_
           · intro L hL
             have haddLen1 : len + 1 = BitVec.ofNat 64 (len.toNat + 1) := by
               apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rfl
             ffi2_steps
             rw [haddLen1]
             refine hL (len.toNat + 1) _
               ⟨Nat.le_refl _, by dsimp only [totalB]; unfold natSLimbCount; omega, ?_⟩
             dsimp only [totalB]
             rw [show len.toNat + 1 - len.toNat - 1 = 0 by omega, List.replicate_zero,
               List.append_nil, ← haddLen1, ← Nat.sub_sub]
             exact hm5'
           · intro L pad mL ⟨hpadLo, hpadHi, hmL⟩ ih
             have hpad64 : pad < 2 ^ 64 := by
               dsimp only [totalB] at hpadHi; unfold natSLimbCount ffiNatMaxBytes at *; omega
             have htb64 : totalB < 2 ^ 64 := by
               dsimp only [totalB]; unfold natSLimbCount ffiNatMaxBytes at *; omega
             ffi2_steps
             · have hcLt : pad < totalB := by
                 have hc : (BitVec.ofNat 64 pad).toNat < (BitVec.ofNat 64 totalB).toNat := by
                   assumption
                 rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpad64,
                   Nat.mod_eq_of_lt htb64] at hc
               have hregF : (region (p + 16#64 + BitVec.ofNat 64 pad) (totalB - pad) ⋆
                   (bytes (p + 16#64) (srcData ++ [1] ++ List.replicate (pad - len.toNat - 1) 0) ⋆
                     cell64 p mpzHeaderWord ⋆ cell64 (p + 8#64) metaW ⋆
                     rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)) mL := sep_ac hmL
               obtain ⟨hokP, hmL'⟩ := region_pop_store_byte 0#8 (by omega) (by omega) hregF
               refine ⟨hokP, ?_⟩
               ffi2_steps
               have hadd1 : BitVec.ofNat 64 pad + 1#64 = BitVec.ofNat 64 (pad + 1) := by
                 apply BitVec.eq_of_toNat_eq
                 rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                   BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpad64,
                   Nat.mod_eq_of_lt (by omega)]
               have hlenPrefix :
                   (srcData ++ [1] ++ List.replicate (pad - len.toNat - 1) (0 : UInt8)).length =
                     pad := by
                 simp only [List.length_append, List.length_singleton, List.length_replicate]; omega
               have hrepSucc :
                   srcData ++ [1] ++ List.replicate (pad - len.toNat - 1) (0 : UInt8) ++ [0] =
                   srcData ++ [1] ++ List.replicate (pad + 1 - len.toNat - 1) 0 := by
                 rw [show pad + 1 - len.toNat - 1 = (pad - len.toNat - 1) + 1 by omega,
                   List.replicate_succ', ← List.append_assoc]
               have hjoinZero :
                   (bytes (p + 16#64) (srcData ++ [1] ++ List.replicate (pad - len.toNat - 1) 0) ⋆
                     bytes (p + 16#64 + BitVec.ofNat 64 pad)
                       [UInt8.ofNat (0#8 : BitVec 8).toNat]) =
                   bytes (p + 16#64)
                     (srcData ++ [1] ++ List.replicate (pad + 1 - len.toNat - 1) 0) := by
                 have hjb := bytes_append (p + 16#64)
                   (srcData ++ [1] ++ List.replicate (pad - len.toNat - 1) 0) [0]
                   (by simp only [List.length_singleton]; rw [hlenPrefix]; omega)
                 rw [hlenPrefix] at hjb
                 rw [show UInt8.ofNat (0#8 : BitVec 8).toNat = 0 from rfl, ← hjb, hrepSucc]
               have hmL'' :
                   (bytes (p + 16#64)
                     (srcData ++ [1] ++ List.replicate (pad + 1 - len.toNat - 1) 0) ⋆
                     region (p + 16#64 + BitVec.ofNat 64 (pad + 1)) (totalB - (pad + 1)) ⋆
                     cell64 p mpzHeaderWord ⋆ cell64 (p + 8#64) metaW ⋆
                     rtC0Inv rt st' ⋆ bytes srcPtr srcData ⋆ R)
                   (storeMem mL i8 (p + 16#64 + BitVec.ofNat 64 pad) 0#8) := by
                 rw [← hjoinZero, ← hadd1, ← BitVec.add_assoc, Nat.sub_sub]; exact sep_ac hmL'
               rw [show BitVec.ofNat 64 pad + 1 = BitVec.ofNat 64 (pad + 1) from hadd1]
               exact ih (pad + 1) _ (by omega) ⟨by omega, by omega, hmL''⟩
             · have hpadEq : pad = totalB := by
                 have hc : ¬ (BitVec.ofNat 64 pad).toNat < (BitVec.ofNat 64 totalB).toNat := by
                   assumption
                 rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpad64,
                   Nat.mod_eq_of_lt htb64] at hc
                 omega
               subst hpadEq
               rw [Nat.sub_self, region_zero] at hmL
               let fullBs := srcData ++ [1] ++ List.replicate (totalB - len.toNat - 1) (0 : UInt8)
               have hfullLen : fullBs.length = 8 * natSLimbCount len.toNat := by
                 simp [fullBs, totalB, hlen]; unfold natSLimbCount; omega
               obtain ⟨hll, _, hvalL, harrL⟩ :=
                 bytes_eq_array64_of_len_mul8 (a := p + 16#64) (k := natSLimbCount len.toNat)
                   hfullLen (by dsimp only [totalB] at htb64; omega)
               let limbs := bytesToLimbs64 (natSLimbCount len.toNat) fullBs
               have hvalS : limbsVal limbs = natOfBytesS srcData := by
                 dsimp only [limbs]; rw [hvalL]
                 dsimp only [fullBs]
                 rw [bytesToNatLE_append, bytesToNatLE_replicate_zero,
                   Nat.mul_zero, Nat.add_zero]
                 exact (natOfBytesS_eq_bytesToNatLE_snoc srcData).symm
               have hcanons := mkMpzNatObj_canon_of_natOfBytesS hp0 hp8 (by omega)
                 (by rw [hlen]; exact hvalid.1) (by rw [hlen]; exact hll) hvalS
               have hevenP : (p &&& 1#64) = 0#64 := bv64_and1_zero_of_mod8 hp8
               have hmObj : (rtC0Inv rt st' ⋆ lcnfObjMem (mkMpzNatObj p limbs) ⋆
                   bytes srcPtr srcData ⋆ R) mL := by
                 rw [lcnfObjMem_mkMpzNatObj, show BitVec.ofNat 64 limbs.length =
                     BitVec.ofNat 64 (natSLimbCount len.toNat) from by rw [hll],
                   ← hmetaDef, ← harrL]
                 dsimp only [fullBs]
                 exact sep_ac hmL
               exact hPost p st' (mkMpzNatObj p limbs) mL hp0 hp8 hevenP hpr hremLe hremLo rfl
                 hcanons.1 hcanons.2 hmObj)
    · rw [ite_eq_right hvalid] at hPost
      by_cases hcap : len.toNat ≤ ffiNatMaxBytes
      · have hszBv := ffi_nat_sz_bv len hcap hgt7
        ffi2_steps <;> first
          | exact hPost
          | (exfalso; unfold ffiNatMaxBytes at hcap
             have hc : 268435431 < len.toNat := by assumption
             omega)
          | (exfalso
             have hc : st.hdr.s_end.toNat < st.hdr.s_cur.toNat := by assumption
             have := st.curLeEnd; omega)
          | (exfalso
             try rw [ffi2_sub_rem_eq st] at *
             try rw [ffi2_sz_rhs_eq len hcap hgt7] at *
             exact hvalid ⟨hcap, by omega⟩)
      · ffi2_steps <;> first
          | exact hPost
          | (exfalso; unfold ffiNatMaxBytes at hcap
             have hc : ¬ 268435431 < len.toNat := by assumption
             omega)

theorem lcnf_ffi_nat_wrap_ok_wp :
    ∀ xs m Q X, ffiNatWrapOkSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_nat_wrap_ok.body xs m Q X := by
  intro ⟨rt, srcPtr, len, ⟨⟩⟩ m Q X ⟨st, srcData, R, hlen, hm, hPost⟩
  dsimp only [Func.wp, lcnf_ffi_nat_wrap_ok, lcnf_ffi_nat_wrap_ok_body]
  by_cases hle7 : len.toNat ≤ 7
  · rw [ite_eq_left hle7] at hPost
    by_cases hrem16 : 16 ≤ st.rem
    · rw [ite_eq_left hrem16] at hPost
      ffi2_steps <;> first
        | (ffi2_call ffiEnv_nat_of_bytes
           dsimp only [ffiNatOfBytesSpec, vals, Tup.map, Arg.val]
           refine ⟨st, srcData, R, hlen, hm, ?_⟩
           rw [ite_eq_left hle7]
           ffi2_steps
           ffi2_call ffiEnv_mk_ok
           dsimp only [ffiMkOkSpec, vals, Tup.map, Arg.val]
           refine ⟨st, bytes srcPtr srcData ⋆ R,
             (sep_ac hm : (rtC0Inv rt st ⋆ (bytes srcPtr srcData ⋆ R)) m), ?_⟩
           rw [ite_eq_left hrem16]
           intro p st' m' hp0 hp8 hpr hremLe hremLo hokCanon hm'
           ffi2_steps
           exact hPost p st' m' hp0 hp8 hpr hremLe hremLo hokCanon (sep_ac hm'))
        | (exfalso; have hc : st.hdr.s_end.toNat < st.hdr.s_cur.toNat := by assumption
           have := st.curLeEnd; omega)
        | (exfalso; try rw [ffi2_sub_rem_eq st] at *
           try rw [show (16 : BitVec 64).toNat = 16 from rfl] at *; omega)
    · rw [ite_eq_right hrem16] at hPost
      ffi2_steps <;> first
        | exact hPost
        | (exfalso; try rw [ffi2_sub_rem_eq st] at *
           try rw [show (16 : BitVec 64).toNat = 16 from rfl] at *; omega)
  · rw [ite_eq_right hle7] at hPost
    have hgt7 : 7 < len.toNat := Nat.lt_of_not_le hle7
    by_cases hvalid : len.toNat ≤ ffiNatMaxBytes ∧ natSAllocBytes len.toNat + 16 ≤ st.rem
    · rw [ite_eq_left hvalid] at hPost
      ffi2_steps <;> first
        | (ffi2_call ffiEnv_nat_of_bytes
           dsimp only [ffiNatOfBytesSpec, vals, Tup.map, Arg.val]
           refine ⟨st, srcData, R, hlen, hm, ?_⟩
           rw [ite_eq_right hle7, ite_eq_left ⟨hvalid.1, by omega⟩]
           intro natP st1 newObj m1 hnat0 hnat8 hnatEven hpr1 hrem1Le hrem1Lo haddr hrtCan
             hmpzCan hm1
           ffi2_steps
           ffi2_call ffiEnv_mk_ok
           dsimp only [ffiMkOkSpec, vals, Tup.map, Arg.val]
           refine ⟨st1, lcnfObjMem newObj ⋆ bytes srcPtr srcData ⋆ R, sep_ac hm1, ?_⟩
           have hrem16 : 16 ≤ st1.rem := by omega
           rw [ite_eq_left hrem16]
           intro p st2 m2 hp0 hp8 hpr2 hrem2Le hrem2Lo hokCanon hm2
           ffi2_steps
           exact hPost p natP st2 newObj m2 hp0 hp8 hnat0 hnat8 hnatEven (hpr1.trans hpr2)
             (by omega) (by omega) haddr hrtCan hmpzCan hokCanon (sep_ac hm2))
        | (unfold ffiNatMaxBytes at hvalid
           have hc := (by assumption : 268435431 < len.toNat); omega)
        | (have hc := (by assumption : st.hdr.s_end.toNat < st.hdr.s_cur.toNat)
           have := st.curLeEnd; omega)
        | (exfalso; try rw [ffi2_sub_rem_eq st] at *
           try rw [ffi2_wrap_sz_rhs_eq len hvalid.1 hgt7] at *; omega)
    · rw [ite_eq_right hvalid] at hPost
      by_cases hcap : len.toNat ≤ ffiNatMaxBytes
      · ffi2_steps <;> first
          | exact hPost
          | (unfold ffiNatMaxBytes at hcap
             have hc := (by assumption : 268435431 < len.toNat); omega)
          | (have hc := (by assumption : st.hdr.s_end.toNat < st.hdr.s_cur.toNat)
             have := st.curLeEnd; omega)
          | (exfalso; try rw [ffi2_sub_rem_eq st] at *
             try rw [ffi2_wrap_sz_rhs_eq len hcap hgt7] at *
             exact hvalid ⟨hcap, by omega⟩)
      · ffi2_steps <;> first
          | exact hPost
          | (unfold ffiNatMaxBytes at hcap
             have hc := (by assumption : ¬ 268435431 < len.toNat); omega)

/-! ## 4. Bidirectional `O(N)` `ByteArray ↔ Sentineled Nat` Bridge Proofs -/

theorem lcnf_ffi_ba_to_nat_s_wp :
    ∀ xs m Q X, ffiBaToNatSSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_ba_to_nat_s.body xs m Q X := by
  intro ⟨rt, ba, ⟨⟩⟩ m Q X ⟨st, baObj, R, haddr, hcanon, hm, hPost⟩
  subst haddr
  dsimp only [Func.wp, lcnf_ffi_ba_to_nat_s, lcnf_ffi_ba_to_nat_s_body]
  ffi2_steps
  ffi2_call ffiEnv_ba_len
  dsimp only [ffiBaLenSpec, vals, Tup.map, Arg.val]
  refine ⟨baObj, rtC0Inv rt st ⋆ R, rfl, hcanon, sep_ac hm, ?_⟩
  ffi2_steps
  ffi2_call ffiEnv_nat_wrap_ok
  dsimp only [ffiNatWrapOkSpec, vals, Tup.map, Arg.val]
  have hbaEq := lcnfObjMem_sarray_eq hcanon.2.2.2.2.2.1
  rw [hbaEq] at hm
  let objFrame : Mem 64 → Prop :=
    cell64 baObj.addr baObj.header ⋆
    cell64 (baObj.addr + 8#64) (BitVec.ofNat 64 baObj.arrSize) ⋆
    cell64 (baObj.addr + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
    region (baObj.addr + BitVec.ofNat 64 (24 + baObj.scalarData.length))
      (baObj.totalBytes - (24 + baObj.scalarData.length)) ⋆ R
  have hmUnpack : (rtC0Inv rt st ⋆ bytes (baObj.addr + 24#64) baObj.scalarData ⋆ objFrame) m := by
    dsimp only [objFrame]; exact sep_ac hm
  have hcapLt : baObj.scalarData.length ≤ ffiBaMaxCap := by
    have h1 := hcanon.2.2.2.2.2.2.1
    have h2 := hcanon.2.2.2.2.2.2.2.1
    have h3 := hcanon.2.2.2.2.2.2.2.2
    unfold baMaxCap ffiBaMaxCap at *
    omega
  have hlenNatMax : (BitVec.ofNat 64 baObj.scalarData.length).toNat ≤ ffiNatMaxBytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold ffiBaMaxCap at hcapLt; omega)]
    unfold ffiBaMaxCap ffiNatMaxBytes at *
    omega
  have hlenToNat : (BitVec.ofNat 64 baObj.scalarData.length).toNat = baObj.scalarData.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold ffiBaMaxCap at hcapLt; omega)]
  refine ⟨st, baObj.scalarData, objFrame, hlenToNat.symm, hmUnpack, ?_⟩
  rw [hlenToNat]
  dsimp only at hPost
  by_cases hle7 : baObj.scalarData.length ≤ 7
  · rw [ite_eq_left hle7] at hPost
    rw [ite_eq_left hle7]
    split at hPost
    · rename_i hrem
      rw [ite_eq_left hrem]
      intro p st' m' hp0 hp8 hpr hremLe hremLo hokCanon hm'
      have hmRepack : (rtC0Inv rt st' ⋆
          lcnfObjMem (mkFfiResOkObj p (boxNat (natOfBytesS baObj.scalarData))) ⋆
          lcnfObjMem baObj ⋆ R) m' := by
        rw [hbaEq]; dsimp only [objFrame] at hm'; exact sep_ac hm'
      exact hPost p st' m' hp0 hp8 hpr hremLe hremLo hokCanon hmRepack
    · rename_i hrem
      rw [ite_eq_right hrem]
      exact hPost
  · rw [ite_eq_right hle7] at hPost
    rw [ite_eq_right hle7]
    by_cases hrem : natSAllocBytes baObj.scalarData.length + 16 ≤ st.rem
    · have hvalid : baObj.scalarData.length ≤ ffiNatMaxBytes ∧
          natSAllocBytes baObj.scalarData.length + 16 ≤ st.rem := by
        rw [hlenToNat] at hlenNatMax
        exact ⟨hlenNatMax, hrem⟩
      rw [ite_eq_left hrem] at hPost
      rw [ite_eq_left hvalid]
      intro p natP st' newObj m' hp0 hp8 hnat0 hnat8 hnatEven hpr hremLe hremLo haddr hrtCan
        hmpzCan hokCanon hm'
      have hmRepack : (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p natP) ⋆ lcnfObjMem newObj ⋆
          lcnfObjMem baObj ⋆ R) m' := by
        rw [hbaEq]; dsimp only [objFrame] at hm'; exact sep_ac hm'
      exact hPost p natP st' newObj m' hp0 hp8 hnat0 hnat8 hnatEven hpr hremLe hremLo haddr hrtCan
        hmpzCan hokCanon hmRepack
    · have hnot : ¬ (baObj.scalarData.length ≤ ffiNatMaxBytes ∧
          natSAllocBytes baObj.scalarData.length + 16 ≤ st.rem) := fun h => hrem h.2
      rw [ite_eq_right hrem] at hPost
      rw [ite_eq_right hnot]
      exact hPost

theorem lcnf_ffi_nat_s_to_ba_wp :
    ∀ xs m Q X, ffiNatSToBaSpec xs m Q X →
      Func.wp ffiEnv lcnf_ffi_nat_s_to_ba.body xs m Q X := by
  intro ⟨rt, a, ⟨⟩⟩ m Q X ⟨st, scr, scrLimbs, val, objs, R, hcapLt, hrep, hm, hPost⟩
  dsimp only [Func.wp, lcnf_ffi_nat_s_to_ba, lcnf_ffi_nat_s_to_ba_body]
  ffi2_steps
  ffi2_call ffiEnv_nat_bytes_len
  dsimp only [ffiNatBytesLenSpec, vals, Tup.map, Arg.val]
  refine ⟨val, objs,
    rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrLimbs ⋆ R,
    hrep, sep_ac hm, ?_⟩
  cases hbs : bytesOfNatS val with
  | none =>
    rw [hbs] at hPost
    dsimp only at hPost ⊢
    ffi2_steps <;> first
      | exact hPost
      | (exfalso
         have hc : ffiInvalidLen ≠ 18446744073709551615#64 := by assumption
         exact hc rfl)
  | some bs =>
    rw [hbs] at hPost
    dsimp only at hPost ⊢
    have hnatEq : natOfBytesS bs = val := natOfBytesS_of_bytesOfNatS hbs
    have hbsMax : bs.length ≤ ffiNatMaxBytes := by
      by_cases hsmall : val < 2 ^ 63
      · have := (natOfBytesS_lt_2p63_iff bs).mp (by rwa [hnatEq])
        unfold ffiNatMaxBytes; omega
      · rw [RtNatRep, ite_eq_right hsmall] at hrep
        rcases hrep with ⟨_, obj, _, _, hcanon⟩
        rw [← hnatEq] at hcanon
        have hlimbs := (mpzNatCanon_natOfBytesS_bytesN8 hcanon).2.1
        have hmax := hcanon.2.2.2.2.2.1
        unfold natSLimbCount ffiMpzMaxLimbs ffiNatMaxBytes at *
        omega
    have hbsNeInv : BitVec.ofNat 64 bs.length ≠ ffiInvalidLen := fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold ffiNatMaxBytes at hbsMax; omega),
        show ffiInvalidLen.toNat = 2 ^ 64 - 1 from by decide] at this
      unfold ffiNatMaxBytes at hbsMax
      omega
    ffi2_steps
    · exfalso; exact hbsNeInv (by assumption)
    · ffi2_call ffiEnv_nat_bytes_ptr
      dsimp only [ffiNatBytesPtrSpec, vals, Tup.map, Arg.val]
      by_cases hsmall : val < 2 ^ 63
      · have hle7 : bs.length ≤ 7 := (natOfBytesS_lt_2p63_iff bs).mp (by rwa [hnatEq])
        rw [RtNatRep, ite_eq_left hsmall] at hrep
        have hand1 : (a &&& 1#64) = 1#64 := by
          rw [hrep]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            show (1 : Nat) % 2 ^ 64 = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : 2 * val + 1 < 2 ^ 64)]
          change (2 * val + 1) &&& (2 ^ 1 - 1) = 1
          rw [Nat.and_two_pow_sub_one_eq_mod, Nat.pow_one]
          omega
        have hodd : (a &&& 1#64) ≠ 0#64 := by rw [hand1]; decide
        have hshr1 : (a >>> 1) = BitVec.ofNat 64 (natOfBytesS bs) := by
          rw [hrep, hnatEq]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.shiftRight_eq_div_pow, Nat.pow_one,
            Nat.mod_eq_of_lt (by omega : 2 * val + 1 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : val < 2 ^ 64)]
          omega
        rw [ite_eq_left hodd]
        refine ⟨scr, scrLimbs, rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R, hcapLt, sep_ac hm, ?_⟩
        by_cases hmiss : scr = 0#64 ∨ scrLimbs.length = 0
        · have hcond : bs.length ≤ 7 ∧ (scr = 0#64 ∨ scrLimbs.length = 0) := ⟨hle7, hmiss⟩
          rw [ite_eq_left hmiss]
          rw [ite_eq_left hcond] at hPost
          ffi2_steps <;> first
            | exact hPost
            | (exfalso; exact hodd ‹(a &&& 1#64) = 0#64›)
            | (exfalso; exact ‹(0#64 : BitVec 64) ≠ 0› rfl)
        · have hscrNz : scr ≠ 0#64 := fun h => hmiss (Or.inl h)
          have hlenPos : 0 < scrLimbs.length := Nat.pos_of_ne_zero fun h => hmiss (Or.inr h)
          have hnotCond : ¬ (bs.length ≤ 7 ∧ (scr = 0#64 ∨ scrLimbs.length = 0)) :=
            fun h => hmiss h.2
          rw [ite_eq_right hmiss]
          rw [ite_eq_right hnotCond] at hPost
          intro m1 hm1
          rw [hshr1] at hm1
          rw [ite_eq_left hle7] at hPost
          ffi2_steps <;> first
            | (exfalso; exact hodd ‹(a &&& 1#64) = 0#64›)
            | (exfalso; exact hscrNz ‹scr = 0#64›)
            | (let scrLimbs' := scrLimbs.set 0 (BitVec.ofNat 64 (natOfBytesS bs))
               have hcons : scrLimbs' = BitVec.ofNat 64 (natOfBytesS bs) :: scrLimbs'.tail := by
                 cases hscr : scrLimbs with
                 | nil => simp [hscr] at hlenPos
                 | cons _ tl => simp [scrLimbs', hscr, List.set_cons_zero]
               have hcellSplit := taggedNat_natOfBytesS_cell64_split scr hle7
               have hm1bytes : (bytes scr bs ⋆
                   (bytes (scr + BitVec.ofNat 64 bs.length)
                     ([1] ++ List.replicate (7 - bs.length) 0) ⋆
                     array64 (scr + 8#64) scrLimbs'.tail ⋆
                     cell64 (rt + 33672#64) scr ⋆
                     cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                     rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m1 := by
                 change (cell64 (rt + 33672#64) scr ⋆
                   cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                   array64 scr scrLimbs' ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m1 at hm1
                 rw [hcons, array64_cons, hcellSplit] at hm1
                 exact sep_ac hm1
               ffi2_call ffiEnv_ba_wrap_ok
               dsimp only [ffiBaWrapOkSpec, vals, Tup.map, Arg.val]
               let frame' : Mem 64 → Prop :=
                 bytes (scr + BitVec.ofNat 64 bs.length)
                   ([1] ++ List.replicate (7 - bs.length) 0) ⋆
                 array64 (scr + 8#64) scrLimbs'.tail ⋆
                 cell64 (rt + 33672#64) scr ⋆
                 cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                 lcnfHeap objs ⋆ R
               have hbsToNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
                 rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
               refine ⟨st, bs, frame', hbsToNat.symm,
                 (by dsimp only [frame']; exact sep_ac hm1bytes), ?_⟩
               rw [hbsToNat]
               by_cases hfit : bs.length ≤ ffiBaMaxCap ∧ baAllocBytes bs.length + 16 ≤ st.rem
               · rw [ite_eq_left hfit] at hPost ⊢
                 intro p ba st' m2 hp0 hp8 hba0 hba8 hpr hremLe hremLo hbaCan hokCan hm2
                 have hm2' : (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
                     cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                     array64 scr scrLimbs' ⋆ lcnfObjMem (mkFfiResOkObj p ba) ⋆
                     lcnfObjMem (mkBaObj ba 1#32 bs.length bs) ⋆ lcnfHeap objs ⋆ R) m2 := by
                   rw [hcons, array64_cons, hcellSplit]
                   dsimp only [frame'] at hm2
                   exact sep_ac hm2
                 exact hPost p ba st' m2 hp0 hp8 hba0 hba8 hpr hremLe hremLo hbaCan hokCan hm2'
               · rw [ite_eq_right hfit] at hPost ⊢
                 exact hPost m1 (sep_ac hm1))
      · have hge8 : 8 ≤ bs.length := Nat.le_of_not_lt fun hlt =>
          hsmall (by rw [← hnatEq]; exact natOfBytesS_lt_2p63 (by omega))
        have hnotLe7 : ¬ bs.length ≤ 7 := by omega
        have hnotCond : ¬ (bs.length ≤ 7 ∧ (scr = 0#64 ∨ scrLimbs.length = 0)) :=
          fun h => hnotLe7 h.1
        rw [RtNatRep, ite_eq_right hsmall] at hrep
        rcases hrep with ⟨heven, obj, hmem, haddr, hcanon⟩
        subst haddr
        have hnotOdd : ¬ (obj.addr &&& 1#64) ≠ 0#64 := fun h => h heven
        rw [ite_eq_right hnotOdd]
        rw [ite_eq_right hnotCond] at hPost
        rw [ite_eq_right hnotLe7] at hPost
        ffi2_steps <;> first
          | (exfalso; rw [heven] at *; contradiction)
          | (obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmem
             have hcanonS : RtMpzNatCanon objs[idx] (natOfBytesS bs) := hnatEq ▸ hcanon
             let tailBytes : Mem 64 → Prop :=
               bytes (objs[idx].addr + 16#64 + BitVec.ofNat 64 bs.length)
                 ([1] ++ List.replicate (8 * objs[idx].limbs.length - bs.length - 1) 0)
             have hmHeap : (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                 cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                 array64 scr scrLimbs ⋆ R)) m := sep_ac hm
             rw [lcnfHeap_focus objs hidx, ffi2_lcnfObjMem_mpz_eq hcanonS.2.1,
               mpzNatCanon_natOfBytesS_split hcanonS] at hmHeap
             change (cell64 objs[idx].addr objs[idx].header ⋆
                 cell64 (objs[idx].addr + 8#64) objs[idx].mpzMeta ⋆
                 (bytes (objs[idx].addr + 16#64) bs ⋆ tailBytes) ⋆
               (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))) ⋆
               (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                 cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                 array64 scr scrLimbs ⋆ R)) m at hmHeap
             ffi2_call ffiEnv_ba_wrap_ok
             dsimp only [ffiBaWrapOkSpec, vals, Tup.map, Arg.val]
             let frame' : Mem 64 → Prop :=
               tailBytes ⋆
               cell64 objs[idx].addr objs[idx].header ⋆
               cell64 (objs[idx].addr + 8#64) objs[idx].mpzMeta ⋆
               lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1)) ⋆
               cell64 (rt + 33672#64) scr ⋆
               cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
               array64 scr scrLimbs ⋆ R
             have hbsToNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
               rw [BitVec.toNat_ofNat,
                 Nat.mod_eq_of_lt (by unfold ffiNatMaxBytes at hbsMax; omega)]
             refine ⟨st, bs, frame', hbsToNat.symm,
               (by dsimp only [frame']; exact sep_ac hmHeap), ?_⟩
             rw [hbsToNat]
             by_cases hfit : bs.length ≤ ffiBaMaxCap ∧ baAllocBytes bs.length + 16 ≤ st.rem
             · rw [ite_eq_left hfit] at hPost ⊢
               intro p ba st' m2 hp0 hp8 hba0 hba8 hpr hremLe hremLo hbaCan hokCan hm2
               have hm2' : (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
                   cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                   array64 scr scrLimbs ⋆ lcnfObjMem (mkFfiResOkObj p ba) ⋆
                   lcnfObjMem (mkBaObj ba 1#32 bs.length bs) ⋆ lcnfHeap objs ⋆ R) m2 := by
                 rw [lcnfHeap_focus objs hidx, ffi2_lcnfObjMem_mpz_eq hcanonS.2.1,
                   mpzNatCanon_natOfBytesS_split hcanonS]
                 change (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
                   cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                   array64 scr scrLimbs ⋆ lcnfObjMem (mkFfiResOkObj p ba) ⋆
                   lcnfObjMem (mkBaObj ba 1#32 bs.length bs) ⋆
                   (cell64 objs[idx].addr objs[idx].header ⋆
                     cell64 (objs[idx].addr + 8#64) objs[idx].mpzMeta ⋆
                     (bytes (objs[idx].addr + 16#64) bs ⋆ tailBytes) ⋆
                     (lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1)))) ⋆ R) m2
                 dsimp only [frame'] at hm2
                 exact sep_ac hm2
               exact hPost p ba st' m2 hp0 hp8 hba0 hba8 hpr hremLe hremLo hbaCan hokCan hm2'
             · rw [ite_eq_right hfit] at hPost ⊢
               exact hPost m hm)

end LeanQbe.T.LeanLCNF
