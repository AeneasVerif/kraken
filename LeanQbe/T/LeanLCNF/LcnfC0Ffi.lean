module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Module
public import LeanQbe.T.Wf
public meta import LeanQbe.T.Frontend.C0

/-!
# Data-Pure Verified C0 FFI Adapters (`LcnfC0Ffi`, Shard F2)

Purely additive, data-pure (`0` `*Proof*`/`*Spec*` imports) C0 FFI adapter library and pure-Lean
sentineled `Nat`-as-Bytes specification bridging `LeanLCNF` carriers (`ByteArray` and sentineled
`Nat`) with runtime-agnostic raw `(ptr, len)` C0 kernels:

1. **Pure Lean FFI carrier types & sentineled `Nat`-as-Bytes math**:
   - `SolveStatus` and `FfiRes α` (all error constructors are 0-field tagged scalars -> 0 B alloc).
   - `bytesToNatLE`, `natOfBytesS bs := 2^(8 * bs.length) + bytesToNatLE bs`, `natToBytesLE`,
     `isValidNatBytesS`, `bytesOfNatS`, `sentinelByteIdx`, plus exact round-trip and
     `L ≤ 7` (tagged) vs `L ≥ 8` (boxed `MPZ`) split theorems.
2. **Acyclic pure C0 adapter module (`ffiMod`, 15 functions, `<= 3` SysV args/fn, `0` `alloca`,
   `0` `lcnf_panic` calls, `exits = []`)**:
   - Top-down `s_end` scratch carve/reclaim (`lcnf_ffi_get_end`, `lcnf_ffi_carve_scratch`,
     `lcnf_ffi_restore_scratch`).
   - `ByteArray` (`BaCanon`, tag `248`, `ba + 24`) read & `FfiRes.ok` wrap helpers
     (`lcnf_ffi_ba_ptr`, `lcnf_ffi_ba_len`, `lcnf_ffi_mk_ok`, `lcnf_ffi_ba_of_bytes`,
     `lcnf_ffi_ba_wrap_ok`).
   - Sentineled `Nat` read/write helpers handling `L ≤ 7` tagged staging in `rt->scratch[0]` vs
     `L ≥ 8` zero-copy `MPZ` limbs at `p + 16`, plus automatic canonical `MPZ` construction
     (`lcnf_ffi_sentinel_byte_idx`, `lcnf_ffi_nat_bytes_len`, `lcnf_ffi_nat_bytes_ptr`,
     `lcnf_ffi_nat_of_bytes`, `lcnf_ffi_nat_wrap_ok`).
   - `O(N)` `ByteArray ↔ Sentineled Nat` bridges (`lcnf_ffi_ba_to_nat_s`, `lcnf_ffi_nat_s_to_ba`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0

/-! ## 1. Pure Lean FFI Carrier Types & Layout Constants -/

/-- Decision-kernel status (all 0-field ctors -> unboxed scalar, 0 B allocation). -/
inductive SolveStatus where
  | unknown
  | sat
  | unsat
  | oom
  | invalidInput
  deriving Repr, BEq, DecidableEq

/-- Value-returning FFI result: only `.ok` allocates (`16` B ctor 0); errors are 0 B scalars. -/
inductive FfiRes (α : Type) where
  | ok (val : α)
  | invalidInput
  | oom
  | outOfFuel
  deriving Repr, BEq, DecidableEq

/-- Packed 64-bit header for `FfiRes.ok` (`rc = 1, cs_sz = 16, other = 1, tag = 0`). -/
@[expose] def ffiResOkHeader : BitVec 64 := 0x0001001000000001#64

/-- Tagged scalar encoding of `FfiRes.invalidInput` (ctor 1 -> `(1 << 1) | 1 = 3`). -/
@[expose] def ffiResInvalidInputWord : BitVec 64 := 3#64

/-- Tagged scalar encoding of `FfiRes.oom` (ctor 2 -> `(2 << 1) | 1 = 5`). -/
@[expose] def ffiResOomWord : BitVec 64 := 5#64

/-- Tagged scalar encoding of `FfiRes.outOfFuel` (ctor 3 -> `(3 << 1) | 1 = 7`). -/
@[expose] def ffiResOutOfFuelWord : BitVec 64 := 7#64

/-- Error sentinel returned by `lcnf_ffi_nat_bytes_len` on an invalid sentineled `Nat`. -/
@[expose] def ffiInvalidLen : BitVec 64 := 0xffffffffffffffff#64

/-- Maximum `ByteArray` payload length (`baMaxCap = 268,435,416`). -/
@[expose] def ffiBaMaxCap : Nat := 268435416

/-- Maximum `MPZ` limb count (`mpzMaxLimbs = 33,554,429`). -/
@[expose] def ffiMpzMaxLimbs : Nat := 0x01fffffd

/-- Maximum byte length for a sentineled `Nat` (`8 * (mpzMaxLimbs - 1) + 7 = 268,435,431`). -/
@[expose] def ffiNatMaxBytes : Nat := 268435431

/-! ## 2. Pure Sentineled `Nat`-as-Bytes Specification & Round-Trip Algebra -/

/-- Little-endian natural value of a byte list: `bs[0] + 256 * bs[1] + ...`. -/
@[expose] def bytesToNatLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNatLE bs

/-- Sentineled little-endian `Nat` encoding of an exact byte slice:
`natOfBytesS bs = 2 ^ (8 * bs.length) + bytesToNatLE bs`.
Preserves trailing `0x00` bytes and splits cleanly at `L ≤ 7` (tagged) vs `L ≥ 8` (boxed MPZ). -/
@[expose] def natOfBytesS (bs : List UInt8) : Nat :=
  2 ^ (8 * bs.length) + bytesToNatLE bs

/-- Extract `k` little-endian bytes from `n`. -/
@[expose] def natToBytesLE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: natToBytesLE k (n / 256)

/-- Whether `n : Nat` is a valid sentineled byte buffer (`n ≥ 1` and `n.log2 % 8 = 0`). -/
@[expose] def isValidNatBytesS (n : Nat) : Bool :=
  decide (0 < n ∧ n.log2 % 8 = 0)

/-- Decode a sentineled `Nat` into its exact `List UInt8`, or `none` if the sentinel is invalid. -/
@[expose] def bytesOfNatS (n : Nat) : Option (List UInt8) :=
  if 0 < n ∧ n.log2 % 8 = 0 then
    some (natToBytesLE (n.log2 / 8) n)
  else
    none

/-- Pure model of `lcnf_ffi_sentinel_byte_idx(w)`: index `k ∈ [0..7]` of the highest nonzero byte
of `w` when that byte equals `1`, or `8` if `w = 0` or the highest nonzero byte is not `1`. -/
@[expose] def sentinelByteIdx (w : BitVec 64) : Nat :=
  if w = 0#64 then 8
  else if w.toNat.log2 % 8 = 0 then w.toNat.log2 / 8
  else 8

theorem bytesToNatLE_nil : bytesToNatLE [] = 0 := rfl

theorem bytesToNatLE_cons (b : UInt8) (bs : List UInt8) :
    bytesToNatLE (b :: bs) = b.toNat + 256 * bytesToNatLE bs := rfl

theorem bytesToNatLE_lt (bs : List UInt8) : bytesToNatLE bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [bytesToNatLE]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    have hpow : 2 ^ (8 * (bs.length + 1)) = 256 * 2 ^ (8 * bs.length) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    simp only [bytesToNatLE, List.length_cons, hpow]
    omega

theorem bytesToNatLE_append (xs ys : List UInt8) :
    bytesToNatLE (xs ++ ys) = bytesToNatLE xs + 2 ^ (8 * xs.length) * bytesToNatLE ys := by
  induction xs with
  | nil => simp [bytesToNatLE]
  | cons x xs ih =>
    have hpow : 2 ^ (8 * (xs.length + 1)) = 256 * 2 ^ (8 * xs.length) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    simp only [List.cons_append, bytesToNatLE, ih, List.length_cons, hpow]
    rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem bytesToNatLE_replicate_zero (k : Nat) :
    bytesToNatLE (List.replicate k (0 : UInt8)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [List.replicate_succ, bytesToNatLE, ih]

theorem natOfBytesS_eq_bytesToNatLE_snoc (bs : List UInt8) :
    natOfBytesS bs = bytesToNatLE (bs ++ [1]) := by
  rw [bytesToNatLE_append]
  have h1 : bytesToNatLE [1] = 1 := rfl
  rw [h1, Nat.mul_one, Nat.add_comm]
  rfl

theorem natOfBytesS_pos (bs : List UInt8) : 0 < natOfBytesS bs := by
  unfold natOfBytesS
  have hp : 0 < 2 ^ (8 * bs.length) := Nat.pow_pos (by decide)
  omega

theorem natOfBytesS_bounds (bs : List UInt8) :
    2 ^ (8 * bs.length) ≤ natOfBytesS bs ∧ natOfBytesS bs < 2 ^ (8 * bs.length + 1) := by
  unfold natOfBytesS
  have hlt := bytesToNatLE_lt bs
  have h2 : 2 ^ (8 * bs.length + 1) = 2 ^ (8 * bs.length) + 2 ^ (8 * bs.length) := by
    rw [Nat.pow_succ]; omega
  omega

theorem natOfBytesS_log2 (bs : List UInt8) : (natOfBytesS bs).log2 = 8 * bs.length := by
  have hpos : natOfBytesS bs ≠ 0 := Nat.ne_of_gt (natOfBytesS_pos bs)
  obtain ⟨hlo, hhi⟩ := natOfBytesS_bounds bs
  have hge : 8 * bs.length ≤ (natOfBytesS bs).log2 := (Nat.le_log2 hpos).mpr hlo
  have hlt : (natOfBytesS bs).log2 < 8 * bs.length + 1 := (Nat.log2_lt hpos).mpr hhi
  omega

theorem isValidNatBytesS_natOfBytesS (bs : List UInt8) :
    isValidNatBytesS (natOfBytesS bs) = true := by
  unfold isValidNatBytesS
  rw [decide_eq_true_eq, natOfBytesS_log2]
  exact ⟨natOfBytesS_pos bs, by omega⟩

theorem natToBytesLE_length (k n : Nat) : (natToBytesLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [natToBytesLE, ih]

theorem natToBytesLE_bytesToNatLE (bs : List UInt8) :
    natToBytesLE bs.length (bytesToNatLE bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [List.length_cons, bytesToNatLE, natToBytesLE]
    have hmod : (b.toNat + 256 * bytesToNatLE bs) % 256 = b.toNat := by omega
    have hdiv : (b.toNat + 256 * bytesToNatLE bs) / 256 = bytesToNatLE bs := by omega
    have hu : UInt8.ofNat b.toNat = b := by
      apply UInt8.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      simp
    rw [hmod, hdiv, hu, ih]

theorem natToBytesLE_add_mul_pow (k m q : Nat) :
    natToBytesLE k (q * 2 ^ (8 * k) + m) = natToBytesLE k m := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    have hpow : 2 ^ (8 * (k + 1)) = 256 * 2 ^ (8 * k) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    simp only [natToBytesLE, hpow]
    have hmul : q * (256 * 2 ^ (8 * k)) = 256 * (q * 2 ^ (8 * k)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm q 256, Nat.mul_assoc]
    rw [hmul]
    have hmod : (256 * (q * 2 ^ (8 * k)) + m) % 256 = m % 256 := by omega
    have hdiv : (256 * (q * 2 ^ (8 * k)) + m) / 256 = q * 2 ^ (8 * k) + m / 256 := by omega
    rw [hmod, hdiv, ih (m / 256)]

theorem bytesToNatLE_natToBytesLE (k n : Nat) :
    bytesToNatLE (natToBytesLE k n) = n % 2 ^ (8 * k) := by
  induction k generalizing n with
  | zero => simp [natToBytesLE, bytesToNatLE, Nat.mod_one]
  | succ k ih =>
    have hpow : 2 ^ (8 * (k + 1)) = 256 * 2 ^ (8 * k) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    simp only [natToBytesLE, bytesToNatLE, ih]
    have hu : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      simp [Nat.mod_mod_of_dvd]
    rw [hu, hpow]
    have hdm : n % (256 * 2 ^ (8 * k)) = n % 256 + 256 * ((n / 256) % 2 ^ (8 * k)) := by
      have h1 := Nat.mod_mul_right_div_self n 256 (2 ^ (8 * k))
      have h2 := Nat.div_add_mod (n % (256 * 2 ^ (8 * k))) 256
      have h3 : n % (256 * 2 ^ (8 * k)) % 256 = n % 256 :=
        Nat.mod_mod_of_dvd n (Nat.dvd_mul_right 256 (2 ^ (8 * k)))
      omega
    omega

theorem bytesToNatLE_inj {bs1 bs2 : List UInt8}
    (hlen : bs1.length = bs2.length)
    (hval : bytesToNatLE bs1 = bytesToNatLE bs2) : bs1 = bs2 := by
  have h1 := natToBytesLE_bytesToNatLE bs1
  have h2 := natToBytesLE_bytesToNatLE bs2
  rw [← h1, ← h2, hlen, hval]

/-- Exact round-trip: `bytesOfNatS (natOfBytesS bs) = some bs` for every byte list `bs`. -/
theorem bytesOfNatS_natOfBytesS (bs : List UInt8) :
    bytesOfNatS (natOfBytesS bs) = some bs := by
  unfold bytesOfNatS
  have hpos := natOfBytesS_pos bs
  have hlog := natOfBytesS_log2 bs
  have hcond : 0 < natOfBytesS bs ∧ (natOfBytesS bs).log2 % 8 = 0 := ⟨hpos, by rw [hlog]; omega⟩
  rw [ite_eq_left hcond, hlog, show 8 * bs.length / 8 = bs.length by omega]
  unfold natOfBytesS
  have hadd := natToBytesLE_add_mul_pow bs.length (bytesToNatLE bs) 1
  rw [Nat.one_mul] at hadd
  rw [hadd, natToBytesLE_bytesToNatLE]

/-- Exact inverse: any `n` decoding via `bytesOfNatS n = some bs` satisfies `natOfBytesS bs = n`. -/
theorem natOfBytesS_of_bytesOfNatS {n : Nat} {bs : List UInt8}
    (h : bytesOfNatS n = some bs) : natOfBytesS bs = n := by
  unfold bytesOfNatS at h
  split at h
  · rename_i hc
    have hbs := Option.some.inj h
    subst hbs
    rcases hc with ⟨hpos, hmod⟩
    have hnz : n ≠ 0 := Nat.ne_of_gt hpos
    have hlog : 8 * (n.log2 / 8) = n.log2 := by omega
    have hlo : 2 ^ (8 * (n.log2 / 8)) ≤ n := by
      rw [hlog]; exact (Nat.le_log2 hnz).mp (Nat.le_refl _)
    have hhi : n < 2 ^ (8 * (n.log2 / 8) + 1) := by
      rw [hlog]; exact (Nat.log2_lt hnz).mp (Nat.lt_succ_self _)
    have h2 : 2 ^ (8 * (n.log2 / 8) + 1) = 2 ^ (8 * (n.log2 / 8)) + 2 ^ (8 * (n.log2 / 8)) := by
      rw [Nat.pow_succ]; omega
    unfold natOfBytesS
    rw [natToBytesLE_length, bytesToNatLE_natToBytesLE]
    have hmodEq : n % 2 ^ (8 * (n.log2 / 8)) = n - 2 ^ (8 * (n.log2 / 8)) := by
      rw [Nat.mod_eq_sub_mod hlo, Nat.mod_eq_of_lt (by omega)]
    omega
  · nomatch h

theorem natOfBytesS_inj {bs1 bs2 : List UInt8}
    (h : natOfBytesS bs1 = natOfBytesS bs2) : bs1 = bs2 := by
  have h1 := bytesOfNatS_natOfBytesS bs1
  have h2 := bytesOfNatS_natOfBytesS bs2
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- Small sentineled byte slices (`L ≤ 7`) ALWAYS fit in a tagged scalar `Nat` (`< 2^63`). -/
theorem natOfBytesS_lt_2p63 {bs : List UInt8} (h : bs.length ≤ 7) :
    natOfBytesS bs < 2 ^ 63 := by
  have hhi := (natOfBytesS_bounds bs).2
  have hpow : 2 ^ (8 * bs.length + 1) ≤ 2 ^ 63 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Large sentineled byte slices (`L ≥ 8`) are ALWAYS boxed `MPZ` values (`≥ 2^63`). -/
theorem natOfBytesS_ge_2p63 {bs : List UInt8} (h : 8 ≤ bs.length) :
    2 ^ 63 ≤ natOfBytesS bs := by
  have hlo := (natOfBytesS_bounds bs).1
  have hpow : 2 ^ 63 ≤ 2 ^ (8 * bs.length) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Exact dual-representation boundary: `natOfBytesS bs < 2^63 ↔ bs.length ≤ 7`. -/
theorem natOfBytesS_lt_2p63_iff (bs : List UInt8) :
    natOfBytesS bs < 2 ^ 63 ↔ bs.length ≤ 7 := by
  constructor
  · intro hlt
    exact Nat.le_of_not_lt fun hgt =>
      Nat.not_lt_of_ge (natOfBytesS_ge_2p63 hgt) hlt
  · exact natOfBytesS_lt_2p63

/-! ## 3. Pure Acyclic C0 FFI Adapter Module (`ffiMod`) -/

/-- Pure C0 source for the FFI adapter library (`<= 3` args/fn, `0` `alloca`, `0` `lcnf_panic`).
Struct offsets match `LcnfC0FullRt` (`33688` B) byte-for-byte (`s.cur @ 33552`, `s.end @ 33560`,
`scratch @ 33672`, `scratch_cap @ 33680`). -/
@[expose] meta def lcnfC0FfiSrc : String := "
typedef struct {
  u64 allocs;
  u64 frees;
  u64 live;
  u64 peak_live;
  u64 persistent;
  u64 reused;
  u64 cold_decs;
  u64 bytes;
} LcnfC0FfiStats;

typedef struct {
  u64 large_free;
  u64 ba_empty;
  u64 cur;
  u64 end;
  u64 work;
  u64 work_cap;
  u64 chunks;
  u64 nchunks;
  u64 chunks_cap;
  LcnfC0FfiStats st;
} LcnfC0FfiHdr;

typedef struct {
  u64 extra_args[32];
  u64 globals[4096];
  u64 free_list[64];
  LcnfC0FfiHdr s;
} LcnfC0FfiBaseRt;

typedef struct {
  LcnfC0FfiBaseRt base;
  u64 scratch;
  u64 scratch_cap;
} LcnfC0FfiRt;

extern u64 lcnf_alloc(u64 rt, u64 sz);
extern void r2_mem_copy_bytes(u64 dst, u64 src, u64 len);

u64 lcnf_ffi_get_end(u64 rt) {
  LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
  return r->base.s.end;
}

u64 lcnf_ffi_carve_scratch(u64 rt, u64 req_bytes) {
  if (req_bytes == 0ULL || req_bytes > 0xfffffffffffffff8ULL) {
    return 0ULL;
  }
  LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
  u64 cur = r->base.s.cur;
  u64 end = r->base.s.end;
  u64 wend = end & 0xfffffffffffffff8ULL;
  u64 wcap = (req_bytes + 7ULL) & 0xfffffffffffffff8ULL;
  if (wend < cur || wcap > wend - cur) {
    return 0ULL;
  }
  u64 wptr = wend - wcap;
  r->base.s.end = wptr;
  return wptr;
}

void lcnf_ffi_restore_scratch(u64 rt, u64 saved_end) {
  LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
  r->base.s.end = saved_end;
}

u64 lcnf_ffi_ba_ptr(u64 ba) {
  return ba + 24ULL;
}

u64 lcnf_ffi_ba_len(u64 ba) {
  return *(u64 *)(ba + 8ULL);
}

u64 lcnf_ffi_mk_ok(u64 rt, u64 val) {
  LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
  u64 cur = r->base.s.cur;
  u64 end = r->base.s.end;
  if (end < cur || 16ULL > end - cur) {
    return 5ULL;
  }
  u64 p = lcnf_alloc(rt, 16ULL);
  *(u64 *)p = 0x0001001000000001ULL;
  *(u64 *)(p + 8ULL) = val;
  return p;
}

u64 lcnf_ffi_ba_of_bytes(u64 rt, u64 src_ptr, u64 len) {
  if (len > 268435416ULL) {
    return 0ULL;
  }
  LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
  u64 cur = r->base.s.cur;
  u64 end = r->base.s.end;
  u64 ba_bytes = (24ULL + len + 7ULL) & 0xfffffffffffffff8ULL;
  if (end < cur || ba_bytes > end - cur) {
    return 0ULL;
  }
  u64 p = lcnf_alloc(rt, ba_bytes);
  *(u64 *)p = 0xf801000000000001ULL;
  *(u64 *)(p + 8ULL) = len;
  *(u64 *)(p + 16ULL) = len;
  if (len > 0ULL) {
    r2_mem_copy_bytes(p + 24ULL, src_ptr, len);
  }
  return p;
}

u64 lcnf_ffi_ba_wrap_ok(u64 rt, u64 src_ptr, u64 len) {
  if (len > 268435416ULL) {
    return 5ULL;
  }
  LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
  u64 cur = r->base.s.cur;
  u64 end = r->base.s.end;
  u64 ba_bytes = (24ULL + len + 7ULL) & 0xfffffffffffffff8ULL;
  if (end < cur || ba_bytes + 16ULL > end - cur) {
    return 5ULL;
  }
  u64 ba = lcnf_ffi_ba_of_bytes(rt, src_ptr, len);
  return lcnf_ffi_mk_ok(rt, ba);
}

u64 lcnf_ffi_sentinel_byte_idx(u64 w) {
  if (w == 0ULL) {
    return 8ULL;
  }
  u64 k = 7ULL;
  while (k > 0ULL) {
    if (((w >> (8ULL * k)) & 0xffULL) != 0ULL) {
      break;
    }
    k = k - 1ULL;
  }
  if (((w >> (8ULL * k)) & 0xffULL) != 1ULL) {
    return 8ULL;
  }
  return k;
}

u64 lcnf_ffi_nat_bytes_len(u64 a) {
  if ((a & 1ULL) != 0ULL) {
    u64 v = a >> 1;
    u64 k = lcnf_ffi_sentinel_byte_idx(v);
    if (k >= 8ULL) {
      return 0xffffffffffffffffULL;
    }
    return k;
  }
  u64 nlimbs = *(u64 *)(a + 8ULL) >> 32;
  if (nlimbs == 0ULL || nlimbs > 0x01fffffdULL) {
    return 0xffffffffffffffffULL;
  }
  u64 top = ((u64 *)(a + 16ULL))[nlimbs - 1ULL];
  u64 k = lcnf_ffi_sentinel_byte_idx(top);
  if (k >= 8ULL) {
    return 0xffffffffffffffffULL;
  }
  return 8ULL * (nlimbs - 1ULL) + k;
}

u64 lcnf_ffi_nat_bytes_ptr(u64 rt, u64 a) {
  if ((a & 1ULL) != 0ULL) {
    LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
    u64 scr = r->scratch;
    u64 cap = r->scratch_cap;
    if (scr == 0ULL || cap == 0ULL) {
      return 0ULL;
    }
    *(u64 *)scr = a >> 1;
    return scr;
  }
  return a + 16ULL;
}

u64 lcnf_ffi_nat_of_bytes(u64 rt, u64 src_ptr, u64 len) {
  if (len <= 7ULL) {
    u64 v = 0ULL;
    u64 i = 0ULL;
    while (i < len) {
      u64 b = (u64)(*(u8 *)(src_ptr + i));
      v = v | (b << (8ULL * i));
      i = i + 1ULL;
    }
    v = v | (1ULL << (8ULL * len));
    return (v << 1) | 1ULL;
  }
  if (len > 268435431ULL) {
    return 0ULL;
  }
  u64 nlimbs = (len >> 3) + 1ULL;
  u64 sz = 16ULL + 8ULL * nlimbs;
  LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
  u64 cur = r->base.s.cur;
  u64 end = r->base.s.end;
  if (end < cur || sz > end - cur) {
    return 0ULL;
  }
  u64 p = lcnf_alloc(rt, sz);
  *(u64 *)p = 0xfa00000000000001ULL;
  *(u64 *)(p + 8ULL) = nlimbs | (nlimbs << 32);
  r2_mem_copy_bytes(p + 16ULL, src_ptr, len);
  *(u8 *)(p + 16ULL + len) = (u8)1;
  u64 pad_i = len + 1ULL;
  u64 total_b = 8ULL * nlimbs;
  while (pad_i < total_b) {
    *(u8 *)(p + 16ULL + pad_i) = (u8)0;
    pad_i = pad_i + 1ULL;
  }
  return p;
}

u64 lcnf_ffi_nat_wrap_ok(u64 rt, u64 src_ptr, u64 len) {
  LcnfC0FfiRt *r = (LcnfC0FfiRt *)rt;
  u64 cur = r->base.s.cur;
  u64 end = r->base.s.end;
  if (len <= 7ULL) {
    if (end < cur || 16ULL > end - cur) {
      return 5ULL;
    }
    u64 v = lcnf_ffi_nat_of_bytes(rt, src_ptr, len);
    return lcnf_ffi_mk_ok(rt, v);
  }
  if (len > 268435431ULL) {
    return 5ULL;
  }
  u64 nlimbs = (len >> 3) + 1ULL;
  u64 sz = 16ULL + 8ULL * nlimbs;
  if (end < cur || sz + 16ULL > end - cur) {
    return 5ULL;
  }
  u64 p = lcnf_ffi_nat_of_bytes(rt, src_ptr, len);
  return lcnf_ffi_mk_ok(rt, p);
}

u64 lcnf_ffi_ba_to_nat_s(u64 rt, u64 ba) {
  u64 len = lcnf_ffi_ba_len(ba);
  return lcnf_ffi_nat_wrap_ok(rt, ba + 24ULL, len);
}

u64 lcnf_ffi_nat_s_to_ba(u64 rt, u64 a) {
  u64 len = lcnf_ffi_nat_bytes_len(a);
  if (len == 0xffffffffffffffffULL) {
    return 3ULL;
  }
  u64 ptr = lcnf_ffi_nat_bytes_ptr(rt, a);
  if ((a & 1ULL) != 0ULL && ptr == 0ULL) {
    return 5ULL;
  }
  return lcnf_ffi_ba_wrap_ok(rt, ptr, len);
}
"

section ElabFfiC0
open Lean Elab Command in
local elab "lcnf_c0_ffi!" : command =>
  elabC0Module (some `lcnfFfi) lcnfC0FfiSrc (exits := []) (forceExpose := true)

lcnf_c0_ffi!
end ElabFfiC0

/-- Verified C0 FFI adapter module (`15` acyclic functions, `<= 3` args/fn, `0` exits, calling
only `lcnf_alloc` and `r2_mem_copy_bytes` from `rtC0CoreMod`). -/
@[expose] def ffiMod : Module :=
  { fns := lcnfFfi_fns
    externs :=
      [ { name := "lcnf_alloc", as := [i64, i64], rs := [i64] }
      , { name := "r2_mem_copy_bytes", as := [i64, i64, i64], rs := [] } ]
    exits := [] }

theorem lcnf_ffi_get_end_wf : Func.Wf lcnf_ffi_get_end_body := by t_wf_reify
theorem lcnf_ffi_carve_scratch_wf : Func.Wf lcnf_ffi_carve_scratch_body := by t_wf_reify
theorem lcnf_ffi_restore_scratch_wf : Func.Wf lcnf_ffi_restore_scratch_body := by t_wf_reify
theorem lcnf_ffi_ba_ptr_wf : Func.Wf lcnf_ffi_ba_ptr_body := by t_wf_reify
theorem lcnf_ffi_ba_len_wf : Func.Wf lcnf_ffi_ba_len_body := by t_wf_reify
theorem lcnf_ffi_mk_ok_wf : Func.Wf lcnf_ffi_mk_ok_body := by t_wf_reify
theorem lcnf_ffi_ba_of_bytes_wf : Func.Wf lcnf_ffi_ba_of_bytes_body := by t_wf_reify
theorem lcnf_ffi_ba_wrap_ok_wf : Func.Wf lcnf_ffi_ba_wrap_ok_body := by t_wf_reify
theorem lcnf_ffi_sentinel_byte_idx_wf : Func.Wf lcnf_ffi_sentinel_byte_idx_body := by t_wf_reify
theorem lcnf_ffi_nat_bytes_len_wf : Func.Wf lcnf_ffi_nat_bytes_len_body := by t_wf_reify
theorem lcnf_ffi_nat_bytes_ptr_wf : Func.Wf lcnf_ffi_nat_bytes_ptr_body := by t_wf_reify
theorem lcnf_ffi_nat_of_bytes_wf : Func.Wf lcnf_ffi_nat_of_bytes_body := by t_wf_reify
theorem lcnf_ffi_nat_wrap_ok_wf : Func.Wf lcnf_ffi_nat_wrap_ok_body := by t_wf_reify
theorem lcnf_ffi_ba_to_nat_s_wf : Func.Wf lcnf_ffi_ba_to_nat_s_body := by t_wf_reify
theorem lcnf_ffi_nat_s_to_ba_wf : Func.Wf lcnf_ffi_nat_s_to_ba_body := by t_wf_reify

theorem ffiMod_fns_wf : ∀ fn ∈ ffiMod.fns, Fn.Wf fn := by
  intro fn hfn
  simp only [ffiMod, lcnfFfi_fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact lcnf_ffi_get_end_wf
  · exact lcnf_ffi_carve_scratch_wf
  · exact lcnf_ffi_restore_scratch_wf
  · exact lcnf_ffi_ba_ptr_wf
  · exact lcnf_ffi_ba_len_wf
  · exact lcnf_ffi_mk_ok_wf
  · exact lcnf_ffi_ba_of_bytes_wf
  · exact lcnf_ffi_ba_wrap_ok_wf
  · exact lcnf_ffi_sentinel_byte_idx_wf
  · exact lcnf_ffi_nat_bytes_len_wf
  · exact lcnf_ffi_nat_bytes_ptr_wf
  · exact lcnf_ffi_nat_of_bytes_wf
  · exact lcnf_ffi_nat_wrap_ok_wf
  · exact lcnf_ffi_ba_to_nat_s_wf
  · exact lcnf_ffi_nat_s_to_ba_wf

theorem ffiMod_checkAcyclic : ffiMod.checkAcyclic = true := by
  t_kernel_rfl

theorem ffiMod_fns_length : ffiMod.fns.length = 15 := rfl

theorem ffiMod_sysv_args_le_6 : ∀ fn ∈ ffiMod.fns, fn.as.length ≤ 6 := by
  decide

end LeanQbe.T.LeanLCNF
