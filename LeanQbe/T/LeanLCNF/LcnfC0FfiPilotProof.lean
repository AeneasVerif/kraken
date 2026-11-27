/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiPilotProof3
import LeanQbe.T.MainLink

/-!
# Shard `F3` `< 64 KiB` Parameterized Slab & Non-Vacuity Proofs (`LcnfC0FfiPilotProof`)

Constructs the `< 64 KiB` parameterized concrete slab `nvPilotSlab (rem : Nat)` at
`nvPilotBase := 0x1000#64` (built via `bytes_append` + `array64_eq_bytesN8` +
`sep_of_bytes_append`, `0` `import all`), proves `nvPilotMem_ok` and `length ≤ 65536`, and derives
concrete `Mem 64` WP non-vacuity (`X := False`, `<= std3`) across all `5` pilot functions:
`checkSatBA` (UNSAT, SAT, OOM), `checkSatNat` (zero-copy `MPZ` UNSAT, `L ≤ 7` tagged scalar, OOM),
`xorBA` (ok, OOM), `xorNat` (tagged ok, `MPZ` ok, OOM), and `solveXorBA` (round-trip UNSAT, OOM).
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.LcnfC0FfiPilot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLRC
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain

public section

/-! ## 1. Parameterized `< 64 KiB` Concrete Slab (`nvPilotSlab`, `0x1000#64`) -/

private theorem replicate_add {α : Type _} (a : α) : ∀ m n : Nat,
    List.replicate m a ++ List.replicate n a = List.replicate (m + n) a
  | 0, n => by simp
  | m + 1, n => by
    rw [List.replicate_succ, List.cons_append, replicate_add a m n, ← List.replicate_succ]
    congr 1; omega

private theorem bytesN8_replicate_zero :
    ∀ k : Nat, bytesN 8 (List.replicate k 0#64) = List.replicate (8 * k) 0
  | 0 => rfl
  | k + 1 => by
    have h0 : Int.toBytes 8 (0#64 : BitVec 64).toNat = List.replicate 8 0 := by decide
    have hstep : bytesN 8 (0#64 :: List.replicate k 0#64) =
        Int.toBytes 8 (0#64 : BitVec 64).toNat ++ bytesN 8 (List.replicate k 0#64) := rfl
    rw [List.replicate_succ, hstep, h0, bytesN8_replicate_zero k, replicate_add,
      show 8 + 8 * k = 8 * (k + 1) by omega]

private theorem sep_of_bytes_append {a : BitVec 64} {xs ys : List UInt8}
    {P Q : Mem 64 → Prop} {m : Mem 64}
    (hfit : xs.length + ys.length ≤ 2 ^ 64)
    (hp : P (xs.At a))
    (hq : Q (ys.At (a + BitVec.ofNat 64 xs.length)))
    (hm : bytes a (xs ++ ys) m) : (P ⋆ Q) m := by
  rw [bytes_append a xs ys hfit] at hm
  exact sep_mono2 (fun _ h => h ▸ hp) (fun _ h => h ▸ hq) _ hm

private theorem array64_zero_of_replicate {a : BitVec 64} {k n : Nat}
    (hn : n = 8 * k) (hk : n ≤ 2 ^ 64) :
    array64 a (List.replicate k 0#64) ((List.replicate n 0).At a) := by
  subst hn
  have hlen : (List.replicate k (0#64 : BitVec 64)).length = k := List.length_replicate
  rw [array64_eq_bytesN8 a _ (by rw [hlen]; exact hk), bytesN8_replicate_zero]
  rfl

private theorem cell64_of_bytesN8_one (a v : BitVec 64) :
    cell64 a v ((bytesN 8 [v]).At a) := by
  have h := array64_eq_bytesN8 a [v] (by simp)
  simp only [array64, sep_emp] at h
  rw [h]
  rfl

private theorem nvFfiHdrWords_len (h : LcnfC0Rt) : (nvFfiHdrWords h).length = 17 := rfl

private theorem lcnfC0Rt_At_of_bytesN8 (p : BitVec 64) (hdr : LcnfC0Rt) :
    LcnfC0Rt.At p hdr ((bytesN 8 (nvFfiHdrWords hdr)).At (p + 33536#64)) := by
  have h := array64_eq_bytesN8 (p + 33536#64) (nvFfiHdrWords hdr)
    (by simp [nvFfiHdrWords])
  have hm : array64 (p + 33536#64) (nvFfiHdrWords hdr)
      ((bytesN 8 (nvFfiHdrWords hdr)).At (p + 33536#64)) := by
    rw [h]; rfl
  simp only [nvFfiHdrWords, array64, sep_emp, cell64_eq_cell, BitVec.add_assoc] at hm
  unfold LcnfC0Rt.At
  exact sep_cast_ac hm (by ac_rfl)

private theorem initSmallPools_emp (n : Nat) :
    smallPoolsAt (List.replicate rtNumClasses 0#64) (fun _ => []) n = emp := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : (List.replicate rtNumClasses 0#64).getD n 0#64 = 0#64 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    have hslot : smallPoolSlot n 0#64 [] = emp := by
      funext m
      unfold smallPoolSlot
      split <;> simp [smallFreeList]
    simp only [smallPoolsAt, ih, heq, hslot, sep_emp]

@[expose] def baObjBytes (o : LcnfObj) : List UInt8 :=
  bytesN 8 [o.header, BitVec.ofNat 64 o.arrSize, BitVec.ofNat 64 o.cap] ++
    o.scalarData ++ List.replicate (o.totalBytes - (24 + o.scalarData.length)) 0

@[expose] def mpzObjBytes (o : LcnfObj) : List UInt8 :=
  bytesN 8 ([o.header, o.mpzMeta] ++ o.limbs)

private theorem lcnfObjMem_baObjBytes {o : LcnfObj} (hcanon : BaCanon o)
    (hfit : o.totalBytes < 2 ^ 64) :
    lcnfObjMem o ((baObjBytes o).At o.addr) := by
  rcases hcanon with ⟨_, _, _, _, hoth, htag, harr, hle, _⟩
  have htb : o.totalBytes = align8 (24 + o.cap) := by
    simp [LcnfObj.totalBytes, htag, hoth, arrayTag, sarrayTag]
  have hpad24 : 24 + o.scalarData.length ≤ o.totalBytes := by
    rw [htb]
    exact Nat.le_trans (by omega) (align8_ge _)
  have hbytes : bytes o.addr (baObjBytes o) ((baObjBytes o).At o.addr) := rfl
  have hlenHdr : (bytesN 8 [o.header, BitVec.ofNat 64 o.arrSize,
      BitVec.ofNat 64 o.cap]).length = 24 := by
    rw [bytesN_length]; simp
  have hlenTail : (o.scalarData ++
      List.replicate (o.totalBytes - (24 + o.scalarData.length)) 0).length =
      o.totalBytes - 24 := by
    simp [List.length_replicate]; omega
  dsimp only [baObjBytes] at hbytes
  rw [List.append_assoc] at hbytes
  have hm := sep_of_bytes_append
    (P := cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
      cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap))
    (Q := bytes (o.addr + 24#64) o.scalarData ⋆
      region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
        (o.totalBytes - (24 + o.scalarData.length)))
    (by rw [hlenHdr, hlenTail]; omega)
    (by
      have ha := array64_eq_bytesN8 o.addr
        [o.header, BitVec.ofNat 64 o.arrSize, BitVec.ofNat 64 o.cap] (by simp)
      have hb : array64 o.addr [o.header, BitVec.ofNat 64 o.arrSize, BitVec.ofNat 64 o.cap]
          ((bytesN 8 [o.header, BitVec.ofNat 64 o.arrSize, BitVec.ofNat 64 o.cap]).At o.addr) := by
        rw [ha]; rfl
      simp only [array64, sep_emp, BitVec.add_assoc] at hb
      exact sep_cast_ac hb (by ac_rfl))
    (by
      rw [hlenHdr, show BitVec.ofNat 64 24 = 24#64 from rfl]
      exact sep_of_bytes_append
        (P := bytes (o.addr + 24#64) o.scalarData)
        (Q := region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
          (o.totalBytes - (24 + o.scalarData.length)))
        (by simp [List.length_replicate]; omega)
        rfl
        (by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          exact ⟨_, List.length_replicate, rfl⟩)
        rfl)
    hbytes
  simp only [lcnfObjMem, htag, show sarrayTag ≠ closureTag by decide,
    show sarrayTag ≠ arrayTag by decide, ↓reduceIte]
  exact sep_cast_ac hm (by ac_rfl)

private theorem lcnfObjMem_mpzObjBytes {o : LcnfObj} (htag : o.tag = mpzTag)
    (hfit : 8 * (2 + o.limbs.length) ≤ 2 ^ 64) :
    lcnfObjMem o ((mpzObjBytes o).At o.addr) := by
  have ha := array64_eq_bytesN8 o.addr (o.header :: o.mpzMeta :: o.limbs)
    (by simp only [List.length_cons]; omega)
  have hm : array64 o.addr (o.header :: o.mpzMeta :: o.limbs) ((mpzObjBytes o).At o.addr) := by
    change array64 o.addr (o.header :: o.mpzMeta :: o.limbs)
      ((bytesN 8 (o.header :: o.mpzMeta :: o.limbs)).At o.addr)
    rw [ha]; rfl
  simp only [array64, BitVec.add_assoc] at hm
  rw [show (8 : BitVec 64) + 8 = 16#64 from rfl, show (8 : BitVec 64) = 8#64 from rfl] at hm
  simp only [lcnfObjMem, htag, show mpzTag ≠ closureTag by decide,
    show mpzTag ≠ arrayTag by decide, show mpzTag ≠ sarrayTag by decide,
    show mpzTag ≠ stringTag by decide, ↓reduceIte]
  exact sep_cast_ac hm (by ac_rfl)

@[expose] def nvPilotBase : BitVec 64 := 0x1000#64
@[expose] def nvPilotWorkCap : Nat := 8
@[expose] def nvPilotRem : Nat := 4096
@[expose] def nvPilotOomRem : Nat := 16
@[expose] def nvPilotScrCap : Nat := 32

@[expose] def nvPilotScr (rem : Nat) : BitVec 64 :=
  nvPilotBase + BitVec.ofNat 64 (33752 + rem)

@[expose] def nvPilotScrLimbs : List (BitVec 64) :=
  List.replicate nvPilotScrCap 0#64

@[expose] def nvPilotHdr (rem : Nat) : LcnfC0Rt :=
  { s_large_free := 0#64
    s_ba_empty := 0#64
    s_cur := nvPilotBase + 33752#64
    s_end := nvPilotBase + BitVec.ofNat 64 (33752 + rem)
    s_work := nvPilotBase + 33688#64
    s_work_cap := BitVec.ofNat 64 nvPilotWorkCap
    s_chunks := 0#64
    s_nchunks := 0#64
    s_chunks_cap := 0#64
    s_st_allocs := 0#64
    s_st_frees := 0#64
    s_st_live := 0#64
    s_st_peak_live := 0#64
    s_st_persistent := 0#64
    s_st_reused := 0#64
    s_st_cold_decs := 0#64
    s_st_bytes := 0#64 }

@[expose] def nvPilotRtSt (rem : Nat) (hrem : rem ≤ 4096) : RtC0State :=
  { extraArgs := List.replicate rtExtraSlots 0#64
    globals := List.replicate rtGlobalSlots 0#64
    freeList := List.replicate rtNumClasses 0#64
    hdr := nvPilotHdr rem
    workBuf := List.replicate nvPilotWorkCap 0#64
    smallPools := fun _ => []
    largeNodes := []
    extraLen := List.length_replicate
    globalsLen := List.length_replicate
    freeListLen := List.length_replicate
    workLen := List.length_replicate
    curLeEnd := by
      dsimp only [nvPilotHdr]
      rw [BitVec.toNat_add, BitVec.toNat_add, show nvPilotBase.toNat = 4096 from rfl,
        show (33752#64 : BitVec 64).toNat = 33752 from rfl, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    arenaAlign := by dsimp only [nvPilotHdr]; decide
    curNz := by dsimp only [nvPilotHdr]; decide }

/-- Pure byte encoding of `"p cnf 1 2\n1 0\n-1 0\n"` (`19` bytes, `8 ≤ L`). -/
@[expose] def nvUnsatDimacs : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Pure byte encoding of `"p cnf 1 1\n1 0\n"` (`14` bytes). -/
@[expose] def nvSatDimacs : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 49, 10, 49, 32, 48, 10]

@[expose] def nvXorKey : UInt8 := 0x5A
@[expose] def nvXorKeyBv : BitVec 8 := 0x5A#8
@[expose] def nvMaskedDimacs : List UInt8 := nvUnsatDimacs.map (· ^^^ nvXorKey)

/-- Pure byte encoding of `"hello"` (`5` bytes, `L ≤ 7` tagged path). -/
@[expose] def nvTaggedBytes : List UInt8 := [104, 101, 108, 108, 111]
@[expose] def nvTaggedNat : Nat := natOfBytesS nvTaggedBytes
@[expose] def nvTaggedArg : BitVec 64 := boxNat nvTaggedNat

@[expose] def u64Of8Bytes (bs : List UInt8) : BitVec 64 :=
  BitVec.ofNat 64 (bytesToNatLE (bs.take 8))

@[expose] def nvUnsatPadded : List UInt8 :=
  nvUnsatDimacs ++ [1] ++ List.replicate 4 0

@[expose] def nvUnsatMpzLimbs : List (BitVec 64) :=
  [ u64Of8Bytes (nvUnsatPadded.drop 0)
  , u64Of8Bytes (nvUnsatPadded.drop 8)
  , u64Of8Bytes (nvUnsatPadded.drop 16) ]

@[expose] def nvUnsatBaAddr (rem : Nat) : BitVec 64 :=
  nvPilotBase + BitVec.ofNat 64 (34008 + rem)

@[expose] def nvSatBaAddr (rem : Nat) : BitVec 64 :=
  nvPilotBase + BitVec.ofNat 64 (34056 + rem)

@[expose] def nvUnsatMpzAddr (rem : Nat) : BitVec 64 :=
  nvPilotBase + BitVec.ofNat 64 (34096 + rem)

@[expose] def nvMaskedBaAddr (rem : Nat) : BitVec 64 :=
  nvPilotBase + BitVec.ofNat 64 (34136 + rem)

@[expose] def nvUnsatBaObj (rem : Nat) : LcnfObj :=
  mkBaObj (nvUnsatBaAddr rem) 1#32 nvUnsatDimacs.length nvUnsatDimacs

@[expose] def nvSatBaObj (rem : Nat) : LcnfObj :=
  mkBaObj (nvSatBaAddr rem) 1#32 nvSatDimacs.length nvSatDimacs

@[expose] def nvUnsatMpzObj (rem : Nat) : LcnfObj :=
  { addr := nvUnsatMpzAddr rem
    rc := 1#32
    csSz := 0
    other := 0
    tag := mpzTag
    cap := 3
    arrSize := 3
    limbs := nvUnsatMpzLimbs }

@[expose] def nvMaskedUnsatBaObj (rem : Nat) : LcnfObj :=
  mkBaObj (nvMaskedBaAddr rem) 1#32 nvMaskedDimacs.length nvMaskedDimacs

@[expose] def nvPilotRtPrefix (rem : Nat) : List UInt8 :=
  List.replicate 256 0 ++ List.replicate 32768 0 ++ List.replicate 512 0 ++
    bytesN 8 (nvFfiHdrWords (nvPilotHdr rem)) ++
    bytesN 8 [nvPilotScr rem, BitVec.ofNat 64 nvPilotScrCap] ++
    List.replicate 64 0 ++ List.replicate rem 0 ++ List.replicate 256 0

@[expose] def nvPilotSlab (rem : Nat) : List UInt8 :=
  nvPilotRtPrefix rem ++
    baObjBytes (nvUnsatBaObj rem) ++
    baObjBytes (nvSatBaObj rem) ++
    mpzObjBytes (nvUnsatMpzObj rem) ++
    baObjBytes (nvMaskedUnsatBaObj rem)

@[expose] def nvPilotMem (rem : Nat) : Mem 64 :=
  (nvPilotSlab rem).At nvPilotBase

private theorem nvUnsatBa_bytesLen (a : BitVec 64) :
    (baObjBytes (mkBaObj a 1#32 nvUnsatDimacs.length nvUnsatDimacs)).length = 48 := by
  dsimp only [baObjBytes, mkBaObj, LcnfObj.totalBytes]
  simp only [List.length_append, List.length_replicate, bytesN_length, List.length_cons,
    List.length_nil, sarrayTag, arrayTag]
  rfl

private theorem nvSatBa_bytesLen (a : BitVec 64) :
    (baObjBytes (mkBaObj a 1#32 nvSatDimacs.length nvSatDimacs)).length = 40 := by
  dsimp only [baObjBytes, mkBaObj, LcnfObj.totalBytes]
  simp only [List.length_append, List.length_replicate, bytesN_length, List.length_cons,
    List.length_nil, sarrayTag, arrayTag]
  rfl

private theorem nvMaskedBa_bytesLen (a : BitVec 64) :
    (baObjBytes (mkBaObj a 1#32 nvMaskedDimacs.length nvMaskedDimacs)).length = 48 := by
  dsimp only [baObjBytes, mkBaObj, LcnfObj.totalBytes]
  simp only [List.length_append, List.length_replicate, bytesN_length, List.length_cons,
    List.length_nil, sarrayTag, arrayTag]
  rfl

theorem nvPilotSlab_len (rem : Nat) : (nvPilotSlab rem).length = 34184 + rem := by
  dsimp only [nvPilotSlab, nvUnsatBaObj, nvSatBaObj, nvMaskedUnsatBaObj]
  simp only [List.length_append, nvUnsatBa_bytesLen, nvSatBa_bytesLen, nvMaskedBa_bytesLen]
  have hrt : (nvPilotRtPrefix rem).length = 34008 + rem := by
    simp only [nvPilotRtPrefix, List.length_append, List.length_replicate, bytesN_length,
      nvFfiHdrWords_len, List.length_cons, List.length_nil]
    omega
  have hmpz : (mpzObjBytes (nvUnsatMpzObj rem)).length = 40 := by
    dsimp only [mpzObjBytes, nvUnsatMpzObj]
    simp only [bytesN_length, List.length_append, List.length_cons, List.length_nil]
    rfl
  rw [hrt, hmpz]
  omega

theorem nvPilotSlab_lt_64k : (nvPilotSlab nvPilotRem).length ≤ 65536 := by
  rw [nvPilotSlab_len]; unfold nvPilotRem; decide

theorem nvPilotOomSlab_lt_64k : (nvPilotSlab nvPilotOomRem).length ≤ 65536 := by
  rw [nvPilotSlab_len]; unfold nvPilotOomRem; decide

private theorem nvPilotAddr_nz_align8 {off rem : Nat} (hoff : off ≤ 60000) (hoff8 : off % 8 = 0)
    (hrem : rem ≤ 4096) (hrem8 : rem % 8 = 0) :
    let a := nvPilotBase + BitVec.ofNat 64 (off + rem)
    a ≠ 0#64 ∧ a.toNat % 8 = 0 := by
  have hto : (nvPilotBase + BitVec.ofNat 64 (off + rem)).toNat = 4096 + (off + rem) := by
    rw [BitVec.toNat_add, show nvPilotBase.toNat = 4096 from rfl, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_⟩
  · intro h
    have h0 := congrArg BitVec.toNat h
    rw [hto, BitVec.toNat_zero] at h0
    omega
  · rw [hto]; omega

private theorem nvBaObj_canon {off rem : Nat} (hoff : off ≤ 60000) (hoff8 : off % 8 = 0)
    (hrem : rem ≤ 4096) (hrem8 : rem % 8 = 0) {xs : List UInt8} (hcap : xs.length ≤ baMaxCap) :
    BaCanon (mkBaObj (nvPilotBase + BitVec.ofNat 64 (off + rem)) 1#32 xs.length xs) := by
  have ha := nvPilotAddr_nz_align8 hoff hoff8 hrem hrem8
  exact mkBaObj_canon ha.1 ha.2 (by decide) (le_refl _) hcap

theorem nvUnsatBaObj_canon {rem : Nat} (hrem : rem ≤ 4096) (hrem8 : rem % 8 = 0) :
    BaCanon (nvUnsatBaObj rem) :=
  nvBaObj_canon (by decide) (by decide) hrem hrem8 (by decide)

theorem nvSatBaObj_canon {rem : Nat} (hrem : rem ≤ 4096) (hrem8 : rem % 8 = 0) :
    BaCanon (nvSatBaObj rem) :=
  nvBaObj_canon (by decide) (by decide) hrem hrem8 (by decide)

theorem nvMaskedUnsatBaObj_canon {rem : Nat} (hrem : rem ≤ 4096) (hrem8 : rem % 8 = 0) :
    BaCanon (nvMaskedUnsatBaObj rem) :=
  nvBaObj_canon (by decide) (by decide) hrem hrem8 (by decide)

private theorem nvUnsatMpz_const_ok :
    0 ≤ (1#32 : BitVec 32).toInt ∧ (0 : Nat) < 65536 ∧ (0 : Nat) < 256 ∧ mpzTag < 256 ∧
      rtMinObjBytes ≤ 40 ∧ (40 : Nat) < rtMaxObjBytes ∧ (40 : Nat) % 8 = 0 ∧
      nvUnsatMpzLimbs.length = 3 ∧ (3 : Nat) ≤ 33554429 ∧ (3 : Nat) < 2 ^ 32 ∧
      mpzTag ≠ closureTag ∧ mpzTag ≠ arrayTag ∧ mpzTag ≠ sarrayTag ∧ mpzTag ≠ stringTag ∧
      8 * (2 + nvUnsatMpzLimbs.length) ≤ 2 ^ 64 ∧ 1 ≤ nvUnsatMpzLimbs.length ∧
      nvUnsatMpzLimbs.length ≤ ffiMpzMaxLimbs ∧ nvUnsatMpzLimbs.getLast! ≠ 0#64 := by
  decide

private theorem nvUnsatBa_tb_lt :
    (mkBaObj 4096#64 1#32 nvUnsatDimacs.length nvUnsatDimacs).totalBytes < 2 ^ 64 := by
  decide

private theorem nvSatBa_tb_lt :
    (mkBaObj 4096#64 1#32 nvSatDimacs.length nvSatDimacs).totalBytes < 2 ^ 64 := by
  decide

private theorem nvMaskedBa_tb_lt :
    (mkBaObj 4096#64 1#32 nvMaskedDimacs.length nvMaskedDimacs).totalBytes < 2 ^ 64 := by
  decide

theorem nvUnsatMpzObj_rtCanon {rem : Nat} (hrem : rem ≤ 4096) (hrem8 : rem % 8 = 0) :
    RtMpzNatCanon (nvUnsatMpzObj rem) (natOfBytesS nvUnsatDimacs) := by
  have hbytesEq : bytesN 8 nvUnsatMpzLimbs = nvUnsatPadded := by decide
  have hval : limbsVal nvUnsatMpzLimbs = natOfBytesS nvUnsatDimacs := by
    rw [← bytesToNatLE_bytesN8, hbytesEq, nvUnsatPadded, List.append_assoc,
      bytesToNatLE_append, bytesToNatLE_append, bytesToNatLE_replicate_zero,
      Nat.mul_zero, Nat.add_zero]
    exact (natOfBytesS_eq_bytesToNatLE_snoc nvUnsatDimacs).symm
  have ha := nvPilotAddr_nz_align8 (off := 34096) (by decide) (by decide) hrem hrem8
  have hc := nvUnsatMpz_const_ok
  have htb : (nvUnsatMpzObj rem).totalBytes = 40 := by
    dsimp only [nvUnsatMpzObj, LcnfObj.totalBytes]
    rw [ite_eq_right hc.2.2.2.2.2.2.2.2.2.2.2.1, ite_eq_right hc.2.2.2.2.2.2.2.2.2.2.2.2.1,
      ite_eq_right hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ite_eq_left rfl]
  have hwf : (nvUnsatMpzObj rem).Wf := by
    refine ⟨ha.1, ha.2, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, ?_, ?_, ?_, ?_⟩
    · rw [htb]; exact hc.2.2.2.2.1
    · rw [htb]; exact hc.2.2.2.2.2.1
    · rw [htb]
    · simp only [nvUnsatMpzObj, ite_true]
      exact ⟨hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1⟩
  have hr : (nvUnsatMpzObj rem).arrSize = (nvUnsatMpzObj rem).limbs.length := by
    dsimp only [nvUnsatMpzObj]; rw [hc.2.2.2.2.2.2.2.1]
  exact ⟨hwf, rfl, rfl, hr, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hval, natOfBytesS_ge_2p63 (by decide)⟩

private theorem nvPilotRtPrefix_ok {rem : Nat} (hrem : rem ≤ 4096) :
    (rtC0Inv nvPilotBase (nvPilotRtSt rem hrem) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr rem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr rem) nvPilotScrLimbs)
      ((nvPilotRtPrefix rem).At nvPilotBase) := by
  let st := nvPilotRtSt rem hrem
  have hsm : smallPoolsAt st.freeList st.smallPools rtNumClasses = emp :=
    initSmallPools_emp rtNumClasses
  have hlg : largeFreeList st.hdr.s_large_free st.largeNodes = emp := by
    funext m'
    simp only [largeFreeList, largeSeg, st, nvPilotRtSt, nvPilotHdr, true_and]
  have hremSt : st.rem = rem := by
    dsimp only [RtC0State.rem, st, nvPilotRtSt, nvPilotHdr]
    rw [BitVec.toNat_add, BitVec.toNat_add, show nvPilotBase.toNat = 4096 from rfl,
      show (33752#64 : BitVec 64).toNat = 33752 from rfl, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hb01 : bytes nvPilotBase (List.replicate 256 0 ++ (List.replicate 32768 0 ++
      (List.replicate 512 0 ++ (bytesN 8 (nvFfiHdrWords (nvPilotHdr rem)) ++
      (bytesN 8 [nvPilotScr rem, BitVec.ofNat 64 nvPilotScrCap] ++
      (List.replicate 64 0 ++ (List.replicate rem 0 ++ List.replicate 256 0)))))))
      ((nvPilotRtPrefix rem).At nvPilotBase) := by
    dsimp only [nvPilotRtPrefix]
    simp only [List.append_assoc]
    rfl
  have h256 := sep_of_bytes_append
    (P := array64 nvPilotBase st.extraArgs)
    (Q := array64 (nvPilotBase + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 (nvPilotBase + 33024#64) st.freeList ⋆
      (LcnfC0Rt.At nvPilotBase st.hdr ⋆
      ((cell64 (nvPilotBase + 33672#64) (nvPilotScr rem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length)) ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (region st.hdr.s_cur st.rem ⋆
      array64 (nvPilotScr rem) nvPilotScrLimbs))))))
    (by simp only [List.length_append, List.length_replicate, bytesN_length,
        nvFfiHdrWords_len, List.length_cons, List.length_nil]; omega)
    (array64_zero_of_replicate (k := 32) (n := 256) rfl (by decide))
    (by
      rw [List.length_replicate, show (256#64 : BitVec 64) = BitVec.ofNat 64 256 from rfl]
      refine sep_of_bytes_append
        (by simp only [List.length_append, List.length_replicate, bytesN_length,
            nvFfiHdrWords_len, List.length_cons, List.length_nil]; omega)
        (by
          have hg := array64_zero_of_replicate (a := nvPilotBase + BitVec.ofNat 64 rtGlobalsOff)
            (k := 4096) (n := 32768) (by decide) (by decide)
          rw [show rtGlobalsOff = 256 from rfl] at hg
          exact hg)
        (by
          rw [List.length_replicate, BitVec.add_assoc]
          have h33024 : (256#64 : BitVec 64) + 32768#64 = 33024#64 := by decide
          rw [h33024]
          refine sep_of_bytes_append
            (by simp only [List.length_append, List.length_replicate, bytesN_length,
                nvFfiHdrWords_len, List.length_cons, List.length_nil]; omega)
            (array64_zero_of_replicate (k := 64) (n := 512) rfl (by decide))
            (by
              rw [List.length_replicate, BitVec.add_assoc]
              have h33536 : (33024#64 : BitVec 64) + 512#64 = 33536#64 := by decide
              rw [h33536]
              refine sep_of_bytes_append
                (by simp only [List.length_append, List.length_replicate, bytesN_length,
                    nvFfiHdrWords_len, List.length_cons, List.length_nil]; omega)
                (lcnfC0Rt_At_of_bytesN8 nvPilotBase (nvPilotHdr rem))
                (by
                  have hhdrL : (bytesN 8 (nvFfiHdrWords (nvPilotHdr rem))).length = 136 := by
                    simp only [bytesN_length, nvFfiHdrWords_len]
                  rw [hhdrL, BitVec.add_assoc]
                  have h33672 : (33536#64 : BitVec 64) + 136#64 = 33672#64 := by decide
                  rw [h33672]
                  refine sep_of_bytes_append
                    (by simp only [List.length_append, List.length_replicate, bytesN_length,
                        List.length_cons, List.length_nil]; omega)
                    (by
                      have ha := array64_eq_bytesN8 (nvPilotBase + 33672#64)
                        [nvPilotScr rem, BitVec.ofNat 64 nvPilotScrCap] (by simp)
                      have hb : array64 (nvPilotBase + 33672#64)
                          [nvPilotScr rem, BitVec.ofNat 64 nvPilotScrCap]
                          ((bytesN 8 [nvPilotScr rem, BitVec.ofNat 64 nvPilotScrCap]).At
                            (nvPilotBase + 33672#64)) := by rw [ha]; rfl
                      simp only [array64, sep_emp, BitVec.add_assoc] at hb
                      have h8 : (33672#64 : BitVec 64) + 8 = 33680#64 := by decide
                      have hscrL : nvPilotScrLimbs.length = nvPilotScrCap := List.length_replicate
                      rw [h8] at hb
                      rw [hscrL]
                      exact hb)
                    (by
                      have hmL : (bytesN 8 [nvPilotScr rem, BitVec.ofNat 64 nvPilotScrCap]).length =
                          16 := by simp only [bytesN_length, List.length_cons, List.length_nil]
                      rw [hmL, BitVec.add_assoc]
                      have h33688 : (33672#64 : BitVec 64) + 16#64 = 33688#64 := by decide
                      rw [h33688]
                      refine sep_of_bytes_append
                        (by simp only [List.length_append, List.length_replicate]; omega)
                        (array64_zero_of_replicate (k := 8) (n := 64) rfl (by decide))
                        (by
                          have hw : st.hdr.s_work +
                              BitVec.ofNat 64 (List.replicate 64 (0 : UInt8)).length =
                              nvPilotBase + 33752#64 := by
                            dsimp only [st, nvPilotRtSt, nvPilotHdr]
                            rw [List.length_replicate, BitVec.add_assoc]
                            decide
                          rw [hw]
                          refine sep_of_bytes_append
                            (by simp only [List.length_replicate]; omega)
                            (by
                              rw [hremSt]
                              exact ⟨List.replicate rem 0, List.length_replicate, rfl⟩)
                            (by
                              rw [List.length_replicate, BitVec.add_assoc, ← BitVec.ofNat_add]
                              exact array64_zero_of_replicate (k := 32) (n := 256) rfl (by decide))
                            rfl)
                        rfl)
                    rfl)
                rfl)
            rfl)
        rfl)
    hb01
  unfold rtC0Inv
  rw [hsm, hlg]
  exact sep_cast_ac h256 (by ac_rfl)

private theorem nvAddr_add (off1 step off2 rem : Nat) (h : off1 + step = off2) :
    nvPilotBase + BitVec.ofNat 64 (off1 + rem) + BitVec.ofNat 64 step =
      nvPilotBase + BitVec.ofNat 64 (off2 + rem) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem nvPilotMem_ok {rem : Nat} (hrem : rem ≤ 4096) (hrem8 : rem % 8 = 0) :
    (rtC0Inv nvPilotBase (nvPilotRtSt rem hrem) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr rem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr rem) nvPilotScrLimbs ⋆
      lcnfObjMem (nvUnsatBaObj rem) ⋆
      lcnfObjMem (nvSatBaObj rem) ⋆
      lcnfObjMem (nvUnsatMpzObj rem) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj rem))
      (nvPilotMem rem) := by
  have h0 : bytes nvPilotBase (nvPilotRtPrefix rem ++ (baObjBytes (nvUnsatBaObj rem) ++
      (baObjBytes (nvSatBaObj rem) ++ (mpzObjBytes (nvUnsatMpzObj rem) ++
      baObjBytes (nvMaskedUnsatBaObj rem))))) (nvPilotMem rem) := by
    change bytes nvPilotBase _ ((nvPilotSlab rem).At nvPilotBase)
    dsimp only [nvPilotSlab]
    simp only [List.append_assoc]
    rfl
  have hrtLen : (nvPilotRtPrefix rem).length = 34008 + rem := by
    simp only [nvPilotRtPrefix, List.length_append, List.length_replicate, bytesN_length,
      nvFfiHdrWords_len, List.length_cons, List.length_nil]
    omega
  have h1Len : (baObjBytes (nvUnsatBaObj rem)).length = 48 := nvUnsatBa_bytesLen _
  have h2Len : (baObjBytes (nvSatBaObj rem)).length = 40 := nvSatBa_bytesLen _
  have h3Len : (mpzObjBytes (nvUnsatMpzObj rem)).length = 40 := by
    dsimp only [mpzObjBytes, nvUnsatMpzObj]
    simp only [bytesN_length, List.length_append, List.length_cons, List.length_nil]
    rfl
  have h4Len : (baObjBytes (nvMaskedUnsatBaObj rem)).length = 48 := nvMaskedBa_bytesLen _
  have htb1 : (nvUnsatBaObj rem).totalBytes < 2 ^ 64 := by
    simpa [nvUnsatBaObj, mkBaObj, LcnfObj.totalBytes] using nvUnsatBa_tb_lt
  have htb2 : (nvSatBaObj rem).totalBytes < 2 ^ 64 := by
    simpa [nvSatBaObj, mkBaObj, LcnfObj.totalBytes] using nvSatBa_tb_lt
  have htb4 : (nvMaskedUnsatBaObj rem).totalBytes < 2 ^ 64 := by
    simpa [nvMaskedUnsatBaObj, mkBaObj, LcnfObj.totalBytes] using nvMaskedBa_tb_lt
  have hfit3 : 8 * (2 + (nvUnsatMpzObj rem).limbs.length) ≤ 2 ^ 64 :=
    nvUnsatMpz_const_ok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm := sep_of_bytes_append
    (P := rtC0Inv nvPilotBase (nvPilotRtSt rem hrem) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr rem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr rem) nvPilotScrLimbs)
    (Q := lcnfObjMem (nvUnsatBaObj rem) ⋆ (lcnfObjMem (nvSatBaObj rem) ⋆
      (lcnfObjMem (nvUnsatMpzObj rem) ⋆ lcnfObjMem (nvMaskedUnsatBaObj rem))))
    (by rw [hrtLen, List.length_append, List.length_append, List.length_append,
        h1Len, h2Len, h3Len, h4Len]; omega)
    (nvPilotRtPrefix_ok hrem)
    (by
      rw [hrtLen]
      refine sep_of_bytes_append
        (by rw [h1Len, List.length_append, List.length_append, h2Len, h3Len, h4Len]; omega)
        (lcnfObjMem_baObjBytes (nvUnsatBaObj_canon hrem hrem8) htb1)
        (by
          rw [h1Len]
          dsimp only [nvUnsatBaObj, mkBaObj, nvUnsatBaAddr]
          rw [nvAddr_add 34008 48 34056 rem rfl]
          refine sep_of_bytes_append
            (by rw [h2Len, List.length_append, h3Len, h4Len]; omega)
            (lcnfObjMem_baObjBytes (nvSatBaObj_canon hrem hrem8) htb2)
            (by
              rw [h2Len]
              dsimp only [nvSatBaObj, mkBaObj, nvSatBaAddr]
              rw [nvAddr_add 34056 40 34096 rem rfl]
              refine sep_of_bytes_append
                (by rw [h3Len, h4Len]; omega)
                (lcnfObjMem_mpzObjBytes (o := nvUnsatMpzObj rem) rfl hfit3)
                (by
                  rw [h3Len]
                  dsimp only [nvUnsatMpzObj, nvUnsatMpzAddr]
                  rw [nvAddr_add 34096 40 34136 rem rfl]
                  exact lcnfObjMem_baObjBytes (nvMaskedUnsatBaObj_canon hrem hrem8) htb4)
                rfl)
            rfl)
        rfl)
    h0
  exact sep_cast_ac hm (by ac_rfl)

/-! ## 2. Concrete `< 64 KiB` Non-Vacuity Theorems (`X := False`, `<= std3`) -/

private theorem nvUnsatTrace_ok :
    UnitUnsatTrace 1 (List.replicate (2 * 1) 0#8) (List.drop 9 nvUnsatDimacs) 2 := by
  refine UnitUnsatTrace.step (l := 0) (rest := List.drop 13 nvUnsatDimacs) (by decide)
    rfl (by decide) ?_
  refine UnitUnsatTrace.conflict (l := 1) (rest := [10]) (k := 0) (by decide)
    rfl (by decide) ⟨CNF.empty, rfl⟩

private theorem nvSatTrace_ok :
    UnitSatTrace 1 (List.replicate (2 * 1) 0#8) 0 (List.drop 9 nvSatDimacs) 1 [1#8, 255#8] 1 := by
  refine UnitSatTrace.step (l := 0) (rest := [10]) (k := 0) (by decide) rfl (by decide) ?_
  exact UnitSatTrace.done (by decide)

theorem nv_pilot_checkSatBA_unsat :
    Func.wp pilotLinkedEnv pilotTfs.tf_0.toFn.body
      (nvPilotBase, nvUnsatBaAddr nvPilotRem, 2048#64, 100#64, ()) (nvPilotMem nvPilotRem)
      (fun (r, ()) _ =>
        r = 20#64 ∧ ∃ cnf, parseDimacs nvUnsatDimacs = some cnf ∧ cnf.Unsat)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvSatBaObj nvPilotRem) ⋆ lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) (nvPilotMem nvPilotRem) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hwp := pilot_checkSatBA_unsat_wp (workReq := 2048#64) (fuel := 100#64)
    (nvUnsatBaObj_canon (rem := nvPilotRem) (by decide) (by decide)) (by decide)
    (by decide) (by decide)
    (by unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf ffiCarveWcap align8
        decide)
    (by decide) (by decide) nvUnsatTrace_ok hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => ⟨h.1, h.2.1⟩) (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_checkSatBA_sat :
    Func.wp pilotLinkedEnv pilotTfs.tf_0.toFn.body
      (nvPilotBase, nvSatBaAddr nvPilotRem, 2048#64, 100#64, ()) (nvPilotMem nvPilotRem)
      (fun (r, ()) _ =>
        r = 10#64 ∧ ∃ cnf, parseDimacs nvSatDimacs = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) (nvPilotMem nvPilotRem) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hwp := pilot_checkSatBA_sat_wp (workReq := 2048#64) (fuel := 100#64)
    (nvSatBaObj_canon (rem := nvPilotRem) (by decide) (by decide)) (by decide)
    (by decide) (by decide)
    (by unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf ffiCarveWcap align8
        decide)
    (by decide) (by decide) nvSatTrace_ok
    (fun v hv => by cases v with | zero => decide | succ _ => omega)
    (by decide) hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => ⟨h.1, h.2.1⟩) (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_checkSatBA_oom :
    Func.wp pilotLinkedEnv pilotTfs.tf_0.toFn.body
      (nvPilotBase, nvUnsatBaAddr nvPilotRem, 8192#64, 100#64, ()) (nvPilotMem nvPilotRem)
      (fun (r, ()) m' => r = 3#64 ∧ m' = nvPilotMem nvPilotRem)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvSatBaObj nvPilotRem) ⋆ lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) (nvPilotMem nvPilotRem) :=
    sep_cast_ac hm0 (by ac_rfl)
  exact pilot_checkSatBA_oom_wp (nvUnsatBaObj_canon (rem := nvPilotRem) (by decide) (by decide))
    (by decide) hm

theorem nv_pilot_checkSatNat_mpz_unsat :
    Func.wp pilotLinkedEnv pilotTfs.tf_1.toFn.body
      (nvPilotBase, nvUnsatMpzAddr nvPilotRem, 2048#64, 100#64, ()) (nvPilotMem nvPilotRem)
      (fun (r, ()) _ =>
        r = 20#64 ∧ ∃ cnf, parseDimacs nvUnsatDimacs = some cnf ∧ cnf.Unsat)
      (fun _ _ _ _ => False) := by
  let hrt := nvPilotRtSt nvPilotRem (by decide)
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase hrt ⋆ cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
      lcnfHeap [nvUnsatMpzObj nvPilotRem] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) (nvPilotMem nvPilotRem) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hge63 : ¬ (natOfBytesS nvUnsatDimacs < 2 ^ 63) :=
    Nat.not_lt_of_ge (natOfBytesS_ge_2p63 (by decide))
  have hrep : RtNatRep (nvUnsatMpzAddr nvPilotRem) (natOfBytesS nvUnsatDimacs)
      [nvUnsatMpzObj nvPilotRem] := by
    simp only [RtNatRep, hge63, ↓reduceIte]
    exact ⟨by decide, nvUnsatMpzObj nvPilotRem, List.mem_cons_self, rfl,
      nvUnsatMpzObj_rtCanon (by decide) (by decide)⟩
  have hwp := pilot_checkSatNat_unsat_wp (workReq := 2048#64) (fuel := 100#64)
    (by decide) hrep (bytesOfNatS_natOfBytesS nvUnsatDimacs)
    (by decide) (fun h => absurd (by decide : (nvUnsatMpzAddr nvPilotRem &&& 1#64) = 0#64) h)
    (fun _ => by decide) (by decide) (by decide)
    (by unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf ffiCarveWcap align8
        decide)
    (by decide) (by decide) nvUnsatTrace_ok hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => ⟨h.1, h.2.1⟩) (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_checkSatNat_tagged :
    Func.wp pilotLinkedEnv pilotTfs.tf_1.toFn.body
      (nvPilotBase, nvTaggedArg, 2048#64, 100#64, ()) (nvPilotMem nvPilotRem)
      (fun (r, ()) _ => r = 0#64)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆ lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem)))
      (nvPilotMem nvPilotRem) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hwp := pilot_checkSatNat_tagged_wp (bs := nvTaggedBytes) (workReq := 2048#64)
    (fuel := 100#64) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => h.1) (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_checkSatNat_oom :
    Func.wp pilotLinkedEnv pilotTfs.tf_1.toFn.body
      (nvPilotBase, nvUnsatMpzAddr nvPilotRem, 8192#64, 100#64, ()) (nvPilotMem nvPilotRem)
      (fun (r, ()) _ => r = 3#64)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [nvUnsatMpzObj nvPilotRem] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) (nvPilotMem nvPilotRem) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hge63 : ¬ (natOfBytesS nvUnsatDimacs < 2 ^ 63) :=
    Nat.not_lt_of_ge (natOfBytesS_ge_2p63 (by decide))
  have hrep : RtNatRep (nvUnsatMpzAddr nvPilotRem) (natOfBytesS nvUnsatDimacs)
      [nvUnsatMpzObj nvPilotRem] := by
    simp only [RtNatRep, hge63, ↓reduceIte]
    exact ⟨by decide, nvUnsatMpzObj nvPilotRem, List.mem_cons_self, rfl,
      nvUnsatMpzObj_rtCanon (by decide) (by decide)⟩
  have hwp := pilot_checkSatNat_oom_wp (workReq := 8192#64) (fuel := 100#64)
    (by decide) hrep (bytesOfNatS_natOfBytesS nvUnsatDimacs)
    (by decide) (fun h => absurd (by decide : (nvUnsatMpzAddr nvPilotRem &&& 1#64) = 0#64) h)
    (fun _ => by decide) (by decide) hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => h.1) (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_xorBA_ok :
    Func.wp pilotLinkedEnv pilotTfs.tf_2.toFn.body
      (nvPilotBase, nvMaskedBaAddr nvPilotRem, nvXorKeyBv, ()) (nvPilotMem nvPilotRem)
      (fun (p, ()) _ => p ≠ 0#64 ∧ p.toNat % 8 = 0)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotRem))) (nvPilotMem nvPilotRem) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hwp := pilot_xorBA_ok_wp (key := nvXorKeyBv)
    (nvMaskedUnsatBaObj_canon (rem := nvPilotRem) (by decide) (by decide)) (by decide)
    (by decide) hm
  exact wp_mono (fun ⟨p, ()⟩ m' ⟨_, _, hp0, hp8, _⟩ => ⟨hp0, hp8⟩)
    (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_xorBA_oom :
    Func.wp pilotLinkedEnv pilotTfs.tf_2.toFn.body
      (nvPilotBase, nvMaskedBaAddr nvPilotOomRem, nvXorKeyBv, ()) (nvPilotMem nvPilotOomRem)
      (fun (r, ()) _ => r = ffiResOomWord)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotOomRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotOomRem (by decide)) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj nvPilotOomRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotOomRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotOomRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotOomRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotOomRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotOomRem))) (nvPilotMem nvPilotOomRem) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hwp := pilot_xorBA_oom_wp (key := nvXorKeyBv)
    (nvMaskedUnsatBaObj_canon (rem := nvPilotOomRem) (by decide) (by decide)) (by decide)
    (by unfold pilotXorBaOk ffiCarveOk ffiCarveWcap ffiCarveWend baAllocBytes align8
        simp [nvMaskedUnsatBaObj, mkBaObj, nvPilotRtSt, nvPilotHdr, nvPilotBase, nvPilotOomRem]
        decide) hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => h.1) (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_xorNat_tagged_ok :
    Func.wp pilotLinkedEnv pilotTfs.tf_3.toFn.body
      (nvPilotBase, nvTaggedArg, nvXorKeyBv, ()) (nvPilotMem nvPilotRem)
      (fun (p, ()) _ => p ≠ 0#64 ∧ p.toNat % 8 = 0)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆ lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem)))
      (nvPilotMem nvPilotRem) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hwp := pilot_xorNat_tagged_ok_wp (bs := nvTaggedBytes) (key := nvXorKeyBv)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hm
  exact wp_mono (fun ⟨p, ()⟩ m' ⟨_, _, hp0, hp8, _⟩ => ⟨hp0, hp8⟩)
    (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_xorNat_mpz_ok :
    Func.wp pilotLinkedEnv pilotTfs.tf_3.toFn.body
      (nvPilotBase, nvUnsatMpzAddr nvPilotRem, nvXorKeyBv, ()) (nvPilotMem nvPilotRem)
      (fun (p, ()) _ => p ≠ 0#64 ∧ p.toNat % 8 = 0)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [nvUnsatMpzObj nvPilotRem] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) (nvPilotMem nvPilotRem) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hge63 : ¬ (natOfBytesS nvUnsatDimacs < 2 ^ 63) :=
    Nat.not_lt_of_ge (natOfBytesS_ge_2p63 (by decide))
  have hrep : RtNatRep (nvUnsatMpzAddr nvPilotRem) (natOfBytesS nvUnsatDimacs)
      [nvUnsatMpzObj nvPilotRem] := by
    simp only [RtNatRep, hge63, ↓reduceIte]
    exact ⟨by decide, nvUnsatMpzObj nvPilotRem, List.mem_cons_self, rfl,
      nvUnsatMpzObj_rtCanon (by decide) (by decide)⟩
  have hwp := pilot_xorNat_mpz_ok_wp (key := nvXorKeyBv) (by decide) hrep (by decide) (by decide)
    (by decide) (by decide) hm
  exact wp_mono (fun ⟨p, ()⟩ m' ⟨_, _, _, _, hp0, hp8, _⟩ => ⟨hp0, hp8⟩)
    (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_xorNat_oom :
    Func.wp pilotLinkedEnv pilotTfs.tf_3.toFn.body
      (nvPilotBase, nvUnsatMpzAddr nvPilotOomRem, nvXorKeyBv, ()) (nvPilotMem nvPilotOomRem)
      (fun (r, ()) _ => r = ffiResOomWord)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotOomRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotOomRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotOomRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotOomRem) nvPilotScrLimbs ⋆
      lcnfHeap [nvUnsatMpzObj nvPilotOomRem] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotOomRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotOomRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotOomRem))) (nvPilotMem nvPilotOomRem) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hge63 : ¬ (natOfBytesS nvUnsatDimacs < 2 ^ 63) :=
    Nat.not_lt_of_ge (natOfBytesS_ge_2p63 (by decide))
  have hrep : RtNatRep (nvUnsatMpzAddr nvPilotOomRem) (natOfBytesS nvUnsatDimacs)
      [nvUnsatMpzObj nvPilotOomRem] := by
    simp only [RtNatRep, hge63, ↓reduceIte]
    exact ⟨by decide, nvUnsatMpzObj nvPilotOomRem, List.mem_cons_self, rfl,
      nvUnsatMpzObj_rtCanon (by decide) (by decide)⟩
  have hwp := pilot_xorNat_oom_wp (key := nvXorKeyBv) (by decide) hrep
    (bytesOfNatS_natOfBytesS nvUnsatDimacs)
    (by decide) (fun h => absurd (by decide : (nvUnsatMpzAddr nvPilotOomRem &&& 1#64) = 0#64) h)
    (fun _ => by decide)
    (by unfold pilotXorNatOk ffiCarveOk ffiCarveWcap ffiCarveWend natSAllocBytes natSLimbCount
          align8
        simp [nvPilotRtSt, nvPilotHdr, nvPilotBase, nvPilotOomRem]
        decide)
    hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => h.1) (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_solveXorBA_unsat :
    Func.wp pilotLinkedEnv pilotTfs.tf_4.toFn.body
      (nvPilotBase, nvMaskedBaAddr nvPilotRem, nvXorKeyBv, 2048#64, 100#64, ())
      (nvPilotMem nvPilotRem)
      (fun (r, ()) _ =>
        (r = 0#64 ∨ r = 3#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs nvUnsatDimacs = some cnf ∧ cnf.Unsat))
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotRem))) (nvPilotMem nvPilotRem) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hinv : List.map (fun x => x ^^^ UInt8.ofBitVec nvXorKeyBv) nvMaskedDimacs =
      nvUnsatDimacs := by decide
  have hwp := pilot_solveXorBA_unsat_wp (key := nvXorKeyBv) (workReq := 2048#64) (fuel := 100#64)
    (nvMaskedUnsatBaObj_canon (rem := nvPilotRem) (by decide) (by decide))
    (by decide) (by decide) (by decide) hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => ⟨h.1, fun hr => by
    have h20 := h.2.1 hr
    simpa [nvMaskedUnsatBaObj, mkBaObj, hinv] using h20⟩) (fun _ _ _ _ h => h) _ _ hwp

theorem nv_pilot_solveXorBA_oom :
    Func.wp pilotLinkedEnv pilotTfs.tf_4.toFn.body
      (nvPilotBase, nvMaskedBaAddr nvPilotOomRem, nvXorKeyBv, 2048#64, 100#64, ())
      (nvPilotMem nvPilotOomRem)
      (fun (r, ()) _ => r = 3#64)
      (fun _ _ _ _ => False) := by
  have hm0 := nvPilotMem_ok (rem := nvPilotOomRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotOomRem (by decide)) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj nvPilotOomRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotOomRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotOomRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotOomRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotOomRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotOomRem))) (nvPilotMem nvPilotOomRem) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hwp := pilot_solveXorBA_oom_wp (key := nvXorKeyBv) (workReq := 2048#64) (fuel := 100#64)
    (nvMaskedUnsatBaObj_canon (rem := nvPilotOomRem) (by decide) (by decide))
    (by decide) (by decide)
    (by unfold pilotXorBaOk ffiCarveOk ffiCarveWcap ffiCarveWend baAllocBytes align8
        simp [nvMaskedUnsatBaObj, mkBaObj, nvPilotRtSt, nvPilotHdr, nvPilotBase, nvPilotOomRem]
        decide)
    hm
  exact wp_mono (fun ⟨r, ()⟩ m' h => h.1) (fun _ _ _ _ h => h) _ _ hwp

end

end LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
