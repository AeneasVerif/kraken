module

public import LeanQbe.T.LeanLCNF.LcnfC0Ffi
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumMath
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Cells

/-!
# Separation-Logic Contracts & Framing Theorems for `LcnfC0Ffi` (Shard F2)

Defines the formal specification layer for all 15 pure-C0 FFI adapter functions in `ffiMod`
(`0` `import all`, `0` `@[expose]` on theorems/lemmas, `XPost`-independent / non-aborting OOM):

1. **Top-down `s_end` scratch carve/reclaim framing (`rtC0Inv_carve_top_split`,
   `rtC0Inv_restore_top_merge`)**:
   - Proves `rtC0Inv rt st` splits cleanly at `wptr = (s_end & ~7) - align8 reqBytes` into a
     reduced-`s_end` `rtC0Inv ⋆ region wptr wcap ⋆ region wend tailPad`, and merges back after
     arbitrary interior allocations to restore `PreservesMeta` with 100% reclaim.
2. **Canonical `FfiRes.ok`, `RtMpzNatCanon`, `RtNatRep`, and `MPZ`/tagged `↔ bytes` framing**:
   - `array64_eq_bytesN8`, `bytes_eq_array64_of_len_mul8`, `mpzNatCanon_natOfBytesS_split`
     (zero-copy `L ≥ 8` read), and `taggedNat_natOfBytesS_cell64_split` (`L ≤ 7` staging in
     `rt->scratch[0]`).
3. **Closed specification table (`ffiSpecEntries`, `ffiEnv`)**:
   - Contracts for all 15 `lcnf_ffi_*` functions (`noExit := true`, non-aborting OOM/invalidInput)
     plus the 2 `rtC0CoreMod` externs (`lcnf_alloc`, `r2_mem_copy_bytes`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

/-! ## 1. Top-Down `s_end` Carve & Reclaim Model + Separation-Logic Framing -/

/-- Metadata preserved across a temporary top-down `s_end` scratch carve (every field of
`PreservesMeta` except `s_end`). -/
@[expose] def RtC0State.PreservesMetaExceptEnd (st st' : RtC0State) : Prop :=
  st'.extraArgs = st.extraArgs ∧
  st'.globals = st.globals ∧
  st'.hdr.s_ba_empty = st.hdr.s_ba_empty ∧
  st'.hdr.s_work = st.hdr.s_work ∧
  st'.hdr.s_work_cap = st.hdr.s_work_cap ∧
  st'.hdr.s_chunks = st.hdr.s_chunks ∧
  st'.hdr.s_nchunks = st.hdr.s_nchunks ∧
  st'.hdr.s_chunks_cap = st.hdr.s_chunks_cap

theorem RtC0State.PreservesMeta.toExceptEnd {st st' : RtC0State}
    (h : st'.PreservesMeta st) : st'.PreservesMetaExceptEnd st :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem RtC0State.PreservesMetaExceptEnd.refl (st : RtC0State) :
    st.PreservesMetaExceptEnd st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RtC0State.PreservesMetaExceptEnd.trans {st1 st2 st3 : RtC0State}
    (h12 : st2.PreservesMetaExceptEnd st1) (h23 : st3.PreservesMetaExceptEnd st2) :
    st3.PreservesMetaExceptEnd st1 := by
  rcases h12 with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  rcases h23 with ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5,
    a6.trans b6, a7.trans b7, a8.trans b8⟩

theorem RtC0State.preservesMeta_of_exceptEnd {st st' : RtC0State}
    (h : st'.PreservesMetaExceptEnd st) (hend : st'.hdr.s_end = st.hdr.s_end) :
    st'.PreservesMeta st :=
  ⟨h.1, h.2.1, h.2.2.1, hend.symm, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- Update only `s_end` on an `RtC0State`, preserving every other field. -/
@[expose] def RtC0State.withEnd (st : RtC0State) (newEnd : BitVec 64)
    (hle : st.hdr.s_cur.toNat ≤ newEnd.toNat) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := { st.hdr with s_end := newEnd }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := hle
  arenaAlign := st.arenaAlign
  curNz := st.curNz

theorem RtC0State.withEnd_preservesMetaExceptEnd (st : RtC0State) (newEnd : BitVec 64)
    (hle : st.hdr.s_cur.toNat ≤ newEnd.toNat) :
    (st.withEnd newEnd hle).PreservesMetaExceptEnd st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 8-byte aligned ceiling `s_end & ~7`. -/
@[expose] def ffiCarveWend (sEnd : BitVec 64) : BitVec 64 :=
  sEnd &&& 0xfffffffffffffff8#64

/-- 8-byte aligned scratch capacity for `reqBytes`. -/
@[expose] def ffiCarveWcap (reqBytes : BitVec 64) : Nat :=
  align8 reqBytes.toNat

/-- Headroom predicate for `lcnf_ffi_carve_scratch(rt, reqBytes)`. -/
@[expose] def ffiCarveOk (st : RtC0State) (reqBytes : BitVec 64) : Prop :=
  reqBytes ≠ 0#64 ∧
  reqBytes.toNat ≤ 2 ^ 64 - 8 ∧
  st.hdr.s_cur.toNat ≤ (ffiCarveWend st.hdr.s_end).toNat ∧
  ffiCarveWcap reqBytes ≤ (ffiCarveWend st.hdr.s_end).toNat - st.hdr.s_cur.toNat

instance instDecidableFfiCarveOk (st : RtC0State) (reqBytes : BitVec 64) :
    Decidable (ffiCarveOk st reqBytes) := by
  unfold ffiCarveOk
  infer_instance

/-- Carved top-down workspace base pointer `wend - wcap`. -/
@[expose] def ffiCarveWptr (st : RtC0State) (reqBytes : BitVec 64) : BitVec 64 :=
  ffiCarveWend st.hdr.s_end - BitVec.ofNat 64 (ffiCarveWcap reqBytes)

theorem bv64_and_not7_toNat (x : BitVec 64) :
    (x &&& 0xfffffffffffffff8#64).toNat = (x.toNat / 8) * 8 := by
  have hbits : x &&& 0xfffffffffffffff8#64 = (x >>> 3) <<< 3 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    have hm : (0xfffffffffffffff8#64 : BitVec 64).getLsbD i = decide (3 ≤ i) := by
      revert i; decide
    rw [hm]
    by_cases h3 : i < 3
    · have hnot : ¬ (3 ≤ i) := by omega
      simp [h3, hnot]
    · have h3le : 3 ≤ i := by omega
      simp [h3le, hi, h3]
  rw [hbits, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, show (2 ^ 3 : Nat) = 8 from rfl]
  have hx := x.isLt
  have hlt : x.toNat / 8 * 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]

theorem ffiCarveWend_props (sEnd : BitVec 64) :
    (ffiCarveWend sEnd).toNat ≤ sEnd.toNat ∧
    (ffiCarveWend sEnd).toNat % 8 = 0 ∧
    sEnd.toNat - (ffiCarveWend sEnd).toNat < 8 := by
  unfold ffiCarveWend
  rw [bv64_and_not7_toNat]
  omega

theorem ffiCarveWcap_bv_eq {reqBytes : BitVec 64} (hhi : reqBytes.toNat ≤ 2 ^ 64 - 8) :
    ((reqBytes + 7#64) &&& 0xfffffffffffffff8#64) = BitVec.ofNat 64 (ffiCarveWcap reqBytes) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_and_not7_toNat, BitVec.toNat_add, show (7#64 : BitVec 64).toNat = 7 from rfl,
    Nat.mod_eq_of_lt (by omega : reqBytes.toNat + 7 < 2 ^ 64)]
  unfold ffiCarveWcap align8
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ffiCarveWptr_props {st : RtC0State} {reqBytes : BitVec 64}
    (hok : ffiCarveOk st reqBytes) :
    let wend := ffiCarveWend st.hdr.s_end
    let wcap := ffiCarveWcap reqBytes
    let wptr := ffiCarveWptr st reqBytes
    8 ≤ wcap ∧ wcap % 8 = 0 ∧ wcap < 2 ^ 64 ∧
    wptr.toNat = wend.toNat - wcap ∧
    st.hdr.s_cur.toNat ≤ wptr.toNat ∧
    wptr ≠ 0#64 ∧ wptr.toNat % 8 = 0 ∧
    st.hdr.s_cur + BitVec.ofNat 64 (wptr.toNat - st.hdr.s_cur.toNat) = wptr ∧
    wptr + BitVec.ofNat 64 wcap = wend := by
  rcases hok with ⟨hnz, hhi, hcurLe, hwcapLe⟩
  have hreqPos : 0 < reqBytes.toNat := Nat.pos_of_ne_zero fun h0 =>
    hnz (BitVec.eq_of_toNat_eq h0)
  have hwcapLo : 8 ≤ ffiCarveWcap reqBytes := by unfold ffiCarveWcap align8; omega
  have hwcapMod : ffiCarveWcap reqBytes % 8 = 0 := by unfold ffiCarveWcap align8; omega
  have hwcapLt : ffiCarveWcap reqBytes < 2 ^ 64 := by unfold ffiCarveWcap align8; omega
  have hwendProps := ffiCarveWend_props st.hdr.s_end
  have hwcapLeWend : ffiCarveWcap reqBytes ≤ (ffiCarveWend st.hdr.s_end).toNat := by omega
  have hbvLe : BitVec.ofNat 64 (ffiCarveWcap reqBytes) ≤ ffiCarveWend st.hdr.s_end := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt]
    exact hwcapLeWend
  have hwptrNat : (ffiCarveWptr st reqBytes).toNat =
      (ffiCarveWend st.hdr.s_end).toNat - ffiCarveWcap reqBytes := by
    unfold ffiCarveWptr
    rw [BitVec.toNat_sub_of_le hbvLe, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwcapLt]
  have hcurLeWptr : st.hdr.s_cur.toNat ≤ (ffiCarveWptr st reqBytes).toNat := by omega
  have hcurPos : 0 < st.hdr.s_cur.toNat := Nat.pos_of_ne_zero fun h0 =>
    st.curNz (BitVec.eq_of_toNat_eq h0)
  have hwptrNz : ffiCarveWptr st reqBytes ≠ 0#64 := fun h0 => by
    have := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
    omega
  have hwptrMod : (ffiCarveWptr st reqBytes).toNat % 8 = 0 := by
    rw [hwptrNat]; omega
  have hadd1 : st.hdr.s_cur +
      BitVec.ofNat 64 ((ffiCarveWptr st reqBytes).toNat - st.hdr.s_cur.toNat) =
      ffiCarveWptr st reqBytes := by
    apply BitVec.eq_of_toNat_eq
    have hwlt := (ffiCarveWptr st reqBytes).isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hadd2 : ffiCarveWptr st reqBytes + BitVec.ofNat 64 (ffiCarveWcap reqBytes) =
      ffiCarveWend st.hdr.s_end := by
    unfold ffiCarveWptr
    bv_omega
  exact ⟨hwcapLo, hwcapMod, hwcapLt, hwptrNat, hcurLeWptr, hwptrNz, hwptrMod, hadd1, hadd2⟩

/-- Separation-logic framing theorem (split): carving `[wptr, wend)` from the top of `rtC0Inv`'s
bump arena splits `region st.hdr.s_cur st.rem` cleanly into the reduced bump arena
`region stCarved.hdr.s_cur stCarved.rem`, the disjoint carved workspace `region wptr wcap`,
and the trailing `< 8`-byte alignment pad `region wend tailPad`. -/
theorem rtC0Inv_carve_top_split {st : RtC0State} {reqBytes : BitVec 64}
    (hok : ffiCarveOk st reqBytes) :
    let wend := ffiCarveWend st.hdr.s_end
    let wcap := ffiCarveWcap reqBytes
    let wptr := ffiCarveWptr st reqBytes
    let hle : st.hdr.s_cur.toNat ≤ wptr.toNat := (ffiCarveWptr_props hok).2.2.2.2.1
    let stCarved := st.withEnd wptr hle
    let tailPad := st.hdr.s_end.toNat - wend.toNat
    region st.hdr.s_cur st.rem =
      (region stCarved.hdr.s_cur stCarved.rem ⋆
        region wptr wcap ⋆
        region wend tailPad) ∧
    stCarved.rem + wcap + tailPad = st.rem ∧
    stCarved.PreservesMetaExceptEnd st := by
  have hp := ffiCarveWptr_props hok
  have hwp := ffiCarveWend_props st.hdr.s_end
  rcases hp with ⟨_, _, _, hwptrNat, hcurLeWptr, _, _, hadd1, hadd2⟩
  have hwendLe := hwp.1
  have hendLt := st.hdr.s_end.isLt
  have hcurLeWend := hok.2.2.1
  have hwcapLeDiff := hok.2.2.2
  have hremEq : st.rem =
      (st.withEnd (ffiCarveWptr st reqBytes) hcurLeWptr).rem +
        (ffiCarveWcap reqBytes + (st.hdr.s_end.toNat - (ffiCarveWend st.hdr.s_end).toNat)) := by
    simp only [RtC0State.rem, RtC0State.withEnd]
    omega
  have hsplit1 : region st.hdr.s_cur st.rem =
      (region st.hdr.s_cur (st.withEnd (ffiCarveWptr st reqBytes) hcurLeWptr).rem ⋆
        region (ffiCarveWptr st reqBytes)
          (ffiCarveWcap reqBytes + (st.hdr.s_end.toNat - (ffiCarveWend st.hdr.s_end).toNat))) := by
    conv => lhs; rw [hremEq]
    rw [region_split (by simp only [RtC0State.rem, RtC0State.withEnd]; omega)]
    simp only [RtC0State.rem, RtC0State.withEnd]
    rw [hadd1]
  have hsplit2 :
      region (ffiCarveWptr st reqBytes)
        (ffiCarveWcap reqBytes + (st.hdr.s_end.toNat - (ffiCarveWend st.hdr.s_end).toNat)) =
      (region (ffiCarveWptr st reqBytes) (ffiCarveWcap reqBytes) ⋆
        region (ffiCarveWend st.hdr.s_end)
          (st.hdr.s_end.toNat - (ffiCarveWend st.hdr.s_end).toNat)) := by
    rw [region_split (by omega), hadd2]
  refine ⟨?_, ?_, st.withEnd_preservesMetaExceptEnd _ hcurLeWptr⟩
  · rw [hsplit1, hsplit2, ← sep_assoc]
    rfl
  · simp only [RtC0State.rem, RtC0State.withEnd]; omega

/-- Separation-logic framing theorem (reclaim): after arbitrary allocations inside `[cur, wptr)`
producing `stMid` with `stMid.hdr.s_end = wptr`, restoring `s_end := savedEnd` merges the carved
workspace `region wptr wcap` and alignment pad `region wend tailPad` back into `stMid`'s bump
arena with 100% reclaim and restores `PreservesMeta st`! -/
theorem rtC0Inv_restore_top_merge {st stMid : RtC0State}
    {wptr wend savedEnd : BitVec 64} {wcap tailPad : Nat}
    (hMidEnd : stMid.hdr.s_end = wptr)
    (hadd1 : wptr + BitVec.ofNat 64 wcap = wend)
    (hnat1 : wptr.toNat + wcap = wend.toNat)
    (hnat2 : wend.toNat + tailPad = savedEnd.toNat) :
    let hle : stMid.hdr.s_cur.toNat ≤ savedEnd.toNat := by
      have := stMid.curLeEnd; rw [hMidEnd] at this; omega
    let stRestored := stMid.withEnd savedEnd hle
    (region stMid.hdr.s_cur stMid.rem ⋆ region wptr wcap ⋆ region wend tailPad) =
      region stRestored.hdr.s_cur stRestored.rem ∧
    stRestored.rem = stMid.rem + wcap + tailPad ∧
    (stMid.PreservesMetaExceptEnd st → savedEnd = st.hdr.s_end →
      stRestored.PreservesMeta st) := by
  have hcurLeWptr : stMid.hdr.s_cur.toNat ≤ wptr.toNat := hMidEnd ▸ stMid.curLeEnd
  have hcurLeSaved : stMid.hdr.s_cur.toNat ≤ savedEnd.toNat := by omega
  have hsavedLt := savedEnd.isLt
  have hptr1 : stMid.hdr.s_cur + BitVec.ofNat 64 stMid.rem = wptr := by
    apply BitVec.eq_of_toNat_eq
    have hwlt := wptr.isLt
    simp only [RtC0State.rem, hMidEnd]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (region wptr wcap ⋆ region wend tailPad) = region wptr (wcap + tailPad) := by
    rw [← hadd1]
    exact region_merge_eq rfl (by omega)
  have hm2 : (region stMid.hdr.s_cur stMid.rem ⋆ region wptr (wcap + tailPad)) =
      region stMid.hdr.s_cur (stMid.rem + (wcap + tailPad)) := by
    rw [← hptr1]
    exact region_merge_eq rfl (by simp only [RtC0State.rem, hMidEnd]; omega)
  have hremEq : (stMid.withEnd savedEnd hcurLeSaved).rem = stMid.rem + wcap + tailPad := by
    simp only [RtC0State.rem, RtC0State.withEnd, hMidEnd]; omega
  refine ⟨?_, hremEq, fun hmeta hsaved => ?_⟩
  · rw [sep_assoc, hm1, hm2]
    congr 1
    rw [hremEq, Nat.add_assoc]
  · exact RtC0State.preservesMeta_of_exceptEnd
      (hmeta.trans (stMid.withEnd_preservesMetaExceptEnd savedEnd hcurLeSaved))
      hsaved

/-! ## 2. Canonical `FfiRes.ok`, `RtMpzNatCanon`, `RtNatRep`, and Byte/Limb Bridges -/

/-- Construct a canonical `FfiRes.ok(val)` heap object (`16` B, ctor 0, 1 object field). -/
@[expose] def mkFfiResOkObj (addr val : BitVec 64) : LcnfObj :=
  { addr := addr
    rc := 1#32
    csSz := 16
    other := 1
    tag := 0
    fields := [val] }

/-- Canonical invariant for a freshly allocated `FfiRes.ok(val)` constructor cell. -/
@[expose] def FfiResOkCanon (o : LcnfObj) (val : BitVec 64) : Prop :=
  o.addr ≠ 0#64 ∧ o.addr.toNat % 8 = 0 ∧ o.rc = 1#32 ∧
  o.csSz = 16 ∧ o.other = 1 ∧ o.tag = 0 ∧ o.fields = [val] ∧ o.scalarData = []

theorem FfiResOkCanon.wf {o : LcnfObj} {val : BitVec 64} (h : FfiResOkCanon o val) : o.Wf := by
  rcases h with ⟨h0, h8, hrc, hcs, ho, ht, hf, hs⟩
  have htb : o.totalBytes = 16 := by
    simp [LcnfObj.totalBytes, ht, hcs, arrayTag, sarrayTag, stringTag, mpzTag]
  refine ⟨h0, h8, by simp [hrc], by omega, by omega, by omega,
    by rw [htb]; decide, by rw [htb]; decide, by rw [htb], ?_⟩
  simp [ht, closureTag, arrayTag, sarrayTag, stringTag, mpzTag, hf, ho, hs, hcs]

theorem mkFfiResOkObj_canon {p val : BitVec 64} (hp0 : p ≠ 0#64) (hp8 : p.toNat % 8 = 0) :
    FfiResOkCanon (mkFfiResOkObj p val) val :=
  ⟨hp0, hp8, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mkFfiResOkObj_header (p val : BitVec 64) :
    (mkFfiResOkObj p val).header = ffiResOkHeader := by
  apply BitVec.eq_of_getLsbD_eq
  simp only [LcnfObj.header, mkFfiResOkObj, ffiResOkHeader,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  decide

theorem lcnfObjMem_mkFfiResOkObj (p val : BitVec 64) :
    lcnfObjMem (mkFfiResOkObj p val) =
      (cell64 p ffiResOkHeader ⋆ cell64 (p + 8#64) val) := by
  unfold lcnfObjMem
  simp only [mkFfiResOkObj, closureTag, arrayTag, sarrayTag, stringTag, mpzTag,
    show (0 : Nat) ≠ 245 by decide, show (0 : Nat) ≠ 246 by decide,
    show (0 : Nat) ≠ 248 by decide, show (0 : Nat) ≠ 249 by decide,
    show (0 : Nat) ≠ 250 by decide, ↓reduceIte,
    List.length_singleton, List.length_nil, Nat.mul_one, Nat.add_zero, Nat.sub_self,
    array64_cons, array64_nil, bytes_nil_eq, region_zero, sep_emp]
  rw [← mkFfiResOkObj_header p val]
  rfl

/-- Canonical boxed `MPZ` `Nat` invariant over R0's unified `LcnfObj` (`tag 250`, `other = 0`,
trimmed limbs, `val ≥ 2^63`). -/
@[expose] def RtMpzNatCanon (obj : LcnfObj) (n : Nat) : Prop :=
  obj.Wf ∧
  obj.tag = mpzTag ∧
  obj.other = 0 ∧
  obj.arrSize = obj.limbs.length ∧
  1 ≤ obj.limbs.length ∧
  obj.limbs.length ≤ ffiMpzMaxLimbs ∧
  obj.limbs.getLast! ≠ 0#64 ∧
  limbsVal obj.limbs = n ∧
  2 ^ 63 ≤ n

/-- Unified R0 representation predicate for Lean runtime `Nat` values (`(2*n+1)` scalar or boxed
`MPZ`). -/
@[expose] def RtNatRep (w : BitVec 64) (n : Nat) (objs : List LcnfObj) : Prop :=
  if n < 2 ^ 63 then w = BitVec.ofNat 64 (2 * n + 1)
  else (w &&& 1#64) = 0#64 ∧ ∃ obj ∈ objs, obj.addr = w ∧ RtMpzNatCanon obj n

/-- Construct a fresh `MPZ` `LcnfObj` (`rc = 1, csSz = 0, other = 0, tag = 250`) satisfying BOTH
`RtMpzNatCanon` (R1 BigNum) and `MpzCanon` (R2b Strings). -/
@[expose] def mkMpzNatObj (addr : BitVec 64) (limbs : List (BitVec 64)) : LcnfObj :=
  { addr := addr
    rc := 1#32
    csSz := 0
    other := 0
    tag := mpzTag
    cap := limbs.length
    arrSize := limbs.length
    limbs := limbs }

/-- Limb count required for a boxed sentineled `Nat` (`len / 8 + 1`). -/
@[expose] def natSLimbCount (len : Nat) : Nat :=
  len / 8 + 1

/-- Heap bytes allocated by `lcnf_ffi_nat_of_bytes` (`0` for `len ≤ 7`, `16 + 8*(len/8 + 1)` for
`len ≥ 8`). -/
@[expose] def natSAllocBytes (len : Nat) : Nat :=
  if len ≤ 7 then 0 else 16 + 8 * natSLimbCount len

theorem mkMpzNatObj_header (p : BitVec 64) (limbs : List (BitVec 64)) :
    (mkMpzNatObj p limbs).header = mpzHeaderWord := by
  apply BitVec.eq_of_getLsbD_eq
  simp only [LcnfObj.header, mkMpzNatObj, mpzTag, mpzHeaderWord,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  decide

theorem lcnfObjMem_mkMpzNatObj (p : BitVec 64) (limbs : List (BitVec 64)) :
    lcnfObjMem (mkMpzNatObj p limbs) =
      (cell64 p mpzHeaderWord ⋆
        cell64 (p + 8#64) (BitVec.ofNat 64 limbs.length ||| (BitVec.ofNat 64 limbs.length <<< 32)) ⋆
        array64 (p + 16#64) limbs) := by
  unfold lcnfObjMem
  simp only [mkMpzNatObj, LcnfObj.mpzMeta, mpzTag, closureTag, arrayTag, sarrayTag, stringTag,
    show (250 : Nat) ≠ 245 by decide, show (250 : Nat) ≠ 246 by decide,
    show (250 : Nat) ≠ 248 by decide, show (250 : Nat) ≠ 249 by decide, ↓reduceIte]
  rw [← mkMpzNatObj_header p limbs]
  rfl

/-! ### Byte ↔ 64-bit Limb Algebra & Separation-Logic Bridges -/

theorem intToBytes_nat_eq_natToBytesLE : ∀ (k n : Nat),
    Int.toBytes k (n : Int) = natToBytesLE k n
  | 0, _ => rfl
  | k + 1, n => by
    simp only [Int.toBytes, natToBytesLE]
    have hdiv : (n : Int) / 256 = ((n / 256 : Nat) : Int) := by omega
    rw [hdiv, intToBytes_nat_eq_natToBytesLE k (n / 256)]
    rfl

theorem bytesToNatLE_intToBytes8 (v : BitVec 64) :
    bytesToNatLE (Int.toBytes 8 (v.toNat : Int)) = v.toNat := by
  rw [intToBytes_nat_eq_natToBytesLE, bytesToNatLE_natToBytesLE,
    show 2 ^ (8 * 8) = 2 ^ 64 from rfl, Nat.mod_eq_of_lt v.isLt]

theorem bytesToNatLE_bytesN8 (xs : List (BitVec 64)) :
    bytesToNatLE (bytesN 8 xs) = limbsVal xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hcons : bytesN 8 (x :: xs) = Int.toBytes 8 (x.toNat : Int) ++ bytesN 8 xs := rfl
    rw [hcons, bytesToNatLE_append, Int.toBytes_length, bytesToNatLE_intToBytes8,
      limbsVal_cons, show 2 ^ (8 * 8) = 2 ^ 64 from rfl, ih]

theorem array64_eq_bytesN8 (a : BitVec 64) (xs : List (BitVec 64))
    (h : 8 * xs.length ≤ 2 ^ 64) :
    array64 a xs = bytes a (bytesN 8 xs) := by
  rw [array64_eq_word8Array, word8Array_eq a xs h]
  rfl

/-- Pack a byte list of length `8 * k` into `k` little-endian 64-bit limbs. -/
@[expose] def bytesToLimbs64 : Nat → List UInt8 → List (BitVec 64)
  | 0, _ => []
  | k + 1, bs => BitVec.ofNat 64 (bytesToNatLE (bs.take 8)) :: bytesToLimbs64 k (bs.drop 8)

theorem bytesToLimbs64_length (k : Nat) (bs : List UInt8) :
    (bytesToLimbs64 k bs).length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [bytesToLimbs64, ih]

theorem bytesN8_bytesToLimbs64 : ∀ (k : Nat) (bs : List UInt8),
    bs.length = 8 * k → bytesN 8 (bytesToLimbs64 k bs) = bs
  | 0, bs, hlen => by
    cases bs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | k + 1, bs, hlen => by
    have h8 : 8 ≤ bs.length := by omega
    have htakeLen : (bs.take 8).length = 8 := List.length_take_of_le h8
    have hlt64 : bytesToNatLE (bs.take 8) < 2 ^ 64 := by
      have h := bytesToNatLE_lt (bs.take 8)
      rwa [htakeLen] at h
    have hnat : natToBytesLE 8 (bytesToNatLE (bs.take 8)) = bs.take 8 := by
      have h := natToBytesLE_bytesToNatLE (bs.take 8)
      rwa [htakeLen] at h
    have hhead : Int.toBytes 8 (BitVec.ofNat 64 (bytesToNatLE (bs.take 8))).toNat = bs.take 8 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, intToBytes_nat_eq_natToBytesLE, hnat]
    have hdropLen : (bs.drop 8).length = 8 * k := by simp; omega
    have hcons : bytesN 8 (bytesToLimbs64 (k + 1) bs) =
        Int.toBytes 8 (BitVec.ofNat 64 (bytesToNatLE (bs.take 8))).toNat ++
        bytesN 8 (bytesToLimbs64 k (bs.drop 8)) := rfl
    rw [hcons, hhead, bytesN8_bytesToLimbs64 k (bs.drop 8) hdropLen, List.take_append_drop]

/-- Convert any `8 * k`-byte `bytes a bs` slice directly into `array64 a limbs` with exact value
preservation (`limbsVal limbs = bytesToNatLE bs`). -/
theorem bytes_eq_array64_of_len_mul8 {a : BitVec 64} {bs : List UInt8} {k : Nat}
    (hlen : bs.length = 8 * k) (hfit : 8 * k ≤ 2 ^ 64) :
    let limbs := bytesToLimbs64 k bs
    limbs.length = k ∧
    bytesN 8 limbs = bs ∧
    limbsVal limbs = bytesToNatLE bs ∧
    bytes a bs = array64 a limbs := by
  have hlenL := bytesToLimbs64_length k bs
  have hbn := bytesN8_bytesToLimbs64 k bs hlen
  have hval : limbsVal (bytesToLimbs64 k bs) = bytesToNatLE bs := by
    rw [← bytesToNatLE_bytesN8, hbn]
  have harr : bytes a bs = array64 a (bytesToLimbs64 k bs) := by
    rw [array64_eq_bytesN8 a _ (by rw [hlenL]; exact hfit), hbn]
  exact ⟨hlenL, hbn, hval, harr⟩

/-- For any canonical `MPZ` encoding `natOfBytesS bs`, `8 ≤ bs.length`, `limbs.length = bs.length /
8 + 1`, and its raw byte representation is `bs ++ [1] ++ pad0` verbatim. -/
theorem mpzNatCanon_natOfBytesS_bytesN8 {obj : LcnfObj} {bs : List UInt8}
    (h : RtMpzNatCanon obj (natOfBytesS bs)) :
    8 ≤ bs.length ∧
    obj.limbs.length = natSLimbCount bs.length ∧
    bytesN 8 obj.limbs =
      bs ++ [1] ++ List.replicate (8 * obj.limbs.length - bs.length - 1) 0 := by
  rcases h with ⟨_, _, _, _, h1, _, hlast, hval, hge63⟩
  have hge8 : 8 ≤ bs.length := by
    exact Nat.le_of_not_lt fun hlt =>
      Nat.not_lt_of_ge hge63 (natOfBytesS_lt_2p63 (by omega))
  have hne : obj.limbs ≠ [] := fun he => by simp [he] at h1
  have hlog : (limbsVal obj.limbs).log2 = 8 * bs.length := by
    rw [hval, natOfBytesS_log2]
  have hlb : 2 ^ (64 * (obj.limbs.length - 1)) ≤ limbsVal obj.limbs := by
    rw [list_getLast!_eq_getLast _ hne] at hlast
    exact limbsVal_ge_pow_of_nonzero_last hne hlast
  have hub : limbsVal obj.limbs < 2 ^ (64 * obj.limbs.length) := limbsVal_lt_pow obj.limbs
  have hpos : limbsVal obj.limbs ≠ 0 := by rw [hval]; exact Nat.ne_of_gt (natOfBytesS_pos bs)
  have hloLog : 64 * (obj.limbs.length - 1) ≤ (limbsVal obj.limbs).log2 :=
    (Nat.le_log2 hpos).mpr hlb
  have hhiLog : (limbsVal obj.limbs).log2 < 64 * obj.limbs.length :=
    (Nat.log2_lt hpos).mpr hub
  have hlimbsLen : obj.limbs.length = natSLimbCount bs.length := by
    unfold natSLimbCount; omega
  have hpadLen : (bs ++ [1] ++ List.replicate (8 * obj.limbs.length - bs.length - 1) 0).length =
      (bytesN 8 obj.limbs).length := by
    rw [bytesN_length]
    simp [hlimbsLen, natSLimbCount]
    omega
  have hpadVal :
      bytesToNatLE (bs ++ [1] ++ List.replicate (8 * obj.limbs.length - bs.length - 1) 0) =
      bytesToNatLE (bytesN 8 obj.limbs) := by
    rw [bytesToNatLE_append, bytesToNatLE_replicate_zero, Nat.mul_zero, Nat.add_zero,
      ← natOfBytesS_eq_bytesToNatLE_snoc, bytesToNatLE_bytesN8, hval]
  exact ⟨hge8, hlimbsLen, bytesToNatLE_inj hpadLen.symm hpadVal.symm⟩

/-- Zero-copy separation-logic split for boxed sentineled `Nat` (`L ≥ 8`):
`array64 (obj.addr + 16#64) obj.limbs` splits directly into `bytes (obj.addr + 16#64) bs`
framed against the trailing sentinel + zero-padding bytes! -/
theorem mpzNatCanon_natOfBytesS_split {obj : LcnfObj} {bs : List UInt8}
    (h : RtMpzNatCanon obj (natOfBytesS bs)) :
    array64 (obj.addr + 16#64) obj.limbs =
      (bytes (obj.addr + 16#64) bs ⋆
        bytes (obj.addr + 16#64 + BitVec.ofNat 64 bs.length)
          ([1] ++ List.replicate (8 * obj.limbs.length - bs.length - 1) 0)) := by
  have hfit : 8 * obj.limbs.length ≤ 2 ^ 64 := by
    have hmax := h.2.2.2.2.2.1
    unfold ffiMpzMaxLimbs at hmax; omega
  have hbn := (mpzNatCanon_natOfBytesS_bytesN8 h).2.2
  rw [array64_eq_bytesN8 _ _ hfit, hbn, List.append_assoc]
  have hlen :
      bs.length +
        ([1] ++ List.replicate (8 * obj.limbs.length - bs.length - 1) (0 : UInt8)).length =
      8 * obj.limbs.length := by
    have hl := congrArg List.length hbn
    rw [bytesN_length, List.length_append, List.length_append] at hl
    rw [List.length_append]
    omega
  exact bytes_append (obj.addr + 16#64) bs _ (by rw [hlen]; exact hfit)

/-- Staged `rt->scratch[0]` separation-logic split for small sentineled `Nat` (`L ≤ 7`):
`cell64 scr (BitVec.ofNat 64 (natOfBytesS bs))` splits directly into `bytes scr bs` framed
against `[1] ++ 0^(7 - L)`! -/
theorem taggedNat_natOfBytesS_cell64_split (scr : BitVec 64) {bs : List UInt8}
    (hle : bs.length ≤ 7) :
    cell64 scr (BitVec.ofNat 64 (natOfBytesS bs)) =
      (bytes scr bs ⋆
        bytes (scr + BitVec.ofNat 64 bs.length) ([1] ++ List.replicate (7 - bs.length) 0)) := by
  have hlt64 : natOfBytesS bs < 2 ^ 64 :=
    Nat.lt_trans (natOfBytesS_lt_2p63 hle) (by decide)
  have h1 : cell64 scr (BitVec.ofNat 64 (natOfBytesS bs)) =
      bytes scr (Int.toBytes 8 ((BitVec.ofNat 64 (natOfBytesS bs)).toNat : Int)) := by
    rw [cell64_eq_word8]
    rfl
  have hbytesEq : Int.toBytes 8 ((BitVec.ofNat 64 (natOfBytesS bs)).toNat : Int) =
      bs ++ ([1] ++ List.replicate (7 - bs.length) 0) := by
    apply bytesToNatLE_inj
    · rw [Int.toBytes_length]; simp; omega
    · rw [bytesToNatLE_intToBytes8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
        ← List.append_assoc, bytesToNatLE_append, bytesToNatLE_replicate_zero,
        Nat.mul_zero, Nat.add_zero, ← natOfBytesS_eq_bytesToNatLE_snoc]
  rw [h1, hbytesEq]
  exact bytes_append scr bs _ (by simp; omega)

/-- Characterization of `sentinelByteIdx` on the top limb of a canonical `MPZ`. -/
theorem sentinelByteIdx_mpz_spec {obj : LcnfObj} {n : Nat}
    (h : RtMpzNatCanon obj n) :
    let top := obj.limbs.getLast!
    let k := sentinelByteIdx top
    (k < 8 ↔ ∃ bs : List UInt8, bytesOfNatS n = some bs) ∧
    (∀ bs : List UInt8, bytesOfNatS n = some bs →
      k < 8 ∧ 8 * (obj.limbs.length - 1) + k = bs.length) := by
  rcases h with ⟨_, _, _, _, h1, _, hlast, hval, hge63⟩
  have hne : obj.limbs ≠ [] := fun he => by simp [he] at h1
  have hlast' : obj.limbs.getLast hne ≠ 0#64 := by rwa [← list_getLast!_eq_getLast _ hne]
  have hlogEq := limbsVal_log2 hne hlast'
  rw [hval] at hlogEq
  have hclz : (obj.limbs.getLast hne).clz.toNat =
      64 - ((obj.limbs.getLast hne).toNat.log2 + 1) := by
    rw [BitVec.toNat_clz]
    simp [hlast']
  have htopNz : (obj.limbs.getLast hne).toNat ≠ 0 := fun h0 =>
    hlast' (BitVec.eq_of_toNat_eq h0)
  have htopLogLt : (obj.limbs.getLast hne).toNat.log2 < 64 :=
    (Nat.log2_lt htopNz).mpr (obj.limbs.getLast hne).isLt
  have hnLog : n.log2 = 64 * (obj.limbs.length - 1) + (obj.limbs.getLast hne).toNat.log2 := by
    rw [hlogEq, hclz]; omega
  have htopEq : obj.limbs.getLast! = obj.limbs.getLast hne := list_getLast!_eq_getLast _ hne
  have hposN : 0 < n := by omega
  have hmodIff : (obj.limbs.getLast hne).toNat.log2 % 8 = 0 ↔ n.log2 % 8 = 0 := by
    rw [hnLog]; omega
  constructor
  · constructor
    · intro hk
      dsimp only [sentinelByteIdx] at hk
      rw [htopEq, ite_eq_right hlast'] at hk
      split at hk
      · rename_i hmodTop
        have hmodN : n.log2 % 8 = 0 := hmodIff.mp hmodTop
        exact ⟨natToBytesLE (n.log2 / 8) n, by simp [bytesOfNatS, hposN, hmodN]⟩
      · omega
    · rintro ⟨bs, hbs⟩
      unfold bytesOfNatS at hbs
      split at hbs
      · rename_i hc
        have hmodTop : (obj.limbs.getLast hne).toNat.log2 % 8 = 0 := hmodIff.mpr hc.2
        dsimp only [sentinelByteIdx]
        rw [htopEq, ite_eq_right hlast', ite_eq_left hmodTop]
        omega
      · nomatch hbs
  · intro bs hbs
    unfold bytesOfNatS at hbs
    split at hbs
    · rename_i hc
      have hmodTop : (obj.limbs.getLast hne).toNat.log2 % 8 = 0 := hmodIff.mpr hc.2
      have hbsEq := Option.some.inj hbs
      have hbsLen : bs.length = n.log2 / 8 := by rw [← hbsEq, natToBytesLE_length]
      dsimp only [sentinelByteIdx]
      rw [htopEq, ite_eq_right hlast', ite_eq_left hmodTop]
      exact ⟨by omega, by rw [hbsLen, hnLog]; omega⟩
    · nomatch hbs

/-! ## 3. Function `Spec` Contracts (`noExit := true`, Non-Aborting OOM) -/

/-- `lcnf_ffi_get_end(rt) -> s_end`: reads the current arena high-water mark `r->s.end`. -/
@[expose] def ffiGetEndSpec : Spec [i64] [i64] := fun (rt, ()) m Q _ =>
  ∃ (st : RtC0State) (R : Mem 64 → Prop),
    (rtC0Inv rt st ⋆ R) m ∧ Q (st.hdr.s_end, ()) m

/-- `lcnf_ffi_carve_scratch(rt, reqBytes) -> wptr`:
Top-down carve from `s_end`. Returns `0#64` with state unchanged on OOM/invalid request
(`XPost := False`, never panics); on success returns 8B-aligned `wptr ≠ 0#64` and splits
`rtC0Inv` into reduced-`s_end` `rtC0Inv rt stCarved ⋆ region wptr wcap ⋆ region wend tailPad`. -/
@[expose] def ffiCarveScratchSpec : Spec [i64, i64] [i64] := fun (rt, reqBytes, ()) m Q _ =>
  ∃ (st : RtC0State) (R : Mem 64 → Prop),
    (rtC0Inv rt st ⋆ R) m ∧
    if hok : ffiCarveOk st reqBytes then
      let wend := ffiCarveWend st.hdr.s_end
      let wcap := ffiCarveWcap reqBytes
      let wptr := ffiCarveWptr st reqBytes
      let hle : st.hdr.s_cur.toNat ≤ wptr.toNat := (ffiCarveWptr_props hok).2.2.2.2.1
      let stCarved := st.withEnd wptr hle
      let tailPad := st.hdr.s_end.toNat - wend.toNat
      ∀ m',
        wptr ≠ 0#64 → wptr.toNat % 8 = 0 →
        reqBytes.toNat ≤ wcap →
        stCarved.PreservesMetaExceptEnd st →
        stCarved.hdr.s_end = wptr →
        (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆ region wend tailPad ⋆ R) m' →
        Q (wptr, ()) m'
    else
      Q (0#64, ()) m

/-- `lcnf_ffi_restore_scratch(rt, savedEnd) -> ()`:
Restores `r->s.end = savedEnd` and merges the carved scratch `[wptr, wend)` and alignment pad
`[wend, savedEnd)` back into `stMid`'s bump arena with 100% reclaim. -/
@[expose] def ffiRestoreScratchSpec : Spec [i64, i64] [] := fun (rt, savedEnd, ()) m Q _ =>
  ∃ (stMid : RtC0State) (wptr wend : BitVec 64) (wcap tailPad : Nat) (R : Mem 64 → Prop),
    stMid.hdr.s_end = wptr ∧
    wptr + BitVec.ofNat 64 wcap = wend ∧
    wptr.toNat + wcap = wend.toNat ∧
    wend.toNat + tailPad = savedEnd.toNat ∧
    (rtC0Inv rt stMid ⋆ region wptr wcap ⋆ region wend tailPad ⋆ R) m ∧
    ∀ stRestored m',
      stRestored.PreservesMetaExceptEnd stMid →
      stRestored.hdr.s_end = savedEnd →
      stRestored.rem = stMid.rem + wcap + tailPad →
      (rtC0Inv rt stRestored ⋆ R) m' →
      Q () m'

/-- `lcnf_ffi_ba_ptr(ba) -> ba + 24`: zero-copy payload pointer for any `ByteArray`. -/
@[expose] def ffiBaPtrSpec : Spec [i64] [i64] := fun (ba, ()) m Q _ =>
  Q (ba + 24#64, ()) m

/-- `lcnf_ffi_ba_len(ba) -> len`: reads exact byte length of a canonical `ByteArray`. -/
@[expose] def ffiBaLenSpec : Spec [i64] [i64] := fun (ba, ()) m Q _ =>
  ∃ (baObj : LcnfObj) (R : Mem 64 → Prop),
    baObj.addr = ba ∧ BaCanon baObj ∧ (lcnfObjMem baObj ⋆ R) m ∧
    Q (BitVec.ofNat 64 baObj.scalarData.length, ()) m

/-- `lcnf_ffi_mk_ok(rt, val) -> res`: allocates `FfiRes.ok(val)` (`16` B) when `16 ≤ st.rem`,
or returns `5#64 = FfiRes.oom` with memory unchanged (non-aborting OOM). -/
@[expose] def ffiMkOkSpec : Spec [i64, i64] [i64] := fun (rt, val, ()) m Q _ =>
  ∃ (st : RtC0State) (R : Mem 64 → Prop),
    (rtC0Inv rt st ⋆ R) m ∧
    if 16 ≤ st.rem then
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem → st.rem - 16 ≤ st'.rem →
        FfiResOkCanon (mkFfiResOkObj p val) val →
        (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p val) ⋆ R) m' →
        Q (p, ()) m'
    else
      Q (ffiResOomWord, ()) m

/-- `lcnf_ffi_ba_of_bytes(rt, srcPtr, len) -> p`: allocates canonical `ByteArray` copying `len`
bytes from `srcPtr`, or returns `0#64` on OOM / `len > baMaxCap` (non-aborting). -/
@[expose] def ffiBaOfBytesSpec : Spec [i64, i64, i64] [i64] := fun (rt, srcPtr, len, ()) m Q _ =>
  ∃ (st : RtC0State) (srcData : List UInt8) (R : Mem 64 → Prop),
    srcData.length = len.toNat ∧
    (rtC0Inv rt st ⋆ bytes srcPtr srcData ⋆ R) m ∧
    if len.toNat ≤ ffiBaMaxCap ∧ baAllocBytes len.toNat ≤ st.rem then
      ∀ p st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        st.rem - baAllocBytes len.toNat ≤ st'.rem →
        let baObj := mkBaObj p 1#32 len.toNat srcData
        BaCanon baObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ bytes srcPtr srcData ⋆ R) m' →
        Q (p, ()) m'
    else
      Q (0#64, ()) m

/-- `lcnf_ffi_ba_wrap_ok(rt, srcPtr, len) -> res`: allocates `FfiRes.ok(ba)` copying `len` bytes
from `srcPtr`, or returns `5#64 = FfiRes.oom` with `0` allocations on OOM (non-aborting). -/
@[expose] def ffiBaWrapOkSpec : Spec [i64, i64, i64] [i64] := fun (rt, srcPtr, len, ()) m Q _ =>
  ∃ (st : RtC0State) (srcData : List UInt8) (R : Mem 64 → Prop),
    srcData.length = len.toNat ∧
    (rtC0Inv rt st ⋆ bytes srcPtr srcData ⋆ R) m ∧
    if len.toNat ≤ ffiBaMaxCap ∧ baAllocBytes len.toNat + 16 ≤ st.rem then
      ∀ p ba st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 → ba ≠ 0#64 → ba.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        st.rem - (baAllocBytes len.toNat + 16) ≤ st'.rem →
        let baObj := mkBaObj ba 1#32 len.toNat srcData
        let okObj := mkFfiResOkObj p ba
        BaCanon baObj → FfiResOkCanon okObj ba →
        (rtC0Inv rt st' ⋆ lcnfObjMem okObj ⋆ lcnfObjMem baObj ⋆ bytes srcPtr srcData ⋆ R) m' →
        Q (p, ()) m'
    else
      Q (ffiResOomWord, ()) m

/-- `lcnf_ffi_sentinel_byte_idx(w) -> k`: pure word scan returning `sentinelByteIdx w`. -/
@[expose] def ffiSentinelByteIdxSpec : Spec [i64] [i64] := fun (w, ()) m Q _ =>
  Q (BitVec.ofNat 64 (sentinelByteIdx w), ()) m

/-- `lcnf_ffi_nat_bytes_len(a) -> len`: validates sentineled `Nat` (tagged or boxed MPZ),
returning exact byte length `bs.length` if `bytesOfNatS val = some bs`, else `ffiInvalidLen`. -/
@[expose] def ffiNatBytesLenSpec : Spec [i64] [i64] := fun (a, ()) m Q _ =>
  ∃ (val : Nat) (objs : List LcnfObj) (R : Mem 64 → Prop),
    RtNatRep a val objs ∧ (lcnfHeap objs ⋆ R) m ∧
    match bytesOfNatS val with
    | some bs => Q (BitVec.ofNat 64 bs.length, ()) m
    | none => Q (ffiInvalidLen, ()) m

/-- `lcnf_ffi_nat_bytes_ptr(rt, a) -> ptr`:
- For `L ≤ 7` (tagged scalar): stages `a >> 1` into `rt->scratch[0]` (returning `0#64` if
  `scr = 0 ∨ scrLimbs = []`) and returns `scr`.
- For `L ≥ 8` (boxed `MPZ`): zero-copy returns `a + 16#64` without touching memory. -/
@[expose] def ffiNatBytesPtrSpec : Spec [i64, i64] [i64] := fun (rt, a, ()) m Q _ =>
  if (a &&& 1#64) ≠ 0#64 then
    ∃ (scr : BitVec 64) (scrLimbs : List (BitVec 64)) (R : Mem 64 → Prop),
      scrLimbs.length < 2 ^ 64 ∧
      (cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr scrLimbs ⋆ R) m ∧
      if scr = 0#64 ∨ scrLimbs.length = 0 then
        Q (0#64, ()) m
      else
        ∀ m',
          (cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 scr (scrLimbs.set 0 (a >>> 1)) ⋆ R) m' →
          Q (scr, ()) m'
  else
    Q (a + 16#64, ()) m

/-- `lcnf_ffi_nat_of_bytes(rt, srcPtr, len) -> w`:
Constructs canonical sentineled `Nat` representing `natOfBytesS srcData`:
- `len ≤ 7`: zero heap allocation, returns tagged `boxNat (natOfBytesS srcData)`.
- `8 ≤ len ≤ ffiNatMaxBytes` and `natSAllocBytes len ≤ st.rem`: allocates canonical `MPZ`
  (`RtMpzNatCanon` & `MpzCanon` automatically via sentinel `0x01` byte!).
- Otherwise: returns `0#64` with memory unchanged (non-aborting OOM). -/
@[expose] def ffiNatOfBytesSpec : Spec [i64, i64, i64] [i64] := fun (rt, srcPtr, len, ()) m Q _ =>
  ∃ (st : RtC0State) (srcData : List UInt8) (R : Mem 64 → Prop),
    srcData.length = len.toNat ∧
    (rtC0Inv rt st ⋆ bytes srcPtr srcData ⋆ R) m ∧
    if len.toNat ≤ 7 then
      Q (boxNat (natOfBytesS srcData), ()) m
    else if len.toNat ≤ ffiNatMaxBytes ∧ natSAllocBytes len.toNat ≤ st.rem then
      ∀ p st' newObj m',
        p ≠ 0#64 → p.toNat % 8 = 0 → (p &&& 1#64) = 0#64 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        st.rem - natSAllocBytes len.toNat ≤ st'.rem →
        newObj.addr = p →
        RtMpzNatCanon newObj (natOfBytesS srcData) →
        MpzCanon newObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem newObj ⋆ bytes srcPtr srcData ⋆ R) m' →
        Q (p, ()) m'
    else
      Q (0#64, ()) m

/-- `lcnf_ffi_nat_wrap_ok(rt, srcPtr, len) -> res`:
Wraps `lcnf_ffi_nat_of_bytes` into `FfiRes Nat` with combined headroom pre-check:
returns `FfiRes.ok(val)` on success, or `5#64 = FfiRes.oom` with `0` allocations on OOM. -/
@[expose] def ffiNatWrapOkSpec : Spec [i64, i64, i64] [i64] := fun (rt, srcPtr, len, ()) m Q _ =>
  ∃ (st : RtC0State) (srcData : List UInt8) (R : Mem 64 → Prop),
    srcData.length = len.toNat ∧
    (rtC0Inv rt st ⋆ bytes srcPtr srcData ⋆ R) m ∧
    if len.toNat ≤ 7 then
      if 16 ≤ st.rem then
        let v := boxNat (natOfBytesS srcData)
        ∀ p st' m',
          p ≠ 0#64 → p.toNat % 8 = 0 →
          st'.PreservesMeta st → st'.rem ≤ st.rem → st.rem - 16 ≤ st'.rem →
          FfiResOkCanon (mkFfiResOkObj p v) v →
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p v) ⋆ bytes srcPtr srcData ⋆ R) m' →
          Q (p, ()) m'
      else
        Q (ffiResOomWord, ()) m
    else if len.toNat ≤ ffiNatMaxBytes ∧ natSAllocBytes len.toNat + 16 ≤ st.rem then
      ∀ p natP st' newObj m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        natP ≠ 0#64 → natP.toNat % 8 = 0 → (natP &&& 1#64) = 0#64 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        st.rem - (natSAllocBytes len.toNat + 16) ≤ st'.rem →
        newObj.addr = natP →
        RtMpzNatCanon newObj (natOfBytesS srcData) →
        MpzCanon newObj →
        FfiResOkCanon (mkFfiResOkObj p natP) natP →
        (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p natP) ⋆ lcnfObjMem newObj ⋆
          bytes srcPtr srcData ⋆ R) m' →
        Q (p, ()) m'
    else
      Q (ffiResOomWord, ()) m

/-- `lcnf_ffi_ba_to_nat_s(rt, ba) -> res`: `O(N)` conversion from borrowed `ByteArray` to
`FfiRes Nat` encoding `natOfBytesS baObj.scalarData`. -/
@[expose] def ffiBaToNatSSpec : Spec [i64, i64] [i64] := fun (rt, ba, ()) m Q _ =>
  ∃ (st : RtC0State) (baObj : LcnfObj) (R : Mem 64 → Prop),
    baObj.addr = ba ∧ BaCanon baObj ∧
    (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m ∧
    let bs := baObj.scalarData
    if bs.length ≤ 7 then
      if 16 ≤ st.rem then
        let v := boxNat (natOfBytesS bs)
        ∀ p st' m',
          p ≠ 0#64 → p.toNat % 8 = 0 →
          st'.PreservesMeta st → st'.rem ≤ st.rem → st.rem - 16 ≤ st'.rem →
          FfiResOkCanon (mkFfiResOkObj p v) v →
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p v) ⋆ lcnfObjMem baObj ⋆ R) m' →
          Q (p, ()) m'
      else
        Q (ffiResOomWord, ()) m
    else if natSAllocBytes bs.length + 16 ≤ st.rem then
      ∀ p natP st' newObj m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        natP ≠ 0#64 → natP.toNat % 8 = 0 → (natP &&& 1#64) = 0#64 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        st.rem - (natSAllocBytes bs.length + 16) ≤ st'.rem →
        newObj.addr = natP →
        RtMpzNatCanon newObj (natOfBytesS bs) →
        MpzCanon newObj →
        FfiResOkCanon (mkFfiResOkObj p natP) natP →
        (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p natP) ⋆ lcnfObjMem newObj ⋆
          lcnfObjMem baObj ⋆ R) m' →
        Q (p, ()) m'
    else
      Q (ffiResOomWord, ()) m

/-- `lcnf_ffi_nat_s_to_ba(rt, a) -> res`: `O(N)` conversion from borrowed sentineled `Nat` to
`FfiRes ByteArray`:
- invalid sentinel -> `3#64 = FfiRes.invalidInput` (0 alloc)
- tagged (`L ≤ 7`) with missing scratch -> `5#64 = FfiRes.oom` (0 alloc)
- valid & sufficient headroom -> `FfiRes.ok(ba)` with `ba.scalarData = bs`
- valid & OOM -> `5#64 = FfiRes.oom` (0 alloc) -/
@[expose] def ffiNatSToBaSpec : Spec [i64, i64] [i64] := fun (rt, a, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
      (val : Nat) (objs : List LcnfObj) (R : Mem 64 → Prop),
    scrLimbs.length < 2 ^ 64 ∧
    RtNatRep a val objs ∧
    (rtC0Inv rt st ⋆
      cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆
      lcnfHeap objs ⋆ R) m ∧
    match bytesOfNatS val with
    | none => Q (ffiResInvalidInputWord, ()) m
    | some bs =>
      if bs.length ≤ 7 ∧ (scr = 0#64 ∨ scrLimbs.length = 0) then
        Q (ffiResOomWord, ()) m
      else
        let scrLimbs' :=
          if bs.length ≤ 7 then scrLimbs.set 0 (BitVec.ofNat 64 (natOfBytesS bs))
          else scrLimbs
        if bs.length ≤ ffiBaMaxCap ∧ baAllocBytes bs.length + 16 ≤ st.rem then
          ∀ p ba st' m',
            p ≠ 0#64 → p.toNat % 8 = 0 → ba ≠ 0#64 → ba.toNat % 8 = 0 →
            st'.PreservesMeta st → st'.rem ≤ st.rem →
            st.rem - (baAllocBytes bs.length + 16) ≤ st'.rem →
            let baObj := mkBaObj ba 1#32 bs.length bs
            let okObj := mkFfiResOkObj p ba
            BaCanon baObj → FfiResOkCanon okObj ba →
            (rtC0Inv rt st' ⋆
              cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              array64 scr scrLimbs' ⋆
              lcnfObjMem okObj ⋆ lcnfObjMem baObj ⋆ lcnfHeap objs ⋆ R) m' →
            Q (p, ()) m'
        else
          ∀ m',
            (rtC0Inv rt st ⋆
              cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              array64 scr scrLimbs' ⋆
              lcnfHeap objs ⋆ R) m' →
            Q (ffiResOomWord, ()) m'

/-! ## 4. Closed Specification Table (`ffiSpecEntries`, `ffiEnv`) -/

/-- Specification table for `ffiMod` (15 defined FFI adapters + 2 `rtC0CoreMod` externs). -/
@[expose] def ffiSpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn lcnf_ffi_get_end ffiGetEndSpec true
  , SpecEntry.ofFn lcnf_ffi_carve_scratch ffiCarveScratchSpec true
  , SpecEntry.ofFn lcnf_ffi_restore_scratch ffiRestoreScratchSpec true
  , SpecEntry.ofFn lcnf_ffi_ba_ptr ffiBaPtrSpec true
  , SpecEntry.ofFn lcnf_ffi_ba_len ffiBaLenSpec true
  , SpecEntry.ofFn lcnf_ffi_mk_ok ffiMkOkSpec true
  , SpecEntry.ofFn lcnf_ffi_ba_of_bytes ffiBaOfBytesSpec true
  , SpecEntry.ofFn lcnf_ffi_ba_wrap_ok ffiBaWrapOkSpec true
  , SpecEntry.ofFn lcnf_ffi_sentinel_byte_idx ffiSentinelByteIdxSpec true
  , SpecEntry.ofFn lcnf_ffi_nat_bytes_len ffiNatBytesLenSpec true
  , SpecEntry.ofFn lcnf_ffi_nat_bytes_ptr ffiNatBytesPtrSpec true
  , SpecEntry.ofFn lcnf_ffi_nat_of_bytes ffiNatOfBytesSpec true
  , SpecEntry.ofFn lcnf_ffi_nat_wrap_ok ffiNatWrapOkSpec true
  , SpecEntry.ofFn lcnf_ffi_ba_to_nat_s ffiBaToNatSSpec true
  , SpecEntry.ofFn lcnf_ffi_nat_s_to_ba ffiNatSToBaSpec true
  , ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocRemSpec, false⟩
  , ⟨"r2_mem_copy_bytes", [i64, i64, i64], [], r2MemCopyBytesSpec, false⟩ ]

/-- Specification environment for verifying `ffiMod`. -/
@[expose] def ffiEnv : Env := Env.ofTable ffiSpecEntries

theorem ffiSpecEntries_nodup : (ffiSpecEntries.map SpecEntry.name).Nodup := by
  decide

theorem ffiEnv_lcnf_alloc {xs m Q X} :
    lcnfAllocRemSpec xs m Q X → ffiEnv "lcnf_alloc" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocRemSpec, false⟩)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_r2_mem_copy_bytes {xs m Q X} :
    r2MemCopyBytesSpec xs m Q X → ffiEnv "r2_mem_copy_bytes" [i64, i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem
    (e := ⟨"r2_mem_copy_bytes", [i64, i64, i64], [], r2MemCopyBytesSpec, false⟩)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_ba_len {xs m Q X} :
    ffiBaLenSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_ba_len" [i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_ba_len ffiBaLenSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_mk_ok {xs m Q X} :
    ffiMkOkSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_mk_ok" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_mk_ok ffiMkOkSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_ba_of_bytes {xs m Q X} :
    ffiBaOfBytesSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_ba_of_bytes" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_ba_of_bytes ffiBaOfBytesSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_ba_wrap_ok {xs m Q X} :
    ffiBaWrapOkSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_ba_wrap_ok" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_ba_wrap_ok ffiBaWrapOkSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_sentinel_byte_idx {xs m Q X} :
    ffiSentinelByteIdxSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_sentinel_byte_idx" [i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_sentinel_byte_idx ffiSentinelByteIdxSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_nat_bytes_len {xs m Q X} :
    ffiNatBytesLenSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_nat_bytes_len" [i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_nat_bytes_len ffiNatBytesLenSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_nat_bytes_ptr {xs m Q X} :
    ffiNatBytesPtrSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_nat_bytes_ptr" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_nat_bytes_ptr ffiNatBytesPtrSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_nat_of_bytes {xs m Q X} :
    ffiNatOfBytesSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_nat_of_bytes" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_nat_of_bytes ffiNatOfBytesSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

theorem ffiEnv_nat_wrap_ok {xs m Q X} :
    ffiNatWrapOkSpec xs m Q (fun _ _ _ _ => False) →
    ffiEnv "lcnf_ffi_nat_wrap_ok" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_ffi_nat_wrap_ok ffiNatWrapOkSpec true)
    (by simp [ffiSpecEntries]) ffiSpecEntries_nodup

end LeanQbe.T.LeanLCNF
