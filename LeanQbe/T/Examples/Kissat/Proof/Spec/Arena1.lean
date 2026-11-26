/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Logic.C0Step
public import Kraken.Mem
public import Kraken.Separation
meta import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
meta import Lean.Elab.Command

/-!
# Kissat `D-Full` Generic Indexed Arena Accessors & Scoped Bridge (`FullArenaTactics`, `Stage 4`)

Replaces `419` hand-written `@[scoped c0_load]` / `@[scoped c0_store]` accessors with:
1. Generic indexed `fullHdr_load` / `fullHdr_store` / `fullHdr_store_nat` (`HdrWordField`, `144`
   words) and `fullArr_load` / `fullArr_load_bv` / `fullArr_store` / `fullArr_store_bv` /
   `fullArr_load0` / `fullArr_store0` (`ArrayField`, `41` arrays), plus offset-lookup bridges
   `fullHdr_load_ofOff` / `fullHdr_store_ofOff`.
2. A single `CommandElabM` bridge emitting all `withReducible`-safe `@[scoped c0_load]` /
   `@[scoped c0_store]` rules inside `FullArenaTactics` as 1-term calls to the generic accessors
   (zero `ecancel`, `O(1)` `AddrKey` dispatch).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open LeanQbe.T LeanQbe.T.ProofUtil Kraken.Bedrock2.Test

theorem ufM {c : FullCfg} {s s' : FullState} {G G' B B' R : Mem 64 → Prop}
    {m' : Mem 64} (_hs : FullMem c s = (G ⋆ B)) (hs' : FullMem c s' = (G' ⋆ B'))
    (hb : B' = B) (h : ((G' ⋆ B) ⋆ R) m') : (FullMem c s' ⋆ R) m' := by
  rw [hs', hb]; exact h

theorem m8 (a i : BitVec 64) : a + i * 8 = a + BitVec.ofNat 64 (8 * i.toNat) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]

private theorem m4 (a i : BitVec 64) : a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]

/-! ## 1. Generic Indexed Header & Array Accessors -/

section GenericAccessors
variable {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}

/-- Generic `FullHdr` 64-bit word load indexed by `HdrWordField` (`0..143`). -/
theorem fullHdr_load (f : HdrWordField) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (f.addr c) = some (f.get c s) := by
  by_cases ht : 4 ≤ f.wordIdx
  · have hnz : f.wordIdx ≠ 0 := by omega
    have hoff : f.byteOff = 32 + 8 * (f.wordIdx - 4) := by unfold HdrWordField.byteOff; omega
    have hlt : f.wordIdx - 4 < 140 := by have := f.wordIdx_lt; omega
    have hget := fullHdrTailGet (f.wordIdx - 4) hlt hm
    rw [f.hdrTailWords_get ht c s] at hget
    simpa only [HdrWordField.addr, hnz, ↓reduceIte, hoff] using hget
  · rcases HdrWordField.prefix_cases (f := f) (by omega) with rfl | rfl | rfl | rfl
    · exact load_dimacs_mv (focus_dimacs hm)
    · exact load_dimacs_nc (focus_dimacs hm)
    · exact load_dimacs_cur (focus_dimacs hm)
    · exact load_dimacs_val (focus_dimacs hm)

/-- Generic `FullHdr` 64-bit word store indexed by `HdrWordField` (all `92` mutable words). -/
theorem fullHdr_store (f : HdrWordField) (hmut : f.isMutable = true) (v : BitVec 64)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (f.addr c) ∧
      (FullMem c (f.set s v) ⋆ R) (storeMem m i64 (f.addr c) v) := by
  by_cases ht : 4 ≤ f.wordIdx
  · have hnz : f.wordIdx ≠ 0 := by omega
    have htm : f.isTailMut = true := by simp [HdrWordField.isTailMut, hmut, ht]
    have hoff : f.byteOff = 32 + 8 * (f.wordIdx - 4) := by unfold HdrWordField.byteOff; omega
    have hlt : f.wordIdx - 4 < 140 := by have := f.wordIdx_lt; omega
    have ⟨hd1, hd2, hca, hsa⟩ := f.set_frame htm c s v
    have hput := fullHdrTailPut (f.wordIdx - 4) hlt v (f.set s v) hm
      (f.hdrTailWords_set htm c s v) hd1 hd2 hca hsa
    simpa only [HdrWordField.addr, hnz, ↓reduceIte, hoff] using hput
  · rcases HdrWordField.prefix_cases (f := f) (by omega) with rfl | rfl | rfl | rfl
    · simp [HdrWordField.isMutable] at hmut
    · simp [HdrWordField.isMutable] at hmut
    · obtain ⟨hok, hst⟩ := store_dimacs_cur v (focus_dimacs hm)
      exact ⟨hok, unfocus_dimacs hst⟩
    · obtain ⟨hok, hst⟩ := store_dimacs_val v (focus_dimacs hm)
      exact ⟨hok, unfocus_dimacs hst⟩

/-- Generic `FullHdr` `Nat`-backed word store indexed by `HdrWordField` (`12` `Nat` fields). -/
theorem fullHdr_store_nat (f : HdrWordField) (hnat : f.isNat = true) (v : Nat)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (f.addr c) ∧
      (FullMem c (f.setNat s v) ⋆ R) (storeMem m i64 (f.addr c) (BitVec.ofNat 64 v)) := by
  have ht := HdrWordField.isNat_ge4 hnat
  have hnz : f.wordIdx ≠ 0 := by omega
  have hoff : f.byteOff = 32 + 8 * (f.wordIdx - 4) := by unfold HdrWordField.byteOff; omega
  have hlt : f.wordIdx - 4 < 140 := by have := f.wordIdx_lt; omega
  have ⟨hd1, hd2, hca, hsa⟩ := f.setNat_frame hnat c s v
  have hput := fullHdrTailPut (f.wordIdx - 4) hlt (BitVec.ofNat 64 v) (f.setNat s v) hm
    (f.hdrTailWords_setNat hnat c s v) hd1 hd2 hca hsa
  simpa only [HdrWordField.addr, hnz, ↓reduceIte, hoff] using hput

/-- Offset-lookup bridge for `FullHdr` loads via `HdrWordField.ofOff?`. -/
theorem fullHdr_load_ofOff {off : Nat} {f : HdrWordField} (hlk : HdrWordField.ofOff? off = some f)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 off) = some (f.get c s) := by
  have hbo := HdrWordField.ofOff?_eq_some hlk
  have haddr : c.hdr + BitVec.ofNat 64 off = f.addr c := by
    unfold HdrWordField.addr; split
    · rename_i hz; have : off = 0 := by rw [← hbo, HdrWordField.byteOff, hz]
      subst this; exact BitVec.add_zero c.hdr
    · rw [hbo]
  rw [haddr]; exact fullHdr_load f hm

/-- Offset-lookup bridge for `FullHdr` stores via `HdrWordField.ofOff?`. -/
theorem fullHdr_store_ofOff {off : Nat} {f : HdrWordField} (hlk : HdrWordField.ofOff? off = some f)
    (hmut : f.isMutable = true) (v : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + BitVec.ofNat 64 off) ∧
      (FullMem c (f.set s v) ⋆ R) (storeMem m i64 (c.hdr + BitVec.ofNat 64 off) v) := by
  have hbo := HdrWordField.ofOff?_eq_some hlk
  have haddr : c.hdr + BitVec.ofNat 64 off = f.addr c := by
    unfold HdrWordField.addr; split
    · rename_i hz; have : off = 0 := by rw [← hbo, HdrWordField.byteOff, hz]
      subst this; exact BitVec.add_zero c.hdr
    · rw [hbo]
  rw [haddr]; exact fullHdr_store f hmut v hm

private theorem elemAddr_eq_bytes (a : ArrayField) (c : FullCfg) (i : Nat) :
    a.elemAddr c i = a.ptr c + BitVec.ofNat 64 (a.elemTy.bytes * i) := by
  rcases a.elemTy_cases with h | h | h <;>
    simp [ArrayField.elemAddr, h, Ty.bytes, Ty.size, i8, i32, i64]

private theorem elemAddrBv_eq (a : ArrayField) (c : FullCfg) (i : BitVec 64) :
    a.elemAddrBv c i = a.elemAddr c i.toNat := by
  rcases a.elemTy_cases with h | h | h
  · simp [ArrayField.elemAddrBv, ArrayField.elemAddr, h, i8]
  · simp only [ArrayField.elemAddrBv, ArrayField.elemAddr, h, i32]; exact m4 (a.ptr c) i
  · simp only [ArrayField.elemAddrBv, ArrayField.elemAddr, h, i64]; exact m8 (a.ptr c) i

private theorem elemAddr_zero (a : ArrayField) (c : FullCfg) :
    a.elemAddr c 0 = a.ptr c := by
  rcases a.elemTy_cases with h | h | h <;> simp [ArrayField.elemAddr, h, i8, i32, i64]

private theorem elemTy_bytes_le (a : ArrayField) : a.elemTy.bytes ≤ 2 ^ 64 := by
  rcases a.elemTy_cases with h | h | h <;> simp [h, i8, i32, i64, Ty.bytes, Ty.size]

/-- Generic `FullMem` array load indexed by `ArrayField` (`Nat` index). -/
theorem fullArr_load (a : ArrayField) {i : Nat} (hi : i < (a.get s).length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m a.elemTy (a.elemAddr c i) = some (a.get s)[i] := by
  rw [elemAddr_eq_bytes]; exact loadVal_array (t := a.elemTy) (elemTy_bytes_le a) hi (a.focus hm)

/-- Generic `FullMem` array load indexed by `ArrayField` (`BitVec 64` index). -/
theorem fullArr_load_bv (a : ArrayField) {i : BitVec 64} (hi : i.toNat < (a.get s).length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m a.elemTy (a.elemAddrBv c i) = some (a.get s)[i.toNat] := by
  rw [elemAddrBv_eq]; exact fullArr_load a hi hm

/-- Generic `FullMem` array store indexed by `ArrayField` (`Nat` index). -/
theorem fullArr_store (a : ArrayField) {i : Nat} (v : Val a.elemTy) (hi : i < (a.get s).length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m a.elemTy (a.elemAddr c i) ∧
      (FullMem c (a.set s ((a.get s).set i v)) ⋆ R)
        (storeMem m a.elemTy (a.elemAddr c i) v) := by
  rw [elemAddr_eq_bytes]
  obtain ⟨hok, hst⟩ := store_array (t := a.elemTy) v (elemTy_bytes_le a) hi (a.focus hm)
  exact ⟨hok, a.unfocus hst⟩

/-- Generic `FullMem` array store indexed by `ArrayField` (`BitVec 64` index). -/
theorem fullArr_store_bv (a : ArrayField) {i : BitVec 64} (v : Val a.elemTy)
    (hi : i.toNat < (a.get s).length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m a.elemTy (a.elemAddrBv c i) ∧
      (FullMem c (a.set s ((a.get s).set i.toNat v)) ⋆ R)
        (storeMem m a.elemTy (a.elemAddrBv c i) v) := by
  rw [elemAddrBv_eq]; exact fullArr_store a v hi hm

/-- Generic index-0 base-address load for any `ArrayField`. -/
theorem fullArr_load0 (a : ArrayField) (hi : 0 < (a.get s).length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m a.elemTy (a.ptr c) = some (a.get s)[0] := by
  rw [← elemAddr_zero a c]; exact fullArr_load a hi hm

/-- Generic index-0 base-address store for any `ArrayField`. -/
theorem fullArr_store0 (a : ArrayField) (v : Val a.elemTy) (hi : 0 < (a.get s).length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m a.elemTy (a.ptr c) ∧
      (FullMem c (a.set s ((a.get s).set 0 v)) ⋆ R) (storeMem m a.elemTy (a.ptr c) v) := by
  rw [← elemAddr_zero a c]; exact fullArr_store a v hi hm

end GenericAccessors

/-! ## 2. Strictly Scoped `FullArenaTactics` (`O(1)` `@[scoped c0_load]` / `@[scoped c0_store]`) -/

namespace FullArenaTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true
attribute [scoped bv_c0] HdrWordField.ofOff?_byteOff HdrWordField.ofWordIdx?_wordIdx

@[scoped bv_c0] theorem bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

section GeneratedBridge
open Lean Elab Command

local elab "gen_full_arena_accessors!" : command => do
  let cId := mkIdent `c
  let sId := mkIdent `s
  let rId := mkIdent `R
  let mId := mkIdent `m
  let vId := mkIdent `v
  let iId := mkIdent `i
  let hiId := mkIdent `hi
  let hmId := mkIdent `hm
  let hvId := mkIdent `_hv
  let cHdr := mkIdent (`c ++ `hdr)
  let sCore := mkIdent (`s ++ `core)
  let sScr := mkIdent (`s ++ `scratch)
  let vNat := mkIdent (`v ++ `toNat)
  let iNat := mkIdent (`i ++ `toNat)
  -- 1. Emit `144` header loads and `104` header stores as 1-term calls to `fullHdr_*`
  for idx in [:hdrWordSpecs.size] do
    let sp := hdrWordSpecs[idx]!
    let ctorId := mkIdent (`HdrWordField ++ Name.mkSimple sp.ctor)
    let offLit := Syntax.mkNumLit (toString (8 * idx))
    let addrStx : Term ←
      if idx == 0 then pure cHdr else `(term| $cHdr + $offLit)
    let ldNm := mkIdent (Name.mkSimple ("load_full_" ++ sp.ctor))
    let valStx : Term ← match sp.kind with
      | .cfgNat f => let cf := mkIdent (`c ++ Name.mkSimple f); `(term| BitVec.ofNat 64 $cf)
      | .cfgPtr f => pure (mkIdent (`c ++ Name.mkSimple f))
      | .coreNat f =>
        let sf := mkIdent (`s ++ `core ++ Name.mkSimple f); `(term| BitVec.ofNat 64 $sf)
      | .coreBv f => pure (mkIdent (`s ++ `core ++ Name.mkSimple f))
      | .scrNat f =>
        let sf := mkIdent (`s ++ `scratch ++ Name.mkSimple f); `(term| BitVec.ofNat 64 $sf)
      | .scrBv f => pure (mkIdent (`s ++ `scratch ++ Name.mkSimple f))
    elabCommand (← `(command|
      @[scoped c0_load] theorem $ldNm:ident {$cId : FullCfg} {$sId : FullState}
          {$rId : Mem 64 → Prop} {$mId : Mem 64} ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
          loadVal $mId i64 $addrStx = some $valStx :=
        fullHdr_load $ctorId $hmId))
    let stNm := mkIdent (Name.mkSimple ("store_full_" ++ sp.ctor))
    let c0StNm := mkIdent (Name.mkSimple ("c0_store_full_" ++ sp.ctor))
    match sp.kind with
    | .cfgNat _ | .cfgPtr _ => pure ()
    | .coreBv f =>
      let fi := mkIdent (Name.mkSimple f)
      elabCommand (← `(command|
        @[scoped c0_store] theorem $stNm:ident {$cId : FullCfg} {$sId : FullState}
            {$rId : Mem 64 → Prop} {$mId : Mem 64} ($vId : BitVec 64)
            ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
            storeOk $mId i64 $addrStx ∧
              (FullMem $cId { $sId with core := { $sCore with $fi:ident := $vId } } ⋆ $rId)
                (storeMem $mId i64 $addrStx $vId) :=
          fullHdr_store $ctorId rfl $vId $hmId))
    | .scrBv f =>
      let fi := mkIdent (Name.mkSimple f)
      elabCommand (← `(command|
        @[scoped c0_store] theorem $stNm:ident {$cId : FullCfg} {$sId : FullState}
            {$rId : Mem 64 → Prop} {$mId : Mem 64} ($vId : BitVec 64)
            ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
            storeOk $mId i64 $addrStx ∧
              (FullMem $cId { $sId with scratch := { $sScr with $fi:ident := $vId } } ⋆ $rId)
                (storeMem $mId i64 $addrStx $vId) :=
          fullHdr_store $ctorId rfl $vId $hmId))
    | .coreNat f =>
      let fi := mkIdent (Name.mkSimple f)
      elabCommand (← `(command|
        @[scoped c0_store] theorem $stNm:ident {$cId : FullCfg} {$sId : FullState}
            {$rId : Mem 64 → Prop} {$mId : Mem 64} ($vId : Nat) ($hvId : $vId < 2 ^ 64)
            ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
            storeOk $mId i64 $addrStx ∧
              (FullMem $cId { $sId with core := { $sCore with $fi:ident := $vId } } ⋆ $rId)
                (storeMem $mId i64 $addrStx (BitVec.ofNat 64 $vId)) :=
          fullHdr_store_nat $ctorId rfl $vId $hmId))
      elabCommand (← `(command|
        @[scoped c0_store] theorem $c0StNm:ident {$cId : FullCfg} {$sId : FullState}
            {$rId : Mem 64 → Prop} {$mId : Mem 64} ($vId : BitVec 64)
            ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
            storeOk $mId i64 $addrStx ∧
              (FullMem $cId { $sId with core := { $sCore with $fi:ident := $vNat } } ⋆ $rId)
                (storeMem $mId i64 $addrStx $vId) :=
          fullHdr_store $ctorId rfl $vId $hmId))
    | .scrNat f =>
      let fi := mkIdent (Name.mkSimple f)
      elabCommand (← `(command|
        @[scoped c0_store] theorem $stNm:ident {$cId : FullCfg} {$sId : FullState}
            {$rId : Mem 64 → Prop} {$mId : Mem 64} ($vId : Nat) ($hvId : $vId < 2 ^ 64)
            ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
            storeOk $mId i64 $addrStx ∧
              (FullMem $cId { $sId with scratch := { $sScr with $fi:ident := $vId } } ⋆ $rId)
                (storeMem $mId i64 $addrStx (BitVec.ofNat 64 $vId)) :=
          fullHdr_store_nat $ctorId rfl $vId $hmId))
      elabCommand (← `(command|
        @[scoped c0_store] theorem $c0StNm:ident {$cId : FullCfg} {$sId : FullState}
            {$rId : Mem 64 → Prop} {$mId : Mem 64} ($vId : BitVec 64)
            ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
            storeOk $mId i64 $addrStx ∧
              (FullMem $cId { $sId with scratch := { $sScr with $fi:ident := $vNat } } ⋆ $rId)
                (storeMem $mId i64 $addrStx $vId) :=
          fullHdr_store $ctorId rfl $vId $hmId))
  -- 2. Emit `164` array accessors + `8` index-0 shortcuts as 1-term calls to `fullArr_*`
  for sp in arrayFieldSpecs do
    let ctorId := mkIdent (`ArrayField ++ Name.mkSimple sp.ctor)
    let cPtr := mkIdent (`c ++ Name.mkSimple sp.ptrFld)
    let fldId := mkIdent (Name.mkSimple sp.ctor)
    let elTyId := mkIdent (Name.mkSimple sp.elemTy)
    let valTy : Term ← match sp.elemTy with
      | "i8" => `(BitVec 8)
      | "i32" => `(BitVec 32)
      | _ => `(BitVec 64)
    let lstId := mkIdent <|
      (if sp.isCore then `s ++ `core else `s ++ `scratch) ++ Name.mkSimple sp.ctor
    let mkUpd (idxStx : Term) : CommandElabM Term :=
      if sp.isCore then
        `(term| { $sId with core := { $sCore with $fldId:ident := List.set $lstId $idxStx $vId } })
      else
        `(term|
          { $sId with scratch := { $sScr with $fldId:ident := List.set $lstId $idxStx $vId } })
    let (addrN, addrB) ← match sp.elemTy with
      | "i8" => pure (← `(term| $cPtr + BitVec.ofNat 64 $iId),
                      ← `(term| $cPtr + $iId))
      | "i32" => pure (← `(term| $cPtr + BitVec.ofNat 64 (4 * $iId)),
                       ← `(term| $cPtr + $iId * 4))
      | _ => pure (← `(term| $cPtr + BitVec.ofNat 64 (8 * $iId)),
                   ← `(term| $cPtr + $iId * 8))
    let updN ← mkUpd iId
    let updB ← mkUpd iNat
    let ldNm := mkIdent (Name.mkSimple ("load_full_" ++ sp.ctor))
    let c0LdNm := mkIdent (Name.mkSimple ("c0_load_full_" ++ sp.ctor))
    let stNm := mkIdent (Name.mkSimple ("store_full_" ++ sp.ctor))
    let c0StNm := mkIdent (Name.mkSimple ("c0_store_full_" ++ sp.ctor))
    elabCommand (← `(command|
      @[scoped c0_load] theorem $ldNm:ident {$cId : FullCfg} {$sId : FullState}
          {$rId : Mem 64 → Prop} {$mId : Mem 64} {$iId : Nat}
          ($hiId : $iId < List.length $lstId) ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
          loadVal $mId $elTyId $addrN = some $lstId[$iId] :=
        fullArr_load $ctorId $hiId $hmId))
    elabCommand (← `(command|
      @[scoped c0_load] theorem $c0LdNm:ident {$cId : FullCfg} {$sId : FullState}
          {$rId : Mem 64 → Prop} {$mId : Mem 64} {$iId : BitVec 64}
          ($hiId : $iNat < List.length $lstId) ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
          loadVal $mId $elTyId $addrB = some $lstId[$iNat] :=
        fullArr_load_bv $ctorId $hiId $hmId))
    elabCommand (← `(command|
      @[scoped c0_store] theorem $stNm:ident {$cId : FullCfg} {$sId : FullState}
          {$rId : Mem 64 → Prop} {$mId : Mem 64} {$iId : Nat} ($vId : $valTy)
          ($hiId : $iId < List.length $lstId) ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
          storeOk $mId $elTyId $addrN ∧
            (FullMem $cId $updN ⋆ $rId) (storeMem $mId $elTyId $addrN $vId) :=
        fullArr_store $ctorId $vId $hiId $hmId))
    elabCommand (← `(command|
      @[scoped c0_store] theorem $c0StNm:ident {$cId : FullCfg} {$sId : FullState}
          {$rId : Mem 64 → Prop} {$mId : Mem 64} {$iId : BitVec 64} ($vId : $valTy)
          ($hiId : $iNat < List.length $lstId) ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
          storeOk $mId $elTyId $addrB ∧
            (FullMem $cId $updB ⋆ $rId) (storeMem $mId $elTyId $addrB $vId) :=
        fullArr_store_bv $ctorId $vId $hiId $hmId))
    if sp.idx0 then
      let upd0 ← mkUpd (← `(term| 0))
      let ld0Nm := mkIdent (Name.mkSimple ("load_full_" ++ sp.ctor ++ "0"))
      let st0Nm := mkIdent (Name.mkSimple ("store_full_" ++ sp.ctor ++ "0"))
      elabCommand (← `(command|
        @[scoped c0_load] theorem $ld0Nm:ident {$cId : FullCfg} {$sId : FullState}
            {$rId : Mem 64 → Prop} {$mId : Mem 64}
            ($hiId : 0 < List.length $lstId) ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
            loadVal $mId $elTyId $cPtr = some $lstId[0] :=
          fullArr_load0 $ctorId $hiId $hmId))
      elabCommand (← `(command|
        @[scoped c0_store] theorem $st0Nm:ident {$cId : FullCfg} {$sId : FullState}
            {$rId : Mem 64 → Prop} {$mId : Mem 64} ($vId : $valTy)
            ($hiId : 0 < List.length $lstId) ($hmId : (FullMem $cId $sId ⋆ $rId) $mId) :
            storeOk $mId $elTyId $cPtr ∧
              (FullMem $cId $upd0 ⋆ $rId) (storeMem $mId $elTyId $cPtr $vId) :=
          fullArr_store0 $ctorId $vId $hiId $hmId))

gen_full_arena_accessors!

end GeneratedBridge

end FullArenaTactics

end LeanQbe.T.Examples.Kissat.Proof.Spec
