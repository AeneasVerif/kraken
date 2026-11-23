module

public meta import LeanQbe.T.Examples.Kissat.FullM7CongHash
public meta import LeanQbe.T.Examples.Kissat.FullM7CongHashProof
public import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Unit Tests, 4-ISA Legalization & Axiom Audit (`KissatM7CongHashTest`)

Verifies `FullM7CongHash` & `FullM7CongHashProof` (`FullM7CongHashProof0`):
1. Executable `#guard` simulation of dynamic congruence hash-table power-of-2 scaling beyond
   legacy `4096` (`4096 -> 8192 -> 16384 -> 32768 -> 65536 -> 131072`), collision-chain probing
   & miss detection, and tight `scratch_cap` power-of-2 capping without OOM or table wipe.
2. Static `#guard` checks on `m7CongHashModule`, `m7CongHashSpecTable`, C++ / QBE emission,
   and 4-ISA `Fn.legal` legalization (`.aarch64`, `.scalar64`, `.x64AVX2`, `.x64AVX512`).
3. Restated module-level verification, concrete `Mem 64` UNSAT NV theorems, and single-line
   `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7CongHashTest

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7CongHash

/-! ## 1. Linear-State Pure-Lean Reference Simulator (`0` `.eq_def` Reduction Leaks) -/

private def simEmpty : UInt32 := 0xFFFFFFFF

private def simHashEnt (scr : Array UInt32) (ent : UInt32) : UInt64 := Id.run do
  let e := ent.toNat
  let mw := scr[e + 1]!
  let etag := (mw >>> 28).toUInt64
  let arity := (mw &&& 0xFF).toNat
  let mut h : UInt64 := etag * 0x9E3779B1 + arity.toUInt64
  for j in [:arity] do
    h := h * 0x85EBCA77 + scr[e + 2 + j]!.toUInt64 + 1
  return h

private def simHashTmp (htag harity : UInt32) (tmp : Array UInt32) : UInt64 := Id.run do
  let arity := harity.toNat
  let mut h : UInt64 := htag.toUInt64 * 0x9E3779B1 + harity.toUInt64
  for j in [:arity] do
    h := h * 0x85EBCA77 + tmp[j]!.toUInt64 + 1
  return h

private def simInit (ctrlOff htOff maxSz : Nat) : StateM (Array UInt32) Nat := do
  let cap := (← get).size
  if ctrlOff + 8 > htOff || htOff + 16 > cap || htOff > 0x7FFFFFFF then
    return 0
  let avail := cap - htOff
  let mut lim := if maxSz == 0 then 131072 else min 131072 (max 16 maxSz)
  if avail < lim then
    lim := avail
  let mut sz : Nat := 16
  for _ in [:16] do
    if 2 * sz ≤ lim && 2 * sz ≤ 131072 then
      sz := 2 * sz
  for j in [:sz] do
    modify fun s => s.set! (htOff + j) simEmpty
  modify fun s =>
    (s.set! (ctrlOff + 6) (UInt32.ofNat htOff)).set! (ctrlOff + 7) (UInt32.ofNat sz)
  return sz

private def simGrow (ctrlOff : Nat) : StateM (Array UInt32) Nat := do
  let s0 ← get
  let cap := s0.size
  let htOff := s0[ctrlOff + 6]!.toNat
  let oldSz := s0[ctrlOff + 7]!.toNat
  if oldSz ≥ 131072 || htOff + 2 * oldSz > cap then
    return oldSz
  let newSz := 2 * oldSz
  for k in [oldSz:newSz] do
    modify fun s => s.set! (htOff + k) simEmpty
  for i in [:oldSz] do
    let raw := (← get)[htOff + i]!
    if raw != simEmpty && (raw &&& 0x80000000) == 0 && raw.toNat < htOff then
      modify fun s => s.set! (htOff + i) simEmpty
      let mut cur := raw
      for _ in [:newSz] do
        if cur == simEmpty then
          break
        let hv := simHashEnt (← get) cur
        let mut slot := (hv &&& (UInt64.ofNat newSz - 1)).toNat
        let mut nextCur := cur
        for _ in [:newSz] do
          let dst := (← get)[htOff + slot]!
          if dst == simEmpty then
            modify fun s => s.set! (htOff + slot) (cur ||| 0x80000000)
            nextCur := simEmpty
            break
          else if (dst &&& 0x80000000) == 0 then
            modify fun s => s.set! (htOff + slot) (cur ||| 0x80000000)
            nextCur := if dst.toNat < htOff then dst else simEmpty
            break
          slot := (slot + 1) &&& (newSz - 1)
        cur := nextCur
  for j in [:newSz] do
    let v := (← get)[htOff + j]!
    if v != simEmpty then
      modify fun s => s.set! (htOff + j) (v &&& 0x7FFFFFFF)
  modify fun s => s.set! (ctrlOff + 7) (UInt32.ofNat newSz)
  return newSz

private def simGrowClear (ctrlOff resSz : Nat) : StateM (Array UInt32) (Nat × Nat) := do
  let s0 ← get
  let cap := s0.size
  let htOff := s0[ctrlOff + 6]!.toNat
  let oldSz := s0[ctrlOff + 7]!.toNat
  if oldSz == 131072 || htOff + 2 * oldSz > cap then
    return (oldSz, resSz)
  let newSz := 2 * oldSz
  for j in [:newSz] do
    modify fun s => s.set! (htOff + j) simEmpty
  modify fun s => s.set! (ctrlOff + 7) (UInt32.ofNat newSz)
  return (newSz, 0)

private def simLookup (scr : Array UInt32) (ctrlOff : Nat) (htag harity : UInt32)
    (tmp : Array UInt32) : UInt32 := Id.run do
  let htOff := scr[ctrlOff + 6]!.toNat
  let htSz := scr[ctrlOff + 7]!.toNat
  let hv := (simHashTmp htag harity tmp).toNat
  let mut slot := hv &&& (htSz - 1)
  let arity := harity.toNat
  for _ in [:htSz] do
    let ent := scr[htOff + slot]!
    if ent == simEmpty then
      return simEmpty
    let e := ent.toNat
    if e + 2 + arity ≤ htOff then
      let mw := scr[e + 1]!
      if (mw >>> 28) == htag && (mw &&& 0xFF) == harity then
        let mut eq := true
        for j in [:arity] do
          if scr[e + 2 + j]! != tmp[j]! then
            eq := false
            break
        if eq then
          return ent
    slot := (slot + 1) &&& (htSz - 1)
  return simEmpty

private def simInsert (ctrlOff resSz : Nat) (ent : UInt32) :
    StateM (Array UInt32) (UInt32 × Nat) := do
  let s0 ← get
  let htOff := s0[ctrlOff + 6]!.toNat
  let mut htSz := s0[ctrlOff + 7]!.toNat
  if htSz ≤ 131072 && (resSz ≥ htSz || 4 * resSz ≥ 3 * htSz) then
    htSz ← simGrow ctrlOff
  let s1 ← get
  let e := ent.toNat
  let mw := s1[e + 1]!
  let etag := mw >>> 28
  let earity := mw &&& 0xFF
  let arity := earity.toNat
  let hv := (simHashEnt s1 ent).toNat
  let mut slot := hv &&& (htSz - 1)
  for _ in [:htSz] do
    let s2 ← get
    let cur := s2[htOff + slot]!
    if cur == simEmpty then
      modify fun s => s.set! (htOff + slot) ent
      return (ent, resSz + 1)
    if cur == ent then
      return (ent, resSz)
    let ce := cur.toNat
    if ce + 2 + arity ≤ htOff then
      let mw_c := s2[ce + 1]!
      if (mw_c >>> 28) == etag && (mw_c &&& 0xFF) == earity then
        let mut eq := true
        for j in [:arity] do
          if s2[ce + 2 + j]! != s2[e + 2 + j]! then
            eq := false
            break
        if eq then
          return (cur, resSz)
    slot := (slot + 1) &&& (htSz - 1)
  return (simEmpty, resSz)

private def testScaleTo65536And131072 : Bool :=
  let run64 := (Id.run <| StateT.run (m := Id) (do
    let sz0 ← simInit 0 1024 4096
    if sz0 != 4096 then return false
    modify fun s => ((s.set! 64 0).set! 65 (((1 : UInt32) <<< 28) ||| 1)).set! 66 42
    let (r0, rsz) ← simInsert 0 0 64
    if r0 != 64 || rsz != 1 then return false
    let sz1 ← simGrow 0
    let sz2 ← simGrow 0
    let sz3 ← simGrow 0
    let sz4 ← simGrow 0
    let sz5 ← simGrow 0
    let scr ← get
    let found := simLookup scr 0 1 1 #[42]
    return [sz0, sz1, sz2, sz3, sz4, sz5] == [4096, 8192, 16384, 32768, 65536, 65536] &&
      scr[7]!.toNat == 65536 && found == 64) (Array.replicate 70000 (0 : UInt32))).1
  let run128 := (Id.run <| StateT.run (m := Id) (do
    let sz0 ← simInit 0 1024 4096
    modify fun s => ((s.set! 64 0).set! 65 (((1 : UInt32) <<< 28) ||| 1)).set! 66 77
    let (_, _) ← simInsert 0 0 64
    let sz1 ← simGrow 0
    let sz2 ← simGrow 0
    let sz3 ← simGrow 0
    let sz4 ← simGrow 0
    let sz5 ← simGrow 0
    let sz6 ← simGrow 0
    let scr ← get
    let found := simLookup scr 0 1 1 #[77]
    return [sz0, sz1, sz2, sz3, sz4, sz5, sz6] ==
        [4096, 8192, 16384, 32768, 65536, 131072, 131072] &&
      scr[7]!.toNat == 131072 && found == 64) (Array.replicate 140000 (0 : UInt32))).1
  run64 && run128

private def testAutoGrowPast4096 : Bool := (Id.run <| StateT.run (m := Id) (do
  let nGates := 6200
  let htOff := nGates * 3 + 64
  let sz0 ← simInit 0 htOff 4096
  if sz0 != 4096 then return false
  for i in [:nGates] do
    let e := 16 + i * 3
    modify fun s =>
      ((s.set! e (UInt32.ofNat i)).set! (e + 1) (((1 : UInt32) <<< 28) ||| 1)).set!
        (e + 2) (UInt32.ofNat (1000 + i))
  let mut rsz := 0
  for i in [:nGates] do
    let e := UInt32.ofNat (16 + i * 3)
    let (r, rsz') ← simInsert 0 rsz e
    if r != e then return false
    rsz := rsz'
  let scr ← get
  if scr[7]!.toNat != 16384 || rsz != nGates then return false
  for i in [:nGates] do
    let e := UInt32.ofNat (16 + i * 3)
    if simLookup scr 0 1 1 #[UInt32.ofNat (1000 + i)] != e then
      return false
  return simLookup scr 0 1 1 #[999999] == simEmpty) (Array.replicate (6200 * 3 + 20064) 0)).1

private def testCollisionAndTightCap : Bool :=
  let colOk := (Id.run <| StateT.run (m := Id) (do
    let _ ← simInit 0 64 8192
    let hA := (simHashTmp 1 1 #[14915]).toNat
    let hB := (simHashTmp 1 1 #[31299]).toNat
    let hC := (simHashTmp 1 1 #[14916]).toNat
    if hA % 8192 != 2 || hB % 8192 != 2 || hC % 8192 != 3 then return false
    if hA % 16384 != 2 || hB % 16384 != 2 || hC % 16384 != 3 then return false
    modify fun s =>
      ((((((((s.set! 8 0).set! 9 (((1 : UInt32) <<< 28) ||| 1)).set! 10 14915).set!
        16 0).set! 17 (((1 : UInt32) <<< 28) ||| 1)).set! 18 31299).set!
        24 0).set! 25 (((1 : UInt32) <<< 28) ||| 1)).set! 26 14916
    modify fun s =>
      ((((s.set! 32 0).set! 33 (((1 : UInt32) <<< 28) ||| 1)).set! 34 14915))
    let (rC, rsz1) ← simInsert 0 0 24
    let (rA, rsz2) ← simInsert 0 rsz1 8
    let (rB, rsz3) ← simInsert 0 rsz2 16
    let (rDup, rsz4) ← simInsert 0 rsz3 32
    if rC != 24 || rA != 8 || rB != 16 || rDup != 8 || rsz4 != 3 then return false
    let scr ← get
    if scr[64 + 3]! != 24 || scr[64 + 2]! != 8 || scr[64 + 4]! != 16 then return false
    if simLookup scr 0 1 1 #[14915] != 8 || simLookup scr 0 1 1 #[31299] != 16 ||
        simLookup scr 0 1 1 #[14916] != 24 then return false
    if simLookup scr 0 1 1 #[99999] != simEmpty then return false
    let szG ← simGrow 0
    if szG != 16384 then return false
    let scrG ← get
    return simLookup scrG 0 1 1 #[14915] == 8 &&
      simLookup scrG 0 1 1 #[31299] == 16 &&
      simLookup scrG 0 1 1 #[14916] == 24) (Array.replicate 16500 (0 : UInt32))).1
  let clearOk := (Id.run <| StateT.run (m := Id) (do
    let sz0 ← simInit 0 64 4096
    modify fun s => ((s.set! 8 0).set! 9 (((1 : UInt32) <<< 28) ||| 1)).set! 10 14915
    let (_, rsz1) ← simInsert 0 0 8
    let (sz1, r1) ← simGrowClear 0 rsz1
    let (sz2, r2) ← simGrowClear 0 123
    let (sz3, r3) ← simGrowClear 0 456
    let (sz4, r4) ← simGrowClear 0 789
    let (sz5, r5) ← simGrowClear 0 999
    let (sz6, r6) ← simGrowClear 0 42
    let scr ← get
    return [sz0, sz1, sz2, sz3, sz4, sz5, sz6] ==
        [4096, 8192, 16384, 32768, 65536, 131072, 131072] &&
      [r1, r2, r3, r4, r5, r6] == [0, 0, 0, 0, 0, 42] &&
      scr[64 + 2]! == simEmpty) (Array.replicate 132000 (0 : UInt32))).1
  let capOk := (Id.run <| StateT.run (m := Id) (do
    let szTight ← simInit 0 64 131072
    modify fun s => ((s.set! 8 0).set! 9 (((1 : UInt32) <<< 28) ||| 1)).set! 10 14915
    let (_, rsz1) ← simInsert 0 0 8
    let szCap ← simGrow 0
    let (szNoWipe, rsz2) ← simGrowClear 0 rsz1
    let scr ← get
    return szTight == 16384 && szCap == 16384 && szNoWipe == 16384 && rsz2 == rsz1 &&
      simLookup scr 0 1 1 #[14915] == 8) (Array.replicate 20000 (0 : UInt32))).1
  let failOk := (Id.run <| StateT.run (m := Id) (do
    let szFail ← simInit 0 64 16
    return szFail == 0) (Array.replicate 70 (0 : UInt32))).1
  colOk && clearOk && capOk && failOk

#guard testScaleTo65536And131072
#guard testAutoGrowPast4096
#guard testCollisionAndTightCap

/-! ## 2. Static IR, SpecTable, C++ / QBE Emission & 4-ISA Legalization Guards -/

#guard m7CongHash_fns.length == 6
#guard m7CongHashModule.fns.length == 6
#guard m7CongHashSpecTable.length == 6
#guard (PrintCpp.ppTModule m7CongHashModule).isOk
#guard match PrintCpp.ppTModule m7CongHashModule with
  | .ok s => (s.splitOn "full_cong_ht_grow_clear_m7").length > 1 &&
      (s.splitOn "9e3779b1").length > 1 && (s.splitOn "85ebca77").length > 1 &&
      (s.splitOn "0x20000ULL").length > 1
  | .error _ => false
#guard (PrintQbe.module m7CongHashModule).isOk
#guard (PrintCpp.ppModule (m7CongHash_fns.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (m7CongHash_fns.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (m7CongHash_fns.map (Fn.legal .x64AVX2))).isOk
#guard m7CongHash_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. Restated Module-Level Verification & Non-Vacuity Theorems -/

theorem m7ch_wf_thm : ∀ f ∈ m7CongHashFns, f.Wf :=
  m7CongHashFns_wf

theorem m7ch_acyc_thm : m7CongHashModule.checkAcyclic = true :=
  m7CongHash_acyclic

theorem m7ch_no_exit_thm :
    ∀ (f : Sym) (as bs : List Ty) (xs : Tup Val as)
      (m : Mem 64) (Q : Post bs) (X X' : XPost),
      m7CongHashEnv f as bs xs m Q X → m7CongHashEnv f as bs xs m Q X' :=
  m7CongHashEnv_noExit

theorem m7ch_tbl_thm :
    TableImpl m7CongHashEnv m7CongHashFns m7CongHashSpecTable :=
  m7CongHash_tableImpl

theorem m7ch_mod_ok_thm : ModuleOk m7CongHashEnv m7CongHashModule :=
  m7CongHash_moduleOk

theorem m7ch_nv_init_thm :
    Func.wp m7CongHashEnv full_cong_ht_init_m7_body
      (nvM7CongCfg.hdr, 0#64, 64#64, 16384#64, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16384#64 ∧ PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_cong_ht_init

theorem m7ch_nv_grow_thm :
    Func.wp m7CongHashEnv full_cong_ht_grow_m7_body
      (nvM7CongCfg.hdr, 0#64, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16384#64 ∧ PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        (∃ jC < 16384, s'.scratch.scratch_buf[64 + jC]? = some 24#32) ∧
        (∃ jA < 16384, s'.scratch.scratch_buf[64 + jA]? = some 8#32) ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_cong_ht_grow

theorem m7ch_nv_grow_clear_thm :
    Func.wp m7CongHashEnv full_cong_ht_grow_clear_m7_body
      (nvM7CongCfg.hdr, 0#64, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16384#64 ∧ s'.scratch.res_sz = 0#64 ∧
        PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        (∀ j < 16384, s'.scratch.scratch_buf[64 + j]? = some 0xFFFFFFFF#32) ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_cong_ht_grow_clear

theorem m7ch_nv_lookup_thm :
    Func.wp m7CongHashEnv full_cong_ht_lookup_m7_body
      (nvM7CongCfg.hdr, 0#64, 1#32, 1#32, ()) nvM7CongMem
      (fun (ret, ()) m' => ret = 8#32 ∧ m' = nvM7CongMem)
      (fun _ _ _ _ => False) :=
  nv_m7_cong_ht_lookup

theorem m7ch_nv_insert_thm :
    Func.wp m7CongHashEnv full_cong_ht_insert_m7_body
      (nvM7CongCfg.hdr, 0#64, 16#32, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16#32 ∧ PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 8192 ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_cong_ht_insert

theorem m7ch_nv_insert_grow_thm :
    Func.wp m7CongHashEnv full_cong_ht_insert_m7_body
      (nvM7CongCfg.hdr, 0#64, 16#32, ()) nvM7CongMemGrow
      (fun (ret, ()) m' => ∃ s',
        ret = 16#32 ∧ PreservesCoreSlice FullState.core nvM7CongStateGrow s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongStateGrow s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        (∃ jC < 16384, s'.scratch.scratch_buf[64 + jC]? = some 24#32) ∧
        (∃ jA < 16384, s'.scratch.scratch_buf[64 + jA]? = some 8#32) ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_cong_ht_insert_grow

end LeanQbeTest.T.KissatM7CongHashTest

abbrev m7ch_wf := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_wf_thm
abbrev m7ch_acyc := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_acyc_thm
abbrev m7ch_no_exit := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_no_exit_thm
abbrev m7ch_tbl := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_tbl_thm
abbrev m7ch_mod_ok := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_mod_ok_thm
abbrev m7ch_nv_init := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_init_thm
abbrev m7ch_nv_grow := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_grow_thm
abbrev m7ch_nv_grow_clear := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_grow_clear_thm
abbrev m7ch_nv_lookup := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_lookup_thm
abbrev m7ch_nv_insert := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_insert_thm
abbrev m7ch_nv_insert_grow := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_insert_grow_thm

#print axioms m7ch_wf
#print axioms m7ch_acyc
#print axioms m7ch_no_exit
#print axioms m7ch_tbl
#print axioms m7ch_mod_ok
#print axioms m7ch_nv_init
#print axioms m7ch_nv_grow
#print axioms m7ch_nv_grow_clear
#print axioms m7ch_nv_lookup
#print axioms m7ch_nv_insert
#print axioms m7ch_nv_insert_grow
