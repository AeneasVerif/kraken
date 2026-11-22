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

/-! ## 1. Linear-State Pure-Lean Reference Simulator (`0` `.eq_def` M1 Leaks) -/

private def simEmpty : UInt32 := 0xFFFFFFFF

private def simHashEnt (scr : Array UInt32) (ent : UInt32) : UInt32 := Id.run do
  let e := ent.toNat
  let mw := scr[e + 1]!
  let arity := (mw &&& 0xFF).toNat
  let mut h : UInt32 := mw * 0x9E3779B9 + 1
  for j in [:arity] do
    let v := scr[e + 2 + j]!
    h := (h ^^^ (h >>> 13)) * 0x9E3779B9 + v + 1
  return h

private def simHashTmp (htag harity : UInt32) (tmp : Array UInt32) : UInt32 := Id.run do
  let arity := harity.toNat
  let mw := (htag <<< 28) ||| (harity &&& 0xFF)
  let mut h : UInt32 := mw * 0x9E3779B9 + 1
  for j in [:arity] do
    let v := tmp[j]!
    h := (h ^^^ (h >>> 13)) * 0x9E3779B9 + v + 1
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
  for j in [:oldSz] do
    modify fun s => s.set! (htOff + oldSz + j) simEmpty
  for j in [:oldSz] do
    let w := (← get)[htOff + j]!
    if w != simEmpty then
      modify fun s => s.set! (htOff + j) (w ||| 0x80000000)
  for idx in [:oldSz] do
    for _ in [:oldSz] do
      let raw := (← get)[htOff + idx]!
      if raw == simEmpty || (raw &&& 0x80000000) == 0 then
        break
      let ent := raw &&& 0x7FFFFFFF
      modify fun s => s.set! (htOff + idx) simEmpty
      let hv := (simHashEnt (← get) ent).toNat
      let mut slot := hv % newSz
      for _ in [:newSz] do
        let dst := (← get)[htOff + slot]!
        if dst == simEmpty then
          modify fun s => s.set! (htOff + slot) ent
          break
        else if (dst &&& 0x80000000) != 0 then
          modify fun s => (s.set! (htOff + slot) ent).set! (htOff + idx) dst
          break
        slot := (slot + 1) % newSz
  modify fun s => s.set! (ctrlOff + 7) (UInt32.ofNat newSz)
  return newSz

private def simLookup (scr : Array UInt32) (ctrlOff : Nat) (htag harity : UInt32)
    (tmp : Array UInt32) : UInt32 := Id.run do
  let htOff := scr[ctrlOff + 6]!.toNat
  let htSz := scr[ctrlOff + 7]!.toNat
  let hv := (simHashTmp htag harity tmp).toNat
  let mut slot := hv % htSz
  let arity := harity.toNat
  for _ in [:htSz] do
    let ent := scr[htOff + slot]!
    if ent == simEmpty then
      return simEmpty
    let e := ent.toNat
    let mw := scr[e + 1]!
    if (mw >>> 28) == htag && (mw &&& 0xFF) == harity then
      let mut eq := true
      for j in [:arity] do
        if scr[e + 2 + j]! != tmp[j]! then
          eq := false
          break
      if eq then
        return ent
    slot := (slot + 1) % htSz
  return simEmpty

private def simInsert (ctrlOff resSz : Nat) (ent : UInt32) :
    StateM (Array UInt32) (UInt32 × Nat) := do
  let s0 ← get
  let htOff := s0[ctrlOff + 6]!.toNat
  let mut htSz := s0[ctrlOff + 7]!.toNat
  if 4 * (resSz + 1) > 3 * htSz then
    htSz ← simGrow ctrlOff
  let s1 ← get
  let e := ent.toNat
  let mw := s1[e + 1]!
  let arity := (mw &&& 0xFF).toNat
  let hv := (simHashEnt s1 ent).toNat
  let mut slot := hv % htSz
  for _ in [:htSz] do
    let s2 ← get
    let cur := s2[htOff + slot]!
    if cur == simEmpty then
      modify fun s => s.set! (htOff + slot) ent
      return (ent, resSz + 1)
    let ce := cur.toNat
    if s2[ce + 1]! == mw then
      let mut eq := true
      for j in [:arity] do
        if s2[ce + 2 + j]! != s2[e + 2 + j]! then
          eq := false
          break
      if eq then
        return (cur, resSz)
    slot := (slot + 1) % htSz
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
    let _ ← simInit 0 64 16
    let x1 : UInt32 := 10
    let mut x2 : UInt32 := 0
    let target := (simHashTmp 2 1 #[10]).toNat % 16
    for k in [11:200] do
      if (simHashTmp 2 1 #[UInt32.ofNat k]).toNat % 16 == target then
        x2 := UInt32.ofNat k
        break
    if x2 == 0 then return false
    modify fun s =>
      ((((((((s.set! 16 0).set! 17 (((2 : UInt32) <<< 28) ||| 1)).set! 18 x1).set!
        20 0).set! 21 (((2 : UInt32) <<< 28) ||| 1)).set! 22 x2).set!
        24 0).set! 25 (((2 : UInt32) <<< 28) ||| 1)).set! 26 x1
    let (r1, rsz1) ← simInsert 0 0 16
    let (r2, rsz2) ← simInsert 0 rsz1 20
    let (r3, rsz3) ← simInsert 0 rsz2 24
    if r1 != 16 || r2 != 20 || r3 != 16 || rsz3 != 2 then return false
    let scr ← get
    if simLookup scr 0 2 1 #[x1] != 16 || simLookup scr 0 2 1 #[x2] != 20 then return false
    if simLookup scr 0 2 1 #[99999] != simEmpty then return false
    let szG ← simGrow 0
    if szG != 32 then return false
    let scrG ← get
    return simLookup scrG 0 2 1 #[x1] == 16 &&
      simLookup scrG 0 2 1 #[x2] == 20) (Array.replicate 256 (0 : UInt32))).1
  let capOk := (Id.run <| StateT.run (m := Id) (do
    let szTight ← simInit 0 64 131072
    let szCap ← simGrow 0
    return szTight == 16384 && szCap == 16384) (Array.replicate 20000 (0 : UInt32))).1
  let failOk := (Id.run <| StateT.run (m := Id) (do
    let szFail ← simInit 0 64 16
    return szFail == 0) (Array.replicate 70 (0 : UInt32))).1
  colOk && capOk && failOk

#guard testScaleTo65536And131072
#guard testAutoGrowPast4096
#guard testCollisionAndTightCap

/-! ## 2. Static IR, SpecTable, C++ / QBE Emission & 4-ISA Legalization Guards -/

#guard m7CongHash_fns.length == 5
#guard m7CongHashModule.fns.length == 5
#guard m7CongHashSpecTable.length == 5
#guard (PrintCpp.ppTModule m7CongHashModule).isOk
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
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_cong_ht_grow

theorem m7ch_nv_insert_thm :
    Func.wp m7CongHashEnv full_cong_ht_insert_m7_body
      (nvM7CongCfg.hdr, 0#64, 8#32, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        PreservesCoreSlice FullState.core nvM7CongState s' ∧ s'.LengthsOk nvM7CongCfg ∧
        FullExtScratchPres nvM7CongState s' ∧
        (∃ new_sz, (new_sz = 8192 ∨ new_sz = 16384) ∧
          M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 new_sz) ∧
        (ret = 0xFFFFFFFF#32 ∨ ret = 8#32 ∨ ret.toNat < 64) ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_cong_ht_insert

end LeanQbeTest.T.KissatM7CongHashTest

abbrev m7ch_wf := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_wf_thm
abbrev m7ch_acyc := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_acyc_thm
abbrev m7ch_no_exit := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_no_exit_thm
abbrev m7ch_tbl := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_tbl_thm
abbrev m7ch_mod_ok := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_mod_ok_thm
abbrev m7ch_nv_init := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_init_thm
abbrev m7ch_nv_grow := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_grow_thm
abbrev m7ch_nv_insert := @LeanQbeTest.T.KissatM7CongHashTest.m7ch_nv_insert_thm

#print axioms m7ch_wf
#print axioms m7ch_acyc
#print axioms m7ch_no_exit
#print axioms m7ch_tbl
#print axioms m7ch_mod_ok
#print axioms m7ch_nv_init
#print axioms m7ch_nv_grow
#print axioms m7ch_nv_insert
