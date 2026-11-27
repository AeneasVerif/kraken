/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
public import LeanQbe.T.LeanLCNF.LcnfC0FfiProof
public import LeanQbe.T.Examples.Kissat.PlainLemmas
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.ControlComb

/-!
# Shard `F3` Pilot C0 Kernel & Kissat Wrappers WP Proofs (`LcnfC0FfiPilotProof0`)

Target-generic specifications, environment setup, and WP proofs for:
- `c0_xor_bytes`: `K2a` 6-arg pure byte-XOR kernel returning `(status << 56) | out_len`
- `lcnf_c0_kissat_raw`: top-down `s_end` scratch carve/reclaim around `kissat_solve_bytes`
- `lcnf_c0_kissat_solve_ba` / `lcnf_c0_kissat_solve_nat`: borrowed `ByteArray` / sentineled `Nat`
  Kissat entry points (`L ≤ 7` via `rt->scratch[0]`, `L ≥ 8` zero-copy MPZ).

Companion `LcnfC0FfiPilotProof1.lean` verifies `lcnf_c0_xor_ba`, `lcnf_c0_xor_nat`, and
`pilotC0Mod_moduleOk`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.LcnfC0FfiPilot

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open scoped LeanQbe.T.ProofUtil

local macro "p0_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hfast))
local macro "p0_split" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hsplit))
local macro "p0_straight" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hstraight))
local macro "p0_call " h:ident : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_))

public section

/-! ## 1. Specifications (`K2a` Kernel & 5 Thin Non-Aborting C0 Wrappers) -/

/-- Specification for `c0_xor_bytes(in_ptr, in_len, out_ptr, out_cap, key_u8, flags)`:
returns `(status << 56) | out_len`, with `status = 0` on success, `2` on nonzero `flags`, and
`1` on length/capacity/overflow bounds violation. -/
@[expose] def c0XorBytesSpec : Spec [i64, i64, i64, i64, i64, i64] [i64] :=
  fun (inPtr, inLen, outPtr, outCap, keyU8, flags, ()) m Q _ =>
    if flags ≠ 0#64 then
      Q (2#64 <<< 56#64, ()) m
    else if inLen.toNat > 0x00ffffffffffffff ∨ inLen.toNat > outCap.toNat ∨
        inPtr.toNat + inLen.toNat ≥ 2 ^ 64 ∨ outPtr.toNat + outCap.toNat ≥ 2 ^ 64 then
      Q (1#64 <<< 56#64, ()) m
    else
      ∃ (inData : List UInt8) (R : Mem 64 → Prop),
        inData.length = inLen.toNat ∧
        (bytes inPtr inData ⋆ region outPtr outCap.toNat ⋆ R) m ∧
        ∀ m',
          (bytes inPtr inData ⋆
            bytes outPtr (inData.map (· ^^^ UInt8.ofNat keyU8.toNat)) ⋆
            region (outPtr + inLen) (outCap.toNat - inLen.toNat) ⋆ R) m' →
          Q (inLen, ()) m'

/-- Specification for `lcnf_c0_kissat_raw(rt, cnf_ptr, cnf_len, work_req, fuel)`.
Never panics (`XPost := False`): returns `3#64` on invalid/OOM scratch carve, else delegates
to `Kissat.Plain.kissat_solve_bytes` and reclaims the carved `s_end` workspace. -/
@[expose] def pilotKissatRawSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (rt, cnfPtr, cnfLen, workReq, fuel, ()) m Q _ =>
    ∃ (st : RtC0State) (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cnfLen = BitVec.ofNat 64 cnfBytes.length ∧
      cnfPtr.toNat + cnfBytes.length < 2 ^ 64 ∧
      (rtC0Inv rt st ⋆ bytes cnfPtr cnfBytes ⋆ R) m ∧
      if ffiCarveOk st workReq then
        ∀ r st' m',
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧
            ∃ α, cnf.Sat α) →
          (∀ mv nc i0,
            0 < fuel.toNat →
            plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq →
            i0 ≤ cnfBytes.length →
            parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
            UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
            r = 20#64) →
          (∀ mv nc i0 vals' te',
            te' < fuel.toNat →
            plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq →
            i0 ≤ cnfBytes.length →
            parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
            UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0
              (cnfBytes.drop i0) nc vals' te' →
            (∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
            runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) mv = true →
            r = 10#64) →
          st'.PreservesMetaExceptEnd st →
          st'.hdr.s_end = st.hdr.s_end →
          st'.rem = st.rem →
          (rtC0Inv rt st' ⋆ bytes cnfPtr cnfBytes ⋆ R) m' →
          Q (r, ()) m'
      else
        Q (3#64, ()) m

/-- Specification for `lcnf_c0_kissat_solve_ba(rt, ba, work_req, fuel)`. -/
@[expose] def pilotKissatSolveBASpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (rt, ba, workReq, fuel, ()) m Q _ =>
    ∃ (st : RtC0State) (baObj : LcnfObj) (R : Mem 64 → Prop),
      baObj.addr = ba ∧ BaCanon baObj ∧
      (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m ∧
      if baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64 ∧
          ffiCarveOk st workReq then
        ∀ r st' m',
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
          (r = 20#64 → ∃ cnf, parseDimacs baObj.scalarData = some cnf ∧ cnf.Unsat) →
          (r = 10#64 → ∃ cnf, parseDimacs baObj.scalarData = some cnf ∧ ¬ cnf.Unsat ∧
            ∃ α, cnf.Sat α) →
          (∀ mv nc i0,
            0 < fuel.toNat →
            plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq →
            i0 ≤ baObj.scalarData.length →
            parseHeader baObj.scalarData = some (mv, nc, baObj.scalarData.drop i0) →
            UnitUnsatTrace mv (List.replicate (2 * mv) 0#8)
              (baObj.scalarData.drop i0) nc →
            r = 20#64) →
          (∀ mv nc i0 vals' te',
            te' < fuel.toNat →
            plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq →
            i0 ≤ baObj.scalarData.length →
            parseHeader baObj.scalarData = some (mv, nc, baObj.scalarData.drop i0) →
            UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0
              (baObj.scalarData.drop i0) nc vals' te' →
            (∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
            runKissatCheckModel baObj.scalarData (vals'.map UInt8.ofBitVec) mv = true →
            r = 10#64) →
          st'.PreservesMetaExceptEnd st →
          st'.hdr.s_end = st.hdr.s_end →
          st'.rem = st.rem →
          (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m' →
          Q (r, ()) m'
      else
        Q (3#64, ()) m

/-- Specification for `lcnf_c0_kissat_solve_nat(rt, a, work_req, fuel)`.
Handles both tagged `L ≤ 7` sentineled Nats (via `rt->scratch[0]`) and boxed `L ≥ 8` MPZs
(zero-copy directly from `a + 16`), never panicking. -/
@[expose] def pilotKissatSolveNatSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (rt, a, workReq, fuel, ()) m Q _ =>
    ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
      (val : Nat) (objs : List LcnfObj) (R : Mem 64 → Prop),
      scrLimbs.length < 2 ^ 64 ∧
      RtNatRep a val objs ∧
      (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
      match bytesOfNatS val with
      | none => Q (1#64, ()) m
      | some bs =>
        if (a &&& 1#64) ≠ 0#64 ∧ (scr = 0#64 ∨ scrLimbs.length = 0) then
          Q (3#64, ()) m
        else
          ((a &&& 1#64) ≠ 0#64 → scr.toNat + 8 < 2 ^ 64) ∧
          ((a &&& 1#64) = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64) ∧
          if ffiCarveOk st workReq then
            ∀ r st' scrLimbs' m',
              (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
              scrLimbs'.length = scrLimbs.length →
              (r = 20#64 → ∃ cnf, parseDimacs bs = some cnf ∧ cnf.Unsat) →
              (r = 10#64 → ∃ cnf, parseDimacs bs = some cnf ∧ ¬ cnf.Unsat ∧
                ∃ α, cnf.Sat α) →
              (∀ mv nc i0,
                0 < fuel.toNat →
                plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq →
                i0 ≤ bs.length →
                parseHeader bs = some (mv, nc, bs.drop i0) →
                UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (bs.drop i0) nc →
                r = 20#64) →
              (∀ mv nc i0 vals' te',
                te' < fuel.toNat →
                plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq →
                i0 ≤ bs.length →
                parseHeader bs = some (mv, nc, bs.drop i0) →
                UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0
                  (bs.drop i0) nc vals' te' →
                (∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                runKissatCheckModel bs (vals'.map UInt8.ofBitVec) mv = true →
                r = 10#64) →
              st'.PreservesMetaExceptEnd st →
              st'.hdr.s_end = st.hdr.s_end →
              st'.rem = st.rem →
              (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
                array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m' →
              Q (r, ()) m'
          else
            ∀ scrLimbs' m',
              scrLimbs'.length = scrLimbs.length →
              (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
                array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m' →
              Q (3#64, ()) m'

/-- Headroom predicate for `lcnf_c0_xor_ba(rt, ba, key)` succeeding with `.ok`. -/
@[expose] def pilotXorBaOk (st : RtC0State) (len : Nat) : Prop :=
  len ≤ ffiBaMaxCap ∧
  if len = 0 then
    baAllocBytes 0 + 16 ≤ st.rem
  else
    ffiCarveOk st (BitVec.ofNat 64 len) ∧
    baAllocBytes len + 16 ≤
      (ffiCarveWend st.hdr.s_end).toNat - ffiCarveWcap (BitVec.ofNat 64 len) - st.hdr.s_cur.toNat

instance instDecidablePilotXorBaOk (st : RtC0State) (len : Nat) :
    Decidable (pilotXorBaOk st len) := by
  unfold pilotXorBaOk
  infer_instance

/-- Specification for `lcnf_c0_xor_ba(rt, ba, key)`. -/
@[expose] def pilotXorBASpec : Spec [i64, i64, i8] [i64] := fun (rt, ba, key, ()) m Q _ =>
  ∃ (st : RtC0State) (baObj : LcnfObj) (R : Mem 64 → Prop),
    baObj.addr = ba ∧ BaCanon baObj ∧
    baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64 ∧
    (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m ∧
    let len := baObj.scalarData.length
    let outData := baObj.scalarData.map (· ^^^ UInt8.ofNat key.toNat)
    if pilotXorBaOk st len then
      ∀ p baNew st' m',
        p ≠ 0#64 → p.toNat % 8 = 0 →
        baNew ≠ 0#64 → baNew.toNat % 8 = 0 →
        st'.PreservesMetaExceptEnd st → st'.hdr.s_end = st.hdr.s_end →
        st'.rem ≤ st.rem → st.rem - (baAllocBytes len + 16) ≤ st'.rem →
        let newBaObj := mkBaObj baNew 1#32 len outData
        let okObj := mkFfiResOkObj p baNew
        BaCanon newBaObj → FfiResOkCanon okObj baNew →
        (rtC0Inv rt st' ⋆ lcnfObjMem okObj ⋆ lcnfObjMem newBaObj ⋆ lcnfObjMem baObj ⋆ R) m' →
        Q (p, ()) m'
    else
      ∀ st' m',
        st'.PreservesMetaExceptEnd st → st'.hdr.s_end = st.hdr.s_end →
        st'.rem = st.rem →
        (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m' →
        Q (ffiResOomWord, ()) m'

/-- Headroom predicate for `lcnf_c0_xor_nat(rt, a, key)` succeeding with `.ok`. -/
@[expose] def pilotXorNatOk (st : RtC0State) (len : Nat) : Prop :=
  len ≤ ffiNatMaxBytes ∧
  if len = 0 then
    natSAllocBytes 0 + 16 ≤ st.rem
  else
    ffiCarveOk st (BitVec.ofNat 64 len) ∧
    natSAllocBytes len + 16 ≤
      (ffiCarveWend st.hdr.s_end).toNat - ffiCarveWcap (BitVec.ofNat 64 len) - st.hdr.s_cur.toNat

instance instDecidablePilotXorNatOk (st : RtC0State) (len : Nat) :
    Decidable (pilotXorNatOk st len) := by
  unfold pilotXorNatOk
  infer_instance

/-- Specification for `lcnf_c0_xor_nat(rt, a, key)`. -/
@[expose] def pilotXorNatSpec : Spec [i64, i64, i8] [i64] := fun (rt, a, key, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (val : Nat) (objs : List LcnfObj) (R : Mem 64 → Prop),
    scrLimbs.length < 2 ^ 64 ∧
    RtNatRep a val objs ∧
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    match bytesOfNatS val with
    | none => Q (ffiResInvalidInputWord, ()) m
    | some bs =>
      if (a &&& 1#64) ≠ 0#64 ∧ 0 < bs.length ∧ (scr = 0#64 ∨ scrLimbs.length = 0) then
        Q (ffiResOomWord, ()) m
      else
        ((a &&& 1#64) ≠ 0#64 → scr.toNat + 8 < 2 ^ 64) ∧
        ((a &&& 1#64) = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64) ∧
        let outNat := natOfBytesS (bs.map (· ^^^ UInt8.ofNat key.toNat))
        if pilotXorNatOk st bs.length then
          if bs.length ≤ 7 then
            ∀ p st' scrLimbs' m',
              p ≠ 0#64 → p.toNat % 8 = 0 →
              scrLimbs'.length = scrLimbs.length →
              st'.PreservesMetaExceptEnd st → st'.hdr.s_end = st.hdr.s_end →
              st'.rem ≤ st.rem → st.rem - 16 ≤ st'.rem →
              FfiResOkCanon (mkFfiResOkObj p (boxNat outNat)) (boxNat outNat) →
              (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p (boxNat outNat)) ⋆
                cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
                array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m' →
              Q (p, ()) m'
          else
            ∀ p natP st' newObj scrLimbs' m',
              p ≠ 0#64 → p.toNat % 8 = 0 →
              natP ≠ 0#64 → natP.toNat % 8 = 0 → (natP &&& 1#64) = 0#64 →
              scrLimbs'.length = scrLimbs.length →
              st'.PreservesMetaExceptEnd st → st'.hdr.s_end = st.hdr.s_end →
              st'.rem ≤ st.rem → st.rem - (natSAllocBytes bs.length + 16) ≤ st'.rem →
              RtMpzNatCanon newObj outNat → newObj.addr = natP → MpzCanon newObj →
              FfiResOkCanon (mkFfiResOkObj p natP) natP →
              (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p natP) ⋆
                lcnfObjMem newObj ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
                array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m' →
              Q (p, ()) m'
        else
          ∀ st' scrLimbs' m',
            scrLimbs'.length = scrLimbs.length →
            st'.PreservesMetaExceptEnd st → st'.hdr.s_end = st.hdr.s_end →
            st'.rem = st.rem →
            (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
              array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m' →
            Q (ffiResOomWord, ()) m'

/-! ## 2. Pilot C0 Table & Environment Composition -/

/-- Specification table for `pilotC0_fns`. -/
@[expose] def pilotC0SpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn c0_xor_bytes c0XorBytesSpec true
  , SpecEntry.ofFn lcnf_c0_kissat_raw pilotKissatRawSpec true
  , SpecEntry.ofFn lcnf_c0_kissat_solve_ba pilotKissatSolveBASpec true
  , SpecEntry.ofFn lcnf_c0_kissat_solve_nat pilotKissatSolveNatSpec true
  , SpecEntry.ofFn lcnf_c0_xor_ba pilotXorBASpec true
  , SpecEntry.ofFn lcnf_c0_xor_nat pilotXorNatSpec true
  ]

theorem pilotC0SpecEntries_nodup : (pilotC0SpecEntries.map SpecEntry.name).Nodup := by
  refine listNodup_nodup ?_
  decide

theorem pilotC0_table_of_mem {e : SpecEntry} (he : e ∈ pilotC0SpecEntries)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost} (h : e.eff xs m Q X) :
    Env.ofTable pilotC0SpecEntries e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem he pilotC0SpecEntries_nodup h

@[expose] def ffiPureMod : Module := { ffiMod with externs := [] }

/-- Core `plainModule` environment supporting both general correctness and deterministic UNSAT/SAT
witnesses. -/
@[expose] def pilotPlainEnv : Env := mkPlainEnv plainSolveBytesCoreSpec

/-- Environment covering `plainModule`, `ffiMod`, and `pilotC0_fns`. -/
@[expose] def pilotC0Env : Env := fun f as bs xs m Q X =>
  Env.ofModule plainModule pilotPlainEnv f as bs xs m Q X ∨
    Env.ofModule ffiPureMod ffiEnv f as bs xs m Q X ∨
      Env.ofTable pilotC0SpecEntries f as bs xs m Q X

/-! ## 3. Environment Lookup & Separation Helpers -/

theorem pilotC0Env_kissat_solve_bytes {xs m Q X}
    (h : plainSolveBytesCoreSpec xs m Q X) :
    pilotC0Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X := by
  refine Or.inl ⟨?_, ?_⟩
  · decide
  · exact mkPlainEnv_solve_bytes plainSolveBytesCoreSpec (fun _ _ _ _ h' => h') _ m _ X h

private theorem ffiEnv_of_mem {e : SpecEntry} (he : e ∈ ffiSpecEntries)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost} (h : e.eff xs m Q X) :
    ffiEnv e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem he ffiSpecEntries_nodup h

theorem pilotC0Env_ffi_mem {e : SpecEntry} (he : e ∈ ffiSpecEntries)
    (hm : (e.name, e.as, e.rs) ∈ ffiPureMod.sigs)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost} (h : e.eff xs m Q X) :
    pilotC0Env e.name e.as e.rs xs m Q X :=
  Or.inr (Or.inl ⟨hm, ffiEnv_of_mem he h⟩)

theorem pilotC0Env_get_end {xs m Q X}
    (h : ffiGetEndSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_get_end" [i64] [i64] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_get_end ffiGetEndSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_carve_scratch {xs m Q X}
    (h : ffiCarveScratchSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_carve_scratch" [i64, i64] [i64] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_carve_scratch ffiCarveScratchSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_restore_scratch {xs m Q X}
    (h : ffiRestoreScratchSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_restore_scratch" [i64, i64] [] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_restore_scratch ffiRestoreScratchSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_ba_ptr {xs m Q X}
    (h : ffiBaPtrSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_ba_ptr" [i64] [i64] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_ba_ptr ffiBaPtrSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_ba_len {xs m Q X}
    (h : ffiBaLenSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_ba_len" [i64] [i64] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_ba_len ffiBaLenSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_ba_wrap_ok {xs m Q X}
    (h : ffiBaWrapOkSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_ba_wrap_ok" [i64, i64, i64] [i64] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_ba_wrap_ok ffiBaWrapOkSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_nat_bytes_len {xs m Q X}
    (h : ffiNatBytesLenSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_nat_bytes_len" [i64] [i64] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_nat_bytes_len ffiNatBytesLenSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_nat_bytes_ptr {xs m Q X}
    (h : ffiNatBytesPtrSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_nat_bytes_ptr" [i64, i64] [i64] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_nat_bytes_ptr ffiNatBytesPtrSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_nat_wrap_ok {xs m Q X}
    (h : ffiNatWrapOkSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_ffi_nat_wrap_ok" [i64, i64, i64] [i64] xs m Q X :=
  pilotC0Env_ffi_mem (e := SpecEntry.ofFn lcnf_ffi_nat_wrap_ok ffiNatWrapOkSpec true)
    (by simp [ffiSpecEntries]) (by decide) h

theorem pilotC0Env_c0_xor_bytes {xs m Q X}
    (h : c0XorBytesSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "c0_xor_bytes" [i64, i64, i64, i64, i64, i64] [i64] xs m Q X :=
  Or.inr (Or.inr (pilotC0_table_of_mem
    (e := SpecEntry.ofFn c0_xor_bytes c0XorBytesSpec true) (by simp [pilotC0SpecEntries]) h))

theorem pilotC0Env_kissat_raw {xs m Q X}
    (h : pilotKissatRawSpec xs m Q (fun _ _ _ _ => False)) :
    pilotC0Env "lcnf_c0_kissat_raw" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  Or.inr (Or.inr (pilotC0_table_of_mem
    (e := SpecEntry.ofFn lcnf_c0_kissat_raw pilotKissatRawSpec true)
    (by simp [pilotC0SpecEntries]) h))

private theorem bv64_sub_max_lt_iff (a b : BitVec 64) :
    (0xffffffffffffffff#64 - b).toNat < a.toNat ↔ 2 ^ 64 ≤ b.toNat + a.toNat := by
  rw [BitVec.toNat_sub]
  have hb : b.toNat ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt b.isLt
  have h1 : ((2 ^ 64 - b.toNat) + (0xffffffffffffffff#64 : BitVec 64).toNat) % 2 ^ 64 =
      2 ^ 64 - 1 - b.toNat := by
    rw [show (0xffffffffffffffff#64 : BitVec 64).toNat = 2 ^ 64 - 1 from by decide]
    omega
  rw [h1]
  omega

private theorem bv64_add_bytes_sub_cancel (a : BitVec 64) (n : Nat) :
    a + BitVec.ofNat 64 (n + 1) = a + BitVec.ofNat 64 n + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem bv8_xor_u8_eq (b : UInt8) (k : BitVec 64) :
    UInt8.ofNat
      (((BitVec.setWidth 64 (BitVec.ofNat 8 b.toNat) ^^^ (k &&& 255#64)).setWidth 8).toNat) =
      b ^^^ UInt8.ofNat k.toNat := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp only [UInt8.toBitVec_xor, BitVec.toNat_xor, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_and]
  have hb : b.toNat < 256 := b.toNat_lt
  have hbv : b.toBitVec.toNat = b.toNat := rfl
  have hmod : (b.toNat ^^^ k.toNat % 2 ^ 8) % 2 ^ 8 = b.toNat ^^^ k.toNat % 2 ^ 8 :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hb (Nat.mod_lt k.toNat (by decide)))
  have hU : (UInt8.ofNat k.toNat).toBitVec.toNat = k.toNat % 256 := UInt8.toNat_ofNat
  rw [hbv, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_trans hb (by decide)),
    show (255 : Nat) % 2 ^ 64 = 255 from rfl, Nat.and_two_pow_sub_one_eq_mod _ 8,
    show ∀ n : Nat, (UInt8.ofNat n).toBitVec.toNat = n % 256 from fun _ => UInt8.toNat_ofNat,
    hmod, show (2 ^ 8 : Nat) = 256 from rfl]
  have hxorLt : b.toNat ^^^ k.toNat % 256 < 256 :=
    Nat.xor_lt_two_pow (n := 8) hb (Nat.mod_lt k.toNat (by decide))
  rw [Nat.mod_eq_of_lt hxorLt, hU]

@[expose] def baObjShell (baObj : LcnfObj) : Mem 64 → Prop :=
  cell64 baObj.addr baObj.header ⋆
  cell64 (baObj.addr + 8#64) (BitVec.ofNat 64 baObj.arrSize) ⋆
  cell64 (baObj.addr + 16#64) (BitVec.ofNat 64 baObj.cap) ⋆
  region (baObj.addr + BitVec.ofNat 64 (24 + baObj.scalarData.length))
    (baObj.totalBytes - (24 + baObj.scalarData.length))

theorem baObj_payload_split {baObj : LcnfObj} (hc : BaCanon baObj)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem baObj ⋆ R) m) :
    (bytes (baObj.addr + 24#64) baObj.scalarData ⋆ (baObjShell baObj ⋆ R)) m := by
  rw [lcnfObjMem_sarray_eq hc.2.2.2.2.2.1] at hm
  dsimp only [baObjShell]
  exact sep_ac hm

theorem baObj_payload_merge {baObj : LcnfObj} (hc : BaCanon baObj)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes (baObj.addr + 24#64) baObj.scalarData ⋆ (baObjShell baObj ⋆ R)) m) :
    (lcnfObjMem baObj ⋆ R) m := by
  rw [lcnfObjMem_sarray_eq hc.2.2.2.2.2.1]
  dsimp only [baObjShell] at hm
  exact sep_ac hm

@[expose] def taggedScrTail (scr : BitVec 64) (bs : List UInt8)
    (tl : List (BitVec 64)) : Mem 64 → Prop :=
  bytes (scr + BitVec.ofNat 64 bs.length) ([1] ++ List.replicate (7 - bs.length) 0) ⋆
  array64 (scr + 8#64) tl

theorem tagged_array64_split {scr : BitVec 64} {bs : List UInt8} {tl : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hle7 : bs.length ≤ 7)
    (hm : (array64 scr (BitVec.ofNat 64 (natOfBytesS bs) :: tl) ⋆ R) m) :
    (bytes scr bs ⋆ (taggedScrTail scr bs tl ⋆ R)) m := by
  rw [array64_cons, taggedNat_natOfBytesS_cell64_split scr hle7] at hm
  dsimp only [taggedScrTail]
  exact sep_ac hm

theorem tagged_array64_merge {scr : BitVec 64} {bs : List UInt8} {tl : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hle7 : bs.length ≤ 7)
    (hm : (bytes scr bs ⋆ (taggedScrTail scr bs tl ⋆ R)) m) :
    (array64 scr (BitVec.ofNat 64 (natOfBytesS bs) :: tl) ⋆ R) m := by
  rw [array64_cons, taggedNat_natOfBytesS_cell64_split scr hle7]
  dsimp only [taggedScrTail] at hm
  exact sep_ac hm

@[expose] def mpzHeapShell (objs : List LcnfObj) (idx : Nat) (a : BitVec 64)
    (obj : LcnfObj) (bs : List UInt8) : Mem 64 → Prop :=
  bytes (a + 16#64 + BitVec.ofNat 64 bs.length)
    ([1] ++ List.replicate (8 * obj.limbs.length - bs.length - 1) 0) ⋆
  cell64 a obj.header ⋆ cell64 (a + 8#64) obj.mpzMeta ⋆
  lcnfHeap (objs.take idx) ⋆ lcnfHeap (objs.drop (idx + 1))

theorem mpz_heap_split {objs : List LcnfObj} {idx : Nat} (hi : idx < objs.length)
    {obj : LcnfObj} {bs : List UInt8} {a : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hobj : objs[idx] = obj) (haddr : obj.addr = a)
    (hcanon : RtMpzNatCanon obj (natOfBytesS bs))
    (hm : (lcnfHeap objs ⋆ R) m) :
    (bytes (a + 16#64) bs ⋆ (mpzHeapShell objs idx a obj bs ⋆ R)) m := by
  rw [lcnfHeap_focus objs hi, hobj, ffi2_lcnfObjMem_mpz_eq hcanon.2.1,
    mpzNatCanon_natOfBytesS_split (obj := obj) hcanon, haddr] at hm
  dsimp only [mpzHeapShell]
  exact sep_ac hm

theorem mpz_heap_merge {objs : List LcnfObj} {idx : Nat} (hi : idx < objs.length)
    {obj : LcnfObj} {bs : List UInt8} {a : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hobj : objs[idx] = obj) (haddr : obj.addr = a)
    (hcanon : RtMpzNatCanon obj (natOfBytesS bs))
    (hm : (bytes (a + 16#64) bs ⋆ (mpzHeapShell objs idx a obj bs ⋆ R)) m) :
    (lcnfHeap objs ⋆ R) m := by
  rw [lcnfHeap_focus objs hi, hobj, ffi2_lcnfObjMem_mpz_eq hcanon.2.1,
    mpzNatCanon_natOfBytesS_split (obj := obj) hcanon, haddr]
  dsimp only [mpzHeapShell] at hm
  exact sep_ac hm

theorem restore_xor_scratch_region {wptr : BitVec 64} {len wcap : Nat}
    {outData : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : outData.length = len) (hle : len ≤ wcap) (hfit : wcap ≤ 2 ^ 64)
    (hm : (bytes wptr outData ⋆
      region (wptr + BitVec.ofNat 64 len) (wcap - len) ⋆ R) m) :
    (region wptr wcap ⋆ R) m := by
  rw [Std.ExtHashMap.sep_assoc] at hm
  have hm1 : (region wptr len ⋆
      (region (wptr + BitVec.ofNat 64 len) (wcap - len) ⋆ R)) m :=
    sep_mono (fun _ h => hlen ▸ bytes_to_region h) hm
  rw [← Std.ExtHashMap.sep_assoc,
    ← region_split (a := wptr) (n1 := len) (n2 := wcap - len) (by omega),
    show len + (wcap - len) = wcap by omega] at hm1
  exact hm1

theorem bytesOfNatS_len_le {val : Nat} {bs : List UInt8} {a : BitVec 64}
    {objs : List LcnfObj} (hrep : RtNatRep a val objs) (hbs : bytesOfNatS val = some bs) :
    bs.length ≤ ffiNatMaxBytes := by
  have hnat : natOfBytesS bs = val := natOfBytesS_of_bytesOfNatS hbs
  by_cases hsmall : val < 2 ^ 63
  · have := (natOfBytesS_lt_2p63_iff bs).mp (by rwa [hnat])
    unfold ffiNatMaxBytes; omega
  · rw [RtNatRep, ite_eq_right hsmall] at hrep
    rcases hrep with ⟨_, obj, _, _, hcanon⟩
    rw [← hnat] at hcanon
    have hlimbs := (mpzNatCanon_natOfBytesS_bytesN8 hcanon).2.1
    have hmax := hcanon.2.2.2.2.2.1
    unfold ffiMpzMaxLimbs at hmax
    unfold natSLimbCount at hlimbs
    unfold ffiNatMaxBytes
    omega

theorem ffiCarve_wend_add_tail (st : RtC0State) :
    (ffiCarveWend st.hdr.s_end).toNat +
      (st.hdr.s_end.toNat - (ffiCarveWend st.hdr.s_end).toNat) =
      st.hdr.s_end.toNat := by
  have := (ffiCarveWend_props st.hdr.s_end).1; omega

theorem ffiCarve_wptr_add_wcap {st : RtC0State} {req : BitVec 64}
    (hok : ffiCarveOk st req) :
    (ffiCarveWptr st req).toNat + ffiCarveWcap req = (ffiCarveWend st.hdr.s_end).toNat := by
  have h1 := (ffiCarveWptr_props hok).2.2.2.1
  have h2 := Nat.le_trans hok.2.2.2 (Nat.sub_le _ _)
  omega

theorem ffiCarve_rem_reclaim {st : RtC0State} {req : BitVec 64}
    (hok : ffiCarveOk st req) :
    (st.withEnd (ffiCarveWptr st req) (ffiCarveWptr_props hok).2.2.2.2.1).rem +
      ffiCarveWcap req + (st.hdr.s_end.toNat - (ffiCarveWend st.hdr.s_end).toNat) =
      st.rem := by
  change (ffiCarveWptr st req).toNat - st.hdr.s_cur.toNat +
      ffiCarveWcap req + (st.hdr.s_end.toNat - (ffiCarveWend st.hdr.s_end).toNat) =
    st.hdr.s_end.toNat - st.hdr.s_cur.toNat
  have h1 := ffiCarve_wptr_add_wcap hok
  have h2 := ffiCarve_wend_add_tail st
  have h3 := (ffiCarveWptr_props hok).2.2.2.2.1
  omega

/-! ## 4. Kernel WP Proof (`c0_xor_bytes`) -/

private theorem bv64_jnz_sub_lt_false {a b : BitVec 64}
    (h : (0xffffffffffffffff#64 - b).ult a = false) :
    b.toNat + a.toNat < 2 ^ 64 := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, bv64_sub_max_lt_iff] at h
  omega

private theorem bv64_jnz_sub_lt_true {a b : BitVec 64} (hfit : b.toNat + a.toNat < 2 ^ 64)
    (h : (0xffffffffffffffff#64 - b).ult a = true) : False := by
  rw [BitVec.ult_eq_decide, decide_eq_true_iff, bv64_sub_max_lt_iff] at h
  omega

theorem c0_xor_bytes_wp :
    ∀ xs m Q X, c0XorBytesSpec xs m Q X →
      Func.wp pilotC0Env c0_xor_bytes.body xs m Q X := by
  intro ⟨inPtr, inLen, outPtr, outCap, keyU8, flags, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, c0_xor_bytes, c0_xor_bytes_body, c0XorBytesSpec] at hPre ⊢
  by_cases hfl : flags ≠ 0#64
  · rw [ite_eq_left hfl] at hPre
    p0_split
    · p0_straight; exact hPre
    · p0_straight; exact absurd hc hfl
  · rw [ite_eq_right hfl] at hPre
    have hfl0 : flags = 0#64 := Classical.not_not.mp hfl
    by_cases hbad : inLen.toNat > 0x00ffffffffffffff ∨ inLen.toNat > outCap.toNat ∨
        inPtr.toNat + inLen.toNat ≥ 2 ^ 64 ∨ outPtr.toNat + outCap.toNat ≥ 2 ^ 64
    · rw [ite_eq_left hbad] at hPre
      p0_split
      · p0_straight; exact absurd hfl0 hc
      · p0_split
        · p0_straight; exact hPre
        · have h1 : inLen.toNat ≤ 0x00ffffffffffffff := Nat.le_of_not_lt hc
          p0_split
          · p0_straight; exact hPre
          · have h2 : inLen.toNat ≤ outCap.toNat := Nat.le_of_not_lt hc
            p0_straight
            refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
            · intro _; p0_straight; exact hPre
            · intro hlt3
              dsimp only [Arg.val] at hlt3
              have h3 : inPtr.toNat + inLen.toNat < 2 ^ 64 := bv64_jnz_sub_lt_false hlt3
              p0_straight
              refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
              · intro _; p0_straight; exact hPre
              · intro hlt4
                dsimp only [Arg.val] at hlt4
                have h4 : outPtr.toNat + outCap.toNat < 2 ^ 64 := bv64_jnz_sub_lt_false hlt4
                p0_straight
                rcases hbad with h | h | h | h
                · exact absurd h1 (Nat.not_le_of_lt h)
                · exact absurd h2 (Nat.not_le_of_lt h)
                · exact absurd h3 (Nat.not_lt_of_ge h)
                · exact absurd h4 (Nat.not_lt_of_ge h)
    · rw [ite_eq_right hbad] at hPre
      rcases hPre with ⟨inData, R, hlen, hm, hPost⟩
      have hmax : inLen.toNat ≤ 0x00ffffffffffffff := by omega
      have hcap : inLen.toNat ≤ outCap.toNat := by omega
      have hinFit : inPtr.toNat + inLen.toNat < 2 ^ 64 := by omega
      have houtFit : outPtr.toNat + outCap.toNat < 2 ^ 64 := by omega
      p0_split
      · p0_straight; exact absurd hfl0 hc
      · p0_split
        · p0_straight; exact absurd hc (Nat.not_lt_of_ge hmax)
        · p0_split
          · p0_straight; exact absurd hc (Nat.not_lt_of_ge hcap)
          · p0_straight
            refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
            · intro hlt3
              dsimp only [Arg.val] at hlt3
              exact absurd hlt3 (fun h => bv64_jnz_sub_lt_true hinFit h)
            · intro _
              p0_straight
              refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
              · intro hlt4
                dsimp only [Arg.val] at hlt4
                exact absurd hlt4 (fun h => bv64_jnz_sub_lt_true houtFit h)
              · intro _
                p0_straight
                refine wp_while_state1 (t := i64)
                  (proj := fun k : Nat => BitVec.ofNat 64 k)
                  (μ := fun k : Nat => inLen.toNat - k)
                  (Inv := fun k m' => k ≤ inLen.toNat ∧
                    (bytes inPtr inData ⋆
                      bytes outPtr ((inData.take k).map (· ^^^ UInt8.ofNat keyU8.toNat)) ⋆
                      region (outPtr + BitVec.ofNat 64 k) (outCap.toNat - k) ⋆ R) m')
                  ?_ ?_
                · intro L hL
                  refine hL 0 m ⟨Nat.zero_le _, ?_⟩
                  rw [List.take_zero, List.map_nil, bytes_nil_eq, Std.ExtHashMap.sep_emp]
                  exact sep_ac hm
                · intro L k m' ⟨hkLe, hmInv⟩ ih
                  p0_split
                  · p0_straight
                    have hkLt : k < inLen.toNat := by
                      rwa [Nat.mod_eq_of_lt (by omega)] at hc
                    have hltSrc : k < inData.length := by omega
                    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
                    let v : BitVec 8 := (BitVec.setWidth 64 (BitVec.ofNat 8 inData[k].toNat) ^^^
                      (keyU8 &&& 255#64)).setWidth 8
                    have hmReg : (region (outPtr + BitVec.ofNat 64 k) (outCap.toNat - k) ⋆
                        (bytes inPtr inData ⋆
                          bytes outPtr ((inData.take k).map (· ^^^ UInt8.ofNat keyU8.toNat)) ⋆
                            R)) m' :=
                      sep_ac hmInv
                    obtain ⟨hstOk, hstMem⟩ := region_pop_store_byte v
                      (by omega : 0 < outCap.toNat - k) (by omega : outCap.toNat - k ≤ 2 ^ 64)
                      hmReg
                    change LeanQbe.T.wp _ _ _ _ _
                    refine wp_store_sep (⟨hstOk, hstMem⟩ :
                      storeOk m' i8 (outPtr + BitVec.ofNat 64 k) ∧ _) ?_
                    intro mNext hmNext
                    p0_straight
                    have hadd1 : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
                      apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                        show (1 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
                    have htake : inData.take (k + 1) = inData.take k ++ [inData[k]] := by
                      rw [List.take_add_one, List.getElem?_eq_getElem hltSrc, Option.toList_some]
                    have hbyteEq : UInt8.ofNat v.toNat = inData[k] ^^^ UInt8.ofNat keyU8.toNat :=
                      bv8_xor_u8_eq inData[k] keyU8
                    have hlenMap : ((inData.take k).map (· ^^^ UInt8.ofNat keyU8.toNat)).length =
                        k := by
                      rw [List.length_map, List.length_take_of_le (by omega)]
                    have hfitJoin : ((inData.take k).map (· ^^^ UInt8.ofNat keyU8.toNat)).length +
                        [UInt8.ofNat v.toNat].length ≤ 2 ^ 64 := by
                      rw [List.length_singleton, hlenMap]; omega
                    have hjoin : (bytes outPtr ((inData.take k).map
                        (· ^^^ UInt8.ofNat keyU8.toNat)) ⋆
                        bytes (outPtr + BitVec.ofNat 64 k) [UInt8.ofNat v.toNat]) =
                        bytes outPtr ((inData.take (k + 1)).map
                          (· ^^^ UInt8.ofNat keyU8.toNat)) := by
                      have h := (bytes_append outPtr
                        ((inData.take k).map (· ^^^ UInt8.ofNat keyU8.toNat))
                        [UInt8.ofNat v.toNat] hfitJoin).symm
                      rw [hlenMap] at h
                      rw [htake, List.map_append, List.map_singleton, ← hbyteEq]
                      exact h
                    have hmStep : (bytes inPtr inData ⋆
                        bytes outPtr ((inData.take (k + 1)).map (· ^^^ UInt8.ofNat keyU8.toNat)) ⋆
                        region (outPtr + BitVec.ofNat 64 (k + 1))
                          (outCap.toNat - (k + 1)) ⋆ R) mNext := by
                      have hsub : outCap.toNat - (k + 1) = outCap.toNat - k - 1 := by omega
                      have hmA : ((bytes outPtr ((inData.take k).map
                          (· ^^^ UInt8.ofNat keyU8.toNat)) ⋆
                          bytes (outPtr + BitVec.ofNat 64 k) [UInt8.ofNat v.toNat]) ⋆
                          bytes inPtr inData ⋆
                          region (outPtr + BitVec.ofNat 64 (k + 1))
                            (outCap.toNat - (k + 1)) ⋆ R) mNext := by
                        rw [bv64_add_bytes_sub_cancel, hsub]
                        exact sep_ac hmNext
                      rw [hjoin] at hmA
                      exact sep_ac hmA
                    rw [hadd1]
                    exact ih (k + 1) mNext (by omega) ⟨by omega, hmStep⟩
                  · p0_straight
                    have hkEq : k = inLen.toNat := by
                      rw [Nat.mod_eq_of_lt (by omega)] at hc
                      omega
                    subst hkEq
                    rw [← hlen, List.take_length] at hmInv
                    have hlenBv : BitVec.ofNat 64 inData.length = inLen := by
                      rw [hlen]
                      exact BitVec.eq_of_toNat_eq (by
                        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inLen.isLt])
                    rw [hlenBv, hlen] at hmInv
                    exact hPost m' (sep_ac hmInv)

/-! ## 5. Kissat Wrapper WP Proofs (`raw`, `solve_ba`, `solve_nat`) -/

theorem lcnf_c0_kissat_raw_wp :
    ∀ xs m Q X, pilotKissatRawSpec xs m Q X →
      Func.wp pilotC0Env lcnf_c0_kissat_raw.body xs m Q X := by
  intro ⟨rt, cnfPtr, cnfLen, workReq, fuel, ⟨⟩⟩ m Q X
    ⟨st, cnfBytes, R, hcl, hcfit, hm, hPost⟩
  dsimp only [Func.wp, lcnf_c0_kissat_raw, lcnf_c0_kissat_raw_body]
  by_cases hvalid : workReq = 0#64 ∨ 2 ^ 64 - 8 < workReq.toNat
  · have hnotOk : ¬ ffiCarveOk st workReq := fun h => by
      rcases hvalid with h0 | hhi
      · exact h.1 h0
      · have := h.2.1; omega
    rw [ite_eq_right hnotOk] at hPost
    p0_steps <;> first
      | exact hPost
      | (exfalso
         have hne0 : workReq ≠ 0#64 := by assumption
         have hle : ¬ ((18446744073709551608 : BitVec 64).toNat < workReq.toNat) := by assumption
         rw [show (18446744073709551608 : BitVec 64).toNat = 2 ^ 64 - 8 from by decide] at hle
         rcases hvalid with h0 | hhi
         · exact hne0 h0
         · omega)
  · have hnz : workReq ≠ 0#64 := fun h => hvalid (Or.inl h)
    have hhi : workReq.toNat ≤ 2 ^ 64 - 8 := by omega
    have hwcapBv := ffiCarveWcap_bv_eq hhi
    p0_steps <;> first
      | (exfalso; exact hnz (by assumption))
      | (exfalso
         have hgt : (18446744073709551608 : BitVec 64).toNat < workReq.toNat := by assumption
         rw [show (18446744073709551608 : BitVec 64).toNat = 2 ^ 64 - 8 from by decide] at hgt
         omega)
      | (p0_call pilotC0Env_get_end
         dsimp only [ffiGetEndSpec, vals, Tup.map, Arg.val]
         refine ⟨st, bytes cnfPtr cnfBytes ⋆ R, sep_ac hm, ?_⟩
         p0_steps
         p0_call pilotC0Env_carve_scratch
         dsimp only [ffiCarveScratchSpec, vals, Tup.map, Arg.val]
         refine ⟨st, bytes cnfPtr cnfBytes ⋆ R, sep_ac hm, ?_⟩
         by_cases hok : ffiCarveOk st workReq
         · rw [dite_eq_left hok]
           rw [ite_eq_left hok] at hPost
           intro m1 hwptrNz hwptrMod hwcapGe hpresEnd hmidEnd hm1
           have hwprops := ffiCarveWptr_props hok
           let wptr := ffiCarveWptr st workReq
           let wend := ffiCarveWend st.hdr.s_end
           let wcap := ffiCarveWcap workReq
           let tailPad := st.hdr.s_end.toNat - wend.toNat
           let stCarved := st.withEnd wptr hwprops.2.2.2.2.1
           have hwfit : wptr.toNat + wcap < 2 ^ 64 := by
             have hsum := ffiCarve_wptr_add_wcap hok
             have := (ffiCarveWend st.hdr.s_end).isLt
             change wptr.toNat + wcap = (ffiCarveWend st.hdr.s_end).toNat at hsum
             omega
           p0_steps <;> first
             | (exfalso; exact hwptrNz (by assumption))
             | (rw [show (7 : BitVec 64) = 7#64 from rfl,
                  show (18446744073709551608 : BitVec 64) = 0xfffffffffffffff8#64 from rfl, hwcapBv]
                p0_call pilotC0Env_kissat_solve_bytes
                dsimp only [plainSolveBytesCoreSpec, vals, Tup.map, Arg.val]
                refine ⟨cnfBytes, wcap,
                  rtC0Inv rt stCarved ⋆ region wend tailPad ⋆ R,
                  hcl, rfl, hcfit, hwfit, sep_ac hm1, fun r m2 hr hu hs hunsW hsatW hm2 => ?_⟩
                p0_steps
                p0_call pilotC0Env_restore_scratch
                dsimp only [ffiRestoreScratchSpec, vals, Tup.map, Arg.val]
                have hm2' : (rtC0Inv rt stCarved ⋆ region wptr wcap ⋆
                    region wend tailPad ⋆ bytes cnfPtr cnfBytes ⋆ R) m2 := by
                  dsimp only [wptr] at hm2 ⊢
                  exact sep_ac hm2
                refine ⟨stCarved, wptr, wend, wcap, tailPad,
                  bytes cnfPtr cnfBytes ⋆ R, hmidEnd, hwprops.2.2.2.2.2.2.2.2,
                  ffiCarve_wptr_add_wcap hok, ffiCarve_wend_add_tail st,
                  sep_ac hm2', fun stRestored m3 hpresR hendR hremR hm3 => ?_⟩
                p0_steps
                have hremEq : stRestored.rem = st.rem := by
                  rw [hremR]; exact ffiCarve_rem_reclaim hok
                exact hPost r stRestored m3 hr hu hs hunsW hsatW
                  (hpresEnd.trans hpresR) hendR hremEq
                  (sep_ac hm3))
         · rw [dite_eq_right hok]
           rw [ite_eq_right hok] at hPost
           p0_steps <;> first
             | exact hPost
             | (exfalso; exact ‹(0#64 : BitVec 64) ≠ 0#64› rfl))

theorem lcnf_c0_kissat_solve_ba_wp :
    ∀ xs m Q X, pilotKissatSolveBASpec xs m Q X →
      Func.wp pilotC0Env lcnf_c0_kissat_solve_ba.body xs m Q X := by
  intro ⟨rt, ba, workReq, fuel, ⟨⟩⟩ m Q X
    ⟨st, baObj, R, haddr, hcanon, hm, hPost⟩
  dsimp only [Func.wp, lcnf_c0_kissat_solve_ba, lcnf_c0_kissat_solve_ba_body]
  subst haddr
  have hlenMax : baObj.scalarData.length ≤ ffiBaMaxCap := by
    have h1 := hcanon.2.2.2.2.2.2.1
    have h2 := hcanon.2.2.2.2.2.2.2.1
    have h3 := hcanon.2.2.2.2.2.2.2.2
    unfold baMaxCap at h3; unfold ffiBaMaxCap; omega
  have hlenToNat : (BitVec.ofNat 64 baObj.scalarData.length).toNat = baObj.scalarData.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold ffiBaMaxCap at hlenMax; omega)]
  p0_steps
  p0_call pilotC0Env_ba_len
  dsimp only [ffiBaLenSpec, vals, Tup.map, Arg.val]
  refine ⟨baObj, rtC0Inv rt st ⋆ R, rfl, hcanon, sep_ac hm, ?_⟩
  p0_straight
  refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
  · intro hlt24
    dsimp only [Arg.val] at hlt24
    have hsub24 : ((18446744073709551615 : BitVec 64) - 24).toNat = 2 ^ 64 - 25 := by decide
    rw [BitVec.ult_eq_decide, decide_eq_true_iff, hsub24] at hlt24
    have hbad : ¬ (baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64 ∧
        ffiCarveOk st workReq) := fun h => by omega
    rw [ite_eq_right hbad] at hPost
    p0_straight
    exact hPost
  · intro hge24f
    dsimp only [Arg.val] at hge24f
    have hsub24 : ((18446744073709551615 : BitVec 64) - 24).toNat = 2 ^ 64 - 25 := by decide
    rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub24] at hge24f
    have h24Fit : baObj.addr.toNat + 24 < 2 ^ 64 := by omega
    p0_straight
    p0_call pilotC0Env_ba_ptr
    dsimp only [ffiBaPtrSpec, vals, Tup.map, Arg.val]
    have hptrNat : (baObj.addr + 24#64).toNat = baObj.addr.toNat + 24 := by
      rw [BitVec.toNat_add, show (24#64 : BitVec 64).toNat = 24 from rfl,
        Nat.mod_eq_of_lt h24Fit]
    p0_straight
    refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
    · intro hltLen
      dsimp only [Arg.val] at hltLen
      change (0xffffffffffffffff#64 - (baObj.addr + 24#64)).ult
        (BitVec.ofNat 64 baObj.scalarData.length) = true at hltLen
      rw [BitVec.ult_eq_decide, decide_eq_true_iff, bv64_sub_max_lt_iff] at hltLen
      rw [hptrNat, hlenToNat] at hltLen
      have hbad : ¬ (baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64 ∧
          ffiCarveOk st workReq) := fun h => by omega
      rw [ite_eq_right hbad] at hPost
      p0_straight
      exact hPost
    · intro hlenf
      dsimp only [Arg.val] at hlenf
      change (0xffffffffffffffff#64 - (baObj.addr + 24#64)).ult
        (BitVec.ofNat 64 baObj.scalarData.length) = false at hlenf
      have hptrLenFit : (baObj.addr + 24#64).toNat +
          (BitVec.ofNat 64 baObj.scalarData.length).toNat < 2 ^ 64 :=
        bv64_jnz_sub_lt_false hlenf
      have h24 : (baObj.addr + 24#64).toNat + baObj.scalarData.length < 2 ^ 64 := by
        rwa [hlenToNat] at hptrLenFit
      have hfitAll : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64 := by
        rwa [hptrNat] at h24
      p0_straight
      p0_call pilotC0Env_kissat_raw
      dsimp only [pilotKissatRawSpec, vals, Tup.map, Arg.val]
      have hm0 : (lcnfObjMem baObj ⋆ (rtC0Inv rt st ⋆ R)) m := sep_ac hm
      have hm1 := baObj_payload_split hcanon hm0
      refine ⟨st, baObj.scalarData, baObjShell baObj ⋆ R, rfl, h24, sep_ac hm1, ?_⟩
      by_cases hok : ffiCarveOk st workReq
      · rw [ite_eq_left hok]
        rw [ite_eq_left ⟨hfitAll, hok⟩] at hPost
        intro r st' m' hr hu hs hunsW hsatW hpres hend hrem hm'
        have hm'0 : (bytes (baObj.addr + 24#64) baObj.scalarData ⋆
            (baObjShell baObj ⋆ (rtC0Inv rt st' ⋆ R))) m' := sep_ac hm'
        exact hPost r st' m' hr hu hs hunsW hsatW hpres hend hrem
          (sep_ac (baObj_payload_merge hcanon hm'0))
      · rw [ite_eq_right hok]
        rw [ite_eq_right (fun h => hok h.2)] at hPost
        exact hPost

theorem lcnf_c0_kissat_solve_nat_wp :
    ∀ xs m Q X, pilotKissatSolveNatSpec xs m Q X →
      Func.wp pilotC0Env lcnf_c0_kissat_solve_nat.body xs m Q X := by
  intro ⟨rt, a, workReq, fuel, ⟨⟩⟩ m Q X
    ⟨st, scr, scrLimbs, val, objs, R, hscrLt, hrep, hm, hPost⟩
  dsimp only [Func.wp, lcnf_c0_kissat_solve_nat, lcnf_c0_kissat_solve_nat_body]
  p0_steps
  p0_call pilotC0Env_nat_bytes_len
  dsimp only [ffiNatBytesLenSpec, vals, Tup.map, Arg.val]
  refine ⟨val, objs, rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆ array64 scr scrLimbs ⋆ R,
    hrep, sep_ac hm, ?_⟩
  cases hbs : bytesOfNatS val with
  | none =>
    rw [hbs] at hPost
    dsimp only at hPost ⊢
    p0_steps <;> first
      | exact hPost
      | (exfalso; exact ‹ffiInvalidLen ≠ 18446744073709551615#64› rfl)
  | some bs =>
    rw [hbs] at hPost
    dsimp only at hPost ⊢
    have hbsMax := bytesOfNatS_len_le hrep hbs
    have hbsNeInv : BitVec.ofNat 64 bs.length ≠ 18446744073709551615#64 := fun h => by
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold ffiNatMaxBytes at hbsMax; omega),
        show (18446744073709551615#64 : BitVec 64).toNat = 2 ^ 64 - 1 from by decide] at hn
      unfold ffiNatMaxBytes at hbsMax; omega
    p0_steps <;> first
      | (exfalso; exact hbsNeInv (by assumption))
      | (p0_call pilotC0Env_nat_bytes_ptr
         dsimp only [ffiNatBytesPtrSpec, vals, Tup.map, Arg.val]
         by_cases hodd : (a &&& 1#64) ≠ 0#64
         · rw [ite_eq_left hodd]
           refine ⟨scr, scrLimbs, rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R, hscrLt, sep_ac hm, ?_⟩
           by_cases hnoScr : scr = 0#64 ∨ scrLimbs.length = 0
           · rw [ite_eq_left hnoScr]
             rw [ite_eq_left ⟨hodd, hnoScr⟩] at hPost
             p0_steps <;> first
               | exact hPost
               | (exfalso; exact ‹(0#64 : BitVec 64) ≠ 0#64› rfl)
           · rw [ite_eq_right hnoScr]
             rw [ite_eq_right (fun ⟨_, h⟩ => hnoScr h)] at hPost
             rcases hPost with ⟨hscrFit, _, hRawPost⟩
             have hscrNe : scr ≠ 0#64 := fun h => hnoScr (Or.inl h)
             have hscrPos : 0 < scrLimbs.length := Nat.pos_of_ne_zero fun h => hnoScr (Or.inr h)
             have hnatEq : natOfBytesS bs = val := natOfBytesS_of_bytesOfNatS hbs
             have hvalSmall : val < 2 ^ 63 := Nat.lt_of_not_le fun hbig => by
               rw [RtNatRep, ite_eq_right (Nat.not_lt_of_ge hbig)] at hrep
               exact hodd hrep.1
             have hle7 : bs.length ≤ 7 := (natOfBytesS_lt_2p63_iff bs).mp (by rwa [hnatEq])
             have haEq : a = BitVec.ofNat 64 (2 * val + 1) := by
               simpa [RtNatRep, hvalSmall] using hrep
             have hash : (a >>> 1) = BitVec.ofNat 64 (natOfBytesS bs) := by
               rw [haEq, hnatEq]
               apply BitVec.eq_of_toNat_eq
               have hlt : 2 * val + 1 < 2 ^ 64 := by
                 have := natOfBytesS_lt_2p63 hle7; omega
               have hv : val < 2 ^ 64 := by have := natOfBytesS_lt_2p63 hle7; omega
               rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                 Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow, Nat.pow_one,
                 Nat.mod_eq_of_lt hv]
               omega
             intro m1 hm1
             let scrLimbs' := scrLimbs.set 0 (a >>> 1)
             have hlenSet : scrLimbs'.length = scrLimbs.length := List.length_set
             have hsplitCons : scrLimbs' = (a >>> 1) :: scrLimbs'.tail := by
               cases hL : scrLimbs with
               | nil => simp [hL] at hscrPos
               | cons hd tl => simp [scrLimbs', hL]
             p0_steps <;> first
               | (exfalso; exact hscrNe (by assumption))
               | (p0_call pilotC0Env_kissat_raw
                  dsimp only [pilotKissatRawSpec, vals, Tup.map, Arg.val]
                  let scrMeta := cell64 (rt + 33672#64) scr ⋆
                    cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length)
                  let restFrame := scrMeta ⋆ lcnfHeap objs ⋆ R
                  have hm1A : (array64 scr (BitVec.ofNat 64 (natOfBytesS bs) :: scrLimbs'.tail) ⋆
                      (rtC0Inv rt st ⋆ restFrame)) m1 := by
                    rw [← hash, ← hsplitCons]
                    dsimp only [restFrame, scrMeta]
                    exact sep_ac hm1
                  have hm1Split : (rtC0Inv rt st ⋆ bytes scr bs ⋆
                      (taggedScrTail scr bs scrLimbs'.tail ⋆ restFrame)) m1 :=
                    sep_ac (tagged_array64_split hle7 hm1A)
                  refine ⟨st, bs, taggedScrTail scr bs scrLimbs'.tail ⋆ restFrame, rfl,
                    by have := hscrFit hodd; omega, hm1Split, ?_⟩
                  by_cases hok : ffiCarveOk st workReq
                  · rw [ite_eq_left hok] at hRawPost ⊢
                    intro r st' m2 hr hu hs hunsW hsatW hpres hend hrem hm2
                    have hm2Arr := tagged_array64_merge hle7
                      (R := rtC0Inv rt st' ⋆ restFrame) (sep_ac hm2)
                    rw [← hash, ← hsplitCons] at hm2Arr
                    have hm2Merge : (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
                        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
                        array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m2 := by
                      dsimp only [restFrame, scrMeta] at hm2Arr
                      rw [← hlenSet] at hm2Arr
                      exact sep_ac hm2Arr
                    exact hRawPost r st' scrLimbs' m2 hr hlenSet hu hs hunsW hsatW
                      hpres hend hrem hm2Merge
                  · rw [ite_eq_right hok] at hRawPost ⊢
                    have hm1Merge : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
                        array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m1 := by
                      rw [hlenSet]
                      exact sep_ac hm1
                    exact hRawPost scrLimbs' m1 hlenSet hm1Merge)
         · have heven : (a &&& 1#64) = 0#64 := Classical.not_not.mp hodd
           rw [ite_eq_right hodd]
           rw [ite_eq_right (fun ⟨h, _⟩ => hodd h)] at hPost
           rcases hPost with ⟨_, hmpzFit, hRawPost⟩
           have hbig : ¬ val < 2 ^ 63 := fun hlt => by
             have ha : a = BitVec.ofNat 64 (2 * val + 1) := by simpa [RtNatRep, hlt] using hrep
             have hand : (a &&& 1#64) = 1#64 := by
               rw [ha]
               apply BitVec.eq_of_toNat_eq
               rw [BitVec.toNat_and, BitVec.toNat_ofNat,
                 show (1#64 : BitVec 64).toNat = 1 from rfl,
                 Nat.mod_eq_of_lt (by omega : 2 * val + 1 < 2 ^ 64),
                 Nat.and_one_is_mod]
               omega
             rw [hand] at heven; exact absurd heven (by decide)
           have hrepBig := hrep
           rw [RtNatRep, ite_eq_right hbig] at hrepBig
           rcases hrepBig with ⟨_, obj, hobjMem, hobjAddr, hcanon⟩
           have hnatEq : natOfBytesS bs = val := natOfBytesS_of_bytesOfNatS hbs
           have hcanonBs : RtMpzNatCanon obj (natOfBytesS bs) := by rwa [hnatEq]
           have ha16Nz : a + 16#64 ≠ 0#64 := fun h => by
             have hf := hmpzFit heven
             have h16 := congrArg BitVec.toNat h
             rw [BitVec.toNat_add, show (16#64 : BitVec 64).toNat = 16 from rfl,
               Nat.mod_eq_of_lt (by omega : a.toNat + 16 < 2 ^ 64),
               show (0#64 : BitVec 64).toNat = 0 from rfl] at h16
             omega
           have ha16Fit : (a + 16#64).toNat + bs.length < 2 ^ 64 := by
             have hf := hmpzFit heven
             rw [BitVec.toNat_add, show (16#64 : BitVec 64).toNat = 16 from rfl,
               Nat.mod_eq_of_lt (by omega : a.toNat + 16 < 2 ^ 64)]
             exact hf
           obtain ⟨idx, hidx, hobjEq⟩ := List.mem_iff_getElem.mp hobjMem
           p0_steps <;> first
             | (exfalso; exact ha16Nz (by assumption))
             | (p0_call pilotC0Env_kissat_raw
                dsimp only [pilotKissatRawSpec, vals, Tup.map, Arg.val]
                let scrFull := cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  array64 scr scrLimbs
                have hm0 : (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ scrFull ⋆ R)) m := by
                  dsimp only [scrFull]; exact sep_ac hm
                have hmSplit := mpz_heap_split hidx hobjEq hobjAddr hcanonBs hm0
                refine ⟨st, bs, mpzHeapShell objs idx a obj bs ⋆ scrFull ⋆ R, rfl, ha16Fit,
                  sep_ac hmSplit, ?_⟩
                by_cases hok : ffiCarveOk st workReq
                · rw [ite_eq_left hok] at hRawPost ⊢
                  intro r st' m2 hr hu hs hunsW hsatW hpres hend hrem hm2
                  have hm2Merge := mpz_heap_merge hidx hobjEq hobjAddr hcanonBs
                    (R := rtC0Inv rt st' ⋆ scrFull ⋆ R) (sep_ac hm2)
                  have hm2Rest : (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
                      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m2 := by
                    dsimp only [scrFull] at hm2Merge
                    exact sep_ac hm2Merge
                  exact hRawPost r st' scrLimbs m2 hr rfl hu hs hunsW hsatW
                    hpres hend hrem hm2Rest
                · rw [ite_eq_right hok] at hRawPost ⊢
                  exact hRawPost scrLimbs m rfl hm))

end

end LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
