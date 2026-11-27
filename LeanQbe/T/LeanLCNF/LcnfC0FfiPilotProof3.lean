/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiPilotProof2
import LeanQbe.T.MainLink
import LeanQbe.T.Logic.ProofKit

/-!
# Shard `F3` End-to-End Target-Generic Pilot Proofs (`LcnfC0FfiPilotProof3`)

Packages target-generic end-to-end WP proofs (`XPost := False`, `<= std3`) over the `171`-function
closed module `pilotLinkedMod` for all `5` lowered Lean pilot callers:

1. `checkSatBA` (`pilotTfs.tf_0`): UNSAT (`20#64 => ∃ cnf, parseDimacs bs = some cnf ∧ cnf.Unsat`),
   SAT (`10#64 => ∃ cnf, ... ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α`), and non-aborting OOM (`3#64`).
2. `checkSatNat` (`pilotTfs.tf_1`): sentineled `Nat` (`natOfBytesS`) covering both `L ≤ 7` tagged
   scalars via `rt->scratch[0]` and `L ≥ 8` zero-copy `MPZ` limbs, plus non-aborting OOM (`3#64`).
3. `xorBA` (`pilotTfs.tf_2`) and `xorNat` (`pilotTfs.tf_3`): functional XOR equality returning
   `FfiRes.ok(...)` and non-aborting OOM (`ffiResOomWord = 5#64`).
4. `solveXorBA` (`pilotTfs.tf_4`): round-trip XOR decode (`ByteArray`) + Kissat solve + Perceus
   `lcnf_dec_ref_cold` (`0` leaked heap objects), plus non-aborting OOM (`3#64`).
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.LcnfC0FfiPilot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain

public section

/-! ## 1. `pilotLinkedEnv` Membership, Table Lookup, & No-Exit Bridges -/

private theorem ofTable_name_mem : ∀ {tbl : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost},
    Env.ofTable tbl f as bs xs m Q X → f ∈ tbl.map SpecEntry.name
  | e :: _, f, as, bs, xs, m, Q, X, h => by
    rcases h with ⟨hcast, _⟩ | ⟨_, htail⟩
    · have hf : f = e.name := by simpa using hcast.1.symm
      rw [hf]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ofTable_name_mem htail)

private theorem ofModule_name_mem {M : Module} {Γ : Env} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hex : M.externs = []) (h : Env.ofModule M Γ f as bs xs m Q X) :
    f ∈ M.fns.map Fn.name := by
  have hs : (f, as, bs) ∈ M.sigs := h.1
  simp only [Module.sigs, hex, List.map_nil, List.append_nil] at hs
  rcases List.mem_map.mp hs with ⟨fn, hfn, hsig⟩
  have hnm : f = fn.name := (congrArg (fun p : SigEntry => p.1) hsig).symm
  rw [hnm]
  exact List.mem_map_of_mem hfn

private theorem boxNat_and_one (n : Nat) :
    (boxNat n &&& 1#64) ≠ 0#64 := by
  intro heq
  have hto := congrArg BitVec.toNat heq
  rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.and_one_is_mod] at hto
  simp only [boxNat, BitVec.toNat_ofNat] at hto
  omega

theorem pilotProgEnv_le_pilotLinkedEnv {f : Sym} {as rs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : pilotProgEnv f as rs xs m Q X) :
    pilotLinkedEnv f as rs xs m Q X :=
  Or.inr (Or.inr h)

theorem pilotProgMod_mem_pilotLinkedMod {fn : Fn} (hfn : fn ∈ pilotProgMod.fns) :
    fn ∈ pilotLinkedMod.fns := by
  dsimp only [pilotLinkedMod, pilotLinkedFns]
  exact List.mem_append_right _ hfn

theorem pilotProgEnv_checkSatBA {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : pilotKissatSolveBASpec xs m Q X) :
    pilotProgEnv pilotTfs.tf_0.toFn.name pilotTfs.tf_0.toFn.as pilotTfs.tf_0.toFn.rs
      xs m Q X :=
  Env.ofTable_of_mem (tbl := pilotProgSpecEntries)
    (e := SpecEntry.ofFn pilotTfs.tf_0.toFn pilotKissatSolveBASpec true)
    (by simp [pilotProgSpecEntries]) pilotProgSpecEntries_nodup h

theorem pilotProgEnv_checkSatNat {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : pilotKissatSolveNatSpec xs m Q X) :
    pilotProgEnv pilotTfs.tf_1.toFn.name pilotTfs.tf_1.toFn.as pilotTfs.tf_1.toFn.rs
      xs m Q X :=
  Env.ofTable_of_mem (tbl := pilotProgSpecEntries)
    (e := SpecEntry.ofFn pilotTfs.tf_1.toFn pilotKissatSolveNatSpec true)
    (by simp [pilotProgSpecEntries]) pilotProgSpecEntries_nodup h

theorem pilotProgEnv_xorBA {xs : Tup Val [i64, i64, i8]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : pilotXorBASpec xs m Q X) :
    pilotProgEnv pilotTfs.tf_2.toFn.name pilotTfs.tf_2.toFn.as pilotTfs.tf_2.toFn.rs
      xs m Q X :=
  Env.ofTable_of_mem (tbl := pilotProgSpecEntries)
    (e := SpecEntry.ofFn pilotTfs.tf_2.toFn pilotXorBASpec true)
    (by simp [pilotProgSpecEntries]) pilotProgSpecEntries_nodup h

theorem pilotProgEnv_xorNat {xs : Tup Val [i64, i64, i8]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : pilotXorNatSpec xs m Q X) :
    pilotProgEnv pilotTfs.tf_3.toFn.name pilotTfs.tf_3.toFn.as pilotTfs.tf_3.toFn.rs
      xs m Q X :=
  Env.ofTable_of_mem (tbl := pilotProgSpecEntries)
    (e := SpecEntry.ofFn pilotTfs.tf_3.toFn pilotXorNatSpec true)
    (by simp [pilotProgSpecEntries]) pilotProgSpecEntries_nodup h

theorem pilotProgEnv_solveXorBA {xs : Tup Val [i64, i64, i8, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : pilotSolveXorBASpec xs m Q X) :
    pilotProgEnv pilotTfs.tf_4.toFn.name pilotTfs.tf_4.toFn.as pilotTfs.tf_4.toFn.rs
      xs m Q X :=
  Env.ofTable_of_mem (tbl := pilotProgSpecEntries)
    (e := SpecEntry.ofFn pilotTfs.tf_4.toFn pilotSolveXorBASpec true)
    (by simp [pilotProgSpecEntries]) pilotProgSpecEntries_nodup h

theorem pilotLinkedEnv_noExit_prog {f : Fn} (hf : f ∈ pilotProgMod.fns)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X1 X2 : XPost}
    (h : pilotLinkedEnv f.name f.as f.rs xs m Q X1) :
    pilotLinkedEnv f.name f.as f.rs xs m Q X2 := by
  have hnotC0 : ∀ {xs' m' Q' X'}, ¬ pilotC0Env f.name f.as f.rs xs' m' Q' X' := by
    intro xs' m' Q' X' h0
    have hall : (pilotProgMod.fns.map Fn.name).all (fun nm =>
        !(pilotC0SpecEntries.map SpecEntry.name ++
          (plainModule.fns ++ ffiPureMod.fns).map Fn.name).contains nm) = true := by decide
    have hmem := List.all_eq_true.mp hall f.name (List.mem_map_of_mem hf)
    simp at hmem
    rcases h0 with hp | hffi | hc
    · rcases List.mem_map.mp (ofModule_name_mem rfl hp) with ⟨g, hg, heq⟩
      exact hmem.2.1 g hg heq
    · rcases List.mem_map.mp (ofModule_name_mem rfl hffi) with ⟨g, hg, heq⟩
      exact hmem.2.2 g hg heq
    · rcases List.mem_map.mp (ofTable_name_mem hc) with ⟨g, hg, heq⟩
      exact hmem.1 g hg heq
  have hnotRt : ∀ {xs' m' Q' X'},
      ¬ Env.ofModule rtC0CoreMod rtC0CoreEnv f.name f.as f.rs xs' m' Q' X' := by
    intro xs' m' Q' X' hr
    have hall : (pilotProgMod.fns.map Fn.name).all (fun nm =>
        !(rtC0CoreMod.fns.map Fn.name).contains nm) = true := by decide
    have hmem := List.all_eq_true.mp hall f.name (List.mem_map_of_mem hf)
    simp at hmem
    rcases List.mem_map.mp (ofModule_name_mem rfl hr) with ⟨g, hg, heq⟩
    exact hmem g hg heq
  rcases h with h0 | h1 | h2
  · exact absurd h0 hnotC0
  · exact absurd h1 hnotRt
  · exact Or.inr (Or.inr (pilotProgEnv_noExit hf h2))

/-! ## 2. Target-Generic Spec Witnesses & End-to-End Pilot WP Theorems (`X := False`) -/

theorem pilotKissatSolveBASpec_unsat {rt workReq fuel : BitVec 64} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64} {mv nc i0 : Nat}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq) (hfuel : 0 < fuel.toNat)
    (hwcap : plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq)
    (hi0 : i0 ≤ baObj.scalarData.length)
    (hhdr : parseHeader baObj.scalarData = some (mv, nc, List.drop i0 baObj.scalarData))
    (htrace : UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (List.drop i0 baObj.scalarData) nc)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    pilotKissatSolveBASpec (rt, baObj.addr, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 20#64 ∧ (∃ cnf, parseDimacs baObj.scalarData = some cnf ∧ cnf.Unsat) ∧
        ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧
          st'.rem = st.rem ∧ (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, baObj, R, rfl, hcanon, hm, ?_⟩
  rw [ite_eq_left ⟨hfit, hcarve⟩]
  intro r st' m' _ hu _ huns _ hpres hsend hrem hm'
  have hr20 : r = 20#64 := huns mv nc i0 hfuel hwcap hi0 hhdr htrace
  exact ⟨hr20, hu hr20, st', hpres, hsend, hrem, hm'⟩

theorem pilotKissatSolveBASpec_sat {rt workReq fuel : BitVec 64} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    {mv nc i0 : Nat} {vals' : List (BitVec 8)} {te' : Nat}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq) (hte : te' < fuel.toNat)
    (hwcap : plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq)
    (hi0 : i0 ≤ baObj.scalarData.length)
    (hhdr : parseHeader baObj.scalarData = some (mv, nc, List.drop i0 baObj.scalarData))
    (htrace : UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0 (List.drop i0 baObj.scalarData) nc
      vals' te')
    (hall : ∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8)
    (hchk : runKissatCheckModel baObj.scalarData (List.map UInt8.ofBitVec vals') mv = true)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    pilotKissatSolveBASpec (rt, baObj.addr, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 10#64 ∧
        (∃ cnf, parseDimacs baObj.scalarData = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧
          st'.rem = st.rem ∧ (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, baObj, R, rfl, hcanon, hm, ?_⟩
  rw [ite_eq_left ⟨hfit, hcarve⟩]
  intro r st' m' _ _ hs _ hsat hpres hsend hrem hm'
  have hr10 : r = 10#64 := hsat mv nc i0 vals' te' hte hwcap hi0 hhdr htrace hall hchk
  exact ⟨hr10, hs hr10, st', hpres, hsend, hrem, hm'⟩

theorem pilotKissatSolveBASpec_oom {rt workReq fuel : BitVec 64} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hno : ¬ (baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64 ∧ ffiCarveOk st workReq))
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    pilotKissatSolveBASpec (rt, baObj.addr, workReq, fuel, ()) m
      (fun (r, ()) m' => r = 3#64 ∧ m' = m) (fun _ _ _ _ => False) := by
  refine ⟨st, baObj, R, rfl, hcanon, hm, ?_⟩
  rw [ite_eq_right hno]
  exact ⟨rfl, rfl⟩

theorem pilot_checkSatBA_unsat_wp {rt workReq fuel : BitVec 64} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64} {mv nc i0 : Nat}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq) (hfuel : 0 < fuel.toNat)
    (hwcap : plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq)
    (hi0 : i0 ≤ baObj.scalarData.length)
    (hhdr : parseHeader baObj.scalarData = some (mv, nc, List.drop i0 baObj.scalarData))
    (htrace : UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (List.drop i0 baObj.scalarData) nc)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_0.toFn.body (rt, baObj.addr, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 20#64 ∧ (∃ cnf, parseDimacs baObj.scalarData = some cnf ∧ cnf.Unsat) ∧
        ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧
          st'.rem = st.rem ∧ (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_checkSatBA_wp _ _ _ _
    (pilotKissatSolveBASpec_unsat hcanon hfit hcarve hfuel hwcap hi0 hhdr htrace hm)

theorem pilot_checkSatBA_sat_wp {rt workReq fuel : BitVec 64} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    {mv nc i0 : Nat} {vals' : List (BitVec 8)} {te' : Nat}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq) (hte : te' < fuel.toNat)
    (hwcap : plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq)
    (hi0 : i0 ≤ baObj.scalarData.length)
    (hhdr : parseHeader baObj.scalarData = some (mv, nc, List.drop i0 baObj.scalarData))
    (htrace : UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0 (List.drop i0 baObj.scalarData) nc
      vals' te')
    (hall : ∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8)
    (hchk : runKissatCheckModel baObj.scalarData (List.map UInt8.ofBitVec vals') mv = true)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_0.toFn.body (rt, baObj.addr, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 10#64 ∧
        (∃ cnf, parseDimacs baObj.scalarData = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧
          st'.rem = st.rem ∧ (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_checkSatBA_wp _ _ _ _
    (pilotKissatSolveBASpec_sat hcanon hfit hcarve hte hwcap hi0 hhdr htrace hall hchk hm)

theorem pilot_checkSatBA_oom_wp {rt workReq fuel : BitVec 64} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hno : ¬ (baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64 ∧ ffiCarveOk st workReq))
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_0.toFn.body (rt, baObj.addr, workReq, fuel, ()) m
      (fun (r, ()) m' => r = 3#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  pilot_checkSatBA_wp _ _ _ _ (pilotKissatSolveBASpec_oom hcanon hno hm)

theorem pilotKissatSolveNatSpec_unsat {rt a workReq fuel scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {val : Nat} {objs : List LcnfObj}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {mv nc i0 : Nat}
    (hscrLt : scrLimbs.length < 2 ^ 64)
    (hrep : RtNatRep a val objs)
    (hbs : bytesOfNatS val = some bs)
    (hscrOk : ¬ (a &&& 1#64 ≠ 0#64 ∧ (scr = 0#64 ∨ scrLimbs.length = 0)))
    (hfitTag : a &&& 1#64 ≠ 0#64 → scr.toNat + 8 < 2 ^ 64)
    (hfitMpz : a &&& 1#64 = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq) (hfuel : 0 < fuel.toNat)
    (hwcap : plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq)
    (hi0 : i0 ≤ bs.length)
    (hhdr : parseHeader bs = some (mv, nc, List.drop i0 bs))
    (htrace : UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (List.drop i0 bs) nc)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    pilotKissatSolveNatSpec (rt, a, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 20#64 ∧ (∃ cnf, parseDimacs bs = some cnf ∧ cnf.Unsat) ∧
        ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, scr, scrLimbs, val, objs, R, hscrLt, hrep, hm, ?_⟩
  rw [hbs]
  dsimp only
  rw [ite_eq_right hscrOk]
  refine ⟨hfitTag, hfitMpz, ?_⟩
  rw [ite_eq_left hcarve]
  intro r st' scrLimbs' m' _ hlen hu _ huns _ hpres hsend hrem hm'
  have hr20 : r = 20#64 := huns mv nc i0 hfuel hwcap hi0 hhdr htrace
  exact ⟨hr20, hu hr20, st', scrLimbs', hlen, hpres, hsend, hrem, hm'⟩

theorem pilotKissatSolveNatSpec_sat {rt a workReq fuel scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {val : Nat} {objs : List LcnfObj}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    {mv nc i0 : Nat} {vals' : List (BitVec 8)} {te' : Nat}
    (hscrLt : scrLimbs.length < 2 ^ 64)
    (hrep : RtNatRep a val objs)
    (hbs : bytesOfNatS val = some bs)
    (hscrOk : ¬ (a &&& 1#64 ≠ 0#64 ∧ (scr = 0#64 ∨ scrLimbs.length = 0)))
    (hfitTag : a &&& 1#64 ≠ 0#64 → scr.toNat + 8 < 2 ^ 64)
    (hfitMpz : a &&& 1#64 = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq) (hte : te' < fuel.toNat)
    (hwcap : plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq)
    (hi0 : i0 ≤ bs.length)
    (hhdr : parseHeader bs = some (mv, nc, List.drop i0 bs))
    (htrace : UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0 (List.drop i0 bs) nc vals' te')
    (hall : ∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8)
    (hchk : runKissatCheckModel bs (List.map UInt8.ofBitVec vals') mv = true)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    pilotKissatSolveNatSpec (rt, a, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 10#64 ∧
        (∃ cnf, parseDimacs bs = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, scr, scrLimbs, val, objs, R, hscrLt, hrep, hm, ?_⟩
  rw [hbs]
  dsimp only
  rw [ite_eq_right hscrOk]
  refine ⟨hfitTag, hfitMpz, ?_⟩
  rw [ite_eq_left hcarve]
  intro r st' scrLimbs' m' _ hlen _ hs _ hsat hpres hsend hrem hm'
  have hr10 : r = 10#64 := hsat mv nc i0 vals' te' hte hwcap hi0 hhdr htrace hall hchk
  exact ⟨hr10, hs hr10, st', scrLimbs', hlen, hpres, hsend, hrem, hm'⟩

theorem pilotKissatSolveNatSpec_tagged_nonDimacs {rt workReq fuel scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64)
    (hlen7 : bs.length ≤ 7)
    (hnoDim : parseDimacs bs = none)
    (hscrNz : scr ≠ 0#64) (hscrPos : 0 < scrLimbs.length)
    (hfitTag : scr.toNat + 8 < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap [] ⋆ R) m) :
    pilotKissatSolveNatSpec (rt, boxNat (natOfBytesS bs), workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 0#64 ∧
        ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap [] ⋆ R) m')
      (fun _ _ _ _ => False) := by
  have hlt63 : natOfBytesS bs < 2 ^ 63 := natOfBytesS_lt_2p63 hlen7
  have hrep : RtNatRep (boxNat (natOfBytesS bs)) (natOfBytesS bs) [] := by
    simp only [RtNatRep, hlt63, ↓reduceIte, boxNat]
  refine ⟨st, scr, scrLimbs, natOfBytesS bs, [], R, hscrLt, hrep, hm, ?_⟩
  rw [bytesOfNatS_natOfBytesS]
  dsimp only
  have hscrOk : ¬ (boxNat (natOfBytesS bs) &&& 1#64 ≠ 0#64 ∧
      (scr = 0#64 ∨ scrLimbs.length = 0)) := by
    intro h
    rcases h.2 with rfl | h0
    · exact hscrNz rfl
    · omega
  rw [ite_eq_right hscrOk]
  have hodd := boxNat_and_one (natOfBytesS bs)
  refine ⟨fun _ => hfitTag, fun h0 => absurd h0 hodd, ?_⟩
  rw [ite_eq_left hcarve]
  intro r st' scrLimbs' m' hdom hlen hu hs _ _ hpres hsend hrem hm'
  have hr0 : r = 0#64 := by
    rcases hdom with rfl | rfl | rfl
    · rfl
    · rcases hs rfl with ⟨cnf, hc, _⟩
      rw [hnoDim] at hc
      cases hc
    · rcases hu rfl with ⟨cnf, hc, _⟩
      rw [hnoDim] at hc
      cases hc
  exact ⟨hr0, st', scrLimbs', hlen, hpres, hsend, hrem, hm'⟩

theorem pilotKissatSolveNatSpec_oom {rt a workReq fuel scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {val : Nat} {objs : List LcnfObj}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64)
    (hrep : RtNatRep a val objs)
    (hbs : bytesOfNatS val = some bs)
    (hscrOk : ¬ (a &&& 1#64 ≠ 0#64 ∧ (scr = 0#64 ∨ scrLimbs.length = 0)))
    (hfitTag : a &&& 1#64 ≠ 0#64 → scr.toNat + 8 < 2 ^ 64)
    (hfitMpz : a &&& 1#64 = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64)
    (hnoCarve : ¬ ffiCarveOk st workReq)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    pilotKissatSolveNatSpec (rt, a, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 3#64 ∧ ∃ scrLimbs' : List (BitVec 64), scrLimbs'.length = scrLimbs.length ∧
          (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, scr, scrLimbs, val, objs, R, hscrLt, hrep, hm, ?_⟩
  rw [hbs]
  dsimp only
  rw [ite_eq_right hscrOk]
  refine ⟨hfitTag, hfitMpz, ?_⟩
  rw [ite_eq_right hnoCarve]
  intro scrLimbs' m' hlen hm'
  exact ⟨rfl, scrLimbs', hlen, hm'⟩

theorem pilot_checkSatNat_unsat_wp {rt a workReq fuel scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {val : Nat} {objs : List LcnfObj}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {mv nc i0 : Nat}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hrep : RtNatRep a val objs)
    (hbs : bytesOfNatS val = some bs)
    (hscrOk : ¬ (a &&& 1#64 ≠ 0#64 ∧ (scr = 0#64 ∨ scrLimbs.length = 0)))
    (hfitTag : a &&& 1#64 ≠ 0#64 → scr.toNat + 8 < 2 ^ 64)
    (hfitMpz : a &&& 1#64 = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq) (hfuel : 0 < fuel.toNat)
    (hwcap : plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq)
    (hi0 : i0 ≤ bs.length) (hhdr : parseHeader bs = some (mv, nc, List.drop i0 bs))
    (htrace : UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (List.drop i0 bs) nc)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_1.toFn.body (rt, a, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 20#64 ∧ (∃ cnf, parseDimacs bs = some cnf ∧ cnf.Unsat) ∧
        ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_checkSatNat_wp _ _ _ _
    (pilotKissatSolveNatSpec_unsat hscrLt hrep hbs hscrOk hfitTag hfitMpz hcarve hfuel hwcap hi0
      hhdr htrace hm)

theorem pilot_checkSatNat_sat_wp {rt a workReq fuel scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {val : Nat} {objs : List LcnfObj}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    {mv nc i0 : Nat} {vals' : List (BitVec 8)} {te' : Nat}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hrep : RtNatRep a val objs)
    (hbs : bytesOfNatS val = some bs)
    (hscrOk : ¬ (a &&& 1#64 ≠ 0#64 ∧ (scr = 0#64 ∨ scrLimbs.length = 0)))
    (hfitTag : a &&& 1#64 ≠ 0#64 → scr.toNat + 8 < 2 ^ 64)
    (hfitMpz : a &&& 1#64 = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64)
    (hcarve : ffiCarveOk st workReq) (hte : te' < fuel.toNat)
    (hwcap : plainFixedBytes mv + nc * 40 + 136 + 8 ≤ ffiCarveWcap workReq)
    (hi0 : i0 ≤ bs.length) (hhdr : parseHeader bs = some (mv, nc, List.drop i0 bs))
    (htrace : UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0 (List.drop i0 bs) nc vals' te')
    (hall : ∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8)
    (hchk : runKissatCheckModel bs (List.map UInt8.ofBitVec vals') mv = true)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_1.toFn.body (rt, a, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 10#64 ∧
        (∃ cnf, parseDimacs bs = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_checkSatNat_wp _ _ _ _
    (pilotKissatSolveNatSpec_sat hscrLt hrep hbs hscrOk hfitTag hfitMpz hcarve hte hwcap hi0 hhdr
      htrace hall hchk hm)

theorem pilot_checkSatNat_tagged_wp {rt workReq fuel scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hlen7 : bs.length ≤ 7)
    (hnoDim : parseDimacs bs = none)
    (hscrNz : scr ≠ 0#64) (hscrPos : 0 < scrLimbs.length)
    (hfitTag : scr.toNat + 8 < 2 ^ 64) (hcarve : ffiCarveOk st workReq)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap [] ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_1.toFn.body
      (rt, boxNat (natOfBytesS bs), workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 0#64 ∧ ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap [] ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_checkSatNat_wp _ _ _ _
    (pilotKissatSolveNatSpec_tagged_nonDimacs hscrLt hlen7 hnoDim hscrNz hscrPos hfitTag hcarve hm)

theorem pilot_checkSatNat_oom_wp {rt a workReq fuel scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {val : Nat} {objs : List LcnfObj}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hrep : RtNatRep a val objs)
    (hbs : bytesOfNatS val = some bs)
    (hscrOk : ¬ (a &&& 1#64 ≠ 0#64 ∧ (scr = 0#64 ∨ scrLimbs.length = 0)))
    (hfitTag : a &&& 1#64 ≠ 0#64 → scr.toNat + 8 < 2 ^ 64)
    (hfitMpz : a &&& 1#64 = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64)
    (hnoCarve : ¬ ffiCarveOk st workReq)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_1.toFn.body (rt, a, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 3#64 ∧ ∃ scrLimbs' : List (BitVec 64), scrLimbs'.length = scrLimbs.length ∧
          (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_checkSatNat_wp _ _ _ _
    (pilotKissatSolveNatSpec_oom hscrLt hrep hbs hscrOk hfitTag hfitMpz hnoCarve hm)

theorem pilotXorBASpec_ok {rt : BitVec 64} {key : BitVec 8} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hok : pilotXorBaOk st baObj.scalarData.length)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    pilotXorBASpec (rt, baObj.addr, key, ()) m
      (fun (p, ()) m' =>
        let outData := List.map (fun x => x ^^^ UInt8.ofNat key.toNat) baObj.scalarData
        ∃ (baNew : BitVec 64) (st' : RtC0State),
          p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ baNew ≠ 0#64 ∧ baNew.toNat % 8 = 0 ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem ≤ st.rem ∧
          BaCanon (mkBaObj baNew 1#32 baObj.scalarData.length outData) ∧
          FfiResOkCanon (mkFfiResOkObj p baNew) baNew ∧
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p baNew) ⋆
            lcnfObjMem (mkBaObj baNew 1#32 baObj.scalarData.length outData) ⋆
            lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, baObj, R, rfl, hcanon, hfit, hm, ?_⟩
  rw [ite_eq_left hok]
  dsimp only
  intro p baNew st' m' hp0 hp8 hba0 hba8 hpres hsend hrem _ hnew hokC hm'
  exact ⟨baNew, st', hp0, hp8, hba0, hba8, hpres, hsend, hrem, hnew, hokC, hm'⟩

theorem pilotXorBASpec_oom {rt : BitVec 64} {key : BitVec 8} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hno : ¬ pilotXorBaOk st baObj.scalarData.length)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    pilotXorBASpec (rt, baObj.addr, key, ()) m
      (fun (r, ()) m' =>
        r = ffiResOomWord ∧ ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, baObj, R, rfl, hcanon, hfit, hm, ?_⟩
  rw [ite_eq_right hno]
  intro st' m' hpres hsend hrem hm'
  exact ⟨rfl, st', hpres, hsend, hrem, hm'⟩

theorem pilot_xorBA_ok_wp {rt : BitVec 64} {key : BitVec 8} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hok : pilotXorBaOk st baObj.scalarData.length)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_2.toFn.body (rt, baObj.addr, key, ()) m
      (fun (p, ()) m' =>
        let outData := List.map (fun x => x ^^^ UInt8.ofNat key.toNat) baObj.scalarData
        ∃ (baNew : BitVec 64) (st' : RtC0State),
          p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ baNew ≠ 0#64 ∧ baNew.toNat % 8 = 0 ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem ≤ st.rem ∧
          BaCanon (mkBaObj baNew 1#32 baObj.scalarData.length outData) ∧
          FfiResOkCanon (mkFfiResOkObj p baNew) baNew ∧
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p baNew) ⋆
            lcnfObjMem (mkBaObj baNew 1#32 baObj.scalarData.length outData) ⋆
            lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_xorBA_wp _ _ _ _ (pilotXorBASpec_ok hcanon hfit hok hm)

theorem pilot_xorBA_oom_wp {rt : BitVec 64} {key : BitVec 8} {st : RtC0State}
    {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hno : ¬ pilotXorBaOk st baObj.scalarData.length)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_2.toFn.body (rt, baObj.addr, key, ()) m
      (fun (r, ()) m' =>
        r = ffiResOomWord ∧ ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_xorBA_wp _ _ _ _ (pilotXorBASpec_oom hcanon hfit hno hm)

theorem pilotXorNatSpec_tagged_ok {rt scr : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hlen7 : bs.length ≤ 7)
    (hscrNz : scr ≠ 0#64) (hscrPos : 0 < scrLimbs.length)
    (hfitTag : scr.toNat + 8 < 2 ^ 64)
    (hok : pilotXorNatOk st bs.length)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap [] ⋆ R) m) :
    pilotXorNatSpec (rt, boxNat (natOfBytesS bs), key, ()) m
      (fun (p, ()) m' =>
        let outNat := natOfBytesS (List.map (fun x => x ^^^ UInt8.ofNat key.toNat) bs)
        ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem ≤ st.rem ∧
          FfiResOkCanon (mkFfiResOkObj p (boxNat outNat)) (boxNat outNat) ∧
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p (boxNat outNat)) ⋆
            cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap [] ⋆ R) m')
      (fun _ _ _ _ => False) := by
  have hlt63 : natOfBytesS bs < 2 ^ 63 := natOfBytesS_lt_2p63 hlen7
  have hrep : RtNatRep (boxNat (natOfBytesS bs)) (natOfBytesS bs) [] := by
    simp only [RtNatRep, hlt63, ↓reduceIte, boxNat]
  refine ⟨st, scr, scrLimbs, natOfBytesS bs, [], R, hscrLt, hrep, hm, ?_⟩
  rw [bytesOfNatS_natOfBytesS]
  dsimp only
  have hscrOk : ¬ (boxNat (natOfBytesS bs) &&& 1#64 ≠ 0#64 ∧ 0 < bs.length ∧
      (scr = 0#64 ∨ scrLimbs.length = 0)) := by
    intro h
    rcases h.2.2 with rfl | h0
    · exact hscrNz rfl
    · omega
  rw [ite_eq_right hscrOk]
  have hodd := boxNat_and_one (natOfBytesS bs)
  refine ⟨fun _ => hfitTag, fun h0 => absurd h0 hodd, ?_⟩
  rw [ite_eq_left hok, ite_eq_left hlen7]
  intro p st' scrLimbs' m' hp0 hp8 hlen hpres hsend hrem _ hokC hm'
  exact ⟨st', scrLimbs', hp0, hp8, hlen, hpres, hsend, hrem, hokC, hm'⟩

theorem pilotXorNatSpec_mpz_ok {rt a scr : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {obj : LcnfObj} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64)
    (hrep : RtNatRep a (natOfBytesS bs) [obj])
    (hge8 : 8 ≤ bs.length)
    (heven : (a &&& 1#64) = 0#64)
    (hfitMpz : a.toNat + 16 + bs.length < 2 ^ 64)
    (hok : pilotXorNatOk st bs.length)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap [obj] ⋆ R) m) :
    pilotXorNatSpec (rt, a, key, ()) m
      (fun (p, ()) m' =>
        let outNat := natOfBytesS (List.map (fun x => x ^^^ UInt8.ofNat key.toNat) bs)
        ∃ (natP : BitVec 64) (st' : RtC0State) (newObj : LcnfObj) (scrLimbs' : List (BitVec 64)),
          p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ natP ≠ 0#64 ∧ natP.toNat % 8 = 0 ∧
          natP &&& 1#64 = 0#64 ∧ scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem ≤ st.rem ∧
          RtMpzNatCanon newObj outNat ∧ newObj.addr = natP ∧ MpzCanon newObj ∧
          FfiResOkCanon (mkFfiResOkObj p natP) natP ∧
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p natP) ⋆ lcnfObjMem newObj ⋆
            cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap [obj] ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, scr, scrLimbs, natOfBytesS bs, [obj], R, hscrLt, hrep, hm, ?_⟩
  rw [bytesOfNatS_natOfBytesS]
  dsimp only
  rw [ite_eq_right (fun h => h.1 heven)]
  refine ⟨fun h => absurd heven h, fun _ => hfitMpz, ?_⟩
  rw [ite_eq_left hok, ite_eq_right (show ¬ bs.length ≤ 7 by omega)]
  intro p natP st' newObj scrLimbs' m' hp0 hp8 hnp0 hnp8 hnpe hlen hpres hsend hrem _ hc haddr
    hmpz hokC hm'
  exact ⟨natP, st', newObj, scrLimbs', hp0, hp8, hnp0, hnp8, hnpe, hlen, hpres, hsend, hrem, hc,
    haddr, hmpz, hokC, hm'⟩

theorem pilotXorNatSpec_oom {rt a scr : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {val : Nat} {objs : List LcnfObj}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hrep : RtNatRep a val objs)
    (hbs : bytesOfNatS val = some bs)
    (hscrOk : ¬ (a &&& 1#64 ≠ 0#64 ∧ 0 < bs.length ∧ (scr = 0#64 ∨ scrLimbs.length = 0)))
    (hfitTag : a &&& 1#64 ≠ 0#64 → scr.toNat + 8 < 2 ^ 64)
    (hfitMpz : a &&& 1#64 = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64)
    (hno : ¬ pilotXorNatOk st bs.length)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    pilotXorNatSpec (rt, a, key, ()) m
      (fun (r, ()) m' =>
        r = ffiResOomWord ∧ ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, scr, scrLimbs, val, objs, R, hscrLt, hrep, hm, ?_⟩
  rw [hbs]
  dsimp only
  rw [ite_eq_right hscrOk]
  refine ⟨hfitTag, hfitMpz, ?_⟩
  rw [ite_eq_right hno]
  intro st' scrLimbs' m' hlen hpres hsend hrem hm'
  exact ⟨rfl, st', scrLimbs', hlen, hpres, hsend, hrem, hm'⟩

theorem pilot_xorNat_tagged_ok_wp {rt scr : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hlen7 : bs.length ≤ 7)
    (hscrNz : scr ≠ 0#64) (hscrPos : 0 < scrLimbs.length)
    (hfitTag : scr.toNat + 8 < 2 ^ 64) (hok : pilotXorNatOk st bs.length)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap [] ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_3.toFn.body (rt, boxNat (natOfBytesS bs), key, ()) m
      (fun (p, ()) m' =>
        let outNat := natOfBytesS (List.map (fun x => x ^^^ UInt8.ofNat key.toNat) bs)
        ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem ≤ st.rem ∧
          FfiResOkCanon (mkFfiResOkObj p (boxNat outNat)) (boxNat outNat) ∧
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p (boxNat outNat)) ⋆
            cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap [] ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_xorNat_wp _ _ _ _
    (pilotXorNatSpec_tagged_ok hscrLt hlen7 hscrNz hscrPos hfitTag hok hm)

theorem pilot_xorNat_mpz_ok_wp {rt a scr : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {obj : LcnfObj} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hrep : RtNatRep a (natOfBytesS bs) [obj])
    (hge8 : 8 ≤ bs.length) (heven : (a &&& 1#64) = 0#64)
    (hfitMpz : a.toNat + 16 + bs.length < 2 ^ 64) (hok : pilotXorNatOk st bs.length)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap [obj] ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_3.toFn.body (rt, a, key, ()) m
      (fun (p, ()) m' =>
        let outNat := natOfBytesS (List.map (fun x => x ^^^ UInt8.ofNat key.toNat) bs)
        ∃ (natP : BitVec 64) (st' : RtC0State) (newObj : LcnfObj) (scrLimbs' : List (BitVec 64)),
          p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ natP ≠ 0#64 ∧ natP.toNat % 8 = 0 ∧
          natP &&& 1#64 = 0#64 ∧ scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem ≤ st.rem ∧
          RtMpzNatCanon newObj outNat ∧ newObj.addr = natP ∧ MpzCanon newObj ∧
          FfiResOkCanon (mkFfiResOkObj p natP) natP ∧
          (rtC0Inv rt st' ⋆ lcnfObjMem (mkFfiResOkObj p natP) ⋆ lcnfObjMem newObj ⋆
            cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap [obj] ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_xorNat_wp _ _ _ _ (pilotXorNatSpec_mpz_ok hscrLt hrep hge8 heven hfitMpz hok hm)

theorem pilot_xorNat_oom_wp {rt a scr : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {val : Nat} {objs : List LcnfObj}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hscrLt : scrLimbs.length < 2 ^ 64) (hrep : RtNatRep a val objs)
    (hbs : bytesOfNatS val = some bs)
    (hscrOk : ¬ (a &&& 1#64 ≠ 0#64 ∧ 0 < bs.length ∧ (scr = 0#64 ∨ scrLimbs.length = 0)))
    (hfitTag : a &&& 1#64 ≠ 0#64 → scr.toNat + 8 < 2 ^ 64)
    (hfitMpz : a &&& 1#64 = 0#64 → a.toNat + 16 + bs.length < 2 ^ 64)
    (hno : ¬ pilotXorNatOk st bs.length)
    (hm : (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_3.toFn.body (rt, a, key, ()) m
      (fun (r, ()) m' =>
        r = ffiResOomWord ∧ ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)),
          scrLimbs'.length = scrLimbs.length ∧
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧ st'.rem = st.rem ∧
          (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ lcnfHeap objs ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_xorNat_wp _ _ _ _
    (pilotXorNatSpec_oom hscrLt hrep hbs hscrOk hfitTag hfitMpz hno hm)

theorem pilotSolveXorBASpec_unsat {rt workReq fuel : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hwc : 2 ≤ st.workCap)
    (hok : pilotXorBaOk st baObj.scalarData.length)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    let outData := List.map (fun x => x ^^^ UInt8.ofNat key.toNat) baObj.scalarData
    pilotSolveXorBASpec (rt, baObj.addr, key, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 3#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs outData = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs outData = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧
          st'.rem ≤ st.rem ∧ (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, baObj, R, rfl, hcanon, hfit, hwc, hm, ?_⟩
  rw [ite_eq_left hok]
  intro r st' m' hdom hu hs hpres hsend hrem hm'
  exact ⟨hdom, hu, hs, st', hpres, hsend, hrem, hm'⟩

theorem pilotSolveXorBASpec_oom {rt workReq fuel : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hwc : 2 ≤ st.workCap)
    (hno : ¬ pilotXorBaOk st baObj.scalarData.length)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    pilotSolveXorBASpec (rt, baObj.addr, key, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 3#64 ∧ ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧
          st'.rem = st.rem ∧ (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine ⟨st, baObj, R, rfl, hcanon, hfit, hwc, hm, ?_⟩
  rw [ite_eq_right hno]
  intro st' m' hpres hsend hrem hm'
  exact ⟨rfl, st', hpres, hsend, hrem, hm'⟩

theorem pilot_solveXorBA_unsat_wp {rt workReq fuel : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hwc : 2 ≤ st.workCap) (hok : pilotXorBaOk st baObj.scalarData.length)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    let outData := List.map (fun x => x ^^^ UInt8.ofNat key.toNat) baObj.scalarData
    Func.wp pilotLinkedEnv pilotTfs.tf_4.toFn.body (rt, baObj.addr, key, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 3#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs outData = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs outData = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧
          st'.rem ≤ st.rem ∧ (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_solveXorBA_wp _ _ _ _ (pilotSolveXorBASpec_unsat hcanon hfit hwc hok hm)

theorem pilot_solveXorBA_oom_wp {rt workReq fuel : BitVec 64} {key : BitVec 8}
    {st : RtC0State} {baObj : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hcanon : BaCanon baObj)
    (hfit : baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64)
    (hwc : 2 ≤ st.workCap) (hno : ¬ pilotXorBaOk st baObj.scalarData.length)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m) :
    Func.wp pilotLinkedEnv pilotTfs.tf_4.toFn.body (rt, baObj.addr, key, workReq, fuel, ()) m
      (fun (r, ()) m' =>
        r = 3#64 ∧ ∃ st' : RtC0State,
          st'.PreservesMetaExceptEnd st ∧ st'.hdr.s_end = st.hdr.s_end ∧
          st'.rem = st.rem ∧ (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m')
      (fun _ _ _ _ => False) :=
  pilot_solveXorBA_wp _ _ _ _ (pilotSolveXorBASpec_oom hcanon hfit hwc hno hm)

end

end LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
