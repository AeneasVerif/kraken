/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiPilotProof1
public import LeanQbe.T.LeanLCNF.LcnfC0FfiProof
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.ControlComb

/-!
# Shard `F3` Pilot Lowered-Module `ModuleOk` & Per-Function WP Proofs (`LcnfC0FfiPilotProof2`)

Composes the full `171`-function closed module
`pilotLinkedMod :=`
`  plainModule (59) ++ rtC0CoreMod (86) ++ ffiMod (15) ++ pilotC0 (6) ++ pilotProg (5)`
with `0` externs (`exits := ["lcnf_panic"]`), proves `Func.wp pilotLinkedEnv` for all `5` lowered
Lean pilot functions (`checkSatBA`, `checkSatNat`, `xorBA`, `xorNat`, `solveXorBA`), and
establishes whole-module `pilotLinkedMod_moduleOk`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.LcnfC0FfiPilot

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLRC
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open scoped LeanQbe.T.ProofUtil

local macro "p2_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hfast))
local macro "p2_straight" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_hstraight))
local macro "p2_call " h:ident : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_))

public section

/-! ## 1. Composed Modules & Closed `pilotLinkedEnv` -/

/-- Canonical `26`-function pilot tail compiled per arch:
`ffiMod (15) ++ pilotC0 (6) ++ pilotProg (5)`. -/
@[expose] def pilotTailFns : List Fn :=
  ffiMod.fns ++ pilotC0_fns ++ pilotProgMod.fns

/-- Standalone tail `Module` declaring `plainModule.sigs` and `rtC0CoreMod.sigs` as externs. -/
@[expose] def pilotTailMod : Module :=
  { fns := pilotTailFns
    externs := (rtC0CoreMod.fns ++ plainModule.fns).map
      (fun f => ({ name := f.name, as := f.as, rs := f.rs } : Extern))
    exits := rtExitSyms }

/-- Canonical `171`-function linked function list (`59 + 101 + 6 + 5`). -/
@[expose] def pilotLinkedFns : List Fn :=
  plainModule.fns ++ rtC0WithFfiMod.fns ++ pilotC0_fns ++ pilotProgMod.fns

/-- Closed `171`-function verified FFI pilot `Module` (`0` externs, `exits := ["lcnf_panic"]`). -/
@[expose] def pilotLinkedMod : Module :=
  { fns := pilotLinkedFns, externs := [], exits := rtExitSyms }

theorem pilotLinkedMod_fns_tail_eq :
    pilotLinkedMod.fns = (plainModule.fns ++ rtC0CoreMod.fns) ++ pilotTailMod.fns := by
  simp only [pilotLinkedMod, pilotLinkedFns, rtC0WithFfiMod, rtC0WithFfiFns, pilotTailMod,
    pilotTailFns, List.append_assoc]

theorem pilotLinkedMod_checkAcyclic : pilotLinkedMod.checkAcyclic = true := by
  t_kernel_rfl

private theorem allFns_append {P : Fn → Prop} {xs ys : List Fn}
    (hx : ∀ f ∈ xs, P f) (hy : ∀ f ∈ ys, P f) : ∀ f ∈ xs ++ ys, P f := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact hx f h1
  · exact hy f h2

theorem pilotLinkedMod_fns_wf : ∀ f ∈ pilotLinkedMod.fns, f.Wf := by
  dsimp only [pilotLinkedMod, pilotLinkedFns]
  refine allFns_append (allFns_append (allFns_append plainFns_wf ?_) pilotC0_fns_wf)
    pilotProgMod_fns_wf
  exact rtC0WithFfiMod_allFns_wf.mem

theorem pilotProgMod_fns_eq :
    pilotProgMod.fns =
      [pilotTfs.tf_0.toFn, pilotTfs.tf_1.toFn, pilotTfs.tf_2.toFn,
       pilotTfs.tf_3.toFn, pilotTfs.tf_4.toFn] :=
  rfl

/-- End-to-end contract for `solveXorBA(rt, ba, key, workReq, fuel)`:
unpacks borrowed `ba`, XORs into a fresh temporary `ByteArray`, calls `kissat_solve_bytes`,
releases the temporary objects via Perceus `lcnf_dec_ref_cold` (`0` leaks), and handles
non-aborting OOM (`3#64`). -/
@[expose] def pilotSolveXorBASpec : Spec [i64, i64, i8, i64, i64] [i64] :=
  fun (rt, ba, key, _workReq, _fuel, ()) m Q _ =>
    ∃ (st : RtC0State) (baObj : LcnfObj) (R : Mem 64 → Prop),
      baObj.addr = ba ∧ BaCanon baObj ∧
      baObj.addr.toNat + 24 + baObj.scalarData.length < 2 ^ 64 ∧
      2 ≤ st.workCap ∧
      (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m ∧
      let len := baObj.scalarData.length
      let outData := baObj.scalarData.map (· ^^^ UInt8.ofNat key.toNat)
      if pilotXorBaOk st len then
        ∀ r st' m',
          (r = 0#64 ∨ r = 3#64 ∨ r = 10#64 ∨ r = 20#64) →
          (r = 20#64 → ∃ cnf, parseDimacs outData = some cnf ∧ cnf.Unsat) →
          (r = 10#64 → ∃ cnf, parseDimacs outData = some cnf ∧ ¬ cnf.Unsat ∧
            ∃ α, cnf.Sat α) →
          st'.PreservesMetaExceptEnd st →
          st'.hdr.s_end = st.hdr.s_end →
          st'.rem ≤ st.rem →
          (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m' →
          Q (r, ()) m'
      else
        ∀ st' m',
          st'.PreservesMetaExceptEnd st →
          st'.hdr.s_end = st.hdr.s_end →
          st'.rem = st.rem →
          (rtC0Inv rt st' ⋆ lcnfObjMem baObj ⋆ R) m' →
          Q (3#64, ()) m'

/-- Specification table for the `5` lowered Lean pilot functions (`noExit := true`). -/
@[expose] def pilotProgSpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn pilotTfs.tf_0.toFn pilotKissatSolveBASpec true
  , SpecEntry.ofFn pilotTfs.tf_1.toFn pilotKissatSolveNatSpec true
  , SpecEntry.ofFn pilotTfs.tf_2.toFn pilotXorBASpec true
  , SpecEntry.ofFn pilotTfs.tf_3.toFn pilotXorNatSpec true
  , SpecEntry.ofFn pilotTfs.tf_4.toFn pilotSolveXorBASpec true
  ]

theorem pilotProgSpecEntries_nodup : (pilotProgSpecEntries.map SpecEntry.name).Nodup := by
  refine listNodup_nodup ?_
  decide

/-- Specification environment for `pilotProgMod` (`5` lowered Lean pilot callers). -/
@[expose] def pilotProgEnv : Env := Env.ofTable pilotProgSpecEntries

/-- Closed `171`-function specification environment covering `plainModule`, `rtC0CoreMod`,
`ffiMod`, `pilotC0_module`, and `pilotProgMod`. -/
@[expose] def pilotLinkedEnv : Env := fun f as bs xs m Q X =>
  pilotC0Env f as bs xs m Q X ∨
    Env.ofModule rtC0CoreMod rtC0CoreEnv f as bs xs m Q X ∨
      Env.ofTable pilotProgSpecEntries f as bs xs m Q X

/-! ## 2. Environment Embedding & `noExit` Helpers -/

theorem pilotC0Env_le_pilotLinkedEnv :
    ∀ f as bs xs m Q X,
      pilotC0Env f as bs xs m Q X → pilotLinkedEnv f as bs xs m Q X :=
  fun _ _ _ _ _ _ _ h => Or.inl h

theorem rtC0CoreMod_env_le_pilotLinkedEnv :
    ∀ f as bs xs m Q X,
      Env.ofModule rtC0CoreMod rtC0CoreEnv f as bs xs m Q X →
      pilotLinkedEnv f as bs xs m Q X :=
  fun _ _ _ _ _ _ _ h => Or.inr (Or.inl h)

private theorem ffiEnv_ofTable_sub {tbl : List SpecEntry} {Γ' : Env}
    (h : ∀ e ∈ tbl, ∀ xs m Q X, e.eff xs m Q X → Γ' e.name e.as e.rs xs m Q X) :
    ∀ f as bs xs m Q X, Env.ofTable tbl f as bs xs m Q X → Γ' f as bs xs m Q X := by
  induction tbl with
  | nil => intro _ _ _ _ _ _ _ hf; exact hf.elim
  | cons e es ih =>
    intro f as bs xs m Q X hs
    rcases hs with ⟨⟨rfl, rfl, rfl⟩, he⟩ | ⟨_, hrest⟩
    · exact h e List.mem_cons_self xs m Q X he
    · exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')) f as bs xs m Q X hrest

theorem ffiEnv_le_pilotLinkedEnv :
    ∀ f as bs xs m Q X,
      ffiEnv f as bs xs m Q X → pilotLinkedEnv f as bs xs m Q X := by
  refine ffiEnv_ofTable_sub (fun e he xs m Q X h => ?_)
  simp only [ffiSpecEntries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by decide,
      Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩))
  · exact Or.inr (Or.inl ⟨by decide, rtC0CoreEnv_lcnf_alloc h⟩)
  · exact Or.inr (Or.inl ⟨by decide, rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _
      (rtR2Env_r2_mem_copy_bytes h)⟩)

private theorem ofTable_mem_sigs {tbl : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable tbl f as bs xs m Q X) :
    (f, as, bs) ∈ tbl.map (fun e => (e.name, e.as, e.rs)) := by
  induction tbl with
  | nil => exact h.elim
  | cons e es ih =>
    rcases h with ⟨⟨rfl, rfl, rfl⟩, _⟩ | ⟨_, hrest⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hrest)

theorem pilotPlainEnv_le_pilotLinkedEnv :
    ∀ f as bs xs m Q X,
      pilotPlainEnv f as bs xs m Q X → pilotLinkedEnv f as bs xs m Q X := by
  intro f as bs xs m Q X h
  have hsig : (f, as, bs) ∈
      (plainSpecTable plainSolveBytesCoreSpec).map (fun e => (e.name, e.as, e.rs)) :=
    ofTable_mem_sigs h
  have hmem : ∀ s ∈
      (plainSpecTable plainSolveBytesCoreSpec).map (fun e => (e.name, e.as, e.rs)),
      s ∈ plainModule.sigs := by
    dsimp only [plainSpecTable, List.map_cons, List.map_nil]
    decide
  exact Or.inl (Or.inl ⟨hmem _ hsig, h⟩)

theorem pilotLinkedEnv_kissat_solve_ba {xs m Q X}
    (h : pilotKissatSolveBASpec xs m Q X) :
    pilotLinkedEnv "lcnf_c0_kissat_solve_ba" [i64, i64, i64, i64] [i64] xs m Q X :=
  pilotC0Env_le_pilotLinkedEnv _ _ _ _ _ _ _
    (Or.inr (Or.inr (pilotC0_table_of_mem
      (e := SpecEntry.ofFn lcnf_c0_kissat_solve_ba pilotKissatSolveBASpec true)
      (by simp [pilotC0SpecEntries]) h)))

theorem pilotLinkedEnv_kissat_solve_nat {xs m Q X}
    (h : pilotKissatSolveNatSpec xs m Q X) :
    pilotLinkedEnv "lcnf_c0_kissat_solve_nat" [i64, i64, i64, i64] [i64] xs m Q X :=
  pilotC0Env_le_pilotLinkedEnv _ _ _ _ _ _ _
    (Or.inr (Or.inr (pilotC0_table_of_mem
      (e := SpecEntry.ofFn lcnf_c0_kissat_solve_nat pilotKissatSolveNatSpec true)
      (by simp [pilotC0SpecEntries]) h)))

theorem pilotLinkedEnv_xor_ba {xs m Q X}
    (h : pilotXorBASpec xs m Q X) :
    pilotLinkedEnv "lcnf_c0_xor_ba" [i64, i64, i8] [i64] xs m Q X :=
  pilotC0Env_le_pilotLinkedEnv _ _ _ _ _ _ _
    (Or.inr (Or.inr (pilotC0_table_of_mem
      (e := SpecEntry.ofFn lcnf_c0_xor_ba pilotXorBASpec true)
      (by simp [pilotC0SpecEntries]) h)))

theorem pilotLinkedEnv_xor_nat {xs m Q X}
    (h : pilotXorNatSpec xs m Q X) :
    pilotLinkedEnv "lcnf_c0_xor_nat" [i64, i64, i8] [i64] xs m Q X :=
  pilotC0Env_le_pilotLinkedEnv _ _ _ _ _ _ _
    (Or.inr (Or.inr (pilotC0_table_of_mem
      (e := SpecEntry.ofFn lcnf_c0_xor_nat pilotXorNatSpec true)
      (by simp [pilotC0SpecEntries]) h)))

theorem pilotLinkedEnv_dec_ref_cold {xs m Q X}
    (h : lcnfDecRefColdSpec xs m Q X) :
    pilotLinkedEnv "lcnf_dec_ref_cold" [i64, i64] [] xs m Q X :=
  Or.inr (Or.inl ⟨by decide, rtC0CoreEnv_lcnf_dec_ref_cold h⟩)

theorem pilotProgEnv_noExit {f : Fn} (_hf : f ∈ pilotProgMod.fns)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X1 X2 : XPost}
    (h : pilotProgEnv f.name f.as f.rs xs m Q X1) :
    pilotProgEnv f.name f.as f.rs xs m Q X2 :=
  Env.ofTable_noExit (fun e he => by
    simp only [pilotProgSpecEntries, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl) f.name f.as f.rs xs m Q X1 X2 h

theorem pilotC0_noExit {f : Fn} (_hf : f ∈ pilotC0_fns)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X1 X2 : XPost}
    (h : Env.ofTable pilotC0SpecEntries f.name f.as f.rs xs m Q X1) :
    Env.ofTable pilotC0SpecEntries f.name f.as f.rs xs m Q X2 :=
  Env.ofTable_noExit (fun e he => by
    simp only [pilotC0SpecEntries, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) f.name f.as f.rs xs m Q X1 X2 h

/-! ## 3. Separation-Logic Tag, RC-Inc, & Perceus `DecColdRel` Helpers -/

private theorem cell64_sep_self_false {p w1 w2 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 p w1 ⋆ cell64 p w2 ⋆ R) m) : False := by
  let v : BitVec 64 := if w2 = w1 + 1#64 then w1 + 2#64 else w1 + 1#64
  have hne : v ≠ w2 := by
    dsimp only [v]
    split
    · next heq =>
      intro h2
      have h12 : (w1 + 2#64).toNat = (w1 + 1#64).toNat := congrArg BitVec.toNat (h2.trans heq)
      simp only [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
        show (1#64 : BitVec 64).toNat = 1 from rfl] at h12
      omega
    · next hne1 => exact fun h2 => hne1 h2.symm
  have h' : (cell64 p w1 ⋆ (cell64 p w2 ⋆ R)) m := sep_ac h
  obtain ⟨_, hm'⟩ := @store_cell64 p w1 v (cell64 p w2 ⋆ R) m h'
  have h1 : loadVal (storeMem m i64 p v) i64 p = some v := loadVal_cell64 hm'
  have hm'' : (cell64 p w2 ⋆ (cell64 p v ⋆ R)) (storeMem m i64 p v) := sep_ac hm'
  have h2 : loadVal (storeMem m i64 p v) i64 p = some w2 := loadVal_cell64 hm''
  rw [h1] at h2
  exact hne (Option.some.inj h2)

private theorem lcnfObjMem_eq_cell64_sep (o : LcnfObj) :
    ∃ Q, lcnfObjMem o = (cell64 o.addr o.header ⋆ Q) := by
  unfold lcnfObjMem
  split
  · simp only [sep_assoc]; exact ⟨_, rfl⟩
  · split
    · simp only [sep_assoc]; exact ⟨_, rfl⟩
    · split
      · simp only [sep_assoc]; exact ⟨_, rfl⟩
      · split
        · simp only [sep_assoc]; exact ⟨_, rfl⟩
        · split
          · simp only [sep_assoc]; exact ⟨_, rfl⟩
          · simp only [sep_assoc]; exact ⟨_, rfl⟩

private theorem lcnfObjMem_load_cell64 {o : LcnfObj} (_hwf : o.Wf)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ R) m) :
    ∃ R', (cell64 o.addr o.header ⋆ R') m := by
  obtain ⟨Q, hq⟩ := lcnfObjMem_eq_cell64_sep o
  rw [hq, sep_assoc] at hm
  exact ⟨Q ⋆ R, hm⟩

private theorem ffiResOk_load_tag0 {p val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem (mkFfiResOkObj p val) ⋆ R) m) :
    loadVal m i8 (p + 7#64) = some 0#8 := by
  rw [lcnfObjMem_mkFfiResOkObj] at hm
  have hbytes : Int.toBytes 8 (ffiResOkHeader : BitVec 64).toInt =
      [1, 0, 0, 0, 16, 0, 1] ++ [0] := by
    decide
  have hcell : cell64 p ffiResOkHeader =
      (bytes p [1, 0, 0, 0, 16, 0, 1] ⋆ cell (t := i8) (p + 7#64) 0#8) := by
    have hs : Eq ((Int.toBytes 8 (ffiResOkHeader : BitVec 64).toInt).At p) =
        (Eq (([1, 0, 0, 0, 16, 0, 1] : List UInt8).At p) ⋆
          Eq (([0] : List UInt8).At (p + 7#64))) := by
      rw [hbytes]
      exact Mem.At_append_sep _ _ p (by decide)
    have h0 : cell (t := i8) (p + 7#64) 0#8 = Eq (([0] : List UInt8).At (p + 7#64)) := by
      change cell (t := i8) (p + 7#64) (BitVec.ofNat 8 (0 : UInt8).toNat) = _
      rw [← bytes_singleton_eq_cell8]
      rfl
    rw [h0]
    exact hs
  rw [hcell] at hm
  have hm' : (cell (t := i8) (p + 7#64) 0#8 ⋆
      (bytes p [1, 0, 0, 0, 16, 0, 1] ⋆ cell64 (p + 8#64) val ⋆ R)) m := sep_ac hm
  exact loadVal_cell (t := i8) (by decide) hm'

private theorem baHeaderWord2_eq :
    ∀ p cap data, (mkBaObj p 2#32 cap data).header = 0xf801000000000002#64 := by
  intro p cap data
  apply BitVec.eq_of_getLsbD_eq
  simp only [LcnfObj.header, mkBaObj, sarrayTag, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  decide

private theorem baObj_rc1_load_store_inc {p : BitVec 64} {cap : Nat} {data : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem (mkBaObj p 1#32 cap data) ⋆ R) m) :
    loadVal m i32 p = some 1#32 ∧
      storeOk m i32 p ∧
      (lcnfObjMem (mkBaObj p 2#32 cap data) ⋆ R) (storeMem m i32 p 2#32) := by
  rw [lcnfObjMem_sarray_eq rfl, mkBaObj_header] at hm
  dsimp only [mkBaObj] at hm
  have hb1 : Int.toBytes 8 (0xf801000000000001#64 : BitVec 64).toInt =
      Int.toBytes 4 ((toBits i32 (1#32 : BitVec 32)).setWidth 32).toInt ++ [0, 0, 1, 248] := by
    decide
  have hb2 : Int.toBytes 8 (0xf801000000000002#64 : BitVec 64).toInt =
      Int.toBytes 4 ((toBits i32 (2#32 : BitVec 32)).setWidth 32).toInt ++ [0, 0, 1, 248] := by
    decide
  have hc1 : cell64 p baHeaderWord =
      (cell (t := i32) p 1#32 ⋆ bytes (p + 4#64) [0, 0, 1, 248]) := by
    change Eq ((Int.toBytes 8 (0xf801000000000001#64 : BitVec 64).toInt).At p) = _
    rw [hb1]
    exact Mem.At_append_sep _ _ p (by decide)
  have hc2 : cell64 p (mkBaObj p 2#32 cap data).header =
      (cell (t := i32) p 2#32 ⋆ bytes (p + 4#64) [0, 0, 1, 248]) := by
    rw [baHeaderWord2_eq]
    change Eq ((Int.toBytes 8 (0xf801000000000002#64 : BitVec 64).toInt).At p) = _
    rw [hb2]
    exact Mem.At_append_sep _ _ p (by decide)
  rw [hc1] at hm
  repeat rw [sep_assoc] at hm
  have hld : loadVal m i32 p = some 1#32 :=
    loadVal_cell (t := i32) (by decide) hm
  obtain ⟨hstOk, hstMem⟩ := store_cell (t := i32) 2#32 (by decide) hm
  rw [← sep_assoc (cell (t := i32) p 2#32), ← hc2] at hstMem
  repeat rw [← sep_assoc] at hstMem
  refine ⟨hld, hstOk, ?_⟩
  rw [lcnfObjMem_sarray_eq rfl]
  dsimp only [mkBaObj]
  exact hstMem

private theorem lcnfObjMem_rc1_load {p : BitVec 64} {val : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem (mkFfiResOkObj p val) ⋆ R) m) :
    loadVal m i32 p = some 1#32 := by
  rw [lcnfObjMem_mkFfiResOkObj] at hm
  have hb : Int.toBytes 8 (ffiResOkHeader : BitVec 64).toInt =
      Int.toBytes 4 ((toBits i32 (1#32 : BitVec 32)).setWidth 32).toInt ++
        [16, 0, 1, 0] := by
    decide
  have hc : cell64 p ffiResOkHeader =
      (cell (t := i32) p 1#32 ⋆ bytes (p + 4#64) [16, 0, 1, 0]) := by
    change Eq ((Int.toBytes 8 (ffiResOkHeader : BitVec 64).toInt).At p) = _
    rw [hb]
    exact Mem.At_append_sep _ _ p (by decide)
  rw [hc] at hm
  have hm' : (cell (t := i32) p 1#32 ⋆
      (bytes (p + 4#64) [16, 0, 1, 0] ⋆ cell64 (p + 8#64) val ⋆ R)) m := sep_ac hm
  exact loadVal_cell (t := i32) (by decide) hm'

private theorem lcnfObjMem_ba1_load_rc {p : BitVec 64} {cap : Nat} {data : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem (mkBaObj p 1#32 cap data) ⋆ R) m) :
    loadVal m i32 p = some 1#32 := by
  have hb : Int.toBytes 8 (0xf801000000000001#64 : BitVec 64).toInt =
      Int.toBytes 4 ((toBits i32 (1#32 : BitVec 32)).setWidth 32).toInt ++ [0, 0, 1, 248] := by
    decide
  rw [lcnfObjMem_sarray_eq rfl, mkBaObj_header] at hm
  dsimp only [mkBaObj] at hm
  have hc : cell64 p baHeaderWord =
      (cell (t := i32) p 1#32 ⋆ bytes (p + 4#64) [0, 0, 1, 248]) := by
    change Eq ((Int.toBytes 8 (0xf801000000000001#64 : BitVec 64).toInt).At p) = _
    rw [hb]
    exact Mem.At_append_sep _ _ p (by decide)
  rw [hc] at hm
  have hm' : (cell (t := i32) p 1#32 ⋆
      (bytes (p + 4#64) [0, 0, 1, 248] ⋆ cell64 (p + 8#64) (BitVec.ofNat 64 data.length) ⋆
        cell64 (p + 16#64) (BitVec.ofNat 64 cap) ⋆ bytes (p + 24#64) data ⋆
        region (p + BitVec.ofNat 64 (24 + data.length))
          ((mkBaObj p 1#32 cap data).totalBytes - (24 + data.length)) ⋆ R)) m := sep_ac hm
  exact loadVal_cell (t := i32) (by decide) hm'

private theorem decColdRel_singleton_nil {obj : LcnfObj} {objs' : List LcnfObj}
    (hrel : DecColdRel obj.addr [obj] objs') : objs' = [] := by
  cases objs' with
  | nil => rfl
  | cons o' rest =>
    have ho' := hrel.2.2.2.2.1 o' List.mem_cons_self
    obtain ⟨o, hoMem, hoAddr, _⟩ := ho'.2.2
    rw [List.mem_singleton] at hoMem
    subst hoMem
    exact absurd hoAddr.symm ho'.2.1

private theorem decColdRel_ok_ba_rc2 {okP baNew : BitVec 64} {len : Nat}
    {outData : List UInt8} {objs' : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hne : okP ≠ baNew)
    (hrel : DecColdRel okP [mkFfiResOkObj okP baNew, mkBaObj baNew 2#32 len outData] objs')
    (hm : (lcnfHeap objs' ⋆ R) m) :
    objs' = [mkBaObj baNew 1#32 len outData] := by
  let okObj := mkFfiResOkObj okP baNew
  let ba2 := mkBaObj baNew 2#32 len outData
  have hbaCh : ba2.childFields = [] := by
    simp [ba2, mkBaObj, LcnfObj.childFields, sarrayTag, closureTag, arrayTag]
  have hokCh : okObj.childFields = [baNew] := by
    simp [okObj, mkFfiResOkObj, LcnfObj.childFields, closureTag, arrayTag]
  have hbaRcPos : 0 < ba2.rc.toInt := by dsimp only [ba2, mkBaObj]; decide
  have hbaRcNat : ba2.rc.toNat = 2 := by dsimp only [ba2, mkBaObj]; decide
  cases objs' with
  | nil =>
    have hdrop := (hrel.2.2.2.2.2.2.2.2 ba2 (by simp [ba2]) hbaRcPos).2
    have hmem : ba2 ∈ freedObjs [okObj, ba2] [] := by
      simp [freedObjs]
    have hrc := (hdrop hmem).1
    have hfr : freedObjs [okObj, ba2] [] = [okObj, ba2] := rfl
    rw [hfr] at hrc
    have hbaAddr : ba2.addr = baNew := rfl
    have hneSym : (if ba2.addr = okP then 1 else 0) = 0 := by
      rw [hbaAddr]; exact ite_eq_right hne.symm
    have hrefs : nonPersistRefs [okObj, ba2] ba2.addr = 1 := by
      dsimp only [nonPersistRefs, List.foldl]
      rw [hokCh, hbaCh]
      dsimp only [okObj, ba2, mkFfiResOkObj, mkBaObj]
      simp
    rw [hneSym, hrefs, hbaRcNat] at hrc
    omega
  | cons o1 rest =>
    have hinfo1 := hrel.2.2.2.2.1 o1 List.mem_cons_self
    obtain ⟨src1, hsrc1, haddr1, hcs1, hoth1, htag1, hfun1, har1, hcap1, hsz1, hst1, hfl1,
      hsc1, hlb1, _⟩ := hinfo1.2.2
    have ho1Ba : o1.addr = baNew := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hsrc1
      rcases hsrc1 with rfl | rfl
      · exact absurd haddr1.symm hinfo1.2.1
      · exact haddr1.symm
    cases rest with
    | cons o2 rest2 =>
      have hinfo2 := hrel.2.2.2.2.1 o2 (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨src2, hsrc2, haddr2, _⟩ := hinfo2.2.2
      have ho2Ba : o2.addr = baNew := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsrc2
        rcases hsrc2 with rfl | rfl
        · exact absurd haddr2.symm hinfo2.2.1
        · exact haddr2.symm
      simp only [lcnfHeap] at hm
      obtain ⟨Q1, hq1⟩ := lcnfObjMem_eq_cell64_sep o1
      obtain ⟨Q2, hq2⟩ := lcnfObjMem_eq_cell64_sep o2
      rw [hq1, hq2, ho1Ba, ho2Ba] at hm
      have hm' : (cell64 baNew o1.header ⋆ cell64 baNew o2.header ⋆
          (Q1 ⋆ Q2 ⋆ lcnfHeap rest2 ⋆ R)) m := sep_cast_ac hm (by ac_rfl)
      exact False.elim (cell64_sep_self_false hm')
    | nil =>
      have ho1Mem : o1 ∈ [o1] := List.mem_singleton.mpr rfl
      have hrcEq := (hrel.2.2.2.2.2.2.2.2 ba2 (by simp [ba2]) hbaRcPos).1 o1 ho1Mem
        (by rw [ho1Ba]; rfl)
      have hfr : freedObjs [okObj, ba2] [o1] = [okObj] := by
        simp [freedObjs, okObj, ba2, ho1Ba, hne, mkFfiResOkObj, mkBaObj]
      have hbaAddr : ba2.addr = baNew := rfl
      have hneSym : (if ba2.addr = okP then 1 else 0) = 0 := by
        rw [hbaAddr]; exact ite_eq_right hne.symm
      have hrefs : nonPersistRefs [okObj] ba2.addr = 1 := by
        dsimp only [nonPersistRefs, List.foldl]
        rw [hokCh]
        dsimp only [okObj, ba2, mkFfiResOkObj, mkBaObj]
        simp
      rw [hfr, hneSym, hrefs, hbaRcNat] at hrcEq
      have ho1Rc : o1.rc = 1#32 := by
        apply BitVec.eq_of_toNat_eq
        rw [show (1#32 : BitVec 32).toNat = 1 from by decide]
        omega
      have hsrcEq : src1 = ba2 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsrc1
        rcases hsrc1 with rfl | rfl
        · exact absurd haddr1.symm hinfo1.2.1
        · rfl
      subst hsrcEq
      have ho1Eq : o1 = mkBaObj baNew 1#32 len outData := by
        cases o1
        rw [LcnfObj.mk.injEq]
        dsimp only [ba2, mkBaObj] at *
        exact ⟨ho1Ba, ho1Rc, hcs1, hoth1, htag1, hfun1, har1, hcap1, hsz1, hst1, hfl1, hsc1, hlb1⟩
      rw [ho1Eq]

/-! ## 4. Lowered Pilot Function WP Proofs (`pilotLinkedEnv`) -/

theorem pilot_checkSatBA_wp :
    ∀ xs m Q X, pilotKissatSolveBASpec xs m Q X →
      Func.wp pilotLinkedEnv pilotTfs.tf_0.toFn.body xs m Q X := by
  intro ⟨rt, ba, workReq, fuel, ⟨⟩⟩ m Q X hPre
  p2_steps
  p2_call pilotLinkedEnv_kissat_solve_ba
  exact hPre

theorem pilot_checkSatNat_wp :
    ∀ xs m Q X, pilotKissatSolveNatSpec xs m Q X →
      Func.wp pilotLinkedEnv pilotTfs.tf_1.toFn.body xs m Q X := by
  intro ⟨rt, a, workReq, fuel, ⟨⟩⟩ m Q X hPre
  p2_steps
  p2_call pilotLinkedEnv_kissat_solve_nat
  exact hPre

theorem pilot_xorBA_wp :
    ∀ xs m Q X, pilotXorBASpec xs m Q X →
      Func.wp pilotLinkedEnv pilotTfs.tf_2.toFn.body xs m Q X := by
  intro ⟨rt, ba, key, ⟨⟩⟩ m Q X hPre
  p2_steps
  p2_call pilotLinkedEnv_xor_ba
  exact hPre

theorem pilot_xorNat_wp :
    ∀ xs m Q X, pilotXorNatSpec xs m Q X →
      Func.wp pilotLinkedEnv pilotTfs.tf_3.toFn.body xs m Q X := by
  intro ⟨rt, a, key, ⟨⟩⟩ m Q X hPre
  p2_steps
  p2_call pilotLinkedEnv_xor_nat
  exact hPre

private theorem eqRec_self {α : Sort _} {a : α} {P : α → Sort _} (h : a = a) (x : P a) :
    (h ▸ x) = x := by
  cases h; rfl

private theorem ite_split {P : Prop} [inst : Decidable P] {A B : Prop}
    (h1 : P → A) (h2 : ¬ P → B) : @ite Prop P inst A B := by
  by_cases h : P
  · rw [ite_eq_left h]; exact h1 h
  · rw [ite_eq_right h]; exact h2 h

local macro "p2_free_ret" rRes:ident st3:ident m3:ident hdom3:ident hu3:ident
    hs3:ident hpres3:ident hs3end:ident hrem3Le:ident hm3:ident
    rt:ident baObj:ident st:ident hst1End:ident hwc:ident
    hnewCan:ident hbaEven:ident hpres1:ident hpres2:ident
    hPost:ident R:ident outData:ident newBaObj1:ident hcl1:ident hrc1:ident : tactic =>
  `(tactic| (
    p2_straight
    let P_L3 : Tup Val [] → Mem 64 → Prop := fun () mL3 =>
      ($rRes = 0#64 ∨ $rRes = 3#64 ∨ $rRes = 10#64 ∨ $rRes = 20#64) ∧
      ($rRes = 20#64 → ∃ cnf, parseDimacs $outData = some cnf ∧ cnf.Unsat) ∧
      ($rRes = 10#64 → ∃ cnf, parseDimacs $outData = some cnf ∧ ¬ cnf.Unsat ∧
        ∃ α, cnf.Sat α) ∧
      ∃ st4 : RtC0State,
        st4.PreservesMetaExceptEnd $st ∧ st4.hdr.s_end = ($st).hdr.s_end ∧
        st4.rem ≤ ($st).rem ∧ (rtC0Inv $rt st4 ⋆ lcnfObjMem $baObj ⋆ $R) mL3
    refine wp_join_group P_L3 ?_ ?_
    · rintro J3 ⟨⟩ mF ⟨hdomF, huF, hsF, st4, hpres4, hs4end, hrem4, hmF⟩
      p2_steps
      exact $hPost $rRes st4 mF hdomF huF hsF hpres4 hs4end hrem4 hmF
    · intro J3 hJ3
      p2_straight
      constructor
      · intro hc
        exfalso
        dsimp only [Arg.val, liftCmp, lift2, CmpOp.evalBits] at hc
        repeat (first | rw [eqRec_self] at hc | erw [eqRec_self] at hc)
        have hbe := $hbaEven
        erw [hbe] at hc
        exact absurd hc (by decide)
      · intro _
        have hm3' := $hm3
        repeat (first | rw [eqRec_self] at hm3' | erw [eqRec_self] at hm3')
        have hm3Ba : (lcnfObjMem $newBaObj1 ⋆
            (rtC0Inv $rt $st3 ⋆ lcnfObjMem $baObj ⋆ $R)) $m3 :=
          sep_cast_ac hm3' (by ac_rfl)
        refine wp_load_of (v := 1#32) ?_ ?_
        · dsimp only [Arg.val]; repeat rw [eqRec_self]
          exact lcnfObjMem_ba1_load_rc hm3Ba
        p2_straight
        constructor
        · intro _
          have hst3Wc : 1 ≤ ($st3).workCap := by
            have hw3 := ($hpres3).2.2.2.2.1
            have hw2 := ($hpres2).toExceptEnd.2.2.2.2.1
            have hw1 := ($hpres1).2.2.2.2.1
            change 1 ≤ ($st3).hdr.s_work_cap.toNat
            rw [← hw3, ← hw2, ← hw1]
            exact Nat.le_trans (by decide) $hwc
          have hm3Cold : (rtC0Inv $rt $st3 ⋆ lcnfHeap [$newBaObj1] ⋆
              (lcnfObjMem $baObj ⋆ $R)) $m3 := by
            simp only [lcnfHeap, sep_emp]
            exact sep_cast_ac hm3' (by ac_rfl)
          p2_steps
          p2_call pilotLinkedEnv_dec_ref_cold
          dsimp only [lcnfDecRefColdSpec, vals, Tup.map, Arg.val]
          repeat rw [eqRec_self]
          refine ⟨$hbaEven, $st3, [$newBaObj1], lcnfObjMem $baObj ⋆ $R, hst3Wc, hm3Cold,
            ⟨$newBaObj1, List.mem_cons_self, rfl, rfl⟩,
            fun o ho => by rw [List.mem_singleton] at ho; subst ho; exact ($hnewCan).wf,
            $hcl1, $hrc1, fun st4 objs4 m4 hpres4 hrem4 hrel4 hm4 => ?_⟩
          repeat rw [eqRec_self] at hrel4 hm4
          have hnil := decColdRel_singleton_nil hrel4
          subst hnil
          simp only [lcnfHeap, sep_emp] at hm4
          p2_steps
          refine hJ3 () m4 ⟨$hdom3, $hu3, $hs3, st4, ?_, ?_, ?_, sep_cast_ac hm4 (by ac_rfl)⟩
          · exact ($hpres1).trans (($hpres2).toExceptEnd.trans
              (($hpres3).trans hpres4.toExceptEnd))
          · have hse3 := $hs3end
            have hpr2 := $hpres2
            try rw [hpres4.2.2.2.1]
            try rw [← hpres4.2.2.2.1]
            try rw [hse3]
            try rw [hpr2.2.2.2.1]
            try rw [← hpr2.2.2.2.1]
            exact $hst1End
          · rw [hrem4]; exact $hrem3Le
        · intro hc
          exfalso
          dsimp only [Arg.val] at hc
          repeat rw [eqRec_self] at hc
          exact absurd hc (by decide) ))

theorem pilot_solveXorBA_wp :
    ∀ xs m Q X, pilotSolveXorBASpec xs m Q X →
      Func.wp pilotLinkedEnv pilotTfs.tf_4.toFn.body xs m Q X := by
  intro ⟨rt, ba, key, workReq, fuel, ⟨⟩⟩ m Q X
    ⟨st, baObj, R, haddr, hcanon, hfit, hwc, hm, hPost⟩
  subst haddr
  let len := baObj.scalarData.length
  let outData := baObj.scalarData.map (· ^^^ UInt8.ofNat key.toNat)
  dsimp only [Func.wp, pilotTfs, Frontend.C0.TFlatFn.toFn]
  p2_steps
  p2_call pilotLinkedEnv_xor_ba
  dsimp only [pilotXorBASpec, vals, Tup.map, Arg.val]
  refine ⟨st, baObj, R, rfl, hcanon, hfit, hm, ?_⟩
  by_cases hok : pilotXorBaOk st len
  · rw [ite_eq_left hok]
    rw [ite_eq_left hok] at hPost
    intro p baNew st1 m1 hp0 hp8 hba0 hba8 hpres1 hs1end hrem1Le _ hnewCan hokCan hm1
    repeat rw [eqRec_self] at hm1 hnewCan
    p2_steps
    let P_L0 : Tup Val [i64] → Mem 64 → Prop := fun (tagV, ()) mL0 =>
      tagV = 0#64 ∧ mL0 = m1
    refine wp_join_group P_L0 ?_ ?_
    · rintro J0 ⟨tagV, ⟨⟩⟩ mL0 ⟨rfl, rfl⟩
      dsimp only [denoteB, denote, Blocks.get]
      change @LeanQbe.T.wp pilotLinkedEnv [i64] Q X _ mL0
      c0_hsteps
      have hldBaNew : loadVal mL0 i64 (p + 8#64) = some baNew := by
        have h := hm1
        rw [lcnfObjMem_mkFfiResOkObj] at h
        repeat rw [sep_assoc] at h
        rw [sep_comm] at h
        repeat rw [sep_assoc] at h
        rw [sep_comm (cell64 p ffiResOkHeader), sep_assoc] at h
        exact loadVal_cell64 h
      { refine wp_load_of (v := baNew) ?_ ?_
        · dsimp only [Arg.val]; repeat rw [eqRec_self]; exact hldBaNew
        p2_steps
        have hbaEven : (baNew &&& 1#64) = 0#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 1 from by decide,
            Nat.and_one_is_mod, show (0#64 : BitVec 64).toNat = 0 from rfl]
          omega
        have hbaBitF : ((baNew &&& 1#64) != 0#64) = false := by
          rw [hbaEven]; decide
        let newBaObj1 := mkBaObj baNew 1#32 len outData
        let newBaObj2 := mkBaObj baNew 2#32 len outData
        let P_L1 : Tup Val [] → Mem 64 → Prop := fun () mL1 =>
          (rtC0Inv rt st1 ⋆ lcnfObjMem (mkFfiResOkObj p baNew) ⋆
            lcnfObjMem newBaObj2 ⋆ lcnfObjMem baObj ⋆ R) mL1
        refine wp_join_group P_L1 ?_ ?_
        · rintro J1 ⟨⟩ mL1 hmL1
          p2_steps
          have hst1End : st1.hdr.s_end = st.hdr.s_end := hs1end
          have hst1Wc : 2 ≤ st1.workCap := by
            change 2 ≤ st1.hdr.s_work_cap.toNat
            rw [← hpres1.2.2.2.2.1]
            exact hwc
          have hpEven : (p &&& 1#64) = 0#64 := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 1 from by decide,
              Nat.and_one_is_mod, show (0#64 : BitVec 64).toNat = 0 from rfl]
            omega
          have hnePBa : p ≠ baNew := fun heq => by
            subst heq
            dsimp only [P_L1] at hmL1
            rw [lcnfObjMem_mkFfiResOkObj] at hmL1
            obtain ⟨Q2, hq2⟩ := lcnfObjMem_eq_cell64_sep newBaObj2
            rw [hq2] at hmL1
            have hmBad : (cell64 p newBaObj2.header ⋆ cell64 p ffiResOkHeader ⋆
                (Q2 ⋆ rtC0Inv rt st1 ⋆ cell64 (p + 8#64) p ⋆
                  lcnfObjMem baObj ⋆ R)) mL1 :=
              sep_cast_ac hmL1 (by ac_rfl)
            exact cell64_sep_self_false hmBad
          let okObj := mkFfiResOkObj p baNew
          let heap2 : List LcnfObj := [okObj, newBaObj2]
          have hcan2 : BaCanon newBaObj2 := by
            rcases hnewCan with ⟨a1, a2, _, a4, a5, a6, a7, a8, a9⟩
            exact ⟨a1, a2, (by dsimp only [newBaObj2, mkBaObj]; decide), a4, a5, a6, a7, a8, a9⟩
          have hclosed2 : lcnfHeapClosed heap2 := by
            intro o ho f hf _hf0
            simp only [heap2, List.mem_cons, List.not_mem_nil, or_false] at ho
            rcases ho with rfl | rfl
            · have hcf : okObj.childFields = [baNew] := by
                simp [okObj, mkFfiResOkObj, LcnfObj.childFields, closureTag, arrayTag]
              rw [hcf, List.mem_singleton] at hf; subst hf
              exact ⟨newBaObj2, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
            · simp [newBaObj2, mkBaObj, LcnfObj.childFields, sarrayTag, closureTag,
                arrayTag] at hf
          have hrcSound2 : RcSound p heap2 := by
            refine ⟨?_, ?_⟩
            · intro q hq hrc
              simp only [heap2, List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl <;> simp [okObj, newBaObj2, mkFfiResOkObj, mkBaObj] at hrc
            · intro y hy _
              simp only [heap2, List.mem_cons, List.not_mem_nil, or_false] at hy
              rcases hy with rfl | rfl
              · have hcf1 : okObj.childFields = [baNew] := by
                  simp [okObj, mkFfiResOkObj, LcnfObj.childFields, closureTag, arrayTag]
                have hcf2 : newBaObj2.childFields = [] := by
                  simp [newBaObj2, mkBaObj, LcnfObj.childFields, sarrayTag, closureTag, arrayTag]
                dsimp only [nonPersistRefs, heap2, List.foldl]
                rw [hcf1, hcf2]
                dsimp only [okObj, newBaObj2, mkFfiResOkObj, mkBaObj]
                simp [hnePBa.symm]
              · have hcf1 : okObj.childFields = [baNew] := by
                  simp [okObj, mkFfiResOkObj, LcnfObj.childFields, closureTag, arrayTag]
                have hcf2 : newBaObj2.childFields = [] := by
                  simp [newBaObj2, mkBaObj, LcnfObj.childFields, sarrayTag, closureTag, arrayTag]
                dsimp only [nonPersistRefs, heap2, List.foldl]
                rw [hcf1, hcf2]
                dsimp only [okObj, newBaObj2, mkFfiResOkObj, mkBaObj]
                simp [hnePBa.symm]
          let P_L2 : Tup Val [] → Mem 64 → Prop := fun () mL2 =>
            ∃ st2 : RtC0State,
              st2.PreservesMeta st1 ∧ st2.rem = st1.rem ∧
              (rtC0Inv rt st2 ⋆ lcnfObjMem newBaObj1 ⋆ lcnfObjMem baObj ⋆ R) mL2
          refine wp_join_group P_L2 ?_ ?_
          · rintro J2 ⟨⟩ mL2 ⟨st2, hpres2, hrem2, hmL2⟩
            have hcl1 : lcnfHeapClosed [newBaObj1] := by
              intro o ho f hf _
              rw [List.mem_singleton] at ho; subst ho
              simp [newBaObj1, mkBaObj, LcnfObj.childFields, sarrayTag, closureTag, arrayTag] at hf
            have hrc1 : RcSound baNew [newBaObj1] := by
              refine ⟨?_, ?_⟩
              · intro q hq hrc
                rw [List.mem_singleton] at hq; subst hq
                simp [newBaObj1, mkBaObj] at hrc
              · intro y hy _
                rw [List.mem_singleton] at hy; subst hy
                have hcf : newBaObj1.childFields = [] := by
                  simp [newBaObj1, mkBaObj, LcnfObj.childFields, sarrayTag, closureTag, arrayTag]
                dsimp only [nonPersistRefs, List.foldl]
                rw [hcf]
                dsimp only [newBaObj1, mkBaObj]
                simp
            p2_steps
            p2_call pilotLinkedEnv_kissat_solve_ba
            dsimp only [pilotKissatSolveBASpec, vals, Tup.map, Arg.val]
            repeat rw [eqRec_self]
            refine ⟨st2, newBaObj1, lcnfObjMem baObj ⋆ R, rfl, hnewCan, sep_ac hmL2, ?_⟩
            refine ite_split (fun _ => ?_) (fun _ => ?_)
            · intro rRes st3 m3 hdom3 hu3 hs3 _ _ hpres3 hs3end hrem3 hm3
              have hdom3' : rRes = 0#64 ∨ rRes = 3#64 ∨ rRes = 10#64 ∨ rRes = 20#64 :=
                hdom3.elim Or.inl (fun h => Or.inr (Or.inr h))
              have hrem3Le : st3.rem ≤ st.rem := by rw [hrem3, hrem2]; exact hrem1Le
              p2_free_ret rRes st3 m3 hdom3' hu3 hs3 hpres3 hs3end hrem3Le hm3
                rt baObj st hst1End hwc hnewCan hbaEven hpres1 hpres2
                hPost R outData newBaObj1 hcl1 hrc1
            · let rOom : BitVec 64 := 3#64
              have hdomOom : rOom = 0#64 ∨ rOom = 3#64 ∨ rOom = 10#64 ∨ rOom = 20#64 :=
                Or.inr (Or.inl rfl)
              have huOom : rOom = 20#64 → ∃ cnf, parseDimacs outData = some cnf ∧ cnf.Unsat :=
                fun h => absurd h (by decide)
              have hsOom : rOom = 10#64 → ∃ cnf, parseDimacs outData = some cnf ∧ ¬ cnf.Unsat ∧
                  ∃ α, cnf.Sat α :=
                fun h => absurd h (by decide)
              have hpresOom : st2.PreservesMetaExceptEnd st2 :=
                RtC0State.PreservesMetaExceptEnd.refl st2
              have hsEndOom : st2.hdr.s_end = st2.hdr.s_end := rfl
              have hrem2Le : st2.rem ≤ st.rem := by rw [hrem2]; exact hrem1Le
              p2_free_ret rOom st2 mL2 hdomOom huOom hsOom hpresOom hsEndOom hrem2Le hmL2
                rt baObj st hst1End hwc hnewCan hbaEven hpres1 hpres2
                hPost R outData newBaObj1 hcl1 hrc1
          · intro J2 hJ2
            p2_steps
            refine wp_load_of (v := 1#32) ?_ ?_
            · dsimp only [Arg.val]; repeat rw [eqRec_self]
              have h := hmL1
              dsimp only [P_L1] at h
              repeat rw [sep_assoc] at h
              rw [sep_comm (rtC0Inv rt st1), sep_assoc] at h
              exact lcnfObjMem_rc1_load h
            p2_straight
            constructor
            · intro _
              p2_steps
              p2_call pilotLinkedEnv_dec_ref_cold
              dsimp only [lcnfDecRefColdSpec, vals, Tup.map, Arg.val]
              repeat rw [eqRec_self]
              refine ⟨hpEven, st1, heap2, lcnfObjMem baObj ⋆ R,
                (by dsimp only [heap2]; exact hst1Wc),
                (by
                  dsimp only [P_L1] at hmL1
                  simp only [heap2, lcnfHeap, sep_emp]
                  exact sep_cast_ac hmL1 (by ac_rfl)),
                ⟨okObj, List.mem_cons_self, rfl, rfl⟩, ?_, hclosed2, hrcSound2, ?_⟩
              · intro o ho
                simp only [heap2, List.mem_cons, List.not_mem_nil, or_false] at ho
                rcases ho with rfl | rfl
                · exact hokCan.wf
                · exact hcan2.wf
              · intro st2 objs2 m2 hpres2 hrem2 hrel2 hm2
                repeat rw [eqRec_self] at hrel2 hm2
                have hm2' : (lcnfHeap objs2 ⋆ (rtC0Inv rt st2 ⋆ lcnfObjMem baObj ⋆ R)) m2 :=
                  sep_cast_ac hm2 (by ac_rfl)
                have hobjsEq := decColdRel_ok_ba_rc2 hnePBa hrel2 hm2'
                subst hobjsEq
                simp only [lcnfHeap, sep_emp] at hm2
                p2_steps
                exact hJ2 () m2 ⟨st2, hpres2, hrem2, sep_cast_ac hm2 (by ac_rfl)⟩
            · intro hc
              exfalso
              dsimp only [Arg.val] at hc
              repeat rw [eqRec_self] at hc
              exact absurd hc (by decide)
        · intro J1 hJ1
          p2_steps
          · exfalso
            repeat rw [eqRec_self] at hc
            exact absurd hbaEven hc
          · obtain ⟨hldBa, hstOk, hstMem⟩ := baObj_rc1_load_store_inc
              (R := rtC0Inv rt st1 ⋆ lcnfObjMem (mkFfiResOkObj p baNew) ⋆
                lcnfObjMem baObj ⋆ R) (sep_ac hm1)
            refine wp_load_of (v := 1#32)
              (by dsimp only [Arg.val]; repeat rw [eqRec_self]; exact hldBa) ?_
            p2_steps
            change LeanQbe.T.wp _ _ _ _ _
            refine wp_store_sep (P := lcnfObjMem newBaObj2)
              (R := rtC0Inv rt st1 ⋆ lcnfObjMem (mkFfiResOkObj p baNew) ⋆
                lcnfObjMem baObj ⋆ R) ?_ ?_
            · dsimp only [Arg.val]; repeat rw [eqRec_self]
              rw [show (1#32 + BitVec.ofNat 32 (BitVec.slt 0 (1#32 : BitVec 32)).toNat :
                  BitVec 32) = 2#32 from by decide]
              repeat (first | rw [eqRec_self] at hstMem | erw [eqRec_self] at hstMem)
              exact ⟨hstOk, hstMem⟩
            intro m2 hm2
            p2_steps
            refine hJ1 () m2 ?_
            dsimp only [P_L1]
            exact sep_cast_ac hm2 (by ac_rfl) }
    · intro J0 hJ0
      have hpEven : (p &&& 1#64) = 0#64 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 1 from by decide,
          Nat.and_one_is_mod, show (0#64 : BitVec 64).toNat = 0 from rfl]
        omega
      dsimp only [denote]
      change @LeanQbe.T.wp pilotLinkedEnv [i64] Q X _ m1
      p2_straight
      constructor
      · intro hc
        exfalso
        dsimp only [Arg.val, liftCmp, lift2, CmpOp.evalBits] at hc
        rw [decide_eq_true_iff] at hc
        repeat rw [eqRec_self] at hc
        exact absurd hpEven hc
      · intro _
        refine wp_load_of (v := 0#8) ?_ ?_
        · dsimp only [Arg.val]; repeat rw [eqRec_self]
          have h := hm1
          repeat rw [sep_assoc] at h
          rw [sep_comm (rtC0Inv rt st1), sep_assoc] at h
          exact ffiResOk_load_tag0 h
        p2_steps
        exact hJ0 (0#64, ()) m1 ⟨rfl, rfl⟩
  · rw [ite_eq_right hok]
    rw [ite_eq_right hok] at hPost
    intro st' m' hpres hsend hrem hm'
    dsimp only [ffiResOomWord]
    change @LeanQbe.T.wp pilotLinkedEnv [i64] Q X _ m'
    p2_steps
    let P_L0 : Tup Val [i64] → Mem 64 → Prop := fun (tagV, ()) mL0 =>
      tagV = 2#64 ∧ mL0 = m'
    refine wp_join_group P_L0 ?_ ?_
    · rintro J0 ⟨tagV, ⟨⟩⟩ mL0 ⟨rfl, rfl⟩
      dsimp only [denoteB, denote, Blocks.get]
      change @LeanQbe.T.wp pilotLinkedEnv [i64] Q X _ mL0
      p2_straight
      constructor
      · intro hc
        exfalso
        dsimp only [Arg.val] at hc
        repeat rw [eqRec_self] at hc
        exact absurd hc (by decide)
      · intro _
        p2_straight
        constructor
        · intro hc
          exfalso
          dsimp only [Arg.val] at hc
          repeat rw [eqRec_self] at hc
          exact absurd hc (by decide)
        · intro _
          p2_straight
          constructor
          · intro _
            p2_steps
            exact hPost st' mL0 hpres hsend hrem hm'
          · intro hc
            exfalso
            dsimp only [Arg.val] at hc
            repeat rw [eqRec_self] at hc
            exact absurd hc (by decide)
    · intro J0 hJ0
      dsimp only [denote]
      change @LeanQbe.T.wp pilotLinkedEnv [i64] Q X _ m'
      p2_straight
      constructor
      · intro _
        p2_steps
        exact hJ0 (2#64, ()) m' ⟨rfl, rfl⟩
      · intro hc
        exfalso
        dsimp only [Arg.val, liftCmp, lift2, CmpOp.evalBits] at hc
        rw [decide_eq_false_iff_not] at hc
        repeat rw [eqRec_self] at hc
        exact hc (by decide)

/-! ## 5. Whole-Module `ModuleOk` (`pilotLinkedMod_moduleOk`) -/

private theorem pilotLinkedMod_namesNodup : pilotLinkedMod.namesNodup := by
  have hc := pilotLinkedMod_checkAcyclic
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hc
  exact Module.namesNodup_of_checkNamesNodup hc.1

theorem pilotLinkedMod_fns_mem_plain {f : Fn} (h : f ∈ plainModule.fns) :
    f ∈ pilotLinkedMod.fns := by
  simp only [pilotLinkedMod, pilotLinkedFns, List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))

theorem pilotLinkedMod_fns_mem_rtC0 {f : Fn} (h : f ∈ rtC0CoreMod.fns) :
    f ∈ pilotLinkedMod.fns := by
  simp only [pilotLinkedMod, pilotLinkedFns, rtC0WithFfiMod, rtC0WithFfiFns, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (Or.inl h)))

theorem pilotLinkedMod_fns_mem_ffi {f : Fn} (h : f ∈ ffiPureMod.fns) :
    f ∈ pilotLinkedMod.fns := by
  simp only [pilotLinkedMod, pilotLinkedFns, rtC0WithFfiMod, rtC0WithFfiFns, ffiPureMod,
    List.mem_append] at h ⊢
  exact Or.inl (Or.inl (Or.inr (Or.inr h)))

theorem pilotLinkedMod_fns_mem_c0 {f : Fn} (h : f ∈ pilotC0_fns) :
    f ∈ pilotLinkedMod.fns := by
  simp only [pilotLinkedMod, pilotLinkedFns, List.mem_append]
  exact Or.inl (Or.inr h)

theorem pilotLinkedMod_fns_mem_prog {f : Fn} (h : f ∈ pilotProgMod.fns) :
    f ∈ pilotLinkedMod.fns := by
  simp only [pilotLinkedMod, pilotLinkedFns, List.mem_append]
  exact Or.inr h

theorem pilotC0_fns_wp :
    ∀ fn ∈ pilotC0_fns, ∀ xs m Q X,
      Env.ofTable pilotC0SpecEntries fn.name fn.as fn.rs xs m Q X →
      Func.wp pilotC0Env fn.body xs m Q X := by
  intro fn hfn xs m Q X hpre
  simp only [pilotC0_fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact c0_xor_bytes_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp hpre)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    exact lcnf_c0_kissat_raw_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h0)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    have h1 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h0
    exact lcnf_c0_kissat_solve_ba_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h1)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    have h1 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h0
    have h2 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h1
    exact lcnf_c0_kissat_solve_nat_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h2)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    have h1 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h0
    have h2 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h1
    have h3 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h2
    exact lcnf_c0_xor_ba_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h3)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    have h1 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h0
    have h2 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h1
    have h3 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h2
    have h4 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h3
    exact lcnf_c0_xor_nat_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h4)

theorem pilotProgMod_fns_wp :
    ∀ fn ∈ pilotProgMod.fns, ∀ xs m Q X,
      pilotProgEnv fn.name fn.as fn.rs xs m Q X →
      Func.wp pilotLinkedEnv fn.body xs m Q X := by
  intro fn hfn xs m Q X hpre
  rw [pilotProgMod_fns_eq] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl
  · exact pilot_checkSatBA_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp hpre)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    exact pilot_checkSatNat_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h0)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    have h1 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h0
    exact pilot_xorBA_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h1)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    have h1 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h0
    have h2 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h1
    exact pilot_xorNat_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h2)
  · have h0 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp hpre
    have h1 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h0
    have h2 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h1
    have h3 := (Env.ofTable_cons_ne (by decide) _ _ _ _).mp h2
    exact pilot_solveXorBA_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp h3)

private theorem ofModule_mem_fn_names {M : Module} {Γ : Env} (he : M.externs = [])
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofModule M Γ f as bs xs m Q X) :
    f ∈ M.fns.map Fn.name := by
  have hs := h.1
  simp only [Module.sigs, he, List.map_nil, List.append_nil, List.mem_map] at hs
  rcases hs with ⟨g, hg, heq⟩
  exact List.mem_map.mpr ⟨g, hg, congrArg Prod.fst heq⟩

private theorem ofTable_mem_map_name {tbl : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable tbl f as bs xs m Q X) :
    f ∈ tbl.map SpecEntry.name := by
  induction tbl with
  | nil => exact h.elim
  | cons e es ih =>
    rcases h with ⟨⟨rfl, _, _⟩, _⟩ | ⟨_, hrest⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hrest)

private theorem nodup_disj_l_r {α : Type} {a b : List α} (h : (a ++ b).Nodup)
    {x : α} (ha : x ∈ a) (hb : x ∈ b) : False :=
  (List.nodup_append.mp h).2.2 x ha x hb rfl

theorem pilotLinkedMod_fn_sound :
    ∀ fn ∈ pilotLinkedMod.fns, ∀ xs m Q X,
      pilotLinkedEnv fn.name fn.as fn.rs xs m Q X →
      Func.wp pilotLinkedEnv fn.body xs m Q X := by
  have hnd :
      (((plainModule.fns.map Fn.name ++
          (rtC0CoreMod.fns.map Fn.name ++ ffiPureMod.fns.map Fn.name)) ++
          pilotC0_fns.map Fn.name) ++
          pilotProgMod.fns.map Fn.name).Nodup := by
    simpa [Module.namesNodup, Module.names, pilotLinkedMod, pilotLinkedFns,
      rtC0WithFfiMod, rtC0WithFfiFns, ffiPureMod, List.map_append] using pilotLinkedMod_namesNodup
  have h1234 := (List.nodup_append.mp hnd).1
  have h123 := (List.nodup_append.mp h1234).1
  have h23 := (List.nodup_append.mp h123).2.1
  have hc0Names : ∀ {f : Sym},
      f ∈ pilotC0SpecEntries.map SpecEntry.name → f ∈ pilotC0_fns.map Fn.name := by
    intro f hf
    simpa [pilotC0SpecEntries, pilotC0_fns, SpecEntry.ofFn] using hf
  have hprogNames : ∀ {f : Sym},
      f ∈ pilotProgSpecEntries.map SpecEntry.name → f ∈ pilotProgMod.fns.map Fn.name := by
    intro f hf
    simpa [pilotProgSpecEntries, pilotProgMod_fns_eq, SpecEntry.ofFn] using hf
  have heFfi : ffiPureMod.externs = [] := rfl
  intro fn hfn xs m Q X hpre
  simp only [pilotLinkedMod, pilotLinkedFns, rtC0WithFfiMod, rtC0WithFfiFns,
    List.mem_append] at hfn
  have hmemFfi : ∀ g, g ∈ ffiMod.fns → g ∈ ffiPureMod.fns := fun g hg => hg
  rcases hpre with (hpl | hff | hc0) | hrt | hpr
  · have hn := ofModule_mem_fn_names rfl hpl
    rcases hfn with ((hp | (hr | hf)) | hc) | hg
    · exact wp_env_mono (fun _ _ _ _ _ _ _ => pilotPlainEnv_le_pilotLinkedEnv _ _ _ _ _ _ _) _ _
        (mkPlainEnv_sound plainSolveBytesCoreSpec (fun _ _ _ _ h => h) fn hp xs m Q X hpl.2)
    · exact absurd (List.mem_map_of_mem hr) (fun hrn =>
        nodup_disj_l_r h123 hn (List.mem_append_left _ hrn))
    · exact absurd (List.mem_map_of_mem (hmemFfi fn hf)) (fun hfn' =>
        nodup_disj_l_r h123 hn (List.mem_append_right _ hfn'))
    · exact absurd (List.mem_map_of_mem hc) (fun hcn =>
        nodup_disj_l_r h1234 (List.mem_append_left _ hn) hcn)
    · exact absurd (List.mem_map_of_mem hg) (fun hgn =>
        nodup_disj_l_r hnd (List.mem_append_left _ (List.mem_append_left _ hn)) hgn)
  · have hn := ofModule_mem_fn_names heFfi hff
    rcases hfn with ((hp | (hr | hf)) | hc) | hg
    · exact absurd (List.mem_map_of_mem hp) (fun hpn =>
        nodup_disj_l_r h123 hpn (List.mem_append_right _ hn))
    · exact absurd (List.mem_map_of_mem hr) (fun hrn =>
        nodup_disj_l_r h23 hrn hn)
    · exact wp_env_mono (fun _ _ _ _ _ _ _ => ffiEnv_le_pilotLinkedEnv _ _ _ _ _ _ _) _ _
        (ffiMod_fn_sound (hmemFfi fn hf) hff.2)
    · exact absurd (List.mem_map_of_mem hc) (fun hcn =>
        nodup_disj_l_r h1234 (List.mem_append_right _ (List.mem_append_right _ hn)) hcn)
    · exact absurd (List.mem_map_of_mem hg) (fun hgn =>
        nodup_disj_l_r hnd
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hn))) hgn)
  · have hn := hc0Names (ofTable_mem_map_name hc0)
    rcases hfn with ((hp | (hr | hf)) | hc) | hg
    · exact absurd (List.mem_map_of_mem hp) (fun hpn =>
        nodup_disj_l_r h1234 (List.mem_append_left _ hpn) hn)
    · exact absurd (List.mem_map_of_mem hr) (fun hrn =>
        nodup_disj_l_r h1234 (List.mem_append_right _ (List.mem_append_left _ hrn)) hn)
    · exact absurd (List.mem_map_of_mem (hmemFfi fn hf)) (fun hfn' =>
        nodup_disj_l_r h1234 (List.mem_append_right _ (List.mem_append_right _ hfn')) hn)
    · exact wp_env_mono (fun _ _ _ _ _ _ _ => pilotC0Env_le_pilotLinkedEnv _ _ _ _ _ _ _) _ _
        (pilotC0_fns_wp fn hc xs m Q X hc0)
    · exact absurd (List.mem_map_of_mem hg) (fun hgn =>
        nodup_disj_l_r hnd (List.mem_append_right _ hn) hgn)
  · have hn := ofModule_mem_fn_names rfl hrt
    rcases hfn with ((hp | (hr | hf)) | hc) | hg
    · exact absurd (List.mem_map_of_mem hp) (fun hpn =>
        nodup_disj_l_r h123 hpn (List.mem_append_left _ hn))
    · exact wp_env_mono (fun _ _ _ _ _ _ _ => rtC0CoreMod_env_le_pilotLinkedEnv _ _ _ _ _ _ _)
        _ _ (by
          obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hr
          exact (rtC0CoreMod_moduleOk.ofModule.fnsOk pre fn post hsp).2.2 xs m Q X hrt)
    · exact absurd (List.mem_map_of_mem (hmemFfi fn hf)) (fun hfn' =>
        nodup_disj_l_r h23 hn hfn')
    · exact absurd (List.mem_map_of_mem hc) (fun hcn =>
        nodup_disj_l_r h1234 (List.mem_append_right _ (List.mem_append_left _ hn)) hcn)
    · exact absurd (List.mem_map_of_mem hg) (fun hgn =>
        nodup_disj_l_r hnd
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hn))) hgn)
  · have hn := hprogNames (ofTable_mem_map_name hpr)
    rcases hfn with ((hp | (hr | hf)) | hc) | hg
    · exact absurd (List.mem_map_of_mem hp) (fun hpn =>
        nodup_disj_l_r hnd (List.mem_append_left _ (List.mem_append_left _ hpn)) hn)
    · exact absurd (List.mem_map_of_mem hr) (fun hrn =>
        nodup_disj_l_r hnd
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hrn))) hn)
    · exact absurd (List.mem_map_of_mem (hmemFfi fn hf)) (fun hfn' =>
        nodup_disj_l_r hnd
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hfn'))) hn)
    · exact absurd (List.mem_map_of_mem hc) (fun hcn =>
        nodup_disj_l_r hnd (List.mem_append_right _ hcn) hn)
    · exact pilotProgMod_fns_wp fn hg xs m Q X hpr

theorem pilotLinkedMod_moduleOk : ModuleOk pilotLinkedEnv pilotLinkedMod :=
  Module.moduleOk_of_checkAcyclic pilotLinkedMod_checkAcyclic pilotLinkedMod_fns_wf
    pilotLinkedMod_fn_sound

end

end LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
