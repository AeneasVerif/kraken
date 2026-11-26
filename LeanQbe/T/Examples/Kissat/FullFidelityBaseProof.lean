/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBase
public import LeanQbe.T.Examples.Kissat.FullFidelityBaseProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBaseProofBveVar
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofNv
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve1
import LeanQbe.T.Examples.Kissat.FullM7HotTernaryProof
import LeanQbe.T.Examples.Kissat.FullM7HotHop1Proof
import all LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullM7Splice
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofNv
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullM8FidV12Proof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import LeanQbe.T.Examples.Kissat.FullM4Bva
import LeanQbe.T.Examples.Kissat.FullBvaHeap
import LeanQbe.T.Examples.Kissat.FullM5HeurCore
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6Sweep
import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
import LeanQbe.T.Examples.Kissat.FullM7BveGates
import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
import LeanQbe.T.Examples.Kissat.FullFastBveBudgets
import LeanQbe.T.Examples.Kissat.FullM3CongBva
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Purified `FullFidelityBase` Closed Assembly Proof (`FullFidelityBaseProof`)

Packages the canonical flattened `469`-row specification table `fidBaseSpecTable` and flat table
environment `fidBaseEnv := Env.ofTable fidBaseSpecTable` over `FullFidelityBase.fidBaseModule`
(`469` fns, `0` externs, `0` exits, `0` beyond-upstream heuristics):
1. Flattens the `449`-fn `FullM8SweepV2.m8FidV123t2Env` tower into `m8SwFlatTable` via
   signature-preserving `mergeRows`, establishing `Env.ofTable m8SwFlatTable ↔ m8FidV123t2Env` and
   `m8SwFlat_moduleOk : ModuleOk (Env.ofTable m8SwFlatTable) m8FidV123t2Module`.
2. Patches `fidBaseReplRows` (`4` changed specs) and `fidBaseBeforeRows` (`3` Min + `17` purified
   BVE helpers) onto `m8SwFlatTable` to form `fidBaseSpecTable` (`469` rows, `noExit = true`,
   `Nodup`, matching `fidBaseFns.map Fn.sig`).
3. Closes unconditional `469/469` `fidBase_moduleOk : ModuleOk fidBaseEnv fidBaseModule`,
   `fidBase_tableImpl`, `fidBase_solve_bytes_sound`, `fidBase_solve_bytes_host_sound`,
   `fidBase_unsat_nv`, and genuine non-bailout concrete `Mem 64` UNSAT non-vacuity
   (`XPost := False`, `std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBase

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7HotTernary
open LeanQbe.T.Examples.Kissat.FullM7HotHop1
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity

private abbrev fRowSig := FullM8CoreParity.rowSig

/-! ## 1. `mergeRows` & `PatchModule.patchRows` Flattening Lemmas -/

private def mergeEntry (e1 e2 : SpecEntry) : SpecEntry :=
  ⟨e1.name, e1.as, e1.rs,
    fun xs m Q X =>
      e1.eff xs m Q X ∨
        ∃ (has : e2.as = e1.as) (hrs : e2.rs = e1.rs), e2.cast has hrs xs m Q X,
    e1.noExit && e2.noExit⟩

private def mergeRows (extra tbl : List SpecEntry) : List SpecEntry :=
  tbl.map fun e =>
    match extra.find? (·.name == e.name) with
    | none => e
    | some e2 => mergeEntry e e2

private theorem mergeRows_sigs (extra tbl : List SpecEntry) :
    (mergeRows extra tbl).map fRowSig = tbl.map fRowSig := by
  unfold mergeRows
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  dsimp only [Function.comp_def]
  cases extra.find? (·.name == e.name) <;> rfl

private theorem mergeRows_names (extra tbl : List SpecEntry) :
    (mergeRows extra tbl).map SpecEntry.name = tbl.map SpecEntry.name := by
  have h := congrArg (List.map Prod.fst) (mergeRows_sigs extra tbl)
  simpa only [List.map_map, Function.comp_def, fRowSig] using h

private theorem mergeRows_noExit {extra tbl : List SpecEntry}
    (hTbl : tbl.all SpecEntry.noExit = true) (hEx : extra.all SpecEntry.noExit = true) :
    (mergeRows extra tbl).all SpecEntry.noExit = true := by
  rw [List.all_eq_true]
  intro x hx
  rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
  have h1 := List.all_eq_true.mp hTbl e he
  cases hf : extra.find? (·.name == e.name) with
  | none => exact h1
  | some e2 =>
    have h2 := List.all_eq_true.mp hEx e2 (List.mem_of_find?_eq_some hf)
    simp [mergeEntry, h1, h2]

private theorem cast_noExit_eq {e : SpecEntry} (hno : e.noExit = true)
    {as bs : List Ty} (has : e.as = as) (hrs : e.rs = bs)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X X' : XPost}
    (h : e.cast has hrs xs m Q X) : e.cast has hrs xs m Q X' := by
  cases e with
  | mk nm eas ers sp nx =>
    dsimp only at hno has hrs
    subst hno; subst has; subst hrs
    simpa only [SpecEntry.cast, SpecEntry.eff, ite_true] using h

private theorem ofTable_mergeRows_iff {extra tbl : List SpecEntry}
    (hTblNd : (tbl.map SpecEntry.name).Nodup)
    (hExNd : (extra.map SpecEntry.name).Nodup)
    (hTblNo : tbl.all SpecEntry.noExit = true)
    (hExNo : extra.all SpecEntry.noExit = true)
    (hExIn : ∀ e2 ∈ extra, ∃ e1 ∈ tbl, fRowSig e1 = fRowSig e2)
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost} :
    Env.ofTable (mergeRows extra tbl) f as bs xs m Q X ↔
      Env.ofTable tbl f as bs xs m Q X ∨ Env.ofTable extra f as bs xs m Q X := by
  have hMrgNd : ((mergeRows extra tbl).map SpecEntry.name).Nodup := by
    rw [mergeRows_names]; exact hTblNd
  constructor
  · intro h
    obtain ⟨e', he', hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim h
    rcases List.mem_map.mp he' with ⟨e1, he1, rfl⟩
    cases hf : extra.find? (·.name == e1.name) with
    | none =>
      simp only [hf] at hnm has hrs hcast
      exact Or.inl (ofTable_of_cast he1 hTblNd hnm has hrs hcast)
    | some e2 =>
      simp only [hf] at hnm has hrs hcast
      have he2 : e2 ∈ extra := List.mem_of_find?_eq_some hf
      have hnm2 : e2.name = e1.name :=
        beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == e1.name) hf)
      have hno1 : e1.noExit = true := List.all_eq_true.mp hTblNo e1 he1
      have hno2 : e2.noExit = true := List.all_eq_true.mp hExNo e2 he2
      cases e1 with
      | mk nm1 as1 rs1 sp1 nx1 =>
        dsimp only [mergeEntry] at hnm has hrs hno1 hcast
        subst hnm; subst has; subst hrs; subst hno1
        simp only [SpecEntry.cast, SpecEntry.eff, hno2, Bool.and_self, ite_true] at hcast
        rcases hcast with h1 | ⟨has2, hrs2, h2⟩
        · exact Or.inl (Env.ofTable_of_mem he1 hTblNd
            (by simpa only [SpecEntry.eff, ite_true] using h1))
        · exact Or.inr (ofTable_of_cast he2 hExNd hnm2 has2 hrs2
            (cast_noExit_eq hno2 has2 hrs2 h2))
  · rintro (ht | hx)
    · obtain ⟨e1, he1, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim ht
      let e' : SpecEntry :=
        match extra.find? (·.name == e1.name) with
        | none => e1
        | some e2 => mergeEntry e1 e2
      have he' : e' ∈ mergeRows extra tbl := List.mem_map.mpr ⟨e1, he1, rfl⟩
      cases hf : extra.find? (·.name == e1.name) with
      | none =>
        have heq : e' = e1 := by simp [e', hf]
        rw [heq] at he'
        exact ofTable_of_cast he' hMrgNd hnm has hrs hcast
      | some e2 =>
        have heq : e' = mergeEntry e1 e2 := by simp [e', hf]
        rw [heq] at he'
        have hno1 : e1.noExit = true := List.all_eq_true.mp hTblNo e1 he1
        have hno2 : e2.noExit = true :=
          List.all_eq_true.mp hExNo e2 (List.mem_of_find?_eq_some hf)
        cases e1 with
        | mk nm1 as1 rs1 sp1 nx1 =>
          dsimp only at hnm has hrs hno1
          subst hnm; subst has; subst hrs; subst hno1
          refine Env.ofTable_of_mem he' hMrgNd ?_
          simp only [mergeEntry, SpecEntry.eff, hno2, Bool.and_self, ite_true]
          exact Or.inl (by simpa only [SpecEntry.cast, SpecEntry.eff, ite_true] using hcast)
    · obtain ⟨e2, he2, hnm2, has2, hrs2, hcast2⟩ := env_ofTable_mem_elim hx
      obtain ⟨e1, he1, hsig⟩ := hExIn e2 he2
      have hnm1 : e1.name = e2.name := congrArg Prod.fst hsig
      have has1 : e1.as = e2.as := congrArg (fun p => p.2.1) hsig
      have hrs1 : e1.rs = e2.rs := congrArg (fun p => p.2.2) hsig
      have hfind : extra.find? (·.name == e1.name) = some e2 := by
        have hsome : (extra.find? (·.name == e1.name)).isSome = true :=
          List.find?_isSome.mpr ⟨e2, he2, beq_iff_eq.mpr hnm1.symm⟩
        cases hf : extra.find? (·.name == e1.name) with
        | none => simp [hf] at hsome
        | some e2' =>
          have h2' := List.mem_of_find?_eq_some hf
          have hnm2' :=
            beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == e1.name) hf)
          rw [m8cp_nodup_name_eq SpecEntry.name hExNd h2' he2 (hnm2'.trans hnm1)]
      have he' : mergeEntry e1 e2 ∈ mergeRows extra tbl :=
        List.mem_map.mpr ⟨e1, he1, by simp [hfind]⟩
      have hno1 : e1.noExit = true := List.all_eq_true.mp hTblNo e1 he1
      have hno2 : e2.noExit = true := List.all_eq_true.mp hExNo e2 he2
      cases e1 with
      | mk nm1 as1 rs1 sp1 nx1 =>
        dsimp only at hnm1 has1 hrs1 hno1
        have hnmf : nm1 = f := hnm1.trans hnm2
        have hasf : as1 = as := has1.trans has2
        have hrsf : rs1 = bs := hrs1.trans hrs2
        subst hnmf; subst hasf; subst hrsf; subst hno1
        refine Env.ofTable_of_mem he' hMrgNd ?_
        simp only [mergeEntry, SpecEntry.eff, hno2, Bool.and_self, ite_true]
        exact Or.inr ⟨has2, hrs2, cast_noExit_eq hno2 has2 hrs2 hcast2⟩

private theorem mem_patchRows_of_repl {rRows tbl : List SpecEntry}
    {bRows : List (Sym × List SpecEntry)} {r e : SpecEntry}
    (hRNd : (rRows.map SpecEntry.name).Nodup) (hr : r ∈ rRows) (he : e ∈ tbl)
    (hnm : r.name = e.name) : r ∈ PatchModule.patchRows rRows bRows tbl := by
  have hf : rRows.find? (·.name == e.name) = some r := by
    have hs : (rRows.find? (·.name == e.name)).isSome = true :=
      List.find?_isSome.mpr ⟨r, hr, beq_iff_eq.mpr hnm⟩
    cases h : rRows.find? (·.name == e.name) with
    | none => simp [h] at hs
    | some r' =>
      have hn' := beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == e.name) h)
      rw [m8cp_nodup_name_eq SpecEntry.name hRNd (List.mem_of_find?_eq_some h) hr
        (hn'.trans hnm.symm)]
  simp only [PatchModule.patchRows, List.mem_flatMap, List.mem_append, List.mem_singleton]
  exact ⟨e, he, Or.inr (by simp [hf])⟩

private theorem mem_patchRows_of_before {rRows tbl : List SpecEntry}
    {bRows : List (Sym × List SpecEntry)} {tgt : Sym} {ins : List SpecEntry}
    {b e : SpecEntry} (hBNd : (bRows.map Prod.fst).Nodup)
    (hp : (tgt, ins) ∈ bRows) (hb : b ∈ ins) (he : e ∈ tbl) (hnm : e.name = tgt) :
    b ∈ PatchModule.patchRows rRows bRows tbl := by
  have hf : bRows.find? (·.1 == e.name) = some (tgt, ins) := by
    have hs : (bRows.find? (·.1 == e.name)).isSome = true :=
      List.find?_isSome.mpr ⟨(tgt, ins), hp, beq_iff_eq.mpr hnm.symm⟩
    cases h : bRows.find? (·.1 == e.name) with
    | none => simp [h] at hs
    | some p' =>
      have hn' := beq_iff_eq.mp
        (List.find?_some (p := fun p : Sym × List SpecEntry => p.1 == e.name) h)
      rw [m8cp_nodup_name_eq Prod.fst hBNd (List.mem_of_find?_eq_some h) hp (hn'.trans hnm)]
  simp only [PatchModule.patchRows, List.mem_flatMap, List.mem_append, PatchModule.patchRowInsAt]
  exact ⟨e, he, Or.inl (by simp [hf, hb])⟩

private theorem mem_patchRows_of_base {rRows tbl : List SpecEntry}
    {bRows : List (Sym × List SpecEntry)} {e : SpecEntry}
    (he : e ∈ tbl) (hnr : e.name ∉ rRows.map SpecEntry.name) :
    e ∈ PatchModule.patchRows rRows bRows tbl := by
  have hf : rRows.find? (·.name == e.name) = none := by
    cases h : rRows.find? (·.name == e.name) with
    | none => rfl
    | some r =>
      have hn := beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == e.name) h)
      exact absurd (List.mem_map.mpr ⟨r, List.mem_of_find?_eq_some h, hn⟩) hnr
  simp only [PatchModule.patchRows, List.mem_flatMap, List.mem_append, List.mem_singleton]
  exact ⟨e, he, Or.inr (by simp [hf])⟩

private theorem row_of_idx {fs : List Fn} {tbl : List SpecEntry}
    (hSigs : tbl.map fRowSig = fs.map Fn.sig) {i : Nat} {s : SigEntry}
    (hi : fs[i]?.map Fn.sig = some s) : ∃ e ∈ tbl, fRowSig e = s := by
  obtain ⟨g, hg, hsg⟩ := m8cp_sig_of_map hi
  have hm : s ∈ fs.map Fn.sig := hsg ▸ List.mem_map_of_mem (List.mem_of_getElem? hg)
  rw [← hSigs] at hm
  rcases List.mem_map.mp hm with ⟨e, he, hes⟩
  exact ⟨e, he, hes⟩

private theorem sig_eq_of_idx {fs : List Fn} (hnd : (fs.map Fn.name).Nodup)
    {i : Nat} {s : SigEntry} (hi : fs[i]?.map Fn.sig = some s)
    {g : Fn} (hg : g ∈ fs) (hnm : s.1 = g.name) : g.sig = s := by
  obtain ⟨g0, hg0, hsg0⟩ := m8cp_sig_of_map hi
  have hgeq := m8cp_nodup_name_eq Fn.name hnd hg (List.mem_of_getElem? hg0)
    (hnm.symm.trans (congrArg Prod.fst hsg0).symm)
  rw [hgeq, hsg0]

/-! ## 2. Batched Base Signature Cache (Zero `find?` String Scans) -/

private theorem slotSig_at {xs : List Fn} {idxs : List Nat} {sigs : List (Option SigEntry)}
    (h : idxs.map (fun i => xs[i]?.map Fn.sig) = sigs) (k idx : Nat) (sg : Option SigEntry)
    (hi : idxs[k]? = some idx := by decide) (hs : sigs[k]? = some sg := by decide) :
    xs[idx]?.map Fn.sig = sg := by
  have h0 := PatchModule.slotSig_at h k
  simpa [hi, hs] using h0

private def m7SlotIdxs : List Nat := [347, 368, 405]

private def m7SlotSigs : List (Option SigEntry) :=
  [ some ("full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32])
  , some ("full_reorder_queue_m7", [i64], [i64])
  , some ("full_search_m6", [i64], [i64]) ]

private theorem m7_slotSigs_ok :
    m7SlotIdxs.map (fun i => FullM7.m7Fns[i]?.map Fn.sig) = m7SlotSigs := by
  t_kernel_rfl

private theorem m7_idx_347 : FullM7.m7Fns[347]?.map Fn.sig =
    some ("full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32]) :=
  slotSig_at m7_slotSigs_ok 0 347 _

private theorem m7_idx_368 : FullM7.m7Fns[368]?.map Fn.sig =
    some ("full_reorder_queue_m7", [i64], [i64]) :=
  slotSig_at m7_slotSigs_ok 1 368 _

private theorem m7_idx_405 : FullM7.m7Fns[405]?.map Fn.sig =
    some ("full_search_m6", [i64], [i64]) :=
  slotSig_at m7_slotSigs_ok 2 405 _

private def m7fSlotIdxs : List Nat := [172, 257, 258, 260, 299]

private def m7fSlotSigs : List (Option SigEntry) :=
  [ some ("full_extend_push2", [i64, i32, i32], [.bool])
  , some ("full_cong_enq_var", [i64, i64, i32], [])
  , some ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64])
  , some ("full_cong_worklist", [i64, i64, i64, i64], [i64])
  , some ("full_sweep_dense_m6", [i64, i64, i64], [i64]) ]

private theorem m7f_slotSigs_ok :
    m7fSlotIdxs.map (fun i => m7FidelityFns[i]?.map Fn.sig) = m7fSlotSigs := by
  t_kernel_rfl

private theorem m7f_idx_172 : m7FidelityFns[172]?.map Fn.sig =
    some ("full_extend_push2", [i64, i32, i32], [.bool]) :=
  slotSig_at m7f_slotSigs_ok 0 172 _

private theorem m7f_idx_257 : m7FidelityFns[257]?.map Fn.sig =
    some ("full_cong_enq_var", [i64, i64, i32], []) :=
  slotSig_at m7f_slotSigs_ok 1 257 _

private theorem m7f_idx_258 : m7FidelityFns[258]?.map Fn.sig =
    some ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64]) :=
  slotSig_at m7f_slotSigs_ok 2 258 _

private theorem m7f_idx_260 : m7FidelityFns[260]?.map Fn.sig =
    some ("full_cong_worklist", [i64, i64, i64, i64], [i64]) :=
  slotSig_at m7f_slotSigs_ok 3 260 _

private theorem m7f_idx_299 : m7FidelityFns[299]?.map Fn.sig =
    some ("full_sweep_dense_m6", [i64, i64, i64], [i64]) :=
  slotSig_at m7f_slotSigs_ok 4 299 _

private def swSlotPairs : List (Nat × SigEntry) :=
  [ (17, ("full_wstack_defrag", [i64], []))
  , (31, ("full_log10_q16_m7", [i64], [i64]))
  , (32, ("full_scale_delta_m5", [i64, i64], [i64]))
  , (39, ("full_backtrack", [i64, i64], []))
  , (66, ("m6_hdr_delaying", [i64, i64], [.bool]))
  , (67, ("m6_hdr_bump_delay", [i64, i64], []))
  , (68, ("m6_hdr_reduce_delay", [i64, i64], []))
  , (70, ("m6_hdr_get_watermark", [i64, i64], [i64]))
  , (71, ("m6_hdr_set_watermark", [i64, i64, i64], []))
  , (86, ("full_propagate", [i64], [i64]))
  , (111, ("full_reduce_m6", [i64, .bool], [i64]))
  , (124, ("full_min_mark", [i64, i32, i8], []))
  , (129, ("full_sort_tmp", [i64], []))
  , (135, ("full_min_shrink_m6", [i64], []))
  , (137, ("full_min_shrink", [i64], []))
  , (151, ("full_analyze_m6_hdr", [i64], [i64]))
  , (169, ("full_rephase", [i64], []))
  , (170, ("full_restart_due", [i64], [i64]))
  , (171, ("full_restart", [i64], []))
  , (180, ("full_set_inactive", [i64, i32, i32], []))
  , (209, ("full_viv_clause_m6", [i64, i32], [i64]))
  , (211, ("full_viv_collect_m6", [i64, i64], [i64]))
  , (212, ("full_viv_count_m6", [i64, i64], []))
  , (213, ("full_viv_keys_m6", [i64, i64], []))
  , (214, ("full_viv_sort_sched_m6", [i64, i64], []))
  , (215, ("full_viv_clear_tier_m6", [i64, i64], []))
  , (217, ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))
  , (218, ("full_vivify_m6_hdr", [i64], [i64]))
  , (226, ("full_backbone_m6", [i64, i64], [i64]))
  , (235, ("full_substitute", [i64], [i64]))
  , (236, ("full_enter_dense", [i64], [.bool]))
  , (237, ("full_rebuild_watches", [i64], [i64]))
  , (243, ("full_has_ternary", [i64, i32, i32, i32], [.bool]))
  , (275, ("full_congruence_dense", [i64, i64], [i64]))
  , (299, ("full_m6_max_v", [i64], [i64]))
  , (314, ("full_m6_dense_prop", [i64], [.bool]))
  , (331, ("full_m6_sweep_var", [i64, i32, i64], [i64]))
  , (333, ("full_m6_collect_cands", [i64], [i32]))
  , (334, ("full_m6_sweep_vars", [i64, i64, i64], [i64]))
  , (335, ("full_sweep_dense_m6", [i64, i64, i64], [i64]))
  , (338, ("full_dense_flush_units_m7", [i64], [.bool]))
  , (346, ("full_bve_collect_m7", [i64, i32, i64, i32], [i32]))
  , (352, ("full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool]))
  , (368, ("full_bve_gates_m7", [i64, i32, i32, i32], []))
  , (369, ("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]))
  , (370, ("full_bve_weaken", [i64, i32, i32, i32], [.bool]))
  , (372, ("full_bve_commit_res", [i64, i64, i64], [i64]))
  , (373, ("full_bve_ext_need", [i64, i32, i32], [i64]))
  , (374, ("full_bve_var_m7", [i64, i32], [i64]))
  , (375, ("full_bve_var", [i64, i32], [i64]))
  , (377, ("full_bva_hop1", [i64, i32, i32], [i64]))
  , (378, ("full_bva_hop2", [i64, i32, i32], [i64]))
  , (389, ("full_factor", [i64, i64], [i64]))
  , (407, ("full_reorder_m6", [i64, i64], [i64]))
  , (412, ("full_min_u64", [i64, i64], [i64]))
  , (415, ("full_bve_var_key_m7", [i64, i32], [i64]))
  , (418, ("full_bve_heap_push_m7", [i64, i64, i32], [i64]))
  , (432, ("full_lucky_late_m7", [i64], [i64]))
  , (437, ("full_switch_mode_m7", [i64], []))
  , (438, ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
  , (439, ("full_probe_tail_m6", [i64, i64], [i64]))
  , (440, ("full_probe_m6", [i64, .bool], [i64]))
  , (442, ("full_simplify_m6", [i64, .bool, .bool], [i64]))
  , (443, ("m6_hdr_decide_fid", [i64], [i64]))
  , (444, ("full_search_m6", [i64], [i64])) ]

private def swBaseProps : Bool :=
  (m8SwBaseSpecTable.length == 449) &&
  m8SwBaseSpecTable.all (fun e => e.name != "full_bve_gates_fid") &&
  swSlotPairs.all (fun p =>
    match m8SwBaseSpecTable[p.1]? with
    | some e => SigEntry.beq (fRowSig e) p.2
    | none => false)

private theorem swBaseProps_ok : swBaseProps = true := by t_kernel_rfl

private theorem swBase_len_ok : m8SwBaseSpecTable.length = 449 := by
  have h := swBaseProps_ok
  simp only [swBaseProps, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

private theorem swBase_sigs_fRow :
    m8SwBaseSpecTable.map fRowSig = m8FidV123t2Fns.map Fn.sig := by
  have hc : m8SwBaseSpecTable.map fRowSig =
      m8SwBaseSpecTable.map FullM8CoreParity.spliceRowSig :=
    List.map_congr_left (fun _ _ => rfl)
  exact hc.trans m8cp_swBase_sigs

private theorem sw_not_mem_gates :
    "full_bve_gates_fid" ∉ m8FidV123t2Fns.map Fn.name := by
  have h := swBaseProps_ok
  simp only [swBaseProps, Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.1.2
  intro hm
  have h1 : "full_bve_gates_fid" ∈ m8SwBaseSpecTable.map SpecEntry.name := by
    have hs := congrArg (List.map Prod.fst) swBase_sigs_fRow
    have hL : m8SwBaseSpecTable.map SpecEntry.name = (m8SwBaseSpecTable.map fRowSig).map Prod.fst :=
      by rw [List.map_map]; exact List.map_congr_left (fun _ _ => rfl)
    have hR : m8FidV123t2Fns.map Fn.name = (m8FidV123t2Fns.map Fn.sig).map Prod.fst :=
      by rw [List.map_map]; exact List.map_congr_left (fun _ _ => rfl)
    rw [hL, hs, ← hR]; exact hm
  rcases List.mem_map.mp h1 with ⟨e, he, hnm⟩
  have heq := hall e he
  simp only [bne_iff_ne, ne_eq] at heq
  exact heq hnm

private theorem swSlot_sig_of_mem {idx : Nat} {s : SigEntry}
    (hm : (idx, s) ∈ swSlotPairs := by decide) :
    m8FidV123t2Fns[idx]?.map Fn.sig = some s := by
  have h := swBaseProps_ok
  simp only [swBaseProps, Bool.and_eq_true] at h
  have h1 := List.all_eq_true.mp h.2 (idx, s) hm
  cases hg : m8SwBaseSpecTable[idx]? with
  | none => simp [hg] at h1
  | some e =>
    simp only [hg] at h1
    have heq := SigEntry.beq_iff_eq.mp h1
    rw [← List.getElem?_map, ← swBase_sigs_fRow, List.getElem?_map, hg, Option.map_some, heq]

private theorem sw_idx_135 : m8FidV123t2Fns[135]?.map Fn.sig =
    some ("full_min_shrink_m6", [i64], []) := swSlot_sig_of_mem
private theorem sw_idx_137 : m8FidV123t2Fns[137]?.map Fn.sig =
    some ("full_min_shrink", [i64], []) := swSlot_sig_of_mem
private theorem sw_idx_217 : m8FidV123t2Fns[217]?.map Fn.sig =
    some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_243 : m8FidV123t2Fns[243]?.map Fn.sig =
    some ("full_has_ternary", [i64, i32, i32, i32], [.bool]) := swSlot_sig_of_mem
private theorem sw_idx_334 : m8FidV123t2Fns[334]?.map Fn.sig =
    some ("full_m6_sweep_vars", [i64, i64, i64], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_374 : m8FidV123t2Fns[374]?.map Fn.sig =
    some ("full_bve_var_m7", [i64, i32], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_375 : m8FidV123t2Fns[375]?.map Fn.sig =
    some ("full_bve_var", [i64, i32], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_377 : m8FidV123t2Fns[377]?.map Fn.sig =
    some ("full_bva_hop1", [i64, i32, i32], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_378 : m8FidV123t2Fns[378]?.map Fn.sig =
    some ("full_bva_hop2", [i64, i32, i32], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_415 : m8FidV123t2Fns[415]?.map Fn.sig =
    some ("full_bve_var_key_m7", [i64, i32], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_418 : m8FidV123t2Fns[418]?.map Fn.sig =
    some ("full_bve_heap_push_m7", [i64, i64, i32], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_438 : m8FidV123t2Fns[438]?.map Fn.sig =
    some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_440 : m8FidV123t2Fns[440]?.map Fn.sig =
    some ("full_probe_m6", [i64, .bool], [i64]) := swSlot_sig_of_mem
private theorem sw_idx_444 : m8FidV123t2Fns[444]?.map Fn.sig =
    some ("full_search_m6", [i64], [i64]) := swSlot_sig_of_mem

private theorem not_in_swRows (nm : Sym)
    (h : !(m8SwNamesLit.contains nm) = true := by decide) :
    nm ∉ m8SweepEnvRows.map SpecEntry.name := by
  rw [m8SweepEnvRows_names_eq]
  simp only [Bool.not_eq_true'] at h
  simpa using h

/-! ## 3. Flattening `m8FidV123t2Env` (`449` Rows) into `m8SwFlatTable` -/

private def m7FidMergedBase : List SpecEntry :=
  mergeRows mfExtraBaseRows m7FidBaseTable

private def m7FidFlatTable : List SpecEntry :=
  PatchModule.patchRows m7FidReplRows m7FidBeforeRows m7FidMergedBase

private def m8V12ExtraRows : List SpecEntry :=
  [ ⟨"full_cong_enq_var", [i64, i64, i32], [], m8CongEnqVarSpec, true⟩
  , ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], m8CongEvalGateSpec, true⟩
  , ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], m8CongWorklistSpec, true⟩ ]

private def m8V12FlatTable : List SpecEntry :=
  mergeRows m8V12ExtraRows m7FidFlatTable

private def m8SwExtPush2Row : SpecEntry :=
  ⟨"full_extend_push2", [i64, i32, i32], [.bool], m6ExtendPush2Spec, true⟩

private def m8SwFlatTable : List SpecEntry :=
  PatchModule.patchRows [m8SwExtPush2Row] [("full_sweep_dense_m6", m8SweepEnvRows)] m8V12FlatTable

private theorem m7FidMergedBase_sigs :
    m7FidMergedBase.map fRowSig = FullM7.m7Fns.map Fn.sig := by
  rw [m7FidMergedBase, mergeRows_sigs]; exact m7FidBaseTable_sigs

private theorem mfExtraBaseRows_nodup : (mfExtraBaseRows.map SpecEntry.name).Nodup := by
  have h := mfExtraRows_nodup
  rw [mfExtraRows, List.map_append, List.nodup_append] at h
  exact h.1

private theorem mfExtraBaseRows_noExit : mfExtraBaseRows.all SpecEntry.noExit = true := by
  rw [List.all_eq_true]
  intro e he
  exact mfExtraRows_noExit e (by rw [mfExtraRows]; exact List.mem_append_left _ he)

private theorem m7FidMergedBase_noExit : m7FidMergedBase.all SpecEntry.noExit = true :=
  mergeRows_noExit m7FidBaseTable_noExit mfExtraBaseRows_noExit

private def mfExtraBaseIdxs : List Nat :=
  [ 54, 56, 81, 82, 175, 124, 116, 117, 127, 128, 129, 130, 132, 133, 154, 155, 156, 157, 158
  , 159, 160, 161, 162, 163, 165, 177, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201
  , 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215 ]

private theorem mfExtraBaseRows_in_m7Base :
    ∀ e2 ∈ mfExtraBaseRows, ∃ e1 ∈ m7FidBaseTable, fRowSig e1 = fRowSig e2 := by
  have hlen : mfExtraBaseIdxs.length = mfExtraBaseRows.length := by decide
  have hchk : (mfExtraBaseIdxs.zip (mfExtraBaseRows.map fRowSig)).all
      (fun p => FullM7.m7Fns[p.1]?.map Fn.sig == some p.2) = true := by
    t_kernel_rfl
  intro e2 he2
  rcases List.mem_iff_getElem.mp he2 with ⟨k, hk, rfl⟩
  have hk' : k < (mfExtraBaseIdxs.zip (mfExtraBaseRows.map fRowSig)).length := by
    simp [hlen, hk]
  have hmem := List.getElem_mem hk'
  have h1 := List.all_eq_true.mp hchk _ hmem
  simp only [List.getElem_zip, List.getElem_map, beq_iff_eq] at h1
  exact row_of_idx m7FidBaseTable_sigs h1

private theorem m7FidFlatTable_sigs :
    m7FidFlatTable.map fRowSig = m7FidelityFns.map Fn.sig := by
  rw [m7FidFlatTable, m7FidelityFns_eq_patchFns]
  refine patchRows_sigs_eq_patchFns_self m7FidMergedBase_sigs ?_ ?_ m7FidRepls_sigs
  · intro e f hnm
    dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt, m7FidBeforeRows, m7FidBefores,
      FullM7FidelityCore.fidCorePatchBefores, FullM7FidelitySearch.fidSearchPatchBefores]
    rw [hnm]
    by_cases h1 : ("full_bva_filter_row" == f.name) <;>
      by_cases h2 : ("full_reorder_queue_m7" == f.name) <;>
      by_cases h3 : ("full_search_m6" == f.name)
    · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
    · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
    · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h3).symm) (by decide)
    · have h1e := beq_iff_eq.mp h1; rw [← h1e]; simp; rfl
    · exact absurd ((beq_iff_eq.mp h2).trans (beq_iff_eq.mp h3).symm) (by decide)
    · have h2e := beq_iff_eq.mp h2; rw [← h2e]; simp; rfl
    · have h3e := beq_iff_eq.mp h3; rw [← h3e]; simp; rfl
    · have h1n : "full_bva_filter_row" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
      have h2n : "full_reorder_queue_m7" ≠ f.name := fun h => h2 (beq_iff_eq.mpr h)
      have h3n : "full_search_m6" ≠ f.name := fun h => h3 (beq_iff_eq.mpr h)
      simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n, m8cp_sym_ne_beq h3n]
  · intro r hr e he hnm
    rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
    have hsig0 : FullM8CoreParity.rowSig (match mfExtraBaseRows.find? (·.name == e0.name) with
        | none => e0 | some e2 => mergeEntry e0 e2) = FullM8CoreParity.rowSig e0 := by
      cases mfExtraBaseRows.find? (·.name == e0.name) <;> rfl
    rw [hsig0]; exact m7FidReplRows_sigs_match r hr e0 he0 (hnm.trans (congrArg Prod.fst hsig0))

private theorem m7FidFlatTable_nodup : (m7FidFlatTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup m7FidFlatTable_sigs m7FidelityFns_names_nodup

private theorem m7FidFlatTable_noExit : m7FidFlatTable.all SpecEntry.noExit = true := by
  unfold m7FidFlatTable
  refine patchRows_noExit (rRows := m7FidReplRows) (bRows := m7FidBeforeRows)
    (rs := m7FidMergedBase) m7FidMergedBase_noExit ?_ ?_
  · rw [List.all_eq_true]; intro r hr
    simp only [m7FidReplRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mfExtraRows_noExit _ (List.getElem_mem _)
  · intro p hp
    simp only [m7FidBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact List.all_eq_true.mpr (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact mfExtraRows_noExit _ (List.getElem_mem _))

private theorem m7FidFlatTable_iff {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    Env.ofTable m7FidFlatTable f as bs xs m Q X ↔ m7FidelityEnv f as bs xs m Q X := by
  have hReplSigs : ∀ r ∈ m7FidReplRows, ∀ e ∈ m7FidMergedBase,
      r.name = e.name → fRowSig r = fRowSig e := by
    intro r hr e he hnm
    rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
    have hsig0 : fRowSig (match mfExtraBaseRows.find? (·.name == e0.name) with
        | none => e0 | some e2 => mergeEntry e0 e2) = fRowSig e0 := by
      cases mfExtraBaseRows.find? (·.name == e0.name) <;> rfl
    rw [hsig0]; exact m7FidReplRows_sigs_match r hr e0 he0 (hnm.trans (congrArg Prod.fst hsig0))
  have hBefDisj : ∀ p ∈ m7FidBeforeRows, ∀ b ∈ p.2,
      b.name ∉ m7FidMergedBase.map SpecEntry.name := by
    rw [m7FidMergedBase, mergeRows_names]
    have hnd := congrArg (List.map Prod.fst) m7FidBaseTable_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hnd
    change m7FidBaseTable.map SpecEntry.name = FullM7.m7Fns.map Fn.name at hnd
    rw [hnd]
    intro p hp b hb
    simp only [m7FidBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [List.mem_singleton] at hb <;> subst hb
    · exact m7Fns_not_mem_bml
    · exact m7Fns_not_mem_sift
    · exact m7Fns_not_mem_hdec
  have hrn : m7FidReplRows.map SpecEntry.name =
      ["full_vivify_tier_m6_hdr", "full_compact_needed", "full_walk_m7",
       "full_bump_analyzed_m6_hdr", "full_walk_warmup_m7", "full_walk"] := by t_kernel_rfl
  have hbn : (m7FidBeforeRows.flatMap Prod.snd).map SpecEntry.name =
      ["full_bva_match_large_fid", "full_reorder_sift_fid", "m6_hdr_decide_fid"] := by
    t_kernel_rfl
  have hReplNd : (m7FidReplRows.map SpecEntry.name).Nodup := by rw [hrn]; decide
  have hBefKeyNd : (m7FidBeforeRows.map Prod.fst).Nodup := by decide
  constructor
  · intro h
    rcases ofTable_patchRows_elim hReplSigs hBefDisj h with hr | hb | ⟨hnr, hnb, hmrg⟩
    · rcases hr with ⟨r, hr, rfl, has, hrs, hcast⟩
      have hr_ex : r ∈ mfExtraRows := by
        simp only [m7FidReplRows, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact List.getElem_mem _
      exact M7FidelityEnv.extra (ofTable_of_cast hr_ex mfExtraRows_nodup rfl has hrs hcast)
    · rcases hb with ⟨p, hp, b, hb_p, rfl, has, hrs, hcast⟩
      have hb_ex : b ∈ mfExtraRows := by
        simp only [m7FidBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp only [List.mem_singleton] at hb_p <;> subst hb_p <;>
          exact List.getElem_mem _
      exact M7FidelityEnv.extra (ofTable_of_cast hb_ex mfExtraRows_nodup rfl has hrs hcast)
    · rcases (ofTable_mergeRows_iff m7FidBaseTable_nodup mfExtraBaseRows_nodup
          m7FidBaseTable_noExit mfExtraBaseRows_noExit mfExtraBaseRows_in_m7Base).mp hmrg with
        hb0 | hex0
      · refine M7FidelityEnv.base (fun hexcl => ?_) hb0
        rw [hrn] at hnr; rw [hbn] at hnb
        simp only [mfExclNames, List.mem_cons, List.not_mem_nil, or_false] at hexcl
        rcases hexcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd (by decide) hnr | exact absurd (by decide) hnb
      · obtain ⟨e, he, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim hex0
        exact M7FidelityEnv.extra (ofTable_of_cast
          (by rw [mfExtraRows]; exact List.mem_append_left _ he)
          mfExtraRows_nodup hnm has hrs hcast)
  · intro h
    cases h with
    | base hne hb0 =>
      have hmrg := (ofTable_mergeRows_iff m7FidBaseTable_nodup mfExtraBaseRows_nodup
        m7FidBaseTable_noExit mfExtraBaseRows_noExit mfExtraBaseRows_in_m7Base).mpr (Or.inl hb0)
      obtain ⟨e, he, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim hmrg
      have hnr : e.name ∉ m7FidReplRows.map SpecEntry.name := by
        rw [hnm, hrn]; intro hm; apply hne
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ofTable_of_cast (mem_patchRows_of_base he hnr) m7FidFlatTable_nodup hnm has hrs hcast
    | extra hex =>
      obtain ⟨e, he, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim hex
      rw [mfExtraRows, List.mem_append] at he
      rcases he with heBase | heTail
      · have hmrg := (ofTable_mergeRows_iff m7FidBaseTable_nodup mfExtraBaseRows_nodup
          m7FidBaseTable_noExit mfExtraBaseRows_noExit mfExtraBaseRows_in_m7Base).mpr
            (Or.inr (ofTable_of_cast heBase mfExtraBaseRows_nodup hnm has hrs hcast))
        obtain ⟨e', he', hnm', has', hrs', hcast'⟩ := env_ofTable_mem_elim hmrg
        have hnr : e'.name ∉ m7FidReplRows.map SpecEntry.name := by
          have hdisj : (mfExtraBaseRows.map SpecEntry.name).all
              (fun nm => !((m7FidReplRows.map SpecEntry.name).contains nm)) = true := by
            rw [hrn]; t_kernel_rfl
          have hmem_eb : e'.name ∈ mfExtraBaseRows.map SpecEntry.name := by
            rw [hnm', ← hnm]; exact List.mem_map_of_mem heBase
          have h1 := List.all_eq_true.mp hdisj e'.name hmem_eb
          simp only [Bool.not_eq_true'] at h1; simpa using h1
        exact ofTable_of_cast (mem_patchRows_of_base he' hnr) m7FidFlatTable_nodup
          hnm' has' hrs' hcast'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at heTail
        rcases heTail with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs mf_idx_217
          exact ofTable_of_cast (mem_patchRows_of_repl hReplNd
            (by dsimp only [m7FidReplRows]; exact List.mem_cons_self) he0
            (congrArg Prod.fst hs0).symm) m7FidFlatTable_nodup hnm has hrs hcast
        · obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs mf_idx_353
          exact ofTable_of_cast (mem_patchRows_of_repl hReplNd
            (by dsimp only [m7FidReplRows]; exact List.mem_cons_of_mem _ List.mem_cons_self) he0
            (congrArg Prod.fst hs0).symm) m7FidFlatTable_nodup hnm has hrs hcast
        · obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs mf_idx_164
          exact ofTable_of_cast (mem_patchRows_of_repl hReplNd
            (by dsimp only [m7FidReplRows]; iterate 2 apply List.mem_cons_of_mem
                exact List.mem_cons_self) he0
            (congrArg Prod.fst hs0).symm) m7FidFlatTable_nodup hnm has hrs hcast
        · obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs mf_idx_118
          exact ofTable_of_cast (mem_patchRows_of_repl hReplNd
            (by dsimp only [m7FidReplRows]; iterate 3 apply List.mem_cons_of_mem
                exact List.mem_cons_self) he0
            (congrArg Prod.fst hs0).symm) m7FidFlatTable_nodup hnm has hrs hcast
        · have hm166 : FullM7.m7Fns[166]?.map Fn.sig = some ("full_walk_warmup_m7", [i64], []) := by
            rw [mf_idx_166]; rfl
          obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs hm166
          exact ofTable_of_cast (mem_patchRows_of_repl hReplNd
            (by dsimp only [m7FidReplRows]; iterate 4 apply List.mem_cons_of_mem
                exact List.mem_cons_self) he0
            (congrArg Prod.fst hs0).symm) m7FidFlatTable_nodup hnm has hrs hcast
        · have hm168 : FullM7.m7Fns[168]?.map Fn.sig = some ("full_walk", [i64], []) := by
            rw [mf_idx_168]; rfl
          obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs hm168
          exact ofTable_of_cast (mem_patchRows_of_repl hReplNd
            (by dsimp only [m7FidReplRows]; iterate 5 apply List.mem_cons_of_mem
                exact List.mem_cons_self) he0
            (congrArg Prod.fst hs0).symm) m7FidFlatTable_nodup hnm has hrs hcast
        · obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs m7_idx_347
          exact ofTable_of_cast (mem_patchRows_of_before hBefKeyNd List.mem_cons_self
            List.mem_cons_self he0 (congrArg Prod.fst hs0)) m7FidFlatTable_nodup hnm has hrs hcast
        · obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs m7_idx_368
          exact ofTable_of_cast (mem_patchRows_of_before hBefKeyNd
            (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self he0
            (congrArg Prod.fst hs0)) m7FidFlatTable_nodup hnm has hrs hcast
        · obtain ⟨e0, he0, hs0⟩ := row_of_idx m7FidMergedBase_sigs m7_idx_405
          exact ofTable_of_cast (mem_patchRows_of_before hBefKeyNd
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            List.mem_cons_self he0 (congrArg Prod.fst hs0)) m7FidFlatTable_nodup hnm has hrs hcast

private theorem m8V12FlatTable_sigs_m7 :
    m8V12FlatTable.map fRowSig = m7FidelityFns.map Fn.sig := by
  rw [m8V12FlatTable, mergeRows_sigs, m7FidFlatTable_sigs]

private theorem m8V12FlatTable_sigs :
    m8V12FlatTable.map fRowSig = m8FidV12Fns.map Fn.sig := by
  rw [m8V12FlatTable_sigs_m7]; exact m8FidV12Fns_sigs.symm

private theorem m8V12FlatTable_nodup : (m8V12FlatTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup m8V12FlatTable_sigs m8FidV12Fns_names_nodup

private theorem m8V12FlatTable_noExit : m8V12FlatTable.all SpecEntry.noExit = true := by
  unfold m8V12FlatTable
  exact mergeRows_noExit m7FidFlatTable_noExit (by decide)

private theorem m8V12ExtraRows_in_m7Flat :
    ∀ e2 ∈ m8V12ExtraRows, ∃ e1 ∈ m7FidFlatTable, fRowSig e1 = fRowSig e2 := by
  intro e2 he2
  simp only [m8V12ExtraRows, List.mem_cons, List.not_mem_nil, or_false] at he2
  rcases he2 with rfl | rfl | rfl
  · exact row_of_idx m7FidFlatTable_sigs m7f_idx_257
  · exact row_of_idx m7FidFlatTable_sigs m7f_idx_258
  · exact row_of_idx m7FidFlatTable_sigs m7f_idx_260

private theorem m8V12FlatTable_iff {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    Env.ofTable m8V12FlatTable f as bs xs m Q X ↔ m8FidV12Env f as bs xs m Q X := by
  have hExNd : (m8V12ExtraRows.map SpecEntry.name).Nodup := by decide
  have hExNo : m8V12ExtraRows.all SpecEntry.noExit = true := by decide
  rw [m8V12FlatTable, ofTable_mergeRows_iff m7FidFlatTable_nodup hExNd m7FidFlatTable_noExit hExNo
    m8V12ExtraRows_in_m7Flat, m7FidFlatTable_iff]
  constructor
  · rintro (hm7 | hex)
    · exact .base hm7
    · obtain ⟨e, he, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim hex
      simp only [m8V12ExtraRows, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;>
        (dsimp only at hnm has hrs; subst hnm; subst has; subst hrs)
      · exact .enqVar xs m Q X
          (by simpa only [SpecEntry.cast, SpecEntry.eff, ite_true, m8CongEnqVarSpec] using hcast)
      · exact .evalGate xs m Q X
          (by simpa only [SpecEntry.cast, SpecEntry.eff, ite_true, m8CongEvalGateSpec] using hcast)
      · exact .worklist xs m Q X
          (by simpa only [SpecEntry.cast, SpecEntry.eff, ite_true, m8CongWorklistSpec] using hcast)
  · intro h
    cases h with
    | base hm7 => exact Or.inl hm7
    | enqVar _ _ _ _ hs =>
      exact Or.inr (Env.ofTable_of_mem
        (e := ⟨"full_cong_enq_var", [i64, i64, i32], [], m8CongEnqVarSpec, true⟩)
        List.mem_cons_self hExNd (by simp only [SpecEntry.eff, ite_true]; exact hs))
    | evalGate _ _ _ _ hs =>
      exact Or.inr (Env.ofTable_of_mem
        (e := ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64],
          m8CongEvalGateSpec, true⟩)
        (List.mem_cons_of_mem _ List.mem_cons_self) hExNd
        (by simp only [SpecEntry.eff, ite_true]; exact hs))
    | worklist _ _ _ _ hs =>
      exact Or.inr (Env.ofTable_of_mem
        (e := ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], m8CongWorklistSpec, true⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hExNd
        (by simp only [SpecEntry.eff, ite_true]; exact hs))

private theorem m8SwFlatTable_sigs :
    m8SwFlatTable.map fRowSig = m8FidV123t2Fns.map Fn.sig := by
  have hEq : m8FidV123t2Fns =
      PatchModule.patchFns m8SweepV2Repls m8FidV123t2Befores m8FidV12Fns := by
    rw [m8FidV123t2Fns_eq_patch]
    unfold mfPatchFns PatchModule.patchFns
    induction m8FidV12Fns with
    | nil => rfl
    | cons a t ih =>
      simp only [List.flatMap_cons]
      have hi : PatchModule.patchInsAt m8FidV123t2Befores a =
          mfPatchInsAt m8FidV123t2Befores a := by
        dsimp only [PatchModule.patchInsAt, mfPatchInsAt, m8FidV123t2Befores]
        by_cases h1 : ("full_sweep_dense_m6" == a.name)
        · have h1e := beq_iff_eq.mp h1; rw [← h1e]
          simp only [beq_self_eq_true, List.find?, List.filterMap_cons, ↓reduceIte,
            List.filterMap_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
        · have h1n : "full_sweep_dense_m6" ≠ a.name := fun h => h1 (beq_iff_eq.mpr h)
          simp only [m8cp_sym_ne_beq h1n, List.find?, List.filterMap_cons, Bool.false_eq_true,
            ↓reduceIte, List.filterMap_nil, List.flatten_nil]
      rw [hi, ih]
  have hSwSigs : m8SweepEnvRows.map fRowSig = m8SweepV2Helpers.map Fn.sig := by t_kernel_rfl
  rw [m8SwFlatTable, hEq]
  refine patchRows_sigs_eq_patchFns_self m8V12FlatTable_sigs ?_ ?_ ?_
  · intro e f hnm
    dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt, m8FidV123t2Befores]
    rw [hnm]
    by_cases h1 : ("full_sweep_dense_m6" == f.name)
    · have h1e := beq_iff_eq.mp h1; rw [← h1e]
      simp only [List.find?, beq_self_eq_true]; exact hSwSigs
    · have h1n : "full_sweep_dense_m6" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
      simp only [List.find?, m8cp_sym_ne_beq h1n, List.map_nil]
  · intro r hr e he hnm
    rcases List.mem_singleton.mp hr with rfl
    have he_sig : fRowSig e ∈ m8V12FlatTable.map fRowSig := List.mem_map_of_mem he
    rw [m8V12FlatTable_sigs_m7] at he_sig
    rcases List.mem_map.mp he_sig with ⟨g, hg, hge⟩
    have hs := sig_eq_of_idx m7FidelityFns_names_nodup m7f_idx_172 hg
      (hnm.trans (congrArg Prod.fst hge).symm)
    change FullM8CoreParity.rowSig m8SwExtPush2Row = fRowSig e
    rw [← hge, hs]; rfl
  · intro r hr f hf hnm
    rcases List.mem_singleton.mp hr with rfl
    have hf_sig : f.sig ∈ m8FidV12Fns.map Fn.sig := List.mem_map_of_mem hf
    rw [m8FidV12Fns_sigs] at hf_sig
    rcases List.mem_map.mp hf_sig with ⟨g, hg, hgf⟩
    have hs := sig_eq_of_idx m7FidelityFns_names_nodup m7f_idx_299 hg
      (hnm.trans (congrArg Prod.fst hgf).symm)
    rw [← hgf, hs]; rfl

private theorem m8SwFlatTable_nodup : (m8SwFlatTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup m8SwFlatTable_sigs m8FidV123t2Fns_names_nodup

private theorem m8SwFlatTable_noExit : m8SwFlatTable.all SpecEntry.noExit = true := by
  unfold m8SwFlatTable
  refine patchRows_noExit (rRows := [m8SwExtPush2Row])
    (bRows := [("full_sweep_dense_m6", m8SweepEnvRows)]) (rs := m8V12FlatTable)
    m8V12FlatTable_noExit rfl fun p hp => ?_
  rcases List.mem_singleton.mp hp with rfl
  exact List.all_eq_true.mpr m8SweepEnvRows_noExit

private theorem m8SwFlatTable_iff {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    Env.ofTable m8SwFlatTable f as bs xs m Q X ↔ m8FidV123t2Env f as bs xs m Q X := by
  have hReplSigs : ∀ r ∈ ([m8SwExtPush2Row] : List SpecEntry), ∀ e ∈ m8V12FlatTable,
      r.name = e.name → fRowSig r = fRowSig e := by
    intro r hr e he hnm
    rcases List.mem_singleton.mp hr with rfl
    have he_sig : fRowSig e ∈ m8V12FlatTable.map fRowSig := List.mem_map_of_mem he
    rw [m8V12FlatTable_sigs_m7] at he_sig
    rcases List.mem_map.mp he_sig with ⟨g, hg, hge⟩
    have hs := sig_eq_of_idx m7FidelityFns_names_nodup m7f_idx_172 hg
      (hnm.trans (congrArg Prod.fst hge).symm)
    change FullM8CoreParity.rowSig m8SwExtPush2Row = fRowSig e
    rw [← hge, hs]; rfl
  have hBefDisj : ∀ p ∈ ([("full_sweep_dense_m6", m8SweepEnvRows)] :
      List (Sym × List SpecEntry)),
      ∀ b ∈ p.2, b.name ∉ m8V12FlatTable.map SpecEntry.name := by
    have hn : m8V12FlatTable.map SpecEntry.name = m8FidV12Fns.map Fn.name := by
      have hm := congrArg (List.map Prod.fst) m8V12FlatTable_sigs
      simpa only [List.map_map, Function.comp_def, Fn.sig] using hm
    rw [hn]
    intro p hp b hb hmem
    rcases List.mem_singleton.mp hp with rfl
    rcases List.mem_map.mp hmem with ⟨g, hg, hgn⟩
    exact m8Sw_not_mem_v12 hg (hgn ▸ List.mem_map_of_mem hb)
  constructor
  · intro h
    rcases ofTable_patchRows_elim hReplSigs hBefDisj h with hr | hb | ⟨hnr, _, hv12⟩
    · rcases hr with ⟨r, hr, rfl, has, hrs, hcast⟩
      rcases List.mem_singleton.mp hr with rfl
      dsimp only [m8SwExtPush2Row] at has hrs hcast
      cases has; cases hrs
      exact .extPush2 (by
        simpa only [SpecEntry.cast, SpecEntry.eff, ite_true, m6ExtendPush2Spec,
          SafetySlice.spec] using hcast)
    · rcases hb with ⟨p, hp, b, hb_p, rfl, has, hrs, hcast⟩
      rcases List.mem_singleton.mp hp with rfl
      exact .sweep (ofTable_of_cast hb_p m8SweepEnvRows_nodup rfl has hrs hcast)
    · exact .base (fun hex => hnr (by simpa [m8SwExclNames, m8SwExtPush2Row] using hex))
        (m8V12FlatTable_iff.mp hv12)
  · intro h
    cases h with
    | base hne hv12 =>
      obtain ⟨e, he, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim (m8V12FlatTable_iff.mpr hv12)
      have hnr : e.name ∉ ([m8SwExtPush2Row] : List SpecEntry).map SpecEntry.name := by
        simpa [m8SwExtPush2Row, m8SwExclNames, hnm] using hne
      exact ofTable_of_cast (mem_patchRows_of_base he hnr) m8SwFlatTable_nodup hnm has hrs hcast
    | extPush2 hs =>
      obtain ⟨e0, he0, hs0⟩ := row_of_idx m8V12FlatTable_sigs_m7 m7f_idx_172
      have hmem : m8SwExtPush2Row ∈ m8SwFlatTable :=
        mem_patchRows_of_repl (by decide) List.mem_cons_self he0 (congrArg Prod.fst hs0).symm
      exact Env.ofTable_of_mem hmem m8SwFlatTable_nodup (by
        simpa only [m8SwExtPush2Row, SpecEntry.eff, ite_true, m6ExtendPush2Spec,
          SafetySlice.spec] using hs)
    | sweep hsw =>
      obtain ⟨b, hb, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim hsw
      obtain ⟨e0, he0, hs0⟩ := row_of_idx m8V12FlatTable_sigs_m7 m7f_idx_299
      have hmem : b ∈ m8SwFlatTable :=
        mem_patchRows_of_before (by decide) List.mem_cons_self hb he0 (congrArg Prod.fst hs0)
      exact ofTable_of_cast hmem m8SwFlatTable_nodup hnm has hrs hcast

private theorem m8FidV123t2_ext_nil : m8FidV123t2Module.externs = [] := by
  t_kernel_rfl

private theorem m8SwFlat_moduleOk : ModuleOk (Env.ofTable m8SwFlatTable) m8FidV123t2Module := by
  refine ⟨m8FidV123t2_moduleOk.nodup, fun pre fn post hsplit => ?_⟩
  have ⟨hwf, hcalls, hwp⟩ := m8FidV123t2_moduleOk.fnsOk pre fn post hsplit
  refine ⟨hwf, hcalls, fun xs m Q X hsp => ?_⟩
  have hca := hcalls
  rw [m8FidV123t2_ext_nil, FullM8SweepV2.m8FidV123t2_noExit, List.map_nil, List.append_nil] at hca
  exact wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
    hca (fun _ _ _ _ _ _ _ _ hg => m8SwFlatTable_iff.mpr hg) m
    (hwp xs m Q X (m8SwFlatTable_iff.mp hsp))

/-! ## 4. Purified `469`-Row `fidBaseSpecTable` & Flat `fidBaseEnv` -/

/-- Purified `17`-row BVE helper specifications (omits `D-11` XOR & `D-22` BCE). -/
def fidBveHelperRows : List SpecEntry :=
  [ ⟨"full_bve_find_equiv_m8", [i64, i32, i32], [.bool], m8BveFindEquivSpec, true⟩
  , ⟨"full_bve_find_and_m8", [i64, i32, i32, i32], [.bool], m8BveFindAndSpec, true⟩
  , ⟨"full_bve_match_tern_m8", [i64, i32, i32, i32, i32, i32], [i32], m8BveMatchTernSpec, true⟩
  , ⟨"full_bve_find_ite_side_m8", [i64, i32, i32, i32, .bool], [.bool],
      m8BveFindIteSideSpec, true⟩
  , ⟨"full_bve_find_ite_m8", [i64, i32, i32, i32], [.bool], m8BveFindIteSpec, true⟩
  , ⟨"full_k6_watch_m8", [i64, i32, i32, i32, i32], [], m8K6WatchSpec, true⟩
  , ⟨"full_k6_assign_m8", [i64, i32, i32], [], m8K6AssignSpec, true⟩
  , ⟨"full_k6_mtf_m8", [i64, i32], [], m8K6MtfSpec, true⟩
  , ⟨"full_k6_backtrack_m8", [i64, i32], [], m8K6BacktrackSpec, true⟩
  , ⟨"full_k6_prop_m8", [i64], [i32], m8K6PropSpec, true⟩
  , ⟨"full_k6_ana_cl_m8", [i64, i32, i32], [], m8K6AnaClSpec, true⟩
  , ⟨"full_k6_analyze_m8", [i64, i32], [.bool], m8K6AnalyzeSpec, true⟩
  , ⟨"full_k6_solve_m8", [i64, i32], [i64], m8K6SolveSpec, true⟩
  , ⟨"full_k6_core_m8", [i64], [], m8K6CoreSpec, true⟩
  , ⟨"full_k6_extract_and_solve_m8", [i64, i32, i32, i32, .bool, i32], [.bool],
      m8K6ExtractSolveSpec, true⟩
  , ⟨"full_bve_def_k6_m8", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩
  , ⟨"full_bve_gates_fid", [i64, i32, i32, i32], [], m8BveGatesSpec, true⟩ ]

theorem fidBveHelperRows_sigs :
    fidBveHelperRows.map (fun e => (e.name, e.as, e.rs)) = fidBveHelpers.map Fn.sig := by
  t_kernel_rfl

theorem fidBveHelperRows_noExit : fidBveHelperRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidBveHelperRows_nodup : (fidBveHelperRows.map SpecEntry.name).Nodup := by
  decide

private def fidBaseReplRows : List SpecEntry :=
  [ ⟨"full_min_shrink_m6", [i64], [], m8MinShrinkSpec, true⟩
  , ⟨"full_min_shrink", [i64], [], m8MinShrinkSpec, true⟩
  , ⟨"full_bve_var_key_m7", [i64, i32], [i64], m8BveVarKeySpec, true⟩
  , ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], m8BveHeapPushSpec, true⟩ ]

private def fidBaseBeforeRows : List (Sym × List SpecEntry) :=
  [ ("full_min_shrink_m6", m8MinHelperRows)
  , ("full_bve_var_m7", fidBveHelperRows) ]

/-- Canonical flattened `469`-row specification table for `FullFidelityBase.fidBaseModule`. -/
def fidBaseSpecTable : List SpecEntry :=
  PatchModule.patchRows fidBaseReplRows fidBaseBeforeRows m8SwFlatTable

/-- Canonical flat table environment for `fidBaseModule` (`469` fns, `0` inductive wrappers). -/
def fidBaseEnv : Env := Env.ofTable fidBaseSpecTable

private theorem fidBase_replSigs :
    ∀ r ∈ fidBaseRepls, ∀ g ∈ m8FidV123t2Fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  simp only [fidBaseRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_135 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_374 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_375 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_415 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_438 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_440 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_444 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_334 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_217 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_243 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_377 hg hnm).symm
  · exact (sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_378 hg hnm).symm

private theorem fidBase_not_in_sw :
    ∀ nm ∈ (fidBaseBefores.flatMap Prod.snd).map Fn.name, nm ∉ m8FidV123t2Fns.map Fn.name := by
  have hmin : (m8MinHelpers.map Fn.name).all
      (fun nm => !(m8FidV123t2Fns.map Fn.name).contains nm) = true := by
    rw [List.all_eq_true]
    intro nm hm
    have hm' : nm ∈ m8MinHelperRows.map SpecEntry.name := by
      have hs := congrArg (List.map Prod.fst) m8MinHelperRows_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hs
      change m8MinHelperRows.map SpecEntry.name = m8MinHelpers.map Fn.name at hs
      exact hs ▸ hm
    rcases List.mem_map.mp hm' with ⟨e, he, rfl⟩
    simp only [Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr fun hc =>
      m8cp_min_help_not_in_sw e he (List.contains_iff_mem.mp hc)
  have hbve_sub : ∀ nm ∈ fidBveHelpers.map Fn.name,
      nm = "full_bve_gates_fid" ∨ nm ∈ m8BveHelperRows.map SpecEntry.name := by
    have hsn : fidBveHelpers.map Fn.name = fidBveHelperRows.map SpecEntry.name := by
      have hs := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hs
      exact hs.symm
    intro nm hm
    rw [hsn] at hm
    have hn1 : nm ∈ ["full_bve_find_equiv_m8", "full_bve_find_and_m8", "full_bve_match_tern_m8",
        "full_bve_find_ite_side_m8", "full_bve_find_ite_m8", "full_k6_watch_m8",
        "full_k6_assign_m8", "full_k6_mtf_m8", "full_k6_backtrack_m8", "full_k6_prop_m8",
        "full_k6_ana_cl_m8", "full_k6_analyze_m8", "full_k6_solve_m8", "full_k6_core_m8",
        "full_k6_extract_and_solve_m8", "full_bve_def_k6_m8", "full_bve_gates_fid"] := by
      simpa [fidBveHelperRows] using hm
    by_cases hg : nm = "full_bve_gates_fid"
    · exact Or.inl hg
    · right
      have hk : (["full_bve_find_equiv_m8", "full_bve_find_and_m8", "full_bve_match_tern_m8",
          "full_bve_find_ite_side_m8", "full_bve_find_ite_m8", "full_k6_watch_m8",
          "full_k6_assign_m8", "full_k6_mtf_m8", "full_k6_backtrack_m8", "full_k6_prop_m8",
          "full_k6_ana_cl_m8", "full_k6_analyze_m8", "full_k6_solve_m8", "full_k6_core_m8",
          "full_k6_extract_and_solve_m8", "full_bve_def_k6_m8"] : List Sym).all
          (fun s => (m8BveHelperRows.map SpecEntry.name).contains s) = true := by decide
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn1
      have hrest : nm ∈ (["full_bve_find_equiv_m8", "full_bve_find_and_m8",
          "full_bve_match_tern_m8", "full_bve_find_ite_side_m8", "full_bve_find_ite_m8",
          "full_k6_watch_m8", "full_k6_assign_m8", "full_k6_mtf_m8", "full_k6_backtrack_m8",
          "full_k6_prop_m8", "full_k6_ana_cl_m8", "full_k6_analyze_m8", "full_k6_solve_m8",
          "full_k6_core_m8", "full_k6_extract_and_solve_m8", "full_bve_def_k6_m8"] :
          List Sym) := by
        rcases hn1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact absurd rfl hg | decide
      exact List.contains_iff_mem.mp (List.all_eq_true.mp hk nm hrest)
  intro nm hm hsw
  have hbm : nm ∈ m8MinHelpers.map Fn.name ++ fidBveHelpers.map Fn.name := by
    simpa [fidBaseBefores] using hm
  rcases List.mem_append.mp hbm with hm1 | hm2
  · have h1 := List.all_eq_true.mp hmin nm hm1
    simp only [Bool.not_eq_true'] at h1
    exact Bool.noConfusion (h1.symm.trans (List.contains_iff_mem.mpr hsw))
  · rcases hbve_sub nm hm2 with rfl | hm2'
    · exact sw_not_mem_gates hsw
    · rcases List.mem_map.mp hm2' with ⟨e, he, rfl⟩
      exact m8cp_bve_help_not_in_sw m8BveHook e he hsw

private theorem patchInsAt_mem_flatMap {befores : List (Sym × List Fn)} {f b : Fn}
    (hb : b ∈ PatchModule.patchInsAt befores f) :
    b ∈ befores.flatMap Prod.snd := by
  unfold PatchModule.patchInsAt at hb
  cases h : befores.find? (·.1 == f.name) with
  | none => simp [h] at hb
  | some p =>
    simp only [h] at hb
    exact List.mem_flatMap.mpr ⟨p, List.mem_of_find?_eq_some h, hb⟩

private theorem patchInsAt_nodup_flatMap {befores : List (Sym × List Fn)}
    (hBef : ((befores.flatMap Prod.snd).map Fn.name).Nodup) (f : Fn) :
    ((PatchModule.patchInsAt befores f).map Fn.name).Nodup := by
  unfold PatchModule.patchInsAt
  cases h : befores.find? (·.1 == f.name) with
  | none => simp
  | some p =>
    have hp := List.mem_of_find?_eq_some h
    have hnd : ∀ {xs : List (Sym × List Fn)},
        ((xs.flatMap Prod.snd).map Fn.name).Nodup → ∀ q ∈ xs, (q.2.map Fn.name).Nodup := by
      intro xs hx q hq
      induction xs with
      | nil => nomatch hq
      | cons hd tl ih =>
        simp only [List.flatMap_cons, List.map_append, List.nodup_append] at hx
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hx.1
        · exact ih hx.2.1 hq
    exact hnd hBef p hp

private theorem mem_patchFns_names_elim {repls fs : List Fn} {befores : List (Sym × List Fn)}
    {nm : Sym} (h : nm ∈ (PatchModule.patchFns repls befores fs).map Fn.name) :
    nm ∈ fs.map Fn.name ∨ ∃ g ∈ fs, ∃ b ∈ PatchModule.patchInsAt befores g, b.name = nm := by
  rcases List.mem_map.mp h with ⟨x, hx, rfl⟩
  simp only [PatchModule.patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton] at hx
  rcases hx with ⟨g, hg, hbef | rfl⟩
  · exact Or.inr ⟨g, hg, x, hbef, rfl⟩
  · left
    have hnm : ((repls.find? (·.name == g.name)).getD g).name = g.name := by
      cases hf : repls.find? (·.name == g.name) with
      | none => rfl
      | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == g.name) hf)
    rw [hnm]
    exact List.mem_map_of_mem hg

private theorem patchInsAt_disj_of_ne {befores : List (Sym × List Fn)}
    (hBef : ((befores.flatMap Prod.snd).map Fn.name).Nodup)
    {f g b₁ b₂ : Fn} (hne : f.name ≠ g.name)
    (hb₁ : b₁ ∈ PatchModule.patchInsAt befores f)
    (hb₂ : b₂ ∈ PatchModule.patchInsAt befores g) : b₁.name ≠ b₂.name := by
  have find_eq : ∀ {x b : Fn}, b ∈ PatchModule.patchInsAt befores x →
      ∃ ins, befores.find? (·.1 == x.name) = some (x.name, ins) ∧ b ∈ ins := by
    intro x b hb
    unfold PatchModule.patchInsAt at hb
    cases h : befores.find? (·.1 == x.name) with
    | none => simp [h] at hb
    | some p =>
      simp only [h] at hb
      have hk := beq_iff_eq.mp (List.find?_some (p := fun q : Sym × List Fn => q.1 == x.name) h)
      cases p with
      | mk k ins => dsimp only at hk; subst hk; exact ⟨ins, rfl, hb⟩
  obtain ⟨ins₁, hf₁, hm₁⟩ := find_eq hb₁
  obtain ⟨ins₂, hf₂, hm₂⟩ := find_eq hb₂
  have hp₁ := List.mem_of_find?_eq_some hf₁
  have hp₂ := List.mem_of_find?_eq_some hf₂
  have aux : ∀ {xs : List (Sym × List Fn)},
      ((xs.flatMap Prod.snd).map Fn.name).Nodup →
      ∀ {k₁ k₂ : Sym} {i₁ i₂ : List Fn},
        (k₁, i₁) ∈ xs → (k₂, i₂) ∈ xs → k₁ ≠ k₂ →
        ∀ x ∈ i₁, ∀ y ∈ i₂, x.name ≠ y.name := by
    intro xs hx k₁ k₂ i₁ i₂ h1 h2 hne' x hx' y hy' hxy
    induction xs with
    | nil => nomatch h1
    | cons hd tl ih =>
      simp only [List.flatMap_cons, List.map_append, List.nodup_append] at hx
      rcases List.mem_cons.mp h1 with h1 | h1 <;> rcases List.mem_cons.mp h2 with h2 | h2
      · exact absurd ((congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm) hne'
      · rw [← h1] at hx
        exact hx.2.2 x.name (List.mem_map_of_mem hx') y.name
          (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨_, h2, hy'⟩)) hxy
      · rw [← h2] at hx
        exact hx.2.2 y.name (List.mem_map_of_mem hy') x.name
          (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨_, h1, hx'⟩)) hxy.symm
      · exact ih hx.2.1 h1 h2
  exact aux hBef hp₁ hp₂ hne b₁ hm₁ b₂ hm₂

private theorem patchFns_names_nodup {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hFs : (fs.map Fn.name).Nodup)
    (hBef : ((befores.flatMap Prod.snd).map Fn.name).Nodup)
    (hDisj : ∀ b ∈ befores.flatMap Prod.snd, b.name ∉ fs.map Fn.name) :
    ((PatchModule.patchFns repls befores fs).map Fn.name).Nodup := by
  induction fs with
  | nil => simp [PatchModule.patchFns]
  | cons f fs ih =>
    simp only [List.map_cons, List.nodup_cons] at hFs
    have hDisjTail : ∀ b ∈ befores.flatMap Prod.snd, b.name ∉ fs.map Fn.name := fun b hb hm =>
      hDisj b hb (List.mem_cons_of_mem _ hm)
    have ihNd := ih hFs.2 hDisjTail
    simp only [PatchModule.patchFns, List.flatMap_cons, List.map_append, List.map_singleton]
    have hreplNm : ((repls.find? (·.name == f.name)).getD f).name = f.name := by
      cases hf : repls.find? (·.name == f.name) with
      | none => rfl
      | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) hf)
    rw [hreplNm]
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨patchInsAt_nodup_flatMap hBef f,
      (by simp : ([f.name] : List Sym).Nodup), fun nm1 hm1 nm2 hm2 heq => ?_⟩, ihNd,
      fun nm1 hm1 nm2 hm2 heq => ?_⟩
    · subst heq
      simp only [List.mem_singleton] at hm2; subst hm2
      rcases List.mem_map.mp hm1 with ⟨b, hb, hbn⟩
      exact hDisj b (patchInsAt_mem_flatMap hb) (hbn ▸ List.mem_cons_self)
    · subst heq
      rw [List.mem_append, List.mem_singleton] at hm1
      rcases mem_patchFns_names_elim hm2 with htail | ⟨g, hg, b₂, hb₂, hbn⟩
      · rcases hm1 with hm_ins | rfl
        · rcases List.mem_map.mp hm_ins with ⟨b, hb, rfl⟩
          exact hDisj b (patchInsAt_mem_flatMap hb) (List.mem_cons_of_mem _ htail)
        · exact hFs.1 htail
      · rcases hm1 with hm_ins | rfl
        · rcases List.mem_map.mp hm_ins with ⟨b₁, hb₁, hb₁n⟩
          have hfg : f.name ≠ g.name := fun h => hFs.1 (h ▸ List.mem_map_of_mem hg)
          exact patchInsAt_disj_of_ne hBef hfg hb₁ hb₂ (hb₁n.trans hbn.symm)
        · exact hDisj b₂ (patchInsAt_mem_flatMap hb₂) (hbn ▸ List.mem_cons_self)

theorem fidBaseFns_names_nodup : (fidBaseFns.map Fn.name).Nodup := by
  have hBefNd : ((fidBaseBefores.flatMap Prod.snd).map Fn.name).Nodup := by
    have hs1 : m8MinHelpers.map Fn.name = m8MinHelperRows.map SpecEntry.name := by
      have hs := congrArg (List.map Prod.fst) m8MinHelperRows_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hs
      exact hs.symm
    have hs2 : fidBveHelpers.map Fn.name = fidBveHelperRows.map SpecEntry.name := by
      have hs := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hs
      exact hs.symm
    simp only [fidBaseBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, hs1, hs2]
    refine List.nodup_append.mpr
      ⟨m8MinHelperRows_nodup, fidBveHelperRows_nodup, fun nm1 h1 nm2 h2 heq => ?_⟩
    subst heq
    have hdisj : (m8MinHelperRows.map SpecEntry.name).all
        (fun s => !(fidBveHelperRows.map SpecEntry.name).contains s) = true := by decide
    have hc := List.all_eq_true.mp hdisj nm1 h1
    simp only [Bool.not_eq_true'] at hc
    exact Bool.noConfusion (hc.symm.trans (List.contains_iff_mem.mpr h2))
  exact patchFns_names_nodup m8FidV123t2Fns_names_nodup hBefNd
    (fun b hb => fidBase_not_in_sw b.name (List.mem_map_of_mem hb))

private theorem fidBase_namesNodup : fidBaseModule.namesNodup := by
  change (fidBaseFns.map Fn.name ++ m8FidV123t2Module.externs.map Extern.name).Nodup
  rw [m8FidV123t2_ext_nil, List.map_nil, List.append_nil]
  exact fidBaseFns_names_nodup

private theorem patchFns_length_two {repls fs : List Fn} {k₁ k₂ : Sym} {i₁ i₂ : List Fn}
    (hnd : (fs.map Fn.name).Nodup) (hne : k₁ ≠ k₂)
    (hk₁ : k₁ ∈ fs.map Fn.name) (hk₂ : k₂ ∈ fs.map Fn.name) :
    (PatchModule.patchFns repls [(k₁, i₁), (k₂, i₂)] fs).length =
      fs.length + i₁.length + i₂.length := by
  have hsum : ∀ {k : Sym} {n : Nat} {xs : List Fn}, (xs.map Fn.name).Nodup →
      (xs.map fun f => if f.name == k then n else 0).sum =
        if k ∈ xs.map Fn.name then n else 0 := by
    intro k n xs hnd'
    induction xs with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.nodup_cons, List.sum_cons, List.mem_cons] at hnd' ⊢
      rw [ih hnd'.2]
      by_cases ha : a.name = k
      · have hb : (a.name == k) = true := beq_iff_eq.mpr ha
        have hnot : k ∉ t.map Fn.name := fun ht => hnd'.1 (ha ▸ ht)
        rw [hb, ite_eq_left rfl, ite_eq_right hnot, Nat.add_zero, ite_eq_left (Or.inl ha.symm)]
      · have hb : (a.name == k) = false := m8cp_sym_ne_beq ha
        have hna : ¬ (k = a.name) := fun h => ha h.symm
        rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, hna, false_or]
  have hlen : ∀ {xs : List Fn},
      (PatchModule.patchFns repls [(k₁, i₁), (k₂, i₂)] xs).length =
        xs.length + (xs.map fun f => if f.name == k₁ then i₁.length else 0).sum +
          (xs.map fun f => if f.name == k₂ then i₂.length else 0).sum := by
    intro xs
    induction xs with
    | nil => simp [PatchModule.patchFns]
    | cons a t ih =>
      rw [PatchModule.patchFns, List.flatMap_cons, List.length_append, List.length_append,
        List.length_singleton]
      change (PatchModule.patchInsAt [(k₁, i₁), (k₂, i₂)] a).length + 1 +
          (PatchModule.patchFns repls [(k₁, i₁), (k₂, i₂)] t).length = _
      rw [ih]
      have hins : (PatchModule.patchInsAt [(k₁, i₁), (k₂, i₂)] a).length =
          (if a.name == k₁ then i₁.length else 0) +
            (if a.name == k₂ then i₂.length else 0) := by
        dsimp only [PatchModule.patchInsAt]
        by_cases h1 : (k₁ == a.name) = true
        · have h1e := beq_iff_eq.mp h1
          simp [← h1e, m8cp_sym_ne_beq hne]
        · have h1n : k₁ ≠ a.name := fun h => h1 (beq_iff_eq.mpr h)
          by_cases h2 : (k₂ == a.name) = true
          · have h2e := beq_iff_eq.mp h2
            simp [← h2e, m8cp_sym_ne_beq hne, m8cp_sym_ne_beq hne.symm]
          · have h2n : k₂ ≠ a.name := fun h => h2 (beq_iff_eq.mpr h)
            simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n,
              m8cp_sym_ne_beq (Ne.symm h1n), m8cp_sym_ne_beq (Ne.symm h2n)]
      rw [hins, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons]
      omega
  rw [hlen, hsum hnd, hsum hnd, ite_eq_left hk₁, ite_eq_left hk₂]

theorem fidBaseFns_length : fidBaseFns.length = 469 := by
  have hSwLen : m8FidV123t2Fns.length = 449 := by
    have h1 := congrArg List.length m8cp_swBase_sigs
    simp only [List.length_map] at h1
    rw [← h1, swBase_len_ok]
  have hk1 : "full_min_shrink_m6" ∈ m8FidV123t2Fns.map Fn.name := by
    obtain ⟨g, hg, hsg⟩ := m8cp_sig_of_map sw_idx_135
    rw [show ("full_min_shrink_m6" : Sym) = g.name from (congrArg Prod.fst hsg).symm]
    exact List.mem_map_of_mem (List.mem_of_getElem? hg)
  have hk2 : "full_bve_var_m7" ∈ m8FidV123t2Fns.map Fn.name := by
    obtain ⟨g, hg, hsg⟩ := m8cp_sig_of_map sw_idx_374
    rw [show ("full_bve_var_m7" : Sym) = g.name from (congrArg Prod.fst hsg).symm]
    exact List.mem_map_of_mem (List.mem_of_getElem? hg)
  have hm : m8MinHelpers.length = 3 := by rfl
  have hb : fidBveHelpers.length = 17 := by rfl
  change (PatchModule.patchFns fidBaseRepls fidBaseBefores m8FidV123t2Fns).length = 469
  rw [fidBaseBefores, patchFns_length_two m8FidV123t2Fns_names_nodup (by decide) hk1 hk2,
    hSwLen, hm, hb]

private def fidBaseNewCallsOk : Bool :=
  LeanQbe.T.Module.checkFnsCallsOk [] [("full_min_mark", [i64, i32, i8], [])] [] m8MinHelpers &&
  LeanQbe.T.Module.checkFnsCallsOk []
    [("full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool])] [] fidBveHelpers &&
  m8MinShrinkM6Fn.checkCallsOk
    ([("full_sort_tmp", [i64], []), ("full_min_mark", [i64, i32, i8], [])] ++
      m8MinHelpers.map Fn.sig) [] &&
  fidBveVarM7Fn.checkCallsOk
    ([ ("full_bve_collect_m7", [i64, i32, i64, i32], [i32])
     , ("full_bve_ext_need", [i64, i32, i32], [i64])
     , ("full_bve_weaken", [i64, i32, i32, i32], [.bool])
     , ("full_set_inactive", [i64, i32, i32], [])
     , ("full_bve_commit_res", [i64, i64, i64], [i64])
     , ("full_dense_flush_units_m7", [i64], [.bool])
     , ("full_wstack_defrag", [i64], [])
     , ("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool])
     , ("full_bve_gates_m7", [i64, i32, i32, i32], []) ] ++ fidBveHelpers.map Fn.sig) [] &&
  fidBveVarFn.checkCallsOk [("full_bve_var_m7", [i64, i32], [i64])] [] &&
  m8BveVarKeyM7Fn.checkCallsOk [] [] &&
  m8ProbeDticksM6HdrFn.checkCallsOk [("m6_hdr_get_watermark", [i64, i64], [i64])] [] &&
  m8ProbeM6Fn.checkCallsOk
    [ ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
    , ("m6_hdr_set_watermark", [i64, i64, i64], [])
    , ("full_enter_dense", [i64], [.bool])
    , ("full_min_u64", [i64, i64], [i64])
    , ("full_factor", [i64, i64], [i64])
    , ("full_rebuild_watches", [i64], [i64])
    , ("full_backbone_m6", [i64, i64], [i64])
    , ("full_probe_tail_m6", [i64, i64], [i64])
    , ("full_substitute", [i64], [i64])
    , ("m6_hdr_delaying", [i64, i64], [.bool])
    , ("full_sweep_dense_m6", [i64, i64, i64], [i64])
    , ("m6_hdr_bump_delay", [i64, i64], [])
    , ("m6_hdr_reduce_delay", [i64, i64], [])
    , ("full_congruence_dense", [i64, i64], [i64])
    , ("full_vivify_m6_hdr", [i64], [i64])
    , ("full_log10_q16_m7", [i64], [i64])
    , ("full_scale_delta_m5", [i64, i64], [i64]) ] [] &&
  m8SearchM6Fn.checkCallsOk
    [ ("full_lucky_late_m7", [i64], [i64])
    , ("full_propagate", [i64], [i64])
    , ("full_analyze_m6_hdr", [i64], [i64])
    , ("full_reduce_m6", [i64, .bool], [i64])
    , ("full_switch_mode_m7", [i64], [])
    , ("full_restart_due", [i64], [i64])
    , ("full_restart", [i64], [])
    , ("m6_hdr_decide_fid", [i64], [i64])
    , ("full_simplify_m6", [i64, .bool, .bool], [i64])
    , ("full_rephase", [i64], [])
    , ("full_reorder_m6", [i64, i64], [i64]) ] [] &&
  fidSweepVarsFn.checkCallsOk
    [ ("full_m6_max_v", [i64], [i64])
    , ("full_m6_dense_prop", [i64], [.bool])
    , ("full_m6_collect_cands", [i64], [i32])
    , ("full_m6_sweep_var", [i64, i32, i64], [i64]) ] [] &&
  fidVivifyTierFn.checkCallsOk
    [ ("full_viv_collect_m6", [i64, i64], [i64])
    , ("full_viv_clear_tier_m6", [i64, i64], [])
    , ("full_backtrack", [i64, i64], [])
    , ("full_viv_clause_m6", [i64, i32], [i64])
    , ("full_propagate", [i64], [i64])
    , ("full_viv_count_m6", [i64, i64], [])
    , ("full_viv_keys_m6", [i64, i64], [])
    , ("full_viv_sort_sched_m6", [i64, i64], []) ] [] &&
  m7HasTernaryFn.checkCallsOk [] [] &&
  m7Hop1Fn.checkCallsOk [] [] &&
  m7Hop2Fn.checkCallsOk [("full_bva_hop1", [i64, i32, i32], [i64])] []

private theorem fidBaseNewCallsOk_ok : fidBaseNewCallsOk = true := by t_kernel_rfl

private theorem nodup_idx_inj {α : Type _} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} {a : α} (hi : xs[i]? = some a) (hj : xs[j]? = some a) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    have ⟨hnmem, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp at hi hj; subst hi
        exact absurd (List.mem_iff_getElem?.mpr ⟨j, hj⟩) hnmem
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj; subst hj
        exact absurd (List.mem_iff_getElem?.mpr ⟨i, hi⟩) hnmem
      | succ j =>
        simp at hi hj
        exact congrArg Nat.succ (ih hnd' hi hj)

private theorem sig_mem_bPre_of_lt {fs bPre bPost : List Fn} {f0 : Fn}
    (hnd : (fs.map Fn.name).Nodup) (hfs : fs = bPre ++ f0 :: bPost)
    {k idx : Nat} {s₀ s : SigEntry}
    (hk : fs[k]?.map Fn.sig = some s₀) (hnm : s₀.1 = f0.name)
    (hidx : fs[idx]?.map Fn.sig = some s) (hlt : idx < k) :
    s ∈ bPre.map Fn.sig := by
  obtain ⟨g₀, hg₀, hsg₀⟩ := m8cp_sig_of_map hk
  have hb_get : (fs.map Fn.name)[bPre.length]? = some f0.name := by
    rw [List.getElem?_map, hfs, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hk_get : (fs.map Fn.name)[k]? = some f0.name := by
    have hg₀_nm : g₀.name = f0.name := (congrArg Prod.fst hsg₀).trans hnm
    rw [List.getElem?_map, hg₀, Option.map_some, hg₀_nm]
  have hlen : bPre.length = k := nodup_idx_inj hnd hb_get hk_get
  have hlt' : idx < bPre.length := hlen ▸ hlt
  obtain ⟨g, hg, hsg⟩ := m8cp_sig_of_map hidx
  have hg_b : bPre[idx]? = some g := by
    have ha := List.getElem?_append_left (l₁ := bPre) (l₂ := f0 :: bPost) hlt'
    rw [← hfs, hg] at ha
    exact ha.symm
  exact hsg ▸ List.mem_map.mpr ⟨g, List.mem_of_getElem? hg_b, rfl⟩

private theorem mem_patchFns_sigs_of_mem {repls : List Fn} {befores : List (Sym × List Fn)}
    {bPre fs : List Fn} (hSub : ∀ g ∈ bPre, g ∈ fs)
    (hReplSigs : ∀ r ∈ repls, ∀ g ∈ fs, r.name = g.name → r.sig = g.sig)
    {s : SigEntry} (hs : s ∈ bPre.map Fn.sig) :
    s ∈ (PatchModule.patchFns repls befores bPre).map Fn.sig := by
  rcases List.mem_map.mp hs with ⟨g, hg, rfl⟩
  refine List.mem_map.mpr ⟨(repls.find? (·.name == g.name)).getD g, ?_, ?_⟩
  · simp only [PatchModule.patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    exact ⟨g, hg, Or.inr rfl⟩
  · cases hf : repls.find? (·.name == g.name) with
    | none => rfl
    | some r =>
      have hnm := beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == g.name) hf)
      exact hReplSigs r (List.mem_of_find?_eq_some hf) g (hSub g hg) hnm

private def swAllowsOk (k : Nat) (allow : List SigEntry) : Bool :=
  allow.all fun s => swSlotPairs.any fun q => (q.1 < k) && SigEntry.beq s q.2

private theorem swAllow_mem_bPre {bPre bPost : List Fn} {f0 : Fn}
    (hfs : m8FidV123t2Fns = bPre ++ f0 :: bPost)
    (hReplSigs : ∀ r ∈ fidBaseRepls, ∀ g ∈ m8FidV123t2Fns, r.name = g.name → r.sig = g.sig)
    {k : Nat} {s₀ : SigEntry} (hk : m8FidV123t2Fns[k]?.map Fn.sig = some s₀)
    (hnm : s₀.1 = f0.name) {allow : List SigEntry}
    (hok : swAllowsOk k allow = true := by decide) :
    ∀ s ∈ allow, s ∈ (PatchModule.patchFns fidBaseRepls fidBaseBefores bPre).map Fn.sig := by
  have hall := List.all_eq_true.mp hok
  intro s hs
  obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp (hall s hs)
  simp only [Bool.and_eq_true, decide_eq_true_eq, SigEntry.beq_iff_eq] at hqe
  rw [hqe.2]
  have hidx := swSlot_sig_of_mem hq
  have hb := sig_mem_bPre_of_lt m8FidV123t2Fns_names_nodup hfs hk hnm hidx hqe.1
  exact mem_patchFns_sigs_of_mem (fun g hg => hfs ▸ List.mem_append_left _ hg) hReplSigs hb

private theorem repl_callsOk_of {bPre bPost pre : List Fn} {f0 r : Fn}
    (hfs : m8FidV123t2Fns = bPre ++ f0 :: bPost)
    (hReplSigs : ∀ r' ∈ fidBaseRepls, ∀ g ∈ m8FidV123t2Fns, r'.name = g.name → r'.sig = g.sig)
    (hpreMem : ∀ s, s ∈ (PatchModule.patchFns fidBaseRepls fidBaseBefores bPre ++
      PatchModule.patchInsAt fidBaseBefores f0).map Fn.sig → s ∈ pre.map Fn.sig)
    {k : Nat} {s₀ : SigEntry} (hk : m8FidV123t2Fns[k]?.map Fn.sig = some s₀)
    (hnm : s₀.1 = f0.name) {allow : List SigEntry} (ins : List Fn)
    (hChk : r.checkCallsOk (allow ++ ins.map Fn.sig) [] = true)
    (hok : swAllowsOk k allow = true := by decide)
    (hIns : ∀ s ∈ ins.map Fn.sig,
      s ∈ (PatchModule.patchInsAt fidBaseBefores f0).map Fn.sig := by simp) :
    r.callsOk (pre.map Fn.sig) [] := by
  refine PatchModule.fn_callsOk_mono (fun s hs => ?_) (Fn.callsOk_of_checkCallsOk hChk)
  simp only [List.mem_append] at hs ⊢
  rcases hs with hc | hi
  · refine hpreMem s (by
      rw [List.map_append, List.mem_append]
      exact Or.inl (swAllow_mem_bPre hfs hReplSigs hk hnm hok s hc))
  · refine hpreMem s (by
      rw [List.map_append, List.mem_append]
      exact Or.inr (hIns s hi))

private theorem repl_callsOk_noIns {bPre bPost pre : List Fn} {f0 r : Fn}
    (hfs : m8FidV123t2Fns = bPre ++ f0 :: bPost)
    (hReplSigs : ∀ r' ∈ fidBaseRepls, ∀ g ∈ m8FidV123t2Fns, r'.name = g.name → r'.sig = g.sig)
    (hpreMem : ∀ s, s ∈ (PatchModule.patchFns fidBaseRepls fidBaseBefores bPre ++
      PatchModule.patchInsAt fidBaseBefores f0).map Fn.sig → s ∈ pre.map Fn.sig)
    {k : Nat} {s₀ : SigEntry} (hk : m8FidV123t2Fns[k]?.map Fn.sig = some s₀)
    (hnm : s₀.1 = f0.name) {allow : List SigEntry}
    (hChk : r.checkCallsOk allow [] = true)
    (hok : swAllowsOk k allow = true := by decide) :
    r.callsOk (pre.map Fn.sig) [] := by
  refine PatchModule.fn_callsOk_mono (fun s hs => ?_) (Fn.callsOk_of_checkCallsOk hChk)
  exact hpreMem s (by
    rw [List.map_append, List.mem_append]
    exact Or.inl (swAllow_mem_bPre hfs hReplSigs hk hnm hok s hs))

private theorem fidBase_callsOk :
    ∀ pre fn post, fidBaseModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ fidBaseModule.externs.map Extern.sig)
        fidBaseModule.exits := by
  have hBaseAc := m8FidV123t2_acyclic
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hBaseAc
  have hCallsAll := fidBaseNewCallsOk_ok
  simp only [fidBaseNewCallsOk, Bool.and_eq_true] at hCallsAll
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hMin, hBve⟩, hR0⟩, hR1⟩, hR2⟩, hR3⟩, hR4⟩, hR5⟩, hR6⟩, hR7⟩, hR8⟩,
    hR9⟩, hR10⟩, hR11⟩ := hCallsAll
  intro pre fn post hsplit
  have hext_eq : fidBaseModule.externs = [] := m8FidV123t2_ext_nil
  have hex_eq : fidBaseModule.exits = [] := fidBase_noExit
  rw [hext_eq, hex_eq, List.map_nil, List.append_nil]
  change PatchModule.patchFns fidBaseRepls fidBaseBefores m8FidV123t2Fns =
    pre ++ fn :: post at hsplit
  obtain ⟨bPre, f0, bPost, hfs, hPreSigs, hcase⟩ := PatchModule.patchFns_split_mem hsplit
  rcases hcase with ⟨iPre, iPost, hi, hpreMem⟩ | ⟨hfn, hpreMem⟩
  · have hins_cases :
        (f0.name = "full_min_shrink_m6" ∧
          PatchModule.patchInsAt fidBaseBefores f0 = m8MinHelpers) ∨
        (f0.name = "full_bve_var_m7" ∧
          PatchModule.patchInsAt fidBaseBefores f0 = fidBveHelpers) := by
      dsimp only [PatchModule.patchInsAt, fidBaseBefores] at hi ⊢
      by_cases h1 : ("full_min_shrink_m6" == f0.name)
      · have h1e := beq_iff_eq.mp h1; left; refine ⟨h1e.symm, ?_⟩; rw [← h1e]; rfl
      · have h1n : "full_min_shrink_m6" ≠ f0.name := fun h => h1 (beq_iff_eq.mpr h)
        by_cases h2 : ("full_bve_var_m7" == f0.name)
        · have h2e := beq_iff_eq.mp h2; right; refine ⟨h2e.symm, ?_⟩; rw [← h2e]; simp
        · have h2n : "full_bve_var_m7" ≠ f0.name := fun h => h2 (beq_iff_eq.mpr h)
          simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n] at hi
    rcases hins_cases with ⟨hnm, hins⟩ | ⟨hnm, hins⟩
    · rw [hins] at hi
      have hc := LeanQbe.T.Module.checkFnsCallsOk_ok []
        [("full_min_mark", [i64, i32, i8], [])] [] m8MinHelpers iPre fn iPost hMin hi
      refine PatchModule.fn_callsOk_mono (fun s hs => ?_) hc
      simp only [List.nil_append, List.mem_append, List.mem_singleton] at hs
      rcases hs with hiPre | rfl
      · exact hpreMem s (by rw [List.map_append]; exact List.mem_append_right _ hiPre)
      · have hmk := swAllow_mem_bPre hfs fidBase_replSigs sw_idx_135 hnm.symm
          (allow := [("full_min_mark", [i64, i32, i8], [])]) (by decide)
          ("full_min_mark", [i64, i32, i8], []) List.mem_cons_self
        exact hpreMem _ (by rw [List.map_append]; exact List.mem_append_left _ hmk)
    · rw [hins] at hi
      have hc := LeanQbe.T.Module.checkFnsCallsOk_ok []
        [("full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool])] []
        fidBveHelpers iPre fn iPost hBve hi
      refine PatchModule.fn_callsOk_mono (fun s hs => ?_) hc
      simp only [List.nil_append, List.mem_append, List.mem_singleton] at hs
      rcases hs with hiPre | rfl
      · exact hpreMem s (by rw [List.map_append]; exact List.mem_append_right _ hiPre)
      · have hgt := swAllow_mem_bPre hfs fidBase_replSigs sw_idx_374 hnm.symm
          (allow := [("full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool])])
          (by decide) ("full_bve_get_tern_m7", [i64, i32, i32, i32], [.bool]) List.mem_cons_self
        exact hpreMem _ (by rw [List.map_append]; exact List.mem_append_left _ hgt)
  · cases hr : fidBaseRepls.find? (·.name == f0.name) with
    | none =>
      simp only [hr, Option.getD_none] at hfn
      subst hfn
      have hcalls_base := LeanQbe.T.Module.checkFnsCallsOk_ok m8FidV123t2Module.exits
        (m8FidV123t2Module.externs.map Extern.sig) [] m8FidV123t2Fns bPre fn bPost
        hBaseAc.2 (by simpa using hfs)
      rw [m8FidV123t2_ext_nil, FullM8SweepV2.m8FidV123t2_noExit, List.map_nil,
        List.nil_append, List.append_nil] at hcalls_base
      exact PatchModule.fn_callsOk_mono (fun s hs => hPreSigs s hs fidBase_replSigs) hcalls_base
    | some r =>
      have hnm := beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f0.name) hr)
      have hr_mem := List.mem_of_find?_eq_some hr
      simp only [hr, Option.getD_some] at hfn
      subst hfn
      simp only [fidBaseRepls, List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine repl_callsOk_of hfs fidBase_replSigs hpreMem sw_idx_135 hnm m8MinHelpers hR0
          (by decide) ?_
        have hins : PatchModule.patchInsAt fidBaseBefores f0 = m8MinHelpers := by
          dsimp only [PatchModule.patchInsAt, fidBaseBefores]; rw [← hnm]; rfl
        rw [hins]; exact fun _ hs => hs
      · refine repl_callsOk_of hfs fidBase_replSigs hpreMem sw_idx_374 hnm fidBveHelpers hR1
          (by decide) ?_
        have hins : PatchModule.patchInsAt fidBaseBefores f0 = fidBveHelpers := by
          dsimp only [PatchModule.patchInsAt, fidBaseBefores]; rw [← hnm]; rfl
        rw [hins]; exact fun _ hs => hs
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_375 hnm hR2
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_415 hnm hR3
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_438 hnm hR4
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_440 hnm hR5
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_444 hnm hR6
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_334 hnm hR7
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_217 hnm hR8
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_243 hnm hR9
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_377 hnm hR10
      · exact repl_callsOk_noIns hfs fidBase_replSigs hpreMem sw_idx_378 hnm hR11

private theorem fidBase_fast_acyclic :
    fidBaseModule.namesNodup ∧
    (∀ pre fn post, fidBaseModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ m8FidV123t2Module.externs.map Extern.sig)
        m8FidV123t2Module.exits) :=
  ⟨fidBase_namesNodup, fidBase_callsOk⟩

private theorem fidBaseReplRows_sigs_match :
    ∀ r ∈ fidBaseReplRows, ∀ e ∈ m8SwFlatTable, r.name = e.name → fRowSig r = fRowSig e := by
  intro r hr e he hnm
  have he_sig : fRowSig e ∈ m8SwFlatTable.map fRowSig := List.mem_map_of_mem he
  rw [m8SwFlatTable_sigs] at he_sig
  rcases List.mem_map.mp he_sig with ⟨g, hg, hge⟩
  have hgn : r.name = g.name := hnm.trans (congrArg Prod.fst hge).symm
  simp only [fidBaseReplRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [← hge, sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_135 hg hgn]
  · rw [← hge, sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_137 hg hgn]
  · rw [← hge, sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_415 hg hgn]
  · rw [← hge, sig_eq_of_idx m8FidV123t2Fns_names_nodup sw_idx_418 hg hgn]

theorem fidBaseSpecTable_sigs :
    fidBaseSpecTable.map (fun e => (e.name, e.as, e.rs)) = fidBaseFns.map Fn.sig := by
  unfold fidBaseSpecTable
  change (PatchModule.patchRows fidBaseReplRows fidBaseBeforeRows m8SwFlatTable).map fRowSig =
    fidBaseFns.map Fn.sig
  refine patchRows_sigs_eq_patchFns_self m8SwFlatTable_sigs ?_ fidBaseReplRows_sigs_match
    fidBase_replSigs
  intro e f hnm
  dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt,
    fidBaseBeforeRows, fidBaseBefores]
  rw [hnm]
  by_cases h1 : ("full_min_shrink_m6" == f.name) <;>
    by_cases h2 : ("full_bve_var_m7" == f.name)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
  · have h1e := beq_iff_eq.mp h1; rw [← h1e]; exact m8MinHelperRows_sigs
  · have h2e := beq_iff_eq.mp h2; rw [← h2e]; exact fidBveHelperRows_sigs
  · have h1n : "full_min_shrink_m6" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
    have h2n : "full_bve_var_m7" ≠ f.name := fun h => h2 (beq_iff_eq.mpr h)
    simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n]

theorem fidBaseSpecTable_length : fidBaseSpecTable.length = 469 := by
  rw [rowSigs_eq_fnSigs_len fidBaseSpecTable_sigs]
  exact fidBaseFns_length

theorem fidBaseSpecTable_noExit : fidBaseSpecTable.all SpecEntry.noExit = true := by
  unfold fidBaseSpecTable
  refine patchRows_noExit (rRows := fidBaseReplRows) (bRows := fidBaseBeforeRows)
    (rs := m8SwFlatTable) m8SwFlatTable_noExit ?_ ?_
  · rw [List.all_eq_true]; intro r hr
    simp only [fidBaseReplRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rfl
  · intro p hp
    simp only [fidBaseBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact m8MinHelperRows_noExit
    · exact fidBveHelperRows_noExit

theorem fidBaseSpecTable_nodup : (fidBaseSpecTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup fidBaseSpecTable_sigs fidBaseFns_names_nodup

theorem fidBaseEnv_noExit :
    ∀ f as bs xs m Q X X', fidBaseEnv f as bs xs m Q X → fidBaseEnv f as bs xs m Q X' :=
  Env.ofTable_noExit (fun e he => List.all_eq_true.mp fidBaseSpecTable_noExit e he)

/-! ## 5. Flat Table Lookup, Forwarding & Elimination Helpers -/

private theorem fidBase_befDisj :
    ∀ p ∈ fidBaseBeforeRows, ∀ b ∈ p.2, b.name ∉ m8SwFlatTable.map SpecEntry.name := by
  have hn : m8SwFlatTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) m8SwFlatTable_sigs
    simpa only [List.map_map, Function.comp_def, Fn.sig] using hm
  rw [hn]
  have hs1 : m8MinHelperRows.map SpecEntry.name = m8MinHelpers.map Fn.name := by
    have hs := congrArg (List.map Prod.fst) m8MinHelperRows_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hs
    exact hs
  have hs2 : fidBveHelperRows.map SpecEntry.name = fidBveHelpers.map Fn.name := by
    have hs := congrArg (List.map Prod.fst) fidBveHelperRows_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hs
    exact hs
  intro p hp b hb
  have hb_in : b.name ∈ (fidBaseBefores.flatMap Prod.snd).map Fn.name := by
    simp only [fidBaseBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [fidBaseBefores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append]
    rcases hp with rfl | rfl
    · exact List.mem_append_left _ (hs1 ▸ List.mem_map_of_mem hb)
    · exact List.mem_append_right _ (hs2 ▸ List.mem_map_of_mem hb)
  exact fidBase_not_in_sw b.name hb_in

private theorem fidBaseEnv_of_m8SwFlat {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} (hne : f ∉ m8CpExclNames)
    (h : Env.ofTable m8SwFlatTable f as bs xs m Q X) : fidBaseEnv f as bs xs m Q X := by
  obtain ⟨e, he, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim h
  have hnr : e.name ∉ fidBaseReplRows.map SpecEntry.name := by
    rw [hnm]; simpa [fidBaseReplRows, m8CpExclNames] using hne
  exact ofTable_of_cast (mem_patchRows_of_base he hnr) fidBaseSpecTable_nodup hnm has hrs hcast

private theorem fidBaseEnv_of_m8Sw {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} (hne : f ∉ m8CpExclNames)
    (h : m8FidV123t2Env f as bs xs m Q X) : fidBaseEnv f as bs xs m Q X :=
  fidBaseEnv_of_m8SwFlat hne (m8SwFlatTable_iff.mpr h)

private theorem fidBaseEnv_of_m7 {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} (hne : f ∉ m8CpExclNames)
    (h : m7FidelityEnv f as bs xs m Q X) : fidBaseEnv f as bs xs m Q X :=
  fidBaseEnv_of_m8Sw hne (m8cp_m7Fid_to_m8Sw f as bs xs m Q X h)

private theorem fidBaseEnv_of_minHelp {e : SpecEntry} (_he : e ∈ m8MinHelperRows)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : Env.ofTable m8MinHelperRows e.name e.as e.rs xs m Q X) :
    fidBaseEnv e.name e.as e.rs xs m Q X := by
  obtain ⟨b, hb, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim h
  obtain ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_135
  exact ofTable_of_cast
    (mem_patchRows_of_before (by decide) List.mem_cons_self hb he0 (congrArg Prod.fst hs0))
    fidBaseSpecTable_nodup hnm has hrs hcast

private theorem fidBaseEnv_of_bveHelp {e : SpecEntry} (_he : e ∈ fidBveHelperRows)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : Env.ofTable fidBveHelperRows e.name e.as e.rs xs m Q X) :
    fidBaseEnv e.name e.as e.rs xs m Q X := by
  obtain ⟨b, hb, hnm, has, hrs, hcast⟩ := env_ofTable_mem_elim h
  obtain ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_374
  exact ofTable_of_cast
    (mem_patchRows_of_before (by decide) (List.mem_cons_of_mem _ List.mem_cons_self) hb he0
      (congrArg Prod.fst hs0))
    fidBaseSpecTable_nodup hnm has hrs hcast

private theorem fidBaseEnv_repl_intro (i : Nat) (hi : i < fidBaseReplRows.length)
    (hAnc : ∃ e0 ∈ m8SwFlatTable, e0.name = (fidBaseReplRows[i]'hi).name)
    {xs : Tup Val (fidBaseReplRows[i]'hi).as} {m : Mem 64}
    {Q : Post (fidBaseReplRows[i]'hi).rs} {X : XPost}
    (heff : (fidBaseReplRows[i]'hi).eff xs m Q X) :
    fidBaseEnv (fidBaseReplRows[i]'hi).name (fidBaseReplRows[i]'hi).as
      (fidBaseReplRows[i]'hi).rs xs m Q X := by
  obtain ⟨e0, he0, hn0⟩ := hAnc
  exact Env.ofTable_of_mem
    (mem_patchRows_of_repl (by decide) (List.getElem_mem hi) he0 hn0.symm)
    fidBaseSpecTable_nodup heff

private theorem fidBaseEnv_minShrinkM6 {a m Q X} (h : m8MinShrinkSpec a m Q X) :
    fidBaseEnv "full_min_shrink_m6" [i64] [] a m Q X :=
  fidBaseEnv_repl_intro 0 (by decide)
    (let ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_135
     ⟨e0, he0, congrArg Prod.fst hs0⟩)
    (m8MinShrinkSpec_monoX h)

private theorem fidBaseEnv_minShrink {a m Q X} (h : m8MinShrinkSpec a m Q X) :
    fidBaseEnv "full_min_shrink" [i64] [] a m Q X :=
  fidBaseEnv_repl_intro 1 (by decide)
    (let ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_137
     ⟨e0, he0, congrArg Prod.fst hs0⟩)
    (m8MinShrinkSpec_monoX h)

private theorem fidBaseEnv_varKey {a m Q X} (h : m8BveVarKeySpec a m Q X) :
    fidBaseEnv "full_bve_var_key_m7" [i64, i32] [i64] a m Q X := by
  rcases a with ⟨hp, v, ⟨⟩⟩
  obtain ⟨c, s, R, rfl, hl, hm, hQ⟩ := m8BveVarKeySpec_elim h
  exact fidBaseEnv_repl_intro 2 (by decide)
    (let ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_415
     ⟨e0, he0, congrArg Prod.fst hs0⟩)
    (m8BveVarKeySpec_intro rfl hl hm hQ)

private theorem fidBaseEnv_heapPush {a m Q X} (h : m8BveHeapPushSpec a m Q X) :
    fidBaseEnv "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X := by
  rcases a with ⟨hp, hl0, v, ⟨⟩⟩
  obtain ⟨c, s, R, rfl, hl, hm, hQ⟩ := m8BveHeapPushSpec_elim h
  exact fidBaseEnv_repl_intro 3 (by decide)
    (let ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_418
     ⟨e0, he0, congrArg Prod.fst hs0⟩)
    (m8BveHeapPushSpec_intro rfl hl hm hQ)

private theorem fidBaseEnv_to_m8SwFlat {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hneRepl : f ∉ m8CpExclNames)
    (hneMin : f ∉ m8MinHelperRows.map SpecEntry.name)
    (hneBve : f ∉ fidBveHelperRows.map SpecEntry.name)
    (h : fidBaseEnv f as bs xs m Q X) : Env.ofTable m8SwFlatTable f as bs xs m Q X := by
  rcases ofTable_patchRows_elim fidBaseReplRows_sigs_match fidBase_befDisj h with
    hr | hb | ⟨_, _, hbase⟩
  · rcases hr with ⟨r, hr, rfl, _⟩
    exact absurd (by
      have hm : r.name ∈ fidBaseReplRows.map SpecEntry.name := List.mem_map_of_mem hr
      simpa [fidBaseReplRows, m8CpExclNames] using hm) hneRepl
  · rcases hb with ⟨p, hp, b, hb_p, rfl, _⟩
    simp only [fidBaseBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact absurd (List.mem_map_of_mem hb_p) hneMin
    · exact absurd (List.mem_map_of_mem hb_p) hneBve
  · exact hbase

private theorem fidBaseEnv_elim_repl {r : SpecEntry} (hr : r ∈ fidBaseReplRows)
    {xs : Tup Val r.as} {m : Mem 64} {Q : Post r.rs} {X : XPost}
    (h : fidBaseEnv r.name r.as r.rs xs m Q X) : r.eff xs m Q X := by
  have hmem : r ∈ fidBaseSpecTable := by
    have hAnc : ∃ e0 ∈ m8SwFlatTable, r.name = e0.name := by
      simp only [fidBaseReplRows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · obtain ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_135
        exact ⟨e0, he0, (congrArg Prod.fst hs0).symm⟩
      · obtain ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_137
        exact ⟨e0, he0, (congrArg Prod.fst hs0).symm⟩
      · obtain ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_415
        exact ⟨e0, he0, (congrArg Prod.fst hs0).symm⟩
      · obtain ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_418
        exact ⟨e0, he0, (congrArg Prod.fst hs0).symm⟩
    obtain ⟨e0, he0, hn0⟩ := hAnc
    exact mem_patchRows_of_repl (by decide) hr he0 hn0
  obtain ⟨_, _, hc⟩ := m8cp_ofTable_sig_elim fidBaseSpecTable_nodup hmem h
  exact hc

private theorem fidBaseEnv_elim_m7Base {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : fidBaseEnv nm as bs xs m Q X)
    (hneEx : nm ∉ mfExtraRows.map SpecEntry.name := by decide)
    (hneSw : !(m8SwNamesLit.contains nm) = true := by decide)
    (hne1 : nm ∉ m8CpExclNames := by decide)
    (hne2 : nm ∉ m8MinHelperRows.map SpecEntry.name := by decide)
    (hne3 : nm ∉ fidBveHelperRows.map SpecEntry.name := by decide)
    (hne4 : nm ≠ "full_extend_push2" := by decide)
    (hne5 : nm ≠ "full_cong_enq_var" := by decide)
    (hne6 : nm ≠ "full_cong_eval_gate" := by decide)
    (hne7 : nm ≠ "full_cong_worklist" := by decide) :
    sp xs m Q (fun _ _ _ _ => False) := by
  have hsw := m8SwFlatTable_iff.mp (fidBaseEnv_to_m8SwFlat hne1 hne2 hne3 h)
  have hm7 := m8cp_sw_to_m7_of_ne hne4 (not_in_swRows nm hneSw) hne5 hne6 hne7 hsw
  cases hm7 with
  | base _ hb0 => exact m7FidBase_elim_of_mem hmem hb0
  | extra he => exact absurd (mf_ofTable_name_mem he) hneEx

theorem fidBaseEnv_solve_bytes_iff {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    fidBaseEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      m7FidSolveBytesSpec xs m Q (fun _ _ _ _ => False) := by
  constructor
  · intro h
    have hsw := m8SwFlatTable_iff.mp
      (fidBaseEnv_to_m8SwFlat (by decide) (by decide) (by decide) h)
    have hm7 := m8cp_sw_to_m7_of_ne (by decide) (not_in_swRows _ (by decide))
      (by decide) (by decide) (by decide) hsw
    exact m7FidelityEnv_solve_bytes_iff.mp hm7
  · intro hs
    exact fidBaseEnv_of_m7 (by decide) (m7FidelityEnv_solve_bytes_iff.mpr hs)

/-! ## 6. Helper & Replacement `TableImpl` / `Func.wp` Proofs & `fidBase_moduleOk` -/

private theorem fid_bveH (k : Nat) (hk : k < fidBveHelperRows.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : fidBveHelperRows[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ a m Q X, sp a m Q X → fidBaseEnv nm as bs a m Q X := fun a m Q X hs =>
  fidBaseEnv_of_bveHelp (heq ▸ List.getElem_mem hk)
    (Env.ofTable_of_mem (heq ▸ List.getElem_mem hk) fidBveHelperRows_nodup
      (by simpa only [heq, SpecEntry.eff, ite_true] using hno a m Q X hs))

private theorem fid_bveHelpers_impl :
    TableImpl fidBaseEnv fidBveHelpers fidBveHelperRows := by
  dsimp only [fidBveHelpers, fidBveHelperRows]
  exact ⟨ SpecEntry.Impl.of (full_bve_find_equiv_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_bve_find_and_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_bve_match_tern_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_bve_find_ite_side_m8_wp fidBaseEnv
      (m8cp_bveRow_base (fun _ _ _ _ _ _ _ => fidBaseEnv_of_m7) 15 (by decide) rfl
        (by decide) (by decide))
      (fid_bveH 2 (by decide) rfl m8BveMatchTernSpec_noExit)),
    SpecEntry.Impl.of (full_bve_find_ite_m8_wp fidBaseEnv
      (fid_bveH 3 (by decide) rfl m8BveFindIteSideSpec_noExit)),
    SpecEntry.Impl.of (full_k6_watch_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_k6_assign_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_k6_mtf_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_k6_backtrack_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_k6_prop_m8_wp fidBaseEnv
      (fid_bveH 6 (by decide) rfl m8K6AssignSpec_noExit)),
    SpecEntry.Impl.of (full_k6_ana_cl_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_k6_analyze_m8_wp fidBaseEnv
      (fid_bveH 10 (by decide) rfl m8K6AnaClSpec_noExit)
      (fid_bveH 8 (by decide) rfl m8K6BacktrackSpec_noExit)
      (fid_bveH 7 (by decide) rfl m8K6MtfSpec_noExit)
      (fid_bveH 5 (by decide) rfl m8K6WatchSpec_noExit)
      (fid_bveH 6 (by decide) rfl m8K6AssignSpec_noExit)),
    SpecEntry.Impl.of (full_k6_solve_m8_wp fidBaseEnv
      (fid_bveH 8 (by decide) rfl m8K6BacktrackSpec_noExit)
      (fid_bveH 6 (by decide) rfl m8K6AssignSpec_noExit)
      (fid_bveH 9 (by decide) rfl m8K6PropSpec_noExit)
      (fid_bveH 11 (by decide) rfl m8K6AnalyzeSpec_noExit)),
    SpecEntry.Impl.of (full_k6_core_m8_wp fidBaseEnv),
    SpecEntry.Impl.of (full_k6_extract_and_solve_m8_wp fidBaseEnv
      (fid_bveH 5 (by decide) rfl m8K6WatchSpec_noExit)
      (fid_bveH 12 (by decide) rfl m8K6SolveSpec_noExit)
      (fid_bveH 13 (by decide) rfl m8K6CoreSpec_noExit)),
    SpecEntry.Impl.of (full_bve_def_k6_m8_wp fidBaseEnv
      (fid_bveH 14 (by decide) rfl m8K6ExtractSolveSpec_noExit)),
    SpecEntry.Impl.of (full_bve_gates_fid_wp fidBaseEnv
      (fid_bveH 0 (by decide) rfl m8BveFindEquivSpec_noExit)
      (fid_bveH 1 (by decide) rfl m8BveFindAndSpec_noExit)
      (fid_bveH 4 (by decide) rfl m8BveFindIteSpec_noExit)
      (fid_bveH 15 (by decide) rfl m8BveGatesSpec_noExit)),
    trivial ⟩

private theorem fid_bvaHop1_mem :
    (⟨"full_bva_hop1", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop1Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 8 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))

private theorem fid_bvaHop2_mem :
    (⟨"full_bva_hop2", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop2Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
  m7FidBase_part3Pfx_mem _ (by
    unfold m7FidRowsPart3Pfx; (iterate 8 apply List.mem_append_right)
    exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))

private theorem fid_swRow (i : Nat) (nm : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hi : m8SweepEnvRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h)
    (hne : nm ∉ m8CpExclNames := by decide) :
    M6EnvSpec fidBaseEnv nm sp := fun xs m Q X hs =>
  fidBaseEnv_of_m8Sw hne
    (.sweep (Env.ofTable_of_mem (List.mem_of_getElem? hi) m8SweepEnvRows_nodup (hno xs m Q X hs)))

private theorem fid_extraRow (i : Nat) (nm : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hi : mfExtraRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h)
    (hne : nm ∉ m8CpExclNames := by decide) :
    ∀ xs m Q X, sp xs m Q X → fidBaseEnv nm as bs xs m Q X := fun xs m Q X hs =>
  fidBaseEnv_of_m7 hne (mf_extra_at i nm as bs sp hi hno xs m Q X hs)

private def fidBaseSkipNames : List Sym :=
  fidBaseRepls.map Fn.name ++
    ["full_min_shrink", "full_analyze", "full_analyze_core_m6",
     "full_bve_heap_push_m7", "full_elim_bve_m7"]

private theorem fidBase_noCallBad :
    PatchModule.checkNoCallBad fidBaseSkipNames m8CpExclNames m8FidV123t2Fns = true := by
  have hsub : m8cpSkipNames.all (fun s => fidBaseSkipNames.contains s) = true := by t_kernel_rfl
  simp only [PatchModule.checkNoCallBad, List.all_eq_true, Bool.or_eq_true]
  intro f hf
  have h0 := List.all_eq_true.mp m8cp_m8Sw_noCallBad f hf
  rcases Bool.or_eq_true _ _ |>.mp h0 with hs | hno
  · exact Or.inl (List.all_eq_true.mp hsub f.name (List.contains_iff_mem.mp hs))
  · exact Or.inr hno

/-- Closed unconditional `469/469` `ModuleOk` certifying `FullFidelityBase.fidBaseModule`
under flat `fidBaseEnv := Env.ofTable fidBaseSpecTable` (UNSAT-only, `std3`). -/
theorem fidBase_moduleOk : ModuleOk fidBaseEnv fidBaseModule := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc1p := m7FidPart1PfxCallees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hc3 := m7FidPart3Callees_of_sub m7FidBase_part3Pfx_mem
  have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
  have hBaseM7 : ∀ f as bs xs m Q X, f ∉ m8CpExclNames → m7FidelityEnv f as bs xs m Q X →
      fidBaseEnv f as bs xs m Q X := fun _ _ _ _ _ _ _ => fidBaseEnv_of_m7
  have hBR : ∀ {f as bs sp}, (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable →
      ∀ (hnmf : f ∉ mfExclNames) (hncp : f ∉ m8CpExclNames)
        (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)),
      ∀ a m Q X, sp a m Q X → fidBaseEnv f as bs a m Q X := fun hm hnmf hncp hno a m Q X hs =>
    fidBaseEnv_of_m7 hncp (M7FidelityEnv.base hnmf (m7FidBase_row_mem hm hno a m Q X hs))
  have hBefWf : ∀ p ∈ fidBaseBefores, ∀ h ∈ p.2, h.Wf := fun p hp h hh =>
    fidBaseBefores_wf h (List.mem_flatMap.mpr ⟨p, hp, hh⟩)
  refine m8cp_patch_moduleOk_of_noCallBad m8SwFlat_moduleOk
    fidBase_fast_acyclic.1 fidBase_fast_acyclic.2
    fidBaseRepls_wf hBefWf fidBase_noCallBad
    (fun _ _ _ _ _ _ _ => fidBaseEnv_of_m8SwFlat) ?_ ?_ ?_ ?_
  · intro g hg hskip hnone
    simp only [fidBaseSkipNames, fidBaseRepls, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hskip
    rcases hskip with h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · exact False.elim (m8cp_not_mem_replNames_of_find_none hnone (by simp [fidBaseRepls, h]))
    · have hgeq : g = m6oMinShrinkFn := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup
        hg (List.mem_of_getElem? m8cp_sw_fn_137) (h.trans rfl)
      subst hgeq
      intro xs m Q X hsp
      have hs0 := fidBaseEnv_elim_repl (r := fidBaseReplRows[1]'(by decide))
        (List.getElem_mem _) hsp
      exact full_min_shrink_m8_wp fidBaseEnv (fun _ _ _ _ hs => fidBaseEnv_minShrinkM6 hs)
        xs m Q X (m8MinShrinkSpec_monoX hs0)
    · have hgeq : g = m8AnalyzeFn := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup
        hg (List.mem_of_getElem? m8cp_sw_fn_149) (h.trans rfl)
      subst hgeq
      intro xs m Q X hsp
      exact m8_analyze_m8_wp fidBaseEnv
        (hBR hc2p.oneLitConfl (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.deduce1uip) (by decide) (by decide)
          (fun _ _ _ _ h => h))
        (hBR m8cp_restoreBumpAnaM5_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        (fun _ _ _ _ hs => fidBaseEnv_minShrink hs)
        (hBR hc1.tickRel (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc1.emaUpdate (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2p.learnClause (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X (fidBaseEnv_elim_m7Base m8cp_analyzeM5_mem hsp)
    · have hgeq : g = m8AnalyzeCoreM6Fn := m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup
        hg (List.mem_of_getElem? m8cp_sw_fn_150) (h.trans rfl)
      subst hgeq
      intro xs m Q X hsp
      exact m8_analyze_core_m6_m8_wp fidBaseEnv
        (hBR hc2p.oneLitConfl (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2p.anaFailedLit (by decide) (by decide)
          (fun _ _ _ _ h => m6aAnaFailedLitSpec_monoX h))
        (hBR m7FidBase_deduce1uipM6Hdr_mem (by decide) (by decide)
          (fun _ _ _ _ h => m7Deduce1uipHdrSpec_monoX h))
        (hBR hc2p.restoreBumpAna (by decide) (by decide)
          (fun _ _ _ _ h => m6aRestoreBumpAnaSpec_monoX h))
        (fun _ _ _ _ hs => fidBaseEnv_minShrinkM6 hs)
        (hBR hc1.tickRel (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc1.emaUpdate (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2p.learnClause (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X (m6HdrAnalyzeSpec_monoX (fidBaseEnv_elim_m7Base
          (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.analyzeCoreM6) hsp))
    · have hgeq : g = ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
          FullM7BveGates.full_bve_heap_push_m7_body⟩ :=
        m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup
          hg (List.mem_of_getElem? m8cp_sw_fn_418) (h.trans rfl)
      subst hgeq
      intro xs m Q X hsp
      rcases xs with ⟨hp, hl0, v, ⟨⟩⟩
      have hs0 := fidBaseEnv_elim_repl (r := fidBaseReplRows[3]'(by decide))
        (List.getElem_mem _) hsp
      obtain ⟨c, s, R, rfl, hl, hm, hQ⟩ := m8BveHeapPushSpec_elim hs0
      exact full_bve_heap_push_m7_m8_wp fidBaseEnv
        (fun _ _ _ _ hs => fidBaseEnv_varKey hs)
        (m8cp_bveRow_base hBaseM7 35 (by decide) rfl (by decide) (by decide))
        (m8cp_bveRow_base hBaseM7 36 (by decide) rfl (by decide) (by decide))
        _ m Q X (m8BveHeapPushSpec_intro rfl hl hm hQ)
    · have hgeq : g = FullM7FidelityCore.fidElimBveM7Fn :=
        m8cp_nodup_name_eq Fn.name m8FidV123t2Fns_names_nodup
          hg (List.mem_of_getElem? m8cp_sw_fn_421) (h.trans rfl)
      subst hgeq
      intro xs m Q X hsp
      exact full_elim_bve_fid_m8_wp fidBaseEnv
        (m8cp_bveRow_base hBaseM7 1 (by decide) rfl (by decide) (by decide))
        (fun _ _ _ _ hs => fidBaseEnv_heapPush hs)
        (m8cp_bveRow_base hBaseM7 38 (by decide) rfl (by decide) (by decide))
        (m8cp_bveRow_base hBaseM7 39 (by decide) rfl (by decide) (by decide))
        (m8cp_bveRow_base hBaseM7 32 (by decide) rfl (by decide) (by decide))
        xs m Q X (fidBaseEnv_elim_m7Base m7FidBase_elimBveM7_mem hsp)
  · intro g hg hskip hr xs m Q X hsp
    have hgn : g.name ∈ m8SwFlatTable.map SpecEntry.name := by
      have hm := congrArg (List.map Prod.fst) m8SwFlatTable_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hm
      rw [hm]; exact List.mem_map_of_mem hg
    have hneExcl : g.name ∉ m8CpExclNames := by
      intro hx
      simp only [m8CpExclNames, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with he | he | he | he
      · exact m8cp_not_mem_replNames_of_find_none hr
          (by simp only [fidBaseRepls, List.map_cons, List.mem_cons, he]; exact Or.inl rfl)
      · exact hskip
          (by simp only [fidBaseSkipNames, List.mem_append, List.mem_cons, he, true_or, or_true])
      · exact m8cp_not_mem_replNames_of_find_none hr
          (by simp only [fidBaseRepls, List.map_cons, List.mem_cons, he]
              exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact hskip
          (by simp only [fidBaseSkipNames, List.mem_append, List.mem_cons, he, true_or, or_true])
    have hneMin : g.name ∉ m8MinHelperRows.map SpecEntry.name := fun hm => by
      rcases List.mem_map.mp hm with ⟨b, hb, hnm⟩
      exact fidBase_befDisj ("full_min_shrink_m6", m8MinHelperRows) List.mem_cons_self b hb
        (hnm ▸ hgn)
    have hneBve : g.name ∉ fidBveHelperRows.map SpecEntry.name := fun hm => by
      rcases List.mem_map.mp hm with ⟨b, hb, hnm⟩
      exact fidBase_befDisj ("full_bve_var_m7", fidBveHelperRows)
        (List.mem_cons_of_mem _ List.mem_cons_self) b hb (hnm ▸ hgn)
    exact fidBaseEnv_to_m8SwFlat hneExcl hneMin hneBve hsp
  · intro r hr xs m Q X hsp
    simp only [fidBaseRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hs0 := fidBaseEnv_elim_repl (r := fidBaseReplRows[0]'(by decide))
        (List.getElem_mem _) hsp
      exact full_min_shrink_m6_m8_wp fidBaseEnv
        (fid_extraRow 10 "full_sort_tmp" [i64] [] FullM7AnalyzeSort.m7SortTmpSpec rfl
          (fun _ _ _ _ h => FullM7AnalyzeSort.m7SortTmpSpec_monoX h))
        (fid_extraRow 5 "full_min_mark" [i64, i32, i8] [] Full.fullMinMarkSpec rfl)
        (fun a m Q X hs => fidBaseEnv_of_minHelp List.mem_cons_self
          (Env.ofTable_of_mem (e := m8MinHelperRows[0]'(by decide)) List.mem_cons_self
            m8MinHelperRows_nodup (m8MinLitDfsSpec_monoX hs)))
        (fun a m Q X hs => fidBaseEnv_of_minHelp
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (Env.ofTable_of_mem (e := m8MinHelperRows[2]'(by decide))
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            m8MinHelperRows_nodup (m8ShrinkBlkBoolSpec_monoX hs)))
        xs m Q X (m8MinShrinkSpec_monoX hs0)
    · have hExtNeed := hBR (m7FidP3Bve5_mem (i := 4) (by decide)) (by decide) (by decide)
        (fun _ _ _ _ h => h)
      have hWeaken := hBR (m7FidP3Bve5_mem (i := 1) (by decide)) (by decide) (by decide)
        (fun _ _ _ _ h => h)
      have hResPair := hBR (m7FidP3Bve5_mem (i := 0) (by decide)) (by decide) (by decide)
        (fun _ _ _ _ h => h)
      have hCommit := hBR (m7FidP3Bve5_mem (i := 3) (by decide)) (by decide) (by decide)
        (fun _ _ _ _ h => h)
      exact full_bve_var_m7_fid_wp fidBaseEnv
        (m8cp_bveRow_base hBaseM7 9 (by decide) rfl (by decide) (by decide))
        hExtNeed hWeaken
        (hBR hc2.setInactive (by decide) (by decide) (fun _ _ _ _ h => h))
        (fid_bveH 16 (by decide) rfl m8BveGatesSpec_noExit)
        (m8cp_bveRow_base hBaseM7 31 (by decide) rfl (by decide) (by decide))
        hResPair
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag) (by decide) (by decide)
          (fun _ _ _ _ h => h))
        hCommit
        (m8cp_bveRow_base hBaseM7 1 (by decide) rfl (by decide) (by decide))
        xs m Q X (fidBaseEnv_elim_m7Base m7FidBase_bveVar_mem hsp)
    · exact full_bve_var_fid_wp fidBaseEnv
        (hBR m7FidBase_bveVar_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X (fidBaseEnv_elim_m7Base
          (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl)) hsp)
    · rcases xs with ⟨hp, v, ⟨⟩⟩
      have hs0 := fidBaseEnv_elim_repl (r := fidBaseReplRows[2]'(by decide))
        (List.getElem_mem _) hsp
      obtain ⟨c, s, R, rfl, hl, hm, hQ⟩ := m8BveVarKeySpec_elim hs0
      exact full_bve_var_key_m7_m8_wp fidBaseEnv _ m Q X
        (m8BveVarKeySpec_intro rfl hl hm hQ)
    · exact full_probe_dticks_m6_hdr_m8_wp fidBaseEnv
        (hBR hc1.hdrGetWm (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        xs m Q X (m6HdrW2aSpec_monoX (fidBaseEnv_elim_m7Base hc3p.probeDticks hsp))
    · exact full_probe_m6_m8_wp fidBaseEnv
        (hBR hc3p.probeDticks (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (hBR hc1.log10Q16M7 (by decide) (by decide)
          (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h))
        (hBR hc1.scaleDeltaM5 (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2p.vivifyM6Hdr (by decide) (by decide) (fun _ _ _ _ h => m6aVivifySpec_monoX h))
        (hBR hc2.enterDense (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc1p.delaying (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (hBR hc2p.congruenceDense (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2.rebuildWatches (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc1.hdrSetWm (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (hBR hc1p.reduceDelay (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (hBR hc1p.bumpDelay (by decide) (by decide) (fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
        (hBR m7FidBase_sweepDenseM6_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2p.substitute (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR m7FidBase_probeTailM6_mem (by decide) (by decide)
          (fun _ _ _ _ h => m6ProbeTailSpec_monoX h))
        (hBR hc2p.backboneM6 (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR m7FidP3MinU64_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR m7FidP3Factor_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X (m6ProbeSpec_monoX (fidBaseEnv_elim_m7Base m7FidBase_probeM6_mem hsp))
    · exact full_search_m6_m8_wp fidBaseEnv
        (hBR hc3.luckyLateM7 (by decide) (by decide)
          (fun _ _ _ _ h => FullM7Search.m7LuckyLateSpec_monoX h))
        (FullM7Proof.m7_fullPropagate_to_bcpS15
          (hBR hc1.propagate (by decide) (by decide) (fun _ _ _ _ h => h)))
        (hBR hc2.analyzeM6 (by decide) (by decide) (fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h))
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reduceM6) (by decide) (by decide)
          (fun _ _ _ _ h => m6ReduceSpec_monoX h))
        (hBR hc3.switchModeM7 (by decide) (by decide)
          (fun _ _ _ _ h => FullM7Search.m7SwitchModeSpec_monoX h))
        (hBR hc2.restartDue (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR hc2.restart (by decide) (by decide) (fun _ _ _ _ h => h))
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.reorderM6) (by decide) (by decide)
          (fun _ _ _ _ h => h))
        (hBR hc2.rephase (by decide) (by decide) (fun _ _ _ _ h => m7RephaseSpec_monoX h))
        (hBR (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.simplifyM6) (by decide) (by decide)
          (fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
        (fid_extraRow 59 "m6_hdr_decide_fid" [i64] [i64] m6HdrDecideSpec rfl
          (fun _ _ _ _ h => m6HdrDecideSpec_monoX h))
        xs m Q X (fullM6SearchSpec_monoX (fidBaseEnv_elim_m7Base m7FidBase_searchM6_mem hsp))
    · have hsw := m8SwFlatTable_iff.mp
        (fidBaseEnv_to_m8SwFlat (by decide) (by decide) (by decide) hsp)
      have hof := m8Sw_elim_sweep_gen (by decide) hsw
      obtain ⟨_, _, hcast⟩ := m8cp_ofTable_sig_elim m8SweepEnvRows_nodup
        (List.mem_of_getElem? (i := 35) rfl) hof
      exact fid_sweep_vars_wp fidBaseEnv
        (fid_swRow 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec)
        (fid_swRow 15 "full_m6_dense_prop" [i64] [.bool] m6DensePropSpec)
        (fid_swRow 34 "full_m6_collect_cands" [i64] [i32] m6CollectCandsSpec)
        (fid_swRow 32 "full_m6_sweep_var" [i64, i32, i64] [i64] m6SweepVarSpec)
        xs m Q X hcast
    · have hsw := m8SwFlatTable_iff.mp
        (fidBaseEnv_to_m8SwFlat (by decide) (by decide) (by decide) hsp)
      have hm7 := m8cp_sw_to_m7_of_ne (by decide) (not_in_swRows _ (by decide))
        (by decide) (by decide) (by decide) hsw
      have hviv : m6aVivifyTierSpec xs m Q X := by
        cases hm7 with
        | base hne _ => exact absurd (by decide : "full_vivify_tier_m6_hdr" ∈ mfExclNames) hne
        | extra hex =>
          exact m6aVivifyTierSpec_monoX
            (mf_extra_elim (List.mem_of_getElem? (i := 51) rfl) hex)
      exact full_vivify_tier_m6_hdr_fid_wp fidBaseEnv
        (hBR hc1.backtrack (by decide) (by decide) (fun _ _ _ _ h => h))
        (fid_extraRow 46 "full_viv_collect_m6" [i64, i64] [i64] fullVivCollectM6Spec rfl)
        (fid_extraRow 47 "full_viv_count_m6" [i64, i64] [] fullVivCountM6Spec rfl)
        (fid_extraRow 48 "full_viv_keys_m6" [i64, i64] [] fullVivKeysM6Spec rfl)
        (fid_extraRow 49 "full_viv_sort_sched_m6" [i64, i64] [] fullVivSortSchedM6Spec rfl)
        (fid_extraRow 44 "full_viv_clause_m6" [i64, i32] [i64] fullVivClauseM6Spec rfl)
        (FullM7Proof.m7_fullPropagate_to_bcpS15
          (hBR hc1.propagate (by decide) (by decide) (fun _ _ _ _ h => h)))
        (fid_extraRow 50 "full_viv_clear_tier_m6" [i64, i64] [] fullVivClearTierM6Spec rfl)
        xs m Q X hviv
    · exact m7HasTernaryFn_wp fidBaseEnv xs m Q X
        (fidBaseEnv_elim_m7Base m8cp_hasTernary_mem hsp)
    · exact m7Hop1Fn_wp fidBaseEnv xs m Q X
        (fidBaseEnv_elim_m7Base fid_bvaHop1_mem hsp)
    · exact m7Hop2Fn_wp fidBaseEnv
        (hBR fid_bvaHop1_mem (by decide) (by decide) (fun _ _ _ _ h => h))
        xs m Q X (fidBaseEnv_elim_m7Base fid_bvaHop2_mem hsp)
  · intro p hp h hh xs m Q X hs
    simp only [fidBaseBefores, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · refine m8cp_tableImpl_mem_wp
        (m8cp_minHelper_impl hBaseM7 (fun e he _ _ _ _ hm => fidBaseEnv_of_minHelp he hm))
        (fun r hr xs m Q X hsp => ?_) h hh xs m Q X hs
      obtain ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_135
      have hmem : r ∈ fidBaseSpecTable :=
        mem_patchRows_of_before (by decide) List.mem_cons_self hr he0 (congrArg Prod.fst hs0)
      exact (m8cp_ofTable_sig_elim fidBaseSpecTable_nodup hmem hsp).2.2
    · refine m8cp_tableImpl_mem_wp fid_bveHelpers_impl
        (fun r hr xs m Q X hsp => ?_) h hh xs m Q X hs
      obtain ⟨e0, he0, hs0⟩ := row_of_idx m8SwFlatTable_sigs sw_idx_374
      have hmem : r ∈ fidBaseSpecTable :=
        mem_patchRows_of_before (by decide) (List.mem_cons_of_mem _ List.mem_cons_self) hr he0
          (congrArg Prod.fst hs0)
      exact (m8cp_ofTable_sig_elim fidBaseSpecTable_nodup hmem hsp).2.2

/-- Flat `469/469` `TableImpl` directly over `fidBaseEnv := Env.ofTable fidBaseSpecTable`. -/
theorem fidBase_tableImpl :
    TableImpl fidBaseEnv fidBaseModule.fns fidBaseSpecTable :=
  tableImpl_of_moduleOk fidBase_moduleOk fidBaseSpecTable_sigs fidBaseSpecTable_nodup
    (fun _ _ _ _ _ _ h => h)

/-! ## 7. Top-Level Byte-Level UNSAT Soundness & Genuine Non-Bailout Concrete `Mem 64` NV -/

theorem fidBase_solveBytes_mem : m6oSolveBytesFn ∈ fidBaseModule.fns := by
  change m6oSolveBytesFn ∈ fidBaseFns
  exact m8cp_patchFns_mem_of_ne m8FidV123t2_solveBytes_mem fun r hr => by
    simp only [fidBaseRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

/-- Top-level unconditional byte-level UNSAT soundness of `fidBaseModule` (`469` fns, `std3`). -/
theorem fidBase_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidBaseEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8cp_solve_bytes_sound_of fidBase_moduleOk fidBase_solveBytes_mem
    (fun _ _ _ _ hs => fidBaseEnv_solve_bytes_iff.mpr hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidBaseModule`. -/
theorem fidBase_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`r = 20#64`) for `fidBaseModule`. -/
theorem fidBase_unsat_nv :
    Func.wp fidBaseEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8cp_unsat_nv_of fidBase_moduleOk fidBase_solveBytes_mem
    (fun _ _ _ _ hs => fidBaseEnv_solve_bytes_iff.mpr hs)

/-- Concrete `Mem 64` non-bailout BVE key witness (`stable = 1`) under flat `fidBaseEnv`. -/
theorem nv_fid_bve_var_key_mid :
    Func.wp fidBaseEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyMidMem
      (fun (r, ()) m' =>
        r = ((1607100#64 <<< 32) ||| 0xFFFFFFFA#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyMidState m')
      (fun _ _ _ _ => False) :=
  nvM8KeyMid_exec fidBaseEnv

/-- Concrete `Mem 64` non-bailout BVE key clamp witness (`stable = 0`) under flat `fidBaseEnv`. -/
theorem nv_fid_bve_var_key_cap :
    Func.wp fidBaseEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyCapMem
      (fun (r, ()) m' =>
        r = ((8000#64 <<< 32) ||| 0xFFFFFFF8#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyCapState m')
      (fun _ _ _ _ => False) :=
  nvM8KeyCap_exec fidBaseEnv

/-- Concrete `Mem 64` non-bailout `full_probe_dticks_m6_hdr` (`initial = true`) under
`fidBaseEnv`. -/
theorem nv_fid_probe_dticks_init :
    Func.wp fidBaseEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, true, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  nvM8ProbeDticksInit_exec fidBaseEnv

/-- Concrete `Mem 64` non-bailout `full_probe_dticks_m6_hdr` (`initial = false`) under
`fidBaseEnv`. -/
theorem nv_fid_probe_dticks_noninit :
    Func.wp fidBaseEnv FullM8CoreParity.full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => ∃ ext' s',
        10000000 ≤ r.toNat ∧ s'.core = (nvM8DtState 25000000#64).core ∧
        s'.LengthsOk nvM8Cfg ∧ M6HdrScratchPres (nvM8DtState 25000000#64) s' ∧
        M6HdrExtOk ext' ∧ nvM8F0.Unsat ∧ FullM6HdrMem nvM8Cfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  exact nvM8ProbeDticksNoninit_exec fidBaseEnv fun _ _ _ _ hs =>
    fidBaseEnv_of_m7 (by decide) (M7FidelityEnv.base (by decide)
      (m7FidBase_row_mem hc1.hdrGetWm (fun _ _ _ _ h => m6HdrW2aSpec_monoX h) _ _ _ _ hs))

/-- Concrete `Mem 64` 6-step multi-hop DFS UNSAT NV (`r = true`, `search_ticks = 1#64`) under
flat `fidBaseEnv`. -/
theorem nv_fid_min_lit_dfs_large_bin_true :
    Func.wp fidBaseEnv full_min_lit_dfs_m8_body (nvM8Cfg.hdr, 3#32, false, false, ())
      nvM8DfsMem0
      (fun (r, ()) m' =>
        r = true ∧ nvM8DfsStEnd.scratch.search_ticks = 1#64 ∧
        nvM8DfsStEnd.core.mrk = [0#8, 0#8, 2#8, 0#8] ∧ nvM8DfsStEnd.LengthsOk nvM8Cfg ∧
        FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur nvM8DfsStEnd.core ∧ nvM8F0.Unsat ∧
        FullMem nvM8Cfg nvM8DfsStEnd m')
      (fun _ _ _ _ => False) :=
  nvM8MinLitDfs_exec fidBaseEnv fun _ _ _ _ hs =>
    (fid_extraRow 5 "full_min_mark" [i64, i32, i8] [] Full.fullMinMarkSpec rfl) _ _ _ _ hs

/-- Concrete `Mem 64` 18-var non-bailout (`tmp_len = 18 > 16`) `full_min_shrink_m6` UNSAT NV
under flat `fidBaseEnv`. -/
theorem nv_fid_min_shrink_m6 :
    Func.wp fidBaseEnv FullM8CoreParity.full_min_shrink_m6_body (nvM8Min18Cfg.hdr, ())
      nvM8Min18Mem
      (fun () m' => ∃ (F_cur : List (List Nat)) (s' : FullState),
        s'.LengthsOk nvM8Min18Cfg ∧ 1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ FullOtfsWitnessInv nvM8Min18Cfg nvM8F0 F_cur s'.core ∧
        nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) := by
  obtain ⟨g, hg, hsg⟩ := m8cp_sig_of_map sw_idx_135
  have hmem : m8MinShrinkM6Fn ∈ fidBaseModule.fns := by
    change m8MinShrinkM6Fn ∈ PatchModule.patchFns fidBaseRepls fidBaseBefores m8FidV123t2Fns
    simp only [PatchModule.patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    have hgn : g.name = "full_min_shrink_m6" := congrArg Prod.fst hsg
    have hf : fidBaseRepls.find? (·.name == g.name) = some m8MinShrinkM6Fn := by
      rw [hgn]; rfl
    exact ⟨g, List.mem_of_getElem? hg, Or.inr (by rw [hf]; rfl)⟩
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  exact (fidBase_moduleOk.fnsOk pre m8MinShrinkM6Fn post hsplit).2.2 _ _ _ _
    (fidBaseEnv_minShrinkM6 nvM8Min18_spec_inst)

private def nvVivFill (k : Nat) (m : Mem 64) : Mem 64 :=
  match k with
  | 0 => m
  | k + 1 =>
    storeMem (nvVivFill k m) i32
      (nvM8Min18Cfg.pLastLearned + BitVec.ofNat 64 (4 * k)) 0xFFFFFFFF#32

private def nvVivMin18Scratch : FullScratch :=
  { nvM8Min18Scratch with last_learned := List.replicate 16 0xFFFFFFFF#32 }

/-- `18`-var sparse-ready state (`last_learned = -1#32`) for `nv_fid_vivify_tier_sort_guard`. -/
def nvVivMin18State : FullState :=
  { nvM8Min18State with scratch := nvVivMin18Scratch }

/-- Concrete `Mem 64` for `nv_fid_vivify_tier_sort_guard` (`last_learned = -1#32`). -/
def nvVivMin18Mem : Mem 64 :=
  nvVivFill 16 nvM8Min18Mem

private theorem nvVivMin18_lengths : nvVivMin18State.LengthsOk nvM8Min18Cfg :=
  ⟨nvM8Min18_lengths.1, { nvM8Min18_lengths.2 with last_learned_len := by decide }⟩

private theorem nvVivMin18Mem_ok :
    (FullMem nvM8Min18Cfg nvVivMin18State ⋆ emp) nvVivMin18Mem := by
  let c := nvM8Min18Cfg
  let Rest : Mem 64 → Prop :=
    (array64 c.pScore nvVivMin18State.scratch.score ⋆
     array64 c.pSimSig nvVivMin18State.scratch.sim_sig ⋆
     array (t := i32) c.pGlueUsed nvVivMin18State.scratch.glue_used) ⋆
    ((FullScrByteArrs c nvVivMin18State.scratch ⋆ FullScrU32A c nvVivMin18State.scratch ⋆
      FullScrWksArrs c nvVivMin18State.scratch ⋆ FullScrDynArrs c nvVivMin18State.scratch ⋆
      fullScrOuter c nvVivMin18State) ⋆ emp)
  have pIn : ∀ {A B C D E : Mem 64 → Prop} {m : Mem 64},
      (((A ⋆ B ⋆ C ⋆ D) ⋆ E) ⋆ emp) m → (D ⋆ ((A ⋆ B ⋆ C) ⋆ (E ⋆ emp))) m := fun x => sep_ac x
  have pOut : ∀ {A B C D E : Mem 64 → Prop} {m : Mem 64},
      (D ⋆ ((A ⋆ B ⋆ C) ⋆ (E ⋆ emp))) m → (((A ⋆ B ⋆ C ⋆ D) ⋆ E) ⋆ emp) m := fun x => sep_ac x
  have hBase : (array (t := i32) c.pLastLearned (List.replicate 16 0#32) ⋆ Rest) nvM8Min18Mem := by
    have hm := nvM8Min18Mem_ok
    rw [fullMem_eq_scrMeta] at hm; unfold FullScrMetaArrs at hm
    change (((((array64 c.pScore nvVivMin18State.scratch.score ⋆
        array64 c.pSimSig nvVivMin18State.scratch.sim_sig ⋆
        array (t := i32) c.pGlueUsed nvVivMin18State.scratch.glue_used ⋆
        array (t := i32) c.pLastLearned (List.replicate 16 0#32)) ⋆
      (FullScrByteArrs c nvVivMin18State.scratch ⋆ FullScrU32A c nvVivMin18State.scratch ⋆
       FullScrWksArrs c nvVivMin18State.scratch ⋆ FullScrDynArrs c nvVivMin18State.scratch ⋆
       fullScrOuter c nvVivMin18State))) ⋆ emp) nvM8Min18Mem) at hm
    exact pIn hm
  have hStep : ∀ k ≤ 16,
      (array (t := i32) c.pLastLearned
        (List.replicate k 0xFFFFFFFF#32 ++ List.replicate (16 - k) 0#32) ⋆ Rest)
        (nvVivFill k nvM8Min18Mem) := by
    intro k hk
    induction k with
    | zero => exact hBase
    | succ k ih =>
      have hst := (store_array (t := i32) 0xFFFFFFFF#32 (by decide)
        (i := k) (by simp; omega) (ih (by omega))).2
      have heq :
          (List.replicate k 0xFFFFFFFF#32 ++ List.replicate (16 - k) 0#32).set k 0xFFFFFFFF#32 =
            List.replicate (k + 1) 0xFFFFFFFF#32 ++ List.replicate (16 - (k + 1)) 0#32 := by
        apply List.ext_getElem (by simp; omega)
        intro i hi1 hi2
        simp only [List.getElem_set, List.getElem_append, List.length_replicate,
          List.getElem_replicate]
        by_cases h1 : i < k
        · simp [show k ≠ i by omega, h1, Nat.lt_succ_of_lt h1]
        · by_cases h2 : k = i
          · simp [h2]
          · simp [h1, h2, show ¬ (i < k + 1) by omega]
      rw [heq] at hst
      change (array (t := i32) c.pLastLearned
          (List.replicate (k + 1) 0xFFFFFFFF#32 ++ List.replicate (16 - (k + 1)) 0#32) ⋆ Rest)
        (storeMem (nvVivFill k nvM8Min18Mem) i32
          (c.pLastLearned + BitVec.ofNat 64 (4 * k)) 0xFFFFFFFF#32) at hst
      exact hst
  have h16 := hStep 16 (Nat.le_refl _)
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at h16
  rw [fullMem_eq_scrMeta]; unfold FullScrMetaArrs
  change (((array64 c.pScore nvVivMin18State.scratch.score ⋆
      array64 c.pSimSig nvVivMin18State.scratch.sim_sig ⋆
      array (t := i32) c.pGlueUsed nvVivMin18State.scratch.glue_used ⋆
      array (t := i32) c.pLastLearned (List.replicate 16 0xFFFFFFFF#32)) ⋆
    (FullScrByteArrs c nvVivMin18State.scratch ⋆ FullScrU32A c nvVivMin18State.scratch ⋆
     FullScrWksArrs c nvVivMin18State.scratch ⋆ FullScrDynArrs c nvVivMin18State.scratch ⋆
     fullScrOuter c nvVivMin18State)) ⋆ emp) (nvVivFill 16 nvM8Min18Mem)
  exact pOut h16

/-- Concrete `Mem 64` non-bailout (`budget = 1 > 0`, `cur_level = 18 → 0`) UNSAT NV exercising the
newly authored `full_vivify_tier_m6_hdr_fid_body` (`D-01` sort guard) under flat `fidBaseEnv`. -/
theorem nv_fid_vivify_tier_sort_guard :
    Func.wp fidBaseEnv full_vivify_tier_m6_hdr_fid_body (nvM8Min18Cfg.hdr, 0#64, 1#64, 100#64, ())
      nvVivMin18Mem
      (fun (r, ()) m' => ∃ s' : FullState,
        (r = 1#64 ∨ r = 20#64) ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        FullSparseInv nvM8Min18Cfg nvM8F0 s' ∧ nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) := by
  obtain ⟨g, hg, hsg⟩ := m8cp_sig_of_map sw_idx_217
  have hmem : fidVivifyTierFn ∈ fidBaseModule.fns := by
    change fidVivifyTierFn ∈ PatchModule.patchFns fidBaseRepls fidBaseBefores m8FidV123t2Fns
    simp only [PatchModule.patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
    have hgn : g.name = "full_vivify_tier_m6_hdr" := congrArg Prod.fst hsg
    have hf : fidBaseRepls.find? (·.name == g.name) = some fidVivifyTierFn := by rw [hgn]; rfl
    exact ⟨g, List.mem_of_getElem? hg, Or.inr (by rw [hf]; rfl)⟩
  have hsp0 : FullSparseInv nvM8Min18Cfg nvM8F0 nvVivMin18State :=
    FullSparseInvW.toSparse
      ⟨nvVivMin18_lengths, nvM8Min18_witness, nvM8Min18_marksClear,
        (fun r hr _ => by
          change r ∈ fullArenaClauseRefsCore nvVivMin18State.core at hr
          rw [show fullArenaClauseRefsCore nvVivMin18State.core = [] from rfl] at hr; cases hr),
        ⟨fun k hk => Or.inl (by
          dsimp only [nvVivMin18State, nvVivMin18Scratch]
          rw [List.getElem?_replicate, ite_eq_left (by omega)]; rfl), Nat.le_refl 0⟩, rfl⟩
  have hspec : m6aVivifyTierSpec (nvM8Min18Cfg.hdr, 0#64, 1#64, 100#64, ()) nvVivMin18Mem
      (fun (r, ()) m' => ∃ s' : FullState,
        (r = 1#64 ∨ r = 20#64) ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        FullSparseInv nvM8Min18Cfg nvM8F0 s' ∧ nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) :=
    m6aVivifyTierSpec_of hsp0 nvVivMin18Mem_ok fun r s' m' hsp' _ _ hne0 _ hdom _ hm' => by
      rw [sep_emp] at hm'; have ⟨hcl, hpr⟩ := hne0 (by decide)
      exact ⟨s', hdom, hcl, hpr, hsp', nvM8F0_unsat, hm'⟩
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  exact (fidBase_moduleOk.fnsOk pre fidVivifyTierFn post hsplit).2.2 _ _ _ _
    ((fid_extraRow 51 "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64]
      m6aVivifyTierSpec rfl (fun _ _ _ _ h => m6aVivifyTierSpec_monoX h)) _ _ _ _ hspec)

end LeanQbe.T.Examples.Kissat.FullFidelityBase

end
