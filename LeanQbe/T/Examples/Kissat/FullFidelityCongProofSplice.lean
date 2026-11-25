/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCong
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof1a
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProofHt
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof2a
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof2b
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof3a
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof3b
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProofSplice0
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7Transport1
import all LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2c

/-!
# Kissat 4.0.4 Congruence Parity — `PatchBundle` Splice & UNSAT Soundness (`474` fns)

Connects `FullFidelityCong` (`19` replacements + `3` inserted helpers closing `GAP-CONG-01..04`
and `BUG-CONG-00`) onto `FullM8CoreParity.m8SweepV2CoreParityModule` (`471` fns):
1. Exports `fidCongReplRows`, `fidCongBeforeRows`, `fidCongRewireRows`, `fidCongPatchBundle`,
   `fidCongSpecTable` (`474` rows), `fidCongEnv := PatchModule.patchEnv fidCongPatchBundle`,
   `fidCong_acyclic`, `fidCong_moduleOk`, and `fidCong_tableImpl`.
2. Derives closed UNSAT soundness (`fidCong_solve_bytes_sound`, `fidCong_solve_bytes_host_sound`,
   `fidCong_unsat_nv`, `XPost := False`, `0` SAT model proofs) and direct entrypoint `_wp`s.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM7CongIte
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity

private abbrev fidRowSig (e : SpecEntry) : SigEntry := (e.name, e.as, e.rs)

/-! ## 1. `fidCongPatchBundle`, Fast Acyclicity, `ModuleOk`, & `TableImpl` -/

/-- `19`-row replacement contract table matching `fidCongRepls`. -/
def fidCongReplRows : List SpecEntry :=
  [ ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], fidCongEmitXorSpec, true⟩
  , ⟨"full_cong_has_clause_k", [i64, i32], [.bool], m6CongHasClauseKSpec, true⟩
  , ⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64], fidCongExtractXorKSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], fidCongTryXorIteSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], fidCongExtractSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], fidCongAndMatchSpec, true⟩
  , ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], fidCongEvalGateSpec, true⟩
  , ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], fidCongWorklistSpec, true⟩
  , ⟨"full_cong_fwd_subsume", [i64, i64], [i64], m6CongFwdSubsumeSpec, true⟩
  , ⟨"full_cong_ht_hash_ent_m7", [i64, i32, i64], [i64], fidCongHtHashEntSpec, true⟩
  , ⟨"full_cong_ht_init_m7", [i64, i64, i64, i64], [i64], fidCongHtInitSpec, true⟩
  , ⟨"full_cong_ht_grow_m7", [i64, i64], [i64], fidCongHtGrowSpec, true⟩
  , ⟨"full_cong_ht_grow_clear_m7", [i64, i64], [i64], fidCongHtGrowClearSpec, true⟩
  , ⟨"full_cong_ht_lookup_m7", [i64, i64, i32, i32], [i32], fidCongHtLookupSpec, true⟩
  , ⟨"full_cong_ht_insert_m7", [i64, i64, i32], [i32], fidCongHtInsertSpec, true⟩
  , ⟨"full_cong_copy_condbin_m7", [i64, i32, i64, i64], [i64], fidCongCopyCondbinLv0Spec, true⟩
  , ⟨"full_cong_merge_condeq_m7", [i64, i32, i64, i64, i32, i32], [i32],
      fidCongMergeCondeqSpec, true⟩
  , ⟨"full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32], fidCongExtractIteAllSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩ ]

/-- `3`-row flat helper spec table matching `fidCongBefores` (`emit_xor4` + pair sort). -/
def fidCongBeforeRows : List SpecEntry :=
  [ ⟨"full_cong_emit_xor4", [i64, i64, i32, i32, i32, i32], [i64], fidCongEmitXor4Spec, true⟩
  , ⟨"full_cong_sift_pairs_fid", [i64, i64, i64], [], fidCongSiftPairsSpec, true⟩
  , ⟨"full_cong_sort_pairs_fid", [i64, i64], [], fidCongSortPairsSpec, true⟩ ]

/-- Grouped before-host spec table aligned with `fidCongBefores`. -/
def fidCongBeforeRowGroups : List (Sym × List SpecEntry) :=
  [ ("full_cong_extract_xor_k", [fidCongBeforeRows[0]'(by decide)])
  , ("full_cong_fwd_subsume",
      [fidCongBeforeRows[1]'(by decide), fidCongBeforeRows[2]'(by decide)]) ]

/-- `1`-row rewired spec override allowing `full_cong_work_step` to consume `fidCongEvalGateSpec`.
-/
def fidCongRewireRows : List SpecEntry :=
  [⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
    FullM6CongSubst.m6CongWorkStepSpec, true⟩]

/-- Compositional `PatchModule.PatchBundle` splicing `FullFidelityCong` (`19+3`) onto
`FullM8CoreParity.m8SweepV2CoreParityModule` (`471` fns → `474` fns). -/
def fidCongPatchBundle : PatchModule.PatchBundle :=
  { baseMod := m8SweepV2CoreParityModule
    baseTable := m8SweepV2CoreParitySpecTable
    baseOk := m8SweepV2CoreParity_ofTable_moduleOk
    repls := fidCongRepls
    replRows := fidCongReplRows
    befores := fidCongBefores
    beforeRows := fidCongBeforeRows
    rewiredRows := fidCongRewireRows }

/-- Closed `474`-row specification table aligned 1-to-1 with `fidCongModule.fns`. -/
def fidCongSpecTable : List SpecEntry :=
  PatchModule.patchRows (fidCongReplRows ++ fidCongRewireRows) fidCongBeforeRowGroups
    m8SweepV2CoreParitySpecTable

/-- Canonical closed `Env` for `fidCongModule` (`474` fns, `0` externs, `0` exits). -/
def fidCongEnv : Env :=
  PatchModule.patchEnv fidCongPatchBundle

private theorem fidCong_slot20_ok :
    PatchModule.checkSlotPlan m8SweepV2CoreParityFns
      (fidCongRepls ++ [FullM6CongSubst.full_cong_work_step])
      [249, 250, 251, 252, 257, 258, 261, 263, 264, 265, 266, 267, 268, 269, 270, 274, 276, 277,
       278, 262] = true := by
  t_kernel_rfl

private theorem fidCong_slot20_sigs :
    ∀ r ∈ fidCongRepls ++ [FullM6CongSubst.full_cong_work_step],
      ∀ g ∈ m8SweepV2CoreParityFns, r.name = g.name → r.sig = g.sig :=
  PatchModule.replSigs_of_checkSlotPlan m8SweepV2CoreParityFns_names_nodup fidCong_slot20_ok

theorem fidCong_replSigs :
    ∀ r ∈ fidCongRepls, ∀ g ∈ m8SweepV2CoreParityFns, r.name = g.name → r.sig = g.sig :=
  fun r hr g hg hnm => fidCong_slot20_sigs r (List.mem_append_left _ hr) g hg hnm

private theorem fidCong_disj3_ok :
    (["full_cong_emit_xor4", "full_cong_sift_pairs_fid", "full_cong_sort_pairs_fid"].all
      fun nm => !((m8SweepV2CoreParityFns.map Fn.name).contains nm)) = true := by
  t_kernel_rfl

private def fidCongStepNames (f : Fn) : List Sym :=
  if f.name = "full_cong_extract_xor_k" then ["full_cong_emit_xor4", f.name]
  else if f.name = "full_cong_fwd_subsume" then
    ["full_cong_sift_pairs_fid", "full_cong_sort_pairs_fid", f.name]
  else [f.name]

private theorem fidCong_map_name_eq :
    fidCongFns.map Fn.name = m8SweepV2CoreParityFns.flatMap fidCongStepNames := by
  change (PatchModule.patchFns fidCongRepls fidCongBefores m8SweepV2CoreParityFns).map Fn.name = _
  rw [PatchModule.patchFns, List.map_flatMap]
  congr 1; funext f
  simp only [List.map_append, List.map_singleton, PatchModule.patchInsAt, fidCongBefores,
    fidCongStepNames]
  have hrNm : ((fidCongRepls.find? (·.name == f.name)).getD f).name = f.name := by
    cases hf : fidCongRepls.find? (·.name == f.name) with
    | none => rfl
    | some r => exact beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == f.name) hf)
  rw [hrNm]
  by_cases h1 : f.name = "full_cong_extract_xor_k"
  · simp [h1]; rfl
  · by_cases h2 : f.name = "full_cong_fwd_subsume"
    · simp [h2]
      exact ⟨rfl, rfl⟩
    · have h1r : ("full_cong_extract_xor_k" == f.name) = false := m8cp_sym_ne_beq (Ne.symm h1)
      have h2r : ("full_cong_fwd_subsume" == f.name) = false := m8cp_sym_ne_beq (Ne.symm h2)
      simp [h1, h2, h1r, h2r]

private theorem fidCongStepNames_mem {x : Sym} {f : Fn} (h : x ∈ fidCongStepNames f) :
    x = f.name ∨
    (f.name = "full_cong_extract_xor_k" ∧ x = "full_cong_emit_xor4") ∨
    (f.name = "full_cong_fwd_subsume" ∧
      (x = "full_cong_sift_pairs_fid" ∨ x = "full_cong_sort_pairs_fid")) := by
  unfold fidCongStepNames at h
  split at h
  · rename_i h1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inr (Or.inl ⟨h1, rfl⟩)
    · exact Or.inl rfl
  · split at h
    · rename_i h2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact Or.inr (Or.inr ⟨h2, Or.inl rfl⟩)
      · exact Or.inr (Or.inr ⟨h2, Or.inr rfl⟩)
      · exact Or.inl rfl
    · simp only [List.mem_singleton] at h
      exact Or.inl h

theorem fidCongFns_names_nodup : (fidCongFns.map Fn.name).Nodup := by
  rw [fidCong_map_name_eq]
  have hdisj : ∀ s ∈ ["full_cong_emit_xor4", "full_cong_sift_pairs_fid",
      "full_cong_sort_pairs_fid"], s ∉ m8SweepV2CoreParityFns.map Fn.name := fun s hs hmem => by
    have hc := List.all_eq_true.mp fidCong_disj3_ok s hs
    simp only [Bool.not_eq_true'] at hc
    exact absurd hmem (by simpa using hc)
  suffices ∀ fs : List Fn, (fs.map Fn.name).Nodup →
      (∀ s ∈ ["full_cong_emit_xor4", "full_cong_sift_pairs_fid", "full_cong_sort_pairs_fid"],
        s ∉ fs.map Fn.name) →
      (fs.flatMap fidCongStepNames).Nodup from
    this m8SweepV2CoreParityFns m8SweepV2CoreParityFns_names_nodup hdisj
  intro fs hnd hfr
  induction fs with
  | nil => exact .nil
  | cons f tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hfr' : ∀ s ∈ ["full_cong_emit_xor4", "full_cong_sift_pairs_fid",
        "full_cong_sort_pairs_fid"], s ∉ tl.map Fn.name := fun s hs hm =>
      hfr s hs (by simp [hm])
    have htl := ih hnd.2 hfr'
    have hne_bef : ∀ s ∈ ["full_cong_emit_xor4", "full_cong_sift_pairs_fid",
        "full_cong_sort_pairs_fid"], s ≠ f.name := fun s hs hm =>
      hfr s hs (by simp [hm])
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨?_, htl, fun x hx1 y hx2 hxy => ?_⟩
    · dsimp only [fidCongStepNames]
      split
      · refine List.nodup_cons.mpr ⟨?_, by simp⟩
        simp only [List.mem_singleton]
        exact fun hm => hne_bef "full_cong_emit_xor4" List.mem_cons_self hm
      · split
        · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, by simp⟩⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro (h | h)
            · exact absurd h (by decide)
            · exact absurd h (hne_bef "full_cong_sift_pairs_fid"
                (List.mem_cons_of_mem _ List.mem_cons_self))
          · simp only [List.mem_singleton]
            exact fun hm => absurd hm (hne_bef "full_cong_sort_pairs_fid"
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        · simp
    · subst hxy
      rw [List.mem_flatMap] at hx2
      rcases hx2 with ⟨g, hg_tl, hxg⟩
      have hne_fg : f.name ≠ g.name := fun h => hnd.1 (h ▸ List.mem_map_of_mem hg_tl)
      have hne_bef_tl : ∀ s ∈ ["full_cong_emit_xor4", "full_cong_sift_pairs_fid",
          "full_cong_sort_pairs_fid"], s ∉ tl.map Fn.name := hfr'
      rcases fidCongStepNames_mem hx1 with rfl | ⟨hf1, rfl⟩ | ⟨hf2, rfl | rfl⟩ <;>
        rcases fidCongStepNames_mem hxg with hg0 | ⟨hg1, hgx⟩ | ⟨hg2, hgx | hgx⟩
      · exact hne_fg hg0
      · exact hne_bef "full_cong_emit_xor4" List.mem_cons_self hgx.symm
      · exact hne_bef "full_cong_sift_pairs_fid"
          (List.mem_cons_of_mem _ List.mem_cons_self) hgx.symm
      · exact hne_bef "full_cong_sort_pairs_fid"
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hgx.symm
      · exact hne_bef_tl "full_cong_emit_xor4" List.mem_cons_self (hg0 ▸ List.mem_map_of_mem hg_tl)
      · exact hne_fg (hf1.trans hg1.symm)
      · exact absurd hgx (by decide)
      · exact absurd hgx (by decide)
      · exact hne_bef_tl "full_cong_sift_pairs_fid"
          (List.mem_cons_of_mem _ List.mem_cons_self) (hg0 ▸ List.mem_map_of_mem hg_tl)
      · exact absurd hgx (by decide)
      · exact hne_fg (hf2.trans hg2.symm)
      · exact absurd hgx (by decide)
      · exact hne_bef_tl "full_cong_sort_pairs_fid"
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (hg0 ▸ List.mem_map_of_mem hg_tl)
      · exact absurd hgx (by decide)
      · exact absurd hgx (by decide)
      · exact hne_fg (hf2.trans hg2.symm)

private theorem fidCong_namesNodup : fidCongModule.namesNodup := by
  have hex : fidCongModule.externs = [] := rfl
  change (fidCongFns.map Fn.name ++ fidCongModule.externs.map Extern.name).Nodup
  rw [hex, List.map_nil, List.append_nil]
  exact fidCongFns_names_nodup

private theorem fidCong_patchCallsOk :
    PatchModule.checkPatchCallsOk m8SweepV2CoreParityModule fidCongRepls fidCongBefores = true := by
  t_kernel_rfl

private def fidCongChangedNames : List Sym :=
  [ "full_cong_emit_xor", "full_cong_extract_xor_k", "full_cong_try_xor_ite", "full_cong_extract"
  , "full_cong_and_match", "full_cong_eval_gate", "full_cong_worklist", "full_cong_ht_hash_ent_m7"
  , "full_cong_ht_init_m7", "full_cong_ht_grow_m7", "full_cong_ht_grow_clear_m7"
  , "full_cong_ht_lookup_m7", "full_cong_ht_insert_m7", "full_cong_copy_condbin_m7"
  , "full_cong_merge_condeq_m7", "full_cong_extract_ite_all_m7" ]

private theorem sp_frontTable_nodup :
    (fidCongPatchBundle.frontTable.map SpecEntry.name).Nodup := by
  decide

private theorem sp_front_at_no (k : Nat) (hk : k < fidCongPatchBundle.frontTable.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : fidCongPatchBundle.frontTable[k] = ⟨nm, as, bs, sp, true⟩)
    {a : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hs : sp a m Q (fun _ _ _ _ => False)) :
    fidCongEnv nm as bs a m Q X :=
  sp_ofTable_append_left (Env.ofTable_of_mem (heq ▸ List.getElem_mem hk) sp_frontTable_nodup
    (by dsimp [SpecEntry.eff]; exact hs))

private theorem sp_front_at (k : Nat) (hk : k < fidCongPatchBundle.frontTable.length)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (heq : fidCongPatchBundle.frontTable[k] = ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → fidCongEnv nm as bs a m Q X := fun a m Q X hs =>
  sp_front_at_no k hk heq (hno a m Q X hs)

private theorem sp_fidBase_at {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m8SweepV2CoreParitySpecTable)
    (hnf : fidCongPatchBundle.frontTable.find? (·.name == nm) = none := by t_kernel_rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → fidCongEnv nm as bs a m Q X := fun a m Q X hs => by
  change PatchModule.patchEnv fidCongPatchBundle nm as bs a m Q X
  rw [PatchModule.patchEnv_base_eq fidCongPatchBundle hnf]
  exact sp_sw_base_at hmem rfl (hno a m Q X hs)

private theorem sp_fidCong_noCallBad_ok :
    PatchModule.checkNoCallBad
      (fidCongPatchBundle.repls.map Fn.name ++ fidCongPatchBundle.frontNames)
      fidCongChangedNames fidCongPatchBundle.baseMod.fns = true := by
  t_kernel_rfl

/-- Closed unconditional `474/474` `ModuleOk` certifying `fidCongModule` under `fidCongEnv`
(`0` extra axioms, `0` externs/exits). -/
theorem fidCong_moduleOk : ModuleOk fidCongEnv fidCongModule := by
  have hPatchEq : fidCongModule = fidCongPatchBundle.patchedMod := rfl
  rw [hPatchEq]
  have hNodup : fidCongPatchBundle.patchedMod.namesNodup := fidCong_namesNodup
  have hCalls := fidCong_patchCallsOk
  have hCovered : ∀ fn, (fn ∈ fidCongPatchBundle.repls ∨
      fn ∈ fidCongPatchBundle.befores.flatMap Prod.snd) →
      (fidCongPatchBundle.frontTable.find? (·.name == fn.name)).isSome = true := by
    intro fn hfn
    rcases hfn with h1 | h2
    · simp only [fidCongPatchBundle, fidCongRepls, List.mem_cons, List.not_mem_nil,
        or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [fidCongPatchBundle, fidCongBefores, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at h2
      rcases h2 with rfl | rfl | rfl <;> decide
  have hNoCallBad : ∀ fn ∈ fidCongPatchBundle.baseMod.fns,
      fidCongPatchBundle.repls.find? (·.name == fn.name) = none →
      fidCongPatchBundle.frontTable.find? (·.name == fn.name) = none →
      PatchModule.noCallInFn fidCongChangedNames fn = true := by
    intro fn hmem hr hf
    have hc := List.all_eq_true.mp sp_fidCong_noCallBad_ok fn hmem
    rcases (Bool.or_eq_true _ _).mp hc with hskip | hok
    · rw [List.contains_iff_mem, List.mem_append] at hskip
      rcases hskip with hrep | hfr
      · obtain ⟨r, hr', hnm⟩ := List.mem_map.mp hrep
        exfalso; have ht := List.find?_eq_none.mp hr r hr'; simp [hnm] at ht
      · obtain ⟨e, he, hnm⟩ := List.mem_map.mp hfr
        exfalso; have ht := List.find?_eq_none.mp hf e he; simp [hnm] at ht
    · exact hok
  have hFrontImpl : ∀ fn e, fn ∈ fidCongPatchBundle.patchedMod.fns →
      fidCongPatchBundle.frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl fidCongEnv fn e := by
    have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
    have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
    have hc2c := m7Part2CongCallees_of_sub m7FidBase_part2_mem
    have hSortU32_b : (⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩ : SpecEntry) ∈
        m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 53 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
    have hHasTern_b : (⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec,
        true⟩ : SpecEntry) ∈ m7FidBaseTable := m8cp_hasTernary_mem
    have hHasBin_b : (⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩ :
        SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 30 apply List.mem_append_right)
        exact List.mem_append_left _ List.mem_cons_self)
    have hCountBins_b : (⟨"full_cong_count_bins", [i64], [], m6CongCountBinsSpec, true⟩ :
        SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 5) rfl))
    have hFind_b : (⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩ : SpecEntry) ∈
        m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 49 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
    have hUnitFold_b : (⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec,
        true⟩ : SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 51 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
    have hEquivFold_b : (⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
        m3CongEquivFoldSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 51 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))
    have hXorM_b : (⟨"full_cong_xor_match", [i64, i32, i32], [i32], m6CongXorMatchSpec,
        true⟩ : SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 11) rfl))
    have hEnqVar_b : (⟨"full_cong_enq_var", [i64, i64, i32], [], m6CongEnqVarSpec,
        true⟩ : SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 12) rfl))
    have hU64Sort_b : (⟨"full_cong_u64_sort_m7", [i64, i64], [], m7U64SortSpec, true⟩ :
        SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 56 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
    have hExtCondeq_b : (⟨"full_cong_extract_condeq_m7", [i64, i64, i64, i64], [i64],
        m7ExtractCondeqSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 56 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 4) rfl))
    have hSortU32 := sp_fidBase_at (sp_untouched_m7_mem_swTbl hSortU32_b (by decide) (by decide)
      (by decide))
    have hHasTern := sp_fidBase_at (sp_untouched_m7_mem_swTbl hHasTern_b (by decide) (by decide)
      (by decide))
    have hNext := sp_fidBase_at (sp_untouched_m7_mem_swTbl hc1.arenaNext (by decide) (by decide)
      (by decide))
    have hHasBin := sp_fidBase_at (sp_untouched_m7_mem_swTbl hHasBin_b (by decide) (by decide)
      (by decide))
    have hCountBins := sp_fidBase_at (sp_untouched_m7_mem_swTbl hCountBins_b (by decide) (by decide)
      (by decide))
    have hFind := sp_fidBase_at (sp_untouched_m7_mem_swTbl hFind_b (by decide) (by decide)
      (by decide))
    have hUnitFold := sp_fidBase_at (sp_untouched_m7_mem_swTbl hUnitFold_b (by decide) (by decide)
      (by decide))
    have hEquivFold := sp_fidBase_at (sp_untouched_m7_mem_swTbl hEquivFold_b (by decide) (by decide)
      (by decide))
    have hXorM := sp_fidBase_at (sp_untouched_m7_mem_swTbl hXorM_b (by decide) (by decide)
      (by decide))
    have hEnqVar := sp_fidBase_at (sp_m8SwV12_row_mem_swTbl hEnqVar_b (by decide) (by decide) rfl)
    have hAddUnit := sp_fidBase_at (sp_untouched_m7_mem_swTbl hc2.addUnit (by decide) (by decide)
      (by decide))
    have hU64Sort := sp_fidBase_at (sp_untouched_m7_mem_swTbl hU64Sort_b (by decide) (by decide)
      (by decide)) (hno := sp_u64Sort_noExit)
    have hExtCondeq := sp_fidBase_at (sp_untouched_m7_mem_swTbl hExtCondeq_b (by decide) (by decide)
      (by decide))
    have hExtBin := sp_fidBase_at (sp_untouched_m7_mem_swTbl hc2c.extBin (by decide) (by decide)
      (by decide))
    have hFindUE := sp_fidBase_at (sp_untouched_m7_mem_swTbl hc2c.findUE (by decide) (by decide)
      (by decide))
    have hEmitXor := sp_front_at 1 (by decide) rfl
    have hHasClK := sp_front_at 2 (by decide) rfl
    have hExtXorK := sp_front_at 3 (by decide) rfl
    have hTryXI := sp_front_at 4 (by decide) rfl
    have hExtract := sp_front_at 5 (by decide) rfl
    have hAndM := sp_front_at 6 (by decide) rfl
    have hEvalG := sp_front_at 7 (by decide) rfl
    have hWork := sp_front_at 8 (by decide) rfl
    have hFwdSub := sp_front_at 9 (by decide) rfl
    have hHashEnt := sp_front_at 10 (by decide) rfl
    have hHtGrow := sp_front_at 12 (by decide) rfl
    have hCopyCb := sp_front_at 16 (by decide) rfl
    have hMergeCe := sp_front_at 17 (by decide) rfl
    have hExtIteAll := sp_front_at 18 (by decide) rfl
    have hEmitXor4 := sp_front_at 20 (by decide) rfl
    have hSiftPairs := sp_front_at 21 (by decide) rfl
    have hSortPairs := sp_front_at 22 (by decide) rfl
    intro fn e hmem hfind
    change fn ∈ PatchModule.patchFns fidCongRepls fidCongBefores m8SweepV2CoreParityFns at hmem
    simp only [PatchModule.patchFns, List.mem_flatMap, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with ⟨g, hg, hins | rfl⟩
    · unfold PatchModule.patchInsAt at hins
      split at hins
      · rename_i tgt ins hfind_b
        have hm_bef := List.mem_of_find?_eq_some hfind_b
        simp only [fidCongBefores, List.mem_cons, List.not_mem_nil, or_false] at hm_bef
        rcases hm_bef with hb | hb
        · cases hb
          simp only [List.mem_singleton] at hins; subst hins
          have hnm : fidCongEmitXor4Fn.name = "full_cong_emit_xor4" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_emit_xor4") =
              some (fidCongBeforeRows[0]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_emit_xor4_wp fidCongEnv)
        · cases hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hins
          rcases hins with rfl | rfl
          · have hnm : fidCongSiftPairsFn.name = "full_cong_sift_pairs_fid" := rfl
            have hf : fidCongPatchBundle.frontTable.find?
                (·.name == "full_cong_sift_pairs_fid") =
                some (fidCongBeforeRows[1]'(by decide)) := rfl
            rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
            exact SpecEntry.Impl.of (full_cong_sift_pairs_fid_wp fidCongEnv)
          · have hnm : fidCongSortPairsFn.name = "full_cong_sort_pairs_fid" := rfl
            have hf : fidCongPatchBundle.frontTable.find?
                (·.name == "full_cong_sort_pairs_fid") =
                some (fidCongBeforeRows[2]'(by decide)) := rfl
            rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
            exact SpecEntry.Impl.of (full_cong_sort_pairs_fid_wp fidCongEnv hSiftPairs)
      · nomatch hins
    · cases hr_case : fidCongRepls.find? (·.name == g.name) with
      | none =>
        rw [hr_case] at hfind
        dsimp only [Option.getD_none] at hfind
        have hf_ne : ∀ r ∈ fidCongReplRows ++ fidCongBeforeRows, r.name ≠ g.name := by
          intro r hr heq
          have h1 : (r.name ∈ fidCongReplRows.map SpecEntry.name) ∨
              (r.name ∈ fidCongBeforeRows.map SpecEntry.name) := by
            rcases List.mem_append.mp hr with hA | hB
            · exact Or.inl (List.mem_map_of_mem hA)
            · exact Or.inr (List.mem_map_of_mem hB)
          rcases h1 with hA | hB
          · have heq' : g.name ∈ fidCongRepls.map Fn.name := by
              have hnm : fidCongReplRows.map SpecEntry.name = fidCongRepls.map Fn.name := by
                t_kernel_rfl
              rw [← hnm, ← heq]; exact hA
            rcases List.mem_map.mp heq' with ⟨rr, hrr, hrnm⟩
            exfalso; have ht := List.find?_eq_none.mp hr_case rr hrr; simp [hrnm] at ht
          · have hdisj : (fidCongBeforeRows.map SpecEntry.name).all
                (fun s => !((m8SweepV2CoreParityFns.map Fn.name).contains s)) = true :=
              fidCong_disj3_ok
            have hc := List.all_eq_true.mp hdisj r.name hB
            simp only [Bool.not_eq_true'] at hc
            have hgm : r.name ∈ m8SweepV2CoreParityFns.map Fn.name :=
              heq ▸ List.mem_map_of_mem hg
            exact absurd hgm (by simpa using hc)
        have hwsNm : g.name = "full_cong_work_step" := by
          have hm := List.mem_of_find?_eq_some hfind
          have hb := beq_iff_eq.mp (List.find?_some
            (p := fun y : SpecEntry => y.name == g.name) hfind)
          change e ∈ fidCongRewireRows ++ fidCongReplRows ++ fidCongBeforeRows at hm
          simp only [List.append_assoc, List.mem_append] at hm
          rcases hm with hrew | hrest
          · simp only [fidCongRewireRows, List.mem_singleton] at hrew
            rw [← hb, hrew]
          · exact False.elim (hf_ne e (List.mem_append.mpr hrest) hb)
        have hge := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hg
          (List.mem_of_getElem? sp_m8Sw_fn262) hwsNm
        subst hge
        dsimp only [Option.getD_none]
        have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_work_step") =
            some (fidCongRewireRows[0]'(by decide)) := rfl
        rw [hwsNm, hf, Option.some.injEq] at hfind; subst hfind
        exact SpecEntry.Impl.of (workStep_wp_of_inactive_eval fidCongEnv hFind
          (fun hIn => hEvalG _ _ _ _ (m6CongEvalGateSpec_inactive_to_fid hIn)))
      | some r =>
        dsimp only [Option.getD_some]
        rw [hr_case] at hfind
        dsimp only [Option.getD_some] at hfind
        have hr_m := List.mem_of_find?_eq_some hr_case
        simp only [fidCongRepls, List.mem_cons, List.not_mem_nil, or_false] at hr_m
        rcases hr_m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · have hnm : fidCongEmitXorFn.name = "full_cong_emit_xor" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_emit_xor") =
              some (fidCongReplRows[0]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_emit_xor_wp fidCongEnv)
        · have hnm : fidCongHasClauseKFn.name = "full_cong_has_clause_k" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_has_clause_k") =
              some (fidCongReplRows[1]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_has_clause_k_wp fidCongEnv)
        · have hnm : fidCongExtractXorKFn.name = "full_cong_extract_xor_k" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_extract_xor_k") =
              some (fidCongReplRows[2]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_extract_xor_k_wp fidCongEnv hSortU32 hHasClK hEmitXor4)
        · have hnm : fidCongTryXorIteFn.name = "full_cong_try_xor_ite" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_try_xor_ite") =
              some (fidCongReplRows[3]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_try_xor_ite_wp fidCongEnv hHasTern hEmitXor)
        · have hnm : fidCongExtractFn.name = "full_cong_extract" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_extract") =
              some (fidCongReplRows[4]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_extract_wp fidCongEnv hNext hHasBin hCountBins
            hTryXI hExtXorK)
        · have hnm : fidCongAndMatchFn.name = "full_cong_and_match" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_and_match") =
              some (fidCongReplRows[5]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_and_match_wp fidCongEnv hFind)
        · have hnm : fidCongEvalGateFn.name = "full_cong_eval_gate" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_eval_gate") =
              some (fidCongReplRows[6]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_eval_gate_wp fidCongEnv hFind hSortU32 hUnitFold
            hEquivFold hAndM hXorM hEnqVar)
        · have hnm : fidCongWorklistFn.name = "full_cong_worklist" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_worklist") =
              some (fidCongReplRows[7]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_worklist_wp fidCongEnv hFind hEvalG)
        · have hnm : fidCongFwdSubsumeFn.name = "full_cong_fwd_subsume" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_fwd_subsume") =
              some (fidCongReplRows[8]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_fwd_subsume_wp fidCongEnv hNext hAddUnit hFind
            hSortPairs)
        · have hnm : fidCongHtHashEntFn.name = "full_cong_ht_hash_ent_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_ht_hash_ent_m7") =
              some (fidCongReplRows[9]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_ht_hash_ent_m7_wp fidCongEnv)
        · have hnm : fidCongHtInitFn.name = "full_cong_ht_init_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_ht_init_m7") =
              some (fidCongReplRows[10]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_ht_init_m7_wp fidCongEnv)
        · have hnm : fidCongHtGrowFn.name = "full_cong_ht_grow_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_ht_grow_m7") =
              some (fidCongReplRows[11]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_ht_grow_m7_wp fidCongEnv hHashEnt)
        · have hnm : fidCongHtGrowClearFn.name = "full_cong_ht_grow_clear_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find?
              (·.name == "full_cong_ht_grow_clear_m7") =
              some (fidCongReplRows[12]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_ht_grow_clear_m7_wp fidCongEnv)
        · have hnm : fidCongHtLookupFn.name = "full_cong_ht_lookup_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_ht_lookup_m7") =
              some (fidCongReplRows[13]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_ht_lookup_m7_wp fidCongEnv)
        · have hnm : fidCongHtInsertFn.name = "full_cong_ht_insert_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_ht_insert_m7") =
              some (fidCongReplRows[14]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_ht_insert_m7_wp fidCongEnv hHashEnt hHtGrow)
        · have hnm : fidCongCopyCondbinFn.name = "full_cong_copy_condbin_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_copy_condbin_m7") =
              some (fidCongReplRows[15]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_copy_condbin_m7_wp fidCongEnv hU64Sort)
        · have hnm : fidCongMergeCondeqFn.name = "full_cong_merge_condeq_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_cong_merge_condeq_m7") =
              some (fidCongReplRows[16]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_merge_condeq_m7_wp fidCongEnv)
        · have hnm : fidCongExtractIteAllFn.name = "full_cong_extract_ite_all_m7" := rfl
          have hf : fidCongPatchBundle.frontTable.find?
              (·.name == "full_cong_extract_ite_all_m7") =
              some (fidCongReplRows[17]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_cong_extract_ite_all_m7_wp fidCongEnv hCopyCb hExtCondeq
            hMergeCe)
        · have hnm : fidCongruenceDenseFn.name = "full_congruence_dense" := rfl
          have hf : fidCongPatchBundle.frontTable.find? (·.name == "full_congruence_dense") =
              some (fidCongReplRows[18]'(by decide)) := rfl
          rw [hnm, hf, Option.some.injEq] at hfind; subst hfind
          exact SpecEntry.Impl.of (full_congruence_dense_wp fidCongEnv hExtBin hFindUE hExtract
            hExtIteAll hWork hFwdSub)
  refine PatchModule.patchBundle_moduleOk fidCongPatchBundle hNodup fidCong_replSigs
    (fun fn h => h.elim (fun h1 => fidCongRepls_wf fn h1) (fun h2 => fidCongBefores_wf fn h2))
    hCalls hCovered hFrontImpl fidCongChangedNames hNoCallBad fun s hs hnb xs m P E htbl => ?_
  by_cases hf : s.1 ∈ fidCongPatchBundle.frontNames
  · have hm4 : s.1 ∈ ["full_cong_work_step", "full_cong_has_clause_k",
        "full_cong_fwd_subsume", "full_congruence_dense"] := by
      have hchk : (fidCongPatchBundle.frontNames.filter
          (fun nm => !fidCongChangedNames.contains nm)).all
          (fun nm => (["full_cong_work_step", "full_cong_has_clause_k",
            "full_cong_fwd_subsume", "full_congruence_dense"] ++
            fidCongBeforeRows.map SpecEntry.name).contains nm) = true := by
        decide
      have hsig_nm : s.1 ∈ m8SweepV2CoreParityFns.map Fn.name := by
        simp only [LeanQbe.T.Module.sigs, fidCongPatchBundle, m8SweepV2CoreParityModule,
          PatchModule.patchModule, List.mem_append, List.mem_map] at hs
        rcases hs with ⟨g, hg, hgs⟩ | ⟨ex, hex, hexs⟩
        · exact List.mem_map.mpr ⟨g, hg, congrArg Prod.fst hgs⟩
        · simp [m8FidV123t2Module, m8FidV12Module, m7FidelityModule] at hex
      have hc := List.all_eq_true.mp hchk s.1 (List.mem_filter.mpr
        ⟨hf, by simpa using hnb⟩)
      simp only [List.contains_iff_mem, List.mem_append] at hc
      rcases hc with h4 | hbef
      · exact h4
      · have h2 := List.all_eq_true.mp fidCong_disj3_ok s.1 hbef
        simp only [Bool.not_eq_true'] at h2
        exact absurd hsig_nm (by simpa using h2)
    rcases s with ⟨nm0, as0, bs0⟩; dsimp only at hs hnb htbl ⊢
    have hElimBase : ∀ {nm : Sym} {as1 bs1 : List Ty} {sp : Spec as1 bs1},
        (⟨nm, as1, bs1, sp, true⟩ : SpecEntry) ∈ m8SweepV2CoreParitySpecTable →
        nm0 = nm →
        ∃ (ha : as0 = as1) (hb : bs0 = bs1),
          sp (ha ▸ xs) m (hb ▸ P) (fun _ _ _ _ => False) := fun hmem hnm => by
      subst hnm
      obtain ⟨has, hrs, hcast⟩ := m8cp_ofTable_sig_elim m8SweepV2CoreParitySpecTable_nodup hmem htbl
      dsimp only at has hrs; cases has; cases hrs
      dsimp only [SpecEntry.cast, SpecEntry.eff] at hcast
      exact ⟨rfl, rfl, hcast⟩
    have hc2c := m7Part2CongCallees_of_sub m7FidBase_part2_mem
    have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm4
    rcases hm4 with hnm | hnm | hnm | hnm
    · have hWs_b : (⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
          FullM6CongSubst.m6CongWorkStepSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
        m7FidBase_part2_mem _ (by
          unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
          exact List.mem_of_getElem? (i := 14) rfl)
      obtain ⟨rfl, rfl, hs0⟩ := hElimBase
        (sp_untouched_m7_mem_swTbl hWs_b (by decide) (by decide) (by decide)) hnm
      subst hnm; exact sp_front_at_no 0 (by decide) rfl hs0
    · have hClK_b : (⟨"full_cong_has_clause_k", [i64, i32], [.bool], m6CongHasClauseKSpec,
          true⟩ : SpecEntry) ∈ m7FidBaseTable :=
        m7FidBase_part2_mem _ (by
          unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
          exact List.mem_of_getElem? (i := 2) rfl)
      obtain ⟨rfl, rfl, hs0⟩ := hElimBase
        (sp_untouched_m7_mem_swTbl hClK_b (by decide) (by decide) (by decide)) hnm
      subst hnm; exact sp_front_at_no 2 (by decide) rfl hs0
    · obtain ⟨rfl, rfl, hs0⟩ := hElimBase
        (sp_untouched_m7_mem_swTbl hc2c.fwdSub (by decide) (by decide) (by decide)) hnm
      subst hnm; exact sp_front_at_no 9 (by decide) rfl hs0
    · obtain ⟨rfl, rfl, hs0⟩ := hElimBase
        (sp_untouched_m7_mem_swTbl hc2p.congruenceDense (by decide) (by decide) (by decide)) hnm
      subst hnm; exact sp_front_at_no 19 (by decide) rfl hs0
  · have hnone : fidCongPatchBundle.frontTable.find? (·.name == s.1) = none := by
      rw [List.find?_eq_none]
      intro r hr hbeq
      exact hf (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem hr)
    change PatchModule.patchEnv fidCongPatchBundle s.1 s.2.1 s.2.2 xs m P E
    rw [PatchModule.patchEnv_base_eq fidCongPatchBundle hnone]
    exact htbl

private theorem sp_fidCongBefores_sigs (e : SpecEntry) (f : Fn) (hnm : e.name = f.name) :
    (PatchModule.patchRowInsAt fidCongBeforeRowGroups e).map fidRowSig =
      (PatchModule.patchInsAt fidCongBefores f).map Fn.sig := by
  dsimp only [PatchModule.patchRowInsAt, PatchModule.patchInsAt,
    fidCongBeforeRowGroups, fidCongBefores]
  rw [hnm]
  by_cases h1 : ("full_cong_extract_xor_k" == f.name) <;>
    by_cases h2 : ("full_cong_fwd_subsume" == f.name)
  · exact absurd ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm) (by decide)
  · have h1e := beq_iff_eq.mp h1; rw [← h1e]; rfl
  · have h2e := beq_iff_eq.mp h2; rw [← h2e]; rfl
  · have h1n : "full_cong_extract_xor_k" ≠ f.name := fun h => h1 (beq_iff_eq.mpr h)
    have h2n : "full_cong_fwd_subsume" ≠ f.name := fun h => h2 (beq_iff_eq.mpr h)
    simp [m8cp_sym_ne_beq h1n, m8cp_sym_ne_beq h2n]

private theorem sp_fidCongReplRows_sigs :
    ∀ r ∈ fidCongReplRows ++ fidCongRewireRows,
      ∀ e ∈ m8SweepV2CoreParitySpecTable, r.name = e.name → fidRowSig r = fidRowSig e := by
  have hRowFn : (fidCongReplRows ++ fidCongRewireRows).map fidRowSig =
      (fidCongRepls ++ [FullM6CongSubst.full_cong_work_step]).map Fn.sig := by
    t_kernel_rfl
  intro r hr e he hnm
  have hr_mem : fidRowSig r ∈ (fidCongRepls ++ [FullM6CongSubst.full_cong_work_step]).map Fn.sig :=
    hRowFn ▸ List.mem_map_of_mem hr
  rcases List.mem_map.mp hr_mem with ⟨rf, hrf, hrfeq⟩
  have he_mem : fidRowSig e ∈ m8SweepV2CoreParityFns.map Fn.sig :=
    m8SweepV2CoreParitySpecTable_sigs ▸ List.mem_map_of_mem he
  rcases List.mem_map.mp he_mem with ⟨g, hg, hgeq⟩
  have hrf_nm : rf.name = g.name := by
    have h1 := congrArg Prod.fst hrfeq
    have h2 := congrArg Prod.fst hgeq
    exact h1.trans (hnm.trans h2.symm)
  exact hrfeq.symm.trans ((fidCong_slot20_sigs rf hrf g hg hrf_nm).trans hgeq)

theorem fidCongSpecTable_sigs :
    fidCongSpecTable.map (fun e => (e.name, e.as, e.rs)) = fidCongFns.map Fn.sig := by
  change (PatchModule.patchRows (fidCongReplRows ++ fidCongRewireRows) fidCongBeforeRowGroups
    m8SweepV2CoreParitySpecTable).map fidRowSig = fidCongFns.map Fn.sig
  change _ = (PatchModule.patchFns fidCongRepls fidCongBefores m8SweepV2CoreParityFns).map Fn.sig
  refine patchRows_sigs_eq_patchFns_self m8SweepV2CoreParitySpecTable_sigs
    sp_fidCongBefores_sigs sp_fidCongReplRows_sigs fidCong_replSigs

theorem fidCongSpecTable_length : fidCongSpecTable.length = 474 := by
  rw [rowSigs_eq_fnSigs_len fidCongSpecTable_sigs, ← List.length_map Fn.name, fidCong_map_name_eq]
  have hlenBase : m8SweepV2CoreParityFns.length = 471 := by
    rw [← rowSigs_eq_fnSigs_len m8SweepV2CoreParitySpecTable_sigs]
    exact m8SweepV2CoreParitySpecTable_length
  have hmem251 : "full_cong_extract_xor_k" ∈ m8SweepV2CoreParityFns.map Fn.name := by
    have hs := congrArg (List.map Prod.fst) m8SweepV2CoreParitySpecTable_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hs
    rw [← hs]
    have hme : (⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64],
        m6CongExtractXorKSpec, true⟩ : SpecEntry) ∈ m8SweepV2CoreParitySpecTable :=
      sp_untouched_m7_mem_swTbl (m7FidBase_part2_mem _ (by
        unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
        exact List.mem_append_left _ (List.mem_of_getElem? (i := 3) rfl)))
        (by decide) (by decide) (by decide)
    exact List.mem_map_of_mem hme
  have hmem264 : "full_cong_fwd_subsume" ∈ m8SweepV2CoreParityFns.map Fn.name := by
    have hs := congrArg (List.map Prod.fst) m8SweepV2CoreParitySpecTable_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hs
    rw [← hs]
    have hc2c := m7Part2CongCallees_of_sub m7FidBase_part2_mem
    exact List.mem_map_of_mem (sp_untouched_m7_mem_swTbl hc2c.fwdSub (by decide) (by decide)
      (by decide))
  suffices ∀ fs : List Fn, (fs.map Fn.name).Nodup →
      (fs.flatMap fidCongStepNames).length = fs.length +
        (if "full_cong_extract_xor_k" ∈ fs.map Fn.name then 1 else 0) +
        (if "full_cong_fwd_subsume" ∈ fs.map Fn.name then 2 else 0) by
    rw [this m8SweepV2CoreParityFns m8SweepV2CoreParityFns_names_nodup, hlenBase,
      ite_eq_left hmem251, ite_eq_left hmem264]
  intro fs hnd
  induction fs with
  | nil => rfl
  | cons f tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have htl := ih hnd.2
    rw [List.flatMap_cons, List.length_append, htl, List.length_cons]
    dsimp only [fidCongStepNames]
    by_cases h1 : f.name = "full_cong_extract_xor_k"
    · have hk1 : "full_cong_extract_xor_k" ∉ tl.map Fn.name := h1 ▸ hnd.1
      simp [h1, hk1]; omega
    · by_cases h2 : f.name = "full_cong_fwd_subsume"
      · have hk2 : "full_cong_fwd_subsume" ∉ tl.map Fn.name := h2 ▸ hnd.1
        simp [h2, hk2]; omega
      · have hk1 : ("full_cong_extract_xor_k" ∈ (f :: tl).map Fn.name) ↔
            ("full_cong_extract_xor_k" ∈ tl.map Fn.name) := by simp [Ne.symm h1]
        have hk2 : ("full_cong_fwd_subsume" ∈ (f :: tl).map Fn.name) ↔
            ("full_cong_fwd_subsume" ∈ tl.map Fn.name) := by simp [Ne.symm h2]
        rw [ite_eq_right h1, ite_eq_right h2]
        simp only [hk1, hk2, List.length_singleton]; omega

theorem fidCongSpecTable_noExit : fidCongSpecTable.all SpecEntry.noExit = true := by
  refine patchRows_noExit m8SweepV2CoreParitySpecTable_noExit (by decide) fun p hp => ?_
  simp only [fidCongBeforeRowGroups, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> decide

theorem fidCongSpecTable_nodup : (fidCongSpecTable.map SpecEntry.name).Nodup :=
  rowSigs_eq_fnSigs_nodup fidCongSpecTable_sigs fidCongFns_names_nodup

theorem fidCongEnv_of_specTable {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable fidCongSpecTable f as bs xs m Q X) :
    fidCongEnv f as bs xs m Q X := by
  have hBefDisj : ∀ p ∈ fidCongBeforeRowGroups, ∀ b ∈ p.2,
      b.name ∉ m8SweepV2CoreParitySpecTable.map SpecEntry.name := by
    have hs := congrArg (List.map Prod.fst) m8SweepV2CoreParitySpecTable_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hs
    change m8SweepV2CoreParitySpecTable.map SpecEntry.name = m8SweepV2CoreParityFns.map Fn.name
      at hs
    rw [hs]
    intro p hp b hb hmem
    have hb_mem : b ∈ fidCongBeforeRows := by
      simp only [fidCongBeforeRowGroups, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · simp only [List.mem_singleton] at hb; subst hb; exact List.getElem_mem _
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> exact List.getElem_mem _
    have hb_nm : b.name ∈ ["full_cong_emit_xor4", "full_cong_sift_pairs_fid",
        "full_cong_sort_pairs_fid"] := by
      rcases List.mem_cons.mp hb_mem with rfl | hrest
      · decide
      · rcases List.mem_cons.mp hrest with rfl | hrest2
        · decide
        · rcases List.mem_singleton.mp hrest2 with rfl; decide
    have hc := List.all_eq_true.mp fidCong_disj3_ok b.name hb_nm
    simp only [Bool.not_eq_true'] at hc
    exact absurd hmem (by simpa using hc)
  rcases ofTable_patchRows_elim sp_fidCongReplRows_sigs hBefDisj h with hr | hb | hbase
  · rcases hr with ⟨r, hr, rfl, has, hrs, hcast⟩
    have hr_fr : r ∈ fidCongPatchBundle.frontTable := by
      rcases List.mem_append.mp hr with h1 | h2
      · exact List.mem_append_left _ (List.mem_append_right _ h1)
      · exact List.mem_append_left _ (List.mem_append_left _ h2)
    exact sp_ofTable_append_left (ofTable_of_cast hr_fr sp_frontTable_nodup rfl has hrs hcast)
  · rcases hb with ⟨p, hp, b, hb_p, rfl, has, hrs, hcast⟩
    have hb_fr : b ∈ fidCongPatchBundle.frontTable := by
      refine List.mem_append_right _ ?_
      simp only [fidCongBeforeRowGroups, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · simp only [List.mem_singleton] at hb_p; subst hb_p; exact List.getElem_mem _
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_p
        rcases hb_p with rfl | rfl <;> exact List.getElem_mem _
    exact sp_ofTable_append_left (ofTable_of_cast hb_fr sp_frontTable_nodup rfl has hrs hcast)
  · rcases hbase with ⟨hnr, hnb, hbase⟩
    have hnone : fidCongPatchBundle.frontTable.find? (·.name == f) = none := by
      rw [List.find?_eq_none]
      intro r hr hbeq
      have hfnm := (beq_iff_eq.mp hbeq).symm
      rcases List.mem_append.mp hr with hrr | hbf
      · rcases List.mem_append.mp hrr with hrw | hrp
        · exact hnr (List.mem_map.mpr ⟨r, List.mem_append_right _ hrw, hfnm.symm⟩)
        · exact hnr (List.mem_map.mpr ⟨r, List.mem_append_left _ hrp, hfnm.symm⟩)
      · have hbf' : r ∈ fidCongBeforeRowGroups.flatMap Prod.snd := by
          dsimp only [fidCongPatchBundle] at hbf
          simp only [fidCongBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hbf
          rcases hbf with rfl | rfl | rfl
          · exact List.mem_flatMap.mpr ⟨_, List.mem_cons_self, List.mem_cons_self⟩
          · exact List.mem_flatMap.mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
              List.mem_cons_self⟩
          · exact List.mem_flatMap.mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
              List.mem_cons_of_mem _ List.mem_cons_self⟩
        exact hnb (List.mem_map.mpr ⟨r, hbf', hfnm.symm⟩)
    change PatchModule.patchEnv fidCongPatchBundle f as bs xs m Q X
    rw [PatchModule.patchEnv_base_eq fidCongPatchBundle hnone]
    exact hbase

/-- Fast semantic acyclicity + `namesNodup` for `fidCongModule` (`474` fns, `0` kernel body
re-verification of untouched base fns). -/
theorem fidCong_acyclic :
    fidCongModule.namesNodup ∧
    ∀ pre fn post, fidCongModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ fidCongModule.externs.map Extern.sig)
        fidCongModule.exits :=
  ⟨fidCong_namesNodup, fun pre fn post hsplit =>
    (fidCong_moduleOk.fnsOk pre fn post hsplit).2.1⟩

theorem fidCong_tableImpl : TableImpl fidCongEnv fidCongModule.fns fidCongSpecTable :=
  tableImpl_of_moduleOk fidCong_moduleOk fidCongSpecTable_sigs fidCongSpecTable_nodup
    (fun _ _ _ _ _ _ ht => fidCongEnv_of_specTable ht)

/-! ## 2. Closed `kissat_solve_bytes` UNSAT Soundness, Host Lift, & NV Entrypoints -/

theorem fidCong_solveBytes_mem : m6oSolveBytesFn ∈ fidCongModule.fns := by
  change m6oSolveBytesFn ∈ fidCongFns
  exact m8cp_patchFns_mem_of_ne m8SweepV2CoreParity_solveBytes_mem fun r hr => by
    simp only [fidCongRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem fidCongEnv_solve_bytes {a : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m7FidSolveBytesSpec a m Q X) :
    fidCongEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X := by
  have hnf : fidCongPatchBundle.frontTable.find? (·.name == "kissat_solve_bytes") = none := rfl
  change PatchModule.patchEnv fidCongPatchBundle "kissat_solve_bytes" _ _ a m Q X
  rw [PatchModule.patchEnv_base_eq fidCongPatchBundle hnf]
  exact sp_m8SwParityEnv_to_table_of_not_bad (by decide)
    (.base (by decide) (m8cp_m7Fid_to_m8Sw _ _ _ _ _ _ _ (m7FidelityEnv_solve_bytes hs)))

/-- Top-level unconditional byte-level UNSAT soundness of `fidCongModule` (`474` fns,
`XPost := False`, `0` SAT model proofs). -/
theorem fidCong_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidCongEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m8cp_solve_bytes_sound_of fidCong_moduleOk fidCong_solveBytes_mem
    (fun _ _ _ _ hs => fidCongEnv_solve_bytes hs) hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift for `fidCongModule`. -/
theorem fidCong_solve_bytes_host_sound
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

/-- Concrete deterministic Tier-3b UNSAT non-vacuity (`r = 20#64`) for `fidCongModule`. -/
theorem fidCong_unsat_nv :
    Func.wp fidCongEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m8cp_unsat_nv_of fidCong_moduleOk fidCong_solveBytes_mem
    (fun _ _ _ _ hs => fidCongEnv_solve_bytes hs)

theorem fidCongEnv_emitXor4_wp :
    ∀ args m Q X, fidCongEmitXor4Spec args m Q X →
      Func.wp fidCongEnv full_cong_emit_xor4_body args m Q X :=
  full_cong_emit_xor4_wp fidCongEnv

theorem fidCongEnv_andMatch_wp :
    ∀ a m Q X, fidCongAndMatchSpec a m Q X →
      Func.wp fidCongEnv full_cong_and_match_body a m Q X := by
  have hFind_b : (⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 49 apply List.mem_append_right)
      exact List.mem_append_left _ List.mem_cons_self)
  exact full_cong_and_match_wp fidCongEnv
    (sp_fidBase_at (sp_untouched_m7_mem_swTbl hFind_b (by decide) (by decide) (by decide)))

theorem fidCongEnv_htGrowClear_wp :
    ∀ a m Q X, fidCongHtGrowClearSpec a m Q X →
      Func.wp fidCongEnv full_cong_ht_grow_clear_m7_body a m Q X :=
  full_cong_ht_grow_clear_m7_wp fidCongEnv

theorem fidCongEnv_sortPairs_wp :
    ∀ a m Q X, fidCongSortPairsSpec a m Q X →
      Func.wp fidCongEnv full_cong_sort_pairs_fid_body a m Q X :=
  full_cong_sort_pairs_fid_wp fidCongEnv (sp_front_at 21 (by decide) rfl)

theorem fidCongEnv_find {a m Q X} (h : Full.fullCongFindSpec a m Q X) :
    fidCongEnv "full_cong_find" [i64, i32] [i32] a m Q X :=
  have hFind_b : (⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 49 apply List.mem_append_right)
      exact List.mem_append_left _ List.mem_cons_self)
  sp_fidBase_at (sp_untouched_m7_mem_swTbl hFind_b (by decide) (by decide) (by decide))
    (by t_kernel_rfl) (fun _ _ _ _ h => h) a m Q X h

theorem fidCongEnv_evalGate_wp :
    ∀ a m Q X, fidCongEvalGateSpec a m Q X →
      Func.wp fidCongEnv full_cong_eval_gate_body a m Q X := by
  have hSort_b : (⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 53 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  have hUnit_b : (⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 51 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
  have hEquiv_b : (⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec,
      true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 51 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))
  have hXor_b : (⟨"full_cong_xor_match", [i64, i32, i32], [i32], m6CongXorMatchSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 11) rfl))
  have hEnq_b : (⟨"full_cong_enq_var", [i64, i64, i32], [], m6CongEnqVarSpec, true⟩ :
      SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 12) rfl))
  exact full_cong_eval_gate_wp fidCongEnv
    (fun _ _ _ _ h => fidCongEnv_find h)
    (sp_fidBase_at (sp_untouched_m7_mem_swTbl hSort_b (by decide) (by decide) (by decide)))
    (sp_fidBase_at (sp_untouched_m7_mem_swTbl hUnit_b (by decide) (by decide) (by decide)))
    (sp_fidBase_at (sp_untouched_m7_mem_swTbl hEquiv_b (by decide) (by decide) (by decide)))
    (sp_front_at 6 (by decide) rfl)
    (sp_fidBase_at (sp_untouched_m7_mem_swTbl hXor_b (by decide) (by decide) (by decide)))
    (sp_fidBase_at (sp_m8SwV12_row_mem_swTbl hEnq_b (by decide) (by decide) rfl))

theorem fidCongEnv_congruenceDense_wp :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp fidCongEnv full_congruence_dense_body a m Q X := by
  have hc2c := m7Part2CongCallees_of_sub m7FidBase_part2_mem
  exact full_congruence_dense_wp fidCongEnv
    (sp_fidBase_at (sp_untouched_m7_mem_swTbl hc2c.extBin (by decide) (by decide) (by decide)))
    (sp_fidBase_at (sp_untouched_m7_mem_swTbl hc2c.findUE (by decide) (by decide) (by decide)))
    (sp_front_at 5 (by decide) rfl)
    (sp_front_at 18 (by decide) rfl)
    (sp_front_at 8 (by decide) rfl)
    (sp_front_at 9 (by decide) rfl)

end LeanQbe.T.Examples.Kissat.FullFidelityCong

end
