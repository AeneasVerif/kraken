module

public import LeanQbe.T.Examples.Kissat.FullM6HdrProof1
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof2
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 `FullM6Hdr`: Closed `ModuleOk` & Concrete `Mem 64` UNSAT NV (`FullM6HdrProof`)

M1-clean proof module (`public section`, opaque definitions, standard imports, UNSAT-only):
Combines all `27` parametric `Func.wp` proofs (`Proof0`..`Proof2`) into:
1. Closed `32`-row `m6HdrSpecTable` (`27` defined functions + `5` canonical externs, all
   `noExit = true`, zero edits to frozen `FullHdr` / `FullArena1` / `Full1..3` / `FullM4..6`).
2. `m6HdrEnv`, `m6HdrEnv_noExit`, `m6Hdr_tableImpl`, and headline
   `m6Hdr_moduleOk : ModuleOk m6HdrEnv m6HdrModule`.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) on concrete `nvM6HdrMem`
   (the `4,060`-byte heap `[0x700 .. 0x16DC)` pairing `288`-word `M6HdrExt` prefix at `0x700` with
   `nvOneLitMem` at `0x1000`) plus concrete tiny-buffer guard `nv_full_m6_mem_init_tiny`:
   `nv_full_m6_hdr_sizeof`, `nv_full_m6_ext_sizeof`, `nv_m6_hdr_init`, `nv_m6_hdr_reset`,
   `nv_m6_hdr_recompute_tiers`, `nv_m6_hdr_dr_update`, `nv_m6_hdr_dr_allow`, `nv_m6_hdr_analyze`,
   and `nv_full_m6_mem_init_tiny`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Hdr

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Closed `32`-Row `m6HdrSpecTable`, `m6HdrEnv`, and `ModuleOk` -/

section ModuleOkSection

/-- Closed `32`-row specification table for `m6HdrModule` (`27` defined functions + `5` canonical
external callees, all `noExit = true`). -/
def m6HdrSpecTable : List SpecEntry :=
  [ ⟨"full_m6_hdr_sizeof", [], [i64], m6HdrSizeofSpec, true⟩
  , ⟨"full_m6_ext_sizeof", [], [i64], m6ExtSizeofSpec, true⟩
  , ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
  , ⟨"m6_hdr_reset", [i64], [], m6HdrResetSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
  , ⟨"m6_hdr_ext_ready", [i64], [.bool], m6HdrExtReadySpec, true⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitSpec, true⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_record_used", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reset_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"m6_hdr_add_ticks", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩
  , ⟨"m6_hdr_decide", [i64], [i64], m6HdrDecideSpec, true⟩
  , ⟨"m6_hdr_analyze_rsn", [i64, i32, i32], [.bool], m6HdrAnalyzeRsnSpec, true⟩
  , ⟨"m6_hdr_analyze", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩
  , ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  , ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩ ]

theorem m6HdrSpecTable_length : m6HdrSpecTable.length = 32 := by rfl

theorem m6HdrSpecTable_nodup : (m6HdrSpecTable.map SpecEntry.name).Nodup := by
  show ([ "full_m6_hdr_sizeof", "full_m6_ext_sizeof", "m6_hdr_init", "m6_hdr_reset"
    , "m6_ext_ensure_init", "m6_hdr_ext_ready", "full_m6_mem_init", "m6_hdr_sync_legacy_tiers"
    , "m6_hdr_recompute_tiers_mode", "m6_hdr_recompute_tiers", "m6_hdr_update_tier_limits"
    , "m6_hdr_record_used", "m6_hdr_get_tier1", "m6_hdr_get_tier2", "m6_hdr_delaying"
    , "m6_hdr_bump_delay", "m6_hdr_reduce_delay", "m6_hdr_reset_delay", "m6_hdr_get_watermark"
    , "m6_hdr_set_watermark", "m6_hdr_add_ticks", "m6_hdr_dr_init", "m6_hdr_dr_update"
    , "m6_hdr_dr_allow", "m6_hdr_decide", "m6_hdr_analyze_rsn", "m6_hdr_analyze"
    , "full_init_state", "full_next_dec_var", "full_assign", "full_analyze_rsn"
    , "full_analyze" ] : List String).Nodup
  decide

theorem m6HdrSpecTable_noExit : ∀ e ∈ m6HdrSpecTable, e.noExit = true := by
  intro e he
  simp only [m6HdrSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m6HdrSpecTable_allNoExit : m6HdrSpecTable.all (·.noExit) = true := by rfl

/-- Closed environment for `m6HdrModule`. -/
def m6HdrEnv : Env := Env.ofTable m6HdrSpecTable

theorem m6HdrEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6HdrEnv f as bs xs m Q X → m6HdrEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6HdrSpecTable_noExit

private theorem m6HdrEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m6HdrSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by
      intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m6HdrEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m6HdrSpecTable_nodup (hno xs m Q X h)

private theorem m6h_hdr_sizeof_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"full_m6_hdr_sizeof", [], [i64], full_m6_hdr_sizeof_body⟩
      ⟨"full_m6_hdr_sizeof", [], [i64], m6HdrSizeofSpec, true⟩ :=
  SpecEntry.Impl.of (full_m6_hdr_sizeof_wp m6HdrEnv)

private theorem m6h_ext_sizeof_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"full_m6_ext_sizeof", [], [i64], full_m6_ext_sizeof_body⟩
      ⟨"full_m6_ext_sizeof", [], [i64], m6ExtSizeofSpec, true⟩ :=
  SpecEntry.Impl.of (full_m6_ext_sizeof_wp m6HdrEnv)

private theorem m6h_hdr_init_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
      ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_init_wp m6HdrEnv)

private theorem m6h_hdr_reset_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_reset", [i64], [], m6_hdr_reset_body⟩
      ⟨"m6_hdr_reset", [i64], [], m6HdrResetSpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_reset_wp m6HdrEnv
    (m6HdrEnv_row_at 2 ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrInitSpec_monoX h)))

private theorem m6h_ext_ensure_init_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
      ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩ :=
  SpecEntry.Impl.of (m6_ext_ensure_init_wp m6HdrEnv
    (m6HdrEnv_row_at 2 ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrInitSpec_monoX h)))

private theorem m6h_hdr_ext_ready_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_ext_ready", [i64], [.bool], m6_hdr_ext_ready_body⟩
      ⟨"m6_hdr_ext_ready", [i64], [.bool], m6HdrExtReadySpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_ext_ready_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_mem_init_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], full_m6_mem_init_body⟩
      ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitSpec, true⟩ :=
  SpecEntry.Impl.of (full_m6_mem_init_wp m6HdrEnv
    (m6HdrEnv_row_at 27
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩)
    (m6HdrEnv_row_at 2 ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrInitSpec_monoX h)))

private theorem m6h_sync_legacy_tiers_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6_hdr_sync_legacy_tiers_body⟩
      ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_sync_legacy_tiers_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_recompute_tiers_mode_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6_hdr_recompute_tiers_mode_body⟩
      ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_recompute_tiers_mode_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h))
    (m6HdrEnv_row_at 7 ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)))

private theorem m6h_recompute_tiers_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_recompute_tiers", [i64], [], m6_hdr_recompute_tiers_body⟩
      ⟨"m6_hdr_recompute_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_recompute_tiers_wp m6HdrEnv
    (m6HdrEnv_row_at 8
      ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)))

private theorem m6h_update_tier_limits_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_update_tier_limits", [i64], [], m6_hdr_update_tier_limits_body⟩
      ⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_update_tier_limits_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h))
    (m6HdrEnv_row_at 9 ⟨"m6_hdr_recompute_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h)))

private theorem m6h_record_used_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_record_used", [i64, i64], [], m6_hdr_record_used_body⟩
      ⟨"m6_hdr_record_used", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_record_used_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_get_tier1_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], m6_hdr_get_tier1_body⟩
      ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_get_tier1_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_get_tier2_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], m6_hdr_get_tier2_body⟩
      ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_get_tier2_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_delaying_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6_hdr_delaying_body⟩
      ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_delaying_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_bump_delay_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_bump_delay", [i64, i64], [], m6_hdr_bump_delay_body⟩
      ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_bump_delay_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_reduce_delay_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6_hdr_reduce_delay_body⟩
      ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_reduce_delay_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_reset_delay_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_reset_delay", [i64, i64], [], m6_hdr_reset_delay_body⟩
      ⟨"m6_hdr_reset_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_reset_delay_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_get_watermark_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6_hdr_get_watermark_body⟩
      ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_get_watermark_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_set_watermark_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6_hdr_set_watermark_body⟩
      ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_set_watermark_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_add_ticks_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_add_ticks", [i64, i64], [], m6_hdr_add_ticks_body⟩
      ⟨"m6_hdr_add_ticks", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ :=
  SpecEntry.Impl.of (m6_hdr_add_ticks_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_dr_init_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_dr_init", [i64], [], m6_hdr_dr_init_body⟩
      ⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_dr_init_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_dr_update_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_dr_update", [i64], [], m6_hdr_dr_update_body⟩
      ⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_dr_update_wp m6HdrEnv
    (m6HdrEnv_row_at 21 ⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrDrMutSpec_monoX h)))

private theorem m6h_dr_allow_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_dr_allow", [i64], [.bool], m6_hdr_dr_allow_body⟩
      ⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_dr_allow_wp m6HdrEnv
    (m6HdrEnv_row_at 4 ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
      (hno := fun _ _ _ _ h => m6ExtEnsureInitSpec_monoX h)))

private theorem m6h_decide_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_decide", [i64], [i64], m6_hdr_decide_body⟩
      ⟨"m6_hdr_decide", [i64], [i64], m6HdrDecideSpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_decide_wp m6HdrEnv
    (m6HdrEnv_row_at 28 ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩)
    (m6HdrEnv_row_at 29 ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩)
    (m6HdrEnv_row_at 21 ⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrDrMutSpec_monoX h)))

private theorem m6h_analyze_rsn_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_analyze_rsn", [i64, i32, i32], [.bool], m6_hdr_analyze_rsn_body⟩
      ⟨"m6_hdr_analyze_rsn", [i64, i32, i32], [.bool], m6HdrAnalyzeRsnSpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_analyze_rsn_wp m6HdrEnv
    (m6HdrEnv_row_at 11 ⟨"m6_hdr_record_used", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (m6HdrEnv_row_at 30
      ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩))

private theorem m6h_analyze_impl :
    SpecEntry.Impl m6HdrEnv
      ⟨"m6_hdr_analyze", [i64], [i64], m6_hdr_analyze_body⟩
      ⟨"m6_hdr_analyze", [i64], [i64], m6HdrAnalyzeSpec, true⟩ :=
  SpecEntry.Impl.of (m6_hdr_analyze_wp m6HdrEnv
    (m6HdrEnv_row_at 10 ⟨"m6_hdr_update_tier_limits", [i64], [], m6HdrW2aSpec [] [], true⟩
      (hno := fun _ _ _ _ h => m6HdrW2aSpec_monoX h))
    (m6HdrEnv_row_at 22 ⟨"m6_hdr_dr_update", [i64], [], m6HdrDrMutSpec, true⟩
      (hno := fun _ _ _ _ h => m6HdrDrMutSpec_monoX h))
    (m6HdrEnv_row_at 31 ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩))

theorem m6Hdr_allFns_wf : AllFns Fn.Wf m6HdrModule.fns :=
  ⟨full_m6_hdr_sizeof_wf, full_m6_ext_sizeof_wf, m6_hdr_init_wf, m6_hdr_reset_wf,
    m6_ext_ensure_init_wf, m6_hdr_ext_ready_wf, full_m6_mem_init_wf, m6_hdr_sync_legacy_tiers_wf,
    m6_hdr_recompute_tiers_mode_wf, m6_hdr_recompute_tiers_wf, m6_hdr_update_tier_limits_wf,
    m6_hdr_record_used_wf, m6_hdr_get_tier1_wf, m6_hdr_get_tier2_wf, m6_hdr_delaying_wf,
    m6_hdr_bump_delay_wf, m6_hdr_reduce_delay_wf, m6_hdr_reset_delay_wf, m6_hdr_get_watermark_wf,
    m6_hdr_set_watermark_wf, m6_hdr_add_ticks_wf, m6_hdr_dr_init_wf, m6_hdr_dr_update_wf,
    m6_hdr_dr_allow_wf, m6_hdr_decide_wf, m6_hdr_analyze_rsn_wf, m6_hdr_analyze_wf, trivial⟩

theorem m6Hdr_tableImpl : TableImpl m6HdrEnv m6HdrModule.fns m6HdrSpecTable :=
  ⟨m6h_hdr_sizeof_impl, m6h_ext_sizeof_impl, m6h_hdr_init_impl, m6h_hdr_reset_impl,
    m6h_ext_ensure_init_impl, m6h_hdr_ext_ready_impl, m6h_mem_init_impl,
    m6h_sync_legacy_tiers_impl, m6h_recompute_tiers_mode_impl, m6h_recompute_tiers_impl,
    m6h_update_tier_limits_impl, m6h_record_used_impl, m6h_get_tier1_impl, m6h_get_tier2_impl,
    m6h_delaying_impl, m6h_bump_delay_impl, m6h_reduce_delay_impl, m6h_reset_delay_impl,
    m6h_get_watermark_impl, m6h_set_watermark_impl, m6h_add_ticks_impl, m6h_dr_init_impl,
    m6h_dr_update_impl, m6h_dr_allow_impl, m6h_decide_impl, m6h_analyze_rsn_impl,
    m6h_analyze_impl, trivial⟩

/-- Headline `ModuleOk` certifying all `27` functions of `m6HdrModule` under `m6HdrEnv`
(`32` spec rows, `0` exits, fully closed). -/
theorem m6Hdr_moduleOk : ModuleOk m6HdrEnv m6HdrModule :=
  Env.ofTable_moduleOk m6Hdr_acyclic m6Hdr_allFns_wf m6Hdr_tableImpl

end ModuleOkSection

/-! ## 2. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

/-- Concrete `288`-word (`2,304`-byte) zero-initialized `M6HdrExt` word list. -/
def nvM6ExtWords : List (BitVec 64) :=
  List.replicate fullM6ExtWords 0#64

/-- Concrete `4,060`-byte image (`2,304 B` `M6HdrExt` prefix at `0x700` + `1,756 B` `nvOneLitBytes`
at `0x1000`). -/
def nvM6HdrBytes : List UInt8 :=
  bytes64 nvM6ExtWords ++ nvOneLitBytes

/-- Concrete `Mem 64` heap mapped at `nvOneLitCfg.hdr - 2304` (`0x700`). -/
def nvM6HdrMem : Mem 64 :=
  nvM6HdrBytes.At (nvOneLitCfg.hdr - 2304)

theorem nvM6HdrCfg_ok : FullM6HdrCfgOk nvOneLitCfg :=
  M6HdrCfgOk_of_le (by decide)

theorem nvM6ExtWords_len : nvM6ExtWords.length = 288 := by
  unfold nvM6ExtWords fullM6ExtWords
  exact List.length_replicate

theorem nvM6ExtWords_ok : M6HdrExtOk nvM6ExtWords :=
  M6HdrExtOk.of_len nvM6ExtWords_len

theorem nvM6HdrMem_ok : FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState nvM6HdrMem := by
  have hb64 : (bytes64 nvM6ExtWords).length = 2304 := by
    rw [bytes64_length, nvM6ExtWords_len]
  have htw : (Full.hdrTailWords nvOneLitCfg nvOneLitState).length = 140 := rfl
  have hbh : nvBlockHdr.length = 1152 := by
    unfold nvBlockHdr
    rw [List.length_append, bytes64_length, bytes64_length, htw]
    rfl
  have hol : nvOneLitBytes.length = 1756 := by
    simp only [nvOneLitBytes, hbh, nvBlockBytes, nvBlockU32A, nvBlockU32B, nvBlockU32C,
      nvBlockWvec, nvBlockTail, List.length_append, bytesOf_length, bytes64_length,
      nvOneLitState, nvOneLitScratch, List.length_replicate, List.length_cons, List.length_nil,
      Ty.bytes, Ty.size, i8, i32]
  refine fullM6HdrMem_mk
    (nv_sep_append ?_ ?_ (array64_bytes _ _ (by rw [nvM6ExtWords_len]; omega))
      nvOneLitMem_ok)
  · rw [hb64]; decide
  · rw [hb64, hol]; omega

private theorem nvM6HdrF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_m6_hdr_sizeof` (`= 3456`). -/
theorem nv_full_m6_hdr_sizeof :
    Func.wp m6HdrEnv full_m6_hdr_sizeof_body () nvM6HdrMem
      (fun (r, ()) m' => r = 3456#64 ∧ FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState m')
      (fun _ _ _ _ => False) := by
  unfold Func.wp full_m6_hdr_sizeof_body
  rw [wp_ret]
  exact ⟨rfl, nvM6HdrMem_ok⟩

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_m6_ext_sizeof` (`= 2304`). -/
theorem nv_full_m6_ext_sizeof :
    Func.wp m6HdrEnv full_m6_ext_sizeof_body () nvM6HdrMem
      (fun (r, ()) m' => r = 2304#64 ∧ FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState m')
      (fun _ _ _ _ => False) := by
  unfold Func.wp full_m6_ext_sizeof_body
  rw [wp_ret]
  exact ⟨rfl, nvM6HdrMem_ok⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m6_hdr_init`. -/
theorem nv_m6_hdr_init :
    Func.wp m6HdrEnv m6_hdr_init_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext', M6HdrExtInitOk ext' ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' nvOneLitState m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  refine m6h_hdr_init_impl.2 _ _ _ _
    (m6HdrInitSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths hm fun ext' m' hinit hm' => by
      rw [sep_emp] at hm'; exact ⟨ext', hinit, nvM6HdrF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m6_hdr_reset`. -/
theorem nv_m6_hdr_reset :
    Func.wp m6HdrEnv m6_hdr_reset_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', M6HdrExtInitOk ext' ∧ s'.scratch.tier1 = 2#64 ∧
        s'.scratch.tier2 = 6#64 ∧ nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  refine m6h_hdr_reset_impl.2 _ _ _ _
    (m6HdrResetSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths hm
      fun ext' m' hinit hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', _, hinit, rfl, rfl, nvM6HdrF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m6_hdr_recompute_tiers`. -/
theorem nv_m6_hdr_recompute_tiers :
    Func.wp m6HdrEnv m6_hdr_recompute_tiers_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        M6HdrBaseDelayedPres nvOneLitState s' ∧ M6HdrExtOk ext' ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  refine m6h_recompute_tiers_impl.2 _ _ _ _
    (m6HdrW2aSpec_of rfl nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths hm
      fun () ext' s' m' hcore hlen hsc hok _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨ext', s', hcore, hlen, hsc.delayed, hok, nvM6HdrF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m6_hdr_dr_update`:
leaves `nvOneLitState` (including `h->delayed*`) completely unchanged. -/
theorem nv_m6_hdr_dr_update :
    Func.wp m6HdrEnv m6_hdr_dr_update_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext', M6HdrExtInitOk ext' ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' nvOneLitState m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  refine m6h_dr_update_impl.2 _ _ _ _
    (m6HdrDrMutSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths hm
      fun ext' m' hinit _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', hinit, nvM6HdrF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m6_hdr_dr_allow`. -/
theorem nv_m6_hdr_dr_allow :
    Func.wp m6HdrEnv m6_hdr_dr_allow_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext', (r = true ∨ r = false) ∧ M6HdrExtInitOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' nvOneLitState m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  refine m6h_dr_allow_impl.2 _ _ _ _
    (m6HdrDrAllowSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths hm
      fun r ext' m' hinit _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨ext', by cases r <;> simp, hinit, nvM6HdrF0_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for composed `m6_hdr_analyze`: on the level-0
binary conflict in `nvM6HdrMem`, returns `20#64`, certifies `nvOneLitF0.Unsat`, and preserves
`FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState`. -/
theorem nv_m6_hdr_analyze :
    Func.wp m6HdrEnv m6_hdr_analyze_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', r = 20#64 ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
    rw [sep_emp]; exact nvM6HdrMem_ok
  have hmf := (fullM6HdrMem_iff ..).mp hm
  unfold Func.wp m6_hdr_analyze_body
  dsimp only
  rw [wp_let]
  refine wp_load_of (FullArenaTactics.load_full_cur_level hmf) ?_
  refine wp_let_cmp _ _ _ _ _ _ rfl ?_
  refine wp_jnz_of (fun _ => ?_) (fun hf => absurd hf (by decide))
  rw [wp_ret]
  exact ⟨nvM6ExtWords, nvOneLitState, rfl, nvM6HdrF0_unsat, nvM6HdrMem_ok⟩

/-- Concrete tiny-buffer DIMACS bytes (`"p cnf 1 2\n1 0\n-1 0\n"`, `19 B`) and `1,000 B` workspace
(`< 3,456 B = fullM6HdrTotalBytes`) verifying `full_m6_mem_init` guards underflow cleanly. -/
def nvTinyCnfBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

def nvTinyWorkBytes : List UInt8 :=
  List.replicate 1000 0

def nvTinyInitMem : Mem 64 :=
  (nvTinyCnfBytes ++ nvTinyWorkBytes).At 0x2000#64

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_m6_mem_init` on an undersized `1,000 B`
workspace (`< 3,456 B`): returns `0#64` cleanly without pointer underflow and preserves memory. -/
theorem nv_full_m6_mem_init_tiny :
    Func.wp m6HdrEnv full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvTinyCnfBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvTinyCnfBytes.length, 1000#64, 100#64, ())
      nvTinyInitMem
      (fun (r, ()) m' => r = 0#64 ∧
        (bytes 0x2000#64 nvTinyCnfBytes ⋆
          region (0x2000#64 + BitVec.ofNat 64 nvTinyCnfBytes.length) 1000) m')
      (fun _ _ _ _ => False) := by
  have hcl : nvTinyCnfBytes.length = 19 := rfl
  have hwl : nvTinyWorkBytes.length = 1000 := List.length_replicate
  have hm0 : (bytes 0x2000#64 nvTinyCnfBytes ⋆
      region (0x2000#64 + BitVec.ofNat 64 nvTinyCnfBytes.length) 1000) nvTinyInitMem := by
    refine nv_sep_append rfl (by rw [hcl, hwl]; omega) rfl ?_
    exact ⟨nvTinyWorkBytes, hwl, rfl⟩
  have hm : (bytes 0x2000#64 nvTinyCnfBytes ⋆
      region (0x2000#64 + BitVec.ofNat 64 nvTinyCnfBytes.length) (1000#64).toNat ⋆ emp)
      nvTinyInitMem := by
    rw [sep_emp]; exact hm0
  refine m6h_mem_init_impl.2 _ _ _ _
    (fullM6MemInitSpec_of rfl (by rw [hcl]; decide) (by rw [hcl]; decide) hm
      (fun m' hm' _ => ⟨rfl, by rw [sep_emp] at hm'; exact hm'⟩)
      (fun c _ _ _ _ _ _ hcavail _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
        have hlt : (1000#64).toNat < fullM6ExtBytes := by decide
        have hge : 1152 ≤ c.avail := by
          have := c.hsize; unfold fullFixedBytes at this; omega
        omega))

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM6Hdr
