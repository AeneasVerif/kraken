module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiProof1
public import LeanQbe.T.LeanLCNF.LcnfC0FfiProof2
public import LeanQbe.T.LeanLCNF.LcnfC0FullProof
import LeanQbe.T.Logic.ProofKit

/-!
# Top-Level `ModuleOk`, Closed Composition (`rtC0WithFfiMod`) & Concrete `Mem 64` Non-Vacuity

Top-level FFI adapter deliverable (`Shard F2`):
1. `ffiMod_allFns_wf`, `ffiMod_tableImpl`, `ffiMod_moduleOk`, `ffiMod_fn_sound`,
   `ffiEnv_noExit_fns`.
2. Transparent `RtMpzNatCanon ↔ mpzNatCanon` bridge (`rtMpzNatCanon_iff_bnMpzNatCanon`).
3. Closed composed module `rtC0WithFfiMod` (`rtC0CoreMod.fns ++ ffiMod.fns`, `0` externs,
   `exits := rtC0CoreMod.exits`) with `rtC0WithFfiMod_checkAcyclic`, `rtC0WithFfiMod_allFns_wf`,
   `rtC0WithFfiMod_moduleOk`, `rtC0WithFfiMod_fn_sound`, `rtC0WithFfiEnv_noExit_ffi`, and
   public `*_sound` theorems.
4. Concrete `Mem 64` non-vacuity (`XPost := fun _ _ _ _ => False`) inside `rtC0WithFfiEnv` on
   `nvFfiMem`:
   - `nv_ffi_carve_ba_reclaim`: top-down `s_end` carve, reduced-arena `ByteArray` `FfiRes.ok`,
     and `100%` scratch reclaim with `PreservesMeta`.
   - `nv_ffi_oom_no_abort`: non-aborting OOM on `lcnf_ffi_carve_scratch` (`0#64`) and
     `lcnf_ffi_ba_wrap_ok` (`5#64 = ffiResOomWord`).
   - `nv_ffi_nat_tagged_and_boxed`: `L=7` tagged `Nat` and `L=8` boxed `MPZ` (`RtMpzNatCanon` +
     `mpzNatCanon`) on `nvFfiMem`.
   - `nv_ffi_ba_to_nat_to_ba`: end-to-end `ByteArray → Nat → ByteArray` round-trip (`8B`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil

/-! ## 1. `ffiMod` `TableImpl`, `ModuleOk`, & `noExit` -/

private theorem ffiAllFns_of_mem {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, ffiAllFns_of_mem (fun _ hm => h _ (List.mem_cons_of_mem _ hm))⟩

private theorem ffiAllFns_append {P : Fn → Prop} :
    ∀ {fs1 fs2 : List Fn}, AllFns P fs1 → AllFns P fs2 → AllFns P (fs1 ++ fs2)
  | [], _, _, h2 => h2
  | _ :: _, _, h1, h2 => ⟨h1.1, ffiAllFns_append h1.2 h2⟩

theorem ffiMod_allFns_wf : AllFns Fn.Wf ffiMod.fns :=
  ffiAllFns_of_mem ffiMod_fns_wf

theorem ffiMod_tableImpl : TableImpl ffiEnv ffiMod.fns ffiSpecEntries := by
  dsimp only [ffiMod, lcnfFfi_fns, ffiSpecEntries, TableImpl]
  refine ⟨SpecEntry.Impl.of lcnf_ffi_get_end_wp,
    SpecEntry.Impl.of lcnf_ffi_carve_scratch_wp,
    SpecEntry.Impl.of lcnf_ffi_restore_scratch_wp,
    SpecEntry.Impl.of lcnf_ffi_ba_ptr_wp,
    SpecEntry.Impl.of lcnf_ffi_ba_len_wp,
    SpecEntry.Impl.of lcnf_ffi_mk_ok_wp,
    SpecEntry.Impl.of lcnf_ffi_ba_of_bytes_wp,
    SpecEntry.Impl.of lcnf_ffi_ba_wrap_ok_wp,
    SpecEntry.Impl.of lcnf_ffi_sentinel_byte_idx_wp,
    SpecEntry.Impl.of lcnf_ffi_nat_bytes_len_wp,
    SpecEntry.Impl.of lcnf_ffi_nat_bytes_ptr_wp,
    SpecEntry.Impl.of lcnf_ffi_nat_of_bytes_wp,
    SpecEntry.Impl.of lcnf_ffi_nat_wrap_ok_wp,
    SpecEntry.Impl.of lcnf_ffi_ba_to_nat_s_wp,
    SpecEntry.Impl.of lcnf_ffi_nat_s_to_ba_wp, trivial⟩

theorem ffiMod_moduleOk : ModuleOk ffiEnv ffiMod :=
  Env.ofTable_moduleOk ffiMod_checkAcyclic ffiMod_allFns_wf ffiMod_tableImpl

theorem ffiMod_fn_sound {fn : Fn} (hfn : fn ∈ ffiMod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hpre : ffiEnv fn.name fn.as fn.rs xs m Q X) :
    Func.wp ffiEnv fn.body xs m Q X :=
  Env.ofTable_sound (List.nodup_append.mp ffiMod_moduleOk.nodup).1
    ffiMod_tableImpl fn hfn xs m Q X hpre

private theorem ffi_ofTable_noExit_row {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    {e : SpecEntry} (he : e ∈ tbl) (hno : e.noExit = true)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X1 X2 : XPost}
    (h : Env.ofTable tbl e.name e.as e.rs xs m Q X1) :
    Env.ofTable tbl e.name e.as e.rs xs m Q X2 := by
  induction tbl with
  | nil => nomatch he
  | cons r rs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · obtain ⟨_, hs⟩ | ⟨hn, _⟩ := h
      · refine Or.inl ⟨⟨rfl, rfl, rfl⟩, ?_⟩
        simpa [SpecEntry.cast, SpecEntry.eff, hno] using hs
      · exact absurd ⟨rfl, rfl, rfl⟩ hn
    · have hne : r.name ≠ e.name := fun h => hnd.1 (h ▸ List.mem_map_of_mem hmem)
      exact (Env.ofTable_cons_ne hne _ _ _ _).mpr
        (ih hnd.2 hmem ((Env.ofTable_cons_ne hne _ _ _ _).mp h))

private theorem ffi_ofTable_noExit_at {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (i : Nat) (hi : i < tbl.length) (hno : tbl[i].noExit = true)
    {xs : Tup Val tbl[i].as} {m : Mem 64} {Q : Post tbl[i].rs} {X1 X2 : XPost}
    (h : Env.ofTable tbl tbl[i].name tbl[i].as tbl[i].rs xs m Q X1) :
    Env.ofTable tbl tbl[i].name tbl[i].as tbl[i].rs xs m Q X2 :=
  ffi_ofTable_noExit_row hnd (List.getElem_mem hi) hno h

theorem ffiEnv_noExit_fns {fn : Fn} (hfn : fn ∈ ffiMod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X1 X2 : XPost}
    (hpre : ffiEnv fn.name fn.as fn.rs xs m Q X1) :
    ffiEnv fn.name fn.as fn.rs xs m Q X2 := by
  simp only [ffiMod, lcnfFfi_fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 0 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 1 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 2 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 3 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 4 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 5 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 6 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 7 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 8 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 9 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 10 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 11 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 12 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 13 (by decide) rfl hpre
  · exact ffi_ofTable_noExit_at ffiSpecEntries_nodup 14 (by decide) rfl hpre

/-! ## 2. `MPZ` Bridge & Closed `rtC0WithFfiMod` Composition -/

theorem rtMpzNatCanon_iff_bnMpzNatCanon {obj : LcnfObj} {n : Nat} :
    RtMpzNatCanon obj n ↔ mpzNatCanon obj n := by
  unfold RtMpzNatCanon mpzNatCanon
  simp only [ffiMpzMaxLimbs, mpzMaxLimbs]

/-- Closed combined function list: `rtC0CoreMod.fns` followed by all 15 `ffiMod.fns`. -/
@[expose] def rtC0WithFfiFns : List Fn := rtC0CoreMod.fns ++ ffiMod.fns

/-- Closed verified C0 runtime + BigNum + Containers + FFI module (`0` externs). -/
@[expose] def rtC0WithFfiMod : Module :=
  { fns := rtC0WithFfiFns, externs := [], exits := rtC0CoreMod.exits }

theorem rtC0WithFfiMod_checkAcyclic : rtC0WithFfiMod.checkAcyclic = true := by
  t_kernel_rfl

theorem rtC0WithFfiMod_allFns_wf : AllFns Fn.Wf rtC0WithFfiMod.fns :=
  ffiAllFns_append rtC0CoreMod_allFns_wf ffiMod_allFns_wf

private def ffiPureMod : Module := { ffiMod with externs := [] }

/-- Unified specification environment for `rtC0WithFfiMod` combining `rtC0CoreMod` and `ffiMod`. -/
def rtC0WithFfiEnv : Env := fun f as bs xs m Q X =>
  Env.ofModule rtC0CoreMod rtC0CoreEnv f as bs xs m Q X ∨
    Env.ofModule ffiPureMod ffiEnv f as bs xs m Q X

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

theorem rtC0CoreMod_env_le_rtC0WithFfiEnv :
    ∀ f as bs xs m Q X,
      Env.ofModule rtC0CoreMod rtC0CoreEnv f as bs xs m Q X →
      rtC0WithFfiEnv f as bs xs m Q X :=
  fun _ _ _ _ _ _ _ h => Or.inl h

theorem ffiEnv_le_rtC0WithFfiEnv :
    ∀ f as bs xs m Q X, ffiEnv f as bs xs m Q X → rtC0WithFfiEnv f as bs xs m Q X := by
  refine ffiEnv_ofTable_sub (fun e he xs m Q X h => ?_)
  simp only [ffiSpecEntries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inr ⟨by decide, Env.ofTable_of_mem (by simp [ffiSpecEntries]) ffiSpecEntries_nodup h⟩
  · exact Or.inl ⟨by decide, rtC0CoreEnv_lcnf_alloc h⟩
  · exact Or.inl ⟨by decide, rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2Env_r2_mem_copy_bytes h)⟩

private theorem ffi_sig_mem_names {M : Module} {f : Sym} {as bs : List Ty}
    (h : (f, as, bs) ∈ M.sigs) : f ∈ M.names := by
  simp only [Module.sigs, Module.names, List.mem_append, List.mem_map] at h ⊢
  rcases h with ⟨fn, hfn, heq⟩ | ⟨ex, hex, heq⟩
  · exact Or.inl ⟨fn, hfn, congrArg Prod.fst heq⟩
  · exact Or.inr ⟨ex, hex, congrArg Prod.fst heq⟩

private theorem rtC0WithFfi_names_disjoint {f : Sym}
    (h1 : f ∈ rtC0CoreMod.names) (h2 : f ∈ ffiPureMod.names) : False := by
  have hnd : (rtC0CoreMod.fns.map Fn.name ++ ffiMod.fns.map Fn.name).Nodup := by
    have hc := rtC0WithFfiMod_checkAcyclic
    simp only [Module.checkAcyclic, Bool.and_eq_true] at hc
    have hmod := Module.namesNodup_of_checkNamesNodup hc.1
    simpa [Module.namesNodup, Module.names, rtC0WithFfiMod, rtC0WithFfiFns, List.map_append]
      using hmod
  have hdisj := (List.nodup_append.mp hnd).2.2
  have hc1 : f ∈ rtC0CoreMod.fns.map Fn.name := by
    simpa [Module.names, show rtC0CoreMod.externs = [] from rfl] using h1
  have hc2 : f ∈ ffiMod.fns.map Fn.name := by
    simpa [Module.names, ffiPureMod] using h2
  exact hdisj f hc1 f hc2 rfl

private theorem ffi_mem_split {α : Type 1} :
    ∀ (x : α) (xs : List α), x ∈ xs → ∃ pre post : List α, xs = pre ++ x :: post
  | _, [], h => nomatch h
  | x, y :: ys, h => by
    rcases List.mem_cons.mp h with rfl | hmem
    · exact ⟨[], ys, rfl⟩
    · obtain ⟨pre, post, rfl⟩ := ffi_mem_split x ys hmem
      exact ⟨y :: pre, post, rfl⟩

theorem rtC0WithFfiMod_moduleOk : ModuleOk rtC0WithFfiEnv rtC0WithFfiMod := by
  refine Module.moduleOk_of_checkAcyclic rtC0WithFfiMod_checkAcyclic
    rtC0WithFfiMod_allFns_wf.mem ?_
  intro fn hfn xs m Q X hpre
  simp only [rtC0WithFfiMod, rtC0WithFfiFns, List.mem_append] at hfn
  rcases hfn with hcore | hffi
  · rcases hpre with hc | hf
    · have hcoreMod := rtC0CoreMod_moduleOk.ofModule
      obtain ⟨pre, post, hsplit⟩ := ffi_mem_split fn rtC0CoreMod.fns hcore
      have hwp := (hcoreMod.fnsOk pre fn post hsplit).2.2 xs m Q X hc
      exact wp_env_mono rtC0CoreMod_env_le_rtC0WithFfiEnv _ _ hwp
    · exact False.elim (rtC0WithFfi_names_disjoint
        (ffi_sig_mem_names (by
          simp only [Module.sigs, List.mem_append, List.mem_map]
          exact Or.inl ⟨fn, hcore, rfl⟩))
        (ffi_sig_mem_names hf.1))
  · rcases hpre with hc | hf
    · exact False.elim (rtC0WithFfi_names_disjoint
        (ffi_sig_mem_names hc.1)
        (ffi_sig_mem_names (by
          simp only [Module.sigs, ffiPureMod, List.mem_append, List.mem_map]
          exact Or.inl ⟨fn, hffi, rfl⟩)))
    · exact wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (ffiMod_fn_sound hffi hf.2)

theorem rtC0WithFfiMod_fn_sound {fn : Fn} (hfn : fn ∈ rtC0WithFfiMod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hpre : rtC0WithFfiEnv fn.name fn.as fn.rs xs m Q X) :
    Func.wp rtC0WithFfiEnv fn.body xs m Q X := by
  obtain ⟨pre, post, hsplit⟩ := ffi_mem_split fn rtC0WithFfiMod.fns hfn
  exact (rtC0WithFfiMod_moduleOk.fnsOk pre fn post hsplit).2.2 xs m Q X hpre

theorem rtC0WithFfiEnv_noExit_ffi {fn : Fn} (hfn : fn ∈ ffiMod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X1 X2 : XPost}
    (hpre : rtC0WithFfiEnv fn.name fn.as fn.rs xs m Q X1) :
    rtC0WithFfiEnv fn.name fn.as fn.rs xs m Q X2 := by
  rcases hpre with hc | hf
  · exact False.elim (rtC0WithFfi_names_disjoint
      (ffi_sig_mem_names hc.1)
      (ffi_sig_mem_names (by
        simp only [Module.sigs, ffiPureMod, List.mem_append, List.mem_map]
        exact Or.inl ⟨fn, hfn, rfl⟩)))
  · exact Or.inr ⟨hf.1, ffiEnv_noExit_fns hfn hf.2⟩

/-! ## 3. Public `*_sound` Theorems in `rtC0WithFfiEnv` -/

theorem lcnf_ffi_carve_scratch_sound :
    ∀ xs m Q X, ffiCarveScratchSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_carve_scratch.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_carve_scratch_wp xs m Q X h)

theorem lcnf_ffi_restore_scratch_sound :
    ∀ xs m Q X, ffiRestoreScratchSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_restore_scratch.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_restore_scratch_wp xs m Q X h)

theorem lcnf_ffi_ba_of_bytes_sound :
    ∀ xs m Q X, ffiBaOfBytesSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_ba_of_bytes.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_ba_of_bytes_wp xs m Q X h)

theorem lcnf_ffi_ba_wrap_ok_sound :
    ∀ xs m Q X, ffiBaWrapOkSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_ba_wrap_ok.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_ba_wrap_ok_wp xs m Q X h)

theorem lcnf_ffi_nat_of_bytes_sound :
    ∀ xs m Q X, ffiNatOfBytesSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_nat_of_bytes.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_nat_of_bytes_wp xs m Q X h)

theorem lcnf_ffi_nat_bytes_len_sound :
    ∀ xs m Q X, ffiNatBytesLenSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_nat_bytes_len.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_nat_bytes_len_wp xs m Q X h)

theorem lcnf_ffi_nat_wrap_ok_sound :
    ∀ xs m Q X, ffiNatWrapOkSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_nat_wrap_ok.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_nat_wrap_ok_wp xs m Q X h)

theorem lcnf_ffi_ba_to_nat_s_sound :
    ∀ xs m Q X, ffiBaToNatSSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_ba_to_nat_s.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_ba_to_nat_s_wp xs m Q X h)

theorem lcnf_ffi_nat_s_to_ba_sound :
    ∀ xs m Q X, ffiNatSToBaSpec xs m Q X →
      Func.wp rtC0WithFfiEnv lcnf_ffi_nat_s_to_ba.body xs m Q X := fun xs m Q X h =>
  wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_nat_s_to_ba_wp xs m Q X h)

/-! ## 4. Concrete `Mem 64` Non-Vacuity (`XPost := False`) inside `rtC0WithFfiEnv` -/

/-- Concrete base address of the FFI test slab (`0x100000`, 8-byte aligned). -/
@[expose] def nvFfiBase : BitVec 64 := 0x100000#64
/-- Concrete worklist capacity (`8` words). -/
@[expose] def nvFfiWorkCap : Nat := 8
/-- Concrete bump arena capacity (`256` bytes). -/
@[expose] def nvFfiRem : Nat := 256
/-- Concrete BigNum scratch limb capacity (`32` limbs = `256` bytes). -/
@[expose] def nvFfiScrCap : Nat := 32
/-- Concrete scratch buffer address immediately following the `256B` bump arena. -/
@[expose] def nvFfiScr : BitVec 64 := nvFfiBase + 34008#64
/-- Concrete initial zeroed `32`-limb scratch buffer. -/
@[expose] def nvFfiScrLimbs : List (BitVec 64) := List.replicate nvFfiScrCap 0#64

/-- Concrete `LcnfC0Rt` header (`256B` arena `[+33752, +34008)`). -/
@[expose] def nvFfiHdr : LcnfC0Rt :=
  { s_large_free := 0#64
    s_ba_empty := 0#64
    s_cur := nvFfiBase + 33752#64
    s_end := nvFfiBase + 34008#64
    s_work := nvFfiBase + 33688#64
    s_work_cap := BitVec.ofNat 64 nvFfiWorkCap
    s_chunks := 0#64
    s_nchunks := 0#64
    s_chunks_cap := 0#64
    s_st_allocs := 0#64
    s_st_frees := 0#64
    s_st_live := 0#64
    s_st_peak_live := 0#64
    s_st_persistent := 0#64
    s_st_reused := 0#64
    s_st_cold_decs := 0#64
    s_st_bytes := 0#64 }

/-- Concrete transparent `RtC0State` (`rem = 256`, zeroed pools). -/
@[expose] def nvFfiRtSt : RtC0State where
  extraArgs := List.replicate rtExtraSlots 0#64
  globals := List.replicate rtGlobalSlots 0#64
  freeList := List.replicate rtNumClasses 0#64
  hdr := nvFfiHdr
  workBuf := List.replicate nvFfiWorkCap 0#64
  smallPools := fun _ => []
  largeNodes := []
  extraLen := List.length_replicate
  globalsLen := List.length_replicate
  freeListLen := List.length_replicate
  workLen := by decide
  curLeEnd := by decide
  arenaAlign := by decide
  curNz := by decide

/-- Serialized 17 header words (`136` bytes) of `LcnfC0Rt`. -/
@[expose] def nvFfiHdrWords (h : LcnfC0Rt) : List (BitVec 64) :=
  [h.s_large_free, h.s_ba_empty, h.s_cur, h.s_end, h.s_work, h.s_work_cap,
   h.s_chunks, h.s_nchunks, h.s_chunks_cap, h.s_st_allocs, h.s_st_frees,
   h.s_st_live, h.s_st_peak_live, h.s_st_persistent, h.s_st_reused,
   h.s_st_cold_decs, h.s_st_bytes]

/-- Concrete byte image (`34264` bytes) packing `LcnfC0FullRt` + `workBuf` + `256B` arena +
`256B` scratch buffer. -/
@[expose] def nvFfiRtBytes : List UInt8 :=
  List.replicate 256 0 ++ List.replicate 32768 0 ++ List.replicate 512 0 ++
  bytesN 8 (nvFfiHdrWords nvFfiHdr) ++ bytesN 8 [nvFfiScr, BitVec.ofNat 64 nvFfiScrCap] ++
  List.replicate 64 0 ++ List.replicate nvFfiRem 0 ++ List.replicate 256 0

/-- Concrete `Mem 64` slab at `nvFfiBase` satisfying `rtC0Inv` and BigNum scratch cells. -/
@[expose] def nvFfiMem : Mem 64 := nvFfiRtBytes.At nvFfiBase

private theorem ffi_replicate_append {α : Type} (x : α) (a b : Nat) :
    List.replicate a x ++ List.replicate b x = List.replicate (a + b) x := by
  induction a with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, ih, Nat.succ_add, List.replicate_succ]

private theorem bytesN8_replicate_zero (k : Nat) :
    bytesN 8 (List.replicate k (0#64 : BitVec 64)) = List.replicate (8 * k) (0 : UInt8) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hz : Int.toBytes 8 (0#64 : BitVec 64).toNat = List.replicate 8 (0 : UInt8) := by decide
    have hrep : List.replicate 8 (0 : UInt8) ++ List.replicate (8 * k) 0 =
        List.replicate (8 * (k + 1)) 0 := by
      rw [ffi_replicate_append, show 8 + 8 * k = 8 * (k + 1) by omega]
    rw [List.replicate_succ, bytesN, List.flatMap_cons, ← bytesN, ih, hz, hrep]

private theorem nvFfi_sep_append {P Q : Mem 64 → Prop} {a : BitVec 64}
    {bs1 bs2 : List UInt8} {n1 n2 : Nat}
    (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hb : (bytes a bs1 ⋆ bytes (a + BitVec.ofNat 64 n1) bs2) ((bs1 ++ bs2).At a) := by
    rw [← h1, ← bytes_append a bs1 bs2 (by rw [h1, h2]; exact hfit)]
    rfl
  exact sep_mono (fun _ hx => hx ▸ hp) (sep_mono_r (fun _ hx => hx ▸ hq) hb)

private theorem nvFfiSmallPools_emp (n : Nat) :
    smallPoolsAt (List.replicate rtNumClasses 0#64) (fun _ => []) n = emp := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : (List.replicate rtNumClasses 0#64).getD n 0#64 = 0#64 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    have hslot : smallPoolSlot n 0#64 [] = emp := by
      funext m; unfold smallPoolSlot; split <;> simp [smallFreeList]
    simp only [smallPoolsAt, ih, heq, hslot, sep_emp]

private theorem nvFfi_array64_zero {a : BitVec 64} {n : Nat} (hle : 8 * n ≤ 2 ^ 64) :
    array64 a (List.replicate n (0#64 : BitVec 64))
      ((List.replicate (8 * n) (0 : UInt8)).At a) := by
  rw [array64_eq_bytesN8 a (List.replicate n 0#64) (by rw [List.length_replicate]; exact hle),
    bytesN8_replicate_zero]
  rfl

private theorem nvFfiHdr_At :
    LcnfC0Rt.At nvFfiBase nvFfiHdr
      ((bytesN 8 (nvFfiHdrWords nvFfiHdr)).At (nvFfiBase + 33536)) := by
  have ha : array64 (nvFfiBase + 33536#64) (nvFfiHdrWords nvFfiHdr)
      ((bytesN 8 (nvFfiHdrWords nvFfiHdr)).At (nvFfiBase + 33536#64)) := by
    rw [array64_eq_bytesN8 _ _ (by decide)]
    rfl
  simp only [nvFfiHdrWords, array64, sep_emp] at ha
  have h0 : nvFfiBase + 33536#64 = nvFfiBase + 33536 := rfl
  simp only [h0,
    show (nvFfiBase + 33536) + 8 = nvFfiBase + 33544 by decide,
    show (nvFfiBase + 33544) + 8 = nvFfiBase + 33552 by decide,
    show (nvFfiBase + 33552) + 8 = nvFfiBase + 33560 by decide,
    show (nvFfiBase + 33560) + 8 = nvFfiBase + 33568 by decide,
    show (nvFfiBase + 33568) + 8 = nvFfiBase + 33576 by decide,
    show (nvFfiBase + 33576) + 8 = nvFfiBase + 33584 by decide,
    show (nvFfiBase + 33584) + 8 = nvFfiBase + 33592 by decide,
    show (nvFfiBase + 33592) + 8 = nvFfiBase + 33600 by decide,
    show (nvFfiBase + 33600) + 8 = nvFfiBase + 33608 by decide,
    show (nvFfiBase + 33608) + 8 = nvFfiBase + 33616 by decide,
    show (nvFfiBase + 33616) + 8 = nvFfiBase + 33624 by decide,
    show (nvFfiBase + 33624) + 8 = nvFfiBase + 33632 by decide,
    show (nvFfiBase + 33632) + 8 = nvFfiBase + 33640 by decide,
    show (nvFfiBase + 33640) + 8 = nvFfiBase + 33648 by decide,
    show (nvFfiBase + 33648) + 8 = nvFfiBase + 33656 by decide,
    show (nvFfiBase + 33656) + 8 = nvFfiBase + 33664 by decide] at ha
  unfold LcnfC0Rt.At
  have hc : ∀ a v : BitVec 64, cell64 a v = cell (t := i64) a v := fun _ _ => rfl
  simp only [hc] at ha
  exact sep_cast_ac ha (by ac_rfl)

theorem nvFfiMem_ok :
    (rtC0Inv nvFfiBase nvFfiRtSt ⋆
      bytes nvFfiScr (List.replicate 256 0) ⋆
      cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
      cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length)) nvFfiMem := by
  let b0 := List.replicate 256 (0 : UInt8)
  let b1 := List.replicate 32768 (0 : UInt8)
  let b2 := List.replicate 512 (0 : UInt8)
  let b3 := bytesN 8 (nvFfiHdrWords nvFfiHdr)
  let bMeta := bytesN 8 [nvFfiScr, BitVec.ofNat 64 nvFfiScrCap]
  let b4 := List.replicate 64 (0 : UInt8)
  let b5 := List.replicate nvFfiRem (0 : UInt8)
  let b6 := List.replicate 256 (0 : UInt8)
  have hl0 : b0.length = 256 := List.length_replicate
  have hl1 : b1.length = 32768 := List.length_replicate
  have hl2 : b2.length = 512 := List.length_replicate
  have hl3 : b3.length = 136 := by dsimp only [b3]; rw [bytesN_length]; decide
  have hlMeta : bMeta.length = 16 := by dsimp only [bMeta]; rw [bytesN_length]; decide
  have hl4 : b4.length = 64 := List.length_replicate
  have hl5 : b5.length = 256 := List.length_replicate
  have hl6 : b6.length = 256 := List.length_replicate
  have h0 : array64 nvFfiBase nvFfiRtSt.extraArgs (b0.At nvFfiBase) :=
    nvFfi_array64_zero (by decide)
  have h1 : array64 (nvFfiBase + BitVec.ofNat 64 rtGlobalsOff) nvFfiRtSt.globals
      (b1.At (nvFfiBase + 256#64)) :=
    nvFfi_array64_zero (by decide)
  have h2 : array64 (nvFfiBase + 33024#64) nvFfiRtSt.freeList (b2.At (nvFfiBase + 33024#64)) :=
    nvFfi_array64_zero (by decide)
  have h3 : LcnfC0Rt.At nvFfiBase nvFfiRtSt.hdr (b3.At (nvFfiBase + 33536#64)) := nvFfiHdr_At
  have hMeta : (cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
      cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length))
      (bMeta.At (nvFfiBase + 33672#64)) := by
    have ha : array64 (nvFfiBase + 33672#64) [nvFfiScr, BitVec.ofNat 64 nvFfiScrCap]
        (bMeta.At (nvFfiBase + 33672#64)) := by
      dsimp only [bMeta]; rw [array64_eq_bytesN8 _ _ (by decide)]; rfl
    have hlen : nvFfiScrLimbs.length = nvFfiScrCap := List.length_replicate
    rw [hlen]
    simpa [array64, sep_emp, BitVec.add_assoc] using ha
  have h4 : array64 nvFfiRtSt.hdr.s_work nvFfiRtSt.workBuf (b4.At (nvFfiBase + 33688#64)) :=
    nvFfi_array64_zero (by decide)
  have h5 : region nvFfiRtSt.hdr.s_cur nvFfiRtSt.rem (b5.At (nvFfiBase + 33752#64)) := by
    have hr : nvFfiRtSt.rem = 256 := by decide
    rw [hr]
    exact ⟨b5, hl5, rfl⟩
  have h6 : bytes nvFfiScr (List.replicate 256 0) (b6.At (nvFfiBase + 34008#64)) := rfl
  have h01 := nvFfi_sep_append hl0 hl1 (by decide) h0 h1
  have h012 := nvFfi_sep_append (by simp [hl0, hl1] : (b0 ++ b1).length = 33024)
    hl2 (by decide) h01 h2
  have h0123 := nvFfi_sep_append (by simp [hl0, hl1, hl2] : ((b0 ++ b1) ++ b2).length = 33536)
    hl3 (by decide) h012 h3
  have h0123m := nvFfi_sep_append
    (by simp [hl0, hl1, hl2, hl3] : (((b0 ++ b1) ++ b2) ++ b3).length = 33672)
    hlMeta (by decide) h0123 hMeta
  have h0123m4 := nvFfi_sep_append
    (by simp [hl0, hl1, hl2, hl3, hlMeta] :
      ((((b0 ++ b1) ++ b2) ++ b3) ++ bMeta).length = 33688)
    hl4 (by decide) h0123m h4
  have h0123m45 := nvFfi_sep_append
    (by simp [hl0, hl1, hl2, hl3, hlMeta, hl4] :
      (((((b0 ++ b1) ++ b2) ++ b3) ++ bMeta) ++ b4).length = 33752)
    hl5 (by decide) h0123m4 h5
  have hAll := nvFfi_sep_append
    (by simp [hl0, hl1, hl2, hl3, hlMeta, hl4, hl5] :
      ((((((b0 ++ b1) ++ b2) ++ b3) ++ bMeta) ++ b4) ++ b5).length = 34008)
    hl6 (by decide) h0123m45 h6
  have hsm : smallPoolsAt nvFfiRtSt.freeList nvFfiRtSt.smallPools rtNumClasses = emp :=
    nvFfiSmallPools_emp rtNumClasses
  have hlg : largeFreeList nvFfiRtSt.hdr.s_large_free nvFfiRtSt.largeNodes = emp := by
    funext m'; simp [largeFreeList, largeSeg, nvFfiRtSt, nvFfiHdr]
  unfold rtC0Inv
  rw [hsm, hlg, sep_emp, sep_emp]
  exact sep_cast_ac hAll (by ac_rfl)

private theorem nvScrBytes256_split {k : Nat} (hk : k ≤ 256) :
    bytes nvFfiScr (List.replicate 256 (0 : UInt8)) =
      (bytes nvFfiScr (List.replicate k 0) ⋆
        bytes (nvFfiScr + BitVec.ofNat 64 k) (List.replicate (256 - k) 0)) := by
  have hsum : k + (256 - k) = 256 := by omega
  have hlen : (List.replicate k (0 : UInt8)).length +
      (List.replicate (256 - k) (0 : UInt8)).length ≤ 2 ^ 64 := by
    simp only [List.length_replicate]; omega
  have hb := bytes_append nvFfiScr (List.replicate k (0 : UInt8))
    (List.replicate (256 - k) (0 : UInt8)) hlen
  rw [List.length_replicate, ffi_replicate_append, hsum] at hb
  exact hb

/-- NV 1 (`XPost := False`): Top-down `64B` scratch carve (`s_end`: `256 -> 192`), `3B` `ByteArray`
`FfiRes.ok` allocation inside the carved `rtC0Inv`, and `100%` scratch reclaim with
`PreservesMeta`. -/
theorem nv_ffi_carve_ba_reclaim :
    Func.wp rtC0WithFfiEnv lcnf_ffi_carve_scratch.body (nvFfiBase, 64#64, ()) nvFfiMem
      (fun (wptr, _) m1 =>
        wptr ≠ 0#64 ∧ wptr.toNat % 8 = 0 ∧
        ∃ bs : List UInt8, bs.length = 3 ∧
        Func.wp rtC0WithFfiEnv lcnf_ffi_ba_wrap_ok.body (nvFfiBase, wptr, 3#64, ()) m1
          (fun (okP, _) m2 =>
            okP ≠ 0#64 ∧ okP.toNat % 8 = 0 ∧
            Func.wp rtC0WithFfiEnv lcnf_ffi_restore_scratch.body
              (nvFfiBase, nvFfiRtSt.hdr.s_end, ()) m2
              (fun () m3 =>
                ∃ st3 ba, st3.PreservesMeta nvFfiRtSt ∧
                  st3.hdr.s_end = nvFfiRtSt.hdr.s_end ∧
                  256 - baAllocBytes 3 - 16 ≤ st3.rem ∧ st3.rem ≤ 256 ∧
                  BaCanon ba ∧ ba.scalarData = bs ∧
                  (rtC0Inv nvFfiBase st3 ⋆ lcnfObjMem (mkFfiResOkObj okP ba.addr) ⋆
                    lcnfObjMem ba ⋆ bytes nvFfiScr (List.replicate 256 0) ⋆
                    cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
                    cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length)) m3)
              (fun _ _ _ _ => False))
          (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) := by
  let frame0 : Mem 64 → Prop :=
    bytes nvFfiScr (List.replicate 256 0) ⋆
    cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
    cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length)
  apply lcnf_ffi_carve_scratch_sound
  refine ⟨nvFfiRtSt, frame0, sep_cast_ac nvFfiMem_ok (by dsimp only [frame0]; ac_rfl), ?_⟩
  have hok : ffiCarveOk nvFfiRtSt 64#64 := by decide
  split
  case isFalse hno => exact absurd hok hno
  case isTrue hok' =>
    intro wend wcap wptr _ stCarved tailPad m1 hw0 hw8 _ hpr1 hs1end hm1
    have hwptrEq : wptr = nvFfiRtSt.hdr.s_end - 64#64 := by
      change ffiCarveWptr nvFfiRtSt 64#64 = nvFfiRtSt.hdr.s_end - 64#64; decide
    have hwcap64 : wcap = 64 := by change ffiCarveWcap 64#64 = 64; decide
    have hpad0 : tailPad = 0 := by
      change nvFfiRtSt.hdr.s_end.toNat - (ffiCarveWend nvFfiRtSt.hdr.s_end).toNat = 0; decide
    rw [hwcap64, hpad0, region_zero] at hm1
    have hm1reg : (region wptr 64 ⋆ (rtC0Inv nvFfiBase stCarved ⋆ frame0)) m1 :=
      sep_cast_ac hm1 (by ac_rfl)
    obtain ⟨bsAll, hbsLen, hm1bytes⟩ := region_sep_elim hm1reg
    change (bytes wptr bsAll ⋆ (rtC0Inv nvFfiBase stCarved ⋆ frame0)) m1 at hm1bytes
    let bs3 := bsAll.take 3
    let bs61 := bsAll.drop 3
    have hbs3Len : bs3.length = 3 := by simp [bs3, hbsLen]
    have hm1split : (rtC0Inv nvFfiBase stCarved ⋆ bytes wptr bs3 ⋆
        (bytes (wptr + 3#64) bs61 ⋆ frame0)) m1 := by
      have hjoin : bsAll = bs3 ++ bs61 := (List.take_append_drop 3 bsAll).symm
      rw [hjoin, bytes_append wptr bs3 bs61 (by simp [bs3, bs61, hbsLen])] at hm1bytes
      rw [← hbs3Len]
      exact sep_cast_ac hm1bytes (by ac_rfl)
    refine ⟨hw0, hw8, bs3, hbs3Len, ?_⟩
    apply lcnf_ffi_ba_wrap_ok_sound
    let frame1 : Mem 64 → Prop := bytes (wptr + 3#64) bs61 ⋆ frame0
    refine ⟨stCarved, bs3, frame1, hbs3Len.trans (by decide),
      sep_cast_ac hm1split (by dsimp only [frame1]), ?_⟩
    have hrem1 : stCarved.rem = 192 := by
      have h1 : stCarved.rem =
          (ffiCarveWptr nvFfiRtSt 64#64).toNat - nvFfiRtSt.hdr.s_cur.toNat := rfl
      rw [h1]; decide
    have hfit2 : (3#64 : BitVec 64).toNat ≤ ffiBaMaxCap ∧
        baAllocBytes (3#64 : BitVec 64).toNat + 16 ≤ stCarved.rem := by
      rw [hrem1]; decide
    rw [ite_eq_left hfit2]
    intro okP baAddr st2 m2 hok0 hok8 _ _ hpr2 hrem2Le hrem2Lo baObj okObj hbaCan _hokCan hm2
    refine ⟨hok0, hok8, ?_⟩
    apply lcnf_ffi_restore_scratch_sound
    have hm2reg : (rtC0Inv nvFfiBase st2 ⋆ region wptr 64 ⋆ region nvFfiRtSt.hdr.s_end 0 ⋆
        (lcnfObjMem (mkFfiResOkObj okP baAddr) ⋆ lcnfObjMem baObj ⋆ frame0)) m2 := by
      have hback : (bytes wptr bs3 ⋆ bytes (wptr + 3#64) bs61) = bytes wptr bsAll := by
        have h3 : BitVec.ofNat 64 bs3.length = 3#64 := by rw [hbs3Len]
        rw [← h3, ← bytes_append wptr bs3 bs61 (by simp [bs3, bs61, hbsLen]),
          List.take_append_drop]
      have hbytes : (bytes wptr bsAll ⋆
          (rtC0Inv nvFfiBase st2 ⋆ lcnfObjMem (mkFfiResOkObj okP baAddr) ⋆
            lcnfObjMem baObj ⋆ frame0)) m2 := by
        dsimp only [frame1] at hm2
        rw [← hback]
        exact sep_cast_ac hm2 (by dsimp only [okObj]; ac_rfl)
      have hreg := sep_mono (fun _ hb => bytes_to_region hb) hbytes
      rw [hbsLen, region_zero] at *
      exact sep_cast_ac hreg (by ac_rfl)
    refine ⟨st2, wptr, nvFfiRtSt.hdr.s_end, 64, 0,
      lcnfObjMem (mkFfiResOkObj okP baAddr) ⋆ lcnfObjMem baObj ⋆ frame0,
      hpr2.2.2.2.1.symm.trans hs1end, by rw [hwptrEq]; decide, by rw [hwptrEq]; decide, by decide,
      hm2reg, ?_⟩
    intro st3 m3 hpr3 hs3end hrem3 hm3
    have hbaAddr : baObj.addr = baAddr := rfl
    have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
    have hfitB : baAllocBytes 3 + 16 ≤ 192 := by
      have h := hfit2.2
      rwa [hrem1, h3] at h
    rw [hrem1] at hrem2Le
    rw [hrem1, h3] at hrem2Lo
    refine ⟨st3, baObj, ?_, hs3end, ?_, ?_, hbaCan, rfl, ?_⟩
    · exact RtC0State.preservesMeta_of_exceptEnd
        (hpr1.trans (hpr2.toExceptEnd.trans hpr3)) hs3end
    · rw [hrem3]; omega
    · rw [hrem3]; omega
    · rw [hbaAddr]
      exact sep_cast_ac hm3 (by dsimp only [frame0]; ac_rfl)

/-- NV 2 (`XPost := False`): Non-aborting OOM on both `lcnf_ffi_carve_scratch` (`0#64`) and
`lcnf_ffi_ba_wrap_ok` (`5#64 = ffiResOomWord`) on `nvFfiMem` (`rem = 256`). -/
theorem nv_ffi_oom_no_abort :
    Func.wp rtC0WithFfiEnv lcnf_ffi_carve_scratch.body (nvFfiBase, 512#64, ()) nvFfiMem
      (fun (w, _) m' => w = 0#64 ∧ m' = nvFfiMem) (fun _ _ _ _ => False) ∧
    Func.wp rtC0WithFfiEnv lcnf_ffi_ba_wrap_ok.body (nvFfiBase, nvFfiScr, 248#64, ()) nvFfiMem
      (fun (w, _) m' => w = ffiResOomWord ∧ m' = nvFfiMem) (fun _ _ _ _ => False) := by
  refine ⟨?_, ?_⟩
  · apply lcnf_ffi_carve_scratch_sound
    let frame0 : Mem 64 → Prop :=
      bytes nvFfiScr (List.replicate 256 0) ⋆
      cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
      cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length)
    refine ⟨nvFfiRtSt, frame0, sep_cast_ac nvFfiMem_ok (by dsimp only [frame0]; ac_rfl), ?_⟩
    have hn : ¬ ffiCarveOk nvFfiRtSt 512#64 := by decide
    split
    case isTrue hok => exact absurd hok hn
    case isFalse _ => exact ⟨rfl, rfl⟩
  · apply lcnf_ffi_ba_wrap_ok_sound
    have hm : (rtC0Inv nvFfiBase nvFfiRtSt ⋆
        bytes nvFfiScr (List.replicate 248 0) ⋆
        (bytes (nvFfiScr + 248#64) (List.replicate 8 0) ⋆
          cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
          cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length))) nvFfiMem := by
      have h0 := nvFfiMem_ok
      rw [nvScrBytes256_split (k := 248) (by decide)] at h0
      exact sep_cast_ac h0 (by ac_rfl)
    have hlen248 : (List.replicate 248 (0 : UInt8)).length = (248#64 : BitVec 64).toNat := by
      rw [List.length_replicate]; rfl
    refine ⟨nvFfiRtSt, List.replicate 248 0, _, hlen248, hm, ?_⟩
    have hnot : ¬ ((248#64 : BitVec 64).toNat ≤ ffiBaMaxCap ∧
        baAllocBytes (248#64).toNat + 16 ≤ nvFfiRtSt.rem) := by
      intro h
      have hrem : nvFfiRtSt.rem = 256 := by decide
      have hsz : baAllocBytes (248#64).toNat = 272 := by decide
      omega
    rw [ite_eq_right hnot]
    exact ⟨rfl, rfl⟩

/-- NV 3 (`XPost := False`): Sentineled `Nat` marshaling on `nvFfiMem`:
- `L=7` zero-bytes yields tagged unboxed `0x0200000000000001#64` without arena allocation.
- `L=8` zero-bytes yields zero-copy boxed `2`-limb `MPZ` (`RtMpzNatCanon` and `mpzNatCanon` via
  `rtMpzNatCanon_iff_bnMpzNatCanon`) with byte length `8#64`. -/
theorem nv_ffi_nat_tagged_and_boxed :
    Func.wp rtC0WithFfiEnv lcnf_ffi_nat_of_bytes.body (nvFfiBase, nvFfiScr, 7#64, ()) nvFfiMem
      (fun (w, _) m' =>
        w = BitVec.ofNat 64 (2 * (2 ^ 56) + 1) ∧ m' = nvFfiMem)
      (fun _ _ _ _ => False) ∧
    Func.wp rtC0WithFfiEnv lcnf_ffi_nat_of_bytes.body (nvFfiBase, nvFfiScr, 8#64, ()) nvFfiMem
      (fun (p, _) m1 =>
        ∃ (_st1 : RtC0State) (obj : LcnfObj),
          p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ (p &&& 1#64) = 0#64 ∧
          obj.addr = p ∧ RtMpzNatCanon obj (2 ^ 64) ∧
          mpzNatCanon obj (2 ^ 64) ∧
          Func.wp rtC0WithFfiEnv lcnf_ffi_nat_bytes_len.body (p, ()) m1
            (fun (len, _) m2 => len = 8#64 ∧ m2 = m1) (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) := by
  refine ⟨?_, ?_⟩
  · apply lcnf_ffi_nat_of_bytes_sound
    have hm : (rtC0Inv nvFfiBase nvFfiRtSt ⋆
        bytes nvFfiScr (List.replicate 7 0) ⋆
        (bytes (nvFfiScr + 7#64) (List.replicate 249 0) ⋆
          cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
          cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length))) nvFfiMem := by
      have h0 := nvFfiMem_ok
      rw [nvScrBytes256_split (k := 7) (by decide)] at h0
      exact sep_cast_ac h0 (by ac_rfl)
    refine ⟨nvFfiRtSt, List.replicate 7 0, _, by decide, hm, ?_⟩
    rw [ite_eq_left (by decide)]
    have hnat : natOfBytesS (List.replicate 7 0) = 2 ^ 56 := by decide
    rw [hnat]
    exact ⟨rfl, rfl⟩
  · apply lcnf_ffi_nat_of_bytes_sound
    let frameRest : Mem 64 → Prop :=
      bytes (nvFfiScr + 8#64) (List.replicate 248 0) ⋆
      cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
      cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length)
    have hm : (rtC0Inv nvFfiBase nvFfiRtSt ⋆
        bytes nvFfiScr (List.replicate 8 0) ⋆ frameRest) nvFfiMem := by
      have h0 := nvFfiMem_ok
      rw [nvScrBytes256_split (k := 8) (by decide)] at h0
      exact sep_cast_ac h0 (by dsimp only [frameRest]; ac_rfl)
    refine ⟨nvFfiRtSt, List.replicate 8 0, frameRest, by decide, hm, ?_⟩
    rw [ite_eq_right (by decide), ite_eq_left (by decide)]
    intro p st1 obj m1 hp0 hp8 hpEven _ _ _ haddr hrtCan _ hm1
    have hnat : natOfBytesS (List.replicate 8 0) = 2 ^ 64 := by decide
    rw [hnat] at hrtCan
    have hbnCan : mpzNatCanon obj (2 ^ 64) :=
      rtMpzNatCanon_iff_bnMpzNatCanon.mp hrtCan
    refine ⟨st1, obj, hp0, hp8, hpEven, haddr, hrtCan, hbnCan, ?_⟩
    refine wp_env_mono ffiEnv_le_rtC0WithFfiEnv _ _ (lcnf_ffi_nat_bytes_len_wp _ _ _ _ ?_)
    refine ⟨2 ^ 64, [obj],
      rtC0Inv nvFfiBase st1 ⋆ bytes nvFfiScr (List.replicate 8 0) ⋆ frameRest, ?_, ?_, ?_⟩
    · rw [RtNatRep, ite_eq_right (by decide)]
      exact ⟨hpEven, obj, List.mem_singleton_self _, haddr, hrtCan⟩
    · rw [show lcnfHeap [obj] = lcnfObjMem obj by simp [lcnfHeap, sep_emp]]
      exact sep_cast_ac hm1 (by ac_rfl)
    · have hbs : bytesOfNatS (2 ^ 64) = some (List.replicate 8 0) := by decide
      rw [hbs]
      exact ⟨rfl, rfl⟩

/-- NV 4 (`XPost := False`): Bidirectional `ByteArray ↔ Sentineled Nat` round-trip (`8B`) inside
`rtC0WithFfiEnv` on `nvFfiMem`. -/
theorem nv_ffi_ba_to_nat_to_ba :
    Func.wp rtC0WithFfiEnv lcnf_ffi_ba_of_bytes.body (nvFfiBase, nvFfiScr, 8#64, ()) nvFfiMem
      (fun (ba1, _) m1 =>
        Func.wp rtC0WithFfiEnv lcnf_ffi_ba_to_nat_s.body (nvFfiBase, ba1, ()) m1
          (fun (ok1, _) m2 =>
            ∃ okObj1 natP natObj, okObj1 = mkFfiResOkObj ok1 natP ∧
              RtMpzNatCanon natObj (2 ^ 64) ∧
              Func.wp rtC0WithFfiEnv lcnf_ffi_nat_s_to_ba.body (nvFfiBase, natP, ()) m2
                (fun (ok2, _) _m3 =>
                  ∃ okObj2 ba2Obj, okObj2 = mkFfiResOkObj ok2 ba2Obj.addr ∧
                    BaCanon ba2Obj ∧ ba2Obj.scalarData = List.replicate 8 0)
                (fun _ _ _ _ => False))
          (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) := by
  let frameRest : Mem 64 → Prop :=
    bytes (nvFfiScr + 8#64) (List.replicate 248 0) ⋆
    cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
    cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length)
  have hm0 : (rtC0Inv nvFfiBase nvFfiRtSt ⋆
      bytes nvFfiScr (List.replicate 8 0) ⋆ frameRest) nvFfiMem := by
    have h0 := nvFfiMem_ok
    rw [nvScrBytes256_split (k := 8) (by decide)] at h0
    exact sep_cast_ac h0 (by dsimp only [frameRest]; ac_rfl)
  apply lcnf_ffi_ba_of_bytes_sound
  refine ⟨nvFfiRtSt, List.replicate 8 0, frameRest, by decide, hm0, ?_⟩
  rw [ite_eq_left (by decide)]
  intro ba1 st1 m1 hba0 hba8 hpr1 hrem1Le hrem1Lo ba1Obj hbaCan hm1
  have hrem1 : 224 ≤ st1.rem := by
    have : nvFfiRtSt.rem = 256 := by decide
    have : baAllocBytes (8#64 : BitVec 64).toNat = 32 := by decide
    omega
  apply lcnf_ffi_ba_to_nat_s_sound
  refine ⟨st1, ba1Obj, bytes nvFfiScr (List.replicate 8 0) ⋆ frameRest, rfl, hbaCan,
    sep_cast_ac hm1 (by ac_rfl), ?_⟩
  have hlenBa : ba1Obj.scalarData.length = 8 := rfl
  have hgt7 : ¬ ba1Obj.scalarData.length ≤ 7 := by rw [hlenBa]; decide
  have hfit1 : natSAllocBytes ba1Obj.scalarData.length + 16 ≤ st1.rem := by
    have hsz : natSAllocBytes 8 + 16 = 48 := by decide
    rw [hlenBa]; omega
  rw [ite_eq_right hgt7, ite_eq_left hfit1]
  intro ok1 natP st2 natObj m2 hok10 hok18 _ _ hnatEven _ hrem2Le hrem2Lo hnatAddr hnatCan hmpzCan
    hok1Can hm2
  have hnatVal : natOfBytesS ba1Obj.scalarData = 2 ^ 64 := by
    rw [show ba1Obj.scalarData = List.replicate 8 0 from rfl]; decide
  rw [hnatVal] at hnatCan
  refine ⟨mkFfiResOkObj ok1 natP, natP, natObj, rfl, hnatCan, ?_⟩
  have hrem2 : 176 ≤ st2.rem := by
    have hsz : natSAllocBytes 8 + 16 = 48 := by decide
    rw [hlenBa] at hrem2Lo; omega
  apply lcnf_ffi_nat_s_to_ba_sound
  have hmScr : (bytes nvFfiScr (List.replicate 8 0) ⋆ frameRest) =
      (array64 nvFfiScr nvFfiScrLimbs ⋆
        cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
        cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length)) := by
    dsimp only [frameRest]
    have hscrEq : array64 nvFfiScr nvFfiScrLimbs = bytes nvFfiScr (List.replicate 256 0) := by
      have hfitScr : 8 * nvFfiScrLimbs.length ≤ 2 ^ 64 := by
        rw [show nvFfiScrLimbs.length = 32 from List.length_replicate]; decide
      rw [array64_eq_bytesN8 nvFfiScr nvFfiScrLimbs hfitScr]
      dsimp only [nvFfiScrLimbs, nvFfiScrCap]
      rw [bytesN8_replicate_zero]
    rw [hscrEq, nvScrBytes256_split (k := 8) (by decide)]
    ac_rfl
  let scrapFrame := lcnfObjMem (mkFfiResOkObj ok1 natP) ⋆ lcnfObjMem ba1Obj
  have hlt263 : ¬ (2 ^ 64 : Nat) < 2 ^ 63 := by decide
  have hm2' : (rtC0Inv nvFfiBase st2 ⋆
      cell64 (nvFfiBase + 33672#64) nvFfiScr ⋆
      cell64 (nvFfiBase + 33680#64) (BitVec.ofNat 64 nvFfiScrLimbs.length) ⋆
      array64 nvFfiScr nvFfiScrLimbs ⋆ lcnfHeap [natObj] ⋆ scrapFrame) m2 := by
    rw [show lcnfHeap [natObj] = lcnfObjMem natObj by simp [lcnfHeap, sep_emp]]
    have hm2a : (rtC0Inv nvFfiBase st2 ⋆ lcnfObjMem (mkFfiResOkObj ok1 natP) ⋆
        lcnfObjMem natObj ⋆ lcnfObjMem ba1Obj ⋆
        (bytes nvFfiScr (List.replicate 8 0) ⋆ frameRest)) m2 := sep_cast_ac hm2 (by ac_rfl)
    rw [hmScr] at hm2a
    exact sep_cast_ac hm2a (by dsimp only [scrapFrame]; ac_rfl)
  refine ⟨st2, nvFfiScr, nvFfiScrLimbs, 2 ^ 64, [natObj], scrapFrame,
    by dsimp only [nvFfiScrLimbs]; rw [List.length_replicate]; decide, ?_, hm2', ?_⟩
  · rw [RtNatRep, ite_eq_right hlt263]
    exact ⟨hnatEven, natObj, List.mem_singleton_self _, hnatAddr, hnatCan⟩
  · have hnatDec : bytesOfNatS (2 ^ 64) = some (List.replicate 8 0) := by decide
    rw [hnatDec]
    dsimp only
    have hnot7 : ¬ ((List.replicate 8 (0 : UInt8)).length ≤ 7 ∧
        (nvFfiScr = 0#64 ∨ nvFfiScrLimbs.length = 0)) := by
      intro h; exact absurd h.1 (by decide)
    have hfit2 : (List.replicate 8 (0 : UInt8)).length ≤ ffiBaMaxCap ∧
        baAllocBytes (List.replicate 8 (0 : UInt8)).length + 16 ≤ st2.rem := by
      have hm1' : (List.replicate 8 (0 : UInt8)).length ≤ ffiBaMaxCap := by decide
      have hsz : baAllocBytes (List.replicate 8 (0 : UInt8)).length + 16 = 48 := by decide
      omega
    rw [ite_eq_right hnot7, ite_eq_left hfit2]
    intro ok2 ba2 _ _ _ _ _ _ _ _ _ hba2Can _ _
    exact ⟨mkFfiResOkObj ok2 ba2, mkBaObj ba2 1#32 8 (List.replicate 8 0), rfl, hba2Can, rfl⟩

end LeanQbe.T.LeanLCNF
