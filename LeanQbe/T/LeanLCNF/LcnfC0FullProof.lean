module

public import LeanQbe.T.LeanLCNF.LcnfC0Full
public import LeanQbe.T.LeanLCNF.LcnfC0RtProof
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProofAlloc
import all Kraken.Mem
import all Kraken.Separation

/-!
# Composed `ModuleOk`, `TableImpl`, `LcnfC0FullInv`, and Non-Vacuity (`LcnfC0FullProof`)

Composes the four verified pure-C0 runtime modules (`R0`, `R1`, `R2`, `R2b`) into a single closed
specification table `rtC0CoreSpecEntries` (80 entries) and environment `rtC0CoreEnv`:

1. **Cross-module spec alignment:** R1 states its contracts directly over `LcnfC0RtSpec`, so
   `lcnf_alloc` is unified under R2b's progress-aware `lcnfAllocRemSpec` (subsuming the shared
   R0/R1/R2 `lcnfAllocSpec` via `lcnfAllocSpec_to_rem` and `lcnf_alloc_rem_wp`).
2. **Whole-module soundness (`ModuleOk rtC0CoreEnv rtC0CoreMod`):**
   - Proves `rtC0CoreMod_tableImpl : TableImpl rtC0CoreEnv rtC0CoreMod.fns rtC0CoreSpecEntries`
     and `rtC0CoreMod_moduleOk : ModuleOk rtC0CoreEnv rtC0CoreMod` (pure `std3` axioms, 0 externs).
3. **Unified runtime invariant (`LcnfC0FullInv`) & concrete `Mem 64` cross-module non-vacuity:**
   - Defines `LcnfC0FullInv` combining R0's `rtC0Inv` (`0..33671`) with R1's trailing `scratch`
     metadata (`33672..33687`) and scratch array (definitionally R1's `bigNumRtInv`).
   - Proves concrete `Mem 64` (`XPost := False`) cross-module non-vacuity inside `rtC0CoreEnv`
     covering R0 (`lcnf_dec_ref_cold`), R1 (`lcnf_nat_slow`), R2 (`lcnf_ba_empty`), and R2b
     (`lcnf_nat_to_str`, chained `lcnf_str_alloc` → `lcnf_array_replicate`).
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

public section

/-! ## 1. Unified Specification Table (`rtC0CoreSpecEntries`, `rtC0CoreEnv`) -/

/-- Unified R0 rows (`lcnf_alloc` upgraded to progress-aware `lcnfAllocRemSpec`, `noExit = false`).
-/
def rtC0R0SpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn lcnf_alloc lcnfAllocRemSpec false
  , SpecEntry.ofFn lcnf_free_obj lcnfFreeObjSpec false
  , SpecEntry.ofFn lcnf_dec_ref_cold lcnfDecRefColdSpec false
  , SpecEntry.ofFn lcnf_mark_persistent lcnfMarkPersistentSpec false
  , SpecEntry.ofFn lcnf_clo_under lcnfCloUnderSpec false ]

/-- The 34 defined-function rows from `rtR1SpecEntries` (dropping its 2 R0 extern rows). -/
def rtC0R1SpecEntries : List SpecEntry := rtR1SpecEntries.take 34

/-- The 22 defined-function rows from `rtR2SpecEntries` (dropping its 4 R0 extern rows). -/
def rtC0R2SpecEntries : List SpecEntry := rtR2SpecEntries.take 22

/-- The 19 defined-function rows from `rtR2bSpecEntries` (dropping its 4 R0 + 6 R2 extern rows).
-/
def rtC0R2bSpecEntries : List SpecEntry := rtR2bSpecEntries.take 19

/-- Unified 80-row specification table aligned row-by-row with `rtC0CoreMod.fns`. -/
def rtC0CoreSpecEntries : List SpecEntry :=
  rtC0R0SpecEntries ++ rtC0R1SpecEntries ++ rtC0R2SpecEntries ++ rtC0R2bSpecEntries

/-- Closed specification environment of the unified 80-function pure-C0 runtime. -/
def rtC0CoreEnv : Env := Env.ofTable rtC0CoreSpecEntries

/-! ## 2. Unified `Mem 64` Runtime State Invariant (`LcnfC0FullInv`) -/

/-- Unified `Mem 64` runtime invariant combining R0's slab `0..33671` (`rtC0Inv`) with R1's trailing
`scratch` / `scratch_cap` header fields (`33672..33687`) and scratch limb buffer. -/
def LcnfC0FullInv (rt : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) : Mem 64 → Prop :=
  rtC0Inv rt st ⋆
  cell64 (rt + 33672#64) scr ⋆
  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
  array64 scr scrLimbs

end

/-! ## 3. Cross-Module Spec Alignment -/

public section

theorem LcnfC0FullInv_eq_bigNumRtInv (rt : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) :
    LcnfC0FullInv rt st scr scrLimbs = bigNumRtInv rt st scr scrLimbs := by
  unfold LcnfC0FullInv bigNumRtInv; rfl

/-- Weakening from R0/R2 `lcnfAllocSpec` to R2b's progress-aware `lcnfAllocRemSpec`. -/
theorem lcnfAllocSpec_to_rem {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lcnfAllocSpec xs m Q X) : lcnfAllocRemSpec xs m Q X := by
  rcases xs with ⟨rt, sz, ⟨⟩⟩
  rcases h with ⟨st, R, h1, h2, h3, h4, hm, hk⟩
  exact ⟨st, R, h1, h2, h3, h4, hm, fun p st' m' hp0 hp8 hpr hle _ hm' =>
    hk p st' m' hp0 hp8 hpr hle hm'⟩

/-! ## 4. Unified `TableImpl` and `ModuleOk` Composition Across R0 + R1 + R2 + R2b -/

theorem rtC0CoreSpecEntries_nodup : (rtC0CoreSpecEntries.map SpecEntry.name).Nodup := by
  refine listNodup_nodup ?_
  decide

private theorem env_ofTable_sub {tbl : List SpecEntry} {Γ' : Env}
    (h : ∀ e ∈ tbl, ∀ xs m Q X, e.eff xs m Q X → Γ' e.name e.as e.rs xs m Q X) :
    ∀ f as bs xs m Q X, Env.ofTable tbl f as bs xs m Q X → Γ' f as bs xs m Q X := by
  induction tbl with
  | nil => intro _ _ _ _ _ _ _ hf; exact hf.elim
  | cons e es ih =>
    intro f as bs xs m Q X hs
    rcases hs with ⟨⟨rfl, rfl, rfl⟩, he⟩ | ⟨_, hrest⟩
    · exact h e List.mem_cons_self xs m Q X he
    · exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')) f as bs xs m Q X hrest

private theorem rtC0CoreEnv_of_mem {e : SpecEntry} (he : e ∈ rtC0CoreSpecEntries)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost} (h : e.eff xs m Q X) :
    rtC0CoreEnv e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem he rtC0CoreSpecEntries_nodup h

theorem rtC0CoreEnv_lcnf_alloc {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lcnfAllocRemSpec xs m Q X) : rtC0CoreEnv "lcnf_alloc" [i64, i64] [i64] xs m Q X :=
  rtC0CoreEnv_of_mem (e := SpecEntry.ofFn lcnf_alloc lcnfAllocRemSpec false)
    (by simp [rtC0CoreSpecEntries, rtC0R0SpecEntries]) h

theorem rtC0CoreEnv_lcnf_free_obj {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : lcnfFreeObjSpec xs m Q X) : rtC0CoreEnv "lcnf_free_obj" [i64, i64] [] xs m Q X :=
  rtC0CoreEnv_of_mem (e := SpecEntry.ofFn lcnf_free_obj lcnfFreeObjSpec false)
    (by simp [rtC0CoreSpecEntries, rtC0R0SpecEntries]) h

theorem rtC0CoreEnv_lcnf_dec_ref_cold {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : lcnfDecRefColdSpec xs m Q X) :
    rtC0CoreEnv "lcnf_dec_ref_cold" [i64, i64] [] xs m Q X :=
  rtC0CoreEnv_of_mem (e := SpecEntry.ofFn lcnf_dec_ref_cold lcnfDecRefColdSpec false)
    (by simp [rtC0CoreSpecEntries, rtC0R0SpecEntries]) h

theorem rtC0CoreEnv_lcnf_mark_persistent {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : lcnfMarkPersistentSpec xs m Q X) :
    rtC0CoreEnv "lcnf_mark_persistent" [i64, i64] [] xs m Q X :=
  rtC0CoreEnv_of_mem (e := SpecEntry.ofFn lcnf_mark_persistent lcnfMarkPersistentSpec false)
    (by simp [rtC0CoreSpecEntries, rtC0R0SpecEntries]) h

theorem rtC0CoreEnv_lcnf_clo_under {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfCloUnderSpec xs m Q X) :
    rtC0CoreEnv "lcnf_clo_under" [i64, i64, i64] [i64] xs m Q X :=
  rtC0CoreEnv_of_mem (e := SpecEntry.ofFn lcnf_clo_under lcnfCloUnderSpec false)
    (by simp [rtC0CoreSpecEntries, rtC0R0SpecEntries]) h

/-- Every R1 contract in `rtR1Env` implies its corresponding contract in `rtC0CoreEnv`. -/
theorem rtR1Env_le_rtC0CoreEnv :
    ∀ f as bs xs m Q X, rtR1Env f as bs xs m Q X → rtC0CoreEnv f as bs xs m Q X := by
  refine env_ofTable_sub fun e he xs m Q X hs => ?_
  have hsplit : rtR1SpecEntries = rtC0R1SpecEntries ++
      [ ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocSpec, false⟩
      , ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩ ] := rfl
  rw [hsplit, List.mem_append] at he
  rcases he with hfn | hext
  · exact rtC0CoreEnv_of_mem (by simp [rtC0CoreSpecEntries, hfn]) hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hext
    rcases hext with rfl | rfl
    · exact rtC0CoreEnv_lcnf_alloc (lcnfAllocSpec_to_rem hs)
    · exact rtC0CoreEnv_lcnf_dec_ref_cold hs

/-- Every R2 contract in `rtR2Env` implies its corresponding contract in `rtC0CoreEnv`. -/
theorem rtR2Env_le_rtC0CoreEnv :
    ∀ f as bs xs m Q X, rtR2Env f as bs xs m Q X → rtC0CoreEnv f as bs xs m Q X := by
  refine env_ofTable_sub fun e he xs m Q X hs => ?_
  have hsplit : rtR2SpecEntries = rtC0R2SpecEntries ++
      [ ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocRemSpec, false⟩
      , ⟨"lcnf_free_obj", [i64, i64], [], lcnfFreeObjSpec, false⟩
      , ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩
      , ⟨"lcnf_mark_persistent", [i64, i64], [], lcnfMarkPersistentSpec, false⟩ ] := rfl
  rw [hsplit, List.mem_append] at he
  rcases he with hfn | hext
  · exact rtC0CoreEnv_of_mem (by simp [rtC0CoreSpecEntries, hfn]) hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hext
    rcases hext with rfl | rfl | rfl | rfl
    · exact rtC0CoreEnv_lcnf_alloc hs
    · exact rtC0CoreEnv_lcnf_free_obj hs
    · exact rtC0CoreEnv_lcnf_dec_ref_cold hs
    · exact rtC0CoreEnv_lcnf_mark_persistent hs

/-- R2 rows of `rtC0CoreSpecEntries` (used for R2b's `r2_*` extern rows). -/
private theorem rtC0CoreEnv_of_r2 (i : Nat) (hi : i < rtC0R2SpecEntries.length)
    {xs : Tup Val rtC0R2SpecEntries[i].as} {m : Mem 64} {Q : Post rtC0R2SpecEntries[i].rs}
    {X : XPost} (h : rtC0R2SpecEntries[i].eff xs m Q X) :
    rtC0CoreEnv rtC0R2SpecEntries[i].name rtC0R2SpecEntries[i].as rtC0R2SpecEntries[i].rs
      xs m Q X :=
  rtC0CoreEnv_of_mem (by simp [rtC0CoreSpecEntries, List.getElem_mem]) h

/-- Every R2b contract in `rtR2bEnv` implies its corresponding contract in `rtC0CoreEnv`. -/
theorem rtR2bEnv_le_rtC0CoreEnv :
    ∀ f as bs xs m Q X, rtR2bEnv f as bs xs m Q X → rtC0CoreEnv f as bs xs m Q X := by
  refine env_ofTable_sub fun e he xs m Q X hs => ?_
  have hsplit : rtR2bSpecEntries = rtC0R2bSpecEntries ++
      [ ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocRemSpec, false⟩
      , ⟨"lcnf_free_obj", [i64, i64], [], lcnfFreeObjSpec, false⟩
      , ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩
      , ⟨"lcnf_mark_persistent", [i64, i64], [], lcnfMarkPersistentSpec, false⟩
      , ⟨"r2_inc_obj", [i64], [], r2IncObjSpec, false⟩
      , ⟨"r2_dec_obj", [i64, i64], [], r2DecObjSpec, false⟩
      , ⟨"r2_mem_copy_bytes", [i64, i64, i64], [], r2MemCopyBytesSpec, false⟩
      , ⟨"r2_cmp_byte_slices", [i64, i64, i64, i64], [i64], r2CmpByteSlicesSpec, false⟩
      , ⟨"r2_alloc_sarray", [i64, i64, i64], [i64], r2AllocSarraySpec, false⟩
      , ⟨"r2_alloc_array", [i64, i64, i64], [i64], r2AllocArraySpec, false⟩ ] := rfl
  rw [hsplit, List.mem_append] at he
  rcases he with hfn | hext
  · exact rtC0CoreEnv_of_mem (by simp [rtC0CoreSpecEntries, hfn]) hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hext
    rcases hext with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rtC0CoreEnv_lcnf_alloc hs
    · exact rtC0CoreEnv_lcnf_free_obj hs
    · exact rtC0CoreEnv_lcnf_dec_ref_cold hs
    · exact rtC0CoreEnv_lcnf_mark_persistent hs
    · exact rtC0CoreEnv_of_r2 0 (by decide) hs
    · exact rtC0CoreEnv_of_r2 1 (by decide) hs
    · exact rtC0CoreEnv_of_r2 2 (by decide) hs
    · exact rtC0CoreEnv_of_r2 3 (by decide) hs
    · exact rtC0CoreEnv_of_r2 5 (by decide) hs
    · exact rtC0CoreEnv_of_r2 14 (by decide) hs

private theorem wp_lift_of_moduleOk {Γ Γ' : Env} {M : Module} (hM : ModuleOk Γ M)
    (hΓ : ∀ f as bs xs m P E, Γ f as bs xs m P E → Γ' f as bs xs m P E)
    {fn : Fn} (hfn : fn ∈ M.fns) {xs : Tup Val fn.as} {m : Mem 64}
    {Q : Post fn.rs} {X : XPost} (hwp : Func.wp Γ fn.body xs m Q X) :
    Func.wp Γ' fn.body xs m Q X := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hfn
  obtain ⟨hwf, hcalls, _⟩ := hM.fnsOk pre fn post hsplit
  exact wp_env_agree_of_callsOk
    (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
    hcalls (fun f as bs _ xs' m' P E h => hΓ f as bs xs' m' P E h) m hwp

private theorem tableImpl_take_lift {Γ Γ' : Env} {fs : List Fn} {tbl1 tbl2 : List SpecEntry}
    (hlen : fs.length = tbl1.length)
    (hImpl : TableImpl Γ fs (tbl1 ++ tbl2))
    (hLift : ∀ fn ∈ fs, ∀ xs m Q X,
      Func.wp Γ fn.body xs m Q X → Func.wp Γ' fn.body xs m Q X) :
    TableImpl Γ' fs tbl1 := by
  induction fs generalizing tbl1 with
  | nil => cases tbl1 with | nil => trivial | cons _ _ => simp at hlen
  | cons f fs ih =>
    cases tbl1 with
    | nil => simp at hlen
    | cons e es =>
      simp only [List.cons_append, TableImpl] at hImpl ⊢
      rcases hImpl with ⟨⟨hsig, hwp⟩, hrest⟩
      refine ⟨⟨hsig, fun xs m Q X hs =>
          hLift f List.mem_cons_self xs m Q X (hwp xs m Q X hs)⟩, ?_⟩
      exact ih (by simpa using hlen) hrest fun fn hmem =>
        hLift fn (List.mem_cons_of_mem _ hmem)

private theorem tableImpl_append {Γ : Env} {fs1 fs2 : List Fn} {tbl1 tbl2 : List SpecEntry}
    (hlen : fs1.length = tbl1.length)
    (h1 : TableImpl Γ fs1 tbl1) (h2 : TableImpl Γ fs2 tbl2) :
    TableImpl Γ (fs1 ++ fs2) (tbl1 ++ tbl2) := by
  induction fs1 generalizing tbl1 with
  | nil =>
    cases tbl1 with
    | nil => exact h2
    | cons _ _ => simp at hlen
  | cons f fs ih =>
    cases tbl1 with
    | nil => simp at hlen
    | cons e es =>
      simp only [List.cons_append, TableImpl] at h1 ⊢
      exact ⟨h1.1, ih (by simpa using hlen) h1.2⟩

private theorem rtC0R0_tableImpl : TableImpl rtC0CoreEnv rtR0Mod.fns rtC0R0SpecEntries := by
  dsimp only [rtR0Mod, rtR0_fns, rtC0R0SpecEntries, TableImpl]
  refine ⟨⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_alloc_rem_wp rtC0CoreEnv xs m Q X h⟩,
    ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_free_obj_wp rtC0CoreEnv xs m Q X h⟩,
    ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
      lcnf_dec_ref_cold_wp rtC0CoreEnv (fun _ _ _ _ hs => rtC0CoreEnv_lcnf_free_obj hs)
        xs m Q X h⟩,
    ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_mark_persistent_wp rtC0CoreEnv xs m Q X h⟩,
    ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
      lcnf_clo_under_wp rtC0CoreEnv
        (fun _ _ _ _ hs => rtC0CoreEnv_lcnf_alloc (lcnfAllocSpec_to_rem hs))
        (fun _ _ _ _ hs => rtC0CoreEnv_lcnf_free_obj hs) xs m Q X h⟩,
    trivial⟩

private theorem rtC0R1_tableImpl : TableImpl rtC0CoreEnv rtR1Mod.fns rtC0R1SpecEntries := by
  have hsplit : rtR1SpecEntries = rtC0R1SpecEntries ++
      [ ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocSpec, false⟩
      , ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩ ] := rfl
  refine tableImpl_take_lift (by decide) (hsplit ▸ rtR1Mod_tableImpl) ?_
  intro fn hfn xs m Q X hwp
  exact wp_lift_of_moduleOk rtR1Mod_moduleOk rtR1Env_le_rtC0CoreEnv hfn hwp

private theorem rtC0R2_tableImpl : TableImpl rtC0CoreEnv rtR2Mod.fns rtC0R2SpecEntries := by
  have hsplit : rtR2SpecEntries = rtC0R2SpecEntries ++
      [ ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocRemSpec, false⟩
      , ⟨"lcnf_free_obj", [i64, i64], [], lcnfFreeObjSpec, false⟩
      , ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩
      , ⟨"lcnf_mark_persistent", [i64, i64], [], lcnfMarkPersistentSpec, false⟩ ] := rfl
  refine tableImpl_take_lift (by decide) (hsplit ▸ rtR2Mod_tableImpl) ?_
  intro fn hfn xs m Q X hwp
  exact wp_lift_of_moduleOk rtR2Mod_moduleOk rtR2Env_le_rtC0CoreEnv hfn hwp

private theorem rtC0R2b_tableImpl : TableImpl rtC0CoreEnv rtR2bMod.fns rtC0R2bSpecEntries := by
  have hsplit : rtR2bSpecEntries = rtC0R2bSpecEntries ++
      [ ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocRemSpec, false⟩
      , ⟨"lcnf_free_obj", [i64, i64], [], lcnfFreeObjSpec, false⟩
      , ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩
      , ⟨"lcnf_mark_persistent", [i64, i64], [], lcnfMarkPersistentSpec, false⟩
      , ⟨"r2_inc_obj", [i64], [], r2IncObjSpec, false⟩
      , ⟨"r2_dec_obj", [i64, i64], [], r2DecObjSpec, false⟩
      , ⟨"r2_mem_copy_bytes", [i64, i64, i64], [], r2MemCopyBytesSpec, false⟩
      , ⟨"r2_cmp_byte_slices", [i64, i64, i64, i64], [i64], r2CmpByteSlicesSpec, false⟩
      , ⟨"r2_alloc_sarray", [i64, i64, i64], [i64], r2AllocSarraySpec, false⟩
      , ⟨"r2_alloc_array", [i64, i64, i64], [i64], r2AllocArraySpec, false⟩ ] := rfl
  refine tableImpl_take_lift (by decide) (hsplit ▸ rtR2bMod_tableImpl) ?_
  intro fn hfn xs m Q X hwp
  exact wp_lift_of_moduleOk rtR2bMod_moduleOk rtR2bEnv_le_rtC0CoreEnv hfn hwp

/-- All 80 functions in `rtC0CoreMod` conform row-by-row to `rtC0CoreSpecEntries` under
`rtC0CoreEnv` (internalizing all cross-module R0/R1/R2/R2b calls). -/
theorem rtC0CoreMod_tableImpl : TableImpl rtC0CoreEnv rtC0CoreMod.fns rtC0CoreSpecEntries := by
  have h01 := tableImpl_append (by decide : rtR0Mod.fns.length = rtC0R0SpecEntries.length)
    rtC0R0_tableImpl rtC0R1_tableImpl
  have h012 := tableImpl_append
    (by decide : (rtR0Mod.fns ++ rtR1Mod.fns).length =
      (rtC0R0SpecEntries ++ rtC0R1SpecEntries).length)
    h01 rtC0R2_tableImpl
  exact tableImpl_append
    (by decide : (rtR0Mod.fns ++ rtR1Mod.fns ++ rtR2Mod.fns).length =
      (rtC0R0SpecEntries ++ rtC0R1SpecEntries ++ rtC0R2SpecEntries).length)
    h012 rtC0R2b_tableImpl

/-- Headline unified `ModuleOk`: the closed 80-function pure-C0 runtime (`35/38 Lower.rtCalls`,
`0` externs, `exits = ["lcnf_panic"]`) is acyclic, `Func.Wf`, and verified under `rtC0CoreEnv`. -/
theorem rtC0CoreMod_moduleOk : ModuleOk rtC0CoreEnv rtC0CoreMod :=
  Env.ofTable_moduleOk rtC0CoreMod_checkAcyclic rtC0CoreMod_allFns_wf rtC0CoreMod_tableImpl

/-- Universal lookup-indexed soundness corollary for every one of the 80 functions in `rtC0CoreMod`.
-/
theorem rtC0CoreMod_fn_sound {fn : Fn} (hfn : fn ∈ rtC0CoreMod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hpre : rtC0CoreEnv fn.name fn.as fn.rs xs m Q X) :
    Func.wp rtC0CoreEnv fn.body xs m Q X :=
  Env.ofTable_sound rtC0CoreMod_fns_names_nodup rtC0CoreMod_tableImpl fn hfn xs m Q X hpre

/-! ## 5. Unified `LcnfC0FullInv` & Concrete `Mem 64` Cross-Module Non-Vacuity (`XPost := False`) -/

/-- Concrete `Mem 64` state `nvBnMem` satisfies the unified `LcnfC0FullInv` invariant. -/
theorem nvFullMem_ok :
    (LcnfC0FullInv nvBnRtBase nvBnRtState nvBnScr nvBnScrLimbs ⋆
      lcnfHeap nvBnObjs) nvBnMem :=
  nvBnMem_ok

/-- Cross-module NV 1 (`XPost := False`): R1 `lcnf_nat_slow` (`add` on 2-limb MPZs, internally
calling R0 `lcnf_alloc` via `lcnf_nat_alloc`) inside the unified `rtC0CoreEnv`, preserving
`LcnfC0FullInv`. -/
theorem nv_full_nat_add_carry :
    Func.wp rtC0CoreEnv lcnf_nat_slow.body
      (nvBnRtBase, 1#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem
      (fun r m' =>
        ∃ (st' : RtC0State) (scrLimbs' : List (BitVec 64)) (objs' : List LcnfObj) (obj : LcnfObj),
          (r.1 &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = r.1 ∧
          obj.tag = mpzTag ∧ obj.other = 0 ∧ obj.arrSize = 2 ∧
          obj.limbs = [4#64, 4#64] ∧
          (LcnfC0FullInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  have hfn : lcnf_nat_slow ∈ rtR1Mod.fns := by simp [rtR1Mod, rtR1_fns]
  have hwp := wp_lift_of_moduleOk rtR1Mod_moduleOk rtR1Env_le_rtC0CoreEnv hfn nv_bn_nat_add_carry
  exact hwp

/-- Cross-module NV 2 (`XPost := False`): R2b `lcnf_nat_to_str` (calling `r2b_str_alloc_cap` → R0
`lcnf_alloc`) on a boxed `Nat` (`42`) inside the unified `rtC0CoreEnv`, preserving `LcnfC0FullInv`.
-/
theorem nv_full_nat_to_str_boxed :
    Func.wp rtC0CoreEnv lcnf_nat_to_str.body
      (nvBnRtBase, boxNat 42, ()) nvBnMem
      (fun (s, _) m' =>
        s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
        ∃ (st' : RtC0State),
          (LcnfC0FullInv nvBnRtBase st' nvBnScr nvBnScrLimbs ⋆
            lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2) ⋆
            lcnfHeap nvBnObjs) m')
      (fun _ _ _ _ => False) := by
  have hfn : lcnf_nat_to_str ∈ rtR2bMod.fns := by
    change lcnf_nat_to_str ∈ rtR2b_fns; simp [rtR2b_fns]
  have hwpR2b : Func.wp rtR2bEnv lcnf_nat_to_str.body (nvBnRtBase, boxNat 42, ()) nvBnMem
      (fun (s, _) m' =>
        s ≠ 0#64 ∧ s.toNat % 8 = 0 ∧
        ∃ (st' : RtC0State),
          (LcnfC0FullInv nvBnRtBase st' nvBnScr nvBnScrLimbs ⋆
            lcnfObjMem (mkStrObj s 1#32 3 [52, 50] 2) ⋆
            lcnfHeap nvBnObjs) m')
      (fun _ _ _ _ => False) := by
    apply lcnf_nat_to_str_sound
    let frame : Mem 64 → Prop :=
      (cell64 (nvBnRtBase + 33672#64) nvBnScr ⋆
        cell64 (nvBnRtBase + 33680#64) (BitVec.ofNat 64 nvBnScrLimbs.length) ⋆
        array64 nvBnScr nvBnScrLimbs) ⋆
      lcnfHeap nvBnObjs
    have hm : (rtC0Inv nvBnRtBase nvBnRtState ⋆ lcnfHeap [] ⋆ frame) nvBnMem := by
      have h0 := nvFullMem_ok
      unfold LcnfC0FullInv at h0
      simp only [lcnfHeap]
      rw [sep_emp]
      exact sep_cast_ac h0 (by dsimp only [frame]; ac_rfl)
    refine ⟨nvBnRtState, 42, [], frame,
      by simp [NatInHeap]; decide, (fun _ h => nomatch h), hm, ?_⟩
    rw [ite_eq_left (by decide)]
    have hdec : natToDecimalBytes 42 = [52, 50] := by
      rw [natToDecimalBytes, ite_eq_right (by decide),
        natDigitsRev.eq_def, dite_eq_right (by decide),
        natDigitsRev.eq_def, dite_eq_right (by decide),
        natDigitsRev.eq_def, dite_eq_left (by decide)]
      decide
    rw [hdec]
    refine ⟨Or.inr (by decide), fun s st' m' hs0 hs8 _ _ _ hm' => ?_⟩
    refine ⟨hs0, hs8, st', ?_⟩
    unfold LcnfC0FullInv
    simp only [lcnfHeap, List.length_cons, List.length_nil] at hm'
    rw [sep_emp] at hm'
    exact sep_cast_ac hm' (by dsimp only [frame]; ac_rfl)
  exact wp_lift_of_moduleOk rtR2bMod_moduleOk rtR2bEnv_le_rtC0CoreEnv hfn hwpR2b

/-- Cross-module NV 3 (`XPost := False`): sequential cross-module chain inside `rtC0CoreEnv` on
`nvBnMem` (`LcnfC0FullInv`):
1. `lcnf_str_alloc(rt, 0, 0)` (R2b → `r2b_str_alloc_cap` → R0 `lcnf_alloc`) allocates empty `String`
   `s` with `rc = 1` and exact arena progress (`st'.rem ≥ 216`).
2. `lcnf_array_replicate(rt, boxNat 3, s)` (R2b → R2 `r2_alloc_array` → R0 `lcnf_alloc`) allocates a
   3-element `Array` `[s, s, s]` and increments `s`'s refcount `1 → 3`. -/
theorem nv_full_str_alloc_then_array_replicate :
    Func.wp rtC0CoreEnv lcnf_str_alloc.body (nvBnRtBase, 0#64, 0#64, ()) nvBnMem
      (fun (s, _) m1 =>
        Func.wp rtC0CoreEnv lcnf_array_replicate.body (nvBnRtBase, boxNat 3, s, ()) m1
          (fun (arr, _) m2 =>
            arr ≠ 0#64 ∧ arr.toNat % 8 = 0 ∧
            ∃ (st2 : RtC0State),
              (LcnfC0FullInv nvBnRtBase st2 nvBnScr nvBnScrLimbs ⋆
                lcnfObjMem (mkArrObj arr 1#32 3 [s, s, s]) ⋆
                lcnfObjMem (mkStrObj s 3#32 1 [] 0) ⋆
                lcnfHeap nvBnObjs) m2)
          (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) := by
  have hfnStr : lcnf_str_alloc ∈ rtR2bMod.fns := by
    change lcnf_str_alloc ∈ rtR2b_fns; simp [rtR2b_fns]
  have hfnRep : lcnf_array_replicate ∈ rtR2bMod.fns := by
    change lcnf_array_replicate ∈ rtR2b_fns; simp [rtR2b_fns]
  let scrFrame : Mem 64 → Prop :=
    cell64 (nvBnRtBase + 33672#64) nvBnScr ⋆
    cell64 (nvBnRtBase + 33680#64) (BitVec.ofNat 64 nvBnScrLimbs.length) ⋆
    array64 nvBnScr nvBnScrLimbs
  let fullFrame : Mem 64 → Prop := scrFrame ⋆ lcnfHeap nvBnObjs
  have hm0 : (rtC0Inv nvBnRtBase nvBnRtState ⋆ fullFrame) nvBnMem := by
    have h0 := nvFullMem_ok
    unfold LcnfC0FullInv at h0
    exact sep_cast_ac h0 (by dsimp only [fullFrame, scrFrame]; ac_rfl)
  refine wp_lift_of_moduleOk rtR2bMod_moduleOk rtR2bEnv_le_rtC0CoreEnv hfnStr ?_
  apply lcnf_str_alloc_sound
  dsimp only [lcnfStrAllocSpec]
  rw [ite_eq_right (by decide)]
  refine ⟨nvBnRtState, fullFrame, Or.inr (by decide), hm0,
    fun s st1 m1 hs0 hs8 _ _ hremLo hm1 => ?_⟩
  have hrem1 : 48 ≤ st1.rem := by
    have hinit : nvBnRtState.rem = 256 := by decide
    have hreq : strAllocBytes ((0#64 : BitVec 64).toNat + 1) = 40 := by decide
    rw [hinit, hreq] at hremLo
    omega
  have hsObjMem :
      (rtC0Inv nvBnRtBase st1 ⋆ lcnfObjMem (mkStrObj s 1#32 1 [] 0) ⋆ fullFrame) m1 := by
    have hobj : lcnfObjMem (mkStrObj s 1#32 1 [] 0) =
        cell64 s strHeaderWord ⋆ cell64 (s + 8#64) 1#64 ⋆ cell64 (s + 16#64) 1#64 ⋆
        cell64 (s + 24#64) 0#64 ⋆ bytes (s + 32#64) [0] ⋆ region (s + 33#64) 7 := by
      dsimp only [lcnfObjMem, mkStrObj, LcnfObj.totalBytes, LcnfObj.header, strHeaderWord,
        closureTag, arrayTag, sarrayTag, stringTag, mpzTag, align8]
      rfl
    have hparts : (rtC0Inv nvBnRtBase st1 ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) 1#64 ⋆
        cell64 (s + 16#64) 1#64 ⋆ cell64 (s + 24#64) 0#64 ⋆ bytes (s + 32#64) [0] ⋆
        region (s + 33#64) 7 ⋆ fullFrame) m1 := by
      have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
      have hsub : strAllocBytes 1 - 33 = 7 := by decide
      have ha0 : s + 32#64 + 0#64 = s + 32#64 := by bv_omega
      have ha1 : s + 32#64 + 1#64 = s + 33#64 := by bv_omega
      simp only [h0, region_zero, sep_emp, ha0, ha1, hsub,
        show (0#64 : BitVec 64) + 1#64 = 1#64 from rfl] at hm1
      exact sep_cast_ac hm1 (by ac_rfl)
    rw [hobj]
    exact sep_cast_ac hparts (by ac_rfl)
  refine wp_lift_of_moduleOk rtR2bMod_moduleOk rtR2bEnv_le_rtC0CoreEnv hfnRep ?_
  apply lcnf_array_replicate_sound
  dsimp only [lcnfArrayReplicateSpec]
  rw [ite_eq_right (by decide)]
  let sObj := mkStrObj s 1#32 1 [] 0
  have hsCanon : StrCanon sObj :=
    mkStrObj_canon hs0 hs8 (by decide) (by decide) (by decide) (by decide)
  have hsWf : sObj.Wf := hsCanon.wf
  have hsEven : (s &&& 1#64) = 0#64 := bv64_and1_eq_zero_of_mod8 hs8
  have hm1' : (rtC0Inv nvBnRtBase st1 ⋆ lcnfHeap [sObj] ⋆ fullFrame) m1 := by
    simpa [lcnfHeap, sep_emp] using hsObjMem
  refine ⟨st1, [sObj], fullFrame, Or.inr (by simpa [arrAllocBytes, boxNat] using hrem1),
    (fun o ho => by simp only [List.mem_singleton] at ho; subst ho; exact hsWf),
    (fun h => by simp [boxNat] at h),
    (fun _ => ⟨sObj, List.mem_singleton_self _, rfl, fun h => by
      simp [sObj, mkStrObj, boxNat] at h⟩),
    hm1', fun arr st2 objs2 m2 ha0 ha8 _ _ _ _ _ hgt hm2 => ?_⟩
  have hcnt : (boxNat 3 >>> 1).toNat = 3 := by decide
  have hgt' := hgt (by rw [hcnt]; decide)
  rw [ite_eq_right (by intro h; rcases h with rfl | hodd; exact hs0 rfl; exact hodd hsEven)] at hgt'
  rcases hgt' with ⟨o, ho, haddr, hrc⟩
  simp only [List.mem_singleton] at ho
  subst ho
  rw [ite_eq_left (Or.inr (by rw [hcnt]; dsimp only [sObj, mkStrObj]; decide))] at hrc
  rw [hrc, hcnt] at hm2
  have hadd : addRcObjList s 2 [sObj] = [mkStrObj s 3#32 1 [] 0] := by
    simp only [addRcObjList, List.map_cons, List.map_nil, sObj, mkStrObj, LcnfObj.withRc]
    have hcond : True ∧ (1#32 : BitVec 32) ≠ 0#32 := ⟨trivial, by decide⟩
    rw [ite_eq_left hcond]
    rfl
  rw [hadd] at hm2
  simp only [lcnfHeap, sep_emp] at hm2
  refine ⟨ha0, ha8, st2, ?_⟩
  unfold LcnfC0FullInv
  exact sep_cast_ac hm2 (by dsimp only [fullFrame, scrFrame]; ac_rfl)

/-- Cross-module NV 4 (`XPost := False`): R2 `lcnf_ba_empty` (calling R0 `lcnf_alloc` + R0
`lcnf_mark_persistent`) inside `rtC0CoreEnv`, preserving `LcnfC0FullInv`. -/
theorem nv_full_ba_empty :
    Func.wp rtC0CoreEnv lcnf_ba_empty.body (nvBnRtBase, ()) nvBnMem
      (fun (p, _) m' =>
        p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧
        ∃ st' : RtC0State, st'.hdr.s_ba_empty = p ∧
          (LcnfC0FullInv nvBnRtBase st' nvBnScr nvBnScrLimbs ⋆
            lcnfObjMem (mkBaObj p 0#32 0 []) ⋆
            lcnfHeap nvBnObjs) m')
      (fun _ _ _ _ => False) := by
  have hfn : lcnf_ba_empty ∈ rtR2Mod.fns := by simp [rtR2Mod, rtR2_fns]
  refine wp_lift_of_moduleOk rtR2Mod_moduleOk rtR2Env_le_rtC0CoreEnv hfn ?_
  apply lcnf_ba_empty_sound
  let frame : Mem 64 → Prop :=
    (cell64 (nvBnRtBase + 33672#64) nvBnScr ⋆
      cell64 (nvBnRtBase + 33680#64) (BitVec.ofNat 64 nvBnScrLimbs.length) ⋆
      array64 nvBnScr nvBnScrLimbs) ⋆
    lcnfHeap nvBnObjs
  have hm : (rtC0Inv nvBnRtBase nvBnRtState ⋆ frame) nvBnMem := by
    have h0 := nvFullMem_ok
    unfold LcnfC0FullInv at h0
    exact sep_cast_ac h0 (by dsimp only [frame]; ac_rfl)
  refine ⟨nvBnRtState, frame, hm, ?_⟩
  rw [ite_eq_right (by decide)]
  refine ⟨by decide, Or.inr (by decide), fun p st' m' hp0 hp8 _ _ hba hm' => ?_⟩
  refine ⟨hp0, hp8, st', hba, ?_⟩
  unfold LcnfC0FullInv
  exact sep_cast_ac hm' (by dsimp only [frame]; ac_rfl)

/-- Cross-module NV 5 (`XPost := False`): R0 `lcnf_dec_ref_cold` (cascading DFS free calling R0
`lcnf_free_obj`) inside the unified `rtC0CoreEnv` on the concrete 5-node DAG `nvDagMem`. -/
theorem nv_full_dec_ref_cold :
    Func.wp rtC0CoreEnv lcnf_dec_ref_cold.body (nvRtBase, nvAddrA, ()) nvDagMem
      (fun () m' =>
        ∃ st' objs', st'.PreservesMeta nvRtState ∧ st'.rem = nvRtState.rem ∧
          DecColdRel nvAddrA nvDagObjs objs' ∧ (rtC0Inv nvRtBase st' ⋆ lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  have hfn : lcnf_dec_ref_cold ∈ rtC0CoreMod.fns := by
    simp [rtC0CoreMod, rtC0CoreFns, rtR0Mod, rtR0_fns]
  have hA_ch : nvObjA.childFields = [nvAddrB, nvAddrC] := by decide
  have hB_ch : nvObjB.childFields = [nvAddrC] := by decide
  have hC_ch : nvObjC.childFields = [7#64, nvAddrP] := by decide
  have hP_ch : nvObjP.childFields = [11#64] := by decide
  have hU_ch : nvObjU.childFields = [13#64] := by decide
  refine rtC0CoreMod_fn_sound hfn (rtC0CoreEnv_lcnf_dec_ref_cold ?_)
  refine ⟨by decide, nvRtState, nvDagObjs, emp, by decide, by rw [sep_emp]; exact nvDagMem_ok,
    ⟨nvObjA, by simp [nvDagObjs], rfl, rfl⟩, ?_, ?_, ?_,
    fun st' objs' m' hpr hrem hrel hm' => ⟨st', objs', hpr, hrem, hrel, by rwa [sep_emp] at hm'⟩⟩
  · intro o ho
    simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;>
      unfold LcnfObj.Wf LcnfObj.totalBytes <;> decide
  · intro o ho f hf h0
    simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · rw [hA_ch] at hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact ⟨nvObjB, by simp [nvDagObjs], rfl⟩
      · exact ⟨nvObjC, by simp [nvDagObjs], rfl⟩
    · rw [hB_ch] at hf; simp only [List.mem_singleton] at hf; subst hf
      exact ⟨nvObjC, by simp [nvDagObjs], rfl⟩
    · rw [hC_ch] at hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact absurd h0 (by decide)
      · exact ⟨nvObjP, by simp [nvDagObjs], rfl⟩
    · rw [hP_ch] at hf; simp only [List.mem_singleton] at hf; subst hf
      exact absurd h0 (by decide)
    · rw [hU_ch] at hf; simp only [List.mem_singleton] at hf; subst hf
      exact absurd h0 (by decide)
  · refine ⟨?_, ?_⟩
    · intro p hp hrc f hf h0
      simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact absurd hrc (by decide)
      · exact absurd hrc (by decide)
      · exact absurd hrc (by decide)
      · rw [hP_ch] at hf; simp only [List.mem_singleton] at hf; subst hf
        exact absurd h0 (by decide)
      · exact absurd hrc (by decide)
    · intro y hy hpos
      simp only [nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · unfold nonPersistRefs LcnfObj.childFields; decide
      · unfold nonPersistRefs LcnfObj.childFields; decide
      · unfold nonPersistRefs LcnfObj.childFields; decide
      · exact absurd hpos (by decide)
      · unfold nonPersistRefs LcnfObj.childFields; decide

end

end LeanQbe.T.LeanLCNF
