module

public import LeanQbe.T.Examples.Kissat.FullFastCoreBcpLemmas
public import LeanQbe.T.Examples.Kissat.FullProof
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat Stage-5 Fast-Core `ModuleOk`, `Full.fullModule` Splice, & UNSAT Non-Vacuity

Proves:
1. Closed standalone `fastCore_tableImpl` and `fastCore_moduleOk : ModuleOk fastCoreEnv
   fastCoreModule` (`3` optimized BCP functions + extern `full_watch_push` against canonical
   `FullSpec2` contracts).
2. Splice of `[47, 48, 49]` (`full_prop_lit`, `full_propagate_ignore`, `full_propagate`) into
   `Full.fullFns` (`fastCoreFullFns`, `fastCoreFullModule`), preserving `fastCoreFull_fns_wf`,
   `fastCoreFull_acyclic`, and `fastCore_fullEnv_moduleOk_of_missing`.
3. Concrete `Mem 64` binary-watch UNSAT soundness/non-vacuity (`nv_fast_propagate_sound`,
   `XPost := fun _ _ _ _ => False`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FastCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_prop_lit_body full_prop_lit_wf full_prop_lit_wp
  full_propagate_ignore_body full_propagate_ignore_wf full_propagate_ignore_wp
  full_propagate_body full_propagate_wf full_propagate_wp
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. Closed `fastCoreModule` `ModuleOk` (`3` fns + extern `full_watch_push`) -/

/-- Canonical `FullSpec2` specification table for `fastCoreModule` plus extern
`full_watch_push`. -/
def fastCoreSpecTable : List SpecEntry :=
  [ ⟨"full_prop_lit", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  ]

/-- Specification environment induced by `fastCoreSpecTable`. -/
def fastCoreEnv : Env := Env.ofTable fastCoreSpecTable

theorem fastCoreSpecTable_noExit : ∀ e ∈ fastCoreSpecTable, e.noExit = true := by
  intro e he
  simp only [fastCoreSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> rfl

theorem fastCore_noExit :
    ∀ f as bs xs m Q X X',
      fastCoreEnv f as bs xs m Q X → fastCoreEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fastCoreSpecTable_noExit

private theorem fastCoreSpecTable_nodup :
    (fastCoreSpecTable.map SpecEntry.name).Nodup := by
  show (["full_prop_lit", "full_propagate_ignore", "full_propagate",
    "full_watch_push"] : List String).Nodup
  decide

private theorem fastCoreEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : fastCoreSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → fastCoreEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) fastCoreSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `fastCore_fns` against `fastCoreSpecTable`. -/
theorem fastCore_tableImpl :
    TableImpl fastCoreEnv fastCore_fns fastCoreSpecTable := by
  let hPush := fastCoreEnv_row_at 3
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hPropLit := fastCoreEnv_row_at 0
    ⟨"full_prop_lit", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  let hPropIgn := fastCoreEnv_row_at 1
    ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  exact ⟨.of (full_prop_lit_wp fastCoreEnv hPush),
    ⟨.of (full_propagate_ignore_wp fastCoreEnv hPropLit),
    ⟨.of (full_propagate_wp fastCoreEnv hPropIgn), trivial⟩⟩⟩

/-- Closed `ModuleOk` for standalone `fastCoreModule` under canonical `fastCoreEnv`. -/
theorem fastCore_moduleOk : ModuleOk fastCoreEnv fastCoreModule :=
  Env.ofTable_moduleOk fastCore_acyclic
    ⟨full_prop_lit_wf, full_propagate_ignore_wf, full_propagate_wf, trivial⟩
    fastCore_tableImpl

/-! ## 2. Spliced `[47, 48, 49]` `Full.fullModule` integration (`151/166` closed) -/

/-- `Full.fullFns` with indices `[47, 48, 49]` (`full_prop_lit`, `full_propagate_ignore`,
`full_propagate`) replaced by `fastCore_fns`. -/
def fastCoreFullFns : List Fn :=
  Full.fullFns.take 47 ++ fastCore_fns ++ Full.fullFns.drop 50

/-- `Full.fullModule` with its 3-function BCP core spliced from `fastCore_fns`. -/
def fastCoreFullModule : LeanQbe.T.Module :=
  { Full.fullModule with fns := fastCoreFullFns }

theorem fastCoreFull_fns_wf : ∀ f ∈ fastCoreFullFns, f.Wf := by
  intro f hf
  simp only [fastCoreFullFns, List.mem_append] at hf
  rcases hf with (h | h) | h
  · exact Full.fullFns_wf f (List.take_subset _ _ h)
  · exact fastCore_fns_wf f h
  · exact Full.fullFns_wf f (List.drop_subset _ _ h)

theorem fastCoreFull_acyclic : fastCoreFullModule.checkAcyclic = true := by
  t_kernel_rfl

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

private theorem fullFns_nodup : (Full.fullFns.map Fn.name).Nodup := by
  have hchk := Full.full_acyclic
  simp only [Full.fullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem fullSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((Full.fullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (Full.fullSpecTable mainSpec).map SpecEntry.name = Full.fullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (Full.fullSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]; exact fullFns_nodup

private theorem mkFullEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (Full.fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → Full.mkFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h => Env.ofTable_of_mem (List.mem_of_getElem? hi)
    (fullSpecTable_nodup mainSpec) (hno xs m Q X h)

private theorem tableImpl_take {Γ : Env} :
    ∀ (n : Nat) {fs : List Fn} {tbl : List SpecEntry},
      TableImpl Γ fs tbl → TableImpl Γ (fs.take n) (tbl.take n)
  | 0, _, _, _ => trivial
  | _ + 1, [], _, _ => trivial
  | _ + 1, _ :: _, [], h => h.elim
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, tableImpl_take n h.2⟩

private theorem tableImpl_drop {Γ : Env} :
    ∀ (n : Nat) {fs : List Fn} {tbl : List SpecEntry},
      TableImpl Γ fs tbl → TableImpl Γ (fs.drop n) (tbl.drop n)
  | 0, _, _, h => h
  | _ + 1, [], _, _ => trivial
  | _ + 1, _ :: _, [], h => h.elim
  | n + 1, _ :: _, _ :: _, h => tableImpl_drop n h.2

private theorem tableImpl_append {Γ : Env} :
    ∀ {fs₁ : List Fn} {tbl₁ : List SpecEntry} {fs₂ : List Fn} {tbl₂ : List SpecEntry},
      fs₁.length = tbl₁.length →
      TableImpl Γ fs₁ tbl₁ → TableImpl Γ fs₂ tbl₂ →
      TableImpl Γ (fs₁ ++ fs₂) (tbl₁ ++ tbl₂)
  | [], [], _, _, _, _, h2 => h2
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _ :: _, _, _, hlen, h1, h2 =>
    ⟨h1.1, tableImpl_append (Nat.succ.inj hlen) h1.2 h2⟩

/-- Row-by-row `TableImpl` for spliced `fastCoreFullFns` against `Full.fullSpecTable`,
preserving all `151 / 166` closed bridges and exact `8a` / `8b` remaining obligations. -/
theorem fastCore_fullEnv_tableImpl_of_missing
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → Full.fullSolveBytesCoreSpec a m Q X)
    (h8a : ∀ n ∈ Full.fullRemaining8aIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧ (Full.fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (Full.mkFullEnv mainSpec) fn row)
    (h8b : ∀ n ∈ Full.fullRemaining8bIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧ (Full.fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (Full.mkFullEnv mainSpec) fn row) :
    TableImpl (Full.mkFullEnv mainSpec) fastCoreFullFns (Full.fullSpecTable mainSpec) := by
  let Γ := Full.mkFullEnv mainSpec
  have hfull := Full.mkFullEnv_tableImpl_of_missing mainSpec hweaken h8a h8b
  have htake := tableImpl_take 47 hfull
  have hdrop := tableImpl_drop 50 hfull
  have hmid_eq : ((Full.fullSpecTable mainSpec).drop 47).take 3 =
      [ ⟨"full_prop_lit", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
      , ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
      , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ] := rfl
  have htbl_eq : Full.fullSpecTable mainSpec =
      (Full.fullSpecTable mainSpec).take 47 ++
      ([ ⟨"full_prop_lit", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
       , ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
       , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ] ++
       (Full.fullSpecTable mainSpec).drop 50) := by
    have h1 := List.take_append_drop 47 (Full.fullSpecTable mainSpec)
    have h2 := List.take_append_drop 3 ((Full.fullSpecTable mainSpec).drop 47)
    rw [List.drop_drop, show 47 + 3 = 50 from rfl, hmid_eq] at h2
    rw [← h2] at h1
    exact h1.symm
  have hlen47 : (Full.fullFns.take 47).length =
      ((Full.fullSpecTable mainSpec).take 47).length := by
    have hs := congrArg List.length (Full.fullSpecTable_sigs mainSpec)
    simp only [List.length_map] at hs
    simp only [List.length_take, ← hs]
  have h15 := mkFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  have h47 := mkFullEnv_row_at (mainSpec := mainSpec) 47
    ⟨"full_prop_lit", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  have h48 := mkFullEnv_row_at (mainSpec := mainSpec) 48
    ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  have hmid : TableImpl Γ fastCore_fns
      [ ⟨"full_prop_lit", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
      , ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
      , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ] :=
    ⟨.of (full_prop_lit_wp Γ h15),
      ⟨.of (full_propagate_ignore_wp Γ h47),
      ⟨.of (full_propagate_wp Γ h48), trivial⟩⟩⟩
  rw [htbl_eq]
  change TableImpl Γ (Full.fullFns.take 47 ++ (fastCore_fns ++ Full.fullFns.drop 50)) _
  exact tableImpl_append hlen47 htake (tableImpl_append rfl hmid hdrop)

/-- Turn-key `ModuleOk` assembly for spliced `fastCoreFullModule` (`151/166` closed). -/
theorem fastCore_fullEnv_moduleOk_of_missing
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → Full.fullSolveBytesCoreSpec a m Q X)
    (h8a : ∀ n ∈ Full.fullRemaining8aIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧ (Full.fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (Full.mkFullEnv mainSpec) fn row)
    (h8b : ∀ n ∈ Full.fullRemaining8bIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧ (Full.fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (Full.mkFullEnv mainSpec) fn row) :
    ModuleOk (Full.mkFullEnv mainSpec) fastCoreFullModule :=
  Env.ofTable_moduleOk fastCoreFull_acyclic (allFns_of_forall fastCoreFull_fns_wf)
    (fastCore_fullEnv_tableImpl_of_missing mainSpec hweaken h8a h8b)

/-- Specialization of `fastCore_fullEnv_moduleOk_of_missing` at `Full.fullEnv`. -/
theorem fastCore_fullEnv_modOk_rem
    (h8a : ∀ n ∈ Full.fullRemaining8aIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧
        (Full.fullSpecTable Full.fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl Full.fullEnv fn row)
    (h8b : ∀ n ∈ Full.fullRemaining8bIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧
        (Full.fullSpecTable Full.fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl Full.fullEnv fn row) :
    ModuleOk Full.fullEnv fastCoreFullModule :=
  fastCore_fullEnv_moduleOk_of_missing Full.fullSolveBytesSpec
    (fun _ _ _ _ => Full.fullSolveBytesCoreSpec_of_spec) h8a h8b

/-! ## 3. Concrete `Mem 64` binary-watch UNSAT non-vacuity (`XPost := False`) -/

/-- Concrete `FullCfg` (`max_vars = 1`, `wcap = 2`, `avail = 1760`, `slack = 0`). -/
def nvFastPropCfg : FullCfg where
  hdr := 0x1000#64
  avail := 1760
  mv := 1
  max_vars := 1
  bva_cap := 0
  nc := 2
  arena_cap := 0
  wcap := 2
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

/-- Concrete `FullState` with `x0` assigned true at level 0 (`propagated = 0`, `trail_end = 1`,
`fuel = 1`) and a binary watch `(1, 1)` = `(¬x0 ∨ ¬x0)` at `wstk[1]` for literal `1`. -/
def nvFastPropState : FullState where
  core :=
    { Full.nvOneLitState.core with
      wlen := 2
      fuel := 1#64
      confl_type := 0#64
      confl_lit0 := 0#64
      confl_lit1 := 0#64
      wvec := [0#32, 0#32, 1#32, 1#32]
      wstk := [0#32, 0x80000001#32] }
  scratch := Full.nvOneLitScratch

def nvFastBlockHdr : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvFastPropCfg nvFastPropState)

def nvFastBlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvFastPropState.core.vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvFastPropState.scratch.walk_vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvFastPropState.core.lit_mark ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvFastPropState.core.mrk ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvFastPropState.scratch.phases ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvFastPropState.scratch.phases_target ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvFastPropState.scratch.phases_best ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvFastPropState.scratch.walk_best ++ List.replicate 7 0)

def nvFastBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvFastPropState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.core.trail_pos ++ List.replicate 4 0)

def nvFastBlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvFastPropState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.scratch.shrink_stk ++ List.replicate 4 0)

def nvFastBlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvFastPropState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvFastPropState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvFastPropState.core.frame_dec ++ List.replicate 0 0)

def nvFastBlockWvec : List UInt8 :=
  bytesOf (t := i32) nvFastPropState.core.wvec ++
  bytesOf (t := i32) nvFastPropState.core.repr ++
  bytesOf (t := i32) nvFastPropState.scratch.wsort ++
  bytesOf (t := i32) nvFastPropState.scratch.work_stk1 ++
  bytesOf (t := i32) nvFastPropState.scratch.work_stk2 ++
  bytesOf (t := i32) nvFastPropState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvFastPropState.scratch.tarjan_reach ++
  bytes64 nvFastPropState.scratch.score ++
  bytes64 nvFastPropState.scratch.sim_sig

def nvFastBlockTail : List UInt8 :=
  bytesOf (t := i32) nvFastPropState.core.min_stk ++
  bytesOf (t := i32) nvFastPropState.scratch.glue_used ++
  bytesOf (t := i32) nvFastPropState.scratch.last_learned ++
  bytesOf (t := i32) nvFastPropState.core.arena ++
  bytesOf (t := i32) nvFastPropState.core.wstk ++
  bytesOf (t := i32) nvFastPropState.scratch.delayed ++
  bytesOf (t := i32) nvFastPropState.scratch.red_refs ++
  bytesOf (t := i32) nvFastPropState.scratch.extend_stk ++
  bytesOf (t := i32) nvFastPropState.scratch.scratch_buf ++
  List.replicate 0 0

/-- Concrete `1760`-byte arena image encoding `nvFastPropCfg` and `nvFastPropState`. -/
def nvFastPropBytes : List UInt8 :=
  nvFastBlockHdr ++ nvFastBlockBytes ++ nvFastBlockU32A ++ nvFastBlockU32B ++
  nvFastBlockU32C ++ nvFastBlockWvec ++ nvFastBlockTail

/-- Concrete `Mem 64` heap mapped at `nvFastPropCfg.hdr` (`0x1000`). -/
def nvFastPropMem : Mem 64 := nvFastPropBytes.At nvFastPropCfg.hdr

theorem nvFastPropMem_ok : FullMem nvFastPropCfg nvFastPropState nvFastPropMem := by
  let c := nvFastPropCfg; let s := nvFastPropState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : Full.u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvFastBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvFastBlockHdr.At c.hdr) :=
    Full.nv_join_pair
      (Full.nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (Full.nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvFastBlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvFastBlockBytes.At c.pVals) := by
    have h1 := Full.nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesTarget)
      (xs := s.scratch.phases_target) 1 7 rfl (by decide)
    have h7 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesBest)
      (xs := s.scratch.phases_best) 1 7 rfl (by decide)
    have h8 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkBest)
      (xs := s.scratch.walk_best) 1 7 rfl (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_sep_reorg (Full.nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => Full.nv_zip4 hm
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg hall fun _ hm => by
      have hfin := Full.nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvFastBlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvFastBlockU32A.At c.pFlags) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvFastBlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvFastBlockU32B.At c.pTmp) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl
      (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk)
      4 4 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvFastBlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvFastBlockU32C.At c.pQPrev) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail)
      8 0 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec)
      8 0 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvFastBlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvFastBlockWvec.At c.pWvec) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 8 rfl
      (by decide)
    have h8 := Full.nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := Full.nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvFastBlockTail.length = 344 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvFastBlockTail.At c.pMinStk) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned)
      64 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 8 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl
      (by decide)
    have h8 := Full.nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := Full.nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := Full.nv_join_pair h12345678 h9 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h123456789 h10 (by decide) (by decide))
      fun _ hm => by unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := Full.nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := Full.nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := Full.nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := Full.nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := Full.nv_join_pair h04 hWvec (by decide) (by decide)
  exact (Full.nv_sep_reorg (Full.nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

theorem nvFastProp_lengths : nvFastPropState.LengthsOk nvFastPropCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, by decide, by decide, Nat.le_refl _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvFastProp_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvFastProp_entails_11 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨lit, hm, heq⟩ := h1
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

theorem nvFastProp_witness :
    FullWitnessInv nvFastPropCfg Full.nvOneLitF0 [[0], [1]] nvFastPropState.core := by
  have hrefs : fullArenaClauseRefsCore nvFastPropState.core = [] := rfl
  have hcv : nvFastPropState.core.cur_vars = 1 := rfl
  have hte : nvFastPropState.core.trail_end = 1 := rfl
  have hcl : nvFastPropState.core.cur_level = 0 := rfl
  have hdm : nvFastPropState.core.dense_mode = 0#64 := rfl
  have hwat : Full.ModeWatchesInv [[0], [1]] nvFastPropState.core := by
    unfold Full.ModeWatchesInv; rw [ite_eq_left hdm]
    refine Full.WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 l2 h1 h2 hne hp1 hp2 => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · simp [Full.fullWatchSizeCore, nvFastPropState] at hp
      · decide
    · rw [hcv] at h1 h2
      rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        rcases (by omega : l2 = 0 ∨ l2 = 1) with rfl | rfl
      · exact absurd rfl hne
      · simp [Full.fullWatchSizeCore, nvFastPropState] at hp1
      · simp [Full.fullWatchSizeCore, nvFastPropState] at hp2
      · exact absurd rfl hne
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact Full.WatchSliceOk.empty
      · show Full.WatchSliceOk [[0], [1]] nvFastPropState.core 1 1 1
        exact .bin rfl (by decide) (by decide) (by decide) nvFastProp_entails_11 .empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [nvFastPropState, Full.nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.zero_le _
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun L h1 h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nvFastProp_entails_0
      trail_pos_inv := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

private theorem conflictOkW_to_confl {F_cur : List (List Nat)} {s : FullState}
    (h : Full.FullConflictOkW F_cur s) : FullPropDecSpecs.FullConflOkW F_cur s.core := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | hr
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr hr

/-- Concrete `Mem 64` binary-watch UNSAT soundness for `full_propagate_body` under canonical
`fastCoreEnv` (`XPost := False`): verifies partial correctness on `nvFastPropMem` and derives
`nvOneLitF0.Unsat` on conflict return (`r = 1#64`). -/
theorem nv_fast_propagate_sound :
    Func.wp fastCoreEnv full_propagate_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let hPropIgn := fastCoreEnv_row_at 1
    ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  apply full_propagate_wp fastCoreEnv hPropIgn
  refine ⟨nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], nvFastPropState, emp,
    rfl, nvFastProp_lengths, nvFastProp_witness, rfl,
    by rw [sep_emp]; exact nvFastPropMem_ok, ?_⟩
  intro r _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _prop' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _fuel' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' m' s' _hlen' hwf' _htr' _hperm' _hfl' hr _hr0 hr1 _hr2 _hnoop hm'
  refine ⟨hr, fun h1 => ?_, _, hm'⟩
  subst h1
  exact hwf'.level0_unsat_of_conflOkW rfl (conflictOkW_to_confl (hr1 rfl).2.2)

end LeanQbe.T.Examples.Kissat.FastCore
