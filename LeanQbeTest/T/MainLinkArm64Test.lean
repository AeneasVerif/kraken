module

public import LeanQbe.T.MainLink
public import LeanQbe.T.MainLinkSplice
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainSplice
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbeTest.T.MainLinkFixtures
import LeanQbe.T.FlatLemmas
public meta import Lean
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbeTest.T.MainLinkFixtures

/-!
# Compositional Multi-Chunk Linking Test on AAPCS64 Arm64 (`MainLink` + `MainLinkSplice`)

Tests literal-backed `LeanQbe.T.MainLink` end-to-end on `armTarget` (`armLegalTarget`,
`armLayout`, `armInit`):
1. Separately compiles `chunk1` (`bump`), `chunk2` (`doubleBump` calling `bump`), and `chunk3`
   (`top` calling `doubleBump`) via `splice_chunk_literals` + `t_kernel_rfl` (`compileCheckedLit`),
   plus a parallel-compiled `chunk2Par` taking a literal `ext` without referencing `chunk1Compiled`.
2. Links `chunk1` + `chunk2` via O(N) metadata-only `checkLink` (`t_kernel_rfl`), tests
   `checkLinkWithLabels` / `linkCompiledWithLabels` and `checkLinkListWithLabels` /
   `linkCompiledListWithLabels`, and links `[chunk1, chunk2Par, chunk3]` via `checkLinkList`.
3. Derives closed `armInit.run_ret1_sep` execution theorems over the linked hosts
   (`doubleBump(0x1000, 5) = 36`, `top(0x1000, 5) = 37`, updating `cell64 0x1000 21`).
4. Negative metadata checks: duplicate names, `.L` symbol names, and mismatched callee bounds.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainLinkArm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbeTest.T.MainLinkFixtures

export LeanQbeTest.T.MainLinkFixtures (
  fnBump fnDoubleBump fnTop
  chunk1Fns chunk2Fns chunk3Fns
  twoChunkMod threeChunkMod
  twoChunkMod_acyclic threeChunkMod_acyclic
  fnBump_wf fnDoubleBump_wf fnTop_wf
  twoChunkMod_wf threeChunkMod_wf
  bumpSpec doubleBumpSpec topSpec linkΓ
  twoChunkMod_wp threeChunkMod_wp
  initMemBytes initMemBytes_len initMemBytes_cell
)

/-! ## 1. Target Support Theorems -/

private theorem all_supports_arm :
    [fnBump, fnDoubleBump, fnTop].all (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) =
      true := by
  t_kernel_rfl

theorem twoChunkMod_supp :
    ∀ f ∈ twoChunkMod.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true := by
  have hall := supportsAll_to_forall all_supports_arm
  intro f hf
  simp only [twoChunkMod, chunk1Fns, chunk2Fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> exact hall _ (by simp)

theorem threeChunkMod_supp :
    ∀ f ∈ threeChunkMod.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true := by
  have hall := supportsAll_to_forall all_supports_arm
  intro f hf
  simp only [threeChunkMod, chunk1Fns, chunk2Fns, chunk3Fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> exact hall _ (by simp)

/-! ## 2. Literal-backed per-chunk compilation (`splice_chunk_literals` + `compileCheckedLit`) -/

splice_module_hints chunk1Hints armTarget.toIsa armLegalTarget chunk1Fns
splice_module_hints chunk2Hints armTarget.toIsa armLegalTarget chunk2Fns
splice_module_hints chunk3Hints armTarget.toIsa armLegalTarget chunk3Fns

splice_chunk_literals chunk1Code chunk1Bounds chunk1Sigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0 chunk1Fns chunk1Hints

theorem chunk1_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      [] [] 0 chunk1Fns chunk1Hints = .ok (chunk1Code, chunk1Bounds) := by
  t_kernel_rfl

theorem chunk1_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      chunk1Code chunk1Bounds (chunk1Fns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def chunk1Compiled : Compiled armTarget armLegalTarget [] [] 0 chunk1Fns chunk1Hints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 chunk1Fns chunk1Hints 2048 chunk1Code chunk1Bounds chunk1_cm chunk1_meta

splice_chunk_literals chunk2Code chunk2Bounds chunk2Sigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  (chunk1Sigs ++ []) [] 0 chunk2Fns chunk2Hints

theorem chunk2_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      (chunk1Compiled.sigBounds ++ []) [] 0 chunk2Fns chunk2Hints =
      .ok (chunk2Code, chunk2Bounds) := by
  t_kernel_rfl

theorem chunk2_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      chunk2Code chunk2Bounds (chunk2Fns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def chunk2Compiled :
    Compiled armTarget armLegalTarget (chunk1Compiled.sigBounds ++ []) [] 0
      chunk2Fns chunk2Hints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    (chunk1Compiled.sigBounds ++ []) [] 0 chunk2Fns chunk2Hints 2048
    chunk2Code chunk2Bounds chunk2_cm chunk2_meta

/-- Parallel chunk 2 compiled against a standalone literal `ext` (independent of `chunk1`). -/
def parBumpExt : List (SigEntry × Nat) := [(("bump", [i64, i64], [i64]), 0)]

splice_chunk_literals chunk2ParCode chunk2ParBounds chunk2ParSigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  parBumpExt [] 0 chunk2Fns chunk2Hints

theorem chunk2Par_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      parBumpExt [] 0 chunk2Fns chunk2Hints = .ok (chunk2ParCode, chunk2ParBounds) := by
  t_kernel_rfl

theorem chunk2Par_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      chunk2ParCode chunk2ParBounds (chunk2Fns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def chunk2ParCompiled :
    Compiled armTarget armLegalTarget parBumpExt [] 0 chunk2Fns chunk2Hints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    parBumpExt [] 0 chunk2Fns chunk2Hints 2048 chunk2ParCode chunk2ParBounds
    chunk2Par_cm chunk2Par_meta

splice_chunk_literals chunk3Code chunk3Bounds chunk3Sigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  (chunk2ParSigs ++ chunk1Sigs) [] 0 chunk3Fns chunk3Hints

theorem chunk3_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      (chunk2ParSigs ++ chunk1Sigs) [] 0 chunk3Fns chunk3Hints =
      .ok (chunk3Code, chunk3Bounds) := by
  t_kernel_rfl

theorem chunk3_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      chunk3Code chunk3Bounds (chunk3Fns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def chunk3Compiled :
    Compiled armTarget armLegalTarget
      (chunk2ParSigs ++ chunk1Sigs) [] 0
      chunk3Fns chunk3Hints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    (chunk2ParSigs ++ chunk1Sigs) [] 0
    chunk3Fns chunk3Hints 2048 chunk3Code chunk3Bounds chunk3_cm chunk3_meta

/-! ## 3. Metadata-only linking (`checkLink` / `checkLinkList`) & `run_ret1_sep` -/

theorem twoChunk_link_check : checkLink armLayout chunk1Compiled chunk2Compiled = true := by
  t_kernel_rfl

theorem link_labels_ok :
    checkLinkWithLabels armLayout chunk1Compiled chunk2Compiled = true := by
  t_kernel_rfl

def twoChunkLinked :
    Compiled armTarget armLegalTarget [] [] 0
      (chunk1Fns ++ chunk2Fns) (chunk1Hints ++ chunk2Hints) (Nat.max 2048 2048) :=
  linkCompiled armLayout armLabelClean chunk1Compiled chunk2Compiled twoChunk_link_check

def twoChunkLinkedWithLabels :
    Compiled armTarget armLegalTarget [] [] 0
      (chunk1Fns ++ chunk2Fns) (chunk1Hints ++ chunk2Hints) (Nat.max 2048 2048) :=
  linkCompiledWithLabels armLayout chunk1Compiled chunk2Compiled link_labels_ok

theorem twoChunk_doubleBump_fnSpec :
    armTarget.Defined twoChunkLinked.host "doubleBump" ∧
      armTarget.FnSpec twoChunkLinked.host "doubleBump" doubleBumpSpec
        (twoChunkLinked.bound "doubleBump") 0 := by
  have h := linkCompiled_fnSpec armLabelClean chunk1Compiled chunk2Compiled twoChunk_link_check
    twoChunkMod rfl linkΓ twoChunkMod_acyclic twoChunkMod_wf twoChunkMod_supp twoChunkMod_wp
    (fun _ hx => nomatch hx) ⟨(fun _ hx => nomatch hx), (fun _ hx => nomatch hx)⟩
    (f := fnDoubleBump) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨h.1, fnSpec_of_legalEnv_legalSig_eq_noExit rfl rfl
    (by simp [twoChunkMod, Module.sigs, chunk1Fns, chunk2Fns, Fn.sig])
    (fun _ _ _ _ _ hs => hs) h.2⟩

theorem twoChunk_run_ret1_sep :
    Eventually (armTarget.mach.step twoChunkLinked.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.RetsIn (bs := [i64]) (36#64, ()) (armTarget.mach.data st) ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (twoChunkLinked.bound "doubleBump") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (twoChunkLinked.bound "doubleBump") initMemBytes
          (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr twoChunkLinked.host "doubleBump")) := by
  refine armInit.run_ret1_sep twoChunkLinked twoChunk_doubleBump_fnSpec.2
    initMemBytes (0x1000#64, 5#64, ()) 36#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (36#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa using hm'

def threeChunks : List (CompiledChunk armTarget armLegalTarget [] 0) :=
  [ ⟨[], chunk1Fns, chunk1Hints, 2048, chunk1Compiled⟩,
    ⟨parBumpExt, chunk2Fns, chunk2Hints, 2048, chunk2ParCompiled⟩,
    ⟨chunk2ParSigs ++ chunk1Sigs, chunk3Fns, chunk3Hints, 2048, chunk3Compiled⟩ ]

theorem threeChunk_link_check : checkLinkList armLayout [] threeChunks = true := by
  t_kernel_rfl

theorem list_labels_ok :
    checkLinkListWithLabels armLayout [] threeChunks = true := by
  t_kernel_rfl

def threeChunkLinked :
    Compiled armTarget armLegalTarget [] [] 0
      (chunksFns threeChunks) (chunksHints threeChunks) (chunksMaxBound threeChunks) :=
  linkCompiledList armLayout armLabelClean [] threeChunks threeChunk_link_check

def threeChunkLinkedWithLabels :
    Compiled armTarget armLegalTarget [] [] 0
      (chunksFns threeChunks) (chunksHints threeChunks) (chunksMaxBound threeChunks) :=
  linkCompiledListWithLabels armLayout [] threeChunks list_labels_ok

theorem threeChunk_top_fnSpec :
    armTarget.Defined threeChunkLinked.host "top" ∧
      armTarget.FnSpec threeChunkLinked.host "top" topSpec (threeChunkLinked.bound "top") 0 := by
  have h := linkCompiledList_fnSpec armLabelClean [] threeChunks threeChunk_link_check
    threeChunkMod rfl linkΓ threeChunkMod_acyclic threeChunkMod_wf threeChunkMod_supp
    threeChunkMod_wp (fun _ hx => nomatch hx)
    ⟨(fun _ hx => nomatch hx), (fun _ hx => nomatch hx)⟩
    (f := fnTop) (by simp [threeChunkMod, chunk1Fns, chunk2Fns, chunk3Fns])
  exact ⟨h.1, fnSpec_of_legalEnv_legalSig_eq_noExit rfl rfl
    (by simp [threeChunkMod, Module.sigs, chunk1Fns, chunk2Fns, chunk3Fns, Fn.sig])
    (fun _ _ _ _ _ hs => hs) h.2⟩

theorem threeChunk_run_ret1_sep :
    Eventually (armTarget.mach.step threeChunkLinked.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.RetsIn (bs := [i64]) (37#64, ()) (armTarget.mach.data st) ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (threeChunkLinked.bound "top") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (threeChunkLinked.bound "top") initMemBytes
          (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr threeChunkLinked.host "top")) := by
  refine armInit.run_ret1_sep threeChunkLinked threeChunk_top_fnSpec.2
    initMemBytes (0x1000#64, 5#64, ()) 37#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (37#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by simp [threeChunks, chunksMaxBound])
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa using hm'

/-! ## 4. Negative metadata checks (disjointness, `.L` hygiene, bound mismatch) -/

def dupChunkFns : List Fn := [{ fnDoubleBump with name := "bump" }]
splice_module_hints dupChunkHints armTarget.toIsa armLegalTarget dupChunkFns
splice_chunk_literals dupChunkCode dupChunkBounds dupChunkSigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  (chunk1Sigs ++ []) [] 0 dupChunkFns dupChunkHints

def dupChunkCompiled :
    Compiled armTarget armLegalTarget (chunk1Compiled.sigBounds ++ []) [] 0
      dupChunkFns dupChunkHints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    (chunk1Compiled.sigBounds ++ []) [] 0 dupChunkFns dupChunkHints 2048
    dupChunkCode dupChunkBounds (by t_kernel_rfl) (by t_kernel_rfl)

theorem link_dup_name_rejected :
    checkLink armLayout chunk1Compiled dupChunkCompiled = false := by
  t_kernel_rfl

def dotLChunkFns : List Fn := [{ fnDoubleBump with name := "bad.L0" }]
splice_module_hints dotLChunkHints armTarget.toIsa armLegalTarget dotLChunkFns
splice_chunk_literals dotLChunkCode dotLChunkBounds dotLChunkSigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  (chunk1Sigs ++ []) [] 0 dotLChunkFns dotLChunkHints

theorem dotLChunk_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      (chunk1Compiled.sigBounds ++ []) [] 0 dotLChunkFns dotLChunkHints =
      .ok (dotLChunkCode, dotLChunkBounds) := by
  t_kernel_rfl

theorem dotLChunk_meta :
    checkCompileLitWithLabels armTarget.frame.label armLayout.labelsNodup armLayout.progSmall
      dotLChunkCode dotLChunkBounds (dotLChunkFns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def dotLChunkCompiled :
    Compiled armTarget armLegalTarget (chunk1Compiled.sigBounds ++ []) [] 0
      dotLChunkFns dotLChunkHints 2048 :=
  compileCheckedLitWithLabels armTarget armLayout armLegalTarget
    (chunk1Compiled.sigBounds ++ []) [] 0 dotLChunkFns dotLChunkHints 2048
    dotLChunkCode dotLChunkBounds dotLChunk_cm dotLChunk_meta

theorem link_dotL_name_rejected :
    checkLink armLayout chunk1Compiled dotLChunkCompiled = false := by
  t_kernel_rfl

theorem link_bad_bound_rejected :
    checkLinkList armLayout []
      [ ⟨[], chunk1Fns, chunk1Hints, 2048, chunk1Compiled⟩,
        ⟨[(("bump", [i64, i64], [i64]), chunk1Compiled.bound "bump" + 8)],
          chunk2Fns, chunk2Hints, 2048,
          compileChecked armTarget armLayout armLegalTarget armLabelClean
            [(("bump", [i64, i64], [i64]), chunk1Compiled.bound "bump" + 8)] [] 0
            chunk2Fns chunk2Hints 2048 (by t_kernel_rfl)⟩ ] = false := by
  t_kernel_rfl

/-! ## 5. Axiom Audit -/

#print axioms twoChunk_link_check
#print axioms link_labels_ok
#print axioms twoChunk_doubleBump_fnSpec
#print axioms twoChunk_run_ret1_sep
#print axioms threeChunk_link_check
#print axioms list_labels_ok
#print axioms threeChunk_top_fnSpec
#print axioms threeChunk_run_ret1_sep
#print axioms link_dup_name_rejected
#print axioms link_dotL_name_rejected
#print axioms link_bad_bound_rejected

end LeanQbeTest.T.MainLinkArm64Test
