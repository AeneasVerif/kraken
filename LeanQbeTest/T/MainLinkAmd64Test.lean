module

public import LeanQbe.T.MainLink
public import LeanQbe.T.MainLinkSplice
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainSplice
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbeTest.T.MainLinkFixtures
import LeanQbe.T.FlatLemmas
public meta import Lean
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbeTest.T.MainLinkFixtures

/-!
# Compositional Multi-Chunk Linking Test on SysV x64 (`MainLink` + `MainLinkSplice`)

Tests literal-backed `LeanQbe.T.MainLink` end-to-end on `x64Target` (`x64LegalTarget`,
`x64Layout`, `x64Init`):
1. Separately compiles `chunk1` (`bump`), `chunk2` (`doubleBump` calling `bump`), and `chunk3`
   (`top` calling `doubleBump`) via `splice_chunk_literals` + `t_kernel_rfl` (`compileCheckedLit`),
   plus a parallel-compiled `chunk2Par` taking a literal `ext` without referencing `chunk1Compiled`.
2. Links `chunk1` + `chunk2` via O(N) metadata-only `checkLink` (`t_kernel_rfl`, zero compiler
   re-evaluation on literal `code`/`bounds`) and `linkCompiled`, and links `[chunk1, chunk2Par,
   chunk3]` via `checkLinkList` (`t_kernel_rfl`) and `linkCompiledList`.
3. Derives closed `x64Init.run_ret1_sep` execution theorems over the linked hosts
   (`doubleBump(0x1000, 5) = 36`, `top(0x1000, 5) = 37`, updating `cell64 0x1000 21`) and verifies
   `linkCompiled_bound_right` / `linkCompiledList_bound`.
4. Negative metadata checks: duplicate chunk function names, exit-symbol collision, and mismatched
   callee stack bounds.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainLinkAmd64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 Kraken
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

private theorem all_supports_x64 :
    [fnBump, fnDoubleBump, fnTop].all (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) =
      true := by
  t_kernel_rfl

theorem twoChunkMod_supp :
    ∀ f ∈ twoChunkMod.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true := by
  have hall := supportsAll_to_forall all_supports_x64
  intro f hf
  simp only [twoChunkMod, chunk1Fns, chunk2Fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> exact hall _ (by simp)

theorem threeChunkMod_supp :
    ∀ f ∈ threeChunkMod.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true := by
  have hall := supportsAll_to_forall all_supports_x64
  intro f hf
  simp only [threeChunkMod, chunk1Fns, chunk2Fns, chunk3Fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> exact hall _ (by simp)

/-! ## 2. Literal-backed per-chunk compilation (`splice_chunk_literals` + `compileCheckedLit`) -/

splice_module_hints chunk1Hints x64Target.toIsa x64LegalTarget chunk1Fns
splice_module_hints chunk2Hints x64Target.toIsa x64LegalTarget chunk2Fns
splice_module_hints chunk3Hints x64Target.toIsa x64LegalTarget chunk3Fns

splice_chunk_literals chunk1Code chunk1Bounds chunk1Sigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 chunk1Fns chunk1Hints

theorem chunk1_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      [] [] 0 chunk1Fns chunk1Hints = .ok (chunk1Code, chunk1Bounds) := by
  t_kernel_rfl

theorem chunk1_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      chunk1Code chunk1Bounds (chunk1Fns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def chunk1Compiled : Compiled x64Target x64LegalTarget [] [] 0 chunk1Fns chunk1Hints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 chunk1Fns chunk1Hints 2048 chunk1Code chunk1Bounds chunk1_cm chunk1_meta

splice_chunk_literals chunk2Code chunk2Bounds chunk2Sigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  (chunk1Sigs ++ []) [] 0 chunk2Fns chunk2Hints

theorem chunk2_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      (chunk1Compiled.sigBounds ++ []) [] 0 chunk2Fns chunk2Hints =
      .ok (chunk2Code, chunk2Bounds) := by
  t_kernel_rfl

theorem chunk2_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      chunk2Code chunk2Bounds (chunk2Fns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def chunk2Compiled :
    Compiled x64Target x64LegalTarget (chunk1Compiled.sigBounds ++ []) [] 0
      chunk2Fns chunk2Hints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    (chunk1Compiled.sigBounds ++ []) [] 0 chunk2Fns chunk2Hints 2048
    chunk2Code chunk2Bounds chunk2_cm chunk2_meta

/-- Parallel chunk 2 compiled against a standalone literal `ext` (independent of `chunk1`). -/
def parBumpExt : List (SigEntry × Nat) := [(("bump", [i64, i64], [i64]), 0)]

splice_chunk_literals chunk2ParCode chunk2ParBounds chunk2ParSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  parBumpExt [] 0 chunk2Fns chunk2Hints

theorem chunk2Par_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      parBumpExt [] 0 chunk2Fns chunk2Hints = .ok (chunk2ParCode, chunk2ParBounds) := by
  t_kernel_rfl

theorem chunk2Par_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      chunk2ParCode chunk2ParBounds (chunk2Fns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def chunk2ParCompiled :
    Compiled x64Target x64LegalTarget parBumpExt [] 0 chunk2Fns chunk2Hints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    parBumpExt [] 0 chunk2Fns chunk2Hints 2048 chunk2ParCode chunk2ParBounds
    chunk2Par_cm chunk2Par_meta

splice_chunk_literals chunk3Code chunk3Bounds chunk3Sigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  (chunk2ParSigs ++ chunk1Sigs) [] 0 chunk3Fns chunk3Hints

theorem chunk3_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      (chunk2ParSigs ++ chunk1Sigs) [] 0 chunk3Fns chunk3Hints =
      .ok (chunk3Code, chunk3Bounds) := by
  t_kernel_rfl

theorem chunk3_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      chunk3Code chunk3Bounds (chunk3Fns.map Fn.name) [] 2048 = true := by
  t_kernel_rfl

def chunk3Compiled :
    Compiled x64Target x64LegalTarget
      (chunk2ParSigs ++ chunk1Sigs) [] 0
      chunk3Fns chunk3Hints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    (chunk2ParSigs ++ chunk1Sigs) [] 0
    chunk3Fns chunk3Hints 2048 chunk3Code chunk3Bounds chunk3_cm chunk3_meta

/-! ## 3. Metadata-only linking (`checkLink` / `checkLinkList`) & `run_ret1_sep` -/

theorem twoChunk_link_check : checkLink x64Layout chunk1Compiled chunk2Compiled = true := by
  t_kernel_rfl

def twoChunkLinked :
    Compiled x64Target x64LegalTarget [] [] 0
      (chunk1Fns ++ chunk2Fns) (chunk1Hints ++ chunk2Hints) (Nat.max 2048 2048) :=
  linkCompiled x64Layout x64LabelClean chunk1Compiled chunk2Compiled twoChunk_link_check

theorem twoChunk_bound_eq :
    twoChunkLinked.bound "bump" = chunk1Compiled.bound "bump" ∧
      twoChunkLinked.bound "doubleBump" = chunk2Compiled.bound "doubleBump" :=
  ⟨linkCompiled_bound_left chunk1Compiled chunk2Compiled twoChunk_link_check
    (by simp [chunk1Fns, fnBump]),
   linkCompiled_bound_right chunk1Compiled chunk2Compiled twoChunk_link_check
    (by simp [chunk2Fns, fnDoubleBump])⟩

theorem twoChunk_doubleBump_fnSpec :
    x64Target.Defined twoChunkLinked.host "doubleBump" ∧
      x64Target.FnSpec twoChunkLinked.host "doubleBump" doubleBumpSpec
        (twoChunkLinked.bound "doubleBump") 0 := by
  have h := linkCompiled_fnSpec x64LabelClean chunk1Compiled chunk2Compiled twoChunk_link_check
    twoChunkMod rfl linkΓ twoChunkMod_acyclic twoChunkMod_wf twoChunkMod_supp twoChunkMod_wp
    (fun _ hx => nomatch hx) ⟨(fun _ hx => nomatch hx), (fun _ hx => nomatch hx)⟩
    (f := fnDoubleBump) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨h.1, fnSpec_of_legalEnv_legalSig_eq_noExit rfl rfl
    (by simp [twoChunkMod, Module.sigs, chunk1Fns, chunk2Fns, Fn.sig])
    (fun _ _ _ _ _ hs => hs) h.2⟩

theorem twoChunk_run_ret1_sep :
    Eventually (x64Target.mach.step twoChunkLinked.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.RetsIn (bs := [i64]) (36#64, ()) (x64Target.mach.data st) ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (twoChunkLinked.bound "doubleBump") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (twoChunkLinked.bound "doubleBump") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr twoChunkLinked.host "doubleBump")) := by
  refine x64Init.run_ret1_sep twoChunkLinked twoChunk_doubleBump_fnSpec.2
    initMemBytes (0x1000#64, 5#64, ()) 36#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (36#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa using hm'

def threeChunks : List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  [ ⟨[], chunk1Fns, chunk1Hints, 2048, chunk1Compiled⟩,
    ⟨parBumpExt, chunk2Fns, chunk2Hints, 2048, chunk2ParCompiled⟩,
    ⟨chunk2ParSigs ++ chunk1Sigs, chunk3Fns, chunk3Hints, 2048, chunk3Compiled⟩ ]

theorem threeChunk_link_check : checkLinkList x64Layout [] threeChunks = true := by
  t_kernel_rfl

def threeChunkLinked :
    Compiled x64Target x64LegalTarget [] [] 0
      (chunksFns threeChunks) (chunksHints threeChunks) (chunksMaxBound threeChunks) :=
  linkCompiledList x64Layout x64LabelClean [] threeChunks threeChunk_link_check

theorem threeChunk_top_bound_eq :
    threeChunkLinked.bound "top" = chunk3Compiled.bound "top" :=
  linkCompiledList_bound threeChunk_link_check
    (c := ⟨chunk2ParSigs ++ chunk1Sigs, chunk3Fns, chunk3Hints, 2048, chunk3Compiled⟩)
    (by simp [threeChunks]) (by simp [chunk3Fns, fnTop])

theorem threeChunk_top_fnSpec :
    x64Target.Defined threeChunkLinked.host "top" ∧
      x64Target.FnSpec threeChunkLinked.host "top" topSpec (threeChunkLinked.bound "top") 0 := by
  have h := linkCompiledList_fnSpec x64LabelClean [] threeChunks threeChunk_link_check
    threeChunkMod rfl linkΓ threeChunkMod_acyclic threeChunkMod_wf threeChunkMod_supp
    threeChunkMod_wp (fun _ hx => nomatch hx)
    ⟨(fun _ hx => nomatch hx), (fun _ hx => nomatch hx)⟩
    (f := fnTop) (by simp [threeChunkMod, chunk1Fns, chunk2Fns, chunk3Fns])
  exact ⟨h.1, fnSpec_of_legalEnv_legalSig_eq_noExit rfl rfl
    (by simp [threeChunkMod, Module.sigs, chunk1Fns, chunk2Fns, chunk3Fns, Fn.sig])
    (fun _ _ _ _ _ hs => hs) h.2⟩

theorem threeChunk_run_ret1_sep :
    Eventually (x64Target.mach.step threeChunkLinked.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.RetsIn (bs := [i64]) (37#64, ()) (x64Target.mach.data st) ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (threeChunkLinked.bound "top") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (threeChunkLinked.bound "top") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr threeChunkLinked.host "top")) := by
  refine x64Init.run_ret1_sep threeChunkLinked threeChunk_top_fnSpec.2
    initMemBytes (0x1000#64, 5#64, ()) 37#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (37#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by simp [threeChunks, chunksMaxBound])
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa using hm'

/-! ## 4. Negative metadata checks (duplicate name, exit collision, bound mismatch) -/

def dupChunkFns : List Fn := [{ fnDoubleBump with name := "bump" }]
splice_module_hints dupChunkHints x64Target.toIsa x64LegalTarget dupChunkFns
splice_chunk_literals dupChunkCode dupChunkBounds dupChunkSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  (chunk1Sigs ++ []) [] 0 dupChunkFns dupChunkHints

def dupChunkCompiled :
    Compiled x64Target x64LegalTarget (chunk1Compiled.sigBounds ++ []) [] 0
      dupChunkFns dupChunkHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    (chunk1Compiled.sigBounds ++ []) [] 0 dupChunkFns dupChunkHints 2048
    dupChunkCode dupChunkBounds (by t_kernel_rfl) (by t_kernel_rfl)

theorem link_dup_name_rejected :
    checkLink x64Layout chunk1Compiled dupChunkCompiled = false := by
  t_kernel_rfl

theorem exit_collision_rejected :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      chunk1Code chunk1Bounds (chunk1Fns.map Fn.name) ["bump"] 2048 = false := by
  t_kernel_rfl

theorem link_bad_bound_rejected :
    checkLinkList x64Layout []
      [ ⟨[], chunk1Fns, chunk1Hints, 2048, chunk1Compiled⟩,
        ⟨[(("bump", [i64, i64], [i64]), chunk1Compiled.bound "bump" + 8)],
          chunk2Fns, chunk2Hints, 2048,
          compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
            [(("bump", [i64, i64], [i64]), chunk1Compiled.bound "bump" + 8)] [] 0
            chunk2Fns chunk2Hints 2048 (by t_kernel_rfl)⟩ ] = false := by
  t_kernel_rfl

/-! ## 5. Axiom Audit -/

#print axioms LeanQbe.T.compileModule_mono_lookupBound
#print axioms LeanQbe.T.compileModule_append
#print axioms LeanQbe.T.compileCheckedLit
#print axioms LeanQbe.T.compileCheckedLitWithLabels
#print axioms LeanQbe.T.linkCompiled
#print axioms LeanQbe.T.linkCompiledList
#print axioms LeanQbe.T.linkCompiled_fnSpec
#print axioms LeanQbe.T.linkCompiledList_fnSpec
#print axioms twoChunk_link_check
#print axioms twoChunk_bound_eq
#print axioms twoChunk_doubleBump_fnSpec
#print axioms twoChunk_run_ret1_sep
#print axioms threeChunk_link_check
#print axioms threeChunk_top_bound_eq
#print axioms threeChunk_top_fnSpec
#print axioms threeChunk_run_ret1_sep
#print axioms link_dup_name_rejected
#print axioms exit_collision_rejected
#print axioms link_bad_bound_rejected

end LeanQbeTest.T.MainLinkAmd64Test
