module

public import LeanQbe.T.MainLinkReuse
public import LeanQbeTest.T.MainLinkAmd64Test
import LeanQbe.T.FlatLemmas
public meta import Lean
public meta import LeanQbeTest.T.MainLinkAmd64Test
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.Amd64.Targ

/-!
# Callee-Pruned Chunk Reuse Test on SysV x64 (`MainLinkReuse`)

Compiles `doubleBump` (two direct calls to `bump`) **once** against the callee table of an old
module `[bump, helper, doubleBump]`, then reuses that chunk without recompiling it in two new
modules where the existing `checkLinkList` rejects it:

1. **Bound moved** (`modB = [bump, helperB, doubleBump]`): `helperB` now calls `bump`, so its
   stack bound changes. `doubleBump` never calls `helper`.
2. **Function removed** (`MainLinkAmd64Test.twoChunkMod = [bump, doubleBump]`): `helper` is gone.

In both cases `CompiledChunk.relink` retypes the chunk to `pruneExt S acc`, where `S` is the
untrusted source-level candidate `rawLegalCalleesOf` checked by `checkCalleesCover`. The result is
a full `LinkedCert`. In case 2 it also gives the end-to-end `Defined ∧ FnSpec` theorem for
`doubleBump` over the relinked host (`linkCompiledList_fnSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainLinkReuseAmd64Test

open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbeTest.T.MainLinkAmd64Test

/-! ## 1. Old and new prefix functions -/

/-- Old-module helper: a leaf. -/
def fnHelperA : Fn :=
  ⟨"helper", [i64, i64], [i64], fun _ _ (_, x, ()) =>
    .let_ ⟨.add i64, (.var x, .imm 1#64, ())⟩ fun (y, ()) =>
    .ret (.var y, ())⟩

/-- New-module helper: calls `bump`, so its stack bound grows. -/
def fnHelperB : Fn :=
  ⟨"helper", [i64, i64], [i64], fun _ _ (p, x, ()) =>
    .call "bump" (as := [i64, i64]) (bs := [i64]) (.var p, .var x, ()) fun (r, ()) =>
    .let_ ⟨.add i64, (.var r, .imm 1#64, ())⟩ fun (y, ()) =>
    .ret (.var y, ())⟩

def helperAFns : List Fn := [fnHelperA]
def helperBFns : List Fn := [fnHelperB]

splice_module_hints helperAHints x64Target.toIsa x64LegalTarget helperAFns
splice_module_hints helperBHints x64Target.toIsa x64LegalTarget helperBFns

splice_chunk_literals helperACode helperABounds helperASigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  (chunk1Sigs ++ []) [] 0 helperAFns helperAHints

def helperACompiled :
    Compiled x64Target x64LegalTarget (chunk1Compiled.sigBounds ++ []) [] 0
      helperAFns helperAHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    (chunk1Compiled.sigBounds ++ []) [] 0 helperAFns helperAHints 2048
    helperACode helperABounds (by t_kernel_rfl) (by t_kernel_rfl)

splice_chunk_literals helperBCode helperBBounds helperBSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  (chunk1Sigs ++ []) [] 0 helperBFns helperBHints

def helperBCompiled :
    Compiled x64Target x64LegalTarget (chunk1Compiled.sigBounds ++ []) [] 0
      helperBFns helperBHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    (chunk1Compiled.sigBounds ++ []) [] 0 helperBFns helperBHints 2048
    helperBCode helperBBounds (by t_kernel_rfl) (by t_kernel_rfl)

/-- The prefix perturbation is real: `helper`'s stack bound differs between the two modules. -/
theorem helper_bound_moved :
    (helperACompiled.bound "helper" == helperBCompiled.bound "helper") = false := by
  t_kernel_rfl

/-! ## 2. `doubleBump`, compiled once against the old prefix `[bump, helperA]` -/

/-- The old accumulator after `[bump, helperA]` (exactly what `checkChunksExt` builds). -/
abbrev oldAcc : List (SigEntry × Nat) :=
  helperACompiled.sigBounds ++ (chunk1Compiled.sigBounds ++ [])

splice_chunk_literals dblCode dblBounds dblSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  (helperASigs ++ (chunk1Sigs ++ [])) [] 0 chunk2Fns chunk2Hints

def dblCompiled :
    Compiled x64Target x64LegalTarget oldAcc [] 0 chunk2Fns chunk2Hints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    oldAcc [] 0 chunk2Fns chunk2Hints 2048 dblCode dblBounds (by t_kernel_rfl) (by t_kernel_rfl)

def bumpChunk : CompiledChunk x64Target x64LegalTarget [] 0 :=
  ⟨[], chunk1Fns, chunk1Hints, 2048, chunk1Compiled⟩
def helperAChunk : CompiledChunk x64Target x64LegalTarget [] 0 :=
  ⟨_, helperAFns, helperAHints, 2048, helperACompiled⟩
def helperBChunk : CompiledChunk x64Target x64LegalTarget [] 0 :=
  ⟨_, helperBFns, helperBHints, 2048, helperBCompiled⟩
def dblChunk : CompiledChunk x64Target x64LegalTarget [] 0 :=
  ⟨_, chunk2Fns, chunk2Hints, 2048, dblCompiled⟩

/-- Baseline: the old module links with the chunk as compiled. -/
theorem old_link_check :
    checkLinkList x64Layout [] [bumpChunk, helperAChunk, dblChunk] = true := by
  t_kernel_rfl

/-! ## 3. Callee cover of `doubleBump` -/

/-- Untrusted candidate from one walk of the source body (no mid-end, no `Rega`). -/
abbrev dblS : List SigEntry := rawLegalCalleesOf x64LegalTarget chunk2Fns

theorem dblS_eq : dblS = [("bump", [i64, i64], [i64])] := by t_kernel_rfl

theorem dblS_cover_check : checkCalleesCover x64LegalTarget chunk2Fns dblS = true := by
  t_kernel_rfl

theorem dbl_midCallees : midCallees x64LegalTarget chunk2Fns = [("bump", [i64, i64], [i64])] := by
  t_kernel_rfl

/-! ## 4. Case B: `helper`'s bound moved -/

/-- Without pruning, the existing linker rejects the reused chunk. -/
theorem boundMoved_unpruned_rejected :
    checkLinkList x64Layout [] [bumpChunk, helperBChunk, dblChunk] = false := by
  t_kernel_rfl

def newAccB : List (SigEntry × Nat) :=
  helperBCompiled.sigBounds ++ (chunk1Compiled.sigBounds ++ [])

def dblChunkB : CompiledChunk x64Target x64LegalTarget [] 0 :=
  dblChunk.relink (pruneExt dblS newAccB) dblS dblS_cover_check (by t_kernel_rfl)

def chunksB : List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  [bumpChunk, helperBChunk, dblChunkB]

theorem chunksB_link : checkLinkList x64Layout [] chunksB = true := by t_kernel_rfl

def modB : Module where
  fns := [fnBump, fnHelperB, fnDoubleBump]

theorem modB_fns_eq : modB.fns = chunksFns chunksB := rfl

def certB : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean modB [] [] 0 2048 where
  chunks := chunksB
  linkCheck := chunksB_link
  fns_eq := modB_fns_eq
  supportsAll := supportsAll_of_eq modB_fns_eq (supportsAll_of_chunks chunksB)
  maxBound_le := Nat.le_of_ble_eq_true (by t_kernel_rfl)

/-- The relinked chunk keeps the exact old `code` and `doubleBump` stack bound. -/
theorem certB_reuses_code :
    dblChunkB.compiled.code = dblCode ∧
      certB.bound "doubleBump" = dblCompiled.bound "doubleBump" :=
  ⟨rfl, linkCompiledList_bound (c := dblChunkB) chunksB_link
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_map_of_mem List.mem_cons_self :
      fnDoubleBump.name ∈ [fnDoubleBump].map Fn.name)⟩

/-! ## 5. Case C: `helper` removed (`twoChunkMod = [bump, doubleBump]`) -/

theorem removed_unpruned_rejected :
    checkLinkList x64Layout [] [bumpChunk, dblChunk] = false := by
  t_kernel_rfl

def dblChunkC : CompiledChunk x64Target x64LegalTarget [] 0 :=
  dblChunk.relink (pruneExt dblS (chunk1Compiled.sigBounds ++ [])) dblS dblS_cover_check
    (by t_kernel_rfl)

def chunksC : List (CompiledChunk x64Target x64LegalTarget [] 0) := [bumpChunk, dblChunkC]

theorem chunksC_link : checkLinkList x64Layout [] chunksC = true := by t_kernel_rfl

theorem twoChunkMod_fns_eqC : twoChunkMod.fns = chunksFns chunksC := rfl

def certC :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean twoChunkMod [] [] 0 2048 where
  chunks := chunksC
  linkCheck := chunksC_link
  fns_eq := twoChunkMod_fns_eqC
  supportsAll := twoChunkMod_supp
  maxBound_le := Nat.le_of_ble_eq_true (by t_kernel_rfl)

/-- End-to-end machine-code `Defined ∧ FnSpec` for `doubleBump` over the host linked from the
reused, relinked chunk. -/
theorem certC_doubleBump_fnSpec :
    x64Target.Defined certC.host "doubleBump" ∧
      x64Target.FnSpec certC.host "doubleBump" doubleBumpSpec
        (certC.bound "doubleBump") 0 := by
  have h := linkCompiledList_fnSpec x64LabelClean [] chunksC chunksC_link twoChunkMod
    twoChunkMod_fns_eqC linkΓ twoChunkMod_acyclic twoChunkMod_wf twoChunkMod_supp
    twoChunkMod_wp (fun _ hx => nomatch hx) ⟨(fun _ hx => nomatch hx), (fun _ hx => nomatch hx)⟩
    (f := fnDoubleBump) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨h.1, fnSpec_of_legalEnv_legalSig_eq_noExit rfl rfl
    (by simp [twoChunkMod, Module.sigs, chunk1Fns, chunk2Fns, Fn.sig])
    (fun _ _ _ _ _ hs => hs) h.2⟩

/-! ## 6. Axiom audit -/

/-- info: 'LeanQbe.T.compileModule_mono_callees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanQbe.T.compileModule_mono_callees

/-- info: 'LeanQbe.T.CompiledChunk.relink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanQbe.T.CompiledChunk.relink

/-- info: 'LeanQbeTest.T.MainLinkReuseAmd64Test.certB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certB

/--
info: 'LeanQbeTest.T.MainLinkReuseAmd64Test.certC_doubleBump_fnSpec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms certC_doubleBump_fnSpec

end LeanQbeTest.T.MainLinkReuseAmd64Test
