/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12C
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12CRows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12CRowsProof
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep12C
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep12CRows
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat Fidelity Step-12 Bundle C — Source, Legalization, & Proof (`KissatFidelityStep12CTest`)

Self-contained verification suite for `FullFidelityStep12C{,Rows,Proof,RowsProof}` (`508`-fn
`fidStep12CModule` = `505` Step-10 fns + `3` inserted helpers, `0` externs, `0` exits):
1. Module shape, `<= 6`-arg SysV ABI, `namesNodup`, `checkAcyclic`, and `checkPatchCallsOk`
   `#guard`s.
2. Cpp / QBE printing (`PrintCpp.ppTModule`, `PrintQbe.module`) on `fidStep12CModule` (`508` fns)
   and 4-ISA legalization (`aarch64`, `scalar64`, `x64AVX2`, `x64AVX512`) `#guard`s on all `7`
   Step-12C patch functions.
3. Kernel `Fn.Wf`, `callsOk`, and `SpecEntry.Impl` proof witnesses (`std3`, `0` `@[expose]` thms).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityStep12CTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep10
open LeanQbe.T.Examples.Kissat.FullFidelityStep12C
open LeanQbe.T.Examples.Kissat.PatchModule

#guard fidStep12CModuleFns.length == 508
#guard (fidStep12CModuleFns.map Fn.name).eraseDups.length == 508
#guard fidStep12CModuleFns.all fun fn => fn.as.length <= 6
#guard fidStep12CModule.checkAcyclic == true
#guard fidStep12CModule.externs.isEmpty && fidStep12CModule.exits.isEmpty
#guard checkPatchCallsOk fidStep10Module fidStep12CRepls fidStep12CBefores == true
#guard (fidStep12CRepls.map Fn.name) ==
  [ "full_add_clause", "full_sweep_copy", "full_learn_clause_m6", "full_viv_sort_counts_m6" ]
#guard (fidStep12CBefores.flatMap (fun p => p.2.map Fn.name)) ==
  [ "full_watch_pop_c0", "full_reduce_purge_c0", "full_viv_sift_counts_m6" ]

#guard (PrintCpp.ppTModule fidStep12CModule).isOk
#guard (PrintQbe.module fidStep12CModule).isOk
#guard (PrintCpp.ppModule (fidStep12CRepls.map (Fn.legal .aarch64))).isOk
#guard (PrintCpp.ppModule (fidStep12CRepls.map (Fn.legal .scalar64))).isOk
#guard (PrintCpp.ppModule (fidStep12CRepls.map (Fn.legal .x64AVX2))).isOk
#guard (PrintCpp.ppModule (fidStep12CRepls.map (Fn.legal .x64AVX512))).isOk
#guard fidStep12CRepls.all fun fn =>
  (Fn.legal .aarch64 fn).body.isLegal .aarch64 &&
  (Fn.legal .scalar64 fn).body.isLegal .scalar64 &&
  (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2 &&
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard (fidStep12CBefores.flatMap Prod.snd).all fun fn =>
  (Fn.legal .aarch64 fn).body.isLegal .aarch64 &&
  (Fn.legal .scalar64 fn).body.isLegal .scalar64 &&
  (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2 &&
  (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

theorem fidStep12C_wf : ∀ f ∈ fidStep12CModule.fns, f.Wf :=
  fidStep12CModule_wf

theorem fidStep12C_shape :
    fidStep12CModule.fns.length = 508 ∧
    fidStep12CModule.namesNodup ∧
    fidStep12CModule.exits = [] :=
  ⟨fidStep12CFns_length, fidStep12CModule_names_nodup, fidStep12C_noExit⟩

theorem fidStep12C_rows_ok :
    (fidStep12CRows.map SpecEntry.name).Nodup ∧
    ∀ e ∈ fidStep12CRows, e.noExit = true :=
  ⟨fidStep12CRows_nodup, fidStep12CRows_noExit⟩

end LeanQbeTest.T.KissatFidelityStep12CTest

end
