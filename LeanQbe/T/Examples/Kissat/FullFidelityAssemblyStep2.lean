/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
public import LeanQbe.T.Examples.Kissat.FullFidelityBcp
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
meta import LeanQbe.T.Examples.Kissat.FullFidelityBcp
meta import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Canonical Gate-1 `KissatFidelity` Assembly — Step 2 (`FullFidelityAssemblyStep2`)

Step-2 C0 assembly (`471` fns, `0` externs, `0` exits) layering `FullFidelityBcp`'s Option-A
`fidBcpHotPushRepls` (`9` replacements) + `fidBcpHotPushBefores` (`2` inserted helpers:
`full_watch_push_slow_m6`, `full_prop_flush_del_fid`) atop `fidStep1Module` (`469` fns) via
`PatchModule.patchFns`, preserving unified `FullMem` (`151 B/var`).

Includes hot two-level `full_watch_push_m6`, delayed-watch `S1.5` BCP
(`full_propagate_ignore_hot`, `full_propagate_ignore`), VSIDS heap (`full_heap_down`,
`full_heap_pop`), 1UIP (`full_deduce_1uip_m6`, `full_deduce_1uip_m6_hdr`), and decision
(`full_next_dec_var`, `m6_hdr_decide_fid`). Strictly Gate-1 (`0` beyond-upstream heuristics).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep1
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. Step-2 `PatchModule` Splice (`fidStep1Module` + `fidBcpHotPushRepls` = `471` fns) -/

/-- Ordered `471`-fn Step-2 function list (`fidStep1Fns` + `fidBcpHotPushRepls` +
`fidBcpHotPushBefores`). -/
def fidStep2Fns : List Fn :=
  patchFns fidBcpHotPushRepls fidBcpHotPushBefores fidStep1Fns

/-- Closed `471`-function Step-2 module (`0` externs, `0` exits). -/
def fidStep2Module : LeanQbe.T.Module :=
  { fidStep1Module with fns := fidStep2Fns }

theorem fidStep2Fns_eq : fidStep2Module.fns = fidStep2Fns :=
  rfl

theorem fidStep2Module_wf : ∀ f ∈ fidStep2Module.fns, f.Wf :=
  patchFns_wf fidStep1Module_wf fidBcpHotPushRepls_wf fidBcpHotPushBefores_wf

theorem fidStep2_noExit : fidStep2Module.exits = [] :=
  fidStep1_noExit

/-- All `11` functions added or replaced in Step 2 (`9` replacements + `2` helpers). -/
def fidStep2NewFns : List Fn :=
  fidBcpHotPushRepls ++ [FullM7HotWatchPush.m7WatchPushSlowFn, fidPropFlushDelFn]

/-! ## 2. Standalone Gate-1 Purity, Acyclicity, & 4-ISA Codegen Guards -/

#guard fidStep2Fns.length == 471
#guard (fidStep2Fns.map Fn.name).eraseDups.length == 471
#guard fidStep2Module.checkAcyclic == true
#guard fidStep2Module.externs.isEmpty && fidStep2Module.exits.isEmpty
#guard !(fidStep2Fns.map Fn.name).contains "full_bve_find_xor_m8"
#guard !(fidStep2Fns.map Fn.name).contains "full_bve_bce_side_m8"
#guard !(fidStep2Fns.map Fn.name).contains "m8_log2_q16"
#guard !(fidStep2Fns.map Fn.name).contains "full_xor_gauss"
#guard !(fidStep2Fns.map Fn.name).contains "full_prelearn_m8"
#guard (fidStep2Fns.map Fn.name).contains "full_watch_push_slow_m6"
#guard (fidStep2Fns.map Fn.name).contains "full_watch_push_m6"
#guard (fidStep2Fns.map Fn.name).contains "full_prop_flush_del_fid"
#guard (fidStep2Fns.map Fn.name).contains "full_propagate_ignore_hot"
#guard (fidStep2Fns.map Fn.name).contains "full_propagate_ignore"
#guard (fidStep2Fns.map Fn.name).contains "full_deduce_1uip_m6"
#guard (fidStep2Fns.map Fn.name).contains "full_deduce_1uip_m6_hdr"
#guard (fidStep2Fns.map Fn.name).contains "full_next_dec_var"
#guard (fidStep2Fns.map Fn.name).contains "m6_hdr_decide_fid"

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2

end
