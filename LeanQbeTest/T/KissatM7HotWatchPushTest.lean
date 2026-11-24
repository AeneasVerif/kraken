module

public import LeanQbe.T.Examples.Kissat.FullM7HotWatchPush
public import LeanQbe.T.Examples.Kissat.FullM7HotWatchPushProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7HotWatchPush
meta import LeanQbe.T.Examples.Kissat.FullM7HotWatchPushProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M7 `FullM7HotWatchPush`

1. Executable `#guard` checks on `m7HotWatchPushModule` (`2` fns, `1` extern `"full_wstack_defrag_m6"`,
   `0` exits), drop-in handles `m7WatchPushSlowFn` / `m7WatchPushFastFn`, `m7HotWatchPushInlPolicy`,
   `patchM7HotWatchPushFns`, `checkAcyclic = true`, `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal`
   checks (`.aarch64`, `.scalar64`, `.x64AVX2`, `.x64AVX512`).
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, parametric `Func.wp`
   against canonical `Full.fullWatchPushSpec`, `m7HotWatchPushEnv_noExit`, closed `ModuleOk`,
   and concrete `Mem 64` UNSAT non-vacuity (`nv_m7_watch_push_m6`, `XPost := False`, `0` SAT).
3. Single-line `< 115`-col `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7HotWatchPushTest

open Std.Sat
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7HotWatchPush

/-! ## 1. Executable `#guard` Codegen, Policy & Legalization Checks -/

#guard m7HotWatchPushFns.length == 2
#guard m7HotWatchPush_fns.length == 2
#guard m7WatchPushSlowFn.name == "full_watch_push_slow_m6"
#guard m7WatchPushSlowFn.as == [i64, i32, i32, i32, i32]
#guard m7WatchPushSlowFn.rs == [.bool]
#guard m7WatchPushFastFn.name == "full_watch_push_m6"
#guard m7WatchPushFastFn.as == [i64, i32, i32, i32, i32]
#guard m7WatchPushFastFn.rs == [.bool]
#guard m7WatchPushFastFn.numCalls == 1 && m7WatchPushFastFn.numLoops == 0
#guard m7HotWatchPushModule.checkAcyclic == true
#guard m7HotWatchPushModule.externs == [⟨"full_wstack_defrag_m6", [i64], []⟩]
#guard m7HotWatchPushModule.exits.isEmpty == true
#guard m7HotWatchPushSpecTable.length == 3
#guard m7HotWatchPushSpecTable.all (·.noExit) == true
#guard (patchM7HotWatchPushFns [m7WatchPushFastFn]).map (fun f => (f.name, f.as, f.rs)) ==
  m7HotWatchPushFns.map (fun f => (f.name, f.as, f.rs))
example : patchM7HotWatchPushFns [m7WatchPushFastFn] = m7HotWatchPushFns := rfl
#guard m7HotWatchPushInlPolicy.budget "full_watch_push_m6" == 220
#guard m7HotWatchPushInlPolicy.budget "full_watch_push" == 220
#guard m7HotWatchPushInlPolicy.budget "full_watch_push_slow_m6" == 0
#guard m7HotWatchPushInlPolicy.keepOutOfLine == ["full_watch_push_slow_m6"]
#guard (ppTModule m7HotWatchPushModule).isOk
#guard (PrintQbe.module m7HotWatchPushModule).isOk
#guard (ppModule (m7HotWatchPushFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7HotWatchPushFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7HotWatchPushFns.map (Fn.legal .x64AVX2))).isOk
#guard m7HotWatchPushFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem m7wp_slow_wf : Func.Wf full_watch_push_slow_m6_body :=
  full_watch_push_slow_m6_wf

theorem m7wp_fast_wf : Func.Wf full_watch_push_m6_body :=
  full_watch_push_m6_wf

theorem m7wp_fns_wf : ∀ f ∈ m7HotWatchPushFns, f.Wf :=
  m7HotWatchPushFns_wf

theorem m7wp_acyc : m7HotWatchPushModule.checkAcyclic = true :=
  m7HotWatchPush_acyclic

theorem m7wp_slow_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag_m6" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Func.wp Γ m7WatchPushSlowFn.body a m Q X :=
  m7WatchPushSlowFn_wp Γ hDefrag

theorem m7wp_fast_wp (Γ : Env)
    (hSlow : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_slow_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Func.wp Γ m7WatchPushFastFn.body a m Q X :=
  m7WatchPushFastFn_wp Γ hSlow

theorem m7wp_noExit :
    ∀ f as bs xs m Q X X',
      m7HotWatchPushEnv f as bs xs m Q X → m7HotWatchPushEnv f as bs xs m Q X' :=
  m7HotWatchPushEnv_noExit

theorem m7wp_tbl :
    TableImpl m7HotWatchPushEnv m7HotWatchPushFns m7HotWatchPushSpecTable :=
  m7HotWatchPush_tableImpl

theorem m7wp_modOk : ModuleOk m7HotWatchPushEnv m7HotWatchPushModule :=
  m7HotWatchPush_moduleOk

theorem m7wp_nv :
    Func.wp m7HotWatchPushEnv full_watch_push_m6_body
      (nvOneLitCfg.hdr, 0#32, 0#32, 0#32, 1#32, ()) nvOneLitMem
      (fun (ok, ()) m' =>
        nvOneLitF0.Unsat ∧ ok = false ∧
        ∃ wvec' wstk' wlen' wusable' wsort',
          let s' : FullState :=
            { nvOneLitState with
              core := { nvOneLitState.core with
                wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
              scratch := { nvOneLitState.scratch with wsort := wsort' } }
          s'.LengthsOk nvOneLitCfg ∧ WatchStackLayout s'.core ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_watch_push_m6

end LeanQbeTest.T.KissatM7HotWatchPushTest

/-! ## 3. Single-Line `#print axioms` Audit (`std3` Only) -/

abbrev m7hw_slow_wf := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_slow_wf
abbrev m7hw_fast_wf := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_fast_wf
abbrev m7hw_fns_wf := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_fns_wf
abbrev m7hw_acyc := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_acyc
abbrev m7hw_slow_wp := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_slow_wp
abbrev m7hw_fast_wp := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_fast_wp
abbrev m7hw_noExit := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_noExit
abbrev m7hw_tbl := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_tbl
abbrev m7hw_modOk := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_modOk
abbrev m7hw_nv := @LeanQbeTest.T.KissatM7HotWatchPushTest.m7wp_nv

#print axioms m7hw_slow_wf
#print axioms m7hw_fast_wf
#print axioms m7hw_fns_wf
#print axioms m7hw_acyc
#print axioms m7hw_slow_wp
#print axioms m7hw_fast_wp
#print axioms m7hw_noExit
#print axioms m7hw_tbl
#print axioms m7hw_modOk
#print axioms m7hw_nv

end
