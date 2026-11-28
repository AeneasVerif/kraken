/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Kissat.Src.Header
import LeanQbe.T.Examples.Kissat.Src.Config
import LeanQbe.T.Examples.Kissat.Src.Float64
import LeanQbe.T.Examples.Kissat.Src.Tiers
import LeanQbe.T.InterpKissat
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Config
meta import LeanQbe.T.Examples.Kissat.Src.Float64
meta import LeanQbe.T.Examples.Kissat.Src.Tiers
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Bitmask Parity & Execution Tests for `Kissat.Src.Config`

1. Exact upstream `kissat/src/config.c` bitmask & option parity checks across all `5` presets
   (`default`, `plain`, `basic`, `sat`, `unsat`) and all `13` `--plain` options.
2. `checkAcyclic`, `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` checks on `Config.fns` and
   closed `Float64.fns ++ Tiers.fns ++ Config.fns`.
3. `InterpKissat` execution `#guard`s verifying runtime presets on a `3,456`-byte `FullM6Hdr`.
4. Headline `fns_wf` / `checkAcyclic` theorems and single-line `#print axioms` (`<= std3`,
   `< 115c`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.KissatConfigTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Config

/-! ## 1. Pure Preset Bitmask & Upstream 13-Option `--plain` Parity `#guard`s -/

private def plain13Flags : List (BitVec 64) :=
  [ cfgFlagBumpReasons
  , cfgFlagChrono
  , cfgFlagCompact
  , cfgFlagEagerSubsume
  , cfgFlagJumpReasons
  , cfgFlagOtfs
  , cfgFlagPreprocess
  , cfgFlagReorder
  , cfgFlagRephase
  , cfgFlagRestartReuseTrail
  , cfgFlagSimplify
  , cfgFlagTumble
  , cfgFlagStableOnly
  ]

private def plain12DisabledFlags : List (BitVec 64) :=
  [ cfgFlagBumpReasons
  , cfgFlagChrono
  , cfgFlagCompact
  , cfgFlagEagerSubsume
  , cfgFlagJumpReasons
  , cfgFlagOtfs
  , cfgFlagPreprocess
  , cfgFlagReorder
  , cfgFlagRephase
  , cfgFlagRestartReuseTrail
  , cfgFlagSimplify
  , cfgFlagTumble
  ]

private def basic3DisabledFlags : List (BitVec 64) :=
  [ cfgFlagRestart, cfgFlagReduce, cfgFlagMinimize ]

#guard plain13Flags.length == 13
#guard plain12DisabledFlags.length == 12
#guard basic3DisabledFlags.length == 3
#guard (plain13Flags.foldl (· ||| ·) 0#64) == cfgPlain13Mask
#guard (plain12DisabledFlags.foldl (· ||| ·) 0#64) == cfgPlainDisableMask
#guard (basic3DisabledFlags.foldl (· ||| ·) 0#64) == cfgBasicExtraMask

-- Exact symmetric deltas between upstream config.c presets
#guard (cfgDefault ^^^ cfgPlain) == cfgPlain13Mask
#guard (cfgPlain ^^^ cfgBasic) == cfgBasicExtraMask
#guard (cfgDefault ^^^ cfgSat) == (cfgFlagTargetSat ||| cfgFlagRestartintSat)
#guard (cfgDefault ^^^ cfgUnsat) == cfgFlagFocusedOnly

-- All 13 `--plain` option settings vs `default`, `basic`, `sat`, `unsat`
#guard plain12DisabledFlags.all (fun f => cfgHasFlag cfgDefault f)
#guard plain12DisabledFlags.all (fun f => !cfgHasFlag cfgPlain f)
#guard plain12DisabledFlags.all (fun f => !cfgHasFlag cfgBasic f)
#guard plain12DisabledFlags.all (fun f => cfgHasFlag cfgSat f)
#guard plain12DisabledFlags.all (fun f => cfgHasFlag cfgUnsat f)

#guard basic3DisabledFlags.all (fun f => cfgHasFlag cfgDefault f)
#guard basic3DisabledFlags.all (fun f => cfgHasFlag cfgPlain f)
#guard basic3DisabledFlags.all (fun f => !cfgHasFlag cfgBasic f)
#guard basic3DisabledFlags.all (fun f => cfgHasFlag cfgSat f)
#guard basic3DisabledFlags.all (fun f => cfgHasFlag cfgUnsat f)

-- `stable` (0/1/2), `target` (1/2), `restartint` (1/50), and uninitialized-zero fallback
#guard cfgStableVal 0#64 == 1#64
#guard cfgStableVal cfgDefault == 1#64
#guard cfgStableVal cfgPlain == 2#64
#guard cfgStableVal cfgBasic == 2#64
#guard cfgStableVal cfgSat == 1#64
#guard cfgStableVal cfgUnsat == 0#64

#guard cfgTargetVal 0#64 == 1#64
#guard cfgTargetVal cfgDefault == 1#64
#guard cfgTargetVal cfgPlain == 1#64
#guard cfgTargetVal cfgBasic == 1#64
#guard cfgTargetVal cfgSat == 2#64
#guard cfgTargetVal cfgUnsat == 1#64

#guard cfgRestartintVal 0#64 == 1#64
#guard cfgRestartintVal cfgDefault == 1#64
#guard cfgRestartintVal cfgPlain == 1#64
#guard cfgRestartintVal cfgBasic == 1#64
#guard cfgRestartintVal cfgSat == 50#64
#guard cfgRestartintVal cfgUnsat == 1#64

#guard cfgOfId? cfgIdDefault == some cfgDefault
#guard cfgOfId? cfgIdPlain == some cfgPlain
#guard cfgOfId? cfgIdBasic == some cfgBasic
#guard cfgOfId? cfgIdSat == some cfgSat
#guard cfgOfId? cfgIdUnsat == some cfgUnsat
#guard cfgOfId? 5#64 == none

/-! ## 2. Module Acyclicity, Codegen & 4-ISA Legalization `#guard`s -/

def closedCfgModule : LeanQbe.T.Module :=
  { fns := Float64.fns ++ Tiers.fns ++ Config.fns, externs := [], exits := [] }

#guard Config.fns.length == 17
#guard (Config.fns.map Fn.name).eraseDups.length == 17
#guard configModule.checkAcyclic == true
#guard configModule.exits.isEmpty
#guard closedCfgModule.checkAcyclic == true
#guard closedCfgModule.externs.isEmpty && closedCfgModule.exits.isEmpty
#guard (ppTModule configModule).isOk
#guard (PrintQbe.module configModule).isOk
#guard (ppTModule closedCfgModule).isOk
#guard match PrintQbe.module closedCfgModule with
  | .error msg =>
    msg == "PrintQbe: function $u64_mul128 returns 2 values; stock QBE supports at most 1"
  | .ok _ => false
#guard (ppModule (Config.fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (Config.fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (Config.fns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (Config.fns.map (Fn.legal .x64AVX512))).isOk
#guard Config.fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard Config.fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard Config.fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard Config.fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. `InterpKissat` C0 Runtime Preset Execution `#guard`s -/

private def cfgWorkBase : BitVec 64 := 0x10000#64
private def cfgHdrPtr : BitVec 64 := cfgWorkBase + BitVec.ofNat 64 fullM6ExtBytes

private def cfgInitMem : Mem 64 :=
  (List.replicate fullM6HdrTotalBytes (0 : UInt8)).At cfgWorkBase

private def runU64 (name : Sym) (as : List Ty) (args : Tup Val as) (m : Mem 64) :
    Option (BitVec 64 × Mem 64) :=
  match interpModule closedCfgModule 20000 name as [i64] args m with
  | .ok (v, ()) m' => some (v, m')
  | _ => none

private def runBool (name : Sym) (as : List Ty) (args : Tup Val as) (m : Mem 64) :
    Option (Bool × Mem 64) :=
  match interpModule closedCfgModule 20000 name as [.bool] args m with
  | .ok (b, ()) m' => some (b, m')
  | _ => none

private def runVoid1 (name : Sym) (m : Mem 64) : Option (Mem 64) :=
  match interpModule closedCfgModule 20000 name [i64] [] (cfgHdrPtr, ()) m with
  | .ok () m' => some m'
  | _ => none

private def checkState (m : Mem 64) (expMask expStable expTarget expRstInt : BitVec 64) : Bool :=
  let okMask := (runU64 "kissat_config_get" [i64] (cfgHdrPtr, ()) m).map Prod.fst == some expMask
  let okSt :=
    (runU64 "kissat_config_stable" [i64] (cfgHdrPtr, ()) m).map Prod.fst == some expStable
  let okTgt :=
    (runU64 "kissat_config_target" [i64] (cfgHdrPtr, ()) m).map Prod.fst == some expTarget
  let okRst :=
    (runU64 "kissat_config_restartint" [i64] (cfgHdrPtr, ()) m).map Prod.fst == some expRstInt
  let okFlags := (plain12DisabledFlags ++ basic3DisabledFlags).all fun fl =>
    let expected := (expMask &&& fl) != 0#64
    (runBool "kissat_config_flag" [i64, i64] (cfgHdrPtr, fl, ()) m).map Prod.fst == some expected
  okMask && okSt && okTgt && okRst && okFlags

#guard (runU64 "kissat_config_mask_default" [] () cfgInitMem).map Prod.fst == some cfgDefault
#guard (runU64 "kissat_config_mask_plain" [] () cfgInitMem).map Prod.fst == some cfgPlain
#guard (runU64 "kissat_config_mask_basic" [] () cfgInitMem).map Prod.fst == some cfgBasic
#guard (runU64 "kissat_config_mask_sat" [] () cfgInitMem).map Prod.fst == some cfgSat
#guard (runU64 "kissat_config_mask_unsat" [] () cfgInitMem).map Prod.fst == some cfgUnsat
#guard (runBool "kissat_config_has_id" [i64] (cfgIdUnsat, ()) cfgInitMem).map Prod.fst == some true
#guard (runBool "kissat_config_has_id" [i64] (5#64, ()) cfgInitMem).map Prod.fst == some false

private def testRuntimePresets : Bool :=
  match runVoid1 "m6_hdr_init" cfgInitMem with
  | none => false
  | some m0 =>
    let ok0 := checkState m0 cfgDefault 1#64 1#64 1#64
    match runVoid1 "kissat_config_plain" m0 with
    | none => false
    | some mPlain =>
      let okPlain := checkState mPlain cfgPlain 2#64 1#64 1#64
      match runVoid1 "kissat_config_basic" mPlain with
      | none => false
      | some mBasic =>
        let okBasic := checkState mBasic cfgBasic 2#64 1#64 1#64
        match runVoid1 "kissat_config_sat" mBasic with
        | none => false
        | some mSat =>
          let okSat := checkState mSat cfgSat 1#64 2#64 50#64
          match runVoid1 "kissat_config_unsat" mSat with
          | none => false
          | some mUnsat =>
            let okUnsat := checkState mUnsat cfgUnsat 0#64 1#64 1#64
            match runVoid1 "kissat_config_default" mUnsat with
            | none => false
            | some mDef =>
              let okDef := checkState mDef cfgDefault 1#64 1#64 1#64
              let okBad :=
                match runBool "kissat_set_configuration" [i64, i64] (cfgHdrPtr, 99#64, ()) mDef with
                | some (false, mKeep) => checkState mKeep cfgDefault 1#64 1#64 1#64
                | _ => false
              let okSet :=
                match runBool "kissat_set_configuration" [i64, i64]
                    (cfgHdrPtr, cfgIdPlain, ()) mDef with
                | some (true, mPlain2) => checkState mPlain2 cfgPlain 2#64 1#64 1#64
                | _ => false
              ok0 && okPlain && okBasic && okSat && okUnsat && okDef && okBad && okSet

#guard testRuntimePresets

/-! ## 4. Headline Theorems & Single-Line `#print axioms` (`<= std3`, `< 115c`) -/

theorem cfg_fns_wf : ∀ f ∈ Config.fns, f.Wf := Config.fns_wf

theorem cfg_mod_acyclic : configModule.checkAcyclic = true := configModule_checkAcyclic

theorem cfg_closed_acyclic : closedCfgModule.checkAcyclic = true := by rfl

theorem cfg_closed_wf : ∀ f ∈ closedCfgModule.fns, f.Wf := by
  intro f hf
  rcases List.mem_append.mp hf with hft | hc
  · rcases List.mem_append.mp hft with h64 | ht
    · exact Float64.fns_wf f h64
    · exact Tiers.fns_wf f ht
  · exact Config.fns_wf f hc

end LeanQbeTest.T.KissatConfigTest

abbrev kcfg_fns_wf := @LeanQbeTest.T.KissatConfigTest.cfg_fns_wf
abbrev kcfg_mod_acyc := @LeanQbeTest.T.KissatConfigTest.cfg_mod_acyclic
abbrev kcfg_cls_acyc := @LeanQbeTest.T.KissatConfigTest.cfg_closed_acyclic
abbrev kcfg_cls_wf := @LeanQbeTest.T.KissatConfigTest.cfg_closed_wf
abbrev kcfg_get_wf := @LeanQbe.T.Examples.Kissat.Src.Config.kissat_config_get_wf
abbrev kcfg_flag_wf := @LeanQbe.T.Examples.Kissat.Src.Config.kissat_config_flag_wf
abbrev kcfg_def_wf := @LeanQbe.T.Examples.Kissat.Src.Config.kissat_config_default_wf
abbrev kcfg_pln_wf := @LeanQbe.T.Examples.Kissat.Src.Config.kissat_config_plain_wf
abbrev kcfg_bsc_wf := @LeanQbe.T.Examples.Kissat.Src.Config.kissat_config_basic_wf
abbrev kcfg_sat_wf := @LeanQbe.T.Examples.Kissat.Src.Config.kissat_config_sat_wf
abbrev kcfg_uns_wf := @LeanQbe.T.Examples.Kissat.Src.Config.kissat_config_unsat_wf
abbrev kcfg_set_wf := @LeanQbe.T.Examples.Kissat.Src.Config.kissat_set_configuration_wf

#print axioms kcfg_fns_wf
#print axioms kcfg_mod_acyc
#print axioms kcfg_cls_acyc
#print axioms kcfg_cls_wf
#print axioms kcfg_get_wf
#print axioms kcfg_flag_wf
#print axioms kcfg_def_wf
#print axioms kcfg_pln_wf
#print axioms kcfg_bsc_wf
#print axioms kcfg_sat_wf
#print axioms kcfg_uns_wf
#print axioms kcfg_set_wf
