module

import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof
meta import Lean
meta import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
meta import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof

/-!
# Target-Generic Verification Suite for `FactLoop` (`LcnfC0LoopDemo`)

1. Architecture-isolation `#eval` audit (zero `Kraken.X64` / `Kraken.AArch64` / `LeanQbe.T.Amd64` /
   `LeanQbe.T.Arm64` imports).
2. Kernel `#guard` checks on `factLoopTfs`, `factLoopProgMod`, `factLoopLinkedMod`,
   `FactLoop.factAcc 25 1`, and `fact25Bytes`.
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LcnfC0LoopDemoTest

open LeanQbe.T LeanQbe.T.LeanLCNF

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let arch := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "Kraken.AArch64" ||
      s.startsWith "LeanQbe.T.Amd64" || s.startsWith "LeanQbe.T.Arm64"
  if !arch.isEmpty then
    throwError "LcnfC0LoopDemoTest leaked arch imports: {arch.toList}"

#guard factLoopProgMod.fns.length == 2
#guard factLoopProgMod.externs.isEmpty
#guard factLoopProgMod.exits == rtExitSyms
#guard factLoopLinkedMod.fns.length == 82
#guard factLoopLinkedMod.externs.isEmpty
#guard factLoopLinkedMod.exits == rtExitSyms
#guard factLoopLinkedMod.checkAcyclic
#guard FactLoop.factAcc 25 1 == 15511210043330985984000000
#guard fact25Bytes.length == 26
#guard fact25Bytes ==
  "15511210043330985984000000".toList.map (fun c => UInt8.ofNat c.toNat)

#print axioms fact25_acc_eq
#print axioms fact25Bytes_len
#print axioms fact25Bytes_eq_ascii
#print axioms fact25_dec
#print axioms lcnf_nat_alloc_rem_wp
#print axioms bn_nat_from_limbs_rem_wp
#print axioms lcnf_nat_mul_arith_wp
#print axioms lcnf_nat_mul_slow_wp
#print axioms lcnf_nat_to_str_two_limb_wp
#print axioms rtC0CoreMod_loop_wp
#print axioms rtC0CoreMod_loopModuleOk
#print axioms factAcc_wp
#print axioms factStr_wp
#print axioms factLoopLinkedMod_wp
#print axioms factLoopLinkedMod_fns_wf
#print axioms factLoopLinkedMod_acyclic
#print axioms factLoopLinkedMod_moduleOk
#print axioms factLoopEnv_noex
#print axioms loopRtMem_ok
#print axioms fact25_str_spec

end LeanQbeTest.T.LcnfC0LoopDemoTest
