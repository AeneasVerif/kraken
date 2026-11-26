module

public import LeanQbe.T.Arm64.LcnfC0ArrayDemoCertArm64
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemo

/-!
# Verification Suite for AAPCS64 AArch64 R2 Container Demo (`LcnfC0ArrayDemoCertArm64`)

1. Architecture-isolation `#eval` audit (`0` `Kraken.X64` / `LeanQbe.T.Amd64` imports).
2. Structural guards verifying acyclic `89`-fn `0`-extern linking onto `rtC0CoreMod`, R2
   container callee coverage (`lcnf_array_{mk_empty,push,set,get}`,
   `lcnf_ba_{mk_empty,push,set,get}`, `lcnf_dec_ref_cold`), and exact stack bounds `≤ 2048`.
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0ArrayDemoArm64Test

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let x64 := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64.isEmpty then
    throwError "LcnfC0ArrayDemoArm64Test leaked X64/Amd64 imports: {x64.toList}"

#guard arrayDemoLcMod.decls.length == 3
#guard arrayDemoTfs.length == 3
#guard arrayDemoLinkedMod.fns.length == 89
#guard arrayDemoLinkedMod.externs.isEmpty
#guard arrayDemoLinkedMod.exits == ["lcnf_panic"]
#guard arrayDemoLinkedMod.checkAcyclic
#guard checkLegalSigAll armLegalTarget arrayDemoProgMod.fns
#guard arrayDemoTfs.tf_0.toFn.callees.any (fun s => s.1 == "lcnf_array_mk_empty")
#guard arrayDemoTfs.tf_0.toFn.callees.any (fun s => s.1 == "lcnf_array_push")
#guard arrayDemoTfs.tf_0.toFn.callees.any (fun s => s.1 == "lcnf_array_set")
#guard arrayDemoTfs.tf_0.toFn.callees.any (fun s => s.1 == "lcnf_array_get")
#guard arrayDemoTfs.tf_0.toFn.callees.any (fun s => s.1 == "lcnf_dec_ref_cold")
#guard arrayDemoTfs.tf_1.toFn.callees.any (fun s => s.1 == "lcnf_ba_mk_empty")
#guard arrayDemoTfs.tf_1.toFn.callees.any (fun s => s.1 == "lcnf_ba_push")
#guard arrayDemoTfs.tf_1.toFn.callees.any (fun s => s.1 == "lcnf_ba_set")
#guard arrayDemoTfs.tf_1.toFn.callees.any (fun s => s.1 == "lcnf_ba_get")
#guard arrayDemoTfs.tf_2.toFn.callees.any (fun s => s.1 == "lcnf_ba_set")
#guard arrayDemoTfs.tf_2.toFn.callees.any (fun s => s.1 == "lcnf_ba_get")
#guard ArrayDemo.arrayPushSetGet 10 20 42 == 62
#guard ArrayDemo.baPushSetGet 4 10 20 42 == 62
#guard ArrayDemo.baCowSetGet (ByteArray.mk #[10, 20]) 42 == 62
example : boxNat 62 = 125#64 := rfl

#print axioms LeanQbe.T.LeanLCNF.arrayDemoLinkedMod_moduleOk
#print axioms LeanQbe.T.Arm64.arrayDemoArm64ProgCert
#print axioms LeanQbe.T.Arm64.arrayDemoArm64Cert
#print axioms LeanQbe.T.Arm64.arrayDemoArm64Cert_bounds_len
#print axioms LeanQbe.T.Arm64.arrayDemoArm64Cert_bounds_le
#print axioms LeanQbe.T.Arm64.arrayDemoArm64_arrayPushSetGet_fnSpec
#print axioms LeanQbe.T.Arm64.arrayDemoArm64_baPushSetGet_fnSpec
#print axioms LeanQbe.T.Arm64.arrayDemoArm64_baCowSetGet_fnSpec
#print axioms LeanQbe.T.Arm64.arrayDemoArm64_arrayPushSetGet_run
#print axioms LeanQbe.T.Arm64.arrayDemoArm64_baPushSetGet_run
#print axioms LeanQbe.T.Arm64.arrayDemoArm64_baCowSetGet_shared_run

end LeanQbeTest.T.LcnfC0ArrayDemoArm64Test
