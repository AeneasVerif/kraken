module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.Lower1
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbe.T.LeanLCNF.Lower

/-!
# Shard `F1` Arm64 `LinkedCert.weakenNoExit` Test (`LcnfC0ExternF1Arm64Test`)

AAPCS64 Arm64 companion to `LcnfC0ExternF1Test`: verifies zero-recompilation
`LinkedCert.weakenNoExit`, `LinkedCert.weakenExits`, definitional `code`/`bounds` preservation,
`LinkedCert.append` composition with `rtExitSyms` (`nX = 64`), `defined_exit_host`, and negative
exit-check rejection on `armTarget` (`<= std3` axioms, zero `Amd64`/`Kraken.X64` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0ExternF1Arm64Test

open LeanQbe.T
open LeanQbe.T.Arm64
open LeanQbe.T.LeanLCNF

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let bad := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !bad.isEmpty then
    throwError "LcnfC0ExternF1Arm64Test leaked Amd64 imports: {bad.toList}"

/-- Pure leaf function (`f1_leaf x = x + 7`), zero exits. -/
@[expose] def fnF1LeafArm : Fn :=
  ⟨"f1_leaf", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.add i64, (.var x, .imm 7#64, ())⟩ fun (r, ()) =>
    .ret (.var r, ())⟩

/-- Pure caller (`f1_callee x = f1_leaf(x) + 1`), zero exits. -/
@[expose] def fnF1CalleeArm : Fn :=
  ⟨"f1_callee", [i64], [i64], fun _ _ (x, ()) =>
    .call "f1_leaf" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
    .let_ ⟨.add i64, (.var y, .imm 1#64, ())⟩ fun (r, ()) =>
    .ret (.var r, ())⟩

/-- Exit-capable caller calling `.exit "lcnf_panic"` on `x = 0` else `f1_callee x`. -/
@[expose] def fnF1CheckedArm : Fn :=
  ⟨"f1_checked", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.cmp .eq i64, (.var x, .imm 0#64, ())⟩ fun (b, ()) =>
    .jnz (.var b)
      (.exit (as := [i64, i64]) "lcnf_panic" (.imm 0#64, .imm 1#64, ()))
      (.call "f1_callee" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
        .ret (.var y, ()))⟩

@[expose] def noExitModArm : Module :=
  { fns := [fnF1LeafArm, fnF1CalleeArm], externs := [], exits := [] }

@[expose] def exitRtModArm : Module :=
  { fns := [fnF1CheckedArm]
    externs := [{ name := "f1_callee", as := [i64], rs := [i64] }]
    exits := rtExitSyms }

@[expose] def fullF1ModArm : Module :=
  { fns := noExitModArm.fns ++ exitRtModArm.fns, externs := [], exits := rtExitSyms }

compile_linked_chunks! armNoExitCert
  armTarget armLayout armLegalTarget armLabelClean noExitModArm 1
  (compileExt := true)

compile_linked_chunks! armExitCert
  armTarget armLayout armLegalTarget armLabelClean exitRtModArm 1
  (ext := armNoExitCert.exportedExt) (exits := rtExitSyms) (nX := 64)

/-- Lift zero-exit `armNoExitCert` to `exits = rtExitSyms`, `nX = 64` with zero recompilation. -/
@[expose] noncomputable def armWeakCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      noExitModArm [] rtExitSyms 64 2048 :=
  armNoExitCert.weakenNoExit rtExitSyms 64 (by t_kernel_rfl) (by t_kernel_rfl)

theorem armWeakCert_numChunks : armWeakCert.numChunks = armNoExitCert.numChunks :=
  rfl

theorem armWeakCert_bounds : armWeakCert.bounds = armNoExitCert.bounds :=
  armNoExitCert.weakenNoExit_bounds rtExitSyms 64 (by t_kernel_rfl) (by t_kernel_rfl)

theorem armWeakCert_code0 :
    (armWeakCert.chunks[0]'(by decide)).compiled.code =
      (armNoExitCert.chunks[0]'(by decide)).compiled.code :=
  rfl

theorem armWeakCert_defined_panic :
    armTarget.Defined armWeakCert.host "lcnf_panic" :=
  armWeakCert.defined_exit_host (by simp [rtExitSyms])

@[expose] noncomputable def armComposedCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      fullF1ModArm [] rtExitSyms 64 2048 :=
  armWeakCert.append armExitCert rfl (by t_kernel_rfl)

theorem armComposedCert_bounds_len : armComposedCert.bounds.length = 3 := by
  rw [armComposedCert.bounds_length, armComposedCert.fns_eq]
  decide

@[expose] noncomputable def armExtraExitCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      noExitModArm [] (rtExitSyms ++ ["f1_extra_arm"]) 64 2048 :=
  armWeakCert.weakenExits (rtExitSyms ++ ["f1_extra_arm"])
    (fun _ hs => List.mem_append_left _ hs) (by t_kernel_rfl) (by t_kernel_rfl)

theorem armExtraExitCert_defined :
    armTarget.Defined armExtraExitCert.host "f1_extra_arm" :=
  armExtraExitCert.defined_exit_host (by simp [rtExitSyms])

theorem weakenCheck_rejects_dup_fn_arm :
    checkWeakenExitsChunks armLayout ["f1_leaf"] armNoExitCert.chunks = false := by
  t_kernel_rfl

/--
info: 'LeanQbeTest.T.LcnfC0ExternF1Arm64Test.armWeakCert' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms armWeakCert

/--
info: 'LeanQbeTest.T.LcnfC0ExternF1Arm64Test.armComposedCert' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms armComposedCert

end LeanQbeTest.T.LcnfC0ExternF1Arm64Test
