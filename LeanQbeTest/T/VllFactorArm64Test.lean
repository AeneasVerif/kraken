module

public import LeanQbe.T.Arm64.VllFactorArm64
public import LeanQbe.T.Spill
import LeanQbe.T.Unified.DriverLemmas
meta import Lean
meta import LeanQbe.T.Arm64.VllFactorArm640
meta import LeanQbe.T.Arm64.VllFactorArm641
meta import LeanQbe.T.Arm64.VllFactorArm642
meta import LeanQbe.T.Arm64.VllFactorArm64
meta import LeanQbe.T.Spill
meta import LeanQbe.T.Main
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly

/-!
# Verification Suite for AArch64 `BedrockMach` Factoring (`VllFactorArm64Test`)

Verifies:
1. Concrete multi-function unit suite exercising core `Instr arm64Arch` emission (ALU, negated
   immediates, shifts, `zext`/`sext`/`trunc`, `cmp`, `setcc`, `load`/`store`, `loadSext`, loops,
   stack slots, ABI calls, callee-saved `STP`/`LDP`), confirming `0` directive diff against
   `armTarget` and direct `Unified.Factoring` / `vllArmStrict_to_armTarget_fnSpec` instantiation.
2. Full `413/413` `FullM7Fidelity` (`m7FidelityFns`) byte/directive-exact parity between
   `armTarget` and `asmArm64List ∘ vllArmStrictTarget` (both per-function and whole-module
   `compile`), plus `vllArmTarget` parity and core vs `.native` instruction breakdown.
3. `#print axioms` on all headline factoring & soundness theorems.
4. MetaM `importModules` isolation (`0` `Amd64`/`Kraken.X64` transitive imports), kernel
   `Lean.collectAxioms` (`⊆ [propext, Classical.choice, Quot.sound]`), and `ci.isUnsafe` audit.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.VllFactorArm64Test

open LeanQbe.T
open LeanQbe.T.Arm64
open LeanQbe.T.Vll

/-! ## 1. Concrete Multi-Function Unit Suite & Kernel Factoring Witnesses -/

/-- Leaf scalar arithmetic, negated immediate, shifts, conversions, and `i8` load/store. -/
@[expose] def fnArithMem : Fn := ⟨"arithMem", [i64, i64, i32], [i64], fun _ _ (p, x, y, ()) =>
  .load i8 (.var p) fun b =>
  .let_ (op1 (.zext 8 32) (.var b)) fun (bz, ()) =>
  .let_ (op2 (.add i32) (.var bz) (.var y)) fun (s32, ()) =>
  .let_ (op1 (.sext 32 64) (.var s32)) fun (s64, ()) =>
  .let_ (op2 (.add i64) (.var s64) (.imm (-7#64))) fun (ad, ()) =>
  .let_ (op2 (.xor i64) (.var ad) (.var x)) fun (xr, ()) =>
  .let_ (op2 (.shl i64) (.var xr) (.imm 1)) fun (sh, ()) =>
  .let_ (op1 (.trunc 64 8) (.var sh)) fun (lo, ()) =>
  .store (.var lo) (.var p) (
  .let_ (op1 (.neg i64) (.var sh)) fun (ng, ()) =>
  .ret (.var ng, ()))⟩

/-- Diamond branch with `cmp ult`, `ofBool`, boolean `not`, and parameterized join block. -/
@[expose] def fnDiamond : Fn := ⟨"diamond", [i64, i64], [i64], fun _ _ (a, b, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) =>
      .let_ (op2 (.add i64) (.var r) (.imm 1)) fun (r1, ()) => .ret (.var r1, ())) .nil)
    (fun (join, ()) =>
      .let_ (op2 (.ult i64) (.var a) (.var b)) fun (c, ()) =>
      .let_ (op1 (.not .bool) (.var c)) fun (nc, ()) =>
      .let_ (op1 (.ofBool 64) (.var nc)) fun (bi, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.sub i64) (.var b) (.var a)) fun (d, ()) =>
          .let_ (op2 (.add i64) (.var d) (.var bi)) fun (d1, ()) => .jump join (.var d1, ()))
        (.let_ (op2 (.sub i64) (.var a) (.var b)) fun (d, ()) =>
          .let_ (op2 (.add i64) (.var d) (.var bi)) fun (d1, ()) => .jump join (.var d1, ())))⟩

/-- Sign-extending `i8` load (`loadSext` fusion candidate). -/
@[expose] def fnLoadSext : Fn := ⟨"loadSext8", [i64], [i64], fun _ _ (p, ()) =>
  .load i8 (.var p) fun b =>
  .let_ (op1 (.sext 8 64) (.var b)) fun (s, ()) =>
  .ret (.var s, ())⟩

/-- Multi-block triangular sum loop exercising flags, back-edge, and live registers. -/
@[expose] def fnTriSum : Fn := ⟨"triSum", [i64], [i64], fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
      .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
      .let_ (op2 (.ugt i64) (.var i') (.imm 0)) fun (cont, ()) =>
      .jnz (.var cont) (.jump loop (.var i', .var acc', ())) (.ret (.var acc', ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))⟩

/-- Simple leaf helper for multi-call frame/callee-saved testing. -/
@[expose] def fnLeafAdd : Fn := ⟨"leafAdd", [i64, i64], [i64], fun _ _ (a, b, ()) =>
  .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) =>
  .let_ (op2 (.xor i64) (.var s) (.imm 3)) fun (r, ()) =>
  .ret (.var r, ())⟩

/-- Multi-call caller exercising stack slots, ABI calls, and callee-saved `STP`/`LDP`. -/
@[expose] def fnCallerSlots : Fn := ⟨"callerSlots", [i64, i64, i64, i64], [i64],
  fun _ _ (a, b, c, d, ()) =>
  .call (as := [i64, i64]) (bs := [i64]) "leafAdd" (.var a, .var b, ()) fun (r1, ()) =>
  .call (as := [i64, i64]) (bs := [i64]) "leafAdd" (.var c, .var d, ()) fun (r2, ()) =>
  .let_ (op2 (.add i64) (.var r1) (.var r2)) fun (s1, ()) =>
  .let_ (op2 (.add i64) (.var s1) (.var a)) fun (s2, ()) =>
  .let_ (op2 (.add i64) (.var s2) (.var b)) fun (s3, ()) =>
  .let_ (op2 (.add i64) (.var s3) (.var c)) fun (s4, ()) =>
  .let_ (op2 (.add i64) (.var s4) (.var d)) fun (s5, ()) =>
  .ret (.var s5, ())⟩

@[expose] def unitSuite : List Fn :=
  [fnArithMem, fnDiamond, fnLoadSext, fnTriSum, fnLeafAdd, fnCallerSlots]

/-- Direct `Unified.Factoring (Fin 6) Directive (Instr arm64Arch)` witness over `unitSuite`. -/
@[expose] def unitFactoring :
    Unified.Factoring (Fin unitSuite.length) _root_.Directive (Instr arm64Arch) :=
  arm64FactoringAutoList unitSuite

/-- Direct `Unified.Factoring.same_bytes` instantiation on `unitFactoring`. -/
theorem unitSuite_same_bytes (i : Fin unitSuite.length) (is : List (Instr arm64Arch))
    (h : unitFactoring.vll i = .ok is) :
    unitFactoring.direct i = .ok (asmArm64List is) :=
  unitFactoring.same_bytes i is h

/-- Concrete specialization of `vllArmStrict_to_armTarget_fnSpec` on `fnLeafAdd`. -/
theorem fnLeafAdd_fnSpec_bridge (host : Host) (hints : armIsa.Hints) (E : Rega.Ext)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat) {code : List (Instr arm64Arch)} {k₀ : Nat}
    (hf : fnLeafAdd.Wf) (hl : Rega.lowerFn vllArmStrictTarget.toIsa hints E fnLeafAdd = .ok code)
    (hc : (asmArm64List code).IsInfixAt (armMach.prog host) k₀)
    (hu : armTarget.LabelsUnique host)
    (hfr : Rega.effFrame armTarget.toIsa hints E ≤ n)
    (hn : n + 0 ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      armTarget.FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.effFrame armTarget.toIsa hints E + 0 + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → armTarget.Defined host g ∧ nX ≤ n) :
    armTarget.FnSpec host fnLeafAdd.name (Func.spec Γ fnLeafAdd.body) n nX :=
  vllArmStrict_to_armTarget_fnSpec host hints E fnLeafAdd Γ n nX bound hf hl hc hu hfr hn hcal hex

/-! ## 2. Executable Parity & `413/413` `FullM7Fidelity` Byte-Exact Checks -/

meta section

open LeanQbe.T.Examples.Kissat.FullM7Fidelity

private def isNativeInstr : Instr arm64Arch → Bool
  | .native _ => true
  | _ => false

private def isCoreAlu : Instr arm64Arch → Bool
  | .alu .. => true
  | _ => false

private def isCoreCtrl : Instr arm64Arch → Bool
  | .jmp _ | .jcc .. | .call _ | .ret | .label _ => true
  | _ => false

private def isCoreFrame : Instr arm64Arch → Bool
  | .prologue _ | .epilogue _ | .slotLd .. | .slotSt .. => true
  | _ => false

private def isCoreMem : Instr arm64Arch → Bool
  | .load .. | .store .. => true
  | _ => false

private def checkUnitFn (f : Fn) : Bool :=
  let mf := f.mid armLegalTarget
  let hArm := Spill.hints armIsa mf
  let hStrict := Spill.hints vllArmStrictTarget.toIsa mf
  let hVll := Spill.hints vllArmTarget.toIsa mf
  match compileFn armTarget.toIsa armLegalTarget hArm f,
        compileFn vllArmStrictTarget.toIsa armLegalTarget hArm f,
        compileFn vllArmStrictTarget.toIsa armLegalTarget hStrict f,
        compileFn vllArmTarget.toIsa armLegalTarget hVll f with
  | .ok dsArm, .ok isS, .ok isSOwn, .ok isV =>
    asmArm64List isS == dsArm && asmArm64List isSOwn == dsArm && asmArm64List isV == dsArm
  | _, _, _, _ => false

#guard unitSuite.all checkUnitFn

#guard
  let hs := unitSuite.map fun f => Spill.hints armIsa (f.mid armLegalTarget)
  match compile armTarget.toIsa armLegalTarget unitSuite hs,
        compile vllArmStrictTarget.toIsa armLegalTarget unitSuite hs with
  | .ok dsArm, .ok isS => asmArm64List isS == dsArm
  | _, _ => false

#guard
  let hs := unitSuite.map fun f => Spill.hints armIsa (f.mid armLegalTarget)
  match compile vllArmStrictTarget.toIsa armLegalTarget unitSuite hs with
  | .ok isS =>
    isS.any isCoreAlu && isS.any isCoreCtrl && isS.any isCoreFrame && isS.any isCoreMem
  | .error _ => false

/-- Direct `Unified.Factoring (Fin 413) Directive (Instr arm64Arch)` witness for all `413`
`FullM7Fidelity` functions. -/
private def m7FidFactoring :
    Unified.Factoring (Fin m7FidelityFns.length) _root_.Directive (Instr arm64Arch) :=
  arm64FactoringAutoList m7FidelityFns

#guard m7FidelityFns.length == 413

#guard
  if h : 0 < m7FidelityFns.length then
    match m7FidFactoring.direct ⟨0, h⟩, m7FidFactoring.vll ⟨0, h⟩ with
    | .ok ds, .ok is => asmArm64List is == ds
    | _, _ => false
  else false

#eval show IO Unit from do
  let fns := m7FidelityFns
  if fns.length != 413 then
    throw <| IO.userError s!"expected 413 FullM7Fidelity fns, got {fns.length}"
  let mut strictOk : Nat := 0
  let mut vllOk : Nat := 0
  let mut totalVllInstrs : Nat := 0
  let mut coreInstrs : Nat := 0
  let mut nativeInstrs : Nat := 0
  let mut totalDirs : Nat := 0
  for f in fns do
    let mf := f.mid armLegalTarget
    let ext := mf.ext
    let hArm := Spill.hints armIsa mf
    let hVll := Spill.hints vllArmTarget.toIsa mf
    let rArm := Rega.lowerFn armTarget.toIsa hArm ext mf
    let rStrict := Rega.lowerFn vllArmStrictTarget.toIsa hArm ext mf
    let rVll := Rega.lowerFn vllArmTarget.toIsa hVll ext mf
    match rArm, rStrict, rVll with
    | .ok dsArm, .ok isS, .ok isV =>
      if asmArm64List isS != dsArm then
        throw <| IO.userError s!"vllArmStrictTarget directive diff in {f.name}"
      if asmArm64List isV != dsArm then
        throw <| IO.userError s!"vllArmTarget directive diff in {f.name}"
      strictOk := strictOk + 1
      vllOk := vllOk + 1
      totalDirs := totalDirs + dsArm.length
      totalVllInstrs := totalVllInstrs + isS.length
      let nNat := (isS.filter isNativeInstr).length
      nativeInstrs := nativeInstrs + nNat
      coreInstrs := coreInstrs + (isS.length - nNat)
    | .error e, _, _ => throw <| IO.userError s!"armTarget failed on {f.name}: {e}"
    | _, .error e, _ => throw <| IO.userError s!"vllArmStrictTarget failed on {f.name}: {e}"
    | _, _, .error e => throw <| IO.userError s!"vllArmTarget failed on {f.name}: {e}"
  if strictOk != 413 || vllOk != 413 then
    throw <| IO.userError s!"parity mismatch: strict={strictOk}/413, vllArmTarget={vllOk}/413"
  let corePct := (coreInstrs * 1000) / totalVllInstrs
  let natPct := (nativeInstrs * 1000) / totalVllInstrs
  IO.println <|
    s!"FullM7Fidelity Arm64 parity: strict={strictOk}/413, vllArmTarget={vllOk}/413 " ++
    s!"(0 directive diff across {totalDirs} directives)"
  IO.println <|
    s!"VLL Instr stats: total={totalVllInstrs}, core={coreInstrs} " ++
    s!"({corePct / 10}.{corePct % 10}%), native={nativeInstrs} " ++
    s!"({natPct / 10}.{natPct % 10}%)"

end

/-! ## 3. `#print axioms` Checks (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Arm64.vllArmNativeHooks
#print axioms LeanQbe.T.Arm64.vllArmPolicySpec
#print axioms LeanQbe.T.Arm64.vllArmPolicy
#print axioms LeanQbe.T.Arm64.vllArmTarget
#print axioms LeanQbe.T.Arm64.vllArmStrictTarget
#print axioms LeanQbe.T.Arm64.vllArmHooksNoLab
#print axioms LeanQbe.T.Arm64.vllArmLabelClean
#print axioms LeanQbe.T.Arm64.vllArmStrictLabelClean
#print axioms LeanQbe.T.Arm64.vllArmStrict_lowerFn_factor
#print axioms LeanQbe.T.Arm64.vllArmStrict_compileFn_factor
#print axioms LeanQbe.T.Arm64.vllArmStrict_compile_factor
#print axioms LeanQbe.T.Arm64.vllArmStrict_compileModule_factor
#print axioms LeanQbe.T.Arm64.arm64Factoring
#print axioms LeanQbe.T.Arm64.arm64LowerFactoring
#print axioms LeanQbe.T.Arm64.arm64FactoringAuto
#print axioms LeanQbe.T.Arm64.arm64FactoringOn
#print axioms LeanQbe.T.Arm64.arm64LowerFactoringOn
#print axioms LeanQbe.T.Arm64.arm64FactoringList
#print axioms LeanQbe.T.Arm64.arm64FactoringAutoList
#print axioms LeanQbe.T.Arm64.vllArmTarget_lowerFn_correct
#print axioms LeanQbe.T.Arm64.vllArmStrict_lowerFn_correct
#print axioms LeanQbe.T.Arm64.vllArmStrict_to_armTarget_fnSpec
#print axioms LeanQbe.T.Arm64.vllArmStrict_transport_cert
#print axioms LeanQbe.T.Arm64.vllArmStrict_same_bytes
#print axioms LeanQbeTest.T.VllFactorArm64Test.unitSuite_same_bytes
#print axioms LeanQbeTest.T.VllFactorArm64Test.fnLeafAdd_fnSpec_bridge

/-! ## 4. MetaM `importModules` Isolation, `collectAxioms`, and `ci.isUnsafe` Audit -/

meta section
open Lean

private def allowedStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
private def isForbiddenX64Mod (m : Name) : Bool :=
  (m.toString.splitOn "Amd64").length > 1 || m.toString.startsWith "Kraken.X64"

#eval show MetaM Unit from do
  for modName in [`LeanQbe.T.Arm64.VllFactorArm640, `LeanQbe.T.Arm64.VllFactorArm641,
      `LeanQbe.T.Arm64.VllFactorArm642, `LeanQbe.T.Arm64.VllFactorArm64] do
    let env ← importModules #[{ module := modName }] {}
    let bad := env.header.moduleNames.filter isForbiddenX64Mod
    if !bad.isEmpty then throwError "{modName} imports Amd64/X64: {bad.toList}"
  let testBad := (← getEnv).header.moduleNames.filter isForbiddenX64Mod
  if !testBad.isEmpty then throwError "VllFactorArm64Test imports Amd64/X64: {testBad.toList}"
  let env ← getEnv
  let targets : List Name :=
    [ ``LeanQbe.T.Arm64.vllArmNativeHooks
    , ``LeanQbe.T.Arm64.vllArmPolicySpec
    , ``LeanQbe.T.Arm64.vllArmPolicy
    , ``LeanQbe.T.Arm64.vllArmTarget
    , ``LeanQbe.T.Arm64.vllArmStrictTarget
    , ``LeanQbe.T.Arm64.vllArmHooksNoLab
    , ``LeanQbe.T.Arm64.vllArmLabelClean
    , ``LeanQbe.T.Arm64.vllArmStrictLabelClean
    , ``LeanQbe.T.Arm64.vllArmStrict_lowerFn_factor
    , ``LeanQbe.T.Arm64.vllArmStrict_compileFn_factor
    , ``LeanQbe.T.Arm64.vllArmStrict_compile_factor
    , ``LeanQbe.T.Arm64.vllArmStrict_compileModule_factor
    , ``LeanQbe.T.Arm64.arm64Factoring
    , ``LeanQbe.T.Arm64.arm64LowerFactoring
    , ``LeanQbe.T.Arm64.arm64FactoringAuto
    , ``LeanQbe.T.Arm64.arm64FactoringOn
    , ``LeanQbe.T.Arm64.arm64LowerFactoringOn
    , ``LeanQbe.T.Arm64.arm64FactoringList
    , ``LeanQbe.T.Arm64.arm64FactoringAutoList
    , ``LeanQbe.T.Arm64.vllArmTarget_lowerFn_correct
    , ``LeanQbe.T.Arm64.vllArmStrict_lowerFn_correct
    , ``LeanQbe.T.Arm64.vllArmStrict_to_armTarget_fnSpec
    , ``LeanQbe.T.Arm64.vllArmStrict_transport_cert
    , ``LeanQbe.T.Arm64.vllArmStrict_same_bytes
    , ``LeanQbeTest.T.VllFactorArm64Test.unitSuite_same_bytes
    , ``LeanQbeTest.T.VllFactorArm64Test.fnLeafAdd_fnSpec_bridge ]
  for nm in targets do
    let axs ← Lean.collectAxioms nm
    let badAx := axs.filter fun a => !allowedStdAxioms.contains a
    if !badAx.isEmpty then throwError "Disallowed axioms for {nm}: {badAx.toList}"
    match env.find? nm with
    | some ci => if ci.isUnsafe then throwError "Declaration {nm} failed isUnsafe check"
    | none => throwError "Declaration {nm} not found"
  let mut checkedAll : Nat := 0
  for modName in [`LeanQbe.T.Arm64.VllFactorArm640, `LeanQbe.T.Arm64.VllFactorArm641,
      `LeanQbe.T.Arm64.VllFactorArm642, `LeanQbe.T.Arm64.VllFactorArm64] do
    let some idx := env.getModuleIdx? modName
      | throwError "Module {modName} not found in environment"
    let modData := env.header.moduleData[idx.toNat]!
    for nm in modData.constNames do
      if let some ci := env.find? nm then
        let axs ← Lean.collectAxioms nm
        let badAx := axs.filter fun a => !allowedStdAxioms.contains a
        if !badAx.isEmpty then throwError "Disallowed axioms for {nm}: {badAx.toList}"
        if ci.isUnsafe then throwError "Declaration {nm} failed isUnsafe check"
        checkedAll := checkedAll + 1
  IO.println s!"Kernel audit PASS: targets={targets.length}, allModConsts={checkedAll}, x64Leaks=0"

end

end LeanQbeTest.T.VllFactorArm64Test
