/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.LeanLCNF.LcnfC0FfiPilotProof
public import LeanQbe.T.Arm64.KissatPlainCert
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.KissatPlainBounds
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
public meta import LeanQbe.T.LeanLCNF.LcnfC0FfiPilotProof2

/-!
# Shard `F3` AAPCS64 Arm64 Linked Certificate & Machine `Eventually` Witnesses

Zero-recompilation composition of the `171`-function closed AAPCS64 Arm64 binary:
1. `KissatPlainCert.plainCert.weakenNoExit rtExitSyms 64` (`59` Kissat fns, **FIRST** so
   `extListBeq` fast path hits without recompiling Kissat).
2. `.append rtC0CoreArm64Cert` (`86` pure-C0 runtime fns, zero recompilation).
3. `.append pilotTailArm64Cert` (`26` fns: `ffiMod` + C0 pilot wrappers + `5` lowered Lean callers,
   compiled in `3` acyclic chunks via `compile_linked_chunks!`).

Exports `armTarget.Defined` + `armTarget.FnSpec` for all `5` pilot callers and closed machine-level
`Eventually (armTarget.mach.step pilotArm64Cert.host)` non-vacuity witnesses (`XPost := False`,
`<= std3`) over `nvPilotSlab` (`< 64 KiB` @ `0x1000#64`) covering UNSAT (`20#64`), SAT (`10#64`),
tagged scalar `Nat` (`0#64`), zero-copy `MPZ` `Nat` (`20#64`), OOM (`3#64`), `xorBA`/`xorNat` ok &
OOM (`5#64`), and round-trip `solveXorBA` (`0` leaks).
-/

set_option autoImplicit false

namespace LeanQbe.T.Arm64

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain

public section

/-! ## 1. Zero-Recompilation Cert Composition (`59 + 86 + 26 = 171` fns) -/

/-- `59`-function `Kissat.Plain` Arm64 cert weakened with `rtExitSyms` (`64` exit syms), keeping
all existing compiled chunks intact without recompiling Kissat. -/
@[expose] noncomputable def pilotPlainWeakArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      plainModule [] rtExitSyms 64 2048 :=
  KissatPlainCert.plainCert.weakenNoExit rtExitSyms 64 (by t_kernel_rfl) (by t_kernel_rfl)

/-- Combined `145`-function Kissat + `rtC0Core` Arm64 module (`plainModule ++ rtC0CoreMod`). -/
@[expose] def pilotPlainRtModArm64 : Module :=
  { fns := plainModule.fns ++ rtC0CoreMod.fns, externs := [] }

/-- Zero-recompilation `145`-function Arm64 cert putting `pilotPlainWeakArm64Cert` before
`rtC0CoreArm64Cert`. -/
@[expose] noncomputable def pilotPlainRtArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      pilotPlainRtModArm64 [] rtExitSyms 64 2048 :=
  pilotPlainWeakArm64Cert.append rtC0CoreArm64Cert rfl (by t_kernel_rfl)

compile_linked_chunks! pilotTailArm64Cert armTarget armLayout armLegalTarget armLabelClean
  pilotTailMod 9 (ext := rtC0CoreArm64AllExt ++ KissatPlainBounds.plainAllExt)
  (exits := rtExitSyms) (nX := 64) (maxDirs := 1500)

/-- Full `171`-function closed AAPCS64 Arm64 `LinkedCert` (`maxBound = 2048`, `0` externs). -/
@[expose] noncomputable def pilotArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      pilotLinkedMod [] rtExitSyms 64 2048 :=
  pilotPlainRtArm64Cert.append pilotTailArm64Cert pilotLinkedMod_fns_tail_eq (by t_kernel_rfl)

theorem pilotArm64Cert_bounds_len : pilotArm64Cert.bounds.length = 171 :=
  pilotArm64Cert.bounds_length.trans (by t_kernel_rfl)

theorem pilotArm64_legalSigAll : LegalSigAll armLegalTarget pilotLinkedMod.fns := by
  rw [pilotLinkedMod_fns_tail_eq]
  exact legalSigAll_append (by t_kernel_rfl) (legalSigAll_of_check (by decide))

/-! ## 2. `64 KiB` AAPCS64 Arm64 `TargetInit` & Machine-Level `Defined` / `FnSpec` -/

theorem pilotArm64InitMem_entry (n : Nat) (bs : List UInt8)
    (_hn : n ≤ 4096) (_hbs : bs.length ≤ 65536) :
    (Eq (bs.At 4096#64) ⋆ armTarget.Entry 4096#64 4660 n ⋆ emp) (armInitMem n bs) := by
  have hzs : (stackZeros n).length = n := stackZeros_length n
  have hlen : (stackZeros n).length + bs.length ≤ 2 ^ 64 := by rw [hzs]; omega
  have h1 := Mem.At_append_sep (stackZeros n) bs (4096#64 - BitVec.ofNat 64 n) hlen
  rw [hzs, BitVec.sub_add_cancel] at h1
  have heq : Eq (armInitMem n bs) =
      (Eq (bs.At 4096#64) ⋆ Eq ((stackZeros n).At (4096#64 - BitVec.ofNat 64 n)) ⋆ emp) := by
    rw [sep_emp]
    change Eq ((stackZeros n ++ bs).At (4096#64 - BitVec.ofNat 64 n)) = _
    rw [h1, sep_comm]
  have hmem : (Eq (bs.At 4096#64) ⋆ Eq ((stackZeros n).At (4096#64 - BitVec.ofNat 64 n)) ⋆
      emp) (armInitMem n bs) :=
    Eq.mp (congrFun heq (armInitMem n bs)) rfl
  refine sep_mono_mid (fun m hm => ?_) hmem
  rw [show armTarget.Entry 4096#64 4660 n = region (4096#64 - BitVec.ofNat 64 n) n ⋆
      region 4096#64 0 from rfl, region_zero, sep_emp]
  exact ⟨stackZeros n, hzs, hm.symm⟩

/-- `TargetInit` extending `armInit` to `64 KiB` (`65536` bytes) at `0x1000#64` for
`nvPilotSlab`. -/
@[expose] def pilotArm64Init : TargetInit armTarget 4096 65536 where
  sp0 := armInit.sp0
  ra0 := armInit.ra0
  ret0 := armInit.ret0
  arg0 := armInit.arg0
  initState := armInit.initState
  get_sp := armInit.get_sp
  argsIn := armInit.argsIn
  raReg := armInit.raReg
  spEntry := armInit.spEntry
  mem_entry := fun n bs {_as} _ hn hbs => pilotArm64InitMem_entry n bs hn hbs
  retsIn_singleton := armInit.retsIn_singleton
  argsIn_singleton := armInit.argsIn_singleton

private theorem pilotArm64_fnSpec_src {f : Fn} (hf : f ∈ pilotProgMod.fns)
    (has : armLegalTarget.legalSig f.as = f.as)
    (hrs : armLegalTarget.legalSig f.rs = f.rs) :
    armTarget.Defined pilotArm64Cert.host f.name ∧
    armTarget.FnSpec pilotArm64Cert.host f.name
      (pilotLinkedEnv f.name f.as f.rs) (pilotArm64Cert.bound f.name) 64 :=
  pilotArm64Cert.fnSpec_host_src pilotLinkedEnv
    pilotLinkedMod_checkAcyclic pilotLinkedMod_fns_wf pilotLinkedMod_fn_sound
    (pilotProgMod_mem_pilotLinkedMod hf) has hrs
    (fun _ _ _ _ _ h => pilotLinkedEnv_noExit_prog hf h)

theorem pilotArm64_checkSatBA_fnSpec :
    armTarget.Defined pilotArm64Cert.host pilotTfs.tf_0.toFn.name ∧
    armTarget.FnSpec pilotArm64Cert.host pilotTfs.tf_0.toFn.name
      pilotKissatSolveBASpec (pilotArm64Cert.bound pilotTfs.tf_0.toFn.name) 64 :=
  let h := pilotArm64_fnSpec_src
    (by simp [pilotProgMod, lcnfTModuleWithExts, Frontend.C0.tflatFnsToFns, pilotTfs])
    (by decide) (by decide)
  ⟨h.1, Target.FnSpec.of_spec armTarget h.2 fun _ _ _ _ hs =>
    pilotProgEnv_le_pilotLinkedEnv (pilotProgEnv_checkSatBA hs)⟩

theorem pilotArm64_checkSatNat_fnSpec :
    armTarget.Defined pilotArm64Cert.host pilotTfs.tf_1.toFn.name ∧
    armTarget.FnSpec pilotArm64Cert.host pilotTfs.tf_1.toFn.name
      pilotKissatSolveNatSpec (pilotArm64Cert.bound pilotTfs.tf_1.toFn.name) 64 :=
  let h := pilotArm64_fnSpec_src
    (by simp [pilotProgMod, lcnfTModuleWithExts, Frontend.C0.tflatFnsToFns, pilotTfs])
    (by decide) (by decide)
  ⟨h.1, Target.FnSpec.of_spec armTarget h.2 fun _ _ _ _ hs =>
    pilotProgEnv_le_pilotLinkedEnv (pilotProgEnv_checkSatNat hs)⟩

theorem pilotArm64_xorBA_fnSpec :
    armTarget.Defined pilotArm64Cert.host pilotTfs.tf_2.toFn.name ∧
    armTarget.FnSpec pilotArm64Cert.host pilotTfs.tf_2.toFn.name
      pilotXorBASpec (pilotArm64Cert.bound pilotTfs.tf_2.toFn.name) 64 :=
  let h := pilotArm64_fnSpec_src
    (by simp [pilotProgMod, lcnfTModuleWithExts, Frontend.C0.tflatFnsToFns, pilotTfs])
    (by decide) (by decide)
  ⟨h.1, Target.FnSpec.of_spec armTarget h.2 fun _ _ _ _ hs =>
    pilotProgEnv_le_pilotLinkedEnv (pilotProgEnv_xorBA hs)⟩

theorem pilotArm64_xorNat_fnSpec :
    armTarget.Defined pilotArm64Cert.host pilotTfs.tf_3.toFn.name ∧
    armTarget.FnSpec pilotArm64Cert.host pilotTfs.tf_3.toFn.name
      pilotXorNatSpec (pilotArm64Cert.bound pilotTfs.tf_3.toFn.name) 64 :=
  let h := pilotArm64_fnSpec_src
    (by simp [pilotProgMod, lcnfTModuleWithExts, Frontend.C0.tflatFnsToFns, pilotTfs])
    (by decide) (by decide)
  ⟨h.1, Target.FnSpec.of_spec armTarget h.2 fun _ _ _ _ hs =>
    pilotProgEnv_le_pilotLinkedEnv (pilotProgEnv_xorNat hs)⟩

theorem pilotArm64_solveXorBA_fnSpec :
    armTarget.Defined pilotArm64Cert.host pilotTfs.tf_4.toFn.name ∧
    armTarget.FnSpec pilotArm64Cert.host pilotTfs.tf_4.toFn.name
      pilotSolveXorBASpec (pilotArm64Cert.bound pilotTfs.tf_4.toFn.name) 64 :=
  let h := pilotArm64_fnSpec_src
    (by simp [pilotProgMod, lcnfTModuleWithExts, Frontend.C0.tflatFnsToFns, pilotTfs])
    (by decide) (by decide)
  ⟨h.1, Target.FnSpec.of_spec armTarget h.2 fun _ _ _ _ hs =>
    pilotProgEnv_le_pilotLinkedEnv (pilotProgEnv_solveXorBA hs)⟩

/-! ## 3. Closed Hardware `Eventually` Non-Vacuity Witnesses (`XPost := False`, `<= std3`) -/

theorem pilotArm64_checkSatBA_unsat_run :
    let fn := pilotTfs.tf_0.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvUnsatBaAddr nvPilotRem, 2048#64, 100#64, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = 20#64 ∧
        ∃ cnf, parseDimacs nvUnsatDimacs = some cnf ∧ cnf.Unsat)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvSatBaObj nvPilotRem) ⋆ lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) ((nvPilotSlab nvPilotRem).At 4096#64) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hspec := pilotKissatSolveBASpec_unsat (workReq := 2048#64) (fuel := 100#64)
    (mv := 1) (nc := 2) (i0 := 9)
    (nvUnsatBaObj_canon (rem := nvPilotRem) (by decide) (by decide)) (by decide)
    (by decide) (by decide)
    (by unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf ffiCarveWcap align8
        decide)
    (by decide) (by decide)
    (by refine UnitUnsatTrace.step (l := 0) (rest := List.drop 13 nvUnsatDimacs) (by decide)
          rfl (by decide) ?_
        exact UnitUnsatTrace.conflict (l := 1) (rest := [10]) (k := 0) (by decide)
          rfl (by decide) ⟨CNF.empty, rfl⟩)
    hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_checkSatBA_fnSpec.2
    (nvPilotSlab nvPilotRem) args 20#64
    (fun _ => (∃ cnf, parseDimacs nvUnsatDimacs = some cnf ∧ cnf.Unsat) ∧ True)
    nvPilotSlab_lt_64k (by decide) hspec
    (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, ⟨h.2.1, trivial⟩⟩) (by decide)
  exact eventually_weaken _ _ _ _
    (fun st ⟨hpc, hr, hmem⟩ => by
      rw [sep_emp] at hmem
      exact ⟨hpc, hr, (sep_pure_l (P := fun _ => True) |>.mp hmem).1⟩) hrun

theorem pilotArm64_checkSatBA_sat_run :
    let fn := pilotTfs.tf_0.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvSatBaAddr nvPilotRem, 2048#64, 100#64, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = 10#64 ∧
        ∃ cnf, parseDimacs nvSatDimacs = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) ((nvPilotSlab nvPilotRem).At 4096#64) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hspec := pilotKissatSolveBASpec_sat (workReq := 2048#64) (fuel := 100#64)
    (mv := 1) (nc := 1) (i0 := 9)
    (nvSatBaObj_canon (rem := nvPilotRem) (by decide) (by decide)) (by decide)
    (by decide) (by decide)
    (by unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf ffiCarveWcap align8
        decide)
    (by decide) (by decide)
    (UnitSatTrace.step (l := 0) (rest := [10]) (k := 0) (by decide) rfl (by decide)
      (UnitSatTrace.done (by decide)))
    (fun v hv => by cases v with | zero => decide | succ _ => omega)
    (by decide) hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_checkSatBA_fnSpec.2
    (nvPilotSlab nvPilotRem) args 10#64
    (fun _ =>
      (∃ cnf, parseDimacs nvSatDimacs = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧ True)
    nvPilotSlab_lt_64k (by decide) hspec
    (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, ⟨h.2.1, trivial⟩⟩) (by decide)
  exact eventually_weaken _ _ _ _
    (fun st ⟨hpc, hr, hmem⟩ => by
      rw [sep_emp] at hmem
      exact ⟨hpc, hr, (sep_pure_l (P := fun _ => True) |>.mp hmem).1⟩) hrun

theorem pilotArm64_checkSatBA_oom_run :
    let fn := pilotTfs.tf_0.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvUnsatBaAddr nvPilotRem, 8192#64, 100#64, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = 3#64)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvSatBaObj nvPilotRem) ⋆ lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) ((nvPilotSlab nvPilotRem).At 4096#64) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hspec := pilotKissatSolveBASpec_oom (workReq := 8192#64) (fuel := 100#64)
    (nvUnsatBaObj_canon (rem := nvPilotRem) (by decide) (by decide)) (by decide) hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_checkSatBA_fnSpec.2
    (nvPilotSlab nvPilotRem) args 3#64 (fun _ => True) nvPilotSlab_lt_64k (by decide) hspec
    (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, trivial⟩) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hr, _⟩ => ⟨hpc, hr⟩) hrun

theorem pilotArm64_checkSatNat_mpz_unsat_run :
    let fn := pilotTfs.tf_1.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvUnsatMpzAddr nvPilotRem, 2048#64, 100#64, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = 20#64 ∧
        ∃ cnf, parseDimacs nvUnsatDimacs = some cnf ∧ cnf.Unsat)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  let hrt := nvPilotRtSt nvPilotRem (by decide)
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase hrt ⋆ cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [nvUnsatMpzObj nvPilotRem] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) ((nvPilotSlab nvPilotRem).At 4096#64) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hge63 : ¬ (natOfBytesS nvUnsatDimacs < 2 ^ 63) :=
    Nat.not_lt_of_ge (natOfBytesS_ge_2p63 (by decide))
  have hrep : RtNatRep (nvUnsatMpzAddr nvPilotRem) (natOfBytesS nvUnsatDimacs)
      [nvUnsatMpzObj nvPilotRem] := by
    simp only [RtNatRep, hge63, ↓reduceIte]
    exact ⟨by decide, nvUnsatMpzObj nvPilotRem, List.mem_cons_self, rfl,
      nvUnsatMpzObj_rtCanon (by decide) (by decide)⟩
  have hspec := pilotKissatSolveNatSpec_unsat (workReq := 2048#64) (fuel := 100#64)
    (mv := 1) (nc := 2) (i0 := 9)
    (by decide) hrep (bytesOfNatS_natOfBytesS nvUnsatDimacs)
    (by decide) (fun h => absurd (by decide : (nvUnsatMpzAddr nvPilotRem &&& 1#64) = 0#64) h)
    (fun _ => by decide) (by decide) (by decide)
    (by unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf ffiCarveWcap align8
        decide)
    (by decide) (by decide)
    (by refine UnitUnsatTrace.step (l := 0) (rest := List.drop 13 nvUnsatDimacs) (by decide)
          rfl (by decide) ?_
        exact UnitUnsatTrace.conflict (l := 1) (rest := [10]) (k := 0) (by decide)
          rfl (by decide) ⟨CNF.empty, rfl⟩)
    hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_checkSatNat_fnSpec.2
    (nvPilotSlab nvPilotRem) args 20#64
    (fun _ => (∃ cnf, parseDimacs nvUnsatDimacs = some cnf ∧ cnf.Unsat) ∧ True)
    nvPilotSlab_lt_64k (by decide) hspec
    (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, ⟨h.2.1, trivial⟩⟩) (by decide)
  exact eventually_weaken _ _ _ _
    (fun st ⟨hpc, hr, hmem⟩ => by
      rw [sep_emp] at hmem
      exact ⟨hpc, hr, (sep_pure_l (P := fun _ => True) |>.mp hmem).1⟩) hrun

theorem pilotArm64_checkSatNat_tagged_run :
    let fn := pilotTfs.tf_1.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvTaggedArg, 2048#64, 100#64, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = 0#64)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆ lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem)))
      ((nvPilotSlab nvPilotRem).At 4096#64) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hspec := pilotKissatSolveNatSpec_tagged_nonDimacs (bs := nvTaggedBytes)
    (workReq := 2048#64) (fuel := 100#64)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_checkSatNat_fnSpec.2
    (nvPilotSlab nvPilotRem) args 0#64 (fun _ => True) nvPilotSlab_lt_64k (by decide) hspec
    (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, trivial⟩) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hr, _⟩ => ⟨hpc, hr⟩) hrun

theorem pilotArm64_checkSatNat_oom_run :
    let fn := pilotTfs.tf_1.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvUnsatMpzAddr nvPilotRem, 8192#64, 100#64, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = 3#64)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [nvUnsatMpzObj nvPilotRem] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) ((nvPilotSlab nvPilotRem).At 4096#64) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hge63 : ¬ (natOfBytesS nvUnsatDimacs < 2 ^ 63) :=
    Nat.not_lt_of_ge (natOfBytesS_ge_2p63 (by decide))
  have hrep : RtNatRep (nvUnsatMpzAddr nvPilotRem) (natOfBytesS nvUnsatDimacs)
      [nvUnsatMpzObj nvPilotRem] := by
    simp only [RtNatRep, hge63, ↓reduceIte]
    exact ⟨by decide, nvUnsatMpzObj nvPilotRem, List.mem_cons_self, rfl,
      nvUnsatMpzObj_rtCanon (by decide) (by decide)⟩
  have hspec := pilotKissatSolveNatSpec_oom (workReq := 8192#64) (fuel := 100#64)
    (by decide) hrep (bytesOfNatS_natOfBytesS nvUnsatDimacs)
    (by decide) (fun h => absurd (by decide : (nvUnsatMpzAddr nvPilotRem &&& 1#64) = 0#64) h)
    (fun _ => by decide) (by decide) hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_checkSatNat_fnSpec.2
    (nvPilotSlab nvPilotRem) args 3#64 (fun _ => True) nvPilotSlab_lt_64k (by decide) hspec
    (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, trivial⟩) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hr, _⟩ => ⟨hpc, hr⟩) hrun

theorem pilotArm64_xorBA_ok_run :
    let fn := pilotTfs.tf_2.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvMaskedBaAddr nvPilotRem, nvXorKeyBv, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        let p := armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧ p ≠ 0#64 ∧ p.toNat % 8 = 0)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotRem))) ((nvPilotSlab nvPilotRem).At 4096#64) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hspec := pilotXorBASpec_ok (key := nvXorKeyBv)
    (nvMaskedUnsatBaObj_canon (rem := nvPilotRem) (by decide) (by decide)) (by decide)
    (by decide) hm
  refine pilotArm64Cert.run_fnSpec pilotArm64Init pilotArm64_xorBA_fnSpec.2
    (nvPilotSlab nvPilotRem) args nvPilotSlab_lt_64k (by decide) hspec (fun st h => ?_) (by decide)
  rcases h with ⟨hpc, ⟨⟨r, _⟩, m', hr, hrets, _⟩⟩ | ⟨_, _, _, _, hf, _⟩
  · rcases hr with ⟨_, _, hp0, hp8, _⟩
    have hreg := pilotArm64Init.retsIn_singleton r (armTarget.mach.data st) hrets
    exact ⟨hpc, hreg ▸ hp0, hreg ▸ hp8⟩
  · exact False.elim hf

theorem pilotArm64_xorBA_oom_run :
    let fn := pilotTfs.tf_2.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvMaskedBaAddr nvPilotOomRem, nvXorKeyBv, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = ffiResOomWord)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotOomRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotOomRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotOomRem (by decide)) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj nvPilotOomRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotOomRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotOomRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotOomRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotOomRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotOomRem))) ((nvPilotSlab nvPilotOomRem).At 4096#64) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hspec := pilotXorBASpec_oom (key := nvXorKeyBv)
    (nvMaskedUnsatBaObj_canon (rem := nvPilotOomRem) (by decide) (by decide)) (by decide)
    (by unfold pilotXorBaOk ffiCarveOk ffiCarveWcap ffiCarveWend baAllocBytes align8
        simp [nvMaskedUnsatBaObj, mkBaObj, nvPilotRtSt, nvPilotHdr, nvPilotBase, nvPilotOomRem]
        decide) hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_xorBA_fnSpec.2
    (nvPilotSlab nvPilotOomRem) args ffiResOomWord (fun _ => True) nvPilotOomSlab_lt_64k
    (by decide) hspec (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, trivial⟩) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hr, _⟩ => ⟨hpc, hr⟩) hrun

theorem pilotArm64_xorNat_tagged_ok_run :
    let fn := pilotTfs.tf_3.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvTaggedArg, nvXorKeyBv, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        let p := armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧ p ≠ 0#64 ∧ p.toNat % 8 = 0)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotRem) ⋆ lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem)))
      ((nvPilotSlab nvPilotRem).At 4096#64) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hspec := pilotXorNatSpec_tagged_ok (bs := nvTaggedBytes) (key := nvXorKeyBv)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hm
  refine pilotArm64Cert.run_fnSpec pilotArm64Init pilotArm64_xorNat_fnSpec.2
    (nvPilotSlab nvPilotRem) args nvPilotSlab_lt_64k (by decide) hspec (fun st h => ?_) (by decide)
  rcases h with ⟨hpc, ⟨⟨r, _⟩, m', hr, hrets, _⟩⟩ | ⟨_, _, _, _, hf, _⟩
  · rcases hr with ⟨_, _, hp0, hp8, _⟩
    have hreg := pilotArm64Init.retsIn_singleton r (armTarget.mach.data st) hrets
    exact ⟨hpc, hreg ▸ hp0, hreg ▸ hp8⟩
  · exact False.elim hf

theorem pilotArm64_xorNat_mpz_ok_run :
    let fn := pilotTfs.tf_3.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvUnsatMpzAddr nvPilotRem, nvXorKeyBv, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        let p := armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧ p ≠ 0#64 ∧ p.toNat % 8 = 0)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆ lcnfHeap [nvUnsatMpzObj nvPilotRem] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem))) ((nvPilotSlab nvPilotRem).At 4096#64) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hge63 : ¬ (natOfBytesS nvUnsatDimacs < 2 ^ 63) :=
    Nat.not_lt_of_ge (natOfBytesS_ge_2p63 (by decide))
  have hrep : RtNatRep (nvUnsatMpzAddr nvPilotRem) (natOfBytesS nvUnsatDimacs)
      [nvUnsatMpzObj nvPilotRem] := by
    simp only [RtNatRep, hge63, ↓reduceIte]
    exact ⟨by decide, nvUnsatMpzObj nvPilotRem, List.mem_cons_self, rfl,
      nvUnsatMpzObj_rtCanon (by decide) (by decide)⟩
  have hspec := pilotXorNatSpec_mpz_ok (key := nvXorKeyBv)
    (by decide) hrep (by decide) (by decide) (by decide) (by decide) hm
  refine pilotArm64Cert.run_fnSpec pilotArm64Init pilotArm64_xorNat_fnSpec.2
    (nvPilotSlab nvPilotRem) args nvPilotSlab_lt_64k (by decide) hspec (fun st h => ?_) (by decide)
  rcases h with ⟨hpc, ⟨⟨r, _⟩, m', hr, hrets, _⟩⟩ | ⟨_, _, _, _, hf, _⟩
  · rcases hr with ⟨_, _, _, _, hp0, hp8, _⟩
    have hreg := pilotArm64Init.retsIn_singleton r (armTarget.mach.data st) hrets
    exact ⟨hpc, hreg ▸ hp0, hreg ▸ hp8⟩
  · exact False.elim hf

theorem pilotArm64_xorNat_oom_run :
    let fn := pilotTfs.tf_3.toFn
    let args : Tup Val fn.as := (nvPilotBase, nvUnsatMpzAddr nvPilotOomRem, nvXorKeyBv, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = ffiResOomWord)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotOomRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotOomRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotOomRem (by decide)) ⋆
      cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotOomRem) ⋆
      cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
      array64 (nvPilotScr nvPilotOomRem) nvPilotScrLimbs ⋆
      lcnfHeap [nvUnsatMpzObj nvPilotOomRem] ⋆
      (lcnfObjMem (nvUnsatBaObj nvPilotOomRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotOomRem) ⋆
        lcnfObjMem (nvMaskedUnsatBaObj nvPilotOomRem)))
      ((nvPilotSlab nvPilotOomRem).At 4096#64) := by
    simp only [lcnfHeap, sep_emp]
    exact sep_cast_ac hm0 (by ac_rfl)
  have hge63 : ¬ (natOfBytesS nvUnsatDimacs < 2 ^ 63) :=
    Nat.not_lt_of_ge (natOfBytesS_ge_2p63 (by decide))
  have hrep : RtNatRep (nvUnsatMpzAddr nvPilotOomRem) (natOfBytesS nvUnsatDimacs)
      [nvUnsatMpzObj nvPilotOomRem] := by
    simp only [RtNatRep, hge63, ↓reduceIte]
    exact ⟨by decide, nvUnsatMpzObj nvPilotOomRem, List.mem_cons_self, rfl,
      nvUnsatMpzObj_rtCanon (by decide) (by decide)⟩
  have hspec := pilotXorNatSpec_oom (key := nvXorKeyBv) (by decide) hrep
    (bytesOfNatS_natOfBytesS nvUnsatDimacs) (by decide)
    (fun h => absurd (by decide : (nvUnsatMpzAddr nvPilotOomRem &&& 1#64) = 0#64) h)
    (fun _ => by decide)
    (by unfold pilotXorNatOk ffiCarveOk ffiCarveWcap ffiCarveWend natSAllocBytes natSLimbCount
          align8
        simp [nvPilotRtSt, nvPilotHdr, nvPilotBase, nvPilotOomRem]
        decide)
    hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_xorNat_fnSpec.2
    (nvPilotSlab nvPilotOomRem) args ffiResOomWord (fun _ => True) nvPilotOomSlab_lt_64k
    (by decide) hspec (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, trivial⟩) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hr, _⟩ => ⟨hpc, hr⟩) hrun

theorem pilotArm64_solveXorBA_unsat_run :
    let fn := pilotTfs.tf_4.toFn
    let args : Tup Val fn.as :=
      (nvPilotBase, nvMaskedBaAddr nvPilotRem, nvXorKeyBv, 2048#64, 100#64, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        let r := armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        (r = 0#64 ∨ r = 3#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs nvUnsatDimacs = some cnf ∧ cnf.Unsat))
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotRem (by decide)) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj nvPilotRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotRem))) ((nvPilotSlab nvPilotRem).At 4096#64) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hinv : List.map (fun x => x ^^^ UInt8.ofBitVec nvXorKeyBv) nvMaskedDimacs =
      nvUnsatDimacs := by decide
  have hspec := pilotSolveXorBASpec_unsat (key := nvXorKeyBv) (workReq := 2048#64)
    (fuel := 100#64) (nvMaskedUnsatBaObj_canon (rem := nvPilotRem) (by decide) (by decide))
    (by decide) (by decide) (by decide) hm
  refine pilotArm64Cert.run_fnSpec pilotArm64Init pilotArm64_solveXorBA_fnSpec.2
    (nvPilotSlab nvPilotRem) args nvPilotSlab_lt_64k (by decide) hspec (fun st h => ?_) (by decide)
  rcases h with ⟨hpc, ⟨⟨r, _⟩, m', hr, hrets, _⟩⟩ | ⟨_, _, _, _, hf, _⟩
  · have hreg := pilotArm64Init.retsIn_singleton r (armTarget.mach.data st) hrets
    refine ⟨hpc, hreg ▸ hr.1, fun hr20 => ?_⟩
    simpa [nvMaskedUnsatBaObj, mkBaObj, hinv] using hr.2.1 (hreg ▸ hr20)
  · exact False.elim hf

theorem pilotArm64_solveXorBA_oom_run :
    let fn := pilotTfs.tf_4.toFn
    let args : Tup Val fn.as :=
      (nvPilotBase, nvMaskedBaAddr nvPilotOomRem, nvXorKeyBv, 2048#64, 100#64, ())
    Eventually (armTarget.mach.step pilotArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = pilotArm64Init.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) pilotArm64Init.ret0 = 3#64)
      (armTarget.mach.mkState (pilotArm64Init.initState (pilotArm64Cert.bound fn.name)
          (nvPilotSlab nvPilotOomRem) args)
        (armTarget.mach.labelAddr pilotArm64Cert.host fn.name)) := by
  intro fn args
  have hm0 := nvPilotMem_ok (rem := nvPilotOomRem) (by decide) (by decide)
  have hm : (rtC0Inv nvPilotBase (nvPilotRtSt nvPilotOomRem (by decide)) ⋆
      lcnfObjMem (nvMaskedUnsatBaObj nvPilotOomRem) ⋆
      (cell64 (nvPilotBase + 33672#64) (nvPilotScr nvPilotOomRem) ⋆
        cell64 (nvPilotBase + 33680#64) (BitVec.ofNat 64 nvPilotScrLimbs.length) ⋆
        array64 (nvPilotScr nvPilotOomRem) nvPilotScrLimbs ⋆
        lcnfObjMem (nvUnsatBaObj nvPilotOomRem) ⋆ lcnfObjMem (nvSatBaObj nvPilotOomRem) ⋆
        lcnfObjMem (nvUnsatMpzObj nvPilotOomRem))) ((nvPilotSlab nvPilotOomRem).At 4096#64) :=
    sep_cast_ac hm0 (by ac_rfl)
  have hspec := pilotSolveXorBASpec_oom (key := nvXorKeyBv) (workReq := 2048#64) (fuel := 100#64)
    (nvMaskedUnsatBaObj_canon (rem := nvPilotOomRem) (by decide) (by decide))
    (by decide) (by decide)
    (by unfold pilotXorBaOk ffiCarveOk ffiCarveWcap ffiCarveWend baAllocBytes align8
        simp [nvMaskedUnsatBaObj, mkBaObj, nvPilotRtSt, nvPilotHdr, nvPilotBase, nvPilotOomRem]
        decide)
    hm
  have hrun := pilotArm64Cert.run_ret1_sep_i64 pilotArm64Init pilotArm64_solveXorBA_fnSpec.2
    (nvPilotSlab nvPilotOomRem) args 3#64 (fun _ => True) nvPilotOomSlab_lt_64k
    (by decide) hspec (fun ⟨_, ()⟩ _ h => ⟨congrArg (·, ()) h.1, trivial⟩) (by decide)
  exact eventually_weaken _ _ _ _ (fun st ⟨hpc, hr, _⟩ => ⟨hpc, hr⟩) hrun

end

end LeanQbe.T.Arm64
