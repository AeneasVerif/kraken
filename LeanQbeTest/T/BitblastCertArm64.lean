/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.KissatPlainBounds
public import LeanQbe.T.Arm64.KissatPlainCert
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import LeanQbe.T.Examples.Bitblast.Src.Full
public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.Full
public import LeanQbe.T.Examples.Bitblast.Build.Flat
public import LeanQbe.T.Logic.Mem
public import LeanQbeTest.T.BitblastCertCommon
public import LeanQbeTest.T.BitblastCertArm64S0
public import LeanQbeTest.T.BitblastCertArm64S1
public import LeanQbeTest.T.BitblastCertArm64S2
public import LeanQbeTest.T.BitblastCertArm64S3
public import LeanQbeTest.T.BitblastCertArm64S4
public import LeanQbeTest.T.BitblastCertArm64S5
public import Kraken.Mem
public import Kraken.Separation

/-!
# Bitblast + KissatPlain AAPCS64 Arm64 Linked Certificate (`BitblastCertArm64`)

Composes `Arm64.KissatPlainCert.plainCert` (`59` Kissat fns) with the six sliced `(flat := true)`
Bitblast certificates (`bitblastCertArm64S0`..`bitblastCertArm64S5`, `64` fns) via zero-recomp
`LinkedCert.append` (`123` functions total, `0` externs left), and proves:
* `bitblastArm64_bv_solve_bytes_fnSpec`: machine-level `Defined` + `FnSpec` for `bv_solve_bytes`;
* `bitblastArm64_bv_solve_bytes_unsat_sound` / `bitblastArm64_host_bv_solve_bytes_unsat_sound`:
  end-to-end machine-code UNSAT soundness (`X0 = 20#64 -> ∀ prog, parse = some prog → prog.Unsat`);
* `bitblastArm64_nv_unsat_run`: concrete `Mem 64` `Eventually` non-vacuity on `nvProgBytes`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertArm64

open Std Std.ExtHashMap Std.Tactic.BVDecide
open LeanQbe.T LeanQbe.T.Arm64 Kraken Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Src.Full
open LeanQbe.T.Examples.Bitblast.Proof
open LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertCommon
open LeanQbeTest.T.BitblastCertArm64S0
open LeanQbeTest.T.BitblastCertArm64S1
open LeanQbeTest.T.BitblastCertArm64S2
open LeanQbeTest.T.BitblastCertArm64S3
open LeanQbeTest.T.BitblastCertArm64S4
open LeanQbeTest.T.BitblastCertArm64S5

/-- Prefix sub-module `[0, 22)`. -/
@[expose] noncomputable def bitblastPref1ModArm64 : Module :=
  { fns := bitblastFlatMod.fns.take 22 }

/-- Prefix sub-module `[0, 33)`. -/
@[expose] noncomputable def bitblastPref2ModArm64 : Module :=
  { fns := bitblastFlatMod.fns.take 33 }

/-- Prefix sub-module `[0, 44)`. -/
@[expose] noncomputable def bitblastPref3ModArm64 : Module :=
  { fns := bitblastFlatMod.fns.take 44 }

/-- Prefix sub-module `[0, 54)`. -/
@[expose] noncomputable def bitblastPref4ModArm64 : Module :=
  { fns := bitblastFlatMod.fns.take 54 }

/-- Prefix certificate `[0, 22)` (`S0 ++ S1`). -/
@[expose] noncomputable def bitblastPref1Arm64Cert :=
  bitblastCertArm64S0.append bitblastCertArm64S1
    (mod := bitblastPref1ModArm64)
    (by exact List.take_add (l := bitblastFlatMod.fns) (i := 11) (j := 11))
    (by t_kernel_rfl)

/-- Prefix certificate `[0, 33)` (`S0..S2`). -/
@[expose] noncomputable def bitblastPref2Arm64Cert :=
  bitblastPref1Arm64Cert.append bitblastCertArm64S2
    (mod := bitblastPref2ModArm64)
    (by exact List.take_add (l := bitblastFlatMod.fns) (i := 22) (j := 11))
    (by t_kernel_rfl)

/-- Prefix certificate `[0, 44)` (`S0..S3`). -/
@[expose] noncomputable def bitblastPref3Arm64Cert :=
  bitblastPref2Arm64Cert.append bitblastCertArm64S3
    (mod := bitblastPref3ModArm64)
    (by exact List.take_add (l := bitblastFlatMod.fns) (i := 33) (j := 11))
    (by t_kernel_rfl)

/-- Prefix certificate `[0, 54)` (`S0..S4`). -/
@[expose] noncomputable def bitblastPref4Arm64Cert :=
  bitblastPref3Arm64Cert.append bitblastCertArm64S4
    (mod := bitblastPref4ModArm64)
    (by exact List.take_add (l := bitblastFlatMod.fns) (i := 44) (j := 10))
    (by t_kernel_rfl)

/-- Zero-recompilation AAPCS64 Arm64 Bitblast tail certificate (`64` fns, `S0..S5`). -/
@[expose] noncomputable def bitblastTailArm64Cert :=
  bitblastPref4Arm64Cert.append bitblastCertArm64S5
    (mod := bitblastFlatMod)
    (by exact (List.take_append_drop 54 bitblastFlatMod.fns).symm)
    (by t_kernel_rfl)

/-- Closed `123`-function AAPCS64 Arm64 `LinkedCert` (`KissatPlainCert.plainCert` + `bitblast`,
`0` Kissat recompilation, `0` externs, `0` exits). -/
@[expose] noncomputable def bitblastArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      bitblastLinkedMod [] [] 0 2048 :=
  KissatPlainCert.plainCert.append bitblastTailArm64Cert
    bitblastLinkedMod_fns_flat_eq (by t_kernel_rfl)

private theorem bitblastLinkedMod_arm64_legal_check :
    checkLegalSigAll armLegalTarget bitblastLinkedMod.fns = true := by
  t_kernel_rfl

theorem bitblastArm64_legalSigAll : LegalSigAll armLegalTarget bitblastLinkedMod.fns :=
  legalSigAll_of_check bitblastLinkedMod_arm64_legal_check

private theorem bvSolveBytesFn_mem_linked :
    bvSolveBytesFn ∈ bitblastLinkedMod.fns :=
  List.mem_append_right _
    (List.mem_of_getElem? (rfl : bitblastModule.fns[63]? = some bvSolveBytesFn))

/-- `armTarget.Defined` + `armTarget.FnSpec` for `bv_solve_bytes` on any legal AAPCS64 Arm64
host embedding `bitblastArm64Cert.code`. -/
theorem bitblastArm64_bv_solve_bytes_fnSpec [hh : armTarget.mach.Host]
    (k₀ : Nat) (hc : bitblastArm64Cert.code.IsInfixAt hh.prog k₀)
    (hu : armTarget.LabelsUnique hh) :
    armTarget.Defined hh "bv_solve_bytes" ∧
    armTarget.FnSpec hh "bv_solve_bytes"
      (bitblastLinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (bitblastArm64Cert.bound "bv_solve_bytes") 0 :=
  bitblastArm64Cert.fnSpec_noExit_of_legalSigAll hh bitblastLinkedEnv k₀ hc hu
    bitblastLinkedMod_checkAcyclic bitblastLinkedMod_wf bitblastArm64_legalSigAll
    bitblastLinkedEnv_sound bvSolveBytesFn_mem_linked
    (fun args m Q X X' h => bitblastLinkedEnv_noExit _ _ _ args m Q X X' h)

/-- Closed `Defined` + `FnSpec` for `bv_solve_bytes` on `bitblastArm64Cert.host`. -/
theorem bitblastArm64_host_bv_solve_bytes_fnSpec :
    armTarget.Defined bitblastArm64Cert.host "bv_solve_bytes" ∧
    armTarget.FnSpec bitblastArm64Cert.host "bv_solve_bytes"
      (bitblastLinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (bitblastArm64Cert.bound "bv_solve_bytes") 0 :=
  bitblastArm64Cert.fnSpec_host_of_legalSigAll bitblastLinkedEnv
    bitblastLinkedMod_checkAcyclic bitblastLinkedMod_wf bitblastArm64_legalSigAll
    bitblastLinkedEnv_sound bvSolveBytesFn_mem_linked
    (fun args m Q X X' h => bitblastLinkedEnv_noExit _ _ _ args m Q X X' h)

/-- End-to-end AAPCS64 Arm64 machine-code UNSAT soundness for `bv_solve_bytes`: returning
`X0 = 20#64` certifies `BVLogicalExpr.Unsat` for any parsed `BVP1` bytecode input. -/
theorem bitblastArm64_bv_solve_bytes_unsat_sound [hh : armTarget.mach.Host]
    (k₀ : Nat) (hc : bitblastArm64Cert.code.IsInfixAt hh.prog k₀)
    (hu : armTarget.LabelsUnique hh)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hargs : armTarget.ArgsIn (as := [i64, i64, i64, i64, i64])
      (progPtr, progLen, workPtr, workCap, fuel, ()) s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec -
        BitVec.ofNat 64 (bitblastArm64Cert.bound "bv_solve_bytes"))
        (bitblastArm64Cert.bound "bv_solve_bytes") ⋆ R) :
    Eventually (step1 hh.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (st.data.regs.X0.toBitVec = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            st.data.regs.X0.toBitVec = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (bitblastArm64Cert.bound "bv_solve_bytes"))
              (bitblastArm64Cert.bound "bv_solve_bytes") ⋆ R))
      ⟨s, Labels.label "bv_solve_bytes"⟩ := by
  let Q : LeanQbe.T.Post [i64] := fun (r, ()) m' =>
    (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
    (r = 20#64 → ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
    (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel → r = 20#64)
  have hspec := bitblastLinked_bvSolveBytesSpec
    (xs := (progPtr, progLen, workPtr, workCap, fuel, ())) (m := m) (Q := Q)
    (X := fun _ _ _ _ => False)
    ⟨progBytes, Rm, hplen, hm, fun r m' hm' hunsat htriv => ⟨hm', hunsat, htriv⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (arm64_of_returns (bitblastArm64_bv_solve_bytes_fnSpec k₀ hc hu).2
      hspec s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcs, hsp', ⟨r, _⟩, m', ⟨hm', hunsat, htriv⟩, hrets, hdm⟩
  have hreg : st.data.regs.X0.toBitVec = r := armInit.retsIn_singleton r st.data hrets
  exact ⟨hpc, hcs, hsp', m', hm', fun hr20 => hunsat (hreg ▸ hr20),
    fun htr => hreg.trans (htriv htr), hdm⟩

/-- Closed specialization of `bitblastArm64_bv_solve_bytes_unsat_sound` to
`bitblastArm64Cert.host`. -/
theorem bitblastArm64_host_bv_solve_bytes_unsat_sound
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hargs : armTarget.ArgsIn (as := [i64, i64, i64, i64, i64])
      (progPtr, progLen, workPtr, workCap, fuel, ()) s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec -
        BitVec.ofNat 64 (bitblastArm64Cert.bound "bv_solve_bytes"))
        (bitblastArm64Cert.bound "bv_solve_bytes") ⋆ R) :
    Eventually (armTarget.mach.step bitblastArm64Cert.host)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (st.data.regs.X0.toBitVec = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            st.data.regs.X0.toBitVec = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (bitblastArm64Cert.bound "bv_solve_bytes"))
              (bitblastArm64Cert.bound "bv_solve_bytes") ⋆ R))
      (armTarget.mach.mkState s
        (armTarget.mach.labelAddr bitblastArm64Cert.host "bv_solve_bytes")) :=
  bitblastArm64_bv_solve_bytes_unsat_sound (hh := bitblastArm64Cert.host) 0
    bitblastArm64Cert.code_infix_host bitblastArm64Cert.labelsUnique
    progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm hargs hra hsp hmem

/-- Concrete AAPCS64 Arm64 `Mem 64` `Eventually` non-vacuity witness on `nvProgBytes`
(`BCONST false` -> `X0 = 20#64` and `prog.Unsat`). -/
theorem bitblastArm64_nv_unsat_run :
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (nvSlabPtr, nvProgLen, nvSlabWorkPtr, nvWorkCap, nvFuel, ())
    Eventually (armTarget.mach.step bitblastArm64Cert.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        ∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat)
      (armTarget.mach.mkState
        (armInit.initState (bitblastArm64Cert.bound "bv_solve_bytes") nvSlabBytes args)
        (armTarget.mach.labelAddr bitblastArm64Cert.host "bv_solve_bytes")) := by
  intro args
  let Q : LeanQbe.T.Post [i64] := fun (r, ()) _ =>
    r = 20#64 ∧ ∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat
  have hspec := bitblastLinked_bvSolveBytesSpec
    (nvSlab_bvSolveBytesSpec Q (fun _ _ _ _ => False) (fun _ _ hu => ⟨rfl, hu⟩))
  refine bitblastArm64Cert.run_fnSpec armInit bitblastArm64_host_bv_solve_bytes_fnSpec.2
    nvSlabBytes args nvSlabBytes_le_8192 (by decide) hspec (fun st h => ?_) (by decide)
  rcases h with ⟨hpc, ⟨⟨r, _⟩, m', ⟨hr20, hu⟩, hrets, _⟩⟩ | ⟨_, _, _, _, hf, _⟩
  · subst hr20
    exact ⟨hpc, armInit.retsIn_singleton 20#64 (armTarget.mach.data st) hrets, hu⟩
  · exact False.elim hf

end LeanQbeTest.T.BitblastCertArm64
