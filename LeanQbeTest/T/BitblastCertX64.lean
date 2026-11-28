/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertProof
import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatPlainBounds
public import LeanQbe.T.Amd64.KissatPlainCert
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import LeanQbe.T.Examples.Bitblast.Src.Full
public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.Full
public import LeanQbe.T.Examples.Bitblast.Build.Flat
public import LeanQbe.T.Logic.Mem
public import LeanQbeTest.T.BitblastCertCommon
public import LeanQbeTest.T.BitblastCertX64S0
public import LeanQbeTest.T.BitblastCertX64S1
public import LeanQbeTest.T.BitblastCertX64S2
public import LeanQbeTest.T.BitblastCertX64S3
public import LeanQbeTest.T.BitblastCertX64S4
public import LeanQbeTest.T.BitblastCertX64S5
public import Kraken.Mem
public import Kraken.Separation

/-!
# Bitblast + KissatPlain SysV x86-64 Linked Certificate (`BitblastCertX64`)

Composes `Amd64.KissatPlainCert.plainCert` (`59` Kissat fns) with the six sliced `(flat := true)`
Bitblast certificates (`bitblastCertX64S0`..`bitblastCertX64S5`, `64` fns) via zero-recompilation
`LinkedCert.append` (`123` functions total, `0` externs left), and proves:
* `bitblastX64_bv_solve_bytes_fnSpec`: machine-level `Defined` + `FnSpec` for `bv_solve_bytes`;
* `bitblastX64_bv_solve_bytes_unsat_sound` / `bitblastX64_host_bv_solve_bytes_unsat_sound`:
  end-to-end machine-code UNSAT soundness (`rax = 20#64 -> ∀ prog, parse = some prog → prog.Unsat`);
* `bitblastX64_nv_unsat_run`: concrete `Mem 64` `Eventually` non-vacuity on `nvProgBytes`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertX64

open Std Std.ExtHashMap Std.Tactic.BVDecide
open LeanQbe.T LeanQbe.T.Amd64 Kraken Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Src.Full
open LeanQbe.T.Examples.Bitblast.Proof
open LeanQbe.T.Examples.Bitblast.Build
open LeanQbeTest.T.BitblastCertCommon
open LeanQbeTest.T.BitblastCertX64S0
open LeanQbeTest.T.BitblastCertX64S1
open LeanQbeTest.T.BitblastCertX64S2
open LeanQbeTest.T.BitblastCertX64S3
open LeanQbeTest.T.BitblastCertX64S4
open LeanQbeTest.T.BitblastCertX64S5

/-- Prefix sub-module `[0, 22)`. -/
@[expose] noncomputable def bitblastPref1ModX64 : Module :=
  { fns := bitblastFlatMod.fns.take 22 }

/-- Prefix sub-module `[0, 33)`. -/
@[expose] noncomputable def bitblastPref2ModX64 : Module :=
  { fns := bitblastFlatMod.fns.take 33 }

/-- Prefix sub-module `[0, 44)`. -/
@[expose] noncomputable def bitblastPref3ModX64 : Module :=
  { fns := bitblastFlatMod.fns.take 44 }

/-- Prefix sub-module `[0, 54)`. -/
@[expose] noncomputable def bitblastPref4ModX64 : Module :=
  { fns := bitblastFlatMod.fns.take 54 }

/-- Prefix certificate `[0, 22)` (`S0 ++ S1`). -/
@[expose] noncomputable def bitblastPref1X64Cert :=
  bitblastCertX64S0.append bitblastCertX64S1
    (mod := bitblastPref1ModX64)
    (by exact List.take_add (l := bitblastFlatMod.fns) (i := 11) (j := 11))
    (by t_kernel_rfl)

/-- Prefix certificate `[0, 33)` (`S0..S2`). -/
@[expose] noncomputable def bitblastPref2X64Cert :=
  bitblastPref1X64Cert.append bitblastCertX64S2
    (mod := bitblastPref2ModX64)
    (by exact List.take_add (l := bitblastFlatMod.fns) (i := 22) (j := 11))
    (by t_kernel_rfl)

/-- Prefix certificate `[0, 44)` (`S0..S3`). -/
@[expose] noncomputable def bitblastPref3X64Cert :=
  bitblastPref2X64Cert.append bitblastCertX64S3
    (mod := bitblastPref3ModX64)
    (by exact List.take_add (l := bitblastFlatMod.fns) (i := 33) (j := 11))
    (by t_kernel_rfl)

/-- Prefix certificate `[0, 54)` (`S0..S4`). -/
@[expose] noncomputable def bitblastPref4X64Cert :=
  bitblastPref3X64Cert.append bitblastCertX64S4
    (mod := bitblastPref4ModX64)
    (by exact List.take_add (l := bitblastFlatMod.fns) (i := 44) (j := 10))
    (by t_kernel_rfl)

/-- Zero-recompilation SysV x86-64 Bitblast tail certificate (`64` fns, `S0..S5`). -/
@[expose] noncomputable def bitblastTailX64Cert :=
  bitblastPref4X64Cert.append bitblastCertX64S5
    (mod := bitblastFlatMod)
    (by exact (List.take_append_drop 54 bitblastFlatMod.fns).symm)
    (by t_kernel_rfl)

/-- Closed `123`-function SysV x86-64 `LinkedCert` (`KissatPlainCert.plainCert` + `bitblast`,
`0` Kissat recompilation, `0` externs, `0` exits). -/
@[expose] noncomputable def bitblastX64Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      bitblastLinkedMod [] [] 0 2048 :=
  KissatPlainCert.plainCert.append bitblastTailX64Cert
    bitblastLinkedMod_fns_flat_eq (by t_kernel_rfl)

private theorem bitblastLinkedMod_x64_legal_check :
    checkLegalSigAll x64LegalTarget bitblastLinkedMod.fns = true := by
  t_kernel_rfl

theorem bitblastX64_legalSigAll : LegalSigAll x64LegalTarget bitblastLinkedMod.fns :=
  legalSigAll_of_check bitblastLinkedMod_x64_legal_check

private theorem bvSolveBytesFn_mem_linked :
    bvSolveBytesFn ∈ bitblastLinkedMod.fns :=
  List.mem_append_right _
    (List.mem_of_getElem? (rfl : bitblastModule.fns[63]? = some bvSolveBytesFn))

/-- `x64Target.Defined` + `x64Target.FnSpec` for `bv_solve_bytes` on any legal SysV x86-64
host embedding `bitblastX64Cert.code`. -/
theorem bitblastX64_bv_solve_bytes_fnSpec [hh : x64Target.mach.Host]
    (k₀ : Nat) (hc : bitblastX64Cert.code.IsInfixAt hh.prog k₀)
    (hu : x64Target.LabelsUnique hh) :
    x64Target.Defined hh "bv_solve_bytes" ∧
    x64Target.FnSpec hh "bv_solve_bytes"
      (bitblastLinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (bitblastX64Cert.bound "bv_solve_bytes") 0 :=
  bitblastX64Cert.fnSpec_noExit_of_legalSigAll hh bitblastLinkedEnv k₀ hc hu
    bitblastLinkedMod_checkAcyclic bitblastLinkedMod_wf bitblastX64_legalSigAll
    bitblastLinkedEnv_sound bvSolveBytesFn_mem_linked
    (fun args m Q X X' h => bitblastLinkedEnv_noExit _ _ _ args m Q X X' h)

/-- Closed `Defined` + `FnSpec` for `bv_solve_bytes` on `bitblastX64Cert.host`. -/
theorem bitblastX64_host_bv_solve_bytes_fnSpec :
    x64Target.Defined bitblastX64Cert.host "bv_solve_bytes" ∧
    x64Target.FnSpec bitblastX64Cert.host "bv_solve_bytes"
      (bitblastLinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (bitblastX64Cert.bound "bv_solve_bytes") 0 :=
  bitblastX64Cert.fnSpec_host_of_legalSigAll bitblastLinkedEnv
    bitblastLinkedMod_checkAcyclic bitblastLinkedMod_wf bitblastX64_legalSigAll
    bitblastLinkedEnv_sound bvSolveBytesFn_mem_linked
    (fun args m Q X X' h => bitblastLinkedEnv_noExit _ _ _ args m Q X X' h)

/-- End-to-end SysV x86-64 machine-code UNSAT soundness for `bv_solve_bytes`: returning
`rax = 20#64` certifies `BVLogicalExpr.Unsat` for any parsed `BVP1` bytecode input. -/
theorem bitblastX64_bv_solve_bytes_unsat_sound [hh : x64Target.mach.Host]
    (k₀ : Nat) (hc : bitblastX64Cert.code.IsInfixAt hh.prog k₀)
    (hu : x64Target.LabelsUnique hh)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hargs : x64Target.ArgsIn (as := [i64, i64, i64, i64, i64])
      (progPtr, progLen, workPtr, workCap, fuel, ()) s)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (bitblastX64Cert.bound "bv_solve_bytes"))
          (bitblastX64Cert.bound "bv_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 hh.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (st.data.regs.get64 .rax = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            st.data.regs.get64 .rax = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (bitblastX64Cert.bound "bv_solve_bytes"))
              (bitblastX64Cert.bound "bv_solve_bytes" + 8) ⋆ R))
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
    (x64_of_returns (bitblastX64_bv_solve_bytes_fnSpec k₀ hc hu).2 hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', ⟨r, _⟩, m', ⟨hm', hunsat, htriv⟩, hrets, hdm⟩
  have hreg : st.data.regs.get64 .rax = r := x64Init.retsIn_singleton r st.data hrets
  exact ⟨hpc, hcs, hsp', m', hm', fun hr20 => hunsat (hreg ▸ hr20),
    fun htr => hreg.trans (htriv htr), hdm⟩

/-- Closed specialization of `bitblastX64_bv_solve_bytes_unsat_sound` to
`bitblastX64Cert.host`. -/
theorem bitblastX64_host_bv_solve_bytes_unsat_sound
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hargs : x64Target.ArgsIn (as := [i64, i64, i64, i64, i64])
      (progPtr, progLen, workPtr, workCap, fuel, ()) s)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (bitblastX64Cert.bound "bv_solve_bytes"))
          (bitblastX64Cert.bound "bv_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (x64Target.mach.step bitblastX64Cert.host)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (st.data.regs.get64 .rax = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            st.data.regs.get64 .rax = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (bitblastX64Cert.bound "bv_solve_bytes"))
              (bitblastX64Cert.bound "bv_solve_bytes" + 8) ⋆ R))
      (x64Target.mach.mkState s
        (x64Target.mach.labelAddr bitblastX64Cert.host "bv_solve_bytes")) :=
  bitblastX64_bv_solve_bytes_unsat_sound (hh := bitblastX64Cert.host) 0
    bitblastX64Cert.code_infix_host bitblastX64Cert.labelsUnique
    progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm hargs hsp hmem

/-- Concrete SysV x86-64 `Mem 64` `Eventually` non-vacuity witness on `nvProgBytes`
(`BCONST false` -> `rax = 20#64` and `prog.Unsat`). -/
theorem bitblastX64_nv_unsat_run :
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (nvSlabPtr, nvProgLen, nvSlabWorkPtr, nvWorkCap, nvFuel, ())
    Eventually (x64Target.mach.step bitblastX64Cert.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        ∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat)
      (x64Target.mach.mkState
        (x64Init.initState (bitblastX64Cert.bound "bv_solve_bytes") nvSlabBytes args)
        (x64Target.mach.labelAddr bitblastX64Cert.host "bv_solve_bytes")) := by
  intro args
  let Q : LeanQbe.T.Post [i64] := fun (r, ()) _ =>
    r = 20#64 ∧ ∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat
  have hspec := bitblastLinked_bvSolveBytesSpec
    (nvSlab_bvSolveBytesSpec Q (fun _ _ _ _ => False) (fun _ _ hu => ⟨rfl, hu⟩))
  refine bitblastX64Cert.run_fnSpec x64Init bitblastX64_host_bv_solve_bytes_fnSpec.2
    nvSlabBytes args nvSlabBytes_le_8192 (by decide) hspec (fun st h => ?_) (by decide)
  rcases h with ⟨hpc, ⟨⟨r, _⟩, m', ⟨hr20, hu⟩, hrets, _⟩⟩ | ⟨_, _, _, _, hf, _⟩
  · subst hr20
    exact ⟨hpc, x64Init.retsIn_singleton 20#64 (x64Target.mach.data st) hrets, hu⟩
  · exact False.elim hf

end LeanQbeTest.T.BitblastCertX64
