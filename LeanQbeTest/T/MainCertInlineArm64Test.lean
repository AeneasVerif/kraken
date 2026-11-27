module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbeTest.T.Common.Fixtures
public import Std.Sat.CNF
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbeTest.T.Common.Fixtures

/-!
# Certified Inlined Compilation Bridge Tests on AAPCS64 Arm64 (`MainCertInline`)

Arm64 counterpart to `LeanQbeTest.T.MainCertInlineTest`, testing `MainCertInline` end-to-end on
`armTarget`:
1. 4-function module `inlSrcMod` with `inline_mod! inlModB5` (`InlinePolicy.b5`) and `#guard`
   inlining assertions, 2-slice `compile_linked_chunks!` + `eval_prefix_ext!` +
   `LinkedCert.append` + `LinkedCert.castModule inlModB5.eq`, `Kraken.AArch64` `arm64_of_returns`,
   and closed `armInit` `Eventually` (`X0 = 85`, `cell64 0x1000 25`).
2. Kissat-shaped mini-module witness linking `X0 = 85` to `miniUnsatCnf.Unsat` on the inlined
   machine code.
3. Audits single-line standard-axiom `#print axioms`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainCertInlineArm64Test

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbeTest.T.Common.Fixtures

abbrev fnStep := fnStepInl
abbrev fnEntry := fnEntryInl

inline_mod! inlModB5 inlSrcMod InlinePolicy.b5 (compile := true)

def dummyFn : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

#guard (inlModB5.fns.getD 3 dummyFn).checkCallsOk [] []

theorem inlSrcMod_legalSig : LegalSigAll armLegalTarget inlSrcMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-! ## 2. Multi-slice `compile_linked_chunks!` + `castModule` + `arm64_of_returns` -/

def slice1Mod : Module := { fns := inlModB5.fns.take 2 }
def slice2Mod : Module := { fns := inlModB5.fns.drop 2 }

compile_linked_chunks! armB5Slice1
  armTarget armLayout armLegalTarget armLabelClean slice1Mod 1 (flat := true)

eval_prefix_ext! extArmB5Slice1 armTarget armLegalTarget (inlModB5.fns.take 2) (flat := true)

compile_linked_chunks! armB5Slice2
  armTarget armLayout armLegalTarget armLabelClean slice2Mod 1 (ext := extArmB5Slice1)
  (flat := true)

noncomputable def armCertB5Mat :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean inlModB5 [] [] 0 2048 :=
  armB5Slice1.append armB5Slice2
    (by exact (List.take_append_drop 2 inlModB5.fns).symm)
    (by t_kernel_rfl)

noncomputable def armCertB5 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (inlSrcMod.optInlinePolicy InlinePolicy.b5) [] [] 0 2048 :=
  armCertB5Mat.castModule inlModB5.eq

theorem armCertB5_fnspec [hh : Host] (k₀ : Nat)
    (hc : armCertB5.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ inlSrcMod.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (inlΓ f.name f.as f.rs) (armCertB5.bound f.name) 0 :=
  armCertB5.fnSpec_noExit_of_legalSigAll_optInlinePolicy hh inlΓ k₀ hc hu
    inlSrcMod_modOk inlSrcMod_legalSig hf (inlΓ_noExit f.name f.as f.rs)

theorem entry_arm64_ev [hh : Host] (k₀ : Nat)
    (hc : armCertB5.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p d v₀ : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = p) (hx1 : (s.regs.getXReg .X1).toBitVec = d)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v₀ ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armCertB5.bound "entry"))
        (armCertB5.bound "entry") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = entryVal v₀ d)
      ⟨s, Labels.label "entry"⟩ := by
  have hfn : armTarget.FnSpec hh "entry" entrySpec (armCertB5.bound "entry") 0 :=
    (armCertB5_fnspec k₀ hc hu (f := fnEntry) (by simp [inlSrcMod])).2
  have hargs : armTarget.ArgsIn (as := [i64, i64]) (p, d, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hx0⟩
      (.cons ⟨by decide, by simpa [get_reg] using hx1⟩ .nil)⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨mCell, f, hu2, hd2, hmCell, hf⟩, hmRest⟩ := hmem
  have hmEq : s.dmem =⋆ Eq mCell ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armCertB5.bound "entry"))
        (armCertB5.bound "entry") ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨mCell, f, hu2, hd2, rfl, hf⟩, hmRest⟩
  have hspec : entrySpec (p, d, ()) mCell (fun r m' => r = (entryVal v₀ d, ()) ∧ True)
      (fun _ _ _ _ => False) :=
    ⟨v₀, emp, by rwa [sep_emp], fun _ _ => ⟨rfl, trivial⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmEq)
  rintro st ⟨hpc, _, _, _, _, ⟨rfl, _⟩, hrets, _⟩
  have hx0' : (st.data.regs.getXReg .X0).toBitVec = entryVal v₀ d := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton (entryVal v₀ d) st.data hrets
  exact ⟨hpc, hx0'⟩

def initMemBytes : List UInt8 := bytes64 [20#64]

private theorem initMemBytes_len : initMemBytes.length ≤ 8192 := by
  simp [initMemBytes, bytes64_length]

private theorem initMemBytes_cell :
    (cell64 0x1000#64 20#64 ⋆ emp) (initMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [20#64] (by decide)
  simpa [initMemBytes] using h

theorem arm_run_b5_sep :
    Eventually (armTarget.mach.step armCertB5.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 85#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (cell64 0x1000#64 25#64 ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (armCertB5.bound "entry") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (armCertB5.bound "entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr armCertB5.host "entry")) := by
  refine armCertB5.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy armInit inlΓ
    inlSrcMod_modOk inlSrcMod_legalSig (f := fnEntry) (by simp [inlSrcMod]) rfl
    (inlΓ_noExit "entry" [i64, i64] [i64]) initMemBytes (0x1000#64, 5#64, ()) 85#64
    (cell64 0x1000#64 25#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (85#64, ()) ∧ (cell64 0x1000#64 25#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨20#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa using hm'

/-! ## 3. Mini UNSAT Witness (`cnf.Unsat` from Inlined Machine Code) -/

theorem arm_run_b5_unsat :
    Eventually (armTarget.mach.step armCertB5.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 85#64 ∧
        miniUnsatCnf.Unsat)
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (armCertB5.bound "entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr armCertB5.host "entry")) :=
  eventually_weaken _ _ _ _
    (fun _ h => ⟨h.1, h.2.1, miniUnsatCnf_unsat⟩) arm_run_b5_sep

/-! ## 4. Axiom Audit -/

#print axioms armCertB5
#print axioms armCertB5_fnspec
#print axioms entry_arm64_ev
#print axioms arm_run_b5_sep
#print axioms arm_run_b5_unsat

end LeanQbeTest.T.MainCertInlineArm64Test
