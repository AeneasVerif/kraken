module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.LratBytesLemmas
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.LratBytes

/-!
# Untrusted-bytes LRAT proof checker (`lratBytesFns`) on AArch64 (`T16`)

Instantiates the typed-IR 6-function untrusted-bytes DIMACS + Binary LRAT checker module
`lratBytesModule` on `armTarget` (`armLegalTarget`, `armLayout`, `armLabelClean`) with:
* `lratBytesHints` via `splice_module_hints`;
* `compiled_check : checkCompile ... = true` proved in a single kernel reduction (`t_kernel_rfl`);
* `lrat_bytes_module_fnspec` over arbitrary Kraken `Host` instances;
* closed Kraken AArch64 correctness theorems `lrat_check_bytes_arm64_of_fnspec`,
  `lrat_check_bytes_arm64_correct`, and `lrat_check_bytes_arm64_unsat`;
* concrete non-vacuous accepting (`x0 = 1` + `nvBytesCnf.Unsat`) and rejecting (`x0 = 0`)
  execution witnesses on `compiled.host` via `armInit`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.LratBytes

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Arm64 Kraken

splice_module_hints lratBytesHints (armTarget.toIsa) armLegalTarget lratBytesFns

theorem compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 lratBytesFns lratBytesHints 2048 =
      true := by
  t_kernel_rfl

/-- Single kernel evaluation of the compiler on `lratBytesFns` for AArch64. -/
def compiled : Compiled armTarget armLegalTarget [] [] 0 lratBytesFns lratBytesHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean [] [] 0
    lratBytesFns lratBytesHints 2048 compiled_check

private theorem lratBytesFns_supportsSource_all :
    lratBytesFns.all (fun f => (f.opt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

theorem lratBytesFns_supportsSource :
    ∀ f ∈ lratBytesModule.fns, (f.opt).body.supportsSource armLegalTarget = true :=
  fun f hf => List.all_eq_true.mp lratBytesFns_supportsSource_all f hf

section Generic
variable [hh : Host]

private theorem mk_lrat_bytes_module_fnspec
    (mainSpec : Spec [i64, i64, i64, i64, i64, i64] [i64])
    (hsound : ∀ f ∈ lratBytesFns, ∀ args m Q X,
      mkLratBytesEnv mainSpec f.name f.as f.rs args m Q X →
      Func.spec (mkLratBytesEnv mainSpec) f.body args m Q X)
    (hnoex_main : ∀ args m Q X X', mainSpec args m Q X → mainSpec args m Q X')
    (k₀ : Nat) (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ lratBytesModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (mkLratBytesEnv mainSpec f.name f.as f.rs)
        (compiled.bound f.name) 0 := by
  obtain ⟨hdef, hspec⟩ := compiled.fnSpec lratBytesModule rfl hh (mkLratBytesEnv mainSpec) k₀
    hc hu lratBytesModule_checkAcyclic lratBytesFns_wf lratBytesFns_supportsSource hsound
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) hf
  have hmem := hf
  simp only [lratBytesModule, lratBytesFns, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs, hnoex⟩ :
      armLegalTarget.legalSig f.as = f.as ∧ armLegalTarget.legalSig f.rs = f.rs ∧
        (∀ args m Q X X',
          mkLratBytesEnv mainSpec f.name f.as f.rs args m Q X →
          mkLratBytesEnv mainSpec f.name f.as f.rs args m Q X') := by
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
    · exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
    · exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
    · exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
    · exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
    · exact ⟨rfl, rfl, hnoex_main⟩
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

/-- Closed `FnSpec` for every function in `lratBytesModule` on `armTarget`. -/
theorem lrat_bytes_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ lratBytesModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (lratBytesEnv f.name f.as f.rs) (compiled.bound f.name) 0 :=
  mk_lrat_bytes_module_fnspec lratCheckBytesSpec lratBytesEnv_sound
    (fun _ _ _ _ _ h => h) k₀ hc hu hf

private theorem mk_lrat_bytes_entry_fnspec
    (mainSpec : Spec [i64, i64, i64, i64, i64, i64] [i64])
    (hsound : ∀ f ∈ lratBytesFns, ∀ args m Q X,
      mkLratBytesEnv mainSpec f.name f.as f.rs args m Q X →
      Func.spec (mkLratBytesEnv mainSpec) f.body args m Q X)
    (hnoex_main : ∀ args m Q X X', mainSpec args m Q X → mainSpec args m Q X')
    (k₀ : Nat) (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    armTarget.FnSpec hh "lrat_check_bytes" mainSpec (compiled.bound "lrat_check_bytes") 0 := by
  simpa [mkLratBytesEnv] using
    (mk_lrat_bytes_module_fnspec mainSpec hsound hnoex_main k₀ hc hu
      (f := ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩)
      (by simp [lratBytesModule, lratBytesFns])).2

/-- Lifting any `FnSpec` for `"lrat_check_bytes"` at stack bound `b` and contract
`lratCheckBytesSpec` to the closed Kraken-AArch64 statement. -/
theorem lrat_check_bytes_arm64_of_fnspec {b : Nat}
    (hfnspec : armTarget.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec b 0)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨
          (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ := by
  have hargs : armTarget.ArgsIn (as := [i64, i64, i64, i64, i64, i64])
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len, ()) s :=
    ⟨_, rfl,
      .cons ⟨by decide, by simpa [get_reg] using hx0⟩
        (.cons ⟨by decide, by simpa [get_reg] using hx1⟩
          (.cons ⟨by decide, by simpa [get_reg] using hx2⟩
            (.cons ⟨by decide, by simpa [get_reg] using hx3⟩
              (.cons ⟨by decide, by simpa [get_reg] using hx4⟩
                (.cons ⟨by decide, by simpa [get_reg] using hx5⟩ .nil)))))⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hspec : lratCheckBytesSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len, ())
      m
      (fun rs m' => ∃ r : BitVec 64, rs = (r, ()) ∧ (r = 0 ∨ r = 1) ∧
        (r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) m')
      (fun _ _ _ _ => False) :=
    ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, emp,
      rfl, hcnf, hprf, hwork, by rwa [sep_emp],
      fun r m' hr01 hunsat hm' => ⟨r, rfl, hr01, hunsat, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfnspec hspec s ra R hargs hra hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', ⟨r, rfl, hr01, hunsat, hm'⟩, hrets, hmem'⟩
  have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton r st.data hrets
  rw [← hx0'] at hr01 hunsat
  exact ⟨hpc, hr01, hunsat, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem'⟩

/-- Closed end-to-end AArch64 theorem for `lrat_check_bytes`. -/
theorem lrat_check_bytes_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
        (compiled.bound "lrat_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨
          (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
            (compiled.bound "lrat_check_bytes") ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_arm64_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu
        (f := ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩)
        (by simp [lratBytesModule, lratBytesFns])).2)
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem

/-- Trivial-postcondition end-to-end Kraken-AArch64 corollary for any `ValidDimacsCnf cnf`. -/
theorem lrat_check_bytes_arm64_unsat (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf : CNF Nat) (hvalid : ValidDimacsCnf cnf)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 (encodeDimacs cnf).length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
        region work_ptr work_len) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
        (compiled.bound "lrat_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨
          (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ ?_
    (lrat_check_bytes_arm64_correct k₀ hc hu cnf_ptr prf_ptr work_ptr (encodeDimacs cnf)
      prfBytes work_len hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem)
  have hparse := parseDimacs_encodeDimacs hvalid
  grind

end Generic

/-! ## Concrete AArch64 Executions in `compiled.host` (`x0 = 1` and `x0 = 0`) -/

abbrev lratBytesHost : Host := compiled.host
attribute [local instance] lratBytesHost

def lratBytesArgs (cnfBytes prfBytes : List UInt8) :
    Tup Val [i64, i64, i64, i64, i64, i64] :=
  (nvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
   nvPrfPtr cnfBytes, BitVec.ofNat 64 prfBytes.length,
   nvWorkPtr cnfBytes prfBytes, 512#64, ())

def lratBytesState (cnfBytes prfBytes : List UInt8) : MachineData :=
  armInit.initState (as := [i64, i64, i64, i64, i64, i64])
    (compiled.bound "lrat_check_bytes")
    (lratBytesPayload cnfBytes prfBytes) (lratBytesArgs cnfBytes prfBytes)

def lratBytesAcceptState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratAcceptBytes

/-- Concrete accepting execution of compiled `lrat_check_bytes` on Kraken AArch64. -/
theorem lrat_check_bytes_arm64_accepts :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1 ∧ nvBytesCnf.Unsat)
      ⟨lratBytesAcceptState0, Labels.label "lrat_check_bytes"⟩ := by
  have hfn : armTarget.FnSpec lratBytesHost "lrat_check_bytes" lratCheckBytesAcceptSpec
      (compiled.bound "lrat_check_bytes") 0 :=
    mk_lrat_bytes_entry_fnspec lratCheckBytesAcceptSpec lratBytesAcceptEnv_sound
      (fun _ _ _ _ _ h => h) 0 compiled.code_infix_host compiled.labelsUnique
  have hspec : lratCheckBytesAcceptSpec (lratBytesArgs nvDimacsBytes nvLratAcceptBytes)
      ((lratBytesPayload nvDimacsBytes nvLratAcceptBytes).At 0x1000#64)
      (fun rs _ => rs = (1, ()) ∧ nvBytesCnf.Unsat) (fun _ _ _ _ => False) :=
    ⟨nvCnfPtr, nvPrfPtr nvDimacsBytes, nvWorkPtr nvDimacsBytes nvLratAcceptBytes, emp,
      rfl, by simp [nvCnfPtr], by simp [nvPrfPtr, nvCnfPtr],
      by simp [nvWorkPtr, nvPrfPtr, nvCnfPtr],
      by rw [sep_emp]; exact lratBytesPayload_sep _ _ (by simp) (by simp),
      fun _ hu _ => ⟨rfl, hu⟩⟩
  refine armInit.run_fnSpec compiled hfn (lratBytesPayload nvDimacsBytes nvLratAcceptBytes)
    (lratBytesArgs nvDimacsBytes nvLratAcceptBytes)
    (by simp [lratBytesPayload_length]) (by decide) hspec ?_
  rintro st (⟨hpc, _, _, ⟨rfl, hu⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, hu⟩
    simpa [armInit, get_reg] using armInit.retsIn_singleton 1 _ hrets
  · exact hx.elim

def lratBytesRejectState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratRejectBytes

/-- Concrete rejecting execution of compiled `lrat_check_bytes` on Kraken AArch64. -/
theorem lrat_check_bytes_arm64_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0)
      ⟨lratBytesRejectState0, Labels.label "lrat_check_bytes"⟩ := by
  have hfn : armTarget.FnSpec lratBytesHost "lrat_check_bytes" lratCheckBytesRejectSpec
      (compiled.bound "lrat_check_bytes") 0 :=
    mk_lrat_bytes_entry_fnspec lratCheckBytesRejectSpec lratBytesRejectEnv_sound
      (fun _ _ _ _ _ h => h) 0 compiled.code_infix_host compiled.labelsUnique
  have hspec : lratCheckBytesRejectSpec (lratBytesArgs nvDimacsBytes nvLratRejectBytes)
      ((lratBytesPayload nvDimacsBytes nvLratRejectBytes).At 0x1000#64)
      (fun rs _ => rs = (0, ())) (fun _ _ _ _ => False) :=
    ⟨nvCnfPtr, nvPrfPtr nvDimacsBytes, nvWorkPtr nvDimacsBytes nvLratRejectBytes, emp,
      rfl, by simp [nvCnfPtr], by simp [nvPrfPtr, nvCnfPtr],
      by simp [nvWorkPtr, nvPrfPtr, nvCnfPtr],
      by rw [sep_emp]; exact lratBytesPayload_sep _ _ (by simp) (by simp),
      fun _ _ => rfl⟩
  refine eventually_weaken _ _ _ _ (fun st ⟨hpc, hx0⟩ =>
      ⟨hpc, by simpa [armInit, get_reg] using hx0⟩)
    (armInit.run_ret1_i64 compiled hfn (lratBytesPayload nvDimacsBytes nvLratRejectBytes)
      (lratBytesArgs nvDimacsBytes nvLratRejectBytes) 0
      (by simp [lratBytesPayload_length]) (by decide) hspec fun _ _ h => h)

end LeanQbe.T.Arm64.LratBytes
