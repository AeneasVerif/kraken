module

public import LeanQbe.T.Arm64.BenchAbi
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.ChaCha

/-!
# ChaCha20 Block (Scalarized) on AArch64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.ChaCha

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.ChaCha LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Arm64 Kraken

splice_module_hints chacha20Hints (armTarget.toIsa) armLegalTarget chacha20Module.fns

theorem compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0
      chacha20Module.fns chacha20Hints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of scalarized `chacha20Block` for AArch64 (`bound = 192`). -/
@[expose] def compiled :
    Compiled armTarget armLegalTarget [] [] 0 chacha20Module.fns chacha20Hints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 chacha20Module.fns chacha20Hints 2048 compiled_check

private theorem chacha20Fns_supportsSource_all :
    chacha20Module.fns.all (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

theorem chacha20Fns_supportsSource :
    ∀ f ∈ chacha20Module.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true :=
  supportsAll_to_forall chacha20Fns_supportsSource_all

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `chacha20Module` on `armTarget`. -/
theorem chacha20_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ chacha20Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (chacha20Env f.name f.as f.rs)
        (compiled.bound f.name) 0 :=
  chacha20_module_fnspec_gen compiled hh rfl chacha20Fns_supportsSource k₀ hc hu hf

/-- End-to-end correctness of compiled scalarized `chacha20Block` on Kraken AArch64. -/
theorem chacha20Block_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out inp : BitVec 64) (init : State) (old : List Row) (hold : old.length = 4)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout : (s.regs.getXReg .X0).toBitVec = out)
    (hinp : (s.regs.getXReg .X1).toBitVec = inp)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
        (compiled.bound "chacha20Block") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (array (t := v4i32) out (rfcChaCha20Core init).toRows ⋆
            array (t := v4i32) inp init.toRows) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
            (compiled.bound "chacha20Block") ⋆ R))
      ⟨s, Labels.label "chacha20Block"⟩ :=
  chacha20Block_abi_correct arm64BenchAbi hh compiled chacha20Fns_supportsSource
    k₀ hc hu out inp init old hold s ra R hout hinp ⟨hra, hsp⟩ hmem

end Generic

abbrev chachaHost : Host := compiled.host
attribute [local instance] chachaHost

abbrev chachaOut0 := LeanQbe.T.Examples.BenchmarkCertKit.chachaOut0
abbrev chachaInitBytes := LeanQbe.T.Examples.BenchmarkCertKit.chachaInitBytes

@[expose] def chachaState0 : MachineData :=
  armInit.initState (as := [i64, i64]) (compiled.bound "chacha20Block") chachaInitBytes
    (0x1000#64, 0x1040#64, ())

/-- Concrete RFC 8439 §2.3.2 execution witness of scalarized `chacha20Block` in
`compiled.host`. -/
theorem rfc8439_vector_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        st.data.dmem.loadBytes 0x1000#64 64 = some rfc8439_expected_bytes ∧
        ∃ res : State,
          res.toWords = rfc8439_expected_words ∧ res.toBytes = rfc8439_expected_bytes ∧
          (st.data.dmem =⋆
            (array (t := v4i32) 0x1000#64 res.toRows ⋆
              array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
            region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
              (compiled.bound "chacha20Block") ⋆ emp))
      ⟨chachaState0, Labels.label "chacha20Block"⟩ :=
  rfc8439_vector_abi_nonvacuous arm64BenchAbi compiled chacha20Fns_supportsSource

end LeanQbe.T.Arm64.ChaCha
