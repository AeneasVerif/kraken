module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
import LeanQbe.T.Logic.MemLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.ChaCha

/-!
# ChaCha20 Block (`v4i32` SIMD) on SysV x64
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.ChaCha

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.ChaCha LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Amd64 Kraken

splice_module_hints chacha20Hints (x64Target.toIsa) x64LegalTarget chacha20Module.fns

theorem compiled_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      chacha20Module.fns chacha20Hints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of `chacha20Block` for SysV x64 (`v4i32` SIMD, `bound = 8`). -/
def compiled : Compiled x64Target x64LegalTarget [] [] 0 chacha20Module.fns chacha20Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 chacha20Module.fns chacha20Hints 2048 compiled_check

private theorem chacha20Fns_supportsSource_all :
    chacha20Module.fns.all (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

theorem chacha20Fns_supportsSource :
    ∀ f ∈ chacha20Module.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  supportsAll_to_forall chacha20Fns_supportsSource_all

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `chacha20Module` on `x64Target`. -/
theorem chacha20_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ chacha20Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (chacha20Env f.name f.as f.rs)
        (compiled.bound f.name) 0 :=
  chacha20_module_fnspec_gen compiled hh rfl chacha20Fns_supportsSource k₀ hc hu hf

/-- End-to-end correctness of compiled `chacha20Block` on Kraken x64. -/
theorem chacha20Block_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out inp : BitVec 64) (init : State) (old : List Row) (hold : old.length = 4)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout : s.regs.get64 .rdi = out) (hinp : s.regs.get64 .rsi = inp)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
          (compiled.bound "chacha20Block") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (array (t := v4i32) out (rfcChaCha20Core init).toRows ⋆
            array (t := v4i32) inp init.toRows) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
            (compiled.bound "chacha20Block" + 8) ⋆ R))
      ⟨s, Labels.label "chacha20Block"⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (out, inp, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hout⟩ (.cons ⟨by decide, by simpa using hinp⟩ .nil)⟩
  obtain ⟨m, hm, hmEq⟩ := sep_extract_eq hmem
  have hfn : x64Target.FnSpec hh "chacha20Block" chacha20BlockSpec
      (compiled.bound "chacha20Block") 0 :=
    (chacha20_module_fnspec k₀ hc hu List.mem_cons_self).2
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns hfn (chacha20_spec_ok hold hm) s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', hP, _, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩

end Generic

abbrev chachaHost : Host := compiled.host
attribute [local instance] chachaHost

abbrev chachaOut0 := LeanQbe.T.Examples.BenchmarkCertKit.chachaOut0
abbrev chachaInitBytes := LeanQbe.T.Examples.BenchmarkCertKit.chachaInitBytes

def chachaState0 : MachineData :=
  x64Init.initState (as := [i64, i64]) (compiled.bound "chacha20Block") chachaInitBytes
    (0x1000#64, 0x1040#64, ())

/-- Concrete RFC 8439 §2.3.2 execution witness of `chacha20Block` in `compiled.host`. -/
theorem rfc8439_vector_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        st.data.dmem.loadBytes 0x1000#64 64 = some rfc8439_expected_bytes ∧
        ∃ res : State,
          res.toWords = rfc8439_expected_words ∧ res.toBytes = rfc8439_expected_bytes ∧
          (st.data.dmem =⋆
            (array (t := v4i32) 0x1000#64 res.toRows ⋆
              array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
            region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
              (compiled.bound "chacha20Block" + 8) ⋆ emp))
      ⟨chachaState0, Labels.label "chacha20Block"⟩ := by
  have hfn := (chacha20_module_fnspec 0 compiled.code_infix_host compiled.labelsUnique
    List.mem_cons_self).2
  refine eventually_weaken _ _ _ _ ?_
    (rfc8439_vector_target_nonvacuous x64Init compiled hfn rfl)
  rintro st ⟨hpc, hld, res, hw, hb, hm⟩
  refine ⟨hpc, hld, res, hw, hb, ?_⟩
  simpa only [Target.Exit, x64Target, x64FrameTarget, x64FramePreds, x64Frame, x64Init] using hm

end LeanQbe.T.Amd64.ChaCha
