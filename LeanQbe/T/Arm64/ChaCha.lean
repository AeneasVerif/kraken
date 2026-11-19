module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.ChaCha
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.ChaCha

/-!
# ChaCha20 Block (Scalarized) on AArch64 (`T14`)

Instantiates `chacha20Module` (`chacha20Block`) on `armTarget` (`armLegalTarget`, `armLayout`,
`armLabelClean`), where `armLegalTarget` scalarizes `v4i32` rows down to `i32` lanes:
* external hint splicing (`chacha20Hints`) via `splice_module_hints`;
* single-kernel-reduction compilation check (`t_kernel_rfl`, default 200k heartbeats);
* `chacha20_module_fnspec` and closed Kraken AArch64 theorem `chacha20Block_arm64_correct`;
* concrete RFC 8439 §2.3.2 execution witness `rfc8439_vector_arm64_nonvacuous` verifying the exact
  16-word / 64-byte output in `dmem` via `armInit`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.ChaCha

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.ChaCha LeanQbe.T.Arm64 Kraken

splice_module_hints chacha20Hints (armTarget.toIsa) armLegalTarget chacha20Module.fns

/-! ## 1. Compiled Kernel Certificate & Source Support -/

theorem compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0
      chacha20Module.fns chacha20Hints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of scalarized `chacha20Block` for AArch64 (`bound = 192`). -/
def compiled : Compiled armTarget armLegalTarget [] [] 0 chacha20Module.fns chacha20Hints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 chacha20Module.fns chacha20Hints 2048 compiled_check

private theorem chacha20Fns_supportsSource_all :
    chacha20Module.fns.all (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

theorem chacha20Fns_supportsSource :
    ∀ f ∈ chacha20Module.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true :=
  supportsAll_to_forall chacha20Fns_supportsSource_all

/-! ## 2. Generic `FnSpec` and Closed Kraken AArch64 Theorem -/

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `chacha20Module` on `armTarget`. -/
theorem chacha20_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ chacha20Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (chacha20Env f.name f.as f.rs)
        (compiled.bound f.name) 0 := by
  have hmem := hf
  simp only [chacha20Module, List.mem_singleton] at hmem; subst hmem
  exact compiled.fnSpec_noExit_id chacha20Module rfl hh chacha20Env k₀ hc hu
    chacha20Module_checkAcyclic
    (fun g hg => by
      simp only [chacha20Module, List.mem_singleton] at hg; subst hg; exact chacha20Block_wf)
    chacha20Fns_supportsSource
    (fun g hg => by
      simp only [chacha20Module, List.mem_singleton] at hg; subst hg
      exact chacha20Block_correct chacha20Env)
    hf rfl rfl (fun _ _ _ _ _ h => h)

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
      ⟨s, Labels.label "chacha20Block"⟩ := by
  have hargs : armTarget.ArgsIn (as := [i64, i64]) (out, inp, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hout⟩
      (.cons ⟨by decide, by simpa [get_reg] using hinp⟩ .nil)⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
        (compiled.bound "chacha20Block") ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn : armTarget.FnSpec hh "chacha20Block" chacha20BlockSpec
      (compiled.bound "chacha20Block") 0 :=
    (chacha20_module_fnspec k₀ hc hu List.mem_cons_self).2
  have hspec : chacha20BlockSpec (out, inp, ()) m
      (fun _ m' => (array (t := v4i32) out (rfcChaCha20Core init).toRows ⋆
        array (t := v4i32) inp init.toRows) m')
      (fun _ _ _ _ => False) :=
    ⟨init, old, emp, hold, by rw [sep_emp]; exact sep_ac hm,
      fun _ hm' => by rw [sep_emp] at hm'; exact sep_ac hm'⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', hP, _, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩

end Generic

/-! ## 3. Concrete RFC 8439 §2.3.2 Witness in `compiled.host` -/

private theorem rfc8439_expected_bytes_eq_bytesOf :
    bytesOf (t := v4i32) (rfcChaCha20Core rfc8439_test_init).toRows = rfc8439_expected_bytes := by
  decide

abbrev chachaHost : Host := compiled.host
attribute [local instance] chachaHost

def chachaOut0 : List Row := List.replicate 4 (mkRow 0#32 0#32 0#32 0#32)
def chachaInitBytes : List UInt8 := bytesOf (t := v4i32) (chachaOut0 ++ rfc8439_test_init.toRows)

private theorem chachaInitBytes_length : chachaInitBytes.length ≤ 8192 := by
  simp [chachaInitBytes, bytesOf_length, chachaOut0, State.toRows, Ty.bytes, Ty.size]

def chachaState0 : MachineData :=
  armInit.initState (as := [i64, i64]) (compiled.bound "chacha20Block") chachaInitBytes
    (0x1000#64, 0x1040#64, ())

/-- Concrete RFC 8439 §2.3.2 execution witness of scalarized `chacha20Block` in `compiled.host`,
verifying both the 16-word separation-logic state and the exact 64-byte output in `dmem`. -/
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
      ⟨chachaState0, Labels.label "chacha20Block"⟩ := by
  have hfn : armTarget.FnSpec chachaHost "chacha20Block" chacha20BlockSpec
      (compiled.bound "chacha20Block") 0 :=
    (chacha20_module_fnspec 0 compiled.code_infix_host compiled.labelsUnique
      List.mem_cons_self).2
  have hm0 : (array (t := v4i32) 0x1000#64 chachaOut0 ⋆
      array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows)
      (chachaInitBytes.At 0x1000#64) := by
    have ha := array_bytes (t := v4i32) 0x1000#64 (chachaOut0 ++ rfc8439_test_init.toRows)
      (by simp [chachaOut0, State.toRows, Ty.bytes, Ty.size])
    rw [array_append] at ha
    simpa only [chachaInitBytes, chachaOut0, List.length_replicate, Ty.bytes, Ty.size,
      Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
      using ha
  have hspec : chacha20BlockSpec (0x1000#64, 0x1040#64, ()) (chachaInitBytes.At 0x1000#64)
      (fun _ m' =>
        (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
          array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) m')
      (fun _ _ _ _ => False) :=
    ⟨rfc8439_test_init, chachaOut0, emp, rfl, by rw [sep_emp]; exact sep_ac hm0,
      fun _ hm' => by rw [sep_emp] at hm'; exact sep_ac hm'⟩
  refine armInit.run_fnSpec compiled hfn chachaInitBytes (0x1000#64, 0x1040#64, ())
    chachaInitBytes_length rfl hspec ?_
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hdmem : st.data.dmem =⋆
        (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
          array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
        region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
          (compiled.bound "chacha20Block") ⋆ emp := by
      simpa only [Target.Exit, armTarget, armFrameSpec, armFrame, armInit, Nat.add_zero] using
        sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'
    have hdmem_ac : (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
        (array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
            (compiled.bound "chacha20Block") ⋆ emp)) st.data.dmem := sep_ac hdmem
    have hflat : (Eq (rfc8439_expected_bytes.At 0x1000#64) ⋆
        (array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
            (compiled.bound "chacha20Block") ⋆ emp)) st.data.dmem := by
      refine sep_mono (fun _ h => ?_) hdmem_ac
      rw [← rfc8439_expected_bytes_eq_bytesOf]
      exact (array_eq_bytesOf 0x1000#64 _ (by simp [State.toRows, Ty.bytes, Ty.size]) h).symm
    have hload := loadBytes_sep_At (by decide) hflat
    refine ⟨hpc, hload, rfcChaCha20Core rfc8439_test_init,
      rfc8439_test_vector_words, rfc8439_test_vector_bytes, hdmem⟩
  · exact hx.elim

end LeanQbe.T.Arm64.ChaCha
