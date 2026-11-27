module

public import LeanQbe.T.Amd64.BenchAbi
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Examples.Bignum

/-!
# Curve25519 Bignum Kernels on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.Bignum

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.Bignum LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Amd64 Kraken

splice_module_hints mul4x4Hints (x64Target.toIsa) x64LegalTarget mul4x4Module.fns
splice_module_hints addMod25519Hints (x64Target.toIsa) x64LegalTarget addMod25519Module.fns
splice_module_hints subMod25519Hints (x64Target.toIsa) x64LegalTarget subMod25519Module.fns

/-! ## 1. Compiled Kernel Certificates & Directive Inspection -/

theorem mul4x4_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      mul4x4Module.fns mul4x4Hints 2048 = true := by t_kernel_rfl

theorem addMod25519_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      addMod25519Module.fns addMod25519Hints 2048 = true := by t_kernel_rfl

theorem subMod25519_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      subMod25519Module.fns subMod25519Hints 2048 = true := by t_kernel_rfl

/-- Single kernel evaluation of `mul4x4` for SysV x64. -/
@[expose] def mul4x4Compiled :
    Compiled x64Target x64LegalTarget [] [] 0 mul4x4Module.fns mul4x4Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 mul4x4Module.fns mul4x4Hints 2048 mul4x4_check

/-- Single kernel evaluation of `addMod25519` for SysV x64. -/
@[expose] def addMod25519Compiled :
    Compiled x64Target x64LegalTarget [] [] 0 addMod25519Module.fns addMod25519Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 addMod25519Module.fns addMod25519Hints 2048 addMod25519_check

/-- Single kernel evaluation of `subMod25519` for SysV x64. -/
@[expose] def subMod25519Compiled :
    Compiled x64Target x64LegalTarget [] [] 0 subMod25519Module.fns subMod25519Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 subMod25519Module.fns subMod25519Hints 2048 subMod25519_check

meta def isMulxDir : Directive → Bool
  | .instr (.regular _ _ (.mulx _ _ _)) => true | _ => false
meta def isAdcxDir : Directive → Bool
  | .instr (.regular _ _ (.adcx _ _)) => true | _ => false
meta def isAdoxDir : Directive → Bool
  | .instr (.regular _ _ (.adox _ _)) => true | _ => false
meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true | _ => false

#guard (mul4x4Compiled.code.filter isMulxDir).length == 11
#guard (mul4x4Compiled.code.filter isAdcxDir).length == 12
#guard (mul4x4Compiled.code.filter isAdoxDir).length == 12
#guard (mul4x4Compiled.code.filter isSetccDir).length == 0

/-! ## 2. Source Support & Module `FnSpec` -/

private theorem bignumFns_supportsSource_all :
    [mul4x4Fn, addMod25519Fn, subMod25519Fn].all
      (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for `mul4x4Module` on `x64Target`. -/
theorem mul4x4_module_fnspec (k₀ : Nat)
    (hc : mul4x4Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ mul4x4Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (bignumEnv f.name f.as f.rs)
        (mul4x4Compiled.bound f.name) 0 := by
  simp only [mul4x4Module, List.mem_singleton] at hf; subst hf
  exact bignum_single_fnspec_gen mul4x4Compiled hh mul4x4Module_checkAcyclic mul4x4_wf (by simp)
    (supportsAll_to_forall bignumFns_supportsSource_all) (mul4x4_correct bignumEnv)
    k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-- Closed `FnSpec` for `addMod25519Module` on `x64Target`. -/
theorem addMod25519_module_fnspec (k₀ : Nat)
    (hc : addMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ addMod25519Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (bignumEnv f.name f.as f.rs)
        (addMod25519Compiled.bound f.name) 0 := by
  simp only [addMod25519Module, List.mem_singleton] at hf; subst hf
  exact bignum_single_fnspec_gen addMod25519Compiled hh addMod25519Module_checkAcyclic
    addMod25519_wf (by simp) (supportsAll_to_forall bignumFns_supportsSource_all)
    (addMod25519_correct bignumEnv) k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-- Closed `FnSpec` for `subMod25519Module` on `x64Target`. -/
theorem subMod25519_module_fnspec (k₀ : Nat)
    (hc : subMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ subMod25519Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (bignumEnv f.name f.as f.rs)
        (subMod25519Compiled.bound f.name) 0 := by
  simp only [subMod25519Module, List.mem_singleton] at hf; subst hf
  exact bignum_single_fnspec_gen subMod25519Compiled hh subMod25519Module_checkAcyclic
    subMod25519_wf (by simp) (supportsAll_to_forall bignumFns_supportsSource_all)
    (subMod25519_correct bignumEnv) k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-! ## 3. Closed Kraken x64 Correctness Theorems -/

/-- End-to-end correctness of compiled `mul4x4` on Kraken x64. -/
theorem mul4x4_x64_correct (k₀ : Nat)
    (hc : mul4x4Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 8)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : s.regs.get64 .rdi = out) (hpa : s.regs.get64 .rsi = pa)
    (hpb : s.regs.get64 .rdx = pb) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (mul4x4Compiled.bound "mul4x4"))
          (mul4x4Compiled.bound "mul4x4") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
            limbsVal rs = limbsVal as * limbsVal bs ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (mul4x4Compiled.bound "mul4x4"))
            (mul4x4Compiled.bound "mul4x4" + 8) ⋆ R))
      ⟨s, Labels.label "mul4x4"⟩ :=
  bignum_abi_correct x64BenchAbi hh mul4x4Compiled mul4x4Module_checkAcyclic mul4x4_wf (by simp)
    (supportsAll_to_forall bignumFns_supportsSource_all) (mul4x4_correct bignumEnv)
    (legalSig_three_i64 rfl) rfl ⟨rfl, rfl⟩ k₀ hc hu out pa pb as bs out0
    s ra R hout_reg hpa hpb hsp hmem (fun _ => mul4x4_spec_ok has hbs hout)

/-- End-to-end correctness of compiled `addMod25519` on Kraken x64. -/
theorem addMod25519_x64_correct (k₀ : Nat)
    (hc : addMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < p25519) (hb_lt : limbsVal bs < p25519)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : s.regs.get64 .rdi = out) (hpa : s.regs.get64 .rsi = pa)
    (hpb : s.regs.get64 .rdx = pb) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (addMod25519Compiled.bound "addMod25519"))
          (addMod25519Compiled.bound "addMod25519") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = (limbsVal as + limbsVal bs) % p25519 ∧ limbsVal rs < p25519 ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (addMod25519Compiled.bound "addMod25519"))
            (addMod25519Compiled.bound "addMod25519" + 8) ⋆ R))
      ⟨s, Labels.label "addMod25519"⟩ :=
  bignum_abi_correct x64BenchAbi hh addMod25519Compiled addMod25519Module_checkAcyclic
    addMod25519_wf (by simp) (supportsAll_to_forall bignumFns_supportsSource_all)
    (addMod25519_correct bignumEnv) (legalSig_three_i64 rfl) rfl ⟨rfl, rfl⟩ k₀ hc hu
    out pa pb as bs out0 s ra R hout_reg hpa hpb hsp hmem
    (fun _ => addMod25519_spec_ok has hbs hout ha_lt hb_lt)

/-- End-to-end correctness of compiled `subMod25519` on Kraken x64. -/
theorem subMod25519_x64_correct (k₀ : Nat)
    (hc : subMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < p25519) (hb_lt : limbsVal bs < p25519)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : s.regs.get64 .rdi = out) (hpa : s.regs.get64 .rsi = pa)
    (hpb : s.regs.get64 .rdx = pb) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (subMod25519Compiled.bound "subMod25519"))
          (subMod25519Compiled.bound "subMod25519") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = (if limbsVal bs ≤ limbsVal as then limbsVal as - limbsVal bs
                           else limbsVal as + p25519 - limbsVal bs) ∧
            limbsVal rs < p25519 ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (subMod25519Compiled.bound "subMod25519"))
            (subMod25519Compiled.bound "subMod25519" + 8) ⋆ R))
      ⟨s, Labels.label "subMod25519"⟩ :=
  bignum_abi_correct x64BenchAbi hh subMod25519Compiled subMod25519Module_checkAcyclic
    subMod25519_wf (by simp) (supportsAll_to_forall bignumFns_supportsSource_all)
    (subMod25519_correct bignumEnv) (legalSig_three_i64 rfl) rfl ⟨rfl, rfl⟩ k₀ hc hu
    out pa pb as bs out0 s ra R hout_reg hpa hpb hsp hmem
    (fun _ => subMod25519_spec_ok has hbs hout ha_lt hb_lt)

end Generic

/-! ## 4. Concrete SysV x64 Execution Witnesses -/

abbrev nvMulA : List (BitVec 64) := Examples.BenchmarkCertKit.nvMulA
abbrev nvMulB : List (BitVec 64) := Examples.BenchmarkCertKit.nvMulB
abbrev nvMulOut0 : List (BitVec 64) := Examples.BenchmarkCertKit.nvMulOut0
abbrev nvMulBytes : List UInt8 := Examples.BenchmarkCertKit.nvMulBytes

abbrev mul4x4Host : Host := mul4x4Compiled.host
@[expose] def mul4x4State0 : MachineData :=
  x64Init.initState (as := [i64, i64, i64]) (mul4x4Compiled.bound "mul4x4") nvMulBytes
    (0x1000#64, 0x1040#64, 0x1060#64, ())

attribute [local instance] mul4x4Host in
/-- Concrete execution of `mul4x4` on `p25519 * (2^192 + 2)` in `mul4x4Compiled.host`. -/
theorem mul4x4_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
            limbsVal rs = limbsVal nvMulA * limbsVal nvMulB ∧
            (array64 0x1000#64 rs ⋆ array64 0x1040#64 nvMulA ⋆ array64 0x1060#64 nvMulB) m') ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (mul4x4Compiled.bound "mul4x4"))
            (mul4x4Compiled.bound "mul4x4" + 8) ⋆ emp))
      ⟨mul4x4State0, Labels.label "mul4x4"⟩ :=
  bignum_abi_nonvacuous x64BenchAbi mul4x4Compiled mul4x4Module_checkAcyclic mul4x4_wf (by simp)
    (supportsAll_to_forall bignumFns_supportsSource_all) (mul4x4_correct bignumEnv)
    (legalSig_three_i64 rfl) rfl ⟨rfl, rfl⟩ nvMulBytes (0x1000#64, 0x1040#64, 0x1060#64, ())
    nvMulBytes_length nvMul_spec_ok

abbrev nvAddA : List (BitVec 64) := Examples.BenchmarkCertKit.nvAddA
abbrev nvAddB : List (BitVec 64) := Examples.BenchmarkCertKit.nvAddB
abbrev nv4Out0 : List (BitVec 64) := Examples.BenchmarkCertKit.nv4Out0
abbrev nvAddBytes : List UInt8 := Examples.BenchmarkCertKit.nvAddBytes

abbrev addMod25519Host : Host := addMod25519Compiled.host
@[expose] def addMod25519State0 : MachineData :=
  x64Init.initState (as := [i64, i64, i64]) (addMod25519Compiled.bound "addMod25519") nvAddBytes
    (0x1000#64, 0x1020#64, 0x1040#64, ())

attribute [local instance] addMod25519Host in
/-- Concrete execution of `addMod25519` wrapping `(p25519 - 1) + 20 = 19` mod `p25519`. -/
theorem addMod25519_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = 19 ∧
            (array64 0x1000#64 rs ⋆ array64 0x1020#64 nvAddA ⋆ array64 0x1040#64 nvAddB) m') ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (addMod25519Compiled.bound "addMod25519"))
            (addMod25519Compiled.bound "addMod25519" + 8) ⋆ emp))
      ⟨addMod25519State0, Labels.label "addMod25519"⟩ :=
  bignum_abi_nonvacuous x64BenchAbi addMod25519Compiled addMod25519Module_checkAcyclic
    addMod25519_wf (by simp) (supportsAll_to_forall bignumFns_supportsSource_all)
    (addMod25519_correct bignumEnv) (legalSig_three_i64 rfl) rfl ⟨rfl, rfl⟩
    nvAddBytes (0x1000#64, 0x1020#64, 0x1040#64, ()) nvAddBytes_length nvAdd_spec_ok

abbrev nvSubA : List (BitVec 64) := Examples.BenchmarkCertKit.nvSubA
abbrev nvSubB : List (BitVec 64) := Examples.BenchmarkCertKit.nvSubB
abbrev nvSubBytes : List UInt8 := Examples.BenchmarkCertKit.nvSubBytes

abbrev subMod25519Host : Host := subMod25519Compiled.host
@[expose] def subMod25519State0 : MachineData :=
  x64Init.initState (as := [i64, i64, i64]) (subMod25519Compiled.bound "subMod25519") nvSubBytes
    (0x1000#64, 0x1020#64, 0x1040#64, ())

attribute [local instance] subMod25519Host in
/-- Concrete execution of `subMod25519` wrapping `5 - 25 = p25519 - 20` mod `p25519`. -/
theorem subMod25519_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = p25519 - 20 ∧
            (array64 0x1000#64 rs ⋆ array64 0x1020#64 nvSubA ⋆ array64 0x1040#64 nvSubB) m') ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (subMod25519Compiled.bound "subMod25519"))
            (subMod25519Compiled.bound "subMod25519" + 8) ⋆ emp))
      ⟨subMod25519State0, Labels.label "subMod25519"⟩ :=
  bignum_abi_nonvacuous x64BenchAbi subMod25519Compiled subMod25519Module_checkAcyclic
    subMod25519_wf (by simp) (supportsAll_to_forall bignumFns_supportsSource_all)
    (subMod25519_correct bignumEnv) (legalSig_three_i64 rfl) rfl ⟨rfl, rfl⟩
    nvSubBytes (0x1000#64, 0x1020#64, 0x1040#64, ()) nvSubBytes_length nvSub_spec_ok

end LeanQbe.T.Amd64.Bignum
