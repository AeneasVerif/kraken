module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Examples.Bignum

/-!
# Curve25519 Bignum Kernels on SysV x64

Instantiates the typed-IR bignum modules (`mul4x4Module`, `addMod25519Module`, `subMod25519Module`)
on `x64Target` (`x64LegalTarget`, `x64Layout`, `x64LabelClean`) with:
* external hint splicing via `splice_module_hints`;
* single-kernel-reduction compilation checks (`t_kernel_rfl`, default 200k heartbeats);
* directive inspection verifying `mul4x4` uses `mulx`, `adcx`, `adox` with `setcc = 0`;
* closed `FnSpec` and Kraken x64 correctness theorems (`mul4x4_x64_correct`,
  `addMod25519_x64_correct`, `subMod25519_x64_correct`);
* concrete non-vacuous execution witnesses on `*.host` via `x64Init`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.Bignum

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.Bignum LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Amd64 Kraken

splice_module_hints mul4x4Hints (x64Target.toIsa) x64LegalTarget mul4x4Module.fns
splice_module_hints addMod25519Hints (x64Target.toIsa) x64LegalTarget addMod25519Module.fns
splice_module_hints subMod25519Hints (x64Target.toIsa) x64LegalTarget subMod25519Module.fns

/-! ## 1. Compiled Kernel Certificates & Directive Inspection -/

theorem mul4x4_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      mul4x4Module.fns mul4x4Hints 2048 = true := by
  t_kernel_rfl

theorem addMod25519_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      addMod25519Module.fns addMod25519Hints 2048 = true := by
  t_kernel_rfl

theorem subMod25519_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      subMod25519Module.fns subMod25519Hints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of `mul4x4` for SysV x64. -/
def mul4x4Compiled :
    Compiled x64Target x64LegalTarget [] [] 0 mul4x4Module.fns mul4x4Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 mul4x4Module.fns mul4x4Hints 2048 mul4x4_check

/-- Single kernel evaluation of `addMod25519` for SysV x64. -/
def addMod25519Compiled :
    Compiled x64Target x64LegalTarget [] [] 0 addMod25519Module.fns addMod25519Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 addMod25519Module.fns addMod25519Hints 2048 addMod25519_check

/-- Single kernel evaluation of `subMod25519` for SysV x64. -/
def subMod25519Compiled :
    Compiled x64Target x64LegalTarget [] [] 0 subMod25519Module.fns subMod25519Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 subMod25519Module.fns subMod25519Hints 2048 subMod25519_check

meta def isMulxDir : Directive → Bool
  | .instr (.regular _ _ (.mulx _ _ _)) => true
  | _ => false

meta def isAdcxDir : Directive → Bool
  | .instr (.regular _ _ (.adcx _ _)) => true
  | _ => false

meta def isAdoxDir : Directive → Bool
  | .instr (.regular _ _ (.adox _ _)) => true
  | _ => false

meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true
  | _ => false

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
  exact Examples.BenchmarkCertKit.bignum_single_fnspec_gen mul4x4Compiled hh
    mul4x4Module_checkAcyclic mul4x4_wf (by simp)
    (supportsAll_to_forall bignumFns_supportsSource_all)
    (mul4x4_correct bignumEnv) k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-- Closed `FnSpec` for `addMod25519Module` on `x64Target`. -/
theorem addMod25519_module_fnspec (k₀ : Nat)
    (hc : addMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ addMod25519Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (bignumEnv f.name f.as f.rs)
        (addMod25519Compiled.bound f.name) 0 := by
  simp only [addMod25519Module, List.mem_singleton] at hf; subst hf
  exact Examples.BenchmarkCertKit.bignum_single_fnspec_gen addMod25519Compiled hh
    addMod25519Module_checkAcyclic addMod25519_wf (by simp)
    (supportsAll_to_forall bignumFns_supportsSource_all)
    (addMod25519_correct bignumEnv) k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-- Closed `FnSpec` for `subMod25519Module` on `x64Target`. -/
theorem subMod25519_module_fnspec (k₀ : Nat)
    (hc : subMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ subMod25519Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (bignumEnv f.name f.as f.rs)
        (subMod25519Compiled.bound f.name) 0 := by
  simp only [subMod25519Module, List.mem_singleton] at hf; subst hf
  exact Examples.BenchmarkCertKit.bignum_single_fnspec_gen subMod25519Compiled hh
    subMod25519Module_checkAcyclic subMod25519_wf (by simp)
    (supportsAll_to_forall bignumFns_supportsSource_all)
    (subMod25519_correct bignumEnv) k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-! ## 3. Closed Kraken x64 Correctness Theorems -/

private theorem bignum_x64_lift {sym : Sym} {b : Nat} {spec : Spec [i64, i64, i64] []}
    (hfn : x64Target.FnSpec hh sym spec b 0)
    {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)}
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : s.regs.get64 .rdi = out) (hpa : s.regs.get64 .rsi = pa)
    (hpb : s.regs.get64 .rdx = pb) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R)
    {P : Mem 64 → Prop}
    (hspec : ∀ m, (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) m →
      spec (out, pa, pb, ()) m (fun _ m' => P m') (fun _ _ _ _ => False)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ P ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64, i64]) (out, pa, pb, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hout_reg⟩
      (.cons ⟨by decide, by simpa using hpa⟩ (.cons ⟨by decide, by simpa using hpb⟩ .nil))⟩
  obtain ⟨m, hm, hmEq⟩ := BenchmarkCertKit.sep_extract_eq hmem
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns hfn (hspec m hm) s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', hP, _, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩

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
      ⟨s, Labels.label "mul4x4"⟩ := by
  have hfn : x64Target.FnSpec hh "mul4x4" mul4x4Spec (mul4x4Compiled.bound "mul4x4") 0 :=
    (mul4x4_module_fnspec k₀ hc hu List.mem_cons_self).2
  exact bignum_x64_lift hfn s ra R hout_reg hpa hpb hsp hmem
    (fun _ => Examples.BenchmarkCertKit.mul4x4_spec_ok has hbs hout)

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
      ⟨s, Labels.label "addMod25519"⟩ := by
  have hfn : x64Target.FnSpec hh "addMod25519" addMod25519Spec
      (addMod25519Compiled.bound "addMod25519") 0 :=
    (addMod25519_module_fnspec k₀ hc hu List.mem_cons_self).2
  exact bignum_x64_lift hfn s ra R hout_reg hpa hpb hsp hmem
    (fun _ => Examples.BenchmarkCertKit.addMod25519_spec_ok has hbs hout ha_lt hb_lt)

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
      ⟨s, Labels.label "subMod25519"⟩ := by
  have hfn : x64Target.FnSpec hh "subMod25519" subMod25519Spec
      (subMod25519Compiled.bound "subMod25519") 0 :=
    (subMod25519_module_fnspec k₀ hc hu List.mem_cons_self).2
  exact bignum_x64_lift hfn s ra R hout_reg hpa hpb hsp hmem
    (fun _ => Examples.BenchmarkCertKit.subMod25519_spec_ok has hbs hout ha_lt hb_lt)

end Generic

/-! ## 4. Concrete SysV x64 Execution Witnesses -/

abbrev nvMulA : List (BitVec 64) := Examples.BenchmarkCertKit.nvMulA
abbrev nvMulB : List (BitVec 64) := Examples.BenchmarkCertKit.nvMulB
abbrev nvMulOut0 : List (BitVec 64) := Examples.BenchmarkCertKit.nvMulOut0
abbrev nvMulBytes : List UInt8 := Examples.BenchmarkCertKit.nvMulBytes

abbrev mul4x4Host : Host := mul4x4Compiled.host
def mul4x4State0 : MachineData :=
  x64Init.initState (as := [i64, i64, i64]) (mul4x4Compiled.bound "mul4x4") nvMulBytes
    (0x1000#64, 0x1040#64, 0x1060#64, ())

private theorem x64_nv_weaken [Host] {b : Nat} {P : Mem 64 → Prop} {st₀}
    (h : Eventually (step1 Host.exe)
      (fun st => st.pc = x64Init.ra0 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆ P ⋆ x64Target.Exit x64Init.sp0 b ⋆ emp))
      st₀) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ P ⋆ region (0x0ff8#64 - BitVec.ofNat 64 b) (b + 8) ⋆ emp)) st₀ :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hm⟩ => ⟨hpc, by simpa only [Target.Exit, x64Target, x64FrameTarget,
      x64FramePreds, x64Frame, x64Init] using hm⟩) h

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
  x64_nv_weaken <| run_sep_nonvacuous x64Init mul4x4Compiled
    (mul4x4_module_fnspec 0 mul4x4Compiled.code_infix_host
      mul4x4Compiled.labelsUnique List.mem_cons_self).2
    nvMulBytes (0x1000#64, 0x1040#64, 0x1060#64, ()) Examples.BenchmarkCertKit.nvMulBytes_length
    rfl Examples.BenchmarkCertKit.nvMul_spec_ok

abbrev nvAddA : List (BitVec 64) := Examples.BenchmarkCertKit.nvAddA
abbrev nvAddB : List (BitVec 64) := Examples.BenchmarkCertKit.nvAddB
abbrev nv4Out0 : List (BitVec 64) := Examples.BenchmarkCertKit.nv4Out0
abbrev nvAddBytes : List UInt8 := Examples.BenchmarkCertKit.nvAddBytes

abbrev addMod25519Host : Host := addMod25519Compiled.host
def addMod25519State0 : MachineData :=
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
  x64_nv_weaken <| run_sep_nonvacuous x64Init addMod25519Compiled
    (addMod25519_module_fnspec 0 addMod25519Compiled.code_infix_host
      addMod25519Compiled.labelsUnique List.mem_cons_self).2
    nvAddBytes (0x1000#64, 0x1020#64, 0x1040#64, ()) Examples.BenchmarkCertKit.nvAddBytes_length
    rfl Examples.BenchmarkCertKit.nvAdd_spec_ok

abbrev nvSubA : List (BitVec 64) := Examples.BenchmarkCertKit.nvSubA
abbrev nvSubB : List (BitVec 64) := Examples.BenchmarkCertKit.nvSubB
abbrev nvSubBytes : List UInt8 := Examples.BenchmarkCertKit.nvSubBytes

abbrev subMod25519Host : Host := subMod25519Compiled.host
def subMod25519State0 : MachineData :=
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
  x64_nv_weaken <| run_sep_nonvacuous x64Init subMod25519Compiled
    (subMod25519_module_fnspec 0 subMod25519Compiled.code_infix_host
      subMod25519Compiled.labelsUnique List.mem_cons_self).2
    nvSubBytes (0x1000#64, 0x1020#64, 0x1040#64, ()) Examples.BenchmarkCertKit.nvSubBytes_length
    rfl Examples.BenchmarkCertKit.nvSub_spec_ok

end LeanQbe.T.Amd64.Bignum
