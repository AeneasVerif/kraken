module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.MainSplice
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Bignum

/-!
# Curve25519 Bignum Kernels on AArch64

Instantiates the typed-IR bignum modules (`mul4x4Module`, `addMod25519Module`, `subMod25519Module`)
on `armTarget` (`armLegalTarget`, `armLayout`, `armLabelClean`) with:
* external hint splicing via `splice_module_hints`;
* single-kernel-reduction compilation checks (`t_kernel_rfl`, default 200k heartbeats);
* closed `FnSpec` and Kraken AArch64 correctness theorems (`mul4x4_arm64_correct`,
  `addMod25519_arm64_correct`, `subMod25519_arm64_correct`);
* concrete non-vacuous execution witnesses on `*.host` via `armInit`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.Bignum

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.Bignum LeanQbe.T.Arm64 Kraken

splice_module_hints mul4x4Hints (armTarget.toIsa) armLegalTarget mul4x4Module.fns
splice_module_hints addMod25519Hints (armTarget.toIsa) armLegalTarget addMod25519Module.fns
splice_module_hints subMod25519Hints (armTarget.toIsa) armLegalTarget subMod25519Module.fns

/-! ## 1. Compiled Kernel Certificates -/

theorem mul4x4_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0
      mul4x4Module.fns mul4x4Hints 2048 = true := by
  t_kernel_rfl

theorem addMod25519_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0
      addMod25519Module.fns addMod25519Hints 2048 = true := by
  t_kernel_rfl

theorem subMod25519_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0
      subMod25519Module.fns subMod25519Hints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of `mul4x4` for AArch64. -/
def mul4x4Compiled :
    Compiled armTarget armLegalTarget [] [] 0 mul4x4Module.fns mul4x4Hints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 mul4x4Module.fns mul4x4Hints 2048 mul4x4_check

/-- Single kernel evaluation of `addMod25519` for AArch64. -/
def addMod25519Compiled :
    Compiled armTarget armLegalTarget [] [] 0 addMod25519Module.fns addMod25519Hints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 addMod25519Module.fns addMod25519Hints 2048 addMod25519_check

/-- Single kernel evaluation of `subMod25519` for AArch64. -/
def subMod25519Compiled :
    Compiled armTarget armLegalTarget [] [] 0 subMod25519Module.fns subMod25519Hints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean
    [] [] 0 subMod25519Module.fns subMod25519Hints 2048 subMod25519_check

/-! ## 2. Source Support & Module `FnSpec` -/

private theorem bignumFns_supportsSource_all :
    [mul4x4Fn, addMod25519Fn, subMod25519Fn].all
      (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

private theorem bignum_single_fnspec {hh : Host} {f : Fn}
    {hints : List armTarget.toIsa.Hints}
    (M : Compiled armTarget armLegalTarget [] [] 0 [f] hints 2048)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hwf : f.Wf) (hsupp_mem : f ∈ [mul4x4Fn, addMod25519Fn, subMod25519Fn])
    (hwp : ∀ xs m Q X, bignumEnv f.name f.as f.rs xs m Q X →
      Func.wp bignumEnv f.body xs m Q X)
    (k₀ : Nat) (hc : M.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (has : armLegalTarget.legalSig f.as = f.as)
    (hrs : armLegalTarget.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X',
      bignumEnv f.name f.as f.rs args m Q X → bignumEnv f.name f.as f.rs args m Q X') :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (bignumEnv f.name f.as f.rs) (M.bound f.name) 0 := by
  have hsupp : ∀ g ∈ ({ fns := [f], externs := [], exits := [] } : Module).fns,
      (g.earlyOpt).body.supportsSource armLegalTarget = true := by
    intro g hg
    simp only [List.mem_singleton] at hg; rw [hg]
    exact supportsAll_to_forall bignumFns_supportsSource_all f hsupp_mem
  exact M.fnSpec_noExit_id ⟨[f], [], []⟩ rfl hh bignumEnv k₀ hc hu hacyc
    (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hwf)
    hsupp
    (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hwp)
    List.mem_cons_self has hrs hnoex

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for `mul4x4Module` on `armTarget`. -/
theorem mul4x4_module_fnspec (k₀ : Nat)
    (hc : mul4x4Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ mul4x4Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (bignumEnv f.name f.as f.rs)
        (mul4x4Compiled.bound f.name) 0 := by
  simp only [mul4x4Module, List.mem_singleton] at hf; subst hf
  exact bignum_single_fnspec mul4x4Compiled mul4x4Module_checkAcyclic mul4x4_wf
    (by simp) (mul4x4_correct bignumEnv) k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-- Closed `FnSpec` for `addMod25519Module` on `armTarget`. -/
theorem addMod25519_module_fnspec (k₀ : Nat)
    (hc : addMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ addMod25519Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (bignumEnv f.name f.as f.rs)
        (addMod25519Compiled.bound f.name) 0 := by
  simp only [addMod25519Module, List.mem_singleton] at hf; subst hf
  exact bignum_single_fnspec addMod25519Compiled addMod25519Module_checkAcyclic addMod25519_wf
    (by simp) (addMod25519_correct bignumEnv) k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-- Closed `FnSpec` for `subMod25519Module` on `armTarget`. -/
theorem subMod25519_module_fnspec (k₀ : Nat)
    (hc : subMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ subMod25519Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (bignumEnv f.name f.as f.rs)
        (subMod25519Compiled.bound f.name) 0 := by
  simp only [subMod25519Module, List.mem_singleton] at hf; subst hf
  exact bignum_single_fnspec subMod25519Compiled subMod25519Module_checkAcyclic subMod25519_wf
    (by simp) (subMod25519_correct bignumEnv) k₀ hc hu rfl rfl (fun _ _ _ _ _ h => h)

/-! ## 3. Closed Kraken AArch64 Correctness Theorems -/

private theorem bignum_arm64_lift {sym : Sym} {b : Nat} {spec : Spec [i64, i64, i64] []}
    (hfn : armTarget.FnSpec hh sym spec b 0)
    {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)}
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : (s.regs.getXReg .X0).toBitVec = out)
    (hpa : (s.regs.getXReg .X1).toBitVec = pa)
    (hpb : (s.regs.getXReg .X2).toBitVec = pb)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R)
    {P : Mem 64 → Prop}
    (hspec : ∀ m, (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) m →
      spec (out, pa, pb, ()) m (fun _ m' => P m') (fun _ _ _ _ => False)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ P ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  have hargs : armTarget.ArgsIn (as := [i64, i64, i64]) (out, pa, pb, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hout_reg⟩
      (.cons ⟨by decide, by simpa [get_reg] using hpa⟩
        (.cons ⟨by decide, by simpa [get_reg] using hpb⟩ .nil))⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  refine eventually_weaken _ _ _ _ ?_
    (arm64_of_returns hfn (hspec m hm) s ra R hargs hra hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', hP, _, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩

/-- End-to-end correctness of compiled `mul4x4` on Kraken AArch64. -/
theorem mul4x4_arm64_correct (k₀ : Nat)
    (hc : mul4x4Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 8)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : (s.regs.getXReg .X0).toBitVec = out)
    (hpa : (s.regs.getXReg .X1).toBitVec = pa)
    (hpb : (s.regs.getXReg .X2).toBitVec = pb)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (mul4x4Compiled.bound "mul4x4"))
        (mul4x4Compiled.bound "mul4x4") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
            limbsVal rs = limbsVal as * limbsVal bs ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (mul4x4Compiled.bound "mul4x4"))
            (mul4x4Compiled.bound "mul4x4") ⋆ R))
      ⟨s, Labels.label "mul4x4"⟩ := by
  have hfn : armTarget.FnSpec hh "mul4x4" mul4x4Spec (mul4x4Compiled.bound "mul4x4") 0 :=
    (mul4x4_module_fnspec k₀ hc hu List.mem_cons_self).2
  refine bignum_arm64_lift hfn s ra R hout_reg hpa hpb hra hsp hmem fun m hm =>
    ⟨as, bs, out0, emp, has, hbs, hout, by rw [sep_emp]; exact sep_ac hm,
      fun rs m' hrs hmul hm' => ⟨rs, hrs, hmul, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩

/-- End-to-end correctness of compiled `addMod25519` on Kraken AArch64. -/
theorem addMod25519_arm64_correct (k₀ : Nat)
    (hc : addMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < p25519) (hb_lt : limbsVal bs < p25519)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : (s.regs.getXReg .X0).toBitVec = out)
    (hpa : (s.regs.getXReg .X1).toBitVec = pa)
    (hpb : (s.regs.getXReg .X2).toBitVec = pb)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (addMod25519Compiled.bound "addMod25519"))
        (addMod25519Compiled.bound "addMod25519") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = (limbsVal as + limbsVal bs) % p25519 ∧ limbsVal rs < p25519 ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (addMod25519Compiled.bound "addMod25519"))
            (addMod25519Compiled.bound "addMod25519") ⋆ R))
      ⟨s, Labels.label "addMod25519"⟩ := by
  have hfn : armTarget.FnSpec hh "addMod25519" addMod25519Spec
      (addMod25519Compiled.bound "addMod25519") 0 :=
    (addMod25519_module_fnspec k₀ hc hu List.mem_cons_self).2
  refine bignum_arm64_lift hfn s ra R hout_reg hpa hpb hra hsp hmem fun m hm =>
    ⟨as, bs, out0, emp, has, hbs, hout, ha_lt, hb_lt, by rw [sep_emp]; exact sep_ac hm,
      fun rs m' hrs hmod hlt hm' =>
        ⟨rs, hrs, hmod, hlt, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩

/-- End-to-end correctness of compiled `subMod25519` on Kraken AArch64. -/
theorem subMod25519_arm64_correct (k₀ : Nat)
    (hc : subMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < p25519) (hb_lt : limbsVal bs < p25519)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : (s.regs.getXReg .X0).toBitVec = out)
    (hpa : (s.regs.getXReg .X1).toBitVec = pa)
    (hpb : (s.regs.getXReg .X2).toBitVec = pb)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (subMod25519Compiled.bound "subMod25519"))
        (subMod25519Compiled.bound "subMod25519") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = (if limbsVal bs ≤ limbsVal as then limbsVal as - limbsVal bs
                           else limbsVal as + p25519 - limbsVal bs) ∧
            limbsVal rs < p25519 ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (subMod25519Compiled.bound "subMod25519"))
            (subMod25519Compiled.bound "subMod25519") ⋆ R))
      ⟨s, Labels.label "subMod25519"⟩ := by
  have hfn : armTarget.FnSpec hh "subMod25519" subMod25519Spec
      (subMod25519Compiled.bound "subMod25519") 0 :=
    (subMod25519_module_fnspec k₀ hc hu List.mem_cons_self).2
  refine bignum_arm64_lift hfn s ra R hout_reg hpa hpb hra hsp hmem fun m hm =>
    ⟨as, bs, out0, emp, has, hbs, hout, ha_lt, hb_lt, by rw [sep_emp]; exact sep_ac hm,
      fun rs m' hrs hsub hlt hm' =>
        ⟨rs, hrs, hsub, hlt, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩

end Generic

/-! ## 4. Concrete AArch64 Execution Witnesses -/

private theorem array64_split3 (a : BitVec 64) (xs ys zs : List (BitVec 64))
    (h : 8 * (xs ++ ys ++ zs).length ≤ 2 ^ 64) :
    (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys ⋆
      array64 (a + BitVec.ofNat 64 (8 * (xs.length + ys.length))) zs)
      ((bytes64 (xs ++ ys ++ zs)).At a) := by
  have ha := array64_bytes a (xs ++ ys ++ zs) h
  rwa [array64_append, array64_append, List.length_append] at ha

def nvMulA : List (BitVec 64) := [p0, p1, p2, p3]
def nvMulB : List (BitVec 64) := [2#64, 0#64, 0#64, 1#64]
def nvMulOut0 : List (BitVec 64) := List.replicate 8 0#64
def nvMulBytes : List UInt8 := bytes64 (nvMulOut0 ++ nvMulA ++ nvMulB)

private theorem nvMulBytes_length : nvMulBytes.length ≤ 8192 := by
  simp [nvMulBytes, bytes64_length, nvMulOut0, nvMulA, nvMulB]

abbrev mul4x4Host : Host := mul4x4Compiled.host
def mul4x4State0 : MachineData :=
  armInit.initState (as := [i64, i64, i64]) (mul4x4Compiled.bound "mul4x4") nvMulBytes
    (0x1000#64, 0x1040#64, 0x1060#64, ())

attribute [local instance] mul4x4Host in
/-- Concrete execution of `mul4x4` on `p25519 * (2^192 + 2)` in `mul4x4Compiled.host`. -/
theorem mul4x4_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
            limbsVal rs = limbsVal nvMulA * limbsVal nvMulB ∧
            (array64 0x1000#64 rs ⋆ array64 0x1040#64 nvMulA ⋆ array64 0x1060#64 nvMulB) m') ⋆
          region (0x1000#64 - BitVec.ofNat 64 (mul4x4Compiled.bound "mul4x4"))
            (mul4x4Compiled.bound "mul4x4") ⋆ emp))
      ⟨mul4x4State0, Labels.label "mul4x4"⟩ := by
  have hfn : armTarget.FnSpec mul4x4Host "mul4x4" mul4x4Spec
      (mul4x4Compiled.bound "mul4x4") 0 :=
    (mul4x4_module_fnspec 0 mul4x4Compiled.code_infix_host mul4x4Compiled.labelsUnique
      List.mem_cons_self).2
  have hm0 : (array64 0x1000#64 nvMulOut0 ⋆ array64 0x1040#64 nvMulA ⋆
      array64 0x1060#64 nvMulB) (nvMulBytes.At 0x1000#64) := by
    have ha := array64_split3 0x1000#64 nvMulOut0 nvMulA nvMulB
      (by simp [nvMulOut0, nvMulA, nvMulB])
    simpa only [nvMulBytes, nvMulOut0, nvMulA, nvMulB, List.length_replicate,
      List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using ha
  have hspec : mul4x4Spec (0x1000#64, 0x1040#64, 0x1060#64, ()) (nvMulBytes.At 0x1000#64)
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
        limbsVal rs = limbsVal nvMulA * limbsVal nvMulB ∧
        (array64 0x1000#64 rs ⋆ array64 0x1040#64 nvMulA ⋆ array64 0x1060#64 nvMulB) m')
      (fun _ _ _ _ => False) :=
    ⟨nvMulA, nvMulB, nvMulOut0, emp, rfl, rfl, rfl, by rw [sep_emp]; exact sep_ac hm0,
      fun rs m' hrs hmul hm' => ⟨rs, hrs, hmul, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩
  refine armInit.run_fnSpec mul4x4Compiled hfn nvMulBytes (0x1000#64, 0x1040#64, 0x1060#64, ())
    nvMulBytes_length rfl hspec ?_
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · refine ⟨hpc, ?_⟩
    simpa only [Target.Exit, armTarget, armFrameTarget, armFramePreds, armFrame, armInit,
      Nat.add_zero] using
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'
  · exact hx.elim

def nvAddA : List (BitVec 64) := [p0 - 1#64, p1, p2, p3]
def nvAddB : List (BitVec 64) := [20#64, 0#64, 0#64, 0#64]
def nv4Out0 : List (BitVec 64) := List.replicate 4 0#64
def nvAddBytes : List UInt8 := bytes64 (nv4Out0 ++ nvAddA ++ nvAddB)

private theorem nvAddBytes_length : nvAddBytes.length ≤ 8192 := by
  simp [nvAddBytes, bytes64_length, nv4Out0, nvAddA, nvAddB]

private theorem nvAddA_val : limbsVal nvAddA = p25519 - 1 := by
  have hp := limbsVal_p25519
  have h0 : (p0 - 1#64).toNat + 1 = p0.toNat := by decide
  have hsum : limbsVal nvAddA + 1 = p25519 := by
    rw [← hp]
    simp only [nvAddA, limbsVal4_eq]
    omega
  omega

private theorem p25519_gt_100 : 100 < p25519 := by
  unfold p25519
  have h1 : 2 ^ 64 ≤ (2 : Nat) ^ 255 := Nat.pow_le_pow_right (by decide) (by decide)
  have h2 : 119 < 2 ^ 64 := by decide
  omega

private theorem nvAddB_val : limbsVal nvAddB = 20 := by
  simp [nvAddB, limbsVal]

private theorem nvAdd_mod : (limbsVal nvAddA + limbsVal nvAddB) % p25519 = 19 := by
  rw [nvAddA_val, nvAddB_val]
  have hgt := p25519_gt_100
  rw [show p25519 - 1 + 20 = 19 + p25519 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

abbrev addMod25519Host : Host := addMod25519Compiled.host
def addMod25519State0 : MachineData :=
  armInit.initState (as := [i64, i64, i64]) (addMod25519Compiled.bound "addMod25519") nvAddBytes
    (0x1000#64, 0x1020#64, 0x1040#64, ())

attribute [local instance] addMod25519Host in
/-- Concrete execution of `addMod25519` wrapping `(p25519 - 1) + 20 = 19` mod `p25519`. -/
theorem addMod25519_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = 19 ∧
            (array64 0x1000#64 rs ⋆ array64 0x1020#64 nvAddA ⋆ array64 0x1040#64 nvAddB) m') ⋆
          region (0x1000#64 - BitVec.ofNat 64 (addMod25519Compiled.bound "addMod25519"))
            (addMod25519Compiled.bound "addMod25519") ⋆ emp))
      ⟨addMod25519State0, Labels.label "addMod25519"⟩ := by
  have hfn : armTarget.FnSpec addMod25519Host "addMod25519" addMod25519Spec
      (addMod25519Compiled.bound "addMod25519") 0 :=
    (addMod25519_module_fnspec 0 addMod25519Compiled.code_infix_host
      addMod25519Compiled.labelsUnique List.mem_cons_self).2
  have hm0 : (array64 0x1000#64 nv4Out0 ⋆ array64 0x1020#64 nvAddA ⋆
      array64 0x1040#64 nvAddB) (nvAddBytes.At 0x1000#64) := by
    have ha := array64_split3 0x1000#64 nv4Out0 nvAddA nvAddB
      (by simp [nv4Out0, nvAddA, nvAddB])
    simpa only [nvAddBytes, nv4Out0, nvAddA, nvAddB, List.length_replicate,
      List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using ha
  have hAlt : limbsVal nvAddA < p25519 := by rw [nvAddA_val]; have := p25519_gt_100; omega
  have hBlt : limbsVal nvAddB < p25519 := by rw [nvAddB_val]; have := p25519_gt_100; omega
  have hspec : addMod25519Spec (0x1000#64, 0x1020#64, 0x1040#64, ()) (nvAddBytes.At 0x1000#64)
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = 19 ∧
        (array64 0x1000#64 rs ⋆ array64 0x1020#64 nvAddA ⋆ array64 0x1040#64 nvAddB) m')
      (fun _ _ _ _ => False) :=
    ⟨nvAddA, nvAddB, nv4Out0, emp, rfl, rfl, rfl, hAlt, hBlt, by rw [sep_emp]; exact sep_ac hm0,
      fun rs m' hrs hmod _ hm' =>
        ⟨rs, hrs, hmod.trans nvAdd_mod, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩
  refine armInit.run_fnSpec addMod25519Compiled hfn nvAddBytes
    (0x1000#64, 0x1020#64, 0x1040#64, ()) nvAddBytes_length rfl hspec ?_
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · refine ⟨hpc, ?_⟩
    simpa only [Target.Exit, armTarget, armFrameTarget, armFramePreds, armFrame, armInit,
      Nat.add_zero] using
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'
  · exact hx.elim

def nvSubA : List (BitVec 64) := [5#64, 0#64, 0#64, 0#64]
def nvSubB : List (BitVec 64) := [25#64, 0#64, 0#64, 0#64]
def nvSubBytes : List UInt8 := bytes64 (nv4Out0 ++ nvSubA ++ nvSubB)

private theorem nvSubBytes_length : nvSubBytes.length ≤ 8192 := by
  simp [nvSubBytes, bytes64_length, nv4Out0, nvSubA, nvSubB]

private theorem nvSubA_val : limbsVal nvSubA = 5 := by simp [nvSubA, limbsVal]
private theorem nvSubB_val : limbsVal nvSubB = 25 := by simp [nvSubB, limbsVal]

private theorem nvSub_val :
    (if limbsVal nvSubB ≤ limbsVal nvSubA then limbsVal nvSubA - limbsVal nvSubB
     else limbsVal nvSubA + p25519 - limbsVal nvSubB) = p25519 - 20 := by
  rw [nvSubA_val, nvSubB_val]; have := p25519_gt_100; simp; omega

abbrev subMod25519Host : Host := subMod25519Compiled.host
def subMod25519State0 : MachineData :=
  armInit.initState (as := [i64, i64, i64]) (subMod25519Compiled.bound "subMod25519") nvSubBytes
    (0x1000#64, 0x1020#64, 0x1040#64, ())

attribute [local instance] subMod25519Host in
/-- Concrete execution of `subMod25519` wrapping `5 - 25 = p25519 - 20` mod `p25519`. -/
theorem subMod25519_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = p25519 - 20 ∧
            (array64 0x1000#64 rs ⋆ array64 0x1020#64 nvSubA ⋆ array64 0x1040#64 nvSubB) m') ⋆
          region (0x1000#64 - BitVec.ofNat 64 (subMod25519Compiled.bound "subMod25519"))
            (subMod25519Compiled.bound "subMod25519") ⋆ emp))
      ⟨subMod25519State0, Labels.label "subMod25519"⟩ := by
  have hfn : armTarget.FnSpec subMod25519Host "subMod25519" subMod25519Spec
      (subMod25519Compiled.bound "subMod25519") 0 :=
    (subMod25519_module_fnspec 0 subMod25519Compiled.code_infix_host
      subMod25519Compiled.labelsUnique List.mem_cons_self).2
  have hm0 : (array64 0x1000#64 nv4Out0 ⋆ array64 0x1020#64 nvSubA ⋆
      array64 0x1040#64 nvSubB) (nvSubBytes.At 0x1000#64) := by
    have ha := array64_split3 0x1000#64 nv4Out0 nvSubA nvSubB
      (by simp [nv4Out0, nvSubA, nvSubB])
    simpa only [nvSubBytes, nv4Out0, nvSubA, nvSubB, List.length_replicate,
      List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using ha
  have hAlt : limbsVal nvSubA < p25519 := by rw [nvSubA_val]; have := p25519_gt_100; omega
  have hBlt : limbsVal nvSubB < p25519 := by rw [nvSubB_val]; have := p25519_gt_100; omega
  have hspec : subMod25519Spec (0x1000#64, 0x1020#64, 0x1040#64, ()) (nvSubBytes.At 0x1000#64)
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = p25519 - 20 ∧
        (array64 0x1000#64 rs ⋆ array64 0x1020#64 nvSubA ⋆ array64 0x1040#64 nvSubB) m')
      (fun _ _ _ _ => False) :=
    ⟨nvSubA, nvSubB, nv4Out0, emp, rfl, rfl, rfl, hAlt, hBlt, by rw [sep_emp]; exact sep_ac hm0,
      fun rs m' hrs hsub _ hm' =>
        ⟨rs, hrs, hsub.trans nvSub_val, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩
  refine armInit.run_fnSpec subMod25519Compiled hfn nvSubBytes
    (0x1000#64, 0x1020#64, 0x1040#64, ()) nvSubBytes_length rfl hspec ?_
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · refine ⟨hpc, ?_⟩
    simpa only [Target.Exit, armTarget, armFrameTarget, armFramePreds, armFrame, armInit,
      Nat.add_zero] using
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'
  · exact hx.elim

end LeanQbe.T.Arm64.Bignum
