module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.UnionFindLemmas
public import LeanQbe.T.MainSplice
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.UnionFind

/-!
# Union-Find (`ufFns`) on AArch64

Instantiates the typed-IR Union-Find module `ufModule` (`find`, `union`, `unionInline`) on
`armTarget` (`armLegalTarget`, `armLayout`, `armLabelClean`) with:
* `ufHints` via `splice_module_hints`;
* `compiled_check : checkCompile ... = true` proved in a single kernel reduction (`t_kernel_rfl`);
* `uf_module_fnspec` over arbitrary Kraken `Host` instances;
* closed Kraken AArch64 correctness theorems `find_arm64_correct`, `union_arm64_correct`, and
  `unionInline_arm64_correct`;
* concrete non-vacuous execution witnesses on `compiled.host` via `armInit`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.UnionFind

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.UnionFind LeanQbe.T.Arm64 Kraken

splice_module_hints ufHints (armTarget.toIsa) armLegalTarget ufFns

theorem compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 ufFns ufHints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of the compiler on `ufFns` for AArch64. -/
def compiled : Compiled armTarget armLegalTarget [] [] 0 ufFns ufHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean [] [] 0 ufFns ufHints 2048
    compiled_check

private theorem ufFns_supportsSource_all :
    ufFns.all (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

theorem ufFns_supportsSource :
    ∀ f ∈ ufModule.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true :=
  supportsAll_to_forall ufFns_supportsSource_all

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `ufModule` on `armTarget`. -/
theorem uf_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ ufModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (ufEnv f.name f.as f.rs) (compiled.bound f.name) 0 := by
  have hmem := hf
  simp only [ufModule, ufFns, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs, hnoex⟩ :
      armLegalTarget.legalSig f.as = f.as ∧ armLegalTarget.legalSig f.rs = f.rs ∧
        (∀ args m Q X X',
          ufEnv f.name f.as f.rs args m Q X → ufEnv f.name f.as f.rs args m Q X') := by
    rcases hmem with rfl | rfl | rfl <;> exact ⟨rfl, rfl, fun _ _ _ _ _ h => h⟩
  exact compiled.fnSpec_noExit_id ufModule rfl hh ufEnv k₀ hc hu
    ufModule_checkAcyclic ufFns_wf ufFns_supportsSource ufEnv_sound hf has hrs hnoex

/-- End-to-end correctness of compiled `find` on Kraken AArch64. -/
theorem find_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "find"))
        (compiled.bound "find") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = rep x ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n rep ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "find"))
            (compiled.bound "find") ⋆ R))
      ⟨s, Labels.label "find"⟩ := by
  have hargs : armTarget.ArgsIn (as := [i64, i64]) (p, x, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hp⟩
      (.cons ⟨by decide, by simpa [get_reg] using hxx⟩ .nil)⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "find"))
        (compiled.bound "find") ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn : armTarget.FnSpec hh "find" findSpec (compiled.bound "find") 0 :=
    (uf_module_fnspec k₀ hc hu (by simp [ufModule, ufFns] :
      (⟨"find", [i64, i64], [i64], find⟩ : Fn) ∈ ufModule.fns)).2
  have hspec : findSpec (p, x, ()) m (fun r m' => r = (rep x, ()) ∧ uf p n rep m')
      (fun _ _ _ _ => False) :=
    ⟨n, rep, emp, by rw [sep_emp]; exact hm, hx, fun m' hm' => ⟨rfl, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', ⟨rfl, huf'⟩, hrets, hm'⟩
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = rep x := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton (rep x) st.data hrets
  exact ⟨hpc, hx0, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩

private theorem unionLike_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hfn_mem : fn ∈ ufModule.fns) (has : fn.as = [i64, i64, i64]) (hrs : fn.rs = [])
    (hspec_eq : ufEnv fn.name [i64, i64, i64] [] = unionSpec)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound fn.name))
        (compiled.bound fn.name) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound fn.name))
            (compiled.bound fn.name) ⋆ R))
      ⟨s, Labels.label fn.name⟩ := by
  have hargs : armTarget.ArgsIn (as := [i64, i64, i64]) (p, x, y, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hp⟩
      (.cons ⟨by decide, by simpa [get_reg] using hxx⟩
        (.cons ⟨by decide, by simpa [get_reg] using hyy⟩ .nil))⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound fn.name))
        (compiled.bound fn.name) ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn0 := (uf_module_fnspec k₀ hc hu hfn_mem).2
  rw [has, hrs, hspec_eq] at hfn0
  have hspec : unionSpec (p, x, y, ()) m (fun _ m' => uf p n (merge rep x y) m')
      (fun _ _ _ _ => False) :=
    ⟨n, rep, emp, by rw [sep_emp]; exact hm, hx, hy, fun m' hm' => by rwa [sep_emp] at hm'⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn0 hspec s ra R hargs hra hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', huf', _, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩

/-- End-to-end correctness of compiled `union` (calling `find` twice) on Kraken AArch64. -/
theorem union_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "union"))
        (compiled.bound "union") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "union"))
            (compiled.bound "union") ⋆ R))
      ⟨s, Labels.label "union"⟩ :=
  unionLike_arm64_correct k₀ hc hu (fn := ⟨"union", [i64, i64, i64], [], union⟩)
    (by simp [ufModule, ufFns]) rfl rfl rfl p x y n rep hx hy s ra R hp hxx hyy hra hsp hmem

/-- End-to-end correctness of compiled `unionInline` on Kraken AArch64. -/
theorem unionInline_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "unionInline"))
        (compiled.bound "unionInline") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "unionInline"))
            (compiled.bound "unionInline") ⋆ R))
      ⟨s, Labels.label "unionInline"⟩ :=
  unionLike_arm64_correct k₀ hc hu (fn := ⟨"unionInline", [i64, i64, i64], [], unionInline⟩)
    (by simp [ufModule, ufFns]) rfl rfl rfl p x y n rep hx hy s ra R hp hxx hyy hra hsp hmem

end Generic

/-! ## Concrete AArch64 Executions in `compiled.host` -/

abbrev ufHost : Host := compiled.host
attribute [local instance] ufHost

def ufInitBytes : List UInt8 := bytes64 (init 4)

private theorem ufInitBytes_length : ufInitBytes.length ≤ 8192 := by
  simp [ufInitBytes, bytes64_length, init]

def findState0 : MachineData :=
  armInit.initState (as := [i64, i64]) (compiled.bound "find") ufInitBytes (0x1000#64, 3#64, ())
def unionState0 : MachineData :=
  armInit.initState (as := [i64, i64, i64]) (compiled.bound "union") ufInitBytes
    (0x1000#64, 1#64, 2#64, ())
def unionInlineState0 : MachineData :=
  armInit.initState (as := [i64, i64, i64]) (compiled.bound "unionInline") ufInitBytes
    (0x1000#64, 1#64, 2#64, ())

/-- Concrete execution of `find` on `init 4` at `0x1000`: `find(0x1000, 3)` returns `3` in `x0`. -/
theorem find_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 3#64 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 id ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "find"))
            (compiled.bound "find") ⋆ emp))
      ⟨findState0, Labels.label "find"⟩ := by
  have hfn : armTarget.FnSpec ufHost "find" findSpec (compiled.bound "find") 0 :=
    (uf_module_fnspec 0 compiled.code_infix_host compiled.labelsUnique
      (by simp [ufModule, ufFns] : (⟨"find", [i64, i64], [i64], find⟩ : Fn) ∈ ufModule.fns)).2
  refine eventually_weaken _ _ _ _ ?_
    (armInit.run_ret1_sep_i64 compiled hfn ufInitBytes (0x1000#64, 3#64, ()) 3#64
      (uf 0x1000#64 4 id) ufInitBytes_length rfl find_nonvacuous
      fun _ _ ⟨hr, hm⟩ => ⟨hr, by rwa [sep_emp] at hm⟩)
  rintro st ⟨hpc, hx0, hm⟩
  refine ⟨hpc, ?_, ?_⟩
  · simpa [armInit, get_reg] using hx0
  · simpa only [Target.Exit, armTarget, armFrameTarget, armFramePreds, armFrame, armInit,
      Nat.add_zero] using hm

private theorem unionLike_arm64_nonvacuous
    {fn : Fn} (hfn_mem : fn ∈ ufModule.fns) (has : fn.as = [i64, i64, i64]) (hrs : fn.rs = [])
    (hspec_eq : ufEnv fn.name [i64, i64, i64] [] = unionSpec) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound fn.name))
            (compiled.bound fn.name) ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨armInit.initState (as := [i64, i64, i64]) (compiled.bound fn.name) ufInitBytes
          (0x1000#64, 1#64, 2#64, ()),
        Labels.label fn.name⟩ := by
  have hfn := (uf_module_fnspec 0 compiled.code_infix_host compiled.labelsUnique hfn_mem).2
  rw [has, hrs, hspec_eq] at hfn
  refine armInit.run_fnSpec compiled hfn ufInitBytes (0x1000#64, 1#64, 2#64, ())
    ufInitBytes_length rfl union_nonvacuous ?_
  rintro st (⟨hpc, _, m', ⟨rfl, huf'⟩, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, merge_init_1_2⟩
    rw [sep_emp] at huf'
    simpa only [Target.Exit, armTarget, armFrameTarget, armFramePreds, armFrame, armInit,
      Nat.add_zero] using
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'
  · exact hx.elim

/-- Concrete execution of `union` (calling `find` twice) on `init 4` at `0x1000`. -/
theorem union_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "union"))
            (compiled.bound "union") ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionState0, Labels.label "union"⟩ :=
  unionLike_arm64_nonvacuous (fn := ⟨"union", [i64, i64, i64], [], union⟩)
    (by simp [ufModule, ufFns]) rfl rfl rfl

/-- Concrete execution of `unionInline` on `init 4` at `0x1000`. -/
theorem unionInline_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "unionInline"))
            (compiled.bound "unionInline") ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionInlineState0, Labels.label "unionInline"⟩ :=
  unionLike_arm64_nonvacuous (fn := ⟨"unionInline", [i64, i64, i64], [], unionInline⟩)
    (by simp [ufModule, ufFns]) rfl rfl rfl

end LeanQbe.T.Arm64.UnionFind