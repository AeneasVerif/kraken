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
meta import LeanQbe.T.Examples.UnionFind

/-!
# Union-Find (`ufFns`) on SysV x64
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.UnionFind

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.UnionFind LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Amd64 Kraken

splice_module_hints ufHints (x64Target.toIsa) x64LegalTarget ufFns

theorem compiled_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 ufFns ufHints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of the compiler on `ufFns` for SysV x64. -/
def compiled : Compiled x64Target x64LegalTarget [] [] 0 ufFns ufHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean [] [] 0 ufFns ufHints 2048
    compiled_check

private theorem ufFns_supportsSource_all :
    ufFns.all (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

theorem ufFns_supportsSource :
    ∀ f ∈ ufModule.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  supportsAll_to_forall ufFns_supportsSource_all

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `ufModule` on `x64Target`. -/
theorem uf_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ ufModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (ufEnv f.name f.as f.rs) (compiled.bound f.name) 0 :=
  uf_module_fnspec_gen compiled hh rfl ufFns_supportsSource k₀ hc hu hf

/-- End-to-end correctness of compiled `find` on Kraken x64. -/
theorem find_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "find"))
          (compiled.bound "find") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = rep x ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ uf p n rep ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "find"))
            (compiled.bound "find" + 8) ⋆ R))
      ⟨s, Labels.label "find"⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (p, x, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hp⟩ (.cons ⟨by decide, by simpa using hxx⟩ .nil)⟩
  obtain ⟨m, hm, hmEq⟩ := sep_extract_eq hmem
  have hfn : x64Target.FnSpec hh "find" findSpec (compiled.bound "find") 0 :=
    (uf_module_fnspec k₀ hc hu (by simp [ufModule, ufFns] :
      (⟨"find", [i64, i64], [i64], find⟩ : Fn) ∈ ufModule.fns)).2
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns hfn (find_spec_ok hx hm) s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', ⟨rfl, huf'⟩, hrets, hm'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (rep x) st.data hrets, hcs, hsp',
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩

private theorem unionLike_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {fn : Fn} (hfn_mem : fn ∈ ufModule.fns) (has : fn.as = [i64, i64, i64]) (hrs : fn.rs = [])
    (hspec_eq : ufEnv fn.name [i64, i64, i64] [] = unionSpec)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x) (hyy : s.regs.get64 .rdx = y)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound fn.name))
          (compiled.bound fn.name) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound fn.name))
            (compiled.bound fn.name + 8) ⋆ R))
      ⟨s, Labels.label fn.name⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64, i64]) (p, x, y, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hp⟩
      (.cons ⟨by decide, by simpa using hxx⟩ (.cons ⟨by decide, by simpa using hyy⟩ .nil))⟩
  obtain ⟨m, hm, hmEq⟩ := sep_extract_eq hmem
  have hfn0 := (uf_module_fnspec k₀ hc hu hfn_mem).2
  rw [has, hrs, hspec_eq] at hfn0
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns hfn0 (union_spec_ok hx hy hm) s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', huf', _, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩

/-- End-to-end correctness of compiled `union` (calling `find` twice) on Kraken x64. -/
theorem union_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x) (hyy : s.regs.get64 .rdx = y)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "union"))
          (compiled.bound "union") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "union"))
            (compiled.bound "union" + 8) ⋆ R))
      ⟨s, Labels.label "union"⟩ :=
  unionLike_x64_correct k₀ hc hu (fn := ⟨"union", [i64, i64, i64], [], union⟩)
    (by simp [ufModule, ufFns]) rfl rfl rfl p x y n rep hx hy s ra R hp hxx hyy hsp hmem

/-- End-to-end correctness of compiled `unionInline` on Kraken x64. -/
theorem unionInline_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x) (hyy : s.regs.get64 .rdx = y)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "unionInline"))
          (compiled.bound "unionInline") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "unionInline"))
            (compiled.bound "unionInline" + 8) ⋆ R))
      ⟨s, Labels.label "unionInline"⟩ :=
  unionLike_x64_correct k₀ hc hu (fn := ⟨"unionInline", [i64, i64, i64], [], unionInline⟩)
    (by simp [ufModule, ufFns]) rfl rfl rfl p x y n rep hx hy s ra R hp hxx hyy hsp hmem

end Generic

abbrev ufHost : Host := compiled.host
attribute [local instance] ufHost

abbrev ufInitBytes := LeanQbe.T.Examples.BenchmarkCertKit.ufInitBytes

def findState0 : MachineData :=
  x64Init.initState (as := [i64, i64]) (compiled.bound "find") ufInitBytes (0x1000#64, 3#64, ())
def unionState0 : MachineData :=
  x64Init.initState (as := [i64, i64, i64]) (compiled.bound "union") ufInitBytes
    (0x1000#64, 1#64, 2#64, ())
def unionInlineState0 : MachineData :=
  x64Init.initState (as := [i64, i64, i64]) (compiled.bound "unionInline") ufInitBytes
    (0x1000#64, 1#64, 2#64, ())

/-- Concrete execution of `find` on `init 4` at `0x1000`: `find(0x1000, 3)` returns `3` in `rax`. -/
theorem find_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 3#64 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 id ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound "find"))
            (compiled.bound "find" + 8) ⋆ emp))
      ⟨findState0, Labels.label "find"⟩ := by
  have hfn : x64Target.FnSpec ufHost "find" findSpec (compiled.bound "find") 0 :=
    (uf_module_fnspec 0 compiled.code_infix_host compiled.labelsUnique
      (by simp [ufModule, ufFns] : (⟨"find", [i64, i64], [i64], find⟩ : Fn) ∈ ufModule.fns)).2
  refine eventually_weaken _ _ _ _
    (fun st ⟨hpc, hrax, hm⟩ => ⟨hpc, hrax, by
      simpa only [Target.Exit, x64Target, x64FrameTarget, x64FramePreds, x64Frame, x64Init] using
        hm⟩)
    (x64Init.run_ret1_sep_i64 compiled hfn ufInitBytes (0x1000#64, 3#64, ()) 3#64
      (uf 0x1000#64 4 id) ufInitBytes_length rfl find_nonvacuous
      fun _ _ ⟨hr, hm⟩ => ⟨hr, by rwa [sep_emp] at hm⟩)

private theorem unionLike_x64_nonvacuous
    {fn : Fn} (hfn_mem : fn ∈ ufModule.fns) (has : fn.as = [i64, i64, i64]) (hrs : fn.rs = [])
    (hspec_eq : ufEnv fn.name [i64, i64, i64] [] = unionSpec) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound fn.name))
            (compiled.bound fn.name + 8) ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨x64Init.initState (as := [i64, i64, i64]) (compiled.bound fn.name) ufInitBytes
          (0x1000#64, 1#64, 2#64, ()),
        Labels.label fn.name⟩ := by
  have hfn := (uf_module_fnspec 0 compiled.code_infix_host compiled.labelsUnique hfn_mem).2
  rw [has, hrs, hspec_eq] at hfn
  refine x64Init.run_fnSpec compiled hfn ufInitBytes (0x1000#64, 1#64, 2#64, ())
    ufInitBytes_length rfl union_nonvacuous ?_
  rintro st (⟨hpc, _, m', ⟨rfl, huf'⟩, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · rw [sep_emp] at huf'
    exact ⟨hpc, by simpa only [Target.Exit, x64Target, x64FrameTarget, x64FramePreds, x64Frame,
      x64Init] using sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm', merge_init_1_2⟩
  · exact hx.elim

/-- Concrete execution of `union` (calling `find` twice) on `init 4` at `0x1000`. -/
theorem union_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound "union"))
            (compiled.bound "union" + 8) ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionState0, Labels.label "union"⟩ :=
  unionLike_x64_nonvacuous (fn := ⟨"union", [i64, i64, i64], [], union⟩)
    (by simp [ufModule, ufFns]) rfl rfl rfl

/-- Concrete execution of `unionInline` on `init 4` at `0x1000`. -/
theorem unionInline_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound "unionInline"))
            (compiled.bound "unionInline" + 8) ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionInlineState0, Labels.label "unionInline"⟩ :=
  unionLike_x64_nonvacuous (fn := ⟨"unionInline", [i64, i64, i64], [], unionInline⟩)
    (by simp [ufModule, ufFns]) rfl rfl rfl

end LeanQbe.T.Amd64.UnionFind
