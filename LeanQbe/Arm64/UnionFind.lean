module

public import LeanQbe.Arm64.Abi
public import LeanQbe.Examples.UnionFindLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Union-Find (`ufFns`) on AArch64

Instantiates the target-generic Union-Find module `[findFn, unionFn, unionInlineFn]` on
`Arm64.target` via a single kernel evaluation (`compileChecked ... (by kernel_rfl)`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.UnionFind

open LeanQbe LeanQbe.UnionFind Arm64 Kraken

/-- Single kernel evaluation of the compiler on `ufFns` for AArch64. -/
def compiled : Compiled target [] [] 0 ufFns :=
  compileChecked target targetLayout [] [] 0 ufFns 2048 (by kernel_rfl)

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `ufFns` on `Arm64.target`. -/
theorem uf_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {nm : String} (hnm : nm ∈ ufFns.map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (ufEnv nm) (compiled.bound nm) 0 :=
  uf_fnSpec compiled hh k₀ hc hu hnm

/-- End-to-end correctness of compiled `find` on Kraken AArch64. -/
theorem find_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "find" ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "find"))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = rep x ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n rep ⋆
          (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "find" ∧
              f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "find"))) ⋆ R))
      ⟨s, Labels.label "find"⟩ := by
  have hargs : target.ArgsIn [p, x] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hp, hxx]
  refine eventually_weaken _ _ _ _ ?_
    (arm64_of_returns (find_returns compiled hh k₀ hc hu p x n rep hx) s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, hrets,
    f1, f2, hu1, hd1, ⟨m', fe, hu2, hd2, ⟨rfl, huf'⟩, hexit⟩, hf2⟩
  refine ⟨hpc, ?_, hcs, hsp', f1, f2, hu1, hd1, ⟨m', fe, hu2, hd2, huf', hexit⟩, hf2⟩
  simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets

/-- End-to-end correctness of compiled `union` (calling `find` twice) on Kraken AArch64. -/
theorem union_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "union" ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "union"))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "union" ∧
              f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "union"))) ⋆ R))
      ⟨s, Labels.label "union"⟩ := by
  have hargs : target.ArgsIn [p, x, y] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hp, hxx, hyy]
  refine eventually_weaken _ _ _ _ ?_
    (arm64_of_returns (union_returns compiled hh k₀ hc hu p x y n rep hx hy)
      s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, -, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ h => h.2)) hm'⟩

/-- End-to-end correctness of compiled `unionInline` on Kraken AArch64. -/
theorem unionInline_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "unionInline" ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "unionInline"))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "unionInline" ∧
              f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "unionInline"))) ⋆ R))
      ⟨s, Labels.label "unionInline"⟩ := by
  have hargs : target.ArgsIn [p, x, y] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hp, hxx, hyy]
  refine eventually_weaken _ _ _ _ ?_
    (arm64_of_returns (unionInline_returns compiled hh k₀ hc hu p x y n rep hx hy)
      s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, -, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ h => h.2)) hm'⟩

end Generic

/-! ## Concrete AArch64 executions in `compiled.host` -/

abbrev ufHost : Host := compiled.host
attribute [local instance] ufHost

def findState0 : MachineData := initState (compiled.bound "find") ufInitBytes [0x1000, 3]
def unionState0 : MachineData := initState (compiled.bound "union") ufInitBytes [0x1000, 1, 2]
def unionInlineState0 : MachineData :=
  initState (compiled.bound "unionInline") ufInitBytes [0x1000, 1, 2]

/-- Concrete execution of `find` on `init 4` at `0x1000`: `find(0x1000, 3)` returns `3` in `x0`. -/
theorem find_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 3 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 id ⋆
          (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "find" ∧
              f = bs.At (0x1000#64 - BitVec.ofNat 64 (compiled.bound "find"))) ⋆
          Std.ExtHashMap.emp))
      ⟨findState0, Labels.label "find"⟩ :=
  find_witness targetInit compiled

/-- Concrete execution of `union` (calling `find` twice) on `init 4` at `0x1000`. -/
theorem union_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "union" ∧
              f = bs.At (0x1000#64 - BitVec.ofNat 64 (compiled.bound "union"))) ⋆
          Std.ExtHashMap.emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionState0, Labels.label "union"⟩ :=
  union_witness targetInit compiled (by decide) rfl

/-- Concrete execution of `unionInline` on `init 4` at `0x1000`. -/
theorem unionInline_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "unionInline" ∧
              f = bs.At (0x1000#64 - BitVec.ofNat 64 (compiled.bound "unionInline"))) ⋆
          Std.ExtHashMap.emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionInlineState0, Labels.label "unionInline"⟩ :=
  union_witness targetInit compiled (by decide) rfl

end LeanQbe.Arm64.UnionFind
