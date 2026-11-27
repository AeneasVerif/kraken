module

public import LeanQbe.T.Arm64.BenchAbi
public import LeanQbe.T.Examples.BenchmarkCertKit
public import LeanQbe.T.MainSplice
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.UnionFind

/-!
# Union-Find (`ufFns`) on AArch64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.UnionFind

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.UnionFind LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Arm64 Kraken

splice_module_hints ufHints (armTarget.toIsa) armLegalTarget ufFns

theorem compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 ufFns ufHints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of the compiler on `ufFns` for AArch64. -/
@[expose] def compiled : Compiled armTarget armLegalTarget [] [] 0 ufFns ufHints 2048 :=
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
      armTarget.FnSpec hh f.name (ufEnv f.name f.as f.rs) (compiled.bound f.name) 0 :=
  uf_module_fnspec_gen compiled hh rfl ufFns_supportsSource k₀ hc hu hf

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
      ⟨s, Labels.label "find"⟩ :=
  uf_find_abi_correct arm64BenchAbi hh compiled ufFns_supportsSource
    k₀ hc hu p x n rep hx s ra R hp hxx ⟨hra, hsp⟩ hmem

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
  uf_unionLike_abi_correct arm64BenchAbi hh compiled ufFns_supportsSource k₀ hc hu
    (fn := ⟨"union", [i64, i64, i64], [], union⟩) (by simp [ufModule, ufFns]) rfl rfl rfl
    p x y n rep hx hy s ra R hp hxx hyy ⟨hra, hsp⟩ hmem

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
  uf_unionLike_abi_correct arm64BenchAbi hh compiled ufFns_supportsSource k₀ hc hu
    (fn := ⟨"unionInline", [i64, i64, i64], [], unionInline⟩) (by simp [ufModule, ufFns])
    rfl rfl rfl p x y n rep hx hy s ra R hp hxx hyy ⟨hra, hsp⟩ hmem

end Generic

abbrev ufHost : Host := compiled.host
attribute [local instance] ufHost

abbrev ufInitBytes := LeanQbe.T.Examples.BenchmarkCertKit.ufInitBytes

@[expose] def findState0 : MachineData :=
  armInit.initState (as := [i64, i64]) (compiled.bound "find") ufInitBytes (0x1000#64, 3#64, ())
@[expose] def unionState0 : MachineData :=
  armInit.initState (as := [i64, i64, i64]) (compiled.bound "union") ufInitBytes
    (0x1000#64, 1#64, 2#64, ())
@[expose] def unionInlineState0 : MachineData :=
  armInit.initState (as := [i64, i64, i64]) (compiled.bound "unionInline") ufInitBytes
    (0x1000#64, 1#64, 2#64, ())

/-- Concrete execution of `find` on `init 4` at `0x1000`: `find(0x1000, 3)` returns `3` in
`x0`. -/
theorem find_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 3#64 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 id ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "find"))
            (compiled.bound "find") ⋆ emp))
      ⟨findState0, Labels.label "find"⟩ :=
  uf_find_abi_nonvacuous arm64BenchAbi compiled ufFns_supportsSource

/-- Concrete execution of `union` (calling `find` twice) on `init 4` at `0x1000`. -/
theorem union_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "union"))
            (compiled.bound "union") ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionState0, Labels.label "union"⟩ :=
  uf_unionLike_abi_nonvacuous arm64BenchAbi compiled ufFns_supportsSource
    (fn := ⟨"union", [i64, i64, i64], [], union⟩) (by simp [ufModule, ufFns]) rfl rfl rfl

/-- Concrete execution of `unionInline` on `init 4` at `0x1000`. -/
theorem unionInline_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          region (0x1000#64 - BitVec.ofNat 64 (compiled.bound "unionInline"))
            (compiled.bound "unionInline") ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionInlineState0, Labels.label "unionInline"⟩ :=
  uf_unionLike_abi_nonvacuous arm64BenchAbi compiled ufFns_supportsSource
    (fn := ⟨"unionInline", [i64, i64, i64], [], unionInline⟩) (by simp [ufModule, ufFns])
    rfl rfl rfl

end LeanQbe.T.Arm64.UnionFind
