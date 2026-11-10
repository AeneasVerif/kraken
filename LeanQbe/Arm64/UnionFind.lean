module

public import LeanQbe.Arm64.Litmus
public import LeanQbe.Examples.UnionFindLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Union-Find end to end on AArch64 (plan step 5)

Compiles the two-function Union-Find module `[findFn, unionFn]` (`union` calls `find` twice, with
`p`, `y`, and `rx` spilled across calls) as well as the inlined variant `unionInlineFn` through the
full verified pipeline (`compile Arm64.isa` / `compileFn Arm64.isa`), checks the emitted AArch64
assembly by `kernel_rfl`, links `[findFn, unionFn]` via `compile_correct` (`uf_module_fnspec`), and
proves Kraken-AArch64-only end-to-end theorems (`find_arm64_correct`, `union_arm64_correct`,
`unionInline_arm64_correct`) and concrete non-vacuity instances (`find_arm64_nonvacuous`,
`union_arm64_nonvacuous`, `unionInline_arm64_nonvacuous`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.UnionFind

open LeanQbe LeanQbe.UnionFind LeanQbe.Arm64.Tracer LeanQbe.Arm64.Litmus Rega Kraken.AArch64.Parser

/-- `find` packaged as a named function. -/
def findFn : Fn := ⟨"find", find⟩

/-- `union` (calling `find` twice) packaged as a named function. -/
def unionFn : Fn := ⟨"union", union⟩

/-- `unionInline` packaged as a named function. -/
def unionInlineFn : Fn := ⟨"unionInline", unionInline⟩

/-- The AArch64 assembly emitted by `compileFn isa findFn`. -/
def findCode : Program := parseAArch64("find:
  sub sp, sp, #16
  str x30, [sp]
  b find.L0
  find.L0:
  ldr x17, =3
  lslv x2, x1, x17
  add x2, x0, x2
  ldr x3, [x2]
  subs xzr, x3, x1
  csinc w4, wzr, wzr, ne
  cbnz w4, find.L1
  ldr x17, =3
  lslv x1, x3, x17
  add x1, x0, x1
  ldr x1, [x1]
  str x1, [x2]
  b find.L0
  find.L1:
  add x0, x1, #0
  ldr x30, [sp]
  add sp, sp, #16
  ret")

/-- The AArch64 assembly emitted by `compileFn isa unionFn`. -/
def unionCode : Program := parseAArch64("union:
  sub sp, sp, #32
  str x30, [sp, #24]
  str x0, [sp]
  str x2, [sp, #8]
  bl find
  str x0, [sp, #16]
  ldr x0, [sp]
  ldr x1, [sp, #8]
  bl find
  ldr x1, [sp, #16]
  subs xzr, x1, x0
  csinc w1, wzr, wzr, ne
  cbnz w1, union.L0
  ldr x1, [sp, #16]
  ldr x17, =3
  lslv x1, x1, x17
  ldr x2, [sp]
  add x1, x2, x1
  str x0, [x1]
  ldr x30, [sp, #24]
  add sp, sp, #32
  ret
  union.L0:
  ldr x30, [sp, #24]
  add sp, sp, #32
  ret")

/-- The AArch64 assembly emitted by `compileFn isa unionInlineFn`. -/
def unionInlineCode : Program := parseAArch64("unionInline:
  sub sp, sp, #16
  str x30, [sp]
  b unionInline.L0
  unionInline.L0:
  ldr x17, =3
  lslv x3, x1, x17
  add x3, x0, x3
  ldr x4, [x3]
  subs xzr, x4, x1
  csinc w5, wzr, wzr, ne
  cbnz w5, unionInline.L1
  ldr x17, =3
  lslv x1, x4, x17
  add x1, x0, x1
  ldr x1, [x1]
  str x1, [x3]
  b unionInline.L0
  unionInline.L1:
  b unionInline.L2
  unionInline.L2:
  ldr x17, =3
  lslv x4, x2, x17
  add x4, x0, x4
  ldr x5, [x4]
  subs xzr, x5, x2
  csinc w6, wzr, wzr, ne
  cbnz w6, unionInline.L3
  ldr x17, =3
  lslv x2, x5, x17
  add x2, x0, x2
  ldr x2, [x2]
  str x2, [x4]
  b unionInline.L2
  unionInline.L3:
  subs xzr, x1, x2
  csinc w0, wzr, wzr, ne
  cbnz w0, unionInline.L4
  str x2, [x3]
  ldr x30, [sp]
  add sp, sp, #16
  ret
  unionInline.L4:
  ldr x30, [sp]
  add sp, sp, #16
  ret")

theorem find_compile : compileFn isa findFn = .ok findCode := by kernel_rfl
theorem union_compile : compileFn isa unionFn = .ok unionCode := by kernel_rfl
theorem unionInline_compile : compileFn isa unionInlineFn = .ok unionInlineCode := by kernel_rfl

theorem uf_module_compile :
    compile isa [findFn, unionFn] = .ok (findCode ++ unionCode) := by kernel_rfl

def ufEnv : Env := fun g => if g = "find" then findSpec else unionSpec
def ufBound : String → Nat := fun g => if g = "find" then 16 else 48

private theorem findFn_nslots : findFn.nslots isa = 0 := by kernel_rfl
private theorem findFn_callees : findFn.opt.ext.callees = [] := by kernel_rfl
private theorem findFn_exits : findFn.opt.ext.exits = [] := by kernel_rfl
private theorem unionFn_nslots : unionFn.nslots isa = 3 := by kernel_rfl
private theorem unionFn_callees : unionFn.opt.ext.callees = ["find", "find"] := by kernel_rfl
private theorem unionFn_exits : unionFn.opt.ext.exits = [] := by kernel_rfl
private theorem unionInlineFn_nslots : unionInlineFn.nslots isa = 0 := by kernel_rfl
private theorem unionInlineFn_callees : unionInlineFn.opt.ext.callees = [] := by kernel_rfl
private theorem unionInlineFn_exits : unionInlineFn.opt.ext.exits = [] := by kernel_rfl

section Generic
variable [hh : Host]

/-- Linking `[findFn, unionFn]` via `compile_correct`. -/
theorem uf_module_fnspec (k₀ : Nat)
    (hc : (findCode ++ unionCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) (nX : Nat) :
    ∀ f ∈ [findFn, unionFn],
      target.FnSpec hh f.name (ufEnv f.name) (ufBound f.name) nX := by
  refine compile_correct (T := target) hh ufEnv ufBound nX [findFn, unionFn]
    (findCode ++ unionCode) k₀ uf_module_compile hc hu ?_
  intro pre f post heq
  rcases pre with _ | ⟨f1, _ | ⟨f2, pre⟩⟩
  · injection heq with hf htl
    subst hf
    refine ⟨find_wf, find_correct _, by rw [findFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [findFn_callees]; intro _ h; nomatch h
    · rw [findFn_exits]; intro _ h; nomatch h
  · injection heq with hf1 htl
    injection htl with hf _
    subst hf1 hf
    refine ⟨union_wf, union_correct _ (fun _ _ _ _ h => h),
      by rw [unionFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [unionFn_callees]
      intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨Or.inl (by simp [findFn]), by rw [unionFn_nslots]; decide⟩
      · exact ⟨Or.inl (by simp [findFn]), by rw [unionFn_nslots]; decide⟩
      · nomatch hg
    · rw [unionFn_exits]; intro _ h; nomatch h
  · simp at heq

/-- `findCode` alone satisfies `findSpec` as a `Target.FnSpec` in any AArch64 host with unique
labels. -/
theorem find_fnspec (k₀ : Nat) (hc : findCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (nX : Nat) : target.FnSpec hh "find" findSpec 16 nX :=
  Target.FnSpec.of_spec target
    (compileFn_leaf_correct (T := target) hh findFn (fun _ _ _ _ _ => False) 16 nX findCode k₀
      find_compile hc hu find_wf findFn_callees findFn_exits
      (by rw [findFn_nslots]; decide) (by decide))
    (find_correct (fun _ _ _ _ _ => False))

/-- `unionInlineCode` satisfies `unionSpec` as a `Target.FnSpec` in any AArch64 host with unique
labels. -/
theorem unionInline_fnspec (k₀ : Nat) (hc : unionInlineCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (nX : Nat) : target.FnSpec hh "unionInline" unionSpec 16 nX :=
  Target.FnSpec.of_spec target
    (compileFn_leaf_correct (T := target) hh unionInlineFn (fun _ _ _ _ _ => False) 16 nX
      unionInlineCode k₀ unionInline_compile hc hu unionInline_wf unionInlineFn_callees
      unionInlineFn_exits (by rw [unionInlineFn_nslots]; decide) (by decide))
    (unionInline_correct (fun _ _ _ _ _ => False))

/-- End-to-end correctness of compiled `find` on Kraken AArch64: in every host containing
`findCode ++ unionCode` at `k₀` with unique labels, from a state with `p, x` (`x < n`) in
`x0, x1`, 16 bytes of stack space below `sp`, return address `ra` in `x30`, 16-byte aligned `sp`,
and memory `uf p n rep ⋆ ... ⋆ R`, execution eventually reaches `ra` with the canonical
representative `rep x` in `x0`, callee-saved registers `x19`–`x29` and `sp` restored, and memory
satisfying `uf p n rep ⋆ ... ⋆ R` (after path halving). -/
theorem find_arm64_correct (k₀ : Nat)
    (hc : (findCode ++ unionCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = rep x ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n rep ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, huf, hentry⟩, hrest⟩ := hmem
  let Q : LeanQbe.Post := fun rets m' => rets = [rep x] ∧ (uf p n rep ⋆ Std.ExtHashMap.emp) m'
  let X : XPost := fun _ _ _ => False
  have hm : (uf p n rep ⋆ Std.ExtHashMap.emp) m := by rwa [Std.ExtHashMap.sep_emp]
  have hspec : findSpec [p, x] m Q X :=
    ⟨p, x, n, rep, Std.ExtHashMap.emp, rfl, hm, hx, fun _ hm' => ⟨rfl, hm'⟩⟩
  have hargs : target.ArgsIn [p, x] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hp, hxx]
  have hf := uf_module_fnspec k₀ hc hu 0 findFn (by simp)
    [p, x] m Q X hspec s ra R hargs hra hsp
    (by
      simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
      exact ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩)
  have hlab : target.labelAddr hh findFn.name = Host.addrOf k₀ :=
    labelAddr_of_unique (T := target) hu hc.append.1.cons.1
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, huf'⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx', _⟩)
  · rw [Std.ExtHashMap.sep_emp] at huf'
    refine ⟨hpc, ?_, fun r hr => ?_, ?_, sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩
    · simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
  · exact hx'.elim

/-- End-to-end correctness of compiled `union` (calling `find` twice) on Kraken AArch64: in every
host containing `findCode ++ unionCode` at `k₀` with unique labels, from a state with `p, x, y`
(`x, y < n`) in `x0, x1, x2`, 48 bytes of stack space below `sp`, return address `ra` in `x30`,
16-byte aligned `sp`, and memory `uf p n rep ⋆ ... ⋆ R`, execution eventually reaches `ra` with
callee-saved registers `x19`–`x29` and `sp` restored, and memory satisfying
`uf p n (merge rep x y) ⋆ ... ⋆ R`. -/
theorem union_arm64_correct (k₀ : Nat)
    (hc : (findCode ++ unionCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At (s.regs.SP.toBitVec - 48#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At (s.regs.SP.toBitVec - 48#64)) ⋆ R))
      ⟨s, Host.addrOf (k₀ + findCode.length)⟩ := by
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, huf, hentry⟩, hrest⟩ := hmem
  let Q : LeanQbe.Post := fun rets m' => rets = [] ∧ (uf p n (merge rep x y) ⋆ Std.ExtHashMap.emp) m'
  let X : XPost := fun _ _ _ => False
  have hm : (uf p n rep ⋆ Std.ExtHashMap.emp) m := by rwa [Std.ExtHashMap.sep_emp]
  have hspec : unionSpec [p, x, y] m Q X :=
    ⟨p, x, y, n, rep, Std.ExtHashMap.emp, rfl, hm, hx, hy, fun _ hm' => ⟨rfl, hm'⟩⟩
  have hargs : target.ArgsIn [p, x, y] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hp, hxx, hyy]
  have hf := uf_module_fnspec k₀ hc hu 0 unionFn (by simp)
    [p, x, y] m Q X hspec s ra R hargs hra hsp
    (by
      simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
      exact ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩)
  have hlab : target.labelAddr hh unionFn.name = Host.addrOf (k₀ + findCode.length) :=
    labelAddr_of_unique (T := target) hu hc.append.2.cons.1
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, huf'⟩, -, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx', _⟩)
  · rw [Std.ExtHashMap.sep_emp] at huf'
    refine ⟨hpc, fun r hr => ?_, ?_, sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
  · exact hx'.elim

/-- End-to-end correctness of compiled `unionInline` on Kraken AArch64. -/
theorem unionInline_arm64_correct (k₀ : Nat) (hc : unionInlineCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, huf, hentry⟩, hrest⟩ := hmem
  let Q : LeanQbe.Post := fun rets m' => rets = [] ∧ (uf p n (merge rep x y) ⋆ Std.ExtHashMap.emp) m'
  let X : XPost := fun _ _ _ => False
  have hm : (uf p n rep ⋆ Std.ExtHashMap.emp) m := by rwa [Std.ExtHashMap.sep_emp]
  have hspec : unionSpec [p, x, y] m Q X :=
    ⟨p, x, y, n, rep, Std.ExtHashMap.emp, rfl, hm, hx, hy, fun _ hm' => ⟨rfl, hm'⟩⟩
  have hargs : target.ArgsIn [p, x, y] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hp, hxx, hyy]
  have hf := unionInline_fnspec k₀ hc hu 0 [p, x, y] m Q X hspec s ra R hargs hra hsp
    (by
      simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
      exact ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩)
  have hlab : target.labelAddr hh "unionInline" = Host.addrOf k₀ :=
    labelAddr_of_unique (T := target) hu hc.cons.1
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, huf'⟩, -, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx', _⟩)
  · rw [Std.ExtHashMap.sep_emp] at huf'
    refine ⟨hpc, fun r hr => ?_, ?_, sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
  · exact hx'.elim

end Generic

/-! ## Non-vacuity: concrete host containing `findCode ++ unionCode ++ unionInlineCode` -/

def ufProg : Program := (findCode ++ unionCode) ++ unionInlineCode

abbrev ufHost : Host :=
  .ofLayout ufProg (layoutOf ufProg) (layoutOf_zero _) (of_decide_eq_true (by kernel_rfl))

attribute [local instance] ufHost

theorem ufHost_unique : Host.LabelsUnique :=
  Host.labelsUnique_of_nodup (of_decide_eq_true (by kernel_rfl))

theorem ufHost_mod : (findCode ++ unionCode).IsInfixAt Host.prog 0 := ⟨unionInlineCode, rfl⟩

theorem ufHost_unionInline :
    unionInlineCode.IsInfixAt Host.prog (findCode ++ unionCode).length := by
  show unionInlineCode.IsPrefix (((findCode ++ unionCode) ++ unionInlineCode).drop (findCode ++ unionCode).length)
  rw [List.drop_left]
  exact List.prefix_refl _

def ufInitBytes : List UInt8 := bytes64 (init 4)
def ufMem0 : Mem 64 := ufInitBytes.At 0x7000#64

def findState0 : MachineData :=
  { regs := { X0 := 0x7000, X1 := 3, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := (zeros16 ++ ufInitBytes).At 0x6ff0#64 }

def unionState0 : MachineData :=
  { regs := { X0 := 0x7000, X1 := 1, X2 := 2, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := (zeros48 ++ ufInitBytes).At 0x6fd0#64 }

def unionInlineState0 : MachineData :=
  { regs := { X0 := 0x7000, X1 := 1, X2 := 2, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := (zeros16 ++ ufInitBytes).At 0x6ff0#64 }

/-- Concrete execution of `find` on `init 4` at `0x7000`: `find(0x7000, 3)` returns `3` in `x0`. -/
theorem find_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 3 ∧
        (st.data.dmem =⋆ uf 0x7000#64 4 id ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At 0x6ff0#64) ⋆
          Std.ExtHashMap.emp))
      ⟨findState0, Host.addrOf 0⟩ := by
  have huflen : ufInitBytes.length = 32 := by decide
  have hm0 : uf 0x7000#64 4 id ufMem0 := uf_init 0x7000#64 (by decide)
  have hmem : findState0.dmem =⋆ uf 0x7000#64 4 id ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (findState0.regs.SP.toBitVec - 16#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep zeros16 ufInitBytes 0x6ff0#64 (by simp [zeros16, huflen])
    have e1 : (0x6ff0#64 + BitVec.ofNat 64 zeros16.length) = 0x7000#64 := by simp [zeros16]
    rw [e1] at h1
    have h0 : (Eq ((zeros16 ++ ufInitBytes).At 0x6ff0#64)) findState0.dmem := rfl
    rw [h1] at h0
    exact sep_mono_r (fun _ e => e ▸ hm0) (sep_mono (fun f1 hf1 => ⟨zeros16, by simp [zeros16], hf1.symm⟩) h0)
  have h := find_arm64_correct 0 ufHost_mod ufHost_unique 0x7000#64 3 4 id (by decide) findState0
    0x1234 Std.ExtHashMap.emp rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hx0, -, -, hm⟩
  exact ⟨hpc, hx0, hm⟩

/-- Concrete execution of `union` (calling `find` twice) on `init 4` at `0x7000`:
`union(0x7000, 1, 2)` returns with `uf 0x7000 4 (merge id 1 2)` in memory, where `1` and `2` share
a class and `0` is separate. -/
theorem union_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x7000#64 4 (merge id 1 2) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At 0x6fd0#64) ⋆
          Std.ExtHashMap.emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionState0, Host.addrOf findCode.length⟩ := by
  have huflen : ufInitBytes.length = 32 := by decide
  have hm0 : uf 0x7000#64 4 id ufMem0 := uf_init 0x7000#64 (by decide)
  have hmem : unionState0.dmem =⋆ uf 0x7000#64 4 id ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At (unionState0.regs.SP.toBitVec - 48#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep zeros48 ufInitBytes 0x6fd0#64 (by simp [zeros48, huflen])
    have e1 : (0x6fd0#64 + BitVec.ofNat 64 zeros48.length) = 0x7000#64 := by simp [zeros48]
    rw [e1] at h1
    have h0 : (Eq ((zeros48 ++ ufInitBytes).At 0x6fd0#64)) unionState0.dmem := rfl
    rw [h1] at h0
    exact sep_mono_r (fun _ e => e ▸ hm0) (sep_mono (fun f1 hf1 => ⟨zeros48, by simp [zeros48], hf1.symm⟩) h0)
  have h := union_arm64_correct 0 ufHost_mod ufHost_unique 0x7000#64 1 2 4 id (by decide) (by decide)
    unionState0 0x1234 Std.ExtHashMap.emp rfl rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, -, -, hm⟩
  exact ⟨hpc, hm, merge_init_1_2⟩

/-- Concrete execution of `unionInline` on `init 4` at `0x7000`. -/
theorem unionInline_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x7000#64 4 (merge id 1 2) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At 0x6ff0#64) ⋆
          Std.ExtHashMap.emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionInlineState0, Host.addrOf (findCode ++ unionCode).length⟩ := by
  have huflen : ufInitBytes.length = 32 := by decide
  have hm0 : uf 0x7000#64 4 id ufMem0 := uf_init 0x7000#64 (by decide)
  have hmem : unionInlineState0.dmem =⋆ uf 0x7000#64 4 id ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (unionInlineState0.regs.SP.toBitVec - 16#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep zeros16 ufInitBytes 0x6ff0#64 (by simp [zeros16, huflen])
    have e1 : (0x6ff0#64 + BitVec.ofNat 64 zeros16.length) = 0x7000#64 := by simp [zeros16]
    rw [e1] at h1
    have h0 : (Eq ((zeros16 ++ ufInitBytes).At 0x6ff0#64)) unionInlineState0.dmem := rfl
    rw [h1] at h0
    exact sep_mono_r (fun _ e => e ▸ hm0) (sep_mono (fun f1 hf1 => ⟨zeros16, by simp [zeros16], hf1.symm⟩) h0)
  have h := unionInline_arm64_correct (findCode ++ unionCode).length ufHost_unionInline ufHost_unique
    0x7000#64 1 2 4 id (by decide) (by decide) unionInlineState0 0x1234 Std.ExtHashMap.emp rfl rfl rfl
    rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, -, -, hm⟩
  exact ⟨hpc, hm, merge_init_1_2⟩

end LeanQbe.Arm64.UnionFind
