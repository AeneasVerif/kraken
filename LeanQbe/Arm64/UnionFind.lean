module

public import LeanQbe.Arm64.Litmus
public import LeanQbe.Examples.UnionFindLemmas

/-!
# Union-Find end to end on AArch64 (plan step 5)

Compiles `UnionFind.find` (with path halving) and `UnionFind.unionInline` through the full verified
pipeline (`compileFn Arm64.isa`: mid-end `Func.opt`, allocation oracle `Spill.hints`, verified
lowering `Rega.lowerFn`), checks the emitted AArch64 assembly by `kernel_rfl`, and connects
`compileFn_correct` with `UnionFind.find_correct` and `UnionFind.unionInline_correct` to obtain
end-to-end theorems stated solely in terms of Kraken's AArch64 operational semantics (`step1`) and
the functional partition model (`uf`, `merge`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.UnionFind

open LeanQbe LeanQbe.UnionFind LeanQbe.Arm64.Litmus Rega Kraken.AArch64.Parser

/-- `find` packaged as a named function. -/
def findFn : Fn := ⟨"find", find⟩

/-- `unionInline` packaged as a named function. -/
def unionInlineFn : Fn := ⟨"unionInline", unionInline⟩

/-- The AArch64 assembly emitted by `compileFn isa findFn`. -/
def findCode : Program := parseAArch64("find:
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
  ret")

/-- The AArch64 assembly emitted by `compileFn isa unionInlineFn`. -/
def unionInlineCode : Program := parseAArch64("unionInline:
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
  ret
  unionInline.L4:
  ret")

theorem find_compile : compileFn isa findFn = .ok findCode := by kernel_rfl

theorem unionInline_compile : compileFn isa unionInlineFn = .ok unionInlineCode := by kernel_rfl

section Generic
variable [hh : Host]

/-- `findCode` satisfies `findSpec` as a `Target.FnSpec` in any AArch64 host with unique labels. -/
theorem find_fnspec (k₀ : Nat) (hc : findCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (nX : Nat) : target.FnSpec hh "find" findSpec 0 nX :=
  Target.FnSpec.of_spec target
    (compileFn_correct (T := target) hh findFn (fun _ _ _ _ _ => False) 0 nX findCode k₀
      find_compile hc hu find_wf (by decide))
    (find_correct (fun _ _ _ _ _ => False))

/-- `unionInlineCode` satisfies `unionSpec` as a `Target.FnSpec` in any AArch64 host with unique
labels. -/
theorem unionInline_fnspec (k₀ : Nat) (hc : unionInlineCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (nX : Nat) : target.FnSpec hh "unionInline" unionSpec 0 nX :=
  Target.FnSpec.of_spec target
    (compileFn_correct (T := target) hh unionInlineFn (fun _ _ _ _ _ => False) 0 nX unionInlineCode
      k₀ unionInline_compile hc hu unionInline_wf (by decide))
    (unionInline_correct (fun _ _ _ _ _ => False))

/-- End-to-end correctness of compiled `find` on Kraken AArch64: in every host containing `findCode`
at `k₀` with unique labels, from a state with `p, x` (`x < n`) in `x0, x1`, return address `ra` in
`x30`, 16-byte aligned `sp`, and memory `uf p n rep ⋆ R`, execution eventually reaches `ra` with
the canonical representative `rep x` in `x0`, callee-saved registers `x19`–`x29` and `sp` restored,
and memory still satisfying `uf p n rep ⋆ R` (after path halving). -/
theorem find_arm64_correct (k₀ : Nat) (hc : findCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = rep x ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n rep ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  let Q : LeanQbe.Post := fun rets m' => rets = [rep x] ∧ (uf p n rep ⋆ R) m'
  let X : XPost := fun _ _ _ => False
  have hspec : findSpec [p, x] s.dmem Q X :=
    ⟨p, x, n, rep, R, rfl, hmem, hx, fun _ hm' => ⟨rfl, hm'⟩⟩
  have hargs : target.ArgsIn [p, x] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hp, hxx]
  have hmem' : target.mem s =⋆ Eq s.dmem ⋆ target.Entry (target.get s target.sp) ra 0 ⋆
      Std.ExtHashMap.emp := by
    simp [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
  have h := find_fnspec k₀ hc hu 0 [p, x] s.dmem Q X hspec s ra Std.ExtHashMap.emp hargs hra hsp
    hmem'
  have hlab : target.labelAddr hh "find" = Host.addrOf k₀ :=
    labelAddr_of_unique (T := target) hu hc.cons.1
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, huf'⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx', _⟩)
  · refine ⟨hpc, ?_, fun r hr => ?_, ?_, ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
    · simp only [Target.Exit, Nat.add_zero, region_zero, Std.ExtHashMap.sep_emp] at hm'
      exact hm' ▸ huf'
  · exact hx'.elim

/-- End-to-end correctness of compiled `unionInline` on Kraken AArch64: in every host containing
`unionInlineCode` at `k₀` with unique labels, from a state with `p, x, y` (`x, y < n`) in
`x0, x1, x2`, return address `ra` in `x30`, 16-byte aligned `sp`, and memory `uf p n rep ⋆ R`,
execution eventually reaches `ra` with callee-saved registers `x19`–`x29` and `sp` restored, and
memory satisfying `uf p n (merge rep x y) ⋆ R`. -/
theorem unionInline_arm64_correct (k₀ : Nat) (hc : unionInlineCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  let Q : LeanQbe.Post := fun rets m' => rets = [] ∧ (uf p n (merge rep x y) ⋆ R) m'
  let X : XPost := fun _ _ _ => False
  have hspec : unionSpec [p, x, y] s.dmem Q X :=
    ⟨p, x, y, n, rep, R, rfl, hmem, hx, hy, fun _ hm' => ⟨rfl, hm'⟩⟩
  have hargs : target.ArgsIn [p, x, y] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hp, hxx, hyy]
  have hmem' : target.mem s =⋆ Eq s.dmem ⋆ target.Entry (target.get s target.sp) ra 0 ⋆
      Std.ExtHashMap.emp := by
    simp [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
  have h := unionInline_fnspec k₀ hc hu 0 [p, x, y] s.dmem Q X hspec s ra Std.ExtHashMap.emp hargs
    hra hsp hmem'
  have hlab : target.labelAddr hh "unionInline" = Host.addrOf k₀ :=
    labelAddr_of_unique (T := target) hu hc.cons.1
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, huf'⟩, -, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx', _⟩)
  · refine ⟨hpc, fun r hr => ?_, ?_, ?_⟩
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
    · simp only [Target.Exit, Nat.add_zero, region_zero, Std.ExtHashMap.sep_emp] at hm'
      exact hm' ▸ huf'
  · exact hx'.elim

end Generic

/-! ## Non-vacuity: concrete host containing both `findCode` and `unionInlineCode`, and concrete state -/

def ufProg : Program := findCode ++ unionInlineCode

abbrev ufHost : Host := .ofLayout ufProg (layoutOf ufProg) (layoutOf_zero _) (by decide)

attribute [local instance] ufHost

theorem ufHost_unique : Host.LabelsUnique := Host.labelsUnique_of_nodup (by decide)

theorem ufHost_find : findCode.IsInfixAt Host.prog 0 := ⟨unionInlineCode, rfl⟩

theorem ufHost_unionInline : unionInlineCode.IsInfixAt Host.prog findCode.length := by
  show unionInlineCode.IsPrefix ((findCode ++ unionInlineCode).drop findCode.length)
  rw [List.drop_left]
  exact List.prefix_refl _

def ufMem0 : Mem 64 := (bytes64 (init 4)).At 0x2000#64

def findState0 : MachineData :=
  { regs := { X0 := 0x2000, X1 := 3, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := ufMem0 }

def unionState0 : MachineData :=
  { regs := { X0 := 0x2000, X1 := 1, X2 := 2, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := ufMem0 }

/-- Concrete execution of `find` on `init 4` at `0x2000`: `find(0x2000, 3)` returns `3` in `x0`. -/
theorem find_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 3 ∧
        (st.data.dmem =⋆ uf 0x2000#64 4 id ⋆ Std.ExtHashMap.emp))
      ⟨findState0, Host.addrOf 0⟩ := by
  have hmem : findState0.dmem =⋆ uf 0x2000#64 4 id ⋆ Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    exact uf_init 0x2000#64 (by decide)
  have h := find_arm64_correct 0 ufHost_find ufHost_unique 0x2000#64 3 4 id (by decide) findState0
    0x1234 Std.ExtHashMap.emp rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hx0, -, -, hm⟩
  exact ⟨hpc, hx0, hm⟩

/-- Concrete execution of `unionInline` on `init 4` at `0x2000`: `unionInline(0x2000, 1, 2)` returns
with `uf 0x2000 4 (merge id 1 2)` in memory, where `1` and `2` share a class (`merge id 1 2 1 = 2`)
and `0` is separate. -/
theorem unionInline_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x2000#64 4 (merge id 1 2) ⋆ Std.ExtHashMap.emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionState0, Host.addrOf findCode.length⟩ := by
  have hmem : unionState0.dmem =⋆ uf 0x2000#64 4 id ⋆ Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    exact uf_init 0x2000#64 (by decide)
  have h := unionInline_arm64_correct findCode.length ufHost_unionInline ufHost_unique 0x2000#64 1 2
    4 id (by decide) (by decide) unionState0 0x1234 Std.ExtHashMap.emp rfl rfl rfl rfl (by decide)
    hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, -, -, hm⟩
  exact ⟨hpc, hm, merge_init_1_2⟩

end LeanQbe.Arm64.UnionFind
