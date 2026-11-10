module

public import LeanQbe.Examples.Litmus
public import LeanQbe.Examples.UnionFindLemmas
public import LeanQbe.MainLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Union-Find end to end on x64 (plan step 5)

Compiles the two-function Union-Find module `[findFn, unionFn]` (`union` calls `find` twice, with
`p`, `y`, and `rx` spilled across calls) through `compileModule Amd64.isa`, checks the emitted x64
assembly and computed stack bounds `[("find", 8), ("union", 40)]` in the kernel (`kernel_rfl`),
links the module via `compile_sound` (`uf_module_fnspec`), and proves Kraken-x64-only end-to-end
theorems (`find_x64_correct`, `union_x64_correct`, entering at `Labels.label "find"` and
`Labels.label "union"`) and concrete non-vacuity instances (`find_x64_nonvacuous`,
`union_x64_nonvacuous`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

open LeanQbe LeanQbe.UnionFind Rega Amd64

/-- `find` packaged as a named function. -/
abbrev findFn : Fn := ⟨"find", find⟩

/-- `union` (calling `find` twice) packaged as a named function. -/
abbrev unionFn : Fn := ⟨"union", union⟩

/-- The x64 assembly emitted by `compileFn Amd64.isa findFn`. -/
def findCode : Program := parse("find:
  subq $8, %rsp
  movq %rsi, %rax
  jmp find.L0
  find.L0:
  movq %rax, %r11
  movq %rcx, %r10
  movq $3, %rcx
  shlq %cl, %r11
  movq %r10, %rcx
  movq %r11, %rcx
  movq %rdi, %r11
  movq %rcx, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq (%rcx), %rdx
  movq %rdx, %r11
  movq %rax, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %esi
  testl %esi, %esi
  jne find.L1
  movq %rdx, %r11
  movq %rcx, %r10
  movq $3, %rcx
  shlq %cl, %r11
  movq %r10, %rcx
  movq %r11, %rax
  movq %rdi, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq (%rax), %rax
  movq %rax, %r11
  movq %r11, (%rcx)
  jmp find.L0
  find.L1:
  addq $8, %rsp
  ret")

/-- The x64 assembly emitted by `compileFn Amd64.isa unionFn`. -/
def unionCode : Program := parse("union:
  subq $24, %rsp
  movq %rdi, (%rsp)
  movq %rdx, 8(%rsp)
  call find
  movq %rax, 16(%rsp)
  movq (%rsp), %rdi
  movq 8(%rsp), %rsi
  call find
  movq 16(%rsp), %rcx
  movq %rcx, %r11
  movq %rax, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %ecx
  testl %ecx, %ecx
  jne union.L0
  movq 16(%rsp), %rcx
  movq %rcx, %r11
  movq %rcx, %r10
  movq $3, %rcx
  shlq %cl, %r11
  movq %r10, %rcx
  movq %r11, %rcx
  movq (%rsp), %rdx
  movq %rdx, %r11
  movq %rcx, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq %rax, %r11
  movq %r11, (%rcx)
  addq $24, %rsp
  ret
  union.L0:
  addq $24, %rsp
  ret")

def ufBounds : List (String × Nat) := [("find", 8), ("union", 40)]

theorem find_compile : compileFn Amd64.isa findFn = .ok findCode := by kernel_rfl
theorem union_compile : compileFn Amd64.isa unionFn = .ok unionCode := by kernel_rfl

theorem uf_module_compile :
    compileModule Amd64.isa 8 [] [] 0 [findFn, unionFn] =
      .ok (findCode ++ unionCode, ufBounds) := by kernel_rfl

def ufEnv : Env := fun g => if g = "find" then findSpec else unionSpec

section Generic
variable [hh : Host]

/-- Linking `[findFn, unionFn]` via `compile_sound`. -/
theorem uf_module_fnspec (k₀ : Nat)
    (hc : (findCode ++ unionCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∀ p ∈ ufBounds,
      Amd64.target.Defined hh p.1 ∧ Amd64.target.FnSpec hh p.1 (ufEnv p.1) p.2 0 := by
  refine compile_sound (T := Amd64.target) hh ufEnv [] [] 0 [findFn, unionFn]
    (findCode ++ unionCode) ufBounds k₀ uf_module_compile hc hu ?_ ?_
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  · intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | rfl | h
    · exact find_wf
    · exact union_wf
    · nomatch h
  · intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | rfl | h
    · exact find_correct _
    · exact union_correct _ (fun _ _ _ _ h => h)
    · nomatch h

/-- End-to-end correctness of compiled `find` on Kraken x64: in every host containing
`findCode ++ unionCode` at `k₀` with unique labels, from a state at `Labels.label "find"` with
`p, x` (`x < n`) in `rdi, rsi`, 8 bytes of stack space below `rsp`, return address `ra` at `rsp`,
and memory `uf p n rep ⋆ ... ⋆ R`, execution eventually reaches `ra` with the canonical
representative `rep x` in `rax`, callee-saved registers intact, `rsp` popped, and memory satisfying
`uf p n rep ⋆ ... ⋆ R` (after path halving). -/
theorem find_x64_correct (k₀ : Nat)
    (hc : (findCode ++ unionCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (s.regs.get64 .rsp - 8#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = rep x ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ uf p n rep ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.get64 .rsp - 8#64)) ⋆ R))
      ⟨s, Labels.label "find"⟩ := by
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, huf, hentry⟩, hrest⟩ := hmem
  let Q : LeanQbe.Post := fun rets m' => rets = [rep x] ∧ (uf p n rep ⋆ Std.ExtHashMap.emp) m'
  let X : XPost := fun _ _ _ => False
  have hm : (uf p n rep ⋆ Std.ExtHashMap.emp) m := by rwa [Std.ExtHashMap.sep_emp]
  have hspec : findSpec [p, x] m Q X :=
    ⟨p, x, n, rep, Std.ExtHashMap.emp, rfl, hm, hx, fun _ hm' => ⟨rfl, hm'⟩⟩
  have hargs : Amd64.target.ArgsIn [p, x] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, hp, hxx]
  have hf := (uf_module_fnspec k₀ hc hu ("find", 8) (by simp [ufBounds])).2
    [p, x] m Q X hspec s ra R hargs trivial hsp
    ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, huf'⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx', _⟩)
  · rw [Std.ExtHashMap.sep_emp] at huf'
    refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩
    simpa [Target.RetsIn, Target.ValsIn, Amd64.target, Amd64.isa] using hrets
  · exact hx'.elim

/-- End-to-end correctness of compiled `union` (calling `find` twice) on Kraken x64: in every host
containing `findCode ++ unionCode` at `k₀` with unique labels, from a state at
`Labels.label "union"` with `p, x, y` (`x, y < n`) in `rdi, rsi, rdx`, 40 bytes of stack space
below `rsp`, return address `ra` at `rsp`, and memory `uf p n rep ⋆ ... ⋆ R`, execution eventually
reaches `ra` with callee-saved registers intact, `rsp` popped, and memory satisfying
`uf p n (merge rep x y) ⋆ ... ⋆ R`. -/
theorem union_x64_correct (k₀ : Nat)
    (hc : (findCode ++ unionCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x) (hyy : s.regs.get64 .rdx = y)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ uf p n rep ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 40 ∧ f = bs.At (s.regs.get64 .rsp - 40#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ uf p n (merge rep x y) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At (s.regs.get64 .rsp - 40#64)) ⋆ R))
      ⟨s, Labels.label "union"⟩ := by
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, huf, hentry⟩, hrest⟩ := hmem
  let Q : LeanQbe.Post := fun rets m' => rets = [] ∧ (uf p n (merge rep x y) ⋆ Std.ExtHashMap.emp) m'
  let X : XPost := fun _ _ _ => False
  have hm : (uf p n rep ⋆ Std.ExtHashMap.emp) m := by rwa [Std.ExtHashMap.sep_emp]
  have hspec : unionSpec [p, x, y] m Q X :=
    ⟨p, x, y, n, rep, Std.ExtHashMap.emp, rfl, hm, hx, hy, fun _ hm' => ⟨rfl, hm'⟩⟩
  have hargs : Amd64.target.ArgsIn [p, x, y] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, hp, hxx, hyy]
  have hf := (uf_module_fnspec k₀ hc hu ("union", 40) (by simp [ufBounds])).2
    [p, x, y] m Q X hspec s ra R hargs trivial hsp
    ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, huf'⟩, -, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx', _⟩)
  · rw [Std.ExtHashMap.sep_emp] at huf'
    exact ⟨hpc, fun r hr => hcs r hr, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'⟩
  · exact hx'.elim

end Generic

/-! ## Non-vacuity: concrete host containing `findCode ++ unionCode` and concrete state -/

def ufProg : Program := findCode ++ unionCode

abbrev ufHost : Host :=
  .ofLayout ufProg (layoutOf ufProg) (layoutOf_zero _) (of_decide_eq_true (by kernel_rfl))

attribute [local instance] ufHost

theorem ufHost_unique : Host.LabelsUnique :=
  Host.labelsUnique_of_nodup (of_decide_eq_true (by kernel_rfl))

def ufInitBytes : List UInt8 := bytes64 (init 4)
def ufMem0 : Mem 64 := ufInitBytes.At 0x7010#64

def findState0 : MachineData :=
  { regs := { rdi := 0x7010, rsi := 3, rsp := 0x7008 },
    dmem := ((zeros8 ++ raBytes0) ++ ufInitBytes).At 0x7000#64 }

def unionState0 : MachineData :=
  { regs := { rdi := 0x7010, rsi := 1, rdx := 2, rsp := 0x7008 },
    dmem := ((zeros40 ++ raBytes0) ++ ufInitBytes).At 0x6fe0#64 }

/-- Concrete execution of `find` on `init 4` at `0x7010`: `find(0x7010, 3)` returns `3` in `rax`. -/
theorem find_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 3 ∧
        (st.data.dmem =⋆ uf 0x7010#64 4 id ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At 0x7000#64) ⋆
          Std.ExtHashMap.emp))
      ⟨findState0, Labels.label "find"⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have huflen : ufInitBytes.length = 32 := by decide
  have hm0 : uf 0x7010#64 4 id ufMem0 := uf_init 0x7010#64 (by decide)
  have hmem : findState0.dmem =⋆ uf 0x7010#64 4 id ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (findState0.regs.get64 .rsp - 8#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (findState0.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep (zeros8 ++ raBytes0) ufInitBytes 0x7000#64
      (by simp [hlen, zeros8, huflen])
    have e1 : (0x7000#64 + BitVec.ofNat 64 (zeros8 ++ raBytes0).length) = 0x7010#64 := by
      simp [zeros8, hlen]
    rw [e1] at h1
    have h2 := Mem.At_append_sep zeros8 raBytes0 0x7000#64 (by simp [hlen, zeros8])
    have e2 : (0x7000#64 + BitVec.ofNat 64 zeros8.length) = 0x7008#64 := by simp [zeros8]
    rw [e2] at h2
    have h0 : (Eq (((zeros8 ++ raBytes0) ++ ufInitBytes).At 0x7000#64)) findState0.dmem := rfl
    rw [h1] at h0
    refine sep_mono_r (fun _ e => e ▸ hm0) (sep_mono (fun f hf => ?_) h0)
    rw [h2] at hf
    exact sep_mono (fun f1 hf1 => ⟨zeros8, by simp [zeros8], hf1.symm⟩) hf
  have h := find_x64_correct 0 (List.prefix_refl _) ufHost_unique 0x7010#64 3 4 id (by decide)
    findState0 0x1234 Std.ExtHashMap.emp rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -, -, hm⟩
  exact ⟨hpc, hrax, hm⟩

/-- Concrete execution of `union` (calling `find` twice) on `init 4` at `0x7010`:
`union(0x7010, 1, 2)` returns with `uf 0x7010 4 (merge id 1 2)` in memory, where `1` and `2` share
a class and `0` is separate. -/
theorem union_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ uf 0x7010#64 4 (merge id 1 2) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At 0x6fe0#64) ⋆
          Std.ExtHashMap.emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      ⟨unionState0, Labels.label "union"⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have huflen : ufInitBytes.length = 32 := by decide
  have hm0 : uf 0x7010#64 4 id ufMem0 := uf_init 0x7010#64 (by decide)
  have hmem : unionState0.dmem =⋆ uf 0x7010#64 4 id ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 40 ∧ f = bs.At (unionState0.regs.get64 .rsp - 40#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (unionState0.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep (zeros40 ++ raBytes0) ufInitBytes 0x6fe0#64
      (by simp [hlen, zeros40, huflen])
    have e1 : (0x6fe0#64 + BitVec.ofNat 64 (zeros40 ++ raBytes0).length) = 0x7010#64 := by
      simp [zeros40, hlen]
    rw [e1] at h1
    have h2 := Mem.At_append_sep zeros40 raBytes0 0x6fe0#64 (by simp [hlen, zeros40])
    have e2 : (0x6fe0#64 + BitVec.ofNat 64 zeros40.length) = 0x7008#64 := by simp [zeros40]
    rw [e2] at h2
    have h0 : (Eq (((zeros40 ++ raBytes0) ++ ufInitBytes).At 0x6fe0#64)) unionState0.dmem := rfl
    rw [h1] at h0
    refine sep_mono_r (fun _ e => e ▸ hm0) (sep_mono (fun f hf => ?_) h0)
    rw [h2] at hf
    exact sep_mono (fun f1 hf1 => ⟨zeros40, by simp [zeros40], hf1.symm⟩) hf
  have h := union_x64_correct 0 (List.prefix_refl _) ufHost_unique 0x7010#64 1 2 4 id
    (by decide) (by decide) unionState0 0x1234 Std.ExtHashMap.emp rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, -, -, hm⟩
  exact ⟨hpc, hm, merge_init_1_2⟩

end LeanQbe.Litmus
