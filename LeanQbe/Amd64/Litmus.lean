module

public import LeanQbe.Amd64.TargLemmas
public import LeanQbe.Examples.LitmusProgsLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Litmus suite on x64

Instantiates all 10 litmus programs (`tracer`, `ifelse`, `sumto`, `evenodd`, `nested`, `swap`,
`spill10`, `callinc`, `twice`, `sumcall`) on `Amd64.target` via one kernel evaluation per program
(`compileChecked ... (by kernel_rfl)`), proving `FnSpec`s, closed Kraken-x64 end-to-end theorems,
and concrete execution witnesses.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Amd64.Litmus

open LeanQbe LeanQbe.Litmus Amd64 Kraken

def tracerCompiled : Compiled target [] [] 0 [tracer] :=
  compileChecked target targetLayout [] [] 0 [tracer] 2048 (by kernel_rfl)

def ifelseCompiled : Compiled target [] [] 0 [ifelse] :=
  compileChecked target targetLayout [] [] 0 [ifelse] 2048 (by kernel_rfl)

def sumtoCompiled : Compiled target [] [] 0 [sumto] :=
  compileChecked target targetLayout [] [] 0 [sumto] 2048 (by kernel_rfl)

def evenoddCompiled : Compiled target [] [] 0 [evenodd] :=
  compileChecked target targetLayout [] [] 0 [evenodd] 2048 (by kernel_rfl)

def nestedCompiled : Compiled target [] [] 0 [nested] :=
  compileChecked target targetLayout [] [] 0 [nested] 2048 (by kernel_rfl)

def swapCompiled : Compiled target [] [] 0 [swap] :=
  compileChecked target targetLayout [] [] 0 [swap] 2048 (by kernel_rfl)

def spill10Compiled : Compiled target [] [] 0 [spill10] :=
  compileChecked target targetLayout [] [] 0 [spill10] 2048 (by kernel_rfl)

def callincCompiled : Compiled target [] [] 0 [inc, callinc] :=
  compileChecked target targetLayout [] [] 0 [inc, callinc] 2048 (by kernel_rfl)

def twiceCompiled : Compiled target [] ["fail"] 0 [check, twice] :=
  compileChecked target targetLayout [] ["fail"] 0 [check, twice] 2048 (by kernel_rfl)

def sumcallCompiled : Compiled target [] [] 0 [inc, sumcall] :=
  compileChecked target targetLayout [] [] 0 [inc, sumcall] 2048 (by kernel_rfl)

section Generic
variable [hh : Host]

theorem tracer_fnspec (k₀ : Nat) (hc : tracerCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    target.Defined hh "tracer" ∧
      target.FnSpec hh "tracer" (Func.spec emptyEnv tracer.body) (tracerCompiled.bound "tracer") 0 :=
  leaf_fnSpec tracerCompiled tracer_wf hh k₀ hc hu

theorem ifelse_fnspec (k₀ : Nat) (hc : ifelseCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    target.Defined hh "ifelse" ∧
      target.FnSpec hh "ifelse" (Func.spec emptyEnv ifelse.body) (ifelseCompiled.bound "ifelse") 0 :=
  leaf_fnSpec ifelseCompiled ifelse_wf hh k₀ hc hu

theorem sumto_fnspec (k₀ : Nat) (hc : sumtoCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    target.Defined hh "sumto" ∧
      target.FnSpec hh "sumto" (Func.spec emptyEnv sumto.body) (sumtoCompiled.bound "sumto") 0 :=
  leaf_fnSpec sumtoCompiled sumto_wf hh k₀ hc hu

theorem evenodd_fnspec (k₀ : Nat) (hc : evenoddCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    target.Defined hh "evenodd" ∧
      target.FnSpec hh "evenodd" (Func.spec emptyEnv evenodd.body) (evenoddCompiled.bound "evenodd") 0 :=
  leaf_fnSpec evenoddCompiled evenodd_wf hh k₀ hc hu

theorem nested_fnspec (k₀ : Nat) (hc : nestedCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    target.Defined hh "nested" ∧
      target.FnSpec hh "nested" (Func.spec emptyEnv nested.body) (nestedCompiled.bound "nested") 0 :=
  leaf_fnSpec nestedCompiled nested_wf hh k₀ hc hu

theorem swap_fnspec (k₀ : Nat) (hc : swapCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    target.Defined hh "swap" ∧
      target.FnSpec hh "swap" (Func.spec emptyEnv swap.body) (swapCompiled.bound "swap") 0 :=
  leaf_fnSpec swapCompiled swap_wf hh k₀ hc hu

theorem spill10_fnspec (k₀ : Nat) (hc : spill10Compiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) :
    target.Defined hh "spill10" ∧
      target.FnSpec hh "spill10" (Func.spec emptyEnv spill10.body) (spill10Compiled.bound "spill10") 0 :=
  leaf_fnSpec spill10Compiled spill10_wf hh k₀ hc hu

theorem callinc_module_fnspec (k₀ : Nat)
    (hc : callincCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {nm : String} (hnm : nm ∈ [inc, callinc].map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (callincEnv nm) (callincCompiled.bound nm) 0 :=
  callinc_fnSpec callincCompiled hh k₀ hc hu hnm

theorem twice_module_fnspec (k₀ : Nat)
    (hc : twiceCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "fail")
    {nm : String} (hnm : nm ∈ [check, twice].map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (twiceEnv nm) (twiceCompiled.bound nm) 0 :=
  twice_fnSpec twiceCompiled hh k₀ hc hu hfail hnm

theorem sumcall_module_fnspec (k₀ : Nat)
    (hc : sumcallCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {nm : String} (hnm : nm ∈ [inc, sumcall].map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (sumcallEnv nm) (sumcallCompiled.bound nm) 0 :=
  sumcall_fnSpec sumcallCompiled hh k₀ hc hu hnm

/-- `tracer` on Kraken x64. -/
theorem tracer_correct (k₀ : Nat) (hc : tracerCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b p : BitVec 64) (m : Mem 64)
    (hp : ∃ i, m.loadInt p 8 = some i)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b) (hpp : s.regs.get64 .rdx = p)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = tracerCompiled.bound "tracer" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ Eq (m.storeInt p 8 (a + b).toInt) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = tracerCompiled.bound "tracer" + 8 ∧
              f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))) ⋆ R))
      ⟨s, Labels.label "tracer"⟩ := by
  have hargs : target.ArgsIn [a, b, p] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, ha, hb, hpp]
  have hp' : storeOk m .l p := by simpa [storeOk, Sz.bytes] using hp
  refine eventually_weaken _ _ _ _ ?_
    (amd64_of_returns (tracer_returns tracerCompiled hh k₀ hc hu a b p m hp') s ra R hargs hsp
      hmem)
  rintro st ⟨hpc, hcs, hsp', rets, hrets,
    f1, f2, hu1, hd1, ⟨m', fe, hu2, hd2, ⟨rfl, hstore⟩, hexit⟩, hf2⟩
  refine ⟨hpc, ?_, hcs, hsp', f1, f2, hu1, hd1, ⟨m', fe, hu2, hd2, hstore.symm, hexit⟩, hf2⟩
  simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets

/-- `sumto` on Kraken x64. -/
theorem sumto_correct (k₀ : Nat) (hc : sumtoCompiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (n : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = sumtoCompiled.bound "sumto" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (sumtoCompiled.bound "sumto"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = tri n.toNat ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun f => ∃ bs : List UInt8, bs.length = sumtoCompiled.bound "sumto" + 8 ∧
              f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (sumtoCompiled.bound "sumto"))) ⋆ R))
      ⟨s, Labels.label "sumto"⟩ := by
  have hargs : target.ArgsIn [n] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, hrdi]
  refine eventually_weaken _ _ _ _ ?_
    (amd64_of_returns_emp (sumto_returns sumtoCompiled hh k₀ hc hu n hn) s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, hrets, rfl, hm'⟩
  refine ⟨hpc, ?_, hcs, hsp', hm'⟩
  simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets

/-- `callinc` on Kraken x64. -/
theorem callinc_correct (k₀ : Nat)
    (hc : callincCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = callincCompiled.bound "callinc" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (callincCompiled.bound "callinc"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = a + 1 + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun f => ∃ bs : List UInt8, bs.length = callincCompiled.bound "callinc" + 8 ∧
              f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (callincCompiled.bound "callinc"))) ⋆ R))
      ⟨s, Labels.label "callinc"⟩ := by
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, ha, hb]
  refine eventually_weaken _ _ _ _ ?_
    (amd64_of_returns_emp (callinc_returns callincCompiled hh k₀ hc hu a b) s ra R hargs hsp
      hmem)
  rintro st ⟨hpc, hcs, hsp', rets, hrets, rfl, hm'⟩
  refine ⟨hpc, ?_, hcs, hsp', hm'⟩
  simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets

/-- `twice` on Kraken x64. -/
theorem twice_correct (k₀ : Nat)
    (hc : twiceCompiled.code.IsInfixAt Host.prog k₀)
    (hfail : target.Defined hh "fail") (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = twiceCompiled.bound "twice" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (twiceCompiled.bound "twice"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (Truthy a ∧ Truthy b ∧ st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64) ∨
        ((¬Truthy a ∧ st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = a ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0) ∨
         (Truthy a ∧ ¬Truthy b ∧ st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = b ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0)))
      ⟨s, Labels.label "twice"⟩ := by
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, ha, hb]
  have hmem' : s.dmem =⋆ Std.ExtHashMap.emp ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = twiceCompiled.bound "twice" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (twiceCompiled.bound "twice"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R := by
    rw [Std.ExtHashMap.emp_sep]; exact hmem
  refine eventually_weaken _ _ _ _ ?_
    (amd64_of_call_emp (twice_call twiceCompiled hh k₀ hc hu hfail a b) s ra R hargs hsp hmem')
  rintro st (⟨hpc, hcs, hsp', rets, hrets, hm'⟩ |
    ⟨sym', as', -, hpc, has', hspE, m', rfl, _, hcase⟩)
  · obtain ⟨_, _, _, _, ⟨_, _, _, _, ⟨hta, htb, rfl, _⟩, _⟩, _⟩ := hm'
    refine Or.inl ⟨hta, htb, hpc, ?_, hcs, hsp'⟩
    simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
  · rcases hcase with ⟨hna, rfl⟩ | ⟨hta, hnb, rfl⟩
    · refine Or.inr (Or.inl ⟨hna, hpc, ?_, hspE⟩)
      simpa [Target.ArgsIn, Target.ValsIn, target, isa] using has'
    · refine Or.inr (Or.inr ⟨hta, hnb, hpc, ?_, hspE⟩)
      simpa [Target.ArgsIn, Target.ValsIn, target, isa] using has'

/-- `spill10` on Kraken x64. -/
theorem spill10_correct (k₀ : Nat) (hc : spill10Compiled.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b : BitVec 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = spill10Compiled.bound "spill10" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (spill10Compiled.bound "spill10"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = spill10Val a b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun f => ∃ bs : List UInt8, bs.length = spill10Compiled.bound "spill10" + 8 ∧
              f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (spill10Compiled.bound "spill10"))) ⋆ R))
      ⟨s, Labels.label "spill10"⟩ := by
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, ha, hb]
  refine eventually_weaken _ _ _ _ ?_
    (amd64_of_returns_emp (spill10_returns spill10Compiled hh k₀ hc hu a b) s ra R hargs hsp
      hmem)
  rintro st ⟨hpc, hcs, hsp', rets, hrets, rfl, hm'⟩
  refine ⟨hpc, ?_, hcs, hsp', hm'⟩
  simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets

end Generic

/-! ## Concrete x64 execution witnesses -/

abbrev tracerHost : Host := tracerCompiled.host
def tracerState0 : MachineData := initState (tracerCompiled.bound "tracer") zeros8 [40, 2, 0x1000]

attribute [local instance] tracerHost in
theorem tracer_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42 ∧
        (st.data.dmem =⋆ Eq (m0.storeInt 0x1000#64 8 (42 : BitVec 64).toInt) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = tracerCompiled.bound "tracer" + 8 ∧
              f = bs.At (0x0ff8#64 - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))) ⋆
          Std.ExtHashMap.emp))
      ⟨tracerState0, Labels.label "tracer"⟩ :=
  targetInit.run_ret1_sep tracerCompiled (tracer_fnspec 0 tracerCompiled.code_infix_host
      tracerCompiled.labelsUnique).2 zeros8 [40, 2, 0x1000] 42 _ (by decide) (by decide)
    (tracer_spec emptyEnv 40 2 0x1000#64 m0 (by simpa [storeOk, Sz.bytes] using m0_loadInt))
    fun _ _ ⟨hr, hm⟩ => ⟨hr, hm.symm⟩

abbrev sumtoHost : Host := sumtoCompiled.host
def sumtoState : MachineData := initState (sumtoCompiled.bound "sumto") [] [3]

attribute [local instance] sumtoHost in
theorem sumto_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 6)
      ⟨sumtoState, Labels.label "sumto"⟩ :=
  targetInit.run_ret1 sumtoCompiled (sumto_fnspec 0 sumtoCompiled.code_infix_host
      sumtoCompiled.labelsUnique).2 [] [3] 6 (by decide) (by decide)
    (sumto_spec emptyEnv 3 (by decide) _) fun _ _ ⟨hr, _⟩ => hr

abbrev callincHost : Host := callincCompiled.host
def callincState : MachineData := initState (callincCompiled.bound "callinc") [] [40, 1]

attribute [local instance] callincHost in
theorem callinc_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42)
      ⟨callincState, Labels.label "callinc"⟩ :=
  targetInit.run_ret1 callincCompiled (callinc_module_fnspec 0 callincCompiled.code_infix_host
      callincCompiled.labelsUnique (by decide)).2 [] [40, 1] 42 (by decide) (by decide)
    (Q := fun r _ => r = [42]) ⟨40, 1, rfl, rfl⟩ fun _ _ h => h

abbrev twiceHost : Host := twiceCompiled.host
def twiceState (a b : UInt64) : MachineData :=
  initState (twiceCompiled.bound "twice") [] [a.toBitVec, b.toBitVec]

attribute [local instance] twiceHost in
theorem twice_nonvacuous_exit :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = 0)
      ⟨twiceState 20 0, Labels.label "twice"⟩ := by
  refine targetInit.run_fnSpec twiceCompiled (twice_module_fnspec 0 twiceCompiled.code_infix_host
      twiceCompiled.labelsUnique (twiceCompiled.defined_exit_host (by simp)) (nm := "twice")
      (by decide)).2 [] [20, 0] (by decide) (by decide)
    (Q := fun _ _ => False) (X := fun g xs _ => g = "fail" ∧ xs = [0])
    ⟨20, 0, rfl, fun _ h0 => absurd h0 (by decide),
      fun h20 => absurd (by decide : Truthy 20) h20, fun _ _ => ⟨rfl, rfl⟩⟩ ?_
  rintro st (⟨_, _, _, hq, _⟩ | ⟨_, _, _, ⟨rfl, rfl⟩, hpc, has⟩)
  · exact hq.elim
  · exact ⟨hpc, targetInit.argsIn_singleton 0 _ has⟩

abbrev spill10Host : Host := spill10Compiled.host
def spill10State : MachineData := initState (spill10Compiled.bound "spill10") [] [10, 7]

attribute [local instance] spill10Host in
theorem spill10_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = spill10Val 10 7)
      ⟨spill10State, Labels.label "spill10"⟩ :=
  targetInit.run_ret1 spill10Compiled (spill10_fnspec 0 spill10Compiled.code_infix_host
      spill10Compiled.labelsUnique).2 [] [10, 7] (spill10Val 10 7) (by decide) (by decide)
    (spill10_spec emptyEnv 10 7 _) fun _ _ ⟨hr, _⟩ => hr

end LeanQbe.Amd64.Litmus
