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
  have hwp : Func.spec emptyEnv tracer.body [a, b, p] m
      (fun rets m' => rets = [a + b] ∧ m' = storeMem m .l p (a + b)) (fun _ _ _ => False) :=
    tracer_spec emptyEnv a b p m (by simpa [storeOk, Sz.bytes] using hp)
  have hargs : target.ArgsIn [a, b, p] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, ha, hb, hpp]
  have h := (tracer_fnspec k₀ hc hu).2 [a, b, p] m _ _ hwp s ra R hargs trivial hsp hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', hm'⟩
    simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
  · exact hx.elim

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
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [n] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, hrdi]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆
      target.Entry (target.get s target.sp) ra (sumtoCompiled.bound "sumto") ⋆ R := by
    rw [hE, Std.ExtHashMap.emp_sep]; exact hmem
  have h := (sumto_fnspec k₀ hc hu).2 [n] ∅ _ _ (sumto_spec emptyEnv n hn ∅)
    s ra R hargs trivial hsp hmem'
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'; exact hm'
  · exact hx.elim

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
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, ha, hb]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆
      target.Entry (target.get s target.sp) ra (callincCompiled.bound "callinc") ⋆ R := by
    rw [hE, Std.ExtHashMap.emp_sep]; exact hmem
  have hf := (callinc_module_fnspec k₀ hc hu (nm := "callinc") (by decide)).2
    [a, b] ∅ (fun r m' => r = [a + 1 + b] ∧ m' = ∅) (fun _ _ _ => False) ⟨a, b, rfl, rfl, rfl⟩
    s ra R hargs trivial hsp hmem'
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'; exact hm'
  · exact hx.elim

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
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, ha, hb]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆
      target.Entry (target.get s target.sp) ra (twiceCompiled.bound "twice") ⋆ R := by
    rw [hE, Std.ExtHashMap.emp_sep]; exact hmem
  let Q : LeanQbe.Post := fun r m' => Truthy a ∧ Truthy b ∧ r = [a + b] ∧ m' = ∅
  let X : XPost := fun g xs m' =>
    g = "fail" ∧ m' = ∅ ∧ ((¬Truthy a ∧ xs = [a]) ∨ (Truthy a ∧ ¬Truthy b ∧ xs = [b]))
  have hspec : twiceContract [a, b] ∅ Q X :=
    ⟨a, b, rfl, fun hta htb => ⟨hta, htb, rfl, rfl⟩,
      fun hna => ⟨rfl, rfl, Or.inl ⟨hna, rfl⟩⟩,
      fun hta hnb => ⟨rfl, rfl, Or.inr ⟨hta, hnb, rfl⟩⟩⟩
  have hf := (twice_module_fnspec k₀ hc hu hfail (nm := "twice") (by decide)).2
    [a, b] ∅ Q X hspec s ra R hargs trivial hsp hmem'
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨hta, htb, rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, _⟩ |
    ⟨sym', as', m', ⟨rfl, rfl, hcase⟩, _, hpc, has', hspE, _⟩)
  · refine Or.inl ⟨hta, htb, hpc, ?_, fun r hr => hcs r hr, hsp'⟩
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
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, ha, hb]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆
      target.Entry (target.get s target.sp) ra (spill10Compiled.bound "spill10") ⋆ R := by
    rw [hE, Std.ExtHashMap.emp_sep]; exact hmem
  have h := (spill10_fnspec k₀ hc hu).2 [a, b] ∅ _ _ (spill10_spec emptyEnv a b ∅)
    s ra R hargs trivial hsp hmem'
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'; exact hm'
  · exact hx.elim

end Generic

/-! ## Concrete x64 execution witnesses -/

abbrev tracerHost : Host := tracerCompiled.host
def tracerState0 : MachineData :=
  { regs := { rdi := 40, rsi := 2, rdx := 0x1000, rsp := 0x0ff8 },
    dmem := initMem (tracerCompiled.bound "tracer") 0x1234 zeros8 }

attribute [local instance] tracerHost in
theorem tracer_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42 ∧
        (st.data.dmem =⋆ Eq (m0.storeInt 0x1000#64 8 (42 : BitVec 64).toInt) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = tracerCompiled.bound "tracer" + 8 ∧
              f = bs.At (0x0ff8#64 - BitVec.ofNat 64 (tracerCompiled.bound "tracer"))) ⋆
          Std.ExtHashMap.emp))
      ⟨tracerState0, Labels.label "tracer"⟩ := by
  have hmem := initMem_entry (tracerCompiled.bound "tracer") 0x1234 zeros8
    (tracerCompiled.bound_le_max "tracer") (by decide)
  have h := tracer_correct 0 tracerCompiled.code_infix_host tracerCompiled.labelsUnique
    40 2 0x1000#64 m0 m0_loadInt tracerState0 0x1234 Std.ExtHashMap.emp rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -, -, hm⟩
  exact ⟨hpc, hrax, hm⟩

abbrev sumtoHost : Host := sumtoCompiled.host
def sumtoState : MachineData :=
  { regs := { rdi := 3, rsp := 0x0ff8 },
    dmem := initMem (sumtoCompiled.bound "sumto") 0x1234 [] }

attribute [local instance] sumtoHost in
theorem sumto_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 6)
      ⟨sumtoState, Labels.label "sumto"⟩ := by
  have hmem := initMem_empty_entry (sumtoCompiled.bound "sumto") 0x1234
    (sumtoCompiled.bound_le_max "sumto")
  have h := sumto_correct 0 sumtoCompiled.code_infix_host sumtoCompiled.labelsUnique
    3 (by decide) sumtoState 0x1234 Std.ExtHashMap.emp rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -⟩
  exact ⟨hpc, by rw [hrax]; decide⟩

abbrev callincHost : Host := callincCompiled.host
def callincState : MachineData :=
  { regs := { rdi := 40, rsi := 1, rsp := 0x0ff8 },
    dmem := initMem (callincCompiled.bound "callinc") 0x1234 [] }

attribute [local instance] callincHost in
theorem callinc_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42)
      ⟨callincState, Labels.label "callinc"⟩ := by
  have hmem := initMem_empty_entry (callincCompiled.bound "callinc") 0x1234
    (callincCompiled.bound_le_max "callinc")
  have h := callinc_correct 0 callincCompiled.code_infix_host callincCompiled.labelsUnique
    40 1 callincState 0x1234 Std.ExtHashMap.emp rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -⟩
  exact ⟨hpc, by rw [hrax]; decide⟩

abbrev twiceHost : Host := twiceCompiled.host
def twiceState (a b : UInt64) : MachineData :=
  { regs := { rdi := a, rsi := b, rsp := 0x0ff8 },
    dmem := initMem (twiceCompiled.bound "twice") 0x1234 [] }

attribute [local instance] twiceHost in
theorem twice_nonvacuous_exit :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = 0)
      ⟨twiceState 20 0, Labels.label "twice"⟩ := by
  have hmem := initMem_empty_entry (twiceCompiled.bound "twice") 0x1234
    (twiceCompiled.bound_le_max "twice")
  have hfail : target.Defined twiceHost "fail" :=
    twiceCompiled.defined_exit_host (by simp)
  have h := twice_correct 0 twiceCompiled.code_infix_host hfail twiceCompiled.labelsUnique
    20 0 (twiceState 20 0) 0x1234 Std.ExtHashMap.emp rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨_, h0, -⟩ | (⟨hna, -⟩ | ⟨_, _, hpc, hrdi, -⟩))
  · exact absurd h0 (by decide)
  · exact absurd (by decide : Truthy 20) hna
  · exact ⟨hpc, hrdi⟩

abbrev spill10Host : Host := spill10Compiled.host
def spill10State : MachineData :=
  { regs := { rdi := 10, rsi := 7, rsp := 0x0ff8 },
    dmem := initMem (spill10Compiled.bound "spill10") 0x1234 [] }

attribute [local instance] spill10Host in
theorem spill10_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = spill10Val 10 7)
      ⟨spill10State, Labels.label "spill10"⟩ := by
  have hmem := initMem_empty_entry (spill10Compiled.bound "spill10") 0x1234
    (spill10Compiled.bound_le_max "spill10")
  have h := spill10_correct 0 spill10Compiled.code_infix_host spill10Compiled.labelsUnique
    10 7 spill10State 0x1234 Std.ExtHashMap.emp rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -⟩
  exact ⟨hpc, hrax⟩

end LeanQbe.Amd64.Litmus
