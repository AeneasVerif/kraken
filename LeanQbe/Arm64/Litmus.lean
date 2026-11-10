module

public import LeanQbe.Arm64.LitmusCode
public import LeanQbe.Arm64.Tracer
import all Kraken.Separation
import all Kraken.Mem

/-!
# Litmus programs on AArch64: end-to-end theorems and non-vacuity

* `sumto_correct` & `sumto_nonvacuous`: the counting loop end to end on Kraken AArch64.
* `callinc_module_fnspec`, `callinc_correct` & `callinc_nonvacuous`: two-function module
  `[inc, callinc]` with a value spilled across a call.
* `twice_module_fnspec`, `twice_correct` & `twice_nonvacuous_exit`: two-function module
  `[check, twice]` with an exit to `"fail"` propagated through a call.
* `spill10_correct` & `spill10_nonvacuous`: `spill10` end to end on Kraken AArch64.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.Litmus

open LeanQbe LeanQbe.Litmus LeanQbe.Arm64.Tracer Rega

/-- Labels of size 0, every other directive of size 4, from `0x1000`. -/
@[instance_reducible] def layoutOf (p : Program) : Layout :=
  { start := 0x1000, size := fun i => match p[i]? with | some (.label _) => 0 | _ => 4 }

theorem layoutOf_zero (p : Program) :
    ∀ i d, p[i]? = some d → @Kraken.Layout.size _ (layoutOf p) i = 0 → ∃ l, d = .label l := by
  intro i d hd hz
  cases d
  case label l => exact ⟨l, rfl⟩
  all_goals
    have hz' : (match p[i]? with | some (.label _) => 0 | _ => 4) = 0 := hz
    rw [hd] at hz'
    simp at hz'

/-! ## A loop end to end: `sumto` on Kraken AArch64 -/

/-- `sumto` on Kraken AArch64: called with `n < 2^32` in `x0`, 16 bytes of stack space below `sp`,
the return address in `x30` and a 16-byte aligned `sp`, it returns to `ra` with `1 + 2 + … + n` in
`x0`, the callee-saved registers and `sp` intact, the 16-byte stack frame returned with arbitrary
contents, and the frame `R` untouched. -/
theorem sumto_correct [Host] (k₀ : Nat) (hc : sumtoCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (n : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n) (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = tri n.toNat ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [n] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hx0]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆ target.Entry (target.get s target.sp) ra 16 ⋆ R := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.emp_sep, Std.ExtHashMap.sep_emp, hE]
    exact hmem
  have h := sumto_fnspec k₀ hc hu (fun _ _ _ _ _ => False) 0 [n] ∅ _ _ (sumto_spec _ n hn ∅) s ra R
    hargs hra hsp hmem'
  have hlab : target.labelAddr _ sumto.name = Host.addrOf k₀ :=
    labelAddr_of_unique (T := target) hu hc.cons.1
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => ?_, ?_, ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'
      exact hm'
  · exact hx.elim

abbrev sumtoHost : Host := .ofLayout sumtoCode (layoutOf sumtoCode) (layoutOf_zero _) (by decide)

def sumtoState : MachineData :=
  { regs := { X0 := 3, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := zeros16.At 0x6ff0#64 }

attribute [local instance] sumtoHost in
theorem sumto_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 6)
      ⟨sumtoState, Host.addrOf 0⟩ := by
  have hmem : sumtoState.dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (sumtoState.regs.SP.toBitVec - 16#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    exact ⟨zeros16, by simp [zeros16], rfl⟩
  have h := sumto_correct 0 (List.prefix_refl _) (Host.labelsUnique_of_nodup (by decide)) 3
    (by decide) sumtoState 0x1234 Std.ExtHashMap.emp rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hx0, -⟩
  exact ⟨hpc, by rw [hx0]; decide⟩

/-! ## Two-function module with a call and a spill across the call: `[inc, callinc]` -/

def callincEnv : Env := fun g => if g = "inc" then incContract else callincContract
def callincBound : String → Nat := fun g => if g = "inc" then 16 else 32

/-- Linking `[inc, callinc]` via `compile_correct`. -/
theorem callinc_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : (incCode ++ callincCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) (nX : Nat) :
    ∀ f ∈ [inc, callinc],
      target.FnSpec hh f.name (callincEnv f.name) (callincBound f.name) nX := by
  refine compile_correct (T := target) hh callincEnv callincBound nX [inc, callinc]
    (incCode ++ callincCode) k₀ callinc_module_compile hc hu ?_
  intro pre f post heq
  rcases pre with _ | ⟨f1, _ | ⟨f2, pre⟩⟩
  · injection heq with hf htl
    subst hf
    refine ⟨inc_wf, inc_spec _, by rw [inc_nslots]; decide, by decide, ?_, ?_⟩
    · rw [inc_callees]; intro _ h; nomatch h
    · rw [inc_exits]; intro _ h; nomatch h
  · injection heq with hf1 htl
    injection htl with hf _
    subst hf1 hf
    refine ⟨callinc_wf, callinc_spec _ rfl, by rw [callinc_nslots]; decide, by decide, ?_, ?_⟩
    · rw [callinc_callees]
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨Or.inl (by simp [inc]), by rw [callinc_nslots]; decide⟩
    · rw [callinc_exits]; intro _ h; nomatch h
  · simp at heq

/-- `callinc` on Kraken AArch64: in every host containing `incCode ++ callincCode` at index `k₀`,
calling `callinc` (at index `k₀ + incCode.length`) with `a, b` in `x0, x1`, 32 bytes of stack space
below `sp`, return address `ra` in `x30`, and 16-byte aligned `sp` returns to `ra` with `a + 1 + b`
in `x0`. -/
theorem callinc_correct [hh : Host] (k₀ : Nat)
    (hc : (incCode ++ callincCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = 32 ∧ f = bs.At (s.regs.SP.toBitVec - 32#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + 1 + b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun f => ∃ bs : List UInt8, bs.length = 32 ∧ f = bs.At (s.regs.SP.toBitVec - 32#64)) ⋆ R))
      ⟨s, Host.addrOf (k₀ + incCode.length)⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, ha, hb]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆ target.Entry (target.get s target.sp) ra 32 ⋆ R := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.emp_sep, Std.ExtHashMap.sep_emp, hE]
    exact hmem
  have hf := callinc_module_fnspec k₀ hc hu 0 callinc (by simp)
    [a, b] ∅ (fun r m' => r = [a + 1 + b] ∧ m' = ∅) (fun _ _ _ => False) ⟨a, b, rfl, rfl, rfl⟩
    s ra R hargs hra hsp hmem'
  have hlab : target.labelAddr hh callinc.name = Host.addrOf (k₀ + incCode.length) :=
    labelAddr_of_unique (T := target) hu hc.append.2.cons.1
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => ?_, ?_, ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'
      exact hm'
  · exact hx.elim

abbrev callincHost : Host :=
  .ofLayout (incCode ++ callincCode) (layoutOf (incCode ++ callincCode)) (layoutOf_zero _) (by decide)

def callincState : MachineData :=
  { regs := { X0 := 40, X1 := 1, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := zeros32.At 0x6fe0#64 }

attribute [local instance] callincHost in
theorem callinc_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 42)
      ⟨callincState, Host.addrOf incCode.length⟩ := by
  have hmem : callincState.dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = 32 ∧ f = bs.At (callincState.regs.SP.toBitVec - 32#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    exact ⟨zeros32, by simp [zeros32], rfl⟩
  have h := callinc_correct 0 (List.prefix_refl _) (Host.labelsUnique_of_nodup (by decide)) 40 1
    callincState 0x1234 Std.ExtHashMap.emp rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hx0, -⟩
  exact ⟨hpc, by rw [hx0]; decide⟩

/-! ## Exit propagation through a call: `[check, twice]` -/

def twiceEnv : Env := fun g => if g = "check" then checkContract else twiceContract
def twiceBound : String → Nat := fun g => if g = "check" then 16 else 48

/-- Linking `[check, twice]` via `compile_correct` in any host that also defines `"fail"`. -/
theorem twice_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : (checkCode ++ twiceCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "fail") :
    ∀ f ∈ [check, twice],
      target.FnSpec hh f.name (twiceEnv f.name) (twiceBound f.name) 16 := by
  refine compile_correct (T := target) hh twiceEnv twiceBound 16 [check, twice]
    (checkCode ++ twiceCode) k₀ twice_module_compile hc hu ?_
  intro pre f post heq
  rcases pre with _ | ⟨f1, _ | ⟨f2, pre⟩⟩
  · injection heq with hf htl
    subst hf
    refine ⟨check_wf, check_spec _, by rw [check_nslots]; decide, by decide, ?_, ?_⟩
    · rw [check_callees]; intro _ h; nomatch h
    · rw [check_exits]
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨hfail, by decide⟩
  · injection heq with hf1 htl
    injection htl with hf _
    subst hf1 hf
    refine ⟨twice_wf, twice_spec _ rfl, by rw [twice_nslots]; decide, by decide, ?_, ?_⟩
    · rw [twice_callees]
      intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨Or.inl (by simp [check]), by rw [twice_nslots]; decide⟩
      · exact ⟨Or.inl (by simp [check]), by rw [twice_nslots]; decide⟩
      · nomatch hg
    · rw [twice_exits]; intro _ h; nomatch h
  · simp at heq

/-- `twice` on Kraken AArch64: returns `a + b` to `ra` when both have non-zero low 32 bits, or
exits to `"fail"` in a call-ready state with the failing argument in `x0`. -/
theorem twice_correct [hh : Host] (k₀ k_fail : Nat)
    (hc : (checkCode ++ twiceCode).IsInfixAt Host.prog k₀)
    (hfail : Host.prog[k_fail]? = some (.label "fail")) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At (s.regs.SP.toBitVec - 48#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (Truthy a ∧ Truthy b ∧ st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + b ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP) ∨
        ((¬Truthy a ∧ st.pc = Host.addrOf k_fail ∧ (st.data.regs.getXReg .X0).toBitVec = a ∧
          st.data.regs.SP.toNat % 16 = 0) ∨
         (Truthy a ∧ ¬Truthy b ∧ st.pc = Host.addrOf k_fail ∧ (st.data.regs.getXReg .X0).toBitVec = b ∧
          st.data.regs.SP.toNat % 16 = 0)))
      ⟨s, Host.addrOf (k₀ + checkCode.length)⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, ha, hb]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆ target.Entry (target.get s target.sp) ra 48 ⋆ R := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.emp_sep, Std.ExtHashMap.sep_emp, hE]
    exact hmem
  let Q : LeanQbe.Post := fun r m' => Truthy a ∧ Truthy b ∧ r = [a + b] ∧ m' = ∅
  let X : XPost := fun g xs m' =>
    g = "fail" ∧ m' = ∅ ∧ ((¬Truthy a ∧ xs = [a]) ∨ (Truthy a ∧ ¬Truthy b ∧ xs = [b]))
  have hspec : twiceContract [a, b] ∅ Q X :=
    ⟨a, b, rfl, fun hta htb => ⟨hta, htb, rfl, rfl⟩,
      fun hna => ⟨rfl, rfl, Or.inl ⟨hna, rfl⟩⟩,
      fun hta hnb => ⟨rfl, rfl, Or.inr ⟨hta, hnb, rfl⟩⟩⟩
  have hf := twice_module_fnspec k₀ hc hu ⟨k_fail, hfail⟩ twice (by simp)
    [a, b] ∅ Q X hspec s ra R hargs hra hsp hmem'
  have hlab : target.labelAddr hh twice.name = Host.addrOf (k₀ + checkCode.length) :=
    labelAddr_of_unique (T := target) hu hc.append.2.cons.1
  have hflab : target.labelAddr hh "fail" = Host.addrOf k_fail :=
    labelAddr_of_unique (T := target) hu hfail
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨hta, htb, rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, _⟩ |
    ⟨sym', as', m', ⟨rfl, rfl, hcase⟩, _, hpc, has', hspE, _⟩)
  · refine Or.inl ⟨hta, htb, hpc, ?_, fun r hr => ?_, ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
  · rw [hflab] at hpc
    rcases hcase with ⟨hna, rfl⟩ | ⟨hta, hnb, rfl⟩
    · refine Or.inr (Or.inl ⟨hna, hpc, ?_, hspE⟩)
      simpa [Target.ArgsIn, Target.ValsIn, argRegs, get_reg] using has'
    · refine Or.inr (Or.inr ⟨hta, hnb, hpc, ?_, hspE⟩)
      simpa [Target.ArgsIn, Target.ValsIn, argRegs, get_reg] using has'

def twiceProg : Program := checkCode ++ twiceCode ++ [.label "fail"]

abbrev twiceHost : Host :=
  .ofLayout twiceProg (layoutOf twiceProg) (layoutOf_zero _) (by decide)

def twiceState (a b : UInt64) : MachineData :=
  { regs := { X0 := a, X1 := b, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := zeros48.At 0x6fd0#64 }

attribute [local instance] twiceHost in
theorem twice_nonvacuous_exit :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (checkCode.length + twiceCode.length) ∧
        (st.data.regs.getXReg .X0).toBitVec = 0)
      ⟨twiceState 20 0, Host.addrOf checkCode.length⟩ := by
  have hmem : (twiceState 20 0).dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = 48 ∧ f = bs.At ((twiceState 20 0).regs.SP.toBitVec - 48#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    exact ⟨zeros48, by simp [zeros48], rfl⟩
  have hc : (checkCode ++ twiceCode).IsInfixAt Host.prog 0 := ⟨[.label "fail"], rfl⟩
  have hfail : Host.prog[checkCode.length + twiceCode.length]? = some (.label "fail") := by decide
  have h := twice_correct 0 (checkCode.length + twiceCode.length) hc hfail
    (Host.labelsUnique_of_nodup (by decide)) 20 0 (twiceState 20 0) 0x1234
    Std.ExtHashMap.emp rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨_, h0, -⟩ | (⟨hna, -⟩ | ⟨_, _, hpc, hx0, -⟩))
  · exact absurd h0 (by decide)
  · exact absurd (by decide : Truthy 20) hna
  · exact ⟨hpc, hx0⟩

/-! ## `spill10` on Kraken AArch64 -/

theorem spill10_correct [Host] (k₀ : Nat) (hc : spill10Code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b : BitVec 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = spill10Val a b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, ha, hb]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆ target.Entry (target.get s target.sp) ra 16 ⋆ R := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.emp_sep, Std.ExtHashMap.sep_emp, hE]
    exact hmem
  have h := spill10_fnspec k₀ hc hu (fun _ _ _ _ _ => False) 0
    [a, b] ∅ _ _ (spill10_spec _ a b ∅) s ra R hargs hra hsp hmem'
  have hlab : target.labelAddr _ spill10.name = Host.addrOf k₀ :=
    labelAddr_of_unique (T := target) hu hc.cons.1
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => ?_, ?_, ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'
      exact hm'
  · exact hx.elim

abbrev spill10Host : Host :=
  .ofLayout spill10Code (layoutOf spill10Code) (layoutOf_zero _) (of_decide_eq_true (by kernel_rfl))

def spill10State : MachineData :=
  { regs := { X0 := 10, X1 := 7, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := zeros16.At 0x6ff0#64 }

attribute [local instance] spill10Host in
theorem spill10_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = spill10Val 10 7)
      ⟨spill10State, Host.addrOf 0⟩ := by
  have hmem : spill10State.dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (spill10State.regs.SP.toBitVec - 16#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    exact ⟨zeros16, by simp [zeros16], rfl⟩
  have h := spill10_correct 0 (List.prefix_refl _) (Host.labelsUnique_of_nodup (by decide)) 10 7
    spill10State 0x1234 Std.ExtHashMap.emp rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hx0, -⟩
  exact ⟨hpc, hx0⟩

end LeanQbe.Arm64.Litmus
