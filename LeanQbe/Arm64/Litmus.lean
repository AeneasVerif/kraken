module

public import LeanQbe.Arm64.LitmusCode
import all Kraken.Separation

/-!
# Litmus programs on AArch64: `sumto` end to end

`sumto_correct`: the whole pipeline (mid-end, allocation oracle, lowering) on the counting loop,
stated with Kraken AArch64 notions only, in every host that contains the compiled code with unique
labels; `sumto_nonvacuous` instantiates it on a concrete host and state.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.Litmus

open LeanQbe LeanQbe.Litmus Rega

/-- `sumto` on Kraken AArch64: called with `n < 2^32` in `x0`, the return address in `x30` and a
16-byte aligned `sp`, it returns to `ra` with `1 + 2 + … + n` in `x0`, the callee-saved registers
and `sp` intact, and memory untouched. -/
theorem sumto_correct [Host] (k₀ : Nat) (hc : sumtoCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (n : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n) (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0) (hmem : s.dmem =⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = tri n.toNat ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧ (st.data.dmem =⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : target.ArgsIn [n] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hx0]
  have hmem' : target.mem s =⋆ Eq ∅ ⋆ target.Entry (target.get s target.sp) ra 0 ⋆ R := by
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
    · simpa [Target.Exit, region_zero, Std.ExtHashMap.emp_sep, Std.ExtHashMap.sep_emp, hE] using hm'
  · exact hx.elim

/-! ## Non-vacuity of `sumto_correct`: a concrete host and state -/

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

abbrev sumtoHost : Host := .ofLayout sumtoCode (layoutOf sumtoCode) (layoutOf_zero _) (by decide)

def sumtoState : MachineData :=
  { regs := { X0 := 3, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 } }

attribute [local instance] sumtoHost in
theorem sumto_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 6)
      ⟨sumtoState, Host.addrOf 0⟩ := by
  have h := sumto_correct 0 (List.prefix_refl _) (Host.labelsUnique_of_nodup (by decide)) 3
    (by decide) sumtoState 0x1234 Std.ExtHashMap.emp rfl rfl (by decide) rfl
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hx0, -⟩
  exact ⟨hpc, by rw [hx0]; decide⟩

end LeanQbe.Arm64.Litmus
