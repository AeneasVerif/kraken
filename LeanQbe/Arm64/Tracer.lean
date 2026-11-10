module

public import LeanQbe.RegaLemmas
public import LeanQbe.Arm64.Abi
public import Kraken.AArch64.Parser
public import Kraken.AArch64.Print
import all Kraken.Separation
import all Kraken.Mem

/-!
# The tracer function on AArch64 (plan step 2d)

The step-1 function `x = add a b; storel x, p; ret x` through the same generic lowering and the same
theorem (`Rega.lowerFn_correct`) as on x64, instantiated with `Arm64.target`. The final statement,
`tracer_correct`, mentions only Kraken AArch64 notions.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.Tracer

open LeanQbe Rega

/-- The tracer function (plan step 1): `x = add a b; storel x, p; ret x`. -/
def tracer : Fn where
  name := "tracer"
  body := fun _ _ =>
    .param fun a => .param fun b => .param fun p =>
    .let_ (.bin .l .add (.var a) (.var b)) fun x =>
    .store .l (.var x) (.var p) (.ret [.var x])

/-- Trivial hints: `x` (name 3) goes to `x0`. -/
def tracerHints : Hints isa where
  dest n := if n = 3 then some (.reg .X0) else none
  entry _ := ⟨[], []⟩

open Kraken.AArch64.Parser in
/-- What `lower` must produce, written as assembly and parsed by Kraken's parser. -/
def tracerCode : Program := parseAArch64("tracer:
  add x0, x0, x1
  str x0, [x2]
  ret")

theorem tracer_lower : lowerFn tracerHints tracer = .ok tracerCode := by rfl

/-- The assembly text of the compiled tracer. -/
def tracerAsm : String :=
  String.intercalate "\n" (tracerCode.map Kraken.AArch64.Print.directive)

/-! ## A concrete host: the tracer alone, labels of size 0, instructions of size 4 -/

@[instance_reducible] def layout : Layout := { start := 0x1000, size := fun i => if i = 0 then 0 else 4 }

abbrev host : Host :=
  .ofLayout tracerCode layout
    (fun i d hd hz => by
      have hz' : (if i = 0 then 0 else 4) = 0 := hz
      have hi : i = 0 := by
        by_cases h : i = 0
        · exact h
        · simp [h] at hz'
      subst hi
      simp only [tracerCode, List.getElem?_cons_zero, Option.some.injEq] at hd
      exact ⟨"tracer", hd.symm⟩)
    (by decide)

theorem host_unique : target.LabelsUnique host :=
  letI := host; Host.labelsUnique_of_nodup (by decide)

theorem tracer_wf : Func.Wf tracer.body := by
  unfold tracer; wf_tac

/-- The generic theorem, instantiated: the compiled tracer meets its `wp` as a `FnSpec`. -/
theorem tracer_fnspec (Γ : Env) :
    target.FnSpec host "tracer" (Func.spec Γ tracer.body) 0 0 :=
  lowerFn_correct (T := target) host tracerHints tracer Γ 0 tracerCode 0 tracer_lower
    (show List.IsInfixAt tracerCode (target.prog host) 0 from List.prefix_refl _) host_unique
    tracer_wf (by decide) 0

attribute [local instance] host

/-- The tracer on Kraken AArch64: only Kraken notions in the statement. Called with `a b p` in
`x0 x1 x2`, a mapped 8-byte cell at `p` in `m`, the return address in `x30` and a 16-byte aligned
`sp`, it returns to `ra` with `a + b` in `x0`, the callee-saved registers and `sp` intact, and
`a + b` stored at `p`. -/
theorem tracer_correct (a b p : BitVec 64) (m : Mem 64)
    (hp : ∃ i, m.loadInt p 8 = some i)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hpp : (s.regs.getXReg .X2).toBitVec = p)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ Eq (m.storeInt p 8 (a + b).toInt) ⋆ R))
      ⟨s, Host.addrOf 0⟩ := by
  let Q : LeanQbe.Post := fun rets m' => rets = [a + b] ∧ m' = storeMem m .l p (a + b)
  let X : XPost := fun _ _ _ => False
  have hwp : Func.spec (fun _ _ _ _ _ => False) tracer.body [a, b, p] m Q X := by
    simp [Func.spec, tracer, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, storeOk, Sz.bytes, hp, Q]
  have hargs : target.ArgsIn [a, b, p] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, ha, hb, hpp]
  have hmem' : target.mem s =⋆ Eq m ⋆ target.Entry (target.get s target.sp) ra 0 ⋆ R := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
    exact hmem
  have h := tracer_fnspec (fun _ _ _ _ _ => False) [a, b, p] m Q X hwp s ra R hargs hra hsp hmem'
  have hlab : target.labelAddr host "tracer" = Host.addrOf 0 :=
    labelAddr_of_unique host_unique (j := 0) rfl
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => ?_, ?_, ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
    · simpa [Target.Exit, region_zero, Std.ExtHashMap.emp_sep, Std.ExtHashMap.sep_emp, storeMem]
        using hm'
  · exact hx.elim

end LeanQbe.Arm64.Tracer
