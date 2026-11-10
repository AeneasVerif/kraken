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

/-- Trivial hints: `x` (name 3) goes to `x0`, no pre-moves, 0 spill slots. -/
def tracerHints : Hints isa where
  dest n := if n = 3 then some (.reg .X0) else none
  entry _ := ⟨[], []⟩
  pre _ := []
  nslots := 0

open Kraken.AArch64.Parser in
/-- What `lower` must produce, written as assembly and parsed by Kraken's parser. -/
def tracerCode : Program := parseAArch64("tracer:
  sub sp, sp, #16
  str x30, [sp]
  add x0, x0, x1
  str x0, [x2]
  ldr x30, [sp]
  add sp, sp, #16
  ret")

theorem tracer_lower : lowerFn tracerHints ⟨[], []⟩ tracer = .ok tracerCode := by rfl

/-- The assembly text of the compiled tracer. -/
def tracerAsm : String :=
  String.intercalate "\n" (tracerCode.map Kraken.AArch64.Print.directive)

theorem tracer_wf : Func.Wf tracer.body := by
  unfold tracer; wf_tac

section Generic
variable [hh : Host]

/-- The generic theorem, instantiated: the compiled tracer meets its `wp` as a `FnSpec`. -/
theorem tracer_fnspec (k₀ : Nat) (hc : tracerCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (Γ : Env) (nX : Nat) : target.FnSpec hh "tracer" (Func.spec Γ tracer.body) 16 nX :=
  lowerFn_correct (T := target) hh tracerHints ⟨[], []⟩ tracer Γ (fun _ => 0) 16 nX
    tracerCode k₀ tracer_lower hc hu tracer_wf (by decide) (by decide)
    (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- The tracer on Kraken AArch64: only Kraken notions in the statement. In every host that contains
`tracerCode` at index `k₀` and defines no label twice: called with `a b p` in `x0 x1 x2`, a mapped
8-byte cell at `p` in `m`, 16 bytes of stack space below `sp`, the return address in `x30` and a
16-byte aligned `sp`, it returns to `ra` with `a + b` in `x0`, the callee-saved registers and `sp`
intact, `a + b` stored at `p`, the 16-byte stack frame returned with arbitrary contents, and the
frame `R` untouched. -/
theorem tracer_correct (k₀ : Nat) (hc : tracerCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b p : BitVec 64) (m : Mem 64)
    (hp : ∃ i, m.loadInt p 8 = some i)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hpp : (s.regs.getXReg .X2).toBitVec = p)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ Eq (m.storeInt p 8 (a + b).toInt) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.SP.toBitVec - 16#64)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  let Q : LeanQbe.Post := fun rets m' => rets = [a + b] ∧ m' = storeMem m .l p (a + b)
  let X : XPost := fun _ _ _ => False
  have hwp : Func.spec (fun _ _ _ _ _ => False) tracer.body [a, b, p] m Q X := by
    simp [Func.spec, tracer, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, storeOk, Sz.bytes, hp, Q]
  have hargs : target.ArgsIn [a, b, p] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, ha, hb, hpp]
  have hmem' : target.mem s =⋆ Eq m ⋆ target.Entry (target.get s target.sp) ra 16 ⋆ R := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
    exact hmem
  have h := tracer_fnspec k₀ hc hu (fun _ _ _ _ _ => False) 0 [a, b, p] m Q X hwp s ra R hargs hra
    hsp hmem'
  have hlab : target.labelAddr hh "tracer" = Host.addrOf k₀ :=
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
    · exact hm'
  · exact hx.elim

end Generic

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

attribute [local instance] host

theorem host_unique : Host.LabelsUnique := Host.labelsUnique_of_nodup (by decide)

theorem host_contains : tracerCode.IsInfixAt Host.prog 0 := List.prefix_refl _

/-! ## Non-vacuity: a concrete state meeting every premise of `tracer_correct` -/

/-- A 16-byte stack frame at `0x6ff0` (`sp = 0x7000`), and 8 zero bytes at `p = 0x7000`; return
address `0x1234` in `x30`. -/
def zeros8 : List UInt8 := List.replicate 8 0
def zeros16 : List UInt8 := List.replicate 16 0
def zeros32 : List UInt8 := List.replicate 32 0
def zeros48 : List UInt8 := List.replicate 48 0
def m0 : Mem 64 := zeros8.At 0x7000#64
def s0 : MachineData :=
  { regs := { X0 := 40, X1 := 2, X2 := 0x7000, X30 := (0x1234 : Int64).toUInt64, SP := 0x7000 },
    dmem := (zeros16 ++ zeros8).At 0x6ff0#64 }

theorem tracer_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 42 ∧
        (st.data.dmem =⋆ Eq (m0.storeInt 0x7000#64 8 (42 : BitVec 64).toInt) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At 0x6ff0#64) ⋆
          Std.ExtHashMap.emp))
      ⟨s0, Host.addrOf 0⟩ := by
  have hp : ∃ i, m0.loadInt 0x7000#64 8 = some i :=
    ⟨_, Mem.loadInt_sep zeros8 _ 8 Std.ExtHashMap.emp m0 (by rw [Std.ExtHashMap.sep_emp]; rfl)
      (by simp [zeros8]) (by decide)⟩
  have hmem : s0.dmem =⋆ Eq m0 ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s0.regs.SP.toBitVec - 16#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep zeros16 zeros8 0x6ff0#64 (by simp [zeros16, zeros8])
    have e1 : (0x6ff0#64 + BitVec.ofNat 64 zeros16.length) = 0x7000#64 := by simp [zeros16]
    rw [e1] at h1
    have h0 : (Eq ((zeros16 ++ zeros8).At 0x6ff0#64)) s0.dmem := rfl
    rw [h1] at h0
    exact sep_mono (fun f1 hf1 => ⟨zeros16, by simp [zeros16], hf1.symm⟩) h0
  have h := tracer_correct 0 host_contains host_unique 40 2 0x7000#64 m0 hp s0 0x1234
    Std.ExtHashMap.emp rfl rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hx0, -, -, hm⟩
  exact ⟨hpc, hx0, hm⟩

end LeanQbe.Arm64.Tracer
