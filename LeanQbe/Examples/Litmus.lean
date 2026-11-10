module

public import LeanQbe.RegaLemmas
public import LeanQbe.Examples.LitmusProgsLemmas
public import LeanQbe.Amd64.TargLemmas
public import Kraken.X64.PrintATT
public import Kraken.X64.Parser
import all Kraken.Separation
import all Kraken.Mem

set_option autoImplicit false

@[expose] public section

open Lean Elab Tactic Meta in
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := tgt.eq?
    | throwError "kernel_rfl: goal is not an equality{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

namespace LeanQbe.Litmus

open LeanQbe Rega Amd64

/-- Trivial hints: `x` (name 3) goes to `rax`, no pre-moves, 0 spill slots. -/
def tracerHints : Hints Amd64.isa where
  dest n := if n = 3 then some .rax else none
  entry _ := ⟨[], []⟩
  pre _ := []
  nslots := 0

/-- What `lower` must produce, written as assembly and parsed by Kraken's parser. -/
def tracerCode : Program := parse("tracer:
  subq $8, %rsp
  movq %rdi, %r11
  movq %rsi, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq %rax, %r11
  movq %r11, (%rdx)
  addq $8, %rsp
  ret")

theorem tracer_lower : lowerFn tracerHints ⟨[], []⟩ tracer = .ok tracerCode := by rfl

/-! ## The tracer in any host that contains it (generic in the layout, decision D2) -/

section Generic
variable [hh : Host]

/-- The generic theorem, instantiated: the compiled tracer meets its `wp` as a `FnSpec`. -/
theorem tracer_fnspec (k₀ : Nat) (hc : tracerCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (Γ : Env) (nX : Nat) : Amd64.target.FnSpec hh "tracer" (Func.spec Γ tracer.body) 8 nX :=
  lowerFn_correct (T := Amd64.target) hh tracerHints ⟨[], []⟩ tracer Γ (fun _ => 0) 8 nX
    tracerCode k₀ tracer_lower hc hu tracer_wf (by decide) (by decide)
    (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- The tracer on Kraken x64 (decision D11): only Kraken notions in the statement. In every host
that contains `tracerCode` at index `k₀` and defines no label twice: called with `a b p` in
`rdi rsi rdx`, a mapped 8-byte cell at `p` in `m`, 8 bytes of stack space below `rsp` and the return
address at `rsp`, it returns to `ra` with `a + b` in `rax`, the callee-saved registers intact, `rsp`
popped, and `a + b` stored at `p`; the 16 bytes of stack and return-address slot are handed back
with arbitrary contents, and the frame `R` is untouched. -/
theorem tracer_correct (k₀ : Nat) (hc : tracerCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b p : BitVec 64) (m : Mem 64)
    (hp : ∃ i, m.loadInt p 8 = some i)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b) (hpp : s.regs.get64 .rdx = p)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (s.regs.get64 .rsp - 8#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ Eq (m.storeInt p 8 (a + b).toInt) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.get64 .rsp - 8#64)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  let Q : LeanQbe.Post := fun rets m' => rets = [a + b] ∧ m' = storeMem m .l p (a + b)
  let X : XPost := fun _ _ _ => False
  have hwp : Func.spec (fun _ _ _ _ _ => False) tracer.body [a, b, p] m Q X := by
    simp [Func.spec, tracer, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, storeOk, Sz.bytes, hp, Q]
  have hargs : Amd64.target.ArgsIn [a, b, p] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, ha, hb, hpp]
  have h := tracer_fnspec k₀ hc hu _ 0 [a, b, p] m Q X hwp s ra R hargs trivial hsp hmem
  have hlab : Amd64.target.labelAddr hh "tracer" = Host.addrOf k₀ :=
    labelAddr_of_unique (T := Amd64.target) hu hc.cons.1
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', hm'⟩
    simpa [Target.RetsIn, Target.ValsIn, Amd64.target, Amd64.isa] using hrets
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

/-- An 8-byte frame at `0x7000`, the return address at `rsp = 0x7008`, and `p = 0x7010`. -/
def raBytes0 : List UInt8 := (0x1234 : Int64).toUInt64.toBytes
def zeros8 : List UInt8 := List.replicate 8 0
def zeros24 : List UInt8 := List.replicate 24 0
def zeros40 : List UInt8 := List.replicate 40 0
def zeros56 : List UInt8 := List.replicate 56 0

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
def m0 : Mem 64 := zeros8.At 0x7010#64
def s0 : MachineData :=
  { regs := { rdi := 40, rsi := 2, rdx := 0x7010, rsp := 0x7008 },
    dmem := ((zeros8 ++ raBytes0) ++ zeros8).At 0x7000#64 }

theorem tracer_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42 ∧
        (st.data.dmem =⋆ Eq (m0.storeInt 0x7010#64 8 (42 : BitVec 64).toInt) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At 0x7000#64) ⋆ Std.ExtHashMap.emp))
      ⟨s0, Host.addrOf 0⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have hp : ∃ i, m0.loadInt 0x7010#64 8 = some i :=
    ⟨_, Mem.loadInt_sep zeros8 _ 8 Std.ExtHashMap.emp m0 (by rw [Std.ExtHashMap.sep_emp]; rfl)
      (by simp [zeros8]) (by decide)⟩
  have hmem : s0.dmem =⋆ Eq m0 ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (s0.regs.get64 .rsp - 8#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (s0.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep (zeros8 ++ raBytes0) zeros8 0x7000#64 (by simp [hlen, zeros8])
    have e1 : (0x7000#64 + BitVec.ofNat 64 (zeros8 ++ raBytes0).length) = 0x7010#64 := by
      simp [zeros8, hlen]
    rw [e1] at h1
    have h2 := Mem.At_append_sep zeros8 raBytes0 0x7000#64 (by simp [hlen, zeros8])
    have e2 : (0x7000#64 + BitVec.ofNat 64 zeros8.length) = 0x7008#64 := by simp [zeros8]
    rw [e2] at h2
    have h0 : (Eq (((zeros8 ++ raBytes0) ++ zeros8).At 0x7000#64)) s0.dmem := rfl
    rw [h1] at h0
    refine sep_mono (fun f hf => ?_) h0
    rw [h2] at hf
    exact sep_mono (fun f1 hf1 => ⟨zeros8, by simp [zeros8], hf1.symm⟩) hf
  have h := tracer_correct 0 host_contains host_unique 40 2 0x7010#64 m0 hp s0 0x1234
    Std.ExtHashMap.emp rfl rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -, -, hm⟩
  exact ⟨hpc, hrax, hm⟩

end LeanQbe.Litmus
