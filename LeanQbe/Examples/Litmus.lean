module

public import LeanQbe.RegaLemmas
public import LeanQbe.Amd64.TargLemmas
public import Kraken.X64.PrintATT
public import Kraken.X64.Parser
import all Kraken.Separation
import all Kraken.Mem

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

open LeanQbe Rega Amd64

/-- The tracer function (plan step 1): `x = add a b; storel x, p; ret x`. -/
def tracer : Fn where
  name := "tracer"
  body := fun _ _ =>
    .param fun a => .param fun b => .param fun p =>
    .let_ (.bin .l .add (.var a) (.var b)) fun x =>
    .store .l (.var x) (.var p) (.ret [.var x])

/-- Trivial hints: `x` (name 3) goes to `rax`. -/
def tracerHints : Hints Amd64.isa where
  dest n := if n = 3 then some .rax else none
  entry _ := ⟨[], []⟩

/-- What `lower` must produce, written as assembly and parsed by Kraken's parser. -/
def tracerCode : Program := parse("tracer:
  movq %rdi, %r11
  movq %rsi, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq %rax, %r11
  movq %r11, (%rdx)
  ret")

theorem tracer_lower : lowerFn tracerHints tracer = .ok tracerCode := by rfl

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

theorem host_unique : Amd64.target.LabelsUnique host :=
  letI := host; Host.labelsUnique_of_nodup (by decide)

theorem tracer_wf : Func.Wf tracer.body := by
  unfold tracer; wf_tac

/-- The generic theorem, instantiated: the compiled tracer meets its `wp` as a `FnSpec`. -/
theorem tracer_fnspec (mf : MemFacts Amd64.target) (Γ : Env) :
    Amd64.target.FnSpec host "tracer" (Func.spec Γ tracer.body) 0 :=
  lowerFn_correct host tracerHints tracer Γ 0 tracerCode 0 tracer_lower
    (show List.IsInfixAt tracerCode (Amd64.target.prog host) 0 from List.prefix_refl _) host_unique tracer_wf (by decide) mf

theorem region_zero (a : BitVec 64) : region a 0 = Std.ExtHashMap.emp := by
  funext f
  apply propext
  constructor
  · rintro ⟨bs, hl, rfl⟩
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simp [Std.ExtHashMap.emp, List.At]
  · intro hf
    refine ⟨[], rfl, ?_⟩
    simp only [Std.ExtHashMap.emp] at hf
    simp [hf, List.At]

attribute [local instance] host

/-- The tracer on Kraken x64 (decision D11): only Kraken notions in the statement. Called with
`a b p` in `rdi rsi rdx`, a mapped 8-byte cell at `p` in `m`, the return address at `rsp`, it returns to
`ra` with `a + b` in `rax`, the callee-saved registers intact, `rsp` popped, and `a + b` stored at `p`. -/
theorem tracer_correct (mf : MemFacts Amd64.target) (a b p : BitVec 64) (m : Mem 64)
    (hp : ∃ i, m.loadInt p 8 = some i)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b) (hpp : s.regs.get64 .rdx = p)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆ Eq (ra.toUInt64.At (s.regs.get64 .rsp)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ Eq (m.storeInt p 8 (a + b).toInt) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (s.regs.get64 .rsp)) ⋆ R))
      ⟨s, Host.addrOf 0⟩ := by
  let Q : LeanQbe.Post := fun rets m' => rets = [a + b] ∧ m' = storeMem m .l p (a + b)
  let X : XPost := fun _ _ _ => False
  have hwp : Func.spec (fun _ _ _ _ _ => False) tracer.body [a, b, p] m Q X := by
    simp [Func.spec, tracer, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, storeOk, Sz.bytes, hp, Q]
  have hargs : Amd64.target.ArgsIn [a, b, p] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, ha, hb, hpp]
  have hmem' : Amd64.target.mem s =⋆ Eq m ⋆
      Amd64.target.Entry (Amd64.target.get s Amd64.target.sp) ra 0 ⋆ R := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.emp_sep]
    exact hmem
  have h := tracer_fnspec mf _ [a, b, p] m Q X hwp s ra R hargs trivial hsp hmem'
  have hlab : Amd64.target.labelAddr host "tracer" = Host.addrOf 0 :=
    labelAddr_of_unique host_unique (j := 0) rfl
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, Amd64.target, Amd64.isa] using hrets
    · have hE : Amd64.target.Exit (Amd64.target.get s Amd64.target.sp) 0 =
          fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (s.regs.get64 .rsp) := by
        funext f; simp [Target.Exit, region, Amd64.target, Amd64.isa]
      rw [hE] at hm'
      exact hm'
  · exact hx.elim

end LeanQbe.Litmus
