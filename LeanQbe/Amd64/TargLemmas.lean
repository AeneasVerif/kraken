module

public import LeanQbe.Amd64.Targ
public import Kraken.X64.WP
public import Kraken.X64.Sep
public import Kraken.X64.Regs
public import LeanQbe.AbiLemmas
import Kraken.X64.Parser

/-!
# x64 snippet lemmas and the `Target` instance

One step lemma per directive and per snippet of `Targ.lean`, generic in the `Host` and the
position, in continuation form, then `Amd64.target : Target`.

Generic control-flow lemmas come from Kraken (`Kraken/X64/WP/`, `Kraken/X64/Regs.lean`).
-/

@[expose] public section

namespace LeanQbe.Amd64

/-! ## Encodings are the parser's -/

section ParserChecks
open Kraken.X64.Parser
example : parse("mov %rsi, %rax") = mov .rax .rsi := rfl
example : parse("mov $5, %rax") = movi .rax 5 := rfl
example : parse("movq %rdi, (%rdx)") = [storelD .rdi .rdx] := rfl
example : parse("mov (%rdx), %rax") = [ins (.mov (.reg (q .rax)) (.mem (atReg .rdx)))] := rfl
example : parse("add %r10, %r11") = [(binIns .l .add).get rfl] := rfl
example : parse("subl %r10d, %r11d") = [(binIns .w .sub).get rfl] := rfl
example : parse("movl %esi, %eax") = [movlD .rax .rsi] := rfl
example : parse("test %eax, %eax
jnz L") = jnz .rax "L" := rfl
example : parse("jmp L") = jmp "L" := rfl
example : parse("ret") = ret := rfl
end ParserChecks

/-! ## Register file and addresses -/

theorem get_q (regs : Reg64s) (r : Reg64) : regs.get (q r) = regs.get64 r := Reg64s.get_low64 ..

theorem set_q (regs : Reg64s) (r : Reg64) (v : BitVec 64) : regs.set (q r) v = regs.set64 r v :=
  rfl

/-- `[r]` evaluates to the contents of `r` (64-bit addressing). -/
theorem atReg_interp [Labels] (regs : Reg64s) (r : Reg64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ (atReg r) regs p).zeroExtend 64 = regs.get64 r := by
  simp [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, ConstExpr.interp, BitVec.signed]

/-- The value of an operand read from a register file. -/
abbrev argv (regs : Reg64s) (a : Arg Reg64) : Val := (a.map regs.get64).val

theorem argv_congr {regs regs' : Reg64s} {a : Arg Reg64}
    (h : ∀ r, r ∈ a.vars → regs'.get64 r = regs.get64 r) : argv regs' a = argv regs a := by
  cases a with
  | var r => exact h r (by simp [Arg.vars])
  | imm c => rfl

/-- `Op.eval` of a binary operation only depends on the values of its operands. -/
theorem eval_bin_imm (k : Cls) (o : BinOp) (x y : Arg Val) :
    (Op.bin k o x y).eval = (Op.bin k o (.imm x.val) (.imm y.val)).eval := by
  cases k <;> rfl

/-! ## One directive -/

section
variable [Host]

abbrev Run (k : Nat) (s : MachineData) (post : (MachineState → Prop)) : Prop :=
  Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩

theorem eventually_movD {i : Nat} {rd rs : Reg64} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (movD rd rs))
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 rd (s.regs.get64 rs) → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [movD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, set_q, get_q]
  exact hk _ rfl rfl

theorem eventually_moviD {i : Nat} {rd : Reg64} {c : BitVec 64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (moviD rd c))
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 rd c → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [moviD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    ConstExpr.interp, MachineData.set, MachineData.setReg, Effects.All, set_q]
  exact hk _ (by simp) rfl

theorem eventually_argTo {i : Nat} {t : Reg64} {a : Arg Reg64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (argTo t a))
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 t (argv s.regs a) → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  cases a with
  | var r => exact eventually_movD hi hk
  | imm c => exact eventually_moviD hi hk

theorem eventually_movlD {i : Nat} {rd rs : Reg64} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (movlD rd rs))
    (hk : ∀ s' : MachineData,
      s'.regs = s.regs.set64 rd (Cls.w.trunc (s.regs.get64 rs)) → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [movlD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, Reg64s.set_low32,
    Reg64s.get_low32]
  exact hk _ rfl rfl

theorem eventually_binIns {i : Nat} {k : Cls} {o : BinOp} {di : Directive} {v : Val}
    {s : MachineData} {post : (MachineState → Prop)}
    (hb : binIns k o = some di) (hi : Host.prog[i]? = some di)
    (hv : (Op.bin k o (.imm (s.regs.get64 .r11)) (.imm (s.regs.get64 .r10))).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .r11 v → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  cases k <;> cases o <;> simp only [binIns, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
    refine Host.eventually_of_interp_cps hi ?_ <;>
    simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, set_q, get_q,
      Reg64s.set_low32, Reg64s.get_low32] <;>
    simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
    subst hv <;>
    (try intro _) <;>
    refine hk _ ?_ rfl
  all_goals first | rfl | (dsimp only; rw [BitVec.add_comm])

theorem eventually_storelD {i : Nat} {rv ra : Reg64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (storelD rv ra))
    {v : Int} (hload : Mem.loadInt s.dmem (s.regs.get64 ra) 8 = some v)
    (hk : ∀ s' : MachineData, s'.regs = s.regs →
      s'.dmem = Mem.storeInt s.dmem (s.regs.get64 ra) 8 (s.regs.get64 rv).toInt →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [storelD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, Effects.All, get_q, atReg_interp]
  simp only [MachineData.store, Effects.All_require_write_access, Width.bytes, hload]
  exact hk _ rfl rfl

theorem eventually_loadlD {i : Nat} {rd ra : Reg64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (ins (.mov (.reg (q rd)) (.mem (atReg ra)))))
    {v : Int} (hload : Mem.loadInt s.dmem (s.regs.get64 ra) 8 = some v)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 rd (BitVec.ofInt 64 v) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, set_q, atReg_interp]
  simp only [MachineData.load, Effects.All_require_read_access, Width.bytes, hload]
  exact hk _ rfl rfl

theorem eventually_jmp {k j : Nat} {l : Label} {s : MachineData} {post : (MachineState → Prop)}
    (hc : (jmp l).IsInfixAt Host.prog k) (hj : Labels.label l = Host.addrOf j)
    (hk : Run j s post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All]
  rw [hj, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk

theorem eventually_jnz {k j : Nat} {r : Reg64} {l : Label} {s : MachineData}
    {post : (MachineState → Prop)}
    (hc : (jnz r l).IsInfixAt Host.prog k) (hj : Labels.label l = Host.addrOf j)
    (hk : ∀ s' : MachineData, s'.regs = s.regs → s'.dmem = s.dmem →
      (Truthy (s.regs.get64 r) → Run j s' post) ∧
      (¬ Truthy (s.regs.get64 r) → Run (k + 2) s' post)) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, -⟩ := hc1.cons
  refine Host.eventually_of_interp_cps h0 ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Effects.All, Reg64s.get_low32]
  intro af
  refine Host.eventually_of_interp_cps h1 ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All, CondCode.interp,
    StatusFlags.from_result, BitVec.and_self]
  by_cases h0 : Truthy (s.regs.get64 r)
  · have : ((s.regs.get64 r).setWidth 32 == BitVec.zero 32) = false := by
      simpa [BitVec.zero, Truthy] using h0
    simp only [this, Bool.not_false, ↓reduceIte, Effects.All]
    rw [hj]
    refine (hk _ ?_ ?_).1 h0 <;> rfl
  · have : ((s.regs.get64 r).setWidth 32 == BitVec.zero 32) = true := by
      simpa [BitVec.zero, Truthy] using h0
    simp only [this, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Effects.All]
    refine (hk _ ?_ ?_).2 h0 <;> rfl

theorem eventually_ret {k : Nat} {s : MachineData} {ra : Int64} {R : DataMem → Prop}
    {post : (MachineState → Prop)}
    (hc : ret.IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ Eq (ra.toUInt64.At (s.regs.get64 .rsp)) ⋆ R)
    (hk : Eventually (step1 Host.exe) post
      ⟨{ s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) }, ra⟩) :
    Run k s post :=
  Host.eventually_ret (List.isInfixAt_singleton.mp hc) hmem hk

/-! ## Snippets -/

abbrev scratchRegs : List Reg64 := [.r10, .r11]

omit [Host] in
theorem ne_of_not_mem_scratch {r : Reg64} (h : r ∉ scratchRegs) : r ≠ .r10 ∧ r ≠ .r11 :=
  ⟨fun he => h (by simp [he]), fun he => h (by simp [he])⟩

theorem eventually_mov {k : Nat} {rd rs : Reg64} {s : MachineData} {post : (MachineState → Prop)}
    (hc : (mov rd rs).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = s.regs.get64 rs →
      (∀ r, r ∉ [rd] → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 1) s' post) :
    Run k s post := by
  refine eventually_movD (List.isInfixAt_singleton.mp hc) fun s' hs hm => hk s' ?_ ?_ hm
  · rw [hs, Reg64s.get64_set64_same]
  · intro r hr
    rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]

theorem eventually_movi {k : Nat} {rd : Reg64} {c : BitVec 64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hc : (movi rd c).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = c →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 1) s' post) :
    Run k s post := by
  refine eventually_moviD (List.isInfixAt_singleton.mp hc) fun s' hs hm => hk s' ?_ ?_ hm
  · rw [hs, Reg64s.get64_set64_same]
  · intro r hr
    rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]

theorem eventually_op {k : Nat} {o : Op Reg64} {rd : Reg64} {c : List Directive} {v : Val}
    {s : MachineData} {post : (MachineState → Prop)}
    (hop : op o rd = some c) (hc : c.IsInfixAt Host.prog k)
    (hvars : ∀ r, r ∈ o.vars → r ∉ scratchRegs)
    (hv : (o.map s.regs.get64).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + c.length) s' post) :
    Run k s post := by
  cases o with
  | bin kk oo a b =>
    simp only [op, Option.map_eq_some_iff] at hop
    obtain ⟨i, hb, rfl⟩ := hop
    obtain ⟨h0, hc1⟩ := hc.cons
    obtain ⟨h1, hc2⟩ := hc1.cons
    obtain ⟨h2, hc3⟩ := hc2.cons
    obtain ⟨h3, -⟩ := hc3.cons
    have hbv : ∀ r, r ∈ b.vars → r ≠ .r11 := fun r hr =>
      (ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))).2
    refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
    refine eventually_argTo h1 fun s2 hs2 hm2 => ?_
    have e11 : s2.regs.get64 .r11 = argv s.regs a := by
      rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1, Reg64s.get64_set64_same]
    have e10 : s2.regs.get64 .r10 = argv s.regs b := by
      rw [hs2, Reg64s.get64_set64_same]
      exact argv_congr fun r hr => by
        rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hbv r hr))]
    have hv' := (eval_bin_imm kk oo (a.map s.regs.get64) (b.map s.regs.get64)).symm.trans hv
    refine eventually_binIns hb h2 (by rw [e11, e10]; exact hv') fun s3 hs3 hm3 => ?_
    refine eventually_movD h3 fun s4 hs4 hm4 => hk s4 ?_ (fun r hr => ?_) ?_
    · rw [hs4, Reg64s.get64_set64_same, hs3, Reg64s.get64_set64_same]
    · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
      rw [hs4, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs3,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1), hs2,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1), hs1,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1)]
    · rw [hm4, hm3, hm2, hm1]
  | cmp => simp [op] at hop
  | ext => simp [op] at hop
  | copy kk a =>
    have keep : ∀ (x : Val) (s1 : MachineData), s1.regs = s.regs.set64 rd x →
        ∀ r, r ∉ rd :: scratchRegs → s1.regs.get64 r = s.regs.get64 r := by
      intro x s1 hs1 r hr
      simp only [List.mem_cons, not_or] at hr
      rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1)]
    cases kk with
    | l =>
      simp only [op, Option.some.injEq] at hop
      subst hop
      simp only [Op.map, Op.eval, Cls.trunc, Option.some.injEq] at hv
      refine eventually_argTo (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
        hk s1 ?_ (keep _ s1 hs1) hm1
      rw [hs1, Reg64s.get64_set64_same]; exact hv
    | w =>
      cases a with
      | var r =>
        simp only [op, Option.some.injEq] at hop
        subst hop
        simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
        refine eventually_movlD (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
          hk s1 ?_ (keep _ s1 hs1) hm1
        rw [hs1, Reg64s.get64_set64_same]; exact hv
      | imm c0 =>
        simp only [op, Option.some.injEq] at hop
        subst hop
        simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
        refine eventually_moviD (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
          hk s1 ?_ (keep _ s1 hs1) hm1
        rw [hs1, Reg64s.get64_set64_same]; exact hv

theorem eventually_load {k : Nat} {cl : Cls} {sz : Sz} {sg : Bool} {rd : Reg64} {a : Arg Reg64}
    {c : List Directive} {v : Val} {s : MachineData} {post : (MachineState → Prop)}
    (hop : load cl sz sg rd a = some c) (hc : c.IsInfixAt Host.prog k)
    (hv : loadVal s.dmem cl sz sg (argv s.regs a) = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + c.length) s' post) :
    Run k s post := by
  cases cl <;> cases sz <;> cases a <;> simp only [load, reduceCtorEq, Option.some.injEq] at hop
  subst hop
  simp only [loadVal, Option.map_eq_some_iff, Sz.bytes] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  refine eventually_loadlD (List.isInfixAt_singleton.mp hc) hi fun s1 hs1 hm1 =>
    hk s1 ?_ (fun r hr => ?_) hm1
  · rw [hs1, Reg64s.get64_set64_same]
    cases sg <;> rfl
  · simp only [List.mem_cons, not_or] at hr
    rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1)]

theorem eventually_store {k : Nat} {sz : Sz} {x a : Arg Reg64} {c : List Directive}
    {s : MachineData} {post : (MachineState → Prop)}
    (hop : store sz x a = some c) (hc : c.IsInfixAt Host.prog k)
    (hvars : ∀ r, r ∈ x.vars ++ a.vars → r ∉ scratchRegs)
    (hok : storeOk s.dmem sz (argv s.regs a))
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratchRegs → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = storeMem s.dmem sz (argv s.regs a) (argv s.regs x) →
      Run (k + c.length) s' post) :
    Run k s post := by
  cases sz <;> cases a <;> simp only [store, reduceCtorEq, Option.some.injEq] at hop
  rename_i ra
  subst hop
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, -⟩ := hc1.cons
  have hra := ne_of_not_mem_scratch (hvars ra (by simp [Arg.vars]))
  obtain ⟨i, hi⟩ := hok
  refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
  have e : s1.regs.get64 ra = s.regs.get64 ra := by
    rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hra.2)]
  refine eventually_storelD h1 (v := i) (by rw [hm1, e]; exact hi) fun s2 hs2 hm2 =>
    hk s2 (fun r hr => ?_) ?_
  · have := ne_of_not_mem_scratch hr
    rw [hs2, hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm this.2)]
  · rw [hm2, hm1, e, hs1, Reg64s.get64_set64_same]
    rfl

end

/-! ## Frame directives (moved from FrameLemmas.lean, written by memframe) -/

section
variable [Host]

/-- `push %r` -/
theorem eventually_pushD {i : Nat} {r : Reg64} {s : MachineData} {F : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (pushD r))
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp - 8#64) 8 ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) →
      (s'.dmem =⋆ word (s.regs.get64 .rsp - 8#64) (s.regs.get64 r) ⋆ F) →
      Run (i + 1) s' post) :
    Run i s post := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps hi ?_
  simp only [pushD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, get_q, Effects.All]
  refine (store_All_of_sep _ _ .W64 _ _ _ bs F ?_ hl).mpr ?_
  · exact hbs
  exact hk _ rfl (Mem.storeInt_sep _ 8 bs F s.dmem ⟨hbs, hl⟩ _)

/-- `pop %r` -/
theorem eventually_popD {i : Nat} {r : Reg64} {v : Val} {s : MachineData} {F : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (popD r))
    (hmem : s.dmem =⋆ word (s.regs.get64 .rsp) v ⋆ F)
    (hk : ∀ s' : MachineData,
      s'.regs = (s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64)).set64 r v → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [popD, Directive.interp, Instr.interp, Operation.interp]
  refine (load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) F hmem
    (Int.toBytes_length _ _)).mpr ?_
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  simp only [MachineData.set, MachineData.setReg, set_q, Effects.All]
  rw [hv]
  exact hk _ rfl rfl

/-- `sub $c, %rsp` (flags arbitrary). -/
theorem eventually_subSpD {i : Nat} {c : Int64} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (subSpD c))
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - c.toBitVec) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [subSpD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg, Effects.All, set_q,
    get_q]
  exact hk _ (by simp) rfl

/-- `add $c, %rsp` (flags arbitrary). -/
theorem eventually_addSpD {i : Nat} {c : Int64} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (addSpD c))
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp + c.toBitVec) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [addSpD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg, Effects.All, set_q,
    get_q]
  exact hk _ (by simp [BitVec.add_comm]) rfl

/-- `movq %rv, off(%rsp)` -/
theorem eventually_stSpD {i : Nat} {rv : Reg64} {off : Int64} {s : MachineData}
    {F : Mem 64 → Prop} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (stSpD rv off))
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp + off.toBitVec) 8 ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs →
      (s'.dmem =⋆ word (s.regs.get64 .rsp + off.toBitVec) (s.regs.get64 rv) ⋆ F) →
      Run (i + 1) s' post) :
    Run i s post := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps hi ?_
  simp only [stSpD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, get_q, AddrExpr.interp_base_disp]
  refine (store_All_of_sep _ _ .W64 _ _ _ bs F (by simpa using hbs) hl).mpr ?_
  simp only [Effects.All]
  exact hk _ rfl (Mem.storeInt_sep _ 8 bs F s.dmem ⟨hbs, hl⟩ (s.regs.get64 rv).toInt)

/-- `movq off(%rsp), %rd` -/
theorem eventually_ldSpD {i : Nat} {rd : Reg64} {off : Int64} {v : Val} {s : MachineData}
    {F : Mem 64 → Prop} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (ldSpD rd off))
    (hmem : s.dmem =⋆ word (s.regs.get64 .rsp + off.toBitVec) v ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 rd v → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [ldSpD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, AddrExpr.interp_base_disp]
  refine (load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) F hmem
    (Int.toBytes_length _ _)).mpr ?_
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  simp only [MachineData.set, MachineData.setReg, set_q, Effects.All]
  rw [hv]
  exact hk _ rfl rfl

/-- `call l`, where `l` resolves to the address of directive `j`. -/
theorem eventually_callD {i j : Nat} {l : Label} {s : MachineData} {F : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (callD l)) (hj : Labels.label l = Host.addrOf j)
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp - 8#64) 8 ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) →
      (s'.dmem =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.get64 .rsp - 8#64)) ⋆ F) →
      Run j s' post) :
    Run i s post := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps hi ?_
  simp only [callD, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  refine (store_All_of_sep _ _ .W64 _ _ _ bs F ?_ hl).mpr ?_
  · exact hbs
  rw [hj, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk _ rfl (Mem.storeInt_sep _ 8 bs F s.dmem ⟨hbs, hl⟩ _)

/-- `call l` to wherever `l` resolves (the callee need not be in a known position). -/
theorem eventually_callD_any {i : Nat} {l : Label} {s : MachineData} {F : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (callD l))
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp - 8#64) 8 ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) →
      (s'.dmem =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.get64 .rsp - 8#64)) ⋆ F) →
      Eventually (step1 Host.exe) post ⟨s', Labels.label l⟩) :
    Run i s post := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps hi ?_
  simp only [callD, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  refine (store_All_of_sep _ _ .W64 _ _ _ bs F ?_ hl).mpr ?_
  · exact hbs
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk _ rfl (Mem.storeInt_sep _ 8 bs F s.dmem ⟨hbs, hl⟩ _)

/-- `add %rs, %rd`: `rd := rs + rd` (flags arbitrary). -/
theorem eventually_addRR {i : Nat} {rd rs : Reg64} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (ins (.add (.reg (q rd)) (.reg (q rs)))))
    (hk : ∀ s' : MachineData,
      s'.regs = s.regs.set64 rd (s.regs.get64 rs + s.regs.get64 rd) → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, set_q, get_q]
  exact hk _ rfl rfl

/-- `jmp l`, where `l` resolves to the address of directive `j`. -/
theorem eventually_jmpD {i j : Nat} {l : Label} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (jmpD l)) (hj : Labels.label l = Host.addrOf j)
    (hk : Run j s post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [jmpD, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  rw [hj, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk

/-- `jmp l` to wherever `l` resolves (a tail jump, possibly out of the function). -/
theorem eventually_jmpD_any {i : Nat} {l : Label} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (jmpD l))
    (hk : Eventually (step1 Host.exe) post ⟨s, Labels.label l⟩) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [jmpD, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk

end


theorem spEntry_call (sp : Val) (ns : Nat) (h : (sp + 8#64).toNat % 16 = 0) :
    (sp - BitVec.ofNat 64 (frameSize ns) - BitVec.ofNat 64 8 + 8#64).toNat % 16 = 0 := by
  have e : sp - BitVec.ofNat 64 (frameSize ns) - BitVec.ofNat 64 8 + 8#64 =
      sp - BitVec.ofNat 64 (frameSize ns) := by
    rw [BitVec.sub_add_cancel]
  rw [e]
  have hsp := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h
  simp only [frameSize, BitVec.toNat_sub, BitVec.toNat_ofNat]
  split <;> omega

theorem prologue_spec [Host] {k ns : Nat} {s : MachineData} {ra : Int64} {G : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hc : [subSpD (Int64.ofNat (frameSize ns))].IsInfixAt Host.prog k)
    (hF : frameSize ns + 8 ≤ 2 ^ 64)
    (hmem : s.dmem =⋆ Eq (ra.toUInt64.At (s.regs.get64 .rsp)) ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (frameSize ns)) (frameSize ns) ⋆ G)
    (hk : ∀ s' : MachineData, s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (frameSize ns) →
      (∀ r, r ∉ Reg64.rsp :: ([] ++ scratchRegs) → s'.regs.get64 r = s.regs.get64 r) →
      (s'.dmem =⋆ (region (s.regs.get64 .rsp - BitVec.ofNat 64 (frameSize ns) +
          BitVec.ofNat 64 (8 * ns)) (frameSize ns - 8 * ns) ⋆
          Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆
        region (s.regs.get64 .rsp - BitVec.ofNat 64 (frameSize ns)) (8 * ns) ⋆ G) →
      Run (k + 1) s' post) :
    Run k s post := by
  refine eventually_subSpD (List.isInfixAt_singleton.mp hc) fun s' hs hm => hk s' ?_ ?_ ?_
  · rw [hs, Reg64s.get64_set64_same]; simp
  · intro r hr
    rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]
  · have hle : 8 * ns ≤ frameSize ns := by simp only [frameSize]; split <;> omega
    have e : frameSize ns = 8 * ns + (frameSize ns - 8 * ns) := by omega
    rw [hm]
    rw [e, region_split (by omega), ← e] at hmem
    ac_nf at hmem ⊢

theorem epilogue_spec [Host] {k ns : Nat} {s : MachineData} {ra : Int64} {G : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hc : [addSpD (Int64.ofNat (frameSize ns))].IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ (region (s.regs.get64 .rsp + BitVec.ofNat 64 (frameSize ns) -
          BitVec.ofNat 64 (frameSize ns) + BitVec.ofNat 64 (8 * ns)) (frameSize ns - 8 * ns) ⋆
          Eq (ra.toUInt64.At (s.regs.get64 .rsp + BitVec.ofNat 64 (frameSize ns)))) ⋆ G)
    (hk : ∀ s' : MachineData, s'.regs.get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 (frameSize ns) →
      True →
      (∀ r, r ∉ Reg64.rsp :: ([] ++ scratchRegs) → s'.regs.get64 r = s.regs.get64 r) →
      (s'.dmem =⋆ Eq (ra.toUInt64.At (s.regs.get64 .rsp + BitVec.ofNat 64 (frameSize ns))) ⋆
        region (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * ns)) (frameSize ns - 8 * ns) ⋆ G) →
      Run (k + 1) s' post) :
    Run k s post := by
  refine eventually_addSpD (List.isInfixAt_singleton.mp hc) fun s' hs hm => hk s' ?_ trivial ?_ ?_
  · rw [hs, Reg64s.get64_set64_same]; simp
  · intro r hr
    rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]
  · rw [hm]
    rw [BitVec.add_sub_cancel] at hmem
    ac_nf at hmem ⊢


/-! ## The `Target` instance -/

/-- One step of the laid-out host program `h`. -/
def hostStep (h : Host) : MachineState → (MachineState → Prop) → Prop :=
  letI := h; step1 Host.exe

/-- The address label `l` resolves to in host `h`. -/
def hostLabel (h : Host) (l : Label) : Int64 :=
  letI := h; Labels.label l

/-- Kraken x64 as a `Target`. -/
@[reducible] def target : Target where
  toIsa := isa
  MData := MachineData
  Addr := Int64
  State := MachineState
  Host := Host
  get s r := s.regs.get64 r
  mem s := s.dmem
  mkState s a := ⟨s, a⟩
  pc st := st.pc
  data st := st.data
  pc_mk _ _ := rfl
  data_mk _ _ := rfl
  mk_eta _ := rfl
  prog h := @Host.prog h
  addrOf h k := @Host.addrOf h k
  labelAddr := hostLabel
  step := hostStep
  raBytes := 8
  RetAddr sp ra := Eq (ra.toUInt64.At sp)
  raReg _ _ := True
  spEntry sp := (sp + 8#64).toNat % 16 = 0
  Saved sp ra ns := region (sp - BitVec.ofNat 64 (frameSize ns) + BitVec.ofNat 64 (8 * ns))
    (frameSize ns - 8 * ns) ⋆ Eq (ra.toUInt64.At sp)
  spOk _ := True
  sp_not_scratch := by simp
  sp_not_allocatable := by simp
  scratch_not_allocatable := by simp
  calleeSaved_not_scratch := by simp
  calleeSaved_not_allocatable := by simp
  sp_not_calleeSaved := by simp
  argRegs_not_scratch := by simp
  retRegs_not_scratch := by simp
  sp_not_retRegs := by simp
  sp_not_argRegs := by simp
  retAddr_region _ ra _ h := ⟨ra.toUInt64.toBytes, UInt64.toBytes_length _, h.symm⟩
  raReg_congr _ _ _ _ _ := trivial
  raReg_of_raRegs _ _ _ _ _ := trivial
  raRegs_not_allocatable := by simp
  raRegs_not_scratch := by simp
  raRegs_not_calleeSaved := by simp
  raRegs_not_argRegs := by simp
  raRegs_not_retRegs := by simp
  sp_not_raRegs := by simp
  slots_le_frameSize ns := by simp only [frameSize]; split <;> omega
  spOk_frame _ _ _ := trivial
  spEntry_call := spEntry_call
  prologue_spec {h} {_} {_} {_} {_} {_} {_} hc _ _ hF hmem hk := by
    letI := h; exact prologue_spec hc hF hmem hk
  epilogue_spec {h} {_} {_} {_} {_} {_} {_} hc _ hmem hk := by
    letI := h; exact epilogue_spec hc hmem hk
  slotSt_spec {h} {_} {_} {_} {_} {_} {_} hc _ _ hmem hk := by
    letI := h
    exact eventually_stSpD (List.isInfixAt_singleton.mp hc) hmem fun s' hs hm =>
      hk s' (fun r _ => by rw [hs]) hm
  slotLd_spec {h} {_} {_} {rd} {_} {_} {_} {_} hc _ hmem hk := by
    letI := h
    refine eventually_ldSpD (List.isInfixAt_singleton.mp hc) hmem fun s' hs hm =>
      hk s' ?_ (fun r hr => ?_) hm
    · show s'.regs.get64 rd = _
      rw [hs, Reg64s.get64_set64_same]
    · show s'.regs.get64 r = _
      rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]
  call_spec {h} {_} {_} {s} {_} {_} hc hmem hk := by
    letI := h
    refine eventually_callD_any (List.isInfixAt_singleton.mp hc) hmem fun s' hs hm =>
      hk s' ?_ (fun r hr => ?_) trivial ?_
    · show s'.regs.get64 .rsp = _
      rw [hs, Reg64s.get64_set64_same]
    · show s'.regs.get64 r = _
      rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]
    · show (Eq _ ⋆ _) s'.dmem
      have e : s'.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 := by
        rw [hs, Reg64s.get64_set64_same]
      show (Eq ((Host.addrOf (_ + 1)).toUInt64.At (s'.regs.get64 .rsp)) ⋆ _) s'.dmem
      rw [e]; exact hm
  tailJmp_spec {h} {_} {_} {s} {_} hc hk := by
    letI := h
    exact eventually_jmpD_any (List.isInfixAt_singleton.mp hc) (hk s (fun _ _ => rfl) rfl)
  labelAddr_eq {h} {_} {_} hk hfirst := letI := h; Host.label_eq_addrOf hk hfirst
  label_spec {h} {_} {_} {_} {_} hi hrun := letI := h; Host.eventually_label hi hrun
  mov_spec {h} {_} {_} {_} {_} {_} hc hk := letI := h; eventually_mov hc hk
  movi_spec {h} {_} {_} {_} {_} {_} hc hk := letI := h; eventually_movi hc hk
  op_spec {h} {_} {_} {_} {_} {_} {_} {_} hop hc hvars hv hk :=
    letI := h; eventually_op hop hc hvars hv hk
  load_spec {h} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} hop hc _ hv hk :=
    letI := h; eventually_load hop hc hv hk
  store_spec {h} {_} {_} {_} {_} {_} {_} {_} hop hc hvars hok hk :=
    letI := h; eventually_store hop hc hvars hok hk
  jmp_spec {h} {_} {_} {_} {s} {_} hc hj hk :=
    letI := h; eventually_jmp hc hj (hk s (fun _ _ => rfl) rfl)
  jnz_spec {h} {_} {_} {_} {_} {_} {_} hc hj _ hk := by
    letI := h
    exact eventually_jnz hc hj fun s' hregs hmem =>
      hk s' (fun r _ => congrArg (Reg64s.get64 · r) hregs) hmem
  ret_spec {h} {_} {s} {_} {_} {_} hc _ hmem hk := by
    letI := h
    refine eventually_ret hc hmem (hk _ (fun r hr => ?_) ?_ rfl)
    · exact Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (he ▸ List.mem_cons_self)
    · exact Reg64s.get64_set64_same s.regs .rsp _

end LeanQbe.Amd64
