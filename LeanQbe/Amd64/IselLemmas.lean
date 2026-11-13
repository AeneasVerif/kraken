module

public import LeanQbe.Amd64.Isel
public import Kraken.X64.WP
public import Kraken.X64.Sep
public import Kraken.X64.Regs
public import LeanQbe.AbiLemmas
public import LeanQbe.StepSimp
import Kraken.X64.Parser

/-!
# x64 instruction selection: step lemmas

Position-free directive and snippet lemmas for `Isel.lean` stated with `Directive.FallsTo` and
Kraken's `Program.wp`, bridged to `Target`'s continuation-style `eventually_op`, `eventually_load`,
`eventually_store`, and `eventually_jnzCmp` via a small combinator section at the top of the file.

* Every directive `Isel.lean` emits is checked equal to the output of Kraken's x64 parser by `rfl`
  (`ParserChecks`).
* Single-directive lemmas use `Upd s regs s' := ∃ status, s' = { s with regs, status }` so all
  non-flag fields of `MachineData` (`dmem`, `zmms`, and future `df`) are preserved automatically.
* Snippet lemmas compose via `Program.wp.cons` and `Program.wp.append`, with `fun_cases` for
  dispatch (`op`, `store`, `jnzCmp`) and `grind` for register-frame goals.
-/

@[expose] public section

/-! ## Rules for `Directive.FallsTo` and `Program.wp` -/

/-- Directive `d`, run from `s`, falls through into a state satisfying `Q`: every continuation
that accepts such states is accepted, for every label assignment and every address range. -/
def Directive.FallsTo (d : Directive) (s : MachineData) (Q : MachineData → Prop) : Prop :=
  ∀ [Labels] (p : Std.Rco Int64) (next : MachineData → Effects)
    (jmp : Int64 → MachineData → Effects) (P : MachineState → Prop),
    (∀ s', Q s' → (next s').All P) → (d.interp s p next jmp).All P

theorem Directive.FallsTo.wp [Host] {d : Directive} {s : MachineData} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} (h : d.FallsTo s Q) : Program.wp [d] Q E s :=
  Program.wp_singleton fun _ _ => h _ _ _ _ fun _ hq => Or.inl ⟨rfl, hq⟩

namespace Program

variable [Host] {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}

/-- Run the head directive through a fact about it, then the rest. -/
theorem wp.cons {d : Directive} {p : Program} {Qd : MachineData → Prop}
    (hd : Program.wp [d] Qd E s) (hp : ∀ s', Qd s' → Program.wp p Q E s') :
    Program.wp (d :: p) Q E s :=
  Program.wp_cons (Program.wp_mono hp (fun _ _ h => h) hd)

/-- Run a prefix through a fact about it, then the rest. -/
theorem wp.append {p q : Program} {Qp : MachineData → Prop}
    (hp : Program.wp p Qp E s) (hq : ∀ s', Qp s' → Program.wp q Q E s') :
    Program.wp (p ++ q) Q E s :=
  Program.wp_append (Program.wp_mono hq (fun _ _ h => h) hp)

/-- Weaken the fallthrough postcondition. -/
theorem wp.mono {p : Program} {Q' : MachineData → Prop} (h : Program.wp p Q E s)
    (hQ : ∀ s', Q s' → Q' s') : Program.wp p Q' E s :=
  Program.wp_mono hQ (fun _ _ h => h) h

/-- Use `Program.wp` at a position of the host program, in continuation form. -/
theorem wp.eventually {p : Program} {k : Nat} {post : MachineState → Prop}
    (h : Program.wp p Q E s) (hk : p.IsInfixAt Host.prog k)
    (hQ : ∀ s', Q s' → Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + p.length)⟩)
    (hE : ∀ a s', E a s' → Eventually (step1 Host.exe) post ⟨s', a⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine eventually_trans _ _ _ _ (h k hk) ?_
  rintro ⟨s', a⟩ (⟨ha, hq⟩ | he)
  · dsimp only at ha hq; subst ha; exact hQ s' hq
  · exact hE a s' he

end Program

namespace LeanQbe.Amd64

/-- `s'` is `s` with registers `regs` and some flags (preserving `dmem`, `zmms`, etc.). -/
abbrev Upd (s : MachineData) (regs : Reg64s) (s' : MachineData) : Prop :=
  ∃ status, s' = { s with regs, status }

/-- `s'` has registers `regs`, the memory of `s`, and any flags. -/
abbrev Regs (s : MachineData) (regs : Reg64s) (s' : MachineData) : Prop :=
  s'.regs = regs ∧ s'.dmem = s.dmem

/-- `s'` has the registers and memory of `s`, and flags `f`. -/
abbrev Flags (s : MachineData) (f : StatusFlags) (s' : MachineData) : Prop :=
  s'.regs = s.regs ∧ s'.dmem = s.dmem ∧ s'.status = f

/-- `s'` has the registers of `s` and memory `dmem`. -/
abbrev MemUpd (s : MachineData) (dmem : DataMem) (s' : MachineData) : Prop :=
  s'.regs = s.regs ∧ s'.dmem = dmem

theorem Upd.regs {s s' : MachineData} {regs : Reg64s} (h : Upd s regs s') : Regs s regs s' := by
  obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem Upd.zmms {s s' : MachineData} {regs : Reg64s} (h : Upd s regs s') : s'.zmms = s.zmms := by
  obtain ⟨_, rfl⟩ := h; rfl

theorem upd_eq {s s' : MachineData} {regs : Reg64s}
    (h1 : s' = { s with regs := s'.regs, status := s'.status }) (h2 : s'.regs = regs) :
    Upd s regs s' :=
  ⟨s'.status, h2 ▸ h1⟩

theorem wp_regs [Host] {d : Directive} {s : MachineData} {regs : Reg64s}
    {E : Int64 → MachineData → Prop} (h : d.FallsTo s (Upd s regs)) :
    Program.wp [d] (Regs s regs) E s :=
  h.wp.mono fun _ => Upd.regs

theorem wp_flags [Host] {d : Directive} {s : MachineData} {status : StatusFlags}
    {E : Int64 → MachineData → Prop} (h : d.FallsTo s (· = { s with status })) :
    Program.wp [d] (Flags s status) E s :=
  h.wp.mono fun _ h => by subst h; exact ⟨rfl, rfl, rfl⟩

theorem wp_mem [Host] {d : Directive} {s : MachineData} {dmem : DataMem}
    {E : Int64 → MachineData → Prop} (h : d.FallsTo s (· = { s with dmem })) :
    Program.wp [d] (MemUpd s dmem) E s :=
  h.wp.mono fun _ h => by subst h; exact ⟨rfl, rfl⟩

abbrev Run [Host] (k : Nat) (s : MachineData) (post : MachineState → Prop) : Prop :=
  Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩

abbrev scratchRegs : List Reg64 := [.r10, .r11]

theorem ne_of_not_mem_scratch {r : Reg64} (h : r ∉ scratchRegs) : r ≠ .r10 ∧ r ≠ .r11 :=
  ⟨fun he => h (by simp [he]), fun he => h (by simp [he])⟩

/-- What a snippet that computes `v` into `rd` guarantees: the shape of `Target.op_spec`. -/
abbrev Result (s : MachineData) (rd : Reg64) (v : Val) (s' : MachineData) : Prop :=
  s'.regs.get64 rd = v ∧ (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) ∧
    s'.dmem = s.dmem

/-- `s'` keeps the memory of `s` and its registers outside the scratch registers. -/
abbrev Kept (s s' : MachineData) : Prop :=
  (∀ r, r ∉ scratchRegs → s'.regs.get64 r = s.regs.get64 r) ∧ s'.dmem = s.dmem

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
example : parse("imul %r10, %r11") = [(binIns .l .mul).get rfl] := rfl
example : parse("imull %r10d, %r11d") = [(binIns .w .mul).get rfl] := rfl
example : parse("shl %cl, %r11") = [(shiftIns .l .shl).get rfl] := rfl
example : parse("shr %cl, %r11") = [(shiftIns .l .shr).get rfl] := rfl
example : parse("sar %cl, %r11") = [(shiftIns .l .sar).get rfl] := rfl
example : parse("shll %cl, %r11d") = [(shiftIns .w .shl).get rfl] := rfl
example : parse("shrl %cl, %r11d") = [(shiftIns .w .shr).get rfl] := rfl
example : parse("sarl %cl, %r11d") = [(shiftIns .w .sar).get rfl] := rfl
example : parse("cmp %r10, %r11") = [cmpIns .l] := rfl
example : parse("cmpl %r10d, %r11d") = [cmpIns .w] := rfl
example : parse("sete %r11b") = [setccD (condOf .eq)] := rfl
example : parse("setne %r11b") = [setccD (condOf .ne)] := rfl
example : parse("setle %r11b") = [setccD (condOf .sle)] := rfl
example : parse("setl %r11b") = [setccD (condOf .slt)] := rfl
example : parse("setge %r11b") = [setccD (condOf .sge)] := rfl
example : parse("setg %r11b") = [setccD (condOf .sgt)] := rfl
example : parse("setbe %r11b") = [setccD (condOf .ule)] := rfl
example : parse("setb %r11b") = [setccD (condOf .ult)] := rfl
example : parse("setae %r11b") = [setccD (condOf .uge)] := rfl
example : parse("seta %r11b") = [setccD (condOf .ugt)] := rfl
example : parse("neg %rdx") = [negIns .l .rdx] := rfl
example : parse("negl %edx") = [negIns .w .rdx] := rfl
example : parse("movzbl %r11b, %esi") = [movzbD .rsi] := rfl
example : parse("movsbq %dil, %rax") = [extD .l .b true .rax .rdi] := rfl
example : parse("movsbl %dil, %eax") = [extD .w .b true .rax .rdi] := rfl
example : parse("movzbl %dil, %eax") = [extD .l .b false .rax .rdi] := rfl
example : parse("movzbl %dil, %eax") = [extD .w .b false .rax .rdi] := rfl
example : parse("movswq %di, %rax") = [extD .l .h true .rax .rdi] := rfl
example : parse("movswl %di, %eax") = [extD .w .h true .rax .rdi] := rfl
example : parse("movzwl %di, %eax") = [extD .l .h false .rax .rdi] := rfl
example : parse("movzwl %di, %eax") = [extD .w .h false .rax .rdi] := rfl
example : parse("movslq %edi, %rax") = [extD .l .w true .rax .rdi] := rfl
example : parse("movl %edi, %eax") = [extD .w .w true .rax .rdi] := rfl
example : parse("movl %edi, %eax") = [extD .l .w false .rax .rdi] := rfl
example : parse("mov %rdi, %rax") = [extD .l .l true .rax .rdi] := rfl
example : parse("movl %edi, %eax") = [extD .w .l false .rax .rdi] := rfl
example : parse("movsbq (%rdx), %rax") = loadIns .l .b true .rax .rdx := rfl
example : parse("movsbl (%rdx), %eax") = loadIns .w .b true .rax .rdx := rfl
example : parse("movzbl (%rdx), %eax") = loadIns .l .b false .rax .rdx := rfl
example : parse("movswq (%rdx), %rax") = loadIns .l .h true .rax .rdx := rfl
example : parse("movswl (%rdx), %eax") = loadIns .w .h true .rax .rdx := rfl
example : parse("movzwl (%rdx), %eax") = loadIns .w .h false .rax .rdx := rfl
example : parse("movslq (%rdx), %rax") = loadIns .l .w true .rax .rdx := rfl
example : parse("movl (%rdx), %eax") = loadIns .w .w true .rax .rdx := rfl
example : parse("movl (%rdx), %eax") = loadIns .l .w false .rax .rdx := rfl
example : parse("mov (%rdx), %rax") = loadIns .l .l false .rax .rdx := rfl
example : parse("mov (%rdx), %rax; movl %eax, %eax") = loadIns .w .l true .rax .rdx := rfl
example : parse("movb %r11b, (%rdx)") = [storeIns .b .rdx] := rfl
example : parse("movw %r11w, (%rdx)") = [storeIns .h .rdx] := rfl
example : parse("movl %r11d, (%rdx)") = [storeIns .w .rdx] := rfl
example : parse("movq %r11, (%r10)") = [storeIns .l .r10] := rfl
example : parse("mov $5, %r10; mov %r10, %r11; mov %rdi, %r10") =
  (movi .r10 5 ++ [argTo .r11 (.var .r10), argTo .r10 (.var .rdi)]) := rfl
example : parse("mov $0, %rdx; div %r11") = ((divCore .l .udiv).get rfl).1 := rfl
example : parse("mov $0, %rdx; div %r11") = ((divCore .l .urem).get rfl).1 := rfl
example : parse("mov $0, %rdx; divl %r11d") = ((divCore .w .udiv).get rfl).1 := rfl
example : parse("mov $0, %rdx; divl %r11d") = ((divCore .w .urem).get rfl).1 := rfl
example : parse("mov %rax, %rdx; sar $63, %rdx; idiv %r11") =
  ((divCore .l .div).get rfl).1 := rfl
example : parse("mov %rax, %rdx; sar $63, %rdx; idiv %r11") =
  ((divCore .l .rem).get rfl).1 := rfl
example : parse("movl %eax, %edx; sarl $31, %edx; idivl %r11d") =
  ((divCore .w .div).get rfl).1 := rfl
example : parse("movl %eax, %edx; sarl $31, %edx; idivl %r11d") =
  ((divCore .w .rem).get rfl).1 := rfl
example : parse("shlq $3, %rcx") = [(shiftImmIns .l .shl .rcx 3).get rfl] := rfl
example : parse("shrl $3, %ecx") = [(shiftImmIns .w .shr .rcx 3).get rfl] := rfl
example : parse("sarq $63, %rdx") = [(shiftImmIns .l .sar .rdx 63).get rfl] := rfl
example : parse("add %rdi, %rcx") = [(binRegIns .l .add .rcx .rdi).get rfl] := rfl
example : parse("subl %edi, %ecx") = [(binRegIns .w .sub .rcx .rdi).get rfl] := rfl
example : parse("cmp %rax, %rdx") = [cmpRegIns .l .rdx .rax] := rfl
example : parse("movb %sil, (%rdx)") = [storeRegIns .b .rsi .rdx] := rfl
example : parse("movw %si, (%rdx)") = [storeRegIns .h .rsi .rdx] := rfl
example : parse("movl %esi, (%rdx)") = [storeRegIns .w .rsi .rdx] := rfl
example : parse("movq %rsi, (%rdx)") = [storeRegIns .l .rsi .rdx] := rfl
end ParserChecks

/-! ## Register file and addresses

`step_simp` (`LeanQbe/StepSimp.lean`) on x64: Kraken's interpreter down to the reads and writes of
the machine state, and the register accesses of 64 and 32 bits, and reads of 8 and 16 bits, in
terms of `Reg64s.get64` and `Reg64s.set64`. -/

attribute [step_simp] Directive.interp Instr.interp Operation.interp Operand.interp RegOrMem.interp
  RelRegOrMem.interp ConstExpr.interp ShiftCountExpr.interp ShiftCountExpr.interpMasked Effects.All
  MachineData.set MachineData.setReg Reg64s.get_low32 Reg64s.set_low32

/- `grind` reads a register through the writes before it: it splits on whether the two registers
are the same. -/
attribute [grind =] Reg64s.get64_set64

@[step_simp]
theorem get_q (regs : Reg64s) (r : Reg64) : regs.get (q r) = regs.get64 r := Reg64s.get_low64 ..

@[step_simp]
theorem set_q (regs : Reg64s) (r : Reg64) (v : BitVec 64) : regs.set (q r) v = regs.set64 r v :=
  rfl

/-- `[r]` evaluates to the contents of `r` (64-bit addressing). -/
@[step_simp]
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

theorem argv_set64 {regs : Reg64s} {t : Reg64} {x : Val} {a : Arg Reg64} (h : t ∉ a.vars) :
    argv (regs.set64 t x) a = argv regs a :=
  argv_congr fun _ hr => Reg64s.get64_set64_of_ne _ _ _ _ fun e => h (e ▸ hr)

/-- `Op.eval` of a binary operation only depends on the values of its operands. -/
theorem eval_bin_imm (k : Cls) (o : BinOp) (x y : Arg Val) :
    (Op.bin k o x y).eval = (Op.bin k o (.imm x.val) (.imm y.val)).eval := by
  cases k <;> rfl

/-! ## Bit vectors and arithmetic helpers -/

@[step_simp]
theorem get_b8 (regs : Reg64s) (r : Reg64) : regs.get (b8 r) = (regs.get64 r).setWidth 8 := by
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset]
  rfl

@[step_simp]
theorem get_h16 (regs : Reg64s) (r : Reg64) : regs.get (h16 r) = (regs.get64 r).setWidth 16 := by
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset]
  rfl

theorem set_b8 (regs : Reg64s) (r : Reg64) (v : BitVec 8) :
    regs.set (b8 r) v = regs.set64 r ((regs.get64 r).replaceLow v) := rfl

theorem replaceLow_setWidth (old : BitVec 64) (v : BitVec 8) :
    (old.replaceLow v).setWidth 8 = v := by
  ext i hi
  simp only [BitVec.replaceLow, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth]
  grind

theorem take8_and_31 (x : BitVec 64) : (x.take 8).toNat &&& 31 = (lo32 x).toNat % 32 := by
  rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]
  omega

theorem take8_and_63 (x : BitVec 64) : (x.take 8).toNat &&& 63 = x.toNat % 64 := by
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.take, BitVec.extractLsb'_toNat]
  omega

theorem ofInt_setWidth (m : Nat) (hm : m = 8 ∨ m = 16 ∨ m = 32) (n : Int) :
    (BitVec.ofInt 64 n).setWidth m = BitVec.ofInt m n := by
  grind

theorem zero_append_toNat {w : Nat} (a : BitVec w) : ((0 : BitVec w) ++ a).toNat = a.toNat := by
  simp [BitVec.toNat_append]

theorem udiv_lt_two_pow {w : Nat} (a b : BitVec w) : a.toNat / b.toNat < 2 ^ w :=
  Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt

theorem sshiftRight_last_eq_signExtend {w : Nat} (a : BitVec w) :
    (a.sshiftRight (w - 1) ++ a) = a.signExtend (w + w) := by
  grind

theorem sshiftRight_last_append_toInt {w : Nat} (hw : w = 32 ∨ w = 64) (a : BitVec w) :
    (a.sshiftRight (w - 1) ++ a).toInt = a.toInt := by
  rw [sshiftRight_last_eq_signExtend]
  exact BitVec.toInt_signExtend_of_le (by rcases hw with rfl | rfl <;> omega)

theorem tdiv_in_bounds {w : Nat} (hw : w = 32 ∨ w = 64) {a b : BitVec w}
    (hsd : sdivDefined a b = true) :
    ¬ (a.toInt.tdiv b.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ a.toInt.tdiv b.toInt) := by
  simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hsd
  obtain ⟨hb0, hmin⟩ := hsd
  have hmin' : a ≠ BitVec.intMin w ∨ b ≠ -1#w := by
    rwa [show BitVec.allOnes w = -1#w by rcases hw with rfl | rfl <;> decide] at hmin
  have hdiv := BitVec.toInt_sdiv_of_ne_or_ne a b hmin'
  grind

theorem ofInt_tdiv_eq_sdiv {w : Nat} (hw : w = 32 ∨ w = 64) {a b : BitVec w}
    (hsd : sdivDefined a b = true) :
    BitVec.ofInt w (a.toInt.tdiv b.toInt) = a.sdiv b := by
  simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hsd
  obtain ⟨_, hmin⟩ := hsd
  have hmin' : a ≠ BitVec.intMin w ∨ b ≠ -1#w := by
    rwa [show BitVec.allOnes w = -1#w by rcases hw with rfl | rfl <;> decide] at hmin
  rw [← BitVec.toInt_sdiv_of_ne_or_ne a b hmin', BitVec.ofInt_toInt]

theorem ofInt_tmod_eq_srem {w : Nat} (a b : BitVec w) :
    BitVec.ofInt w (a.toInt.tmod b.toInt) = a.srem b := by
  rw [← BitVec.toInt_srem a b, BitVec.ofInt_toInt]

theorem ofNat_div_eq_udiv {w : Nat} (a b : BitVec w) :
    BitVec.ofNat w (a.toNat / b.toNat) = a / b := by
  grind

theorem ofNat_mod_eq_umod {w : Nat} (a b : BitVec w) :
    BitVec.ofNat w (a.toNat % b.toNat) = a % b := by
  grind

theorem eval_bin_comm {k : Cls} {o : BinOp} (hc : isComm o = true) (x y : Val) :
    (Op.bin k o (.imm x) (.imm y)).eval = (Op.bin k o (.imm y) (.imm x)).eval := by
  cases k <;> cases o <;> (try simp [isComm] at hc) <;>
    simp only [Op.eval, Arg.val, BinOp.eval] <;> grind

theorem setWidth32_eval_w (o : BinOp) (x y : Val) :
    (Op.bin .w o (.imm ((x.setWidth 32).zeroExtend 64)) (.imm y)).eval =
      (Op.bin .w o (.imm x) (.imm y)).eval := by
  have hlo : lo32 ((x.setWidth 32).zeroExtend 64) = lo32 x := by simp only [lo32]; grind
  simp only [Op.eval, Arg.val, BinOp.eval, hlo]

theorem eval_cls_trunc (k : Cls) (o : BinOp) (x y : Val) :
    (Op.bin k o (.imm (k.trunc x)) (.imm y)).eval = (Op.bin k o (.imm x) (.imm y)).eval := by
  cases k with
  | l => rfl
  | w => exact setWidth32_eval_w o x y

/-- Negate value `x` at class `k` (`0 - x`). -/
def negVal : Cls → Val → Val
  | .l, x => -x
  | .w, x => zext32 (-lo32 x)

theorem eval_sub_zero_eq_negVal (k : Cls) (x : Val) :
    (Op.bin k .sub (.imm 0) (.imm x)).eval = some (negVal k x) := by
  cases k <;> simp [Op.eval, Arg.val, BinOp.eval, negVal, lo32]

theorem eval_add_negVal (k : Cls) (x y : Val) :
    (Op.bin k .add (.imm (negVal k y)) (.imm x)).eval =
      (Op.bin k .sub (.imm x) (.imm y)).eval := by
  cases k <;>
    simp only [Op.eval, Arg.val, BinOp.eval, negVal, Option.map_some, Option.some.injEq,
      lo32, zext32] <;> grind

theorem negVal_trunc (k : Cls) (x : Val) : negVal k (k.trunc x) = negVal k x := by
  cases k <;> simp only [negVal, Cls.trunc, lo32, zext32] <;> grind

theorem toBitVec_imm32Val_of_fits {c : Val} (h : fitsImm32 c = true) :
    (imm32Val c).toBitVec = c := by
  simpa [imm32Val, fitsImm32, Int64.toBitVec_ofBitVec, beq_iff_eq] using h

theorem toBitVec_imm32Val_truncate32 (c : Val) :
    (imm32Val c).toBitVec.truncate 32 = c.truncate 32 := by
  simp only [imm32Val, Int64.toBitVec_ofBitVec, BitVec.truncate_eq_setWidth]
  grind

theorem toBitVec_storeImmVal {sz : Sz} {c : Val} (h : sz ≠ .l ∨ fitsImm32 c = true) :
    (storeImmVal sz c).toBitVec.truncate (sz.bytes * 8) = c.truncate (sz.bytes * 8) := by
  cases sz with
  | b | h =>
    simp only [storeImmVal, Sz.bytes, Int64.toBitVec_ofBitVec, BitVec.truncate_eq_setWidth]
    grind
  | w => simpa [storeImmVal, Sz.bytes] using toBitVec_imm32Val_truncate32 c
  | l =>
    have hf : fitsImm32 c = true := h.resolve_left (fun hc => hc rfl)
    simpa [storeImmVal, Sz.bytes, BitVec.setWidth_eq] using toBitVec_imm32Val_of_fits hf

theorem leaReg_interp [Labels] (regs : Reg64s) (ra rb : Reg64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg ra), idx := some ⟨rb, .W8⟩ } regs p).zeroExtend
      64 = regs.get64 ra + regs.get64 rb := by
  simp [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, ConstExpr.interp, BitVec.signed,
    Width.bytes, Width.bits, BitVec.setWidth_eq]
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem leaImm_interp [Labels] (regs : Reg64s) (ra : Reg64) {cb : Val} (h : fitsImm32 cb = true)
    (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩
      { base := some (.reg ra), idx := none, disp := .int64 (imm32Val cb) } regs p).zeroExtend 64 =
      regs.get64 ra + cb := by
  have hc : (imm32Val cb).toBitVec = cb := toBitVec_imm32Val_of_fits h
  have hci : (imm32Val cb).toInt = cb.toInt := by rw [← Int64.toInt_toBitVec, hc]
  simp [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, ConstExpr.interp, BitVec.signed,
    hci, Width.bits, BitVec.setWidth_eq]
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

/-! ## Flags of `cmp` -/

/-- The flags after `cmp` computing `a - b` at width `n`, as Kraken's `cmp` sets them. -/
def subFlags {n : Nat} (a b : BitVec n) : StatusFlags :=
  StatusFlags.from_result (a - b)
    { cf := (a - b).unsigned != a.unsigned - b.unsigned,
      af := ((a - b).take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := (a - b).signed != a.signed - b.signed }

theorem cond_subFlags {n : Nat} (hn : n = 32 ∨ n = 64) (co : CmpOp) (x y : BitVec n) :
    (condOf co).interp (subFlags x y) = co.eval x y := by
  rcases hn with rfl | rfl <;> cases co <;>
    grind [condOf, subFlags, StatusFlags.from_result, CondCode.interp, CmpOp.eval, BitVec.unsigned,
      BitVec.signed]

/-- The flags after `cmp{k} %r10, %r11`. -/
def cmpFlags : Cls → Val → Val → StatusFlags
  | .l, a, b => subFlags a b
  | .w, a, b => subFlags (lo32 a) (lo32 b)

/-- `cmp` + `set{cc}` computes the comparison. -/
theorem eval_cmp (k : Cls) (o : CmpOp) (a b : Val) :
    (Op.cmp k o (.imm a) (.imm b)).eval = some (boolVal ((condOf o).interp (cmpFlags k a b))) := by
  have h64 := cond_subFlags (n := 64) (by simp) o a b
  have h32 := cond_subFlags (n := 32) (by simp) o (lo32 a) (lo32 b)
  cases k <;> simp only [Op.eval, Arg.val, cmpFlags, h64, h32]

theorem swapCmp_eval {n : Nat} (co : CmpOp) (a b : BitVec n) :
    (swapCmp co).eval a b = co.eval b a := by
  cases co <;> grind [swapCmp, CmpOp.eval]

/-! ## One directive -/

section
variable [Host] {E : Int64 → MachineData → Prop} {s : MachineData}

theorem wp_movD {rd rs : Reg64} :
    Program.wp [movD rd rs] (Regs s (s.regs.set64 rd (s.regs.get64 rs))) E s :=
  wp_regs fun _ _ _ _ hk => by simp only [step_simp, movD]; exact hk _ ⟨_, rfl⟩

theorem wp_moviD {rd : Reg64} {c : Val} :
    Program.wp [moviD rd c] (Regs s (s.regs.set64 rd c)) E s :=
  wp_regs fun _ _ _ _ hk => by simp only [step_simp, moviD]; exact hk _ (upd_eq rfl (by simp))

theorem wp_argTo {t : Reg64} {a : Arg Reg64} :
    Program.wp [argTo t a] (Regs s (s.regs.set64 t (argv s.regs a))) E s := by
  cases a with
  | var r => exact wp_movD
  | imm c => exact wp_moviD

theorem wp_movlD {rd rs : Reg64} :
    Program.wp [movlD rd rs] (Regs s (s.regs.set64 rd (Cls.w.trunc (s.regs.get64 rs)))) E s :=
  wp_regs fun _ _ _ _ hk => by simp only [step_simp, movlD]; exact hk _ ⟨_, rfl⟩

theorem wp_movK {k : Cls} {rd ra : Reg64} :
    Program.wp [movK k rd ra] (Regs s (s.regs.set64 rd (k.trunc (s.regs.get64 ra)))) E s := by
  cases k with
  | l => exact wp_movD
  | w => exact wp_movlD

theorem wp_extD {k : Cls} {sz : Sz} {sg : Bool} {rd r : Reg64} :
    Program.wp [extD k sz sg rd r]
      (Regs s (s.regs.set64 rd (k.trunc (sz.extend sg (s.regs.get64 r))))) E s := by
  refine wp_regs fun _ _ _ _ hk => ?_
  cases k <;> cases sz <;> cases sg <;>
    simp only [step_simp, extD, movD, movlD] <;>
    refine hk _ (upd_eq rfl ?_) <;>
    dsimp only <;>
    congr 1 <;>
    simp only [Cls.trunc, Sz.extend, lo32, zext32] <;>
    grind

theorem wp_negIns {k : Cls} {rd : Reg64} :
    Program.wp [negIns k rd] (Regs s (s.regs.set64 rd (negVal k (s.regs.get64 rd)))) E s := by
  cases k <;> refine wp_regs fun _ _ _ _ hk => ?_ <;>
    simp only [negIns, step_simp] <;> exact hk _ (upd_eq rfl rfl)

theorem wp_binIns {k : Cls} {o : BinOp} {di : Directive} {v : Val} (hb : binIns k o = some di)
    (hv : (Op.bin k o (.imm (s.regs.get64 .r11)) (.imm (s.regs.get64 .r10))).eval = some v) :
    Program.wp [di] (Regs s (s.regs.set64 .r11 v)) E s := by
  cases k <;> cases o <;> simp only [binIns, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
    refine wp_regs fun _ _ _ _ hk => ?_ <;>
    simp only [step_simp] <;>
    simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
    subst hv <;> (repeat intro _) <;> refine hk _ (upd_eq rfl ?_) <;> grind

theorem wp_binRegIns {k : Cls} {o : BinOp} {rd rs : Reg64} {di : Directive} {v : Val}
    (hb : binRegIns k o rd rs = some di)
    (hv : (Op.bin k o (.imm (s.regs.get64 rd)) (.imm (s.regs.get64 rs))).eval = some v) :
    Program.wp [di] (Regs s (s.regs.set64 rd v)) E s := by
  cases k <;> cases o <;> simp only [binRegIns, reduceCtorEq, Option.some.injEq] at hb <;>
    subst hb <;> refine wp_regs fun _ _ _ _ hk => ?_ <;>
    simp only [step_simp] <;>
    simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
    subst hv <;> (repeat intro _) <;> refine hk _ (upd_eq rfl ?_) <;> grind

theorem wp_binImmIns {k : Cls} {o : BinOp} {rd : Reg64} {cb : Val} {di : Directive} {v : Val}
    (hb : binImmIns k o rd cb = some di) (hf : k = .w ∨ fitsImm32 cb = true)
    (hv : (Op.bin k o (.imm (s.regs.get64 rd)) (.imm cb)).eval = some v) :
    Program.wp [di] (Regs s (s.regs.set64 rd v)) E s := by
  rcases hf with rfl | hfit
  · cases o <;> simp only [binImmIns, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
      refine wp_regs fun _ _ _ _ hk => ?_ <;>
      simp only [step_simp, imm32Op, toBitVec_imm32Val_truncate32] <;>
      simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
      subst hv <;> (repeat intro _) <;> refine hk _ (upd_eq rfl ?_) <;> grind
  · cases k
    · cases o <;> simp only [binImmIns, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
        refine wp_regs fun _ _ _ _ hk => ?_ <;>
        simp only [step_simp, imm32Op, toBitVec_imm32Val_truncate32] <;>
        simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
        subst hv <;> (repeat intro _) <;> refine hk _ (upd_eq rfl ?_) <;> grind
    · have hc64 : (imm32Val cb).toBitVec.truncate 64 = cb := by
        simpa [BitVec.truncate_eq_setWidth, BitVec.setWidth_eq] using toBitVec_imm32Val_of_fits hfit
      cases o <;> simp only [binImmIns, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
        refine wp_regs fun _ _ _ _ hk => ?_ <;>
        simp only [step_simp, imm32Op, hc64] <;>
        simp only [Op.eval, Arg.val, BinOp.eval, Option.some.injEq] at hv <;>
        subst hv <;> (repeat intro _) <;> refine hk _ (upd_eq rfl ?_) <;> grind

theorem wp_shiftIns {k : Cls} {o : BinOp} {di : Directive} {v : Val} (hb : shiftIns k o = some di)
    (hv : (Op.bin k o (.imm (s.regs.get64 .r11)) (.imm (s.regs.get64 .rcx))).eval = some v) :
    Program.wp [di] (Regs s (s.regs.set64 .r11 v)) E s := by
  have e : s.regs.rcx.toBitVec = s.regs.get64 .rcx := rfl
  cases k <;> cases o <;> simp only [shiftIns, reduceCtorEq, Option.some.injEq] at hb <;>
    subst hb <;> refine wp_regs fun _ _ _ _ hk => ?_ <;>
    simp only [step_simp, e, take8_and_31, take8_and_63] <;>
    simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
    subst hv <;>
    repeat' (first | split | (simp only [Effects.All]; intros))
  all_goals
    try simp only [Effects.All]
    intros
    refine hk _ (upd_eq rfl ?_)
    first | rfl | (rename_i h; simp at h; simp [h])

theorem wp_shiftImmIns {k : Cls} {o : BinOp} {r : Reg64} {c : Val} {di : Directive} {v : Val}
    (hb : shiftImmIns k o r c = some di)
    (hv : (Op.bin k o (.imm (s.regs.get64 r)) (.imm c)).eval = some v) :
    Program.wp [di] (Regs s (s.regs.set64 r v)) E s := by
  cases k <;> cases o <;> simp only [shiftImmIns, reduceCtorEq, Option.some.injEq] at hb <;>
    subst hb <;> refine wp_regs fun _ _ _ _ hk => ?_ <;>
    simp only [step_simp, Int64.toBitVec_ofBitVec, take8_and_31, take8_and_63] <;>
    simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
    subst hv <;>
    repeat' (first | split | (simp only [Effects.All]; intros))
  all_goals
    try simp only [Effects.All]
    intros
    refine hk _ (upd_eq rfl ?_)
    first | rfl | (rename_i h; simp at h; simp [h])

theorem wp_leaReg {k : Cls} {o : BinOp} {rd ra rb : Reg64} {v : Val}
    (hk : (k == .l && o == .add && decide (rb ≠ rd)) = true)
    (hv : (Op.bin k o (.imm (s.regs.get64 ra)) (.imm (s.regs.get64 rb))).eval = some v) :
    Program.wp [ins (.lea (q rd) { base := some (.reg ra), idx := some ⟨rb, .W8⟩ })]
      (Regs s (s.regs.set64 rd v)) E s := by
  obtain ⟨⟨rfl, rfl⟩, -⟩ : (k = .l ∧ o = .add) ∧ rb ≠ rd := by simpa using hk
  obtain rfl : s.regs.get64 ra + s.regs.get64 rb = v := Option.some.inj hv
  refine wp_regs fun _ _ _ _ hk => ?_
  simp only [step_simp, leaReg_interp]
  exact hk _ ⟨_, rfl⟩

theorem wp_leaImm {k : Cls} {o : BinOp} {rd ra : Reg64} {cb v : Val}
    (hk : (k == .l && o == .add) = true) (hf : k = .w ∨ fitsImm32 cb = true)
    (hv : (Op.bin k o (.imm (s.regs.get64 ra)) (.imm cb)).eval = some v) :
    Program.wp
      [ins (.lea (q rd) { base := some (.reg ra), idx := none, disp := .int64 (imm32Val cb) })]
      (Regs s (s.regs.set64 rd v)) E s := by
  obtain ⟨rfl, rfl⟩ : k = .l ∧ o = .add := by simpa using hk
  obtain rfl : s.regs.get64 ra + cb = v := Option.some.inj hv
  have hfit := hf.resolve_left (by decide)
  refine wp_regs fun _ _ _ _ hk => ?_
  simp only [step_simp, leaImm_interp _ _ hfit]
  exact hk _ ⟨_, rfl⟩

theorem wp_cmpIns {k : Cls} :
    Program.wp [cmpIns k] (Flags s (cmpFlags k (s.regs.get64 .r11) (s.regs.get64 .r10))) E s := by
  cases k <;> refine wp_flags fun _ _ _ _ hk => ?_ <;>
    simp only [step_simp, cmpIns] <;> exact hk _ rfl

theorem wp_cmpRegIns {k : Cls} {rx ry : Reg64} :
    Program.wp [cmpRegIns k rx ry]
      (Flags s (cmpFlags k (s.regs.get64 rx) (s.regs.get64 ry))) E s := by
  cases k <;> refine wp_flags fun _ _ _ _ hk => ?_ <;>
    simp only [step_simp, cmpRegIns] <;> exact hk _ rfl

theorem wp_cmpImmIns {k : Cls} {rx : Reg64} {cy : Val} (hf : k = .w ∨ fitsImm32 cy = true) :
    Program.wp [cmpImmIns k rx cy] (Flags s (cmpFlags k (s.regs.get64 rx) cy)) E s := by
  rcases hf with rfl | hfit
  · refine wp_flags fun _ _ _ _ hk => ?_
    simp only [step_simp, cmpImmIns, imm32Op, toBitVec_imm32Val_truncate32]
    exact hk _ rfl
  · cases k
    · refine wp_flags fun _ _ _ _ hk => ?_
      simp only [step_simp, cmpImmIns, imm32Op, toBitVec_imm32Val_truncate32]
      exact hk _ rfl
    · have hc64 : (imm32Val cy).toBitVec.truncate 64 = cy := by
        simpa [BitVec.truncate_eq_setWidth, BitVec.setWidth_eq] using toBitVec_imm32Val_of_fits hfit
      refine wp_flags fun _ _ _ _ hk => ?_
      simp only [step_simp, cmpImmIns, imm32Op, hc64]
      exact hk _ rfl

theorem wp_setccD {cc : CondCode} :
    Program.wp [setccD cc]
      (Regs s (s.regs.set64 .r11
        ((s.regs.get64 .r11).replaceLow (BitVec.ofNat Width.W8.bits (cc.interp s.status).toNat))))
      E s :=
  wp_regs fun _ _ _ _ hk => by simp only [step_simp, setccD, set_b8]; exact hk _ (upd_eq rfl rfl)

theorem wp_movzbD {rd : Reg64} :
    Program.wp [movzbD rd]
      (Regs s (s.regs.set64 rd (zext32 (((s.regs.get64 .r11).setWidth 8).zeroExtend 32)))) E s :=
  wp_regs fun _ _ _ _ hk => by simp only [step_simp, movzbD]; exact hk _ ⟨_, rfl⟩

theorem wp_sar63D :
    Program.wp [ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63)))]
      (Regs s (s.regs.set64 .rdx ((s.regs.get64 .rdx).sshiftRight 63))) E s := by
  refine wp_regs fun _ _ _ _ hk => ?_
  simp only [step_simp, BitVec.take]
  change (undefined fun _ => undefined fun _ => _).All _
  intro _ _
  exact hk _ ⟨_, rfl⟩

theorem wp_sar31D :
    Program.wp [ins32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31)))]
      (Regs s (s.regs.set64 .rdx (zext32 ((lo32 (s.regs.get64 .rdx)).sshiftRight 31)))) E s := by
  refine wp_regs fun _ _ _ _ hk => ?_
  simp only [step_simp, BitVec.take]
  change (undefined fun _ => undefined fun _ => _).All _
  intro _ _
  exact hk _ ⟨_, rfl⟩

theorem wp_udiv64D (rdx0 : s.regs.get64 .rdx = 0) (hb0 : s.regs.get64 .r11 ≠ 0) :
    Program.wp [ins (.div (.reg (q .r11)))]
      (Regs s ((s.regs.set64 .rax (s.regs.get64 .rax / s.regs.get64 .r11)).set64 .rdx
        (s.regs.get64 .rax % s.regs.get64 .r11))) E s := by
  refine wp_regs fun _ _ _ _ hk => ?_
  have hlt := udiv_lt_two_pow (s.regs.get64 .rax) (s.regs.get64 .r11)
  have hw : (Width.W64 == Width.W8) = false := rfl
  simp only [step_simp, hw, Bool.false_eq_true, ite_false, rdx0, zero_append_toNat, Width.bits,
    ofNat_div_eq_udiv, ofNat_mod_eq_umod]
  have hcond : ((s.regs.get64 .r11 == 0) ||
      decide (2 ^ 64 ≤ (s.regs.get64 .rax).toNat / (s.regs.get64 .r11).toNat)) = false := by grind
  simp only [hcond, Bool.false_eq_true, ite_false, Effects.All]
  intro _
  exact hk _ ⟨_, rfl⟩

theorem wp_udiv32D (rdx0 : lo32 (s.regs.get64 .rdx) = 0) (hb0 : lo32 (s.regs.get64 .r11) ≠ 0) :
    Program.wp [ins32 (.div (.reg (d .r11)))]
      (Regs s ((s.regs.set64 .rax
        (zext32 (lo32 (s.regs.get64 .rax) / lo32 (s.regs.get64 .r11)))).set64 .rdx
        (zext32 (lo32 (s.regs.get64 .rax) % lo32 (s.regs.get64 .r11))))) E s := by
  refine wp_regs fun _ _ _ _ hk => ?_
  have hlt := udiv_lt_two_pow (lo32 (s.regs.get64 .rax)) (lo32 (s.regs.get64 .r11))
  have hw : (Width.W32 == Width.W8) = false := rfl
  simp only [step_simp, hw, Bool.false_eq_true, ite_false, rdx0, zero_append_toNat, Width.bits,
    ofNat_div_eq_udiv, ofNat_mod_eq_umod]
  have hcond : ((lo32 (s.regs.get64 .r11) == 0) ||
      decide (2 ^ 32 ≤ (lo32 (s.regs.get64 .rax)).toNat / (lo32 (s.regs.get64 .r11)).toNat)) =
      false := by grind
  simp only [hcond, Bool.false_eq_true, ite_false, Effects.All]
  intro _
  exact hk _ ⟨_, rfl⟩

theorem wp_idiv64D (hrdx : s.regs.get64 .rdx = (s.regs.get64 .rax).sshiftRight 63)
    (hsd : sdivDefined (s.regs.get64 .rax) (s.regs.get64 .r11) = true) :
    Program.wp [ins (.idiv (.reg (q .r11)))]
      (Regs s ((s.regs.set64 .rax ((s.regs.get64 .rax).sdiv (s.regs.get64 .r11))).set64 .rdx
        ((s.regs.get64 .rax).srem (s.regs.get64 .r11)))) E s := by
  refine wp_regs fun _ _ _ _ hk => ?_
  have happ := sshiftRight_last_append_toInt (w := 64) (by simp) (s.regs.get64 .rax)
  have hbnd := tdiv_in_bounds (w := 64) (by simp) hsd
  have hb0 : s.regs.get64 .r11 ≠ 0 := by
    simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne] at hsd; exact hsd.1
  have hw : (Width.W64 == Width.W8) = false := rfl
  simp only [step_simp, hw, Bool.false_eq_true, ite_false, hrdx, happ, Width.bits,
    ofInt_tdiv_eq_sdiv (by simp) hsd, ofInt_tmod_eq_srem]
  have hcond : (((s.regs.get64 .r11 == 0) ||
      decide ((s.regs.get64 .rax).toInt.tdiv (s.regs.get64 .r11).toInt < -2 ^ 63)) ||
      decide (2 ^ 63 ≤ (s.regs.get64 .rax).toInt.tdiv (s.regs.get64 .r11).toInt)) = false := by
    grind
  simp only [hcond, Bool.false_eq_true, ite_false, Effects.All]
  intro _
  exact hk _ ⟨_, rfl⟩

theorem wp_idiv32D (hrdx : lo32 (s.regs.get64 .rdx) = (lo32 (s.regs.get64 .rax)).sshiftRight 31)
    (hsd : sdivDefined (lo32 (s.regs.get64 .rax)) (lo32 (s.regs.get64 .r11)) = true) :
    Program.wp [ins32 (.idiv (.reg (d .r11)))]
      (Regs s ((s.regs.set64 .rax
        (zext32 ((lo32 (s.regs.get64 .rax)).sdiv (lo32 (s.regs.get64 .r11))))).set64 .rdx
        (zext32 ((lo32 (s.regs.get64 .rax)).srem (lo32 (s.regs.get64 .r11)))))) E s := by
  refine wp_regs fun _ _ _ _ hk => ?_
  have happ := sshiftRight_last_append_toInt (w := 32) (by simp) (lo32 (s.regs.get64 .rax))
  have hbnd := tdiv_in_bounds (w := 32) (by simp) hsd
  have hb0 : lo32 (s.regs.get64 .r11) ≠ 0 := by
    simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne] at hsd; exact hsd.1
  have hw : (Width.W32 == Width.W8) = false := rfl
  simp only [step_simp, hw, Bool.false_eq_true, ite_false, hrdx, happ, Width.bits,
    ofInt_tdiv_eq_sdiv (by simp) hsd, ofInt_tmod_eq_srem]
  have hcond : (((lo32 (s.regs.get64 .r11) == 0) ||
      decide ((lo32 (s.regs.get64 .rax)).toInt.tdiv (lo32 (s.regs.get64 .r11)).toInt < -2 ^ 31)) ||
      decide (2 ^ 31 ≤ (lo32 (s.regs.get64 .rax)).toInt.tdiv (lo32 (s.regs.get64 .r11)).toInt)) =
      false := by
    grind
  simp only [hcond, Bool.false_eq_true, ite_false, Effects.All]
  intro _
  exact hk _ ⟨_, rfl⟩

theorem wp_loadlD {rd ra : Reg64} {v : Int}
    (hload : Mem.loadInt s.dmem (s.regs.get64 ra) 8 = some v) :
    Program.wp [ins (.mov (.reg (q rd)) (.mem (atReg ra)))]
      (Regs s (s.regs.set64 rd (BitVec.ofInt 64 v))) E s := by
  refine wp_regs fun _ _ _ _ hk => ?_
  simp only [step_simp, MachineData.load, Effects.All_require_read_access, Width.bytes, hload]
  exact hk _ ⟨_, rfl⟩

theorem wp_storelD {rv ra : Reg64} {v : Int}
    (hload : Mem.loadInt s.dmem (s.regs.get64 ra) 8 = some v) :
    Program.wp [storelD rv ra]
      (MemUpd s (Mem.storeInt s.dmem (s.regs.get64 ra) 8 (s.regs.get64 rv).toInt)) E s := by
  refine wp_mem fun _ _ _ _ hk => ?_
  simp only [step_simp, storelD, MachineData.store, Effects.All_require_write_access, Width.bytes,
    hload]
  exact hk _ rfl

theorem wp_storeIns {sz : Sz} {ra : Reg64} {n : Int}
    (hload : Mem.loadInt s.dmem (s.regs.get64 ra) sz.bytes = some n) :
    Program.wp [storeIns sz ra]
      (MemUpd s (storeMem s.dmem sz (s.regs.get64 ra) (s.regs.get64 .r11))) E s := by
  cases sz
  case l => exact wp_storelD hload
  all_goals
    simp only [Sz.bytes] at hload
    refine wp_mem fun _ _ _ _ hk => ?_
    simp only [step_simp, storeIns, MachineData.store, Effects.All_require_write_access,
      Width.bytes, hload]
    exact hk _ rfl

theorem wp_storeRegIns {sz : Sz} {rv ra : Reg64} {n : Int}
    (hload : Mem.loadInt s.dmem (s.regs.get64 ra) sz.bytes = some n) :
    Program.wp [storeRegIns sz rv ra]
      (MemUpd s (storeMem s.dmem sz (s.regs.get64 ra) (s.regs.get64 rv))) E s := by
  cases sz
  case l => exact wp_storelD hload
  all_goals
    simp only [Sz.bytes] at hload
    refine wp_mem fun _ _ _ _ hk => ?_
    simp only [step_simp, storeRegIns, MachineData.store, Effects.All_require_write_access,
      Width.bytes, hload]
    exact hk _ rfl

theorem wp_storeImmIns {sz : Sz} {cx : Val} {ra : Reg64}
    (hf : sz ≠ .l ∨ fitsImm32 cx = true) {n : Int}
    (hload : Mem.loadInt s.dmem (s.regs.get64 ra) sz.bytes = some n) :
    Program.wp [storeImmIns sz cx ra] (MemUpd s (storeMem s.dmem sz (s.regs.get64 ra) cx)) E s := by
  have htr := toBitVec_storeImmVal hf
  cases sz <;> simp only [Sz.bytes] at hload htr ⊢ <;>
    (refine wp_mem fun _ _ _ _ hk => ?_;
     simp only [step_simp, storeImmIns, htr, MachineData.store, Effects.All_require_write_access,
       Width.bytes, hload];
     exact hk _ rfl)

/-! ## Snippets -/

theorem wp_setcc_movzb {cc : CondCode} {rd : Reg64} :
    Program.wp [setccD cc, movzbD rd] (fun s' => s'.regs.get64 rd = boolVal (cc.interp s.status) ∧
      (∀ r, r ≠ rd → r ≠ .r11 → s'.regs.get64 r = s.regs.get64 r) ∧ s'.dmem = s.dmem) E s := by
  refine wp_setccD.cons fun s1 ⟨hs1, hm1⟩ => wp_movzbD.mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_, ?_⟩
  · rw [hs2, Reg64s.get64_set64_same, hs1, Reg64s.get64_set64_same, replaceLow_setWidth]
    cases cc.interp s.status <;> rfl
  · grind
  · grind

/-- One directive that sets `rd` to `v`. -/
theorem wp_result {d : Directive} {rd : Reg64} {v : Val}
    (h : Program.wp [d] (Regs s (s.regs.set64 rd v)) E s) : Program.wp [d] (Result s rd v) E s := by
  refine h.mono fun s1 ⟨hs1, hm1⟩ => ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_binFallback {kk : Cls} {oo : BinOp} {a b : Arg Reg64} {rd : Reg64} {i : Directive}
    {v : Val} (hb : binIns kk oo = some i) (hbv : Reg64.r11 ∉ b.vars)
    (hv : (Op.bin kk oo (.imm (argv s.regs a)) (.imm (argv s.regs b))).eval = some v) :
    Program.wp [argTo .r11 a, argTo .r10 b, i, movD rd .r11] (Result s rd v) E s := by
  refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine wp_argTo.cons fun s2 ⟨hs2, hm2⟩ => ?_
  refine (wp_binIns hb (v := v) ?_).cons fun s3 ⟨hs3, hm3⟩ => ?_
  · grind [argv_set64]
  refine wp_movD.cons fun s4 ⟨hs4, hm4⟩ => Program.wp_nil ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_cmp {kk : Cls} {cc : CondCode} {x y : Arg Reg64} {rd : Reg64} (hy : Reg64.r11 ∉ y.vars) :
    Program.wp [argTo .r11 x, argTo .r10 y, cmpIns kk, setccD cc, movzbD rd]
      (Result s rd (boolVal (cc.interp (cmpFlags kk (argv s.regs x) (argv s.regs y))))) E s := by
  refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine wp_argTo.cons fun s2 ⟨hs2, hm2⟩ => ?_
  refine wp_cmpIns.cons fun s3 ⟨hs3, hm3, hf3⟩ => ?_
  refine wp_setcc_movzb.mono fun s4 ⟨hv4, hfr4, hm4⟩ => ⟨?_, ?_, ?_⟩ <;> grind [argv_set64]

theorem wp_shift {kk : Cls} {oo : BinOp} {i : Directive} {a b : Arg Reg64} {rd : Reg64} {v : Val}
    (hsh : shiftIns kk oo = some i) (hb : Reg64.r10 ∉ b.vars ∧ Reg64.r11 ∉ b.vars)
    (hv : (Op.bin kk oo (.imm (argv s.regs a)) (.imm (argv s.regs b))).eval = some v) :
    Program.wp [argTo .r11 a, movD .r10 .rcx, argTo .rcx b, i, movD .rcx .r10, movD rd .r11]
      (Result s rd v) E s := by
  refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine wp_movD.cons fun s2 ⟨hs2, hm2⟩ => ?_
  refine wp_argTo.cons fun s3 ⟨hs3, hm3⟩ => ?_
  refine (wp_shiftIns hsh (v := v) ?_).cons fun s4 ⟨hs4, hm4⟩ => ?_
  · grind [argv_set64]
  refine wp_movD.cons fun s5 ⟨hs5, hm5⟩ => ?_
  refine wp_movD.cons fun s6 ⟨hs6, hm6⟩ => Program.wp_nil ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_shiftImm {kk : Cls} {oo : BinOp} {a : Arg Reg64} {c0 : Val} {rd : Reg64} {i : Directive}
    {v : Val} (hsh : shiftImmIns kk oo rd c0 = some i)
    (hv : (Op.bin kk oo (.imm (argv s.regs a)) (.imm c0)).eval = some v) :
    Program.wp [argTo rd a, i] (Result s rd v) E s := by
  refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine (wp_shiftImmIns hsh (v := v) ?_).mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_cmpReg {kk : Cls} {cc : CondCode} {rx ry rd : Reg64} :
    Program.wp [cmpRegIns kk rx ry, setccD cc, movzbD rd]
      (Result s rd (boolVal (cc.interp (cmpFlags kk (s.regs.get64 rx) (s.regs.get64 ry)))))
      E s := by
  refine wp_cmpRegIns.cons fun s1 ⟨hs1, hm1, hf1⟩ => ?_
  refine wp_setcc_movzb.mono fun s2 ⟨hv2, hfr2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_cmpImm {kk : Cls} {cc : CondCode} {rx rd : Reg64} {cy : Val}
    (hf : kk = .w ∨ fitsImm32 cy = true) :
    Program.wp [cmpImmIns kk rx cy, setccD cc, movzbD rd]
      (Result s rd (boolVal (cc.interp (cmpFlags kk (s.regs.get64 rx) cy)))) E s := by
  refine (wp_cmpImmIns hf).cons fun s1 ⟨hs1, hm1, hf1⟩ => ?_
  refine wp_setcc_movzb.mono fun s2 ⟨hv2, hfr2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_cmpRegImm {kk : Cls} {cc : CondCode} {rx rd : Reg64} {cy : Val} (hrx : rx ≠ .r10) :
    Program.wp [moviD .r10 cy, cmpRegIns kk rx .r10, setccD cc, movzbD rd]
      (Result s rd (boolVal (cc.interp (cmpFlags kk (s.regs.get64 rx) cy)))) E s := by
  refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine wp_cmpReg.mono fun s2 ⟨hv2, hfr2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_cmpImmReg {kk : Cls} {cc : CondCode} {ry rd : Reg64} {cx : Val} (hry : ry ≠ .r10) :
    Program.wp [moviD .r10 cx, cmpRegIns kk .r10 ry, setccD cc, movzbD rd]
      (Result s rd (boolVal (cc.interp (cmpFlags kk cx (s.regs.get64 ry))))) E s := by
  refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine wp_cmpReg.mono fun s2 ⟨hv2, hfr2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_movK_binImm {kk : Cls} {oo : BinOp} {rd ra : Reg64} {cb : Val} {i : Directive} {v : Val}
    (hb : binImmIns kk oo rd cb = some i) (hf : kk = .w ∨ fitsImm32 cb = true)
    (hv : (Op.bin kk oo (.imm (s.regs.get64 ra)) (.imm cb)).eval = some v) :
    Program.wp [movK kk rd ra, i] (Result s rd v) E s := by
  refine wp_movK.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine (wp_binImmIns hb hf (v := v) ?_).mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;>
    grind [eval_cls_trunc]

theorem wp_movK_binReg {kk : Cls} {oo : BinOp} {rd ra rb : Reg64} {i : Directive} {v : Val}
    (hb : binRegIns kk oo rd rb = some i) (hne : rb ≠ rd)
    (hv : (Op.bin kk oo (.imm (s.regs.get64 ra)) (.imm (s.regs.get64 rb))).eval = some v) :
    Program.wp [movK kk rd ra, i] (Result s rd v) E s := by
  refine wp_movK.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine (wp_binRegIns hb (v := v) ?_).mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;>
    grind [eval_cls_trunc]

theorem wp_movK_neg {kk : Cls} {oo : BinOp} {rd rb : Reg64} {ca v : Val}
    (hsub : (oo == .sub && ca == 0) = true)
    (hv : (Op.bin kk oo (.imm ca) (.imm (s.regs.get64 rb))).eval = some v) :
    Program.wp [movK kk rd rb, negIns kk rd] (Result s rd v) E s := by
  obtain ⟨rfl, rfl⟩ : oo = .sub ∧ ca = 0 := by simpa using hsub
  obtain rfl : negVal kk (s.regs.get64 rb) = v :=
    Option.some.inj ((eval_sub_zero_eq_negVal kk _).symm.trans hv)
  refine wp_movK.cons fun s1 ⟨hs1, hm1⟩ => wp_negIns.mono fun s2 ⟨hs2, hm2⟩ =>
    ⟨?_, ?_, ?_⟩ <;> grind [negVal_trunc]

theorem wp_neg_imm {kk : Cls} {oo : BinOp} {rd : Reg64} {ca v : Val}
    (hsub : (oo == .sub && ca == 0) = true)
    (hv : (Op.bin kk oo (.imm ca) (.imm (s.regs.get64 rd))).eval = some v) :
    Program.wp [negIns kk rd] (Result s rd v) E s := by
  obtain ⟨rfl, rfl⟩ : oo = .sub ∧ ca = 0 := by simpa using hsub
  obtain rfl : negVal kk (s.regs.get64 rd) = v :=
    Option.some.inj ((eval_sub_zero_eq_negVal kk _).symm.trans hv)
  exact wp_result wp_negIns

theorem wp_neg_addReg {kk : Cls} {oo : BinOp} {rd ra rb : Reg64} {i : Directive} {v : Val}
    (hsub : (oo == .sub && decide (rb = rd)) = true) (hra : ¬ ra = rd)
    (hb : binRegIns kk .add rd ra = some i)
    (hv : (Op.bin kk oo (.imm (s.regs.get64 ra)) (.imm (s.regs.get64 rb))).eval = some v) :
    Program.wp [negIns kk rd, i] (Result s rd v) E s := by
  obtain ⟨rfl, rfl⟩ : oo = .sub ∧ rb = rd := by simpa using hsub
  refine wp_negIns.cons fun s1 ⟨hs1, hm1⟩ => ?_
  refine (wp_binRegIns hb (v := v) ?_).mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;>
    grind [eval_add_negVal]

theorem wp_divCore {kk : Cls} {oo : BinOp} {core : List Directive} {res : Reg64} {v : Val}
    (hd : divCore kk oo = some (core, res))
    (hv : (Op.bin kk oo (.imm (s.regs.get64 .rax)) (.imm (s.regs.get64 .r11))).eval = some v) :
    Program.wp core (fun s' => s'.regs.get64 res = v ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s'.regs.get64 r = s.regs.get64 r) ∧ s'.dmem = s.dmem) E s := by
  cases kk <;> cases oo <;>
    simp only [divCore, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hd <;>
    obtain ⟨rfl, rfl⟩ := hd <;> simp only [Op.eval, Arg.val, BinOp.eval] at hv
  case w.div | w.rem =>
    refine wp_movlD.cons fun s1 ⟨hs1, hm1⟩ => ?_
    refine wp_sar31D.cons fun s2 ⟨hs2, hm2⟩ => ?_
    refine (wp_idiv32D ?_ ?_).mono fun s3 ⟨hs3, hm3⟩ => ⟨?_, ?_, ?_⟩ <;> grind [Cls.trunc]
  case l.div | l.rem =>
    refine wp_movD.cons fun s1 ⟨hs1, hm1⟩ => ?_
    refine wp_sar63D.cons fun s2 ⟨hs2, hm2⟩ => ?_
    refine (wp_idiv64D ?_ ?_).mono fun s3 ⟨hs3, hm3⟩ => ⟨?_, ?_, ?_⟩ <;> grind
  case w.udiv | w.urem =>
    refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ => ?_
    refine (wp_udiv32D ?_ ?_).mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;> grind
  case l.udiv | l.urem =>
    refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ => ?_
    refine (wp_udiv64D ?_ ?_).mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;> grind

theorem wp_divSeq {kk : Cls} {oo : BinOp} {core c : List Directive} {res rd : Reg64}
    {a b : Arg Reg64} {v : Val} (hd : divCore kk oo = some (core, res))
    (hseq : divSeq rd core res a b = some c) (hb : Reg64.r10 ∉ b.vars)
    (hv : (Op.bin kk oo (.imm (argv s.regs a)) (.imm (argv s.regs b))).eval = some v) :
    Program.wp c (Result s rd v) E s := by
  simp only [divSeq] at hseq
  repeat' split at hseq
  all_goals cases hseq
  · refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => ?_
    refine wp_argTo.cons fun s2 ⟨hs2, hm2⟩ => ?_
    refine wp_movD.cons fun s3 ⟨hs3, hm3⟩ => ?_
    refine wp_movD.cons fun s4 ⟨hs4, hm4⟩ => ?_
    refine (wp_divCore hd (v := v) ?_).append fun s5 ⟨hv5, hfr5, hm5⟩ => ?_
    · grind [argv_set64]
    refine wp_movD.cons fun s6 ⟨hs6, hm6⟩ => ?_
    refine wp_movD.cons fun s7 ⟨hs7, hm7⟩ => Program.wp_nil ⟨?_, ?_, ?_⟩ <;> grind
  · refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => ?_
    refine wp_argTo.cons fun s2 ⟨hs2, hm2⟩ => ?_
    refine wp_movD.cons fun s3 ⟨hs3, hm3⟩ => ?_
    refine wp_movD.cons fun s4 ⟨hs4, hm4⟩ => ?_
    refine wp_movD.cons fun s5 ⟨hs5, hm5⟩ => ?_
    refine (wp_divCore hd (v := v) ?_).append fun s6 ⟨hv6, hfr6, hm6⟩ => ?_
    · grind [argv_set64]
    refine wp_movD.cons fun s7 ⟨hs7, hm7⟩ => ?_
    refine wp_movD.cons fun s8 ⟨hs8, hm8⟩ => Program.wp_nil ⟨?_, ?_, ?_⟩ <;> grind
  · refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => ?_
    refine wp_argTo.cons fun s2 ⟨hs2, hm2⟩ => ?_
    refine wp_movD.cons fun s3 ⟨hs3, hm3⟩ => ?_
    refine wp_movD.cons fun s4 ⟨hs4, hm4⟩ => ?_
    refine wp_movD.cons fun s5 ⟨hs5, hm5⟩ => ?_
    refine (wp_divCore hd (v := v) ?_).append fun s6 ⟨hv6, hfr6, hm6⟩ => ?_
    · grind [argv_set64]
    refine wp_movD.cons fun s7 ⟨hs7, hm7⟩ => ?_
    refine wp_movD.cons fun s8 ⟨hs8, hm8⟩ => ?_
    refine wp_movD.cons fun s9 ⟨hs9, hm9⟩ => ?_
    refine wp_movD.cons fun s10 ⟨hs10, hm10⟩ => Program.wp_nil ⟨?_, ?_, ?_⟩ <;>
      grind (gen := 12)

/-! ## Dispatch over `op`, `load`, `store`, and `jnzCmp` -/

omit [Host] in
theorem eval_bin_argv {k : Cls} {o : BinOp} {a b : Arg Reg64} {regs : Reg64s} {v : Val}
    (h : ((Op.bin k o a b).map regs.get64).eval = some v) :
    (Op.bin k o (.imm (argv regs a)) (.imm (argv regs b))).eval = some v :=
  (eval_bin_imm k o (a.map regs.get64) (b.map regs.get64)).symm.trans h

omit [Host] in
theorem eval_cmp_argv {k : Cls} {o : CmpOp} {a b : Arg Reg64} {regs : Reg64s} {v : Val}
    (h : ((Op.cmp k o a b).map regs.get64).eval = some v) :
    v = boolVal ((condOf o).interp (cmpFlags k (argv regs a) (argv regs b))) := by
  have h' : (Op.cmp k o (.imm (argv regs a)) (.imm (argv regs b))).eval = some v := by
    rw [← h]; cases k <;> rfl
  exact Option.some.inj (h'.symm.trans (eval_cmp k o _ _))

omit [Host] in
theorem eval_cmp_swap_argv {k : Cls} {o : CmpOp} {a b : Arg Reg64} {regs : Reg64s} {v : Val}
    (h : ((Op.cmp k o a b).map regs.get64).eval = some v) :
    v = boolVal ((condOf (swapCmp o)).interp (cmpFlags k (argv regs b) (argv regs a))) := by
  have h' : (Op.cmp k (swapCmp o) (.imm (argv regs b)) (.imm (argv regs a))).eval = some v := by
    rw [← h]; cases k <;> simp [Op.map, Op.eval, Arg.val, argv, swapCmp_eval]
  exact Option.some.inj (h'.symm.trans (eval_cmp k (swapCmp o) _ _))

omit [Host] in
theorem fits_or {k : Cls} {c : Val} (h : (k == .w || fitsImm32 c) = true) :
    k = .w ∨ fitsImm32 c = true := by
  simpa using h

omit [Host] in
theorem store_fits {sz : Sz} {c : Val} (h : (sz != .l || fitsImm32 c) = true) :
    sz ≠ .l ∨ fitsImm32 c = true := by
  simpa using h

omit [Host] in
theorem comm_fits {k : Cls} {o : BinOp} {c : Val}
    (h : (isComm o && (k == .w || fitsImm32 c)) = true) :
    isComm o = true ∧ (k = .w ∨ fitsImm32 c = true) := by
  simpa using h

omit [Host] in
theorem bin_vars {k : Cls} {o : BinOp} {a b : Arg Reg64}
    (hvars : ∀ r, r ∈ (Op.bin k o a b).vars → r ∉ scratchRegs) :
    Reg64.r10 ∉ b.vars ∧ Reg64.r11 ∉ b.vars :=
  ⟨fun h => hvars _ (List.mem_append_right _ h) (by simp),
    fun h => hvars _ (List.mem_append_right _ h) (by simp)⟩

omit [Host] in
theorem ne_r10 {r : Reg64} {l : List Reg64} (h : ∀ r, r ∈ l → r ∉ scratchRegs) (hr : r ∈ l) :
    r ≠ .r10 :=
  fun e => h r hr (by simp [e])

theorem wp_op {o : Op Reg64} {rd : Reg64} {c : List Directive} {v : Val}
    (hop : op o rd = some c) (hvars : ∀ r, r ∈ o.vars → r ∉ scratchRegs)
    (hv : (o.map s.regs.get64).eval = some v) :
    Program.wp c (Result s rd v) E s := by
  revert hop
  fun_cases op o rd
  all_goals intro hop
  all_goals repeat' (first | contradiction | split at hop)
  all_goals first | cases hop | obtain ⟨i, hb, rfl⟩ := Option.map_eq_some_iff.mp hop | skip
  all_goals try replace hv := eval_bin_argv hv
  · exact wp_result (wp_shiftImmIns ‹_› hv)
  · exact wp_shiftImm ‹_› hv
  · exact wp_shiftImm ‹_› hv
  · exact wp_shift ‹_› (bin_vars hvars) hv
  · exact wp_shift ‹_› (bin_vars hvars) hv
  · exact wp_divSeq ‹_› hop (bin_vars hvars).1 hv
  · exact wp_result (wp_binRegIns hb hv)
  · obtain ⟨hc, rfl⟩ := ‹_ ∧ _›
    exact wp_result (wp_binRegIns hb ((eval_bin_comm hc _ _).trans hv))
  · exact wp_neg_addReg ‹_› ‹_› hb hv
  · exact wp_result (wp_leaReg ‹_› hv)
  · exact wp_movK_binReg hb ‹_› hv
  · exact wp_binFallback hb (bin_vars hvars).2 hv
  · exact wp_result (wp_binImmIns hb (fits_or ‹_›) hv)
  · exact wp_result (wp_leaImm ‹_› (fits_or ‹_›) hv)
  · exact wp_movK_binImm hb (fits_or ‹_›) hv
  · exact wp_binFallback hb (bin_vars hvars).2 hv
  · exact wp_neg_imm ‹_› hv
  · exact wp_movK_neg ‹_› hv
  · obtain ⟨hc, hf⟩ := comm_fits (by assumption)
    exact wp_result (wp_binImmIns hb hf ((eval_bin_comm hc _ _).trans hv))
  · obtain ⟨hc, hf⟩ := comm_fits (by assumption)
    exact wp_result (wp_leaImm ‹_› hf ((eval_bin_comm hc _ _).trans hv))
  · obtain ⟨hc, hf⟩ := comm_fits (by assumption)
    exact wp_movK_binImm hb hf ((eval_bin_comm hc _ _).trans hv)
  · exact wp_binFallback hb (bin_vars hvars).2 hv
  · exact wp_binFallback hb (bin_vars hvars).2 hv
  · obtain rfl := eval_cmp_argv hv; exact wp_cmpReg
  · obtain rfl := eval_cmp_argv hv; exact wp_cmpImm (fits_or ‹_›)
  · obtain rfl := eval_cmp_argv hv
    exact wp_cmpRegImm (ne_r10 hvars (by simp [Op.vars, Arg.vars]))
  · obtain rfl := eval_cmp_swap_argv hv; exact wp_cmpImm (fits_or ‹_›)
  · obtain rfl := eval_cmp_argv hv
    exact wp_cmpImmReg (ne_r10 hvars (by simp [Op.vars, Arg.vars]))
  · obtain rfl := eval_cmp_argv hv
    exact wp_cmp fun h => hvars _ (List.mem_append_right _ h) (by simp)
  all_goals cases hv
  · exact wp_result wp_extD
  · exact wp_result wp_moviD
  · exact wp_result wp_argTo
  · exact wp_result wp_movlD
  · exact wp_result wp_moviD

theorem eventually_op {k : Nat} {o : Op Reg64} {rd : Reg64} {c : List Directive} {v : Val}
    {post : MachineState → Prop}
    (hop : op o rd = some c) (hc : c.IsInfixAt Host.prog k)
    (hvars : ∀ r, r ∈ o.vars → r ∉ scratchRegs)
    (hv : (o.map s.regs.get64).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + c.length) s' post) :
    Run k s post :=
  (wp_op (E := fun _ _ => False) hop hvars hv).eventually hc
    (fun s' ⟨h1, h2, h3⟩ => hk s' h1 h2 h3) (fun _ _ h => h.elim)

theorem wp_loadIns {cl : Cls} {sz : Sz} {sg : Bool} {rd ra : Reg64} {n : Int}
    (hload : Mem.loadInt s.dmem (s.regs.get64 ra) sz.bytes = some n) :
    Program.wp (loadIns cl sz sg rd ra)
      (Regs s (s.regs.set64 rd (cl.trunc (sz.extend sg (BitVec.ofInt 64 n))))) E s := by
  cases cl <;> cases sz <;> cases sg
  case w.l.false | w.l.true =>
    refine (wp_loadlD hload).cons fun s1 ⟨hs1, hm1⟩ => wp_movlD.mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_⟩
    · rw [hs2, hs1, Reg64s.get64_set64_same, Reg64s.set64_set64_same]; rfl
    · rw [hm2, hm1]
  all_goals
    simp only [Sz.bytes] at hload
    refine wp_regs fun _ _ _ _ hk => ?_
    simp only [step_simp, MachineData.load, Effects.All_require_read_access, Width.bytes, hload]
    refine hk _ (upd_eq rfl ?_)
    dsimp only
    congr 1
    try simp only [Cls.trunc, Sz.extend, lo32, zext32, ofInt_setWidth 8 (by simp),
      ofInt_setWidth 16 (by simp), ofInt_setWidth 32 (by simp)]
    try grind

theorem wp_load {cl : Cls} {sz : Sz} {sg : Bool} {rd : Reg64} {a : Arg Reg64}
    {c : List Directive} {v : Val}
    (hop : load cl sz sg rd a = some c)
    (hv : loadVal s.dmem cl sz sg (argv s.regs a) = some v) :
    Program.wp c (Result s rd v) E s := by
  simp only [load, Option.some.injEq] at hop; subst hop
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hv
  cases a with
  | var ra =>
    simp only [addrIn, List.nil_append]
    refine (wp_loadIns hn).mono fun s1 ⟨hs1, hm1⟩ => ⟨?_, ?_, ?_⟩ <;> grind
  | imm c0 =>
    simp only [addrIn, List.singleton_append]
    refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ =>
      (wp_loadIns (n := n) ?_).mono fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_, ?_⟩ <;>
      grind [Arg.map, Arg.val]

theorem eventually_load {k : Nat} {cl : Cls} {sz : Sz} {sg : Bool} {rd : Reg64} {a : Arg Reg64}
    {c : List Directive} {v : Val} {post : MachineState → Prop}
    (hop : load cl sz sg rd a = some c) (hc : c.IsInfixAt Host.prog k)
    (hv : loadVal s.dmem cl sz sg (argv s.regs a) = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + c.length) s' post) :
    Run k s post :=
  (wp_load (E := fun _ _ => False) hop hv).eventually hc
    (fun s' ⟨h1, h2, h3⟩ => hk s' h1 h2 h3) (fun _ _ h => h.elim)

theorem wp_store {sz : Sz} {x a : Arg Reg64} {c : List Directive}
    (hop : store sz x a = some c)
    (hvars : ∀ r, r ∈ x.vars ++ a.vars → r ∉ scratchRegs)
    (hok : storeOk s.dmem sz (argv s.regs a)) :
    Program.wp c (fun s' => (∀ r, r ∉ scratchRegs → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = storeMem s.dmem sz (argv s.regs a) (argv s.regs x)) E s := by
  obtain ⟨n, hn⟩ := hok
  have h10 : ∀ r, r ∈ x.vars ++ a.vars → r ≠ .r10 ∧ r ≠ .r11 := fun r hr =>
    ne_of_not_mem_scratch (hvars r hr)
  revert hop
  fun_cases store sz x a <;> intro hop <;> cases hop <;> cases a <;>
    simp only [addrIn, List.nil_append, List.singleton_append]
  · refine (wp_storeRegIns hn).mono fun s1 ⟨hs1, hm1⟩ => ⟨?_, ?_⟩ <;> grind [Arg.map, Arg.val]
  · refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ => (wp_storeRegIns (n := n) ?_).mono
      fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_⟩ <;> grind [Arg.vars, Arg.map, Arg.val]
  · refine (wp_storeImmIns (store_fits ‹_›) hn).mono fun s1 ⟨hs1, hm1⟩ =>
      ⟨?_, ?_⟩ <;> grind [Arg.map, Arg.val]
  · refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ =>
      (wp_storeImmIns (store_fits ‹_›) (n := n) ?_).mono
      fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_⟩ <;> grind [Arg.map, Arg.val]
  · refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => (wp_storeIns (n := n) ?_).mono
      fun s2 ⟨hs2, hm2⟩ => ⟨?_, ?_⟩ <;> grind [Arg.vars, Arg.map, Arg.val]
  · refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => wp_moviD.cons fun s2 ⟨hs2, hm2⟩ =>
      (wp_storeIns (n := n) ?_).mono fun s3 ⟨hs3, hm3⟩ => ⟨?_, ?_⟩ <;> grind [Arg.map, Arg.val]

theorem eventually_store {k : Nat} {sz : Sz} {x a : Arg Reg64} {c : List Directive}
    {post : MachineState → Prop}
    (hop : store sz x a = some c) (hc : c.IsInfixAt Host.prog k)
    (hvars : ∀ r, r ∈ x.vars ++ a.vars → r ∉ scratchRegs)
    (hok : storeOk s.dmem sz (argv s.regs a))
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratchRegs → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = storeMem s.dmem sz (argv s.regs a) (argv s.regs x) →
      Run (k + c.length) s' post) :
    Run k s post :=
  (wp_store (E := fun _ _ => False) hop hvars hok).eventually hc
    (fun s' ⟨h1, h2⟩ => hk s' h1 h2) (fun _ _ h => h.elim)

theorem wp_jcc {cc : CondCode} {l : Label} :
    Program.wp [ins (.jcc cc l)] (fun s' => s' = s ∧ cc.interp s.status = false)
      (fun a s' => a = Labels.label l ∧ s' = s ∧ cc.interp s.status = true) s := by
  refine Program.wp_singleton fun _ _ => ?_
  simp only [step_simp]
  cases h : cc.interp s.status <;> simp [Effects.All]

theorem wp_jcc_cmp {cc : CondCode} {l : Label} {k : Cls} {x y : Val} {s₀ : MachineData}
    (hf : s.status = cmpFlags k x y) (hkept : Kept s₀ s) :
    Program.wp [ins (.jcc cc l)]
      (fun s' => ¬ Truthy (boolVal (cc.interp (cmpFlags k x y))) ∧ Kept s₀ s')
      (fun a s' => a = Labels.label l ∧ Truthy (boolVal (cc.interp (cmpFlags k x y))) ∧ Kept s₀ s')
      s := by
  refine Program.wp_mono ?_ ?_ wp_jcc
  · rintro _ ⟨rfl, h⟩; exact ⟨by rw [← hf, h]; decide, hkept⟩
  · rintro _ _ ⟨rfl, rfl, h⟩; exact ⟨rfl, by rw [← hf, h]; decide, hkept⟩

theorem wp_jnzCmp {cls : Cls} {co : CmpOp} {a b : Arg Reg64} {l : Label} {c : List Directive}
    {v : Val} (hop : jnzCmp cls co a b l = some c)
    (hvars : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratchRegs)
    (hv : (Op.cmp cls co (a.map s.regs.get64) (b.map s.regs.get64)).eval = some v) :
    Program.wp c (fun s' => ¬ Truthy v ∧ Kept s s')
      (fun pc s' => pc = Labels.label l ∧ Truthy v ∧ Kept s s') s := by
  have h10 : ∀ r, r ∈ a.vars ++ b.vars → r ≠ .r10 ∧ r ≠ .r11 := fun r hr =>
    ne_of_not_mem_scratch (hvars r hr)
  revert hop
  fun_cases jnzCmp cls co a b l <;> intro hop <;> cases hop
  · obtain rfl := eval_cmp_argv hv
    refine wp_cmpRegIns.cons fun s1 ⟨hs1, hm1, hf1⟩ => wp_jcc_cmp hf1 ⟨?_, ?_⟩ <;> grind
  · obtain rfl := eval_cmp_argv hv
    refine (wp_cmpImmIns (fits_or ‹_›)).cons fun s1 ⟨hs1, hm1, hf1⟩ =>
      wp_jcc_cmp hf1 ⟨?_, ?_⟩ <;> grind
  · obtain rfl := eval_cmp_argv hv
    refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ => wp_cmpRegIns.cons fun s2 ⟨hs2, hm2, hf2⟩ =>
      wp_jcc_cmp ?_ ⟨?_, ?_⟩ <;> grind [Arg.vars, Arg.map, Arg.val]
  · obtain rfl := eval_cmp_swap_argv hv
    refine (wp_cmpImmIns (fits_or ‹_›)).cons fun s1 ⟨hs1, hm1, hf1⟩ =>
      wp_jcc_cmp hf1 ⟨?_, ?_⟩ <;> grind
  · obtain rfl := eval_cmp_argv hv
    refine wp_moviD.cons fun s1 ⟨hs1, hm1⟩ => wp_cmpRegIns.cons fun s2 ⟨hs2, hm2, hf2⟩ =>
      wp_jcc_cmp ?_ ⟨?_, ?_⟩ <;> grind [Arg.vars, Arg.map, Arg.val]
  · obtain rfl := eval_cmp_argv hv
    have h11 : Reg64.r11 ∉ b.vars := fun h => hvars _ (List.mem_append_right _ h) (by simp)
    refine wp_argTo.cons fun s1 ⟨hs1, hm1⟩ => wp_argTo.cons fun s2 ⟨hs2, hm2⟩ =>
      wp_cmpIns.cons fun s3 ⟨hs3, hm3, hf3⟩ => wp_jcc_cmp ?_ ⟨?_, ?_⟩ <;> grind [argv_set64]

theorem eventually_jnzCmp {k j : Nat} {cls : Cls} {co : CmpOp} {a b : Arg Reg64} {l : Label}
    {c : List Directive} {v : Val} {post : MachineState → Prop}
    (hop : jnzCmp cls co a b l = some c) (hc : c.IsInfixAt Host.prog k)
    (hj : Labels.label l = Host.addrOf j)
    (hvars : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratchRegs)
    (hv : (Op.cmp cls co (a.map s.regs.get64) (b.map s.regs.get64)).eval = some v)
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratchRegs → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = s.dmem →
      (Truthy v → Run j s' post) ∧ (¬ Truthy v → Run (k + c.length) s' post)) :
    Run k s post :=
  (wp_jnzCmp hop hvars hv).eventually hc (fun s' ⟨hn, h1, h2⟩ => (hk s' h1 h2).2 hn)
    fun _ s' ⟨ea, ht, h1, h2⟩ => ea ▸ hj ▸ (hk s' h1 h2).1 ht

theorem eventually_mov {k : Nat} {rd rs : Reg64} {post : MachineState → Prop}
    (hc : (mov rd rs).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = s.regs.get64 rs →
      (∀ r, r ∉ [rd] → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 1) s' post) :
    Run k s post := by
  refine (wp_movD (E := fun _ _ => False)).eventually hc (fun s' ⟨hs, hm⟩ => hk s' ?_ ?_ hm)
    (fun _ _ h => h.elim) <;> grind

theorem eventually_movi {k : Nat} {rd : Reg64} {c : BitVec 64} {post : MachineState → Prop}
    (hc : (movi rd c).IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = c →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 1) s' post) :
    Run k s post :=
  (wp_result (E := fun _ _ => False) wp_moviD).eventually hc
    (fun s' ⟨h1, h2, h3⟩ => hk s' h1 h2 h3) (fun _ _ h => h.elim)

end

/-- `load` succeeds on every class, width, signedness, destination and address. -/
theorem load_isSome (cl : Cls) (sz : Sz) (sg : Bool) (rd : Reg64) (a : Arg Reg64) :
    (load cl sz sg rd a).isSome = true := rfl

/-- `op` succeeds on every IL operation when the destination is not a scratch register. -/
theorem op_isSome (o : Op Reg64) (rd : Reg64) (hrd : rd ∉ scratchRegs) :
    (op o rd).isSome = true := by
  have hne := ne_of_not_mem_scratch hrd
  cases o with
  | bin k bo a b =>
    cases k <;> cases bo <;> (try cases a) <;> (try cases b) <;>
      simp only [op, shiftIns, shiftImmIns, divCore, divSeq, hne.1, hne.2, or_self,
        ite_false, binRegIns, binImmIns, binIns, Option.map_some] <;>
      repeat' (first | rfl | split)
  | cmp k co a b =>
    cases k <;> cases co <;> cases a <;> cases b <;>
      simp only [op, condOf] <;>
      repeat' (first | rfl | split)
  | ext k s sg a => cases a <;> rfl
  | copy k a => cases k <;> cases a <;> rfl

/-- `store` succeeds on every width, value and address. -/
theorem store_isSome (sz : Sz) (x a : Arg Reg64) : (store sz x a).isSome = true := by
  cases x <;> cases sz <;> (try rfl) <;>
    (simp only [store]; repeat' (first | rfl | split))

end LeanQbe.Amd64
