module

public import LeanQbe.Amd64.Isel
public import Kraken.X64.WP
public import Kraken.X64.Sep
public import Kraken.X64.Regs
public import LeanQbe.AbiLemmas
import Kraken.X64.Parser

/-!
# x64 instruction selection: step lemmas

One step lemma per directive and per snippet of `Isel.lean`, generic in the `Host` and the
position, in continuation form. Every directive `Isel.lean` emits is checked equal to the output of
Kraken's x64 parser by `rfl` (`ParserChecks`), so the printed assembly is what the semantics
describes. The bit-vector facts behind `cmp`/`setcc` (`cond_subFlags`), shift-count masking
(`take8_and_31`, `take8_and_63`) and sub-word loads (`ofInt_setWidth`) are proved by `omega` and
`simp` (no native tactics). The snippet-level lemmas `eventually_op`, `eventually_load`,
`eventually_store` are the `op_spec`, `load_spec`, `store_spec` fields of `Amd64.target`.
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
example : parse("sete %r11b") = [setccD (condOf .eq).2] := rfl
example : parse("setne %r11b") = [setccD (condOf .ne).2] := rfl
example : parse("setle %r11b") = [setccD (condOf .sle).2] := rfl
example : parse("setl %r11b") = [setccD (condOf .slt).2] := rfl
example : parse("setle %r11b") = [setccD (condOf .sge).2] := rfl
example : parse("setl %r11b") = [setccD (condOf .sgt).2] := rfl
example : parse("setbe %r11b") = [setccD (condOf .ule).2] := rfl
example : parse("setb %r11b") = [setccD (condOf .ult).2] := rfl
example : parse("setae %r11b") = [setccD (condOf .uge).2] := rfl
example : parse("seta %r11b") = [setccD (condOf .ugt).2] := rfl
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
example : parse("mov $5, %r10; mov %r10, %r11; mov %rdi, %r10") = (movi .r10 5 ++ [argTo .r11 (.var .r10), argTo .r10 (.var .rdi)]) := rfl
example : parse("mov $0, %rdx; div %r11") = ((divCore .l .udiv).get rfl).1 := rfl
example : parse("mov $0, %rdx; div %r11") = ((divCore .l .urem).get rfl).1 := rfl
example : parse("mov $0, %rdx; divl %r11d") = ((divCore .w .udiv).get rfl).1 := rfl
example : parse("mov $0, %rdx; divl %r11d") = ((divCore .w .urem).get rfl).1 := rfl
example : parse("mov %rax, %rdx; sar $63, %rdx; idiv %r11") = ((divCore .l .div).get rfl).1 := rfl
example : parse("mov %rax, %rdx; sar $63, %rdx; idiv %r11") = ((divCore .l .rem).get rfl).1 := rfl
example : parse("movl %eax, %edx; sarl $31, %edx; idivl %r11d") = ((divCore .w .div).get rfl).1 := rfl
example : parse("movl %eax, %edx; sarl $31, %edx; idivl %r11d") = ((divCore .w .rem).get rfl).1 := rfl
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

/-! ## Bit vectors -/

theorem get_b8 (regs : Reg64s) (r : Reg64) : regs.get (b8 r) = (regs.get64 r).setWidth 8 := by
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset]
  rfl

theorem get_h16 (regs : Reg64s) (r : Reg64) : regs.get (h16 r) = (regs.get64 r).setWidth 16 := by
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset]
  rfl

theorem set_b8 (regs : Reg64s) (r : Reg64) (v : BitVec 8) :
    regs.set (b8 r) v = regs.set64 r ((regs.get64 r).replaceLow v) := rfl

theorem replaceLow_setWidth (old : BitVec 64) (v : BitVec 8) : (old.replaceLow v).setWidth 8 = v := by
  ext i hi
  simp only [BitVec.replaceLow, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth]
  rw [show (old.drop 8).append v = old.drop 8 ++ v from rfl, BitVec.getLsbD_append]
  simp only [hi, ite_true, BitVec.getLsbD_eq_getElem]
  simp [show i < 64 by omega]

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
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  rcases hm with rfl | rfl | rfl <;> simp only [Nat.reducePow] <;> omega

theorem zero_append_toNat {w : Nat} (a : BitVec w) : ((0 : BitVec w) ++ a).toNat = a.toNat := by
  simp [BitVec.toNat_append]

theorem udiv_lt_two_pow {w : Nat} (a b : BitVec w) : a.toNat / b.toNat < 2 ^ w :=
  Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt

theorem sshiftRight_last_eq_signExtend {w : Nat} (a : BitVec w) :
    (a.sshiftRight (w - 1) ++ a) = a.signExtend (w + w) := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_signExtend]
  by_cases h1 : i < w
  · simp [h1, show i < w + w by omega]
  · by_cases h2 : i = w
    · subst i
      simp [show w < w + w by omega, show ¬ (w = 0) by omega, BitVec.msb_eq_getLsbD_last]
    · simp [h1, show i < w + w by omega, show ¬ (w ≤ i - w) by omega,
        show ¬ (w - 1 + (i - w) < w) by omega]

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
  have h1 := BitVec.le_toInt (a.sdiv b)
  have h2 := BitVec.toInt_lt (x := a.sdiv b)
  rcases hw with rfl | rfl <;> omega

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
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_udiv, Nat.mod_eq_of_lt (udiv_lt_two_pow a b)]

theorem ofNat_mod_eq_umod {w : Nat} (a b : BitVec w) :
    BitVec.ofNat w (a.toNat % b.toNat) = a % b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_umod,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt)]

/-! ## Flags of `cmp` -/

/-- The flags after `cmp` computing `a - b` at width `n`, as Kraken's `cmp` sets them. -/
def subFlags {n : Nat} (a b : BitVec n) : StatusFlags :=
  StatusFlags.from_result (a - b)
    { cf := (a - b).unsigned != a.unsigned - b.unsigned,
      af := ((a - b).take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := (a - b).signed != a.signed - b.signed }

theorem subs_c {n : Nat} (a b : BitVec n) :
    ((a - b).unsigned == a.unsigned - b.unsigned) = !(a < b : Bool) := by
  simp only [BitVec.unsigned]
  by_cases h : a < b
  · have h' : a.toNat < b.toNat := h
    simp only [h, decide_true, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    omega
  · have h' : ¬ BitVec.usubOverflow a b := by simpa [BitVec.usubOverflow_eq] using h
    have h'' : b.toNat ≤ a.toNat := by simpa [BitVec.lt_def] using h
    simp only [h, decide_false, Bool.not_false, beq_iff_eq, BitVec.toNat_sub_of_not_usubOverflow h']
    omega

theorem subs_v {n : Nat} (a b : BitVec n) :
    ((a - b).signed != a.signed - b.signed) = BitVec.ssubOverflow a b := by
  simp only [BitVec.signed]
  by_cases h : BitVec.ssubOverflow a b
  · simp only [h, bne_iff_ne, ne_eq]
    have h1 := BitVec.le_two_mul_toInt (x := a - b)
    have h2 := BitVec.two_mul_toInt_lt (x := a - b)
    simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases n with _ | n
    · simp [BitVec.of_length_zero] at h
    · simp only [Nat.add_one_sub_one] at h
      have : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by rw [Int.pow_succ]; omega
      push_cast at h1 h2
      omega
  · simp only [Bool.not_eq_true] at h
    rw [BitVec.toInt_sub_of_not_ssubOverflow (by rw [h]; simp)]
    simp [h]

theorem beq_zero_toInt {n : Nat} (z : BitVec n) : (z == 0#n) = decide (z.toInt = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toInt_inj, BitVec.toInt_zero]

theorem beq_toNat {n : Nat} (x y : BitVec n) : (x == y) = decide (x.toNat = y.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]

set_option linter.unusedSimpArgs false in
theorem cond_subFlags {n : Nat} (hn : n = 32 ∨ n = 64) (co : CmpOp) (x y : BitVec n) :
    (condOf co).2.interp (if (condOf co).1 then subFlags y x else subFlags x y) = co.eval x y := by
  have key : ∀ x y : BitVec n, ∀ cc : CondCode, cc.interp (subFlags x y) =
      cc.interp (StatusFlags.from_result (x - y)
        { cf := !(!(x < y : Bool)), af := false, of := BitVec.ssubOverflow x y }) := by
    intro x y cc
    cases cc <;> simp only [subFlags, StatusFlags.from_result, CondCode.interp, bne, subs_c,
      ← subs_v]
  have hx1 := BitVec.toInt_lt (x := x)
  have hx2 := BitVec.le_toInt x
  have hy1 := BitVec.toInt_lt (x := y)
  have hy2 := BitVec.le_toInt y
  have hd1 := BitVec.toInt_lt (x := x - y)
  have hd2 := BitVec.le_toInt (x - y)
  have he1 := BitVec.toInt_lt (x := y - x)
  have he2 := BitVec.le_toInt (y - x)
  have hmod : ∀ x y : BitVec n, (x - y).toInt % 2 ^ n = (x.toInt - y.toInt) % 2 ^ n := by
    intro x y
    rw [BitVec.toInt_sub]
    have : (x.toInt - y.toInt).bmod (2 ^ n) % ((2 ^ n : Nat) : Int) =
        (x.toInt - y.toInt) % ((2 ^ n : Nat) : Int) := Int.bmod_emod
    push_cast at this
    exact this
  have hm1 := hmod x y
  have hm2 := hmod y x
  have hxn := x.isLt
  have hyn := y.isLt
  have hsub := BitVec.toNat_sub x y
  rcases hn with rfl | rfl <;> cases co <;>
    simp only [condOf, key, Bool.not_not, ite_true, ite_false, Bool.false_eq_true] <;>
    simp only [StatusFlags.from_result, BitVec.ssubOverflow, BitVec.zero_eq, CondCode.interp,
      CmpOp.eval]
  case' inl.sle | inl.slt | inl.sge | inl.sgt | inr.sle | inr.slt | inr.sge | inr.sgt =>
    simp only [BitVec.msb_eq_toInt, beq_zero_toInt, BitVec.sle_eq_decide, BitVec.slt_eq_decide]
  all_goals
    try simp only [beq_toNat, BitVec.toNat_ofNat, BitVec.ule_eq_decide, BitVec.ult_eq_decide,
      BitVec.lt_def, bne]
  all_goals
    rw [Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ← Bool.decide_or, ← Bool.decide_and,
      ← decide_not, beq_iff_eq, ne_eq, decide_eq_decide, decide_eq_true_eq, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false]
    omega

/-- The flags after `cmp{k} %r10, %r11`. -/
def cmpFlags : Cls → Val → Val → StatusFlags
  | .l, a, b => subFlags a b
  | .w, a, b => subFlags (lo32 a) (lo32 b)

/-- `cmp` + `set{cc}` computes the comparison. -/
theorem eval_cmp (k : Cls) (o : CmpOp) (a b : Val) :
    (Op.cmp k o (.imm a) (.imm b)).eval = some (boolVal ((condOf o).2.interp
      (cmpFlags k (if (condOf o).1 then b else a) (if (condOf o).1 then a else b)))) := by
  have h := fun n hn x y => cond_subFlags (n := n) hn o x y
  have h64 := h 64 (by simp) a b
  have h32 := h 32 (by simp) (lo32 a) (lo32 b)
  cases k <;> simp only [Op.eval, Arg.val, cmpFlags] <;>
    by_cases hc : (condOf o).1 <;>
    simp only [hc, ite_true, ite_false, Bool.false_eq_true] at h64 h32 ⊢ <;>
    simp only [h64, h32]

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
    (repeat intro _) <;>
    refine hk _ ?_ rfl
  all_goals first | rfl | (dsimp only; rw [BitVec.add_comm])

theorem eventually_shiftIns {i : Nat} {k : Cls} {o : BinOp} {di : Directive} {v : Val}
    {s : MachineData} {post : (MachineState → Prop)}
    (hb : shiftIns k o = some di) (hi : Host.prog[i]? = some di)
    (hv : (Op.bin k o (.imm (s.regs.get64 .r11)) (.imm (s.regs.get64 .rcx))).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .r11 v → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  have e : s.regs.rcx.toBitVec = s.regs.get64 .rcx := rfl
  cases k <;> cases o <;> simp only [shiftIns, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
    refine Host.eventually_of_interp_cps hi ?_ <;>
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
      MachineData.setReg, Effects.All, set_q, get_q, Reg64s.set_low32, Reg64s.get_low32,
      ShiftCountExpr.interpMasked, ShiftCountExpr.interp, e, take8_and_31, take8_and_63] <;>
    simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
    subst hv
  all_goals
    repeat' (first | split | (simp only [Effects.All]; intros))
  all_goals
    try simp only [Effects.All]
    intros
    refine hk _ ?_ rfl
  all_goals
    first
    | rfl
    | (rename_i h; simp at h; simp [h])

theorem eventually_cmpIns {i : Nat} {k : Cls} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (cmpIns k))
    (hk : ∀ s' : MachineData, s'.regs = s.regs → s'.dmem = s.dmem →
      s'.status = cmpFlags k (s.regs.get64 .r11) (s.regs.get64 .r10) → Run (i + 1) s' post) :
    Run i s post := by
  cases k <;>
    refine Host.eventually_of_interp_cps hi ?_ <;>
    simp only [cmpIns, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, Effects.All, get_q, Reg64s.get_low32] <;>
    exact hk _ rfl rfl rfl

theorem eventually_setcc_movzb {i : Nat} {cc : CondCode} {rd : Reg64} {s : MachineData}
    {post : (MachineState → Prop)}
    (h1 : Host.prog[i]? = some (setccD cc)) (h2 : Host.prog[i + 1]? = some (movzbD rd))
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = boolVal (cc.interp s.status) →
      (∀ r, r ≠ rd → r ≠ .r11 → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (i + 2) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps h1 ?_
  simp only [setccD, Directive.interp, Instr.interp, Operation.interp, MachineData.set,
    MachineData.setReg, Effects.All, set_b8]
  refine Host.eventually_of_interp_cps h2 ?_
  simp only [movzbD, Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Effects.All, Reg64s.set_low32, get_b8,
    Reg64s.get64_set64_same, replaceLow_setWidth]
  refine hk _ ?_ (fun r h1 h2 => ?_) rfl
  · rw [Reg64s.get64_set64_same]
    cases cc.interp s.status <;> rfl
  · rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h1), Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h2)]

theorem eventually_extD {i : Nat} {k : Cls} {sz : Sz} {sg : Bool} {rd r : Reg64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (extD k sz sg rd r))
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 rd (k.trunc (sz.extend sg (s.regs.get64 r))) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  cases k <;> cases sz <;> cases sg <;>
    simp only [extD, movD, movlD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, set_q, get_q,
      Reg64s.set_low32, Reg64s.get_low32, get_b8, get_h16] <;>
    refine hk _ ?_ rfl <;>
    dsimp only <;>
    congr 1 <;>
    simp only [Cls.trunc, Sz.extend, lo32, zext32] <;>
    ext j hj <;>
    simp [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last] <;>
    by_cases h1 : j < 8 <;> by_cases h2 : j < 16 <;> by_cases h3 : j < 32 <;> simp [h1, h2, h3] <;>
    omega

theorem eventually_sar63D {i : Nat} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63)))))
    (hk : ∀ s' : MachineData,
      s'.regs = s.regs.set64 .rdx ((s.regs.get64 .rdx).sshiftRight 63) → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Effects.All, set_q, get_q, ShiftCountExpr.interpMasked,
    ShiftCountExpr.interp, ConstExpr.interp, BitVec.take]
  change (undefined fun _ => undefined fun _ => Effects.done _).All _
  intro _ _
  exact hk _ rfl rfl

theorem eventually_sar31D {i : Nat} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (ins32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31)))))
    (hk : ∀ s' : MachineData,
      s'.regs = s.regs.set64 .rdx (zext32 ((lo32 (s.regs.get64 .rdx)).sshiftRight 31)) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Effects.All, Reg64s.set_low32, Reg64s.get_low32,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp, BitVec.take]
  change (undefined fun _ => undefined fun _ => Effects.done _).All _
  intro _ _
  exact hk _ rfl rfl

theorem eventually_udiv64D {i : Nat} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (ins (.div (.reg (q .r11)))))
    (rdx0 : s.regs.get64 .rdx = 0) (hb0 : s.regs.get64 .r11 ≠ 0)
    (hk : ∀ s' : MachineData,
      s'.regs = (s.regs.set64 .rax (s.regs.get64 .rax / s.regs.get64 .r11)).set64 .rdx
        (s.regs.get64 .rax % s.regs.get64 .r11) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  have hlt := udiv_lt_two_pow (s.regs.get64 .rax) (s.regs.get64 .r11)
  have hw : (Width.W64 == Width.W8) = false := rfl
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.setReg,
    Effects.All, set_q, get_q, hw, Bool.false_eq_true, ite_false, rdx0, zero_append_toNat,
    Width.bits, ofNat_div_eq_udiv, ofNat_mod_eq_umod]
  have hcond : ((s.regs.get64 .r11 == 0) ||
      decide (2 ^ 64 ≤ (s.regs.get64 .rax).toNat / (s.regs.get64 .r11).toNat)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    exact ⟨hb0, Nat.not_le_of_lt hlt⟩
  simp only [hcond, Bool.false_eq_true, ite_false, Effects.All]
  intro _
  exact hk _ rfl rfl

theorem eventually_udiv32D {i : Nat} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (ins32 (.div (.reg (d .r11)))))
    (rdx0 : lo32 (s.regs.get64 .rdx) = 0) (hb0 : lo32 (s.regs.get64 .r11) ≠ 0)
    (hk : ∀ s' : MachineData,
      s'.regs = (s.regs.set64 .rax
        (zext32 (lo32 (s.regs.get64 .rax) / lo32 (s.regs.get64 .r11)))).set64 .rdx
        (zext32 (lo32 (s.regs.get64 .rax) % lo32 (s.regs.get64 .r11))) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  have hlt := udiv_lt_two_pow (lo32 (s.regs.get64 .rax)) (lo32 (s.regs.get64 .r11))
  have hw : (Width.W32 == Width.W8) = false := rfl
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.setReg,
    Effects.All, Reg64s.set_low32, Reg64s.get_low32, hw, Bool.false_eq_true, ite_false, rdx0,
    zero_append_toNat, Width.bits, ofNat_div_eq_udiv, ofNat_mod_eq_umod]
  have hcond : ((lo32 (s.regs.get64 .r11) == 0) ||
      decide (2 ^ 32 ≤ (lo32 (s.regs.get64 .rax)).toNat / (lo32 (s.regs.get64 .r11)).toNat)) =
      false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    exact ⟨hb0, Nat.not_le_of_lt hlt⟩
  simp only [hcond, Bool.false_eq_true, ite_false, Effects.All]
  intro _
  exact hk _ rfl rfl

theorem eventually_idiv64D {i : Nat} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (ins (.idiv (.reg (q .r11)))))
    (hrdx : s.regs.get64 .rdx = (s.regs.get64 .rax).sshiftRight 63)
    (hsd : sdivDefined (s.regs.get64 .rax) (s.regs.get64 .r11) = true)
    (hk : ∀ s' : MachineData,
      s'.regs = (s.regs.set64 .rax ((s.regs.get64 .rax).sdiv (s.regs.get64 .r11))).set64 .rdx
        ((s.regs.get64 .rax).srem (s.regs.get64 .r11)) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  have happ := sshiftRight_last_append_toInt (w := 64) (by simp) (s.regs.get64 .rax)
  have hbnd := tdiv_in_bounds (w := 64) (by simp) hsd
  have hb0 : s.regs.get64 .r11 ≠ 0 := by
    simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne] at hsd; exact hsd.1
  have hw : (Width.W64 == Width.W8) = false := rfl
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.setReg,
    Effects.All, set_q, get_q, hw, Bool.false_eq_true, ite_false, hrdx, happ, Width.bits,
    ofInt_tdiv_eq_sdiv (by simp) hsd, ofInt_tmod_eq_srem]
  have hcond : (((s.regs.get64 .r11 == 0) ||
      decide ((s.regs.get64 .rax).toInt.tdiv (s.regs.get64 .r11).toInt < -2 ^ 63)) ||
      decide (2 ^ 63 ≤ (s.regs.get64 .rax).toInt.tdiv (s.regs.get64 .r11).toInt)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    exact ⟨⟨hb0, fun h => hbnd (Or.inl h)⟩, fun h => hbnd (Or.inr h)⟩
  simp only [hcond, Bool.false_eq_true, ite_false, Effects.All]
  intro _
  exact hk _ rfl rfl

theorem eventually_idiv32D {i : Nat} {s : MachineData} {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (ins32 (.idiv (.reg (d .r11)))))
    (hrdx : lo32 (s.regs.get64 .rdx) = (lo32 (s.regs.get64 .rax)).sshiftRight 31)
    (hsd : sdivDefined (lo32 (s.regs.get64 .rax)) (lo32 (s.regs.get64 .r11)) = true)
    (hk : ∀ s' : MachineData,
      s'.regs = (s.regs.set64 .rax
        (zext32 ((lo32 (s.regs.get64 .rax)).sdiv (lo32 (s.regs.get64 .r11))))).set64 .rdx
        (zext32 ((lo32 (s.regs.get64 .rax)).srem (lo32 (s.regs.get64 .r11)))) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  have happ := sshiftRight_last_append_toInt (w := 32) (by simp) (lo32 (s.regs.get64 .rax))
  have hbnd := tdiv_in_bounds (w := 32) (by simp) hsd
  have hb0 : lo32 (s.regs.get64 .r11) ≠ 0 := by
    simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne] at hsd; exact hsd.1
  have hw : (Width.W32 == Width.W8) = false := rfl
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.setReg,
    Effects.All, Reg64s.set_low32, Reg64s.get_low32, hw, Bool.false_eq_true, ite_false, hrdx, happ,
    Width.bits, ofInt_tdiv_eq_sdiv (by simp) hsd, ofInt_tmod_eq_srem]
  have hcond : (((lo32 (s.regs.get64 .r11) == 0) ||
      decide ((lo32 (s.regs.get64 .rax)).toInt.tdiv (lo32 (s.regs.get64 .r11)).toInt < -2 ^ 31)) ||
      decide (2 ^ 31 ≤ (lo32 (s.regs.get64 .rax)).toInt.tdiv (lo32 (s.regs.get64 .r11)).toInt)) =
      false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    exact ⟨⟨hb0, fun h => hbnd (Or.inl h)⟩, fun h => hbnd (Or.inr h)⟩
  simp only [hcond, Bool.false_eq_true, ite_false, Effects.All]
  intro _
  exact hk _ rfl rfl

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

theorem eventually_storeIns {i : Nat} {sz : Sz} {ra : Reg64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (storeIns sz ra))
    {n : Int} (hload : Mem.loadInt s.dmem (s.regs.get64 ra) sz.bytes = some n)
    (hk : ∀ s' : MachineData, s'.regs = s.regs →
      s'.dmem = storeMem s.dmem sz (s.regs.get64 ra) (s.regs.get64 .r11) →
      Run (i + 1) s' post) :
    Run i s post := by
  cases sz
  case l => exact eventually_storelD hi hload hk
  all_goals
    simp only [Sz.bytes] at hload
    refine Host.eventually_of_interp_cps hi ?_
    simp only [storeIns, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, MachineData.set, Effects.All, atReg_interp, get_b8, get_h16,
      Reg64s.get_low32]
    simp only [MachineData.store, Effects.All_require_write_access, Width.bytes, hload]
    exact hk _ rfl rfl

theorem eventually_loadIns {k : Nat} {cl : Cls} {sz : Sz} {sg : Bool} {rd ra : Reg64}
    {s : MachineData} {post : (MachineState → Prop)}
    (hc : (loadIns cl sz sg rd ra).IsInfixAt Host.prog k)
    {n : Int} (hload : Mem.loadInt s.dmem (s.regs.get64 ra) sz.bytes = some n)
    (hk : ∀ s' : MachineData,
      s'.regs = s.regs.set64 rd (cl.trunc (sz.extend sg (BitVec.ofInt 64 n))) →
      s'.dmem = s.dmem → Run (k + (loadIns cl sz sg rd ra).length) s' post) :
    Run k s post := by
  cases cl <;> cases sz <;> cases sg
  case w.l.false | w.l.true =>
    simp only [loadIns] at hc hk
    obtain ⟨h0, hc1⟩ := hc.cons
    refine eventually_loadlD h0 hload fun s1 hs1 hm1 => ?_
    refine eventually_movlD (List.isInfixAt_singleton.mp hc1) fun s2 hs2 hm2 => hk s2 ?_ ?_
    · rw [hs2, hs1, Reg64s.get64_set64_same, Reg64s.set64_set64_same]
      rfl
    · rw [hm2, hm1]
  all_goals
    simp only [loadIns, List.length_singleton] at hc hk ⊢
    simp only [Sz.bytes] at hload
    refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
    simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, set_q,
      Reg64s.set_low32, atReg_interp]
    simp only [MachineData.load, Effects.All_require_read_access, Width.bytes, hload]
    refine hk _ ?_ rfl
  all_goals dsimp only
  all_goals congr 1
  all_goals try simp only [Cls.trunc, Sz.extend, lo32, zext32, ofInt_setWidth 8 (by simp),
      ofInt_setWidth 16 (by simp), ofInt_setWidth 32 (by simp)]
  all_goals
    first
    | rfl
    | (try generalize BitVec.ofInt 8 n = x) <;> (try generalize BitVec.ofInt 16 n = x) <;>
      (try generalize BitVec.ofInt 32 n = x) <;>
      ext j hj <;>
      simp [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last] <;>
      by_cases h1 : j < 8 <;> by_cases h2 : j < 16 <;> by_cases h3 : j < 32 <;>
      simp [h1, h2, h3] <;> first | omega | exact BitVec.getLsbD_of_ge _ _ (by omega)

end

section
variable [Host]

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

theorem eventually_cmp {k : Nat} {kk : Cls} {cc : CondCode} {x y : Arg Reg64} {rd : Reg64}
    {s : MachineData} {post : (MachineState → Prop)}
    (hc : [argTo .r11 x, argTo .r10 y, cmpIns kk, setccD cc, movzbD rd].IsInfixAt Host.prog k)
    (hy : ∀ r, r ∈ y.vars → r ≠ .r11)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = boolVal (cc.interp (cmpFlags kk (argv s.regs x) (argv s.regs y))) →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 5) s' post) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, hc2⟩ := hc1.cons
  obtain ⟨h2, hc3⟩ := hc2.cons
  obtain ⟨h3, hc4⟩ := hc3.cons
  obtain ⟨h4, -⟩ := hc4.cons
  refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
  refine eventually_argTo h1 fun s2 hs2 hm2 => ?_
  have e11 : s2.regs.get64 .r11 = argv s.regs x := by
    rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1, Reg64s.get64_set64_same]
  have e10 : s2.regs.get64 .r10 = argv s.regs y := by
    rw [hs2, Reg64s.get64_set64_same]
    exact argv_congr fun r hr => by
      rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hy r hr))]
  refine eventually_cmpIns h2 fun s3 hs3 hm3 hf3 => ?_
  refine eventually_setcc_movzb h3 h4 fun s4 hv4 hfr4 hm4 => hk s4 ?_ (fun r hr => ?_) ?_
  · rw [hv4, hf3, e11, e10]
  · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
    rw [hfr4 r hr.1 hr.2.2.1, hs3, hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1), hs1,
      Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1)]
  · rw [hm4, hm3, hm2, hm1]

theorem eventually_shift {k : Nat} {kk : Cls} {oo : BinOp} {i : Directive} {a b : Arg Reg64}
    {rd : Reg64} {v : Val} {s : MachineData} {post : (MachineState → Prop)}
    (hsh : shiftIns kk oo = some i)
    (hc : [argTo .r11 a, movD .r10 .rcx, argTo .rcx b, i, movD .rcx .r10, movD rd .r11].IsInfixAt
      Host.prog k)
    (hb : ∀ r, r ∈ b.vars → r ≠ .r10 ∧ r ≠ .r11)
    (hv : (Op.bin kk oo (.imm (argv s.regs a)) (.imm (argv s.regs b))).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 6) s' post) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, hc2⟩ := hc1.cons
  obtain ⟨h2, hc3⟩ := hc2.cons
  obtain ⟨h3, hc4⟩ := hc3.cons
  obtain ⟨h4, hc5⟩ := hc4.cons
  obtain ⟨h5, -⟩ := hc5.cons
  refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
  refine eventually_movD h1 fun s2 hs2 hm2 => ?_
  refine eventually_argTo h2 fun s3 hs3 hm3 => ?_
  have e11 : s3.regs.get64 .r11 = argv s.regs a := by
    rw [hs3, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs2,
      Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1, Reg64s.get64_set64_same]
  have ecx : s3.regs.get64 .rcx = argv s.regs b := by
    rw [hs3, Reg64s.get64_set64_same]
    exact argv_congr fun r hr => by
      rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hb r hr).1), hs1,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hb r hr).2)]
  have e10 : s3.regs.get64 .r10 = s.regs.get64 .rcx := by
    rw [hs3, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs2, Reg64s.get64_set64_same, hs1,
      Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
  refine eventually_shiftIns hsh h3 (by rw [e11, ecx]; exact hv) fun s4 hs4 hm4 => ?_
  refine eventually_movD h4 fun s5 hs5 hm5 => ?_
  refine eventually_movD h5 fun s6 hs6 hm6 => hk s6 ?_ (fun r hr => ?_) ?_
  · rw [hs6, Reg64s.get64_set64_same, hs5, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs4,
      Reg64s.get64_set64_same]
  · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
    rw [hs6, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs5, Reg64s.get64_set64]
    split
    · next he =>
      subst he
      rw [hs4, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), e10]
    · next he =>
      rw [hs4, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1), hs3,
        Reg64s.get64_set64_of_ne _ _ _ _ he, hs2,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1), hs1,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1)]
  · rw [hm6, hm5, hm4, hm3, hm2, hm1]

theorem eventually_divCore {k : Nat} {kk : Cls} {oo : BinOp} {core : List Directive} {res : Reg64}
    {v : Val} {s : MachineData} {post : (MachineState → Prop)}
    (hd : divCore kk oo = some (core, res)) (hc : core.IsInfixAt Host.prog k)
    (hv : (Op.bin kk oo (.imm (s.regs.get64 .rax)) (.imm (s.regs.get64 .r11))).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 res = v →
      (∀ r, r ≠ .rax → r ≠ .rdx → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + core.length) s' post) :
    Run k s post := by
  have keep2 : ∀ (regs0 : Reg64s) (v1 v2 : Val) (r : Reg64),
      r ≠ .rax → r ≠ .rdx → ((regs0.set64 .rax v1).set64 .rdx v2).get64 r = regs0.get64 r := by
    intro regs0 v1 v2 r h1 h2
    rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h2),
      Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h1)]
  cases kk <;> cases oo <;> simp only [divCore, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hd
  case w.div | w.rem =>
    obtain ⟨rfl, rfl⟩ := hd
    simp only [Op.eval, Arg.val, BinOp.eval] at hv
    by_cases hsd : sdivDefined (lo32 (s.regs.get64 .rax)) (lo32 (s.regs.get64 .r11)) = true
    · simp only [hsd, ite_true, Option.map_some, Option.some.injEq] at hv
      subst hv
      obtain ⟨h0, hc1⟩ := hc.cons
      obtain ⟨h1, hc2⟩ := hc1.cons
      obtain ⟨h2, -⟩ := hc2.cons
      refine eventually_movlD h0 fun s1 hs1 hm1 => ?_
      refine eventually_sar31D h1 fun s2 hs2 hm2 => ?_
      have e_rax : s2.regs.get64 .rax = s.regs.get64 .rax := by
        rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1,
          Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      have e_r11 : s2.regs.get64 .r11 = s.regs.get64 .r11 := by
        rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1,
          Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      have e_rdx : lo32 (s2.regs.get64 .rdx) = (lo32 (s2.regs.get64 .rax)).sshiftRight 31 := by
        rw [e_rax, hs2, Reg64s.get64_set64_same, hs1, Reg64s.get64_set64_same]
        simp [lo32, zext32, Cls.trunc]
      refine eventually_idiv32D h2 e_rdx (by rw [e_rax, e_r11]; exact hsd) fun s3 hs3 hm3 =>
        hk s3 ?_ (fun r h1 h2 => ?_) (by rw [hm3, hm2, hm1])
      · first
        | rw [hs3, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), Reg64s.get64_set64_same, e_rax,
            e_r11]
        | rw [hs3, Reg64s.get64_set64_same, e_rax, e_r11]
      · rw [hs3, keep2 _ _ _ r h1 h2, hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h2), hs1,
          Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h2)]
    · simp only [hsd, Bool.false_eq_true, ite_false, Option.map_none, reduceCtorEq] at hv
  case l.div | l.rem =>
    obtain ⟨rfl, rfl⟩ := hd
    simp only [Op.eval, Arg.val, BinOp.eval] at hv
    by_cases hsd : sdivDefined (s.regs.get64 .rax) (s.regs.get64 .r11) = true
    · simp only [hsd, ite_true, Option.some.injEq] at hv
      subst hv
      obtain ⟨h0, hc1⟩ := hc.cons
      obtain ⟨h1, hc2⟩ := hc1.cons
      obtain ⟨h2, -⟩ := hc2.cons
      refine eventually_movD h0 fun s1 hs1 hm1 => ?_
      refine eventually_sar63D h1 fun s2 hs2 hm2 => ?_
      have e_rax : s2.regs.get64 .rax = s.regs.get64 .rax := by
        rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1,
          Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      have e_r11 : s2.regs.get64 .r11 = s.regs.get64 .r11 := by
        rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1,
          Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      have e_rdx : s2.regs.get64 .rdx = (s2.regs.get64 .rax).sshiftRight 63 := by
        rw [e_rax, hs2, Reg64s.get64_set64_same, hs1, Reg64s.get64_set64_same]
      refine eventually_idiv64D h2 e_rdx (by rw [e_rax, e_r11]; exact hsd) fun s3 hs3 hm3 =>
        hk s3 ?_ (fun r h1 h2 => ?_) (by rw [hm3, hm2, hm1])
      · first
        | rw [hs3, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), Reg64s.get64_set64_same, e_rax,
            e_r11]
        | rw [hs3, Reg64s.get64_set64_same, e_rax, e_r11]
      · rw [hs3, keep2 _ _ _ r h1 h2, hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h2), hs1,
          Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h2)]
    · simp only [hsd, Bool.false_eq_true, ite_false, reduceCtorEq] at hv
  case w.udiv | w.urem =>
    obtain ⟨rfl, rfl⟩ := hd
    simp only [Op.eval, Arg.val, BinOp.eval] at hv
    by_cases hb0 : lo32 (s.regs.get64 .r11) = 0
    · simp only [hb0, ite_true, Option.map_none, reduceCtorEq] at hv
    · simp only [hb0, ite_false, Option.map_some, Option.some.injEq] at hv
      subst hv
      obtain ⟨h0, hc1⟩ := hc.cons
      obtain ⟨h1, -⟩ := hc1.cons
      refine eventually_moviD h0 fun s1 hs1 hm1 => ?_
      have e_rax : s1.regs.get64 .rax = s.regs.get64 .rax := by
        rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      have e_r11 : s1.regs.get64 .r11 = s.regs.get64 .r11 := by
        rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      have e_rdx : lo32 (s1.regs.get64 .rdx) = 0 := by
        rw [hs1, Reg64s.get64_set64_same]; rfl
      refine eventually_udiv32D h1 e_rdx (by rw [e_r11]; exact hb0) fun s2 hs2 hm2 =>
        hk s2 ?_ (fun r h1 h2 => ?_) (by rw [hm2, hm1])
      · first
        | rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), Reg64s.get64_set64_same, e_rax,
            e_r11]
        | rw [hs2, Reg64s.get64_set64_same, e_rax, e_r11]
      · rw [hs2, keep2 _ _ _ r h1 h2, hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h2)]
  case l.udiv | l.urem =>
    obtain ⟨rfl, rfl⟩ := hd
    simp only [Op.eval, Arg.val, BinOp.eval] at hv
    by_cases hb0 : s.regs.get64 .r11 = 0
    · simp only [hb0, ite_true, reduceCtorEq] at hv
    · simp only [hb0, ite_false, Option.some.injEq] at hv
      subst hv
      obtain ⟨h0, hc1⟩ := hc.cons
      obtain ⟨h1, -⟩ := hc1.cons
      refine eventually_moviD h0 fun s1 hs1 hm1 => ?_
      have e_rax : s1.regs.get64 .rax = s.regs.get64 .rax := by
        rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      have e_r11 : s1.regs.get64 .r11 = s.regs.get64 .r11 := by
        rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      have e_rdx : s1.regs.get64 .rdx = 0 := by rw [hs1, Reg64s.get64_set64_same]
      refine eventually_udiv64D h1 e_rdx (by rw [e_r11]; exact hb0) fun s2 hs2 hm2 =>
        hk s2 ?_ (fun r h1 h2 => ?_) (by rw [hm2, hm1])
      · first
        | rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), Reg64s.get64_set64_same, e_rax,
            e_r11]
        | rw [hs2, Reg64s.get64_set64_same, e_rax, e_r11]
      · rw [hs2, keep2 _ _ _ r h1 h2, hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm h2)]

theorem eventually_divSeq {k : Nat} {kk : Cls} {oo : BinOp} {core c : List Directive} {res rd : Reg64}
    {a b : Arg Reg64} {v : Val} {s : MachineData} {post : (MachineState → Prop)}
    (hd : divCore kk oo = some (core, res))
    (hseq : divSeq rd core res a b = some c)
    (hc : c.IsInfixAt Host.prog k)
    (hb : ∀ r, r ∈ b.vars → r ≠ .r10 ∧ r ≠ .r11)
    (hv : (Op.bin kk oo (.imm (argv s.regs a)) (.imm (argv s.regs b))).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + c.length) s' post) :
    Run k s post := by
  by_cases hscr : rd = .r10 ∨ rd = .r11
  · simp [divSeq, hscr] at hseq
  · have hrd10 : rd ≠ .r10 := fun he => hscr (Or.inl he)
    have hrd11 : rd ≠ .r11 := fun he => hscr (Or.inr he)
    by_cases hrax : rd = .rax
    · subst hrax
      simp only [divSeq, hscr, ite_false, ite_true, Option.some.injEq] at hseq
      subst hseq
      obtain ⟨h0, hc1⟩ := hc.cons
      obtain ⟨h1, hc2⟩ := hc1.cons
      obtain ⟨h2, hc3⟩ := hc2.cons
      obtain ⟨h3, hc_rest⟩ := hc3.cons
      obtain ⟨hcore, hpost⟩ := List.IsInfixAt.append hc_rest
      obtain ⟨hp0, hpost1⟩ := hpost.cons
      obtain ⟨hp1, -⟩ := hpost1.cons
      refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
      refine eventually_argTo h1 fun s2 hs2 hm2 => ?_
      refine eventually_movD h2 fun s3 hs3 hm3 => ?_
      refine eventually_movD h3 fun s4 hs4 hm4 => ?_
      have erax : s4.regs.get64 .rax = argv s.regs a := by
        rw [hs4, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs3, Reg64s.get64_set64_same, hs2,
          Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1, Reg64s.get64_set64_same]
      have er11 : s4.regs.get64 .r11 = argv s.regs b := by
        rw [hs4, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs3,
          Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs2, Reg64s.get64_set64_same]
        exact argv_congr fun r hr => by
          rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hb r hr).1)]
      have er10 : s4.regs.get64 .r10 = s.regs.get64 .rdx := by
        rw [hs4, Reg64s.get64_set64_same, hs3, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs2,
          Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1,
          Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
      refine eventually_divCore hd hcore (by rw [erax, er11]; exact hv) fun s5 hv5 hfr5 hm5 => ?_
      refine eventually_movD hp0 fun s6 hs6 hm6 => ?_
      refine eventually_movD hp1 fun s7 hs7 hm7 => ?_
      have := hk s7 ?_ (fun r hr => ?_) (by rw [hm7, hm6, hm5, hm4, hm3, hm2, hm1])
      · simp only [List.length_cons, List.length_append, List.length_nil] at this; rwa [show k + 1 + 1 + 1 + 1 + core.length + 1 + 1 = k + (core.length + 2 + 1 + 1 + 1 + 1) by omega]
      · rw [hs7, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs6, Reg64s.get64_set64_same, hv5]
      · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
        rw [hs7, Reg64s.get64_set64]
        split
        · next he =>
          subst he
          rw [hs6, Reg64s.get64_set64_of_ne _ _ _ _ (by decide),
            hfr5 .r10 (by decide) (by decide), er10]
        · next he =>
          rw [hs6, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1),
            hfr5 r hr.1 (Ne.symm he), hs4, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1),
            hs3, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs2,
            Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1), hs1,
            Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1)]
    · by_cases hrdx : rd = .rdx
      · subst hrdx
        simp only [divSeq, reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq] at hseq
        subst hseq
        obtain ⟨h0, hc1⟩ := hc.cons
        obtain ⟨h1, hc2⟩ := hc1.cons
        obtain ⟨h2, hc3⟩ := hc2.cons
        obtain ⟨h3, hc4⟩ := hc3.cons
        obtain ⟨h4, hc_rest⟩ := hc4.cons
        obtain ⟨hcore, hpost⟩ := List.IsInfixAt.append hc_rest
        obtain ⟨hp0, hpost1⟩ := hpost.cons
        obtain ⟨hp1, -⟩ := hpost1.cons
        refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
        refine eventually_argTo h1 fun s2 hs2 hm2 => ?_
        refine eventually_movD h2 fun s3 hs3 hm3 => ?_
        refine eventually_movD h3 fun s4 hs4 hm4 => ?_
        refine eventually_movD h4 fun s5 hs5 hm5 => ?_
        have erax : s5.regs.get64 .rax = argv s.regs a := by
          rw [hs5, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs4, Reg64s.get64_set64_same, hs3,
            Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs2,
            Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1, Reg64s.get64_set64_same]
        have er11 : s5.regs.get64 .r11 = argv s.regs b := by
          rw [hs5, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs4,
            Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs3,
            Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs2, Reg64s.get64_set64_same]
          exact argv_congr fun r hr => by
            rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hb r hr).1)]
        have er10 : s5.regs.get64 .r10 = s.regs.get64 .rax := by
          rw [hs5, Reg64s.get64_set64_same, hs4, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs3,
            Reg64s.get64_set64_same, hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1,
            Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
        refine eventually_divCore hd hcore (by rw [erax, er11]; exact hv) fun s6 hv6 hfr6 hm6 => ?_
        refine eventually_movD hp0 fun s7 hs7 hm7 => ?_
        refine eventually_movD hp1 fun s8 hs8 hm8 => ?_
        have := hk s8 ?_ (fun r hr => ?_) (by rw [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1])
        · simp only [List.length_cons, List.length_append, List.length_nil] at this; rwa [show k + 1 + 1 + 1 + 1 + 1 + core.length + 1 + 1 = k + (core.length + 2 + 1 + 1 + 1 + 1 + 1) by omega]
        · rw [hs8, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs7, Reg64s.get64_set64_same, hv6]
        · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
          rw [hs8, Reg64s.get64_set64]
          split
          · next he =>
            subst he
            rw [hs7, Reg64s.get64_set64_of_ne _ _ _ _ (by decide),
              hfr6 .r10 (by decide) (by decide), er10]
          · next he =>
            rw [hs7, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1),
              hfr6 r (Ne.symm he) hr.1, hs5, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1),
              hs4, Reg64s.get64_set64_of_ne _ _ _ _ he, hs3,
              Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs2,
              Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1), hs1,
              Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1)]
      · simp only [divSeq, hscr, hrax, hrdx, ite_false, Option.some.injEq] at hseq
        subst hseq
        obtain ⟨h0, hc1⟩ := hc.cons
        obtain ⟨h1, hc2⟩ := hc1.cons
        obtain ⟨h2, hc3⟩ := hc2.cons
        obtain ⟨h3, hc4⟩ := hc3.cons
        obtain ⟨h4, hc_rest⟩ := hc4.cons
        obtain ⟨hcore, hpost⟩ := List.IsInfixAt.append hc_rest
        obtain ⟨hp0, hpost1⟩ := hpost.cons
        obtain ⟨hp1, hpost2⟩ := hpost1.cons
        obtain ⟨hp2, hpost3⟩ := hpost2.cons
        obtain ⟨hp3, -⟩ := hpost3.cons
        refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
        refine eventually_argTo h1 fun s2 hs2 hm2 => ?_
        refine eventually_movD h2 fun s3 hs3 hm3 => ?_
        refine eventually_movD h3 fun s4 hs4 hm4 => ?_
        refine eventually_movD h4 fun s5 hs5 hm5 => ?_
        have erax : s5.regs.get64 .rax = argv s.regs a := by
          rw [hs5, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs4, Reg64s.get64_set64_same, hs3,
            Reg64s.get64_set64_of_ne _ _ _ _ hrd10, hs2,
            Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1, Reg64s.get64_set64_same]
        have er11 : s5.regs.get64 .r11 = argv s.regs b := by
          rw [hs5, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs4,
            Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs3,
            Reg64s.get64_set64_of_ne _ _ _ _ hrd11, hs2, Reg64s.get64_set64_same]
          exact argv_congr fun r hr => by
            rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hb r hr).1)]
        refine eventually_divCore hd hcore (by rw [erax, er11]; exact hv) fun s6 hv6 hfr6 hm6 => ?_
        refine eventually_movD hp0 fun s7 hs7 hm7 => ?_
        refine eventually_movD hp1 fun s8 hs8 hm8 => ?_
        refine eventually_movD hp2 fun s9 hs9 hm9 => ?_
        refine eventually_movD hp3 fun s10 hs10 hm10 => ?_
        have := hk s10 ?_ (fun r hr => ?_)
          (by rw [hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1])
        · simp only [List.length_cons, List.length_append, List.length_nil] at this; rwa [show k + 1 + 1 + 1 + 1 + 1 + core.length + 1 + 1 + 1 + 1 = k + (core.length + 4 + 1 + 1 + 1 + 1 + 1) by omega]
        · rw [hs10, Reg64s.get64_set64_same, hs9, Reg64s.get64_set64_of_ne _ _ _ _ (by decide),
            hs8, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs7, Reg64s.get64_set64_same, hv6]
        · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
          rw [hs10, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs9, Reg64s.get64_set64]
          split
          · next he =>
            subst he
            rw [hs8, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hrdx), hs7,
              Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hrd11), hfr6 rd hrax hrdx, hs5,
              Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hrd10), hs4,
              Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hrax), hs3, Reg64s.get64_set64_same, hs2,
              Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1,
              Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
          · next he_rax =>
            rw [hs8, Reg64s.get64_set64]
            split
            · next he =>
              subst he
              rw [hs7, Reg64s.get64_set64_of_ne _ _ _ _ (by decide),
                hfr6 .r10 (by decide) (by decide), hs5, Reg64s.get64_set64_same, hs4,
                Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs3,
                Reg64s.get64_set64_of_ne _ _ _ _ hrdx, hs2,
                Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1,
                Reg64s.get64_set64_of_ne _ _ _ _ (by decide)]
            · next he_rdx =>
              rw [hs7, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1),
                hfr6 r (Ne.symm he_rax) (Ne.symm he_rdx), hs5,
                Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1), hs4,
                Reg64s.get64_set64_of_ne _ _ _ _ he_rax, hs3,
                Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs2,
                Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1), hs1,
                Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1)]

theorem eventually_op {k : Nat} {o : Op Reg64} {rd : Reg64} {c : List Directive} {v : Val}
    {s : MachineData} {post : (MachineState → Prop)}
    (hop : op o rd = some c) (hc : c.IsInfixAt Host.prog k)
    (hvars : ∀ r, r ∈ o.vars → r ∉ scratchRegs)
    (hv : (o.map s.regs.get64).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + c.length) s' post) :
    Run k s post := by
  have keep : ∀ (x : Val) (s1 : MachineData), s1.regs = s.regs.set64 rd x →
      ∀ r, r ∉ rd :: scratchRegs → s1.regs.get64 r = s.regs.get64 r := by
    intro x s1 hs1 r hr
    simp only [List.mem_cons, not_or] at hr
    rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1)]
  cases o with
  | bin kk oo a b =>
    have hav : ∀ r, r ∈ a.vars → r ≠ .r10 ∧ r ≠ .r11 := fun r hr =>
      ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))
    have hbv : ∀ r, r ∈ b.vars → r ≠ .r10 ∧ r ≠ .r11 := fun r hr =>
      ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))
    have hv' := (eval_bin_imm kk oo (a.map s.regs.get64) (b.map s.regs.get64)).symm.trans hv
    cases hsh : shiftIns kk oo with
    | some i =>
      simp only [op, hsh, Option.some.injEq] at hop
      subst hop
      exact eventually_shift hsh hc hbv hv' hk
    | none =>
    cases hdv : divCore kk oo with
    | some cr =>
      simp only [op, hsh, hdv] at hop
      exact eventually_divSeq hdv hop hc hbv hv' hk
    | none =>
    simp only [op, hsh, hdv, Option.map_eq_some_iff] at hop
    obtain ⟨i, hb, rfl⟩ := hop
    obtain ⟨h0, hc1⟩ := hc.cons
    obtain ⟨h1, hc2⟩ := hc1.cons
    obtain ⟨h2, hc3⟩ := hc2.cons
    obtain ⟨h3, -⟩ := hc3.cons
    refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
    refine eventually_argTo h1 fun s2 hs2 hm2 => ?_
    have e11 : s2.regs.get64 .r11 = argv s.regs a := by
      rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1, Reg64s.get64_set64_same]
    have e10 : s2.regs.get64 .r10 = argv s.regs b := by
      rw [hs2, Reg64s.get64_set64_same]
      exact argv_congr fun r hr => by
        rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hbv r hr).2)]
    refine eventually_binIns hb h2 (by rw [e11, e10]; exact hv') fun s3 hs3 hm3 => ?_
    refine eventually_movD h3 fun s4 hs4 hm4 => hk s4 ?_ (fun r hr => ?_) ?_
    · rw [hs4, Reg64s.get64_set64_same, hs3, Reg64s.get64_set64_same]
    · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
      rw [hs4, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs3,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1), hs2,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1), hs1,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1)]
    · rw [hm4, hm3, hm2, hm1]
  | cmp kk oo a b =>
    have hav : ∀ r, r ∈ a.vars → r ≠ .r11 := fun r hr =>
      (ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))).2
    have hbv : ∀ r, r ∈ b.vars → r ≠ .r11 := fun r hr =>
      (ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))).2
    have hv' : (Op.cmp kk oo (.imm (argv s.regs a)) (.imm (argv s.regs b))).eval = some v := by
      rw [← hv]; cases kk <;> rfl
    rw [eval_cmp, Option.some.injEq] at hv'
    subst hv'
    simp only [op, Option.some.injEq] at hop
    subst hop
    cases hsw : (condOf oo).1 <;> simp only [hsw, ite_true, ite_false, Bool.false_eq_true] at hc hk ⊢
    · exact eventually_cmp hc hbv hk
    · exact eventually_cmp hc hav hk
  | ext kk sz sg a =>
    simp only [Op.map, Op.eval, Option.some.injEq] at hv
    subst hv
    cases a with
    | var r =>
      simp only [op, Option.some.injEq] at hop
      subst hop
      exact eventually_extD (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
        hk s1 (by rw [hs1, Reg64s.get64_set64_same]; rfl) (keep _ s1 hs1) hm1
    | imm c0 =>
      simp only [op, Option.some.injEq] at hop
      subst hop
      exact eventually_moviD (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
        hk s1 (by rw [hs1, Reg64s.get64_set64_same]; rfl) (keep _ s1 hs1) hm1
  | copy kk a =>
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
  simp only [load, Option.some.injEq] at hop
  subst hop
  simp only [loadVal, Option.map_eq_some_iff] at hv
  obtain ⟨n, hn, rfl⟩ := hv
  cases a with
  | var ra =>
    simp only [addrIn, List.nil_append] at hc hk ⊢
    refine eventually_loadIns hc hn fun s1 hs1 hm1 => hk s1 ?_ (fun r hr => ?_) hm1
    · rw [hs1, Reg64s.get64_set64_same]
    · simp only [List.mem_cons, not_or] at hr
      rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1)]
  | imm c0 =>
    simp only [addrIn, List.singleton_append, List.length_cons] at hc hk ⊢
    obtain ⟨h0, hc1⟩ := hc.cons
    refine eventually_moviD h0 fun s1 hs1 hm1 => ?_
    refine eventually_loadIns hc1 (by rw [hm1, hs1, Reg64s.get64_set64_same]; exact hn)
      fun s2 hs2 hm2 => ?_
    have := hk s2 (by rw [hs2, Reg64s.get64_set64_same]) (fun r hr => ?_) (by rw [hm2, hm1])
    · rwa [Nat.add_assoc, Nat.add_comm 1]
    · simp only [List.mem_cons, not_or] at hr
      rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs1,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1)]

theorem eventually_store {k : Nat} {sz : Sz} {x a : Arg Reg64} {c : List Directive}
    {s : MachineData} {post : (MachineState → Prop)}
    (hop : store sz x a = some c) (hc : c.IsInfixAt Host.prog k)
    (hvars : ∀ r, r ∈ x.vars ++ a.vars → r ∉ scratchRegs)
    (hok : storeOk s.dmem sz (argv s.regs a))
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratchRegs → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = storeMem s.dmem sz (argv s.regs a) (argv s.regs x) →
      Run (k + c.length) s' post) :
    Run k s post := by
  simp only [store, Option.some.injEq] at hop
  subst hop
  obtain ⟨n, hn⟩ := hok
  obtain ⟨h0, hc1⟩ := hc.cons
  refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
  have e11 : s1.regs.get64 .r11 = argv s.regs x := by rw [hs1, Reg64s.get64_set64_same]
  cases a with
  | var ra =>
    simp only [addrIn] at hc1 hk ⊢
    have hra := ne_of_not_mem_scratch (hvars ra (by simp [Arg.vars]))
    have e : s1.regs.get64 ra = s.regs.get64 ra := by
      rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hra.2)]
    refine eventually_storeIns (List.isInfixAt_singleton.mp hc1) (n := n)
      (by rw [hm1, e]; exact hn) fun s2 hs2 hm2 => hk s2 (fun r hr => ?_) ?_
    · have := ne_of_not_mem_scratch hr
      rw [hs2, hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm this.2)]
    · rw [hm2, hm1, e, e11]
      rfl
  | imm c0 =>
    simp only [addrIn] at hc1 hk ⊢
    obtain ⟨h1, hc2⟩ := hc1.cons
    refine eventually_moviD h1 fun s2 hs2 hm2 => ?_
    have e10 : s2.regs.get64 .r10 = c0 := by rw [hs2, Reg64s.get64_set64_same]
    have e11' : s2.regs.get64 .r11 = argv s.regs x := by
      rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), e11]
    refine eventually_storeIns (List.isInfixAt_singleton.mp hc2) (n := n)
      (by rw [hm2, hm1, e10]; exact hn) fun s3 hs3 hm3 => hk s3 (fun r hr => ?_) ?_
    · have := ne_of_not_mem_scratch hr
      rw [hs3, hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm this.1), hs1,
        Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm this.2)]
    · rw [hm3, hm2, hm1, e10, e11']
      rfl


end
/-- `op` succeeds on every IL operation when the destination is not a scratch register. -/
theorem op_isSome (o : Op Reg64) (rd : Reg64) (hrd : rd ∉ scratchRegs) : (op o rd).isSome = true := by
  have := ne_of_not_mem_scratch hrd
  cases o with
  | bin k bo a b =>
    cases k <;> cases bo <;> cases rd <;>
      first | rfl | exact absurd rfl this.1 | exact absurd rfl this.2
  | cmp k co a b => rfl
  | ext k s sg a => cases a <;> rfl
  | copy k a => cases k <;> cases a <;> rfl

/-- `load` succeeds on every class, width, signedness, destination and address. -/
theorem load_isSome (cl : Cls) (sz : Sz) (sg : Bool) (rd : Reg64) (a : Arg Reg64) :
    (load cl sz sg rd a).isSome = true := rfl

/-- `store` succeeds on every width, value and address. -/
theorem store_isSome (sz : Sz) (x a : Arg Reg64) : (store sz x a).isSome = true := rfl

/-! ## Fast-path instruction selection: step lemmas and totality -/

theorem eval_bin_comm {k : Cls} {o : BinOp} (hc : isComm o = true) (x y : Val) :
    (Op.bin k o (.imm x) (.imm y)).eval = (Op.bin k o (.imm y) (.imm x)).eval := by
  cases k <;> cases o <;> (try simp [isComm] at hc) <;> simp only [Op.eval, Arg.val, BinOp.eval]
  · rw [BitVec.add_comm]
  · rw [BitVec.mul_comm]
  · rw [BitVec.and_comm]
  · rw [BitVec.or_comm]
  · rw [BitVec.xor_comm]
  · rw [BitVec.add_comm]
  · rw [BitVec.mul_comm]
  · rw [BitVec.and_comm]
  · rw [BitVec.or_comm]
  · rw [BitVec.xor_comm]

section
variable [Host]

theorem eventually_shiftImmIns {i : Nat} {k : Cls} {o : BinOp} {r : Reg64} {c : Val}
    {di : Directive} {v : Val} {s : MachineData} {post : (MachineState → Prop)}
    (hb : shiftImmIns k o r c = some di) (hi : Host.prog[i]? = some di)
    (hv : (Op.bin k o (.imm (s.regs.get64 r)) (.imm c)).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 r v → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  cases k <;> cases o <;> simp only [shiftImmIns, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
    refine Host.eventually_of_interp_cps hi ?_ <;>
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
      MachineData.setReg, Effects.All, set_q, get_q, Reg64s.set_low32, Reg64s.get_low32,
      ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Int64.toBitVec_ofBitVec, take8_and_31, take8_and_63] <;>
    simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
    subst hv
  all_goals
    repeat' (first | split | (simp only [Effects.All]; intros))
  all_goals
    try simp only [Effects.All]
    intros
    refine hk _ ?_ rfl
  all_goals
    first
    | rfl
    | (rename_i h; simp at h; simp [h])

theorem eventually_shiftImm {k : Nat} {kk : Cls} {oo : BinOp} {a : Arg Reg64} {c0 : Val}
    {rd : Reg64} {i : Directive} {v : Val} {s : MachineData} {post : (MachineState → Prop)}
    (hsh : shiftImmIns kk oo rd c0 = some i)
    (hc : [argTo rd a, i].IsInfixAt Host.prog k)
    (hv : (Op.bin kk oo (.imm (argv s.regs a)) (.imm c0)).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 2) s' post) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, -⟩ := hc1.cons
  refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
  have erd : s1.regs.get64 rd = argv s.regs a := by rw [hs1, Reg64s.get64_set64_same]
  refine eventually_shiftImmIns hsh h1 (by rw [erd]; exact hv) fun s2 hs2 hm2 =>
    hk s2 ?_ (fun r hr => ?_) ?_
  · rw [hs2, Reg64s.get64_set64_same]
  · simp only [List.mem_cons, not_or] at hr
    rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs1,
      Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1)]
  · rw [hm2, hm1]

theorem eventually_binRegIns {i : Nat} {k : Cls} {o : BinOp} {rd rs : Reg64} {di : Directive}
    {v : Val} {s : MachineData} {post : (MachineState → Prop)}
    (hb : binRegIns k o rd rs = some di) (hi : Host.prog[i]? = some di)
    (hv : (Op.bin k o (.imm (s.regs.get64 rd)) (.imm (s.regs.get64 rs))).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 rd v → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  cases k <;> cases o <;> simp only [binRegIns, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
    refine Host.eventually_of_interp_cps hi ?_ <;>
    simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, set_q, get_q,
      Reg64s.set_low32, Reg64s.get_low32] <;>
    simp only [Op.eval, Arg.val, BinOp.eval, Option.map_some, Option.some.injEq] at hv <;>
    subst hv <;>
    (repeat intro _) <;>
    refine hk _ ?_ rfl
  all_goals first | rfl | (dsimp only; rw [BitVec.add_comm])

theorem eventually_cmpRegIns {i : Nat} {k : Cls} {rx ry : Reg64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (cmpRegIns k rx ry))
    (hk : ∀ s' : MachineData, s'.regs = s.regs → s'.dmem = s.dmem →
      s'.status = cmpFlags k (s.regs.get64 rx) (s.regs.get64 ry) → Run (i + 1) s' post) :
    Run i s post := by
  cases k <;>
    refine Host.eventually_of_interp_cps hi ?_ <;>
    simp only [cmpRegIns, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, Effects.All, get_q, Reg64s.get_low32] <;>
    exact hk _ rfl rfl rfl

theorem eventually_cmpReg {k : Nat} {kk : Cls} {cc : CondCode} {rx ry rd : Reg64}
    {s : MachineData} {post : (MachineState → Prop)}
    (hc : [cmpRegIns kk rx ry, setccD cc, movzbD rd].IsInfixAt Host.prog k)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = boolVal (cc.interp (cmpFlags kk (s.regs.get64 rx) (s.regs.get64 ry))) →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 3) s' post) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, hc2⟩ := hc1.cons
  obtain ⟨h2, -⟩ := hc2.cons
  refine eventually_cmpRegIns h0 fun s1 hs1 hm1 hf1 => ?_
  refine eventually_setcc_movzb h1 h2 fun s2 hv2 hfr2 hm2 => hk s2 ?_ (fun r hr => ?_) ?_
  · rw [hv2, hf1]
  · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
    rw [hfr2 r hr.1 hr.2.2.1, hs1]
  · rw [hm2, hm1]

theorem eventually_cmpRegImm {k : Nat} {kk : Cls} {cc : CondCode} {rx rd : Reg64} {cy : Val}
    {s : MachineData} {post : (MachineState → Prop)}
    (hc : [moviD .r10 cy, cmpRegIns kk rx .r10, setccD cc, movzbD rd].IsInfixAt Host.prog k)
    (hrx : rx ≠ .r10)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = boolVal (cc.interp (cmpFlags kk (s.regs.get64 rx) cy)) →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 4) s' post) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  refine eventually_moviD h0 fun s1 hs1 hm1 => ?_
  refine eventually_cmpReg hc1 fun s2 hv2 hfr2 hm2 => hk s2 ?_ (fun r hr => ?_) ?_
  · rw [hv2, hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hrx), Reg64s.get64_set64_same]
  · have hne := ne_of_not_mem_scratch fun h => hr (List.mem_cons_of_mem _ h)
    rw [hfr2 r hr, hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hne.1)]
  · rw [hm2, hm1]

theorem eventually_cmpImmReg {k : Nat} {kk : Cls} {cc : CondCode} {ry rd : Reg64} {cx : Val}
    {s : MachineData} {post : (MachineState → Prop)}
    (hc : [moviD .r10 cx, cmpRegIns kk .r10 ry, setccD cc, movzbD rd].IsInfixAt Host.prog k)
    (hry : ry ≠ .r10)
    (hk : ∀ s' : MachineData,
      s'.regs.get64 rd = boolVal (cc.interp (cmpFlags kk cx (s.regs.get64 ry))) →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 4) s' post) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  refine eventually_moviD h0 fun s1 hs1 hm1 => ?_
  refine eventually_cmpReg hc1 fun s2 hv2 hfr2 hm2 => hk s2 ?_ (fun r hr => ?_) ?_
  · rw [hv2, hs1, Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hry)]
  · have hne := ne_of_not_mem_scratch fun h => hr (List.mem_cons_of_mem _ h)
    rw [hfr2 r hr, hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hne.1)]
  · rw [hm2, hm1]

theorem eventually_storeRegIns {i : Nat} {sz : Sz} {rv ra : Reg64} {s : MachineData}
    {post : (MachineState → Prop)}
    (hi : Host.prog[i]? = some (storeRegIns sz rv ra))
    {n : Int} (hload : Mem.loadInt s.dmem (s.regs.get64 ra) sz.bytes = some n)
    (hk : ∀ s' : MachineData, s'.regs = s.regs →
      s'.dmem = storeMem s.dmem sz (s.regs.get64 ra) (s.regs.get64 rv) →
      Run (i + 1) s' post) :
    Run i s post := by
  cases sz
  case l => exact eventually_storelD hi hload hk
  all_goals
    simp only [Sz.bytes] at hload
    refine Host.eventually_of_interp_cps hi ?_
    simp only [storeRegIns, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, MachineData.set, Effects.All, atReg_interp, get_b8, get_h16,
      Reg64s.get_low32]
    simp only [MachineData.store, Effects.All_require_write_access, Width.bytes, hload]
    exact hk _ rfl rfl

theorem eventually_binFallback {k : Nat} {kk : Cls} {oo : BinOp} {a b : Arg Reg64} {rd : Reg64}
    {i : Directive} {v : Val} {s : MachineData} {post : (MachineState → Prop)}
    (hb : binIns kk oo = some i)
    (hc : [argTo .r11 a, argTo .r10 b, i, movD rd .r11].IsInfixAt Host.prog k)
    (hbv : ∀ r, r ∈ b.vars → r ≠ .r10 ∧ r ≠ .r11)
    (hv' : (Op.bin kk oo (.imm (argv s.regs a)) (.imm (argv s.regs b))).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + 4) s' post) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, hc2⟩ := hc1.cons
  obtain ⟨h2, hc3⟩ := hc2.cons
  obtain ⟨h3, -⟩ := hc3.cons
  refine eventually_argTo h0 fun s1 hs1 hm1 => ?_
  refine eventually_argTo h1 fun s2 hs2 hm2 => ?_
  have e11 : s2.regs.get64 .r11 = argv s.regs a := by
    rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (by decide), hs1, Reg64s.get64_set64_same]
  have e10 : s2.regs.get64 .r10 = argv s.regs b := by
    rw [hs2, Reg64s.get64_set64_same]
    exact argv_congr fun r hr => by
      rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm (hbv r hr).2)]
  refine eventually_binIns hb h2 (by rw [e11, e10]; exact hv') fun s3 hs3 hm3 => ?_
  refine eventually_movD h3 fun s4 hs4 hm4 => hk s4 ?_ (fun r hr => ?_) ?_
  · rw [hs4, Reg64s.get64_set64_same, hs3, Reg64s.get64_set64_same]
  · simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
    rw [hs4, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs3,
      Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1), hs2,
      Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1), hs1,
      Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.2.1)]
  · rw [hm4, hm3, hm2, hm1]

theorem eventually_fastOp {k : Nat} {o : Op Reg64} {rd : Reg64} {c : List Directive} {v : Val}
    {s : MachineData} {post : (MachineState → Prop)}
    (hop : fastOp o rd = some c) (hc : c.IsInfixAt Host.prog k)
    (hvars : ∀ r, r ∈ o.vars → r ∉ scratchRegs)
    (hv : (o.map s.regs.get64).eval = some v)
    (hk : ∀ s' : MachineData, s'.regs.get64 rd = v →
      (∀ r, r ∉ rd :: scratchRegs → s'.regs.get64 r = s.regs.get64 r) → s'.dmem = s.dmem →
      Run (k + c.length) s' post) :
    Run k s post := by
  have keep : ∀ (x : Val) (s1 : MachineData), s1.regs = s.regs.set64 rd x →
      ∀ r, r ∉ rd :: scratchRegs → s1.regs.get64 r = s.regs.get64 r := by
    intro x s1 hs1 r hr
    simp only [List.mem_cons, not_or] at hr
    rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1)]
  cases o with
  | bin kk oo a b =>
    have hav : ∀ r, r ∈ a.vars → r ≠ .r10 ∧ r ≠ .r11 := fun r hr =>
      ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))
    have hbv : ∀ r, r ∈ b.vars → r ≠ .r10 ∧ r ≠ .r11 := fun r hr =>
      ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))
    have hv' := (eval_bin_imm kk oo (a.map s.regs.get64) (b.map s.regs.get64)).symm.trans hv
    cases hsh : shiftIns kk oo with
    | some i =>
      cases b with
      | var rb =>
        simp only [fastOp, hsh, Option.some.injEq] at hop
        subst hop
        exact eventually_shift hsh hc hbv hv' hk
      | imm c0 =>
        cases hsi : shiftImmIns kk oo rd c0 with
        | some si =>
          cases kk with
          | w =>
            simp only [fastOp, hsh, hsi, Option.some.injEq] at hop
            subst hop
            exact eventually_shiftImm hsi hc hv' hk
          | l =>
            cases a with
            | imm ca =>
              simp only [fastOp, hsh, hsi, Option.some.injEq] at hop
              subst hop
              exact eventually_shiftImm hsi hc hv' hk
            | var ra =>
              simp only [fastOp, hsh, hsi] at hop
              by_cases h1 : ra = rd
              · subst h1
                simp only [ite_true, Option.some.injEq] at hop
                subst hop
                exact eventually_shiftImmIns hsi (List.isInfixAt_singleton.mp hc) hv' fun s1 hs1 hm1 =>
                  hk s1 (by rw [hs1, Reg64s.get64_set64_same]) (keep _ s1 hs1) hm1
              · simp only [h1, ite_false, Option.some.injEq] at hop
                subst hop
                exact eventually_shiftImm hsi hc hv' hk
        | none =>
          simp only [fastOp, hsh, hsi, Option.some.injEq] at hop
          subst hop
          exact eventually_shift hsh hc hbv hv' hk
    | none =>
    cases hdv : divCore kk oo with
    | some cr =>
      simp only [fastOp, hsh, hdv] at hop
      exact eventually_divSeq hdv hop hc hbv hv' hk
    | none =>
    cases kk with
    | w =>
      simp only [fastOp, hsh, hdv, Option.map_eq_some_iff] at hop
      obtain ⟨i, hb, rfl⟩ := hop
      exact eventually_binFallback hb hc hbv hv' hk
    | l =>
      cases a with
      | imm ca =>
        simp only [fastOp, hsh, hdv, Option.map_eq_some_iff] at hop
        obtain ⟨i, hb, rfl⟩ := hop
        exact eventually_binFallback hb hc hbv hv' hk
      | var ra =>
        cases b with
        | imm cb =>
          simp only [fastOp, hsh, hdv] at hop
          by_cases hra : ra = rd
          · subst hra
            simp only [ite_true, Option.map_eq_some_iff] at hop
            obtain ⟨i, hb, rfl⟩ := hop
            obtain ⟨h0, hc1⟩ := hc.cons
            obtain ⟨h1, -⟩ := hc1.cons
            have hrd10 : ra ≠ .r10 := (hav ra (by simp [Arg.vars])).1
            refine eventually_moviD h0 fun s1 hs1 hm1 => ?_
            have erd : s1.regs.get64 ra = s.regs.get64 ra := by
              rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hrd10)]
            have e10 : s1.regs.get64 .r10 = cb := by rw [hs1, Reg64s.get64_set64_same]
            refine eventually_binRegIns hb h1 (by rw [erd, e10]; exact hv') fun s2 hs2 hm2 =>
              hk s2 (by rw [hs2, Reg64s.get64_set64_same]) (fun r hr => ?_) (by rw [hm2, hm1])
            simp only [List.mem_cons, not_or, List.not_mem_nil] at hr
            rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs1,
              Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.2.1)]
          · simp only [hra, ite_false, Option.map_eq_some_iff] at hop
            obtain ⟨i, hb, rfl⟩ := hop
            exact eventually_binFallback hb hc hbv hv' hk
        | var rb =>
          simp only [fastOp, hsh, hdv] at hop
          by_cases hra : ra = rd
          · subst hra
            simp only [ite_true, Option.map_eq_some_iff] at hop
            obtain ⟨i, hb, rfl⟩ := hop
            exact eventually_binRegIns hb (List.isInfixAt_singleton.mp hc) hv' fun s1 hs1 hm1 =>
              hk s1 (by rw [hs1, Reg64s.get64_set64_same]) (keep _ s1 hs1) hm1
          · simp only [hra, ite_false] at hop
            by_cases hrb : isComm oo = true ∧ rb = rd
            · simp only [hrb, and_self, ite_true, Option.map_eq_some_iff] at hop
              obtain ⟨i, hb, rfl⟩ := hop
              rcases hrb with ⟨hcomm, rfl⟩
              rw [eval_bin_comm hcomm] at hv'
              exact eventually_binRegIns hb (List.isInfixAt_singleton.mp hc) hv' fun s1 hs1 hm1 =>
                hk s1 (by rw [hs1, Reg64s.get64_set64_same]) (keep _ s1 hs1) hm1
            · simp only [hrb, ite_false] at hop
              by_cases hne : rb ≠ rd
              · simp only [ne_eq, hne, not_false_eq_true, ite_true, Option.map_eq_some_iff] at hop
                obtain ⟨i, hb, rfl⟩ := hop
                obtain ⟨h0, hc1⟩ := hc.cons
                obtain ⟨h1, -⟩ := hc1.cons
                refine eventually_movD h0 fun s1 hs1 hm1 => ?_
                have erd : s1.regs.get64 rd = s.regs.get64 ra := by rw [hs1, Reg64s.get64_set64_same]
                have erb : s1.regs.get64 rb = s.regs.get64 rb := by
                  rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hne)]
                refine eventually_binRegIns hb h1 (by rw [erd, erb]; exact hv') fun s2 hs2 hm2 =>
                  hk s2 (by rw [hs2, Reg64s.get64_set64_same]) (fun r hr => ?_) (by rw [hm2, hm1])
                simp only [List.mem_cons, not_or] at hr
                rw [hs2, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1), hs1,
                  Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr.1)]
              · simp only [hne, ite_false, Option.map_eq_some_iff] at hop
                obtain ⟨i, hb, rfl⟩ := hop
                exact eventually_binFallback hb hc hbv hv' hk
  | cmp kk oo a b =>
    have hav : ∀ r, r ∈ a.vars → r ≠ .r10 ∧ r ≠ .r11 := fun r hr =>
      ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))
    have hbv : ∀ r, r ∈ b.vars → r ≠ .r10 ∧ r ≠ .r11 := fun r hr =>
      ne_of_not_mem_scratch (hvars r (by simp [Op.vars, hr]))
    have hv' : (Op.cmp kk oo (.imm (argv s.regs a)) (.imm (argv s.regs b))).eval = some v := by
      rw [← hv]; cases kk <;> rfl
    rw [eval_cmp, Option.some.injEq] at hv'
    subst hv'
    cases hsw : (condOf oo).1 <;>
      simp only [fastOp, hsw, ite_true, ite_false, Bool.false_eq_true] at hop hc hk ⊢
    · cases a with
      | var rx =>
        cases b with
        | var ry =>
          simp only [Option.some.injEq] at hop; subst hop
          exact eventually_cmpReg hc hk
        | imm cy =>
          simp only [Option.some.injEq] at hop; subst hop
          exact eventually_cmpRegImm hc (hav rx (by simp [Arg.vars])).1 hk
      | imm cx =>
        cases b with
        | var ry =>
          simp only [Option.some.injEq] at hop; subst hop
          exact eventually_cmpImmReg hc (hbv ry (by simp [Arg.vars])).1 hk
        | imm cy =>
          simp only [Option.some.injEq] at hop; subst hop
          exact eventually_cmp hc (fun r hr => (hbv r hr).2) hk
    · cases b with
      | var rx =>
        cases a with
        | var ry =>
          simp only [Option.some.injEq] at hop; subst hop
          exact eventually_cmpReg hc hk
        | imm cy =>
          simp only [Option.some.injEq] at hop; subst hop
          exact eventually_cmpRegImm hc (hbv rx (by simp [Arg.vars])).1 hk
      | imm cx =>
        cases a with
        | var ry =>
          simp only [Option.some.injEq] at hop; subst hop
          exact eventually_cmpImmReg hc (hav ry (by simp [Arg.vars])).1 hk
        | imm cy =>
          simp only [Option.some.injEq] at hop; subst hop
          exact eventually_cmp hc (fun r hr => (hav r hr).2) hk
  | ext kk sz sg a =>
    simp only [Op.map, Op.eval, Option.some.injEq] at hv
    subst hv
    cases a with
    | var r =>
      simp only [fastOp, Option.some.injEq] at hop
      subst hop
      exact eventually_extD (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
        hk s1 (by rw [hs1, Reg64s.get64_set64_same]; rfl) (keep _ s1 hs1) hm1
    | imm c0 =>
      simp only [fastOp, Option.some.injEq] at hop
      subst hop
      exact eventually_moviD (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
        hk s1 (by rw [hs1, Reg64s.get64_set64_same]; rfl) (keep _ s1 hs1) hm1
  | copy kk a =>
    cases kk with
    | l =>
      simp only [fastOp, Option.some.injEq] at hop
      subst hop
      simp only [Op.map, Op.eval, Cls.trunc, Option.some.injEq] at hv
      refine eventually_argTo (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
        hk s1 ?_ (keep _ s1 hs1) hm1
      rw [hs1, Reg64s.get64_set64_same]; exact hv
    | w =>
      cases a with
      | var r =>
        simp only [fastOp, Option.some.injEq] at hop
        subst hop
        simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
        refine eventually_movlD (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
          hk s1 ?_ (keep _ s1 hs1) hm1
        rw [hs1, Reg64s.get64_set64_same]; exact hv
      | imm c0 =>
        simp only [fastOp, Option.some.injEq] at hop
        subst hop
        simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
        refine eventually_moviD (List.isInfixAt_singleton.mp hc) fun s1 hs1 hm1 =>
          hk s1 ?_ (keep _ s1 hs1) hm1
        rw [hs1, Reg64s.get64_set64_same]; exact hv

theorem eventually_fastStore {k : Nat} {sz : Sz} {x a : Arg Reg64} {c : List Directive}
    {s : MachineData} {post : (MachineState → Prop)}
    (hop : fastStore sz x a = some c) (hc : c.IsInfixAt Host.prog k)
    (hvars : ∀ r, r ∈ x.vars ++ a.vars → r ∉ scratchRegs)
    (hok : storeOk s.dmem sz (argv s.regs a))
    (hk : ∀ s' : MachineData, (∀ r, r ∉ scratchRegs → s'.regs.get64 r = s.regs.get64 r) →
      s'.dmem = storeMem s.dmem sz (argv s.regs a) (argv s.regs x) →
      Run (k + c.length) s' post) :
    Run k s post := by
  obtain ⟨n, hn⟩ := hok
  cases x with
  | var rv =>
    simp only [fastStore, Option.some.injEq] at hop
    subst hop
    have hrv := ne_of_not_mem_scratch (hvars rv (by simp [Arg.vars]))
    cases a with
    | var ra =>
      simp only [addrIn, List.nil_append, List.length_singleton] at hc hk ⊢
      refine eventually_storeRegIns (List.isInfixAt_singleton.mp hc) hn fun s1 hs1 hm1 =>
        hk s1 (fun r _ => by rw [hs1]) hm1
    | imm c0 =>
      simp only [addrIn, List.singleton_append, List.length_cons] at hc hk ⊢
      obtain ⟨h0, hc1⟩ := hc.cons
      refine eventually_moviD h0 fun s1 hs1 hm1 => ?_
      have e10 : s1.regs.get64 .r10 = c0 := by rw [hs1, Reg64s.get64_set64_same]
      have erv : s1.regs.get64 rv = s.regs.get64 rv := by
        rw [hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hrv.1)]
      refine eventually_storeRegIns (List.isInfixAt_singleton.mp hc1)
        (by rw [hm1, e10]; exact hn) fun s2 hs2 hm2 => hk s2 (fun r hr => ?_) ?_
      · have := ne_of_not_mem_scratch hr
        rw [hs2, hs1, Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm this.1)]
      · rw [hm2, hm1, e10, erv]; rfl
  | imm cx =>
    exact eventually_store hop hc hvars ⟨n, hn⟩ hk

end

/-- `fastOp` succeeds on every IL operation when the destination is not a scratch register. -/
theorem fastOp_isSome (o : Op Reg64) (rd : Reg64) (hrd : rd ∉ scratchRegs) :
    (fastOp o rd).isSome = true := by
  have hne := ne_of_not_mem_scratch hrd
  cases o with
  | bin k bo a b =>
    cases k <;> cases bo <;> (try cases a) <;> (try cases b) <;>
      simp only [fastOp, shiftIns, shiftImmIns, divCore, divSeq, hne.1, hne.2, or_self,
        ite_false, binRegIns, binIns, Option.map_some] <;>
      repeat' (first | rfl | split)
  | cmp k co a b =>
    cases co <;> cases a <;> cases b <;> rfl
  | ext k s sg a => cases a <;> rfl
  | copy k a => cases k <;> cases a <;> rfl

/-- `fastStore` succeeds on every width, value and address. -/
theorem fastStore_isSome (sz : Sz) (x a : Arg Reg64) : (fastStore sz x a).isSome = true := by
  cases x <;> rfl

end LeanQbe.Amd64
