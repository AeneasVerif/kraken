module

public import LeanQbe.Arm64.TargLemmas
import Std.Tactic.BVDecide

/-!
# AArch64 instruction selection lemmas

`op_runs`: the snippet `op o (.reg d)` of `Isel.lean` computes `o`'s value into `x d`, clobbering
at most `x16`/`x17` and leaving memory unchanged.

* Flag facts for `subs` (`subs_c`, `subs_v`, `notCondOf_subs`): after `cmp a, b`, the negated
  condition of `cset` holds iff the IL comparison is false, at widths 32 and 64.
* Remainders: `umod_eq_sub`, `srem_eq_sub` (`msub` after `udiv`/`sdiv`).
* One lemma per family: `binIns_runs`, `cmpIns_runs`, `extIns_runs`; operands `args_runs`.

No native bit-blasting tactics: proofs go through `toNat`/`toInt` and `omega`, or bitwise `ext`.
-/

@[expose] public section

namespace LeanQbe.Arm64

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

theorem umod_eq_sub {n : Nat} (a b : BitVec n) : a % b = a - (a / b) * b := by
  apply BitVec.eq_of_toNat_eq
  have h := BitVec.isLt a
  rw [BitVec.toNat_umod, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv]
  have hq : a.toNat / b.toNat * b.toNat ≤ a.toNat := Nat.div_mul_le_self _ _
  have := Nat.mod_add_div a.toNat b.toNat
  rw [Nat.mul_comm] at this
  rw [Nat.mod_eq_of_lt (a := a.toNat / b.toNat * b.toNat) (by omega)]
  rw [show 2 ^ n - a.toNat / b.toNat * b.toNat + a.toNat = 2 ^ n + (a.toNat - a.toNat / b.toNat * b.toNat) by omega]
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (a := a.toNat - a.toNat / b.toNat * b.toNat) (by omega)]
  omega

theorem srem_eq_sub {n : Nat} (a b : BitVec n) : a.srem b = a - (a.sdiv b) * b := by
  rw [BitVec.srem_eq, BitVec.sdiv_eq]
  rcases a.msb <;> rcases b.msb <;> simp only [umod_eq_sub, BitVec.udiv_eq] <;>
    simp only [BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg, BitVec.sub_eq_add_neg, BitVec.neg_add]

theorem getRegOrZr_xzr (regs : Reg64s) (w : RegWidth) : regs.getRegOrZr (xzr w) = 0#w.bits := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]

set_option linter.unusedSimpArgs false in
theorem binIns_runs (w : RegWidth) (bo : BinOp) (d a b t : XReg) (s : MachineData)
    (r : BitVec w.bits) (ht : bo = .rem ∨ bo = .urem → t ≠ a ∧ t ≠ b)
    (hv : bo.eval ((get s (.reg a)).setWidth w.bits) ((get s (.reg b)).setWidth w.bits) = some r) :
    ∃ s', Runs (binIns w bo d a b t) s s' ∧ get s' (.reg d) = r.setWidth 64 ∧
      (∀ x, x ≠ .reg d → x ≠ .reg t → get s' x = get s x) ∧ s'.dmem = s.dmem := by
  generalize hx : (get s (.reg a)).setWidth w.bits = x at hv
  generalize hy : (get s (.reg b)).setWidth w.bits = y at hv
  rw [get_reg] at hx hy
  cases bo
  case rem =>
    obtain ⟨hta, htb⟩ := ht (Or.inl rfl)
    by_cases h : sdivDefined x y = true
    · simp only [BinOp.eval, h, ite_true, Option.some.injEq] at hv
      subst hv
      have hy0 : y ≠ 0 := by
        simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne] at h; exact h.1
      have hy0' : ¬ y.toNat = 0 := fun h0 => hy0 (BitVec.eq_of_toNat_eq (h0.trans rfl))
      refine ⟨wr (wr s t ((x.sdiv y).setWidth 64)) d ((x.srem y).setWidth 64),
        Runs.cons (s₂ := wr s t ((x.sdiv y).setWidth 64)) (fun p next jmp => ?_)
          (Runs.single fun p next jmp => ?_), get_wr_same ..,
        fun z hz hz' => by rw [get_wr_of_ne _ _ _ _ hz, get_wr_of_ne _ _ _ _ hz'], rfl⟩
      all_goals subst hx hy; cases w <;> simp at hy0' <;>
        simp [Operation.interp, MachineData.setRegOrZr, setRegOrZr_zr, getRegOrZr_zr, wr,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hta, Reg64s.getXReg_setXReg_of_ne _ _ _ _ htb,
          Reg64s.getXReg_setXReg_same, BitVec.toNat_eq, hy0', srem_eq_sub]
    · simp only [BinOp.eval, h, Bool.false_eq_true, ite_false, reduceCtorEq] at hv
  case urem =>
    obtain ⟨hta, htb⟩ := ht (Or.inr rfl)
    by_cases h : y = 0
    · simp only [BinOp.eval, h, ite_true, reduceCtorEq] at hv
    · simp only [BinOp.eval, h, ite_false, Option.some.injEq] at hv
      subst hv
      have hy0' : ¬ y.toNat = 0 := fun h0 => h (BitVec.eq_of_toNat_eq (h0.trans rfl))
      refine ⟨wr (wr s t ((x / y).setWidth 64)) d ((x % y).setWidth 64),
        Runs.cons (s₂ := wr s t ((x / y).setWidth 64)) (fun p next jmp => ?_)
          (Runs.single fun p next jmp => ?_), get_wr_same ..,
        fun z hz hz' => by rw [get_wr_of_ne _ _ _ _ hz, get_wr_of_ne _ _ _ _ hz'], rfl⟩
      all_goals subst hx hy; cases w <;> simp at hy0' <;>
        simp [Operation.interp, MachineData.setRegOrZr, setRegOrZr_zr, getRegOrZr_zr, wr,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hta, Reg64s.getXReg_setXReg_of_ne _ _ _ _ htb,
          Reg64s.getXReg_setXReg_same, BitVec.toNat_eq, hy0', umod_eq_sub]
  all_goals cases w
  all_goals
    refine ⟨wr s d (r.setWidth 64), Runs.single fun p next jmp => ?_, get_wr_same ..,
      fun x hx _ => get_wr_of_ne _ _ _ _ hx, rfl⟩
    simp only [BinOp.eval] at hv
    simp only [Operation.interp, MachineData.setRegOrZr, setRegOrZr_zr, getRegOrZr_zr,
      ShiftRegExpr.interp, wr, getRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
      BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.ushiftRight_eq, hx, hy]
  case div.W32 | div.W64 =>
    by_cases h : sdivDefined x y = true
    · simp only [h, ite_true, Option.some.injEq] at hv
      subst hv
      have hy0 : y ≠ 0 := by
        simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne] at h; exact h.1
      have hy0' : ¬ y.toNat = 0 := fun h0 => hy0 (BitVec.eq_of_toNat_eq (h0.trans rfl))
      simp [BitVec.toNat_eq, hy0']
    · simp only [h, Bool.false_eq_true, ite_false, reduceCtorEq] at hv
  case udiv.W32 | udiv.W64 =>
    by_cases h : y = 0
    · simp only [h, ite_true, reduceCtorEq] at hv
    · simp only [h, ite_false, Option.some.injEq] at hv
      subst hv
      have hy0' : ¬ y.toNat = 0 := fun h0 => h (BitVec.eq_of_toNat_eq (h0.trans rfl))
      simp [BitVec.toNat_eq, hy0']
  all_goals (simp only [Option.some.injEq] at hv; rw [hv])

theorem setRegOrZr_xzr (regs : Reg64s) (w : RegWidth) (v : BitVec w.bits) :
    regs.setRegOrZr (xzr w) v = regs := by
  cases w <;> rfl

theorem beq_zero_toInt {n : Nat} (z : BitVec n) : (z == 0#n) = decide (z.toInt = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toInt_inj, BitVec.toInt_zero]

theorem beq_toNat {n : Nat} (x y : BitVec n) : (x == y) = decide (x.toNat = y.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]

theorem notCondOf_subs {n : Nat} (hn : n = 32 ∨ n = 64) (co : CmpOp) (x y : BitVec n) :
    (notCondOf co).interp (StatusFlags.subs (x - y) x y) = !(co.eval x y) := by
  simp only [StatusFlags.subs, StatusFlags.from_result, subs_c, subs_v, BitVec.ssubOverflow,
    BitVec.zero_eq]
  have hx1 := BitVec.toInt_lt (x := x)
  have hx2 := BitVec.le_toInt x
  have hy1 := BitVec.toInt_lt (x := y)
  have hy2 := BitVec.le_toInt y
  have hd1 := BitVec.toInt_lt (x := x - y)
  have hd2 := BitVec.le_toInt (x - y)
  have hmod : (x - y).toInt % 2 ^ n = (x.toInt - y.toInt) % 2 ^ n := by
    rw [BitVec.toInt_sub]
    have : (x.toInt - y.toInt).bmod (2 ^ n) % ((2 ^ n : Nat) : Int) =
        (x.toInt - y.toInt) % ((2 ^ n : Nat) : Int) := Int.bmod_emod
    push_cast at this
    exact this
  have hxn := x.isLt
  have hyn := y.isLt
  have hsub := BitVec.toNat_sub x y
  rcases hn with rfl | rfl <;> cases co
  case' inl.sle | inl.slt | inl.sge | inl.sgt | inr.sle | inr.slt | inr.sge | inr.sgt =>
    simp only [notCondOf, CondCode.interp, CmpOp.eval, BitVec.msb_eq_toInt, beq_zero_toInt,
      BitVec.sle_eq_decide, BitVec.slt_eq_decide]
  all_goals
    try simp only [notCondOf, CondCode.interp, CmpOp.eval, beq_toNat, BitVec.toNat_ofNat,
      BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.lt_def, bne]
  all_goals
    rw [Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ← Bool.decide_or, ← Bool.decide_and, ← decide_not, beq_iff_eq, ne_eq,
      decide_eq_decide, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true]
    omega

set_option linter.unusedSimpArgs false in
theorem cmpIns_runs (w : RegWidth) (co : CmpOp) (d a b : XReg) (s : MachineData) :
    ∃ s', Runs (cmpIns w co d a b) s s' ∧
      get s' (.reg d) =
        boolVal (co.eval ((get s (.reg a)).setWidth w.bits) ((get s (.reg b)).setWidth w.bits)) ∧
      (∀ x, x ≠ .reg d → get s' x = get s x) ∧ s'.dmem = s.dmem := by
  generalize hx : (get s (.reg a)).setWidth w.bits = x
  generalize hy : (get s (.reg b)).setWidth w.bits = y
  rw [get_reg] at hx hy
  have hc := notCondOf_subs (by cases w <;> simp) co x y
  refine ⟨wr { s with status := StatusFlags.subs (x - y) x y } d (boolVal (co.eval x y)),
    Runs.cons (s₂ := { s with status := StatusFlags.subs (x - y) x y }) (fun p next jmp => ?_)
      (Runs.single fun p next jmp => ?_), get_wr_same .., fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
  · simp only [Operation.interp, MachineData.setRegOrZr, setRegOrZr_xzr, getRegOrZr_zr,
      ShiftRegExpr.interp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero, hx, hy]
  · simp only [Operation.interp, MachineData.setRegOrZr, setRegOrZr_zr, getRegOrZr_xzr, hc, wr]
    congr 3
    cases co.eval x y <;> decide

set_option linter.unusedSimpArgs false in
theorem extIns_runs (k : Cls) (sz : Sz) (sg : Bool) (d a : XReg) (s : MachineData) :
    ∃ s', Runs (extIns k sz sg d a) s s' ∧ get s' (.reg d) = k.trunc (sz.extend sg (get s (.reg a))) ∧
      (∀ x, x ≠ .reg d → get s' x = get s x) ∧ s'.dmem = s.dmem := by
  refine ⟨wr s d (k.trunc (sz.extend sg (get s (.reg a)))), ?_, get_wr_same ..,
    fun z hz => get_wr_of_ne _ _ _ _ hz, rfl⟩
  rw [get_reg]
  cases sz <;> cases sg <;> cases k <;> dsimp only [extIns, widthOf, topBit] <;>
    refine Runs.single fun p next jmp => ?_ <;>
    simp only [Operation.interp, MachineData.setRegOrZr, setRegOrZr_zr, getRegOrZr_zr,
      getRegOrZr_xzr, ShiftRegExpr.interp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
      evalSBFM, evalUBFM, Cls.trunc, Sz.extend, wr, BitVec.take, ite_true,
      ite_false, Bool.false_eq_true] <;>
    congr 3 <;> simp [lo32, zext32] <;> ext i hi <;>
    simp [BitVec.getElem_signExtend, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last] <;>
    by_cases h1 : i < 8 <;> by_cases h2 : i < 16 <;> by_cases h3 : i < 32 <;> simp [h1, h2, h3] <;> omega

theorem argIn_reg {a : Arg Reg} {tmp : XReg} {ca : List Directive} {ra : XReg}
    (h : argIn a tmp = some (ca, ra)) : a = .var (.reg ra) ∨ (ra = tmp ∧ ∃ c, a = .imm c) := by
  match a, h with
  | .var (.reg r), h =>
    simp only [argIn, Option.some.injEq, Prod.mk.injEq] at h
    exact .inl (by rw [h.2])
  | .imm c, h =>
    simp only [argIn, Option.some.injEq, Prod.mk.injEq] at h
    exact .inr ⟨h.2.symm, c, rfl⟩

theorem args_runs {a b : Arg Reg} {ca cb : List Directive} {ra rb : XReg} {s : MachineData}
    (ha : argIn a .X16 = some (ca, ra)) (hb : argIn b .X17 = some (cb, rb))
    (hvars : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch) :
    ∃ s₂, Runs (ca ++ cb) s s₂ ∧ get s₂ (.reg ra) = (a.map (get s)).val ∧
      get s₂ (.reg rb) = (b.map (get s)).val ∧ (∀ r, r ∉ scratch → get s₂ r = get s r) ∧
      s₂.dmem = s.dmem := by
  obtain ⟨s₁, h₁, hra, hf₁, hd₁, -⟩ := argIn_runs ha s
  obtain ⟨s₂, h₂, hrb, hf₂, hd₂, -⟩ := argIn_runs hb s₁
  refine ⟨s₂, h₁.append h₂, ?_, ?_, ?_, hd₂.trans hd₁⟩
  · rw [hf₂ _ ?_, hra]
    rcases argIn_reg ha with h | ⟨h, -⟩
    · have := hvars (.reg ra) (by simp [h, Arg.vars])
      simp only [scratch, List.mem_cons, not_or] at this
      exact this.2.1
    · simp [h]
  · rw [hrb]
    refine Arg.val_map_congr fun r hr => hf₁ r ?_
    have := hvars r (List.mem_append_right _ hr)
    simp only [scratch, List.mem_cons, not_or] at this
    exact this.1
  · intro r hr
    simp only [scratch, List.mem_cons, not_or] at hr
    rw [hf₂ r hr.2.1, hf₁ r hr.1]

theorem remTmp_spec {a b : Arg Reg} {ca cb : List Directive} {ra rb t : XReg}
    (ha : argIn a .X16 = some (ca, ra)) (hb : argIn b .X17 = some (cb, rb))
    (hvars : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch) (ht : remTmp a b = some t) :
    (t = .X16 ∨ t = .X17) ∧ t ≠ ra ∧ t ≠ rb := by
  have hva : ∀ r, a = .var (.reg r) → r ≠ .X16 ∧ r ≠ .X17 := fun r h => by
    have := hvars (.reg r) (by simp [h, Arg.vars])
    simpa [scratch] using this
  have hvb : ∀ r, b = .var (.reg r) → r ≠ .X16 ∧ r ≠ .X17 := fun r h => by
    have := hvars (.reg r) (by simp [h, Arg.vars])
    simpa [scratch] using this
  rcases argIn_reg ha with ha' | ⟨ha', c, hac⟩ <;> rcases argIn_reg hb with hb' | ⟨hb', c', hbc⟩
  · subst ha' hb'
    simp only [remTmp, Option.some.injEq] at ht
    subst ht
    exact ⟨.inr rfl, fun h => (hva ra rfl).2 h.symm, fun h => (hvb rb rfl).2 h.symm⟩
  · subst ha' hb' hbc
    simp only [remTmp, Option.some.injEq] at ht
    subst ht
    exact ⟨.inl rfl, fun h => (hva ra rfl).1 h.symm, by decide⟩
  · subst ha' hb' hac
    simp only [remTmp, Option.some.injEq] at ht
    subst ht
    exact ⟨.inr rfl, by decide, fun h => (hvb rb rfl).2 h.symm⟩
  · subst hac hbc
    simp [remTmp] at ht

theorem op_runs {o : Op Reg} {d : XReg} {c : List Directive} {v : Val} {s : MachineData}
    (hc : op o (.reg d) = some c) (hvars : ∀ r, r ∈ o.vars → r ∉ scratch)
    (hv : (o.map (get s)).eval = some v) :
    ∃ s', Runs c s s' ∧ get s' (.reg d) = v ∧ (∀ r, r ∉ .reg d :: scratch → get s' r = get s r) ∧
      s'.dmem = s.dmem := by
  cases o with
  | bin k bo a b =>
    simp only [op, bind, Option.bind_eq_some_iff] at hc
    obtain ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, hc⟩ := hc
    have hv' : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch := hvars
    obtain ⟨t, ht16, ht, rfl⟩ : ∃ t, (t = .X16 ∨ t = .X17) ∧ (bo = .rem ∨ bo = .urem → t ≠ ra ∧ t ≠ rb) ∧
        c = ca ++ cb ++ binIns (widthOf k) bo d ra rb t := by
      cases bo
      case rem | urem =>
        obtain ⟨t, ht, hc⟩ := Option.bind_eq_some_iff.mp hc
        simp only [Option.some.injEq] at hc
        obtain ⟨h1, h2, h3⟩ := remTmp_spec ha hb hv' ht
        exact ⟨t, h1, fun _ => ⟨h2, h3⟩, hc.symm⟩
      all_goals
        simp only [Option.bind_some, Option.some.injEq] at hc
        exact ⟨.X16, .inl rfl, fun h => by simp at h, hc.symm⟩
    obtain ⟨s₂, h₂, hra, hrb, hf₂, hd₂⟩ := args_runs (s := s) ha hb hv'
    simp only [Op.map, Op.eval] at hv
    cases k
    · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
      obtain ⟨s', h', hd', hf', hm'⟩ := binIns_runs .W32 bo d ra rb t s₂ r ht
        (by rw [hra, hrb]; exact hr)
      refine ⟨s', h₂.append h', hd', fun z hz => ?_, hm'.trans hd₂⟩
      obtain ⟨hzd, hz16, hz17⟩ := not_mem_rd_scratch hz
      rw [hf' z hzd (by rcases ht16 with rfl | rfl <;> assumption),
        hf₂ z (by simp [scratch, hz16, hz17])]
    · obtain ⟨s', h', hd', hf', hm'⟩ := binIns_runs .W64 bo d ra rb t s₂ v ht
        (by rw [hra, hrb]; simpa using hv)
      refine ⟨s', h₂.append h', hd'.trans (BitVec.setWidth_eq v), fun z hz => ?_, hm'.trans hd₂⟩
      obtain ⟨hzd, hz16, hz17⟩ := not_mem_rd_scratch hz
      rw [hf' z hzd (by rcases ht16 with rfl | rfl <;> assumption),
        hf₂ z (by simp [scratch, hz16, hz17])]
  | cmp k co a b =>
    simp only [op, bind, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl⟩ := hc
    have hv' : ∀ r, r ∈ a.vars ++ b.vars → r ∉ scratch := hvars
    obtain ⟨s₂, h₂, hra, hrb, hf₂, hd₂⟩ := args_runs (s := s) ha hb hv'
    obtain ⟨s', h', hd', hf', hm'⟩ := cmpIns_runs (widthOf k) co d ra rb s₂
    refine ⟨s', h₂.append h', ?_, fun z hz => ?_, hm'.trans hd₂⟩
    · rw [hd', hra, hrb]
      cases k <;> simp only [Op.map, Op.eval, Option.some.injEq] at hv <;> subst hv
      · rfl
      · simp [widthOf]
    · obtain ⟨hzd, hz16, hz17⟩ := not_mem_rd_scratch hz
      rw [hf' z hzd, hf₂ z (by simp [scratch, hz16, hz17])]
  | ext k sz sg a =>
    rcases a with ((r | _) | c₀)
    · simp only [op, Option.some.injEq] at hc
      subst hc
      obtain ⟨s', h', hd', hf', hm'⟩ := extIns_runs k sz sg d r s
      simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
      exact ⟨s', h', hd'.trans hv, fun z hz => hf' z (not_mem_rd_scratch hz).1, hm'⟩
    · simp [op] at hc
    · simp only [op, Option.some.injEq] at hc
      subst hc
      simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
      exact ⟨_, runs_movImm _ _ s, (get_wr_same ..).trans hv,
        fun z hz => get_wr_of_ne _ _ _ _ (not_mem_rd_scratch hz).1, rfl⟩
  | copy k a =>
    rcases a with ((r | _) | c₀)
    · simp only [op, Option.some.injEq] at hc
      subst hc
      obtain ⟨s', h', hd', hf', hm'⟩ := extIns_runs k .l false d r s
      simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
      exact ⟨s', h', hd'.trans hv, fun z hz => hf' z (not_mem_rd_scratch hz).1, hm'⟩
    · simp [op] at hc
    · simp only [op, Option.some.injEq] at hc
      subst hc
      simp only [Op.map, Op.eval, Arg.map, Arg.val, Option.some.injEq] at hv
      exact ⟨_, runs_movImm _ _ s, (get_wr_same ..).trans hv,
        fun z hz => get_wr_of_ne _ _ _ _ (not_mem_rd_scratch hz).1, rfl⟩

end LeanQbe.Arm64
